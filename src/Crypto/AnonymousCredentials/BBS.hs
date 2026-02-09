{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module: Crypto.AnonymousCredentials.BBS
--
-- __This library has not been independently audited. Use at your own risk.__
--
-- BBS MAC and keyed-verification anonymous credential presentation,
-- based on Section 3.1 of the Range.pdf construction.
--
-- A BBS MAC on messages @(m_1, ..., m_L)@ is a pair @(A, e)@ where
-- @A = (g + Σ h_i * m_i) ^ {1/(e+x)}@ for secret key @x@ and system-wide
-- public generators @h_1, ..., h_L@.
--
-- The presentation protocol provides:
--
-- * __Unlinkability__: each presentation is randomized with fresh scalars,
--   so different presentations of the same credential are unlinkable.
--
-- * __Selective disclosure__: the holder can reveal a subset of attributes
--   while proving knowledge of the remaining hidden attributes in zero
--   knowledge.
--
-- * __Scoped pseudonyms__: via the Dodis-Yampolskiy PRF, a credential
--   attribute can serve as a PRF key that produces a unique, deterministic
--   pseudonym per scope label. The proof binds the pseudonym to the
--   credential by sharing the PRF key witness across both the MAC
--   and PRF equations.
--
-- Verification is keyed: the verifier must hold the secret key.
module Crypto.AnonymousCredentials.BBS
  ( -- * System Parameters
    SystemParams(..)
  , setupParams
    -- * Secret Key
  , SecretKey(..)
  , keygen
    -- * MAC
  , MAC(..)
  , bbsMAC
  , verifyMAC
    -- * Presentation
  , Presentation(..)
  , present
  , verifyPresentation
    -- * Presentation with Scoped Pseudonym
  , PseudonymPresentation(..)
  , presentWithPseudonym
  , verifyPseudonymPresentation
  ) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Word (Word8)
import qualified Data.Vector as V

import Crypto.Sigma.DuplexSponge
import Crypto.Sigma.Error (DeserializeError)
import Crypto.Sigma.FiatShamir (prove, verify, i2osp)
import Crypto.Sigma.Group
import Crypto.Sigma.LinearMap
import Crypto.Sigma.Protocol
import Crypto.Sigma.Random (MonadRandom)
import Crypto.Sigma.Scalar

import Crypto.AnonymousCredentials.Internal (dyPRF)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- | System-wide public generators @h_1, ..., h_L@ for @L@ attributes.
--
-- These are random group elements with unknown discrete log relationships.
newtype SystemParams g = SystemParams
  { spGenerators :: V.Vector g }

-- | Secret key: a single scalar @x@.
newtype SecretKey g = SecretKey
  { skScalar :: GroupScalar g }

-- | BBS MAC @(A, e)@ on a vector of messages.
--
-- Satisfies @A^{e+x} = g + Σ h_i * m_i@ (the "body" @B@).
data MAC g = MAC
  { macA :: g
  , macE :: GroupScalar g
  }

-- | A credential presentation with selective disclosure.
--
-- Contains randomized MAC components and a Fiat-Shamir proof of
-- knowledge of the hidden attributes plus the MAC exponent.
data Presentation g = Presentation
  { presAPrime   :: g
  -- ^ @A' = A^{r1 * r2}@
  , presBBar     :: g
  -- ^ @Bbar = B^{r1}@
  , presDisclosed :: V.Vector (Int, GroupScalar g)
  -- ^ @(index, message)@ pairs for disclosed attributes (0-based indices)
  , presProof    :: ByteString
  -- ^ Compact Fiat-Shamir proof of knowledge of hidden attributes
  }

-- | A credential presentation with a scoped pseudonym.
--
-- In addition to selective disclosure, the holder proves correct
-- evaluation of the Dodis-Yampolskiy PRF using a credential attribute
-- as the PRF key.
data PseudonymPresentation g = PseudonymPresentation
  { ppAPrime    :: g
  -- ^ @A' = A^{r1 * r2}@
  , ppBBar      :: g
  -- ^ @Bbar = B^{r1}@
  , ppDisclosed :: V.Vector (Int, GroupScalar g)
  -- ^ @(index, message)@ pairs for disclosed attributes (0-based indices)
  , ppPseudonym :: g
  -- ^ Scoped pseudonym @P = (1 / (k + scope)) * G@
  , ppScope     :: GroupScalar g
  -- ^ The scope label used to derive the pseudonym
  , ppProof     :: ByteString
  -- ^ Compact Fiat-Shamir proof
  }

------------------------------------------------------------------------
-- Setup, key generation, and MAC
------------------------------------------------------------------------

-- | Generate @L@ random public generators for a system supporting
-- @L@ attributes.
setupParams :: forall g m. (Group g, MonadRandom m) => Int -> m (SystemParams g)
setupParams numAttrs = SystemParams <$> V.replicateM numAttrs groupRandom

-- | Generate a secret key (a single random scalar @x@).
keygen :: forall g m. (Group g, MonadRandom m) => m (SecretKey g)
keygen = SecretKey <$> scalarRandom

-- | Compute a BBS MAC on a vector of messages, producing @(A, e)@.
--
-- Computes @B = g + Σ h_i * m_i@, chooses random @e@, and sets
-- @A = B^{1/(e+x)}@.
bbsMAC :: forall g m. (Group g, MonadRandom m)
       => SystemParams g
       -> SecretKey g
       -> V.Vector (GroupScalar g)
       -> m (MAC g)
bbsMAC (SystemParams hs) (SecretKey x) msgs = do
  e <- scalarRandom
  let b = computeB hs msgs
      a = b |*| scalarInvert (e .+. x)
  pure (MAC a e)

-- | Verify a BBS MAC using the secret key.
--
-- Checks @A^{e+x} == g + Σ h_i * m_i@.
-- Verification is keyed (requires the secret key).
verifyMAC :: forall g. Group g
          => SystemParams g
          -> SecretKey g
          -> V.Vector (GroupScalar g)
          -> MAC g
          -> Bool
verifyMAC (SystemParams hs) (SecretKey x) msgs (MAC a e) =
     a /= groupIdentity
  && groupScalarMul a (e .+. x) == computeB hs msgs

------------------------------------------------------------------------
-- Presentation (without pseudonym)
------------------------------------------------------------------------

-- | Create a presentation proving knowledge of a valid BBS MAC
-- with selective disclosure.
--
-- The prover randomizes the MAC and produces a zero-knowledge
-- proof that they know the hidden attributes and the MAC exponent.
--
-- The sponge parameter should be initialized with appropriate protocol
-- and session identifiers for domain separation.
--
-- @disclosedIdxs@ contains 0-based indices of attributes to reveal.
present :: forall g sponge m.
           (Group g, DuplexSponge sponge, Unit sponge ~ Word8, MonadRandom m)
        => sponge
        -> SystemParams g
        -> V.Vector (GroupScalar g)
        -> MAC g
        -> V.Vector Int
        -> m (Presentation g)
present sponge (SystemParams hs) msgs (MAC a e) disclosedIdxs = do
  r1 <- scalarRandom
  r2 <- scalarRandom
  let b      = computeB hs msgs
      aPrime = groupScalarMul a (r1 .*. r2)
      bBar   = groupScalarMul b r1
      r3     = scalarInvert r1

      numAttrs = V.length msgs
      discSet  = V.toList disclosedIdxs
      hidden   = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]
      disclosed = V.map (\i -> (i, msgs V.! i)) disclosedIdxs

      -- Abar = A'^{-e} + Bbar^{r2} = A'^x (without knowing x)
      aBar = groupScalarMul aPrime (scalarNeg e)
               |+| groupScalarMul bBar r2

      -- H_1 = g + sum_{i in D} h_i * m_i
      h1 = V.foldl' (\acc (i, m_i) -> acc |+| groupScalarMul (hs V.! i) m_i)
             groupGenerator disclosed

      -- Witness: [negE, r2, r3, negM_{h_0}, ..., negM_{h_{k-1}}]
      negE = scalarNeg e
      hiddenNegMsgs = V.map (\i -> scalarNeg (msgs V.! i)) hidden
      witness = V.fromList [negE, r2, r3] V.++ hiddenNegMsgs

      relation = buildBBSRelation aPrime bBar aBar h1 hs hidden
      sponge'  = absorbPresentation @g sponge hs aPrime bBar disclosed

  proofBytes <- prove sponge' (newSchnorrProof relation) witness
  pure Presentation
    { presAPrime   = aPrime
    , presBBar     = bBar
    , presDisclosed = disclosed
    , presProof    = proofBytes
    }

-- | Verify a credential presentation using the secret key.
--
-- The verifier computes @Abar = x * A'@ and checks the proof.
verifyPresentation :: forall g sponge.
                      (Group g, DuplexSponge sponge, Unit sponge ~ Word8)
                   => sponge
                   -> SystemParams g
                   -> SecretKey g
                   -> Int
                   -> Presentation g
                   -> Either DeserializeError Bool
verifyPresentation sponge (SystemParams hs) (SecretKey x) numAttrs pres =
  let aPrime   = presAPrime pres
      bBar     = presBBar pres
      disclosed = presDisclosed pres
  in
  if aPrime == groupIdentity
    then Right False
  else
    let aBar = groupScalarMul aPrime x

        discSet = V.toList (V.map fst disclosed)
        hidden  = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]

        -- H_1 = g + sum_{i in D} h_i * m_i
        h1 = V.foldl' (\acc (i, m_i) -> acc |+| groupScalarMul (hs V.! i) m_i)
               groupGenerator disclosed

        relation = buildBBSRelation aPrime bBar aBar h1 hs hidden
        sponge'  = absorbPresentation @g sponge hs aPrime bBar disclosed
    in verify sponge' (newSchnorrProof relation) (presProof pres)

------------------------------------------------------------------------
-- Presentation with scoped pseudonym
------------------------------------------------------------------------

-- | Create a credential presentation with a scoped pseudonym.
--
-- One credential attribute (at index @prfKeyIdx@, 0-based) serves as the
-- Dodis-Yampolskiy PRF key. The pseudonym @P = (1 / (k + scope)) * G@ is
-- computed and a combined sigma protocol proof demonstrates both:
--
-- 1. Knowledge of a valid BBS MAC (hidden attributes)
-- 2. Correct PRF evaluation: binding the pseudonym to the same key @k@
--    in the credential.
--
-- The PRF key attribute must NOT appear in @disclosedIdxs@.
presentWithPseudonym :: forall g sponge m.
                        ( Group g, DuplexSponge sponge
                        , Unit sponge ~ Word8, MonadRandom m )
                     => sponge
                     -> SystemParams g
                     -> V.Vector (GroupScalar g)
                     -> MAC g
                     -> V.Vector Int
                     -> Int
                     -> GroupScalar g
                     -> m (PseudonymPresentation g)
presentWithPseudonym sponge (SystemParams hs) msgs (MAC a e)
                     disclosedIdxs prfKeyIdx scope = do
  r1 <- scalarRandom
  r2 <- scalarRandom
  let b      = computeB hs msgs
      aPrime = groupScalarMul a (r1 .*. r2)
      bBar   = groupScalarMul b r1
      r3     = scalarInvert r1

      numAttrs = V.length msgs
      discSet  = V.toList disclosedIdxs
      hidden   = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]
      disclosed = V.map (\i -> (i, msgs V.! i)) disclosedIdxs

      aBar = groupScalarMul aPrime (scalarNeg e)
               |+| groupScalarMul bBar r2

      h1 = V.foldl' (\acc (i, m_i) -> acc |+| groupScalarMul (hs V.! i) m_i)
             groupGenerator disclosed

      k = msgs V.! prfKeyIdx
      pseudonym = dyPRF @g k scope

      negE = scalarNeg e
      hiddenNegMsgs = V.map (\i -> scalarNeg (msgs V.! i)) hidden
      witness = V.fromList [negE, r2, r3] V.++ hiddenNegMsgs

      relation = buildBBSCombinedRelation aPrime bBar aBar h1 hs hidden
                   pseudonym scope prfKeyIdx
      sponge'  = absorbPseudonymPresentation @g
                   sponge hs aPrime bBar disclosed pseudonym scope

  proofBytes <- prove sponge' (newSchnorrProof relation) witness
  pure PseudonymPresentation
    { ppAPrime    = aPrime
    , ppBBar      = bBar
    , ppDisclosed = disclosed
    , ppPseudonym = pseudonym
    , ppScope     = scope
    , ppProof     = proofBytes
    }

-- | Verify a credential presentation with a scoped pseudonym.
verifyPseudonymPresentation :: forall g sponge.
                               ( Group g, DuplexSponge sponge
                               , Unit sponge ~ Word8 )
                            => sponge
                            -> SystemParams g
                            -> SecretKey g
                            -> Int
                            -> Int
                            -> PseudonymPresentation g
                            -> Either DeserializeError Bool
verifyPseudonymPresentation sponge (SystemParams hs) (SecretKey x)
                            numAttrs prfKeyIdx pres =
  let aPrime    = ppAPrime pres
      bBar      = ppBBar pres
      disclosed = ppDisclosed pres
      pseudonym = ppPseudonym pres
      scope     = ppScope pres
  in
  if aPrime == groupIdentity
    then Right False
  else if pseudonym == groupIdentity
    then Right False
  else
    let aBar = groupScalarMul aPrime x

        discSet = V.toList (V.map fst disclosed)
        hidden  = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]

        h1 = V.foldl' (\acc (i, m_i) -> acc |+| groupScalarMul (hs V.! i) m_i)
               groupGenerator disclosed

        relation = buildBBSCombinedRelation aPrime bBar aBar h1 hs hidden
                     pseudonym scope prfKeyIdx
        sponge'  = absorbPseudonymPresentation @g
                     sponge hs aPrime bBar disclosed pseudonym scope
    in verify sponge' (newSchnorrProof relation) (ppProof pres)

------------------------------------------------------------------------
-- Internal: compute B
------------------------------------------------------------------------

-- | Compute @B = g + Σ h_i * m_i@.
computeB :: forall g. Group g => V.Vector g -> V.Vector (GroupScalar g) -> g
computeB hs msgs =
  V.ifoldl' (\acc i m_i -> acc |+| groupScalarMul (hs V.! i) m_i)
    groupGenerator msgs

------------------------------------------------------------------------
-- Internal: linear relation builders
------------------------------------------------------------------------

-- | Build the linear relation for BBS presentation (no pseudonym).
--
-- Witness scalars (3 + k): [negE, r2, r3, negM_{h_0}, ..., negM_{h_{k-1}}]
--
-- Equation 1: Abar = negE * A' + r2 * Bbar
-- Equation 2: H_1  = r3 * Bbar + sum_j negM_{h_j} * h_{h_j}
--
-- Bbar is shared between both equations.
buildBBSRelation :: forall g. Group g
                 => g             -- ^ A'
                 -> g             -- ^ Bbar
                 -> g             -- ^ Abar
                 -> g             -- ^ H_1
                 -> V.Vector g    -- ^ system generators h_i
                 -> V.Vector Int  -- ^ hidden attribute indices
                 -> LinearRelation g
buildBBSRelation aPrime bBar aBar h1 hs hidden =
  buildLinearRelation_ $ do
    let k = V.length hidden

    -- Witness scalars: negE, r2, r3, negM_{h_0}, ..., negM_{h_{k-1}}
    scalarIds <- allocateScalars (3 + k)
    let negEId  = scalarIds V.! 0
        r2Id    = scalarIds V.! 1
        r3Id    = scalarIds V.! 2
        negMIds = V.drop 3 scalarIds

    -- Elements for Eq 1: A', Bbar (shared), Abar (image)
    eq1ElemIds <- allocateElements 3
    let aPrimeElemId = eq1ElemIds V.! 0
        bBarElemId   = eq1ElemIds V.! 1
        aBarElemId   = eq1ElemIds V.! 2

    -- Elements for Eq 2: h_{h_0}, ..., h_{h_{k-1}}, H_1 (image)
    -- Note: Bbar is shared from eq1 (bBarElemId)
    eq2ElemIds <- allocateElements (k + 1)
    let hElemIds  = V.take k eq2ElemIds
        h1ElemId  = eq2ElemIds V.! k

    -- Set element values
    setElements
      [ (aPrimeElemId, aPrime)
      , (bBarElemId, bBar)
      , (aBarElemId, aBar)
      ]
    setElements $ V.toList $ V.imap
      (\j hIdx -> (hElemIds V.! j, hs V.! hIdx)) hidden
    setElements [(h1ElemId, h1)]

    -- Eq 1: Abar = negE * A' + r2 * Bbar
    appendEquation aBarElemId
      [ (negEId, aPrimeElemId)
      , (r2Id,   bBarElemId)
      ]

    -- Eq 2: H_1 = r3 * Bbar + sum_j negM_{h_j} * h_{h_j}
    appendEquation h1ElemId $
      (r3Id, bBarElemId) :
      V.toList (V.imap (\j _ -> (negMIds V.! j, hElemIds V.! j)) hidden)

-- | Build the combined linear relation for BBS + Dodis-Yampolskiy PRF.
--
-- Same as 'buildBBSRelation' plus one extra equation:
--   Q = negM_{prfKeyPos} * (-P)
-- where Q = G - scope * P, sharing the negM scalar with Eq 2.
buildBBSCombinedRelation :: forall g. Group g
                         => g -> g -> g -> g -> V.Vector g -> V.Vector Int
                         -> g -> GroupScalar g -> Int
                         -> LinearRelation g
buildBBSCombinedRelation aPrime bBar aBar h1 hs hidden
                         pseudonym scope prfKeyIdx =
  buildLinearRelation_ $ do
    let k = V.length hidden

    -- Witness scalars: negE, r2, r3, negM_{h_0}, ..., negM_{h_{k-1}}
    scalarIds <- allocateScalars (3 + k)
    let negEId  = scalarIds V.! 0
        r2Id    = scalarIds V.! 1
        r3Id    = scalarIds V.! 2
        negMIds = V.drop 3 scalarIds

    -- Elements for Eq 1: A', Bbar (shared), Abar (image)
    eq1ElemIds <- allocateElements 3
    let aPrimeElemId = eq1ElemIds V.! 0
        bBarElemId   = eq1ElemIds V.! 1
        aBarElemId   = eq1ElemIds V.! 2

    -- Elements for Eq 2: h_{h_0}, ..., h_{h_{k-1}}, H_1 (image)
    eq2ElemIds <- allocateElements (k + 1)
    let hElemIds  = V.take k eq2ElemIds
        h1ElemId  = eq2ElemIds V.! k

    -- PRF elements: (-P), Q
    prfElemIds <- allocateElements 2
    let negPElemId = prfElemIds V.! 0
        qElemId    = prfElemIds V.! 1

    -- Set element values
    setElements
      [ (aPrimeElemId, aPrime)
      , (bBarElemId, bBar)
      , (aBarElemId, aBar)
      ]
    setElements $ V.toList $ V.imap
      (\j hIdx -> (hElemIds V.! j, hs V.! hIdx)) hidden
    setElements [(h1ElemId, h1)]

    let q = groupGenerator |-| (pseudonym |*| scope)
    setElements [(negPElemId, groupNeg pseudonym), (qElemId, q)]

    -- Eq 1: Abar = negE * A' + r2 * Bbar
    appendEquation aBarElemId
      [ (negEId, aPrimeElemId)
      , (r2Id,   bBarElemId)
      ]

    -- Eq 2: H_1 = r3 * Bbar + sum_j negM_{h_j} * h_{h_j}
    appendEquation h1ElemId $
      (r3Id, bBarElemId) :
      V.toList (V.imap (\j _ -> (negMIds V.! j, hElemIds V.! j)) hidden)

    -- Eq 3 (PRF): Q = negM_{prfKeyPos} * (-P)
    -- Since witness has negM_j = -m_j, and at prfKeyPos we have -k,
    -- this gives Q = (-k) * (-P) = k * P, which is correct.
    let prfKeyPos = case V.findIndex (== prfKeyIdx) hidden of
                      Just p  -> p
                      Nothing -> error
                        "presentWithPseudonym: PRF key index must be hidden"
    appendEquation qElemId [(negMIds V.! prfKeyPos, negPElemId)]

------------------------------------------------------------------------
-- Internal: Fiat-Shamir sponge absorption
------------------------------------------------------------------------

-- | Absorb presentation context into a Fiat-Shamir sponge:
-- system params (all h_i), A', Bbar, then length-prefixed sorted
-- disclosed pairs.
absorbPresentation :: forall g sponge.
                       (Group g, DuplexSponge sponge, Unit sponge ~ Word8)
                    => sponge -> V.Vector g -> g -> g
                    -> V.Vector (Int, GroupScalar g) -> sponge
absorbPresentation s0 hs aPrime bBar disclosed =
  let -- Absorb system params
      s1 = V.foldl'
             (\s h -> absorbDuplexSponge s (BS.unpack $ serializeElement h))
             s0 hs
      -- Absorb A' and Bbar
      s2 = absorbDuplexSponge s1 (BS.unpack $ serializeElement aPrime)
      s3 = absorbDuplexSponge s2 (BS.unpack $ serializeElement bBar)
      -- Absorb disclosed pairs
      sorted = sortBy (comparing fst) (V.toList disclosed)
      s4 = absorbDuplexSponge s3 (BS.unpack $ i2osp 4 (length sorted))
      s5 = foldl
             (\s (i, m) ->
               absorbDuplexSponge
                 (absorbDuplexSponge s (BS.unpack $ i2osp 4 i))
                 (BS.unpack $ serializeScalar m))
             s4 sorted
  in s5

-- | Absorb pseudonym presentation context: the base presentation context
-- plus the pseudonym point and scope scalar.
absorbPseudonymPresentation :: forall g sponge.
                                ( Group g, DuplexSponge sponge
                                , Unit sponge ~ Word8 )
                             => sponge -> V.Vector g -> g -> g
                             -> V.Vector (Int, GroupScalar g)
                             -> g -> GroupScalar g -> sponge
absorbPseudonymPresentation s0 hs aPrime bBar disclosed pseudonym scope =
  let s1 = absorbPresentation @g s0 hs aPrime bBar disclosed
      s2 = absorbDuplexSponge s1 (BS.unpack $ serializeElement pseudonym)
      s3 = absorbDuplexSponge s2 (BS.unpack $ serializeScalar scope)
  in s3
