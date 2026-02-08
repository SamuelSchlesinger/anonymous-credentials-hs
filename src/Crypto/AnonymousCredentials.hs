{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module: Crypto.AnonymousCredentials
--
-- __This library has not been independently audited. Use at your own risk.__
--
-- BBS MAC (algebraic MAC) and keyed-verification anonymous credential
-- presentation, based on the construction from "Algebraic MACs and
-- Keyed-Verification Anonymous Credentials" (Chase, Meiklejohn, Zaverucha,
-- CCS 2014).
--
-- The MAC is computed over a prime-order group without pairings. Each MAC
-- includes auxiliary base points derived from the secret key, which allow
-- the credential holder to construct zero-knowledge proofs of knowledge
-- of hidden attributes using sigma protocols.
--
-- The presentation protocol provides:
--
-- * __Unlinkability__: each presentation is randomized with a fresh scalar,
--   so different presentations of the same credential are unlinkable.
--
-- * __Selective disclosure__: the holder can reveal a subset of attributes
--   while proving knowledge of the remaining hidden attributes in zero
--   knowledge.
--
-- * __Scoped pseudonyms__: via the Dodis-Yampolskiy PRF, a credential
--   attribute can serve as a PRF key that produces a unique, deterministic
--   pseudonym per scope label. The proof binds the pseudonym to the
--   credential by sharing the PRF key witness across both the MAC and
--   PRF equations.
--
-- Verification is keyed: the verifier must hold the secret key.
module Crypto.AnonymousCredentials
  ( -- * Secret Key
    SecretKey(..)
  , keygen
    -- * MAC
  , MAC(..)
  , bbsMAC
  , verifyMAC
    -- * Presentation
  , Presentation(..)
  , present
  , verifyPresentation
    -- * Dodis-Yampolskiy PRF
  , dyPRF
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

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- | Secret key for BBS MAC supporting @L@ attributes.
--
-- Contains @L + 1@ scalars: @x_0@ (base key) and @x_1, ..., x_L@
-- (per-attribute keys).
newtype SecretKey g = SecretKey
  { skScalars :: V.Vector (GroupScalar g) }

-- | BBS MAC on a vector of messages.
--
-- The MAC consists of:
--
-- * A random base point @u@
-- * The MAC value @u' = u_0 + Σ_{i=0}^{L-1} m_i * u_{i+1}@
-- * Auxiliary base points @u_j = x_j * u@ for @j = 0, ..., L@
--
-- The auxiliary bases enable the credential holder to construct
-- zero-knowledge proofs of knowledge of hidden attributes.
data MAC g = MAC
  { macU      :: g
  , macUPrime :: g
  , macUBases :: V.Vector g
  }

-- | A credential presentation with selective disclosure.
--
-- Contains a randomized MAC, disclosed attribute values, and a
-- Fiat-Shamir proof of knowledge of the hidden attributes.
data Presentation g = Presentation
  { presU         :: g
  -- ^ Randomized base point @U = r * u@
  , presUPrime    :: g
  -- ^ Randomized MAC value @U' = r * u'@
  , presUBases    :: V.Vector g
  -- ^ Randomized bases @U_j = r * u_j@ for @j = 0, ..., L@
  , presDisclosed :: V.Vector (Int, GroupScalar g)
  -- ^ @(index, message)@ pairs for disclosed attributes (0-based indices)
  , presProof     :: ByteString
  -- ^ Compact Fiat-Shamir proof of knowledge of hidden attributes
  }

-- | A credential presentation with a scoped pseudonym.
--
-- In addition to selective disclosure, the holder proves correct
-- evaluation of the Dodis-Yampolskiy PRF using a credential attribute
-- as the PRF key. The pseudonym is deterministic per (key, scope) pair
-- but unlinkable across different scopes.
data PseudonymPresentation g = PseudonymPresentation
  { ppU         :: g
  -- ^ Randomized base point @U = r * u@
  , ppUPrime    :: g
  -- ^ Randomized MAC value @U' = r * u'@
  , ppUBases    :: V.Vector g
  -- ^ Randomized bases @U_j = r * u_j@ for @j = 0, ..., L@
  , ppDisclosed :: V.Vector (Int, GroupScalar g)
  -- ^ @(index, message)@ pairs for disclosed attributes (0-based indices)
  , ppPseudonym :: g
  -- ^ Scoped pseudonym @P = (1 / (k + scope)) * G@
  , ppScope     :: GroupScalar g
  -- ^ The scope label used to derive the pseudonym
  , ppProof     :: ByteString
  -- ^ Compact Fiat-Shamir proof of knowledge of hidden attributes
  -- and correct PRF evaluation
  }

------------------------------------------------------------------------
-- Key generation and MAC
------------------------------------------------------------------------

-- | Generate a secret key for @numAttrs@-attribute MACs.
keygen :: forall g m. (Group g, MonadRandom m) => Int -> m (SecretKey g)
keygen numAttrs = SecretKey <$> V.replicateM (numAttrs + 1) scalarRandom

-- | Compute a BBS MAC on a vector of messages.
--
-- The messages vector must have exactly @L@ elements, matching the number
-- of attributes the secret key was generated for.
bbsMAC :: forall g m. (Group g, MonadRandom m)
       => SecretKey g
       -> V.Vector (GroupScalar g)
       -> m (MAC g)
bbsMAC (SecretKey sk) msgs = do
  u <- groupRandom
  let uBases = V.map (groupScalarMul u) sk
      uPrime = V.ifoldl'
        (\acc i m_i -> acc |+| groupScalarMul (uBases V.! (i + 1)) m_i)
        (V.head uBases)
        msgs
  pure (MAC u uPrime uBases)

-- | Verify a BBS MAC using the secret key.
verifyMAC :: forall g. Group g
          => SecretKey g
          -> V.Vector (GroupScalar g)
          -> MAC g
          -> Bool
verifyMAC (SecretKey sk) msgs (MAC u uPrime uBases) =
     u /= groupIdentity
  && V.length uBases == V.length sk
  && V.length msgs == V.length sk - 1
  && V.and (V.zipWith (\x_j u_j -> u_j == groupScalarMul u x_j) sk uBases)
  && uPrime == expected
  where
    expected = V.ifoldl'
      (\acc i m_i -> acc |+| groupScalarMul (uBases V.! (i + 1)) m_i)
      (V.head uBases)
      msgs

------------------------------------------------------------------------
-- Dodis-Yampolskiy PRF
------------------------------------------------------------------------

-- | Evaluate the Dodis-Yampolskiy PRF.
--
-- Given a PRF key @k@ and a scope label, computes:
--
-- @P = (1 / (k + scope)) * G@
--
-- where @G@ is the group generator. Different scope labels produce
-- different pseudonyms for the same key, enabling scoped unlinkability.
--
-- The scope can be derived from an arbitrary label by hashing it into
-- a scalar via 'Crypto.Sigma.Scalar.scalarFromUniformBytes'.
dyPRF :: forall g. Group g => GroupScalar g -> GroupScalar g -> g
dyPRF k scope = groupGenerator |*| scalarInvert (k .+. scope)

------------------------------------------------------------------------
-- Presentation (without pseudonym)
------------------------------------------------------------------------

-- | Create a presentation proving knowledge of a valid MAC with selective
-- disclosure.
--
-- The holder randomizes the MAC and produces a zero-knowledge proof that
-- they know the hidden attributes. The sponge parameter should be
-- initialized with appropriate protocol and session identifiers for domain
-- separation (e.g. via 'Crypto.Sigma.FiatShamir.makeIV').
--
-- @disclosedIdxs@ contains 0-based indices of attributes to reveal.
present :: forall g sponge m.
           (Group g, DuplexSponge sponge, Unit sponge ~ Word8, MonadRandom m)
        => sponge
        -> V.Vector (GroupScalar g)
        -> MAC g
        -> V.Vector Int
        -> m (Presentation g)
present sponge msgs (MAC u uPrime uBases) disclosedIdxs = do
  r <- scalarRandom
  let rU      = groupScalarMul u r
      rUPrime = groupScalarMul uPrime r
      rUBases = V.map (\b -> groupScalarMul b r) uBases

      numAttrs = V.length msgs
      discSet  = V.toList disclosedIdxs
      hidden   = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]
      disclosed = V.map (\i -> (i, msgs V.! i)) disclosedIdxs
      hiddenMsgs = V.map (\i -> msgs V.! i) hidden

      v = computeV rUPrime rUBases disclosed
      relation = buildMACRelation rUBases v hidden
      sponge' = absorbPresentation @g sponge rU rUPrime rUBases disclosed

  proofBytes <- prove sponge' (newSchnorrProof relation) hiddenMsgs
  pure Presentation
    { presU         = rU
    , presUPrime    = rUPrime
    , presUBases    = rUBases
    , presDisclosed = disclosed
    , presProof     = proofBytes
    }

-- | Verify a credential presentation using the secret key.
--
-- Checks that:
--
-- 1. The randomized base point is not the identity.
-- 2. Each randomized base @U_j@ equals @x_j * U@ (key consistency).
-- 3. The Fiat-Shamir proof of knowledge of hidden attributes verifies.
verifyPresentation :: forall g sponge.
                      (Group g, DuplexSponge sponge, Unit sponge ~ Word8)
                   => sponge
                   -> SecretKey g
                   -> Int
                   -> Presentation g
                   -> Either DeserializeError Bool
verifyPresentation sponge (SecretKey sk) numAttrs pres =
  let rU       = presU pres
      rUPrime  = presUPrime pres
      rUBases  = presUBases pres
      disclosed = presDisclosed pres
  in
  if rU == groupIdentity
    then Right False
  else if V.length rUBases /= V.length sk
    then Right False
  else if not (V.and (V.zipWith (\x_j u_j -> u_j == groupScalarMul rU x_j) sk rUBases))
    then Right False
  else
    let discSet = V.toList (V.map fst disclosed)
        hidden  = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]
        v = computeV rUPrime rUBases disclosed
        relation = buildMACRelation rUBases v hidden
        sponge' = absorbPresentation @g sponge rU rUPrime rUBases disclosed
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
-- 1. Knowledge of a valid MAC (hidden attributes)
-- 2. Correct PRF evaluation: @(k + scope) * P = G@, binding the pseudonym
--    to the same key @k@ in the credential.
--
-- The PRF key attribute must NOT appear in @disclosedIdxs@.
presentWithPseudonym :: forall g sponge m.
                        ( Group g, DuplexSponge sponge
                        , Unit sponge ~ Word8, MonadRandom m )
                     => sponge
                     -> V.Vector (GroupScalar g)
                     -> MAC g
                     -> V.Vector Int
                     -> Int
                     -> GroupScalar g
                     -> m (PseudonymPresentation g)
presentWithPseudonym sponge msgs (MAC u uPrime uBases) disclosedIdxs prfKeyIdx scope = do
  r <- scalarRandom
  let rU      = groupScalarMul u r
      rUPrime = groupScalarMul uPrime r
      rUBases = V.map (\b -> groupScalarMul b r) uBases

      numAttrs = V.length msgs
      discSet  = V.toList disclosedIdxs
      hidden   = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]
      disclosed = V.map (\i -> (i, msgs V.! i)) disclosedIdxs
      hiddenMsgs = V.map (\i -> msgs V.! i) hidden

      k = msgs V.! prfKeyIdx
      pseudonym = dyPRF @g k scope

      v = computeV rUPrime rUBases disclosed
      relation = buildCombinedRelation rUBases v hidden pseudonym scope prfKeyIdx
      sponge' = absorbPseudonymPresentation @g
                  sponge rU rUPrime rUBases disclosed pseudonym scope

  proofBytes <- prove sponge' (newSchnorrProof relation) hiddenMsgs
  pure PseudonymPresentation
    { ppU         = rU
    , ppUPrime    = rUPrime
    , ppUBases    = rUBases
    , ppDisclosed = disclosed
    , ppPseudonym = pseudonym
    , ppScope     = scope
    , ppProof     = proofBytes
    }

-- | Verify a credential presentation with a scoped pseudonym.
--
-- In addition to the standard MAC checks, verifies:
--
-- 4. The pseudonym is not the identity.
-- 5. The combined proof binds the pseudonym to the hidden PRF key
--    attribute via the Dodis-Yampolskiy relation.
verifyPseudonymPresentation :: forall g sponge.
                               ( Group g, DuplexSponge sponge
                               , Unit sponge ~ Word8 )
                            => sponge
                            -> SecretKey g
                            -> Int
                            -> Int
                            -> PseudonymPresentation g
                            -> Either DeserializeError Bool
verifyPseudonymPresentation sponge (SecretKey sk) numAttrs prfKeyIdx pres =
  let rU        = ppU pres
      rUPrime   = ppUPrime pres
      rUBases   = ppUBases pres
      disclosed = ppDisclosed pres
      pseudonym = ppPseudonym pres
      scope     = ppScope pres
  in
  if rU == groupIdentity
    then Right False
  else if pseudonym == groupIdentity
    then Right False
  else if V.length rUBases /= V.length sk
    then Right False
  else if not (V.and (V.zipWith (\x_j u_j -> u_j == groupScalarMul rU x_j) sk rUBases))
    then Right False
  else
    let discSet = V.toList (V.map fst disclosed)
        hidden  = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]
        v = computeV rUPrime rUBases disclosed
        relation = buildCombinedRelation rUBases v hidden pseudonym scope prfKeyIdx
        sponge' = absorbPseudonymPresentation @g
                    sponge rU rUPrime rUBases disclosed pseudonym scope
    in verify sponge' (newSchnorrProof relation) (ppProof pres)

------------------------------------------------------------------------
-- Internal: proof image computation
------------------------------------------------------------------------

-- | Compute the proof image:
-- @V = U' - U_0 - Σ_{(j,m_j) ∈ disclosed} m_j * U_{j+1}@
computeV :: forall g. Group g
         => g -> V.Vector g -> V.Vector (Int, GroupScalar g) -> g
computeV rUPrime rUBases disclosed =
  rUPrime |-| V.head rUBases |-|
    V.foldl' (\acc (j, m_j) -> acc |+| groupScalarMul (rUBases V.! (j + 1)) m_j)
      groupIdentity
      disclosed

------------------------------------------------------------------------
-- Internal: linear relation builders
------------------------------------------------------------------------

-- | Build the linear relation for the MAC-only ZK proof:
-- @V = Σ_{i ∈ hidden} m_i * U_{i+1}@
buildMACRelation :: forall g. Group g
                 => V.Vector g -> g -> V.Vector Int -> LinearRelation g
buildMACRelation rUBases v hiddenIndices =
  buildLinearRelation_ $ do
    let n = V.length hiddenIndices
    scalarIds <- allocateScalars n
    elemIds   <- allocateElements (n + 1)
    let basisIds = V.take n elemIds
        imageId  = elemIds V.! n
    setElements $ V.toList $ V.imap
      (\idx i -> (basisIds V.! idx, rUBases V.! (i + 1))) hiddenIndices
    setElements [(imageId, v)]
    appendEquation imageId
      (V.toList $ V.zip scalarIds basisIds)

-- | Build a combined linear relation for MAC + Dodis-Yampolskiy PRF:
--
-- Equation 1 (MAC):  @V = Σ_{i ∈ hidden} m_i * U_{i+1}@
-- Equation 2 (PRF):  @Q = k * P@  where @Q = G - scope * P@
--
-- Both equations share the scalar variable for the PRF key @k@,
-- binding the pseudonym to the credential.
buildCombinedRelation :: forall g. Group g
                      => V.Vector g
                      -> g
                      -> V.Vector Int
                      -> g
                      -> GroupScalar g
                      -> Int
                      -> LinearRelation g
buildCombinedRelation rUBases v hiddenIndices pseudonym scope prfKeyIdx =
  buildLinearRelation_ $ do
    let n = V.length hiddenIndices
    scalarIds <- allocateScalars n

    -- MAC elements: n bases + 1 image
    macElemIds <- allocateElements (n + 1)
    let macBasisIds = V.take n macElemIds
        macImageId  = macElemIds V.! n

    -- PRF elements: 1 base (P) + 1 image (Q)
    prfElemIds <- allocateElements 2
    let prfBasisId = prfElemIds V.! 0
        prfImageId = prfElemIds V.! 1

    -- Set MAC basis elements: U_{i+1} for each hidden attribute i
    setElements $ V.toList $ V.imap
      (\idx i -> (macBasisIds V.! idx, rUBases V.! (i + 1))) hiddenIndices
    setElements [(macImageId, v)]

    -- Set PRF elements: P (pseudonym) and Q = G - scope * P
    let q = groupGenerator |-| (pseudonym |*| scope)
    setElements [(prfBasisId, pseudonym), (prfImageId, q)]

    -- MAC equation: V = Σ_{i∈H} m_i * U_{i+1}
    appendEquation macImageId
      (V.toList $ V.zip scalarIds macBasisIds)

    -- PRF equation: Q = k * P
    -- k's scalar variable is at the position of prfKeyIdx in hiddenIndices
    let kPos = case V.findIndex (== prfKeyIdx) hiddenIndices of
                 Just p  -> p
                 Nothing -> error
                   "presentWithPseudonym: PRF key index must be hidden"
    appendEquation prfImageId [(scalarIds V.! kPos, prfBasisId)]

------------------------------------------------------------------------
-- Internal: Fiat-Shamir sponge absorption
------------------------------------------------------------------------

-- | Absorb presentation context into a Fiat-Shamir sponge for domain
-- separation: U, U', all U_j bases, and sorted disclosed (index, message)
-- pairs.
absorbPresentation :: forall g sponge.
                      (Group g, DuplexSponge sponge, Unit sponge ~ Word8)
                   => sponge -> g -> g -> V.Vector g
                   -> V.Vector (Int, GroupScalar g) -> sponge
absorbPresentation s0 rU rUPrime rUBases disclosed =
  let s1 = absorbDuplexSponge s0 (BS.unpack $ serializeElement rU)
      s2 = absorbDuplexSponge s1 (BS.unpack $ serializeElement rUPrime)
      s3 = V.foldl'
             (\s b -> absorbDuplexSponge s (BS.unpack $ serializeElement b))
             s2 rUBases
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
                            => sponge -> g -> g -> V.Vector g
                            -> V.Vector (Int, GroupScalar g)
                            -> g -> GroupScalar g -> sponge
absorbPseudonymPresentation s0 rU rUPrime rUBases disclosed pseudonym scope =
  let s1 = absorbPresentation @g s0 rU rUPrime rUBases disclosed
      s2 = absorbDuplexSponge s1 (BS.unpack $ serializeElement pseudonym)
      s3 = absorbDuplexSponge s2 (BS.unpack $ serializeScalar scope)
  in s3
