{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module: Crypto.AnonymousCredentials.CMZ
--
-- __This library has not been independently audited. Use at your own risk.__
--
-- CMZ MAC_GGM (algebraic MAC) and keyed-verification anonymous credential
-- presentation, based on the construction from "Algebraic MACs and
-- Keyed-Verification Anonymous Credentials" (Chase, Meiklejohn, Zaverucha,
-- CCS 2014).
--
-- Unlike the BBS variant (see "Crypto.AnonymousCredentials.BBS"), the CMZ
-- MAC is compact — just two group elements @(U, U')@ — but requires
-- public parameters @H@ (a second generator) and @X_i = x_i * H@ for
-- Pedersen commitments during presentation.
--
-- The core MAC equation is the same:
-- @U' = (x_0 + Σ x_i * m_i) * U@.
--
-- The presentation protocol provides:
--
-- * __Unlinkability__: each presentation is randomized with a fresh scalar.
--
-- * __Selective disclosure__: the holder reveals a subset of attributes
--   while proving knowledge of the remaining hidden attributes in zero
--   knowledge via Pedersen commitments.
--
-- * __Scoped pseudonyms__: via the Dodis-Yampolskiy PRF.
--
-- Verification is keyed: the verifier must hold the secret key.
module Crypto.AnonymousCredentials.CMZ
  ( -- * Secret Key and Public Parameters
    SecretKey(..)
  , PublicParams(..)
  , keygen
    -- * MAC
  , MAC(..)
  , cmzMAC
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

-- | Secret key for CMZ MAC supporting @L@ attributes.
--
-- Contains @L + 1@ scalars: @x_0@ (base key) and @x_1, ..., x_L@
-- (per-attribute keys).
newtype SecretKey g = SecretKey
  { skScalars :: V.Vector (GroupScalar g) }

-- | Public parameters for CMZ presentations.
--
-- Contains a second generator @H@ (with unknown discrete log to @G@)
-- and public key elements @X_i = x_i * H@ for Pedersen commitments.
data PublicParams g = PublicParams
  { cmzH  :: g            -- ^ Second generator
  , cmzXi :: V.Vector g   -- ^ @X_i = x_i * H@ for @i = 0, ..., L@
  }

-- | CMZ MAC on a vector of messages.
--
-- The MAC consists of just two group elements:
--
-- * A random base point @U = b * G@
-- * The MAC value @U' = (x_0 + Σ x_i * m_i) * U@
data MAC g = MAC
  { macU      :: g   -- ^ Random base point
  , macUPrime :: g   -- ^ MAC value
  }

-- | A credential presentation with selective disclosure.
--
-- Contains a re-randomized MAC, Pedersen commitments for hidden
-- attributes, disclosed attribute values, and a Fiat-Shamir proof.
data Presentation g = Presentation
  { presU            :: g
  -- ^ Re-randomized base point @U_hat = a * U@
  , presUPrimeCommit :: g
  -- ^ Committed MAC value @U_hat' + r * G@
  , presCommitments  :: V.Vector g
  -- ^ Pedersen commitments @commit_i = m_i * U_hat + z_i * H@ (hidden only)
  , presDisclosed    :: V.Vector (Int, GroupScalar g)
  -- ^ @(index, message)@ pairs for disclosed attributes (0-based indices)
  , presProof        :: ByteString
  -- ^ Compact Fiat-Shamir proof
  }

-- | A credential presentation with a scoped pseudonym.
data PseudonymPresentation g = PseudonymPresentation
  { ppU            :: g
  -- ^ Re-randomized base point @U_hat = a * U@
  , ppUPrimeCommit :: g
  -- ^ Committed MAC value @U_hat' + r * G@
  , ppCommitments  :: V.Vector g
  -- ^ Pedersen commitments (hidden only)
  , ppDisclosed    :: V.Vector (Int, GroupScalar g)
  -- ^ @(index, message)@ pairs for disclosed attributes (0-based indices)
  , ppPseudonym    :: g
  -- ^ Scoped pseudonym @P = (1 / (k + scope)) * G@
  , ppScope        :: GroupScalar g
  -- ^ The scope label used to derive the pseudonym
  , ppProof        :: ByteString
  -- ^ Compact Fiat-Shamir proof
  }

------------------------------------------------------------------------
-- Key generation and MAC
------------------------------------------------------------------------

-- | Generate a secret key and public parameters for @numAttrs@-attribute MACs.
keygen :: forall g m. (Group g, MonadRandom m)
       => Int -> m (SecretKey g, PublicParams g)
keygen numAttrs = do
  h  <- groupRandom
  xs <- V.replicateM (numAttrs + 1) scalarRandom
  let xis = V.map (groupScalarMul h) xs
  pure (SecretKey xs, PublicParams h xis)

-- | Compute a CMZ MAC on a vector of messages.
--
-- The messages vector must have exactly @L@ elements, matching the number
-- of attributes the secret key was generated for.
cmzMAC :: forall g m. (Group g, MonadRandom m)
       => SecretKey g
       -> V.Vector (GroupScalar g)
       -> m (MAC g)
cmzMAC (SecretKey sk) msgs = do
  u <- groupRandom
  let x0     = V.head sk
      xs     = V.tail sk
      expo   = V.ifoldl' (\acc i m_i -> acc .+. (xs V.! i .*. m_i)) x0 msgs
      uPrime = groupScalarMul u expo
  pure (MAC u uPrime)

-- | Verify a CMZ MAC using the secret key.
verifyMAC :: forall g. Group g
          => SecretKey g
          -> V.Vector (GroupScalar g)
          -> MAC g
          -> Bool
verifyMAC (SecretKey sk) msgs (MAC u uPrime) =
     u /= groupIdentity
  && V.length msgs == V.length sk - 1
  && uPrime == expected
  where
    x0     = V.head sk
    xs     = V.tail sk
    expo   = V.ifoldl' (\acc i m_i -> acc .+. (xs V.! i .*. m_i)) x0 msgs
    expected = groupScalarMul u expo

------------------------------------------------------------------------
-- Presentation (without pseudonym)
------------------------------------------------------------------------

-- | Create a presentation proving knowledge of a valid CMZ MAC with
-- selective disclosure.
--
-- The holder re-randomizes the MAC, commits to hidden attributes using
-- Pedersen commitments, and produces a zero-knowledge proof.
present :: forall g sponge m.
           (Group g, DuplexSponge sponge, Unit sponge ~ Word8, MonadRandom m)
        => sponge
        -> PublicParams g
        -> V.Vector (GroupScalar g)
        -> MAC g
        -> V.Vector Int
        -> m (Presentation g)
present sponge pp msgs (MAC u uPrime) disclosedIdxs = do
  let h = cmzH pp
      xis = cmzXi pp

  -- Re-randomize
  a <- scalarRandom
  let uHat  = groupScalarMul u a
      uHat' = groupScalarMul uPrime a

  -- Commit U'
  r <- scalarRandom
  let uPrimeCommit = uHat' |+| groupScalarMul groupGenerator r

  -- Partition attributes
  let numAttrs = V.length msgs
      discSet  = V.toList disclosedIdxs
      hidden   = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]
      disclosed = V.map (\i -> (i, msgs V.! i)) disclosedIdxs
      k = V.length hidden

  -- Pedersen commitments for hidden attributes
  zs <- V.replicateM k scalarRandom
  let commits = V.imap (\j hIdx ->
        let m_i = msgs V.! hIdx
            z_j = zs V.! j
        in groupScalarMul uHat m_i |+| groupScalarMul h z_j) hidden

  -- V = sum(z_j * X_{h_j}) - r * G
  let vVal = V.ifoldl' (\acc j hIdx ->
               acc |+| groupScalarMul (xis V.! (hIdx + 1)) (zs V.! j))
             groupIdentity hidden
             |-| groupScalarMul groupGenerator r

  -- Build witness: [m_{h_0}, ..., m_{h_{k-1}}, z_0, ..., z_{k-1}, negR]
  let negR = scalarNeg r
      hiddenMsgs = V.map (\i -> msgs V.! i) hidden
      witness = hiddenMsgs V.++ zs V.++ V.singleton negR

  let relation = buildCMZRelation uHat h commits xis vVal hidden
      sponge'  = absorbCMZPresentation @g sponge pp uHat uPrimeCommit commits disclosed

  proofBytes <- prove sponge' (newSchnorrProof relation) witness
  pure Presentation
    { presU            = uHat
    , presUPrimeCommit = uPrimeCommit
    , presCommitments  = commits
    , presDisclosed    = disclosed
    , presProof        = proofBytes
    }

-- | Verify a credential presentation using the secret key.
verifyPresentation :: forall g sponge.
                      (Group g, DuplexSponge sponge, Unit sponge ~ Word8)
                   => sponge
                   -> SecretKey g
                   -> PublicParams g
                   -> Int
                   -> Presentation g
                   -> Either DeserializeError Bool
verifyPresentation sponge (SecretKey sk) pp numAttrs pres =
  let uHat         = presU pres
      uPrimeCommit = presUPrimeCommit pres
      commits      = presCommitments pres
      disclosed    = presDisclosed pres
      h            = cmzH pp
      xis          = cmzXi pp
  in
  let discSet = V.toList (V.map fst disclosed)
      hidden  = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]
  in
  if uHat == groupIdentity
    then Right False
  else if V.length commits /= V.length hidden
    then Right False
  else if V.any (\(dj, _) -> dj < 0 || dj >= numAttrs) disclosed
    then Right False
  else
    let -- V = x_0 * U_hat + sum(x_{h_i} * commit_i)
        --   + sum(x_{d_j} * m_j * U_hat) - UPrimeCommit
        vVal = groupScalarMul uHat (V.head sk)
             |+| V.ifoldl' (\acc j hIdx ->
                   acc |+| groupScalarMul (commits V.! j) (sk V.! (hIdx + 1)))
                 groupIdentity hidden
             |+| V.foldl' (\acc (dj, m_j) ->
                   acc |+| groupScalarMul uHat (sk V.! (dj + 1) .*. m_j))
                 groupIdentity disclosed
             |-| uPrimeCommit

        relation = buildCMZRelation uHat h commits xis vVal hidden
        sponge'  = absorbCMZPresentation @g sponge pp uHat uPrimeCommit commits disclosed
    in verify sponge' (newSchnorrProof relation) (presProof pres)

------------------------------------------------------------------------
-- Presentation with scoped pseudonym
------------------------------------------------------------------------

-- | Create a credential presentation with a scoped pseudonym.
presentWithPseudonym :: forall g sponge m.
                        ( Group g, DuplexSponge sponge
                        , Unit sponge ~ Word8, MonadRandom m )
                     => sponge
                     -> PublicParams g
                     -> V.Vector (GroupScalar g)
                     -> MAC g
                     -> V.Vector Int
                     -> Int
                     -> GroupScalar g
                     -> m (PseudonymPresentation g)
presentWithPseudonym sponge pp msgs (MAC u uPrime) disclosedIdxs prfKeyIdx scope = do
  let h = cmzH pp
      xis = cmzXi pp

  -- Re-randomize
  a <- scalarRandom
  let uHat  = groupScalarMul u a
      uHat' = groupScalarMul uPrime a

  -- Commit U'
  r <- scalarRandom
  let uPrimeCommit = uHat' |+| groupScalarMul groupGenerator r

  -- Partition attributes
  let numAttrs = V.length msgs
      discSet  = V.toList disclosedIdxs
      hidden   = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]
      disclosed = V.map (\i -> (i, msgs V.! i)) disclosedIdxs
      k = V.length hidden

  -- Pedersen commitments for hidden attributes
  zs <- V.replicateM k scalarRandom
  let commits = V.imap (\j hIdx ->
        let m_i = msgs V.! hIdx
            z_j = zs V.! j
        in groupScalarMul uHat m_i |+| groupScalarMul h z_j) hidden

  -- Pseudonym
  let prfKey    = msgs V.! prfKeyIdx
      pseudonym = dyPRF @g prfKey scope

  -- V = sum(z_j * X_{h_j}) - r * G
  let vVal = V.ifoldl' (\acc j hIdx ->
               acc |+| groupScalarMul (xis V.! (hIdx + 1)) (zs V.! j))
             groupIdentity hidden
             |-| groupScalarMul groupGenerator r

  -- Build witness: [m_{h_0}, ..., m_{h_{k-1}}, z_0, ..., z_{k-1}, negR]
  let negR = scalarNeg r
      hiddenMsgs = V.map (\i -> msgs V.! i) hidden
      witness = hiddenMsgs V.++ zs V.++ V.singleton negR

  let relation = buildCMZCombinedRelation uHat h commits xis vVal hidden
                   pseudonym scope prfKeyIdx
      sponge'  = absorbCMZPseudonymPresentation @g
                   sponge pp uHat uPrimeCommit commits disclosed pseudonym scope

  proofBytes <- prove sponge' (newSchnorrProof relation) witness
  pure PseudonymPresentation
    { ppU            = uHat
    , ppUPrimeCommit = uPrimeCommit
    , ppCommitments  = commits
    , ppDisclosed    = disclosed
    , ppPseudonym    = pseudonym
    , ppScope        = scope
    , ppProof        = proofBytes
    }

-- | Verify a credential presentation with a scoped pseudonym.
verifyPseudonymPresentation :: forall g sponge.
                               ( Group g, DuplexSponge sponge
                               , Unit sponge ~ Word8 )
                            => sponge
                            -> SecretKey g
                            -> PublicParams g
                            -> Int
                            -> Int
                            -> PseudonymPresentation g
                            -> Either DeserializeError Bool
verifyPseudonymPresentation sponge (SecretKey sk) pp numAttrs prfKeyIdx pres =
  let uHat         = ppU pres
      uPrimeCommit = ppUPrimeCommit pres
      commits      = ppCommitments pres
      disclosed    = ppDisclosed pres
      pseudonym    = ppPseudonym pres
      scope        = ppScope pres
      h            = cmzH pp
      xis          = cmzXi pp
  in
  let discSet = V.toList (V.map fst disclosed)
      hidden  = V.fromList [i | i <- [0..numAttrs-1], i `notElem` discSet]
  in
  if uHat == groupIdentity
    then Right False
  else if pseudonym == groupIdentity
    then Right False
  else if V.length commits /= V.length hidden
    then Right False
  else if V.any (\(dj, _) -> dj < 0 || dj >= numAttrs) disclosed
    then Right False
  else
    let vVal = groupScalarMul uHat (V.head sk)
             |+| V.ifoldl' (\acc j hIdx ->
                   acc |+| groupScalarMul (commits V.! j) (sk V.! (hIdx + 1)))
                 groupIdentity hidden
             |+| V.foldl' (\acc (dj, m_j) ->
                   acc |+| groupScalarMul uHat (sk V.! (dj + 1) .*. m_j))
                 groupIdentity disclosed
             |-| uPrimeCommit

        relation = buildCMZCombinedRelation uHat h commits xis vVal hidden
                     pseudonym scope prfKeyIdx
        sponge'  = absorbCMZPseudonymPresentation @g
                     sponge pp uHat uPrimeCommit commits disclosed pseudonym scope
    in verify sponge' (newSchnorrProof relation) (ppProof pres)

------------------------------------------------------------------------
-- Internal: linear relation builders
------------------------------------------------------------------------

-- | Build the linear relation for CMZ presentation (no pseudonym).
--
-- Scalars (2k+1): [m_{h_0}, ..., m_{h_{k-1}}, z_0, ..., z_{k-1}, negR]
--
-- Equations (k+1):
--   For j = 0..k-1: commit_j = m_{h_j} * U_hat + z_j * H
--   V = sum_{j=0}^{k-1}(z_j * X_{h_j}) + negR * G
buildCMZRelation :: forall g. Group g
                 => g              -- ^ U_hat
                 -> g              -- ^ H
                 -> V.Vector g     -- ^ commits
                 -> V.Vector g     -- ^ X_i (public params, 0..L)
                 -> g              -- ^ V
                 -> V.Vector Int   -- ^ hidden indices
                 -> LinearRelation g
buildCMZRelation uHat h commits xis vVal hidden =
  buildLinearRelation_ $ do
    let k = V.length hidden

    -- Scalars: k message scalars, k blinding scalars, 1 negR
    scalarIds <- allocateScalars (2 * k + 1)
    let msgScalarIds = V.take k scalarIds
        zScalarIds   = V.slice k k scalarIds
        negRScalarId = scalarIds V.! (2 * k)

    -- Elements for commitment equations: U_hat, H, k commit images
    commitElemIds <- allocateElements (k + 2)
    let uHatElemId = commitElemIds V.! 0
        hElemId    = commitElemIds V.! 1
        commitImageIds = V.slice 2 k commitElemIds

    -- Elements for V equation: k X_{h_j} bases, G, V image
    vElemIds <- allocateElements (k + 2)
    let xElemIds  = V.take k vElemIds
        gElemId   = vElemIds V.! k
        vImageId  = vElemIds V.! (k + 1)

    -- Set element values
    setElements [(uHatElemId, uHat), (hElemId, h)]
    setElements $ V.toList $ V.imap
      (\j _ -> (commitImageIds V.! j, commits V.! j)) hidden
    setElements $ V.toList $ V.imap
      (\j hIdx -> (xElemIds V.! j, xis V.! (hIdx + 1))) hidden
    setElements [(gElemId, groupGenerator), (vImageId, vVal)]

    -- Commitment equations: commit_j = m_{h_j} * U_hat + z_j * H
    V.iforM_ hidden $ \j _hIdx ->
      appendEquation (commitImageIds V.! j)
        [ (msgScalarIds V.! j, uHatElemId)
        , (zScalarIds V.! j,   hElemId)
        ]

    -- V equation: V = sum(z_j * X_{h_j}) + negR * G
    appendEquation vImageId $
      V.toList (V.imap (\j _ -> (zScalarIds V.! j, xElemIds V.! j)) hidden)
      ++ [(negRScalarId, gElemId)]

-- | Build the combined linear relation for CMZ + Dodis-Yampolskiy PRF.
--
-- Same as 'buildCMZRelation' plus one extra equation:
--   Q = k * P   where Q = G - scope * P
buildCMZCombinedRelation :: forall g. Group g
                         => g -> g -> V.Vector g -> V.Vector g -> g
                         -> V.Vector Int -> g -> GroupScalar g -> Int
                         -> LinearRelation g
buildCMZCombinedRelation uHat h commits xis vVal hidden
                         pseudonym scope prfKeyIdx =
  buildLinearRelation_ $ do
    let k = V.length hidden

    -- Scalars: k message scalars, k blinding scalars, 1 negR
    scalarIds <- allocateScalars (2 * k + 1)
    let msgScalarIds = V.take k scalarIds
        zScalarIds   = V.slice k k scalarIds
        negRScalarId = scalarIds V.! (2 * k)

    -- Elements for commitment equations: U_hat, H, k commit images
    commitElemIds <- allocateElements (k + 2)
    let uHatElemId = commitElemIds V.! 0
        hElemId    = commitElemIds V.! 1
        commitImageIds = V.slice 2 k commitElemIds

    -- Elements for V equation: k X_{h_j} bases, G, V image
    vElemIds <- allocateElements (k + 2)
    let xElemIds  = V.take k vElemIds
        gElemId   = vElemIds V.! k
        vImageId  = vElemIds V.! (k + 1)

    -- PRF elements: P, Q
    prfElemIds <- allocateElements 2
    let prfBasisId = prfElemIds V.! 0
        prfImageId = prfElemIds V.! 1

    -- Set element values
    setElements [(uHatElemId, uHat), (hElemId, h)]
    setElements $ V.toList $ V.imap
      (\j _ -> (commitImageIds V.! j, commits V.! j)) hidden
    setElements $ V.toList $ V.imap
      (\j hIdx -> (xElemIds V.! j, xis V.! (hIdx + 1))) hidden
    setElements [(gElemId, groupGenerator), (vImageId, vVal)]

    let q = groupGenerator |-| (pseudonym |*| scope)
    setElements [(prfBasisId, pseudonym), (prfImageId, q)]

    -- Commitment equations
    V.iforM_ hidden $ \j _hIdx ->
      appendEquation (commitImageIds V.! j)
        [ (msgScalarIds V.! j, uHatElemId)
        , (zScalarIds V.! j,   hElemId)
        ]

    -- V equation
    appendEquation vImageId $
      V.toList (V.imap (\j _ -> (zScalarIds V.! j, xElemIds V.! j)) hidden)
      ++ [(negRScalarId, gElemId)]

    -- PRF equation: Q = k * P
    let kPos = case V.findIndex (== prfKeyIdx) hidden of
                 Just p  -> p
                 Nothing -> error
                   "presentWithPseudonym: PRF key index must be hidden"
    appendEquation prfImageId [(msgScalarIds V.! kPos, prfBasisId)]

------------------------------------------------------------------------
-- Internal: Fiat-Shamir sponge absorption
------------------------------------------------------------------------

-- | Absorb CMZ presentation context into a Fiat-Shamir sponge.
--
-- Absorbs the public parameters @H@ and all @X_i@ for domain separation,
-- followed by the presentation-specific values.
absorbCMZPresentation :: forall g sponge.
                         (Group g, DuplexSponge sponge, Unit sponge ~ Word8)
                      => sponge -> PublicParams g -> g -> g -> V.Vector g
                      -> V.Vector (Int, GroupScalar g) -> sponge
absorbCMZPresentation s0 pp uHat uPrimeCommit commits disclosed =
  let -- Absorb public parameters for domain separation
      s1 = absorbDuplexSponge s0 (BS.unpack $ serializeElement (cmzH pp))
      s2 = V.foldl'
             (\s xi -> absorbDuplexSponge s (BS.unpack $ serializeElement xi))
             s1 (cmzXi pp)
      -- Absorb presentation values
      s3 = absorbDuplexSponge s2 (BS.unpack $ serializeElement uHat)
      s4 = absorbDuplexSponge s3 (BS.unpack $ serializeElement uPrimeCommit)
      s5 = V.foldl'
             (\s c -> absorbDuplexSponge s (BS.unpack $ serializeElement c))
             s4 commits
      sorted = sortBy (comparing fst) (V.toList disclosed)
      s6 = absorbDuplexSponge s5 (BS.unpack $ i2osp 4 (length sorted))
      s7 = foldl
             (\s (i, m) ->
               absorbDuplexSponge
                 (absorbDuplexSponge s (BS.unpack $ i2osp 4 i))
                 (BS.unpack $ serializeScalar m))
             s6 sorted
  in s7

-- | Absorb CMZ pseudonym presentation context.
absorbCMZPseudonymPresentation :: forall g sponge.
                                  ( Group g, DuplexSponge sponge
                                  , Unit sponge ~ Word8 )
                               => sponge -> PublicParams g -> g -> g -> V.Vector g
                               -> V.Vector (Int, GroupScalar g)
                               -> g -> GroupScalar g -> sponge
absorbCMZPseudonymPresentation s0 pp uHat uPrimeCommit commits disclosed pseudonym scope =
  let s1 = absorbCMZPresentation @g s0 pp uHat uPrimeCommit commits disclosed
      s2 = absorbDuplexSponge s1 (BS.unpack $ serializeElement pseudonym)
      s3 = absorbDuplexSponge s2 (BS.unpack $ serializeScalar scope)
  in s3
