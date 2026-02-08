{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module: Crypto.AnonymousCredentials.Internal
--
-- Shared utilities for anonymous credential schemes.
module Crypto.AnonymousCredentials.Internal
  ( dyPRF
  ) where

import Crypto.Sigma.Group
import Crypto.Sigma.Scalar

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
