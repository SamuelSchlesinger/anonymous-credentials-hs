-- |
-- Module: Crypto.AnonymousCredentials
--
-- Re-exports BBS MAC and Dodis-Yampolskiy PRF for backwards compatibility.
-- For the CMZ MAC_GGM scheme, use "Crypto.AnonymousCredentials.CMZ".
module Crypto.AnonymousCredentials
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
    -- * Dodis-Yampolskiy PRF
  , dyPRF
    -- * Presentation with Scoped Pseudonym
  , PseudonymPresentation(..)
  , presentWithPseudonym
  , verifyPseudonymPresentation
  ) where

import Crypto.AnonymousCredentials.BBS
import Crypto.AnonymousCredentials.Internal (dyPRF)
