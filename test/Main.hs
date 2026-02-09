{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Vector as V

import Crypto.Sigma.Scalar
import Crypto.Sigma.Group
import Crypto.Sigma.FiatShamir (makeIV)
import Crypto.Sigma.Shake128 (Shake128Sponge)
import Crypto.Sigma.Curve25519.Ristretto255

import Crypto.AnonymousCredentials
import qualified Crypto.AnonymousCredentials.CMZ as CMZ

type G = Ristretto255Point
type S = Ristretto255Scalar

sponge :: Shake128Sponge
sponge = makeIV "bbs-mac-test" "session-0"

cmzSponge :: Shake128Sponge
cmzSponge = makeIV "cmz-mac-test" "session-0"

main :: IO ()
main = defaultMain $ testGroup "Anonymous Credentials"
  [ testGroup "BBS MAC" [macTests, presentationTests, prfTests, pseudonymTests]
  , testGroup "CMZ MAC" [cmzMacTests, cmzPresentationTests, cmzPseudonymTests]
  ]

------------------------------------------------------------------------
-- MAC tests
------------------------------------------------------------------------

macTests :: TestTree
macTests = testGroup "MAC"
  [ testCase "MAC verifies with correct messages" $ do
      params <- setupParams @G 3
      sk <- keygen @G
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC params sk msgs
      assertBool "MAC should verify" (verifyMAC params sk msgs mac)

  , testCase "MAC rejects wrong messages" $ do
      params <- setupParams @G 3
      sk <- keygen @G
      msgs <- V.replicateM 3 (scalarRandom @S)
      wrongMsgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC params sk msgs
      assertBool "MAC should not verify with wrong messages"
        (not (verifyMAC params sk wrongMsgs mac))

  , testCase "MAC rejects wrong key" $ do
      params <- setupParams @G 3
      sk1 <- keygen @G
      sk2 <- keygen @G
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC params sk1 msgs
      assertBool "MAC should not verify with wrong key"
        (not (verifyMAC params sk2 msgs mac))

  , testCase "MAC works with 0 attributes" $ do
      params <- setupParams @G 0
      sk <- keygen @G
      let msgs = V.empty
      mac <- bbsMAC params sk msgs
      assertBool "MAC should verify" (verifyMAC params sk msgs mac)

  , testCase "MAC works with 1 attribute" $ do
      params <- setupParams @G 1
      sk <- keygen @G
      msgs <- V.replicateM 1 (scalarRandom @S)
      mac <- bbsMAC params sk msgs
      assertBool "MAC should verify" (verifyMAC params sk msgs mac)

  , testCase "MAC works with 20 attributes" $ do
      params <- setupParams @G 20
      sk <- keygen @G
      msgs <- V.replicateM 20 (scalarRandom @S)
      mac <- bbsMAC params sk msgs
      assertBool "MAC should verify" (verifyMAC params sk msgs mac)

  , testCase "A^{e+x} == B correctness" $ do
      params <- setupParams @G 3
      sk <- keygen @G
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC params sk msgs
      let hs = spGenerators params
          x  = skScalar sk
          e  = macE mac
          a  = macA mac
          b  = V.ifoldl' (\acc i m_i -> acc |+| groupScalarMul (hs V.! i) m_i)
                 (groupGenerator :: G) msgs
      assertBool "A^{e+x} should equal B"
        (groupScalarMul a (e .+. x) == b)
  ]

------------------------------------------------------------------------
-- Presentation tests (without pseudonym)
------------------------------------------------------------------------

presentationTests :: TestTree
presentationTests = testGroup "Presentation"
  [ testCase "all messages hidden" $ do
      params <- setupParams @G 3
      sk <- keygen @G
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC params sk msgs
      pres <- present @G @Shake128Sponge sponge params msgs mac V.empty
      case verifyPresentation @G @Shake128Sponge sponge params sk 3 pres of
        Left err  -> assertFailure ("deserialize error: " ++ show err)
        Right ok  -> assertBool "presentation should verify" ok

  , testCase "all messages disclosed" $ do
      params <- setupParams @G 3
      sk <- keygen @G
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC params sk msgs
      pres <- present @G @Shake128Sponge sponge params msgs mac (V.fromList [0,1,2])
      case verifyPresentation @G @Shake128Sponge sponge params sk 3 pres of
        Left err  -> assertFailure ("deserialize error: " ++ show err)
        Right ok  -> assertBool "presentation should verify" ok

  , testCase "partial disclosure" $ do
      params <- setupParams @G 5
      sk <- keygen @G
      msgs <- V.replicateM 5 (scalarRandom @S)
      mac <- bbsMAC params sk msgs
      pres <- present @G @Shake128Sponge sponge params msgs mac (V.fromList [1,3])
      case verifyPresentation @G @Shake128Sponge sponge params sk 5 pres of
        Left err  -> assertFailure ("deserialize error: " ++ show err)
        Right ok  -> assertBool "presentation should verify" ok

  , testCase "wrong secret key rejects" $ do
      params <- setupParams @G 3
      sk1 <- keygen @G
      sk2 <- keygen @G
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC params sk1 msgs
      pres <- present @G @Shake128Sponge sponge params msgs mac V.empty
      case verifyPresentation @G @Shake128Sponge sponge params sk2 3 pres of
        Left _err -> pure ()
        Right ok  -> assertBool "should reject with wrong key" (not ok)

  , testCase "presentations are unlinkable (different randomizations)" $ do
      params <- setupParams @G 2
      sk <- keygen @G
      msgs <- V.replicateM 2 (scalarRandom @S)
      mac <- bbsMAC params sk msgs
      pres1 <- present @G @Shake128Sponge sponge params msgs mac V.empty
      pres2 <- present @G @Shake128Sponge sponge params msgs mac V.empty
      case verifyPresentation @G @Shake128Sponge sponge params sk 2 pres1 of
        Left err -> assertFailure ("pres1 deserialize error: " ++ show err)
        Right ok -> assertBool "pres1 should verify" ok
      case verifyPresentation @G @Shake128Sponge sponge params sk 2 pres2 of
        Left err -> assertFailure ("pres2 deserialize error: " ++ show err)
        Right ok -> assertBool "pres2 should verify" ok
      assertBool "presentations should have different A'"
        (presAPrime pres1 /= presAPrime pres2)

  , testCase "0 attributes, all hidden" $ do
      params <- setupParams @G 0
      sk <- keygen @G
      let msgs = V.empty
      mac <- bbsMAC params sk msgs
      pres <- present @G @Shake128Sponge sponge params msgs mac V.empty
      case verifyPresentation @G @Shake128Sponge sponge params sk 0 pres of
        Left err  -> assertFailure ("deserialize error: " ++ show err)
        Right ok  -> assertBool "presentation should verify" ok

  , testCase "20 attributes, partial disclosure" $ do
      params <- setupParams @G 20
      sk <- keygen @G
      msgs <- V.replicateM 20 (scalarRandom @S)
      mac <- bbsMAC params sk msgs
      pres <- present @G @Shake128Sponge sponge params msgs mac (V.fromList [0,5,10,15,19])
      case verifyPresentation @G @Shake128Sponge sponge params sk 20 pres of
        Left err  -> assertFailure ("deserialize error: " ++ show err)
        Right ok  -> assertBool "presentation should verify" ok

  , testCase "wrong sponge session rejects" $ do
      let sponge1 = makeIV @Shake128Sponge "bbs-mac-test" "session-A"
          sponge2 = makeIV @Shake128Sponge "bbs-mac-test" "session-B"
      params <- setupParams @G 3
      sk <- keygen @G
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC params sk msgs
      pres <- present @G @Shake128Sponge sponge1 params msgs mac V.empty
      case verifyPresentation @G @Shake128Sponge sponge2 params sk 3 pres of
        Left _err -> pure ()
        Right ok  -> assertBool "should reject with wrong session" (not ok)
  ]

------------------------------------------------------------------------
-- Dodis-Yampolskiy PRF tests
------------------------------------------------------------------------

prfTests :: TestTree
prfTests = testGroup "Dodis-Yampolskiy PRF"
  [ testCase "PRF is deterministic" $ do
      k <- scalarRandom @S
      scope <- scalarRandom @S
      let p1 = dyPRF @G k scope
          p2 = dyPRF @G k scope
      assertBool "same key and scope should produce same pseudonym" (p1 == p2)

  , testCase "different scopes produce different pseudonyms" $ do
      k <- scalarRandom @S
      scope1 <- scalarRandom @S
      scope2 <- scalarRandom @S
      let p1 = dyPRF @G k scope1
          p2 = dyPRF @G k scope2
      assertBool "different scopes should produce different pseudonyms" (p1 /= p2)

  , testCase "different keys produce different pseudonyms" $ do
      k1 <- scalarRandom @S
      k2 <- scalarRandom @S
      scope <- scalarRandom @S
      let p1 = dyPRF @G k1 scope
          p2 = dyPRF @G k2 scope
      assertBool "different keys should produce different pseudonyms" (p1 /= p2)

  , testCase "PRF satisfies (k + scope) * P = G" $ do
      k <- scalarRandom @S
      scope <- scalarRandom @S
      let p = dyPRF @G k scope
          lhs = groupScalarMul p (k .+. scope)
      assertBool "PRF correctness: (k + scope) * P = G"
        (lhs == (groupGenerator :: G))
  ]

------------------------------------------------------------------------
-- Pseudonym presentation tests
------------------------------------------------------------------------

pseudonymTests :: TestTree
pseudonymTests = testGroup "Pseudonym Presentation"
  [ testCase "pseudonym presentation verifies (all hidden)" $ do
      params <- setupParams @G 3
      sk <- keygen @G
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      m2 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1, m2]  -- k is at index 0
      mac <- bbsMAC params sk msgs
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge params msgs mac V.empty 0 scope
      case verifyPseudonymPresentation @G @Shake128Sponge sponge params sk 3 0 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "pseudonym presentation should verify" ok

  , testCase "pseudonym presentation verifies (partial disclosure)" $ do
      params <- setupParams @G 4
      sk <- keygen @G
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      m2 <- scalarRandom @S
      m3 <- scalarRandom @S
      scope <- scalarRandom @S
      -- k at index 2, disclose indices 0 and 3
      let msgs = V.fromList [m1, m2, k, m3]
      mac <- bbsMAC params sk msgs
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge params msgs mac (V.fromList [0, 3]) 2 scope
      case verifyPseudonymPresentation @G @Shake128Sponge sponge params sk 4 2 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "pseudonym presentation should verify" ok

  , testCase "pseudonym matches standalone PRF evaluation" $ do
      params <- setupParams @G 2
      sk <- keygen @G
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- bbsMAC params sk msgs
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge params msgs mac V.empty 0 scope
      let expected = dyPRF @G k scope
      assertBool "pseudonym should match direct PRF evaluation"
        (ppPseudonym pres == expected)

  , testCase "same key and scope produce same pseudonym across presentations" $ do
      params <- setupParams @G 2
      sk <- keygen @G
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- bbsMAC params sk msgs
      pres1 <- presentWithPseudonym @G @Shake128Sponge
                 sponge params msgs mac V.empty 0 scope
      pres2 <- presentWithPseudonym @G @Shake128Sponge
                 sponge params msgs mac V.empty 0 scope
      -- Both should verify
      case verifyPseudonymPresentation @G @Shake128Sponge sponge params sk 2 0 pres1 of
        Left err -> assertFailure ("pres1 error: " ++ show err)
        Right ok -> assertBool "pres1 should verify" ok
      case verifyPseudonymPresentation @G @Shake128Sponge sponge params sk 2 0 pres2 of
        Left err -> assertFailure ("pres2 error: " ++ show err)
        Right ok -> assertBool "pres2 should verify" ok
      -- Pseudonyms should be identical (same key, same scope)
      assertBool "pseudonyms should match" (ppPseudonym pres1 == ppPseudonym pres2)
      -- But randomizations should differ
      assertBool "A' should differ" (ppAPrime pres1 /= ppAPrime pres2)

  , testCase "different scopes produce different pseudonyms" $ do
      params <- setupParams @G 2
      sk <- keygen @G
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope1 <- scalarRandom @S
      scope2 <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- bbsMAC params sk msgs
      pres1 <- presentWithPseudonym @G @Shake128Sponge
                 sponge params msgs mac V.empty 0 scope1
      pres2 <- presentWithPseudonym @G @Shake128Sponge
                 sponge params msgs mac V.empty 0 scope2
      assertBool "different scopes should give different pseudonyms"
        (ppPseudonym pres1 /= ppPseudonym pres2)

  , testCase "wrong secret key rejects pseudonym presentation" $ do
      params <- setupParams @G 2
      sk1 <- keygen @G
      sk2 <- keygen @G
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- bbsMAC params sk1 msgs
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge params msgs mac V.empty 0 scope
      case verifyPseudonymPresentation @G @Shake128Sponge sponge params sk2 2 0 pres of
        Left _   -> pure ()
        Right ok -> assertBool "should reject wrong key" (not ok)

  , testCase "wrong PRF key index rejects" $ do
      params <- setupParams @G 3
      sk <- keygen @G
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      m2 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1, m2]
      mac <- bbsMAC params sk msgs
      -- Present with prfKeyIdx=0 but verify with prfKeyIdx=1
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge params msgs mac V.empty 0 scope
      case verifyPseudonymPresentation @G @Shake128Sponge sponge params sk 3 1 pres of
        Left _   -> pure ()
        Right ok -> assertBool "should reject wrong PRF key index" (not ok)

  , testCase "20 attributes with pseudonym" $ do
      params <- setupParams @G 20
      sk <- keygen @G
      k <- scalarRandom @S
      otherMsgs <- V.replicateM 19 (scalarRandom @S)
      scope <- scalarRandom @S
      let msgs = V.cons k otherMsgs  -- k at index 0
      mac <- bbsMAC params sk msgs
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge params msgs mac (V.fromList [5,10,15]) 0 scope
      case verifyPseudonymPresentation @G @Shake128Sponge sponge params sk 20 0 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "presentation should verify" ok
  ]

------------------------------------------------------------------------
-- CMZ MAC tests
------------------------------------------------------------------------

cmzMacTests :: TestTree
cmzMacTests = testGroup "MAC"
  [ testCase "MAC verifies with correct messages" $ do
      (sk, _pp) <- CMZ.keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk msgs
      assertBool "MAC should verify" (CMZ.verifyMAC sk msgs mac)

  , testCase "MAC rejects wrong messages" $ do
      (sk, _pp) <- CMZ.keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      wrongMsgs <- V.replicateM 3 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk msgs
      assertBool "MAC should not verify with wrong messages"
        (not (CMZ.verifyMAC sk wrongMsgs mac))

  , testCase "MAC rejects wrong key" $ do
      (sk1, _pp1) <- CMZ.keygen @G 3
      (sk2, _pp2) <- CMZ.keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk1 msgs
      assertBool "MAC should not verify with wrong key"
        (not (CMZ.verifyMAC sk2 msgs mac))

  , testCase "MAC works with 0 attributes" $ do
      (sk, _pp) <- CMZ.keygen @G 0
      let msgs = V.empty
      mac <- CMZ.cmzMAC sk msgs
      assertBool "MAC should verify" (CMZ.verifyMAC sk msgs mac)

  , testCase "MAC works with 1 attribute" $ do
      (sk, _pp) <- CMZ.keygen @G 1
      msgs <- V.replicateM 1 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk msgs
      assertBool "MAC should verify" (CMZ.verifyMAC sk msgs mac)

  , testCase "MAC works with 20 attributes" $ do
      (sk, _pp) <- CMZ.keygen @G 20
      msgs <- V.replicateM 20 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk msgs
      assertBool "MAC should verify" (CMZ.verifyMAC sk msgs mac)
  ]

------------------------------------------------------------------------
-- CMZ Presentation tests
------------------------------------------------------------------------

cmzPresentationTests :: TestTree
cmzPresentationTests = testGroup "Presentation"
  [ testCase "all messages hidden" $ do
      (sk, pp) <- CMZ.keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk msgs
      pres <- CMZ.present @G @Shake128Sponge cmzSponge pp msgs mac V.empty
      case CMZ.verifyPresentation @G @Shake128Sponge cmzSponge sk pp 3 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "presentation should verify" ok

  , testCase "all messages disclosed" $ do
      (sk, pp) <- CMZ.keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk msgs
      pres <- CMZ.present @G @Shake128Sponge cmzSponge pp msgs mac (V.fromList [0,1,2])
      case CMZ.verifyPresentation @G @Shake128Sponge cmzSponge sk pp 3 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "presentation should verify" ok

  , testCase "partial disclosure" $ do
      (sk, pp) <- CMZ.keygen @G 5
      msgs <- V.replicateM 5 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk msgs
      pres <- CMZ.present @G @Shake128Sponge cmzSponge pp msgs mac (V.fromList [1,3])
      case CMZ.verifyPresentation @G @Shake128Sponge cmzSponge sk pp 5 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "presentation should verify" ok

  , testCase "wrong secret key rejects" $ do
      (sk1, pp1) <- CMZ.keygen @G 3
      (sk2, _pp2) <- CMZ.keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk1 msgs
      pres <- CMZ.present @G @Shake128Sponge cmzSponge pp1 msgs mac V.empty
      case CMZ.verifyPresentation @G @Shake128Sponge cmzSponge sk2 pp1 3 pres of
        Left _err -> pure ()
        Right ok  -> assertBool "should reject with wrong key" (not ok)

  , testCase "presentations are unlinkable (different randomizations)" $ do
      (sk, pp) <- CMZ.keygen @G 2
      msgs <- V.replicateM 2 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk msgs
      pres1 <- CMZ.present @G @Shake128Sponge cmzSponge pp msgs mac V.empty
      pres2 <- CMZ.present @G @Shake128Sponge cmzSponge pp msgs mac V.empty
      case CMZ.verifyPresentation @G @Shake128Sponge cmzSponge sk pp 2 pres1 of
        Left err -> assertFailure ("pres1 deserialize error: " ++ show err)
        Right ok -> assertBool "pres1 should verify" ok
      case CMZ.verifyPresentation @G @Shake128Sponge cmzSponge sk pp 2 pres2 of
        Left err -> assertFailure ("pres2 deserialize error: " ++ show err)
        Right ok -> assertBool "pres2 should verify" ok
      assertBool "presentations should have different U"
        (CMZ.presU pres1 /= CMZ.presU pres2)

  , testCase "0 attributes, all hidden" $ do
      (sk, pp) <- CMZ.keygen @G 0
      let msgs = V.empty
      mac <- CMZ.cmzMAC sk msgs
      pres <- CMZ.present @G @Shake128Sponge cmzSponge pp msgs mac V.empty
      case CMZ.verifyPresentation @G @Shake128Sponge cmzSponge sk pp 0 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "presentation should verify" ok

  , testCase "20 attributes, partial disclosure" $ do
      (sk, pp) <- CMZ.keygen @G 20
      msgs <- V.replicateM 20 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk msgs
      pres <- CMZ.present @G @Shake128Sponge cmzSponge pp msgs mac
                (V.fromList [0,5,10,15,19])
      case CMZ.verifyPresentation @G @Shake128Sponge cmzSponge sk pp 20 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "presentation should verify" ok

  , testCase "wrong sponge session rejects" $ do
      let sponge1 = makeIV @Shake128Sponge "cmz-mac-test" "session-A"
          sponge2 = makeIV @Shake128Sponge "cmz-mac-test" "session-B"
      (sk, pp) <- CMZ.keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- CMZ.cmzMAC sk msgs
      pres <- CMZ.present @G @Shake128Sponge sponge1 pp msgs mac V.empty
      case CMZ.verifyPresentation @G @Shake128Sponge sponge2 sk pp 3 pres of
        Left _err -> pure ()
        Right ok  -> assertBool "should reject with wrong session" (not ok)
  ]

------------------------------------------------------------------------
-- CMZ Pseudonym presentation tests
------------------------------------------------------------------------

cmzPseudonymTests :: TestTree
cmzPseudonymTests = testGroup "Pseudonym Presentation"
  [ testCase "pseudonym presentation verifies (all hidden)" $ do
      (sk, pp) <- CMZ.keygen @G 3
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      m2 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1, m2]
      mac <- CMZ.cmzMAC sk msgs
      pres <- CMZ.presentWithPseudonym @G @Shake128Sponge
                cmzSponge pp msgs mac V.empty 0 scope
      case CMZ.verifyPseudonymPresentation @G @Shake128Sponge
             cmzSponge sk pp 3 0 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "pseudonym presentation should verify" ok

  , testCase "pseudonym presentation verifies (partial disclosure)" $ do
      (sk, pp) <- CMZ.keygen @G 4
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      m2 <- scalarRandom @S
      m3 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [m1, m2, k, m3]
      mac <- CMZ.cmzMAC sk msgs
      pres <- CMZ.presentWithPseudonym @G @Shake128Sponge
                cmzSponge pp msgs mac (V.fromList [0, 3]) 2 scope
      case CMZ.verifyPseudonymPresentation @G @Shake128Sponge
             cmzSponge sk pp 4 2 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "pseudonym presentation should verify" ok

  , testCase "pseudonym matches standalone PRF evaluation" $ do
      (sk, pp) <- CMZ.keygen @G 2
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- CMZ.cmzMAC sk msgs
      pres <- CMZ.presentWithPseudonym @G @Shake128Sponge
                cmzSponge pp msgs mac V.empty 0 scope
      let expected = dyPRF @G k scope
      assertBool "pseudonym should match direct PRF evaluation"
        (CMZ.ppPseudonym pres == expected)

  , testCase "same key and scope produce same pseudonym across presentations" $ do
      (sk, pp) <- CMZ.keygen @G 2
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- CMZ.cmzMAC sk msgs
      pres1 <- CMZ.presentWithPseudonym @G @Shake128Sponge
                 cmzSponge pp msgs mac V.empty 0 scope
      pres2 <- CMZ.presentWithPseudonym @G @Shake128Sponge
                 cmzSponge pp msgs mac V.empty 0 scope
      case CMZ.verifyPseudonymPresentation @G @Shake128Sponge
             cmzSponge sk pp 2 0 pres1 of
        Left err -> assertFailure ("pres1 error: " ++ show err)
        Right ok -> assertBool "pres1 should verify" ok
      case CMZ.verifyPseudonymPresentation @G @Shake128Sponge
             cmzSponge sk pp 2 0 pres2 of
        Left err -> assertFailure ("pres2 error: " ++ show err)
        Right ok -> assertBool "pres2 should verify" ok
      assertBool "pseudonyms should match"
        (CMZ.ppPseudonym pres1 == CMZ.ppPseudonym pres2)
      assertBool "U should differ"
        (CMZ.ppU pres1 /= CMZ.ppU pres2)

  , testCase "different scopes produce different pseudonyms" $ do
      (sk, pp) <- CMZ.keygen @G 2
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope1 <- scalarRandom @S
      scope2 <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- CMZ.cmzMAC sk msgs
      pres1 <- CMZ.presentWithPseudonym @G @Shake128Sponge
                 cmzSponge pp msgs mac V.empty 0 scope1
      pres2 <- CMZ.presentWithPseudonym @G @Shake128Sponge
                 cmzSponge pp msgs mac V.empty 0 scope2
      assertBool "different scopes should give different pseudonyms"
        (CMZ.ppPseudonym pres1 /= CMZ.ppPseudonym pres2)

  , testCase "wrong secret key rejects pseudonym presentation" $ do
      (sk1, pp1) <- CMZ.keygen @G 2
      (sk2, _pp2) <- CMZ.keygen @G 2
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- CMZ.cmzMAC sk1 msgs
      pres <- CMZ.presentWithPseudonym @G @Shake128Sponge
                cmzSponge pp1 msgs mac V.empty 0 scope
      case CMZ.verifyPseudonymPresentation @G @Shake128Sponge
             cmzSponge sk2 pp1 2 0 pres of
        Left _   -> pure ()
        Right ok -> assertBool "should reject wrong key" (not ok)

  , testCase "wrong PRF key index rejects" $ do
      (sk, pp) <- CMZ.keygen @G 3
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      m2 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1, m2]
      mac <- CMZ.cmzMAC sk msgs
      pres <- CMZ.presentWithPseudonym @G @Shake128Sponge
                cmzSponge pp msgs mac V.empty 0 scope
      case CMZ.verifyPseudonymPresentation @G @Shake128Sponge
             cmzSponge sk pp 3 1 pres of
        Left _   -> pure ()
        Right ok -> assertBool "should reject wrong PRF key index" (not ok)

  , testCase "20 attributes with pseudonym" $ do
      (sk, pp) <- CMZ.keygen @G 20
      k <- scalarRandom @S
      otherMsgs <- V.replicateM 19 (scalarRandom @S)
      scope <- scalarRandom @S
      let msgs = V.cons k otherMsgs
      mac <- CMZ.cmzMAC sk msgs
      pres <- CMZ.presentWithPseudonym @G @Shake128Sponge
                cmzSponge pp msgs mac (V.fromList [5,10,15]) 0 scope
      case CMZ.verifyPseudonymPresentation @G @Shake128Sponge
             cmzSponge sk pp 20 0 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "presentation should verify" ok
  ]
