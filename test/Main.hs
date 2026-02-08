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

type G = Ristretto255Point
type S = Ristretto255Scalar

sponge :: Shake128Sponge
sponge = makeIV "bbs-mac-test" "session-0"

main :: IO ()
main = defaultMain $ testGroup "BBS MAC" [macTests, presentationTests, prfTests, pseudonymTests]

------------------------------------------------------------------------
-- MAC tests
------------------------------------------------------------------------

macTests :: TestTree
macTests = testGroup "MAC"
  [ testCase "MAC verifies with correct messages" $ do
      sk <- keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC sk msgs
      assertBool "MAC should verify" (verifyMAC sk msgs mac)

  , testCase "MAC rejects wrong messages" $ do
      sk <- keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      wrongMsgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC sk msgs
      assertBool "MAC should not verify with wrong messages" (not (verifyMAC sk wrongMsgs mac))

  , testCase "MAC rejects wrong key" $ do
      sk1 <- keygen @G 3
      sk2 <- keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC sk1 msgs
      assertBool "MAC should not verify with wrong key" (not (verifyMAC sk2 msgs mac))

  , testCase "MAC works with 0 attributes" $ do
      sk <- keygen @G 0
      let msgs = V.empty
      mac <- bbsMAC sk msgs
      assertBool "MAC should verify" (verifyMAC sk msgs mac)

  , testCase "MAC works with 1 attribute" $ do
      sk <- keygen @G 1
      msgs <- V.replicateM 1 (scalarRandom @S)
      mac <- bbsMAC sk msgs
      assertBool "MAC should verify" (verifyMAC sk msgs mac)

  , testCase "MAC works with 20 attributes" $ do
      sk <- keygen @G 20
      msgs <- V.replicateM 20 (scalarRandom @S)
      mac <- bbsMAC sk msgs
      assertBool "MAC should verify" (verifyMAC sk msgs mac)
  ]

------------------------------------------------------------------------
-- Presentation tests (without pseudonym)
------------------------------------------------------------------------

presentationTests :: TestTree
presentationTests = testGroup "Presentation"
  [ testCase "all messages hidden" $ do
      sk <- keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC sk msgs
      pres <- present @G @Shake128Sponge sponge msgs mac V.empty
      case verifyPresentation @G @Shake128Sponge sponge sk 3 pres of
        Left err  -> assertFailure ("deserialize error: " ++ show err)
        Right ok  -> assertBool "presentation should verify" ok

  , testCase "all messages disclosed" $ do
      sk <- keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC sk msgs
      pres <- present @G @Shake128Sponge sponge msgs mac (V.fromList [0,1,2])
      case verifyPresentation @G @Shake128Sponge sponge sk 3 pres of
        Left err  -> assertFailure ("deserialize error: " ++ show err)
        Right ok  -> assertBool "presentation should verify" ok

  , testCase "partial disclosure" $ do
      sk <- keygen @G 5
      msgs <- V.replicateM 5 (scalarRandom @S)
      mac <- bbsMAC sk msgs
      pres <- present @G @Shake128Sponge sponge msgs mac (V.fromList [1,3])
      case verifyPresentation @G @Shake128Sponge sponge sk 5 pres of
        Left err  -> assertFailure ("deserialize error: " ++ show err)
        Right ok  -> assertBool "presentation should verify" ok

  , testCase "wrong secret key rejects" $ do
      sk1 <- keygen @G 3
      sk2 <- keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC sk1 msgs
      pres <- present @G @Shake128Sponge sponge msgs mac V.empty
      case verifyPresentation @G @Shake128Sponge sponge sk2 3 pres of
        Left _err -> pure ()
        Right ok  -> assertBool "should reject with wrong key" (not ok)

  , testCase "presentations are unlinkable (different randomizations)" $ do
      sk <- keygen @G 2
      msgs <- V.replicateM 2 (scalarRandom @S)
      mac <- bbsMAC sk msgs
      pres1 <- present @G @Shake128Sponge sponge msgs mac V.empty
      pres2 <- present @G @Shake128Sponge sponge msgs mac V.empty
      case verifyPresentation @G @Shake128Sponge sponge sk 2 pres1 of
        Left err -> assertFailure ("pres1 deserialize error: " ++ show err)
        Right ok -> assertBool "pres1 should verify" ok
      case verifyPresentation @G @Shake128Sponge sponge sk 2 pres2 of
        Left err -> assertFailure ("pres2 deserialize error: " ++ show err)
        Right ok -> assertBool "pres2 should verify" ok
      assertBool "presentations should have different U"
        (presU pres1 /= presU pres2)

  , testCase "0 attributes, all hidden" $ do
      sk <- keygen @G 0
      let msgs = V.empty
      mac <- bbsMAC sk msgs
      pres <- present @G @Shake128Sponge sponge msgs mac V.empty
      case verifyPresentation @G @Shake128Sponge sponge sk 0 pres of
        Left err  -> assertFailure ("deserialize error: " ++ show err)
        Right ok  -> assertBool "presentation should verify" ok

  , testCase "20 attributes, partial disclosure" $ do
      sk <- keygen @G 20
      msgs <- V.replicateM 20 (scalarRandom @S)
      mac <- bbsMAC sk msgs
      pres <- present @G @Shake128Sponge sponge msgs mac (V.fromList [0,5,10,15,19])
      case verifyPresentation @G @Shake128Sponge sponge sk 20 pres of
        Left err  -> assertFailure ("deserialize error: " ++ show err)
        Right ok  -> assertBool "presentation should verify" ok

  , testCase "wrong sponge session rejects" $ do
      let sponge1 = makeIV @Shake128Sponge "bbs-mac-test" "session-A"
          sponge2 = makeIV @Shake128Sponge "bbs-mac-test" "session-B"
      sk <- keygen @G 3
      msgs <- V.replicateM 3 (scalarRandom @S)
      mac <- bbsMAC sk msgs
      pres <- present @G @Shake128Sponge sponge1 msgs mac V.empty
      case verifyPresentation @G @Shake128Sponge sponge2 sk 3 pres of
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
      sk <- keygen @G 3
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      m2 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1, m2]  -- k is at index 0
      mac <- bbsMAC sk msgs
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge msgs mac V.empty 0 scope
      case verifyPseudonymPresentation @G @Shake128Sponge sponge sk 3 0 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "pseudonym presentation should verify" ok

  , testCase "pseudonym presentation verifies (partial disclosure)" $ do
      sk <- keygen @G 4
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      m2 <- scalarRandom @S
      m3 <- scalarRandom @S
      scope <- scalarRandom @S
      -- k at index 2, disclose indices 0 and 3
      let msgs = V.fromList [m1, m2, k, m3]
      mac <- bbsMAC sk msgs
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge msgs mac (V.fromList [0, 3]) 2 scope
      case verifyPseudonymPresentation @G @Shake128Sponge sponge sk 4 2 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "pseudonym presentation should verify" ok

  , testCase "pseudonym matches standalone PRF evaluation" $ do
      sk <- keygen @G 2
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- bbsMAC sk msgs
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge msgs mac V.empty 0 scope
      let expected = dyPRF @G k scope
      assertBool "pseudonym should match direct PRF evaluation"
        (ppPseudonym pres == expected)

  , testCase "same key and scope produce same pseudonym across presentations" $ do
      sk <- keygen @G 2
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- bbsMAC sk msgs
      pres1 <- presentWithPseudonym @G @Shake128Sponge
                 sponge msgs mac V.empty 0 scope
      pres2 <- presentWithPseudonym @G @Shake128Sponge
                 sponge msgs mac V.empty 0 scope
      -- Both should verify
      case verifyPseudonymPresentation @G @Shake128Sponge sponge sk 2 0 pres1 of
        Left err -> assertFailure ("pres1 error: " ++ show err)
        Right ok -> assertBool "pres1 should verify" ok
      case verifyPseudonymPresentation @G @Shake128Sponge sponge sk 2 0 pres2 of
        Left err -> assertFailure ("pres2 error: " ++ show err)
        Right ok -> assertBool "pres2 should verify" ok
      -- Pseudonyms should be identical (same key, same scope)
      assertBool "pseudonyms should match" (ppPseudonym pres1 == ppPseudonym pres2)
      -- But MAC randomizations should differ
      assertBool "U should differ" (ppU pres1 /= ppU pres2)

  , testCase "different scopes produce different pseudonyms" $ do
      sk <- keygen @G 2
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope1 <- scalarRandom @S
      scope2 <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- bbsMAC sk msgs
      pres1 <- presentWithPseudonym @G @Shake128Sponge
                 sponge msgs mac V.empty 0 scope1
      pres2 <- presentWithPseudonym @G @Shake128Sponge
                 sponge msgs mac V.empty 0 scope2
      assertBool "different scopes should give different pseudonyms"
        (ppPseudonym pres1 /= ppPseudonym pres2)

  , testCase "wrong secret key rejects pseudonym presentation" $ do
      sk1 <- keygen @G 2
      sk2 <- keygen @G 2
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1]
      mac <- bbsMAC sk1 msgs
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge msgs mac V.empty 0 scope
      case verifyPseudonymPresentation @G @Shake128Sponge sponge sk2 2 0 pres of
        Left _   -> pure ()
        Right ok -> assertBool "should reject wrong key" (not ok)

  , testCase "wrong PRF key index rejects" $ do
      sk <- keygen @G 3
      k <- scalarRandom @S
      m1 <- scalarRandom @S
      m2 <- scalarRandom @S
      scope <- scalarRandom @S
      let msgs = V.fromList [k, m1, m2]
      mac <- bbsMAC sk msgs
      -- Present with prfKeyIdx=0 but verify with prfKeyIdx=1
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge msgs mac V.empty 0 scope
      case verifyPseudonymPresentation @G @Shake128Sponge sponge sk 3 1 pres of
        Left _   -> pure ()
        Right ok -> assertBool "should reject wrong PRF key index" (not ok)

  , testCase "20 attributes with pseudonym" $ do
      sk <- keygen @G 20
      k <- scalarRandom @S
      otherMsgs <- V.replicateM 19 (scalarRandom @S)
      scope <- scalarRandom @S
      let msgs = V.cons k otherMsgs  -- k at index 0
      mac <- bbsMAC sk msgs
      pres <- presentWithPseudonym @G @Shake128Sponge
                sponge msgs mac (V.fromList [5,10,15]) 0 scope
      case verifyPseudonymPresentation @G @Shake128Sponge sponge sk 20 0 pres of
        Left err -> assertFailure ("deserialize error: " ++ show err)
        Right ok -> assertBool "presentation should verify" ok
  ]
