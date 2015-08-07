module Ditto.Test where
import Ditto.Syntax
import Ditto.Parse
import Test.HUnit

testParse :: String -> Exp -> Test
testParse s a = TestCase $ case parseE s of
  Left error -> assertFailure ("Parse error:\n" ++ show error)
  Right a' -> a @=? a'

unitTests :: Test
unitTests = TestList [testParse "Type" Type]

runTests :: IO Counts
runTests = runTestTT unitTests

main = runTests >> return ()

