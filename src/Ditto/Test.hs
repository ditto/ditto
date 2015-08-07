module Ditto.Test where
import Ditto.Syntax
import Ditto.Parse
import Test.HUnit

testParse :: String -> Maybe Exp -> Test
testParse s ma = TestCase $ case parseE s of
  Left error -> assertFailure ("Parse error:\n" ++ show error)
  Right a -> maybe (return ()) (@=? a) ma

unitTests :: Test
unitTests = TestList
  [ testParse "Type" (Just Type)
  , testParse "A" (Just (EVar "A"))
  , testParse "F x y z" Nothing
  , testParse "(x : A) (y : B) : Type" Nothing
  , testParse "(x : A) (y : B x) : C x y" Nothing
  , testParse "(x : A) (y : B) -> c" Nothing
  , testParse "(x : A) (y : B x) : C (((z : A) -> z) x) (g x y)" Nothing
  ]

runTests :: IO Counts
runTests = runTestTT unitTests

main = runTests >> return ()

