module Ditto.Test where
import Ditto.Syntax
import Ditto.Parse
import Ditto.Check
import Test.HUnit

asExp :: String -> Exp
asExp s = case parseE s of
  Right a -> a
  Left e -> error (show e)

testCheck :: String -> String -> Test
testCheck a _A = TestCase $ case runCheck (asExp a) (asExp _A) of
  Left error -> assertFailure ("Check error:\n" ++ error)
  Right () -> return ()

testParse :: String -> Maybe Exp -> Test
testParse s ma = TestCase $ case parseE s of
  Left error -> assertFailure ("Parse error:\n" ++ show error)
  Right a -> maybe (return ()) (@=? a) ma

checkTests :: Test
checkTests = "Check tests" ~:
  [ testCheck "Type" "Type"
  , testCheck "(x : Type) : Type" "Type"
  , testCheck _Identity "Type"
  , testCheck identity _Identity
  , testCheck ("(A : Type) (a : A) -> (" ++ identity ++ " A) (" ++ identity ++ " A a)") _Identity
  ]
  where
  _Identity = "(A : Type) (a : A) : A"
  identity = "((A : Type) (a : A) -> a)"

parseTests :: Test
parseTests = "Parse tests" ~:
  [ testParse "Type" (Just Type)
  , testParse "A" (Just (EVar "A"))
  , testParse "F x y z" Nothing
  , testParse "(x : A) (y : B) : Type" Nothing
  , testParse "(x : A) (y : B x) : C x y" Nothing
  , testParse "(x : A) (y : B) -> c" Nothing
  , testParse "(x : A) (y : B x) : C (((z : A) -> z) x) (g x y)" Nothing
  ]

unitTests :: Test
unitTests = TestList [parseTests, checkTests]

runTests :: IO Counts
runTests = runTestTT unitTests

main = runTests >> return ()

