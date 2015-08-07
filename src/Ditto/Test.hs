module Ditto.Test where
import Ditto.Syntax
import Ditto.Parse
import Ditto.Check
import Ditto.Conv
import Test.HUnit

----------------------------------------------------------------------

_Identity = "(A : Type) (a : A) : A"
identity = "((A : Type) (a : A) -> a)"

convTests :: Test
convTests = "Conv tests" ~:
  [ testConv "Type" "Type"
  , testConv (identity ++ "Type Type") "Type"
  , testConv "(A : Type) (a : A) -> a" "(B : Type) (b : B) -> b"
  ]

checkTests :: Test
checkTests = "Check tests" ~:
  [ testCheck "Type" "Type"
  , testCheckFails "(x : A) : B x" "Type"
  , testCheck "(x : Type) : Type" "Type"
  , testCheck _Identity "Type"
  , testCheck identity _Identity
  , testCheck "(B : Type) (b : B) -> b" _Identity
  , testCheckFails identity "Type"
  , testCheck ("(A : Type) (a : A) -> (" ++ identity ++ " A) (" ++ identity ++ " A a)") _Identity
  ]

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

----------------------------------------------------------------------

unitTests :: Test
unitTests = TestList [parseTests, checkTests, convTests]

runTests :: IO Counts
runTests = runTestTT unitTests

main = runTests >> return ()

----------------------------------------------------------------------

asExp :: String -> Exp
asExp s = case parseE s of
  Right a -> a
  Left e -> error (show e)

----------------------------------------------------------------------

testConv :: String -> String -> Test
testConv a b = TestCase $ case runConv (asExp a) (asExp b) of
  Left error -> assertFailure ("Conv error:\n" ++ error)
  Right _ -> return ()

----------------------------------------------------------------------

testCheck :: String -> String -> Test
testCheck a _A = TestCase $ case runCheck (asExp a) (asExp _A) of
  Left error -> assertFailure ("Check error:\n" ++ error)
  Right () -> return ()

testCheckFails :: String -> String -> Test
testCheckFails a _A = TestCase $ case runCheck (asExp a) (asExp _A) of
  Right () -> assertFailure ("Expected check failure:\n" ++ (a ++ " : " ++ _A))
  Left error -> return ()

----------------------------------------------------------------------

testParse :: String -> Maybe Exp -> Test
testParse s ma = TestCase $ case parseE s of
  Left error -> assertFailure ("Parse error:\n" ++ show error)
  Right a -> maybe (return ()) (@=? a) ma

----------------------------------------------------------------------