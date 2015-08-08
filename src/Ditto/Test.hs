module Ditto.Test where
import Ditto.Syntax
import Ditto.Parse
import Ditto.Check
import Ditto.Conv
import Ditto.Whnf
import Test.HUnit

----------------------------------------------------------------------

_Identity = "((A : Type) (a : A) : A)"
identity = "((A : Type) (a : A) -> a)"
_PiWh = "((A : Type) : " ++ identity ++ " Type Type)"

idProg = unlines
  [ "def id : (A : Type) (a : A) : A where"
  , "(A : Type) (a : A) -> a"
  , "end"

  , "def KType : Type where"
  , "id ((A : Type) : id Type Type)"
  , "end"
  ]

whnfTests :: Test
whnfTests = "Whnf tests" ~:
  [ testWhnf "Type" "Type"
  , testWhnf "((A : Type) (a : A) -> a) Type Type" "Type"
  , testWhnf ("((A : Type) (a : A) -> a) Type " ++ _Identity) _Identity
  , testWhnf (identity ++ " Type " ++ _PiWh) _PiWh
  , testWhnfFails (identity ++ " Type " ++ _PiWh) "(B : Type) : Type"
  ]

convTests :: Test
convTests = "Conv tests" ~:
  [ testConv "Type" "Type"
  , testConv (identity ++ "Type Type") "Type"
  , testConv "(A : Type) (a : A) -> a" "(B : Type) (b : B) -> b"
  , testConv (identity ++ " Type " ++ _PiWh) "(B : Type) : Type"
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
  , testParse idProg Nothing
  ]

----------------------------------------------------------------------

unitTests :: Test
unitTests = TestList [parseTests, checkTests, convTests, whnfTests]

runTests :: IO Counts
runTests = runTestTT unitTests

main = runTests >> return ()

----------------------------------------------------------------------

asExp :: String -> Exp
asExp s = case parseE s of
  Right a -> a
  Left e -> error (show e)

----------------------------------------------------------------------

testWhnf :: String -> String -> Test
testWhnf a b = TestCase $ case runWhnf (asExp a) of
  Left error -> assertFailure ("Whnf error:\n" ++ error)
  Right a' -> let
    error = "Whnf error:\n" ++ show a' ++ " != " ++ show (asExp b)
    in assertBool error (alpha a' (asExp b))

testWhnfFails :: String -> String -> Test
testWhnfFails a b = TestCase $ case runWhnf (asExp a) of
  Left error -> assertFailure ("Unexpected whnf error:\n" ++ error)
  Right a' -> let
    error = "Whnf reduced too much error:\n" ++ show a'
    in assertBool error (not (alpha a' (asExp b)))

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

testParseProg :: String -> Test
testParseProg s = TestCase $ case parseP s of
  Left error -> assertFailure ("Parse error:\n" ++ show error)
  Right xs -> return ()

testParse :: String -> Maybe Exp -> Test
testParse s ma = TestCase $ case parseE s of
  Left error -> assertFailure ("Parse error:\n" ++ show error)
  Right a -> maybe (return ()) (@=? a) ma

----------------------------------------------------------------------