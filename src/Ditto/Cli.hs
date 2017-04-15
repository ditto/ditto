module Ditto.Cli where
import Ditto.Syntax
import Ditto.Parse
import Ditto.Check
import Options.Applicative
import Data.Semigroup ((<>))
import Control.Monad

----------------------------------------------------------------------

data Options = Options
  { optFilename :: String
  , optVerbosity :: Verbosity
  }
  deriving (Show, Read, Eq)  

----------------------------------------------------------------------

parseOptions :: Parser Options
parseOptions = Options
   <$> strOption
       ( long "typecheck"
      <> short 't'
      <> metavar "FILENAME"
      <> help "Type check FILENAME" )
   <*> flag Normal Verbose
       ( long "verbose"
      <> short 'v'
      <> help "Enable verbose mode" )

menu :: ParserInfo Options
menu = info (helper <*> parseOptions)
  ( fullDesc
  <> progDesc "Type check FILENAME"
  <> header "Ditto - A Super Kawaii Programming Language with Dependent Types!"
  )

runCli :: IO ()
runCli = do
  opts <- execParser menu
  code <- readFile (optFilename opts)
  case parseP code of
    Left e -> putStrLn (show e)
    Right ds -> case runCheckProg (optVerbosity opts) ds of
      Left e -> putStr e
      Right holes -> putStr holes

----------------------------------------------------------------------

