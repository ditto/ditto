module Ditto.Solve where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Conv

----------------------------------------------------------------------

solveProbs :: TCM ()
solveProbs = do
  xs <- probGNames
  mapM_ (flip updateProb workProb) xs

----------------------------------------------------------------------

workProb :: Prob -> TCM MProb
workProb (Prob1 acts ctx a1 a2) = resetCtx acts ctx (conv a1 a2)
workProb (ProbN p acts ctx as1 as2) = workProb p >>= \case
  Nothing -> resetCtx acts ctx (convArgs as1 as2)
  Just p' -> return (Just (ProbN p' acts ctx as1 as2))

----------------------------------------------------------------------
