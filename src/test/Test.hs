module Main where
import Ditto.Test

main = do
  runUnitTests
  runIntegrationTests "tests/pass"
  return ()

