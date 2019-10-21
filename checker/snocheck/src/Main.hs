{-# LANGUAGE Safe #-}
module Main where

import           System.Environment
import qualified Data.ByteString               as B
import           Decode
import           VectSet
import           Check

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["-r", proofFileName] ->
      print . checkProof . proofSteps =<< B.readFile proofFileName
    ["-v", proofFileName] -> putStrLn "Verified checking not yet implemented"
    _                     -> do
      putStrLn "usage (reference checker): snocheck -r PROOF"
      putStrLn "       (verified checker): snocheck -v PROOF"
