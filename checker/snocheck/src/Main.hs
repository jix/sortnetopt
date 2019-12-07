{-# LANGUAGE Safe #-}
module Main where

import           System.Environment
import qualified Data.ByteString               as B
import           Decode
import           VectSet
import           Check
import           Translate
import qualified Verified.Checker              as VC

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["-r", proofFileName] ->
      print . checkProof . proofSteps =<< B.readFile proofFileName
    ["-v", proofFileName] -> do
      proofData <- B.readFile proofFileName
      let steps   = proofSteps proofData
          vcSteps = translateProofSteps steps
          result  = do
            (width, bound) <- VC.check_proof_get_bound vcSteps
            return (VC.integer_of_int width, VC.integer_of_int bound)
      print result
    _ -> do
      putStrLn "usage (reference checker): snocheck -r PROOF"
      putStrLn "       (verified checker): snocheck -v PROOF"
