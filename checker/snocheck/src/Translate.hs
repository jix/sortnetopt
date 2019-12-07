{-# LANGUAGE Safe #-}
module Translate
  ( translateProofSteps
  )
where

import qualified Verified.Checker              as VC
import           ProofStep
import           VectSet                        ( VectSet )
import qualified VectSet                       as VS

translateProofSteps :: (Int, Int -> ProofStep) -> VC.Proof_cert
translateProofSteps (stepCount, steps) =
  VC.ProofCert (VC.Int_of_integer $ toInteger stepCount) (translateStepFn steps)

translateStepFn :: (Int -> ProofStep) -> VC.Int -> VC.Proof_step
translateStepFn steps (VC.Int_of_integer stepId) =
  translateStep (steps $ fromInteger stepId)

translateStep :: ProofStep -> VC.Proof_step
translateStep step = VC.ProofStep width vectList stepBound stepWitnesses
 where
  width         = VC.Int_of_integer . toInteger $ VS.channels (vectSet step)
  vectList      = VS.asBoolVectList (vectSet step)
  stepBound     = VC.Int_of_integer . toInteger $ bound step
  stepWitnesses = translateWitnesses (witnesses step)

translateWitnesses :: Witnesses -> VC.Proof_step_witnesses
translateWitnesses (Huffman pol witnesses) =
  VC.HuffmanWitnesses pol (translateWitnessList witnesses)
translateWitnesses (Successors witnesses) =
  VC.SuccessorWitnesses (translateWitnessList witnesses)

translateWitnessList :: [Maybe Witness] -> [Maybe VC.Proof_witness]
translateWitnessList = map (fmap translateWitness)

translateWitness :: Witness -> VC.Proof_witness
translateWitness witness = VC.ProofWitness
  (VC.Int_of_integer . toInteger $ stepId witness)
  (invert witness)
  (map (VC.Int_of_integer . toInteger) $ perm witness)
