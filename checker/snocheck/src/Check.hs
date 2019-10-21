{-# LANGUAGE Safe #-}
module Check
  ( checkProof
  )
where

import           Control.Monad
import           Data.Foldable
import           Data.Maybe
import           Data.Traversable
import           Data.IntMap.Strict             ( IntMap )
import qualified Data.IntMap.Strict            as IM
import           ProofStep
import           VectSet                        ( VectSet )
import qualified VectSet                       as VS

type Result a = Either String a

type ProofSteps = Int -> Either String ProofStep

check :: String -> Bool -> Result ()
check msg cond = if cond then return () else Left msg

checkProof :: (Int, Int -> ProofStep) -> Result (Int, Int)
checkProof (stepCount, stepFn) = do
  traverse_ checkStep' [0 .. stepCount - 1]
  let lastStep = stepFn $ stepCount - 1
  return (VS.channels $ vectSet lastStep, bound lastStep)
 where
  steps n | 0 <= n && n < stepCount = return $ stepFn n
          | otherwise               = Left "step id out of bounds"

  checkStep' stepId = case checkStep steps stepId of
    Left err -> Left $ "step " ++ show stepId ++ ": " ++ err
    x        -> x

checkStep :: ProofSteps -> Int -> Result ()
checkStep steps stepId = do
  step <- steps stepId
  case witnesses step of
    Huffman pol witnesses -> checkHuffman steps step pol witnesses
    Successors witnesses  -> checkSuccessors steps step witnesses

checkHuffman :: ProofSteps -> ProofStep -> Bool -> [Maybe Witness] -> Result ()
checkHuffman steps step pol witnesses = do
  let vs               = vectSet step
      channels         = VS.channels vs
      extremalChannels = VS.extremalChannels pol vs
  check "wrong number of huffman witnesses"
        (length extremalChannels == length witnesses)
  bounds <- for (zip extremalChannels witnesses) $ \(c, witness) -> do
    let prunedSet = VS.pruneExtremal pol c vs
    getBound steps witness prunedSet
  check "huffman bound too low" (huffmanBound bounds >= bound step)
  return ()

huffmanBound :: [Int] -> Int
huffmanBound = huffmanBound' . IM.fromListWith (+) . map (\k -> (k, 1))

huffmanBound' :: IntMap Int -> Int
huffmanBound' queue = case queuePop queue of
  Just (item, queue') -> case queuePop queue' of
    Nothing -> item
    Just (item2, queue'') ->
      huffmanBound' $ queuePush (1 + max item item2) queue''

queuePop :: IntMap Int -> Maybe (Int, IntMap Int)
queuePop queue = do
  ((item, count), rest) <- IM.minViewWithKey queue
  let rest' = if count > 1 then IM.insert item (count - 1) rest else rest
  return (item, rest')

queuePush :: Int -> IntMap Int -> IntMap Int
queuePush item = IM.insertWith (+) item 1

checkSuccessors :: ProofSteps -> ProofStep -> [Maybe Witness] -> Result ()
checkSuccessors steps step witnesses = do
  let vs         = vectSet step
      channels   = VS.channels vs
      successors = catMaybes
        [ VS.applyComp i j vs | i <- [0 .. channels - 1], j <- [0 .. i - 1] ]

  check "wrong number of successor witnesses"
        (length successors == length witnesses)

  for_ (zip successors witnesses) $ \(successor, witness) -> do
    b <- getBound steps witness successor
    check "successor bound too low" (b + 1 >= bound step)
    return ()

  return ()

getBound :: ProofSteps -> Maybe Witness -> VectSet -> Result Int
getBound _ Nothing vs | VS.size vs <= VS.channels vs = return 0
                      | otherwise                    = return 1
getBound steps (Just witness) vs = do
  witnessStep <- steps $ stepId witness
  let witnessSet         = vectSet witnessStep
      witnessSet' = if invert witness then VS.invert witnessSet else witnessSet
      witnessBound       = bound witnessStep
      permutedWitnessSet = VS.permute (perm witness) witnessSet'
      permuted           = VS.permute (perm witness) vs
  check "witness does not subsume target" (VS.subsumes permutedWitnessSet vs)
  return witnessBound
