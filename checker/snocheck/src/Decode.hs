{-# LANGUAGE Safe #-}
module Decode
  ( proofSteps
  )
where

import           Data.Bits
import           Data.Word
import           Data.ByteString                ( ByteString )
import qualified Data.ByteString               as B
import           VectSet                        ( VectSet )
import qualified VectSet                       as VS
import           ProofStep

readLE :: Int -> ByteString -> Int
readLE len bytes = sum
  [ (`shift` (8 * i)) . fromIntegral $ B.index bytes i | i <- [0 .. len - 1] ]

read32LE :: ByteString -> Int
read32LE = readLE 4

read64LE :: ByteString -> Int
read64LE = readLE 8

bits :: Word8 -> [Bool]
bits x = [ testBit x i | i <- [0 .. 7] ]

proofSteps :: ByteString -> (Int, Int -> ProofStep)
proofSteps proofData = (stepCount, decodeProofStep . encodedStep)
  where (stepCount, encodedStep) = encodedProofSteps proofData

encodedProofSteps :: ByteString -> (Int, Int -> ByteString)
encodedProofSteps proofData = (stepCount, stepData)
 where
  stepCount = read32LE proofData
  stepData step =
    let stepHeader = B.drop (4 + 12 * step) proofData
        offset     = read64LE stepHeader
        length     = read32LE $ B.drop 8 stepHeader
    in  B.take length $ B.drop offset proofData

decodeProofStep :: ByteString -> ProofStep
decodeProofStep stepData = ProofStep { vectSet   = vectSet
                                     , bound     = bound
                                     , witnesses = witnesses
                                     }
 where
  channels                       = fromIntegral (B.index stepData 0)
  bound                          = fromIntegral (B.index stepData 1)
  encodedSetLength               = bit (0 `max` (channels - 3))
  encodedSetBytes                = B.take encodedSetLength (B.drop 2 stepData)
  vectSet                        = VS.fromBytes channels encodedSetBytes
  witnessData                    = B.drop (encodedSetLength + 2) stepData
  (witnessType, witnessChannels) = case B.index witnessData 0 of
    0 -> (Huffman False, channels - 1)
    1 -> (Huffman True, channels - 1)
    2 -> (Successors, channels)
  witnesses =
    witnessType . decodeWitnesses witnessChannels $ B.drop 1 witnessData

decodeWitnesses :: Int -> ByteString -> [Maybe Witness]
decodeWitnesses channels bs = case B.uncons bs of
  Nothing        -> []
  Just (0, tail) -> decodeWitness False tail
  Just (1, tail) -> decodeWitness True tail
  Just (2, tail) -> (Nothing :) $! decodeWitnesses channels tail
 where
  decodeWitness invert bs =
    let (perm, tail) = B.splitAt channels bs
    in  ((  Just
         $! (Witness { invert = invert
                     , perm   = map fromIntegral . B.unpack $ perm
                     , stepId = read32LE tail
                     }
            )
         ) :
        )
          $! decodeWitnesses channels (B.drop 4 tail)
