{-# LANGUAGE Safe #-}
module ProofStep
  ( ProofStep(..)
  , Witnesses(..)
  , Witness(..)
  , witnessList
  )
where

import           VectSet                        ( VectSet )
import qualified VectSet                       as VS
data ProofStep = ProofStep
  { vectSet :: !VectSet
  , bound :: !Int
  , witnesses :: !Witnesses
  } deriving (Show)

data Witnesses = Huffman Bool [Maybe Witness]
               | Successors [Maybe Witness]
               deriving (Show)

witnessList :: Witnesses -> [Maybe Witness]
witnessList (Huffman _ ws) = ws
witnessList (Successors ws) = ws

data Witness = Witness
  { stepId :: !Int
  , invert :: !Bool
  , perm :: ![Int]
  } deriving (Show)

