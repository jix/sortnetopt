{-# LANGUAGE Safe, BangPatterns #-}
module VectSet
  ( VectSet(channels)
  , allVects
  , fromBytes
  , applyComp
  , size
  , permute
  , invert
  , subsumes
  , extremalChannels
  , pruneExtremal
  , asBoolVectList
  )
where

import           Data.Bits
import           Control.Monad
import           Data.IntSet                    ( IntSet )
import qualified Data.IntSet                   as IS
import           Data.ByteString                ( ByteString )
import qualified Data.ByteString               as B

data VectSet = VectSet
  { channels :: !Int
  , vects :: !IntSet
  } deriving (Show, Eq)

allVects :: Int -> VectSet
allVects channels =
  VectSet { channels = channels, vects = IS.fromList [0 .. (bit channels) - 1] }

fromBytes :: Int -> ByteString -> VectSet
fromBytes channels bytes = VectSet { channels = channels, vects = vs }
 where
  vs = fst $ B.foldl' addByte (IS.empty, 0) bytes
  addByte (!set, !pos) 0 = (set, pos + 8)
  addByte (!set, !pos) n =
    addByte (IS.insert (pos + countTrailingZeros n) set, pos) (n .&. (n - 1))

applyComp :: Int -> Int -> VectSet -> Maybe VectSet
applyComp a b vs = guard irredundant
  >> return VectSet { channels = channels vs, vects = vs' }
 where
  aMask  = bit a
  bMask  = bit b
  abMask = aMask .|. bMask
  have xMask = any ((== xMask) . (.&. abMask)) (IS.toList $ vects vs)
  irredundant = have aMask && have bMask
  vs' = IS.map (\v -> if v .&. abMask == bMask then v `xor` abMask else v)
    $ vects vs

size :: VectSet -> Int
size = IS.size . vects

permute :: [Int] -> VectSet -> VectSet
permute perm vs = VectSet { channels = channels vs
                          , vects    = IS.map permVect $ vects vs
                          }
 where
  permVect v =
    foldr (\ !p !a -> (a `shiftL` 1) .|. fromEnum (testBit v p)) 0 perm

invert :: VectSet -> VectSet
invert vs = VectSet { channels = channels vs, vects = vs' }
 where
  mask = (bit $ channels vs) - 1
  vs'  = IS.map (xor mask) $ vects vs

subsumes :: VectSet -> VectSet -> Bool
subsumes a b | channels a == channels b = IS.isSubsetOf (vects a) (vects b)

extremalChannels :: Bool -> VectSet -> [Int]
extremalChannels pol vs =
  [ i | i <- [0 .. channels vs - 1], IS.member (bit i `xor` flip) (vects vs) ]
  where flip = if pol then (bit $ channels vs) - 1 else 0

pruneExtremal :: Bool -> Int -> VectSet -> VectSet
pruneExtremal pol a vs | channels vs > 0 = VectSet { channels = channels vs - 1
                                                   , vects    = vs'
                                                   }
 where
  mask     = bit a
  target   = if pol then 0 else mask
  maskLow  = (bit a) - 1
  maskHigh = complement maskLow
  vs' =
    IS.map (\v -> v .&. maskLow .|. (v `shiftR` 1) .&. maskHigh)
      . IS.filter (\v -> v .&. mask == target)
      $ vects vs

asBoolVectList :: VectSet -> [[Bool]]
asBoolVectList vs = map toBoolVect (IS.toList (vects vs))
  where toBoolVect v = [testBit v i | i <- [0..channels vs - 1]]
