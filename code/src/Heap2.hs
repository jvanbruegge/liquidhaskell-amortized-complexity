{-@ LIQUID "--ple-local" @-}

module Heap2 where

import Prelude hiding (replicate)
import Data.List (uncons)
import Language.Haskell.Liquid.ProofCombinators (Proof, (?), trivial)

data Tree a = MkTree a [Tree a]

singleton :: a -> Tree a
singleton x = MkTree x []

{-@ reflect mergeTree @-}
mergeTree :: Ord a => Tree a -> Tree a -> Tree a
mergeTree l@(MkTree lr lc) r@(MkTree rr rc)
  | lr <= rr = MkTree lr (r : lc)
  | otherwise = MkTree rr (l : rc)

data Heap a = FEnd | F0 (Heap a) | F1 (Tree a) (Heap a)

{-@ reflect insertTree @-}
insertTree :: Ord a => Tree a -> Heap a -> Heap a
insertTree t FEnd = F1 t FEnd
insertTree t (F0 f) = F1 t f
insertTree t (F1 t' f) = F0 (insertTree (mergeTree t t') f)

mergeHeaps :: Ord a => Heap a -> Heap a -> Heap a
mergeHeaps FEnd r = r
mergeHeaps l FEnd = l
mergeHeaps (F0 l) (F0 r) = F0 (mergeHeaps l r)
mergeHeaps (F1 t l) (F0 r) = F1 t (mergeHeaps l r)
mergeHeaps (F0 l) (F1 t r) = F1 t (mergeHeaps l r)
mergeHeaps (F1 t l) (F1 t' r) = F0 (insertTree (mergeTree t t') (mergeHeaps l r))

empty :: Heap a
empty = FEnd

pushHeap :: Ord a => a -> Heap a -> Heap a
pushHeap x f = insertTree (singleton x) f

-- Amortized Analysis

{-@ reflect insertTreeT @-}
insertTreeT :: Ord a => Tree a -> Heap a -> Int
insertTreeT _ FEnd = 1
insertTreeT _ (F0 _) = 1
insertTreeT t (F1 t' f) = 1 + insertTreeT (mergeTree t t') f

{-@ reflect pot @-}
pot :: Heap a -> Int
pot FEnd = 0
pot (F0 rest) = pot rest
pot (F1 _ rest) = 1 + pot rest

{-@ automatic-instances insertTreeAmortized @-}
{-@ insertTreeAmortized :: t:_ -> f:_ -> { insertTreeT t f + pot (insertTree t f) - pot f <= 2 } @-}
insertTreeAmortized :: Ord a => Tree a -> Heap a -> Proof
insertTreeAmortized t (F1 t' f') = trivial ? insertTreeAmortized (mergeTree t t') f'
insertTreeAmortized _ _ = trivial

-- Appendix: Pretty print trees
mapToList :: (Tree a -> b) -> [Tree a] -> [b]
mapToList _ [] = []
mapToList f (x : xs) = f x : mapToList f xs

{-@ lineLength :: String -> { x:Int | x >= 0 } @-}
lineLength :: String -> Int
lineLength = maybe 0 (length . fst) . uncons . lines

horizontal :: String -> String -> String
horizontal a b = unlines (go (lineLength a) (lineLength b) (lines a) (lines b))

replicate :: Int -> a -> [a]
replicate n x
  | n <= 0 = []
  | otherwise = x : replicate (n - 1) x

{-@ go :: Int -> Int -> xs:[String] -> ys:[String] -> [String] / [len xs, len ys] @-}
go :: Int -> Int -> [String] -> [String] -> [String]
go _ _ [] [] = []
go n m [] (x:xs) = (replicate (n + 2) ' ' <> x) : go n m [] xs
go n m (x:xs) [] = (x <> replicate (m + 2) ' ') : go n m xs []
go n m (x:xs) (y:ys) = (x <> "  " <> y) : go n m xs ys

instance Show a => Show (Tree a) where
  show (MkTree x xs) = case withBars (mapToList show xs) of
    [] -> show x
    [y] -> let
            x' = show x
            n = lineLength y
           in replicate (n - length x') ' ' <> x' <> "\n" <> replicate (n - 1) ' ' <> "|\n" <> y
    xs'@(x':_) -> let
            s = foldl1 horizontal xs'
            n = lineLength x'
            m = lineLength s
            s' = show x
           in replicate (m - length s') ' ' <> s' <> "\n" <> replicate n ' ' <> replicate (m - n - 1) '_' <> "|\n" <> s
    where
      withBars [] = []
      withBars [y] = [replicate (lineLength y - 1) ' ' <> "|\n" <> y]
      withBars (y:ys) = (replicate (lineLength y - 1) ' ' <> "/\n" <> y) : withBars ys

testTree :: Tree Int
testTree = MkTree 7 [MkTree 12 [MkTree 13 []], MkTree 8 []]

testTree2 :: Tree Int
testTree2 = MkTree 3 [MkTree 5 [MkTree 9 []], MkTree 4 []]

testTree3 :: Tree Int
testTree3 = mergeTree testTree testTree2
