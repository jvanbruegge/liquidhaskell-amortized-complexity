{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE UndecidableInstances #-}
{-@ LIQUID "--ple-local" @-}

module Heap where

import Prelude hiding (replicate)
import Data.List (uncons)
import Data.Kind (Type)
import Language.Haskell.Liquid.ProofCombinators (Proof, QED (..), (***), (===), (?))

data Nat = Zero | Succ Nat
  deriving stock Show

data Tree (k :: Nat) a where
  MkTree :: a -> DecList Tree k a -> Tree k a

data DecList (t :: Nat -> Type -> Type) (k :: Nat) (a :: Type) where
  DNil :: DecList t Zero a
  DCons :: t k a -> DecList t k a -> DecList t (Succ k) a

singleton :: a -> Tree Zero a
singleton x = MkTree x DNil

{-@ reflect mergeTree @-}
mergeTree :: Ord a => Tree k a -> Tree k a -> Tree (Succ k) a
mergeTree l@(MkTree lr lc) r@(MkTree rr rc)
  | lr <= rr = MkTree lr (DCons r lc)
  | otherwise = MkTree rr (DCons l rc)

data Binary
  = B0 Binary
  | B1 Binary
  | BEnd
  deriving stock Show

type family BInc (binary :: Binary) :: Binary where
  BInc BEnd = B1 BEnd
  BInc (B0 rest) = B1 rest
  BInc (B1 rest) = B0 (BInc rest)

type family BAdd (x :: Binary) (y :: Binary) :: Binary where
  BAdd BEnd y = y
  BAdd x BEnd = x
  BAdd (B0 x) (B0 y) = B0 (BAdd x y)
  BAdd (B1 x) (B0 y) = B1 (BAdd x y)
  BAdd (B0 x) (B1 y) = B1 (BAdd x y)
  BAdd (B1 x) (B1 y) = B0 (BInc (BAdd x y))

--type Forest :: Nat -> Binary -> Type -> Type
{-data Forest k b a where
  FEnd :: Forest k BEnd a
  F0 :: Forest (Succ k) b a -> Forest k (B0 b) a
  F1 :: Tree k a -> Forest (Succ k) b a -> Forest k (B1 b) a
-}
data Forest k b a =
  b ~ BEnd => FEnd
  | forall b'. b ~ B0 b' => F0 (Forest (Succ k) b' a)
  | forall b'. b ~ B1 b' => F1 (Tree k a) (Forest (Succ k) b' a)

{-@ reflect insertTree @-}
insertTree :: Ord a => Tree k a -> Forest k b a -> Forest k (BInc b) a
insertTree t FEnd = F1 t FEnd
insertTree t (F0 f) = F1 t f
insertTree t (F1 t' f) = F0 (insertTree (mergeTree t t') f)

mergeForests :: Ord a => Forest k lb a -> Forest k rb a -> Forest k (BAdd lb rb) a
mergeForests FEnd r = r
mergeForests l FEnd = l
mergeForests (F0 l) (F0 r) = F0 (mergeForests l r)
mergeForests (F1 t l) (F0 r) = F1 t (mergeForests l r)
mergeForests (F0 l) (F1 t r) = F1 t (mergeForests l r)
mergeForests (F1 t l) (F1 t' r) = F0 (insertTree (mergeTree t t') (mergeForests l r))

type Heap :: Binary -> Type -> Type
newtype Heap b a = Heap (Forest Zero b a)

empty :: Heap BEnd a
empty = Heap FEnd

pushHeap :: Ord a => a -> Heap b a -> Heap (BInc b) a
pushHeap x (Heap f) = Heap (insertTree (singleton x) f)

mergeHeap :: Ord a => Heap lb a -> Heap rb a -> Heap (BAdd lb rb) a
mergeHeap (Heap l) (Heap r) = Heap (mergeForests l r)

-- Amortized Analysis

{-@ reflect insertTreeT @-}
insertTreeT :: Ord a => Tree k a -> Forest k b a -> Int
insertTreeT _ FEnd = 1
insertTreeT _ (F0 _) = 1
insertTreeT t (F1 t' f) = 1 + insertTreeT (mergeTree t t') f

{-@ reflect pot @-}
pot :: Forest k b a -> Int
pot FEnd = 0
pot (F0 rest) = pot rest
pot (F1 _ rest) = 1 + pot rest

{-@ insertTreeAmortized :: t:_ -> f:_ -> { insertTreeT t f + pot (insertTree t f) - pot f <= 2 } @-}
insertTreeAmortized :: Ord a => Tree k a -> Forest k b a -> Proof
insertTreeAmortized t f@FEnd =
  insertTreeT t f + pot (insertTree t f) - pot f
    === 1 + pot (insertTree t f) - 0
    === 1 + pot (F1 t FEnd) -- fails
    === undefined
    *** QED
{-    === 1 + pot (F1 t FEnd) - 0
    === 1 + 1 + pot FEnd
    *** QED -}
insertTreeAmortized r f = undefined



-- Appendix: Pretty print trees
mapToList :: (forall k'. t k' a -> b) -> DecList t k a -> [b]
mapToList _ DNil = []
mapToList f (DCons x xs) = f x : mapToList f xs

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

instance Show a => Show (Tree k a) where
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

testTree :: Tree (Succ (Succ Zero)) Int
testTree = MkTree 7 (DCons (MkTree 12 (DCons (MkTree 13 DNil) DNil)) (DCons (MkTree 8 DNil) DNil))

testTree2 :: Tree (Succ (Succ Zero)) Int
testTree2 = MkTree 3 (DCons (MkTree 5 (DCons (MkTree 9 DNil) DNil)) (DCons (MkTree 4 DNil) DNil))

testTree3 :: Tree (Succ (Succ (Succ Zero))) Int
testTree3 = mergeTree testTree testTree2
