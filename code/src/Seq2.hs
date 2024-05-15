{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--max-case-expand=100000" @-}
{-@ LIQUID "--ple-local" @-}

module Seq2 where

import Prelude hiding (foldl, foldr, (++), max)

import Language.Haskell.Liquid.ProofCombinators (Proof, QED (..), (***), (=<=), (===), (?))

data Seq a = Nil
  | Unit a
  | More (Some a) (Seq (Tuple a)) (Some a)

data Some a = One a | Two a a | Three a a a

data Tuple a = Pair a a | Triple a a a

{-@ reflect cons @-}
cons :: a -> Seq a -> Seq a
cons x Nil = Unit x
cons x (Unit y) = More (One x) Nil (One y)
cons x (More (One y) q u) = More (Two x y) q u
cons x (More (Two y z) q u) = More (Three x y z) q u
cons x (More (Three y z w) q u) = More (Two x y) (cons (Pair z w) q) u

{-@ reflect snoc @-}
snoc :: Seq a -> a -> Seq a
snoc Nil x = Unit x
snoc (Unit x) y = More (One x) Nil (One y)
snoc (More u q (One x)) y = More u q (Two x y)
snoc (More u q (Two x y)) z = More u q (Three x y z)
snoc (More u q (Three x y z)) w = More u (snoc q (Pair x y)) (Two z w)

{-@ reflect toList @-}
{-@ toList :: Some a -> { xs:[a] | len xs >= 1 && len xs <= 3 } @-}
toList :: Some a -> [a]
toList (One x) = [x]
toList (Two x y) = [x, y]
toList (Three x y z) = [x, y, z]

{-@ reflect toTuples @-}
{-@ toTuples :: { xs:[_] | len xs >= 2 && len xs <= 9 } -> { ys:[_] | len ys >= 1 && len ys <= 3 } @-}
toTuples :: [a] -> [Tuple a]
toTuples = toTuples'

{-@ reflect toTuples' @-}
{-@ toTuples' :: { xs:[_] | len xs != 1 && len xs <= 9 } -> { ys:[_] | if len xs == 0 then len ys == 0 else if len xs <= 3 then len ys == 1 else if len xs <= 6 then len ys == 2 else len ys == 3 } @-}
toTuples' :: [a] -> [Tuple a]
toTuples' [] = []
toTuples' [x, y] = [Pair x y]
toTuples' [x, y, z, w] = [Pair x y, Pair z w]
toTuples' (x:y:z:xs) = Triple x y z : toTuples' xs

{-@ reflect foldl @-}
foldl :: (b -> a -> b) -> b -> [a] -> b 
foldl _ x [] = x
foldl f a (x:xs) = foldl f (f a x) xs

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ x [] = x
foldr f a (x:xs) = f x (foldr f a xs)

{-@ reflect ++ @-}
{-@ (++) :: x:[_] -> y:[_] -> { z:[_] | len z == len x + len y } @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

{-@ reflect glue @-}
{-@ glue :: Seq a -> { xs:[_] | len xs <= 3 } -> Seq a -> Seq a @-}
glue :: Seq a -> [a] -> Seq a -> Seq a
glue Nil as q2 = foldr cons q2 as
glue q1 as Nil = foldl snoc q1 as
glue (Unit x) as q2 = foldr cons q2 (x : as)
glue q1 as (Unit x) = snoc (foldl snoc q1 as) x
glue (More u1 q1 v1) as (More u2 q2 v2) = More u1 (glue q1 (toTuples (toList v1 ++ as ++ toList u2)) q2) v2

{-@ reflect append @-}
append :: Seq a -> Seq a -> Seq a
append q1 q2 = glue q1 [] q2


------------- COMPLEXITY ANALYSIS -----------------

{-@ reflect pot @-}
{-@ pot :: Seq a -> { x:Int | x >= 0 } @-}
pot :: Seq a -> Int
pot Nil = 0
pot (Unit _) = 0
pot (More u q v) = dang u + pot q + dang v

{-@ reflect dang @-}
{-@ dang :: Some a -> { x:Int | x >= 0 } @-}
dang :: Some a -> Int
dang (One _) = 1
dang (Two _ _) = 0
dang (Three _ _ _) = 1

{-@ reflect consT @-}
{-@ consT :: a -> Seq a -> { x:Int | x >= 1 } @-}
consT :: a -> Seq a -> Int
consT _ Nil = 1
consT _ (Unit _) = 1
consT _ (More (One _) _ _) = 1
consT _ (More (Two _ _) _ _) = 1
consT _ (More (Three _ z w) q _) = 1 + consT (Pair z w) q

{-@ reflect snocT @-}
{-@ snocT :: Seq a -> a -> { x:Int | x >= 1 } @-}
snocT :: Seq a -> a -> Int
snocT Nil _ = 1
snocT (Unit _) _ = 1
snocT (More _ _ (One _)) _ = 1
snocT (More _ _ (Two _ _)) _ = 1
snocT (More _ q (Three x y _)) _ = 1 + snocT q (Pair x y)

{-@ consAmortized :: x:a -> q:Seq a -> { consT x q + pot (cons x q) - pot q <= 3 } @-}
consAmortized :: a -> Seq a -> ()
consAmortized x qq@Nil =
  consT x qq + pot (cons x qq) - pot qq
    === 1 + pot (Unit x) - 0
    === 1
    *** QED
consAmortized x qq@(Unit y) =
  consT x qq + pot (cons x qq) - pot qq
    === 1 + pot (More (One x) Nil (One y)) - 0
    === 1 + dang (One x) + pot Nil + dang (One y)
    === 3
    *** QED
consAmortized x qq@(More (One y) q u) = 
  consT x qq + pot (cons x qq) - pot qq
    === 1 + pot (More (Two x y) q u) - (dang (One y) + pot q + dang u)
    === 1 + (dang (Two x y) + pot q + dang u) - 1 - pot q - dang u
    === 0
    *** QED
consAmortized x qq@(More (Two y z) q u) =
  consT x qq + pot (cons x qq) - pot qq
    === 1 + pot (More (Three x y z) q u) - (dang (Two y z) + pot q + dang u)
    === 1 + dang (Three x y z) + pot q + dang u - 0 - pot q - dang u
    === 1 + 1
    *** QED
consAmortized x qq@(More (Three y z w) q u) =
  consT x qq + pot (cons x qq) - pot qq
    === (1 + consT (Pair z w) q) + pot (More (Two x y) (cons (Pair z w) q) u) - (dang (Three y z w) + pot q + dang u)
    === consT (Pair z w) q + dang (Two x y) + pot (cons (Pair z w) q) + dang u - pot q - dang u
    === consT (Pair z w) q + pot (cons (Pair z w) q) - pot q
    ? consAmortized (Pair z w) q
    *** QED

{-@ automatic-instances snocAmortized @-}
{-@ snocAmortized :: q:Seq a -> x:a -> { snocT q x + pot (snoc q x) - pot q <= 3 } @-}
snocAmortized :: Seq a -> a -> Proof
snocAmortized qq@(More u q (Three x y z)) w =
  snocT qq w + pot (snoc qq w) - pot qq
  === 1 + snocT q (Pair x y) + pot (More u (snoc q (Pair x y)) (Two z w)) - dang u - pot q - 1
  === snocT q (Pair x y) + pot (snoc q (Pair x y)) - pot q
  ? snocAmortized q (Pair x y)
  *** QED
snocAmortized qq w =
  snocT qq w + pot (snoc qq w) - pot qq
  =<= 3
  *** QED

{-@ reflect foldrT @-}
{-@ foldrT :: (a -> b -> b) -> (a -> b -> { x:Int | x >= 1 }) -> b -> [a] -> { x:Int | x >= 1 } @-}
foldrT :: (a -> b -> b) -> (a -> b -> Int) -> b -> [a] -> Int
foldrT _ _ _ [] = 1
foldrT f fT b (x:xs) = fT x (foldr f b xs) + foldrT f fT b xs

{-@ reflect foldlT @-}
{-@ foldlT :: (b -> a -> b) -> (b -> a -> { x:Int | x >= 1 }) -> b -> [a] -> { x:Int | x >= 1 } @-}
foldlT :: (b -> a -> b) -> (b -> a -> Int) -> b -> [a] -> Int
foldlT _ _ _ [] = 1
foldlT f fT a (x:xs) = fT a x + foldlT f fT (f a x) xs

{-@ reflect tuplesToList @-}
{-@ tuplesToList :: x:[_] -> { y:[_] | len y <= 3 * len x && len y >= 2 * len x } @-}
tuplesToList :: [Tuple a] -> [a]
tuplesToList [] = []
tuplesToList (Pair a b:xs) = a:b:tuplesToList xs
tuplesToList (Triple a b c:xs) = a:b:c:tuplesToList xs

{-@ reflect seqToList @-}
seqToList :: Seq a -> [a]
seqToList Nil = []
seqToList (Unit x) = [x]
seqToList (More u q v) = toList u ++ tuplesToList (seqToList q) ++ toList v

{-@ reflect glueT @-}
{-@ glueT :: Seq a -> { as:[a] | len as <= 3 } -> Seq a -> { x:Int | x >= 1 } @-}
glueT :: Seq a -> [a] -> Seq a -> Int
glueT Nil as q2 = 1 + foldrT cons consT q2 as
glueT q1 as Nil = 1 + foldlT snoc snocT q1 as
glueT (Unit x) as q2 = 1 + foldrT cons consT q2 (x : as)
glueT q1 as (Unit x) = 1 + snocT (foldl snoc q1 as) x + foldlT snoc snocT q1 as
glueT (More _ q1 v1) as (More u2 q2 _) = 1 + glueT q1 (toTuples (toList v1 ++ as ++ toList u2)) q2

{-@ reflect log2 @-}
{-@ log2 :: { x:Int | x >= 1 } -> { y:Int | y >= 0 } @-}
log2 :: Int -> Int
log2 1 = 0
log2 n = 1 + log2 (n `div` 2)

{-@ log2Mono :: { x:Int | 1 <= x } -> { y:Int | x <= y } -> { log2 x <= log2 y } @-}
log2Mono :: Int -> Int -> Proof
log2Mono 1 m = log2 1 <= log2 m *** QED
log2Mono n m =
  log2 n <= log2 m
  === 1 + log2 (n `div` 2) <= 1 + log2 (m `div` 2)
  === log2 (n `div` 2) <= log2 (m `div` 2)
  ? log2Mono (n `div` 2) (m `div` 2)
  *** QED

{-@ foldrTCons :: q:Seq a -> as:[a] -> { foldrT cons consT q as + pot (foldr cons q as) - pot q <= 3 * len as + 1 } @-}
foldrTCons :: Seq a -> [a] -> Proof
foldrTCons q as@[] =
  foldrT cons consT q as + pot (foldr cons q as) - pot q
  === 1 + pot q - pot q
  *** QED
foldrTCons q as@(x:xs) =
  foldrT cons consT q as + pot (foldr cons q as) - pot q
  === consT x (foldr cons q xs) + foldrT cons consT q xs + pot (cons x (foldr cons q xs)) - pot q
      + pot (foldr cons q xs) - pot (foldr cons q xs)
  ? consAmortized x (foldr cons q xs)
  =<= 3 + foldrT cons consT q xs + pot (foldr cons q xs) - pot q
  ? foldrTCons q xs
  =<= 3 + 3 * length xs + 1
  *** QED

{-@ foldlTSnoc :: q:Seq a -> as:[a] -> { foldlT snoc snocT q as + pot (foldl snoc q as) - pot q <= 3 * len as + 1 } @-}
foldlTSnoc :: Seq a -> [a] -> Proof
foldlTSnoc q as@[] =
  foldlT snoc snocT q as + pot (foldl snoc q as) - pot q
  === 1 + pot q - pot q
  *** QED
foldlTSnoc q as@(x:xs) =
  foldlT snoc snocT q as + pot (foldl snoc q as) - pot q
  === snocT q x + foldlT snoc snocT (snoc q x) xs + pot (foldl snoc (snoc q x) xs) - pot q
      + pot (snoc q x) - pot (snoc q x)
  ? snocAmortized q x
  =<= 3 + foldlT snoc snocT (snoc q x) xs + pot (foldl snoc (snoc q x) xs) - pot (snoc q x)
  ? foldlTSnoc (snoc q x) xs
  *** QED

{-@ inline max @-}
max :: Int -> Int -> Int
max a b = if a >= b then a else b

{-@ divCancel :: x:Int -> { div (2 * x) 2 == x } @-}
divCancel :: Int -> Proof
divCancel _ = ()

{-@ glueAmortized :: q1:Seq a -> { as:[a] | len as <= 3 } -> q2:Seq a -> { glueT q1 as q2 + pot (glue q1 as q2) - pot q1 - pot q2 <= log2 (max (len (seqToList q1) + len (seqToList q2)) 2) + 14 } @-}
glueAmortized :: Seq a -> [a] -> Seq a -> Proof
glueAmortized q1@Nil as q2 =
  glueT q1 as q2 + pot (glue q1 as q2) - pot q1 - pot q2
  === 1 + foldrT cons consT q2 as + pot (foldr cons q2 as) - pot q1 - pot q2
  ? foldrTCons q2 as
  =<= 1 + 3 * length as + 1 - pot q1
  =<= log2 (max (length (seqToList q1) + length (seqToList q2)) 2) + 14
  *** QED
glueAmortized q1 as q2@Nil =
  glueT q1 as q2 + pot (glue q1 as q2) - pot q1 - pot q2
  === 1 + foldlT snoc snocT q1 as + pot (foldl snoc q1 as) - pot q1 - pot q2
  ? foldlTSnoc q1 as
  =<= 1 + 3 * length as + 1 - pot q2
  =<= log2 (max (length (seqToList q1) + length (seqToList q2)) 2) + 14
  *** QED
glueAmortized q1@(Unit x) as q2 =
  glueT q1 as q2 + pot (glue q1 as q2) - pot q1 - pot q2
  === 1 + foldrT cons consT q2 (x:as) + pot (foldr cons q2 (x:as)) - pot q1 - pot q2
  ? foldrTCons q2 (x:as)
  =<= 1 + 3 * length (x:as) + 1 - pot q1
  =<= log2 (max (length (seqToList q1) + length (seqToList q2)) 2) + 14
  *** QED
glueAmortized q1 as q2@(Unit x) = 
  glueT q1 as q2 + pot (glue q1 as q2) - pot q1 - pot q2
  === 1 + snocT (foldl snoc q1 as) x + foldlT snoc snocT q1 as + pot (snoc (foldl snoc q1 as) x) - pot q1 - pot q2 + pot (foldl snoc q1 as) - pot (foldl snoc q1 as)
  ? snocAmortized (foldl snoc q1 as) x
  =<= 1 + 3 + foldlT snoc snocT q1 as - pot q1 - pot q2 + pot (foldl snoc q1 as)
  ? foldlTSnoc q1 as
  =<= 1 + 3 + 3 * length as + 1 - pot q2
  =<= log2 (max (length (seqToList q1) + length (seqToList q2)) 2) + 14
  *** QED
glueAmortized qq1@(More u1 q1 v1) as qq2@(More u2 q2 v2) =
  glueT qq1 as qq2 + pot (glue qq1 as qq2) - pot qq1 - pot qq2
  === 1 + glueT q1 (toTuples (toList v1 ++ as ++ toList u2)) q2
      + pot (More u1 (glue q1 (toTuples (toList v1 ++ as ++ toList u2)) q2) v2)
      - dang u1 - pot q1 - dang v1 - dang u2 - pot q2 - dang v2
  === 1 + glueT q1 (toTuples (toList v1 ++ as ++ toList u2)) q2
      + pot (glue q1 (toTuples (toList v1 ++ as ++ toList u2)) q2)
      - pot q1 - dang v1 - dang u2 - pot q2
  ? glueAmortized q1 (toTuples (toList v1 ++ as ++ toList u2)) q2
  =<= log2 (max (length (seqToList q1) + length (seqToList q2)) 2) + 15
  ? divCancel (max (length (seqToList q1) + length (seqToList q2)) 2)
  === 1 + log2 (2 * max (length (seqToList q1) + length (seqToList q2)) 2 `div` 2) + 14
  === log2 (2 * max (length (seqToList q1) + length (seqToList q2)) 2) + 14
  ? log2Mono (2 * max (length (seqToList q1) + length (seqToList q2)) 2) (4 + 2 * length (seqToList q1) + 2 * length (seqToList q2))
  =<= log2 (4 + 2 * length (seqToList q1) + 2 * length (seqToList q2)) + 14
  ? log2Mono (4 + 2 * length (seqToList q1) + 2 * length (seqToList q2))
      (4 + length (tuplesToList (seqToList q1)) + length (tuplesToList (seqToList q2)))
  =<= log2 (4 + length (tuplesToList (seqToList q1)) + length (tuplesToList (seqToList q2))) + 14
  ? log2Mono (4 + length (tuplesToList (seqToList q1)) + length (tuplesToList (seqToList q2))) 
      (max (length (toList u1 ++ tuplesToList (seqToList q1) ++ toList v1)
        + length (toList u2 ++ tuplesToList (seqToList q2) ++ toList v2)) 2)
  =<= log2 (max (length (toList u1 ++ tuplesToList (seqToList q1) ++ toList v1)
      + length (toList u2 ++ tuplesToList (seqToList q2) ++ toList v2)) 2) + 14
  === log2 (max (length (seqToList qq1) + length (seqToList qq2)) 2) + 14
  *** QED
