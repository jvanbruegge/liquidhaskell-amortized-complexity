{-@ LIQUID "--ple-local" @-}

module Stack (Stack, push, multipop) where

import Language.Haskell.Liquid.ProofCombinators (Proof, QED (..), (***), (===), (?), trivial)
import Prelude hiding (min)

data Stack a = Nil | Cons a (Stack a)

{-@ inline min @-}
min :: Int -> Int -> Int
min x y = if x <= y then x else y

{-@ measure slen @-}
{-@ slen :: s:Stack a -> { n:Int | n >= 0 } @-}
slen :: Stack a -> Int
slen Nil = 0
slen (Cons _ xs) = 1 + slen xs

{-@ push :: a -> s:Stack a -> { s':Stack a | slen s' = slen s + 1 } @-}
{-@ reflect push @-}
push :: a -> Stack a -> Stack a
push x xs = Cons x xs

{-@ multipop :: { n:Int | n >= 0 } -> s:Stack a -> { p:([a], Stack a) |
      len (fst p) == min n (slen s) && slen (snd p) == slen s - min n (slen s) } @-}
{-@ reflect multipop @-}
multipop :: Int -> Stack a -> ([a], Stack a)
multipop 0 xs = ([], xs)
multipop _ Nil = ([], Nil)
multipop n (Cons x xs) = case multipop (n - 1) xs of (l, s) -> (x : l, s)

------------------------
-- Potential Analysis --
------------------------

{-@ inline t_push @-}
t_push :: a -> Stack a -> Int
t_push _ _ = 1

{-@ inline t_multipop @-}
t_multipop :: Int -> Stack a -> Int
t_multipop n xs = min n (slen xs)

{-@ inline phi @-}
phi :: Stack a -> Int
phi s = slen s

{-@ c1 :: { n:Int | n >= 0 } @-}
{-@ inline c1 @-}
c1 :: Int
c1 = 2

{-@ c2 :: { n:Int | n >= 0 } @-}
{-@ inline c2 @-}
c2 :: Int
c2 = 0

{-@ ammortized_push :: x:a -> st:Stack a -> { t_push x st + phi (push x st) - phi st == c1 } @-}
ammortized_push :: a -> Stack a -> Proof
ammortized_push x st = t_push x st + phi (push x st) - phi st *** QED

{-@ ammortized_pop :: { n:Int | n >= 0 } -> st:Stack a -> { t_multipop n st + phi (snd (multipop n st)) - phi st == c2 } @-}
ammortized_pop :: Int -> Stack a -> Proof
ammortized_pop n st = t_multipop n st + phi (snd (multipop n st)) - phi st *** QED

-----------------------------------------------
-- Without complex postcondition on multipop --
-----------------------------------------------

{-@ multipop2 :: { n:Int | n >= 0 } -> s:Stack a -> p:([a], Stack a) @-}
{-@ reflect multipop2 @-}
multipop2 :: Int -> Stack a -> ([a], Stack a)
multipop2 0 xs = ([], xs)
multipop2 _ Nil = ([], Nil)
multipop2 n (Cons x xs) = case multipop2 (n - 1) xs of (l, s) -> (x : l, s)

{-@ automatic-instances ammortized_pop2 @-}
{-@ ammortized_pop2 :: { n:Int | n >= 0 } -> st:Stack a -> { t_multipop n st + phi (snd (multipop2 n st)) - phi st == c2 } @-}
ammortized_pop2 :: Int -> Stack a -> Proof
ammortized_pop2 0 _ = trivial
ammortized_pop2 _ Nil = trivial
ammortized_pop2 n (Cons x xs) =
  t_multipop n (Cons x xs) + phi (snd (multipop2 n (Cons x xs))) - phi (Cons x xs)
    === t_multipop n (Cons x xs) + phi (snd (case multipop2 (n - 1) xs of (l, st') -> (x : l, st'))) - phi (Cons x xs)
    === t_multipop n (Cons x xs) + phi (snd (multipop2 (n - 1) xs)) - phi (Cons x xs)
    === 1 + t_multipop (n - 1) xs + phi (snd (multipop2 (n - 1) xs)) - phi (Cons x xs)
    === 1 + t_multipop (n - 1) xs + phi (snd (multipop2 (n - 1) xs)) - phi xs - 1
    === t_multipop (n - 1) xs + phi (snd (multipop2 (n - 1) xs)) - phi xs
    ? ammortized_pop2 (n - 1) xs
    === c2
    *** QED
