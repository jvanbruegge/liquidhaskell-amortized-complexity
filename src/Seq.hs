module Seq where

import Language.Haskell.Liquid.ProofCombinators (Proof, QED (..), (***), (===), (?))

---------------------------------
-- Copy pasted from containers --
---------------------------------

data FingerTree a
  = EmptyT
  | Single a
  | Deep !(Digit a) (FingerTree (Node a)) !(Digit a)

data Node a
  = Node2 a a
  | Node3 a a a

data Digit a
  = One a
  | Two a a
  | Three a a a
  | Four a a a a

data ViewLTree a = ConsLTree a (FingerTree a) | EmptyLTree

{-@ reflect consTree @-}
consTree :: a -> FingerTree a -> FingerTree a
consTree a EmptyT = Single a
consTree a (Single b) = Deep (One a) EmptyT (One b)
consTree a (Deep (Four b c d e) m sf) = Deep (Two a b) (Node3 c d e `consTree` m) sf
consTree a (Deep (Three b c d) m sf) = Deep (Four a b c d) m sf
consTree a (Deep (Two b c) m sf) = Deep (Three a b c) m sf
consTree a (Deep (One b) m sf) = Deep (Two a b) m sf

{-@ viewLTree :: t:FingerTree a -> ViewLTree a / [size t, 0] @-}
viewLTree :: FingerTree a -> ViewLTree a
viewLTree EmptyT = EmptyLTree
viewLTree (Single a) = ConsLTree a EmptyT
viewLTree (Deep (One a) m sf) = ConsLTree a (pullL m sf)
viewLTree (Deep (Two a b) m sf) = ConsLTree a (Deep (One b) m sf)
viewLTree (Deep (Three a b c) m sf) = ConsLTree a (Deep (Two b c) m sf)
viewLTree (Deep (Four a b c d) m sf) = ConsLTree a (Deep (Three b c d) m sf)

{-@ pullL :: t:FingerTree (Node a) -> Digit a -> FingerTree a / [size t, 1] @-}
pullL :: FingerTree (Node a) -> Digit a -> FingerTree a
pullL m sf = case viewLTree m of
  EmptyLTree -> digitToTree' sf
  ConsLTree pr m' -> Deep (nodeToDigit pr) m' sf

digitToTree' :: Digit a -> FingerTree a
digitToTree' (Four a b c d) = Deep (Two a b) EmptyT (Two c d)
digitToTree' (Three a b c) = Deep (Two a b) EmptyT (One c)
digitToTree' (Two a b) = Deep (One a) EmptyT (One b)
digitToTree' (One a) = Single a

nodeToDigit :: Node a -> Digit a
nodeToDigit (Node2 a b) = Two a b
nodeToDigit (Node3 a b c) = Three a b c

-------------------------
-- Complexity analysis --
-------------------------

{-@ size :: FingerTree a -> Nat @-}
{-@ measure size @-}
size :: FingerTree a -> Int
size EmptyT = 0
size (Single _) = 1
size (Deep v q w) = 1 + digitSize v + size q + digitSize w

{-@ digitSize :: Digit a -> Nat @-}
{-@ measure digitSize @-}
digitSize :: Digit a -> Int
digitSize One {} = 1
digitSize Two {} = 2
digitSize Three {} = 3
digitSize Four {} = 4

{-@ phi :: FingerTree a -> Nat @-}
{-@ reflect phi @-}
phi :: FingerTree a -> Int
phi EmptyT = 0
phi (Single _) = 0
phi (Deep u q v) = dang u + phi q + dang v

{-@ dang :: Digit a -> { n:Int | n == 0 || n == 1 } @-}
{-@ reflect dang @-}
dang :: Digit a -> Int
dang One {} = 1
dang Two {} = 0
dang Three {} = 0
dang Four {} = 1

{-@ consT :: a -> FingerTree a -> Nat @-}
{-@ reflect consT @-}
consT :: a -> FingerTree a -> Int
consT _ EmptyT = 1
consT _ (Single _) = 1
consT _ (Deep One {} _ _) = 1
consT _ (Deep Two {} _ _) = 1
consT _ (Deep Three {} _ _) = 1
consT _ (Deep (Four _ a b c) q _) = 1 + consT (Node3 a b c) q

{-@ amortizedConsP :: x:a -> q:FingerTree a -> { consT x q + phi (consTree x q) - phi q <= 3 } @-}
amortizedConsP :: a -> FingerTree a -> Proof
amortizedConsP x EmptyT =
  consT x EmptyT + phi (consTree x EmptyT) - phi EmptyT
    === 1 + phi (Single x) - 0
    === 1
    *** QED
amortizedConsP x t@(Single a) =
  consT x t + phi (consTree x t) - phi t
    === 1 + phi (Deep (One x) EmptyT (One a))
    === 1 + dang (One x) + phi EmptyT + dang (One a)
    === 3
    *** QED
amortizedConsP x t@(Deep (One a) q v) =
  consT x t + phi (consTree x t) - phi t
    === 1 + phi (Deep (Two x a) q v) - dang (One a) - phi q - dang v
    === 1 + dang (Two x a) + phi q + dang v - 1 - phi q - dang v
    === 0
    *** QED
amortizedConsP x t@(Deep (Two a b) q v) =
  consT x t + phi (consTree x t) - phi t
    === 1 + phi (Deep (Three x a b) q v) - phi t
    === 1 + dang (Three x a b) + phi q + dang v - dang (Two a b) - phi q - dang v
    === 1
    *** QED
amortizedConsP x t@(Deep (Three a b c) q v) =
  consT x t + phi (consTree x t) - phi t
    === 1 + phi (Deep (Four x a b c) q v) - phi t
    === 1 + dang (Four x a b c) + phi q + dang v - dang (Three a b c) - phi q - dang v
    === 2
    *** QED
amortizedConsP x t@(Deep (Four a b c d) q v) =
  consT x t + phi (consTree x t) - phi t
    === consT x t + phi (Deep (Two x a) consNode v) - phi t
    === (1 + consT (Node3 b c d) q)
      + (dang (Two x a) + phi consNode + dang v)
      - (dang (Four a b c d) + phi q + dang v)
    === 1 + consT (Node3 b c d) q + dang (Two x a) + phi consNode - dang (Four a b c d) - phi q
    === consT (Node3 b c d) q + phi consNode - phi q
    ? amortizedConsP (Node3 b c d) q
    *** QED
  where
    consNode = consTree (Node3 b c d) q
