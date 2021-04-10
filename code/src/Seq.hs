module Seq where

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
consTree a (Deep (Four b c d e) m sf) = m `seq` Deep (Two a b) (Node3 c d e `consTree` m) sf
consTree a (Deep (Three b c d) m sf) = Deep (Four a b c d) m sf
consTree a (Deep (Two b c) m sf) = Deep (Three a b c) m sf
consTree a (Deep (One b) m sf) = Deep (Two a b) m sf

{-@ viewLTree :: t:FingerTree a -> ViewLTree a / [size t, 0] @-}
{-@ reflect viewLTree @-}
viewLTree :: FingerTree a -> ViewLTree a
viewLTree EmptyT = EmptyLTree
viewLTree (Single a) = ConsLTree a EmptyT
viewLTree (Deep (One a) m sf) = ConsLTree a (pullL m sf)
viewLTree (Deep (Two a b) m sf) = ConsLTree a (Deep (One b) m sf)
viewLTree (Deep (Three a b c) m sf) = ConsLTree a (Deep (Two b c) m sf)
viewLTree (Deep (Four a b c d) m sf) = ConsLTree a (Deep (Three b c d) m sf)

{-@ pullL :: t:FingerTree (Node a) -> Digit a -> FingerTree a / [size t, 1] @-}
{-@ reflect pullL @-}
pullL :: FingerTree (Node a) -> Digit a -> FingerTree a
pullL m sf = case viewLTree m of
  EmptyLTree -> digitToTree' sf
  ConsLTree pr m' -> Deep (nodeToDigit pr) m' sf

{-@ reflect digitToTree' @-}
digitToTree' :: Digit a -> FingerTree a
digitToTree' (Four a b c d) = Deep (Two a b) EmptyT (Two c d)
digitToTree' (Three a b c) = Deep (Two a b) EmptyT (One c)
digitToTree' (Two a b) = Deep (One a) EmptyT (One b)
digitToTree' (One a) = Single a

{-@ reflect nodeToDigit @-}
nodeToDigit :: Node a -> Digit a
nodeToDigit (Node2 a b) = Two a b
nodeToDigit (Node3 a b c) = Three a b c

{-@ reflect snocTree @-}
snocTree :: FingerTree a -> a -> FingerTree a
snocTree EmptyT a = Single a
snocTree (Single a) b = Deep (One a) EmptyT (One b)
-- See note on `seq` in `consTree`.
snocTree (Deep pr m (Four a b c d)) e = m `seq` Deep pr (m `snocTree` Node3 a b c) (Two d e)
snocTree (Deep pr m (Three a b c)) d = Deep pr m (Four a b c d)
snocTree (Deep pr m (Two a b)) c = Deep pr m (Three a b c)
snocTree (Deep pr m (One a)) b = Deep pr m (Two a b)

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

{-@ phiView :: ViewLTree a -> Nat @-}
{-@ reflect phiView @-}
phiView :: ViewLTree a -> Int
phiView EmptyLTree = 0
phiView (ConsLTree _ t) = phi t

{-@ dang :: Digit a -> { n:Int | n == 0 || n == 1 } @-}
{-@ reflect dang @-}
dang :: Digit a -> Int
dang One {} = 1
dang Two {} = 0
dang Three {} = 0
dang Four {} = 1
