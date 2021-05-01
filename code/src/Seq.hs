{-# LANGUAGE BangPatterns #-}

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

infixr 5 `consTree`

infixl 5 `snocTree`

infixr 5 `appendTree0`

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

{-@ reflect appendTree0 @-}
appendTree0 :: FingerTree a -> FingerTree a -> FingerTree a
appendTree0 EmptyT xs = xs
appendTree0 xs EmptyT = xs
appendTree0 (Single x) xs = x `consTree` xs
appendTree0 xs (Single x) = xs `snocTree` x
appendTree0 (Deep pr1 m1 sf1) (Deep pr2 m2 sf2) = Deep pr1 m sf2
  where
    !m = addDigits0 m1 sf1 pr2 m2

{-@ addDigits0 :: a:FingerTree (Node a) -> Digit a -> Digit a -> FingerTree (Node a) -> FingerTree (Node a) / [size a, 5] @-}
{-@ reflect addDigits0 @-}
addDigits0 :: FingerTree (Node a) -> Digit a -> Digit a -> FingerTree (Node a) -> FingerTree (Node a)
addDigits0 m1 (One a) (One b) m2 = appendTree1 m1 (Node2 a b) m2
addDigits0 m1 (One a) (Two b c) m2 = appendTree1 m1 (Node3 a b c) m2
addDigits0 m1 (One a) (Three b c d) m2 = appendTree2 m1 (Node2 a b) (Node2 c d) m2
addDigits0 m1 (One a) (Four b c d e) m2 = appendTree2 m1 (Node3 a b c) (Node2 d e) m2
addDigits0 m1 (Two a b) (One c) m2 = appendTree1 m1 (Node3 a b c) m2
addDigits0 m1 (Two a b) (Two c d) m2 = appendTree2 m1 (Node2 a b) (Node2 c d) m2
addDigits0 m1 (Two a b) (Three c d e) m2 = appendTree2 m1 (Node3 a b c) (Node2 d e) m2
addDigits0 m1 (Two a b) (Four c d e f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits0 m1 (Three a b c) (One d) m2 = appendTree2 m1 (Node2 a b) (Node2 c d) m2
addDigits0 m1 (Three a b c) (Two d e) m2 = appendTree2 m1 (Node3 a b c) (Node2 d e) m2
addDigits0 m1 (Three a b c) (Three d e f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits0 m1 (Three a b c) (Four d e f g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits0 m1 (Four a b c d) (One e) m2 = appendTree2 m1 (Node3 a b c) (Node2 d e) m2
addDigits0 m1 (Four a b c d) (Two e f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits0 m1 (Four a b c d) (Three e f g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits0 m1 (Four a b c d) (Four e f g h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2

{-@ appendTree1 :: a:FingerTree (Node a) -> Node a -> FingerTree (Node a) -> FingerTree (Node a) / [size a, 1] @-}
{-@ reflect appendTree1 @-}
appendTree1 :: FingerTree (Node a) -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree1 EmptyT !a xs = a `consTree` xs
appendTree1 xs !a EmptyT = xs `snocTree` a
appendTree1 (Single x) !a xs = x `consTree` a `consTree` xs
appendTree1 xs !a (Single x) = xs `snocTree` a `snocTree` x
appendTree1 (Deep pr1 m1 sf1) a (Deep pr2 m2 sf2) = Deep pr1 m sf2
  where
    !m = addDigits1 m1 sf1 a pr2 m2

{-@ addDigits1 :: a:FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a)) / [size a, 5] @-}
{-@ reflect addDigits1 @-}
addDigits1 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits1 m1 (One a) b (One c) m2 = appendTree1 m1 (Node3 a b c) m2
addDigits1 m1 (One a) b (Two c d) m2 = appendTree2 m1 (Node2 a b) (Node2 c d) m2
addDigits1 m1 (One a) b (Three c d e) m2 = appendTree2 m1 (Node3 a b c) (Node2 d e) m2
addDigits1 m1 (One a) b (Four c d e f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits1 m1 (Two a b) c (One d) m2 = appendTree2 m1 (Node2 a b) (Node2 c d) m2
addDigits1 m1 (Two a b) c (Two d e) m2 = appendTree2 m1 (Node3 a b c) (Node2 d e) m2
addDigits1 m1 (Two a b) c (Three d e f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits1 m1 (Two a b) c (Four d e f g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits1 m1 (Three a b c) d (One e) m2 = appendTree2 m1 (Node3 a b c) (Node2 d e) m2
addDigits1 m1 (Three a b c) d (Two e f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits1 m1 (Three a b c) d (Three e f g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits1 m1 (Three a b c) d (Four e f g h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits1 m1 (Four a b c d) e (One f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits1 m1 (Four a b c d) e (Two f g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits1 m1 (Four a b c d) e (Three f g h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits1 m1 (Four a b c d) e (Four f g h i) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2

{-@ appendTree2 :: a:FingerTree (Node a) -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a) / [size a, 2] @-}
{-@ reflect appendTree2 @-}
appendTree2 :: FingerTree (Node a) -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree2 EmptyT !a !b xs = a `consTree` b `consTree` xs
appendTree2 xs !a !b EmptyT = xs `snocTree` a `snocTree` b
appendTree2 (Single x) a b xs = x `consTree` a `consTree` b `consTree` xs
appendTree2 xs a b (Single x) = xs `snocTree` a `snocTree` b `snocTree` x
appendTree2 (Deep pr1 m1 sf1) a b (Deep pr2 m2 sf2) = Deep pr1 m sf2
  where
    !m = addDigits2 m1 sf1 a b pr2 m2

{-@ addDigits2 :: a:FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a)) / [size a, 5] @-}
{-@ reflect addDigits2 @-}
addDigits2 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits2 m1 (One a) b c (One d) m2 = appendTree2 m1 (Node2 a b) (Node2 c d) m2
addDigits2 m1 (One a) b c (Two d e) m2 = appendTree2 m1 (Node3 a b c) (Node2 d e) m2
addDigits2 m1 (One a) b c (Three d e f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits2 m1 (One a) b c (Four d e f g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits2 m1 (Two a b) c d (One e) m2 = appendTree2 m1 (Node3 a b c) (Node2 d e) m2
addDigits2 m1 (Two a b) c d (Two e f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits2 m1 (Two a b) c d (Three e f g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits2 m1 (Two a b) c d (Four e f g h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits2 m1 (Three a b c) d e (One f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits2 m1 (Three a b c) d e (Two f g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits2 m1 (Three a b c) d e (Three f g h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits2 m1 (Three a b c) d e (Four f g h i) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (One g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits2 m1 (Four a b c d) e f (Two g h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits2 m1 (Four a b c d) e f (Three g h i) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 = appendTree4 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2

{-@ appendTree3 :: a:FingerTree (Node a) -> Node a -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a) / [size a, 3] @-}
{-@ reflect appendTree3 @-}
appendTree3 :: FingerTree (Node a) -> Node a -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree3 EmptyT !a !b !c xs = a `consTree` b `consTree` c `consTree` xs
appendTree3 xs !a !b !c EmptyT = xs `snocTree` a `snocTree` b `snocTree` c
appendTree3 (Single x) a b c xs = x `consTree` a `consTree` b `consTree` c `consTree` xs
appendTree3 xs a b c (Single x) = xs `snocTree` a `snocTree` b `snocTree` c `snocTree` x
appendTree3 (Deep pr1 m1 sf1) a b c (Deep pr2 m2 sf2) = Deep pr1 m sf2
  where
    !m = addDigits3 m1 sf1 a b c pr2 m2

{-@ addDigits3 :: a:FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a)) / [size a, 5] @-}
{-@ reflect addDigits3 @-}
addDigits3 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits3 m1 (One a) !b !c !d (One e) m2 = appendTree2 m1 (Node3 a b c) (Node2 d e) m2
addDigits3 m1 (One a) b c d (Two e f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits3 m1 (One a) b c d (Three e f g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits3 m1 (One a) b c d (Four e f g h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits3 m1 (Two a b) !c !d !e (One f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits3 m1 (Two a b) c d e (Two f g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits3 m1 (Two a b) c d e (Three f g h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits3 m1 (Two a b) c d e (Four f g h i) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits3 m1 (Three a b c) !d !e !f (One g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits3 m1 (Three a b c) d e f (Two g h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits3 m1 (Three a b c) d e f (Three g h i) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 = appendTree4 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2
addDigits3 m1 (Four a b c d) !e !f !g (One h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits3 m1 (Four a b c d) e f g (Two h i) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 = appendTree4 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 = appendTree4 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) (Node2 j k) m2

{-@ appendTree4 :: a:FingerTree (Node a) -> Node a -> Node a -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a) / [size a, 4] @-}
{-@ reflect appendTree4 @-}
appendTree4 :: FingerTree (Node a) -> Node a -> Node a -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree4 EmptyT !a !b !c !d xs = a `consTree` b `consTree` c `consTree` d `consTree` xs
appendTree4 xs !a !b !c !d EmptyT = xs `snocTree` a `snocTree` b `snocTree` c `snocTree` d
appendTree4 (Single x) a b c d xs = x `consTree` a `consTree` b `consTree` c `consTree` d `consTree` xs
appendTree4 xs a b c d (Single x) = xs `snocTree` a `snocTree` b `snocTree` c `snocTree` d `snocTree` x
appendTree4 (Deep pr1 m1 sf1) a b c d (Deep pr2 m2 sf2) = Deep pr1 m sf2
  where
    !m = addDigits4 m1 sf1 a b c d pr2 m2

{-@ addDigits4 :: a:FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a)) / [size a, 5] @-}
{-@ reflect addDigits4 @-}
addDigits4 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits4 m1 (One a) !b !c !d !e (One f) m2 = appendTree2 m1 (Node3 a b c) (Node3 d e f) m2
addDigits4 m1 (One a) b c d e (Two f g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits4 m1 (One a) b c d e (Three f g h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits4 m1 (One a) b c d e (Four f g h i) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits4 m1 (Two a b) !c !d !e !f (One g) m2 = appendTree3 m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits4 m1 (Two a b) c d e f (Two g h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits4 m1 (Two a b) c d e f (Three g h i) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 = appendTree4 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2
addDigits4 m1 (Three a b c) !d !e !f !g (One h) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits4 m1 (Three a b c) d e f g (Two h i) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 = appendTree4 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 = appendTree4 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) (Node2 j k) m2
addDigits4 m1 (Four a b c d) !e !f !g !h (One i) m2 = appendTree3 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits4 m1 (Four a b c d) !e !f !g !h (Two i j) m2 = appendTree4 m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2
addDigits4 m1 (Four a b c d) !e !f !g !h (Three i j k) m2 = appendTree4 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) (Node2 j k) m2
addDigits4 m1 (Four a b c d) !e !f !g !h (Four i j k l) m2 = appendTree4 m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) (Node3 j k l) m2

-------------------------
-- Complexity analysis --
-------------------------

{-@ size :: FingerTree a -> Nat @-}
{-@ measure size @-}
size :: FingerTree a -> Int
size EmptyT = 0
size (Single _) = 1
size (Deep _ q _) = 2 + size q

{-@ dSize :: FingerTree a -> { d:Double | d >= 0 } @-}
{-@ reflect dSize @-}
dSize :: FingerTree a -> Double
dSize EmptyT = 0
dSize (Single _) = 1
dSize (Deep _ q _) = 2 + dSize q

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
