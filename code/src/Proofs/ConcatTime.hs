{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Proofs.ConcatTime where

import Seq

{-@ concatT :: FingerTree a -> FingerTree a -> Nat @-}
{-@ reflect concatT @-}
concatT :: FingerTree a -> FingerTree a -> Int
concatT EmptyT _ = 1
concatT _ EmptyT = 1
concatT (Single _) _ = 1
concatT _ (Single _) = 1
concatT (Deep pr1 m1 sf1) (Deep pr2 m2 sf2) = addDigits0T m1 sf1 pr2 m2

{-@ addDigits0T :: a:FingerTree (Node a) -> Digit a -> Digit a -> FingerTree (Node a) -> Nat / [size a, 5] @-}
{-@ reflect addDigits0T @-}
addDigits0T :: FingerTree (Node a) -> Digit a -> Digit a -> FingerTree (Node a) -> Int
addDigits0T m1 (One a) (One b) m2 = 1 + appendTree1T m1 (Node2 a b) m2
addDigits0T m1 (One a) (Two b c) m2 = 1 + appendTree1T m1 (Node3 a b c) m2
addDigits0T m1 (One a) (Three b c d) m2 = 1 + appendTree2T m1 (Node2 a b) (Node2 c d) m2
addDigits0T m1 (One a) (Four b c d e) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node2 d e) m2
addDigits0T m1 (Two a b) (One c) m2 = 1 + appendTree1T m1 (Node3 a b c) m2
addDigits0T m1 (Two a b) (Two c d) m2 = 1 + appendTree2T m1 (Node2 a b) (Node2 c d) m2
addDigits0T m1 (Two a b) (Three c d e) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node2 d e) m2
addDigits0T m1 (Two a b) (Four c d e f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits0T m1 (Three a b c) (One d) m2 = 1 + appendTree2T m1 (Node2 a b) (Node2 c d) m2
addDigits0T m1 (Three a b c) (Two d e) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node2 d e) m2
addDigits0T m1 (Three a b c) (Three d e f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits0T m1 (Three a b c) (Four d e f g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits0T m1 (Four a b c d) (One e) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node2 d e) m2
addDigits0T m1 (Four a b c d) (Two e f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits0T m1 (Four a b c d) (Three e f g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits0T m1 (Four a b c d) (Four e f g h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2

{-@ appendTree1T :: a:FingerTree (Node a) -> Node a -> FingerTree (Node a) -> Nat / [size a, 1] @-}
{-@ reflect appendTree1T @-}
appendTree1T :: FingerTree (Node a) -> Node a -> FingerTree (Node a) -> Int
appendTree1T EmptyT !a xs = 1
appendTree1T xs !a EmptyT = 1
appendTree1T (Single x) !a xs = 1
appendTree1T xs !a (Single x) = 1
appendTree1T (Deep pr1 m1 sf1) a (Deep pr2 m2 sf2) = 1 + addDigits1T m1 sf1 a pr2 m2

{-@ addDigits1T :: a:FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> Nat / [size a, 5] @-}
{-@ reflect addDigits1T @-}
addDigits1T :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> Int
addDigits1T m1 (One a) b (One c) m2 = 1 + appendTree1T m1 (Node3 a b c) m2
addDigits1T m1 (One a) b (Two c d) m2 = 1 + appendTree2T m1 (Node2 a b) (Node2 c d) m2
addDigits1T m1 (One a) b (Three c d e) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node2 d e) m2
addDigits1T m1 (One a) b (Four c d e f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits1T m1 (Two a b) c (One d) m2 = 1 + appendTree2T m1 (Node2 a b) (Node2 c d) m2
addDigits1T m1 (Two a b) c (Two d e) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node2 d e) m2
addDigits1T m1 (Two a b) c (Three d e f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits1T m1 (Two a b) c (Four d e f g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits1T m1 (Three a b c) d (One e) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node2 d e) m2
addDigits1T m1 (Three a b c) d (Two e f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits1T m1 (Three a b c) d (Three e f g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits1T m1 (Three a b c) d (Four e f g h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits1T m1 (Four a b c d) e (One f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits1T m1 (Four a b c d) e (Two f g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits1T m1 (Four a b c d) e (Three f g h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits1T m1 (Four a b c d) e (Four f g h i) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2

{-@ appendTree2T :: a:FingerTree (Node a) -> Node a -> Node a -> FingerTree (Node a) -> Nat / [size a, 2] @-}
{-@ reflect appendTree2T @-}
appendTree2T :: FingerTree (Node a) -> Node a -> Node a -> FingerTree (Node a) -> Int
appendTree2T EmptyT !a !b xs = 1
appendTree2T xs !a !b EmptyT = 1
appendTree2T (Single x) a b xs = 1
appendTree2T xs a b (Single x) = 1
appendTree2T (Deep pr1 m1 sf1) a b (Deep pr2 m2 sf2) = 1 + addDigits2T m1 sf1 a b pr2 m2

{-@ addDigits2T :: a:FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> Nat / [size a, 5] @-}
{-@ reflect addDigits2T @-}
addDigits2T :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> Int
addDigits2T m1 (One a) b c (One d) m2 = 1 + appendTree2T m1 (Node2 a b) (Node2 c d) m2
addDigits2T m1 (One a) b c (Two d e) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node2 d e) m2
addDigits2T m1 (One a) b c (Three d e f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits2T m1 (One a) b c (Four d e f g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits2T m1 (Two a b) c d (One e) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node2 d e) m2
addDigits2T m1 (Two a b) c d (Two e f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits2T m1 (Two a b) c d (Three e f g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits2T m1 (Two a b) c d (Four e f g h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits2T m1 (Three a b c) d e (One f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits2T m1 (Three a b c) d e (Two f g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits2T m1 (Three a b c) d e (Three f g h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits2T m1 (Three a b c) d e (Four f g h i) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits2T m1 (Four a b c d) e f (One g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits2T m1 (Four a b c d) e f (Two g h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits2T m1 (Four a b c d) e f (Three g h i) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits2T m1 (Four a b c d) e f (Four g h i j) m2 = 1 + appendTree4T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2

{-@ appendTree3T :: a:FingerTree (Node a) -> Node a -> Node a -> Node a -> FingerTree (Node a) -> Nat / [size a, 3] @-}
{-@ reflect appendTree3T @-}
appendTree3T :: FingerTree (Node a) -> Node a -> Node a -> Node a -> FingerTree (Node a) -> Int
appendTree3T EmptyT !a !b !c xs = 1
appendTree3T xs !a !b !c EmptyT = 1
appendTree3T (Single x) a b c xs = 1
appendTree3T xs a b c (Single x) = 1
appendTree3T (Deep pr1 m1 sf1) a b c (Deep pr2 m2 sf2) = 1 + addDigits3T m1 sf1 a b c pr2 m2

{-@ addDigits3T :: a:FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> Nat / [size a, 5] @-}
{-@ reflect addDigits3T @-}
addDigits3T :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> Int
addDigits3T m1 (One a) !b !c !d (One e) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node2 d e) m2
addDigits3T m1 (One a) b c d (Two e f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits3T m1 (One a) b c d (Three e f g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits3T m1 (One a) b c d (Four e f g h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits3T m1 (Two a b) !c !d !e (One f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits3T m1 (Two a b) c d e (Two f g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits3T m1 (Two a b) c d e (Three f g h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits3T m1 (Two a b) c d e (Four f g h i) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits3T m1 (Three a b c) !d !e !f (One g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits3T m1 (Three a b c) d e f (Two g h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits3T m1 (Three a b c) d e f (Three g h i) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits3T m1 (Three a b c) d e f (Four g h i j) m2 = 1 + appendTree4T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2
addDigits3T m1 (Four a b c d) !e !f !g (One h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits3T m1 (Four a b c d) e f g (Two h i) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits3T m1 (Four a b c d) e f g (Three h i j) m2 = 1 + appendTree4T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2
addDigits3T m1 (Four a b c d) e f g (Four h i j k) m2 = 1 + appendTree4T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) (Node2 j k) m2

{-@ appendTree4T :: a:FingerTree (Node a) -> Node a -> Node a -> Node a -> Node a -> FingerTree (Node a) -> Nat / [size a, 4] @-}
{-@ reflect appendTree4T @-}
appendTree4T :: FingerTree (Node a) -> Node a -> Node a -> Node a -> Node a -> FingerTree (Node a) -> Int
appendTree4T EmptyT !a !b !c !d xs = 1
appendTree4T xs !a !b !c !d EmptyT = 1
appendTree4T (Single x) a b c d xs = 1
appendTree4T xs a b c d (Single x) = 1
appendTree4T (Deep pr1 m1 sf1) a b c d (Deep pr2 m2 sf2) = 1 + addDigits4T m1 sf1 a b c d pr2 m2

{-@ addDigits4T :: a:FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> Nat / [size a, 5] @-}
{-@ reflect addDigits4T @-}
addDigits4T :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> Int
addDigits4T m1 (One a) !b !c !d !e (One f) m2 = 1 + appendTree2T m1 (Node3 a b c) (Node3 d e f) m2
addDigits4T m1 (One a) b c d e (Two f g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits4T m1 (One a) b c d e (Three f g h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits4T m1 (One a) b c d e (Four f g h i) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits4T m1 (Two a b) !c !d !e !f (One g) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node2 d e) (Node2 f g) m2
addDigits4T m1 (Two a b) c d e f (Two g h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits4T m1 (Two a b) c d e f (Three g h i) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits4T m1 (Two a b) c d e f (Four g h i j) m2 = 1 + appendTree4T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2
addDigits4T m1 (Three a b c) !d !e !f !g (One h) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) m2
addDigits4T m1 (Three a b c) d e f g (Two h i) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits4T m1 (Three a b c) d e f g (Three h i j) m2 = 1 + appendTree4T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2
addDigits4T m1 (Three a b c) d e f g (Four h i j k) m2 = 1 + appendTree4T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) (Node2 j k) m2
addDigits4T m1 (Four a b c d) !e !f !g !h (One i) m2 = 1 + appendTree3T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) m2
addDigits4T m1 (Four a b c d) !e !f !g !h (Two i j) m2 = 1 + appendTree4T m1 (Node3 a b c) (Node3 d e f) (Node2 g h) (Node2 i j) m2
addDigits4T m1 (Four a b c d) !e !f !g !h (Three i j k) m2 = 1 + appendTree4T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) (Node2 j k) m2
addDigits4T m1 (Four a b c d) !e !f !g !h (Four i j k l) m2 = 1 + appendTree4T m1 (Node3 a b c) (Node3 d e f) (Node3 g h i) (Node3 j k l) m2
