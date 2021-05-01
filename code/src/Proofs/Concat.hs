module Proofs.Concat where

import Language.Haskell.Liquid.ProofCombinators (Proof, QED (..), trivial, (***), (=<=), (===), (?))
import Proofs.ConcatTime
import Proofs.Cons
import Seq
import Prelude hiding (min)

{-@ type PDouble = { x:Double | x > 0 } @-}

{-@ pow2Aux :: Nat -> PDouble @-}
{-@ reflect pow2Aux @-}
pow2Aux :: Int -> Double
pow2Aux 0 = 1
pow2Aux n = 2 * pow2Aux (n - 1)

{-@ pow2 :: Int -> Double @-}
{-@ reflect pow2 @-}
pow2 :: Int -> Double
pow2 n = if n < 0 then 1 / pow2Aux (- n) else pow2Aux n

{-@ assume pow2AddP :: a:Int -> b:Int -> { pow2 (a + b) == pow2 a * pow2 b } @-}
pow2AddP :: Int -> Int -> Proof
pow2AddP _ _ = ()

{-@ assume timesPow2P :: x:Double -> { n:Int | n >= -1 && n <= 1 } -> { x * pow2 n <= 2 * x } @-}
timesPow2P :: Double -> Int -> Proof
timesPow2P _ _ = ()

-- This function has its arguments flip or LiquidHaskell tries to induct on the wrong variable
{-@ powAux :: Nat -> PDouble -> PDouble @-}
{-@ reflect powAux @-}
powAux :: Int -> Double -> Double
powAux 0 _ = 1
powAux n x = x * powAux (n - 1) x

{-@ pow :: PDouble -> Nat -> PDouble @-}
{-@ inline pow @-}
pow :: Double -> Int -> Double
pow x n = powAux n x

{-@ assume powBinomP :: x:PDouble -> y:PDouble -> { pow (x + y) 2 = pow x 2 + 2 * x * y + pow y 2 } @-}
powBinomP :: Double -> Double -> Proof
powBinomP _ _ = ()

{-
{-@ assume pow2LessP :: { n:Int | n <= 5 } -> { pow2 n <= 32 } @-}
pow2LessP :: Int -> Proof
pow2LessP _ = ()
-}

{-

{-@ amortizedConcatP :: t1:FingerTree a -> { t2:FingerTree a | size t1 <= size t2 } -> { pow2 (concatT t1 t2 + phi (appendTree0 t1 t2) - phi t2) <= 128 * (size t1 + 1) } @-}
amortizedConcatP :: FingerTree a -> FingerTree a -> Proof
{-amortizedConcatP EmptyT xs =
  pow2 (concatT EmptyT xs + phi (appendTree0 EmptyT xs) - phi xs)
    === pow2 (1 + phi xs - phi xs)
    === pow2Pos 1
    === 2 * pow2Pos 0
    *** QED
amortizedConcatP t1@(Single x) t2 =
  pow2 (concatT t1 t2 + phi (appendTree0 t1 t2) - phi t2)
    === pow2 expr ? amortizedCons1P x t2 ? pow2LessP expr
    *** QED
  where
    expr = 1 + phi (consTree x t2) - phi t2
amortizedConcatP t1@(Deep pr1 m1 sf1) t2@(Deep pr2 m2 sf2) =
  pow2 (concatT t1 t2 + phi (appendTree0 t1 t2) - phi t2)
    === pow2 (addDigits0T m1 sf1 pr2 m2 + phi (Deep pr1 (addDigits0 m1 sf1 pr2 m2) sf2) - phi t2)
    === pow2 (addDigits0T m1 sf1 pr2 m2 + phi (addDigits0 m1 sf1 pr2 m2) + dang pr1 + dang sf2 - dang pr2 - phi m2 - dang sf2)
    === pow2 (expr + dang pr1 - dang pr2) ? pow2AddP expr (dang pr1 - dang pr2)
    === pow2 expr * pow2 (dang pr1 - dang pr2) ? amortizedAddDigits0P m1 sf1 pr2 m2 ? timesPow2P (pow2 expr) (dang pr1 - dang pr2)
    *** QED
  where
    expr = addDigits0T m1 sf1 pr2 m2 + phi (addDigits0 m1 sf1 pr2 m2) - phi m2
amortizedConcatP _ _ = error "impossible"-}
amortizedConcatP = undefined

{-@ amortizedAddDigits0P :: m1:FingerTree (Node a) -> sf1:Digit a -> pr2:Digit a -> { m2:FingerTree (Node a) | size m1 <= size m2 } -> { pow2 (addDigits0T m1 sf1 pr2 m2 + phi (addDigits0 m1 sf1 pr2 m2) - phi m2) <= 64 * (size m1 + 1) }  @-}
amortizedAddDigits0P :: FingerTree (Node a) -> Digit a -> Digit a -> FingerTree (Node a) -> Proof
{-amortizedAddDigits0P m1 sf1@(One a) pr2@(One b) m2 =
  pow2 (addDigits0T m1 sf1 pr2 m2 + phi (addDigits0 m1 sf1 pr2 m2) - phi m2)
    === pow2 (1 + expr) ? pow2AddP 1 expr
    === pow2 1 * pow2 expr ? amortizedAppendTree1P m1 (Node2 a b) m2 ? timesPow2P (pow2 expr) 1
    *** QED
  where
    expr = appendTree1T m1 (Node2 a b) m2 + phi (appendTree1 m1 (Node2 a b) m2) - phi m2
amortizedAddDigits0P m1 sf1@(One a) pr2@(Two b c) m2 =
  pow2 (addDigits0T m1 sf1 pr2 m2 + phi (addDigits0 m1 sf1 pr2 m2) - phi m2)
    === pow2 (1 + expr) ? pow2AddP 1 expr
    === pow2 1 * pow2 expr ? amortizedAppendTree1P m1 (Node3 a b c) m2 ? timesPow2P (pow2 expr) 1
    *** QED
  where
    expr = appendTree1T m1 (Node3 a b c) m2 + phi (appendTree1 m1 (Node3 a b c) m2) - phi m2
-}
amortizedAddDigits0P _ _ _ _ = undefined

-}

{-amortizedAppendTree1P m1@EmptyT n m2 =
  pow2 (appendTree1T m1 n m2 + phi (appendTree1 m1 n m2) - phi m2)
    === pow2 expr ? amortizedCons1P n m2 ? pow2LessP expr
    *** QED
  where
    expr = 1 + phi (consTree n m2) - phi m2
amortizedAppendTree1P _ _ EmptyT = trivial
amortizedAppendTree1P m1@(Single a) n m2 =
  pow2 (appendTree1T m1 n m2 + phi (appendTree1 m1 n m2) - phi m2)
    === pow2 (1 + phi (consTree a (consTree n m2)) - phi m2)
    === pow2 expr ? amortizedCons1P a (consTree n m2) ? amortizedCons1P n m2 ? pow2LessP expr
    *** QED
  where
    expr =
      (1 + phi (consTree a (consTree n m2)) - phi (consTree n m2))
        + (1 + phi (consTree n m2) - phi m2)
        - 1
amortizedAppendTree1P _ _ (Single _) = trivial
-}
{-@ amortizedAppendTree1P :: t1:FingerTree (Node a) -> n:Node a -> { t2:FingerTree (Node a) | size t1 <= size t2 } -> { pow2 (appendTree1T t1 n t2 + phi (appendTree1 t1 n t2) - phi t2) <= pow (dSize t1 + 1) 2 } @-}
amortizedAppendTree1P :: FingerTree (Node a) -> Node a -> FingerTree (Node a) -> Proof
amortizedAppendTree1P t1@(Deep pr1 m1 sf1) n t2@(Deep pr2 m2 sf2) =
  pow2 (appendTree1T t1 n t2 + phi (appendTree1 t1 n t2) - phi t2)
    === pow2 (1 + addDigits1T m1 sf1 n pr2 m2 + phi (Deep pr1 (addDigits1 m1 sf1 n pr2 m2) sf2) - phi t2)
    === pow2 (expr + 1 + dang pr1 - dang pr2) ? pow2AddP expr (1 + dang pr1 - dang pr2)
    === pow2 expr * pow2 (1 + dang pr1 - dang pr2) ? pow2AddP 1 (dang pr1 - dang pr2)
    === pow2 expr * pow2 1 * pow2 (dang pr1 - dang pr2) ? timesPow2P (pow2 expr * pow2 1) (dang pr1 - dang pr2)
    =<= 2 * pow2 expr * pow2 1
    === 2 * pow2 expr * pow2Aux 1
    === 2 * 2 * pow2Aux 0 * pow2 expr
    === 4 * pow2 expr ? amortizedAddDigits1P m1 sf1 n pr2 m2
    =<= 4 * pow (dSize m1 + 1) 2
    === undefined
    *** QED
  where
    expr = addDigits1T m1 sf1 n pr2 m2 + phi (addDigits1 m1 sf1 n pr2 m2) - phi m2
amortizedAppendTree1P _ _ _ = undefined

{-@ amortizedAddDigits1P:: m1:FingerTree (Node (Node a)) -> sf1:Digit (Node a) -> n:Node a -> pr2:Digit (Node a) -> { m2:FingerTree (Node (Node a)) | size m1 <= size m2 } -> { pow2 (addDigits1T m1 sf1 n pr2 m2 + phi (addDigits1 m1 sf1 n pr2 m2) - phi m2) <= pow (dSize m1 + 1) 2 } @-}
amortizedAddDigits1P :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> Proof
{-amortizedAddDigits1P m1 (One a) b (One c) m2 =
  pow2 (addDigits1T m1 (One a) b (One c) m2 + phi (addDigits1 m1 (One a) b (One c) m2) - phi m2)
    === pow2 (1 + expr) ? pow2AddP 1 expr
    === pow2 1 * pow2 expr
    === pow2Pos 1 * pow2 expr
    === 2 * pow2Pos 0 * pow2 expr ? amortizedAppendTree1P m1 (Node a b c) m2
    === undefined
    *** QED
  where
    expr = appendTree1T m1 (Node3 a b c) m2 + phi (appendTree1 m1 (Node3 a b c) m2) - phi m2
-}
amortizedAddDigits1P _ _ _ _ _ = undefined

{-

{-@ amortizedAddDigits1P:: m1:FingerTree (Node (Node a)) -> sf1:Digit (Node a) -> n:Node a -> pr2:Digit (Node a) -> { m2:FingerTree (Node (Node a)) | size m1 <= size m2 } -> { x:Nat | x <= 4 } -> { pow2 (addDigits1T m1 sf1 n pr2 m2 + phi (addDigits1 m1 sf1 n pr2 m2) - phi m2 + x) <= 100 * (size m1 + 1) } @-}
amortizedAddDigits1P :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> Int -> Proof
amortizedAddDigits1P m1 (One a) b (One c) m2 x =
  pow2 (addDigits1T m1 (One a) b (One c) m2 + phi (addDigits1 m1 (One a) b (One c) m2) - phi m2 + x)
    === pow2 (1 + appendTree1T m1 (Node3 a b c) m2 + phi (appendTree1 m1 (Node3 a b c) m2) - phi m2 + x)
    === undefined
    *** QED
amortizedAddDigits1P _ _ _ _ _ _ = undefined

-}

{-
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
-}
