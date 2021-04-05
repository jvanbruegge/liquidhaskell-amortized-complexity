module Proofs.Tails where

import Language.Haskell.Liquid.ProofCombinators (Proof, QED (..), (***), (===), (?))
import Lemmas
import Seq

-- This is equivalent to the case expression in pullL, but saves me a lot of typing
-- If this would not be equivalent, LiquidHaskell would complain, so it is fine to use this
{-@ reflect pullL' @-}
pullL' :: ViewLTree (Node a) -> Digit a -> FingerTree a
pullL' EmptyLTree sf = digitToTree' sf
pullL' (ConsLTree pr m') sf = Deep (nodeToDigit pr) m' sf

{-@ tailT :: FingerTree a -> Nat @-}
{-@ reflect tailT @-}
tailT :: FingerTree a -> Int
tailT (Deep (One _) m _) = 1 + tailT m
tailT _ = 1

{-@ amortizedTailP :: t:FingerTree a -> { tailT t + phiView (viewLTree t) - phi t <= 3 } @-}
amortizedTailP :: FingerTree a -> Proof
amortizedTailP EmptyT =
  tailT EmptyT + phiView (viewLTree EmptyT) - phi EmptyT
    === 1 + phiView EmptyLTree
    === 1
    *** QED
amortizedTailP (Single x) =
  tailT (Single x) + phiView (viewLTree (Single x)) - phi (Single x)
    === 1 + phiView (ConsLTree x EmptyT)
    === 1 + phi EmptyT
    === 1
    *** QED
amortizedTailP t@(Deep (Four a b c d) m v) =
  tailT t + phiView (viewLTree t) - phi t
    === 1 + phiView (ConsLTree a t2) - phi t
    === 1 + phi t2 - dang (Four a b c d) - phi m - dang v
    === dang (Three b c d) + phi m + dang v - phi m - dang v
    *** QED
  where
    t2 = Deep (Three b c d) m v
amortizedTailP t@(Deep (Three a b c) m v) =
  tailT t + phiView (viewLTree t) - phi t
    === 1 + phiView (ConsLTree a t2) - phi t
    === 1 + phi t2 - dang (Three a b c) - phi m - dang v
    === 1 + dang (Two b c) + phi m + dang v - phi m - dang v
    *** QED
  where
    t2 = Deep (Two b c) m v
amortizedTailP t@(Deep (Two a b) m v) =
  tailT t + phiView (viewLTree t) - phi t
    === 1 + phiView (ConsLTree a t2) - phi t
    === 1 + phi t2 - dang (Two a b) - phi m - dang v
    === 1 + dang (One b) + phi m + dang v - phi m - dang v
    *** QED
  where
    t2 = Deep (One b) m v
amortizedTailP t@(Deep (One a) t2 v) =
  tailT t + phiView (viewLTree t) - phi t
    === tailT t + phiView (ConsLTree a (pullL t2 v)) - phi t
    === tailT t + phi (pullL t2 v) - phi t
    === tailT t + phi (pullL' (viewLTree t2) v) - phi t
    === 1 + tailT t2 + phi (pullL' (viewLTree t2) v) - dang (One a) - phi t2 - dang v
    === tailT t2 + phi (pullL' (viewLTree t2) v) - phi t2 - dang v
    ? amortizedTailAuxP t2 v
    *** QED

{-@ amortizedTailAuxP :: t:FingerTree (Node a) -> v:Digit a -> { tailT t + phi (pullL' (viewLTree t) v) - dang v - phi t <= 3 } @-}
amortizedTailAuxP :: FingerTree (Node a) -> Digit a -> Proof
amortizedTailAuxP t@EmptyT v =
  tailT t + phi (pullL' (viewLTree t) v) - phi t - dang v
    === 1 + phi (pullL' EmptyLTree v) - dang v
    === 1 + phi (digitToTree' v) - dang v
    ? phiDigitToTreeP v
    *** QED
amortizedTailAuxP t@(Single a) v =
  tailT t + phi (pullL' (viewLTree t) v) - phi t - dang v
    === 1 + phi (pullL' (ConsLTree a EmptyT) v) - phi t - dang v
    === 1 + phi (Deep (nodeToDigit a) EmptyT v) - dang v
    === 1 + dang (nodeToDigit a) + phi EmptyT + dang v - dang v
    ? dangNodeToDigitP a
    *** QED
amortizedTailAuxP t@(Deep (Four a b c d) m sf) v =
  tailT t + phi (pullL' (viewLTree t) v) - phi t - dang v
    === 1 + phi (pullL' (ConsLTree a t2) v) - dang (Four a b c d) - phi m - dang sf - dang v
    === undefined
    === phi (Deep (nodeToDigit a) t2 v) - phi m - dang sf - dang v
    === dang (nodeToDigit a) + phi t2 + dang v - phi m - dang sf - dang v
    ? dangNodeToDigitP a
    === dang (Three b c d) + phi m + dang sf - phi m - dang sf
    *** QED
  where
    t2 = Deep (Three b c d) m sf
amortizedTailAuxP t@(Deep (Three a b c) m sf) v =
  tailT t + phi (pullL' (viewLTree t) v) - phi t - dang v
    === 1 + phi (pullL' (ConsLTree a t2) v) - phi t - dang v
    === 1 + phi (Deep (nodeToDigit a) t2 v) - phi t - dang v
    === 1 + dang (nodeToDigit a) + phi t2 + dang v - dang (Three a b c) - phi m - dang sf - dang v
    ? dangNodeToDigitP a
    === 1 + dang (Two b c) + phi m + dang sf - phi m - dang sf
    *** QED
  where
    t2 = Deep (Two b c) m sf
amortizedTailAuxP t@(Deep (Two a b) m sf) v =
  tailT t + phi (pullL' (viewLTree t) v) - phi t - dang v
    === 1 + phi (pullL' (ConsLTree a t2) v) - phi t - dang v
    === 1 + phi (Deep (nodeToDigit a) t2 v) - phi t - dang v
    === 1 + dang (nodeToDigit a) + phi t2 + dang v - dang (Two a b) - phi m - dang sf - dang v
    ? dangNodeToDigitP a
    === 1 + dang (One b) + phi m + dang sf - phi m - dang sf
    *** QED
  where
    t2 = Deep (One b) m sf
amortizedTailAuxP t@(Deep (One a) m sf) v =
  tailT t + phi (pullL' (viewLTree t) v) - phi t - dang v
    === tailT t + phi (pullL' (ConsLTree a (pullL m sf)) v) - phi t - dang v
    === tailT t + phi (Deep (nodeToDigit a) (pullL m sf) v) - phi t - dang v
    === tailT t + dang (nodeToDigit a) + phi (pullL m sf) - phi t
    ? dangNodeToDigitP a -- apply: dang (nodeToDigit _) is always 0
    === tailT t + phi (pullL' (viewLTree m) sf) - dang (One a) - phi m - dang sf
    === tailT m + phi (pullL' (viewLTree m) sf) - phi m - dang sf
    ? amortizedTailAuxP m sf -- apply: induction hypothesis
    *** QED
