module Proofs.Snoc where

import Language.Haskell.Liquid.ProofCombinators (Proof, QED (..), (***), (===), (?))
import Seq

{-@ snocT :: FingerTree a -> a -> Nat @-}
{-@ reflect snocT @-}
snocT :: FingerTree a -> a -> Int
snocT EmptyT _ = 1
snocT (Single _) _ = 1
snocT (Deep _ _ One {}) _ = 1
snocT (Deep _ _ Two {}) _ = 1
snocT (Deep _ _ Three {}) _ = 1
snocT (Deep _ q (Four a b c _)) _ = 1 + snocT q (Node3 a b c)

{-@ amortizedSnocP :: q:FingerTree a -> x:a -> { snocT q x + phi (snocTree q x) - phi q <= 3 } @-}
amortizedSnocP :: FingerTree a -> a -> Proof
amortizedSnocP EmptyT x =
  snocT EmptyT x + phi (snocTree EmptyT x) - phi EmptyT
    === 1 + phi (Single x)
    *** QED
amortizedSnocP t@(Single a) x =
  snocT t x + phi (snocTree t x) - phi t
    === 1 + phi (Deep (One a) EmptyT (One x))
    === 1 + dang (One a) + phi EmptyT + dang (One x)
    *** QED
amortizedSnocP t@(Deep v q (One a)) x =
  snocT t x + phi (snocTree t x) - phi t
    === 1 + phi (Deep v q (Two a x)) - phi t
    === 1 + dang v + phi q + dang (Two a x) - dang v - phi q - dang (One a)
    *** QED
amortizedSnocP t@(Deep v q (Two a b)) x =
  snocT t x + phi (snocTree t x) - phi t
    === 1 + phi (Deep v q (Three a b x)) - phi t
    === 1 + dang v + phi q + dang (Three a b x) - dang v - phi q - dang (Two a b)
    *** QED
amortizedSnocP t@(Deep v q (Three a b c)) x =
  snocT t x + phi (snocTree t x) - phi t
    === 1 + phi (Deep v q (Four a b c x)) - phi t
    === 1 + dang v + phi q + dang (Four a b c x) - dang v - phi q - dang (Three a b c)
    *** QED
amortizedSnocP t@(Deep v q (Four a b c d)) x =
  snocT t x + phi (snocTree t x) - phi t
    === snocT t x + phi (Deep v (snocTree q (Node3 a b c)) (Two d x)) - phi t
    === 1 + snocT q (Node3 a b c) + dang v + phi (snocTree q (Node3 a b c)) + dang (Two d x) - dang v - phi q - dang (Four a b c d)
    === snocT q (Node3 a b c) + phi (snocTree q (Node3 a b c)) - phi q
    ? amortizedSnocP q (Node3 a b c)
    *** QED
