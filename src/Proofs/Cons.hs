module Proofs.Cons where

import Language.Haskell.Liquid.ProofCombinators (Proof, QED (..), (***), (===), (?))
import Seq

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
    === 1 + phi (Single x)
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
