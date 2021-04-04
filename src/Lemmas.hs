module Lemmas where

import Language.Haskell.Liquid.ProofCombinators (Proof, QED (..), (***), (===))
import Seq

{-@ dangNodeToDigitP :: n:Node a -> { dang (nodeToDigit n) == 0 } @-}
dangNodeToDigitP :: Node a -> Proof
dangNodeToDigitP n@(Node2 a b) =
  dang (nodeToDigit n)
    === dang (Two a b)
    *** QED
dangNodeToDigitP n@(Node3 a b c) =
  dang (nodeToDigit n)
    === dang (Three a b c)
    *** QED

{-@ phiDigitToTreeP :: v:Digit a -> { phi (digitToTree' v) - dang v <= 2 } @-}
phiDigitToTreeP :: Digit a -> Proof
phiDigitToTreeP v@(Four a b c d) =
  phi (digitToTree' v) - dang v
    === phi (Deep (Two a b) EmptyT (Two c d)) - 1
    === dang (Two a b) + phi EmptyT + dang (Two c d) - 1
    === -1
    *** QED
phiDigitToTreeP v@(Three a b c) =
  phi (digitToTree' v) - dang v
    === phi (Deep (Two a b) EmptyT (One c))
    === dang (Two a b) + phi EmptyT + dang (One c)
    === 1
    *** QED
phiDigitToTreeP v@(Two a b) =
  phi (digitToTree' v) - dang v
    === phi (Deep (One a) EmptyT (One b))
    === dang (One a) + phi EmptyT + dang (One b)
    === 2
    *** QED
phiDigitToTreeP v@(One a) =
  phi (digitToTree' v) - dang v
    === phi (Single a) - 1
    === -1
    *** QED
