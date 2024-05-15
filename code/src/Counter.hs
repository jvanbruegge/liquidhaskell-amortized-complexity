{-@ LIQUID "--ple-local" @-}
module Counter where

import Language.Haskell.Liquid.ProofCombinators (Proof, QED (..), (***), (===), (?), trivial)

data Binary = B0 Binary | B1 Binary | BEnd

{-@ reflect inc @-}
inc :: Binary -> Binary
inc BEnd = B1 BEnd
inc (B0 rest) = B1 rest
inc (B1 rest) = B0 (inc rest)

-- Amortized analysis

{-@ reflect incT @-}
{-@ incT :: Binary -> { x:Int | x > 0 } @-}
incT :: Binary -> Int
incT BEnd = 1
incT (B0 _) = 1
incT (B1 rest) = 1 + incT rest

{-@ reflect pot @-}
{-@ pot :: Binary -> { x:Int | x >= 0 } @-}
pot :: Binary -> Int
pot BEnd = 0
pot (B0 rest) = pot rest
pot (B1 rest) = 1 + pot rest

{-@ automatic-instances incAmortized @-}
{-@ incAmortized :: b:Binary -> { incT b + pot (inc b) - pot b <= 2 } @-}
incAmortized :: Binary -> Proof
incAmortized b@(B1 rest) =
  incT b + pot (inc b) - pot b
  === 1 + incT rest + pot (B0 (inc rest)) - 1 - pot rest
  === incT rest + pot (inc rest) - pot rest
  ? incAmortized rest
  *** QED
incAmortized _ = trivial
