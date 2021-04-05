module Main where

import Language.Haskell.Liquid.ProofCombinators (Proof, QED (..), (***), (===), (?))
import Stack ()
import Prelude hiding (reverse)

{-@ append :: xs:[a] -> ys:[a] -> { zs:[a] | len zs == len xs + len ys } @-}
append :: [a] -> [a] -> [a]
append [] ys = ys
append (x : xs) ys = x : append xs ys

{-@ appendAssocP :: xs:[a] -> ys:[a] -> zs:[a] ->
      { append (append xs ys) zs == append xs (append ys zs) } @-}
appendAssocP :: [a] -> [a] -> [a] -> Proof
appendAssocP [] ys zs =
  append (append [] ys) zs
    === append ys zs
    === append [] (append ys zs)
    *** QED
appendAssocP (x : xs) ys zs =
  append (append (x : xs) ys) zs
    === append (x : append xs ys) zs
    === (x : append (append xs ys) zs)
    ? appendAssocP xs ys zs
    === (x : append xs (append ys zs))
    === append (x : xs) (append ys zs)
    *** QED

{-@ appendRightIdP :: xs:[a] -> { xs == append xs [] } @-}
appendRightIdP :: [a] -> Proof
appendRightIdP [] = append [] [] *** QED
appendRightIdP (x : xs) =
  (x : xs)
    ? appendRightIdP xs
    === (x : append xs [])
    === append (x : xs) []
    *** QED

{-@ reverse :: xs:[a] -> { ys:[a] | len xs == len ys } @-}
reverse :: [a] -> [a]
reverse [] = []
reverse (x : xs) = append (reverse xs) [x]

{-@ reflect append @-}
{-@ reflect reverse @-}

{-@ reverseApp :: xs:[a] -> ys:[a] -> { zs : [a] | zs == append (reverse xs) ys } @-}
reverseApp :: [a] -> [a] -> [a]
reverseApp [] ys =
  append (reverse []) ys
    === append [] ys
    === ys
reverseApp (x : xs) ys =
  append (reverse (x : xs)) ys
    === append (append (reverse xs) [x]) ys
    ? appendAssocP (reverse xs) [x] ys
    === append (reverse xs) (append [x] ys)
    === append (reverse xs) (x : append [] ys)
    === append (reverse xs) (x : ys)
    ? reverseApp xs (x : ys)
    === reverseApp xs (x : ys)

{-@ reverse' :: xs:[a] -> { ys:[a] | ys = reverse xs } @-}
reverse' :: [a] -> [a]
reverse' xs =
  reverse xs
    ? appendRightIdP (reverse xs)
    === append (reverse xs) []
    === reverseApp xs []

main :: IO ()
main = putStrLn $ reverse "Hello, world!"
