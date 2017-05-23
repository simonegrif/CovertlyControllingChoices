module MyBasics where

import Data.List

infix 1 -->
(-->) :: Bool -> Bool -> Bool
x --> y = not x || y

assert :: (a -> b -> Bool) -> (a -> b -> String) -> (a -> b) -> a -> b
assert p warning f x = let y = f x in
  if p x y then y else error (warning x y)

bin2int :: [Bool] -> Int
bin2int = bin . reverse where
  bin []  = 0
  bin [False] = 0
  bin [True] = 1
  bin (False:bs) = 2 * bin bs
  bin (True:bs) = 2 * bin bs + 1

int2bin :: Int -> [Bool]
int2bin j = reverse (int2bin' j) where
  int2bin' 0 = []
  int2bin' 1 = [True]
  int2bin' n = odd n : int2bin' (div n 2)

groupOrder :: (a -> a -> Ordering) -> [a] ->
              ([a] -> [a] -> Ordering, [[a]])
groupOrder f xs = let
  g a b = f a b == EQ
  grouped = groupBy g (sortBy f xs)
  h ys1 ys2 = f (head ys1) (head ys2)
  in (h, grouped)

minimaBy :: (a -> a -> Ordering) -> [a] -> [a]
minimaBy f xs = let
    (h, grouped) = groupOrder f xs
  in minimumBy h grouped

maximaBy :: (a -> a -> Ordering) -> [a] -> [a]
maximaBy f xs = let
    (h, grouped) = groupOrder f xs
  in maximumBy h grouped

get :: String -> IO String
get str = do putStr str
             getLine
