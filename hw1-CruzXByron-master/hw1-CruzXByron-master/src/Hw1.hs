{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{- | CSE 116: Intro to Haskell Assignment.
     Do not change the skeleton code!

     You may only replace the `error "TBD:..."` parts.

     For this assignment, you may use any library function on integers
     but only the following library functions on lists:

     length
     (++)
     (==)

 -}

module Hw1 where

import Prelude  hiding (replicate, sum, reverse)


-- | Sum the elements of a list
--
-- >>> sumList [1, 2, 3, 4]
-- WAS 10
-- NOW TBD:sumList
-- NOW TBD:sumList
-- NOW TBD:sumList
-- WAS 7
-- NOW TBD:sumList
-- WAS 7
-- NOW TBD:sumList
-- WAS 36
-- NOW TBD:sumList
-- NOW TBD:sumList
-- WAS 36
-- NOW TBD:sumList
-- >>> sumList [1, 3, 5, 7, 9, 11]
-- WAS 36
-- NOW TBD:sumList

sumList :: [Int] -> Int
sumList [] = 0                           -- empty list, leave sum at 0
sumList xs = head xs + sumList (tail xs) -- non empty, add head, recur tail

-- | `digitsOfInt n` should return `[]` if `n` is not positive,
--    and otherwise returns the list of digits of `n` in the
--    order in which they appear in `n`.
--
-- >>> digitsOfInt 3124
-- [3, 1, 2, 4]
--
-- >>> digitsOfInt 352663
-- [3, 5, 2, 6, 6, 3]

--MUST ALWAYS ENCLOSE NEGATIVE NUMBERS IN PARENTHESES
digitsOfInt :: Int -> [Int]
digitsOfInt n
        | n <= 0 = []
        | otherwise = digitsOfInt (n `div` 10) ++ [n `mod` 10]

-- | `digits n` returns the list of digits of `n`
--
-- >>> digits 31243
-- [3,1,2,4,3]
--
-- digits (-23422)
-- [2, 3, 4, 2, 2]

digits :: Int -> [Int]
digits n = digitsOfInt (abs n)

-- | From http://mathworld.wolfram.com/AdditivePersistence.html
--   Consider the process of taking a number, adding its digits,
--   then adding the digits of the number derived from it, etc.,
--   until the remaining number has only one digit.
--   The number of additions required to obtain a single digit
--   from a number n is called the additive persistence of n,
--   and the digit obtained is called the digital root of n.
--   For example, the sequence obtained from the starting number
--   9876 is 9876 -> 30 -> 3, so 9876 has
--   an additive persistence of 2 and
--   a digital root of 3.
--
-- NOTE: assume additivePersistence & digitalRoot are only called with positive numbers

-- >>> additivePersistence 9876
-- 2

-- >>> additivePersistence 99999
-- 2

-- OHH since we recur we dont need a counter, just add 1
-- for every value of sumList that is greater than 10
-- until we hit a recursion step that is less than it,
-- ending the recursion. we add up all previous recursion
-- steps (callback?)

additivePersistence :: Int -> Int
additivePersistence n 
                | n < 10 = 0
                | otherwise = 1 + additivePersistence (sumList (digitsOfInt n))

-- | digitalRoot n is the digit obtained at the end of the sequence
--   computing the additivePersistence

-- >>> digitalRoot 9876
-- 3

-- >>> digitalRoot 99999
-- 9

digitalRoot :: Int -> Int
digitalRoot n 
        | n >= 10 = digitalRoot (sumList (digitsOfInt n))
        | otherwise = n


-- | listReverse [x1,x2,...,xn] returns [xn,...,x2,x1]
--
-- >>> listReverse []
-- []
--
-- >>> listReverse [1,2,3,4]
-- [4,3,2,1]
--
-- >>> listReverse ["i", "want", "to", "ride", "my", "bicycle"]
-- ["bicycle", "my", "ride", "to", "want", "i"]

listReverse :: [a] -> [a]
listReverse xs 
        | null xs = []
        | otherwise = listReverse (tail xs) ++ [head xs]

-- | In Haskell, a `String` is a simply a list of `Char`, that is:
--
-- >>> ['h', 'a', 's', 'k', 'e', 'l', 'l']
-- "haskell"
--
-- >>> palindrome "malayalam"
-- True
--
-- >>> palindrome "myxomatosis"
-- False

palindrome :: String -> Bool
palindrome w 
        | w == listReverse w = True 
        | otherwise = False
