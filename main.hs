{-# LANGUAGE StandaloneDeriving #-}

module Main where

import Text.Read (readMaybe)
import Out

deriving instance (Show Q)
deriving instance (Read Q)

q_to_float :: Q -> Double
q_to_float (Qmake x y) = (fromInteger $ toInteger x)/(fromInteger $ toInteger y)

{-
bound :: Int
bound = 2

div_mesh :: Int -> [(Float,Float)]
div_mesh n = do
    den <- [1..n]
    num <- [(-(bound*den))..(bound*den)]
    if num == 0 then [] else return (q_to_float $ Qmake num den , q_to_float $ qnz_to_Q $ Qmake num den)

mesh :: Int
mesh = 7
-}

max_rat :: Int
max_rat = 300

get_pairs :: [(Double,Double)]
get_pairs = do
    i <- [1..max_rat]
    let q_in = nat_to_Q i
    let f_in = q_to_float q_in
    if f_in > 1.0 || f_in < -1.0 then [] else do
        let q_out = qnz_to_Q q_in
        let f_out = q_to_float q_out
        return (f_in, f_out)

print_pair :: (Double,Double) -> String
print_pair (f1,f2) = "" ++ show f1 ++ " , " ++ show f2 ++ ""

print_pairs :: [(Double,Double)] -> String
print_pairs [] = ""
print_pairs (p:ps) = print_pair p ++ "\n" ++ print_pairs ps

main :: IO()
main = writeFile "data.out" $ print_pairs get_pairs