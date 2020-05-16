{-# LANGUAGE StandaloneDeriving #-}

module Main where

import Text.Read (readMaybe)
import System.IO
import Control.Monad (forM_)

import Out

deriving instance (Show Q)
deriving instance (Read Q)

q_to_double :: Q -> Double
q_to_double (Qmake x y) = (fromInteger $ toInteger x)/(fromInteger $ toInteger y)

max_rat :: Integer
max_rat = 3000

-- Q - {0}

get_pairs :: [(Double,Double)]
get_pairs = do
  i <- [0..(max_rat-1)]
  let (q_in,_) = nth_Qnz i
  let d_in = q_to_double q_in
  let q_out = qnz_to_Q (q_in,())
  let d_out = q_to_double q_out
  return (q_to_double q_in, q_to_double q_out)

print_pair :: (Double,Double) -> String
print_pair (f1,f2) = show f1 ++ ", " ++ show f2

-- print_pairs :: [(Double,Double)] -> String
-- print_pairs [] = ""
-- print_pairs (p:ps) = print_pair p ++ "\n" ++ print_pairs ps

--main :: IO()
--main = writeFile "data.out" $ print_pairs get_pairs

main :: IO ()
main = withFile "data.out" WriteMode $ \h ->
  forM_ get_pairs $ \t -> hPutStrLn h $ print_pair t

--  forM_ get_triples (print_tuple "data.out")



