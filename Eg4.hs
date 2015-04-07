{-# LANGUAGE TemplateHaskell #-}
-- Correlations
import TH

type Date = Int
type Value = Int

main :: IO ()
main 
 = do pull_corr1 <- pull_file "egs/eg_corr1.txt"
      pull_corr2 <- pull_file "egs/eg_corr2.txt"
      $$(comb [||let c1     = Read pull_corr1
                     c1'    = Map  read_corr c1
                     c2     = Read pull_corr2
                     c2'    = Map  read_corr c2

                     c1''   = Filter in_range c1'
                     c2''   = Filter in_range c2'

                     cs     = Merge c1'' c2''

                     cs'    = Map add_count cs

                     ds     = GroupBy sums  cs'

                     gs     = Filter multiple_entries ds
                     vals   = Map get_result gs

                     _      = When vals show_corr
                 in () ||])
 where
  read_corr :: String -> (Date,Value)
  read_corr = read

  in_range :: (Date,Value) -> Bool
  in_range (d,_)
   = d >= 20140200 && d < 20140300

  add_count :: (Date,Value) -> (Date,(Value,Int))
  add_count (d,v) = (d,(v,1))

  sums :: (Value,Int) -> (Value,Int) -> (Value,Int)
  sums (a,b) (c,d) = (a+c, b+d)

  multiple_entries :: (Date,(Value,Int)) -> Bool
  multiple_entries (d,(v,c)) = c > 1

  get_result :: (Date,(Value,Int)) -> (Date,Value)
  get_result (d,(v,c))
   = (d, v `div` c)


  show_corr = print

