{-# LANGUAGE TemplateHaskell #-}
-- two-way correlation with three inputs
import TH

type Date = Int
type Value = Int
type Row = (Date, (Value, Int))

main :: IO ()
main 
 = do pull_corr1 <- pull_file "egs/eg_corr1.txt"
      pull_corr2 <- pull_file "egs/eg_corr2.txt"
      pull_corr3 <- pull_file "egs/eg_corr1.txt"
      $$(comb [||let c1     = Read pull_corr1
                     c2     = Read pull_corr2
                     c3     = Read pull_corr3

                     c1'    = Map  read_corr c1
                     c2'    = Map  read_corr c2
                     c3'    = Map  read_corr c3

                     cs1    = Merge c1' c2'
                     cs1'   = Filter in_range cs1

                     cs2    = Merge c2' c3'
                     cs2'   = Filter in_range cs2

                     ds1    = GroupBy sums  cs1'
                     gs1    = Filter multiple_entries ds1
                     vals1   = Map get_result gs1

                     ds2    = GroupBy sums  cs2'
                     gs2    = Filter multiple_entries ds2
                     vals2   = Map get_result gs2

                     _      = When vals1 (show_corr 1)
                     _      = When vals2 (show_corr 2)
                 in () ||])
 where
  read_corr :: String -> Row
  read_corr s
   | (d,v) <- read s
   = (d,(v,1))

  in_range :: Row -> Bool
  in_range (d,_)
   = d >= 20140200 && d < 20140300

  sums :: (Value,Int) -> (Value,Int) -> (Value,Int)
  sums (a,b) (c,d) = (a+c, b+d)

  multiple_entries :: Row -> Bool
  multiple_entries (d,(v,c)) = c > 1

  get_result :: Row -> (Date,Value)
  get_result (d,(v,c))
   = (d, v `div` c)


  show_corr i x = print (i,x)

