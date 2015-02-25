{-# LANGUAGE TemplateHaskell #-}
import TH

main :: IO ()
main 
 = do pull_xs       <- pull_file "egs/zip1.txt"
      pull_ys       <- pull_file "egs/zip1.txt"
      $$(comb [||let xs     = Map readI (Read pull_xs)
                     ys     = Map readI (Read pull_ys)
                     
                     xs'    = Filter (>0) xs
                     ys'    = Filter (<0) ys
                     zz     = Zip xs' ys'

                     _      = When zz out
                 in () ||])
 where
  readI :: String -> Int
  readI = read

  out :: (Int,Int) -> IO ()
  out = print


