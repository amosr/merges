{-# LANGUAGE TemplateHaskell #-}
import TH

main :: IO ()
main 
 = do pull_xs       <- pull_file "egs/zip1.txt"
      $$(comb [||let xs     = Map readI (Read pull_xs)

                     xs'    = Filter (>0) xs
                     xs''   = Filter (<0) xs
                     zz     = Zip xs' xs''

                     _      = When zz out
                 in () ||])
 where
  readI :: String -> Int
  readI = read

  out :: (Int,Int) -> IO ()
  out = print

