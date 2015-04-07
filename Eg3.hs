{-# LANGUAGE TemplateHaskell #-}
import TH

main :: IO ()
main 
 = do pull_accounts <- pull_file "egs/eg_accounts.txt"
      $$(comb [||let as     = Read pull_accounts
                     as'    = Map  id  as
                     as''   = Map  id  as'
                     all    = Map  id  as''
                 in () ||])
