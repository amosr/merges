{-# LANGUAGE TemplateHaskell #-}
import TH

main :: IO ()
main 
 = do pull_accounts <- pull_file "egs/eg_accounts.txt"
      pull_loans    <- pull_file "egs/eg_loans.txt"
      $$(comb [||let as     = Read pull_accounts
                     ls     = Read pull_loans

                     -- parse the input records
                     as'    = Map read_account  as
                     ls'    = Map read_loan     ls
                     
                     -- inject input..
                     as''   = Map left          as'
                     ls''   = Map right         ls'

                     -- merge
                     all    = Merge as'' ls''

                     join   = GroupBy sum_account all

                     join'  = Filter both_just join
                     join'' = Map    get_just  join'

                     arrears= Filter ((<0).amount) join''
                     offers = Filter ((>5000).amount) join''

                     _  = When arrears send_arrears_email
                     _  = When offers  raise_credit_limit
                 in () ||])
 where
  send_arrears_email b = putStrLn  ("NAUGHTY BOY: " ++ show b) 
  raise_credit_limit b = putStrLn  ("my best friend: " ++ show b) 

  right (a,b) = (a, (Nothing, Just b))
  left  (a,b) = (a, (Just b, Nothing))

  sum_account (ln,ll) (rn,rr)
   = ( case (ln, rn) of
        (Just n, _) -> Just n
        (_, Just n) -> Just n
        (_, _)      -> Nothing
     , case (ll, rr) of
        (Just l, Just r) -> Just (l+r)
        (Just l, _)      -> Just l
        (_,      Just r) -> Just r
        (_, _)           -> Nothing
        )

  both_just (a,(Just _, Just _))
    = True
  both_just _
    = False

  get_just (a,(Just b, Just c))
   = (a, b, c)

  amount (a,b,c) = c

  read_account :: String -> (Int,String)
  read_account = read

  read_loan :: String -> (Int,Int)
  read_loan = read

