{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Main where
import Automata4QQ
import Data.IORef
import qualified Data.Vector as V

read_account :: String -> (Int,String)
read_account = read

read_loan :: String -> (Int,Int)
read_loan = read

pull_file :: String -> IO (IO (Maybe String))
pull_file nm
 = do   file <- readFile nm
        ls' <- newIORef (lines file)
        let pull
             = do   i <- readIORef ls'
                    case i of
                     [] -> return Nothing
                     (i:is)
                        -> writeIORef ls' is >> return (Just i)
        return pull

go :: IO ()
go
 = do   pull_accounts  <- pull_file "eg_accounts.txt"
        pull_loans     <- pull_file "eg_loans.txt"
        [auto|
            as = read pull_accounts
            -- read loans (both sorted by account id)
            ls = read pull_loans

            -- parse the input records
            as'  = map read_account as
            ls'  = map read_loan    ls

            -- inject the input records into a common type so we can merge them
            as'' = map left         as'
            ls'' = map right        ls'

            -- merge the accounts and loans together
            -- so all of same account id are consecutive
            all = merge as'' ls''

            -- group consecutive loans and accounts of same id
            -- summing up loan amounts etc
            join = group_by sum_account all

            -- filter out any with no accounts or no loans
            join' = filter both_just join
            join'' = map get_just join'

            -- filter into two groups depending on loan value
            arrears = filter in_arrears join''
            offers  = filter offer_loan join''

            -- send emails
            when arrears send_arrears_email
            when offers  send_loan_offer
            |]
 where
  send_arrears_email b = putStrLn  ("NAUGHTY BOY: " ++ show b) 
  send_loan_offer    b = putStrLn  ("my best friend: " ++ show b) 

  right (a,b) = (a, (Nothing, Just b))
  left  (a,b) = (a, (Just b, Nothing))

  sum_account (a,(ln,ll)) (_,(rn,rr))
   = (a,
     ( case (ln, rn) of
        (Just n, _) -> Just n
        (_, Just n) -> Just n
        (_, _)      -> Nothing
     , case (ll, rr) of
        (Just l, Just r) -> Just (l+r)
        (Just l, _)      -> Just l
        (_,      Just r) -> Just r
        (_, _)           -> Nothing
        ))

  both_just (a,(Just _, Just _))
    = True
  both_just _
    = False

  get_just (a,(Just b, Just c))
   = (a, b, c)

  in_arrears (a,b,c)
   = c < (-100)
  offer_loan (a,b,c)
   = c > 100 && c < 5000


main = go

