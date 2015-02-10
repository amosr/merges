module Automata4QQParse  where
import Automata4
import Automata4Coms
import Automata4Prog

import Control.Applicative


data AStmt
 = SRead String String
 | SCom  (Machine' String)
 | SWhen String String

parse :: String -> Maybe [AStmt]
parse str
 = concat <$> mapM (parse1.words.uncomment) (lines str)
 where
  uncomment = takeWhile (/='#')

  parse1 [b,"=","read", inp]
   = Just [SRead b inp]
  parse1 (b:"=":com:args)
   = case (com,args) of
      ("zip", [l,r])
       -> Just [SCom (Machine' (zip_a l r b))]
      ("append", [l,r])
       -> Just [SCom (Machine' (append_a l r b))]
      ("map", [f,l])
       -> Just [SCom (Machine' (map_a f l b))]
      ("filter", [f,l])
       -> Just [SCom (Machine' (filter_a f l b))]
      ("merge", [l,r])
       -> Just [SCom (Machine' (merge_a l r b))]
      _
       -> Nothing
  parse1 ["when", b, fun]
   = Just [SWhen b fun]
  parse1 []
   = Just []
  parse1 _
   = Nothing

machinesOfParse :: [AStmt] -> [Machine' String]
machinesOfParse stmts
 = concatMap get stmts
 where
  get (SCom m)
   = [m]
  get _
   = []

