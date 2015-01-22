{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes #-}
module Kahn1Egs where
import Kahn1Out
import Lists

data Graph' i o
 = forall d. Graph' (Graph i d o)

rungy (Graph' g) ins
 = let (os,tr) = evalG g ins
   in  (vshow os, tr)

example_graph :: Graph' '[Int] '[Int]
example_graph
 = Graph' 
 $ Out Here
 $ Trans (ICons Here INil) odd_plus_1
 $ Inp
 $ Empty

g_self_zip :: Graph' '[Int] '[(Int,Int)]
g_self_zip
 = Graph'
 $ Out Here
 $ Trans (ICons Here (ICons Here INil)) proc_zip2
 $ Inp
 $ Empty

g_zip2 :: Graph' '[Int, Int] '[(Int,Int)]
g_zip2
 = Graph'
 $ Out Here
 $ Trans (ICons Here (ICons (There Here) INil)) proc_zip2
 $ Inp
 $ Inp
 $ Empty

g_app2 :: Graph' '[Int, Int] '[Int]
g_app2
 = Graph'
 $ Out Here
 $ Trans (ICons Here (ICons (There Here) INil)) proc_app2
 $ Inp
 $ Inp
 $ Empty

-- requires unbounded buffer
g_self_app2 :: Graph' '[Int] '[Int]
g_self_app2
 = Graph'
 $ Out Here
 $ Trans (ICons Here (ICons Here INil)) proc_app2
 $ Inp
 $ Empty




proc_zip2 :: Process () '[a,b] (a,b)
proc_zip2
 = Process () fun
 where
  fun
   = \_     -> Get () Here $
     \in1 _ -> case in1 of
                Nothing -> Done
                Just a' -> Get () (There Here) $
                 \in2 _ -> case in2 of
                            Nothing -> Done
                            Just b' -> Put () (a',b') fun

proc_app2 :: Process () '[a,a] a
proc_app2
 = Process () fun
 where
  fun
   = \_     -> Get () Here $
     \in1 _ -> case in1 of
                Nothing -> Get () (There Here) $
                 \in2 _ -> case in2 of
                            Nothing -> Done
                            Just r' -> Put () r' fun
                Just l' -> Put () l' fun



odd_plus_1 :: Process () '[Int] Int
odd_plus_1
 = Process () fun
 where
  fun :: () -> Step () '[Int] Int
  fun
   = \_     -> Get () Here $
     -- throw first get away
     \eve _ -> Get () Here $
     \odd _ -> case odd of
                Nothing -> Done
                Just o' -> Put () (o'+1) fun

run_odd_1 :: [Int] -> [Int]
run_odd_1 ins
 = let vs = VCons ins VNil
       os = eval1 odd_plus_1 vs
   in  os
