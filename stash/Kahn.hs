-- Kahn process networks
{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes #-}

module Kahn where
import Lists


data Step s is os
 = forall i. Get s (Index is i)    (Maybe i -> s -> Step s is os)
 | forall o. Put s (Index os o) o             (s -> Step s is os)
 | Done

data Process s is os
 = Process s (s -> Step s is os)


eval1 :: VNils os => Process s is os -> Values is -> Values os
eval1 (Process s_ f_) vs_
 = go s_ f_ vs_ vnils
 where
  go s f ins outs
   = case f s of
      Get s' ix   f'
       -> let (v,ins') = takedrop1 ix ins
          in  go s' (f' v) ins' outs
      Put s' ox o f'
       -> let outs'    = push1 ox o outs
          in  go s' f' ins outs'
      Done
       -> outs

odd_plus_1 :: Process () '[Int] '[Int]
odd_plus_1
 = Process () fun
 where
  fun :: () -> Step () '[Int] '[Int]
  fun
   = \_     -> Get () Here $
     -- throw first get away
     \eve _ -> Get () Here $
     \odd _ -> case odd of
                Nothing -> Done
                Just o' -> Put () Here (o'+1) fun

run_odd_1 :: [Int] -> [Int]
run_odd_1 ins
 = let vs = VCons ins VNil
       os = eval1 odd_plus_1 vs
   in case os of
        VCons o _ -> o


