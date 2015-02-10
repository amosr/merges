{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes, StandaloneDeriving, ScopedTypeVariables #-}
module Automata4Prog where
import Automata4
import Automata4Coms
import Data.List (permutations)

data In = In
data a := b = a := b

data Program name where
 Let1 :: (Show s, Ord s) => name := (name -> name -> Machine s name) -> name -> In -> Program name -> Program name

 Let2 :: (Show s, Ord s) => name := (name -> name -> name -> Machine s name) -> name -> name -> In -> Program name -> Program name

 Read :: name -> In -> Program name -> Program name
 Return :: Program name

data Machine' n
 = forall s. (Show s, Ord s) => Machine' (Machine s n)

instance Show n => Show (Machine' n) where
 show (Machine' m) = ppr_machine m

machines :: forall name. Program name -> [Machine' name]
machines p
 = go p
 where
  go (Let1 (n := m) n1 In p')
   = Machine' (m n1 n) : go p'
  go (Let2 (n := m) n1 n2 In p')
   = Machine' (m n1 n2 n) : go p'
  -- actually, don't need to do anything?
  go (Read n In p') = go p'
  go Return = []

compile :: forall name. (Ord name, Show name) => Program name -> Maybe (Machine' name)
compile p_
 = fuse_all (machines p_)

fuse_all :: forall name. (Ord name, Show name) => [Machine' name] -> Maybe (Machine' name)
fuse_all ms
 = first_just
 $ map go
 $ permutations ms
 where
  go []
   = Nothing
  go [m]
   = Just m
  go (Machine' a : ms)
   = case go ms of
      Just (Machine' b)
       -> case fuse a b of
           Left _ -> Nothing
           Right m' -> Just (Machine' m')
      Nothing
       -> Nothing
   
  first_just []
   = Nothing
  first_just (Just n : _)
   = Just n
  first_just (_ : rs)
   = first_just rs

  -- fuse' :: forall s1 s2. (Show s1, Ord s1, Show s2, Ord s2) => Machine s1 name -> Machine s2 name -> Program name -> Maybe (Machine' name)
  -- fuse' m1 m2 p
  --  = case fuse m1 m2 of
  --      Left _ -> Nothing
  --      Right m' -> go p (Machine' m')

eg :: Program Names
eg
 = Read A In $
   Read B In $
   Let1 (U := filter_a ">5") A In $
   Let1 (V := map_a "+1")    B In $
   Let2 (Z := zip_a)       U V In $
   Return

eg2 :: Program Names
eg2
 = Read A In $
   Let1 (B := filter_a ">5") A In $
   Return
