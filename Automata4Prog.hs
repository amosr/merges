{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes, StandaloneDeriving, ScopedTypeVariables #-}
module Automata4Prog where
import Automata4
import Automata4V
import Automata4Coms
import Data.List (permutations)

import qualified Data.Set as S


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

compile :: forall name. (Ord name, Show name) => Program name -> Either String (Machine' name)
compile p_
 = fuse_all (machines p_)

fuse_all :: forall name. (Ord name, Show name) => [Machine' name] -> Either String (Machine' name)
fuse_all ms
 = first_just
 $ map go
 -- $ permutations
 [ ms ]
 where
  go []
   = Left "No machines"
  go [m]
   = Right m
  go (Machine' a : ms)
   = case go ms of
      Right (Machine' b)
       | (_,oa) <- freevars a
       , S.size oa == 1
       , Just (oa', _) <- S.minView oa
       , oa' `S.member` fst (freevars b)
       -> case fuseV b a of
           Left r -> Left (show r)
           Right m' -> Right $ Machine' $ minimise m'
       | (_,ob) <- freevars b
       , S.size ob == 1
       , Just (ob', _) <- S.minView ob
       , ob' `S.member` fst (freevars a)
       -> case fuseV a b of
           Left r -> Left (show r)
           Right m' -> Right $ Machine' $ minimise m'
       | otherwise
       -> case fuse a b of
           Left r -> Left (show r)
           Right m' -> Right $ Machine' $ minimise m'
      Left err
       -> Left err
   
  first_just []
   = Left "none"
  first_just [x]
   = x
  first_just (Right n : _)
   = Right n
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
