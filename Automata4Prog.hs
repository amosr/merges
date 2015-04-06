{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes, StandaloneDeriving, ScopedTypeVariables #-}
module Automata4Prog where
import Automata4
import Automata4Coms
import Automata4Merge
import Automata4Min
import Automata4V
import Data.List (permutations)

import qualified Data.Set as S


data Machine' n f
 = forall s. (Show s, Ord s) => Machine' (Machine s n f)

instance (Show n, Show f) => Show (Machine' n f) where
 show (Machine' m) = ppr_machine m

fuse_all :: forall name f. (Ord name, Show name, Show f, Eq f) => [Machine' name f] -> Either String (Machine' name f)
fuse_all ms
 = first_just
 $ map go
 -- $ permutations
 -- TODO: the thing left here is that we want to walk the dag, and only fuse "related things" to start with.
 -- there's no point fusing machines for "x = map c" and "y = map d" together
 -- because we don't know whether to compute Xs then Ys, or Ys then Xs, or both interleaved.
 -- so instead we would fuse those two vertical chains, then only once we see a machine
 -- that uses both, fuse them all together.
 [ ms ]
 where
  go []
   = Left "No machines"
  go [m]
   = Right m
  go (Machine' a : ms)
   = case go ms of
      Right (Machine' b)
       -- out of a is used by second machine, and the machines do not share inputs
       | (ia,oa) <- freevars a
       , (ib,ob) <- freevars b
       , S.size oa == 1
       , Just (outa, _) <- S.minView oa
       , outa `S.member` ib
       , S.null (ia `S.intersection` ib)
       -> case fuseV b a of
           Left r -> Left (show r)
           Right m' -> Right $ Machine' $ minimise m'

       | (ia,oa) <- freevars a
       , (ib,ob) <- freevars b
       , S.size ob == 1
       , Just (outb, _) <- S.minView ob
       , outb `S.member` ia
       , S.null (ia `S.intersection` ib)
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
