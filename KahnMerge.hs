{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes #-}
module KahnMerge where

import Merge
import Kahn1Out
import Lists

-- | Process of a given two-input stream weaver
pMerge :: Merge a b c s -> Process s '[a, b] c
pMerge m
 = Process (_init m) fun_start
 where
  fun_start
   = \s    -> Get s Here         $
     \a s  -> Get s (There Here) $
     \b s  -> fun_with a b s

  fun_with a b s
   = case (a,b) of
      (Just a', Just b')
       | (val,s') <- _emit m a' b' s
       -> put_maybe s' val (move_on (_move m a' b' s') a b)
      (Just a', Nothing)
       | (val,s') <- _remainL m a' s
       -> put_maybe s' val (move_on L a b)
      (Nothing, Just b')
       | (val,s') <- _remainR m b' s
       -> put_maybe s' val (move_on R a b)

      -- Finished
      _
       -> put_maybe s (_finish m s) (\s -> Done)


  put_maybe s' val rest
   = case val of
      Nothing
       -> rest s'
      Just v'
       -> Put s' v' rest

  move_on mov a b s
   = case mov of
      L  -> Get s Here         $ \a' s' -> fun_with a' b s'
      R  -> Get s (There Here) $ \b' s' -> fun_with a b' s'
      LR ->            Get s Here $
             \a' s  -> Get s (There Here) $
             \b' s' -> fun_with a' b' s'


