{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes #-}
module KahnStream where

import Stream
import Kahn1Out
import Lists

-- | Process of a given single-input stream
pStream :: Stream a b s -> Process s '[a] b
pStream stream
 = Process (_init stream) fun_start
 where
  fun_start
   = \s    -> Get s Here         $
     \a s  -> fun_with a s

  fun_with a s
   = case _emit stream a s of
      Yield b s' fwd
       -> Put s' b (move_on a fwd)
      Skip    s' fwd
       -> move_on a fwd s'
      Stream.Done
       -> Kahn1Out.Done

  move_on a fwd s
   = case fwd of
      Forward
       -> Get s Here $ \a' s' -> fun_with a' s'
      Stay
       ->                        fun_with a  s


