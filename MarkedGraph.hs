-- Marked graphs: a subset of Petri nets.
-- Every place has exactly one input transition and one output transition, so no parallel arcs.
-- I guess a transition can have multiple output places though.
-- For a given place, only one output transition exists, so if the place is full there is only one choice of what to execute.
-- Marked graphs are much easier to analyse than general Petri nets: deadlocks cannot occur on cycles with at least one token going through them.
-- http://en.wikipedia.org/wiki/Marked_graph
{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes #-}

module MarkedGraph where

data Transition a b
 = Transition (a -> b)

data Place a
 = Place
    (PlaceName a) -- ^ Unique id
    [a]           -- ^ Values

data PlaceName a
 = PlaceName Int String
 deriving (Eq,Ord,Show)

data Index :: [*] -> * -> * where
  Here :: Index (x ': xs) x
  There :: Index xs x -> Index (y ': xs) x

data MarkedGraph :: [*] -> [*] -> [*] -> * where
  Empty :: MarkedGraph '[] '[] '[]
  Inp   :: MarkedGraph i d o -> MarkedGraph (a ': i) (a ': d) o
  Out   :: Index d x -> MarkedGraph i d o -> MarkedGraph i d (x ': o)

  Trans :: Index d x -> Transition a b -> MarkedGraph i d o -> MarkedGraph i (x ': d) o

  -- For creating cycles
  BackEdge :: Index d a -> Index d a -> MarkedGraph i d o

