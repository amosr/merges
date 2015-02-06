{-# LANGUAGE ScopedTypeVariables #-}
module Automata where
import Data.Maybe    (mapMaybe)
import Data.List     (nub, sort, groupBy)
import Data.Function (on)

data Machine s n
 = Machine
  { _states :: [(s, State s n)]
  , _init   :: s }
 deriving Show

data State s n
 = State [(n, s)]
 deriving Show

trace :: (Eq n, Eq s) => Machine s n -> [n] -> Maybe [s]
trace m ws
 = go (_init m) ws
 where
  go s []
   = Just []
  go s (w:ws)
   | Just (State sf)
                <- lookup s $ _states m
   , Just s'    <- lookup w sf 
   , Just t'    <- go s' ws
   = Just (s : t')
   | otherwise
   = Nothing

zip_a :: n -> n -> n -> Machine Int n 
zip_a a b e
 = Machine
 { _init   = 0
 , _states =
    [ (0, State [(a, 1)])
    , (1, State [(b, 2)])
    , (2, State [(e, 0)])
    ]
 }

append_a :: n -> n -> n -> Machine Int n 
append_a a b e
 = Machine
 { _init   = 0
 , _states =
    [ (0, State [(a, 1), (b, 3)])
    , (1, State [(e, 0)])
    , (2, State [(b, 3)])
    , (3, State [(e, 2)])
    ]
 }


-- | We have two machines m1 and m2 with states s1 and s2,
-- and we want to execute m1 as normal, until a particular letter 'n' shows up.
-- When an 'n' shows up, we want to execute m2 from where we last left off, until it also has an 'n'.
data Subst s1 s2
 -- | The state of m1, with the set of states in m2 we must start from next time
 = S1 s1 [s2]
 -- | We are executing m2 at this state, and will return to m1 after an 'n' is reached.
 | S2 s1 [s2]
 deriving (Eq,Ord, Show)

subst2 :: forall n s1 s2. (Eq n, Ord s1, Ord s2)
       => Machine s1 n -> n -> Machine s2 n -> Machine (Subst s1 s2) n
subst2 m1 n m2
 = Machine
 { _init   = init
 , _states = go init []
 }
 where
  -- Start at the initial states of both machines
  init = S1  (_init m1) [_init m2] 

  -- For given state, generate the transitions, and if they don't already have states, create them
  go :: Subst s1 s2 -> [(Subst s1 s2, State (Subst s1 s2) n)] -> [(Subst s1 s2, State (Subst s1 s2) n)]
  go s states
   -- Given state already created
   | Just _ <- lookup s states
   = states

   -- Executing machine 1
   | S1 s1 s2s <- s
   -- Get machine 1's transitions for this state
   , Just (State ts) <- lookup s1 (_states m1)
     -- Check transitions against 'n'
   = let ts' = concatMap (trans1 s2s) ts
         -- Add this state, with given transitions
         states' = (s, State ts') : states
         -- For each transition, add its state
     in  foldr go states' (map snd ts')

   -- Executing machine 2 in set of states s2s
   | S2 s1 s2s <- s
         -- Find all transitions from set of s2s
   = let ts' = trans2 s2s s1
         -- Add this state
         states' = (S2 s1 s2s, State ts') : states
         -- Add the transitions as states
     in  foldr go states' (map snd ts')

  -- For a machine 1 transition,
  -- check whether to stay on machine 1 or move to machine 2
  trans1 :: [s2] -> (n,s1) -> [(n, Subst s1 s2)]
  trans1 s2s (n',s1)
   -- Move to machine 2
   | n == n'
   = trans2 s2s s1
   -- Stay on machine 1
   | otherwise
   = [(n', S1 s1 s2s)]

  trans2 :: [s2] -> s1 -> [(n, Subst s1 s2)]
  trans2 s2s s1
     -- Get all machine 2's states in s2s
   = let ss = mapMaybe (flip lookup (_states m2)) s2s
     -- Find all the transitions, and group them by the letter
         ts = groupBy ((==) `on` fst)
            $ concatMap (\(State t) -> t) ss
     -- For each transition:
     --   if it is letter 'n', we go back to machine 1, at state s1
     --   otherwise, we keep evaluating machine 2 on this set of states
         ts'= map (goBack s1) ts
     in  ts'

  -- Go back to machine 1 if letter is 'n'
  goBack :: s1 -> [(n, s2)] -> (n, Subst s1 s2)
  goBack s1 ns2s@((n',_):_) -- groupBy won't create an empty list
   | n == n'
   = (n', S1 s1 (nub $ sort $ map snd ns2s))
   | otherwise
   = (n', S2 s1 (nub $ sort $ map snd ns2s))

{-

*Automata> subst2 (zip_a "app" "c" "zip") "app" (append_a "a" "b" "app")
Machine {_states =
[(S1 2 [0],State [("zip",S1 0 [0])])
,(S1 1 [0],State [("c",S1 2 [0])])
,(S2 1 [1],State [("app",S1 1 [0])])
,(S1 0 [2],State [("b",S2 1 [3])])
,(S1 2 [2],State [("zip",S1 0 [2])])
,(S1 1 [2],State [("c",S1 2 [2])])
,(S2 1 [3],State [("app",S1 1 [2])])
,(S1 0 [0],State [("a",S2 1 [1]),("b",S2 1 [3])])

]
, _init = S1 0 [0]}

-}
