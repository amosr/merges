-- Special case for vertical fusion
module Automata4V where
import Automata4

import qualified Data.Set as S
import qualified Data.Map as M

import Data.Monoid

data M'V = M'1 | M'2
 deriving (Eq,Ord,Show)
-- | The resulting label type of fusing two machines vertically.
data L'V l1 l2
 -- | Cross product of the two labels, and which machine is executing (1 or 2)
 = L'V l1 l2 M'V
 deriving (Eq,Ord,Show)

-- | Fuse two machines together vertically.
-- Machine 2 can only have one output.
-- Machine 1 and machine 2 cannot share inputs.
-- Machine 1 must read from machine 2's sole output.
--
-- If these preconditions do not hold, this function will produce an incorrect machine; use general fuse instead.
-- If these conditions hold, we can use a simpler, specialised fusion algorithm.
-- Basically, we start by executing M1, and whenever M2's output is read, we swap to M2 until an output is made, then swapping back to M1.
-- Sometimes the general one can get confused and generate too many states.
fuseV :: (Ord l1, Ord l2, Ord name) => Machine l1 name f -> Machine l2 name f -> Either (MergeError l1 l2 name f) (Machine (L'V l1 l2) name f)
fuseV m1 m2
 = do   trans <- go init M.empty
        return Machine
         { _init = init
         , _trans = trans
         }
 where
  init = L'V (_init m1) (_init m2) M'1

  -- Compute the transition for new state l, adding it to the map.
  -- go :: (L' l1 l2 name) -> M.Map (L' l1 l2 name) (Transition (L' l1 l2 name) name) -> Either (MergeError l1 l2 name) (M.Map (L' l1 l2 name) (Transition (L' l1 l2 name) name))
  go l@(L'V l1 l2 m1or2) m
   -- Already computed.
   | M.member l m
   = return m

   | M'1 <- m1or2
   , Just t1 <- M.lookup l1 (_trans m1)
   = case t1 of
      Pull ina l1Y l1N
       | ina `S.member` out2
       -> insert m l (Skip (L'V l1 l2 M'2))
      _
       -> insert m l (mapT (\l1' -> L'V l1' l2 M'1) t1)
   | M'2 <- m1or2
   , Just t1 <- M.lookup l1 (_trans m1)
   , Just t2 <- M.lookup l2 (_trans m2)
   = case t2 of
      Out f l'
       | Pull ina l1Y l1N <- t1
       , ina == _state f
       -> insert m l (Out f (L'V l1Y l' M'1))
      OutFinished n l'
       | Pull ina l1Y l1N <- t1
       , ina == n
       -> insert m l (OutFinished n (L'V l1N l' M'1))
      _
       -> insert m l (mapT (\l2' -> L'V l1 l2' M'2) t2)

   | otherwise
   = Left (ErrorBadTransition l1 l2)

  insert m l t@(Pull _ lY lN)
   = do m' <- go lY (M.insert l t m)
        go lN m'
  insert m l t@(Release _ l')
   = go l'
   $ M.insert l t m
  insert m l t@(Update _ l')
   = go l'
   $ M.insert l t m
  insert m l t@(If _ lY lN)
   = do m' <- go lY (M.insert l t m)
        go lN m'
  insert m l t@(Out _ l')
   = go l'
   $ M.insert l t m
  insert m l t@(OutFinished _ l')
   = go l'
   $ M.insert l t m
  insert m l t@(Skip l')
   = go l'
   $ M.insert l t m
  insert m l Done
   = return
   $ M.insert l Done m

  (in1,out1) = freevars m1
  (in2,out2) = freevars m2

