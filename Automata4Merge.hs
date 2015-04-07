-- General merging of machines
module Automata4Merge where
import Automata4

import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad (foldM)

import Debug.Trace

-- | The resulting label type of fusing two machines.
data L' l1 l2 name
 -- | Cross product of the two labels, along with a set of pending events for each machine
 = L' l1 (S.Set (Event name)) l2 (S.Set (Event name))
 deriving (Eq,Ord,Show)


-- | Short-hand for a map from composite labels to transitions
type TMap l1 l2 name fun = M.Map (L' l1 l2 name) (Transition (L' l1 l2 name) name fun)


-- | Possible errors
data MergeError l1 l2 name fun
 -- | One of the input machines is malformed, pointing to a non-existent label
 = ErrorBadTransition (L' l1 l2 name)
 | ErrorBadTransitionV l1 l2
 -- | An unhandled case. Probably requires extra buffering.
 | ErrorUnhandled (Transition l1 name fun) (S.Set (Event name)) (Transition l2 name fun) (S.Set (Event name))
 deriving Show


-- | Fuse entire machine
fuse    :: (Ord name, Ord l1, Ord l2)
        => Machine l1 name fun -> Machine l2 name fun
        -> Either (MergeError l1 l2 name fun) (Machine (L' l1 l2 name) name fun)
fuse m1 m2
 = do   trans <- fuse' m1 m2 init M.empty
        return Machine
         { _init  = init
         , _trans = trans
         }
 where
  init = L' (_init m1) S.empty (_init m2) S.empty


-- | Add given label to machine, and recursively add its successors
fuse'   :: (Ord name, Ord l1, Ord l2)
        => Machine l1 name fun -> Machine l2 name fun
        -> L' l1 l2 name
        -> TMap l1 l2 name fun
        -> Either (MergeError l1 l2 name fun) (TMap l1 l2 name fun)
fuse' m1 m2 l m
 -- Don't add what's already there, so we can eventually terminate
 | Just _ <- M.lookup l m
 = return m

 | otherwise
 = do   t     <- move m1 m2 l
        let m' = M.insert l t m
        foldM (flip $ fuse' m1 m2) m' (map fst $ succs t)


-- | Compute transition for given label.
--
move    :: (Ord name, Ord l1, Ord l2)
        => Machine l1 name fun -> Machine l2 name fun
        -> L' l1 l2 name
        -> Either (MergeError l1 l2 name fun) (Transition (L' l1 l2 name) name fun)
move m1 m2 l
 | L' s1 e1 s2 e2 <- l
 , Just t1 <- M.lookup s1 (_trans m1)
 , Just t2 <- M.lookup s2 (_trans m2)
 -- (Commutative)
 = case move' m1 m2 t1 t2 l of
    Just mv -> return mv
    Nothing
     -> case move' m2 m1 t2 t1 (flipL l) of
         Just mv
          | trace "(Commutative)" True
          -> return (mapT flipL mv)
         Nothing
          | trace "Fail..." True
          -> Left (ErrorUnhandled t1 e1 t2 e2)
 | otherwise
 = Left (ErrorBadTransition l)

 where
  flipL (L' s1 e1 s2 e2)
   =     L' s2 e2 s1 e1

  move' m1 m2 t1 t2 (L' s1 e1 s2 e2)
   -- Non-interfering states

   -- (Update)
   | Update f s1' <- t1
   , trace "(Update)" True
   = return
   $ Update f (L' s1' e1 s2 e2)
   -- (Skip)
   | Skip s1' <- t1
   , trace "(Skip)" True
   = return
   $ Skip (L' s1' e1 s2 e2)
   -- (If)
   | If f st sf <- t1
   , trace "(If)" True
   = return
   $ If f (L' st e1 s2 e2) (L' sf e1 s2 e2)
   -- (DoneDone)
   | Done <- t1
   , Done <- t2
   , trace "(DoneDone)" True
   = return
   $ Done


   -- Output and finishing output

   -- (OutputClosed)
   | Out f s1' <- t1
   , n <- _state f
   , isInput n m2
   , Closed n `S.member` e2
   , trace "(OutputClosed)" True
   = return
   $ Out f (L' s1' e1 s2 e2)

   -- (OutputReady)
   | Out f s1' <- t1
   , n <- _state f
   , isInput n m2
   , not (Value n `S.member` e2)
   , trace "(OutputReady)" True
   = return
   $ Out f (L' s1' e1 s2 (S.insert (Value n) e2))

   -- (OutputLocal)
   | Out f s1' <- t1
   , n <- _state f
   , not $ isInput n m2
   , trace "(OutputLocal)" True
   = return
   $ Out f (L' s1' e1 s2 e2)

   -- (OutFinishedClosed)
   | OutFinished n s1' <- t1
   , isInput n m2
   , Closed n `S.member` e2
   , not (Value n `S.member` e2)
   , trace "(OutFinishedClosed)" True
   = return
   $ OutFinished n (L' s1' e1 s2 e2)

   -- (OutFinishedReady)
   | OutFinished n s1' <- t1
   , isInput n m2
   , not (Value  n `S.member` e2)
   , not (Closed n `S.member` e2)
   , trace "(OutFinishedReady)" True
   = return
   $ OutFinished n (L' s1' e1 s2 (S.insert (Finished n) e2))

   -- (OutFinishedLocal)
   | OutFinished n s1' <- t1
   , not $ isInput n m2
   , trace "(OutFinishedLocal)" True
   = return
   $ OutFinished n (L' s1' e1 s2 e2)


   -- Pulls

   -- (PullLocal)
   | Pull n sT sF <- t1
   , not $ isInput  n m2
   , not $ isOutput n m2
   , trace "(PullLocal)" True
   = return
   $ Pull n (L' sT e1 s2 e2) (L' sF e1 s2 e2)

   -- (PullClosed)
   | Pull n sT sF <- t1
   , Closed n `S.member` e2
   , trace "(PullClosed)" True
   = return
   $ Pull n (L' sT e1 s2 e2) (L' sF e1 s2 e2)

   -- (PullValue)
   | Pull n sT _F <- t1
   , Value n `S.member` e1
   , trace "(PullValue)" True
   = return
   $ Skip (L' sT e1 s2 e2)

   -- (PullFinished)
   | Pull n _T sF <- t1
   , Finished n `S.member` S.union e1 e2
   , not (Value n `S.member` S.union e1 e2)
   , trace "(PullFinished)" True
   = return
   $ Skip (L' sF e1 s2 e2)

   -- (PullReady)
   | Pull n sT sF <- t1
   , not (Finished n `S.member` S.union e1 e2)
   , not (Value n `S.member` S.union e1 e2)
   , isInput n m2
   , trace "(PullReady)" True
   = return
   $ Pull n (L' sT (S.insert (Value n) e1)    s2 (S.insert (Value n) e2)) 
            (L' sF (S.insert (Finished n) e1) s2 (S.insert (Finished n) e2))


   -- Releasing pulled values

   -- (ReleaseLocal)
   | Release n s' <- t1
   , not $ isInput  n m2
   , not $ isOutput n m2
   , trace "(ReleaseLocal)" True
   = return
   $ Release n (L' s' e1 s2 e2)
   
   -- (ReleaseOutput)
   | Release n s' <- t1
   , isOutput n m2
   , Value n `S.member` e1
   , trace "(ReleaseOutput)" True
   = return
   $ Skip (L' s' (S.delete (Value n) e1) s2 e2)

   -- (ReleaseSharedFirst)
   | Release n s' <- t1
   , isInput n m2
   , Value n `S.member` e1
   , Value n `S.member` e2
   , trace "(ReleaseSharedFirst)" True
   = return
   $ Skip (L' s' (S.delete (Value n) e1) s2 e2)

   -- (ReleaseSharedSecond)
   | Release n s' <- t1
   , isInput n m2
   , Value n `S.member` e1
   , not (Value n `S.member` e2)
   , trace "(ReleaseSharedSecond)" True
   = return
   $ Release n (L' s' (S.delete (Value n) e1) s2 e2)


   -- Closing

   -- (CloseLocal)
   | Close n s' <- t1
   , not $ isInput  n m2
   , not $ isOutput n m2
   , trace "(CloseLocal)" True
   = return
   $ Close n (L' s' e1 s2 e2)

   -- (CloseOutput)
   | Close n s' <- t1
   , isOutput n m2
   , trace "(CloseOutput)" True
   = return
   $ Skip (L' s' (S.insert (Closed n) e1) s2 e2)

   -- (CloseSharedOne)
   | Close n s' <- t1
   , isInput n m2
   , not (Finished n `S.member` S.union e1 e2)
   , not (Closed   n `S.member` e2)
   , trace "(CloseSharedOne)" True
   = return
   $ Skip (L' s' (S.insert (Closed n) e1) s2 e2)

   -- (CloseSharedFinished)
   | Close n s' <- t1
   , isInput n m2
   , Finished n `S.member` S.union e1 e2
   , trace "(CloseSharedFinished)" True
   = return
   $ Skip (L' s' (S.insert (Closed n) e1) s2 e2)

   -- (CloseSharedBoth)
   | Close n s' <- t1
   , isInput n m2
   , not (Finished n `S.member` S.union e1 e2)
   ,      Closed   n `S.member` e2
   , trace "(CloseSharedBoth)" True
   = return
   $ Close n (L' s' (S.insert (Closed n) e1) s2 e2)


   -- Failure!
   | otherwise
   = Nothing




  isInput n m
   = S.member n
   $ fst
   $ freevars m
  isOutput n m
   = S.member n
   $ snd
   $ freevars m

