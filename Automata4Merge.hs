-- General merging of machines
module Automata4Merge where
import Automata4

import qualified Data.Set as S
import qualified Data.Map as M


-- | The resulting label type of fusing two machines.
data L' l1 l2 name
 -- | Cross product of the two labels, along with a set of pending events
 = L' l1 l2 (S.Set (Event name))
 deriving (Eq,Ord,Show)

-- | Possible errors
data MergeError l1 l2 name fun
 -- | One of the input machines is malformed, pointing to a non-existent label
 = ErrorBadTransition l1 l2
 -- | An unhandled case. Probably requires extra buffering.
 | ErrorUnhandled (Transition l1 name fun) (Transition l2 name fun) (S.Set (Event name))
 -- | No release after a pull
 | ErrorNoRelease (Transition l1 name fun) (Transition l2 name fun) (S.Set (Event name))
 -- | Release after unsuccessful pull or something
 | ErrorReleaseOfNonValue (Transition l1 name fun) (Transition l2 name fun) (S.Set (Event name))
 deriving Show


-- | Fuse two machines together.
-- They should share at least one input, or one of the outputs should be another's inputs.
-- If they do not share anything, it will still work, but the ordering will be kind of arbitrary.
fuse :: (Ord name, Ord l1, Ord l2) => Machine l1 name fun -> Machine l2 name fun -> Either (MergeError l1 l2 name fun) (Machine (L' l1 l2 name) name fun)
fuse m1 m2
 = do   trans <- go init M.empty
        return Machine
         { _init = init
         , _trans = trans
         }
 where
  init = L' (_init m1) (_init m2) S.empty

  -- Compute the transition for new state l, adding it to the map.
  -- go :: (L' l1 l2 name) -> M.Map (L' l1 l2 name) (Transition (L' l1 l2 name) name) -> Either (MergeError l1 l2 name) (M.Map (L' l1 l2 name) (Transition (L' l1 l2 name) name))
  go l@(L' l1 l2 evs) m
   -- Already computed.
   | M.member l m
   = return m

   -- Look up transitions of each machine.
   -- If this fails, the original machine must be malformed.
   | Just t1 <- M.lookup l1 (_trans m1)
   , Just t2 <- M.lookup l2 (_trans m2)
   = case (t1,t2) of

     -- Simple cases --------------------
     -- Updates can be performed as usual.
     (Update f l', _)
      -> insert m l (Update f (L' l' l2 evs))
     (_, Update f l')
      -> insert m l (Update f (L' l1 l' evs))

     -- Ifs only affect one machine.
     -- If we knew somehow (magically) that the two functions were the same, with the same state/inputs,
     -- we could take both ifs in the same direction.
     -- But we don't, which is why (merge A B) and (merge A B) will not fuse.
     (If f l1Y l1N, _)
      -> insert m l (If f (L' l1Y l2 evs) (L' l1N l2 evs))
     (_, If f l2Y l2N)
      -> insert m l (If f (L' l1 l2Y evs) (L' l1 l2N evs))

     -- Skips
     (Skip l', _)
      -> insert m l (Skip (L' l' l2 evs))
     (_, Skip l')
      -> insert m l (Skip (L' l1 l' evs))

     -- Both machines are done
     (Done, Done)
      -> insert m l Done


     -- Outputs -------------------------

     -- Output first machine
     (Out f l', _)
      -- If outa is used by second machine and second machine is finished,
      -- it doesn't matter
      | _state f `S.member` in2
      , isDone t2
      -> insert m l (Out f (L' l' l2 (S.delete (Value (_state f)) evs)))
      -- If outa is used by second machine, and there's already an unhandled emit for outa, we cannot emit any more
      | _state f `S.member` in2
      , not (S.member (Value (_state f)) evs)
      -> insert m l (Out f (L' l' l2 (S.insert (Value (_state f)) evs)))
      -- If outa is not used by the second machine, we can just output it
      | not (_state f `S.member` in2)
      -> insert m l (Out f (L' l' l2 evs))

     -- Output second machine
     (_, Out f l')
      -- If outa is used by first machine and first machine is finished,
      -- it doesn't matter
      | _state f `S.member` in1
      , isDone t1
      -> insert m l (Out f (L' l1 l' (S.delete (Value (_state f)) evs)))
      -- If outb is used by first machine, and there's already an unhandled emit for outb, we cannot emit any more
      | _state f `S.member` in1
      , not (S.member (Value (_state f)) evs)
      -> insert m l (Out f (L' l1 l' (S.insert (Value (_state f)) evs)))
      -- If outa is not used by the second machine, we can just output it
      | not (_state f `S.member` in1)
      -> insert m l (Out f (L' l1 l' evs))

     -- Output first machine finished
     (OutFinished o l', _)
      -- If output is used by second machine, and the second machine is finished, go ahead
      | o `S.member` in2
      , isDone t2
      -> insert m l (OutFinished o (L' l' l2 (S.insert (Finished o) evs)))
      -- If output is used by the second machine, and there are no unhandled events, go ahead
      | o `S.member` in2
      , not (S.member (Value o) evs)
      -> insert m l (OutFinished o (L' l' l2 (S.insert (Finished o) evs)))
      -- If output is not used, don't have to add an event for it
      | not (o `S.member` in2)
      -> insert m l (OutFinished o (L' l' l2 evs))

     -- Output second machine finished
     (_, OutFinished o l')
      -- If output is used by first machine, and the first machine is finished, go ahead
      | o `S.member` in1
      , isDone t1
      -> insert m l (OutFinished o (L' l1 l' (S.insert (Finished o) evs)))
      -- If output is used by the first machine, and there are no unhandled events, go ahead
      | o `S.member` in1
      , not (S.member (Value o) evs)
      -> insert m l (OutFinished o (L' l1 l' (S.insert (Finished o) evs)))
      -- If output is not used, don't have to add an event for it
      | not (o `S.member` in1)
      -> insert m l (OutFinished o (L' l1 l' evs))


     -- Pulls ----------------

     -- The first machine is trying to pull.
     -- There are a few possibilities here:
     --
     --1* the second machine is Done, which means the first machine can execute whatever it wants.
     --   We pull from ina, and leave the second machine at Done.
     --
     --2* ina is used by both machines, has already been pulled by the first machine, but the second machine hasn't consumed this input yet.
     --   The pull cannot be performed as it would require buffering. We fall through to a later case, to allow machine 2 to run.
     --
     --3* ina is used by both machines, and there is no existing buffered value of ina.
     --   In this case, we can pull from ina, and add a `Value ina' event for machine two to handle
     --
     --4* ina is actually computed by the second machine, and has not yet been computed by machine 2.
     --   We fall through to a later case, allowing machine 2 to run.
     --
     --5* ina is computed by the second machine, and is already on the event stack.
     --   We can simply skip machine 1 to its next state with input.
     --
     --6* ina is not used by the second machine, so can be pulled with no restrictions.
     --   We pull from ina, without adding an event for machine two.

     -- 1. Second machine is done.
     (Pull ina l1Y l1N, Done)
      -- Second machine computes ina, so we know it's finished
      | ina `S.member` out2
      , S.member (Value ina) evs
      -> insert m l (Skip (L' l1Y l2 evs))
      | ina `S.member` out2
      -> insert m l (Skip (L' l1N l2 evs))

      -- Still some leftover bits to do
      | S.member (Value ina) evs
      -> insert m l (Skip (L' l1Y l2 evs))
      | S.member (Finished ina) evs
      -> insert m l (Skip (L' l1N l2 evs))
      -- Just an input
      | otherwise
      -> insert m l (Pull ina (L' l1Y l2 evs) (L' l1N l2 evs))

     (Pull ina l1Y l1N, _)
      -- 2. fall through

      -- ina is finished
      | S.member (Finished ina) evs
      -> insert m l (Skip (L' l1N l2 evs))

      -- 3. ina is used by both machines, and there is no existing buffered value of ina
      | not (S.member (Value ina) evs)
      , ina `S.member` in2
      -> insert m l (Pull ina (L' l1Y l2 (S.insert (Value ina) evs)) (L' l1N l2 (S.insert (Finished ina) evs)))

      -- 4. fall through

      -- 5. ina is computed by the second machine, and is on the event stack
      | ina `S.member` out2
      , S.member (Value ina) evs
      -> insert m l (Skip (L' l1Y l2 evs))
      -- ina is computed by the second machine, and it's finished
      | ina `S.member` out2
      , S.member (Finished ina) evs
      -> insert m l (Skip (L' l1N l2 evs))

      -- 6. ina is not used by the second machine
      | not (ina `S.member` in2) && not (ina `S.member` out2)
      -> insert m l (Pull ina (L' l1Y l2 evs) (L' l1N l2 (S.insert (Finished ina) evs)))



     -- The second machine is trying to pull.
     -- Similarly, if the first machine is done, the second can do more or less what it wants.
     (Done, Pull inb l2Y l2N)
      -- inb is computed by first machine so it must be finished
      | inb `S.member` out1
      , S.member (Value inb) evs
      -> insert m l (Skip (L' l1 l2Y evs))
      | inb `S.member` out1
      -> insert m l (Skip (L' l1 l2N evs))
      | S.member (Value inb) evs
      -> insert m l (Skip (L' l1 l2Y evs))
      | S.member (Finished inb) evs
      -> insert m l (Skip (L' l1 l2N evs))
      | otherwise
      -> insert m l (Pull inb (L' l1 l2Y evs) (L' l1 l2N evs))

     (_, Pull inb l2Y l2N)
      -- If inb is also used by first machine, don't pull but wait for first machine to do it.
      | inb `S.member` in1
      -- there is a value of inb. we may proceed.
      -- but don't delete value - release will do that
      , S.member (Value inb) evs
      -> insert m l (Skip (L' l1 l2Y evs))
      | inb `S.member` in1
      -- inb is finished
      , S.member (Finished inb) evs
      -> insert m l (Skip (L' l1 l2N evs))

      -- inb is computed by the first machine, and it has produced a value
      | inb `S.member` out1
      , S.member (Value inb) evs
      -> insert m l (Skip (L' l1 l2Y evs))

      -- If inb is not used by the first machine, we can pull as we wish
      | not (inb `S.member` in1) && not (inb `S.member` out1)
      -> insert m l (Pull inb (L' l1 l2Y evs) (L' l1 l2N evs))

     (Release ina l', _)
      -- If ina is computed by the second machine, we must have a value of it in the buffer now.
      -- Release it.
      | ina `S.member` out2
      -- , Value ina `S.member` evs
      -> insert m l (Skip (L' l' l2 (S.delete (Value ina) evs)))
      -- Otherwise, we don't have a value in the buffer and something is very wrong
      -- | ina `S.member` out2
      -- -> Left (ErrorReleaseOfNonValue t1 t2 evs)

      -- If ina is used by second machine, we cannot release until after it has
      | ina `S.member` in2
      , not (Value ina `S.member` evs) || isDone t2
      -> insert m l (Release ina (L' l' l2 evs))

      -- If ina is not used or computed by the second machine, we can release as we please.
      -- It's not needed in the events
      | not (ina `S.member` in2) && not (ina `S.member` out2)
      -> insert m l (Release ina (L' l' l2 evs))

     (_, Release inb l')
      -- If inb is computed by the first machine, we must have a value of it in the buffer now.
      -- Release it.
      | inb `S.member` out1
      -- , Value inb `S.member` evs
      -> insert m l (Skip (L' l1 l' (S.delete (Value inb) evs)))
      -- Otherwise, we don't have a value in the buffer and something is very wrong
      -- | inb `S.member` out1
      -- -> Left (ErrorReleaseOfNonValue t1 t2 evs)

      -- If inb is used by the first machine but it's finished, we must release
      | inb `S.member` in1
      , isDone t1
      -> insert m l (Release inb (L' l1 l' (S.delete (Value inb) evs)))
      -- If inb is used by the first machine, we don't need to perform an actual release, but just remove it from events so the first machine can release.
      | inb `S.member` in1
      , Value inb `S.member` evs
      -> insert m l (Skip (L' l1 l' (S.delete (Value inb) evs)))
      -- inb is used by the first machine and we don't have it in the buffer yet. Bad.
      | inb `S.member` in1
      -> Left (ErrorReleaseOfNonValue t1 t2 evs)

      -- If inb is not used by the first machine, we can release
      | not (inb `S.member` in1) && not (inb `S.member` out1)
      -> insert m l (Release inb (L' l1 l' evs))


     (_,_)
      -> Left (ErrorUnhandled t1 t2 evs)


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


fuse_print a b
 = case fuse a b of
    Left err -> putStrLn ("error: " ++ show err)
    Right v  -> putStrLn (ppr_machine v)

