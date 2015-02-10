module Automata4 where

import qualified Data.Set as S
import qualified Data.Map as M

import Data.Monoid

-- | A "worker function" that accesses state associated with a particular output,
-- and uses the current values of "inputs".
-- Each output has a separate state, the idea being different states are non-interfering and so can be reordered or whatever.
data Function name
 = Function
 { _name    :: String
 , _state   :: name
 , _inputs  :: [name]
 }
 deriving Show

-- | A constrained state machine, though I call the machine states "labels", and the inside function state "output states".
data Machine label name
 = Machine
 { _init  :: label -- would be initial state here too
 , _trans :: M.Map label (Transition label name)
 }
 deriving Show

-- | A transition from one label to others.
-- The reason "name" is not separated into ins and outs is that fusing two machines can wire one machine's inputs to another's outputs.
-- This would make the type of @fuse@ rather irritating.
--
-- There are certain invariants that a machine should uphold:
--  * A machine can only use an input after pulling from it, and before releasing it.
--  * A machine cannot release an input it has not pulled from, and can only release once.
--  * A machine must release an input before pulling from it again.
--  * A machine must not output to a stream after "finishing" the stream.
--  * A machine can only enter "Done" after finishing all its outputs.
--
data Transition label name
 -- | Pull from input, going to first label if there is input available, or second if the input is finished.
 = Pull   name         label label
 -- | After a successful pull, the input must be released.
 -- This signifies that this machine is finished using the buffered value, and allows a new one to be pulled.
 -- In the case of fusing machines, this allows another machine to now pull from this input.
 | Release name        label
 -- | Update the local output state, using given information.
 | Update (Function name) label
 -- | If based on given values and state
 | If     (Function name) label label
 -- | Output a single value to output stream (function's _state specifies which stream)
 | Out    (Function name) label
 -- | Finish the output stream. It cannot be written to any more.
 | OutFinished name label
 -- | Do nothing. Useful for code generation in fuse.
 | Skip   label
 -- | This machine has no more processing to do.
 -- When fusing two machines, if one is Done the other is free to execute as normal.
 | Done
 deriving Show


-- | Pretty print a machine as an ugly goto program
ppr_machine :: (Ord label, Show label, Show name) => Machine label name -> String
ppr_machine m
 = unlines $
    [ "goto " ++ lbl (_init m) ]
     ++ (map ppr_trans $ M.toList $ _trans m)
 where
  lbl l
   | Just ix <- M.lookupIndex l $ _trans m
   = "LBL" ++ show ix
   | otherwise
   = error "undefined_index"

  ppr_trans (l,t)
   = lbl l ++ ": (" ++ show l ++ ")\n    " ++ ppr_t t

  ppr_t (Pull ss yes no)
   =  show ss ++ "_v = read " ++ show ss ++ "\n"
   ++ "     if full  -> goto " ++ lbl yes ++ "\n"
   ++ "     if empty -> goto " ++ lbl no  ++ "\n"

  ppr_t (Release ss l)
   =  "release " ++ show ss ++ "\n"
   ++ "     goto " ++ lbl l ++ "\n"

  ppr_t (Update f l)
   =  show (_state f) ++ "_s = " ++ ppr_f f ++ "\n"
   ++ "     goto " ++ lbl l ++ "\n"

  ppr_t (If f yes no)
   =  "case " ++ ppr_f f ++ " of\n"
   ++ "     True     -> goto " ++ lbl yes ++ "\n"
   ++ "     False    -> goto " ++ lbl no  ++ "\n"

  ppr_t (Out f l)
   =  show (_state f) ++ "_v = " ++ ppr_f f ++ "\n"
   ++ "     emit " ++ show (_state f) ++ "_v\n"
   ++ "     goto " ++ lbl l ++ "\n"

  ppr_t (OutFinished o l)
   =  show o ++ "_v = Nothing" ++ "\n"
   ++ "     emit " ++ show o ++ "_v\n"
   ++ "     goto " ++ lbl l ++ "\n"

  ppr_t (Skip l)
   = "goto " ++ lbl l

  ppr_t Done
   = "return"

  ppr_f f
   = _name f ++ "(" ++ show (_state f) ++ ", " ++ show (_inputs f) ++ ")"


-- | Just for testing
data Names = A | B | C | D | E | U | V | W | X | Y | Z
 deriving (Show, Eq, Ord)

-- | Zip two inputs together.
-- 1. Pull from both.
-- 2. Output.
-- 3. Release both.
--    Goto 1.
zip_a :: n -> n -> n -> Machine Int n
zip_a ina inb out
 = Machine
 { _init = 0
 , _trans = M.fromList
 $ [ (0, Pull ina 1 999)
   , (1, Pull inb 2 999)
   , (2, Out  (Function "pair" out [ina,inb]) 3)
   , (3, Release ina 4)
   , (4, Release inb 0)
   , (999, OutFinished out 1000)
   , (1000, Done) ]
 }

-- | Append two inputs
append_a :: n -> n -> n -> Machine Int n
append_a ina inb out
 = Machine
 { _init = 0
 , _trans = M.fromList
 $ [ (0, Pull ina                     1 10)
   , (1, Out  (Function "just" out [ina]) 2)
   , (2, Release ina                  0)

   , (10, Pull inb                    11 999)
   , (11, Out  (Function "just" out [inb]) 12)
   , (12, Release inb                 10)

   , (999, OutFinished out 1000)
   , (1000, Done) ]
 }



-- | Collect the inputs and outputs of a machine.
freevars :: Ord name => Machine l name -> (S.Set name, S.Set name)
freevars m
 = mconcat
 $ map get
 $ M.elems
 $ _trans m
 where
  get (Pull n _ _)
   = (S.singleton n, S.empty)
  get (Release n _)
   = (S.singleton n, S.empty)
  get (Update f _)
   = get_f f
  get (If f _ _)
   = get_f f
  get (Out f _)
   = get_f f
  get (OutFinished n _)
   = (S.empty, S.singleton n)
  get (Skip l)
   = (S.empty, S.empty)
  get (Done)
   = (S.empty, S.empty)

  get_f f
   = (S.fromList $ _inputs f, S.singleton $ _state f)


-- | Pending events that have not been dealt with by one of the machines
data Event name
 -- | A value has been pulled or created on this stream
 = Value name
 -- | This stream is finished
 | Finished  name
 deriving (Eq,Ord,Show)

-- | The resulting label type of fusing two machines.
data L' l1 l2 name
 -- | Cross product of the two labels, along with a set of pending events
 = L' l1 l2 (S.Set (Event name))
 deriving (Eq,Ord,Show)

-- | Possible errors
data MergeError l1 l2 name
 -- | One of the input machines is malformed, pointing to a non-existent label
 = ErrorBadTransition l1 l2
 -- | An unhandled case. Probably requires extra buffering.
 | ErrorUnhandled (Transition l1 name) (Transition l2 name) (S.Set (Event name))
 -- | No release after a pull
 | ErrorNoRelease (Transition l1 name) (Transition l2 name) (S.Set (Event name))
 -- | Release after unsuccessful pull or something
 | ErrorReleaseOfNonValue (Transition l1 name) (Transition l2 name) (S.Set (Event name))
 deriving Show

-- | Fuse two machines together.
-- They should share at least one input, or one of the outputs should be another's inputs.
-- If they do not share anything, it will still work, but the ordering will be kind of arbitrary.
fuse :: (Ord name, Ord l1, Ord l2) => Machine l1 name -> Machine l2 name -> Either (MergeError l1 l2 name) (Machine (L' l1 l2 name) name)
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

     -- If both machines are pulling from the same source, it's easy enough.
     -- We pull from the input once
     (Pull ina l1Y l1N, Pull inb l2Y l2N)
      | ina == inb
      -- Check if machine 1 has already pulled on this source, but machine 2 has not dealt with it.
      -- This actually means that machine 1 has pulled without releasing.
      , S.member (Value ina) evs
      -> Left (ErrorNoRelease t1 t2 evs) -- insert m l (Skip (L' l1 l2Y (filter (/=Value ina) evs)))
      | ina == inb
      -- We already know the input is finished, so we can just skip to the finished parts.
      -- We don't need to filter out the finished here, because it'll stay finished
      , S.member (Finished ina) evs
      -> insert m l (Skip (L' l1N l2N evs))

      -- Pull both at once
      -- add a Value ina to the buffer, so l2 can release it.
      | ina == inb
      -> insert m l (Pull ina (L' l1Y l2Y (S.insert (Value ina) evs)) (L' l1N l2N (S.insert (Finished ina) evs)))

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
      -> insert m l (Skip (L' l1Y l2 (S.delete (Value ina) evs)))
      | ina `S.member` out2
      -> insert m l (Skip (L' l1N l2 evs))

      -- Still some leftover bits to do
      | S.member (Value ina) evs
      -> insert m l (Skip (L' l1Y l2 (S.delete (Value ina) evs)))
      | S.member (Finished ina) evs
      -> insert m l (Skip (L' l1N l2 evs))
      -- Just an input
      | otherwise
      -> insert m l (Pull ina (L' l1Y l2 evs) (L' l1N l2 evs))

     (Pull ina l1Y l1N, _)
      -- 2. fall through

      -- 3. ina is used by both machines, and there is no existing buffered value of ina
      | not (S.member (Value ina) evs)
      , ina `S.member` in2
      -> insert m l (Pull ina (L' l1Y l2 (S.insert (Value ina) evs)) (L' l1N l2 (S.insert (Finished ina) evs)))

      -- ina is finished
      | S.member (Finished ina) evs
      -> insert m l (Skip (L' l1N l2 evs))

      -- 4. fall through

      -- 5. ina is computed by the second machine, and is on the event stack
      | ina `S.member` out2
      , S.member (Value ina) evs
      -> insert m l (Skip (L' l1Y l2 (S.delete (Value ina) evs)))
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
      -> insert m l (Skip (L' l1 l2Y (S.delete (Value inb) evs)))
      | inb `S.member` out1
      -> insert m l (Skip (L' l1 l2N evs))
      | S.member (Value inb) evs
      -> insert m l (Skip (L' l1 l2Y (S.delete (Value inb) evs)))
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
      , Value ina `S.member` evs
      -> insert m l (Skip (L' l' l2 (S.delete (Value ina) evs)))
      -- Otherwise, we don't have a value in the buffer and something is very wrong
      | ina `S.member` out2
      -> Left (ErrorReleaseOfNonValue t1 t2 evs)

      -- If ina is used by second machine, we cannot release until after it has
      | ina `S.member` in2
      , not (Value ina `S.member` evs)
      -> insert m l (Release ina (L' l' l2 evs))

      -- If ina is not used or computed by the second machine, we can release as we please.
      -- It's not needed in the events
      | not (ina `S.member` in2)
      -> insert m l (Release ina (L' l' l2 evs))

     (_, Release inb l')
      -- If inb is computed by the first machine, we must have a value of it in the buffer now.
      -- Release it.
      | inb `S.member` out1
      , Value inb `S.member` evs
      -> insert m l (Skip (L' l1 l' (S.delete (Value inb) evs)))
      -- Otherwise, we don't have a value in the buffer and something is very wrong
      | inb `S.member` out1
      -> Left (ErrorReleaseOfNonValue t1 t2 evs)

      -- If inb is used by the first machine, we don't need to perform an actual release, but just remove it from events so the first machine can release.
      | inb `S.member` in1
      , Value inb `S.member` evs
      -> insert m l (Skip (L' l1 l' (S.delete (Value inb) evs)))
      -- inb is used by the first machine and we don't have it in the buffer yet. Bad.
      | inb `S.member` in1
      -> Left (ErrorReleaseOfNonValue t1 t2 evs)

      -- If inb is not used by the first machine, we can release
      | not (inb `S.member` in1)
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

  isDone Done
   = True
  isDone _
   = False

  (in1,out1) = freevars m1
  (in2,out2) = freevars m2


fuse_print a b
 = case fuse a b of
    Left err -> putStrLn ("error: " ++ show err)
    Right v  -> putStrLn (ppr_machine v)