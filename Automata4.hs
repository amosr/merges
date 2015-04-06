module Automata4 where

import qualified Data.Set as S
import qualified Data.Map as M

import Data.Monoid

-- | A "worker function" that accesses state associated with a particular output,
-- and uses the current values of "inputs".
-- Each output has a separate state, the idea being different states are non-interfering and so can be reordered or whatever.
data Function name fun
 = Function
 { _fun     :: fun
 -- which output this function "belongs to"
 , _state   :: name
 -- arguments to function
 , _inputs  :: [name]
 }
 deriving (Show, Eq, Ord)

-- | A constrained state machine, though I call the machine states "labels", and the inside function state "output states".
data Machine label name fun
 = Machine
 { _init  :: label -- would be initial state here too
 , _trans :: M.Map label (Transition label name fun)
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
data Transition label name fun
 -- | Pull from input, going to first label if there is input available, or second if the input is finished.
 = Pull   name         label label
 -- | After a successful pull, the input must be released.
 -- This signifies that this machine is finished using the buffered value, and allows a new one to be pulled.
 -- In the case of fusing machines, this allows another machine to now pull from this input.
 | Release name        label
 -- | A named input may still have data, but we will not read it.
 -- For fusion, this means that the other machine now has full control over pulling this.
 | Close   name        label
 -- | Update the local output state, using given information.
 | Update (Function name fun) label
 -- | If based on given values and state
 | If     (Function name fun) label label
 -- | Output a single value to output stream (function's _state specifies which stream)
 | Out    (Function name fun) label
 -- | Finish the output stream. It cannot be written to any more.
 | OutFinished name label
 -- | Do nothing. Useful for code generation in fuse.
 | Skip   label
 -- | This machine has no more processing to do.
 -- When fusing two machines, if one is Done the other is free to execute as normal.
 | Done
 deriving Show

mapT :: (l -> l') -> Transition l n f -> Transition l' n f
mapT f t
 = case t of
    Pull n l1 l2    -> Pull n (f l1) (f l2)
    Release n l1    -> Release n (f l1)
    Close   n l1    -> Close   n (f l1)
    Update f' l1    -> Update f' (f l1)
    If f' l1 l2     -> If f' (f l1) (f l2)
    Out f' l1       -> Out f' (f l1)
    OutFinished n l1-> OutFinished n (f l1)
    Skip l1         -> Skip (f l1)
    Done            -> Done

isDone :: Transition l n f -> Bool
isDone Done
 = True
isDone _
 = False


-- | The alphabet for a machine
data Sigma name fun
 = SPullSome name
 | SPullNone name
 | SRelease name
 | SClose   name
 | SUpdate  (Function name fun)
 | SIfTrue  (Function name fun)
 | SIfFalse (Function name fun)
 | SOut     (Function name fun)
 | SOutFinished name
 | SSkip
 deriving (Eq, Show, Ord)


is_predecessor :: Eq label => label -> Transition label name fun -> [Sigma name fun]
is_predecessor l t
 = case t of
    Pull n l1 l2
     -> ifeq l1 (SPullSome n) ++ ifeq l2 (SPullNone n)
    Release n l1
     -> ifeq l1 (SRelease n)
    Close   n l1
     -> ifeq l1 (SClose n)
    Update f l1
     -> ifeq l1 (SUpdate f)
    If f l1 l2
     -> ifeq l1 (SIfTrue f) ++ ifeq l2 (SIfFalse f)
    Out f l1
     -> ifeq l1 (SOut f)
    OutFinished n l1
     -> ifeq l1 (SOutFinished n)
    Skip l1
     -> ifeq l1 (SSkip)
    Done
     -> []
 where
  ifeq l' r
   = if l == l'
     then [r]
     else []

preds :: Eq label => Machine label name fun -> label -> [(label, Sigma name fun)]
preds m l
 = concatMap go
 $ M.toList
 $ _trans m
 where
  go (l',t)
   = map (\t -> (l',t)) (is_predecessor l t)

succs :: Transition label name fun -> [(label, Sigma name fun)]
succs t
 = case t of
    Pull n l1 l2
     -> [(l1, SPullSome n), (l2, SPullNone n)]
    Release n l
     -> [(l, SRelease n)]
    Close n l
     -> [(l, SClose n)]
    Update f l
     -> [(l, SUpdate f)]
    If f l1 l2
     -> [(l1, SIfTrue f), (l2, SIfTrue f)]
    Out f l
     -> [(l, SOut f)]
    OutFinished n l
     -> [(l, SOutFinished n)]
    Skip l
     -> [(l, SSkip)]
    Done
     -> []


-- | Pretty print a machine as an ugly goto program
ppr_machine :: (Ord label, Show label, Show name, Show fun) => Machine label name fun -> String
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

  ppr_t (Close ss l)
   =  "close   " ++ show ss ++ "\n"
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
   = show (_fun f) ++ "(" ++ show (_state f) ++ ", " ++ show (_inputs f) ++ ")"



-- | Collect the inputs and outputs of a machine.
freevars :: Ord name => Machine l name fun -> (S.Set name, S.Set name)
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
  get (Close n _)
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
 -- | An input stream has been closed before it is finished
 | Closed name
 deriving (Eq,Ord,Show)


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

-- | Minimise
minimise :: (Ord l, Ord n, Eq f) => Machine l n f -> Machine Int n f
minimise
 = minimise_hopcroft . minimise_skips

-- | Minimise
-- Just remove skips (epsilons?) for now
minimise_skips :: Ord l => Machine l n f -> Machine l n f
minimise_skips m
 = Machine
 { _init  = to (_init m)
 , _trans = M.mapMaybe go (_trans m)
 }
 where
  to l
   = case M.lookup l $ _trans m of
      Nothing -> error "Malformed machine to minimise"
      Just (Skip l') -> to l'
      Just _    -> l

  go t
   = case t of
      Skip _ -> Nothing

      Pull n l1 l2      -> Just $ Pull n (to l1) (to l2)
      Release n l       -> Just $ Release n (to l)
      Close   n l       -> Just $ Close   n (to l)
      Update f l        -> Just $ Update f (to l)
      If f l1 l2        -> Just $ If f (to l1) (to l2)
      Out f l           -> Just $ Out f (to l)
      OutFinished n l   -> Just $ OutFinished n (to l)
      Done              -> Just $ Done
      

minimise_hopcroft :: (Ord l, Ord n, Eq f) => Machine l n f -> Machine Int n f
minimise_hopcroft m
 = let ts = M.toList $ _trans m
       qs = S.fromList $ map fst   ts
       fs = S.fromList $ map fst $ filter (isDone.snd) ts
       cs = classes (S.fromList [fs, qs S.\\ fs]) (S.fromList [fs])
   in  partition_by m cs
 where
  classes p w
   | Just (a, w') <- S.minView w
   = let chars    = m_fromListWith S.union $ map swappy $ concatMap (preds m) $ S.toList a
         (p',w'') = foldl char_split (p,w') chars
     in  classes p' w''

   -- w is empty
   | otherwise
   = p

  -- M.fromListWith, but without Ord.
  m_fromListWith f ls
   = foldl (m_ins f) [] ls

  m_ins f [] (a,s)
   = [(a,s)]
  m_ins f ((a',s'):rs) (a,s)
   | a' == a
   = (a, f s s') : rs
   | otherwise
   = (a', s') : m_ins f rs (a,s)

  char_split (p,w) (_, pres)
   = S.fold (split pres) (p, w) p

  split x y (p,w)
   | xny <- S.intersection x y
   , ymx <- y S.\\ x
   , not $ S.null xny 
   , not $ S.null ymx 
   = let p' = S.insert xny (S.insert ymx (S.delete y p))
         w' | y `S.member` w
            = S.insert xny (S.insert ymx (S.delete y w))
            | otherwise
            = w
    in   if   S.size xny <= S.size ymx
         then (p', S.insert xny w')
         else (p', S.insert ymx w')

   | otherwise
   = (p, w)

  swappy (a,b) = (b,S.singleton a)

partition_by :: Ord l => Machine l n f -> S.Set (S.Set l) -> Machine Int n f
partition_by m cs
 = Machine
 { _init  = ix (_init m)
 , _trans = M.fromList $ map go $ M.toList $ _trans m
 }
 where
  ix l
   = case concatMap (ix_search l) (S.toList cs `zip` [0..]) of
      [] -> error "bad partition"
      (x:xs) -> x
  ix_search l (c,ix)
   | l `S.member` c
   = [ix]
   | otherwise
   = []

  go (l, t)
   = (ix l, trans t)

  trans t
   = case t of
      Pull n l1 l2      -> Pull n (ix l1) (ix l2)
      Release n l1      -> Release n (ix l1)
      Close   n l1      -> Close   n (ix l1)
      Update f l1       -> Update f (ix l1)
      If f l1 l2        -> If f (ix l1) (ix l2)
      Out f l1          -> Out f (ix l1)
      OutFinished n l1  -> OutFinished n (ix l1)
      Skip l1           -> Skip (ix l1)
      Done              -> Done

-- TODO
minimise_reorder :: Ord l => Machine l n f -> Machine l n f
minimise_reorder m
 = Machine
 { _init = _init m
 , _trans = M.fromList $ map go $ M.toList $ _trans m
 }
 where
  go = id

