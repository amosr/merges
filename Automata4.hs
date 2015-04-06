-- Definition of machines
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


