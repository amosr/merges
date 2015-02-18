module Automata2 where

import qualified Data.Set as S
import qualified Data.Map as M

import Data.Monoid

newtype Function = FunctionName String
 deriving Show

data Machine label name
 = Machine
 { _init  :: label -- would be initial state here too
 , _trans :: M.Map label (Transition label name)
 }
 deriving Show

data Transition label name
 = Pull   name         label label
 | Update Function name label
 | If     Function name label label
 | Out    Function name label
 | Skip   label
 | Done
 deriving Show

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

  ppr_t (Update (FunctionName fn) out l)
   =  show out ++ "_s = " ++ fn ++ "\n"
   ++ "     goto " ++ lbl l ++ "\n"

  ppr_t (If (FunctionName fn) out yes no)
   =  "case " ++ fn ++ " of\n"
   ++ "     True     -> goto " ++ lbl yes ++ "\n"
   ++ "     False    -> goto " ++ lbl no  ++ "\n"

  ppr_t (Out (FunctionName fn) out l)
   =  show out ++ "_v = " ++ fn ++ "\n"
   ++ "     goto " ++ lbl l ++ "\n"

  ppr_t (Skip l)
   = "goto " ++ lbl l

  ppr_t Done
   = "return"

data L = L0 | L1 | L2 | L3 | LEnd
 deriving (Show, Eq, Ord)
data Names = A | B | C | D | E | U | V | W | X | Y | Z
 deriving (Show, Eq, Ord)

zip_a :: n -> n -> n -> Machine L n
zip_a ina inb out
 = Machine
 { _init = L0
 , _trans = M.fromList
 $ [ (L0, Pull ina L1 LEnd)
   , (L1, Pull inb L2 LEnd)
   , (L2, Out  (FunctionName "a*b") out L0)
   , (LEnd, Done) ]
 }

append_a :: n -> n -> n -> Machine L n
append_a ina inb out
 = Machine
 { _init = L0
 , _trans = M.fromList
 $ [ (L0, Pull ina                     L1 L2)
   , (L1, Out  (FunctionName "a") out L0)
   , (L2, Pull inb                     L3 LEnd)
   , (L3, Out  (FunctionName "b") out L2)

   , (LEnd, Done) ]
 }

merge_a :: n -> n -> n -> Machine Int n
merge_a ina inb out
 = Machine
 { _init = 0
 , _trans = M.fromList
 $ [ ( 0, Pull ina               1 a_empty)
   , ( 1, Pull inb               2 b_empty')
   , ( 2, Out  (FunctionName "min a b") out 3)
   , ( 3, If   (FunctionName "a < b")   out 4 5)
   , ( 4, Pull ina               2 a_empty')
   , ( 5, Pull inb               2 b_empty')

   , (10, Pull inb               11 50)
   , (11, Out  (FunctionName "b") out 10)

   , (20, Pull ina               21 50)
   , (21, Out  (FunctionName "a") out 20)

   , (50, Done)
   ]
 }
 where
  a_empty = 10
  a_empty'= 11
  b_empty'= 21

freevars :: Ord name => Machine l name -> (S.Set name, S.Set name)
freevars m
 = mconcat
 $ map get
 $ M.elems
 $ _trans m
 where
  get (Pull n _ _)
   = (S.singleton n, S.empty)
  get (Update _ n _)
   = (S.empty, S.singleton n)
  get (If _ n _ _)
   = (S.empty, S.singleton n)
  get (Out _ n _)
   = (S.empty, S.singleton n)
  get (Skip l)
   = (S.empty, S.empty)
  get (Done)
   = (S.empty, S.empty)

data Event name
 = Pulled name
 | Empty  name
 | Emitted name
 deriving (Eq,Ord,Show)

data L' l1 l2 name
 = L' l1 l2 [Event name]
 deriving (Eq,Ord,Show)

data MergeError l1 l2 name
 = ErrorBadTransition l1 l2
 | RequiresBuffer name
 | ErrorUnhandled (Transition l1 name) (Transition l2 name) [Event name]
 deriving Show

fuse :: (Ord name, Ord l1, Ord l2) => Machine l1 name -> Machine l2 name -> Either (MergeError l1 l2 name) (Machine (L' l1 l2 name) name)
fuse m1 m2
 = do   trans <- go init M.empty
        return Machine
         { _init = init
         , _trans = trans
         }
 where
  init = L' (_init m1) (_init m2) []

  go l@(L' l1 l2 evs) m
   | M.member l m
   = return m

   | Just t1 <- M.lookup l1 (_trans m1)
   , Just t2 <- M.lookup l2 (_trans m2)
   = case (t1,t2) of

     -- Updates
     (Update f n l', _)
      -> insert m l (Update f n (L' l' l2 evs))
     (_, Update f n l')
      -> insert m l (Update f n (L' l1 l' evs))

     -- Ifs
     (If f n l1Y l1N, _)
      -> insert m l (If f n (L' l1Y l2 evs) (L' l1N l2 evs))
     (_, If f n l2Y l2N)
      -> insert m l (If f n (L' l1 l2Y evs) (L' l1 l2N evs))

     -- Skips
     (Skip l', _)
      -> insert m l (Skip (L' l' l2 evs))
     (_, Skip l')
      -> insert m l (Skip (L' l1 l' evs))

     -- Output first machine
     (Out f outa l', _)
      -- If outa is used by second machine, and there's already an unhandled emit for outa, we cannot emit any more
      | outa `S.member` in2
      , not (elem (Emitted outa) evs)
      -> insert m l (Out f outa (L' l' l2 (Emitted outa : evs)))
      -- If outa is used by second machine and second machine is finished,
      -- it doesn't matter
      | outa `S.member` in2
      , isDone t2
      -> insert m l (Out f outa (L' l' l2 (filter (/=Emitted outa) evs)))
      -- If outa is not used by the second machine, we can just output it
      | not (outa `S.member` in2)
      -> insert m l (Out f outa (L' l' l2 evs))

     -- Output second machine
     (_, Out f outb l')
      -- If outb is used by first machine, and there's already an unhandled emit for outb, we cannot emit any more
      | outb `S.member` in1
      , not (elem (Emitted outb) evs)
      -> insert m l (Out f outb (L' l1 l' (Emitted outb : evs)))
      -- If outa is used by first machine and first machine is finished,
      -- it doesn't matter
      | outb `S.member` in1
      , isDone t1
      -> insert m l (Out f outb (L' l1 l' (filter (/=Emitted outb) evs)))
      -- If outa is not used by the second machine, we can just output it
      | not (outb `S.member` in1)
      -> insert m l (Out f outb (L' l1 l' evs))

     -- If both machines are pulling from the same source, it's easy enough.
     -- We pull from the input once
     (Pull ina l1Y l1N, Pull inb l2Y l2N)
      | ina == inb
      -- Check if machine 1 has already pulled on this source, but machine 2 has not dealt with it.
      -- In which case, we just execute machine 2 with the existing value, leaving machine 1 alone
      , elem (Pulled ina) evs
      -> insert m l (Skip (L' l1 l2Y (filter (/=Pulled ina) evs)))
      | ina == inb
      -- I think we could actually step l1 to l1N here, because we know it's empty.
      , elem (Empty ina) evs
      -> insert m l (Skip (L' l1 l2N (filter (/=Empty ina) evs)))
          -- Left (RequiresBuffer ina)

      | ina == inb
      -> insert m l (Pull ina (L' l1Y l2Y evs) (L' l1N l2N evs))

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
     --   In this case, we can pull from ina, and add a `Pulled ina' event for machine two to handle
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
      , elem (Emitted ina) evs
      -> insert m l (Skip (L' l1Y l2 (filter (/= Emitted ina) evs)))
      | ina `S.member` out2
      -> insert m l (Skip (L' l1N l2 evs))

      -- Still some leftover bits to do
      | elem (Pulled ina) evs
      -> insert m l (Skip (L' l1Y l2 (filter (/= Pulled ina) evs)))
      | elem (Empty ina) evs
      -> insert m l (Skip (L' l1N l2 (filter (/= Empty ina) evs)))
      -- Just an input
      | otherwise
      -> insert m l (Pull ina (L' l1Y l2 evs) (L' l1N l2 evs))

     (Pull ina l1Y l1N, _)
      -- 2. fall through

      -- 3. ina is used by both machines, and there is no existing buffered value of ina
      | not (elem (Pulled ina) evs || elem (Empty ina) evs)
      , ina `S.member` in2
      -> insert m l (Pull ina (L' l1Y l2 (Pulled ina : evs)) (L' l1N l2 (Empty ina : evs)))

      -- 4. fall through

      -- 5. ina is computed by the second machine, and is on the event stack
      | ina `S.member` out2
      , elem (Emitted ina) evs
      -> insert m l (Skip (L' l1Y l2 (filter (/=Emitted ina) evs)))

      -- 6. ina is not used by the second machine
      | not (ina `S.member` in2) && not (ina `S.member` out2)
      -> insert m l (Pull ina (L' l1Y l2 evs) (L' l1N l2 evs))



     -- The second machine is trying to pull.
     -- Similarly, if the first machine is done, the second can do more or less what it wants.
     -- TODO: actually, I think the second machine should be given priority in this case
     -- since the first machine is the 'driver', ... Not quite that simple.
     -- I think we might want a "release" mechanism
     (Done, Pull inb l2Y l2N)
      -- inb is computed by first machine so it must be finished
      | inb `S.member` out1
      , elem (Emitted inb) evs
      -> insert m l (Skip (L' l1 l2Y (filter (/= Emitted inb) evs)))
      | inb `S.member` out1
      -> insert m l (Skip (L' l1 l2N evs))
      | elem (Pulled inb) evs
      -> insert m l (Skip (L' l1 l2Y (filter (/= Pulled inb) evs)))
      | elem (Empty inb) evs
      -> insert m l (Skip (L' l1 l2N (filter (/= Empty inb) evs)))
      | otherwise
      -> insert m l (Pull inb (L' l1 l2Y evs) (L' l1 l2N evs))

     (_, Pull inb l2Y l2N)
      -- If inb is also used by first machine, don't pull but wait for first machine to do it.
      | inb `S.member` in1
      -- there is a value of inb
      , elem (Pulled inb) evs
      -> insert m l (Skip (L' l1 l2Y (filter (/= Pulled inb) evs)))
      | inb `S.member` in1
      -- inb is finished
      , elem (Empty inb) evs
      -> insert m l (Skip (L' l1 l2N (filter (/= Empty inb) evs)))

      -- inb is computed by the first machine, and it has produced a value
      | inb `S.member` out1
      , elem (Emitted inb) evs
      -> insert m l (Skip (L' l1 l2Y (filter (/=Emitted inb) evs)))

      -- If inb is not used by the first machine, we can pull as we wish
      | not (inb `S.member` in1) && not (inb `S.member` out1)
      -> insert m l (Pull inb (L' l1 l2Y evs) (L' l1 l2N evs))
     -- Both done
     (Done, Done)
      -> insert m l Done

     (_,_)
      -> Left (ErrorUnhandled t1 t2 evs)


   | otherwise
   = Left (ErrorBadTransition l1 l2)

  insert m l t@(Pull _ lY lN)
   = do m' <- go lY (M.insert l t m)
        go lN m'
  insert m l t@(Update _ _ l')
   = go l'
   $ M.insert l t m
  insert m l t@(If _ _ lY lN)
   = do m' <- go lY (M.insert l t m)
        go lN m'
  insert m l t@(Out _ _ l')
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
