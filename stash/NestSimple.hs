-- | All same type
--
{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes, TupleSections #-}
module NestSimple where
import qualified Stream       as SS
import qualified Merge        as MM
import qualified Data.Map as M
import Debug.Trace

type Elt = Int
type Name=String

data Op where
    OpStream :: SS.Stream Elt Elt     s -> s -> Name -> Op
    OpMerge  :: MM.Merge  Elt Elt Elt s -> s -> Name -> Name -> Op

data Nest
 = Nest
 { _ins  :: [Name]
 , _outs :: [Name]
 , _ops  :: [(Name,Op)] }

opSS :: SS.Stream Elt Elt s -> Name -> Op
opSS ss in1
 = OpStream ss (SS._init ss) in1

opMM :: MM.Merge Elt Elt Elt s -> Name -> Name -> Op
opMM mm in1 in2
 = OpMerge mm (MM._init mm) in1 in2

data Status
 = Yield Int
 | Done
 deriving (Show, Eq)

maybeOfStatus :: Status -> Maybe Int
maybeOfStatus (Yield i) = Just i
maybeOfStatus Done      = Nothing

type SMap    = M.Map Name Status

type InMap   = M.Map Name [Elt]
type OutMap  = M.Map Name [Elt]
-- a thing and its outputs, and whether they are waiting on something
type WaitMap = M.Map Name (M.Map Name Bool)

waitMap :: Nest -> WaitMap
waitMap nest
 = foldl insert init (_ops nest)
 where
  init
   = M.fromList
   $ map (,M.empty)
   (_ins nest ++ map fst (_ops nest))

  insert m (n,OpMerge _ _ in1 in2)
   = insM in1 n
   $ insM in2 n
   $ m
  insert m (n,OpStream _ _ in1)
   = insM in1 n
   $ m

  insM :: Name -> Name -> WaitMap -> WaitMap
  insM inp out m
   = M.insertWith M.union
     inp
   ( M.singleton out True )
     m

-- are all users of n waiting on input?
waiting :: WaitMap -> Name -> Bool
waiting wm n
 = and
 $ M.elems
 $ maybe M.empty id
 $ M.lookup n wm
 

inmap :: Nest -> [[Elt]] -> InMap
inmap Nest{_ins = ns} ins
 = M.fromList
 $ zip ns ins

pull_in :: Name -> InMap -> SMap -> (InMap, SMap)
pull_in n im sm
 = case M.lookup n im of
   Just (x:xs)
    -> ( M.insert n xs        im
       , M.insert n (Yield x) sm)
   _
    -> ( im
       , M.insert n Done      sm)

data OOp
 = OInput
 | OOp Op

nest_ops :: Nest -> [(Name, OOp)]
nest_ops nest
 =  map (,OInput) (_ins nest)
 ++ map (\(n,o) -> (n, OOp o)) (_ops nest)


run1 :: InMap -> SMap -> (Name,OOp) -> (InMap, SMap, Bool, [Name], OOp)
run1 im sm (nm,op)
 = case op of
    OInput
     -> let (im', sm') = pull_in nm im sm
        in  (im', sm', True, [], op)

    OOp (OpStream str s in1)
     -> let x = get in1
        in  case SS._emit str x s of
             SS.Yield v s' fw
              -> (im, put (Yield v), True
                 , ifFw fw in1
                 , OOp (OpStream str s' in1))
             SS.Skip s' fw
              -> (im, sm, False
                 , ifFw fw in1
                 , OOp (OpStream str s' in1))
             SS.Done
              -> (im, put Done, True, [], OOp (OpStream str s in1))

    OOp (OpMerge  mer s in1 in2)
     -> case (get in1, get in2) of
        (Just x1, Just x2)
         -> merg mer in1 in2    (MM._emit    mer x1 x2 s)
                 (move (MM._move    mer x1 x2 s) in1 in2)
            
        (Just x1, Nothing)
         -> merg mer in1 in2    (MM._remainL mer x1    s) [in1]
        (Nothing, Just x2)
         -> merg mer in1 in2    (MM._remainR mer    x2 s) [in2]
        (Nothing, Nothing)
         -> (im, M.insert nm Done sm, True, [], OOp (OpMerge mer s in1 in2))
         -- -> merg mer in1 in2    (MM._finish  mer       s, s) []

 where
  merg :: forall s. MM.Merge Elt Elt Elt s -> Name -> Name -> (Maybe Elt, s) -> [Name] -> (InMap, SMap, Bool, [Name], OOp)
  merg mer in1 in2 (out, s') mov
   = (im
     , maybe sm (put.Yield) out
     , maybe False (const True) out
     , mov
     , OOp (OpMerge mer s' in1 in2))

  get innm
   = case M.lookup innm sm of
      Nothing -> error "Scheduling error?"
      Just x  -> maybeOfStatus x

  put v
   = M.insert nm v sm

  ifFw SS.Forward nm
   = [nm]
  ifFw SS.Stay _nm
   = []
  move MM.L in1 in2
   = [in1]
  move MM.R in1 in2
   = [in2]
  move MM.LR in1 in2
   = [in1, in2]


add_out :: Nest -> SMap -> Name -> OutMap -> OutMap
add_out nest sm nm om
 | elem nm $ _outs nest
 , Just (Yield x) <- M.lookup nm sm
 = M.insertWith (flip (++)) nm [x] om
 | otherwise
 = om

schedule :: Nest -> [[Elt]] -> OutMap
schedule nest ins
 = go im sm wm om [] ops
 where
  im  = inmap nest ins
  sm  = M.empty
  wm  = waitMap nest
  om  = M.empty
  ops = nest_ops nest

  go im sm wm om pre []
   -- TODO check if done?
   = om

  go im sm wm om pre ((n,o):os)
   | trace (show (im,sm,wm,om)) True
   , Just m <- M.lookup n wm
   -- check if everything that relies on this operator's output
   -- is ready to receive something (waiting on input)
   , and $ M.elems m
   -- TODO check that input is available ???
   = let (im', sm', prog, waits, o') = run1 im sm (n,o)
         om' = add_out nest sm' n om
         m'  = if   prog
               then M.map (const False) m
               else m
         wm' = updwaits n waits $ M.insert n m' wm
     in if M.lookup n sm' == Just Done
        then go im' sm' wm' om' (pre ++ [(n,o)]) os
        else go im' sm' wm' om' [] (pre ++ [(n,o)] ++ os)

   | otherwise
   = go im sm wm om (pre ++ [(n,o)]) os

  updwaits n [] m
   = m
  updwaits n (n1:rs) m
   | Just m1 <- M.lookup n1 m
   = M.insert n1 (M.insert n True m1) m
   | otherwise
   = error ("Not in waitmap " ++ show (n, n1, m))

nest1 :: Nest
nest1
 = Nest
 { _ins = ["x"]
 , _ops = [("y", opSS (SS.map (+1)) "x")]
 , _outs = ["y"] }

nest2 :: Nest
nest2
 = Nest
 { _ins = ["x", "y"]
 , _ops = [("z", opMM MM.append "x" "y")]
 , _outs = ["z"] }


nest3 :: Nest
nest3
 = Nest
 { _ins = ["x"]
 , _ops = [("z", opMM MM.append "x" "x")]
 , _outs = ["z"] }


nest4 :: Nest
nest4
 = Nest
 { _ins = ["x", "y"]
 , _ops = [("z", opMM MM.segnums "x" "y")]
 , _outs = ["z"] }
-- suggestions from talk
-- PDL prop dyn logic, game theory first order logic, streamit, modal implication
