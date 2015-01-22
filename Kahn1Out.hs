-- Kahn process networks
-- with only one output
{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes #-}

module Kahn1Out where
import Lists

import Debug.Trace


data Step s is o
 = forall i. Get s (Index is i) (Maybe i -> s -> Step s is o)
 |           Put s o                       (s -> Step s is o)
 |           Done

data Process s is o
 = Process s (s -> Step s is o)


eval1 :: Process s is o -> Values is -> [o]
eval1 (Process s_ f_) vs_
 = go s_ f_ vs_ []
 where
  go s f ins outs
   = case f s of
      Get s' ix   f'
       -> let (v,ins') = takedrop1 ix ins
          in  go s' (f' v) ins' outs
      Put s' o f'
       -> let outs'    = outs ++ [o]
          in  go s' f' ins outs'
      Done
       -> outs



data Graph :: [*] -> [*] -> [*] -> * where
  Empty :: Graph '[] '[] '[]
  Inp   :: Graph i d o -> Graph (a ': i) (a ': d) o
  Out   :: Index d x -> Graph i d o -> Graph i d (x ': o)

  Trans :: Indices d ins -> Process s ins out -> Graph i d o -> Graph i (out ': d) o

  -- For creating cycles
  -- BackEdge :: Index d a -> Index d a -> MarkedGraph i d o


data Status
 = Running [Int]
 | Finished
 | NotStarted
 deriving Show

-- for each data node, store the set of who is waiting on it,
-- and also the total number of outputs (max size of set)
data OutSet :: [*] -> * where
    OSNil  :: OutSet '[]
    OSCons :: Status -> Int -> OutSet xs -> OutSet (x ': xs)

instance Show (OutSet xs) where
 show OSNil = "OSNil"
 show (OSCons ss is os) = "OSCons (" ++ show ss ++ ") " ++ show is ++ " (" ++ show os ++ ")"

outSet :: Graph i d o -> OutSet d
outSet g_
 = go g_ 0
 where
  go :: forall i' d' o'. Graph i' d' o' -> Int -> OutSet d'
  go g ix = case g of
    Empty
     -> OSNil
    Inp g'
     -> OSCons NotStarted (count g_ ix) (go g' (ix+1))
    Out _ g'
     -> go g' ix
    Trans _ _ g'
     -> OSCons NotStarted (count g_ ix) (go g' (ix+1))

  count :: forall i' d' o'. Graph i' d' o' -> Int -> Int
  count g (-1)
   = 0
  count g n
   = case g of
      Empty
       -> 0
      Inp g'
       -> count g' (n-1)
      Out ix g'
       | natOfIx ix == n
       -> 1 + count g' n
       | otherwise
       -> count g' n
      Trans ixs _ g'
       -- Check against n-1 because trans itself binds a new one
       -> countIxs ixs (n-1) + count g' (n-1)

  countIxs :: forall xs ys. Indices xs ys -> Int -> Int
  countIxs INil _
   = 0
  countIxs (ICons ix rest) n
   = if   natOfIx ix == n
     then 1 + countIxs rest n
     else     countIxs rest n


evalG :: Graph i d o -> Values i -> (Values o, Bool)
evalG g_ ins_
 = let ds  = valsOfIns  g_ ins_
       os  = outsOfVals g_ ds
       set = outSet     g_
   in  go g_ ds os set
 where
  -- All list values in ds, except for inputs, must have 0 or 1 length
  go g ds os set
   = case fire1 g ds os set of
      Nothing
       -> (os, all_finished ds)
      Just (g', d', o', s')
       -> go g' d' o' s'

  fire1 :: Graph i' d' o' -> Values d' -> Values o' -> OutSet d' -> Maybe (Graph i' d' o', Values d', Values o', OutSet d')

  fire1 Empty _ _ _
   | trace "Empty" True
   = Nothing
  fire1 (Inp g) (VCons inp ds) os (OSCons swaiting smax set)
   | trace ("Inp:" ++ show swaiting) True
   = case swaiting of
      NotStarted
       -> Just (Inp g, VCons inp ds, os, OSCons (Running []) smax set)
      Running sw
       -> if   length sw == smax
          then let s' = if null inp then Finished else Running []
               in  Just (Inp g, VCons (tail inp) ds, os, OSCons s' smax set)
          else fmap (\(g',a,b,c) -> (Inp g', VCons inp a, b, OSCons swaiting smax c))
                    $ fire1 g ds os set
      Finished
       -> fmap (\(g', a,b,c) -> (Inp g', VCons inp a, b, OSCons swaiting smax c))
               $ fire1 g ds os set

  fire1 (Out ox g) ds (VCons o os) set
   | trace ("Out") True
   , not $ lookupWaiting ox set
   , (Just val,_) <- takedrop1 ox ds
   = Just (Out ox g, ds, VCons (o ++ [val]) os, insertIntoWaiting ox set)
   | otherwise
   = fmap (\(g', a,b,c) -> (Out ox g', a, VCons o b, c))
               $ fire1 g ds os set

  fire1 (Trans ixs (Process s f) g) (VCons op ds) os (OSCons swaiting smax set)
   | trace ("Trans:" ++ show swaiting) True
   , trace ("Set:" ++ show set) True
   = let down s' f' = fmap (\(g', a,b,c) -> (Trans ixs (Process s' f') g', VCons op a, b, OSCons swaiting smax c))
                     $ fire1 g ds os set
         run  = case f s of
                 Get s' ix f'
                  -> case lookupOS (lookupIX ix ixs) set of
                     NotStarted
                      -> Nothing
                     Running _
                      | lookupWaiting (lookupIX ix ixs) set
                      , trace ("nothing to do") True
                      -> -- It's already waiting for new input from there, so cannot move
                         Nothing
                      | otherwise
                      , trace "pulling" True
                      , (val,_) <- takedrop1 (lookupIX ix ixs) ds
                      , f''     <- f' val
                      , set'    <- insertIntoWaiting (lookupIX ix ixs) set
                      -> Just (Trans ixs (Process s' f'') g, VCons op ds, os, OSCons swaiting smax set')
                     Finished
                      -> Just (Trans ixs (Process s' (f' Nothing)) g, VCons op ds, os, OSCons swaiting smax set)
                 Put s' v  f'
                  -> Just (Trans ixs (Process s' f') g, VCons [v] ds, os, OSCons (Running []) smax set)
                 Done
                  -- It's finished so all inputs can spin without worrying about this one being ready
                  | set' <- removeFromWaitMaxCount ixs set
                  -> Just (Trans ixs (Process s f) g, VCons op ds, os, OSCons Finished smax set)
     in
     case swaiting of
      NotStarted
       -> case run of
           Just blah -> Just blah
           Nothing   -> down s f
      Running sw
       | length sw == smax
       -> case run of
           Just blah -> Just blah
           Nothing   -> down s f
      _
       -> down s f

  all_finished _ = True

  lookupIX :: Index to x -> Indices from to -> Index from x
  lookupIX Here (ICons here _)
   = here
  lookupIX (There ix) (ICons _ there)
   = lookupIX ix there

  lookupOS :: Index xs x -> OutSet xs -> Status
  lookupOS Here (OSCons here _ _)
   = here
  lookupOS (There ix) (OSCons _ _ there)
   = lookupOS ix there

  lookupWaiting :: Index xs x -> OutSet xs -> Bool
  lookupWaiting ix os
   = lookupWaiting_go (natOfIx ix) ix os

  lookupWaiting_go :: Int -> Index xs x -> OutSet xs -> Bool
  lookupWaiting_go ix Here (OSCons (Running sw) _ _)
   = elem ix sw
  lookupWaiting_go ix Here other
   = True
  lookupWaiting_go ix (There there) (OSCons _ _ rest)
   = lookupWaiting_go ix there rest


  insertIntoWaiting :: Index xs x -> OutSet xs -> OutSet xs
  insertIntoWaiting ix os
   = insertIntoWaiting_go (natOfIx ix) ix os

  insertIntoWaiting_go :: Int -> Index xs x -> OutSet xs -> OutSet xs
  insertIntoWaiting_go ix Here (OSCons (Running sw) smax rest)
   = OSCons (Running (ix : sw)) smax rest
  insertIntoWaiting_go ix Here other
   = other
  insertIntoWaiting_go ix (There there) (OSCons sw smax rest)
   = OSCons sw smax (insertIntoWaiting_go ix there rest)

  removeFromWaitMaxCount :: Indices xs as -> OutSet xs -> OutSet xs
  removeFromWaitMaxCount INil os
   = os
  removeFromWaitMaxCount (ICons ix ixs) os
   = removeFromWaitMaxCount ixs (removeFromWaitMaxCount1 ix os)

  removeFromWaitMaxCount1 :: Index xs a -> OutSet xs -> OutSet xs
  removeFromWaitMaxCount1 Here (OSCons sw smax rest)
   = OSCons sw (smax-1) rest
  removeFromWaitMaxCount1 (There there) (OSCons sw smax rest)
   = OSCons sw smax $ removeFromWaitMaxCount1 there rest


valsOfIns :: Graph i d o -> Values i -> Values d
valsOfIns Empty ins
 = VNil
valsOfIns (Inp g') (VCons vs ins)
 = VCons vs (valsOfIns g' ins)
valsOfIns (Out _ g') ins
 = valsOfIns g' ins
valsOfIns (Trans _ _ g') ins
 = VCons [] (valsOfIns g' ins)

outsOfVals :: Graph i d o -> Values d -> Values o
outsOfVals Empty ds
 = VNil
outsOfVals (Inp g') (VCons _ ds)
 = outsOfVals g' ds
outsOfVals (Out ix g') ds
 = VCons (index ix ds) (outsOfVals g' ds)
outsOfVals (Trans _ _ g') (VCons _ ds)
 = outsOfVals g' ds


