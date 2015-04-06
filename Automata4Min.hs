-- Minimisation of machines
module Automata4Min where
import Automata4

import qualified Data.Set as S
import qualified Data.Map as M

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

