-- Invariant checking of machines
module Automata4Check where
import Automata4

import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad (when, forM_)


data CheckError l n
 = CheckNoSuchLabel l
 | CheckNoSuchSigma l
 | CheckPullWithoutRelease l n
 | CheckReleaseOfNonValue  l n
 | CheckCloseWithoutRelease l n
 | CheckFunArgsOfNonValue l [n]
 | CheckOutAlreadyFinished l n
 | CheckOutFinishedAlreadyFinished l n
 | CheckDoneNotFinished l (S.Set (Event n))
 | CheckNotMatching l (S.Set (Event n)) (S.Set (Event n))
 | CheckCyclic (S.Set n) (S.Set n)
 deriving Show



generate :: (Ord name, Ord l) => M.Map l (S.Set (Event name)) -> Machine l name fun -> l -> Sigma name fun -> Either (CheckError l name) (S.Set (Event name))
generate gamma m s l
 | Just es <- M.lookup s gamma
 , Just ty <- M.lookup s (_trans m)
 = case ty of
    Pull{}
     | SPullSome n  <- l
     -> return
      $ Value n     `S.insert` es
     | SPullNone n  <- l
     -> return
      $ Finished n  `S.insert` es
    Release n _
     -> return
      $ Value n     `S.delete` es
    Close n _
     -> return
      $ Closed n    `S.insert` es
    Update{}
     -> return
      $ es
    If{}
     -> return
      $ es
    Out f _
     -> return
      $ Value (_state f) `S.insert` es
    OutFinished n _
     -> return
      $ Finished n  `S.insert` es
    Skip{}
     -> return
      $ es

    _
     -> Left (CheckNoSuchSigma s)
 | otherwise
 = Left (CheckNoSuchLabel s)


check_state :: (Ord name, Ord l) => M.Map l (S.Set (Event name)) -> Machine l name fun -> l -> Either (CheckError l name) () 
check_state gamma m s
 | Just es <- M.lookup s gamma
 , Just ty <- M.lookup s (_trans m)
 = case ty of
    Pull n _ _
     |  not (Value n    `S.member` es)
     && not (Finished n `S.member` es)
     && not (Closed n   `S.member` es)
     -> return ()
     | otherwise
     -> Left (CheckPullWithoutRelease s n)

    Release n _
     |       Value n    `S.member` es
     -> return ()
     | otherwise
     -> Left (CheckReleaseOfNonValue s n)
    Close n _
     |  not (Value n    `S.member` es)
     && not (Finished n `S.member` es)
     && not (Closed n   `S.member` es)
     -> return ()
     | otherwise
     -> Left (CheckCloseWithoutRelease s n)

    Update f _
     |  all (`S.member` es) (fvs f)
     -> return ()
     | otherwise
     -> Left (CheckFunArgsOfNonValue s (_inputs f))
     
    If f _ _
     |  all (`S.member` es) (fvs f)
     -> return ()
     | otherwise
     -> Left (CheckFunArgsOfNonValue s (_inputs f))

    Out f _
     |  not (Finished (_state f) `S.member` es)
     -> return ()
     | otherwise
     -> Left (CheckOutAlreadyFinished s (_state f))

    OutFinished n _
     |  not (Finished n `S.member` es)
     -> return ()
     | otherwise
     -> Left (CheckOutFinishedAlreadyFinished s n)

    Skip{}
     -> return ()

    Done
     |  all (\n -> Finished n `S.member` es || Closed n `S.member` es)
            (S.toList $ uncurry S.union $ freevars m)
     -> return ()
     | otherwise
     -> Left (CheckDoneNotFinished s es)
 | otherwise
 = error "check_state: state not in event set or not in machine"

 where
  fvs f
   = map Value
   $ filter (/= _state f)
   $ _inputs f


closure :: (Ord name, Ord l) => M.Map l (S.Set (Event name)) -> Machine l name fun -> M.Map l (S.Set (Event name)) -> Either (CheckError l name) (M.Map l (S.Set (Event name)))
closure gamma m p
 = case M.minViewWithKey p of
    -- (Finished)
    Nothing
     -> return gamma

    Just ((s,b), p')
     | Just a <- M.lookup s gamma
     -> if   a == b
        -- (State already computed)
        then closure gamma m p'
        -- (Allow different output types)
        else let diff = S.difference a b
                 outs = snd (freevars m)
                 allo = all (`S.member` S.map Value outs)
                      $ S.toList diff
             in  if allo
                 then closure (M.delete s gamma) m (M.insert s (a `S.intersection` b) p')
                 else Left (CheckNotMatching s a b)
     -- (Compute transitions)
     | otherwise
     -> let gamma' = M.insert s b gamma
            
            get (lbl,sig)
             = do g' <- generate gamma' m s sig
                  return (lbl, g')
        in  do
                p'' <- mapM get
                    $ succs (_trans m M.! s)

                closure gamma' m (p' `M.union` M.fromList p'')



check_machine :: (Ord name, Ord l) => Machine l name fun -> Either (CheckError l name) (M.Map l (S.Set (Event name)))
check_machine m
 = do   when (not $ S.null $ uncurry S.intersection $ freevars m) $
            Left (uncurry CheckCyclic $ freevars m)
        gamma <- closure M.empty m (M.singleton (_init m) S.empty)
        forM_ (M.keys $ _trans m) (check_state gamma m)
        return gamma
        
   
