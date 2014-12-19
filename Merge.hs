module Merge where

data Move
 = L | R | LR

data Merge a b c s
 = Merge
 { _init    :: s
 , _move    :: a -> b -> s -> Move
 , _emit    :: a -> b -> s -> (Maybe c, s)
 -- | Right side has finished, but there remain some on left
 , _remainL :: a ->      s -> (Maybe c, s)
 -- | Left side has finished, but there remain some on right
 , _remainR ::      b -> s -> (Maybe c, s)
 -- | Both sides finished
 , _finish  ::           s ->  Maybe c
 }


-- | Simple zip
zip :: Merge a b (a,b) ()
zip
 = Merge
 { _init    = ()
 , _move    = \a b s -> LR
 , _emit    = \a b s -> (Just (a,b), s)
 , _remainL = \a   s -> (Nothing,    s)
 , _remainR = \  b s -> (Nothing,    s)
 , _finish  = \    s ->  Nothing
 }


-- | Sparse vector add
sv_plus :: (Ord k, Num v)
        => Merge (k,v) (k,v) (k,v) ()
sv_plus
 = Merge
 { _init    = ()
 , _move    = \a b s ->
                    if      fst a == fst b
                    then        LR
                    else if fst a <  fst b
                    then        L
                    else -- fst b <  fst a
                                 R
 , _emit    = \a b s ->
                    if      fst a == fst b
                    then        (Just (fst a, snd a + snd b), s)
                    else if fst a <  fst b
                    then        (Just (fst a, snd a), s)
                    else -- fst b <  fst a
                                (Just (fst b, snd b), s)
 , _remainL = \a   s -> (Just (fst a, snd a), s)
 , _remainR = \  b s -> (Just (fst b, snd b), s)
 , _finish  = \    s ->  Nothing
 }

-- | Inner merge join
merjoin :: (Ord k)
        => Merge (k,a) (k,b) (k,(a,b)) ()
merjoin
 = Merge
 { _init    = ()
 , _move    = \a b s ->
                    if      fst a == fst b
                    then        LR
                    else if fst a <  fst b
                    then        L
                    else -- fst b <  fst a
                                 R
 , _emit    = \a b s ->
                    if      fst a == fst b
                    then        (Just (fst a, (snd a, snd b)), s)
                    else
                                (Nothing, s)
 , _remainL = \a   s -> (Nothing, s)
 , _remainR = \  b s -> (Nothing, s)
 , _finish  = \    s ->  Nothing
 }


-- | Append
append  :: Merge a a a ()
append
 = Merge
 { _init    = ()
 , _move    = \a b s -> L
 , _emit    = \a b s -> (Just a, s)
 , _remainL = \a   s -> (Just a, s)
 , _remainR = \  b s -> (Just b, s)
 , _finish  = \    s ->  Nothing
 }

-- | Indices of a segmented array
-- need the data array too just so we have something to iterate over
--
-- indices = segscan (\a b -> a+1) (-1)
--
indices :: Merge Int a Int (Int,Int)
indices
 = Merge
 { _init    = (0,0)
 , _move    = \a b s ->
                    if fst s == snd s
                    then L
                    else  R
 , _emit    = \a b s ->
                    if fst s == snd s
                    then (Nothing, (0, a))
                    else (Just (fst s), (fst s + 1, snd s))
 , _remainL = \a   s -> (Nothing, s) -- No way
 , _remainR = \  b s -> (Just (fst s), (fst s + 1, snd s)) -- Only for last segment
 , _finish  = \    s ->  Nothing
 }

-- | Segmented scan
segscan :: (a -> a -> a) -> a -> Merge Int a a (a,Int)
segscan f k
 = Merge
 { _init    = (k,0)
 , _move    = \a b s ->
                    if snd s == 0
                    then L
                    else  R
 , _emit    = \a b s ->
                    if snd s == 0
                    then (Nothing, (k, a))
                    else (Just (f (fst s) b), (f (fst s) b, snd s - 1))
 , _remainL = \a   s -> (Nothing, s) -- No way
 , _remainR = \  b s ->
                    if snd s == 0
                    then (Nothing, (k,0))
                    else (Just (f (fst s) b), (f (fst s) b, snd s - 1)) -- Only for last segment
 , _finish  = \    s ->  Nothing
 }

-- | Segmented fold
segfold :: (a -> a -> a) -> a -> Merge Int a a (a,Int,Bool)
segfold f k
 = Merge
 { _init    = (k,0,False)
 , _move    = \a b (_,s2,_) ->
                    if s2 == 0
                    then L
                    else  R
 , _emit    = \a b (s1,s2,s3) ->
                    if s2 == 0 && s3
                    then (Just s1, (k, a, True))
                    else if not s3
                    then (Nothing, (k, a, True))
                    else (Nothing, (f s1 b, s2 - 1, True))
 , _remainL = \a   s -> (Nothing, s) -- No way
 , _remainR = \  b (s1,s2,_) ->
                    if s2 == 0
                    then (Nothing, (s1,s2,True))
                    else (Nothing, (f s1 b, s2 - 1, True)) -- Only for last segment
 , _finish  = \    (s1,_,_) ->  Just s1
 }

-- | Segment ids
-- > segnums [1,2,3] [x,x,x,x,x,x,x]
-- = [0, 1, 1, 2, 2, 2]
segnums :: Merge Int a Int (Int,Int)
segnums
 = Merge
 { _init    = (-1,0)
 , _move    = \a b s ->
                    if snd s == 0
                    then L
                    else  R
 , _emit    = \a b s ->
                    if snd s == 0
                    then (Nothing, (fst s + 1, a))
                    else (Just (fst s), (fst s, snd s - 1))
 , _remainL = \a   s -> (Nothing, s)
 , _remainR = \  b s ->
                    if snd s == 0
                    then (Nothing, s)
                    else (Just (fst s), (fst s, snd s - 1))
 , _finish  = \    s ->  Nothing
 }


-- > merge [(1,a), (1, b), (3, c)] [(1,z), (2, f)]
-- = [(1,a), (1,b), (1,z), (2,f), (3,c)]
merge :: Ord k
            => Merge (k,v) (k,v) (k,v) () 
merge
 = Merge
 { _init    = ()
 , _move    = \a b s ->
                    if      fst a <= fst b
                    then        L
                    else -- fst a >  fst b
                                 R
 , _emit    = \a b s ->
                    if      fst a <= fst b
                    then    (Just a, s)
                    else -- fst a >  fst b
                            (Just b, s)
 , _remainL = \a   s ->     (Just a, s)
 , _remainR = \  b s ->     (Just b, s)
 , _finish  = \    s ->      Nothing
 }




eval :: Merge a b c s -> [a] -> [b] -> [c]
eval m as bs
 = go (_init m) as bs
 where
  go s [] []
   = cons (_finish m s) []

  go s (a:as) (b:bs)
   = let (val,s') = _emit m a b s
         (as',bs')= move a b s (a:as) (b:bs) 
     in cons val (go s' as' bs')

  go s (a:as) []
   = let (val,s') = _remainL m a s
     in cons val (go s' as [])

  go s [] (b:bs)
   = let (val,s') = _remainR m b s
     in cons val (go s' [] bs)


  move a b s as bs
   = case _move m a b s of
      L  -> (drop 1 as, bs)
      R  -> (as, drop 1 bs)
      LR -> (drop 1 as, drop 1 bs)


  cons Nothing  ls
   = ls
  cons (Just l) ls
   = l : ls
  

test1 = [(1,3), (2,5)]
test2 = [(2,1), (3,5)]
-- > eval sv_plus test1 test2
-- [(1,3),(2,6),(3,5)]

