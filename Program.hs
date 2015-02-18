{-# LANGUAGE GADTs, ExistentialQuantification #-}
module Program where

data Source a
 = forall s. Source s (s -> IO (Maybe a, s))

data Comb a where
 Read    :: Source a -> Comb a
 Map     :: (a->b)    -> Comb a -> Comb b
 Zip     :: Comb a    -> Comb b -> Comb c
 Filter  :: (a->Bool) -> Comb a -> Comb a
 Append  :: Comb a    -> Comb a -> Comb a
 Merge   :: Comb (Int,a) -> Comb (Int,a) -> Comb (Int,a)
 Indices :: Comb Int -> Comb Int
 GroupBy :: Eq eq => (a -> a -> a) -> Comb (eq,a) -> Comb (eq,a)


data Sink a
 = forall s. Sink s (s -> Maybe a -> IO s)

data When a
 = When (Comb a) (Sink a)

