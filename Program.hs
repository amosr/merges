{-# LANGUAGE GADTs, ExistentialQuantification #-}
module Program where
import Data.IORef

-- TODO: move to explicit state
-- (s, s -> IO (Maybe a))
type Source a
 = (IO (Maybe a))

data Comb a where
 Read    :: Source a -> Comb a
 Map     :: (a->b)    -> Comb a -> Comb b
 Zip     :: Comb a    -> Comb b -> Comb c
 Filter  :: (a->Bool) -> Comb a -> Comb a
 Append  :: Comb a    -> Comb a -> Comb a
 Merge   :: Comb (Int,a) -> Comb (Int,a) -> Comb (Int,a)
 Indices :: Comb Int -> Comb Int
 GroupBy :: Eq eq => (a -> a -> a) -> Comb (eq,a) -> Comb (eq,a)


type Sink a
 = (a -> IO ())

data When a
 = When (Comb a) (Sink a)


pull_file :: String -> IO (Source String)
pull_file nm
 = do   file <- readFile nm
        ls' <- newIORef (lines file)
        let pull
             = do   i <- readIORef ls'
                    case i of
                     [] -> return Nothing
                     (i:is)
                        -> writeIORef ls' is >> return (Just i)
        return pull

