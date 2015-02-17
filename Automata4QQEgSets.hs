{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Main where
import Automata4QQ
import Data.IORef
import qualified Data.Vector as V

buffer :: IO (Maybe a) -> IO (IO (Maybe a))
buffer act
 = do   v  <- gen
        v' <- newIORef v
        i' <- newIORef 0
        let pull
             = do   i <- readIORef i'
                    v <- readIORef v'
                    case i >= size of
                     True
                      -> do v  <- gen
                            writeIORef i' 1
                            writeIORef v' v
                            return (v `V.unsafeIndex` 0)
                     False
                      -> do writeIORef i' (i + 1)
                            return (v `V.unsafeIndex` i)
        return pull
 where
  size = 1000
  gen  = V.generateM size (const act) 
        

pull_file :: String -> IO (IO (Maybe String))
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

set_xor :: IO ()
set_xor
 = do   pull1  <- pull_file "nums1.txt"
        pull2  <- pull_file "nums2.txt"
        [auto|
            a = read pull1
            b = read pull2

            a' = map readI a
            b' = map readI b

            aa = map dup a'
            bb = map dup b'
            merg = merge aa bb

            ones = map const1 merg
            
            counts = group_by plus_snd ones

            xor = filter snd_eq_1 counts
            xor' = map fst xor

            when xor'  out
            |]
 where
  dup a = (a,a)
  {-# INLINE dup #-}
  const1 (a,_) = (a, one_i)
  {-# INLINE const1 #-}

  readI :: String -> Int
  readI = read
  {-# INLINE readI #-}

  plus_snd (a,b) (_,b')
   = (a, b + b')
  {-# INLINE plus_snd #-}

  snd_eq_1 = (==one_i) . snd
  {-# INLINE snd_eq_1 #-}

  one_i = 1 :: Int
  {-# INLINE one_i #-}


  out :: Int -> IO ()
  out b = putStrLn  ("xor: " ++ show b) 
  {-# INLINE out #-}

main = set_xor



{-

a <- pull1 or A_EMPTY
b <- pull1 or B_EMPTY

aa = dup $ read a
bb = dup $ read a



A_EMPTY:
B_EMPTY:

-}
