{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Main where
import Automata4QQ
import Data.IORef

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
 = do   pull1 <- pull_file "nums1.txt"
        pull2 <- pull_file "nums2.txt"
        [auto|
            a = read pull1
            b = read pull2

            a' = map read a
            b' = map read b

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
  inc = (+5)
  gt1 = (>10)
  dup a = (a,a)
  const1 (a,_) = (a, one_i)

  plus_snd (a,b) (_,b')
   = (a, b + b')

  snd_eq_1 = (==one_i) . snd

  one_i = 1 :: Int


  out b = putStrLn  ("xor: " ++ show b) 


main = set_xor
