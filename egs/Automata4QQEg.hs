{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Automata4QQEg where
import Automata4QQ
import Data.IORef

puller :: [a] -> IO (IO (Maybe a))
puller ls
 = do   ls' <- newIORef ls
        let pull
             = do   i <- readIORef ls'
                    case i of
                     [] -> return Nothing
                     (i:is)
                        -> writeIORef ls' is >> return (Just i)
        return pull

bobo :: IO ()
bobo
 = do   pull1 <- puller [1..10]
        pull2 <- puller [5..15]
        pull3 <- puller [5..15]
        pull4 <- puller [5..15]
        [auto|
            a = read pull1
            b = read pull2
            c = read pull3
            d = read pull4

            a' = map dup a
            b' = map dup b
            c' = map dup c
            d' = map dup d

            m1 = merge a' b'
            m2 = merge c' d'

            m3 = merge m1 m2
            when m3 out_merg
            |]
 where
  inc = (+5)
  gt1 = (>10)
  dup a = (a,a)


  out_filtd b = putStrLn ("filtd:" ++ show b) 
  out_merg b = putStrLn  ("merg: " ++ show b) 

