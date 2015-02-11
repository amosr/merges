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
        [auto|
            a = read pull1
            b = read pull2

            incd = map inc a
            filtd = filter gt1 incd

            ff = map dup filtd
            bb = map dup b      # self-zips don't work

            merg = merge ff  bb

            vals = map snd merg
            ix = indices vals

            when ix out_filtd
            when merg  out_merg
            |]
 where
  inc = (+5)
  gt1 = (>10)
  dup a = (a,a)


  out_filtd b = putStrLn ("filtd:" ++ show b) 
  out_merg b = putStrLn  ("merg: " ++ show b) 

