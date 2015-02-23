{-# LANGUAGE TemplateHaskell #-}
import TH

foo :: Source Int -> Sink Int -> IO ()
foo from to =
 $$(comb [||let x  = Read from
                x' = Map (+1) x
                _  = When x' to
            in () ||])
