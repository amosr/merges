{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Automata4QQ (auto) where
import Automata4
import Automata4Coms
import Automata4Prog
import Automata4QQParse

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import Control.Applicative

import qualified Data.Map as M
import qualified Data.Set as S

import Data.IORef

auto :: QuasiQuoter
auto
 = QuasiQuoter
 { quoteExp = auto_exp
 }

auto_exp :: String -> Q Exp
auto_exp str
 = case parse str of
    Just stmts
     | ms <- machinesOfParse stmts
     -> case fuse_all ms of
         Nothing
          -> error "can't fuse these together"
         Just m
          -> generate m stmts
    Nothing-> error "bad parse"

generate :: Machine' String -> [AStmt] -> Q Exp
generate (Machine' m) stmts
 = do   lbls <- M.fromList <$> (mapM mklbl $ M.toList trans)
        bufs <- buffnames
        ios  <- mkbuffs bufs
        decs <- mapM (mkfun lbls bufs) $ M.toList trans
        let init' = lbls M.! init
        return
         $ DoE (ios
            ++ [LetS decs
               , NoBindS (VarE init') ])

 where

  mklbl (l,_)
   | Just ix <- M.lookupIndex l trans
   = do n' <- newName ("lbl" ++ show ix)
        return (l, n')
   | otherwise
   = error "Impossible: l must be in trans map"

  buffnames
   = let (ins,outs) = freevars m
         all        = S.union ins outs
     in  M.fromList <$> (mapM buffname $ S.toList all)
  buffname n
   = do n' <- newName (n ++ "_v")
        return (n, n')

  mkbuffs bufs
   = mapM mkbuff $ M.toList bufs
  mkbuff (_,n')
   = do io <- [|newIORef (error "Uninitialised")|]
        return $ BindS (VarP n') io
     

  args = []

  mkfun lbls bufs (l,t)
   = do t' <- mktrans lbls bufs t
        return
          $ FunD (lbls M.! l)
            [ Clause args (NormalB t') [] ]

  mktrans lbls bufs t
   = case t of
      Pull from full empty
       | from' <- getFrom from
       , w <- VarE (bufs M.! from)
       ->    [|do   x <- $(return $ VarE $ mkName from')
                    case x of
                     Just x'
                      -> do writeIORef $(return w) x'
                            $(return $ VarE $ lbls M.! full)
                     Nothing
                      -> $(return $ VarE $ lbls M.! empty)|]

      Release _ goto
       -> return $ VarE (lbls M.! goto)

      -- todo
      Update _ goto
       -> return $ VarE (lbls M.! goto)
      If (Function f out ins) yes no
       -> do    (ins',rs) <- reads bufs ins
                let is = map (VarE) ins'
                let f' = foldl AppE (VarE $ mkName f) is
                if_ <- [| case $(return f') of
                        True ->  $(return $ VarE $ lbls M.! yes)
                        False -> $(return $ VarE $ lbls M.! no)
                        |]
                return
                 $ DoE (rs
                     ++ [NoBindS if_])

      Out (Function f out ins) goto
       -> do    (ins',rs) <- reads bufs ins
                o <- newName out
                let is = map (VarE) ins'
                let f' = foldl AppE (VarE $ mkName f) is
                writeo <- [|writeIORef|]
                let when = case getWhen out of
                         Nothing -> []
                         Just w' -> [ NoBindS ( VarE (mkName w') `AppE` VarE o ) ]
                 
                return
                 $ DoE (rs
                    ++ [ LetS [ ValD (VarP o) (NormalB f') [] ]
                       , NoBindS (writeo `AppE` (VarE (bufs M.! out))`AppE` (VarE o)) ]
                    ++ when
                    ++ [ NoBindS $ VarE $ lbls M.! goto ] )

      OutFinished _ goto
       -> return $ VarE (lbls M.! goto)
      Skip goto
       -> return $ VarE (lbls M.! goto)
      Done
       -> [| return () |]

  reads bufs ins
   = unzip <$> mapM (read1 bufs) ins

  read1 bufs i
   = do i' <- newName i
        r  <- [|readIORef $(return $ VarE $ bufs M.! i)|]
        return (i', BindS (VarP i') r )

  trans = _trans m
  init  = _init m

  getFrom from
   = getFrom' from stmts
  getFrom' from []
   = from
  getFrom' from (s : rest)
   | SRead f f2 <- s
   , f == from
   = f2
   | otherwise
   = getFrom' from rest

  getWhen from
   = getWhen' from stmts
  getWhen' from []
   = Nothing
  getWhen' from (s : rest)
   | SWhen f f2 <- s
   , f == from
   = Just f2
   | otherwise
   = getWhen' from rest

