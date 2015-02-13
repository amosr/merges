{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Automata4QQ (auto
    , module Automata4Coms) where
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
        stns <- statenames
        decs <- mapM (mkfun lbls bufs stns) $ M.toList trans
        let init' = lbls M.! init
        uninit <- [|error "Uninitialised"|]
        return
         $ DoE ([LetS decs
               , NoBindS (app_args (const uninit) (VarE init') bufs stns) ])

 where

  mklbl (l,_)
   | Just ix <- M.lookupIndex l trans
   = do n' <- newName ("lbl" ++ show ix)
        return (l, n')
   | otherwise
   = error "Impossible: l must be in trans map"

  app_args foo f bufs stns
   = foldl AppE f
   $ map (foo . VarE . snd)
   ( M.toList bufs ++ M.toList stns )

  buffnames
   = let (ins,outs) = freevars m
         all        = S.union ins outs
     in  M.fromList <$> (mapM buffname $ S.toList all)
  buffname n
   = do n' <- newName (n ++ "_v")
        return (n, n')

  statenames
   = let (_,  outs) = freevars m
     in  M.fromList <$> (mapM statename $ S.toList outs)
  statename n
   = do n' <- newName (n ++ "_s")
        return (n, n')
     

  mkfun lbls bufs stns (l,t)
   = do t' <- mktrans lbls bufs stns t
        let args = map (VarP . snd) (M.toList bufs ++ M.toList stns) 
        return
          $ FunD (lbls M.! l)
            [ Clause args (NormalB t') [] ]

  mktrans lbls bufs stns t
   = case t of
      Pull from full empty
       | from' <- getFrom from
       , w <- bufs M.! from
       ->    [|do   o <- $(return $ VarE $ mkName from')
                    case o of
                     Just x'
                      -> do $(return $ VarP w) <- return x'
                            $(return $ app_args id (VarE $ lbls M.! full) bufs stns)
                     Nothing
                      -> $(return $ app_args id (VarE $ lbls M.! empty) bufs stns)|]

      Release _ goto
       -> return $ app_args id (VarE (lbls M.! goto)) bufs stns

      Update (Function f out ins) goto
       | sn <- stns M.! out
       -> do    let ins'      = reads bufs ins out stns
                let is = map (VarE) ins'
                let f' = foldl AppE (VarE $ mkName f) is
                r <- [|return $(return f')|]
                return
                 $ DoE ([ BindS (VarP sn) r
                       , NoBindS $ app_args id (VarE $ lbls M.! goto) bufs stns ] )

      If (Function f out ins) yes no
       -> do    let ins' = reads bufs ins out stns
                let is = map (VarE) ins'
                let f' = foldl AppE (VarE $ mkName f) is
                if_ <- [| case $(return f') of
                        True ->  $(return $ app_args id (VarE $ lbls M.! yes) bufs stns)
                        False -> $(return $ app_args id (VarE $ lbls M.! no ) bufs stns )
                        |]
                return
                 $ DoE ([NoBindS if_])

      Out (Function f out ins) goto
       | bn <- bufs M.! out
       -> do    let ins' = reads bufs ins out stns
                let is = map (VarE) ins'
                let f' = foldl AppE (VarE $ mkName f) is
                r <- [|return $(return f')|]
                let when = case getWhen out of
                         Nothing -> []
                         Just w' -> [ NoBindS ( VarE (mkName w') `AppE` VarE bn ) ]
                 
                return
                 $ DoE ([ BindS (VarP bn) r ]
                    ++ when
                    ++ [ NoBindS $ app_args id (VarE $ lbls M.! goto) bufs stns ] )

      OutFinished _ goto
       -> return $ app_args id (VarE (lbls M.! goto)) bufs stns
      Skip goto
       -> return $ app_args id (VarE (lbls M.! goto)) bufs stns
      Done
       -> [| return () |]

  reads bufs ins out stns
   = map (readfrom bufs out stns) ins
  readfrom bufs out stns i
   | i == out
   = stns M.! i
   | otherwise
   = bufs M.! i

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

