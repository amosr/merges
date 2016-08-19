{-# LANGUAGE TemplateHaskell #-}
module TH(comb, module Program) where
import Program
import Automata4
import Automata4Coms
import Automata4Prog
import THFunctions
import THGen
import Control.Applicative

import qualified Data.Map as M

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (unsafeTExpCoerce)
import Debug.Trace

data Decl nm
 = DWhen   nm Exp
 | DSource Exp
 | DMach (Machine' nm Exp)

dmach :: (Ord s, Show s) => Machine s n Exp -> Decl n
dmach = DMach . Machine'

comb :: Q (TExp ()) -> Q (TExp (IO ()))
comb exp
 = do   u <- [|()|]
        exp' <- unType <$> exp
        
        case exp' of
           LetE decs xx
            | xx == u
            -> do ds <- concat <$> mapM get_dec decs
                  let ms  = machines_of_decs ds
                      m   = fuse_all ms
                      sms = source_sink_map ds
                  case m of
                   Left e
                    -> err e
                   Right m'
                    ->  unsafeTExpCoerce (generate m' sms)

            -- xx isn't a unit
            | otherwise
            -> err "the 'in' of the lets must be ()"
           _
            -> err "not lets"

 where

  get_dec (ValD (VarP b) (NormalB x) [])
   | [ConE w, comb, sink] <- takeApps x
   , w == 'When
   = do (cs,cn) <- nested' b comb
        nn <- newName (show b)
        return (cs ++ [(nn, DWhen cn sink)])

   | otherwise
   = fst <$> nested'start b x

  get_dec (ValD WildP (NormalB x) [])
   | [ConE w, comb, sink] <- takeApps x
   , w == 'When
   = do (cs,cn) <- nested' (mkName "when_") comb
        nn <- newName "when_"
        return (cs ++ [(nn, DWhen cn sink)])

  get_dec _
   = error "let bindings can only be Whens or Combs"

  machines_of_decs = concatMap get_mach
  get_mach (_, DMach m) = [m]
  get_mach _ = []

  source_sink_map = M.fromList . concatMap get_source_sink
  get_source_sink (b, DSource x) = [(b,x)]
  get_source_sink (_, DWhen b x) = [(b,x)]
  get_source_sink _              = []

  nested'      = nested True
  nested'start = nested False

  nested l b x
   | [ConE c, source] <- takeApps x
   , c == 'Read
   = named' (DSource source) []

   | [ConE c, f, inp] <- takeApps x
   , c == 'Map
   = do (rs,inp') <- nested' b inp
        named (dmach . map_a functions f inp') rs

   | [ConE c, in1, in2] <- takeApps x
   , c == 'Zip
   = do (rs ,in1') <- nested' b in1
        (rs',in2') <- nested' b in2
        named (dmach . zip_a functions in1' in2') (rs ++ rs')

   | [ConE c, f, in1] <- takeApps x
   , c == 'Filter
   = do (rs ,in1') <- nested' b in1
        named (dmach . filter_a functions f in1') rs

   | [ConE c, in1, in2] <- takeApps x
   , c == 'Append
   = do (rs ,in1') <- nested' b in1
        (rs',in2') <- nested' b in2
        named (dmach . append_a functions in1' in2') (rs ++ rs')

   | [ConE c, in1, in2] <- takeApps x
   , c == 'Merge
   = do (rs ,in1') <- nested' b in1
        (rs',in2') <- nested' b in2
        named (dmach . merge_a functions in1' in2') (rs ++ rs')

   | [ConE c, in1] <- takeApps x
   , c == 'Indices
   = do (rs ,in1') <- nested' b in1
        named (dmach . indices_a functions in1') rs

   | [ConE c, f, in1] <- takeApps x
   , c == 'GroupBy
   = do (rs ,in1') <- nested' b in1
        named (dmach . group_by_a functions f in1') rs

   | [ConE c, in1] <- takeApps x
   , c == 'Count
   = do (rs ,in1') <- nested' b in1
        named (dmach . count_a functions in1') rs



   | VarE n <- x
   = return ([], n)

   where
    nm = if l then newName (show b) else return b

    named' r rs = named (const r) rs
    named r rs
     = do   b' <- nm
            return ((b', r b') : rs, b')


  takeApps (AppE a b)
   = takeApps a ++ [b]
  takeApps f
   = [f]

  err x =
   error ("Error: " ++ x ++ "\nUsage: $(comb [| let... B :: When|Comb in () |])")
