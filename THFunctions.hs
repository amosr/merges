{-# LANGUAGE TemplateHaskell #-}
module THFunctions where
import Automata4Coms

import Language.Haskell.TH

functions :: Functions Exp
functions
 = Functions
 { f_pair = v 'pair
 , f_fst  = v 'fst
 , f_snd  = v 'snd
 , f_id   = v 'id
 , f_onfst= \x -> v 'onfst `AppE` x
 , f_apsnd= \x -> v 'apsnd `AppE` x
 , f_eq   = v '(==)
 , f_le   = v '(<=)
 , f_lt   = v '(<)
 , f_pair0= v 'pair0
 , f_plus1= v 'plus1
 , f_fsts = \x -> v 'fsts `AppE` x
 , f_uncurry = \x -> v 'uncurry `AppE` x
 }
 where
  v = VarE

pair a b = (a,b)
onfst f (la,_)  (ra,_)  = f la ra
apsnd f (la,lb) (ra,rb) = (la, f lb rb)
pair0 b = (0,b)
plus1 a = a+1
fsts f (a,b) = (f a, b)

