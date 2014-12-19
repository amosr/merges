-- | One input, one output
--
{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes #-}
module Nest1 where
import Stream       as Str
import Merge        as Mer
import qualified EMap as M

data Name a =
    Name (M.Key Int a)

data Op a where
    OpStream :: Stream a b s  -> Name a -> Op b
    OpMerge  :: Merge a b c s -> Name a -> Name b -> Op c

data MapList (k :: * -> *) :: [*] -> * where
    MNil  :: MapList k '[]
    MCons :: k a -> MapList k as -> MapList k (a ': as)

data Nest as bs
 = Nest
 { _ins  :: MapList Name as
 , _outs :: MapList Name bs
 , _ops  :: M.Map Int Op }


data StateOf a = forall s. StateOf s
data Const a b = Const a

run :: Nest is os -> MapList [] is -> MapList [] os
run nest inputs
 = go inputs inits
 where
  go inps ss
   = let vs      = takes nest inps
         (vs',ss',fws,done) = shake ops vs ss
         rets    = produces nest vs
         inps'   = drops fws  inps
     in  if   done
         then rets
         else rets `apps` go inps' ss 

  shake [] vs ss
   = (vs, ss, M.empty, False)

  shake (o:ops) vs ss
   = case o of
      OpStream str in1
       ->
      OpMerge mer in1 in2
       ->
   = ([], ss)


  ops = M.pairs $ _ops nest

  inits
   = M.mapWithKey
   (\k v -> case v of
        OpStream str _
         -> StateOf $ Str._init str
        OpMerge  mer _ _
         -> StateOf $ Mer._init mer)
   (_ops nest)


takes :: Nest is os -> MapList [] is -> M.Map Int []
takes nest lists
 = go lists (_ins nest)
 where
  go :: MapList [] iss -> MapList Name iss -> M.Map Int Maybe
  go (MCons i is) (MCons (Name n) ns)
   = M.insert n (take 1 i)
   $ go is ns

  go _ MNil = M.empty
  go MNil _ = M.empty


produces :: Nest is os -> M.Map Int [] -> MapList [] os
produces nest vals
 = go (_outs nest)
 where
  go :: MapList Name oss -> MapList [] oss
  go (MCons (Name n) ns)
   =        maybe [] id (M.lookup n vals)
   `MCons`  go ns

  go MNil = MNil

apps    :: MapList [] a -> MapList [] a -> MapList [] a
apps = zipWithT (++)

drops    :: MapList (Const Bool) a -> MapList [] a -> MapList [] a
drops = zipWithT (\(Const a) b -> if a then drop 1 b else b)

zipWithT :: (forall t. f t -> g t -> h t)
         -> MapList f ts
         -> MapList g ts
         -> MapList h ts
zipWithT _ MNil MNil
 = MNil
zipWithT f (MCons a as) (MCons b bs)
 = f a b `MCons` zipWithT f as bs

