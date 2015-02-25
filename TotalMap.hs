{-# LANGUAGE EmptyDataDecls, EmptyCase, RankNTypes, MultiParamTypeClasses, FlexibleInstances #-}
module TotalMap where
import qualified Prelude as P
import Prelude hiding (lookup)

class Inj a b where
 inj :: a -> b

instance Inj a a where
 inj = id

instance Inj a (Either a b) where
 inj = Left

instance Inj a (Either b a) where
 inj = Right


data Map k v = Map (k -> v)

data Void 

empty :: Map Void v
empty = Map (\v -> case v of)

lookup :: Inj k' k => Map k v -> k' -> v
lookup (Map kvs) k
 = kvs (inj k)

singleton :: v -> (forall k. k -> Map k v -> res) -> res
singleton v co
 = co () (Map (const v))

union :: Map k v -> Map k' v -> Map (Either k k') v -- (forall k''. (Inj k k'', Inj k' k'') => Map k'' v -> res) -> res
union (Map kvs) (Map kvs')
 = let kv' k = case k of
                Left k' -> kvs k'
                Right k' -> kvs' k'
   in Map kv'


{-
insert :: Eq k => Map k v -> v -> (forall k'. Eq k' => k' -> (k -> k') -> Map k' v -> res) -> res
insert (Map kvs) v c
 = let kvs'  = map (\(k,v) -> (Right k, v)) kvs
       kvs'' = (Left (), v) : kvs'
   in c (Left ()) Right (Map kvs'')
-}

