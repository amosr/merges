{-# LANGUAGE ExistentialQuantification, KindSignatures, RankNTypes #-}
module EMap where
import Unsafe.Coerce
import qualified Data.Map as M
import Control.Applicative

type Id a = a

data Key k a
 = Key k
 deriving (Eq,Ord)

data Ex1 (v :: * -> *)
 = forall a.
 Ex1 (v a)

data Ex2 (k :: * -> *) (v :: * -> *)
 = forall a.
 Ex2 (k a) (v a)


data Map k (v :: * -> *)
 = Map (M.Map k (Ex1 v))

empty :: Map k v
empty = Map M.empty

insert  :: Ord k
        => Key k a -> v a -> Map k v -> Map k v
insert (Key k) v (Map m)
 = Map
 $ M.insert k (Ex1 v) m

lookup  :: Ord k
        => Key k a -> Map k v -> Maybe (v a)
lookup (Key k) (Map m)
 = unsafeCoerce <$> M.lookup k m

pairs :: Map k v -> [Ex2 (Key k) v]
pairs (Map m)
 = map (\(k,Ex1 v) -> Ex2 (Key k) v)
 $ M.toList m


mapWithKey :: Ord k
    => (forall a. Key k a -> v a -> v' a)
    -> Map k v
    -> Map k v'
mapWithKey f (Map m)
 = Map
 $ M.mapWithKey
 (\k (Ex1 v) -> Ex1 (f (Key k) v))
   m

