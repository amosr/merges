{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, DataKinds, KindSignatures, RankNTypes #-}
module Lists where
import Data.Maybe (listToMaybe)

data Index :: [*] -> * -> * where
  Here :: Index (x ': xs) x
  There :: Index xs x -> Index (y ': xs) x

natOfIx :: Index xs x -> Int
natOfIx Here        = 0
natOfIx (There ix)  = natOfIx ix + 1

data Values :: [*] -> * where
    VNil  :: Values '[]
    VCons :: [a] -> Values as -> Values (a ': as)

data Indices :: [*] -> [*] -> * where
    INil  :: Indices from '[]
    ICons :: Index from a -> Indices from as -> Indices from (a ': as)



class VNils (xs :: [*]) where
    vnils :: Values xs
instance VNils '[] where
    vnils = VNil
instance VNils xs => VNils (x ': xs) where
    vnils = VCons [] vnils


class VShow (xs :: [*]) where
    vshow :: Values xs -> [[String]]
instance VShow '[] where
    vshow _ = []
instance (VShow xs, Show x) => VShow (x ': xs) where
    vshow (VCons vs rs) = map show vs : vshow rs



takedrop1 :: Index xs x -> Values xs -> (Maybe x, Values xs)
takedrop1 Here (VCons vs rs)
 = ( listToMaybe $ take 1 vs
   , VCons (drop 1 vs) rs )

takedrop1 (There ix) (VCons vs rs)
 = let (l, r)  = takedrop1 ix rs
   in  (l, VCons vs r)

takedrop1 _ VNil
 = error "Impossible!"

index :: Index xs x -> Values xs -> [x]
index Here (VCons vs _)
 = vs
index (There ix) (VCons _ rs)
 = index ix rs

index ix VNil
 = error "Impossible!"

push1 :: Index xs x -> x -> Values xs -> Values xs
push1 Here o (VCons vs rs)
 = VCons (vs ++ [o]) rs

push1 (There ix) o (VCons vs rs)
 = VCons vs (push1 ix o rs)

push1 _ _ VNil
 = error "Impossible!"


-- Set of indices into given list of types
-- The index value type is lost and cannot be recovered, but can be tested against.
type IndexSet (xs :: [*]) = [Int]

isSize :: IndexSet xs -> Int
isSize ls = length ls

isInsert :: IndexSet xs -> Index xs a -> IndexSet xs
isInsert ls ix
 | elem ix' ls
 = ls
 | otherwise
 = (ix' : ls)
 where
  ix' = natOfIx ix

isMember :: IndexSet xs -> Index xs a -> Bool
isMember ls ix
 = elem (natOfIx ix) ls

isEmpty :: IndexSet xs
isEmpty = []

