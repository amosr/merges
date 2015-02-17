{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Main where

set_xor :: IO ()
set_xor
 = do   f1 <- readFile "nums1.txt"
        f2 <- readFile "nums2.txt"
        mapM_ print (xor f1 f2)
 where
  xor f1 f2
   = let a' = map read $ lines f1
         b' = map read $ lines f2

         aa = zip a' a'
         bb = zip b' b'

         merg = merge aa bb
         ones = map (\(a,_) -> (a, 1)) merg

         counts = group_by_fst (+) ones
         xors = filter ((==1).snd) counts
      in map fst xors

merge :: [(Int,a)] -> [(Int,a)] -> [(Int,a)]
merge as bs
 = go as bs
 where
  go (a:as) (b:bs)
   | fst a <= fst b
   = a : go as (b:bs)
   | otherwise
   = b : go (a:as) bs

  go as []
   = as
  go [] bs
   = bs

group_by_fst :: Eq i => (a -> a -> a) -> [(i,a)] -> [(i,a)]
group_by_fst f as
 = go1 as
 where
  go1 []
   = []
  go1 (a:as)
   = go2 a as

  go2 s []
   = [s]
  go2 s (a:as)
   | fst s == fst a
   = go2 (fst s, snd s `f` snd a) as
   | otherwise
   = s : go2 a as

main = set_xor
