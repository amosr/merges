module SortMerge where
import Data.List (sortBy)
import Data.Function (on)

merge :: (Num k, Ord k, Num v)
      => [(k,v)] -> [(k,v)]
      -> [(k,v)]
merge ls rs
 = let both   = ls ++ rs
       sorted = sortBy (compare `on` fst) both

        -- I think a segmented fold would be better here
       fsum   = \(p1,p2) (c1,c2) -> if p1 == c1
                                    then (p1, p2+c2)
                                    else (c1, c2)
       sums   = drop 1
              $ scanl fsum (0,0) sorted

       fsame  = \(pf,(p1,p2)) (c1,c2) -> if p1 == c1
                                         then (False,(c1,c2))
                                         else (True,(c1,c2))
       scans  = reverse
              $ drop 1
              $ scanl fsame (False,(0,0))
              $ reverse sums

       filts  = filter fst scans

       vals   = map snd filts

   in  vals

