module Automata4Coms where
import Automata4
import qualified Data.Map as M
import Debug.Trace

-- | THE FUNCTIONS WE NEED
data Functions f
 = Functions
 -- | a -> b -> (a,b)
 -- pair a b = (a,b)
 { f_pair  :: f
 -- (a,b) -> a
 -- fst (a,b) = a
 , f_fst   :: f
 -- (a,b) -> b
 -- snd (a,b) = b
 , f_snd   :: f
 -- a -> a
 -- id a = a
 , f_id    :: f
 -- (a -> a -> c) -> (a,b) -> (a,b) -> c
 --onfst f (la,_) (ra,_) = f la ra
 , f_onfst :: f -> f
 -- (b -> b -> c) -> (a,b) -> (a,b) -> (a,b)
 -- apsnd f (la,lb) (ra,rb) = (la, f lb rb)
 -- (should only be called if la and rb same or something)
 , f_apsnd :: f -> f
 , f_eq    :: f -- Int -> Int -> Bool
 , f_le    :: f -- Int -> Int -> Bool
 , f_lt    :: f -- Int -> Int -> Bool
 , f_pair0 :: f -- b -> (Int,b)
 , f_plus1 :: f -- Int -> Int
 , f_fsts  :: f -> f -- (a -> c) -> (a,b) -> (c,b)
 , f_uncurry :: f -> f -- (a -> b -> c) -> (a,b) -> c
 , f_constI :: Int -> f -- Int
 }

functions_string :: Functions String
functions_string
 = Functions
 { f_pair = "pair"
 , f_fst  = "fst"
 , f_snd  = "snd"
 , f_id   = "id"
 , f_onfst= ("fst "++)
 , f_apsnd= ("snd "++)
 , f_eq   = "=="
 , f_le   = "<="
 , f_lt   = "<"
 , f_pair0= "pair0"
 , f_plus1= "(+1)"
 , f_fsts = ("fsts "++)
 , f_uncurry = ("uncurry "++)
 , f_constI = \i -> show i
 }


empty_a :: Machine Int n f
empty_a
 = Machine
 { _init = 0
 , _trans = M.fromList [(0, Done)]
 }

-- | Zip two inputs together.
-- 1. Pull from both.
-- 2. Output.
-- 3. Release both.
--    Goto 1.
zip_a :: Functions f -> n -> n -> n -> Machine Int n f
zip_a f ina inb out
 = Machine
 { _init = 0
 , _trans = M.fromList
 $ [ (0, Pull ina 1 998)
   , (1, Pull inb 2 990)
   , (2, Out  (Function (f_pair f) out [ina,inb]) 3)
   , (3, Release ina 4)
   , (4, Release inb 0)

   , (990, Release ina 997)
   , (997, Close ina 999)
   , (998, Close inb 999)
   , (999, OutFinished out 1000)
   , (1000, Done) ]
 }

-- | Append two inputs
append_a :: Functions f -> n -> n -> n -> Machine Int n f
append_a f ina inb out
 = Machine
 { _init = 0
 , _trans = M.fromList
 $ [ (0, Pull ina                     1 10)
   , (1, Out  (Function (f_id f) out [ina]) 2)
   , (2, Release ina                  0)

   , (10, Pull inb                    11 999)
   , (11, Out  (Function (f_id f) out [inb]) 12)
   , (12, Release inb                 10)

   , (999, OutFinished out 1000)
   , (1000, Done) ]
 }


merge_a :: Functions f -> n -> n -> n -> Machine Int n f
merge_a f ina inb out
 = Machine
 { _init = 0
 , _trans = M.fromList
     [ (0, Pull ina         1 100)
     -- [Value a]
     , (1, Pull inb         2 200)
     -- [Value a, Value b]
     , (2, If (Function (f_onfst f (f_le f)) out [ina,inb]) 10 20)

     -- [Value a, Value b, a <= b]
     , (10, Out (Function (f_id f) out [ina]) 11)
     , (11, Release ina                     12)
     -- [Value b]
     , (12, Pull ina                2       101)

     -- [Value a, Value b, b < a]
     , (20, Out (Function (f_id f) out [inb]) 21)
     , (21, Release inb                     22)
     -- [Value a]
     , (22, Pull inb                2       200)


     -- [Empty a] suck from b
     , (100, Pull inb       101 900)
     -- [Empty a, Value b]
     , (101, Out (Function (f_id f) out [inb]) 102)
     , (102, Release inb    100)

     -- [Value a, Empty b] suck from a
     , (200, Out (Function (f_id f) out [ina]) 201)
     , (201, Release ina                     202)
     , (202, Pull    ina          200        900)

     -- [Empty a, Empty b]
     , (900, OutFinished out 901)
     , (901, Done)
     ]
 }


filter_a :: Functions f -> f -> n -> n -> Machine Int n f
filter_a f pred inp out
 = Machine
 { _init = 0
 , _trans = M.fromList
    [ (0, Pull inp  1   900)
    -- [Value inp]
    , (1, If (Function pred out [inp]) 10 11)
    
    -- [Value inp, pred inp]
    , (10, Out (Function (f_id f) out [inp]) 11)
    -- [Value inp]
    , (11, Release inp 0)

    -- [Empty inp]
    , (900, OutFinished out 901)
    , (901, Done)
    ]
 }

map_a :: Functions f -> f -> n -> n -> Machine Int n f
map_a f fun inp out
 = Machine
 { _init = 0
 , _trans = M.fromList
    [ (0, Pull inp 1 900)
    -- [Value inp]
    , (1, Out (Function fun out [inp]) 2)
    -- [Value inp]
    , (2, Release inp 0)

    -- [Empty inp]
    , (900, OutFinished out 901)
    , (901, Done)
    ]
 }

indices_a :: Functions f -> n -> n -> Machine Int n f
indices_a f inp out
 = Machine
 { _init = 0
 , _trans = M.fromList
    [ (0, Pull inp 1 900)
    , (1, Update (Function (f_pair0 f) out [inp]) 3)
    , (3, Release inp 4)

    , (4, Out (Function (f_fst f) out [out]) 5)
    , (5, Update (Function (f_fsts f (f_plus1 f)) out [out]) 6)
    , (6, If (Function (f_uncurry f (f_lt f))  out [out]) 4 0)

    , (900, OutFinished out 901)
    , (901, Done) ]
 }


-- Group by, kind of like a segmented fold.
-- Consecutive runs with the same first element are collected together with the worker function.
--
-- actually, because of stupid, the worker function should be
--  ((Int,a) -> (Int,a) -> (Int,a))
-- but should leave the first alone..
-- 
-- group_by :: (a -> a -> a) -> [(Int,a)] -> [(Int, a)]
group_by_a :: Functions f -> f -> n -> n -> Machine Int n f
group_by_a f fun inp out
 = Machine
 { _init = 0
 , _trans = M.fromList
    [ (0, Pull inp 1 40)
    , (1, Update (Function (f_id f) out [inp]) 2)
    , (2, Release inp 3)
    , (3, Pull inp 4 30)

    , (4, If (Function (f_onfst f (f_eq f)) out [out, inp]) 10 20)

    , (10,Update (Function (f_apsnd f fun) out [out,inp]) 2)

    , (20, Out (Function (f_id f) out [out]) 1)


    , (30, Out (Function (f_id f) out [out]) 40)
    , (40, OutFinished out 50)
    , (50, Done)
    ]
 }



-- Count a single thing
-- This is kind of silly, but ok
--
-- count :: [a] -> [Int]
count_a :: Functions f -> n -> n -> Machine Int n f
count_a f inp out
 = Machine
 { _init = 0
 , _trans = M.fromList
    [ (0, Update (Function (f_constI f 0) out []) 1)
    , (1, Pull inp 2 900)
    , (2, Update (Function (f_plus1 f) out [out]) 3)
    , (3, Release inp 1)

    , (900, Out (Function (f_id f) out [out]) 901)
    , (901, OutFinished out 902)
    , (902, Done) ]
 }

