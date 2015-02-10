module Automata4Coms where
import Automata4
import qualified Data.Map as M

-- | Just for testing
data Names = A | B | C | D | E | U | V | W | X | Y | Z
 deriving (Show, Eq, Ord)

empty_a :: Machine Int n
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
zip_a :: n -> n -> n -> Machine Int n
zip_a ina inb out
 = Machine
 { _init = 0
 , _trans = M.fromList
 $ [ (0, Pull ina 1 999)
   , (1, Pull inb 2 990)
   , (2, Out  (Function "pair" out [ina,inb]) 3)
   , (3, Release ina 4)
   , (4, Release inb 0)

   , (990, Release ina 999)
   , (999, OutFinished out 1000)
   , (1000, Done) ]
 }

-- | Append two inputs
append_a :: n -> n -> n -> Machine Int n
append_a ina inb out
 = Machine
 { _init = 0
 , _trans = M.fromList
 $ [ (0, Pull ina                     1 10)
   , (1, Out  (Function "id" out [ina]) 2)
   , (2, Release ina                  0)

   , (10, Pull inb                    11 999)
   , (11, Out  (Function "id" out [inb]) 12)
   , (12, Release inb                 10)

   , (999, OutFinished out 1000)
   , (1000, Done) ]
 }


merge_a :: n -> n -> n -> Machine Int n
merge_a ina inb out
 = Machine
 { _init = 0
 , _trans = M.fromList
     [ (0, Pull ina         1 100)
     -- [Value a]
     , (1, Pull inb         2 200)
     -- [Value a, Value b]
     , (2, If (Function "le" out [ina,inb]) 10 20)

     -- [Value a, Value b, a <= b]
     , (10, Out (Function "id" out [ina]) 11)
     , (11, Release ina                     12)
     -- [Value b]
     , (12, Pull ina                2       101)

     -- [Value a, Value b, b < a]
     , (20, Out (Function "id" out [inb]) 21)
     , (21, Release inb                     22)
     -- [Value a]
     , (22, Pull inb                2       200)


     -- [Empty a] suck from b
     , (100, Pull inb       101 900)
     -- [Empty a, Value b]
     , (101, Out (Function "id" out [inb]) 102)
     , (102, Release inb    100)

     -- [Value a, Empty b] suck from a
     , (200, Out (Function "id" out [ina]) 201)
     , (201, Release ina                     202)
     , (202, Pull    ina          200        900)

     -- [Empty a, Empty b]
     , (900, OutFinished out 901)
     , (901, Done)
     ]
 }

filter_a :: String -> n -> n -> Machine Int n
filter_a pred inp out
 = Machine
 { _init = 0
 , _trans = M.fromList
    [ (0, Pull inp  1   900)
    -- [Value inp]
    , (1, If (Function pred out [inp]) 10 11)
    
    -- [Value inp, pred inp]
    , (10, Out (Function "id" out [inp]) 11)
    -- [Value inp]
    , (11, Release inp 0)

    -- [Empty inp]
    , (900, OutFinished out 901)
    , (901, Done)
    ]
 }

map_a :: String -> n -> n -> Machine Int n
map_a fun inp out
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

indices_a :: n -> n -> Machine Int n
indices_a inp out
 = Machine
 { _init = 0
 , _trans = M.fromList
    [ (0, Pull inp 1 900)
    , (1, Update (Function "ix=0" out []) 2)
    , (2, Update (Function "upto=$" out [inp]) 3)
    , (3, Release inp 4)

    , (4, Out (Function "ix" out []) 5)
    , (5, Update (Function "ix=ix+1" out []) 6)
    , (6, If (Function "ix<upto" out []) 4 0)

    , (900, OutFinished out 901)
    , (901, Done) ]
 }
