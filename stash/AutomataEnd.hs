module AutomataEnd where
import Automata

data N ins = Read ins | End ins
 deriving (Eq,Ord,Show)

zip_a :: n -> n -> n -> Machine Int (N n)
zip_a a b e
 = Machine
 { _init   = 0
 , _states =
    [ (0, State [(Read a, 1)])
    , (1, State [(Read b, 2)])
    , (2, State [(Read e, 0)])
    ]
 }

append_a :: n -> n -> n -> Machine Int (N n)
append_a a b e
 = Machine
 { _init   = 0
 , _states =
    [ (0, State [(Read a, 1), (End a, 2)])
    , (1, State [(Read e, 0)])
    , (2, State [(Read b, 3)])
    , (3, State [(Read e, 2)])
    ]
 }

{-

Machine {_states =
[(S1 2 [0],State [(Read "zip",S1 0 [0])])
,(S1 1 [0],State [(Read "c",S1 2 [0])])
,(S2 1 [1],State [(Read "app",S1 1 [0])])
,(S1 0 [2],State [(Read "b",S2 1 [3])])
,(S1 2 [2],State [(Read "zip",S1 0 [2])])
,(S1 1 [2],State [(Read "c",S1 2 [2])])
,(S2 1 [3],State [(Read "app",S1 1 [2])])
,(S2 1 [2],State [(Read "b",S2 1 [3])])
,(S1 0 [0],State [(Read "a",S2 1 [1]),(End "a",S2 1 [2])])
], _init = S1 0 [0]}

-}



