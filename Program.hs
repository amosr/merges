module Automata3 where
import Text.PrettyPrint.Leijen

data Function = F String
 deriving Show

data P ins out
 = P ins out :> P ins out
 | Pull ins
 | WhileAvailable [ins] (P ins out)
 | IfAvailable    [ins] (P ins out) (P ins out)
 | IfState        Function out (P ins out) (P ins out)
 | Out            Function out
 | Update         Function out
 | Skip
 deriving Show

-- | Merge two programs, horizontally.
-- Requires that each graph does not use the other's outs.
-- Also requires Outs(p1) intersect Outs(p2) = {}
--horiz2 :: (Eq ins, Eq outs) => P ins outs -> P ins outs -> Maybe (P ins outs)
--horiz2 p1 p2
-- = ...

instance (Show ins, Show out) => Pretty (P ins out) where
 pretty p
  = case p of
     a :> b
      -> pretty a <$> pretty b
     Pull a
      -> text "pull" <+> text (show a)
     WhileAvailable is p
      -> text "while" <+> text (show is) <$>
         indent 4 (pretty p)
     IfAvailable is then_ else_
      -> text "if_available" <+> text (show is) <$>
         indent 4 (pretty then_) <$>
         text "else" <$>
         indent 4 (pretty else_)

     IfState (F f) o then_ else_
      -> text "if_state (" <> text f <> text ") (" <> text (show o) <> text ")" <$>
         indent 4 (pretty then_) <$>
         text "else" <$>
         indent 4 (pretty else_)

     Out (F f) o
      -> text "out (" <> text f <> text ") (" <> text (show o) <> text ")"

     Update (F f) o
      -> text "update (" <> text f <> text ") (" <> text (show o) <> text ")"

     Skip
      -> text "skip"


data In1 = In1
 deriving (Show, Eq, Ord)
data Ins = InA | InB
 deriving (Show, Eq, Ord)
data Out = Emit
 deriving (Show, Eq, Ord)


zip_a :: P Ins Out
zip_a
 = WhileAvailable [InA, InB] $
    Pull InA:>
    Pull InB:>
    Out  (F "a*b") Emit

append_a :: P Ins Out
append_a
 = WhileAvailable [InA] (
    Pull InA :>
    Out (F "a") Emit) :>
   WhileAvailable [InB] (
    Pull InB :>
    Out (F "b") Emit)

merge_a :: P Ins Out
merge_a
 = IfAvailable [InA] (
    IfAvailable [InB] (
        Pull InA :>
        Pull InB :>
        WhileAvailable [InA,InB] (
          IfState (F "a < b") Emit (
            Pull InA :>
            Out (F "a") Emit
          ) (
            Pull InB :>
            Out (F "b") Emit
          )
        ) :>
        suck InA :>
        suck InB
    ) (suck InA)
   ) (suck InB)
 where
  suck x
   = WhileAvailable [x] (Pull x :> Out (F (show x)) Emit)

map_a :: P In1 Out
map_a
 = WhileAvailable [In1] $
    Pull In1:>
    Out  (F "f a") Emit


filter_a :: P In1 Out
filter_a
 = WhileAvailable [In1] $
    Pull In1 :>
    IfState (F "p a") Emit (
        Out  (F "a") Emit
    ) (Skip)


