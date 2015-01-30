module Regex where

data Rx n
 = Elem n
 | Empty
 | Alt  (Rx n) (Rx n)
 | Seq  (Rx n) (Rx n)
 | Star (Rx n)
 deriving Show

data StarSeqs n = StarSeqs [Alts n]
data Alts n = Alts [Seqs n]
data Seqs n = Seqs [Stars n]
data Stars n = One [n] | Repeat [n]

rxOfStar :: StarSeqs n -> Rx n
rxOfStar r
 = ss r
 where
  ss (StarSeqs ns)
   = strip_emp $ foldl Seq Empty (map (Star . alt) ns)

  alt (Alts (a:as))
   = foldl Alt (seq a) (map seq as)
  alt (Alts [])
   = Empty -- actually should be fail
  
  seq (Seqs stars)
   = strip_emp $ foldl Seq Empty (map star stars)
  
  star (One ns)
   = strip_emp $ foldl Seq Empty (map Elem ns)
  star (Repeat ns)
   = Star $ strip_emp $ foldl Seq Empty (map Elem ns)

  strip_emp (Star b)
   = case strip_emp b of
      Empty -> Empty
      b'    -> Star b'
  strip_emp (Seq a b)
   = case (strip_emp a, strip_emp b) of
      (Empty, Empty)
       -> Empty
      (Empty, b)
       -> b
      (a, Empty)
       -> a
      (a,b)
       -> (Seq a b)
  strip_emp b
   = b


ppr_rx :: Show n => Rx n -> String
ppr_rx (Elem n) = show n
ppr_rx (Empty)  = ""
ppr_rx (Alt a b) = "(" ++ ppr_rx a ++ " | " ++ ppr_rx b ++ " )"
ppr_rx (Seq a b) = ppr_rx a ++ "; " ++ ppr_rx b
ppr_rx (Star i@(Seq _ _))   = "(" ++ ppr_rx i ++ ")*"
ppr_rx (Star i@(Empty))     = "(" ++ ppr_rx i ++ ")*"
ppr_rx (Star i)             =        ppr_rx i ++  "*"

filter_rx :: (n -> Maybe n) -> Rx n -> Rx n
filter_rx f rx
 = case rx of
    Elem n
     | Just n' <- f n
     -> Elem n'
     | otherwise
     -> Empty

    Empty
     -> Empty
    Alt a b
     -> Alt (filter_rx f a) (filter_rx f b)
    Seq a b
     -> Seq (filter_rx f a) (filter_rx f b)
    Star a
     -> Star (filter_rx f a)


normalise :: Rx n -> Rx n
normalise rx_
 = go rx_
 where
  go rx
   = case rx of
      Elem _
       -> rx
      Empty
       -> rx
      Alt a b
       -> Alt (go a) (go b)
      Seq a b
       -> empties Seq a b
      Star a
       | Empty <- go a
       -> Empty
       | otherwise
       -> Star (go a)

  empties c a b
   = let a' = go a
         b' = go b
     in case (a', b') of
       (Empty,Empty)
        -> Empty
       (Empty, _)
        -> b'
       (_, Empty)
        -> a'
       (_, _)
        -> c a' b'


data E n = Emit | EJust n
 deriving (Eq,Ord,Show)

-- map :*: (AE)*
map_r :: n -> Rx (E n)
map_r n = Star (Seq (Elem (EJust n)) (Elem Emit))

map_s :: n -> StarSeqs (E n)
map_s n = StarSeqs [Alts [Seqs [One [EJust n, Emit]]]]

-- filter :*: (AE?)*
filter_r :: n -> Rx (E n)
filter_r n = Star (Seq (Elem (EJust n)) (Alt Empty (Elem Emit)))

filter_s :: n -> StarSeqs (E n)
filter_s n = StarSeqs [Alts [Seqs [One [EJust n, Emit]], Seqs [One [EJust n]] ]]

-- indices :*: (AE*)*
indices_r :: n -> Rx (E n)
indices_r n = Star (Seq (Elem $ EJust n) (Star $ Elem Emit))

indices_s :: n -> StarSeqs (E n)
indices_s n = StarSeqs [Alts [Seqs [One [EJust n], Repeat [Emit]] ]]

-- filter (map...)          :*: (abE?)*
-- map (filter...)          :*: (a(bE)?)*
-- filter (indices...)      :*: (a(bE*)?)*
-- map    (indices...)      :*: (abE*)*
-- filter filter filter     :*: (a(b(cE?)?)?)*

-- inj1 b (aE) (b(|E))*
-- ab(|E)

-- inj1 b (aE)* (b(|E))*
-- = (ab(|E))*

-- inj1 b (a(|E))* (bE)*
-- = (a(|bE))*

{-
inj1 :: Eq n => Rx (E n) -> Rx (E n) -> Rx (E n)
inj1 rx1 rx2
 = go rx1 rx2
 where
  go q r
   | Empty <- q
   = Empty

   | Star q' <- q
   , Star r' <- r
   = Star (go q' r')
   -- TODO questionable
   | Star r' <- r
   = go q r'

   | Elem n' <- q
   , n' == Emit
   = r
   | Elem n' <- q
   = q

   | Seq q1 q2 <- q
   = Seq (go q1 r) (go q2 r)

   | Alt q1 q2 <- q
   = Alt (go q1 r) (go q2 r)
-}

inj1 :: Eq n => n -> Rx n -> Rx n -> Rx n
inj1 n rx1 rx2
 = go rx1 rx2
 where
  -- q = target
  -- r = value
  go q r
   = case (q,r) of
      (Empty,_)
       -> Empty
      (Star q', Star r')
       -> Star (go q' r')
      (Star q', _)
       -> Star (go q' r)
      (Elem n', _)
       | n' == n
       -> r
       | otherwise
       -> q
      (Seq q1 q2, _)
       -> Seq (go q1 r) (go q2 r)
      (Alt q1 q2, _)
       -> Alt (go q1 r) (go q2 r)

subname :: Eq n => n -> n -> Rx n -> Rx n
subname n n' rx
 = filter_rx (\c -> if c == n then Just n' else Just c) rx

sub2 :: Eq n => n -> n -> (n -> n -> Rx (E n)) -> Rx (E n) -> Rx (E n) -> Rx (E n)
sub2 n1 n2 rx p q
 = let n1' = EJust n1
       n2' = EJust n2
       rx' = rx n1 n2
       p'  = subname Emit n1' p
       q'  = subname Emit n2' q
   in  inj1 n2' (inj1 n1' rx' p') q'


-- Append :*: (aE)* (bE)*
-- so with
--  c = (aE)*(bE)*
--  d = (cE)*(pE)*
-- substituting c into d gets
--  c' = (ac)*(bc)*
--  d' = (acE)*(bcE)* (pE)*
--
-- subst c := (ac)*(bc)* in (cE)*(pE)*
-- subst c := (ac)*(bc)* in (cE)*
-- subst c := (ac)*(bc)* in  cE
-- subst c := (ac)*(bc)* in  cE
-- subst c := cE         in  (ac)*(bc)*
-- subst c := cE         in  (ac)*            ; subst c := cE in (bc)*
-- (acE)*(bcE)*
--
--
-- subst c := a*b* in (cE)*(cEE)*
-- ((aE)*(bE)*(bEE)* | (aE)*(aEE)*(bEE)*)
--
-- ( subst c := a*b* in (cE) ; subst c :=   b* in (cEE)* 
-- | subst c := a*   in (cE) ; subst c := a*b* in (cEE)*
-- )
--



append_r :: n -> n -> Rx (E n)
append_r a b
 = Seq (Star (Seq (Elem $ EJust a) (Elem Emit)))
       (Star (Seq (Elem $ EJust b) (Elem Emit)))

append_s :: n -> n -> StarSeqs (E n)
append_s a b
 = StarSeqs
    [ Alts [Seqs [One [EJust a, Emit]] ]
    , Alts [Seqs [One [EJust b, Emit]] ] ]

merge_r :: n -> n -> Rx (E n)
merge_r a b
 = Star (Seq (Star (Seq (Elem $ EJust a) (Elem Emit)))
             (Star (Seq (Elem $ EJust b) (Elem Emit))))

merge_s :: n -> n -> StarSeqs (E n)
merge_s a b
 = StarSeqs
    [ Alts [ Seqs [One [EJust a, Emit]]
           , Seqs [One [EJust b, Emit]] ] ]

zip_r :: n -> n -> Rx (E n)
zip_r a b
 = Star (Seq (Elem $ EJust a) (Seq (Elem $ EJust b) (Elem Emit)))

zip_s :: n -> n -> StarSeqs (E n)
zip_s a b
 = StarSeqs
    [ Alts [ Seqs [One [EJust a, EJust b, Emit]] ] ]


-- subst n := rx in rx
starsub1 :: Eq n => n -> StarSeqs (E n) -> StarSeqs (E n) -> StarSeqs (E n)
starsub1 n_ (StarSeqs insert) (StarSeqs into)
 = StarSeqs (go into)
 where
  splits []
   = []
  splits (Alts a : as)
   = 
   | contains_alts n_ (Alts a)
   = 

  go []
   = []
  go (Alts as : ss)
   | contains_alts n_ (Alts as)
   = go_alts as ++ go ss
   | otherwise
   = Alts as : go ss
 
  go_alts []
   = []
  go_alts (Seqs seq : alts)
   | contains_seqs n_ (Seqs seq)
   = go_seqs seq ++ go_alts alts
   | otherwise
   = Seqs seq : go_alts alts

  go_seqs []
   = []


  contains_ss n (StarSeqs ins)
   = any (contains_alts n) ins

  contains_alts n (Alts seqs)
   = any (contains_seqs n) seqs

  contains_seqs n (Seqs stars)
   = any (contains_stars n) stars

  contains_stars n (One ns)
   = elem n ns
  contains_stars n (Repeat ns)
   = elem n ns

{-
data StarSeqs n = StarSeqs [Alts n]
data Alts n = Alts [Seqs n]
data Seqs n = Seqs [Stars n]
data Stars n = One [n] | Repeat [n]
-}
