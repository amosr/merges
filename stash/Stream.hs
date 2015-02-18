module Stream where
import Prelude hiding (map, filter)

data Forward
 = Forward | Stay
data Step b s
 = Yield b s Forward
 | Skip    s Forward
 | Done

data Stream a b s
 = Stream
 { _init    :: s
 , _emit    :: Maybe a -> s -> Step b s
 }


map :: (a -> b) -> Stream a b ()
map f
 = Stream
 { _init    = ()
 , _emit    = \a s ->
                case a of
                 Just a' -> Yield (f a') s Forward
                 Nothing -> Done
 }


filter :: (a -> Bool) -> Stream a a ()
filter f
 = Stream
 { _init    = ()
 , _emit    = \a s ->
                case a of
                 Just a' ->
                  case f a' of
                   True  -> Yield a' s Forward
                   False -> Skip     s Forward
                 Nothing -> Done
 }


scan :: (a -> a -> a) -> a -> Stream a a a
scan k z
 = Stream
 { _init    = z
 , _emit    = \a s ->
                case a of
                 Just a' ->
                  Yield (k s a') (k s a') Forward
                 Nothing -> Done
 }


indices :: Stream Int Int Int
indices
 = Stream
 { _init    = 0
 , _emit    = \a s ->
                case a of
                 Just a' ->
                  if   a' == s
                  then Skip 0 Forward
                  else Yield s (s+1) Stay
                 Nothing -> Done
 }



eval :: Stream a b s -> [a] -> [b]
eval strm as
 = go (_init strm) as
 where
  go s []
   = case _emit strm Nothing s of
      Yield v s' _
       -> v : go s' []
      Skip    s' _
       ->     go s' []
      Done
       -> []

  go s (a:as)
   = case _emit strm (Just a) s of
      Yield v s' fw
       -> v : go  s' (forward a as fw)
      Skip    s' fw
       -> go  s' (forward a as fw)
      Done
       -> []

  forward a as Forward
   = as
  forward a as Stay
   = a:as
  
