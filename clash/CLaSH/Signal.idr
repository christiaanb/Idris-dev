module CLaSH.Signal

-- import Data.HVect

%access public

infixr 5 :-
abstract codata Signal a = (:-) a (Signal a)

namespace Signal
  abstract
  head : (sig : Signal a) -> a
  head (h :- _) = h

  abstract
  tail : (sig : Signal a) -> Signal a
  tail (_ :- tl) = tl

  abstract
  mapS : (a -> b) -> Signal a -> Signal b
  mapS f (a :- as) = f a :- mapS f as

  abstract
  pureS : a -> Signal a
  pureS a = a :- pureS a

  abstract
  appS : Signal (a -> b) -> Signal a -> Signal b
  appS (f :- fs) as = f (head as) :- (appS fs (tail as))

  abstract
  register : (initS : a) -> (sig : Signal a) -> Signal a
  register i s = i :- s

sample : (i : Nat) -> (s : Signal a) -> List a
sample Z     inp = []
sample (S n) inp = head inp :: sample n (tail inp)

fromList : (l : List a) -> Signal a
fromList (x::xs) = x :- fromList xs

simulate : (Signal a -> Signal b) -> List a -> List b
simulate f is = sample (length is) (f (fromList is))

instance Functor Signal where
  map = Signal.mapS

instance Applicative Signal where
  pure  = Signal.pureS
  (<$>) = Signal.appS

-- namespace HVect
--   head : {ts : Vect n Type} -> (hs : HVect (t::ts)) -> t
--   head (x::xs) = x

--   tail : {ts : Vect n Type} -> (hs : HVect (t::ts)) -> HVect ts
--   tail (x::xs) = xs

--   abstract
--   pack : {ts : Vect n Type} -> (hs : HVect (map Signal ts)) -> Signal (HVect ts)
--   pack {ts=[]}     []      = pure HVect.Nil
--   pack {ts=t::ts'} (x::xs) = [| HVect.(::) x (pack xs) |]

--   abstract
--   unpack : {ts : Vect n Type} -> (phs : Signal (HVect ts)) -> HVect (map Signal ts)
--   unpack {ts=[]}      nils = []
--   unpack {ts=t::ts'}  hvs  = map HVect.head hvs :: unpack (map HVect.tail hvs)

-- lift : {is : Vect m Type} -> {ts : Vect n Type} ->
--        (mealy : s -> HVect is -> HVect [s,HVect ts]) -> (ini : s) ->
--        (inpt : HVect (map Signal is)) -> HVect (map Signal ts)
-- lift {s} {ts} fun initS inp = unpack (head (tail res))
--   where
--     res   : HVect [Signal s, Signal (HVect ts)]
--     prevS : Signal s
--     res   = unpack [| fun prevS (pack inp) |]
--     prevS = register initS (head res)

namespace Vect
  abstract
  pack : (vs : Vect n (Signal a)) -> Signal (Vect n a)
  pack vs = map Signal.head vs :- pack (map Signal.tail vs)

  abstract
  unpack : (pvs : Signal (Vect n a)) -> Vect n (Signal a)
  unpack {n=Z}   vs = []
  unpack {n=S k} vs = map Vect.head vs :: unpack (map Vect.tail vs)

instance Num a => Num (Signal a) where
  (+) a b     = [| (+) a b |]
  (-) a b     = [| (-) a b |]
  (*) a b     = [| (*) a b |]
  abs         = map abs
  fromInteger = pure . fromInteger
