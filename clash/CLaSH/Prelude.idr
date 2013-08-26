module CLaSH.Prelude

import CLaSH.Default
import CLaSH.Signal
import CLaSH.Prelude.Vect
import Data.HVect

%access public

window : (Default a) => Signal a -> Vect (S (S n)) (Signal a)
window {a} x = (x::prev)
  where
    prev : Default a => Vect (S n) (Signal a)
    next : Default a => Vect (S n) (Signal a)
    prev = unpack (register (pure def) (pack next))
    next = x +>> prev
