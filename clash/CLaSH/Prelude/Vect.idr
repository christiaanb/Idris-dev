module CLaSH.Prelude.Vect

%access public
%default total

infixr 4 +>>
(+>>) : (el : a) -> (vs : Vect (S n) a) -> Vect (S n) a
(+>>) x xs = x :: init xs

vindexM_integer : (vs : Vect n a) -> (ind : Integer) -> Maybe a
vindexM_integer []        _ = Nothing
vindexM_integer (x :: _)  0 = Just x
vindexM_integer (_ :: xs) n = vindexM_integer xs (n-1)

maxIndex : (vs : Vect n a) -> Integer
maxIndex {n} _ = cast n - 1

infix 5 !
partial
(!) : (vs : Vect n a) -> (ind : Integer) -> a
(!) xs i = case (vindexM_integer xs (maxIndex xs - i)) of
             Just a => a

vreplaceM_integer : (vs : Vect n a) -> (ind : Integer) -> (el : a) -> Maybe (Vect n a)
vreplaceM_integer Nil       _ _ = Nothing
vreplaceM_integer (_ :: xs) 0 y = Just (y :: xs)
vreplaceM_integer (x :: xs) n y = case vreplaceM_integer xs (n-1) y of
                                    Just xs' => Just (x :: xs')
                                    Nothing  => Nothing

partial
vreplace : (vs : Vect n a) -> (ind : Integer) -> (el : a) -> Vect n a
vreplace xs i a = case vreplaceM_integer xs (maxIndex xs - i) a of
                    Just xs' => xs'
