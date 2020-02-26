module Memory where

open import Util

record VarMonad (m : Monad) (Ptr : Set -> Set ) : Set1 where
  field
    new : {A : Set} -> (a : A) -> m (Ptr A)
    get : {A : Set} -> Ptr A -> m A
    set : {A : Set} -> Ptr A -> A -> m ONE

    new_prop : {A : Set} -> {{_ : Eq (Ptr A)}} -> (a b : A) ->
                (| (new a) \= (new b) |) === (return true)
