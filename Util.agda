module Util where

open import Agda.Primitive

data NULL {n : Level} : Set n where

data ONE {n : Level} : Set n where
  one : ONE

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

record Eq {a} (A : Set a) : Set a where
  field
    _==_ : A -> A -> Bool

open Eq {{...}} public

_\=_ : {A : Set} -> {{_ : Eq A}} -> A -> A -> Bool
_\=_ x y = not (x == y)


instance
  eqBool : Eq Bool
  _==_ {{eqBool}} true true = true
  _==_ {{eqBool}} false false = true
  _==_ {{eqBool}} _ _ = false

--general equality
infix 4 _===_

data _===_ {A : Set} (x : A) : A -> Set where
  refl : x === x
