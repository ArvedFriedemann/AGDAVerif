module Solver where

open import Util
open import Agda.Primitive

_~U~_ = _⊔_

--computable functions
data t {n m : Level} (A : Set n) (B : Set m) : Set (lsuc (n ~U~ m)) where
  pure : B -> t A B
  _<>_ : {I : Set (n ~U~ m)} -> t A I -> t I B -> t A B
