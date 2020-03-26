module memory3 where

open import util

open import Agda.Primitive renaming (_⊔_ to _~U~_ )

import Relation.Binary.PropositionalEquality as Eqal
open Eqal using (refl; trans; sym; cong; cong-app; subst) renaming (_≡_ to _===_)
open Eqal.≡-Reasoning using (begin_; step-≡; step-≡˘) renaming (_≡⟨⟩_ to _=<>_ ; _∎ to _end)

private
  variable
    l ll : Level

record Mem {l} : Set (lsuc l) where
  field
    ptr : Mem -> Set -> Set

    empty : Mem
    --this fist and does not work because for some weird reason the result cannot depend on itself -.-
    new : {A : Set} -> (m : Mem) -> A -> m' of Mem and' ((ptr m' A) and (ptr m A -> ptr m' A))
    get : {A : Set} -> (m : Mem) -> ptr m A -> A
    put : {A : Set} -> (m : Mem) -> ptr m A -> A -> m' of Mem and' (ptr m A -> ptr m' A)

    new-prop : {A : Set} -> (a : A) -> (m m' : Mem) -> (p : ptr m' A) ->
                < m' , << p , _ >> > === new m a -> get m' p === a

    get-over-put : {A : Set} -> (a : A) -> (m m' : Mem) -> (p : ptr m A) ->
                                (trans : ptr m A -> ptr m' A) ->
                  < m' , trans > === put m p a -> get m' (trans p) === a

    inactivity-put : {A : Set} -> (a : A) -> (m m' : Mem) -> (p : ptr m A) ->
                                  (trans : ptr m A -> ptr m' A) ->
                    < m' , trans > === put m p a ->
                    forall (p' : ptr m A) -> p' =/= p ->
                      (get m p' === get m' (trans p'))

    inactivity-new : {A : Set} -> (a : A) -> (m m' : Mem) -> (p : ptr m' A) ->
                                  (trans : ptr m A -> ptr m' A) ->
                    < m' , << p , trans >> > === new m a ->
                    forall (p' : ptr m A) -> (get m p' === get m' (trans p'))
