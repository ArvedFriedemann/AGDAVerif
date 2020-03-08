module Solver where

open import Util
open import Agda.Primitive

_~U~_ = _⊔_

--computable functions
data m {n : Level} (A : Set n) : Set (lsuc n) where
  fail : m A
  pure : A -> m A
  _<$>_ : {B : Set n} -> m (B -> A) -> m B -> m A --this is needed to freeze the creation of values
  _>->=_ : {B : Set n} -> m B -> m (B -> m A) -> m A --slightly modified bind. In this case, even the operator needs to be a value in the monad. This is kinda the recursion operator.
  _|||_ : m A -> m A -> m A

--In order for this to work, it needs to be made sure the values are only transformed with allowed functions. in fact, best would be if all transformations were defined within the monad. Functions would be defined via ite-transformation, however, this needs some identification mechanism for the values. Is equality of addresses enough? Can it be prevented for the same value to go into two different parts? Maybe there could be an equality proof given from the outside! or like...nonequality from all values previously present. That sounds super cumbersome.
--Within the monad, there are only atomic values, and fixed constructions on values (namely tuples). could these constructors be given from outside? They would freeze into tuples anyway, but they might enable actual values afterwards.
--Then, simple equational ite-reasoning, only that there is no mechanism ensuring that every values has to be deducible. in that case, start a search.
--Is it at all needed to already think of recursion and self reference? Hard to tell.
--recursion through monadic bind works by depending the next observed context on the currently observed object. the interesting thing: General rules on the context that are learned throughout the search could make it reasonable to cache contexts, reusing the data when the search comes back to it. On the long run: Memory management like time management

--extractable values
--idea behind this: There is always only finitely many constructors. The values can be extracted bit by bit, always giving the constructor with monadic references to the subvalues
data pointerthingy where
  selector : A -> f B -> B       --a function to make a value interact as a selector. Can be used as an identification
  --needs to return someting containing the context again for next values
  selector2 : A -> f (B f A) -> B f A --this modeles the fact that the value A with its pointers is still needed in the type.
  getVal : f A -> (B, m (f A)) --this returns some selector value with the addresses to the subvalues.
  getVal : f A -> ((A -> A -> ... -> B), m (f A)) --this returns the constructor with the subsequent addresses
