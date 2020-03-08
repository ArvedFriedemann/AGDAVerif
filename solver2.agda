module solver2 where

data Value : Set where
  top : Value
  bot : Value
  unas : Value
  val : {A : Set} -> A -> Value
  ite : Value -> Value -> Value -> Value -> Value --first argument (choice) is value forming the decision. Disjunction as an ite with unassigned choice. The resulting values can depend on the choice or something for recursion?
  --maybe get information on functions by prooving that they return all the information needed!

--maybe function f : A -> B -> (B, A) needed...so that it can get the needed value
--sets as predicates A -> Set
data RevFkt {A B : Set} (f : A -> B) : Set where
  revkrit : ((a : A) -> (b : B) -> exists (frev : A -> B -> (A -> Set)) st (x : A) -> (frev a b x) -> f x = b)) -> RevFkt f --the set should be a computable one
--could be rewritten to have the frev function as the only argument to the constructor apart from the proof that it's working.

--This approach models quite well the behaviour of a generalised form of clause learning. However, modeling complexity with it is still hard because there is no proper reflection of general functions involved.

--technically, for solving, maybe monad sufficient. Only that now, value clashes need to occur. A value can be unassigned, but if the same value gets assigned different values there will be a conflict. 
