/-!
Defines type of constraint variables
-/

/-- `Var n` is the set of `n` variables -/
inductive Var : Nat → Type where
  | z : Var (Nat.succ n)
  | s : Var n → Var (Nat.succ n)

open Var

-- The two variables in the set of two variables
example : Var 2 := z
example : Var 2 := s z
