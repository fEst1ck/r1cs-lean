/-
! Defines a representation of R1CS constraints
-/
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import R1CS.Var

-- The prime number `p` with which we form the field `ZMod p`
variable (p : Nat) [hp : Fact (Prime p)]

-- Number of constraint variables
variable (n : Nat)

/-- AST `a * x` -/
structure Subterm where
  coeff : ZMod p
  var : Var n

/-- AST `a₁ * x₁ + a₂ * x₂ + ... + aₙ * xₙ` -/
structure Term where
  subterms : List (@Subterm p n)

/-- Represents an equation `(a . x) * (b . x) - c . x = 0`
-/
-- Our representation is not in normal form;
-- but we can prove the semantical equivalence of
-- the our representation and the normal form
-- when necessary
structure Constraint where
  a : @Term p n
  b : @Term p n
  c : @Term p n

/--
A circuit is specified by a list of constraints
(a₀ . x) * (b0 . x) - c₁ . x = 0;
(a₁ . x) * (b0 . x) - c₂ . x = 0;
...
-/
structure Circuit where
  constraints : List (Constraint p n)

/--
A witness is an assignment of values in F_p to the constraint variables
-/
def Witness : Type := Var n → ZMod p

@[simp]
def subterm_denot {p n} (s : @Subterm p n) (x : Witness p n) : ZMod p :=
  let coeff := s.coeff
  let var := s.var
  coeff * x var

@[simp]
def term_denot {p n} (t : @Term p n) (x : Witness p n) : ZMod p :=
  let subterms := t.subterms
  (subterms.map (fun t => subterm_denot t x)).sum

/--
The denotation of a constraint is a predicate on witness
that the constraint is satisfied by the witness.
-/
@[reducible, simp]
def denot_constraint (c : Constraint p n) (x : Witness p n) : Prop :=
  let a := c.a
  let b := c.b
  let c := c.c
  term_denot a x * term_denot b x - term_denot c x = 0

/--
The denotation of a circuit is a predicate on witness
that all constraints are satisfied by the witness.
-/
@[reducible, simp]
def denot_circuit {p} {n} (c : Circuit p n) (x : Witness p n) : Prop :=
  let constraints := c.constraints
  List.foldl (fun acc c => acc ∧ denot_constraint p n c x) True constraints
