/-
! We verify the correctness of the example circuit `IsEqual`
! in `example.circom` in the root directory of the project.
-/
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Field.ZMod
import R1CS.Var
import R1CS.R1CS

@[reducible]
def p : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617
variable [hp : Fact (Nat.Prime p)]
abbrev Fp : Type := ZMod p

-- Number of constraint variables
@[reducible]
def n : Nat := 7

open Var

-- Set of constraint variables
@[simp, reducible]
def Vars := Var n

def one : Vars := z
def main.out : Vars := z.s
def main.in : Vector Vars 2 := #v[z.s.s, z.s.s.s]
def main.isz.out : Vars := z.s.s.s.s
def main.isz.in : Var n := z.s.s.s.s.s
def main.isz.inv : Var n := z.s.s.s.s.s.s

-- Constraints
-- [ main.isz.in ] * [ main.isz.inv ] - [ 1 +21888242871839275222246405745257275088548364400416034343698204186575808495616main.out ] = 0
@[simp]
def constraint1 : Constraint p n :=
  { a := ⟨[⟨1, main.isz.in⟩]⟩,
    b := ⟨[⟨1, main.isz.inv⟩]⟩,
    c := ⟨[⟨1, one⟩, ⟨-1, main.out⟩]⟩ }

-- [ main.isz.in ] * [ main.out ] - [  ] = 0
@[simp]
def constraint2 : Constraint p n :=
  { a := ⟨[⟨1, main.isz.in⟩]⟩,
    b := ⟨[⟨1, main.out⟩]⟩,
    c := ⟨[]⟩ }

-- [  ] * [  ] - [ 21888242871839275222246405745257275088548364400416034343698204186575808495616main.in[0] +main.in[1] +21888242871839275222246405745257275088548364400416034343698204186575808495616main.isz.in ] = 0
@[simp]
def constraint3 : Constraint p n :=
  { a := ⟨[]⟩,
    b := ⟨[]⟩,
    c := ⟨[⟨-1, main.in[0]⟩, ⟨1, main.in[1]⟩, ⟨-1, main.isz.in⟩ ]⟩ }

@[simp]
def is_zero_input : Vars := main.isz.in
@[simp, reducible]
def is_zero_output : Vars := main.out

-- Circuit supposed to compute is_zero
@[reducible, simp]
def circuit_is_zero : Circuit p n :=
  { constraints := [constraint1, constraint2] }

-- Returns 1 if x = 0, 0 otherwise
@[simp, reducible]
def is_zero (x : Fp) : Fp :=
  if x = 0 then 1 else 0

-- Specification that the witness computes is_zero
@[simp]
def spec_is_zero (w : Witness p n) : Prop :=
  w is_zero_output = is_zero (w is_zero_input)

-- Proves that a witness satifying the constraints
-- also satisfies the functional specification
lemma circuit_is_zero_correctness :
∀ (w : Witness p n),
  w one = 1 →
  denot_circuit circuit_is_zero w →
  spec_is_zero w := by
  intros w _ h_circ
  dsimp at h_circ
  rcases h_circ with ⟨⟨_, h_circ1⟩, h_circ2⟩
  simp at h_circ1
  aesop
  have h := congrArg (· + 1) h_circ1
  simp at h
  exact h

-- Circuit supposed to compute is_equal
@[reducible, simp]
def circuit_equal : Circuit p n :=
  { constraints := [constraint1, constraint2, constraint3] }

-- Returns 1 if x = y, 0 otherwise
@[simp, reducible]
def is_equal (x y : Fp) : Fp :=
  if x = y then 1 else 0

-- Specification that the witness computes is_equal
@[simp]
def spec_is_equal (w : Witness p n) : Prop :=
  w main.out = is_equal (w main.in[1]) (w main.in[0])

lemma is_zero_eq_is_equal :
∀ (x y : Fp),
is_zero (x - y) = is_equal x y := by
  intros x y
  aesop
  have h := congrArg (· + y) h
  simp at h
  aesop

-- Proves that a witness satifying the constraints
-- also satisfies the functional specification
lemma circuit_equal_correctness :
∀ (w : Witness p n),
  w one = 1 →
  denot_circuit circuit_equal w →
  w main.out = is_equal (w main.in[1]) (w main.in[0]) := by
  intros w h_one h_circ
  rcases h_circ with ⟨⟨⟨_, h_circ1⟩, h_circ2⟩, h_circ3⟩
  rw [<- is_zero_eq_is_equal]
  rw [circuit_is_zero_correctness w h_one ⟨⟨True.intro, h_circ1⟩, h_circ2⟩]
  simp
  simp at h_circ3
  have h : w main.isz.in = w main.in[1] - w main.in[0] := by
    have h_circ3 := congrArg (· + (w main.in[1] - w main.in[0])) h_circ3
    simp at h_circ3
    exact h_circ3
  aesop
