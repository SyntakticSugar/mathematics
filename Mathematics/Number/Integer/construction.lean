/-
Module      : Integers
Description : Formal developement of ℤ.
Maintainer  : Robert Culling <rhsculling@pm.com>

This module constructs the integers as a quotient
of the product ℕ × ℕ under the relation:

  (a,b) ~ (c,d) ↔ a+d = c+b

Negation, Addition and multiplication are defined
and shown to descend to this quotient.

Theorems about these functions will go in:
  Mathematics.Integer.arithmetic
-/

-- Integers require importing ℕ
import Mathematics.Number.natural
open ℕ

-- ℤ is defined as the quotient of the following type ...
def preInt := ℕ × ℕ

def nat_to_preInt (n : Nat) : preInt :=
  (nat_to_peano n, zero)

-- ... by the following relation ...
def preRel (x y : preInt) : Prop :=
  x.fst + y.snd = y.fst + x.snd

-- ... which is shown below to be an equivalence relation.
theorem preRel_reflx :
  ∀ x : preInt, preRel x x :=
  by
    intro x
    unfold preRel
    rfl

theorem preRel_symm :
  ∀ x y : preInt, preRel x y → preRel y x :=
  by
    intro x y
    unfold preRel
    intro t₁
    exact Eq.symm t₁

theorem preRel_trans :
  ∀ x y z : preInt, preRel x y → preRel y z → preRel x z :=
  by
    intro x y z
    unfold preRel
    intro t₁ t₂
    have h₁ : x.fst + y.snd + z.snd = y.fst + x.snd + z.snd :=
      by congr
    rw [add_comm x.fst y.snd, add_comm y.fst,add_assoc x.snd, t₂] at h₁
    rw [<-add_assoc x.snd, add_comm x.snd] at h₁
    rw [add_comm y.snd,add_assoc x.fst, add_comm y.snd,<-add_assoc] at h₁
    -- have t₃ : x.fst + z.snd = z.fst + x.snd :=
    exact add_right_cancel y.snd (x.fst + z.snd) (z.fst + x.snd) h₁

-- Seems to be some type inference error that @-prefix bypasses.
instance preRel_equiv : Equivalence preRel :=
{ refl  := @preRel_reflx,
  symm  := @preRel_symm,
  trans := @preRel_trans }

-- We define the integers ℤ as the quotient by this equivalence.
def intSetoid : Setoid preInt :=
  Setoid.mk preRel preRel_equiv

def ℤ := Quotient intSetoid

def fromNat (n : ℕ) : ℤ :=
  Quotient.mk intSetoid (n, 0)

/-
  On ℤ we want to write functions and prove properties of them.

  For example:

    [ ] :: Negation (Unary)
    [ ] :: Addition (Binary)
    [ ] :: Multiplication (Binary)

  For each of these functions we employ the following steps:

    1. Define the function on preInt.
    2. Write a proof that it's well-defined wrt. preRel.
    3. Write a function from preInt (× preInt) to ℤ
    4. Use Quotient.liftₙ to lift this to ℤ

  Kudos to Jason Rute for explaining this:

  proofassistants.stackexchange.com/questions/2663

  Any odd choices in what follows are my own!

-/

/-
  Defining negation on ℤ
-/

def preInt_neg (x : preInt) : preInt :=
  (x.snd, x.fst)

theorem neg_congr :
  ∀ x y : preInt, preRel x y → preRel (preInt_neg x) (preInt_neg y) :=
    by
      intro x y
      unfold preRel
      intro h₁
      rw [preInt_neg,preInt_neg]
      simp
      apply Eq.symm
      rw [add_comm,add_comm x.snd]
      exact h₁

def negAux (x : preInt) : ℤ :=
  Quotient.mk intSetoid (preInt_neg x)

theorem negAux_congr :
  ∀ x y : preInt, preRel x y → negAux x = negAux y :=
    by
      intro x y
      intro h₁
      apply Quotient.sound
      exact neg_congr x y h₁

def int_neg : ℤ → ℤ :=
  Quotient.lift negAux negAux_congr

-- Notation for negation
prefix:100 "-" => int_neg

/-
  Defining addition on ℤ
-/
