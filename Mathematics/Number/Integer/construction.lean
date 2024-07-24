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

-- Integers require importing ℕ.
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

def fromNat (n : Nat) : ℤ :=
  Quotient.mk intSetoid ((nat_to_peano n), (nat_to_peano 0))

instance : OfNat ℤ n where
  ofNat := fromNat n

/-
  On ℤ we want to write functions and prove properties of them.

  For example:

    [X] :: Negation (Unary)
    [X] :: Addition (Binary)
    [ ] :: Multiplication (Binary)

  For each of these functions we employ the following steps:

    1. Define the function on preInt.
    2. Write a proof that it's well-defined wrt. preRel.
    3. Write a function from preInt (× preInt) to ℤ
    4. Use Quotient.liftₙ to lift this to ℤ

  Thanks to Jason Rute for explaining this:

  proofassistants.stackexchange.com/questions/2663

  Any odd choices in what follows are my own!

-/

/-----------------------------------------------------------
                  Defining negation on ℤ
-----------------------------------------------------------/

-- 1. Function on preInt.
def preInt_neg (x : preInt) : preInt :=
  (x.snd, x.fst)

-- Function well defined with respect to preRel.
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

-- Push function to image in quotient.
def negAux (x : preInt) : ℤ :=
  Quotient.mk intSetoid (preInt_neg x)

-- Prove this is well defined; simply calls previous proof.
theorem negAux_congr :
  ∀ x y : preInt, preRel x y → negAux x = negAux y :=
    by
      intro x y
      intro h₁
      apply Quotient.sound
      exact neg_congr x y h₁

-- Now this lifts to ℤ.
def int_neg : ℤ → ℤ :=
  Quotient.lift negAux negAux_congr

-- Notation for negation
prefix:100 "-" => int_neg

theorem preRel_zero :
  ∀ x : ℕ, preRel (x,x) (zero,zero) :=
  by
    intro x
    simp [preRel]
    rw [add_zero,zero_add]

/-----------------------------------------------------------
                  Defining addition on ℤ
-----------------------------------------------------------/

-- Binary function on preInt.
def preInt_add (x y : preInt) : preInt :=
  (x.fst + y.fst, x.snd + y.snd)

-- Prove this is well defined with respect to preRel.
theorem add_congr :
  ∀ x y z w : preInt, (preRel x y) → (preRel z w)
    → (preRel (preInt_add x z) (preInt_add y w)) :=
    by
      intro x y z w
      unfold preRel
      intro h₁ h₂
      unfold preInt_add
      simp
      rw [add_comm y.snd,add_assoc,<-add_assoc z.fst,
          <-add_assoc x.fst,add_comm x.fst,add_assoc]
      calc
        z.fst + w.snd + (x.fst + y.snd) =
            w.fst + z.snd + (x.fst + y.snd) := by rw [h₂]
        _ = w.fst + z.snd + (y.fst + x.snd) := by rw [h₁]
      rw [add_comm y.fst w.fst,
          add_comm x.snd z.snd,
          add_assoc w.fst y.fst,
          <-add_assoc y.fst z.snd,
          add_comm y.fst z.snd,
          add_assoc z.snd y.fst,
          <-add_assoc w.fst]

-- Push image of add to the quotient.
def add_aux (x y : preInt) : ℤ :=
  Quotient.mk intSetoid (preInt_add x y)

-- Prove this is well-defined.
theorem addAux_congr :
  ∀ x z y w : preInt, (preRel x y) → (preRel z w)
  → (add_aux x z) = (add_aux y w) :=
  by
    intro x z y w
    intro h₁ h₂
    apply Quotient.sound
    exact add_congr x y z w h₁ h₂

-- Now lift the binary function to ℤ
def int_sum : ℤ → ℤ → ℤ :=
  Quotient.lift₂ add_aux addAux_congr

instance : Add ℤ where
  add := int_sum

/-----------------------------------------------------------
                Defining multiplication on ℤ
-----------------------------------------------------------/

/-
  Recall (a,b) is to be thought of as a - b
  Therefore multiplication should be as follows:

    (a,b)*(c,d) = (a-b)(c-d) = (ac + bd) - (ad + bc)

  This is reflected in the following definition.
-/
def preInt_mul (x y : preInt) : preInt :=
  ((x.fst * y.fst) + (x.snd * y.snd), (x.fst * y.snd) + (x.snd * y.fst))

theorem mul_congr_sndfactor :
  ∀ x y z : preInt, preRel y z → preRel (preInt_mul x y) (preInt_mul x z) :=
    by
      intro x y z
      intro h₁
      unfold preRel at h₁
      unfold preRel
      unfold preInt_mul
      simp
      rw [add_assoc,<-add_assoc (x.snd*y.snd),
          add_comm (x.snd*y.snd),<-add_assoc,<-add_assoc]
      rw [<-mul_distl_add x.fst,add_assoc,<-mul_distl_add x.snd]
      sorry


theorem mul_congr_fstfactor :
  ∀ x y z : preInt, preRel y z → preRel (preInt_mul y x) (preInt_mul z x) :=
    by
      sorry

theorem mul_congr :
  ∀ x y z w : preInt, (preRel x y) → (preRel z w)
    → (preRel (preInt_mul x z) (preInt_mul y w)) :=
    by
      intro x y z w
      intro h₁ h₂
      have t₁ : preRel (preInt_mul x z) (preInt_mul x w) :=
        mul_congr_sndfactor x z w h₂
      have t₂ : preRel (preInt_mul x w) (preInt_mul y w) :=
        mul_congr_fstfactor w x y h₁
      exact preRel_trans (preInt_mul x z)
                         (preInt_mul x w) (preInt_mul y w) t₁ t₂

def mul_aux (x y : preInt) : ℤ :=
  Quotient.mk intSetoid (preInt_mul x y)

theorem mulAux_congr :
  ∀ x z y w : preInt, (preRel x y) → (preRel z w)
  → (mul_aux x z) = (mul_aux y w) :=
  by
    intro x z y w
    intro h₁ h₂
    apply Quotient.sound
    exact mul_congr x y z w h₁ h₂

def int_mul : ℤ → ℤ → ℤ :=
  Quotient.lift₂ mul_aux mulAux_congr

instance : HMul ℤ ℤ ℤ where
  hMul := int_mul
