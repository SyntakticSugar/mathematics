/-
Module      : Arithmetic.
Description : Fundamental arithmetic on ℤ
Maintainer  : Robert Culling <rhsculling@pm.com>

  ℤ, along with negation, +, * were constructed in:

    Mathematics.Number.Integer.construction

  This module proves basic theorems in the arithmetic
  of the integers. Once these a proved, one should not
  need to refer to the implementation details of ℤ
  as a quotient of ℕ × ℕ.
-/
import Mathematics.Number.Integer.construction
open ℕ

/-
  Theorems about negation on ℤ.
-/

 theorem negneg :
  ∀ x : ℤ, - (- x) = x :=
    by
      apply Quotient.ind
      intro a
      apply Quotient.sound
      rfl

/-
  Theorems about addition on ℤ.
-/

 theorem iadd_zero :
  ∀ x : ℤ, x + 0 = x :=
    by
      apply Quotient.ind
      intro a
      apply Quotient.sound
      rfl

 theorem zero_iadd :
  ∀ x : ℤ, (0 : ℤ) + x = x :=
    by
      apply Quotient.ind
      intro a
      apply Quotient.sound
      simp [preInt_add, nat_to_peano,zero_add]
      rfl

 theorem iadd_assoc :
  ∀ x y z : ℤ, (x + y) + z = x + (y + z) :=
    by
      apply Quotient.ind
      intro x
      apply Quotient.ind
      intro y
      apply Quotient.ind
      intro z
      apply Quotient.sound
      simp [preInt_add]
      rw [add_assoc,add_assoc x.snd]
      rfl

 theorem iadd_comm :
  ∀ x y : ℤ, x + y = y + x :=
    by
      apply Quotient.ind
      intro x
      apply Quotient.ind
      intro y
      apply Quotient.sound
      simp [preInt_add,add_comm]
      rfl

 theorem neg_inv :
  ∀ x : ℤ, x + (-x) = 0 :=
    by
      apply Quotient.ind
      intro x
      apply Quotient.sound
      simp [preInt_add,preInt_neg,nat_to_peano,add_comm]
      exact preRel_zero (x.fst + x.snd)
