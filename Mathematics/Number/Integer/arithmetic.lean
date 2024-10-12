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

 theorem add_neg :
  ∀ x : ℤ, x + (-x) = 0 :=
    by
      apply Quotient.ind
      intro x
      apply Quotient.sound
      simp [preInt_add,preInt_neg,nat_to_peano,add_comm]
      exact preRel_zero (x.fst + x.snd)

theorem neg_add :
  ∀ x : ℤ, (- x) + x = 0 :=
    by
      intro a
      rw [iadd_comm]
      apply add_neg

/-
  Theorems about multiplication on ℤ.
-/

theorem imul_zero :
  ∀ x : ℤ, x * 0 = 0 :=
    by
      apply Quotient.ind
      intro a
      apply Quotient.sound
      rfl

theorem zero_imul :
  ∀ x : ℤ, 0 * x = 0 :=
    by
      apply Quotient.ind
      intro a
      apply Quotient.sound
      simp [nat_to_peano,preInt_mul]
      rw [zero_mul,zero_mul,zero_add]
      rfl

theorem imul_one :
  ∀ x : ℤ, x * 1 = x :=
    by
      apply Quotient.ind
      intro a
      apply Quotient.sound
      simp [nat_to_peano]
      simp [preInt_mul]
      simp [mul_zero,add_zero,zero_add,mul_succ]
      rfl

theorem one_imul :
  ∀ x : ℤ, 1 * x = x :=
    by
      apply Quotient.ind
      intro a
      apply Quotient.sound
      simp [nat_to_peano, preInt_mul]
      simp [zero_mul,add_zero,succ_mul,zero_add]
      rfl

theorem imul_assoc :
  ∀ x y z : ℤ, (x * y) * z = x * (y * z) :=
    by
      apply Quotient.ind
      intro a
      apply Quotient.ind
      intro b
      apply Quotient.ind
      intro c
      apply Quotient.sound
      sorry
