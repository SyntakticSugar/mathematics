/-
Module      : Arithmetic.
Description : Fundamental arithmetic on ℤ
Maintainer  : Robert Culling <rhsculling@pm.com>

  ℤ, along with negation, +, * were constructed in:

    Mathematics.Number.Integer.construction

  This module proves basic theorems in the arithmetic
  of the integers. Once these are proved, one should not
  need to refer to the implementation details of ℤ
  as a quotient of ℕ × ℕ.
-/
import Mathematics.Number.Integer.construction
import Mathematics.Algebra.semiring
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
      simp [preInt_add,nat_to_peano,zero_add]
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
      simp [preInt_mul]
      simp [mul_distr_add,mul_distl_add]
      simp [mul_assoc]
      -- Work on first components.
      rw [add_assoc,
          <-add_assoc (a.snd *(b.snd*c.fst)),
          <-add_comm (a.fst * (b.snd * c.snd)),
          add_assoc,
          add_comm (a.snd * (b.snd * c.fst)) (a.snd * (b.fst * c.snd)),
          <-add_assoc]
      -- Work on second components.
      rw [add_assoc (a.fst * (b.fst * c.snd)),
          add_comm (a.snd *(b.snd * c.snd)),
          add_assoc (a.fst * (b.snd * c.fst)),
          <-add_assoc (a.fst * (b.fst * c.snd))]
      rfl

theorem imul_comm :
  ∀ x y : ℤ, x * y = y * x :=
    by
      -- This proof was almost entirely given by
      -- GitHub Copilot.
      apply Quotient.ind
      intro a
      apply Quotient.ind
      intro b
      apply Quotient.sound
      simp [preInt_mul]
      simp [mul_comm]
      rw [add_comm (a.fst * b.snd) (b.fst * a.snd)] -- it got this step wrong
      rfl

 theorem imul_distl_iadd :
    ∀ x y z : ℤ, x * (y + z) = (x * y) + (x * z) :=
      by
        apply Quotient.ind
        intro a
        apply Quotient.ind
        intro b
        apply Quotient.ind
        intro c
        apply Quotient.sound
        simp [preInt_mul, preInt_add]
        -- First component.
        rw [mul_distl_add, mul_distl_add]
        rw [add_assoc]
        rw [<-add_assoc (a.fst*c.fst)]
        rw [add_comm (a.fst*c.fst)]
        rw [add_assoc (a.snd*b.snd)]
        rw [<-add_assoc]
        -- Second component
        rw [mul_distl_add]
        rw [mul_distl_add]
        rw [add_assoc (a.fst*b.snd)]
        rw [<-add_assoc (a.fst*c.snd)]
        rw [add_comm (a.fst*c.snd)]
        rw [add_assoc (a.snd*b.fst)]
        rw [<-add_assoc (a.fst*b.snd)]
        rfl

-- Now enough of the basic properties of ℤ are proved, one shouldn't
-- have to descend all the way to the quotient space representation to
-- prove theorems. For example, right distributivity follows from
-- left distributivity and the commutativity of multiplication.
 theorem imul_distr_iadd :
    ∀ x y z : ℤ, (y + z) * x = (y * x) + (z * x) :=
      by
        intro a b c
        simp [imul_comm]
        apply imul_distl_iadd

instance : CommSemiring ℤ where
  one           := fromNat 1
  zero          := fromNat 0
  add_assoc     := iadd_assoc
  add_comm      := iadd_comm
  add_zero      := iadd_zero
  zero_add      := zero_iadd
  mul_one       := imul_one
  one_mul       := one_imul
  mul_assoc     := imul_assoc
  mul_distl_add := imul_distl_iadd
  mul_distr_add := imul_distr_iadd
  mul_comm      := imul_comm
