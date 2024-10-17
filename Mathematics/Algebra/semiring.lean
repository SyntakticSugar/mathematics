/-
Module      : Semirings
Description : Type class for Rings and Semirings
Maintainer  : Robert Culling <rhsculling@pm.com>

  This type class systems follows that described here:

  The Lean Mathematical Library
  https://arxiv.org/pdf/1910.09336

  as well as that defined in Lean4 and Mathlib4.
-/

import Mathematics.Algebra.monoid

class Semiring (α : Type u) extends Monoid α, CommAddMonoid α where
  mul_distl_add : ∀ x y z : α, x * (y + z) = x * y + x * z
  mul_distr_add : ∀ x y z : α, (y + z) * x = y * x + z * x

class CommSemiring (α : Type u) extends Semiring α, CommMonoid α
