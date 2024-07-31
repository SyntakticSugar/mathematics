/-
Module      : Monoids
Description : Base of the Algebraic Heirachy
Maintainer  : Robert Culling <rhsculling@pm.com>

  (Comm)(Add)Monoids are defined to be extensions
  of the corresponding (Comm)(Add)Semigroup classes.

-/

import Mathematics.Algebra.semigroup

open Semigroup

class Monoid (α : Type u) extends Semigroup α  where
  one : α
  one_mul : ∀ a : α,  one * a = a
  mul_one : ∀ a : α,  a * one = a

class CommMonoid (α : Type u) extends CommSemigroup α  where
  one : α
  one_mul : ∀ a : α,  one * a = a

class AddMonoid (α : Type u) extends AddSemigroup α  where
  zero : α
  zero_add : ∀ a : α,  zero + a = a
  add_zero : ∀ a : α,  a + zero = a

class CommAddMonoid (α : Type u) extends CommAddSemigroup α  where
  zero : α
  zero_add : ∀ a : α,  zero + a = a
