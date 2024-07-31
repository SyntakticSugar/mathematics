/-
Module      : Semigroups
Description : Base of the Algebraic Heirachy
Maintainer  : Robert Culling <rhsculling@pm.com>

  This the first of a few files building the hierachy
  of strucutres from abstract algebra. These are encoded
  as type classes. Inspired by and following the
  exposition in the following paper:

  The Lean Mathematical Library
  https://arxiv.org/pdf/1910.09336

  Group ⊆ Monoid ⊆ Semigroup ⊆ Magma = HMul

  Magma are types with a binary operation on them.
  In Lean 4 these are encoded as instances of the
  type class HMul, or just Mul.

-/

class Semigroup (α : Type u) extends HMul α α α where
  mul_assoc : ∀ a b c : α, (a * b) * c =  a * (b * c)

class CommSemigroup (α : Type u) extends Semigroup α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddSemigroup (α : Type u) extends Add α where
  add_assoc : ∀ a b c : α, (a + b) + c =  a + (b + c)

class CommAddSemigroup (α : Type u) extends AddSemigroup α where
  add_comm : ∀ a b : α, a + b = b + a
