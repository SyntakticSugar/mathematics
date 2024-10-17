/-
Module      : Monoids
Description : Base of the Algebraic Heirachy
Maintainer  : Robert Culling <rhsculling@pm.com>

  (Comm)(Add)Monoids are defined to be extensions
  of the corresponding (Comm)(Add)Semigroup classes.

-/

import Mathematics.Algebra.prelude
import Mathematics.Algebra.semigroup

open Semigroup

-- Monoids are semigroups with an identity.
class Monoid (α : Type u) extends hasOne α, Semigroup α where
  one_mul : ∀ a : α,  one * a = a
  mul_one : ∀ a : α,  a * one = a

class CommMonoid (α : Type u) extends Monoid α, CommSemigroup α

-- Additive monoids are additive semigroups with an identity.
class AddMonoid (α : Type u) extends hasZero α, AddSemigroup α where
  zero_add : ∀ a : α,  zero + a = a
  add_zero : ∀ a : α,  a + zero = a

class CommAddMonoid (α : Type u) extends AddMonoid α, CommAddSemigroup α
