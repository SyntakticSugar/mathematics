/-
Module      : Groups
Description : Definitions of (Add)(Comm)Groups
Maintainer  : Robert Culling <rhsculling@pm.com>

  (Comm)(Add)Groups are defined to be extensions
  of the corresponding (Comm)(Add)Monoid classes.

-/

import Mathematics.Algebra.monoid

open Monoid

class Group (α : Type u) extends Monoid α where
  inv : α → α
  inv_mul : ∀ a : α, (inv a) * a = one
  mul_inv : ∀ a : α, a * (inv a) = one

class CommGroup (α : Type u) extends CommMonoid α where
  inv : α → α
  inv_mul : ∀ a : α, (inv a) * a = one

class AddGroup (α : Type u) extends AddMonoid α where
  inv : α → α
  inv_add : ∀ a : α, (inv a) + a = zero
  add_inv : ∀ a : α, a + (inv a) = zero

class CommAddGroup (α : Type u) extends AddMonoid α where
  inv : α → α
  inv_mul : ∀ a : α, (inv a) + a = zero
