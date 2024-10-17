/-
Module      : Algebra.Prelude
Description : Base of the type class system
Maintainer  : Robert Culling <rhsculling@pm.com>

  These few type classes are some of the base typeclasses
  of which many others will be extensions. These are
  some of the fundamental properties types can have.

  This typeclass system follows this paper closely:

  The Lean Mathematical Library
  https://arxiv.org/pdf/1910.09336

  Name of this module follows that of the module
  at the core of Lean4 definitions:

  src/Init/Prelude.lean

  For some reason "class Zero" from prelude is
  not available automatically. Nor is there a class
  for "One" in the Lean4 prelude.

  This library implements its own hasZero and hasOne.

-/

-- Class of types with some distinguished "zero" term.
class hasZero (α : Type u) where
  -- This class acts as lean4/src/init/prelude.lean "Zero" class.
  zero : α

-- Class of types with some distinguished "one" or "unit" term.
class hasOne (α : Type u) where
  one : α

-- Class of types for which distinguished "zero", "unit" are distinct.
class zero_ne_one (α : Type u) extends hasZero α, hasOne α where
  zero_ne_one : ¬(zero = one)
