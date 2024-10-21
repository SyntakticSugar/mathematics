/-
Module      : Permutations
Description : Implementing Permutations
Maintainer  : rhsculling @ pm dot com

  My implementation of code related to permutations
  and sorting lists. Following the  Lean4 std library
  code setout here:

  ...Lean4/src/Init/Data/List/Basic.lean, and
  ...Lean4/src/Init/Data/List/Perm.lean

  and the Coq stdlib documentation setout at this link:

  https://coq.inria.fr/doc/v8.9/stdlib/index.html

  Working towards the verification of a sorting
  algorithm like Merge Sort.

  Note :: second entry in the Coq stdlib inductive definition
  of permutation is confusing. Seems like the implication is
  the converse of the correct one? Or I am missing something...
  Lean4 has it the way I expected it.

-/

inductive Permutation : {A : Type u} -> List A -> List A -> Prop where
  -- Empty list a permutation of itself.
  | nil_perm                               : Permutation [] []
  -- Cons-ing equal terms preserves permutations.
  | perm_cons (x : A) {l₁ l₂ : List A}     :
      Permutation l₁ l₂ -> Permutation (x :: l₁) (x :: l₂)
  -- Swapping first two preserves permutations.
  | perm_swap (x y : A) (l : List A)       : Permutation (y :: x :: l) (x :: y :: l)
  -- Permutatations of permutations are permutations.
  | perm_trans {l₁ l₂ l₃ : List A} :
      Permutation l₁ l₂ → Permutation l₂ l₃ → Permutation l₁ l₃

open List
open Permutation

-- Permutation is an equivalence relation:
theorem permutation_reflexive : ∀ l : List A,
  Permutation l l :=
    by
      intro x
      induction x with
      | nil           => exact nil_perm
      | cons x xs ih  => exact (perm_cons x) ih

theorem permutation_symmetric : ∀ l l' : List A,
  Permutation l l' -> Permutation l' l :=
    by
      intro x y h
      -- Induction on the nature of the witness to
      -- the fact l l' are permutations of each other.
      induction h with
      | nil_perm                  => exact nil_perm
      | perm_cons _ _ ih          => exact perm_cons _ ih
      | perm_swap a b l           => exact (perm_swap b a l)
      | perm_trans _ _ ih₁ ih₂    => exact (perm_trans ih₂ ih₁)

theorem permutation_transitive : ∀ l l' l'' : List A,
  Permutation l l' -> Permutation l' l'' -> Permutation l l'' :=
    by
      intro x y z t₁ t₂
      exact perm_trans t₁ t₂
