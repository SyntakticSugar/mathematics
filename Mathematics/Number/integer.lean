/-
Module      : Integers
Description : Formal developement of ℤ.
Maintainer  : Robert Culling <rhsculling@pm.com>

This module constructs the integers as a quotient
of the product ℕ × ℕ under the relation:

  (a,b) ~ (c,d) ↔ a+d = c+b

Addition and multiplication are defined and
shown to descend to this quotient.
-/

-- Integers require importing ℕ
import Mathematics.Number.natural
open ℕ

-- ℤ is defined as the quotient of the following type ...
def preInt := ℕ × ℕ

def nat_to_preInt (n : Nat) : preInt :=
  (nat_to_peano n, zero)

-- ... by the following relation ...
def preRel (x y : preInt) : Prop :=
  x.fst + y.snd = y.fst + x.snd

-- ... which is shown below to be an equivalence relation.
theorem preRel_reflx :
  ∀ x : preInt, preRel x x :=
  by
    intro x
    unfold preRel
    rfl

theorem preRel_symm :
  ∀ x y : preInt, preRel x y → preRel y x :=
  by
    intro x y
    unfold preRel
    intro t₁
    exact Eq.symm t₁

theorem preRel_trans :
  ∀ x y z : preInt, preRel x y → preRel y z → preRel x z :=
  by
    intro x y z
    unfold preRel
    intro t₁ t₂
    have h₁ : x.fst + y.snd + z.snd = y.fst + x.snd + z.snd :=
      by congr
    rw [add_comm x.fst y.snd, add_comm y.fst,add_assoc x.snd, t₂] at h₁
    rw [<-add_assoc x.snd, add_comm x.snd] at h₁
    rw [add_comm y.snd,add_assoc x.fst, add_comm y.snd,<-add_assoc] at h₁
    -- have t₃ : x.fst + z.snd = z.fst + x.snd :=
    exact add_right_cancel y.snd (x.fst + z.snd) (z.fst + x.snd) h₁

-- Seems to be some type inference error that @-prefix bypasses.
instance preRel_equiv : Equivalence preRel :=
{ refl  := @preRel_reflx,
  symm  := @preRel_symm,
  trans := @preRel_trans }

-- We define the integers ℤ as the quotient by this equivalence.
def ℤ := Quotient (Setoid.mk preRel preRel_equiv)
