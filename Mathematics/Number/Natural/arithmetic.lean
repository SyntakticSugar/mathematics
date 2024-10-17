/-
Module      : Natural Numbers
Description : Formal developement of the natural numbers.
Maintainer  : Robert Culling <rhsculling@pm.com>

  This module develops the formal theory of the natural
  numbers following the Peano axioms. Although what we
  consider "axioms" typically are now theorems derived
  from the foundational type theory. Specifically from
  the structure of inductive types.

  Theorems about the arithmetic of the natural numbers
  are proven. Enough to show that ℕ is an instance
  of the class of semirings.

-/

import Mathematics.Algebra.semiring

-- In the beginning, God created the integers...
inductive ℕ where
  | zero : ℕ
  | succ : ℕ → ℕ
  deriving Repr
-- ... everything else must be formally verified.

open ℕ

theorem succ_not_zero :
  ∀ x : ℕ, succ x ≠ zero :=
  by
    intro a
    intro h₁
    injection h₁

-- The following allows for the use of numeral
-- representations of terms in ℕ.
def nat_to_peano (n : Nat) : ℕ :=
  match n with
  | 0     => zero
  | n + 1 => succ (nat_to_peano n)

instance : OfNat ℕ n where
  ofNat := nat_to_peano n

-- The first two Peano axioms are in fact
-- theorems deduced from the structure of
-- inductive definitions of types.
def pred (m : ℕ) : ℕ :=
  match m with
    | zero   => zero
    | succ n => n

theorem succ_injective :
  ∀ m n : ℕ, succ m = succ n → m = n :=
  by
    intro m n
    intro t
    injection t
    --exact congrArg pred t

theorem zero_neq_one :
  zero ≠ (succ zero) :=
  λ e : zero = succ zero => by injection e

-- The arithmetic axioms are used to define
-- addition and multiplication on ℕ
def add (m n : ℕ) : ℕ :=
  match n with
    | zero    => m
    | succ x  => succ (add m x)

instance : Add ℕ where
  add := add

def mul (m n : ℕ) : ℕ :=
  match n with
    | zero    => zero
    | succ x  => (mul m x) + m

instance : HMul ℕ ℕ ℕ where
  hMul := mul

-- Lean has the final axiom, induction, defined
-- for all inductively defined types.

/-
  Theorems about addition on ℕ
-/

 theorem nadd_zero :
  ∀ x : ℕ, x + zero = x :=
    by
      intro x
      rfl

 theorem nadd_succ :
  ∀ x y : ℕ, x + succ y = succ (x + y) :=
    by
      intro x y
      rfl

theorem zero_add_induction (t : zero + x = x) :
   zero + succ x = succ x :=
    by
      rw [nadd_succ, t]

 theorem zero_nadd :
  ∀ x : ℕ, zero + x = x :=
    by
      intro x
      induction x with
      | zero      => rfl
      | succ x ih => exact (zero_add_induction ih)

 theorem succ_nadd :
  ∀ x y : ℕ, (succ x) + y = succ (x + y) :=
    by
      intro x y
      induction y with
      | zero      => rfl
      | succ y ih => rw [nadd_succ,nadd_succ,ih]

 theorem nadd_assoc :
  ∀ x y z : ℕ, (x + y) + z = x + (y + z) :=
    by
      intro x y z
      induction z with
      | zero      => rw [nadd_zero,nadd_zero]
      | succ z ih => rw [nadd_succ,nadd_succ,nadd_succ,ih]

 theorem nadd_comm :
  ∀ x y : ℕ, x + y = y + x :=
  by
    intro x y
    induction x with
    | zero      => rw [zero_nadd,nadd_zero]
    | succ x ih => rw [nadd_succ,succ_nadd,ih]

 theorem nadd_left_cancel :
  ∀ x y z : ℕ, x + y = x + z → y = z :=
  by
    intro x y z
    induction x with
    | zero      => rw [zero_nadd,zero_nadd]
                   intro t
                   exact t
    | succ x ih => rw [succ_nadd,succ_nadd]
                   intro h
                   have w₁ : x + y = x + z :=
                    succ_injective (x + y) (x + z) h
                   exact ih w₁

  theorem nadd_right_cancel :
  ∀ x y z : ℕ, y + x = z + x → y = z :=
  by
    intro x y z
    intro t₁
    rw [nadd_comm y x, nadd_comm z x] at t₁
    exact nadd_left_cancel x y z t₁

/-
  Theorems about multiplication on ℕ
-/

 theorem nmul_zero :
  ∀ x : ℕ, x * zero = zero :=
    by
      intro x
      rfl

 theorem nmul_succ :
  ∀ x y : ℕ, x * succ y = x * y + x :=
  by
    intro x y
    rfl

 theorem zero_nmul :
  ∀ x : ℕ, zero * x = zero :=
  by
    intro x
    induction x with
    | zero      => rfl
    | succ x ih => rw [nmul_succ,ih,nadd_zero]

 theorem succ_nmul :
  ∀ x y : ℕ, (succ x) * y = (x * y) + y :=
  by
    intro x y
    induction y with
    | zero      => rw [nmul_zero,nmul_zero,nadd_zero]
    | succ y ih => rw [nadd_succ,nmul_succ,nadd_succ,
                       nmul_succ,ih,nadd_assoc,
                       nadd_comm y x,nadd_assoc]

theorem nmul_one :
  ∀ x : ℕ, x * (succ zero) = x :=
    by
      intro a
      rw [nmul_succ,nmul_zero,zero_nadd]

 theorem nmul_distl_nadd :
  ∀ x y z : ℕ, x * (y + z) = (x * y) + (x * z) :=
  by
    intro x y z
    induction x with
    | zero      => rw [zero_nmul,zero_nmul,zero_nmul,zero_nadd]
    | succ x ih => rw [succ_nmul,succ_nmul,succ_nmul,ih,
                       nadd_assoc (x * y) y, <-nadd_assoc y (x *z),
                       nadd_comm y (x * z),nadd_assoc,nadd_assoc]

 theorem nmul_assoc :
  ∀ x y z : ℕ, (x * y) * z = x * (y * z) :=
  by
    intro x y z
    induction z with
    | zero      => rw [nmul_zero,nmul_zero,nmul_zero]
    | succ z ih => rw [nmul_succ,nmul_succ,ih,nmul_distl_nadd]

 theorem nmul_comm :
  ∀ x y : ℕ, x * y = y * x :=
  by
    intro x y
    induction x with
    | zero      => rw [zero_nmul,nmul_zero]
    | succ x ih => rw [succ_nmul,nmul_succ,ih]

theorem one_nmul :
  ∀ x : ℕ, (succ zero) * x = x :=
    by
      intro a
      rw [nmul_comm]
      apply nmul_one

 theorem nmul_distr_nadd :
  ∀ x y z : ℕ, (y + z) * x = (y * x) + (z * x) :=
  by
    intro x y z
    rw [nmul_comm,nmul_comm y x, nmul_comm z x,nmul_distl_nadd]

/-
  Lemma for equational reasoning in ℕ.
-/

theorem nadd_summands_cancel_left :
  ∀ x y : ℕ, x + y = x → y = zero :=
    by
      intro x y
      intro h₁
      have t₁ : x + y = x + zero :=
        calc
          x + y = x         := h₁
          _     = x + zero  := by rw [nadd_zero]
      exact nadd_left_cancel x y zero t₁

theorem nadd_summands_cancel_right :
  ∀ x y : ℕ, y + x = x → y = zero :=
    by
      intro x y
      intro h₁
      rw [nadd_comm] at h₁
      exact nadd_summands_cancel_left x y h₁

theorem nadd_bothsides_right :
  ∀ x y z : ℕ, x = y → x + z = y + z :=
  by
    intro x y z
    intro h₁
    congr
    -- Could do induction...
    -- induction z with
    -- | zero      => rw [add_zero, add_zero,h₁]
    -- | succ k ih => rw [add_succ, add_succ, ih]

theorem add_bothsides_left :
  ∀ x y z : ℕ, x = y → z + x = z + y :=
  by
    intro x y z
    intro h₁
    congr

/-
  Instantiate algebraic classes so that the same name
  for the analogous theorems across types can be used.

  E.g. add_comm will be the name of a theorem for each
  of the types ℕ ℤ ℚ ℝ ℂ etc. Each of these will be
  instances of particularly type classes. This fact allows
  for overloading theorem names.
-/

instance : CommSemiring ℕ where
  one := succ zero
  zero := zero
  add_assoc := nadd_assoc
  add_comm := nadd_comm
  add_zero := nadd_zero
  zero_add := zero_nadd
  mul_one := nmul_one
  one_mul := one_nmul
  mul_assoc := nmul_assoc
  mul_distl_add := nmul_distl_nadd
  mul_distr_add := nmul_distr_nadd
  mul_comm := nmul_comm
