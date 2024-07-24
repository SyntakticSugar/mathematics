/-
Module      : Natural Numbers
Description : Formal developement of the natural numbers.
Maintainer  : Robert Culling <rhsculling@pm.com>

  This module develops the formal theory of the natural
  numbers following the Peano axioms. Although what are
  considered "axioms" typically are now theorems derived
  from the foundational type theory. Specifically from
  the structure of inductive types.

  Theorems about the arithmetic of the natural numbers
  are proven. Enough to show that ℕ is an instance
  of the class of semirings.

-/
-- Open the namespace for the nat(ural) numbers here.
-- namespace nat

-- In the beginning, God created the integers...
inductive ℕ where
  | zero : ℕ
  | succ : ℕ → ℕ
  deriving Repr
-- ... everything else must be formally verified.

open ℕ

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
    -- injection t
    exact congrArg pred t

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

theorem add_zero :
  ∀ x : ℕ, x + zero = x :=
    by
      intro x
      rfl

theorem add_succ :
  ∀ x y : ℕ, x + succ y = succ (x + y) :=
    by
      intro x y
      rfl

theorem zero_add :
  ∀ x : ℕ, zero + x = x :=
    by
      intro x
      induction x with
      | zero      => rfl
      | succ x ih => rw [add_succ,ih]

theorem succ_add :
  ∀ x y : ℕ, (succ x) + y = succ (x + y) :=
    by
      intro x y
      induction y with
      | zero      => rfl
      | succ y ih => rw [add_succ,add_succ,ih]

theorem add_assoc :
  ∀ x y z : ℕ, (x + y) + z = x + (y + z) :=
    by
      intro x y z
      induction z with
      | zero      => rw [add_zero,add_zero]
      | succ z ih => rw [add_succ,add_succ,add_succ,ih]

theorem add_comm :
  ∀ x y : ℕ, x + y = y + x :=
  by
    intro x y
    induction x with
    | zero      => rw [zero_add,add_zero]
    | succ x ih => rw [add_succ,succ_add,ih]

theorem add_left_cancel :
  ∀ x y z : ℕ, x + y = x + z → y = z :=
  by
    intro x y z
    induction x with
    | zero      => rw [zero_add,zero_add]
                   intro t
                   exact t
    | succ x ih => rw [succ_add,succ_add]
                   intro h
                   have w₁ : x + y = x + z :=
                    succ_injective (x + y) (x + z) h
                   exact ih w₁

 theorem add_right_cancel :
  ∀ x y z : ℕ, y + x = z + x → y = z :=
  by
    intro x y z
    intro t₁
    rw [add_comm y x, add_comm z x] at t₁
    exact add_left_cancel x y z t₁

/-
  Theorems about multiplication on ℕ
-/

theorem mul_zero :
  ∀ x : ℕ, x * zero = zero :=
    by
      intro x
      rfl

theorem mul_succ :
  ∀ x y : ℕ, x * succ y = x * y + x :=
  by
    intro x y
    rfl

theorem zero_mul :
  ∀ x : ℕ, zero * x = zero :=
  by
    intro x
    induction x with
    | zero      => rfl
    | succ x ih => rw [mul_succ,ih,add_zero]

theorem succ_mul :
  ∀ x y : ℕ, (succ x) * y = (x * y) + y :=
  by
    intro x y
    induction y with
    | zero      => rw [mul_zero,mul_zero,add_zero]
    | succ y ih => rw [add_succ,mul_succ,add_succ,
                       mul_succ,ih,add_assoc,
                       add_comm y x,add_assoc]

theorem mul_distl_add :
  ∀ x y z : ℕ, x * (y + z) = (x * y) + (x * z) :=
  by
    intro x y z
    induction x with
    | zero      => rw [zero_mul,zero_mul,zero_mul,zero_add]
    | succ x ih => rw [succ_mul,succ_mul,succ_mul,ih,
                       add_assoc (x * y) y, <-add_assoc y (x *z),
                       add_comm y (x * z),add_assoc,add_assoc]

theorem mul_assoc :
  ∀ x y z : ℕ, (x * y) * z = x * (y * z) :=
  by
    intro x y z
    induction z with
    | zero      => rw [mul_zero,mul_zero,mul_zero]
    | succ z ih => rw [mul_succ,mul_succ,ih,mul_distl_add]

theorem mul_comm :
  ∀ x y : ℕ, x * y = y * x :=
  by
    intro x y
    induction x with
    | zero      => rw [zero_mul,mul_zero]
    | succ x ih => rw [succ_mul,mul_succ,ih]

theorem mul_distr_add :
  ∀ x y z : ℕ, (y + z) * x = (y * x) + (z * x) :=
  by
    intro x y z
    rw [mul_comm,mul_comm y x, mul_comm z x,mul_distl_add]

/-
  Lemma for equational reasoning in ℕ.
-/

theorem add_summands_cancel_left :
  ∀ x y : ℕ, x + y = x → y = zero :=
    by
      intro x y
      intro h₁
      have t₁ : x + y = x + zero :=
        calc
          x + y = x         := h₁
          _     = x + zero  := by rw [add_zero]
      exact add_left_cancel x y zero t₁

theorem add_summands_cancel_right :
  ∀ x y : ℕ, y + x = x → y = zero :=
    by
      intro x y
      intro h₁
      rw [add_comm] at h₁
      exact add_summands_cancel_left x y h₁

theorem add_bothsides_right :
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

-- Close the namespace for nat(ural numbers) here.
-- end nat
