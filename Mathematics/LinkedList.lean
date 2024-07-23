inductive LinkedList (α : Type u) where
  | nil   : LinkedList α
  | cons  : α → LinkedList α → LinkedList α
  deriving Repr

open LinkedList

-- Appending lists together.
def append (as bs : LinkedList α) : LinkedList α :=
  match as with
  | nil        => bs
  | cons a ass => cons a (append ass bs)

theorem nil_append (as : LinkedList α) :
  append nil as = as :=
  by
    rfl

theorem cons_append (a : α) (as bs : LinkedList α) :
  append (cons a as) bs = cons a (append as bs) :=
  by
    rfl

theorem append_nil (as : LinkedList α) :
  append as nil = as :=
  by
    induction as with
    | nil           => rfl
    | cons a ass ih => rw [cons_append, ih]

theorem append_assoc (as bs cs : LinkedList α) :
  append (append as bs) cs = append as (append bs cs) :=
  by
    induction as with
    | nil           => rw [nil_append, nil_append]
    | cons a ass ih => rw [cons_append,cons_append,ih,<-cons_append]

def length {α : Type u} (as : LinkedList α) : Nat :=
  match as with
  | nil        => 0
  | cons _ ass => 1 + (length ass)

theorem length_cons (a : α) (as : LinkedList α) :
  length (cons a as) = 1 + length as :=
  by
    rfl

theorem length_append (as bs : LinkedList α) :
  length (append as bs) = (length as) + (length bs) :=
  by
    induction as with
    | nil           => rw [nil_append,length,Nat.zero_add]
    | cons a ass ih => rw [cons_append,length_cons,ih,length,Nat.add_assoc]

-- Reversing a list.
def snoc (as : LinkedList α) (a : α) : LinkedList α :=
  match as with
  | nil         => cons a nil
  | (cons x xs) => cons x (snoc xs a)

theorem length_snoc : ∀ (as : LinkedList α) (a : α),
  length (snoc as a) = 1 + length (as) :=
  by
    intro l a
    induction l with
    | nil          => rw [snoc, length, length, length]
    | cons x xs ih => rw [snoc, length, ih, length]

def reverse (as : LinkedList α) : LinkedList α :=
  match as with
  | nil       => nil
  | cons x xs => snoc (reverse xs) x

theorem rev_snoc (as : LinkedList α) (a : α) :
  reverse (snoc as a) = cons a (reverse as) :=
  by
    induction as with
    | nil          => rw [snoc, reverse, reverse, reverse, snoc]
    | cons x xs ih => rw [snoc, reverse, ih, snoc, reverse]

theorem revrev : ∀ as : LinkedList α,
  reverse (reverse as) = as :=
  by
    intro l
    induction l with
    | nil          => rfl
    | cons x xs ih => rw [reverse, rev_snoc,ih]

theorem length_reverse : ∀ as : LinkedList α,
  length (reverse as) = length as :=
  by
    intro l
    induction l with
    | nil          => rw [reverse]
    | cons x xs ih => rw [reverse, length_snoc, length, ih]

-- Defining this predicate, one can write and TEST
-- Various sorting algorithms!
def sorted (as : List Nat) : Prop :=
  match as with
  | []              => True
  | [_]             => True
  | (x :: y :: xs)  => (x ≤ y) ∧ sorted (y :: xs)

example : sorted [1,2,3] :=
  by
    unfold sorted
    apply And.intro
    exact Nat.le_succ 1
    unfold sorted
    apply And.intro
    exact Nat.le_succ 2
    unfold sorted
    exact True.intro
