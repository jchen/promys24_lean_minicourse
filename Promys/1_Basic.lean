import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.Prime.Defs

/-
EVERYTHING in Lean has a type! We can check its type using #type
-/

-- Numbers
#check 1
#check 0
#check 2.3

-- Cartesian Coordinates
#check (1, 2)

-- Sets
#check {x : ℤ | ∃ k, x = 2 * k}

-- We can define functions on numbers
def f x := -1 * x
#check f
-- A (ℤ → ℤ) means it takes an integer and returns an integer.

-- We might write it like this
#check (λ x ↦ -1 * x)

-- Types must match! What if we tried to pass it a Cartesian coordinate? (type error)
def p := (1, 2)
#check f p

-- We can have multiple arguments
def g x y := x * y + 4
#check g

-- Types have types too! Types have type 'Type'.
#check ℕ
#check ℤ

-- Wait...
#check Type
#check Type 1

-- What about the type of statements?
-- Statements are typed 'Prop' for proposition.
#check 1 < 2
#check ∀ (x : ℤ), ∃ y, y ∣ x
#check True
#check False

-- Type checking is not evaluation! Incorrect statements can exist.
#check 2 < 1
#check 2 < 1 → 1 < 0

-- Something can have a type that is the proposition. That is a _proof_ of said proposition.

def exists_diophantine_solutions x y := ∃ a b, a * x + b * y = 1
#check exists_diophantine_solutions

axiom bezout {x y} : Nat.gcd x y = 1 → exists_diophantine_solutions x y
#check bezout

-- If I have a proof that Nat.gcd x y = 1
theorem proof_of_5_7_coprime : Nat.gcd 5 7 = 1 := by trivial
#check proof_of_5_7_coprime

-- I can apply it to Bezout's Lemma to get a proof that there exists solutions to diophantine equation 5a + 7b = 1
#check bezout proof_of_5_7_coprime

-- Generally, we can't prove things using 'trivial'. We generally prove things in Proof mode. A view pops up on the right with our current hypotheses at all times and the goal of the statement we are trying to prove

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
  by
    intro ha
    apply hbc
    apply hab
    apply ha

theorem fst_of_two_props_exact (a b : Prop) (ha : a) (hb : b) :
  a :=
  by exact ha

theorem fst_of_two_props_assumption (a b : Prop)
    (ha : a) (hb : b) :
  a :=
  by assumption

-- Introduction and Elimination Rules

theorem And_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

theorem And_swap_braces :
  ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    { exact And.right hab }
    { exact And.left hab }

opaque f : ℕ → ℕ

theorem f5_if (h : ∀n : ℕ, f n = n) :
  f 5 = 5 :=
  by exact h 5

theorem Or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
  by
    intro hab
    apply Or.elim hab
    { intro ha
      exact Or.inr ha }
    { intro hb
      exact Or.inl hb }

theorem modus_ponens (a b : Prop) :
  (a → b) → a → b :=
  by
    intro hab ha
    apply hab
    exact ha

theorem Not_Not_intro (a : Prop) :
  a → ¬¬ a :=
  by
    intro ha hna
    apply hna
    exact ha

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) :
  a = c :=
  by
    rw [hab]
    rw [hcb]

theorem a_proof_of_negation (a : Prop) :
  a → ¬¬ a :=
  by
    rw [Not]
    rw [Not]
    intro ha
    intro hna
    apply hna
    exact ha
