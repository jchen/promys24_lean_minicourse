import Mathlib.Data.Nat.Defs

/-
Everything in Lean has a type! We can check its type using #type
-/

#check ℕ
#check ℤ

#check Empty
#check Unit
#check Bool

#check ℕ → ℤ
#check ℤ → ℕ
#check Bool → ℕ → ℤ
#check (Bool → ℕ) → ℤ
#check ℕ → (Bool → ℕ) → ℤ

#check fun x : ℕ ↦ x
#check fun f : ℕ → ℕ ↦ fun g : ℕ → ℕ ↦ fun h : ℕ → ℕ ↦
  fun x : ℕ ↦ h (g (f x))
#check fun (f g h : ℕ → ℕ) (x : ℕ) ↦ h (g (f x))

/-
What about the type of statements?
-/

#check 1 < 2

-- Type checking is not evaluation!
#check 2 < 1

/-
Backwards Proofs
-/

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
