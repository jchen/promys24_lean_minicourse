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
def h x := -1 * x
#check h
-- A (ℤ → ℤ) means it takes an integer and returns an integer.

-- We might write it like this
#check (λ x ↦ -1 * x)

-- Types must match! What if we tried to pass it a Cartesian coordinate? (type error)
def p := (1, 2)
#check h p

-- We can have multiple arguments
def g x y := x * y + 4
#check g

/-Type of g
In LEAN, a function with multiple arguments is treated as a sequence of functions, each taking one argument. So, the type ℕ → ℕ → ℕ means:

g is a function that takes a natural number x (of type ℕ) and returns another function.
This returned function then takes another natural number y and produces the final output, which is also a natural number (of type ℕ).
So, the full type ℕ → ℕ → ℕ describes a function that takes two natural numbers and returns a natural number.

This matches the definition of g because:

x and y are natural numbers.
x * y + 4 is a natural number (since multiplication and addition of natural numbers result in natural numbers).-/

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

/-This defines a function named exists_diophantine_solutions that takes two arguments, x and y, and returns a proposition.

What is the Function Doing?
The function describes a Diophantine equation: a * x + b * y = 1, where a and b are integers.
The expression ∃ a b, a * x + b * y = 1 reads as "there exist integers a and b such that a * x + b * y = 1."
Therefore, exists_diophantine_solutions x y is a proposition that asserts the existence of such integers a and b for given x and y.

Hence it has a type of N→ N → prop -/

axiom bezout {x y} : Nat.gcd x y = 1 → exists_diophantine_solutions x y
#check bezout
/-In Lean, an axiom is a fundamental assertion that is assumed to be true without proof. The line of code you provided introduces an axiom named bezout, which represents Bézout's identity, a key theorem in number theory.-/
-- If I have a proof that Nat.gcd x y = 1

theorem proof_of_5_7_coprime : Nat.gcd 5 7 = 1 := by trivial
/-by simp-/
#check proof_of_5_7_coprime
/-:= by trivial: This is the proof of the theorem. The by trivial tactic tells Lean to use a simple proof strategy. In this case, Lean knows that 5 and 7 are prime numbers and that their GCD is 1, so it can easily conclude that Nat.gcd 5 7 = 1 is true without requiring a more complex proof.-/

-- I can apply it to Bezout's Lemma to get a proof that there exists solutions to diophantine equation 5a + 7b = 1
#check bezout proof_of_5_7_coprime

-- Generally, we can't prove things using 'trivial'. We generally prove things in Proof mode. A view pops up on the right with our current hypotheses at all times and the goal of the statement we are trying to prove

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
  by
    intro ha
    /-This introduces a new hypothesis ha, which assumes that a is true. In Lean, intro is used to assume the premise of an implication when trying to prove the conclusion.
The goal now is to prove c under the assumption that a is true.-/
    apply hbc
    /-This step applies the assumption hbc : b → c. The goal is now to prove b because hbc tells us that if b is true, then c will follow.
So the goal shifts from proving c to proving b.-/
    apply hab
    /-This step applies the assumption hab : a → b. Now, the goal is to prove a because hab tells us that if a is true, then b will follow.
So the goal shifts from proving b to proving a.-/
    apply ha
    /-Finally, apply ha is used to directly apply the hypothesis ha, which is the assumption that a is true.
This satisfies the goal of proving a, and thus, by the previous steps, b is proven, and then c is proven as a result.-/

/-This is a formalization of the transitivity of implication in logic. If a leads to b, and b leads to c, then a should lead to c.-/

theorem fst_of_two_props_exact (a b : Prop) (ha : a) (hb : b) :
  a :=
  by exact ha
/-What Does the Theorem Claim?
The theorem fst_of_two_props_exact claims that if:

a is true (i.e., ha : a), and
b is true (i.e., hb : b),
-/
  /-The name "fst_of_two_props_exact" suggests that it's focusing on the "first" proposition a and proving it.-/

theorem fst_of_two_props_assumption (a b : Prop)
    (ha : a) (hb : b) :
  a :=
  by assumption

/-This theorem is almost identical to fst_of_two_props_exact but uses a different proof technique. While exact ha explicitly names the assumption being used, assumption automatically finds the relevant assumption, making it a convenient and often used tactic in proofs where the goal is directly one of the available assumptions.-/
-- Introduction and Elimination Rules

theorem And_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    /- The And.right tactic is used to extract the second component of the conjunction hab, which is b.-/
    exact hab
    apply And.left
    exact hab

  /-it proves that the logical conjunction (AND) operation is commutative. This means that if a ∧ b is true, then b ∧ a is also true.-/

theorem And_swap_braces :
  ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    { exact And.right hab }
    { exact And.left hab }

    /-commutativity of conjunction: if a ∧ b is true, then b ∧ a is also true-/

opaque f : ℕ → ℕ
/-This declares a function f from natural numbers (ℕ) to natural numbers (ℕ) but marks it as opaque.
opaque: In Lean, an opaque definition is one whose implementation is hidden. When a definition is marked as opaque, its internal workings are not revealed, which means you cannot see or reason about its implementation details directly. You can only use it in proofs based on its type.-/

theorem f5_if (h : ∀n : ℕ, f n = n) :
  f 5 = 5 :=
  by exact h 5

  /-This proof is straightforward because the assumption h already guarantees that f behaves as an identity function, and applying this assumption to the specific case of 5 directly achieves the goal.-/

theorem Or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
  by
    intro hab
    apply Or.elim hab
    { intro ha
      exact Or.inr ha }
    { intro hb
      exact Or.inl hb }

      /-it proves that logical disjunction (OR) is commutative. This means that if a ∨ b (i.e., either a or b is true) holds, then b ∨ a (i.e., either b or a is true) also holds.-/

theorem modus_ponens (a b : Prop) :
  (a → b) → a → b :=
  by
    intro hab ha
    apply hab
    exact ha
    /-intro hab ha:

This introduces two assumptions:
hab is the hypothesis that a → b (if a then b).
ha is the hypothesis that a is true.
apply hab:

The apply tactic is used to use the hypothesis hab in the goal. Since hab is a → b, applying hab requires proving a to get b.
At this point, the goal becomes to prove b using hab and ha.
exact ha:

The exact tactic is used to directly apply the hypothesis ha to the goal. Since ha provides a, and we need a to apply hab, exact ha completes the proof by providing the value of a needed to use hab.-/

theorem Not_Not_intro (a : Prop) :
  a → ¬¬ a :=
  by
    intro ha hna
    apply hna
    exact ha

/-Proof Strategy: The proof uses the intro tactic to introduce the assumptions. Then:
It applies hna (which assumes ¬ a) to show that this assumption leads to a contradiction, proving ¬¬ a.
It uses exact ha to provide the necessary proof that a is true, thus demonstrating that ¬ a cannot hold.-/

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) :
  a = c :=
  by
    rw [hab]
    rw [hcb]

/-Theorem Statement: The theorem Eq_trans_symm_rw asserts that if a is equal to b and c is equal to b, then a must be equal to c. This leverages the transitivity and symmetry of equality.
Proof Strategy: The proof uses the rw (rewrite) tactic to apply the given equalities:
First, it rewrites a as b in the goal, which changes the goal to b = c.
Then, it rewrites b as c in the new goal, transforming it into c = c, which is always true.-/

theorem a_proof_of_negation (a : Prop) :
  a → ¬¬ a :=
  by
    rw [Not]
    rw [Not]
    intro ha
    intro hna
    apply hna
    exact ha
/-Theorem Statement: The theorem a_proof_of_negation asserts that if a proposition a is true, then its double negation ¬¬ a is also true. This demonstrates the principle of double negation in classical logic.

Proof Strategy: The proof uses the rw (rewrite) tactic to transform ¬¬ a into ¬ (a → False). It then introduces the assumptions:
ha provides the truth of a.
hna provides the assumption that ¬ a is false, which translates to a being true.
Finally, it applies hna and uses exact ha to show that a satisfies the requirement.-/
-- How do we prove this?
theorem funny_proof (a : Prop) :
  ¬¬ a → a :=
  by
    sorry

-- (left as an exercise)
