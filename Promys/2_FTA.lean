import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

theorem fta { a b c : ℤ } (a_dvd_bc : a ∣ b * c) (a_coprime_b : IsCoprime a b) : a ∣ c := by
  -- There is some k such that a * k = b * c
  -- BEZOUT'S!
  -- Substitute
  -- Factor c
  -- There is such an element!
  sorry
