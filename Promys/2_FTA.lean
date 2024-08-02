import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

theorem fta { a b c : ℤ } (a_dvd_bc : a ∣ b * c) (a_coprime_b : IsCoprime a b) : a ∣ c := by
  -- There is some k such that a * k = b * c
  obtain ⟨k, hk⟩ := a_dvd_bc
  -- BEZOUT'S!
  obtain ⟨x, y, h⟩ := a_coprime_b
  have hc : x * a * c + y * (b * c) = 1 * c := by rw [←h]; ring
  -- Substitute hk into hc
  rw [hk] at hc
  -- Factor c
  have ha : a * (x * c + y * k) = c := by linarith
  -- There is such an element! (x * c + y * k)
  existsi (x * c + y * k)
  tauto
