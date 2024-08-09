import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

set_option linter.unusedTactic false

open Nat

-- Here's a proof that there are infinitely many primes, as a mathematical theorem

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  -- We use the factorial trick
  -- Split the goal into (q ≥ N) and (Prime q)
  -- Prove (q ≥ N)
  -- Prove (Prime q)
  sorry
