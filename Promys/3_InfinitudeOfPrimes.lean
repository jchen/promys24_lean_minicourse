import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

set_option linter.unusedTactic false

open Nat

-- here's a proof that there are infinitely many primes, as a mathematical theorem

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  intro N
  let F := N ! + 1
  let q := minFac F
  use q

  have n_fac_ge_0 : N ! > 0 := factorial_pos N
  have f_ne_1 : F ≠ 1 := by linarith
  have q_prime : Nat.Prime q := minFac_prime f_ne_1

  -- Split the goal into (q ≥ N) and (Prime q)
  apply And.intro

  -- Prove (q ≥ N)
  {
    -- We prove by contradiction, let's say ¬ q ≥ N
    by_contra q_ngeq_N
    -- So that means q < N
    have q_leq_N : q ≤ N := by linarith
    -- q | F since q is the minimum prime factor of F
    have q_dvd_F : q ∣ F := minFac_dvd F
    -- q also divides N! since q ≤ N
    have q_dvd_N_fac : q ∣ N ! := Iff.mpr (Prime.dvd_factorial (minFac_prime f_ne_1)) q_leq_N
    -- q | 1 since q | F and q | N!, and it divides any linear combination of the two
    have q_dvd_1 : q ∣ 1 := Iff.mp (Nat.dvd_add_right q_dvd_N_fac) q_dvd_F
    -- q is prime, so it cannot divide 1
    apply Nat.Prime.not_dvd_one q_prime q_dvd_1
  }
  -- Prove (Prime q)
  {
    exact q_prime
  }

  done

-- But really, this is a proof about a *program* caled `biggerPrime`!

def biggerPrime (N : ℕ) : ℕ := Nat.minFac (N ! + 1)

#check @biggerPrime

#eval biggerPrime 7

theorem biggerPrimeIsPrime : ∀ N, Nat.Prime (biggerPrime N) := by
  intro N
  let F := N ! + 1
  have n_fac_ge_0 : N ! > 0 := factorial_pos N
  have f_ne_1 : F ≠ 1 := by linarith
  exact minFac_prime f_ne_1
  done

theorem biggerPrimeIsBigger : ∀ N, biggerPrime N ≥ N := by
  -- Same thing as above
  intro N
  let F := N ! + 1
  have n_fac_ge_0 : N ! > 0 := factorial_pos N
  have f_ne_1 : F ≠ 1 := by linarith

  by_contra q_ngeq_N
  have q_leq_N : biggerPrime N ≤ N := by linarith
  have q_dvd_F : biggerPrime N ∣ N ! + 1 := minFac_dvd (N ! + 1)
  have q_dvd_N_fac : biggerPrime N ∣ N ! := Iff.mpr (Prime.dvd_factorial (minFac_prime f_ne_1)) q_leq_N
  have q_dvd_1 : biggerPrime N ∣ 1 := Iff.mp (Nat.dvd_add_right q_dvd_N_fac) q_dvd_F
  apply Nat.Prime.not_dvd_one (biggerPrimeIsPrime N) q_dvd_1
  done

-- we can use our verified program to prove our original theorem
theorem infinitude_of_primes2 : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  intro N
  use biggerPrime N
  apply And.intro
  { exact biggerPrimeIsBigger _ }
  { exact biggerPrimeIsPrime _ }
  done
