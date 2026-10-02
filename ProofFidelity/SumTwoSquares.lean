/-
Copyright (c) 2026 ProofFidelity contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProofFidelity contributors
-/
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.NumberTheory.SumTwoSquares
import ProofFidelity.PrimesModFour

/-!
# Which primes are sums of two squares

The obstruction is elementary: a square is `0` or `1` mod `4`
(`Int.sq_emod_four`), so a sum of two squares is never `3` mod `4`.

The converse for primes is Fermat's Christmas theorem. Mathlib proves it as
`Nat.Prime.sq_add_sq`, using unique factorization in the Gaussian integers.
This file does not reprove that direction. It records the equivalence, with
the obstruction proved here and the representation cited from mathlib.

The prime `2 = 1 ^ 2 + 1 ^ 2` is the case people drop. It is `2` mod `4`,
so the right hypothesis is `p % 4 ≠ 3`, not `p % 4 = 1`.
-/

namespace ProofFidelity

/-- No integer congruent to `3` mod `4` is a sum of two integer squares.
The Lean remainder on `ℤ` is nonnegative, so this includes negative `n`
(`(-1) % 4 = 3`), which are excluded because a sum of squares is nonnegative. -/
theorem not_sum_two_squares_of_emod_four_eq_three {n : ℤ} (h : n % 4 = 3) :
    ¬∃ a b : ℤ, a ^ 2 + b ^ 2 = n := by
  intro ⟨a, b, hn⟩
  have hsum : (a ^ 2 + b ^ 2) % 4 = (a ^ 2 % 4 + b ^ 2 % 4) % 4 :=
    Int.add_emod (a ^ 2) (b ^ 2) 4
  rw [hn, h, Int.sq_emod_four, Int.sq_emod_four] at hsum
  have hres (x : ℤ) : x % 2 = 0 ∨ x % 2 = 1 := by
    have h0 : 0 ≤ x % 2 := Int.emod_nonneg x (by decide)
    have h1 : x % 2 < 2 := Int.emod_lt_of_pos x (by decide)
    omega
  rcases hres a with ha | ha <;> rcases hres b with hb | hb <;>
    simp [ha, hb] at hsum

theorem not_sum_two_squares_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) :
    ¬∃ a b : ℕ, a ^ 2 + b ^ 2 = n := by
  intro ⟨a, b, hn⟩
  exact not_sum_two_squares_of_emod_four_eq_three (n := n) (by exact_mod_cast h)
    ⟨a, b, by exact_mod_cast hn⟩

/-- A prime is a sum of two natural-number squares if and only if it is not
congruent to `3` modulo `4`. -/
theorem Prime.sum_two_squares_iff {p : ℕ} (hp : p.Prime) :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ p % 4 ≠ 3 := by
  constructor
  · intro h h3
    exact not_sum_two_squares_of_mod_four_eq_three h3 h
  · intro h
    have : Fact p.Prime := ⟨hp⟩
    exact Nat.Prime.sq_add_sq h

/-- There are infinitely many primes that are not sums of two squares. -/
theorem exists_prime_not_sum_two_squares_gt (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ ¬∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  obtain ⟨p, hpN, hp, hmod⟩ := exists_prime_mod_four_eq_three_gt N
  exact ⟨p, hpN, hp, not_sum_two_squares_of_mod_four_eq_three hmod⟩

end ProofFidelity
