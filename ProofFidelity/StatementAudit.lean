/-
Copyright (c) 2026 ProofFidelity contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProofFidelity contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import ProofFidelity.PrimesModFour
import ProofFidelity.SumTwoSquares
import ProofFidelity.VietaJumping

/-!
# Statement audit

Each theorem below is a formalization that typechecks and looks close to a real
statement, together with a machine-checked reason to reject it.

The informal claim is recorded in the docstring. The theorem that follows is the
**negation** of the bad formalization: a counterexample, a quantifier swap, or a
witness that does not have the property the proof assigned to it.

This is the review task. A proof that compiles can still be a proof of the wrong
statement, and a statement that is true can still be the wrong answer if it is
strictly weaker than what was asked. The second kind cannot be refuted by
`¬ P`, because a weaker true statement is still true. Those are named in the
module docstring of the positive development and rejected by comparing statements,
not by finding a counterexample.
-/

namespace ProofFidelity

lemma not_isSquare_two : ¬IsSquare (2 : ℕ) := by
  intro ⟨r, hr⟩
  have hrlt : r < 2 := by
    by_contra h
    have : 2 ≤ r := by omega
    have : 4 ≤ r * r := by nlinarith
    omega
  interval_cases r <;> simp at hr

/-- Informal: if `ab + 1` divides `a² + b²`, the quotient is a square.
Bad formalization: the denominator was written `a * b`. -/
theorem audit_imo_wrong_denominator :
    ¬∀ a b : ℕ, 0 < a → 0 < b → a * b ∣ a ^ 2 + b ^ 2 →
      IsSquare ((a ^ 2 + b ^ 2) / (a * b)) := by
  intro h
  have := h 1 1 (by decide) (by decide) (by decide)
  have hq : (1 ^ 2 + 1 ^ 2) / (1 * 1) = 2 := by decide
  rw [hq] at this
  exact not_isSquare_two this

/-- Informal: the same claim, for positive integers.
Bad formalization: the quantifiers range over all of `ℤ`.
`a = -3`, `b = 1` gives divisor `-2`, dividend `10`, quotient `-5`. -/
theorem audit_imo_drops_positivity :
    ¬∀ a b : ℤ, a * b + 1 ∣ a ^ 2 + b ^ 2 →
      IsSquare ((a ^ 2 + b ^ 2) / (a * b + 1)) := by
  intro h
  have hdvd : (-3 : ℤ) * 1 + 1 ∣ (-3) ^ 2 + (1 : ℤ) ^ 2 := ⟨-5, by norm_num⟩
  have hsq := h (-3) 1 hdvd
  have hq : ((-3 : ℤ) ^ 2 + (1 : ℤ) ^ 2) / ((-3) * 1 + 1) = -5 := by norm_num
  rw [hq] at hsq
  obtain ⟨r, hr⟩ := hsq
  have : (0 : ℤ) ≤ r * r := mul_self_nonneg r
  linarith

/-- Informal: for every `N` there is a prime `p > N` with `p ≡ 3 (mod 4)`.
Bad formalization: the quantifiers were swapped. The bad statement says there
is one prime strictly larger than every natural number. -/
theorem audit_quantifier_swap :
    ¬∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ ∀ N : ℕ, N < p := by
  intro ⟨p, _, _, hall⟩
  exact (lt_irrefl p) (hall p)

/-- Informal: every prime with `p % 4 ≠ 3` is a sum of two squares.
Bad formalization: the hypothesis was strengthened to `p % 4 ≠ 1`, which
excludes the prime `2 = 1 ^ 2 + 1 ^ 2`. -/
theorem audit_forgets_two :
    ¬∀ p : ℕ, p.Prime → p % 4 ≠ 1 → ¬∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  intro h
  exact h 2 Nat.prime_two (by decide) ⟨1, 1, by decide⟩

/-- Informal: build an integer `≡ 3 (mod 4)` past `N` by the Euclid trick.
Bad formalization: the witness `4 * N ! + 1` was used instead of `4 * N ! - 1`.
Already for `N = 1` the bad witness is `5`, which is `1` mod `4`. -/
theorem audit_euclid_sign :
    ¬(4 * Nat.factorial 1 + 1) % 4 = 3 := by
  decide

/-- The correct witness really is `3` mod `4`. -/
example : (4 * Nat.factorial 1 - 1) % 4 = 3 := by decide

/-- Informal: if `n % 4 = 3`, then the least prime factor of `n` is `3` mod `4`.
This is the natural bug in the Euclid argument. `35 = 5 * 7` is `3` mod `4`,
but `minFac 35 = 5`. Some other prime factor (`7`) does the job, which is why
`exists_prime_factor_mod_four_eq_three` inducts instead of returning `minFac`. -/
lemma minFac_thirtyfive : Nat.minFac 35 = 5 := by
  have hle : Nat.minFac 35 ≤ 5 := Nat.minFac_le_of_dvd (by decide : 2 ≤ 5) (by decide)
  have hge : 2 ≤ Nat.minFac 35 := (Nat.minFac_prime (by decide : (35 : ℕ) ≠ 1)).two_le
  interval_cases hmin : Nat.minFac 35
  · exfalso
    have : 2 ∣ 35 := by simpa [hmin] using Nat.minFac_dvd 35
    revert this
    decide
  · exfalso
    have : 3 ∣ 35 := by simpa [hmin] using Nat.minFac_dvd 35
    revert this
    decide
  · exfalso
    have : 4 ∣ 35 := by simpa [hmin] using Nat.minFac_dvd 35
    revert this
    decide
  · rfl

theorem audit_minFac_need_not_be_three_mod_four :
    ¬∀ n : ℕ, 2 ≤ n → n % 4 = 3 → n.minFac % 4 = 3 := by
  intro h
  have h35 : Nat.minFac 35 % 4 = 3 := h 35 (by decide) (by decide)
  rw [minFac_thirtyfive] at h35
  have : 5 % 4 ≠ 3 := by decide
  exact this h35

example : ∃ p : ℕ, p.Prime ∧ p ∣ 35 ∧ p % 4 = 3 :=
  ⟨7, by decide, by decide, by decide⟩

/-- Informal: among any `2n - 1` elements of `ZMod n`, some `n` of them sum to `0`.
Bad formalization: `2n - 2` elements were claimed to suffice.
For `n = 3` the sequence `(0, 0, 1, 1)` has no 3-term subsequence summing to `0`.
The sharp theorem is `ZMod.erdos_ginzburg_ziv` in mathlib. -/
theorem audit_egz_off_by_one :
    ∃ a : Fin 4 → ZMod 3, ∀ t : Finset (Fin 4), t.card = 3 → ∑ i ∈ t, a i ≠ 0 := by
  let a : Fin 4 → ZMod 3 := ![0, 0, 1, 1]
  refine ⟨a, ?_⟩
  intro t ht
  have hcompl : (Finset.univ \ t).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ht]
    decide
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcompl
  have hi_not_mem : i ∉ t := by
    have hmem : i ∈ Finset.univ \ t := by
      rw [hi]
      simp
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2
  have ht_eq : t = Finset.univ.erase i := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_erase.mpr ⟨fun hxi => hi_not_mem (hxi ▸ hx), Finset.mem_univ _⟩
    · intro hx
      have hx_ne : x ≠ i := (Finset.mem_erase.mp hx).1
      by_contra hnot
      have hxmem : x ∈ Finset.univ \ t := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
      have hsing : x ∈ ({i} : Finset (Fin 4)) := by rwa [hi] at hxmem
      exact hx_ne (Finset.mem_singleton.mp hsing)
  subst ht_eq
  fin_cases i <;> decide

end ProofFidelity
