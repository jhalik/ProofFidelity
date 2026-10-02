/-
Copyright (c) 2026 ProofFidelity contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProofFidelity contributors
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Infinitely many primes congruent to `3` modulo `4`

Euclid's argument, made effective. For every `N` there is a prime

`N < p ≤ 4 * N ! - 1` with `p % 4 = 3`.

The least prime factor of `4 * N ! - 1` need not itself be `3` mod `4`
(`35 = 5 * 7` is the model case: `35 % 4 = 3` but `minFac 35 = 5`).
The proof therefore shows that *some* prime factor is `3` mod `4`, by induction
on the integer, using that a product is `3` mod `4` only when exactly one
factor is.

Mathlib already proves the harder congruence `p ≡ 1 [MOD k]` for every `k > 0`,
via cyclotomic polynomials (`exists_prime_gt_modEq_one`). The argument here is
the elementary one, and it produces an explicit bound the cyclotomic proof does
not.
-/

namespace ProofFidelity

/-- Multiplying two natural numbers gives a residue of `3` mod `4` only in the
two unbalanced cases. Residues `0` and `2` make the product even, and
`3 * 3 = 9 ≡ 1`. -/
lemma mul_mod_four_eq_three {a b : ℕ} (h : (a * b) % 4 = 3) :
    a % 4 = 1 ∧ b % 4 = 3 ∨ a % 4 = 3 ∧ b % 4 = 1 := by
  have hmod : (a % 4 * (b % 4)) % 4 = 3 := by
    simpa [Nat.mul_mod] using h
  generalize ha : a % 4 = x at hmod
  generalize hb : b % 4 = y at hmod
  have hx : x < 4 := by simpa [ha] using Nat.mod_lt a (by decide : 0 < 4)
  have hy : y < 4 := by simpa [hb] using Nat.mod_lt b (by decide : 0 < 4)
  interval_cases x <;> interval_cases y <;> simp_all

/-- If `2 ≤ n` and `n % 4 = 3`, then some prime divisor of `n` is `3` mod `4`. -/
theorem exists_prime_factor_mod_four_eq_three :
    ∀ n : ℕ, 2 ≤ n → n % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn hmod
    by_cases hprime : n.Prime
    · exact ⟨n, hprime, dvd_rfl, hmod⟩
    · set a := n.minFac with ha_def
      have ha_prime : a.Prime := Nat.minFac_prime (by omega : n ≠ 1)
      have ha_dvd : a ∣ n := n.minFac_dvd
      have ha_lt : a < n := (Nat.not_prime_iff_minFac_lt hn).1 hprime
      have ha_two : 2 ≤ a := ha_prime.two_le
      obtain ⟨b, hb⟩ := ha_dvd
      have hb_two : 2 ≤ b := by
        have hb0 : b ≠ 0 := by
          intro h0
          simp [h0] at hb
          omega
        have hb1 : b ≠ 1 := by
          intro h1
          have : n = a := by simpa [h1] using hb
          omega
        omega
      have hb_lt : b < n := by
        rw [hb]
        have hmul : 1 * b < a * b :=
          Nat.mul_lt_mul_of_pos_right (by omega : 1 < a) (by omega : 0 < b)
        simpa using hmul
      have hsplit : a % 4 = 1 ∧ b % 4 = 3 ∨ a % 4 = 3 ∧ b % 4 = 1 :=
        mul_mod_four_eq_three (by simpa [hb] using hmod)
      rcases hsplit with ⟨_, hb3⟩ | ⟨ha3, _⟩
      · obtain ⟨p, hp, hpd, hpm⟩ := ih b hb_lt hb_two hb3
        have hpn : p ∣ n := by
          rw [hb]
          exact dvd_mul_of_dvd_right hpd a
        exact ⟨p, hp, hpn, hpm⟩
      · exact ⟨a, ha_prime, n.minFac_dvd, ha3⟩

/-- Euclid witness: `4 * N ! - 1` is an integer greater than `1`, congruent to `3` mod `4`,
and not divisible by any prime `≤ N`. -/
theorem exists_prime_gt_mod_four_eq_three (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p ≤ 4 * Nat.factorial N - 1 ∧ p.Prime ∧ p % 4 = 3 := by
  have hfact : 0 < Nat.factorial N := Nat.factorial_pos N
  have hle : 1 ≤ 4 * Nat.factorial N := by omega
  let M : ℕ := 4 * Nat.factorial N - 1
  have hM_add : M + 1 = 4 * Nat.factorial N := Nat.sub_add_cancel hle
  have hM_form : M = 3 + 4 * (Nat.factorial N - 1) := by omega
  have hMmod : M % 4 = 3 := by
    rw [hM_form, Nat.add_mul_mod_self_left]
  have hM2 : 2 ≤ M := by omega
  obtain ⟨p, hp, hpd, hpm⟩ := exists_prime_factor_mod_four_eq_three M hM2 hMmod
  refine ⟨p, ?_, Nat.le_of_dvd (by omega : 0 < M) hpd, hp, hpm⟩
  by_contra hNp
  have hple : p ≤ N := Nat.le_of_not_gt hNp
  have hpf : p ∣ Nat.factorial N := Nat.dvd_factorial hp.pos hple
  have hp4 : p ∣ 4 * Nat.factorial N := dvd_mul_of_dvd_right hpf 4
  have hpM : (p : ℤ) ∣ (M : ℤ) := by exact_mod_cast hpd
  have hp4Z : (p : ℤ) ∣ (4 * Nat.factorial N : ℤ) := by exact_mod_cast hp4
  have hdiff : (4 * Nat.factorial N : ℤ) - (M : ℤ) = 1 := by
    have : (M : ℤ) + 1 = (4 * Nat.factorial N : ℤ) := by exact_mod_cast hM_add
    linarith
  obtain ⟨u, hu⟩ := hp4Z
  obtain ⟨v, hv⟩ := hpM
  have hp1 : (p : ℤ) ∣ (1 : ℤ) := ⟨u - v, by linarith⟩
  have hp1N : p ∣ 1 := by exact_mod_cast hp1
  exact hp.not_dvd_one hp1N

/-- There are infinitely many primes congruent to `3` modulo `4`. -/
theorem exists_prime_mod_four_eq_three_gt (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 4 = 3 := by
  obtain ⟨p, hpN, _, hp, hmod⟩ := exists_prime_gt_mod_four_eq_three N
  exact ⟨p, hpN, hp, hmod⟩

/-- The same fact, in the `Set.Infinite` packaging. -/
theorem infinite_primes_mod_four_eq_three :
    {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite :=
  Set.infinite_of_forall_exists_gt fun N => by
    obtain ⟨p, hpN, hp, hmod⟩ := exists_prime_mod_four_eq_three_gt N
    exact ⟨p, ⟨hp, hmod⟩, hpN⟩

end ProofFidelity
