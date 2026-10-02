/-
Copyright (c) 2026 ProofFidelity contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProofFidelity contributors
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic

/-!
# Vieta jumping

Two Diophantine statements proved by flipping the other root of a quadratic.

## IMO 1988 Problem 6

Let `a` and `b` be positive integers such that `a * b + 1` divides `a ^ 2 + b ^ 2`.
Then `(a ^ 2 + b ^ 2) / (a * b + 1)` is a perfect square.

The denominator is `a * b + 1`, not `a * b`. The pair `(1, 1)` divides in both
conventions, but the quotients are `1` and `2`, and `2` is not a square.
Positivity also matters: `a = -3`, `b = 1` gives the quotient `-5`.

## A constant-descent companion

Let `a` and `b` be positive integers such that `a * b` divides `a ^ 2 + b ^ 2 + 1`.
Then the quotient is exactly `3`: `a ^ 2 + b ^ 2 + 1 = 3 * a * b`.
-/

namespace ProofFidelity

/-- If `k` is not a square and `(x, y)` is a positive solution of
`x ^ 2 + y ^ 2 = k * (x * y + 1)` with `y ≤ x`, the other Vieta root in `x`
is a strictly smaller positive solution with the same `k` and the same `y`. -/
lemma vieta_descend {k x y : ℕ} (hx : 0 < x) (hy : 0 < y) (hle : y ≤ x)
    (heq : x ^ 2 + y ^ 2 = k * (x * y + 1)) (hns : ¬IsSquare k) :
    ∃ x' : ℕ, 0 < x' ∧ x' + y < x + y ∧ x' ^ 2 + y ^ 2 = k * (x' * y + 1) := by
  have hk0 : k ≠ 0 := by
    intro hk
    simp [hk] at heq
    omega
  have heqZ : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 = (k : ℤ) * ((x : ℤ) * y + 1) := by
    exact_mod_cast heq
  let x' : ℤ := (k : ℤ) * y - x
  have hsum : (x : ℤ) + x' = (k : ℤ) * y := by
    simp [x']
  have hprod : (x : ℤ) * x' = (y : ℤ) ^ 2 - (k : ℤ) := by
    have : (k : ℤ) * x * y - (x : ℤ) ^ 2 = (y : ℤ) ^ 2 - k := by linarith [heqZ]
    calc
      (x : ℤ) * x' = x * ((k : ℤ) * y - x) := by simp [x']
      _ = (k : ℤ) * x * y - x ^ 2 := by ring
      _ = (y : ℤ) ^ 2 - k := this
  have hid : x' ^ 2 + (y : ℤ) ^ 2 = (k : ℤ) * (x' * y + 1) := by
    nlinarith [hsum, hprod]
  have hprod_add : (x : ℤ) * x' + (k : ℤ) = (y : ℤ) ^ 2 := by
    linarith [hprod]
  have hx'_ne : x' ≠ 0 := by
    intro h0
    have hk_sq : (k : ℤ) = (y : ℤ) ^ 2 := by
      rw [h0, mul_zero, zero_add] at hprod_add
      exact hprod_add
    have hk_nat : k = y ^ 2 := by exact_mod_cast hk_sq
    exact hns ⟨y, by simpa [pow_two] using hk_nat⟩
  have hx'_pos : 0 < x' := by
    have hx'_nonneg : 0 ≤ x' := by
      by_contra hneg
      have hx'le : x' ≤ -1 := by omega
      have hden : x' * (y : ℤ) + 1 ≤ 0 := by nlinarith
      have hleft : 0 < x' ^ 2 + (y : ℤ) ^ 2 := by nlinarith [hy]
      have hright : (k : ℤ) * (x' * y + 1) ≤ 0 := by nlinarith [hk0]
      linarith [hid]
    omega
  have hx'_lt : x' < x := by
    have hyx : (y : ℤ) ≤ x := by exact_mod_cast hle
    have hkpos : (1 : ℤ) ≤ k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hcmp : (y : ℤ) ^ 2 - k < (x : ℤ) ^ 2 := by nlinarith
    have : (x : ℤ) * x' < (x : ℤ) * x := by linarith [hprod]
    nlinarith
  have hx'_coe : (x'.toNat : ℤ) = x' := Int.toNat_of_nonneg (le_of_lt hx'_pos)
  refine ⟨x'.toNat, ?_, ?_, ?_⟩
  · exact_mod_cast (show (0 : ℤ) < (x'.toNat : ℤ) by rw [hx'_coe]; exact hx'_pos)
  · have hlt_nat : x'.toNat < x := by
      exact_mod_cast (show (x'.toNat : ℤ) < (x : ℤ) by rw [hx'_coe]; exact hx'_lt)
    omega
  · have hidN : (x'.toNat : ℤ) ^ 2 + (y : ℤ) ^ 2 =
        (k : ℤ) * ((x'.toNat : ℤ) * y + 1) := by
      rw [hx'_coe]
      exact hid
    exact_mod_cast hidN

/-- **IMO 1988 Problem 6.** -/
theorem imo1988_p6 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hdvd : a * b + 1 ∣ a ^ 2 + b ^ 2) :
    IsSquare ((a ^ 2 + b ^ 2) / (a * b + 1)) := by
  set k := (a ^ 2 + b ^ 2) / (a * b + 1) with hk_def
  have hk : a ^ 2 + b ^ 2 = k * (a * b + 1) := by
    simpa [hk_def, Nat.mul_comm] using (Nat.div_mul_cancel hdvd).symm
  by_contra hns
  have no_solution :
      ∀ n : ℕ, ¬∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ x ^ 2 + y ^ 2 = k * (x * y + 1) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      rintro ⟨x, y, hx, hy, hsum, heq⟩
      rcases le_or_gt y x with hle | hlt
      · obtain ⟨x', hx', hsum', heq'⟩ := vieta_descend hx hy hle heq hns
        have : x' + y < n := by omega
        exact ih (x' + y) this ⟨x', y, hx', hy, rfl, heq'⟩
      · have heq_swap : y ^ 2 + x ^ 2 = k * (y * x + 1) := by
          simpa [Nat.add_comm, Nat.mul_comm] using heq
        obtain ⟨y', hy', hsum', heq'⟩ :=
          vieta_descend hy hx (Nat.le_of_lt hlt) heq_swap hns
        have : y' + x < n := by
          simpa [hsum, Nat.add_comm] using hsum'
        exact ih (y' + x) this ⟨y', x, hy', hx, rfl, heq'⟩
  exact no_solution (a + b) ⟨a, b, ha, hb, rfl, hk⟩

/-- If `a * b` divides `a ^ 2 + b ^ 2 + 1` for positive integers `a, b`, the quotient is `3`. -/
theorem eq_three_of_dvd_sq_add_sq_add_one {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hdvd : a * b ∣ a ^ 2 + b ^ 2 + 1) : a ^ 2 + b ^ 2 + 1 = 3 * (a * b) := by
  suffices ∀ s a b : ℕ, a + b = s → 0 < a → 0 < b → b ≤ a → a * b ∣ a ^ 2 + b ^ 2 + 1 →
      a ^ 2 + b ^ 2 + 1 = 3 * (a * b) by
    rcases le_or_gt b a with hle | hlt
    · exact this (a + b) a b rfl ha hb hle hdvd
    · have hdvd' : b * a ∣ b ^ 2 + a ^ 2 + 1 := by
        simpa [Nat.mul_comm, Nat.add_comm] using hdvd
      simpa [Nat.mul_comm, Nat.add_comm] using
        this (b + a) b a rfl hb ha (Nat.le_of_lt hlt) hdvd'
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro a b hs ha hb hle hdvd
    set k := (a ^ 2 + b ^ 2 + 1) / (a * b) with hk_def
    have hk : a ^ 2 + b ^ 2 + 1 = k * (a * b) := by
      simpa [hk_def, Nat.mul_comm] using (Nat.div_mul_cancel hdvd).symm
    cases eq_or_lt_of_le hle with
    | inl heq =>
      -- `b = a`: then `a ^ 2` divides `1`, so `a = 1` and the quotient is `3`.
      rw [heq] at hdvd hs ⊢
      have hd : a ^ 2 ∣ 2 * a ^ 2 + 1 := by
        simpa [Nat.two_mul, Nat.pow_two] using hdvd
      have hd_self : a ^ 2 ∣ 2 * a ^ 2 := ⟨2, by ring⟩
      have hd1 : a ^ 2 ∣ 1 := by
        have hZm : (a ^ 2 : ℤ) ∣ (2 * a ^ 2 : ℤ) := by exact_mod_cast hd_self
        have hZ1 : (a ^ 2 : ℤ) ∣ ((2 * a ^ 2 + 1 : ℕ) : ℤ) := by exact_mod_cast hd
        have hsub : (a ^ 2 : ℤ) ∣ 1 := by
          simpa using dvd_sub hZ1 hZm
        exact_mod_cast hsub
      have ha1 : a = 1 := by
        have hsq : a ^ 2 = 1 := Nat.dvd_one.mp hd1
        have ha2 : a < 2 := by
          by_contra hge
          have : 2 ≤ a := Nat.le_of_not_gt hge
          have : 4 ≤ a * a := by nlinarith
          have : a * a = 1 := by simpa [Nat.pow_two] using hsq
          omega
        omega
      subst ha1
      rfl
    | inr hba =>
      -- `b < a`. The other root `a' = k * b - a` is a smaller positive solution.
      have ha_le : a ≤ k * b := by
        by_contra hlt
        have hkb : k * b < a := Nat.lt_of_not_ge hlt
        have hmul : k * a * b < a * a := by
          calc
            k * a * b = a * (k * b) := by ring
            _ < a * a := Nat.mul_lt_mul_of_pos_left hkb ha
        have : a ^ 2 + b ^ 2 + 1 < a ^ 2 := by
          calc
            a ^ 2 + b ^ 2 + 1 = k * (a * b) := hk
            _ = k * a * b := by ring
            _ < a * a := hmul
            _ = a ^ 2 := by rw [Nat.pow_two]
        omega
      let a' : ℕ := k * b - a
      have ha'_sum : a + a' = k * b := by
        have : a' + a = k * b := by simpa [a'] using Nat.sub_add_cancel ha_le
        simpa [Nat.add_comm] using this
      have ha'_prod : a * a' = b ^ 2 + 1 := by
        have hZ : (a : ℤ) * a' = (b : ℤ) ^ 2 + 1 := by
          have hkZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + 1 = (k : ℤ) * ((a : ℤ) * b) := by
            exact_mod_cast hk
          have hsumZ : (a : ℤ) + a' = (k : ℤ) * b := by exact_mod_cast ha'_sum
          nlinarith
        exact_mod_cast hZ
      have ha'_pos : 0 < a' := by
        have hne : a' ≠ 0 := by
          intro h0
          rw [h0, Nat.mul_zero] at ha'_prod
          omega
        omega
      have ha'_lt : a' < a := by
        have hsq : b ^ 2 + 1 < a ^ 2 := by
          have hba1 : b + 1 ≤ a := Nat.succ_le_of_lt hba
          zify at hba1
          nlinarith
        have : a * a' < a * a := by
          rw [ha'_prod, ← Nat.pow_two]
          exact hsq
        exact Nat.lt_of_mul_lt_mul_left this
      have heq' : a' ^ 2 + b ^ 2 + 1 = k * (a' * b) := by
        have hZ : (a' : ℤ) ^ 2 + (b : ℤ) ^ 2 + 1 = (k : ℤ) * ((a' : ℤ) * b) := by
          have hkZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + 1 = (k : ℤ) * ((a : ℤ) * b) := by
            exact_mod_cast hk
          have hsumZ : (a : ℤ) + a' = (k : ℤ) * b := by exact_mod_cast ha'_sum
          nlinarith
        exact_mod_cast hZ
      have hsum_lt : a' + b < s := by omega
      have hsmall : a' ^ 2 + b ^ 2 + 1 = 3 * (a' * b) := by
        rcases le_total a' b with hord | hord
        · have hdvd_small : b * a' ∣ b ^ 2 + a' ^ 2 + 1 := by
            refine ⟨k, ?_⟩
            calc
              b ^ 2 + a' ^ 2 + 1 = a' ^ 2 + b ^ 2 + 1 := by ac_rfl
              _ = k * (a' * b) := heq'
              _ = b * a' * k := by ring
          simpa [Nat.add_comm, Nat.mul_comm] using
            ih (b + a') (by simpa [Nat.add_comm] using hsum_lt) b a' rfl hb ha'_pos hord hdvd_small
        · have hdvd_small : a' * b ∣ a' ^ 2 + b ^ 2 + 1 := by
            refine ⟨k, ?_⟩
            calc
              a' ^ 2 + b ^ 2 + 1 = k * (a' * b) := heq'
              _ = a' * b * k := by ring
          exact ih (a' + b) hsum_lt a' b rfl ha'_pos hb hord hdvd_small
      have hk3 : k * (a' * b) = 3 * (a' * b) := by
        rw [← heq', hsmall]
      have hc : 0 < a' * b := by positivity
      have hk_eq : k = 3 := Nat.eq_of_mul_eq_mul_right hc hk3
      rw [hk_eq] at hk
      exact hk

/-- Quotient `1`, from `(a, b) = (1, 1)`. -/
example : IsSquare ((1 ^ 2 + 1 ^ 2) / (1 * 1 + 1)) :=
  imo1988_p6 (a := 1) (b := 1) Nat.one_pos Nat.one_pos (by decide)

/-- Quotient `4 = 2 ^ 2`, from `(a, b) = (8, 2)`. -/
example : (8 ^ 2 + 2 ^ 2) / (8 * 2 + 1) = 4 := by decide

example : 1 ^ 2 + 1 ^ 2 + 1 = 3 * (1 * 1) :=
  eq_three_of_dvd_sq_add_sq_add_one (a := 1) (b := 1) Nat.one_pos Nat.one_pos (by decide)

example : 1 ^ 2 + 2 ^ 2 + 1 = 3 * (1 * 2) :=
  eq_three_of_dvd_sq_add_sq_add_one (a := 1) (b := 2) Nat.one_pos (by decide) (by decide)

end ProofFidelity
