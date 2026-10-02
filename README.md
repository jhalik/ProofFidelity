# ProofFidelity

A Lean 4 library on current mathlib. It does the two things a formalization review actually checks: the formal statement is the theorem that was claimed, and the proof compiles for that statement.

`lake build` is the whole test. There is no `sorry` and no extra axiom.

## What is proved

**Primes congruent to 3 mod 4.** For every natural number `N` there is a prime `p` with

```text
N < p ≤ 4 · N! − 1  and  p ≡ 3 (mod 4).
```

The argument is Euclid's, not the cyclotomic proof of `p ≡ 1 (mod k)` already in mathlib. It is effective, and it does not return `Nat.minFac`. That would be wrong: `35 = 5 · 7` is `3` mod `4`, but its least prime factor is `5`. The lemma `exists_prime_factor_mod_four_eq_three` finds some prime factor by induction on the residue of a product.

**Sums of two squares.** An integer congruent to `3` mod `4` is never a sum of two integer squares. For a prime, this obstruction is also sufficient:

```text
p prime  →  (p = a² + b² for some a, b)  ↔  p % 4 ≠ 3.
```

The `←` direction is Fermat's Christmas theorem, cited as `Nat.Prime.sq_add_sq`. The prime `2 = 1² + 1²` is why the hypothesis is `≠ 3` and not `= 1`.

**IMO 1988, Problem 6.** If `a` and `b` are positive integers and `ab + 1` divides `a² + b²`, then the quotient is a perfect square. The proof is Vieta jumping: the other root of the quadratic in `a` is a smaller positive solution unless the quotient is already a square.

**Companion.** If `ab` divides `a² + b² + 1`, the quotient is exactly `3`.

## What is rejected

`ProofFidelity/StatementAudit.lean` proves the negation of six near-miss formalizations. Each one is a mistake that still looks like the theorem.

| Informal claim | What went wrong | Refutation |
| --- | --- | --- |
| IMO 1988, Problem 6 | Denominator written `ab` instead of `ab + 1` | `(1, 1)` gives quotient `2`, not a square |
| The same claim | Quantifiers taken over `ℤ` | `(-3, 1)` gives quotient `-5` |
| Infinitely many primes `≡ 3 (mod 4)` | Quantifiers swapped | one prime cannot exceed every `N` |
| Primes that are sums of two squares | Hypothesis written `p % 4 ≠ 1` | excludes `2 = 1² + 1²` |
| The Euclid witness | `4 · N! + 1` instead of `4 · N! − 1` | for `N = 1` the witness is `5` |
| The least prime factor is `3` mod `4` | `minFac` in place of "some prime factor" | `minFac 35 = 5` |
| Erdős–Ginzburg–Ziv | `2n − 2` elements instead of `2n − 1` | `(0, 0, 1, 1)` in `ZMod 3` |

A true but strictly weaker statement is a different failure. `∃ p, Prime p ∧ p % 4 = 3` compiles and is true, and it is not "there are infinitely many such primes". Both sides are true, so they are logically equivalent and `¬ P` cannot express the gap. The review has to compare the statement with the claim.

## Review rubric

Use this on a formalization, human or model-written.

**Statement.** Reject if a quantifier moved, a hypothesis disappeared (positivity, coprimality, the exact modulus), a bound is off by one, or divisibility runs in the wrong direction. Reject a true weaker theorem when the claim was the strong one. Check the witness, not only the existential: `minFac` is not "a prime factor with this residue".

**Proof.** No `sorry`, no new axiom. A finite check may be `decide` or `norm_num` after the mathematical reduction is explicit. A citation of a mathlib theorem is better than a second proof of it, provided the cited statement is the one being used (`Nat.Prime.sq_add_sq` assumes `p % 4 ≠ 3`, not `p % 4 = 1`).

**Style.** Names say the mathematical content. The informal statement sits in the docstring above the formal one, including the hypothesis that is easy to drop.

## Layout

```text
ProofFidelity/PrimesModFour.lean     elementary infinitude, with a bound
ProofFidelity/SumTwoSquares.lean     the mod-4 obstruction, plus Fermat's theorem
ProofFidelity/VietaJumping.lean      IMO 1988 Problem 6, and the quotient-3 lemma
ProofFidelity/StatementAudit.lean    machine-checked rejections
```

## Build

```bash
lake exe cache get
lake build
```

The toolchain is the mathlib revision pinned in `lean-toolchain` (`v4.34.1` at the time of writing).
