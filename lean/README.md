# Lean 4 formalization

`A100475/Basic.lean` proves the negative answer in Lean 4 + Mathlib with no `sorry`:

```lean
theorem A100475.answer :
    ¬ ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x)
```

`reverseDigits`, `aStartAt` and `IsUltimatelyPeriodic` are restated verbatim from
[`FormalConjectures/OEIS/100475.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/100475.lean)
(blob `a2a7c03062ae8dd107182c0d11662134bdf7924f`). So `answer` is literally the negation of the
upstream `OeisA100475.conjecture`. The file also proves the stronger statements
`not_ultimatelyPeriodic` (every positive start, including 1), `eventually_strictly_increasing`, and
`tendsto_atTop`.

## Proof structure

The Lean proof differs from `PROOF.md` in two ways. It does **not** use Rosser's theorem, which
is not in Mathlib. Instead, the cutoff is lowered from 60,000 to 10^4.

1. **Prime counting** (`count_prime_pow_ten_lt`): π(10^d) < 10^(d−1) for every d ≥ 5.
   - d = 5, 6, 7 are computed exactly (9592, 78498 and 664579 primes).
   - Each d ≥ 8 follows from the case d − 1 and Mathlib's Chebyshev bound θ(x) ≤ x·log 4
     (`Chebyshev.theta_le_log4_mul_x`). The argument is
     (π(10^d) − π(10^(d−1)))·log 10^(d−1) ≤ θ(10^d), together with 2^33 < 10^10.
2. **Tail** (`lt_step_of_ge`): suppose n ≥ 10^4 has d digits. Step 1 gives p_n ≥ 10^d, and a
   prime never ends in 0, so reversing p_n keeps its digit count. Hence `reverseDigits p_n > n`.
3. **Finite part** (`esc_all`): every start 1 ≤ n < 10^4 reaches the region ≥ 10^4 within
   10 steps.
   - The required values p_1 … p_9999 come from a table.
   - `tab_check` verifies the table exactly: it starts at 2, its entries are prime and
     increasing, and each gap contains no other prime.
   - `nth_prime_eq_tab` then identifies the table with Mathlib's `Nat.nth Nat.Prime`.
4. Steps 2 and 3 together show that every positive orbit is eventually strictly increasing, so it
   is never ultimately periodic.

## Trust base

`#print axioms A100475.answer` gives `propext`, `Classical.choice` and `Quot.sound`, plus one
`native_decide` axiom for each of five finite computations:

| Lemma | What is computed |
|---|---|
| `count_prime_1e5`, `count_prime_1e6`, `count_prime_1e7` | π(10^5) < 10^4, π(10^6) < 10^5, π(10^7) < 10^6 |
| `tab_check` | correctness of the table p_1 … p_9999 |
| `esc_all` | all starts below 10^4 escape within 10 steps |

`native_decide` trusts the Lean compiler as well as the kernel. Replacing these five computations
with kernel-checked certificates would remove that extra trust. All other reasoning is
kernel-checked against Mathlib.

## Build

```bash
cd lean
lake exe cache get   # download the prebuilt Mathlib cache
lake build           # about 4 minutes; the native computations take most of it
lake env lean Check.lean   # prints the axioms and the statement of `answer`
```

Toolchain: `leanprover/lean4:v4.36.0-rc2`. Mathlib is pinned at
`59c7f902e2bff1ceeb8466715bcb052b69b6a70f`.

## Provenance and licences

Prepared in the project's AI-assisted cross-verification stage (2026-11-08). Original Lean code
is under the MIT License (`../LICENSE`).

The three restated definitions come from formal-conjectures, © 2026 The Formal Conjectures
Authors, under the Apache License 2.0. A copy of that licence is in
`THIRD_PARTY_LICENSE-Apache-2.0.txt`.
