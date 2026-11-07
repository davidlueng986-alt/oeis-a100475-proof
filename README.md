# OEIS A100475: No positive orbit enters a loop

**A complete negative solution to the positive-start loop question recorded in [OEIS A100475](https://oeis.org/A100475).** This repository contains a mathematical proof, a complete finite certificate, its original independent algorithmic checker, and a separately written second checker. The proof has passed internal independent mathematical/computational review. **Update 2026-11-08: a Lean 4 + Mathlib formalization of the full negative answer is in [`lean/`](lean/). It contains no `sorry`, and its trust base is listed in [`lean/README.md`](lean/README.md). The result has not been peer-reviewed or accepted by OEIS. Claims of worldwide priority are not made.**

## The problem

Let `p_n` be the `n`th prime, indexed with `p_1 = 2`, and let `rev10` reverse the decimal digits of a positive integer. Define

```text
F(n) = rev10(p_n), n >= 1.
a_x(0) = x, a_x(t+1) = F(a_x(t)), x >= 1.
```

**Original question:** Is there any positive initial value other than 1 for which the iteration eventually enters a cycle?

**Answer: no.** In fact, for every positive starting value `x`, the orbit is eventually strictly increasing and tends to infinity.

The zero start used to totalize a [Lean formal statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/100475.lean) is not part of this question; zero has a trivial periodic orbit only in that artificial extension. The existing `conjecture` in that Lean file is the *existential* statement asking for a positive periodic orbit; the result here proves its **negation**, not the existential declaration as currently written.

## Proof in brief

1. Rosser's prime bound gives `p_n > n log(n)` for every positive integer `n` ([NIST DLMF 27.12.2](https://dlmf.nist.gov/27.12.E2)). Since `e < 3`, we have `e^10 < 3^10 = 59049 < 60000`. Hence `p_n > 10 n` whenever `n > 60000`.
2. If `n` has `d` decimal digits, `p_n > 10 n` has at least `d+1` digits. A prime never ends in zero, so digit reversal preserves its number of decimal digits. Therefore `F(n) > n` whenever `n > 60000`. Every orbit above this cutoff increases forever.
3. The finite certificate checks **every** `n = 1, ..., 60000` with exact primes and digit reversal. A verified positive exit-rank function strictly decreases until the iteration leaves this finite interval. The maximum number of steps before exit is **10**. A second graph algorithm independently excludes all finite-region cycles.
4. Hence all positive orbits eventually enter the strictly increasing region and no positive orbit can be ultimately periodic. **QED.**

See [`PROOF.md`](PROOF.md) for the full argument and exact relation to the original question.

## Reproduce

Requires Python 3 and `g++` (only `python3` for the supplied certificate). No GPU, paid API or AI model required.

```bash
python3 verify_certificate.py      # verifies supplied certificate.tsv, including all 60,000 states
python3 independent_check.py       # independently enumerates the entire finite state graph
python3 clean_replay.py            # rebuilds certificate in a fresh temporary directory
```

To regenerate the finite certificate manually:

```bash
g++ -O2 -std=c++17 -Wall -Wextra -pedantic build_certificate.cpp -o build_certificate
./build_certificate > generation.json
python3 verify_certificate.py
```

The SHA-256 of the expected `certificate.tsv` is

```text
9871bc6f20f6b3fb2e4f4e5a90fc2ae484fe9537f74f87e1781f68f42c92baa0
```

## Lean formalization

[`lean/A100475/Basic.lean`](lean/A100475/Basic.lean) proves `¬ ∃ x, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x)`. Its definitions are restated verbatim from the formal-conjectures file, so this is literally the negation of the upstream `conjecture`. The Lean proof replaces Rosser's theorem with Mathlib's Chebyshev bound θ(x) ≤ x log 4, and lowers the finite cutoff from 60,000 to 10^4. Five finite computations use `native_decide`, which means trusting the Lean compiler as well as the kernel. Details, axioms and build steps are in [`lean/README.md`](lean/README.md).

## Evidence and provenance

- [`PROOF.md`](PROOF.md): full ordinary-mathematics proof, including the precise quantifier and boundary-case interpretation.
- [`certificate.tsv`](certificate.tsv): all 60,000 exact cases with exit ranks.
- [`verify_certificate.py`](verify_certificate.py): exact certificate checker using a separate prime-generation and reversal algorithm.
- [`independent_check.py`](independent_check.py): separately written finite-case checker, not dependent on the supplied certificate.
- [`INDEPENDENT_AUDIT_2026-11-08.md`](INDEPENDENT_AUDIT_2026-11-08.md): 2026-11-08 independent audit and its scope.
- [`AUDIT.md`](AUDIT.md): previous research-source, novelty and completeness audit.
- [`RESULT_zh.md`](RESULT_zh.md): Traditional Chinese explanation.

The underlying sequence is attributed to **Jonathan Vos Post** (OEIS A100475, 2004). The prime bound is due to **Barkley Rosser** (1939). The finite proof/certificate and initial audit were prepared in an AI-assisted Codex research session, and the supplementary mathematical audit and second finite checker were performed in a later GPT-6 session (2026-11-08). AI review should not be represented as a human mathematician's endorsement.

## Licensing

Original textual material in this repository is released under **[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)**; original source code is released under the **MIT License** (see [`LICENSE`](LICENSE) and [`LICENSE-TEXT.md`](LICENSE-TEXT.md)). Third-party source material is *not relicensed*: OEIS content is CC BY-SA 4.0; the Formal Conjectures repository applies Apache-2.0 to software and additional source-dependent licenses to mathematical content. We link to those sources rather than copying their source files, except that `lean/A100475/Basic.lean` restates three short definitions from the Formal Conjectures A100475 file under Apache-2.0, with attribution (licence copy in `lean/THIRD_PARTY_LICENSE-Apache-2.0.txt`). See [`NOTICE.md`](NOTICE.md).

## Current public status (checked 2026-11-08)

The OEIS page still posed the loop question, and `google-deepmind/formal-conjectures` still tagged the positive-start question as open in the checked revision. Targeted web and GitHub research found no earlier public complete answer, but this is **not a priority proof**. We invite independent mathematical verification and feedback before seeking public recognition or a formal statement-status change.
