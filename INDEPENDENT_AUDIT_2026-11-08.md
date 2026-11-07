# OEIS A100475 — independent mathematical audit (2026-11-08)

**Auditor:** GPT-6, independently reviewing the Codex proof and its exact certificate, using locally executed tools.  
**Verdict:** COMPLETE MATHEMATICAL PROOF PASSES THIS INDEPENDENT AUDIT.  
**Mathematical status assessment:** Original positive-start loop question answered **NO**. Internal resolution may be recorded `closed` under the project's exact-proof+independent-review rule.  
**Caveat:** No full Lean formalization, human expert acceptance, OEIS editor acceptance, or worldwide originality/priority certification is claimed.

## 1. Exact original question
OEIS https://oeis.org/A100475 asks whether starting from a positive value other than 1, iteration of nth-prime decimal digit reversal can eventually loop. The upstream formal file (same SHA checked on 2026-11-08: a2a7c03062ae8dd107182c0d11662134bdf7924f) represents the POSITIVE-START existential question with a `sorry`. It separately proves the trivial zero-start constant orbit, explicitly excluded from the intended OEIS question. The supplied proof establishes the NEGATION of the positive-start existence claim; it does not constitute a Lean proof of that existential assertion as written.

## 2. Independent proof logic check
For each n>=1 define p_n as the n-th prime (p_1=2) and F(n) as the usual decimal digit reversal of p_n.

**External theorem:** NIST DLMF 27.12.2 gives p_n > n ln n for all positive integer n. Source: https://dlmf.nist.gov/27.12.E2 .

**Infinite tail:** For n>60000, because e<3 and 3^10=59049<60000, we have ln(n)>10; hence p_n>10n. If n has d decimal digits, 10^(d-1)<=n<10^d, so p_n>10^d and has at least d+1 digits. Every prime has a nonzero last decimal digit, so decimal reversal preserves its digit count. Consequently F(n)>=10^d>n. Thus n>60000 is invariant and F iterates strictly increase without bound.

**Finite complement:** All starts n=1,...,60000 must exit above the threshold. The original package's complete exact certificate validates this. Separate reimplementation described below does NOT ingest the supplied certificate or ranks and verifies the same stronger fact.

**Conclusion:** Every positive orbit eventually exceeds 60000 and thereafter is strictly increasing. Therefore no positive starting orbit is ultimately periodic, including starting at 1. This answers the full original positive-start question negatively. The proof does not rely on heuristic numerical extrapolation.

## 3. Executed reproducibility and independent computations

- Ran original `verify_certificate.py`: PASS, 60000 rows, 60000 primes, p_60000=746773, max exit steps=10, Kahn elimination removes 60000 vertices.
- Ran original `clean_replay.py` in fresh temporary build directory: PASS; rebuilt certificate bytes identical and verification JSON identical. This validates deterministic replay in this runtime, not on an independent machine.
- Certificate SHA-256: `9871bc6f20f6b3fb2e4f4e5a90fc2ae484fe9537f74f87e1781f68f42c92baa0`.
- Created a new `independent_second_audit.py`: separate prime sieve with explicit composite marking; arithmetic digit reversal; independent functional-graph topological elimination and dynamic path-length computation. Does NOT read supplied certificate or supplied checker's ranks.
- New implementation: PASS; 60000 vertices removed, p_60000=746773; maximum escape steps=10; 54598 starts exit in one step; 1 start requires 10 steps.
- No probabilistic primality tests, solver `UNKNOWN`, or incomplete search are part of this conclusion.

## 4. Audit of potential failure points

1. **Indexing:** One-based p_1=2 matches OEIS and the upstream Lean `Nat.nth Prime (k-1)` for positive k.
2. **Zero artifact:** x=0 is excluded; otherwise it produces a trivial constant orbit in the upstream totalized recurrence.
3. **Rosser bound:** External theorem is unconditional and has correct indexing. n>60000 implies ln(n)>10 without floating point approximations.
4. **Reversal length:** p_n modulo 10 is never zero. Leading zero after digit reversal is impossible, so reversed result retains prime's decimal digit count.
5. **Finite-infinite bridge:** Includes n=60000 in the finite range; n>60000 in the infinite argument. Boundary complete.
6. **Graph algorithm:** Every n<=60000 has exactly one next state F(n)>0. The finite internal edges form a directed functional graph. Topological elimination of all 60000 vertices proves no retained directed cycle; in a finite graph, every internal infinite path would repeat, so each state exits.
7. **Result scope:** The complete mathematical conclusion is ordinary rigorous argument + exact finite certificate. It is not a Lean kernel proof and does not prove the original **existential** Lean proposition; it proves its negation.
8. **Priority:** Targeted primary-source and GitHub searches show official sources still pose the positive-start question; searches cannot exclude all unpublished or undiscovered independent solutions.

## 5. Recommendations

- Archive this independent audit and code in `04_CLOSURE_EVIDENCE/OEIS-A100475` once the canonical internal status is updated.
- For public contribution: ask a distinct mathematical reviewer to assess the proof (or write the negated formal theorem in Lean), and submit findings with proper attribution to OEIS/formal-conjectures maintainers. No external submission has been made.
- Preserve the original Codex proof and reproducibility bundle; do not paraphrase the claim as having received external expert approval.

**External sources checked:** https://oeis.org/A100475 ; https://dlmf.nist.gov/27.12.E2 ; https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/100475.lean ; https://github.com/google-deepmind/formal-conjectures/pull/5567 .
