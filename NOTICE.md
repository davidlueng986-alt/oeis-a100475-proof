# Attributions, source licenses, and publication status

**OEIS A100475** — original sequence and question by Jonathan Vos Post,
Nov 22, 2004: https://oeis.org/A100475 . OEIS materials are CC BY-SA 4.0:
https://oeis.org/wiki/The_OEIS_End-User_License_Agreement . This repository
links to OEIS and independently states mathematical definitions rather than
redistributing the OEIS database.

**Rosser inequality** — Barkley Rosser, *The n-th Prime is Greater than n log n*,
Proceedings of the London Mathematical Society s2-45 (1939), 21–44.
https://doi.org/10.1112/plms/s2-45.1.21 ; statement also recorded by NIST:
https://dlmf.nist.gov/27.12.E2 . This previously established result is an
input to the proof, not a newly proved theorem here.

**Formal Conjectures statement** — https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/100475.lean ; upstream software is Apache-2.0, but its third-party mathematical content follows source license rules. No upstream Lean file has been copied here. The definitions `reverseDigits`, `aStartAt` and `IsUltimatelyPeriodic` (© 2026 The Formal Conjectures Authors, Apache-2.0, blob a2a7c03062ae8dd107182c0d11662134bdf7924f) are restated verbatim, with attribution, in `lean/A100475/Basic.lean`. A copy of the Apache License 2.0 is in `lean/THIRD_PARTY_LICENSE-Apache-2.0.txt`. The current upstream question is existential: whether any positive initial value enters a loop. The result here proves the NEGATION; changing only its tag without correcting the proposition would be invalid.

**Provenance** — AI-assisted Codex development and computational certificate,
then GPT-6 independent reasoning and second-checker review (2026-11-08).
Review and novelty searches do not establish global priority, official
acceptance, or end-to-end Lean formal verification.

**Mathlib** — the Lean formalization depends on Mathlib (Apache-2.0, https://github.com/leanprover-community/mathlib4), including Chebyshev's bound `Chebyshev.theta_le_log4_mul_x`. Mathlib is fetched at build time and not redistributed here.
