# Closure decision: original A100475 loop question

resolution: closed
workflow: verified
verification: mixed
closure_claim: our_complete_proof
community_acceptance: unassessed
worldwide_priority: not_established

The exact original positive-start question is answered NO. Every positive
orbit of reversal of the nth prime eventually strictly increases and tends
to infinity. See PROOF.md for all quantifiers and its finite-to-infinite
argument, and AUDIT.md for prior status, credit, and limitations.

Gate assessment against 03_VERIFICATION_AND_CLOSURE.md:

1. Identity passes: original source archived, one-based indexing and
   positive domain verified; the existential question is answered false.
2. Prior-status search passes within its documented scope: live primary
   entry and official source still ask the question; no prior complete
   resolution found. Search limitations are stated, not treated as proof
   of priority.
3. Completeness passes: established Rosser theorem, proved decimal bridge,
   exhaustive verified ranks on the entire finite complement, and proved
   divergence/nonperiodicity. No unresolved lemma or probabilistic test.
4. Independent audit passes via different prime/reversal algorithms and
   a rank-independent graph check. Analytic review is same-model, not an
   external expert review.
5. Reproducibility passes: exact source/code/certificate, SHA-256 manifest,
   versions, commands, and successful fresh-directory replay supplied.
6. No new Lean proof is used. The archived .lean source contains the
   original `sorry`; it is not submitted as a proof. The result is an
   ordinary proof with an independently checked finite certificate.
7. Credit/prior-equivalent audit supplied; Rosser and original authors
   credited. Independent publication priority and community acceptance
   are not self-awarded.

This internal CLOSED label means the stated original mathematical question
has a complete supplied proof under the stated verification scope. It is
not a claim of journal acceptance, external review, or full formalization.
