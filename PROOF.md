# A100475: no positive starting value leads to a loop

Date: 2026-11-07. Ordinary mathematical proof with an exact, independently
checked finite certificate. No end-to-end Lean verification is claimed.

Let p_n be the nth prime, indexed by p_1=2. Put

    F(n) = rev_10(p_n),  n >= 1,

where rev_10 reverses the usual decimal digits. For every positive integer
x, define a_x(0)=x and a_x(t+1)=F(a_x(t)).

**Theorem.** For every x>=1, the sequence a_x eventually strictly increases
and tends to infinity. In particular, there is no positive starting value
x other than 1 whose sequence is ultimately periodic. The same conclusion
also holds for x=1.

This answers the loop question in [OEIS A100475](https://oeis.org/A100475)
in the negative. Zero is outside the one-based prime-index domain.

## 1. A uniform bound valid at arbitrarily large inputs

Rosser's unconditional theorem states

    p_n > n ln(n)  for every integer n>=1.

The indexing and exact inequality are recorded in
[NIST DLMF 27.12.2](https://dlmf.nist.gov/27.12.E2).
Original attribution: Barkley Rosser, *The n-th Prime is Greater than n log n*,
Proceedings of the London Mathematical Society s2-45(1) (1939), 21–44,
[DOI](https://doi.org/10.1112/plms/s2-45.1.21).
We use this established theorem, not the prime number theorem as an
unquantified asymptotic approximation.

Set B=60000. The elementary inequality e<3 gives

    e^10 < 3^10 = 59049 < B.

For completeness, e=sum_{k>=0}1/k!, and k!>=2^(k-1) for k>=2,
strictly for k>=3, so sum_{k>=2}1/k! < sum_{k>=2}2^(1-k)=1.
Thus e<3. Hence n>B implies ln(n)>10 and therefore

    p_n > 10n.                                      (1)

Every prime has a nonzero last decimal digit: an integer ending in zero
is divisible by 10 and cannot be prime. Reversal therefore preserves the
number of decimal digits of p_n.

Let n have d digits, so 10^(d-1)<=n<10^d. By (1),
p_n>10n>=10^d, so p_n has at least d+1 digits. Its reversal has the same
number of digits, and consequently

    F(n) >= 10^d > n  whenever n>B.                  (2)

In particular, the region n>B is forward invariant. This is a theorem
about all integers above B, not an extrapolation from finite computation.

## 2. The complete remaining finite obligation

The accompanying certificate.tsv gives exactly one row for every n=1,...,B:

    n    p_n    F_n    exit_steps

Its independently verified assertions are:

1. The p_n column consists of all primes in increasing order through
   p_60000=746773, with no missing primes.
2. F_n is the exact decimal reversal of p_n.
3. Each rank r(n)=exit_steps is a positive integer at most 10.
4. If F_n>B, then r(n)=1. If F_n<=B, then
   r(n)=1+r(F_n).

Induction on the positive integer r(n) proves that a start n<=B exits
the interval [1,B] after exactly r(n) steps. Indeed rank 1 has its next
value above B; any larger rank has its next value in [1,B] at rank one
smaller. Thus every positive start reaches a value above B, in at most
10 steps if it starts at most B, and in zero steps otherwise.

The certificate SHA-256 is

    9871bc6f20f6b3fb2e4f4e5a90fc2ae484fe9537f74f87e1781f68f42c92baa0

The generator uses exhaustive trial division and arithmetic digit reversal.
verify_certificate.py uses a separately implemented Eratosthenes sieve and
string reversal. It checks every row and every rank equation. In addition,
it removes all 60000 vertices using Kahn's algorithm on the graph of edges
n -> F_n that remain in [1,B]; this provides a second cycle check that
does not use the supplied ranks.

Sieve completeness is exact: every composite integer at most 746773 has
a prime divisor at most its square root, and is marked by that divisor's
sieve pass. Every marked integer is composite. The checker enumerates all
unmarked integers in order and requires there to be exactly 60000 of them,
matching every certificate prime. It therefore verifies nth-prime indices,
not just the primality of selected entries. All arithmetic is integer;
there are no probable-prime tests or numerical logarithm estimates.

## 3. Conclusion for every positive start

Choose t0 with a_x(t0)>B, whose existence is proved in Section 2. By (2)
and induction, a_x(t+1)>a_x(t)>B for every t>=t0. Since these are integers,
a_x(t0+j)>=a_x(t0)+j; hence a_x tends to infinity.

If the sequence were ultimately periodic, there would be N and P>=1
with a_x(t+P)=a_x(t) for every t>=N. For t>=max(N,t0), strict increase
gives a_x(t+P)>a_x(t), a contradiction. This proves the theorem. QED.

As a second global check, any hypothetical cycle has a maximum M.
If M>B, (2) sends M to a larger cycle member, a contradiction. If M<=B,
the verified decreasing exit ranks exclude the cycle. These two cases
exhaust all finite cycles, of arbitrary length and with arbitrary starts.

## Exact relationship to the formal-conjectures question

The upstream [Formal Conjectures Lean source](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/100475.lean), checked Git blob
a2a7c03062ae8dd107182c0d11662134bdf7924f, defines aStartAt using the
zero-based Nat.nth prime at index k-1 for positive k. This is exactly p_k.
Its positive-start question is the existential assertion

    exists x>0, x!=1 and IsUltimatelyPeriodic(aStartAt x).

Our theorem proves the **negation** of that assertion. In that fetched
version the question is literally written as a theorem of the existential
proposition with `sorry`; it would have to be changed to its negation
(or an answered question) to encode the negative answer. We do not claim
to have proved the false existential statement as written. The separately
proved zero-start behavior in that source is not used as a solution.

## Reproduce

From this directory, without Python optimization flags:

```sh
g++ -O2 -std=c++17 -Wall -Wextra -pedantic build_certificate.cpp -o build_certificate
./build_certificate > generation.json
python verify_certificate.py
python clean_replay.py
```

The finite checker establishes Section 2; the ordinary mathematical
argument in Sections 1 and 3 connects it to the infinite original problem.
The checker is not an end-to-end proof-assistant verification of Rosser's
theorem or the full conclusion.
