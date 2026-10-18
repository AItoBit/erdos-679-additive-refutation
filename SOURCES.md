# Erdős 679: sources and statement audit

This development addresses the known refutation of the additive strengthening.
It does not resolve the main question with the factor `1 + ε`.
No mathematical novelty is claimed.

## Exact target

For every real `C` and natural `K`, for every sufficiently large natural `n`,
there is a natural `k` such that

\[
K<k<n,\qquad
\omega(n-k)\geq\frac{\log k}{\log\log k}+C.
\]

Here `ω` counts distinct prime factors. The Lean declaration is
`Erdos679.additive_refutation` in `Solution.lean`.
The threshold for `n` may depend on both `C` and `K`.
The condition `k < n` ensures `n - k` is positive, so natural subtraction
does not introduce a zero-input degeneracy. The proof chooses `k` above
`exp (exp 1)`, where the logarithmic quotient is increasing.

This contradicts a uniform additive bound with any constant and any fixed
lower cutoff for `k`. It does not contradict the main proposed multiplicative
bound: an unbounded additive excess can still be smaller than
`ε * log k / log (log k)`.

## Primary source

P. Erdős, *Some unconventional problems in number theory*, Acta Mathematica
Academiae Scientiarum Hungaricae **33** (1979), 71–80. DOI:
[10.1007/BF01903382](https://doi.org/10.1007/BF01903382), MR515121.
The bibliography record [Er79d](https://www.erdosproblems.com/bibs/Er79d)
identifies this article. The accessible author-archive scan is
[1979-23.pdf](https://users.renyi.hu/~p_erdos/1979-23.pdf).
Other articles with the same title appeared in Math. Magazine and Astérisque;
they are not the cited Er79d article.

On printed page 71, `ν(n)` denotes the number of distinct prime factors.
Printed page 72, equation (3), asks for infinitely many `n` with simultaneous
inequalities for `ν(n-k)` and `Ω(n-k)`, for every `k₀(ε) < k < n`.
The distinct-factor inequality is the modern problem page's main question.
Equation (4) proposes additive constants for both functions, with
`k₀(C) < k < n`. Erdős conjectures its failure for every constant and all
sufficiently large `n`. Our theorem for distinct factors alone refutes that
simultaneous additive strengthening and the isolated distinct-factor version.

## Known argument and prior formalization

- [Problem 679](https://www.erdosproblems.com/679) and its
  [discussion](https://www.erdosproblems.com/forum/thread/679#post-2975)
  credit **DottedCalculator**, 11 January 2026, with the primorial argument
  disproving the additive strengthening.
- **llllvvuu** posted a Lean formalization produced by **Aristotle**, with an
  explicit prime-number-theorem hypothesis. The immutable
  [gist revision 31fe2e8d3cb26fc2db675908c8516209c16db0fb](https://gist.github.com/llllvvuu/29912cd94579163bda36b094b4cb4c8b/31fe2e8d3cb26fc2db675908c8516209c16db0fb)
  is dated 12 January 2026. Its author note records these roles.
  Its `Claim_proof` proves the same eventual additive refutation conditional
  on `pn_asymptotic`. That proposition is a hypothesis, not a custom axiom.
  The inspected gist contains no explicit license or dependency manifest.
- The PNT hypothesis has a proved counterpart in
  [PrimeNumberTheoremAnd, commit 55270df807213fc3584523d09e0311d7dc073ff5,
  Consequences.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/55270df807213fc3584523d09e0311d7dc073ff5/PrimeNumberTheoremAnd/Consequences.lean#L974).
  `pn_asymptotic` uses `nth_prime`, defined as `Nat.nth Nat.Prime`.
  That revision uses Lean 4.33.1 and Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`.
  This project does not depend on that external development.

The current Lean implementation was written independently in this session.
It uses a fixed residue window and elementary Chebyshev estimates, rather
than the gist's PNT assumption and primorial index depending on `n`.
The shared primorial strategy is attributed to DottedCalculator. Prior
formalization credit belongs to Aristotle and llllvvuu. These credits are not
claims of endorsement or participation in this implementation.

## Proof derivation and constants

Write `P_m` for the product of the first `m` primes, with zero-based prime
indexing. These primes are distinct, so `ω(P_m) = m`.

1. Mathlib's explicit Chebyshev lower bound for prime counting implies
   `p_n ≤ (3/2) n log n` eventually: the normalized lower estimate tends to
   `(3/2) log 2 > 1`. No PNT is assumed.
2. Summing logarithms of this estimate, and absorbing finitely many initial
   primes, gives
   `log P_m ≤ B + log(m!) + m (log(3/2) + log log m)` for a fixed `B`.
   Stirling's elementary bound gives `log(m!) ≤ m log m - 0.9m` eventually.
   Use `B ≤ 0.1m` eventually and `log(3/2) ≤ 0.5`. Hence
   `log P_m ≤ m (log m + log log m - 0.3)` eventually.
3. The elementary comparison `m! ≤ P_m` and a lower Stirling estimate give
   `m (log m - 2) < log P_m` eventually.
4. Choose `K₀ ≥ K` strictly above `exp(exp 1)`. Since
   `log(P_m + K₀) ≤ log P_m + K₀` and `K₀ < 0.1m` eventually, the shifted
   logarithm `θ_m = log(P_m + K₀)` satisfies the preceding lower bound and
   the upper bound with saving `0.2m`.
5. The abstract gap lemma turns bounds
   `m(log m - 2) < θ_m ≤ m(log m + log log m - δ)`, with fixed `δ > 0`,
   into `θ_m / log θ_m + C < m` eventually. Indeed,
   `log θ_m > log m + log log m - δ/2` eventually, while
   `C₀(log m + log log m) = o(m)` for `C₀ = max C 0`.
6. Fix one sufficiently large `m`. For each `n > K₀ + P_m`, set
   `k = K₀ + 1 + ((n - K₀ - 1) % P_m)`.
   Then `K₀ < k ≤ K₀ + P_m < n`, and `P_m` divides the positive integer
   `n-k`. Thus `ω(n-k) ≥ m`. Monotonicity of `log x / log log x` on the
   chosen range completes the desired inequality.

The finite-window lifting is called `Erdos679/CRT.lean` for organization, but it only
needs one modulus and elementary remainder arithmetic.

## Reading record and limits

- Supplied `679.pdf`: all three rendered page images read by the root agent
  and independently by the source-audit agent. It is a forum printout, not a
  new proof manuscript.
- Er79d: the source-audit agent read the complete extracted text of all ten
  pages and visually checked printed page 72, including equations (3) and
  (4). It did not visually read all ten page images. OCR elsewhere is imperfect.
- Prior gist: author note and complete 397-line Lean file read. This was a
  source and statement audit, not a build of the gist.
- PNT project: relevant definitions, theorem implementation, toolchain,
  manifest, and license inspected; not the whole project or full transitive
  proof dependency closure.
- Lau's newer bound, mentioned by the problem page: only the available
  problem-page description/excerpt was reviewed. The full Lau paper was not
  read in this audit and is not counted as a fully read paper or used in the proof.

This is an agent audit. It is not human peer review. Build, warning, axiom,
Comparator, and independent-kernel results must be taken from the verification
logs for the exact final source snapshot. This document does not assert that
those checks have passed.
