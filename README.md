# Erdős 679: the known additive refutation

This project proves the **known refutation of the additive strengthening** of
[Erdős problem 679](https://www.erdosproblems.com/679). The main multiplicative
question remains open. No mathematical novelty is claimed.

For every real number `C` and natural number `K`, every sufficiently large `n`
admits `K < k < n` such that

\[
\omega(n-k) \ge \frac{\log k}{\log\log k}+C.
\]

Here `ω` counts distinct prime factors. The named theorem is
`Erdos679.additive_refutation` in [Solution.lean](Solution.lean).
Its proof is unconditional and uses only Mathlib as a direct dependency.

The argument is credited to **DottedCalculator** in the
[problem discussion](https://www.erdosproblems.com/forum/thread/679#post-2975).
A prior conditional Lean formalization by **Aristotle**, supplied and edited by
**llllvvuu**, is credited in [SOURCES.md](SOURCES.md). This implementation was
written independently using a fixed residue window and Chebyshev estimates.
The earlier implementation was not copied into this project.

## Proof

Let `P_m` be the product of the first `m` primes. Mathlib's Chebyshev estimate
implies `p_n ≤ 1.5 n log n` eventually. Summing its logarithm and applying
Stirling gives

\[
m(\log m-2)<\log P_m
\le m(\log m+\log\log m-0.3)
\]

eventually. Enlarge `K` to `K₀ > exp(exp 1)`. For fixed `K₀`,
`θ_m = log(P_m + K₀)` satisfies the same lower bound and the upper bound with
saving `0.2m`. Consequently `θ_m / log θ_m + C < m` for sufficiently large `m`.

Fix one such `m`. If `n > K₀ + P_m`, take
`k = K₀ + 1 + ((n - K₀ - 1) % P_m)`.
Then `K₀ < k ≤ K₀ + P_m < n` and `P_m` divides `n-k > 0`, so
`ω(n-k) ≥ m`. The function `log x / log log x` is increasing above `exp(exp 1)`.
The estimate at the end of the residue window therefore proves the result.
See [SOURCES.md](SOURCES.md) for details and exact attribution.

## Reproduce

The toolchain is Lean `4.35.0-rc2`; Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
lake exe cache get
lake --wfail build Solution Challenge
```

`Challenge.lean` deliberately contains one theorem hole for statement
comparison. The proof modules and `Solution.lean` contain no theorem holes.
The Comparator configuration allows only `propext`, `Classical.choice`, and
`Quot.sound` for the solution theorem. Read the verification report for checks
actually run against a particular commit; preparation alone is not verification.

## Responsibility and automation

AItoBit commissioned the development and accepted responsibility as maintainer.
Codex agents generated the Lean implementation, audited the sources, and
independently reviewed the mathematical argument. No human expert review or
manual human proof-writing is claimed. See `formalization.yaml` for metadata.

The implementation is released under the Apache License 2.0.
