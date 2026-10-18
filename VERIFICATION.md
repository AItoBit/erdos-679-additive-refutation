# Verification record

## Lean 4.33.1 baseline

The independently written source baseline was checked in the existing
formal-conjectures environment, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.
All five modules compiled with `lake env lean -j1 -DwarningAsError=true`.

The final theorem `Erdos679.additive_refutation` reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Its proof has no PNT hypothesis, no theorem holes, and no native computation.
Two independent agents reviewed mathematical/source correspondence. This is
agent review, not human expert review.

## Supported-toolchain port

The same proof has been ported into the module system with Lean `4.35.0-rc2`
and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
Linux CI for the initial commit `682b2277ab59addb95ec18455148428e9bb39ee6`
elaborated all proof modules, `Solution`, and `Challenge`. Its strict build
reported one deprecated import; that import is corrected in this revision.
The CI workflow performs the full warning-free build and final theorem axiom
inspection. Its run identifies the exact checked commit. Palomar's complete
mechanical preflight is separate; no registry acceptance is asserted here.
`Challenge.lean` deliberately has one statement-comparison hole; it is excluded
from the solution's dependency closure.
