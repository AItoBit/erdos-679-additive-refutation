/-
Copyright 2026 The Erdős 679 Formalization Contributors.
Licensed under the Apache License, Version 2.0. See LICENSE.
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Challenge: the additive strengthening of Erdős problem 679

This file deliberately leaves the known additive refutation unproved for
statement comparison. Solution.lean contains the complete proof.
The main multiplicative question remains open.
-/

@[expose] public section

set_option warn.sorry false

open Filter Real

namespace Erdos679

/-- Every additive constant and cutoff are eventually violated by a suitable shift. -/
theorem additive_refutation (C : ℝ) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ k < n, K < k ∧
      log (k : ℝ) / log (log k) + C ≤
        (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) := by
  sorry

end Erdos679
