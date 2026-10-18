/-
Copyright 2026 The Erdős 679 Formalization Contributors.
Licensed under the Apache License, Version 2.0. See LICENSE.
-/
module

public import Erdos679.Analytic
public import Erdos679.Gap
public import Erdos679.CRT

/-!
# Refutation of the additive strengthening of Erdős problem 679

The primorial construction follows the argument credited to DottedCalculator in
https://www.erdosproblems.com/forum/thread/679#post-2975.
The theorem below concerns the additive strengthening, not the main multiplicative question.
-/

@[expose] public section

open Filter Real
open scoped Topology

namespace Erdos679

/-- Adding a fixed natural number changes the logarithm of a positive integer by at most that number. -/
lemma log_nat_add_le (P K : ℕ) (hP : 0 < P) :
    log ((P + K : ℕ) : ℝ) ≤ log (P : ℝ) + K := by
  have hp : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have hpone : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hsum : (0 : ℝ) < (P : ℝ) + K := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsum hp)
  rw [Real.log_div hsum.ne' hp.ne'] at hlog
  have hratio : ((P : ℝ) + K) / P ≤ (K : ℝ) + 1 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hpone)]
  push_cast
  linarith

/-- A fixed shift preserves a positive linear saving in the primorial logarithm. -/
lemma eventually_shifted_log_primeProduct_le (K : ℕ) :
    ∀ᶠ m : ℕ in atTop, log ((primeProduct m + K : ℕ) : ℝ) ≤
      m * (log m + log (log m) - (1 / 5 : ℝ)) := by
  have hlim : Tendsto (fun m : ℕ => (K : ℝ) / m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall := hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [eventually_log_primeProduct_le, hsmall,
    eventually_gt_atTop (0 : ℕ)] with m hm hs hm0
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hs' := (div_lt_iff₀ hmp).mp hs
  have hshift := log_nat_add_le (primeProduct m) K (primeProduct_pos m)
  nlinarith

/-- The lower primorial estimate also holds after a fixed nonnegative shift. -/
lemma eventually_shifted_log_primeProduct_gt (K : ℕ) :
    ∀ᶠ m : ℕ in atTop, m * (log m - 2) < log ((primeProduct m + K : ℕ) : ℝ) := by
  filter_upwards [eventually_log_primeProduct_gt] with m hm
  apply hm.trans_le
  apply Real.log_le_log (Nat.cast_pos.mpr (primeProduct_pos m))
  exact_mod_cast (Nat.le_add_right (primeProduct m) K)

/-- For every additive constant and every lower bound on the shift, all sufficiently
large inputs admit a shift violating that additive bound. -/
theorem additive_refutation (C : ℝ) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ k < n, K < k ∧
      log (k : ℝ) / log (log k) + C ≤
        (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) := by
  let K₀ := max K (Nat.ceil (exp (exp 1)) + 1)
  have hK : K ≤ K₀ := le_max_left _ _
  have hKlarge : exp (exp 1) < (K₀ : ℝ) := by
    have hceil : exp (exp 1) ≤ (Nat.ceil (exp (exp 1)) : ℝ) := Nat.le_ceil _
    have hlt : (Nat.ceil (exp (exp 1)) : ℝ) < (K₀ : ℝ) := by
      exact_mod_cast (Nat.lt_succ_self (Nat.ceil (exp (exp 1)))).trans_le (le_max_right K _)
    exact hceil.trans_lt hlt
  let θ : ℕ → ℝ := fun m => log ((primeProduct m + K₀ : ℕ) : ℝ)
  have hgap := gap_from_log_bounds θ (1 / 5) (by norm_num)
    (eventually_shifted_log_primeProduct_le K₀)
    (eventually_shifted_log_primeProduct_gt K₀) C
  obtain ⟨m, hm⟩ := hgap.exists
  have hwindow : ∀ k, K₀ < k → k ≤ K₀ + primeProduct m →
      log (k : ℝ) / log (log k) + C ≤
        (ArithmeticFunction.cardDistinctFactors (primeProduct m) : ℝ) := by
    intro k hklo hkhi
    have hk : exp (exp 1) < (k : ℝ) :=
      hKlarge.trans (Nat.cast_lt.mpr hklo)
    have hxy : (k : ℝ) ≤ ((K₀ + primeProduct m : ℕ) : ℝ) := Nat.cast_le.mpr hkhi
    have hmono := log_log_quotient_mono hk hxy
    have hbound : log ((K₀ + primeProduct m : ℕ) : ℝ) /
        log (log ((K₀ + primeProduct m : ℕ) : ℝ)) + C < (m : ℝ) := by
      simpa only [θ, Nat.add_comm] using hm
    rw [cardDistinctFactors_primeProduct]
    linarith
  have hlift := eventually_finite_window_lifting (primeProduct m) K₀
    (primeProduct_pos m) (fun k => log (k : ℝ) / log (log k)) C hwindow
  filter_upwards [hlift] with n hn
  obtain ⟨k, hkn, hklo, hbound⟩ := hn
  exact ⟨k, hkn, hK.trans_lt hklo, hbound⟩

end Erdos679


