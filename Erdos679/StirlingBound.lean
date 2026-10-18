/-
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

/-! # Elementary upper bounds for the logarithm of a factorial -/

@[expose] public section

open Filter Real
open scoped Topology

namespace Erdos679

/-- An elementary upper bound obtained from the decreasing Stirling sequence. -/
theorem log_factorial_le_stirling (n : ℕ) (hn : 1 ≤ n) :
    log (n.factorial : ℝ) ≤ (n : ℝ) * log n - n + 1 + log n / 2 := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (n - 1))
  change log (Stirling.stirlingSeq ((n - 1).succ)) ≤
    log (Stirling.stirlingSeq 1) at h
  have hsucc : (n - 1).succ = n := by omega
  rw [hsucc, Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
    Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne',
    Real.log_div hnpos.ne' (Real.exp_ne_zero _), Real.log_exp] at h
  linarith

/-- For sufficiently large natural numbers the linear saving can be chosen as $0.9n$. -/
theorem eventually_log_factorial_le :
    ∀ᶠ n : ℕ in atTop,
      log (n.factorial : ℝ) ≤ (n : ℝ) * log n - (9 / 10 : ℝ) * n := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum := hone.add (hlog.div_const 2)
  have hsmall := hsum.eventually_lt_const (by norm_num : (0 : ℝ) + 0 / 2 < 1 / 10)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hsmall hn
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hratio : (1 + log (n : ℝ) / 2) / (n : ℝ) < 1 / 10 := by
    change (1 : ℝ) / (n : ℝ) + (log (n : ℝ) / (n : ℝ)) / 2 < 1 / 10 at hsmall
    calc
      (1 + log (n : ℝ) / 2) / (n : ℝ) =
          1 / (n : ℝ) + (log (n : ℝ) / (n : ℝ)) / 2 := by ring
      _ < 1 / 10 := hsmall
  have hlinear := (div_lt_iff₀ hnpos).mp hratio
  have hbound := log_factorial_le_stirling n hn
  linarith

end Erdos679
