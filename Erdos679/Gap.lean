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

public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# An analytic gap criterion for the additive variant of Erdős problem 679

The hypotheses are bounds on a sequence of logarithms. This lemma does not
assert that a primorial sequence satisfies them.
-/

@[expose] public section

open Filter Real
open scoped Topology

namespace Erdos679

/-- The logarithmic comparison function is increasing beyond its small-input singularities. -/
theorem log_log_quotient_mono {x y : ℝ} (hx : exp (exp 1) < x) (hxy : x ≤ y) :
    log x / log (log x) ≤ log y / log (log y) := by
  have hxp : 0 < x := (Real.exp_pos _).trans hx
  have hlx : exp 1 < log x := (Real.lt_log_iff_exp_lt hxp).mpr hx
  have hlogs := Real.log_le_log hxp hxy
  have hanti := Real.log_div_self_antitoneOn hlx.le (hlx.le.trans hlogs) hlogs
  have he : (1 : ℝ) < exp 1 := by
    simp
  have hp : 0 < log (log y) / log y :=
    div_pos (Real.log_pos ((he.trans hlx).trans_le hlogs))
      ((Real.exp_pos 1).trans_le (hlx.le.trans hlogs))
  simpa only [one_div_div] using one_div_le_one_div_of_le hp hanti

/-- A fixed saving in a logarithmic upper bound forces an unbounded additive gap. -/
theorem gap_from_log_bounds (θ : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hupper : ∀ᶠ m : ℕ in atTop,
      θ m ≤ m * (log m + log (log m) - δ))
    (hlower : ∀ᶠ m : ℕ in atTop, m * (log m - 2) < θ m) (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, θ m / log (θ m) + C < m := by
  let C₀ := max C 0
  have hC : 0 ≤ C₀ := le_max_right _ _
  have hL : Tendsto (fun m : ℕ => log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun m : ℕ => log (m : ℝ) / m) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hsmall := (hratio.const_mul (2 * C₀)).eventually
    (gt_mem_nhds (show 2 * C₀ * (0 : ℝ) < δ / 4 by nlinarith))
  have hinv : Tendsto (fun m : ℕ => 2 / log (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have hlog : Tendsto (fun m : ℕ => log (1 - 2 / log (m : ℝ)))
      atTop (𝓝 0) := by
    have hsub := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hinv
    simpa using hsub.log (by norm_num)
  have hlogbound := hlog.eventually (lt_mem_nhds (by linarith : -δ / 2 < (0 : ℝ)))
  have hlarge := tendsto_natCast_atTop_atTop.eventually_gt_atTop C₀
  filter_upwards [hupper, hlower, hsmall, hlogbound, hL.eventually_gt_atTop 3,
    hlarge, eventually_ge_atTop (1 : ℕ)] with m hu hl hs hlogb hLm hmC hm1
  have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < m := by linarith
  have hLp : 0 < log (m : ℝ) := by linarith
  have hloglog : log (log (m : ℝ)) ≤ log m :=
    (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hs' : 2 * C₀ * log (m : ℝ) < (δ / 4) * m := by
    apply (div_lt_iff₀ hmpos).mp
    simpa only [mul_div_assoc] using hs
  have hCA : C₀ * (log (m : ℝ) + log (log m)) < (δ / 4) * m := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hloglog)]
  have hbase : 0 < (m : ℝ) * (log m - 2) := mul_pos hmpos (by linarith)
  have hθone : 1 < θ m := by nlinarith
  have hfactor : 0 < 1 - 2 / log (m : ℝ) := by
    have : 2 / log (m : ℝ) < 1 := (div_lt_one hLp).mpr (by linarith)
    linarith
  have heq : log ((m : ℝ) * (log m - 2)) =
      log m + log (log m) + log (1 - 2 / log m) := by
    have heq' : (m : ℝ) * (log m - 2) = m * log m * (1 - 2 / log m) := by
      field_simp [hLp.ne']
    rw [heq', Real.log_mul (mul_ne_zero hmpos.ne' hLp.ne') hfactor.ne',
      Real.log_mul hmpos.ne' hLp.ne']
  have hθlog := Real.log_lt_log hbase hl
  rw [heq] at hθlog
  have hθlower : log (m : ℝ) + log (log m) - δ / 2 < log (θ m) := by
    linarith
  have hbound : θ m < ((m : ℝ) - C₀) * log (θ m) := by
    calc
      θ m ≤ m * (log m + log (log m) - δ) := hu
      _ < (m - C₀) * (log m + log (log m) - δ / 2) := by
        nlinarith [mul_nonneg hC hδ.le, mul_pos hδ hmpos]
      _ < (m - C₀) * log (θ m) :=
        mul_lt_mul_of_pos_left hθlower (by linarith)
  have hdiv := (div_lt_iff₀ (Real.log_pos hθone)).mpr hbound
  have hCC : C ≤ C₀ := le_max_left _ _
  linarith

end Erdos679
