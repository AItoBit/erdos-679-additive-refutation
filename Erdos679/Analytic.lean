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

public import Erdos679.StirlingBound
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-!
# Analytic estimates for Erdős problem 679

These elementary estimates use the Chebyshev lower bound already in Mathlib.
The primorial strategy is described in the discussion of Erdős problem 679:
https://www.erdosproblems.com/forum/thread/679#post-2975.
-/

@[expose] public section

open Filter Real
open scoped Topology

namespace Erdos679

lemma log_add_div_tendsto_zero (b : ℝ) :
    Tendsto (fun x : ℝ => log (x + b) / x) atTop (𝓝 0) := by
  have h := (Real.tendsto_log_comp_add_sub_log b).div_atTop tendsto_id
  have h' := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  convert h.add h' using 1 <;> simp only [id_eq, add_zero]
  ext x
  ring

lemma log_mul_log_ratio (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => log (a * x * log x) / log x) atTop (𝓝 1) := by
  have hc : Tendsto (fun x : ℝ => log a / log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hl : Tendsto (fun x : ℝ => log (log x) / log x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hs := (hc.add (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1))).add hl
  have he : (fun x : ℝ => log (a * x * log x) / log x) =ᶠ[atTop]
      (fun x => log a / log x + 1 + log (log x) / log x) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.log_mul (mul_ne_zero ha.ne' (by positivity)) (Real.log_pos hx).ne',
      Real.log_mul ha.ne' (by positivity)]
    field_simp [(Real.log_pos hx).ne']
  simpa using hs.congr' he.symm

/-- The explicit Chebyshev lower bound, normalized at $a x \log x$. -/
lemma chebyshev_lower_ratio (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ =>
      (((a * x * log x - 1) * log 2 - log (a * x * log x + 2)) /
        log (a * x * log x)) / x) atTop (𝓝 (a * log 2)) := by
  have hx : Tendsto (fun x : ℝ => x * log x) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hax : Tendsto (fun x : ℝ => a * x * log x) atTop atTop := by
    simpa only [mul_assoc] using hx.const_mul_atTop ha
  have hi : Tendsto (fun x : ℝ => 1 / (x * log x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hx
  have hl : Tendsto (fun x : ℝ => log (a * x * log x + 2) / (x * log x))
      atTop (𝓝 0) := by
    have h := ((log_add_div_tendsto_zero 2).comp hax).mul_const a
    convert h using 1 <;> try simp
    ext x
    field_simp
  have hn := (((tendsto_const_nhds :
    Tendsto (fun _ : ℝ => a) atTop (𝓝 a)).sub hi).mul_const (log 2)).sub hl
  have hden := log_mul_log_ratio a ha
  have hquot := hn.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have he : (fun x : ℝ =>
      (((a * x * log x - 1) * log 2 - log (a * x * log x + 2)) /
        log (a * x * log x)) / x) =ᶠ[atTop]
      (fun x => (((a - 1 / (x * log x)) * log 2 -
        log (a * x * log x + 2) / (x * log x)) /
          (log (a * x * log x) / log x))) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hax.eventually_gt_atTop 1] with x hx hax1
    have hx0 : x ≠ 0 := by positivity
    have hl0 : log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp [hx0, hl0, (Real.log_pos hax1).ne']
  simpa using hquot.congr' he.symm

/-- Chebyshev's elementary bound gives a constant strictly below $e$ in the
upper bound for the $n$th prime. -/
lemma eventually_nth_prime_le :
    ∀ᶠ n : ℕ in atTop, (Nat.nth Nat.Prime n : ℝ) ≤
      (3 / 2 : ℝ) * n * log n := by
  have hlim := (chebyshev_lower_ratio (3 / 2) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have hconstant : (1 : ℝ) < (3 / 2) * log 2 := by
    have hlog := Real.lt_log_one_add_of_pos (x := 1) (by norm_num)
    norm_num at hlog
    linarith
  have hbound := hlim.eventually (lt_mem_nhds hconstant)
  have hx : Tendsto (fun n : ℕ => (3 / 2 : ℝ) * n * log n) atTop atTop := by
    have h := tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [mul_assoc, Function.comp_apply] using h.const_mul_atTop (by norm_num : (0 : ℝ) < 3 / 2)
  filter_upwards [hbound, hx.eventually_gt_atTop 1, eventually_gt_atTop (0 : ℕ)]
    with n hn hxn hn0
  have hpi := Chebyshev.pi_ge' hxn
  have hcount : n < Nat.primeCounting ⌊(3 / 2 : ℝ) * n * log n⌋₊ := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlt := (lt_div_iff₀ hnpos).mp hn
    have hreal : (n : ℝ) < Nat.primeCounting ⌊(3 / 2 : ℝ) * n * log n⌋₊ := by
      linarith
    exact_mod_cast hreal
  change n < Nat.count Nat.Prime (⌊(3 / 2 : ℝ) * n * log n⌋₊ + 1) at hcount
  have hp := (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mp hcount
  change Nat.nth Nat.Prime n < ⌊(3 / 2 : ℝ) * n * log n⌋₊ + 1 at hp
  have hpn : Nat.nth Nat.Prime n ≤ ⌊(3 / 2 : ℝ) * n * log n⌋₊ := Nat.lt_succ_iff.mp hp
  exact (show (Nat.nth Nat.Prime n : ℝ) ≤ ⌊(3 / 2 : ℝ) * n * log n⌋₊ by
    exact_mod_cast hpn).trans (Nat.floor_le (by linarith))

/-- Product of the first $m$ primes, with zero-based prime indexing. -/
noncomputable def primeProduct (m : ℕ) : ℕ := ∏ i ∈ Finset.range m, Nat.nth Nat.Prime i

lemma primeProduct_pos (m : ℕ) : 0 < primeProduct m := by
  exact Finset.prod_pos fun i _ => (Nat.prime_nth_prime i).pos

lemma primeProduct_succ (m : ℕ) :
    primeProduct (m + 1) = primeProduct m * Nat.nth Nat.Prime m :=
  Finset.prod_range_succ _ _

lemma factorial_le_primeProduct (m : ℕ) : m.factorial ≤ primeProduct m := by
  induction m with
  | zero => simp [primeProduct]
  | succ m ih =>
    rw [Nat.factorial_succ, primeProduct_succ]
    have hp := Nat.add_two_le_nth_prime m
    exact Nat.mul_le_mul (by omega : m + 1 ≤ Nat.nth Nat.Prime m)
      ih |>.trans_eq (Nat.mul_comm _ _)

lemma log_primeProduct (m : ℕ) :
    log (primeProduct m : ℝ) = ∑ i ∈ Finset.range m, log (Nat.nth Nat.Prime i) := by
  rw [primeProduct, Nat.cast_prod, Real.log_prod]
  intro i _
  exact_mod_cast (Nat.prime_nth_prime i).ne_zero

lemma sum_log_succ (m : ℕ) :
    ∑ i ∈ Finset.range m, log ((i + 1 : ℕ) : ℝ) = log (m.factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

/-- A finite initial segment contributes a constant to the prime-log sum. -/
lemma log_primeProduct_le_sum (N : ℕ) (hN : 2 ≤ N)
    (hp : ∀ i ≥ N, (Nat.nth Nat.Prime i : ℝ) ≤ (3 / 2 : ℝ) * i * log i)
    {m : ℕ} (hm : N ≤ m) (hlog : 1 ≤ log m) :
    log (primeProduct m : ℝ) ≤ log (primeProduct N : ℝ) + log (m.factorial : ℝ) +
      m * (log (3 / 2 : ℝ) + log (log m)) := by
  let g : ℕ → ℝ := fun i => log ((i + 1 : ℕ) : ℝ) +
    (log (3 / 2 : ℝ) + log (log m))
  have hgnonneg (i : ℕ) : 0 ≤ g i := by
    dsimp [g]
    exact add_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i)))
      (add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg hlog))
  have htail : ∑ i ∈ Finset.Ico N m, log (Nat.nth Nat.Prime i) ≤
      ∑ i ∈ Finset.Ico N m, g i := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨hiN, him⟩ := Finset.mem_Ico.mp hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
    have himr : (i : ℝ) ≤ m := by exact_mod_cast him.le
    have hli : 0 ≤ log (i : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ i by omega))
    have hlim : log (i : ℝ) ≤ log m := Real.log_le_log hi0 himr
    have hsize : (Nat.nth Nat.Prime i : ℝ) ≤
        (3 / 2 : ℝ) * (i + 1) * log m := by
      apply (hp i hiN).trans
      apply mul_le_mul
      · nlinarith
      · exact hlim
      · exact hli
      · positivity
    have hplog := Real.log_le_log (by exact_mod_cast (Nat.prime_nth_prime i).pos) hsize
    rw [Real.log_mul (by positivity) (by linarith),
      Real.log_mul (by norm_num) (by positivity)] at hplog
    dsimp [g]
    push_cast
    linarith
  have hprefix : 0 ≤ ∑ i ∈ Finset.range N, g i :=
    Finset.sum_nonneg fun i _ => hgnonneg i
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i => log (Nat.nth Nat.Prime i)) hm
  have hgsplit := Finset.sum_range_add_sum_Ico g hm
  have hgsum : ∑ i ∈ Finset.range m, g i =
      log (m.factorial : ℝ) + m * (log (3 / 2 : ℝ) + log (log m)) := by
    simp only [g, Finset.sum_add_distrib, sum_log_succ, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  rw [log_primeProduct, log_primeProduct]
  linarith

/-- The prime product has a fixed linear saving beyond its leading two terms. -/
lemma eventually_log_primeProduct_le :
    ∀ᶠ m : ℕ in atTop, log (primeProduct m : ℝ) ≤
      m * (log m + log (log m) - (3 / 10 : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_nth_prime_le
  let L := max N 2
  have hL : 2 ≤ L := le_max_right _ _
  have hp : ∀ i ≥ L, (Nat.nth Nat.Prime i : ℝ) ≤ (3 / 2 : ℝ) * i * log i :=
    fun i hi => hN i ((le_max_left _ _).trans hi)
  have hpref : Tendsto (fun m : ℕ => log (primeProduct L : ℝ) / m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall := hpref.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 10)
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop L, eventually_log_factorial_le,
    hsmall, hlogtop.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℕ)]
    with m hm hfact hsmall hlog hm0
  have hbound := log_primeProduct_le_sum L hL hp hm hlog
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  have hprefix := (div_lt_iff₀ hmpos).mp hsmall
  have hconstant := Real.log_le_sub_one_of_pos (x := (3 / 2 : ℝ)) (by norm_num)
  have hcm := mul_le_mul_of_nonneg_left hconstant hmpos.le
  nlinarith

/-- A factorial lower bound is sufficient for the lower primorial estimate. -/
lemma eventually_log_primeProduct_gt :
    ∀ᶠ m : ℕ in atTop, m * (log m - 2) < log (primeProduct m : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hl := Stirling.le_log_factorial_stirling (show m ≠ 0 by omega)
  have hlog : 0 ≤ log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hconstant : 0 ≤ log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.two_le_pi])
  have hprod : log (m.factorial : ℝ) ≤ log (primeProduct m : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast factorial_le_primeProduct m)
  nlinarith

lemma primeFactors_primeProduct (m : ℕ) :
    (primeProduct m).primeFactors =
      (Finset.range m).image (fun i => Nat.nth Nat.Prime i) := by
  induction m with
  | zero => simp [primeProduct]
  | succ m ih =>
    rw [primeProduct_succ, Nat.primeFactors_mul (primeProduct_pos m).ne'
      (Nat.prime_nth_prime m).ne_zero, ih, (Nat.prime_nth_prime m).primeFactors]
    simp [Finset.range_add_one, Finset.image_insert, Finset.union_singleton]

lemma cardDistinctFactors_primeProduct (m : ℕ) :
    ArithmeticFunction.cardDistinctFactors (primeProduct m) = m := by
  have hcard : (primeProduct m).primeFactors.card = m := by
    rw [primeFactors_primeProduct,
      Finset.card_image_of_injective _ (Nat.nth_injective Nat.infinite_setOfPred_prime),
      Finset.card_range]
  simpa only [← Nat.toFinset_factors, List.card_toFinset,
    ArithmeticFunction.cardDistinctFactors_apply] using hcard

lemma primeProduct_strictMono : StrictMono primeProduct := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [primeProduct_succ]
  exact lt_mul_of_one_lt_right (primeProduct_pos m) (Nat.prime_nth_prime m).one_lt

lemma primeProduct_tendsto : Tendsto primeProduct atTop atTop :=
  primeProduct_strictMono.tendsto_atTop

end Erdos679
