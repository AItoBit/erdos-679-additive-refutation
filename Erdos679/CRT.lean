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

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Lean.Elab.Tactic.Omega

/-!
# A finite-window reduction for Erdős problem 679

These lemmas lift an explicitly assumed finite-window estimate to all sufficiently
large inputs. They do not establish that the finite-window hypothesis holds.
-/
@[expose] public section

namespace Erdos679

/-- Divisibility preserves the number of distinct prime factors when the target is nonzero. -/
theorem cardDistinctFactors_le_of_dvd {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    ArithmeticFunction.cardDistinctFactors a ≤ ArithmeticFunction.cardDistinctFactors b := by
  simpa only [← Nat.toFinset_factors, List.card_toFinset,
    ArithmeticFunction.cardDistinctFactors_apply] using
      Finset.card_le_card (Nat.primeFactors_mono hab hb)

/-- A complete residue window gives a suitable shift for each input beyond that window. -/
theorem finite_window_lifting (M K : ℕ) (hM : 0 < M) (F : ℕ → ℝ) (C : ℝ)
    (hwindow : ∀ k, K < k → k ≤ K + M →
      F k + C ≤ (ArithmeticFunction.cardDistinctFactors M : ℝ))
    {n : ℕ} (hn : K + M < n) :
    ∃ k < n, K < k ∧ F k + C ≤ (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) := by
  let k := K + 1 + (n - K - 1) % M
  have hr := Nat.mod_lt (n - K - 1) hM
  have hklo : K < k := by omega
  have hkhi : k ≤ K + M := by omega
  have hkn : k < n := by omega
  have hdiv : M ∣ n - k := by
    have heq := Nat.mod_add_div (n - K - 1) M
    refine ⟨(n - K - 1) / M, ?_⟩
    omega
  refine ⟨k, hkn, hklo, le_trans (hwindow k hklo hkhi) ?_⟩
  exact Nat.cast_le.mpr (cardDistinctFactors_le_of_dvd hdiv (by omega))

/-- The finite-window hypothesis is sufficient for an eventual lower bound. -/
theorem eventually_finite_window_lifting (M K : ℕ) (hM : 0 < M) (F : ℕ → ℝ) (C : ℝ)
    (hwindow : ∀ k, K < k → k ≤ K + M →
      F k + C ≤ (ArithmeticFunction.cardDistinctFactors M : ℝ)) :
    ∀ᶠ n in Filter.atTop,
      ∃ k < n, K < k ∧ F k + C ≤ (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) := by
  apply Filter.eventually_atTop.mpr
  refine ⟨K + M + 1, ?_⟩
  intro n hn
  exact finite_window_lifting M K hM F C hwindow (by omega)

end Erdos679
