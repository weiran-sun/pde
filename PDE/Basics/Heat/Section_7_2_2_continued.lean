import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.Basic
import Mathlib.Tactic
import PDE.Section_7_2_1
import PDE.Section_7_2_2


noncomputable section

open Real Set MeasureTheory Filter
open scoped Topology

namespace Chapter7

--------------------------------------------------------------------------------
-- Definitions
--------------------------------------------------------------------------------

variable {α : ℝ} (hα : 0 < α)
variable {g : ℝ → ℝ} (hg_int : Integrable g volume)


/-- The L¹ norm constant C = ∫|g(y)|dy -/
noncomputable def C (g : ℝ → ℝ) : ℝ := ∫ y, |g y|

--------------------------------------------------------------------------------
-- Helper Lemmas
--------------------------------------------------------------------------------

/-- The exponential term in the heat kernel is bounded by 1 -/
lemma exp_heat_le_one (x y α t : ℝ) (hα : 0 < α) (ht : 0 < t) :
    Real.exp (-(x - y)^2 / (4 * α * t)) ≤ 1 := by
  apply exp_le_one_iff.mpr
  apply div_nonpos_of_nonpos_of_nonneg
  · apply neg_nonpos.mpr; positivity
  · positivity

/-- The heat kernel is nonnegative -/
lemma heatKernel_nonneg (α x t : ℝ) (hα : 0 < α) (ht : 0 < t) :
    0 ≤ heatKernel α x t := by
  unfold heatKernel
  positivity

lemma integrable_heatKernel_abs_g (α x t : ℝ) (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g volume) :
    Integrable (fun y => heatKernel α (x - y) t * |g y|) volume := by
  have hg_abs : Integrable (fun y => |g y|) volume := hg.abs

  -- The heat kernel is bounded by a constant
  have hK_bdd : ∃ C, ∀ y, ‖heatKernel α (x - y) t‖ ≤ C := by
    use 1 / Real.sqrt (4 * Real.pi * α * t)
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_bound_pointwise hα ht y).1]
    exact (heatKernel_bound_pointwise hα ht y).2

  -- The heat kernel is measurable
  have hK_meas : AEStronglyMeasurable (fun y => heatKernel α (x - y) t) volume := by
    simpa using meas_heatKernel
  exact Integrable.bdd_mul hg_abs hK_meas hK_bdd


/-- Integrability of heat kernel times g -/
lemma integrable_heatKernel_g (α x t : ℝ) (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g volume) :
    Integrable (fun y => heatKernel α (x - y) t * g y) volume := by
  have hK_bdd : ∃ C, ∀ y, ‖heatKernel α (x - y) t‖ ≤ C := by
    use 1 / Real.sqrt (4 * Real.pi * α * t)
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_bound_pointwise hα ht y).1]
    exact (heatKernel_bound_pointwise hα ht y).2
  have hK_meas : AEStronglyMeasurable (fun y => heatKernel α (x - y) t) volume := by
    simpa using meas_heatKernel
  exact Integrable.bdd_mul hg hK_meas hK_bdd

--------------------------------------------------------------------------------
-- Main Decay Theorem
--------------------------------------------------------------------------------

/--
**Decay Property**: For any fixed position x, the solution decays to 0 as t → ∞.

The proof follows these steps:
1. Use triangle inequality: |u(x,t)| ≤ ∫ Φ(x-y,t)|g(y)|dy
2. Use exp(-(x-y)²/(4αt)) ≤ 1 to bound the integral
3. Pull out the constant 1/√(4παt) to get C/√(4παt)
4. Show this bound → 0 as t → ∞
-/
theorem heat_eq_decay (x α : ℝ) (hα : 0 < α) (hg_int : Integrable g volume) :
    Tendsto (fun t ↦ heatConvolutionHK α g x t) atTop (𝓝 0) := by

  -- Define the bounding function C/√(4παt)
  let bound_func := fun t => (C g) / Real.sqrt (4 * Real.pi * α * t)

  -- Step 1: Establish |u(x,t)| ≤ C/√(4παt) for all large t
  have h_bound : ∀ᶠ t in atTop, |heatConvolutionHK α g x t| ≤ bound_func t := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [heatConvolutionHK, bound_func, C]

    calc |∫ y, heatKernel α (x - y) t * g y|
      _ ≤ ∫ y, |heatKernel α (x - y) t * g y| :=
        abs_integral_le_integral_abs
      _ = ∫ y, heatKernel α (x - y) t * |g y| := by
        congr 1 with y
        rw [abs_mul, abs_of_nonneg (heatKernel_bound_pointwise hα ht y).1]
      _ ≤ ∫ y, (1 / Real.sqrt (4 * Real.pi * α * t)) * |g y| := by
              refine integral_mono ?_ ?_ ?_
              · exact integrable_heatKernel_abs_g α x t hα ht hg_int
              · exact Integrable.const_mul hg_int.abs (1 / Real.sqrt (4 * Real.pi * α * t))
              · intro y
                exact mul_le_mul_of_nonneg_right (heatKernel_bound_pointwise hα ht y).2 (abs_nonneg _)
      _ = (1 / Real.sqrt (4 * Real.pi * α * t)) * ∫ y, |g y| :=
        integral_const_mul _ _
      _ = (∫ y, |g y|) / Real.sqrt (4 * Real.pi * α * t) := by
        simp; ring

  -- Step 2: Show the bound → 0 as t → ∞
  have h_lim : Tendsto bound_func atTop (𝓝 0) := by
    simp only [bound_func]

    -- Rewrite 0 = C * 0
    conv_rhs => rw [show (0 : ℝ) = (C g) * 0 by simp]

    apply Tendsto.const_mul (C g)
    have h2 : Tendsto (fun t => Real.sqrt (4 * Real.pi * α * t)) atTop atTop := by
      simp only [Real.sqrt_eq_rpow]
      apply (tendsto_rpow_atTop (by norm_num : 0 < (1/2 : ℝ))).comp
      exact Tendsto.const_mul_atTop (by positivity : 0 < 4 * Real.pi * α) tendsto_id
    exact tendsto_inv_atTop_zero.comp h2

  -- Step 3: Apply squeeze theorem
  rw[tendsto_zero_iff_abs_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
    (Eventually.of_forall (fun t => abs_nonneg _)) h_bound

end Chapter7
