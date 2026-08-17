import Mathlib
import PDE.Basics.Heat.HeatKernelND
import PDE.Basics.Laplace.FundamentalSolutionND
import PDE.Background.CalculusMeasureTheory.GraphHausdorffMeasure.R3GraphMeasure

/-!
# Undergraduate Problem 22: Verifying the Divergence Theorem for a Cubic Radial Field

Source: `pde_latex/problems/undergraduate/problem_22.tex` (Math 418/718 Fall 2022,
HW-2, Part 2, Problem 1).

## Informal statement

> Let `Ω ⊆ ℝ³` be the unit ball centred at zero. Let `f(x) = x|x|²` for `x ∈ ℝ³`.
> Justify that the divergence theorem holds for `f`, that is, prove by directly
> computing both sides to show that
> `∫_Ω ∇·f(x) dx = ∫_{∂Ω} f(x)·n(x) dS`,
> where `n` denotes the outward normal on the boundary of `Ω` and the right-hand
> side is the surface integral.

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem22.tex`:

* The ambient space is `E 3 = EuclideanSpace ℝ (Fin 3)` (`Heat.E`), the field
  is `fun y => ‖y‖^2 • y`, and the divergence `∇·f` is `Heat.div_field`, the
  trace of the Fréchet derivative — the coordinate-free form of `∑ᵢ ∂_{xᵢ} fᵢ`.
* On the unit sphere the outward unit normal is `n(x) = x` (radial direction, of
  unit length since `‖x‖ = 1` there), so the flux integrand `f(x)·n(x)` is the
  real inner product `⟪‖x‖^2 • x, x⟫_ℝ`.
* The surface measure `dS` is the Euclidean-normalized 2-dimensional Hausdorff
  measure `μHE[2]`; its total mass on the unit sphere is `4π` by
  `GraphAreaFull.sphere_area_unit` (whose `E3'` is an abbrev of
  `EuclideanSpace ℝ (Fin 3)`).
* Both sides are computed independently — exactly as the source demands — and
  each equals `4π`.
-/

open MeasureTheory Heat
open scoped MeasureTheory RealInnerProductSpace

/-- The ambient Euclidean 3-space `EuclideanSpace ℝ (Fin 3)` (= `Heat.E 3`). -/
local notation "E3" => Heat.E 3

namespace Problems.Undergraduate.Problem22

/-- **Divergence of the cubic radial field** (blueprint `lem:problem22-div-eq`).
For every `x ∈ ℝ³`, the divergence of the field `f(y) = ‖y‖² • y` — the trace of
its Fréchet derivative at `x` — equals `5‖x‖²`. -/
theorem div_field_radial (x : E3) :
    Heat.div_field (fun y : E3 => ‖y‖ ^ 2 • y) x = 5 * ‖x‖ ^ 2 := by
  have hF : HasFDerivAt (fun y : E3 => ‖y‖ ^ 2 • y)
      ((‖x‖ ^ 2 : ℝ) • ContinuousLinearMap.id ℝ (E 3) +
        (((2 : ℝ) • innerSL ℝ x)).smulRight x) x :=
    (hasFDerivAt_norm_sq x).smul (hasFDerivAt_id x)
  unfold Heat.div_field
  rw [hF.fderiv, Laplace.trace_radial_field_deriv]
  push_cast
  ring

/-- **The volume side equals `4π`** (blueprint `lem:problem22-volume-side`).
The volume integral of the divergence `5‖x‖²` over the open unit ball is `4π`. -/
theorem volume_integral_eq :
    ∫ x in Metric.ball (0 : E3) 1, 5 * ‖x‖ ^ 2 = 4 * Real.pi := by
  -- Rewrite the set integral as a full-space integral of a radial profile.
  have h1 : ∫ x in Metric.ball (0 : E3) 1, 5 * ‖x‖ ^ 2
      = ∫ x : E3, (Set.Iio (1 : ℝ)).indicator (fun r => 5 * r ^ 2) ‖x‖ := by
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    congr 1
    ext x
    by_cases hx : ‖x‖ < 1
    · simp [Set.indicator, Metric.mem_ball, dist_zero_right, hx]
    · simp [Set.indicator, Metric.mem_ball, dist_zero_right, hx]
  rw [h1, MeasureTheory.integral_fun_norm_addHaar volume
    ((Set.Iio (1 : ℝ)).indicator (fun r => 5 * r ^ 2))]
  have hdim : Module.finrank ℝ (E 3) = 3 := finrank_euclideanSpace_fin
  rw [hdim]
  -- The radial integral: ∫_{(0,∞)} y² · 1_{[0,1)}(y) · 5y² dy = ∫₀¹ 5y⁴ = 1.
  have hrad : ∫ y in Set.Ioi (0 : ℝ),
      y ^ (3 - 1) • (Set.Iio (1 : ℝ)).indicator (fun r => 5 * r ^ 2) y = 1 := by
    have hind : ∀ y ∈ Set.Ioi (0 : ℝ),
        y ^ (3 - 1) • (Set.Iio (1 : ℝ)).indicator (fun r => 5 * r ^ 2) y
          = (Set.Ioo (0 : ℝ) 1).indicator (fun r => 5 * r ^ 4) y := by
      intro y hy
      by_cases hy1 : y < 1
      · simp only [Set.indicator_of_mem (Set.mem_Iio.mpr hy1),
          Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hy, hy1⟩), smul_eq_mul]
        ring
      · simp [Set.indicator_of_notMem, hy1, Set.mem_Iio, Set.mem_Ioo]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hind,
      ← MeasureTheory.integral_indicator measurableSet_Ioi]
    have : (Set.Ioi (0 : ℝ)).indicator ((Set.Ioo (0 : ℝ) 1).indicator fun r => 5 * r ^ 4)
        = (Set.Ioo (0 : ℝ) 1).indicator (fun r => 5 * r ^ 4) := by
      ext y
      by_cases hy : y ∈ Set.Ioo (0 : ℝ) 1
      · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hy.1), Set.indicator_of_mem hy]
      · by_cases hy0 : y ∈ Set.Ioi (0 : ℝ)
        · rw [Set.indicator_of_mem hy0, Set.indicator_of_notMem hy]
        · rw [Set.indicator_of_notMem hy0, Set.indicator_of_notMem hy]
    rw [this, MeasureTheory.integral_indicator measurableSet_Ioo,
      show Set.Ioo (0:ℝ) 1 = Set.Ioo 0 1 from rfl]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    simp only [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [hrad]
  -- The volume of the unit ball in ℝ³ is 4π/3.
  have hvol : volume.real (Metric.ball (0 : E3) 1) = Real.pi * 4 / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    simp [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi * 4 / 3)]
  rw [hvol]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- **The surface side equals `4π`** (blueprint `lem:problem22-surface-side`).
The flux of `f` through the unit sphere, computed against the Euclidean-normalized
2-dimensional Hausdorff measure, is `4π`. Here `x` itself is the outward unit
normal `n(x)` at `x ∈ 𝕊²`, so the integrand is exactly `f(x)·n(x)`. -/
theorem surface_integral_eq :
    ∫ x in Metric.sphere (0 : E3) 1, ⟪(‖x‖ ^ 2 : ℝ) • x, x⟫ ∂μHE[2]
      = 4 * Real.pi := by
  -- On the sphere ‖x‖ = 1, so the integrand is pointwise 1.
  have hpt : ∀ x ∈ Metric.sphere (0 : E3) 1,
      ⟪(‖x‖ ^ 2 : ℝ) • x, x⟫ = (1 : ℝ) := by
    intro x hx
    have hnx : ‖x‖ = 1 := by simpa [dist_zero_right] using hx
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hnx]
    norm_num
  rw [MeasureTheory.setIntegral_congr_fun
      (Metric.isClosed_sphere.measurableSet) hpt,
    MeasureTheory.setIntegral_const]
  rw [smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
    show Metric.sphere (0 : E3) 1 = Metric.sphere (0 : GraphAreaFull.E3') 1 from rfl,
    GraphAreaFull.sphere_area_unit, ENNReal.toReal_ofReal (by positivity)]

/-- **Problem 22: divergence-theorem check for the cubic radial field**
(blueprint `thm:problem22-divergence-check`).
The divergence theorem holds for the field `f(x) = ‖x‖² • x` on the open unit
ball: the volume integral of the divergence equals the boundary flux. -/
theorem divergence_check :
    ∫ x in Metric.ball (0 : E3) 1, Heat.div_field (fun y : E3 => ‖y‖ ^ 2 • y) x
      = ∫ x in Metric.sphere (0 : E3) 1, ⟪(‖x‖ ^ 2 : ℝ) • x, x⟫ ∂μHE[2] := by
  have hLHS : ∫ x in Metric.ball (0 : E3) 1,
      Heat.div_field (fun y : E3 => ‖y‖ ^ 2 • y) x
        = ∫ x in Metric.ball (0 : E3) 1, 5 * ‖x‖ ^ 2 :=
    MeasureTheory.setIntegral_congr_fun measurableSet_ball
      fun x _ => div_field_radial x
  rw [hLHS, volume_integral_eq, surface_integral_eq]

end Problems.Undergraduate.Problem22
