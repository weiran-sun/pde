import Mathlib
import PDE.Basics.Heat.HeatKernelND
import PDE.Basics.Laplace.FundamentalSolutionND
import PDE.Basics.LaplacianBridge
import PDE.Basics.Laplace.LaplaceDistributionalLaplacian

/-!
# Undergraduate Problem 23: The Distributional Laplacian of `1/‖x‖` in ℝ³

Source: `pde_latex/problems/undergraduate/problem_23.tex` (Math 418/718 Fall
2022, HW-3, Part 2, Problem 2).

## Informal statement

> **(a)** Let `f : ℝ³ → ℝ` be `f(x) = |x|`. Find `∇f` for `x ≠ 0`.
>
> **(b)** Show that `Δ(1/|x|) = 0` for `x ∈ ℝ³ \ {0}`.
>
> **(c)** Show that `lim_{ε→0⁺} ∫_{B(0,ε)} (1/|x|) Δφ(x) dx = 0` for every
> `φ ∈ C^∞`, where `B(0,ε) ⊆ ℝ³` is the ball of radius `ε` centred at zero.
>
> **(d)** Use (b) and (c) to prove `-Δ(1/|x|) = 4π δ₀` in the sense of
> distributions.

## Semantic alignment

* The ambient space is `E 3 = EuclideanSpace ℝ (Fin 3)` (`Heat.E`); the
  Laplacian is `Heat.laplacian` (trace of the Fréchet derivative of the
  gradient field), identified with Mathlib's `Δ` by
  `Basics.laplacian_eq_mathlib` (`PDE/Basics/LaplacianBridge.lean`).
* Part (a): the gradient of the norm at `x ≠ 0` is the radial unit vector
  `‖x‖⁻¹ • x` — Mathlib's `gradient` applied to `fun y => ‖y‖`.
* Part (b): pointwise harmonicity of `y ↦ 1/‖y‖` away from the origin.
* Part (c): the limit is along the right-neighborhood filter `𝓝[>] 0`; the
  smoothness hypothesis `ContDiff ℝ ∞ φ` matches the source's `φ ∈ C^∞`
  (no compact support is needed for this part).
* Part (d): the distributional identity is stated in bare pairing form: for
  every test function `φ ∈ C_c^∞(ℝ³)`,
  `∫ (1/‖x‖) Δφ dx = -4π φ(0)`, i.e. `⟨-Δ(1/‖x‖), φ⟩ = 4π φ(0)`.
  Per the project route (blueprint chapter
  `PDE_Basics_Laplace_LaplaceDistributionalLaplacian.tex`), the proof goes
  through the mollified kernel `ψ_a(x) = (‖x‖² + a²)^{-1/2}` using volume
  integrals only — no sphere surface integrals.
-/

open MeasureTheory Filter Heat
open scoped Topology ContDiff

/-- The ambient Euclidean 3-space `EuclideanSpace ℝ (Fin 3)` (= `Heat.E 3`). -/
local notation "E3" => Heat.E 3

namespace Problems.Undergraduate.Problem23

/-- **Part (a): gradient of the norm** (blueprint `lem:problem23-gradient-norm`).
For `x ≠ 0`, the function `f(y) = ‖y‖` is differentiable at `x` with
`∇f(x) = x / ‖x‖`, the radial unit vector. -/
theorem gradient_norm_eq {x : E3} (hx : x ≠ 0) :
    gradient (fun y : E3 => ‖y‖) x = ‖x‖⁻¹ • x := by
  rw [gradient, fderiv_norm_eq x hx, map_smul, LinearIsometryEquiv.symm_apply_apply, one_div]

/-- **Part (b): harmonicity of `1/‖x‖` away from the origin**
(blueprint `lem:problem23-laplacian-inv-norm-zero`).
For `x ≠ 0`, the Laplacian of `y ↦ 1/‖y‖` vanishes at `x`. -/
theorem laplacian_inv_norm_eq_zero {x : E3} (hx : x ≠ 0) :
    Heat.laplacian (fun y : E3 => 1 / ‖y‖) x = 0 :=
  _root_.laplacian_inv_norm_eq_zero hx

/-- **Part (c): the small-ball integral vanishes in the limit**
(blueprint `lem:problem23-ball-integral-vanishes`).
For every smooth `φ : ℝ³ → ℝ`,
`∫_{B(0,ε)} (1/‖x‖) Δφ(x) dx → 0` as `ε → 0⁺`. -/
theorem tendsto_ball_integral_inv_norm_mul_laplacian
    (φ : E3 → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Tendsto (fun ε : ℝ => ∫ x in Metric.ball (0 : E3) ε,
        (1 / ‖x‖) * Heat.laplacian φ x) (𝓝[>] 0) (𝓝 0) := by
  have hcont : Continuous (fun x : E3 => Heat.laplacian φ x) := by
    show Continuous (fun x : E3 => _root_.laplacian φ x)
    unfold _root_.laplacian _root_.div_field
    exact continuous_trace.comp (continuousOn_univ.mp
      (fderiv_continuousOn_of_c1 _ _ isOpen_univ
        (gradient_c1_of_c2 _ _ isOpen_univ (contDiff_infty.mp hφ 2).contDiffOn)))
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E3) 1).exists_bound_of_continuousOn
    hcont.continuousOn
  have hint : IntegrableOn (fun x : E3 => (1 / ‖x‖) * Heat.laplacian φ x)
      (Metric.ball (0 : E3) 1) volume := by
    refine Integrable.mono' ((inv_norm_integrableOn_ball 1 one_pos).mul_const M)
      ((inv_norm_integrableOn_ball 1 one_pos).aestronglyMeasurable.mul
        hcont.aestronglyMeasurable.restrict) ?_
    rw [ae_restrict_iff' measurableSet_ball]
    refine Eventually.of_forall fun x hx => ?_
    rw [norm_mul, Real.norm_eq_abs (1 / ‖x‖), abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (hM x (Metric.ball_subset_closedBall hx)) (by positivity)
  have hvol : Tendsto (fun ε : ℝ =>
      (volume.restrict (Metric.ball (0 : E3) 1)) (Metric.ball (0 : E3) ε))
      (𝓝[>] 0) (𝓝 0) := by
    have hiInter : ⋂ r > (0 : ℝ), Metric.ball (0 : E3) r = {0} := by
      ext y
      simp only [Set.mem_iInter, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
      constructor
      · intro h
        by_contra hy
        exact absurd (h ‖y‖ (norm_pos_iff.mpr hy)) (lt_irrefl _)
      · rintro rfl r hr
        simpa using hr
    have hzero : (volume.restrict (Metric.ball (0 : E3) 1)) {0} = 0 :=
      nonpos_iff_eq_zero.mp
        ((Measure.restrict_apply_le _ _).trans_eq (measure_singleton 0))
    have h := MeasureTheory.tendsto_measure_biInter_gt
      (μ := volume.restrict (Metric.ball (0 : E3) 1))
      (s := fun ε : ℝ => Metric.ball (0 : E3) ε) (a := 0)
      (fun r _ => measurableSet_ball.nullMeasurableSet)
      (fun i j _ hij => Metric.ball_subset_ball hij)
      ⟨1, one_pos, ((Measure.restrict_apply_le _ _).trans_lt measure_ball_lt_top).ne⟩
    rw [hiInter, hzero] at h
    exact h
  refine Filter.Tendsto.congr' ?_ (hint.tendsto_setIntegral_nhds_zero hvol)
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  rw [Measure.restrict_restrict measurableSet_ball,
      Set.inter_eq_self_of_subset_left (Metric.ball_subset_ball hε.2.le)]

/-- **Part (d): the distributional Laplacian of `1/‖x‖` is `-4π δ₀`**
(blueprint `thm:problem23-dist-laplacian`).
For every test function `φ ∈ C_c^∞(ℝ³)`,
`∫_{ℝ³} (1/‖x‖) Δφ(x) dx = -4π φ(0)`; equivalently, `-Δ(1/‖x‖) = 4π δ₀`
in the sense of distributions. -/
theorem dist_laplacian_inv_norm
    (φ : E3 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    ∫ x : E3, (1 / ‖x‖) * Heat.laplacian φ x = -(4 * Real.pi) * φ 0 :=
  Laplace.dist_laplacian_inv_norm hφ hsupp

/-- **Part (d), rearranged pairing form**
(blueprint `thm:problem23-dist-laplacian-pairing`).
The pairing `⟨-Δ(1/‖x‖), φ⟩ = -∫ (1/‖x‖) Δφ` equals `4π φ(0)` — the display
`-Δ(1/‖x‖) = 4π δ₀` exactly as the source writes it. -/
theorem neg_dist_laplacian_inv_norm
    (φ : E3 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    -∫ x : E3, (1 / ‖x‖) * Heat.laplacian φ x = 4 * Real.pi * φ 0 := by
  rw [dist_laplacian_inv_norm φ hφ hsupp]
  ring

end Problems.Undergraduate.Problem23
