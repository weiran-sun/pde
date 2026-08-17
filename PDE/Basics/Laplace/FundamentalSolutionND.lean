import PDE.Basics.Heat.HeatKernelND
import PDE.Basics.Laplace.PoissonEquation

/-!
# The fundamental solution of the Laplacian in dimension `N`

Dimension-parametric fundamental solution `Φ_N` of the Laplacian on
`E N = EuclideanSpace ℝ (Fin N)` (Choksi, Definition 8.5.1), with the log
branch for `N = 2` and the power branch `-1 / (N (N-2) ω_N ‖x‖^(N-2))` for
`N ≥ 3`, where `ω_N` is the Lebesgue volume of the unit ball in `E N`.

The Laplacian is the `N`-dimensional `Heat.laplacian` of
`PDE/Basics/Heat/HeatKernelND.lean` (trace of the Fréchet derivative of the
gradient field). At `N = 3` the definition recovers the existing 3D
fundamental solution `fundamental_sol_3d`.

Blueprint: `blueprint/src/chapters/PDE_Basics_Laplace_FundamentalSolutionND.tex`.
-/

open MeasureTheory Set InnerProductSpace
open scoped Topology ContDiff

open Heat

namespace Laplace

/-- `ω_N`: the Lebesgue volume of the unit ball `B(0,1) ⊆ E N`.
So `unitBallVolume 2 = π` and `unitBallVolume 3 = 4π/3`. -/
noncomputable def unitBallVolume (N : ℕ) : ℝ :=
  (volume (Metric.ball (0 : E N) 1)).toReal

/-- The fundamental solution of the Laplacian in dimension `N ≥ 2`
(Choksi, Definition 8.5.1): `(1/(2π)) log ‖x‖` for `N = 2` and
`-1 / (N (N-2) ω_N ‖x‖^(N-2))` for `N ≥ 3`. The value at `x = 0` is
irrelevant to every statement below. -/
noncomputable def fundamentalSolution (N : ℕ) (x : E N) : ℝ :=
  if N = 2 then (1 / (2 * Real.pi)) * Real.log ‖x‖
  else -(1 / ((N : ℝ) * ((N : ℝ) - 2) * unitBallVolume N * ‖x‖ ^ (N - 2)))

lemma fundamentalSolution_two (x : E 2) :
    fundamentalSolution 2 x = (1 / (2 * Real.pi)) * Real.log ‖x‖ := by
  simp [fundamentalSolution]

lemma fundamentalSolution_of_three_le {N : ℕ} (hN : 3 ≤ N) (x : E N) :
    fundamentalSolution N x =
      -(1 / ((N : ℝ) * ((N : ℝ) - 2) * unitBallVolume N * ‖x‖ ^ (N - 2))) := by
  rw [fundamentalSolution, if_neg (by omega)]

/-- The unit-ball volume is positive (any dimension). -/
lemma unitBallVolume_pos (N : ℕ) : 0 < unitBallVolume N :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne'
    measure_ball_lt_top.ne

/-- `ω_2 = π`. -/
lemma unitBallVolume_two : unitBallVolume 2 = Real.pi := by
  unfold unitBallVolume
  rw [EuclideanSpace.volume_ball_fin_two]
  simp [ENNReal.toReal_ofReal Real.pi_nonneg]

/-- `ω_3 = 4π/3`. -/
lemma unitBallVolume_three : unitBallVolume 3 = Real.pi * 4 / 3 := by
  unfold unitBallVolume
  rw [EuclideanSpace.volume_ball_fin_three]
  simp [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi * 4 / 3)]

/-- Fréchet derivative of the norm away from the origin:
`D‖·‖(x) = ⟪x, ·⟫ / ‖x‖`. -/
lemma hasFDerivAt_norm_of_ne_zero {n : ℕ} {x : E n} (hx : x ≠ 0) :
    HasFDerivAt (fun x' : E n => ‖x'‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hsq : HasFDerivAt (fun x' : E n => Real.sqrt (‖x'‖ ^ 2))
      ((1 / (2 * Real.sqrt (‖x‖ ^ 2))) • ((2 : ℝ) • innerSL ℝ x)) x :=
    (hasFDerivAt_norm_sq x).sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have hfun : (fun x' : E n => Real.sqrt (‖x'‖ ^ 2)) = fun x' : E n => ‖x'‖ :=
    funext fun x' => by rw [Real.sqrt_sq (norm_nonneg x')]
  rw [hfun] at hsq
  apply hsq.congr_fderiv
  rw [smul_smul, Real.sqrt_sq (norm_nonneg x)]
  congr 1
  have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

/-- Radial chain rule (Fréchet form): if `f : ℝ → ℝ` has derivative `f'` at
`r = ‖x‖` and `x ≠ 0`, then `x' ↦ f ‖x'‖` has Fréchet derivative
`(f' / ‖x‖) ⟪x, ·⟫` at `x`. -/
lemma hasFDerivAt_comp_norm {n : ℕ} {x : E n} (hx : x ≠ 0) {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' ‖x‖) :
    HasFDerivAt (fun x' : E n => f ‖x'‖) ((f' / ‖x‖) • innerSL ℝ x) x := by
  have h := hf.comp_hasFDerivAt x (hasFDerivAt_norm_of_ne_zero hx)
  apply h.congr_fderiv
  rw [smul_smul, div_eq_mul_inv]

/-- Radial chain rule (gradient form): if `f : ℝ → ℝ` has derivative `f'` at
`r = ‖x‖` and `x ≠ 0`, then `x' ↦ f ‖x'‖` has gradient `(f' / ‖x‖) • x` at `x`. -/
lemma hasGradientAt_comp_norm {n : ℕ} {x : E n} (hx : x ≠ 0) {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' ‖x‖) :
    HasGradientAt (fun x' : E n => f ‖x'‖) ((f' / ‖x‖) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  apply (hasFDerivAt_comp_norm hx hf).congr_fderiv
  ext v
  simp [InnerProductSpace.toDual_apply_apply]

/-- Gradient of the fundamental solution away from the origin:
`∇ Φ_N (x) = x / (N ω_N ‖x‖^N)`. Covers both branches (for `N = 2`,
note `2 ω_2 = 2π`). -/
theorem gradient_fundamentalSolution {N : ℕ} (hN : 2 ≤ N) {x : E N} (hx : x ≠ 0) :
    HasGradientAt (fundamentalSolution N)
      ((1 / ((N : ℝ) * unitBallVolume N * ‖x‖ ^ N)) • x) x := by
  have hr : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hω : (0 : ℝ) < unitBallVolume N := unitBallVolume_pos N
  rcases eq_or_lt_of_le hN with h2 | h3
  · -- `N = 2`: logarithmic branch
    subst h2
    have hfun : fundamentalSolution 2 = fun x' : E 2 =>
        (1 / (2 * Real.pi)) * Real.log ‖x'‖ := funext fundamentalSolution_two
    rw [hfun]
    have hf : HasDerivAt (fun r : ℝ => (1 / (2 * Real.pi)) * Real.log r)
        ((1 / (2 * Real.pi)) * ‖x‖⁻¹) ‖x‖ :=
      (Real.hasDerivAt_log hr.ne').const_mul (1 / (2 * Real.pi))
    have h := hasGradientAt_comp_norm hx hf
    convert h using 2
    rw [unitBallVolume_two]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp
  · -- `N ≥ 3`: power branch
    have hN3 : 3 ≤ N := h3
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 3 := ⟨N - 3, by omega⟩
    have hfun : fundamentalSolution (m + 3) = fun x' : E (m + 3) =>
        -(1 / (((m + 3 : ℕ) : ℝ) * (((m + 3 : ℕ) : ℝ) - 2) * unitBallVolume (m + 3) *
          ‖x'‖ ^ (m + 3 - 2))) :=
      funext (fundamentalSolution_of_three_le (by omega))
    rw [hfun]
    set c : ℝ := ((m + 3 : ℕ) : ℝ) * (((m + 3 : ℕ) : ℝ) - 2) * unitBallVolume (m + 3) with hc
    have hcpos : 0 < c := by
      rw [hc]
      have h1 : (0 : ℝ) < ((m + 3 : ℕ) : ℝ) := by positivity
      have h2 : (0 : ℝ) < ((m + 3 : ℕ) : ℝ) - 2 := by push_cast; linarith
      exact mul_pos (mul_pos h1 h2) hω
    have hpow : HasDerivAt (fun r : ℝ => c * r ^ (m + 3 - 2))
        (c * (((m + 3 - 2 : ℕ) : ℝ) * ‖x‖ ^ (m + 3 - 2 - 1))) ‖x‖ :=
      (hasDerivAt_pow (m + 3 - 2) ‖x‖).const_mul c
    have hne : c * ‖x‖ ^ (m + 3 - 2) ≠ 0 := by positivity
    have hf : HasDerivAt
        (fun r : ℝ => -(1 / (c * r ^ (m + 3 - 2))))
        (-(-(c * (((m + 3 - 2 : ℕ) : ℝ) * ‖x‖ ^ (m + 3 - 2 - 1))) /
          (c * ‖x‖ ^ (m + 3 - 2)) ^ 2)) ‖x‖ := by
      simpa only [one_div] using (hpow.fun_inv hne).fun_neg
    have h := hasGradientAt_comp_norm hx hf
    convert h using 2
    have hm2 : m + 3 - 2 = m + 1 := by omega
    have hm1 : m + 3 - 2 - 1 = m := by omega
    rw [hc]
    simp only [hm2]
    have hm0 : ((1 : ℝ) + (m : ℝ)) ≠ 0 := by positivity
    push_cast
    field_simp
    ring_nf
    rw [show ‖x‖ ^ 3 * ‖x‖ ^ (m * 2) * (m : ℝ) * (1 + (m : ℝ))⁻¹ +
        ‖x‖ ^ 3 * ‖x‖ ^ (m * 2) * (1 + (m : ℝ))⁻¹ =
        ‖x‖ ^ 3 * ‖x‖ ^ (m * 2) * ((1 + (m : ℝ)) * (1 + (m : ℝ))⁻¹) by ring,
      mul_inv_cancel₀ hm0, mul_one]

/-- The fundamental solution is `C^∞` away from the origin. -/
theorem contDiffOn_fundamentalSolution {N : ℕ} (hN : 2 ≤ N) :
    ContDiffOn ℝ ∞ (fundamentalSolution N) {x : E N | x ≠ 0} := by
  intro x hx
  have hx' : x ≠ 0 := hx
  apply ContDiffAt.contDiffWithinAt
  have hnorm : ContDiffAt ℝ ∞ (fun x' : E N => ‖x'‖) x := contDiffAt_norm ℝ hx'
  rcases eq_or_lt_of_le hN with h2 | h3
  · -- `N = 2`: logarithmic branch
    have hfun : fundamentalSolution N = fun x' : E N =>
        (1 / (2 * Real.pi)) * Real.log ‖x'‖ := by
      subst h2; exact funext fundamentalSolution_two
    rw [hfun]
    have hlog : ContDiffAt ℝ ∞ (fun x' : E N => Real.log ‖x'‖) x :=
      (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr hx')).comp x hnorm
    exact hlog.const_smul (1 / (2 * Real.pi))
  · -- `N ≥ 3`: power branch
    have hfun : fundamentalSolution N = fun x' : E N =>
        -(1 / ((N : ℝ) * ((N : ℝ) - 2) * unitBallVolume N * ‖x'‖ ^ (N - 2))) :=
      funext (fundamentalSolution_of_three_le (by omega))
    rw [hfun]
    have hden : ContDiffAt ℝ ∞
        (fun x' : E N => (N : ℝ) * ((N : ℝ) - 2) * unitBallVolume N * ‖x'‖ ^ (N - 2)) x :=
      (hnorm.pow (N - 2)).const_smul ((N : ℝ) * ((N : ℝ) - 2) * unitBallVolume N)
    have hne : (N : ℝ) * ((N : ℝ) - 2) * unitBallVolume N * ‖x‖ ^ (N - 2) ≠ 0 := by
      have h1 : (0 : ℝ) < (N : ℝ) := by positivity
      have h2 : (0 : ℝ) < (N : ℝ) - 2 := by
        have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 3 ≤ N)
        linarith
      have h3 := unitBallVolume_pos N
      have h4 : (0 : ℝ) < ‖x‖ ^ (N - 2) := pow_pos (norm_pos_iff.mpr hx') _
      positivity
    have := (hden.inv hne).neg
    simp only [one_div]
    exact this

/-- Fréchet derivative of a radial vector field `y ↦ g(‖y‖) • y` at `x ≠ 0`:
`g(r) • id + (g'(r)/r) • (x ⊗ x)` (with `x ⊗ x = (innerSL x).smulRight x`). -/
lemma hasFDerivAt_radial_field {n : ℕ} {x : E n} (hx : x ≠ 0) {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' ‖x‖) :
    HasFDerivAt (fun y : E n => g ‖y‖ • y)
      (g ‖x‖ • ContinuousLinearMap.id ℝ (E n) +
        ((g' / ‖x‖) • innerSL ℝ x).smulRight x) x := by
  have hc : HasFDerivAt (fun y : E n => g ‖y‖) ((g' / ‖x‖) • innerSL ℝ x) x :=
    hasFDerivAt_comp_norm hx hg
  exact hc.smul (hasFDerivAt_id x)

/-- Trace of the radial-field derivative: `N g(r) + (g'(r)/r) ‖x‖²`. -/
lemma trace_radial_field_deriv {n : ℕ} (x : E n) (a b : ℝ) :
    LinearMap.trace ℝ (E n)
      ((a • ContinuousLinearMap.id ℝ (E n) + (b • innerSL ℝ x).smulRight x :
        E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) = a * n + b * ‖x‖ ^ 2 := by
  have hadd : ((a • ContinuousLinearMap.id ℝ (E n) + (b • innerSL ℝ x).smulRight x :
      E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) =
      (a • ContinuousLinearMap.id ℝ (E n) : E n →L[ℝ] E n) +
      ((b • innerSL ℝ x).smulRight x : E n →L[ℝ] E n) := rfl
  rw [hadd, map_add]
  congr 1
  · rw [show ((a • ContinuousLinearMap.id ℝ (E n) : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) =
        a • (ContinuousLinearMap.id ℝ (E n) : E n →ₗ[ℝ] E n) from rfl, map_smul]
    simp [LinearMap.trace_id, smul_eq_mul]
  · rw [show (((b • innerSL ℝ x).smulRight x : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) =
        LinearMap.smulRight (b • (innerSL ℝ x : E n →ₗ[ℝ] ℝ)) x from rfl,
      LinearMap.trace_smulRight]
    simp only [LinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe,
      coe_innerSL_apply]
    rw [real_inner_self_eq_norm_sq]

/-- Harmonicity away from the origin: `Δ Φ_N (x) = 0` for `x ≠ 0`,
where `Δ` is the `N`-dimensional `Heat.laplacian`. -/
theorem laplacian_fundamentalSolution_eq_zero {N : ℕ} (hN : 2 ≤ N) {x : E N} (hx : x ≠ 0) :
    laplacian (fundamentalSolution N) x = 0 := by
  classical
  have hr : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hω : (0 : ℝ) < unitBallVolume N := unitBallVolume_pos N
  set d : ℝ := (N : ℝ) * unitBallVolume N with hd
  have hdpos : 0 < d := by
    rw [hd]; have : (0 : ℝ) < (N : ℝ) := by positivity
    exact mul_pos this hω
  -- the radial coefficient of the gradient field
  set g : ℝ → ℝ := fun r => 1 / (d * r ^ N) with hg
  -- the gradient field itself
  have hgrad_eq : gradient (fundamentalSolution N) =ᶠ[𝓝 x]
      fun y : E N => g ‖y‖ • y := by
    filter_upwards [IsOpen.mem_nhds isOpen_ne hx] with y hy
    exact (gradient_fundamentalSolution hN hy).gradient
  -- derivative of the radial coefficient
  have hdenne : d * ‖x‖ ^ N ≠ 0 := by positivity
  have hgderiv : HasDerivAt g
      (-(d * ((N : ℝ) * ‖x‖ ^ (N - 1))) / (d * ‖x‖ ^ N) ^ 2) ‖x‖ := by
    rw [hg]
    simpa only [one_div] using ((hasDerivAt_pow N ‖x‖).const_mul d).fun_inv hdenne
  -- Fréchet derivative of the gradient field at x
  have hF := hasFDerivAt_radial_field hx hgderiv
  -- compute the laplacian as a trace
  unfold Heat.laplacian Heat.div_field
  rw [Filter.EventuallyEq.fderiv_eq hgrad_eq, hF.fderiv, trace_radial_field_deriv]
  -- arithmetic: N g(r) + (g'(r)/r) r² = 0
  have hNr : ‖x‖ ^ (N - 1) * ‖x‖ = ‖x‖ ^ N := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hg]
  field_simp
  rw [hNr]
  ring

/-- The case `N = 3` recovers the three-dimensional fundamental solution:
`Φ_3 (x) = -1 / (4π ‖x‖) = fundamental_sol_3d x` for `x ≠ 0`
(using `ω_3 = 4π/3`, so `3 · 1 · ω_3 = 4π`). -/
theorem fundamentalSolution_three_eq_fundamental_sol_3d {x : E 3} (hx : x ≠ 0) :
    fundamentalSolution 3 x = fundamental_sol_3d x := by
  rw [fundamentalSolution_of_three_le le_rfl x, unitBallVolume_three]
  unfold fundamental_sol_3d
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  norm_num
  rw [neg_div]
  congr 1
  field_simp

/- Planner strategy: two chain-rule layers through the affine map
`A y = c • (y - p)`, whose linear part is `c • id` (self-adjoint).

Layer 1 (gradient transport): show `gradient (u ∘ A) x = c • gradient u (A x)`
for ALL `x`.
* Differentiable case: `HasFDerivAt.comp` gives
  `fderiv ℝ (u ∘ A) x = (fderiv ℝ u (A x)).comp (c • id)`; transport through
  Riesz via `gradient = ⇑(toDual ℝ (E n)).symm ∘ fderiv ℝ u` (see the `hgrad`
  rewrites in `PDE/Basics/LaplacianBridge.lean`).
* Junk case: `A` is an affine homeomorphism (inverse `z ↦ c⁻¹ • z + p`, needs
  `hc : c ≠ 0`), so `DifferentiableAt ℝ (u ∘ A) x ↔ DifferentiableAt ℝ u (A x)`
  — differentiability transfers both ways. Both sides are then `0` via
  `fderiv_zero_of_not_differentiableAt` (verified in Mathlib).

Layer 2: the gradient field of the composite is `x ↦ c • ∇u (A x)`; the same
affine transfer applies to this field, and
`fderiv ℝ (fun x => c • ∇u (A x)) x = c • (fderiv ℝ (∇u) (A x)).comp (c • id)`,
whose trace picks up `c²` by linearity of the trace.

In-file structural precedent: `laplacian_comp_linearIsometryEquiv`
(`PDE/Basics/Laplace/CalculusBasic.lean:317`) does the same
two-layer transfer for a linear isometry (there without the `c²` factor);
here the isometry is replaced by `c • id` and the junk case must be handled
explicitly since the statement is unconditional (no `ContDiffAt` hypothesis). -/
/-- Differentiability transfer through the affine homeomorphism `y ↦ c • (y - p)`
(`c ≠ 0`): `f ∘ A` is differentiable at `x` iff `f` is differentiable at `A x`. -/
lemma differentiableAt_comp_smul_sub_iff {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E n → F) {c : ℝ} (hc : c ≠ 0) (p x : E n) :
    DifferentiableAt ℝ (fun y => f (c • (y - p))) x ↔
      DifferentiableAt ℝ f (c • (x - p)) := by
  constructor
  · intro h
    have hB : DifferentiableAt ℝ (fun z : E n => c⁻¹ • z + p) (c • (x - p)) :=
      (differentiableAt_id.const_smul c⁻¹).add_const p
    have hBx : c⁻¹ • (c • (x - p)) + p = x := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul, sub_add_cancel]
    have h2 : DifferentiableAt ℝ
        ((fun y => f (c • (y - p))) ∘ fun z : E n => c⁻¹ • z + p) (c • (x - p)) :=
      DifferentiableAt.comp _ (by simpa [hBx] using h) hB
    have heq : ((fun y => f (c • (y - p))) ∘ fun z : E n => c⁻¹ • z + p) = f := by
      funext z
      simp [Function.comp, add_sub_cancel_right, smul_smul, mul_inv_cancel₀ hc]
    rwa [heq] at h2
  · intro h
    exact h.comp x ((differentiableAt_id.sub_const p).const_smul c)

/-- Gradient transport through the affine map `A y = c • (y - p)` (linear part
`c • id`, self-adjoint): `∇(u ∘ A)(x) = c • ∇u(A x)` for EVERY `x` — in the
non-differentiable case both sides vanish because `A` is an affine homeomorphism. -/
lemma gradient_comp_smul_sub {n : ℕ} (u : E n → ℝ) {c : ℝ} (hc : c ≠ 0)
    (p x : E n) :
    gradient (fun y => u (c • (y - p))) x = c • gradient u (c • (x - p)) := by
  by_cases hu : DifferentiableAt ℝ u (c • (x - p))
  · -- differentiable case: chain rule + Riesz transport of the dual pairing
    have hA : HasFDerivAt (fun y : E n => c • (y - p))
        (c • ContinuousLinearMap.id ℝ (E n)) x :=
      ((hasFDerivAt_id x).sub_const p).const_smul c
    have hgrad := hu.hasGradientAt
    rw [hasGradientAt_iff_hasFDerivAt] at hgrad
    have hcomp := hgrad.comp x hA
    have H : HasGradientAt (fun y => u (c • (y - p)))
        (c • gradient u (c • (x - p))) x := by
      rw [hasGradientAt_iff_hasFDerivAt]
      apply hcomp.congr_fderiv
      ext v
      simp
    exact H.gradient
  · -- junk case: both sides are 0
    have h1 : ¬ DifferentiableAt ℝ (fun y => u (c • (y - p))) x := fun h =>
      hu ((differentiableAt_comp_smul_sub_iff u hc p x).mp h)
    unfold gradient
    rw [fderiv_zero_of_not_differentiableAt h1,
      fderiv_zero_of_not_differentiableAt hu]
    simp

/-- **Laplacian of a scaled translate** (`lem:fundsolnd-laplacian-comp-smul-sub`):
`Δ(y ↦ u(c • (y - p)))(x) = c² Δu(c • (x - p))`, unconditionally. -/
lemma laplacian_comp_smul_sub {n : ℕ} (u : E n → ℝ) {c : ℝ} (hc : c ≠ 0)
    (p x : E n) :
    laplacian (fun y => u (c • (y - p))) x = c^2 * laplacian u (c • (x - p)) := by
  unfold Heat.laplacian Heat.div_field
  -- Layer 1: the gradient field of the composite is `y ↦ c • ∇u(c • (y - p))`,
  -- unconditionally in y.
  have hgrad_eq : gradient (fun y => u (c • (y - p)))
      = fun y => c • gradient u (c • (y - p)) :=
    funext fun y => gradient_comp_smul_sub u hc p y
  rw [hgrad_eq]
  by_cases hg : DifferentiableAt ℝ (gradient u) (c • (x - p))
  · -- Layer 2: chain rule for the transported gradient field; the derivative is
    -- `c • (D(∇u)(Ax) ∘ (c • id)) = c² • D(∇u)(Ax)`, whose trace carries the `c²`.
    have hA : HasFDerivAt (fun y : E n => c • (y - p))
        (c • ContinuousLinearMap.id ℝ (E n)) x :=
      ((hasFDerivAt_id x).sub_const p).const_smul c
    have hcomp := hg.hasFDerivAt.comp x hA
    have hsmul : HasFDerivAt (fun y => c • gradient u (c • (y - p)))
        (c • ((fderiv ℝ (gradient u) (c • (x - p))).comp
          (c • ContinuousLinearMap.id ℝ (E n)))) x :=
      hcomp.const_smul c
    rw [hsmul.fderiv]
    have hc2 : (c • ((fderiv ℝ (gradient u) (c • (x - p))).comp
        (c • ContinuousLinearMap.id ℝ (E n))) : E n →L[ℝ] E n)
        = c ^ 2 • fderiv ℝ (gradient u) (c • (x - p)) := by
      ext v
      simp [smul_smul, pow_two]
    rw [hc2,
      show ((c ^ 2 • fderiv ℝ (gradient u) (c • (x - p)) : E n →L[ℝ] E n) :
        E n →ₗ[ℝ] E n)
        = c ^ 2 • ((fderiv ℝ (gradient u) (c • (x - p)) : E n →L[ℝ] E n) :
          E n →ₗ[ℝ] E n) from rfl,
      map_smul, smul_eq_mul]
  · -- junk case: the transported field is non-differentiable at x exactly because
    -- `∇u` is non-differentiable at `A x`; both traces vanish.
    have hnd : ¬ DifferentiableAt ℝ (fun y => c • gradient u (c • (y - p))) x := by
      intro hcontra
      apply hg
      have h1 : DifferentiableAt ℝ (fun y => gradient u (c • (y - p))) x := by
        have h2 : DifferentiableAt ℝ
            (fun y => c⁻¹ • (c • gradient u (c • (y - p)))) x :=
          hcontra.const_smul c⁻¹
        simpa [smul_smul, inv_mul_cancel₀ hc] using h2
      exact (differentiableAt_comp_smul_sub_iff (gradient u) hc p x).mp h1
    rw [fderiv_zero_of_not_differentiableAt hnd,
      fderiv_zero_of_not_differentiableAt hg]
    simp

/-- **Harmonicity of a scaled translate**
(`cor:fundsolnd-laplacian-comp-smul-sub-zero`): if `Δu(c • (x - p)) = 0` then
`Δ(y ↦ u(c • (y - p)))(x) = 0`. -/
/- Planner strategy: rewrite by `laplacian_comp_smul_sub`, then `mul_zero`. -/
lemma laplacian_comp_smul_sub_eq_zero {n : ℕ} (u : E n → ℝ) {c : ℝ} (hc : c ≠ 0)
    (p x : E n) (h : laplacian u (c • (x - p)) = 0) :
    laplacian (fun y => u (c • (y - p))) x = 0 := by
  rw [laplacian_comp_smul_sub u hc p x, h, mul_zero]

end Laplace
