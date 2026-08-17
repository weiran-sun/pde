import Mathlib
import PDE
import PDE.Basics.Wave.WaveIVP1D
import PDE.Basics.Wave.WaveIVP2D

/-!
# Undergraduate Problem 10: D'Alembert's Formula via the Method of Descent

Source: `pde_latex/problems/undergraduate/problem_10.tex` (Math 418, HW-4, Problem 2).

## Informal statement

> Use the method of descent to derive the solution to the 1D wave equation
> ```
>   u_tt - c² u_xx = 0,   x ∈ ℝ,
>   u(x, 0) = φ(x),  u_t(x, 0) = ψ(x),   x ∈ ℝ,
> ```
> by using the formula for the 2D wave equation shown in class: for fixed
> `x̄ = (x̄₁, x̄₂)`,
> ```
>   u(x̄, t̄) = (1/2πc²t̄) ∬_{B(x̄, ct̄)} ψ(x₁,x₂) √(1 + f_{x₁}² + f_{x₂}²) dx₁ dx₂
>            + ∂/∂t̄ ( (1/2πc²t̄) ∬_{B(x̄, ct̄)} φ(x₁,x₂) √(1 + f_{x₁}² + f_{x₂}²) dx₁ dx₂ ),
> ```
> where `f(x₁,x₂) = √((ct̄)² - (x₁-x̄₁)² - (x₂-x̄₂)²)`.
> You should recover the d'Alembert formula at the end.

## Semantic alignment

* The surface-integral form quoted in the problem is turned into the bulk-integral
  form over the solid disk by the problem's own first step
  `√(1 + f_{x₁}² + f_{x₂}²) = ct̄ / √((ct̄)² - |y - x̄|²)` (equation (2) of the
  source); the bulk form is exactly the library expression `Wave.poisson2D`
  (`PDE/Basics/Wave/WaveIVP2D.lean`, Choksi Theorem 4.2 — the "formula shown in
  class" in this project's canon; there the `t̄`-derivative of the `φ`-integral
  has already been carried out, producing the `∇φ·(y-x)` term).
* Per the project strategy, the 2D solution formula enters as an *explicit
  hypothesis* of the final corollary (`dAlembert_by_descent`): the descent
  argument itself never uses the (unproved) 2D existence theorem
  `Wave.IsSolutionWaveIVP2D.eq_poisson2D`.
* "Descend by taking data depending only on `x₁`" — the lift `lift g (y₁,y₂) = g y₁`
  (`def lift`); the descent computation is `poisson2D_lift_eq_dAlembert`:
  `poisson2D c (lift φ) (lift ψ) x t` equals the d'Alembert expression
  `Wave.dAlembert c φ ψ x₁ t` in the first coordinate.
* The source's inner-integral computation `∫_{-α}^{α} dy/√(α² - y²) = π` is
  `integral_one_div_sqrt_sq_sub_sq`; the reduction of the double integral over
  the disk to the iterated one is `integral_ball_lift` (Fubini); the collapse of
  the `φ`-half by the fundamental theorem of calculus (the source's
  `∂/∂t̄ ((1/2c)∫φ)` step, already differentiated in `poisson2D`) is
  `integral_phi_term`.
* "You should recover the d'Alembert formula" — `dAlembert_by_descent` concludes
  `u₂(x, t) = ½[φ(x₁+ct) + φ(x₁-ct)] + (1/2c)∫_{x₁-ct}^{x₁+ct} ψ(s) ds`, the
  d'Alembert formula in the first coordinate.
-/

open Real MeasureTheory intervalIntegral InnerProductSpace
open scoped RealInnerProductSpace

namespace Problems.Undergraduate.Problem10

/-- The plane `ℝ²` as a Euclidean space. -/
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **Lifted one-dimensional data.** The lift of `g : ℝ → ℝ` to the plane,
`g̃(y₁, y₂) = g(y₁)` — the data "depending only on the first coordinate" used in
the method of descent. -/
def lift (g : ℝ → ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun y => g (y 0)

/-- **The arcsine integral**: `∫_{-α}^{α} dy / √(α² - y²) = π` for `α > 0` —
the universal constant produced by the inner integral of the descent
computation. -/
theorem integral_one_div_sqrt_sq_sub_sq {α : ℝ} (hα : 0 < α) :
    ∫ y in (-α)..α, 1 / Real.sqrt (α ^ 2 - y ^ 2) = π := by
  have hab : (-α) ≤ α := by linarith
  -- the primitive is `y ↦ arcsin (y / α)`
  have hderiv : ∀ y ∈ Set.Ioo (-α) α,
      HasDerivAt (fun y => Real.arcsin (y / α))
        (1 / Real.sqrt (α ^ 2 - y ^ 2)) y := by
    intro y hy
    have hy1 : y / α ≠ -1 := by
      intro h
      have hy' : y = -α := by
        field_simp at h
        linarith
      linarith [hy.1]
    have hy2 : y / α ≠ 1 := by
      intro h
      have hy' : y = α := by
        field_simp at h
        exact h
      linarith [hy.2]
    have harc := Real.hasDerivAt_arcsin hy1 hy2
    have hdiv : HasDerivAt (fun y : ℝ => y / α) (1 / α) y := by
      simpa using (hasDerivAt_id y).div_const α
    have h := harc.comp y hdiv
    have hsq : (0 : ℝ) < α ^ 2 - y ^ 2 := by nlinarith [hy.1, hy.2]
    have hs : Real.sqrt (α ^ 2 - y ^ 2) ≠ 0 := by positivity
    have heq : 1 / Real.sqrt (1 - (y / α) ^ 2) * (1 / α)
        = 1 / Real.sqrt (α ^ 2 - y ^ 2) := by
      have h1 : 1 - (y / α) ^ 2 = (α ^ 2 - y ^ 2) / α ^ 2 := by
        field_simp
      rw [h1, Real.sqrt_div hsq.le, Real.sqrt_sq hα.le]
      field_simp
    exact heq ▸ h
  have hcont : ContinuousOn (fun y => Real.arcsin (y / α))
      (Set.Icc (-α) α) :=
    (Real.continuous_arcsin.comp (continuous_id.div_const α)).continuousOn
  have hnonneg : ∀ y ∈ Set.Ioo (-α) α,
      0 ≤ 1 / Real.sqrt (α ^ 2 - y ^ 2) := fun y _ => by positivity
  have hint : IntervalIntegrable (fun y => 1 / Real.sqrt (α ^ 2 - y ^ 2))
      volume (-α) α := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    · rwa [Set.uIcc_of_le hab]
    · simpa [min_eq_left hab, max_eq_right hab] using hderiv
    · simp only [min_eq_left hab, max_eq_right hab]
      exact hnonneg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint]
  rw [div_self hα.ne', neg_div, div_self hα.ne', Real.arcsin_one,
    Real.arcsin_neg_one]
  ring

/-- **Gradient of a lifted function.** If `g ∈ C¹(ℝ)`, the gradient of the lift
`g̃(y₁,y₂) = g(y₁)` is `g'(y₁) e₁`. -/
theorem gradient_lift {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (y : EuclideanSpace ℝ (Fin 2)) :
    gradient (lift g) y =
      EuclideanSpace.single (0 : Fin 2) (deriv g (y 0)) := by
  have hg' : HasDerivAt g (deriv g (y 0)) (y 0) :=
    (hg.differentiable one_ne_zero (y 0)).hasDerivAt
  have hproj : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 0)
      (EuclideanSpace.proj (0 : Fin 2) :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) y := by
    exact (EuclideanSpace.proj (0 : Fin 2)
      (𝕜 := ℝ)).hasFDerivAt
  have hF : HasFDerivAt (lift g)
      (deriv g (y 0) • (EuclideanSpace.proj (0 : Fin 2) :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) y :=
    hg'.comp_hasFDerivAt y hproj
  have hgrad : HasGradientAt (lift g)
      (EuclideanSpace.single (0 : Fin 2) (deriv g (y 0))) y := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have heq : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2)))
        (EuclideanSpace.single (0 : Fin 2) (deriv g (y 0))) =
        deriv g (y 0) • (EuclideanSpace.proj (0 : Fin 2) :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) := by
      ext w
      simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
    rw [heq]
    exact hF
  exact hgrad.gradient

/-- Pairing the gradient of a lifted function with a displacement picks out the
first component: `⟪∇g̃(y), y - x⟫ = g'(y₁)(y₁ - x₁)`. -/
theorem inner_gradient_lift_sub {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪gradient (lift g) y, y - x⟫ = deriv g (y 0) * (y 0 - x 0) := by
  rw [gradient_lift hg y, EuclideanSpace.inner_single_left]
  simp

/-- Step (i) of the disk Fubini: translation invariance of the Lebesgue measure
reduces the disk integral to the centered case `x = 0`, shifting the argument
of `g` by `x₁`. -/
private lemma integral_ball_lift_translate {r : ℝ}
    (x : EuclideanSpace ℝ (Fin 2)) (g : ℝ → ℝ) :
    ∫ y in Metric.ball x r, g (y 0) / Real.sqrt (r ^ 2 - ‖y - x‖ ^ 2) =
      ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r,
        g (y 0 + x 0) / Real.sqrt (r ^ 2 - ‖y‖ ^ 2) := by
  have hmp := MeasureTheory.measurePreserving_add_right
    (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))) x
  have hemb : MeasurableEmbedding
      (fun y : EuclideanSpace ℝ (Fin 2) => y + x) :=
    (MeasurableEquiv.addRight x).measurableEmbedding
  have hpre : (fun y : EuclideanSpace ℝ (Fin 2) => y + x) ⁻¹'
      Metric.ball x r = Metric.ball 0 r := by
    ext y; simp [Metric.mem_ball, dist_eq_norm]
  rw [← hpre, ← hmp.setIntegral_preimage_emb hemb]
  simp only [add_sub_cancel_right, WithLp.ofLp_add, Pi.add_apply]

/-- Step (ii) of the disk Fubini: transport the centered disk integral to the
product space `ℝ × ℝ` via the measure-preserving identification
`EuclideanSpace ℝ (Fin 2) ≃ ℝ × ℝ`
(`EuclideanSpace.volume_preserving_measurableEquiv` composed with
`MeasureTheory.volume_preserving_piFinTwoEquiv`). -/
private lemma integral_ball_zero_eq_prod {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r,
        g (y 0) / Real.sqrt (r ^ 2 - ‖y‖ ^ 2) =
      ∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2},
        g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2)) := by
  have hmp : MeasureTheory.MeasurePreserving
      (fun p : ℝ × ℝ => WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm p) :
        ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) volume volume :=
    (PiLp.volume_preserving_toLp (Fin 2)).comp
      (MeasureTheory.volume_preserving_finTwoArrow ℝ).symm
  have hemb : MeasurableEmbedding
      (fun p : ℝ × ℝ => WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm p) :
        ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) :=
    (MeasurableEquiv.finTwoArrow.symm.trans
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))).measurableEmbedding
  have hnorm : ∀ p : ℝ × ℝ,
      ‖(WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm p) :
        EuclideanSpace ℝ (Fin 2))‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    intro p
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_two, MeasurableEquiv.finTwoArrow, sq_abs]
  have happ : ∀ p : ℝ × ℝ,
      (WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm p) :
        EuclideanSpace ℝ (Fin 2)) 0 = p.1 := by
    intro p; simp [MeasurableEquiv.finTwoArrow]
  have hpre : (fun p : ℝ × ℝ =>
        WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm p) :
        ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) ⁻¹' Metric.ball 0 r =
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2} := by
    ext p
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right,
      Set.mem_setOf_eq]
    rw [← hnorm p, ← pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero]
  rw [← hpre, ← hmp.setIntegral_preimage_emb hemb]
  refine MeasureTheory.setIntegral_congr_fun (hpre ▸ (by measurability :
      MeasurableSet {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2})) fun p _ => ?_
  rw [happ p, hnorm p]

/-- The arcsine integrand is interval-integrable: it is the nonnegative
derivative of `y ↦ arcsin (y / α)` on the interior (the integrability argument
of `integral_one_div_sqrt_sq_sub_sq`). -/
private lemma intervalIntegrable_one_div_sqrt_sq_sub_sq {α : ℝ} (hα : 0 < α) :
    IntervalIntegrable (fun y => 1 / Real.sqrt (α ^ 2 - y ^ 2))
      volume (-α) α := by
  have hab : (-α) ≤ α := by linarith
  have hderiv : ∀ y ∈ Set.Ioo (-α) α,
      HasDerivAt (fun y => Real.arcsin (y / α))
        (1 / Real.sqrt (α ^ 2 - y ^ 2)) y := by
    intro y hy
    have hy1 : y / α ≠ -1 := by
      intro h
      have hy' : y = -α := by
        field_simp at h
        linarith
      linarith [hy.1]
    have hy2 : y / α ≠ 1 := by
      intro h
      have hy' : y = α := by
        field_simp at h
        exact h
      linarith [hy.2]
    have harc := Real.hasDerivAt_arcsin hy1 hy2
    have hdiv : HasDerivAt (fun y : ℝ => y / α) (1 / α) y := by
      simpa using (hasDerivAt_id y).div_const α
    have h := harc.comp y hdiv
    have hsq : (0 : ℝ) < α ^ 2 - y ^ 2 := by nlinarith [hy.1, hy.2]
    have heq : 1 / Real.sqrt (1 - (y / α) ^ 2) * (1 / α)
        = 1 / Real.sqrt (α ^ 2 - y ^ 2) := by
      have h1 : 1 - (y / α) ^ 2 = (α ^ 2 - y ^ 2) / α ^ 2 := by
        field_simp
      rw [h1, Real.sqrt_div hsq.le, Real.sqrt_sq hα.le]
      field_simp
    exact heq ▸ h
  have hcont : ContinuousOn (fun y => Real.arcsin (y / α))
      (Set.Icc (-α) α) :=
    (Real.continuous_arcsin.comp (continuous_id.div_const α)).continuousOn
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
  · rwa [Set.uIcc_of_le hab]
  · simpa [min_eq_left hab, max_eq_right hab] using hderiv
  · simp only [min_eq_left hab, max_eq_right hab]
    exact fun y _ => by positivity

/-- Step (iv) of the disk Fubini: for `y₁² < r²` the inner integral is the
universal constant `π`, by `integral_one_div_sqrt_sq_sub_sq` with
`α = √(r² - y₁²)`. -/
private lemma inner_integral_eq_pi {r y₁ : ℝ} (h : y₁ ^ 2 < r ^ 2) :
    ∫ y₂ in (-Real.sqrt (r ^ 2 - y₁ ^ 2))..Real.sqrt (r ^ 2 - y₁ ^ 2),
        1 / Real.sqrt (r ^ 2 - y₁ ^ 2 - y₂ ^ 2) = π := by
  have hα : (0:ℝ) < Real.sqrt (r ^ 2 - y₁ ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hαsq : Real.sqrt (r ^ 2 - y₁ ^ 2) ^ 2 = r ^ 2 - y₁ ^ 2 :=
    Real.sq_sqrt (by linarith)
  simpa [hαsq, sub_sub] using integral_one_div_sqrt_sq_sub_sq hα

/-- Integrability of the descent integrand over the open disk in `ℝ × ℝ` — the
Fubini hypothesis. Established by the iterated computation with `|g|` in place
of `g` (blueprint proof of `lem:problem10-disk-fubini`). -/
private lemma integrableOn_disk_descent {r : ℝ} (hr : 0 < r)
    {g : ℝ → ℝ} (hg : Continuous g) :
    IntegrableOn
      (fun p : ℝ × ℝ => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2)))
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2} := by
  have hD : MeasurableSet {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2} := by
    have hc : Continuous fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 := by fun_prop
    exact (isOpen_lt hc continuous_const).measurableSet
  rw [← MeasureTheory.integrable_indicator_iff hD,
    MeasureTheory.Measure.volume_eq_prod]
  have hmeas : Measurable
      (fun p : ℝ × ℝ => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2))) := by
    have h1 : Measurable fun p : ℝ × ℝ => g p.1 :=
      hg.measurable.comp measurable_fst
    have h2 : Measurable fun p : ℝ × ℝ =>
        Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2)) := by fun_prop
    exact h1.div h2
  -- the slice of the disk at abscissa `x` is `Ioo (-β) β`, `β = √(r² - x²)`
  have hind : ∀ x ∈ Set.Ioo (-r) r, ∀ y : ℝ,
      Set.indicator {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
        (fun p => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2))) (x, y) =
      Set.indicator
        (Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2)) (Real.sqrt (r ^ 2 - x ^ 2)))
        (fun y => g x * (1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2))) y := by
    intro x hx y
    have hx2 : x ^ 2 < r ^ 2 := by
      have h1 := hx.1; have h2 := hx.2; nlinarith
    have hβpos : 0 < Real.sqrt (r ^ 2 - x ^ 2) := Real.sqrt_pos.2 (by linarith)
    have hβsq : Real.sqrt (r ^ 2 - x ^ 2) ^ 2 = r ^ 2 - x ^ 2 :=
      Real.sq_sqrt (by linarith)
    have hmem : (x, y) ∈ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2} ↔
        y ∈ Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2))
          (Real.sqrt (r ^ 2 - x ^ 2)) := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioo]
      constructor
      · intro h
        constructor
        · nlinarith [sq_nonneg (y + Real.sqrt (r ^ 2 - x ^ 2))]
        · nlinarith [sq_nonneg (y - Real.sqrt (r ^ 2 - x ^ 2))]
      · rintro ⟨h1, h2⟩
        nlinarith
    by_cases hy : y ∈ Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2))
        (Real.sqrt (r ^ 2 - x ^ 2))
    · rw [Set.indicator_of_mem (hmem.2 hy), Set.indicator_of_mem hy]
      rw [mul_one_div]
      congr 2
      ring
    · rw [Set.indicator_of_notMem (fun h => hy (hmem.1 h)),
        Set.indicator_of_notMem hy]
  have hzero : ∀ x : ℝ, x ∉ Set.Ioo (-r) r → ∀ y : ℝ,
      Set.indicator {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
        (fun p => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2))) (x, y)
          = 0 := by
    intro x hx y
    have hx' : x ≤ -r ∨ r ≤ x := by
      by_contra h
      push Not at h
      exact hx ⟨h.1, h.2⟩
    have hx2 : r ^ 2 ≤ x ^ 2 := by
      rcases hx' with h | h
      · nlinarith
      · nlinarith
    apply Set.indicator_of_notMem
    simp only [Set.mem_setOf_eq, not_lt]
    nlinarith [sq_nonneg y]
  -- integrability of each slice
  have hsliceInt : ∀ x ∈ Set.Ioo (-r) r,
      MeasureTheory.Integrable (fun y =>
        g x * (1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2)))
        (volume.restrict (Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2))
          (Real.sqrt (r ^ 2 - x ^ 2)))) := by
    intro x hx
    have hx2 : x ^ 2 < r ^ 2 := by
      have h1 := hx.1; have h2 := hx.2; nlinarith
    have hβpos : 0 < Real.sqrt (r ^ 2 - x ^ 2) := Real.sqrt_pos.2 (by linarith)
    have hβsq : Real.sqrt (r ^ 2 - x ^ 2) ^ 2 = r ^ 2 - x ^ 2 :=
      Real.sq_sqrt (by nlinarith)
    have h1 : IntegrableOn (fun y => 1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2))
        (Set.Ioc (-Real.sqrt (r ^ 2 - x ^ 2)) (Real.sqrt (r ^ 2 - x ^ 2)))
        volume := by
      have := intervalIntegrable_one_div_sqrt_sq_sub_sq hβpos
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
        (by linarith : -Real.sqrt (r ^ 2 - x ^ 2) ≤ Real.sqrt (r ^ 2 - x ^ 2))]
        at this
      simpa [hβsq] using this
    exact ((h1.mono_set Set.Ioo_subset_Ioc_self).const_mul (g x))
  refine (MeasureTheory.integrable_prod_iff
    ((hmeas.indicator hD).aestronglyMeasurable)).2 ⟨?_, ?_⟩
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ Set.Ioo (-r) r
    · rw [show (fun y => Set.indicator {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
          (fun p => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2))) (x, y)) =
          Set.indicator
            (Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2)) (Real.sqrt (r ^ 2 - x ^ 2)))
            (fun y => g x * (1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2)))
        from funext (hind x hx)]
      exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).2
        (hsliceInt x hx)
    · simp only [hzero x hx]
      exact MeasureTheory.integrable_zero _ _ _
  · -- the norm-integral function is the indicator of `|g| · π` on `(-r, r)`
    have hnormeq : (fun x => ∫ y, ‖Set.indicator
        {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
        (fun p => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2))) (x, y)‖) =
        Set.indicator (Set.Ioo (-r) r) (fun x => |g x| * π) := by
      funext x
      by_cases hx : x ∈ Set.Ioo (-r) r
      · rw [Set.indicator_of_mem hx]
        have hx2 : x ^ 2 < r ^ 2 := by
          have h1 := hx.1; have h2 := hx.2; nlinarith
        have hβpos : 0 < Real.sqrt (r ^ 2 - x ^ 2) :=
          Real.sqrt_pos.2 (by linarith)
        calc (∫ y, ‖Set.indicator {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
              (fun p => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2)))
              (x, y)‖)
            = ∫ y, Set.indicator
                (Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2))
                  (Real.sqrt (r ^ 2 - x ^ 2)))
                (fun y => |g x| * (1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2)))
                y := by
              refine MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall fun y => ?_)
              beta_reduce
              rw [hind x hx y]
              by_cases hy : y ∈ Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2))
                  (Real.sqrt (r ^ 2 - x ^ 2))
              · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy,
                  Real.norm_eq_abs, abs_mul, abs_of_nonneg
                  (by positivity :
                    (0:ℝ) ≤ 1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2))]
              · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy,
                  norm_zero]
          _ = ∫ y in Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2))
                (Real.sqrt (r ^ 2 - x ^ 2)),
                |g x| * (1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2)) :=
              MeasureTheory.integral_indicator measurableSet_Ioo
          _ = ∫ y in (-Real.sqrt (r ^ 2 - x ^ 2))..(Real.sqrt (r ^ 2 - x ^ 2)),
                |g x| * (1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2)) := by
              rw [intervalIntegral.integral_of_le (by linarith),
                MeasureTheory.integral_Ioc_eq_integral_Ioo]
          _ = |g x| * ∫ y in
                (-Real.sqrt (r ^ 2 - x ^ 2))..(Real.sqrt (r ^ 2 - x ^ 2)),
                1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2) :=
              intervalIntegral.integral_const_mul _ _
          _ = |g x| * π := by rw [inner_integral_eq_pi hx2]
      · rw [Set.indicator_of_notMem hx]
        simp only [hzero x hx, norm_zero, MeasureTheory.integral_zero]
    rw [hnormeq, MeasureTheory.integrable_indicator_iff measurableSet_Ioo]
    exact ((hg.abs.mul continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Set.Ioo_subset_Icc_self

/-- Step (iii) of the disk Fubini: the disk is the region between the graphs
`y₂ = ±√(r² - y₁²)` over `y₁ ∈ (-r, r)`, so by Fubini
(`MeasureTheory.setIntegral_prod` with `integrableOn_disk_descent`) the double
integral is the iterated one. -/
private lemma integral_disk_eq_iterated {r : ℝ} (hr : 0 < r)
    {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2},
        g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2)) =
      ∫ y₁ in (-r)..r, g y₁ *
        ∫ y₂ in (-Real.sqrt (r ^ 2 - y₁ ^ 2))..Real.sqrt (r ^ 2 - y₁ ^ 2),
          1 / Real.sqrt (r ^ 2 - y₁ ^ 2 - y₂ ^ 2) := by
  have hD : MeasurableSet {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2} := by
    have hc : Continuous fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 := by fun_prop
    exact (isOpen_lt hc continuous_const).measurableSet
  have hint := integrableOn_disk_descent hr hg
  have hint' : MeasureTheory.Integrable
      (Set.indicator {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
        (fun p => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2)))) volume :=
    (MeasureTheory.integrable_indicator_iff hD).2 hint
  rw [MeasureTheory.Measure.volume_eq_prod] at hint'
  -- each slice of the indicator integrates to the inner arcsine integral
  have hslice : ∀ x : ℝ,
      (∫ y, Set.indicator {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
        (fun p => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2))) (x, y)) =
      Set.indicator (Set.Ioo (-r) r)
        (fun x => g x *
          ∫ y in (-Real.sqrt (r ^ 2 - x ^ 2))..(Real.sqrt (r ^ 2 - x ^ 2)),
            1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioo (-r) r
    · rw [Set.indicator_of_mem hx]
      have hx2 : x ^ 2 < r ^ 2 := by
        have h1 := hx.1; have h2 := hx.2; nlinarith
      have hβpos : 0 < Real.sqrt (r ^ 2 - x ^ 2) := Real.sqrt_pos.2 (by linarith)
      have hβsq : Real.sqrt (r ^ 2 - x ^ 2) ^ 2 = r ^ 2 - x ^ 2 :=
        Real.sq_sqrt (by linarith)
      -- the slice of the disk at abscissa `x` is the open interval `(-β, β)`
      have hind : ∀ y : ℝ,
          Set.indicator {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
            (fun p => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2))) (x, y) =
          Set.indicator
            (Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2)) (Real.sqrt (r ^ 2 - x ^ 2)))
            (fun y => g x * (1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2))) y := by
        intro y
        have hmem : (x, y) ∈ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2} ↔
            y ∈ Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2))
              (Real.sqrt (r ^ 2 - x ^ 2)) := by
          simp only [Set.mem_setOf_eq, Set.mem_Ioo]
          constructor
          · intro h
            constructor
            · nlinarith [sq_nonneg (y + Real.sqrt (r ^ 2 - x ^ 2))]
            · nlinarith [sq_nonneg (y - Real.sqrt (r ^ 2 - x ^ 2))]
          · rintro ⟨h1, h2⟩
            nlinarith
        by_cases hy : y ∈ Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2))
            (Real.sqrt (r ^ 2 - x ^ 2))
        · rw [Set.indicator_of_mem (hmem.2 hy), Set.indicator_of_mem hy]
          rw [mul_one_div]
          congr 2
          ring
        · rw [Set.indicator_of_notMem (fun h => hy (hmem.1 h)),
            Set.indicator_of_notMem hy]
      calc (∫ y, Set.indicator {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
            (fun p => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2))) (x, y))
          = ∫ y, Set.indicator
              (Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2)) (Real.sqrt (r ^ 2 - x ^ 2)))
              (fun y => g x * (1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2))) y :=
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hind)
        _ = ∫ y in Set.Ioo (-Real.sqrt (r ^ 2 - x ^ 2))
              (Real.sqrt (r ^ 2 - x ^ 2)),
              g x * (1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2)) :=
            MeasureTheory.integral_indicator measurableSet_Ioo
        _ = ∫ y in (-Real.sqrt (r ^ 2 - x ^ 2))..(Real.sqrt (r ^ 2 - x ^ 2)),
              g x * (1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2)) := by
            rw [intervalIntegral.integral_of_le (by linarith),
              MeasureTheory.integral_Ioc_eq_integral_Ioo]
        _ = g x * ∫ y in (-Real.sqrt (r ^ 2 - x ^ 2))..(Real.sqrt (r ^ 2 - x ^ 2)),
              1 / Real.sqrt (r ^ 2 - x ^ 2 - y ^ 2) :=
            intervalIntegral.integral_const_mul _ _
    · rw [Set.indicator_of_notMem hx]
      have hx' : x ≤ -r ∨ r ≤ x := by
        by_contra h
        push Not at h
        exact hx ⟨h.1, h.2⟩
      have hx2 : r ^ 2 ≤ x ^ 2 := by
        rcases hx' with h | h
        · nlinarith
        · nlinarith
      have hz : ∀ y : ℝ, Set.indicator {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}
          (fun p => g p.1 / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2))) (x, y)
            = 0 := by
        intro y
        apply Set.indicator_of_notMem
        simp only [Set.mem_setOf_eq, not_lt]
        nlinarith [sq_nonneg y]
      simp only [hz, MeasureTheory.integral_zero]
  rw [← MeasureTheory.integral_indicator hD, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.integral_prod _ hint']
  simp_rw [hslice]
  rw [MeasureTheory.integral_indicator measurableSet_Ioo,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : (-r) ≤ r)]

/-- Step (v) of the disk Fubini: substituting the constant inner integral `π`
(valid a.e. on `(-r, r)`, by `inner_integral_eq_pi`) and pulling it out of the
outer integral. -/
private lemma intervalIntegral_mul_inner_eq_pi_mul {r : ℝ} (hr : 0 < r)
    (g : ℝ → ℝ) :
    ∫ y₁ in (-r)..r, g y₁ *
        ∫ y₂ in (-Real.sqrt (r ^ 2 - y₁ ^ 2))..Real.sqrt (r ^ 2 - y₁ ^ 2),
          1 / Real.sqrt (r ^ 2 - y₁ ^ 2 - y₂ ^ 2) =
      π * ∫ y₁ in (-r)..r, g y₁ := by
  have hae : ∀ᵐ y₁ ∂(volume : MeasureTheory.Measure ℝ),
      y₁ ∈ Set.uIoc (-r) r →
      (g y₁ * ∫ y₂ in (-Real.sqrt (r ^ 2 - y₁ ^ 2))..Real.sqrt (r ^ 2 - y₁ ^ 2),
        1 / Real.sqrt (r ^ 2 - y₁ ^ 2 - y₂ ^ 2)) = g y₁ * π := by
    filter_upwards [Set.Countable.ae_notMem (Set.countable_singleton r) volume]
      with y₁ hy₁ hmem
    rw [Set.uIoc_of_le (by linarith : -r ≤ r)] at hmem
    have hne : y₁ ≠ r := fun h => hy₁ (h ▸ Set.mem_singleton r)
    rw [inner_integral_eq_pi
      (by nlinarith [hmem.1, lt_of_le_of_ne hmem.2 hne] : y₁ ^ 2 < r ^ 2)]
  rw [intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_mul_const]
  ring

/-- Step (vi) of the disk Fubini: undoing the translation on the 1D side —
`∫_{-r}^{r} g(s + x₁) ds = ∫_{x₁-r}^{x₁+r} g(s) ds`
(`intervalIntegral.integral_comp_add_right`). -/
private lemma intervalIntegral_comp_add {r : ℝ} (x₁ : ℝ) (g : ℝ → ℝ) :
    ∫ s in (-r)..r, g (s + x₁) = ∫ s in (x₁ - r)..(x₁ + r), g s := by
  rw [intervalIntegral.integral_comp_add_right g x₁]; congr 1 <;> ring

/-- **Fubini over the disk with the descent weight.** For `r > 0` and continuous
`g : ℝ → ℝ`,

  `∬_{B(x,r)} g(y₁) / √(r² - |y - x|²) dy = π ∫_{x₁-r}^{x₁+r} g(s) ds` :

the disk is the region between the graphs `y₂ = ±√(r² - (y₁-x₁)²)`, and for each
`y₁` the inner integral is the universal constant `π` of
`integral_one_div_sqrt_sq_sub_sq`. -/
theorem integral_ball_lift {r : ℝ} (hr : 0 < r) (x : EuclideanSpace ℝ (Fin 2))
    {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ y in Metric.ball x r, g (y 0) / Real.sqrt (r ^ 2 - ‖y - x‖ ^ 2) =
      π * ∫ s in (x 0 - r)..(x 0 + r), g s := by
  have hg' : Continuous fun s => g (s + x 0) :=
    hg.comp (continuous_id.add continuous_const)
  calc ∫ y in Metric.ball x r, g (y 0) / Real.sqrt (r ^ 2 - ‖y - x‖ ^ 2)
      = ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r,
          g (y 0 + x 0) / Real.sqrt (r ^ 2 - ‖y‖ ^ 2) :=
        integral_ball_lift_translate x g
    _ = ∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2},
          g (p.1 + x 0) / Real.sqrt (r ^ 2 - (p.1 ^ 2 + p.2 ^ 2)) :=
        integral_ball_zero_eq_prod hr (fun s => g (s + x 0))
    _ = ∫ y₁ in (-r)..r, g (y₁ + x 0) *
          ∫ y₂ in (-Real.sqrt (r ^ 2 - y₁ ^ 2))..Real.sqrt (r ^ 2 - y₁ ^ 2),
            1 / Real.sqrt (r ^ 2 - y₁ ^ 2 - y₂ ^ 2) :=
        integral_disk_eq_iterated hr hg'
    _ = π * ∫ y₁ in (-r)..r, g (y₁ + x 0) :=
        intervalIntegral_mul_inner_eq_pi_mul hr (fun s => g (s + x 0))
    _ = π * ∫ s in (x 0 - r)..(x 0 + r), g s := by
        rw [intervalIntegral_comp_add (x 0) g]

/-- **Collapse of the displacement half.** For `φ ∈ C¹(ℝ)`, the integrand
`φ(y) + φ'(y)(y - a)` is the derivative of `y ↦ φ(y)(y - a)`, so by the
fundamental theorem of calculus

  `∫_{a-r}^{a+r} (φ(y) + φ'(y)(y - a)) dy = r (φ(a+r) + φ(a-r))`. -/
theorem integral_phi_term {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (a r : ℝ) :
    ∫ y in (a - r)..(a + r), (φ y + deriv φ y * (y - a)) =
      r * (φ (a + r) + φ (a - r)) := by
  have hderiv : ∀ y ∈ Set.uIcc (a - r) (a + r),
      HasDerivAt (fun y => φ y * (y - a)) (φ y + deriv φ y * (y - a)) y := by
    intro y _
    have h1 : HasDerivAt φ (deriv φ y) y :=
      (hφ.differentiable one_ne_zero y).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => y - a) 1 y := (hasDerivAt_id y).sub_const a
    have h3 := h1.mul h2
    simp only [mul_one] at h3
    exact (add_comm (deriv φ y * (y - a)) (φ y)) ▸ h3
  have hcont : Continuous fun y => φ y + deriv φ y * (y - a) := by
    have hd : Continuous (deriv φ) := (hφ.iterate_deriv' 0 1).continuous
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable _ _)]
  ring

/-- **Descent: the 2D Poisson expression on lifted data.** For `c > 0`,
`φ ∈ C²(ℝ)`, `ψ ∈ C¹(ℝ)`, and `t > 0`, evaluating the 2D solution expression
`Wave.poisson2D` on the lifted data `φ̃, ψ̃` at any `x ∈ ℝ²` yields the
d'Alembert expression in the first coordinate:

  `poisson2D c φ̃ ψ̃ x t = ½[φ(x₁+ct) + φ(x₁-ct)] + (1/2c)∫_{x₁-ct}^{x₁+ct} ψ`. -/
theorem poisson2D_lift_eq_dAlembert {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 1 ψ)
    (x : EuclideanSpace ℝ (Fin 2)) {t : ℝ} (ht : 0 < t) :
    Wave.poisson2D c (lift φ) (lift ψ) x t = Wave.dAlembert c φ ψ (x 0) t := by
  have hct : 0 < c * t := mul_pos hc ht
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le one_le_two
  have hderivφ : Continuous (deriv φ) := hφ.continuous_deriv one_le_two
  have hgcont : Continuous fun s => φ s + deriv φ s * (s - x 0) + t * ψ s := by
    fun_prop
  have hint1 : IntervalIntegrable (fun s => φ s + deriv φ s * (s - x 0))
      volume (x 0 - c * t) (x 0 + c * t) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hint2 : IntervalIntegrable (fun s => t * ψ s)
      volume (x 0 - c * t) (x 0 + c * t) := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc Wave.poisson2D c (lift φ) (lift ψ) x t
      = (2 / (4 * π * c * t)) * ∫ y in Metric.ball x (c * t),
          (fun s => φ s + deriv φ s * (s - x 0) + t * ψ s) (y 0) /
            Real.sqrt ((c * t) ^ 2 - ‖y - x‖ ^ 2) := by
        rw [Wave.poisson2D]
        congr 1
        refine MeasureTheory.setIntegral_congr_fun measurableSet_ball
          fun y _ => ?_
        rw [inner_gradient_lift_sub hφ1 x y, mul_pow]
        simp only [lift]
    _ = (2 / (4 * π * c * t)) * (π * ∫ s in (x 0 - c * t)..(x 0 + c * t),
          (φ s + deriv φ s * (s - x 0) + t * ψ s)) := by
        rw [integral_ball_lift hct x hgcont]
    _ = Wave.dAlembert c φ ψ (x 0) t := by
        rw [Wave.dAlembert, intervalIntegral.integral_add hint1 hint2,
          integral_phi_term hφ1 (x 0) (c * t),
          intervalIntegral.integral_const_mul]
        have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
        field_simp
        ring

/-- **D'Alembert's formula by the method of descent.** Let `c > 0`,
`φ ∈ C²(ℝ)`, `ψ ∈ C¹(ℝ)`, and suppose `u₂ : ℝ² × ℝ → ℝ` satisfies the 2D
solution formula for the lifted data — "the formula shown in class", taken as an
explicit hypothesis. Then `u₂` is given by the d'Alembert formula in the first
coordinate:

  `u₂(x, t) = ½[φ(x₁+ct) + φ(x₁-ct)] + (1/2c) ∫_{x₁-ct}^{x₁+ct} ψ(s) ds`

for all `x ∈ ℝ²` and `t > 0` — recovering d'Alembert's formula, as the problem
requests. -/
theorem dAlembert_by_descent {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 1 ψ)
    {u₂ : EuclideanSpace ℝ (Fin 2) → ℝ → ℝ}
    (hu₂ : ∀ (x : EuclideanSpace ℝ (Fin 2)) {t : ℝ}, 0 < t →
      u₂ x t = Wave.poisson2D c (lift φ) (lift ψ) x t)
    (x : EuclideanSpace ℝ (Fin 2)) {t : ℝ} (ht : 0 < t) :
    u₂ x t = (φ (x 0 + c * t) + φ (x 0 - c * t)) / 2
      + (1 / (2 * c)) * ∫ s in (x 0 - c * t)..(x 0 + c * t), ψ s := by
  rw [hu₂ x ht, poisson2D_lift_eq_dAlembert hc hφ hψ x ht, Wave.dAlembert]

end Problems.Undergraduate.Problem10
