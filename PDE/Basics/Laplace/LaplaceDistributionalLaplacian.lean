import Mathlib
import PDE.Basics.Heat.HeatKernelND
import PDE.Basics.Laplace.FundamentalSolutionND
import PDE.Basics.LaplacianBridge

/-!
# The Distributional Laplacian of `1/‖x‖` in Three Dimensions

Blueprint: `blueprint/src/chapters/PDE_Basics_Laplace_LaplaceDistributionalLaplacian.tex`.

The central computation of potential theory: for every test function
`φ ∈ C_c^∞(ℝ³)`,
`∫ (1/‖x‖) Δφ dx = -4π φ(0)`, i.e. `Δ(1/‖x‖) = -4π δ₀` in the sense of
distributions.

## Route (mollified kernel)

Instead of excising a small ball and using Green's second identity on the
annulus (the source's route), we regularize the singular kernel to the
everywhere-smooth family `ψ_a(x) = (‖x‖² + a²)^{-1/2}` (`mollified`),
compute `Δψ_a = -3a²(‖x‖² + a²)^{-5/2}` exactly (`laplacian_mollified`),
move the Laplacian off the test function by integration by parts over all
of ℝ³ (`mollified_ibp`, Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` applied twice per
direction), and let `a → 0⁺`: the harmonicity defects `-Δψ_a` form a peak
family of constant total mass `4π` (`peak_integral`,
`mollified_concentration`, via Mathlib's
`tendsto_integral_comp_smul_smul_of_integrable`), while dominated
convergence (domination `0 < ψ_a ≤ 1/‖x‖`, `mollified_le_inv_norm`, with
the dominating function locally integrable by
`integrableOn_inv_norm_ball`) sends the left side to
`∫ (1/‖x‖) Δφ` (`dist_laplacian_inv_norm`).

The Laplacian is the trace-form `Heat.laplacian`, identified with
Mathlib's `Δ` by `Basics.laplacian_eq_mathlib`
(`PDE/Basics/LaplacianBridge.lean`).
-/

open MeasureTheory Filter Heat
open scoped Topology ContDiff

/-- The ambient Euclidean 3-space `EuclideanSpace ℝ (Fin 3)` (= `Heat.E 3`). -/
local notation "E3" => Heat.E 3

open Heat

namespace Laplace

/-! ## The mollified kernel and its derivatives -/

/-- **Mollified kernel** (blueprint `def:distlap-mollified`).
For a parameter `a > 0`, `ψ_a(x) = (‖x‖² + a²)^{-1/2}` — an
everywhere-smooth regularization of the singular kernel `1/‖x‖`. -/
noncomputable def mollified (a : ℝ) (x : E3) : ℝ :=
  (‖x‖ ^ 2 + a ^ 2) ^ (-(1 / 2) : ℝ)

/-- The mollified kernel is everywhere positive (companion to
`lem:distlap-mollified-le`). -/
lemma mollified_pos {a : ℝ} (ha : 0 < a) (x : E3) : 0 < mollified a x := by
  have h : (0 : ℝ) < ‖x‖ ^ 2 + a ^ 2 := by positivity
  exact Real.rpow_pos_of_pos h _

/-- The mollified kernel is smooth on all of `E3` (regularity claim of
`def:distlap-mollified`). -/
lemma contDiff_mollified {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (mollified a) := by
  have h : ContDiff ℝ ∞ (fun x : E3 => ‖x‖ ^ 2 + a ^ 2) :=
    (contDiff_norm_sq ℝ).add contDiff_const
  exact h.rpow_const_of_ne fun x => by positivity

/-- **Comparison with the singular kernel** (blueprint
`lem:distlap-mollified-le`): for `x ≠ 0`, `ψ_a(x) ≤ 1/‖x‖`. -/
lemma mollified_le_inv_norm (a : ℝ) {x : E3} (hx : x ≠ 0) :
    mollified a x ≤ 1 / ‖x‖ := by
  have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have h2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hle : ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 + a ^ 2 := by nlinarith [sq_nonneg a]
  calc mollified a x ≤ (‖x‖ ^ 2) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos h2 hle (by norm_num)
    _ = 1 / ‖x‖ := by
        rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x)]
        norm_num [Real.rpow_neg_one]

/-- Pointwise convergence `ψ_a(x) → 1/‖x‖` as `a → 0⁺` for fixed `x ≠ 0`
(limit claim of `lem:distlap-mollified-le`). -/
lemma tendsto_mollified_inv_norm {x : E3} (hx : x ≠ 0) :
    Tendsto (fun a : ℝ => mollified a x) (𝓝[>] 0) (𝓝 (1 / ‖x‖)) := by
  have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have h2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hcont : ContinuousAt (fun a : ℝ => (‖x‖ ^ 2 + a ^ 2) ^ (-(1 / 2) : ℝ)) 0 := by
    refine ContinuousAt.rpow_const ?_ (Or.inl ?_)
    · exact continuousAt_const.add ((continuousAt_id.pow 2))
    · simpa using h2.ne'
  have hval : (‖x‖ ^ 2 + (0 : ℝ) ^ 2) ^ (-(1 / 2) : ℝ) = 1 / ‖x‖ := by
    rw [show ‖x‖ ^ 2 + (0 : ℝ) ^ 2 = ‖x‖ ^ 2 by ring,
      ← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x)]
    norm_num [Real.rpow_neg_one]
  have := hcont.tendsto
  rw [hval] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **Gradient of the mollified kernel** (blueprint
`lem:distlap-mollified-gradient`): at every `x` (origin included),
`∇ψ_a(x) = -(‖x‖² + a²)^{-3/2} • x`. -/
lemma gradient_mollified {a : ℝ} (ha : 0 < a) (x : E3) :
    HasGradientAt (mollified a)
      ((-((‖x‖ ^ 2 + a ^ 2) ^ (-(3 / 2) : ℝ))) • x) x := by
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 + a ^ 2 := by positivity
  -- derivative of the outer profile `s ↦ (s + a²)^{-1/2}` at `s = ‖x‖²`
  have hf : HasDerivAt (fun s : ℝ => (s + a ^ 2) ^ (-(1 / 2) : ℝ))
      (1 * (-(1 / 2) : ℝ) * (‖x‖ ^ 2 + a ^ 2) ^ ((-(1 / 2) : ℝ) - 1)) (‖x‖ ^ 2) :=
    ((hasDerivAt_id (‖x‖ ^ 2)).add_const (a ^ 2)).rpow_const (Or.inl hpos.ne')
  -- chain rule against the squared norm (valid at every x, origin included)
  have hcomp := hf.comp_hasFDerivAt x (Heat.hasFDerivAt_norm_sq x)
  rw [hasGradientAt_iff_hasFDerivAt]
  apply hcomp.congr_fderiv
  ext v
  have hexp : ((-(1 / 2) : ℝ) - 1) = (-(3 / 2) : ℝ) := by norm_num
  simp only [hexp, smul_apply, innerSL_apply_apply,
    InnerProductSpace.toDual_apply_apply, real_inner_smul_left, smul_eq_mul]
  ring

/-- **Laplacian of the mollified kernel** (blueprint
`lem:distlap-mollified-laplacian`): at every `x`,
`Δψ_a(x) = -3a²(‖x‖² + a²)^{-5/2}`. In particular `-Δψ_a > 0`
everywhere. -/
lemma laplacian_mollified {a : ℝ} (ha : 0 < a) (x : E3) :
    Heat.laplacian (mollified a) x =
      -3 * a ^ 2 * (‖x‖ ^ 2 + a ^ 2) ^ (-(5 / 2) : ℝ) := by
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 + a ^ 2 := by positivity
  -- the radial coefficient of the gradient field, as a function of ‖y‖²
  set G : E3 → ℝ := fun y => -((‖y‖ ^ 2 + a ^ 2) ^ (-(3 / 2) : ℝ)) with hG
  -- the gradient field is `y ↦ G y • y`, everywhere
  have hgrad_eq : gradient (mollified a) = fun y : E3 => G y • y :=
    funext fun y => (gradient_mollified ha y).gradient
  -- Fréchet derivative of the radial coefficient at x (uniform, no case split)
  have hf : HasDerivAt (fun s : ℝ => -((s + a ^ 2) ^ (-(3 / 2) : ℝ)))
      (-(1 * (-(3 / 2) : ℝ) * (‖x‖ ^ 2 + a ^ 2) ^ ((-(3 / 2) : ℝ) - 1))) (‖x‖ ^ 2) :=
    (((hasDerivAt_id (‖x‖ ^ 2)).add_const (a ^ 2)).rpow_const (Or.inl hpos.ne')).neg
  have hc : HasFDerivAt G
      ((3 * (‖x‖ ^ 2 + a ^ 2) ^ (-(5 / 2) : ℝ)) • innerSL ℝ x) x := by
    have h := hf.comp_hasFDerivAt x (Heat.hasFDerivAt_norm_sq x)
    apply h.congr_fderiv
    rw [smul_smul]
    congr 1
    rw [show ((-(3 / 2) : ℝ) - 1) = (-(5 / 2) : ℝ) by norm_num]
    ring
  -- Fréchet derivative of the gradient field
  have hF : HasFDerivAt (fun y : E3 => G y • y)
      (G x • ContinuousLinearMap.id ℝ E3 +
        ((3 * (‖x‖ ^ 2 + a ^ 2) ^ (-(5 / 2) : ℝ)) • innerSL ℝ x).smulRight x) x :=
    hc.smul (hasFDerivAt_id x)
  -- the Laplacian as a trace
  unfold Heat.laplacian Heat.div_field
  rw [hgrad_eq, hF.fderiv, Laplace.trace_radial_field_deriv]
  -- arithmetic: 3 G(x) + 3 s^{-5/2} ‖x‖² = -3a² s^{-5/2} with s = ‖x‖² + a²
  have hsplit : (‖x‖ ^ 2 + a ^ 2) ^ (-(3 / 2) : ℝ) =
      (‖x‖ ^ 2 + a ^ 2) ^ (-(5 / 2) : ℝ) * (‖x‖ ^ 2 + a ^ 2) := by
    rw [show (-(3 / 2) : ℝ) = -(5 / 2) + 1 by norm_num, Real.rpow_add hpos,
      Real.rpow_one]
  rw [hG]
  simp only []
  rw [hsplit]
  push_cast [show (Module.finrank ℝ E3 : ℕ) = 3 from finrank_euclideanSpace_fin]
  ring

/-! ## The peak-function normalization -/

/-- The peak profile `Φ̃(u) = 3(1 + ‖u‖²)^{-5/2}` is integrable on ℝ³
(integrability claim of `lem:distlap-peak-integral`; Mathlib's
`integrable_rpow_neg_one_add_norm_sq` with `finrank = 3 < 5 = r`). -/
lemma peak_integrable :
    Integrable (fun u : E3 => 3 * (1 + ‖u‖ ^ 2) ^ (-(5 / 2) : ℝ)) := by
  have h : Integrable (fun u : E3 => ((1 : ℝ) + ‖u‖ ^ 2) ^ ((-(5 : ℝ)) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simp; norm_num)
  have := h.const_mul 3
  simpa [neg_div] using this

/-- The explicit antiderivative of the radial peak integrand:
`d/dr [r³(1 + r²)^{-3/2}] = 3r²(1 + r²)^{-5/2}` at every `r`. -/
private lemma hasDerivAt_peakAntideriv (x : ℝ) :
    HasDerivAt (fun r : ℝ => r ^ 3 * (1 + r ^ 2) ^ (-(3 / 2) : ℝ))
      (x ^ 2 * (3 * (1 + x ^ 2) ^ (-(5 / 2) : ℝ))) x := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  have h2 : HasDerivAt (fun r : ℝ => (1 + r ^ 2) ^ (-(3 / 2) : ℝ))
      (2 * x * (-(3 / 2) : ℝ) * (1 + x ^ 2) ^ ((-(3 / 2) : ℝ) - 1)) x :=
    h1.rpow_const (Or.inl hpos.ne')
  have h3 := (hasDerivAt_pow 3 x).mul h2
  have hsplit : (1 + x ^ 2) ^ (-(3 / 2) : ℝ) =
      (1 + x ^ 2) ^ (-(5 / 2) : ℝ) * (1 + x ^ 2) := by
    rw [show (-(3 / 2) : ℝ) = -(5 / 2) + 1 by norm_num, Real.rpow_add hpos,
      Real.rpow_one]
  have hderiv_eq : (3 : ℕ) * x ^ (3 - 1) * (1 + x ^ 2) ^ (-(3 / 2) : ℝ) +
      x ^ 3 * (2 * x * (-(3 / 2) : ℝ) * (1 + x ^ 2) ^ ((-(3 / 2) : ℝ) - 1)) =
      x ^ 2 * (3 * (1 + x ^ 2) ^ (-(5 / 2) : ℝ)) := by
    rw [show ((-(3 / 2) : ℝ) - 1) = (-(5 / 2) : ℝ) by norm_num, hsplit]
    push_cast
    ring
  exact hderiv_eq ▸ h3

/-- The antiderivative `r³(1 + r²)^{-3/2} = (r²/(1 + r²))^{3/2}` tends to `1`
at infinity. -/
private lemma tendsto_peakAntideriv :
    Tendsto (fun r : ℝ => r ^ 3 * (1 + r ^ 2) ^ (-(3 / 2) : ℝ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
  have h3 : Tendsto (fun r : ℝ => 1 - (1 + r ^ 2)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h1.inv_tendsto_atTop
  have h4 : Tendsto (fun r : ℝ => (1 - (1 + r ^ 2)⁻¹) ^ ((3 : ℝ) / 2))
      atTop (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ ((3 : ℝ) / 2)) 1 :=
      Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
    simpa [Function.comp_def, Real.one_rpow] using hc.tendsto.comp h3
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have heq : 1 - (1 + r ^ 2)⁻¹ = r ^ 2 / (1 + r ^ 2) := by
    field_simp
    ring
  have hnum : (r ^ 2) ^ ((3 : ℝ) / 2) = r ^ 3 := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le,
      show (2 : ℕ) * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hden : (1 + r ^ 2) ^ (-((3 : ℝ) / 2)) = ((1 + r ^ 2) ^ ((3 : ℝ) / 2))⁻¹ :=
    Real.rpow_neg hpos.le _
  rw [heq, Real.div_rpow hr2.le hpos.le, hnum, show (-(3 / 2) : ℝ) = -((3 : ℝ) / 2)
    by norm_num, hden, div_eq_mul_inv]

/-- The radial peak integral: `∫_0^∞ 3r²(1 + r²)^{-5/2} dr = 1`
(improper FTC against the antiderivative `r³(1 + r²)^{-3/2}`). -/
private lemma radial_peak_integral
    (hint : IntegrableOn
      (fun y : ℝ => y ^ 2 * (3 * (1 + y ^ 2) ^ (-(5 / 2) : ℝ))) (Set.Ioi 0)) :
    ∫ y in Set.Ioi (0 : ℝ), y ^ 2 * (3 * (1 + y ^ 2) ^ (-(5 / 2) : ℝ)) = 1 := by
  have hFcont : Continuous
      (fun r : ℝ => r ^ 3 * (1 + r ^ 2) ^ (-(3 / 2) : ℝ)) := by
    refine (continuous_pow 3).mul ?_
    exact (continuous_const.add (continuous_pow 2)).rpow_const
      fun x => Or.inl (show (1 : ℝ) + x ^ 2 ≠ 0 by positivity)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun r : ℝ => r ^ 3 * (1 + r ^ 2) ^ (-(3 / 2) : ℝ))
    (f' := fun y : ℝ => y ^ 2 * (3 * (1 + y ^ 2) ^ (-(5 / 2) : ℝ)))
    (a := 0) (m := 1)
    hFcont.continuousWithinAt
    (fun x _ => hasDerivAt_peakAntideriv x)
    hint tendsto_peakAntideriv
  simpa using h

/-- **Total mass of the peak profile** (blueprint
`lem:distlap-peak-integral`): `∫_{ℝ³} 3(1 + ‖u‖²)^{-5/2} du = 4π`. -/
lemma peak_integral :
    ∫ u : E3, 3 * (1 + ‖u‖ ^ 2) ^ (-(5 / 2) : ℝ) = 4 * Real.pi := by
  -- polar decomposition of the volume integral
  have h := MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure E3))
    (fun s : ℝ => 3 * (1 + s ^ 2) ^ (-(5 / 2) : ℝ))
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at h
  -- integrability of the radial integrand, from integrability of the profile
  have hint : IntegrableOn
      (fun y : ℝ => y ^ 2 * (3 * (1 + y ^ 2) ^ (-(5 / 2) : ℝ))) (Set.Ioi 0) := by
    have := (MeasureTheory.integrable_fun_norm_addHaar (μ := (volume : Measure E3))
      (f := fun s : ℝ => 3 * (1 + s ^ 2) ^ (-(5 / 2) : ℝ))).mp peak_integrable
    simpa [finrank_euclideanSpace_fin, smul_eq_mul] using this
  -- the unit-ball volume in dimension 3
  have hball : volume.real (Metric.ball (0 : E3) 1) = Real.pi * 4 / 3 := by
    have h3 := Laplace.unitBallVolume_three
    unfold Laplace.unitBallVolume at h3
    simpa [MeasureTheory.measureReal_def] using h3
  rw [show (fun u : E3 => 3 * (1 + ‖u‖ ^ 2) ^ (-(5 / 2) : ℝ)) =
    fun u : E3 => (fun s : ℝ => 3 * (1 + s ^ 2) ^ (-(5 / 2) : ℝ)) ‖u‖ from rfl,
    h, hball, radial_peak_integral hint]
  ring

/-! ## Local integrability of the singular kernel -/

/-- **Local integrability of `1/‖y‖`** (blueprint
`lem:distlap-locally-integrable`, integrability claim): `y ↦ 1/‖y‖` is
integrable on every ball `B(0, r) ⊆ ℝ³`. -/
lemma integrableOn_inv_norm_ball {r : ℝ} (_hr : 0 < r) :
    IntegrableOn (fun y : E3 => 1 / ‖y‖) (Metric.ball 0 r) volume := by
  rw [show (fun y : E3 => 1 / ‖y‖) = fun y : E3 => (fun s : ℝ => 1 / s) ‖y‖ from rfl,
    MeasureTheory.integrableOn_fun_norm_addHaar volume]
  have heq : Set.EqOn (fun y : ℝ => y ^ (Module.finrank ℝ E3 - 1) • (1 / y))
      (fun y : ℝ => y) (Set.Ioo 0 r) := by
    intro y hy
    have hy0 : y ≠ 0 := hy.1.ne'
    simp only [finrank_euclideanSpace_fin, smul_eq_mul]
    field_simp
  rw [integrableOn_congr_fun heq measurableSet_Ioo]
  exact (continuous_id.integrableOn_Icc (μ := volume) (a := 0) (b := r)).mono_set
    Set.Ioo_subset_Icc_self

/-- Value of the small-ball integral (value claim of
`lem:distlap-locally-integrable`): `∫_{B(0,r)} 1/‖y‖ dy = 2πr²`. -/
lemma integral_inv_norm_ball {r : ℝ} (hr : 0 < r) :
    ∫ y in Metric.ball (0 : E3) r, 1 / ‖y‖ = 2 * Real.pi * r ^ 2 := by
  -- extend the integrand from the ball to a global radial profile
  have hind : ∫ y in Metric.ball (0 : E3) r, 1 / ‖y‖ =
      ∫ y : E3, (fun s : ℝ => (Set.Iio r).indicator (fun t => 1 / t) s) ‖y‖ := by
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ Metric.ball (0 : E3) r
    · have hmem : ‖y‖ ∈ Set.Iio r := by
        simpa [Metric.mem_ball, dist_zero_right] using hy
      rw [Set.indicator_of_mem hy]
      simp only []
      rw [Set.indicator_of_mem hmem]
    · have hmem : ‖y‖ ∉ Set.Iio r := by
        simpa [Metric.mem_ball, dist_zero_right] using hy
      rw [Set.indicator_of_notMem hy]
      simp only []
      rw [Set.indicator_of_notMem hmem]
  -- polar decomposition
  rw [hind, MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure E3))]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  -- the radial integral reduces to ∫_{(0,r)} y dy = r²/2
  have hradial : ∫ y in Set.Ioi (0 : ℝ),
      y ^ (3 - 1) * (Set.Iio r).indicator (fun t => 1 / t) y = r ^ 2 / 2 := by
    have heq : ∀ y ∈ Set.Ioi (0 : ℝ),
        y ^ (3 - 1) * (Set.Iio r).indicator (fun t => 1 / t) y =
        (Set.Ioo 0 r).indicator id y := by
      intro y (hy : 0 < y)
      by_cases hyr : y < r
      · rw [Set.indicator_of_mem (Set.mem_Iio.mpr hyr),
          Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hy, hyr⟩)]
        simp only [id]
        field_simp
      · rw [Set.indicator_of_notMem (by simpa using hyr),
          Set.indicator_of_notMem (by simp [Set.mem_Ioo, hyr])]
        ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq,
      MeasureTheory.integral_indicator measurableSet_Ioo,
      Measure.restrict_restrict_of_subset (Set.Ioo_subset_Ioi_self)]
    have : ∫ y in Set.Ioo (0 : ℝ) r, y = ∫ y in (0)..r, y := by
      rw [intervalIntegral.integral_of_le hr.le,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [show (id : ℝ → ℝ) = fun y => y from rfl, this, integral_id]
    ring
  rw [hradial]
  -- the unit-ball volume in dimension 3
  have hball : volume.real (Metric.ball (0 : E3) 1) = Real.pi * 4 / 3 := by
    have h3 := Laplace.unitBallVolume_three
    unfold Laplace.unitBallVolume at h3
    simpa [MeasureTheory.measureReal_def] using h3
  rw [hball]
  ring

/-! ## Integration by parts and concentration -/

/-- Expansion of the project Laplacian of a `C²` function as the sum of pure
second directional derivatives along the standard orthonormal basis (via the
bridge `Basics.laplacian_eq_mathlib` and Mathlib's
`laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`). -/
private lemma laplacian_eq_sum_dirDeriv {h : E3 → ℝ} (hh : ContDiff ℝ 2 h)
    (x : E3) :
    Heat.laplacian h x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ h y (stdOrthonormalBasis ℝ E3 i)) x
        (stdOrthonormalBasis ℝ E3 i) := by
  rw [Basics.laplacian_eq_mathlib,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  have hc : DifferentiableAt ℝ (fderiv ℝ h) x :=
    ((hh.fderiv_right le_rfl).differentiable one_ne_zero).differentiableAt
  rw [fderiv_clm_apply hc (differentiableAt_const _)]
  simp [ContinuousLinearMap.flip_apply]

/-- **Moving the Laplacian onto the mollified kernel** (blueprint
`lem:distlap-ibp`): for `a > 0` and `φ ∈ C_c^∞(ℝ³)`,
`∫ ψ_a Δφ = ∫ (Δψ_a) φ`. -/
lemma mollified_ibp {a : ℝ} (ha : 0 < a) {φ : E3 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    ∫ x : E3, mollified a x * Heat.laplacian φ x =
      ∫ x : E3, Heat.laplacian (mollified a) x * φ x := by
  classical
  have hψ : ContDiff ℝ ∞ (mollified a) := contDiff_mollified ha
  have hψ2 : ContDiff ℝ 2 (mollified a) := contDiff_infty.mp hψ 2
  have hφ2 : ContDiff ℝ 2 φ := contDiff_infty.mp hφ 2
  have hψc : Continuous (mollified a) := hψ.continuous
  have hφc : Continuous φ := hφ.continuous
  -- per-direction double integration by parts
  have key : ∀ v : E3,
      ∫ x : E3, mollified a x * fderiv ℝ (fun y => fderiv ℝ φ y v) x v =
      ∫ x : E3, fderiv ℝ (fun y => fderiv ℝ (mollified a) y v) x v * φ x := by
    intro v
    -- the four directional-derivative functions in play
    set Dφ : E3 → ℝ := fun x => fderiv ℝ φ x v with hDφdef
    set Dψ : E3 → ℝ := fun x => fderiv ℝ (mollified a) x v with hDψdef
    -- regularity
    have hDφ1 : ContDiff ℝ 1 Dφ :=
      (hφ2.fderiv_right le_rfl).clm_apply contDiff_const
    have hDψ1 : ContDiff ℝ 1 Dψ :=
      (hψ2.fderiv_right le_rfl).clm_apply contDiff_const
    have hDφc : Continuous Dφ := hDφ1.continuous
    have hDψc : Continuous Dψ := hDψ1.continuous
    have hDDφc : Continuous (fun x => fderiv ℝ Dφ x v) :=
      contDiff_zero.mp ((hDφ1.fderiv_right le_rfl).clm_apply contDiff_const)
    have hDDψc : Continuous (fun x => fderiv ℝ Dψ x v) :=
      contDiff_zero.mp ((hDψ1.fderiv_right le_rfl).clm_apply contDiff_const)
    -- compact supports
    have hDφsupp : HasCompactSupport Dφ :=
      (hsupp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E3 →L[ℝ] ℝ => L v) rfl
    have hDDφsupp : HasCompactSupport (fun x => fderiv ℝ Dφ x v) :=
      (hDφsupp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E3 →L[ℝ] ℝ => L v) rfl
    -- differentiability, everywhere
    have hψdiff : Differentiable ℝ (mollified a) :=
      hψ2.differentiable (by norm_num)
    have hφdiff : Differentiable ℝ φ := hφ2.differentiable (by norm_num)
    have hDφdiff : Differentiable ℝ Dφ := hDφ1.differentiable one_ne_zero
    have hDψdiff : Differentiable ℝ Dψ := hDψ1.differentiable one_ne_zero
    -- first IBP: f = ψ_a, g = Dφ
    have h1 : ∫ x : E3, mollified a x * fderiv ℝ Dφ x v =
        -∫ x : E3, fderiv ℝ (mollified a) x v * Dφ x := by
      refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
        (fun x _ => hψdiff.differentiableAt) (fun x _ => hDφdiff.differentiableAt)
      · exact (hDψc.mul hDφc).integrable_of_hasCompactSupport
          (hDφsupp.mul_left)
      · exact (hψc.mul hDDφc).integrable_of_hasCompactSupport
          (hDDφsupp.mul_left)
      · exact (hψc.mul hDφc).integrable_of_hasCompactSupport
          (hDφsupp.mul_left)
    -- second IBP: f = Dψ, g = φ
    have h2 : ∫ x : E3, Dψ x * fderiv ℝ φ x v =
        -∫ x : E3, fderiv ℝ Dψ x v * φ x := by
      refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
        (fun x _ => hDψdiff.differentiableAt) (fun x _ => hφdiff.differentiableAt)
      · exact (hDDψc.mul hφc).integrable_of_hasCompactSupport
          (hsupp.mul_left)
      · exact (hDψc.mul hDφc).integrable_of_hasCompactSupport
          (hDφsupp.mul_left)
      · exact (hDψc.mul hφc).integrable_of_hasCompactSupport
          (hsupp.mul_left)
    -- chain the two: ∫ ψ (DDφ) = -∫ Dψ Dφ = ∫ (DDψ) φ
    have hswap : ∫ x : E3, fderiv ℝ (mollified a) x v * Dφ x =
        ∫ x : E3, Dψ x * fderiv ℝ φ x v :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => rfl)
    rw [h1, hswap, h2, neg_neg]
  -- expand both Laplacians and swap integral and finite sum
  have hexpφ : (fun x : E3 => mollified a x * Heat.laplacian φ x) =
      fun x : E3 => ∑ i, mollified a x *
        fderiv ℝ (fun y => fderiv ℝ φ y (stdOrthonormalBasis ℝ E3 i)) x
          (stdOrthonormalBasis ℝ E3 i) :=
    funext fun x => by rw [laplacian_eq_sum_dirDeriv hφ2 x, Finset.mul_sum]
  have hexpψ : (fun x : E3 => Heat.laplacian (mollified a) x * φ x) =
      fun x : E3 => ∑ i,
        fderiv ℝ (fun y => fderiv ℝ (mollified a) y (stdOrthonormalBasis ℝ E3 i)) x
          (stdOrthonormalBasis ℝ E3 i) * φ x :=
    funext fun x => by rw [laplacian_eq_sum_dirDeriv hψ2 x, Finset.sum_mul]
  -- integrability of each summand (for the integral/sum swap)
  have hsummand_φ : ∀ i : Fin (Module.finrank ℝ E3),
      Integrable (fun x : E3 => mollified a x *
        fderiv ℝ (fun y => fderiv ℝ φ y (stdOrthonormalBasis ℝ E3 i)) x
          (stdOrthonormalBasis ℝ E3 i)) := by
    intro i
    set v := stdOrthonormalBasis ℝ E3 i
    have hDφ1 : ContDiff ℝ 1 (fun x => fderiv ℝ φ x v) :=
      (hφ2.fderiv_right le_rfl).clm_apply contDiff_const
    have hDDφc : Continuous
        (fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x v) :=
      contDiff_zero.mp ((hDφ1.fderiv_right le_rfl).clm_apply contDiff_const)
    have hDφsupp : HasCompactSupport (fun x => fderiv ℝ φ x v) :=
      (hsupp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E3 →L[ℝ] ℝ => L v) rfl
    have hDDφsupp : HasCompactSupport
        (fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x v) :=
      (hDφsupp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E3 →L[ℝ] ℝ => L v) rfl
    exact (hψc.mul hDDφc).integrable_of_hasCompactSupport hDDφsupp.mul_left
  have hsummand_ψ : ∀ i : Fin (Module.finrank ℝ E3),
      Integrable (fun x : E3 =>
        fderiv ℝ (fun y => fderiv ℝ (mollified a) y (stdOrthonormalBasis ℝ E3 i)) x
          (stdOrthonormalBasis ℝ E3 i) * φ x) := by
    intro i
    set v := stdOrthonormalBasis ℝ E3 i
    have hDψ1 : ContDiff ℝ 1 (fun x => fderiv ℝ (mollified a) x v) :=
      (hψ2.fderiv_right le_rfl).clm_apply contDiff_const
    have hDDψc : Continuous
        (fun x => fderiv ℝ (fun y => fderiv ℝ (mollified a) y v) x v) :=
      contDiff_zero.mp ((hDψ1.fderiv_right le_rfl).clm_apply contDiff_const)
    exact (hDDψc.mul hφc).integrable_of_hasCompactSupport hsupp.mul_left
  rw [hexpφ, hexpψ, MeasureTheory.integral_finsetSum _ (fun i _ => hsummand_φ i),
    MeasureTheory.integral_finsetSum _ (fun i _ => hsummand_ψ i)]
  exact Finset.sum_congr rfl fun i _ => key (stdOrthonormalBasis ℝ E3 i)

/-- The exact scaling identity behind the concentration argument: with
`c = 1/a`, the harmonicity defect `-Δψ_a` is the renormalized peak profile
`c³ Φ̃(c • x)`. -/
private lemma scaling_identity {a : ℝ} (ha : 0 < a) (x : E3) :
    a⁻¹ ^ 3 * (3 * (1 + ‖a⁻¹ • x‖ ^ 2) ^ (-(5 / 2) : ℝ)) =
      3 * a ^ 2 * (‖x‖ ^ 2 + a ^ 2) ^ (-(5 / 2) : ℝ) := by
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hbase : 1 + ‖a⁻¹ • x‖ ^ 2 = (‖x‖ ^ 2 + a ^ 2) / a ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  have hden : (a ^ 2) ^ (-(5 / 2) : ℝ) = (a ^ 5)⁻¹ := by
    rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le,
      show (2 : ℕ) * (-(5 / 2) : ℝ) = -((5 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg ha.le, Real.rpow_natCast]
  rw [hbase, Real.div_rpow (by positivity) ha2.le, hden]
  have h5 : (0 : ℝ) < a ^ 5 := by positivity
  field_simp

/-- **Concentration of the harmonicity defect** (blueprint
`lem:distlap-concentration`): for `φ ∈ C_c^∞(ℝ³)`,
`∫ (-Δψ_a) φ → 4π φ(0)` as `a → 0⁺`. -/
lemma mollified_concentration {φ : E3 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    Tendsto (fun a : ℝ =>
        ∫ x : E3, -Heat.laplacian (mollified a) x * φ x)
      (𝓝[>] 0) (𝓝 (4 * Real.pi * φ 0)) := by
  have hπ : (0 : ℝ) < 4 * Real.pi := by positivity
  -- the normalized peak profile Φ̃/4π
  set p : E3 → ℝ := fun u => (4 * Real.pi)⁻¹ * (3 * (1 + ‖u‖ ^ 2) ^ (-(5 / 2) : ℝ))
    with hp
  have h_nonneg : ∀ u, 0 ≤ p u := fun u => by
    have : (0 : ℝ) < 1 + ‖u‖ ^ 2 := by positivity
    have := Real.rpow_pos_of_pos this (-(5 / 2) : ℝ)
    positivity
  have h_int_one : ∫ u : E3, p u = 1 := by
    rw [hp, MeasureTheory.integral_const_mul, peak_integral]
    field_simp
  -- decay: ‖x‖³ p(x) → 0 at infinity
  have h_decay : Tendsto (fun x : E3 => ‖x‖ ^ (Module.finrank ℝ E3) * p x)
      (Bornology.cobounded E3) (𝓝 0) := by
    have hsplit : ∀ r : ℝ, (1 + r ^ 2) ^ (-(5 / 2) : ℝ) =
        (1 + r ^ 2) ^ (-(3 / 2) : ℝ) * (1 + r ^ 2)⁻¹ := fun r => by
      have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
      rw [show (-(5 / 2) : ℝ) = -(3 / 2) + (-1) by norm_num,
        Real.rpow_add hpos, Real.rpow_neg_one]
    have h1 : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
    have hradial : Tendsto
        (fun r : ℝ => r ^ 3 * ((4 * Real.pi)⁻¹ *
          (3 * (1 + r ^ 2) ^ (-(5 / 2) : ℝ)))) atTop (𝓝 0) := by
      have hprod : Tendsto
          (fun r : ℝ => (4 * Real.pi)⁻¹ * 3 *
            ((r ^ 3 * (1 + r ^ 2) ^ (-(3 / 2) : ℝ)) * (1 + r ^ 2)⁻¹))
          atTop (𝓝 ((4 * Real.pi)⁻¹ * 3 * (1 * 0))) :=
        (tendsto_const_nhds.mul
          (tendsto_peakAntideriv.mul h1.inv_tendsto_atTop))
      simp only [mul_zero] at hprod
      refine hprod.congr fun r => ?_
      rw [hsplit r]
      ring
    have hcomp := hradial.comp
      (tendsto_norm_cobounded_atTop :
        Tendsto (norm : E3 → ℝ) (Bornology.cobounded E3) atTop)
    simp only [finrank_euclideanSpace_fin]
    exact hcomp.congr fun x => by simp [hp]
  -- the peak-function theorem, at c → ∞
  have hg_int : Integrable φ :=
    hφ.continuous.integrable_of_hasCompactSupport hsupp
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable
    h_nonneg h_int_one h_decay hg_int hφ.continuous.continuousAt
  -- multiply by the constant 4π and substitute c = a⁻¹
  have hmul := hpeak.const_mul (4 * Real.pi)
  have hcomp := hmul.comp tendsto_inv_nhdsGT_zero
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  simp only [Function.comp_apply, finrank_euclideanSpace_fin, smul_eq_mul]
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show 4 * Real.pi * (a⁻¹ ^ 3 * p (a⁻¹ • x) * φ x) =
    -Heat.laplacian (mollified a) x * φ x
  rw [laplacian_mollified ha x, hp]
  have key := scaling_identity ha x
  have h4 : (4 * Real.pi) * (4 * Real.pi)⁻¹ = 1 := mul_inv_cancel₀ hπ.ne'
  linear_combination φ x * key +
    φ x * (a⁻¹ ^ 3 * (3 * (1 + ‖a⁻¹ • x‖ ^ 2) ^ (-(5 / 2) : ℝ))) * h4

/-- Continuity of `Δφ` for smooth `φ` (side fact for the main theorem;
avoids the ω-graded root-namespace `laplacian_continuous`). -/
private lemma laplacian_continuous_of_contDiff {φ : E3 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    Continuous (fun x => Heat.laplacian φ x) := by
  have hφ2 : ContDiff ℝ 2 φ := contDiff_infty.mp hφ 2
  have hgrad : ContDiff ℝ 1 (gradient φ) := by
    have hfd : ContDiff ℝ 1 (fderiv ℝ φ) := hφ2.fderiv_right le_rfl
    exact ((InnerProductSpace.toDual ℝ E3).symm.contDiff.comp hfd :)
  have hcont : Continuous (fun x => fderiv ℝ (gradient φ) x) :=
    hgrad.continuous_fderiv one_ne_zero
  exact _root_.continuous_trace.comp hcont

/-- Compact support of `Δφ` (side fact for the main theorem; the root
`laplacian_compact_support` at `n = 3` is definitionally this statement). -/
private lemma laplacian_hasCompactSupport {φ : E3 → ℝ}
    (hsupp : HasCompactSupport φ) :
    HasCompactSupport (fun x => Heat.laplacian φ x) :=
  _root_.laplacian_compact_support φ hsupp

/-! ## The main theorem -/

/-- **Distributional Laplacian of `1/‖x‖`** (blueprint
`thm:dist-laplacian-inv-norm`; Choksi, Theorem 10.1): for every test
function `φ ∈ C_c^∞(ℝ³)`,
`∫_{ℝ³} (1/‖x‖) Δφ(x) dx = -4π φ(0)` — the bare pairing form of
`Δ(1/‖x‖) = -4π δ₀` in the sense of distributions. -/
theorem dist_laplacian_inv_norm {φ : E3 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    ∫ x : E3, (1 / ‖x‖) * Heat.laplacian φ x = -(4 * Real.pi) * φ 0 := by
  -- the support of Δφ is contained in a ball B(0, R)
  have hΔsupp : HasCompactSupport (fun x => Heat.laplacian φ x) :=
    laplacian_hasCompactSupport hsupp
  have hΔcont : Continuous (fun x => Heat.laplacian φ x) :=
    laplacian_continuous_of_contDiff hφ
  obtain ⟨R, hR, hRsupp⟩ : ∃ R > 0,
      tsupport (fun x => Heat.laplacian φ x) ⊆ Metric.ball (0 : E3) R := by
    obtain ⟨R, hR, hsub⟩ :=
      hΔsupp.isBounded.subset_ball_lt 0 0
    exact ⟨R, hR, hsub⟩
  -- a uniform bound for Δφ
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖Heat.laplacian φ x‖ ≤ M :=
    hΔsupp.exists_bound_of_continuous hΔcont
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  -- limit (i): dominated convergence gives ∫ ψ_a Δφ → ∫ ‖x‖⁻¹ Δφ
  have h_lim1 : Tendsto (fun a : ℝ => ∫ x : E3, mollified a x * Heat.laplacian φ x)
      (𝓝[>] 0) (𝓝 (∫ x : E3, (1 / ‖x‖) * Heat.laplacian φ x)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := (Metric.ball (0 : E3) R).indicator fun x => (1 / ‖x‖) * M)
      ?_ ?_ ?_ ?_
    · -- a.e.-strong measurability of ψ_a Δφ for a > 0
      filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
      exact ((contDiff_mollified ha).continuous.mul hΔcont).aestronglyMeasurable
    · -- domination by the fixed integrable bound
      filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : E3))]
        with x (hx : x ≠ 0)
      by_cases hxR : x ∈ Metric.ball (0 : E3) R
      · rw [Set.indicator_of_mem hxR]
        have h1 : 0 < mollified a x := mollified_pos ha x
        have h2 : mollified a x ≤ 1 / ‖x‖ := mollified_le_inv_norm a hx
        calc ‖mollified a x * Heat.laplacian φ x‖
            = mollified a x * ‖Heat.laplacian φ x‖ := by
              rw [norm_mul, Real.norm_eq_abs, abs_of_pos h1]
          _ ≤ (1 / ‖x‖) * M :=
              mul_le_mul h2 (hM x) (norm_nonneg _)
                (by positivity)
      · rw [Set.indicator_of_notMem hxR]
        have hzero : Heat.laplacian φ x = 0 :=
          image_eq_zero_of_notMem_tsupport fun hmem => hxR (hRsupp hmem)
        simp [hzero]
    · -- the bound is integrable
      rw [MeasureTheory.integrable_indicator_iff measurableSet_ball]
      exact (integrableOn_inv_norm_ball hR).mul_const M
    · -- a.e.-pointwise convergence
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : E3))]
        with x (hx : x ≠ 0)
      exact (tendsto_mollified_inv_norm hx).mul_const _
  -- limit (ii): IBP + concentration give ∫ ψ_a Δφ → -4π φ(0)
  have h_lim2 : Tendsto (fun a : ℝ => ∫ x : E3, mollified a x * Heat.laplacian φ x)
      (𝓝[>] 0) (𝓝 (-(4 * Real.pi) * φ 0)) := by
    have hneg : Tendsto (fun a : ℝ =>
        -∫ x : E3, -Heat.laplacian (mollified a) x * φ x)
        (𝓝[>] 0) (𝓝 (-(4 * Real.pi * φ 0))) :=
      (mollified_concentration hφ hsupp).neg
    have heq : (fun a : ℝ => -∫ x : E3, -Heat.laplacian (mollified a) x * φ x)
        =ᶠ[𝓝[>] 0] fun a : ℝ => ∫ x : E3, mollified a x * Heat.laplacian φ x := by
      filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
      rw [mollified_ibp ha hφ hsupp, ← MeasureTheory.integral_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    have := hneg.congr' heq
    simpa [neg_mul] using this
  -- uniqueness of limits along 𝓝[>] 0
  exact tendsto_nhds_unique h_lim1 h_lim2

end Laplace
