import Mathlib
import PDE.Background.FunctionalAnalysis.DistributionPairing1D

/-!
# Undergraduate Problem 26: Distributional Derivatives of a Piecewise Function and of `|x|`

Source: `pde_latex/problems/undergraduate/problem_26.tex` (Math 418 Fall 2022,
HW-9, Part 2, Problem 1).

## Informal statement

> (a) Use the definition of the distributional derivative to find the
> first-order derivative (in the distributional sense) of the piecewise
> function `h` that is `2` on `x ≤ -1`, `0` on `-1 < x < 1`, `x²` on
> `1 ≤ x ≤ 2`, and `4` on `x > 2`.
>
> (b) For `f(x) = |x|`, find `f''` directly from the definition of the
> second-order distributional derivative, then as the first derivative of
> `f'`. Do the two computations agree as distributions?

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem26.tex`:

* Distributions live on `Ω = (⊤ : Opens ℝ)` and are Mathlib's
  `𝓓'(Ω, ℝ)` (`Distribution`, blueprint `def:dist-pairing` /
  `def:dist-deriv` / `def:dist-delta`, all `\mathlibok`).
* A locally integrable `f : ℝ → ℝ` is paired with test functions through
  `TestFunction.integralAgainstBilinCLM` specialized to real multiplication
  and the Lebesgue measure; the local abbreviation `toDistribution` below
  records exactly that specialization.
* The distributional derivative is `Distribution.lineDerivCLM` in the
  direction `(1 : ℝ)`; the local abbreviation `distDeriv` pins the order
  parameters to `⊤`.
* The sign function of the blueprint (value at `0` irrelevant) is
  Mathlib's `Real.sign`.
* Answers: `h' = -2·δ₋₁ + δ₁ + T_g` with `g = 2x·𝟙_(1,2)`
  (`thm:problem26-h-deriv`), and `|x|'' = 2·δ₀` both directly
  (`thm:problem26-abs-second-direct`) and as `(T_sgn)' = 2·δ₀` composed
  with `|x|' = T_sgn` (`lem:problem26-abs-first`,
  `thm:problem26-abs-second-via-first`, `cor:problem26-agree`).
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff
open PDE.Background.FunctionalAnalysis.DistributionPairing1D

namespace Problems.Undergraduate.Problem26

/-- `Real.sign` is measurable (it is piecewise constant on the measurable
pieces `Iio 0`, `{0}`, `Ioi 0`). -/
lemma measurable_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

/-- `Real.sign` is bounded by `1`. -/
lemma abs_sign_le_one (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with hs | hs | hs <;> rw [hs] <;> norm_num

/-- `Real.sign` is locally integrable on `ℝ` (bounded and measurable). -/
lemma locallyIntegrableOn_sign :
    LocallyIntegrableOn Real.sign ((⊤ : Opens ℝ) : Set ℝ) volume := by
  rw [Opens.coe_top, locallyIntegrableOn_univ]
  exact (memLp_top_of_bound measurable_sign.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_sign_le_one x)).locallyIntegrable le_top

/-! ## Part (a): the piecewise function `h` -/

/-- **The piecewise function `h`** (blueprint `def:problem26-h`):
`h = 2` on `x ≤ -1`, `0` on `-1 < x < 1`, `x²` on `1 ≤ x ≤ 2`, `4` on
`x > 2`. Bounded and measurable, hence locally integrable. -/
noncomputable def h (x : ℝ) : ℝ :=
  if x ≤ -1 then 2 else if x < 1 then 0 else if x ≤ 2 then x ^ 2 else 4

/-- `h` is measurable (piecewise on measurable pieces). -/
lemma measurable_h : Measurable h := by
  unfold h
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Iic (by fun_prop) measurable_const))

/-- `h` is bounded by `4`. -/
lemma abs_h_le_four (x : ℝ) : |h x| ≤ 4 := by
  unfold h
  split_ifs with h1 h2 h3
  · norm_num
  · norm_num
  · rw [abs_of_nonneg (by positivity)]
    nlinarith [not_lt.mp h2, not_le.mp h1]
  · norm_num

/-- `h` is locally integrable on `ℝ` (bounded and measurable). -/
lemma locallyIntegrableOn_h :
    LocallyIntegrableOn h ((⊤ : Opens ℝ) : Set ℝ) volume := by
  rw [Opens.coe_top, locallyIntegrableOn_univ]
  exact (memLp_top_of_bound measurable_h.aestronglyMeasurable 4
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_h_le_four x)).locallyIntegrable le_top

/-- The right-hand-side density `g = 2x·𝟙_(1,2)` is locally integrable. -/
lemma locallyIntegrableOn_indicator_two_mul :
    LocallyIntegrableOn ((Ioo (1 : ℝ) 2).indicator fun x => 2 * x)
      ((⊤ : Opens ℝ) : Set ℝ) volume := by
  rw [Opens.coe_top, locallyIntegrableOn_univ]
  refine Integrable.locallyIntegrable ?_
  rw [integrable_indicator_iff measurableSet_Ioo]
  exact ((continuous_const.mul continuous_id).integrableOn_Icc).mono_set
    Ioo_subset_Icc_self

/-- **Problem 26(a)** (blueprint `thm:problem26-h-deriv`): in the sense of
distributions, `h' = -2·δ₋₁ + δ₁ + T_g` where `g = 2x·𝟙_(1,2)`. The jumps
of `h` at `-1` and `1` contribute the Dirac masses; there is no jump at
`2`. -/
theorem h_deriv :
    distDeriv (toDistribution h)
      = (-2 : ℝ) • Distribution.delta (-1 : ℝ) + Distribution.delta (1 : ℝ)
        + toDistribution ((Ioo (1 : ℝ) 2).indicator fun x => 2 * x) := by
  ext φ
  have hφd : Continuous (deriv (φ : ℝ → ℝ)) :=
    φ.contDiff.continuous_deriv (by norm_num)
  have hF : Integrable (fun x => deriv (φ : ℝ → ℝ) x * h x) volume :=
    (hφd.integrable_of_hasCompactSupport φ.hasCompactSupport.deriv).mul_bdd
      measurable_h.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using abs_h_le_four x)
  -- the four pieces
  have p1 : ∫ x in Iic (-1 : ℝ), deriv (φ : ℝ → ℝ) x * h x = 2 * φ (-1) := by
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun x (hx : x ≤ -1) => by
        rw [show h x = 2 from if_pos hx, mul_comm])]
    exact integral_Iic_const_mul_deriv 2 (-1) φ φ.contDiff φ.hasCompactSupport
  have p2 : ∫ x in (-1 : ℝ)..1, deriv (φ : ℝ → ℝ) x * h x = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun (g := fun _ => (0 : ℝ)) measurableSet_Ioo
        (fun x hx => by
          have hx0 : h x = 0 := by
            unfold h; rw [if_neg (not_le.mpr hx.1), if_pos hx.2]
          rw [hx0, mul_zero]),
      integral_zero]
  have p3 : ∫ x in (1 : ℝ)..2, deriv (φ : ℝ → ℝ) x * h x
      = 4 * φ 2 - 1 * φ 1 - ∫ x in (1 : ℝ)..2, 2 * x * φ x := by
    have hcongr : ∫ x in (1 : ℝ)..2, deriv (φ : ℝ → ℝ) x * h x
        = ∫ x in (1 : ℝ)..2, x ^ 2 * deriv (φ : ℝ → ℝ) x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
      have hx2 : h x = x ^ 2 := by
        unfold h
        rw [if_neg (by linarith [hx.1]), if_neg (not_lt.mpr hx.1),
          if_pos hx.2]
      rw [hx2, mul_comm]
    have hibp := intervalIntegral_mul_deriv_ibp 1 2 (by norm_num)
      (fun x => x ^ 2) φ (by fun_prop) φ.contDiff
    rw [hcongr, hibp]
    norm_num [deriv_pow]
  have p4 : ∫ x in Ioi (2 : ℝ), deriv (φ : ℝ → ℝ) x * h x = -(4 * φ 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x (hx : 2 < x) => by
        have hx4 : h x = 4 := by
          unfold h
          rw [if_neg (by linarith), if_neg (by linarith),
            if_neg (not_le.mpr hx)]
        rw [hx4, mul_comm])]
    exact integral_Ioi_const_mul_deriv 4 2 φ φ.contDiff φ.hasCompactSupport
  -- split the full-line integral at the breakpoints
  have split : ∫ x, deriv (φ : ℝ → ℝ) x * h x
      = (∫ x in Iic (-1 : ℝ), deriv (φ : ℝ → ℝ) x * h x)
        + ((∫ x in (-1 : ℝ)..1, deriv (φ : ℝ → ℝ) x * h x)
          + ((∫ x in (1 : ℝ)..2, deriv (φ : ℝ → ℝ) x * h x)
            + ∫ x in Ioi (2 : ℝ), deriv (φ : ℝ → ℝ) x * h x)) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hF.integrableOn
        hF.integrableOn,
      ← intervalIntegral.integral_interval_add_Ioi (a := (-1 : ℝ))
        (b := (1 : ℝ)) hF.integrableOn hF.integrableOn,
      ← intervalIntegral.integral_interval_add_Ioi (a := (1 : ℝ))
        (b := (2 : ℝ)) hF.integrableOn hF.integrableOn]
  -- the pairing with the indicator density
  have hind : ∫ x, φ x * (Ioo (1 : ℝ) 2).indicator (fun x => 2 * x) x
      = ∫ x in (1 : ℝ)..2, 2 * x * φ x := by
    have hswap : (fun x => φ x * (Ioo (1 : ℝ) 2).indicator (fun x => 2 * x) x)
        = (Ioo (1 : ℝ) 2).indicator fun x => 2 * x * φ x := by
      ext x
      by_cases hx : x ∈ Ioo (1 : ℝ) 2
      · simp [hx, mul_comm]
      · simp [hx]
    rw [hswap, MeasureTheory.integral_indicator measurableSet_Ioo,
      intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
      integral_Ioc_eq_integral_Ioo]
  calc distDeriv (toDistribution h) φ
      = -toDistribution h (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) :=
        distDeriv_apply _ φ
    _ = -∫ x, deriv (φ : ℝ → ℝ) x * h x := by
        rw [toDistribution_apply locallyIntegrableOn_h]
        simp_rw [lineDerivCLM_one_apply]
    _ = -2 * φ (-1) + φ 1 + ∫ x in (1 : ℝ)..2, 2 * x * φ x := by
        rw [split, p1, p2, p3, p4]; ring
    _ = ((-2 : ℝ) • Distribution.delta (-1 : ℝ) + Distribution.delta (1 : ℝ)
          + toDistribution ((Ioo (1 : ℝ) 2).indicator fun x => 2 * x) :
          𝓓'((⊤ : Opens ℝ), ℝ)) φ := by
        rw [FunLike.coe_add, Pi.add_apply, FunLike.coe_add, Pi.add_apply,
          FunLike.coe_smul, Pi.smul_apply,
          Distribution.delta_apply, Distribution.delta_apply,
          toDistribution_apply locallyIntegrableOn_indicator_two_mul, hind,
          smul_eq_mul]

/-! ## Part (b): the second derivative of `|x|`, two ways -/

/-- **The first derivative of `|x|` is `sgn`** (blueprint
`lem:problem26-abs-first`): in the sense of distributions,
`|·|' = T_sgn`, where `sgn` is Mathlib's `Real.sign` (its value at `0` is
irrelevant under the integral). -/
theorem abs_deriv :
    distDeriv (toDistribution fun x => |x|) = toDistribution Real.sign := by
  ext φ
  have hφ1 : ContDiff ℝ 1 (φ : ℝ → ℝ) := φ.contDiff.of_le (by norm_num)
  have hφc : Continuous (φ : ℝ → ℝ) := φ.contDiff.continuous
  have hφd : Continuous (deriv (φ : ℝ → ℝ)) := hφ1.continuous_deriv le_rfl
  have habs : LocallyIntegrableOn (fun x : ℝ => |x|) ((⊤ : Opens ℝ) : Set ℝ)
      volume := by
    rw [Opens.coe_top, locallyIntegrableOn_univ]
    exact continuous_abs.locallyIntegrable
  have hφint : Integrable (φ : ℝ → ℝ) volume :=
    hφc.integrable_of_hasCompactSupport φ.hasCompactSupport
  -- integrability of `deriv φ * |x|`
  have hmulint : Integrable (fun x => deriv (φ : ℝ → ℝ) x * |x|) volume :=
    (hφd.mul continuous_abs).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.deriv.mul_right)
  -- left piece: `∫_{Iic 0} deriv φ · |x| = ∫_{Iic 0} φ`
  have h1 : ∫ x in Iic (0 : ℝ), deriv (φ : ℝ → ℝ) x * |x|
      = ∫ x in Iic (0 : ℝ), φ x := by
    have hval : ∫ x in Iic (0 : ℝ), deriv (φ : ℝ → ℝ) x * |x|
        = ∫ x in Iic (0 : ℝ), (-x) * deriv (φ : ℝ → ℝ) x := by
      rw [integral_Iic_eq_integral_Iio, integral_Iic_eq_integral_Iio]
      exact setIntegral_congr_fun measurableSet_Iio fun x (hx : x < 0) => by
        rw [abs_of_neg hx, mul_comm]
    have hzero : Filter.Tendsto ((fun x : ℝ => -x) * (φ : ℝ → ℝ))
        (nhdsWithin 0 (Iio 0)) (nhds 0) := by
      have h0 : Filter.Tendsto ((fun x : ℝ => -x) * (φ : ℝ → ℝ))
          (nhds 0) (nhds 0) := by
        simpa using (continuous_neg.mul hφc).tendsto 0
      exact h0.mono_left nhdsWithin_le_nhds
    have hinfty : Filter.Tendsto ((fun x : ℝ => -x) * (φ : ℝ → ℝ))
        Filter.atBot (nhds 0) :=
      (φ.hasCompactSupport.mul_left.is_zero_at_infty).mono_left
        atBot_le_cocompact
    have hibp := MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul
      (u := fun x : ℝ => -x) (u' := fun _ : ℝ => -1)
      (v := (φ : ℝ → ℝ)) (v' := deriv (φ : ℝ → ℝ)) (a := (0 : ℝ))
      (fun x _ => (hasDerivAt_id x).neg)
      (fun x _ => (hφ1.differentiable one_ne_zero x).hasDerivAt)
      (((continuous_neg.mul hφd).integrable_of_hasCompactSupport
        φ.hasCompactSupport.deriv.mul_left).integrableOn)
      (((continuous_const.mul hφc).integrable_of_hasCompactSupport
        φ.hasCompactSupport.mul_left).integrableOn)
      hzero hinfty
    rw [hval, hibp]
    simp [MeasureTheory.integral_neg]
  -- right piece: `∫_{Ioi 0} deriv φ · |x| = -∫_{Ioi 0} φ`
  have h2 : ∫ x in Ioi (0 : ℝ), deriv (φ : ℝ → ℝ) x * |x|
      = -∫ x in Ioi (0 : ℝ), φ x := by
    have hval : ∫ x in Ioi (0 : ℝ), deriv (φ : ℝ → ℝ) x * |x|
        = ∫ x in Ioi (0 : ℝ), x * deriv (φ : ℝ → ℝ) x :=
      setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => by
        rw [abs_of_pos hx, mul_comm]
    have hzero : Filter.Tendsto ((fun x : ℝ => x) * (φ : ℝ → ℝ))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have h0 : Filter.Tendsto ((fun x : ℝ => x) * (φ : ℝ → ℝ))
          (nhds 0) (nhds 0) := by
        simpa using (continuous_id'.mul hφc).tendsto 0
      exact h0.mono_left nhdsWithin_le_nhds
    have hinfty : Filter.Tendsto ((fun x : ℝ => x) * (φ : ℝ → ℝ))
        Filter.atTop (nhds 0) :=
      (φ.hasCompactSupport.mul_left.is_zero_at_infty).mono_left
        atTop_le_cocompact
    have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (u := fun x : ℝ => x) (u' := fun _ : ℝ => 1)
      (v := (φ : ℝ → ℝ)) (v' := deriv (φ : ℝ → ℝ)) (a := (0 : ℝ))
      (fun x _ => hasDerivAt_id x)
      (fun x _ => (hφ1.differentiable one_ne_zero x).hasDerivAt)
      (((continuous_id.mul hφd).integrable_of_hasCompactSupport
        φ.hasCompactSupport.deriv.mul_left).integrableOn)
      (((continuous_const.mul hφc).integrable_of_hasCompactSupport
        φ.hasCompactSupport.mul_left).integrableOn)
      hzero hinfty
    rw [hval, hibp]
    simp
  -- the sign pairing splits the same way
  have hsgnint : Integrable (fun x => φ x * Real.sign x) volume :=
    hφint.mul_bdd measurable_sign.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using abs_sign_le_one x)
  have hsgn : ∫ x, φ x * Real.sign x
      = -(∫ x in Iic (0 : ℝ), φ x) + ∫ x in Ioi (0 : ℝ), φ x := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hsgnint.integrableOn
      hsgnint.integrableOn]
    congr 1
    · rw [integral_Iic_eq_integral_Iio, integral_Iic_eq_integral_Iio,
        setIntegral_congr_fun measurableSet_Iio
          (fun x (hx : x < 0) => by rw [Real.sign_of_neg hx, mul_neg_one]),
        MeasureTheory.integral_neg]
    · exact setIntegral_congr_fun measurableSet_Ioi
        fun x (hx : 0 < x) => by rw [Real.sign_of_pos hx, mul_one]
  calc distDeriv (toDistribution fun x => |x|) φ
      = -toDistribution (fun x => |x|)
          (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) := distDeriv_apply _ φ
    _ = -∫ x, deriv (φ : ℝ → ℝ) x * |x| := by
        rw [toDistribution_apply habs]
        simp_rw [lineDerivCLM_one_apply]
    _ = -(∫ x in Iic (0 : ℝ), φ x) + ∫ x in Ioi (0 : ℝ), φ x := by
        rw [← intervalIntegral.integral_Iic_add_Ioi hmulint.integrableOn
          hmulint.integrableOn, h1, h2]
        ring
    _ = ∫ x, φ x * Real.sign x := hsgn.symm
    _ = toDistribution Real.sign φ :=
        (toDistribution_apply locallyIntegrableOn_sign φ).symm

/-- **Problem 26(b), via the first derivative** (blueprint
`thm:problem26-abs-second-via-first`): the distributional derivative of the
sign function is `2·δ₀`; combined with `abs_deriv` this computes `|x|''`
as the first derivative of the first derivative. -/
theorem sgn_deriv :
    distDeriv (toDistribution Real.sign)
      = (2 : ℝ) • Distribution.delta (0 : ℝ) := by
  ext φ
  have hφd : Integrable (deriv (φ : ℝ → ℝ)) volume :=
    (φ.contDiff.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
      φ.hasCompactSupport.deriv
  have hint : Integrable (fun x => deriv (φ : ℝ → ℝ) x * Real.sign x) volume :=
    hφd.mul_bdd measurable_sign.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using abs_sign_le_one x)
  have h1 : ∫ x in Iic (0 : ℝ), deriv (φ : ℝ → ℝ) x * Real.sign x
      = -1 * φ 0 := by
    rw [integral_Iic_eq_integral_Iio,
      setIntegral_congr_fun measurableSet_Iio
        (fun x (hx : x < 0) => by rw [Real.sign_of_neg hx, mul_comm]),
      ← integral_Iic_eq_integral_Iio]
    exact integral_Iic_const_mul_deriv (-1) 0 φ φ.contDiff φ.hasCompactSupport
  have h2 : ∫ x in Ioi (0 : ℝ), deriv (φ : ℝ → ℝ) x * Real.sign x
      = -(1 * φ 0) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x (hx : 0 < x) => by rw [Real.sign_of_pos hx, mul_comm])]
    exact integral_Ioi_const_mul_deriv 1 0 φ φ.contDiff φ.hasCompactSupport
  have key : ∫ x, deriv (φ : ℝ → ℝ) x * Real.sign x = -(2 * φ 0) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn
      hint.integrableOn, h1, h2]
    ring
  calc distDeriv (toDistribution Real.sign) φ
      = -toDistribution Real.sign (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) :=
        distDeriv_apply _ φ
    _ = -∫ x, (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ :
          𝓓((⊤ : Opens ℝ), ℝ)) x * Real.sign x := by
        rw [toDistribution_apply locallyIntegrableOn_sign]
    _ = -∫ x, deriv (φ : ℝ → ℝ) x * Real.sign x := by
        simp_rw [lineDerivCLM_one_apply]
    _ = 2 * φ 0 := by rw [key]; ring
    _ = ((2 : ℝ) • Distribution.delta (0 : ℝ)) φ := by simp

/-- **IBP core for the direct computation**: for any bundled test function
`ψ`, `∫ ψ'(x)·|x| dx = ∫_{Iic 0} ψ - ∫_{Ioi 0} ψ`. This is the genuine
half-line integration by parts against `|x|` (with `u = ∓x`), stated for an
arbitrary test function so that `abs_second_deriv_direct` can instantiate
it at the bundled derivative `ψ = φ'`. -/
lemma integral_deriv_mul_abs (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ∫ x, deriv (ψ : ℝ → ℝ) x * |x|
      = (∫ x in Iic (0 : ℝ), ψ x) - ∫ x in Ioi (0 : ℝ), ψ x := by
  have hψ1 : ContDiff ℝ 1 (ψ : ℝ → ℝ) := ψ.contDiff.of_le (by norm_num)
  have hψc : Continuous (ψ : ℝ → ℝ) := ψ.contDiff.continuous
  have hψd : Continuous (deriv (ψ : ℝ → ℝ)) := hψ1.continuous_deriv le_rfl
  have hmulint : Integrable (fun x => deriv (ψ : ℝ → ℝ) x * |x|) volume :=
    (hψd.mul continuous_abs).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.deriv.mul_right)
  -- left piece: `∫_{Iic 0} ψ' · |x| = ∫_{Iic 0} ψ` (IBP with `u = -x`)
  have h1 : ∫ x in Iic (0 : ℝ), deriv (ψ : ℝ → ℝ) x * |x|
      = ∫ x in Iic (0 : ℝ), ψ x := by
    have hval : ∫ x in Iic (0 : ℝ), deriv (ψ : ℝ → ℝ) x * |x|
        = ∫ x in Iic (0 : ℝ), (-x) * deriv (ψ : ℝ → ℝ) x := by
      rw [integral_Iic_eq_integral_Iio, integral_Iic_eq_integral_Iio]
      exact setIntegral_congr_fun measurableSet_Iio fun x (hx : x < 0) => by
        rw [abs_of_neg hx, mul_comm]
    have hzero : Filter.Tendsto ((fun x : ℝ => -x) * (ψ : ℝ → ℝ))
        (nhdsWithin 0 (Iio 0)) (nhds 0) := by
      have h0 : Filter.Tendsto ((fun x : ℝ => -x) * (ψ : ℝ → ℝ))
          (nhds 0) (nhds 0) := by
        simpa using (continuous_neg.mul hψc).tendsto 0
      exact h0.mono_left nhdsWithin_le_nhds
    have hinfty : Filter.Tendsto ((fun x : ℝ => -x) * (ψ : ℝ → ℝ))
        Filter.atBot (nhds 0) :=
      (ψ.hasCompactSupport.mul_left.is_zero_at_infty).mono_left
        atBot_le_cocompact
    have hibp := MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul
      (u := fun x : ℝ => -x) (u' := fun _ : ℝ => -1)
      (v := (ψ : ℝ → ℝ)) (v' := deriv (ψ : ℝ → ℝ)) (a := (0 : ℝ))
      (fun x _ => (hasDerivAt_id x).neg)
      (fun x _ => (hψ1.differentiable one_ne_zero x).hasDerivAt)
      (((continuous_neg.mul hψd).integrable_of_hasCompactSupport
        ψ.hasCompactSupport.deriv.mul_left).integrableOn)
      (((continuous_const.mul hψc).integrable_of_hasCompactSupport
        ψ.hasCompactSupport.mul_left).integrableOn)
      hzero hinfty
    rw [hval, hibp]
    simp [MeasureTheory.integral_neg]
  -- right piece: `∫_{Ioi 0} ψ' · |x| = -∫_{Ioi 0} ψ` (IBP with `u = x`)
  have h2 : ∫ x in Ioi (0 : ℝ), deriv (ψ : ℝ → ℝ) x * |x|
      = -∫ x in Ioi (0 : ℝ), ψ x := by
    have hval : ∫ x in Ioi (0 : ℝ), deriv (ψ : ℝ → ℝ) x * |x|
        = ∫ x in Ioi (0 : ℝ), x * deriv (ψ : ℝ → ℝ) x :=
      setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => by
        rw [abs_of_pos hx, mul_comm]
    have hzero : Filter.Tendsto ((fun x : ℝ => x) * (ψ : ℝ → ℝ))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have h0 : Filter.Tendsto ((fun x : ℝ => x) * (ψ : ℝ → ℝ))
          (nhds 0) (nhds 0) := by
        simpa using (continuous_id'.mul hψc).tendsto 0
      exact h0.mono_left nhdsWithin_le_nhds
    have hinfty : Filter.Tendsto ((fun x : ℝ => x) * (ψ : ℝ → ℝ))
        Filter.atTop (nhds 0) :=
      (ψ.hasCompactSupport.mul_left.is_zero_at_infty).mono_left
        atTop_le_cocompact
    have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (u := fun x : ℝ => x) (u' := fun _ : ℝ => 1)
      (v := (ψ : ℝ → ℝ)) (v' := deriv (ψ : ℝ → ℝ)) (a := (0 : ℝ))
      (fun x _ => hasDerivAt_id x)
      (fun x _ => (hψ1.differentiable one_ne_zero x).hasDerivAt)
      (((continuous_id.mul hψd).integrable_of_hasCompactSupport
        ψ.hasCompactSupport.deriv.mul_left).integrableOn)
      (((continuous_const.mul hψc).integrable_of_hasCompactSupport
        ψ.hasCompactSupport.mul_left).integrableOn)
      hzero hinfty
    rw [hval, hibp]
    simp
  rw [← intervalIntegral.integral_Iic_add_Ioi hmulint.integrableOn
    hmulint.integrableOn, h1, h2]
  ring

/-- **Problem 26(b), direct computation** (blueprint
`thm:problem26-abs-second-direct`): the second-order distributional
derivative of `|x|` — computed directly from the definition,
`⟨|·|'', φ⟩ = ⟨T_{|·|}, φ''⟩ = 2φ(0)` — equals `2·δ₀`. The intended DIRECT
route: unfold the definition twice to `⟨T_{|x|}, φ''⟩` and integrate by
parts on each half-line. -/
/- Planner strategy:
Do NOT use `abs_deriv` or `sgn_deriv` in this proof — the point is the
direct computation from the definition.
1. `ext φ`, then apply `distDeriv_apply` twice: the two minus signs cancel,
   giving `⟨T'', φ⟩ = ⟨T_{|x|}, (φ')'⟩`. Here
   `TestFunction.lineDerivCLM ℝ 1 φ` is the *bundled* test function whose
   coercion to `ℝ → ℝ` is `deriv φ` (pointwise via `lineDerivCLM_one_apply`,
   :125). Its `.contDiff` and `.hasCompactSupport` fields exist (verified:
   `TestFunction.contDiff` / `TestFunction.hasCompactSupport` apply to any
   bundled test function).
2. Unfold the pairing with `toDistribution_apply habs` (the local
   integrability fact `habs` for `|·|` is proved inline in `abs_deriv`,
   :302 — reprove it the same way) and rewrite with `lineDerivCLM_one_apply`
   (`simp_rw`), so the goal becomes
   `∫ x, deriv (deriv φ) x * |x| = 2 * φ 0` (up to signs/layout).
3. Now mirror the `abs_deriv` proof (:296) verbatim with `φ` replaced by the
   bundled `TestFunction.lineDerivCLM ℝ 1 φ`:
   * split the integral at 0 via `intervalIntegral.integral_Iic_add_Ioi`;
   * left half: `MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul` with
     `u = -x` (as at :330); right half:
     `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` with `u = x`
     (as at :359); boundary terms vanish (compact support + `u 0 = 0`);
   * writing `ψ := deriv φ`, after IBP the two halves are
     `∫_{Iic 0} ψ` and `-∫_{Ioi 0} ψ`, i.e. `∫_{Iic 0} deriv φ` and
     `-∫_{Ioi 0} deriv φ`; evaluate them with
     `integral_Iic_const_mul_deriv 1 0` (:57) and
     `integral_Ioi_const_mul_deriv 1 0` (:66) applied to the original `φ`,
     yielding `φ 0` and `-(-φ 0)` — total `2 * φ 0`.
4. Finish with `Distribution.delta_apply` + `smul_eq_mul`, as in the final
   calc step of `sgn_deriv` (:432).
-/
theorem abs_second_deriv_direct :
    distDeriv (distDeriv (toDistribution fun x => |x|))
      = (2 : ℝ) • Distribution.delta (0 : ℝ) := by
  ext φ
  have habs : LocallyIntegrableOn (fun x : ℝ => |x|) ((⊤ : Opens ℝ) : Set ℝ)
      volume := by
    rw [Opens.coe_top, locallyIntegrableOn_univ]
    exact continuous_abs.locallyIntegrable
  -- the bundled test function `ψ = φ'`
  set ψ : 𝓓((⊤ : Opens ℝ), ℝ) := TestFunction.lineDerivCLM ℝ (1 : ℝ) φ with hψ
  -- the half-line integrals of `ψ = φ'` are `φ 0` and `-φ 0`
  have hIic : ∫ x in Iic (0 : ℝ), ψ x = φ 0 := by
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun x _ => lineDerivCLM_one_apply φ x)]
    simpa using
      integral_Iic_const_mul_deriv 1 0 φ φ.contDiff φ.hasCompactSupport
  have hIoi : ∫ x in Ioi (0 : ℝ), ψ x = -φ 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x _ => lineDerivCLM_one_apply φ x)]
    simpa using
      integral_Ioi_const_mul_deriv 1 0 φ φ.contDiff φ.hasCompactSupport
  calc distDeriv (distDeriv (toDistribution fun x => |x|)) φ
      = -distDeriv (toDistribution fun x => |x|) ψ := distDeriv_apply _ φ
    _ = toDistribution (fun x => |x|) (TestFunction.lineDerivCLM ℝ (1 : ℝ) ψ)
        := by rw [distDeriv_apply, neg_neg]
    _ = ∫ x, deriv (ψ : ℝ → ℝ) x * |x| := by
        rw [toDistribution_apply habs]
        simp_rw [lineDerivCLM_one_apply]
    _ = (∫ x in Iic (0 : ℝ), ψ x) - ∫ x in Ioi (0 : ℝ), ψ x :=
        integral_deriv_mul_abs ψ
    _ = 2 * φ 0 := by rw [hIic, hIoi]; ring
    _ = ((2 : ℝ) • Distribution.delta (0 : ℝ)) φ := by simp

/-- **The two computations of `|x|''` agree** (blueprint
`cor:problem26-agree`): the second-order distributional derivative of
`|x|` and the derivative of `|x|' = T_sgn` are equal as distributions —
both are `2·δ₀`. -/
theorem abs_second_deriv_agree :
    distDeriv (distDeriv (toDistribution fun x => |x|))
      = distDeriv (toDistribution Real.sign) :=
  abs_second_deriv_direct.trans sgn_deriv.symm

end Problems.Undergraduate.Problem26
