import Mathlib
import PDE.Background.FunctionalAnalysis.DistributionPairing1D

/-!
# Undergraduate Problem 27: Distributional Derivative of a Ramp Sequence

Source: `pde_latex/problems/undergraduate/problem_27.tex` (Math 418/718
Midterm, Problem A).

## Informal statement

> Consider the sequence of functions
> `f_n(x) = 0` for `x ≤ -1/n`, `-nx` for `-1/n < x < 0`, `1` for `x ≥ 0`.
> Find the distributional derivative of each `f_n`.

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem27.tex`:

* Distributions live on `Ω = (⊤ : Opens ℝ)` and are Mathlib's `𝓓'(Ω, ℝ)`;
  the pairing `toDistribution`, the derivative `distDeriv`, and the IBP
  lemmas come from the shared layer
  `PDE.Background.FunctionalAnalysis.DistributionPairing1D`.
* Answer (`thm:problem27-fn-deriv`): for `n ≥ 1`,
  `f_n' = δ_{-1/n} + δ_0 + T_{h_n}` where
  `h_n = (-n)·𝟙_(-1/n, 0)` records the classical slope of the middle
  piece; the two jumps of height `+1` (at `-1/n` and at `0`) contribute
  the Dirac masses.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff
open PDE.Background.FunctionalAnalysis.DistributionPairing1D

namespace Problems.Undergraduate.Problem27

/-- **The ramp sequence** (blueprint `def:problem27-fn`):
`f_n = 0` on `x ≤ -1/n`, `-nx` on `-1/n < x < 0`, `1` on `x ≥ 0`.
Bounded and measurable, hence locally integrable. -/
noncomputable def fn (n : ℕ) (x : ℝ) : ℝ :=
  if x ≤ -(1 / (n : ℝ)) then 0 else if x < 0 then -(n : ℝ) * x else 1

/-- `fn n` is measurable (piecewise on measurable pieces). -/
lemma measurable_fn (n : ℕ) : Measurable (fn n) := by
  unfold fn
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iio (by fun_prop) measurable_const)

/-- `fn n` is bounded by `1`: on the middle piece `-1/n < x < 0` the value
`-nx` lies in `[0, 1]`. -/
lemma abs_fn_le_one (n : ℕ) (x : ℝ) : |fn n x| ≤ 1 := by
  unfold fn
  split_ifs with h1 h2
  · norm_num
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hx : -(1 / (n : ℝ)) < x := not_le.mp h1
    have hnonneg : (0 : ℝ) ≤ -(n : ℝ) * x := by nlinarith
    rw [abs_of_nonneg hnonneg]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h' : (-1 : ℝ) < x * (n : ℝ) := by
        rw [← div_lt_iff₀ hnpos, neg_div]; exact hx
      nlinarith [h']
  · norm_num

/-- `fn n` is locally integrable on `ℝ` (bounded and measurable). -/
lemma locallyIntegrableOn_fn (n : ℕ) :
    LocallyIntegrableOn (fn n) ((⊤ : Opens ℝ) : Set ℝ) volume := by
  rw [Opens.coe_top, locallyIntegrableOn_univ]
  exact (memLp_top_of_bound (measurable_fn n).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_fn_le_one n x)).locallyIntegrable le_top

/-- The regular part `h_n = (-n)·𝟙_(-1/n, 0)` of the derivative is locally
integrable (bounded with compact support). -/
lemma locallyIntegrableOn_indicator_slope (n : ℕ) :
    LocallyIntegrableOn ((Ioo (-(1 / (n : ℝ))) 0).indicator fun _ => -(n : ℝ))
      ((⊤ : Opens ℝ) : Set ℝ) volume := by
  rw [Opens.coe_top, locallyIntegrableOn_univ]
  refine Integrable.locallyIntegrable ?_
  rw [integrable_indicator_iff measurableSet_Ioo]
  exact integrableOn_const measure_Ioo_lt_top.ne

/-- **Problem 27** (blueprint `thm:problem27-fn-deriv`): for `n ≥ 1`, in the
sense of distributions,
`f_n' = δ_{-1/n} + δ_0 + T_{h_n}` with `h_n = (-n)·𝟙_(-1/n, 0)`: the jumps
of `f_n` at `-1/n` and `0` (each of height `+1`) contribute the Dirac
masses, and the classical slope `-n` of the middle piece contributes the
regular part. -/
theorem fn_deriv (n : ℕ) (hn : 1 ≤ n) :
    distDeriv (toDistribution (fn n))
      = Distribution.delta (-(1 / (n : ℝ)))
        + Distribution.delta (0 : ℝ)
        + toDistribution
            ((Ioo (-(1 / (n : ℝ))) 0).indicator fun _ => -(n : ℝ)) := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
  have hab : -(1 / (n : ℝ)) ≤ (0 : ℝ) :=
    neg_nonpos.mpr (one_div_nonneg.mpr (Nat.cast_nonneg n))
  ext φ
  have hφd : Continuous (deriv (φ : ℝ → ℝ)) :=
    φ.contDiff.continuous_deriv (by norm_num)
  have hF : Integrable (fun x => deriv (φ : ℝ → ℝ) x * fn n x) volume :=
    (hφd.integrable_of_hasCompactSupport φ.hasCompactSupport.deriv).mul_bdd
      (measurable_fn n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using abs_fn_le_one n x)
  -- the three pieces
  have p1 : ∫ x in Iic (-(1 / (n : ℝ))), deriv (φ : ℝ → ℝ) x * fn n x
      = 0 := by
    rw [setIntegral_congr_fun (g := fun _ => (0 : ℝ)) measurableSet_Iic
      (fun x (hx : x ≤ -(1 / (n : ℝ))) => by
        rw [show fn n x = 0 from if_pos hx, mul_zero]),
      integral_zero]
  have p2 : ∫ x in (-(1 / (n : ℝ)))..0, deriv (φ : ℝ → ℝ) x * fn n x
      = -φ (-(1 / (n : ℝ)))
        - ∫ x in (-(1 / (n : ℝ)))..0, -(n : ℝ) * φ x := by
    have hcongr : ∫ x in (-(1 / (n : ℝ)))..0, deriv (φ : ℝ → ℝ) x * fn n x
        = ∫ x in (-(1 / (n : ℝ)))..0,
            (-(n : ℝ) * x) * deriv (φ : ℝ → ℝ) x := by
      rw [intervalIntegral.integral_of_le hab,
        intervalIntegral.integral_of_le hab,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      exact setIntegral_congr_fun measurableSet_Ioo fun x hx => by
        have hx2 : fn n x = -(n : ℝ) * x := by
          unfold fn; rw [if_neg (not_le.mpr hx.1), if_pos hx.2]
        rw [hx2, mul_comm]
    have hderiv : (deriv fun x : ℝ => -(n : ℝ) * x) = fun _ => -(n : ℝ) := by
      funext x
      simp
    have hibp := intervalIntegral_mul_deriv_ibp (-(1 / (n : ℝ))) 0 hab
      (fun x => -(n : ℝ) * x) φ (by fun_prop) φ.contDiff
    rw [hcongr, hibp]
    simp_rw [hderiv]
    have hval : -(n : ℝ) * -(1 / (n : ℝ)) = 1 := by field_simp
    rw [hval]
    ring
  have p3 : ∫ x in Ioi (0 : ℝ), deriv (φ : ℝ → ℝ) x * fn n x
      = -(1 * φ 0) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x (hx : (0 : ℝ) < x) => by
        have hx1 : fn n x = 1 := by
          unfold fn
          rw [if_neg (not_le.mpr (lt_of_le_of_lt hab hx)),
            if_neg (not_lt.mpr hx.le)]
        rw [hx1, mul_comm])]
    exact integral_Ioi_const_mul_deriv 1 0 φ φ.contDiff φ.hasCompactSupport
  -- split the full-line integral at the breakpoints
  have split : ∫ x, deriv (φ : ℝ → ℝ) x * fn n x
      = (∫ x in Iic (-(1 / (n : ℝ))), deriv (φ : ℝ → ℝ) x * fn n x)
        + ((∫ x in (-(1 / (n : ℝ)))..0, deriv (φ : ℝ → ℝ) x * fn n x)
          + ∫ x in Ioi (0 : ℝ), deriv (φ : ℝ → ℝ) x * fn n x) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hF.integrableOn
        hF.integrableOn,
      ← intervalIntegral.integral_interval_add_Ioi
        (a := -(1 / (n : ℝ))) (b := (0 : ℝ)) hF.integrableOn hF.integrableOn]
  -- the pairing with the indicator density
  have hind : ∫ x, φ x
        * (Ioo (-(1 / (n : ℝ))) 0).indicator (fun _ => -(n : ℝ)) x
      = ∫ x in (-(1 / (n : ℝ)))..0, -(n : ℝ) * φ x := by
    have hswap : (fun x => φ x
          * (Ioo (-(1 / (n : ℝ))) 0).indicator (fun _ => -(n : ℝ)) x)
        = (Ioo (-(1 / (n : ℝ))) 0).indicator fun x => -(n : ℝ) * φ x := by
      ext x
      simp only [Set.indicator_apply]
      split_ifs <;> ring
    rw [hswap, MeasureTheory.integral_indicator measurableSet_Ioo,
      intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  calc distDeriv (toDistribution (fn n)) φ
      = -toDistribution (fn n) (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) :=
        distDeriv_apply _ φ
    _ = -∫ x, deriv (φ : ℝ → ℝ) x * fn n x := by
        rw [toDistribution_apply (locallyIntegrableOn_fn n)]
        simp_rw [lineDerivCLM_one_apply]
    _ = φ (-(1 / (n : ℝ))) + φ 0
          + ∫ x in (-(1 / (n : ℝ)))..0, -(n : ℝ) * φ x := by
        rw [split, p1, p2, p3]; ring
    _ = ((Distribution.delta (-(1 / (n : ℝ))) + Distribution.delta (0 : ℝ)
          + toDistribution ((Ioo (-(1 / (n : ℝ))) 0).indicator
              fun _ => -(n : ℝ))) : 𝓓'((⊤ : Opens ℝ), ℝ)) φ := by
        rw [FunLike.coe_add, Pi.add_apply, FunLike.coe_add, Pi.add_apply,
          Distribution.delta_apply, Distribution.delta_apply,
          toDistribution_apply (locallyIntegrableOn_indicator_slope n), hind]

end Problems.Undergraduate.Problem27
