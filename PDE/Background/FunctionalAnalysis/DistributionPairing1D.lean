import Mathlib

/-!
# Shared 1-D Distribution Infrastructure

Shared 1-D distribution infrastructure (regular-distribution pairing,
distributional derivative in direction 1, IBP lemmas) on Mathlib's `𝓓'`
API; consumed by Problems 26 and 27.

## Main declarations

* `integral_Iic_const_mul_deriv` — half-line IBP on the left:
  `∫_{-∞}^a c·φ' = c·φ(a)`
* `integral_Ioi_const_mul_deriv` — half-line IBP on the right:
  `∫_a^∞ c·φ' = -c·φ(a)`
* `intervalIntegral_mul_deriv_ibp` — IBP on a bounded interval
* `toDistribution` — the regular distribution `T_f` of a locally
  integrable `f : ℝ → ℝ`
* `distDeriv` — the distributional derivative on `ℝ` (direction `1`)
* `toDistribution_apply`, `distDeriv_apply`, `lineDerivCLM_one_apply` —
  unfolding lemmas for the pairing and the derivative
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff

namespace PDE.Background.FunctionalAnalysis.DistributionPairing1D

/-! ## Integration-by-parts infrastructure

These three lemmas are stated for bare smooth compactly supported functions
(rather than bundled test functions) so that later files (Problem 27) can
reuse them directly. -/

/-- **Half-line integral of a derivative, left** (blueprint
`lem:dist-ibp-halfline-left`): for a test function `φ`,
`∫_{-∞}^a c·φ'(x) dx = c·φ(a)`. -/
theorem integral_Iic_const_mul_deriv (c a : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    ∫ x in Iic a, c * deriv φ x = c * φ a := by
  rw [MeasureTheory.integral_const_mul,
    HasCompactSupport.integral_Iic_deriv_eq (hφ.of_le (by norm_num)) hsupp]

/-- **Half-line integral of a derivative, right** (blueprint
`lem:dist-ibp-halfline-right`): for a test function `φ`,
`∫_a^∞ c·φ'(x) dx = -c·φ(a)`. -/
theorem integral_Ioi_const_mul_deriv (c a : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    ∫ x in Ioi a, c * deriv φ x = -(c * φ a) := by
  rw [MeasureTheory.integral_const_mul,
    HasCompactSupport.integral_Ioi_deriv_eq (hφ.of_le (by norm_num)) hsupp,
    mul_neg]

/-- **Integration by parts on a bounded interval** (blueprint
`lem:dist-ibp-interval`): for `g` continuously differentiable and `φ` a
test function,
`∫_a^b g·φ' = g(b)φ(b) - g(a)φ(a) - ∫_a^b g'·φ`. -/
theorem intervalIntegral_mul_deriv_ibp (a b : ℝ) (_hab : a ≤ b) (g φ : ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) (hφ : ContDiff ℝ ∞ φ) :
    ∫ x in a..b, g x * deriv φ x
      = g b * φ b - g a * φ a - ∫ x in a..b, deriv g x * φ x := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => (hg.differentiable one_ne_zero x).hasDerivAt)
    (fun x _ => (hφ1.differentiable one_ne_zero x).hasDerivAt)
    ((hg.continuous_deriv le_rfl).intervalIntegrable a b)
    ((hφ1.continuous_deriv le_rfl).intervalIntegrable a b)

/-! ## Distribution-level abbreviations

Readability specializations of the chapter's three Mathlib anchors; they
introduce no new mathematics. -/

/-- The distribution `T_f` of a locally integrable `f : ℝ → ℝ` (blueprint
`def:dist-pairing`, backed by Mathlib's
`TestFunction.integralAgainstBilinCLM` specialized to real multiplication
and the Lebesgue measure): `⟨T_f, φ⟩ = ∫ f·φ`. -/
noncomputable abbrev toDistribution (f : ℝ → ℝ) : 𝓓'((⊤ : Opens ℝ), ℝ) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) volume f

/-- The distributional derivative on `ℝ` (blueprint `def:dist-deriv`,
backed by Mathlib's `Distribution.lineDerivCLM` in direction `1`):
`⟨T', φ⟩ = -⟨T, φ'⟩`. -/
noncomputable abbrev distDeriv (T : 𝓓'((⊤ : Opens ℝ), ℝ)) :
    𝓓'((⊤ : Opens ℝ), ℝ) :=
  Distribution.lineDerivCLM (1 : ℝ) T

/-- Unfolding the pairing: for `f` locally integrable,
`⟨T_f, φ⟩ = ∫ φ·f`. (Mathlib's bilinear pairing applies the test function
on the left.) -/
lemma toDistribution_apply {f : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (⊤ : Opens ℝ) volume)
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    toDistribution f φ = ∫ x, φ x * f x :=
  TestFunction.integralAgainstBilinCLM_eq_integral hf

/-- Unfolding the distributional derivative:
`⟨T', φ⟩ = -⟨T, ∂₁φ⟩` where `∂₁φ` is the classical derivative of the test
function `φ` along `1`. -/
lemma distDeriv_apply (T : 𝓓'((⊤ : Opens ℝ), ℝ)) (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    distDeriv T φ = -T (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ) :=
  Distribution.lineDerivCLM_apply

/-- The test-function derivative along `1` is the ordinary derivative:
`(∂₁φ)(x) = φ'(x)`. -/
lemma lineDerivCLM_one_apply (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (x : ℝ) :
    (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ : 𝓓((⊤ : Opens ℝ), ℝ)) x
      = deriv (φ : ℝ → ℝ) x := by
  rw [TestFunction.lineDerivCLM_apply_of_le le_top,
    (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv,
    fderiv_apply_one_eq_deriv]

end PDE.Background.FunctionalAnalysis.DistributionPairing1D
