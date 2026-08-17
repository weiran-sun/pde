/-
Copyright (c) 2025. All rights reserved.
Formalization of the orthonormal basis of sine functions on [0, pi].

The system {sqrt(2/pi) * sin(nx)}_{n >= 1} forms an orthonormal basis of L^2([0, pi]).
These are eigenfunctions of -d^2/dx^2 with Dirichlet boundary conditions.

Reference: Choksi, "Partial Differential Equations, A First Course", AMS 2022.
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace PDE.Background.FunctionalAnalysis.OrthonormalBasis

/-! # Orthonormal Basis: Sine System on [0, pi]

We establish that the normalized sine system forms an orthonormal basis of L^2([0, pi]).

## Main results

* `sin_mul_sin` — product-to-sum identity for sine
* `integral_cos_npi` — integral of cos(nx) over [0, pi] vanishes for n ≠ 0
* `integral_one_pi` — integral of 1 over [0, pi] equals pi
* `sin_orthogonal` — orthogonality of sin(mx) and sin(nx) for m ≠ n
* `sin_norm` — integral of sin^2(nx) over [0, pi] equals pi/2
* `sinBasis` — the normalized sine basis functions
* `sinBasis_orthonormal` — orthonormality of the sine system
* `sinBasis_complete` — completeness of the sine system in L^2([0, pi])
-/

/-- Product-to-sum identity: sin(a) * sin(b) = (cos(a - b) - cos(a + b)) / 2. -/
theorem sin_mul_sin (a b : ℝ) :
    sin a * sin b = (cos (a - b) - cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- The integral of cos(nx) over [0, pi] vanishes for any nonzero integer n. -/
theorem integral_cos_npi (n : ℤ) (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..π, cos (n * x) = 0 := by
  have hc : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  rw [intervalIntegral.integral_comp_mul_left Real.cos hc, integral_cos]
  simp [Real.sin_int_mul_pi]

/-- The integral of 1 over [0, pi] equals pi. -/
theorem integral_one_pi :
    ∫ x in (0 : ℝ)..π, (1 : ℝ) = π := by
  simp

/-- Orthogonality: for distinct positive integers m ≠ n,
    the integral of sin(mx) * sin(nx) over [0, pi] vanishes. -/
theorem sin_orthogonal (m n : ℕ+) (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..π, sin (m * x) * sin (n * x) = 0 := by
  have hz : ((m : ℤ)) ≠ (n : ℤ) := by exact_mod_cast hmn
  have hsub : ((m : ℤ) - n) ≠ 0 := sub_ne_zero.mpr hz
  have hadd : ((m : ℤ) + n) ≠ 0 := by positivity
  have h1 : ∫ x in (0 : ℝ)..π, cos (((m : ℝ) - n) * x) = 0 := by
    have := integral_cos_npi ((m : ℤ) - n) hsub
    push_cast at this
    exact this
  have h2 : ∫ x in (0 : ℝ)..π, cos (((m : ℝ) + n) * x) = 0 := by
    have := integral_cos_npi ((m : ℤ) + n) hadd
    push_cast at this
    exact this
  have key : ∀ x : ℝ, sin ((m : ℝ) * x) * sin ((n : ℝ) * x) =
      (cos (((m : ℝ) - n) * x) - cos (((m : ℝ) + n) * x)) / 2 := by
    intro x
    rw [sin_mul_sin, ← sub_mul, ← add_mul]
  have hint1 : IntervalIntegrable (fun x => cos (((m : ℝ) - n) * x)) volume 0 π :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 π
  have hint2 : IntervalIntegrable (fun x => cos (((m : ℝ) + n) * x)) volume 0 π :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 π
  simp only [key]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hint1 hint2, h1, h2]
  ring

/-- The L² norm squared: integral of sin²(nx) over [0, pi] equals pi/2. -/
theorem sin_norm (n : ℕ+) :
    ∫ x in (0 : ℝ)..π, sin (n * x) ^ 2 = π / 2 := by
  have h2n : ((2 * n : ℤ)) ≠ 0 := by positivity
  have hc : ∫ x in (0 : ℝ)..π, cos ((2 * (n : ℝ)) * x) = 0 := by
    have := integral_cos_npi (2 * n) h2n
    push_cast at this
    exact this
  have key : ∀ x : ℝ, sin ((n : ℝ) * x) ^ 2 =
      1 / 2 - cos ((2 * (n : ℝ)) * x) / 2 := by
    intro x
    rw [Real.sin_sq, Real.cos_sq, mul_assoc]; ring
  have hint1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 2) volume 0 π :=
    intervalIntegrable_const
  have hint2 : IntervalIntegrable (fun x => cos ((2 * (n : ℝ)) * x) / 2) volume 0 π :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).div_const 2).intervalIntegrable 0 π
  simp only [key]
  have h2 : ∫ x in (0 : ℝ)..π, cos (2 * (n : ℝ) * x) / 2 = 0 := by
    rw [intervalIntegral.integral_div, hc]; norm_num
  rw [intervalIntegral.integral_sub hint1 hint2, h2,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The normalized sine basis function: e_n(x) = sqrt(2/pi) * sin(nx). -/
def sinBasis (n : ℕ+) (x : ℝ) : ℝ :=
  Real.sqrt (2 / π) * sin (n * x)

/-- The sine system {sqrt(2/pi) * sin(nx)}_{n >= 1} is orthonormal in L^2([0, pi]). -/
theorem sinBasis_orthonormal :
    ∀ m n : ℕ+, ∫ x in (0 : ℝ)..π, sinBasis m x * sinBasis n x =
      if m = n then 1 else 0 := by
  intro m n
  have hs : Real.sqrt (2 / π) * Real.sqrt (2 / π) = 2 / π :=
    Real.mul_self_sqrt (by positivity)
  have key : ∀ x : ℝ, sinBasis m x * sinBasis n x =
      (2 / π) * (sin ((m : ℝ) * x) * sin ((n : ℝ) * x)) := by
    intro x
    unfold sinBasis
    rw [mul_mul_mul_comm, hs]
  simp only [key]
  rw [intervalIntegral.integral_const_mul]
  by_cases h : m = n
  · subst h
    rw [if_pos rfl]
    have hnorm : ∫ x in (0 : ℝ)..π, sin ((m : ℝ) * x) * sin ((m : ℝ) * x) = π / 2 := by
      simpa [pow_two] using sin_norm m
    rw [hnorm]
    field_simp
  · rw [if_neg h, sin_orthogonal m n h, mul_zero]

/-- The sine system is complete in L^2([0, pi]): if f is orthogonal to all
    basis functions, then f = 0 a.e. -/
theorem sinBasis_complete
    (f : ℝ → ℝ) (hf : Integrable f (volume.restrict (Icc 0 π)))
    (horth : ∀ n : ℕ+, ∫ x in (0 : ℝ)..π, f x * sinBasis n x = 0) :
    f =ᵐ[volume.restrict (Icc 0 π)] 0 := by
  sorry

end PDE.Background.FunctionalAnalysis.OrthonormalBasis
