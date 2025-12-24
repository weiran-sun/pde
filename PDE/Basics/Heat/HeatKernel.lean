import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The Heat Kernel and the 1D Heat Equation

## Main Definitions

* `heatKernel α x t`: The fundamental solution to the 1D heat equation with diffusivity `α`
* `heatK α`: Helper constant `4πα` appearing in the normalization
* `a α t`: Helper function `1/(4αt)` appearing in the exponential
* `c α t`: Normalization constant `1/√(4παt)`

## Main Results

* `heatKernel_pos`: The heat kernel is strictly positive for all `x` when `α > 0` and `t > 0`
* `integral_heatKernel_one_gaussian`: The heat kernel integrates to one (normalization property)
* `heatKernel_solves_heat_eq`: The heat kernel satisfies the heat equation `∂u/∂t = α ∂²u/∂x²`

## Reference

This formalization follows Chapter 7.2.1, ["Partial Differential Equations, A First Course"](https://bookstore.ams.org/amstext-54/) by Professor [Rustom Choksi](https://scholar.google.com/citations?user=Fk1zaTgAAAAJ&hl=en).

-/

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel



variable (α t : ℝ)

/-! ## Core Definitions -/

/-- The one-dimensional heat kernel (fundamental solution) with diffusivity `α`.

    For `α > 0` and `t > 0`, this function gives the temperature distribution at time `t`
    resulting from a unit point source at `x = 0` at time `t = 0`. -/

noncomputable def heatKernel (α : ℝ) (x t : ℝ) : ℝ :=
  (1 / Real.sqrt (4 * Real.pi * α * t)) * Real.exp (-(x^2) / (4 * α * t))


/-- Helper constant `k = 4πα` used in the normalization factor. -/
noncomputable def heatK (α : ℝ) : ℝ := 4 * Real.pi * α


/-- The coefficient `a(α,t) = 1/(4αt)` appearing in the exponential term. -/
@[simp]
noncomputable def a (α : ℝ) (t : ℝ) : ℝ := 1 / (4 * α * t)


/-- The normalization constant `c(α,t) = 1/√(4παt)`. -/
@[simp]
noncomputable def c (α : ℝ) (t : ℝ) : ℝ := 1 / Real.sqrt ((heatK α) * t)


/-! ## Basic Properties and Positivity -/

lemma heatK_pos {α : ℝ} (hα : α > 0) : heatK α > 0 := by
  unfold heatK; positivity


lemma a_pos {α t : ℝ} (hα : α > 0) (ht : t > 0) : a α t > 0 := by
  unfold a; positivity


lemma c_pos {α t : ℝ} (hα : α > 0) (ht : t > 0) : c α t > 0 := by
  unfold c heatK; positivity


/-- **Property 1**: The heat kernel is strictly positive for all `x` when `α > 0` and `t > 0`. -/
lemma heatKernel_pos {x : ℝ} (hα : 0 < α) (ht : 0 < t) :
    0 < heatKernel α x t := by
  unfold heatKernel
  positivity


/-! ## Normalization Property -/

/-- **Property 2**: The heat kernel integrates to one over all of ℝ.

    This shows that the heat kernel is properly normalized and can be interpreted
    as a probability density function (specifically, a Gaussian distribution). -/
lemma integral_heatKernel_one_gaussian (hα : 0 < α) (ht : 0 < t) :
    ∫ x : ℝ, heatKernel α x t = 1 := by
  let b := 1 / (4 * α * t)
  have b_pos : 0 < b := by positivity
  calc ∫ x : ℝ, heatKernel α x t
      = ∫ x : ℝ, (1 / Real.sqrt (Real.pi / b)) * Real.exp (-b * x^2) := by
          congr 1; funext x; simp [heatKernel, b, div_eq_mul_inv]; ring_nf
    _ = (1 / Real.sqrt (Real.pi / b)) * ∫ x : ℝ, Real.exp (-b * x^2) :=
          integral_const_mul _ _
    _ = (1 / Real.sqrt (Real.pi / b)) * Real.sqrt (Real.pi / b) := by
          rw [integral_gaussian b]
    _ = 1 := by field_simp [ne_of_gt b_pos]


/-! ## Derivative Lemmas

We establish the derivatives of the heat kernel with respect to both space and time variables.
These are needed to verify that the heat kernel satisfies the heat equation.
-/

section Derivatives

/-! ### Helper Lemmas for Derivatives -/

/-- Derivative of `1/√x` at a positive point. -/
lemma deriv_sqrt_inv {x : ℝ} (hx : x > 0) :
    HasDerivAt (fun τ => 1 / Real.sqrt τ)
                (-(1 / (2 * x)) * (1 / Real.sqrt x)) x := by
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt hx.ne.symm
  have hpos : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have := HasDerivAt.inv hsqrt hpos
  convert this using 1
  field_simp [hpos]
  · rfl
  · rw [Real.sq_sqrt hx.le]; field_simp [ne_of_gt hx]; ring


/-- Derivative of the exponential term `exp(-(x²)/(4αt))` with respect to `x`. -/
lemma deriv_exp_heatKernel {α t x : ℝ} (ht : 0 < t) (hα : 0 < α) :
    HasDerivAt (fun x' => Real.exp (-(x'^2) / (4 * α * t)))
                ((-(1 / (4 * α * t)) * (2 * x)) * Real.exp (-(x^2) / (4 * α * t))) x := by
  have hpow : HasDerivAt (fun x' : ℝ => x' ^ 2) (2 * x) x := by
    simpa [pow_two] using (hasDerivAt_pow (x := x) (n := 2))
  have hg : HasDerivAt (fun x' => -(x'^2) / (4 * α * t))
                        (-(1 / (4 * α * t)) * (2 * x)) x := by
    have := hpow.const_mul (-(1 / (4 * α * t)))
    convert this using 1; ext x'; field_simp
  simpa [mul_comm, mul_left_comm, mul_assoc, pow_two] using
    (Real.hasDerivAt_exp (x := (-(x^2) / (4 * α * t)))).comp x hg


/-! ### Time Derivative -/

/-- The time derivative of the heat kernel `∂/∂t heatKernel(α, x, t)`. -/
lemma hasDerivAt_heatKernel_t (hα : 0 < α) {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => heatKernel α x τ)
      ((-(1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * α * t))) *
         Real.exp (-(x^2) / (4 * α * t))
       + (1 / Real.sqrt (4 * Real.pi * α * t)) *
         ((1 / (4 * α)) * (1 / t^2) * x^2) * Real.exp (-(x^2) / (4 * α * t))) t := by
  unfold heatKernel

  -- Derivative of the prefactor 1/√(4παt) with respect to t
  have h_coef : HasDerivAt (fun τ => 1 / Real.sqrt (4 * Real.pi * α * τ))
                            (-(1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * α * t))) t := by
    have hg : HasDerivAt (fun τ ↦ 4 * Real.pi * α * τ) (4 * Real.pi * α) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * Real.pi * α)
    have hpos : 4 * Real.pi * α * t > 0 := by positivity
    have := (deriv_sqrt_inv hpos).comp t hg
    convert this using 1
    field_simp [ne_of_gt hpos]; ring_nf

  -- Derivative of the exponent -(x²)/(4ατ) with respect to t
  have h_inside : HasDerivAt (fun τ => -(x^2) / (4 * α * τ))
                              ((1 / (4 * α)) * (1 / t^2) * x^2) t := by
    have hexp1 : HasDerivAt (fun τ => τ⁻¹) (-(t^2)⁻¹) t := by
      simpa using hasDerivAt_inv (ne_of_gt ht)
    convert (hexp1.const_mul (-(x^2) / (4 * α))) using 1
    · ext τ; field_simp
    · field_simp

  -- Apply chain rule through the exponential
  have h_exp : HasDerivAt (fun τ => Real.exp (-(x^2) / (4 * α * τ)))
                          (((1 / (4 * α)) * (1 / t^2) * x^2) *
                           Real.exp (-(x^2) / (4 * α * t))) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp (x := (-(x^2) / (4 * α * t)))).comp t h_inside

  -- Apply product rule to combine the two parts
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_coef.mul h_exp


/-! ### First Spatial Derivative -/

/-- The first spatial derivative of the heat kernel `∂/∂x heatKernel(α, x, t)`. -/
lemma hasDerivAt_heatKernel_x {α t x : ℝ} (ht : 0 < t) (hα : 0 < α) :
    HasDerivAt (fun x' => heatKernel α x' t)
      ((1 / Real.sqrt (4 * Real.pi * α * t)) * (-(1 / (4 * α * t)) * (2 * x)) *
       Real.exp (-(x^2) / (4 * α * t))) x := by
  unfold heatKernel
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (deriv_exp_heatKernel ht hα).const_mul (1 / Real.sqrt (4 * Real.pi * α * t))


/-! ### Second Spatial Derivative -/

/-- Auxiliary lemma: derivative of the first spatial derivative's formula. -/
lemma hasDerivAt_heatKernel_x_x {α t x : ℝ} (ht : 0 < t) (hα : 0 < α) :
    HasDerivAt
      (fun x' => (1 / Real.sqrt (4 * Real.pi * α * t)) *
                 (-(1 / (4 * α * t)) * (2 * x')) *
                 Real.exp (-(x'^2) / (4 * α * t)))
      ((1 / Real.sqrt (4 * Real.pi * α * t)) *
        ((-(1 / (4 * α * t)) * 2) * Real.exp (-(x^2) / (4 * α * t))
         + (-(1 / (4 * α * t)) * (2 * x)) * (-(1 / (4 * α * t)) * (2 * x)) *
           Real.exp (-(x^2) / (4 * α * t)))) x := by
  have h1 : HasDerivAt (fun x' => (-(1 / (4 * α * t))) * (2 * x'))
                        (-(1 / (4 * α * t)) * 2) x := by
    simpa using ((hasDerivAt_id x).const_mul 2).const_mul (-(1 / (4 * α * t)))

  -- Apply product rule: f(x') * h(x') where f is linear and h is exponential
  have hprod : HasDerivAt
      (fun x' => ((-(1 / (4 * α * t))) * (2 * x')) * Real.exp (-(x'^2) / (4 * α * t)))
      ((-(1 / (4 * α * t)) * 2) * Real.exp (-(x^2) / (4 * α * t))
       + ((-(1 / (4 * α * t)) * (2 * x)) *
          ((-(1 / (4 * α * t)) * (2 * x)) * Real.exp (-(x^2) / (4 * α * t))))) x :=
    h1.mul (deriv_exp_heatKernel ht hα (x := x))

  -- Simplify the second term
  have hprod' : HasDerivAt
      (fun x' => (-(1 / (4 * α * t)) * (2 * x')) * Real.exp (-(x'^2) / (4 * α * t)))
      ((-(1 / (4 * α * t)) * 2) * Real.exp (-(x^2) / (4 * α * t))
       + (-(1 / (4 * α * t)) * (2 * x)) * (-(1 / (4 * α * t)) * (2 * x)) *
         Real.exp (-(x^2) / (4 * α * t))) x := by
    simpa [mul_assoc] using hprod

  simpa [mul_assoc] using hprod'.const_mul (1 / Real.sqrt (4 * Real.pi * α * t))


/-- The second spatial derivative of the heat kernel `∂²/∂x² heatKernel(α, x, t)`. -/
lemma hasDerivAt_heatKernel_xx {α t x : ℝ} (ht : 0 < t) (hα : 0 < α) :
    HasDerivAt
      (fun x' => deriv (fun x'' => heatKernel α x'' t) x')
      ((1 / Real.sqrt (4 * Real.pi * α * t)) *
        ((-(1 / (4 * α * t)) * 2) * Real.exp (-(x^2) / (4 * α * t))
         + (-(1 / (4 * α * t)) * (2 * x)) * (-(1 / (4 * α * t)) * (2 * x)) *
           Real.exp (-(x^2) / (4 * α * t)))) x := by
  have : deriv (fun x'' => heatKernel α x'' t) =
         fun x' => (1 / Real.sqrt (4 * Real.pi * α * t)) *
                   (-(1 / (4 * α * t)) * (2 * x')) *
                   Real.exp (-(x'^2) / (4 * α * t)) := by
    ext x'
    exact (hasDerivAt_heatKernel_x ht hα (x := x')).deriv
  rw [this]
  exact (hasDerivAt_heatKernel_x_x ht hα (x := x))

end Derivatives


/-! ## Main Theorem: The Heat Equation

The heat kernel satisfies the one-dimensional heat equation `∂u/∂t = α ∂²u/∂x²`.
This is the fundamental property that makes it the fundamental solution to the heat equation.
-/

/-- **Main Theorem**: The heat kernel satisfies the heat equation.

    For any `α > 0`, `t > 0`, and `x ∈ ℝ`, we have:
```
    ∂/∂t heatKernel(α, x, t) = α * ∂²/∂x² heatKernel(α, x, t)
```

    This establishes that the heat kernel is indeed the fundamental solution
    to the one-dimensional heat equation. -/

theorem heatKernel_solves_heat_eq (hα : 0 < α) {t x : ℝ} (ht : 0 < t) :
    deriv (fun τ => heatKernel α x τ) t
      = α * deriv (fun x' => deriv (fun x'' => heatKernel α x'' t) x') x := by
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have ht_ne : t ≠ 0 := ne_of_gt ht
  rw [(hasDerivAt_heatKernel_t α hα ht).deriv, (hasDerivAt_heatKernel_xx ht hα).deriv]
  field_simp [hα_ne, ht_ne]
  ring_nf


/-! ## Property 4: Convergence to Dirac Delta

As `t → 0⁺`, the heat kernel `heatKernel(α, x, t)` concentrates at the origin and
converges to the Dirac delta distribution `δ₀` in the sense of distributions.

More precisely, for any test funciton φ(x)
```
lim_{t → 0⁺} ∫ heatKernel(α, x, t) · φ(x) dx = φ(0)
```

This property explains why the heat kernel serves as the fundamental solution:
it represents the evolution of an initial point source of heat at `x = 0`.

**Formal proof**: See Section [7.2.3] for the complete formalization of this convergence result.
-/


end HeatKernel
