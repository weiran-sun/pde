import Mathlib
import PDE
import PDE.Basics.Heat.HeatKernel

/-!
# Undergraduate Problem 16: Uniform Gaussian Bounds on All Derivatives of the Heat Kernel

Source: `pde_latex/problems/undergraduate/problem_16.tex` (Math 418/718, HW-6, Problem 3).

## Informal statement

> Suppose `t > δ₀ > 0`. Prove that for any given `α, β ∈ ℕ ∪ {0}`, there exists
> a constant `C(α, β, δ₀)` such that
> `|∂ₓ^α ∂ₜ^β K(x, t)| ≤ C(α, β, δ₀) e^{-x²/(8t)}` for all `x ∈ ℝ`, `t > δ₀`,
> where `K(x, t) = (4πt)^{-1/2} e^{-x²/(4t)}` is the heat kernel.

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem16.tex`:

* The problem's kernel `K(x, t) = (4πt)^{-1/2} e^{-x²/(4t)}` is the project's
  general one-dimensional heat kernel
  `Heat.heatKernel α x t = (1/√(4παt)) · exp(-(x²)/(4αt))`
  (`PDE/Basics/Heat/HeatKernel.lean`, blueprint `def:heatKernel-1d`)
  instantiated at diffusivity `α = 1`.
* The mixed derivative `∂ₓ^α ∂ₜ^β K` is spelled with iterated one-variable
  derivatives of slice functions, matching the library convention:
  `iteratedDeriv m (fun x' ↦ iteratedDeriv n (fun t' ↦ heatKernel 1 x' t') t) x`
  — the inner `iteratedDeriv n` differentiates the time slice `t' ↦ K x' t'`
  at `t`, and the outer `iteratedDeriv m` differentiates the resulting
  function of `x'` at `x`. (Here `m, n` are the source's derivative orders
  `α, β`; the letter `α` is reserved for the diffusivity in the library.)
* The existence of `C(α, β, δ₀)` is stated as `∃ C, 0 < C ∧ …` with the bound
  quantified over all `x : ℝ` and all `t > δ₀`, exactly the source's uniform
  half-plane bound. The theorem is the `α = 1` instance of the general
  uniform mixed-derivative bound `Heat.heatKernel_mixed_deriv_bound`
  (blueprint `lem:heatKernel-mixed-deriv-bound`), whose exponent
  `x²/(8·α·t)` at `α = 1` is exactly the problem's `x²/(8t)`.
-/

open Heat

namespace Problems.Undergraduate.Problem16

/-- **Problem 16** (blueprint `thm:problem16-deriv-bound`): Gaussian bound on
all mixed derivatives of the heat kernel, uniform over the half-plane
`t > δ₀`. For `K = Heat.heatKernel 1` (the heat kernel at diffusivity `1`)
and any derivative orders `m` (in `x`) and `n` (in `t`), there is a constant
`C = C(m, n, δ₀) > 0` with
`|∂ₓ^m ∂ₜ^n K(x, t)| ≤ C · exp(-x²/(8t))` for all `x ∈ ℝ` and `t > δ₀`. -/
theorem heatKernel_deriv_bound {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (m n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x t : ℝ, δ₀ < t →
      |iteratedDeriv m (fun x' ↦ iteratedDeriv n (fun t' ↦ heatKernel 1 x' t') t) x|
        ≤ C * Real.exp (-x ^ 2 / (8 * t)) := by
  obtain ⟨C, hC0, hC⟩ := heatKernel_mixed_deriv_bound one_pos hδ₀ m n
  refine ⟨C + 1, by positivity, fun x t hδt ↦ ?_⟩
  have h := hC x t hδt
  rw [show (8 : ℝ) * 1 * t = 8 * t by ring] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

end Problems.Undergraduate.Problem16
