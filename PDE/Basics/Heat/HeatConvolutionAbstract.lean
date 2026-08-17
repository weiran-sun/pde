import Mathlib

/-!
# Convolution solves the heat equation (computation–free version)

We work in `ℝ` and set
`U Φ g x t = ∫ y, Φ (x - y) t * g y`.

The hypotheses are exactly the ones that a textbook proof uses:
- you can differentiate under the integral in `t` (once) and in `x` (twice);
- the kernel `Φ` itself satisfies `Φ_t = κ Φ_xx` (at the time we care about).

No explicit formula for `Φ` is used anywhere.

Migrated from `Section_7.lean`.

## Status: intentionally standalone

Nothing in `PDE/` imports this module. That is deliberate, not an oversight. The
concrete Gaussian result, `heat_from_convolution_heatKernel` in
`PDE.Basics.Heat.HeatSolution`, carries its own self-contained proof and discharges the
`swap_*` hypotheses below via `swap_t_heatKernel` / `swap_x_heatKernel` /
`swap_xx_heatKernel`. This file is kept as a statement of the argument's skeleton,
reusable for other fundamental solutions (Poisson, wave, Schrödinger), since `Φ` here is
a bare variable carrying no analytic content.

Should a future kernel want to instantiate `heat_from_convolution` directly, note that
the concrete definitions already align *definitionally* — no bridge lemmas are needed.
Each of the following holds by `rfl` (verified):

* `HKt α x t = Φt (heatKernel α) x t`
* `HKx α x t = Φx (heatKernel α) x t`
* `HKxx α x t = Φxx (heatKernel α) x t`
* `heatConvolutionHK α g x t = U (heatKernel α) g x t`

The one wrinkle is quantifier shape: the `swap_*` hypotheses below are stated `∀ x t`,
whereas the `swap_*_heatKernel` lemmas fix `t` under a hypothesis `0 < t`.
-/

noncomputable section
open scoped Real
open scoped Topology
open MeasureTheory
open Filter

namespace Heat

variable {κ : ℝ} {Φ : ℝ → ℝ → ℝ} {g : ℝ → ℝ}

/-- The solution candidate. -/
def U (Φ : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (x t : ℝ) : ℝ :=
  ∫ y, Φ (x - y) t * g y

/-- Shorthands for the partial derivatives of `Φ`. -/
def Φt (Φ : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ := deriv (fun τ => Φ x τ) t
def Φx (Φ : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ := deriv (fun ξ => Φ ξ t) x
def Φxx (Φ : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ := deriv (fun x' => Φx Φ x' t) x

/--
**Abstract verification** that `U Φ g` satisfies the heat equation `u_t = κ u_xx`
at a given point `(x₀, t₀)`, using only:
* `swap_t`, `swap_x`, `swap_xx`: differentiation can be moved inside the integral;
* `Φ_solves_heat`: the kernel solves `Φ_t = κ Φ_xx` pointwise in space at time `t₀`.

No explicit form of `Φ` is used.
-/

theorem heat_from_convolution
  (swap_t :
    ∀ x t,
      HasDerivAt
        (fun τ => ∫ y, Φ (x - y) τ * g y)
        (∫ y, Φt Φ (x - y) t * g y) t)
  (swap_x :
    ∀ t x,
      HasDerivAt
        (fun x' => ∫ y, Φ (x' - y) t * g y)
        (∫ y, Φx Φ (x - y) t * g y) x)
  (swap_xx :
    ∀ t x,
      HasDerivAt
        (fun x' => ∫ y, Φx Φ (x' - y) t * g y)
        (∫ y, Φxx Φ (x - y) t * g y) x)
  (Φ_solves_heat : ∀ x t, Φt Φ x t = κ * Φxx Φ x t) :
  ∀ x t,
    deriv (fun τ => U Φ g x τ) t
      = κ * deriv (fun x' => deriv (fun x'' => U Φ g x'' t) x') x := by
  intro x t
  classical
  -- u_t(x,t)
  have hut :
      deriv (fun τ => U Φ g x τ) t
        = ∫ y, Φt Φ (x - y) t * g y := by
    simpa [U, Φt] using (swap_t x t).deriv

  -- identify u_x(·,t) as a function of x
  have hDx :
      (fun x' => deriv (fun z => U Φ g z t) x')
        = (fun x' => ∫ y, Φx Φ (x' - y) t * g y) := by
    funext x'
    simpa [U, Φx] using (swap_x t x').deriv

  -- differentiate that function at x
  have hDx_at :
      deriv (fun x' => deriv (fun z => U Φ g z t) x') x
        = deriv (fun x' => ∫ y, Φx Φ (x' - y) t * g y) x := by
    simpa using congrArg (fun f : ℝ → ℝ => deriv f x) hDx

  -- compute that derivative via the second swap
  have hx :
      deriv (fun x' => ∫ y, Φx Φ (x' - y) t * g y) x
        = ∫ y, Φxx Φ (x - y) t * g y := by
    simpa [Φx, Φxx] using (swap_xx t x).deriv

  -- name u_xx(x,t)
  have huxx :
      deriv (fun x' => deriv (fun z => U Φ g z t) x') x
        = ∫ y, Φxx Φ (x - y) t * g y := hDx_at.trans hx

  -- finish: substitute the kernel PDE inside the integrand and pull κ out
  calc
    deriv (fun τ => U Φ g x τ) t
        = ∫ y, Φt Φ (x - y) t * g y := hut
    _   = ∫ y, κ * (Φxx Φ (x - y) t * g y) := by
            -- pointwise Φ_t = κ Φ_xx, then multiply by g y and integrate
            have hpt :
                (fun y : ℝ => Φt Φ (x - y) t * g y)
              = (fun y : ℝ => κ * (Φxx Φ (x - y) t * g y)) := by
              funext y
              simpa [mul_left_comm, mul_assoc]
                using congrArg (fun r => r * g y) (Φ_solves_heat (x - y) t)
            simpa using congrArg (fun f : ℝ → ℝ => ∫ y, f y) hpt
    _   = κ * ∫ y, Φxx Φ (x - y) t * g y := by
            simpa [smul_eq_mul] using
              (integral_smul (c := κ)
                (f := fun y : ℝ => Φxx Φ (x - y) t * g y))
    _   = κ * deriv (fun x' => deriv (fun z => U Φ g z t) x') x := by
            simp [huxx]

def heatConvolution (Φ : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (x t : ℝ) : ℝ :=
  U Φ g x t

end Heat
