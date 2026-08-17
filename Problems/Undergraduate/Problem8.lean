import Mathlib
import PDE.Basics.Wave.WaveEnergyConservation1D

/-!
# Undergraduate Problem 8: Uniqueness by the Energy Method for `u_tt - c² u_xx = -2u`

Source: `pde_latex/problems/undergraduate/problem_8.tex` (Math 418, HW-3, Problem 5).

## Informal statement

> Use the energy method to show that the following equation has *at most* one
> classical solution:
> ```
>   u_tt - c² u_xx = -2u,   (x, t) ∈ ℝ × ℝ,
>   u(x, 0) = φ(x),   u_t(x, 0) = ψ(x),
> ```
> that is, if `u` is a classical solution to the above equation, then `u` must
> be unique. Here you can assume without proof that if the initial data are
> compactly supported, then the solution to the above equation is also
> compactly supported for each time.

## Semantic alignment

* "classical solution of `u_tt - c² u_xx = -2u`" — the library predicate
  `Wave.IsWaveSolution c 2 0 u` (`PDE/Basics/Wave/WaveEnergyConservation1D.lean`):
  joint `C²` regularity and `u_tt = c² u_xx - 2·u + 0` pointwise on `ℝ²`, i.e.
  the family `u_tt = c² u_xx - k·u + f` at `k = 2`, `f = 0`.
* "assume without proof … compactly supported for each time" — per the problem
  statement this propagation is a standing hypothesis, taken in the
  cone-support form the library uses: `Wave.HasConeSupport c R u`
  (`u x t = 0` for `|x| ≥ R + c|t|`), which is what compactly supported data
  yield via finite propagation speed.
* "at most one classical solution" — `uniqueness`: two solutions with the same
  initial data `φ`, `ψ` agree, `u₁ = u₂`. Same quantifiers as the source:
  `c > 0` and the data `φ`, `ψ` are arbitrary.
* The energy method itself (the hint's modified energy
  `E₂(t) = ½∫ u_t² + c² u_x² + 2u² dx`, its conservation, and the vanishing
  argument) lives in the reusable library theorem
  `Wave.uniqueness_energy_method`; this file instantiates it at `k = 2`.
-/

open Wave

namespace Problems.Undergraduate.Problem8

/-- **Problem 8: at most one classical solution** of
`u_tt - c² u_xx = -2u`, `u(x,0) = φ(x)`, `u_t(x,0) = ψ(x)` (with the
problem's standing compact-support assumption, in cone-support form):
two `C²` solutions with the same initial data coincide.

Instantiation of `Wave.uniqueness_energy_method` at `k = 2`, `f = 0`, using
the modified energy `E₂(t) = ½∫ u_t² + c² u_x² + 2u² dx`. -/
theorem uniqueness {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ} {u₁ u₂ : ℝ → ℝ → ℝ}
    (hu₁ : IsWaveSolution c 2 0 u₁) (hu₂ : IsWaveSolution c 2 0 u₂)
    {R₁ R₂ : ℝ} (hsupp₁ : HasConeSupport c R₁ u₁)
    (hsupp₂ : HasConeSupport c R₂ u₂)
    (hu₁0 : ∀ x, u₁ x 0 = φ x) (hu₂0 : ∀ x, u₂ x 0 = φ x)
    (hu₁t : ∀ x, dt u₁ x 0 = ψ x) (hu₂t : ∀ x, dt u₂ x 0 = ψ x) :
    u₁ = u₂ := by
  funext x t
  exact uniqueness_energy_method hc (by norm_num) hu₁ hu₂ hsupp₁ hsupp₂
    (fun x => (hu₁0 x).trans (hu₂0 x).symm)
    (fun x => (hu₁t x).trans (hu₂t x).symm) x t

end Problems.Undergraduate.Problem8
