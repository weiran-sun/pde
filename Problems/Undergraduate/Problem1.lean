import Mathlib
import PDE
import PDE.Basics.Wave.WaveGeneralSolution1D
import PDE.Basics.Wave.WaveIVP1D

/-!
# Undergraduate Problem 1: A Cauchy Problem for the 1D Wave Equation

Source: `pde_latex/problems/undergraduate/problem_1.tex`.

## Informal statement

> Consider the Cauchy problem
> ```
>   u_tt - c² u_xx = 0,   -∞ < x < ∞, t > 0,
>   u(x, 0) = sin x,      -∞ < x < ∞,
>   u_t(x, 0) = 0,        -∞ < x < ∞.
> ```
> a) Find a solution to the Cauchy problem and identify its forward and backward
>    waves.
> b) Show that the solution found in part (a) satisfies
>    `u(x, t + 2π/c) = u(x, t)`.

## Semantic alignment

* The Cauchy problem is formalized by the library predicate
  `Wave.IsSolutionWaveIVP1D c φ ψ u` (`PDE/Basics/Wave/WaveIVP1D.lean`) with data
  `φ = Real.sin`, `ψ = 0`: it packages joint `C²` regularity of `u`, the wave
  equation `u_tt = c² u_xx` on all of `ℝ²`, the initial displacement
  `u(x,0) = sin x`, and the initial velocity `u_t(x,0) = 0`. (As in the library,
  classical solutions are taken on all of `ℝ²` rather than `t > 0`; the wave
  equation is time reversible and the initial data are read off at `t = 0`.)
* "Find a solution" — `solution c x t = sin x * cos (c*t)`
  (`def solution`), which solves the Cauchy problem for `c > 0`
  (`solution_isSolutionWaveIVP1D`) and is the *only* classical solution
  (`solution_unique`), matching the informal proof's appeal to uniqueness via
  D'Alembert's formula (`Wave.IsSolutionWaveIVP1D.eq_dAlembert`).
* "Identify its forward and backward waves" — the decomposition
  `sin x * cos (c*t) = (1/2) sin (x + c*t) + (1/2) sin (x - c*t)`
  (`solution_eq_backwardWave_add_forwardWave`), stated through the library's
  `Wave.backwardWave c (fun s => sin s / 2)` (left-moving, profile `½ sin`) and
  `Wave.forwardWave c (fun s => sin s / 2)` (right-moving, profile `½ sin`),
  matching the informal identification of the forward wave `½ sin(x-ct)` and
  the backward wave `½ sin(x+ct)`.
* Part (b) — `solution_periodic`: for `c > 0`,
  `solution c x (t + 2*π/c) = solution c x t` for all `x t`, exactly the claimed
  `2π/c`-periodicity in time.
-/

open Real Wave

namespace Problems.Undergraduate.Problem1

/-- **The solution of Problem 1**: `u(x, t) = sin x * cos (c t)`. -/
noncomputable def solution (c : ℝ) : ℝ → ℝ → ℝ :=
  fun x t => Real.sin x * Real.cos (c * t)

/-- The D'Alembert expression for the data `φ = sin`, `ψ = 0` of Problem 1
collapses to `sin x * cos (c t)`: the integral term vanishes and
`sin (x + ct) + sin (x - ct) = 2 sin x cos (ct)`. -/
theorem dAlembert_sin_zero (c x t : ℝ) :
    Wave.dAlembert c Real.sin 0 x t = solution c x t := by
  have h : Real.sin (x + c * t) + Real.sin (x - c * t) =
      2 * (Real.sin x * Real.cos (c * t)) := by
    rw [Real.sin_add_sin]
    ring_nf
  simp only [Wave.dAlembert, solution, Pi.zero_apply,
    intervalIntegral.integral_zero, mul_zero, add_zero, h]
  ring

/-- **Part (a), existence**: for `c > 0`, `u(x, t) = sin x * cos (c t)` is a
classical solution of the Cauchy problem `u_tt = c² u_xx`, `u(x,0) = sin x`,
`u_t(x,0) = 0`. -/
theorem solution_isSolutionWaveIVP1D {c : ℝ} (hc : 0 < c) :
    Wave.IsSolutionWaveIVP1D c Real.sin 0 (solution c) := by
  have heq : Wave.dAlembert c Real.sin 0 = solution c := by
    funext x t
    exact dAlembert_sin_zero c x t
  have h := Wave.isSolutionWaveIVP1D_dAlembert (ψ := 0) hc Real.contDiff_sin
    contDiff_const
  rwa [heq] at h

/-- **Part (a), uniqueness**: for `c > 0`, every classical solution of the
Cauchy problem with data `φ = sin`, `ψ = 0` equals `sin x * cos (c t)`. -/
theorem solution_unique {c : ℝ} (hc : 0 < c) {u : ℝ → ℝ → ℝ}
    (hu : Wave.IsSolutionWaveIVP1D c Real.sin 0 u) (x t : ℝ) :
    u x t = solution c x t := by
  rw [hu.eq_dAlembert hc x t, dAlembert_sin_zero]

/-- **Part (a), forward and backward waves**: the solution is the superposition
of the backward (left-moving) wave `½ sin (x + ct)` and the forward
(right-moving) wave `½ sin (x - ct)`. -/
theorem solution_eq_backwardWave_add_forwardWave (c x t : ℝ) :
    solution c x t =
      Wave.backwardWave c (fun s => Real.sin s / 2) x t +
        Wave.forwardWave c (fun s => Real.sin s / 2) x t := by
  simp only [solution, Wave.backwardWave, Wave.forwardWave]
  have h : Real.sin (x + c * t) + Real.sin (x - c * t) =
      2 * (Real.sin x * Real.cos (c * t)) := by
    rw [Real.sin_add_sin]
    ring_nf
  linarith

/-- **Part (b)**: for `c > 0`, the solution is `2π/c`-periodic in time:
`u(x, t + 2π/c) = u(x, t)`. -/
theorem solution_periodic {c : ℝ} (hc : 0 < c) (x t : ℝ) :
    solution c x (t + 2 * π / c) = solution c x t := by
  have h : c * (t + 2 * π / c) = c * t + 2 * π := by
    field_simp
  simp only [solution, h, Real.cos_add_two_pi]

end Problems.Undergraduate.Problem1
