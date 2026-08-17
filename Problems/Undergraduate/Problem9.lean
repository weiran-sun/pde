import Mathlib
import PDE
import PDE.Basics.Wave.WaveIVPSource1D

/-!
# Undergraduate Problem 9: Duhamel's Principle and the Half-Line Problem

Source: `pde_latex/problems/undergraduate/problem_9.tex` (Math 418, HW-4,
Problem 1).

## Informal statement

> (a) Prove Duhamel's principle for the 1-dimensional inhomogeneous wave
> equation: let `u(x, t) = ∫_0^t U(x, t-s, s) ds`, where `U(x, τ, s)` is a
> classical solution to `U_ττ - c² U_xx = 0`, `U(x, 0, s) = 0`,
> `U_τ(x, 0, s) = f(x, s)`. Then `u` is a solution to
> `u_tt - c² u_xx = f(x, t)`, `u(x, 0) = 0`, `u_t(x, 0) = 0`.
>
> (b) Find a solution to `u_tt - c² u_xx = f(x, t)`, `x > 0`, `t > 0`,
> `u(x, 0) = φ(x)`, `u_t(x, 0) = ψ(x)` for `x > 0`, `u(0, t) = h(t)`,
> for `f ∈ C¹(ℝ×ℝ)` and `φ, ψ, h ∈ C²(ℝ)`.
>
> (c) What are the necessary conditions on `φ, ψ, h` such that the solution
> obtained in (b) is in `C²([0,∞) × [0,∞))`?

## Semantic alignment

* **Part (a)** is exactly the library theorem
  `PDE.Basics.Wave.WaveIVPSource1D.duhamel_principle`
  (`PDE/Basics/Wave/WaveIVPSource1D.lean`); `duhamel` below is its thin
  restatement, proved by direct application. `U` is curried as
  `U : ℝ → ℝ → ℝ → ℝ` with `U x τ s`; jointly `C²` regularity formalizes
  "nice enough such that the interchange of derivatives and integrals holds",
  the homogeneous wave equation in `(x, τ)` and the `τ = 0` data are the
  three displayed conditions, and the conclusion — that
  `u(x,t) = ∫_0^t U(x, t-s, s) ds` solves the inhomogeneous problem with
  zero data — is packaged by the library predicate
  `IsSolutionWaveIVPSource1D c f 0 0 u`.
* **Part (b)**: `solution` is the assembled two-branch formula of the
  informal solution (`u = w + v + η`, superposition of the reflected source
  response, the odd-reflection D'Alembert wave, and the boundary wave
  `h(t - x/c)`), with the two regions `x ≥ ct` (undisturbed by the boundary)
  and `0 < x < ct` (influenced by the boundary) distinguished exactly as in
  the informal summary display. `IsSolutionHalfLineIBVP` packages the four
  displayed conditions of the informal problem: `C²` regularity on the open
  quadrant, the inhomogeneous wave equation there, the initial data for
  `x > 0`, and the Dirichlet boundary data for `t ≥ 0`. The main theorem
  `isSolutionHalfLineIBVP_solution` states that the formula solves the
  problem, under the corner compatibility conditions of part (c) and the
  odd-extension matching conditions `φ(0) = φ''(0) = ψ(0) = 0` used by the
  reflection argument.
* **Part (c)**: `compatibility_of_contDiff` — if a classical solution is
  `C²` through the corner `(0,0)` of the closed quadrant, then
  `h(0) = φ(0)`, `h'(0) = ψ(0)`, `h''(0) = c²φ''(0) + f(0,0)`, matching the
  informal three-level trace argument (continuity gives the zeroth-order
  match, `C¹` matches `u_t` along the two boundary axes, and `C²` plus the
  PDE gives the second-order condition).

## Conventions

Functions of space-time are curried, `u : ℝ → ℝ → ℝ` with `u x t`; partial
derivatives use `Wave.xderiv` / `Wave.tderiv` (`WaveGeneralSolution1D`),
matching `Wave.IsSolutionWaveBVP1D`.
-/

open MeasureTheory intervalIntegral Real Set Wave
open PDE.Basics.Wave.WaveIVPSource1D

noncomputable section

namespace Problems.Undergraduate.Problem9

/-- **Problem 9(a): Duhamel's principle for the 1D wave equation.**
Let `c > 0` and let `U x τ s` be jointly `C²` with, for each fixed `s`, a
solution of the homogeneous wave equation in `(x, τ)` with data
`U(x, 0, s) = 0`, `U_τ(x, 0, s) = f(x, s)`. Then
`u(x, t) = ∫_0^t U(x, t-s, s) ds` is a classical solution of
`u_tt - c² u_xx = f` with `u(x, 0) = u_t(x, 0) = 0`.

Thin restatement of the library theorem
`PDE.Basics.Wave.WaveIVPSource1D.duhamel_principle`. -/
theorem duhamel (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ → ℝ)
    (U : ℝ → ℝ → ℝ → ℝ)
    (hU : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2))
    (hUeq : ∀ s x τ, deriv (deriv (fun σ => U x σ s)) τ
      = c ^ 2 * deriv (fun y => deriv (fun z => U z τ s) y) x)
    (hU0 : ∀ s x, U x 0 s = 0)
    (hU1 : ∀ s x, deriv (fun σ => U x σ s) 0 = f x s) :
    IsSolutionWaveIVPSource1D c f (fun _ => 0) (fun _ => 0)
      (fun x t => ∫ s in (0 : ℝ)..t, U x (t - s) s) :=
  duhamel_principle c hc f U hU hUeq hU0 hU1

/-- **The Problem 9(b) solution formula.** The superposition `u = w + v + η`
of the source response, the odd-reflection D'Alembert wave, and the boundary
wave, written out as a two-branch piecewise formula:

* for `x ≥ ct` (undisturbed by the boundary):
  `½[φ(x+ct) + φ(x-ct)] + (1/2c)∫_{x-ct}^{x+ct} ψ
    + (1/2c)∫_0^t ∫_{x-c(t-s)}^{x+c(t-s)} f(y,s) dy ds`;
* for `0 < x < ct` (influenced by the boundary):
  `½[φ(x+ct) - φ(ct-x)] + (1/2c)∫_{ct-x}^{ct+x} ψ + h(t - x/c)
    + (1/2c)∫_0^{t-x/c} ∫_{c(t-s)-x}^{c(t-s)+x} f(y,s) dy ds
    + (1/2c)∫_{t-x/c}^t ∫_{x-c(t-s)}^{x+c(t-s)} f(y,s) dy ds`. -/
def solution (c : ℝ) (f : ℝ → ℝ → ℝ) (φ ψ h : ℝ → ℝ) (x t : ℝ) : ℝ :=
  if c * t ≤ x then
    (φ (x + c * t) + φ (x - c * t)) / 2
      + (1 / (2 * c)) * (∫ s in (x - c * t)..(x + c * t), ψ s)
      + (1 / (2 * c)) *
          (∫ s in (0 : ℝ)..t,
            (∫ y in (x - c * (t - s))..(x + c * (t - s)), f y s))
  else
    (φ (x + c * t) - φ (c * t - x)) / 2
      + (1 / (2 * c)) * (∫ s in (c * t - x)..(c * t + x), ψ s)
      + h (t - x / c)
      + (1 / (2 * c)) *
          (∫ s in (0 : ℝ)..(t - x / c),
            (∫ y in (c * (t - s) - x)..(c * (t - s) + x), f y s))
      + (1 / (2 * c)) *
          (∫ s in (t - x / c)..t,
            (∫ y in (x - c * (t - s))..(x + c * (t - s)), f y s))

/-- `u` is a classical solution of the half-line initial-boundary value
problem with source `f`, initial data `φ, ψ`, and Dirichlet boundary data
`h`:

  `u_tt - c² u_xx = f(x,t)` for `x > 0`, `t > 0`;
  `u(x, 0) = φ(x)`, `u_t(x, 0) = ψ(x)` for `x > 0`;
  `u(0, t) = h(t)` for `t ≥ 0`;

with `u` of class `C²` on the open quadrant `(0,∞) × (0,∞)`. -/
structure IsSolutionHalfLineIBVP (c : ℝ) (f : ℝ → ℝ → ℝ) (φ ψ h : ℝ → ℝ)
    (u : ℝ → ℝ → ℝ) : Prop where
  /-- `u` is `C²` on the open quadrant `(0,∞) × (0,∞)`. -/
  contDiffOn : ContDiffOn ℝ 2 (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioi 0)
  /-- The inhomogeneous wave equation holds in the open quadrant. -/
  waveEq : ∀ x t : ℝ, 0 < x → 0 < t →
    tderiv (tderiv u) x t - c ^ 2 * xderiv (xderiv u) x t = f x t
  /-- Initial displacement: `u(x, 0) = φ(x)` for `x > 0`. -/
  init : ∀ x : ℝ, 0 < x → u x 0 = φ x
  /-- Initial velocity: `u_t(x, 0) = ψ(x)` for `x > 0`. -/
  initVel : ∀ x : ℝ, 0 < x → tderiv u x 0 = ψ x
  /-- Dirichlet boundary data: `u(0, t) = h(t)` for `t ≥ 0`. -/
  boundary : ∀ t : ℝ, 0 ≤ t → u 0 t = h t

/-- **Problem 9(b): the formula solves the half-line problem.** For `c > 0`,
`f ∈ C¹(ℝ²)`, `φ, ψ, h ∈ C²(ℝ)`, under the corner compatibility conditions
`h(0) = φ(0)`, `h'(0) = ψ(0)`, `h''(0) = c²φ''(0) + f(0,0)` and the
odd-extension matching conditions `φ(0) = φ''(0) = 0`, `ψ(0) = 0`, the
piecewise formula `solution` is a classical solution of the half-line
initial-boundary value problem. -/
theorem isSolutionHalfLineIBVP_solution (c : ℝ) (hc : 0 < c)
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 1 (Function.uncurry f))
    (φ ψ h : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) (hh : ContDiff ℝ 2 h)
    (hcomp0 : h 0 = φ 0) (hcomp1 : deriv h 0 = ψ 0)
    (hcomp2 : deriv (deriv h) 0 = c ^ 2 * deriv (deriv φ) 0 + f 0 0)
    (hφ0 : φ 0 = 0) (hφ2 : deriv (deriv φ) 0 = 0) (hψ0 : ψ 0 = 0) :
    IsSolutionHalfLineIBVP c f φ ψ h (solution c f φ ψ h) := by
  sorry

/-- **Problem 9(c): necessity of the corner compatibility conditions.**
If `u` is a classical solution of the half-line problem whose restriction to
the closed quadrant `[0,∞) × [0,∞)` is `C²` (through the corner `(0,0)`),
with `f` continuous and `φ, ψ, h` twice continuously differentiable at `0`,
then

  `h(0) = φ(0)`, `h'(0) = ψ(0)`, `h''(0) = c²φ''(0) + f(0,0)`. -/
theorem compatibility_of_contDiff (c : ℝ) (hc : 0 < c)
    (f : ℝ → ℝ → ℝ) (hf : Continuous (Function.uncurry f))
    (φ ψ h : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hu : IsSolutionHalfLineIBVP c f φ ψ h u)
    (hreg : ContDiffOn ℝ 2 (Function.uncurry u) (Set.Ici 0 ×ˢ Set.Ici 0))
    (hφ : ContDiffAt ℝ 2 φ 0) (hψ : ContDiffAt ℝ 2 ψ 0)
    (hh : ContDiffAt ℝ 2 h 0) :
    h 0 = φ 0 ∧ deriv h 0 = ψ 0 ∧
      deriv (deriv h) 0 = c ^ 2 * deriv (deriv φ) 0 + f 0 0 := by
  sorry

end Problems.Undergraduate.Problem9
