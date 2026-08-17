/-
Copyright (c) 2026. All rights reserved.
Formalization of the 1D wave equation with a source term.

The inhomogeneous initial value problem on the whole line,

  u_tt - c² u_xx = f(x, t),   u(x, 0) = φ(x),   u_t(x, 0) = ψ(x),

is solved by the source-term extension of D'Alembert's formula

  u(x,t) = ½[φ(x+ct) + φ(x-ct)] + (1/2c) ∫_{x-ct}^{x+ct} ψ(s) ds
           + (1/2c) ∬_D f(y,τ) dy dτ,

where D is the domain of dependence of (x, t): the triangle with top point
(x, t) and base points (x ± ct, 0).  Duhamel's principle produces the
zero-data solution of the inhomogeneous problem as a time integral of a
family of homogeneous solutions.

Reference: Choksi, "Partial Differential Equations, A First Course",
AMS 2022, Section 3.6 (Theorem 3.2, Duhamel's Principle).
Source LaTeX: pde_latex/PDE/Basics/Wave/WaveIVPSource1D.tex
-/
import Mathlib

open MeasureTheory Real Set intervalIntegral

noncomputable section

namespace PDE.Basics.Wave.WaveIVPSource1D

/-! # The 1D wave equation with a source term

## Main declarations

* `IsSolutionWaveIVPSource1D` — classical solution predicate for the
  inhomogeneous whole-line IVP `u_tt - c²u_xx = f`, `u(·,0) = φ`,
  `u_t(·,0) = ψ`.
* `dependenceTriangle` — the domain of dependence of the point `(x, t)`.
* `dAlembertSource` — the source-term extension of D'Alembert's formula.
* `integral_dependenceTriangle` — the double integral over the domain of
  dependence as an iterated interval integral.
* `isSolution_eq_dAlembertSource` — Theorem 3.2: every classical solution
  is given by the extended D'Alembert formula.
* `duhamel_principle` — Duhamel's principle for the 1D wave equation, in
  the form `u(x,t) = ∫_0^t U(x, t-s, s) ds`.

## Conventions

Functions of space-time are curried, `u : ℝ → ℝ → ℝ` with `u x t`; time is
the second argument.  Partial derivatives are expressed with `deriv` in one
variable while the other is frozen, matching the convention of
`PDE.Basics.Heat`.  Classical regularity is imposed as joint `C²`
smoothness on all of `ℝ × ℝ` (the standard extension of "C² on the closed
upper half-plane" used throughout this library); the PDE itself is only
required where the informal problem poses it, `t > 0`.
-/

/-- `u` is a classical solution of the whole-line initial value problem for
the 1D wave equation with source term `f`, initial displacement `φ` and
initial velocity `ψ`:

  `u_tt - c² u_xx = f(x,t)` for `t > 0`,  `u(x,0) = φ(x)`,  `u_t(x,0) = ψ(x)`. -/
structure IsSolutionWaveIVPSource1D (c : ℝ) (f : ℝ → ℝ → ℝ) (φ ψ : ℝ → ℝ)
    (u : ℝ → ℝ → ℝ) : Prop where
  /-- `u` is twice continuously differentiable jointly in `(x, t)`. -/
  contDiff : ContDiff ℝ 2 (Function.uncurry u)
  /-- The inhomogeneous wave equation holds for positive times. -/
  waveEq : ∀ x t, 0 < t →
    deriv (deriv (u x)) t
      - c ^ 2 * deriv (fun y => deriv (fun z => u z t) y) x = f x t
  /-- Initial displacement. -/
  init : ∀ x, u x 0 = φ x
  /-- Initial velocity. -/
  initVel : ∀ x, deriv (u x) 0 = ψ x

/-- The domain of dependence of the point `(x, t)` for propagation speed `c`:
the closed triangle in the `(y, τ)` plane with top vertex `(x, t)` and base
points `(x - ct, 0)`, `(x + ct, 0)`. -/
def dependenceTriangle (c x t : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ t ∧
    x - c * (t - p.2) ≤ p.1 ∧ p.1 ≤ x + c * (t - p.2)}

/-- The source-term extension of D'Alembert's formula (Choksi (3.11)):

  `½[φ(x+ct) + φ(x-ct)] + (1/2c)∫_{x-ct}^{x+ct} ψ + (1/2c)∬_D f`,

with the double integral over the domain of dependence written as an
iterated interval integral. -/
def dAlembertSource (c : ℝ) (f : ℝ → ℝ → ℝ) (φ ψ : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (φ (x + c * t) + φ (x - c * t)) / 2
    + (1 / (2 * c)) * (∫ s in (x - c * t)..(x + c * t), ψ s)
    + (1 / (2 * c)) *
        (∫ s in (0 : ℝ)..t, ∫ y in (x - c * (t - s))..(x + c * (t - s)), f y s)

/-- The double integral of a continuous function over the domain of
dependence equals the iterated interval integral appearing in
`dAlembertSource` (Fubini over the triangle). -/
theorem integral_dependenceTriangle (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f)) (x t : ℝ) (ht : 0 ≤ t) :
    ∫ p in dependenceTriangle c x t, f p.1 p.2
      = ∫ s in (0 : ℝ)..t, ∫ y in (x - c * (t - s))..(x + c * (t - s)), f y s := by
  sorry

/-- **Theorem 3.2 (D'Alembert's formula with a source term).**
If `u` is a classical solution of the inhomogeneous initial value problem

  `u_tt - c² u_xx = f`, `u(x,0) = φ(x)`, `u_t(x,0) = ψ(x)`,

with `c > 0` and `f ∈ C¹`, then for every `t ≥ 0`

  `u(x,t) = ½[φ(x+ct) + φ(x-ct)] + (1/2c)∫_{x-ct}^{x+ct} ψ + (1/2c)∬_D f`,

where `D` is the domain of dependence of `(x, t)`. -/
theorem isSolution_eq_dAlembertSource (c : ℝ) (hc : 0 < c)
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 1 (Function.uncurry f))
    (φ ψ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hu : IsSolutionWaveIVPSource1D c f φ ψ u)
    (x t : ℝ) (ht : 0 ≤ t) :
    u x t = dAlembertSource c f φ ψ x t := by
  sorry

/-- **Duhamel's principle for the 1D wave equation.**
Let `U x τ s` be, for each fixed `s`, a solution of the homogeneous wave
equation in the variables `(x, τ)` with "initial" data at `τ = 0`

  `U(x, 0, s) = 0`,  `U_τ(x, 0, s) = f(x, s)`.

Then `u(x, t) = ∫_0^t U(x, t - s, s) ds` is a classical solution of the
inhomogeneous problem `u_tt - c² u_xx = f` with zero initial displacement
and velocity.

(Choksi states this with `w(x, t; s) := U(x, t - s, s)`, which solves the
wave equation for `t > s` with data prescribed at `t = s`; the two forms
are equivalent, and this is the form used by problem 9.) -/
theorem duhamel_principle (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ → ℝ)
    (U : ℝ → ℝ → ℝ → ℝ)
    (hU : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2))
    (hUeq : ∀ s x τ, deriv (deriv (fun σ => U x σ s)) τ
      = c ^ 2 * deriv (fun y => deriv (fun z => U z τ s) y) x)
    (hU0 : ∀ s x, U x 0 s = 0)
    (hU1 : ∀ s x, deriv (fun σ => U x σ s) 0 = f x s) :
    IsSolutionWaveIVPSource1D c f (fun _ => 0) (fun _ => 0)
      (fun x t => ∫ s in (0 : ℝ)..t, U x (t - s) s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- joint C² smoothness of (x,t) ↦ ∫_0^t U(x, t-s, s) ds
    sorry
  · -- the inhomogeneous wave equation for t > 0
    intro x t ht
    sorry
  · -- u(x,0) = 0 : the integral over [0,0] vanishes
    intro x
    simp
  · -- u_t(x,0) = 0
    intro x
    sorry

end PDE.Basics.Wave.WaveIVPSource1D
