import Mathlib

/-!
# The Initial Value Problem for the 2D Wave Equation: Solution Formula

This file formalizes the solution formula for the initial value problem for the
wave equation in two space dimensions,

  `u_tt = c² Δu`,  `u(𝐱, 0) = φ(𝐱)`,  `u_t(𝐱, 0) = ψ(𝐱)`,  `𝐱 ∈ ℝ²`,

following Rustum Choksi's *Partial Differential Equations: A First Course*
(Theorem 4.2). The solution is given by the 2D Poisson expression

  `u(𝐱,t) = (2 / 4πct) ∬_{B(𝐱, ct)} (φ(𝐲) + ∇φ(𝐲)·(𝐲-𝐱) + t ψ(𝐲))
            / √(c²t² - |𝐲-𝐱|²) d𝐲`,

an integral over the *solid* disk `B(𝐱, ct)` — in contrast with Kirchhoff's
formula in 3D, which integrates over a sphere. The informal proof is the
*method of descent*: extend the data trivially to `ℝ³`, apply Kirchhoff's
formula, and evaluate the resulting sphere integral by parametrizing the two
hemispheres over their common projection, the disk `B(𝐱, ct)`.

## Main declarations

* `Wave.IsSolutionWaveIVP2D` — the classical-solution predicate for the 2D
  whole-space IVP.
* `Wave.poisson2D` — the 2D Poisson expression (the right-hand side of the
  solution formula).
* `Wave.IsSolutionWaveIVP2D.eq_poisson2D` — Theorem 4.2: every classical
  solution with smooth data is given by the 2D Poisson expression.

## Conventions

Space is `EuclideanSpace ℝ (Fin 2)`; functions of space-time are curried,
`u : EuclideanSpace ℝ (Fin 2) → ℝ → ℝ` with time as the second argument, and
time derivatives are one-variable `deriv`s with the space point frozen —
matching the convention of the 1D wave files. The spatial Laplacian is
Mathlib's `InnerProductSpace` Laplacian `Δ`, and `∇φ` is Mathlib's `gradient`.
Classical solutions are taken jointly `C²` on all of
`EuclideanSpace ℝ (Fin 2) × ℝ`, with the PDE imposed for `t > 0` and the data
read off at `t = 0`, as in the 1D IVP files.

## Reference

Theorem 4.2, ["Partial Differential Equations, A First Course"](https://bookstore.ams.org/amstext-54/)
by Rustum Choksi.
-/

open Real MeasureTheory InnerProductSpace Laplacian
open scoped RealInnerProductSpace

namespace Wave

/-- The plane `ℝ²` as a Euclidean space. -/
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- `u` is a classical solution of the initial value problem for the 2D wave
equation on the whole plane with wave speed `c`, initial displacement `φ`, and
initial velocity `ψ`:

  `u_tt = c² Δu` for `t > 0`,  `u(𝐱, 0) = φ(𝐱)`,  `u_t(𝐱, 0) = ψ(𝐱)`.

Here `u x t` is the displacement at the point `x ∈ ℝ²` and time `t`, `u` is
required to be `C²` jointly in `(x, t)`, and `Δ` is the spatial Laplacian. -/
structure IsSolutionWaveIVP2D (c : ℝ) (φ ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (u : EuclideanSpace ℝ (Fin 2) → ℝ → ℝ) : Prop where
  /-- The solution is twice continuously differentiable jointly in `(x, t)`. -/
  contDiff : ContDiff ℝ 2 (Function.uncurry u)
  /-- The wave equation `u_tt = c² Δu` holds for positive times. -/
  waveEq : ∀ (x : EuclideanSpace ℝ (Fin 2)) (t : ℝ), 0 < t →
    deriv (deriv (u x)) t = c ^ 2 * Δ (fun y => u y t) x
  /-- Initial displacement: `u(𝐱, 0) = φ(𝐱)`. -/
  initPos : ∀ x : EuclideanSpace ℝ (Fin 2), u x 0 = φ x
  /-- Initial velocity: `u_t(𝐱, 0) = ψ(𝐱)`. -/
  initVel : ∀ x : EuclideanSpace ℝ (Fin 2), deriv (u x) 0 = ψ x

/-- **The 2D Poisson expression.** For wave speed `c`, initial displacement `φ`,
and initial velocity `ψ`, this is the right-hand side of the solution formula
for the 2D wave equation (Choksi (4.23)):

  `(2 / 4πct) ∬_{B(𝐱, ct)} (φ(𝐲) + ∇φ(𝐲)·(𝐲-𝐱) + t ψ(𝐲)) / √(c²t² - |𝐲-𝐱|²) d𝐲`,

a Lebesgue ("bulk") integral over the solid open disk of radius `ct`
centered at `𝐱`. -/
noncomputable def poisson2D (c : ℝ) (φ ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ℝ :=
  (2 / (4 * π * c * t)) *
    ∫ y in Metric.ball x (c * t),
      (φ y + ⟪gradient φ y, y - x⟫ + t * ψ y) / Real.sqrt (c ^ 2 * t ^ 2 - ‖y - x‖ ^ 2)

/-- **Solution formula for the 2D wave equation** (Choksi, Theorem 4.2).
If `c > 0`, the data `φ, ψ` are smooth, and `u` is a classical solution of the
initial value problem for the 2D wave equation, then for every `𝐱 ∈ ℝ²` and
`t > 0`,

  `u(𝐱,t) = (2 / 4πct) ∬_{B(𝐱, ct)} (φ(𝐲) + ∇φ(𝐲)·(𝐲-𝐱) + t ψ(𝐲))
            / √(c²t² - |𝐲-𝐱|²) d𝐲`.

The informal proof is the method of descent from Kirchhoff's formula in 3D. -/
theorem IsSolutionWaveIVP2D.eq_poisson2D {c : ℝ} (hc : 0 < c)
    {φ ψ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {u : EuclideanSpace ℝ (Fin 2) → ℝ → ℝ} (hu : IsSolutionWaveIVP2D c φ ψ u)
    (x : EuclideanSpace ℝ (Fin 2)) {t : ℝ} (ht : 0 < t) :
    u x t = poisson2D c φ ψ x t := by
  sorry

end Wave
