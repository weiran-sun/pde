import Mathlib
import PDE
import PDE.Basics.Wave.WaveIVPSource1D

/-!
# Undergraduate Problem 3: An Inhomogeneous Cauchy Problem for the 1D Wave Equation

Source: `pde_latex/problems/undergraduate/problem_3.tex`.

## Informal statement

> Find one solution to the problem
> ```
>   u_tt - u_xx = xt,     -∞ < x < ∞, t > 0,
>   u(x, 0) = 0,          -∞ < x < ∞,
>   u_t(x, 0) = eˣ,       -∞ < x < ∞.
> ```

## Semantic alignment

* The inhomogeneous Cauchy problem is formalized by the library predicate
  `PDE.Basics.Wave.WaveIVPSource1D.IsSolutionWaveIVPSource1D c f φ ψ u`
  (`PDE/Basics/Wave/WaveIVPSource1D.lean`) with wave speed `c = 1`, source
  `f = fun x t => x * t`, initial displacement `φ = 0`, and initial velocity
  `ψ = Real.exp`: it packages joint `C²` regularity of `u`, the inhomogeneous
  wave equation `u_tt - c²u_xx = f x t` for `t > 0`, the initial displacement
  `u(x,0) = 0`, and the initial velocity `u_t(x,0) = eˣ` — exactly the three
  displayed conditions of the informal problem.
* "Find one solution" — `solution x t = eˣ sinh t + x t³ / 6` (`def solution`),
  which solves the problem (`solution_isSolutionWaveIVPSource1D`, the main
  theorem answering the informal question).
* The informal proof obtains the solution by evaluating the source-term
  extension of D'Alembert's formula with `c = 1`, `φ = 0`, `ψ(s) = eˢ`,
  `F(y,τ) = yτ`. The two computations of that evaluation are formalized as
  `velocityTerm_eq` (the initial-velocity term `½∫_{x-t}^{x+t} eˢ ds = eˣ sinh t`)
  and `sourceTerm_eq` (the source term
  `½∫₀ᵗ ∫_{x-(t-τ)}^{x+(t-τ)} yτ dy dτ = ½∫₀ᵗ 2xτ(t-τ) dτ = xt³/6`),
  matching the informal computation line by line.
* As in the informal proof's closing remark ("obtained from the general
  source-term solution formula with exactly the prescribed data"), the
  formula characterizes the solution: `eq_solution_of_isSolution` states that
  every classical solution agrees with `solution` for `t ≥ 0`.

## Note on the library formula (resolved)

An earlier revision of `PDE.Basics.Wave.WaveIVPSource1D.dAlembertSource`
elaborated with the source term *inside* the integrand of the `ψ`-integral;
this was fixed in iter-002 by explicit parenthesization, and the evaluation
lemmas `velocityTerm_eq` and `sourceTerm_eq` now combine (in
`eq_solution_of_isSolution`) into
`dAlembertSource 1 (fun y τ => y*τ) (fun _ => 0) Real.exp x t = solution x t`.
-/

open Real PDE.Basics.Wave.WaveIVPSource1D

namespace Problems.Undergraduate.Problem3

/-- **The solution of Problem 3**: `u(x, t) = eˣ sinh t + x t³ / 6`. -/
noncomputable def solution : ℝ → ℝ → ℝ :=
  fun x t => Real.exp x * Real.sinh t + x * t ^ 3 / 6

/-- The initial-velocity term of the source-term D'Alembert formula for the
data of Problem 3: `½ ∫_{x-t}^{x+t} eˢ ds = eˣ sinh t`. -/
theorem velocityTerm_eq (x t : ℝ) :
    (1 / 2 : ℝ) * ∫ s in (x - t)..(x + t), Real.exp s
      = Real.exp x * Real.sinh t := by
  rw [integral_exp, Real.sinh_eq, Real.exp_add, Real.exp_sub, Real.exp_neg]
  ring

/-- The source term of the source-term D'Alembert formula for the data of
Problem 3: the inner integral is `∫_{x-(t-τ)}^{x+(t-τ)} yτ dy = 2xτ(t-τ)`,
so `½ ∫₀ᵗ ∫_{x-(t-τ)}^{x+(t-τ)} yτ dy dτ = ½ ∫₀ᵗ 2xτ(t-τ) dτ = xt³/6`. -/
theorem sourceTerm_eq (x t : ℝ) :
    (1 / 2 : ℝ) * ∫ τ in (0 : ℝ)..t,
        (∫ y in (x - (t - τ))..(x + (t - τ)), y * τ)
      = x * t ^ 3 / 6 := by
  have hinner : ∀ τ : ℝ,
      (∫ y in (x - (t - τ))..(x + (t - τ)), y * τ)
        = 2 * x * t * τ - 2 * x * τ ^ 2 := by
    intro τ
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  rw [intervalIntegral.integral_congr
    (g := fun τ => 2 * x * t * τ - 2 * x * τ ^ 2) (fun τ _ => hinner τ)]
  rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun τ : ℝ => 2 * x * t * τ).intervalIntegrable 0 t)
      ((by fun_prop : Continuous fun τ : ℝ => 2 * x * τ ^ 2).intervalIntegrable 0 t),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_id, integral_pow]
  ring

/-- Time derivative of the solution: `u_t(x, t) = eˣ cosh t + x t² / 2`. -/
theorem hasDerivAt_solution_time (x t : ℝ) :
    HasDerivAt (solution x) (Real.exp x * Real.cosh t + x * t ^ 2 / 2) t := by
  have h1 : HasDerivAt (fun τ : ℝ => Real.exp x * Real.sinh τ)
      (Real.exp x * Real.cosh t) t := (Real.hasDerivAt_sinh t).const_mul _
  have h2 : HasDerivAt (fun τ : ℝ => x * τ ^ 3 / 6) (x * t ^ 2 / 2) t := by
    have h := ((hasDerivAt_pow 3 t).const_mul x).div_const 6
    norm_num at h
    have he : x * (3 * t ^ 2) / 6 = x * t ^ 2 / 2 := by ring
    rwa [he] at h
  exact h1.add h2

/-- Spatial derivative of the solution: `u_x(x, t) = eˣ sinh t + t³ / 6`. -/
theorem hasDerivAt_solution_space (t x : ℝ) :
    HasDerivAt (fun z => solution z t) (Real.exp x * Real.sinh t + t ^ 3 / 6)
      x := by
  have h1 : HasDerivAt (fun z : ℝ => Real.exp z * Real.sinh t)
      (Real.exp x * Real.sinh t) x := (Real.hasDerivAt_exp x).mul_const _
  have h2 : HasDerivAt (fun z : ℝ => z * t ^ 3 / 6) (t ^ 3 / 6) x := by
    have h := ((hasDerivAt_id x).mul_const (t ^ 3)).div_const 6
    have he : 1 * t ^ 3 / 6 = t ^ 3 / 6 := by ring
    rwa [he] at h
  exact h1.add h2

/-- **The main theorem (existence)**: `u(x, t) = eˣ sinh t + x t³ / 6` is a
classical solution of the Cauchy problem `u_tt - u_xx = xt`, `u(x,0) = 0`,
`u_t(x,0) = eˣ`. -/
theorem solution_isSolutionWaveIVPSource1D :
    IsSolutionWaveIVPSource1D 1 (fun x t => x * t) (fun _ => 0) Real.exp
      solution := by
  constructor
  · -- joint C² regularity
    have : Function.uncurry solution
        = fun p : ℝ × ℝ => Real.exp p.1 * Real.sinh p.2 + p.1 * p.2 ^ 3 / 6 :=
      rfl
    rw [this]
    fun_prop
  · -- the wave equation `u_tt - u_xx = x t` for `t > 0`
    intro x t _
    have ht : deriv (solution x) = fun τ => Real.exp x * Real.cosh τ + x * τ ^ 2 / 2 :=
      funext fun τ => (hasDerivAt_solution_time x τ).deriv
    have htt : deriv (deriv (solution x)) t = Real.exp x * Real.sinh t + x * t := by
      rw [ht]
      have h1 : HasDerivAt (fun τ : ℝ => Real.exp x * Real.cosh τ)
          (Real.exp x * Real.sinh t) t := (Real.hasDerivAt_cosh t).const_mul _
      have h2 : HasDerivAt (fun τ : ℝ => x * τ ^ 2 / 2) (x * t) t := by
        have h := ((hasDerivAt_pow 2 t).const_mul x).div_const 2
        norm_num at h
        have he : x * (2 * t) / 2 = x * t := by ring
        rwa [he] at h
      exact (h1.add h2).deriv
    have hx : (fun y => deriv (fun z => solution z t) y)
        = fun y => Real.exp y * Real.sinh t + t ^ 3 / 6 :=
      funext fun y => (hasDerivAt_solution_space t y).deriv
    have hxx : deriv (fun y => deriv (fun z => solution z t) y) x
        = Real.exp x * Real.sinh t := by
      rw [hx]
      have h := ((Real.hasDerivAt_exp x).mul_const (Real.sinh t)).add_const
        (t ^ 3 / 6)
      rw [h.deriv]
    rw [htt, hxx]
    ring
  · -- initial displacement `u(x, 0) = 0`
    intro x
    simp [solution]
  · -- initial velocity `u_t(x, 0) = eˣ`
    intro x
    rw [(hasDerivAt_solution_time x 0).deriv]
    simp

/-- **Uniqueness**: every classical solution of the Cauchy problem of
Problem 3 agrees with `eˣ sinh t + x t³ / 6` for `t ≥ 0`.

The proof appeals to the source-term extension of D'Alembert's formula
(`isSolution_eq_dAlembertSource`) and evaluates the resulting expression
with `velocityTerm_eq` and `sourceTerm_eq`. -/
theorem eq_solution_of_isSolution {u : ℝ → ℝ → ℝ}
    (hu : IsSolutionWaveIVPSource1D 1 (fun x t => x * t) (fun _ => 0)
      Real.exp u) (x t : ℝ) (ht : 0 ≤ t) :
    u x t = solution x t := by
  have hf : ContDiff ℝ 1 (Function.uncurry fun y τ : ℝ => y * τ) :=
    contDiff_fst.mul contDiff_snd
  have h := isSolution_eq_dAlembertSource 1 one_pos _ hf _ _ u hu x t ht
  -- `h : u x t = dAlembertSource 1 (fun y τ => y * τ) (fun _ => 0) Real.exp x t`.
  -- The right-hand side is `0 + ½∫ψ + ½∬f`, which evaluates via
  -- `velocityTerm_eq` and `sourceTerm_eq` to `solution x t`.
  rw [h]
  simp only [dAlembertSource, one_mul, mul_one, solution]
  have hv := velocityTerm_eq x t
  have hs := sourceTerm_eq x t
  linarith [hv, hs]

end Problems.Undergraduate.Problem3
