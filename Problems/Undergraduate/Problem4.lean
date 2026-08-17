import Mathlib
import PDE
import PDE.Basics.Wave.WaveIVPSource1D

/-!
# Undergraduate Problem 4: An Inhomogeneous Cauchy Problem for the 1D Wave Equation

Source: `pde_latex/problems/undergraduate/problem_4.tex`.

## Informal statement

> Find one solution to the problem
> ```
>   u_tt - u_xx = 1,   -∞ < x < ∞, t > 0,
>   u(x, 0) = x²,      -∞ < x < ∞,
>   u_t(x, 0) = 1,     -∞ < x < ∞.
> ```

## Semantic alignment

* The problem is formalized by the library predicate
  `PDE.Basics.Wave.WaveIVPSource1D.IsSolutionWaveIVPSource1D c f φ ψ u`
  (`PDE/Basics/Wave/WaveIVPSource1D.lean`) with `c = 1`, source `f = 1`,
  initial displacement `φ = fun s => s²`, and initial velocity `ψ = 1`: it
  packages joint `C²` regularity of `u`, the inhomogeneous wave equation
  `u_tt - c²u_xx = f` for `t > 0`, the initial displacement `u(x,0) = x²`,
  and the initial velocity `u_t(x,0) = 1` — exactly the three displayed
  conditions of the informal problem.
* "Find one solution" — `solution x t = x² + t + (3/2)t²` (`def solution`),
  the function the informal proof produces, and
  `solution_isSolutionWaveIVPSource1D` verifies it is a classical solution.
* The informal proof obtains this expression by evaluating the source-term
  extension of D'Alembert's formula (the library's
  `Wave.WaveIVPSource1D.dAlembertSource`) at the prescribed data; the
  evaluation of its three contributions to `x² + t²`, `t`, and `t²/2` is
  `dAlembertSource_eq`.
* `solution_unique` records the "since this expression is obtained from the
  general source-term solution formula" remark as an actual uniqueness
  statement: every classical solution agrees with `solution` for `t ≥ 0`,
  via the library theorem
  `Wave.WaveIVPSource1D.isSolution_eq_dAlembertSource` (Choksi Thm. 3.2).
-/

open Real MeasureTheory intervalIntegral PDE.Basics.Wave.WaveIVPSource1D

namespace Problems.Undergraduate.Problem4

/-- **The solution of Problem 4**: `u(x, t) = x² + t + (3/2)t²`. -/
noncomputable def solution : ℝ → ℝ → ℝ :=
  fun x t => x ^ 2 + t + 3 / 2 * t ^ 2

/-- The source-term D'Alembert expression for the data of Problem 4
(`c = 1`, `φ(s) = s²`, `ψ = 1`, `F = 1`) evaluates to `x² + t + (3/2)t²`:
its three contributions are `x² + t²`, `t`, and `t²/2`. -/
theorem dAlembertSource_eq (x t : ℝ) :
    dAlembertSource 1 (fun _ _ => 1) (fun s => s ^ 2) (fun _ => 1) x t
      = solution x t := by
  unfold dAlembertSource
  simp only [one_mul, mul_one]
  have hinner : ∀ s : ℝ,
      (∫ _y in (x - (t - s))..(x + (t - s)), (1 : ℝ)) = 2 * (t - s) := by
    intro s
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  have houter : (∫ s in (0 : ℝ)..t,
      ∫ _y in (x - (t - s))..(x + (t - s)), (1 : ℝ)) = t ^ 2 := by
    rw [intervalIntegral.integral_congr (g := fun s => 2 * (t - s))
      (fun s _ => hinner s)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  rw [houter, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  unfold solution
  ring

/-- **Problem 4**: `u(x, t) = x² + t + (3/2)t²` is a classical solution of
`u_tt - u_xx = 1`, `u(x,0) = x²`, `u_t(x,0) = 1`. -/
theorem solution_isSolutionWaveIVPSource1D :
    IsSolutionWaveIVPSource1D 1 (fun _ _ => 1) (fun s => s ^ 2) (fun _ => 1)
      solution := by
  -- time derivatives: `∂_t u = 1 + 3t`, `∂_tt u = 3`
  have hderivT : ∀ x : ℝ, deriv (solution x) = fun t => 1 + 3 * t := by
    intro x
    funext t
    have h1 : HasDerivAt (fun τ : ℝ => x ^ 2 + τ + 3 / 2 * τ ^ 2)
        (0 + 1 + 3 / 2 * (2 * t ^ 1)) t :=
      (((hasDerivAt_const t (x ^ 2)).add (hasDerivAt_id t)).add
        ((hasDerivAt_pow 2 t).const_mul (3 / 2)))
    have hval : (0 : ℝ) + 1 + 3 / 2 * (2 * t ^ 1) = 1 + 3 * t := by ring
    rw [hval] at h1
    exact h1.deriv
  have hderivTT : ∀ x t : ℝ, deriv (deriv (solution x)) t = 3 := by
    intro x t
    rw [hderivT x]
    have h2 : HasDerivAt (fun τ : ℝ => 1 + 3 * τ) (0 + 3 * 1) t :=
      (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul 3)
    have hval : (0 : ℝ) + 3 * 1 = 3 := by norm_num
    rw [hval] at h2
    exact h2.deriv
  -- space derivatives: `∂_x u = 2x`, `∂_xx u = 2`
  have hderivX : ∀ t : ℝ, deriv (fun z => solution z t) = fun y => 2 * y := by
    intro t
    funext y
    have h : HasDerivAt (fun z : ℝ => z ^ 2 + t + 3 / 2 * t ^ 2) (2 * y) y := by
      have h1 : HasDerivAt (fun z : ℝ => z ^ 2 + t + 3 / 2 * t ^ 2)
          (2 * y ^ 1) y :=
        ((hasDerivAt_pow 2 y).add_const t).add_const (3 / 2 * t ^ 2)
      simpa using h1
    exact h.deriv
  have hderivXX : ∀ t x : ℝ, deriv (fun y => deriv (fun z => solution z t) y) x = 2 := by
    intro t x
    rw [hderivX t]
    have h : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    exact h.deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- joint C² regularity: a polynomial in `(x, t)`
    have : Function.uncurry solution
        = fun p : ℝ × ℝ => p.1 ^ 2 + p.2 + 3 / 2 * p.2 ^ 2 := rfl
    rw [this]
    exact ((contDiff_fst.pow 2).add contDiff_snd).add
      (contDiff_const.mul (contDiff_snd.pow 2))
  · -- the PDE: `u_tt - 1² u_xx = 3 - 2 = 1`
    intro x t _
    rw [hderivTT x t, hderivXX t x]
    norm_num
  · -- initial displacement
    intro x
    simp [solution]
  · -- initial velocity
    intro x
    rw [hderivT x]
    norm_num

/-- **Uniqueness**: every classical solution of Problem 4 equals
`x² + t + (3/2)t²` for `t ≥ 0`, by D'Alembert's formula with a source term
(Choksi Theorem 3.2), evaluated at the data of the problem by
`dAlembertSource_eq`. -/
theorem solution_unique (v : ℝ → ℝ → ℝ)
    (hv : IsSolutionWaveIVPSource1D 1 (fun _ _ => 1) (fun s => s ^ 2)
      (fun _ => 1) v)
    (x t : ℝ) (ht : 0 ≤ t) : v x t = solution x t := by
  have h := isSolution_eq_dAlembertSource 1 one_pos (fun _ _ => 1)
    contDiff_const (fun s => s ^ 2) (fun _ => 1) v hv x t ht
  rw [h, dAlembertSource_eq]

end Problems.Undergraduate.Problem4
