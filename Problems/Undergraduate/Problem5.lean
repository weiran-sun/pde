import Mathlib
import PDE
import PDE.Basics.Wave.WaveIVP1D

/-!
# Undergraduate Problem 5: An Explicit D'Alembert Computation

Source: `pde_latex/problems/undergraduate/problem_5.tex` (Math 418, HW-2, Problem 1).

## Informal statement

> Solve
> ```
>   u_tt - 4 u_xx = 0,
>   u(x, 0) = log(1 + x²),
>   u_t(x, 0) = 4 + x.
> ```
> Simplify your answer and check that it does satisfy the equation and the
> initial data.

## Semantic alignment

* The IVP is the whole-line wave Cauchy problem with `c = 2` (so `c² = 4`),
  `φ(x) = log(1 + x²)`, `ψ(x) = 4 + x`, formalized by the library predicate
  `Wave.IsSolutionWaveIVP1D 2 φ ψ u` (`PDE/Basics/Wave/WaveIVP1D.lean`): joint
  `C²` regularity, `u_tt = 2² u_xx` on all of `ℝ²`, and the two initial
  conditions read off at `t = 0`. (As in the library, classical solutions are
  taken on all of `ℝ²` rather than `t > 0`; the wave equation is time
  reversible.)
* "Solve … simplify your answer" — `solution x t =
  ½ log((1 + (x+2t)²)(1 + (x-2t)²)) + 4t + xt` (`def solution`), the simplified
  closed form obtained from D'Alembert's formula; `dAlembert_eq` records that
  the D'Alembert expression `Wave.dAlembert 2 φ ψ` equals this simplified form
  (the log algebra `log a + log b = log (ab)` plus the interval integral of the
  linear function `4 + s`).
* "check that it does satisfy the equation and the initial data" —
  `solution_isSolutionWaveIVP1D : Wave.IsSolutionWaveIVP1D 2 φ ψ solution`.
* Uniqueness (implicit in "Solve", and proved in the source via D'Alembert's
  formula) — `solution_unique`: every classical solution equals `solution`,
  via `Wave.IsSolutionWaveIVP1D.eq_dAlembert` and `dAlembert_eq`.
-/

open Real Wave

namespace Problems.Undergraduate.Problem5

/-- The initial displacement of Problem 5: `φ(x) = log (1 + x²)`. -/
noncomputable def φ : ℝ → ℝ := fun x => Real.log (1 + x ^ 2)

/-- The initial velocity of Problem 5: `ψ(x) = 4 + x`. -/
def ψ : ℝ → ℝ := fun x => 4 + x

/-- **The simplified solution of Problem 5**:
`u(x, t) = ½ log((1 + (x + 2t)²)(1 + (x - 2t)²)) + 4t + xt`. -/
noncomputable def solution : ℝ → ℝ → ℝ := fun x t =>
  (1 / 2) * Real.log ((1 + (x + 2 * t) ^ 2) * (1 + (x - 2 * t) ^ 2))
    + 4 * t + x * t

/-- **Evaluation of the D'Alembert expression**: for the data `c = 2`,
`φ(x) = log (1 + x²)`, `ψ(x) = 4 + x`, the D'Alembert expression simplifies to
`solution`. The displacement half combines the two logarithms via
`log a + log b = log (ab)` (both factors are `≥ 1 > 0`), and the velocity half
is the interval integral `¼ ∫_{x-2t}^{x+2t} (4 + s) ds = 4t + xt`. -/
theorem dAlembert_eq (x t : ℝ) :
    Wave.dAlembert 2 φ ψ x t = solution x t := by
  have ha : (0 : ℝ) < 1 + (x + 2 * t) ^ 2 := by positivity
  have hb : (0 : ℝ) < 1 + (x - 2 * t) ^ 2 := by positivity
  have hlog : Real.log ((1 + (x + 2 * t) ^ 2) * (1 + (x - 2 * t) ^ 2)) =
      Real.log (1 + (x + 2 * t) ^ 2) + Real.log (1 + (x - 2 * t) ^ 2) :=
    Real.log_mul ha.ne' hb.ne'
  have hint : (∫ s in (x - 2 * t)..(x + 2 * t), ψ s) = 16 * t + 4 * (x * t) := by
    simp only [ψ]
    rw [intervalIntegral.integral_add intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const,
      integral_id]
    simp only [smul_eq_mul]
    ring
  simp only [Wave.dAlembert, φ, solution, hint, hlog]
  ring

/-- The initial displacement `φ(x) = log (1 + x²)` is `C²` (indeed smooth,
since `1 + x² > 0` everywhere). -/
theorem contDiff_φ : ContDiff ℝ 2 φ := by
  have h : ContDiff ℝ 2 fun x : ℝ => 1 + x ^ 2 := by fun_prop
  exact h.log fun x => by positivity

/-- The initial velocity `ψ(x) = 4 + x` is `C¹`. -/
theorem contDiff_ψ : ContDiff ℝ 1 ψ := by
  unfold ψ; fun_prop

/-- **The simplified solution solves the IVP** (the "check" the problem
requests): `solution` is a classical solution of `u_tt = 4 u_xx`,
`u(x,0) = log (1 + x²)`, `u_t(x,0) = 4 + x`. -/
theorem solution_isSolutionWaveIVP1D :
    Wave.IsSolutionWaveIVP1D 2 φ ψ solution := by
  have heq : Wave.dAlembert 2 φ ψ = solution := by
    funext x t
    exact dAlembert_eq x t
  have h := Wave.isSolutionWaveIVP1D_dAlembert (c := 2) (by norm_num)
    contDiff_φ contDiff_ψ
  rwa [heq] at h

/-- **Uniqueness**: every classical solution of the IVP of Problem 5 equals
the simplified solution. -/
theorem solution_unique {u : ℝ → ℝ → ℝ}
    (hu : Wave.IsSolutionWaveIVP1D 2 φ ψ u) (x t : ℝ) :
    u x t = solution x t := by
  rw [hu.eq_dAlembert (by norm_num) x t, dAlembert_eq]

end Problems.Undergraduate.Problem5
