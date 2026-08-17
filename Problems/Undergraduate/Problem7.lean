import Mathlib
import PDE
import PDE.Basics.Wave.WaveIVP1D

/-!
# Undergraduate Problem 7: Odd Data Give Odd Solutions

Source: `pde_latex/problems/undergraduate/problem_7.tex` (Math 418, HW-2, Problem 5).

## Informal statement

> Suppose `u` is a classical solution to the wave equation
> ```
>   u_tt - c² u_xx = 0,
>   u(x, 0) = φ(x),
>   u_t(x, 0) = ψ(x).
> ```
> (a) Prove that if `φ` and `ψ` are both odd functions of `x`, then the solution
> to the wave equation `u` is also odd in `x` for each `t`, by using the
> d'Alembert formula.
> (b) Give another proof of (a) by using the uniqueness of the solution to the
> above initial-value problem for the wave equation. In this proof you will
> study the equation without explicitly solving it.
> Hint: what does `u(-x,t)` satisfy? What does `-u(-x,t)` satisfy?

## Semantic alignment

* "Classical solution to the wave equation with data `φ, ψ`" is the library
  predicate `Wave.IsSolutionWaveIVP1D c φ ψ u`
  (`PDE/Basics/Wave/WaveIVP1D.lean`): joint `C²` regularity on `ℝ²`,
  `u_tt = c² u_xx` everywhere, and the initial conditions at `t = 0`.
* "Odd function" is Mathlib's `Function.Odd` (`f (-x) = -f x` for all `x`).
* "`u` is odd in `x` for each `t`" is `∀ x t, u (-x) t = -u x t`.
* Part (a) — `solution_odd_of_eq_dAlembert`, proved by rewriting `u` as the
  D'Alembert expression (`Wave.IsSolutionWaveIVP1D.eq_dAlembert`) and applying
  the algebraic oddness of that expression (`dAlembert_odd`, the substitution
  `z = -s` in the velocity integral).
* Part (b) — `solution_odd_of_unique`, proved without solving the equation:
  `w(x,t) = -u(-x,t)` is a classical solution with data `-φ(-·) = φ`,
  `-ψ(-·) = ψ` (`isSolutionWaveIVP1D_neg_reflect`, the chain-rule computation
  from the hint), so `u = w` by uniqueness
  (`Wave.IsSolutionWaveIVP1D.unique`).
-/

open Wave

namespace Problems.Undergraduate.Problem7

/-- **Oddness of the D'Alembert expression.** If the initial displacement `φ` and
the initial velocity `ψ` are odd, then the D'Alembert expression is odd in `x`
for each `t`. The displacement half is the oddness of `φ` at `x ± ct`; the
velocity half is the substitution `z = -s` in the interval integral together
with the oddness of `ψ`. -/
theorem dAlembert_odd {c : ℝ} {φ ψ : ℝ → ℝ} (hφ : Function.Odd φ)
    (hψ : Function.Odd ψ) (x t : ℝ) :
    Wave.dAlembert c φ ψ (-x) t = -Wave.dAlembert c φ ψ x t := by
  have e1 : -x + c * t = -(x - c * t) := by ring
  have e2 : -x - c * t = -(x + c * t) := by ring
  have hint : (∫ s in (-x - c * t)..(-x + c * t), ψ s)
      = -∫ s in (x - c * t)..(x + c * t), ψ s := by
    rw [e1, e2, ← intervalIntegral.integral_comp_neg]
    simp_rw [hψ.eq]
    exact intervalIntegral.integral_neg
  simp only [Wave.dAlembert]
  rw [hint, e1, e2, hφ.eq, hφ.eq]
  ring

/-- **Part (a): oddness via D'Alembert's formula.** If `φ` and `ψ` are odd and
`u` is a classical solution of the whole-line wave IVP, then `u` is odd in `x`
for each `t`. Proof: `u` equals the D'Alembert expression
(`Wave.IsSolutionWaveIVP1D.eq_dAlembert`), which is odd (`dAlembert_odd`). -/
theorem solution_odd_of_eq_dAlembert {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ}
    (hφ : Function.Odd φ) (hψ : Function.Odd ψ) {u : ℝ → ℝ → ℝ}
    (hu : Wave.IsSolutionWaveIVP1D c φ ψ u) (x t : ℝ) :
    u (-x) t = -u x t := by
  rw [hu.eq_dAlembert hc, hu.eq_dAlembert hc, dAlembert_odd hφ hψ]

/-- **The reflected function is a solution.** If `u` is a classical solution of
the whole-line wave IVP with data `φ, ψ`, then `w(x,t) = -u(-x,t)` is a
classical solution with data `x ↦ -φ(-x)`, `x ↦ -ψ(-x)`. The two inner factors
`(-1)` from `∂ₓ` square away in `w_xx`, so `w` satisfies the same wave
equation. -/
theorem isSolutionWaveIVP1D_neg_reflect {c : ℝ} {φ ψ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : Wave.IsSolutionWaveIVP1D c φ ψ u) :
    Wave.IsSolutionWaveIVP1D c (fun x => -φ (-x)) (fun x => -ψ (-x))
      (fun x t => -u (-x) t) where
  contDiff := by
    have hg : ContDiff ℝ 2 fun p : ℝ × ℝ => (-p.1, p.2) := by fun_prop
    have h : ContDiff ℝ 2 fun p : ℝ × ℝ => u (-p.1) p.2 := hu.contDiff.comp hg
    exact h.neg
  waveEq := by
    intro x t
    -- time side: the outer negation passes through both `t`-derivatives
    have ht : deriv (deriv fun τ => -u (-x) τ) t
        = -deriv (deriv (u (-x))) t := by
      simp [deriv.fun_neg]
    -- space side: two applications of `deriv_comp_neg`, the signs squaring away
    have hx1 : (deriv fun ξ => -u (-ξ) t) = fun ξ => deriv (fun y => u y t) (-ξ) := by
      funext ξ
      rw [deriv.fun_neg, deriv_comp_neg (fun y => u y t), neg_neg]
    have hx : deriv (deriv fun ξ => -u (-ξ) t) x
        = -deriv (deriv fun ξ => u ξ t) (-x) := by
      rw [hx1, deriv_comp_neg]
    rw [ht, hx, hu.waveEq (-x) t]
    ring
  initPos := by
    intro x
    rw [hu.initPos]
  initVel := by
    intro x
    rw [deriv.fun_neg, hu.initVel]

/-- **Part (b): oddness via uniqueness.** If `φ` and `ψ` are odd and `u` is a
classical solution of the whole-line wave IVP, then `u` is odd in `x` for each
`t` — proved without solving the equation: `w(x,t) = -u(-x,t)` solves the same
IVP (`isSolutionWaveIVP1D_neg_reflect` plus oddness of the data), so `u = w` by
uniqueness (`Wave.IsSolutionWaveIVP1D.unique`). -/
theorem solution_odd_of_unique {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ}
    (hφ : Function.Odd φ) (hψ : Function.Odd ψ) {u : ℝ → ℝ → ℝ}
    (hu : Wave.IsSolutionWaveIVP1D c φ ψ u) (x t : ℝ) :
    u (-x) t = -u x t := by
  have hw := isSolutionWaveIVP1D_neg_reflect hu
  have hφ' : (fun y => -φ (-y)) = φ := funext fun y => by rw [hφ.eq, neg_neg]
  have hψ' : (fun y => -ψ (-y)) = ψ := funext fun y => by rw [hψ.eq, neg_neg]
  rw [hφ', hψ'] at hw
  have h := congrFun (congrFun (hu.unique hc hw) x) t
  -- h : u x t = -u (-x) t
  linarith

end Problems.Undergraduate.Problem7
