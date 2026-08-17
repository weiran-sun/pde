import Mathlib
import PDE
import PDE.Basics.Wave.WaveIVP1D
import Problems.Undergraduate.Problem6

/-!
# Undergraduate Problem 17: Failure of the Maximum Principle for the Wave Equation

Source: `pde_latex/problems/undergraduate/problem_17.tex` (Math 418/718, HW-6, Problem 4).

## Informal statement

> (a) Construct an explicit example to show that wave equations on the whole
> line do not obey the maximum principle, that is, if `φ(x)` is the initial
> data of the wave equation and `u(x, t)` is a solution, then in general
> `max_{x ∈ ℝ, t ≥ 0} u(x, t) = max_{x ∈ ℝ} φ(x)` does not hold.

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem17.tex`:

* "Wave equation on the whole line with initial data `(φ, ψ)`" is the
  classical-solution predicate `Wave.IsSolutionWaveIVP1D` at speed `c = 1`
  (`PDE/Basics/Wave/WaveIVP1D.lean`, blueprint `def:wave-ivp-1d-solution`).
* The failure of the maximum principle is stated existentially: there are data
  `(φ, ψ)`, a classical solution `u`, and a point `(x₀, t₀)` with `t₀ ≥ 0` at
  which `u(x₀, t₀) > sup_x φ(x)` — refuting the proposed identity
  `max_{x, t ≥ 0} u = max_x φ`. The supremum of `φ` is spelled
  `sSup (Set.range φ)`; for the witness `φ ≡ 0` it equals `0` (a genuine
  attained maximum), so no `sSup`-on-unbounded-sets subtlety arises.
* The source takes `ψ ∈ C_c^∞(ℝ)` nonnegative and not identically zero. Since
  the existence half of D'Alembert's theorem
  (`Wave.isSolutionWaveIVP1D_dAlembert`, blueprint `thm:dalembert-solves`)
  only needs `ψ ∈ C¹`, the blueprint substitutes the concrete `C¹` witness
  `ψ(s) = (max {1 - s², 0})² = ((1-s²)₊)²`, supported in `[-1, 1]`, whose
  integral evaluates in closed form to `16/15`.
* The solution witness is the D'Alembert expression `Wave.dAlembert 1 0 ψ`
  (blueprint `def:dalembert-expression`); at `(x₀, t₀) = (0, 1)` the
  integration window `[x₀ - t₀, x₀ + t₀] = [-1, 1]` captures all of `ψ`, and
  `u(0, 1) = ½ · 16/15 = 8/15 > 0 = sup_x φ`.
-/

open MeasureTheory intervalIntegral Set

namespace Problems.Undergraduate.Problem17

/-- **The initial velocity witness** (blueprint `def:problem17-psi`):
`ψ(s) = (max {1 - s², 0})²`. Thus `ψ(s) = (1-s²)²` for `|s| ≤ 1` and
`ψ(s) = 0` for `|s| ≥ 1`; in particular `ψ ≥ 0` everywhere, `ψ` vanishes
outside `[-1, 1]`, and `ψ(0) = 1 > 0`. In the notation of Problem 6,
`ψ = pplus 2 ∘ (fun s => 1 - s²)`. -/
noncomputable def psi : ℝ → ℝ := fun s => max (1 - s ^ 2) 0 ^ 2

/-- **`C¹` regularity of the witness** (blueprint `lem:problem17-psi-contDiff`).
`ψ = q₂ ∘ p` with `p(s) = 1 - s²` smooth and `q₂ = pplus 2` the truncated
square, which is `C¹` by Problem 6's `contDiff_pplus` (the case `k = 1`). -/
theorem contDiff_psi : ContDiff ℝ 1 psi := by
  have hq : ContDiff ℝ 1 (Problem6.pplus 2) := by
    simpa using Problem6.contDiff_pplus 1
  have hp : ContDiff ℝ 1 (fun s : ℝ => 1 - s ^ 2) := by fun_prop
  have hcomp : psi = Problem6.pplus 2 ∘ fun s : ℝ => 1 - s ^ 2 := by
    funext s
    simp [psi, Problem6.pplus]
  rw [hcomp]
  exact hq.comp hp

/-- **Integral of the witness** (blueprint `lem:problem17-psi-integral`):
`∫_{-1}^{1} ψ(s) ds = 16/15`. On `[-1, 1]` the integrand is the polynomial
`(1-s²)² = 1 - 2s² + s⁴` with antiderivative `s - ⅔s³ + ⅕s⁵`. -/
theorem integral_psi : (∫ s in (-1:ℝ)..1, psi s) = 16 / 15 := by
  have hEq : Set.EqOn psi (fun s : ℝ => 1 - 2 * s ^ 2 + s ^ 4)
      (Set.uIcc (-1:ℝ) 1) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hs
    have hsq : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    simp only [psi, max_eq_left (by linarith : (0:ℝ) ≤ 1 - s ^ 2)]
    ring
  rw [intervalIntegral.integral_congr hEq]
  have hderiv : ∀ s ∈ Set.uIcc (-1:ℝ) 1,
      HasDerivAt (fun s : ℝ => s - 2 / 3 * s ^ 3 + 1 / 5 * s ^ 5)
        (1 - 2 * s ^ 2 + s ^ 4) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => s) 1 s := hasDerivAt_id s
    have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * s ^ 2) s := by
      simpa using hasDerivAt_pow 3 s
    have h5 : HasDerivAt (fun s : ℝ => s ^ 5) (5 * s ^ 4) s := by
      simpa using hasDerivAt_pow 5 s
    have h := (h1.sub (h3.const_mul (2 / 3))).add (h5.const_mul (1 / 5))
    have heq : (1:ℝ) - 2 / 3 * (3 * s ^ 2) + 1 / 5 * (5 * s ^ 4)
        = 1 - 2 * s ^ 2 + s ^ 4 := by ring
    exact heq ▸ h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((Continuous.intervalIntegrable (by fun_prop) _ _))]
  norm_num

/-- **Wave equations do not obey the maximum principle** (blueprint
`thm:problem17-wave-no-max-principle`; Math 418/718, HW-6, Problem 4(a)).

There exist initial data `(φ, ψ)`, a classical solution `u` of the whole-line
wave IVP with speed `c = 1` and data `(φ, ψ)`, and a point `(x₀, t₀)` with
`t₀ ≥ 0`, such that `u(x₀, t₀) > sup_x φ(x)` — so the proposed maximum
principle `max_{x, t ≥ 0} u = max_x φ` fails. Witnesses: `φ ≡ 0`, the initial
velocity `ψ` of `def:problem17-psi`, the D'Alembert solution
`u = Wave.dAlembert 1 0 ψ`, and `(x₀, t₀) = (0, 1)`, where
`u(0, 1) = ½ ∫_{-1}^1 ψ = 8/15 > 0 = sup_x φ(x)`. -/
theorem wave_no_max_principle :
    ∃ (φ ψ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (x₀ t₀ : ℝ),
      Wave.IsSolutionWaveIVP1D 1 φ ψ u ∧ 0 ≤ t₀ ∧
        sSup (Set.range φ) < u x₀ t₀ := by
  refine ⟨fun _ => 0, psi, Wave.dAlembert 1 (fun _ => 0) psi, 0, 1,
    Wave.isSolutionWaveIVP1D_dAlembert one_pos contDiff_const contDiff_psi,
    zero_le_one, ?_⟩
  have hsup : sSup (Set.range fun _ : ℝ => (0:ℝ)) = 0 := by
    rw [Set.range_const, csSup_singleton]
  have hval : Wave.dAlembert 1 (fun _ => 0) psi 0 1 = 8 / 15 := by
    simp only [Wave.dAlembert]
    norm_num [integral_psi]
  rw [hsup, hval]
  norm_num

end Problems.Undergraduate.Problem17
