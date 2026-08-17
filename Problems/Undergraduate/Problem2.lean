import Mathlib
import PDE
import PDE.Basics.Wave.WaveGeneralSolution1D
import PDE.Basics.Wave.WaveIVP1D

/-!
# Undergraduate Problem 2: A Vibrating Semi-Infinite String Fixed at `x = 0`

Source: `pde_latex/problems/undergraduate/problem_2.tex`.

## Informal statement

> Find a solution to the following initial boundary value problem for a vibrating
> semi-infinite string which is fixed at `x = 0`:
>
>   `u_tt - u_xx = 0`   for `0 < x < ∞`, `t > 0`,
>   `u(0, t) = 0`       for `t > 0`,
>   `u(x, 0) = f(x)`    for `0 ≤ x < ∞`,
>   `u_t(x, 0) = g(x)`  for `0 ≤ x < ∞`,
>
> where `f ∈ C²([0,∞))` and `g ∈ C¹([0,∞))` satisfy the compatibility conditions
> `f(0) = f''(0) = g(0) = 0`.

The solution is obtained by extending `f` and `g` as odd functions over the real
line, solving the whole-line Cauchy problem by D'Alembert's formula, and restricting
to the half-plane `x ≥ 0`; explicitly,

  `u(x,t) = ½[f(x+t) + f(x-t)] + ½ ∫_{x-t}^{x+t} g(s) ds`         if `x ≥ t`,
  `u(x,t) = ½[f(x+t) - f(t-x)] + ½ ∫_{t-x}^{x+t} g(s) ds`         if `0 ≤ x ≤ t`.

## Semantic alignment

* `f ∈ C²([0,∞))` ↦ `ContDiffOn ℝ 2 f (Set.Ici 0)`; likewise
  `g ∈ C¹([0,∞))` ↦ `ContDiffOn ℝ 1 g (Set.Ici 0)`.
* The compatibility condition `f''(0) = 0` is read with the one-sided (within
  `[0,∞)`) second derivative: `iteratedDerivWithin 2 f (Set.Ici 0) 0 = 0`.
* The classical-solution predicate `Problem2.IsSolutionFixedEndIBVP f g u`
  matches the displayed system clause by clause: `u` is `C²` on the closed quadrant
  `[0,∞) × [0,∞)`, satisfies `u_tt = u_xx` for `x > 0`, `t > 0`, the boundary
  condition `u 0 t = 0` for `t > 0`, and the initial conditions `u x 0 = f x`,
  `∂_t u x 0 = g x` for `x ≥ 0`. Partial derivatives are the one-variable `deriv`
  slices `Wave.xderiv` / `Wave.tderiv` from `PDE.Basics.Wave.WaveGeneralSolution1D`.
* "Find a solution" ↦ `Problem2.exists_solution` exhibits one, namely
  `Problem2.solution f g = Wave.dAlembert 1 (oddExtension f) (oddExtension g)`
  (odd reflection + D'Alembert with `c = 1`, exactly the hinted construction);
  `Problem2.solution_eq_of_le_x` / `Problem2.solution_eq_of_le_t` identify it with
  the two-case explicit formula above.

## Note on reuse

The odd-extension construction and the fixed-end solution formula are the content
of the library chapter `pde_latex/PDE/Basics/Wave/WaveBVP1D.tex`
(`PDE/Basics/Wave/WaveBVP1D.lean`), which does not exist yet. The declarations
`Problem2.oddExtension` and its smoothness lemmas below are reusable and should
migrate there (generalized to arbitrary wave speed `c > 0`) once that file lands;
this problem file would then shrink to the `c = 1` instantiation.
-/

open MeasureTheory intervalIntegral Set
open scoped Interval

namespace Problem2

/-!
### The odd extension

Extending the data of the half-line problem to the whole line by odd reflection is
the key device: D'Alembert's formula applies to the extensions, and oddness of the
resulting solution enforces the fixed-end boundary condition `u(0,t) = 0`.
-/

/-- The odd extension of `f : ℝ → ℝ` from `[0,∞)` to `ℝ`:
`oddExtension f x = f x` for `x ≥ 0` and `oddExtension f x = -f (-x)` for `x < 0`.
Only the values of `f` on `[0,∞)` are consulted. -/
noncomputable def oddExtension (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if 0 ≤ x then f x else -f (-x)

/-- The odd extension agrees with the original function on `[0,∞)`. -/
theorem oddExtension_apply_of_nonneg (f : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    oddExtension f x = f x :=
  if_pos hx

/-- The odd extension is an odd function (given the compatibility `f 0 = 0`). -/
theorem oddExtension_neg {f : ℝ → ℝ} (hf0 : f 0 = 0) (x : ℝ) :
    oddExtension f (-x) = -oddExtension f x := by
  unfold oddExtension
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [if_pos (by linarith), if_neg (by linarith), neg_neg]
  · simp [hf0]
  · rw [if_neg (by linarith), if_pos hx.le, neg_neg]

/-- Bridge to the library: the problem-local odd extension is definitionally the
general odd extension of `PDE/Basics/Wave/WaveBVP1D.lean`. -/
theorem oddExtension_eq_wave (f : ℝ → ℝ) : oddExtension f = Wave.oddExtension f :=
  rfl

/-- **`C²` regularity of the odd extension.** If `f ∈ C²([0,∞))` and
`f(0) = f''(0) = 0` (second derivative one-sided), then the odd extension of `f`
is `C²` on all of `ℝ`. -/
theorem contDiff_two_oddExtension {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ici 0))
    (hf0 : f 0 = 0) (hf2 : iteratedDerivWithin 2 f (Set.Ici 0) 0 = 0) :
    ContDiff ℝ 2 (oddExtension f) := by
  rw [oddExtension_eq_wave]
  exact Wave.contDiff_two_oddExtension hf hf0 hf2

/-- **`C¹` regularity of the odd extension.** If `g ∈ C¹([0,∞))` and `g(0) = 0`,
then the odd extension of `g` is `C¹` on all of `ℝ`. -/
theorem contDiff_one_oddExtension {g : ℝ → ℝ} (hg : ContDiffOn ℝ 1 g (Set.Ici 0))
    (hg0 : g 0 = 0) : ContDiff ℝ 1 (oddExtension g) := by
  rw [oddExtension_eq_wave]
  exact Wave.contDiff_one_oddExtension hg hg0

/-!
### The initial boundary value problem and its solution
-/

/-- `u` is a classical solution of the initial boundary value problem for the
vibrating semi-infinite string fixed at `x = 0` (wave speed `c = 1`):

  `u_tt - u_xx = 0` for `x > 0`, `t > 0`;  `u(0,t) = 0` for `t > 0`;
  `u(x,0) = f(x)` and `u_t(x,0) = g(x)` for `x ≥ 0`;

with `u` of class `C²` on the closed quadrant `[0,∞) × [0,∞)`. -/
structure IsSolutionFixedEndIBVP (f g : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  /-- The solution is `C²` on the closed quadrant `[0,∞) × [0,∞)`. -/
  contDiffOn : ContDiffOn ℝ 2 (Function.uncurry u) (Set.Ici 0 ×ˢ Set.Ici 0)
  /-- The wave equation `u_tt = u_xx` holds in the open quadrant. -/
  waveEq : ∀ x t : ℝ, 0 < x → 0 < t →
    Wave.tderiv (Wave.tderiv u) x t = Wave.xderiv (Wave.xderiv u) x t
  /-- The fixed-end (Dirichlet) boundary condition `u(0, t) = 0`. -/
  boundary : ∀ t : ℝ, 0 < t → u 0 t = 0
  /-- Initial displacement: `u(x, 0) = f(x)` for `x ≥ 0`. -/
  initPos : ∀ x : ℝ, 0 ≤ x → u x 0 = f x
  /-- Initial velocity: `u_t(x, 0) = g(x)` for `x ≥ 0`. -/
  initVel : ∀ x : ℝ, 0 ≤ x → Wave.tderiv u x 0 = g x

/-- The solution of Problem 2: apply D'Alembert's expression (wave speed `c = 1`)
to the odd extensions of the initial data, following the hint. -/
noncomputable def solution (f g : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Wave.dAlembert 1 (oddExtension f) (oddExtension g)

/-- Bridge to the library: `Problem2.solution` is the fixed-end solution of
`PDE/Basics/Wave/WaveBVP1D.lean` at wave speed `c = 1`. -/
theorem solution_eq_fixedEndSolution (f g : ℝ → ℝ) :
    solution f g = Wave.fixedEndSolution 1 f g :=
  rfl

/-- **Main theorem (Problem 2).** For `f ∈ C²([0,∞))`, `g ∈ C¹([0,∞))` with
`f(0) = f''(0) = g(0) = 0`, the odd-reflection D'Alembert function
`Problem2.solution f g` is a classical solution of the initial boundary value
problem for the semi-infinite string fixed at `x = 0`. -/
theorem isSolutionFixedEndIBVP_solution {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ici 0)) (hg : ContDiffOn ℝ 1 g (Set.Ici 0))
    (hf0 : f 0 = 0) (hf2 : iteratedDerivWithin 2 f (Set.Ici 0) 0 = 0)
    (hg0 : g 0 = 0) :
    IsSolutionFixedEndIBVP f g (solution f g) := by
  have h := Wave.isSolutionWaveBVP1D_fixedEndSolution one_pos hf hg hf0 hf2 hg0
  rw [solution_eq_fixedEndSolution]
  refine ⟨h.contDiffOn, ?_, ?_, h.initPos, h.initVel⟩
  · intro x t hx ht
    simpa using h.waveEq x t hx ht
  · intro t ht
    exact h.boundary t ht.le

/-- **Problem 2, as stated**: the initial boundary value problem for the vibrating
semi-infinite string fixed at `x = 0` has a (classical) solution. -/
theorem exists_solution {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ici 0)) (hg : ContDiffOn ℝ 1 g (Set.Ici 0))
    (hf0 : f 0 = 0) (hf2 : iteratedDerivWithin 2 f (Set.Ici 0) 0 = 0)
    (hg0 : g 0 = 0) :
    ∃ u : ℝ → ℝ → ℝ, IsSolutionFixedEndIBVP f g u :=
  ⟨solution f g, isSolutionFixedEndIBVP_solution hf hg hf0 hf2 hg0⟩

/-!
### The explicit two-case formula

Written exclusively in terms of the original data `f`, `g`, the solution is the
piecewise formula displayed in the problem statement: away from the boundary's
domain of influence (`x ≥ t`) it is plain D'Alembert; near the boundary
(`0 ≤ x ≤ t`) the reflected term `-f(t-x)` and the folded integral appear.
-/

/-- Explicit formula, case `x ≥ t`: the boundary has no effect and the solution is
given by the plain D'Alembert formula in terms of `f` and `g`. -/
theorem solution_eq_of_le_x {f g : ℝ → ℝ} {x t : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) :
    solution f g x t
      = (f (x + t) + f (x - t)) / 2 + (1 / 2) * ∫ s in (x - t)..(x + t), g s := by
  have h := Wave.fixedEndSolution_eq_of_le_x (c := 1) one_pos (φ := f) (ψ := g)
    ht (by simpa using htx)
  rw [solution_eq_fixedEndSolution]
  simpa using h

/-- Explicit formula, case `0 ≤ x ≤ t`: the reflected wave `-f(t-x)` appears and
the velocity integral folds to `[t-x, x+t]`.

The compatibility hypotheses `f(0) = g(0) = 0` and the continuity of `g` on
`[0,∞)` (all standing assumptions of the problem) make the odd extension of `g`
continuous, hence integrable on compact intervals, so the velocity integral may
be split at the reflection point. -/
theorem solution_eq_of_le_t {f g : ℝ → ℝ} (hf0 : f 0 = 0)
    (hg : ContinuousOn g (Set.Ici 0)) (hg0 : g 0 = 0)
    {x t : ℝ} (hx : 0 ≤ x) (hxt : x ≤ t) :
    solution f g x t
      = (f (x + t) - f (t - x)) / 2 + (1 / 2) * ∫ s in (t - x)..(x + t), g s := by
  have h := Wave.fixedEndSolution_eq_of_le_t (c := 1) one_pos hf0 hg hg0
    hx (by simpa using hxt)
  rw [solution_eq_fixedEndSolution]
  simpa using h

end Problem2
