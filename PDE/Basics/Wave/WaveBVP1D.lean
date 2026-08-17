import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import PDE.Basics.Wave.WaveGeneralSolution1D
import PDE.Basics.Wave.WaveIVP1D

/-!
# The 1D Wave Equation on the Half-Line: Fixed End and Odd Reflection

This file formalizes the boundary/initial value problem for the semi-infinite
string with a fixed (Dirichlet) left end,

  `v_tt = c² v_xx` for `x ≥ 0, t ≥ 0`,  `v(x,0) = φ(x)`,  `v_t(x,0) = ψ(x)`,
  `v(0,t) = 0`,

following Rustum Choksi's *Partial Differential Equations: A First Course*,
Section 3.8.1.

Main results:
* `Wave.oddExtension` — the odd reflection of a function on `[0,∞)` to `ℝ`,
  with `C²`/`C¹` regularity transfer under the compatibility conditions
  (`Wave.contDiff_two_oddExtension`, `Wave.contDiff_one_oddExtension`).
* `Wave.IsSolutionWaveBVP1D` — the classical-solution predicate for the
  fixed-end BVP/IVP on the quadrant `[0,∞) × [0,∞)`.
* `Wave.fixedEndSolution` — the candidate solution: D'Alembert's expression
  applied to the odd extensions of the data (equation (3.18)).
* `Wave.isSolutionWaveBVP1D_fixedEndSolution` — existence: under the
  compatibility conditions `φ(0) = φ''(0) = ψ(0) = 0`, the odd-reflection
  D'Alembert function is a classical solution.
* `Wave.fixedEndSolution_eq_of_le_x` / `Wave.fixedEndSolution_eq_of_le_t` —
  the explicit two-case formula (3.19)/(3.20) in terms of the original data.
* `Wave.IsSolutionWaveBVP1D.eq_fixedEndSolution` — the representation theorem
  (Theorem 3.3): every classical solution of the fixed-end BVP/IVP is given by
  the odd-reflection D'Alembert expression, hence by the piecewise
  formula (3.21); uniqueness follows (`Wave.IsSolutionWaveBVP1D.unique`).

Partial derivatives of a two-variable function are the one-variable `deriv`
slices `Wave.xderiv` / `Wave.tderiv` from `PDE.Basics.Wave.WaveGeneralSolution1D`.

## Reference

Chapter 3.8.1, ["Partial Differential Equations, A First Course"](https://bookstore.ams.org/amstext-54/)
by Rustum Choksi.
-/

open MeasureTheory intervalIntegral Set
open scoped Interval

namespace Wave

/-!
### 1. The odd extension

Extending the half-line data to the whole line by odd reflection is the key
device: D'Alembert's formula applies to the extensions, and oddness of the
resulting solution enforces the fixed-end boundary condition `v(0,t) = 0`.
-/

/-- The odd extension of `f : ℝ → ℝ` from `[0,∞)` to `ℝ`:
`oddExtension f x = f x` for `x ≥ 0` and `oddExtension f x = -f (-x)` for
`x < 0`. Only the values of `f` on `[0,∞)` are consulted. -/
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

/-!
#### Scaffold: one-sided matching for the regularity of the odd extension

Following the chapter's proof (`lem:wave-odd-extension-c2`,
`lem:wave-odd-extension-c1`): on each open half-line the odd extension agrees
with a smooth function (`f` on the right, `-f ∘ (-·)` on the left), and at the
origin the one-sided derivatives match thanks to the compatibility conditions.
Concretely, the derivative of the odd extension is the *even* extension
`x ↦ f'(|x|)` of the one-sided derivative, and the derivative of that even
extension is in turn the odd extension of the one-sided second derivative
(which is where `f''(0) = 0` enters).
-/

/-- The odd extension agrees with `-f(-·)` on `(-∞, 0]` when `f 0 = 0`
(the closed left branch of the piecewise formula). -/
private lemma oddExtension_apply_of_nonpos {f : ℝ → ℝ} (hf0 : f 0 = 0) {x : ℝ}
    (hx : x ≤ 0) : oddExtension f x = -f (-x) := by
  rcases hx.lt_or_eq with h | rfl
  · exact if_neg (not_le.mpr h)
  · simp [oddExtension, hf0]

/-- The even extension `x ↦ g(|x|)` of a function continuous on `[0,∞)` is
continuous on all of `ℝ` (no compatibility condition needed). -/
private lemma continuous_comp_abs {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ici 0)) : Continuous fun x => g |x| :=
  hg.comp_continuous continuous_abs fun x => abs_nonneg x

/-- Continuity of the odd extension: if `f` is continuous on `[0,∞)` and
`f 0 = 0`, then the odd extension is continuous on all of `ℝ`. -/
private lemma continuous_oddExtension {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ici 0)) (hf0 : f 0 = 0) :
    Continuous (oddExtension f) := by
  have hF : Continuous fun x : ℝ => f |x| := continuous_comp_abs hf
  have hext : oddExtension f = fun x => if (0 : ℝ) ≤ x then f |x| else -f |x| := by
    funext x
    by_cases hx : 0 ≤ x
    · simp [oddExtension, hx, abs_of_nonneg hx]
    · simp [oddExtension, hx, abs_of_neg (not_le.mp hx)]
  rw [hext]
  exact hF.if_le hF.neg continuous_const continuous_id fun x hx => by
    simp [← hx, hf0]

/-- Derivative of the odd extension on the open right half-line: for `x > 0`
the odd extension locally coincides with `f`, so it has the one-sided
derivative of `f` as derivative. -/
private lemma hasDerivAt_oddExtension_of_pos {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (oddExtension f) (derivWithin f (Set.Ici 0) x) x := by
  have hd : HasDerivAt f (derivWithin f (Set.Ici 0) x) x :=
    ((hf.differentiableOn one_ne_zero x hx.le).hasDerivWithinAt).hasDerivAt
      (Ici_mem_nhds hx)
  have heq : oddExtension f =ᶠ[nhds x] f := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact oddExtension_apply_of_nonneg f hy.le
  exact hd.congr_of_eventuallyEq heq

/-- Derivative of the odd extension on the open left half-line: for `x < 0`
the odd extension locally coincides with `-f(-·)`, whose derivative by the
chain rule is the (even) reflection `f'(-x)` of the one-sided derivative. -/
private lemma hasDerivAt_oddExtension_of_neg {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0)) {x : ℝ} (hx : x < 0) :
    HasDerivAt (oddExtension f) (derivWithin f (Set.Ici 0) (-x)) x := by
  have hd : HasDerivAt f (derivWithin f (Set.Ici 0) (-x)) (-x) :=
    ((hf.differentiableOn one_ne_zero (-x) (neg_pos.mpr hx).le).hasDerivWithinAt).hasDerivAt
      (Ici_mem_nhds (neg_pos.mpr hx))
  have hneg : HasDerivAt (fun y : ℝ => -f (-y)) (derivWithin f (Set.Ici 0) (-x)) x := by
    simpa [Function.comp_def, Pi.neg_def] using (hd.comp x (hasDerivAt_neg x)).neg
  have heq : oddExtension f =ᶠ[nhds x] fun y => -f (-y) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact if_neg (not_le.mpr hy)
  exact hneg.congr_of_eventuallyEq heq

/-- One-sided matching at the origin: with `f 0 = 0`, the difference quotients
of the odd extension from both sides converge to the one-sided derivative
`f'(0⁺)`, so the odd extension is differentiable at `0` with that derivative. -/
private lemma hasDerivAt_oddExtension_zero {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0)) (hf0 : f 0 = 0) :
    HasDerivAt (oddExtension f) (derivWithin f (Set.Ici 0) 0) 0 := by
  set d := derivWithin f (Set.Ici 0) 0 with hd_def
  have hdf : HasDerivWithinAt f d (Set.Ici 0) 0 :=
    (hf.differentiableOn one_ne_zero 0 (Set.mem_Ici.mpr le_rfl)).hasDerivWithinAt
  -- right half-line: the odd extension is `f`
  have hright : HasDerivWithinAt (oddExtension f) d (Set.Ici 0) 0 :=
    hdf.congr (fun y hy => oddExtension_apply_of_nonneg f hy)
      (oddExtension_apply_of_nonneg f le_rfl)
  -- left half-line: the odd extension is `-f (-·)`, reflected to `[0,∞)`
  have hneg : HasDerivWithinAt (fun y : ℝ => -y) (-1 : ℝ) (Set.Iic 0) 0 :=
    (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun y : ℝ => -y) (Set.Iic 0) (Set.Ici 0) :=
    fun y hy => Set.mem_Ici.mpr (neg_nonneg.mpr (Set.mem_Iic.mp hy))
  have hdf' : HasDerivWithinAt f d (Set.Ici 0) (-(0 : ℝ)) := by
    rw [neg_zero]; exact hdf
  have hcomp : HasDerivWithinAt (fun y : ℝ => f (-y)) (d * (-1)) (Set.Iic 0) 0 :=
    hdf'.comp (0 : ℝ) hneg hmaps
  have hleft : HasDerivWithinAt (oddExtension f) d (Set.Iic 0) 0 := by
    have : HasDerivWithinAt (fun y : ℝ => -f (-y)) d (Set.Iic 0) 0 := by
      simpa [Function.comp_def, Pi.neg_def] using hcomp.neg
    exact this.congr (fun y hy => oddExtension_apply_of_nonpos hf0 hy)
      (oddExtension_apply_of_nonpos hf0 le_rfl)
  -- glue the closed half-lines
  have hunion : HasDerivWithinAt (oddExtension f) d (Set.Iic 0 ∪ Set.Ici 0) 0 :=
    hleft.union hright
  rw [Set.Iic_union_Ici] at hunion
  exact hunion.hasDerivAt Filter.univ_mem

/-- **Derivative formula for the odd extension**: the derivative of `f_odd` is
the even extension `x ↦ f'(|x|)` of the one-sided derivative of `f`. -/
private lemma hasDerivAt_oddExtension {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ici 0)) (hf0 : f 0 = 0) (x : ℝ) :
    HasDerivAt (oddExtension f) (derivWithin f (Set.Ici 0) |x|) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_neg hx]; exact hasDerivAt_oddExtension_of_neg hf hx
  · rw [abs_zero]; exact hasDerivAt_oddExtension_zero hf hf0
  · rw [abs_of_pos hx]; exact hasDerivAt_oddExtension_of_pos hf hx

/-- Derivative of the even extension: if `g ∈ C¹([0,∞))` and the one-sided
derivative vanishes at the origin, then `x ↦ g(|x|)` is differentiable
everywhere with derivative the *odd* extension of `g'`. (At `0` this is where
the compatibility `g'(0) = 0` makes the one-sided slopes `±g'(0)` agree.) -/
private lemma hasDerivAt_comp_abs {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Ici 0))
    (hg' : derivWithin g (Set.Ici 0) 0 = 0) (x : ℝ) :
    HasDerivAt (fun y => g |y|) (oddExtension (derivWithin g (Set.Ici 0)) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · -- left half-line: locally `g(-·)`, derivative `-g'(-x)`
    have hd : HasDerivAt g (derivWithin g (Set.Ici 0) (-x)) (-x) :=
      ((hg.differentiableOn one_ne_zero (-x) (neg_pos.mpr hx).le).hasDerivWithinAt).hasDerivAt
        (Ici_mem_nhds (neg_pos.mpr hx))
    have hneg : HasDerivAt (fun y : ℝ => g (-y))
        (-derivWithin g (Set.Ici 0) (-x)) x := by
      simpa [Function.comp_def] using hd.comp x (hasDerivAt_neg x)
    have heq : (fun y : ℝ => g |y|) =ᶠ[nhds x] fun y => g (-y) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      rw [abs_of_neg hy]
    have : HasDerivAt (fun y : ℝ => g |y|) (-derivWithin g (Set.Ici 0) (-x)) x :=
      hneg.congr_of_eventuallyEq heq
    simpa [oddExtension, not_le.mpr hx] using this
  · -- origin: both one-sided slopes vanish by the compatibility `g'(0) = 0`
    have hdg : HasDerivWithinAt g (0 : ℝ) (Set.Ici 0) 0 := by
      simpa [hg'] using
        (hg.differentiableOn one_ne_zero 0 (Set.mem_Ici.mpr le_rfl)).hasDerivWithinAt
    have hright : HasDerivWithinAt (fun y : ℝ => g |y|) (0 : ℝ) (Set.Ici 0) 0 :=
      hdg.congr (fun y hy => by rw [abs_of_nonneg hy]) (by simp)
    have hneg : HasDerivWithinAt (fun y : ℝ => -y) (-1 : ℝ) (Set.Iic 0) 0 :=
      (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun y : ℝ => -y) (Set.Iic 0) (Set.Ici 0) :=
      fun y hy => Set.mem_Ici.mpr (neg_nonneg.mpr (Set.mem_Iic.mp hy))
    have hdg2 : HasDerivWithinAt g (0 : ℝ) (Set.Ici 0) (-(0 : ℝ)) := by
      rw [neg_zero]; exact hdg
    have hcomp : HasDerivWithinAt (fun y : ℝ => g (-y)) (0 : ℝ) (Set.Iic 0) 0 := by
      simpa [Function.comp_def] using hdg2.comp (0 : ℝ) hneg hmaps
    have hleft : HasDerivWithinAt (fun y : ℝ => g |y|) (0 : ℝ) (Set.Iic 0) 0 :=
      hcomp.congr (fun y hy => by rw [abs_of_nonpos hy]) (by simp)
    have hunion : HasDerivWithinAt (fun y : ℝ => g |y|) (0 : ℝ)
        (Set.Iic 0 ∪ Set.Ici 0) 0 := hleft.union hright
    rw [Set.Iic_union_Ici] at hunion
    have h0 : oddExtension (derivWithin g (Set.Ici 0)) 0 = 0 := by
      simp [oddExtension, hg']
    rw [h0]
    exact hunion.hasDerivAt Filter.univ_mem
  · -- right half-line: locally `g`
    have hd : HasDerivAt g (derivWithin g (Set.Ici 0) x) x :=
      ((hg.differentiableOn one_ne_zero x hx.le).hasDerivWithinAt).hasDerivAt
        (Ici_mem_nhds hx)
    have heq : (fun y : ℝ => g |y|) =ᶠ[nhds x] g := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [abs_of_pos hy]
    have : HasDerivAt (fun y : ℝ => g |y|) (derivWithin g (Set.Ici 0) x) x :=
      hd.congr_of_eventuallyEq heq
    simpa [oddExtension, hx.le] using this

/-- `C¹` regularity of the even extension `x ↦ g(|x|)` for `g ∈ C¹([0,∞))`
with `g'(0) = 0`: assembly of `hasDerivAt_comp_abs` (differentiability and the
derivative formula) with `continuous_oddExtension` (continuity of the odd
extension of `g'`). -/
private lemma contDiff_one_comp_abs {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Ici 0))
    (hg' : derivWithin g (Set.Ici 0) 0 = 0) :
    ContDiff ℝ 1 fun x => g |x| := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y => g |y|)
      (oddExtension (derivWithin g (Set.Ici 0)) x) x :=
    hasDerivAt_comp_abs hg hg'
  have hderiv : (deriv fun y => g |y|)
      = oddExtension (derivWithin g (Set.Ici 0)) :=
    funext fun x => (hd x).deriv
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  rw [hderiv]
  exact continuous_oddExtension
    (hg.continuousOn_derivWithin (uniqueDiffOn_Ici 0) le_rfl) hg'

/-- The one-sided derivative of the one-sided derivative is `C⁰`-one-sided
differentiable data: `φ ∈ C²([0,∞))` yields `φ' ∈ C¹([0,∞))`. -/
private lemma contDiffOn_one_derivWithin {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Ici 0)) :
    ContDiffOn ℝ 1 (derivWithin φ (Set.Ici 0)) (Set.Ici 0) := by
  exact hφ.derivWithin (uniqueDiffOn_Ici 0) (by norm_num)

/-- Unfolding the compatibility hypothesis: the second `iteratedDerivWithin`
at `0` is the one-sided derivative of the one-sided derivative at `0`. -/
private lemma derivWithin_derivWithin_zero_of_iteratedDerivWithin_two {φ : ℝ → ℝ}
    (hφ2 : iteratedDerivWithin 2 φ (Set.Ici 0) 0 = 0) :
    derivWithin (derivWithin φ (Set.Ici 0)) (Set.Ici 0) 0 = 0 := by
  have h1 : iteratedDerivWithin 1 φ (Set.Ici 0) = derivWithin φ (Set.Ici 0) := by
    funext y
    rw [iteratedDerivWithin_one]
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ, h1] at hφ2
  exact hφ2

/-- **`C²` regularity of the odd extension.** If `φ ∈ C²([0,∞))` and
`φ(0) = φ''(0) = 0` (second derivative one-sided), then the odd extension of
`φ` is `C²` on all of `ℝ`. -/
theorem contDiff_two_oddExtension {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Ici 0)) (hφ0 : φ 0 = 0)
    (hφ2 : iteratedDerivWithin 2 φ (Set.Ici 0) 0 = 0) :
    ContDiff ℝ 2 (oddExtension φ) := by
  have hφ1 : ContDiffOn ℝ 1 φ (Set.Ici 0) := hφ.of_le one_le_two
  have hd : ∀ x : ℝ, HasDerivAt (oddExtension φ) (derivWithin φ (Set.Ici 0) |x|) x :=
    hasDerivAt_oddExtension hφ1 hφ0
  have hderiv : deriv (oddExtension φ) = fun x => derivWithin φ (Set.Ici 0) |x| :=
    funext fun x => (hd x).deriv
  have h1 : ContDiff ℝ 1 (deriv (oddExtension φ)) := by
    rw [hderiv]
    exact contDiff_one_comp_abs (contDiffOn_one_derivWithin hφ)
      (derivWithin_derivWithin_zero_of_iteratedDerivWithin_two hφ2)
  rw [show ((2 : WithTop ℕ∞)) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨fun x => (hd x).differentiableAt, fun h => by simp at h, h1⟩

/-- **`C¹` regularity of the odd extension.** If `ψ ∈ C¹([0,∞))` and
`ψ(0) = 0`, then the odd extension of `ψ` is `C¹` on all of `ℝ`. -/
theorem contDiff_one_oddExtension {ψ : ℝ → ℝ}
    (hψ : ContDiffOn ℝ 1 ψ (Set.Ici 0)) (hψ0 : ψ 0 = 0) :
    ContDiff ℝ 1 (oddExtension ψ) := by
  have hd : ∀ x : ℝ, HasDerivAt (oddExtension ψ) (derivWithin ψ (Set.Ici 0) |x|) x :=
    hasDerivAt_oddExtension hψ hψ0
  have hderiv : deriv (oddExtension ψ) = fun x => derivWithin ψ (Set.Ici 0) |x| :=
    funext fun x => (hd x).deriv
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  rw [hderiv]
  exact continuous_comp_abs
    (hψ.continuousOn_derivWithin (uniqueDiffOn_Ici 0) le_rfl)

/-!
### 2. The fixed-end BVP/IVP and its solution
-/

/-- `v` is a classical solution of the boundary/initial value problem (3.17)
for the semi-infinite string fixed at `x = 0`, with wave speed `c`, initial
displacement `φ`, and initial velocity `ψ`:

  `v_tt = c² v_xx` for `x > 0`, `t > 0`;  `v(0,t) = 0` for `t ≥ 0`;
  `v(x,0) = φ(x)` and `v_t(x,0) = ψ(x)` for `x ≥ 0`;

with `v` of class `C²` on the closed quadrant `[0,∞) × [0,∞)`. -/
structure IsSolutionWaveBVP1D (c : ℝ) (φ ψ : ℝ → ℝ) (v : ℝ → ℝ → ℝ) : Prop where
  /-- The solution is `C²` on the closed quadrant `[0,∞) × [0,∞)`. -/
  contDiffOn : ContDiffOn ℝ 2 (Function.uncurry v) (Set.Ici 0 ×ˢ Set.Ici 0)
  /-- The wave equation `v_tt = c² v_xx` holds in the open quadrant. -/
  waveEq : ∀ x t : ℝ, 0 < x → 0 < t →
    tderiv (tderiv v) x t = c ^ 2 * xderiv (xderiv v) x t
  /-- The fixed-end (Dirichlet) boundary condition `v(0, t) = 0`. -/
  boundary : ∀ t : ℝ, 0 ≤ t → v 0 t = 0
  /-- Initial displacement: `v(x, 0) = φ(x)` for `x ≥ 0`. -/
  initPos : ∀ x : ℝ, 0 ≤ x → v x 0 = φ x
  /-- Initial velocity: `v_t(x, 0) = ψ(x)` for `x ≥ 0`. -/
  initVel : ∀ x : ℝ, 0 ≤ x → tderiv v x 0 = ψ x

/-- **The odd-reflection D'Alembert solution** (equation (3.18)): D'Alembert's
expression applied to the odd extensions of the data,

  `v(x,t) = ½[φ_odd(x+ct) + φ_odd(x-ct)] + (1/2c) ∫_{x-ct}^{x+ct} ψ_odd(s) ds`. -/
noncomputable def fixedEndSolution (c : ℝ) (φ ψ : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  dAlembert c (oddExtension φ) (oddExtension ψ)

/-- The interval integral of the odd extension over a symmetric interval
`[-a, a]` vanishes. (No integrability is needed: the reflection `s ↦ -s`
identity for interval integrals is unconditional.) -/
private lemma integral_oddExtension_symm {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 0) (a : ℝ) :
    (∫ s in (-a)..a, oddExtension ψ s) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) (oddExtension ψ)
  simp only [neg_neg, oddExtension_neg hψ0, intervalIntegral.integral_neg] at h
  linarith

/-- **Existence for the fixed-end BVP/IVP.** For `c > 0`, `φ ∈ C²([0,∞))`,
`ψ ∈ C¹([0,∞))` with the compatibility conditions `φ(0) = φ''(0) = ψ(0) = 0`,
the odd-reflection D'Alembert function is a classical solution of the
boundary/initial value problem (3.17). -/
theorem isSolutionWaveBVP1D_fixedEndSolution {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Ici 0)) (hψ : ContDiffOn ℝ 1 ψ (Set.Ici 0))
    (hφ0 : φ 0 = 0) (hφ2 : iteratedDerivWithin 2 φ (Set.Ici 0) 0 = 0)
    (hψ0 : ψ 0 = 0) :
    IsSolutionWaveBVP1D c φ ψ (fixedEndSolution c φ ψ) := by
  have hφodd : ContDiff ℝ 2 (oddExtension φ) := contDiff_two_oddExtension hφ hφ0 hφ2
  have hψodd : ContDiff ℝ 1 (oddExtension ψ) := contDiff_one_oddExtension hψ hψ0
  have hsol : IsSolutionWaveIVP1D c (oddExtension φ) (oddExtension ψ)
      (dAlembert c (oddExtension φ) (oddExtension ψ)) :=
    isSolutionWaveIVP1D_dAlembert hc hφodd hψodd
  unfold fixedEndSolution
  refine ⟨hsol.contDiff.contDiffOn, ?_, ?_, ?_, ?_⟩
  · intro x t _ _
    simpa [tderiv, xderiv] using hsol.waveEq x t
  · intro t _
    show dAlembert c (oddExtension φ) (oddExtension ψ) 0 t = 0
    unfold dAlembert
    rw [show (0 : ℝ) + c * t = c * t by ring, show (0 : ℝ) - c * t = -(c * t) by ring,
      oddExtension_neg hφ0, integral_oddExtension_symm hψ0]
    ring
  · intro x hx
    show dAlembert c (oddExtension φ) (oddExtension ψ) x 0 = φ x
    rw [hsol.initPos x, oddExtension_apply_of_nonneg φ hx]
  · intro x hx
    show tderiv (dAlembert c (oddExtension φ) (oddExtension ψ)) x 0 = ψ x
    simpa [tderiv, oddExtension_apply_of_nonneg ψ hx] using hsol.initVel x

/-!
### 3. The explicit two-case formula

Written exclusively in terms of the original data `φ`, `ψ`, the odd-reflection
solution is the piecewise formula (3.21): away from the boundary's domain of
influence (`x ≥ ct`) it is plain D'Alembert; near the boundary (`0 ≤ x ≤ ct`)
the reflected wave `-φ(ct-x)` and the folded integral appear.
-/

/-- **Explicit formula away from the boundary** (equation (3.19)): for
`x ≥ ct ≥ 0` the fixed boundary has no effect and the solution is the plain
D'Alembert formula in terms of `φ` and `ψ`. -/
theorem fixedEndSolution_eq_of_le_x {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ}
    {x t : ℝ} (ht : 0 ≤ t) (htx : c * t ≤ x) :
    fixedEndSolution c φ ψ x t
      = (φ (x + c * t) + φ (x - c * t)) / 2
        + (1 / (2 * c)) * ∫ s in (x - c * t)..(x + c * t), ψ s := by
  have hct : 0 ≤ c * t := mul_nonneg hc.le ht
  have hle : x - c * t ≤ x + c * t := by linarith
  unfold fixedEndSolution dAlembert
  rw [oddExtension_apply_of_nonneg φ (by linarith : (0:ℝ) ≤ x + c * t),
    oddExtension_apply_of_nonneg φ (by linarith : (0:ℝ) ≤ x - c * t),
    intervalIntegral.integral_congr fun s hs => oddExtension_apply_of_nonneg ψ
      (le_trans (by linarith : (0:ℝ) ≤ x - c * t) (Set.uIcc_of_le hle ▸ hs).1)]

/-- **Explicit formula near the boundary** (equation (3.20)): for
`0 ≤ x ≤ ct` the reflected wave `-φ(ct-x)` appears and the velocity integral
folds to `[ct-x, x+ct]`.

The continuity and compatibility hypotheses on `ψ` (standing assumptions of
the BVP) guarantee the odd extension is integrable, so the integral may be
split at the reflection point. -/
theorem fixedEndSolution_eq_of_le_t {c : ℝ} (_hc : 0 < c) {φ ψ : ℝ → ℝ}
    (hφ0 : φ 0 = 0) (hψ : ContinuousOn ψ (Set.Ici 0)) (hψ0 : ψ 0 = 0)
    {x t : ℝ} (hx : 0 ≤ x) (hxt : x ≤ c * t) :
    fixedEndSolution c φ ψ x t
      = (φ (x + c * t) - φ (c * t - x)) / 2
        + (1 / (2 * c)) * ∫ s in (c * t - x)..(x + c * t), ψ s := by
  have hct : 0 ≤ c * t := hx.trans hxt
  have hcont : Continuous (oddExtension ψ) := continuous_oddExtension hψ hψ0
  have h1 : oddExtension φ (x + c * t) = φ (x + c * t) :=
    oddExtension_apply_of_nonneg φ (by linarith)
  have h2 : oddExtension φ (x - c * t) = -φ (c * t - x) := by
    rw [oddExtension_apply_of_nonpos hφ0 (by linarith : x - c * t ≤ 0), neg_sub]
  have hsplit : (∫ s in (x - c * t)..(x + c * t), oddExtension ψ s)
      = (∫ s in (x - c * t)..(c * t - x), oddExtension ψ s)
        + ∫ s in (c * t - x)..(x + c * t), oddExtension ψ s :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hsym : (∫ s in (x - c * t)..(c * t - x), oddExtension ψ s) = 0 := by
    rw [show x - c * t = -(c * t - x) by ring]
    exact integral_oddExtension_symm hψ0 _
  have hle : c * t - x ≤ x + c * t := by linarith
  have hlast : (∫ s in (c * t - x)..(x + c * t), oddExtension ψ s)
      = ∫ s in (c * t - x)..(x + c * t), ψ s :=
    intervalIntegral.integral_congr fun s hs =>
      oddExtension_apply_of_nonneg ψ (le_trans (by linarith : (0:ℝ) ≤ c * t - x)
        (Set.uIcc_of_le hle ▸ hs).1)
  unfold fixedEndSolution dAlembert
  rw [h1, h2, hsplit, hsym, hlast]
  ring

/-!
### 4. The representation theorem (Theorem 3.3) and uniqueness

Scaffold, following the chapter proof of Theorem 3.3: extend `v` oddly in the
spatial variable. The boundary condition `v(0,t) = 0` together with the wave
equation up to the boundary (which forces `v_xx(0,t) = c⁻² v_tt(0,t) = 0`)
makes the reflection a `C²` solution of the whole-line wave equation on the
closed upper half-plane, with initial data the odd extensions `φ_odd, ψ_odd`.
The half-plane d'Alembert representation identifies the reflection with
`dAlembert c φ_odd ψ_odd`; restriction to `x ≥ 0` gives (3.18).
-/

/-- The odd reflection, in the spatial variable, of a two-variable function:
`oddReflection v x t = v x t` for `x ≥ 0` and `= -v (-x) t` for `x < 0`. This
is the two-variable device of the chapter proof of Theorem 3.3, with the time
variable as a parameter. -/
noncomputable def oddReflection (v : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x t => if 0 ≤ x then v x t else -v (-x) t

/-- The odd reflection agrees with `v` on the right half-plane `x ≥ 0`. -/
theorem oddReflection_apply_of_nonneg (v : ℝ → ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x)
    (t : ℝ) : oddReflection v x t = v x t :=
  if_pos hx

/-- The odd reflection agrees with `-v(-·,·)` on the left half-plane
(`lem:wave-oddreflect-nonpos`): for `x < 0` this is the second branch of the
definition; at `x = 0` both sides vanish by the boundary condition
`v(0,t) = 0`. -/
theorem IsSolutionWaveBVP1D.oddReflection_apply_of_nonpos {c : ℝ} {φ ψ : ℝ → ℝ}
    {v : ℝ → ℝ → ℝ} (hv : IsSolutionWaveBVP1D c φ ψ v) {x : ℝ} (hx : x ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) : oddReflection v x t = -v (-x) t := by
  rcases hx.lt_or_eq with h | rfl
  · exact if_neg (not_le.mpr h)
  · simp [oddReflection, hv.boundary t ht]

/-- Initial displacement of the odd reflection: the odd extension of `φ`. -/
theorem IsSolutionWaveBVP1D.oddReflection_initPos {c : ℝ} {φ ψ : ℝ → ℝ}
    {v : ℝ → ℝ → ℝ} (hv : IsSolutionWaveBVP1D c φ ψ v) (x : ℝ) :
    oddReflection v x 0 = oddExtension φ x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [oddReflection_apply_of_nonneg v hx, oddExtension_apply_of_nonneg φ hx,
      hv.initPos x hx]
  · rw [show oddReflection v x 0 = -v (-x) 0 from if_neg (not_le.mpr hx),
      show oddExtension φ x = -φ (-x) from if_neg (not_le.mpr hx),
      hv.initPos (-x) (by linarith)]

/-- Initial velocity of the odd reflection: the odd extension of `ψ`. -/
theorem IsSolutionWaveBVP1D.oddReflection_initVel {c : ℝ} {φ ψ : ℝ → ℝ}
    {v : ℝ → ℝ → ℝ} (hv : IsSolutionWaveBVP1D c φ ψ v) (x : ℝ) :
    tderiv (oddReflection v) x 0 = oddExtension ψ x := by
  rcases le_or_gt 0 x with hx | hx
  · have h : (fun τ => oddReflection v x τ) = fun τ => v x τ :=
      funext fun τ => if_pos hx
    rw [tderiv, h, oddExtension_apply_of_nonneg ψ hx, ← hv.initVel x hx, tderiv]
  · have h : (fun τ => oddReflection v x τ) = fun τ => -v (-x) τ :=
      funext fun τ => if_neg (not_le.mpr hx)
    rw [tderiv, h, show oddExtension ψ x = -ψ (-x) from if_neg (not_le.mpr hx),
      ← hv.initVel (-x) (by linarith), tderiv]
    exact deriv.fun_neg ..

/-- Scaffold stub (`lem:wave-oddreflect-c2`): **joint `C²` regularity of the
odd reflection** on the closed upper half-plane. The boundary condition
`v(0,t) = 0` kills the even-order `t`-derivatives of `v` along `x = 0`, and
the wave equation up to the boundary (via continuity of the second derivatives
on the closed quadrant) forces `v_xx(0,t) = c⁻² v_tt(0,t) = 0` — the
two-variable analogue of the compatibility `φ(0) = φ''(0) = 0` in
`Wave.contDiff_two_oddExtension`, with `t` as a parameter. -/
theorem IsSolutionWaveBVP1D.contDiffOn_oddReflection {c : ℝ} (hc : 0 < c)
    {φ ψ : ℝ → ℝ} {v : ℝ → ℝ → ℝ} (hv : IsSolutionWaveBVP1D c φ ψ v) :
    ContDiffOn ℝ 2 (Function.uncurry (oddReflection v))
      (Set.univ ×ˢ Set.Ici 0) := by
  sorry

/-- (`lem:wave-oddreflect-solves`): **the odd reflection satisfies the wave
equation** on the open upper half-plane. For `x > 0` this is the equation for
`v`; for `x < 0` both sides pick up a sign through the reflection; at `x = 0`
both sides vanish outright — the pure time derivatives die on the axis by the
boundary condition `v(0,·) = 0`, and the spatial slice `ξ ↦ ∂ₓṽ(ξ,t)` is an
even function, so its `deriv` at `0` is `0` unconditionally (`deriv_comp_neg`
needs no differentiability). -/
theorem IsSolutionWaveBVP1D.oddReflection_waveEq {c : ℝ} (_hc : 0 < c)
    {φ ψ : ℝ → ℝ} {v : ℝ → ℝ → ℝ} (hv : IsSolutionWaveBVP1D c φ ψ v)
    (x t : ℝ) (ht : 0 < t) :
    tderiv (tderiv (oddReflection v)) x t
      = c ^ 2 * xderiv (xderiv (oddReflection v)) x t := by
  -- time derivatives commute with the reflection, branch by branch: the time
  -- slice at fixed `y` is literally `v y ·` (for `y ≥ 0`) resp. `-v (-y) ·`
  -- (for `y < 0`), so no eventual-equality is needed.
  have htd_pos : ∀ y : ℝ, 0 ≤ y → ∀ τ : ℝ,
      tderiv (oddReflection v) y τ = tderiv v y τ := by
    intro y hy τ
    have h : (fun σ => oddReflection v y σ) = fun σ => v y σ :=
      funext fun σ => oddReflection_apply_of_nonneg v hy σ
    show deriv (fun σ => oddReflection v y σ) τ = deriv (fun σ => v y σ) τ
    rw [h]
  have htd_neg : ∀ y : ℝ, y < 0 → ∀ τ : ℝ,
      tderiv (oddReflection v) y τ = -tderiv v (-y) τ := by
    intro y hy τ
    have h : (fun σ => oddReflection v y σ) = fun σ => -v (-y) σ :=
      funext fun σ => if_neg (not_le.mpr hy)
    show deriv (fun σ => oddReflection v y σ) τ = -deriv (fun σ => v (-y) σ) τ
    rw [h]
    exact deriv.fun_neg ..
  -- spatial derivative through the reflection: even reflection of `∂ₓv`.
  -- Here the agreement is only local (on the open half-lines), so the slice
  -- derivatives transfer through `Filter.EventuallyEq.deriv_eq`.
  have hxd_pos : ∀ ξ : ℝ, 0 < ξ → ∀ τ : ℝ,
      xderiv (oddReflection v) ξ τ = xderiv v ξ τ := by
    intro ξ hξ τ
    have heq : (fun η => oddReflection v η τ) =ᶠ[nhds ξ] fun η => v η τ := by
      filter_upwards [Ioi_mem_nhds hξ] with η hη
      exact oddReflection_apply_of_nonneg v hη.le τ
    show deriv (fun η => oddReflection v η τ) ξ = deriv (fun η => v η τ) ξ
    exact heq.deriv_eq
  have hxd_neg : ∀ ξ : ℝ, ξ < 0 → ∀ τ : ℝ,
      xderiv (oddReflection v) ξ τ = xderiv v (-ξ) τ := by
    intro ξ hξ τ
    have heq : (fun η => oddReflection v η τ) =ᶠ[nhds ξ] fun η => -v (-η) τ := by
      filter_upwards [Iio_mem_nhds hξ] with η hη
      exact if_neg (not_le.mpr hη)
    show deriv (fun η => oddReflection v η τ) ξ = deriv (fun η => v η τ) (-ξ)
    rw [heq.deriv_eq]
    have h1 : deriv (fun η : ℝ => -v (-η) τ) ξ
        = -deriv (fun η : ℝ => v (-η) τ) ξ := deriv.fun_neg ..
    have h2 : deriv (fun η : ℝ => v (-η) τ) ξ
        = -deriv (fun η => v η τ) (-ξ) := by
      simpa using deriv_comp_neg (fun η => v η τ) ξ
    rw [h1, h2, neg_neg]
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · -- left half-plane: both second derivatives pick up one sign through the
    -- reflection, so the equation for `v` at `(-x, t)` transfers.
    have hL : tderiv (tderiv (oddReflection v)) x t = -tderiv (tderiv v) (-x) t := by
      have h1 : (fun τ => tderiv (oddReflection v) x τ)
          = fun τ => -tderiv v (-x) τ :=
        funext fun τ => htd_neg x hx τ
      show deriv (fun τ => tderiv (oddReflection v) x τ) t
          = -deriv (fun τ => tderiv v (-x) τ) t
      rw [h1]
      exact deriv.fun_neg ..
    have hR : xderiv (xderiv (oddReflection v)) x t = -xderiv (xderiv v) (-x) t := by
      have heq : (fun ξ => xderiv (oddReflection v) ξ t)
          =ᶠ[nhds x] fun ξ => xderiv v (-ξ) t := by
        filter_upwards [Iio_mem_nhds hx] with ξ hξ
        exact hxd_neg ξ hξ t
      show deriv (fun ξ => xderiv (oddReflection v) ξ t) x
          = -deriv (fun ξ => xderiv v ξ t) (-x)
      rw [heq.deriv_eq]
      simpa using deriv_comp_neg (fun ξ => xderiv v ξ t) x
    rw [hL, hR, hv.waveEq (-x) t (neg_pos.mpr hx) ht]
    ring
  · -- the axis: both sides vanish. The pure time derivatives die because
    -- `v(0,·) ≡ 0` on `[0,∞)` (boundary condition), and the spatial slice of
    -- `∂ₓṽ` is even, so its `deriv` at `0` vanishes unconditionally.
    have hv0 : ∀ τ : ℝ, 0 < τ → tderiv v 0 τ = 0 := by
      intro τ hτ
      have heq : (fun σ => v 0 σ) =ᶠ[nhds τ] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hτ] with σ hσ
        exact hv.boundary σ hσ.le
      show deriv (fun σ => v 0 σ) τ = 0
      rw [heq.deriv_eq, deriv_const]
    have hL : tderiv (tderiv (oddReflection v)) 0 t = 0 := by
      have h1 : (fun τ => tderiv (oddReflection v) 0 τ) = fun τ => tderiv v 0 τ :=
        funext fun τ => htd_pos 0 le_rfl τ
      have heq : (fun τ => tderiv v 0 τ) =ᶠ[nhds t] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds ht] with τ hτ
        exact hv0 τ hτ
      show deriv (fun τ => tderiv (oddReflection v) 0 τ) t = 0
      rw [h1, heq.deriv_eq, deriv_const]
    have heven : (fun ξ => xderiv (oddReflection v) (-ξ) t)
        = fun ξ => xderiv (oddReflection v) ξ t := by
      funext ξ
      rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
      · rw [hxd_pos (-ξ) (neg_pos.mpr hξ) t, hxd_neg ξ hξ t]
      · rw [neg_zero]
      · rw [hxd_neg (-ξ) (neg_lt_zero.mpr hξ) t, neg_neg, hxd_pos ξ hξ t]
    have hR : xderiv (xderiv (oddReflection v)) 0 t = 0 := by
      have h2 : deriv (fun ξ : ℝ => xderiv (oddReflection v) (-ξ) t) 0
          = -deriv (fun ξ => xderiv (oddReflection v) ξ t) 0 := by
        simpa using deriv_comp_neg (fun ξ => xderiv (oddReflection v) ξ t) 0
      rw [heven] at h2
      show deriv (fun ξ => xderiv (oddReflection v) ξ t) 0 = 0
      linarith
    rw [hL, hR, mul_zero]
  · -- right half-plane: the reflection agrees with `v` near `(x, t)`.
    have hL : tderiv (tderiv (oddReflection v)) x t = tderiv (tderiv v) x t := by
      have h1 : (fun τ => tderiv (oddReflection v) x τ) = fun τ => tderiv v x τ :=
        funext fun τ => htd_pos x hx.le τ
      show deriv (fun τ => tderiv (oddReflection v) x τ) t
          = deriv (fun τ => tderiv v x τ) t
      rw [h1]
    have hR : xderiv (xderiv (oddReflection v)) x t = xderiv (xderiv v) x t := by
      have heq : (fun ξ => xderiv (oddReflection v) ξ t)
          =ᶠ[nhds x] fun ξ => xderiv v ξ t := by
        filter_upwards [Ioi_mem_nhds hx] with ξ hξ
        exact hxd_pos ξ hξ t
      show deriv (fun ξ => xderiv (oddReflection v) ξ t) x
          = deriv (fun ξ => xderiv v ξ t) x
      exact heq.deriv_eq
    rw [hL, hR]
    exact hv.waveEq x t hx ht

/-- **Half-plane d'Alembert representation** — a `C²` solution of the wave
equation on the closed upper half-plane taking data `φ, ψ` at `t = 0` equals
the d'Alembert expression for `t ≥ 0`.

Thin wrapper reducing to `IsSolutionWaveIVPHalfPlane1D.eq_dAlembert`
(`thm:wave-halfplane-dalembert` in `PDE.Basics.Wave.WaveIVP1D`): the four
hypotheses are exactly the fields of `IsSolutionWaveIVPHalfPlane1D`, packaged
by anonymous constructor. Kept `private` so it never becomes load-bearing
API — callers outside this file should use the `WaveIVP1D` theorem directly. -/
private theorem eq_dAlembert_of_halfPlane {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ}
    (hreg : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ici 0))
    (hwave : ∀ x t : ℝ, 0 < t →
      tderiv (tderiv u) x t = c ^ 2 * xderiv (xderiv u) x t)
    (hinit : ∀ x : ℝ, u x 0 = φ x) (hvel : ∀ x : ℝ, tderiv u x 0 = ψ x)
    {x t : ℝ} (ht : 0 ≤ t) :
    u x t = dAlembert c φ ψ x t :=
  IsSolutionWaveIVPHalfPlane1D.eq_dAlembert hc
    ⟨hreg, hwave, hinit, hvel⟩ ht

/-- **Solution formula for the fixed-end BVP/IVP** (Theorem 3.3). Every
classical solution of the boundary/initial value problem (3.17) is given on the
quadrant `x, t ≥ 0` by the odd-reflection D'Alembert expression (3.18) — hence,
via `Wave.fixedEndSolution_eq_of_le_x` and `Wave.fixedEndSolution_eq_of_le_t`,
by the piecewise formula (3.21).

Glue over the odd-reflection scaffold: the reflection of `v` is a half-plane
solution with data `φ_odd, ψ_odd`, so the half-plane d'Alembert representation
applies, and on `x ≥ 0` the reflection is `v` while the d'Alembert expression
of the odd extensions is `fixedEndSolution`. -/
theorem IsSolutionWaveBVP1D.eq_fixedEndSolution {c : ℝ} (hc : 0 < c)
    {φ ψ : ℝ → ℝ} {v : ℝ → ℝ → ℝ} (hv : IsSolutionWaveBVP1D c φ ψ v)
    {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    v x t = fixedEndSolution c φ ψ x t := by
  have h := eq_dAlembert_of_halfPlane hc (hv.contDiffOn_oddReflection hc)
    (hv.oddReflection_waveEq hc) hv.oddReflection_initPos
    hv.oddReflection_initVel (x := x) ht
  rw [← oddReflection_apply_of_nonneg v hx t, h]
  rfl

/-- **Uniqueness for the fixed-end BVP/IVP.** Two classical solutions of the
boundary/initial value problem (3.17) with the same data agree on the quadrant
`x, t ≥ 0`. -/
theorem IsSolutionWaveBVP1D.unique {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ}
    {u v : ℝ → ℝ → ℝ} (hu : IsSolutionWaveBVP1D c φ ψ u)
    (hv : IsSolutionWaveBVP1D c φ ψ v) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    u x t = v x t := by
  rw [hu.eq_fixedEndSolution hc hx ht, hv.eq_fixedEndSolution hc hx ht]

end Wave
