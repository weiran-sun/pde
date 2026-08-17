import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The General Solution of the 1D Wave Equation

This file formalizes the general solution of the one-dimensional wave equation
`u_tt - c² u_xx = 0`, following Rustum Choksi's *Partial Differential Equations:
A First Course*, Section 3.2.

Main results:
* `Wave.IsWaveSolution1D` — the classical (`C²`) solution predicate for the 1D
  wave equation on all of `ℝ × ℝ`.
* `Wave.isWaveSolution1D_travelingWaves` — for `C²` profiles `F`, `G`, the
  superposition `u(x,t) = F(x + ct) + G(x - ct)` of a backward and a forward
  traveling wave solves the wave equation.
* `Wave.exists_add_decomposition_of_mixed_deriv_eq_zero` — the general solution
  of `v_ζη = 0` is `v(ζ,η) = f(ζ) + g(η)`.
* `Wave.IsWaveSolution1D.exists_travelingWave_decomposition` — conversely,
  every `C²` solution of the wave equation has the form
  `u(x,t) = F(x + ct) + G(x - ct)` with `F`, `G` of class `C²`
  (Proposition 3.2.1); `Wave.isWaveSolution1D_iff_exists_travelingWaves` is
  the two-way version.

Partial derivatives of a two-variable function `u : ℝ → ℝ → ℝ` are expressed
through one-variable `deriv` slices (`Wave.xderiv`, `Wave.tderiv`), matching
the convention used in `PDE.Basics.Heat`.

## Reference

Chapter 3.2, ["Partial Differential Equations, A First Course"](https://bookstore.ams.org/amstext-54/)
by Rustum Choksi.
-/

open Real

namespace Wave

/-!
### 1. Partial-derivative shorthands

For `u = u(x, t)` we write `xderiv u` for `∂u/∂x` and `tderiv u` for `∂u/∂t`,
both again functions of `(x, t)`, so that second derivatives compose:
`xderiv (xderiv u) = u_xx`, `tderiv (tderiv u) = u_tt`.
-/

/-- Partial derivative of `u = u(x, t)` in the first (spatial) variable. -/
noncomputable def xderiv (u : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun ξ => u ξ t) x

/-- Partial derivative of `u = u(x, t)` in the second (temporal) variable. -/
noncomputable def tderiv (u : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun τ => u x τ) t

/-!
### 1b. Slice derivatives via the joint Fréchet derivative

For a jointly differentiable `u`, the partial derivatives `xderiv u` and
`tderiv u` are the joint Fréchet derivative evaluated at the coordinate
directions `(1, 0)` and `(0, 1)`. This lets joint `C²` regularity flow into
the one-variable slices.
-/

/-- The `t`-slice `τ ↦ u x τ` of a jointly differentiable function has
derivative `fderiv ℝ U (x, t) (0, 1)`, where `U` is the uncurried `u`. -/
lemma hasDerivAt_slice_snd {u : ℝ → ℝ → ℝ} {x t : ℝ}
    (hU : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, t)) :
    HasDerivAt (fun τ => u x τ)
      (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, t) (0, 1)) t := by
  have h1 : HasDerivAt (fun τ : ℝ => ((x : ℝ), τ)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  exact hU.hasFDerivAt.comp_hasDerivAt t h1

/-- The `x`-slice `ξ ↦ u ξ t` of a jointly differentiable function has
derivative `fderiv ℝ U (x, t) (1, 0)`, where `U` is the uncurried `u`. -/
lemma hasDerivAt_slice_fst {u : ℝ → ℝ → ℝ} {x t : ℝ}
    (hU : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, t)) :
    HasDerivAt (fun ξ => u ξ t)
      (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, t) (1, 0)) x := by
  have h1 : HasDerivAt (fun ξ : ℝ => (ξ, (t : ℝ))) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  exact hU.hasFDerivAt.comp_hasDerivAt x h1

/-- `tderiv` through the joint Fréchet derivative. -/
lemma tderiv_eq_fderiv {u : ℝ → ℝ → ℝ} {x t : ℝ}
    (hU : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, t)) :
    tderiv u x t = fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, t) (0, 1) :=
  (hasDerivAt_slice_snd hU).deriv

/-- `xderiv` through the joint Fréchet derivative. -/
lemma xderiv_eq_fderiv {u : ℝ → ℝ → ℝ} {x t : ℝ}
    (hU : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, t)) :
    xderiv u x t = fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, t) (1, 0) :=
  (hasDerivAt_slice_fst hU).deriv

/-- If `u` is jointly `C²` then `tderiv u` is jointly `C¹`. -/
lemma contDiff_one_tderiv {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => tderiv u p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => tderiv u p.1 p.2) =
      fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p (0, 1) := by
    funext p
    exact tderiv_eq_fderiv ((hu.differentiable (by norm_num)) (p.1, p.2))
  rw [h]
  exact (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- If `u` is jointly `C²` then `xderiv u` is jointly `C¹`. -/
lemma contDiff_one_xderiv {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => xderiv u p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => xderiv u p.1 p.2) =
      fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p (1, 0) := by
    funext p
    exact xderiv_eq_fderiv ((hu.differentiable (by norm_num)) (p.1, p.2))
  rw [h]
  exact (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- Sum rule for `tderiv` at a point of joint differentiability. -/
lemma tderiv_add {u v : ℝ → ℝ → ℝ} {x t : ℝ}
    (hu : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, t))
    (hv : DifferentiableAt ℝ (fun p : ℝ × ℝ => v p.1 p.2) (x, t)) :
    tderiv (fun x t => u x t + v x t) x t = tderiv u x t + tderiv v x t :=
  ((hasDerivAt_slice_snd hu).add (hasDerivAt_slice_snd hv)).deriv.trans
    (by rw [← tderiv_eq_fderiv hu, ← tderiv_eq_fderiv hv])

/-- Sum rule for `xderiv` at a point of joint differentiability. -/
lemma xderiv_add {u v : ℝ → ℝ → ℝ} {x t : ℝ}
    (hu : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, t))
    (hv : DifferentiableAt ℝ (fun p : ℝ × ℝ => v p.1 p.2) (x, t)) :
    xderiv (fun x t => u x t + v x t) x t = xderiv u x t + xderiv v x t :=
  ((hasDerivAt_slice_fst hu).add (hasDerivAt_slice_fst hv)).deriv.trans
    (by rw [← xderiv_eq_fderiv hu, ← xderiv_eq_fderiv hv])

/-- Chain rule along an affine line: if `w` is jointly differentiable at
`(α s + β, γ s + δ)` then `s' ↦ w (α s' + β) (γ s' + δ)` has derivative
`α ⬝ w_x + γ ⬝ w_t` there. -/
lemma hasDerivAt_affine_slice {w : ℝ → ℝ → ℝ} {α β γ δ s : ℝ}
    (hw : DifferentiableAt ℝ (fun p : ℝ × ℝ => w p.1 p.2) (α * s + β, γ * s + δ)) :
    HasDerivAt (fun s' => w (α * s' + β) (γ * s' + δ))
      (α * xderiv w (α * s + β) (γ * s + δ) +
        γ * tderiv w (α * s + β) (γ * s + δ)) s := by
  have hline : HasDerivAt (fun s' : ℝ => (α * s' + β, γ * s' + δ)) (α, γ) s := by
    have h1 : HasDerivAt (fun s' : ℝ => α * s' + β) α s := by
      simpa using (((hasDerivAt_id s).const_mul α).add_const β)
    have h2 : HasDerivAt (fun s' : ℝ => γ * s' + δ) γ s := by
      simpa using (((hasDerivAt_id s).const_mul γ).add_const δ)
    exact h1.prodMk h2
  have hcomp := hw.hasFDerivAt.comp_hasDerivAt s hline
  have hsplit :
      fderiv ℝ (fun p : ℝ × ℝ => w p.1 p.2) (α * s + β, γ * s + δ) (α, γ) =
        α * xderiv w (α * s + β) (γ * s + δ) +
          γ * tderiv w (α * s + β) (γ * s + δ) := by
    have hαγ : ((α, γ) : ℝ × ℝ) = α • ((1 : ℝ), (0 : ℝ)) + γ • ((0 : ℝ), (1 : ℝ)) := by
      simp
    rw [xderiv_eq_fderiv hw, tderiv_eq_fderiv hw, hαγ, map_add, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul]
  exact hsplit ▸ hcomp

/-- The mixed partial `∂ₓ ∂ₜ u` is the second Fréchet derivative applied to
`(1,0)` then `(0,1)` (helper for Clairaut). -/
lemma xderiv_tderiv_eq_fderiv2 {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) (x t : ℝ) :
    xderiv (tderiv u) x t =
      fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2)) (x, t) (1, 0) (0, 1) := by
  have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => tderiv u p.1 p.2) (x, t) :=
    ((contDiff_one_tderiv hu).differentiable (by norm_num)) _
  rw [xderiv_eq_fderiv hdiff]
  have heq : (fun p : ℝ × ℝ => tderiv u p.1 p.2) =
      fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p (0, 1) := by
    funext p
    exact tderiv_eq_fderiv ((hu.differentiable (by norm_num)) _)
  rw [heq, fderiv_clm_apply
    (((hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) _)
    (differentiableAt_const _)]
  simp

/-- The mixed partial `∂ₜ ∂ₓ u` is the second Fréchet derivative applied to
`(0,1)` then `(1,0)` (helper for Clairaut). -/
lemma tderiv_xderiv_eq_fderiv2 {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) (x t : ℝ) :
    tderiv (xderiv u) x t =
      fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2)) (x, t) (0, 1) (1, 0) := by
  have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => xderiv u p.1 p.2) (x, t) :=
    ((contDiff_one_xderiv hu).differentiable (by norm_num)) _
  rw [tderiv_eq_fderiv hdiff]
  have heq : (fun p : ℝ × ℝ => xderiv u p.1 p.2) =
      fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p (1, 0) := by
    funext p
    exact xderiv_eq_fderiv ((hu.differentiable (by norm_num)) _)
  rw [heq, fderiv_clm_apply
    (((hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) _)
    (differentiableAt_const _)]
  simp

/-- **Clairaut / Schwarz**: for a jointly `C²` function of two real variables
the mixed partial derivatives agree. -/
lemma tderiv_xderiv_comm {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) (x t : ℝ) :
    tderiv (xderiv u) x t = xderiv (tderiv u) x t := by
  have hsymm := second_derivative_symmetric
      (f := fun p : ℝ × ℝ => u p.1 p.2)
      (f' := fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2))
      (fun y => ((hu.differentiable (by norm_num)) y).hasFDerivAt)
      ((((hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
        ((x, t) : ℝ × ℝ)).hasFDerivAt)
  rw [xderiv_tderiv_eq_fderiv2 hu, tderiv_xderiv_eq_fderiv2 hu]
  exact hsymm _ _

/-!
### 2. Traveling waves and the solution predicate
-/

/-- The forward (right-moving) traveling wave with profile `G`:
`(x, t) ↦ G (x - c t)`. -/
noncomputable def forwardWave (c : ℝ) (G : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x t => G (x - c * t)

/-- The backward (left-moving) traveling wave with profile `F`:
`(x, t) ↦ F (x + c t)`. -/
noncomputable def backwardWave (c : ℝ) (F : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x t => F (x + c * t)

/-- A classical solution of the 1D wave equation with wave speed `c` on all of
`ℝ × ℝ`: the function `u = u(x, t)` is `C²` (jointly in both variables) and
satisfies `u_tt = c² u_xx` pointwise. -/
structure IsWaveSolution1D (c : ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)
  waveEq : ∀ x t, tderiv (tderiv u) x t = c ^ 2 * xderiv (xderiv u) x t

/-- The linear change of variables `(x, t) ↦ x + k t` is `C²`
(helper for `isWaveSolution1D_profileWave`). -/
private lemma contDiff_shiftMap (k : ℝ) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => p.1 + k * p.2) :=
  contDiff_fst.add (contDiff_const.mul contDiff_snd)

/-- `x`-derivative of a profile composed with the shift `x + k t`:
`∂ₓ G(x + kt) = G'(x + kt)` (helper, no differentiability needed since both
sides degenerate together). -/
lemma xderiv_profileWave (G : ℝ → ℝ) (k x t : ℝ) :
    xderiv (fun x t => G (x + k * t)) x t = deriv G (x + k * t) := by
  simpa [xderiv] using deriv_comp_add_const G (k * t) x

/-- `t`-derivative of a profile composed with the shift `x + k t`:
`∂ₜ G(x + kt) = k G'(x + kt)` (helper). -/
lemma tderiv_profileWave (G : ℝ → ℝ) (k x t : ℝ) :
    tderiv (fun x t => G (x + k * t)) x t = k * deriv G (x + k * t) := by
  have h1 := deriv_comp_mul_left k (fun s => G (x + s)) t
  have h2 := deriv_comp_const_add G x (k * t)
  simp only [smul_eq_mul] at h1
  calc tderiv (fun x t => G (x + k * t)) x t
      = k * deriv (fun s => G (x + s)) (k * t) := h1
    _ = k * deriv G (x + k * t) := by rw [h2]

/-- Any profile wave `(x, t) ↦ G (x + k t)` with `C²` profile and `k² = c²`
solves the 1D wave equation with speed `c` (covers the forward wave `k = -c`
and the backward wave `k = c` simultaneously). -/
lemma isWaveSolution1D_profileWave {c : ℝ} {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    {k : ℝ} (hk : k ^ 2 = c ^ 2) :
    IsWaveSolution1D c (fun x t => G (x + k * t)) := by
  refine ⟨hG.comp (contDiff_shiftMap k), fun x t => ?_⟩
  have hx : xderiv (fun x t => G (x + k * t)) = fun x t => deriv G (x + k * t) := by
    funext x t; exact xderiv_profileWave G k x t
  have ht : tderiv (fun x t => G (x + k * t)) = fun x t => k * deriv G (x + k * t) := by
    funext x t; exact tderiv_profileWave G k x t
  rw [hx, ht]
  calc tderiv (fun x t => k * deriv G (x + k * t)) x t
      = k * tderiv (fun x t => deriv G (x + k * t)) x t := by
        simp only [tderiv]; exact deriv_const_mul_field k
    _ = k * (k * deriv (deriv G) (x + k * t)) := by rw [tderiv_profileWave]
    _ = c ^ 2 * deriv (deriv G) (x + k * t) := by rw [← hk]; ring
    _ = c ^ 2 * xderiv (fun x t => deriv G (x + k * t)) x t := by
        rw [xderiv_profileWave]

/-- A forward traveling wave `G (x - ct)` with `C²` profile solves the 1D wave
equation. -/
theorem isWaveSolution1D_forwardWave {c : ℝ} {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) :
    IsWaveSolution1D c (forwardWave c G) := by
  have h : forwardWave c G = fun x t => G (x + -c * t) := by
    funext x t; simp [forwardWave, sub_eq_add_neg]
  rw [h]
  exact isWaveSolution1D_profileWave hG (by ring)

/-- A backward traveling wave `F (x + ct)` with `C²` profile solves the 1D wave
equation. -/
theorem isWaveSolution1D_backwardWave {c : ℝ} {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    IsWaveSolution1D c (backwardWave c F) := by
  have h : backwardWave c F = fun x t => F (x + c * t) := rfl
  rw [h]
  exact isWaveSolution1D_profileWave hF rfl

/-- Superposition principle: the sum of two classical solutions of the 1D wave
equation is again a classical solution. -/
theorem IsWaveSolution1D.add {c : ℝ} {u v : ℝ → ℝ → ℝ}
    (hu : IsWaveSolution1D c u) (hv : IsWaveSolution1D c v) :
    IsWaveSolution1D c (fun x t => u x t + v x t) := by
  have hud : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun q : ℝ × ℝ => u q.1 q.2) p :=
    fun p => (hu.contDiff.differentiable (by norm_num)) p
  have hvd : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun q : ℝ × ℝ => v q.1 q.2) p :=
    fun p => (hv.contDiff.differentiable (by norm_num)) p
  have htd : tderiv (fun x t => u x t + v x t) =
      fun x t => tderiv u x t + tderiv v x t := by
    funext x t; exact tderiv_add (hud (x, t)) (hvd (x, t))
  have hxd : xderiv (fun x t => u x t + v x t) =
      fun x t => xderiv u x t + xderiv v x t := by
    funext x t; exact xderiv_add (hud (x, t)) (hvd (x, t))
  have hutd : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun q : ℝ × ℝ => tderiv u q.1 q.2) p :=
    fun p => ((contDiff_one_tderiv hu.contDiff).differentiable (by norm_num)) p
  have hvtd : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun q : ℝ × ℝ => tderiv v q.1 q.2) p :=
    fun p => ((contDiff_one_tderiv hv.contDiff).differentiable (by norm_num)) p
  have huxd : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun q : ℝ × ℝ => xderiv u q.1 q.2) p :=
    fun p => ((contDiff_one_xderiv hu.contDiff).differentiable (by norm_num)) p
  have hvxd : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun q : ℝ × ℝ => xderiv v q.1 q.2) p :=
    fun p => ((contDiff_one_xderiv hv.contDiff).differentiable (by norm_num)) p
  refine ⟨(hu.contDiff.add hv.contDiff : _), fun x t => ?_⟩
  rw [htd, hxd, tderiv_add (hutd (x, t)) (hvtd (x, t)),
    xderiv_add (huxd (x, t)) (hvxd (x, t)), hu.waveEq, hv.waveEq]
  ring

/-- For arbitrary `C²` profiles `F` and `G`, the superposition
`u(x, t) = F (x + ct) + G (x - ct)` is a classical solution of the 1D wave
equation. This is the easy direction of Proposition 3.2.1. -/
theorem isWaveSolution1D_travelingWaves {c : ℝ} {F G : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) :
    IsWaveSolution1D c (fun x t => F (x + c * t) + G (x - c * t)) :=
  (isWaveSolution1D_backwardWave hF).add (isWaveSolution1D_forwardWave hG)

/-!
### 3. Characteristic coordinates

The change of variables `ζ = x + ct`, `η = x - ct` (inverted:
`x = (ζ + η)/2`, `t = (ζ - η)/(2c)`) turns the wave operator into a multiple
of the mixed second derivative `∂_ζ ∂_η`.
-/

/-- `u` expressed in the characteristic coordinates `ζ = x + ct`, `η = x - ct`:
`charCoords c u ζ η = u ((ζ + η)/2) ((ζ - η)/(2c))`. -/
noncomputable def charCoords (c : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun ζ η => u ((ζ + η) / 2) ((ζ - η) / (2 * c))

/-- The characteristic-coordinate expression of a `C²` function is `C²`
(the change of variables is linear). -/
theorem contDiff_charCoords {c : ℝ} {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => charCoords c u p.1 p.2) := by
  have hlin : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((p.1 + p.2) / 2, (p.1 - p.2) / (2 * c))) :=
    ((contDiff_fst.add contDiff_snd).div_const 2).prodMk
      ((contDiff_fst.sub contDiff_snd).div_const (2 * c))
  exact hu.comp hlin

/-- Derivative of the `ζ`-slice of `w` in characteristic coordinates:
`∂_ζ [w((ζ+η)/2, (ζ-η)/(2c))] = ½ w_x + (1/(2c)) w_t` (helper). -/
lemma hasDerivAt_charSlice_fst {c : ℝ} {w : ℝ → ℝ → ℝ} {ζ η : ℝ}
    (hw : DifferentiableAt ℝ (fun p : ℝ × ℝ => w p.1 p.2)
      ((ζ + η) / 2, (ζ - η) / (2 * c))) :
    HasDerivAt (fun ξ => w ((ξ + η) / 2) ((ξ - η) / (2 * c)))
      (1 / 2 * xderiv w ((ζ + η) / 2) ((ζ - η) / (2 * c)) +
        1 / (2 * c) * tderiv w ((ζ + η) / 2) ((ζ - η) / (2 * c))) ζ := by
  have hp1 : (1 : ℝ) / 2 * ζ + η / 2 = (ζ + η) / 2 := by ring
  have hp2 : (1 : ℝ) / (2 * c) * ζ + -(η / (2 * c)) = (ζ - η) / (2 * c) := by ring
  have h := hasDerivAt_affine_slice (w := w) (α := 1 / 2) (β := η / 2)
    (γ := 1 / (2 * c)) (δ := -(η / (2 * c))) (s := ζ) (by rw [hp1, hp2]; exact hw)
  rw [hp1, hp2] at h
  have hfun : (fun s' => w (1 / 2 * s' + η / 2) (1 / (2 * c) * s' + -(η / (2 * c)))) =
      fun ξ => w ((ξ + η) / 2) ((ξ - η) / (2 * c)) := by
    funext ξ
    rw [show (1 : ℝ) / 2 * ξ + η / 2 = (ξ + η) / 2 by ring,
      show (1 : ℝ) / (2 * c) * ξ + -(η / (2 * c)) = (ξ - η) / (2 * c) by ring]
  rwa [hfun] at h

/-- Derivative of the `η`-slice of `w` in characteristic coordinates:
`∂_η [w((ζ+η)/2, (ζ-η)/(2c))] = ½ w_x − (1/(2c)) w_t` (helper). -/
lemma hasDerivAt_charSlice_snd {c : ℝ} {w : ℝ → ℝ → ℝ} {ζ η : ℝ}
    (hw : DifferentiableAt ℝ (fun p : ℝ × ℝ => w p.1 p.2)
      ((ζ + η) / 2, (ζ - η) / (2 * c))) :
    HasDerivAt (fun τ => w ((ζ + τ) / 2) ((ζ - τ) / (2 * c)))
      (1 / 2 * xderiv w ((ζ + η) / 2) ((ζ - η) / (2 * c)) -
        1 / (2 * c) * tderiv w ((ζ + η) / 2) ((ζ - η) / (2 * c))) η := by
  have hp1 : (1 : ℝ) / 2 * η + ζ / 2 = (ζ + η) / 2 := by ring
  have hp2 : -(1 / (2 * c)) * η + ζ / (2 * c) = (ζ - η) / (2 * c) := by ring
  have h := hasDerivAt_affine_slice (w := w) (α := 1 / 2) (β := ζ / 2)
    (γ := -(1 / (2 * c))) (δ := ζ / (2 * c)) (s := η) (by rw [hp1, hp2]; exact hw)
  rw [hp1, hp2] at h
  have hfun : (fun s' => w (1 / 2 * s' + ζ / 2) (-(1 / (2 * c)) * s' + ζ / (2 * c))) =
      fun τ => w ((ζ + τ) / 2) ((ζ - τ) / (2 * c)) := by
    funext τ
    rw [show (1 : ℝ) / 2 * τ + ζ / 2 = (ζ + τ) / 2 by ring,
      show -(1 / (2 * c)) * τ + ζ / (2 * c) = (ζ - τ) / (2 * c) by ring]
  rw [hfun] at h
  have hval : 1 / 2 * xderiv w ((ζ + η) / 2) ((ζ - η) / (2 * c)) +
      -(1 / (2 * c)) * tderiv w ((ζ + η) / 2) ((ζ - η) / (2 * c)) =
      1 / 2 * xderiv w ((ζ + η) / 2) ((ζ - η) / (2 * c)) -
        1 / (2 * c) * tderiv w ((ζ + η) / 2) ((ζ - η) / (2 * c)) := by ring
  rwa [hval] at h

/-- First characteristic partial: `∂_η (charCoords c u) = ½ u_x − (1/(2c)) u_t`
at the transported point (helper). -/
lemma tderiv_charCoords_eq {c : ℝ} {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) (ζ η : ℝ) :
    tderiv (charCoords c u) ζ η =
      1 / 2 * xderiv u ((ζ + η) / 2) ((ζ - η) / (2 * c)) -
        1 / (2 * c) * tderiv u ((ζ + η) / 2) ((ζ - η) / (2 * c)) := by
  have hw : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2)
      ((ζ + η) / 2, (ζ - η) / (2 * c)) := (hu.differentiable (by norm_num)) _
  exact (hasDerivAt_charSlice_snd hw).deriv

/-- In characteristic coordinates the wave operator becomes a multiple of the
mixed second derivative: for `C²` functions `u` and `c ≠ 0`,
`(∂_ζ ∂_η (charCoords c u))(ζ, η) = -(1/(4c²)) (u_tt - c² u_xx)` evaluated at
`x = (ζ + η)/2`, `t = (ζ - η)/(2c)`. The chain-rule computation
`∂_x = ∂_ζ + ∂_η`, `∂_t = c ∂_ζ - c ∂_η` gives
`u_tt - c² u_xx = -4c² ∂_ζ ∂_η u`. -/
theorem tderiv_xderiv_charCoords {c : ℝ} (hc : c ≠ 0) {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) (ζ η : ℝ) :
    xderiv (tderiv (charCoords c u)) ζ η =
      -(1 / (4 * c ^ 2)) *
        (tderiv (tderiv u) ((ζ + η) / 2) ((ζ - η) / (2 * c)) -
          c ^ 2 * xderiv (xderiv u) ((ζ + η) / 2) ((ζ - η) / (2 * c))) := by
  -- Rewrite the inner slice function via `tderiv_charCoords_eq`.
  have hfun : (fun ξ => tderiv (charCoords c u) ξ η) =
      fun ξ => 1 / 2 * xderiv u ((ξ + η) / 2) ((ξ - η) / (2 * c)) -
        1 / (2 * c) * tderiv u ((ξ + η) / 2) ((ξ - η) / (2 * c)) := by
    funext ξ
    exact tderiv_charCoords_eq hu ξ η
  -- Differentiate each summand along the `ζ`-characteristic slice.
  have hxd : DifferentiableAt ℝ (fun p : ℝ × ℝ => xderiv u p.1 p.2)
      ((ζ + η) / 2, (ζ - η) / (2 * c)) :=
    ((contDiff_one_xderiv hu).differentiable (by norm_num)) _
  have htd : DifferentiableAt ℝ (fun p : ℝ × ℝ => tderiv u p.1 p.2)
      ((ζ + η) / 2, (ζ - η) / (2 * c)) :=
    ((contDiff_one_tderiv hu).differentiable (by norm_num)) _
  have h1 := (hasDerivAt_charSlice_fst (w := xderiv u) hxd).const_mul (1 / 2 : ℝ)
  have h2 := (hasDerivAt_charSlice_fst (w := tderiv u) htd).const_mul (1 / (2 * c) : ℝ)
  have hderiv : deriv (fun ξ =>
      1 / 2 * xderiv u ((ξ + η) / 2) ((ξ - η) / (2 * c)) -
        1 / (2 * c) * tderiv u ((ξ + η) / 2) ((ξ - η) / (2 * c))) ζ =
      1 / 2 * (1 / 2 * xderiv (xderiv u) ((ζ + η) / 2) ((ζ - η) / (2 * c)) +
          1 / (2 * c) * tderiv (xderiv u) ((ζ + η) / 2) ((ζ - η) / (2 * c))) -
        1 / (2 * c) * (1 / 2 * xderiv (tderiv u) ((ζ + η) / 2) ((ζ - η) / (2 * c)) +
          1 / (2 * c) * tderiv (tderiv u) ((ζ + η) / 2) ((ζ - η) / (2 * c))) :=
    (h1.sub h2).deriv
  rw [xderiv, hfun, hderiv]
  -- Mixed partials commute (Clairaut), then pure field algebra.
  rw [tderiv_xderiv_comm hu]
  field_simp
  ring

/-!
### 4. The general solution of `v_ζη = 0`
-/

/-- General solution of the PDE `v_ζη = 0` on `ℝ²`: a `C²` function whose
mixed second derivative `∂_ζ (∂_η v)` vanishes identically splits as
`v(ζ, η) = f(ζ) + g(η)` with `f`, `g` of class `C²`. Concretely one may take
`f(ζ) = v(ζ, 0)` and `g(η) = ∫_0^η (∂_η v)(0, s) ds`. -/
theorem exists_add_decomposition_of_mixed_deriv_eq_zero {v : ℝ → ℝ → ℝ}
    (hv : ContDiff ℝ 2 (fun p : ℝ × ℝ => v p.1 p.2))
    (hmixed : ∀ ζ η, xderiv (tderiv v) ζ η = 0) :
    ∃ f g : ℝ → ℝ, ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧
      ∀ ζ η, v ζ η = f ζ + g η := by
  -- `∂_η v` is jointly `C¹`.
  have htv : ContDiff ℝ 1 (fun p : ℝ × ℝ => tderiv v p.1 p.2) :=
    contDiff_one_tderiv hv
  -- With zero `ζ`-derivative, `∂_η v` is constant in `ζ`: `∂_η v(ζ,η) = h(η)`.
  have hconst : ∀ ζ η, tderiv v ζ η = tderiv v 0 η := by
    intro ζ η
    have hdiff : Differentiable ℝ (fun ξ => tderiv v ξ η) := by
      have := (htv.differentiable (by norm_num)).comp
        ((differentiable_id (𝕜 := ℝ) (E := ℝ)).prodMk (differentiable_const η))
      exact this
    exact is_const_of_deriv_eq_zero hdiff (fun ξ => hmixed ξ η) ζ 0
  -- `h(η) = ∂_η v(0, η)` is `C¹`.
  set h : ℝ → ℝ := fun η => tderiv v 0 η with hh_def
  have hh : ContDiff ℝ 1 h := by
    have := htv.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)
    exact this
  -- `g(η) = ∫_0^η h`, the antiderivative of `h`, is `C²` with `g' = h`, `g 0 = 0`.
  set g : ℝ → ℝ := fun η => ∫ s in (0 : ℝ)..η, h s with hg_def
  have hg_deriv : ∀ η, HasDerivAt g (h η) η := fun η =>
    ((hh.continuous).integral_hasStrictDerivAt 0 η).hasDerivAt
  have hg_deriv_eq : deriv g = h := funext fun η => (hg_deriv η).deriv
  have hg : ContDiff ℝ 2 g := by
    rw [show ((2 : WithTop ℕ∞) = 1 + 1) from rfl, contDiff_succ_iff_deriv]
    exact ⟨fun η => (hg_deriv η).differentiableAt, by simp, hg_deriv_eq ▸ hh⟩
  have hg_zero : g 0 = 0 := intervalIntegral.integral_same
  -- `f(ζ) = v(ζ, 0)` is `C²` as a slice.
  set f : ℝ → ℝ := fun ζ => v ζ 0 with hf_def
  have hf : ContDiff ℝ 2 f := by
    have := hv.comp ((contDiff_id (𝕜 := ℝ) (E := ℝ)).prodMk (contDiff_const (c := (0 : ℝ))))
    exact this
  refine ⟨f, g, hf, hg, fun ζ η => ?_⟩
  -- For fixed `ζ`, `η ↦ v ζ η - g η` has zero derivative, hence is constant.
  have hzero : ∀ η', deriv (fun η'' => v ζ η'' - g η'') η' = 0 := by
    intro η'
    have hslice : HasDerivAt (fun η'' => v ζ η'') (tderiv v ζ η') η' := by
      have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => v p.1 p.2) (ζ, η') :=
        (hv.differentiable (by norm_num)) _
      exact (tderiv_eq_fderiv hd) ▸ hasDerivAt_slice_snd hd
    have hsub : HasDerivAt (fun η'' => v ζ η'' - g η'') (tderiv v ζ η' - h η') η' :=
      hslice.sub (hg_deriv η')
    rw [hsub.deriv, hconst ζ η']
    simp [hh_def]
  have hdiff : Differentiable ℝ (fun η'' => v ζ η'' - g η'') := by
    intro η'
    have hslice : DifferentiableAt ℝ (fun η'' => v ζ η'') η' := by
      have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => v p.1 p.2) (ζ, η') :=
        (hv.differentiable (by norm_num)) _
      exact (hasDerivAt_slice_snd hd).differentiableAt
    exact hslice.sub (hg_deriv η').differentiableAt
  have hconst2 := is_const_of_deriv_eq_zero hdiff hzero η 0
  have : v ζ η - g η = v ζ 0 - g 0 := hconst2
  rw [hg_zero] at this
  linarith [this]

/-!
### 5. The general solution of the 1D wave equation (Proposition 3.2.1)
-/

/-- **General solution of the 1D wave equation**, hard direction
(Proposition 3.2.1): every classical `C²` solution of `u_tt = c² u_xx`
(`c > 0`) is the superposition of a backward and a forward traveling wave,
`u(x, t) = F (x + ct) + G (x - ct)`, with `C²` profiles `F` and `G`. -/
theorem IsWaveSolution1D.exists_travelingWave_decomposition {c : ℝ} (hc : 0 < c)
    {u : ℝ → ℝ → ℝ} (hu : IsWaveSolution1D c u) :
    ∃ F G : ℝ → ℝ, ContDiff ℝ 2 F ∧ ContDiff ℝ 2 G ∧
      ∀ x t, u x t = F (x + c * t) + G (x - c * t) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  -- The characteristic-coordinate expression `v` has vanishing mixed partial.
  have hv : ContDiff ℝ 2 (fun p : ℝ × ℝ => charCoords c u p.1 p.2) :=
    contDiff_charCoords hu.contDiff
  have hmixed : ∀ ζ η, xderiv (tderiv (charCoords c u)) ζ η = 0 := by
    intro ζ η
    rw [tderiv_xderiv_charCoords hc0 hu.contDiff ζ η, hu.waveEq]
    ring
  -- Split `v(ζ,η) = f(ζ) + g(η)` and substitute back.
  obtain ⟨f, g, hf, hg, hfg⟩ :=
    exists_add_decomposition_of_mixed_deriv_eq_zero hv hmixed
  refine ⟨f, g, hf, hg, fun x t => ?_⟩
  have hback : charCoords c u (x + c * t) (x - c * t) = u x t := by
    rw [charCoords]
    congr 1
    · ring
    · field_simp
      ring
  rw [← hback, hfg]

/-- **General solution of the 1D wave equation** (Proposition 3.2.1), two-way
version: a `C²` function `u` satisfies `u_tt = c² u_xx` (`c > 0`) if and only
if it has the form `u(x, t) = F (x + ct) + G (x - ct)` for some `C²` profiles
`F` and `G`. (The regularity hypothesis `hu` is kept for alignment with the
informal statement; the reverse implication re-derives it from the profiles.) -/
theorem isWaveSolution1D_iff_exists_travelingWaves {c : ℝ} (hc : 0 < c)
    {u : ℝ → ℝ → ℝ} (_hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) :
    IsWaveSolution1D c u ↔
      ∃ F G : ℝ → ℝ, ContDiff ℝ 2 F ∧ ContDiff ℝ 2 G ∧
        ∀ x t, u x t = F (x + c * t) + G (x - c * t) := by
  constructor
  · exact fun h => h.exists_travelingWave_decomposition hc
  · rintro ⟨F, G, hF, hG, hFG⟩
    have huF : u = fun x t => F (x + c * t) + G (x - c * t) := by
      funext x t; exact hFG x t
    rw [huF]
    exact isWaveSolution1D_travelingWaves hF hG

end Wave
