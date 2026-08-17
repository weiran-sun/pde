import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import PDE.Basics.Wave.WaveGeneralSolution1D

/-!
# The Initial Value Problem for the 1D Wave Equation: D'Alembert's Formula

This file formalizes D'Alembert's solution formula for the initial value problem
for the one-dimensional wave equation on the whole line,

  `u_tt = c² u_xx`,  `u(x,0) = φ(x)`,  `u_t(x,0) = ψ(x)`,

following Rustom Choksi's Partial Differential Equations book (Chapter 3.3).

We establish:
1.  The D'Alembert expression
    `u(x,t) = ½[φ(x+ct) + φ(x-ct)] + (1/2c) ∫_{x-ct}^{x+ct} ψ(s) ds`.
2.  The classical-solution predicate for the whole-line IVP.
3.  D'Alembert's formula: every classical solution of the IVP is given by the
    D'Alembert expression (Theorem 3.1).
4.  Existence: for `φ ∈ C²` and `ψ ∈ C¹` the D'Alembert expression solves the IVP.
5.  Uniqueness of the classical solution, as a corollary.

The informal source states the wave equation for `t > 0`; here classical solutions
are taken `C²` on all of `ℝ²` (the wave equation is time reversible, and this is the
setting in which the general-solution decomposition `u = f(x+ct) + g(x-ct)` is proved),
with the initial data read off at `t = 0`.

## Reference

This formalization follows Chapter 3.3, ["Partial Differential Equations, A First Course"](https://bookstore.ams.org/amstext-54/) by Professor [Rustom Choksi](https://scholar.google.com/citations?user=Fk1zaTgAAAAJ&hl=en).

-/

open MeasureTheory intervalIntegral
open scoped Interval

namespace Wave

/-- **The D'Alembert expression.** For wave speed `c`, initial displacement `φ`, and
initial velocity `ψ`, this is the right-hand side of D'Alembert's formula
`½ [φ(x+ct) + φ(x-ct)] + (1/2c) ∫_{x-ct}^{x+ct} ψ(s) ds`. -/
noncomputable def dAlembert (c : ℝ) (φ ψ : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (φ (x + c * t) + φ (x - c * t)) / 2
    + (1 / (2 * c)) * ∫ s in (x - c * t)..(x + c * t), ψ s

/-- `u` is a classical solution of the initial value problem for the 1D wave equation
on the whole line with wave speed `c`, initial displacement `φ`, and initial
velocity `ψ`:

  `u_tt = c² u_xx` on `ℝ × ℝ`, `u(x,0) = φ(x)`, `u_t(x,0) = ψ(x)`.

Here `u x t` is the displacement at position `x` and time `t`, and `u` is required
to be `C²` in both variables jointly. -/
structure IsSolutionWaveIVP1D (c : ℝ) (φ ψ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  /-- The solution is twice continuously differentiable jointly in `(x, t)`. -/
  contDiff : ContDiff ℝ 2 (Function.uncurry u)
  /-- The wave equation `u_tt = c² u_xx` holds everywhere. -/
  waveEq : ∀ x t : ℝ,
    deriv (deriv (u x)) t = c ^ 2 * deriv (deriv fun ξ => u ξ t) x
  /-- Initial displacement: `u(x, 0) = φ(x)`. -/
  initPos : ∀ x : ℝ, u x 0 = φ x
  /-- Initial velocity: `u_t(x, 0) = ψ(x)`. -/
  initVel : ∀ x : ℝ, deriv (u x) 0 = ψ x

/-- Time derivative of a traveling-wave superposition `τ ↦ f (x + cτ) + g (x - cτ)`
(chain-rule helper for D'Alembert's formula). -/
private lemma hasDerivAt_superposition_snd {c : ℝ} {f g : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x t : ℝ) :
    HasDerivAt (fun τ => f (x + c * τ) + g (x - c * τ))
      (c * deriv f (x + c * t) - c * deriv g (x - c * t)) t := by
  have hin₁ : HasDerivAt (fun τ : ℝ => x + c * τ) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).const_add x
  have hin₂ : HasDerivAt (fun τ : ℝ => x - c * τ) (-c) t := by
    simpa using ((hasDerivAt_id t).const_mul c).const_sub x
  have h1 : HasDerivAt (fun τ => f (x + c * τ)) (deriv f (x + c * t) * c) t :=
    ((hf _).hasDerivAt).comp t hin₁
  have h2 : HasDerivAt (fun τ => g (x - c * τ)) (deriv g (x - c * t) * (-c)) t :=
    ((hg _).hasDerivAt).comp t hin₂
  have hval : c * deriv f (x + c * t) - c * deriv g (x - c * t)
      = deriv f (x + c * t) * c + deriv g (x - c * t) * (-c) := by ring
  rw [hval]
  exact h1.add h2

/-- Fundamental theorem of calculus for a `C²` function
(helper for D'Alembert's formula): `∫_a^b h' = h(b) - h(a)`. -/
private lemma integral_deriv_eq_sub_of_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (a b : ℝ) : ∫ s in a..b, deriv h s = h b - h a := by
  have hd : ContDiff ℝ 1 (deriv h) := (contDiff_succ_iff_deriv.mp hh).2.2
  exact intervalIntegral.integral_deriv_eq_sub
    (fun s _ => (hh.differentiable (by norm_num)) s)
    (hd.continuous.intervalIntegrable a b)

/-- **D'Alembert's formula** (Theorem 3.1). Every classical solution of the initial
value problem for the 1D wave equation on the whole line is given by
`u(x,t) = ½ [φ(x+ct) + φ(x-ct)] + (1/2c) ∫_{x-ct}^{x+ct} ψ(s) ds`. -/
theorem IsSolutionWaveIVP1D.eq_dAlembert {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} (hu : IsSolutionWaveIVP1D c φ ψ u) (x t : ℝ) :
    u x t = dAlembert c φ ψ x t := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  -- `u` is a classical wave solution in the sense of `WaveGeneralSolution1D`
  have huw : IsWaveSolution1D c u :=
    ⟨hu.contDiff, fun x t => hu.waveEq x t⟩
  -- decompose into traveling waves (Proposition 3.2.1)
  obtain ⟨F, G, hF, hG, huFG⟩ := huw.exists_travelingWave_decomposition hc
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hG1 : Differentiable ℝ G := hG.differentiable (by norm_num)
  -- initial displacement: `F + G = φ`
  have hsum : ∀ α : ℝ, F α + G α = φ α := fun α => by
    have h := (huFG α 0).symm.trans (hu.initPos α)
    simpa using h
  -- initial velocity: `c F' - c G' = ψ`
  have hvel : ∀ α : ℝ, c * deriv F α - c * deriv G α = ψ α := fun α => by
    have hslice : u α = fun τ => F (α + c * τ) + G (α - c * τ) :=
      funext fun τ => huFG α τ
    have hd := (hasDerivAt_superposition_snd (c := c) hF1 hG1 α 0).deriv
    rw [← hu.initVel α, hslice]
    simpa using hd.symm
  -- evaluate the D'Alembert integral via the fundamental theorem of calculus
  have hFd1 : ContDiff ℝ 1 (deriv F) := (contDiff_succ_iff_deriv.mp hF).2.2
  have hGd1 : ContDiff ℝ 1 (deriv G) := (contDiff_succ_iff_deriv.mp hG).2.2
  have hFdc : Continuous (deriv F) := hFd1.continuous
  have hGdc : Continuous (deriv G) := hGd1.continuous
  have hψint : ∫ s in (x - c * t)..(x + c * t), ψ s
      = c * (F (x + c * t) - F (x - c * t)) - c * (G (x + c * t) - G (x - c * t)) := by
    have hψeq : ψ = fun s => c * deriv F s - c * deriv G s :=
      funext fun s => (hvel s).symm
    have hsub : ∫ s in (x - c * t)..(x + c * t),
          ((fun s => c * deriv F s) s - (fun s => c * deriv G s) s)
        = (∫ s in (x - c * t)..(x + c * t), c * deriv F s)
          - ∫ s in (x - c * t)..(x + c * t), c * deriv G s :=
      intervalIntegral.integral_sub
        ((continuous_const.mul hFdc).intervalIntegrable _ _)
        ((continuous_const.mul hGdc).intervalIntegrable _ _)
    rw [hψeq]
    rw [show (∫ s in (x - c * t)..(x + c * t), c * deriv F s - c * deriv G s)
        = ∫ s in (x - c * t)..(x + c * t),
            ((fun s => c * deriv F s) s - (fun s => c * deriv G s) s) from rfl,
      hsub, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_deriv_eq_sub_of_contDiff hF, integral_deriv_eq_sub_of_contDiff hG]
  -- assemble
  rw [huFG x t]
  simp only [dAlembert, hψint, ← hsum (x + c * t), ← hsum (x - c * t)]
  field_simp
  ring

/-- Helper: any superposition `u(x,t) = f(x+ct) + g(x-ct)` of `C²` traveling waves is a
classical solution of the whole-line IVP with data `φ = f + g`, `ψ = c f' - c g'`. -/
theorem isSolutionWaveIVP1D_travelingWaves {c : ℝ} {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    IsSolutionWaveIVP1D c (fun x => f x + g x)
      (fun x => c * deriv f x - c * deriv g x)
      (fun x t => f (x + c * t) + g (x - c * t)) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfd : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
  have hgd : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have hfd1 : Differentiable ℝ (deriv f) := hfd.differentiable (by norm_num)
  have hgd1 : Differentiable ℝ (deriv g) := hgd.differentiable (by norm_num)
  -- derivatives of the inner affine maps
  have hin₁ : ∀ x t : ℝ, HasDerivAt (fun τ : ℝ => x + c * τ) c t := fun x t => by
    simpa using ((hasDerivAt_id t).const_mul c).const_add x
  have hin₂ : ∀ x t : ℝ, HasDerivAt (fun τ : ℝ => x - c * τ) (-c) t := fun x t => by
    simpa using ((hasDerivAt_id t).const_mul c).const_sub x
  -- first t-derivative
  have hut : ∀ x t : ℝ, HasDerivAt (fun τ => f (x + c * τ) + g (x - c * τ))
      (c * deriv f (x + c * t) - c * deriv g (x - c * t)) t := by
    intro x t
    have h1 : HasDerivAt (fun τ => f (x + c * τ)) (deriv f (x + c * t) * c) t :=
      ((hf1 _).hasDerivAt).comp t (hin₁ x t)
    have h2 : HasDerivAt (fun τ => g (x - c * τ)) (deriv g (x - c * t) * (-c)) t :=
      ((hg1 _).hasDerivAt).comp t (hin₂ x t)
    have hval : c * deriv f (x + c * t) - c * deriv g (x - c * t)
        = deriv f (x + c * t) * c + deriv g (x - c * t) * (-c) := by ring
    rw [hval]
    exact h1.add h2
  have hut_eq : ∀ x : ℝ, (deriv fun τ => f (x + c * τ) + g (x - c * τ))
      = fun t => c * deriv f (x + c * t) - c * deriv g (x - c * t) :=
    fun x => funext fun t => (hut x t).deriv
  -- second t-derivative
  have hutt : ∀ x t : ℝ,
      HasDerivAt (fun τ => c * deriv f (x + c * τ) - c * deriv g (x - c * τ))
        (c ^ 2 * deriv (deriv f) (x + c * t) + c ^ 2 * deriv (deriv g) (x - c * t)) t := by
    intro x t
    have h1 : HasDerivAt (fun τ => deriv f (x + c * τ)) (deriv (deriv f) (x + c * t) * c) t :=
      ((hfd1 _).hasDerivAt).comp t (hin₁ x t)
    have h2 : HasDerivAt (fun τ => deriv g (x - c * τ)) (deriv (deriv g) (x - c * t) * (-c)) t :=
      ((hgd1 _).hasDerivAt).comp t (hin₂ x t)
    have hval : c ^ 2 * deriv (deriv f) (x + c * t) + c ^ 2 * deriv (deriv g) (x - c * t)
        = c * (deriv (deriv f) (x + c * t) * c) - c * (deriv (deriv g) (x - c * t) * (-c)) := by
      ring
    rw [hval]
    exact (h1.const_mul c).sub (h2.const_mul c)
  -- first x-derivative
  have hux : ∀ t x : ℝ, HasDerivAt (fun ξ => f (ξ + c * t) + g (ξ - c * t))
      (deriv f (x + c * t) + deriv g (x - c * t)) x := by
    intro t x
    have h1 : HasDerivAt (fun ξ => f (ξ + c * t)) (deriv f (x + c * t)) x :=
      ((hf1 _).hasDerivAt).comp_add_const x (c * t)
    have h2 : HasDerivAt (fun ξ => g (ξ - c * t)) (deriv g (x - c * t)) x :=
      ((hg1 _).hasDerivAt).comp_sub_const x (c * t)
    exact h1.add h2
  have hux_eq : ∀ t : ℝ, (deriv fun ξ => f (ξ + c * t) + g (ξ - c * t))
      = fun x => deriv f (x + c * t) + deriv g (x - c * t) :=
    fun t => funext fun x => (hux t x).deriv
  -- second x-derivative
  have huxx : ∀ t x : ℝ,
      HasDerivAt (fun ξ => deriv f (ξ + c * t) + deriv g (ξ - c * t))
        (deriv (deriv f) (x + c * t) + deriv (deriv g) (x - c * t)) x := by
    intro t x
    have h1 : HasDerivAt (fun ξ => deriv f (ξ + c * t)) (deriv (deriv f) (x + c * t)) x :=
      ((hfd1 _).hasDerivAt).comp_add_const x (c * t)
    have h2 : HasDerivAt (fun ξ => deriv g (ξ - c * t)) (deriv (deriv g) (x - c * t)) x :=
      ((hgd1 _).hasDerivAt).comp_sub_const x (c * t)
    exact h1.add h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- joint C² smoothness
    have haff₁ : ContDiff ℝ 2 (fun p : ℝ × ℝ => p.1 + c * p.2) :=
      contDiff_fst.add (contDiff_const.mul contDiff_snd)
    have haff₂ : ContDiff ℝ 2 (fun p : ℝ × ℝ => p.1 - c * p.2) :=
      contDiff_fst.sub (contDiff_const.mul contDiff_snd)
    exact (hf.comp haff₁).add (hg.comp haff₂)
  · -- the wave equation
    intro x t
    show deriv (deriv fun τ => f (x + c * τ) + g (x - c * τ)) t
      = c ^ 2 * deriv (deriv fun ξ => f (ξ + c * t) + g (ξ - c * t)) x
    have L : deriv (deriv fun τ => f (x + c * τ) + g (x - c * τ)) t
        = c ^ 2 * deriv (deriv f) (x + c * t) + c ^ 2 * deriv (deriv g) (x - c * t) := by
      rw [hut_eq x]
      exact (hutt x t).deriv
    have R : deriv (deriv fun ξ => f (ξ + c * t) + g (ξ - c * t)) x
        = deriv (deriv f) (x + c * t) + deriv (deriv g) (x - c * t) := by
      rw [hux_eq t]
      exact (huxx t x).deriv
    rw [L, R]
    ring
  · -- initial displacement
    intro x
    simp
  · -- initial velocity
    intro x
    show deriv (fun τ => f (x + c * τ) + g (x - c * τ)) 0 = c * deriv f x - c * deriv g x
    simpa using (hut x 0).deriv

/-- **Existence via D'Alembert's formula** (Exercise 3.1). For `c > 0`, `φ ∈ C²`, and
`ψ ∈ C¹`, the D'Alembert expression is a classical solution of the initial value
problem for the 1D wave equation on the whole line. -/
theorem isSolutionWaveIVP1D_dAlembert {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 1 ψ) :
    IsSolutionWaveIVP1D c φ ψ (dAlembert c φ ψ) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  -- the antiderivative of `ψ` vanishing at `0`
  set Ψ : ℝ → ℝ := fun α => ∫ s in (0:ℝ)..α, ψ s with hΨdef
  have hΨderiv : ∀ α : ℝ, HasDerivAt Ψ (ψ α) α := fun α =>
    (hψ.continuous.integral_hasStrictDerivAt 0 α).hasDerivAt
  have hΨ2 : ContDiff ℝ 2 Ψ := by
    have hderiv : deriv Ψ = ψ := funext fun α => (hΨderiv α).deriv
    have h : ContDiff ℝ (1 + 1) Ψ :=
      (contDiff_succ_iff_deriv (n := 1)).mpr
        ⟨fun α => (hΨderiv α).differentiableAt, by simp, by rw [hderiv]; exact hψ⟩
    norm_num at h
    exact h
  -- the traveling-wave profiles
  set f : ℝ → ℝ := fun α => φ α / 2 + 1 / (2 * c) * Ψ α with hfdef
  set g : ℝ → ℝ := fun α => φ α / 2 - 1 / (2 * c) * Ψ α with hgdef
  have hf : ContDiff ℝ 2 f := (hφ.div_const 2).add (contDiff_const.mul hΨ2)
  have hg : ContDiff ℝ 2 g := (hφ.div_const 2).sub (contDiff_const.mul hΨ2)
  have hf' : ∀ α : ℝ, HasDerivAt f (deriv φ α / 2 + 1 / (2 * c) * ψ α) α := fun α =>
    (((hφ.differentiable (by norm_num)) α).hasDerivAt.div_const 2).add
      ((hΨderiv α).const_mul (1 / (2 * c)))
  have hg' : ∀ α : ℝ, HasDerivAt g (deriv φ α / 2 - 1 / (2 * c) * ψ α) α := fun α =>
    (((hφ.differentiable (by norm_num)) α).hasDerivAt.div_const 2).sub
      ((hΨderiv α).const_mul (1 / (2 * c)))
  have base := isSolutionWaveIVP1D_travelingWaves (c := c) hf hg
  -- identify the data of the traveling-wave superposition with `φ`, `ψ`
  have hφeq : (fun x => f x + g x) = φ := by
    funext x
    simp only [hfdef, hgdef]
    ring
  have hψeq : (fun x => c * deriv f x - c * deriv g x) = ψ := by
    funext x
    rw [(hf' x).deriv, (hg' x).deriv]
    field_simp
    ring
  -- identify the superposition with the D'Alembert expression
  have hueq : dAlembert c φ ψ = fun x t => f (x + c * t) + g (x - c * t) := by
    funext x t
    have hsplit : ∫ s in (x - c * t)..(x + c * t), ψ s = Ψ (x + c * t) - Ψ (x - c * t) := by
      rw [hΨdef]
      exact (intervalIntegral.integral_interval_sub_left
        (hψ.continuous.intervalIntegrable _ _) (hψ.continuous.intervalIntegrable _ _)).symm
    simp only [dAlembert, hfdef, hgdef, hsplit]
    ring
  rw [hueq, ← hφeq, ← hψeq]
  exact base

/-- **Uniqueness of the classical solution.** Two classical solutions of the initial
value problem for the 1D wave equation with the same data coincide. -/
theorem IsSolutionWaveIVP1D.unique {c : ℝ} (hc : 0 < c) {φ ψ : ℝ → ℝ}
    {u v : ℝ → ℝ → ℝ} (hu : IsSolutionWaveIVP1D c φ ψ u)
    (hv : IsSolutionWaveIVP1D c φ ψ v) : u = v := by
  funext x t
  rw [hu.eq_dAlembert hc x t, hv.eq_dAlembert hc x t]

/-!
### The half-plane d'Alembert representation

The whole-line theorem `IsSolutionWaveIVP1D.eq_dAlembert` assumes the solution is
`C²` on all of `ℝ²`. For the fixed-end problem on the half-line
(`PDE.Basics.Wave.WaveBVP1D`) the odd reflection of a solution is only controlled
on the closed upper half-plane `t ≥ 0`, so the representation theorem is needed in
that setting. The traveling-wave decomposition of `WaveGeneralSolution1D` is
global, so instead the proof integrates along characteristics: the Riemann
invariants `u_t + c u_x` and `u_t - c u_x` satisfy the transport equations
`(∂_t - c ∂_x)(u_t + c u_x) = u_tt - c² u_xx = 0` and
`(∂_t + c ∂_x)(u_t - c u_x) = 0`, hence are constant along the characteristics
`x + ct = const` and `x - ct = const` respectively; averaging the two constancy
relations determines `u_t`, and the fundamental theorem of calculus in time
recovers `u` and yields D'Alembert's expression.
-/

/-- `u` is a classical solution of the initial value problem for the 1D wave
equation on the **closed upper half-plane**: `u` is jointly `C²` on `ℝ × [0,∞)`,
satisfies `u_tt = c² u_xx` for `t > 0`, and takes the initial data `φ`, `ψ` at
`t = 0`. Partial derivatives are the one-variable slices `Wave.xderiv` /
`Wave.tderiv`. (Blueprint block `def:wave-halfplane-solution`.) -/
structure IsSolutionWaveIVPHalfPlane1D (c : ℝ) (φ ψ : ℝ → ℝ)
    (u : ℝ → ℝ → ℝ) : Prop where
  /-- The solution is twice continuously differentiable jointly in `(x, t)` on the
  closed upper half-plane. -/
  contDiffOn : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ici 0)
  /-- The wave equation `u_tt = c² u_xx` holds on the open upper half-plane. -/
  waveEq : ∀ x t : ℝ, 0 < t →
    tderiv (tderiv u) x t = c ^ 2 * xderiv (xderiv u) x t
  /-- Initial displacement: `u(x, 0) = φ(x)`. -/
  initPos : ∀ x : ℝ, u x 0 = φ x
  /-- Initial velocity: `u_t(x, 0) = ψ(x)`. -/
  initVel : ∀ x : ℝ, tderiv u x 0 = ψ x

/- Planner strategy (transcribed from iter-017 plan §2 / session_18 recs §1 —
pure transcription, no research phase; every name below is grep-verified against
the Mathlib pin or is a local declaration with the cited coordinates):

Design: zero-derivative constancy along the minus characteristic through `(x, t)`.
Let `S := Set.univ ×ˢ Set.Ici 0` and build the boundary-safe Riemann invariant
from the *within* Fréchet derivative (same device as the CLOSED in-file precedent
`eq_integral_tderiv` below — copy its incantations verbatim):

  `V : ℝ → ℝ → ℝ := fun y s => fderivWithin ℝ (Function.uncurry u) S (y, s) (0, 1)
      + c * fderivWithin ℝ (Function.uncurry u) S (y, s) (1, 0)`

(the `(0,1)` slot is `u_t`, the `(1,0)` slot is `u_x`), and slice it along the
characteristic:  `F : ℝ → ℝ := fun s => V (x + c * t - c * s) s`,
so `F t` is the LHS at `(x, t)` and `F 0` reads the initial data at `x + c * t`.

Skeleton:
1. `hUD : UniqueDiffOn ℝ S := uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)`.
2. `F` is continuous on `Set.Icc 0 t`: compose
   `hu.contDiffOn.continuousOn_fderivWithin hUD (by norm_num)` with the continuous
   characteristic line, then `.clm_apply continuousOn_const` — exactly as in
   step (2) of `eq_integral_tderiv`.
3. Interior derivative (`s ∈ Set.Ioo 0 t`): the point `(x + c*t - c*s, s)` has
   `S ∈ nhds _` via `prod_mem_nhds Filter.univ_mem (Ici_mem_nhds hs.1)`, so
   `fderivWithin_of_mem_nhds` turns `V` — *eventually near the point* — into the
   fderiv-based form `W y s = tderiv u y s + c * xderiv u y s`
   (`tderiv_eq_fderiv` WaveGeneralSolution1D:91, `xderiv_eq_fderiv` :97; joint
   differentiability from `(hu.contDiffOn.contDiffAt hnh).differentiableAt`).
   Transfer the derivative across the eventual equality
   (`HasDerivAt.congr_of_eventuallyEq` / `Filter.EventuallyEq.hasDerivAt_iff`),
   and differentiate the slice of `W` with `Wave.hasDerivAt_affine_slice`
   (WaveGeneralSolution1D:143, instantiated `α := -c, β := x + c*t, γ := 1,
   δ := 0`), giving `F' s = -c * (W_x) + (W_t)`. Expanding, the mixed second
   partials cancel by local Schwarz (`second_derivative_symmetric`; if only
   eventual differentiability of the fderiv is in hand, use
   `second_derivative_symmetric_of_eventually`) and the pure terms cancel by
   `hu.waveEq _ _ hs.1` — so `F' s = 0`; downgrade to
   `HasDerivWithinAt F 0 (Set.Ioi s) s`.
4. Endpoint constancy `F t = F 0`: one-sided FTC exactly as in step (6) of
   `eq_integral_tderiv` — `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
   ht hcont hderiv` with integrand `0` (integrability by `intervalIntegrable_const`;
   `∫ 0 = F t - F 0`; `t = 0` is handled uniformly since `Ioo 0 0 = ∅`).
5. Convert `F t` to `tderiv u x t + c * xderiv u x t`: for `0 < t` use
   `fderivWithin_of_mem_nhds` + `tderiv_eq_fderiv` / `xderiv_eq_fderiv`
   (via `hasDerivAt_slice_snd` WaveGeneralSolution1D:72); for `t = 0`,
   `F t = F 0` is trivial and step 6 applies directly.
6. Read `F 0` off the initial data: `tderiv u (x + c*t) 0 = ψ (x + c*t)` is
   `hu.initVel`; for the x-part, `xderiv u y 0 = deriv φ y` by differentiating
   the x-slice equality `(fun ξ => u ξ 0) = φ` (funext of `hu.initPos` —
   `xderiv u y 0 = deriv (fun ξ => u ξ 0) y = deriv φ y`).

Known repairs (pre-validated in the iter-015 lane that closed `eq_integral_tderiv`):
- write `nhds`, NOT `𝓝` — this file has no `open Topology`;
- a trailing `rfl` is needed after `rw [..., tderiv_eq_fderiv hdiff]`-style
  rewrites (uncurry unfolding residue). -/
/-- Scaffold stub (`lem:wave-halfplane-char-plus`): **constancy of the Riemann
invariant `u_t + c u_x` along the minus characteristics.** The invariant
`v = u_t + c u_x` satisfies the transport equation `v_t - c v_x = 0` (this is the
wave equation plus equality of mixed second partials), so it is constant along
each line `x + ct = const` in the closed upper half-plane; evaluating at `t = 0`
via the initial data gives the stated right-hand side. -/
theorem IsSolutionWaveIVPHalfPlane1D.charPlus_eq {c : ℝ} {φ ψ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} (hu : IsSolutionWaveIVPHalfPlane1D c φ ψ u)
    {x t : ℝ} (ht : 0 ≤ t) :
    tderiv u x t + c * xderiv u x t
      = ψ (x + c * t) + c * deriv φ (x + c * t) := by
  sorry

/- Planner strategy: sign-flip twin of `charPlus_eq` — reuse its entire proof
skeleton with the invariant `G s = (u_t - c u_x)(x - c*(t - s), s)`, i.e.
`V y s := fderivWithin ℝ (Function.uncurry u) S (y, s) (0, 1)
  - c * fderivWithin ℝ (Function.uncurry u) S (y, s) (1, 0)` sliced along
`s ↦ (x - c*t + c*s, s)` (instantiate `Wave.hasDerivAt_affine_slice` with
`α := c, β := x - c*t, γ := 1, δ := 0`). The interior derivative computation is
identical except for signs: Schwarz cancels the mixed terms (now with `+c·u_xt`
against `-c·u_tx`), `hu.waveEq` kills the pure terms, and the endpoint FTC and
`t = 0` readoff (`hu.initVel`, `xderiv u y 0 = deriv φ y` from `hu.initPos`)
are unchanged. Same known repairs apply: `nhds` not `𝓝`, trailing `rfl` after
`tderiv_eq_fderiv`/`xderiv_eq_fderiv` rewrites. -/
/-- Scaffold stub (`lem:wave-halfplane-char-minus`): **constancy of the Riemann
invariant `u_t - c u_x` along the plus characteristics.** The invariant
`w = u_t - c u_x` satisfies the transport equation `w_t + c w_x = 0`, so it is
constant along each line `x - ct = const` in the closed upper half-plane;
evaluating at `t = 0` via the initial data gives the stated right-hand side. -/
theorem IsSolutionWaveIVPHalfPlane1D.charMinus_eq {c : ℝ} {φ ψ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} (hu : IsSolutionWaveIVPHalfPlane1D c φ ψ u)
    {x t : ℝ} (ht : 0 ≤ t) :
    tderiv u x t - c * xderiv u x t
      = ψ (x - c * t) - c * deriv φ (x - c * t) := by
  sorry

/- Planner strategy: pure algebra, no analysis. Add the two characteristic
relations `hu.charPlus_eq ht` and `hu.charMinus_eq ht`: the `c * xderiv u x t`
terms cancel, leaving `2 * tderiv u x t = ψ(x+ct) + ψ(x-ct)
+ c*(deriv φ (x+ct) - deriv φ (x-ct))`; divide by 2. `linarith
[hu.charPlus_eq ht, hu.charMinus_eq ht]` (with the goal pre-normalized by
`ring_nf` if needed) or a `have h := ...; linarith` pair should close it. -/
/-- Scaffold stub (`lem:wave-halfplane-ut`): **the time derivative of a half-plane
solution.** Averaging the two characteristic constancy relations
(`charPlus_eq` and `charMinus_eq`) eliminates `u_x` and expresses `u_t` through
the initial data alone. -/
theorem IsSolutionWaveIVPHalfPlane1D.tderiv_eq {c : ℝ} {φ ψ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} (hu : IsSolutionWaveIVPHalfPlane1D c φ ψ u)
    {x t : ℝ} (ht : 0 ≤ t) :
    tderiv u x t
      = (ψ (x + c * t) + ψ (x - c * t)) / 2
        + (c / 2) * (deriv φ (x + c * t) - deriv φ (x - c * t)) := by
  sorry

/-- Scaffold stub (`lem:wave-halfplane-ftc`): **fundamental theorem of calculus in
time for a half-plane solution.** The time slice `τ ↦ u x τ` is `C²` on `[0, t]`
with derivative `tderiv u x ·`, so integrating from `0` recovers `u` from the
initial displacement and the time derivative. -/
theorem IsSolutionWaveIVPHalfPlane1D.eq_integral_tderiv {c : ℝ} {φ ψ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} (hu : IsSolutionWaveIVPHalfPlane1D c φ ψ u)
    {x t : ℝ} (ht : 0 ≤ t) :
    u x t = φ x + ∫ s in (0:ℝ)..t, tderiv u x s := by
  set S : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ici 0 with hSdef
  set g : ℝ → ℝ := fun s => fderivWithin ℝ (Function.uncurry u) S (x, s) (0, 1)
    with hgdef
  have hUD : UniqueDiffOn ℝ S := uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)
  -- (1) the time slice τ ↦ u x τ is C² on [0,∞), hence continuous on [0,t]
  have hslice : ContDiffOn ℝ 2 (fun τ => u x τ) (Set.Ici 0) := by
    have hcomp := hu.contDiffOn.comp
      ((contDiff_const.prodMk contDiff_id).contDiffOn :
        ContDiffOn ℝ 2 (fun τ : ℝ => ((x : ℝ), τ)) (Set.Ici 0))
      (fun τ (hτ : τ ∈ Set.Ici 0) => Set.mem_prod.mpr ⟨Set.mem_univ x, hτ⟩)
    simpa [Function.comp_def, Function.uncurry] using hcomp
  have hcont : ContinuousOn (fun τ => u x τ) (Set.Icc 0 t) :=
    hslice.continuousOn.mono Set.Icc_subset_Ici_self
  -- (2) g is continuous on [0,t] (the within-derivative reaches the boundary)
  have hgcont : ContinuousOn g (Set.Icc 0 t) := by
    have hfd : ContinuousOn (fderivWithin ℝ (Function.uncurry u) S) S :=
      hu.contDiffOn.continuousOn_fderivWithin hUD (by norm_num)
    have hline : ContinuousOn (fun τ : ℝ => ((x : ℝ), τ)) (Set.Icc 0 t) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hmaps : Set.MapsTo (fun τ : ℝ => ((x : ℝ), τ)) (Set.Icc 0 t) S :=
      fun τ hτ => Set.mem_prod.mpr ⟨Set.mem_univ x, hτ.1⟩
    simpa [Function.comp_def] using
      ((hfd.comp hline hmaps).clm_apply continuousOn_const)
  -- (3) for s > 0 the within-derivative is the genuine time derivative
  have hgt : ∀ s : ℝ, 0 < s → g s = tderiv u x s := by
    intro s hs
    have hnh : S ∈ nhds ((x : ℝ), s) :=
      prod_mem_nhds Filter.univ_mem (Ici_mem_nhds hs)
    have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, s) :=
      (hu.contDiffOn.contDiffAt hnh).differentiableAt (by norm_num)
    show fderivWithin ℝ (Function.uncurry u) S (x, s) (0, 1) = tderiv u x s
    rw [fderivWithin_of_mem_nhds hnh, tderiv_eq_fderiv hdiff]
    rfl
  -- (4) right-derivative of the slice at interior times, value g s
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun τ => u x τ) (g s) (Set.Ioi s) s := by
    intro s hs
    have hnh : S ∈ nhds ((x : ℝ), s) :=
      prod_mem_nhds Filter.univ_mem (Ici_mem_nhds hs.1)
    have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, s) :=
      (hu.contDiffOn.contDiffAt hnh).differentiableAt (by norm_num)
    rw [hgt s hs.1, tderiv_eq_fderiv hdiff]
    exact (hasDerivAt_slice_snd hdiff).hasDerivWithinAt
  -- (5) integrability of g on [0,t]
  have hgint : IntervalIntegrable g MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le ht]
  -- (6) one-sided FTC (handles t = 0 uniformly: Ioo 0 0 = ∅)
  have hftc : (∫ s in (0 : ℝ)..t, g s) = u x t - u x 0 :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hcont hderiv hgint
  -- (7) swap integrands: tderiv u x · = g on Ι 0 t = Ioc 0 t (all s > 0 there)
  have hcongr : (∫ s in (0 : ℝ)..t, tderiv u x s) = ∫ s in (0 : ℝ)..t, g s := by
    refine intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Set.uIoc_of_le ht] at hs
    exact (hgt s hs.1).symm
  rw [hcongr, hftc, hu.initPos x]
  ring

/-- Scaffold stub (`thm:wave-halfplane-dalembert`): **the half-plane d'Alembert
representation.** A classical solution of the wave IVP on the closed upper
half-plane is given by the D'Alembert expression for all `t ≥ 0`. Substituting
the time-derivative formula (`tderiv_eq`) into the time integral
(`eq_integral_tderiv`) and evaluating the resulting integrals — the `ψ` terms by
the substitutions `s ↦ x ± cs`, the `deriv φ` terms by the fundamental theorem of
calculus — produces the D'Alembert expression. -/
theorem IsSolutionWaveIVPHalfPlane1D.eq_dAlembert {c : ℝ} (hc : 0 < c)
    {φ ψ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} (hu : IsSolutionWaveIVPHalfPlane1D c φ ψ u)
    {x t : ℝ} (ht : 0 ≤ t) :
    u x t = dAlembert c φ ψ x t := by
  sorry

/-- A whole-plane classical solution is in particular a half-plane classical
solution (glue; lets the whole-line results flow into the half-plane API). -/
theorem IsSolutionWaveIVP1D.isSolutionWaveIVPHalfPlane1D {c : ℝ} {φ ψ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} (hu : IsSolutionWaveIVP1D c φ ψ u) :
    IsSolutionWaveIVPHalfPlane1D c φ ψ u where
  contDiffOn := hu.contDiff.contDiffOn
  waveEq := fun x t _ => hu.waveEq x t
  initPos := hu.initPos
  initVel := hu.initVel

end Wave
