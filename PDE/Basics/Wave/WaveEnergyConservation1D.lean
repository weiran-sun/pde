import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import PDE.Basics.Wave.WaveGeneralSolution1D

/-!
# Conservation of the Total Energy for the 1D Wave Equation

This file formalizes conservation of the total (kinetic + potential) energy for
$C^2$ solutions of the 1D wave equation $u_{tt} = \frac{T}{\rho} u_{xx}$ on the
whole line, following Rustom Choksi's Partial Differential Equations book
(Chapter 3.5).

We also expose the energy method in a reusable form: for the zeroth-order
perturbation $u_{tt} = c^2 u_{xx} - k u$ ($k \ge 0$) we define the modified
energy $E_k$, prove its conservation, and derive uniqueness of the initial
value problem. The case $k = 0$ recovers the classical statements; $k = 2$ is
the form needed for the energy-method uniqueness in problem 8.

Solutions are assumed to have *cone support*: $u(x,t) = 0$ whenever
$|x| \ge R + c|t|$. For compactly supported initial data this is automatic by
D'Alembert's formula, and taking it as a hypothesis keeps this file independent
of the solution formula.

## Main declarations

* `Wave.kineticEnergy`, `Wave.potentialEnergy`, `Wave.totalEnergy` — the
  energies $KE(t)$, $PE(t)$, $E(t)$ of the string at time $t$.
* `Wave.totalEnergy_eq_const` — conservation of the total energy.
* `Wave.modifiedEnergy`, `Wave.modifiedEnergy_eq_const` — the energy
  $E_k(t) = \frac12 \int u_t^2 + c^2 u_x^2 + k u^2 \,dx$ and its conservation.
* `Wave.eq_zero_of_initialData_zero`, `Wave.uniqueness_energy_method` — the
  energy method: vanishing data force the zero solution; uniqueness for the
  IVP of $u_{tt} = c^2 u_{xx} - k u + f$.

## Conventions

A solution is a function `u : ℝ → ℝ → ℝ` with `u x t` the displacement at
position `x` and time `t`. Partial derivatives are spelled with `deriv`:
`deriv (fun τ => u x τ) t` is $u_t$ and `deriv (fun ξ => u ξ t) x` is $u_x$.

## Reference

Chapter 3.5, ["Partial Differential Equations, A First Course"](https://bookstore.ams.org/amstext-54/)
by Professor [Rustom Choksi](https://scholar.google.com/citations?user=Fk1zaTgAAAAJ&hl=en).
-/

open MeasureTheory

namespace Wave

/-- The time derivative $u_t(x,t)$ of a solution `u : ℝ → ℝ → ℝ`. -/
noncomputable def dt (u : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun τ => u x τ) t

/-- The space derivative $u_x(x,t)$ of a solution `u : ℝ → ℝ → ℝ`. -/
noncomputable def dx (u : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun ξ => u ξ t) x

/-- The second time derivative $u_{tt}(x,t)$. -/
noncomputable def dtt (u : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun τ => dt u x τ) t

/-- The second space derivative $u_{xx}(x,t)$. -/
noncomputable def dxx (u : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun ξ => dx u ξ t) x

/-- `u` solves the 1D wave equation $u_{tt} = c^2 u_{xx} - k u + f$ classically:
`u` is $C^2$ as a function of $(x, t)$ and the equation holds pointwise.
`k = 0`, `f = 0` is the homogeneous wave equation. -/
structure IsWaveSolution (c k : ℝ) (f : ℝ → ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)
  eqn : ∀ x t, dtt u x t = c ^ 2 * dxx u x t - k * u x t + f x t

/-- `u` vanishes outside the cone $|x| < R + c|t|$; for compactly supported
initial data this holds automatically by D'Alembert's formula. -/
def HasConeSupport (c R : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ x t, R + c * |t| ≤ |x| → u x t = 0

/-- The total kinetic energy of the string at time `t`:
$KE(t) = \frac{1}{2} \int_{-\infty}^\infty \rho\, u_t^2\, dx$. -/
noncomputable def kineticEnergy (ρ : ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / 2) * ∫ x : ℝ, ρ * dt u x t ^ 2

/-- The total potential energy of the string at time `t`:
$PE(t) = \frac{T}{2} \int_{-\infty}^\infty u_x^2\, dx$. -/
noncomputable def potentialEnergy (T : ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  (T / 2) * ∫ x : ℝ, dx u x t ^ 2

/-- The total energy $E(t) = KE(t) + PE(t)$ of the string at time `t`. -/
noncomputable def totalEnergy (T ρ : ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  kineticEnergy ρ u t + potentialEnergy T u t

/-- The modified energy
$E_k(t) = \frac{1}{2}\int_{-\infty}^\infty u_t^2 + c^2 u_x^2 + k u^2 \, dx$
associated with the equation $u_{tt} = c^2 u_{xx} - k u$. For `k = 0` this is
the density-normalized total energy. -/
noncomputable def modifiedEnergy (c k : ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / 2) * ∫ x : ℝ, (dt u x t ^ 2 + c ^ 2 * dx u x t ^ 2 + k * u x t ^ 2)

/-! ### Scaffold for the conservation proofs

Private stubs decomposing `modifiedEnergy_eq_const` (and via it
`totalEnergy_eq_const`) following the blueprint chapter proof: cone support
kills the derivatives outside the cone, differentiation under the integral
sign gives $E_k'(t)$, the PDE turns the integrand into the flux derivative
$c^2 (u_t u_x)_x$, and the flux integrates to zero by compact support. -/

/-- The mixed derivative $u_{xt} = \partial_t u_x$ (time derivative of the
space derivative). -/
private noncomputable def dtdx (u : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun τ => dx u x τ) t

/-- Outside the cone (strictly), the time derivative vanishes: `u` is zero on
a neighborhood of `t` in the time variable. -/
private lemma dt_eq_zero_of_coneSupport {c R : ℝ} {u : ℝ → ℝ → ℝ}
    (hsupp : HasConeSupport c R u) {x t : ℝ} (hx : R + c * |t| < |x|) :
    dt u x t = 0 := by
  have hopen : IsOpen {τ : ℝ | R + c * |τ| < |x|} :=
    isOpen_lt (continuous_const.add (continuous_const.mul continuous_abs))
      continuous_const
  have hev : (fun τ => u x τ) =ᶠ[nhds t] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hx] with τ hτ
    exact hsupp x τ hτ.le
  rw [dt, hev.deriv_eq]
  exact deriv_const t 0

/-- Outside the cone (strictly), the space derivative vanishes: `u` is zero on
a neighborhood of `x` in the space variable. -/
private lemma dx_eq_zero_of_coneSupport {c R : ℝ} {u : ℝ → ℝ → ℝ}
    (hsupp : HasConeSupport c R u) {x t : ℝ} (hx : R + c * |t| < |x|) :
    dx u x t = 0 := by
  have hopen : IsOpen {ξ : ℝ | R + c * |t| < |ξ|} :=
    isOpen_lt continuous_const continuous_abs
  have hev : (fun ξ => u ξ t) =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hx] with ξ hξ
    exact hsupp ξ t hξ.le
  rw [dx, hev.deriv_eq]
  exact deriv_const x 0

/-- For a $C^2$ function of $(x,t)$, the time derivative is jointly $C^1$. -/
private lemma contDiff_one_dt {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => dt u p.1 p.2) :=
  contDiff_one_tderiv hu

/-- For a $C^2$ function of $(x,t)$, the space derivative is jointly $C^1$. -/
private lemma contDiff_one_dx {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => dx u p.1 p.2) :=
  contDiff_one_xderiv hu

/-- Clairaut / Schwarz for the shorthands: for a jointly $C^2$ function the
mixed derivative $\partial_t \partial_x u$ equals $\partial_x \partial_t u$. -/
private lemma dtdx_eq_deriv_dt {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) (x t : ℝ) :
    dtdx u x t = deriv (fun ξ => dt u ξ t) x :=
  tderiv_xderiv_comm hu x t

/-- The flux slice $x \mapsto u_t(x,t)\,u_x(x,t)$ is compactly supported
(cone support bounds the support by `|x| ≤ R + c|t|`). -/
private lemma hasCompactSupport_flux_slice {c R : ℝ} {u : ℝ → ℝ → ℝ}
    (hsupp : HasConeSupport c R u) (t : ℝ) :
    HasCompactSupport fun x => dt u x t * dx u x t := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(R + c * |t|)) (b := R + c * |t|))
  intro x hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  have hlt : R + c * |t| < |x| := by
    rcases hx with h | h
    · exact lt_abs.mpr (Or.inr (by linarith))
    · exact lt_abs.mpr (Or.inl h)
  rw [dt_eq_zero_of_coneSupport hsupp hlt, zero_mul]

/-- The flux slice $x \mapsto u_t(x,t)\,u_x(x,t)$ is $C^1$. -/
private lemma contDiff_one_flux_slice {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) (t : ℝ) :
    ContDiff ℝ 1 fun ξ => dt u ξ t * dx u ξ t := by
  have h1 : ContDiff ℝ 1 fun ξ => dt u ξ t :=
    (contDiff_one_dt hu).comp (contDiff_id.prodMk contDiff_const)
  have h2 : ContDiff ℝ 1 fun ξ => dx u ξ t :=
    (contDiff_one_dx hu).comp (contDiff_id.prodMk contDiff_const)
  exact h1.mul h2

/-- A $C^1$ compactly supported function has vanishing total derivative
integral: split `ℝ` at `0` via `MeasureTheory.integral_Iic_add_Ioi` and apply
`HasCompactSupport.integral_Iic_deriv_eq` / `.integral_Ioi_deriv_eq`. -/
private lemma integral_deriv_eq_zero_of_hasCompactSupport {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hsupp : HasCompactSupport g) :
    ∫ x : ℝ, deriv g x = 0 := by
  have hcont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hsupp' : HasCompactSupport (deriv g) := hsupp.deriv
  have hint : Integrable (deriv g) := hcont.integrable_of_hasCompactSupport hsupp'
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    hint.integrableOn hint.integrableOn,
    hsupp.integral_Iic_deriv_eq hg 0, hsupp.integral_Ioi_deriv_eq hg 0]
  ring

/-- A function of `x` vanishing for `R + c|t| < |x|` has compact support
(helper: support is contained in the closed interval `[-(R+c|t|), R+c|t|]`). -/
private lemma hasCompactSupport_of_coneVanish {c R t : ℝ} {g : ℝ → ℝ}
    (h : ∀ x, R + c * |t| < |x| → g x = 0) :
    HasCompactSupport g := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(R + c * |t|)) (b := R + c * |t|))
  intro x hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  apply h
  rcases hx with h' | h'
  · exact lt_abs.mpr (Or.inr (by linarith))
  · exact lt_abs.mpr (Or.inl h')

/-- The time-derivative slice $x \mapsto u_t(x,t)$ is continuous (helper). -/
private lemma continuous_dt_slice {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) (t : ℝ) :
    Continuous fun x => dt u x t :=
  ((contDiff_one_dt hu).comp (contDiff_id.prodMk contDiff_const)).continuous

/-- The space-derivative slice $x \mapsto u_x(x,t)$ is continuous (helper). -/
private lemma continuous_dx_slice {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) (t : ℝ) :
    Continuous fun x => dx u x t :=
  ((contDiff_one_dx hu).comp (contDiff_id.prodMk contDiff_const)).continuous

/-- The squared time-derivative slice is integrable (helper). -/
private lemma integrable_dt_sq {c R : ℝ} {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2))
    (hsupp : HasConeSupport c R u) (t : ℝ) :
    Integrable fun x => dt u x t ^ 2 := by
  apply ((continuous_dt_slice hu t).pow 2).integrable_of_hasCompactSupport
  exact hasCompactSupport_of_coneVanish (c := c) (R := R) (t := t) fun x hx => by
    simp only [Pi.pow_apply, dt_eq_zero_of_coneSupport hsupp hx]; norm_num

/-- The squared space-derivative slice is integrable (helper). -/
private lemma integrable_dx_sq {c R : ℝ} {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2))
    (hsupp : HasConeSupport c R u) (t : ℝ) :
    Integrable fun x => dx u x t ^ 2 := by
  apply ((continuous_dx_slice hu t).pow 2).integrable_of_hasCompactSupport
  exact hasCompactSupport_of_coneVanish (c := c) (R := R) (t := t) fun x hx => by
    simp only [Pi.pow_apply, dx_eq_zero_of_coneSupport hsupp hx]; norm_num

/-- For a jointly $C^2$ function, the second time derivative $u_{tt}$ is
jointly continuous (helper: `dtt u = tderiv (dt u)` and `dt u` is $C^1$). -/
private lemma continuous_dtt {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) :
    Continuous fun p : ℝ × ℝ => dtt u p.1 p.2 := by
  have h : (fun p : ℝ × ℝ => dtt u p.1 p.2) =
      fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => dt u q.1 q.2) p (0, 1) := by
    funext p
    exact tderiv_eq_fderiv (((contDiff_one_dt hu).differentiable (by norm_num)) _)
  rw [h]
  exact (((contDiff_one_dt hu).fderiv_right (m := 0) (by norm_num)).clm_apply
    contDiff_const).continuous

/-- For a jointly $C^2$ function, the mixed derivative $u_{xt} = \partial_t u_x$
is jointly continuous (helper: `dtdx u = tderiv (dx u)` and `dx u` is $C^1$). -/
private lemma continuous_dtdx {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)) :
    Continuous fun p : ℝ × ℝ => dtdx u p.1 p.2 := by
  have h : (fun p : ℝ × ℝ => dtdx u p.1 p.2) =
      fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => dx u q.1 q.2) p (0, 1) := by
    funext p
    exact tderiv_eq_fderiv (((contDiff_one_dx hu).differentiable (by norm_num)) _)
  rw [h]
  exact (((contDiff_one_dx hu).fderiv_right (m := 0) (by norm_num)).clm_apply
    contDiff_const).continuous

/-- **Differentiation under the integral sign** for the modified energy
(via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`): the integrand is
$C^1$ in $t$ with locally uniformly dominated derivative thanks to smoothness
and cone support. -/
private lemma hasDerivAt_modifiedEnergy {c k : ℝ} (hc : 0 < c)
    {u : ℝ → ℝ → ℝ} (hu : IsWaveSolution c k 0 u)
    {R : ℝ} (hsupp : HasConeSupport c R u) (t : ℝ) :
    HasDerivAt (modifiedEnergy c k u)
      (∫ x : ℝ, (dt u x t * dtt u x t + c ^ 2 * dx u x t * dtdx u x t
        + k * u x t * dt u x t)) t := by
  -- The fixed compact spatial window containing the support of every time
  -- slice with `s ∈ ball t 1`, and the sup bound of the derivative there.
  set M : ℝ := R + c * (|t| + 1) with hM_def
  have hGcont : Continuous fun p : ℝ × ℝ =>
      2 * (dt u p.1 p.2 * dtt u p.1 p.2 + c ^ 2 * dx u p.1 p.2 * dtdx u p.1 p.2
        + k * u p.1 p.2 * dt u p.1 p.2) := by
    have h1 := (contDiff_one_dt hu.contDiff).continuous
    have h2 := (contDiff_one_dx hu.contDiff).continuous
    have h3 := continuous_dtt hu.contDiff
    have h4 := continuous_dtdx hu.contDiff
    have h5 := hu.contDiff.continuous
    exact continuous_const.mul (((h1.mul h3).add
      ((continuous_const.mul h2).mul h4)).add ((continuous_const.mul h5).mul h1))
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := -M) (b := M)).prod
    (isCompact_Icc (a := t - 1) (b := t + 1))).exists_bound_of_continuousOn
    hGcont.continuousOn
  -- Ingredients for the dominated differentiation lemma.
  have hs : Metric.ball t 1 ∈ nhds t := Metric.ball_mem_nhds t one_pos
  have hF_meas : ∀ᶠ s in nhds t, AEStronglyMeasurable
      (fun x : ℝ => dt u x s ^ 2 + c ^ 2 * dx u x s ^ 2 + k * u x s ^ 2)
      volume := by
    refine Filter.Eventually.of_forall fun s => ?_
    have hcont : Continuous fun x : ℝ =>
        dt u x s ^ 2 + c ^ 2 * dx u x s ^ 2 + k * u x s ^ 2 := by
      have h5 : Continuous fun x => u x s :=
        hu.contDiff.continuous.comp (continuous_id.prodMk continuous_const)
      exact (((continuous_dt_slice hu.contDiff s).pow 2).add
        (continuous_const.mul ((continuous_dx_slice hu.contDiff s).pow 2))).add
        (continuous_const.mul (h5.pow 2))
    exact hcont.aestronglyMeasurable
  have hu_cont_slice : Continuous fun x => u x t :=
    hu.contDiff.continuous.comp (continuous_id.prodMk continuous_const)
  have hint_u : Integrable fun x => u x t ^ 2 := by
    apply (hu_cont_slice.pow 2).integrable_of_hasCompactSupport
    exact hasCompactSupport_of_coneVanish (c := c) (R := R) (t := t) fun x hx => by
      simp only [Pi.pow_apply, hsupp x t hx.le]; norm_num
  have hF_int : Integrable
      (fun x : ℝ => dt u x t ^ 2 + c ^ 2 * dx u x t ^ 2 + k * u x t ^ 2)
      volume :=
    ((integrable_dt_sq hu.contDiff hsupp t).add
      ((integrable_dx_sq hu.contDiff hsupp t).const_mul _)).add
      (hint_u.const_mul _)
  have hF'_meas : AEStronglyMeasurable
      (fun x : ℝ => 2 * (dt u x t * dtt u x t + c ^ 2 * dx u x t * dtdx u x t
        + k * u x t * dt u x t)) volume :=
    (hGcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  -- Membership in the window `ball t 1` bounds `|s|` by `|t| + 1`.
  have hball : ∀ s ∈ Metric.ball t 1, t - 1 ≤ s ∧ s ≤ t + 1 ∧ |s| < |t| + 1 := by
    intro s hs'
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hs'
    refine ⟨by linarith [hs'.2], by linarith [hs'.1], ?_⟩
    have := abs_sub_abs_le_abs_sub s t
    have habs : |s - t| < 1 := abs_sub_lt_iff.mpr hs'
    linarith
  -- Off the window, the derivative of the density vanishes for all `s ∈ ball t 1`.
  have hvanish : ∀ s ∈ Metric.ball t 1, ∀ x : ℝ, M < |x| →
      dt u x s = 0 ∧ dx u x s = 0 ∧ u x s = 0 := by
    intro s hs' x hx
    have hcone : R + c * |s| < |x| := by
      have h1 : c * |s| < c * (|t| + 1) :=
        mul_lt_mul_of_pos_left (hball s hs').2.2 hc
      have : R + c * |s| < M := by rw [hM_def]; linarith
      linarith
    exact ⟨dt_eq_zero_of_coneSupport hsupp hcone,
      dx_eq_zero_of_coneSupport hsupp hcone, hsupp x s hcone.le⟩
  have h_bound : ∀ᵐ x : ℝ ∂volume, ∀ s ∈ Metric.ball t 1,
      ‖2 * (dt u x s * dtt u x s + c ^ 2 * dx u x s * dtdx u x s
        + k * u x s * dt u x s)‖
        ≤ (Set.Icc (-M) M).indicator (fun _ => C) x := by
    refine Filter.Eventually.of_forall fun x s hs' => ?_
    by_cases hx : |x| ≤ M
    · have hxK : (x, s) ∈ Set.Icc (-M) M ×ˢ Set.Icc (t - 1) (t + 1) := by
        refine ⟨Set.mem_Icc.mpr (abs_le.mp hx), Set.mem_Icc.mpr ?_⟩
        exact ⟨(hball s hs').1, (hball s hs').2.1⟩
      rw [Set.indicator_of_mem (Set.mem_Icc.mpr (abs_le.mp hx))]
      exact hC (x, s) hxK
    · obtain ⟨h1, h2, h3⟩ := hvanish s hs' x (not_le.mp hx)
      rw [Set.indicator_of_notMem (by rw [Set.mem_Icc, ← abs_le]; exact hx)]
      simp [h1, h2, h3]
  have hbound_int : Integrable ((Set.Icc (-M) M).indicator (fun _ => C)) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    exact MeasureTheory.integrableOn_const measure_Icc_lt_top.ne
  have h_diff : ∀ᵐ x : ℝ ∂volume, ∀ s ∈ Metric.ball t 1,
      HasDerivAt (fun s' => dt u x s' ^ 2 + c ^ 2 * dx u x s' ^ 2
        + k * u x s' ^ 2)
        (2 * (dt u x s * dtt u x s + c ^ 2 * dx u x s * dtdx u x s
          + k * u x s * dt u x s)) s := by
    refine Filter.Eventually.of_forall fun x s _ => ?_
    have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, s) :=
      (hu.contDiff.differentiable (by norm_num)) _
    have h_u : HasDerivAt (fun τ => u x τ) (dt u x s) s :=
      (hasDerivAt_slice_snd hd).differentiableAt.hasDerivAt
    have hddt : DifferentiableAt ℝ (fun p : ℝ × ℝ => dt u p.1 p.2) (x, s) :=
      ((contDiff_one_dt hu.contDiff).differentiable (by norm_num)) _
    have h_dt : HasDerivAt (fun τ => dt u x τ) (dtt u x s) s :=
      (hasDerivAt_slice_snd hddt).differentiableAt.hasDerivAt
    have hddx : DifferentiableAt ℝ (fun p : ℝ × ℝ => dx u p.1 p.2) (x, s) :=
      ((contDiff_one_dx hu.contDiff).differentiable (by norm_num)) _
    have h_dx : HasDerivAt (fun τ => dx u x τ) (dtdx u x s) s :=
      (hasDerivAt_slice_snd hddx).differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun s' => dt u x s' ^ 2)
        (2 * dt u x s * dtt u x s) s := by
      simpa using h_dt.fun_pow 2
    have h2 : HasDerivAt (fun s' => c ^ 2 * dx u x s' ^ 2)
        (c ^ 2 * (2 * dx u x s * dtdx u x s)) s := by
      simpa using (h_dx.fun_pow 2).const_mul (c ^ 2)
    have h3 : HasDerivAt (fun s' => k * u x s' ^ 2)
        (k * (2 * u x s * dt u x s)) s := by
      simpa using (h_u.fun_pow 2).const_mul k
    have hsum := (h1.add h2).add h3
    have hval : 2 * dt u x s * dtt u x s + c ^ 2 * (2 * dx u x s * dtdx u x s)
        + k * (2 * u x s * dt u x s)
        = 2 * (dt u x s * dtt u x s + c ^ 2 * dx u x s * dtdx u x s
          + k * u x s * dt u x s) := by ring
    exact hval ▸ hsum
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have h := key.2.const_mul (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) * ∫ x : ℝ, 2 * (dt u x t * dtt u x t
      + c ^ 2 * dx u x t * dtdx u x t + k * u x t * dt u x t)
      = ∫ x : ℝ, (dt u x t * dtt u x t + c ^ 2 * dx u x t * dtdx u x t
        + k * u x t * dt u x t) := by
    rw [MeasureTheory.integral_const_mul]
    ring
  have hEq : modifiedEnergy c k u = fun s : ℝ =>
      (1 / 2 : ℝ) * ∫ x : ℝ, (dt u x s ^ 2 + c ^ 2 * dx u x s ^ 2
        + k * u x s ^ 2) := rfl
  rw [hEq]
  exact hval ▸ h

/-- **Pointwise identity from the PDE**: substituting
$u_{tt} = c^2 u_{xx} - k u$ into the differentiated energy density, the
$k$-terms cancel and the rest is the flux derivative $c^2\,(u_t u_x)_x$
(using Clairaut for $u_{xt} = u_{tx}$). -/
private lemma energyDensity_deriv_eq_flux {c k : ℝ}
    {u : ℝ → ℝ → ℝ} (hu : IsWaveSolution c k 0 u) (x t : ℝ) :
    dt u x t * dtt u x t + c ^ 2 * dx u x t * dtdx u x t + k * u x t * dt u x t
      = c ^ 2 * deriv (fun ξ => dt u ξ t * dx u ξ t) x := by
  -- Product rule for the flux slice: both factors are differentiable x-slices
  -- of jointly C¹ functions.
  have hdt : HasDerivAt (fun ξ => dt u ξ t) (deriv (fun ξ => dt u ξ t) x) x := by
    have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => dt u p.1 p.2) (x, t) :=
      ((contDiff_one_dt hu.contDiff).differentiable (by norm_num)) _
    exact (hasDerivAt_slice_fst hd).differentiableAt.hasDerivAt
  have hdx : HasDerivAt (fun ξ => dx u ξ t) (dxx u x t) x := by
    have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => dx u p.1 p.2) (x, t) :=
      ((contDiff_one_dx hu.contDiff).differentiable (by norm_num)) _
    exact (hasDerivAt_slice_fst hd).differentiableAt.hasDerivAt
  have hprod : deriv (fun ξ => dt u ξ t * dx u ξ t) x
      = deriv (fun ξ => dt u ξ t) x * dx u x t + dt u x t * dxx u x t :=
    (hdt.mul hdx).deriv
  rw [hprod, ← dtdx_eq_deriv_dt hu.contDiff x t]
  -- Substitute the PDE and cancel the k-terms.
  have heqn := hu.eqn x t
  simp only [Pi.zero_apply] at heqn
  rw [heqn]
  ring

/-- The flux term integrates to zero over `ℝ`: the flux slice is $C^1$ and
compactly supported. -/
private lemma integral_flux_deriv_eq_zero {c k : ℝ}
    {u : ℝ → ℝ → ℝ} (hu : IsWaveSolution c k 0 u)
    {R : ℝ} (hsupp : HasConeSupport c R u) (t : ℝ) :
    ∫ x : ℝ, deriv (fun ξ => dt u ξ t * dx u ξ t) x = 0 :=
  integral_deriv_eq_zero_of_hasCompactSupport
    (contDiff_one_flux_slice hu.contDiff t) (hasCompactSupport_flux_slice hsupp t)

/-- $E_k'(s) = 0$: chain the differentiation under the integral, the pointwise
flux identity, and the vanishing flux integral. -/
private lemma hasDerivAt_modifiedEnergy_zero {c k : ℝ} (hc : 0 < c)
    {u : ℝ → ℝ → ℝ} (hu : IsWaveSolution c k 0 u)
    {R : ℝ} (hsupp : HasConeSupport c R u) (s : ℝ) :
    HasDerivAt (modifiedEnergy c k u) 0 s := by
  have h := hasDerivAt_modifiedEnergy hc hu hsupp s
  have hval : (∫ x : ℝ, (dt u x s * dtt u x s + c ^ 2 * dx u x s * dtdx u x s
      + k * u x s * dt u x s)) = 0 := by
    have hcongr : (fun x : ℝ => dt u x s * dtt u x s
        + c ^ 2 * dx u x s * dtdx u x s + k * u x s * dt u x s)
        = fun x : ℝ => c ^ 2 * deriv (fun ξ => dt u ξ s * dx u ξ s) x :=
      funext fun x => energyDensity_deriv_eq_flux hu x s
    rw [hcongr, MeasureTheory.integral_const_mul,
      integral_flux_deriv_eq_zero hu hsupp s, mul_zero]
  rwa [hval] at h

/-- **Conservation of the modified energy.** Let `u` be a $C^2$ solution of
$u_{tt} = c^2 u_{xx} - k u$ ($c > 0$) with cone support. Then
$E_k(t) = E_k(0)$ for all `t`. -/
theorem modifiedEnergy_eq_const {c k : ℝ} (hc : 0 < c)
    {u : ℝ → ℝ → ℝ} (hu : IsWaveSolution c k 0 u)
    {R : ℝ} (hsupp : HasConeSupport c R u) (t : ℝ) :
    modifiedEnergy c k u t = modifiedEnergy c k u 0 := by
  have h0 : ∀ s, HasDerivAt (modifiedEnergy c k u) 0 s :=
    fun s => hasDerivAt_modifiedEnergy_zero hc hu hsupp s
  exact is_const_of_deriv_eq_zero (fun s => (h0 s).differentiableAt)
    (fun s => (h0 s).deriv) t 0

/-- The total energy is `ρ` times the modified energy with speed
$c = \sqrt{T/\rho}$ and $k = 0$: combine the two integrals (integrability from
smoothness and cone support) and use $c^2 = T/\rho$. -/
private lemma totalEnergy_eq_smul_modifiedEnergy {T ρ : ℝ} (hT : 0 < T)
    (hρ : 0 < ρ) {u : ℝ → ℝ → ℝ} (hu : IsWaveSolution (Real.sqrt (T / ρ)) 0 0 u)
    {R : ℝ} (hsupp : HasConeSupport (Real.sqrt (T / ρ)) R u) (t : ℝ) :
    totalEnergy T ρ u t = ρ * modifiedEnergy (Real.sqrt (T / ρ)) 0 u t := by
  have hc2 : Real.sqrt (T / ρ) ^ 2 = T / ρ :=
    Real.sq_sqrt (le_of_lt (div_pos hT hρ))
  have hint_t : Integrable fun x => dt u x t ^ 2 :=
    integrable_dt_sq hu.contDiff hsupp t
  have hint_x : Integrable fun x => dx u x t ^ 2 :=
    integrable_dx_sq hu.contDiff hsupp t
  have hsplit : (∫ x : ℝ, (dt u x t ^ 2 + Real.sqrt (T / ρ) ^ 2 * dx u x t ^ 2
      + 0 * u x t ^ 2))
      = (∫ x : ℝ, dt u x t ^ 2)
        + Real.sqrt (T / ρ) ^ 2 * ∫ x : ℝ, dx u x t ^ 2 := by
    simp only [zero_mul, add_zero]
    rw [MeasureTheory.integral_add hint_t (hint_x.const_mul _),
      MeasureTheory.integral_const_mul]
  have hKE : kineticEnergy ρ u t = (ρ / 2) * ∫ x : ℝ, dt u x t ^ 2 := by
    rw [kineticEnergy, MeasureTheory.integral_const_mul]
    ring
  rw [totalEnergy, modifiedEnergy, hsplit, hKE, potentialEnergy, hc2]
  field_simp

/-- **Conservation of Total Energy** (Choksi §3.5). Let `u` be a $C^2$ solution
of the wave equation $u_{tt} = \frac{T}{\rho} u_{xx}$ ($T, \rho > 0$) vanishing
outside the cone $|x| < R + \sqrt{T/\rho}\,|t|$. Then the total energy
$E(t) = \frac12 \int \rho u_t^2 + T u_x^2 \, dx$ is constant in time. -/
theorem totalEnergy_eq_const {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ)
    {u : ℝ → ℝ → ℝ} (hu : IsWaveSolution (Real.sqrt (T / ρ)) 0 0 u)
    {R : ℝ} (hsupp : HasConeSupport (Real.sqrt (T / ρ)) R u) (t : ℝ) :
    totalEnergy T ρ u t = totalEnergy T ρ u 0 := by
  have hc : 0 < Real.sqrt (T / ρ) := Real.sqrt_pos.mpr (div_pos hT hρ)
  rw [totalEnergy_eq_smul_modifiedEnergy hT hρ hu hsupp t,
    totalEnergy_eq_smul_modifiedEnergy hT hρ hu hsupp 0,
    modifiedEnergy_eq_const hc hu hsupp t]

/-- **The energy method, vanishing form.** A $C^2$ solution of
$u_{tt} = c^2 u_{xx} - k u$ ($c > 0$, $k \ge 0$) with cone support and
vanishing initial data $u(\cdot,0) = u_t(\cdot,0) = 0$ vanishes identically. -/
theorem eq_zero_of_initialData_zero {c k : ℝ} (hc : 0 < c) (hk : 0 ≤ k)
    {u : ℝ → ℝ → ℝ} (hu : IsWaveSolution c k 0 u)
    {R : ℝ} (hsupp : HasConeSupport c R u)
    (h0 : ∀ x, u x 0 = 0) (h1 : ∀ x, dt u x 0 = 0) :
    ∀ x t, u x t = 0 := by
  -- The energy density of `u` at each time, and its basic properties.
  set F : ℝ → ℝ → ℝ := fun t x =>
    dt u x t ^ 2 + c ^ 2 * dx u x t ^ 2 + k * u x t ^ 2 with hF_def
  have hcont_u_slice : ∀ t, Continuous fun x => u x t := fun t =>
    hu.contDiff.continuous.comp (continuous_id.prodMk continuous_const)
  have hFcont : ∀ t, Continuous (F t) := fun t =>
    (((continuous_dt_slice hu.contDiff t).pow 2).add
      (continuous_const.mul ((continuous_dx_slice hu.contDiff t).pow 2))).add
      (continuous_const.mul ((hcont_u_slice t).pow 2))
  have hFnonneg : ∀ t x, 0 ≤ F t x := fun t x =>
    add_nonneg (add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg c) (sq_nonneg _)))
      (mul_nonneg hk (sq_nonneg _))
  have hFint : ∀ t, Integrable (F t) := by
    intro t
    have hint_u : Integrable fun x => u x t ^ 2 := by
      apply ((hcont_u_slice t).pow 2).integrable_of_hasCompactSupport
      exact hasCompactSupport_of_coneVanish (c := c) (R := R) (t := t)
        fun x hx => by simp only [Pi.pow_apply, hsupp x t hx.le]; norm_num
    exact ((integrable_dt_sq hu.contDiff hsupp t).add
      ((integrable_dx_sq hu.contDiff hsupp t).const_mul _)).add
      (hint_u.const_mul _)
  -- The modified energy vanishes at `t = 0`: all three density terms vanish.
  have hE0 : modifiedEnergy c k u 0 = 0 := by
    have hdx0 : ∀ x, dx u x 0 = 0 := by
      intro x
      have : (fun ξ => u ξ 0) = fun _ => (0 : ℝ) := funext h0
      rw [dx, this]
      exact deriv_const x 0
    have hzero : (fun x : ℝ => dt u x 0 ^ 2 + c ^ 2 * dx u x 0 ^ 2
        + k * u x 0 ^ 2) = fun _ => (0 : ℝ) := by
      funext x
      rw [h0, h1, hdx0]
      ring
    rw [modifiedEnergy, hzero, MeasureTheory.integral_zero, mul_zero]
  -- Conservation transports the vanishing to every time.
  have hEt : ∀ t, modifiedEnergy c k u t = 0 := fun t =>
    (modifiedEnergy_eq_const hc hu hsupp t).trans hE0
  -- Nonnegative continuous integrand with zero integral vanishes identically.
  have hFzero : ∀ t x, F t x = 0 := by
    intro t
    have hint : (∫ x : ℝ, F t x) = 0 := by
      have := hEt t
      rw [modifiedEnergy] at this
      have h2 : (∫ x : ℝ, (dt u x t ^ 2 + c ^ 2 * dx u x t ^ 2
          + k * u x t ^ 2)) = 0 := by linarith
      simpa [hF_def] using h2
    have hae : F t =ᵐ[volume] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg (hFnonneg t) (hFint t)).mp hint
    have heq : F t = 0 := ((hFcont t).ae_eq_iff_eq volume continuous_const).mp hae
    exact fun x => congrFun heq x
  -- Each term is nonnegative, so `u_t` vanishes identically.
  have hdt_zero : ∀ x t, dt u x t = 0 := by
    intro x t
    have h := hFzero t x
    have h1' : dt u x t ^ 2 ≤ 0 := by
      have h2 : 0 ≤ c ^ 2 * dx u x t ^ 2 :=
        mul_nonneg (sq_nonneg c) (sq_nonneg _)
      have h3 : 0 ≤ k * u x t ^ 2 := mul_nonneg hk (sq_nonneg _)
      simp only [hF_def] at h
      nlinarith
    have hsq : dt u x t ^ 2 = 0 := le_antisymm h1' (sq_nonneg _)
    exact pow_eq_zero_iff two_ne_zero |>.mp hsq
  -- `u(x, ·)` has zero derivative, hence is constant equal to `u(x, 0) = 0`.
  intro x t
  have hdiff : Differentiable ℝ fun τ => u x τ := by
    intro τ
    have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => u p.1 p.2) (x, τ) :=
      (hu.contDiff.differentiable (by norm_num)) _
    exact (hasDerivAt_slice_snd hd).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun τ => hdt_zero x τ) t 0
  rw [hconst, h0]

/-- **Uniqueness via the energy method.** The initial value problem for
$u_{tt} = c^2 u_{xx} - k u + f$ ($c > 0$, $k \ge 0$) has at most one $C^2$
solution with cone support: two solutions with the same initial data agree.
`k = 0`, `f = 0` is classical uniqueness for the wave IVP; `k = 2` is the
statement needed in problem 8. -/
theorem uniqueness_energy_method {c k : ℝ} (hc : 0 < c) (hk : 0 ≤ k)
    {f u₁ u₂ : ℝ → ℝ → ℝ}
    (hu₁ : IsWaveSolution c k f u₁) (hu₂ : IsWaveSolution c k f u₂)
    {R₁ R₂ : ℝ} (hsupp₁ : HasConeSupport c R₁ u₁)
    (hsupp₂ : HasConeSupport c R₂ u₂)
    (h0 : ∀ x, u₁ x 0 = u₂ x 0) (h1 : ∀ x, dt u₁ x 0 = dt u₂ x 0) :
    ∀ x t, u₁ x t = u₂ x t := by
  -- The difference solves the homogeneous equation with vanishing data.
  set w : ℝ → ℝ → ℝ := fun x t => u₁ x t - u₂ x t with hw_def
  have hcd : ContDiff ℝ 2 (fun p : ℝ × ℝ => w p.1 p.2) :=
    hu₁.contDiff.sub hu₂.contDiff
  -- Derivative arithmetic: all the shorthands subtract.
  have hdt_w : ∀ x t, dt w x t = dt u₁ x t - dt u₂ x t := by
    intro x t
    have hd1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => u₁ p.1 p.2) (x, t) :=
      (hu₁.contDiff.differentiable (by norm_num)) _
    have hd2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => u₂ p.1 p.2) (x, t) :=
      (hu₂.contDiff.differentiable (by norm_num)) _
    have hh1 : HasDerivAt (fun τ => u₁ x τ) (dt u₁ x t) t :=
      (hasDerivAt_slice_snd hd1).differentiableAt.hasDerivAt
    have hh2 : HasDerivAt (fun τ => u₂ x τ) (dt u₂ x t) t :=
      (hasDerivAt_slice_snd hd2).differentiableAt.hasDerivAt
    exact (hh1.sub hh2).deriv
  have hdx_w : ∀ x t, dx w x t = dx u₁ x t - dx u₂ x t := by
    intro x t
    have hd1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => u₁ p.1 p.2) (x, t) :=
      (hu₁.contDiff.differentiable (by norm_num)) _
    have hd2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => u₂ p.1 p.2) (x, t) :=
      (hu₂.contDiff.differentiable (by norm_num)) _
    have hh1 : HasDerivAt (fun ξ => u₁ ξ t) (dx u₁ x t) x :=
      (hasDerivAt_slice_fst hd1).differentiableAt.hasDerivAt
    have hh2 : HasDerivAt (fun ξ => u₂ ξ t) (dx u₂ x t) x :=
      (hasDerivAt_slice_fst hd2).differentiableAt.hasDerivAt
    exact (hh1.sub hh2).deriv
  have hdtt_w : ∀ x t, dtt w x t = dtt u₁ x t - dtt u₂ x t := by
    intro x t
    have hfun : (fun τ => dt w x τ) = fun τ => dt u₁ x τ - dt u₂ x τ :=
      funext fun τ => hdt_w x τ
    rw [dtt, hfun]
    have hd1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => dt u₁ p.1 p.2) (x, t) :=
      ((contDiff_one_dt hu₁.contDiff).differentiable (by norm_num)) _
    have hd2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => dt u₂ p.1 p.2) (x, t) :=
      ((contDiff_one_dt hu₂.contDiff).differentiable (by norm_num)) _
    have hh1 : HasDerivAt (fun τ => dt u₁ x τ) (dtt u₁ x t) t :=
      (hasDerivAt_slice_snd hd1).differentiableAt.hasDerivAt
    have hh2 : HasDerivAt (fun τ => dt u₂ x τ) (dtt u₂ x t) t :=
      (hasDerivAt_slice_snd hd2).differentiableAt.hasDerivAt
    exact (hh1.sub hh2).deriv
  have hdxx_w : ∀ x t, dxx w x t = dxx u₁ x t - dxx u₂ x t := by
    intro x t
    have hfun : (fun ξ => dx w ξ t) = fun ξ => dx u₁ ξ t - dx u₂ ξ t :=
      funext fun ξ => hdx_w ξ t
    rw [dxx, hfun]
    have hd1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => dx u₁ p.1 p.2) (x, t) :=
      ((contDiff_one_dx hu₁.contDiff).differentiable (by norm_num)) _
    have hd2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => dx u₂ p.1 p.2) (x, t) :=
      ((contDiff_one_dx hu₂.contDiff).differentiable (by norm_num)) _
    have hh1 : HasDerivAt (fun ξ => dx u₁ ξ t) (dxx u₁ x t) x :=
      (hasDerivAt_slice_fst hd1).differentiableAt.hasDerivAt
    have hh2 : HasDerivAt (fun ξ => dx u₂ ξ t) (dxx u₂ x t) x :=
      (hasDerivAt_slice_fst hd2).differentiableAt.hasDerivAt
    exact (hh1.sub hh2).deriv
  -- `w` is a solution of the homogeneous equation.
  have hw_sol : IsWaveSolution c k 0 w := by
    refine ⟨hcd, fun x t => ?_⟩
    have he1 := hu₁.eqn x t
    have he2 := hu₂.eqn x t
    rw [hdtt_w, hdxx_w, he1, he2]
    simp only [hw_def, Pi.zero_apply]
    ring
  -- `w` has cone support with radius `max R₁ R₂`.
  have hw_supp : HasConeSupport c (max R₁ R₂) w := by
    intro x t hx
    have hx1 : R₁ + c * |t| ≤ |x| :=
      le_trans (by have := le_max_left R₁ R₂; linarith) hx
    have hx2 : R₂ + c * |t| ≤ |x| :=
      le_trans (by have := le_max_right R₁ R₂; linarith) hx
    simp only [hw_def, hsupp₁ x t hx1, hsupp₂ x t hx2, sub_zero]
  -- Vanishing initial data for `w`.
  have hw0 : ∀ x, w x 0 = 0 := fun x => by
    simp only [hw_def, h0 x, sub_self]
  have hw1 : ∀ x, dt w x 0 = 0 := fun x => by
    rw [hdt_w, h1 x, sub_self]
  -- Conclude via the vanishing form of the energy method.
  intro x t
  have := eq_zero_of_initialData_zero hc hk hw_sol hw_supp hw0 hw1 x t
  simpa [hw_def, sub_eq_zero] using this

end Wave
