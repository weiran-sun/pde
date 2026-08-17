import Mathlib
import PDE
import PDE.Basics.Heat.HeatKernel

/-!
# Undergraduate Problem 24: The Heat Kernel and the Heaviside Initial Datum

Source: `pde_latex/problems/undergraduate/problem_24.tex` (Math 418/718 Fall 2022,
HW-5, Problem 1).

## Informal statement

> Let `U(t,x) = (4πt)^{-1/2} e^{-x²/(4t)}` (`t > 0`, `x ∈ ℝ`) be the fundamental
> solution of the heat equation `∂ₜu = ∂ₓ²u`.
> (a) Verify by direct computation that `U` satisfies the heat equation for `t > 0`.
> (b) With the discontinuous datum `g = 𝟙_{[0,∞)}`, let
> `u(t,x) = ∫ U(t, x-y) g(y) dy`.
> (b1) Show `u` is `C^∞` in `(t,x)` for `t > 0` and solves the heat equation there.
> (b2) Show `u(t,x) → g̃(x)` as `t → 0⁺`, where `g̃ = 1` for `x > 0`, `1/2` at
> `x = 0`, `0` for `x < 0`.

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem24.tex`:

* The problem's kernel `U(t, x)` is the project's general one-dimensional heat
  kernel `Heat.heatKernel α x t = (1/√(4παt)) · exp(-(x²)/(4αt))`
  (`PDE/Basics/Heat/HeatKernel.lean`, blueprint `def:heatKernel-1d`) at
  diffusivity `α = 1`, with argument order `U(t, x) = heatKernel 1 x t`.
* The datum `g` (`def:problem24-g`) is spelled `if 0 ≤ x then 1 else 0`,
  matching the source's `g(x) = 1` for `x ≥ 0`, `0` for `x < 0`.
* The convolution `u` (`def:problem24-u`) is the Lebesgue integral
  `u t x = ∫ y, heatKernel 1 (x - y) t * g y` over all of `ℝ`.
* Part (a) (`thm:problem24-kernel-solves-heat`) is stated with nested slice
  derivatives `deriv (fun τ ↦ heatKernel 1 x τ) t` and
  `deriv (fun x' ↦ deriv (fun x'' ↦ heatKernel 1 x'' t) x') x`, matching the
  library convention; it is the `α = 1` instance of
  `Heat.heatKernel_solves_heat_eq`.
* The interchange-free route of the chapter: the convolution is evaluated in
  closed form (`lem:problem24-closed-form`) as `u t x = G (x / (2√t))`, where
  `G s = (√π)⁻¹ ∫_{-∞}^s e^{-z²} dz` (`def:problem24-G`); parts (b1) and (b2)
  are read off the closed form by the chain rule and composition of limits.
  The source's authorized differentiation-under-the-integral assumption is
  thereby not needed.
* Part (b1) (`thm:problem24-smooth-solves`) states joint `C^∞` smoothness as
  `ContDiffOn ℝ ∞` of the uncurried map on `Set.Ioi 0 ×ˢ Set.univ`, and the
  heat equation pointwise with the slice-derivative spelling above.
* Part (b2) (`thm:problem24-initial-limit`) states the `t → 0⁺` limit along
  `nhdsWithin 0 (Set.Ioi 0)`, with the limit value `g̃(x)` spelled as the
  nested conditional `if x < 0 then 0 else if x = 0 then 1/2 else 1`.
-/

open MeasureTheory Filter Heat Set
open scoped Topology ContDiff

namespace Problems.Undergraduate.Problem24

/-! ## Definitions -/

/-- **Heaviside step datum** (blueprint `def:problem24-g`): `g x = 1` for
`x ≥ 0` and `g x = 0` for `x < 0`. -/
noncomputable def g (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

-- Formula verification on concrete data (standing rule).
example : g 1 = 1 := by norm_num [g]
example : g (-1) = 0 := by norm_num [g]
example : g 0 = 1 := by norm_num [g]

/-- **Convolution of the heat kernel with the step datum** (blueprint
`def:problem24-u`): `u t x = ∫ y, U(t, x - y) g(y) dy` with
`U(t, x) = heatKernel 1 x t`. -/
noncomputable def u (t x : ℝ) : ℝ := ∫ y : ℝ, heatKernel 1 (x - y) t * g y

/-- **Normalized Gaussian antiderivative** (blueprint `def:problem24-G`):
`G s = (√π)⁻¹ ∫_{-∞}^s e^{-z²} dz`, the CDF of the density `e^{-z²}/√π`. -/
noncomputable def G (s : ℝ) : ℝ :=
  (Real.sqrt Real.pi)⁻¹ * ∫ z in Iic s, Real.exp (-z ^ 2)

/-! ## Part (a): the kernel solves the heat equation -/

/-- **Problem 24 (a)** (blueprint `thm:problem24-kernel-solves-heat`): the heat
kernel `U(t, x) = heatKernel 1 x t` satisfies `∂ₜU = ∂ₓ²U` for `t > 0`. The
`α = 1` instance of `Heat.heatKernel_solves_heat_eq`. -/
theorem kernel_solves_heat {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun τ ↦ heatKernel 1 x τ) t
      = deriv (fun x' ↦ deriv (fun x'' ↦ heatKernel 1 x'' t) x') x := by
  simpa using heatKernel_solves_heat_eq 1 one_pos ht (x := x)

/-! ## Properties of the Gaussian antiderivative -/

/-- The Gaussian `z ↦ e^{-z²}` is integrable on `ℝ`. -/
private lemma integrable_gauss : Integrable (fun z : ℝ ↦ Real.exp (-z ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos

/-- The total Gaussian integral is `√π` (Mathlib's `integral_gaussian` at
`b = 1`; blueprint `lem:problem24-gaussian-integral-mathlib`). -/
private lemma integral_gauss : (∫ z : ℝ, Real.exp (-z ^ 2)) = Real.sqrt Real.pi := by
  simpa using integral_gaussian (1 : ℝ)

/-- The half-line Gaussian integral: `∫ z in Iic 0, e^{-z²} = √π / 2`. -/
private lemma integral_gauss_Iic_zero :
    (∫ z in Iic (0 : ℝ), Real.exp (-z ^ 2)) = Real.sqrt Real.pi / 2 := by
  have hrefl : (∫ z in Iic (0 : ℝ), Real.exp (-z ^ 2))
      = ∫ z in Ioi (0 : ℝ), Real.exp (-z ^ 2) := by
    rw [show (Ioi (0 : ℝ)) = Ioi (-(0 : ℝ)) by norm_num,
      ← integral_comp_neg_Iic (0 : ℝ) (fun z ↦ Real.exp (-z ^ 2))]
    simp
  have hIoi : (∫ z in Ioi (0 : ℝ), Real.exp (-z ^ 2)) = Real.sqrt Real.pi / 2 := by
    simpa using integral_gaussian_Ioi (1 : ℝ)
  rw [hrefl, hIoi]

/-- **Value of `G` at the origin** (blueprint `lem:problem24-G-half`):
`G 0 = 1/2`, by evenness of the Gaussian and the total integral `√π`. -/
lemma G_zero : G 0 = 1 / 2 := by
  have hπ : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [G, integral_gauss_Iic_zero]
  field_simp

/-- **Limits of `G` at `±∞`** (blueprint `lem:problem24-G-limits`):
`G(s) → 1` as `s → +∞` and `G(s) → 0` as `s → -∞`. -/
lemma G_limits : Tendsto G atTop (𝓝 1) ∧ Tendsto G atBot (𝓝 0) := by
  have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  constructor
  · -- s → +∞: the truncated integrals tend to the total integral √π.
    have hcover : AECover (volume : Measure ℝ) atTop (fun s : ℝ ↦ Iic s) :=
      aecover_Iic tendsto_id
    have hint : Tendsto (fun s : ℝ ↦ ∫ z in Iic s, Real.exp (-z ^ 2)) atTop
        (𝓝 (∫ z : ℝ, Real.exp (-z ^ 2))) :=
      hcover.integral_tendsto_of_countably_generated integrable_gauss
    rw [integral_gauss] at hint
    have h1 := hint.const_mul (Real.sqrt Real.pi)⁻¹
    rw [inv_mul_cancel₀ hπ] at h1
    exact h1
  · -- s → -∞: the truncated integrals tend to 0.
    have hint : Tendsto (fun s : ℝ ↦ ∫ z in Iic s, Real.exp (-z ^ 2)) atBot (𝓝 0) :=
      tendsto_integral_Iic_zero tendsto_id
    have h1 := hint.const_mul (Real.sqrt Real.pi)⁻¹
    rw [mul_zero] at h1
    exact h1

/-- Split-at-0 form of `G` (pre-authorized helper): the improper lower limit
is isolated in the constant `G 0`, leaving a proper interval integral. -/
private lemma G_eq_add_intervalIntegral (s : ℝ) :
    G s = G 0 + (Real.sqrt Real.pi)⁻¹ * ∫ z in (0:ℝ)..s, Real.exp (-z ^ 2) := by
  have h := intervalIntegral.integral_Iic_sub_Iic
    (integrable_gauss.integrableOn (s := Iic 0))
    (integrable_gauss.integrableOn (s := Iic s))
  unfold G
  rw [← h]
  ring

/-- `G` has derivative `e^{-s²}/√π` at every point (FTC on the split form). -/
private lemma hasDerivAt_G (s : ℝ) :
    HasDerivAt G (Real.exp (-s ^ 2) / Real.sqrt Real.pi) s := by
  have hcont : Continuous fun z : ℝ ↦ Real.exp (-z ^ 2) := by fun_prop
  have h := ((hcont.integral_hasStrictDerivAt 0 s).hasDerivAt.const_mul
    (Real.sqrt Real.pi)⁻¹).const_add (G 0)
  have hfun : G = fun u ↦ G 0 + (Real.sqrt Real.pi)⁻¹ * ∫ z in (0:ℝ)..u,
      Real.exp (-z ^ 2) := funext G_eq_add_intervalIntegral
  rw [hfun]
  simpa [div_eq_inv_mul] using h

/-- The normalized Gaussian density (the closed form of `G'`) has derivative
`-2s e^{-s²}/√π` at every point (chain rule). -/
private lemma hasDerivAt_gaussDensity (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Real.exp (-s ^ 2) / Real.sqrt Real.pi)
      (-(2 * s) * Real.exp (-s ^ 2) / Real.sqrt Real.pi) s := by
  have hin : HasDerivAt (fun s : ℝ ↦ -s ^ 2) (-(2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_mul (-1 : ℝ)
  have hexp : HasDerivAt (fun s : ℝ ↦ Real.exp (-s ^ 2))
      (Real.exp (-s ^ 2) * (-(2 * s))) s := hin.exp
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    hexp.div_const (Real.sqrt Real.pi)

/-- The closed form of `G'` is `C^∞`. -/
private lemma contDiff_G_deriv :
    ContDiff ℝ ∞ (fun s : ℝ ↦ Real.exp (-s ^ 2) / Real.sqrt Real.pi) := by
  have : ContDiff ℝ ∞ (fun s : ℝ ↦ Real.exp (-s ^ 2)) :=
    Real.contDiff_exp.comp ((contDiff_id.pow 2).neg)
  exact this.div_const _

/-- **Smoothness and derivatives of `G`** (blueprint `lem:problem24-G-deriv`):
`G` is `C^∞` on `ℝ` with `G'(s) = e^{-s²}/√π` and
`G''(s) = -2s e^{-s²}/√π`. -/
lemma G_smooth_deriv :
    ContDiff ℝ ∞ G ∧
      (∀ s : ℝ, deriv G s = Real.exp (-s ^ 2) / Real.sqrt Real.pi) ∧
      (∀ s : ℝ, deriv (deriv G) s
        = -(2 * s) * Real.exp (-s ^ 2) / Real.sqrt Real.pi) := by
  have hderiv : deriv G = fun s ↦ Real.exp (-s ^ 2) / Real.sqrt Real.pi :=
    funext fun s ↦ (hasDerivAt_G s).deriv
  refine ⟨?_, fun s ↦ by rw [hderiv], fun s ↦ ?_⟩
  · -- differentiable + C^∞ derivative ⇒ C^∞
    rw [contDiff_infty_iff_deriv]
    exact ⟨fun s ↦ (hasDerivAt_G s).differentiableAt, hderiv ▸ contDiff_G_deriv⟩
  · -- second derivative by the chain rule on the closed form of G'
    rw [hderiv]
    exact (hasDerivAt_gaussDensity s).deriv

/-! ## The closed form of the convolution -/

/-- **Closed form** (blueprint `lem:problem24-closed-form`): for `t > 0`,
`u t x = G (x / (2√t))`. The convolution integral is evaluated by restricting
to the half-line, reflecting/translating `y ↦ x - y`, and scaling
`w = 2√t·z`. -/
lemma u_eq_gauss {t : ℝ} (ht : 0 < t) (x : ℝ) :
    u t x = G (x / (2 * Real.sqrt t)) := by
  have hst : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hc : (0:ℝ) < 2 * Real.sqrt t := by positivity
  -- Step 1: indicator reduction to the half-line.
  have h1 : u t x = ∫ y in Ici (0:ℝ), heatKernel 1 (x - y) t := by
    rw [u, ← integral_indicator measurableSet_Ici]
    congr 1
    funext y
    by_cases hy : (0:ℝ) ≤ y
    · simp [g, hy]
    · simp [g, hy]
  -- Step 2: reflect/translate `y ↦ x - y`, mapping `Ici 0` onto `Iic x`.
  have h2 : (∫ y in Ici (0:ℝ), heatKernel 1 (x - y) t)
      = ∫ w in Iic x, heatKernel 1 w t := by
    have hmp : MeasurePreserving (fun y : ℝ ↦ x - y) volume volume :=
      Measure.measurePreserving_sub_left volume x
    have hemb : MeasurableEmbedding (fun y : ℝ ↦ x - y) :=
      (MeasurableEquiv.subLeft x).measurableEmbedding
    have himg : (fun y : ℝ ↦ x - y) '' Ici 0 = Iic x := by
      rw [image_const_sub_Ici, sub_zero]
    calc ∫ y in Ici (0:ℝ), heatKernel 1 (x - y) t
        = ∫ w in (fun y : ℝ ↦ x - y) '' Ici 0, heatKernel 1 w t :=
          (hmp.setIntegral_image_emb hemb (fun w ↦ heatKernel 1 w t)
            (Ici 0)).symm
      _ = ∫ w in Iic x, heatKernel 1 w t := by rw [himg]
  -- The kernel is even in its spatial argument.
  have hK_even : ∀ w : ℝ, heatKernel 1 (-w) t = heatKernel 1 w t := by
    intro w; simp [heatKernel]
  -- Step 3a: reflect the half-line integral to `Ioi (-x)`.
  have h3 : (∫ w in Iic x, heatKernel 1 w t)
      = ∫ w in Ioi (-x), heatKernel 1 w t := by
    rw [← integral_comp_neg_Iic x (fun w ↦ heatKernel 1 w t)]
    congr 1; funext w; exact (hK_even w).symm
  -- Step 3b: scale `w = (2√t)·z`.
  have h4 : (∫ w in Ioi (-x), heatKernel 1 w t)
      = (2 * Real.sqrt t) *
          ∫ z in Ioi (-x / (2 * Real.sqrt t)),
            heatKernel 1 (2 * Real.sqrt t * z) t := by
    have := integral_comp_mul_left_Ioi (fun w ↦ heatKernel 1 w t)
      (-x / (2 * Real.sqrt t)) hc
    rw [mul_div_cancel₀ (-x) hc.ne'] at this
    rw [this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  -- Step 3c: the scaled kernel is the normalized Gaussian.
  have hker : ∀ z : ℝ, heatKernel 1 (2 * Real.sqrt t * z) t
      = (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-z ^ 2) := by
    intro z
    have hsq : (2 * Real.sqrt t * z) ^ 2 = 4 * t * z ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt ht.le]; ring
    unfold heatKernel
    rw [one_div, hsq]
    congr 2
    · ring_nf
    · field_simp
  -- Assemble, converting the constants: `(2√t)/√(4πt) = 1/√π`.
  have hconst : 2 * Real.sqrt t * (Real.sqrt (4 * Real.pi * t))⁻¹
      = (Real.sqrt Real.pi)⁻¹ := by
    have h4πt : Real.sqrt (4 * Real.pi * t)
        = 2 * Real.sqrt t * Real.sqrt Real.pi := by
      rw [show (4:ℝ) * Real.pi * t = (4 * t) * Real.pi by ring,
        Real.sqrt_mul (by positivity),
        show (4:ℝ) * t = 2 ^ 2 * t by norm_num,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [h4πt, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (by positivity : (2 * Real.sqrt t) ≠ 0), one_mul]
  -- Step 3d: reflect back to `Iic (x/(2√t))` using evenness of the Gaussian.
  have h5 : (∫ z in Ioi (-x / (2 * Real.sqrt t)), Real.exp (-z ^ 2))
      = ∫ z in Iic (x / (2 * Real.sqrt t)), Real.exp (-z ^ 2) := by
    rw [show -x / (2 * Real.sqrt t) = -(x / (2 * Real.sqrt t)) by ring,
      ← integral_comp_neg_Iic (x / (2 * Real.sqrt t)) (fun z ↦ Real.exp (-z ^ 2))]
    congr 1; funext z; rw [neg_sq]
  calc u t x
      = ∫ y in Ici (0:ℝ), heatKernel 1 (x - y) t := h1
    _ = ∫ w in Iic x, heatKernel 1 w t := h2
    _ = ∫ w in Ioi (-x), heatKernel 1 w t := h3
    _ = (2 * Real.sqrt t) *
          ∫ z in Ioi (-x / (2 * Real.sqrt t)),
            heatKernel 1 (2 * Real.sqrt t * z) t := h4
    _ = (2 * Real.sqrt t) * ((Real.sqrt (4 * Real.pi * t))⁻¹ *
          ∫ z in Ioi (-x / (2 * Real.sqrt t)), Real.exp (-z ^ 2)) := by
        congr 1
        rw [← integral_const_mul]
        congr 1; funext z; exact hker z
    _ = (Real.sqrt Real.pi)⁻¹ *
          ∫ z in Iic (x / (2 * Real.sqrt t)), Real.exp (-z ^ 2) := by
        rw [← mul_assoc, hconst, h5]
    _ = G (x / (2 * Real.sqrt t)) := rfl

/-! ## Part (b1): smoothness and the heat equation -/

/-- **Problem 24 (b1)** (blueprint `thm:problem24-smooth-solves`): the
convolution `u` is jointly `C^∞` on `(0,∞) × ℝ` and solves the heat equation
`∂ₜu = ∂ₓ²u` there. Read off the closed form `u t x = G (x/(2√t))` by the
chain rule. -/
theorem u_smooth_solves_heat :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ u p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      ∀ t x : ℝ, 0 < t →
        deriv (fun τ ↦ u τ x) t = deriv (fun ξ ↦ deriv (fun ξ' ↦ u t ξ') ξ) x := by
  have hG := G_smooth_deriv.1
  constructor
  · -- Joint smoothness of the closed form `G (x/(2√t))`, transferred by congr.
    have hclosed : ContDiffOn ℝ ∞
        (fun p : ℝ × ℝ ↦ G (p.2 / (2 * Real.sqrt p.1))) (Ioi 0 ×ˢ univ) := by
      intro p hp
      have hp1 : (0:ℝ) < p.1 := hp.1
      have hst : (0:ℝ) < Real.sqrt p.1 := Real.sqrt_pos.mpr hp1
      apply ContDiffAt.contDiffWithinAt
      have hsq : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ Real.sqrt q.1) p :=
        (Real.contDiffAt_sqrt hp1.ne').comp p contDiffAt_fst
      have hη : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ ↦ q.2 / (2 * Real.sqrt q.1)) p :=
        contDiffAt_snd.div (contDiffAt_const.mul hsq)
          (by positivity : (2:ℝ) * Real.sqrt p.1 ≠ 0)
      exact hG.contDiffAt.comp p hη
    exact hclosed.congr fun p hp ↦ u_eq_gauss hp.1 p.2
  · intro t x ht
    have hst : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    -- Time derivative of the closed form by the chain rule.
    have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t :=
      Real.hasDerivAt_sqrt ht.ne'
    have hden : HasDerivAt (fun τ : ℝ ↦ 2 * Real.sqrt τ)
        (2 * (1 / (2 * Real.sqrt t))) t := hsqrt.const_mul 2
    have hdinv : HasDerivAt (fun τ : ℝ ↦ (2 * Real.sqrt τ)⁻¹)
        (-(2 * (1 / (2 * Real.sqrt t))) / (2 * Real.sqrt t) ^ 2) t :=
      hden.inv (by positivity)
    have hinner : HasDerivAt (fun τ : ℝ ↦ x * (2 * Real.sqrt τ)⁻¹)
        (x * (-(2 * (1 / (2 * Real.sqrt t))) / (2 * Real.sqrt t) ^ 2)) t :=
      hdinv.const_mul x
    have hcomp_t : HasDerivAt (fun τ : ℝ ↦ G (x * (2 * Real.sqrt τ)⁻¹))
        (Real.exp (-(x * (2 * Real.sqrt t)⁻¹) ^ 2) / Real.sqrt Real.pi *
          (x * (-(2 * (1 / (2 * Real.sqrt t))) / (2 * Real.sqrt t) ^ 2))) t :=
      (hasDerivAt_G _).comp t hinner
    have hev : (fun τ ↦ u τ x) =ᶠ[𝓝 t] fun τ ↦ G (x * (2 * Real.sqrt τ)⁻¹) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with τ hτ
      rw [u_eq_gauss hτ x, div_eq_mul_inv]
    -- First space derivative of the closed form, at every point.
    have hux : (fun ξ : ℝ ↦ u t ξ) = fun ξ ↦ G (ξ * (2 * Real.sqrt t)⁻¹) := by
      funext ξ; rw [u_eq_gauss ht ξ, div_eq_mul_inv]
    have hlin : ∀ ξ : ℝ, HasDerivAt (fun ξ' : ℝ ↦ ξ' * (2 * Real.sqrt t)⁻¹)
        ((2 * Real.sqrt t)⁻¹) ξ := fun ξ ↦ by
      simpa using (hasDerivAt_id ξ).mul_const (2 * Real.sqrt t)⁻¹
    have hderiv_x : deriv (fun ξ' ↦ u t ξ')
        = fun ξ ↦ Real.exp (-(ξ * (2 * Real.sqrt t)⁻¹) ^ 2) / Real.sqrt Real.pi *
            (2 * Real.sqrt t)⁻¹ := by
      funext ξ
      rw [hux]
      have h := (hasDerivAt_G (ξ * (2 * Real.sqrt t)⁻¹)).comp ξ (hlin ξ)
      exact h.deriv
    -- Second space derivative via the closed form of `G'`.
    have hsecond : HasDerivAt
        (fun ξ ↦ Real.exp (-(ξ * (2 * Real.sqrt t)⁻¹) ^ 2) / Real.sqrt Real.pi *
          (2 * Real.sqrt t)⁻¹)
        (-(2 * (x * (2 * Real.sqrt t)⁻¹)) * Real.exp (-(x * (2 * Real.sqrt t)⁻¹) ^ 2) /
          Real.sqrt Real.pi * (2 * Real.sqrt t)⁻¹ * (2 * Real.sqrt t)⁻¹) x := by
      have h := ((hasDerivAt_gaussDensity (x * (2 * Real.sqrt t)⁻¹)).comp x
        (hlin x)).mul_const (2 * Real.sqrt t)⁻¹
      simpa [Function.comp_def, mul_assoc] using h
    calc deriv (fun τ ↦ u τ x) t
        = Real.exp (-(x * (2 * Real.sqrt t)⁻¹) ^ 2) / Real.sqrt Real.pi *
            (x * (-(2 * (1 / (2 * Real.sqrt t))) / (2 * Real.sqrt t) ^ 2)) := by
          rw [hev.deriv_eq, hcomp_t.deriv]
      _ = -(2 * (x * (2 * Real.sqrt t)⁻¹)) *
            Real.exp (-(x * (2 * Real.sqrt t)⁻¹) ^ 2) /
            Real.sqrt Real.pi * (2 * Real.sqrt t)⁻¹ * (2 * Real.sqrt t)⁻¹ := by
          field_simp
      _ = deriv (fun ξ ↦ deriv (fun ξ' ↦ u t ξ') ξ) x := by
          simp only [hderiv_x]
          exact hsecond.deriv.symm

/-! ## Part (b2): the pointwise initial limit -/

/-- **Problem 24 (b2)** (blueprint `thm:problem24-initial-limit`): as
`t → 0⁺`, `u(t, x) → g̃(x)` where `g̃` is `1` for `x > 0`, `1/2` at `x = 0`,
and `0` for `x < 0` — the datum at its points of continuity and the average
of the one-sided values at the jump. -/
theorem u_tendsto_initial (x : ℝ) :
    Tendsto (fun t ↦ u t x) (𝓝[>] 0)
      (𝓝 (if x < 0 then 0 else if x = 0 then 1 / 2 else 1)) := by
  -- `u t x = G (x/(2√t))` eventually on `𝓝[>] 0`.
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), G (x / (2 * Real.sqrt t)) = u t x := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (u_eq_gauss ht x).symm
  -- `2√t → 0⁺` as `t → 0⁺`, so `(2√t)⁻¹ → +∞`.
  have hdenom : Tendsto (fun t : ℝ ↦ 2 * Real.sqrt t) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun t : ℝ ↦ 2 * Real.sqrt t) (𝓝 0) (𝓝 (2 * Real.sqrt 0)) :=
        (Real.continuous_sqrt.const_mul 2).continuousAt
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
      exact mem_Ioi.mpr (by positivity)
  have hinv : Tendsto (fun t : ℝ ↦ (2 * Real.sqrt t)⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp hdenom
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- x < 0: the argument tends to -∞ and G → 0.
    rw [if_pos hx]
    have harg : Tendsto (fun t : ℝ ↦ x / (2 * Real.sqrt t)) (𝓝[>] 0) atBot := by
      simp only [div_eq_mul_inv]
      exact (tendsto_const_mul_atBot_of_neg hx).mpr hinv
    exact (G_limits.2.comp harg).congr' hev
  · -- x = 0: `u t 0 = G 0 = 1/2` is eventually constant.
    rw [if_neg (by rw [hx]; exact lt_irrefl 0), if_pos hx]
    have : ∀ᶠ t in 𝓝[>] (0:ℝ), (1:ℝ) / 2 = u t x := by
      filter_upwards [hev] with t ht
      rw [← ht, hx, zero_div, G_zero]
    exact tendsto_const_nhds.congr' this
  · -- x > 0: the argument tends to +∞ and G → 1.
    rw [if_neg (not_lt.mpr hx.le), if_neg hx.ne']
    have harg : Tendsto (fun t : ℝ ↦ x / (2 * Real.sqrt t)) (𝓝[>] 0) atTop := by
      simp only [div_eq_mul_inv]
      exact hinv.const_mul_atTop hx
    exact (G_limits.1.comp harg).congr' hev

end Problems.Undergraduate.Problem24
