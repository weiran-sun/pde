import Mathlib
import PDE

/-!
# Undergraduate Problem 28: Energy Decay and Uniqueness for the Drift–Reaction Heat Equation

Source: `pde_latex/problems/undergraduate/problem_28.tex` (Math 418/718 Midterm, Problem B).

## Informal statement

> Consider the equation
> ```
>   ∂ₜ u = ∂ₓₓ u − ∂ₓ u + c u,   u(0, x) = g(x),
> ```
> where `c` is a given constant. Consider solutions satisfying
> `u ∈ C²(ℝ₊ × ℝ) ∩ L²(ℝ₊ × ℝ)` and `u → 0`, `∂ₓ u → 0` as `x → ±∞`.
> Let `E(t) = ∫_ℝ u²(t, x) dx` be the energy functional.
> (a) Show that if `c ≤ 0`, then `E(t)` decreases in time.
> (b) Show that for any `c ∈ ℝ`, the equation has at most one solution satisfying
> the conditions prescribed.

## Semantic alignment

The source's solution differentiates `E` under the integral sign over the unbounded
domain `ℝ` and integrates by parts, discarding the boundary flux by the prescribed
decay `u, ∂ₓ u → 0`. Following the blueprint chapter
(`Problems_Undergraduate_Problem28.tex`, "What is assumed and what is proved"),
these analytic steps are **not re-derived** from the `C² ∩ L²` regularity and decay
prescriptions; instead the solution class `IsSolution` packages their conclusions
as **hypotheses**:

* the energy-differentiation identity `E'(t) = 2 ∫ u ∂ₜu dx`
  (field `energy_hasDerivAt` — differentiation under the integral sign);
* the two flux identities `∫ u ∂ₓₓu dx = −∫ (∂ₓu)² dx` (field `flux_diffusion`)
  and `∫ u ∂ₓu dx = 0` (field `flux_drift`) — integration by parts on `[A, B]`
  with the flux killed in the limit `A → −∞`, `B → ∞` by the prescribed decay;
* integrability of the four products `u ∂ₜu`, `u ∂ₓₓu`, `u ∂ₓu`, `(∂ₓu)²`
  (fields `integrable_mul_dt`, `integrable_mul_dxx`, `integrable_mul_dx`,
  `integrable_dx_sq`) — the side conditions for splitting the integral termwise;
* slice continuity and square-integrability (fields `slice_continuous`,
  `sq_integrable`) — the fragments of `C²` and `L²` the arguments use;
* right-continuity of the energy at `t = 0` (field `energy_tendsto_initial`) —
  the endpoint regularity that the source's `C²`-up-to-`{t = 0}` provides.

What **is proved** is everything downstream: substituting the PDE into the energy
derivative and splitting the integral (`energy_deriv_eq`), the sign analysis for
part (a) (`energy_antitone`), the Grönwall argument for part (b) (`uniqueness`,
via Mathlib's `le_gronwallBound_of_liminf_deriv_right_le`), and the pointwise
upgrade (`uniqueness_pointwise`).

Derivatives are spelled as slice derivatives: the `t`-derivative as
`deriv (fun τ ↦ u τ x) t`, the `x`-derivatives as `deriv (fun ξ ↦ u t ξ) x` and
`deriv (deriv (fun ξ ↦ u t ξ)) x`, matching the blueprint chapter.
-/

open Real MeasureTheory Filter Set

namespace Problems.Undergraduate.Problem28

/-- **The energy functional** (blueprint `def:problem28-energy`).
For `u : ℝ → ℝ → ℝ` (time first) and `t : ℝ`, the energy of `u` at time `t` is
`E_u(t) = ∫_ℝ u(t,x)² dx`, the Lebesgue integral of the square of the spatial
slice. -/
noncomputable def energy (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (u t x) ^ 2

/-- The energy is nonnegative, with no hypothesis on `u` (the integrand is a
square). Part of blueprint `def:problem28-energy`. -/
theorem energy_nonneg (u : ℝ → ℝ → ℝ) (t : ℝ) : 0 ≤ energy u t :=
  integral_nonneg fun _ => sq_nonneg _

/-- **The prescribed solution class** (blueprint `def:problem28-solution`).
A function `u : ℝ → ℝ → ℝ` (time first) lies in the solution class for the datum
`g` if it satisfies the initial condition, the PDE
`∂ₜu = ∂ₓₓu − ∂ₓu + c u` for `t > 0`, and the analytic package that in the
source follows from the prescribed `C² ∩ L²` regularity and the decay
`u, ∂ₓu → 0` as `x → ±∞`: slice continuity and square-integrability,
integrability of the four products, differentiation of the energy under the
integral sign, the two boundary-flux identities, and right-continuity of the
energy at `t = 0`. See the module docstring for the assumed-vs-proved split. -/
structure IsSolution (c : ℝ) (g : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  /-- Field 1 (initial datum): `u(0, x) = g(x)`. -/
  initial : ∀ x, u 0 x = g x
  /-- Field 2 (PDE): `∂ₜu = ∂ₓₓu − ∂ₓu + c u` for `t > 0`. -/
  pde : ∀ t, 0 < t → ∀ x, deriv (fun τ => u τ x) t =
      deriv (deriv (fun ξ => u t ξ)) x - deriv (fun ξ => u t ξ) x + c * u t x
  /-- Field 3 (slice regularity): each spatial slice is continuous. -/
  slice_continuous : ∀ t, 0 ≤ t → Continuous fun x => u t x
  /-- Field 4 (square-integrability of slices): `x ↦ u(t,x)²` is integrable. -/
  sq_integrable : ∀ t, 0 ≤ t → Integrable fun x => (u t x) ^ 2
  /-- Field 5a (integrability of the products): `x ↦ u ∂ₜu` is integrable. -/
  integrable_mul_dt : ∀ t, 0 < t →
      Integrable fun x => u t x * deriv (fun τ => u τ x) t
  /-- Field 5b (integrability of the products): `x ↦ u ∂ₓₓu` is integrable. -/
  integrable_mul_dxx : ∀ t, 0 < t →
      Integrable fun x => u t x * deriv (deriv (fun ξ => u t ξ)) x
  /-- Field 5c (integrability of the products): `x ↦ u ∂ₓu` is integrable. -/
  integrable_mul_dx : ∀ t, 0 < t →
      Integrable fun x => u t x * deriv (fun ξ => u t ξ) x
  /-- Field 5d (integrability of the products): `x ↦ (∂ₓu)²` is integrable. -/
  integrable_dx_sq : ∀ t, 0 < t →
      Integrable fun x => (deriv (fun ξ => u t ξ) x) ^ 2
  /-- Field 6 (energy differentiation): differentiation under the integral sign,
  `E_u'(t) = 2 ∫ u ∂ₜu dx` for `t > 0`. -/
  energy_hasDerivAt : ∀ t, 0 < t →
      HasDerivAt (energy u) (2 * ∫ x, u t x * deriv (fun τ => u τ x) t) t
  /-- Field 7 (flux identity for the diffusion term):
  `∫ u ∂ₓₓu dx = −∫ (∂ₓu)² dx` for `t > 0`. -/
  flux_diffusion : ∀ t, 0 < t →
      (∫ x, u t x * deriv (deriv (fun ξ => u t ξ)) x) =
        -∫ x, (deriv (fun ξ => u t ξ) x) ^ 2
  /-- Field 8 (flux identity for the drift term): `∫ u ∂ₓu dx = 0` for `t > 0`. -/
  flux_drift : ∀ t, 0 < t → (∫ x, u t x * deriv (fun ξ => u t ξ) x) = 0
  /-- Field 9 (continuity of the energy at the initial time): `E_u` is
  right-continuous at `t = 0`. -/
  energy_tendsto_initial :
      Filter.Tendsto (energy u) (nhdsWithin 0 (Set.Ioi 0)) (nhds (energy u 0))

/-- **The energy identity** (blueprint `lem:problem28-energy-identity`, the
source's displayed equation (∗)). For a solution `u` and `t > 0`,

  `E_u'(t) = −2 ∫ (∂ₓu)² dx + 2 c E_u(t)` :

substitute the PDE pointwise under the integral, split by linearity using the
integrability fields, and apply the two flux identities. -/
theorem energy_deriv_eq {c : ℝ} {g : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : IsSolution c g u) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (energy u)
      (-2 * (∫ x, (deriv (fun ξ => u t ξ) x) ^ 2) + 2 * c * energy u t) t := by
  have hA := hu.integrable_mul_dxx t ht
  have hB := hu.integrable_mul_dx t ht
  have hU := (hu.sq_integrable t ht.le).const_mul c
  have hAB : Integrable (fun x => u t x * deriv (deriv (fun ξ => u t ξ)) x -
      u t x * deriv (fun ξ => u t ξ) x) volume := hA.sub hB
  have key : 2 * (∫ x, u t x * deriv (fun τ => u τ x) t) =
      -2 * (∫ x, (deriv (fun ξ => u t ξ) x) ^ 2) + 2 * c * energy u t := by
    have hcong : (∫ x, u t x * deriv (fun τ => u τ x) t) =
        ∫ x, (u t x * deriv (deriv (fun ξ => u t ξ)) x -
          u t x * deriv (fun ξ => u t ξ) x + c * (u t x) ^ 2) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [hu.pde t ht x]; ring
    rw [hcong, integral_add hAB hU, integral_sub hA hB,
      integral_const_mul, hu.flux_diffusion t ht, hu.flux_drift t ht]
    simp only [energy]
    ring
  exact key ▸ hu.energy_hasDerivAt t ht

/-- **Part (a): the energy is nonincreasing**
(blueprint `thm:problem28-energy-decay`). If `c ≤ 0` and `u` lies in the
solution class, then `E_u` is nonincreasing on `[0, ∞)`: for `0 ≤ s ≤ t`,
`E_u(t) ≤ E_u(s)`. The derivative is `≤ 2 c E_u ≤ 0` by the energy identity,
and `E_u` is continuous on `[0, ∞)` (differentiable on `(0, ∞)`,
right-continuous at `0`). -/
theorem energy_antitone {c : ℝ} (hc : c ≤ 0) {g : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : IsSolution c g u) : AntitoneOn (energy u) (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · -- continuity on `Ici 0`
    intro t ht
    obtain rfl | ht' := (Set.mem_Ici.mp ht).eq_or_lt
    · exact continuousWithinAt_Ioi_iff_Ici.mp hu.energy_tendsto_initial
    · exact (energy_deriv_eq hu ht').continuousAt.continuousWithinAt
  · -- differentiability on the interior
    rw [interior_Ici]
    exact fun t ht =>
      (energy_deriv_eq hu ht).differentiableAt.differentiableWithinAt
  · -- the derivative is nonpositive on the interior
    rw [interior_Ici]
    intro t ht
    rw [(energy_deriv_eq hu ht).deriv]
    have h1 : (0 : ℝ) ≤ ∫ x, (deriv (fun ξ => u t ξ) x) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have h2 := energy_nonneg u t
    nlinarith [mul_nonneg (neg_nonneg.mpr hc) h2]

/-- **Part (b): uniqueness in the prescribed class**
(blueprint `thm:problem28-uniqueness`). If `u₁, u₂` lie in the solution class
for the datum `g` and their difference lies in the class for the datum `0`
(the PDE and zero-datum fields are automatic by linearity; the analytic package
is a hypothesis for the same reason it is one for `u₁`, `u₂`), then the
difference carries no energy: `E_{u₁−u₂}(t) = 0` for all `t ≥ 0`.

Proof: `E(0) = 0` from the zero datum; the energy identity gives the one-sided
bound `E' ≤ 2|c| E` on `(0, ∞)`; Grönwall
(`le_gronwallBound_of_liminf_deriv_right_le` with `δ = E(t₀)`, `K = 2|c|`,
`ε = 0`) yields `E(t) ≤ E(t₀) e^{2|c|(t−t₀)}` on `[t₀, t]`; let `t₀ → 0⁺`
using right-continuity of the energy at `0`. -/
theorem uniqueness {c : ℝ} {g : ℝ → ℝ} {u₁ u₂ : ℝ → ℝ → ℝ}
    (_hu₁ : IsSolution c g u₁) (_hu₂ : IsSolution c g u₂)
    (hd : IsSolution c 0 fun t x => u₁ t x - u₂ t x) :
    ∀ t, 0 ≤ t → energy (fun t x => u₁ t x - u₂ t x) t = 0 := by
  set v : ℝ → ℝ → ℝ := fun t x => u₁ t x - u₂ t x with hv
  -- the energy of the difference vanishes at the initial time
  have hE0 : energy v 0 = 0 := by
    have h0 : ∀ x, v 0 x = 0 := fun x => by simpa using hd.initial x
    have hfun : (fun x => (v 0 x) ^ 2) = fun _ => (0 : ℝ) :=
      funext fun x => by simp [h0 x]
    simp only [energy, hfun]
    simp
  -- the Grönwall estimate on `[t₀, t]` for `0 < t₀ ≤ t`
  have key : ∀ t : ℝ, 0 < t → ∀ t₀ : ℝ, 0 < t₀ → t₀ ≤ t →
      energy v t ≤ energy v t₀ * Real.exp (2 * |c| * (t - t₀)) := by
    intro t ht t₀ ht₀ ht₀t
    have hcont : ContinuousOn (energy v) (Set.Icc t₀ t) := fun s hs =>
      (energy_deriv_eq hd (lt_of_lt_of_le ht₀ hs.1)).continuousAt.continuousWithinAt
    have hslope : ∀ s ∈ Set.Ico t₀ t, ∀ r : ℝ,
        (-2 * (∫ x, (deriv (fun ξ => v s ξ) x) ^ 2) + 2 * c * energy v s) < r →
        ∃ᶠ z in nhdsWithin s (Set.Ioi s),
          (z - s)⁻¹ * (energy v z - energy v s) < r := by
      intro s hs r hr
      have hda := energy_deriv_eq hd (lt_of_lt_of_le ht₀ hs.1)
      have hmono : nhdsWithin s (Set.Ioi s) ≤ nhdsWithin s {s}ᶜ :=
        nhdsWithin_mono s fun z hz =>
          Set.mem_compl_singleton_iff.mpr (ne_of_gt hz)
      have hts := hda.tendsto_slope.mono_left hmono
      have hev : ∀ᶠ z in nhdsWithin s (Set.Ioi s), slope (energy v) s z < r :=
        hts.eventually_lt_const hr
      refine (hev.mono fun z hz => ?_).frequently
      rwa [slope_def_field, div_eq_inv_mul] at hz
    have hbound : ∀ s ∈ Set.Ico t₀ t,
        (-2 * (∫ x, (deriv (fun ξ => v s ξ) x) ^ 2) + 2 * c * energy v s) ≤
          2 * |c| * energy v s + 0 := by
      intro s hs
      have h1 : (0 : ℝ) ≤ ∫ x, (deriv (fun ξ => v s ξ) x) ^ 2 :=
        integral_nonneg fun _ => sq_nonneg _
      have h2 := energy_nonneg v s
      have h3 : c ≤ |c| := le_abs_self c
      nlinarith [mul_nonneg (sub_nonneg.mpr h3) h2]
    have hgron := le_gronwallBound_of_liminf_deriv_right_le hcont hslope
      le_rfl hbound t ⟨ht₀t, le_rfl⟩
    rwa [gronwallBound_ε0] at hgron
  intro t ht
  obtain rfl | htpos := ht.eq_or_lt
  · exact hE0
  -- let `t₀ → 0⁺`: the Grönwall bound tends to `0`
  refine le_antisymm ?_ (energy_nonneg v t)
  have h9 : Filter.Tendsto (energy v) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := hd.energy_tendsto_initial
    rwa [hE0] at this
  have hexp : Filter.Tendsto (fun t₀ : ℝ => Real.exp (2 * |c| * (t - t₀)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp (2 * |c| * t))) := by
    have hcexp : Continuous fun t₀ : ℝ => Real.exp (2 * |c| * (t - t₀)) := by
      fun_prop
    simpa using (hcexp.tendsto 0).mono_left nhdsWithin_le_nhds
  have hprod : Filter.Tendsto
      (fun t₀ : ℝ => energy v t₀ * Real.exp (2 * |c| * (t - t₀)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using h9.mul hexp
  have hev : ∀ᶠ t₀ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      energy v t ≤ energy v t₀ * Real.exp (2 * |c| * (t - t₀)) := by
    filter_upwards [Ioo_mem_nhdsGT htpos] with t₀ ht₀
    exact key t htpos t₀ ht₀.1 ht₀.2.le
  exact ge_of_tendsto hprod hev

/-- **Pointwise uniqueness** (blueprint `cor:problem28-uniqueness-pointwise`).
Under the hypotheses of `uniqueness`, `u₁(t,x) = u₂(t,x)` for all `t ≥ 0` and
`x ∈ ℝ`: the slice of the difference is continuous, nonnegative after squaring,
integrable, and has vanishing integral, hence vanishes a.e. and (by continuity)
everywhere. -/
theorem uniqueness_pointwise {c : ℝ} {g : ℝ → ℝ} {u₁ u₂ : ℝ → ℝ → ℝ}
    (hu₁ : IsSolution c g u₁) (hu₂ : IsSolution c g u₂)
    (hd : IsSolution c 0 fun t x => u₁ t x - u₂ t x) :
    ∀ t, 0 ≤ t → ∀ x, u₁ t x = u₂ t x := by
  intro t ht x
  set v : ℝ → ℝ → ℝ := fun t x => u₁ t x - u₂ t x with hv
  have hE : energy v t = 0 := uniqueness hu₁ hu₂ hd t ht
  have hnonneg : (0 : ℝ → ℝ) ≤ fun x => (v t x) ^ 2 := fun _ => sq_nonneg _
  have hint : Integrable fun x => (v t x) ^ 2 := hd.sq_integrable t ht
  have hae : (fun x => (v t x) ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hint).mp hE
  have hcont : Continuous fun x => (v t x) ^ 2 :=
    (hd.slice_continuous t ht).pow 2
  have heq : (fun x => (v t x) ^ 2) = 0 :=
    (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae
  have hx : (v t x) ^ 2 = 0 := by simpa using congrFun heq x
  have hvx : v t x = 0 := by
    exact pow_eq_zero_iff two_ne_zero |>.mp hx
  exact sub_eq_zero.mp hvx

end Problems.Undergraduate.Problem28
