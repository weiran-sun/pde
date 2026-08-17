import Mathlib
import PDE.Basics.Heat.HeatKernelND
import PDE.Background.CalculusMeasureTheory.GraphHausdorffMeasure.R3GraphMeasure

/-!
# Undergraduate Problem 20: Consequences of Poisson's Formula — Normalization,
# Weak Maximum Principle, and Half-Space Decay

Source: `pde_latex/problems/undergraduate/problem_20.tex` (Math 418/718, HW-9,
Problem 1).

## Informal statement

> Let `B(0,R) ⊆ ℝ³` be the open ball of radius `R > 0`.
>
> (a) Prove that `(R² − |x|²)/(4πR) ∫_{∂B(0,R)} |y − x|⁻³ dS_y = 1` for any
> `R > 0` and `x ∈ B(0,R)`.
>
> (b) Use Poisson's formula on `B(0,R)` to prove directly that harmonic
> functions on `B(0,R)` satisfy the weak maximum principle (assuming
> `u ∈ C(closure B(0,R))`).
>
> (c) For the half-space Dirichlet problem on `ℝ³₊` with bounded, compactly
> supported boundary datum `g`, show that the solution given by Poisson's
> formula on the half-space satisfies `u(x) → 0` as `|x| → ∞`.

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem20.tex`:

* The ambient space is `EuclideanSpace ℝ (Fin 3)` (= `Heat.E 3`); the
  half-space `ℝ³₊` is `{x | 0 < x 2}` and its boundary plane is
  `{y | y 2 = 0}` (third coordinate `x₃` is `x 2`).
* All surface integrals are against the Euclidean-normalized 2-dimensional
  Hausdorff measure `μHE[2]`; the sphere has finite total mass
  `μHE[2](∂B(0,R)) = 4πR²` by `GraphAreaFull.sphere_area`.
* **The Poisson formulas are never proved here** — exactly as in the source,
  which *uses* Poisson's formula ("which states that …") without proof. Each
  representation enters as an explicit hypothesis predicate:
  `SatisfiesPoissonFormula` packages the ball formula together with its
  integrability side condition (blueprint `def:problem20-poisson-hyp`), and
  `HalfSpaceRepresentation` packages the half-space formula with its support,
  finiteness, and integrability side conditions (blueprint
  `def:problem20-halfspace-hyp`). Everything downstream is proved.
* Part (a) is the ball hypothesis instantiated at the constant function `1`
  (legitimate because constants are harmonic —
  `Problems.Undergraduate.Problem13.laplacian_const` — and continuous).
* Part (b): the maxima `max_{closure B} u` and `max_{∂B} u` of the source are
  rendered as `sSup (u '' Metric.closedBall 0 R)` and
  `sSup (u '' Metric.sphere 0 R)`; continuity of `u` on the compact closed
  ball makes both suprema attained maxima.
* Part (c): the far-field estimate chain of the source, with the split
  `‖x − y‖ ≥ ‖x‖ − ‖y‖ ≥ ‖x‖/2` for `‖y‖ ≤ R₀ ≤ ‖x‖/2`, the quantitative
  bound `|u(x)| ≤ (4 M μHE[2](K) / π) ‖x‖⁻²`, and the ε–ρ decay statement.
-/

open MeasureTheory Heat
open scoped MeasureTheory RealInnerProductSpace

/-- The ambient Euclidean 3-space `EuclideanSpace ℝ (Fin 3)` (= `Heat.E 3`). -/
local notation "E3" => Heat.E 3

namespace Problems.Undergraduate.Problem20

/-- **The Poisson-formula hypothesis on `B(0,R)`** (blueprint
`def:problem20-poisson-hyp`).

*Poisson's formula holds for `u` on `B(0,R)`* if for every `x ∈ B(0,R)`:

1. (Integrability side condition) `y ↦ u(y) ‖x − y‖⁻³` is integrable on the
   sphere `∂B(0,R)` with respect to `μHE[2]`;
2. (The formula) `u(x) = (R² − ‖x‖²)/(4πR) ∫_{∂B(0,R)} u(y) ‖x − y‖⁻³ dμHE²(y)`.

The integrand is well defined on the sphere: for `x ∈ B(0,R)` and
`y ∈ ∂B(0,R)` we have `‖x‖ < R = ‖y‖`, so `x ≠ y` and `‖x − y‖ > 0`. In the
source this hypothesis is available for every harmonic
`u ∈ C²(B(0,R)) ∩ C(closure B(0,R))`; here it is taken as the definition of
the class of functions the ball results apply to. -/
structure SatisfiesPoissonFormula (R : ℝ) (u : E3 → ℝ) : Prop where
  /-- Integrability side condition: the Poisson integrand is `μHE[2]`-integrable
  on the boundary sphere, for every interior point `x`. -/
  integrable : ∀ x ∈ Metric.ball (0 : E3) R,
      IntegrableOn (fun y => u y * (1 / ‖x - y‖ ^ 3))
        (Metric.sphere (0 : E3) R) μHE[2]
  /-- The formula: `u` is represented by its Poisson integral at every interior
  point. -/
  formula : ∀ x ∈ Metric.ball (0 : E3) R,
      u x = (R ^ 2 - ‖x‖ ^ 2) / (4 * Real.pi * R) *
        ∫ y in Metric.sphere (0 : E3) R, u y * (1 / ‖x - y‖ ^ 3) ∂μHE[2]

/-- **Part (a): the kernel integrates to one** (blueprint
`thm:problem20-normalization`).

If Poisson's formula holds for the constant function `1` on `B(0,R)` — the
instantiation the source justifies by noting that `1` is harmonic
(`Problems.Undergraduate.Problem13.laplacian_const`) and continuous on the
closed ball — then for every `x ∈ B(0,R)`,
`(R² − ‖x‖²)/(4πR) ∫_{∂B(0,R)} ‖x − y‖⁻³ dμHE²(y) = 1`. -/
theorem normalization {R : ℝ} (_hR : 0 < R)
    (h1 : SatisfiesPoissonFormula R (fun _ => (1 : ℝ)))
    {x : E3} (hx : x ∈ Metric.ball (0 : E3) R) :
    (R ^ 2 - ‖x‖ ^ 2) / (4 * Real.pi * R) *
      ∫ y in Metric.sphere (0 : E3) R, 1 / ‖x - y‖ ^ 3 ∂μHE[2] = 1 := by
  have h := (h1.formula x hx).symm
  simpa only [one_mul] using h

/-- **Interior values are bounded by the boundary maximum** (blueprint
`lem:problem20-interior-bound`).

Let `R > 0` and let `u` be continuous on `closure B(0,R)`. If Poisson's
formula holds on `B(0,R)` both for `u` and for the constant function `1`,
then `u(x) ≤ max_{∂B(0,R)} u` for every `x ∈ B(0,R)`.

Proof route: pointwise on the sphere `u(y) ‖x−y‖⁻³ ≤ M ‖x−y‖⁻³` with
`M = max_{∂B} u` (the kernel is positive); integrate (both sides integrable by
the two hypotheses); multiply by the positive prefactor; conclude by the
representation for `u` and the normalization (part (a)). -/
lemma interior_le_boundary_max {R : ℝ} (hR : 0 < R) {u : E3 → ℝ}
    (hu : ContinuousOn u (Metric.closedBall (0 : E3) R))
    (hP : SatisfiesPoissonFormula R u)
    (h1 : SatisfiesPoissonFormula R (fun _ => (1 : ℝ)))
    {x : E3} (hx : x ∈ Metric.ball (0 : E3) R) :
    u x ≤ sSup (u '' Metric.sphere (0 : E3) R) := by
  have husph : ContinuousOn u (Metric.sphere (0 : E3) R) :=
    hu.mono Metric.sphere_subset_closedBall
  have hbdd : BddAbove (u '' Metric.sphere (0 : E3) R) :=
    ((isCompact_sphere (0 : E3) R).image_of_continuousOn husph).bddAbove
  set M := sSup (u '' Metric.sphere (0 : E3) R) with hMdef
  -- Pointwise comparison on the sphere: `u y ≤ M` and the kernel is nonnegative.
  have hle : ∀ y ∈ Metric.sphere (0 : E3) R, u y ≤ M := fun y hy =>
    le_csSup hbdd (Set.mem_image_of_mem u hy)
  -- Integral comparison, both sides integrable by the two hypotheses.
  have hint_u := hP.integrable x hx
  have hint_M : IntegrableOn (fun y => M * (1 / ‖x - y‖ ^ 3))
      (Metric.sphere (0 : E3) R) μHE[2] := by
    have h := (h1.integrable x hx).const_mul M
    simp only [one_mul] at h
    exact h
  have hmono : ∫ y in Metric.sphere (0 : E3) R, u y * (1 / ‖x - y‖ ^ 3) ∂μHE[2]
      ≤ ∫ y in Metric.sphere (0 : E3) R, M * (1 / ‖x - y‖ ^ 3) ∂μHE[2] := by
    refine MeasureTheory.setIntegral_mono_on hint_u hint_M
      Metric.isClosed_sphere.measurableSet fun y hy => ?_
    exact mul_le_mul_of_nonneg_right (hle y hy) (by positivity)
  -- The prefactor is nonnegative since `‖x‖ < R`.
  have hxR : ‖x‖ < R := by
    simpa [Metric.mem_ball, dist_zero_right] using hx
  have hpre : 0 ≤ (R ^ 2 - ‖x‖ ^ 2) / (4 * Real.pi * R) := by
    have hnum : 0 ≤ R ^ 2 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have hden : 0 < 4 * Real.pi * R := by positivity
    exact div_nonneg hnum hden.le
  calc u x
      = (R ^ 2 - ‖x‖ ^ 2) / (4 * Real.pi * R) *
        ∫ y in Metric.sphere (0 : E3) R, u y * (1 / ‖x - y‖ ^ 3) ∂μHE[2] :=
      hP.formula x hx
    _ ≤ (R ^ 2 - ‖x‖ ^ 2) / (4 * Real.pi * R) *
        ∫ y in Metric.sphere (0 : E3) R, M * (1 / ‖x - y‖ ^ 3) ∂μHE[2] :=
      mul_le_mul_of_nonneg_left hmono hpre
    _ = M * ((R ^ 2 - ‖x‖ ^ 2) / (4 * Real.pi * R) *
        ∫ y in Metric.sphere (0 : E3) R, 1 / ‖x - y‖ ^ 3 ∂μHE[2]) := by
      rw [MeasureTheory.integral_const_mul]; ring
    _ = M * 1 := by rw [normalization hR h1 hx]
    _ = M := mul_one M

/-- **Part (b): the weak maximum principle on the ball** (blueprint
`thm:problem20-weak-max`).

Let `R > 0` and let `u` be continuous on `closure B(0,R)`. If Poisson's
formula holds on `B(0,R)` both for `u` and for the constant function `1`,
then the maximum of `u` over the closed ball is attained on the boundary
sphere: `max_{closure B(0,R)} u = max_{∂B(0,R)} u`. Both maxima exist (and the
suprema below are attained) since `u` is continuous on the nonempty compact
sets `closure B(0,R)` and `∂B(0,R)`. -/
theorem weak_maximum_principle {R : ℝ} (hR : 0 < R) {u : E3 → ℝ}
    (hu : ContinuousOn u (Metric.closedBall (0 : E3) R))
    (hP : SatisfiesPoissonFormula R u)
    (h1 : SatisfiesPoissonFormula R (fun _ => (1 : ℝ))) :
    sSup (u '' Metric.closedBall (0 : E3) R)
      = sSup (u '' Metric.sphere (0 : E3) R) := by
  have hsph_ne : (Metric.sphere (0 : E3) R).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hR.le
  have hball_bdd : BddAbove (u '' Metric.closedBall (0 : E3) R) :=
    ((isCompact_closedBall (0 : E3) R).image_of_continuousOn hu).bddAbove
  refine le_antisymm ?_ ?_
  · -- `≤`: every point of the closed ball is interior or boundary; both give
    -- `u x ≤ sSup (u '' sphere)`.
    refine csSup_le ((hsph_ne.mono Metric.sphere_subset_closedBall).image u) ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hx) with hx' | hx'
    · exact interior_le_boundary_max hR hu hP h1 (Metric.mem_ball.mpr hx')
    · have hbdd : BddAbove (u '' Metric.sphere (0 : E3) R) :=
        ((isCompact_sphere (0 : E3) R).image_of_continuousOn
          (hu.mono Metric.sphere_subset_closedBall)).bddAbove
      exact le_csSup hbdd (Set.mem_image_of_mem u (Metric.mem_sphere.mpr hx'))
  · -- `≥`: the sphere is contained in the closed ball.
    exact csSup_le_csSup hball_bdd (hsph_ne.image u)
      (Set.image_mono Metric.sphere_subset_closedBall)

/-- **The half-space Poisson representation** (blueprint
`def:problem20-halfspace-hyp`).

*`u` is represented by the half-space Poisson integral of `g` with support
`K`* if:

1. (Support in the boundary plane) `K ⊆ ∂ℝ³₊ = {y | y₃ = 0}` and `g` vanishes
   off `K`;
2. (Finiteness of the support's area) `μHE[2](K) < ∞`;
3. (Integrability side condition) for every `x ∈ ℝ³₊` (i.e. `x₃ > 0`), the
   function `y ↦ g(y) ‖x − y‖⁻³` is `μHE[2]`-integrable on `K`;
4. (The formula) `u(x) = (2x₃)/(4π) ∫_K g(y) ‖x − y‖⁻³ dμHE²(y)` for every
   `x ∈ ℝ³₊` (since `g` vanishes off `K`, integrating over `K` is the same as
   over the whole boundary plane, which is the form the source writes).

The integrand is well defined: for `x ∈ ℝ³₊` and `y ∈ K` we have
`x₃ > 0 = y₃`, so `x ≠ y` and `‖x − y‖ > 0`. -/
structure HalfSpaceRepresentation (u g : E3 → ℝ) (K : Set E3) : Prop where
  /-- Support in the boundary plane: `K` lies in `{y | y₃ = 0}`. -/
  support_subset : K ⊆ {y : E3 | y 2 = 0}
  /-- `g` vanishes off `K`. -/
  eq_zero_off_support : ∀ y ∉ K, g y = 0
  /-- Finiteness of the support's area: `μHE[2](K) < ∞`. -/
  finite_area : μHE[2] K < ⊤
  /-- Integrability side condition: `y ↦ g(y) ‖x − y‖⁻³` is `μHE[2]`-integrable
  on `K`, for every `x` in the open half-space. -/
  integrable : ∀ x : E3, 0 < x 2 →
      IntegrableOn (fun y => g y * (1 / ‖x - y‖ ^ 3)) K μHE[2]
  /-- The formula: `u` is the half-space Poisson integral of `g` at every point
  of the open half-space. -/
  formula : ∀ x : E3, 0 < x 2 →
      u x = (2 * x 2) / (4 * Real.pi) *
        ∫ y in K, g y * (1 / ‖x - y‖ ^ 3) ∂μHE[2]

/-- **Far-field kernel bound** (blueprint `lem:problem20-far-kernel-bound`).

If `‖y‖ ≤ R₀` and `‖x‖ ≥ 2R₀` with `R₀ > 0`, then `‖x − y‖ ≥ ‖x‖/2 > 0` and
hence `‖x − y‖⁻³ ≤ 8 ‖x‖⁻³`. Triangle inequality
`‖x − y‖ ≥ ‖x‖ − ‖y‖ ≥ ‖x‖ − R₀ ≥ ‖x‖/2`, then cube and take reciprocals. -/
lemma far_kernel_bound {R₀ : ℝ} (hR₀ : 0 < R₀) {x y : E3}
    (hy : ‖y‖ ≤ R₀) (hx : 2 * R₀ ≤ ‖x‖) :
    ‖x‖ / 2 ≤ ‖x - y‖ ∧ 1 / ‖x - y‖ ^ 3 ≤ 8 / ‖x‖ ^ 3 := by
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by linarith) hx
  have hdist : ‖x‖ / 2 ≤ ‖x - y‖ := by
    have htri : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
    linarith
  refine ⟨hdist, ?_⟩
  have hcube : (‖x‖ / 2) ^ 3 ≤ ‖x - y‖ ^ 3 :=
    pow_le_pow_left₀ (by positivity) hdist 3
  have hpos : (0 : ℝ) < (‖x‖ / 2) ^ 3 := by positivity
  calc 1 / ‖x - y‖ ^ 3 ≤ 1 / (‖x‖ / 2) ^ 3 := by
        apply one_div_le_one_div_of_le hpos hcube
    _ = 8 / ‖x‖ ^ 3 := by ring

/-- **Quantitative far-field bound on the Poisson integral** (blueprint
`lem:problem20-decay-bound`).

Suppose `u` is represented by the half-space Poisson integral of `g` with
support `K`, `|g| ≤ M` with `M ≥ 0`, and `K ⊆ closedBall 0 R₀` with `R₀ > 0`.
Then for every `x` in the open half-space with `‖x‖ ≥ 2R₀`,
`|u(x)| ≤ (4 M μHE[2](K) / π) ‖x‖⁻²`.

Proof route: pointwise `|g(y) ‖x−y‖⁻³| ≤ 8M ‖x‖⁻³` on `K` by
`far_kernel_bound`; integrate (integrand integrable by condition 3, constant
integrable since `μHE[2](K) < ∞`); bound the prefactor by
`|2x₃/(4π)| = x₃/(2π) ≤ ‖x‖/(2π)`; assemble. -/
lemma decay_bound {u g : E3 → ℝ} {K : Set E3} (hKm : MeasurableSet K)
    (hrep : HalfSpaceRepresentation u g K)
    {M : ℝ} (hM : 0 ≤ M) (hg : ∀ y, |g y| ≤ M)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hK : K ⊆ Metric.closedBall (0 : E3) R₀)
    {x : E3} (hx3 : 0 < x 2) (hx : 2 * R₀ ≤ ‖x‖) :
    |u x| ≤ 4 * M * (μHE[2] K).toReal / Real.pi * (1 / ‖x‖ ^ 2) := by
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by linarith) hx
  -- Step 1: pointwise bound `|g(y) ‖x−y‖⁻³| ≤ 8M/‖x‖³` on `K`.
  have hpt : ∀ y ∈ K, |g y * (1 / ‖x - y‖ ^ 3)| ≤ M * (8 / ‖x‖ ^ 3) := by
    intro y hy
    have hyR : ‖y‖ ≤ R₀ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hK hy
    obtain ⟨hd, hker⟩ := far_kernel_bound hR₀ hyR hx
    have hdpos : 0 < ‖x - y‖ := lt_of_lt_of_le (by positivity) hd
    have hker_nonneg : 0 ≤ 1 / ‖x - y‖ ^ 3 := by positivity
    rw [abs_mul, abs_of_nonneg hker_nonneg]
    exact mul_le_mul (hg y) hker hker_nonneg hM
  -- Step 2: integral bound via the triangle inequality and monotonicity.
  have hint := hrep.integrable x hx3
  have hbound : |∫ y in K, g y * (1 / ‖x - y‖ ^ 3) ∂μHE[2]|
      ≤ M * (8 / ‖x‖ ^ 3) * (μHE[2] K).toReal := by
    calc |∫ y in K, g y * (1 / ‖x - y‖ ^ 3) ∂μHE[2]|
        ≤ ∫ y in K, |g y * (1 / ‖x - y‖ ^ 3)| ∂μHE[2] :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ _y in K, M * (8 / ‖x‖ ^ 3) ∂μHE[2] := by
          exact MeasureTheory.setIntegral_mono_on hint.abs
            (MeasureTheory.integrableOn_const hrep.finite_area.ne) hKm hpt
      _ = M * (8 / ‖x‖ ^ 3) * (μHE[2] K).toReal := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul,
            MeasureTheory.measureReal_def, mul_comm]
  -- Step 3: the prefactor is at most `‖x‖/(2π)`.
  have hx3norm : x 2 ≤ ‖x‖ := by
    calc x 2 ≤ |x 2| := le_abs_self _
      _ = ‖x 2‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := PiLp.norm_apply_le x 2
  -- Step 4: assemble.
  rw [hrep.formula x hx3, abs_mul]
  have hpre : |(2 * x 2) / (4 * Real.pi)| ≤ ‖x‖ / (2 * Real.pi) := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_pos]
  calc |(2 * x 2) / (4 * Real.pi)| * |∫ y in K, g y * (1 / ‖x - y‖ ^ 3) ∂μHE[2]|
      ≤ ‖x‖ / (2 * Real.pi) * (M * (8 / ‖x‖ ^ 3) * (μHE[2] K).toReal) := by
        refine mul_le_mul hpre hbound (abs_nonneg _) (by positivity)
    _ = 4 * M * (μHE[2] K).toReal / Real.pi * (1 / ‖x‖ ^ 2) := by
        field_simp
        ring

/-- **Part (c): decay at infinity** (blueprint `thm:problem20-halfspace-decay`).

Let `K` be compact, `g` bounded, and suppose `u` is represented by the
half-space Poisson integral of `g` with support `K`. Then `u` tends to `0` at
infinity within the half-space: for every `ε > 0` there is `ρ > 0` such that
`|u(x)| ≤ ε` for every `x ∈ ℝ³₊` with `‖x‖ ≥ ρ`.

Proof route: pick `M` bounding `|g|` and `R₀ > 0` with
`K ⊆ closedBall 0 R₀`; set `C = 4 M μHE[2](K) / π` and
`ρ = max (2R₀) √(C/ε)`; conclude by `decay_bound`. -/
theorem halfspace_decay {u g : E3 → ℝ} {K : Set E3} (hK : IsCompact K)
    {M : ℝ} (hg : ∀ y, |g y| ≤ M)
    (hrep : HalfSpaceRepresentation u g K) :
    ∀ ε > 0, ∃ ρ > 0, ∀ x : E3, 0 < x 2 → ρ ≤ ‖x‖ → |u x| ≤ ε := by
  intro ε hε
  -- `M ≥ 0` since it dominates an absolute value.
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hg 0)
  -- `K` is compact, hence bounded: enclose it in a closed ball of positive
  -- radius.
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : E3)
  set R₀ : ℝ := max r 1 with hR₀def
  have hR₀ : (0 : ℝ) < R₀ := lt_of_lt_of_le one_pos (le_max_right r 1)
  have hKR₀ : K ⊆ Metric.closedBall (0 : E3) R₀ :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left r 1))
  -- The constant of the quantitative bound.
  set C : ℝ := 4 * M * (μHE[2] K).toReal / Real.pi with hCdef
  have hC : 0 ≤ C := by positivity
  refine ⟨max (2 * R₀) (Real.sqrt (C / ε)), lt_of_lt_of_le (by linarith)
    (le_max_left _ _), fun x hx3 hρx => ?_⟩
  have hx2R₀ : 2 * R₀ ≤ ‖x‖ := le_trans (le_max_left _ _) hρx
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by linarith) hx2R₀
  -- The quantitative far-field bound applies.
  have hbound := decay_bound hK.isClosed.measurableSet hrep hM hg hR₀ hKR₀
    hx3 hx2R₀
  -- And `C/‖x‖² ≤ ε` since `‖x‖ ≥ √(C/ε)`.
  have hsqrt : Real.sqrt (C / ε) ≤ ‖x‖ := le_trans (le_max_right _ _) hρx
  have hsq : C / ε ≤ ‖x‖ ^ 2 := by
    have := Real.sq_sqrt (div_nonneg hC hε.le)
    nlinarith [Real.sqrt_nonneg (C / ε)]
  have hfinal : C * (1 / ‖x‖ ^ 2) ≤ ε := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at hsq
    linarith
  exact le_trans hbound hfinal

end Problems.Undergraduate.Problem20
