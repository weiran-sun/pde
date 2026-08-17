import PDE.Methods.Galerkin.Parabolic.ParabolicExistence
import PDE.Methods.ODEMethods.CaratheodoryExistence

/-!
# Galerkin ODE solvability in the honest Carathéodory regime

`parabolic_operator_v2` fielded `galerkin_ode_solvable` because the Galerkin system
`d'(t) = F(t) − A(t)·d(t)` lives in the honest `L∞/L²` regime — the matrix `A(t)ₖⱼ =
B(t)[wⱼ,wₖ]` and forcing `F(t)ₖ = (f t, wₖ)` are merely *measurable* in `t` — and Mathlib only
has classical Picard–Lindelöf (continuous-in-`t`).  `CaratheodoryFull` supplies the missing
Carathéodory existence theorem; this file consumes it:

* `affine_ode_exists_global_ac` — the affine system with measurable-in-`t`, uniformly bounded
  `A` and integrable forcing has a **global** solution on `[0,T]`: continuous, satisfying the
  integral equation, differentiable a.e. with the ODE a.e.  Continuation of local Carathéodory
  steps; the step length is uniform because the ball radius `‖x0‖+1` is slaved to the start
  value, so no a-priori Grönwall bound is needed.
* `galerkin_ode_solvable_ac` — the Galerkin system of `exists_weakSolution` is globally solvable
  under v2's own hypotheses (`hP_bdd` + the `hP_tmeas` measurability duct-tape + `f : L2TL2`):
  the solution is continuous (absolutely continuous, via its integral equation) and satisfies
  v2's `GalerkinODE` (the a.e. ODE + initial condition).  This supersedes v2's sorried
  `galerkin_ode_solvable`, whose statement was both duct-taped (continuity in `t` assumed) and
  too strong (`∃!` fails: the a.e. ODE does not pin the solution).

**On completing `exists_weakSolution` itself**: its internal coefficient-construction sorry
demands `ContDiff ℝ 1` coefficients, which is *unprovable* in the honest regime — with
measurable-in-`t` data the coefficients are absolutely continuous, not `C¹` (e.g. forcing by the
indicator of a fat Cantor set admits no `C¹` solution).  The remaining gap is therefore not
existence (closed here) but the generalization of the energy/limit pipeline from `C¹` to
absolutely continuous coefficients (integral-form energy identity and Grönwall); the integral
equation delivered by `galerkin_ode_solvable_ac` is exactly the input that pipeline needs. -/

open MeasureTheory ENNReal Filter Topology NNReal

variable {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}

section AffineCaratheodory

variable {m : ℕ}

/-- Assemble a.e. strong measurability of a `Fin m → ℝ`-valued map from its components. -/
private lemma aestronglyMeasurable_pi_of_components {μ : Measure ℝ} {G : ℝ → Fin m → ℝ}
    (h : ∀ k, AEStronglyMeasurable (fun t => G t k) μ) : AEStronglyMeasurable G μ :=
  (aemeasurable_pi_iff.2 (fun k => (h k).aemeasurable)).aestronglyMeasurable

/-- The affine field is continuous in `y` for every fixed `t` (it is affine). -/
private lemma affineField_continuous_in_y (A : ℝ → Fin m → Fin m → ℝ) (F : ℝ → Fin m → ℝ)
    (t : ℝ) : Continuous (affineField A F t) := by
  refine continuous_pi (fun k => ?_)
  exact continuous_const.sub (continuous_finsetSum _ (fun j _ =>
    continuous_const.mul (continuous_apply j)))

/-- Composition of the (measurable-in-`t`) affine field with a continuous curve is a.e. strongly
measurable. -/
lemma affineField_comp_aestronglyMeasurable {A : ℝ → Fin m → Fin m → ℝ} {F : ℝ → Fin m → ℝ}
    (hAmeas : ∀ k j, AEStronglyMeasurable (fun t => A t k j) volume)
    (hFmeas : ∀ k, AEStronglyMeasurable (fun t => F t k) volume)
    {γ : ℝ → Fin m → ℝ} (hγ : Continuous γ) :
    AEStronglyMeasurable (fun t => affineField A F t (γ t)) volume := by
  refine aestronglyMeasurable_pi_of_components (fun k => ?_)
  have hsum : AEStronglyMeasurable (fun t => ∑ j, A t k j * γ t j) volume := by
    have h := Finset.aestronglyMeasurable_sum (μ := volume) Finset.univ
      (f := fun j : Fin m => fun t => A t k j * γ t j)
      (fun j _ => (hAmeas k j).mul ((continuous_apply j).comp hγ).aestronglyMeasurable)
    have heq : (∑ j : Fin m, fun t => A t k j * γ t j)
        = fun t => ∑ j : Fin m, A t k j * γ t j := by
      funext t
      simp [Finset.sum_apply]
    rwa [heq] at h
  exact (hFmeas k).sub hsum

/-- Composition of the affine field with a continuous curve is interval integrable (dominated by
`‖F‖ + m·κ·sup‖γ‖` on the compact interval). -/
lemma affineField_comp_intervalIntegrable {A : ℝ → Fin m → Fin m → ℝ} {F : ℝ → Fin m → ℝ}
    {κ : ℝ} (hκ : 0 ≤ κ) (hA : ∀ t k j, |A t k j| ≤ κ)
    (hAmeas : ∀ k j, AEStronglyMeasurable (fun t => A t k j) volume)
    (hFmeas : ∀ k, AEStronglyMeasurable (fun t => F t k) volume)
    (hFint : Integrable (fun t => ‖F t‖) volume)
    {γ : ℝ → Fin m → ℝ} (hγ : Continuous γ) (c c' : ℝ) :
    IntervalIntegrable (fun s => affineField A F s (γ s)) volume c c' := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_uIcc (a := c) (b := c')).image_of_continuousOn hγ.norm.continuousOn).bddAbove
  rw [intervalIntegrable_iff]
  have hbig : IntegrableOn (fun s => affineField A F s (γ s)) (Set.uIcc c c') volume := by
    refine Integrable.mono'
      ((hFint.integrableOn).add
        (integrableOn_const (C := (m : ℝ) * κ * C) (hs := isCompact_uIcc.measure_lt_top.ne)))
      ((affineField_comp_aestronglyMeasurable hAmeas hFmeas hγ).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
    simp only [Pi.add_apply]
    refine (affineField_norm_le hκ hA s (γ s)).trans ?_
    have h1 : ‖γ s‖ ≤ C := hC ⟨s, hs, rfl⟩
    have h2 : (0:ℝ) ≤ (m : ℝ) * κ := mul_nonneg (Nat.cast_nonneg m) hκ
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  exact hbig.mono_set Set.uIoc_subset_uIcc

/-- **Local Carathéodory step** for the affine system, via `CaratheodoryFull.IsSetup`.  The ball
radius is slaved to the start value (`b = ‖x0‖+1`), which makes the admissible step length `δ`
*uniform in the start point* — the continuation needs no a-priori bound. -/
lemma affine_ac_local_step {A : ℝ → Fin m → Fin m → ℝ} {F : ℝ → Fin m → ℝ}
    {κ : ℝ} (hκ : 0 ≤ κ) (hA : ∀ t k j, |A t k j| ≤ κ)
    (hAmeas : ∀ k j, AEStronglyMeasurable (fun t => A t k j) volume)
    (hFmeas : ∀ k, AEStronglyMeasurable (fun t => F t k) volume)
    (hFint : Integrable (fun t => ‖F t‖) volume)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : 2 * δ * ((m : ℝ) * κ) ≤ 1 / 2)
    (t0 : ℝ) (x0 : Fin m → ℝ)
    (hsmallF : ∫ s in Set.Icc (t0 - δ) (t0 + δ), ‖F s‖ ≤ 1 / 2) :
    ∃ x : ℝ → Fin m → ℝ, Continuous x ∧
      ∀ t ∈ Set.Icc (t0 - δ) (t0 + δ),
        x t = x0 + ∫ s in t0..t, affineField A F s (x s) := by
  have hmκ : (0:ℝ) ≤ (m : ℝ) * κ := mul_nonneg (Nat.cast_nonneg m) hκ
  have hIccvol : volume (Set.Icc (t0 - δ) (t0 + δ)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have S : CaratheodoryFull.IsSetup t0 δ (‖x0‖ + 1) x0 (affineField A F)
      (fun s => ‖F s‖ + (m : ℝ) * κ * (2 * ‖x0‖ + 1)) := by
    refine ⟨hδ, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun x _ =>
        (affineField_comp_aestronglyMeasurable hAmeas hFmeas continuous_const).restrict
    · exact Eventually.of_forall (fun t => (affineField_continuous_in_y A F t).continuousOn)
    · exact fun s => add_nonneg (norm_nonneg _) (mul_nonneg hmκ (by positivity))
    · exact (hFint.integrableOn).add
        (integrableOn_const (C := (m : ℝ) * κ * (2 * ‖x0‖ + 1)) (hs := hIccvol))
    · refine Eventually.of_forall (fun t x hx => ?_)
      have hxn : ‖x‖ ≤ 2 * ‖x0‖ + 1 := by
        have h1 : ‖x‖ - ‖x0‖ ≤ ‖x - x0‖ := norm_sub_norm_le x x0
        have h2 : dist x x0 ≤ ‖x0‖ + 1 := Metric.mem_closedBall.mp hx
        rw [dist_eq_norm] at h2
        linarith
      refine (affineField_norm_le hκ hA t x).trans ?_
      have h3 := mul_le_mul_of_nonneg_left hxn hmκ
      linarith
    · -- smallness: ∫ (‖F‖ + mκ(2‖x0‖+1)) ≤ ‖x0‖ + 1 over the symmetric interval
      have hIadd : ∫ s in Set.Icc (t0 - δ) (t0 + δ),
            (‖F s‖ + (m : ℝ) * κ * (2 * ‖x0‖ + 1))
          = (∫ s in Set.Icc (t0 - δ) (t0 + δ), ‖F s‖)
            + ∫ _s in Set.Icc (t0 - δ) (t0 + δ), (m : ℝ) * κ * (2 * ‖x0‖ + 1) :=
        integral_add (hFint.integrableOn)
          (integrableOn_const (C := (m : ℝ) * κ * (2 * ‖x0‖ + 1)) (hs := hIccvol))
      have hvol : volume.real (Set.Icc (t0 - δ) (t0 + δ)) = 2 * δ := by
        rw [MeasureTheory.measureReal_def, Real.volume_Icc,
          show t0 + δ - (t0 - δ) = 2 * δ from by ring,
          ENNReal.toReal_ofReal (by linarith)]
      rw [hIadd, MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
      nlinarith [hsmallF,
        mul_le_mul_of_nonneg_right hδκ (show (0:ℝ) ≤ 2 * ‖x0‖ + 1 by positivity),
        norm_nonneg x0]
  obtain ⟨x, hxc, _, hxeq⟩ := S.exists_solution
  exact ⟨x, hxc, hxeq⟩

/-- **A.e. differentiability from the integral equation** (Lebesgue differentiation,
coordinatewise): a curve satisfying `y t = y₀ + ∫₀ᵗ g` on `[0,T]` with `g` interval integrable
has `y' = g` a.e. on `[0,T]`. -/
lemma ae_hasDerivAt_of_integral_eq {T : ℝ} (hT : 0 < T)
    {g y : ℝ → Fin m → ℝ} {y₀ : Fin m → ℝ}
    (hgint : IntervalIntegrable g volume 0 T)
    (hyeq : ∀ t ∈ Set.Icc (0:ℝ) T, y t = y₀ + ∫ s in (0:ℝ)..t, g s) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)), HasDerivAt y (g t) t := by
  set L : Fin m → ((Fin m → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i with hL
  have hLg : ∀ i, IntervalIntegrable (fun s => L i (g s)) volume 0 T := by
    intro i
    rw [intervalIntegrable_iff] at hgint ⊢
    exact (L i).integrable_comp hgint
  have hFTC : ∀ᵐ τ ∂volume, ∀ i : Fin m, τ ∈ Set.uIcc (0:ℝ) T →
      ∀ c ∈ Set.uIcc (0:ℝ) T,
        HasDerivAt (fun u => ∫ s in c..u, L i (g s)) (L i (g τ)) τ :=
    ae_all_iff.mpr fun i => (hLg i).ae_hasDerivAt_integral
  have hne1 : ∀ᵐ τ : ℝ, τ ≠ (0:ℝ) := by
    rw [ae_iff]
    rw [show {τ : ℝ | ¬τ ≠ 0} = {0} from by ext τ; simp]
    exact measure_singleton 0
  have hne2 : ∀ᵐ τ : ℝ, τ ≠ T := by
    rw [ae_iff]
    rw [show {τ : ℝ | ¬τ ≠ T} = {T} from by ext τ; simp]
    exact measure_singleton T
  have huIcc : Set.uIcc (0:ℝ) T = Set.Icc 0 T := Set.uIcc_of_le hT.le
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hFTC, hne1, hne2] with τ hτFTC hτ1 hτ2 hτI
  have hlt1 : 0 < τ := lt_of_le_of_ne hτI.1 (Ne.symm hτ1)
  have hlt2 : τ < T := lt_of_le_of_ne hτI.2 hτ2
  have hcoord : ∀ i : Fin m, HasDerivAt (fun u => L i (y u)) (L i (g τ)) τ := by
    intro i
    have hi := hτFTC i (huIcc ▸ hτI) 0 (huIcc ▸ (Set.left_mem_Icc.mpr hT.le))
    have heq : (fun u => L i (y u)) =ᶠ[𝓝 τ]
        fun u => L i y₀ + ∫ s in (0:ℝ)..u, L i (g s) := by
      filter_upwards [Ioo_mem_nhds hlt1 hlt2] with u hu
      have hu' : u ∈ Set.Icc (0:ℝ) T := Set.Ioo_subset_Icc_self hu
      have hgu : IntervalIntegrable g volume 0 u :=
        hgint.mono_set (by
          rw [Set.uIcc_of_le hu'.1, Set.uIcc_of_le hT.le]
          exact Set.Icc_subset_Icc le_rfl hu'.2)
      rw [hyeq u hu', map_add, ← (L i).intervalIntegral_comp_comm hgu]
    exact (hi.const_add _).congr_of_eventuallyEq heq
  exact hasDerivAt_pi.2 (fun i => hcoord i)

/-- **Global Carathéodory existence on `[0,T]` for the affine system.**  With `A` uniformly
bounded and measurable in `t` and `‖F‖` integrable, the system `y' = F(t) − A(t)y` has a global
solution on `[0,T]`: continuous, satisfying the integral equation (absolute continuity), and
solving the ODE a.e.  Proof: local Carathéodory steps (`CaratheodoryFull`) of uniform length,
glued through the integral equation; the a.e. derivative comes from Lebesgue differentiation. -/
theorem affine_ode_exists_global_ac {T : ℝ} (hT : 0 < T)
    (A : ℝ → Fin m → Fin m → ℝ) (F : ℝ → Fin m → ℝ) (y₀ : Fin m → ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ) (hA : ∀ t k j, |A t k j| ≤ κ)
    (hAmeas : ∀ k j, AEStronglyMeasurable (fun t => A t k j) volume)
    (hFmeas : ∀ k, AEStronglyMeasurable (fun t => F t k) volume)
    (hFint : Integrable (fun t => ‖F t‖) volume) :
    ∃ y : ℝ → Fin m → ℝ, Continuous y ∧ y 0 = y₀ ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, y t = y₀ + ∫ s in (0:ℝ)..t, affineField A F s (y s)) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
        HasDerivAt y (affineField A F t (y t)) t := by
  have hmκ : (0:ℝ) ≤ (m : ℝ) * κ := mul_nonneg (Nat.cast_nonneg m) hκ
  have h4 : (0:ℝ) < 4 * ((m : ℝ) * κ) + 1 := by linarith
  -- a uniform admissible step length δ, from uniform continuity of the primitive of ‖F‖
  have hΦcont : Continuous (fun t => ∫ s in (0:ℝ)..t, ‖F s‖) := hFint.continuous_primitive 0
  have huc : UniformContinuousOn (fun t => ∫ s in (0:ℝ)..t, ‖F s‖)
      (Set.Icc (-1 : ℝ) (T + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hΦcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨dd, hdd, hduc⟩ := huc (1/2) (by norm_num)
  set δ : ℝ := min 1 (min (dd / 3) (1 / (4 * ((m : ℝ) * κ) + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (lt_min (by positivity) (one_div_pos.mpr h4))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδdd : δ ≤ dd / 3 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδκ : 2 * δ * ((m : ℝ) * κ) ≤ 1 / 2 := by
    have hδle : δ ≤ 1 / (4 * ((m : ℝ) * κ) + 1) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hp : δ * (4 * ((m : ℝ) * κ) + 1) ≤ 1 := by
      rw [← le_div_iff₀ h4]
      exact hδle
    nlinarith [hp, hmκ, hδ0.le]
  -- smallness of ∫‖F‖ over every admissible step interval
  have hsmall : ∀ t0 ∈ Set.Icc (0:ℝ) T,
      ∫ s in Set.Icc (t0 - δ) (t0 + δ), ‖F s‖ ≤ 1 / 2 := by
    intro t0 ht0
    have hc : t0 - δ ∈ Set.Icc (-1 : ℝ) (T + 1) :=
      ⟨by linarith [ht0.1], by linarith [ht0.2, hδ0.le]⟩
    have hc' : t0 + δ ∈ Set.Icc (-1 : ℝ) (T + 1) :=
      ⟨by linarith [ht0.1, hδ0.le], by linarith [ht0.2]⟩
    have hΔ := hduc _ hc' _ hc (by
      rw [Real.dist_eq, show t0 + δ - (t0 - δ) = 2 * δ from by ring,
        abs_of_nonneg (by linarith [hδ0.le] : (0:ℝ) ≤ 2 * δ)]
      linarith [hδdd, hdd])
    have heq : ∫ s in Set.Icc (t0 - δ) (t0 + δ), ‖F s‖
        = (∫ s in (0:ℝ)..(t0 + δ), ‖F s‖) - ∫ s in (0:ℝ)..(t0 - δ), ‖F s‖ := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [hδ0.le] : t0 - δ ≤ t0 + δ)]
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (hFint.intervalIntegrable (a := 0) (b := t0 - δ))
        (hFint.intervalIntegrable (a := t0 - δ) (b := t0 + δ))
      linarith [hadj]
    rw [heq]
    rw [Real.dist_eq] at hΔ
    have h1 := le_abs_self ((∫ s in (0:ℝ)..(t0 + δ), ‖F s‖)
      - ∫ s in (0:ℝ)..(t0 - δ), ‖F s‖)
    linarith [hΔ.le, h1]
  -- continuation: a solution of the integral equation on [0, min ((n+1)δ) T] for every n
  have key : ∀ n : ℕ, ∃ y : ℝ → Fin m → ℝ, Continuous y ∧ y 0 = y₀ ∧
      ∀ t ∈ Set.Icc (0:ℝ) (min (((n + 1 : ℕ) : ℝ) * δ) T),
        y t = y₀ + ∫ s in (0:ℝ)..t, affineField A F s (y s) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨x, hxc, hxeq⟩ := affine_ac_local_step hκ hA hAmeas hFmeas hFint hδ0 hδκ 0 y₀
        (hsmall 0 ⟨le_rfl, hT.le⟩)
      refine ⟨x, hxc, ?_, ?_⟩
      · have h0 := hxeq 0 ⟨by linarith [hδ0.le], by linarith [hδ0.le]⟩
        simpa using h0
      · intro t ht
        refine hxeq t ⟨by linarith [ht.1, hδ0.le], ?_⟩
        have h1 : t ≤ ((0 + 1 : ℕ) : ℝ) * δ := le_trans ht.2 (min_le_left _ _)
        have h2 : ((0 + 1 : ℕ) : ℝ) * δ = δ := by norm_num
        linarith
    | succ n ih =>
      obtain ⟨y, hyc, hy0, hyeq⟩ := ih
      set b : ℝ := min (((n + 1 : ℕ) : ℝ) * δ) T with hbdef
      set b' : ℝ := min (((n + 1 + 1 : ℕ) : ℝ) * δ) T with hb'def
      have hb0 : (0:ℝ) ≤ b := le_min (mul_nonneg (by positivity) hδ0.le) hT.le
      have hbT : b ≤ T := min_le_right _ _
      rcases le_total T (((n + 1 : ℕ) : ℝ) * δ) with hTle | hTge
      · -- [0,T] already covered
        have hb : b = T := min_eq_right hTle
        have hstep : ((n + 1 : ℕ) : ℝ) * δ ≤ ((n + 1 + 1 : ℕ) : ℝ) * δ := by
          push_cast; nlinarith [hδ0.le]
        have hb' : b' = T := min_eq_right (hTle.trans hstep)
        refine ⟨y, hyc, hy0, ?_⟩
        rw [hb']
        rw [hb] at hyeq
        exact hyeq
      · -- extend by one Carathéodory step from time b
        have hb : b = ((n + 1 : ℕ) : ℝ) * δ := min_eq_left hTge
        have hb'δ : b' ≤ b + δ := by
          rw [hb'def, hb]
          refine (min_le_left _ _).trans (le_of_eq ?_)
          push_cast; ring
        obtain ⟨β, hβc, hβeq⟩ := affine_ac_local_step hκ hA hAmeas hFmeas hFint hδ0 hδκ b (y b)
          (hsmall b ⟨hb0, hbT⟩)
        have hβb : β b = y b := by
          have h0 := hβeq b ⟨by linarith [hδ0.le], by linarith [hδ0.le]⟩
          simpa using h0
        have hγc : Continuous (fun τ => if τ ≤ b then y τ else β τ) := by
          refine Continuous.if_le hyc hβc continuous_id continuous_const (fun τ hτ => ?_)
          have hτ' : τ = b := hτ
          rw [hτ']
          exact hβb.symm
        have hγy : ∀ s ∈ Set.Icc (0:ℝ) b, (fun τ => if τ ≤ b then y τ else β τ) s = y s :=
          fun s hs => if_pos hs.2
        have hγβ : ∀ s ∈ Set.Icc b b', (fun τ => if τ ≤ b then y τ else β τ) s = β s := by
          intro s hs
          by_cases hsb : s ≤ b
          · have hsbeq : s = b := le_antisymm hsb hs.1
            subst hsbeq
            show (if b ≤ b then y b else β b) = β b
            rw [if_pos le_rfl]
            exact hβb.symm
          · exact if_neg hsb
        refine ⟨fun τ => if τ ≤ b then y τ else β τ, hγc, ?_, ?_⟩
        · show (if (0:ℝ) ≤ b then y 0 else β 0) = y₀
          rw [if_pos hb0, hy0]
        · intro t ht
          rcases le_total t b with htb | hbt
          · -- t ≤ b : the inherited piece
            have htmem : t ∈ Set.Icc (0:ℝ) b := ⟨ht.1, htb⟩
            rw [hγy t htmem, hyeq t htmem]
            congr 1
            refine intervalIntegral.integral_congr (fun s hs => ?_)
            rw [Set.uIcc_of_le ht.1] at hs
            have hsmem : s ∈ Set.Icc (0:ℝ) b := ⟨hs.1, hs.2.trans htb⟩
            rw [hγy s hsmem]
          · -- b ≤ t : the new piece, spliced through the adjacent-interval identity
            have htβ : t ∈ Set.Icc (b - δ) (b + δ) :=
              ⟨by linarith [hδ0.le], ht.2.trans hb'δ⟩
            have htbb' : t ∈ Set.Icc b b' := ⟨hbt, ht.2⟩
            rw [hγβ t htbb', hβeq t htβ, hyeq b ⟨hb0, le_rfl⟩]
            have hI1 : (∫ s in (0:ℝ)..b, affineField A F s (y s))
                = ∫ s in (0:ℝ)..b, affineField A F s
                    ((fun τ => if τ ≤ b then y τ else β τ) s) := by
              refine intervalIntegral.integral_congr (fun s hs => ?_)
              rw [Set.uIcc_of_le hb0] at hs
              rw [hγy s hs]
            have hI2 : (∫ s in b..t, affineField A F s (β s))
                = ∫ s in b..t, affineField A F s
                    ((fun τ => if τ ≤ b then y τ else β τ) s) := by
              refine intervalIntegral.integral_congr (fun s hs => ?_)
              rw [Set.uIcc_of_le hbt] at hs
              rw [hγβ s ⟨hs.1, hs.2.trans ht.2⟩]
            rw [hI1, hI2, add_assoc,
              intervalIntegral.integral_add_adjacent_intervals
                (affineField_comp_intervalIntegrable hκ hA hAmeas hFmeas hFint hγc 0 b)
                (affineField_comp_intervalIntegrable hκ hA hAmeas hFmeas hFint hγc b t)]
  -- enough steps cover [0,T]
  obtain ⟨n, hn⟩ := exists_nat_ge (T / δ)
  obtain ⟨y, hyc, hy0, hyeq⟩ := key n
  have hcover : min (((n + 1 : ℕ) : ℝ) * δ) T = T := by
    refine min_eq_right ?_
    have hTn : T ≤ (n : ℝ) * δ := by
      rw [← div_le_iff₀ hδ0]
      exact hn
    push_cast
    nlinarith [hδ0.le]
  rw [hcover] at hyeq
  refine ⟨y, hyc, hy0, hyeq, ?_⟩
  exact ae_hasDerivAt_of_integral_eq hT
    (affineField_comp_intervalIntegrable hκ hA hAmeas hFmeas hFint hyc 0 T) hyeq

end AffineCaratheodory

/-! ## Theorem 1 in the honest regime: global solvability of the Galerkin system

The Galerkin matrix `A(t)ₖⱼ = B(t)[wⱼ,wₖ]` is measurable in `t` (from v2's `hP_tmeas`, tested on
constant curves) and uniformly bounded (from `hP_bdd`); the forcing entries `(f t, wₖ)` are
measurable with `L¹` norm (from `f ∈ L²(0,T;L²)`).  Extending both by zero outside `[0,T]` gives
global Carathéodory data, and `affine_ode_exists_global_ac` yields the coefficients. -/

set_option maxHeartbeats 1000000 in
/-- **Global solvability of the Galerkin system in the honest Carathéodory regime.**  Under the
hypotheses of v2's `exists_weakSolution` (uniform bound `hP_bdd`, time-measurability `hP_tmeas`,
`L²(0,T;L²)` forcing), the `m`-dimensional Galerkin system has a global solution on `[0,T]`:
continuous coefficients satisfying v2's `GalerkinODE` (the a.e. ODE + initial condition), given
by an explicit integral equation (absolute continuity).  This supersedes v2's sorried
`galerkin_ode_solvable`: no continuity-in-`t` duct-tape, and no false `∃!`. -/
theorem galerkin_ode_solvable_ac
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    {M : ℝ} (hP_bdd : ∀ t, (P t).IsBounded M)
    (hP_tmeas : ∀ (z : L2TH10U d U hU T) (w0 : H1U0 d U hU),
      AEStronglyMeasurable (fun t => parabilinform (P t) (z t) w0)
        (volume.restrict (Set.Icc (0:ℝ) T)))
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U)) (m : ℕ) :
    ∃ dCoeffs : Fin m → ℝ → ℝ,
      (∀ k, Continuous (dCoeffs k)) ∧ GalerkinODE G P T f g dCoeffs := by
  have hMnn : 0 ≤ M := (abs_nonneg _).trans ((hP_bdd 0).2.2 0)
  -- the Galerkin data, extended by zero outside [0,T]
  set A : ℝ → Fin m → Fin m → ℝ := fun t k j =>
    (Set.Icc (0:ℝ) T).indicator
      (fun s => parabilinform (P s) (G.w (j : ℕ)) (G.w (k : ℕ))) t with hAdef
  set F : ℝ → Fin m → ℝ := fun t k =>
    (Set.Icc (0:ℝ) T).indicator
      (fun s => (inner ℝ (f s) (WkpU.toLp (G.w (k : ℕ)).val) : ℝ)) t with hFdef
  -- uniform bound on the matrix entries
  set S : ℝ := ∑ i : Fin m, ‖G.w (i : ℕ)‖ with hSdef
  have hS_le : ∀ j : Fin m, ‖G.w (j : ℕ)‖ ≤ S := fun j =>
    Finset.single_le_sum (f := fun i : Fin m => ‖G.w (i : ℕ)‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ j)
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hκnn : 0 ≤ M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * (S * S) :=
    mul_nonneg (mul_nonneg hMnn (by positivity)) (mul_nonneg hSnn hSnn)
  have hA_bdd : ∀ t k j, |A t k j| ≤ M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * (S * S) := by
    intro t k j
    by_cases htmem : t ∈ Set.Icc (0:ℝ) T
    · rw [hAdef]
      simp only [Set.indicator_of_mem htmem]
      refine (parabilinform_bound (P := P t) M (hP_bdd t)
        (G.w (j : ℕ)) (G.w (k : ℕ))).trans ?_
      have h1 : ‖G.w (j : ℕ)‖ * ‖G.w (k : ℕ)‖ ≤ S * S :=
        mul_le_mul (hS_le j) (hS_le k) (norm_nonneg _) hSnn
      have h2 : 0 ≤ M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) := mul_nonneg hMnn (by positivity)
      calc M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖G.w (j : ℕ)‖ * ‖G.w (k : ℕ)‖
          = M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * (‖G.w (j : ℕ)‖ * ‖G.w (k : ℕ)‖) := by ring
        _ ≤ M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * (S * S) := mul_le_mul_of_nonneg_left h1 h2
    · rw [hAdef]
      simp only [Set.indicator_of_notMem htmem]
      simpa using hκnn
  -- measurability of the extended matrix (from hP_tmeas, tested on constant curves)
  have hA_meas : ∀ k j, AEStronglyMeasurable (fun t => A t k j) volume := by
    intro k j
    have hz := hP_tmeas (Lp.const 2 (volume.restrict (Set.Icc (0:ℝ) T)) (G.w (j : ℕ)))
      (G.w (k : ℕ))
    have hraw : AEStronglyMeasurable
        (fun t => parabilinform (P t) (G.w (j : ℕ)) (G.w (k : ℕ)))
        (volume.restrict (Set.Icc (0:ℝ) T)) := by
      refine hz.congr ?_
      filter_upwards [Lp.coeFn_const 2 (volume.restrict (Set.Icc (0:ℝ) T)) (G.w (j : ℕ))]
        with t ht
      rw [ht]
      rfl
    exact (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr hraw
  -- measurability + integrability of the extended forcing
  have hFraw_meas : ∀ k : Fin m, AEStronglyMeasurable
      (fun t => (inner ℝ (f t) (WkpU.toLp (G.w (k : ℕ)).val) : ℝ))
      (volume.restrict (Set.Icc (0:ℝ) T)) := fun k =>
    (MeasureTheory.Lp.aestronglyMeasurable f).inner aestronglyMeasurable_const
  have hF_meas : ∀ k, AEStronglyMeasurable (fun t => F t k) volume := fun k =>
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr (hFraw_meas k)
  have hFnorm_le : ∀ t, ‖F t‖ ≤ (Set.Icc (0:ℝ) T).indicator (fun s => ‖f s‖) t := by
    intro t
    by_cases htmem : t ∈ Set.Icc (0:ℝ) T
    · rw [Set.indicator_of_mem htmem]
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun k => ?_)
      rw [hFdef]
      simp only [Set.indicator_of_mem htmem]
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [G.orthonormal_L2.1 (k : ℕ), mul_one]
    · rw [Set.indicator_of_notMem htmem]
      refine (pi_norm_le_iff_of_nonneg le_rfl).2 (fun k => ?_)
      rw [hFdef]
      simp only [Set.indicator_of_notMem htmem]
      simp
  have hF_int : Integrable (fun t => ‖F t‖) volume := by
    have hfnorm : Integrable (fun t => ‖f t‖) (volume.restrict (Set.Icc (0:ℝ) T)) :=
      ((MeasureTheory.Lp.memLp f).integrable (by norm_num)).norm
    refine Integrable.mono' ((integrable_indicator_iff measurableSet_Icc).mpr hfnorm)
      ((aestronglyMeasurable_pi_of_components (fun k => hF_meas k)).norm) ?_
    refine Eventually.of_forall (fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hFnorm_le t
  -- solve the affine system globally
  obtain ⟨y, hyc, hy0, _, hyae⟩ := affine_ode_exists_global_ac hT A F
    (fun k => inner ℝ g (WkpU.toLp (G.w (k : ℕ)).val)) hκnn hA_bdd hA_meas hF_meas hF_int
  refine ⟨fun k t => y t k, fun k => (continuous_apply k).comp hyc, fun k => ?_, fun k => ?_⟩
  · -- the a.e. Galerkin ODE
    filter_upwards [hyae, ae_restrict_mem measurableSet_Icc] with t hd ht
    show deriv (fun τ => y τ k) t
        + ∑ j : Fin m, y t j * parabilinform (P t) (G.w (j : ℕ)) (G.w (k : ℕ))
      = inner ℝ (f t) (WkpU.toLp (G.w (k : ℕ)).val)
    rw [(hasDerivAt_pi.1 hd k).deriv]
    show (F t k - ∑ j, A t k j * y t j)
        + ∑ j : Fin m, y t j * parabilinform (P t) (G.w (j : ℕ)) (G.w (k : ℕ))
      = inner ℝ (f t) (WkpU.toLp (G.w (k : ℕ)).val)
    have hFt : F t k = inner ℝ (f t) (WkpU.toLp (G.w (k : ℕ)).val) := by
      rw [hFdef]
      simp only [Set.indicator_of_mem ht]
    have hsum : ∑ j, A t k j * y t j
        = ∑ j : Fin m, y t j * parabilinform (P t) (G.w (j : ℕ)) (G.w (k : ℕ)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hAdef]
      simp only [Set.indicator_of_mem ht]
      rw [mul_comm]
    rw [hFt, hsum]
    ring
  · -- the initial condition
    show y 0 k = inner ℝ g (WkpU.toLp (G.w (k : ℕ)).val)
    rw [hy0]
