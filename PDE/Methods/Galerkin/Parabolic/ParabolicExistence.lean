import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

import PDE.Methods.Galerkin.Parabolic.ParabolicOperator

/-!
Strong Assumptions for the Galerkin ODE

Instead of L^2 and L^∞ assumptions on the coefficients and functions, we strengthen to all continuous in time on a compact set [0.T]

We proceed to prove everything still lies in the Lp spaces since continuous functions on compact sets are bounded and measurable, and the time measure is finite.
-/

open MeasureTheory ENNReal Filter Topology NNReal

variable {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}



/-- **Strong coefficient hypothesis** -/
def CoeffsContinuousInTime (P : ℝ → ParabolicCoeffs d) (T : ℝ) : Prop :=
  (∀ i j x, ContinuousOn (fun t => (P t).a i j x) (Set.Icc (0:ℝ) T)) ∧
  (∀ i x, ContinuousOn (fun t => (P t).b i x) (Set.Icc (0:ℝ) T)) ∧
  (∀ x, ContinuousOn (fun t => (P t).c x) (Set.Icc (0:ℝ) T))

/-!  Bilinear form continuous in time-/

/-- With bounded, time-continuous coefficients, `t ↦ B(t)[u,v]` is continuous on `[0,T]`. -/
lemma parabilinform_continuousOn {M T : ℝ}
    (P : ℝ → ParabolicCoeffs d) (hP_bdd : ∀ t, (P t).IsBounded M)
    (hP_cont : CoeffsContinuousInTime P T) (u v : H1U0 d U hU) :
    ContinuousOn (fun t => parabilinform (P t) u v) (Set.Icc (0:ℝ) T) := by
  obtain ⟨hPa, hPb, hPc⟩ := hP_cont
  have hpu : ∀ i, MemLp (partialU i u) 2 (μU d U) := fun i =>
    WkpU.weakDeriv_memLp u.val 1 (le_refl 1) (fun _ => i)
  have hpv : ∀ j, MemLp (partialU j v) 2 (μU d U) := fun j =>
    WkpU.weakDeriv_memLp v.val 1 (le_refl 1) (fun _ => j)
  have huf : MemLp (fun x => (u : (Fin d → ℝ) → ℝ) x) 2 (μU d U) := WkpU.memLp u.val
  have hvf : MemLp (fun x => (v : (Fin d → ℝ) → ℝ) x) 2 (μU d U) := WkpU.memLp v.val
  unfold parabilinform
  refine continuousOn_of_dominated
    (bound := fun x => M * ((∑ i, ∑ j, |partialU i u x * partialU j v x|)
      + ((∑ i, |partialU i u x * (v : (Fin d → ℝ) → ℝ) x|)
        + |(u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x|)))
    (fun t _ =>
      (parabilinform_integrand_integrable (P := P t) (hP_bdd t) u v).aestronglyMeasurable)
    (fun t _ => ?_) ?_ ?_
  · -- pointwise domination by the envelope
    obtain ⟨hMa, hMb, hMc⟩ := hP_bdd t
    refine Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs]
    have hA_bd : |∑ i, ∑ j, (P t).a i j x * partialU i u x * partialU j v x|
        ≤ M * ∑ i, ∑ j, |partialU i u x * partialU j v x| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun j _ => ?_)
      rw [mul_assoc, abs_mul]
      exact mul_le_mul_of_nonneg_right (hMa i j x) (abs_nonneg _)
    have hB_bd : |∑ i, (P t).b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x|
        ≤ M * ∑ i, |partialU i u x * (v : (Fin d → ℝ) → ℝ) x| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [mul_assoc, abs_mul]
      exact mul_le_mul_of_nonneg_right (hMb i x) (abs_nonneg _)
    have hC_bd : |(P t).c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x|
        ≤ M * |(u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x| := by
      rw [mul_assoc, abs_mul]
      exact mul_le_mul_of_nonneg_right (hMc x) (abs_nonneg _)
    calc |(∑ i, ∑ j, (P t).a i j x * partialU i u x * partialU j v x)
            + (∑ i, (P t).b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x)
            + (P t).c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x|
        ≤ |∑ i, ∑ j, (P t).a i j x * partialU i u x * partialU j v x|
            + |∑ i, (P t).b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x|
            + |(P t).c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ M * (∑ i, ∑ j, |partialU i u x * partialU j v x|)
            + M * (∑ i, |partialU i u x * (v : (Fin d → ℝ) → ℝ) x|)
            + M * |(u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x| :=
          add_le_add (add_le_add hA_bd hB_bd) hC_bd
      _ = M * ((∑ i, ∑ j, |partialU i u x * partialU j v x|)
            + ((∑ i, |partialU i u x * (v : (Fin d → ℝ) → ℝ) x|)
              + |(u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x|)) := by ring
  · -- the envelope is integrable (products of L² functions are L¹)
    refine Integrable.const_mul ?_ M
    refine Integrable.add
      (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
        ((hpu i).integrable_mul (hpv j)).abs)))
      (Integrable.add
        (integrable_finsetSum _ (fun i _ => ((hpu i).integrable_mul hvf).abs))
        ((huf.integrable_mul hvf).abs))
  · -- for each x the integrand is continuous in t on [0,T]
    refine Eventually.of_forall (fun x => ?_)
    refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
    · exact continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ =>
        ((hPa i j x).mul continuousOn_const).mul continuousOn_const))
    · exact continuousOn_finsetSum _ (fun i _ =>
        ((hPb i x).mul continuousOn_const).mul continuousOn_const)
    · exact ((hPc x).mul continuousOn_const).mul continuousOn_const

/-! ## Strong forcing: continuous curves `[0,T] → L²(U)` and their `L²(0,T;L²)` lift -/

section StrongForcing

variable (T : ℝ)

/-- Continuous on compact set implies measurable -/
lemma continuousOn_forcing_memLp (f : ℝ → Lp ℝ 2 (μU d U))
    (hf : ContinuousOn f (Set.Icc (0:ℝ) T)) :
    MemLp f 2 (volume.restrict (Set.Icc (0:ℝ) T)) := by
  haveI : SecondCountableTopologyEither ℝ (Lp ℝ 2 (μU d U)) := ⟨Or.inl inferInstance⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound (hf.aestronglyMeasurable measurableSet_Icc) C ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall (fun t ht => hC t ht)

/-- The continuous forcing packaged as an element of `L²(0,T;L²(U))`, so that every v2 lemma
(stated for `L2TL2` data) applies to it verbatim. -/
noncomputable def forcingLift (f : ℝ → Lp ℝ 2 (μU d U))
    (hf : ContinuousOn f (Set.Icc (0:ℝ) T)) : L2TL2 d U T :=
  (continuousOn_forcing_memLp T f hf).toLp f

/-- The lift's representative agrees a.e. with the continuous forcing. -/
lemma forcingLift_coeFn (f : ℝ → Lp ℝ 2 (μU d U))
    (hf : ContinuousOn f (Set.Icc (0:ℝ) T)) :
    (forcingLift T f hf : ℝ → Lp ℝ 2 (μU d U))
      =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)] f :=
  MemLp.coeFn_toLp _

/-- Bochner norm of the lift, in terms of the continuous data. -/
lemma forcingLift_norm_sq (f : ℝ → Lp ℝ 2 (μU d U))
    (hf : ContinuousOn f (Set.Icc (0:ℝ) T)) :
    ‖forcingLift T f hf‖ ^ 2 = ∫ t in Set.Icc (0:ℝ) T, ‖f t‖ ^ 2 := by
  rw [L2TL2_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [forcingLift_coeFn T f hf] with t ht
  rw [ht]

/-- Continuity on `[0,T]` of the Galerkin forcing entries `t ↦ (f t, w)_{L²}` — v2's `hFcont`
duct-tape hypothesis, now a theorem for strong data. -/
lemma forcing_inner_continuousOn (f : ℝ → Lp ℝ 2 (μU d U))
    (hf : ContinuousOn f (Set.Icc (0:ℝ) T)) (w : Lp ℝ 2 (μU d U)) :
    ContinuousOn (fun t => (inner ℝ (f t) w : ℝ)) (Set.Icc (0:ℝ) T) :=
  hf.inner continuousOn_const

end StrongForcing

/-! ## The strong Galerkin ODE and the bridge to v2 -/

/-- strong Galerkin ODE -/
def GalerkinODEStrong (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ)
    (f : ℝ → Lp ℝ 2 (μU d U)) (g : Lp ℝ 2 (μU d U))
    {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ) : Prop :=
  (∀ k : Fin m, ∀ t ∈ Set.Icc (0:ℝ) T,
      deriv (dCoeffs k) t
        + ∑ j : Fin m, dCoeffs j t * parabilinform (P t) (G.w j.val) (G.w k.val)
      = inner ℝ (f t) (WkpU.toLp (G.w k.val).val))
  ∧ (∀ k : Fin m, dCoeffs k 0 = inner ℝ g (WkpU.toLp (G.w k.val).val))

/-- **Bridge to v2.** -/
lemma GalerkinODEStrong.galerkinODE
    {G : GalerkinBasis d U hU} {P : ℝ → ParabolicCoeffs d} {T : ℝ}
    {f : ℝ → Lp ℝ 2 (μU d U)} {g : Lp ℝ 2 (μU d U)} {m : ℕ} {dCoeffs : Fin m → ℝ → ℝ}
    (h : GalerkinODEStrong G P T f g dCoeffs)
    (hf : ContinuousOn f (Set.Icc (0:ℝ) T)) :
    GalerkinODE G P T (forcingLift T f hf) g dCoeffs := by
  refine ⟨fun k => ?_, h.2⟩
  filter_upwards [forcingLift_coeFn T f hf, ae_restrict_mem measurableSet_Icc] with t hft ht
  rw [hft]
  exact h.1 k t ht


theorem galerkin_energy_estimate_strong
    {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ)
    (hP_bdd : ∀ t, (P t).IsBounded M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : ℝ → Lp ℝ 2 (μU d U)) (hf : ContinuousOn f (Set.Icc (0:ℝ) T))
        (g : Lp ℝ 2 (μU d U)) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ),
        (∀ k, ContDiff ℝ 1 (dCoeffs k)) →
        GalerkinODEStrong G P T f g dCoeffs →
        (∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
            ‖WkpU.toLp (uapprox G dCoeffs t).val‖^2
              ≤ C * ((∫ s in Set.Icc (0:ℝ) T, ‖f s‖^2) + ‖g‖^2))
        ∧
        ((∫ t in Set.Icc (0:ℝ) T, ‖uapprox G dCoeffs t‖^2)
            ≤ C * ((∫ s in Set.Icc (0:ℝ) T, ‖f s‖^2) + ‖g‖^2))
        ∧
        ((∫ t in Set.Icc (0:ℝ) T,
            (hinvNormOfH1 (u'approx G dCoeffs t))^2)
            ≤ C * ((∫ s in Set.Icc (0:ℝ) T, ‖f s‖^2) + ‖g‖^2)) := by
  obtain ⟨C, hCnn, hC⟩ := galerkin_energy_estimate hθ hMpos G P T hT hP_para hP_bdd
  refine ⟨C, hCnn, ?_⟩
  intro f hf g m dCoeffs hdiff hODE
  rw [← forcingLift_norm_sq T f hf]
  exact hC (forcingLift T f hf) g dCoeffs hdiff (hODE.galerkinODE hf)

/-!

Mathlib's `IsPicardLindelof` is local (the solution must stay in the ball on which the
vector-field conditions are stated), so the compact interval `[0,T]` is covered by
**continuation**: a Grönwall a-priori bound `R` on any solution makes the admissible step length
uniform, and finitely many local Picard–Lindelöf steps glued end to end reach `T`.  Everything is
done for a general affine field `v t y = F t − (A t)·y` with `A` uniformly bounded and `A, F`
continuous — exactly the Galerkin system's shape. -/

section AffineODE

variable {m : ℕ}

/-- The affine (Galerkin-type) vector field `v t y = F t − (A t)·y`. -/
def affineField (A : ℝ → Fin m → Fin m → ℝ) (F : ℝ → Fin m → ℝ) :
    ℝ → (Fin m → ℝ) → (Fin m → ℝ) :=
  fun t y k => F t k - ∑ j, A t k j * y j

/-- The affine field is (uniformly in `t`) Lipschitz in `y`, with constant `m·κ`. -/
lemma affineField_dist_le {A : ℝ → Fin m → Fin m → ℝ} {F : ℝ → Fin m → ℝ} {κ : ℝ}
    (hκ : 0 ≤ κ) (hA : ∀ t k j, |A t k j| ≤ κ) (t : ℝ) (y z : Fin m → ℝ) :
    dist (affineField A F t y) (affineField A F t z) ≤ (m : ℝ) * κ * dist y z := by
  rw [dist_eq_norm, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hκ) (norm_nonneg _))).2 (fun k => ?_)
  have hk : (affineField A F t y - affineField A F t z) k
      = ∑ j, A t k j * (z j - y j) := by
    simp only [affineField, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hk, Real.norm_eq_abs]
  calc |∑ j, A t k j * (z j - y j)|
      ≤ ∑ j, |A t k j * (z j - y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, κ * ‖y - z‖ := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [abs_mul, abs_sub_comm]
        refine mul_le_mul (hA t k j) ?_ (abs_nonneg _) hκ
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm (y - z) j
    _ = (m : ℝ) * κ * ‖y - z‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Bundled `LipschitzWith` form of `affineField_dist_le`. -/
lemma affineField_lipschitzWith {A : ℝ → Fin m → Fin m → ℝ} {F : ℝ → Fin m → ℝ} {κ : ℝ}
    (hκ : 0 ≤ κ) (hA : ∀ t k j, |A t k j| ≤ κ) (t : ℝ) :
    LipschitzWith (Real.toNNReal ((m : ℝ) * κ)) (affineField A F t) := by
  refine LipschitzWith.of_dist_le_mul (fun y z => ?_)
  rw [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg m) hκ)]
  exact affineField_dist_le hκ hA t y z

/-- Affine growth of the field: `‖v t y‖ ≤ ‖F t‖ + m·κ·‖y‖`. -/
lemma affineField_norm_le {A : ℝ → Fin m → Fin m → ℝ} {F : ℝ → Fin m → ℝ} {κ : ℝ}
    (hκ : 0 ≤ κ) (hA : ∀ t k j, |A t k j| ≤ κ) (t : ℝ) (y : Fin m → ℝ) :
    ‖affineField A F t y‖ ≤ ‖F t‖ + (m : ℝ) * κ * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hκ) (norm_nonneg _)))).2 (fun k => ?_)
  have h1 : ‖affineField A F t y k‖ ≤ ‖F t k‖ + ‖∑ j, A t k j * y j‖ := norm_sub_le _ _
  refine h1.trans (add_le_add (norm_le_pi_norm (F t) k) ?_)
  rw [Real.norm_eq_abs]
  calc |∑ j, A t k j * y j|
      ≤ ∑ j, |A t k j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, κ * ‖y‖ := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [abs_mul]
        refine mul_le_mul (hA t k j) ?_ (abs_nonneg _) hκ
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm y j
    _ = (m : ℝ) * κ * ‖y‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The field composed with a continuous curve is continuous in `t`. -/
lemma affineField_continuous_comp {A : ℝ → Fin m → Fin m → ℝ} {F : ℝ → Fin m → ℝ}
    (hAc : ∀ k j, Continuous (fun t => A t k j)) (hFc : ∀ k, Continuous (fun t => F t k))
    {γ : ℝ → Fin m → ℝ} (hγ : Continuous γ) :
    Continuous (fun t => affineField A F t (γ t)) := by
  refine continuous_pi (fun k => ?_)
  exact (hFc k).sub (continuous_finsetSum _ (fun j _ =>
    (hAc k j).mul ((continuous_apply j).comp hγ)))

/-- For `t` in the left-open part of `[a,c]`, `[a,c]` is a right-neighbourhood of `t`. -/
private lemma Icc_mem_nhdsGE_of_mem' {a c t : ℝ} (h : t ∈ Set.Ico a c) :
    Set.Icc a c ∈ 𝓝[≥] t :=
  Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici t) (Iic_mem_nhds h.2))
    (fun _ hx => ⟨h.1.trans hx.1, hx.2⟩)

/-- For `t < u`, `[0,u]` is a neighbourhood of `t` within any `[0,s']`. -/
private lemma Icc_left_mem_nhdsWithin {s' t u : ℝ} (h : t < u) :
    Set.Icc (0:ℝ) u ∈ 𝓝[Set.Icc (0:ℝ) s'] t :=
  Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Icc (0:ℝ) s') (Iio_mem_nhds h))
    (fun _ hx => ⟨hx.1.1, le_of_lt hx.2⟩)

/-- For `a < t`, `[a,s']` is a neighbourhood of `t` within `[0,s']`. -/
private lemma Icc_right_mem_nhdsWithin {a s' t : ℝ} (h : a < t) :
    Set.Icc a s' ∈ 𝓝[Set.Icc (0:ℝ) s'] t :=
  Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Icc (0:ℝ) s') (Ioi_mem_nhds h))
    (fun _ hx => ⟨le_of_lt hx.2, hx.1.2⟩)

/-- **Local Picard–Lindelöf step.**  From any start time `s` and start value of norm `≤ R`, the
affine system has a solution on `[s,s']` as long as the step length does not exceed
`1 / max 1 (Cf + m·κ·(R+1))`.  This is Mathlib's `IsPicardLindelof` applied on the ball of radius
`1` around the start value. -/
lemma affineField_local_step {A : ℝ → Fin m → Fin m → ℝ} {F : ℝ → Fin m → ℝ} {κ Cf R : ℝ}
    (hκ : 0 ≤ κ) (hA : ∀ t k j, |A t k j| ≤ κ)
    (hAc : ∀ k j, Continuous (fun t => A t k j)) (hFc : ∀ k, Continuous (fun t => F t k))
    (hCf : ∀ t, ‖F t‖ ≤ Cf)
    {s s' : ℝ} (hss' : s ≤ s')
    (hstep : s' - s ≤ 1 / max 1 (Cf + (m : ℝ) * κ * (R + 1)))
    (x : Fin m → ℝ) (hx : ‖x‖ ≤ R) :
    ∃ α : ℝ → Fin m → ℝ, α s = x ∧
      ∀ t ∈ Set.Icc s s', HasDerivWithinAt α (affineField A F t (α t)) (Set.Icc s s') t := by
  set L : ℝ := max 1 (Cf + (m : ℝ) * κ * (R + 1)) with hLdef
  have hL1 : (1:ℝ) ≤ L := le_max_left _ _
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hpl : IsPicardLindelof (affineField A F) (tmin := s) (tmax := s')
      ⟨s, le_rfl, hss'⟩ x 1 0 (Real.toNNReal L) (Real.toNNReal ((m : ℝ) * κ)) := by
    refine ⟨fun t _ => (affineField_lipschitzWith hκ hA t).lipschitzOnWith,
      fun z _ => (affineField_continuous_comp hAc hFc continuous_const).continuousOn,
      fun t _ z hz => ?_, ?_⟩
    · -- norm bound on the ball of radius 1 around x
      rw [Real.coe_toNNReal _ hL0.le]
      have hzn : ‖z‖ ≤ R + 1 := by
        have h1 : ‖z‖ - ‖x‖ ≤ ‖z - x‖ := norm_sub_norm_le z x
        have h2 : dist z x ≤ 1 := by simpa using Metric.mem_closedBall.mp hz
        rw [dist_eq_norm] at h2
        linarith
      refine (affineField_norm_le hκ hA t z).trans (le_trans ?_ (le_max_right 1 _))
      exact add_le_add (hCf t)
        (mul_le_mul_of_nonneg_left hzn (mul_nonneg (Nat.cast_nonneg m) hκ))
    · -- the step-length constraint `L·(s'−s) ≤ a − r = 1`
      show (Real.toNNReal L : ℝ) * max (s' - s) (s - s) ≤ ((1:ℝ≥0) : ℝ) - ((0:ℝ≥0) : ℝ)
      rw [Real.coe_toNNReal _ hL0.le, sub_self, max_eq_left (sub_nonneg.2 hss')]
      have hle : L * (s' - s) ≤ 1 := by
        calc L * (s' - s) ≤ L * (1 / L) := mul_le_mul_of_nonneg_left hstep hL0.le
          _ = 1 := by field_simp
      push_cast
      linarith
  obtain ⟨α, hα0, hαd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, hαd⟩

/-- **Grönwall a-priori bound** for solutions of the affine system on `[0,b]`. -/
lemma affineField_apriori {A : ℝ → Fin m → Fin m → ℝ} {F : ℝ → Fin m → ℝ} {κ Cf : ℝ}
    (hκ : 0 ≤ κ) (hA : ∀ t k j, |A t k j| ≤ κ) (hCf : ∀ t, ‖F t‖ ≤ Cf)
    {b : ℝ} {α : ℝ → Fin m → ℝ}
    (hαc : ContinuousOn α (Set.Icc 0 b))
    (hαd : ∀ t ∈ Set.Icc (0:ℝ) b,
      HasDerivWithinAt α (affineField A F t (α t)) (Set.Icc 0 b) t) :
    ∀ t ∈ Set.Icc (0:ℝ) b, ‖α t‖ ≤ gronwallBound ‖α 0‖ ((m : ℝ) * κ) Cf t := by
  intro t ht
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (f' := fun s => affineField A F s (α s)) (K := (m : ℝ) * κ) (ε := Cf) hαc
    (fun s hs => (hαd s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem' hs))
    le_rfl
    (fun s _ => by
      have h1 := affineField_norm_le (F := F) hκ hA s (α s)
      have h2 := hCf s
      linarith)
  simpa using h t ht

/-- ODE only on ball, need to extend globally on T-/
theorem affine_ode_exists_global {T : ℝ} (hT : 0 < T)
    (A : ℝ → Fin m → Fin m → ℝ) (F : ℝ → Fin m → ℝ) (y₀ : Fin m → ℝ) {κ Cf : ℝ}
    (hκ : 0 ≤ κ) (hA : ∀ t k j, |A t k j| ≤ κ)
    (hAc : ∀ k j, Continuous (fun t => A t k j)) (hFc : ∀ k, Continuous (fun t => F t k))
    (hCf : ∀ t, ‖F t‖ ≤ Cf) :
    ∃ y : ℝ → Fin m → ℝ, ContDiff ℝ 1 y ∧ y 0 = y₀ ∧
      ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt y (affineField A F t (y t)) t := by
  have hCf0 : 0 ≤ Cf := (norm_nonneg (F 0)).trans (hCf 0)
  have hmκ : 0 ≤ (m : ℝ) * κ := mul_nonneg (Nat.cast_nonneg m) hκ
  -- Grönwall a-priori radius and the induced uniform step length
  set R : ℝ := gronwallBound ‖y₀‖ ((m : ℝ) * κ) Cf T with hRdef
  have hR0 : ‖y₀‖ ≤ R := by
    have h := gronwallBound_mono (norm_nonneg y₀) hCf0 hmκ hT.le
    rw [gronwallBound_x0] at h
    rw [← hRdef] at h
    exact h
  set L : ℝ := max 1 (Cf + (m : ℝ) * κ * (R + 1)) with hLdef
  have hL1 : (1:ℝ) ≤ L := le_max_left _ _
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL1
  set δ : ℝ := 1 / L with hδdef
  have hδ0 : 0 < δ := by positivity
  -- any partial solution stays in the ball of radius R
  have hapriori : ∀ b : ℝ, 0 ≤ b → b ≤ T → ∀ α : ℝ → Fin m → ℝ, α 0 = y₀ →
      (∀ t ∈ Set.Icc (0:ℝ) b,
        HasDerivWithinAt α (affineField A F t (α t)) (Set.Icc 0 b) t) →
      ∀ t ∈ Set.Icc (0:ℝ) b, ‖α t‖ ≤ R := by
    intro b _ hbT α hα0 hαd t ht
    have hαc : ContinuousOn α (Set.Icc 0 b) := fun s hs => (hαd s hs).continuousWithinAt
    refine (affineField_apriori hκ hA hCf hαc hαd t ht).trans ?_
    rw [hα0, hRdef]
    exact gronwallBound_mono (norm_nonneg _) hCf0 hmκ (ht.2.trans hbT)
  -- continuation: a solution exists on [0, min ((n+1)δ) T] for every n
  have key : ∀ n : ℕ, ∃ α : ℝ → Fin m → ℝ, α 0 = y₀ ∧
      ∀ t ∈ Set.Icc (0:ℝ) (min (((n + 1 : ℕ) : ℝ) * δ) T),
        HasDerivWithinAt α (affineField A F t (α t))
          (Set.Icc (0:ℝ) (min (((n + 1 : ℕ) : ℝ) * δ) T)) t := by
    intro n
    induction n with
    | zero =>
      refine affineField_local_step hκ hA hAc hFc hCf
        (le_min (mul_nonneg (by positivity) hδ0.le) hT.le) ?_ y₀ hR0
      rw [← hLdef, ← hδdef, sub_zero]
      refine (min_le_left _ _).trans (le_of_eq ?_)
      norm_num
    | succ n ih =>
      obtain ⟨α, hα0, hαd⟩ := ih
      set b : ℝ := min (((n + 1 : ℕ) : ℝ) * δ) T with hbdef
      set b' : ℝ := min (((n + 1 + 1 : ℕ) : ℝ) * δ) T with hb'def
      have hb0 : (0:ℝ) ≤ b := le_min (mul_nonneg (by positivity) hδ0.le) hT.le
      rcases le_total T (((n + 1 : ℕ) : ℝ) * δ) with hTle | hTge
      · -- [0,T] is already covered
        have hb : b = T := min_eq_right hTle
        have hstep : ((n + 1 : ℕ) : ℝ) * δ ≤ ((n + 1 + 1 : ℕ) : ℝ) * δ := by
          push_cast; nlinarith [hδ0.le]
        have hb' : b' = T := min_eq_right (hTle.trans hstep)
        refine ⟨α, hα0, ?_⟩
        rw [hb']
        rw [hb] at hαd
        exact hαd
      · -- extend by one Picard–Lindelöf step from time b
        have hb : b = ((n + 1 : ℕ) : ℝ) * δ := min_eq_left hTge
        have hbb' : b ≤ b' := by
          refine le_min ?_ (hb ▸ hTge)
          rw [hb]; push_cast; nlinarith [hδ0.le]
        have hb'b : b' - b ≤ δ := by
          have h1 : b' ≤ b + δ := by
            rw [hb'def, hb]
            refine (min_le_left _ _).trans (le_of_eq ?_)
            push_cast; ring
          linarith
        have hαb : ‖α b‖ ≤ R :=
          hapriori b hb0 (min_le_right _ _) α hα0 hαd b ⟨hb0, le_rfl⟩
        obtain ⟨β, hβ0, hβd⟩ := affineField_local_step hκ hA hAc hFc hCf hbb'
          (by rw [← hLdef, ← hδdef]; exact hb'b) (α b) hαb
        -- glue the two solutions at time b
        refine ⟨fun τ => if τ ≤ b then α τ else β τ, by simp only [if_pos hb0]; exact hα0, ?_⟩
        have hγα : ∀ x ∈ Set.Icc (0:ℝ) b,
            (fun τ => if τ ≤ b then α τ else β τ) x = α x := fun x hx => if_pos hx.2
        have hγβ : ∀ x ∈ Set.Icc b b',
            (fun τ => if τ ≤ b then α τ else β τ) x = β x := by
          intro x hx
          by_cases hxb : x ≤ b
          · have hxeq : x = b := le_antisymm hxb hx.1
            subst hxeq
            show (if b ≤ b then α b else β b) = β b
            rw [if_pos hxb, hβ0]
          · simp only [if_neg hxb]
        intro t ht
        rcases lt_trichotomy t b with htb | htb | htb
        · -- t < b : the left piece governs
          have htmem : t ∈ Set.Icc (0:ℝ) b := ⟨ht.1, htb.le⟩
          have h1 := (hαd t htmem).congr hγα (hγα t htmem)
          rw [← hγα t htmem] at h1
          exact h1.mono_of_mem_nhdsWithin (Icc_left_mem_nhdsWithin htb)
        · -- t = b : union of the two one-sided solutions
          have hmem1 : b ∈ Set.Icc (0:ℝ) b := ⟨hb0, le_rfl⟩
          have hmem2 : b ∈ Set.Icc b b' := ⟨le_rfl, hbb'⟩
          have h1 := (hαd b hmem1).congr hγα (hγα b hmem1)
          have h2 := (hβd b hmem2).congr hγβ (hγβ b hmem2)
          rw [← hγα b hmem1] at h1
          rw [hβ0, ← hγα b hmem1] at h2
          have h3 := h1.union h2
          rw [Set.Icc_union_Icc_eq_Icc hb0 hbb'] at h3
          rw [htb]
          exact h3
        · -- b < t : the right piece governs
          have htmem : t ∈ Set.Icc b b' := ⟨htb.le, ht.2⟩
          have h1 := (hβd t htmem).congr hγβ (hγβ t htmem)
          rw [← hγβ t htmem] at h1
          exact h1.mono_of_mem_nhdsWithin (Icc_right_mem_nhdsWithin htb)
  -- enough steps cover [0,T]
  obtain ⟨n, hn⟩ := exists_nat_ge (T / δ)
  obtain ⟨α, hα0, hαd⟩ := key n
  have hcover : min (((n + 1 : ℕ) : ℝ) * δ) T = T := by
    refine min_eq_right ?_
    have hTn : T ≤ (n : ℝ) * δ := by
      rw [← div_le_iff₀ hδ0]
      exact hn
    push_cast
    nlinarith [hδ0.le]
  rw [hcover] at hαd
  have hαc : ContinuousOn α (Set.Icc 0 T) := fun s hs => (hαd s hs).continuousWithinAt
  -- upgrade to a globally C¹ solution via the integral (Picard) form
  have hπc : Continuous (fun τ : ℝ => max 0 (min τ T)) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hπmem : ∀ τ : ℝ, max 0 (min τ T) ∈ Set.Icc (0:ℝ) T :=
    fun τ => ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hπid : ∀ t ∈ Set.Icc (0:ℝ) T, max 0 (min t T) = t :=
    fun t ht => by rw [min_eq_left ht.2, max_eq_right ht.1]
  have hαπc : Continuous (fun τ => α (max 0 (min τ T))) := by
    have h := hαc.comp_continuous hπc hπmem
    simpa [Function.comp_def] using h
  set w : ℝ → Fin m → ℝ := fun τ => affineField A F τ (α (max 0 (min τ T))) with hwdef
  have hwc : Continuous w := affineField_continuous_comp hAc hFc hαπc
  have hwα : ∀ t ∈ Set.Icc (0:ℝ) T, w t = affineField A F t (α t) := fun t ht => by
    simp only [hwdef]
    rw [hπid t ht]
  set y : ℝ → Fin m → ℝ := fun t => y₀ + ∫ τ in (0:ℝ)..t, w τ with hydef
  have hyd : ∀ t, HasDerivAt y (w t) t := by
    intro t
    have h := intervalIntegral.integral_hasDerivAt_right
      (hwc.intervalIntegrable 0 t)
      ⟨Set.univ, Filter.univ_mem, hwc.aestronglyMeasurable.restrict⟩
      hwc.continuousAt
    exact h.const_add y₀
  have hy0 : y 0 = y₀ := by simp [hydef]
  have hyα : ∀ t ∈ Set.Icc (0:ℝ) T, y t = α t := by
    have hzero := constant_of_has_deriv_right_zero
      (f := fun τ => y τ - α τ) (a := 0) (b := T)
      (((continuous_iff_continuousAt.2 (fun t => (hyd t).continuousAt)).continuousOn).sub hαc)
      (fun s hs => by
        have h1 : HasDerivWithinAt y (w s) (Set.Ici s) s := (hyd s).hasDerivWithinAt
        have h2 : HasDerivWithinAt α (affineField A F s (α s)) (Set.Ici s) s :=
          (hαd s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
            (Icc_mem_nhdsGE_of_mem' hs)
        have h3 := h1.sub h2
        rw [hwα s (Set.Ico_subset_Icc_self hs), sub_self] at h3
        exact h3)
    intro t ht
    have h := hzero t ht
    rw [hy0, hα0, sub_self] at h
    exact sub_eq_zero.mp h
  refine ⟨y, ?_, hy0, ?_⟩
  · refine contDiff_one_iff_deriv.2 ⟨fun t => (hyd t).differentiableAt, ?_⟩
    have hde : deriv y = w := funext (fun t => (hyd t).deriv)
    rw [hde]
    exact hwc
  · intro t ht
    have h := hyd t
    rw [hwα t ht, ← hyα t ht] at h
    exact h

/-- **Uniqueness on `[0,T]`** for the affine system (Grönwall, via Mathlib's
`ODE_solution_unique`). -/
theorem affine_ode_unique {T : ℝ}
    (A : ℝ → Fin m → Fin m → ℝ) (F : ℝ → Fin m → ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ) (hA : ∀ t k j, |A t k j| ≤ κ)
    {y z : ℝ → Fin m → ℝ}
    (hyc : ContinuousOn y (Set.Icc 0 T)) (hzc : ContinuousOn z (Set.Icc 0 T))
    (hyd : ∀ t ∈ Set.Icc (0:ℝ) T,
      HasDerivWithinAt y (affineField A F t (y t)) (Set.Icc 0 T) t)
    (hzd : ∀ t ∈ Set.Icc (0:ℝ) T,
      HasDerivWithinAt z (affineField A F t (z t)) (Set.Icc 0 T) t)
    (h0 : y 0 = z 0) :
    Set.EqOn y z (Set.Icc (0:ℝ) T) := by
  refine ODE_solution_unique (fun t => affineField_lipschitzWith (F := F) hκ hA t)
    hyc (fun t ht => ?_) hzc (fun t ht => ?_) h0
  · exact (hyd t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem' ht)
  · exact (hzd t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem' ht)

end AffineODE

/-! ## Theorem 1, strong form: global solvability of the Galerkin system -/

/-- **Global solvability of the Galerkin ODE under the strong assumptions.**   -/
theorem galerkin_ode_solvable_strong
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    {M : ℝ} (hP_bdd : ∀ t, (P t).IsBounded M)
    (hP_cont : CoeffsContinuousInTime P T)
    (f : ℝ → Lp ℝ 2 (μU d U)) (hf : ContinuousOn f (Set.Icc (0:ℝ) T))
    (g : Lp ℝ 2 (μU d U)) (m : ℕ) :
    ∃ dCoeffs : Fin m → ℝ → ℝ,
      (∀ k, ContDiff ℝ 1 (dCoeffs k)) ∧
      GalerkinODEStrong G P T f g dCoeffs ∧
      (∀ dCoeffs' : Fin m → ℝ → ℝ, (∀ k, ContDiff ℝ 1 (dCoeffs' k)) →
        GalerkinODEStrong G P T f g dCoeffs' →
        ∀ k : Fin m, Set.EqOn (dCoeffs' k) (dCoeffs k) (Set.Icc (0:ℝ) T)) := by
  have hMnn : 0 ≤ M := (abs_nonneg _).trans ((hP_bdd 0).2.2 0)
  -- the time projection onto [0,T], used to extend the data continuously to all of ℝ
  have hπc : Continuous (fun τ : ℝ => max 0 (min τ T)) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hπmem : ∀ τ : ℝ, max 0 (min τ T) ∈ Set.Icc (0:ℝ) T :=
    fun τ => ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hπid : ∀ t ∈ Set.Icc (0:ℝ) T, max 0 (min t T) = t :=
    fun t ht => by rw [min_eq_left ht.2, max_eq_right ht.1]
  -- the (projected) coefficient matrix and forcing vector of the Galerkin system
  set A : ℝ → Fin m → Fin m → ℝ := fun t k j =>
    parabilinform (P (max 0 (min t T))) (G.w (j : ℕ)) (G.w (k : ℕ)) with hAdef
  set F : ℝ → Fin m → ℝ := fun t k =>
    inner ℝ (f (max 0 (min t T))) (WkpU.toLp (G.w (k : ℕ)).val) with hFdef
  -- uniform bound on the matrix entries: κ = M(d²+d+1)·S², S = Σ‖wᵢ‖
  set S : ℝ := ∑ i : Fin m, ‖G.w (i : ℕ)‖ with hSdef
  have hS_le : ∀ j : Fin m, ‖G.w (j : ℕ)‖ ≤ S := fun j =>
    Finset.single_le_sum (f := fun i : Fin m => ‖G.w (i : ℕ)‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ j)
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hκnn : 0 ≤ M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * (S * S) :=
    mul_nonneg (mul_nonneg hMnn (by positivity)) (mul_nonneg hSnn hSnn)
  have hA_bdd : ∀ t k j, |A t k j| ≤ M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * (S * S) := by
    intro t k j
    simp only [hAdef]
    refine (parabilinform_bound (P := P (max 0 (min t T))) M (hP_bdd _)
      (G.w (j : ℕ)) (G.w (k : ℕ))).trans ?_
    have h1 : ‖G.w (j : ℕ)‖ * ‖G.w (k : ℕ)‖ ≤ S * S :=
      mul_le_mul (hS_le j) (hS_le k) (norm_nonneg _) hSnn
    have h2 : 0 ≤ M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) := mul_nonneg hMnn (by positivity)
    calc M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖G.w (j : ℕ)‖ * ‖G.w (k : ℕ)‖
        = M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * (‖G.w (j : ℕ)‖ * ‖G.w (k : ℕ)‖) := by ring
      _ ≤ M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * (S * S) := mul_le_mul_of_nonneg_left h1 h2
  -- continuity of the matrix and forcing (the discharged duct-tape hypotheses)
  have hAc : ∀ k j, Continuous (fun t => A t k j) := by
    intro k j
    have h := (parabilinform_continuousOn P hP_bdd hP_cont
      (G.w (j : ℕ)) (G.w (k : ℕ))).comp_continuous hπc hπmem
    simpa [hAdef, Function.comp_def] using h
  have hFc : ∀ k, Continuous (fun t => F t k) := by
    intro k
    have h := (forcing_inner_continuousOn T f hf
      (WkpU.toLp (G.w (k : ℕ)).val)).comp_continuous hπc hπmem
    simpa [hFdef, Function.comp_def] using h
  -- uniform bound on the forcing (continuity on the compact interval)
  obtain ⟨Cf, hCfIcc⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hCfnn : 0 ≤ Cf := (norm_nonneg _).trans (hCfIcc 0 ⟨le_rfl, hT.le⟩)
  have hCf : ∀ t, ‖F t‖ ≤ Cf := by
    intro t
    refine (pi_norm_le_iff_of_nonneg hCfnn).2 (fun k => ?_)
    simp only [hFdef]
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have h1 : ‖WkpU.toLp (G.w (k : ℕ)).val‖ = 1 := G.orthonormal_L2.1 (k : ℕ)
    rw [h1, mul_one]
    exact hCfIcc _ (hπmem t)
  -- solve the affine system globally
  set y₀ : Fin m → ℝ := fun k => inner ℝ g (WkpU.toLp (G.w (k : ℕ)).val) with hy₀def
  obtain ⟨y, hyC1, hy0, hyODE⟩ :=
    affine_ode_exists_global hT A F y₀ hκnn hA_bdd hAc hFc hCf
  refine ⟨fun k t => y t k, fun k => contDiff_pi.1 hyC1 k, ⟨?_, ?_⟩, ?_⟩
  · -- the strong Galerkin ODE holds pointwise on [0,T]
    intro k t ht
    show deriv (fun τ => y τ k) t
        + ∑ j : Fin m, y t j * parabilinform (P t) (G.w (j : ℕ)) (G.w (k : ℕ))
      = inner ℝ (f t) (WkpU.toLp (G.w (k : ℕ)).val)
    have hd := (hasDerivAt_pi.1 (hyODE t ht) k).deriv
    rw [hd]
    show (F t k - ∑ j, A t k j * y t j)
        + ∑ j : Fin m, y t j * parabilinform (P t) (G.w (j : ℕ)) (G.w (k : ℕ))
      = inner ℝ (f t) (WkpU.toLp (G.w (k : ℕ)).val)
    have hFt : F t k = inner ℝ (f t) (WkpU.toLp (G.w (k : ℕ)).val) := by
      simp only [hFdef]
      rw [hπid t ht]
    have hsum : ∑ j, A t k j * y t j
        = ∑ j : Fin m, y t j * parabilinform (P t) (G.w (j : ℕ)) (G.w (k : ℕ)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hAdef]
      rw [hπid t ht, mul_comm]
    rw [hFt, hsum]
    ring
  · -- initial condition
    intro k
    show y 0 k = inner ℝ g (WkpU.toLp (G.w (k : ℕ)).val)
    rw [hy0]
  · -- uniqueness among C¹ solutions on [0,T]
    intro dc' hdc'C1 hdc' k t ht
    have hZd : ∀ s ∈ Set.Icc (0:ℝ) T,
        HasDerivWithinAt (fun τ j => dc' j τ)
          (affineField A F s (fun j => dc' j s)) (Set.Icc 0 T) s := by
      intro s hs
      refine hasDerivWithinAt_pi.2 (fun j => ?_)
      have hder : HasDerivAt (dc' j) (deriv (dc' j) s) s :=
        ((hdc'C1 j).differentiable (by norm_num)).differentiableAt.hasDerivAt
      have hval : affineField A F s (fun i => dc' i s) j = deriv (dc' j) s := by
        show F s j - ∑ i, A s j i * dc' i s = deriv (dc' j) s
        have hODE := hdc'.1 j s hs
        have hFs : F s j = inner ℝ (f s) (WkpU.toLp (G.w (j : ℕ)).val) := by
          simp only [hFdef]
          rw [hπid s hs]
        have hsum : ∑ i, A s j i * dc' i s
            = ∑ i : Fin m, dc' i s * parabilinform (P s) (G.w (i : ℕ)) (G.w (j : ℕ)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hAdef]
          rw [hπid s hs, mul_comm]
        rw [hFs, hsum]
        linarith [hODE]
      rw [hval]
      exact hder.hasDerivWithinAt
    have hYd : ∀ s ∈ Set.Icc (0:ℝ) T,
        HasDerivWithinAt y (affineField A F s (y s)) (Set.Icc 0 T) s :=
      fun s hs => (hyODE s hs).hasDerivWithinAt
    have h0 : (fun τ j => dc' j τ) 0 = y 0 := by
      funext j
      rw [hy0]
      show dc' j 0 = y₀ j
      simp only [hy₀def]
      exact hdc'.2 j
    have hEq := affine_ode_unique A F hκnn hA_bdd
      (fun s hs => (hZd s hs).continuousWithinAt)
      (fun s hs => (hYd s hs).continuousWithinAt)
      hZd hYd h0
    exact congrFun (hEq ht) k



set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Existence of a weak solution for strong (continuous-in-time) data.**   -/
theorem exists_weakSolution_strong
    {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ)
    (hP_bdd : ∀ t, (P t).IsBounded M)
    (hP_cont : CoeffsContinuousInTime P T)
    (hP_tmeas : ∀ (z : L2TH10U d U hU T) (w0 : H1U0 d U hU),
      AEStronglyMeasurable (fun t => parabilinform (P t) (z t) w0)
        (volume.restrict (Set.Icc (0:ℝ) T)))
    (hP_riesz : ∀ (φ : ℝ → ℝ) (w0 : H1U0 d U hU),
      ∃ R : L2TH10U d U hU T, ∀ (z : L2TH10U d U hU T),
        (∫ t in Set.Icc (0:ℝ) T, φ t * parabilinform (P t) (z t) w0) = inner ℝ z R)
    (f : ℝ → Lp ℝ 2 (μU d U)) (hf : ContinuousOn f (Set.Icc (0:ℝ) T))
    (g : Lp ℝ 2 (μU d U)) :
    ∃ (u : L2TH10U d U hU T) (u' : L2TH10U_dual d U hU T),
      IsWeakSolution P T (forcingLift T f hf) g u u' := by
  obtain ⟨G⟩ := exists_galerkinBasis d U hU
  -- the Galerkin coefficient sequence: honest, via Picard–Lindelöf
  have hcoeffs : ∀ m : ℕ, ∃ dc : Fin m → ℝ → ℝ,
      (∀ k, ContDiff ℝ 1 (dc k)) ∧ GalerkinODE G P T (forcingLift T f hf) g dc := by
    intro m
    obtain ⟨dc, hC1, hstrong, _⟩ :=
      galerkin_ode_solvable_strong G P T hT hP_bdd hP_cont f hf g m
    exact ⟨dc, hC1, hstrong.galerkinODE hf⟩
  choose dCoeffsSeq h_C1 h_galerkin using hcoeffs
  -- energy estimates + weak compactness give the weak limits (v2, fully proven)
  obtain ⟨subseq, hmono, u, u', hconv_u, hconv_u'⟩ :=
    galerkin_seq_extract_limits G P T hT hθ hMpos hP_para hP_bdd (forcingLift T f hf) g
      dCoeffsSeq h_galerkin h_C1
  refine ⟨u, u', ?_, ?_⟩
  · -- weak time derivative, preserved under the weak limits (v2)
    exact isWeakTimeDeriv_of_weak_limits
      (fun n => galerkin_approx_isWeakTimeDeriv G T hT.le (dCoeffsSeq (subseq n))
        (h_C1 (subseq n)))
      hconv_u hconv_u'
  · -- weak formulation, by density from the basis identities (v2)
    exact weaksol_of_basis G P T hP_bdd (forcingLift T f hf) g u u'
      (galerkin_weaklimit_basis G P T hP_bdd hP_tmeas hP_riesz (forcingLift T f hf) g
        dCoeffsSeq h_galerkin h_C1 subseq hmono u u' hconv_u hconv_u')
