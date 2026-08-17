import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.MeanInequalities

import PDE.FunctionSpaces.SobolevSpace.SobolevSpaces

/-!
# Mollification (Evans C.5 / §5.3.1 — phase M of the approximation plan)

`mollify φ U f` is the convolution of the zero-extension of `f : (Fin d → ℝ) →ₘ[μU d U] ℝ`
with the normalized bump `φ.normed volume` (mollifier radius `φ.rOut`).  Headline results:

* **`mollify_weakDeriv` (M4)**: at every `x` whose closed `φ.rOut`-ball sits inside `U`, the
  classical iterated derivative of the mollification *is* the mollification of the weak
  derivative: `D^s (mollify φ U u) x = mollify φ U (weakDeriv u) x`.
  Classical side: iterated directional derivatives of a convolution land on the smooth factor
  (`iteratedFDeriv_convolution_right`).  Weak side: for fixed `x` the reflected bump
  `y ↦ φ.normed (x − y)` is a `Cc_inftyU` test function, so the IBP *definition* of the weak
  derivative applies; the reflection chain rule (`iteratedFDeriv_comp_const_sub`) produces the
  matching `(−1)ⁿ`, which cancels against the IBP sign.

* **`eLpNorm_mollify_le` (Minkowski-type bound; the quantitative half of M5)**:
  `‖mollify φ U f‖_{Lᵖ(ℝᵈ)} ≤ ‖f‖_{Lᵖ(U)}`.  This is Minkowski's integral inequality for a
  probability kernel, proven unconditionally at the `ℝ≥0∞` level
  (`lintegral_convolution_pow_le`) via the sum-form Hölder inequality
  (`ENNReal.lintegral_mul_norm_pow_le`, exponents `1/p` and `1 − 1/p`) + Tonelli +
  translation invariance of `volume` — no finiteness case analysis anywhere.

The qualitative half of M5 (`mollify φ f → f` in `Lᵖ` as `φ.rOut → 0`) additionally needs
continuity of translation in `Lᵖ` and is the next step of the plan.
-/

open MeasureTheory ENNReal Filter Topology NNReal Metric
open scoped Convolution

variable {d : ℕ+} {U : Set (Fin d → ℝ)}

/-! ## Zero extension -/

/-- Zero-extension to `ℝᵈ` of (the canonical representative of) an a.e. class on `U`. -/
noncomputable def extZ (U : Set (Fin d → ℝ)) (f : (Fin d → ℝ) →ₘ[μU d U] ℝ) :
    (Fin d → ℝ) → ℝ :=
  U.indicator f

lemma extZ_ae_eq (hU : MeasurableSet U) (f : (Fin d → ℝ) →ₘ[μU d U] ℝ) :
    extZ U f =ᵐ[μU d U] ⇑f := by
  filter_upwards [ae_restrict_mem hU] with x hx
  exact Set.indicator_of_mem hx _

lemma extZ_aestronglyMeasurable (hU : MeasurableSet U) (f : (Fin d → ℝ) →ₘ[μU d U] ℝ) :
    AEStronglyMeasurable (extZ U f) volume :=
  (aestronglyMeasurable_indicator_iff hU).mpr f.aestronglyMeasurable

/-- The zero-extension of a globally-`Lᵖ` function on `U` is locally integrable on all of
`ℝᵈ` (via Hölder on each compact; this can fail for merely locally-`Lᵖ` functions). -/
lemma extZ_locallyIntegrable (hU : IsOpen U) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : (Fin d → ℝ) →ₘ[μU d U] ℝ} (hf : MemLp f p (μU d U)) :
    LocallyIntegrable (extZ U f) volume := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  rw [IntegrableOn, extZ, integrable_indicator_iff hU.measurableSet, IntegrableOn,
    Measure.restrict_restrict hU.measurableSet]
  haveI : IsFiniteMeasure (volume.restrict (U ∩ K)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_right) hK.measure_lt_top
  exact (hf.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)).integrable
    Fact.out

/-! ## Mollification: definition and smoothness (M1–M3) -/

/-- Mollification of an a.e. class on `U`: convolution of its zero-extension with the
normalized bump `φ.normed volume`. -/
noncomputable def mollify (φ : ContDiffBump (0 : Fin d → ℝ)) (U : Set (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₘ[μU d U] ℝ) : (Fin d → ℝ) → ℝ :=
  (extZ U f) ⋆ φ.normed volume

/-- The mollification of a (globally) `Lᵖ` function is smooth on all of `ℝᵈ`. -/
lemma mollify_contDiff (φ : ContDiffBump (0 : Fin d → ℝ)) (hU : IsOpen U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : (Fin d → ℝ) →ₘ[μU d U] ℝ}
    (hf : MemLp f p (μU d U)) {n : ℕ∞} :
    ContDiff ℝ n (mollify φ U f) :=
  HasCompactSupport.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
    φ.hasCompactSupport_normed (extZ_locallyIntegrable hU hf) φ.contDiff_normed

/-! ## Iterated directional derivatives of a convolution (classical side of M4) -/

/-- Right-peeling form of `iteratedFDeriv_succ_apply_right`, with the evaluation pushed
inside: the `(n+1)`-st derivative applied to `m` is the `n`-th derivative of the directional
derivative along the last entry of `m`. -/
lemma iteratedFDeriv_succ_apply_right' {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (n : ℕ) (x : Fin d → ℝ)
    (m : Fin (n + 1) → (Fin d → ℝ)) :
    iteratedFDeriv ℝ (n + 1) F x m
      = iteratedFDeriv ℝ n (fun y => fderiv ℝ F y (m (Fin.last n))) x (Fin.init m) := by
  rw [iteratedFDeriv_succ_apply_right]
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ F) :=
    hF.fderiv_right (by exact_mod_cast le_top)
  have hcomp : iteratedFDeriv ℝ n (fun y => fderiv ℝ F y (m (Fin.last n))) x
      = (ContinuousLinearMap.apply ℝ ℝ (m (Fin.last n))).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fderiv ℝ F) x) :=
    ContinuousLinearMap.iteratedFDeriv_comp_left
      (ContinuousLinearMap.apply ℝ ℝ (m (Fin.last n))) hfd.contDiffAt
      (by exact_mod_cast le_top)
  rw [hcomp]
  rfl

/-- **Iterated directional derivatives of a convolution hit the smooth factor**:
`D^m (f ⋆ g) = f ⋆ D^m g` for `f` locally integrable and `g` smooth with compact support. -/
lemma iteratedFDeriv_convolution_right (n : ℕ) :
    ∀ {f g : (Fin d → ℝ) → ℝ}, LocallyIntegrable f volume →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
      ∀ (x : Fin d → ℝ) (m : Fin n → (Fin d → ℝ)),
        iteratedFDeriv ℝ n (f ⋆ g) x m
          = (f ⋆ fun z => iteratedFDeriv ℝ n g z m) x := by
  induction n with
  | zero =>
    intro f g hf hg hgs x m
    have h0 : (fun z => iteratedFDeriv ℝ 0 g z m) = g :=
      funext fun z => iteratedFDeriv_zero_apply m
    rw [iteratedFDeriv_zero_apply, h0]
  | succ n ih =>
    intro f g hf hg hgs x m
    have hconv_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ⋆ g) :=
      HasCompactSupport.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
        hgs hf hg
    rw [iteratedFDeriv_succ_apply_right' hconv_smooth n x m]
    have hgd_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => fderiv ℝ g z (m (Fin.last n))) :=
      (hg.fderiv_right (by exact_mod_cast le_top)).clm_apply contDiff_const
    have hgd_supp : HasCompactSupport (fun z => fderiv ℝ g z (m (Fin.last n))) :=
      HasCompactSupport.comp_left
        (g := fun L : (Fin d → ℝ) →L[ℝ] ℝ => L (m (Fin.last n)))
        (hgs.fderiv ℝ) rfl
    have hfd : (fun y => fderiv ℝ (f ⋆ g) y (m (Fin.last n)))
        = fun y => (f ⋆ fun z => fderiv ℝ g z (m (Fin.last n))) y := by
      funext y
      rw [(hgs.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hf
        (hg.of_le (by exact_mod_cast le_top)) y).fderiv]
      exact convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ) hf
        (hgs.fderiv ℝ) (hg.continuous_fderiv (by simp)) y (m (Fin.last n))
    rw [hfd, ih hf hgd_smooth hgd_supp x (Fin.init m)]
    congr 1
    funext z
    exact (iteratedFDeriv_succ_apply_right' hg n z m).symm

/-! ## Reflection chain rule -/

/-- Iterated derivatives of the reflected function `z ↦ g (x − z)`: composing with the
negation continuous linear map and a translation; the multilinear sign is `(−1)ⁿ`. -/
lemma iteratedFDeriv_comp_const_sub {g : (Fin d → ℝ) → ℝ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (n : ℕ) (x y : Fin d → ℝ)
    (m : Fin n → (Fin d → ℝ)) :
    iteratedFDeriv ℝ n (fun z => g (x - z)) y m
      = (-1 : ℝ) ^ n • iteratedFDeriv ℝ n g (x - y) m := by
  have hdecomp : (fun z : Fin d → ℝ => g (x - z))
      = (fun w : Fin d → ℝ => g (x + w)) ∘ ⇑(-(ContinuousLinearMap.id ℝ (Fin d → ℝ))) := by
    funext z
    simp [sub_eq_add_neg]
  have htrans : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : Fin d → ℝ => g (x + w)) :=
    hg.comp (contDiff_const.add contDiff_id)
  rw [hdecomp,
    ContinuousLinearMap.iteratedFDeriv_comp_right
      (-(ContinuousLinearMap.id ℝ (Fin d → ℝ))) htrans y (by exact_mod_cast le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have harg : (fun i => (-(ContinuousLinearMap.id ℝ (Fin d → ℝ))) (m i))
      = fun i => (-1 : ℝ) • m i := by
    funext i
    simp
  have hpt : (-(ContinuousLinearMap.id ℝ (Fin d → ℝ))) y = -y := by simp
  rw [harg, hpt, iteratedFDeriv_comp_add_left n x (-y),
    ContinuousMultilinearMap.map_smul_univ]
  rw [show x + -y = x - y from (sub_eq_add_neg x y).symm]
  congr 1
  simp

/-! ## The reflected bump is a test function -/

/-- For `x` with `closedBall x φ.rOut ⊆ U`, the reflected bump `y ↦ φ.normed (x − y)` is a
`Cc_inftyU` test function on `U`. -/
lemma bumpReflect_mem_Cc_inftyU (φ : ContDiffBump (0 : Fin d → ℝ)) (x : Fin d → ℝ)
    (hx : Metric.closedBall x φ.rOut ⊆ U) :
    (fun y => φ.normed volume (x - y)) ∈ Cc_inftyU d U := by
  have hsupp : Function.support (fun y => φ.normed volume (x - y))
      ⊆ Metric.ball x φ.rOut := by
    intro y hy
    have hmem : x - y ∈ Function.support (φ.normed volume) := hy
    rw [φ.support_normed_eq (μ := volume), Metric.mem_ball, dist_zero_right] at hmem
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    exact hmem
  have htsupp : tsupport (fun y => φ.normed volume (x - y))
      ⊆ Metric.closedBall x φ.rOut :=
    (closure_mono hsupp).trans Metric.closure_ball_subset_closedBall
  refine ⟨?_, htsupp.trans hx, ?_⟩
  · exact IsCompact.of_isClosed_subset (isCompact_closedBall x φ.rOut)
      (isClosed_tsupport _) htsupp
  · exact φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)

/-! ## M4: the mollified weak derivative -/

variable {hU : IsOpen U}

set_option maxHeartbeats 1000000 in
/-- **The mollified weak derivative is the mollifier convolved with the weak derivative**
(Evans §5.3.1, step 2): for `u ∈ W^{k,p}(U)` and every `x` whose closed `φ.rOut`-ball lies in
`U`, `D^s (mollify φ U u) x = mollify φ U (D^s_weak u) x`. -/
theorem mollify_weakDeriv {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : ContDiffBump (0 : Fin d → ℝ)) (u : WkpU d k p U hU)
    (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d)
    (x : Fin d → ℝ) (hx : Metric.closedBall x φ.rOut ⊆ U) :
    iteratedFDeriv ℝ n (mollify φ U u.val.val) x (unitSeq s)
      = mollify φ U (WkpU.weakDeriv u n hn s) x := by
  have hloc : LocallyIntegrable (extZ U u.val.val) volume :=
    extZ_locallyIntegrable hU (WkpU.memLp u)
  have hclass := iteratedFDeriv_convolution_right n hloc
    (φ.contDiff_normed (μ := volume)) (φ.hasCompactSupport_normed (μ := volume)) x
    (unitSeq s)
  -- reduce both sides to integrals over `μU d U`
  have hind : ∀ (g : (Fin d → ℝ) →ₘ[μU d U] ℝ) (K : (Fin d → ℝ) → ℝ),
      (∫ t, ContinuousLinearMap.lsmul ℝ ℝ (extZ U g t) (K (x - t)) ∂volume)
        = ∫ t, (g : (Fin d → ℝ) → ℝ) t • K (x - t) ∂μU d U := by
    intro g K
    have heq : (fun t => ContinuousLinearMap.lsmul ℝ ℝ (extZ U g t) (K (x - t)))
        = U.indicator fun t => (g : (Fin d → ℝ) → ℝ) t • K (x - t) := by
      funext t
      by_cases ht : t ∈ U
      · simp [extZ, Set.indicator_of_mem ht]
      · simp [extZ, Set.indicator_of_notMem ht]
    rw [heq, integral_indicator hU.measurableSet]
    rfl
  simp only [mollify]
  rw [hclass, convolution_def,
    hind u.val.val (fun z => iteratedFDeriv ℝ n (φ.normed volume) z (unitSeq s)),
    convolution_def, hind (WkpU.weakDeriv u n hn s) (φ.normed volume)]
  -- the IBP identity with the reflected bump as test function
  have hspec := WeakmultiderivU_spec U u.val s (WkpU.hasWeakDeriv u n hn s)
    (fun y => φ.normed volume (x - y)) (bumpReflect_mem_Cc_inftyU φ x hx)
  -- reflect the iterated derivative of the test function
  have hrefl : (fun t => (u.val : (Fin d → ℝ) → ℝ) t •
        (iteratedFDeriv ℝ n (fun y => φ.normed volume (x - y)) t) (unitSeq s))
      =ᵐ[μU d U] fun t => (-1 : ℝ) ^ (n : ℕ) • ((u.val : (Fin d → ℝ) → ℝ) t •
        iteratedFDeriv ℝ n (φ.normed volume) (x - t) (unitSeq s)) := by
    refine Eventually.of_forall (fun t => ?_)
    dsimp only
    rw [iteratedFDeriv_comp_const_sub (φ.contDiff_normed (μ := volume)) n x t (unitSeq s)]
    simp only [smul_eq_mul]
    ring
  rw [integral_congr_ae hrefl, integral_smul] at hspec
  -- cancel the (−1)ⁿ and finish by commuting the product
  have hmain := smul_right_injective ℝ
    (pow_ne_zero (n : ℕ) (neg_ne_zero.mpr (one_ne_zero (α := ℝ)))) hspec
  rw [hmain]
  refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
  simp only [smul_eq_mul, WkpU.weakDeriv]
  ring

/-! ## Minkowski-type bound (quantitative half of M5) -/

set_option maxHeartbeats 1000000 in
/-- **Minkowski's integral inequality for a probability kernel** (unconditional, `ℝ≥0∞`
level): if `∫ w = 1` then `∫ (∫ F t · w(x−t) dt)^p dx ≤ ∫ F^p`.  Sum-form Hölder against the
probability weight (Jensen), then Tonelli and translation invariance of `volume`. -/
theorem lintegral_convolution_pow_le {w F : (Fin d → ℝ) → ℝ≥0∞} {p : ℝ} (hp : 1 ≤ p)
    (hw : Measurable w) (hF : Measurable F) (hw1 : (∫⁻ y, w y) = 1) :
    (∫⁻ x, (∫⁻ t, F t * w (x - t)) ^ p) ≤ ∫⁻ x, F x ^ p := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
  -- translation/reflection invariance of the kernel mass
  have hshift₁ : ∀ t₀ : Fin d → ℝ, (∫⁻ x, w (x - t₀)) = 1 := by
    intro t₀
    have hmp : MeasurePreserving (fun x : Fin d → ℝ => x + -t₀) volume volume :=
      ⟨measurable_add_const _, map_add_right_eq_self volume _⟩
    calc (∫⁻ x, w (x - t₀)) = ∫⁻ x, w (x + -t₀) := by
          refine lintegral_congr fun x => ?_
          rw [sub_eq_add_neg]
      _ = ∫⁻ y, w y := hmp.lintegral_comp hw
      _ = 1 := hw1
  have hshift₂ : ∀ x₀ : Fin d → ℝ, (∫⁻ t, w (x₀ - t)) = 1 := by
    intro x₀
    have hmpn : MeasurePreserving (fun t : Fin d → ℝ => -t) volume volume :=
      ⟨measurable_neg, Measure.map_neg_eq_self volume⟩
    have hmpl : MeasurePreserving (fun t : Fin d → ℝ => x₀ + t) volume volume :=
      ⟨measurable_const_add _, map_add_left_eq_self volume _⟩
    have hcomp := (hmpl.comp hmpn).lintegral_comp hw
    calc (∫⁻ t, w (x₀ - t)) = ∫⁻ t, w (x₀ + -t) := by
          refine lintegral_congr fun t => ?_
          rw [sub_eq_add_neg]
      _ = ∫⁻ y, w y := hcomp
      _ = 1 := hw1
  -- Tonelli + invariance: ∫∫ G t · w(x−t) dt dx = ∫ G
  have hkey : ∀ {G : (Fin d → ℝ) → ℝ≥0∞}, Measurable G →
      (∫⁻ x, ∫⁻ t, G t * w (x - t)) = ∫⁻ t, G t := by
    intro G hG
    rw [lintegral_lintegral_swap
      (((hG.comp measurable_snd).mul
        (hw.comp (measurable_fst.sub measurable_snd))).aemeasurable)]
    calc (∫⁻ t, ∫⁻ x, G t * w (x - t))
        = ∫⁻ t, G t * ∫⁻ x, w (x - t) := by
          refine lintegral_congr fun t => ?_
          have hwt : Measurable fun x : Fin d → ℝ => w (x - t) :=
            hw.comp (measurable_id.sub measurable_const)
          rw [lintegral_const_mul _ hwt]
      _ = ∫⁻ t, G t := by
          refine lintegral_congr fun t => ?_
          rw [hshift₁ t, mul_one]
  -- pointwise Jensen via the sum-form Hölder inequality
  have hjensen : ∀ x : Fin d → ℝ,
      (∫⁻ t, F t * w (x - t)) ^ p ≤ ∫⁻ t, F t ^ p * w (x - t) := by
    intro x
    have hwx : Measurable fun t => w (x - t) := hw.comp (measurable_const.sub measurable_id)
    have hFp : Measurable fun t => F t ^ p :=
      (ENNReal.continuous_rpow_const.measurable).comp hF
    have hexp1 : (0 : ℝ) ≤ 1 / p := by positivity
    have hexp2 : (0 : ℝ) ≤ 1 - 1 / p := by
      have h1 : 1 / p ≤ 1 := by
        rw [div_le_one hp0]
        exact hp
      linarith
    have hHolder := ENNReal.lintegral_mul_norm_pow_le (μ := volume)
      ((hFp.mul hwx).aemeasurable) hwx.aemeasurable hexp1 hexp2 (by ring)
    have hcollapse : (fun t => (F t ^ p * w (x - t)) ^ (1 / p) * w (x - t) ^ (1 - 1 / p))
        = fun t => F t * w (x - t) := by
      funext t
      rw [ENNReal.mul_rpow_of_nonneg _ _ hexp1, ← ENNReal.rpow_mul,
        mul_one_div_cancel hp0.ne', ENNReal.rpow_one, mul_assoc,
        ← ENNReal.rpow_add_of_nonneg _ _ hexp1 hexp2,
        show 1 / p + (1 - 1 / p) = 1 from by ring, ENNReal.rpow_one]
    simp only [Pi.mul_apply] at hHolder
    rw [hcollapse, hshift₂ x, ENNReal.one_rpow, mul_one] at hHolder
    have hpow := ENNReal.rpow_le_rpow hHolder (le_of_lt hp0)
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one] at hpow
  calc (∫⁻ x, (∫⁻ t, F t * w (x - t)) ^ p)
      ≤ ∫⁻ x, ∫⁻ t, F t ^ p * w (x - t) := lintegral_mono hjensen
    _ = ∫⁻ t, F t ^ p := hkey ((ENNReal.continuous_rpow_const.measurable).comp hF)

set_option maxHeartbeats 1000000 in
/-- **The mollification does not increase the `Lᵖ` norm**: `‖mollify φ U f‖_{Lᵖ(ℝᵈ)} ≤
‖f‖_{Lᵖ(U)}` for `1 ≤ p < ∞` — Minkowski's inequality for the probability kernel
`φ.normed volume`. -/
theorem eLpNorm_mollify_le (φ : ContDiffBump (0 : Fin d → ℝ)) (hU : IsOpen U)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (hp1 : 1 ≤ p)
    (f : (Fin d → ℝ) →ₘ[μU d U] ℝ) :
    eLpNorm (mollify φ U f) p volume ≤ eLpNorm (f : (Fin d → ℝ) → ℝ) p (μU d U) := by
  -- a measurable representative of the zero-extension
  set f₀ := (extZ_aestronglyMeasurable hU.measurableSet f).mk (extZ U f) with hf₀def
  have hf₀meas : StronglyMeasurable f₀ :=
    (extZ_aestronglyMeasurable hU.measurableSet f).stronglyMeasurable_mk
  have h_ae : extZ U f =ᵐ[volume] f₀ :=
    (extZ_aestronglyMeasurable hU.measurableSet f).ae_eq_mk
  -- the mollification is unchanged under the representative swap
  have hmoll : mollify φ U f = fun x => ∫ t, f₀ t • φ.normed volume (x - t) := by
    funext x
    simp only [mollify, convolution_def, ContinuousLinearMap.lsmul_apply]
    exact integral_congr_ae (h_ae.mono fun t ht => by dsimp only; rw [ht])
  -- pointwise enorm bound by the ℝ≥0∞ convolution
  have hpt_bound : ∀ x : Fin d → ℝ, ‖(∫ t, f₀ t • φ.normed volume (x - t))‖ₑ
      ≤ ∫⁻ t, ‖f₀ t‖ₑ * ‖φ.normed volume (x - t)‖ₑ := by
    intro x
    refine (enorm_integral_le_lintegral_enorm _).trans
      (le_of_eq (lintegral_congr fun t => ?_))
    rw [smul_eq_mul, enorm_mul]
  -- unit mass of the kernel in ℝ≥0∞
  have hmass : (∫⁻ y, ‖φ.normed volume y‖ₑ) = 1 := by
    have h1 := ofReal_integral_eq_lintegral_ofReal (φ.integrable_normed (μ := volume))
      (Eventually.of_forall φ.nonneg_normed)
    rw [φ.integral_normed, ENNReal.ofReal_one] at h1
    calc (∫⁻ y, ‖φ.normed volume y‖ₑ)
        = ∫⁻ y, ENNReal.ofReal (φ.normed volume y) :=
          lintegral_congr fun y => Real.enorm_of_nonneg (φ.nonneg_normed y)
      _ = 1 := h1.symm
  have hw_meas : Measurable fun z : Fin d → ℝ => ‖φ.normed volume z‖ₑ :=
    φ.continuous_normed.measurable.enorm
  have hF_meas : Measurable fun t => ‖f₀ t‖ₑ := hf₀meas.measurable.enorm
  have hpR : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hpt hp1
  -- assemble
  have hext : eLpNorm (extZ U f) p volume = eLpNorm (f : (Fin d → ℝ) → ℝ) p (μU d U) :=
    eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet
  rw [← hext, hmoll, eLpNorm_eq_lintegral_rpow_enorm hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm hp0 hpt]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  calc (∫⁻ x, ‖(∫ t, f₀ t • φ.normed volume (x - t))‖ₑ ^ p.toReal)
      ≤ ∫⁻ x, (∫⁻ t, ‖f₀ t‖ₑ * ‖φ.normed volume (x - t)‖ₑ) ^ p.toReal := by
        refine lintegral_mono fun x => ?_
        exact ENNReal.rpow_le_rpow (hpt_bound x) (by positivity)
    _ ≤ ∫⁻ x, ‖f₀ x‖ₑ ^ p.toReal :=
        lintegral_convolution_pow_le hpR hw_meas hF_meas hmass
    _ = ∫⁻ x, ‖extZ U f x‖ₑ ^ p.toReal := by
        refine lintegral_congr_ae (h_ae.mono fun x hx => ?_)
        dsimp only
        rw [hx]
