import PDE.Basics.Laplace.CalculusBasic
import PDE.Background.CalculusMeasureTheory.SphereSurfaceMeasure
import PDE.Background.CalculusMeasureTheory.DomainGeometry

open Real Set MeasureTheory Metric Filter Function Pointwise InnerProductSpace RealInnerProductSpace
open scoped BigOperators Topology

/-!
### Basic Integrals and Properties
-/

lemma integral_Ioo_r_sq (R : ℝ) (hR : 0 < R) : ∫ r in Set.Ioo 0 R, r^2 = R^3 / 3 := by
  have h_symm : (Set.Ioo 0 R : Set ℝ) =ᶠ[ae volume] Set.Ioc 0 R :=
    Ioo_ae_eq_Ioc
  rw [MeasureTheory.Measure.restrict_congr_set h_symm, ← intervalIntegral.integral_of_le hR.le]
  simp only [integral_pow, Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Nat.cast_ofNat]
  ring

lemma integral_Ioo_r_sq_eval (u : E → ℝ) (x₀ : E) (R : ℝ) (hR : 0 < R) :
    ∫ r in Set.Ioo 0 R, 4 * Real.pi * r^2 * u x₀ = (4 / 3) * Real.pi * R^3 * u x₀ := by
  have h : (fun r ↦ 4 * Real.pi * r^2 * u x₀) = fun r ↦ (4 * Real.pi * u x₀) * r^2 := by ext; ring
  rw [h, MeasureTheory.integral_const_mul, integral_Ioo_r_sq R hR]
  ring

lemma integral_cross_smul (Ω : Set E) (u v : E → ℝ) (t : ℝ) :
  ∫ x in Ω, ⟪gradient u x, t • gradient v x⟫_ℝ = t * ∫ x in Ω, ⟪gradient u x, gradient v x⟫_ℝ := by
  simp_rw [real_inner_smul_right]
  exact integral_const_mul t fun x => ⟪gradient u x, gradient v x⟫_ℝ

lemma integral_eq_setIntegral_of_support_subset (Ω : Set E) (v f : E → ℝ)
  (hv_supp : tsupport v ⊆ Ω) :
  ∫ x, v x • f x = ∫ x in Ω, v x * f x := by
  change ∫ x, v x * f x = _
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [image_eq_zero_of_notMem_tsupport fun h => hx (hv_supp h)]).symm

lemma eq_zero_on_ball_of_nonneg_integral_zero (f : E → ℝ) (x₀ : E) (R : ℝ)
    (h_cont : ContinuousOn f (Metric.closedBall x₀ R))
    (h_int_f : IntegrableOn f (Metric.closedBall x₀ R))
    (h_nonneg : ∀ x ∈ Metric.closedBall x₀ R, 0 ≤ f x)
    (h_int_zero : ∫ x in Metric.closedBall x₀ R, f x = 0) :
    ∀ x ∈ Metric.ball x₀ R, f x = 0 := by
  have h_ae_nonneg : ∀ᵐ x ∂(volume.restrict (Metric.closedBall x₀ R)), 0 ≤ f x := by
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with y hy
    exact h_nonneg y hy
  have h_ae_eq_zero := (integral_eq_zero_iff_of_nonneg_ae h_ae_nonneg h_int_f).mp h_int_zero
  intro x hx
  by_contra h_neq
  have h_pos : 0 < f x := lt_of_le_of_ne (h_nonneg x (Metric.ball_subset_closedBall hx)) (fun h ↦ h_neq h.symm)
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := Metric.continuousOn_iff.mp h_cont x (Metric.ball_subset_closedBall hx) (f x / 2) (by linarith)
  let r' := min δ (R - dist x x₀) / 2
  have hr'_pos : 0 < r' := by
    have h_lt := Metric.mem_ball.mp hx
    rw [dist_comm] at h_lt
    have : 0 < R - dist x x₀ := sub_pos.mpr hx
    positivity
  have h_subset : Metric.closedBall x r' ⊆ Metric.closedBall x₀ R := by
    intro y hy; rw [Metric.mem_closedBall] at hy ⊢
    have hx_dist := Metric.mem_ball.mp hx
    have h_tri := dist_triangle x₀ x y
    have h_symm1 : dist x y = dist y x := dist_comm x y
    have h_symm2 : dist x₀ y = dist y x₀ := dist_comm x₀ y
    have h_symm3 : dist x₀ x = dist x x₀ := dist_comm x₀ x
    have h_min : min δ (R - dist x x₀) ≤ R - dist x x₀ := min_le_right δ (R - dist x x₀)
    have h_r_def : r' = min δ (R - dist x x₀) / 2 := rfl
    linarith
  have h_pointwise_bound : ∀ y ∈ Metric.closedBall x r', f x / 2 ≤ f y := fun y hy ↦ by
    have hy_R : y ∈ Metric.closedBall x₀ R := h_subset hy
    rw [Metric.mem_closedBall] at hy
    have h_bound := hδ_bound y hy_R (by
      have h_r_def : r' = min δ (R - dist x x₀) / 2 := rfl
      have h_min : min δ (R - dist x x₀) ≤ δ := min_le_left δ (R - dist x x₀)
      linarith)
    rw [Real.dist_eq] at h_bound
    have := abs_lt.mp h_bound
    linarith
  have h_sub_int : IntegrableOn f (Metric.closedBall x r') := IntegrableOn.mono_set h_int_f h_subset
  have h_const_int_pos : 0 < ∫ y in Metric.closedBall x r', f x / 2 := by
    rw [setIntegral_const, volume_closed_ball_3d x r' hr'_pos, smul_eq_mul]
    positivity
  have h_int_pos : 0 < ∫ y in Metric.closedBall x r', f y :=
    lt_of_lt_of_le h_const_int_pos (setIntegral_mono_on (continuousOn_const.integrableOn_compact (isCompact_closedBall x r')) h_sub_int isClosed_closedBall.measurableSet h_pointwise_bound)
  have h_integral_le : ∫ y in Metric.closedBall x r', f y ≤ ∫ y in Metric.closedBall x₀ R, f y :=
    setIntegral_mono_set h_int_f h_ae_nonneg (Filter.Eventually.of_forall h_subset)
  exact ne_of_gt (lt_of_lt_of_le h_int_pos h_integral_le) h_int_zero

lemma continuousOn_ae_eq_zero_to_pointwise (Ω : Set E) (f : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hf_cont : ContinuousOn f Ω)
  (h_ae : f =ᵐ[volume.restrict Ω] 0) :
  ∀ x ∈ Ω, f x = 0 := by
  intro x hx
  by_contra h_neq
  exact lt_irrefl (0 : ENNReal) (calc
    0 < volume (Ω ∩ (fun y => ‖f y‖) ⁻¹' (Set.Ioi 0)) :=
      (ContinuousOn.isOpen_inter_preimage hf_cont.norm h_domain.is_open isOpen_Ioi).measure_pos volume ⟨x, hx, norm_pos_iff.mpr h_neq⟩
    _ = volume {y | ¬(y ∈ Ω → f y = 0)} := congr_arg _ (by ext; simp [Classical.not_imp])
    _ = 0 := (ae_restrict_iff' h_domain.is_open.measurableSet).mp h_ae)

/-!
### Polar and Spherical Transformations
-/

lemma integral_sphere_change_vars (x₀ : E) (r : ℝ) (hr : 0 < r) (u : E → ℝ) :
    ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea =
    r ^ 2 * ∫ (y : E) in sphere 0 1, u (x₀ + r • y) ∂surfaceArea := by
  let e_scale : E ≃ₜ E := Homeomorph.smulOfNeZero r hr.ne'
  let e_trans : E ≃ₜ E := Homeomorph.addRight x₀
  let e_affine : E ≃ₜ E := e_scale.trans e_trans

  have h_domain : e_affine ⁻¹' (sphere x₀ r) = sphere 0 1 := by
    ext y
    simp only [e_affine, e_scale, e_trans, mem_preimage, Homeomorph.trans_apply, Homeomorph.smulOfNeZero_apply, Homeomorph.coe_addRight, mem_sphere_iff_norm, add_sub_cancel_right, sub_zero]
    exact ⟨fun a ↦ mul_left_cancel₀ hr.ne' (by rw [mul_one]; rwa [norm_smul, Real.norm_of_nonneg hr.le] at a), fun a ↦ by rw [norm_smul, Real.norm_of_nonneg hr.le, a, mul_one]⟩

  have h_measure_scale : MeasureTheory.Measure.map e_affine surfaceArea = (ENNReal.ofReal ((r^2)⁻¹)) • surfaceArea := by
    change MeasureTheory.Measure.map (e_trans ∘ e_scale) surfaceArea = _
    rw [← MeasureTheory.Measure.map_map e_trans.continuous.measurable e_scale.continuous.measurable]
    have h_map_scale : MeasureTheory.Measure.map e_scale surfaceArea = (ENNReal.ofReal ((r^2)⁻¹)) • surfaceArea := by
      ext s hs
      rw [MeasureTheory.Measure.map_apply e_scale.continuous.measurable hs, MeasureTheory.Measure.smul_apply]
      have h_preimage : e_scale ⁻¹' s = r⁻¹ • s := by
        ext w
        simp only [Set.mem_preimage, Set.mem_smul_set]
        constructor
        · intro hw
          exact ⟨r • w, hw, by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]⟩
        · rintro ⟨v, hv, rfl⟩
          change r • (r⁻¹ • v) ∈ s
          rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
          exact hv
      rw [h_preimage]
      show μH[2] (r⁻¹ • s) = ENNReal.ofReal (r ^ 2)⁻¹ • μH[2] s
      rw [MeasureTheory.Measure.hausdorffMeasure_smul₀ (by positivity) (inv_ne_zero hr.ne') s]
      congr 1
      simp only [nnnorm_inv, NNReal.rpow_ofNat, inv_pow]
      ext : 1; simp [sup_of_le_left, hr.le]
    rw [h_map_scale, MeasureTheory.Measure.map_smul]
    erw [Isometry.map_hausdorffMeasure (IsometryEquiv.isometry (IsometryEquiv.addRight x₀))]
    congr 1
    have : Set.range (⇑(IsometryEquiv.addRight x₀)) = Set.univ :=
      Set.range_eq_univ.mpr (IsometryEquiv.addRight x₀).surjective
    rw [this, MeasureTheory.Measure.restrict_univ]
    simp_all only [Homeomorph.smulOfNeZero_apply, EquivLike.range_eq_univ, e_affine, e_scale, e_trans];rfl
    simp_all only [Homeomorph.smulOfNeZero_apply, Nat.ofNat_nonneg, true_or, e_affine, e_scale, e_trans]

  have h_cov : ∫ (x : E) in sphere x₀ r, u x ∂(MeasureTheory.Measure.map e_affine surfaceArea) = ∫ (y : E) in e_affine ⁻¹' (sphere x₀ r), u (e_affine y) ∂surfaceArea := by
    rw [MeasureTheory.Measure.restrict_map e_affine.measurableEmbedding.measurable isClosed_sphere.measurableSet, e_affine.measurableEmbedding.integral_map]

  rw [h_measure_scale, h_domain, MeasureTheory.Measure.restrict_smul, MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (by positivity)] at h_cov
  rw [show (fun y ↦ u (e_affine y)) = (fun y ↦ u (x₀ + r • y)) by ext y; exact congrArg u (add_comm (r • y) x₀)] at h_cov
  rw [← h_cov, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul]

lemma integral_ball_polar (R : ℝ) (f : E → ℝ) :
    ∫ y in Metric.ball (0 : E) R, f y =
    ∫ r in Set.Ioo 0 R, ∫ y in sphere (0 : E) r, f y ∂surfaceArea := by
  sorry

lemma integral_closedBall_translation (u : E → ℝ) (x₀ : E) (R : ℝ) :
    ∫ x in Metric.closedBall x₀ R, u x = ∫ y in Metric.closedBall (0 : E) R, u (x₀ + y) := by
  let e : E ≃ₜ E := Homeomorph.addLeft x₀
  have h_domain : e ⁻¹' Metric.closedBall x₀ R = Metric.closedBall (0 : E) R := by
    ext y; simp [e, Metric.mem_closedBall, dist_eq_norm]
  have h_measure : volume = Measure.map e volume :=
    (Measure.IsAddLeftInvariant.map_add_left_eq_self x₀).symm
  change ∫ x, u x ∂(volume.restrict (Metric.closedBall x₀ R)) = _
  rw [h_measure, MeasureTheory.Measure.restrict_map e.measurableEmbedding.measurable isClosed_closedBall.measurableSet,
    e.measurableEmbedding.integral_map, h_domain]
  exact congrFun (congrArg integral (congrFun (congrArg Measure.restrict h_measure) (closedBall 0 R))) fun x ↦ u (e x)

lemma integral_sphere_translation (u : E → ℝ) (x₀ : E) :
    ∀ r, ∫ x in sphere x₀ r, u x ∂surfaceArea = ∫ y in sphere (0 : E) r, u (x₀ + y) ∂surfaceArea := by
  intro r
  let e : E ≃ₜ E := Homeomorph.addLeft x₀
  have h_domain : e ⁻¹' sphere x₀ r = sphere (0 : E) r := by ext y; simp [e]
  have h_measure : Measure.map e surfaceArea = surfaceArea := by
    erw [Isometry.map_hausdorffMeasure (IsometryEquiv.addLeft x₀).isometry, e.surjective.range_eq, Measure.restrict_univ]; rfl
    simp_all only [Homeomorph.coe_addLeft, preimage_add_sphere, sub_self, Nat.ofNat_nonneg, true_or, e]
  change ∫ x, u x ∂(surfaceArea.restrict (sphere x₀ r)) = _
  rw [← h_measure, Measure.restrict_map e.measurableEmbedding.measurable isClosed_sphere.measurableSet,
    e.measurableEmbedding.integral_map, h_domain]
  exact congrFun (congrArg integral (congrFun (congrArg Measure.restrict (id (Eq.symm h_measure))) (sphere 0 r))) fun x ↦ u (e x)

lemma integral_closedBall_eq_ball (u : E → ℝ) (x₀ : E) (R : ℝ) :
    ∫ y in Metric.closedBall (0 : E) R, u (x₀ + y) = ∫ y in Metric.ball (0 : E) R, u (x₀ + y) := by
  have h_symm : (Metric.closedBall (0 : E) R : Set E) =ᶠ[ae volume] Metric.ball (0 : E) R := by
    refine MeasureTheory.ae_eq_set.mpr ⟨measure_mono_null (fun _ ⟨h1, h2⟩ ↦ le_antisymm h1 (not_lt.mp h2)) (volume_sphere 0 R), ?_⟩
    rw [Set.sdiff_eq_empty.mpr Metric.ball_subset_closedBall]
    exact measure_empty
  rw [MeasureTheory.Measure.restrict_congr_set h_symm]

lemma integral_closedBall_polar (u : E → ℝ) (x₀ : E) (R : ℝ) :
    ∫ x in Metric.closedBall x₀ R, u x = ∫ r in Set.Ioo 0 R, ∫ x in sphere x₀ r, u x ∂surfaceArea := by
  rw [integral_closedBall_translation u x₀ R, integral_closedBall_eq_ball u x₀ R, integral_ball_polar R (fun y ↦ u (x₀ + y))]
  congr 1; ext r; exact (integral_sphere_translation u x₀ r).symm

lemma volume_eq_integral_surfaceArea (x₀ : E) (R : ℝ) :
  (volume (Metric.closedBall x₀ R)).toReal = ∫ r in Set.Ioo 0 R, (surfaceArea (sphere x₀ r)).toReal := by
  sorry

lemma integral_Ioo_surfaceArea_eval (u : E → ℝ) (x₀ : E) (R : ℝ) :
    ∫ r in Set.Ioo 0 R, (surfaceArea (sphere x₀ r)).toReal * u x₀ = (volume (Metric.closedBall x₀ R)).toReal * u x₀ := by
  rw [volume_eq_integral_surfaceArea x₀ R, ← MeasureTheory.integral_mul_const]

/-!
### Spherical Means and Limits
-/

lemma averaging_lemma_spherical (R₀ : ℝ) (hR₀ : 0 < R₀)
    (phi : E → ℝ)
    (h_cont : ContinuousOn phi (Metric.ball 0 R₀)) :
    Filter.Tendsto (fun r => (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, phi x ∂surfaceArea) (𝓝[>] 0) (𝓝 (phi 0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε

  have h_phi_0_identity : ∀ r > 0, phi 0 = (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, phi 0 ∂surfaceArea := fun r hr ↦ by
    rw [setIntegral_const]
    unfold Measure.real
    have h_area : (surfaceArea (sphere 0 r)).toReal = 4 * π * r^2 := by
      rw [← surface_area_sphere_three_dim r hr, setIntegral_const]; simp_all [gt_iff_lt, smul_eq_mul, mul_one]; rfl
    rw [h_area, smul_eq_mul]
    have h_ne : 4 * π * r ^ 2 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) Real.pi_ne_zero) (pow_ne_zero 2 hr.ne')
    field_simp [h_ne]

  obtain ⟨δ₁, hδ₁_pos, hδ₁_cont⟩ := Metric.continuousAt_iff.mp (h_cont.continuousAt (isOpen_ball.mem_nhds (Metric.mem_ball_self hR₀))) ε hε
  use min δ₁ R₀, lt_min hδ₁_pos hR₀
  intro r hr_pos hr_dist
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hr_pos] at hr_dist

  have hr_lt_R₀ : r < R₀ := hr_dist.trans_le (min_le_right δ₁ R₀)
  have h_c_pos : 0 < 1 / (4 * π * r^2) := one_div_pos.mpr (mul_pos (mul_pos (by norm_num) pi_pos) (pow_pos hr_pos 2))

  calc
    dist ((1 / (4 * π * r^2)) * ∫ x in sphere 0 r, phi x ∂surfaceArea) (phi 0)
      = abs ((1 / (4 * π * r^2)) * ∫ x in sphere 0 r, (phi x - phi 0) ∂surfaceArea) := by
        conv_lhs => rw [h_phi_0_identity r hr_pos]
        rw [dist_eq_norm, Real.norm_eq_abs, ← mul_sub, ← integral_sub]
        · have h_subset : sphere (0 : E) r ⊆ ball (0 : E) R₀ := fun x hx ↦ by
            rw [mem_sphere] at hx
            exact mem_ball.mpr (hx ▸ hr_lt_R₀)
          have h_cont_sphere : ContinuousOn phi (sphere (0 : E) r) := h_cont.mono h_subset
          haveI : IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) r)) := isFiniteMeasure_sphere r hr_pos
          obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) r).bddAbove_image h_cont_sphere.norm
          refine MeasureTheory.Integrable.mono (integrable_const C) (ContinuousOn.aestronglyMeasurable h_cont_sphere isClosed_sphere.measurableSet) ?_
          rw [MeasureTheory.ae_restrict_iff' isClosed_sphere.measurableSet]
          exact Eventually.of_forall fun x hx ↦ by rw [Real.norm_eq_abs]; exact (hC (Set.mem_image_of_mem _ hx)).trans (le_abs_self C)
        · haveI : IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) r)) := isFiniteMeasure_sphere r hr_pos
          exact integrable_const (phi 0)
    _ ≤ (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, abs (phi x - phi 0) ∂surfaceArea := by
        rw [abs_mul, abs_of_pos h_c_pos]
        exact mul_le_mul_of_nonneg_left (by simp_rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _) h_c_pos.le
    _ < (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, ε ∂surfaceArea := by
        have h_finite_meas : surfaceArea (sphere 0 r) < ⊤ := measure_sphere_lt_top _ hr_pos
        haveI : IsFiniteMeasure (surfaceArea.restrict (sphere 0 r)) := ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact h_finite_meas⟩
        have h_int_rhs : IntegrableOn (fun _ ↦ ε) (sphere 0 r) surfaceArea := integrable_const ε
        have h_cont_abs : ContinuousOn (fun x ↦ abs (phi x - phi 0)) (sphere 0 r) := ContinuousOn.abs (ContinuousOn.sub (h_cont.mono (fun x hx ↦ by rw [mem_sphere] at hx; exact mem_ball.mpr (hx.symm ▸ hr_lt_R₀))) continuousOn_const)
        obtain ⟨C, hC⟩ := (isCompact_sphere 0 r).exists_bound_of_continuousOn h_cont_abs
        have h_int_lhs : IntegrableOn (fun x ↦ abs (phi x - phi 0)) (sphere 0 r) surfaceArea := by
          obtain ⟨C, hC⟩ := (isCompact_sphere 0 r).exists_bound_of_continuousOn h_cont_abs
          apply Integrable.of_bound (C := C)
          · exact h_cont_abs.aestronglyMeasurable isClosed_sphere.measurableSet
          · filter_upwards [self_mem_ae_restrict isClosed_sphere.measurableSet] with x hx
            exact hC x hx
        have h_meas_pos : 0 < surfaceArea (sphere 0 r) := by
          have h_area : (surfaceArea (sphere 0 r)).toReal = 4 * π * r^2 := by rw [← surface_area_sphere_three_dim r hr_pos, setIntegral_const]; simp_all; rfl
          have h_pos : 0 < 4 * π * r^2 := mul_pos (mul_pos (by norm_num) pi_pos) (pow_pos hr_pos 2)
          have : 0 < (surfaceArea (sphere 0 r)).toReal := h_area ▸ h_pos
          exact ENNReal.toReal_pos_iff.mp this |>.1.bot_lt
        have h_bound : ∀ x ∈ sphere 0 r, abs (phi x - phi 0) < ε := fun x hx ↦ by
          rw [mem_sphere] at hx
          have h_dist : dist x 0 < δ₁ := hx ▸ hr_dist.trans_le (min_le_left δ₁ R₀)
          have := hδ₁_cont h_dist
          rwa [Real.dist_eq] at this
        have h_integral_lt : ∫ x in sphere 0 r, abs (phi x - phi 0) ∂surfaceArea < ∫ x in sphere 0 r, ε ∂surfaceArea := by
          rw [← sub_pos, ← integral_sub h_int_rhs h_int_lhs]
          have h_nonneg : 0 ≤ᵐ[surfaceArea.restrict (sphere 0 r)] (fun x ↦ ε - abs (phi x - phi 0)) := by filter_upwards [self_mem_ae_restrict isClosed_sphere.measurableSet] with x hx using sub_nonneg.mpr (h_bound x hx).le
          rw [integral_pos_iff_support_of_nonneg_ae h_nonneg (Integrable.sub h_int_rhs h_int_lhs), Measure.restrict_apply' isClosed_sphere.measurableSet]
          rw [Set.inter_eq_right.mpr (fun x hx ↦ Function.mem_support.mpr (sub_pos.mpr (h_bound x hx)).ne')]
          exact h_meas_pos
        exact mul_lt_mul_of_pos_left h_integral_lt h_c_pos
    _ = ε := by
        have h_denom : 4 * π * r^2 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) (pow_ne_zero 2 hr_pos.ne')
        calc (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, ε ∂surfaceArea
          _ = ε * ((1 / (4 * π * r^2)) * ∫ x in sphere 0 r, 1 ∂surfaceArea) := by simp; ring
          _ = ε := by
                rw [surface_area_sphere_three_dim r hr_pos]
                field_simp [h_denom]
                ring_nf
                aesop

lemma averaging_lemma_spherical_translated (R₀ : ℝ) (hR₀ : 0 < R₀)
    (phi : E → ℝ) (x₀ : E)
    (h_cont : ContinuousOn phi (Metric.ball x₀ R₀)) :
    Filter.Tendsto (fun r ↦ (1 / (4 * π * r^2)) * ∫ x in sphere x₀ r, phi x ∂surfaceArea) (𝓝[>] 0) (𝓝 (phi x₀)) := by
  let psi := fun x ↦ phi (x + x₀)
  have h_cont_psi : ContinuousOn psi (Metric.ball 0 R₀) :=
    ContinuousOn.comp h_cont (continuous_add_const x₀).continuousOn (fun x hx ↦ by simpa [Metric.mem_ball, dist_eq_norm] using hx)

  have h_integral_eq : ∀ r, ∫ x in sphere x₀ r, phi x ∂surfaceArea = ∫ x in sphere 0 r, psi x ∂surfaceArea := fun r ↦ by
    let g : E ≃ᵢ E := IsometryEquiv.addRight x₀
    have hg_surj : Function.Surjective g := fun y ↦ ⟨y - x₀, sub_add_cancel y x₀⟩
    have hg_emb : MeasurableEmbedding g := (Homeomorph.addRight x₀).measurableEmbedding
    have h_map : MeasureTheory.Measure.map g surfaceArea = surfaceArea := by
      erw [Isometry.map_hausdorffMeasure (isometry_add_right x₀) (Or.inr hg_surj)]
      have : Set.range (fun x ↦ x + x₀) = Set.univ := Set.range_eq_univ.mpr hg_surj
      rw [this, MeasureTheory.Measure.restrict_univ]
      simp_all only [psi, g]
      rfl
    rw [← h_map]
    change ∫ x, phi x ∂((MeasureTheory.Measure.map g surfaceArea).restrict (sphere x₀ r)) = _
    rw [MeasureTheory.Measure.restrict_map hg_emb.measurable isClosed_sphere.measurableSet]
    rw [hg_emb.integral_map, h_map, show g ⁻¹' (sphere x₀ r) = sphere 0 r by ext x; simp [g]]
    rfl

  have h_fun_eq : (fun r ↦ (1 / (4 * π * r^2)) * ∫ x in sphere x₀ r, phi x ∂surfaceArea) = (fun r ↦ (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, psi x ∂surfaceArea) := by ext r; rw [h_integral_eq r]

  rw [show phi x₀ = psi 0 by dsimp [psi]; rw [zero_add], h_fun_eq]
  exact averaging_lemma_spherical R₀ hR₀ psi h_cont_psi

lemma continuousOn_spherical_mean (u : E → ℝ) (x₀ : E) (R : ℝ)
    (h_cont_u : ContinuousOn u (Metric.closedBall x₀ R)) :
    ContinuousOn (fun r ↦ 1 / (4 * π * r ^ 2) * ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea) (Set.Ioc 0 R) := by

  have h_phi_alt : Set.EqOn (fun r ↦ 1 / (4 * π * r ^ 2) * ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea)
      (fun r ↦ (1 / (4 * π)) * ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea) (Set.Ioc 0 R) := by
    intro r hr
    have hr_sq_ne_zero : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.1.ne'
    dsimp only
    rw [integral_sphere_change_vars x₀ r hr.1 u]
    calc 1 / (4 * π * r ^ 2) * (r ^ 2 * ∫ (y : E) in sphere 0 1, u (x₀ + r • y) ∂surfaceArea)
      _ = (1 / (4 * π * r ^ 2) * r ^ 2) * ∫ (y : E) in sphere 0 1, u (x₀ + r • y) ∂surfaceArea := by rw [mul_assoc];field_simp
      _ = 1 / (4 * π) * ∫ (y : E) in sphere 0 1, u (x₀ + r • y) ∂surfaceArea := by
        congr 1
        calc 1 / (4 * π * r ^ 2) * r ^ 2 = 1 / (4 * π) * (1 / r ^ 2 * r ^ 2) := by ring
        _ = 1 / (4 * π) := by rw [one_div_mul_cancel hr_sq_ne_zero, mul_one]

  refine ContinuousOn.congr ?_ h_phi_alt
  apply ContinuousOn.mul continuousOn_const

  have h_param_integral : ContinuousOn (fun r ↦ ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea) (Set.Ioc 0 R) := by
    intro r hr

    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ Metric.closedBall x₀ R, ‖u x‖ ≤ M := by
      have h_compact := isCompact_closedBall x₀ R
      obtain ⟨M, hM_bdd⟩ := (h_compact.image_of_continuousOn h_cont_u.norm).bddAbove
      exact ⟨M, fun x hx ↦ hM_bdd (Set.mem_image_of_mem _ hx)⟩

    have h_cont_integrand : ∀ᵐ y ∂(surfaceArea.restrict (sphere 0 1)), ContinuousWithinAt (fun r' ↦ u (x₀ + r' • y)) (Set.Ioc 0 R) r := by
      rw [ae_restrict_iff' isClosed_sphere.measurableSet]
      refine Eventually.of_forall (fun y hy ↦ ?_)
      have h_mapsTo : Set.MapsTo (fun r' ↦ x₀ + r' • y) (Set.Ioc 0 R) (Metric.closedBall x₀ R) := fun r' hr' ↦ by
        simpa [dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp hy, Real.norm_of_nonneg hr'.1.le] using hr'.2
      exact ContinuousWithinAt.comp (h_cont_u _ (h_mapsTo hr)) (continuous_const.add (continuous_id.smul continuous_const)).continuousWithinAt h_mapsTo

    have h_meas_integrand : ∀ r' ∈ Set.Ioc 0 R, AEStronglyMeasurable (fun y ↦ u (x₀ + r' • y)) (surfaceArea.restrict (sphere 0 1)) := fun r' hr' ↦ by
      have h_mapsTo_y : Set.MapsTo (fun y ↦ x₀ + r' • y) (sphere 0 1) (Metric.closedBall x₀ R) := fun y hy ↦ by
        simpa [dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp hy, Real.norm_of_nonneg hr'.1.le] using hr'.2
      exact (ContinuousOn.comp h_cont_u (continuous_const.add (continuous_id.const_smul r')).continuousOn h_mapsTo_y).aestronglyMeasurable isClosed_sphere.measurableSet

    have h_bound_integrable : IntegrableOn (fun _ ↦ M) (sphere 0 1) surfaceArea := by
      haveI : IsFiniteMeasure (surfaceArea.restrict (sphere 0 1)) := by
        refine ⟨lt_top_iff_ne_top.mpr (fun h_top ↦ ?_)⟩
        have h_zero : (surfaceArea (sphere 0 1)).toReal = 0 := by simp_all
        rw [unit_sphere_area_hausdorff] at h_zero
        linarith [show (0 : ℝ) < 4 * π by positivity]
      exact integrable_const M

    have h_dominate : ∀ r' ∈ Set.Ioc 0 R, ∀ᵐ y ∂(surfaceArea.restrict (sphere 0 1)), ‖u (x₀ + r' • y)‖ ≤ M := fun r' hr' ↦ by
      rw [ae_restrict_iff' isClosed_sphere.measurableSet]
      exact Eventually.of_forall (fun y hy ↦ hM _ (by simpa [dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp hy, Real.norm_of_nonneg hr'.1.le] using hr'.2))

    exact continuousWithinAt_of_dominated
      (eventually_nhdsWithin_of_forall h_meas_integrand)
      (eventually_nhdsWithin_of_forall h_dominate)
      h_bound_integrable
      h_cont_integrand

  exact h_param_integral

lemma spherical_mean_eqOn (u : E → ℝ) (x₀ : E) (R : ℝ) :
    Set.EqOn (fun r ↦ 1 / (4 * π * r ^ 2) * ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea)
      (fun r ↦ (1 / (4 * π)) * ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea) (Set.Ioo 0 R) := by
  intro r hr
  show 1 / (4 * π * r ^ 2) * ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea =
       1 / (4 * π) * ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea
  rw [integral_sphere_change_vars x₀ r hr.1 u]
  have hr_ne : r ≠ 0 := hr.1.ne'
  field_simp

/-!
### Gradient and Trace Integral
-/

lemma trace_integral_swap (G : E → E →L[ℝ] E) (hG : Integrable G) :
  LinearMap.trace ℝ E ((∫ y, G y).toLinearMap) = ∫ y, LinearMap.trace ℝ E (G y).toLinearMap := by
  let trace_clm : (E →L[ℝ] E) →L[ℝ] ℝ := {
    toFun := fun L => LinearMap.trace ℝ E L.toLinearMap
    map_add' := fun L₁ L₂ => map_add (LinearMap.trace ℝ E) L₁.toLinearMap L₂.toLinearMap
    map_smul' := fun c L => map_smul (LinearMap.trace ℝ E) c L.toLinearMap
    cont := continuous_trace
  }
  exact (trace_clm.integral_comp_comm hG).symm

lemma gradient_integral_of_dominated (F : E → E → ℝ) (x : E) (bound : E → ℝ)
  (hε : ∃ ε > 0, ∀ᵐ y, ∀ x' ∈ Metric.ball x ε, ‖fderiv ℝ (fun x'' => F x'' y) x'‖ ≤ bound y)
  (h_bound_int : Integrable bound volume)
  (hF_int : Integrable (fun y => F x y) volume)
  (hF_meas : ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (fun y => F x' y) volume)
  (hF'_meas : AEStronglyMeasurable (fun y => fderiv ℝ (fun x'' => F x'' y) x) volume)
  (h_diff : ∀ᵐ y, ∀ x' ∈ Metric.ball x (hε.choose), HasFDerivAt (fun x'' => F x'' y)
              (fderiv ℝ (fun x'' => F x'' y) x') x') :
  gradient (fun x' => ∫ y, F x' y) x = ∫ y, gradient (fun x' => F x' y) x := by
  unfold gradient
  rw [(hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds x hε.choose_spec.1) hF_meas hF_int
    hF'_meas hε.choose_spec.2 h_bound_int h_diff).fderiv]
  exact riesz_integral_swap (fun y => fderiv ℝ (fun x' => F x' y) x)
    (h_bound_int.mono' hF'_meas (hε.choose_spec.2.mono (fun y hy => hy x (Metric.mem_ball_self hε.choose_spec.1))))

lemma integral_squeeze_bound (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (u : E → ℝ) (n : E → E) (x₀ : E)
  (h_grad_bound : ∃ (M : ℝ) (ε₀ : ℝ), 0 < ε₀ ∧ ∀ ε ∈ Set.Ioc 0 ε₀,
    ∀ x ∈ Metric.sphere x₀ ε, ‖⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ‖ ≤ M)
  (h_G_bound : ∃ (C : ℝ) (ε₀ : ℝ), 0 < ε₀ ∧ ∀ ε ∈ Set.Ioc 0 ε₀,
    ∀ x ∈ Metric.sphere x₀ ε, ‖G x x₀‖ ≤ C / ε)
  (h_ball_sub_omega_bound : ∃ (R : ℝ), 0 < R ∧ ∀ ε ∈ Set.Ioc 0 R, Metric.closedBall x₀ ε ⊆ Ω)
  (h_sphere_area : ∀ ε > 0, surfaceArea (Metric.sphere x₀ ε) = ENNReal.ofReal (4 * Real.pi * ε ^ 2)):
  ∃ (K : ℝ) (ε₀ : ℝ), 0 < ε₀ ∧ ∀ ε ∈ Set.Ioc 0 ε₀,
    ‖∫ x in Metric.sphere x₀ ε, G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ ∂surfaceArea‖ ≤ K * ε := by
  obtain ⟨M, ε₁, hε₁_pos, hM_bound⟩ := h_grad_bound
  obtain ⟨C, ε₂, hε₂_pos, hC_bound⟩ := h_G_bound
  obtain ⟨R, hR_pos, hR_bound⟩ := h_ball_sub_omega_bound
  exact ⟨C * M * 4 * Real.pi, min (min ε₁ ε₂) R, lt_min (lt_min hε₁_pos hε₂_pos) hR_pos, fun ε hε => by
    have h_pt : ∀ x ∈ Metric.sphere x₀ ε, ‖G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ‖ ≤ (C * M) / ε :=
      fun x hx => integrand_pointwise_bound G u n x₀ x ε C M
        (hC_bound ε ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩ x hx)
        (hM_bound ε ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩ x hx)
    have h_int := MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae' (by rw [h_sphere_area ε hε.1]; exact ENNReal.ofReal_lt_top) (Eventually.of_forall h_pt)
    unfold MeasureTheory.Measure.real at h_int
    rw [h_sphere_area ε hε.1, ENNReal.toReal_ofReal (by positivity)] at h_int
    calc
      ‖∫ x in Metric.sphere x₀ ε, G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ ∂surfaceArea‖
        ≤ ((C * M) / ε) * (4 * Real.pi * ε ^ 2) := h_int
      _ = ((C * M) / ε) * ε * (4 * Real.pi * ε) := by ring
      _ = C * M * (4 * Real.pi * ε) := by rw [div_mul_cancel₀ _ (ne_of_gt hε.1)]
      _ = C * M * 4 * Real.pi * ε := by ring⟩

/-!
### Boundary Integrals and Transformations
-/

lemma boundary_integral_rewrite (Ω : Set E) (u : E → ℝ) (n : E → E) (x₀ : E) (Φ : E → ℝ) :
  (∫ x in frontier Ω, (u x * ⟪n x, gradientWithin (fun y => Φ (y - x₀)) (closure Ω) x⟫ - Φ (x - x₀) * ⟪n x, gradientWithin u (closure Ω) x⟫) ∂surfaceArea) =
  - ∫ x in frontier Ω, (Φ (x - x₀) * ⟪gradientWithin u (closure Ω) x, n x⟫ - u x * ⟪gradientWithin (fun y => Φ (y - x₀)) (closure Ω) x, n x⟫) ∂surfaceArea := by
  rw [← integral_neg]
  exact setIntegral_congr_fun isClosed_frontier.measurableSet fun x _ => by simp_rw [real_inner_comm (n x)]; ring

lemma frontier_integral_const (Ω : Set E) [HasPDEDomain Ω] (u : E → ℝ) (n : E → E)
  (x₀ : E) (hx₀ : x₀ ∈ Ω) (Φ : E → ℝ) :
  ∀ᶠ ε in 𝓝[>] 0,
    (∫ x in frontier Ω, (Φ (x - x₀) * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫ - u x * ⟪gradientWithin (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫) ∂surfaceArea) =
    ∫ x in frontier Ω, (Φ (x - x₀) * ⟪gradientWithin u (closure Ω) x, n x⟫ - u x * ⟪gradientWithin (fun y => Φ (y - x₀)) (closure Ω) x, n x⟫) ∂surfaceArea := by
  filter_upwards [eventually_disjoint_frontier_closedBall HasPDEDomain.is_open hx₀] with ε h_disj
  exact setIntegral_congr_fun isClosed_frontier.measurableSet fun x hx => by
    rw [gradientWithin_frontier_excised_eq Ω u x₀ x ε (Set.disjoint_left.mp h_disj hx),
      gradientWithin_frontier_excised_eq Ω (fun y => Φ (y - x₀)) x₀ x ε (Set.disjoint_left.mp h_disj hx)]

lemma integrableOn_greens_f_frontier_within_gen (Ω : Set E) [HasPDEDomain Ω] (n_Omega : E → E)
    (x₀ : E) (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) (u v : E → ℝ)
    (h_bound : Bornology.IsBounded Ω) (h_area : surfaceArea (frontier Ω) ≠ ⊤)
    (hu : ContDiffOn ℝ 2 u (closure (Ω \ Metric.closedBall x₀ ε)))
    (hv : ContDiffOn ℝ 2 v (closure (Ω \ Metric.closedBall x₀ ε)))
    (hn_cont : ContinuousOn n_Omega (frontier Ω)) :
    IntegrableOn (fun x => v x * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n_Omega x⟫_ℝ -
      u x * ⟪gradientWithin v (closure (Ω \ Metric.closedBall x₀ ε)) x, n_Omega x⟫_ℝ) (frontier Ω) surfaceArea := by
  have h_front_sub : frontier Ω ⊆ closure (Ω \ Metric.closedBall x₀ ε) := fun x hx => by
    have h_uni := closure_mono (Set.subset_sdiff_union Ω (Metric.closedBall x₀ ε)) (frontier_subset_closure hx)
    rwa [closure_union, Metric.isClosed_closedBall.closure_eq, mem_union, or_iff_left (fun hb => notMem_of_mem_sdiff hx ((HasPDEDomain.is_open (s := Ω)).interior_eq.symm ▸ h_subset hb))] at h_uni
  exact integrableOn_of_continuousOn_compact_finite_measure
    (isCompact_of_isClosed_isBounded isClosed_frontier (h_bound.closure.subset frontier_subset_closure))
    isClosed_frontier.measurableSet (lt_top_iff_ne_top.mpr h_area)
    (((hv.continuousOn.mono h_front_sub).mul (ContinuousOn.inner
      ((contDiffOn_1_gradientWithin_continuousOn (hu.of_le (by norm_num))
        (annulus_has_pde_domain_gen Ω x₀ ε hε h_subset).unique_diff).mono h_front_sub) hn_cont)).sub
    ((hu.continuousOn.mono h_front_sub).mul (ContinuousOn.inner
      ((contDiffOn_1_gradientWithin_continuousOn (hv.of_le (by norm_num))
        (annulus_has_pde_domain_gen Ω x₀ ε hε h_subset).unique_diff).mono h_front_sub) hn_cont)))

lemma integral_boundary_sum (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (u v : E → ℝ) (n : E → E)
  (h_int_front : IntegrableOn (fun x ↦ u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (frontier Ω) surfaceArea)
  (h_int_sph_a : IntegrableOn (fun x ↦ u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere a ε) surfaceArea)
  (h_int_sph_b : IntegrableOn (fun x ↦ u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere b ε) surfaceArea) :
  ∫ x in frontier (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)),
    (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ -
     v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea =
  (∫ x in frontier Ω, (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea) +
  (∫ x in Metric.sphere a ε, (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea) +
  (∫ x in Metric.sphere b ε, (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea) := by
  rw [frontier_punctured_eq_union Ω a b ε hε h_disjoint ha_subset hb_subset,
    MeasureTheory.setIntegral_union (disjoint_frontier_union_sphere_a_sphere_b Ω a b ε hb_subset h_disjoint) (isCompact_sphere b ε).measurableSet (IntegrableOn.union h_int_front h_int_sph_a) h_int_sph_b,
    MeasureTheory.setIntegral_union (disjoint_frontier_sphere ha_subset) (isCompact_sphere a ε).measurableSet h_int_front h_int_sph_a]

lemma boundary_integrable_sphere {Ω : Set E} [HasPDEDomain Ω]
  {G : E → E → ℝ} {u : E → ℝ} {n : E → E} {x₀ : E} {ε : ℝ}
  (hε : 0 < ε)
  (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (hu_cont : ContinuousOn u (closure Ω))
  (hn_cont : ContinuousOn n (Metric.sphere x₀ ε))
  (h_grad_u_cont : ContinuousOn (fun x => gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x) (Metric.sphere x₀ ε))
  (hG_cont : ContinuousOn (fun x => G x x₀) (Metric.sphere x₀ ε))
  (h_grad_G_cont : ContinuousOn (fun x => gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x) (Metric.sphere x₀ ε)) :
  IntegrableOn (fun x => u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ -
    G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) (Metric.sphere x₀ ε) surfaceArea := by
  have h_cont_u : ContinuousOn u (Metric.sphere x₀ ε) :=
    hu_cont.mono (Metric.sphere_subset_closedBall.trans (h_subset.trans subset_closure))
  have h_cont_integrand : ContinuousOn (fun x => u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ - G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) (Metric.sphere x₀ ε) :=
    (h_cont_u.mul (h_grad_G_cont.inner hn_cont)).sub (hG_cont.mul (h_grad_u_cont.inner hn_cont))
  exact integrableOn_compact_surface_of_continuousOn
    (isCompact_sphere x₀ ε)
    (ne_of_lt (surfaceArea_sphere_lt_top x₀ hε))
    _ h_cont_integrand

lemma integrable_mul_inner_gradientWithin_normal
  (Ω : Set E)
  [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (u v : E → ℝ)
  (hu_diff : ContDiffOn ℝ 1 u (closure Ω))
  (hv_cont : ContinuousOn v (closure Ω))
  (n : E → E)
  (h_n_cont : ContinuousOn n (frontier Ω)) :
  IntegrableOn (fun x => v x * ⟪gradientWithin u (closure Ω) x, n x⟫_ℝ) (frontier Ω) surfaceArea := by
  have h_cont : ContinuousOn (fun x => ⟪v x • gradientWithin u (closure Ω) x, n x⟫_ℝ) (frontier Ω) :=
    ContinuousOn.inner ((smul_gradientWithin_continuousOn Ω u v hu_diff hv_cont).mono frontier_subset_closure) h_n_cont
  exact (funext fun x => (real_inner_smul_left (gradientWithin u (closure Ω) x) (n x) (v x)).symm) ▸
    integrableOn_frontier_of_continuousOn Ω h_bounded h_area _ h_cont

lemma integrable_harmonic_corrector_boundary
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (u H : E → ℝ)
  (hu_cont : ContinuousOn u (closure Ω))
  (hu_diff : ContDiffOn ℝ 1 u (closure Ω))
  (hH_cont : ContinuousOn H (closure Ω))
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω))
  (n : E → E)
  (h_cont_n : ContinuousOn n (frontier Ω)) :
  IntegrableOn (fun x => u x * ⟪n x, gradientWithin H (closure Ω) x⟫_ℝ - H x * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) (frontier Ω) surfaceArea := by
  have h_eq : (fun x => u x * ⟪n x, gradientWithin H (closure Ω) x⟫_ℝ - H x * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) =
    (fun x => u x * ⟪gradientWithin H (closure Ω) x, n x⟫_ℝ - H x * ⟪gradientWithin u (closure Ω) x, n x⟫_ℝ) := by
    ext x
    rw [real_inner_comm (n x), real_inner_comm (n x)]
  rw [h_eq]
  exact Integrable.sub
    (integrable_mul_inner_gradientWithin_normal Ω h_bounded h_area H u hH_diff hu_cont n h_cont_n)
    (integrable_mul_inner_gradientWithin_normal Ω h_bounded h_area u H hu_diff hH_cont n h_cont_n)

/-!
### General Domain Integrability
-/

lemma inv_norm_mul_laplacian_integrable (φ : E → ℝ) (h_smooth : ContDiff ℝ ⊤ φ) (h_supp : HasCompactSupport φ) :
  Integrable (fun x => (1 / ‖x‖) * laplacian φ x) volume := by
  obtain ⟨C, hC⟩ := ((laplacian_compact_support φ h_supp).isCompact.image (laplacian_continuous φ h_smooth).norm).bddAbove
  obtain ⟨R₀, hR₀⟩ := h_supp.isBounded.subset_ball (0 : E)
  let R := max R₀ 1
  rw [← integrableOn_univ, ← union_compl_self (Metric.ball (0 : E) R)]
  refine IntegrableOn.union (Integrable.mono' ((inv_norm_integrableOn_ball R (by positivity)).norm.mul_const (max 0 C)) ?_ ?_) ?_
  · exact (inv_norm_integrableOn_ball R (by positivity)).aestronglyMeasurable.mul (laplacian_continuous φ h_smooth).aestronglyMeasurable.restrict
  · refine Eventually.of_forall fun x => by
      rw [norm_mul]
      by_cases hx : laplacian φ x = 0
      · rw [hx, norm_zero]
        exact mul_le_mul_of_nonneg_left (le_max_left 0 C) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_left ((hC (mem_image_of_mem _ (subset_closure hx))).trans (le_max_right 0 C)) (norm_nonneg _)
  · refine IntegrableOn.congr_fun (integrable_zero E ℝ _) (fun x hx => ?_) measurableSet_ball.compl;
    rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hx (hR₀.trans (Metric.ball_subset_ball (le_max_left R₀ 1)) h)), mul_zero]; rfl

lemma integrable_inner_gradient_of_c1
  (Ω : Set E)
  [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (u v : E → ℝ)
  (hu_diff : ContDiffOn ℝ 1 u (closure Ω))
  (hv_diff : ContDiffOn ℝ 1 v (closure Ω)) :
  IntegrableOn (fun x => ⟪gradient u x, gradient v x⟫_ℝ) Ω := by
  have h_grad_u_cont : ContinuousOn (gradientWithin u (closure Ω)) (closure Ω) :=
    continuousOn_gradientWithin_of_contDiffOn h_domain.unique_diff u hu_diff
  have h_grad_v_cont : ContinuousOn (gradientWithin v (closure Ω)) (closure Ω) :=
    continuousOn_gradientWithin_of_contDiffOn h_domain.unique_diff v hv_diff
  have h_int_omega_within : IntegrableOn (fun x => ⟪gradientWithin u (closure Ω) x, gradientWithin v (closure Ω) x⟫_ℝ) Ω :=
    ((ContinuousOn.inner h_grad_u_cont h_grad_v_cont).integrableOn_compact
      h_bounded.isCompact_closure).mono_set subset_closure
  have h_grad_eq : ∀ w x (hx : x ∈ Ω), gradient w x = gradientWithin w (closure Ω) x := fun w x hx =>
    congrArg (InnerProductSpace.toDual ℝ E).symm (fderivWithin_of_mem_nhds (Filter.mem_of_superset (h_domain.is_open.mem_nhds hx) subset_closure)).symm
  exact h_int_omega_within.congr_fun (fun x hx => by simp_rw [← h_grad_eq u x hx, ← h_grad_eq v x hx]) h_domain.is_open.measurableSet

lemma integrable_mul_laplacian_of_c2
  (Ω : Set E)
  [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (u v : E → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hv_cont : ContinuousOn v (closure Ω)) :
  IntegrableOn (fun x => v x * laplacianWithin u (closure Ω) x) Ω :=
  ((hv_cont.mul (laplacianWithin_continuousOn Ω u hu_diff)).integrableOn_compact
    h_bounded.isCompact_closure).mono_set subset_closure

/-!
### Punctured Domains and Flux
-/

lemma integrableOn_H_grad_sphere (Ω : Set E) [HasPDEDomain Ω] (H u : E → ℝ) (x₀ : E) (ε ε₀ : ℝ)
  (hε : ε ∈ Set.Ioc 0 ε₀) (h_ball_subset_hyp : Metric.closedBall x₀ ε₀ ⊆ Ω)
  (hu_cont : ContinuousOn u (closure Ω)) (hH_diff : ContDiffOn ℝ 1 H (closure Ω)) :
  MeasureTheory.IntegrableOn (fun x => u x * ⟪gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ) (Metric.sphere x₀ ε) surfaceArea := by
  have h_cont : ContinuousOn (fun x => u x * ⟪gradientWithin H (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ) (Metric.sphere x₀ ε) :=
    (hu_cont.mono (((Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_closedBall hε.2)).trans h_ball_subset_hyp).trans subset_closure)).mul
      (((continuousOn_gradientWithin_H_excised Ω H x₀ ε ε₀ hε h_ball_subset_hyp hH_diff).mono
        (sphere_subset_closure_annulus Ω x₀ ε ε₀ hε h_ball_subset_hyp)).inner
        (((continuous_id.sub continuous_const).const_smul (-(1 / ε))).continuousOn))
  exact integrableOn_compact_surface_of_continuousOn
    (isCompact_sphere x₀ ε)
    (ne_of_lt (surfaceArea_sphere_lt_top x₀ hε.1))
    _ h_cont

lemma limit_sphere_H_grad_zero (Ω : Set E) [HasPDEDomain Ω]
  (H u : E → ℝ) (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (hu_cont : ContinuousOn u (closure Ω))
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω)) :
  Filter.Tendsto
    (fun ε => ∫ x in Metric.sphere x₀ ε,
      u x * ⟪gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea)
    (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨ε₀, hε₀_pos, h_ball_subset⟩ := exists_pos_closedBall_subset_of_isOpen HasPDEDomain.is_open hx₀
  obtain ⟨M, hM_pos, hM_bound⟩ := exists_H_grad_bound Ω H u x₀ ε₀ h_ball_subset hu_cont hH_diff
  exact squeeze_zero_norm'
    (Filter.eventually_of_mem (Ioc_mem_nhdsGT hε₀_pos) fun ε hε => by
      calc
        ‖∫ x in Metric.sphere x₀ ε, u x * ⟪gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea‖
          ≤ ∫ x in Metric.sphere x₀ ε, ‖u x * ⟪gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ‖ ∂surfaceArea :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in Metric.sphere x₀ ε, M ∂surfaceArea :=
            MeasureTheory.integral_mono_ae (integrableOn_H_grad_sphere Ω H u x₀ ε ε₀ hε h_ball_subset hu_cont hH_diff).norm
              (integrableOn_compact_surface_of_continuousOn (isCompact_sphere x₀ ε) (ne_of_lt (surfaceArea_sphere_lt_top x₀ hε.1)) (fun _ => M) continuousOn_const)
              (ae_restrict_of_forall_mem isClosed_sphere.measurableSet fun x hx => pointwise_H_grad_bound Ω H u x₀ ε ε₀ hε h_ball_subset hH_diff M hM_bound x hx)
        _ = surfaceArea.real (Metric.sphere x₀ ε) • M := by exact setIntegral_const M
        _ = M * (surfaceArea (Metric.sphere x₀ ε)).toReal := by
            unfold MeasureTheory.Measure.real
            rw [smul_eq_mul, mul_comm]
        _ = M * (ENNReal.ofReal (4 * Real.pi * ε ^ 2)).toReal := by rw [sphere_surface_area x₀ ε hε.1]
        _ = M * (4 * Real.pi * ε ^ 2) := by rw [ENNReal.toReal_ofReal (by positivity)])
    (limit_area_bound_zero M)

lemma vol_int_zero_punctured (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (u v : E → ℝ)
  (hu_harm : IsHarmonic u (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)))
  (hv_harm : IsHarmonic v (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) :
  ∫ x in (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)),
  (u x * laplacianWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x -
   v x * laplacianWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) = 0 := by
  have h_open : IsOpen (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) :=
    IsOpen.sdiff HasPDEDomain.is_open (IsClosed.union Metric.isClosed_closedBall Metric.isClosed_closedBall)
  apply Eq.trans (b := ∫ x in Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε), (0 : ℝ))
  · refine setIntegral_congr_fun h_open.measurableSet fun x hx ↦ ?_
    simp [laplacianWithin_closure_eq_laplacian u _ h_open x hx,
      laplacianWithin_closure_eq_laplacian v _ h_open x hx,
      hu_harm x hx, hv_harm x hx]
  · exact setIntegral_eq_zero_of_forall_eq_zero fun x ↦ congrFun rfl

lemma integrable_flux_diff_sphere (Ω : Set E) [HasPDEDomain Ω] (a b c : E) (ε : ℝ)
  (u v : E → ℝ) (n : E → E)
  (h_finite_area : surfaceArea (Metric.sphere c ε) ≠ ⊤)
  (h_cont_u : ContinuousOn u (Metric.sphere c ε))
  (h_cont_v : ContinuousOn v (Metric.sphere c ε))
  (h_cont_n : ContinuousOn n (Metric.sphere c ε))
  (h_cont_grad_u : ContinuousOn (fun x ↦ gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere c ε))
  (h_cont_grad_v : ContinuousOn (fun x ↦ gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere c ε)) :
  IntegrableOn (fun x ↦ u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere c ε) surfaceArea := by
  have h_compact : IsCompact (Metric.sphere c ε) := isCompact_sphere c ε
  have h_cont_integrand : ContinuousOn (fun x ↦ u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere c ε) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.mul h_cont_u
      apply ContinuousOn.inner h_cont_grad_v h_cont_n
    · apply ContinuousOn.mul h_cont_v
      apply ContinuousOn.inner h_cont_grad_u h_cont_n
  exact integrableOn_compact_surface_of_continuousOn h_compact h_finite_area _ h_cont_integrand

lemma integrable_flux_diff_frontier (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (u v : E → ℝ) (n : E → E)
  (hu_zero : ∀ x ∈ frontier Ω, u x = 0)
  (hv_zero : ∀ x ∈ frontier Ω, v x = 0) :
  IntegrableOn (fun x ↦ u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (frontier Ω) surfaceArea := by
  refine Integrable.congr (integrable_zero E ℝ (surfaceArea.restrict (frontier Ω))) (Filter.EventuallyEq.symm ?_)
  refine (ae_restrict_iff' isClosed_frontier.measurableSet).mpr (Filter.Eventually.of_forall fun x hx => by
    simp_rw [hu_zero x hx, hv_zero x hx]
    ring_nf; aesop)

lemma integrable_flux_diff_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (u v : E → ℝ) (n : E → E)
  (h_finite_area : surfaceArea (Metric.sphere a ε) ≠ ⊤)
  (h_cont_u : ContinuousOn u (Metric.sphere a ε))
  (h_cont_v : ContinuousOn v (Metric.sphere a ε))
  (h_cont_n : ContinuousOn n (Metric.sphere a ε))
  (h_cont_grad_u : ContinuousOn (fun x ↦ gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε))
  (h_cont_grad_v : ContinuousOn (fun x ↦ gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε)) :
  IntegrableOn (fun x ↦ u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere a ε) surfaceArea :=
  integrable_flux_diff_sphere Ω a b a ε u v n h_finite_area h_cont_u h_cont_v h_cont_n h_cont_grad_u h_cont_grad_v

lemma integrable_flux_diff_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (u v : E → ℝ) (n : E → E)
  (h_finite_area : surfaceArea (Metric.sphere b ε) ≠ ⊤)
  (h_cont_u : ContinuousOn u (Metric.sphere b ε))
  (h_cont_v : ContinuousOn v (Metric.sphere b ε))
  (h_cont_n : ContinuousOn n (Metric.sphere b ε))
  (h_cont_grad_u : ContinuousOn (fun x ↦ gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε))
  (h_cont_grad_v : ContinuousOn (fun x ↦ gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε)) :
  IntegrableOn (fun x ↦ u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere b ε) surfaceArea :=
  integrable_flux_diff_sphere Ω a b b ε u v n h_finite_area h_cont_u h_cont_v h_cont_n h_cont_grad_u h_cont_grad_v

lemma integrable_flux_diff_frontier_union_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (u v : E → ℝ) (n : E → E)
  (hu_zero : ∀ x ∈ frontier Ω, u x = 0)
  (hv_zero : ∀ x ∈ frontier Ω, v x = 0)
  (h_finite_area_a : surfaceArea (Metric.sphere a ε) ≠ ⊤)
  (h_cont_u_a : ContinuousOn u (Metric.sphere a ε))
  (h_cont_v_a : ContinuousOn v (Metric.sphere a ε))
  (h_cont_n_a : ContinuousOn n (Metric.sphere a ε))
  (h_cont_grad_u_a : ContinuousOn (fun x ↦ gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε))
  (h_cont_grad_v_a : ContinuousOn (fun x ↦ gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε)) :
  IntegrableOn (fun x ↦ u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (frontier Ω ∪ Metric.sphere a ε) surfaceArea := by
  apply IntegrableOn.union
  · exact integrable_flux_diff_frontier Ω a b ε u v n hu_zero hv_zero
  · exact integrable_flux_diff_sphere_a Ω a b ε u v n h_finite_area_a h_cont_u_a h_cont_v_a h_cont_n_a h_cont_grad_u_a h_cont_grad_v_a

/-!
### Singularities and Component Integrability
-/

lemma integrable_H_a_cross_term_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (H_a v : E → ℝ) (n : E → E)
  (h_finite_area : surfaceArea (Metric.sphere a ε) ≠ ⊤)
  (h_cont_H_a : ContinuousOn H_a (Metric.sphere a ε))
  (h_cont_v : ContinuousOn v (Metric.sphere a ε))
  (h_cont_n : ContinuousOn n (Metric.sphere a ε))
  (h_cont_grad_H_a : ContinuousOn (fun x ↦ gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε))
  (h_cont_grad_v : ContinuousOn (fun x ↦ gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε)) :
  IntegrableOn (fun x ↦ H_a x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere a ε) surfaceArea := by
  exact integrableOn_compact_surface_of_continuousOn (isCompact_sphere a ε) h_finite_area _ (ContinuousOn.sub (ContinuousOn.mul h_cont_H_a (ContinuousOn.inner h_cont_grad_v h_cont_n)) (ContinuousOn.mul h_cont_v (ContinuousOn.inner h_cont_grad_H_a h_cont_n)))

lemma integrableOn_inner_grad_Ha_grad_v_ball (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (v : E → ℝ)
  (H_a : E → ℝ)
  (h_cont_grad_Ha : ContinuousOn (gradient H_a) (Metric.closedBall a ε))
  (h_cont_grad_v : ContinuousOn (gradient v) (Metric.closedBall a ε)) :
  IntegrableOn (fun x ↦ ⟪gradient H_a x, gradient v x⟫) (Metric.ball a ε) volume := by
  have h_cont : ContinuousOn (fun x ↦ ⟪gradient H_a x, gradient v x⟫) (Metric.closedBall a ε) := by
    apply ContinuousOn.inner h_cont_grad_Ha h_cont_grad_v
  have h_compact : IsCompact (Metric.closedBall a ε) := isCompact_closedBall a ε
  have h_int_closed : IntegrableOn (fun x ↦ ⟪gradient H_a x, gradient v x⟫) (Metric.closedBall a ε) volume :=
    ContinuousOn.integrableOn_compact h_compact h_cont
  exact IntegrableOn.mono_set h_int_closed Metric.ball_subset_closedBall

lemma integrableOn_v_mul_laplacianWithin_Ha_ball (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (v : E → ℝ)
  (H_a : E → ℝ)
  (h_cont_v : ContinuousOn v (Metric.closedBall a ε))
  (h_cont_laplacian : ContinuousOn (fun x ↦ laplacianWithin H_a (closure (Metric.ball a ε)) x) (Metric.closedBall a ε)) :
  IntegrableOn (fun x ↦ v x * laplacianWithin H_a (closure (Metric.ball a ε)) x) (Metric.ball a ε) volume := by
  have h_cont : ContinuousOn (fun x ↦ v x * laplacianWithin H_a (closure (Metric.ball a ε)) x) (Metric.closedBall a ε) := by
    apply ContinuousOn.mul h_cont_v h_cont_laplacian
  have h_compact : IsCompact (Metric.closedBall a ε) := isCompact_closedBall a ε
  have h_int_closed : IntegrableOn (fun x ↦ v x * laplacianWithin H_a (closure (Metric.ball a ε)) x) (Metric.closedBall a ε) volume :=
    ContinuousOn.integrableOn_compact h_compact h_cont
  exact IntegrableOn.mono_set h_int_closed Metric.ball_subset_closedBall

lemma integrableOn_v_mul_inner_gradWithin_Ha_normal_ball (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (v : E → ℝ)
  (H_a : E → ℝ)
  (n_ball : E → E)
  (h_compact : IsCompact (frontier (Metric.ball a ε)))
  (h_finite_area : surfaceArea (frontier (Metric.ball a ε)) ≠ ⊤)
  (h_cont_v : ContinuousOn v (frontier (Metric.ball a ε)))
  (h_cont_n : ContinuousOn n_ball (frontier (Metric.ball a ε)))
  (h_cont_grad_Ha : ContinuousOn (fun x ↦ gradientWithin H_a (closure (Metric.ball a ε)) x) (frontier (Metric.ball a ε))) :
  IntegrableOn (fun x ↦ v x * ⟪gradientWithin H_a (closure (Metric.ball a ε)) x, n_ball x⟫) (frontier (Metric.ball a ε)) surfaceArea := by
  have h_cont_integrand : ContinuousOn (fun x ↦ v x * ⟪gradientWithin H_a (closure (Metric.ball a ε)) x, n_ball x⟫) (frontier (Metric.ball a ε)) := by
    apply ContinuousOn.mul h_cont_v
    apply ContinuousOn.inner h_cont_grad_Ha h_cont_n
  exact integrableOn_compact_surface_of_continuousOn h_compact h_finite_area _ h_cont_integrand

lemma integrableOn_Ha_mul_laplacianWithin_v_ball (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (v : E → ℝ)
  (H_a : E → ℝ)
  (h_cont_Ha : ContinuousOn H_a (Metric.closedBall a ε))
  (h_cont_laplacian_v : ContinuousOn (fun x ↦ laplacianWithin v (closure (Metric.ball a ε)) x) (Metric.closedBall a ε)) :
  IntegrableOn (fun x ↦ H_a x * laplacianWithin v (closure (Metric.ball a ε)) x) (Metric.ball a ε) volume := by
  have h_cont : ContinuousOn (fun x ↦ H_a x * laplacianWithin v (closure (Metric.ball a ε)) x) (Metric.closedBall a ε) := by
    apply ContinuousOn.mul h_cont_Ha h_cont_laplacian_v
  have h_compact : IsCompact (Metric.closedBall a ε) := isCompact_closedBall a ε
  have h_int_closed : IntegrableOn (fun x ↦ H_a x * laplacianWithin v (closure (Metric.ball a ε)) x) (Metric.closedBall a ε) volume :=
    ContinuousOn.integrableOn_compact h_compact h_cont
  exact IntegrableOn.mono_set h_int_closed Metric.ball_subset_closedBall

lemma integrableOn_Ha_mul_inner_gradWithin_v_normal_ball (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (v : E → ℝ)
  (H_a : E → ℝ)
  (n_ball : E → E)
  (h_compact : IsCompact (frontier (Metric.ball a ε)))
  (h_finite_area : surfaceArea (frontier (Metric.ball a ε)) ≠ ⊤)
  (h_cont_Ha : ContinuousOn H_a (frontier (Metric.ball a ε)))
  (h_cont_n : ContinuousOn n_ball (frontier (Metric.ball a ε)))
  (h_cont_grad_v : ContinuousOn (fun x ↦ gradientWithin v (closure (Metric.ball a ε)) x) (frontier (Metric.ball a ε))) :
  IntegrableOn (fun x ↦ H_a x * ⟪gradientWithin v (closure (Metric.ball a ε)) x, n_ball x⟫) (frontier (Metric.ball a ε)) surfaceArea := by
  have h_cont_integrand : ContinuousOn (fun x ↦ H_a x * ⟪gradientWithin v (closure (Metric.ball a ε)) x, n_ball x⟫) (frontier (Metric.ball a ε)) := by
    apply ContinuousOn.mul h_cont_Ha
    apply ContinuousOn.inner h_cont_grad_v h_cont_n
  exact integrableOn_compact_surface_of_continuousOn h_compact h_finite_area _ h_cont_integrand

lemma integrable_H_b_cross_term_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (H_b u : E → ℝ) (n : E → E)
  (h_finite_area : surfaceArea (Metric.sphere b ε) ≠ ⊤)
  (h_cont_H_b : ContinuousOn H_b (Metric.sphere b ε))
  (h_cont_u : ContinuousOn u (Metric.sphere b ε))
  (h_cont_n : ContinuousOn n (Metric.sphere b ε))
  (h_cont_grad_H_b : ContinuousOn (fun x ↦ gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε))
  (h_cont_grad_u : ContinuousOn (fun x ↦ gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε)) :
  IntegrableOn (fun x ↦ u x * ⟪gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - H_b x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere b ε) surfaceArea := by
  have h_compact : IsCompact (Metric.sphere b ε) := isCompact_sphere b ε
  have h_cont_integrand : ContinuousOn (fun x ↦ u x * ⟪gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - H_b x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere b ε) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.mul h_cont_u
      apply ContinuousOn.inner h_cont_grad_H_b h_cont_n
    · apply ContinuousOn.mul h_cont_H_b
      apply ContinuousOn.inner h_cont_grad_u h_cont_n
  exact integrableOn_compact_surface_of_continuousOn h_compact h_finite_area _ h_cont_integrand

lemma integrableOn_inner_grad_Hb_grad_u_ball (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (u : E → ℝ)
  (H_b : E → ℝ)
  (h_cont_grad_Hb : ContinuousOn (gradient H_b) (Metric.closedBall b ε))
  (h_cont_grad_u : ContinuousOn (gradient u) (Metric.closedBall b ε)) :
  IntegrableOn (fun x ↦ ⟪gradient u x, gradient H_b x⟫) (Metric.ball b ε) volume := by
  have h_cont : ContinuousOn (fun x ↦ ⟪gradient u x, gradient H_b x⟫) (Metric.closedBall b ε) := by
    apply ContinuousOn.inner h_cont_grad_u h_cont_grad_Hb
  have h_compact : IsCompact (Metric.closedBall b ε) := isCompact_closedBall b ε
  have h_int_closed : IntegrableOn (fun x ↦ ⟪gradient u x, gradient H_b x⟫) (Metric.closedBall b ε) volume :=
    ContinuousOn.integrableOn_compact h_compact h_cont
  exact IntegrableOn.mono_set h_int_closed Metric.ball_subset_closedBall

lemma integrableOn_u_mul_laplacianWithin_Hb_ball (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (u : E → ℝ)
  (H_b : E → ℝ)
  (h_cont_u : ContinuousOn u (Metric.closedBall b ε))
  (h_cont_laplacian : ContinuousOn (fun x ↦ laplacianWithin H_b (closure (Metric.ball b ε)) x) (Metric.closedBall b ε)) :
  IntegrableOn (fun x ↦ u x * laplacianWithin H_b (closure (Metric.ball b ε)) x) (Metric.ball b ε) volume := by
  have h_cont : ContinuousOn (fun x ↦ u x * laplacianWithin H_b (closure (Metric.ball b ε)) x) (Metric.closedBall b ε) := by
    apply ContinuousOn.mul h_cont_u h_cont_laplacian
  have h_compact : IsCompact (Metric.closedBall b ε) := isCompact_closedBall b ε
  have h_int_closed : IntegrableOn (fun x ↦ u x * laplacianWithin H_b (closure (Metric.ball b ε)) x) (Metric.closedBall b ε) volume :=
    ContinuousOn.integrableOn_compact h_compact h_cont
  exact IntegrableOn.mono_set h_int_closed Metric.ball_subset_closedBall

lemma integrableOn_u_mul_inner_gradWithin_Hb_normal_ball (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (u : E → ℝ)
  (H_b : E → ℝ)
  (n_ball : E → E)
  (h_compact : IsCompact (frontier (Metric.ball b ε)))
  (h_finite_area : surfaceArea (frontier (Metric.ball b ε)) ≠ ⊤)
  (h_cont_u : ContinuousOn u (frontier (Metric.ball b ε)))
  (h_cont_n : ContinuousOn n_ball (frontier (Metric.ball b ε)))
  (h_cont_grad_Hb : ContinuousOn (fun x ↦ gradientWithin H_b (closure (Metric.ball b ε)) x) (frontier (Metric.ball b ε))) :
  IntegrableOn (fun x ↦ u x * ⟪gradientWithin H_b (closure (Metric.ball b ε)) x, n_ball x⟫) (frontier (Metric.ball b ε)) surfaceArea := by
  have h_cont_integrand : ContinuousOn (fun x ↦ u x * ⟪gradientWithin H_b (closure (Metric.ball b ε)) x, n_ball x⟫) (frontier (Metric.ball b ε)) := by
    apply ContinuousOn.mul h_cont_u
    apply ContinuousOn.inner h_cont_grad_Hb h_cont_n
  exact integrableOn_compact_surface_of_continuousOn h_compact h_finite_area _ h_cont_integrand

lemma integrableOn_Hb_mul_laplacianWithin_u_ball (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (u : E → ℝ)
  (H_b : E → ℝ)
  (h_cont_Hb : ContinuousOn H_b (Metric.closedBall b ε))
  (h_cont_laplacian_u : ContinuousOn (fun x ↦ laplacianWithin u (closure (Metric.ball b ε)) x) (Metric.closedBall b ε)) :
  IntegrableOn (fun x ↦ H_b x * laplacianWithin u (closure (Metric.ball b ε)) x) (Metric.ball b ε) volume := by
  have h_cont : ContinuousOn (fun x ↦ H_b x * laplacianWithin u (closure (Metric.ball b ε)) x) (Metric.closedBall b ε) := by
    apply ContinuousOn.mul h_cont_Hb h_cont_laplacian_u
  have h_compact : IsCompact (Metric.closedBall b ε) := isCompact_closedBall b ε
  have h_int_closed : IntegrableOn (fun x ↦ H_b x * laplacianWithin u (closure (Metric.ball b ε)) x) (Metric.closedBall b ε) volume :=
    ContinuousOn.integrableOn_compact h_compact h_cont
  exact IntegrableOn.mono_set h_int_closed Metric.ball_subset_closedBall

lemma integrableOn_Hb_mul_inner_gradWithin_u_normal_ball (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (u : E → ℝ)
  (H_b : E → ℝ)
  (n_ball : E → E)
  (h_compact : IsCompact (frontier (Metric.ball b ε)))
  (h_finite_area : surfaceArea (frontier (Metric.ball b ε)) ≠ ⊤)
  (h_cont_Hb : ContinuousOn H_b (frontier (Metric.ball b ε)))
  (h_cont_n : ContinuousOn n_ball (frontier (Metric.ball b ε)))
  (h_cont_grad_u : ContinuousOn (fun x ↦ gradientWithin u (closure (Metric.ball b ε)) x) (frontier (Metric.ball b ε))) :
  IntegrableOn (fun x ↦ H_b x * ⟪gradientWithin u (closure (Metric.ball b ε)) x, n_ball x⟫) (frontier (Metric.ball b ε)) surfaceArea := by
  have h_cont_integrand : ContinuousOn (fun x ↦ H_b x * ⟪gradientWithin u (closure (Metric.ball b ε)) x, n_ball x⟫) (frontier (Metric.ball b ε)) := by
    apply ContinuousOn.mul h_cont_Hb
    apply ContinuousOn.inner h_cont_grad_u h_cont_n
  exact integrableOn_compact_surface_of_continuousOn h_compact h_finite_area _ h_cont_integrand

/-!
### Green's Identities
-/

lemma greens_first_identity (Ω : Set E) (u v : E → ℝ) (n : E → E)
  [h_domain : HasPDEDomain Ω] (hn : IsOutwardUnitNormal Ω n)
  (h_F_diff : ContDiffOn ℝ 1 (fun x => v x • gradient u x) Ω)
  (h_F_cont : ContinuousOn (fun x => v x • gradientWithin u (closure Ω) x) (closure Ω))
  (h_int_grad : IntegrableOn (fun x => ⟪gradient u x, gradient v x⟫_ℝ) Ω)
  (h_int_lap : IntegrableOn (fun x => v x * laplacianWithin u (closure Ω) x) Ω) :
  ∫ x in Ω, ⟪gradient u x, gradient v x⟫_ℝ =
  (∫ x in frontier Ω, v x * ⟪gradientWithin u (closure Ω) x, n x⟫_ℝ ∂surfaceArea) - ∫ x in Ω, v x * laplacianWithin u (closure Ω) x := by
  sorry

lemma greens_second_identity (Ω : Set E) (u v : E → ℝ) (n : E → E)
  [h_domain : HasPDEDomain Ω] (hn : IsOutwardUnitNormal Ω n)
  (h_F_diff_uv : ContDiffOn ℝ 1 (fun x => v x • gradient u x) Ω)
  (h_F_cont_uv : ContinuousOn (fun x => v x • gradientWithin u (closure Ω) x) (closure Ω))
  (h_int_grad_uv : IntegrableOn (fun x => ⟪gradient u x, gradient v x⟫_ℝ) Ω)
  (h_int_lap_uv : IntegrableOn (fun x => v x * laplacianWithin u (closure Ω) x) Ω)
  (h_int_surf_uv : IntegrableOn (fun x => v x * ⟪gradientWithin u (closure Ω) x, n x⟫_ℝ) (frontier Ω) surfaceArea)
  (h_F_diff_vu : ContDiffOn ℝ 1 (fun x => u x • gradient v x) Ω)
  (h_F_cont_vu : ContinuousOn (fun x => u x • gradientWithin v (closure Ω) x) (closure Ω))
  (h_int_lap_vu : IntegrableOn (fun x => u x * laplacianWithin v (closure Ω) x) Ω)
  (h_int_surf_vu : IntegrableOn (fun x => u x * ⟪gradientWithin v (closure Ω) x, n x⟫_ℝ) (frontier Ω) surfaceArea) :
  ∫ x in Ω, (u x * laplacianWithin v (closure Ω) x - v x * laplacianWithin u (closure Ω) x) =
  (∫ x in frontier Ω, (u x * ⟪gradientWithin v (closure Ω) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure Ω) x, n x⟫_ℝ) ∂surfaceArea) := by
  rw [integral_sub h_int_lap_vu h_int_lap_uv, integral_sub h_int_surf_vu h_int_surf_uv]
  linarith [greens_first_identity Ω u v n hn h_F_diff_uv h_F_cont_uv h_int_grad_uv h_int_lap_uv,
    greens_first_identity Ω v u n hn h_F_diff_vu h_F_cont_vu (by simp only [real_inner_comm]; exact h_int_grad_uv) h_int_lap_vu,
    show ∫ x in Ω, ⟪gradient u x, gradient v x⟫_ℝ = ∫ x in Ω, ⟪gradient v x, gradient u x⟫_ℝ by simp_rw [real_inner_comm]]

lemma apply_greens_second_identity
  (Ω : Set E)
  [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (u v : E → ℝ)
  (hu_cont : ContinuousOn u (closure Ω))
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hv_cont : ContinuousOn v (closure Ω))
  (hv_diff : ContDiffOn ℝ 2 v (closure Ω))
  (n : E → E)
  (hn : IsOutwardUnitNormal Ω n)
  (h_n_cont : ContinuousOn n (frontier Ω)) :
  ∫ x in Ω, (u x * laplacianWithin v (closure Ω) x - v x * laplacianWithin u (closure Ω) x) =
  ∫ x in frontier Ω, (u x * ⟪gradientWithin v (closure Ω) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure Ω) x, n x⟫_ℝ) ∂surfaceArea := by
  exact greens_second_identity Ω u v n hn
    (smul_gradient_contDiffOn_one Ω u v hu_diff hv_diff)
    (smul_gradientWithin_continuousOn Ω u v (hu_diff.of_le (by decide)) hv_cont)
    (integrable_inner_gradient_of_c1 Ω h_bounded u v (hu_diff.of_le (by decide)) (hv_diff.of_le (by decide)))
    (integrable_mul_laplacian_of_c2 Ω h_bounded u v hu_diff hv_cont)
    (integrable_mul_inner_gradientWithin_normal Ω h_bounded h_area u v (hu_diff.of_le (by decide)) hv_cont n h_n_cont)
    (smul_gradient_contDiffOn_one Ω v u hv_diff hu_diff)
    (smul_gradientWithin_continuousOn Ω v u (hv_diff.of_le (by decide)) hu_cont)
    (integrable_mul_laplacian_of_c2 Ω h_bounded v u hv_diff hu_cont)
    (integrable_mul_inner_gradientWithin_normal Ω h_bounded h_area v u (hv_diff.of_le (by decide)) hu_cont n h_n_cont)

lemma harmonic_laplacian_zero (u : E → ℝ) (Ω : Set E) (x : E) (hx : x ∈ Ω)
  [h_domain : HasPDEDomain Ω]
  (h_harm : IsHarmonic u Ω) :
  laplacianWithin u (closure Ω) x = 0 := by
  rw [laplacianWithin_closure_eq_laplacian u Ω h_domain.is_open x hx]
  exact h_harm x hx

lemma greens_second_identity_harmonic
  (Ω : Set E)
  [h_domain : HasPDEDomain Ω]
  (u H : E → ℝ)
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (hu_cont : ContinuousOn u (closure Ω))
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hu_harm : IsHarmonic u Ω)
  (hH_cont : ContinuousOn H (closure Ω))
  (hH_diff : ContDiffOn ℝ 2 H (closure Ω))
  (hH_harm : IsHarmonic H Ω)
  (n : E → E)
  (hn : IsOutwardUnitNormal Ω n)
  (hn_cont : ContinuousOn n (frontier Ω)) :
  ∫ x in frontier Ω,
    (u x * ⟪n x, gradientWithin H (closure Ω) x⟫_ℝ -
    H x * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) ∂surfaceArea = 0 := by
  have h_integrand_eq : (fun x => u x * ⟪n x, gradientWithin H (closure Ω) x⟫_ℝ - H x * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) =
    (fun x => u x * ⟪gradientWithin H (closure Ω) x, n x⟫_ℝ - H x * ⟪gradientWithin u (closure Ω) x, n x⟫_ℝ) := by
    ext x
    rw [real_inner_comm (n x), real_inner_comm (n x)]
  rw [h_integrand_eq]
  rw [← apply_greens_second_identity Ω h_bounded h_area u H hu_cont hu_diff hH_cont hH_diff n hn hn_cont]
  rw [MeasureTheory.setIntegral_congr_fun h_domain.is_open.measurableSet fun x hx => by
    rw [harmonic_laplacian_zero u Ω x hx hu_harm, harmonic_laplacian_zero H Ω x hx hH_harm]]
  simp_all only [ne_eq, mul_zero, sub_self, integral_zero]
