import PDE.Basics.Laplace.LaplaceDirichletPrinciple

noncomputable section

open Real Set MeasureTheory Metric Filter Function Pointwise InnerProductSpace FiniteDimensional
open scoped BigOperators Topology Classical


lemma step_ii_domain_exists (φ : E → ℝ) (h_supp : HasCompactSupport φ) :
  ∃ Ω : Set E, HasPDEDomain Ω ∧ Metric.ball (0 : E) 1 ⊆ Ω ∧ tsupport φ ⊆ Ω ∧ Bornology.IsBounded Ω ∧ surfaceArea (frontier Ω) ≠ ⊤ := by
  have h_bound_supp := h_supp.isCompact.isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball 0).mp h_bound_supp
  use Metric.ball 0 (max 2 R)
  refine ⟨instHasPDEDomainBall 0 (max 2 R) (lt_max_iff.mpr (Or.inl zero_lt_two)), ?_, ?_, Metric.isBounded_ball, ?_⟩
  · exact Metric.ball_subset_ball (le_max_of_le_left one_le_two)
  · exact Subset.trans hR (Metric.ball_subset_ball (le_max_right 2 R))
  · rw [frontier_ball 0 (lt_max_iff.mpr (Or.inl zero_lt_two)).ne']
    exact (measure_sphere_lt_top (max 2 R) (lt_max_iff.mpr (Or.inl zero_lt_two))).ne

lemma integral_frontier_vanishes (φ : E → ℝ) (Ω : Set E) [HasPDEDomain Ω] (n_Omega : E → E) (ε : ℝ)
    (hΩ_supp : tsupport φ ⊆ Ω) :
    ∫ x in frontier Ω, ((1 / ‖x‖) * ⟪gradientWithin φ (closure (Ω \ Metric.closedBall (0 : E) ε)) x, n_Omega x⟫_ℝ - φ x * ⟪gradientWithin (fun y : E => 1 / ‖y‖) (closure (Ω \ Metric.closedBall (0 : E) ε)) x, n_Omega x⟫_ℝ) ∂surfaceArea = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun x hx => by
    simp [phi_eq_zero_on_frontier φ Ω (HasPDEDomain.is_open (s := Ω)) hΩ_supp x hx,
          gradientWithin_phi_eq_zero_on_frontier φ Ω (HasPDEDomain.is_open (s := Ω)) hΩ_supp ε x hx]

lemma step_ii_greens_annulus (φ : E → ℝ) (h_smooth : ContDiff ℝ ⊤ φ)
  (Ω : Set E) [HasPDEDomain Ω]
  (n_Omega : E → E) (h_norm_Omega : IsOutwardUnitNormal Ω n_Omega)
  (h_cont_n : ContinuousOn n_Omega (frontier Ω))
  (h_bound : Bornology.IsBounded Ω) (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall (0 : E) ε ⊆ Ω)
  (hΩ_supp : tsupport φ ⊆ Ω) :
    ∫ x in Ω \ Metric.ball (0 : E) ε, (1 / ‖x‖) * laplacian φ x =
    ∫ x in Metric.sphere (0 : E) ε, ((1 / ‖x‖) * ⟪gradient φ x, -(1 / ε) • x⟫_ℝ -
      φ x * ⟪gradient (fun y => 1 / ‖y‖) x, -(1 / ε) • x⟫_ℝ) ∂surfaceArea := by
  calc ∫ x in Ω \ Metric.ball (0 : E) ε, (1 / ‖x‖) * laplacian φ x
    _ = ∫ x in Ω \ Metric.ball (0 : E) ε, ((1 / ‖x‖) * laplacian φ x - φ x * laplacian (fun y : E => 1 / ‖y‖) x) := by
        refine setIntegral_congr_fun (HasPDEDomain.is_open.measurableSet.diff Metric.isOpen_ball.measurableSet) (fun x hx ↦ ?_)
        have hz : x ≠ 0 := fun h ↦ by simp_all [Set.mem_sdiff, Metric.mem_ball]
        simp_rw [laplacian_inv_norm_eq_zero hz, mul_zero, sub_zero]

    _ = ∫ x in Ω \ Metric.closedBall (0 : E) ε, ((1 / ‖x‖) * laplacian φ x - φ x * laplacian (fun y : E => 1 / ‖y‖) x) := by
        apply MeasureTheory.setIntegral_congr_set
        apply MeasureTheory.measure_symmDiff_eq_zero_iff.mp
        refine measure_mono_null (fun x hx ↦ ?_) (volume_sphere 0 ε)
        simp only [Set.mem_symmDiff, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right, Metric.mem_sphere] at hx ⊢
        rcases hx with ⟨⟨hxΩ, h1⟩, h2⟩ | ⟨⟨hxΩ, h1⟩, h2⟩ <;>
        push Not at h2 <;> linarith [h2 hxΩ]

    _ = ∫ x in Ω \ Metric.closedBall (0 : E) ε, ((1 / ‖x‖) * laplacianWithin φ (closure (Ω \ Metric.closedBall (0 : E) ε)) x - φ x * laplacianWithin (fun y : E => 1 / ‖y‖) (closure (Ω \ Metric.closedBall (0 : E) ε)) x) := by
        have h_open' : IsOpen (Ω \ Metric.closedBall (0 : E) ε) := HasPDEDomain.is_open.sdiff Metric.isClosed_closedBall
        refine setIntegral_congr_fun h_open'.measurableSet (fun x hx ↦ ?_)
        rw [laplacianWithin_closure_eq_laplacian φ _ h_open' x hx, laplacianWithin_closure_eq_laplacian (fun y ↦ 1 / ‖y‖) _ h_open' x hx]

    _ = (∫ x in frontier Ω, ((1 / ‖x‖) * ⟪gradientWithin φ (closure (Ω \ Metric.closedBall (0 : E) ε)) x, n_Omega x⟫_ℝ - φ x * ⟪gradientWithin (fun y : E => 1 / ‖y‖) (closure (Ω \ Metric.closedBall (0 : E) ε)) x, n_Omega x⟫_ℝ) ∂surfaceArea) +
        ∫ x in Metric.sphere (0 : E) ε, ((1 / ‖x‖) * ⟪gradientWithin φ (closure (Ω \ Metric.closedBall (0 : E) ε)) x, -(1 / ε) • x⟫_ℝ - φ x * ⟪gradientWithin (fun y : E => 1 / ‖y‖) (closure (Ω \ Metric.closedBall (0 : E) ε)) x, -(1 / ε) • x⟫_ℝ) ∂surfaceArea := by
        simpa [sub_zero] using greens_second_identity_annulus_gen Ω n_Omega h_norm_Omega h_cont_n 0 ε hε h_subset h_bound h_area φ (fun x ↦ 1 / ‖x‖) (ContDiff.contDiffOn (ContDiff.of_le h_smooth le_top)) (inv_norm_smooth_on_annulus Ω ε hε)

    _ = ∫ x in Metric.sphere (0 : E) ε, ((1 / ‖x‖) * ⟪gradient φ x, -(1 / ε) • x⟫_ℝ - φ x * ⟪gradient (fun y : E => 1 / ‖y‖) x, -(1 / ε) • x⟫_ℝ) ∂surfaceArea := by
        rw [integral_frontier_vanishes φ Ω n_Omega ε hΩ_supp, zero_add]
        refine setIntegral_congr_fun Metric.isClosed_sphere.measurableSet (fun x hx ↦ ?_)
        rw [gradientWithin_eq_gradient_sphere_phi φ h_smooth Ω ε hε h_subset x hx, gradientWithin_eq_gradient_sphere_inv_norm Ω ε hε h_subset x hx]

lemma split_integral_laplacian (φ : E → ℝ) (h_smooth : ContDiff ℝ ⊤ φ) (h_supp : HasCompactSupport φ) :
    ∀ ε > 0, ∫ x : E, (1 / ‖x‖) * laplacian φ x =
    (∫ x in ((univ : Set E) \ Metric.ball (0 : E) ε), (1 / ‖x‖) * laplacian φ x) +
    (∫ x in Metric.ball (0 : E) ε, (1 / ‖x‖) * laplacian φ x) := fun ε _ => by
  rw [show (univ : Set E) \ Metric.ball (0 : E) ε = (Metric.ball (0 : E) ε)ᶜ by ext; simp]
  exact (integral_add_compl measurableSet_ball (inv_norm_mul_laplacian_integrable φ h_smooth h_supp)).symm.trans (add_comm _ _)

lemma integrand_bound_sphere (φ : E → ℝ) (ε : ℝ) (hε : 0 < ε) (M : ℝ) (h_grad : ∀ x, ‖gradient φ x‖ ≤ M) (x : E) (hx : x ∈ Metric.sphere (0 : E) ε) :
  ‖(1 / ‖x‖) * ⟪gradient φ x, -(1 / ε) • x⟫_ℝ‖ ≤ M / ε := by
  have h_norm_x : ‖x‖ = ε := by rwa [Metric.mem_sphere, dist_zero_right] at hx
  rw [norm_mul, h_norm_x, Real.norm_of_nonneg (div_nonneg one_pos.le hε.le)]
  calc (1 / ε) * |⟪gradient φ x, -(1 / ε) • x⟫_ℝ|
    _ ≤ (1 / ε) * ‖gradient φ x‖ := mul_le_mul_of_nonneg_left (abs_inner_sphere_normal_le_norm hε h_norm_x) (div_nonneg one_pos.le hε.le)
    _ ≤ (1 / ε) * M := mul_le_mul_of_nonneg_left (h_grad x) (div_nonneg one_pos.le hε.le)
    _ = M / ε := by ring

lemma step_iii_sphere_tendsto_zero (φ : E → ℝ) (h_smooth : ContDiff ℝ ⊤ φ) (h_supp : HasCompactSupport φ) :
    Tendsto (fun ε => ∫ x in Metric.sphere (0 : E) ε, (1 / ‖x‖) * ⟪gradient φ x, -(1 / ε) • x⟫_ℝ ∂surfaceArea) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, h_grad⟩ := bound_gradient_of_compact_support φ h_smooth h_supp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_const_mul_eps_zero M) (Eventually.of_forall fun ε => norm_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  calc
    ‖∫ x in Metric.sphere (0 : E) ε, (1 / ‖x‖) * ⟪gradient φ x, -(1 / ε) • x⟫_ℝ ∂surfaceArea‖
      ≤ ∫ x in Metric.sphere (0 : E) ε, ‖(1 / ‖x‖) * ⟪gradient φ x, -(1 / ε) • x⟫_ℝ‖ ∂surfaceArea := MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ _ in Metric.sphere (0 : E) ε, (M / ε) ∂surfaceArea := by
        have h_cont : ContinuousOn (fun x ↦ ‖(1 / ‖x‖) * ⟪gradient φ x, -(1 / ε) • x⟫_ℝ‖) (Metric.sphere (0 : E) ε) := by
          have h_smul : Continuous (fun x : E ↦ -(1 / ε) • x) := by
            change Continuous ((fun _ : E ↦ -(1 / ε)) • (id : E → E))
            exact Continuous.smul continuous_const continuous_id
          refine ContinuousOn.norm (ContinuousOn.mul ?_ (ContinuousOn.inner (continuous_gradient φ h_smooth).continuousOn h_smul.continuousOn))
          refine ContinuousOn.div continuousOn_const continuous_norm.continuousOn (fun x hx ↦ ?_)
          rw [Metric.mem_sphere, dist_zero_right] at hx
          subst hx
          simp_all only [mem_Ioi, norm_pos_iff, ne_eq, norm_eq_zero, not_false_eq_true]
        apply MeasureTheory.setIntegral_mono_on
          (integrableOn_of_continuousOn_compact_finite_measure (isCompact_sphere (0 : E) ε)
            isClosed_sphere.measurableSet (measure_sphere_lt_top ε hε) h_cont)
          (MeasureTheory.integrableOn_const (measure_sphere_lt_top ε hε).ne (by finiteness))
          isClosed_sphere.measurableSet (integrand_bound_sphere φ ε hε M h_grad)
    _ = (M / ε) * (surfaceArea (Metric.sphere (0 : E) ε)).toReal := by
        rw [MeasureTheory.integral_const, smul_eq_mul, mul_comm]
        congr 1
        simp [MeasureTheory.Measure.real]
    _ ≤ (M / ε) * (4 * π * ε ^ 2) := mul_le_mul_of_nonneg_left (by rw [measure_sphere_scaling ε hε, ENNReal.toReal_mul, unit_sphere_area_hausdorff, ENNReal.toReal_ofReal (by positivity)]; ring_nf; linarith) (div_nonneg (le_trans (norm_nonneg _) (h_grad 0)) (le_of_lt hε))
    _ = M * 4 * π * ε := by
        simp_all only [mem_Ioi]
        field_simp [hε.ne']

lemma step_iv_sphere_integral_eq (φ : E → ℝ) (ε : ℝ) (hε : 0 < ε) :
  ∫ x in Metric.sphere (0 : E) ε, -(φ x * ⟪gradient (fun y => 1 / ‖y‖) x, -(1 / ε) • x⟫_ℝ) ∂surfaceArea =
  -4 * π * ((1 / (4 * π * ε^2)) * ∫ x in Metric.sphere (0 : E) ε, φ x ∂surfaceArea) := by
  have h_eq : ∀ x ∈ Metric.sphere (0 : E) ε, -(φ x * ⟪gradient (fun y => 1 / ‖y‖) x, -(1 / ε) • x⟫_ℝ) = -(1 / ε^2) * φ x := fun x hx => by
    rw [inner_gradient_inv_norm_sphere_normal hε (by rwa [Metric.mem_sphere, dist_zero_right] at hx)]
    ring
  rw [setIntegral_congr_fun isClosed_sphere.measurableSet h_eq, integral_const_mul]
  field_simp [hε.ne.symm, Real.pi_ne_zero]

lemma step_iv_sphere_integral_eq' (φ : E → ℝ) (x₀ : E) (ε : ℝ) (hε : 0 < ε) :
  ∫ x in Metric.sphere x₀ ε, -(φ x * ⟪gradient (fun y => 1 / ‖y - x₀‖) x, -(1 / ε) • (x - x₀)⟫_ℝ) ∂surfaceArea =
  -4 * π * ((1 / (4 * π * ε^2)) * ∫ x in Metric.sphere x₀ ε, φ x ∂surfaceArea) := by
  have h_inner : ∀ x ∈ Metric.sphere x₀ ε, ⟪gradient (fun y => 1 / ‖y - x₀‖) x, -(1 / ε) • (x - x₀)⟫_ℝ = 1 / ε^2 := by
    intro x hx
    exact inner_gradient_inv_norm_sphere_normal_shifted x₀ ε hε x hx
  have h_eq : ∀ x ∈ Metric.sphere x₀ ε, -(φ x * ⟪gradient (fun y => 1 / ‖y - x₀‖) x, -(1 / ε) • (x - x₀)⟫_ℝ) = -(1 / ε^2) * φ x := fun x hx => by
    rw [h_inner x hx]
    ring
  rw [setIntegral_congr_fun isClosed_sphere.measurableSet h_eq, integral_const_mul]
  field_simp [hε.ne.symm, Real.pi_ne_zero]

lemma integral_outside_ball_eq_domain (φ : E → ℝ) (Ω : Set E) (h_supp_omega : tsupport φ ⊆ Ω) :
    ∀ ε > 0, ∫ (x : E) in univ \ ball 0 ε, 1 / ‖x‖ * laplacian φ x = ∫ (x : E) in Ω \ ball 0 ε, 1 / ‖x‖ * laplacian φ x := by
  intro ε _
  have h_ind : (fun x ↦ 1 / ‖x‖ * laplacian φ x) = (tsupport φ).indicator (fun x ↦ 1 / ‖x‖ * laplacian φ x) := by
    ext x; by_cases hx : x ∈ tsupport φ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; simp [laplacian_eq_zero_of_notMem_tsupport hx]
  rw [h_ind]
  simp_rw [integral_indicator (isClosed_tsupport φ).measurableSet, MeasureTheory.Measure.restrict_restrict (isClosed_tsupport φ).measurableSet]
  have h_dom : (univ \ ball 0 ε) ∩ tsupport φ = (Ω \ ball 0 ε) ∩ tsupport φ := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_univ, true_and]
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨⟨h_supp_omega h2, h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ ↦ ⟨h1, h2⟩⟩
  congr 1; rw [Set.inter_comm, h_dom, Set.inter_comm]

lemma integral_greens_split (φ : E → ℝ) (h_smooth : ContDiff ℝ ⊤ φ)
  (Ω : Set E) [HasPDEDomain Ω]
  (n_Omega : E → E) (h_norm_Omega : IsOutwardUnitNormal Ω n_Omega)
  (h_cont_n : ContinuousOn n_Omega (frontier Ω))
  (h_bound : Bornology.IsBounded Ω) (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (h_supp_omega : tsupport φ ⊆ Ω) :
  ∀ ε > 0, Metric.closedBall (0 : E) ε ⊆ Ω → ∫ (x : E) in Ω \ Metric.ball 0 ε, 1 / ‖x‖ * laplacian φ x =
  (∫ (x : E) in Metric.sphere 0 ε, 1 / ‖x‖ * ⟪gradient φ x, -(1 / ε) • x⟫_ℝ ∂surfaceArea) +
  (∫ (x : E) in Metric.sphere 0 ε, -(φ x * ⟪gradient (fun y ↦ 1 / ‖y‖) x, -(1 / ε) • x⟫_ℝ) ∂surfaceArea) := by
  intro ε hε h_subset
  rw [step_ii_greens_annulus φ h_smooth Ω n_Omega h_norm_Omega h_cont_n h_bound h_area ε hε h_subset h_supp_omega]
  have h_compact : IsCompact (Metric.sphere (0 : E) ε) := isCompact_sphere 0 ε
  have h_sphere_meas : surfaceArea (Metric.sphere (0 : E) ε) < ⊤ := measure_sphere_lt_top ε hε
  have h_meas_set : MeasurableSet (Metric.sphere (0 : E) ε) := IsCompact.measurableSet h_compact

  have h_cont_1 : ContinuousOn (fun x ↦ 1 / ‖x‖ * ⟪gradient φ x, -(1 / ε) • x⟫_ℝ) (Metric.sphere 0 ε) := by
    apply ContinuousOn.mul
    · refine ContinuousOn.div continuousOn_const continuous_norm.continuousOn (fun x hx ↦ ?_)
      rw [mem_sphere_zero_iff_norm.mp hx]
      exact ne_of_gt hε
    · apply ContinuousOn.inner
      · exact (contDiffOn_1_gradient_continuousOn (h_smooth.of_le le_top).contDiffOn isOpen_univ).mono (subset_univ _)
      · have h_smul : Continuous (fun x : E ↦ -(1 / ε) • x) := by
          change Continuous ((fun _ : E ↦ -(1 / ε)) • (id : E → E))
          exact Continuous.smul continuous_const continuous_id
        exact h_smul.continuousOn

  have h_int_1 : IntegrableOn (fun x ↦ 1 / ‖x‖ * ⟪gradient φ x, -(1 / ε) • x⟫_ℝ) (Metric.sphere 0 ε) surfaceArea :=
    integrableOn_of_continuousOn_compact_finite_measure h_compact h_meas_set h_sphere_meas h_cont_1

  have h_cont_2 : ContinuousOn (fun x ↦ φ x * ⟪gradient (fun y ↦ 1 / ‖y‖) x, -(1 / ε) • x⟫_ℝ) (Metric.sphere 0 ε) := by
    apply ContinuousOn.mul h_smooth.continuous.continuousOn
    apply ContinuousOn.inner
    · have h_grad_inv : ContinuousOn (gradient (fun y : E ↦ 1 / ‖y‖)) {0}ᶜ := by
        apply contDiffOn_1_gradient_continuousOn
        · exact ContDiffOn.div contDiffOn_const (ContDiffOn.norm ℝ contDiffOn_id (fun x hx ↦ hx)) (fun x hx ↦ norm_ne_zero_iff.mpr hx)
        · exact isOpen_compl_singleton
      refine h_grad_inv.mono (fun x hx h_zero ↦ ?_)
      have h_norm : ‖x‖ = ε := mem_sphere_zero_iff_norm.mp hx
      rw [h_zero, norm_zero] at h_norm
      exact ne_of_gt hε h_norm.symm
    · have h_smul : Continuous (fun x : E ↦ -(1 / ε) • x) := by
        change Continuous ((fun _ : E ↦ -(1 / ε)) • (id : E → E))
        exact Continuous.smul continuous_const continuous_id
      exact h_smul.continuousOn

  have h_int_2 : IntegrableOn (fun x ↦ φ x * ⟪gradient (fun y ↦ 1 / ‖y‖) x, -(1 / ε) • x⟫_ℝ) (Metric.sphere 0 ε) surfaceArea :=
    integrableOn_of_continuousOn_compact_finite_measure h_compact h_meas_set h_sphere_meas h_cont_2

  rw [integral_sub h_int_1 h_int_2, integral_neg, sub_eq_add_neg]

lemma split_integral_laplacian_eventually_eq (φ : E → ℝ) (h_smooth : ContDiff ℝ ⊤ φ) (h_supp : HasCompactSupport φ) :
    (fun ε ↦ (∫ (x : E) in univ \ Metric.ball 0 ε, 1 / ‖x‖ * laplacian φ x) + ∫ (x : E) in Metric.ball 0 ε, 1 / ‖x‖ * laplacian φ x) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ ↦ ∫ (x : E), 1 / ‖x‖ * laplacian φ x) := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (split_integral_laplacian φ h_smooth h_supp ε hε).symm

theorem dist_laplacian_inv_norm (φ : E → ℝ) (h_smooth : ContDiff ℝ ⊤ φ) (h_supp : HasCompactSupport φ) :
    ∫ x : E, (1 / ‖x‖) * laplacian φ x = -4 * π * φ (0 : E) := by
  obtain ⟨Ω, inst, h_ball_1_subset, h_supp_omega, h_bound, h_area⟩ := step_ii_domain_exists φ h_supp

  have step_i := integral_ball_tendsto_zero _ (inv_norm_mul_laplacian_integrable φ h_smooth h_supp)
  have step_iii := step_iii_sphere_tendsto_zero φ h_smooth h_supp
  have avg := averaging_lemma_spherical 1 zero_lt_one φ h_smooth.continuous.continuousOn

  have h_term2_lim : Tendsto (fun ε ↦ ∫ x in Metric.sphere 0 ε, -(φ x * ⟪gradient (fun y ↦ 1 / ‖y‖) x, -(1 / ε) • x⟫_ℝ) ∂surfaceArea) (𝓝[>] 0) (𝓝 (-4 * π * φ 0)) := by
    refine Tendsto.congr' ?_ (Tendsto.const_mul (-4 * π) avg)
    filter_upwards [self_mem_nhdsWithin] with ε hε using (step_iv_sphere_integral_eq φ ε hε).symm

  have h_term1_lim : Tendsto (fun ε ↦ ∫ x in univ \ Metric.ball 0 ε, 1 / ‖x‖ * laplacian φ x) (𝓝[>] 0) (𝓝 (-4 * π * φ 0)) := by
    have h_add := Tendsto.add step_iii h_term2_lim
    rw [zero_add] at h_add
    refine Tendsto.congr' ?_ h_add
    obtain ⟨n_Omega, h_norm_Omega, h_cont_n⟩ :=
      (inst.toHasDivergenceTheoremDomain).has_normal
    filter_upwards [self_mem_nhdsWithin, eventually_closedBall_subset_domain h_ball_1_subset] with ε hε h_subset
    rw [integral_outside_ball_eq_domain φ Ω h_supp_omega ε hε, integral_greens_split φ h_smooth Ω n_Omega h_norm_Omega h_cont_n h_bound h_area h_supp_omega ε hε h_subset]

  have h_lhs_lim : Tendsto (fun ε ↦ ∫ x, 1 / ‖x‖ * laplacian φ x) (𝓝[>] (0 : ℝ)) (𝓝 (-4 * π * φ 0)) := by
    have h_add := Tendsto.add h_term1_lim step_i
    rw [add_zero] at h_add
    exact Tendsto.congr' (split_integral_laplacian_eventually_eq φ h_smooth h_supp) h_add

  haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique tendsto_const_nhds h_lhs_lim
