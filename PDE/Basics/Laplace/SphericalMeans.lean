import PDE.Basics.Laplace.GreensIdentities

open Real Set MeasureTheory Metric Filter Function Pointwise InnerProductSpace
open scoped BigOperators Topology Classical

/-!
### Spherical Integrands and Maps
-/

lemma sphere_integral_revert_vars (u : E → ℝ) (x₀ : E) (r : ℝ) (hr : 0 < r) :
  ∫ (y : E) in sphere 0 1, (fderiv ℝ u (x₀ + r • y)) y ∂surfaceArea =
  (1 / r^2) * ∫ (x : E) in sphere x₀ r, (fderiv ℝ u x) (x - x₀) * (1 / r) ∂surfaceArea := by
  let g : E ≃ₜ E := (Homeomorph.addRight (-x₀)).trans (Homeomorph.smulOfNeZero (1 / r) (by positivity))
  symm
  calc
    (1 / r^2) * ∫ (x : E) in sphere x₀ r, (fderiv ℝ u x) (x - x₀) * (1 / r) ∂surfaceArea
      = (1 / r^2) * ∫ (x : E) in sphere x₀ r, (fderiv ℝ u (g.symm (g x))) (g x) ∂surfaceArea := by
        simp_rw [show ∀ x, g.symm (g x) = x from fun x ↦ by rw [Homeomorph.symm_apply_apply],
          show ∀ x, g x = (1 / r) • (x - x₀) from fun x ↦ by change (1 / r) • (x + -x₀) = _; rw [sub_eq_add_neg],
          show ∀ x, (fderiv ℝ u x) ((1 / r) • (x - x₀)) = (fderiv ℝ u x) (x - x₀) * (1 / r) from fun x ↦ by rw [(fderiv ℝ u x).map_smul, smul_eq_mul, mul_comm]]
    _ = (1 / r^2) * ∫ (y : E) in sphere 0 1, (fderiv ℝ u (g.symm y)) y ∂(MeasureTheory.Measure.map g surfaceArea) := by
        rw [← (Homeomorph.measurableEmbedding g).integral_map (fun y ↦ (fderiv ℝ u (g.symm y)) y)]
        rw [MeasureTheory.Measure.restrict_map (Homeomorph.measurableEmbedding g).measurable isClosed_sphere.measurableSet, sphere_integral_preimage x₀ r hr]
    _ = ∫ (y : E) in sphere 0 1, (fderiv ℝ u (x₀ + r • y)) y ∂surfaceArea := by
        rw [sphere_integral_map_measure x₀ r hr, MeasureTheory.Measure.restrict_smul, MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg r), smul_eq_mul]
        rw [← mul_assoc, one_div, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul]
        simp_rw [g, sphere_integral_gsymm x₀ r hr]

lemma integrableOn_spherical_integrand (u : E → ℝ) (Ω : Set E) (x₀ : E) (R : ℝ) (r : ℝ)
    (hr : r ∈ Set.Ioo 0 R)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω) :
    IntegrableOn (fun y ↦ u (x₀ + r • y)) (sphere (0 : E) 1) surfaceArea := by
  have h_cont_comp : ContinuousOn (fun y ↦ u (x₀ + r • y)) (sphere (0 : E) 1) := by
    have h_mapsTo : Set.MapsTo (fun y ↦ x₀ + r • y) (sphere (0 : E) 1) (Metric.closedBall x₀ R) := fun y hy ↦ by
      simpa [dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp hy, Real.norm_of_nonneg hr.1.le] using hr.2.le
    exact (h_smooth.continuousOn.mono h_closed_ball).comp
      (continuous_const.add (continuous_id.const_smul r)).continuousOn h_mapsTo

  obtain ⟨C, hC⟩ := (isCompact_sphere 0 1).bddAbove_image h_cont_comp.norm
  haveI : IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) 1)) := isFiniteMeasure_sphere 1 Real.zero_lt_one

  refine MeasureTheory.Integrable.mono (MeasureTheory.integrable_const C)
    (h_cont_comp.aestronglyMeasurable isClosed_sphere.measurableSet) ?_
  rw [MeasureTheory.ae_restrict_iff' isClosed_sphere.measurableSet]
  exact Eventually.of_forall fun y hy ↦ by
    simpa [Real.norm_eq_abs] using (hC (Set.mem_image_of_mem _ hy)).trans (le_abs_self C)

/-!
### Radial and Spherical Derivatives
-/

lemma hasDerivAt_spherical_integrand (u : E → ℝ) (Ω : Set E) (x₀ : E) (R : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω) :
    ∃ u' : ℝ → E → ℝ, ∀ r' ∈ Set.Ioo 0 R, ∀ y ∈ sphere (0 : E) 1, HasDerivAt (fun s ↦ u (x₀ + s • y)) (u' r' y) r' := by
  refine ⟨fun r' y ↦ (fderiv ℝ u (x₀ + r' • y)) y, fun r' hr' y hy ↦ ?_⟩
  have h_in_open_ball : x₀ + r' • y ∈ Metric.ball x₀ R := by
    simpa [dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp hy, Real.norm_of_nonneg hr'.1.le] using hr'.2
  have h_diff_u : DifferentiableAt ℝ u (x₀ + r' • y) :=
    (h_smooth.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_ball.mem_nhds h_in_open_ball) (Metric.ball_subset_closedBall.trans h_closed_ball))
  have h_diff_affine : HasDerivAt (fun s ↦ x₀ + s • y) y r' := by
    simpa using ((hasDerivAt_id r').smul_const y).const_add x₀
  exact h_diff_u.hasFDerivAt.comp_hasDerivAt r' h_diff_affine

lemma spherical_integrand_deriv_eq_fderiv (u : E → ℝ) (Ω : Set E) (x₀ : E) (R : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (u' : ℝ → E → ℝ)
    (hu' : ∀ r' ∈ Set.Ioo 0 R, ∀ y ∈ sphere (0 : E) 1, HasDerivAt (fun s ↦ u (x₀ + s • y)) (u' r' y) r') :
    ∀ s ∈ Set.Ioo 0 R, ∀ y ∈ sphere (0 : E) 1, u' s y = (fderiv ℝ u (x₀ + s • y)) y := by
  intro s hs y hy
  have h_in_open : x₀ + s • y ∈ Metric.ball x₀ R := by
    simpa [dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp hy, Real.norm_of_nonneg hs.1.le] using hs.2
  have h_diff_u : DifferentiableAt ℝ u (x₀ + s • y) :=
    (h_smooth.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_ball.mem_nhds h_in_open) (Metric.ball_subset_closedBall.trans h_closed_ball))
  have h_diff_affine : HasDerivAt (fun t ↦ x₀ + t • y) y s := by
    simpa using ((hasDerivAt_id s).smul_const y).const_add x₀
  exact HasDerivAt.unique (hu' s hs y hy) (h_diff_u.hasFDerivAt.comp_hasDerivAt s h_diff_affine)

lemma deriv_integral_sphere_radius_meas (u : E → ℝ) (Ω : Set E) (x₀ : E) (R r : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 1 u Ω)
    (hr : r ∈ Set.Ioo 0 R) :
    ∀ᶠ s in 𝓝 r, AEStronglyMeasurable (fun y ↦ u (x₀ + s • y)) (surfaceArea.restrict (sphere (0 : E) 1)) := by
  filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
  exact (h_smooth.continuousOn.comp (continuous_const.add (continuous_id.const_smul s)).continuousOn
    (fun y hy ↦ h_closed_ball (affine_mem_closedBall x₀ hs.1.le hs.2.le hy)))
    |>.aestronglyMeasurable isClosed_sphere.measurableSet

lemma deriv_integral_sphere_radius_int (u : E → ℝ) (Ω : Set E) (x₀ : E) (R r : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 1 u Ω)
    (hr : r ∈ Set.Ioo 0 R) :
    Integrable (fun y ↦ u (x₀ + r • y)) (surfaceArea.restrict (sphere (0 : E) 1)) := by
  have h_cont := h_smooth.continuousOn.comp (continuous_const.add (continuous_id.const_smul r)).continuousOn
    (fun y hy ↦ h_closed_ball (affine_mem_closedBall x₀ hr.1.le hr.2.le hy))
  obtain ⟨C, hC⟩ := (isCompact_sphere 0 1).image_of_continuousOn (continuous_norm.comp_continuousOn h_cont) |>.bddAbove
  exact (integrable_const C).mono (h_cont.aestronglyMeasurable isClosed_sphere.measurableSet) <|
    (ae_restrict_iff' isClosed_sphere.measurableSet).mpr <|
      Filter.Eventually.of_forall fun y hy ↦ le_trans (hC (Set.mem_image_of_mem _ hy)) (le_abs_self C)

lemma deriv_integral_sphere_radius_deriv_meas (u : E → ℝ) (Ω : Set E) (x₀ : E) (R r : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_open : IsOpen Ω)
    (h_smooth : ContDiffOn ℝ 1 u Ω)
    (hr : r ∈ Set.Ioo 0 R) :
    AEStronglyMeasurable (fun y ↦ deriv (fun s' ↦ u (x₀ + s' • y)) r) (surfaceArea.restrict (sphere (0 : E) 1)) := by
  have h_cont := (h_smooth.continuousOn_fderiv_of_isOpen h_open le_rfl).comp
    (continuous_const.add (continuous_id.const_smul r)).continuousOn
    (fun y hy ↦ h_closed_ball (affine_mem_closedBall x₀ hr.1.le hr.2.le hy))
  exact (ContinuousOn.clm_apply h_cont continuousOn_id).aestronglyMeasurable isClosed_sphere.measurableSet |>.congr <| by
    filter_upwards [ae_restrict_mem isClosed_sphere.measurableSet] with y hy
    exact (deriv_comp_affine u Ω x₀ y r h_open h_smooth <|
      h_closed_ball <| Metric.ball_subset_closedBall <| affine_mem_ball x₀ hr hy).symm

lemma deriv_integral_sphere_radius_bound (u : E → ℝ) (Ω : Set E) (x₀ : E) (R r ε M : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_open : IsOpen Ω)
    (h_smooth : ContDiffOn ℝ 1 u Ω)
    (hε_subset : Metric.ball r ε ⊆ Set.Ioo 0 R)
    (hM_bound : ∀ s ∈ Set.Ioo 0 R, ∀ y ∈ sphere (0 : E) 1, ‖fderiv ℝ u (x₀ + s • y)‖ ≤ M) :
    ∀ᵐ y ∂(surfaceArea.restrict (sphere (0 : E) 1)), ∀ s ∈ Metric.ball r ε, ‖deriv (fun s' ↦ u (x₀ + s' • y)) s‖ ≤ M := by
  rw [ae_restrict_iff' isClosed_sphere.measurableSet]
  exact Filter.Eventually.of_forall fun y hy s hs ↦ by
    rw [deriv_comp_affine u Ω x₀ y s h_open h_smooth (h_closed_ball <| Metric.ball_subset_closedBall <| affine_mem_ball x₀ (hε_subset hs) hy)]
    exact (ContinuousLinearMap.le_opNorm _ y).trans <| by
      rw [mem_sphere_zero_iff_norm.mp hy, mul_one]
      exact hM_bound s (hε_subset hs) y hy

lemma deriv_integral_sphere_radius_diff (u : E → ℝ) (Ω : Set E) (x₀ : E) (R r ε : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_open : IsOpen Ω)
    (h_smooth : ContDiffOn ℝ 1 u Ω)
    (hε_subset : Metric.ball r ε ⊆ Set.Ioo 0 R) :
    ∀ᵐ y ∂(surfaceArea.restrict (sphere (0 : E) 1)), ∀ s ∈ Metric.ball r ε,
      HasDerivAt (fun s' ↦ u (x₀ + s' • y)) (deriv (fun s' ↦ u (x₀ + s' • y)) s) s := by
  rw [ae_restrict_iff' isClosed_sphere.measurableSet]
  exact Filter.Eventually.of_forall fun y hy s hs ↦
    ((h_smooth.differentiableOn (by exact Ne.symm (zero_ne_one' (WithTop ℕ∞)))).differentiableAt <|
      h_open.mem_nhds <| h_closed_ball <| Metric.ball_subset_closedBall <| affine_mem_ball x₀ (hε_subset hs) hy)
    |>.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_affine_radius x₀ y s)
    |>.differentiableAt.hasDerivAt

lemma deriv_integral_sphere_radius (u : E → ℝ) (Ω : Set E) (x₀ : E) (R r : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_open : IsOpen Ω)
    (h_smooth : ContDiffOn ℝ 1 u Ω)
    (hr : r ∈ Set.Ioo 0 R) :
    deriv (fun s ↦ ∫ (y : E) in sphere 0 1, u (x₀ + s • y) ∂surfaceArea) r =
      ∫ (y : E) in sphere 0 1, deriv (fun s ↦ u (x₀ + s • y)) r ∂surfaceArea := by
  obtain ⟨ε, hε_pos, hε_subset⟩ := Metric.isOpen_iff.mp isOpen_Ioo r hr
  obtain ⟨M, hM_bound⟩ := fderiv_bound_on_closedBall u Ω x₀ R h_closed_ball h_open h_smooth
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := surfaceArea.restrict (sphere 0 1))
    (F := fun s y ↦ u (x₀ + s • y))
    (F' := fun s y ↦ deriv (fun s' ↦ u (x₀ + s' • y)) s)
    (bound := fun _ ↦ M)
    (Metric.ball_mem_nhds r hε_pos)
    (deriv_integral_sphere_radius_meas u Ω x₀ R r h_closed_ball h_smooth hr)
    (deriv_integral_sphere_radius_int u Ω x₀ R r h_closed_ball h_smooth hr)
    (deriv_integral_sphere_radius_deriv_meas u Ω x₀ R r h_closed_ball h_open h_smooth hr)
    (deriv_integral_sphere_radius_bound u Ω x₀ R r ε M h_closed_ball h_open h_smooth hε_subset hM_bound)
    (integrable_const M)
    (deriv_integral_sphere_radius_diff u Ω x₀ R r ε h_closed_ball h_open h_smooth hε_subset)).2.deriv

lemma deriv_spherical_mean (u : E → ℝ) (Ω : Set E) (x₀ : E) (R r : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_open : IsOpen Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (hr : r ∈ Set.Ioo 0 R) :
    deriv (fun s ↦ 1 / (4 * π * s ^ 2) * ∫ (x : E) in sphere x₀ s, u x ∂surfaceArea) r =
      (1 / (4 * π)) * ∫ y in sphere 0 1, (fderiv ℝ u (x₀ + r • y) y) ∂surfaceArea := by
  have h_ev_eq : (fun s ↦ 1 / (4 * π * s ^ 2) * ∫ (x : E) in sphere x₀ s, u x ∂surfaceArea) =ᶠ[𝓝 r]
      (fun s ↦ 1 / (4 * π) * ∫ (y : E) in sphere 0 1, u (x₀ + s • y) ∂surfaceArea) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    rw [integral_sphere_change_vars x₀ s hs.1 u, ← mul_assoc]
    congr 1
    have hs_ne : s ≠ 0 := hs.1.ne'
    have hπ_ne : π ≠ 0 := Real.pi_ne_zero
    field_simp

  rw [Filter.EventuallyEq.deriv_eq h_ev_eq]
  simp only [deriv_const_mul_field']
  congr 1
  rw [deriv_integral_sphere_radius u Ω x₀ R r h_closed_ball h_open (h_smooth.of_le (by norm_num)) hr]

  apply integral_congr_ae
  filter_upwards [ae_restrict_mem isClosed_sphere.measurableSet] with y hy
  exact deriv_comp_affine u Ω x₀ y r h_open (h_smooth.of_le (by norm_num)) <|
    h_closed_ball <| Metric.ball_subset_closedBall <| affine_mem_ball x₀ hr hy

/-!
### Spherical Mean Bounds
-/

lemma spherical_integrand_deriv_bound (u : E → ℝ) (Ω : Set E) (h_open : IsOpen Ω) (x₀ : E) (R : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (u' : ℝ → E → ℝ)
    (hu' : ∀ r' ∈ Set.Ioo 0 R, ∀ y ∈ sphere (0 : E) 1, HasDerivAt (fun s ↦ u (x₀ + s • y)) (u' r' y) r') :
    ∃ M : ℝ, IntegrableOn (fun _ : E ↦ M) (sphere (0 : E) 1) surfaceArea ∧ ∀ r' ∈ Set.Ioo 0 R, ∀ᵐ y ∂(surfaceArea.restrict (sphere 0 1)), ‖u' r' y‖ ≤ M := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ Metric.closedBall x₀ R, ‖fderiv ℝ u x‖ ≤ C := by
    have h_cont_deriv := (ContDiffOn.continuousOn_fderiv_of_isOpen h_smooth h_open (by norm_num)).mono h_closed_ball
    obtain ⟨C, hC_bdd⟩ := (isCompact_closedBall x₀ R).bddAbove_image h_cont_deriv.norm
    exact ⟨C, fun x hx ↦ hC_bdd (Set.mem_image_of_mem _ hx)⟩

  refine ⟨C, ?_, fun r' hr' ↦ ?_⟩
  · haveI : IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) 1)) := isFiniteMeasure_sphere 1 Real.zero_lt_one
    exact MeasureTheory.integrable_const C
  · rw [MeasureTheory.ae_restrict_iff' isClosed_sphere.measurableSet]
    refine Eventually.of_forall fun y hy ↦ ?_
    have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
    have h_in_ball : x₀ + r' • y ∈ Metric.closedBall x₀ R := by
      simpa [dist_eq_norm, norm_smul, hy_norm, Real.norm_of_nonneg hr'.1.le] using hr'.2.le
    have h_diff_u : DifferentiableAt ℝ u (x₀ + r' • y) := by
      have h_in_open : x₀ + r' • y ∈ Metric.ball x₀ R := by
        simpa [dist_eq_norm, norm_smul, hy_norm, Real.norm_of_nonneg hr'.1.le] using hr'.2
      exact (h_smooth.differentiableOn (by norm_num)).differentiableAt
        (Filter.mem_of_superset (isOpen_ball.mem_nhds h_in_open) (Metric.ball_subset_closedBall.trans h_closed_ball))
    have h_diff_affine : HasDerivAt (fun s ↦ x₀ + s • y) y r' := by simpa using ((hasDerivAt_id r').smul_const y).const_add x₀
    rw [HasDerivAt.unique (hu' r' hr' y hy) (h_diff_u.hasFDerivAt.comp_hasDerivAt r' h_diff_affine)]
    calc ‖(fderiv ℝ u (x₀ + r' • y)) y‖
      _ ≤ ‖fderiv ℝ u (x₀ + r' • y)‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ y
      _ = ‖fderiv ℝ u (x₀ + r' • y)‖ := by rw [hy_norm, mul_one]
      _ ≤ C := hC (x₀ + r' • y) h_in_ball

lemma differentiableOn_spherical_mean (u : E → ℝ) (Ω : Set E) (h_open : IsOpen Ω) (x₀ : E) (R : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω) :
    DifferentiableOn ℝ (fun r ↦ 1 / (4 * π * r ^ 2) * ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea) (Set.Ioo 0 R) := by
  refine DifferentiableOn.congr ?_ (spherical_mean_eqOn u x₀ R)

  have h_param_integral : DifferentiableOn ℝ (fun r ↦ ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea) (Set.Ioo 0 R) := fun r hr ↦ by
    obtain ⟨u', hu'⟩ := hasDerivAt_spherical_integrand u Ω x₀ R h_closed_ball h_smooth
    obtain ⟨ε, hε_pos, hε_subset⟩ := Metric.isOpen_iff.mp isOpen_Ioo r hr

    have h_cont_deriv := (ContDiffOn.continuousOn_fderiv_of_isOpen h_smooth h_open (by norm_num)).mono h_closed_ball
    obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ R).bddAbove_image h_cont_deriv.norm
    haveI : IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) 1)) := isFiniteMeasure_sphere 1 Real.zero_lt_one

    have h_has_deriv : HasDerivAt (fun r ↦ ∫ y in sphere (0:E) 1, u (x₀ + r • y) ∂surfaceArea)
        (∫ y in sphere (0:E) 1, u' r y ∂surfaceArea) r :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (E := ℝ) (α := E)
        (μ := surfaceArea.restrict (sphere 0 1))
        (F := fun r y ↦ u (x₀ + r • y))
        (F' := u')
        (x₀ := r)
        (Metric.ball_mem_nhds r hε_pos) ?_
        (integrableOn_spherical_integrand u Ω x₀ R r hr h_closed_ball h_smooth)
        ?_ ?_ (MeasureTheory.integrable_const C) ?_).2
    exact h_has_deriv.differentiableAt.differentiableWithinAt

    · exact Filter.eventually_of_mem (Metric.ball_mem_nhds r hε_pos) fun s hs_mem ↦ by
        have hs_Ioo := hε_subset hs_mem
        have h_mapsTo : Set.MapsTo (fun y ↦ x₀ + s • y) (sphere (0 : E) 1) (Metric.closedBall x₀ R) := fun y hy ↦ by
          simpa [dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp hy, Real.norm_of_nonneg hs_Ioo.1.le] using hs_Ioo.2.le
        exact ((h_smooth.continuousOn.mono h_closed_ball).comp (continuous_const.add (continuous_id.const_smul s)).continuousOn h_mapsTo).aestronglyMeasurable isClosed_sphere.measurableSet

    · have h_mapsTo : Set.MapsTo (fun y ↦ x₀ + r • y) (sphere (0 : E) 1) (Metric.closedBall x₀ R) := fun y hy ↦ by
        simpa [dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp hy, Real.norm_of_nonneg hr.1.le] using hr.2.le
      have h_aesm : AEStronglyMeasurable (fun y ↦ fderiv ℝ u (x₀ + r • y) y)
          (surfaceArea.restrict (sphere 0 1)) :=
        ((h_cont_deriv.comp (continuous_const.add (continuous_id.const_smul r)).continuousOn
          h_mapsTo).clm_apply continuousOn_id).aestronglyMeasurable isClosed_sphere.measurableSet
      refine MeasureTheory.AEStronglyMeasurable.congr h_aesm ?_
      filter_upwards [ae_restrict_mem isClosed_sphere.measurableSet] with y hy
      exact (spherical_integrand_deriv_eq_fderiv u Ω x₀ R h_closed_ball h_smooth u' hu' r hr y hy).symm

    · rw [MeasureTheory.ae_restrict_iff' isClosed_sphere.measurableSet]
      exact Eventually.of_forall fun y hy s hs_mem ↦ by
        have hs_Ioo := hε_subset hs_mem
        rw [spherical_integrand_deriv_eq_fderiv u Ω x₀ R h_closed_ball h_smooth u' hu' s hs_Ioo y hy]
        have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
        have h_in_ball : x₀ + s • y ∈ Metric.closedBall x₀ R := by
          simpa [dist_eq_norm, norm_smul, hy_norm, Real.norm_of_nonneg hs_Ioo.1.le] using hs_Ioo.2.le
        exact (ContinuousLinearMap.le_opNorm _ y).trans (by rw [hy_norm, mul_one]; exact hC (Set.mem_image_of_mem _ h_in_ball))

    · rw [MeasureTheory.ae_restrict_iff' isClosed_sphere.measurableSet]
      exact Eventually.of_forall fun y hy s hs_mem ↦ hu' s (hε_subset hs_mem) y hy

  exact h_param_integral.const_mul (1 / (4 * π))

/-!
### Divergence Theorem and Green's Second Identity
-/

lemma divergence_theorem (F : E → E) (s : Set E) (n : E → E)
    [HasDivergenceTheoremDomain s]
    [InnerProductSpace ℝ E]
    [MeasureSpace E]
    (hn_normal : IsOutwardUnitNormal s n)
    (h_smooth : ContDiffOn ℝ 1 F (closure s)) :
    ∫ x in s, div_field F x ∂volume =
    ∫ x in frontier s, (⟪F x, n x⟫_ℝ) ∂(Measure.hausdorffMeasure (Module.finrank ℝ E - 1)) := by
  sorry

lemma greens_second_identity_annulus_gen (Ω : Set E) [HasPDEDomain Ω] (n_Omega : E → E)
  (h_norm_Omega : IsOutwardUnitNormal Ω n_Omega)
  (h_cont_nΩ : ContinuousOn n_Omega (frontier Ω)) (x₀ : E) (ε : ℝ) (hε : 0 < ε)
  (h_subset : Metric.closedBall x₀ ε ⊆ Ω) (h_bound : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤) (u v : E → ℝ)
  (hu : ContDiffOn ℝ 2 u (closure (Ω \ Metric.closedBall x₀ ε)))
  (hv : ContDiffOn ℝ 2 v (closure (Ω \ Metric.closedBall x₀ ε))) :
  ∫ x in Ω \ Metric.closedBall x₀ ε, (v x * laplacianWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x - u x * laplacianWithin v (closure (Ω \ Metric.closedBall x₀ ε)) x) =
  (∫ x in frontier Ω, (v x * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n_Omega x⟫_ℝ - u x * ⟪gradientWithin v (closure (Ω \ Metric.closedBall x₀ ε)) x, n_Omega x⟫_ℝ) ∂surfaceArea) +
  ∫ x in Metric.sphere x₀ ε, (v x * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ - u x * ⟪gradientWithin v (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ) ∂surfaceArea := by
  let U := Ω \ Metric.closedBall x₀ ε
  let n_total : E → E := fun x => if x ∈ frontier Ω then n_Omega x else -(1 / ε) • (x - x₀)
  let F : E → E := fun x => v x • gradientWithin u (closure U) x - u x • gradientWithin v (closure U) x
  let f : E → ℝ := fun x => v x * ⟪gradientWithin u (closure U) x, n_total x⟫_ℝ - u x * ⟪gradientWithin v (closure U) x, n_total x⟫_ℝ

  have h_pde_U := annulus_has_pde_domain_gen Ω x₀ ε hε h_subset
  have hU_open := h_pde_U.is_open
  have h_smooth_F := contDiffOn_greens_F U h_pde_U.unique_diff u v hu hv

  have h_grad_eq : ∀ y ∈ U, F y = v y • gradient u y - u y • gradient v y := fun y hy => by
    have h_nhds : closure U ∈ nhds y := Filter.mem_of_superset ((h_pde_U.is_open).mem_nhds hy) subset_closure
    dsimp [F]; unfold gradientWithin gradient
    rw [fderivWithin_of_mem_nhds h_nhds, fderivWithin_of_mem_nhds h_nhds]

  have h_div_rule : ∀ x ∈ U, div_field F x = v x * laplacianWithin u (closure U) x - u x * laplacianWithin v (closure U) x := fun x hx => by
    unfold div_field
    rw [← fderivWithin_eq_fderiv_of_isOpen F U h_pde_U.is_open x hx,
        fderivWithin_congr (fun y hy => h_grad_eq y hy) (h_grad_eq x hx),
        fderivWithin_eq_fderiv_of_isOpen _ U h_pde_U.is_open x hx]
    change div_field (fun y => v y • gradient u y - u y • gradient v y) x = _
    rw [div_field_greens_identity_on U h_pde_U.is_open u v hu hv x hx,
        laplacianWithin_closure_eq_laplacian u U h_pde_U.is_open x hx,
        laplacianWithin_closure_eq_laplacian v U h_pde_U.is_open x hx]

  have h_norm_U : IsOutwardUnitNormal U n_total := by sorry
  have h_thm := divergence_theorem F U n_total h_norm_U h_smooth_F
  rw [show (Measure.hausdorffMeasure (Module.finrank ℝ E - 1) : Measure E) = surfaceArea by dsimp [surfaceArea]; rw [finrank_euclideanSpace]; norm_num] at h_thm

  have h_F_f : ∀ x ∈ frontier U, ⟪F x, n_total x⟫_ℝ = f x := fun x _ => by
    dsimp [f, F]; rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]

  rw [setIntegral_congr_fun h_pde_U.is_open.measurableSet h_div_rule,
      setIntegral_congr_fun isClosed_frontier.measurableSet h_F_f] at h_thm

  have h_front := frontier_diff_closedBall_gen Ω x₀ ε hε h_subset
  have h_disj : Disjoint (frontier Ω) (Metric.sphere x₀ ε) :=
    Set.disjoint_left.mpr fun x hx hx_sph => hx.2 ((HasPDEDomain.is_open (s := Ω)).interior_eq.symm ▸ h_subset (Metric.sphere_subset_closedBall hx_sph))

  have h_meas_sphere : surfaceArea (Metric.sphere x₀ ε) < ⊤ := by
    let g : E ≃ᵢ E := IsometryEquiv.addRight x₀
    have hg_surj : Function.Surjective g := fun y ↦ ⟨y - x₀, sub_add_cancel y x₀⟩
    have hg_emb : MeasurableEmbedding g := (Homeomorph.addRight x₀).measurableEmbedding
    have h_map : MeasureTheory.Measure.map g surfaceArea = surfaceArea := by
      erw [Isometry.map_hausdorffMeasure (isometry_add_right x₀) (Or.inr hg_surj)]
      have h_range : Set.range (fun x ↦ x + x₀) = Set.univ := Set.range_eq_univ.mpr hg_surj
      rw [h_range, MeasureTheory.Measure.restrict_univ]
      rfl
    rw [← h_map, MeasureTheory.Measure.map_apply hg_emb.measurable isClosed_sphere.measurableSet]
    have h_preimage : g ⁻¹' Metric.sphere x₀ ε = Metric.sphere 0 ε := by
      ext y
      simp [g]
    rw [h_preimage]
    exact measure_sphere_lt_top ε hε

  have h_int_S : IntegrableOn f (Metric.sphere x₀ ε) surfaceArea := by
    have h_f : Set.EqOn f (fun x => ⟪F x, -(1 / ε) • (x - x₀)⟫_ℝ) (Metric.sphere x₀ ε) :=
      fun x hx => by dsimp [f, F, n_total]; rw [if_neg (Set.disjoint_right.mp h_disj hx), inner_sub_left, real_inner_smul_left, real_inner_smul_left]
    have h_cont : ContinuousOn (fun x => ⟪F x, -(1 / ε) • (x - x₀)⟫_ℝ) (Metric.sphere x₀ ε) :=
      ContinuousOn.inner (h_smooth_F.continuousOn.mono fun x hx => frontier_subset_closure (h_front ▸ Or.inr hx)) (((continuous_id.sub continuous_const).const_smul (-(1 / ε))).continuousOn)
    exact (integrableOn_of_continuousOn_compact_finite_measure (isCompact_sphere x₀ ε) isClosed_sphere.measurableSet h_meas_sphere h_cont).congr_fun h_f.symm isClosed_sphere.measurableSet

  have h_int_Ω : IntegrableOn f (frontier Ω) surfaceArea :=
    integrableOn_greens_f_frontier_within_gen Ω n_total x₀ ε hε h_subset u v h_bound h_area hu hv
      (h_cont_nΩ.congr fun x hx => by simp only [n_total, if_pos hx])

  rw [h_thm, h_front, setIntegral_union h_disj isClosed_sphere.measurableSet h_int_Ω h_int_S]
  congr 1
  · exact setIntegral_congr_fun isClosed_frontier.measurableSet fun x hx => by dsimp [f, n_total]; rw [if_pos hx]
  · exact setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx => by dsimp [f, n_total]; rw [if_neg (fun h => h_disj.le_bot ⟨h, hx⟩)]
