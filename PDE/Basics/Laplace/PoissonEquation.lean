import PDE.Basics.Laplace.FundamentalSolution

open MeasureTheory Set Metric Filter
open scoped Real Topology ContDiff

noncomputable def fundamental_sol_3d (x : E) : ℝ :=
  -1 / (4 * Real.pi * ‖x‖)

lemma fundamental_sol_norm_eq (y : E) :
  ‖fundamental_sol_3d y‖ = (1 / (4 * Real.pi)) * (1 / ‖y‖) := by
  unfold fundamental_sol_3d
  rw [Real.norm_eq_abs, abs_div, abs_neg, abs_one, abs_of_nonneg (by positivity)]
  exact div_mul_eq_div_mul_one_div 1 (4 * π) ‖y‖

lemma integrableOn_fundamental_sol_bound (R M : ℝ) (hR : 0 < R) :
  IntegrableOn (fun y : E => ‖fundamental_sol_3d y‖ * M) (Metric.ball (0 : E) R) volume := by
  simp_rw [fundamental_sol_norm_eq]
  exact ((inv_norm_integrableOn_ball R hR).const_mul (1 / (4 * Real.pi))).mul_const M

lemma fundamental_sol_bound_integrable (R M : ℝ) (hR : 0 < R) :
  Integrable (fun y : E => ‖fundamental_sol_3d y‖ * M * (Set.indicator (Metric.ball (0 : E) R) (fun _ => (1 : ℝ)) y)) volume := by
  rw [funext fun y => indicator_mul_one_eq (fun y' => ‖fundamental_sol_3d y'‖ * M) R y, integrable_indicator_equiv]
  exact integrableOn_fundamental_sol_bound R M hR

lemma fundamental_sol_ae_measurable : AEStronglyMeasurable fundamental_sol_3d volume := by
  unfold fundamental_sol_3d
  exact Measurable.aestronglyMeasurable (Measurable.div measurable_const (Measurable.mul measurable_const (Continuous.measurable continuous_norm)))

lemma shifted_f_ae_measurable (f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (x' : E) :
  AEStronglyMeasurable (fun y => f (x' - y)) volume := by
  exact Continuous.aestronglyMeasurable (hf_smooth.continuous.comp (continuous_const.sub continuous_id))

lemma ae_measurable_conv (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (x : E) :
  ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (fun y => Φ y * f (x' - y)) volume := by
  apply Eventually.of_forall
  intro x'
  rw [hΦ]
  exact fundamental_sol_ae_measurable.mul (shifted_f_ae_measurable f hf_smooth x')

lemma integrable_conv (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E) :
  Integrable (fun y => Φ y * f (x - y)) volume := by
  rcases conv_pointwise_bound f hf_smooth hf_supp x with ⟨R_supp, M, h_f_bound⟩
  let R_pos := max R_supp 1
  have hR_pos : 0 < R_pos := lt_max_iff.mpr (Or.inr zero_lt_one)
  let M_pos := max M 0
  rw [hΦ]
  exact (fundamental_sol_bound_integrable R_pos M_pos hR_pos).mono'
    (fundamental_sol_ae_measurable.mul (shifted_f_ae_measurable f hf_smooth x))
    (Eventually.of_forall (fun y => by
      rw [norm_mul, mul_assoc]
      refine le_trans (mul_le_mul_of_nonneg_left (h_f_bound y) (norm_nonneg _)) ?_
      apply mul_le_mul_of_nonneg_left
      · by_cases hy : y ∈ Metric.ball (0 : E) R_supp
        · have hy_pos : y ∈ Metric.ball (0 : E) R_pos := Metric.ball_subset_ball (le_max_left R_supp 1) hy
          simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hy_pos, mul_one]
          exact le_max_left M 0
        · by_cases hy_pos : y ∈ Metric.ball (0 : E) R_pos
          · simp only [Set.indicator_of_notMem hy, Set.indicator_of_mem hy_pos, mul_zero, mul_one]
            exact le_max_right M 0
          · simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy_pos, mul_zero];simp
      · exact norm_nonneg _))

lemma grad_integrable_bound (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E) :
  ∃ (bound : E → ℝ), Integrable bound volume ∧ ∀ᶠ x' in 𝓝 x, ∀ y, ‖gradient (fun x'' => Φ y * f (x'' - y)) x'‖ ≤ bound y := by
  rcases shifted_gradient_bound f hf_smooth hf_supp with ⟨M, hM⟩
  rcases convolution_support_in_ball f hf_supp x 1 with ⟨R_supp, hR_supp⟩
  let R_pos := max R_supp 1
  have hR_pos : 0 < R_pos := lt_max_iff.mpr (Or.inr zero_lt_one)
  use fun y : E => ‖fundamental_sol_3d y‖ * M * Set.indicator (Metric.ball (0 : E) R_pos) (fun _ => (1 : ℝ)) y
  constructor
  · exact fundamental_sol_bound_integrable R_pos M hR_pos
  · apply Filter.eventually_of_mem (U := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos)
    intro x' hx' y
    rw [hΦ, gradient_const_mul fundamental_sol_3d f hf_smooth y x', norm_smul]
    by_cases hy : y ∈ Metric.ball (0 : E) R_pos
    · simp only [Set.indicator_of_mem hy, mul_one]
      exact mul_le_mul_of_nonneg_left (hM x' y) (norm_nonneg _)
    · simp only [Set.indicator_of_notMem hy, mul_zero]
      have hy_supp : y ∉ Metric.ball (0 : E) R_supp :=
        fun h => hy (Metric.ball_subset_ball (le_max_left R_supp 1) h)
      rw [gradient_zero_of_outside_support f x y 1 R_supp hR_supp x' hx' hy_supp]
      simp only [Real.norm_eq_abs, norm_zero, mul_zero, le_refl]

lemma fderiv_grad_integrable_bound (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E) :
  ∃ (bound : E → ℝ), Integrable bound volume ∧ ∀ᶠ x' in 𝓝 x, ∀ y, ‖fderiv ℝ (fun x'' => gradient (fun x''' => Φ y * f (x''' - y)) x'') x'‖ ≤ bound y := by
  rcases shifted_fderiv_gradient_bound f hf_smooth hf_supp with ⟨M, hM⟩
  rcases convolution_support_in_ball f hf_supp x 1 with ⟨R_supp, hR_supp⟩
  let R_pos := max R_supp 1
  have hR_pos : 0 < R_pos := lt_max_iff.mpr (Or.inr zero_lt_one)
  use fun y : E => ‖fundamental_sol_3d y‖ * M * Set.indicator (Metric.ball (0 : E) R_pos) (fun _ => (1 : ℝ)) y
  constructor
  · exact fundamental_sol_bound_integrable R_pos M hR_pos
  · apply Filter.eventually_of_mem (U := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos)
    intro x' hx' y
    rw [hΦ, fderiv_gradient_const_mul fundamental_sol_3d f hf_smooth y x', norm_smul]
    by_cases hy : y ∈ Metric.ball (0 : E) R_pos
    · simp only [Set.indicator_of_mem hy, mul_one]
      exact mul_le_mul_of_nonneg_left (hM x' y) (norm_nonneg _)
    · simp only [Set.indicator_of_notMem hy, mul_zero]
      have hy_supp : y ∉ Metric.ball (0 : E) R_supp :=
        fun h => hy (Metric.ball_subset_ball (le_max_left R_supp 1) h)
      rw [fderiv_gradient_zero_of_outside_support f x y 1 R_supp hR_supp x' hx' hy_supp]
      simp only [Real.norm_eq_abs, norm_zero, mul_zero, le_refl]

lemma ae_measurable_fderiv_conv (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (x : E) :
  AEStronglyMeasurable (fun y => fderiv ℝ (fun x' => Φ y * f (x' - y)) x) volume := by
  have h_eq : (fun y => fderiv ℝ (fun x' => Φ y * f (x' - y)) x) = fun y => Φ y • fderiv ℝ f (x - y) := by
    funext y
    rw [show (fun x' => Φ y * f (x' - y)) = Φ y • (fun x' => f (x' - y)) by ext; simp [smul_eq_mul],
        fderiv_const_smul (diff_shifted_f f hf_smooth y x) (Φ y),
        fderiv_shifted f x y]
  rw [h_eq]
  have h_meas_Phi : AEStronglyMeasurable Φ volume := by
    rw [hΦ]
    exact fundamental_sol_ae_measurable
  exact AEStronglyMeasurable.smul h_meas_Phi
    ((hf_smooth.continuous_fderiv (by exact WithTop.top_ne_zero)).comp (continuous_const.sub continuous_id)).aestronglyMeasurable

lemma fderiv_integral_swap_conv (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E)
  (bound : E → ℝ) (h_bound_int : Integrable bound volume)
  (h_bound : ∀ᶠ x' in 𝓝 x, ∀ y, ‖gradient (fun x'' => Φ y * f (x'' - y)) x'‖ ≤ bound y) :
  fderiv ℝ (fun x' => ∫ y, Φ y * f (x' - y)) x = ∫ y, fderiv ℝ (fun x' => Φ y * f (x' - y)) x := by
  rcases Metric.eventually_nhds_iff_ball.mp (h_bound.mono (fun x' hx' y =>
    show ‖fderiv ℝ (fun x'' => Φ y * f (x'' - y)) x'‖ ≤ bound y by
      rw [fderiv_norm_eq_gradient_norm]
      exact hx' y)) with ⟨ε, hε_pos, h_bound_ball⟩
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds x hε_pos)
    (ae_measurable_conv Φ f hΦ hf_smooth x)
    (integrable_conv Φ f hΦ hf_smooth hf_supp x)
    (ae_measurable_fderiv_conv Φ f hΦ hf_smooth x)
    (Eventually.of_forall (fun y x' hx' => h_bound_ball x' hx' y))
    h_bound_int
    (Eventually.of_forall (fun y x' _ => (integrand_differentiable Φ f hf_smooth y x').hasFDerivAt))).fderiv

lemma gradient_convolution_pass (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E) :
  gradient (fun x' => ∫ y : E, Φ y * f (x' - y)) x = ∫ y : E, gradient (fun x' => Φ y * f (x' - y)) x := by
  rcases grad_integrable_bound Φ f hΦ hf_smooth hf_supp x with ⟨bound, h_bound_int, h_bound_nhds⟩
  have hε : ∃ ε > 0, ∀ᵐ y ∂volume, ∀ x' ∈ Metric.ball x ε, ‖fderiv ℝ (fun x'' => Φ y * f (x'' - y)) x'‖ ≤ bound y := by
    rcases Metric.eventually_nhds_iff_ball.mp (h_bound_nhds.mono (fun x' hx' y =>
      show ‖fderiv ℝ (fun x'' => Φ y * f (x'' - y)) x'‖ ≤ bound y by rw [fderiv_norm_eq_gradient_norm]; exact hx' y)) with ⟨ε, hε_pos, h_bound_ball⟩
    exact ⟨ε, hε_pos, Eventually.of_forall (fun y x' hx' => h_bound_ball x' hx' y)⟩
  exact gradient_integral_of_dominated (fun x' y => Φ y * f (x' - y)) x bound hε h_bound_int
    (integrable_conv Φ f hΦ hf_smooth hf_supp x)
    (ae_measurable_conv Φ f hΦ hf_smooth x)
    (ae_measurable_fderiv_conv Φ f hΦ hf_smooth x)
    (Eventually.of_forall (fun y x' _ => (integrand_differentiable Φ f hf_smooth y x').hasFDerivAt))

lemma ae_measurable_gradient_conv (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (x : E) :
  ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (fun y => gradient (fun x'' => Φ y * f (x'' - y)) x') volume := by
  apply Eventually.of_forall
  intro x'
  have h_eq : (fun y => gradient (fun x'' => Φ y * f (x'' - y)) x') = fun y => Φ y • gradient f (x' - y) := by
    funext y
    rw [gradient_const_mul Φ f hf_smooth y x', gradient_shifted f x' y]
  rw [h_eq]
  have h_meas_Phi : AEStronglyMeasurable Φ volume := by
    rw [hΦ]
    exact fundamental_sol_ae_measurable
  exact AEStronglyMeasurable.smul h_meas_Phi
    (((diff_gradient f hf_smooth).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)

lemma integrable_gradient_conv (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E) :
  Integrable (fun y => gradient (fun x'' => Φ y * f (x'' - y)) x) volume := by
  rcases grad_integrable_bound Φ f hΦ hf_smooth hf_supp x with ⟨bound, h_bound_int, h_bound_nhds⟩
  exact h_bound_int.mono' (ae_measurable_gradient_conv Φ f hΦ hf_smooth x).self_of_nhds (Eventually.of_forall h_bound_nhds.self_of_nhds)

lemma ae_measurable_fderiv_gradient_conv (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (x : E) :
  AEStronglyMeasurable (fun y => fderiv ℝ (fun x' => gradient (fun x'' => Φ y * f (x'' - y)) x') x) volume := by
  simp_rw [fderiv_gradient_const_mul Φ f hf_smooth, fderiv_gradient_shifted_eq]
  exact AEStronglyMeasurable.smul (hΦ.symm ▸ fundamental_sol_ae_measurable)
    ((continuous_fderiv_gradient f hf_smooth).comp (continuous_const.sub continuous_id)).aestronglyMeasurable

lemma fderiv_gradient_integral_swap_conv (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E) :
  fderiv ℝ (fun x' => ∫ y, gradient (fun x'' => Φ y * f (x'' - y)) x') x = ∫ y, fderiv ℝ (fun x' => gradient (fun x'' => Φ y * f (x'' - y)) x') x := by
  rcases fderiv_grad_integrable_bound Φ f hΦ hf_smooth hf_supp x with ⟨bound, h_bound_int, h_bound_nhds⟩
  rcases Metric.eventually_nhds_iff_ball.mp h_bound_nhds with ⟨ε, hε_pos, h_bound_ball⟩
  have h_diff : ∀ᵐ y ∂volume, ∀ x' ∈ Metric.ball x ε, HasFDerivAt (fun x'' => gradient (fun x''' => Φ y * f (x''' - y)) x'') (fderiv ℝ (fun x'' => gradient (fun x''' => Φ y * f (x''' - y)) x'') x') x' :=
    Eventually.of_forall fun y x' _ => by
      simp_rw [gradient_const_mul Φ f hf_smooth y]
      exact ((diff_gradient_shifted f hf_smooth y x').const_smul (Φ y)).hasFDerivAt
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds x hε_pos)
    (ae_measurable_gradient_conv Φ f hΦ hf_smooth x)
    (integrable_gradient_conv Φ f hΦ hf_smooth hf_supp x)
    (ae_measurable_fderiv_gradient_conv Φ f hΦ hf_smooth x)
    (Eventually.of_forall fun y x' hx' => h_bound_ball x' hx' y)
    h_bound_int h_diff).fderiv

lemma integrable_fderiv_gradient_conv (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E) :
  Integrable (fun y => fderiv ℝ (fun x' => gradient (fun x'' => Φ y * f (x'' - y)) x') x) volume := by
  rcases fderiv_grad_integrable_bound Φ f hΦ hf_smooth hf_supp x with ⟨bound, h_bound_int, h_bound_nhds⟩
  exact h_bound_int.mono' (ae_measurable_fderiv_gradient_conv Φ f hΦ hf_smooth x) (Eventually.of_forall h_bound_nhds.self_of_nhds)

lemma laplacian_convolution_pass (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E) :
  laplacian (fun x' => ∫ y : E, Φ y * f (x' - y)) x = ∫ y : E, Φ y * laplacian (fun x' => f (x' - y)) x := by
  unfold laplacian div_field
  rw [funext (fun x' => gradient_convolution_pass Φ f hΦ hf_smooth hf_supp x'),
      fderiv_gradient_integral_swap_conv Φ f hΦ hf_smooth hf_supp x,
      trace_integral_swap _ (integrable_fderiv_gradient_conv Φ f hΦ hf_smooth hf_supp x)]
  congr 1
  ext y
  exact laplacian_const_sub_mul Φ f hf_smooth y x

lemma eval_fundamental_sol (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E) :
  ∫ y : E, Φ y * laplacian (fun y' => f (x - y')) y = f x := by
  rw [hΦ]
  have h_integrand : (fun y => fundamental_sol_3d y * laplacian (fun y' => f (x - y')) y) = fun y => (-1 / (4 * Real.pi)) * ((1 / ‖y‖) * laplacian (fun y' => f (x - y')) y) := by
    ext y; unfold fundamental_sol_3d; ring
  rw [h_integrand, integral_const_mul]
  erw [dist_laplacian_inv_norm (fun y => f (x - y)) (hf_smooth.comp (contDiff_const.sub contDiff_id)) (hf_supp.comp_homeomorph (Homeomorph.subLeft x))]
  change (-1 / (4 * Real.pi)) * (-4 * Real.pi * f (x - 0)) = f x
  rw [sub_zero]
  field_simp

theorem poisson_solution_3d (Φ f : E → ℝ) (hΦ : Φ = fundamental_sol_3d) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E) :
  laplacian (fun x' => convolution Φ f x') x = f x := by
  change laplacian (fun x' => ∫ y : E, Φ y * f (x' - y)) x = f x
  rw [laplacian_convolution_pass Φ f hΦ hf_smooth hf_supp x]
  simp_rw [laplacian_translation_symmetry f hf_smooth x]
  exact eval_fundamental_sol Φ f hΦ hf_smooth hf_supp x
