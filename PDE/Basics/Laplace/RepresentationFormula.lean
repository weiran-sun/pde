import PDE.Basics.Laplace.PoissonEquation

open Real Set MeasureTheory Metric Filter Function Pointwise InnerProductSpace RealInnerProductSpace
open scoped BigOperators Topology

lemma laplacian_Phi_shift_zero (Φ : E → ℝ) (hΦ : ∀ x, Φ x = -1 / (4 * Real.pi * ‖x‖))
    (x₀ x : E) (hx_ne_x0 : x ≠ x₀) :
    laplacian (fun y => Φ (y - x₀)) x = 0 := by
  have : (fun y => Φ (y - x₀)) = fun y => (-1 / (4 * Real.pi)) * (1 / ‖y - x₀‖) := by ext; rw [hΦ]; ring
  rw [this, laplacian_const_mul _ _ x (contDiffAt_inv_norm_sub x₀ x hx_ne_x0),
    laplacian_inv_norm_shift x₀ x hx_ne_x0, laplacian_inv_norm_eq_zero (sub_ne_zero.mpr hx_ne_x0), mul_zero]

lemma diff_Phi_at (x₀ x : E) (hx_ne : x - x₀ ≠ 0) (Φ : E → ℝ) (hΦ : ∀ y, Φ y = -1 / (4 * Real.pi * ‖y‖)) :
  DifferentiableAt ℝ (fun y => Φ (y - x₀)) x := by
  have h_eq : (fun y => Φ (y - x₀)) = fun y => -1 * (4 * Real.pi * ‖y - x₀‖)⁻¹ := by
    exact (eqOn_univ (fun y ↦ Φ (y - x₀)) fun y ↦ -1 * (4 * π * ‖y - x₀‖)⁻¹).mp fun ⦃x⦄ a ↦ hΦ (x - x₀)
  rw [h_eq]
  exact (differentiableAt_const (-1 : ℝ)).mul (((differentiableAt_const (4 * Real.pi)).mul (DifferentiableAt.norm ℝ (differentiableAt_id.sub (differentiableAt_const x₀)) hx_ne)).inv (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)) (norm_ne_zero_iff.mpr hx_ne)))

lemma representation_green_identity (Ω : Set E) [HasPDEDomain Ω]
  (u : E → ℝ) (n : E → E) (hn : IsOutwardUnitNormal Ω n)
  (h_cont_n : ContinuousOn n (frontier Ω))
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (x₀ : E) (h_bound : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (Φ : E → ℝ) (hΦ : ∀ x, Φ x = -1 / (4 * Real.pi * ‖x‖))
  (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  ∫ x in Ω \ Metric.closedBall x₀ ε, (Φ (x - x₀) * laplacianWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x - u x * laplacianWithin (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x) =
  (∫ x in frontier Ω, (Φ (x - x₀) * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫ - u x * ⟪gradientWithin (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫) ∂surfaceArea) +
  ∫ x in Metric.sphere x₀ ε, (Φ (x - x₀) * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫ - u x * ⟪gradientWithin (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫) ∂surfaceArea := by
  have hPhi_diff : ContDiffOn ℝ 2 (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) := by
    simp only [hΦ]
    have h_bound_val : ∀ y ∈ closure (Ω \ Metric.closedBall x₀ ε), ε ≤ ‖y - x₀‖ := fun y hy ↦
      closure_minimal (fun x hx ↦ le_of_lt (not_le.mp fun h ↦ hx.2 (by rwa [Metric.mem_closedBall, dist_eq_norm])))
        (isClosed_le continuous_const (continuous_id.sub continuous_const).norm) hy
    exact contDiffOn_const.div
      (contDiffOn_const.mul (ContDiffOn.norm ℝ (contDiffOn_id.sub contDiffOn_const) (fun y hy ↦ norm_pos_iff.mp (lt_of_lt_of_le hε (h_bound_val y hy)))))
      (fun y hy ↦ ne_of_gt (mul_pos (mul_pos (by norm_num) Real.pi_pos) (lt_of_lt_of_le hε (h_bound_val y hy))))
  exact greens_second_identity_annulus_gen Ω n hn h_cont_n x₀ ε hε h_subset h_bound h_area u (fun y => Φ (y - x₀)) (hu_diff.mono (closure_mono Set.sdiff_subset)) hPhi_diff

lemma laplacian_fundamental_solution_shift_zero (Φ : E → ℝ) (hΦ : ∀ x, Φ x = -1 / (4 * Real.pi * ‖x‖))
    (x₀ x : E) (hx_ne_x0 : x ≠ x₀) :
    laplacian (fun y => Φ (y - x₀)) x = 0 := by
  have : (fun y => Φ (y - x₀)) = fun y => (-1 / (4 * Real.pi)) * (1 / ‖y - x₀‖) := by ext; rw [hΦ]; ring
  rw [this, laplacian_const_mul (-1 / (4 * Real.pi)) (fun y => 1 / ‖y - x₀‖) x (contDiffAt_const.div ((contDiffAt_norm ℝ (sub_ne_zero.mpr hx_ne_x0)).comp x (contDiffAt_id.sub contDiffAt_const)) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx_ne_x0))),
    laplacian_inv_norm_shift x₀ x hx_ne_x0, laplacian_inv_norm_eq_zero (sub_ne_zero.mpr hx_ne_x0), mul_zero]

lemma representation_lhs_zero (Ω : Set E) [HasPDEDomain Ω]
  (u : E → ℝ) (hu_harm : IsHarmonic u Ω) (x₀ : E)
  (Φ : E → ℝ) (hΦ : ∀ x, Φ x = -1 / (4 * Real.pi * ‖x‖))
  (ε : ℝ) (hε : 0 < ε) :
  ∫ x in Ω \ Metric.closedBall x₀ ε, (Φ (x - x₀) * laplacianWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x - u x * laplacianWithin (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x) = 0 := by
  have h_open : IsOpen (Ω \ Metric.closedBall x₀ ε) := HasPDEDomain.is_open.sdiff Metric.isClosed_closedBall
  exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => by
    rw [laplacianWithin_closure_eq_laplacian u _ h_open x hx, laplacianWithin_closure_eq_laplacian (fun y ↦ Φ (y - x₀)) _ h_open x hx, hu_harm x hx.1, laplacian_fundamental_solution_shift_zero Φ hΦ x₀ x (dist_pos.mp (lt_trans hε (not_le.mp hx.2)))]
    ring

lemma integrand_sphere_rewrite (u : E → ℝ) (Ω : Set E) (x₀ : E) (ε : ℝ)
  (Φ : E → ℝ) (hΦ : ∀ x, Φ x = -1 / (4 * Real.pi * ‖x‖)) :
  ∀ x ∈ Metric.sphere x₀ ε,
    Φ (x - x₀) * ⟪gradientWithin u (closure Ω) x, -(1 / ε) • (x - x₀)⟫ =
    (1 / (4 * Real.pi * ε^2)) * ⟪gradientWithin u (closure Ω) x, x - x₀⟫ := by
  intro x hx
  rw [hΦ, ← dist_eq_norm, Metric.mem_sphere.mp hx, real_inner_smul_right]
  ring

lemma limit_term_one_zero (Ω : Set E) [HasPDEDomain Ω]
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (Φ : E → ℝ) (hΦ : ∀ x, Φ x = -1 / (4 * Real.pi * ‖x‖)) :
  Filter.Tendsto (fun ε => ∫ x in Metric.sphere x₀ ε, Φ (x - x₀) * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫ ∂surfaceArea) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨ε₀, hε₀_pos, h_ball_subset⟩ := Metric.isOpen_iff.mp HasPDEDomain.is_open x₀ hx₀
  let phi : E → ℝ := fun x => ⟪gradientWithin u (closure Ω) x, x - x₀⟫
  have h_eventually_eq : (fun ε => ∫ x in Metric.sphere x₀ ε, Φ (x - x₀) * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫ ∂surfaceArea) =ᶠ[𝓝[>] 0] (fun ε => (1 / (4 * Real.pi * ε^2)) * ∫ x in Metric.sphere x₀ ε, phi x ∂surfaceArea) := by
    filter_upwards [eventually_gradientWithin_excised_eq_sphere Ω u hu_diff x₀ ε₀ hε₀_pos h_ball_subset, self_mem_nhdsWithin] with ε h_grad _
    rw [setIntegral_congr_fun isClosed_sphere.measurableSet (fun x hx ↦ by rw [h_grad x hx]),
      setIntegral_congr_fun isClosed_sphere.measurableSet (integrand_sphere_rewrite u Ω x₀ ε Φ hΦ), integral_const_mul]
  exact Filter.Tendsto.congr' h_eventually_eq.symm ((show phi x₀ = 0 by simp [phi]) ▸ averaging_lemma_spherical_translated ε₀ hε₀_pos phi x₀ (continuousOn_gradientWithin_inner_sub Ω u hu_diff x₀ ε₀ h_ball_subset))

lemma differentiableAt_fundamental_sol_3d {x : E} (hx : x ≠ 0) :
  DifferentiableAt ℝ fundamental_sol_3d x := by
  unfold fundamental_sol_3d
  refine DifferentiableAt.const_mul (DifferentiableAt.fun_inv ?_ ?_) (-1)
  · exact DifferentiableAt.mul (differentiableAt_const (4 * Real.pi)) (differentiableAt_id.norm ℝ hx)
  · intro h_zero
    exact hx (norm_eq_zero.mp (by simp_all))

lemma differentiableAt_fundamental_sol_shift (x₀ x : E) (ε : ℝ) (hε_pos : 0 < ε)
  (hx : x ∈ Metric.sphere x₀ ε) :
  DifferentiableAt ℝ (fun y => fundamental_sol_3d (y - x₀)) x := by
  have h_ne : x - x₀ ≠ 0 := by
    intro h_eq
    rw [Metric.mem_sphere, dist_eq_norm, h_eq, norm_zero] at hx
    exact hε_pos.ne' hx.symm
  exact DifferentiableAt.fun_comp' x (differentiableAt_fundamental_sol_3d h_ne)
    (DifferentiableAt.sub differentiableAt_id (differentiableAt_const x₀))

lemma gradientWithin_Phi_eq (Ω : Set E) [HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε)
  (x : E) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) (hx : x ∈ Metric.sphere x₀ ε) :
  gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x = gradient (fun y => fundamental_sol_3d (y - x₀)) x := by
  unfold gradientWithin gradient
  rw [DifferentiableAt.fderivWithin (differentiableAt_fundamental_sol_shift x₀ x ε hε_pos hx) (uniqueDiffWithinAt_closure_annulus Ω x₀ ε hε_pos x h_subset hx)]

lemma fundamental_sol_3d_eq_mul_inv_norm (y x₀ : E) :
  fundamental_sol_3d (y - x₀) = (-1 / (4 * Real.pi)) * (1 / ‖y - x₀‖) := by
  unfold fundamental_sol_3d
  ring

lemma Phi_grad_inner_eval (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε) (x : E) (hx : x ∈ Metric.sphere x₀ ε) :
  ⟪gradient (fun y => fundamental_sol_3d (y - x₀)) x, -(1 / ε) • (x - x₀)⟫ = -1 / (4 * Real.pi * ε^2) := by
  simp_rw [fundamental_sol_3d_eq_mul_inv_norm]
  rw [gradient_const_mul_inv_norm x₀ ε hε_pos x hx, real_inner_smul_left, inner_gradient_inv_norm_sphere_normal_shifted x₀ ε hε_pos x hx]
  ring

lemma eventually_integral_sphere_grad_fundamental_sol_eq (Ω : Set E) [HasPDEDomain Ω] (u : E → ℝ)
  (x₀ : E) (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) (h_ball_subset : Metric.ball x₀ ε₀ ⊆ Ω) :
  (fun ε => ∫ x in Metric.sphere x₀ ε, u x * ⟪gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫ ∂surfaceArea) =ᶠ[𝓝[>] 0] (fun ε => (-1 / (4 * Real.pi * ε^2)) * ∫ x in Metric.sphere x₀ ε, u x ∂surfaceArea) := by
  filter_upwards [Ico_mem_nhdsGT (by linarith : 0 < ε₀ / 2), self_mem_nhdsWithin] with ε hε hε_pos
  rw [← integral_const_mul]
  exact setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx => by
    rw [gradientWithin_Phi_eq Ω x₀ ε hε_pos x ((Metric.closedBall_subset_ball (by linarith [hε.2, hε₀_pos])).trans h_ball_subset) hx, Phi_grad_inner_eval x₀ ε hε_pos x hx]
    ring

lemma limit_term_two_eq_u_val (Ω : Set E) [HasPDEDomain Ω] (u : E → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω)) (x₀ : E) (ε₀ : ℝ) (hε₀_pos : 0 < ε₀)
  (h_ball_subset : Metric.ball x₀ ε₀ ⊆ Ω) :
  Filter.Tendsto (fun ε => ∫ x in Metric.sphere x₀ ε, u x * ⟪gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫ ∂surfaceArea) (𝓝[>] 0) (𝓝 (-u x₀)) := by
  rcases u_continuousOn_ball Ω u hu_diff x₀ ε₀ hε₀_pos h_ball_subset with ⟨R₀, hR₀_pos, h_cont⟩
  exact Filter.Tendsto.congr' (eventually_integral_sphere_grad_fundamental_sol_eq Ω u x₀ ε₀ hε₀_pos h_ball_subset).symm
    (Filter.Tendsto.congr' (Eventually.of_forall (fun ε => by ring))
      (Filter.Tendsto.neg (averaging_lemma_spherical_translated R₀ hR₀_pos u x₀ h_cont)))

lemma continuousOn_Phi_sphere (x₀ : E) (ε : ℝ) (hε : 0 < ε) (Φ : E → ℝ)
  (hΦ : ∀ x, Φ x = -1 / (4 * Real.pi * ‖x‖)) :
  ContinuousOn (fun x => Φ (x - x₀)) (Metric.sphere x₀ ε) := by
  simp_rw [hΦ]
  exact continuousOn_const.div (continuous_const.mul (continuous_id.sub continuous_const).norm).continuousOn
    (fun x hx => mul_ne_zero (by positivity) (by rw [Metric.mem_sphere, dist_eq_norm] at hx; exact hx.symm ▸ hε.ne'))

lemma integrand_one_continuousOn (Ω : Set E) [HasPDEDomain Ω] (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (x₀ : E) (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) (Φ : E → ℝ)
  (hΦ : ∀ x, Φ x = -1 / (4 * Real.pi * ‖x‖)) :
  ContinuousOn (fun x => Φ (x - x₀) * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫) (Metric.sphere x₀ ε) := by
  have h_smul : Continuous (fun x : E ↦ -(1 / ε) • (x - x₀)) := by
    change Continuous ((fun _ : E ↦ -(1 / ε)) • (id - fun _ : E ↦ x₀))
    exact Continuous.smul continuous_const (Continuous.sub continuous_id continuous_const)
  exact (continuousOn_Phi_sphere x₀ ε hε Φ hΦ).mul
    ((continuousOn_gradientWithin_excised_sphere Ω u hu_diff x₀ ε hε h_subset).inner h_smul.continuousOn)

lemma gradientWithin_Phi_eq_explicit (Ω : Set E) [HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε : 0 < ε)
  (h_subset : Metric.closedBall x₀ ε ⊆ Ω) (x : E) (hx : x ∈ Metric.sphere x₀ ε)
  (Φ : E → ℝ) (hΦ : ∀ y, Φ y = -1 / (4 * Real.pi * ‖y‖)) :
  gradientWithin (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x = (1 / (4 * Real.pi * ‖x - x₀‖^3)) • (x - x₀) := by
  have hx_neq : x - x₀ ≠ 0 := fun h => hε.ne' (by rw [Metric.mem_sphere, dist_eq_norm, h, norm_zero] at hx; exact hx.symm)
  have h_grad_eq : gradientWithin (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x = gradient (fun y => Φ (y - x₀)) x := by
    unfold gradientWithin gradient
    rw [DifferentiableAt.fderivWithin (diff_Phi_at x₀ x hx_neq Φ hΦ) (uniqueDiffWithinAt_closure_annulus Ω x₀ ε hε x h_subset hx)]
  have h_ext : (fun y => Φ (y - x₀)) = fun y => (-1 / (4 * Real.pi)) * (1 / ‖y - x₀‖) := by ext y; rw [hΦ]; ring
  rw [h_grad_eq, h_ext, gradient_const_mul_inv_norm x₀ ε hε x hx, gradient_inv_norm_shift x₀ x, gradient_inv_norm (x - x₀) hx_neq, smul_smul]
  congr 1
  ring

lemma grad_Phi_continuousOn (Ω : Set E) [HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε : 0 < ε)
  (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (Φ : E → ℝ) (hΦ : ∀ x, Φ x = -1 / (4 * Real.pi * ‖x‖)) :
  ContinuousOn (fun x => gradientWithin (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x) (Metric.sphere x₀ ε) := by
  have h_cont : Continuous (fun x : E => (1 / (4 * Real.pi * ε^3) : ℝ) • (x - x₀)) := by
    change Continuous ((fun _ : E ↦ (1 / (4 * Real.pi * ε^3) : ℝ)) • (id - fun _ : E ↦ x₀))
    exact continuous_const.smul (continuous_id.sub continuous_const)
  refine ContinuousOn.congr h_cont.continuousOn (fun x hx => Eq.symm ?_)
  rw [gradientWithin_Phi_eq_explicit Ω x₀ ε hε h_subset x hx Φ hΦ]
  rw [Metric.mem_sphere, dist_eq_norm] at hx
  rw [hx]

lemma integrand_two_continuousOn (Ω : Set E) [HasPDEDomain Ω] (u : E → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω)) (x₀ : E) (ε : ℝ) (hε : 0 < ε)
  (h_subset : Metric.closedBall x₀ ε ⊆ Ω) (Φ : E → ℝ) (hΦ : ∀ x, Φ x = -1 / (4 * Real.pi * ‖x‖)) :
  ContinuousOn (fun x => u x * ⟪gradientWithin (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫) (Metric.sphere x₀ ε) := by
  have h_smul : Continuous (fun x : E ↦ -(1 / ε) • (x - x₀)) := by
    change Continuous ((fun _ : E ↦ -(1 / ε)) • (id - fun _ : E ↦ x₀))
    exact Continuous.smul continuous_const (Continuous.sub continuous_id continuous_const)
  exact (hu_diff.continuousOn.mono (Metric.sphere_subset_closedBall.trans (h_subset.trans subset_closure))).mul
    ((grad_Phi_continuousOn Ω x₀ ε hε h_subset Φ hΦ).inner h_smul.continuousOn)
theorem representation_formula (Ω : Set E) [HasPDEDomain Ω]
  (u : E → ℝ) (n : E → E) (hn : IsOutwardUnitNormal Ω n)
  (h_cont_n : ContinuousOn n (frontier Ω))
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hu_harm : IsHarmonic u Ω) (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (h_bound : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (Φ : E → ℝ) (hΦ : ∀ x, Φ x = -1 / (4 * Real.pi * ‖x‖)) :
  u x₀ = ∫ x in frontier Ω,
    (u x * ⟪n x, gradientWithin (fun y => Φ (y - x₀)) (closure Ω) x⟫ -
    Φ (x - x₀) * ⟪n x, gradientWithin u (closure Ω) x⟫) ∂surfaceArea := by
  obtain ⟨ε₀, hε₀_pos, h_ball_subset⟩ := Metric.isOpen_iff.mp HasPDEDomain.is_open x₀ hx₀
  have h_sphere_tendsto : Filter.Tendsto (fun ε => ∫ x in Metric.sphere x₀ ε, (Φ (x - x₀) * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫ - u x * ⟪gradientWithin (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫) ∂surfaceArea) (𝓝[>] 0) (𝓝 (u x₀)) := by
    have h_sub := (limit_term_one_zero Ω u hu_diff x₀ hx₀ Φ hΦ).sub (show Filter.Tendsto _ _ _ from (show (fun y => Φ (y - x₀)) = (fun y => fundamental_sol_3d (y - x₀)) by ext y; exact hΦ _) ▸ limit_term_two_eq_u_val Ω u hu_diff x₀ ε₀ hε₀_pos h_ball_subset)
    rw [show (0 : ℝ) - -u x₀ = u x₀ by ring] at h_sub
    refine Filter.Tendsto.congr' ?_ h_sub
    filter_upwards [eventually_closedBall_subset_of_isOpen HasPDEDomain.is_open hx₀, self_mem_nhdsWithin] with ε h_sub hε
    exact Eq.symm (integral_sub (integrableOn_of_continuousOn_compact_finite_measure (isCompact_sphere x₀ ε) isClosed_sphere.measurableSet (surfaceArea_sphere_lt_top x₀ hε) (integrand_one_continuousOn Ω u hu_diff x₀ ε hε h_sub Φ hΦ)) (integrableOn_of_continuousOn_compact_finite_measure (isCompact_sphere x₀ ε) isClosed_sphere.measurableSet (surfaceArea_sphere_lt_top x₀ hε) (integrand_two_continuousOn Ω u hu_diff x₀ ε hε h_sub Φ hΦ)))
  have h_main_value : ∫ x in frontier Ω, (Φ (x - x₀) * ⟪gradientWithin u (closure Ω) x, n x⟫ - u x * ⟪gradientWithin (fun y => Φ (y - x₀)) (closure Ω) x, n x⟫) ∂surfaceArea = -u x₀ := by
    refine tendsto_nhds_unique tendsto_const_nhds (Filter.Tendsto.congr' (frontier_integral_const Ω u n x₀ hx₀ Φ) ?_)
    refine Filter.Tendsto.congr' ?_ (Filter.Tendsto.neg h_sphere_tendsto)
    filter_upwards [eventually_closedBall_subset_of_isOpen HasPDEDomain.is_open hx₀, self_mem_nhdsWithin] with ε h_subset hε_pos
    exact Eq.symm (eq_neg_iff_add_eq_zero.mpr (representation_lhs_zero Ω u hu_harm x₀ Φ hΦ ε hε_pos ▸ (representation_green_identity Ω u n hn h_cont_n hu_diff x₀ h_bound h_area Φ hΦ ε hε_pos h_subset).symm))
  rw [boundary_integral_rewrite Ω u n x₀ Φ, h_main_value, neg_neg]
