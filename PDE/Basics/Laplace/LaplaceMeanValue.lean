import PDE.Basics.Laplace.SphericalMeans

noncomputable section

open Real Set MeasureTheory Metric Filter Function Pointwise InnerProductSpace
open scoped BigOperators Topology

lemma divergence_theorem_scalar (u : E → ℝ) (s : Set E) (n : E → E)
    [h_domain : HasPDEDomain s]
    (hn_normal : IsOutwardUnitNormal s n)
    (h_smooth : ContDiffOn ℝ 2 u (closure s)) :
    ∫ x in s, laplacianWithin u (closure s) x ∂volume =
    ∫ x in frontier s, (fderivWithin ℝ u (closure s) x) (n x) ∂(Measure.hausdorffMeasure 2) := by
  rw [setIntegral_congr_fun h_domain.is_open.measurableSet (fun x hx ↦ laplacianWithin_eq_div_field u s h_domain.is_open x hx)]
  rw [divergence_theorem (gradientWithin u (closure s)) s n hn_normal (contDiffOn_gradientWithin u (closure s) h_domain.unique_diff h_smooth)]
  simp_rw [gradientWithin, InnerProductSpace.toDual_symm_apply]
  rw [show (Module.finrank ℝ E : ℝ) - 1 = 2 by change (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) - 1 = 2; rw [finrank_euclideanSpace]; norm_num]

lemma divergence_theorem_ball (u : E → ℝ) (x₀ : E) (r : ℝ) (hr_pos : 0 < r)
    (h_smooth : ContDiffOn ℝ 2 u (closure (Metric.ball x₀ r))) :
    ∫ x in sphere x₀ r, (fderivWithin ℝ u (closure (Metric.ball x₀ r)) x) (x - x₀) * (1 / r) ∂surfaceArea =
    ∫ x in Metric.ball x₀ r, laplacianWithin u (closure (Metric.ball x₀ r)) x := by
  haveI : HasPDEDomain (Metric.ball x₀ r) := instHasPDEDomainBall x₀ r hr_pos
  rw [← frontier_ball_eq_sphere x₀ r hr_pos]
  simp_rw [mul_comm _ (1 / r), ← smul_eq_mul, ← ContinuousLinearMap.map_smul]
  exact (divergence_theorem_scalar u (Metric.ball x₀ r) (fun x ↦ (1 / r) • (x - x₀)) (ball_outward_normal x₀ r) h_smooth).symm

/-
### Theorem 8.1: The Mean Value Property
-/

lemma laplace_mean_value_property_vol_eq (u : E → ℝ) (x₀ : E) (r : ℝ) :
  ∫ x in Metric.ball x₀ r, laplacianWithin u (closure (Metric.ball x₀ r)) x ∂volume = ∫ x in Metric.ball x₀ r, laplacian u x ∂volume := by
  refine setIntegral_congr_fun isOpen_ball.measurableSet (fun x hx ↦ ?_)
  unfold laplacianWithin laplacian div_fieldWithin div_field
  rw [fderivWithin_of_mem_nhds (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) subset_closure),
    ← fderivWithin_of_mem_nhds (isOpen_ball.mem_nhds hx),
    fderivWithin_congr
      (show EqOn (gradientWithin u (closure (Metric.ball x₀ r))) (gradient u) (Metric.ball x₀ r) from fun y hy ↦ by unfold gradientWithin gradient; rw [fderivWithin_of_mem_nhds (Filter.mem_of_superset (isOpen_ball.mem_nhds hy) subset_closure)])
      (by unfold gradientWithin gradient; rw [fderivWithin_of_mem_nhds (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) subset_closure)]),
    fderivWithin_of_mem_nhds (isOpen_ball.mem_nhds hx)]

lemma laplace_mean_value_property_bound_eq (u : E → ℝ) (Ω : Set E) (x₀ : E) (r : ℝ) (hr_pos : 0 < r)
  (h_open : IsOpen Ω) (h_subset : Metric.closedBall x₀ r ⊆ Ω) (h_smooth : ContDiffOn ℝ 2 u Ω) :
  ∫ x in sphere x₀ r, (fderiv ℝ u x) (x - x₀) * (1 / r) ∂surfaceArea = ∫ x in sphere x₀ r, (fderivWithin ℝ u (closure (Metric.ball x₀ r)) x) (x - x₀) * (1 / r) ∂surfaceArea := by
  refine setIntegral_congr_fun isClosed_sphere.measurableSet (fun x hx ↦ ?_)
  rw [((h_smooth.differentiableOn (by norm_num)).differentiableAt (h_open.mem_nhds (h_subset (Metric.sphere_subset_closedBall hx)))).fderivWithin ((instHasPDEDomainBall x₀ r hr_pos).unique_diff x (frontier_subset_closure (by rwa [frontier_ball_eq_sphere x₀ r hr_pos])))]

lemma laplace_mean_value_property_deriv_zero (u : E → ℝ) (Ω : Set E) (x₀ : E) (R r : ℝ)
  (h_open : IsOpen Ω) (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
  (h_smooth : ContDiffOn ℝ 2 u Ω) (h_harmonic : IsHarmonic u Ω) (hr : r ∈ Set.Ioo 0 R) :
  deriv (fun (ρ : ℝ) ↦ (1 / (4 * π * ρ^2)) * ∫ x in sphere x₀ ρ, u x ∂surfaceArea) r = 0 := by
  calc
    deriv (fun (ρ : ℝ) ↦ (1 / (4 * π * ρ^2)) * ∫ x in sphere x₀ ρ, u x ∂surfaceArea) r
      = (1 / (4 * π * r^2)) * ∫ x in sphere x₀ r, (fderiv ℝ u x) (x - x₀) * (1 / r) ∂surfaceArea := by
        rw [deriv_spherical_mean u Ω x₀ R r h_closed_ball h_open h_smooth hr, sphere_integral_revert_vars u x₀ r hr.1, ← mul_assoc]; congr 1; ring
    _ = (1 / (4 * π * r^2)) * ∫ x in Metric.ball x₀ r, laplacian u x ∂volume := by
        rw [laplace_mean_value_property_bound_eq u Ω x₀ r hr.1 h_open (Set.Subset.trans (Metric.closedBall_subset_closedBall (le_of_lt hr.2)) h_closed_ball) h_smooth, divergence_theorem_ball u x₀ r hr.1 (h_smooth.mono (Set.Subset.trans Metric.closure_ball_subset_closedBall (Set.Subset.trans (Metric.closedBall_subset_closedBall (le_of_lt hr.2)) h_closed_ball))), laplace_mean_value_property_vol_eq]
    _ = 0 := by
        rw [show ∫ x in Metric.ball x₀ r, laplacian u x ∂volume = 0 from integral_eq_zero_of_ae (Eventually.mono (self_mem_ae_restrict isOpen_ball.measurableSet) (fun x hx ↦ h_harmonic x ((Set.Subset.trans (Metric.closedBall_subset_closedBall (le_of_lt hr.2)) h_closed_ball) (Metric.ball_subset_closedBall hx)))), mul_zero]

lemma laplace_mean_value_property_const (u : E → ℝ) (Ω : Set E) (x₀ : E) (R r : ℝ)
  (h_open : IsOpen Ω) (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
  (h_smooth : ContDiffOn ℝ 2 u Ω) (h_harmonic : IsHarmonic u Ω) (hr : r ∈ Set.Ioo 0 R) :
  (1 / (4 * π * r^2)) * ∫ x in sphere x₀ r, u x ∂surfaceArea = (1 / (4 * π * R^2)) * ∫ x in sphere x₀ R, u x ∂surfaceArea := by
  let phi := fun (ρ : ℝ) ↦ (1 / (4 * π * ρ^2)) * ∫ x in sphere x₀ ρ, u x ∂surfaceArea
  exact (constant_of_has_deriv_right_zero
    ((continuousOn_spherical_mean u x₀ R (h_smooth.continuousOn.mono h_closed_ball)).mono fun x hx ↦ ⟨hr.1.trans_le hx.1, hx.2⟩)
    (fun x hx ↦ by rw [← laplace_mean_value_property_deriv_zero u Ω x₀ R x h_open h_closed_ball h_smooth h_harmonic ⟨hr.1.trans_le hx.1, hx.2⟩]; exact ((differentiableOn_spherical_mean u Ω h_open x₀ R h_closed_ball h_smooth).differentiableAt (isOpen_Ioo.mem_nhds ⟨hr.1.trans_le hx.1, hx.2⟩)).hasDerivAt.hasDerivWithinAt)
    R ⟨hr.2.le, le_rfl⟩).symm

theorem laplace_mean_value_property_3D
  (u : E → ℝ) (Ω : Set E) (x₀ : E) (R : ℝ)
  (h_open : IsOpen Ω)
  (hR : 0 < R)
  (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
  (h_smooth : ContDiffOn ℝ 2 u Ω)
  (h_harmonic : IsHarmonic u Ω) :
  u x₀ = (1 / (4 * π * R^2)) * ∫ x in sphere x₀ R, u x ∂surfaceArea := by
  let phi := fun (r : ℝ) ↦ (1 / (4 * π * r^2)) * ∫ x in sphere x₀ r, u x ∂surfaceArea
  exact tendsto_nhds_unique
    (averaging_lemma_spherical_translated R hR u x₀ (h_smooth.continuousOn.mono (Set.Subset.trans Metric.ball_subset_closedBall h_closed_ball)))
    (by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      rw [Filter.EventuallyEq, nhdsWithin, Filter.eventually_inf_principal]
      filter_upwards [isOpen_Iio.mem_nhds hR] with r hr_lt hr_pos
      exact (laplace_mean_value_property_const u Ω x₀ R r h_open h_closed_ball h_smooth h_harmonic ⟨hr_pos, hr_lt⟩).symm)
