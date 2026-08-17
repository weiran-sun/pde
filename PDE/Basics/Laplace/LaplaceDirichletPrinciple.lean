import PDE.Basics.Laplace.LaplaceMaximumPrinciple
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section

open Real Set MeasureTheory Metric Filter Function Pointwise InnerProductSpace
open scoped BigOperators Topology

def IsAdmissible (Ω : Set E) (h : E → ℝ) (w : E → ℝ) : Prop :=
  ContDiffOn ℝ 2 w Ω ∧
  ContDiffOn ℝ 1 w (closure Ω) ∧
  (∀ x ∈ frontier Ω, w x = h x) ∧
  IntegrableOn (fun x => ‖gradient w x‖ ^ 2) Ω

def IsTestFunction (Ω : Set E) (v : E → ℝ) : Prop :=
  ContDiffOn ℝ 2 v Ω ∧ ∀ x ∈ frontier Ω, v x = 0

def DirichletEnergy (Ω : Set E) (w : E → ℝ) : ℝ :=
  (1 / 2) * ∫ x in Ω, ‖gradient w x‖ ^ 2


lemma test_function_boundary_integral (Ω : Set E) (u v : E → ℝ) (n : E → E)
  (hv : IsTestFunction Ω v) :
  ∫ x in frontier Ω, v x * ⟪gradientWithin u (closure Ω) x, n x⟫_ℝ ∂surfaceArea = 0 := by
  rw [setIntegral_congr_fun isClosed_frontier.measurableSet (fun x hx => by rw [hv.2 x hx, zero_mul]), integral_zero]

lemma harmonic_volume_integral (Ω : Set E) (u v : E → ℝ)
  (h_domain : HasPDEDomain Ω)
  (hu_harm : IsHarmonic u Ω) :
  ∫ x in Ω, v x * laplacian u x = 0 := by
  rw [setIntegral_congr_fun h_domain.is_open.measurableSet (fun x hx => by rw [hu_harm x hx, mul_zero]), integral_zero]

lemma admissible_sub_boundary (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) (x : E) (hx : x ∈ frontier Ω) :
  (u - w) x = 0 := by
  rw [Pi.sub_apply, hu_admis.2.2.1 x hx, hw_admis.2.2.1 x hx, sub_self]

lemma admissible_cross_measurable (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (h_domain : HasPDEDomain Ω) (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) :
  AEStronglyMeasurable (fun x => ⟪gradient u x, gradient (u - w) x⟫_ℝ) (volume.restrict Ω) := by
  exact ((contDiffOn_gradient_continuousOn hu_admis.1 h_domain.is_open).inner
    (contDiffOn_gradient_continuousOn (hu_admis.1.sub hw_admis.1) h_domain.is_open)).aestronglyMeasurable h_domain.is_open.measurableSet

lemma admissible_differentiableAt (Ω : Set E) (h : E → ℝ) (u : E → ℝ) (x : E)
  (h_domain : HasPDEDomain Ω) (hu_admis : IsAdmissible Ω h u) (hx : x ∈ Ω) :
  DifferentiableAt ℝ u x := by
  exact (hu_admis.1.differentiableOn (by decide) x hx).differentiableAt (h_domain.is_open.mem_nhds hx)


lemma gradient_sub_sq_bound_pointwise (Ω : Set E) (h : E → ℝ) (u w : E → ℝ) (x : E)
  (h_domain : HasPDEDomain Ω) (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) (hx : x ∈ Ω) :
  ‖gradient (u - w) x‖ ^ 2 ≤ 2 * ‖gradient u x‖ ^ 2 + 2 * ‖gradient w x‖ ^ 2 := by
  rw [gradient_sub_pointwise u w x (admissible_differentiableAt Ω h u x h_domain hu_admis hx) (admissible_differentiableAt Ω h w x h_domain hw_admis hx)]
  exact norm_sub_sq_bound (gradient u x) (gradient w x)

lemma admissible_diff_measurable (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (h_domain : HasPDEDomain Ω) (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) :
  AEStronglyMeasurable (fun x => ‖gradient (u - w) x‖ ^ 2) (volume.restrict Ω) := by
  exact (contDiffOn_gradient_norm_sq_continuousOn (hu_admis.1.sub hw_admis.1) h_domain.is_open).aestronglyMeasurable h_domain.is_open.measurableSet

lemma admissible_diff_integrable (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (h_domain : HasPDEDomain Ω)
  (hu_admis : IsAdmissible Ω h u)
  (hw_admis : IsAdmissible Ω h w) :
  IntegrableOn (fun x => ‖gradient (u - w) x‖ ^ 2) Ω := by
  refine Integrable.mono' ((hu_admis.2.2.2.const_mul 2).add (hw_admis.2.2.2.const_mul 2))
    (admissible_diff_measurable Ω h u w h_domain hu_admis hw_admis) ?_
  rw [ae_restrict_iff' h_domain.is_open.measurableSet]
  exact Filter.Eventually.of_forall fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact gradient_sub_sq_bound_pointwise Ω h u w x h_domain hu_admis hw_admis hx

lemma admissible_cross_integrable (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (h_domain : HasPDEDomain Ω)
  (hu_admis : IsAdmissible Ω h u)
  (hw_admis : IsAdmissible Ω h w) :
  IntegrableOn (fun x => ⟪gradient u x, gradient (u - w) x⟫_ℝ) Ω := by
  refine Integrable.mono' (hu_admis.2.2.2.add (admissible_diff_integrable Ω h u w h_domain hu_admis hw_admis))
    (admissible_cross_measurable Ω h u w h_domain hu_admis hw_admis) ?_
  rw [ae_restrict_iff' h_domain.is_open.measurableSet]
  exact Filter.Eventually.of_forall fun x _ => inner_bound (gradient u x) (gradient (u - w) x)

lemma admissible_cross_diff (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) :
  ContDiffOn ℝ 1 (fun x => (u - w) x • gradient u x) Ω := by
  exact ((hu_admis.1.sub hw_admis.1).of_le (by decide)).smul (gradient_c1_of_c2 u Ω h_domain.is_open hu_admis.1)

lemma admissible_cross_cont (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) :
  ContinuousOn (fun x => (u - w) x • gradientWithin u (closure Ω) x) (closure Ω) := by
  exact (hu_admis.2.1.continuousOn.sub hw_admis.2.1.continuousOn).smul (contDiffOn_1_gradientWithin_continuousOn hu_admis.2.1 h_domain.unique_diff)

lemma cross_term_vanishing (Ω : Set E) (h : E → ℝ) (u w : E → ℝ) (n : E → E)
  [h_domain : HasPDEDomain Ω] (hn : IsOutwardUnitNormal Ω n)
  (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w)
  (hu_harm : IsHarmonic u Ω) :
  ∫ x in Ω, ⟪gradient u x, gradient (u - w) x⟫_ℝ = 0 := by
  have h_int_lap : IntegrableOn (fun x => (u - w) x * laplacianWithin u (closure Ω) x) Ω :=
    IntegrableOn.congr_fun integrableOn_zero (fun x hx => by rw [harmonic_laplacian_zero u Ω x hx hu_harm, mul_zero]) h_domain.is_open.measurableSet
  rw [greens_first_identity Ω u (u - w) n hn (admissible_cross_diff Ω h u w hu_admis hw_admis) (admissible_cross_cont Ω h u w hu_admis hw_admis) (admissible_cross_integrable Ω h u w h_domain hu_admis hw_admis) h_int_lap,
    setIntegral_congr_fun isClosed_frontier.measurableSet (fun x hx => by rw [admissible_sub_boundary Ω h u w hu_admis hw_admis x hx, zero_mul]),
    setIntegral_congr_fun h_domain.is_open.measurableSet (fun x hx => by rw [harmonic_laplacian_zero u Ω x hx hu_harm, mul_zero]),
    integral_zero, integral_zero, sub_zero]

lemma energy_expansion (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (h_domain : HasPDEDomain Ω)
  (hu_admis : IsAdmissible Ω h u)
  (hw_admis : IsAdmissible Ω h w) :
  DirichletEnergy Ω w = DirichletEnergy Ω u - (∫ x in Ω, ⟪gradient u x, gradient (u - w) x⟫_ℝ) + DirichletEnergy Ω (u - w) := by
  unfold DirichletEnergy
  have h_int_u : IntegrableOn (fun x => (1 / 2 : ℝ) * ‖gradient u x‖ ^ 2) Ω :=
    hu_admis.2.2.2.const_mul (1 / 2)
  have h_int_sub : IntegrableOn (fun x => (1 / 2 : ℝ) * ‖gradient (u - w) x‖ ^ 2) Ω :=
    (admissible_diff_integrable Ω h u w h_domain hu_admis hw_admis).const_mul (1 / 2)
  have h_int_cross : IntegrableOn (fun x => ⟪gradient u x, gradient (u - w) x⟫_ℝ) Ω :=
    admissible_cross_integrable Ω h u w h_domain hu_admis hw_admis
  erw [← integral_const_mul (1 / 2 : ℝ) (fun x => ‖gradient w x‖ ^ 2),
    setIntegral_congr_fun h_domain.is_open.measurableSet (fun x hx => by
      rw [pointwise_energy_expansion (gradient u x) (gradient w x),
        ← gradient_sub_pointwise u w x (admissible_differentiableAt Ω h u x h_domain hu_admis hx) (admissible_differentiableAt Ω h w x h_domain hw_admis hx)]),
    integral_add (h_int_u.sub h_int_cross) h_int_sub,
    integral_sub h_int_u h_int_cross,
    integral_const_mul (1 / 2 : ℝ) (fun x => ‖gradient u x‖ ^ 2),
    integral_const_mul (1 / 2 : ℝ) (fun x => ‖gradient (u - w) x‖ ^ 2)]

lemma energy_nonnegative (Ω : Set E) (v : E → ℝ) :
  DirichletEnergy Ω v ≥ 0 := by
  unfold DirichletEnergy
  positivity

theorem dirichlet_principle_backward (Ω : Set E) (h : E → ℝ) (u : E → ℝ) (n : E → E)
  [h_domain : HasPDEDomain Ω] (hn : IsOutwardUnitNormal Ω n)
  (hu_admis : IsAdmissible Ω h u) (hu_harm : IsHarmonic u Ω) :
  ∀ w, IsAdmissible Ω h w → DirichletEnergy Ω w ≥ DirichletEnergy Ω u := by
  intro w hw_admis
  linarith [energy_expansion Ω h u w h_domain hu_admis hw_admis,
    cross_term_vanishing Ω h u w n hn hu_admis hw_admis hu_harm,
    energy_nonnegative Ω (u - w)]

lemma admissible_perturbation (Ω : Set E) (h : E → ℝ) (u v : E → ℝ) (t : ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u) (hv_admis : IsAdmissible Ω (fun _ => 0) v) :
  IsAdmissible Ω h (fun x => u x - t * v x) := by
  refine ⟨hu_admis.1.sub (hv_admis.1.const_smul t), hu_admis.2.1.sub (hv_admis.2.1.const_smul t),
    fun x hx => by simp [hu_admis.2.2.1 x hx, hv_admis.2.2.1 x hx], ?_⟩
  have h_int_tv : IntegrableOn (fun x => ‖t • gradient v x‖ ^ 2) Ω := by
    have heq : (fun x => ‖t • gradient v x‖ ^ 2) = (fun x => t ^ 2 * ‖gradient v x‖ ^ 2) := by
      ext; simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [heq]
    exact hv_admis.2.2.2.const_mul (t ^ 2)
  refine Integrable.mono' ((hu_admis.2.2.2.const_mul 2).add (h_int_tv.const_mul 2))
    ((contDiffOn_gradient_norm_sq_continuousOn (hu_admis.1.sub (hv_admis.1.const_smul t)) h_domain.is_open).aestronglyMeasurable h_domain.is_open.measurableSet) ?_
  rw [ae_restrict_iff' h_domain.is_open.measurableSet]
  exact Filter.Eventually.of_forall fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    change ‖gradient (u - t • v) x‖ ^ 2 ≤ _
    rw [gradient_sub_pointwise u (t • v) x (admissible_differentiableAt Ω h u x h_domain hu_admis hx) ((admissible_differentiableAt Ω (fun _ => 0) v x h_domain hv_admis hx).const_smul t)]
    change ‖gradient u x - gradient (fun y => t * v y) x‖ ^ 2 ≤ _
    rw [gradient_smul_pointwise v t x (admissible_differentiableAt Ω (fun _ => 0) v x h_domain hv_admis hx)]
    exact norm_sub_sq_bound (gradient u x) (t • gradient v x)

lemma energy_smul (Ω : Set E) (v : E → ℝ) (t : ℝ)
  [h_domain : HasPDEDomain Ω]
  (hv_admis : IsAdmissible Ω (fun _ => 0) v) :
  DirichletEnergy Ω (fun x => t * v x) = t ^ 2 * DirichletEnergy Ω v := by
  unfold DirichletEnergy
  have h_int_eq : ∫ x in Ω, ‖gradient (fun y => t * v y) x‖ ^ 2 = ∫ x in Ω, t ^ 2 * ‖gradient v x‖ ^ 2 :=
    setIntegral_congr_fun h_domain.is_open.measurableSet fun x hx => by
      rw [gradient_smul_pointwise v t x (admissible_differentiableAt Ω (fun _ => 0) v x h_domain hv_admis hx)]
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [h_int_eq, integral_const_mul]
  ring

lemma variation_inequality_reduction (Ω : Set E) (h : E → ℝ) (u v : E → ℝ) (t : ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u) (hv_admis : IsAdmissible Ω (fun _ => 0) v)
  (h_bound : DirichletEnergy Ω u ≤ DirichletEnergy Ω (fun x => u x - t * v x)) :
  0 ≤ -t * (∫ x in Ω, ⟪gradient u x, gradient v x⟫_ℝ) + t ^ 2 * DirichletEnergy Ω v := by
  have h_expand := energy_expansion Ω h u (fun x => u x - t * v x) h_domain hu_admis (admissible_perturbation Ω h u v t hu_admis hv_admis)
  have h_sub_eq : u - (fun x => u x - t * v x) = fun x => t * v x := by
    ext x
    change u x - (u x - t * v x) = t * v x
    ring
  rw [h_sub_eq] at h_expand
  have h_int_congr : ∫ x in Ω, ⟪gradient u x, gradient (fun y => t * v y) x⟫_ℝ = t * ∫ x in Ω, ⟪gradient u x, gradient v x⟫_ℝ := by
    rw [setIntegral_congr_fun h_domain.is_open.measurableSet fun x hx => by
      rw [gradient_smul_pointwise v t x (admissible_differentiableAt Ω (fun _ => 0) v x h_domain hv_admis hx)]]
    exact integral_cross_smul Ω u v t
  rw [h_int_congr, energy_smul Ω v t hv_admis] at h_expand
  linarith

lemma first_variation_vanishes (Ω : Set E) (h : E → ℝ) (u : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u)
  (h_min : ∀ w, IsAdmissible Ω h w → DirichletEnergy Ω u ≤ DirichletEnergy Ω w) :
  ∀ v, IsAdmissible Ω (fun _ => 0) v → HasCompactSupport v → tsupport v ⊆ Ω → ∫ x in Ω, ⟪gradient u x, gradient v x⟫_ℝ = 0 := by
  intro v hv_admis _ _
  exact real_polynomial_pos_implies_linear_zero (∫ x in Ω, ⟪gradient u x, gradient v x⟫_ℝ) (DirichletEnergy Ω v)
    fun t => variation_inequality_reduction Ω h u v t hu_admis hv_admis
      (h_min (fun x => u x - t * v x) (admissible_perturbation Ω h u v t hu_admis hv_admis))

lemma admissible_test_diff (Ω : Set E) (h : E → ℝ) (u v : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u) (hv_admis : IsAdmissible Ω (fun _ => 0) v) :
  ContDiffOn ℝ 1 (fun x => v x • gradient u x) Ω := by
  exact (hv_admis.1.of_le (by decide)).smul (gradient_c1_of_c2 u Ω h_domain.is_open hu_admis.1)

lemma admissible_test_cont (Ω : Set E) (h : E → ℝ) (u v : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u) (hv_admis : IsAdmissible Ω (fun _ => 0) v) :
  ContinuousOn (fun x => v x • gradientWithin u (closure Ω) x) (closure Ω) := by
  exact hv_admis.2.1.continuousOn.smul (contDiffOn_1_gradientWithin_continuousOn hu_admis.2.1 h_domain.unique_diff)


lemma laplacian_continuous_of_c2 (u : E → ℝ) (Ω : Set E)
  [h_domain : HasPDEDomain Ω] (h_smooth : ContDiffOn ℝ 2 u Ω) :
  ContinuousOn (laplacian u) Ω := by
  unfold laplacian div_field
  exact continuous_trace.comp_continuousOn (fderiv_continuousOn_of_c1 (fun x => gradient u x) Ω h_domain.is_open (gradient_c1_of_c2 u Ω h_domain.is_open h_smooth))

lemma admissible_test_integrable (Ω : Set E) (h : E → ℝ) (u v : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u) (hv_admis : IsAdmissible Ω (fun _ => 0) v) :
  IntegrableOn (fun x => ⟪gradient u x, gradient v x⟫_ℝ) Ω := by
  refine Integrable.mono' (hu_admis.2.2.2.add hv_admis.2.2.2)
    (((contDiffOn_gradient_continuousOn hu_admis.1 h_domain.is_open).inner
      (contDiffOn_gradient_continuousOn hv_admis.1 h_domain.is_open)).aestronglyMeasurable h_domain.is_open.measurableSet) ?_
  rw [ae_restrict_iff' h_domain.is_open.measurableSet]
  exact Filter.Eventually.of_forall fun x _ => inner_bound (gradient u x) (gradient v x)

lemma admissible_test_lap_integrable (Ω : Set E) (h : E → ℝ) (u v : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u) (hv_admis : IsAdmissible Ω (fun _ => 0) v)
  (hv_compact : HasCompactSupport v) (hv_supp : tsupport v ⊆ Ω) :
  IntegrableOn (fun x => v x * laplacianWithin u (closure Ω) x) Ω := by
  suffices IntegrableOn (fun x => v x * laplacian u x) Ω by
    refine Integrable.congr this ?_
    rw [EventuallyEq, ae_restrict_iff' h_domain.is_open.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => by rw [laplacianWithin_closure_eq_laplacian u Ω h_domain.is_open x hx]
  rw [← Set.union_sdiff_cancel hv_supp]
  exact (ContinuousOn.integrableOn_compact hv_compact ((hv_admis.1.continuousOn.mul (laplacian_continuous_of_c2 u Ω hu_admis.1)).mono hv_supp)).union
    (integrableOn_zero.congr_fun (fun x hx => by
      have h_zero : v x = 0 := by_contra fun h_nz => hx.2 (subset_tsupport v h_nz)
      simp[h_zero]) (h_domain.is_open.measurableSet.diff (isClosed_tsupport v).measurableSet))

lemma greens_zero_boundary (Ω : Set E) (h : E → ℝ) (u v : E → ℝ) (n : E → E)
  [h_domain : HasPDEDomain Ω] (hn : IsOutwardUnitNormal Ω n)
  (hu_admis : IsAdmissible Ω h u) (hv_admis : IsAdmissible Ω (fun _ => 0) v)
  (hv_compact : HasCompactSupport v) (hv_supp : tsupport v ⊆ Ω) :
  ∫ x in Ω, ⟪gradient u x, gradient v x⟫_ℝ = - ∫ x in Ω, v x * laplacian u x := by
  rw [greens_first_identity Ω u v n hn (admissible_test_diff Ω h u v hu_admis hv_admis) (admissible_test_cont Ω h u v hu_admis hv_admis) (admissible_test_integrable Ω h u v hu_admis hv_admis) (admissible_test_lap_integrable Ω h u v hu_admis hv_admis hv_compact hv_supp),
    setIntegral_congr_fun isClosed_frontier.measurableSet (fun x hx => by rw [hv_admis.2.2.1 x hx, zero_mul]),
    integral_zero, zero_sub,
    setIntegral_congr_fun h_domain.is_open.measurableSet (fun x hx => by rw [laplacianWithin_closure_eq_laplacian u Ω h_domain.is_open x hx])]

lemma smooth_compact_is_admissible {T : ℕ} (Ω : Set E) (v : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hT : 2 ≤ T)
  (hv_smooth : ContDiff ℝ T v)
  (hv_comp : HasCompactSupport v)
  (hv_supp : tsupport v ⊆ Ω) :
  IsAdmissible Ω (fun _ => 0) v := by
  have h_v_c2 : ContDiff ℝ 2 v := hv_smooth.of_le (by exact_mod_cast hT)
  have h_v_c1 : ContDiff ℝ 1 v := h_v_c2.of_le (by decide)
  refine ⟨h_v_c2.contDiffOn, h_v_c1.contDiffOn,
    fun x hx => image_eq_zero_of_notMem_tsupport fun h => by
      rw [frontier, h_domain.is_open.interior_eq] at hx
      exact hx.2 (hv_supp h), ?_⟩
  rw [← Set.union_sdiff_cancel hv_supp]
  exact (ContinuousOn.integrableOn_compact hv_comp ((contDiffOn_gradient_norm_sq_continuousOn h_v_c2.contDiffOn isOpen_univ).mono (subset_univ _))).union
    (integrableOn_zero.congr_fun (fun x hx => by simp [gradient_zero_outside_support v x hx.2]) (h_domain.is_open.measurableSet.diff (isClosed_tsupport v).measurableSet))

lemma integral_to_pointwise (Ω : Set E) (f : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hf_cont : ContinuousOn f Ω)
  (h_ortho : ∀ v, IsAdmissible Ω (fun _ => 0) v → HasCompactSupport v → tsupport v ⊆ Ω → ∫ x in Ω, v x * f x = 0) :
  ∀ x ∈ Ω, f x = 0 := by
  exact continuousOn_ae_eq_zero_to_pointwise Ω f hf_cont ((ae_restrict_iff' h_domain.is_open.measurableSet).mpr
    (IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero h_domain.is_open (hf_cont.locallyIntegrableOn h_domain.is_open.measurableSet)
      fun g hg_smooth hg_comp hg_supp => by
        rw [integral_eq_setIntegral_of_support_subset Ω g f hg_supp]
        have h_g_c2 : ContDiff ℝ 2 g := hg_smooth.of_le (by decide)
        exact h_ortho g (smooth_compact_is_admissible Ω g (by decide) h_g_c2 hg_comp hg_supp) hg_comp hg_supp))

theorem dirichlet_principle_forward (Ω : Set E) (h : E → ℝ) (u : E → ℝ) (n : E → E)
  [h_domain : HasPDEDomain Ω] (hn : IsOutwardUnitNormal Ω n)
  (hu_admis : IsAdmissible Ω h u)
  (h_min : ∀ w, IsAdmissible Ω h w → DirichletEnergy Ω u ≤ DirichletEnergy Ω w) :
  IsHarmonic u Ω := by
  intro x hx
  exact integral_to_pointwise Ω (laplacian u) (laplacian_continuous_of_c2 u Ω hu_admis.1)
    (fun v hv_admis hv_compact hv_supp =>
      neg_eq_zero.mp ((greens_zero_boundary Ω h u v n hn hu_admis hv_admis hv_compact hv_supp).symm.trans
        (first_variation_vanishes Ω h u hu_admis h_min v hv_admis hv_compact hv_supp))) x hx
