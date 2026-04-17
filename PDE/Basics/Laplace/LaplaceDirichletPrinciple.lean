import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Kernel.Integral
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.LinearAlgebra.Trace
import PDE.Basics.Laplace.LaplaceMeanValue

noncomputable section

open Real Set MeasureTheory Metric Filter Function Pointwise InnerProductSpace
open scoped BigOperators Topology


-- not exactly definition in textbook, b/c textbook relies on physical intuition
-- of IntegrableOn
def IsAdmissible (Ω : Set E) (h : E → ℝ) (w : E → ℝ) : Prop :=
  ContDiffOn ℝ 2 w Ω ∧
  (ContinuousOn w (closure Ω) ∧ ContinuousOn (fun x => gradient w x) (closure Ω)) ∧ --DOES NOT EXACTLY MATCH BOOK
  (∀ x ∈ frontier Ω, w x = h x) ∧
  IntegrableOn (fun x => ‖gradient w x‖ ^ 2) Ω

def IsTestFunction (Ω : Set E) (v : E → ℝ) : Prop :=
  ContDiffOn ℝ 2 v Ω ∧ ∀ x ∈ frontier Ω, v x = 0

def DirichletEnergy (Ω : Set E) (w : E → ℝ) : ℝ :=
  (1 / 2) * ∫ x in Ω, ‖gradient w x‖ ^ 2

lemma divergence_theorem_vector (F : E → E) (s : Set E) (n : E → E)
  [h_domain : HasPDEDomain s]
  (hn_normal : IsOutwardUnitNormal s n)
  (h_diff : ContDiffOn ℝ 1 F s)
  (h_cont : ContinuousOn F (closure s)) :
  ∫ x in s, div_fieldWithin F (closure s) x ∂volume =
  ∫ x in frontier s, ⟪F x, n x⟫_ℝ ∂(Measure.hausdorffMeasure 2) :=
sorry

lemma trace_smulRight_eq (f : E →ₗ[ℝ] ℝ) (F : E) :
  LinearMap.trace ℝ E (f.smulRight F) = f F := by
  let b := Module.Free.chooseBasis ℝ E
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  have h_trace : ((LinearMap.toMatrix b b) (f.smulRight F)).trace = ∑ x, (b.repr F) x * f (b x) := by
    simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, LinearMap.smulRight_apply, mul_comm]
  rw [h_trace]
  have h_smul : ∀ x, (b.repr F) x * f (b x) = f ((b.repr F) x • b x) := by
    intro x
    rw [LinearMap.map_smul, smul_eq_mul]
  simp_rw [h_smul]
  rw [← map_sum]
  rw [b.sum_repr F]

lemma trace_smulRight_fderiv_eq_inner (v : E → ℝ) (F : E) (s : Set E) (x : E)
  (hs : IsOpen s) (hx : x ∈ s) :
  LinearMap.trace ℝ E ((fderivWithin ℝ v s x).smulRight F : E →ₗ[ℝ] E) =
  ⟪gradient v x, F⟫_ℝ := by
  change LinearMap.trace ℝ E (LinearMap.smulRight (fderivWithin ℝ v s x : E →ₗ[ℝ] ℝ) F) = ⟪gradient v x, F⟫_ℝ
  rw [trace_smulRight_eq]
  rw [fderivWithin_of_isOpen hs hx]
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]
  simp

lemma trace_fderivWithin_smul (v : E → ℝ) (F : E → E) (s : Set E) (x : E)
  (hs : IsOpen s) (hx : x ∈ s)
  (hv_diff : DifferentiableWithinAt ℝ v s x)
  (hF_diff : DifferentiableWithinAt ℝ F s x) :
  LinearMap.trace ℝ E (fderivWithin ℝ (fun y => v y • F y) s x) =
  LinearMap.trace ℝ E ((fderivWithin ℝ v s x).smulRight (F x) : E →ₗ[ℝ] E) +
  v x * LinearMap.trace ℝ E (fderivWithin ℝ F s x) := by
  have h_eq : (fun y => v y • F y) = v • F := rfl
  rw [h_eq]
  rw [fderivWithin_smul (hs.uniqueDiffOn x hx) hv_diff hF_diff]
  push_cast
  rw [LinearMap.map_add]
  rw [LinearMap.map_smul]
  simp_rw [smul_eq_mul]
  linarith

lemma boundary_inner_smul (u v : E → ℝ) (n : E → E) (x : E) :
  ⟪v x • gradient u x, n x⟫_ℝ = v x * ⟪gradient u x, n x⟫_ℝ := by
  rw [real_inner_smul_left]

lemma inner_grad_comm (u v : E → ℝ) (x : E) :
  ⟪gradient v x, gradient u x⟫_ℝ = ⟪gradient u x, gradient v x⟫_ℝ := by
  rw [real_inner_comm]

lemma div_scalar_mul_gradient (u v : E → ℝ) (s : Set E) (x : E)
  (hs : IsOpen s) (hx : x ∈ s)
  (hv_diff : DifferentiableWithinAt ℝ v s x)
  (hu_diff : DifferentiableWithinAt ℝ (fun y => gradient u y) s x) :
  div_fieldWithin (fun y => v y • gradient u y) s x =
  ⟪gradient v x, gradient u x⟫_ℝ + v x * laplacianWithin u s x := by
  unfold div_fieldWithin laplacianWithin
  rw [trace_fderivWithin_smul v (fun y => gradient u y) s x hs hx hv_diff hu_diff]
  rw [trace_smulRight_fderiv_eq_inner v (gradient u x) s x hs hx]
  unfold div_fieldWithin
  have h_grad_eq : fderivWithin ℝ (fun y => gradient u y) s x = fderivWithin ℝ (gradientWithin u s) s x := by
    apply fderivWithin_congr
    · intro y hy
      unfold gradient gradientWithin
      rw [fderivWithin_of_isOpen hs hy]
    · unfold gradient gradientWithin
      rw [fderivWithin_of_isOpen hs hx]

  rw [h_grad_eq]

lemma greens_first_identity (Ω : Set E) (u v : E → ℝ) (n : E → E)
  [h_domain : HasPDEDomain Ω] (hn : IsOutwardUnitNormal Ω n)
  (h_F_diff : ContDiffOn ℝ 1 (fun x => v x • gradient u x) Ω)
  (h_F_cont : ContinuousOn (fun x => v x • gradient u x) (closure Ω))
  (h_int_grad : IntegrableOn (fun x => ⟪gradient u x, gradient v x⟫_ℝ) Ω)
  (h_int_lap : IntegrableOn (fun x => v x * laplacianWithin u (closure Ω) x) Ω) :
  ∫ x in Ω, ⟪gradient u x, gradient v x⟫_ℝ =
  (∫ x in frontier Ω, v x * ⟪gradient u x, n x⟫_ℝ ∂surfaceArea) - ∫ x in Ω, v x * laplacianWithin u (closure Ω) x := by
  sorry

  -- have h_div := divergence_theorem_vector (fun x => v x • gradient u x) Ω n hn h_F_diff h_F_cont

  -- have h_lhs : (fun x => div_fieldWithin (fun y => v y • gradient u y) (closure Ω) x) =
  --              (fun x => ⟪gradient v x, gradient u x⟫_ℝ + v x * laplacianWithin u (closure Ω) x) := by
  --   ext x
  --   rw [div_scalar_mul_gradient_closure u v Ω x]

  -- have h_rhs : (fun x => ⟪v x • gradient u x, n x⟫_ℝ) =
  --              (fun x => v x * ⟪gradient u x, n x⟫_ℝ) := by
  --   ext x
  --   rw [boundary_inner_smul u v n x]

  -- rw [h_lhs, h_rhs] at h_div

  -- have h_symm_func : (fun x => ⟪gradient v x, gradient u x⟫_ℝ) = (fun x => ⟪gradient u x, gradient v x⟫_ℝ) := by
  --   ext x
  --   rw [inner_grad_comm u v x]

  -- have h_int_grad_symm : IntegrableOn (fun x => ⟪gradient v x, gradient u x⟫_ℝ) Ω := by
  --   rw [h_symm_func]
  --   exact h_int_grad

  -- rw [integral_add h_int_grad_symm h_int_lap] at h_div
  -- rw [h_symm_func] at h_div

  -- exact eq_sub_of_add_eq h_div


lemma test_function_boundary_integral (Ω : Set E) (u v : E → ℝ) (n : E → E)
  (hv : IsTestFunction Ω v) :
  ∫ x in frontier Ω, v x * ⟪gradient u x, n x⟫_ℝ ∂surfaceArea = 0 := by
  have heq : Set.EqOn (fun x => v x * ⟪gradient u x, n x⟫_ℝ) (fun x => 0) (frontier Ω) := by
    intro x hx
    simp_rw [hv.2 x hx, zero_mul]
  rw [setIntegral_congr_fun isClosed_frontier.measurableSet heq]
  rw [integral_zero]

lemma harmonic_volume_integral (Ω : Set E) (u v : E → ℝ)
  (h_domain : HasPDEDomain Ω)
  (hu_harm : IsHarmonic u Ω) :
  ∫ x in Ω, v x * laplacian u x = 0 := by
  have heq : Set.EqOn (fun x => v x * laplacian u x) (fun x => 0) Ω := by
    intro x hx
    unfold IsHarmonic at hu_harm
    simp_rw [hu_harm x hx, mul_zero]
  rw [setIntegral_congr_fun h_domain.is_open.measurableSet heq]
  rw [integral_zero]

lemma admissible_sub_boundary (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) (x : E) (hx : x ∈ frontier Ω) :
  (u - w) x = 0 := by
  have hu_bound : u x = h x := hu_admis.2.2.1 x hx
  have hw_bound : w x = h x := hw_admis.2.2.1 x hx
  rw [Pi.sub_apply, hu_bound, hw_bound]
  ring

lemma laplacianWithin_closure_eq_laplacian (u : E → ℝ) (Ω : Set E) (h_open : IsOpen Ω) (x : E) (hx : x ∈ Ω) :
  laplacianWithin u (closure Ω) x = laplacian u x := by
  have h_nhds : closure Ω ∈ 𝓝 x := Filter.mem_of_superset (h_open.mem_nhds hx) subset_closure
  have h_ev_eq : gradientWithin u (closure Ω) =ᶠ[𝓝 x] gradient u := by
    apply Filter.eventuallyEq_of_mem (h_open.mem_nhds hx)
    intro y hy
    have h_nhds_y : closure Ω ∈ 𝓝 y := Filter.mem_of_superset (h_open.mem_nhds hy) subset_closure
    unfold gradientWithin gradient
    rw [fderivWithin_of_mem_nhds h_nhds_y]
  unfold laplacianWithin laplacian div_fieldWithin div_field
  rw [fderivWithin_of_mem_nhds h_nhds]
  rw [h_ev_eq.fderiv_eq]

lemma harmonic_laplacian_zero (u : E → ℝ) (Ω : Set E) (x : E) (hx : x ∈ Ω)
  [h_domain : HasPDEDomain Ω]
  (h_harm : IsHarmonic u Ω) :
  laplacianWithin u (closure Ω) x = 0 := by
  rw [laplacianWithin_closure_eq_laplacian u Ω h_domain.is_open x hx]
  exact h_harm x hx

lemma contDiffOn_gradient_continuousOn {f : E → ℝ} {s : Set E}
  (hf : ContDiffOn ℝ 2 f s) (hs : IsOpen s) :
  ContinuousOn (fun x => gradient f x) s := by
  have h_fderiv_within : ContinuousOn (fun x => fderivWithin ℝ f s x) s :=
    hf.continuousOn_fderivWithin hs.uniqueDiffOn (by decide)
  have h_fderiv : ContinuousOn (fun x => fderiv ℝ f x) s := by
    apply ContinuousOn.congr h_fderiv_within
    intro x hx
    exact (fderivWithin_of_isOpen hs hx).symm
  have h_lin : Continuous (fun L => (toDual ℝ E).symm L) := (toDual ℝ E).symm.continuous
  unfold gradient
  exact h_lin.comp_continuousOn h_fderiv

lemma admissible_cross_measurable (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (h_domain : HasPDEDomain Ω) (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) :
  AEStronglyMeasurable (fun x => ⟪gradient u x, gradient (u - w) x⟫_ℝ) (volume.restrict Ω) := by
  have hu_grad_cont : ContinuousOn (fun x => gradient u x) Ω :=
    contDiffOn_gradient_continuousOn hu_admis.1 h_domain.is_open
  have hsub_grad_cont : ContinuousOn (fun x => gradient (u - w) x) Ω :=
    contDiffOn_gradient_continuousOn (hu_admis.1.sub hw_admis.1) h_domain.is_open
  have h_inner_cont : ContinuousOn (fun x => ⟪gradient u x, gradient (u - w) x⟫_ℝ) Ω :=
    hu_grad_cont.inner hsub_grad_cont
  exact h_inner_cont.aestronglyMeasurable h_domain.is_open.measurableSet

lemma admissible_differentiableAt (Ω : Set E) (h : E → ℝ) (u : E → ℝ) (x : E)
  (h_domain : HasPDEDomain Ω) (hu_admis : IsAdmissible Ω h u) (hx : x ∈ Ω) :
  DifferentiableAt ℝ u x := by
  have h_diff : DifferentiableOn ℝ u Ω := hu_admis.1.differentiableOn (by decide)
  have hd_within : DifferentiableWithinAt ℝ u Ω x := h_diff x hx
  have h_nhds : Ω ∈ 𝓝 x := h_domain.is_open.mem_nhds hx
  exact hd_within.differentiableAt h_nhds

lemma gradient_sub_pointwise (u w : E → ℝ) (x : E)
  (hu : DifferentiableAt ℝ u x) (hw : DifferentiableAt ℝ w x) :
  gradient (u - w) x = gradient u x - gradient w x := by
  unfold gradient
  rw [fderiv_sub hu hw]
  simp only [map_sub]

lemma norm_sub_sq_bound (a b : E) :
  ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h_pl : ‖a + b‖ * ‖a + b‖ + ‖a - b‖ * ‖a - b‖ = 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) := parallelogram_law_with_norm ℝ a b
  calc
    ‖a - b‖ ^ 2 = ‖a - b‖ * ‖a - b‖ := by ring
    _ ≤ ‖a + b‖ * ‖a + b‖ + ‖a - b‖ * ‖a - b‖ := by
      have h_pos : 0 ≤ ‖a + b‖ * ‖a + b‖ := by positivity
      linarith
    _ = 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) := h_pl
    _ = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by ring

lemma gradient_sub_sq_bound_pointwise (Ω : Set E) (h : E → ℝ) (u w : E → ℝ) (x : E)
  (h_domain : HasPDEDomain Ω) (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) (hx : x ∈ Ω) :
  ‖gradient (u - w) x‖ ^ 2 ≤ 2 * ‖gradient u x‖ ^ 2 + 2 * ‖gradient w x‖ ^ 2 := by
  have hu_diff := admissible_differentiableAt Ω h u x h_domain hu_admis hx
  have hw_diff := admissible_differentiableAt Ω h w x h_domain hw_admis hx
  rw [gradient_sub_pointwise u w x hu_diff hw_diff]
  exact norm_sub_sq_bound (gradient u x) (gradient w x)

lemma contDiffOn_gradient_norm_sq_continuousOn {f : E → ℝ} {s : Set E}
  (hf : ContDiffOn ℝ 2 f s) (hs : IsOpen s) :
  ContinuousOn (fun x => ‖gradient f x‖ ^ 2) s := by
  have h_grad_cont : ContinuousOn (fun x => gradient f x) s := contDiffOn_gradient_continuousOn hf hs
  exact (h_grad_cont.norm).pow 2

lemma inner_bound (a b : E) : ‖⟪a, b⟫_ℝ‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h1 : ‖⟪a, b⟫_ℝ‖ ≤ ‖a‖ * ‖b‖ := norm_inner_le_norm a b
  have h2 : 0 ≤ (‖a‖ - ‖b‖) ^ 2 := sq_nonneg (‖a‖ - ‖b‖)
  have h3 : (‖a‖ - ‖b‖) ^ 2 = ‖a‖ ^ 2 - 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by ring
  nlinarith

lemma admissible_diff_measurable (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (h_domain : HasPDEDomain Ω) (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) :
  AEStronglyMeasurable (fun x => ‖gradient (u - w) x‖ ^ 2) (volume.restrict Ω) := by
  have h_sub_diff : ContDiffOn ℝ 2 (u - w) Ω := hu_admis.1.sub hw_admis.1
  have h_cont : ContinuousOn (fun x => ‖gradient (u - w) x‖ ^ 2) Ω :=
  contDiffOn_gradient_norm_sq_continuousOn h_sub_diff h_domain.is_open
  exact h_cont.aestronglyMeasurable h_domain.is_open.measurableSet

lemma admissible_diff_integrable (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (h_domain : HasPDEDomain Ω)
  (hu_admis : IsAdmissible Ω h u)
  (hw_admis : IsAdmissible Ω h w) :
  IntegrableOn (fun x => ‖gradient (u - w) x‖ ^ 2) Ω := by
  have h_int_u : IntegrableOn (fun x => ‖gradient u x‖ ^ 2) Ω := hu_admis.2.2.2
  have h_int_w : IntegrableOn (fun x => ‖gradient w x‖ ^ 2) Ω := hw_admis.2.2.2
  have h_int_bound : IntegrableOn (fun x => 2 * ‖gradient u x‖ ^ 2 + 2 * ‖gradient w x‖ ^ 2) Ω :=
    (h_int_u.const_mul 2).add (h_int_w.const_mul 2)
  apply Integrable.mono' h_int_bound
  · exact admissible_diff_measurable Ω h u w h_domain hu_admis hw_admis
  · rw [ae_restrict_iff' h_domain.is_open.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have h_pos : 0 ≤ ‖gradient (u - w) x‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h_pos]
    exact gradient_sub_sq_bound_pointwise Ω h u w x h_domain hu_admis hw_admis hx

lemma admissible_cross_integrable (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (h_domain : HasPDEDomain Ω)
  (hu_admis : IsAdmissible Ω h u)
  (hw_admis : IsAdmissible Ω h w) :
  IntegrableOn (fun x => ⟪gradient u x, gradient (u - w) x⟫_ℝ) Ω := by
  have h_int_u : IntegrableOn (fun x => ‖gradient u x‖ ^ 2) Ω := hu_admis.2.2.2
  have h_int_sub : IntegrableOn (fun x => ‖gradient (u - w) x‖ ^ 2) Ω :=
    admissible_diff_integrable Ω h u w h_domain hu_admis hw_admis
  have h_int_bound : IntegrableOn (fun x => ‖gradient u x‖ ^ 2 + ‖gradient (u - w) x‖ ^ 2) Ω :=
    h_int_u.add h_int_sub
  apply Integrable.mono' h_int_bound
  · exact admissible_cross_measurable Ω h u w h_domain hu_admis hw_admis
  · rw [ae_restrict_iff' h_domain.is_open.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro x _
    exact inner_bound (gradient u x) (gradient (u - w) x)

lemma gradient_c1_of_c2 (u : E → ℝ) (Ω : Set E) (h_open : IsOpen Ω) (h_smooth : ContDiffOn ℝ 2 u Ω) :
  ContDiffOn ℝ 1 (fun x => gradient u x) Ω := by
  have hgrad : gradientWithin u Ω = (InnerProductSpace.toDual ℝ E).symm ∘ fderivWithin ℝ u Ω := by
    ext x
    rfl
  have hfw : ContDiffOn ℝ 1 (fderivWithin ℝ u Ω) Ω :=
    h_smooth.fderivWithin h_open.uniqueDiffOn (by norm_num)
  have hgrad_within : ContDiffOn ℝ 1 (gradientWithin u Ω) Ω := by
    rw [hgrad]
    exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn hfw
  have h_eq : ∀ x ∈ Ω, gradient u x = gradientWithin u Ω x := by
    intro x hx
    exact (gradientWithin_eq_gradient_of_isOpen u Ω h_open x hx).symm
  exact hgrad_within.congr h_eq

lemma admissible_cross_diff (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) :
  ContDiffOn ℝ 1 (fun x => (u - w) x • gradient u x) Ω := by
  have h_u_c2 : ContDiffOn ℝ 2 u Ω := hu_admis.1
  have h_w_c2 : ContDiffOn ℝ 2 w Ω := hw_admis.1
  have h_u_c1 : ContDiffOn ℝ 1 u Ω := h_u_c2.of_le (by decide)
  have h_w_c1 : ContDiffOn ℝ 1 w Ω := h_w_c2.of_le (by decide)
  have h_sub : ContDiffOn ℝ 1 (fun x => (u - w) x) Ω := h_u_c1.sub h_w_c1
  have h_grad : ContDiffOn ℝ 1 (fun x => gradient u x) Ω := gradient_c1_of_c2 u Ω h_domain.is_open h_u_c2
  exact h_sub.smul h_grad

lemma admissible_cross_cont (Ω : Set E) (h : E → ℝ) (u w : E → ℝ)
  (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w) :
  ContinuousOn (fun x => (u - w) x • gradient u x) (closure Ω) := by
  have h_u_cont : ContinuousOn u (closure Ω) := hu_admis.2.1.1
  have h_w_cont : ContinuousOn w (closure Ω) := hw_admis.2.1.1
  have h_grad_cont : ContinuousOn (fun x => gradient u x) (closure Ω) := hu_admis.2.1.2
  have h_sub_cont : ContinuousOn (fun x => (u - w) x) (closure Ω) := h_u_cont.sub h_w_cont
  exact h_sub_cont.smul h_grad_cont

lemma cross_term_vanishing (Ω : Set E) (h : E → ℝ) (u w : E → ℝ) (n : E → E)
  [h_domain : HasPDEDomain Ω] (hn : IsOutwardUnitNormal Ω n)
  (hu_admis : IsAdmissible Ω h u) (hw_admis : IsAdmissible Ω h w)
  (hu_harm : IsHarmonic u Ω) :
  ∫ x in Ω, ⟪gradient u x, gradient (u - w) x⟫_ℝ = 0 := by

  have h_diff : ContDiffOn ℝ 1 (fun x => (u - w) x • gradient u x) Ω :=
    admissible_cross_diff Ω h u w hu_admis hw_admis

  have h_cont : ContinuousOn (fun x => (u - w) x • gradient u x) (closure Ω) :=
    admissible_cross_cont Ω h u w hu_admis hw_admis

  have h_int_grad : IntegrableOn (fun x => ⟪gradient u x, gradient (u - w) x⟫_ℝ) Ω :=
    admissible_cross_integrable Ω h u w h_domain hu_admis hw_admis

  have h_int_lap : IntegrableOn (fun x => (u - w) x * laplacianWithin u (closure Ω) x) Ω := by
    apply IntegrableOn.congr_fun integrableOn_zero
    · intro x hx
      have h_zero := harmonic_laplacian_zero u Ω x hx hu_harm
      simp_rw [h_zero]
      ring
    · exact h_domain.is_open.measurableSet


  rw [greens_first_identity Ω u (u - w) n hn h_diff h_cont h_int_grad h_int_lap]

  have h_bound : ∫ x in frontier Ω, (u - w) x * ⟪gradient u x, n x⟫_ℝ ∂surfaceArea = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have h_zero : (u - w) x = 0 := admissible_sub_boundary Ω h u w hu_admis hw_admis x hx
    rw [h_zero]
    ring

  have h_vol : ∫ x in Ω, (u - w) x * laplacianWithin u (closure Ω) x = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have h_lap_zero : laplacianWithin u (closure Ω) x = 0 := harmonic_laplacian_zero u Ω x hx hu_harm
    rw [h_lap_zero]
    ring

  rw [h_bound, h_vol]
  ring

lemma pointwise_energy_expansion (a b : E) :
  (1 / 2 : ℝ) * ‖b‖ ^ 2 = (1 / 2 : ℝ) * ‖a‖ ^ 2 - ⟪a, a - b⟫_ℝ + (1 / 2 : ℝ) * ‖a - b‖ ^ 2 := by
  have h1 : ‖b‖ ^ 2 = ⟪b, b⟫_ℝ := (real_inner_self_eq_norm_sq b).symm
  have h2 : ‖a‖ ^ 2 = ⟪a, a⟫_ℝ := (real_inner_self_eq_norm_sq a).symm
  have h3 : ‖a - b‖ ^ 2 = ⟪a - b, a - b⟫_ℝ := (real_inner_self_eq_norm_sq (a - b)).symm
  rw [h1, h2, h3]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm b a]
  ring

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

  have h_in_w : (1 / 2 : ℝ) * ∫ x in Ω, ‖gradient w x‖ ^ 2 = ∫ x in Ω, (1 / 2 : ℝ) * ‖gradient w x‖ ^ 2 :=
    (integral_const_mul (1 / 2 : ℝ) (fun x => ‖gradient w x‖ ^ 2)).symm
  have h_in_u : (1 / 2 : ℝ) * ∫ x in Ω, ‖gradient u x‖ ^ 2 = ∫ x in Ω, (1 / 2 : ℝ) * ‖gradient u x‖ ^ 2 :=
    (integral_const_mul (1 / 2 : ℝ) (fun x => ‖gradient u x‖ ^ 2)).symm
  have h_in_sub : (1 / 2 : ℝ) * ∫ x in Ω, ‖gradient (u - w) x‖ ^ 2 = ∫ x in Ω, (1 / 2 : ℝ) * ‖gradient (u - w) x‖ ^ 2 :=
    (integral_const_mul (1 / 2 : ℝ) (fun x => ‖gradient (u - w) x‖ ^ 2)).symm

  rw [h_in_w, h_in_u, h_in_sub]

  have h_pointwise : ∫ x in Ω, (1 / 2 : ℝ) * ‖gradient w x‖ ^ 2 =
                     ∫ x in Ω, ((1 / 2 : ℝ) * ‖gradient u x‖ ^ 2 - ⟪gradient u x, gradient (u - w) x⟫_ℝ + (1 / 2 : ℝ) * ‖gradient (u - w) x‖ ^ 2) := by
    apply setIntegral_congr_fun h_domain.is_open.measurableSet
    intro x hx
    have hu_diff := admissible_differentiableAt Ω h u x h_domain hu_admis hx
    have hw_diff := admissible_differentiableAt Ω h w x h_domain hw_admis hx
    simp_rw [pointwise_energy_expansion (gradient u x) (gradient w x)]
    rw [gradient_sub_pointwise u w x hu_diff hw_diff]

  rw [h_pointwise]

  have h_split1 : ∫ x in Ω, ((1 / 2 : ℝ) * ‖gradient u x‖ ^ 2 - ⟪gradient u x, gradient (u - w) x⟫_ℝ + (1 / 2 : ℝ) * ‖gradient (u - w) x‖ ^ 2) =
                  (∫ x in Ω, (1 / 2 : ℝ) * ‖gradient u x‖ ^ 2 - ⟪gradient u x, gradient (u - w) x⟫_ℝ) + ∫ x in Ω, (1 / 2 : ℝ) * ‖gradient (u - w) x‖ ^ 2 :=
    integral_add (h_int_u.sub h_int_cross) h_int_sub
  rw [h_split1]

  have h_split2 : ∫ x in Ω, (1 / 2 : ℝ) * ‖gradient u x‖ ^ 2 - ⟪gradient u x, gradient (u - w) x⟫_ℝ =
                  (∫ x in Ω, (1 / 2 : ℝ) * ‖gradient u x‖ ^ 2) - ∫ x in Ω, ⟪gradient u x, gradient (u - w) x⟫_ℝ :=
    integral_sub h_int_u h_int_cross
  rw [h_split2]

lemma energy_nonnegative (Ω : Set E) (v : E → ℝ) :
  DirichletEnergy Ω v ≥ 0 := by
  unfold DirichletEnergy
  positivity

theorem dirichlet_principle_backward (Ω : Set E) (h : E → ℝ) (u : E → ℝ) (n : E → E)
  [h_domain : HasPDEDomain Ω] (hn : IsOutwardUnitNormal Ω n)
  (hu_admis : IsAdmissible Ω h u) (hu_harm : IsHarmonic u Ω) :
  ∀ w, IsAdmissible Ω h w → DirichletEnergy Ω w ≥ DirichletEnergy Ω u := by
  intro w hw_admis

  have h_cross : ∫ x in Ω, ⟪gradient u x, gradient (u - w) x⟫_ℝ = 0 :=
    cross_term_vanishing Ω h u w n hn hu_admis hw_admis hu_harm

  have h_energy_expansion : DirichletEnergy Ω w =
    DirichletEnergy Ω u - (∫ x in Ω, ⟪gradient u x, gradient (u - w) x⟫_ℝ) + DirichletEnergy Ω (u - w) :=
    energy_expansion Ω h u w h_domain hu_admis hw_admis

  have h_energy_eq : DirichletEnergy Ω w = DirichletEnergy Ω u + DirichletEnergy Ω (u - w) := by
    rw [h_energy_expansion, h_cross]
    ring

  have h_energy_v_nonneg : DirichletEnergy Ω (u - w) ≥ 0 :=
    energy_nonnegative Ω (u - w)

  linarith [h_energy_eq, h_energy_v_nonneg]

-- PROVING THE FORWARD STEP

lemma first_variation_vanishes (Ω : Set E) (h : E → ℝ) (u : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u)
  (h_min : ∀ w, IsAdmissible Ω h w → DirichletEnergy Ω u ≤ DirichletEnergy Ω w) :
  ∀ v, IsAdmissible Ω (fun _ => 0) v → ∫ x in Ω, ⟪gradient u x, gradient v x⟫_ℝ = 0 :=
sorry

lemma admissible_test_diff (Ω : Set E) (h : E → ℝ) (u v : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u) (hv_admis : IsAdmissible Ω (fun _ => 0) v) :
  ContDiffOn ℝ 1 (fun x => v x • gradient u x) Ω := by
  have h_u_c2 : ContDiffOn ℝ 2 u Ω := hu_admis.1
  have h_v_c2 : ContDiffOn ℝ 2 v Ω := hv_admis.1
  have h_v_c1 : ContDiffOn ℝ 1 v Ω := h_v_c2.of_le (by decide)
  have h_grad : ContDiffOn ℝ 1 (fun x => gradient u x) Ω := gradient_c1_of_c2 u Ω h_domain.is_open h_u_c2
  exact h_v_c1.smul h_grad

lemma admissible_test_cont (Ω : Set E) (h : E → ℝ) (u v : E → ℝ)
  (hu_admis : IsAdmissible Ω h u) (hv_admis : IsAdmissible Ω (fun _ => 0) v) :
  ContinuousOn (fun x => v x • gradient u x) (closure Ω) := by
  have h_v_cont : ContinuousOn v (closure Ω) := hv_admis.2.1.1
  have h_grad_cont : ContinuousOn (fun x => gradient u x) (closure Ω) := hu_admis.2.1.2
  exact h_v_cont.smul h_grad_cont

lemma continuous_trace : Continuous (fun (L : E →L[ℝ] E) => LinearMap.trace ℝ E (L : E →ₗ[ℝ] E)) := by
  let traceLM : (E →L[ℝ] E) →ₗ[ℝ] ℝ := {
    toFun := fun L => LinearMap.trace ℝ E (L : E →ₗ[ℝ] E)
    map_add' := fun x y => by simp
    map_smul' := fun c x => by simp
  }
  exact LinearMap.continuous_of_finiteDimensional traceLM

lemma fderiv_continuousOn_of_c1 (F : E → E) (Ω : Set E) (h_open : IsOpen Ω)
  (h_smooth : ContDiffOn ℝ 1 F Ω) :
  ContinuousOn (fun x => fderiv ℝ F x) Ω := by
  have h_fderiv_within := h_smooth.continuousOn_fderivWithin h_open.uniqueDiffOn (by decide)
  apply ContinuousOn.congr h_fderiv_within
  intro x hx
  exact (fderivWithin_of_isOpen h_open hx).symm

lemma laplacian_continuous_of_c2 (u : E → ℝ) (Ω : Set E)
  [h_domain : HasPDEDomain Ω] (h_smooth : ContDiffOn ℝ 2 u Ω) :
  ContinuousOn (laplacian u) Ω := by
  have h_grad_c1 : ContDiffOn ℝ 1 (fun x => gradient u x) Ω :=
    gradient_c1_of_c2 u Ω h_domain.is_open h_smooth
  have h_fderiv_cont : ContinuousOn (fun x => fderiv ℝ (fun y => gradient u y) x) Ω :=
    fderiv_continuousOn_of_c1 (fun x => gradient u x) Ω h_domain.is_open h_grad_c1
  unfold laplacian div_field
  exact continuous_trace.comp_continuousOn h_fderiv_cont

lemma admissible_test_integrable (Ω : Set E) (h : E → ℝ) (u v : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hu_admis : IsAdmissible Ω h u) (hv_admis : IsAdmissible Ω (fun _ => 0) v) :
  IntegrableOn (fun x => ⟪gradient u x, gradient v x⟫_ℝ) Ω := by
  have h_int_u : IntegrableOn (fun x => ‖gradient u x‖ ^ 2) Ω := hu_admis.2.2.2
  have h_int_v : IntegrableOn (fun x => ‖gradient v x‖ ^ 2) Ω := hv_admis.2.2.2

  have h_int_bound : IntegrableOn (fun x => ‖gradient u x‖ ^ 2 + ‖gradient v x‖ ^ 2) Ω :=
    h_int_u.add h_int_v

  have h_grad_u_cont : ContinuousOn (fun x => gradient u x) Ω :=
    contDiffOn_gradient_continuousOn hu_admis.1 h_domain.is_open

  have h_grad_v_cont : ContinuousOn (fun x => gradient v x) Ω :=
    contDiffOn_gradient_continuousOn hv_admis.1 h_domain.is_open

  have h_inner_cont : ContinuousOn (fun x => ⟪gradient u x, gradient v x⟫_ℝ) Ω :=
    h_grad_u_cont.inner h_grad_v_cont

  apply Integrable.mono' h_int_bound
  · exact h_inner_cont.aestronglyMeasurable h_domain.is_open.measurableSet
  · rw [ae_restrict_iff' h_domain.is_open.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro x _
    exact inner_bound (gradient u x) (gradient v x)

lemma greens_zero_boundary (Ω : Set E) (h : E → ℝ) (u v : E → ℝ) (n : E → E)
  [h_domain : HasPDEDomain Ω] (hn : IsOutwardUnitNormal Ω n)
  (hu_admis : IsAdmissible Ω h u) (hv_admis : IsAdmissible Ω (fun _ => 0) v)
  (h_lap_int : IntegrableOn (fun x => v x * laplacianWithin u (closure Ω) x) Ω) : -- NOT SURE IF THIS SHOULD BE HERE
  ∫ x in Ω, ⟪gradient u x, gradient v x⟫_ℝ = - ∫ x in Ω, v x * laplacian u x := by
  have h_diff : ContDiffOn ℝ 1 (fun x => v x • gradient u x) Ω :=
    admissible_test_diff Ω h u v hu_admis hv_admis
  have h_cont : ContinuousOn (fun x => v x • gradient u x) (closure Ω) :=
    admissible_test_cont Ω h u v hu_admis hv_admis
  have h_int_grad : IntegrableOn (fun x => ⟪gradient u x, gradient v x⟫_ℝ) Ω :=
    admissible_test_integrable Ω h u v hu_admis hv_admis

  have h_green := greens_first_identity Ω u v n hn h_diff h_cont h_int_grad h_lap_int

  have h_bound : ∫ x in frontier Ω, v x * ⟪gradient u x, n x⟫_ℝ ∂surfaceArea = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have h_v_zero : v x = 0 := hv_admis.2.2.1 x hx
    rw [h_v_zero]
    ring

  have h_lap_eq : ∫ x in Ω, v x * laplacianWithin u (closure Ω) x = ∫ x in Ω, v x * laplacian u x := by
    apply setIntegral_congr_fun h_domain.is_open.measurableSet
    intro x hx
    simp_rw [laplacianWithin_closure_eq_laplacian u Ω h_domain.is_open x hx]

  rw [h_bound, h_lap_eq] at h_green
  linarith

lemma integral_to_pointwise (Ω : Set E) (f : E → ℝ)
  [h_domain : HasPDEDomain Ω]
  (hf_cont : ContinuousOn f Ω)
  (h_ortho : ∀ v, IsAdmissible Ω (fun _ => 0) v → ∫ x in Ω, v x * f x = 0) :
  ∀ x ∈ Ω, f x = 0 :=
sorry

theorem dirichlet_principle_forward (Ω : Set E) (h : E → ℝ) (u : E → ℝ) (n : E → E)
  [h_domain : HasPDEDomain Ω] (hn : IsOutwardUnitNormal Ω n)
  (hu_admis : IsAdmissible Ω h u)
  (h_min : ∀ w, IsAdmissible Ω h w → DirichletEnergy Ω u ≤ DirichletEnergy Ω w) :
  IsHarmonic u Ω := by

  have h_lap_cont : ContinuousOn (laplacian u) Ω :=
    laplacian_continuous_of_c2 u Ω hu_admis.1

  have h_ortho : ∀ v, IsAdmissible Ω (fun _ => 0) v → ∫ x in Ω, v x * laplacian u x = 0 := by
    intro v hv_admis
    have h_var := first_variation_vanishes Ω h u hu_admis h_min v hv_admis
    have h_lap_int : IntegrableOn (fun x => v x * laplacianWithin u (closure Ω) x) Ω := sorry
    have h_green := greens_zero_boundary Ω h u v n hn hu_admis hv_admis h_lap_int

    rw [h_var] at h_green
    linarith

  intro x hx
  exact integral_to_pointwise Ω (laplacian u) h_lap_cont h_ortho x hx
