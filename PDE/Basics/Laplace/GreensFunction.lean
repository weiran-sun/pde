import PDE.Basics.Laplace.RepresentationFormula

open Real Set MeasureTheory Metric Filter Function Pointwise InnerProductSpace RealInnerProductSpace
open scoped BigOperators Topology

def IsGreensFunction (G : E → E → ℝ) (Ω : Set E) : Prop :=
  ∀ x₀ ∈ Ω, ∃ H : E → ℝ,
    ContinuousOn H (closure Ω) ∧
    ContDiffOn ℝ ⊤ H Ω ∧
    IsHarmonic H Ω ∧
    (∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x) ∧
    (∀ x ∈ frontier Ω, G x x₀ = 0) ∧
    (∀ x ∈ frontier Ω, H x = -fundamental_sol_3d (x - x₀))

lemma combine_greens_representation_integrals
  (Ω : Set E)
  (x₀ : E)
  (u H : E → ℝ)
  (G : E → E → ℝ)
  (n : E → E)
  (h_G_val : ∀ x ∈ frontier Ω, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (h_G_grad : ∀ x ∈ frontier Ω, gradientWithin (fun y => G y x₀) (closure Ω) x =
    gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure Ω) x + gradientWithin H (closure Ω) x)
  (h_int_Phi : IntegrableOn (fun x => u x * ⟪n x, gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure Ω) x⟫_ℝ - fundamental_sol_3d (x - x₀) * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) (frontier Ω) surfaceArea)
  (h_int_H : IntegrableOn (fun x => u x * ⟪n x, gradientWithin H (closure Ω) x⟫_ℝ - H x * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) (frontier Ω) surfaceArea) :
  ∫ x in frontier Ω, (u x * ⟪n x, gradientWithin (fun y => G y x₀) (closure Ω) x⟫_ℝ - G x x₀ * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) ∂surfaceArea =
  ∫ x in frontier Ω, (u x * ⟪n x, gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure Ω) x⟫_ℝ - fundamental_sol_3d (x - x₀) * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) ∂surfaceArea +
  ∫ x in frontier Ω, (u x * ⟪n x, gradientWithin H (closure Ω) x⟫_ℝ - H x * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) ∂surfaceArea := by
  rw [← MeasureTheory.integral_add h_int_Phi h_int_H]
  exact MeasureTheory.setIntegral_congr_fun isClosed_frontier.measurableSet fun x hx => by
    rw [h_G_val x hx, h_G_grad x hx, inner_add_right]
    ring

lemma greens_boundary_val_eq
  (Ω : Set E) (x₀ : E) (G : E → E → ℝ) (H : E → ℝ)
  (hG_zero : ∀ x ∈ frontier Ω, G x x₀ = 0)
  (hH_cancel : ∀ x ∈ frontier Ω, H x = -fundamental_sol_3d (x - x₀)) :
  ∀ x ∈ frontier Ω, G x x₀ = fundamental_sol_3d (x - x₀) + H x :=
  fun x hx => by rw [hG_zero x hx, hH_cancel x hx]; ring

lemma greens_func_eq_on_closure_diff
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (x₀ : E)
  (G : E → E → ℝ) (H : E → ℝ)
  (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hG_val_eq : ∀ x ∈ frontier Ω, G x x₀ = fundamental_sol_3d (x - x₀) + H x) :
  Set.EqOn (fun y => G y x₀) (fun y => fundamental_sol_3d (y - x₀) + H y) (closure Ω \ {x₀}) := by
  rintro y ⟨hy_clos, hy_neq⟩
  by_cases hy_in : y ∈ Ω
  · exact hG_eq y ⟨hy_in, hy_neq⟩
  · exact hG_val_eq y ⟨hy_clos, by rwa [h_domain.is_open.interior_eq]⟩

lemma gradientWithin_greens_func_congr
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (G : E → E → ℝ) (H : E → ℝ)
  (x : E) (hx : x ∈ frontier Ω)
  (h_eq_on : Set.EqOn (fun y => G y x₀) (fun y => fundamental_sol_3d (y - x₀) + H y) (closure Ω \ {x₀})) :
  gradientWithin (fun y => G y x₀) (closure Ω) x = gradientWithin (fun y => fundamental_sol_3d (y - x₀) + H y) (closure Ω) x := by
  have ⟨h_clos, h_not_int⟩ : x ∈ closure Ω \ interior Ω := hx
  have h_x_neq : x ≠ x₀ := by rintro rfl; exact h_not_int (by rwa [h_domain.is_open.interior_eq])
  exact congrArg ⇑(InnerProductSpace.toDual ℝ E).symm <| Filter.EventuallyEq.fderivWithin_eq
    (by filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds h_x_neq), self_mem_nhdsWithin] with y hy_neq hy_clos; exact h_eq_on ⟨hy_clos, hy_neq⟩)
    (h_eq_on ⟨h_clos, h_x_neq⟩)

lemma differentiableWithinAt_fundamental_sol_3d
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (x : E) (hx : x ∈ frontier Ω) :
  DifferentiableWithinAt ℝ (fun y => fundamental_sol_3d (y - x₀)) (closure Ω) x := by
  have h_x_neq : x ≠ x₀ := by rintro rfl; exact hx.2 (by rwa [h_domain.is_open.interior_eq])
  have h_eq : (fun y => fundamental_sol_3d (y - x₀)) = fun y => -1 * (4 * Real.pi * ‖y - x₀‖)⁻¹ := funext fun _ => div_eq_mul_inv (-1 : ℝ) _
  rw [h_eq]
  exact (((differentiable_id.differentiableAt.sub (differentiable_const x₀).differentiableAt).norm ℝ
    (sub_ne_zero.mpr h_x_neq)).const_mul (4 * Real.pi)).inv
    (ne_of_gt (mul_pos (by positivity) (norm_pos_iff.mpr (sub_ne_zero.mpr h_x_neq))))
    |>.const_mul (-1) |>.differentiableWithinAt

lemma gradientWithin_fundamental_add_H
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (H : E → ℝ)
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω))
  (x : E) (hx : x ∈ frontier Ω) :
  gradientWithin (fun y => fundamental_sol_3d (y - x₀) + H y) (closure Ω) x =
    gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure Ω) x + gradientWithin H (closure Ω) x := by
  unfold gradientWithin
  erw [fderivWithin_add (h_domain.unique_diff x hx.1)
    (differentiableWithinAt_fundamental_sol_3d Ω x₀ hx₀ x hx)
    (hH_diff.differentiableOn_one x hx.1)]
  rw [map_add]

lemma greens_boundary_grad_eq
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (G : E → E → ℝ) (H : E → ℝ)
  (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hG_val_eq : ∀ x ∈ frontier Ω, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω)) :
  ∀ x ∈ frontier Ω, gradientWithin (fun y => G y x₀) (closure Ω) x =
    gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure Ω) x + gradientWithin H (closure Ω) x := by
  intro x hx
  rw [gradientWithin_greens_func_congr Ω x₀ hx₀ G H x hx (greens_func_eq_on_closure_diff Ω x₀ G H hG_eq hG_val_eq)]
  exact gradientWithin_fundamental_add_H Ω x₀ hx₀ H hH_diff x hx

lemma fundamental_sol_3d_contDiffOn_compl (x₀ : E) :
  ContDiffOn ℝ 1 (fun y => fundamental_sol_3d (y - x₀)) ({x₀} : Set E)ᶜ := by
  change ContDiffOn ℝ 1 (fun y => -1 / (4 * Real.pi * ‖y - x₀‖)) _
  exact contDiff_const.contDiffOn.div
    (contDiff_const.contDiffOn.mul (ContDiffOn.norm ℝ (contDiff_id.sub contDiff_const).contDiffOn (fun y hy => sub_ne_zero.mpr hy)))
    (fun y hy => ne_of_gt (by have : 0 < ‖y - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy); positivity))

lemma gradient_fundamental_sol_3d_continuousOn (x₀ : E) :
  ContinuousOn (fun x => gradient (fun y => fundamental_sol_3d (y - x₀)) x) ({x₀} : Set E)ᶜ :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
    ((fundamental_sol_3d_contDiffOn_compl x₀).continuousOn_fderiv_of_isOpen isOpen_compl_singleton le_rfl)

lemma fundamental_sol_3d_continuousOn_frontier (Ω : Set E) [h_domain : HasPDEDomain Ω] (x₀ : E) (hx₀ : x₀ ∈ Ω) :
  ContinuousOn (fun x => fundamental_sol_3d (x - x₀)) (frontier Ω) := by
  change ContinuousOn (fun x => -1 / (4 * Real.pi * ‖x - x₀‖)) _
  exact continuousOn_const.div
    (continuousOn_const.mul (continuous_id.sub continuous_const).norm.continuousOn)
    (fun x hx => ne_of_gt (by
      have h_ne : x - x₀ ≠ 0 := fun h => hx.2 (sub_eq_zero.mp h ▸ (h_domain.is_open.interior_eq.symm ▸ hx₀))
      have : 0 < ‖x - x₀‖ := norm_pos_iff.mpr h_ne
      positivity))

lemma fundamental_sol_boundary_term1_continuousOn
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (u : E → ℝ) (hu_cont : ContinuousOn u (closure Ω))
  (n : E → E) (h_cont_n : ContinuousOn n (frontier Ω)) :
  ContinuousOn (fun x => u x * ⟪n x, gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure Ω) x⟫_ℝ) (frontier Ω) := by
  have h_front_sub : frontier Ω ⊆ ({x₀} : Set E)ᶜ :=
    fun x hx h_eq => hx.2 (h_eq.symm ▸ h_domain.is_open.interior_eq.symm ▸ hx₀)
  exact (hu_cont.mono frontier_subset_closure).mul <| h_cont_n.inner <|
    ((gradient_fundamental_sol_3d_continuousOn x₀).mono h_front_sub).congr <| fun x hx =>
      congrArg ⇑(InnerProductSpace.toDual ℝ E).symm <|
        (((fundamental_sol_3d_contDiffOn_compl x₀).differentiableOn (by
        exact
          Ne.symm (zero_ne_one' (WithTop ℕ∞)))).differentiableAt
          (isOpen_compl_singleton.mem_nhds (h_front_sub hx))).fderivWithin
          (h_domain.unique_diff x (frontier_subset_closure hx))

lemma integrable_fundamental_sol_boundary_term1
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (u : E → ℝ) (hu_cont : ContinuousOn u (closure Ω))
  (n : E → E) (h_cont_n : ContinuousOn n (frontier Ω)) :
  IntegrableOn (fun x => u x * ⟪n x, gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure Ω) x⟫_ℝ) (frontier Ω) surfaceArea :=
  integrableOn_frontier_of_continuousOn Ω h_bounded h_area _
    (fundamental_sol_boundary_term1_continuousOn Ω x₀ hx₀ u hu_cont n h_cont_n)

lemma fundamental_sol_boundary_term2_continuousOn
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (n : E → E) (h_cont_n : ContinuousOn n (frontier Ω)) :
  ContinuousOn (fun x => fundamental_sol_3d (x - x₀) * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) (frontier Ω) :=
  (fundamental_sol_3d_continuousOn_frontier Ω x₀ hx₀).mul <| h_cont_n.inner <|
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
      ((hu_diff.of_le (by decide)).continuousOn_fderivWithin h_domain.unique_diff le_rfl)).mono frontier_subset_closure

lemma integrable_fundamental_sol_boundary_term2
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (n : E → E) (h_cont_n : ContinuousOn n (frontier Ω)) :
  IntegrableOn (fun x => fundamental_sol_3d (x - x₀) * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) (frontier Ω) surfaceArea :=
  integrableOn_frontier_of_continuousOn Ω h_bounded h_area _
    (fundamental_sol_boundary_term2_continuousOn Ω x₀ hx₀ u hu_diff n h_cont_n)

lemma integrable_fundamental_sol_boundary
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (u : E → ℝ) (hu_cont : ContinuousOn u (closure Ω)) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (n : E → E) (h_cont_n : ContinuousOn n (frontier Ω)) :
  IntegrableOn (fun x => u x * ⟪n x, gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure Ω) x⟫_ℝ -
    fundamental_sol_3d (x - x₀) * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) (frontier Ω) surfaceArea :=
  Integrable.sub
    (integrable_fundamental_sol_boundary_term1 Ω h_bounded h_area x₀ hx₀ u hu_cont n h_cont_n)
    (integrable_fundamental_sol_boundary_term2 Ω h_bounded h_area x₀ hx₀ u hu_diff n h_cont_n)

lemma greens_dirichlet_representation
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (G : E → E → ℝ)
  (hG : IsGreensFunction G Ω)
  (u g : E → ℝ)
  (hu_cont : ContinuousOn u (closure Ω))
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hu_harm : IsHarmonic u Ω)
  (hu_bc : ∀ x ∈ frontier Ω, u x = g x)
  (n : E → E)
  (hn : IsOutwardUnitNormal Ω n)
  (h_cont_n : ContinuousOn n (frontier Ω)) :
  ∀ x₀ ∈ Ω, u x₀ = ∫ x in frontier Ω,
    g x * ⟪gradientWithin (fun y => G y x₀) (closure Ω) x, n x⟫_ℝ ∂surfaceArea := by
  intro x₀ hx₀
  rcases hG x₀ hx₀ with ⟨H, hH_cont, hH_diff, hH_harm, hG_eq, hG_bc⟩
  have hH_diff_ext : ContDiffOn ℝ 2 H (closure Ω) := sorry
  have h_G_val := greens_boundary_val_eq Ω x₀ G H hG_bc.1 hG_bc.2
  exact (show u x₀ = ∫ x in frontier Ω, (u x * ⟪n x, gradientWithin (fun y => G y x₀) (closure Ω) x⟫_ℝ - G x x₀ * ⟪n x, gradientWithin u (closure Ω) x⟫_ℝ) ∂surfaceArea by
    rw [combine_greens_representation_integrals Ω x₀ u H G n h_G_val
          (greens_boundary_grad_eq Ω x₀ hx₀ G H hG_eq h_G_val (hH_diff_ext.of_le (by decide)))
          (integrable_fundamental_sol_boundary Ω h_bounded h_area x₀ hx₀ u hu_cont hu_diff n h_cont_n)
          (integrable_harmonic_corrector_boundary Ω h_bounded h_area u H hu_cont (hu_diff.of_le (by decide)) hH_cont (hH_diff_ext.of_le (by decide)) n h_cont_n),
        greens_second_identity_harmonic Ω u H h_bounded h_area hu_cont hu_diff hu_harm hH_cont hH_diff_ext hH_harm n hn h_cont_n,
        add_zero]
    exact representation_formula Ω u n hn h_cont_n hu_diff hu_harm x₀ hx₀ h_bounded h_area fundamental_sol_3d (fun _ ↦ rfl)).trans <| MeasureTheory.integral_congr_ae <| by
      filter_upwards [MeasureTheory.ae_restrict_mem isClosed_frontier.measurableSet] with x hx
      rw [hG_bc.1 x hx, hu_bc x hx, zero_mul, sub_zero, real_inner_comm]


-----------------------------BEGIN THE GREEN_POISSON_REPRESENTATION--------------


lemma fundamental_sol_3d_eq_const_mul_inv_norm (x₀ : E) :
    (fun x => fundamental_sol_3d (x - x₀)) = fun x => (-1 / (4 * Real.pi)) * (‖x - x₀‖)⁻¹ := by
  ext
  unfold fundamental_sol_3d
  ring

lemma fundamental_sol_integrable
  (Ω : Set E)
  (h_bounded : Bornology.IsBounded Ω)
  (x₀ : E) :
  IntegrableOn (fun x => fundamental_sol_3d (x - x₀)) Ω := by
  obtain ⟨R, hR, h_sub⟩ := bounded_image_sub_subset_ball Ω h_bounded x₀
  rw [fundamental_sol_3d_eq_const_mul_inv_norm x₀]
  exact ((integrableOn_inv_norm_translate Ω x₀).mpr <|
    IntegrableOn.mono_set (integrable_inv_norm_closedBall R hR) h_sub).const_mul (-1 / (4 * Real.pi) : ℝ)

lemma integrable_singular_part
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (f : E → ℝ)
  (hf_cont : ContinuousOn f (closure Ω))
  (x₀ : E)
  (M : ℝ)
  (hM : ∀ x ∈ Ω, |f x| ≤ M) :
  IntegrableOn (fun x => fundamental_sol_3d (x - x₀) * f x) Ω := by
  refine MeasureTheory.Integrable.mono ((fundamental_sol_integrable Ω h_bounded x₀).mul_const M) ?_ ?_
  · exact (fundamental_sol_integrable Ω h_bounded x₀).aestronglyMeasurable.mul
      ((hf_cont.mono subset_closure).aestronglyMeasurable h_domain.is_open.measurableSet)
  · refine (ae_restrict_iff' h_domain.is_open.measurableSet).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    rw [norm_mul, norm_mul, Real.norm_eq_abs (f x), Real.norm_eq_abs M, abs_of_nonneg (le_trans (abs_nonneg (f x)) (hM x hx))]
    exact mul_le_mul_of_nonneg_left (hM x hx) (norm_nonneg _)

lemma ae_eq_greens_integrand
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (G : E → E → ℝ)
  (H f : E → ℝ)
  (x₀ : E)
  (step1_split_integrand : ∀ x ∈ Ω \ {x₀}, G x x₀ * f x = fundamental_sol_3d (x - x₀) * f x + H x * f x) :
  (fun x => fundamental_sol_3d (x - x₀) * f x + H x * f x) =ᵐ[volume.restrict Ω] (fun x => G x x₀ * f x) := by
  refine (ae_restrict_iff' h_domain.is_open.measurableSet).mpr ?_
  filter_upwards [ae_ne_singleton x₀] with x hx
  intro hx_omega
  exact (step1_split_integrand x ⟨hx_omega, hx⟩).symm

lemma greens_function_integrable
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (G : E → E → ℝ)
  (hG : IsGreensFunction G Ω)
  (f : E → ℝ)
  (hf_cont : ContinuousOn f (closure Ω))
  (x₀ : E)
  (hx₀ : x₀ ∈ Ω) :
  IntegrableOn (fun x => G x x₀ * f x) Ω := by
  obtain ⟨H, hH_cont, _, _, hG_eq, _, _⟩ := hG x₀ hx₀
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn h_bounded.isCompact_closure hf_cont
  exact Integrable.congr
    ((integrable_singular_part Ω h_bounded f hf_cont x₀ M fun x hx => hM x (subset_closure hx)).add
      ((hH_cont.mul hf_cont).integrableOn_compact h_bounded.isCompact_closure |>.mono_set subset_closure))
    (ae_eq_greens_integrand Ω G H f x₀ fun x hx => by rw [hG_eq x hx]; ring)

lemma fundamental_sol_3d_laplacian {y x₀ : E} (h : y ≠ x₀) :
    laplacian (fun z => fundamental_sol_3d (z - x₀)) y = 0 := by
  rw [fundamental_sol_3d_eq_const_mul_inv_norm x₀]
  simp_rw [inv_eq_one_div]
  rw [laplacian_const_mul (-1 / (4 * Real.pi) : ℝ) (fun z => 1 / ‖z - x₀‖) y (contDiffAt_inv_norm_sub x₀ y h),
    laplacian_inv_norm_shift x₀ y h,
    laplacian_inv_norm_eq_zero (sub_ne_zero.mpr h),
    mul_zero]

lemma contDiffAt_fundamental_sol_3d (x₀ x : E) (h : x ≠ x₀) :
    ContDiffAt ℝ 2 (fun y => fundamental_sol_3d (y - x₀)) x := by
  rw [fundamental_sol_3d_eq_const_mul_inv_norm x₀]
  simp_rw [inv_eq_one_div]
  exact contDiffAt_const.mul (contDiffAt_inv_norm_sub x₀ x h)

lemma greens_laplacian_punctured
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (x₀ : E) (hx₀ : x₀ ∈ Ω) (x : E) (hx : x ∈ Ω \ {x₀}) :
  laplacian (fun y => G y x₀) x = 0 := by
  obtain ⟨H, _, hH_diff_open, hH_harm, hG_eq_open, _, _⟩ := hG x₀ hx₀
  have hx_ne : x ≠ x₀ := fun h => hx.2 (Set.mem_singleton_iff.mpr h)
  rw [laplacian_congr (Filter.eventuallyEq_of_mem ((IsOpen.sdiff h_domain.is_open isClosed_singleton).mem_nhds hx) hG_eq_open)]
  rw [laplacian_add _ _ x (contDiffAt_fundamental_sol_3d x₀ x hx_ne)
    ((hH_diff_open.contDiffAt (h_domain.is_open.mem_nhds hx.1)).of_le le_top)]
  rw [fundamental_sol_3d_laplacian hx_ne, hH_harm x hx.1, add_zero]

lemma contDiffOn_fundamental_sol_3d_punctured (x₀ : E) (s : Set E) :
    ContDiffOn ℝ 2 (fun y => fundamental_sol_3d (y - x₀)) (s \ {x₀}) := by
  rw [fundamental_sol_3d_eq_const_mul_inv_norm x₀]
  refine contDiff_const.contDiffOn.mul (ContDiffOn.inv ?_ (fun y hy => norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy.2)))
  exact ContDiffOn.norm ℝ (contDiff_id.contDiffOn.sub contDiff_const.contDiffOn) (fun y hy => sub_ne_zero.mpr hy.2)

lemma contDiffOn_greens_func_punctured
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (G : E → E → ℝ)
  (hG : IsGreensFunction G Ω)
  (x₀ : E)
  (hx₀ : x₀ ∈ Ω) :
  ContDiffOn ℝ 2 (fun y => G y x₀) (closure Ω \ {x₀}) := by
  obtain ⟨H, _, _, _, hG_eq_open, hG_bc, hH_bc⟩ := hG x₀ hx₀
  have hH_diff_closure : ContDiffOn ℝ 2 H (closure Ω \ {x₀}) := by
    sorry
  refine ContDiffOn.congr ((contDiffOn_fundamental_sol_3d_punctured x₀ (closure Ω)).add hH_diff_closure) ?_
  exact greens_func_eq_on_closure_diff Ω x₀ G H hG_eq_open fun y hy => by rw [hG_bc y hy, hH_bc y hy]; ring

lemma laplacianWithin_greens_func_annulus
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (G : E → E → ℝ)
  (hG : IsGreensFunction G Ω)
  (x₀ : E)
  (hx₀ : x₀ ∈ Ω)
  (ε : ℝ)
  (hε : 0 < ε) :
  ∀ x ∈ Ω \ Metric.closedBall x₀ ε,
    laplacianWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x = 0 := by
  rintro x ⟨hx_omega, hx_ball⟩
  rw [laplacianWithin_closure_eq_laplacian (fun y => G y x₀) (Ω \ Metric.closedBall x₀ ε)
    (IsOpen.sdiff h_domain.is_open isClosed_closedBall) x ⟨hx_omega, hx_ball⟩]
  refine greens_laplacian_punctured Ω G hG x₀ hx₀ x ⟨hx_omega, fun h => ?_⟩
  rw [Set.mem_singleton_iff] at h
  exact hx_ball (h.symm ▸ Metric.mem_closedBall_self hε.le)

lemma greens_second_annulus_evaluated
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (G : E → E → ℝ)
  (hG : IsGreensFunction G Ω)
  (u f : E → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hu_poisson : ∀ x ∈ Ω, laplacian u x = f x)
  (x₀ : E)
  (hx₀ : x₀ ∈ Ω)
  (ε : ℝ)
  (hε : 0 < ε)
  (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (n : E → E)
  (hn : IsOutwardUnitNormal Ω n)
  (h_cont_n : ContinuousOn n (frontier Ω)) :
  ∫ x in Ω \ Metric.closedBall x₀ ε, G x x₀ * f x =
  (∫ x in frontier Ω,
    (G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ -
     u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) ∂surfaceArea) +
  ∫ x in Metric.sphere x₀ ε,
    (G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ -
     u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ) ∂surfaceArea := by
  have h_open : IsOpen (Ω \ Metric.closedBall x₀ ε) := IsOpen.sdiff h_domain.is_open isClosed_closedBall
  refine Eq.trans (MeasureTheory.setIntegral_congr_fun h_open.measurableSet fun x hx => ?_)
    (greens_second_identity_annulus_gen Ω n hn h_cont_n x₀ ε hε h_subset h_bounded h_area u (fun y => G y x₀)
      (hu_diff.mono (closure_mono Set.sdiff_subset))
      ((contDiffOn_greens_func_punctured Ω G hG x₀ hx₀).mono (closure_diff_ball_subset_closure_punctured Ω x₀ ε hε)))
  rw [laplacianWithin_greens_func_annulus Ω G hG x₀ hx₀ ε hε x hx,
    laplacianWithin_closure_eq_laplacian u (Ω \ Metric.closedBall x₀ ε) h_open x hx,
    hu_poisson x hx.1]
  ring

lemma fundamental_sol_3d_contDiffAt {x₀ x : E} (h : x ≠ x₀) :
    ContDiffAt ℝ 2 (fun y => fundamental_sol_3d (y - x₀)) x :=
  contDiffAt_fundamental_sol_3d x₀ x h

lemma fundamental_sol_3d_contDiffOn_punctured (x₀ : E) (ε : ℝ) (hε : 0 < ε) (Ω : Set E) :
    ContDiffOn ℝ 2 (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) :=
  contDiffOn_of_forall_contDiffAt fun _ hx =>
    fundamental_sol_3d_contDiffAt (x_ne_x₀_of_dist_ge_pos hε (dist_ge_of_mem_closure_punctured hx))

lemma greens_eq_sum_on_closure {G : E → E → ℝ} {H : E → ℝ} {Ω : Set E} {x₀ : E} {ε : ℝ} (hε : 0 < ε)
    (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
    (hG_bound : ∀ x ∈ frontier Ω, G x x₀ = 0)
    (hH_bound : ∀ x ∈ frontier Ω, H x = -fundamental_sol_3d (x - x₀)) :
    ∀ x ∈ closure (Ω \ Metric.closedBall x₀ ε), G x x₀ = fundamental_sol_3d (x - x₀) + H x :=
  fun x hx => (mem_punctured_or_frontier_of_mem_closure hε hx).elim (hG_eq x)
    (fun h => by rw [hG_bound x h, hH_bound x h, add_neg_cancel])

lemma contDiffOn_greens_sum_congr {G : E → E → ℝ} {H : E → ℝ} {Ω : Set E} {x₀ : E} {ε : ℝ} (hε : 0 < ε)
    (hF : ContDiffOn ℝ 2 (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)))
    (hH : ContDiffOn ℝ 2 H (closure (Ω \ Metric.closedBall x₀ ε)))
    (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
    (hG_bound : ∀ x ∈ frontier Ω, G x x₀ = 0)
    (hH_bound : ∀ x ∈ frontier Ω, H x = -fundamental_sol_3d (x - x₀)) :
    ContDiffOn ℝ 2 (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) :=
  ContDiffOn.congr (hF.add hH) (greens_eq_sum_on_closure hε hG_eq hG_bound hH_bound)

lemma laplacian_greens_function_zero_punctured {Ω : Set E} [HasPDEDomain Ω]
    {G : E → E → ℝ} (hG : IsGreensFunction G Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ x ∈ Ω \ Metric.closedBall x₀ ε, laplacian (fun y => G y x₀) x = 0 := by
  rintro x ⟨hx_omega, hx_ball⟩
  refine greens_laplacian_punctured Ω G hG x₀ hx₀ x ⟨hx_omega, fun h => ?_⟩
  rw [Set.mem_singleton_iff] at h
  subst h
  exact hx_ball (Metric.mem_closedBall_self hε.le)

lemma greens_integrand_simplification {Ω : Set E} [HasPDEDomain Ω]
    {G : E → E → ℝ} (hG : IsGreensFunction G Ω)
    {u f : E → ℝ} (hu_poisson : ∀ x ∈ Ω, laplacian u x = f x)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ x ∈ Ω \ Metric.closedBall x₀ ε,
      u x * laplacian (fun y => G y x₀) x - G x x₀ * laplacian u x = -(G x x₀ * f x) := by
  intro x hx
  rw [laplacian_greens_function_zero_punctured hG hx₀ hε x hx, hu_poisson x hx.1, mul_zero, zero_sub]

lemma greens_second_punctured
    (Ω : Set E) [HasPDEDomain Ω]
    (h_bounded : Bornology.IsBounded Ω)
    (h_area : surfaceArea (frontier Ω) ≠ ⊤)
    (G : E → E → ℝ)
    (hG : IsGreensFunction G Ω)
    (u f : E → ℝ)
    (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
    (hu_poisson : ∀ x ∈ Ω, laplacian u x = f x)
    (n : E → E)
    (hn : IsOutwardUnitNormal Ω n)
    (h_cont_n : ContinuousOn n (frontier Ω))
    (x₀ : E)
    (hx₀ : x₀ ∈ Ω)
    (ε : ℝ)
    (hε : 0 < ε)
    (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
    ∫ x in Ω \ Metric.closedBall x₀ ε, G x x₀ * f x =
    (∫ x in frontier Ω,
      (G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ -
      u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) ∂surfaceArea) +
    ∫ x in Metric.sphere x₀ ε,
      (G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ -
      u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ) ∂surfaceArea :=
  greens_second_annulus_evaluated Ω h_bounded h_area G hG u f hu_diff hu_poisson x₀ hx₀ ε hε h_subset n hn h_cont_n

lemma continuousOn_gradientWithin_fundamental_sol_frontier {Ω : Set E} [HasPDEDomain Ω] {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ContinuousOn (fun x => gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure Ω) x) (frontier Ω) :=
  ((gradient_fundamental_sol_3d_continuousOn x₀).mono (frontier_subset_compl_singleton hx₀)).congr fun x hx => by
    have h_open : IsOpen Ω := HasPDEDomain.is_open
    have h_x_notin_Ω : x ∉ Ω := fun h_in => hx.2 (h_open.interior_eq.symm ▸ h_in)
    have h_x_neq_x₀ : x - x₀ ≠ 0 := by
      intro h_eq
      exact h_x_notin_Ω (sub_eq_zero.mp h_eq ▸ hx₀)
    have h_diff : DifferentiableAt ℝ (fun y ↦ fundamental_sol_3d (y - x₀)) x := by
      exact diff_Phi_at x₀ x h_x_neq_x₀ fundamental_sol_3d (congrFun rfl)
    have h_unique : UniqueDiffWithinAt ℝ (closure Ω) x :=
      HasPDEDomain.unique_diff x hx.1
    exact
      gradientWithin_eq_gradient_of_differentiableAt (fun y ↦ fundamental_sol_3d (y - x₀))
        (closure Ω) x h_diff h_unique

lemma continuousOn_gradientWithin_G_frontier {Ω : Set E} [HasPDEDomain Ω]
  {G : E → E → ℝ} {H : E → ℝ} {x₀ : E} (hx₀ : x₀ ∈ Ω)
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω))
  (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hG_val_eq : ∀ x ∈ frontier Ω, G x x₀ = fundamental_sol_3d (x - x₀) + H x) :
  ContinuousOn (fun x => gradientWithin (fun y => G y x₀) (closure Ω) x) (frontier Ω) :=
  ContinuousOn.congr ((continuousOn_gradientWithin_fundamental_sol_frontier hx₀).add
    ((continuousOn_gradientWithin_of_contDiffOn HasPDEDomain.unique_diff H hH_diff).mono frontier_subset_closure))
    (greens_boundary_grad_eq Ω x₀ hx₀ G H hG_eq hG_val_eq hH_diff)

-- need to refactor
lemma integrable_u_mul_grad_G_frontier {Ω : Set E} [HasPDEDomain Ω]
  (H : E → ℝ)
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  {G : E → E → ℝ} {u : E → ℝ} {n : E → E} {x₀ : E} {ε : ℝ}
  (hx₀ : x₀ ∈ Ω)
  (hu_cont : ContinuousOn u (closure Ω))
  (hn_cont : ContinuousOn n (frontier Ω))
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω))
  (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hG_val_eq : ∀ x ∈ frontier Ω, G x x₀ = fundamental_sol_3d (x - x₀) + H x) :
  IntegrableOn (fun x => u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) (frontier Ω) surfaceArea := by
  have h_cont : ContinuousOn (fun x => u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) (frontier Ω) :=
    (hu_cont.mono frontier_subset_closure).mul
      (((continuousOn_gradientWithin_G_frontier hx₀ hH_diff hG_eq hG_val_eq).congr
        (eqOn_gradientWithin_excised_frontier h_subset)).inner hn_cont)
  exact integrableOn_compact_surface_of_continuousOn
    (isCompact_iff_isClosed_bounded.mpr ⟨isClosed_frontier, h_bounded.closure.subset frontier_subset_closure⟩)
    h_area _ h_cont

lemma GreensFunction_zero_on_frontier {Ω : Set E} {G : E → E → ℝ} {x₀ : E}
  (hG : IsGreensFunction G Ω) (hx₀ : x₀ ∈ Ω) {x : E} (hx : x ∈ frontier Ω) :
  G x x₀ = 0 := by
  obtain ⟨_, _, _, _, _, h_zero_front, _⟩ := hG x₀ hx₀
  exact h_zero_front x hx

lemma boundary_integrable_frontier {Ω : Set E} [HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  {G : E → E → ℝ} {u : E → ℝ} {n : E → E} {x₀ : E} {ε : ℝ}
  (hG : IsGreensFunction G Ω)
  (hx₀ : x₀ ∈ Ω)
  (hu_cont : ContinuousOn u (closure Ω))
  (hn_cont : ContinuousOn n (frontier Ω))
  (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (H : E → ℝ)
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω))
  (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hG_val_eq : ∀ x ∈ frontier Ω, G x x₀ = fundamental_sol_3d (x - x₀) + H x) :
  IntegrableOn (fun x => u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ -
    G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) (frontier Ω) surfaceArea := by
  have h_zero_int : IntegrableOn (fun _ : E => (0 : ℝ)) (frontier Ω) surfaceArea := integrable_zero _ _ _
  have h_int_right : IntegrableOn (fun x => G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) (frontier Ω) surfaceArea := by
    refine MeasureTheory.IntegrableOn.congr_fun h_zero_int (fun x hx => ?_) isClosed_frontier.measurableSet
    simp [GreensFunction_zero_on_frontier hG hx₀ hx]
  exact (integrable_u_mul_grad_G_frontier H h_bounded h_area hx₀ hu_cont hn_cont hH_diff h_subset hG_eq hG_val_eq).sub h_int_right

-- need to refactor


lemma greens_integrand_eq_on_frontier {Ω : Set E} [HasPDEDomain Ω]
    {G : E → E → ℝ} {u g : E → ℝ} {n : E → E} {x₀ : E} {ε : ℝ}
    (hG : IsGreensFunction G Ω) (hx₀ : x₀ ∈ Ω)
    (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
    (hu_bc : ∀ x ∈ frontier Ω, u x = g x) :
    ∀ x ∈ frontier Ω,
      u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ -
      G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ =
      g x * ⟪gradientWithin (fun y => G y x₀) (closure Ω) x, n x⟫_ℝ := by
  intro x hx
  have h_u_eq_g : u x = g x := by
    exact hu_bc x hx
  have h_G_zero : G x x₀ = 0 := by
    obtain ⟨_, _, _, _, _, h_zero_front, _⟩ := hG x₀ hx₀
    exact h_zero_front x hx
  have h_open_Ω : IsOpen Ω := HasPDEDomain.is_open
  have h_x_notin_Ω : x ∉ Ω := fun h_in => hx.2 (h_open_Ω.interior_eq.symm ▸ h_in)
  have h_x_notin_ball : x ∉ Metric.closedBall x₀ ε := fun h_in => h_x_notin_Ω (h_subset h_in)
  have h_compl_open : IsOpen (Metric.closedBall x₀ ε)ᶜ := isClosed_closedBall.isOpen_compl
  have h_x_in_compl : x ∈ (Metric.closedBall x₀ ε)ᶜ := h_x_notin_ball
  have h_nhds_eq : 𝓝[closure (Ω \ Metric.closedBall x₀ ε)] x = 𝓝[closure Ω] x := by
    refine nhdsWithin_eq_iff_eventuallyEq.mpr ?_
    exact eventuallyEq_closure_diff_closedBall Ω x₀ x ε h_x_notin_ball
  have h_grad_G_eq : ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ = ⟪gradientWithin (fun y => G y x₀) (closure Ω) x, n x⟫_ℝ := by
    have h_grad_eq : gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x = gradientWithin (fun y => G y x₀) (closure Ω) x := by
      exact gradientWithin_frontier_excised_eq Ω (fun y ↦ G y x₀) x₀ x ε h_x_notin_ball
    rw [h_grad_eq]
  rw [h_u_eq_g, h_G_zero, zero_mul, sub_zero, h_grad_G_eq]

lemma continuousOn_G_sphere {Ω : Set E} [HasPDEDomain Ω]
  {G : E → E → ℝ} {x₀ : E} {ε : ℝ}
  (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (H : E → ℝ)
  (hH_cont : ContinuousOn H (closure Ω))
  (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x) :
  ContinuousOn (fun x => G x x₀) (Metric.sphere x₀ ε) := by
  have h_sphere_subset : Metric.sphere x₀ ε ⊆ Ω \ {x₀} := by
    intro x hx
    have h_in_ball : x ∈ Metric.closedBall x₀ ε := Metric.sphere_subset_closedBall hx
    have h_in_Ω : x ∈ Ω := h_subset h_in_ball
    have h_neq : x ≠ x₀ := by
      intro h_eq
      have h_dist : dist x x₀ = ε := hx
      rw [h_eq, dist_self] at h_dist
      exact (ne_of_lt hε) h_dist
    exact ⟨h_in_Ω, h_neq⟩
  have h_G_eq_on_sphere : EqOn (fun x => G x x₀) (fun x => fundamental_sol_3d (x - x₀) + H x) (Metric.sphere x₀ ε) := by
    intro x hx
    exact hG_eq x (h_sphere_subset hx)
  have h_fund_cont : ContinuousOn (fun x => fundamental_sol_3d (x - x₀)) (Metric.sphere x₀ ε) := by
    have h_cont_sub : Continuous (fun x => x - x₀) := continuous_id.sub continuous_const
    have h_fund_cont_away : ContinuousOn fundamental_sol_3d {0}ᶜ := by
        have h_norm_cont : ContinuousOn (fun x : E => ‖x‖) {0}ᶜ := continuous_norm.continuousOn
        have h_ne_zero : ∀ x ∈ ({0}ᶜ : Set E), ‖x‖ ≠ 0 := fun x hx => norm_ne_zero_iff.mpr hx
        have h_inv_norm_cont : ContinuousOn (fun x : E => ‖x‖⁻¹) {0}ᶜ := h_norm_cont.inv₀ h_ne_zero
        unfold fundamental_sol_3d
        exact continuousOn_const.div (continuousOn_const.mul h_norm_cont) (by
      intro x hx
      have h1 : (4 : ℝ) * π ≠ 0 := by positivity
      exact mul_ne_zero h1 (h_ne_zero x hx))
    have h_maps_to : MapsTo (fun x => x - x₀) (Metric.sphere x₀ ε) {0}ᶜ := by
      intro x hx
      have h_dist : dist x x₀ = ε := hx
      rw [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero]
      intro h_eq
      rw [h_eq, dist_self] at h_dist
      exact (ne_of_lt hε) h_dist
    exact h_fund_cont_away.comp h_cont_sub.continuousOn h_maps_to
  have h_H_cont : ContinuousOn H (Metric.sphere x₀ ε) := by
    have h_sphere_subset_closure : Metric.sphere x₀ ε ⊆ closure Ω :=
      Metric.sphere_subset_closedBall.trans (h_subset.trans subset_closure)
    exact ContinuousOn.mono hH_cont h_sphere_subset_closure
  exact (h_fund_cont.add h_H_cont).congr h_G_eq_on_sphere

lemma continuousOn_gradient_fundamental_sol_3d_shifted_away (x₀ : E) :
  ContinuousOn (fun x => gradient (fun y => fundamental_sol_3d (y - x₀)) x) ({x₀} : Set E)ᶜ :=
  continuousOn_gradient_of_contDiffOn isOpen_compl_singleton
    (fun y => fundamental_sol_3d (y - x₀)) (fundamental_sol_3d_contDiffOn_compl x₀)

lemma continuousOn_gradientWithin_fundamental_sol_3d_sphere {Ω : Set E} [HasPDEDomain Ω]
  {x₀ : E} {ε : ℝ} (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  ContinuousOn (fun x => gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x) (Metric.sphere x₀ ε) := by
  have h_not_center : ∀ x ∈ Metric.sphere x₀ ε, x ∈ ({x₀} : Set E)ᶜ :=
    fun x hx (h_eq : x = x₀) => ne_of_gt hε (by
      rw [Metric.mem_sphere] at hx
      rw [h_eq, dist_self] at hx
      exact hx.symm)
  exact ((continuousOn_gradient_fundamental_sol_3d_shifted_away x₀).mono h_not_center).congr
    (fun x hx => gradientWithin_eq_gradient_of_differentiableAt (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x
      ((fundamental_sol_3d_contDiffOn_compl x₀).differentiableOn_one.differentiableAt (isOpen_compl_singleton.mem_nhds (h_not_center x hx)))
      ((annulus_has_pde_domain Ω x₀ ε hε h_subset).unique_diff x (mem_closure_annulus_of_mem_sphere hε h_subset hx)))

lemma eqOn_gradientWithin_G_sphere {Ω : Set E} [HasPDEDomain Ω]
  {G : E → E → ℝ} {x₀ : E} {ε : ℝ}
  (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (H : E → ℝ) (hH_C1 : ContDiffOn ℝ 1 H Ω)
  (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x) :
  EqOn (fun x => gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x)
       (fun x => gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x +
                 gradientWithin H (closure (Ω \ Metric.closedBall x₀ ε)) x)
       (Metric.sphere x₀ ε) := by
  intro x hx
  have h_in_U : x ∈ Ω \ {x₀} :=
    ⟨h_subset (Metric.sphere_subset_closedBall hx), by
      rintro rfl
      rw [Metric.mem_sphere, dist_self] at hx
      exact ne_of_gt hε hx.symm⟩
  have h_diff_g : DifferentiableAt ℝ (fun y => fundamental_sol_3d (y - x₀)) x :=
    (fundamental_sol_3d_contDiffOn_compl x₀).differentiableOn_one.differentiableAt
      (isOpen_compl_singleton.mem_nhds h_in_U.2)
  have h_diff_h : DifferentiableAt ℝ H x :=
    hH_C1.differentiableOn_one.differentiableAt (HasPDEDomain.is_open.mem_nhds h_in_U.1)
  have h_eq_nhds : (fun y => G y x₀) =ᶠ[𝓝 x] (fun y => fundamental_sol_3d (y - x₀) + H y) :=
    Filter.mem_of_superset ((HasPDEDomain.is_open.sdiff isClosed_singleton).mem_nhds h_in_U) hG_eq
  have h_unique_diff : UniqueDiffWithinAt ℝ (closure (Ω \ Metric.closedBall x₀ ε)) x :=
    (annulus_has_pde_domain Ω x₀ ε hε h_subset).unique_diff x (mem_closure_annulus_of_mem_sphere hε h_subset hx)
  simp_rw [gradientWithin_eq_gradient_of_differentiableAt _ _ x (h_eq_nhds.differentiableAt_iff.mpr (h_diff_g.add h_diff_h)) h_unique_diff,
           gradientWithin_eq_gradient_of_differentiableAt _ _ x h_diff_g h_unique_diff,
           gradientWithin_eq_gradient_of_differentiableAt _ _ x h_diff_h h_unique_diff]
  unfold gradient
  rw [h_eq_nhds.fderiv_eq]
  erw [fderiv_add h_diff_g h_diff_h]
  rw [map_add]

lemma continuousOn_gradientWithin_G_sphere {Ω : Set E} [HasPDEDomain Ω]
  {G : E → E → ℝ} {x₀ : E} {ε : ℝ}
  (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (H : E → ℝ)
  (hH_C1 : ContDiffOn ℝ 1 H Ω)
  (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x) :
  ContinuousOn (fun x => gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x) (Metric.sphere x₀ ε) := by
  exact ((continuousOn_gradientWithin_fundamental_sol_3d_sphere hε h_subset).add
    (continuousOn_gradientWithin_H_sphere hε h_subset H hH_C1)).congr
    (eqOn_gradientWithin_G_sphere hε h_subset H hH_C1 hG_eq)

lemma setIntegral_union_frontier_sphere {Ω : Set E} [HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  {G : E → E → ℝ} {u : E → ℝ} {n : E → E} {x₀ : E} {ε : ℝ}
  (hG : IsGreensFunction G Ω)
  (hx₀ : x₀ ∈ Ω)
  (hu_cont : ContinuousOn u (closure Ω))
  (hu_C1 : ContDiffOn ℝ 1 u Ω)
  (hn_cont : ContinuousOn n (frontier Ω))
  (hn_cont_sphere : ContinuousOn n (Metric.sphere x₀ ε))
  (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (H : E → ℝ)
  (hH_cont : ContinuousOn H (closure Ω))
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω))
  (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hG_val_eq : ∀ x ∈ frontier Ω, G x x₀ = fundamental_sol_3d (x - x₀) + H x) :
  ∫ x in frontier Ω ∪ Metric.sphere x₀ ε,
      (u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ -
       G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) ∂surfaceArea =
  (∫ x in frontier Ω,
    (u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ -
     G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) ∂surfaceArea) +
  (∫ x in Metric.sphere x₀ ε,
    (u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ -
     G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) ∂surfaceArea) := by
  have h_frontier_disjoint : Disjoint (frontier Ω) (Metric.sphere x₀ ε) := disjoint_frontier_sphere h_subset
  have h_meas_sphere : MeasurableSet (Metric.sphere x₀ ε) := isClosed_sphere.measurableSet
  have h_int_frontier : IntegrableOn (fun x => u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ - G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) (frontier Ω) surfaceArea := by
    exact boundary_integrable_frontier h_bounded h_area hG hx₀ hu_cont hn_cont h_subset H hH_diff hG_eq hG_val_eq
  have h_int_sphere : IntegrableOn (fun x => u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ - G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) (Metric.sphere x₀ ε) surfaceArea := by
    have h_grad_u_cont : ContinuousOn (fun x => gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x) (Metric.sphere x₀ ε) :=
      continuousOn_gradientWithin_u_sphere hu_C1 hε h_subset
    have hG_cont : ContinuousOn (fun x => G x x₀) (Metric.sphere x₀ ε) := by
      exact continuousOn_G_sphere hε h_subset H hH_cont hG_eq
    have h_grad_G_cont : ContinuousOn (fun x => gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x) (Metric.sphere x₀ ε) := by
      exact continuousOn_gradientWithin_G_sphere hε h_subset H (hH_diff.mono subset_closure) hG_eq
    exact boundary_integrable_sphere hε h_subset hu_cont hn_cont_sphere h_grad_u_cont hG_cont h_grad_G_cont
  exact MeasureTheory.setIntegral_union h_frontier_disjoint h_meas_sphere h_int_frontier h_int_sphere

lemma boundary_integral_split {Ω : Set E} [HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  {G : E → E → ℝ} {u g : E → ℝ} {n : E → E} {x₀ : E}
  (hG : IsGreensFunction G Ω)
  (hx₀ : x₀ ∈ Ω)
  (hu_cont : ContinuousOn u (closure Ω))
  (hu_C1 : ContDiffOn ℝ 1 u Ω)
  (hn_cont : ContinuousOn n (closure Ω))
  (hu_bc : ∀ x ∈ frontier Ω, u x = g x)
  (H : E → ℝ)
  (hH_cont : ContinuousOn H (closure Ω))
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω))
  (hG_eq : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hG_val_eq : ∀ x ∈ frontier Ω, G x x₀ = fundamental_sol_3d (x - x₀) + H x) :
  ∀ ε > 0, Metric.closedBall x₀ ε ⊆ Ω →
    ∫ x in frontier (Ω \ Metric.closedBall x₀ ε),
      (u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ -
       G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) ∂surfaceArea =
    (∫ x in frontier Ω, g x * ⟪gradientWithin (fun y => G y x₀) (closure Ω) x, n x⟫_ℝ ∂surfaceArea) +
    (∫ x in Metric.sphere x₀ ε,
      (u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ -
       G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) ∂surfaceArea) := by
  intro ε hε h_subset
  have hn_cont_frontier := hn_cont.mono frontier_subset_closure
  have hn_cont_sphere := hn_cont.mono (Metric.sphere_subset_closedBall.trans (h_subset.trans subset_closure))
  rw [frontier_diff_closedBall_gen Ω x₀ ε hε h_subset,
    setIntegral_union_frontier_sphere h_bounded h_area hG hx₀ hu_cont hu_C1 hn_cont_frontier hn_cont_sphere hε h_subset H hH_cont hH_diff hG_eq hG_val_eq,
    MeasureTheory.setIntegral_congr_fun isClosed_frontier.measurableSet (greens_integrand_eq_on_frontier (n := n) hG hx₀ h_subset hu_bc (ε := ε))]


lemma norm_fundamental_sol_3d_on_sphere {x x₀ : E} {ε ε₀ : ℝ}
  (hε : ε ∈ Set.Ioc 0 ε₀) (hx : x ∈ Metric.sphere x₀ ε) :
  ‖fundamental_sol_3d (x - x₀)‖ = 1 / (4 * Real.pi * ε) := by
  unfold fundamental_sol_3d
  simp_all
  subst hx
  simp_all only [norm_pos_iff, ne_eq, abs_norm, mul_eq_mul_left_iff, mul_eq_mul_right_iff, inv_inj, abs_eq_self,
    inv_eq_zero, OfNat.ofNat_ne_zero, or_false, norm_eq_zero]
  obtain ⟨left, right⟩ := hε
  positivity

lemma greens_function_sphere_bound (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (H : E → ℝ) (hH_cont : ContinuousOn H (closure Ω))
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x) :
  ∃ (C : ℝ) (ε₀ : ℝ), 0 < ε₀ ∧ ∀ ε ∈ Set.Ioc 0 ε₀,
    ∀ x ∈ Metric.sphere x₀ ε, ‖G x x₀‖ ≤ C / ε := by
  obtain ⟨ε₀, hε₀_pos, h_ball_subset⟩ := exists_pos_closedBall_subset_of_isOpen HasPDEDomain.is_open hx₀
  obtain ⟨M_H, hM_H_nonneg, hH_le⟩ := exists_norm_bound_closedBall H hH_cont x₀ ε₀ hε₀_pos h_ball_subset
  exact ⟨(1 / (4 * Real.pi)) + (M_H * ε₀), ε₀, hε₀_pos, fun ε hε x hx => by
    have h_x_in_diff : x ∈ Ω \ {x₀} :=
      ⟨h_ball_subset (Metric.closedBall_subset_closedBall hε.2 (Metric.sphere_subset_closedBall hx)),
       dist_pos.mp ((Metric.mem_sphere.mp hx).symm ▸ hε.1)⟩
    calc ‖G x x₀‖
      _ = ‖fundamental_sol_3d (x - x₀) + H x‖ := by rw [hG_eq_fund x h_x_in_diff]
      _ ≤ ‖fundamental_sol_3d (x - x₀)‖ + ‖H x‖ := norm_add_le _ _
      _ = 1 / (4 * Real.pi * ε) + ‖H x‖ := by rw [norm_fundamental_sol_3d_on_sphere hε hx]
      _ ≤ 1 / (4 * Real.pi * ε) + M_H := by
          gcongr
          exact hH_le x (Metric.closedBall_subset_closedBall hε.2 (Metric.sphere_subset_closedBall hx))
      _ ≤ (1 / (4 * Real.pi) + M_H * ε₀) / ε := greens_bound_algebra hε.1 hε.2 hM_H_nonneg⟩

lemma continuousOn_fundamental_sol_3d_sphere (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε) :
  ContinuousOn (fun x => fundamental_sol_3d (x - x₀)) (Metric.sphere x₀ ε) := by
  unfold fundamental_sol_3d
  exact continuousOn_const.div
    (continuous_const.mul (continuous_id.sub continuous_const).norm).continuousOn
    (fun x hx => by
      rw [← dist_eq_norm, Metric.mem_sphere.mp hx]
      positivity)

lemma continuousOn_greens_sphere {Ω : Set E}
  {G : E → E → ℝ} {H : E → ℝ} (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε)
  (hH_cont : ContinuousOn H (closure Ω))
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (h_sphere_sub_omega : Metric.sphere x₀ ε ⊆ Ω) :
  ContinuousOn (fun x => G x x₀) (Metric.sphere x₀ ε) := by
  exact ContinuousOn.congr
    ((continuousOn_fundamental_sol_3d_sphere x₀ ε hε_pos).add
      (hH_cont.mono (h_sphere_sub_omega.trans subset_closure)))
    (fun x hx => (hG_eq_fund x (sphere_subset_diff_singleton hε_pos h_sphere_sub_omega hx)))

lemma continuousOn_greens_integrand_sphere (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (u : E → ℝ) (n : E → E) (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε)
  (H : E → ℝ) (hH_cont : ContinuousOn H (closure Ω))
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hn_cont : ContinuousOn n (closure Ω))
  (h_ball_sub_omega : Metric.closedBall x₀ ε ⊆ Ω) :
  ContinuousOn (fun x => G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) (Metric.sphere x₀ ε) :=
  (continuousOn_greens_sphere x₀ ε hε_pos hH_cont hG_eq_fund
      (Metric.sphere_subset_closedBall.trans h_ball_sub_omega)).mul
    ((continuousOn_gradientWithin_excised_sphere Ω u hu_diff x₀ ε hε_pos h_ball_sub_omega).inner
      (hn_cont.mono ((Metric.sphere_subset_closedBall.trans h_ball_sub_omega).trans subset_closure)))

lemma integrand_integrable_on_sphere (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (u : E → ℝ) (n : E → E) (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε)
  (H : E → ℝ) (hH_cont : ContinuousOn H (closure Ω))
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hn_cont : ContinuousOn n (closure Ω))
  (h_ball_sub_omega : Metric.closedBall x₀ ε ⊆ Ω)
  (C M : ℝ)
  (h_integrand_bound : ∀ x ∈ Metric.sphere x₀ ε, ‖G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ‖ ≤ (C * M) / ε)
  (h_area_enn : surfaceArea (Metric.sphere x₀ ε) = ENNReal.ofReal (4 * Real.pi * ε ^ 2)) :
  IntegrableOn (fun x => G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) (Metric.sphere x₀ ε) surfaceArea := by
  exact MeasureTheory.IntegrableOn.of_bound
    (by rw [h_area_enn]; exact ENNReal.ofReal_lt_top)
    ((continuousOn_greens_integrand_sphere Ω G u n x₀ ε hε_pos H hH_cont hG_eq_fund hu_diff hn_cont h_ball_sub_omega).aestronglyMeasurable isClosed_sphere.measurableSet)
    ((C * M) / ε)
    ((ae_restrict_iff' isClosed_sphere.measurableSet).mpr (Eventually.of_forall h_integrand_bound))


lemma limit_sphere_G_grad_u
  (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (n : E → E) (hn_cont : ContinuousOn n (closure Ω))
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (hn_eq : ∀ ε > 0, ∀ x ∈ Metric.sphere x₀ ε, -(1 / ε) • (x - x₀) = n x) :
  Filter.Tendsto
    (fun ε => ∫ x in Metric.sphere x₀ ε,
      G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea)
    (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨H, hH_cont, _, _, hG_eq_fund, _, _⟩ := hG x₀ hx₀
  obtain ⟨R, hR_pos, hR_sub⟩ := exists_pos_closedBall_subset_of_isOpen ‹HasPDEDomain Ω›.is_open hx₀
  obtain ⟨K, ε₀, hε₀_pos, h_bound_legacy⟩ := integral_squeeze_bound Ω G u n x₀
    (gradient_inner_normal_bound Ω u hu_diff n hn_cont x₀ hx₀)
    (greens_function_sphere_bound Ω G x₀ hx₀ H hH_cont hG_eq_fund)
    ⟨R, hR_pos, fun ε (hε : ε ∈ Set.Ioc 0 R) => (Metric.closedBall_subset_closedBall hε.2).trans hR_sub⟩
    (sphere_surface_area x₀)
  have h_tendsto : Filter.Tendsto (fun ε => K * ε) (𝓝[>] 0) (𝓝 0) := by
    have h_eval : Filter.Tendsto (fun ε => K * ε) (𝓝 0) (𝓝 (K * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using h_eval)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.eventually_of_mem (Ioc_mem_nhdsGT hε₀_pos) fun ε hε => by
      have h_integral_eq : ∫ x in Metric.sphere x₀ ε, G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea =
                           ∫ x in Metric.sphere x₀ ε, G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ ∂surfaceArea :=
        setIntegral_congr_fun (isCompact_sphere x₀ ε).measurableSet (fun x hx => by rw [hn_eq ε hε.1 x hx])
      rw [h_integral_eq]
      exact h_bound_legacy ε hε)
    h_tendsto)

lemma greens_eq_fund_add_H_on_closure (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (H : E → ℝ) (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε)
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hG_front : ∀ x ∈ frontier Ω, G x x₀ = 0)
  (hH_front : ∀ x ∈ frontier Ω, H x = -fundamental_sol_3d (x - x₀)) :
  Set.EqOn (fun y => G y x₀) (fun y => fundamental_sol_3d (y - x₀) + H y) (closure (Ω \ Metric.closedBall x₀ ε)) := by
  intro y hy
  rcases mem_diff_singleton_or_frontier_of_mem_closure_excised hε_pos hy with hy_omega | hy_front
  · exact hG_eq_fund y hy_omega
  · simp_rw [hG_front y hy_front, hH_front y hy_front]
    ring

lemma gradientWithin_fund_add_H_on_sphere {Ω : Set E} [HasPDEDomain Ω]
  (H : E → ℝ) (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε) (h_ball_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω)) (x : E) (hx : x ∈ Metric.sphere x₀ ε) :
  gradientWithin (fun y => fundamental_sol_3d (y - x₀) + H y) (closure (Ω \ Metric.closedBall x₀ ε)) x =
  gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x +
  gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x := by
  have h_in_closure := sphere_subset_closure_diff_ball x₀ ε hε_pos h_ball_subset hx
  unfold gradientWithin
  have h_add : (fun y ↦ fundamental_sol_3d (y - x₀) + H y) = (fun y ↦ fundamental_sol_3d (y - x₀)) + fun y ↦ H y := rfl
  rw [h_add, fderivWithin_add
    ((annulus_has_pde_domain Ω x₀ ε hε_pos h_ball_subset).unique_diff x h_in_closure)
    ((diff_Phi_at x₀ x (sub_ne_zero.mpr (dist_pos.mp ((Metric.mem_sphere.mp hx).symm ▸ hε_pos))) fundamental_sol_3d (congrFun rfl)).differentiableWithinAt)
    ((hH_diff.differentiableOn (by exact Ne.symm (zero_ne_one' (WithTop ℕ∞))) x (closure_mono sdiff_subset h_in_closure)).mono (closure_mono sdiff_subset))]
  exact map_add (InnerProductSpace.toDual ℝ E).symm _ _

lemma greens_integrand_split_pointwise (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (H : E → ℝ) (u : E → ℝ) (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε)
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hG_front : ∀ x ∈ frontier Ω, G x x₀ = 0)
  (hH_front : ∀ x ∈ frontier Ω, H x = -fundamental_sol_3d (x - x₀))
  (x : E) (hx : x ∈ Metric.sphere x₀ ε)
  (h_ball_subset_hyp : Metric.closedBall x₀ ε ⊆ Ω)
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω)) :
  u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ =
  u x * ⟪gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ +
  u x * ⟪gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ := by
  have h_grad_split : gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x =
    gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x +
    gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x := by
    calc
      gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x
        = gradientWithin (fun y => fundamental_sol_3d (y - x₀) + H y) (closure (Ω \ Metric.closedBall x₀ ε)) x := by
          unfold gradientWithin
          have h_eq := greens_eq_fund_add_H_on_closure Ω G H x₀ ε hε_pos hG_eq_fund hG_front hH_front
          rw [fderivWithin_congr h_eq (h_eq (sphere_subset_closure_diff_ball x₀ ε hε_pos h_ball_subset_hyp hx))]
      _ = gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x +
          gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x :=
          gradientWithin_fund_add_H_on_sphere H x₀ ε hε_pos h_ball_subset_hyp hH_diff x hx
  rw [h_grad_split, inner_add_left, mul_add]

lemma contDiffOn_fundamental_sol_excised (Ω : Set E) (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε) :
  ContDiffOn ℝ 1 (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) := by
  have h_subset : closure (Ω \ Metric.closedBall x₀ ε) ⊆ {z | ε ≤ ‖z - x₀‖} :=
    closure_minimal (fun z hz => (le_of_lt (not_le.mp hz.2)).trans (le_of_eq (dist_eq_norm z x₀)))
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  have h_neq : ∀ y ∈ closure (Ω \ Metric.closedBall x₀ ε), y - x₀ ≠ 0 :=
    fun y hy => norm_pos_iff.mp (lt_of_lt_of_le hε_pos (h_subset hy))
  unfold fundamental_sol_3d
  exact ContDiffOn.div contDiffOn_const
    (ContDiffOn.mul contDiffOn_const (ContDiffOn.norm ℝ (ContDiff.contDiffOn (ContDiff.sub contDiff_id contDiff_const)) h_neq))
    (fun y hy => ne_of_gt (mul_pos (by positivity) (lt_of_lt_of_le hε_pos (h_subset hy))))

lemma continuousOn_gradientWithin_fundamental_sol_excised (Ω : Set E) [HasPDEDomain Ω]
  (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε) (h_ball_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  ContinuousOn (fun x => gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x) (closure (Ω \ Metric.closedBall x₀ ε)) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
    ((contDiffOn_fundamental_sol_excised Ω x₀ ε hε_pos).continuousOn_fderivWithin
      (annulus_has_pde_domain Ω x₀ ε hε_pos h_ball_subset).unique_diff le_rfl)

lemma integrableOn_fundamental_sol_sphere (Ω : Set E) [HasPDEDomain Ω] (u : E → ℝ) (x₀ : E) (ε ε₀ : ℝ)
  (hε : ε ∈ Set.Ioc 0 ε₀) (h_ball_subset_hyp : Metric.closedBall x₀ ε₀ ⊆ Ω)
  (hu_cont : ContinuousOn u (closure Ω)) :
  MeasureTheory.IntegrableOn (fun x => u x * ⟪gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ) (Metric.sphere x₀ ε) surfaceArea := by
  have h_smul : Continuous (fun x : E ↦ -(1 / ε) • (x - x₀)) := by
    change Continuous ((fun _ : E ↦ -(1 / ε)) • (id - fun _ : E ↦ x₀))
    exact Continuous.smul continuous_const (Continuous.sub continuous_id continuous_const)
  have h_cont : ContinuousOn (fun x => u x * ⟪gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ) (Metric.sphere x₀ ε) :=
    (hu_cont.mono (((Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_closedBall hε.2)).trans h_ball_subset_hyp).trans subset_closure)).mul
      (((continuousOn_gradientWithin_fundamental_sol_excised Ω x₀ ε hε.1 ((Metric.closedBall_subset_closedBall hε.2).trans h_ball_subset_hyp)).mono
        (sphere_subset_closure_annulus Ω x₀ ε ε₀ hε h_ball_subset_hyp)).inner
        h_smul.continuousOn)
  exact integrableOn_compact_surface_of_continuousOn
    (isCompact_sphere x₀ ε)
    (ne_of_lt (surfaceArea_sphere_lt_top x₀ hε.1))
    _ h_cont

lemma eventually_split_sphere_integral (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (H : E → ℝ) (u : E → ℝ) (x₀ : E)
  (ε₀ : ℝ) (hε₀_pos : 0 < ε₀)
  (h_ball_subset_hyp : Metric.closedBall x₀ ε₀ ⊆ Ω)
  (hu_cont : ContinuousOn u (closure Ω))
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω))
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (hG_front : ∀ x ∈ frontier Ω, G x x₀ = 0)
  (hH_front : ∀ x ∈ frontier Ω, H x = -fundamental_sol_3d (x - x₀)) :
  ∀ᶠ ε in 𝓝[>] 0,
    ∫ x in Metric.sphere x₀ ε, u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea =
    (∫ x in Metric.sphere x₀ ε, u x * ⟪gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea) +
    (∫ x in Metric.sphere x₀ ε, u x * ⟪gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea) := by
  exact Filter.eventually_of_mem (Ioc_mem_nhdsGT hε₀_pos) fun ε hε =>
    (MeasureTheory.setIntegral_congr_fun isClosed_sphere.measurableSet (fun x hx =>
      greens_integrand_split_pointwise Ω G H u x₀ ε hε.1 hG_eq_fund hG_front hH_front x hx
        ((Metric.closedBall_subset_closedBall hε.2).trans h_ball_subset_hyp) hH_diff)).trans
      (MeasureTheory.integral_add
        (integrableOn_fundamental_sol_sphere Ω u x₀ ε ε₀ hε h_ball_subset_hyp hu_cont)
        (integrableOn_H_grad_sphere Ω H u x₀ ε ε₀ hε h_ball_subset_hyp hu_cont hH_diff))

lemma limit_sphere_u_grad_G (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (u : E → ℝ) (hu_cont : ContinuousOn u (closure Ω))
  (x₀ : E) (hx₀ : x₀ ∈ Ω) :
  Filter.Tendsto
    (fun ε => ∫ x in Metric.sphere x₀ ε,
      u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea)
    (𝓝[>] 0) (𝓝 (- u x₀)) := by
  obtain ⟨H, _, _, _, hG_eq_fund, hG_front, hH_front⟩ := hG x₀ hx₀
  have hH_diff_closure : ContDiffOn ℝ 2 H (closure Ω) := sorry
  obtain ⟨ε₀, hε₀_pos, h_ball_subset⟩ := exists_pos_closedBall_subset_of_isOpen HasPDEDomain.is_open hx₀
  have h_limit_Phi : Filter.Tendsto
    (fun ε => ∫ x in Metric.sphere x₀ ε, u x * ⟪gradientWithin (fun y => fundamental_sol_3d (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea)
    (𝓝[>] 0) (𝓝 (- u x₀)) := by
    have h_avg := (averaging_lemma_spherical_translated ε₀ hε₀_pos u x₀ (hu_cont.mono ((Metric.ball_subset_closedBall.trans h_ball_subset).trans subset_closure))).neg
    have h_eq : (fun ε => -((1 / (4 * Real.pi * ε ^ 2)) * ∫ x in Metric.sphere x₀ ε, u x ∂surfaceArea)) =
      (fun ε => (-1 / (4 * Real.pi * ε ^ 2)) * ∫ x in Metric.sphere x₀ ε, u x ∂surfaceArea) := by ext; ring
    exact Filter.Tendsto.congr' (eventually_integral_sphere_grad_fundamental_sol_eq Ω u x₀ ε₀ hε₀_pos (Metric.ball_subset_closedBall.trans h_ball_subset)).symm (h_eq ▸ h_avg)
  have h_sum := h_limit_Phi.add (limit_sphere_H_grad_zero Ω H u x₀ hx₀ hu_cont (by exact ContDiffOn.of_succ hH_diff_closure))
  rw [add_zero] at h_sum
  exact Filter.Tendsto.congr' ((eventually_split_sphere_integral Ω G H u x₀ ε₀ hε₀_pos h_ball_subset hu_cont (by exact ContDiffOn.of_succ hH_diff_closure) hG_eq_fund hG_front hH_front).mono fun _ h => h.symm) h_sum

lemma greens_representation_front_eq (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (u g : E → ℝ) (hu_bc : ∀ x ∈ frontier Ω, u x = g x)
  (n : E → E) (x₀ : E) (hx₀ : x₀ ∈ Ω) (ε : ℝ)
  (h_ball_subset_ε : Metric.closedBall x₀ ε ⊆ Ω) :
  ∫ x in frontier Ω,
      (G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ -
      u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ) ∂surfaceArea =
    - ∫ x in frontier Ω, g x * ⟪gradientWithin (fun y => G y x₀) (closure Ω) x, n x⟫_ℝ ∂surfaceArea := by
  have h_integrand_eq : EqOn
    (fun x => G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ - u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ)
    (fun x => - (g x * ⟪gradientWithin (fun y => G y x₀) (closure Ω) x, n x⟫_ℝ))
    (frontier Ω) := by
    intro x hx
    obtain ⟨_, _, _, _, _, hG_zero, _⟩ := hG x₀ hx₀
    have h_x_notin_ball : x ∉ Metric.closedBall x₀ ε := fun h_in =>
      hx.2 <| ‹HasPDEDomain Ω›.is_open.interior_eq.symm ▸ h_ball_subset_ε h_in
    simp_rw [hG_zero x hx, hu_bc x hx, gradientWithin_frontier_excised_eq Ω (fun y ↦ G y x₀) x₀ x ε h_x_notin_ball]
    ring
  rw [setIntegral_congr_fun isClosed_frontier.measurableSet h_integrand_eq, integral_neg]

lemma integrable_greens_grad_u_sphere
  (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε) (h_ball_subset_ε : Metric.closedBall x₀ ε ⊆ Ω)
  (H : E → ℝ) (hH_cont : ContinuousOn H (closure Ω))
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (M : ℝ) (hM_bound : ∀ x ∈ Metric.sphere x₀ ε, ‖⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ‖ ≤ M)
  (C : ℝ) (hC_bound : ∀ x ∈ Metric.sphere x₀ ε, ‖G x x₀‖ ≤ C / ε) :
  IntegrableOn (fun x => G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ) (Metric.sphere x₀ ε) surfaceArea := by
  have h_smul : Continuous (fun x : E ↦ -(1 / ε) • (x - x₀)) := by
    change Continuous ((fun _ : E ↦ -(1 / ε)) • (id - fun _ : E ↦ x₀))
    exact Continuous.smul continuous_const (Continuous.sub continuous_id continuous_const)
  exact integrand_integrable_on_sphere Ω G u (fun x => -(1 / ε) • (x - x₀)) x₀ ε hε_pos H hH_cont hG_eq_fund hu_diff
    h_smul.continuousOn
    h_ball_subset_ε C M
    (fun x hx => by
      rw [norm_mul, ← div_mul_eq_mul_div]
      exact mul_le_mul (hC_bound x hx) (hM_bound x hx) (norm_nonneg _) ((norm_nonneg _).trans (hC_bound x hx)))
    (sphere_surface_area x₀ ε hε_pos)

lemma integrable_u_grad_greens_sphere
  (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (x₀ : E) (hx₀ : x₀ ∈ Ω) (ε : ℝ) (hε_pos : 0 < ε)
  (h_ball_subset_ε : Metric.closedBall x₀ ε ⊆ Ω) :
  IntegrableOn (fun x => u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ) (Metric.sphere x₀ ε) surfaceArea := by
  obtain ⟨H_ext, _, hH_ext_diff, _, hH_ext_eq, _, _⟩ := hG x₀ hx₀
  haveI : IsFiniteMeasure (surfaceArea.restrict (Metric.sphere x₀ ε)) :=
    isFiniteMeasure_restrict.mpr (by rw [sphere_surface_area x₀ ε hε_pos]; exact ENNReal.ofReal_ne_top)
  have h_cont_u := hu_diff.continuousOn.mono
    (Metric.sphere_subset_closedBall.trans (h_ball_subset_ε.trans subset_closure))
  have h_cont_grad := continuousOn_gradientWithin_G_sphere hε_pos h_ball_subset_ε
    H_ext (hH_ext_diff.of_le le_top) hH_ext_eq
  have h_cont_normal : ContinuousOn (fun x => -(1 / ε) • (x - x₀)) (Metric.sphere x₀ ε) := by
    have h_smul : Continuous (fun x : E ↦ -(1 / ε) • (x - x₀)) := by
      change Continuous ((fun _ : E ↦ -(1 / ε)) • (id - fun _ : E ↦ x₀))
      exact Continuous.smul continuous_const (Continuous.sub continuous_id continuous_const)
    exact h_smul.continuousOn
  have h_int : IntegrableOn _ _ (surfaceArea.restrict (Metric.sphere x₀ ε)) :=
    (h_cont_u.mul (h_cont_grad.inner h_cont_normal)).integrableOn_compact (isCompact_sphere x₀ ε)
  rw [IntegrableOn] at h_int ⊢
  rw [Measure.restrict_restrict isClosed_sphere.measurableSet, Set.inter_self] at h_int
  exact h_int

lemma greens_representation_sphere_split
  (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (x₀ : E) (hx₀ : x₀ ∈ Ω) (ε : ℝ) (hε_pos : 0 < ε)
  (h_ball_subset_ε : Metric.closedBall x₀ ε ⊆ Ω)
  (H : E → ℝ) (hH_cont : ContinuousOn H (closure Ω))
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (M : ℝ) (hM_bound : ∀ x ∈ Metric.sphere x₀ ε, ‖⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ‖ ≤ M)
  (C : ℝ) (hC_bound : ∀ x ∈ Metric.sphere x₀ ε, ‖G x x₀‖ ≤ C / ε) :
  ∫ x in Metric.sphere x₀ ε,
      (G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ -
      u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ) ∂surfaceArea =
    (∫ x in Metric.sphere x₀ ε, G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea) -
    (∫ x in Metric.sphere x₀ ε, u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea) := by
  have h_integrable_1 := integrable_greens_grad_u_sphere Ω G u hu_diff x₀ ε hε_pos h_ball_subset_ε H hH_cont hG_eq_fund M hM_bound C hC_bound
  have h_integrable_2 := integrable_u_grad_greens_sphere Ω G hG u hu_diff x₀ hx₀ ε hε_pos h_ball_subset_ε
  exact integral_sub h_integrable_1 h_integrable_2

lemma greens_representation_split_epsilon (Ω : Set E) [HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (u f g : E → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hu_poisson : ∀ x ∈ Ω, laplacian u x = f x)
  (hu_bc : ∀ x ∈ frontier Ω, u x = g x)
  (n : E → E) (hn : IsOutwardUnitNormal Ω n)
  (h_cont_n : ContinuousOn n (frontier Ω))
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (ε₀ : ℝ) (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω)
  (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀)
  (H : E → ℝ) (hH_cont : ContinuousOn H (closure Ω))
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (M : ℝ) (hM_bound : ∀ x ∈ Metric.sphere x₀ ε, ‖⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ‖ ≤ M)
  (C : ℝ) (hC_bound : ∀ x ∈ Metric.sphere x₀ ε, ‖G x x₀‖ ≤ C / ε) :
  ∫ x in Ω \ Metric.closedBall x₀ ε, G x x₀ * f x =
  -(∫ x in frontier Ω, g x * ⟪gradientWithin (fun y => G y x₀) (closure Ω) x, n x⟫_ℝ ∂surfaceArea) +
  (∫ x in Metric.sphere x₀ ε, G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea) -
  (∫ x in Metric.sphere x₀ ε, u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea) := by
  have h_ball_subset_ε : Metric.closedBall x₀ ε ⊆ Ω :=
    (Metric.closedBall_subset_closedBall hε_le).trans h_ball_subset
  have h_step2 := greens_second_punctured Ω h_bounded h_area G hG u f hu_diff hu_poisson n hn h_cont_n x₀ hx₀ ε hε_pos h_ball_subset_ε
  have h_front_eq := greens_representation_front_eq Ω G hG u g hu_bc n x₀ hx₀ ε h_ball_subset_ε
  have h_sphere_split := greens_representation_sphere_split Ω G hG u hu_diff x₀ hx₀ ε hε_pos h_ball_subset_ε H hH_cont hG_eq_fund M hM_bound C hC_bound
  rw [h_step2, h_front_eq, h_sphere_split, ← add_sub_assoc]

lemma continuousOn_fundamental_sol_3d_punctured :
  ContinuousOn fundamental_sol_3d ({0}ᶜ : Set E) := by
  unfold fundamental_sol_3d
  exact continuousOn_const.div (continuousOn_const.mul continuous_norm.continuousOn)
    (fun x hx => mul_ne_zero (by positivity) (norm_ne_zero_iff.mpr hx))

lemma continuousOn_Greens_function_sphere
  (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (H : E → ℝ)
  (hH_cont : ContinuousOn H (closure Ω))
  (x₀ : E) (ε₀ : ℝ) (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω)
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) ε₀) :
  ContinuousOn (fun x => G x x₀) (Metric.sphere x₀ ε) := by
  have h_eq : EqOn (fun x => G x x₀) (fun x => fundamental_sol_3d (x - x₀) + H x) (Metric.sphere x₀ ε) := fun x hx =>
    hG_eq_fund x ⟨h_ball_subset (Metric.closedBall_subset_closedBall hε.2 (Metric.sphere_subset_closedBall hx)),
      fun heq => hε.1.ne' (by rw [heq, Metric.mem_sphere, dist_self] at hx; exact hx.symm)⟩
  exact ((continuousOn_fundamental_sol_3d_sphere x₀ ε hε.1).add
    (hH_cont.mono (Metric.sphere_subset_closedBall.trans ((Metric.closedBall_subset_closedBall hε.2).trans (h_ball_subset.trans subset_closure))))).congr h_eq

lemma exists_bound_Greens_function_sphere
  (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (H : E → ℝ)
  (hH_cont : ContinuousOn H (closure Ω))
  (x₀ : E) (ε₀ : ℝ) (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω)
  (hG_eq_fund : ∀ x ∈ Ω \ {x₀}, G x x₀ = fundamental_sol_3d (x - x₀) + H x)
  (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) ε₀) :
  ∃ C : ℝ, ∀ x ∈ Metric.sphere x₀ ε, ‖G x x₀‖ ≤ C / ε := by
  have h_cont_G_scaled : ContinuousOn (fun x => ε * ‖G x x₀‖) (Metric.sphere x₀ ε) :=
    continuousOn_const.mul (continuousOn_Greens_function_sphere Ω G H hH_cont x₀ ε₀ h_ball_subset hG_eq_fund ε hε).norm
  obtain ⟨C, hC⟩ := ((isCompact_sphere x₀ ε).image_of_continuousOn h_cont_G_scaled).bddAbove
  exact ⟨C, fun x hx => (le_div_iff₀ hε.1).mpr (by
    rw [mul_comm]
    exact hC (Set.mem_image_of_mem _ hx))⟩

lemma greens_representation_eventually_eq_split
  (Ω : Set E) [HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (u f g : E → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hu_poisson : ∀ x ∈ Ω, laplacian u x = f x)
  (hu_bc : ∀ x ∈ frontier Ω, u x = g x)
  (n : E → E) (hn : IsOutwardUnitNormal Ω n)
  (h_cont_n : ContinuousOn n (frontier Ω))
  (x₀ : E) (hx₀ : x₀ ∈ Ω)
  (ε₀ : ℝ) (hε₀_pos : 0 < ε₀)
  (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω) :
  (fun ε => ∫ x in Ω \ Metric.closedBall x₀ ε, G x x₀ * f x) =ᶠ[𝓝[>] 0]
  fun ε => -(∫ x in frontier Ω, g x * ⟪gradientWithin (fun y => G y x₀) (closure Ω) x, n x⟫_ℝ ∂surfaceArea) +
    (∫ x in Metric.sphere x₀ ε, G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea) -
    (∫ x in Metric.sphere x₀ ε, u x * ⟪gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ ∂surfaceArea) := by
  exact Filter.eventually_of_mem (Ioc_mem_nhdsGT hε₀_pos) fun ε hε => by
    obtain ⟨H, hH_cont, _, _, hG_eq_fund, _, _⟩ := hG x₀ hx₀
    obtain ⟨M, hM_bound⟩ := exists_bound_gradient_u_sphere Ω u (by exact ContDiffOn.of_succ hu_diff) x₀ ε₀ h_ball_subset ε hε
    obtain ⟨C, hC_bound⟩ := exists_bound_Greens_function_sphere Ω G H hH_cont x₀ ε₀ h_ball_subset hG_eq_fund ε hε
    exact greens_representation_split_epsilon Ω h_bounded h_area G hG u f g hu_diff hu_poisson hu_bc n hn h_cont_n x₀ hx₀ ε₀ h_ball_subset ε hε.1 hε.2 H hH_cont hG_eq_fund M hM_bound C hC_bound

lemma poisson_greens_dirichlet_representation
  (Ω : Set E) [h_domain : HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (G : E → E → ℝ)
  (hG : IsGreensFunction G Ω)
  (u f g : E → ℝ)
  (hu_cont : ContinuousOn u (closure Ω))
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hf_cont : ContinuousOn f (closure Ω))
  (hu_poisson : ∀ x ∈ Ω, laplacian u x = f x)
  (hu_bc : ∀ x ∈ frontier Ω, u x = g x)
  (n : E → E)
  (hn : IsOutwardUnitNormal Ω n)
  (hn_cont : ContinuousOn n (closure Ω))
  (hn_inner : ∀ x₀ ∈ Ω, ∀ ε > 0, ∀ x ∈ Metric.sphere x₀ ε, -(1 / ε) • (x - x₀) = n x) :
  ∀ x₀ ∈ Ω, u x₀ = (∫ x in frontier Ω,
    g x * ⟪gradientWithin (fun y => G y x₀) (closure Ω) x, n x⟫_ℝ ∂surfaceArea) +
    ∫ x in Ω, G x x₀ * f x := by
  intro x₀ hx₀
  obtain ⟨ε₀, hε₀_pos, h_ball_subset⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (h_domain.is_open.mem_nhds hx₀)
  have h_lim_const : Filter.Tendsto (fun _ : ℝ => -(∫ x in frontier Ω, g x * ⟪gradientWithin (fun y => G y x₀) (closure Ω) x, n x⟫_ℝ ∂surfaceArea))
    (𝓝[>] 0) (𝓝 (-(∫ x in frontier Ω, g x * ⟪gradientWithin (fun y => G y x₀) (closure Ω) x, n x⟫_ℝ ∂surfaceArea))) := tendsto_const_nhds
  have h_lim_rhs := (h_lim_const.add
    (limit_sphere_G_grad_u Ω G hG u hu_diff n hn_cont x₀ hx₀ (hn_inner x₀ hx₀))).sub
    (limit_sphere_u_grad_G Ω G hG u hu_cont x₀ hx₀)
  have h_ev_eq := greens_representation_eventually_eq_split Ω h_bounded h_area G hG u f g hu_diff hu_poisson hu_bc n hn (hn_cont.mono (frontier_subset_closure (s := Ω))) x₀ hx₀ ε₀ hε₀_pos h_ball_subset
  have h_vol_lim : Filter.Tendsto (fun ε => ∫ x in Ω \ Metric.closedBall x₀ ε, G x x₀ * f x) (𝓝[>] 0) (𝓝 (∫ x in Ω, G x x₀ * f x)) :=
    tendsto_setIntegral_punctured_of_integrable (greens_function_integrable Ω h_bounded G hG f hf_cont x₀ hx₀)
  have h_eq := tendsto_nhds_unique h_lim_rhs (Filter.Tendsto.congr' h_ev_eq h_vol_lim)
  linarith
