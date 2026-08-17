import PDE.Background.CalculusMeasureTheory.PDEDomains
import PDE.Background.CalculusMeasureTheory.DomainGeometry
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open Real Set MeasureTheory Metric Filter Function Pointwise InnerProductSpace RealInnerProductSpace
open scoped BigOperators Topology Classical ContDiff

noncomputable def div_field (F : E → E) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ F x)

noncomputable def div_fieldWithin (F : E → E) (s : Set E) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderivWithin ℝ F s x)

noncomputable def laplacianWithin (u : E → ℝ) (s : Set E) (x : E) : ℝ :=
  div_fieldWithin (gradientWithin u s) s x

noncomputable def laplacian (u : E → ℝ) (x : E) : ℝ :=
  div_field (gradient u) x

noncomputable def sphericalParam (θ ϕ : ℝ) : E :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![Real.sin ϕ * Real.cos θ, Real.sin ϕ * Real.sin θ, Real.cos ϕ]

def IsHarmonic (u : E → ℝ) (Ω : Set E) : Prop :=
  ∀ x ∈ Ω, laplacian u x = 0

/-!
### Algebraic and Pointwise Bounds
-/

lemma norm_sub_sq_bound (a b : E) :
  ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h_pl := parallelogram_law_with_norm ℝ a b
  have h_pos : 0 ≤ ‖a + b‖ ^ 2 := by positivity
  linarith

lemma pointwise_energy_expansion (a b : E) :
  (1 / 2 : ℝ) * ‖b‖ ^ 2 = (1 / 2 : ℝ) * ‖a‖ ^ 2 - ⟪a, a - b⟫_ℝ + (1 / 2 : ℝ) * ‖a - b‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, real_inner_comm b a]
  ring

lemma real_polynomial_pos_implies_linear_zero (A B : ℝ)
  (h : ∀ t : ℝ, 0 ≤ -t * A + t ^ 2 * B) : A = 0 := by
  rcases le_or_gt B 0 with hB | hB
  · nlinarith [h A]
  · rw [← sq_eq_zero_iff]
    linarith [sq_nonneg A, mul_nonneg (h (A / (2 * B))) (show 0 ≤ 4 * B by positivity),
      show (-(A / (2 * B)) * A + (A / (2 * B)) ^ 2 * B) * (4 * B) = -A ^ 2 by field_simp; ring]

lemma inner_bound (a b : E) : ‖⟪a, b⟫_ℝ‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  nlinarith [norm_inner_le_norm (𝕜 := ℝ) a b, sq_nonneg (‖a‖ - ‖b‖)]

lemma abs_inner_sphere_normal_le_norm {v x : E} {ε : ℝ} (hε : 0 < ε) (hx : ‖x‖ = ε) :
  |⟪v, -(1 / ε) • x⟫_ℝ| ≤ ‖v‖ := by
  have : ‖-(1 / ε) • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity), hx, div_mul_cancel₀ 1 hε.ne']
  linarith [abs_real_inner_le_norm v (-(1 / ε) • x), this ▸ mul_one ‖v‖]

lemma inner_grad_comm (u v : E → ℝ) (x : E) :
  ⟪gradient v x, gradient u x⟫_ℝ = ⟪gradient u x, gradient v x⟫_ℝ := by
  rw [real_inner_comm]

/-!
### Frechet Derivative and Gradient Properties
-/

lemma gradient_inner_fderiv (u : E → ℝ) (x v : E) :
    ⟪gradient u x, v⟫_ℝ = (fderiv ℝ u x) v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

lemma fderivWithin_eq_fderiv_of_isOpen {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (F : E → F') (s : Set E) (hs : IsOpen s) (x : E) (hx : x ∈ s) :
    fderivWithin ℝ F s x = fderiv ℝ F x := by
  exact fderivWithin_of_mem_nhds (hs.mem_nhds hx)

lemma gradientWithin_eq_gradient_of_isOpen (u : E → ℝ) (s : Set E) (hs : IsOpen s) (x : E) (hx : x ∈ s) :
    gradientWithin u s x = gradient u x := by
  unfold gradientWithin gradient
  rw [fderivWithin_eq_fderiv_of_isOpen u s hs x hx]

lemma eqOn_gradient_fderivWithin {Ω : Set E} (h_open : IsOpen Ω) (u : E → ℝ) :
  Set.EqOn (gradient u) ((InnerProductSpace.toDual ℝ E).symm ∘ fderivWithin ℝ u Ω) Ω :=
  fun y hy => by
    unfold gradient
    rw [Function.comp_apply, fderivWithin_eq_fderiv_of_isOpen u Ω h_open y hy]

lemma fderiv_norm_eq_gradient_norm (F : E → ℝ) (x : E) :
  ‖fderiv ℝ F x‖ = ‖gradient F x‖ := by
  rw [gradient,LinearIsometryEquiv.norm_map]

lemma gradient_add {f g : E → ℝ} {x : E}
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  gradient (fun y ↦ f y + g y) x = gradient f x + gradient g x := by
  have h_fderiv : fderiv ℝ (fun y ↦ f y + g y) x = fderiv ℝ f x + fderiv ℝ g x := by
    exact fderiv_add hf hg
  unfold gradient
  rw [h_fderiv]
  simp only [map_add]

lemma gradient_sub_pointwise (u w : E → ℝ) (x : E)
  (hu : DifferentiableAt ℝ u x) (hw : DifferentiableAt ℝ w x) :
  gradient (u - w) x = gradient u x - gradient w x := by
  unfold gradient
  rw [fderiv_sub hu hw]
  simp only [map_sub]

lemma gradient_smul_pointwise (v : E → ℝ) (t : ℝ) (x : E)
  (hv : DifferentiableAt ℝ v x) :
  gradient (fun y => t * v y) x = t • gradient v x := by
  change gradient (t • v) x = _
  unfold gradient
  rw [fderiv_const_smul hv]
  exact map_smul (InnerProductSpace.toDual ℝ E).symm t (fderiv ℝ v x)

lemma diff_shifted_f (f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (y x' : E) :
  DifferentiableAt ℝ (fun x'' => f (x'' - y)) x' := by
  exact Differentiable.differentiableAt ((hf_smooth.differentiable (by exact WithTop.top_ne_zero)).comp (differentiable_id.sub (differentiable_const y)))

lemma fderiv_shifted (f : E → ℝ) (x y : E) :
  fderiv ℝ (fun x' => f (x' - y)) x = fderiv ℝ f (x - y) := by
  exact fderiv_comp_sub y

lemma gradient_shifted (f : E → ℝ) (x y : E) :
  gradient (fun x' => f (x' - y)) x = gradient f (x - y) := by
  rw [gradient,gradient,fderiv_shifted f x y]

lemma fderiv_const_sub_generic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (g : E → F) (hg_diff : Differentiable ℝ g) (x y : E) :
  fderiv ℝ (fun y' => g (x - y')) y = - fderiv ℝ g (x - y) := by
  change fderiv ℝ (g ∘ fun y' => x - y') y = _
  rw [fderiv_comp y (hg_diff (x - y)) ((differentiableAt_const x).sub differentiableAt_id)]
  have h_deriv_sub : fderiv ℝ (fun y' => x - y') y = -ContinuousLinearMap.id ℝ E := by
    change fderiv ℝ ((fun _ : E => x) - id) y = _
    rw [fderiv_sub (differentiableAt_const x) differentiableAt_id]
    ext
    simp
  rw [h_deriv_sub]
  ext
  simp

lemma gradient_const_sub (f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (x y : E) :
  gradient (fun y' => f (x - y')) y = - gradient f (x - y) := by
  unfold gradient
  rw [fderiv_const_sub_generic f (hf_smooth.differentiable (by exact WithTop.top_ne_zero)) x y]
  exact map_neg (InnerProductSpace.toDual ℝ E).symm _

lemma gradient_const_mul (Φ f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (y : E) (x' : E) :
  gradient (fun x'' => Φ y * f (x'' - y)) x' = Φ y • gradient (fun x'' => f (x'' - y)) x' := by
  simp_rw [← smul_eq_mul]
  unfold gradient
  rw [fderiv_fun_const_smul (diff_shifted_f f hf_smooth y x') (Φ y)]
  exact map_smul (InnerProductSpace.toDual ℝ E).symm (Φ y) (fderiv ℝ (fun x'' => f (x'' - y)) x')

lemma fderiv_gradient_shifted_eq (f : E → ℝ) (x y : E) :
  fderiv ℝ (fun x'' => gradient (fun x''' => f (x''' - y)) x'') x = fderiv ℝ (gradient f) (x - y) := by
  rw [show (fun x'' => gradient (fun x''' => f (x''' - y)) x'') = fun x'' => gradient f (x'' - y) by funext x''; exact gradient_shifted f x'' y]
  exact fderiv_comp_sub y

lemma riesz_comp_smooth (u : E → E →L[ℝ] ℝ) (hu_smooth : ContDiff ℝ ⊤ u) :
  ContDiff ℝ ⊤ (fun x => (InnerProductSpace.toDual ℝ E).symm (u x)) := by
  exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp hu_smooth

lemma diff_gradient (f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) :
  Differentiable ℝ (gradient f) := by
  exact (show ContDiff ℝ ⊤ (gradient f) by
    rw [show gradient f = fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) by ext x; simp [gradient]]
    exact riesz_comp_smooth (fderiv ℝ f) (hf_smooth.fderiv_right le_top)
  ).differentiable (by exact WithTop.top_ne_zero)

lemma diff_gradient_shifted (f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (y x' : E) :
  DifferentiableAt ℝ (fun x'' => gradient (fun x''' => f (x''' - y)) x'') x' := by
  rw [show (fun x'' => gradient (fun x''' => f (x''' - y)) x'') = fun x'' => gradient f (x'' - y) by funext x''; exact gradient_shifted f x'' y]
  exact Differentiable.differentiableAt ((diff_gradient f hf_smooth).comp (differentiable_id.sub (differentiable_const y)))

lemma fderiv_gradient_const_mul (Φ f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (y : E) (x' : E) :
  fderiv ℝ (fun x'' => gradient (fun x''' => Φ y * f (x''' - y)) x'') x' =
  Φ y • fderiv ℝ (fun x'' => gradient (fun x''' => f (x''' - y)) x'') x' := by
  rw [show (fun x'' => gradient (fun x''' => Φ y * f (x''' - y)) x'') = (fun x'' => Φ y • gradient (fun x''' => f (x''' - y)) x'') by funext x''; exact gradient_const_mul Φ f hf_smooth y x'']
  exact fderiv_const_smul (diff_gradient_shifted f hf_smooth y x') (Φ y)

lemma gradientWithin_add_of_eqOn {f g h : E → ℝ} {s : Set E} {x : E}
  (hx : x ∈ s) (h_unique : UniqueDiffWithinAt ℝ s x)
  (heq : Set.EqOn f (fun y ↦ g y + h y) s)
  (hg_diff : DifferentiableWithinAt ℝ g s x)
  (hh_diff : DifferentiableWithinAt ℝ h s x) :
  gradientWithin f s x = gradientWithin g s x + gradientWithin h s x := by
  unfold gradientWithin
  erw [fderivWithin_congr' heq hx, fderivWithin_add h_unique hg_diff hh_diff, map_add (InnerProductSpace.toDual ℝ E).symm]

lemma gradientWithin_add_of_contDiffOn {s : Set E} (hs : UniqueDiffOn ℝ s)
  (f g : E → ℝ) (hf : ContDiffOn ℝ 1 f s) (hg : ContDiffOn ℝ 1 g s) {x : E} (hx : x ∈ s) :
  gradientWithin (fun y => f y + g y) s x = gradientWithin f s x + gradientWithin g s x := by
  unfold gradientWithin
  erw [fderivWithin_add (hs x hx) (hf.differentiableOn (by exact Ne.symm (zero_ne_one' ℕ∞ω)) x hx) (hg.differentiableOn (by exact Ne.symm (zero_ne_one' ℕ∞ω)) x hx)]
  exact map_add (InnerProductSpace.toDual ℝ E).symm _ _

lemma gradientWithin_congr {s : Set E} {f g : E → ℝ} {x : E} (h_eq : Set.EqOn f g s) (hx : f x = g x) :
  gradientWithin f s x = gradientWithin g s x := by
  unfold gradientWithin
  rw [fderivWithin_congr h_eq hx]

/-!
### Trace, Divergence and Laplacian Properties
-/

lemma continuous_trace : Continuous (fun (L : E →L[ℝ] E) => LinearMap.trace ℝ E (L : E →ₗ[ℝ] E)) := by
  let traceLM : (E →L[ℝ] E) →ₗ[ℝ] ℝ := {
    toFun := fun L => LinearMap.trace ℝ E (L : E →ₗ[ℝ] E)
    map_add' := fun x y => by simp
    map_smul' := fun c x => by simp}
  exact LinearMap.continuous_of_finiteDimensional traceLM

lemma trace_id_fin3 : LinearMap.trace ℝ E (ContinuousLinearMap.id ℝ E) = 3 := by
  rw [ContinuousLinearMap.coe_id, LinearMap.trace_id]
  change (Module.finrank ℝ E : ℝ) = 3
  simp [finrank_euclideanSpace]

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
  change LinearMap.trace ℝ E (fderivWithin ℝ (v • F) s x) = _
  rw [fderivWithin_smul (hs.uniqueDiffOn x hx) hv_diff hF_diff]
  simp; ring

lemma trace_smulRight_toDual (x : E) :
  LinearMap.trace ℝ E (ContinuousLinearMap.smulRight (InnerProductSpace.toDual ℝ E x) x) = ‖x‖^2 := by
  have h_trace : (ContinuousLinearMap.smulRight (InnerProductSpace.toDual ℝ E x) x : E →ₗ[ℝ] E) =
      dualTensorHom ℝ E E ((InnerProductSpace.toDual ℝ E x : E →ₗ[ℝ] ℝ) ⊗ₜ[ℝ] x) := by
    ext
    simp [dualTensorHom_apply]
  rw [h_trace, LinearMap.trace_eq_contract_apply]
  simp [contractLeft_apply]

lemma trace_conj_linearEquiv (A : E →L[ℝ] E) (R : E ≃ₗᵢ[ℝ] E) :
  LinearMap.trace ℝ E ((R.symm : E →L[ℝ] E).toLinearMap ∘ₗ A.toLinearMap ∘ₗ (R : E →L[ℝ] E).toLinearMap) =
  LinearMap.trace ℝ E A.toLinearMap := by
  rw [LinearMap.trace_comp_cycle A.toLinearMap (R.symm : E →L[ℝ] E).toLinearMap (R : E →L[ℝ] E).toLinearMap]
  have h_id : A.toLinearMap ∘ₗ (R : E →L[ℝ] E).toLinearMap ∘ₗ (R.symm : E →L[ℝ] E).toLinearMap = A.toLinearMap := by ext; simp
  rw [h_id]

lemma fderiv_linearIsometryEquiv (R : E ≃ₗᵢ[ℝ] E) (x : E) :
  fderiv ℝ (fun y => R y) x = (R : E →L[ℝ] E) :=
  ContinuousLinearEquiv.fderiv R.toContinuousLinearEquiv

lemma gradient_comp_linearIsometryEquiv
  (u : E → ℝ) (R : E ≃ₗᵢ[ℝ] E) (x : E)
  (hu : DifferentiableAt ℝ u (R x)) :
  gradient (fun y => u (R y)) x = R.symm (gradient u (R x)) := by
  unfold gradient
  have h_comp : fderiv ℝ (fun y => u (R y)) x = fderiv ℝ (u ∘ ⇑R) x := rfl
  rw [h_comp, fderiv_comp x hu ((R : E →L[ℝ] E).differentiable x), fderiv_linearIsometryEquiv R x]
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  ext v
  change fderiv ℝ u (R x) (R v) = (InnerProductSpace.toDual ℝ E) (R.symm ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u (R x)))) v
  have h_iso := R.inner_map_map (R.symm ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u (R x)))) v
  rw [LinearIsometryEquiv.apply_symm_apply] at h_iso
  rw [InnerProductSpace.toDual_apply_apply, ← h_iso, ← InnerProductSpace.toDual_symm_apply]

lemma fderiv_gradient_comp_linearIsometryEquiv
  (u : E → ℝ) (R : E ≃ₗᵢ[ℝ] E) (x : E)
  (hu : ContDiffAt ℝ 2 u (R x)) :
  fderiv ℝ (fun y => R.symm (gradient u (R y))) x =
    (R.symm : E →L[ℝ] E).comp ((fderiv ℝ (gradient u) (R x)).comp (R : E →L[ℝ] E)) := by
  have h_grad_diff : DifferentiableAt ℝ (gradient u) (R x) := by
    unfold gradient
    have h_fd : ContDiffAt ℝ 1 (fderiv ℝ u) (R x) := hu.fderiv_right le_rfl
    exact (ContinuousLinearEquiv.differentiableAt ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv)).comp (R x) (h_fd.differentiableAt (by norm_num))
  have h_R_diff : DifferentiableAt ℝ (fun y => R y) x := (R : E →L[ℝ] E).differentiable x
  have h_symm_diff : DifferentiableAt ℝ (fun y => R.symm y) (gradient u (R x)) := (R.symm : E →L[ℝ] E).differentiable (gradient u (R x))
  have h_comp_outer : fderiv ℝ (fun y => R.symm (gradient u (R y))) x = fderiv ℝ ((fun y => R.symm y) ∘ (gradient u ∘ fun y => R y)) x := rfl
  rw [h_comp_outer, fderiv_comp x h_symm_diff (DifferentiableAt.comp x h_grad_diff h_R_diff)]
  erw [fderiv_linearIsometryEquiv R.symm (gradient u (R x))]
  rw [fderiv_comp x h_grad_diff h_R_diff]
  erw [fderiv_linearIsometryEquiv R x]

lemma laplacian_comp_linearIsometryEquiv
  (u : E → ℝ) (R : E ≃ₗᵢ[ℝ] E) (x : E)
  (hu : ContDiffAt ℝ 2 u (R x)) :
  laplacian (fun y => u (R y)) x = laplacian u (R x) := by
  unfold laplacian div_field
  have h_eventually_eq : ∀ᶠ y in nhds x, gradient (fun z => u (R z)) y = R.symm (gradient u (R y)) := by
    have h_diff_nhds : ∀ᶠ y in nhds x, DifferentiableAt ℝ u (R y) :=
      ((R : E →L[ℝ] E).continuous.tendsto x).eventually ((ContDiffAt.eventually hu (by decide)).mono fun z hz => ContDiffAt.differentiableAt hz (by norm_num))
    exact h_diff_nhds.mono fun y hy => gradient_comp_linearIsometryEquiv u R y hy
  rw [Filter.EventuallyEq.fderiv_eq h_eventually_eq, fderiv_gradient_comp_linearIsometryEquiv u R x hu]
  exact trace_conj_linearEquiv (fderiv ℝ (gradient u) (R x)) R

lemma boundary_inner_smul (u v : E → ℝ) (n : E → E) (x : E) :
  ⟪v x • gradient u x, n x⟫_ℝ = v x * ⟪gradient u x, n x⟫_ℝ := by
  rw [real_inner_smul_left]

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

lemma div_field_congr {F G : E → E} {x : E} (h : ∀ᶠ y in 𝓝 x, F y = G y) :
    div_field F x = div_field G x := by
  rw [div_field,div_field,Filter.EventuallyEq.fderiv_eq h]

lemma div_field_greens_identity_term
    (u v : E → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x : E) :
    div_field (fun x => v x • gradient u x - u x • gradient v x) x =
    v x * laplacian u x - u x * laplacian v x := by
  have hdgu : DifferentiableAt ℝ (gradient u) x := ((LinearIsometryEquiv.contDiff _).comp (ContDiff.fderiv (f := fun _ y ↦ u y) (g := fun p ↦ p) (hu.comp contDiff_snd) contDiff_id (by norm_num) : ContDiff ℝ 1 _)).differentiable (by norm_num) x
  have hdgv : DifferentiableAt ℝ (gradient v) x := ((LinearIsometryEquiv.contDiff _).comp (ContDiff.fderiv (f := fun _ y ↦ v y) (g := fun p ↦ p) (hv.comp contDiff_snd) contDiff_id (by norm_num) : ContDiff ℝ 1 _)).differentiable (by norm_num) x
  have h_trace_smulRight : ∀ (φ : E →L[ℝ] ℝ) (w : E), LinearMap.trace ℝ E ↑(φ.smulRight w) = φ w :=
    fun φ w ↦ by rw [show (↑(φ.smulRight w) : E →ₗ[ℝ] E) = dualTensorHom ℝ E E ((φ : _) ⊗ₜ[ℝ] w) by ext; simp [dualTensorHom_apply], LinearMap.trace_eq_contract_apply]; simp [contractLeft_apply]
  dsimp [div_field, laplacian]
  erw [fderiv_sub ((hv.differentiable (by norm_num) x).smul hdgu) ((hu.differentiable (by norm_num) x).smul hdgv),
      fderiv_smul (hv.differentiable (by norm_num) x) hdgu,
      fderiv_smul (hu.differentiable (by norm_num) x) hdgv]
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_add, LinearMap.map_sub, LinearMap.map_add]
  simp_rw [ContinuousLinearMap.toLinearMap_smul, map_smul, h_trace_smulRight, ← gradient_inner_fderiv, real_inner_comm (gradient u x)]
  ring_nf

lemma gradient_c1_of_c2 (u : E → ℝ) (Ω : Set E) (h_open : IsOpen Ω) (h_smooth : ContDiffOn ℝ 2 u Ω) :
  ContDiffOn ℝ 1 (fun x => gradient u x) Ω := by
  exact ((InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn
    (h_smooth.fderivWithin h_open.uniqueDiffOn (by decide))).congr
    fun x hx => (gradientWithin_eq_gradient_of_isOpen u Ω h_open x hx).symm

lemma div_field_greens_identity_on (U : Set E) (hU_open : IsOpen U) (u v : E → ℝ)
  (hu : ContDiffOn ℝ 2 u (closure U)) (hv : ContDiffOn ℝ 2 v (closure U)) (x : E) (hx : x ∈ U) :
  div_field (fun y => v y • gradient u y - u y • gradient v y) x =
  v x * laplacian u x - u x * laplacian v x := by
  have hu_D := (((hu x (subset_closure hx)).differentiableWithinAt (by norm_num)).mono subset_closure).differentiableAt (hU_open.mem_nhds hx)
  have hv_D := (((hv x (subset_closure hx)).differentiableWithinAt (by norm_num)).mono subset_closure).differentiableAt (hU_open.mem_nhds hx)
  have hgu_D := ((gradient_c1_of_c2 u U hU_open (hu.mono subset_closure)).differentiableOn (by norm_num) x hx).differentiableAt (hU_open.mem_nhds hx)
  have hgv_D := ((gradient_c1_of_c2 v U hU_open (hv.mono subset_closure)).differentiableOn (by norm_num) x hx).differentiableAt (hU_open.mem_nhds hx)

  unfold div_field
  have heq : (fun y : E => v y • gradient u y - u y • gradient v y) =
             (v • gradient u) - (u • gradient v) := by
    ext y; simp [Pi.sub_apply]
  rw [heq, fderiv_sub (hv_D.smul hgu_D) (hu_D.smul hgv_D),
      fderiv_smul hv_D hgu_D, fderiv_smul hu_D hgv_D]
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_add,
             ContinuousLinearMap.toLinearMap_smul, map_sub, map_add, map_smul]
  erw [trace_smulRight_eq, trace_smulRight_eq]
  erw [← gradient_inner_fderiv v x (gradient u x), ← gradient_inner_fderiv u x (gradient v x)]
  rw [real_inner_comm (gradient v x) (gradient u x)]
  simp only [laplacian, smul_eq_mul]
  exact add_sub_add_right_eq_sub (v x * (LinearMap.trace ℝ E) ↑(fderiv ℝ (fun x ↦ gradient u x) x))
      (u x * (LinearMap.trace ℝ E) ↑(fderiv ℝ (fun x ↦ gradient v x) x))
      ⟪gradient v x, gradient u x⟫_ℝ

lemma laplacianWithin_eq_laplacian (u : E → ℝ) (s : Set E) (hs : IsOpen s) (x : E) (hx : x ∈ s) :
    laplacianWithin u s x = laplacian u x := by
  unfold laplacianWithin laplacian div_fieldWithin div_field
  rw [fderivWithin_congr (fun y hy ↦ gradientWithin_eq_gradient_of_isOpen u s hs y hy) (gradientWithin_eq_gradient_of_isOpen u s hs x hx), fderivWithin_eq_fderiv_of_isOpen (gradient u) s hs x hx]

lemma laplacianWithin_eq_div_field (u : E → ℝ) (s : Set E) (hs_open : IsOpen s) (x : E) (hx : x ∈ s) :
    laplacianWithin u (closure s) x = div_field (gradientWithin u (closure s)) x := by
  unfold laplacianWithin div_fieldWithin div_field
  have h_nhds : closure s ∈ 𝓝 x := Filter.mem_of_superset (hs_open.mem_nhds hx) subset_closure
  have h_deriv : fderivWithin ℝ (gradientWithin u (closure s)) (closure s) x = fderiv ℝ (gradientWithin u (closure s)) x :=
    fderivWithin_of_mem_nhds h_nhds
  rw [h_deriv]

lemma laplacianWithin_closure_eq_laplacian (u : E → ℝ) (Ω : Set E) (h_open : IsOpen Ω) (x : E) (hx : x ∈ Ω) :
  laplacianWithin u (closure Ω) x = laplacian u x := by
  unfold laplacianWithin laplacian div_fieldWithin div_field
  rw [fderivWithin_of_mem_nhds (Filter.mem_of_superset (h_open.mem_nhds hx) subset_closure)]
  have h_ev : gradientWithin u (closure Ω) =ᶠ[𝓝 x] gradient u :=
    Filter.eventuallyEq_of_mem (h_open.mem_nhds hx) fun y hy => by
      unfold gradientWithin gradient
      rw [fderivWithin_of_mem_nhds (Filter.mem_of_superset (h_open.mem_nhds hy) subset_closure)]
  rw [h_ev.fderiv_eq]

lemma laplacianWithin_eq_laplacian_of_mem_nhds (u : E → ℝ) (s : Set E) (x : E) (hx : s ∈ nhds x) :
  laplacianWithin u s x = laplacian u x := by
  have h_eq : gradientWithin u s =ᶠ[nhds x] gradient u := by
    filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hx)] with y hy
    unfold gradientWithin gradient
    rw [fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hy)]
  unfold laplacianWithin div_fieldWithin laplacian div_field
  rw [fderivWithin_of_mem_nhds hx, h_eq.fderiv_eq]

lemma laplacian_congr {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) : laplacian f x = laplacian g x := by
  unfold laplacian div_field
  rw [EventuallyEq.fderiv_eq (EventuallyEq.gradient h)]

lemma gradient_add_eventually {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (fun y => gradient (fun z => f z + g z) y) =ᶠ[𝓝 x] (fun y => gradient f y + gradient g y) := by
  filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
  unfold gradient
  erw [fderiv_add (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num)), map_add]

lemma differentiableAt_gradient_of_contDiffAt (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (gradient f) x :=
  ((LinearIsometryEquiv.contDiff _).contDiffAt.comp x (ContDiffAt.fderiv (f := fun _ y ↦ f y) (g := fun p ↦ p) (hf.comp (x, x) contDiffAt_snd) contDiffAt_id (by norm_num) : ContDiffAt ℝ 1 _ x)).differentiableAt (by norm_num)

lemma laplacian_add (f g : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    laplacian (fun y => f y + g y) x = laplacian f x + laplacian g x := by
  unfold laplacian div_field
  erw [EventuallyEq.fderiv_eq (gradient_add_eventually hf hg),
    fderiv_add (differentiableAt_gradient_of_contDiffAt f x hf) (differentiableAt_gradient_of_contDiffAt g x hg),
    map_add]

lemma laplacian_const_sub_mul (Φ f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (y x : E) :
  laplacian (fun x' => Φ y * f (x' - y)) x = Φ y * laplacian (fun x' => f (x' - y)) x := by
  unfold laplacian div_field
  erw [fderiv_gradient_const_mul Φ f hf_smooth y x, map_smul, smul_eq_mul]

lemma laplacian_translation_symmetry (f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (x y : E) :
  laplacian (fun x' => f (x' - y)) x = laplacian (fun y' => f (x - y')) y := by
  unfold laplacian div_field
  rw [funext (fun x'' => gradient_shifted f x'' y), fderiv_comp_sub y,
      funext (fun y'' => gradient_const_sub f hf_smooth x y'')]
  simp only [fderiv_fun_neg, fderiv_const_sub_generic _ (diff_gradient f hf_smooth) x y, neg_neg]

lemma gradient_const_mul_eventuallyEq (c : ℝ) (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    ∀ᶠ y in 𝓝 x, gradient (fun y => c * f y) y = c • gradient f y := by
  filter_upwards [hf.eventually (by decide)] with y hy
  exact gradient_smul_pointwise f c y (hy.differentiableAt (by norm_num))

lemma laplacian_const_mul (c : ℝ) (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    laplacian (fun y => c * f y) x = c * laplacian f x := by
  unfold laplacian div_field
  rw [Filter.EventuallyEq.fderiv_eq (gradient_const_mul_eventuallyEq c f x hf)]
  erw [fderiv_const_smul (differentiableAt_gradient_of_contDiffAt f x hf) c]
  exact LinearMap.map_smul (LinearMap.trace ℝ E) c (fderiv ℝ (gradient f) x)

/-!
### ContDiffOn, Continuity, and Differentiability
-/

lemma contDiffOn_gradientWithin (u : E → ℝ) (s : Set E)
    (hs : UniqueDiffOn ℝ s) (h_smooth : ContDiffOn ℝ 2 u s) :
    ContDiffOn ℝ 1 (gradientWithin u s) s :=
  (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn (h_smooth.fderivWithin hs (by norm_num))

lemma differentiableAt_gradient_of_contDiffOn {u : E → ℝ} {Ω : Set E} {x : E}
    (h_smooth : ContDiffOn ℝ 2 u Ω) (h_nhds : Ω ∈ nhds x) :
    DifferentiableAt ℝ (gradient u) x := by
  unfold gradient
  have h_fderiv : ContDiffAt ℝ 1 (fderiv ℝ u) x := (h_smooth.contDiffAt h_nhds).fderiv_right le_rfl
  exact (ContinuousLinearEquiv.differentiableAt ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv)).comp x
    (h_fderiv.differentiableAt (by norm_num))

lemma smooth_on_ball_closure (u : E → ℝ) (x₀ : E) (r : ℝ) (hr_pos : 0 < r)
    (h_smooth : ContDiffOn ℝ 2 u (Metric.closedBall x₀ r)) :
    ContDiffOn ℝ 2 u (closure (Metric.ball x₀ r)) := by
  rw [closure_ball_eq_closedBall x₀ r hr_pos]
  exact h_smooth

lemma contDiffOn_1_gradientWithin_continuousOn {f : E → ℝ} {s : Set E}
  (hf : ContDiffOn ℝ 1 f s) (hs : UniqueDiffOn ℝ s) :
  ContinuousOn (fun x => gradientWithin f s x) s := by
  unfold gradientWithin
  exact (toDual ℝ E).symm.continuous.comp_continuousOn (hf.continuousOn_fderivWithin hs (by decide))

lemma contDiffOn_1_gradient_continuousOn {f : E → ℝ} {s : Set E}
  (hf : ContDiffOn ℝ 1 f s) (hs : IsOpen s) :
  ContinuousOn (fun x => gradient f x) s := by
  unfold gradient
  exact (toDual ℝ E).symm.continuous.comp_continuousOn <|
    (hf.continuousOn_fderivWithin hs.uniqueDiffOn (by decide)).congr
      fun x hx => (fderivWithin_of_isOpen hs hx).symm

lemma contDiffOn_gradient_continuousOn {f : E → ℝ} {s : Set E}
  (hf : ContDiffOn ℝ 2 f s) (hs : IsOpen s) :
  ContinuousOn (fun x => gradient f x) s := by
  unfold gradient
  exact (toDual ℝ E).symm.continuous.comp_continuousOn <|
    (hf.continuousOn_fderivWithin hs.uniqueDiffOn (by decide)).congr
      fun x hx => (fderivWithin_of_isOpen hs hx).symm

lemma contDiffOn_gradient_norm_sq_continuousOn {f : E → ℝ} {s : Set E}
  (hf : ContDiffOn ℝ 2 f s) (hs : IsOpen s) :
  ContinuousOn (fun x => ‖gradient f x‖ ^ 2) s := by
  exact ((contDiffOn_gradient_continuousOn hf hs).norm).pow 2

lemma fderiv_continuousOn_of_c1 (F : E → E) (Ω : Set E) (h_open : IsOpen Ω)
  (h_smooth : ContDiffOn ℝ 1 F Ω) :
  ContinuousOn (fun x => fderiv ℝ F x) Ω := by
  exact (h_smooth.continuousOn_fderivWithin h_open.uniqueDiffOn (by decide)).congr fun x hx => (fderivWithin_of_isOpen h_open hx).symm

lemma contDiffOn_gradWithin (U : Set E) (h_unique : UniqueDiffOn ℝ (closure U)) (u : E → ℝ) (hu : ContDiffOn ℝ 2 u (closure U)) :
  ContDiffOn ℝ 1 (gradientWithin u (closure U)) (closure U) := by
  exact (LinearIsometryEquiv.contDiff (InnerProductSpace.toDual ℝ E).symm).comp_contDiffOn (by exact hu.fderivWithin h_unique (by norm_num))

lemma contDiffOn_greens_F (U : Set E) (h_unique : UniqueDiffOn ℝ (closure U)) (u v : E → ℝ)
  (hu : ContDiffOn ℝ 2 u (closure U)) (hv : ContDiffOn ℝ 2 v (closure U)) :
  ContDiffOn ℝ 1 (fun x => v x • gradientWithin u (closure U) x - u x • gradientWithin v (closure U) x) (closure U) := by
  apply ContDiffOn.sub
  · exact ContDiffOn.smul (hv.of_le (by norm_num)) (by exact contDiffOn_gradWithin U h_unique u hu)
  · exact ContDiffOn.smul (hu.of_le (by norm_num)) (by exact contDiffOn_gradWithin U h_unique v hv)

lemma fderiv_is_smooth_top (f : E → ℝ) (hf_smooth : ContDiff ℝ ∞ f) :
  ContDiff ℝ ∞ (fderiv ℝ f) :=
  (contDiff_infty_iff_fderiv.mp hf_smooth).2

lemma continuous_fderiv_gradient (f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) :
  Continuous (fderiv ℝ (gradient f)) := by
  exact (show ContDiff ℝ ⊤ (gradient f) by
    rw [show gradient f = fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) by ext x; simp [gradient]]
    exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp (hf_smooth.fderiv_right le_top)
  ).continuous_fderiv (by exact WithTop.top_ne_zero)

lemma integrand_differentiable (Φ f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (y x' : E) :
  DifferentiableAt ℝ (fun x'' => Φ y * f (x'' - y)) x' :=
  (((hf_smooth.differentiable (by exact WithTop.top_ne_zero)).differentiableAt).comp x'
    (differentiable_id.sub (differentiable_const y)).differentiableAt).const_mul (Φ y)

lemma contDiffAt_norm_of_ne_zero {x : E} (hx : x ≠ 0) :
  ContDiffAt ℝ 2 (fun y => ‖y‖) x := by
  exact contDiffAt_norm ℝ hx

lemma contDiffAt_const_mul_norm {x : E} (hx : x ≠ 0) (c : ℝ) :
    ContDiffAt ℝ 2 (fun y => c * ‖y‖) x :=
  contDiffAt_const.mul (contDiffAt_norm_of_ne_zero hx)

lemma contDiffAt_const_div_of_ne_zero {f : E → ℝ} {x : E} (c : ℝ)
    (hf_diff : ContDiffAt ℝ 2 f x) (hf_ne_zero : f x ≠ 0) :
    ContDiffAt ℝ 2 (fun y => c / f y) x :=
  contDiffAt_const.div hf_diff hf_ne_zero

lemma contDiffAt_of_contDiffOn_top {f : E → ℝ} {s : Set E} (hs : IsOpen s) (x : E) (hx : x ∈ s) (hf : ContDiffOn ℝ ⊤ f s) :
    ContDiffAt ℝ 2 f x :=
  (hf.contDiffAt (hs.mem_nhds hx)).of_le le_top

lemma contDiffOn_of_forall_contDiffAt {f : E → ℝ} {s : Set E}
    (h : ∀ x ∈ s, ContDiffAt ℝ 2 f x) :
    ContDiffOn ℝ 2 f s :=
  fun x hx => (h x hx).contDiffWithinAt

lemma contDiffOn_closure_restrict {f : E → ℝ} {Ω : Set E} {x₀ : E} {ε : ℝ}
    (hf : ContDiffOn ℝ 2 f (closure Ω)) :
    ContDiffOn ℝ 2 f (closure (Ω \ Metric.closedBall x₀ ε)) :=
  hf.mono (closure_mono sdiff_subset)

lemma greens_H_contDiffOn_punctured_closure {H : E → ℝ} {Ω : Set E} {x₀ : E} {ε : ℝ}
  (hH_diff : ContDiffOn ℝ ⊤ H (closure Ω)) :
  ContDiffOn ℝ 2 H (closure (Ω \ Metric.closedBall x₀ ε)) :=
  (hH_diff.mono closure_diff_subset_closure).of_le le_top

lemma differentiableAt_of_contDiffOn_closure {Ω : Set E} [HasPDEDomain Ω]
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω)) {x : E} (hx : x ∈ Ω) :
  DifferentiableAt ℝ u x :=
  ((hu_diff.differentiableOn (by norm_num)).mono subset_closure).differentiableAt
    (HasPDEDomain.is_open.mem_nhds hx)

lemma continuousOn_gradientWithin {s : Set E} (hs : UniqueDiffOn ℝ s) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u s) :
  ContinuousOn (fun x => gradientWithin u s x) s :=
  (toDual ℝ E).symm.continuous.comp_continuousOn ((hu.of_le (Preorder.le_refl 2)).continuousOn_fderivWithin hs (by norm_num))

lemma continuousOn_gradientWithin_of_contDiffOn
  {s : Set E} (hs : UniqueDiffOn ℝ s) (u : E → ℝ) (hu_diff : ContDiffOn ℝ 1 u s) :
  ContinuousOn (gradientWithin u s) s :=
  ((toDual ℝ E).symm.toContinuousLinearEquiv.continuous.comp_continuousOn
    (hu_diff.continuousOn_fderivWithin hs le_rfl)).congr fun _ _ => rfl

lemma continuousOn_gradient_of_contDiffOn
  {s : Set E} (hs : IsOpen s) (u : E → ℝ) (hu_diff : ContDiffOn ℝ 1 u s) :
  ContinuousOn (gradient u) s :=
  (toDual ℝ E).symm.continuous.comp_continuousOn
    (hu_diff.continuousOn_fderiv_of_isOpen hs le_rfl)

lemma contDiffOn_one_gradientWithin_of_two
  {s : Set E} (hs : UniqueDiffOn ℝ s) (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u s) :
  ContDiffOn ℝ 1 (gradientWithin u s) s :=
  ((toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hu_diff.fderivWithin hs le_rfl)).congr fun _ _ => rfl

lemma contDiffOn_one_gradient_of_two
  {s : Set E} (hs : IsOpen s) (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u s) :
  ContDiffOn ℝ 1 (gradient u) s :=
  ((toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (ContDiffOn.fderiv_of_isOpen hu_diff hs le_rfl)).congr fun _ _ => rfl

lemma gradientWithin_contDiffOn_one
  (Ω : Set E)
  [h_domain : HasPDEDomain Ω]
  (u : E → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω)) :
  ContDiffOn ℝ 1 (gradientWithin u (closure Ω)) (closure Ω) :=
  contDiffOn_one_gradientWithin_of_two h_domain.unique_diff u hu_diff

lemma smul_gradient_contDiffOn_one
  (Ω : Set E)
  [h_domain : HasPDEDomain Ω]
  (u v : E → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (hv_diff : ContDiffOn ℝ 2 v (closure Ω)) :
  ContDiffOn ℝ 1 (fun x => v x • gradient u x) Ω :=
  ((hv_diff.of_le (by decide)).mono subset_closure).smul
    (contDiffOn_one_gradient_of_two h_domain.is_open u (hu_diff.mono subset_closure))

lemma smul_gradientWithin_continuousOn
  (Ω : Set E)
  [h_domain : HasPDEDomain Ω]
  (u v : E → ℝ)
  (hu_diff : ContDiffOn ℝ 1 u (closure Ω))
  (hv_cont : ContinuousOn v (closure Ω)) :
  ContinuousOn (fun x => v x • gradientWithin u (closure Ω) x) (closure Ω) :=
  hv_cont.smul (((toDual ℝ E).symm.toContinuousLinearEquiv.continuous.comp_continuousOn
    (hu_diff.continuousOn_fderivWithin h_domain.unique_diff le_rfl)).congr fun _ _ => rfl)

lemma div_fieldWithin_continuousOn
  (Ω : Set E)
  [h_domain : HasPDEDomain Ω]
  (F : E → E)
  (hF_c1 : ContDiffOn ℝ 1 F (closure Ω)) :
  ContinuousOn (fun x => div_fieldWithin F (closure Ω) x) (closure Ω) :=
  (LinearMap.continuous_of_finiteDimensional
    ({ toFun := fun L => LinearMap.trace ℝ E L
       map_add' := fun _ _ => by simp
       map_smul' := fun _ _ => by simp } : (E →L[ℝ] E) →ₗ[ℝ] ℝ)).comp_continuousOn
    (hF_c1.continuousOn_fderivWithin h_domain.unique_diff le_rfl)

lemma laplacianWithin_continuousOn
  (Ω : Set E)
  [h_domain : HasPDEDomain Ω]
  (u : E → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω)) :
  ContinuousOn (laplacianWithin u (closure Ω)) (closure Ω) :=
  div_fieldWithin_continuousOn Ω (gradientWithin u (closure Ω)) (gradientWithin_contDiffOn_one Ω u hu_diff)

/-!
### Geometric Calculus
-/

lemma sphere_eq_image_sphericalParam :
  Metric.sphere (0 : E) 1 = (fun (p : ℝ × ℝ) ↦ sphericalParam p.1 p.2) '' (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 Real.pi) := by
  ext x
  simp only [Metric.mem_sphere, Set.mem_image, dist_zero_right, Set.mem_prod, Set.mem_Icc, Prod.exists]
  constructor
  · intro hx
    have h_norm : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
      have h : ‖x‖ ^ 2 = 1 ^ 2 := by rw [hx]
      rw [← real_inner_self_eq_norm_sq] at h
      simp [inner, Fin.sum_univ_succ] at h
      linarith

    let r_xy := Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
    let θ := if 0 ≤ x 1 then Real.arccos (x 0 / r_xy) else 2 * Real.pi - Real.arccos (x 0 / r_xy)
    let ϕ := Real.arccos (x 2)

    use θ, ϕ
    constructor
    · constructor
      · constructor
        · simp only [θ]
          split_ifs
          · exact Real.arccos_nonneg _
          · linarith [Real.arccos_le_pi (x 0 / r_xy), Real.pi_pos]
        · simp only [θ]
          split_ifs
          · linarith [Real.arccos_le_pi (x 0 / r_xy), Real.pi_pos]
          · linarith [Real.arccos_nonneg (x 0 / r_xy)]
      · constructor
        · exact Real.arccos_nonneg _
        · exact Real.arccos_le_pi _
    · ext i
      simp only [θ, ϕ, r_xy]
      unfold sphericalParam
      match i with
      | 0 =>
        change Real.sin ϕ * Real.cos θ = x 0
        simp [ϕ, θ, r_xy, Real.sin_arccos]
        rw [show 1 - x 2 ^ 2 = x 0 ^ 2 + x 1 ^ 2 by linarith [h_norm]]
        split_ifs with h1
        · rw [Real.cos_arccos]
          · rcases eq_or_ne (√(x 0 ^ 2 + x 1 ^ 2)) 0 with hr | hr
            · have : x 0 ^ 2 + x 1 ^ 2 = 0 := by rw [← Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), hr, zero_pow two_ne_zero]
              rw [hr, show x 0 = 0 by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]]
              ring
            · exact (mul_comm _ _).trans (div_mul_cancel₀ (x 0) hr)
          · by_cases hr : √(x 0 ^ 2 + x 1 ^ 2) = 0
            · rw [hr, div_zero]; linarith
            · rw [le_div_iff₀ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr))]
              have h_abs : |x 0| ≤ √(x 0 ^ 2 + x 1 ^ 2) := by
                rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (x 1)])
              linarith [neg_le_abs (x 0), h_abs]
          · by_cases hr : √(x 0 ^ 2 + x 1 ^ 2) = 0
            · rw [hr, div_zero]; linarith
            · rw [div_le_iff₀ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr))]
              have h_abs : |x 0| ≤ √(x 0 ^ 2 + x 1 ^ 2) := by
                rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (x 1)])
              linarith [le_abs_self (x 0), h_abs]
        · have h_cos_shift : Real.cos (2 * Real.pi - Real.arccos (x 0 / √(x 0 ^ 2 + x 1 ^ 2))) = Real.cos (Real.arccos (x 0 / √(x 0 ^ 2 + x 1 ^ 2))) := by
            rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]; ring
          rw [h_cos_shift, Real.cos_arccos]
          · rcases eq_or_ne (√(x 0 ^ 2 + x 1 ^ 2)) 0 with hr | hr
            · have : x 0 ^ 2 + x 1 ^ 2 = 0 := by rw [← Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), hr, zero_pow two_ne_zero]
              rw [hr, show x 0 = 0 by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]]
              ring
            · · exact (mul_comm _ _).trans (div_mul_cancel₀ (x 0) hr)
          · by_cases hr : √(x 0 ^ 2 + x 1 ^ 2) = 0
            · rw [hr, div_zero]; linarith
            · rw [le_div_iff₀ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr))]
              have h_abs : |x 0| ≤ √(x 0 ^ 2 + x 1 ^ 2) := by
                rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (x 1)])
              linarith [neg_le_abs (x 0), h_abs]
          · by_cases hr : √(x 0 ^ 2 + x 1 ^ 2) = 0
            · rw [hr, div_zero]; linarith
            · rw [div_le_iff₀ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr))]
              have h_abs : |x 0| ≤ √(x 0 ^ 2 + x 1 ^ 2) := by
                rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (x 1)])
              linarith [le_abs_self (x 0), h_abs]
      | 1 =>
        change Real.sin ϕ * Real.sin θ = x 1
        simp only [ϕ, θ, r_xy, Real.sin_arccos]
        rw [show 1 - x 2 ^ 2 = x 0 ^ 2 + x 1 ^ 2 by linarith [h_norm]]
        split_ifs with h1
        · rcases eq_or_ne (x 0 ^ 2 + x 1 ^ 2) 0 with hr2 | hr2
          · have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
            have hx1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
            simp [hx0, hx1]
          · have hr_pos : 0 < x 0 ^ 2 + x 1 ^ 2 := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hr2)
            have h_inner : 1 - (x 0 / √(x 0 ^ 2 + x 1 ^ 2)) ^ 2 = x 1 ^ 2 / (x 0 ^ 2 + x 1 ^ 2) := by
              rw [div_pow, Real.sq_sqrt (le_of_lt hr_pos)]; have : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := hr2; field_simp; ring
            simp
            rw [Real.sin_arccos, h_inner, Real.sqrt_div (sq_nonneg (x 1)), Real.sqrt_sq h1, mul_comm]
            exact div_mul_cancel₀ (x 1) (ne_of_gt (Real.sqrt_pos.mpr hr_pos))
        · have h_sin_shift : Real.sin (2 * Real.pi - Real.arccos (x 0 / √(x 0 ^ 2 + x 1 ^ 2))) = - Real.sin (Real.arccos (x 0 / √(x 0 ^ 2 + x 1 ^ 2))) := by
            rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]; ring
          rw [h_sin_shift, Real.sin_arccos]
          rcases eq_or_ne (x 0 ^ 2 + x 1 ^ 2) 0 with hr2 | hr2
          · have hx1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
            have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
            simp [hx0, hx1]
          · have hr_pos : 0 < x 0 ^ 2 + x 1 ^ 2 := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hr2)
            have h_inner : 1 - (x 0 / √(x 0 ^ 2 + x 1 ^ 2)) ^ 2 = x 1 ^ 2 / (x 0 ^ 2 + x 1 ^ 2) := by
              rw [div_pow, Real.sq_sqrt (le_of_lt hr_pos)]; have : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := hr2; field_simp; ring
            rw [h_inner, Real.sqrt_div (sq_nonneg (x 1)), Real.sqrt_sq_eq_abs, abs_of_nonpos (le_of_not_ge h1)]
            rw [show - (-x 1 / √(x 0 ^ 2 + x 1 ^ 2)) = x 1 / √(x 0 ^ 2 + x 1 ^ 2) by ring, mul_comm]
            simp
            exact div_mul_cancel₀ (x 1) (ne_of_gt (Real.sqrt_pos.mpr hr_pos))
      | 2 =>
        change Real.cos ϕ = x 2
        simp
        have h_sq : x 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), h_norm]
        have h_le : x 2 ≤ 1 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
        have h_ge : -1 ≤ x 2 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
        exact Real.cos_arccos h_ge h_le
  · rintro ⟨θ, ϕ, ⟨_, _⟩, ⟨_, _⟩, rfl⟩
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
    unfold sphericalParam
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three, one_pow]
    ring_nf
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq ϕ]

lemma fderiv_smul_commute (u : E → ℝ) (x x₀ : E) (r : ℝ) :
    (fderiv ℝ u x) ((1 / r) • (x - x₀)) = (fderiv ℝ u x) (x - x₀) * (1 / r) := by
  simp_all only [one_div, map_smul, map_sub, smul_eq_mul]
  linarith

lemma hasDerivAt_affine_radius (x₀ y : E) (s : ℝ) :
    HasDerivAt (fun s' ↦ x₀ + s' • y) y s := by
  simpa using (hasDerivAt_id s).smul_const y |>.const_add x₀

lemma deriv_comp_affine (u : E → ℝ) (Ω : Set E) (x₀ y : E) (r : ℝ)
    (h_open : IsOpen Ω)
    (h_smooth : ContDiffOn ℝ 1 u Ω)
    (h_in_Omega : x₀ + r • y ∈ Ω) :
    deriv (fun s ↦ u (x₀ + s • y)) r = (fderiv ℝ u (x₀ + r • y)) y :=
  (h_smooth.differentiableOn (by exact Ne.symm (zero_ne_one' ℕ∞ω))).differentiableAt (h_open.mem_nhds h_in_Omega)
    |>.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_affine_radius x₀ y r)
    |>.deriv

lemma fderiv_bound_on_closedBall (u : E → ℝ) (Ω : Set E) (x₀ : E) (R : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_open : IsOpen Ω)
    (h_smooth : ContDiffOn ℝ 1 u Ω) :
    ∃ M : ℝ, ∀ s ∈ Set.Ioo 0 R, ∀ y ∈ sphere (0 : E) 1, ‖fderiv ℝ u (x₀ + s • y)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ R).image_of_continuousOn
    (continuous_norm.comp_continuousOn ((h_smooth.continuousOn_fderiv_of_isOpen h_open le_rfl).mono h_closed_ball)) |>.bddAbove
  exact ⟨M, fun s hs y hy ↦ hM (Set.mem_image_of_mem _ (affine_mem_closedBall x₀ hs.1.le hs.2.le hy))⟩

lemma affine_eval_at_radius (x₀ x : E) (r : ℝ) (hr : 0 < r) :
    x₀ + r • ((1 / r) • (x - x₀)) = x := by
  rw [one_div, ← mul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]; abel

lemma hasDerivAt_radial_comp (u : E → ℝ) (x₀ x : E) (r : ℝ) (hr : 0 < r)
    (hu : DifferentiableAt ℝ u x) :
    HasDerivAt (fun s ↦ u (x₀ + s • ((1 / r) • (x - x₀))))
      ((fderiv ℝ u x) ((1 / r) • (x - x₀))) r :=
  (show HasFDerivAt u (fderiv ℝ u x) (x₀ + r • _) by rw [affine_eval_at_radius x₀ x r hr]; exact hu.hasFDerivAt)
    |>.comp_hasDerivAt r (hasDerivAt_affine_radius x₀ ((1 / r) • (x - x₀)) r)

lemma fderiv_eq_radial_deriv (u : E → ℝ) (x₀ x : E) (r : ℝ) (hr : 0 < r)
    (hu : DifferentiableAt ℝ u x) :
    (fderiv ℝ u x) ((1 / r) • (x - x₀)) =
    deriv (fun s ↦ u (x₀ + s • ((1 / r) • (x - x₀)))) r := by
  have h_has_deriv := hasDerivAt_radial_comp u x₀ x r hr hu
  exact h_has_deriv.deriv.symm

lemma uniqueDiffWithinAt_outside_ball_shifted (x₀ : E) (ε : ℝ) (hε : 0 < ε) (x : E) (hx : dist x x₀ = ε) :
  UniqueDiffWithinAt ℝ {y : E | ε ≤ dist y x₀} x := by
  have hx_norm : ‖x - x₀‖ = ε := by rw [← dist_eq_norm, hx]

  have h_convex : Convex ℝ {y : E | ε^2 ≤ ⟪x - x₀, y - x₀⟫_ℝ} := fun y hy z hz a b ha hb hab => by
    change ε^2 ≤ ⟪x - x₀, (a • y + b • z) - x₀⟫_ℝ
    have h_sub : (a • y + b • z) - x₀ = a • (y - x₀) + b • (z - x₀) := by
      calc (a • y + b • z) - x₀ = (a • y + b • z) - (1 : ℝ) • x₀ := by rw [one_smul]
        _ = (a • y + b • z) - (a + b) • x₀ := by rw [hab]
        _ = a • y + b • z - (a • x₀ + b • x₀) := by rw [add_smul]
        _ = (a • y - a • x₀) + (b • z - b • x₀) := by abel
        _ = a • (y - x₀) + b • (z - x₀) := by rw [smul_sub, smul_sub]
    rw [h_sub, inner_add_right, inner_smul_right, inner_smul_right]
    calc ε^2 = a * ε^2 + b * ε^2 := by rw [← add_mul, hab, one_mul]
      _ ≤ a * ⟪x - x₀, y - x₀⟫_ℝ + b * ⟪x - x₀, z - x₀⟫_ℝ := add_le_add (mul_le_mul_of_nonneg_left hy ha) (mul_le_mul_of_nonneg_left hz hb)

  have h_int : (interior {y : E | ε^2 ≤ ⟪x - x₀, y - x₀⟫_ℝ}).Nonempty := by
    refine ⟨x + (x - x₀), mem_interior.mpr ⟨{y | ε^2 < ⟪x - x₀, y - x₀⟫_ℝ}, ?_,
      isOpen_lt continuous_const (continuous_const.inner (continuous_id.sub continuous_const)), ?_⟩⟩
    · intro y hy
      simp only [Set.mem_setOf_eq] at hy ⊢
      exact le_of_lt hy
    · simp only [Set.mem_setOf_eq]
      have h_sub_add : x + (x - x₀) - x₀ = (x - x₀) + (x - x₀) := by abel
      rw [h_sub_add, inner_add_right, real_inner_self_eq_norm_sq, hx_norm]
      have h_pos : 0 < ε^2 := sq_pos_of_ne_zero (ne_of_gt hε)
      linarith

  refine (UniqueDiffOn.uniqueDiffWithinAt (uniqueDiffOn_convex h_convex h_int) ?_).mono fun y hy => ?_
  · simp only [Set.mem_setOf_eq]
    rw [real_inner_self_eq_norm_sq, hx_norm]
  · exact (mul_le_mul_iff_of_pos_left hε).mp <| by
      have h_le : ε^2 ≤ ε * dist y x₀ := by
        calc ε^2 ≤ ⟪x - x₀, y - x₀⟫_ℝ := hy
          _ ≤ ‖x - x₀‖ * ‖y - x₀‖ := real_inner_le_norm (x - x₀) (y - x₀)
          _ = ε * dist y x₀ := by rw [hx_norm, ← dist_eq_norm]
      rw [sq] at h_le
      exact h_le

lemma gradientWithin_eq_gradient_of_differentiableAt (u : E → ℝ) (s : Set E) (x : E)
  (hu : DifferentiableAt ℝ u x) (hs : UniqueDiffWithinAt ℝ s x) :
  gradientWithin u s x = gradient u x := by
  dsimp only [gradientWithin, gradient]
  rw [show fderivWithin ℝ u s x = fderiv ℝ u x by exact DifferentiableAt.fderivWithin hu hs]

lemma uniqueDiffWithinAt_closure_annulus (Ω : Set E) [HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε : 0 < ε) (x : E)
  (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (hx : x ∈ Metric.sphere x₀ ε) :
  UniqueDiffWithinAt ℝ (closure (Ω \ Metric.closedBall x₀ ε)) x := by
  refine ((uniqueDiffWithinAt_outside_ball_shifted x₀ ε hε x (Metric.mem_sphere.mp hx)).inter (HasPDEDomain.is_open.mem_nhds (h_subset (Metric.sphere_subset_closedBall hx)))).mono fun y hy => ?_
  rw [Metric.mem_closure_iff]
  intro δ hδ

  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp HasPDEDomain.is_open y hy.2
  have hy_lb : ε ≤ dist y x₀ := hy.1
  let t := (min δ r / 2) / dist y x₀
  have ht_pos : 0 < t := div_pos (half_pos (lt_min hδ hr_pos)) (by exact hε.trans_le hy_lb)

  let y' := x₀ + (1 + t) • (y - x₀)

  have h_dist : dist y' y = min δ r / 2 := by
    rw [dist_eq_norm]
    have h_sub : y' - y = t • (y - x₀) := by
      change x₀ + (1 + t) • (y - x₀) - y = t • (y - x₀)
      rw [add_smul, one_smul]
      abel
    rw [h_sub, norm_smul, Real.norm_of_nonneg ht_pos.le]
    have h_dist_eq : ‖y - x₀‖ = dist y x₀ := by rw [dist_eq_norm]
    rw [h_dist_eq, div_mul_cancel₀ _ (ne_of_gt (by exact hε.trans_le hy_lb))]

  refine ⟨y', ⟨?_, ?_⟩, ?_⟩
  · apply hr_sub
    rw [Metric.mem_ball, h_dist]
    linarith [min_le_right δ r, hr_pos]
  · intro h_in
    rw [Metric.mem_closedBall, dist_eq_norm] at h_in
    have h_sub_x0 : y' - x₀ = (1 + t) • (y - x₀) := by
      change x₀ + (1 + t) • (y - x₀) - x₀ = (1 + t) • (y - x₀)
      abel
    rw [h_sub_x0, norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 + t)] at h_in
    have h_dist_eq : ‖y - x₀‖ = dist y x₀ := by rw [dist_eq_norm]
    rw [h_dist_eq] at h_in
    have : 0 < t * dist y x₀ := mul_pos ht_pos (by exact hε.trans_le hy_lb)
    linarith
  · rw [dist_comm, h_dist]
    linarith [min_le_left δ r, hδ]

lemma contDiffOn_1_ball_of_C2_Omega (Ω : Set E) [HasPDEDomain Ω] (q : E) (ε : ℝ)
  (hq_subset : Metric.closedBall q ε ⊆ Ω) (H : E → ℝ) (hH_diff : ContDiffOn ℝ 2 H Ω) :
  ContDiffOn ℝ 1 H (Metric.ball q ε) :=
  (hH_diff.of_le (by decide)).mono (Metric.ball_subset_closedBall.trans hq_subset)

lemma continuousOn_closure_ball_of_C2_Omega (Ω : Set E) [HasPDEDomain Ω] (q : E) (ε : ℝ) (hε : 0 < ε)
  (hq_subset : Metric.closedBall q ε ⊆ Ω) (H : E → ℝ) (hH_diff : ContDiffOn ℝ 2 H Ω) :
  ContinuousOn H (closure (Metric.ball q ε)) := by
  rw [closure_ball q (ne_of_gt hε)]
  exact hH_diff.continuousOn.mono hq_subset

lemma continuousOn_closedBall_of_C2_Omega (Ω : Set E) [HasPDEDomain Ω] (q : E) (ε : ℝ)
  (hq_subset : Metric.closedBall q ε ⊆ Ω) (H : E → ℝ) (hH_diff : ContDiffOn ℝ 2 H Ω) :
  ContinuousOn H (Metric.closedBall q ε) :=
  hH_diff.continuousOn.mono hq_subset

lemma continuousOn_sphere_of_C2_Omega (Ω : Set E) [HasPDEDomain Ω] (q : E) (ε : ℝ)
  (hq_subset : Metric.closedBall q ε ⊆ Ω) (H : E → ℝ) (hH_diff : ContDiffOn ℝ 2 H Ω) :
  ContinuousOn H (Metric.sphere q ε) :=
  (continuousOn_closedBall_of_C2_Omega Ω q ε hq_subset H hH_diff).mono Metric.sphere_subset_closedBall

/-!
### Comapct Support and Integration
-/

lemma gradient_zero_outside_support (v : E → ℝ) (x : E) (hx : x ∉ tsupport v) :
  gradient v x = 0 := by
  unfold gradient
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem ((isOpen_compl_iff.mpr (isClosed_tsupport v)).mem_nhds hx) fun y hy => image_eq_zero_of_notMem_tsupport hy)]
  simp only [fderiv_fun_const, Pi.zero_apply, map_zero]

lemma eventuallyEq_zero_of_notMem_tsupport {φ : E → ℝ} {x : E} (hx : x ∉ tsupport φ) :
    φ =ᶠ[𝓝 x] 0 := by
  filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
  exact Function.notMem_support.mp (fun h ↦ hy (subset_closure h))

lemma gradient_eq_zero_of_notMem_tsupport {φ : E → ℝ} {x : E} (hx : x ∉ tsupport φ) :
    gradient φ x = 0 := by
  simp [gradient, (eventuallyEq_zero_of_notMem_tsupport hx).fderiv_eq]

lemma laplacian_eq_zero_of_notMem_tsupport {φ : E → ℝ} {x : E} (hx : x ∉ tsupport φ) :
  laplacian φ x = 0 := by
  have hev : gradient φ =ᶠ[𝓝 x] 0 :=
    Filter.eventually_of_mem
      ((isClosed_tsupport φ).isOpen_compl.mem_nhds hx)
      (fun y hy ↦ gradient_eq_zero_of_notMem_tsupport hy)
  simp [laplacian, div_field, hev.fderiv_eq]

lemma laplacian_continuous (φ : E → ℝ) (h_smooth : ContDiff ℝ ⊤ φ) :
    Continuous (fun x => laplacian φ x) := by
  unfold laplacian div_field
  refine continuous_trace.comp (continuousOn_univ.mp ?_)
  exact fderiv_continuousOn_of_c1 _ _ isOpen_univ
        (gradient_c1_of_c2 _ _ isOpen_univ (h_smooth.contDiffOn.of_le (by norm_num)))

lemma laplacian_compact_support (φ : E → ℝ) (h_supp : HasCompactSupport φ) :
    HasCompactSupport (fun x => laplacian φ x) := by
  apply HasCompactSupport.intro' h_supp (isClosed_tsupport _)
  exact fun x hx => laplacian_eq_zero_of_notMem_tsupport hx

lemma phi_eq_zero_on_frontier (φ : E → ℝ) (Ω : Set E) (h_open : IsOpen Ω)
  (h_supp : tsupport φ ⊆ Ω) (x : E) (hx : x ∈ frontier Ω) : φ x = 0 := by
  rw [show frontier Ω = closure Ω \ Ω by exact h_open.frontier_eq] at hx
  by_contra h_nz
  exact hx.2 (h_supp (subset_closure h_nz))

lemma gradientWithin_phi_eq_zero_on_frontier (φ : E → ℝ) (Ω : Set E) (h_open : IsOpen Ω)
    (h_supp : tsupport φ ⊆ Ω) (ε : ℝ) (x : E) (hx : x ∈ frontier Ω) :
    gradientWithin φ (closure (Ω \ Metric.closedBall (0 : E) ε)) x = 0 := by
  have h_zero : φ =ᶠ[𝓝 x] 0 := Eventually.mono
    (isClosed_closure.isOpen_compl.mem_nhds fun h => (h_open.frontier_eq ▸ hx).2 (h_supp h))
    fun _ hy => by_contra fun h_nz => hy (subset_closure h_nz)
  unfold gradientWithin
  rw [(h_zero.filter_mono nhdsWithin_le_nhds).fderivWithin_eq h_zero.self_of_nhds]
  simp

lemma bound_gradient_of_compact_support (φ : E → ℝ) (h_smooth : ContDiff ℝ ⊤ φ) (h_supp : HasCompactSupport φ) :
  ∃ M : ℝ, ∀ x, ‖gradient φ x‖ ≤ M := by
  have h_cont : Continuous (gradient φ) := (InnerProductSpace.toDual ℝ E).symm.continuous.comp (h_smooth.continuous_fderiv (by exact WithTop.top_ne_zero))
  have h_supp_grad : HasCompactSupport (gradient φ) :=
    IsCompact.of_isClosed_subset h_supp (isClosed_tsupport _)
      (closure_minimal (fun _ hx => by_contra fun h => hx (gradient_eq_zero_of_notMem_tsupport h)) (isClosed_tsupport φ))

  obtain ⟨M, hM⟩ := IsCompact.bddAbove (IsCompact.image h_supp_grad h_cont.norm)
  exact ⟨max M 0, fun x => by
    by_cases hx : x ∈ tsupport (gradient φ)
    · exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · simp [show gradient φ x = 0 by exact Function.notMem_support.mp (fun hmem => hx (subset_closure hmem))]⟩

lemma continuous_gradient (φ : E → ℝ) (h_smooth : ContDiff ℝ ⊤ φ) :
    Continuous (gradient φ) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp (h_smooth.continuous_fderiv (by exact WithTop.top_ne_zero))

lemma hasCompactSupport_gradient (f : E → ℝ) (hf_supp : HasCompactSupport f) :
  HasCompactSupport (gradient f) := by
  rw [show gradient f = (fun u => (InnerProductSpace.toDual ℝ E).symm u) ∘ fderiv ℝ f by funext x; rfl]
  exact HasCompactSupport.comp_left (HasCompactSupport.fderiv ℝ hf_supp) (LinearIsometryEquiv.map_zero (InnerProductSpace.toDual ℝ E).symm)

lemma hasCompactSupport_fderiv_gradient (f : E → ℝ) (hf_supp : HasCompactSupport f) :
  HasCompactSupport (fderiv ℝ (gradient f)) := by
  exact HasCompactSupport.fderiv ℝ (hasCompactSupport_gradient f hf_supp)

lemma fderiv_gradient_bound (f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
  ∃ M : ℝ, ∀ z : E, ‖fderiv ℝ (gradient f) z‖ ≤ M := by
  exact exists_bound_of_continuous_compact_support (fderiv ℝ (gradient f)) (continuous_fderiv_gradient f hf_smooth) (hasCompactSupport_fderiv_gradient f hf_supp)

lemma shifted_fderiv_gradient_bound (f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
  ∃ M : ℝ, ∀ x y : E, ‖fderiv ℝ (fun x'' => gradient (fun x''' => f (x''' - y)) x'') x‖ ≤ M := by
  rcases fderiv_gradient_bound f hf_smooth hf_supp with ⟨M, hM⟩
  exact ⟨M, fun x y => by rw [fderiv_gradient_shifted_eq f x y]; exact hM (x - y)⟩

lemma gradient_zero_of_outside_support (f : E → ℝ) (x y : E) (r R : ℝ)
  (h_supp : ∀ x' ∈ Metric.ball x r, ∀ y ∉ Metric.ball (0 : E) R, f (x' - y) = 0)
  (x' : E) (hx' : x' ∈ Metric.ball x r) (hy : y ∉ Metric.ball (0 : E) R) :
  gradient (fun x'' => f (x'' - y)) x' = 0 := by
  unfold gradient
  rw [Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.ball x r, IsOpen.mem_nhds isOpen_ball hx', fun x'' hx'' => h_supp x'' hx'' y hy⟩ |>.fderiv_eq]
  simp_all only [mem_ball, dist_zero_right, not_lt, fderiv_fun_const, Pi.zero_apply, map_zero]

lemma fderiv_gradient_zero_of_outside_support (f : E → ℝ) (x y : E) (r R : ℝ)
  (h_supp : ∀ x' ∈ Metric.ball x r, ∀ y ∉ Metric.ball (0 : E) R, f (x' - y) = 0)
  (x' : E) (hx' : x' ∈ Metric.ball x r) (hy : y ∉ Metric.ball (0 : E) R) :
  fderiv ℝ (fun x'' => gradient (fun x''' => f (x''' - y)) x'') x' = 0 := by
  rw [Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.ball x r, IsOpen.mem_nhds isOpen_ball hx', fun x'' hx'' => gradient_zero_of_outside_support f x y r R h_supp x'' hx'' hy⟩ |>.fderiv_eq, fderiv_const_apply]

lemma shifted_gradient_bound (f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
  ∃ M : ℝ, ∀ x y : E, ‖gradient (fun x' => f (x' - y)) x‖ ≤ M := by
  rcases bound_gradient_of_compact_support f hf_smooth hf_supp with ⟨M, hM⟩
  exact ⟨M, fun x y => by rw [gradient_shifted f x y]; exact hM (x - y)⟩


lemma integral_ball_tendsto_zero (F : E → ℝ) (hF : Integrable F volume) :
    Tendsto (fun ε => ∫ x in Metric.ball (0 : E) ε, F x) (𝓝[>] 0) (𝓝 0) := by
  simp_rw [← integral_indicator measurableSet_ball]
  have H : Tendsto (fun ε => ∫ x : E, (Metric.ball (0 : E) ε).indicator F x) (𝓝[>] 0) (𝓝 (∫ x : E, 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖)
      (Eventually.of_forall fun _ => hF.aestronglyMeasurable.indicator measurableSet_ball)
      (Eventually.of_forall fun ε => Eventually.of_forall fun x => by
        by_cases hx : x ∈ Metric.ball (0 : E) ε <;> simp [Set.indicator, hx]) hF.norm ?_
    have h_ae : ∀ᵐ x : E ∂volume, x ≠ 0 := by
      rw [ae_iff]; have : {a : E | ¬a ≠ 0} = {0} := by ext; simp
      simp_all only [ne_eq, Decidable.not_not, setOf_eq_eq_singleton, measure_singleton]
    refine h_ae.mono fun x hx => tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (norm_pos_iff.mpr hx))] with ε hε
    exact (Set.indicator_of_notMem (fun h => not_lt_of_gt hε (by rwa [Metric.mem_ball, dist_zero_right] at h)) F).symm
  rw [integral_zero] at H
  exact H

lemma integrableOn_of_continuousOn_compact_finite_measure
    {f : E → ℝ} {s : Set E} {μ : Measure E}
    (h_comp : IsCompact s) (h_meas : MeasurableSet s)
    (h_fin : μ s < ⊤) (h_cont : ContinuousOn f s) :
    IntegrableOn f s μ := by
  obtain ⟨C, hC⟩ := (h_comp.image_of_continuousOn h_cont.norm).bddAbove
  exact MeasureTheory.Integrable.mono (integrableOn_const (C := C) h_fin.ne)
    (h_cont.aestronglyMeasurable h_meas)
    ((ae_restrict_iff' h_meas).mpr (Eventually.of_forall fun x hx => (hC (Set.mem_image_of_mem _ hx)).trans (le_abs_self C)))

/-!
### Inverse Norm Properties
-/

lemma inv_norm_smooth_on_annulus (Ω : Set E) (ε : ℝ) (hε : 0 < ε) :
  ContDiffOn ℝ 2 (fun y : E => 1 / ‖y‖) (closure (Ω \ Metric.closedBall (0 : E) ε)) :=
  have h_bound : ∀ y ∈ closure (Ω \ Metric.closedBall 0 ε), ε ≤ ‖y‖ := fun y hy ↦
    closure_minimal (fun x hx ↦ le_of_lt (not_le.mp fun h ↦ hx.2 (by rwa [Metric.mem_closedBall, dist_zero_right])))
      (isClosed_le continuous_const continuous_norm) hy
  contDiffOn_const.div
    (ContDiffOn.norm ℝ contDiffOn_id (fun y hy ↦ norm_pos_iff.mp (lt_of_lt_of_le hε (h_bound y hy))))
    (fun y hy ↦ ne_of_gt (lt_of_lt_of_le hε (h_bound y hy)))

lemma fderiv_norm_eq (x : E) (hx : x ≠ 0) :
    fderiv ℝ (fun y : E => ‖y‖) x = (1 / ‖x‖) • (InnerProductSpace.toDual ℝ E x) := by
  have h_comp := (hasDerivAt_sqrt (by positivity)).hasFDerivAt.comp x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  rw [show (fun y : E => ‖y‖) = Real.sqrt ∘ fun y => ‖y‖ ^ 2 from
    funext fun y => (Real.sqrt_sq (norm_nonneg y)).symm, h_comp.fderiv]
  ext y; simp [Real.sqrt_sq (norm_nonneg x)]; field_simp

lemma fderiv_inv_norm (x : E) (hx : x ≠ 0) :
  fderiv ℝ (fun y : E => 1 / ‖y‖) x = (-(1 / ‖x‖^3)) • (InnerProductSpace.toDual ℝ E x) := by
  simp_rw [one_div]
  refine ((hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x
    (fderiv_norm_eq x hx ▸ ((contDiffAt_norm ℝ hx).differentiableAt (by exact ne_zero_of_eq_one rfl)).hasFDerivAt)).fderiv.trans ?_
  ext v;simp;field_simp

lemma gradient_inv_norm (x : E) (hx : x ≠ 0) :
    gradient (fun y : E => 1 / ‖y‖) x = -(1 / ‖x‖^3) • x := by
  rw [gradient,fderiv_inv_norm x hx]
  simp

lemma inner_gradient_inv_norm_sphere_normal {x : E} {ε : ℝ} (hε : 0 < ε) (hx : ‖x‖ = ε) :
    ⟪gradient (fun y => 1 / ‖y‖) x, -(1 / ε) • x⟫_ℝ = 1 / ε^2 := by
  rw [gradient_inv_norm x (by rintro rfl; rw [norm_zero] at hx; linarith), hx, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hx]
  field_simp [hε.ne.symm]

lemma fderiv_smul_inv_norm_cubed (x : E) (hx : x ≠ 0) :
  fderiv ℝ (fun y : E => -(1 / ‖y‖^3) • y) x =
  -(1 / ‖x‖^3) • ContinuousLinearMap.id ℝ E +
  (3 / ‖x‖^5) • (ContinuousLinearMap.smulRight (InnerProductSpace.toDual ℝ E x) x) := by
  simp_rw [one_div]
  refine ((((hasDerivAt_pow 3 ‖x‖).inv (pow_ne_zero 3 (norm_ne_zero_iff.mpr hx))).neg.comp_hasFDerivAt x
    (fderiv_norm_eq x hx ▸ ((contDiffAt_norm ℝ hx).differentiableAt (by exact ne_zero_of_eq_one rfl)).hasFDerivAt)).smul
    (hasFDerivAt_id x)).fderiv.trans ?_
  ext v
  simp;field_simp

lemma div_field_neg_inv_norm_cubed (x : E) (hx : x ≠ 0) :
    div_field (fun y : E => -(1 / ‖y‖^3) • y) x = 0 := by
  unfold div_field; rw [fderiv_smul_inv_norm_cubed x hx]
  simp; field_simp; ring

lemma laplacian_inv_norm_eq_zero {x : E} (hx : x ≠ 0) :
  laplacian (fun y : E => 1 / ‖y‖) x = 0 := by
  rw [laplacian,div_field_congr (Filter.eventually_of_mem (isOpen_ne.mem_nhds hx) gradient_inv_norm)]
  exact div_field_neg_inv_norm_cubed x hx

lemma gradient_inv_norm_shift (x₀ x : E) :
  gradient (fun y => 1 / ‖y - x₀‖) x = gradient (fun y => 1 / ‖y‖) (x - x₀) := by
  simp only [one_div]
  unfold gradient
  have h_fderiv : fderiv ℝ (fun y => ‖y - x₀‖⁻¹) x = fderiv ℝ (fun y => ‖y‖⁻¹) (x - x₀) :=
    fderiv_comp_sub (𝕜 := ℝ) (f := fun z => ‖z‖⁻¹) x₀
  rw [h_fderiv]

lemma inner_gradient_inv_norm_sphere_normal_shifted (x₀ : E) (ε : ℝ) (hε : 0 < ε) (x : E) (hx : x ∈ Metric.sphere x₀ ε) :
  ⟪gradient (fun y => 1 / ‖y - x₀‖) x, -(1 / ε) • (x - x₀)⟫_ℝ = 1 / ε^2 := by
  have hx_norm : ‖x - x₀‖ = ε := by
    have h_dist := Metric.mem_sphere.mp hx
    rw [dist_eq_norm] at h_dist
    exact h_dist
  rw [gradient_inv_norm_shift x₀ x]
  exact inner_gradient_inv_norm_sphere_normal hε hx_norm

lemma differentiableAt_inv_norm_sub {x₀ x : E} (h_ne : x - x₀ ≠ 0) :
  DifferentiableAt ℝ (fun y => 1 / ‖y - x₀‖) x := by
  have h_norm := (differentiableAt_id.sub (differentiableAt_const x₀)).norm ℝ h_ne
  exact DifferentiableAt.const_mul (DifferentiableAt.fun_inv h_norm (fun h => h_ne (norm_eq_zero.mp h))) 1

lemma gradient_const_mul_inv_norm (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε) (x : E) (hx : x ∈ Metric.sphere x₀ ε) :
  gradient (fun y => (-1 / (4 * Real.pi)) * (1 / ‖y - x₀‖)) x = (-1 / (4 * Real.pi)) • gradient (fun y => 1 / ‖y - x₀‖) x := by
  unfold gradient
  change (toDual ℝ E).symm (fderiv ℝ ((-1 / (4 * Real.pi)) • (fun y => 1 / ‖y - x₀‖)) x) = _
  rw [fderiv_const_smul (differentiableAt_inv_norm_sub (fun h => hε_pos.ne' (by rw [Metric.mem_sphere, dist_eq_norm, h, norm_zero] at hx; exact hx.symm))), map_smul]

lemma gradient_inv_norm_shift_eventuallyEq (x₀ x : E) (hx_ne_x0 : x ≠ x₀) :
    ∀ᶠ y in 𝓝 x, gradient (fun z => 1 / ‖z - x₀‖) y = gradient (fun z => 1 / ‖z‖) (y - x₀) := by
  filter_upwards [eventually_ne_nhds hx_ne_x0] with y _
  simp only [gradient, one_div, EmbeddingLike.apply_eq_iff_eq]
  exact fderiv_comp_sub (𝕜 := ℝ) (f := fun z => ‖z‖⁻¹) x₀

lemma laplacian_inv_norm_shift (x₀ x : E) (hx_ne_x0 : x ≠ x₀) :
    laplacian (fun y => 1 / ‖y - x₀‖) x = laplacian (fun y => 1 / ‖y‖) (x - x₀) := by
  unfold laplacian div_field
  rw [Filter.EventuallyEq.fderiv_eq (gradient_inv_norm_shift_eventuallyEq x₀ x hx_ne_x0), fderiv_comp_sub (𝕜 := ℝ) (f := gradient (fun z => 1 / ‖z‖)) x₀]

lemma contDiffAt_inv_norm_sub (x₀ x : E) (hx_ne_x0 : x ≠ x₀) :
    ContDiffAt ℝ 2 (fun y => 1 / ‖y - x₀‖) x :=
  contDiffAt_const.div
    ((contDiffAt_norm ℝ (sub_ne_zero.mpr hx_ne_x0)).comp x (contDiffAt_id.sub contDiffAt_const))
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx_ne_x0))

/-!
### Punctured Domains
-/

lemma gradientWithin_eq_gradient_sphere_phi (φ : E → ℝ) (h_smooth : ContDiff ℝ ⊤ φ)
  (Ω : Set E) [HasPDEDomain Ω] (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall (0 : E) ε ⊆ Ω)
  (x : E) (hx : x ∈ Metric.sphere (0 : E) ε) :
  gradientWithin φ (closure (Ω \ Metric.closedBall (0 : E) ε)) x = gradient φ x := by
  apply gradientWithin_eq_gradient_of_differentiableAt
  · exact h_smooth.differentiable (by exact WithTop.top_ne_zero) x
  · exact uniqueDiffWithinAt_closure_annulus Ω (x₀ := 0) ε hε x h_subset hx

lemma gradientWithin_eq_gradient_sphere_inv_norm (Ω : Set E) [HasPDEDomain Ω] (ε : ℝ) (hε : 0 < ε)
  (h_subset : Metric.closedBall (0 : E) ε ⊆ Ω)
  (x : E) (hx : x ∈ Metric.sphere (0 : E) ε) :
  gradientWithin (fun y : E => 1 / ‖y‖) (closure (Ω \ Metric.closedBall (0 : E) ε)) x = gradient (fun y : E => 1 / ‖y‖) x := by
  apply gradientWithin_eq_gradient_of_differentiableAt
  · simp_rw [one_div]
    apply DifferentiableAt.inv
    · exact DifferentiableAt.norm ℝ (by exact differentiableAt_id) (by exact norm_ne_zero_iff.mp (by linarith[mem_sphere_zero_iff_norm.mp hx]))
    · exact by linarith[mem_sphere_zero_iff_norm.mp hx]
  · exact uniqueDiffWithinAt_closure_annulus Ω (x₀ := 0) ε hε x h_subset hx

lemma gradientWithin_excised_eq (Ω : Set E) [HasPDEDomain Ω] (u : E → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω)) (x₀ x : E)
  (ε : ℝ) (hε_pos : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (hx : x ∈ Metric.sphere x₀ ε) :
  gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x = gradientWithin u (closure Ω) x := by
  have h_diff : DifferentiableAt ℝ u x := (hu_diff.differentiableOn (by decide)).differentiableAt
    (Filter.mem_of_superset (IsOpen.mem_nhds HasPDEDomain.is_open (h_subset (Metric.sphere_subset_closedBall hx))) subset_closure)
  rw [gradientWithin_eq_gradient_of_differentiableAt u _ x h_diff (uniqueDiffWithinAt_closure_annulus Ω x₀ ε hε_pos x h_subset hx)]
  exact (gradientWithin_eq_gradient_of_differentiableAt u _ x h_diff (HasPDEDomain.unique_diff x (subset_closure (h_subset (Metric.sphere_subset_closedBall hx))))).symm

lemma continuousOn_gradientWithin_inner_sub (Ω : Set E) [HasPDEDomain Ω]
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (x₀ : E) (ε₀ : ℝ) (h_ball_subset : Metric.ball x₀ ε₀ ⊆ Ω) :
  ContinuousOn (fun x => ⟪gradientWithin u (closure Ω) x, x - x₀⟫) (Metric.ball x₀ ε₀) := by
  exact ((contDiffOn_gradientWithin u (closure Ω) HasPDEDomain.unique_diff hu_diff).continuousOn.mono
    (Subset.trans h_ball_subset subset_closure)).inner (continuous_id.sub continuous_const).continuousOn

lemma eventually_gradientWithin_excised_eq_sphere (Ω : Set E) [HasPDEDomain Ω]
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (x₀ : E) (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) (h_ball_subset : Metric.ball x₀ ε₀ ⊆ Ω) :
  ∀ᶠ ε in 𝓝[>] 0, ∀ x ∈ Metric.sphere x₀ ε,
    gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x = gradientWithin u (closure Ω) x := by
  filter_upwards [Ico_mem_nhdsGT hε₀_pos, self_mem_nhdsWithin] with ε hε hε_pos x hx
  exact gradientWithin_excised_eq Ω u hu_diff x₀ x ε hε_pos (Subset.trans (Metric.closedBall_subset_ball hε.2) h_ball_subset) hx

lemma u_continuousOn_ball (Ω : Set E) [HasPDEDomain Ω] (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (x₀ : E) (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) (h_subset : Metric.ball x₀ ε₀ ⊆ Ω) :
  ∃ R₀ > 0, ContinuousOn u (Metric.ball x₀ R₀) := by
  exact ⟨ε₀, hε₀_pos, hu_diff.continuousOn.mono (h_subset.trans subset_closure)⟩

lemma continuousOn_gradientWithin_excised_sphere (Ω : Set E) [HasPDEDomain Ω] (u : E → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (closure Ω)) (x₀ : E) (ε : ℝ) (hε : 0 < ε)
  (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  ContinuousOn (fun x => gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x) (Metric.sphere x₀ ε) := by
  exact (continuousOn_gradientWithin (annulus_has_pde_domain Ω x₀ ε hε h_subset).unique_diff
    (hu_diff.mono (closure_mono Set.sdiff_subset))).mono
    (sphere_subset_closure_excised Ω x₀ ε hε HasPDEDomain.is_open h_subset)

lemma gradientWithin_frontier_excised_eq (Ω : Set E) [HasPDEDomain Ω] (u : E → ℝ)
  (x₀ x : E) (ε : ℝ) (h_disj : x ∉ Metric.closedBall x₀ ε) :
  gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x = gradientWithin u (closure Ω) x := by
  unfold gradientWithin
  rw [fderivWithin_congr_set (eventuallyEq_closure_diff_closedBall Ω x₀ x ε h_disj)]

lemma gradientWithin_Phi_frontier_excised_eq (Ω : Set E) [HasPDEDomain Ω] (x₀ : E) (x : E) (ε : ℝ)
  (hx_not_mem : x ∉ Metric.closedBall x₀ ε) (Φ : E → ℝ):
  gradientWithin (fun y => Φ (y - x₀)) (closure (Ω \ Metric.closedBall x₀ ε)) x =
  gradientWithin (fun y => Φ (y - x₀)) (closure Ω) x :=
  gradientWithin_frontier_excised_eq Ω (fun y => Φ (y - x₀)) x₀ x ε hx_not_mem

lemma eqOn_gradientWithin_excised_frontier {Ω : Set E} [HasPDEDomain Ω]
    {G : E → E → ℝ} {x₀ : E} {ε : ℝ} (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
    Set.EqOn (fun x => gradientWithin (fun y => G y x₀) (closure (Ω \ Metric.closedBall x₀ ε)) x)
      (fun x => gradientWithin (fun y => G y x₀) (closure Ω) x) (frontier Ω) :=
  fun x hx => gradientWithin_frontier_excised_eq Ω (fun y => G y x₀) x₀ x ε
    fun h_mem => hx.2 ((HasPDEDomain.is_open (s := Ω)).interior_eq.symm ▸ h_subset h_mem)

lemma continuousOn_gradientWithin_u_sphere {Ω : Set E} [HasPDEDomain Ω]
  {u : E → ℝ} {x₀ : E} {ε : ℝ}
  (hu_C1 : ContDiffOn ℝ 1 u Ω)
  (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  ContinuousOn (fun x => gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x) (Metric.sphere x₀ ε) := by
  have h_sphere_subset_Ω : Metric.sphere x₀ ε ⊆ Ω := fun x hx => h_subset (Metric.sphere_subset_closedBall hx)
  have h_grad_cont_Ω : ContinuousOn (fun x => gradient u x) Ω :=
    continuousOn_gradient_of_contDiffOn HasPDEDomain.is_open u hu_C1
  have h_grad_cont_sphere : ContinuousOn (fun x => gradient u x) (Metric.sphere x₀ ε) :=
    h_grad_cont_Ω.mono h_sphere_subset_Ω
  have h_grad_eq : EqOn (fun x => gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x) (fun x => gradient u x) (Metric.sphere x₀ ε) := by
    intro x hx
    have h_in_Ω : x ∈ Ω := h_sphere_subset_Ω hx
    have h_open_Ω : IsOpen Ω := HasPDEDomain.is_open
    have h_diff_on : DifferentiableOn ℝ u Ω := ContDiffOn.differentiableOn_one hu_C1
    have h_diff_at : DifferentiableAt ℝ u x := h_diff_on.differentiableAt (h_open_Ω.mem_nhds h_in_Ω)
    have h_mem_closure : x ∈ closure (Ω \ Metric.closedBall x₀ ε) := by
      have h_in_sphere : x ∈ Metric.sphere x₀ ε := hx
      have h_sphere_subset_closure_compl : Metric.sphere x₀ ε ⊆ closure (Metric.closedBall x₀ ε)ᶜ := by
        intro y hy
        have h_dist_eq : dist y x₀ = ε := hy
        have h_not_lt : ¬ dist y x₀ < ε := by rw [h_dist_eq]; exact lt_irrefl ε
        have h_notin_ball : y ∉ Metric.ball x₀ ε := h_not_lt
        have h_interior_eq : interior (Metric.closedBall x₀ ε) = Metric.ball x₀ ε := interior_closedBall' x₀ ε
        have h_closure_compl : closure (Metric.closedBall x₀ ε)ᶜ = (interior (Metric.closedBall x₀ ε))ᶜ := closure_compl
        have h_notin_interior : y ∉ interior (Metric.closedBall x₀ ε) := by rw [h_interior_eq]; exact h_notin_ball
        exact h_closure_compl.symm ▸ h_notin_interior
      have h_closure_inter : closure (Metric.closedBall x₀ ε)ᶜ ∩ Ω ⊆ closure (Ω \ Metric.closedBall x₀ ε) := by
        intro y hy
        have h_y_in_closure : y ∈ closure (Metric.closedBall x₀ ε)ᶜ := hy.1
        have h_y_in_Ω : y ∈ Ω := hy.2
        have h_open_Ω : IsOpen Ω := HasPDEDomain.is_open
        have h_inter_subset : Ω ∩ closure (Metric.closedBall x₀ ε)ᶜ ⊆ closure (Ω ∩ (Metric.closedBall x₀ ε)ᶜ) := by
          (expose_names; exact IsOpen.inter_closure h_open_Ω_1)
        have h_in_closure_inter : y ∈ closure (Ω ∩ (Metric.closedBall x₀ ε)ᶜ) := h_inter_subset ⟨h_y_in_Ω, h_y_in_closure⟩
        have h_diff_eq : closure (Ω ∩ (Metric.closedBall x₀ ε)ᶜ) = closure (Ω \ Metric.closedBall x₀ ε) := rfl
        exact h_diff_eq ▸ h_in_closure_inter
      exact h_closure_inter ⟨h_sphere_subset_closure_compl h_in_sphere, h_in_Ω⟩
    have h_unique_diff : UniqueDiffWithinAt ℝ (closure (Ω \ Metric.closedBall x₀ ε)) x :=
      (annulus_has_pde_domain Ω x₀ ε hε h_subset).unique_diff x h_mem_closure
    exact gradientWithin_eq_gradient_of_differentiableAt u (closure (Ω \ closedBall x₀ ε)) x h_diff_at h_unique_diff
  exact h_grad_cont_sphere.congr h_grad_eq

lemma continuousOn_gradientWithin_H_sphere {Ω : Set E} [HasPDEDomain Ω]
  {x₀ : E} {ε : ℝ} (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  (H : E → ℝ) (hH_C1 : ContDiffOn ℝ 1 H Ω) :
  ContinuousOn (fun x => gradientWithin H (closure (Ω \ Metric.closedBall x₀ ε)) x) (Metric.sphere x₀ ε) := by
  exact (((InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
    (hH_C1.continuousOn_fderiv_of_isOpen HasPDEDomain.is_open le_rfl)).mono
    (fun x hx => h_subset (Metric.sphere_subset_closedBall hx))).congr (fun x hx =>
      gradientWithin_eq_gradient_of_differentiableAt H (closure (Ω \ Metric.closedBall x₀ ε)) x
        (hH_C1.differentiableOn_one.differentiableAt (HasPDEDomain.is_open.mem_nhds (h_subset (Metric.sphere_subset_closedBall hx))))
        ((annulus_has_pde_domain Ω x₀ ε hε h_subset).unique_diff x (mem_closure_annulus_of_mem_sphere hε h_subset hx)))

lemma gradientWithin_excised_eq_gradient {Ω : Set E} [HasPDEDomain Ω]
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  {x₀ : E} {ε : ℝ} (hε_pos : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  {x : E} (hx : x ∈ Metric.sphere x₀ ε) :
  gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x = gradient u x := by
  have h_diff_at : DifferentiableAt ℝ u x :=
    differentiableAt_of_contDiffOn_closure u hu_diff (h_subset (Metric.sphere_subset_closedBall hx))
  unfold gradientWithin gradient
  rw [fderivWithin_eq_fderiv (uniqueDiffWithinAt_closure_annulus Ω x₀ ε hε_pos x h_subset hx) h_diff_at]

lemma continuousOn_gradient {Ω : Set E} [HasPDEDomain Ω]
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω)) :
  ContinuousOn (gradient u) Ω := by
  exact ContinuousOn.congr
    ((LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E).symm).comp_continuousOn
      ((hu_diff.mono subset_closure).continuousOn_fderivWithin HasPDEDomain.is_open.uniqueDiffOn (by norm_num)))
    (eqOn_gradient_fderivWithin HasPDEDomain.is_open u)

lemma exists_norm_gradient_bound_closedBall {Ω : Set E} [HasPDEDomain Ω]
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (x₀ : E) (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω) :
  ∃ M₁ : ℝ, ∀ y ∈ Metric.closedBall x₀ ε₀, ‖gradient u y‖ ≤ M₁ := by
  obtain ⟨x_max, _, h_max_on⟩ := (isCompact_closedBall x₀ ε₀).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr hε₀_pos.le)
    (ContinuousOn.norm ((continuousOn_gradient u hu_diff).mono h_ball_subset))
  exact ⟨‖gradient u x_max‖, h_max_on⟩

lemma norm_gradientWithin_bound_sphere {Ω : Set E} [HasPDEDomain Ω]
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (x₀ : E) (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω) :
  ∃ M₁ : ℝ, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ x ∈ Metric.sphere x₀ ε,
    ‖gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x‖ ≤ M₁ := by
  obtain ⟨M₁, hM₁_bound⟩ := exists_norm_gradient_bound_closedBall u hu_diff x₀ ε₀ hε₀_pos h_ball_subset
  exact ⟨M₁, fun ε hε x hx => by
    rw [gradientWithin_excised_eq_gradient u hu_diff hε.1 ((Metric.closedBall_subset_closedBall hε.2).trans h_ball_subset) hx]
    exact hM₁_bound x (Metric.closedBall_subset_closedBall hε.2 (Metric.sphere_subset_closedBall hx))⟩

lemma gradient_inner_normal_bound (Ω : Set E) [HasPDEDomain Ω]
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 2 u (closure Ω))
  (n : E → E) (hn_cont : ContinuousOn n (closure Ω))
  (x₀ : E) (hx₀ : x₀ ∈ Ω) :
  ∃ (M : ℝ) (ε₀ : ℝ), 0 < ε₀ ∧ ∀ ε ∈ Set.Ioc 0 ε₀,
    ∀ x ∈ Metric.sphere x₀ ε, ‖⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ‖ ≤ M := by
  obtain ⟨ε₀, hε₀_pos, h_ball_subset⟩ := exists_pos_closedBall_subset_of_isOpen HasPDEDomain.is_open hx₀
  obtain ⟨M₁, hM₁⟩ := norm_gradientWithin_bound_sphere u hu_diff x₀ ε₀ hε₀_pos h_ball_subset
  obtain ⟨M₂, hM₂⟩ := norm_continuous_bound_sphere n hn_cont x₀ ε₀ hε₀_pos h_ball_subset
  exact ⟨M₁ * M₂, ε₀, hε₀_pos, fun ε hε x hx =>
    (norm_inner_le_norm (gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x) (n x)).trans
      (mul_le_mul (hM₁ ε hε x hx) (hM₂ ε hε x hx) (norm_nonneg _) ((norm_nonneg _).trans (hM₁ ε hε x hx)))⟩

lemma integrand_pointwise_bound {Ω : Set E} (G : E → E → ℝ) (u : E → ℝ) (n : E → E) (x₀ x : E) (ε C M : ℝ)
  (h_G : ‖G x x₀‖ ≤ C / ε)
  (h_grad : ‖⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ‖ ≤ M) :
  ‖G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ‖ ≤ (C * M) / ε := by
  calc
    ‖G x x₀ * ⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ‖ = ‖G x x₀‖ * ‖⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, n x⟫_ℝ‖ := norm_mul _ _
    _ ≤ (C / ε) * M := mul_le_mul h_G h_grad (norm_nonneg _) ((norm_nonneg _).trans h_G)
    _ = (C * M) / ε := by ring

lemma continuousOn_gradientWithin_H_excised (Ω : Set E) [HasPDEDomain Ω]
  (H : E → ℝ) (x₀ : E) (ε ε₀ : ℝ) (hε : ε ∈ Set.Ioc 0 ε₀) (h_ball_subset_hyp : Metric.closedBall x₀ ε₀ ⊆ Ω)
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω)) :
  ContinuousOn (fun x => gradientWithin H (closure (Ω \ Metric.closedBall x₀ ε)) x) (closure (Ω \ Metric.closedBall x₀ ε)) :=
  continuousOn_gradientWithin_of_contDiffOn
    (annulus_has_pde_domain Ω x₀ ε hε.1 ((Metric.closedBall_subset_closedBall hε.2).trans h_ball_subset_hyp)).unique_diff
    H ((hH_diff.of_le (by norm_num)).mono (closure_mono Set.sdiff_subset))

lemma continuousOn_gradientWithin_H_closure (Ω : Set E) [HasPDEDomain Ω]
  (H : E → ℝ) (hH_diff : ContDiffOn ℝ 1 H (closure Ω)) :
  ContinuousOn (fun x => gradientWithin (fun y => H y) (closure Ω) x) (closure Ω) :=
  continuousOn_gradientWithin_of_contDiffOn HasPDEDomain.unique_diff H (hH_diff.of_le (by norm_num))

lemma exists_H_grad_bound (Ω : Set E) [HasPDEDomain Ω]
  (H u : E → ℝ) (x₀ : E) (ε₀ : ℝ)
  (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω)
  (hu_cont : ContinuousOn u (closure Ω))
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω)) :
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Metric.closedBall x₀ ε₀, ‖u x‖ * ‖gradientWithin (fun y => H y) (closure Ω) x‖ ≤ M := by
  have h_cont : ContinuousOn (fun x => ‖u x‖ * ‖gradientWithin (fun y => H y) (closure Ω) x‖) (Metric.closedBall x₀ ε₀) :=
    (ContinuousOn.norm (hu_cont.mono (h_ball_subset.trans subset_closure))).mul
      (ContinuousOn.norm ((continuousOn_gradientWithin_H_closure Ω H hH_diff).mono (h_ball_subset.trans subset_closure)))
  obtain ⟨M', hM'⟩ := (isCompact_closedBall x₀ ε₀).bddAbove_image h_cont
  exact ⟨max 0 M', le_max_left 0 M', fun x hx => (hM' (Set.mem_image_of_mem _ hx)).trans (le_max_right 0 M')⟩

lemma gradientWithin_subset_excised (Ω : Set E) [HasPDEDomain Ω]
  (H : E → ℝ) (x₀ : E) (ε ε₀ : ℝ) (hε : ε ∈ Set.Ioc 0 ε₀)
  (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω)
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω)) (x : E) (hx : x ∈ Metric.sphere x₀ ε) :
  gradientWithin H (closure (Ω \ Metric.closedBall x₀ ε)) x = gradientWithin H (closure Ω) x := by
  unfold gradientWithin
  rw [fderivWithin_subset (closure_mono Set.sdiff_subset)
    ((annulus_has_pde_domain Ω x₀ ε hε.1 ((Metric.closedBall_subset_closedBall hε.2).trans h_ball_subset)).unique_diff x (sphere_subset_closure_annulus Ω x₀ ε ε₀ hε h_ball_subset hx))
    (hH_diff.differentiableOn (by norm_num) x (subset_closure (h_ball_subset (Metric.closedBall_subset_closedBall hε.2 (Metric.sphere_subset_closedBall hx)))))]

lemma pointwise_H_grad_bound (Ω : Set E) [HasPDEDomain Ω]
  (H u : E → ℝ) (x₀ : E) (ε ε₀ : ℝ)
  (hε : ε ∈ Set.Ioc 0 ε₀)
  (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω)
  (hH_diff : ContDiffOn ℝ 1 H (closure Ω))
  (M : ℝ)
  (hM_bound : ∀ x ∈ Metric.closedBall x₀ ε₀, ‖u x‖ * ‖gradientWithin (fun y => H y) (closure Ω) x‖ ≤ M)
  (x : E) (hx : x ∈ Metric.sphere x₀ ε) :
  ‖u x * ⟪gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ‖ ≤ M := by
  calc
    ‖u x * ⟪gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ‖
      = ‖u x‖ * ‖⟪gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ‖ := norm_mul _ _
    _ ≤ ‖u x‖ * (‖gradientWithin (fun y => H y) (closure (Ω \ Metric.closedBall x₀ ε)) x‖ * ‖-(1 / ε) • (x - x₀)‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
    _ = ‖u x‖ * ‖gradientWithin (fun y => H y) (closure Ω) x‖ := by
        rw [norm_smul_inv_radius_sub x₀ x ε hε.1 hx, mul_one, gradientWithin_subset_excised Ω H x₀ ε ε₀ hε h_ball_subset hH_diff x hx]
    _ ≤ M := hM_bound x (Metric.closedBall_subset_closedBall hε.2 (Metric.sphere_subset_closedBall hx))

lemma exists_bound_gradient_u_sphere
  (Ω : Set E) [HasPDEDomain Ω]
  (u : E → ℝ) (hu_diff : ContDiffOn ℝ 1 u (closure Ω))
  (x₀ : E) (ε₀ : ℝ) (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω)
  (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) ε₀) :
  ∃ M : ℝ, ∀ x ∈ Metric.sphere x₀ ε, ‖⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ‖ ≤ M := by
  have h_cont_grad_u := (continuousOn_gradientWithin_H_excised Ω u x₀ ε ε₀ hε h_ball_subset hu_diff).mono
    (sphere_subset_closure_annulus Ω x₀ ε ε₀ hε h_ball_subset)
  have h_cont_normal : ContinuousOn (fun x => -(1 / ε) • (x - x₀)) (Metric.sphere x₀ ε) :=
    ((continuous_id.sub continuous_const).const_smul (-(1 / ε))).continuousOn
  have h_cont_inner : ContinuousOn (fun x => ‖⟪gradientWithin u (closure (Ω \ Metric.closedBall x₀ ε)) x, -(1 / ε) • (x - x₀)⟫_ℝ‖) (Metric.sphere x₀ ε) :=
    (h_cont_grad_u.inner h_cont_normal).norm
  obtain ⟨M, hM⟩ := ((isCompact_sphere x₀ ε).image_of_continuousOn h_cont_inner).bddAbove
  exact ⟨M, fun x hx => hM (Set.mem_image_of_mem _ hx)⟩

/-!
### Twice Punctured Domains
-/

lemma differentiableAt_Hb_sphere_b (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (hb_subset : Metric.closedBall b ε ⊆ Ω) (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω)
  (x : E) (hx : x ∈ Metric.sphere b ε) :
  DifferentiableAt ℝ H_b x :=
  (hHb_diff.differentiableOn (by decide)).differentiableAt (IsOpen.mem_nhds HasPDEDomain.is_open (hb_subset (Metric.sphere_subset_closedBall hx)))

lemma uniqueDiffWithinAt_punctured_sphere (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b) (h_ball_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_ball_subset : Metric.closedBall b ε ⊆ Ω)
  (x : E) (hx : x ∈ Metric.sphere a ε) :
  UniqueDiffWithinAt ℝ (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x := by
  have h_disj := disjoint_closedBall_of_dist_lt a b ε h_dist_ab
  haveI : HasPDEDomain (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) :=
    double_annulus_has_pde_domain Ω a b ε hε h_ball_subset hb_ball_subset h_disj
  exact HasPDEDomain.unique_diff x (sphere_subset_closure_punctured Ω a b ε hε h_ball_subset h_disj hx)

lemma contDiffOn_grad_Hb_ball (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (h_ball_subset : Metric.closedBall a ε ⊆ Ω) (H_b : E → ℝ)
  (hH_diff : ContDiffOn ℝ 2 H_b Ω) :
  ContDiffOn ℝ 1 (gradient H_b) (closure (Metric.ball a ε)) := by
  intro y hy
  have hy_Omega : y ∈ Ω := h_ball_subset (closure_minimal Metric.ball_subset_closedBall isClosed_closedBall hy)
  let c : (E →L[ℝ] ℝ) →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact (ContDiffAt.continuousLinearMap_comp c ((hH_diff.contDiffAt (IsOpen.mem_nhds HasPDEDomain.is_open hy_Omega)).fderiv_right le_rfl)).contDiffWithinAt

lemma differentiableAt_Ha_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω)
  (x : E) (hx : x ∈ Metric.sphere a ε) :
  DifferentiableAt ℝ H_a x :=
  (hHa_diff.differentiableOn (by decide)).differentiableAt (IsOpen.mem_nhds HasPDEDomain.is_open (ha_subset (Metric.sphere_subset_closedBall hx)))

lemma contDiffOn_v_smul_grad_Ha_ball (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (v : E → ℝ)
  (H_a : E → ℝ)
  (hv_diff : ContDiffOn ℝ 1 v (Metric.ball a ε))
  (hHa_grad_diff : ContDiffOn ℝ 1 (gradient H_a) (Metric.ball a ε)) :
  ContDiffOn ℝ 1 (fun x ↦ v x • gradient H_a x) (Metric.ball a ε) := by
  exact ContDiffOn.fun_smul hv_diff hHa_grad_diff

lemma continuousOn_v_smul_gradWithin_Ha_ball (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (v : E → ℝ)
  (H_a : E → ℝ)
  (hv_cont : ContinuousOn v (closure (Metric.ball a ε)))
  (hHa_grad_cont : ContinuousOn (fun x ↦ gradientWithin H_a (closure (Metric.ball a ε)) x) (closure (Metric.ball a ε))) :
  ContinuousOn (fun x ↦ v x • gradientWithin H_a (closure (Metric.ball a ε)) x) (closure (Metric.ball a ε)) := by
  exact ContinuousOn.fun_smul hv_cont hHa_grad_cont

lemma contDiffOn_Ha_smul_grad_v_ball (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (v : E → ℝ)
  (H_a : E → ℝ)
  (hHa_diff_1 : ContDiffOn ℝ 1 H_a (Metric.ball a ε))
  (hv_grad_diff : ContDiffOn ℝ 1 (gradient v) (Metric.ball a ε)) :
  ContDiffOn ℝ 1 (fun x ↦ H_a x • gradient v x) (Metric.ball a ε) := by
  exact contDiffOn_v_smul_grad_Ha_ball Ω a ε H_a v hHa_diff_1 hv_grad_diff

lemma continuousOn_Ha_smul_gradWithin_v_ball (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (v : E → ℝ)
  (H_a : E → ℝ)
  (hHa_cont : ContinuousOn H_a (closure (Metric.ball a ε)))
  (hv_grad_cont : ContinuousOn (fun x ↦ gradientWithin v (closure (Metric.ball a ε)) x) (closure (Metric.ball a ε))) :
  ContinuousOn (fun x ↦ H_a x • gradientWithin v (closure (Metric.ball a ε)) x) (closure (Metric.ball a ε)) := by
  exact continuousOn_v_smul_gradWithin_Ha_ball Ω a ε H_a v hHa_cont hv_grad_cont

lemma gradientWithin_Ha_eq_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω)
  (x : E) (hx : x ∈ Metric.sphere a ε) :
  gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x =
  gradientWithin H_a (closure (Metric.ball a ε)) x := by
  have h_diff_Ha : DifferentiableAt ℝ H_a x := (hHa_diff.differentiableOn (by decide)).differentiableAt (IsOpen.mem_nhds HasPDEDomain.is_open (ha_subset (Metric.sphere_subset_closedBall hx)))
  haveI : HasPDEDomain (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) := double_annulus_has_pde_domain Ω a b ε hε ha_subset hb_subset h_disjoint
  haveI : HasPDEDomain (Metric.ball a ε) := instHasPDEDomainBall a ε hε
  rw [gradientWithin_eq_gradient_of_differentiableAt H_a _ x h_diff_Ha (HasPDEDomain.unique_diff x (sphere_a_subset_closure Ω a b ε hε ha_subset h_disjoint hx)),
      gradientWithin_eq_gradient_of_differentiableAt H_a _ x h_diff_Ha (HasPDEDomain.unique_diff x (by rw [closure_ball a (ne_of_gt hε)]; exact Metric.sphere_subset_closedBall hx))]

lemma integrand_eq_sphere_a_ball_flux (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (v H_a : E → ℝ) (n n_ball : E → E)
  (h_n_eq : ∀ x ∈ Metric.sphere a ε, n x = -n_ball x)
  (h_grad_v_eq : ∀ x ∈ Metric.sphere a ε, gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x = gradientWithin v (closure (Metric.ball a ε)) x)
  (h_grad_Ha_eq : ∀ x ∈ Metric.sphere a ε, gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x = gradientWithin H_a (closure (Metric.ball a ε)) x) :
  Set.EqOn
    (fun x ↦ H_a x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ)
    (fun x ↦ - (H_a x * ⟪gradientWithin v (closure (Metric.ball a ε)) x, n_ball x⟫_ℝ - v x * ⟪gradientWithin H_a (closure (Metric.ball a ε)) x, n_ball x⟫_ℝ))
    (Metric.sphere a ε) := by
  intro x hx
  simp_rw [h_n_eq x hx, h_grad_v_eq x hx, h_grad_Ha_eq x hx, inner_neg_right]
  ring

lemma laplacianWithin_eq_laplacian_ball_a (a : E) (ε : ℝ) (v H_a : E → ℝ) :
  Set.EqOn (fun x ↦ H_a x * laplacianWithin v (closure (Metric.ball a ε)) x - v x * laplacianWithin H_a (closure (Metric.ball a ε)) x)
    (fun x ↦ H_a x * laplacian v x - v x * laplacian H_a x) (Metric.ball a ε) := by
  intro x hx
  simp_rw [laplacianWithin_closure_eq_laplacian v (Metric.ball a ε) isOpen_ball x hx,
      laplacianWithin_closure_eq_laplacian H_a (Metric.ball a ε) isOpen_ball x hx]

lemma hHa_diff_1 (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ) (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω) : ContDiffOn ℝ 1 H_a (Metric.ball a ε) :=
  contDiffOn_1_ball_of_C2_Omega Ω a ε ha_subset H_a hHa_diff

lemma hHb_diff_1 (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω) : ContDiffOn ℝ 1 H_b (Metric.ball b ε) :=
  contDiffOn_1_ball_of_C2_Omega Ω b ε hb_subset H_b hHb_diff

lemma hHa_cont_closure (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ) (hε : 0 < ε) (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω) : ContinuousOn H_a (closure (Metric.ball a ε)) :=
  continuousOn_closure_ball_of_C2_Omega Ω a ε hε ha_subset H_a hHa_diff

lemma hHb_cont_closure (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ) (hε : 0 < ε) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω) : ContinuousOn H_b (closure (Metric.ball b ε)) :=
  continuousOn_closure_ball_of_C2_Omega Ω b ε hε hb_subset H_b hHb_diff

lemma hHa_cont_sphere (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ) (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω) : ContinuousOn H_a (Metric.sphere a ε) :=
  continuousOn_sphere_of_C2_Omega Ω a ε ha_subset H_a hHa_diff

lemma hHb_cont_sphere (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω) : ContinuousOn H_b (Metric.sphere b ε) :=
  continuousOn_sphere_of_C2_Omega Ω b ε hb_subset H_b hHb_diff

lemma hHa_cont_closed (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω) :
  ContinuousOn H_a (Metric.closedBall a ε) := by
  exact hHa_diff.continuousOn.mono ha_subset

lemma hHa_cont_front (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω) :
  ContinuousOn H_a (frontier (Metric.ball a ε)) := by
  exact (hHa_cont_closed Ω a ε ha_subset H_a hHa_diff).mono (frontier_subset_closure.trans closure_ball_subset_closedBall)

lemma contDiffOn_grad_Ha_ball (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (h_ball_subset : Metric.closedBall a ε ⊆ Ω) (H_a : E → ℝ)
  (hH_diff : ContDiffOn ℝ 2 H_a Ω) :
  ContDiffOn ℝ 1 (gradient H_a) (closure (Metric.ball a ε)) := by
  intro y hy
  have hy_Omega : y ∈ Ω := h_ball_subset (closure_minimal Metric.ball_subset_closedBall isClosed_closedBall hy)
  let c : (E →L[ℝ] ℝ) →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact (ContDiffAt.continuousLinearMap_comp c ((hH_diff.contDiffAt (IsOpen.mem_nhds HasPDEDomain.is_open hy_Omega)).fderiv_right le_rfl)).contDiffWithinAt

lemma hHa_grad_diff (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω) :
  ContDiffOn ℝ 1 (gradient H_a) (Metric.ball a ε) := by
  exact (contDiffOn_grad_Ha_ball Ω a ε ha_subset H_a hHa_diff).mono subset_closure

lemma hHa_grad_cont (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω) :
  ContinuousOn (fun x ↦ gradientWithin H_a (closure (Metric.ball a ε)) x) (closure (Metric.ball a ε)) := by
  refine (contDiffOn_grad_Ha_ball Ω a ε ha_subset H_a hHa_diff).continuousOn.congr fun x hx => ?_
  unfold gradientWithin gradient
  rw [DifferentiableAt.fderivWithin ((hHa_diff.contDiffAt (HasPDEDomain.is_open.mem_nhds (ha_subset (closure_ball_subset_closedBall hx)))).differentiableAt (by decide)) ((instHasPDEDomainBall a ε hε).unique_diff x hx)]

lemma h_cont_grad_Ha (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω) :
  ContinuousOn (gradient H_a) (Metric.closedBall a ε) := by
  have h_cont_diff : ContDiffOn ℝ 1 (gradient H_a) (Metric.closedBall a ε) := fun y hy =>
    (ContDiffAt.continuousLinearMap_comp (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap ((hHa_diff.contDiffAt (HasPDEDomain.is_open.mem_nhds (ha_subset hy))).fderiv_right le_rfl)).contDiffWithinAt
  exact h_cont_diff.continuousOn

lemma h_cont_grad_Ha_front (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω) :
  ContinuousOn (fun x ↦ gradientWithin H_a (closure (Metric.ball a ε)) x) (frontier (Metric.ball a ε)) := by
  have h_front_subset : frontier (Metric.ball a ε) ⊆ closure (Metric.ball a ε) := frontier_subset_closure
  exact ContinuousOn.mono (hHa_grad_cont Ω a ε hε ha_subset H_a hHa_diff) h_front_subset

lemma h_cont_grad_Ha_sphere (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω) :
  ContinuousOn (fun x ↦ gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε) := by
  refine ((h_cont_grad_Ha Ω a ε ha_subset H_a hHa_diff).mono Metric.sphere_subset_closedBall).congr fun x hx => ?_
  unfold gradientWithin gradient
  rw [DifferentiableAt.fderivWithin ((hHa_diff.contDiffAt (HasPDEDomain.is_open.mem_nhds (ha_subset (Metric.sphere_subset_closedBall hx)))).differentiableAt (by decide)) ((double_annulus_has_pde_domain Ω a b ε hε ha_subset hb_subset h_disjoint).unique_diff x (sphere_a_subset_closure_punctured Ω a b ε hε ha_subset h_disjoint hx))]

lemma h_cont_lap_Ha (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (H_a : E → ℝ) (hHa_diff : ContDiffOn ℝ 2 H_a Ω) :
  ContinuousOn (fun x ↦ laplacianWithin H_a (closure (Metric.ball a ε)) x) (Metric.closedBall a ε) := by
  rw [closure_ball_eq_closedBall a ε hε]
  have h_ud : UniqueDiffOn ℝ (Metric.closedBall a ε) :=
    closure_ball_eq_closedBall a ε hε ▸ (instHasPDEDomainBall a ε hε).unique_diff
  exact continuous_trace.comp_continuousOn <|
    (contDiffOn_gradientWithin H_a (Metric.closedBall a ε) h_ud (hHa_diff.mono ha_subset)).continuousOn_fderivWithin h_ud le_rfl

lemma contDiffOn_u_smul_grad_Hb_ball (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (u : E → ℝ)
  (H_b : E → ℝ)
  (hu_diff : ContDiffOn ℝ 1 u (Metric.ball b ε))
  (hHb_grad_diff : ContDiffOn ℝ 1 (gradient H_b) (Metric.ball b ε)) :
  ContDiffOn ℝ 1 (fun x ↦ u x • gradient H_b x) (Metric.ball b ε) := by
  exact contDiffOn_v_smul_grad_Ha_ball Ω b ε u H_b hu_diff hHb_grad_diff

lemma continuousOn_u_smul_gradWithin_Hb_ball (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (u : E → ℝ)
  (H_b : E → ℝ)
  (hu_cont : ContinuousOn u (closure (Metric.ball b ε)))
  (hHb_grad_cont : ContinuousOn (fun x ↦ gradientWithin H_b (closure (Metric.ball b ε)) x) (closure (Metric.ball b ε))) :
  ContinuousOn (fun x ↦ u x • gradientWithin H_b (closure (Metric.ball b ε)) x) (closure (Metric.ball b ε)) := by
  exact continuousOn_v_smul_gradWithin_Ha_ball Ω b ε u H_b hu_cont hHb_grad_cont

lemma contDiffOn_Hb_smul_grad_u_ball (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (u : E → ℝ)
  (H_b : E → ℝ)
  (hHb_diff_1 : ContDiffOn ℝ 1 H_b (Metric.ball b ε))
  (hu_grad_diff : ContDiffOn ℝ 1 (gradient u) (Metric.ball b ε)) :
  ContDiffOn ℝ 1 (fun x ↦ H_b x • gradient u x) (Metric.ball b ε) := by
  exact contDiffOn_v_smul_grad_Ha_ball Ω b ε H_b u hHb_diff_1 hu_grad_diff

lemma continuousOn_Hb_smul_gradWithin_u_ball (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (u : E → ℝ)
  (H_b : E → ℝ)
  (hHb_cont : ContinuousOn H_b (closure (Metric.ball b ε)))
  (hu_grad_cont : ContinuousOn (fun x ↦ gradientWithin u (closure (Metric.ball b ε)) x) (closure (Metric.ball b ε))) :
  ContinuousOn (fun x ↦ H_b x • gradientWithin u (closure (Metric.ball b ε)) x) (closure (Metric.ball b ε)) := by
  exact continuousOn_v_smul_gradWithin_Ha_ball Ω b ε H_b u hHb_cont hu_grad_cont

lemma gradientWithin_Hb_eq_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω)
  (x : E) (hx : x ∈ Metric.sphere b ε) :
  gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x =
  gradientWithin H_b (closure (Metric.ball b ε)) x := by
  have h_diff_Hb : DifferentiableAt ℝ H_b x := (hHb_diff.differentiableOn (by decide)).differentiableAt (IsOpen.mem_nhds HasPDEDomain.is_open (hb_subset (Metric.sphere_subset_closedBall hx)))
  haveI : HasPDEDomain (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) := double_annulus_has_pde_domain Ω a b ε hε ha_subset hb_subset h_disjoint
  haveI : HasPDEDomain (Metric.ball b ε) := instHasPDEDomainBall b ε hε
  rw [gradientWithin_eq_gradient_of_differentiableAt H_b _ x h_diff_Hb (HasPDEDomain.unique_diff x (by rw [Set.union_comm]; exact sphere_a_subset_closure Ω b a ε hε hb_subset h_disjoint.symm hx)),
      gradientWithin_eq_gradient_of_differentiableAt H_b _ x h_diff_Hb (HasPDEDomain.unique_diff x (by rw [closure_ball b (ne_of_gt hε)]; exact Metric.sphere_subset_closedBall hx))]

lemma integrand_eq_sphere_b_ball_flux (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (u H_b : E → ℝ) (n n_ball : E → E)
  (h_n_eq : ∀ x ∈ Metric.sphere b ε, n x = -n_ball x)
  (h_grad_u_eq : ∀ x ∈ Metric.sphere b ε, gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x = gradientWithin u (closure (Metric.ball b ε)) x)
  (h_grad_Hb_eq : ∀ x ∈ Metric.sphere b ε, gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x = gradientWithin H_b (closure (Metric.ball b ε)) x) :
  Set.EqOn
    (fun x ↦ u x * ⟪gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - H_b x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ)
    (fun x ↦ - (u x * ⟪gradientWithin H_b (closure (Metric.ball b ε)) x, n_ball x⟫_ℝ - H_b x * ⟪gradientWithin u (closure (Metric.ball b ε)) x, n_ball x⟫_ℝ))
    (Metric.sphere b ε) := by
  intro x hx
  simp_rw [h_n_eq x hx, h_grad_u_eq x hx, h_grad_Hb_eq x hx, inner_neg_right]
  ring

lemma laplacianWithin_eq_laplacian_ball_b (b : E) (ε : ℝ) (u H_b : E → ℝ) :
  Set.EqOn (fun x ↦ u x * laplacianWithin H_b (closure (Metric.ball b ε)) x - H_b x * laplacianWithin u (closure (Metric.ball b ε)) x)
    (fun x ↦ u x * laplacian H_b x - H_b x * laplacian u x) (Metric.ball b ε) := by
  intro x hx
  simp_rw [laplacianWithin_closure_eq_laplacian u (Metric.ball b ε) isOpen_ball x hx,
      laplacianWithin_closure_eq_laplacian H_b (Metric.ball b ε) isOpen_ball x hx]

lemma hHb_cont_closed (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω) :
  ContinuousOn H_b (Metric.closedBall b ε) := by
  exact hHb_diff.continuousOn.mono hb_subset

lemma hHb_cont_front (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω) :
  ContinuousOn H_b (frontier (Metric.ball b ε)) := by
  exact (hHb_cont_closed Ω b ε hb_subset H_b hHb_diff).mono (frontier_subset_closure.trans closure_ball_subset_closedBall)

lemma hHb_grad_diff (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω) :
  ContDiffOn ℝ 1 (gradient H_b) (Metric.ball b ε) := by
  exact (contDiffOn_grad_Hb_ball Ω b ε hb_subset H_b hHb_diff).mono subset_closure

lemma hHb_grad_cont (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ) (hε : 0 < ε)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω) :
  ContinuousOn (fun x ↦ gradientWithin H_b (closure (Metric.ball b ε)) x) (closure (Metric.ball b ε)) := by
  refine (contDiffOn_grad_Hb_ball Ω b ε hb_subset H_b hHb_diff).continuousOn.congr fun x hx => ?_
  unfold gradientWithin gradient
  rw [DifferentiableAt.fderivWithin ((hHb_diff.contDiffAt (HasPDEDomain.is_open.mem_nhds (hb_subset (closure_ball_subset_closedBall hx)))).differentiableAt (by decide)) ((instHasPDEDomainBall b ε hε).unique_diff x hx)]

lemma h_cont_grad_Hb (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω) :
  ContinuousOn (gradient H_b) (Metric.closedBall b ε) := by
  have h_cont_diff : ContDiffOn ℝ 1 (gradient H_b) (Metric.closedBall b ε) := by
    intro y hy
    have hy_Omega : y ∈ Ω := hb_subset hy
    let c : (E →L[ℝ] ℝ) →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact (ContDiffAt.continuousLinearMap_comp c ((hHb_diff.contDiffAt (IsOpen.mem_nhds HasPDEDomain.is_open hy_Omega)).fderiv_right le_rfl)).contDiffWithinAt
  exact h_cont_diff.continuousOn

lemma h_cont_grad_Hb_front (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ) (hε : 0 < ε)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω) :
  ContinuousOn (fun x ↦ gradientWithin H_b (closure (Metric.ball b ε)) x) (frontier (Metric.ball b ε)) := by
  have h_front_subset : frontier (Metric.ball b ε) ⊆ closure (Metric.ball b ε) := frontier_subset_closure
  exact ContinuousOn.mono (hHb_grad_cont Ω b ε hε hb_subset H_b hHb_diff) h_front_subset

lemma h_cont_grad_Hb_sphere (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω) :
  ContinuousOn (fun x ↦ gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε) := by
  refine ((h_cont_grad_Hb Ω b ε hb_subset H_b hHb_diff).mono Metric.sphere_subset_closedBall).congr fun x hx => ?_
  unfold gradientWithin gradient
  rw [DifferentiableAt.fderivWithin ((hHb_diff.contDiffAt (HasPDEDomain.is_open.mem_nhds (hb_subset (Metric.sphere_subset_closedBall hx)))).differentiableAt (by decide)) ((double_annulus_has_pde_domain Ω a b ε hε ha_subset hb_subset h_disjoint).unique_diff x (sphere_b_subset_closure_punctured Ω a b ε hε hb_subset h_disjoint hx))]

lemma h_cont_lap_Hb (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ) (hε : 0 < ε)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (H_b : E → ℝ) (hHb_diff : ContDiffOn ℝ 2 H_b Ω) :
  ContinuousOn (fun x ↦ laplacianWithin H_b (closure (Metric.ball b ε)) x) (Metric.closedBall b ε) := by
  rw [closure_ball_eq_closedBall b ε hε]
  have h_ud : UniqueDiffOn ℝ (Metric.closedBall b ε) :=
    closure_ball_eq_closedBall b ε hε ▸ (instHasPDEDomainBall b ε hε).unique_diff
  exact continuous_trace.comp_continuousOn <|
    (contDiffOn_gradientWithin H_b (Metric.closedBall b ε) h_ud (hHb_diff.mono hb_subset)).continuousOn_fderivWithin h_ud le_rfl
