import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq

open MeasureTheory Filter InnerProductSpace Measure Set
open scoped Topology ENNReal Interval

namespace Heat

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable (α t : ℝ)

noncomputable def div_field {n : ℕ} (F : E n → E n) (x : E n) : ℝ :=
  LinearMap.trace ℝ (E n) (fderiv ℝ F x)

noncomputable def div_fieldWithin {n : ℕ} (F : E n → E n) (s : Set (E n)) (x : E n) : ℝ :=
  LinearMap.trace ℝ (E n) (fderivWithin ℝ F s x)

noncomputable def laplacianWithin {n : ℕ} (u : E n → ℝ) (s : Set (E n)) (x : E n) : ℝ :=
  div_fieldWithin (gradientWithin u s) s x

noncomputable def laplacian {n : ℕ} (u : E n → ℝ) (x : E n) : ℝ :=
  div_field (gradient u) x

noncomputable def heatKernelND {n : ℕ} (α : ℝ) (x : E n) (t : ℝ) : ℝ :=
  (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * Real.exp (-‖x‖^2 / (4 * α * t))

noncomputable def heatKND (α : ℝ) : ℝ := 4 * Real.pi * α

@[simp]
noncomputable def aND (α : ℝ) (t : ℝ) : ℝ := 1 / (4 * α * t)

@[simp]
noncomputable def cND (n : ℕ) (α : ℝ) (t : ℝ) : ℝ := 1 / (Real.sqrt ((heatKND α) * t))^n

lemma heatKND_pos {α : ℝ} (hα : α > 0) : heatKND α > 0 := by
  unfold heatKND
  positivity

lemma aND_pos {α t : ℝ} (hα : α > 0) (ht : t > 0) : aND α t > 0 := by
  unfold aND
  positivity

lemma cND_pos {n : ℕ} {α t : ℝ} (hα : α > 0) (ht : t > 0) : cND n α t > 0 := by
  unfold cND heatKND
  positivity

lemma heatKernelND_pos {n : ℕ} {x : E n} (hα : 0 < α) (ht : 0 < t) :
    0 < heatKernelND α x t := by
  unfold heatKernelND
  positivity

lemma heatKernelND_eq_const_mul_exp {n : ℕ} {α t : ℝ} (x : E n) :
    heatKernelND α x t = (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * Real.exp (-‖x‖^2 / (4 * α * t)) := by
  exact rfl

lemma integrable_exp_neg_sq : Integrable (fun x : ℝ => Real.exp (-x^2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) zero_lt_one

lemma exp_neg_norm_sq_eq_smul {n : ℕ} {α t : ℝ} (x : E n) (hα : 0 < α) (ht : 0 < t) :
    Real.exp (-‖x‖^2 / (4 * α * t)) = Real.exp (-‖(Real.sqrt (4 * α * t))⁻¹ • x‖^2) := by
  congr 1
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity),inv_pow, Real.sq_sqrt (by positivity)]
  ring

lemma integral_exp_neg_norm_sq_smul {n : ℕ} {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    ∫ x : E n, Real.exp (-‖x‖^2 / (4 * α * t)) =
      (Real.sqrt (4 * α * t))^n * ∫ u : E n, Real.exp (-‖u‖^2) := by
  have h_eq : (fun x : E n => Real.exp (-‖x‖^2 / (4 * α * t))) = fun x => Real.exp (-‖(Real.sqrt (4 * α * t))⁻¹ • x‖^2) := funext fun x => exp_neg_norm_sq_eq_smul x hα ht
  rw [h_eq]
  have h_meas := MeasureTheory.Measure.integral_comp_smul (volume : Measure (E n)) (fun u : E n => Real.exp (-‖u‖^2)) (Real.sqrt (4 * α * t))⁻¹
  change ∫ x : E n, Real.exp (-‖(Real.sqrt (4 * α * t))⁻¹ • x‖^2) = _ at h_meas
  rw [h_meas, finrank_euclideanSpace_fin]
  have h_pos : 0 < Real.sqrt (4 * α * t) := by positivity
  simp only [smul_eq_mul, abs_pow, abs_of_pos h_pos, inv_pow, inv_inv]


lemma integrable_pi_gaussian (m : ℕ) :
    Integrable (fun u : Fin m → ℝ => ∏ i : Fin m, Real.exp (-(u i)^2)) := by
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.Integrable.fintype_prod_dep (fun _ => integrable_exp_neg_sq)

lemma integrable_prod_gaussian (m : ℕ) :
    Integrable (fun p : ℝ × (Fin m → ℝ) => Real.exp (-(p.1)^2) * ∏ i : Fin m, Real.exp (-(p.2 i)^2)) ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
  exact integrable_exp_neg_sq.mul_prod (integrable_pi_gaussian m)

lemma integral_fin_succ_pi_gaussian (m : ℕ) :
    ∫ u : Fin (m + 1) → ℝ, Real.exp (-(u 0)^2) * ∏ i : Fin m, Real.exp (-(u (Fin.succ i))^2) =
    (∫ x : ℝ, Real.exp (-x^2)) * ∫ v : Fin m → ℝ, (∏ i : Fin m, Real.exp (-(v i)^2)) := by
  let h_equiv : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have h_vol_pres : MeasurePreserving h_equiv volume ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
    rw [← MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have h_integral_map : ∫ u : Fin (m + 1) → ℝ, Real.exp (-(u 0)^2) * ∏ i : Fin m, Real.exp (-(u (Fin.succ i))^2) = ∫ p : ℝ × (Fin m → ℝ), Real.exp (-(p.1)^2) * ∏ i : Fin m, Real.exp (-(p.2 i)^2) ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
    MeasurePreserving.integral_comp h_vol_pres h_equiv.measurableEmbedding (fun p => Real.exp (-(p.1)^2) * ∏ i : Fin m, Real.exp (-(p.2 i)^2))
  have h_fubini : ∫ p : ℝ × (Fin m → ℝ), Real.exp (-(p.1)^2) * ∏ i : Fin m, Real.exp (-(p.2 i)^2) ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) = ∫ x : ℝ, ∫ v : Fin m → ℝ, Real.exp (-x^2) * ∏ i : Fin m, Real.exp (-(v i)^2) := by
    exact Eq.symm (integral_integral (integrable_prod_gaussian m))
  have h_inner : (fun x : ℝ => ∫ v : Fin m → ℝ, Real.exp (-x^2) * ∏ i : Fin m, Real.exp (-(v i)^2)) = fun x : ℝ => Real.exp (-x^2) * ∫ v : Fin m → ℝ, ∏ i : Fin m, Real.exp (-(v i)^2) := by
    ext x
    rw [integral_const_mul]
  rw [h_integral_map, h_fubini, h_inner, integral_mul_const]

lemma integral_fin_pi_gaussian (n : ℕ) :
    ∫ u : Fin n → ℝ, (∏ i : Fin n, Real.exp (-(u i)^2)) = ∏ _ : Fin n, ∫ x : ℝ, Real.exp (-x^2) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    rw [integral_const, smul_eq_mul, mul_one]
    change ((Measure.pi (fun _ => volume)) Set.univ).toReal = 1
    rw [Measure.pi_univ, Finset.univ_eq_empty, Finset.prod_empty, ENNReal.toReal_one]
  | succ m ih =>
    have h_eq : (fun u : Fin (m + 1) → ℝ => ∏ i : Fin (m + 1), Real.exp (-(u i)^2)) = fun u => Real.exp (-(u 0)^2) * ∏ i : Fin m, Real.exp (-(u (Fin.succ i))^2) := funext fun u => Fin.prod_univ_succ (fun i => Real.exp (-(u i)^2))
    have h_prod_succ : (∏ i : Fin (m + 1), ∫ x : ℝ, Real.exp (-x^2)) = (∫ x : ℝ, Real.exp (-x^2)) * (∏ i : Fin m, ∫ x : ℝ, Real.exp (-x^2)) := Fin.prod_univ_succ (fun _ => ∫ x : ℝ, Real.exp (-x^2))
    rw [h_eq, integral_fin_succ_pi_gaussian m, ih, h_prod_succ]

lemma integral_gaussian_norm_euclidean {n : ℕ} :
    ∫ u : E n, Real.exp (-‖u‖^2) = (Real.sqrt Real.pi)^n := by
  have h_eq : (fun u : E n => Real.exp (-‖u‖^2)) = fun u => ∏ i : Fin n, Real.exp (-(u i)^2) := by
    ext u
    rw [← real_inner_self_eq_norm_sq]
    change Real.exp (-(∑ i : Fin n, (u i) * (u i))) = _
    simp_rw [← sq, ← Finset.sum_neg_distrib, Real.exp_sum]
  rw [h_eq]
  have h_meas_emb : MeasurableEmbedding (fun u : E n => u.ofLp) :=
    MeasurableEquiv.measurableEmbedding
      { WithLp.equiv 2 (Fin n → ℝ) with
        measurable_toFun := Continuous.measurable (by continuity)
        measurable_invFun := Continuous.measurable (by continuity) }
  change ∫ (u : E n), (fun v : Fin n → ℝ => ∏ i, Real.exp (-v i ^ 2)) u.ofLp = _
  have h_eq2 : ∫ (u : E n), (fun v : Fin n → ℝ => ∏ i, Real.exp (-v i ^ 2)) u.ofLp =
               ∫ (v : Fin n → ℝ), ∏ i, Real.exp (-v i ^ 2) ∂(Measure.map (fun u : E n => u.ofLp) volume) :=
    (MeasurableEmbedding.integral_map h_meas_emb (fun v : Fin n → ℝ => ∏ i, Real.exp (-v i ^ 2))).symm
  rw [h_eq2]
  erw [(PiLp.volume_preserving_ofLp (Fin n)).map_eq, integral_fin_pi_gaussian n]
  have h_int : ∫ x : ℝ, Real.exp (-x^2) = Real.sqrt Real.pi := by
    have h_one : (fun x : ℝ => Real.exp (-x^2)) = fun x => Real.exp (-1 * x^2) := funext fun x => by congr 1; ring
    rw [h_one, integral_gaussian 1]
    simp
  simp_rw [h_int]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma integral_heatKernelND_one_gaussian {n : ℕ} (hα : 0 < α) (ht : 0 < t) :
    ∫ x : E n, heatKernelND α x t = 1 := by
  unfold heatKernelND
  rw [integral_const_mul, integral_exp_neg_norm_sq_smul hα ht, integral_gaussian_norm_euclidean]
  have h_denom : Real.sqrt (4 * Real.pi * α * t) = Real.sqrt (4 * α * t) * Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  rw [h_denom, mul_pow]
  exact div_mul_cancel₀ 1 (ne_of_gt (by positivity))

section Derivatives

lemma deriv_sqrt_inv_pow_n {x : ℝ} {n : ℕ} (hx : x > 0) :
    HasDerivAt (fun τ => 1 / (Real.sqrt τ)^n)
                (-((n : ℝ) / (2 * x)) * (1 / (Real.sqrt x)^n)) x := by
  apply HasDerivAt.congr_deriv ((hasDerivAt_const _ (1 : ℝ)).div ((Real.hasDerivAt_sqrt (ne_of_gt hx)).pow n) (ne_of_gt (pow_pos (Real.sqrt_pos.mpr hx) n)))
  cases n with
  | zero => simp
  | succ m =>
    rw [show (m + 1 - 1 : ℕ) = m from rfl]
    simp only [Pi.pow_apply]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hx), ne_of_gt (pow_pos (Real.sqrt_pos.mpr hx) (m + 1))]
    have hx_sq : x = (Real.sqrt x)^2 := (Real.sq_sqrt (le_of_lt hx)).symm
    generalize Real.sqrt x = s at hx_sq ⊢
    rw [hx_sq]
    ring_nf


lemma hasFDerivAt_norm_sq {n : ℕ} (x : E n) :
    HasFDerivAt (fun x' : E n => ‖x'‖^2) ((2 : ℝ) • innerSL ℝ x) x := by
  rw [show (fun x' : E n => ‖x'‖^2) = fun x' => ⟪x', x'⟫_ℝ from funext fun x' => (real_inner_self_eq_norm_sq x').symm]
  apply HasFDerivAt.congr_fderiv (HasFDerivAt.inner ℝ (hasFDerivAt_id (𝕜 := ℝ) x) (hasFDerivAt_id (𝕜 := ℝ) x))
  ext v
  simp [real_inner_comm v x]
  ring

lemma hasFDerivAt_exp_neg_norm_sq {n : ℕ} {α t : ℝ} (x : E n) (ht : 0 < t) (hα : 0 < α) :
    HasFDerivAt (fun x' => Real.exp (-‖x'‖^2 / (4 * α * t)))
      ((-(1 / (2 * α * t)) * Real.exp (-‖x‖^2 / (4 * α * t))) • innerSL ℝ x) x := by
  apply HasFDerivAt.congr_fderiv (HasDerivAt.comp_hasFDerivAt x (HasDerivAt.comp (‖x‖^2) (Real.hasDerivAt_exp (-‖x‖^2 / (4 * α * t))) ((hasDerivAt_id (‖x‖^2)).neg.div_const (4 * α * t))) (hasFDerivAt_norm_sq x))
  ext v
  simp only [_root_.smul_apply, smul_eq_mul]
  field_simp
  ring


lemma hasDerivAt_heatKernelND_t {n : ℕ} (hα : 0 < α) {t : ℝ} {x : E n} (ht : 0 < t) :
    HasDerivAt (fun τ => heatKernelND α x τ)
      ((-((n : ℝ) / (2 * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) *
         Real.exp (-‖x‖^2 / (4 * α * t))
       + (1 / (Real.sqrt (4 * Real.pi * α * t))^n) *
         ((1 / (4 * α)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t))) t := by
  unfold heatKernelND
  have h1 := HasDerivAt.comp t (@deriv_sqrt_inv_pow_n (4 * Real.pi * α * t) n (by positivity)) ((hasDerivAt_id t).const_mul (4 * Real.pi * α))
  have h2 := HasDerivAt.comp t (Real.hasDerivAt_exp (-‖x‖^2 / (4 * α * t))) ((((hasDerivAt_id t).const_mul (4 * α)).inv (ne_of_gt (by positivity))).const_mul (-‖x‖^2))
  apply HasDerivAt.congr_deriv (h1.mul h2)
  simp only [Function.comp_apply, id_eq, Pi.inv_apply]
  ring_nf
  field_simp




lemma hasFDerivAt_heatKernelND_x {n : ℕ} {α t : ℝ} {x : E n} (ht : 0 < t) (hα : 0 < α) :
    HasFDerivAt (fun x' => heatKernelND α x' t)
      ((-(1 / (2 * α * t)) * Real.exp (-‖x‖^2 / (4 * α * t)) *
        (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • (innerSL ℝ x)) x := by
  unfold heatKernelND
  apply HasFDerivAt.congr_fderiv ((hasFDerivAt_exp_neg_norm_sq x ht hα).const_mul (1 / (Real.sqrt (4 * Real.pi * α * t))^n))
  ext v
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

end Derivatives

lemma deriv_heatKernelND_t {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) :
    deriv (fun τ => heatKernelND α x τ) t =
    ((-((n : ℝ) / (2 * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) *
       Real.exp (-‖x‖^2 / (4 * α * t))
     + (1 / (Real.sqrt (4 * Real.pi * α * t))^n) *
       ((1 / (4 * α)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t))) := by
  exact (hasDerivAt_heatKernelND_t α hα ht).deriv

lemma gradient_heatKernelND_x {n : ℕ} {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    gradient (fun (x' : E n) => heatKernelND α x' t) =
    fun (x' : E n) => (-(1 / (2 * α * t)) * Real.exp (-‖x'‖^2 / (4 * α * t)) *
      (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • x' := by
  funext x'
  unfold gradient
  rw [(hasFDerivAt_heatKernelND_x ht hα).fderiv]
  have h_isom : (toDual ℝ (E n)).symm (innerSL ℝ x') = x' := by
    change (toDual ℝ (E n)).symm (toDual ℝ (E n) x') = x'
    exact LinearIsometryEquiv.symm_apply_apply (toDual ℝ (E n)) x'
  rw [map_smul, h_isom]

lemma div_field_heatKernelND_grad {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) :
    div_field (fun x' => (-(1 / (2 * α * t)) * Real.exp (-‖x'‖^2 / (4 * α * t)) *
      (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • x') x =
    ((-((n : ℝ) / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) *
       Real.exp (-‖x‖^2 / (4 * α * t))
     + (1 / (Real.sqrt (4 * Real.pi * α * t))^n) *
       ((1 / (4 * α^2)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t))) := by
  unfold div_field
  have h_scalar : HasFDerivAt (fun x' => -(1 / (2 * α * t)) * Real.exp (-‖x'‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n))
    (((1 / (4 * α^2 * t^2)) * Real.exp (-‖x‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • innerSL ℝ x) x := by
    rw [show (fun x' => -(1 / (2 * α * t)) * Real.exp (-‖x'‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) =
      fun x' => (-(1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x'‖^2 / (4 * α * t)) from funext fun x' => by ring]
    apply HasFDerivAt.congr_fderiv ((hasFDerivAt_exp_neg_norm_sq x ht hα).const_mul (-(1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)))
    ext v
    simp only [_root_.smul_apply, smul_eq_mul]
    ring
  erw [(h_scalar.smul (hasFDerivAt_id (𝕜 := ℝ) x)).fderiv]
  have h_trace_id : LinearMap.trace ℝ (E n) (ContinuousLinearMap.id ℝ (E n)) = n := by aesop
  have h_trace_smulRight : ∀ c : ℝ, LinearMap.trace ℝ (E n) (ContinuousLinearMap.smulRight (c • innerSL ℝ x) (id x)) = c * ‖x‖^2 := by
    intro c
    rw [show (ContinuousLinearMap.smulRight (c • innerSL ℝ x) (id x) : E n →ₗ[ℝ] E n) = LinearMap.smulRight (c • (innerSL ℝ x : E n →ₗ[ℝ] ℝ)) x from rfl]
    rw [LinearMap.trace_smulRight]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    simp_all only [one_div, mul_inv_rev, neg_mul, ContinuousLinearMap.coe_id, LinearMap.trace_id,
      finrank_euclideanSpace, Fintype.card_fin, ContinuousLinearMap.coe_coe, coe_innerSL_apply, mul_eq_mul_left_iff]
    left
    exact real_inner_self_eq_norm_sq x
  simp
  ring_nf

lemma laplacian_heatKernelND_x {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) :
    laplacian (fun x' => heatKernelND α x' t) x =
    ((-((n : ℝ) / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) *
       Real.exp (-‖x‖^2 / (4 * α * t))
     + (1 / (Real.sqrt (4 * Real.pi * α * t))^n) *
       ((1 / (4 * α^2)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t))) := by
  unfold laplacian
  rw [gradient_heatKernelND_x hα ht]
  exact div_field_heatKernelND_grad hα ht

theorem heatKernelND_solves_heat_eq {n : ℕ} (hα : 0 < α) {t : ℝ} {x : E n} (ht : 0 < t) :
    deriv (fun τ => heatKernelND α x τ) t = α * laplacian (fun x' => heatKernelND α x' t) x := by
  rw [deriv_heatKernelND_t hα ht, laplacian_heatKernelND_x hα ht]
  ring_nf
  field_simp

end Heat
