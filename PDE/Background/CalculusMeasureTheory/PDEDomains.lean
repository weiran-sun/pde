import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Module.Connected
import PDE.Background.CalculusMeasureTheory.DivergenceTheorem.GeneralizedDivergence

open Real Set Metric Filter Function Pointwise InnerProductSpace
open scoped BigOperators Topology Classical
open GeneralizedDivergenceStandalone


abbrev E := EuclideanSpace ℝ (Fin 3)


noncomputable def E_to_EN2 : E ≃ₗᵢ[ℝ] EN 2 :=
  LinearIsometryEquiv.ofSurjective
    { toFun := fun (x : E) =>
        WithLp.equiv 2 (EM 2 × ℝ) |>.symm (
          WithLp.equiv 2 (Fin 2 → ℝ) |>.symm (fun (i : Fin 2) => x (Fin.castSucc i)),
          x (Fin.last 2)
        )
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl
      norm_map' := fun x => by
        change ‖WithLp.toLp 2 (WithLp.toLp 2 (fun (i : Fin 2) => x.ofLp (Fin.castSucc i)), x.ofLp (Fin.last 2))‖ = ‖x‖
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        let lhs := WithLp.toLp 2 (WithLp.toLp 2 (fun (i : Fin 2) => x.ofLp (Fin.castSucc i)), x.ofLp (Fin.last 2))
        have h_lhs : ‖lhs‖^2 = ⟪lhs, lhs⟫_ℝ := (real_inner_self_eq_norm_sq lhs).symm
        have h_rhs : ‖x‖^2 = ⟪x, x⟫_ℝ := (real_inner_self_eq_norm_sq x).symm
        change ‖lhs‖^2 = ‖x‖^2
        rw [h_lhs, h_rhs]
        change (∑ i : Fin 2, ⟪x.ofLp (Fin.castSucc i), x.ofLp (Fin.castSucc i)⟫_ℝ) + ⟪x.ofLp (Fin.last 2), x.ofLp (Fin.last 2)⟫_ℝ =
               ∑ i : Fin 3, ⟪x.ofLp i, x.ofLp i⟫_ℝ
        symm
        rw [Fin.sum_univ_castSucc] }
    (by
      intro y
      let y_prod := WithLp.equiv 2 (EM 2 × ℝ) y
      let v := WithLp.equiv 2 (Fin 2 → ℝ) y_prod.1
      let c := y_prod.2
      use WithLp.equiv 2 (Fin 3 → ℝ) |>.symm (fun i => if h : i.val < 2 then v ⟨i.val, h⟩ else c)
      change (WithLp.equiv 2 (EM 2 × ℝ)).symm _ = (WithLp.equiv 2 (EM 2 × ℝ)).symm y_prod
      congr 1
      ext i
      · have h_lt : (Fin.castSucc i).val < 2 := i.isLt
        simp; try rfl
        aesop
      · have h_nlt : ¬((Fin.last 2).val < 2) := by decide
        simp; try rfl
    )
/-!
### Domain Definitions
-/


def IsOutwardUnitNormal (s : Set E) (n : E → E) : Prop :=
  IsOutwardNormal (E_to_EN2 '' s) (fun y => E_to_EN2 (n (E_to_EN2.symm y)))

class HasDivergenceTheoremDomain (s : Set E) : Prop where
  has_normal : ∃ n : E → E, IsOutwardUnitNormal s n ∧ ContinuousOn n (frontier s)

class HasPDEDomain (s : Set E) extends HasDivergenceTheoremDomain s where
  is_open : IsOpen s
  is_connected : IsConnected s
  unique_diff : UniqueDiffOn ℝ (closure s)


lemma support_subset_ball (f : E → ℝ) (hf_supp : HasCompactSupport f) :
  ∃ R_f : ℝ, ∀ z : E, f z ≠ 0 → z ∈ Metric.ball (0 : E) R_f := by
  rcases (Metric.isBounded_iff_subset_ball (0 : E)).mp hf_supp.isBounded with ⟨R_f, hR_f⟩
  exact ⟨R_f, fun z hz => hR_f (subset_tsupport f hz)⟩

lemma convolution_norm_ineq (x x' y : E) (r R_f : ℝ) (hx' : x' ∈ Metric.ball x r) (hz : x' - y ∈ Metric.ball (0 : E) R_f) :
  y ∈ Metric.ball (0 : E) (‖x‖ + r + R_f) := by
  simp_rw [Metric.mem_ball, dist_zero_right, dist_eq_norm] at hx' hz ⊢
  linarith [congr_arg norm (sub_add_cancel y x'), norm_add_le (y - x') x', congr_arg norm (sub_add_cancel x' x), norm_add_le (x' - x) x, norm_sub_rev y x']

lemma convolution_support_in_ball (f : E → ℝ) (hf_supp : HasCompactSupport f) (x : E) (r : ℝ) :
  ∃ R : ℝ, ∀ x' ∈ Metric.ball x r, ∀ y : E, y ∉ Metric.ball (0 : E) R → f (x' - y) = 0 := by
  rcases support_subset_ball f hf_supp with ⟨R_f, hR_f⟩
  exact ⟨‖x‖ + r + R_f, fun x' hx' y hy => by_contra fun h_nz => hy (convolution_norm_ineq x x' y r R_f hx' (hR_f (x' - y) h_nz))⟩

lemma indicator_mul_one_eq (f : E → ℝ) (R : ℝ) (y : E) :
  f y * Set.indicator (Metric.ball (0 : E) R) (fun _ => (1 : ℝ)) y = Set.indicator (Metric.ball (0 : E) R) f y := by
  by_cases h : y ∈ Metric.ball (0 : E) R
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

lemma exists_bound_of_continuous_compact_support {F : Type*} [NormedAddCommGroup F] (g : E → F) (hg_cont : Continuous g) (hg_supp : HasCompactSupport g) :
  ∃ M : ℝ, ∀ z : E, ‖g z‖ ≤ M := by
  exact Continuous.bounded_above_of_compact_support hg_cont hg_supp

lemma conv_pointwise_bound (f : E → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) (x : E) :
  ∃ R M : ℝ, ∀ y : E, ‖f (x - y)‖ ≤ M * Set.indicator (Metric.ball (0 : E) R) (fun _ => (1 : ℝ)) y := by
  rcases exists_bound_of_continuous_compact_support f hf_smooth.continuous hf_supp with ⟨M, hM⟩
  rcases support_subset_ball f hf_supp with ⟨R_f, hR_f⟩
  use ‖x‖ + R_f, M
  intro y
  by_cases hy : y ∈ Metric.ball (0 : E) (‖x‖ + R_f)
  · rw [Set.indicator_of_mem hy, mul_one]
    exact hM (x - y)
  · rw [Set.indicator_of_notMem hy, mul_zero]
    by_cases h_nz : f (x - y) = 0
    · rw [h_nz, norm_zero]
    · exfalso
      apply hy
      rw [Metric.mem_ball, dist_zero_right]
      linarith [norm_sub_norm_le y x, norm_sub_rev y x,
        show ‖x - y‖ < R_f by simpa [Metric.mem_ball, dist_zero_right] using hR_f (x - y) h_nz]

lemma greens_integrand_algebra_split (u_val : ℝ) (grad_Phi grad_H n_val : E) :
  u_val * ⟪grad_Phi + grad_H, n_val⟫_ℝ = u_val * ⟪grad_Phi, n_val⟫_ℝ + u_val * ⟪grad_H, n_val⟫_ℝ := by
  rw [inner_add_left, mul_add]

lemma greens_bound_algebra {ε ε₀ M_H : ℝ}
  (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) (hM_H_nonneg : 0 ≤ M_H) :
  (1 / (4 * Real.pi * ε)) + M_H ≤ ((1 / (4 * Real.pi)) + (M_H * ε₀)) / ε := by
  calc
    (1 / (4 * Real.pi * ε)) + M_H = (1 / (4 * Real.pi * ε)) + (M_H * ε) / ε := by
      rw [mul_div_cancel_right₀ M_H (ne_of_gt hε_pos)]
    _ ≤ (1 / (4 * Real.pi * ε)) + (M_H * ε₀) / ε :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε_le hM_H_nonneg) (inv_nonneg.mpr (le_of_lt hε_pos)))
    _ = ((1 / (4 * Real.pi)) + (M_H * ε₀)) / ε := by ring

lemma norm_smul_inv_radius_sub (x₀ x : E) (ε : ℝ) (hε_pos : 0 < ε) (hx : x ∈ Metric.sphere x₀ ε) :
  ‖-(1 / ε) • (x - x₀)‖ = 1 := by
  rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hε_pos),
      ← dist_eq_norm, Metric.mem_sphere.mp hx, div_mul_cancel₀ 1 (ne_of_gt hε_pos)]

lemma tendsto_const_mul_eps_zero (M : ℝ) :
    Tendsto (fun ε => M * 4 * π * ε) (𝓝[>] 0) (𝓝 0) := by
  suffices Tendsto (fun ε => M * 4 * π * ε) (𝓝[>] 0) (𝓝 (M * 4 * π * 0)) by simpa only [mul_zero]
  exact (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).const_mul (M * 4 * π)

lemma limit_area_bound_zero (M : ℝ) :
  Filter.Tendsto (fun ε => M * (4 * Real.pi * ε^2)) (𝓝[>] 0) (𝓝 0) := by
  have h_eval : Filter.Tendsto (fun ε : ℝ => M * (4 * Real.pi * ε^2)) (𝓝 0) (𝓝 (M * (4 * Real.pi * 0^2))) :=
    (continuous_const.mul (continuous_const.mul (continuous_id.pow 2))).tendsto 0
  have h_zero : M * (4 * Real.pi * 0^2) = 0 := by ring
  rw [h_zero] at h_eval
  exact tendsto_nhdsWithin_of_tendsto_nhds h_eval
