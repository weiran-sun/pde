import PDE.Background.CalculusMeasureTheory.PDEDomains
import PDE.Background.CalculusMeasureTheory.DomainGeometry
import PDE.Background.CalculusMeasureTheory.GraphHausdorffMeasure.RnGraphHausdorffMeasure
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Convolution

open Real Set MeasureTheory Metric Filter Function Pointwise InnerProductSpace
open scoped BigOperators Topology
open GeneralizedDivergenceStandalone

noncomputable def surfaceArea : Measure E := Measure.hausdorffMeasure 2

/-!
### Surface Area and Hausdorff Measure
-/

lemma surfaceArea_eq_hausdorff_dim_minus_one :
    surfaceArea = Measure.hausdorffMeasure ((Module.finrank ℝ E : ℝ) - 1) := by
  rw [surfaceArea]
  congr 1;simp;norm_num

lemma hausdorff_dim_eq_surfaceArea :
    Measure.hausdorffMeasure ((Module.finrank ℝ E : ℝ) - 1) = surfaceArea := by
  rw [surfaceArea]
  congr 1;simp;norm_num

/-- WARNING (normalization inconsistency): the `sorry` below is unprovable as stated.
`surfaceArea` is Mathlib's *raw* 2-dimensional Hausdorff measure `μH[2]`, and
`GraphAreaFull.sphere_hausdorffMeasure_unit` (Background/…/GraphHausdorffMeasure/R3GraphMeasure.lean,
fully proved) shows `μH[2] (sphere 0 1) = 16`, not `4π`. The value `4π` holds only for the
*normalized* Euclidean Hausdorff measure `μHE[2] = ENNReal.ofReal (π/4) • μH[2]`
(`GraphAreaFull.euclideanHausdorffMeasure_two_eq`). Consequently `unit_sphere_area_hausdorff`
and every `4πr²` constant downstream carries a `π/4` normalization error relative to `μH[2]`.
Planned fix (separate pass): redefine `surfaceArea := μHE[2]` and derive `sphere_surface_area`
from the proved `GraphAreaFull.sphere_area`. -/
lemma area_formula_spherical :
  (surfaceArea (sphere (0 : E) 1)).toReal =
  ∫ (θ : ℝ) in Set.Icc 0 (2 * Real.pi), ∫ (ϕ : ℝ) in Set.Icc 0 Real.pi, Real.sin ϕ := by
  calc (surfaceArea (sphere (0 : E) 1)).toReal
    _ = ∫ p in (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 Real.pi), Real.sin p.2 ∂(MeasureTheory.Measure.hausdorffMeasure 2) := by sorry
    _ = ∫ p in (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 Real.pi), Real.sin p.2 ∂volume := by rw [MeasureTheory.hausdorffMeasure_prod_real]
    _ = ∫ (θ : ℝ) in Set.Icc 0 (2 * Real.pi), ∫ (ϕ : ℝ) in Set.Icc 0 Real.pi, Real.sin ϕ := by
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.setIntegral_prod]
      exact (Real.continuous_sin.comp continuous_snd).continuousOn.integrableOn_compact (IsCompact.prod isCompact_Icc isCompact_Icc)

lemma unit_sphere_area_hausdorff : (surfaceArea (sphere (0 : E) 1)).toReal = 4 * π := by
  rw [area_formula_spherical]
  simp_rw [show ∫ (ϕ : ℝ) in Set.Icc 0 π, Real.sin ϕ = 2 by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_nonneg, integral_sin]; simp; ring]
  rw [setIntegral_const]
  have : (0 : ℝ) ≤ 2 * π := by positivity
  simp_all only [volume_real_Icc, sub_zero, sup_of_le_left, smul_eq_mul, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
  ring

lemma toSphere_univ_eq_four_pi : (volume : Measure E).toSphere Set.univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [MeasureTheory.Measure.toSphere_apply_univ', measure_sdiff_null (measure_singleton 0)]
  simp only [EuclideanSpace.volume_ball_fin_three, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat, ENNReal.ofReal_one, one_pow, one_mul]
  rw [show (3 : ENNReal) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

lemma measure_sphere_scaling (r : ℝ) (hr_pos : 0 < r) :
  surfaceArea (sphere (0 : E) r) = ENNReal.ofReal (r^2) * surfaceArea (sphere (0 : E) 1) := by
  unfold surfaceArea
  have h_scaling : sphere (0 : E) r = AffineMap.homothety (0 : E) r '' sphere (0 : E) 1 := by
    ext x; simp only [Metric.mem_sphere, Set.mem_image, dist_zero_right, AffineMap.homothety_apply]
    exact ⟨fun hx ↦ ⟨r⁻¹ • x, by simp [norm_smul, abs_of_pos hr_pos, hx, inv_mul_cancel₀ hr_pos.ne'], by simp [smul_smul, mul_inv_cancel₀ hr_pos.ne']⟩, fun ⟨y, hy, hyx⟩ ↦ by simp [norm_smul, abs_of_pos hr_pos, hy,← hyx]⟩
  rw [h_scaling, MeasureTheory.hausdorffMeasure_homothety_image (by norm_num : (0:ℝ) ≤ 2) (0 : E) hr_pos.ne', ENNReal.smul_def, smul_eq_mul, nnnorm_of_nonneg hr_pos.le, ENNReal.ofReal_pow hr_pos.le, ENNReal.ofReal_eq_coe_nnreal hr_pos.le]
  simp [ENNReal.coe_pow]

lemma surfaceArea_sphere_scaled (x₀ : E) {r : ℝ} (hr_pos : 0 < r) :
  surfaceArea (Metric.sphere x₀ r) = ENNReal.ofReal (r^2) * surfaceArea (Metric.sphere x₀ 1) := by
  unfold surfaceArea
  rw [sphere_eq_homothety_image_unit_sphere x₀ hr_pos,
    MeasureTheory.hausdorffMeasure_homothety_image (by norm_num : (0 : ℝ) ≤ 2) x₀ hr_pos.ne',
    ENNReal.smul_def, smul_eq_mul, nnnorm_of_nonneg hr_pos.le, ENNReal.ofReal_pow hr_pos.le,
    ENNReal.ofReal_eq_coe_nnreal hr_pos.le]
  simp [ENNReal.coe_pow]

lemma surfaceArea_sphere_translate (x₀ : E) (ε : ℝ) :
  surfaceArea (Metric.sphere x₀ ε) = surfaceArea (Metric.sphere (0 : E) ε) := by
  unfold surfaceArea
  rw [sphere_eq_image_add_zero x₀ ε]
  have h_iso : Isometry (fun y : E => y + x₀) := (IsometryEquiv.addRight x₀).isometry
  exact Isometry.hausdorffMeasure_image (d := 2) h_iso (Or.inl (by norm_num)) (Metric.sphere 0 ε)

lemma sphere_surface_area (x₀ : E) (ε : ℝ) (hε : 0 < ε) :
  surfaceArea (Metric.sphere x₀ ε) = ENNReal.ofReal (4 * Real.pi * ε ^ 2) := by
  have h_translate : surfaceArea (Metric.sphere x₀ ε) = surfaceArea (Metric.sphere (0 : E) ε) := by
    exact surfaceArea_sphere_translate x₀ ε
  have h_scale : surfaceArea (Metric.sphere (0 : E) ε) = ENNReal.ofReal (ε ^ 2) * surfaceArea (Metric.sphere (0 : E) 1) := by
    exact measure_sphere_scaling ε hε
  have h_hausdorff_eq_toSphere : surfaceArea (Metric.sphere (0 : E) 1) = (volume : Measure E).toSphere Set.univ := by
    rw [toSphere_univ_eq_four_pi]
    have h_toReal : (surfaceArea (Metric.sphere (0 : E) 1)).toReal = 4 * Real.pi := unit_sphere_area_hausdorff
    have h_ne_top : surfaceArea (Metric.sphere (0 : E) 1) ≠ ⊤ := by
      intro h
      simp_rw [h] at h_toReal
      have : (0 : ℝ) < 4 * Real.pi := by positivity
      aesop
    rw [← ENNReal.ofReal_toReal h_ne_top, h_toReal]
  have h_unit_sphere : (volume : Measure E).toSphere Set.univ = ENNReal.ofReal (4 * Real.pi) := by
    exact toSphere_univ_eq_four_pi
  rw [h_translate, h_scale, h_hausdorff_eq_toSphere, h_unit_sphere]
  have h_pos : (0 : ℝ) ≤ ε ^ 2 := sq_nonneg ε
  rw [← ENNReal.ofReal_mul h_pos]
  congr 1
  ring

lemma surface_area_sphere_three_dim (r : ℝ) (hr_pos : 0 < r) :
  ∫ x in sphere (0 : E) r, 1 ∂surfaceArea = 4 * π * r^2 := by
  have h_measure_scaling := measure_sphere_scaling r hr_pos
  rw [setIntegral_const, smul_eq_mul, mul_one]
  unfold Measure.real
  rw [h_measure_scaling, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg r), unit_sphere_area_hausdorff]
  ring

/-!
### Finite Measure and Frontiers
-/

lemma measure_sphere_lt_top (r : ℝ) (hr_pos : 0 < r) :
    surfaceArea (sphere (0 : E) r) < ⊤ := by
  rw [measure_sphere_scaling r hr_pos]
  have h_toReal : (surfaceArea (Metric.sphere (0 : E) 1)).toReal = 4 * Real.pi := unit_sphere_area_hausdorff
  have h_ne_top : surfaceArea (Metric.sphere (0 : E) 1) ≠ ⊤ := by
    intro h
    simp_rw [h] at h_toReal
    have : (0 : ℝ) < 4 * Real.pi := by positivity
    aesop
  exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_ne_top)

lemma isFiniteMeasure_sphere (r : ℝ) (hr_pos : 0 < r) :
    IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) r)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  exact measure_sphere_lt_top r hr_pos

instance instSurfaceAreaSphereIsFiniteMeasure : IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) 1)) := by
  have h_area : (surfaceArea (sphere (0 : E) 1)).toReal = 4 * π := unit_sphere_area_hausdorff
  have h_ne_top : surfaceArea (sphere (0 : E) 1) ≠ ⊤ := by
    intro h_top
    have h_zero : (surfaceArea (sphere (0 : E) 1)).toReal = 0 := by
      rw [h_top]; simp_all
    rw [h_zero] at h_area
    have h_pi_pos : (0 : ℝ) < 4 * π := by positivity
    linarith
  have h_lt_top : surfaceArea (sphere (0 : E) 1) < ⊤ := lt_top_iff_ne_top.mpr h_ne_top
  exact ⟨by simpa using h_lt_top⟩

lemma surfaceArea_sphere_lt_top (x₀ : E) {ε : ℝ} (hε : 0 < ε) :
  surfaceArea (Metric.sphere x₀ ε) < ⊤ := by
  let g : E ≃ᵢ E := IsometryEquiv.addRight x₀
  have h_map : MeasureTheory.Measure.map g surfaceArea = surfaceArea := by
    erw [Isometry.map_hausdorffMeasure (isometry_add_right x₀) (Or.inr (fun y ↦ ⟨y - x₀, sub_add_cancel y x₀⟩))]
    rw [Set.range_eq_univ.mpr (fun y ↦ ⟨y - x₀, sub_add_cancel y x₀⟩), MeasureTheory.Measure.restrict_univ];rfl
  rw [← h_map, MeasureTheory.Measure.map_apply (Isometry.continuous g.isometry).measurable isClosed_sphere.measurableSet]
  exact (show g ⁻¹' Metric.sphere x₀ ε = Metric.sphere 0 ε by ext y; simp [g]) ▸ measure_sphere_lt_top ε hε

lemma surfaceArea_sphere_ne_top (c : E) (r : ℝ) (hr : 0 < r) :
  surfaceArea (Metric.sphere c r) ≠ ⊤ := by
  refine lt_top_iff_ne_top.mp ?_
  exact surfaceArea_sphere_lt_top c hr

lemma surfaceArea_union_ne_top (A B : Set E) (hA : surfaceArea A ≠ ⊤) (hB : surfaceArea B ≠ ⊤) :
  surfaceArea (A ∪ B) ≠ ⊤ :=
  lt_top_iff_ne_top.mp (lt_of_le_of_lt (measure_union_le A B) (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hA, lt_top_iff_ne_top.mpr hB⟩))

lemma area_punctured_neq_top (Ω : Set E) (a b : E) (ε : ℝ)
  (hε_pos : 0 < ε)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤) :
  surfaceArea (frontier (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) ≠ ⊤ := by
  have h_subset : frontier (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) ⊆ frontier Ω ∪ Metric.sphere a ε ∪ Metric.sphere b ε := by
    intro x hx
    rw [Set.sdiff_eq] at hx
    obtain ⟨h_omega, _⟩ | ⟨_, h_compl⟩ := frontier_inter_subset Ω _ hx
    · exact Or.inl (Or.inl h_omega)
    · rw [frontier_compl] at h_compl
      obtain ⟨h_a, _⟩ | ⟨_, h_b⟩ := frontier_union_subset _ _ h_compl
      · exact Or.inl (Or.inr (frontier_closedBall_subset_sphere h_a))
      · exact Or.inr (frontier_closedBall_subset_sphere h_b)
  intro h_top
  exact surfaceArea_union_ne_top _ _
    (surfaceArea_union_ne_top _ _ h_area (surfaceArea_sphere_ne_top a ε hε_pos))
    (surfaceArea_sphere_ne_top b ε hε_pos)
    (top_le_iff.mp (h_top ▸ measure_mono h_subset))

lemma surfaceArea_frontier_ball_ne_top (c : E) (ε : ℝ) :
  surfaceArea (frontier (Metric.ball c ε)) ≠ ⊤ := by
  obtain h_le | h_pos := le_or_gt ε 0
  · rw [Metric.ball_eq_empty.mpr h_le, frontier_empty, MeasureTheory.measure_empty]
    exact ENNReal.zero_ne_top
  · rw [frontier_ball_eq_sphere c ε h_pos]
    exact surfaceArea_sphere_ne_top c ε h_pos

lemma h_fin_area_a (a : E) (ε : ℝ) : surfaceArea (frontier (Metric.ball a ε)) ≠ ⊤ := surfaceArea_frontier_ball_ne_top a ε

lemma h_fin_area_b (b : E) (ε : ℝ) : surfaceArea (frontier (Metric.ball b ε)) ≠ ⊤ := surfaceArea_frontier_ball_ne_top b ε

lemma h_fin_area_sphere_a (a : E) (ε : ℝ) :
  surfaceArea (Metric.sphere a ε) ≠ ⊤ := by
  rcases lt_trichotomy ε 0 with h_neg | rfl | h_pos
  · have h_empty : Metric.sphere a ε = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun (x : E) hx =>
      not_le_of_gt h_neg ((Metric.mem_sphere (α := E)).mp hx ▸ dist_nonneg)
    rw [h_empty, MeasureTheory.measure_empty]
    exact ENNReal.zero_ne_top
  · rw [Metric.sphere_zero]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (by unfold surfaceArea; exact MeasureTheory.Measure.hausdorffMeasure_le_one_of_subsingleton Set.subsingleton_singleton (by norm_num))
  · exact surfaceArea_sphere_ne_top a ε h_pos

lemma h_fin_area_sphere_b (b : E) (ε : ℝ) :
  surfaceArea (Metric.sphere b ε) ≠ ⊤ := by
  rcases lt_trichotomy ε 0 with h_neg | rfl | h_pos
  · have h_empty : Metric.sphere b ε = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun (x : E) hx =>
      not_le_of_gt h_neg ((Metric.mem_sphere (α := E)).mp hx ▸ dist_nonneg)
    rw [h_empty, MeasureTheory.measure_empty]
    exact ENNReal.zero_ne_top
  · rw [Metric.sphere_zero]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (by unfold surfaceArea; exact MeasureTheory.Measure.hausdorffMeasure_le_one_of_subsingleton Set.subsingleton_singleton (by norm_num))
  · exact surfaceArea_sphere_ne_top b ε h_pos

/-!
### Integration and Transformations
-/

lemma sphere_integral_preimage (x₀ : E) (r : ℝ) (hr : 0 < r) :
  ((Homeomorph.addRight (-x₀)).trans (Homeomorph.smulOfNeZero (1 / r) (by positivity))) ⁻¹' (sphere 0 1) = sphere x₀ r := by
  ext x
  simp only [Homeomorph.trans_apply, Set.mem_preimage, Metric.mem_sphere, dist_eq_norm, sub_zero]
  change ‖(1 / r) • (x + -x₀)‖ = 1 ↔ ‖x - x₀‖ = r
  rw [← sub_eq_add_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hr), mul_comm, mul_one_div, div_eq_iff hr.ne', one_mul]

lemma sphere_integral_map_measure (x₀ : E) (r : ℝ) (hr : 0 < r) :
  MeasureTheory.Measure.map ((Homeomorph.addRight (-x₀)).trans (Homeomorph.smulOfNeZero (1 / r) (by positivity))) surfaceArea = (ENNReal.ofReal (r^2)) • (surfaceArea : MeasureTheory.Measure E) := by
  have h_meas_smul : Measurable (fun x : E ↦ (1 / r) • x) := Continuous.measurable (continuous_id.const_smul (1 / r))
  have h_meas_add : Measurable (fun x : E ↦ x + -x₀) := Continuous.measurable (continuous_id.add continuous_const)
  have h_surj : Function.Surjective (fun x : E ↦ x + -x₀) := fun y ↦ ⟨y + x₀, by simp⟩
  rw [show ⇑((Homeomorph.addRight (-x₀)).trans (Homeomorph.smulOfNeZero (1 / r) (by positivity))) = (fun x ↦ (1 / r) • x) ∘ (fun x ↦ x + -x₀) from rfl, ← MeasureTheory.Measure.map_map h_meas_smul h_meas_add]
  have h_map_trans : MeasureTheory.Measure.map (fun x ↦ x + -x₀) surfaceArea = surfaceArea := by
    rw [surfaceArea]; erw [Isometry.map_hausdorffMeasure (isometry_add_right (-x₀)) (Or.inr h_surj)]; rw [Set.range_eq_univ.mpr h_surj]; exact MeasureTheory.Measure.restrict_univ
  ext s hs
  rw [MeasureTheory.Measure.map_apply h_meas_smul hs, MeasureTheory.Measure.smul_apply]
  have h_pre : (fun x ↦ (1 / r) • x) ⁻¹' s = r • s := by
    ext x; simp only [Set.mem_preimage, Set.mem_smul_set]; constructor
    · intro hx; exact ⟨(1 / r) • x, hx, by rw [smul_smul, mul_one_div, div_self hr.ne', one_smul]⟩
    · rintro ⟨y, hy, rfl⟩; rw [smul_smul, one_div, inv_mul_cancel₀ hr.ne', one_smul]; exact hy
  rw [h_pre, h_map_trans, surfaceArea, MeasureTheory.Measure.hausdorffMeasure_smul₀ (by norm_num : (0:ℝ) ≤ 2) hr.ne' s]
  congr 1; ext1; simp [Real.norm_of_nonneg hr.le, Real.toNNReal_pow hr.le]; congr 1; simp; positivity

lemma sphere_integral_gsymm (x₀ : E) (r : ℝ) (hr : 0 < r) (y : E) :
  ((Homeomorph.addRight (-x₀)).trans (Homeomorph.smulOfNeZero (1 / r) (by positivity))).symm y = x₀ + r • y := by
  let g : E ≃ₜ E := (Homeomorph.addRight (-x₀)).trans (Homeomorph.smulOfNeZero (1 / r) (by positivity))
  have h_gx : ∀ x, g x = (1 / r) • (x - x₀) := fun x ↦ by change (1 / r) • (x + -x₀) = _; rw [sub_eq_add_neg]
  have h1 : g (x₀ + r • y) = y := by
    rw [h_gx, add_comm x₀, add_sub_cancel_right, smul_smul, one_div, inv_mul_cancel₀ hr.ne', one_smul]
  calc
    g.symm y = g.symm (g (x₀ + r • y)) := by rw [← h1]; simp_all only [one_div, Homeomorph.trans_apply, Homeomorph.coe_addRight, Homeomorph.smulOfNeZero_apply, smul_add, smul_neg, Homeomorph.symm_trans_apply, Homeomorph.smulOfNeZero_symm_apply, inv_inv, add_neg_cancel_comm, g]
    _ = x₀ + r • y := by simp

/-!
### Volume and Convolutions
-/

lemma volume_sphere (x : E) (r : ℝ) : volume (Metric.sphere x r) = 0 := by
  exact MeasureTheory.Measure.addHaar_sphere volume x r

lemma volume_closed_ball_3d (x₀ : E) (R : ℝ) (hR : 0 < R) :
  volume.real (Metric.closedBall x₀ R) = (4 / 3) * Real.pi * R ^ 3 := by
  change (volume (Metric.closedBall x₀ R)).toReal = _
  rw [Measure.addHaar_closedBall_eq_addHaar_ball volume x₀ R,
      EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le,
      ENNReal.toReal_ofReal (by positivity)]
  ring

noncomputable def convolution (f g : E → ℝ) (x : E) : ℝ :=
  MeasureTheory.convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume x

lemma convolution_commutative (f g : E → ℝ) (x : E) :
  convolution f g x = convolution g f x := by
  unfold _root_.convolution
  rw [MeasureTheory.convolution_eq_swap, MeasureTheory.convolution_def]
  congr 1
  ext y
  exact mul_comm _ _

/-!
### Integrability and Bounds
-/

lemma integrable_indicator_equiv (f : E → ℝ) (R : ℝ) :
  Integrable (Set.indicator (Metric.ball (0 : E) R) f) volume ↔ IntegrableOn f (Metric.ball (0 : E) R) volume := by
  exact integrable_indicator_iff measurableSet_ball

lemma inv_norm_integrableOn_ball (R : ℝ) (hR : 0 < R) :
  IntegrableOn (fun x : E => 1 / ‖x‖) (Metric.ball (0 : E) R) volume := by
  rw [← MeasureTheory.integrable_indicator_iff measurableSet_ball]
  have h_eq : (Metric.ball (0 : E) R).indicator (fun x => 1 / ‖x‖) = fun x => (Set.Ico 0 R).indicator (fun y => 1 / y) ‖x‖ := by
    ext x
    by_cases hx : x ∈ Metric.ball (0 : E) R
    · simp_all only [mem_ball, dist_zero_right, one_div, indicator_of_mem, mem_Ico, norm_nonneg, and_self]
    · simp_all only [mem_ball, dist_zero_right, not_lt, one_div, indicator_of_notMem, mem_Ico, norm_nonneg, true_and]
  rw [h_eq]

  have h_general_dim : Integrable (fun x : E => (Set.Ico 0 R).indicator (fun y => 1 / y) ‖x‖) volume ↔
    IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ E - 1) • (Set.Ico 0 R).indicator (fun z => 1 / z) y) (Set.Ioi 0) := by
    exact integrable_fun_norm_addHaar volume
  rw [h_general_dim, finrank_euclideanSpace_fin]

  have h_pointwise : (fun y : ℝ => y ^ (3 - 1) • (Set.Ico 0 R).indicator (fun z => 1 / z) y) =
    (Set.Ico 0 R).indicator (fun y : ℝ => y) := by
    ext y
    by_cases hy : y ∈ Set.Ico 0 R
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      change y ^ 2 * (1 / y) = y
      rcases eq_or_ne y 0 with rfl | hy0
      · norm_num
      · rw [sq, mul_assoc, mul_one_div_cancel hy0, mul_one]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero]
  rw [h_pointwise]

  unfold IntegrableOn
  rw [MeasureTheory.integrable_indicator_iff measurableSet_Ico]
  change Integrable (fun y => y) ((volume.restrict (Set.Ioi 0)).restrict (Set.Ico 0 R))
  rw [MeasureTheory.Measure.restrict_restrict measurableSet_Ico, Set.inter_comm]

  have h_set_eq : Set.Ioi (0 : ℝ) ∩ Set.Ico 0 R = Set.Ioo 0 R := by
    ext x; simp; exact fun a _ ↦ le_of_lt a
  rw [h_set_eq]

  apply MeasureTheory.IntegrableOn.mono_set (continuous_id.integrableOn_uIoc (μ := volume) (a := 0) (b := R))
  intro x hx
  change x ∈ Set.Ioc (min 0 R) (max 0 R)
  rw [min_eq_left hR.le, max_eq_right hR.le]
  exact ⟨hx.1, hx.2.le⟩

lemma riesz_integral_swap (G : E → E →L[ℝ] ℝ) (hG : Integrable G) :
  (InnerProductSpace.toDual ℝ E).symm (∫ y, G y) = ∫ y, (InnerProductSpace.toDual ℝ E).symm (G y) := by
  apply ext_inner_left ℝ
  intro c
  have hG' : Integrable (fun y => (InnerProductSpace.toDual ℝ E).symm (G y)) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.integrable_comp hG
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  rw [← integral_inner hG' c, ContinuousLinearMap.integral_apply hG]
  congr 1
  ext y
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]

lemma integrableOn_compact_surface_of_continuousOn
  {S : Set E} (h_compact : IsCompact S) (h_area : surfaceArea S ≠ ⊤)
  (f : E → ℝ) (hf_cont : ContinuousOn f S) :
  IntegrableOn f S surfaceArea := by
  haveI : MeasureTheory.IsFiniteMeasure (surfaceArea.restrict S) :=
    isFiniteMeasure_restrict.mpr h_area
  obtain ⟨C, hC⟩ := h_compact.exists_bound_of_continuousOn hf_cont
  exact MeasureTheory.Integrable.of_bound (hf_cont.aestronglyMeasurable h_compact.isClosed.measurableSet) C
    (by filter_upwards [MeasureTheory.ae_restrict_mem h_compact.isClosed.measurableSet] with x hx using hC x hx)

lemma integrableOn_frontier_of_continuousOn
  (Ω : Set E)
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  (f : E → ℝ)
  (hf_cont : ContinuousOn f (frontier Ω)) :
  IntegrableOn f (frontier Ω) surfaceArea := by
  haveI : MeasureTheory.IsFiniteMeasure (surfaceArea.restrict (frontier Ω)) :=
    isFiniteMeasure_restrict.mpr h_area
  obtain ⟨C, hC⟩ := (h_bounded.isCompact_closure.of_isClosed_subset
    isClosed_frontier frontier_subset_closure).exists_bound_of_continuousOn hf_cont
  exact MeasureTheory.Integrable.of_bound (hf_cont.aestronglyMeasurable isClosed_frontier.measurableSet) C
    (by filter_upwards [MeasureTheory.ae_restrict_mem isClosed_frontier.measurableSet] with x hx using hC x hx)

lemma continuousOn_inv_norm_sphere (R : ℝ) (hR : 0 < R) :
    ContinuousOn (fun x : E => 1 / ‖x‖) (Metric.sphere (0 : E) R) := by
  refine ContinuousOn.div continuousOn_const continuous_norm.continuousOn fun x hx => ?_
  rw [mem_sphere_zero_iff_norm.mp hx]
  exact ne_of_gt hR

lemma integrableOn_inv_norm_sphere (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x : E => 1 / ‖x‖) (Metric.sphere (0 : E) R) :=
  (continuousOn_inv_norm_sphere R hR).integrableOn_compact (isCompact_sphere 0 R)

lemma integrable_inv_norm_closedBall (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x : E => (‖x‖)⁻¹) (Metric.closedBall 0 R) := by
  simp_rw [inv_eq_one_div]
  rw [← ball_union_sphere]
  exact IntegrableOn.union (inv_norm_integrableOn_ball R hR) (integrableOn_inv_norm_sphere R hR)

lemma integrableOn_inv_norm_translate (Ω : Set E) (x₀ : E) :
    IntegrableOn (fun x => (‖x - x₀‖)⁻¹) Ω ↔ IntegrableOn (fun x => (‖x‖)⁻¹) ((fun y => y - x₀) '' Ω) := by
  have h_pre : (fun y : E => y - x₀) ⁻¹' ((fun y : E => y - x₀) '' Ω) = Ω := by
    ext x; simp only [mem_preimage, mem_image, sub_left_inj, exists_eq_right]
  have h := (MeasurableEmbedding.integrableOn_map_iff (measurableEmbedding_subRight x₀)
    (f := fun x => (‖x‖)⁻¹) (μ := volume) (s := (fun y : E => y - x₀) '' Ω)).symm
  have h_vol : Measure.map (fun x : E => x - x₀) volume = volume := by
    have h_sub : (fun (x : E) => x - x₀) = fun x => x + -x₀ := funext fun x => sub_eq_add_neg x x₀
    rw [h_sub, Measure.IsAddRightInvariant.map_add_right_eq_self (-x₀)]
  rw [h_pre, h_vol] at h
  exact h

lemma continuousOn_integrableOn_sphere {f : E → ℝ} {a : E} {ε : ℝ}
  (hε : 0 < ε)
  (h_cont : ContinuousOn f (Metric.sphere a ε)) :
  IntegrableOn f (Metric.sphere a ε) surfaceArea := by
  refine integrableOn_compact_surface_of_continuousOn ?_ ?_ f h_cont
  · exact isCompact_sphere a ε
  · have h_trans : surfaceArea (Metric.sphere a ε) = surfaceArea (Metric.sphere (0 : E) ε) := by
      exact surfaceArea_sphere_translate a ε
    rw [h_trans]
    exact ne_top_of_lt (measure_sphere_lt_top ε hε)

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
### Limits of Integrals
-/

lemma ae_ne_singleton (x₀ : E) : ∀ᵐ x ∂volume, x ≠ x₀ := by
  change volume {x : E | ¬x ≠ x₀} = 0
  rw [show {x : E | ¬x ≠ x₀} = {x₀} by ext; simp]
  exact MeasureTheory.measure_singleton x₀

lemma setIntegral_diff_add_inter {F : E → ℝ} {Ω : Set E} {s : Set E}
    [HasPDEDomain Ω] (hs : MeasurableSet s) (hF : IntegrableOn F Ω volume) :
    (∫ x in Ω \ s, F x) + (∫ x in Ω ∩ s, F x) = ∫ x in Ω, F x :=
  (MeasureTheory.setIntegral_union disjoint_sdiff_inter (HasPDEDomain.is_open.measurableSet.inter hs)
    (hF.mono_set Set.sdiff_subset) (hF.mono_set Set.inter_subset_left)).symm.trans
    (congrArg (fun t => ∫ x in t, F x) (Set.sdiff_union_inter Ω s))

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

lemma tendsto_indicator_closedBall_zero_of_ne {F : E → ℝ} {x₀ x : E} (hx : x ≠ x₀) :
    Filter.Tendsto (fun ε => (Metric.closedBall x₀ ε).indicator F x) (𝓝[>] 0) (𝓝 0) :=
  tendsto_const_nhds.congr' <| nhdsWithin_le_nhds <|
    Filter.Eventually.mono (Iio_mem_nhds (dist_pos.mpr hx)) fun ε hε =>
      (Set.indicator_of_notMem (s := Metric.closedBall x₀ ε) (fun h => not_le.mpr hε (Metric.mem_closedBall.mp h)) F).symm

lemma ae_tendsto_indicator_closedBall_zero {F : E → ℝ} {Ω : Set E} {x₀ : E} :
    ∀ᵐ x ∂(volume.restrict Ω), Filter.Tendsto (fun ε => (Metric.closedBall x₀ ε).indicator F x) (𝓝[>] 0) (𝓝 0) :=
  MeasureTheory.ae_restrict_of_ae <|
    (ae_ne_singleton x₀).mono fun _ hx => tendsto_indicator_closedBall_zero_of_ne hx

lemma tendsto_setIntegral_inter_ball_zero {F : E → ℝ} {Ω : Set E} {x₀ : E}
    (hF : IntegrableOn F Ω volume) :
    Filter.Tendsto (fun ε => ∫ x in Ω ∩ Metric.closedBall x₀ ε, F x) (𝓝[>] 0) (𝓝 0) := by
  simp_rw [← MeasureTheory.setIntegral_indicator measurableSet_closedBall]
  simpa only [integral_zero] using MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun x => ‖F x‖)
    (hF_meas := Eventually.of_forall fun _ => hF.aestronglyMeasurable.indicator measurableSet_closedBall)
    (bound_integrable := hF.norm)
    (h_bound := Eventually.of_forall fun _ => Eventually.of_forall fun x => norm_indicator_le_norm_self F x)
    (h_lim := ae_tendsto_indicator_closedBall_zero)

lemma tendsto_setIntegral_punctured_of_integrable {F : E → ℝ} {Ω : Set E} {x₀ : E}
    [HasPDEDomain Ω] (hF : IntegrableOn F Ω volume) :
    Filter.Tendsto (fun ε => ∫ x in Ω \ Metric.closedBall x₀ ε, F x) (𝓝[>] 0) (𝓝 (∫ x in Ω, F x)) := by
  simp_rw [eq_sub_of_add_eq (setIntegral_diff_add_inter measurableSet_closedBall hF)]
  simpa only [sub_zero] using Filter.Tendsto.sub tendsto_const_nhds (tendsto_setIntegral_inter_ball_zero hF)
