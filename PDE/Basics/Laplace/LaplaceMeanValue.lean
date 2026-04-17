import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
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

noncomputable section

open Real Set MeasureTheory Metric Filter Function Pointwise InnerProductSpace
open scoped BigOperators Topology

-- 1. Space Definition: Euclidean R³
abbrev E := EuclideanSpace ℝ (Fin 3)

-- 2. Surface Measure: 2-dim Hausdorff measure
def surfaceArea : Measure E := Measure.hausdorffMeasure 2

def div_field (F : E → E) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ F x)

noncomputable def div_fieldWithin (F : E → E) (s : Set E) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderivWithin ℝ F s x)

noncomputable def laplacianWithin (u : E → ℝ) (s : Set E) (x : E) : ℝ :=
  div_fieldWithin (gradientWithin u s) s x

def laplacian (u : E → ℝ) (x : E) : ℝ :=
  div_field (gradient u) x

-- 4. Harmonicity: Δu = 0
def IsHarmonic (u : E → ℝ) (Ω : Set E) : Prop :=
  ∀ x ∈ Ω, laplacian u x = 0

def IsOutwardUnitNormal (s : Set E) (n : E → E) : Prop := sorry

class HasDivergenceTheoremDomain (s : Set E) : Prop

class HasPDEDomain (s : Set E) extends HasDivergenceTheoremDomain s where
  is_open : IsOpen s
  is_connected : IsConnected s
  unique_diff : UniqueDiffOn ℝ (closure s)

instance instHasPDEDomainBall (x₀ : E) (r : ℝ) (hr : 0 < r) : HasPDEDomain (Metric.ball x₀ r) := by
  sorry

instance ball_has_div_domain (x₀ : E) (r : ℝ) :
    HasDivergenceTheoremDomain (Metric.ball x₀ r) := by
  sorry

lemma ball_outward_normal (x₀ : E) (r : ℝ) :
    IsOutwardUnitNormal (Metric.ball x₀ r) (fun x => (1 / r) • (x - x₀)) := by
  sorry

noncomputable def sphericalParam (θ ϕ : ℝ) : E :=
  EuclideanSpace.equiv (Fin 3) ℝ |>.symm ![Real.sin ϕ * Real.cos θ, Real.sin ϕ * Real.sin θ, Real.cos ϕ]

lemma sphere_eq_image_sphericalParam :
    Metric.sphere (0 : E) 1 = (fun (p : ℝ × ℝ) ↦ sphericalParam p.1 p.2) '' (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 Real.pi) := by
  ext x
  simp only [Metric.mem_sphere, Set.mem_image, dist_zero_right, Set.mem_prod, Set.mem_Icc, Prod.exists]
  constructor
  · intro hx

    have h_norm : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
      have h_sq : ‖x‖ ^ 2 = 1 := by rw [hx, one_pow]
      have h_expand : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
        rw [← real_inner_self_eq_norm_sq x]
        simp only [inner]
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
        simp_all only [one_pow, Fin.isValue, RCLike.inner_apply, conj_trivial, Fin.succ_zero_eq_one,
          Fin.succ_one_eq_two]
        ring
      rw [h_expand] at h_sq
      exact h_sq

    let r_xy := Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
    let θ := if 0 ≤ x 1 then Real.arccos (x 0 / r_xy) else 2 * Real.pi - Real.arccos (x 0 / r_xy)
    let ϕ := Real.arccos (x 2)

    use θ, ϕ
    constructor
    · -- The bounds
      constructor
      · -- θ bounds
        constructor
        · -- 0 ≤ θ
          simp only [θ]
          split_ifs
          · exact Real.arccos_nonneg _
          · have h1 := Real.arccos_le_pi (x 0 / r_xy)
            have h2 := Real.pi_pos
            linarith
        · -- θ ≤ 2 * π
          simp only [θ]
          split_ifs
          · have h1 := Real.arccos_le_pi (x 0 / r_xy)
            have h2 := Real.pi_pos
            linarith
          · have h1 := Real.arccos_nonneg (x 0 / r_xy)
            linarith
      · -- ϕ bounds
        constructor
        · -- 0 ≤ ϕ
          exact Real.arccos_nonneg _
        · -- ϕ ≤ π
          exact Real.arccos_le_pi _
    ·
      ext i
      simp only [θ, ϕ, r_xy]
      unfold sphericalParam
      match i with
      | 0 =>
          -- Goal 0: x-coordinate
          simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply]
          simp
          rw [Real.sin_arccos]
          have h_sub : 1 - x 2 ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by linarith [h_norm]
          rw [h_sub]
          split_ifs with h1
          · -- Case 1: 0 ≤ x 1
            rw[Real.cos_arccos]
            -- Goal 1: The algebra
            · rcases eq_or_ne (√(x 0 ^ 2 + x 1 ^ 2)) 0 with hr | hr
              · -- Pole case (denominator is 0)
                have h1 : x 0 ^ 2 + x 1 ^ 2 = 0 := by
                  calc x 0 ^ 2 + x 1 ^ 2 = (√(x 0 ^ 2 + x 1 ^ 2)) ^ 2 := (Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))).symm
                    _ = 0 ^ 2 := by rw [hr]
                    _ = 0 := by ring
                have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), h1]
                rw [hr, hx0]
                ring
              · -- Standard case (denominator ≠ 0)
                rw [mul_comm]
                exact div_mul_cancel₀ (x 0) hr

            -- Goal 2: Lower bound (-1 ≤ x 0 / r_xy)
            · by_cases hr : √(x 0 ^ 2 + x 1 ^ 2) = 0
              · rw [hr, div_zero]; linarith
              · have hr_pos : 0 < √(x 0 ^ 2 + x 1 ^ 2) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
                rw [le_div_iff₀ hr_pos]
                have h_abs : |x 0| ≤ √(x 0 ^ 2 + x 1 ^ 2) := by
                  rw [← Real.sqrt_sq_eq_abs]
                  exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (x 1)])
                linarith [neg_le_abs (x 0), h_abs]

            -- Goal 3: Upper bound (x 0 / r_xy ≤ 1)
            · by_cases hr : √(x 0 ^ 2 + x 1 ^ 2) = 0
              · rw [hr, div_zero]; linarith
              · have hr_pos : 0 < √(x 0 ^ 2 + x 1 ^ 2) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
                rw [div_le_iff₀ hr_pos]
                have h_abs : |x 0| ≤ √(x 0 ^ 2 + x 1 ^ 2) := by
                  rw [← Real.sqrt_sq_eq_abs]
                  exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (x 1)])
                linarith [le_abs_self (x 0), h_abs]

          · -- Case 2: x 1 < 0
            have h_cos_shift : Real.cos (2 * Real.pi - Real.arccos (x 0 / √(x 0 ^ 2 + x 1 ^ 2))) = Real.cos (Real.arccos (x 0 / √(x 0 ^ 2 + x 1 ^ 2))) := by
              rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
              ring
            rw [h_cos_shift]
            rw [Real.cos_arccos]
            · rcases eq_or_ne (√(x 0 ^ 2 + x 1 ^ 2)) 0 with hr | hr
              · have h_zero_eq : x 0 ^ 2 + x 1 ^ 2 = 0 := by
                  calc x 0 ^ 2 + x 1 ^ 2 = (√(x 0 ^ 2 + x 1 ^ 2)) ^ 2 := (Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))).symm
                    _ = 0 ^ 2 := by rw [hr]
                    _ = 0 := by ring
                have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), h_zero_eq]
                rw [hr, hx0]
                ring
              · rw [mul_comm]
                exact div_mul_cancel₀ (x 0) hr
            · by_cases hr : √(x 0 ^ 2 + x 1 ^ 2) = 0
              · rw [hr, div_zero]; linarith
              · have hr_pos : 0 < √(x 0 ^ 2 + x 1 ^ 2) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
                rw [le_div_iff₀ hr_pos]
                have h_abs : |x 0| ≤ √(x 0 ^ 2 + x 1 ^ 2) := by
                  rw [← Real.sqrt_sq_eq_abs]
                  exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (x 1)])
                linarith [neg_le_abs (x 0), h_abs]
            · by_cases hr : √(x 0 ^ 2 + x 1 ^ 2) = 0
              · rw [hr, div_zero]; linarith
              · have hr_pos : 0 < √(x 0 ^ 2 + x 1 ^ 2) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
                rw [div_le_iff₀ hr_pos]
                have h_abs : |x 0| ≤ √(x 0 ^ 2 + x 1 ^ 2) := by
                  rw [← Real.sqrt_sq_eq_abs]
                  exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (x 1)])
                linarith [le_abs_self (x 0), h_abs]

      | 1 =>
          -- Goal 1: y-coordinate
          simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply]
          simp

          -- 1. Evaluate outer sin(arccos(x 2))
          rw [Real.sin_arccos]

          -- 2. Substitute 1 - x 2^2 with x 0^2 + x 1^2
          have h_sub : 1 - x 2 ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by linarith [h_norm]
          rw [h_sub]

          -- 3. Split the piecewise theta function
          split_ifs with h1
          · -- Case 1: 0 ≤ x 1
            rw [Real.sin_arccos]

            -- Goal 1.1: The algebra
            · rcases eq_or_ne (x 0 ^ 2 + x 1 ^ 2) 0 with hr2 | hr2
              · -- Pole case (denominator is 0)
                have hx1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), hr2]
                have hr_zero : √(x 0 ^ 2 + x 1 ^ 2) = 0 := by rw [hr2, Real.sqrt_zero]
                rw [hr_zero, hx1]
                ring
              · -- Standard case (denominator ≠ 0)
                have hr_pos : 0 < x 0 ^ 2 + x 1 ^ 2 := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hr2)
                have hr_sqrt_sq : (√(x 0 ^ 2 + x 1 ^ 2)) ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Real.sq_sqrt (le_of_lt hr_pos)

                -- Prove 1 - cos^2 = sin^2 algebraically
                have h_inner : 1 - (x 0 / √(x 0 ^ 2 + x 1 ^ 2)) ^ 2 = x 1 ^ 2 / (x 0 ^ 2 + x 1 ^ 2) := by
                  rw [div_pow, hr_sqrt_sq]
                  have : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := hr2
                  field_simp
                  ring

                rw [h_inner, Real.sqrt_div (sq_nonneg (x 1)), Real.sqrt_sq h1]
                rw [mul_comm]
                exact div_mul_cancel₀ (x 1) (by exact ne_of_gt (Real.sqrt_pos.mpr hr_pos))

          · -- Case 2: x 1 < 0
            -- 4. Shift the phase to remove 2π
            have h_sin_shift : Real.sin (2 * Real.pi - Real.arccos (x 0 / √(x 0 ^ 2 + x 1 ^ 2))) = - Real.sin (Real.arccos (x 0 / √(x 0 ^ 2 + x 1 ^ 2))) := by
              rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
              ring
            rw [h_sin_shift, Real.sin_arccos]

            -- Goal 2.1: The algebra
            · rcases eq_or_ne (x 0 ^ 2 + x 1 ^ 2) 0 with hr2 | hr2
              · -- Pole case
                have hx1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), hr2]
                have hr_zero : √(x 0 ^ 2 + x 1 ^ 2) = 0 := by rw [hr2, Real.sqrt_zero]
                rw [hr_zero, hx1]
                ring
              · -- Standard case
                have hr_pos : 0 < x 0 ^ 2 + x 1 ^ 2 := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hr2)
                have hr_sqrt_sq : (√(x 0 ^ 2 + x 1 ^ 2)) ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Real.sq_sqrt (le_of_lt hr_pos)

                have h_inner : 1 - (x 0 / √(x 0 ^ 2 + x 1 ^ 2)) ^ 2 = x 1 ^ 2 / (x 0 ^ 2 + x 1 ^ 2) := by
                  rw [div_pow, hr_sqrt_sq]
                  have : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := hr2
                  field_simp
                  ring

                rw [h_inner, Real.sqrt_div (sq_nonneg (x 1))]

                -- Since x 1 < 0, sqrt(x1^2) evaluates to -x1
                have hx1_neg : x 1 ≤ 0 := le_of_not_ge h1
                rw [Real.sqrt_sq_eq_abs, abs_of_nonpos hx1_neg]

                -- Goal is now: r_xy * - (-x 1 / r_xy) = x 1
                have h_cancel_neg : - (-x 1 / √(x 0 ^ 2 + x 1 ^ 2)) = x 1 / √(x 0 ^ 2 + x 1 ^ 2) := by ring
                rw [h_cancel_neg, mul_comm]
                exact div_mul_cancel₀ (x 1) (by exact ne_of_gt (Real.sqrt_pos.mpr hr_pos))

      | 2 =>
          -- Goal 2: z-coordinate
          simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply]
          simp
          have h_sq : x 2 ^ 2 ≤ 1 := by
            calc x 2 ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
                  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
              _ = 1 := h_norm
          apply Real.cos_arccos
          · nlinarith [h_sq]
          · nlinarith [h_sq]

  · rintro ⟨θ, ϕ, ⟨hθ_nonneg, hθ_le⟩, ⟨hϕ_nonneg, hϕ_le⟩, rfl⟩
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
    unfold sphericalParam
    simp only [one_pow]
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
    ring_nf
    have h1 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    have h2 : Real.sin ϕ ^ 2 + Real.cos ϕ ^ 2 = 1 := Real.sin_sq_add_cos_sq ϕ
    nlinarith

lemma area_formula_spherical :
    (surfaceArea (sphere (0 : E) 1)).toReal =
    ∫ (θ : ℝ) in Set.Icc 0 (2 * Real.pi), ∫ (ϕ : ℝ) in Set.Icc 0 Real.pi, Real.sin ϕ := by

  -- 1. The Pullback (The Area Formula)
  -- This represents the change of variables from the 2D manifold in 3D space
  -- to the flat 2D parameter space, incorporating the scaling factor sin(ϕ).
  have h_pullback : (surfaceArea (sphere (0 : E) 1)).toReal =
      ∫ p in (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 Real.pi), Real.sin p.2 ∂(MeasureTheory.Measure.hausdorffMeasure 2) := by
    -- Requires the Area Formula for manifolds and computing the Gram determinant.
    sorry

  -- 2. The Measure Bridge (Hausdorff to Lebesgue Volume)
  have h_measure_equiv : ∫ p in (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 Real.pi), Real.sin p.2 ∂(MeasureTheory.Measure.hausdorffMeasure 2) =
      ∫ p in (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 Real.pi), Real.sin p.2 ∂volume := by
    rw [MeasureTheory.hausdorffMeasure_prod_real]

  -- 3. Fubini/Tonelli's Theorem (Splitting the 2D volume into iterated 1D integrals)
  have h_fubini : ∫ p in (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 Real.pi), Real.sin p.2 ∂volume =
      ∫ (θ : ℝ) in Set.Icc 0 (2 * Real.pi), ∫ (ϕ : ℝ) in Set.Icc 0 Real.pi, Real.sin ϕ := by
    -- Uses Mathlib's `integral_prod`
    sorry

  rw [h_pullback, h_measure_equiv, h_fubini]

lemma unit_sphere_area_hausdorff : (surfaceArea (sphere (0 : E) 1)).toReal = 4 * π := by

  have h_domain : Metric.sphere (0 : E) 1 = (fun (p : ℝ × ℝ) ↦ sphericalParam p.1 p.2) ''
  (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 Real.pi) := sphere_eq_image_sphericalParam

--VERY DIFFICULT (need to bridge lebesgue measure to hausdorff)
  have h_area_formula : (surfaceArea (sphere (0 : E) 1)).toReal =
      ∫ (θ : ℝ) in Set.Icc 0 (2 * π), ∫ (ϕ : ℝ) in Set.Icc 0 π, Real.sin ϕ := by
    exact area_formula_spherical

  rw [h_area_formula]

  have h_inner_integral : ∫ (ϕ : ℝ) in Set.Icc 0 π, Real.sin ϕ = 2 := by
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le Real.pi_nonneg]
    rw [integral_sin]
    simp; ring

  simp_rw [h_inner_integral]

  have h_outer_integral : ∫ (θ : ℝ) in Set.Icc 0 (2 * π), (2 : ℝ) = 4 * π := by
    rw [setIntegral_const]
    have h_bounds : (0 : ℝ) ≤ 2 * π := by positivity
    simp_all only [Icc_prod_Icc, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
      volume_real_Icc, sub_zero, sup_of_le_left, smul_eq_mul, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    ring

  exact h_outer_integral

lemma surface_area_sphere_three_dim (r : ℝ) (hr_pos : 0 < r) :
    ∫ x in sphere (0 : E) r, 1 ∂surfaceArea = 4 * π * r^2 := by

  -- Step 1: Relate sphere 0 r to sphere 0 1 via scaling
  have h_scaling : sphere (0 : E) r = (fun y => r • y) '' sphere (0 : E) 1 := by
    ext x
    simp only [Metric.mem_sphere, Set.mem_image, dist_zero_right]
    constructor
    · intro hx
      use r⁻¹ • x
      constructor
      · simp [norm_smul, abs_of_pos hr_pos, hx, inv_mul_cancel₀ hr_pos.ne']
      · simp [smul_smul, mul_inv_cancel₀ hr_pos.ne']
    · rintro ⟨y, hy, rfl⟩
      simp [norm_smul, abs_of_pos hr_pos, hy]

  -- Step 2: Use Hausdorff measure scaling for homothety
  have h_measure_scaling : surfaceArea (sphere (0 : E) r) =
          ENNReal.ofReal (r^2) * surfaceArea (sphere (0 : E) 1) := by
        unfold surfaceArea
        rw [h_scaling]

        have h := MeasureTheory.hausdorffMeasure_homothety_image
                    (by norm_num : (0:ℝ) ≤ 2) (0:E) (hr_pos.ne') (sphere (0:E) 1)

        have h_affine : (fun y => r • y) '' sphere (0:E) 1 =
                        AffineMap.homothety (0:E) r '' sphere (0:E) 1 := by
          ext x; simp [AffineMap.homothety_apply]

        rw [h_affine, h]

        rw [ENNReal.smul_def, smul_eq_mul]
        congr 1
        rw [nnnorm_of_nonneg hr_pos.le]
        rw [ENNReal.ofReal_pow hr_pos.le]
        rw [ENNReal.ofReal_eq_coe_nnreal hr_pos.le]
        simp[ENNReal.coe_pow]


  -- Step 3: Convert integral to measure directly
  rw [setIntegral_const]
  rw [smul_eq_mul, mul_one]
  unfold Measure.real
  rw [h_measure_scaling]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (sq_nonneg r)]

  -- Step 5: The fundamental constant
  suffices h_unit : (surfaceArea (sphere (0 : E) 1)).toReal = 4 * π by
    rw [h_unit]
    ring

  unfold surfaceArea
  exact unit_sphere_area_hausdorff

lemma measure_sphere_scaling (r : ℝ) (hr_pos : 0 < r) :
    surfaceArea (sphere (0 : E) r) = ENNReal.ofReal (r^2) * surfaceArea (sphere (0 : E) 1) := by
  have h_scaling : sphere (0 : E) r = (fun y => r • y) '' sphere (0 : E) 1 := by
    ext x
    simp only [Metric.mem_sphere, Set.mem_image, dist_zero_right]
    constructor
    · intro hx
      use r⁻¹ • x
      constructor
      · simp [norm_smul, abs_of_pos hr_pos, hx, inv_mul_cancel₀ hr_pos.ne']
      · simp [smul_smul, mul_inv_cancel₀ hr_pos.ne']
    · rintro ⟨y, hy, rfl⟩
      simp [norm_smul, abs_of_pos hr_pos, hy]
  unfold surfaceArea
  rw [h_scaling]
  have h := MeasureTheory.hausdorffMeasure_homothety_image (by norm_num : (0:ℝ) ≤ 2) (0:E) (hr_pos.ne') (sphere (0:E) 1)
  have h_affine : (fun y => r • y) '' sphere (0:E) 1 = AffineMap.homothety (0:E) r '' sphere (0:E) 1 := by
    ext x; simp [AffineMap.homothety_apply]
  rw [h_affine, h]
  rw [ENNReal.smul_def, smul_eq_mul]
  congr 1
  rw [nnnorm_of_nonneg hr_pos.le]
  rw [ENNReal.ofReal_pow hr_pos.le]
  rw [ENNReal.ofReal_eq_coe_nnreal hr_pos.le]
  simp [ENNReal.coe_pow]

lemma measure_sphere_lt_top (r : ℝ) (hr_pos : 0 < r) :
    surfaceArea (sphere (0 : E) r) < ⊤ := by
  rw [measure_sphere_scaling r hr_pos]
  sorry

lemma isFiniteMeasure_sphere (r : ℝ) (hr_pos : 0 < r) :
    IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) r)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  exact measure_sphere_lt_top r hr_pos

-- 5. Lemma A.7.1 (Averaging Lemma)
theorem averaging_lemma_spherical (R₀ : ℝ) (hR₀ : 0 < R₀)
    (phi : E → ℝ)
    (h_cont : ContinuousOn phi (Metric.ball 0 R₀)) :
    Filter.Tendsto (fun r => (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, phi x ∂surfaceArea) (𝓝[>] 0) (𝓝 (phi 0)) := by
  -- "Proof. Let 𝜖 > 0..."
  -- We start by unfolding the definition of the limit to match the epsilon-delta structure of the text.
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε

  -- "...and note that 𝜙(0) = (1/4𝜋𝑟²) ∫_𝜕𝐵(0,𝑟) 𝜙(0) 𝑑𝑆."
  have h_phi_0_identity : ∀ r > 0, phi 0 = (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, phi 0 ∂surfaceArea := by
    intro r hr
    rw [setIntegral_const]
    unfold Measure.real

    have h_area : (surfaceArea (sphere 0 r)).toReal = 4 * π * r^2 := by
      rw [← surface_area_sphere_three_dim r hr]
      rw [setIntegral_const]
      simp_all only [gt_iff_lt, smul_eq_mul, mul_one]
      rfl


    rw [h_area]
    rw [smul_eq_mul]

    have h_nonzero : 4 * π * r ^ 2 ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) (pow_ne_zero 2 hr.ne')
    field_simp [h_nonzero]

  -- "We want to show that there exists 𝛿 > 0 such that if 𝑟 < 𝛿, then..."
  -- "|| (1/4𝜋𝑟²) ∫... - 𝜙(0) || < 𝜖."
  have h_continuity_delta : ∃ δ > 0, δ ≤ R₀ ∧ ∀ x, dist x 0 < δ → dist (phi x) (phi 0) < ε := by
    have h_cont_at_0 : ContinuousAt phi 0 :=
      h_cont.continuousAt (isOpen_ball.mem_nhds (Metric.mem_ball_self hR₀))
    rw [Metric.continuousAt_iff] at h_cont_at_0
    obtain ⟨δ₁, hδ₁_pos, hδ₁_cont⟩ := h_cont_at_0 ε hε
    use min δ₁ R₀
    constructor
    · exact lt_min hδ₁_pos hR₀
    · constructor
      · exact min_le_right δ₁ R₀
      · intro x hx
        -- hδ₁_cont takes the point implicitly, so we only pass the proof
        exact hδ₁_cont (hx.trans_le (min_le_left δ₁ R₀))

  obtain ⟨δ, hδ_pos, hδ_le_R₀, hδ_cont⟩ := h_continuity_delta
  use δ
  constructor
  · exact hδ_pos
  · intro r hr_pos hr_dist
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hr_pos] at hr_dist
    have hr_lt_delta : r < δ := hr_dist
    have hr_lt_R₀ : r < R₀ := hr_lt_delta.trans_le hδ_le_R₀

    -- The text performs a chain of inequalities. We replicate them step-by-step.

    -- Step 1: Combine the integrals
    -- "|| (1/4𝜋𝑟²) ∫ (𝜙(x) - 𝜙(0)) 𝑑𝑆 ||"
    have step1 : dist ((1 / (4 * π * r^2)) * ∫ x in sphere 0 r, phi x ∂surfaceArea) (phi 0) =
                 abs ((1 / (4 * π * r^2)) * ∫ x in sphere 0 r, (phi x - phi 0) ∂surfaceArea) := by
      conv_lhs => rw [h_phi_0_identity r hr_pos]
      rw [dist_eq_norm, Real.norm_eq_abs]
      rw [← mul_sub]
      rw [← integral_sub]

      · have h_subset : sphere (0 : E) r ⊆ ball (0 : E) R₀ := by
          intro x hx
          rw [mem_sphere] at hx
          rw [mem_ball]
          exact hx.symm ▸ hr_lt_R₀
        have h_cont_sphere : ContinuousOn phi (sphere (0 : E) r) := h_cont.mono h_subset
        have h_compact : IsCompact (sphere (0 : E) r) := isCompact_sphere (0 : E) r
        haveI : IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) r)) := isFiniteMeasure_sphere r hr_pos
        have h_bound : ∃ C : ℝ, ∀ x ∈ sphere (0 : E) r, ‖phi x‖ ≤ C := by
          have h_cont_norm : ContinuousOn (fun x ↦ ‖phi x‖) (sphere (0 : E) r) := h_cont_sphere.norm
          obtain ⟨C, hC⟩ := h_compact.bddAbove_image h_cont_norm
          use C
          intro x hx
          exact hC (Set.mem_image_of_mem _ hx)
        have h_meas : AEStronglyMeasurable phi (surfaceArea.restrict (sphere (0 : E) r)) := by
          exact ContinuousOn.aestronglyMeasurable h_cont_sphere isClosed_sphere.measurableSet

        obtain ⟨C, hC⟩ := h_bound
        have h_int_C : Integrable (fun _ : E ↦ (C : ℝ)) (surfaceArea.restrict (sphere (0 : E) r)) := integrable_const C
        refine MeasureTheory.Integrable.mono h_int_C h_meas ?_
        rw [MeasureTheory.ae_restrict_iff' isClosed_sphere.measurableSet]
        exact Eventually.of_forall fun x hx ↦ by
          rw [Real.norm_eq_abs]
          exact (hC x hx).trans (le_abs_self C)

      · haveI : IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) r)) := isFiniteMeasure_sphere r hr_pos
        exact integrable_const (phi 0)

    -- Step 2: Move absolute value inside
    -- "≤ (1/4𝜋𝑟²) ∫ |𝜙(x) - 𝜙(0)| 𝑑𝑆"
    have step2 : abs ((1 / (4 * π * r^2)) * ∫ x in sphere 0 r, (phi x - phi 0) ∂surfaceArea) ≤
                 (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, abs (phi x - phi 0) ∂surfaceArea := by
      -- 1. Split the absolute value: |c * I| = |c| * |I|
      rw [abs_mul]

      -- 2. Simplify the constant: Since 1/(4πr²) > 0, |c| = c
      have h_c_pos : 0 < 1 / (4 * π * r^2) := by
        apply one_div_pos.mpr
        apply mul_pos
        · apply mul_pos (by norm_num) pi_pos
        · apply pow_pos hr_pos 2
      rw [abs_of_pos h_c_pos]

      -- 3. Multiply the standard inequality by the non-negative constant
      apply mul_le_mul_of_nonneg_left
      · simp_rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm (fun x ↦ phi x - phi 0)
      · exact h_c_pos.le


    -- Step 3: Bound by epsilon
    -- "< (1/4𝜋𝑟²) ∫ 𝜖 𝑑𝑆"
    have step3 : (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, abs (phi x - phi 0) ∂surfaceArea <
                 (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, ε ∂surfaceArea := by

      -- 1. Declare constants and finite measure typeclass at the top level of step3
      have h_c_pos : 0 < 1 / (4 * π * r^2) := by
        apply one_div_pos.mpr
        apply mul_pos
        · apply mul_pos (by norm_num) pi_pos
        · apply pow_pos hr_pos 2

      have h_finite_meas : surfaceArea (sphere 0 r) < ⊤ := by exact measure_sphere_lt_top _ hr_pos

      haveI : IsFiniteMeasure (surfaceArea.restrict (sphere 0 r)) := by
        constructor
        rw [Measure.restrict_apply MeasurableSet.univ]
        rw [Set.univ_inter]
        exact h_finite_meas

      have h_int_rhs : IntegrableOn (fun _ ↦ ε) (sphere 0 r) surfaceArea := by
        exact integrable_const ε

      -- 2. Proceed with the continuity and bound extraction for LHS
      have h_int_lhs : IntegrableOn (fun x ↦ abs (phi x - phi 0)) (sphere 0 r) surfaceArea := by
        have h_cont_abs : ContinuousOn (fun x ↦ abs (phi x - phi 0)) (sphere 0 r) := by
          apply ContinuousOn.abs
          apply ContinuousOn.sub
          · apply h_cont.mono
            intro x hx
            rw [Metric.mem_sphere] at hx
            subst hx
            simp_all only [gt_iff_lt, one_div, mul_inv_rev, integral_const, MeasurableSet.univ,
              measureReal_restrict_apply, univ_inter, smul_eq_mul, dist_zero_right, mem_Ioi, norm_pos_iff, ne_eq,
              mem_ball]
          · exact continuousOn_const

        obtain ⟨C, hC⟩ := (isCompact_sphere 0 r).exists_bound_of_continuousOn h_cont_abs
        apply Integrable.of_bound (C := C)
        · exact h_cont_abs.aestronglyMeasurable isClosed_sphere.measurableSet
        · filter_upwards [self_mem_ae_restrict isClosed_sphere.measurableSet] with x hx
          exact hC x hx

      -- 3. Prove area is positive
      have h_meas_pos : 0 < surfaceArea (sphere 0 r) := by
        have h_area : (surfaceArea (sphere 0 r)).toReal = 4 * π * r^2 := by
          rw [← surface_area_sphere_three_dim r hr_pos]
          rw [setIntegral_const]
          simp_all only [gt_iff_lt, smul_eq_mul, mul_one]
          rfl
        have h_pos : 0 < 4 * π * r^2 := by
          apply mul_pos
          · apply mul_pos (by norm_num) pi_pos
          · apply pow_pos hr_pos 2
        apply lt_of_le_of_ne (zero_le _)
        intro h_zero
        rw [← h_zero] at h_area
        have h_zero_real : (0 : ENNReal).toReal = 0 := rfl
        rw [h_zero_real] at h_area
        rw [← h_area] at h_pos
        exact lt_irrefl 0 h_pos

      have h_bound : ∀ x ∈ sphere 0 r, abs (phi x - phi 0) < ε := by
        intro x hx
        have h_dist : dist x 0 < δ := by
          rw [Metric.mem_sphere] at hx
          rw [hx]
          exact hr_lt_delta
        have h_dist_phi := hδ_cont x h_dist
        rw [Real.dist_eq] at h_dist_phi
        exact h_dist_phi
      -- 4. Combine integrals for strict inequality
      have h_integral_lt : ∫ x in sphere 0 r, abs (phi x - phi 0) ∂surfaceArea <
                           ∫ x in sphere 0 r, ε ∂surfaceArea := by
        rw [← sub_pos]
        rw [← integral_sub h_int_rhs h_int_lhs]

        have h_nonneg : 0 ≤ᵐ[surfaceArea.restrict (sphere 0 r)] (fun x ↦ ε - abs (phi x - phi 0)) := by
          filter_upwards [self_mem_ae_restrict isClosed_sphere.measurableSet] with x hx
          exact sub_nonneg.mpr (h_bound x hx).le

        have h_int_diff : IntegrableOn (fun x ↦ ε - abs (phi x - phi 0)) (sphere 0 r) surfaceArea :=
          Integrable.sub h_int_rhs h_int_lhs

        rw [integral_pos_iff_support_of_nonneg_ae h_nonneg h_int_diff]

        have h_supp_eq : (surfaceArea.restrict (sphere 0 r)) (Function.support (fun x ↦ ε - abs (phi x - phi 0))) = surfaceArea (sphere 0 r) := by
          rw [Measure.restrict_apply' isClosed_sphere.measurableSet]
          have h_inter : Function.support (fun x ↦ ε - abs (phi x - phi 0)) ∩ sphere 0 r = sphere 0 r := by
            apply Set.inter_eq_right.mpr
            intro x hx
            rw [Function.mem_support]
            exact (sub_pos.mpr (h_bound x hx)).ne'
          rw [h_inter]

        rw [h_supp_eq]
        exact h_meas_pos

      exact mul_lt_mul_of_pos_left h_integral_lt h_c_pos

    -- Step 4: Pull epsilon out and evaluate integral of 1
    -- "= 𝜖 (1/4𝜋𝑟²) ∫ 1 𝑑𝑆"
    have step4 : (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, ε ∂surfaceArea =
                 ε * ((1 / (4 * π * r^2)) * ∫ x in sphere 0 r, 1 ∂surfaceArea) := by
      simp; ring


    -- Step 5: Cancel terms
    -- "= 𝜖 (1/4𝜋𝑟²) (4𝜋𝑟²) = 𝜖"
    have step5 : ε * ((1 / (4 * π * r^2)) * ∫ x in sphere 0 r, 1 ∂surfaceArea) = ε := by
      have h_area : ∫ x in sphere 0 r, 1 ∂surfaceArea = 4 * π * r^2 := by
        rw [← surface_area_sphere_three_dim r hr_pos]

      rw [h_area]
      have h_denom : 4 * π * r^2 ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) (pow_ne_zero 2 hr_pos.ne')
      field_simp [(mem_Ioi.mp hr_pos).ne']

    -- Combine steps to prove strict inequality < ε
    calc
      dist ((1 / (4 * π * r^2)) * ∫ x in sphere 0 r, phi x ∂surfaceArea) (phi 0)
        = abs ((1 / (4 * π * r^2)) * ∫ x in sphere 0 r, (phi x - phi 0) ∂surfaceArea) := step1
      _ ≤ (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, abs (phi x - phi 0) ∂surfaceArea := step2
      _ < (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, ε ∂surfaceArea := step3
      _ = ε := by rw [step4, step5]

lemma averaging_lemma_spherical_translated (R₀ : ℝ) (hR₀ : 0 < R₀)
    (phi : E → ℝ) (x₀ : E)
    (h_cont : ContinuousOn phi (Metric.ball x₀ R₀)) :
    Filter.Tendsto (fun r ↦ (1 / (4 * π * r^2)) * ∫ x in sphere x₀ r, phi x ∂surfaceArea) (𝓝[>] 0) (𝓝 (phi x₀)) := by

  let psi := fun x ↦ phi (x + x₀)
  have h_cont_psi : ContinuousOn psi (Metric.ball 0 R₀) := by
    have h_mapsTo : Set.MapsTo (fun x ↦ x + x₀) (Metric.ball 0 R₀) (Metric.ball x₀ R₀) := by
      intro x hx
      simp only [Metric.mem_ball, dist_eq_norm] at hx ⊢
      rw [add_sub_cancel_right]
      simpa using hx
    exact ContinuousOn.comp h_cont (continuous_add_right x₀).continuousOn h_mapsTo

  have h_base := averaging_lemma_spherical R₀ hR₀ psi h_cont_psi
  have h_integral_eq : ∀ r ∈ Set.Ioo 0 R₀, ∫ x in sphere x₀ r, phi x ∂surfaceArea = ∫ x in sphere 0 r, psi x ∂surfaceArea := by
    intro r hr
    let g : E ≃ᵢ E := IsometryEquiv.addRight x₀
    have hg_iso : Isometry g := isometry_add_right x₀
    have hg_surj : Function.Surjective g := fun y ↦ ⟨y - x₀, sub_add_cancel y x₀⟩
    have h_preimage : g ⁻¹' (sphere x₀ r) = sphere 0 r := by
      ext x
      simp only [g, Set.mem_preimage, Metric.mem_sphere, dist_eq_norm]
      change ‖x + x₀ - x₀‖ = r ↔ ‖x - 0‖ = r
      rw [add_sub_cancel_right, sub_zero]

    -- B. Utilize your discovered theorem to prove the measure maps perfectly.
    -- (surfaceArea is defined as hausdorffMeasure)
    have h_map_measure : MeasureTheory.Measure.map g surfaceArea = surfaceArea := by
      erw [Isometry.map_hausdorffMeasure hg_iso (Or.inr hg_surj)]
      rw [hg_surj.range_eq]
      exact MeasureTheory.Measure.restrict_univ

    -- C. Apply the change of variables formula for mapped measures
    have h_cov : ∫ x in sphere x₀ r, phi x ∂surfaceArea = ∫ y in g ⁻¹' (sphere x₀ r), phi (g y) ∂surfaceArea := by
      rw [← h_map_measure]
      have hg_emb : MeasurableEmbedding g := (Homeomorph.addRight x₀).measurableEmbedding
      have hg_meas : Measurable g := hg_emb.measurable
      have hs_meas : MeasurableSet (sphere x₀ r) := isClosed_sphere.measurableSet
      change ∫ x, phi x ∂((MeasureTheory.Measure.map g surfaceArea).restrict (sphere x₀ r)) = _
      rw [MeasureTheory.Measure.restrict_map hg_meas hs_meas]
      rw [hg_emb.integral_map]
      rw [h_map_measure]


    rw [h_cov, h_preimage]
    rfl

  have h_fun_eq : (fun r ↦ (1 / (4 * π * r^2)) * ∫ x in sphere x₀ r, phi x ∂surfaceArea) =ᶠ[𝓝[>] 0]
                  (fun r ↦ (1 / (4 * π * r^2)) * ∫ x in sphere 0 r, psi x ∂surfaceArea) := by
    rw [Filter.EventuallyEq, nhdsWithin, Filter.eventually_inf_principal]

    filter_upwards [isOpen_Iio.mem_nhds hR₀] with r hr_lt hr_pos
    rw [h_integral_eq r ⟨hr_pos, hr_lt⟩]

  have h_val_eq : psi 0 = phi x₀ := by
    dsimp [psi]
    rw [zero_add]
  rw [← h_val_eq]
  exact Filter.Tendsto.congr' h_fun_eq.symm h_base

lemma integral_sphere_change_vars (x₀ : E) (r : ℝ) (hr : 0 < r) (u : E → ℝ) :
    ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea =
    r ^ 2 * ∫ (y : E) in sphere 0 1, u (x₀ + r • y) ∂surfaceArea := by

  -- 1. Define the topological equivalences (Scaling and Translation)
  -- Scaling by r (since r > 0, this is a homeomorphism)
  let e_scale : E ≃ₜ E := Homeomorph.smulOfNeZero r hr.ne'
  -- Translating by x₀
  let e_trans : E ≃ₜ E := Homeomorph.addRight x₀
  -- The full affine transformation y ↦ x₀ + r • y
  let e_affine : E ≃ₜ E := e_scale.trans e_trans

  -- 2. Prove the domains match under the transformation
  have h_domain : e_affine ⁻¹' (sphere x₀ r) = sphere 0 1 := by
    -- This is a straightforward algebraic set equivalence
    ext y
    simp_all only [mem_preimage, Homeomorph.trans_apply, Homeomorph.smulOfNeZero_apply, Homeomorph.coe_addRight,
      mem_sphere_iff_norm, add_sub_cancel_right, sub_zero, e_affine, e_scale, e_trans]
    apply Iff.intro
    · intro a
      rw [norm_smul, Real.norm_of_nonneg hr.le] at a
      apply mul_left_cancel₀ hr.ne'
      rw [a, mul_one]
    · intro a
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      rw [a, mul_one]

  -- 3. THE FIX: The measure scale is actually (r^2)⁻¹.
  have h_measure_scale : MeasureTheory.Measure.map e_affine surfaceArea =
                         (ENNReal.ofReal ((r^2)⁻¹)) • surfaceArea := by
    have h_meas_scale : Measurable e_scale := e_scale.continuous.measurable
    have h_meas_trans : Measurable e_trans := e_trans.continuous.measurable

    change MeasureTheory.Measure.map (e_trans ∘ e_scale) surfaceArea = _
    rw [← MeasureTheory.Measure.map_map h_meas_trans h_meas_scale]

    have h_map_scale : MeasureTheory.Measure.map e_scale surfaceArea = (ENNReal.ofReal ((r^2)⁻¹)) • surfaceArea := by
      ext s hs
      rw [MeasureTheory.Measure.map_apply h_meas_scale hs]
      rw [MeasureTheory.Measure.smul_apply]

      have h_preimage : e_scale ⁻¹' s = r⁻¹ • s := by
        ext w
        simp only [Set.mem_preimage, Set.mem_smul_set]
        constructor
        · intro hw
          use r • w
          refine ⟨hw, ?_⟩
          rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
        · rintro ⟨v, hv, rfl⟩
          change r • (r⁻¹ • v) ∈ s
          rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
          exact hv
      rw [h_preimage]

      have hd : 0 ≤ (2 : ℝ) := by positivity
      change (MeasureTheory.Measure.hausdorffMeasure 2) (r⁻¹ • s) = _
      rw [MeasureTheory.Measure.hausdorffMeasure_smul₀ hd (inv_ne_zero hr.ne') s]

      congr 1
      have hr_inv : (‖r⁻¹‖₊ : ℝ) = r⁻¹ := Real.norm_of_nonneg (inv_nonneg.mpr hr.le)
      simp_all only [Homeomorph.smulOfNeZero_apply, Homeomorph.coe_addRight, Nat.ofNat_nonneg, nnnorm_inv,
        NNReal.coe_inv, coe_nnnorm, norm_eq_abs, inv_inj, abs_eq_self, NNReal.rpow_ofNat, inv_pow, e_affine, e_scale,
        e_trans]
      ext : 1
      simp_all only [NNReal.coe_inv, NNReal.coe_pow, coe_nnnorm, norm_eq_abs, sq_abs, coe_toNNReal', inv_nonneg,
        pow_succ_nonneg, sup_of_le_left]

    rw [h_map_scale]

    rw [MeasureTheory.Measure.map_smul]

    have h_trans_iso : Isometry e_trans := IsometryEquiv.isometry (IsometryEquiv.addRight x₀)
    erw [Isometry.map_hausdorffMeasure h_trans_iso]

    rw [e_trans.surjective.range_eq]
    simp_all only [Homeomorph.smulOfNeZero_apply, Homeomorph.coe_addRight, Measure.restrict_univ, e_affine, e_scale,
      e_trans]
    rfl;simp

  -- 4. THE FIX: The mapped measure belongs on the TARGET side (the x side).
  have h_cov : ∫ (x : E) in sphere x₀ r, u x ∂(MeasureTheory.Measure.map e_affine surfaceArea) =
               ∫ (y : E) in e_affine ⁻¹' (sphere x₀ r), u (e_affine y) ∂surfaceArea := by
    have hg_emb : MeasurableEmbedding e_affine := e_affine.measurableEmbedding
    change ∫ x, u x ∂((MeasureTheory.Measure.map e_affine surfaceArea).restrict (sphere x₀ r)) = _
    rw [MeasureTheory.Measure.restrict_map hg_emb.measurable isClosed_sphere.measurableSet]
    rw [hg_emb.integral_map]

  rw [h_measure_scale, h_domain] at h_cov

  -- 6. Pull the scalar OUT of the integral on the left side
  have h_pull_scalar : ∫ (x : E) in sphere x₀ r, u x ∂((ENNReal.ofReal ((r^2)⁻¹)) • surfaceArea) =
                         (r^2)⁻¹ * ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea := by
      rw [MeasureTheory.Measure.restrict_smul]
      rw [MeasureTheory.integral_smul_measure]
      have h_nonneg : 0 ≤ (r^2)⁻¹ := by positivity
      rw [ENNReal.toReal_ofReal h_nonneg]
      rfl

  -- 7. Conclude the proof algebraically!
  -- First, cleanly swap `u (e_affine y)` for `u (x₀ + r • y)`
  have h_integrand_eq : (fun y ↦ u (e_affine y)) = (fun y ↦ u (x₀ + r • y)) := by
    ext y
    change u (r • y + x₀) = u (x₀ + r • y)
    rw [add_comm]
  rw [h_integrand_eq] at h_cov
  rw [h_pull_scalar] at h_cov
  have h_sq_ne_zero : r ^ 2 ≠ 0 := by positivity
  rw [← h_cov]
  rw [← mul_assoc, mul_inv_cancel₀ h_sq_ne_zero, one_mul]

lemma continuousOn_spherical_mean (u : E → ℝ) (x₀ : E) (R : ℝ)
    (h_cont_u : ContinuousOn u (Metric.closedBall x₀ R)) :
    ContinuousOn (fun r ↦ 1 / (4 * π * r ^ 2) * ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea) (Set.Ioc 0 R) := by

  have h_phi_alt : Set.EqOn (fun r ↦ 1 / (4 * π * r ^ 2) * ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea)
      (fun r ↦ (1 / (4 * π)) * ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea) (Set.Ioc 0 R) := by
    intro r hr
    have hr_pos : 0 < r := hr.1
    have hr_sq_ne_zero : r ^ 2 ≠ 0 := pow_ne_zero 2 hr_pos.ne'
    dsimp
    rw [integral_sphere_change_vars x₀ r hr_pos u]
    calc
      1 / (4 * π * r ^ 2) * (r ^ 2 * ∫ (y : E) in sphere 0 1, u (x₀ + r • y) ∂surfaceArea)
        = (1 / (4 * π * r ^ 2) * r ^ 2) * ∫ (y : E) in sphere 0 1, u (x₀ + r • y) ∂surfaceArea := by
        rw [mul_assoc]; linarith
      _ = 1 / (4 * π) * ∫ (y : E) in sphere 0 1, u (x₀ + r • y) ∂surfaceArea := by
        congr 1
        calc
          1 / (4 * π * r ^ 2) * r ^ 2 = (1 / (4 * π)) * (1 / r ^ 2) * r ^ 2 := by ring
          _ = 1 / (4 * π) := by rw [mul_assoc, one_div_mul_cancel hr_sq_ne_zero, mul_one]

  refine ContinuousOn.congr ?_ h_phi_alt
  apply ContinuousOn.mul continuousOn_const

  have h_param_integral : ContinuousOn (fun r ↦ ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea) (Set.Ioc 0 R) := by
    intro r hr
    have h_bound : ∃ M : ℝ, ∀ x ∈ Metric.closedBall x₀ R, ‖u x‖ ≤ M := by
      have h_compact_ball : IsCompact (Metric.closedBall x₀ R) := by
        simpa using isCompact_closedBall _ _
      have h_cont_norm : ContinuousOn (fun x ↦ ‖u x‖) (Metric.closedBall x₀ R) := by
        exact ContinuousOn.norm h_cont_u
      have h_compact_image : IsCompact ((fun x ↦ ‖u x‖) '' Metric.closedBall x₀ R) := by
        exact IsCompact.image_of_continuousOn h_compact_ball h_cont_norm
      have h_bdd_above : BddAbove ((fun x ↦ ‖u x‖) '' Metric.closedBall x₀ R) := by
        exact h_compact_image.bddAbove
      rcases h_bdd_above with ⟨M, hM⟩
      use M
      intro x hx
      exact hM (Set.mem_image_of_mem _ hx)
    obtain ⟨M, hM⟩ := h_bound

    have h_cont_integrand : ∀ᵐ y ∂(surfaceArea.restrict (sphere 0 1)), ContinuousWithinAt (fun r' ↦ u (x₀ + r' • y)) (Set.Ioc 0 R) r := by
      rw [ae_restrict_iff' isClosed_sphere.measurableSet]
      apply Eventually.of_forall
      intro y hy
      have h_mapsTo : Set.MapsTo (fun r' ↦ x₀ + r' • y) (Set.Ioc 0 R) (Metric.closedBall x₀ R) := by
        intro r' hr'
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h_simp : x₀ + r' • y - x₀ = r' • y := by simp
        rw [h_simp, norm_smul]
        have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
        rw [hy_norm, mul_one, Real.norm_of_nonneg hr'.1.le]
        exact hr'.2
      have h_cont_affine : ContinuousWithinAt (fun r' ↦ x₀ + r' • y) (Set.Ioc 0 R) r := by
        exact (continuous_const.add (continuous_id.smul continuous_const)).continuousWithinAt
      exact ContinuousWithinAt.comp (h_cont_u _ (h_mapsTo hr)) h_cont_affine h_mapsTo

    have h_meas_integrand : ∀ r' ∈ Set.Ioc 0 R, AEStronglyMeasurable (fun y ↦ u (x₀ + r' • y)) (surfaceArea.restrict (sphere 0 1)) := by
      intro r' hr'
      have h_mapsTo_y : Set.MapsTo (fun y ↦ x₀ + r' • y) (sphere 0 1) (Metric.closedBall x₀ R) := by
        intro y hy
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h_simp : x₀ + r' • y - x₀ = r' • y := by simp
        rw [h_simp, norm_smul]
        have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
        rw [hy_norm, mul_one, Real.norm_of_nonneg hr'.1.le]
        exact hr'.2
      have h_cont_affine_y : Continuous (fun y ↦ x₀ + r' • y) := by
        exact continuous_const.add (continuous_const.smul continuous_id)
      have h_cont_comp : ContinuousOn (fun y ↦ u (x₀ + r' • y)) (sphere 0 1) := by
        exact ContinuousOn.comp h_cont_u h_cont_affine_y.continuousOn h_mapsTo_y
      exact h_cont_comp.aestronglyMeasurable isClosed_sphere.measurableSet

    have h_bound_integrable : IntegrableOn (fun _ ↦ M) (sphere 0 1) surfaceArea := by
      have h_area : (surfaceArea (sphere 0 1)).toReal = 4 * π := unit_sphere_area_hausdorff
      have h_ne_top : surfaceArea (sphere 0 1) ≠ ⊤ := by
        intro h_top
        have h_zero : (surfaceArea (sphere 0 1)).toReal = 0 := by
          rw [h_top]; simp_all only [one_div, mul_inv_rev, mem_Ioc, mem_closedBall, norm_eq_abs, and_imp,
            ENNReal.toReal_top, zero_eq_mul, OfNat.ofNat_ne_zero, pi_ne_zero, or_self]
        rw [h_zero] at h_area
        have h_pi_pos : (0 : ℝ) < 4 * π := by positivity
        linarith
      have h_lt_top : surfaceArea (sphere 0 1) < ⊤ := lt_top_iff_ne_top.mpr h_ne_top
      haveI : IsFiniteMeasure (surfaceArea.restrict (sphere 0 1)) := ⟨by simpa using h_lt_top⟩
      exact integrable_const M

    have h_dominate : ∀ r' ∈ Set.Ioc 0 R, ∀ᵐ y ∂(surfaceArea.restrict (sphere 0 1)), ‖u (x₀ + r' • y)‖ ≤ M := by
      intro r' hr'
      rw [ae_restrict_iff' isClosed_sphere.measurableSet]
      apply Eventually.of_forall
      intro y hy
      apply hM
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h_simp : x₀ + r' • y - x₀ = r' • y := by simp
      rw [h_simp, norm_smul]
      have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
      rw [hy_norm, mul_one, Real.norm_of_nonneg hr'.1.le]
      exact hr'.2

    exact continuousWithinAt_of_dominated
      (eventually_nhdsWithin_of_forall h_meas_integrand)
      (eventually_nhdsWithin_of_forall h_dominate)
      h_bound_integrable
      h_cont_integrand

  exact h_param_integral

lemma differentiableOn_spherical_mean (u : E → ℝ) (Ω : Set E) (h_open : IsOpen Ω) (x₀ : E) (R : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω) :
    DifferentiableOn ℝ (fun r ↦ 1 / (4 * π * r ^ 2) * ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea) (Set.Ioo 0 R) := by

  have h_phi_alt : Set.EqOn (fun r ↦ 1 / (4 * π * r ^ 2) * ∫ (x : E) in sphere x₀ r, u x ∂surfaceArea)
      (fun r ↦ (1 / (4 * π)) * ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea) (Set.Ioo 0 R) := by
    intro r hr
    have hr_pos : 0 < r := hr.1
    have hr_sq_ne_zero : r ^ 2 ≠ 0 := pow_ne_zero 2 hr_pos.ne'
    dsimp
    rw [integral_sphere_change_vars x₀ r hr_pos u]
    calc
      1 / (4 * π * r ^ 2) * (r ^ 2 * ∫ (y : E) in sphere 0 1, u (x₀ + r • y) ∂surfaceArea)
        = (1 / (4 * π * r ^ 2) * r ^ 2) * ∫ (y : E) in sphere 0 1, u (x₀ + r • y) ∂surfaceArea := by
        rw [mul_assoc]; linarith
      _ = 1 / (4 * π) * ∫ (y : E) in sphere 0 1, u (x₀ + r • y) ∂surfaceArea := by
        congr 1
        calc
          1 / (4 * π * r ^ 2) * r ^ 2 = (1 / (4 * π)) * (1 / r ^ 2) * r ^ 2 := by ring
          _ = 1 / (4 * π) := by rw [mul_assoc, one_div_mul_cancel hr_sq_ne_zero, mul_one]

  refine DifferentiableOn.congr ?_ h_phi_alt

  have h_param_integral : DifferentiableOn ℝ (fun r ↦ ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea) (Set.Ioo 0 R) := by
    intro r hr
    apply DifferentiableAt.differentiableWithinAt
    have h_deriv : ∃ u' : ℝ → E → ℝ, ∀ r' ∈ Set.Ioo 0 R, ∀ y ∈ sphere (0 : E) 1, HasDerivAt (fun s ↦ u (x₀ + s • y)) (u' r' y) r' := by
      use fun r' y ↦ (fderiv ℝ u (x₀ + r' • y)) y
      intro r' hr' y hy
      have h_in_ball : x₀ + r' • y ∈ Metric.closedBall x₀ R := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h_simp : x₀ + r' • y - x₀ = r' • y := by simp
        rw [h_simp, norm_smul]
        have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
        rw [hy_norm, mul_one, Real.norm_of_nonneg hr'.1.le]
        exact hr'.2.le
      have h_in_Omega : x₀ + r' • y ∈ Ω := h_closed_ball h_in_ball

      have h_diff_u : DifferentiableAt ℝ u (x₀ + r' • y) := by
        have h_in_open_ball : x₀ + r' • y ∈ Metric.ball x₀ R := by
          rw [Metric.mem_ball, dist_eq_norm]
          have h_simp : x₀ + r' • y - x₀ = r' • y := by simp
          rw [h_simp, norm_smul]
          have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
          rw [hy_norm, mul_one, Real.norm_of_nonneg hr'.1.le]
          exact hr'.2
        have h_Omega_nhds : Ω ∈ nhds (x₀ + r' • y) := by
          have h_subset : Metric.ball x₀ R ⊆ Ω := Subset.trans Metric.ball_subset_closedBall h_closed_ball
          exact Filter.mem_of_superset (isOpen_ball.mem_nhds h_in_open_ball) h_subset
        have h_diffOn_Omega : DifferentiableOn ℝ u Ω := by
          apply ContDiffOn.differentiableOn h_smooth
          simp
        exact h_diffOn_Omega.differentiableAt h_Omega_nhds
      have h_diff_affine : HasDerivAt (fun s ↦ x₀ + s • y) y r' := by
        have h_id : HasDerivAt (fun s ↦ s) (1 : ℝ) r' := hasDerivAt_id r'
        have h_smul : HasDerivAt (fun s ↦ s • y) ((1 : ℝ) • y) r' := HasDerivAt.smul_const h_id y
        have h_add : HasDerivAt (fun s ↦ x₀ + s • y) ((1 : ℝ) • y) r' := HasDerivAt.const_add x₀ h_smul
        rwa [one_smul] at h_add
      exact h_diff_u.hasFDerivAt.comp_hasDerivAt r' h_diff_affine

    obtain ⟨u', hu'⟩ := h_deriv

    have h_bound : ∃ M : ℝ, IntegrableOn (fun _ ↦ M) (sphere 0 1) surfaceArea ∧ ∀ r' ∈ Set.Ioo 0 R, ∀ᵐ y ∂(surfaceArea.restrict (sphere 0 1)), ‖u' r' y‖ ≤ M := by
      have h_cont_deriv : ContinuousOn (fderiv ℝ u) (Metric.closedBall x₀ R) := by
        have h_cont_fderiv_Omega : ContinuousOn (fderiv ℝ u) Ω :=
          ContDiffOn.continuousOn_fderiv_of_isOpen h_smooth h_open (by norm_num)
        exact h_cont_fderiv_Omega.mono h_closed_ball
      have h_compact : IsCompact (Metric.closedBall x₀ R) := isCompact_closedBall x₀ R
      have h_deriv_bound : ∃ C : ℝ, ∀ x ∈ Metric.closedBall x₀ R, ‖fderiv ℝ u x‖ ≤ C := by
        have h_cont_norm : ContinuousOn (fun x ↦ ‖fderiv ℝ u x‖) (Metric.closedBall x₀ R) := h_cont_deriv.norm
        obtain ⟨C, hC⟩ := h_compact.bddAbove_image h_cont_norm
        use C
        intro x hx
        exact hC (Set.mem_image_of_mem _ hx)
      obtain ⟨C, hC⟩ := h_deriv_bound
      use C
      constructor
      · haveI : IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) 1)) :=
          isFiniteMeasure_sphere 1 Real.zero_lt_one
        exact MeasureTheory.integrable_const C
      · intro r' hr'
        rw [MeasureTheory.ae_restrict_iff' isClosed_sphere.measurableSet]
        exact Eventually.of_forall fun y hy ↦ by
          have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
          have h_in_ball : x₀ + r' • y ∈ Metric.closedBall x₀ R := by
            rw [Metric.mem_closedBall, dist_eq_norm]
            have h_simp : x₀ + r' • y - x₀ = r' • y := by simp
            rw [h_simp, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg hr'.1.le]
            exact hr'.2.le

          have h_diff_u : DifferentiableAt ℝ u (x₀ + r' • y) := by
            have h_in_open_ball : x₀ + r' • y ∈ Metric.ball x₀ R := by
              rw [Metric.mem_ball, dist_eq_norm]
              have h_simp : x₀ + r' • y - x₀ = r' • y := by simp
              rw [h_simp, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg hr'.1.le]
              exact hr'.2
            have h_Omega_nhds : Ω ∈ nhds (x₀ + r' • y) := by
              have h_subset : Metric.ball x₀ R ⊆ Ω := Subset.trans Metric.ball_subset_closedBall h_closed_ball
              exact Filter.mem_of_superset (isOpen_ball.mem_nhds h_in_open_ball) h_subset
            have h_diffOn_Omega : DifferentiableOn ℝ u Ω := h_smooth.differentiableOn (by norm_num)
            exact h_diffOn_Omega.differentiableAt h_Omega_nhds

          have h_diff_affine : HasDerivAt (fun s ↦ x₀ + s • y) y r' := by
            have h_id : HasDerivAt (fun s ↦ s) (1 : ℝ) r' := hasDerivAt_id r'
            have h_smul : HasDerivAt (fun s ↦ s • y) ((1 : ℝ) • y) r' := HasDerivAt.smul_const h_id y
            have h_add : HasDerivAt (fun s ↦ x₀ + s • y) ((1 : ℝ) • y) r' := HasDerivAt.const_add x₀ h_smul
            rwa [one_smul] at h_add

          have h_actual_deriv := h_diff_u.hasFDerivAt.comp_hasDerivAt r' h_diff_affine
          have h_eq := HasDerivAt.unique (hu' r' hr' y hy) h_actual_deriv

          rw [h_eq]
          have h_op_norm := ContinuousLinearMap.le_opNorm (fderiv ℝ u (x₀ + r' • y)) y
          rw [hy_norm, mul_one] at h_op_norm
          exact h_op_norm.trans (hC (x₀ + r' • y) h_in_ball)
    have h_integrable : IntegrableOn (fun y ↦ u (x₀ + r • y)) (sphere 0 1) surfaceArea := by
      have h_cont_u : ContinuousOn u (Metric.closedBall x₀ R) := by
        have h_cont_Omega : ContinuousOn u Ω := h_smooth.continuousOn
        exact h_cont_Omega.mono h_closed_ball
      have h_mapsTo : Set.MapsTo (fun y ↦ x₀ + r • y) (sphere (0 : E) 1) (Metric.closedBall x₀ R) := by
        intro y hy
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h_simp : x₀ + r • y - x₀ = r • y := by simp
        have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
        rw [h_simp, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg hr.1.le]
        exact hr.2.le
      have h_cont_affine : Continuous (fun y ↦ x₀ + r • y) := continuous_const.add (continuous_const.smul continuous_id)
      have h_cont_comp : ContinuousOn (fun y ↦ u (x₀ + r • y)) (sphere (0 : E) 1) :=
        ContinuousOn.comp h_cont_u h_cont_affine.continuousOn h_mapsTo

      have h_compact : IsCompact (sphere (0 : E) 1) := isCompact_sphere 0 1
      haveI : IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) 1)) := isFiniteMeasure_sphere 1 Real.zero_lt_one

      have h_bound : ∃ C_u : ℝ, ∀ y ∈ sphere (0 : E) 1, ‖u (x₀ + r • y)‖ ≤ C_u := by
        have h_cont_norm : ContinuousOn (fun y ↦ ‖u (x₀ + r • y)‖) (sphere (0 : E) 1) := h_cont_comp.norm
        obtain ⟨C_u, hC_u⟩ := h_compact.bddAbove_image h_cont_norm
        use C_u
        intro y hy
        exact hC_u (Set.mem_image_of_mem _ hy)

      have h_meas : AEStronglyMeasurable (fun y ↦ u (x₀ + r • y)) (surfaceArea.restrict (sphere (0 : E) 1)) :=
        ContinuousOn.aestronglyMeasurable h_cont_comp isClosed_sphere.measurableSet

      obtain ⟨C_u, hC_u⟩ := h_bound
      have h_int_C : IntegrableOn (fun _ : E ↦ (C_u : ℝ)) (sphere (0 : E) 1) surfaceArea := MeasureTheory.integrable_const C_u
      refine MeasureTheory.Integrable.mono h_int_C h_meas ?_
      rw [MeasureTheory.ae_restrict_iff' isClosed_sphere.measurableSet]
      exact Eventually.of_forall fun y hy ↦ by
        rw [Real.norm_eq_abs]
        exact (hC_u y hy).trans (le_abs_self C_u)
    obtain ⟨M, hM_int, hM_bound⟩ := h_bound

    have h_has_deriv : HasDerivAt (fun s ↦ ∫ (y : E) in sphere (0 : E) 1, u (x₀ + s • y) ∂surfaceArea)
                                  (∫ (y : E) in sphere (0 : E) 1, u' r y ∂surfaceArea) r := by
      -- To fill this, you will likely apply MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le.
      -- You have all the pieces:
      -- 1. hM_int: The bounding function M is integrable.
      -- 2. hM_bound: The derivative u' is bounded by M almost everywhere.
      -- 3. hu': The pointwise derivative exists on the interval.
      -- 4. h_integrable: The base function is integrable at r.
      -- 5. The neighborhood: Set.Ioo 0 R is an open neighborhood around r (isOpen_Ioo.mem_nhds hr).

      -- 1. Extract the explicit ε-ball required by the theorem
      -- 1. Extract the explicit ε-ball required by the theorem
      have h_rad : ∃ ε > 0, Metric.ball r ε ⊆ Set.Ioo 0 R := Metric.isOpen_iff.mp isOpen_Ioo r hr
      obtain ⟨ε, hε_pos, hε_subset⟩ := h_rad

      -- 2. Force Lean to unfold IntegrableOn into Integrable so refine doesn't panic
      have h_int_cast : MeasureTheory.Integrable (fun y ↦ u (x₀ + r • y)) (surfaceArea.restrict (sphere (0 : E) 1)) :=
        h_integrable

      -- 3. MASTER HELPER: Prove u' is exactly fderiv once, so we don't repeat the proof for Goals 2 and 3
      have h_u'_eq : ∀ s ∈ Set.Ioo 0 R, ∀ y ∈ sphere (0 : E) 1, u' s y = (fderiv ℝ u (x₀ + s • y)) y := by
        intro s hs_Ioo y hy
        have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
        have h_in_ball : x₀ + s • y ∈ Metric.closedBall x₀ R := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          have h_simp : x₀ + s • y - x₀ = s • y := by simp
          rw [h_simp, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg hs_Ioo.1.le]
          exact hs_Ioo.2.le
        have h_diff_u : DifferentiableAt ℝ u (x₀ + s • y) := by
          have h_in_open_ball : x₀ + s • y ∈ Metric.ball x₀ R := by
            rw [Metric.mem_ball, dist_eq_norm]
            have h_simp : x₀ + s • y - x₀ = s • y := by simp
            rw [h_simp, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg hs_Ioo.1.le]
            exact hs_Ioo.2
          have h_Omega_nhds : Ω ∈ nhds (x₀ + s • y) := by
            have h_subset : Metric.ball x₀ R ⊆ Ω := Subset.trans Metric.ball_subset_closedBall h_closed_ball
            exact Filter.mem_of_superset (isOpen_ball.mem_nhds h_in_open_ball) h_subset
          exact (h_smooth.differentiableOn (by norm_num)).differentiableAt h_Omega_nhds
        have h_diff_affine : HasDerivAt (fun t ↦ x₀ + t • y) y s := by
          have h_id : HasDerivAt (fun t ↦ t) (1 : ℝ) s := hasDerivAt_id s
          have h_smul : HasDerivAt (fun t ↦ t • y) ((1 : ℝ) • y) s := HasDerivAt.smul_const h_id y
          have h_add : HasDerivAt (fun t ↦ x₀ + t • y) ((1 : ℝ) • y) s := HasDerivAt.const_add x₀ h_smul
          rwa [one_smul] at h_add
        have h_actual_deriv := h_diff_u.hasFDerivAt.comp_hasDerivAt s h_diff_affine
        exact HasDerivAt.unique (hu' s hs_Ioo y hy) h_actual_deriv

      -- 4. Re-establish the absolute uniform bound C (bypassing the M quantifier issue)
      have h_cont_deriv : ContinuousOn (fderiv ℝ u) (Metric.closedBall x₀ R) :=
      (ContDiffOn.continuousOn_fderiv_of_isOpen h_smooth h_open (by norm_num)).mono h_closed_ball
      have h_cont_norm_fd : ContinuousOn (fun x ↦ ‖fderiv ℝ u x‖) (Metric.closedBall x₀ R) := h_cont_deriv.norm
      obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ R).bddAbove_image h_cont_norm_fd

      haveI : IsFiniteMeasure (surfaceArea.restrict (sphere (0 : E) 1)) := isFiniteMeasure_sphere 1 Real.zero_lt_one
      have hC_int : MeasureTheory.Integrable (fun _ : E ↦ C) (surfaceArea.restrict (sphere (0 : E) 1)) :=
        MeasureTheory.integrable_const C

      -- 5. Apply the theorem!
      refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds r hε_pos) ?_ h_int_cast ?_ ?_ hC_int ?_).2

      · -- Goal 1 (hF_meas): The function is measurable in the ε-ball around r
        apply Filter.eventually_of_mem (Metric.ball_mem_nhds r hε_pos)
        intro s hs_mem
        have hs_Ioo : s ∈ Set.Ioo 0 R := hε_subset hs_mem
        have h_cont_u : ContinuousOn u (Metric.closedBall x₀ R) := h_smooth.continuousOn.mono h_closed_ball
        have h_mapsTo : Set.MapsTo (fun y ↦ x₀ + s • y) (sphere (0 : E) 1) (Metric.closedBall x₀ R) := by
          intro y hy
          rw [Metric.mem_closedBall, dist_eq_norm]
          have h_simp : x₀ + s • y - x₀ = s • y := by simp
          have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
          rw [h_simp, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg hs_Ioo.1.le]
          exact hs_Ioo.2.le
        have h_cont_affine : Continuous (fun y ↦ x₀ + s • y) := continuous_const.add (continuous_const.smul continuous_id)
        have h_cont_comp : ContinuousOn (fun y ↦ u (x₀ + s • y)) (sphere (0 : E) 1) :=
          ContinuousOn.comp h_cont_u h_cont_affine.continuousOn h_mapsTo
        exact ContinuousOn.aestronglyMeasurable h_cont_comp isClosed_sphere.measurableSet

      · -- Goal 2 (hF'_meas): The derivative is measurable at r
        have h_cont_fderiv_y : ContinuousOn (fun y ↦ (fderiv ℝ u (x₀ + r • y)) y) (sphere (0 : E) 1) := by
          have h_mapsTo : Set.MapsTo (fun y ↦ x₀ + r • y) (sphere (0 : E) 1) (Metric.closedBall x₀ R) := by
            intro y hy
            rw [Metric.mem_closedBall, dist_eq_norm]
            have h_simp : x₀ + r • y - x₀ = r • y := by simp
            have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
            rw [h_simp, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg hr.1.le]
            exact hr.2.le
          have h_cont_affine : Continuous (fun y ↦ x₀ + r • y) := continuous_const.add (continuous_const.smul continuous_id)
          have h_cont_fd_comp : ContinuousOn (fun y ↦ fderiv ℝ u (x₀ + r • y)) (sphere (0 : E) 1) :=
            ContinuousOn.comp h_cont_deriv h_cont_affine.continuousOn h_mapsTo
          exact h_cont_fd_comp.clm_apply continuousOn_id

        have h_meas_fderiv : MeasureTheory.AEStronglyMeasurable (fun y ↦ (fderiv ℝ u (x₀ + r • y)) y) (surfaceArea.restrict (sphere (0 : E) 1)) :=
          ContinuousOn.aestronglyMeasurable h_cont_fderiv_y isClosed_sphere.measurableSet

        refine MeasureTheory.AEStronglyMeasurable.congr h_meas_fderiv ?_

        -- NEW FIX: Extract the equality so 'rw' sees the exact ∀ᵐ syntax
        have h_eq : ∀ᵐ y ∂(surfaceArea.restrict (sphere (0 : E) 1)), (fderiv ℝ u (x₀ + r • y)) y = u' r y := by
          rw [MeasureTheory.ae_restrict_iff' isClosed_sphere.measurableSet]
          exact Eventually.of_forall fun y hy ↦ (h_u'_eq r hr y hy).symm
        exact h_eq

      · -- Goal 3 (h_bound): The derivative is bounded by C universally
        rw [MeasureTheory.ae_restrict_iff' isClosed_sphere.measurableSet]
        exact Eventually.of_forall fun y hy s hs_mem ↦ by
          have hs_Ioo := hε_subset hs_mem
          rw [h_u'_eq s hs_Ioo y hy]
          have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
          have h_in_ball : x₀ + s • y ∈ Metric.closedBall x₀ R := by
            rw [Metric.mem_closedBall, dist_eq_norm]
            have h_simp : x₀ + s • y - x₀ = s • y := by simp
            rw [h_simp, norm_smul, hy_norm, mul_one, Real.norm_of_nonneg hs_Ioo.1.le]
            exact hs_Ioo.2.le
          have h_op_norm := ContinuousLinearMap.le_opNorm (fderiv ℝ u (x₀ + s • y)) y
          rw [hy_norm, mul_one] at h_op_norm
          exact h_op_norm.trans (hC (Set.mem_image_of_mem _ h_in_ball))

      · -- Goal 4 (h_diff): The pointwise derivative exists almost everywhere in the ε-ball
        rw [MeasureTheory.ae_restrict_iff' isClosed_sphere.measurableSet]
        exact Eventually.of_forall fun y hy s hs_mem ↦ hu' s (hε_subset hs_mem) y hy

    exact h_has_deriv.differentiableAt

  exact h_param_integral.const_mul (1 / (4 * π))

lemma affine_mem_closedBall (x₀ : E) {s R : ℝ} (hs_pos : 0 ≤ s) (hs_le : s ≤ R) {y : E} (hy : y ∈ sphere (0 : E) 1) :
    x₀ + s • y ∈ Metric.closedBall x₀ R := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h_simp : x₀ + s • y - x₀ = s • y := by simp
  rw [h_simp, norm_smul]
  have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
  rw [hy_norm, mul_one, Real.norm_of_nonneg hs_pos]
  exact hs_le

lemma affine_mem_ball (x₀ : E) {s R : ℝ} (hs : s ∈ Set.Ioo 0 R) {y : E} (hy : y ∈ sphere (0 : E) 1) :
    x₀ + s • y ∈ Metric.ball x₀ R := by
  rw [Metric.mem_ball, dist_eq_norm]
  have h_simp : x₀ + s • y - x₀ = s • y := by simp
  rw [h_simp, norm_smul]
  have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
  rw [hy_norm, mul_one, Real.norm_of_nonneg hs.1.le]
  exact hs.2

lemma hasDerivAt_affine_radius (x₀ y : E) (s : ℝ) :
    HasDerivAt (fun s' ↦ x₀ + s' • y) y s := by
  have h_id : HasDerivAt (fun s' ↦ s') (1 : ℝ) s := hasDerivAt_id s
  have h_smul : HasDerivAt (fun s' ↦ s' • y) ((1 : ℝ) • y) s := HasDerivAt.smul_const h_id y
  have h_add : HasDerivAt (fun s' ↦ x₀ + s' • y) ((1 : ℝ) • y) s := HasDerivAt.const_add x₀ h_smul
  rwa [one_smul] at h_add

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

lemma deriv_spherical_mean (u : E → ℝ) (Ω : Set E) (x₀ : E) (R r : ℝ)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_open : IsOpen Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (hr : r ∈ Set.Ioo 0 R) :
    deriv (fun s ↦ 1 / (4 * π * s ^ 2) * ∫ (x : E) in sphere x₀ s, u x ∂surfaceArea) r =
      (1 / (4 * π)) * ∫ y in sphere 0 1, (fderiv ℝ u (x₀ + r • y) y) ∂surfaceArea := by
  let phi := fun s ↦ 1 / (4 * π * s ^ 2) * ∫ (x : E) in sphere x₀ s, u x ∂surfaceArea

  have h_phi_eq : deriv phi r = deriv (fun s ↦ 1 / (4 * π) * ∫ (y : E) in sphere 0 1, u (x₀ + s • y) ∂surfaceArea) r := by
    have h_eq_on : Set.EqOn phi (fun s ↦ 1 / (4 * π) * ∫ (y : E) in sphere 0 1, u (x₀ + s • y) ∂surfaceArea) (Set.Ioo 0 R) := by
      intro s hs
      have hs_pos : 0 < s := hs.1
      have hs_sq_ne_zero : s ^ 2 ≠ 0 := pow_ne_zero 2 hs_pos.ne'
      dsimp only [phi]
      rw [integral_sphere_change_vars x₀ s hs_pos u]
      calc
        1 / (4 * π * s ^ 2) * (s ^ 2 * ∫ (y : E) in sphere 0 1, u (x₀ + s • y) ∂surfaceArea)
          = (1 / (4 * π * s ^ 2) * s ^ 2) * ∫ (y : E) in sphere 0 1, u (x₀ + s • y) ∂surfaceArea := by
          rw [mul_assoc]; linarith
        _ = 1 / (4 * π) * ∫ (y : E) in sphere 0 1, u (x₀ + s • y) ∂surfaceArea := by
          congr 1
          calc
            1 / (4 * π * s ^ 2) * s ^ 2 = (1 / (4 * π)) * (1 / s ^ 2) * s ^ 2 := by ring
            _ = 1 / (4 * π) := by rw [mul_assoc, one_div_mul_cancel hs_sq_ne_zero, mul_one]

    have h_nhds : Set.Ioo 0 R ∈ nhds r := isOpen_Ioo.mem_nhds hr
    have h_ev_eq : phi =ᶠ[nhds r] fun s ↦ 1 / (4 * π) * ∫ (y : E) in sphere 0 1, u (x₀ + s • y) ∂surfaceArea :=
      Filter.eventually_of_mem h_nhds h_eq_on
    exact Filter.EventuallyEq.deriv_eq h_ev_eq

  change deriv phi r = _
  rw [h_phi_eq]

  have h_deriv_const : deriv (fun s ↦ 1 / (4 * π) * ∫ (y : E) in sphere 0 1, u (x₀ + s • y) ∂surfaceArea) r =
      1 / (4 * π) * deriv (fun s ↦ ∫ (y : E) in sphere 0 1, u (x₀ + s • y) ∂surfaceArea) r := by
    simp_all only [Set.mem_Ioo, one_div, mul_inv_rev, deriv_const_mul_field']
  rw [h_deriv_const]

  congr 1
  have h_deriv_integral : deriv (fun s ↦ ∫ (y : E) in sphere 0 1, u (x₀ + s • y) ∂surfaceArea) r =
          ∫ (y : E) in sphere 0 1, deriv (fun s ↦ u (x₀ + s • y)) r ∂surfaceArea := by
        have h_eps : ∃ ε > 0, Metric.ball r ε ⊆ Set.Ioo 0 R := Metric.isOpen_iff.mp isOpen_Ioo r hr
        obtain ⟨ε, hε_pos, hε_subset⟩ := h_eps
        have h_bound_exists : ∃ M : ℝ, ∀ s ∈ Metric.ball r ε, ∀ y ∈ sphere (0 : E) 1, ‖deriv (fun s' ↦ u (x₀ + s' • y)) s‖ ≤ M := by
          have h_compact_ball : IsCompact (Metric.closedBall x₀ R) := isCompact_closedBall x₀ R
          have h_cont_fderiv : ContinuousOn (fderiv ℝ u) Ω :=
            ContDiffOn.continuousOn_fderiv_of_isOpen h_smooth h_open (by norm_num)
          have h_cont_fderiv_ball : ContinuousOn (fderiv ℝ u) (Metric.closedBall x₀ R) :=
            h_cont_fderiv.mono h_closed_ball
          have h_cont_norm : ContinuousOn (fun x ↦ ‖fderiv ℝ u x‖) (Metric.closedBall x₀ R) :=
            continuous_norm.comp_continuousOn h_cont_fderiv_ball

          have h_image_compact : IsCompact ((fun x ↦ ‖fderiv ℝ u x‖) '' Metric.closedBall x₀ R) :=
            h_compact_ball.image_of_continuousOn h_cont_norm
          obtain ⟨M, hM⟩ := h_image_compact.bddAbove

          use M
          intro s hs y hy

          have hs_Ioo : s ∈ Set.Ioo 0 R := hε_subset hs
          have h_in_closed_ball : x₀ + s • y ∈ Metric.closedBall x₀ R :=
            affine_mem_closedBall x₀ hs_Ioo.1.le hs_Ioo.2.le hy

          have h_in_open_ball : x₀ + s • y ∈ Metric.ball x₀ R := affine_mem_ball x₀ hs_Ioo hy
          have h_in_Omega : x₀ + s • y ∈ Ω := by
            have h_subset : Metric.ball x₀ R ⊆ Ω := Subset.trans Metric.ball_subset_closedBall h_closed_ball
            exact h_subset h_in_open_ball

          have h_diff_u : DifferentiableAt ℝ u (x₀ + s • y) := by
            have h_diffOn : DifferentiableOn ℝ u Ω := h_smooth.differentiableOn (by norm_num)
            exact h_diffOn.differentiableAt (h_open.mem_nhds h_in_Omega)

          have h_diff_affine : HasDerivAt (fun s' ↦ x₀ + s' • y) y s := hasDerivAt_affine_radius x₀ y s

          have h_hasDeriv : HasDerivAt (fun s' ↦ u (x₀ + s' • y)) ((fderiv ℝ u (x₀ + s • y)) y) s :=
            h_diff_u.hasFDerivAt.comp_hasDerivAt s h_diff_affine

          rw [h_hasDeriv.deriv]

          have h_op_norm : ‖(fderiv ℝ u (x₀ + s • y)) y‖ ≤ ‖fderiv ℝ u (x₀ + s • y)‖ * ‖y‖ :=
            ContinuousLinearMap.le_opNorm (fderiv ℝ u (x₀ + s • y)) y

          have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
          rw [hy_norm, mul_one] at h_op_norm

          have h_M_bound : ‖fderiv ℝ u (x₀ + s • y)‖ ≤ M := hM (Set.mem_image_of_mem _ h_in_closed_ball)
          exact le_trans h_op_norm h_M_bound

        obtain ⟨M, hM_bound⟩ := h_bound_exists

        have h_hasDerivAt : HasDerivAt (fun s ↦ ∫ y in sphere 0 1, u (x₀ + s • y) ∂surfaceArea)
            (∫ y in sphere 0 1, deriv (fun s ↦ u (x₀ + s • y)) r ∂surfaceArea) r := by

          have hF_meas : ∀ᶠ s in 𝓝 r, AEStronglyMeasurable (fun y ↦ u (x₀ + s • y)) (surfaceArea.restrict (sphere 0 1)) := by
            apply Filter.eventually_of_mem (Metric.ball_mem_nhds r hε_pos)
            intro s hs
            have hs_Ioo : s ∈ Set.Ioo 0 R := hε_subset hs
            have hs_pos : 0 < s := hs_Ioo.1
            have h_mapsTo : Set.MapsTo (fun y ↦ x₀ + s • y) (sphere 0 1) Ω := by
              intro y hy
              exact h_closed_ball (affine_mem_closedBall x₀ hs_pos.le hs_Ioo.2.le hy)
            have h_cont_affine : Continuous (fun y ↦ x₀ + s • y) :=
              continuous_const.add (continuous_const.smul continuous_id)
            have h_cont_u : ContinuousOn u Ω := h_smooth.continuousOn
            have h_cont_comp : ContinuousOn (fun y ↦ u (x₀ + s • y)) (sphere 0 1) :=
              ContinuousOn.comp h_cont_u h_cont_affine.continuousOn h_mapsTo
            exact h_cont_comp.aestronglyMeasurable isClosed_sphere.measurableSet

          have hF_int : Integrable (fun y ↦ u (x₀ + r • y)) (surfaceArea.restrict (sphere 0 1)) := by
            have hr_pos : 0 < r := hr.1
            have h_mapsTo : Set.MapsTo (fun y ↦ x₀ + r • y) (sphere 0 1) Ω := by
              intro y hy
              exact h_closed_ball (affine_mem_closedBall x₀ hr_pos.le hr.2.le hy)
            have h_cont_affine : Continuous (fun y ↦ x₀ + r • y) :=
              continuous_const.add (continuous_const.smul continuous_id)
            have h_cont_u : ContinuousOn u Ω := h_smooth.continuousOn
            have h_cont_comp : ContinuousOn (fun y ↦ u (x₀ + r • y)) (sphere 0 1) :=
              ContinuousOn.comp h_cont_u h_cont_affine.continuousOn h_mapsTo

            have h_meas : AEStronglyMeasurable (fun y ↦ u (x₀ + r • y)) (surfaceArea.restrict (sphere 0 1)) :=
              h_cont_comp.aestronglyMeasurable isClosed_sphere.measurableSet

            have h_image_compact : IsCompact ((fun y ↦ ‖u (x₀ + r • y)‖) '' sphere 0 1) :=
              (isCompact_sphere 0 1).image_of_continuousOn (continuous_norm.comp_continuousOn h_cont_comp)
            obtain ⟨C, hC⟩ := h_image_compact.bddAbove

            have h_int_C : Integrable (fun _ ↦ C) (surfaceArea.restrict (sphere 0 1)) := integrable_const C
            apply h_int_C.mono h_meas
            rw [ae_restrict_iff' isClosed_sphere.measurableSet]
            apply Filter.Eventually.of_forall
            intro y hy
            have h1 : ‖u (x₀ + r • y)‖ ≤ C := hC (Set.mem_image_of_mem _ hy)
            have h2 : C ≤ ‖(C : ℝ)‖ := le_abs_self C
            exact le_trans h1 h2

          have hF'_meas : AEStronglyMeasurable (fun y ↦ deriv (fun s' ↦ u (x₀ + s' • y)) r) (surfaceArea.restrict (sphere 0 1)) := by
            have h_eqOn : Set.EqOn (fun y ↦ deriv (fun s' ↦ u (x₀ + s' • y)) r) (fun y ↦ (fderiv ℝ u (x₀ + r • y)) y) (sphere 0 1) := by
              intro y hy
              have h_in_open_ball : x₀ + r • y ∈ Metric.ball x₀ R := affine_mem_ball x₀ hr hy
              have h_Omega_nhds : Ω ∈ 𝓝 (x₀ + r • y) := by
                have h_subset : Metric.ball x₀ R ⊆ Ω := Subset.trans Metric.ball_subset_closedBall h_closed_ball
                exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds h_in_open_ball) h_subset

              have h_diff_u : DifferentiableAt ℝ u (x₀ + r • y) := by
                have h_diffOn : DifferentiableOn ℝ u Ω := h_smooth.differentiableOn (by norm_num)
                exact h_diffOn.differentiableAt h_Omega_nhds

              have h_diff_affine : HasDerivAt (fun s ↦ x₀ + s • y) y r := hasDerivAt_affine_radius x₀ y r
              exact (h_diff_u.hasFDerivAt.comp_hasDerivAt r h_diff_affine).deriv

            have h_cont_fderiv : ContinuousOn (fun y ↦ (fderiv ℝ u (x₀ + r • y)) y) (sphere 0 1) := by
              have hr_pos : 0 < r := hr.1
              have h_mapsTo : Set.MapsTo (fun y ↦ x₀ + r • y) (sphere 0 1) Ω := by
                intro y hy
                exact h_closed_ball (affine_mem_closedBall x₀ hr_pos.le hr.2.le hy)
              have h_cont_affine : Continuous (fun y ↦ x₀ + r • y) :=
                continuous_const.add (continuous_const.smul continuous_id)

              have h_cont_fderiv_Omega : ContinuousOn (fderiv ℝ u) Ω :=
                ContDiffOn.continuousOn_fderiv_of_isOpen h_smooth h_open (by norm_num)

              have h_cont_comp : ContinuousOn (fun y ↦ fderiv ℝ u (x₀ + r • y)) (sphere 0 1) :=
                ContinuousOn.comp h_cont_fderiv_Omega h_cont_affine.continuousOn h_mapsTo

              exact ContinuousOn.clm_apply h_cont_comp continuousOn_id

            have h_meas_fderiv : AEStronglyMeasurable (fun y ↦ (fderiv ℝ u (x₀ + r • y)) y) (surfaceArea.restrict (sphere 0 1)) :=
              h_cont_fderiv.aestronglyMeasurable isClosed_sphere.measurableSet

            apply AEStronglyMeasurable.congr h_meas_fderiv
            change ∀ᵐ y ∂(surfaceArea.restrict (sphere 0 1)), (fderiv ℝ u (x₀ + r • y)) y = deriv (fun s' ↦ u (x₀ + s' • y)) r
            rw [ae_restrict_iff' isClosed_sphere.measurableSet]
            apply Filter.Eventually.of_forall
            intro y hy
            exact (h_eqOn hy).symm

          have h_dom_bound : ∀ᵐ y ∂(surfaceArea.restrict (sphere 0 1)), ∀ s ∈ Metric.ball r ε, ‖deriv (fun s' ↦ u (x₀ + s' • y)) s‖ ≤ M := by
            rw [ae_restrict_iff' isClosed_sphere.measurableSet]
            apply Filter.Eventually.of_forall
            intro y hy s hs
            exact hM_bound s hs y hy

          have h_bound_int : Integrable (fun _ ↦ M) (surfaceArea.restrict (sphere 0 1)) :=
            integrable_const M

          have h_diff : ∀ᵐ y ∂(surfaceArea.restrict (sphere 0 1)), ∀ s ∈ Metric.ball r ε,
              HasDerivAt (fun s' ↦ u (x₀ + s' • y)) (deriv (fun s' ↦ u (x₀ + s' • y)) s) s := by
            rw [ae_restrict_iff' isClosed_sphere.measurableSet]
            apply Filter.Eventually.of_forall
            intro y hy s hs

            have hs_Ioo : s ∈ Set.Ioo 0 R := hε_subset hs
            have h_in_open_ball : x₀ + s • y ∈ Metric.ball x₀ R := affine_mem_ball x₀ hs_Ioo hy

            have h_in_Omega : x₀ + s • y ∈ Ω := by
              have h_subset : Metric.ball x₀ R ⊆ Ω := Subset.trans Metric.ball_subset_closedBall h_closed_ball
              exact h_subset h_in_open_ball

            have h_diff_u : DifferentiableAt ℝ u (x₀ + s • y) := by
              have h_diffOn : DifferentiableOn ℝ u Ω := h_smooth.differentiableOn (by norm_num)
              exact h_diffOn.differentiableAt (h_open.mem_nhds h_in_Omega)

            have h_diff_affine : HasDerivAt (fun s' ↦ x₀ + s' • y) y s := hasDerivAt_affine_radius x₀ y s

            have h_comp : HasDerivAt (fun s' ↦ u (x₀ + s' • y)) ((fderiv ℝ u (x₀ + s • y)) y) s :=
              h_diff_u.hasFDerivAt.comp_hasDerivAt s h_diff_affine
            exact h_comp.differentiableAt.hasDerivAt

          have h_dct := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := surfaceArea.restrict (sphere 0 1))
            (hs := Metric.ball_mem_nhds r hε_pos)
            (bound := fun _ ↦ M)
            (F := fun s y ↦ u (x₀ + s • y))
            (F' := fun s y ↦ deriv (fun s' ↦ u (x₀ + s' • y)) s)
            (x₀ := r)
            (hF_meas := hF_meas)
            (hF_int := hF_int)
            (hF'_meas := hF'_meas)
            (h_bound := h_dom_bound)
            (bound_integrable := h_bound_int)
            (h_diff := h_diff)

          exact h_dct.2
        exact h_hasDerivAt.deriv

  rw [h_deriv_integral]

  apply integral_congr_ae
  change ∀ᵐ y ∂(surfaceArea.restrict (sphere 0 1)), deriv (fun s ↦ u (x₀ + s • y)) r = (fderiv ℝ u (x₀ + r • y)) y
  rw [ae_restrict_iff' isClosed_sphere.measurableSet]
  apply Filter.Eventually.of_forall
  intro y hy

  have h_in_open_ball : x₀ + r • y ∈ Metric.ball x₀ R := affine_mem_ball x₀ hr hy
  have h_Omega_nhds : Ω ∈ 𝓝 (x₀ + r • y) := by
    have h_subset : Metric.ball x₀ R ⊆ Ω := Subset.trans Metric.ball_subset_closedBall h_closed_ball
    exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds h_in_open_ball) h_subset

  have h_diff_u : DifferentiableAt ℝ u (x₀ + r • y) := by
    have h_diffOn : DifferentiableOn ℝ u Ω := h_smooth.differentiableOn (by norm_num)
    exact h_diffOn.differentiableAt h_Omega_nhds

  have h_diff_affine : HasDerivAt (fun s ↦ x₀ + s • y) y r := hasDerivAt_affine_radius x₀ y r
  exact (h_diff_u.hasFDerivAt.comp_hasDerivAt r h_diff_affine).deriv

lemma surfaceArea_eq_hausdorff_dim_minus_one :
    surfaceArea = Measure.hausdorffMeasure ((Module.finrank ℝ E : ℝ) - 1) := by
  rw [surfaceArea]
  congr 1
  simp
  norm_num

lemma affine_eval_at_radius (x₀ x : E) (r : ℝ) (hr : 0 < r) :
    x₀ + r • ((1 / r) • (x - x₀)) = x := by
  simp_all only [one_div]
  rw [← mul_smul]
  rw [mul_inv_cancel₀ (ne_of_gt hr)]
  rw [one_smul]
  abel

lemma hasDerivAt_radial_comp (u : E → ℝ) (x₀ x : E) (r : ℝ) (hr : 0 < r)
    (hu : DifferentiableAt ℝ u x) :
    HasDerivAt (fun s ↦ u (x₀ + s • ((1 / r) • (x - x₀))))
      ((fderiv ℝ u x) ((1 / r) • (x - x₀))) r := by
  have h_path := hasDerivAt_affine_radius x₀ ((1 / r) • (x - x₀)) r
  have h_eval : x₀ + r • ((1 / r) • (x - x₀)) = x := affine_eval_at_radius x₀ x r hr
  have h_u_at_path : HasFDerivAt u (fderiv ℝ u x) (x₀ + r • ((1 / r) • (x - x₀))) := by
    rw [h_eval]
    exact hu.hasFDerivAt
  exact h_u_at_path.comp_hasDerivAt r h_path

lemma fderiv_eq_radial_deriv (u : E → ℝ) (x₀ x : E) (r : ℝ) (hr : 0 < r)
    (hu : DifferentiableAt ℝ u x) :
    (fderiv ℝ u x) ((1 / r) • (x - x₀)) =
    deriv (fun s ↦ u (x₀ + s • ((1 / r) • (x - x₀)))) r := by
  have h_has_deriv := hasDerivAt_radial_comp u x₀ x r hr hu
  exact h_has_deriv.deriv.symm

lemma divergence_theorem (F : E → E) (s : Set E) (n : E → E)
    [HasDivergenceTheoremDomain s]
    [InnerProductSpace ℝ E]
    [MeasureSpace E]
    (hn_normal : IsOutwardUnitNormal s n)
    (h_smooth : ContDiffOn ℝ 1 F (closure s)) :
    ∫ x in s, div_field F x ∂volume =
    ∫ x in frontier s, (⟪F x, n x⟫_ℝ) ∂(Measure.hausdorffMeasure (Module.finrank ℝ E - 1)) := by
  sorry

lemma gradient_inner_fderiv (u : E → ℝ) (x v : E) :
    ⟪gradient u x, v⟫_ℝ = (fderiv ℝ u x) v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

lemma contDiffOn_gradientWithin (u : E → ℝ) (s : Set E)
    (hs : UniqueDiffOn ℝ s) (h_smooth : ContDiffOn ℝ 2 u s) :
    ContDiffOn ℝ 1 (gradientWithin u s) s := by
  have hgrad : gradientWithin u s = (InnerProductSpace.toDual ℝ E).symm ∘ fderivWithin ℝ u s := by
    ext x
    rfl
  rw [hgrad]
  have hfw : ContDiffOn ℝ 1 (fderivWithin ℝ u s) s :=
    h_smooth.fderivWithin hs (by norm_num)
  exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn hfw

lemma fderivWithin_eq_fderiv_of_isOpen {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (F : E → F') (s : Set E) (hs : IsOpen s) (x : E) (hx : x ∈ s) :
    fderivWithin ℝ F s x = fderiv ℝ F x := by
  exact fderivWithin_of_mem_nhds (hs.mem_nhds hx)

lemma gradientWithin_eq_gradient_of_isOpen (u : E → ℝ) (s : Set E) (hs : IsOpen s) (x : E) (hx : x ∈ s) :
    gradientWithin u s x = gradient u x := by
  unfold gradientWithin gradient
  rw [fderivWithin_eq_fderiv_of_isOpen u s hs x hx]

lemma laplacianWithin_eq_laplacian (u : E → ℝ) (s : Set E) (hs : IsOpen s) (x : E) (hx : x ∈ s) :
    laplacianWithin u s x = laplacian u x := by
  unfold laplacianWithin laplacian div_fieldWithin div_field
  have h_congr : fderivWithin ℝ (gradientWithin u s) s x = fderivWithin ℝ (gradient u) s x := by
    apply fderivWithin_congr
    · intro y hy
      exact gradientWithin_eq_gradient_of_isOpen u s hs y hy
    · exact gradientWithin_eq_gradient_of_isOpen u s hs x hx
  rw [h_congr]
  rw [fderivWithin_eq_fderiv_of_isOpen (gradient u) s hs x hx]

lemma laplacianWithin_eq_div_field (u : E → ℝ) (s : Set E) (hs_open : IsOpen s) (x : E) (hx : x ∈ s) :
    laplacianWithin u (closure s) x = div_field (gradientWithin u (closure s)) x := by
  unfold laplacianWithin div_fieldWithin div_field
  have h_nhds : closure s ∈ 𝓝 x := Filter.mem_of_superset (hs_open.mem_nhds hx) subset_closure
  have h_deriv : fderivWithin ℝ (gradientWithin u (closure s)) (closure s) x = fderiv ℝ (gradientWithin u (closure s)) x :=
    fderivWithin_of_mem_nhds h_nhds
  rw [h_deriv]

lemma divergence_theorem_scalar (u : E → ℝ) (s : Set E) (n : E → E)
    [h_domain : HasPDEDomain s]
    (hn_normal : IsOutwardUnitNormal s n)
    (h_smooth : ContDiffOn ℝ 2 u (closure s)) :
    ∫ x in s, laplacianWithin u (closure s) x ∂volume =
    ∫ x in frontier s, (fderivWithin ℝ u (closure s) x) (n x) ∂(Measure.hausdorffMeasure 2) := by
  have hs_unique := h_domain.unique_diff
  have hs_open := h_domain.is_open
  have h_grad_smooth : ContDiffOn ℝ 1 (gradientWithin u (closure s)) (closure s) :=
    contDiffOn_gradientWithin u (closure s) hs_unique h_smooth
  have h_div_base := divergence_theorem (gradientWithin u (closure s)) s n hn_normal h_grad_smooth
  have h_vol_eq : ∫ x in s, laplacianWithin u (closure s) x ∂volume =
                  ∫ x in s, div_field (gradientWithin u (closure s)) x ∂volume :=
    setIntegral_congr_fun hs_open.measurableSet
      (fun x hx => laplacianWithin_eq_div_field u s hs_open x hx)
  have h_integrand : ∀ x : E, @inner ℝ _ _ (gradientWithin u (closure s) x) (n x) =
                               (fderivWithin ℝ u (closure s) x) (n x) := fun x => by
    simp only [gradientWithin, InnerProductSpace.toDual_symm_apply]
  have h_finrank : (Module.finrank ℝ E : ℝ) - 1 = 2 := by
    have h_dim : Module.finrank ℝ E = 3 := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
      rw [finrank_euclideanSpace]
      rfl
    rw [h_dim]
    norm_num
  rw [h_vol_eq, h_div_base]
  simp_rw [h_integrand]
  rw [h_finrank]



lemma frontier_ball_eq_sphere (x₀ : E) (r : ℝ) (hr : 0 < r) :
    frontier (Metric.ball x₀ r) = sphere x₀ r := by
  exact frontier_ball x₀ (ne_of_gt hr)

lemma closure_ball_eq_closedBall (x₀ : E) (r : ℝ) (hr : 0 < r) :
    closure (Metric.ball x₀ r) = Metric.closedBall x₀ r := by
  exact closure_ball x₀ (ne_of_gt hr)

lemma hausdorff_dim_eq_surfaceArea :
    Measure.hausdorffMeasure ((Module.finrank ℝ E : ℝ) - 1) = surfaceArea := by
  rw [surfaceArea]
  congr 1
  simp
  norm_num

lemma fderiv_smul_commute (u : E → ℝ) (x x₀ : E) (r : ℝ) :
    (fderiv ℝ u x) ((1 / r) • (x - x₀)) = (fderiv ℝ u x) (x - x₀) * (1 / r) := by
  simp_all only [one_div, map_smul, map_sub, smul_eq_mul]
  linarith

lemma smooth_on_ball_closure (u : E → ℝ) (x₀ : E) (r : ℝ) (hr_pos : 0 < r)
    (h_smooth : ContDiffOn ℝ 2 u (Metric.closedBall x₀ r)) :
    ContDiffOn ℝ 2 u (closure (Metric.ball x₀ r)) := by
  rw [closure_ball_eq_closedBall x₀ r hr_pos]
  exact h_smooth

lemma divergence_theorem_ball (u : E → ℝ) (x₀ : E) (r : ℝ) (hr_pos : 0 < r)
    (h_smooth : ContDiffOn ℝ 2 u (closure (Metric.ball x₀ r))) :
    ∫ x in sphere x₀ r, (fderivWithin ℝ u (closure (Metric.ball x₀ r)) x) (x - x₀) * (1 / r) ∂surfaceArea =
    ∫ x in Metric.ball x₀ r, laplacianWithin u (closure (Metric.ball x₀ r)) x := by
  haveI h_domain : HasPDEDomain (Metric.ball x₀ r) := instHasPDEDomainBall x₀ r hr_pos
  have h_normal := ball_outward_normal x₀ r
  have h_frontier := frontier_ball_eq_sphere x₀ r hr_pos

  have h_scalar := divergence_theorem_scalar u (Metric.ball x₀ r) (fun x => (1 / r) • (x - x₀)) h_normal h_smooth

  have h_integrand : (fun x => (fderivWithin ℝ u (closure (Metric.ball x₀ r)) x) ((fun y => (1 / r) • (y - x₀)) x)) =
                     (fun x => (fderivWithin ℝ u (closure (Metric.ball x₀ r)) x) (x - x₀) * (1 / r)) := by
    ext x
    have h_smul := (fderivWithin ℝ u (closure (Metric.ball x₀ r)) x).map_smul (1 / r) (x - x₀)
    rw [h_smul]
    rw [smul_eq_mul]
    rw [mul_comm]

  have h_target := h_scalar.symm
  rw [h_frontier] at h_target
  rw [h_integrand] at h_target

  exact h_target

lemma sphere_integral_revert_vars (u : E → ℝ) (x₀ : E) (r : ℝ) (hr : 0 < r) :
    ∫ (y : E) in sphere 0 1, (fderiv ℝ u (x₀ + r • y)) y ∂surfaceArea =
    (1 / r^2) * ∫ (x : E) in sphere x₀ r, (fderiv ℝ u x) (x - x₀) * (1 / r) ∂surfaceArea := by
  let g : E ≃ₜ E :=
    (Homeomorph.addRight (-x₀)).trans (Homeomorph.smulOfNeZero (1 / r) (by positivity))

  have h_preimage : g ⁻¹' (sphere 0 1) = sphere x₀ r := by
    ext x
    simp only [g, Homeomorph.trans_apply, Set.mem_preimage, Metric.mem_sphere, dist_eq_norm, sub_zero]
    change ‖(1 / r) • (x + -x₀)‖ = 1 ↔ ‖x - x₀‖ = r
    rw [← sub_eq_add_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hr)]
    rw [mul_comm, mul_one_div, div_eq_iff hr.ne', one_mul]

  have h_map_measure : MeasureTheory.Measure.map g surfaceArea =
      (ENNReal.ofReal (r^2)) • surfaceArea := by
    have h_g_eq : ⇑g = (fun x ↦ (1 / r) • x) ∘ (fun x ↦ x + -x₀) := rfl
    rw [h_g_eq]

    have h_meas_smul : Measurable (fun x : E ↦ (1 / r) • x) :=
      Continuous.measurable (continuous_const.smul continuous_id)
    have h_meas_add : Measurable (fun x : E ↦ x + -x₀) :=
      Continuous.measurable (continuous_id.add continuous_const)

    rw [← MeasureTheory.Measure.map_map h_meas_smul h_meas_add]

    have h_trans_iso : Isometry (fun x : E ↦ x + -x₀) := isometry_add_right (-x₀)
    have h_trans_surj : Function.Surjective (fun x : E ↦ x + -x₀) := (Homeomorph.addRight (-x₀)).surjective
    have h_map_trans : MeasureTheory.Measure.map (fun x ↦ x + -x₀) surfaceArea = surfaceArea := by
      rw [surfaceArea]
      erw [Isometry.map_hausdorffMeasure h_trans_iso (Or.inr h_trans_surj)]
      rw [h_trans_surj.range_eq]
      exact MeasureTheory.Measure.restrict_univ
    rw [h_map_trans]

    ext s hs
    rw [MeasureTheory.Measure.map_apply h_meas_smul hs]
    rw [MeasureTheory.Measure.smul_apply]

    have h_pre : (fun x ↦ (1 / r) • x) ⁻¹' s = r • s := by
      ext x
      simp only [Set.mem_preimage]
      constructor
      · intro hx
        use (1 / r) • x
        refine ⟨hx, ?_⟩
        dsimp only
        rw [smul_smul, mul_one_div, div_self hr.ne', one_smul]
      · rintro ⟨y, hy, rfl⟩
        dsimp only
        rw [smul_smul, one_div_mul_cancel hr.ne', one_smul]
        exact hy
    rw [h_pre]

    rw [surfaceArea]
    have hd_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    rw [MeasureTheory.Measure.hausdorffMeasure_smul₀ hd_nonneg hr.ne']

    congr 1
    ext
    push_cast
    rw [Real.norm_eq_abs, abs_of_pos hr]
    simp_all only [one_div, Nat.ofNat_nonneg, rpow_ofNat, coe_toNNReal', left_eq_sup, g]
    positivity

  have h_cov : ∫ (x : E) in sphere x₀ r, (fderiv ℝ u (g.symm (g x))) (g x) ∂surfaceArea =
      ∫ (y : E) in sphere 0 1, (fderiv ℝ u (g.symm y)) y ∂(MeasureTheory.Measure.map g surfaceArea) := by
    symm
    have hg_emb : MeasurableEmbedding g := Homeomorph.measurableEmbedding g
    have hg_meas : Measurable g := hg_emb.measurable
    have hs_meas : MeasurableSet (sphere (0 : E) 1) := isClosed_sphere.measurableSet
    rw [MeasureTheory.Measure.restrict_map hg_meas hs_meas]
    rw [h_preimage]
    exact hg_emb.integral_map (fun y ↦ (fderiv ℝ u (g.symm y)) y)

  rw [h_map_measure] at h_cov
  rw [MeasureTheory.Measure.restrict_smul] at h_cov
  rw [MeasureTheory.integral_smul_measure] at h_cov
  rw [ENNReal.toReal_ofReal (sq_nonneg r)] at h_cov
  rw [smul_eq_mul] at h_cov

  have h_gx : ∀ x, g x = (1 / r) • (x - x₀) := by
    intro x
    change (1 / r) • (x + -x₀) = (1 / r) • (x - x₀)
    rw [sub_eq_add_neg]

  have h_gsymm : ∀ y, g.symm y = x₀ + r • y := by
    intro y
    have h1 : g (x₀ + r • y) = y := by
      rw [h_gx, add_comm x₀ (r • y), add_sub_cancel_right, smul_smul, one_div_mul_cancel hr.ne', one_smul]
    rw [← h1, Homeomorph.symm_apply_apply]
    rw[h1]

  simp_rw [Homeomorph.symm_apply_apply] at h_cov
  simp_rw [h_gx] at h_cov

  have h_pull : ∀ x, (fderiv ℝ u x) ((1 / r) • (x - x₀)) = (fderiv ℝ u x) (x - x₀) * (1 / r) := by
    intro x
    rw [(fderiv ℝ u x).map_smul, smul_eq_mul, mul_comm]

  simp_rw [h_pull] at h_cov
  simp_rw [h_gsymm] at h_cov

  rw [h_cov, ← mul_assoc, one_div, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul]

/-
### Theorem 8.1: The Mean Value Property
-/

theorem laplace_mean_value_property_3D
    (u : E → ℝ) (Ω : Set E) (x₀ : E) (R : ℝ)
    (h_open : IsOpen Ω)
    (hR : 0 < R)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (h_harmonic : IsHarmonic u Ω) :
    u x₀ = (1 / (4 * π * R^2)) * ∫ x in sphere x₀ R, u x ∂surfaceArea := by

  let phi := fun (r : ℝ) ↦ (1 / (4 * π * r^2)) * ∫ x in sphere x₀ r, u x ∂surfaceArea

  have h_goal_derivative : ∀ r ∈ Set.Ioo 0 R, deriv phi r = 0 := by
    intro r hr

    have h_change_vars : phi r = (1 / (4 * π)) * ∫ y in sphere 0 1,
                          u (x₀ + r • y) ∂surfaceArea := by
      dsimp [phi]
      have h_integral_cov : ∫ x in sphere x₀ r, u x ∂surfaceArea =
          r^2 * ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea :=
        integral_sphere_change_vars x₀ r hr.1 u
      rw [h_integral_cov]

      have hr_ne_zero : r ≠ 0 := hr.1.ne'
      have hr_sq_ne_zero : r^2 ≠ 0 := pow_ne_zero 2 hr_ne_zero

      calc
        (1 / (4 * π * r^2)) * (r^2 * ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea)
          = (1 / (4 * π * r^2) * r^2) * ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea := by
            rw [mul_assoc]
            linarith
        _ = (1 / (4 * π)) * ∫ y in sphere 0 1, u (x₀ + r • y) ∂surfaceArea := by
          congr 1
          calc
            1 / (4 * π * r^2) * r^2
              = (1 / (4 * π)) * (1 / r^2) * r^2 := by ring
            _ = 1 / (4 * π) := by
              rw [mul_assoc, one_div_mul_cancel hr_sq_ne_zero, mul_one]

    have h_chain_rule : deriv phi r = (1 / (4 * π)) * ∫ y in sphere 0 1,
                       (fderiv ℝ u (x₀ + r • y) y) ∂surfaceArea := by
      exact deriv_spherical_mean u Ω x₀ R r h_closed_ball h_open h_smooth hr

    have h_revert_vars : deriv phi r = (1 / (4 * π * r^2)) * ∫ x in sphere x₀ r,
      (fderiv ℝ u x) (x - x₀) * (1 / r) ∂surfaceArea := by
      rw [h_chain_rule]
      rw [sphere_integral_revert_vars u x₀ r hr.1]
      rw [← mul_assoc]
      have h_frac : 1 / (4 * π) * (1 / r^2) = 1 / (4 * π * r^2) := by ring
      rw [h_frac]

    have h_divergence_thm : deriv phi r = (1 / (4 * π * r^2)) * ∫ x in Metric.ball x₀ r,
                            laplacian u x ∂volume := by
      have hr_pos : 0 < r := hr.1
      have hr_le : r ≤ R := le_of_lt hr.2
      have h_subset : Metric.closedBall x₀ r ⊆ Ω :=
        Set.Subset.trans (Metric.closedBall_subset_closedBall hr_le) h_closed_ball

      -- 1. Align the smoothness hypothesis exactly with the new PDE Domain signature
      have h_smooth_ball : ContDiffOn ℝ 2 u (closure (Metric.ball x₀ r)) := by
        apply h_smooth.mono
        exact Set.Subset.trans Metric.closure_ball_subset_closedBall h_subset

      -- 2. Expand the spherical mean derivative (Outputs global fderiv)
      rw [h_revert_vars]

      -- 3. Bridge the Boundary: Swap global fderiv for fderivWithin
      have h_bound_eq : ∫ x in sphere x₀ r, (fderiv ℝ u x) (x - x₀) * (1 / r) ∂surfaceArea =
                        ∫ x in sphere x₀ r, (fderivWithin ℝ u (closure (Metric.ball x₀ r)) x) (x - x₀) * (1 / r) ∂surfaceArea := by
        apply setIntegral_congr_fun isClosed_sphere.measurableSet
        intro x hx
        have hx_cb : x ∈ Metric.closedBall x₀ r := Metric.sphere_subset_closedBall hx
        have hx_cb_R : x ∈ Metric.closedBall x₀ R := Metric.closedBall_subset_closedBall hr_le hx_cb
        have hx_omega : x ∈ Ω := h_closed_ball hx_cb_R
        have hd : DifferentiableAt ℝ u x :=
          (h_smooth.differentiableOn (by norm_num)).differentiableAt (h_open.mem_nhds hx_omega)
        haveI h_domain : HasPDEDomain (Metric.ball x₀ r) := instHasPDEDomainBall x₀ r hr_pos
        have hx_front : x ∈ frontier (Metric.ball x₀ r) := by
          rw [frontier_ball_eq_sphere x₀ r hr_pos]
          exact hx
        have hx_cl : x ∈ closure (Metric.ball x₀ r) := frontier_subset_closure hx_front
        have h_unique : UniqueDiffWithinAt ℝ (closure (Metric.ball x₀ r)) x :=
          h_domain.unique_diff x hx_cl
        have h_deriv_eq : fderivWithin ℝ u (closure (Metric.ball x₀ r)) x = fderiv ℝ u x :=
          hd.fderivWithin h_unique
        simp_rw [h_deriv_eq]

      rw [h_bound_eq]

      -- 4. Apply the restricted Divergence Theorem
      rw [divergence_theorem_ball u x₀ r hr_pos h_smooth_ball]

      -- 5. Bridge the Interior: Swap laplacianWithin back to global laplacian
      have h_vol_eq : ∫ x in Metric.ball x₀ r, laplacianWithin u (closure (Metric.ball x₀ r)) x ∂volume =
                      ∫ x in Metric.ball x₀ r, laplacian u x ∂volume := by
        apply setIntegral_congr_fun isOpen_ball.measurableSet
        intro x hx
        unfold laplacianWithin laplacian div_fieldWithin div_field
        have h_nhds_cl : closure (Metric.ball x₀ r) ∈ 𝓝 x := Filter.mem_of_superset (isOpen_ball.mem_nhds hx) subset_closure
        have h_nhds_op : Metric.ball x₀ r ∈ 𝓝 x := isOpen_ball.mem_nhds hx
        have h_eq_on : EqOn (gradientWithin u (closure (Metric.ball x₀ r))) (gradient u) (Metric.ball x₀ r) := by
          intro y hy
          unfold gradientWithin gradient
          have hy_nhds_cl : closure (Metric.ball x₀ r) ∈ 𝓝 y := Filter.mem_of_superset (isOpen_ball.mem_nhds hy) subset_closure
          rw [fderivWithin_of_mem_nhds hy_nhds_cl]
        have h1 : fderivWithin ℝ (gradientWithin u (closure (Metric.ball x₀ r))) (closure (Metric.ball x₀ r)) x = fderiv ℝ (gradientWithin u (closure (Metric.ball x₀ r))) x :=
          fderivWithin_of_mem_nhds h_nhds_cl
        have h2 : fderiv ℝ (gradientWithin u (closure (Metric.ball x₀ r))) x = fderivWithin ℝ (gradientWithin u (closure (Metric.ball x₀ r))) (Metric.ball x₀ r) x :=
          (fderivWithin_of_mem_nhds h_nhds_op).symm
        have h3 : fderivWithin ℝ (gradientWithin u (closure (Metric.ball x₀ r))) (Metric.ball x₀ r) x = fderivWithin ℝ (gradient u) (Metric.ball x₀ r) x :=
          fderivWithin_congr h_eq_on (h_eq_on hx)
        have h4 : fderivWithin ℝ (gradient u) (Metric.ball x₀ r) x = fderiv ℝ (gradient u) x :=
          fderivWithin_of_mem_nhds h_nhds_op
        rw [h1, h2, h3, h4]

      rw [h_vol_eq]

    have h_harmonic_zero : deriv phi r = 0 := by
      rw [h_divergence_thm]
      have h_int_zero : ∫ x in ball x₀ r, laplacian u x ∂volume = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [self_mem_ae_restrict isOpen_ball.measurableSet] with x hx
        apply h_harmonic
        exact Set.Subset.trans Metric.ball_subset_closedBall h_closed_ball
                 (Metric.ball_subset_ball hr.2.le hx)
      rw [h_int_zero, mul_zero]
    exact h_harmonic_zero

  have h_phi_cont : ContinuousOn phi (Set.Ioc 0 R) := by
    have h_cont_u : ContinuousOn u (Metric.closedBall x₀ R) := h_smooth.continuousOn.mono
                    h_closed_ball
    exact continuousOn_spherical_mean u x₀ R h_cont_u

  have h_phi_diff : DifferentiableOn ℝ phi (Set.Ioo 0 R) := by
    exact differentiableOn_spherical_mean u Ω h_open x₀ R h_closed_ball h_smooth

  have h_phi_const : ∀ r ∈ Set.Ioo 0 R, phi r = phi R := by
    intro r hr
    have h_sub_Icc : Set.Icc r R ⊆ Set.Ioc 0 R := by
      intro x hx
      exact ⟨hr.1.trans_le hx.1, hx.2⟩
    have hcont : ContinuousOn phi (Set.Icc r R) := h_phi_cont.mono h_sub_Icc
    have hderiv : ∀ x ∈ Set.Ico r R, HasDerivWithinAt phi 0 (Set.Ici x) x := by
      intro x hx
      have hx_Ioo : x ∈ Set.Ioo 0 R := ⟨hr.1.trans_le hx.1, hx.2⟩
      have h_nhds : Set.Ioo 0 R ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx_Ioo
      have h_diff_at : DifferentiableAt ℝ phi x := h_phi_diff.differentiableAt h_nhds
      have h_has_deriv : HasDerivAt phi (deriv phi x) x := h_diff_at.hasDerivAt
      rw [h_goal_derivative x hx_Ioo] at h_has_deriv
      exact h_has_deriv.hasDerivWithinAt
    have h_const_interval := constant_of_has_deriv_right_zero hcont hderiv

    have h_R_mem : R ∈ Set.Icc r R := ⟨hr.2.le, le_rfl⟩
    exact (h_const_interval R h_R_mem).symm

  have h_phi_const : ∀ r ∈ Set.Ioo 0 R, phi r = phi R := by
    intro r hr
    have h_sub_Icc : Set.Icc r R ⊆ Set.Ioc 0 R := by
      intro x hx
      exact ⟨hr.1.trans_le hx.1, hx.2⟩
    have hcont : ContinuousOn phi (Set.Icc r R) := h_phi_cont.mono h_sub_Icc
    have hderiv : ∀ x ∈ Set.Ico r R, HasDerivWithinAt phi 0 (Set.Ici x) x := by
      intro x hx
      have hx_Ioo : x ∈ Set.Ioo 0 R := ⟨hr.1.trans_le hx.1, hx.2⟩
      have h_nhds : Set.Ioo 0 R ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx_Ioo
      have h_diff_at : DifferentiableAt ℝ phi x := h_phi_diff.differentiableAt h_nhds
      have h_has_deriv : HasDerivAt phi (deriv phi x) x := h_diff_at.hasDerivAt
      rw [h_goal_derivative x hx_Ioo] at h_has_deriv
      exact h_has_deriv.hasDerivWithinAt
    have h_const_interval := constant_of_has_deriv_right_zero hcont hderiv

    have h_R_mem : R ∈ Set.Icc r R := ⟨hr.2.le, le_rfl⟩
    exact (h_const_interval R h_R_mem).symm

  have h_averaging_lemma : Filter.Tendsto phi (𝓝[>] 0) (𝓝 (u x₀)) := by
    have h_cont_u : ContinuousOn u (Metric.ball x₀ R) := by
      exact h_smooth.continuousOn.mono (Set.Subset.trans Metric.ball_subset_closedBall
            h_closed_ball)
    exact averaging_lemma_spherical_translated R hR u x₀ h_cont_u

  have h_tendsto_const : Filter.Tendsto phi (𝓝[>] 0) (𝓝 (phi R)) := by
    have h_eq_nhds : (fun _ ↦ phi R) =ᶠ[𝓝[>] 0] phi := by
      rw [Filter.EventuallyEq, nhdsWithin, Filter.eventually_inf_principal]
      filter_upwards [isOpen_Iio.mem_nhds hR] with r hr_lt hr_pos
      exact (h_phi_const r ⟨hr_pos, hr_lt⟩).symm
    exact Filter.Tendsto.congr' h_eq_nhds tendsto_const_nhds

  exact tendsto_nhds_unique h_averaging_lemma h_tendsto_const
