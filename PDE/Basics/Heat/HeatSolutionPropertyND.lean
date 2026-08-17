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
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import PDE.Basics.Heat.HeatSolutionND


namespace Heat

noncomputable section

open Real Set MeasureTheory Metric Filter Function Pointwise
open scoped BigOperators Topology Measure

lemma heatKernelND_even (z : E n) : heatKernelND α (-z) t = heatKernelND α z t := by
  unfold heatKernelND
  rw [norm_neg]

lemma heatKernelND_mass_one_x_sub_y_even (x : E n) (hα : 0 < α) (ht : 0 < t) :
    ∫ y : E n, heatKernelND α (x - y) t = (1 : ℝ) := by
  rw [show (fun y : E n => heatKernelND α (x - y) t) = fun y : E n => heatKernelND α (-x + y) t by
    ext y
    have h_eq : x - y = -(-x + y) := by abel
    rw [h_eq, heatKernelND_even]]
  rw [MeasureTheory.integral_add_left_eq_self (f := fun y : E n => heatKernelND α y t)]
  exact integral_heatKernelND_one_gaussian α t hα ht

lemma heatND_maximum_principle (x : E n) {α t B : ℝ} (hα : 0 < α) (ht : 0 < t)
    (hg_meas : AEMeasurable g) (hBound : ∀ y, |g y| ≤ B) :
    |heatConvolutionHKND α g x t| ≤ B := by
  have h_int_base := integrable_heatKernelND_slice hα ht x
  have h_int_B := h_int_base.mul_const B
  have h_int_L : Integrable (fun y : E n => heatKernelND α (x - y) t * |g y|) := by
    refine h_int_B.mono' (h_int_base.aestronglyMeasurable.mul
      (continuous_abs.comp_aestronglyMeasurable hg_meas.aestronglyMeasurable)) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by unfold heatKernelND; positivity) (abs_nonneg (g y)))]
    exact mul_le_mul_of_nonneg_left (hBound y) (by unfold heatKernelND; positivity)
  have hB : B = ∫ y : E n, heatKernelND α (x - y) t * B := by
    rw [show (fun y : E n => heatKernelND α (x - y) t * B) = fun y : E n => B * heatKernelND α (x - y) t by ext y; ring, MeasureTheory.integral_const_mul, heatKernelND_mass_one_x_sub_y_even x hα ht, mul_one]
  unfold heatConvolutionHKND
  refine le_trans abs_integral_le_integral_abs ?_
  rw [show (fun y : E n => |heatKernelND α (x - y) t * g y|) = fun y : E n => heatKernelND α (x - y) t * |g y| by ext y; rw [abs_mul, abs_of_nonneg (by unfold heatKernelND; positivity)], hB]
  exact integral_mono h_int_L h_int_B fun y => mul_le_mul_of_nonneg_left (hBound y) (by unfold heatKernelND; positivity)

lemma integral_radial_1D_equiv {δ s : ℝ} {n : ℕ} (hs : 0 < s) (hn : n ≠ 0) :
    ∫ y : ℝ in Set.Ioi 0, y ^ (n - 1) * Set.indicator {w : ℝ | δ / s ≤ |s⁻¹ * w|} (fun w => Real.exp (-(s⁻¹ * w)^2)) y =
    s ^ (n : ℝ) * ∫ y : ℝ in Set.Ioi 0, y ^ (n - 1) * Set.indicator {w : ℝ | δ / s ≤ |w|} (fun w => Real.exp (-w^2)) y := by
  have integral_comp_mul_Ioi_left : ∀ (f : ℝ → ℝ), ∫ y : ℝ in Set.Ioi 0, f (s⁻¹ * y) = s * ∫ w : ℝ in Set.Ioi 0, f w := by
    intro f
    have hs_inv_pos : 0 < s⁻¹ := inv_pos.mpr hs
    have h1 : ∫ y : ℝ in Set.Ioi 0, f (s⁻¹ * y) = ∫ y : ℝ, Set.indicator (Set.Ioi 0) (fun y => f (s⁻¹ * y)) y :=
      (MeasureTheory.integral_indicator measurableSet_Ioi).symm
    have h2 : ∫ w : ℝ in Set.Ioi 0, f w = ∫ w : ℝ, Set.indicator (Set.Ioi 0) f w :=
      (MeasureTheory.integral_indicator measurableSet_Ioi).symm
    rw [h1, h2]
    have h_ind : Set.indicator (Set.Ioi 0) (fun y => f (s⁻¹ * y)) = fun y => Set.indicator (Set.Ioi 0) f (s⁻¹ * y) := by
      ext y
      by_cases h : 0 < y
      · have h2 : 0 < s⁻¹ * y := mul_pos hs_inv_pos h
        erw [Set.indicator_of_mem h, Set.indicator_of_mem h2]
      · have h2 : ¬ (0 < s⁻¹ * y) := by
          intro contra
          have h_pos : 0 < s * (s⁻¹ * y) := mul_pos hs contra
          have hs_inv_cancel : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne.symm
          rw [← mul_assoc, hs_inv_cancel, one_mul] at h_pos
          exact h h_pos
        erw [Set.indicator_of_notMem h, Set.indicator_of_notMem h2]
    rw [h_ind]
    have h_int := Measure.integral_comp_mul_left (Set.indicator (Set.Ioi 0) f) s⁻¹
    rw [h_int]
    rw [inv_inv, abs_of_pos hs, smul_eq_mul]
  have radial_integrand_algebra : ∀ w : ℝ, (s * w) ^ (n - 1) * Set.indicator {u : ℝ | δ / s ≤ |u|} (fun u => Real.exp (-u^2)) w =
    s ^ (n - 1) * (w ^ (n - 1) * Set.indicator {u : ℝ | δ / s ≤ |u|} (fun u => Real.exp (-u^2)) w) := by
    intro w
    rw [mul_pow, mul_assoc]

  have s_pow_combine : s * s ^ (n - 1) = s ^ (n : ℝ) := by
    have h_nat_pow : s * s ^ (n - 1) = s ^ n := by
      cases n with
      | zero => contradiction
      | succ m =>
        have h_sub : m + 1 - 1 = m := rfl
        rw [h_sub]
        exact (pow_succ' s m).symm
    have h_real_pow : s ^ n = s ^ (n : ℝ) := by
      exact (Real.rpow_natCast s n).symm
    rw [h_nat_pow, h_real_pow]

  have h_eq : (fun y : ℝ => y ^ (n - 1) * Set.indicator {w : ℝ | δ / s ≤ |s⁻¹ * w|} (fun w => Real.exp (-(s⁻¹ * w)^2)) y) =
              (fun y : ℝ => (fun w : ℝ => (s * w) ^ (n - 1) * Set.indicator {u : ℝ | δ / s ≤ |u|} (fun u => Real.exp (-u^2)) w) (s⁻¹ * y)) := by
    ext y
    have hs_inv : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne.symm
    have h_y : y = s * (s⁻¹ * y) := by
      calc y = 1 * y := by ring
           _ = (s * s⁻¹) * y := by rw [hs_inv]
           _ = s * (s⁻¹ * y) := by ring
    nth_rewrite 1 [h_y]
    dsimp only [Set.indicator, Set.mem_setOf_eq]

  rw [h_eq]
  rw [integral_comp_mul_Ioi_left (fun w => (s * w) ^ (n - 1) * Set.indicator {u : ℝ | δ / s ≤ |u|} (fun u => Real.exp (-u^2)) w)]

  have h_alg : (fun w : ℝ => (s * w) ^ (n - 1) * Set.indicator {u : ℝ | δ / s ≤ |u|} (fun u => Real.exp (-u^2)) w) =
               (fun w : ℝ => s ^ (n - 1) * (w ^ (n - 1) * Set.indicator {u : ℝ | δ / s ≤ |u|} (fun u => Real.exp (-u^2)) w)) := by
    ext w
    exact radial_integrand_algebra w
  rw [h_alg]
  rw [integral_const_mul]
  rw [← mul_assoc, s_pow_combine]

lemma integral_comp_smul_indicator_gaussian {δ s : ℝ} {n : ℕ} (hs : 0 < s) (hn : n ≠ 0) :
    ∫ z : E n, Set.indicator {w : E n | δ / s ≤ ‖s⁻¹ • w‖} (fun w => Real.exp (-‖s⁻¹ • w‖^2)) z =
    s ^ (n : ℝ) * ∫ z : E n, Set.indicator {w : E n | δ / s ≤ ‖w‖} (fun w => Real.exp (-‖w‖^2)) z := by

  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩

  have h_LHS : ∫ z : E n, Set.indicator {w : E n | δ / s ≤ ‖s⁻¹ • w‖} (fun w => Real.exp (-‖s⁻¹ • w‖^2)) z =
    ∫ z : E n, (fun y : ℝ => Set.indicator {u : ℝ | δ / s ≤ |s⁻¹ * u|} (fun u => Real.exp (-(s⁻¹ * u)^2)) y) ‖z‖ := by
    congr 1
    ext z
    have h_norm : ‖s⁻¹ • z‖ = |s⁻¹ * ‖z‖| := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg z)]
    by_cases hz : δ / s ≤ ‖s⁻¹ • z‖
    · have hz' : δ / s ≤ |s⁻¹ * ‖z‖| := by rwa [← h_norm]
      have h_mem1 : z ∈ {w : E n | δ / s ≤ ‖s⁻¹ • w‖} := hz
      have h_mem2 : ‖z‖ ∈ {u : ℝ | δ / s ≤ |s⁻¹ * u|} := hz'
      simp_rw [Set.indicator_of_mem h_mem1, Set.indicator_of_mem h_mem2]
      rw [h_norm, sq_abs]
    · have hz' : ¬ (δ / s ≤ |s⁻¹ * ‖z‖|) := by rwa [← h_norm]
      have h_nmem1 : z ∉ {w : E n | δ / s ≤ ‖s⁻¹ • w‖} := hz
      have h_nmem2 : ‖z‖ ∉ {u : ℝ | δ / s ≤ |s⁻¹ * u|} := hz'
      simp_rw [Set.indicator_of_notMem h_nmem1, Set.indicator_of_notMem h_nmem2]

  have h_RHS : ∫ z : E n, Set.indicator {w : E n | δ / s ≤ ‖w‖} (fun w => Real.exp (-‖w‖^2)) z =
    ∫ z : E n, (fun y : ℝ => Set.indicator {u : ℝ | δ / s ≤ |u|} (fun u => Real.exp (-u^2)) y) ‖z‖ := by
    congr 1
    ext z
    have h_norm : ‖z‖ = |‖z‖| := (abs_of_nonneg (norm_nonneg z)).symm
    by_cases hz : δ / s ≤ ‖z‖
    · have hz' : δ / s ≤ |‖z‖| := by rwa [← h_norm]
      have h_mem1 : z ∈ {w : E n | δ / s ≤ ‖w‖} := hz
      have h_mem2 : ‖z‖ ∈ {u : ℝ | δ / s ≤ |u|} := hz'
      simp_rw [Set.indicator_of_mem h_mem1, Set.indicator_of_mem h_mem2]
    · have hz' : ¬ (δ / s ≤ |‖z‖|) := by rwa [← h_norm]
      have h_nmem1 : z ∉ {w : E n | δ / s ≤ ‖w‖} := hz
      have h_nmem2 : ‖z‖ ∉ {u : ℝ | δ / s ≤ |u|} := hz'
      simp_rw [Set.indicator_of_notMem h_nmem1, Set.indicator_of_notMem h_nmem2]
  rw [h_LHS, h_RHS]

  rw [MeasureTheory.integral_fun_norm_addHaar volume (fun y : ℝ => Set.indicator {u : ℝ | δ / s ≤ |s⁻¹ * u|} (fun u => Real.exp (-(s⁻¹ * u)^2)) y)]
  rw [MeasureTheory.integral_fun_norm_addHaar volume (fun y : ℝ => Set.indicator {u : ℝ | δ / s ≤ |u|} (fun u => Real.exp (-u^2)) y)]
  have h_dim : Module.finrank ℝ (E n) = n := by exact finrank_euclideanSpace_fin
  rw [h_dim]
  simp_rw [smul_eq_mul]
  rw [integral_radial_1D_equiv hs hn]
  ring

lemma heatTail_changeOfVariablesND {α t δ : ℝ} {n : ℕ} (x : E n) (hα : 0 < α) (ht : 0 < t) (hn : n ≠ 0) :
    (∫ y : E n, Set.indicator {y : E n | δ ≤ ‖y - x‖}
              (fun y => heatKernelND α (x - y) t) y)
    = (1 / Real.pi ^ ((n : ℝ) / 2)) *
      ∫ z : E n, Set.indicator
               {z : E n | (δ / Real.sqrt (4 * α * t)) ≤ ‖z‖}
               (fun z => Real.exp (-‖z‖^2)) z := by
  let s : ℝ := Real.sqrt (4 * α * t)
  have hs : 0 < s := by positivity

  have h_shift : ∫ y : E n, Set.indicator {y : E n | δ ≤ ‖y - x‖} (fun y => heatKernelND α (x - y) t) y =
                 ∫ z : E n, Set.indicator {z : E n | δ ≤ ‖z‖} (fun z => heatKernelND α z t) z := by
    have h_eq : ∫ y : E n, Set.indicator {y : E n | δ ≤ ‖y - x‖} (fun y => heatKernelND α (x - y) t) y =
                ∫ y : E n, (fun z => Set.indicator {w : E n | δ ≤ ‖w‖} (fun w => heatKernelND α w t) z) (y - x) := by
      congr 1
      ext y
      dsimp only
      by_cases hz : δ ≤ ‖y - x‖
      · have h_mem1 : y ∈ {y' : E n | δ ≤ ‖y' - x‖} := hz
        have h_mem2 : y - x ∈ {w : E n | δ ≤ ‖w‖} := hz
        rw [Set.indicator_of_mem h_mem1, Set.indicator_of_mem h_mem2]
        have h_symm : x - y = -(y - x) := by abel
        rw [h_symm, heatKernelND_even]
      · have h_nmem1 : y ∉ {y' : E n | δ ≤ ‖y' - x‖} := hz
        have h_nmem2 : y - x ∉ {w : E n | δ ≤ ‖w‖} := hz
        rw [Set.indicator_of_notMem h_nmem1, Set.indicator_of_notMem h_nmem2]
    rw [h_eq]
    exact MeasureTheory.integral_sub_right_eq_self (fun z => Set.indicator {w : E n | δ ≤ ‖w‖} (fun w => heatKernelND α w t) z) x

  have h_const : ∫ z : E n, Set.indicator {z : E n | δ ≤ ‖z‖} (fun z => heatKernelND α z t) z =
                 (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * ∫ z : E n, Set.indicator {z : E n | δ ≤ ‖z‖} (fun z => Real.exp (-‖z‖^2 / (4 * α * t))) z := by
    have h_integrand : (fun z : E n => Set.indicator {w : E n | δ ≤ ‖w‖} (fun w => heatKernelND α w t) z) =
                       (fun z : E n => (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * Set.indicator {w : E n | δ ≤ ‖w‖} (fun w => Real.exp (-‖w‖^2 / (4 * α * t))) z) := by
      ext z
      unfold heatKernelND
      by_cases hz : δ ≤ ‖z‖
      · have h_mem : z ∈ {w : E n | δ ≤ ‖w‖} := hz
        rw [Set.indicator_of_mem h_mem, Set.indicator_of_mem h_mem]
      · have h_nmem : z ∉ {w : E n | δ ≤ ‖w‖} := hz
        rw [Set.indicator_of_notMem h_nmem, Set.indicator_of_notMem h_nmem, mul_zero]
    rw [h_integrand]
    rw [MeasureTheory.integral_const_mul]

  have h_scale_integrand : ∫ z : E n, Set.indicator {z : E n | δ ≤ ‖z‖} (fun z => Real.exp (-‖z‖^2 / (4 * α * t))) z =
                           ∫ z : E n, Set.indicator {w : E n | δ / s ≤ ‖s⁻¹ • w‖} (fun w => Real.exp (-‖s⁻¹ • w‖^2)) z := by
    congr 1
    ext z
    have h_norm : ‖s⁻¹ • z‖ = s⁻¹ * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    have h_sq : ‖s⁻¹ • z‖^2 = ‖z‖^2 / (4 * α * t) := by
      rw [h_norm, mul_pow]
      have hs_sq : (s⁻¹)^2 = 1 / (4 * α * t) := by
        have h1 : (s⁻¹)^2 = (s^2)⁻¹ := by rw [inv_pow]
        have h2 : s^2 = 4 * α * t := by
          change (Real.sqrt (4 * α * t))^2 = 4 * α * t
          exact Real.sq_sqrt (by positivity)
        rw [h1, h2, inv_eq_one_div]
      rw [hs_sq]
      ring
    have h_cond : δ / s ≤ ‖s⁻¹ • z‖ ↔ δ ≤ ‖z‖ := by
      rw [h_norm]
      rw [div_le_iff₀ hs]
      have h_simp : s⁻¹ * ‖z‖ * s = ‖z‖ := by
        calc s⁻¹ * ‖z‖ * s = (s⁻¹ * s) * ‖z‖ := by ring
             _ = 1 * ‖z‖ := by rw [inv_mul_cancel₀ hs.ne.symm]
             _ = ‖z‖ := by ring
      rw [h_simp]
    by_cases hz : δ ≤ ‖z‖
    · have hz' : δ / s ≤ ‖s⁻¹ • z‖ := h_cond.mpr hz
      have h_mem1 : z ∈ {z' : E n | δ ≤ ‖z'‖} := hz
      have h_mem2 : z ∈ {w : E n | δ / s ≤ ‖s⁻¹ • w‖} := hz'
      rw [Set.indicator_of_mem h_mem1, Set.indicator_of_mem h_mem2]
      rw [h_sq]
      field_simp
    · have hz' : ¬ (δ / s ≤ ‖s⁻¹ • z‖) := fun h => hz (h_cond.mp h)
      have h_nmem1 : z ∉ {z' : E n | δ ≤ ‖z'‖} := hz
      have h_nmem2 : z ∉ {w : E n | δ / s ≤ ‖s⁻¹ • w‖} := hz'
      rw [Set.indicator_of_notMem h_nmem1, Set.indicator_of_notMem h_nmem2]

  have h_algebra : (1 / (Real.sqrt (4 * Real.pi * α * t)) ^ n) * s ^ (n : ℝ) = 1 / Real.pi ^ ((n : ℝ) / 2) := by
    rw [Real.rpow_natCast s n]
    have h_sqrt_mul : Real.sqrt (4 * Real.pi * α * t) = Real.sqrt Real.pi * s := by
      have h_pi_pos : 0 ≤ Real.pi := Real.pi_pos.le
      have h_eq : 4 * Real.pi * α * t = Real.pi * (4 * α * t) := by ring
      rw [h_eq, Real.sqrt_mul h_pi_pos]
    rw [h_sqrt_mul, mul_pow]
    have hs_pow_ne : s ^ n ≠ 0 := ne_of_gt (pow_pos hs n)
    have h_pi_pow_ne : (Real.sqrt Real.pi) ^ n ≠ 0 := ne_of_gt (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) n)
    have h_lhs : (1 / ((Real.sqrt Real.pi) ^ n * s ^ n)) * s ^ n = 1 / (Real.sqrt Real.pi) ^ n := by
      field_simp
    rw [h_lhs]
    congr 1
    have h_pi_pos_le : 0 ≤ Real.pi := Real.pi_pos.le
    have h_div : (n : ℝ) / 2 = (1 / 2 : ℝ) * (n : ℝ) := by ring
    rw [h_div, Real.rpow_mul h_pi_pos_le, ← Real.sqrt_eq_rpow, Real.rpow_natCast]

  rw [h_shift, h_const, h_scale_integrand]
  rw [integral_comp_smul_indicator_gaussian hs hn]
  rw [← mul_assoc, h_algebra]

def IsBoundedAbsND (g : E n → ℝ) : Prop := ∃ B, ∀ y, |g y| ≤ B

lemma integrable_gaussianND : Integrable (fun z : E n => Real.exp (-‖z‖^2)) := by
  have h_int := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace (b := (1 : ℂ)) (by norm_num : 0 < (1 : ℂ).re) (0 : ℂ) (0 : E n)
  have h_eq : (fun z : E n => Real.exp (-‖z‖^2)) = fun z => (Complex.exp (-(1 : ℂ) * ↑‖z‖ ^ 2 + (0 : ℂ) * ↑(inner ℝ (0 : E n) z))).re := by
    ext z
    have h1 : (0 : ℂ) * ↑(inner ℝ (0 : E n) z) = 0 := by ring
    have h2 : -(1 : ℂ) * (↑‖z‖ : ℂ) ^ 2 = ↑(-‖z‖^2 : ℝ) := by
      push_cast
      ring
    rw [h1, add_zero, h2]
    have h3 : Complex.exp ↑(-‖z‖^2 : ℝ) = ↑(Real.exp (-‖z‖^2)) := by exact_mod_cast rfl
    rw [h3]
    rfl
  rw [h_eq]
  exact h_int.re

lemma gaussian_tail_boundND {R : ℝ} (hR : 0 < R) (z : E n) :
    Set.indicator {w : E n | R ≤ ‖w‖} (fun w => Real.exp (-‖w‖^2)) z
      ≤ (1 / R ^ 2) * (‖z‖ ^ (2 : ℝ) * Real.exp (-‖z‖^2)) := by
  by_cases hz : R ≤ ‖z‖
  · have h_mem : z ∈ {w : E n | R ≤ ‖w‖} := hz
    rw [Set.indicator_of_mem h_mem]
    have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [h2, Real.rpow_natCast]
    have h_R_pos : 0 ≤ R := le_of_lt hR
    have h_sq_le : R ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith
    have h_R_sq_pos : 0 < R ^ 2 := pow_pos hR 2
    have h_exp_nonneg : 0 ≤ Real.exp (-‖z‖^2) := by positivity
    have h_mul_le : R ^ 2 * Real.exp (-‖z‖^2) ≤ ‖z‖ ^ 2 * Real.exp (-‖z‖^2) :=
      mul_le_mul_of_nonneg_right h_sq_le h_exp_nonneg
    have h_inv_nonneg : 0 ≤ 1 / R ^ 2 := by positivity
    have h_div : (1 / R ^ 2) * (R ^ 2 * Real.exp (-‖z‖^2)) ≤ (1 / R ^ 2) * (‖z‖ ^ 2 * Real.exp (-‖z‖^2)) :=
      mul_le_mul_of_nonneg_left h_mul_le h_inv_nonneg
    have h_cancel : (1 / R ^ 2) * (R ^ 2 * Real.exp (-‖z‖^2)) = Real.exp (-‖z‖^2) := by
      have h_R_sq_ne : R ^ 2 ≠ 0 := ne_of_gt h_R_sq_pos
      calc (1 / R ^ 2) * (R ^ 2 * Real.exp (-‖z‖^2)) = (R ^ 2 / R ^ 2) * Real.exp (-‖z‖^2) := by ring
           _ = 1 * Real.exp (-‖z‖^2) := by rw [div_self h_R_sq_ne]
           _ = Real.exp (-‖z‖^2) := by ring
    rwa [h_cancel] at h_div
  · have h_nmem : z ∉ {w : E n | R ≤ ‖w‖} := hz
    rw [Set.indicator_of_notMem h_nmem]
    have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [h2, Real.rpow_natCast]
    positivity



lemma integrable_norm_rpow_two_mul_gaussianND :
    Integrable (fun z : E n => ‖z‖ ^ (2 : ℝ) * Real.exp (-‖z‖^2)) := by
  by_cases hn : n = 0
  · subst hn
    have h_zero : (fun z : E 0 => ‖z‖ ^ (2 : ℝ) * Real.exp (-‖z‖^2)) = 0 := by
      ext z
      have hz : z = 0 := Subsingleton.elim z 0
      rw [hz, norm_zero, Real.rpow_two]
      simp
    rw [h_zero]
    exact integrable_zero _ _ _
  · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    apply (MeasureTheory.integrable_fun_norm_addHaar volume (f := fun y : ℝ => y ^ (2 : ℝ) * Real.exp (-y^2))).mpr
    have h_dim : Module.finrank ℝ (E n) = n := finrank_euclideanSpace_fin
    rw [h_dim]
    have hs : (-1 : ℝ) < (((n - 1 : ℕ) : ℝ) + (2 : ℝ)) := by
      calc (-1 : ℝ) < 0 := by norm_num
        _ ≤ (((n - 1 : ℕ) : ℝ) + (2 : ℝ)) := by positivity
    have h_int : Integrable (fun y : ℝ => y ^ (((n - 1 : ℕ) : ℝ) + (2 : ℝ)) * Real.exp (-(1 : ℝ) * y ^ 2)) :=
      integrable_rpow_mul_exp_neg_mul_sq (by positivity) hs
    refine MeasureTheory.IntegrableOn.congr_fun h_int.integrableOn (fun y hy => ?_) measurableSet_Ioi
    rw [neg_mul, one_mul, smul_eq_mul]
    have h_pow : y ^ (((n - 1 : ℕ) : ℝ) + (2 : ℝ)) = y ^ (n - 1 : ℕ) * y ^ (2 : ℝ) := by
      rw [Real.rpow_add hy, Real.rpow_natCast]
    rw [h_pow, mul_assoc]

lemma gaussian_tail_tendsto_zeroND :
    Tendsto (fun R : ℝ => ∫ z : E n, Set.indicator {w : E n | R ≤ ‖w‖} (fun w => Real.exp (-‖w‖^2)) z) atTop (𝓝 0) := by
  have h_lim : Tendsto (fun R : ℝ => (1 / R ^ 2) * ∫ z : E n, ‖z‖ ^ (2 : ℝ) * Real.exp (-‖z‖^2)) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num))).mul_const _
  have h_bound : ∀ᶠ R in atTop, ∫ z : E n, Set.indicator {w : E n | R ≤ ‖w‖} (fun w => Real.exp (-‖w‖^2)) z ≤ (1 / R ^ 2) * ∫ z : E n, ‖z‖ ^ (2 : ℝ) * Real.exp (-‖z‖^2) := by
    refine eventually_atTop.2 ⟨1, fun R hR => ?_⟩
    rw [← MeasureTheory.integral_const_mul]
    have hIntR : Integrable (fun z : E n => (1 / R ^ 2) * (‖z‖ ^ (2 : ℝ) * Real.exp (-‖z‖^2))) :=
      integrable_norm_rpow_two_mul_gaussianND.const_mul (1 / R ^ 2)
    exact integral_mono (Integrable.indicator integrable_gaussianND (isClosed_le continuous_const continuous_norm).measurableSet) hIntR (fun z => gaussian_tail_boundND (by positivity) z)
  refine squeeze_zero' (Eventually.of_forall fun R => integral_nonneg fun z => ?_) h_bound h_lim
  by_cases hz : R ≤ ‖z‖
  · rw [Set.indicator_of_mem (hz : z ∈ _)]
    positivity
  · rw [Set.indicator_of_notMem (hz : z ∉ _)]
    exact le_rfl

lemma heatKernelND_tail_tendsto_zero {α δ : ℝ} (x : E n) (hα : 0 < α) (hδ : 0 < δ) (hn : n ≠ 0) :
    Tendsto (fun t : ℝ => ∫ y : E n, Set.indicator {y : E n | δ ≤ ‖y - x‖} (fun y => heatKernelND α (x - y) t) y) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
  have h_sqrt : Tendsto (fun t : ℝ => Real.sqrt (4 * α * t)) (𝓝[>] 0) (𝓝[>] 0) := by
    have h_cont : Continuous (fun t : ℝ => Real.sqrt (4 * α * t)) := continuous_sqrt.comp (continuous_const.mul continuous_id)
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_of_mem self_mem_nhdsWithin fun t _ => by aesop⟩
    simpa using (h_cont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine (tendsto_congr' (eventually_of_mem self_mem_nhdsWithin fun t ht => heatTail_changeOfVariablesND x hα ht hn)).mpr ?_
  have h_comp := (@gaussian_tail_tendsto_zeroND n).comp (Tendsto.const_mul_atTop hδ (tendsto_inv_nhdsGT_zero.comp h_sqrt))
  have h_tendsto := Tendsto.const_mul (1 / Real.pi ^ ((n : ℝ) / 2)) h_comp
  rw [mul_zero] at h_tendsto
  refine Tendsto.congr' ?_ h_tendsto
  apply Eventually.of_forall
  intro t
  simp [Function.comp, div_eq_mul_inv]

lemma heatKernelND_mul_g_sub_bound {α t : ℝ} (x y : E n) (B_bound : ℝ) (g : E n → ℝ)
    (hα : 0 < α) (ht : 0 < t) (hB : ∀ z, |g z| ≤ B_bound) :
    ‖heatKernelND α (x - y) t * (g y - g x)‖ ≤ ‖(B_bound + |g x|) * heatKernelND α (x - y) t‖ := by
  simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by unfold heatKernelND; positivity : 0 ≤ heatKernelND α (x - y) t),
      abs_of_nonneg (add_nonneg ((abs_nonneg (g x)).trans (hB x)) (abs_nonneg (g x))), mul_comm (B_bound + |g x|)]
  exact mul_le_mul_of_nonneg_left
    (le_trans (show |g y - g x| ≤ |g y| + |g x| by simpa [sub_eq_add_neg] using abs_add_le (g y) (-g x)) (add_le_add_left (hB y) _))
    (by unfold heatKernelND; positivity)

lemma integrable_heatKernelND_mul_g_sub {α t : ℝ} (x : E n) (B_bound : ℝ) (g : E n → ℝ)
    (hα : 0 < α) (ht : 0 < t) (hB : ∀ z, |g z| ≤ B_bound) (g_cont : Continuous g) :
    Integrable (fun y : E n => heatKernelND α (x - y) t * (g y - g x)) := by
  exact ((integrable_heatKernelND_slice hα ht x).const_mul (B_bound + |g x|)).mono
    (Continuous.aestronglyMeasurable (by unfold heatKernelND; continuity))
    (Eventually.of_forall fun y => heatKernelND_mul_g_sub_bound x y B_bound g hα ht hB)

lemma heatKernelND_approx_near {α t ε δ : ℝ} (x : E n) (g : E n → ℝ)
    (hα : 0 < α) (ht : 0 < t) (hε : 0 < ε)
    (hδ : ∀ ⦃y⦄, ‖y - x‖ < δ → |g y - g x| < ε / 2)
    (hInt_near : Integrable (fun y : E n => (Set.indicator {z | δ ≤ ‖z - x‖}ᶜ (fun y => heatKernelND α (x - y) t * (g y - g x))) y)) :
    |∫ y : E n, (Set.indicator {z | δ ≤ ‖z - x‖}ᶜ (fun y => heatKernelND α (x - y) t * (g y - g x))) y| ≤ ε / 2 := by
  rw [← Real.norm_eq_abs, ← show ∫ y : E n, heatKernelND α (x - y) t * (ε / 2) = ε / 2 by rw [integral_mul_const, heatKernelND_mass_one_x_sub_y_even x hα ht, one_mul]]
  refine le_trans (norm_integral_le_integral_norm _) (integral_mono hInt_near.norm ((integrable_heatKernelND_slice hα ht x).mul_const (ε / 2)) fun y => ?_)
  by_cases hy : y ∈ {z : E n | δ ≤ ‖z - x‖}ᶜ
  · rw [Set.indicator_of_mem (hy : y ∈ _), norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by unfold heatKernelND; positivity : 0 ≤ heatKernelND α (x - y) t)]
    exact mul_le_mul_of_nonneg_left (hδ (not_le.mp hy)).le (by unfold heatKernelND; positivity)
  · rw [Set.indicator_of_notMem (hy : y ∉ _), norm_zero]
    exact mul_nonneg (by unfold heatKernelND; positivity) (by positivity)

lemma heatKernelND_approx_far {α t ε δ B_bound : ℝ} (x : E n) (g : E n → ℝ)
    (hα : 0 < α) (ht : 0 < t) (hε : 0 < ε)
    (hB : ∀ z, |g z| ≤ B_bound)
    (ht_tail : |∫ y : E n, (Set.indicator {z | δ ≤ ‖z - x‖} (fun y => heatKernelND α (x - y) t)) y| ≤ ε / (4 * (B_bound + |g x| + 1)))
    (hInt_far : Integrable (fun y : E n => (Set.indicator {z | δ ≤ ‖z - x‖} (fun y => heatKernelND α (x - y) t * (g y - g x))) y)) :
    |∫ y : E n, (Set.indicator {z | δ ≤ ‖z - x‖} (fun y => heatKernelND α (x - y) t * (g y - g x))) y| < ε / 2 := by
  have h_B_pos : 0 ≤ B_bound + |g x| := add_nonneg ((abs_nonneg (g x)).trans (hB x)) (abs_nonneg (g x))
  rw [← Real.norm_eq_abs]
  refine lt_of_le_of_lt (b := (B_bound + |g x|) * (ε / (4 * (B_bound + |g x| + 1)))) ?_ ?_
  · refine le_trans (b := ∫ y : E n, ‖(Set.indicator {z | δ ≤ ‖z - x‖} (fun y => heatKernelND α (x - y) t * (g y - g x))) y‖) (norm_integral_le_integral_norm _) ?_
    refine le_trans (b := ∫ y : E n, (B_bound + |g x|) * (Set.indicator {z : E n | δ ≤ ‖z - x‖} (fun y => heatKernelND α (x - y) t)) y) ?_ ?_
    · refine integral_mono hInt_far.norm (((integrable_heatKernelND_slice hα ht x).indicator (isClosed_le continuous_const (by continuity : Continuous (fun z : E n => ‖z - x‖))).measurableSet).const_mul (B_bound + |g x|)) fun y => ?_
      by_cases hy : y ∈ {z : E n | δ ≤ ‖z - x‖}
      · rw [Set.indicator_of_mem (hy : y ∈ _), Set.indicator_of_mem (hy : y ∈ _)]
        rw [← show ‖(B_bound + |g x|) * heatKernelND α (x - y) t‖ = (B_bound + |g x|) * heatKernelND α (x - y) t by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h_B_pos (by unfold heatKernelND; positivity : 0 ≤ heatKernelND α (x - y) t))]]
        exact heatKernelND_mul_g_sub_bound x y B_bound g hα ht hB
      · rw [Set.indicator_of_notMem (hy : y ∉ _), Set.indicator_of_notMem (hy : y ∉ _), norm_zero, mul_zero]
    · rw [MeasureTheory.integral_const_mul, ← abs_of_nonneg (integral_nonneg fun y => ?_)]
      · exact mul_le_mul_of_nonneg_left ht_tail h_B_pos
      · by_cases hy : y ∈ {z : E n | δ ≤ ‖z - x‖}
        · rw [Set.indicator_of_mem (hy : y ∈ _)]; unfold heatKernelND; positivity
        · rw [Set.indicator_of_notMem (hy : y ∉ _)]; exact le_rfl
  · rw [← mul_div_assoc, div_lt_iff₀ (by positivity), show (ε / 2) * (4 * (B_bound + |g x| + 1)) = 2 * (B_bound + |g x| + 1) * ε by ring]
    exact mul_lt_mul_of_pos_right (by linarith) hε

lemma heatKernelND_approx_identity {α : ℝ} (g : E n → ℝ) (x : E n)
    (hα : 0 < α) (g_bounded : IsBoundedAbsND g) (g_cont : Continuous g) (hn : n ≠ 0) :
    Tendsto (fun t : ℝ => ∫ y : E n, heatKernelND α (x - y) t * (g y - g x)) (𝓝[>] 0) (𝓝 0) := by
  classical
  rcases g_bounded with ⟨B_bound, hB⟩
  refine Metric.tendsto_nhds.2 (fun ε hε => ?_)
  rcases Metric.mem_nhds_iff.1 (Metric.tendsto_nhds.1 g_cont.continuousAt (ε / 2) (half_pos hε)) with ⟨δ, hδ_pos, hsub⟩
  have hδ : ∀ ⦃y⦄, ‖y - x‖ < δ → |g y - g x| < ε / 2 := fun y hy =>
    by simpa [dist_eq_norm] using hsub (by aesop)
  have h_B_nonneg : 0 ≤ B_bound := (abs_nonneg (g x)).trans (hB x)
  refine eventually_nhdsWithin_iff.mpr ((eventually_nhdsWithin_iff.mp (Metric.tendsto_nhds.1 (heatKernelND_tail_tendsto_zero x hα hδ_pos hn) _ (by positivity : 0 < ε / (4 * (B_bound + |g x| + 1))))).mono fun t ht_imp ht_pos => ?_)
  rw [Real.dist_eq, sub_zero]
  have hInt_whole := integrable_heatKernelND_mul_g_sub x B_bound g hα ht_pos hB g_cont
  have hInt_far := hInt_whole.indicator (s := {z : E n | δ ≤ ‖z - x‖}) (isClosed_le continuous_const (by continuity : Continuous (fun z : E n => ‖z - x‖))).measurableSet
  have hInt_near := hInt_whole.indicator (s := {z : E n | δ ≤ ‖z - x‖}ᶜ) (isClosed_le continuous_const (by continuity : Continuous (fun z : E n => ‖z - x‖))).measurableSet.compl
  rw [show (∫ y : E n, heatKernelND α (x - y) t * (g y - g x)) =
      (∫ y : E n, (Set.indicator {z | δ ≤ ‖z - x‖}ᶜ (fun y => heatKernelND α (x - y) t * (g y - g x))) y) +
      (∫ y : E n, (Set.indicator {z | δ ≤ ‖z - x‖} (fun y => heatKernelND α (x - y) t * (g y - g x))) y) by
        rw [← integral_add hInt_near hInt_far]
        congr 1; ext y; by_cases hy : y ∈ {z : E n | δ ≤ ‖z - x‖}
        · rw [Set.indicator_of_notMem (show y ∉ {z : E n | δ ≤ ‖z - x‖}ᶜ from fun h => h hy), Set.indicator_of_mem hy, zero_add]
        · rw [Set.indicator_of_mem hy, Set.indicator_of_notMem hy, add_zero]]
  rw [← add_halves ε]
  refine lt_of_le_of_lt (b := |∫ y : E n, (Set.indicator {z | δ ≤ ‖z - x‖}ᶜ (fun y => heatKernelND α (x - y) t * (g y - g x))) y| + |∫ y : E n, (Set.indicator {z | δ ≤ ‖z - x‖} (fun y => heatKernelND α (x - y) t * (g y - g x))) y|) (abs_add_le _ _) ?_
  exact add_lt_add_of_le_of_lt (heatKernelND_approx_near x g hα ht_pos hε hδ hInt_near) (heatKernelND_approx_far x g hα ht_pos hε hB (show _ < _ by simpa [Real.dist_eq] using ht_imp ht_pos).le hInt_far)

theorem heatKernelND_IVP_limit
    {α : ℝ} (g : E n → ℝ) (x : E n)
    (hα : 0 < α)
    (g_bounded : IsBoundedAbsND g)
    (g_cont : Continuous g)
    (hn : n ≠ 0) :
    Tendsto (fun t : ℝ => heatConvolutionHKND α g x t) (𝓝[>] 0) (𝓝 (g x)) := by
  rcases g_bounded with ⟨B_bound, hB⟩
  refine (tendsto_congr' (f₂ := fun t => g x + ∫ y : E n, heatKernelND α (x - y) t * (g y - g x)) (eventually_of_mem self_mem_nhdsWithin fun t ht => ?_)).mpr ?_
  · unfold heatConvolutionHKND
    rw [show (fun y : E n => heatKernelND α (x - y) t * g y) = fun y : E n => heatKernelND α (x - y) t * g x + heatKernelND α (x - y) t * (g y - g x) by ext y; ring]
    rw [integral_add ((integrable_heatKernelND_slice hα ht x).mul_const (g x)) (integrable_heatKernelND_mul_g_sub x B_bound g hα ht hB g_cont)]
    rw [integral_mul_const, heatKernelND_mass_one_x_sub_y_even x hα ht, one_mul]
  · simpa using tendsto_const_nhds.add (heatKernelND_approx_identity g x hα ⟨B_bound, hB⟩ g_cont hn)

end
end Heat
