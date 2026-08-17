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
import PDE.Basics.Heat.HeatKernelND

open MeasureTheory Filter InnerProductSpace Measure Set
open scoped Topology ENNReal Interval

namespace Heat

/-
### SECTION 7_2_2 in N dim
-/


noncomputable def heatConvolutionHKND {n : ℕ} (α : ℝ) (g : E n → ℝ) (x : E n) (t : ℝ) : ℝ :=
  ∫ y, heatKernelND α (x - y) t * g y

noncomputable def HKtND {n : ℕ} (α : ℝ) (x : E n) (t : ℝ) : ℝ :=
  deriv (fun τ => heatKernelND α x τ) t

noncomputable def HKgradND {n : ℕ} (α : ℝ) (x : E n) (t : ℝ) : E n :=
  gradient (fun ξ => heatKernelND α ξ t) x

noncomputable def HKlaplacianND {n : ℕ} (α : ℝ) (x : E n) (t : ℝ) : ℝ :=
  laplacian (fun ξ => heatKernelND α ξ t) x

lemma HKtND_eq_derivative {n : ℕ} (hα : 0 < α) {t : ℝ} {x : E n} (ht : 0 < t) :
    HKtND α x t = ((-((n : ℝ) / (2 * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) *
       Real.exp (-‖x‖^2 / (4 * α * t))
     + (1 / (Real.sqrt (4 * Real.pi * α * t))^n) *
       ((1 / (4 * α)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t))) := by
  unfold HKtND
  exact deriv_heatKernelND_t hα ht

lemma HKgradND_eq_derivative {n : ℕ} {α t : ℝ} {x : E n} (ht : 0 < t) (hα : 0 < α) :
    HKgradND α x t = (-(1 / (2 * α * t)) * Real.exp (-‖x‖^2 / (4 * α * t)) *
      (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • x := by
  unfold HKgradND
  rw [gradient_heatKernelND_x hα ht]

lemma HKlaplacianND_eq_derivative {n : ℕ} {α t : ℝ} {x : E n} (ht : 0 < t) (hα : 0 < α) :
    HKlaplacianND α x t = ((-((n : ℝ) / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) *
       Real.exp (-‖x‖^2 / (4 * α * t))
     + (1 / (Real.sqrt (4 * Real.pi * α * t))^n) *
       ((1 / (4 * α^2)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t))) := by
  unfold HKlaplacianND
  exact laplacian_heatKernelND_x hα ht

lemma cont_HKtND {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) :
  Continuous (fun y : E n => HKtND α (x - y) t) := by
  simp_rw [HKtND_eq_derivative hα ht]
  continuity

lemma meas_HKtND {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) :
  AEStronglyMeasurable (fun y : E n => HKtND α (x - y) t) :=
  (cont_HKtND hα ht).aestronglyMeasurable

lemma cont_HKgradND {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) :
  Continuous (fun y : E n => HKgradND α (x - y) t) := by
  simp_rw [HKgradND_eq_derivative ht hα]
  have h_sub : Continuous (fun y : E n => x - y) := continuous_const.sub continuous_id
  have h_norm_sq : Continuous (fun y : E n => ‖x - y‖^2) := Continuous.pow (Continuous.norm h_sub) 2
  have h_exp : Continuous (fun y : E n => Real.exp (-‖x - y‖^2 / (4 * α * t))) :=
    Real.continuous_exp.comp (Continuous.div_const (Continuous.neg h_norm_sq) (4 * α * t))
  have h_coeff : Continuous (fun y : E n => -(1 / (2 * α * t)) * Real.exp (-‖x - y‖^2 / (4 * α * t)) * (1 / √(4 * Real.pi * α * t) ^ n)) :=
    Continuous.mul (Continuous.mul continuous_const h_exp) continuous_const
  exact Continuous.smul h_coeff h_sub

lemma meas_HKgradND {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) :
  AEStronglyMeasurable (fun y : E n => HKgradND α (x - y) t) :=
  (cont_HKgradND hα ht).aestronglyMeasurable

lemma cont_HKlaplacianND {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) :
    Continuous (fun y : E n => HKlaplacianND α (x - y) t) := by
  simp_rw [HKlaplacianND_eq_derivative ht hα]
  continuity

lemma meas_HKlaplacianND {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) :
    AEStronglyMeasurable (fun y : E n => HKlaplacianND α (x - y) t) :=
  (cont_HKlaplacianND hα ht).aestronglyMeasurable

lemma cont_heatKernelND {n : ℕ} {α t : ℝ} {x : E n} :
  Continuous (fun y : E n => heatKernelND α (x - y) t) := by
  unfold heatKernelND
  continuity

lemma meas_heatKernelND {n : ℕ} {α t : ℝ} {x : E n} :
  AEStronglyMeasurable (fun y : E n => heatKernelND α (x - y) t) :=
  cont_heatKernelND.aestronglyMeasurable

noncomputable def KgradND (n : ℕ) (α t : ℝ) : ℝ :=
  1 / (Real.sqrt (α * t) * (Real.sqrt (4 * Real.pi * α * t))^n)

noncomputable def KlaplacianND (n : ℕ) (α t : ℝ) : ℝ :=
  ((n : ℝ) + 2 * Real.exp (-1)) / (2 * α * t * (Real.sqrt (4 * Real.pi * α * t))^n)

lemma exp_heatND_le_one {n : ℕ} (v : E n) (α t : ℝ) (hα : 0 < α) (ht : 0 < t) :
    Real.exp (-‖v‖^2 / (4 * α * t)) ≤ 1 := by
  rw [Real.exp_le_one_iff, neg_div]
  exact neg_nonpos.mpr (by positivity)

lemma heatKernelND_bound_pointwise {n : ℕ} {α t : ℝ} {x : E n}
    (hα : 0 < α) (ht : 0 < t) :
    ∀ y : E n, heatKernelND α (x - y) t ≥ 0 ∧
      heatKernelND α (x - y) t ≤ 1 / (Real.sqrt (4 * Real.pi * α * t))^n := by
  intro y
  unfold heatKernelND
  constructor
  · positivity
  · have hexp := exp_heatND_le_one (x - y) α t hα ht
    simpa using mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 1 / (Real.sqrt (4 * Real.pi * α * t))^n)

lemma Linfty_heatKernelND {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) :
    MemLp (fun y : E n => heatKernelND α (x - y) t) ∞ volume := by
  refine memLp_top_of_bound meas_heatKernelND (1 / (Real.sqrt (4 * Real.pi * α * t))^n) ?_
  filter_upwards with y
  rw [Real.norm_of_nonneg (heatKernelND_bound_pointwise hα ht y).1]
  exact (heatKernelND_bound_pointwise hα ht y).2

lemma bound_norm_exp_neg_norm {x : ℝ} :
    x * Real.exp (-x) ≤ Real.exp (-1) := by
  simpa [← Real.exp_add, sub_eq_add_neg] using
    mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x - 1)) (Real.exp_pos (-x)).le

lemma norm_sq_mul_exp_neg_mul_norm_sq_le {b : ℝ} (hb : 0 < b) (x : ℝ) :
    x^2 * Real.exp (-(b * x^2)) ≤ Real.exp (-1) / b := by
  rw [le_div_iff₀ hb]
  convert bound_norm_exp_neg_norm (x := b * x^2) using 1
  · aesop
  · ring

lemma pointwise_bound_HKtND {n : ℕ} {α t : ℝ} {x : E n} (ht : 0 < t) (hα : 0 < α) :
    |HKtND α x t| ≤ ((n + 2) / (2 * t)) * cND n α t := by
  simp_rw [HKtND_eq_derivative hα ht]
  have h_cND : cND n α t = 1 / (Real.sqrt (4 * Real.pi * α * t))^n := by
    unfold cND heatKND
    rfl
  have bound_1 : |(-((n : ℝ) / (2 * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x‖^2 / (4 * α * t))| ≤ ((n : ℝ) / (2 * t)) * cND n α t := by
    rw [h_cND]
    have h_pos : 0 ≤ ((n : ℝ) / (2 * t) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x‖^2 / (4 * α * t)) := by positivity
    have h_abs : |(-((n : ℝ) / (2 * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x‖^2 / (4 * α * t))| = ((n : ℝ) / (2 * t) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x‖^2 / (4 * α * t)) := by
      calc |(-((n : ℝ) / (2 * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x‖^2 / (4 * α * t))|
        _ = |- (((n : ℝ) / (2 * t) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x‖^2 / (4 * α * t)))| := by congr 1; ring
        _ = (((n : ℝ) / (2 * t) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x‖^2 / (4 * α * t))) := by rw [abs_neg, abs_of_nonneg h_pos]
    rw [h_abs]
    have hexp := exp_heatND_le_one x α t hα ht
    calc ((n : ℝ) / (2 * t) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x‖^2 / (4 * α * t))
      _ ≤ ((n : ℝ) / (2 * t) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((n : ℝ) / (2 * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) := by ring

  have bound_2 : |(1 / (Real.sqrt (4 * Real.pi * α * t))^n) * ((1 / (4 * α)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t))| ≤ (1 / t) * cND n α t := by
    rw [h_cND]
    have h_pos : 0 ≤ (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * ((1 / (4 * α)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t)) := by positivity
    rw [abs_of_nonneg h_pos]
    have rearrange : (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * ((1 / (4 * α)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t)) =
      (1 / t) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * ((‖x‖^2 / (4 * α * t)) * Real.exp (-(‖x‖^2 / (4 * α * t)))) := by ring_nf
    rw [rearrange]
    have bound_exp : (‖x‖^2 / (4 * α * t)) * Real.exp (-(‖x‖^2 / (4 * α * t))) ≤ 1 := by
      calc (‖x‖^2 / (4 * α * t)) * Real.exp (-(‖x‖^2 / (4 * α * t)))
        _ ≤ Real.exp (-1) := bound_norm_exp_neg_norm
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    calc (1 / t) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * ((‖x‖^2 / (4 * α * t)) * Real.exp (-(‖x‖^2 / (4 * α * t))))
      _ ≤ (1 / t) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * 1 := mul_le_mul_of_nonneg_left bound_exp (by positivity)
      _ = (1 / t) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) := mul_one _
  calc
    |(-((n : ℝ) / (2 * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x‖^2 / (4 * α * t)) + (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * ((1 / (4 * α)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t))|
      ≤ |(-((n : ℝ) / (2 * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x‖^2 / (4 * α * t))| + |(1 / (Real.sqrt (4 * Real.pi * α * t))^n) * ((1 / (4 * α)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t))| := abs_add_le _ _
    _ ≤ ((n : ℝ) / (2 * t)) * cND n α t + (1 / t) * cND n α t := add_le_add bound_1 bound_2
    _ = ((n + 2) / (2 * t)) * cND n α t := by
      ring

lemma HKtND_Linfinity_bound {n : ℕ} {α t : ℝ} {x : E n} (ht : 0 < t) (hα : 0 < α) :
    MemLp (fun y : E n => HKtND α (x - y) t) ∞ volume := by
  refine memLp_top_of_bound (meas_HKtND hα ht) (((n + 2) / (2 * t)) * cND n α t) ?_
  filter_upwards with y
  exact pointwise_bound_HKtND ht hα

lemma pointwise_bound_HKgradND {n : ℕ} {α t : ℝ} {x : E n} (ht : 0 < t) (hα : 0 < α) :
    ‖HKgradND α x t‖ ≤ KgradND n α t := by
  rw [HKgradND_eq_derivative ht hα]
  have h_norm : ‖(-(1 / (2 * α * t)) * Real.exp (-‖x‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • x‖ =
    (1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * (‖x‖ * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
    have h1 : 0 ≤ 1 / (2 * α * t) := by positivity
    have h2 : 0 ≤ Real.exp (-‖x‖^2 / (4 * α * t)) := by positivity
    have h3 : 0 ≤ 1 / (Real.sqrt (4 * Real.pi * α * t))^n := by positivity
    rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3]
    have h_exp : Real.exp (-‖x‖^2 / (4 * α * t)) = Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) := by congr 1; ring
    rw [h_exp]
    ring

  have h_base : ‖x‖ * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) ≤ (Real.sqrt (1 / (4 * α * t)))⁻¹ := by
    have hε : 0 < 1 / (4 * α * t) := by positivity
    have h_bound := Real.abs_mulExpNegMulSq_le (hε := hε) (x := ‖x‖)
    have h_pos : 0 ≤ ‖x‖ * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) := by positivity
    calc ‖x‖ * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2)
      _ = |‖x‖ * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2)| := (abs_of_nonneg h_pos).symm
      _ ≤ (Real.sqrt (1 / (4 * α * t)))⁻¹ := by
        simpa [Real.mulExpNegMulSq, mul_comm, mul_left_comm, mul_assoc, pow_two] using h_bound

  have h_KgradND : KgradND n α t = (1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * (Real.sqrt (1 / (4 * α * t)))⁻¹ := by
    have h1 : 0 < α * t := mul_pos hα ht
    have h2 : Real.sqrt (1 / (4 * α * t)) = 1 / (2 * Real.sqrt (α * t)) := by
      have hd : (0 : ℝ) ≤ 4 := by norm_num
      rw [Real.sqrt_div (by positivity), Real.sqrt_one]
      field_simp
      ring_nf
      simp[hd]
      left
      ring
    have h3 : (Real.sqrt (α * t))^2 = α * t := Real.sq_sqrt (le_of_lt h1)
    rw [h2, inv_div, div_one]
    unfold KgradND
    calc 1 / (Real.sqrt (α * t) * (Real.sqrt (4 * Real.pi * α * t)) ^ n)
      _ = (1 / (2 * (Real.sqrt (α * t))^2)) * (1 / (Real.sqrt (4 * Real.pi * α * t)) ^ n) * (2 * Real.sqrt (α * t)) := by
        have h_ne : Real.sqrt (α * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h1)
        have hp_pos : 0 < Real.sqrt (4 * Real.pi * α * t) := Real.sqrt_pos.mpr (by positivity)
        have hp_ne : (Real.sqrt (4 * Real.pi * α * t)) ^ n ≠ 0 := ne_of_gt (pow_pos hp_pos n)
        field_simp
      _ = (1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t)) ^ n) * (2 * Real.sqrt (α * t)) := by
        rw[h3]
        field_simp
  rw [h_norm, h_KgradND]
  have h_pos : 0 ≤ (1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) := by
    positivity
  exact mul_le_mul_of_nonneg_left h_base h_pos

lemma HKgradND_Linfinity_bound {n : ℕ} {α t : ℝ} {x : E n} (ht : 0 < t) (hα : 0 < α) :
    MemLp (fun y : E n => HKgradND α (x - y) t) ∞ volume := by
  refine memLp_top_of_bound (meas_HKgradND hα ht) (KgradND n α t) ?_
  filter_upwards with y
  exact pointwise_bound_HKgradND ht hα

lemma HKlaplacianND_uniform_bound {n : ℕ} {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    ∀ x : E n, |HKlaplacianND α x t| ≤ KlaplacianND n α t := by
  intro x
  rw [HKlaplacianND_eq_derivative ht hα]

  have expr_eq : ((-((n : ℝ) / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖x‖^2 / (4 * α * t)) +
    (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * ((1 / (4 * α^2)) * (1 / t^2) * ‖x‖^2) * Real.exp (-‖x‖^2 / (4 * α * t))) =
    (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * (-((n : ℝ) / (2 * α * t)) + (1 / (4 * α^2 * t^2)) * ‖x‖^2) * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) := by
    have h_exp : -‖x‖^2 / (4 * α * t) = -(1 / (4 * α * t)) * ‖x‖^2 := by ring
    rw [h_exp]
    ring

  rw [expr_eq]

  have hexp_le_one : Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    aesop

  have core_bound : |-((n : ℝ) / (2 * α * t)) + (1 / (4 * α^2 * t^2)) * ‖x‖^2| * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) ≤
    ((n : ℝ) / (2 * α * t)) + (1 / (α * t)) * Real.exp (-1) := by
    have h_abs1 : |-((n : ℝ) / (2 * α * t))| = (n : ℝ) / (2 * α * t) := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
    have h_abs2 : |(1 / (4 * α^2 * t^2)) * ‖x‖^2| = (1 / (4 * α^2 * t^2)) * ‖x‖^2 := abs_of_nonneg (by positivity)
    have h_bound_apply : ((1 / (4 * α * t)) * ‖x‖^2) * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) ≤ Real.exp (-1) := by
      have h_eq : -(1 / (4 * α * t)) * ‖x‖^2 = -((1 / (4 * α * t)) * ‖x‖^2) := by ring
      rw [h_eq]
      exact bound_norm_exp_neg_norm
    calc |-((n : ℝ) / (2 * α * t)) + (1 / (4 * α^2 * t^2)) * ‖x‖^2| * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2)
      _ ≤ (|-((n : ℝ) / (2 * α * t))| + |(1 / (4 * α^2 * t^2)) * ‖x‖^2|) * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) := mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)
      _ = (((n : ℝ) / (2 * α * t)) + (1 / (4 * α^2 * t^2)) * ‖x‖^2) * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) := by rw [h_abs1, h_abs2]
      _ = ((n : ℝ) / (2 * α * t)) * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) + ((1 / (4 * α^2 * t^2)) * ‖x‖^2) * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) := by ring
      _ ≤ ((n : ℝ) / (2 * α * t)) * 1 + ((1 / (4 * α^2 * t^2)) * ‖x‖^2) * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) := by
        gcongr
      _ = ((n : ℝ) / (2 * α * t)) + (1 / (α * t)) * (((1 / (4 * α * t)) * ‖x‖^2) * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2)) := by ring
      _ ≤ ((n : ℝ) / (2 * α * t)) + (1 / (α * t)) * Real.exp (-1) := by
        gcongr

  calc |(1 / (Real.sqrt (4 * Real.pi * α * t))^n) * (-((n : ℝ) / (2 * α * t)) + (1 / (4 * α^2 * t^2)) * ‖x‖^2) * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2)|
    _ = |1 / (Real.sqrt (4 * Real.pi * α * t))^n| * (|-((n : ℝ) / (2 * α * t)) + (1 / (4 * α^2 * t^2)) * ‖x‖^2| * |Real.exp (-(1 / (4 * α * t)) * ‖x‖^2)|) := by
      rw [abs_mul, abs_mul, mul_assoc]
    _ = (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * (|-((n : ℝ) / (2 * α * t)) + (1 / (4 * α^2 * t^2)) * ‖x‖^2| * Real.exp (-(1 / (4 * α * t)) * ‖x‖^2)) := by
      have h_coeff_pos : 0 ≤ 1 / (Real.sqrt (4 * Real.pi * α * t))^n := by positivity
      have h_exp_pos : 0 ≤ Real.exp (-(1 / (4 * α * t)) * ‖x‖^2) := by positivity
      rw [abs_of_nonneg h_coeff_pos, abs_of_nonneg h_exp_pos]
    _ ≤ (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * (((n : ℝ) / (2 * α * t)) + (1 / (α * t)) * Real.exp (-1)) := by
      exact mul_le_mul_of_nonneg_left core_bound (by positivity)
    _ = KlaplacianND n α t := by
      unfold KlaplacianND
      have h_eq : ((n : ℝ) / (2 * α * t)) + (1 / (α * t)) * Real.exp (-1) = ((n : ℝ) + 2 * Real.exp (-1)) / (2 * α * t) := by ring
      rw [h_eq]
      ring

lemma pointwise_bound_HKlaplacianND {n : ℕ} {α t : ℝ} {x : E n} (ht : 0 < t) (hα : 0 < α) :
    |HKlaplacianND α x t| ≤ KlaplacianND n α t := by
  exact HKlaplacianND_uniform_bound hα ht x

lemma HKlaplacianND_Linfinity_bound {n : ℕ} {α t : ℝ} {x : E n} (ht : 0 < t) (hα : 0 < α) :
    MemLp (fun y : E n => HKlaplacianND α (x - y) t) ∞ volume := by
  refine memLp_top_of_bound (meas_HKlaplacianND hα ht) (KlaplacianND n α t) ?_
  filter_upwards with y
  exact pointwise_bound_HKlaplacianND ht hα

lemma mono_CoeffND {n : ℕ} {α t τ : ℝ} (hτ : 0 < τ) (hα : 0 < α) (hsize : τ ≤ t) :
    cND n α t ≤ cND n α τ := by
  have ht : 0 < t := lt_of_lt_of_le hτ hsize
  have h_cND_t : cND n α t = 1 / (Real.sqrt (4 * Real.pi * α * t))^n := by
    unfold cND heatKND
    rfl
  have h_cND_τ : cND n α τ = 1 / (Real.sqrt (4 * Real.pi * α * τ))^n := by
    unfold cND heatKND
    rfl
  rw [h_cND_t, h_cND_τ]
  have h_sqrt : Real.sqrt (4 * Real.pi * α * τ) ≤ Real.sqrt (4 * Real.pi * α * t) := by
    refine Real.sqrt_le_sqrt ?_
    exact mul_le_mul_of_nonneg_left hsize (by positivity)
  have h_le : (Real.sqrt (4 * Real.pi * α * τ))^n ≤ (Real.sqrt (4 * Real.pi * α * t))^n := by
    exact pow_le_pow_left₀ (by positivity) h_sqrt n
  exact (one_div_le_one_div (by positivity) (by positivity)).mpr h_le

lemma integrable_heatKernelND {n : ℕ} {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    Integrable (fun x : E n => heatKernelND α x t) := by
  unfold heatKernelND
  have h_eq : (fun x : E n => (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * Real.exp (-‖x‖^2 / (4 * α * t))) =
    (1 / (Real.sqrt (4 * Real.pi * α * t))^n) • (fun x : E n => Real.exp (-(1 / (4 * α * t)) * ‖x‖^2)) := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    ring_nf
  rw [h_eq]
  refine Integrable.smul (1 / (Real.sqrt (4 * Real.pi * α * t))^n) ?_
  have h_pos : 0 < 1 / (4 * α * t) := by positivity

  have h_norm_sq : (fun x : E n => Real.exp (-(1 / (4 * α * t)) * ‖x‖^2)) =
    (fun x : E n => Real.exp (-(1 / (4 * α * t)) * ∑ i : Fin n, (x i)^2)) := by
    ext x
    congr 2
    rw [EuclideanSpace.norm_sq_eq x]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [h_norm_sq]

  have h_prod : (fun x : E n => Real.exp (-(1 / (4 * α * t)) * ∑ i : Fin n, (x i)^2)) =
    (fun u : E n => ∏ i : Fin n, Real.exp (-(u i)^2)) ∘ (fun x : E n => Real.sqrt (1 / (4 * α * t)) • x) := by
    ext x
    simp only [Function.comp_apply]
    rw [← Real.exp_sum]
    congr 1
    have h_sqrt : (Real.sqrt (1 / (4 * α * t)))^2 = 1 / (4 * α * t) := Real.sq_sqrt (le_of_lt h_pos)
    calc -(1 / (4 * α * t)) * ∑ i : Fin n, (x i)^2
      _ = ∑ i : Fin n, (-(1 / (4 * α * t)) * (x i)^2) := by rw [Finset.mul_sum]
      _ = ∑ i : Fin n, -((Real.sqrt (1 / (4 * α * t)) * x i)^2) := by
        congr 1
        ext i
        rw [mul_pow, h_sqrt]
        ring
  rw [h_prod]

  have hc : Real.sqrt (1 / (4 * α * t)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h_pos)

  have h_base_int : Integrable (fun u : E n => ∏ i : Fin n, Real.exp (-(u i)^2)) := by
    have h_int := integrable_pi_gaussian n
    change Integrable ((fun v : Fin n → ℝ => ∏ i : Fin n, Real.exp (-(v i)^2)) ∘ fun u : E n => u.ofLp)
    exact ((PiLp.volume_preserving_ofLp (Fin n)).integrable_comp h_int.1).mpr h_int

  exact MeasureTheory.Integrable.comp_smul h_base_int hc

lemma integrable_heatKernelND_slice {n : ℕ} {α t : ℝ}
    (hα : 0 < α) (ht : 0 < t) (x : E n) :
    Integrable (fun y : E n => heatKernelND α (x - y) t) := by
  simp_rw [sub_eq_neg_add]
  exact (integrable_heatKernelND hα ht).comp_add_right x |>.comp_neg

lemma integrable_heatKernelND_mul_of_Linfty
    {n : ℕ} {B α : ℝ} (g : E n → ℝ) {x : E n} {t : ℝ}
    (hα : 0 < α) (ht : 0 < t)
    (hg_meas : AEStronglyMeasurable g)
    (hBound : ∀ y, |g y| ≤ B) :
    Integrable (fun y : E n => heatKernelND α (x - y) t * |g y|) := by
  have h := Integrable.smul_of_top_right (integrable_heatKernelND_slice hα ht x)
    (memLp_top_of_bound hg_meas.norm B (by filter_upwards with y; simpa [Real.norm_eq_abs] using hBound y))
  change Integrable (fun y => |g y| * heatKernelND α (x - y) t) at h
  simpa [mul_comm] using h

lemma integrable_heatKernelND_mul_of_L1
    {n : ℕ} {α : ℝ} (g : E n → ℝ) {x : E n} {t : ℝ}
    (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g) :
    Integrable (fun y : E n => heatKernelND α (x - y) t * g y) := by
  exact Integrable.smul_of_top_right hg (Linfty_heatKernelND hα ht)

lemma aestronglyMeasurable_heatKernelND_mul
    {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) (g : E n → ℝ) (hg : Integrable g volume) :
      AEStronglyMeasurable (fun y : E n => heatKernelND α (x - y) t * g y) volume := by
  exact (integrable_heatKernelND_mul_of_L1 g hα ht hg).aestronglyMeasurable

lemma eventually_aestronglyMeasurable_heatKernelND_mul
    {n : ℕ} {α : ℝ} (g : E n → ℝ) (hg : Integrable g volume) {x : E n} {t : ℝ} (ht : 0 < t) :
    ∀ᶠ τ in 𝓝 t, AEStronglyMeasurable (fun y : E n => heatKernelND α (x - y) τ * g y) volume := by
  filter_upwards [eventually_gt_nhds ht] with τ hτ
  have h_cont : Continuous (fun y : E n => heatKernelND α (x - y) τ) := by continuity
  exact h_cont.aestronglyMeasurable.mul hg.aestronglyMeasurable

lemma aestronglyMeasurable_HKtND_mul
    {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ)
    (hg : Integrable g) (hα : 0 < α) (ht : 0 < t) :
    AEStronglyMeasurable (fun y : E n => HKtND α (x - y) t * g y) volume := by
  exact (meas_HKtND hα ht).mul hg.aestronglyMeasurable

lemma integ_HKtND_mul_of_L1
    {n : ℕ} {α : ℝ} (g : E n → ℝ) {x : E n} {t : ℝ}
    (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g) :
    Integrable (fun y : E n => HKtND α (x - y) t * g y) := by
  exact Integrable.smul_of_top_right hg (HKtND_Linfinity_bound ht hα)

lemma aestronglyMeasurable_HKgradND_mul
    {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ)
    (hg : Integrable g) (hα : 0 < α) (ht : 0 < t) :
    AEStronglyMeasurable (fun y : E n => g y • HKgradND α (x - y) t) volume := by
  exact hg.aestronglyMeasurable.smul (meas_HKgradND hα ht)

lemma integ_HKgradND_mul_of_L1
    {n : ℕ} {α : ℝ} (g : E n → ℝ) {x : E n} {t : ℝ}
    (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g) :
    Integrable (fun y : E n => g y • HKgradND α (x - y) t) := by
  have h_meas := aestronglyMeasurable_HKgradND_mul (x := x) g hg hα ht
  have h_bound : ∀ᵐ y ∂volume, ‖g y • HKgradND α (x - y) t‖ ≤ ‖KgradND n α t * ‖g y‖‖ := by
    filter_upwards with y
    calc ‖g y • HKgradND α (x - y) t‖
      _ = ‖HKgradND α (x - y) t‖ * ‖g y‖ := by rw [norm_smul, mul_comm]
      _ ≤ KgradND n α t * ‖g y‖ := mul_le_mul_of_nonneg_right (pointwise_bound_HKgradND ht hα) (norm_nonneg _)
      _ = ‖KgradND n α t * ‖g y‖‖ := by
        have hp : 0 ≤ KgradND n α t := by unfold KgradND; positivity
        exact (Real.norm_of_nonneg (mul_nonneg hp (norm_nonneg _))).symm
  exact Integrable.mono (hg.norm.const_mul (KgradND n α t)) h_meas h_bound

lemma aestronglyMeasurable_HKlaplacianND_mul
    {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ)
    (hg : Integrable g) (ht : 0 < t) (hα : 0 < α) :
    AEStronglyMeasurable (fun y : E n => HKlaplacianND α (x - y) t * g y) volume := by
  exact (meas_HKlaplacianND hα ht).mul hg.aestronglyMeasurable

lemma integ_HKlaplacianND_mul_of_L1
    {n : ℕ} {α : ℝ} (g : E n → ℝ) {x : E n} {t : ℝ}
    (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g) :
    Integrable (fun y : E n => HKlaplacianND α (x - y) t * g y) := by
  exact Integrable.smul_of_top_right hg (HKlaplacianND_Linfinity_bound ht hα)

lemma diff_HKtND_mul {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ) (ht : 0 < t) (hα : 0 < α) :
    ∀ᵐ y ∂volume, ∀ τ ∈ Metric.ball t (t / 2),
      HasDerivAt (fun τ' => heatKernelND α (x - y) τ' * g y) (HKtND α (x - y) τ * g y) τ := by
  filter_upwards with y
  intro τ hτ
  have τ_pos : 0 < τ := by rw [Metric.mem_ball, Real.dist_eq] at hτ; linarith [abs_sub_lt_iff.mp hτ]
  simp_rw [HKtND_eq_derivative hα τ_pos]
  exact (hasDerivAt_heatKernelND_t α hα τ_pos).mul_const (g y)

lemma diff_HKgradND_mul {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ) (ht : 0 < t) (hα : 0 < α) :
    ∀ᵐ y ∂volume, ∀ x' ∈ Metric.ball x 1,
      HasFDerivAt (fun x'' => heatKernelND α (x'' - y) t * g y) ((g y) • (toDual ℝ (E n)) (HKgradND α (x' - y) t)) x' := by
  filter_upwards with y
  intro x' _
  have h_eq : (fun x'' => heatKernelND α (x'' - y) t * g y) = fun x'' => (g y) • heatKernelND α (x'' - y) t := by
    ext x''
    exact mul_comm _ _
  rw [h_eq]
  have h1 := hasFDerivAt_heatKernelND_x (x := x' - y) ht hα
  have h_inner := (hasFDerivAt_id (𝕜 := ℝ) x').sub (hasFDerivAt_const (𝕜 := ℝ) y x')
  have h_comp_clean : HasFDerivAt (fun x'' => heatKernelND α (x'' - y) t)
    (toDual ℝ (E n) (HKgradND α (x' - y) t)) x' := by
    apply HasFDerivAt.congr_fderiv (h1.comp x' h_inner)
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, sub_zero]
    have h_map : toDual ℝ (E n) (HKgradND α (x' - y) t) =
      (-(1 / (2 * α * t)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • toDual ℝ (E n) (x' - y) := by
      rw [HKgradND_eq_derivative ht hα]
      exact map_smul (toDual ℝ (E n)) _ _
    rw [h_map]
    rfl
  exact h_comp_clean.const_smul (g y)

lemma hasFDerivAt_sub_const {n : ℕ} (x y : E n) :
    HasFDerivAt (fun x'' => x'' - y) (ContinuousLinearMap.id ℝ (E n)) x := by
  refine HasFDerivAt.congr_fderiv ((hasFDerivAt_id (𝕜 := ℝ) x).sub (hasFDerivAt_const (𝕜 := ℝ) y x)) ?_
  ext v
  simp only [ContinuousLinearMap.id_apply, sub_zero]

lemma hasFDerivAt_HKgradND_coeff {n : ℕ} {α t : ℝ} (ξ : E n) (ht : 0 < t) (hα : 0 < α) :
    HasFDerivAt (fun ξ' => -(1 / (2 * α * t)) * Real.exp (-‖ξ'‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n))
      (((1 / (4 * α^2 * t^2)) * Real.exp (-‖ξ‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • innerSL ℝ ξ) ξ := by
  rw [show (fun ξ' : E n => -(1 / (2 * α * t)) * Real.exp (-‖ξ'‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) =
    fun ξ' : E n => (-(1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * Real.exp (-‖ξ'‖^2 / (4 * α * t)) from funext fun _ => by ring]
  refine HasFDerivAt.congr_fderiv ((hasFDerivAt_exp_neg_norm_sq ξ ht hα).const_mul (-(1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n))) ?_
  ext v
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

lemma hasFDerivAt_HKgradND {n : ℕ} {α t : ℝ} {y x' : E n} (ht : 0 < t) (hα : 0 < α) :
    HasFDerivAt (fun x'' => HKgradND α (x'' - y) t)
      ((-(1 / (2 * α * t)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • ContinuousLinearMap.id ℝ (E n) +
       (((1 / (4 * α^2 * t^2)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • innerSL ℝ (x' - y)).smulRight (x' - y)) x' := by
  have h_eq : (fun x'' => HKgradND α (x'' - y) t) = fun x'' => (-(1 / (2 * α * t)) * Real.exp (-‖x'' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • (x'' - y) := by
    ext x''
    rw [HKgradND_eq_derivative ht hα]
  rw [h_eq]
  exact ((hasFDerivAt_HKgradND_coeff (x' - y) ht hα).comp x' (hasFDerivAt_sub_const x' y)).smul (hasFDerivAt_sub_const x' y)

lemma diff_HKlaplacianND_mul {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ) (ht : 0 < t) (hα : 0 < α) :
    ∀ᵐ y ∂volume, ∀ x' ∈ Metric.ball x 1,
      HasFDerivAt (fun x'' => g y • HKgradND α (x'' - y) t)
        (g y • (
          (-(1 / (2 * α * t)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • ContinuousLinearMap.id ℝ (E n)
          +
          (((1 / (4 * α^2 * t^2)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • innerSL ℝ (x' - y)).smulRight (x' - y)
        )) x' := by
  filter_upwards with y
  intro x' _
  exact (hasFDerivAt_HKgradND ht hα).const_smul (g y)

lemma bound_HKtND_mul_loc {n : ℕ} {α t : ℝ} (hα : 0 < α) (ht : 0 < t) (x y : E n) (g : E n → ℝ) :
    ∀ τ ∈ Metric.ball t (t / 2), |HKtND α (x - y) τ * g y| ≤ ((n + 2) / t) * cND n α (t / 2) * |g y| := by
  intro τ hτ
  have hτ_le : t / 2 ≤ τ := by rw [Metric.mem_ball, Real.dist_eq] at hτ; linarith [abs_sub_lt_iff.mp hτ]
  have hτ_pos : 0 < τ := by linarith
  rw [abs_mul]
  apply le_trans (mul_le_mul_of_nonneg_right (pointwise_bound_HKtND hτ_pos hα) (abs_nonneg _))
  gcongr
  · exact (cND_pos hα hτ_pos).le
  · linarith
  · exact mono_CoeffND (by positivity) hα hτ_le

lemma swap_t_heatKernelND {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ) (ht : 0 < t) (hα : 0 < α) (hg : Integrable g) :
    HasDerivAt (fun τ => ∫ y, heatKernelND α (x - y) τ * g y ∂volume) (∫ y, HKtND α (x - y) t * g y ∂volume) t := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t (by positivity : 0 < t / 2)) ?_
    (integrable_heatKernelND_mul_of_L1 g hα ht hg)
    (aestronglyMeasurable_HKtND_mul g hg hα ht)
    (Eventually.of_forall fun y => bound_HKtND_mul_loc hα ht x y g)
    (by simpa using hg.abs.const_mul (((n + 2) / t) * cND n α (t / 2)))
    (diff_HKtND_mul g ht hα)).2
  filter_upwards [Metric.ball_mem_nhds t (by positivity : 0 < t / 2)] with τ hτ
  have hτ_pos : 0 < τ := by rw [Metric.mem_ball, Real.dist_eq] at hτ; linarith [abs_sub_lt_iff.mp hτ]
  exact aestronglyMeasurable_heatKernelND_mul hα hτ_pos g hg

lemma bound_HKgradND_mul_loc {n : ℕ} {α t : ℝ} (ht : 0 < t) (hα : 0 < α) (x y : E n) (g : E n → ℝ) :
    ∀ x' ∈ Metric.ball x 1, ‖(g y) • (toDual ℝ (E n)) (HKgradND α (x' - y) t)‖ ≤ KgradND n α t * ‖g y‖ := by
  intro x' _
  rw [norm_smul, LinearIsometryEquiv.norm_map, mul_comm]
  exact mul_le_mul_of_nonneg_right (pointwise_bound_HKgradND ht hα) (norm_nonneg _)

lemma meas_HKgradND_mul_dual {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ) (hg : Integrable g) (hα : 0 < α) (ht : 0 < t) :
    AEStronglyMeasurable (fun y => (g y) • (toDual ℝ (E n)) (HKgradND α (x - y) t)) volume := by
  have h_eq : (fun y => (g y) • (toDual ℝ (E n)) (HKgradND α (x - y) t)) = fun y => (toDual ℝ (E n)) (g y • HKgradND α (x - y) t) := by
    funext y
    exact (map_smul (toDual ℝ (E n)) (g y) (HKgradND α (x - y) t)).symm
  rw [h_eq]
  exact Continuous.comp_aestronglyMeasurable (ContinuousLinearMap.continuous (toDual ℝ (E n)).toContinuousLinearMap) (aestronglyMeasurable_HKgradND_mul g hg hα ht)

lemma swap_grad_heatKernelND {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ) (ht : 0 < t) (hα : 0 < α) (hg : Integrable g) :
    gradient (fun x' => ∫ y, heatKernelND α (x' - y) t * g y ∂volume) x = ∫ y, g y • HKgradND α (x - y) t ∂volume := by
  have h_deriv_full : HasFDerivAt (fun x' => ∫ y, heatKernelND α (x' - y) t * g y ∂volume)
    (∫ y, (g y) • (toDual ℝ (E n)) (HKgradND α (x - y) t) ∂volume) x :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (Metric.ball_mem_nhds x zero_lt_one)
      (Eventually.of_forall fun _ => aestronglyMeasurable_heatKernelND_mul hα ht g hg)
      (integrable_heatKernelND_mul_of_L1 g hα ht hg)
      (meas_HKgradND_mul_dual g hg hα ht)
      (Eventually.of_forall fun y => bound_HKgradND_mul_loc ht hα x y g)
      (hg.norm.const_mul (KgradND n α t))
      (diff_HKgradND_mul g ht hα)
  unfold gradient
  rw [h_deriv_full.fderiv]
  have h_integrand_eq : (fun y => (g y) • (toDual ℝ (E n)) (HKgradND α (x - y) t)) = fun y => toDual ℝ (E n) (g y • HKgradND α (x - y) t) := by
    funext y
    exact (map_smul (toDual ℝ (E n)) (g y) (HKgradND α (x - y) t)).symm
  erw [h_integrand_eq, ContinuousLinearMap.integral_comp_comm (toDual ℝ (E n)).toContinuousLinearMap (integ_HKgradND_mul_of_L1 g hα ht hg)]
  exact LinearIsometryEquiv.symm_apply_apply (toDual ℝ (E n)) _

noncomputable def HKhessianND {n : ℕ} (α : ℝ) (x : E n) (t : ℝ) : E n →L[ℝ] E n :=
  (-(1 / (2 * α * t)) * Real.exp (-‖x‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • ContinuousLinearMap.id ℝ (E n) +
  (((1 / (4 * α^2 * t^2)) * Real.exp (-‖x‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • innerSL ℝ x).smulRight x

noncomputable def KHessianND (n : ℕ) (α t : ℝ) : ℝ :=
  (1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) +
  (1 / (α * t)) * Real.exp (-1) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)

lemma isBoundedBilinearMap_smulRight {n : ℕ} :
    IsBoundedBilinearMap ℝ (fun p : (E n →L[ℝ] ℝ) × E n => p.1.smulRight p.2) := {
  add_left := fun f₁ f₂ v => by ext1 z; simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply, add_smul]
  smul_left := fun c f v => by ext1 z; simp only [_root_.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_smul]
  add_right := fun f v₁ v₂ => by ext1 z; simp only [ContinuousLinearMap.smulRight_apply, smul_add]; rfl
  smul_right := fun c f v => by
    ext1 z
    simp only [_root_.smul_apply, ContinuousLinearMap.smulRight_apply]
    exact smul_comm (f z) c v
  bound := ⟨1, zero_lt_one, fun f v => by
    simp only [one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun z => ?_)
    rw [ContinuousLinearMap.smulRight_apply, norm_smul, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm f z) (norm_nonneg _)⟩
}

lemma cont_HKhessianND {n : ℕ} {α t : ℝ} {x : E n} :
    Continuous (fun y => HKhessianND α (x - y) t) := by
  unfold HKhessianND
  have h_dist : Continuous (fun y => x - y) := continuous_const.sub continuous_id
  have h_exp : Continuous (fun y => Real.exp (-‖x - y‖^2 / (4 * α * t))) := by continuity
  have h_term2 : Continuous (fun y => (((1 / (4 * α^2 * t^2)) * Real.exp (-‖x - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • innerSL ℝ (x - y)).smulRight (x - y)) :=
    isBoundedBilinearMap_smulRight.continuous.comp ((((continuous_const.mul h_exp).mul continuous_const).smul ((innerSL ℝ).continuous.comp h_dist)).prodMk h_dist)
  exact (((continuous_const.mul h_exp).mul continuous_const).smul continuous_const).add h_term2

lemma meas_HKhessianND_mul {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ) (hg : Integrable g):
    AEStronglyMeasurable (fun y => g y • HKhessianND α (x - y) t) volume :=
  hg.aestronglyMeasurable.smul cont_HKhessianND.aestronglyMeasurable

lemma norm_HKhessianND_term1 {n : ℕ} {α t : ℝ} (v : E n) (ht : 0 < t) (hα : 0 < α) :
    ‖(-(1 / (2 * α * t)) * Real.exp (-‖v‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • ContinuousLinearMap.id ℝ (E n)‖ ≤
    (1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) := by
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity)).trans ?_
  rw [mul_one]
  have := exp_heatND_le_one v α t hα ht
  gcongr
  aesop

lemma bound_HKhessianND_mul {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ) (ht : 0 < t) (hα : 0 < α) :
    ∀ᵐ y ∂volume, ∀ x' ∈ Metric.ball x 1, ‖g y • HKhessianND α (x' - y) t‖ ≤ KHessianND n α t * ‖g y‖ := by
  filter_upwards with y
  intro x' _

  have bound_term1 : ‖(-(1 / (2 * α * t)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • ContinuousLinearMap.id ℝ (E n)‖ ≤ (1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) := by
    calc ‖(-(1 / (2 * α * t)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • ContinuousLinearMap.id ℝ (E n)‖
      _ ≤ |-(1 / (2 * α * t)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)| * 1 := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)
      _ = (1 / (2 * α * t)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) := by
        rw [mul_one, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ (1 / (2 * α * t)) * 1 * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) := by
        gcongr
        exact exp_heatND_le_one (x' - y) α t hα ht
      _ = (1 / (2 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) := by rw [mul_one]

  have bound_term2 : ‖(((1 / (4 * α^2 * t^2)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • innerSL ℝ (x' - y)).smulRight (x' - y)‖ ≤ (1 / (α * t)) * Real.exp (-1) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) := by
    have h_coeff_pos : 0 ≤ (1 / (4 * α^2 * t^2)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) := by positivity
    have h_op : ‖(((1 / (4 * α^2 * t^2)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • innerSL ℝ (x' - y)).smulRight (x' - y)‖ ≤
        ((1 / (4 * α^2 * t^2)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * ‖x' - y‖^2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
      simp only [ContinuousLinearMap.smulRight_apply, _root_.smul_apply, coe_innerSL_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg h_coeff_pos]
      have h_alg : ∀ C V W : ℝ, C * (V * W) * V = C * V^2 * W := fun _ _ _ => by ring
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (x' - y) v) h_coeff_pos) (norm_nonneg _)).trans_eq (h_alg _ _ _)
    calc ‖(((1 / (4 * α^2 * t^2)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) • innerSL ℝ (x' - y)).smulRight (x' - y)‖
      _ ≤ ((1 / (4 * α^2 * t^2)) * Real.exp (-‖x' - y‖^2 / (4 * α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n)) * ‖x' - y‖^2 := h_op
      _ = (1 / (α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * ((‖x' - y‖^2 / (4 * α * t)) * Real.exp (-(‖x' - y‖^2 / (4 * α * t)))) := by
        have h_alg2 : ∀ a t V E S : ℝ, ((1 / (4 * a^2 * t^2)) * E * S) * V^2 = (1 / (a * t)) * S * ((V^2 / (4 * a * t)) * E) := fun _ _ _ _ _ => by ring
        have h_sign : ∀ V a t : ℝ, -V^2 / (4 * a * t) = -(V^2 / (4 * a * t)) := fun _ _ _ => by ring
        rw [h_sign ‖x' - y‖ α t]
        exact h_alg2 α t ‖x' - y‖ (Real.exp (-(‖x' - y‖^2 / (4 * α * t)))) (1 / (Real.sqrt (4 * Real.pi * α * t))^n)
      _ ≤ (1 / (α * t)) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * Real.exp (-1) := by
        gcongr
        exact bound_norm_exp_neg_norm (x := ‖x' - y‖^2 / (4 * α * t))
      _ = (1 / (α * t)) * Real.exp (-1) * (1 / (Real.sqrt (4 * Real.pi * α * t))^n) := by
        have h_alg3 : ∀ A S E : ℝ, A * S * E = A * E * S := fun _ _ _ => by ring
        exact h_alg3 _ _ _

  have bound_D : ‖HKhessianND α (x' - y) t‖ ≤ KHessianND n α t := by
    unfold HKhessianND KHessianND
    exact (norm_add_le _ _).trans (add_le_add bound_term1 bound_term2)

  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right bound_D (norm_nonneg _)

lemma trace_smulRight_innerSL_eq {n : ℕ} (c : ℝ) (x : E n) :
    LinearMap.trace ℝ (E n) ((c • innerSL ℝ x).smulRight x : E n →ₗ[ℝ] E n) = c * ‖x‖^2 := by
  have h_eq : ((c • innerSL ℝ x).smulRight x : E n →ₗ[ℝ] E n) = LinearMap.smulRight (c • (innerSL ℝ x : E n →ₗ[ℝ] ℝ)) x := rfl
  erw [h_eq, LinearMap.trace_smulRight, LinearMap.smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul]

lemma trace_HKhessianND {n : ℕ} {α t : ℝ} (x : E n) (ht : 0 < t) (hα : 0 < α) :
    LinearMap.trace ℝ (E n) (HKhessianND α x t : E n →ₗ[ℝ] E n) = HKlaplacianND α x t := by
  dsimp [HKhessianND]
  rw [map_add, map_smul, LinearMap.trace_id, finrank_euclideanSpace_fin]
  rw [trace_smulRight_innerSL_eq, HKlaplacianND_eq_derivative ht hα]
  simp only [smul_eq_mul]
  ring

lemma integral_trace_comm_HKhessianND {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ) (ht : 0 < t) (hα : 0 < α) (hg : Integrable g) :
    LinearMap.trace ℝ (E n) ((∫ y, g y • HKhessianND α (x - y) t ∂volume : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) =
    ∫ y, HKlaplacianND α (x - y) t * g y ∂volume := by
  let Tr_lin : (E n →L[ℝ] E n) →ₗ[ℝ] ℝ := {
    toFun := fun A => LinearMap.trace ℝ (E n) (A : E n →ₗ[ℝ] E n)
    map_add' := fun A B => by
      have h_add : ((A + B : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) = (A : E n →ₗ[ℝ] E n) + (B : E n →ₗ[ℝ] E n) := rfl
      rw [h_add, map_add]
    map_smul' := fun c A => by
      have h_smul : ((c • A : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) = c • (A : E n →ₗ[ℝ] E n) := rfl
      rw [h_smul, map_smul, RingHom.id_apply]
  }
  let Tr : (E n →L[ℝ] E n) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap Tr_lin
  have h_integ_D : Integrable (fun y => g y • HKhessianND α (x - y) t) volume := by
    have h_pos : 0 ≤ KHessianND n α t := by unfold KHessianND; positivity
    have h_bound : ∀ᵐ y ∂volume, ‖g y • HKhessianND α (x - y) t‖ ≤ ‖KHessianND n α t * ‖g y‖‖ := by
      filter_upwards [bound_HKhessianND_mul g ht hα] with y hy
      calc ‖g y • HKhessianND α (x - y) t‖
        _ ≤ KHessianND n α t * ‖g y‖ := hy x (Metric.mem_ball_self (by norm_num))
        _ = ‖KHessianND n α t * ‖g y‖‖ := (Real.norm_of_nonneg (mul_nonneg h_pos (norm_nonneg _))).symm
    exact Integrable.mono (hg.norm.const_mul (KHessianND n α t)) (meas_HKhessianND_mul g hg) h_bound
  calc LinearMap.trace ℝ (E n) ((∫ y, g y • HKhessianND α (x - y) t ∂volume : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n)
    _ = Tr (∫ y, g y • HKhessianND α (x - y) t ∂volume) := rfl
    _ = ∫ y, Tr (g y • HKhessianND α (x - y) t) ∂volume := (ContinuousLinearMap.integral_comp_comm Tr h_integ_D).symm
    _ = ∫ y, HKlaplacianND α (x - y) t * g y ∂volume := by
      congr 1
      ext y
      calc Tr (g y • HKhessianND α (x - y) t)
        _ = LinearMap.trace ℝ (E n) ((g y • HKhessianND α (x - y) t : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) := rfl
        _ = g y • LinearMap.trace ℝ (E n) (HKhessianND α (x - y) t : E n →ₗ[ℝ] E n) := by
          have h_smul : ((g y • HKhessianND α (x - y) t : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) = g y • (HKhessianND α (x - y) t : E n →ₗ[ℝ] E n) := rfl
          rw [h_smul, map_smul]
        _ = g y * HKlaplacianND α (x - y) t := by rw [trace_HKhessianND _ ht hα]; rfl
        _ = HKlaplacianND α (x - y) t * g y := mul_comm _ _

lemma swap_laplacian_heatKernelND {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ) (ht : 0 < t) (hα : 0 < α) (hg : Integrable g) :
    laplacian (fun x' => ∫ y, heatKernelND α (x' - y) t * g y ∂volume) x = ∫ y, HKlaplacianND α (x - y) t * g y ∂volume := by
  have h_grad_eq : gradient (fun x' => ∫ y, heatKernelND α (x' - y) t * g y ∂volume) =
    fun x' => ∫ y, g y • HKgradND α (x' - y) t ∂volume := by
    funext x'
    exact swap_grad_heatKernelND g ht hα hg
  unfold laplacian div_field
  rw [h_grad_eq]
  have h_deriv_full : HasFDerivAt (fun x' => ∫ y, g y • HKgradND α (x' - y) t ∂volume)
    (∫ y, g y • HKhessianND α (x - y) t ∂volume) x := by
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le
      (Metric.ball_mem_nhds x zero_lt_one)
      (Eventually.of_forall fun _ => aestronglyMeasurable_HKgradND_mul g hg hα ht)
      (integ_HKgradND_mul_of_L1 g hα ht hg)
      (meas_HKhessianND_mul g hg)
      (bound_HKhessianND_mul g ht hα)
      (hg.norm.const_mul (KHessianND n α t))
      (diff_HKlaplacianND_mul g ht hα)
  rw [h_deriv_full.fderiv]
  exact integral_trace_comm_HKhessianND g ht hα hg

theorem heat_from_convolution_heatKernelND {n : ℕ} {α : ℝ} (g : E n → ℝ) (hα : 0 < α) (ht : 0 < t) (hg : Integrable g) :
    ∀ x : E n, deriv (fun τ => heatConvolutionHKND α g x τ) t = α * laplacian (fun x' => heatConvolutionHKND α g x' t) x := by
  intro x
  have h_lap : laplacian (fun x' => heatConvolutionHKND α g x' t) x = ∫ y, HKlaplacianND α (x - y) t * g y ∂volume := by
    have h_expand : (fun x' => heatConvolutionHKND α g x' t) = fun x' => ∫ y, heatKernelND α (x' - y) t * g y ∂volume := by
      ext x'
      rw [heatConvolutionHKND]
    rw [h_expand]
    exact swap_laplacian_heatKernelND g ht hα hg
  calc deriv (fun τ => heatConvolutionHKND α g x τ) t
    _ = deriv (fun τ => ∫ y, heatKernelND α (x - y) τ * g y ∂volume) t := by simp_rw [heatConvolutionHKND]
    _ = ∫ y, HKtND α (x - y) t * g y ∂volume := (swap_t_heatKernelND g ht hα hg (x := x)).deriv
    _ = ∫ y, α * (HKlaplacianND α (x - y) t * g y) ∂volume := by
      have h_eq : ∀ y, HKtND α (x - y) t * g y = α * (HKlaplacianND α (x - y) t * g y) := fun y => by
        have hpde : HKtND α (x - y) t = α * HKlaplacianND α (x - y) t := by
          unfold HKtND HKlaplacianND
          exact heatKernelND_solves_heat_eq α hα ht (x := x - y)
        rw [hpde]
        ring
      simp_rw [h_eq]
    _ = α * ∫ y, HKlaplacianND α (x - y) t * g y ∂volume := MeasureTheory.integral_const_mul α (fun y => HKlaplacianND α (x - y) t * g y)
    _ = α * laplacian (fun x' => heatConvolutionHKND α g x' t) x := by rw [h_lap]

variable {n : ℕ} {g : E n → ℝ} (hg_int : Integrable g volume)

noncomputable def CND (g : E n → ℝ) : ℝ := ∫ y, |g y|

lemma integrable_heatKernelND_bound_helper {n : ℕ} {α t : ℝ} {x : E n} (hα : 0 < α) (ht : 0 < t) (y : E n) :
    ‖heatKernelND α (x - y) t‖ ≤ 1 / (Real.sqrt (4 * Real.pi * α * t))^n := by
  rw [Real.norm_of_nonneg (heatKernelND_bound_pointwise hα ht y).1]
  exact (heatKernelND_bound_pointwise hα ht y).2

lemma integrable_heatKernelND_abs_g {n : ℕ} {α t : ℝ} {x : E n} (g : E n → ℝ) (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g) :
    Integrable (fun y => heatKernelND α (x - y) t * |g y|) :=
  integrable_heatKernelND_mul_of_L1 (fun y => |g y|) hα ht hg.abs

theorem heat_eq_decayND (x : E n) (α : ℝ) (hα : 0 < α) (hg_int : Integrable g) (hn : n ≠ 0) :
    Tendsto (fun t => heatConvolutionHKND α g x t) atTop (𝓝 0) := by
  have h_sqrt : Tendsto (fun t => Real.sqrt (4 * Real.pi * α * t)) atTop atTop := by
    simp_rw [Real.sqrt_eq_rpow]
    exact (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp (Tendsto.const_mul_atTop (by positivity) tendsto_id)
  have h_pow : Tendsto (fun t => (Real.sqrt (4 * Real.pi * α * t))^n) atTop atTop :=
    (tendsto_pow_atTop hn).comp h_sqrt
  have h_lim : Tendsto (fun t => (∫ y, |g y|) / (Real.sqrt (4 * Real.pi * α * t))^n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using Tendsto.const_mul (∫ y, |g y|) (tendsto_inv_atTop_zero.comp h_pow)
  have h_bound : ∀ᶠ t in atTop, |heatConvolutionHKND α g x t| ≤ (∫ y, |g y|) / (Real.sqrt (4 * Real.pi * α * t))^n := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp_rw [heatConvolutionHKND]
    calc |∫ y, heatKernelND α (x - y) t * g y|
      _ ≤ ∫ y, |heatKernelND α (x - y) t * g y| := abs_integral_le_integral_abs
      _ = ∫ y, heatKernelND α (x - y) t * |g y| := by
        congr 1 with y
        rw [abs_mul, abs_of_nonneg (heatKernelND_bound_pointwise hα ht y).1]
      _ ≤ ∫ y, (1 / (Real.sqrt (4 * Real.pi * α * t))^n) * |g y| := by
        refine integral_mono (integrable_heatKernelND_abs_g g hα ht hg_int)
          (Integrable.const_mul hg_int.abs _) fun y => ?_
        exact mul_le_mul_of_nonneg_right (heatKernelND_bound_pointwise hα ht y).2 (abs_nonneg _)
      _ = (∫ y, |g y|) / (Real.sqrt (4 * Real.pi * α * t))^n := by rw [integral_const_mul]; ring
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
    (Eventually.of_forall fun _ => abs_nonneg _) h_bound

end Heat
