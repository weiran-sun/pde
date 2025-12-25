import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Topology.Basic
import PDE.Basics.Heat.HeatKernel

/-!
# The Fundamental Solution and Its Properties

This file formalizes the properties of the heat kernel and its convolution solution
following Rustom Choksi's Partial Differential Equations book (Chapter 7.2.2).

We establish:
1.  Regularity properties (continuity and measurability).
2.  $L^\infty$ bounds and decay estimates essential for dominated convergence.
3.  Integrability of the kernel and its derivatives against a function $g$.
4.  differentiation under the integral sign to prove the convolution solves the heat equation.

## Reference

This formalization follows Chapter 7.2.2, ["Partial Differential Equations, A First Course"](https://bookstore.ams.org/amstext-54/) by Professor [Rustom Choksi](https://scholar.google.com/citations?user=Fk1zaTgAAAAJ&hl=en).

-/

open MeasureTheory Filter
open scoped Topology ENNReal Interval

namespace Heat

/-!
### 1. Definitions and Derivative Shorthands
We define the convolution of the heat kernel with a function $g$ and introduce
shorthand notation for the partial derivatives of the heat kernel.
-/

/-- The convolution of the heat kernel with an initial data function `g`. -/
noncomputable def heatConvolutionHK (α : ℝ) (g : ℝ → ℝ) (x t : ℝ) : ℝ :=
  ∫ y, heatKernel α (x - y) t * g y


/-- Partial derivative of the heat kernel with respect to time $t$. -/
noncomputable def HKt (α : ℝ) (x t : ℝ) : ℝ :=
  deriv (fun τ => heatKernel α x τ) t


/-- Partial derivative of the heat kernel with respect to space $x$. -/
noncomputable def HKx (α : ℝ) (x t : ℝ) : ℝ :=
  deriv (fun ξ => heatKernel α ξ t) x


/-- Second partial derivative of the heat kernel with respect to space $x$. -/
noncomputable def HKxx (α : ℝ) (x t : ℝ) : ℝ :=
  deriv (fun x' => HKx α x' t) x


@[simp] lemma sq_sub_comm (x y : ℝ) : (y - x)^2 = (x - y)^2 := by ring


/-!
### 2. Explicit Derivative Formulas
We use the explicit calculations of the derivatives of the Heat Kernel from the
previous chapter and make them consistent with the notation `HKt`, `HKx`, `HKxx`
-/

lemma HKt_eq_derivative (hα : 0 < α) {t x : ℝ} (ht : 0 < t) :
    HKt α x t = (-(1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * α * t))) * Real.exp (-(x^2) / (4 * α * t))
      + (1 / Real.sqrt (4 * Real.pi * α * t)) * (((1 : ℝ) / (4 * α)) * (1 / (t ^ 2)) * x ^ 2) * Real.exp (-(x^2) / (4 * α * t))
      := (hasDerivAt_heatKernel_t α hα ht).deriv


lemma HKx_eq_derivative {α t x : ℝ} (ht : 0 < t) (hα : 0 < α) :
    HKx α x t = (1 / Real.sqrt (4 * Real.pi * α * t)) * (-(1 / (4 * α * t)) * (2 * x)) * Real.exp (-(x^2) / (4 * α * t))
      := (hasDerivAt_heatKernel_x ht hα).deriv


lemma HKxx_eq_derivative {α t x : ℝ} (ht : 0 < t) (hα : 0 < α) :
  HKxx α x t
    = (1 / Real.sqrt (4 * Real.pi * α * t)) *
      ( (-(1 / (4 * α * t)) * 2) * Real.exp (-(x^2) / (4 * α * t))
      + (-(1 / (4 * α * t)) * (2 * x)) * (-(1 / (4 * α * t)) * (2 * x)) * Real.exp (-(x^2) / (4 * α * t)) )
    := by
    unfold HKxx
    simp_rw [HKx_eq_derivative ht hα]
    exact (hasDerivAt_heatKernel_x_x ht hα).deriv


/-!
### 3. Regularity: Continuity and Measurability
Here we establish that the heat kernel and its derivatives are continuous and
strongly measurable functions. These properties are mainly used here as a prerequisite to
showing that the solution formula indeed solves the heat equation, which requires us to
differentiate under the integral.
-/

section Regularity

lemma cont_HKt {α x t : ℝ} (hα : 0 < α) (ht : 0 < t) :
  Continuous (fun y : ℝ => HKt α (x-y) t) := by
  simp_rw [HKt_eq_derivative hα ht]
  continuity

lemma meas_HKt {α x t : ℝ} (hα : 0 < α) (ht : 0 < t) :
  AEStronglyMeasurable (fun y : ℝ => HKt α (x-y) t) :=
  (cont_HKt hα ht).aestronglyMeasurable

lemma cont_HKx {α x t : ℝ}(hα : 0 < α) (ht : 0 < t):
  Continuous (fun y : ℝ => HKx α (x - y) t) := by
  simp_rw [HKx_eq_derivative ht hα]
  continuity

lemma meas_HKx {α x t : ℝ}(hα : 0 < α) (ht : 0 < t):
  AEStronglyMeasurable (fun y : ℝ => HKx α (x - y) t) :=
  (cont_HKx hα ht).aestronglyMeasurable

lemma cont_HKxx {α x t : ℝ}(hα : 0 < α) (ht : 0 < t) :
    Continuous (fun y : ℝ => HKxx α (x - y) t) := by
  simp_rw [HKxx_eq_derivative ht hα]
  continuity

lemma meas_HKxx {α x t : ℝ}(hα : 0 < α) (ht : 0 < t) :
    AEStronglyMeasurable (fun y : ℝ => HKxx α (x - y) t) :=
  (cont_HKxx (α := α) (t:= t) (x := x) hα ht).aestronglyMeasurable

lemma cont_heatKernel {α x t : ℝ} :
  Continuous (fun y : ℝ => heatKernel α (x-y) t) := by
  unfold heatKernel
  continuity

lemma meas_heatKernel {α x t : ℝ} :
  AEStronglyMeasurable (fun y : ℝ => heatKernel α (x-y) t) :=
  (cont_heatKernel).aestronglyMeasurable

end Regularity


/-!
### 4. Pointwise Bounds and L-infinity Estimates
We define bounding constants `K`, `Kx`, `Kxx` and for the heat kernel's derivatives.
This implies they belong to $L^\infty$.
-/

noncomputable section Bounds


noncomputable def Kx (α t : ℝ) : ℝ :=
  1 / (2 * Real.sqrt Real.pi * α * t)


noncomputable def Kxx (α t : ℝ) : ℝ :=
  (1 + 2 * Real.exp (-1)) / (2 * α * t * Real.sqrt (4 * Real.pi * α * t))


lemma heatKernel_bound_pointwise {α x t : ℝ}
    (hα : 0 < α) (ht : 0 < t) :
    ∀ y, heatKernel α (x - y) t ≥ 0 ∧
      heatKernel α (x - y) t ≤ 1 / Real.sqrt (4 * Real.pi * α * t):= by
    intro y
    unfold heatKernel
    have K_nonneg : 0 ≤ 1 / Real.sqrt (4 * Real.pi * α * t) :=
     one_div_nonneg.mpr (Real.sqrt_nonneg _)
    constructor
    -- heatKernel α (x - y) t ≥ 0 --
    · exact mul_nonneg K_nonneg
        (by simpa using Real.exp_nonneg (-(x - y)^2 / (4 * α * t)))
    -- heatKernel α (x - y) t ≤ 1 / Real.sqrt (4 * Real.pi * α * t)   --
    · have hexp_le_one : Real.exp ( - ((x - y)^2) / (4 * α * t) ) ≤ 1 := by
       refine Real.exp_le_one_iff.mpr ?_
       have : 0 ≤ 4 * α * t := by positivity
       simpa [neg_div] using (neg_nonpos.mpr (div_nonneg (sq_nonneg (x - y)) (this)))
      simpa [one_mul] using mul_le_mul_of_nonneg_left hexp_le_one K_nonneg


lemma Linfty_heatKernel{α x t : ℝ} (hα : 0 < α) (ht : 0 < t) :
  MemLp (fun y : ℝ => heatKernel α (x-y) t) ∞ volume := by
  refine memLp_top_of_bound (meas_heatKernel)
             (1 / Real.sqrt (4 * Real.pi * α * t)) ?_
  filter_upwards with y
  have : ‖heatKernel α (x-y) t‖ ≤ 1 / √(4 * Real.pi * α * t) := by
    rw [Real.norm_of_nonneg (heatKernel_pos α t hα ht).le]
    have := heatKernel_bound_pointwise (α := α) (x := x) (t := t) hα ht y
    simpa [this]
  exact this

-- Technical lemmas for bounds


lemma bound_x_exp_neg_x {x : ℝ} :
  x * Real.exp (-x) ≤ Real.exp (-1) := by
  have hx : x ≤ Real.exp (x - 1) := by
    simpa using (Real.add_one_le_exp (x - 1))
  simpa [← Real.exp_add, sub_eq_add_neg] using
    (mul_le_mul_of_nonneg_right hx (le_of_lt (Real.exp_pos (-x))))


lemma sq_mul_exp_neg_mul_sq_le (hb : 0 < b) (x : ℝ) :
    x^2 * Real.exp (-(b * x^2)) ≤ Real.exp (-1) / b := by
  have h := bound_x_exp_neg_x (x := b * x^2)
  calc
    x^2 * Real.exp (-(b * x^2)) = (1/b) * (b * x^2 * Real.exp (-(b * x^2))) := by
      field_simp [ne_of_gt hb]
      ring
    _ ≤ (1/b) * Real.exp (-1) := by
      gcongr
    _ = Real.exp (-1) / b := by ring


lemma pointwise_bound_HKt {α : ℝ} {x t : ℝ} (ht : 0 < t) (hα : 0 < α) :
  |HKt α x t| ≤ (3/(2*t)) * (c α t) := by
   simp_rw [HKt_eq_derivative (α:=α) (x:=x) (t:=t) hα ht]
   have pos_coeff: 0 ≤ c α t * (1/t) :=  by unfold c; positivity
   have bound_1 : |-(1 / (2 * t)) * c α t * Real.exp (-a α t * x ^ 2)| ≤ (1 / (2 * t)) * (c α t)
      := by
      simp_rw [abs_mul, abs_neg, mul_assoc]
      rw [abs_of_pos (by positivity), abs_of_pos (c_pos hα ht), abs_of_nonneg (Real.exp_nonneg _)]
      have hexp: Real.exp (-a α t * x ^ 2) ≤ 1 :=
         Real.exp_le_one_iff.mpr (by nlinarith [a_pos hα ht, sq_nonneg x])
      gcongr
      linarith [mul_le_mul_of_nonneg_left hexp (c_pos hα ht).le]
   have bound_2:
     |c α t * (1 / (4 * α) * (1 / t ^ 2) * x ^ 2) * Real.exp (-a α t * x ^ 2)|
       ≤ c α t * (1/t)  := by
       simp_rw [abs_mul, mul_assoc]
       rw [abs_of_pos (c_pos hα ht), abs_of_pos (by positivity), abs_of_nonneg (Real.exp_nonneg _)]
       rw [abs_of_pos (by positivity), abs_of_nonneg (by positivity)]
       calc
         c α t * (1 / (4 * α) * (1 / t ^ 2 * (x ^ 2 * Real.exp (-a α t * x ^ 2))))
          = c α t * (1/t) * ((1/(4 * α * t) * x^2) * Real.exp (-a α t * x ^ 2)) := by ring
         _ ≤ c α t * (1/t) * Real.exp (-1) := by
            unfold a
            gcongr
            rw [show (-(1 / (4 * α * t))) * x ^ 2 = -(1 / (4 * α * t) * x ^ 2) by ring]
            exact bound_x_exp_neg_x
         _ ≤ c α t * (1/t) := by
            have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
            nlinarith [mul_le_mul_of_nonneg_left this pos_coeff]
   simp only [c, a, heatK] at bound_1 bound_2
   unfold c heatK
   -- Convert the exponential notation in the goal to match the bounds
   have h1 : -(1 / (4 * α * t)) * x ^ 2 = -x ^ 2 / (4 * α * t) := by field_simp
   rw [← h1]
   calc _ ≤ _ := abs_add _ _
        _ ≤ _ := add_le_add bound_1 bound_2
        _ = 3 / (2 * t) * (1 / √(4 * Real.pi * α * t)) := by ring


lemma HKt_Linfinity_bound {α : ℝ} {x t : ℝ} (ht : 0 < t) (hα : 0 < α) :
    MemLp (fun y => HKt α (x - y) t) ∞ volume := by
  refine memLp_top_of_bound (meas_HKt hα ht) ((3/(2*t)) * (c α t)) ?_
  filter_upwards with y
  exact pointwise_bound_HKt ht hα


lemma pointwise_bound_HKx
  {α x t : ℝ} (ht : 0 < t) (hα : 0 < α) :
  |HKx α x t| ≤ Kx α t := by
  have hHKx :
       HKx α x t = (c α t) * (-2 * (a α t) * x) * Real.exp (-(a α t) * x^2) := by
    rw[HKx_eq_derivative ht hα]; unfold c a heatK; field_simp
  have hbase : |x * Real.exp (-(a α t) * x^2)| ≤ (Real.sqrt (a α t))⁻¹ := by
      simpa [Real.mulExpNegMulSq, mul_comm, mul_left_comm, mul_assoc, pow_two]
        using (Real.abs_mulExpNegMulSq_le (hε := a_pos hα ht) (x := x))
  have hc_nonneg : 0 < c α t := c_pos hα ht
  have ha_nonneg : 0 < 2 * a α t := mul_pos (by norm_num) (a_pos hα ht)
  calc
    |HKx α x t| = |(c α t) * (-2 * (a α t) * x) * Real.exp (-(a α t) * x^2)| := by congr
    _ = |c α t| * |2 * a α t| * |x * Real.exp (-(a α t) * x^2)| := by simp [abs_mul, abs_neg, mul_assoc]
    _ ≤ |c α t| * |2 * a α t| * (Real.sqrt (a α t))⁻¹ := by exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (c α t) * (2 * a α t) * (Real.sqrt (a α t))⁻¹:= by
          congr
          · simp
          · exact abs_of_pos ha_nonneg
    _ = (c α t) * (2 * (a α t / Real.sqrt (a α t))) := by ring
    _ = (c α t) * (2 * Real.sqrt (a α t)) := by rw [Real.div_sqrt]
    _ = Kx α t := by
      unfold a;unfold c;unfold Kx;unfold heatK;field_simp;ring_nf
      congr
      · exact (Real.sq_sqrt hα.le).symm
      · exact (Real.sq_sqrt ht.le).symm


lemma HKx_Linfinity_bound {α : ℝ} {x t : ℝ} (ht : 0 < t) (hα : 0 < α) :
    MemLp (fun y => HKx α (x - y) t) ∞ volume := by
  refine memLp_top_of_bound (meas_HKx hα ht) (Kx α t) ?_
  filter_upwards with y
  exact pointwise_bound_HKx ht hα


lemma HKxx_uniform_bound {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    ∀ x, |HKxx α x t| ≤ Kxx α t := by
  intro x
  rw [HKxx_eq_derivative]

  have ha_pos : 0 < a α t := by exact a_pos hα ht
  have hc_pos : 0 < c α t := by exact c_pos hα ht

  -- State expr_eq with unfolded definitions
  have expr_eq : (1 / √(4 * Real.pi * α * t)) *
      ((-(1 / (4 * α * t)) * 2) * Real.exp (-(1 / (4 * α * t)) * x ^ 2) +
      (-(1 / (4 * α * t)) * (2 * x)) * (-(1 / (4 * α * t)) * (2 * x)) * Real.exp (-(1 / (4 * α * t)) * x ^ 2)) =
      (1 / √(4 * Real.pi * α * t)) * (-2 * (1 / (4 * α * t)) + 4 * (1 / (4 * α * t))^2 * x^2) * Real.exp (-(1 / (4 * α * t)) * x^2) := by
    ring_nf

  have exp_conv : -(1 / (4 * α * t)) * x ^ 2 = -x ^ 2 / (4 * α * t) := by field_simp
  rw [exp_conv, ← exp_conv, exp_conv] at expr_eq
  rw [expr_eq]
  rw[← a]

  have hexp_le_one : Real.exp (-(a α t) * x^2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [a_pos hα ht, sq_nonneg x])

  have core_bound : |-2 * (a α t) + 4 * (a α t)^2 * x^2| * Real.exp (-(a α t) * x^2) ≤
                    2 * (a α t) + 4 * (a α t) * Real.exp (-1) := by
    calc
      |-2 * (a α t) + 4 * (a α t)^2 * x^2| * Real.exp (-(a α t) * x^2)
          ≤ (|-2 * (a α t)| + |4 * (a α t)^2 * x^2|) * Real.exp (-(a α t) * x^2) := by
        exact mul_le_mul_of_nonneg_right (abs_add _ _) (Real.exp_pos _).le
      _ = (2 * (a α t) + 4 * (a α t)^2 * x^2) * Real.exp (-(a α t) * x^2) := by
        congr
        · rw [abs_of_neg (show -2 * (a α t) < 0 from by linarith), neg_mul, neg_neg]
        · rw [abs_of_nonneg (by nlinarith [sq_nonneg (x : ℝ)] : 0 ≤ 4 * (a α t)^2 * x^2)]
      _ = 2 * (a α t) * Real.exp (-(a α t) * x^2) + 4 * (a α t)^2 * x^2 * Real.exp (-(a α t) * x^2) := by ring
      _ ≤ 2 * (a α t) + 4 * (a α t) * Real.exp (-1) := by
        have h1 : 2 * (a α t) * Real.exp (-(a α t) * x^2) ≤ 2 * (a α t) := by
          simpa using mul_le_mul_of_nonneg_left hexp_le_one (by positivity)
        have h2 : 4 * (a α t)^2 * x^2 * Real.exp (-(a α t) * x^2) ≤ 4 * (a α t) * Real.exp (-1)  := by
          rw [show 4 * (a α t)^2 * x^2 * Real.exp (-(a α t) * x^2) =
                  4 * a α t * ((a α t * x^2) * Real.exp (-((a α t) * x^2))) by ring]
          exact mul_le_mul_of_nonneg_left (bound_x_exp_neg_x (x := a α t * x^2)) (by positivity)
        linarith

  let A : ℝ := (-2 : ℝ) * (a α t) + 4 * (a α t)^2 * x^2

  -- Convert exponential notation in the goal to match our calc
  have exp_conv' : -x ^ 2 / (4 * α * t) = -(a α t) * x ^ 2 := by
    unfold a; field_simp
  rw [exp_conv']
  -- Fold c into the goal
  show |c α t * A * Real.exp (-(a α t) * x^2)| ≤ Kxx α t

  calc
    |c α t * A * Real.exp (-(a α t) * x^2)|
        = |c α t| * |A * Real.exp (-(a α t) * x^2)| := by
            simp_rw [abs_mul]
            ring
    _ = |c α t| * (|A| * |Real.exp (-(a α t) * x^2)|) := by
            rw [abs_mul]
    _ = |c α t| * (|A| * Real.exp (-(a α t) * x^2)) := by
            rw [abs_of_nonneg (Real.exp_pos _).le]
    _ ≤ |c α t| * (2 * (a α t) + 4 * (a α t) * Real.exp (-1)) := by
            refine mul_le_mul_of_nonneg_left core_bound (abs_nonneg _)
    _ = c α t * (2 * (a α t) + 4 * (a α t) * Real.exp (-1)) := by
            rw [abs_of_nonneg (le_of_lt hc_pos)]
    _ = c α t * (2 * (a α t)) * (1 + 2 * Real.exp (-1)) := by
            ring
    _ = Kxx α t := by
            unfold Kxx c a heatK
            field_simp
            ring_nf
  exact ht
  exact hα


lemma pointwise_bound_HKxx {α x t : ℝ} (ht : 0 < t) (hα : 0 < α) :
    |HKxx α x t| ≤ Kxx α t := by
  exact HKxx_uniform_bound hα ht x


lemma HKxx_Linfinity_bound {α : ℝ} {x t : ℝ} (ht : 0 < t) (hα : 0 < α) :
    MemLp (fun y => HKxx α (x - y) t) ∞ volume := by
  have bound := Kxx α t
  refine memLp_top_of_bound (meas_HKxx hα ht) (Kxx α t) ?_
  filter_upwards with y
  exact pointwise_bound_HKxx ht hα


-- Lemma stating that c α t is monotonically decreasing in t
lemma mono_Coeff {α : ℝ} {t τ : ℝ} (ht : 0 < t)
  (hτ : 0 < τ) (hα : 0 < α) (hsize: τ ≤ t) : c α t ≤ c α τ
  := by
  unfold c
  have h1 : Real.sqrt (heatK α * t) > 0 := Real.sqrt_pos.mpr (mul_pos (heatK_pos hα) ht)
  have h2 : Real.sqrt (heatK α * τ) > 0 := Real.sqrt_pos.mpr (mul_pos (heatK_pos hα) hτ)
  refine (one_div_le_one_div h1 h2).mpr ?_
  exact Real.sqrt_le_sqrt (by nlinarith [heatK_pos hα])

end Bounds


/-!
### 5. Integrability of the Kernels
We demonstrate that the heat kernel and its derivatives are integrable when
multiplied by an integrable function $g$
-/

section Integrability

lemma integrable_heatKernel (hα : 0 < α) (ht : 0 < t) :
    Integrable (fun x : ℝ => heatKernel α x t) := by
  by_contra h
  have h0 := integral_undef h
  simpa [h0] using integral_heatKernel_one_gaussian α t hα ht


lemma integrable_heatKernel_slice
    (hα : 0 < α) (ht : 0 < t) (x : ℝ) :
    Integrable (fun y : ℝ => heatKernel α (x - y) t) := by
   have : (fun y : ℝ => heatKernel α (x - y) t)
      = (fun y : ℝ => heatKernel α y t) ∘ (fun y => -y + x) := by
    ext y
    simp [sub_eq_neg_add]
   rw [this]
   exact (integrable_heatKernel hα ht).comp_add_right x |>.comp_neg


lemma integrable_heatKernel_mul_of_Linfty
    {B α : ℝ} (g : ℝ → ℝ) {x t : ℝ}
    (hα : 0 < α) (ht : 0 < t)
    (hg_meas : AEStronglyMeasurable g)
    (hBound : ∀ y, |g y| ≤ B) :
    Integrable (fun y : ℝ => heatKernel α (x - y) t * |g y|) := by

    have hg_abs_meas : AEStronglyMeasurable |g|
      := AEStronglyMeasurable.norm hg_meas

    have Linfty_g :
     MemLp (fun y : ℝ => |g y|) ∞ volume := by
     refine memLp_top_of_bound hg_abs_meas B ?_
     filter_upwards with y
     rw [Real.norm_eq_abs, abs_abs]
     exact hBound y

    simpa [mul_comm]
      using Integrable.smul_of_top_right
         (integrable_heatKernel_slice hα ht x) (Linfty_g)


lemma integrable_heatKernel_mul_of_L1
    {α : ℝ} (g : ℝ → ℝ) {x t : ℝ}
    (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g) :
    Integrable (fun y : ℝ => heatKernel α (x - y) t * g y) := by
   simpa using Integrable.smul_of_top_right hg (Linfty_heatKernel hα ht)


lemma aestronglyMeasurable_heatKernel_mul
    {α x t : ℝ} (hα : 0 < α) (ht : 0 < t) (g : ℝ → ℝ) (hg : Integrable g volume) :
      AEStronglyMeasurable (fun y : ℝ => heatKernel α (x - y) t * g y) volume:= by
        exact (integrable_heatKernel_mul_of_L1 g hα ht hg).aestronglyMeasurable


lemma eventually_aestronglyMeasurable_heatKernel_mul
    {α : ℝ} (g : ℝ → ℝ) (hg : Integrable g volume) {x t : ℝ} (ht : 0 < t) :
    ∀ᶠ τ in 𝓝 t, AEStronglyMeasurable (fun y => heatKernel α (x - y) τ * g y) volume := by
  filter_upwards [eventually_gt_nhds ht] with τ hτ
  have : Continuous (fun y => heatKernel α (x - y) τ) := by continuity
  exact (this.aestronglyMeasurable).mul hg.aestronglyMeasurable


lemma aestronglyMeasurable_HKt_mul
    {α x t : ℝ} (g : ℝ → ℝ)
    (hg : Integrable g) (hα : 0 < α) (ht : 0 < t) :
    AEStronglyMeasurable (fun y : ℝ => HKt α (x - y) t * g y) volume := by
    exact (meas_HKt hα ht).mul hg.aestronglyMeasurable


lemma integ_HKt_mul_of_L1
    {α : ℝ} (g : ℝ → ℝ) {x t : ℝ}
    (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g) :
    Integrable (fun y : ℝ => HKt α (x - y) t * g y) := by
   simpa using Integrable.smul_of_top_right hg (HKt_Linfinity_bound ht hα)


lemma aestronglyMeasurable_HKx_mul
    {α x t : ℝ} (g : ℝ → ℝ)
    (hg : Integrable g)(hα : 0 < α) (ht : 0 < t):
    AEStronglyMeasurable (fun y : ℝ => HKx α (x - y) t * g y) volume := by
    exact (meas_HKx hα ht).mul hg.aestronglyMeasurable


lemma integ_HKx_mul_of_L1
    {α : ℝ} (g : ℝ → ℝ) {x t : ℝ}
    (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g) :
    Integrable (fun y : ℝ => HKx α (x - y) t * g y) := by
   simpa using Integrable.smul_of_top_right hg (HKx_Linfinity_bound ht hα)


lemma aestronglyMeasurable_HKxx_mul
    {α x t : ℝ} (g : ℝ → ℝ)
    (hg : Integrable g)(ht : 0 < t) (hα : 0 < α):
    AEStronglyMeasurable (fun y : ℝ => HKxx α (x - y) t * g y) volume := by
  exact (meas_HKxx hα ht).mul hg.aestronglyMeasurable


lemma integ_HKxx_mul_of_L1
    {α : ℝ} (g : ℝ → ℝ) {x t : ℝ}
    (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g) :
    Integrable (fun y : ℝ => HKxx α (x - y) t * g y) := by
   simpa using Integrable.smul_of_top_right hg (HKxx_Linfinity_bound ht hα)

end Integrability


/-!
### 6. Differentiation under the Integral Sign
We establish the validity of swapping the integral and derivative operators.
This requires checking the Dominated Convergence Theorem conditions using the
bounds established in Section 4.
-/

section SwapDerivatives

lemma diff_HKt_mul {α : ℝ} {x t : ℝ} (g : ℝ → ℝ) (ht : 0 < t) (hα : 0 < α):
  ∀ᵐ y ∂volume, ∀ τ ∈ Metric.ball t (t/2),
    HasDerivAt (fun τ' => heatKernel α (x - y) τ' * g y) (HKt α (x - y) τ * g y) τ
  := by
  filter_upwards with y
  intro τ hτ
  have τ_pos: τ > 0 := by
    rw [Metric.mem_ball, Real.dist_eq] at hτ
    have := abs_sub_lt_iff.mp hτ
    linarith
  have h_deriv : HasDerivAt (fun τ' => heatKernel α (x - y) τ') (HKt α (x - y) τ) τ := by
    rw [HKt_eq_derivative hα τ_pos (x := x - y)]
    exact hasDerivAt_heatKernel_t α hα τ_pos
  exact (h_deriv.mul_const (g y))

lemma diff_HKx_mul {α : ℝ} {x t : ℝ} (g : ℝ → ℝ) (ht : 0 < t) (hα : 0 < α):
    ∀ᵐ y ∂volume, ∀ x' ∈ Metric.ball x 1,
      HasDerivAt (fun x'' => heatKernel α (x'' - y) t * g y) (HKx α (x' - y) t * g y) x' := by
  refine Eventually.of_forall ?_
  intro y x' hx'
  have hΦx : HasDerivAt (fun r => heatKernel α r t) (HKx α (x' - y) t) (x' - y) := by
    rw [HKx_eq_derivative]
    exact hasDerivAt_heatKernel_x (x := x' - y) ht hα
    exact ht; exact hα

  -- inner map r(x'') = x'' - y
  have hlin : HasDerivAt (fun x'' : ℝ => x'' - y) (1 - 0) x' := by
    exact HasDerivAt.sub (hasDerivAt_id x') (hasDerivAt_const x' y)

  have hcomp : HasDerivAt ((fun r => heatKernel α r t) ∘ (fun x'' => x'' - y)) (HKx α (x' - y) t * (1-0)) x' :=
    HasDerivAt.comp x' hΦx hlin

  have h_simplify : ((fun r => heatKernel α r t) ∘ (fun x'' => x'' - y)) = (fun x'' => heatKernel α (x'' - y) t) := by
    ext x''; rfl
  rw [h_simplify] at hcomp
  simpa using hcomp.mul_const (g y)


lemma diff_HKxx_mul {α : ℝ} {x t : ℝ} (g : ℝ → ℝ)(ht : 0 < t) (hα : 0 < α):
    ∀ᵐ y ∂volume, ∀ x' ∈ Metric.ball x 1,
      HasDerivAt (fun x'' => HKx α (x'' - y) t * g y) (HKxx α (x' - y) t * g y) x' := by
  refine Eventually.of_forall ?_
  intro y x' hx'

  have hHKxx : HasDerivAt (fun r => HKx α r t) (HKxx α (x' - y) t) (x' - y) := by
    rw [HKxx_eq_derivative]
    exact hasDerivAt_heatKernel_xx ht hα (α := α) (t := t) (x := x' - y)
    exact ht; exact hα

  have hlin : HasDerivAt (fun x'' : ℝ => x'' - y) (1 - 0) x' := by
    exact HasDerivAt.sub (hasDerivAt_id x') (hasDerivAt_const x' y)

  have hcomp : HasDerivAt ((fun r => HKx α r t) ∘ (fun x'' => x'' - y)) (HKxx α (x' - y) t * (1-0)) x' :=
    HasDerivAt.comp x' hHKxx hlin

  have h_simplify : ((fun r => HKx α r t) ∘ (fun x'' => x'' - y)) = (fun x'' => HKx α (x'' - y) t) := by
    ext x''; rfl
  rw [h_simplify] at hcomp
  simpa using hcomp.mul_const (g y)


/-- Swap the time derivative $\partial_t$ with the integral $\int$. -/
lemma swap_t_heatKernel
  {α : ℝ} {x t : ℝ} (g : ℝ → ℝ) (ht : 0 < t) (hα : 0 < α)
  (hg : Integrable g) :
    HasDerivAt
      (fun τ => ∫ y, heatKernel α (x - y) τ * g y ∂volume)
      (∫ y, HKt α (x - y) t * g y ∂volume) t := by
    have t_pos: t/2 > 0 := by positivity
    have τ_pos: ∀ τ ∈ Metric.ball t (t/2), τ > 0 := by
      intro τ hτ
      rw [Metric.mem_ball, Real.dist_eq] at hτ
      have := abs_sub_lt_iff.mp hτ
      linarith
    have mem_nhds : Metric.ball t (t/2) ∈ 𝓝 t := Metric.ball_mem_nhds t (by linarith)

    have meas_HK_mul : ∀ᶠ τ in 𝓝 t,
       AEStronglyMeasurable (fun y : ℝ => heatKernel α (x - y) τ * g y) volume
       := by
       filter_upwards [mem_nhds] with τ hτ
       exact aestronglyMeasurable_heatKernel_mul hα (τ_pos τ hτ) g hg

    have integ_HK_mul: Integrable (fun y : ℝ => heatKernel α (x - y) t * g y)
      := integrable_heatKernel_mul_of_L1 g hα ht hg

    have integ_HKt_mul: Integrable (fun y : ℝ => HKt α (x - y) t * g y)
      := integ_HKt_mul_of_L1 g hα ht hg

    have meas_HKt_mul:
      AEStronglyMeasurable (fun y : ℝ => HKt α (x - y) t * g y) volume
      := aestronglyMeasurable_HKt_mul g hg hα ht

    have diff_HK_mul' : ∀ᵐ y ∂volume, ∀ τ ∈ Metric.ball t (t/2),
      HasDerivAt (fun τ' => heatKernel α (x - y) τ' * g y) (HKt α (x - y) τ * g y) τ
        := by
        filter_upwards [@diff_HKt_mul α x t g ht hα] with y hy
        intro τ hτ
        have h := hy τ hτ
        exact h

    have dominate_fun: ∀ᵐ y ∂volume, ∀ τ ∈ Metric.ball t (t/2),
      |HKt α (x - y) τ * g y| ≤ (3/t) * (c α (t/2)) * |g y|
        := by
        filter_upwards with y
        intro τ hτ
        unfold c
        have τ_lower : τ > t/2 := by
            rw [Metric.mem_ball, Real.dist_eq] at hτ
            have := abs_sub_lt_iff.mp hτ
            linarith
        calc
          |HKt α (x - y) τ * g y| ≤ |HKt α (x - y) τ| * |g y| := by rw [abs_mul]
          _ ≤ (3/(2*τ)) * (c α τ) * |g y| := by
            gcongr
            exact pointwise_bound_HKt (by linarith) hα
          _ ≤ (3/t) * (c α (t/2)) * |g y| := by
            gcongr
            · exact (c_pos hα (by linarith)).le
            · linarith [τ_lower]
            · exact mono_Coeff (by linarith) (by linarith) hα (by linarith)

    have Integ_dominate_fun: Integrable (fun y : ℝ => (3/t) * (c α (t/2)) * |g y|)
      := by
      simpa using (hg.abs).const_mul ((3 / t) * (c α (t/2)))

    have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (by linarith) meas_HK_mul integ_HK_mul meas_HKt_mul dominate_fun Integ_dominate_fun diff_HK_mul'

    exact result.2


/-- Swap the spatial derivative $\partial_x$ with the integral $\int$. -/
lemma swap_x_heatKernel
  {α : ℝ} {x t : ℝ} (g : ℝ → ℝ) (ht : 0 < t) (hα : 0 < α)
  (hg : Integrable g) :
    HasDerivAt
      (fun x' => ∫ y, heatKernel α (x' - y) t * g y ∂volume)
      (∫ y, HKx α (x - y) t * g y ∂volume) x := by
    have t_pos: t/2 > 0 := by positivity

    have mem_nhds : Metric.ball x 1 ∈ 𝓝 x := Metric.ball_mem_nhds x (by norm_num)

    have meas_HK_mul : ∀ᶠ x' in 𝓝 x,
      AEStronglyMeasurable (fun y : ℝ => heatKernel α (x' - y) t * g y) volume := by
        filter_upwards [mem_nhds] with τ hτ
        exact aestronglyMeasurable_heatKernel_mul hα ht g hg

    have integ_HK_mul :
      Integrable (fun y : ℝ => heatKernel α (x - y) t * g y) :=
      integrable_heatKernel_mul_of_L1 g hα ht hg

    have integ_HKx_mul :
      Integrable (fun y : ℝ => HKx α (x - y) t * g y) := by
      simpa using integ_HKx_mul_of_L1 g hα ht hg

    have meas_HKx_mul:
      AEStronglyMeasurable (fun y : ℝ => HKx α (x - y) t * g y) volume
      := aestronglyMeasurable_HKx_mul g hg hα ht

    have diff_HK_mul' : ∀ᵐ y ∂volume, ∀ x' ∈ Metric.ball x 1,
        HasDerivAt (fun x'' => heatKernel α (x'' - y) t * g y) (HKx α (x' - y) t * g y) x' := by
      filter_upwards [diff_HKx_mul (α := α) (t := t) (x := x) g ht hα] with y hy
      intro x' hx'
      have h := hy x' hx'
      exact h

    have dominate_fun :
        ∀ᵐ y ∂volume, ∀ x' ∈ Metric.ball x 1,
          |HKx α (x' - y) t * g y| ≤ 1 / (2 * Real.sqrt Real.pi * α * t) * |g y| := by
      filter_upwards with y
      intro x' hx'
      calc
        |HKx α (x' - y) t * g y| ≤ |HKx α (x' - y) t| * |g y| := by rw [abs_mul]
        _ ≤ Kx α t * |g y| := by
          gcongr
          exact pointwise_bound_HKx ht hα
        _ = 1 / (2 * Real.sqrt Real.pi * α * t) * |g y| := by
          dsimp [Kx]

    have Integ_dominate_fun :
        Integrable (fun y : ℝ => (1 / (2 * Real.sqrt Real.pi * α * t)) * |g y|) :=
      (hg.abs.const_mul (1 / (2 * Real.sqrt Real.pi * α * t)))

    have result :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (by norm_num)
        meas_HK_mul
        integ_HK_mul
        meas_HKx_mul
        dominate_fun
        Integ_dominate_fun
        diff_HK_mul'

    exact result.2


/-- Swap the second spatial derivative $\partial_{xx}$ with the integral $\int$. -/
lemma swap_xx_heatKernel
  {α : ℝ} {x t : ℝ} (g : ℝ → ℝ) (ht : 0 < t) (hα : 0 < α)
  (hg : Integrable g) :
    HasDerivAt
      (fun x' => ∫ y, HKx α (x' - y) t * g y ∂volume)
      (∫ y, HKxx α (x - y) t * g y ∂volume) x := by
    have mem_nhds : Metric.ball x 1 ∈ 𝓝 x := Metric.ball_mem_nhds x (by norm_num)

    have meas_HKx_mul : ∀ᶠ x' in 𝓝 x,
      AEStronglyMeasurable (fun y : ℝ => HKx α (x' - y) t * g y) volume := by
        filter_upwards [mem_nhds] with τ hτ
        exact aestronglyMeasurable_HKx_mul g hg hα ht

    have integ_HKx_mul :
      Integrable (fun y : ℝ => HKx α (x - y) t * g y) :=
      integ_HKx_mul_of_L1 g hα ht hg

    have integ_HKxx_mul :
      Integrable (fun y : ℝ => HKxx α (x - y) t * g y) := by
      simpa using integ_HKxx_mul_of_L1 g hα ht hg

    have meas_HKxx_mul:
      AEStronglyMeasurable (fun y : ℝ => HKxx α (x - y) t * g y) volume
      := aestronglyMeasurable_HKxx_mul g hg ht hα

    have diff_HKx_mul' : ∀ᵐ y ∂volume, ∀ x' ∈ Metric.ball x 1,
        HasDerivAt (fun x'' => HKx α (x'' - y) t * g y) (HKxx α (x' - y) t * g y) x' := by
      filter_upwards [diff_HKxx_mul (α := α) (t := t) (x := x) g ht hα] with y hy
      intro x' hx'
      have h := hy x' hx'
      exact h

    have dominate_fun :
        ∀ᵐ y ∂volume, ∀ x' ∈ Metric.ball x 1,
          |HKxx α (x' - y) t * g y| ≤ Kxx α t * |g y| := by
      filter_upwards with y
      intro x' hx'
      calc
        |HKxx α (x' - y) t * g y| ≤ |HKxx α (x' - y) t| * |g y| := by rw [abs_mul]
        _ ≤ Kxx α t * |g y| := by
          gcongr
          exact pointwise_bound_HKxx ht hα

    have Integ_dominate_fun :
        Integrable (fun y : ℝ => Kxx α t * |g y|) :=
      (hg.abs.const_mul (Kxx α t))

    have result :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (by norm_num)
        meas_HKx_mul
        integ_HKx_mul
        meas_HKxx_mul
        dominate_fun
        Integ_dominate_fun
        diff_HKx_mul'

    exact result.2

end SwapDerivatives


/-!
### 7. Main Result: The Heat Equation
Finally, we combine the pointwise heat equation property of the kernel with the
differentiation-under-integral results to show that the convolution $u(x,t) = (K * g)(x)$
solves the heat equation $u_t = \alpha u_{xx}$.
-/

theorem heat_from_convolution_heatKernel
  {α : ℝ} (g : ℝ → ℝ) (hα : 0 < α) (ht : 0 < t) (hg : Integrable g) :
  ∀ x,
    deriv (fun τ => heatConvolutionHK α g x τ) t
      = α * deriv (fun x' => deriv (fun x'' => heatConvolutionHK α g x'' t) x') x := by
  intro x
  classical

  have swap_t : HasDerivAt (fun τ => ∫ y, heatKernel α (x - y) τ * g y) (∫ y, HKt α (x - y) t * g y) t :=
    swap_t_heatKernel g ht hα hg

  have swap_x : HasDerivAt (fun x' => ∫ y, heatKernel α (x' - y) t * g y) (∫ y, HKx α (x - y) t * g y) x :=
    swap_x_heatKernel g ht hα hg

  have swap_xx : HasDerivAt (fun x' => ∫ y, HKx α (x' - y) t * g y) (∫ y, HKxx α (x - y) t * g y) x :=
    swap_xx_heatKernel g ht hα hg

  -- u_t(x,t)
  have hut :
      deriv (fun τ => heatConvolutionHK α g x τ) t
        = ∫ y, HKt α (x - y) t * g y := by
    simpa [heatConvolutionHK, HKt] using swap_t.deriv

  have swap_x_forall : ∀ x', HasDerivAt (fun x'' => ∫ y, heatKernel α (x'' - y) t * g y)
                            (∫ y, HKx α (x' - y) t * g y) x' := by
    intro x'
    exact swap_x_heatKernel g ht hα hg (x := x')

  have hDx :
      (fun x' => deriv (fun z => heatConvolutionHK α g z t) x')
        = (fun x' => ∫ y, HKx α (x' - y) t * g y) := by
    funext x'
    simpa [heatConvolutionHK, HKx] using (swap_x_forall x').deriv

  -- differentiate that function at x
  have hDx_at :
      deriv (fun x' => deriv (fun z => heatConvolutionHK α g z t) x') x
        = deriv (fun x' => ∫ y, HKx α (x' - y) t * g y) x := by
    simpa using congrArg (fun f : ℝ → ℝ => deriv f x) hDx

  -- compute that derivative via the second swap
  have hx :
      deriv (fun x' => ∫ y, HKx α (x' - y) t * g y) x
        = ∫ y, HKxx α (x - y) t * g y := by
    simpa [HKx, HKxx] using swap_xx.deriv

  -- name u_xx(x,t)
  have huxx :
      deriv (fun x' => deriv (fun z => heatConvolutionHK α g z t) x') x
        = ∫ y, HKxx α (x - y) t * g y := hDx_at.trans hx

  -- Use the established PDE for the heat kernel
  have HK_solves : ∀ y, HKt α (x - y) t = α * HKxx α (x - y) t := fun y =>
    heatKernel_solves_heat_eq (hα := hα) (ht := ht) (x := x - y)

  -- finish: substitute the kernel PDE inside the integrand and pull α out
  calc
    deriv (fun τ => heatConvolutionHK α g x τ) t
        = ∫ y, HKt α (x - y) t * g y := hut
    _   = ∫ y, α * (HKxx α (x - y) t * g y) := by
            have hpt : (fun y : ℝ => HKt α (x - y) t * g y)
                     = (fun y : ℝ => α * (HKxx α (x - y) t * g y)) := by
              funext y
              simpa [mul_left_comm, mul_assoc] using
                congrArg (fun r => r * g y) (HK_solves y)
            simpa using congrArg (fun f : ℝ → ℝ => ∫ y, f y) hpt
    _   = α * ∫ y, HKxx α (x - y) t * g y := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (MeasureTheory.integral_const_mul α (fun y : ℝ => HKxx α (x - y) t * g y))
    _   = α * deriv (fun x' => deriv (fun z => heatConvolutionHK α g z t) x') x := by
            simp [huxx]

end Heat
