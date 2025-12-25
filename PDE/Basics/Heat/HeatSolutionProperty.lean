import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.Order.Basic
import PDE.Basics.Heat.HeatKernel
import PDE.Basics.Heat.HeatSolution

/-!
# Properties of the Heat Fundamental Solution, Solution to the Initial Value Problem

This file establishes key qualitative properties of the solution formula to the heat equation,
involving the convolution of the heat kernel and the initial condition g

## Main Results

* `heat_maximum_principle`: The maximum principle - solutions are bounded by the supremum
  of the initial data
* `heatKernel_IVP_limit_textbook`: Continuity property - the solution converges to the
  initial data as t → 0⁺

## Key Lemmas

* `heatKernel_mass_one_x_sub_y_even`: The solution formula integrates to 1 (translation invariance)
* `heatTail_changeOfVariables`: Change of variables formula for analyzing kernel tails
* `gaussian_tail_bound_by_weighted`: Analytical bound on Gaussian tail integrals

## Reference

This formalization follows Chapter 7.2.3, ["Partial Differential Equations, A First Course"](https://bookstore.ams.org/amstext-54/) by Professor [Rustom Choksi](https://scholar.google.com/citations?user=Fk1zaTgAAAAJ&hl=en).

-/

open MeasureTheory
open scoped Topology
open Filter
open Measure
open MeasureTheory Set Complex
open Set

set_option maxHeartbeats 500000

namespace Heat

variable {g : ℝ → ℝ}
variable {α t : ℝ}


/-! ## Symmetry and Mass Properties -/


/-- The heat kernel is an even function in its spatial argument. -/
lemma heatKernel_even :
    ∀ z : ℝ, heatKernel α (-z) t = heatKernel α z t := by
  intro z
  simp [heatKernel, mul_comm, mul_left_comm]

/-- **Translation Invariance**: The heat kernel integrates to 1 regardless of translation. --/

lemma heatKernel_mass_one_x_sub_y_even
    (x : ℝ) (hα : 0 < α) (ht : 0 < t) : ∫ y, heatKernel α (x - y) t = (1 : ℝ) := by
  have hfun :
      (fun y : ℝ => heatKernel α (x - y) t)
        = (fun y : ℝ => heatKernel α (y - x) t) := by
        unfold heatKernel
        field_simp
  have h_translate :
      ∫ y, heatKernel α (y - x) t = ∫ y, heatKernel α y t := by
    -- `y - x = (-x) + y`
    simpa [add_comm] using (MeasureTheory.integral_add_left_eq_self (μ := volume) (g := -x)
    (f := fun y : ℝ => heatKernel α y t))
  have hMass0 : ∫ y, heatKernel α y t = (1 : ℝ) :=
    integral_heatKernel_one_gaussian (α := α) (t := t) hα ht
  calc
    ∫ y, heatKernel α (x - y) t
        = ∫ y, heatKernel α (y - x) t := by
              simpa using congrArg (fun (f : ℝ → ℝ) => ∫ y, f y) hfun
    _   = ∫ y, heatKernel α y t := h_translate
    _   = (1 : ℝ) := hMass0

/-! ## The Maximum Principle -/


/-- **The Maximum Principle for the Heat Equation**

If the initial data g satisfies |g(y)| ≤ B for all y, then the solution at any
later time and position also satisfies |u(x,t)| ≤ B.

This fundamental property expresses the fact that the heat equation is a diffusion
process that redistributes heat but does not create new temperature extrema. The
maximum and minimum temperatures can only decrease over time. --/

noncomputable def Lmul : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ

lemma heat_maximum_principle
    (x : ℝ) {α t B : ℝ}
    (hα : 0 < α) (ht : 0 < t)
    (hg_meas : AEStronglyMeasurable g)
    (hBound : ∀ y, |g y| ≤ B) :
    |heatConvolutionHK α g x t| ≤ B := by

    unfold heatConvolutionHK

    have hIntR :
      Integrable (fun y : ℝ => heatKernel α (x - y) t * B) := by
       simpa [smul_eq_mul, mul_comm] using ((integrable_heatKernel_slice hα ht x).smul B)

    have hIntL :
      Integrable (fun y : ℝ => heatKernel α (x - y) t * |g y|) :=
      integrable_heatKernel_mul_of_Linfty g hα ht hg_meas hBound

    calc
      |heatConvolutionHK α g x t|
         ≤ ∫ y, heatKernel α (x - y) t * |g y| := by
          simp_rw [heatConvolutionHK]
          refine (abs_integral_le_integral_abs
                (f := fun y => heatKernel α (x - y) t * g y)).trans_eq ?_
          simp_rw [abs_mul, abs_of_pos (heatKernel_pos α t hα ht)]
      _ ≤ ∫ y, heatKernel α (x - y) t * B := by
          refine integral_mono hIntL hIntR (fun y => ?_)
          exact mul_le_mul_of_nonneg_left (hBound y) (heatKernel_pos α t hα ht).le
      _ = (∫ y, heatKernel α (x - y) t) * B := by
          simpa [mul_comm] using
             (integral_const_mul (μ := volume)
             (r := B) (f := fun y : ℝ => heatKernel α (x - y) t))
      _ = B := by
         simp [heatKernel_mass_one_x_sub_y_even x hα ht, one_mul]

/-! ## Gaussian Tail Analysis

This section contains technical lemmas for analyzing the decay of Gaussian tail integrals,
which are needed to prove that the solution converges to the initial data as t → 0⁺.
-/

/-- Change of variables formula for heat kernel tail integrals.

    Transforms the integral ∫_{|y-x| ≥ δ} Φ(x-y,t) dy into a standard Gaussian
    tail integral via the substitution z = (x-y)/√(4αt). -/

lemma heatTail_changeOfVariables
    {α x δ t : ℝ} (hα : 0 < α) (ht : 0 < t) :
  (∫ y, Set.indicator {y : ℝ | δ ≤ |y - x|}
            (fun y => heatKernel α (x - y) t) y)
  = (1 / Real.sqrt Real.pi) *
    ∫ z, Set.indicator
           {z : ℝ | (δ / Real.sqrt (4 * α * t)) ≤ |z|}
           (fun z => Real.exp (-z^2)) z := by
    unfold heatKernel

    let s : ℝ := Real.sqrt (4 * α * t)
    have s_pos: 0 < s := by positivity

    calc
       ∫ (y : ℝ), {y | δ ≤ |y - x|}.indicator (fun y ↦ 1 / √(4 * Real.pi * α * t) * Real.exp (-(x - y) ^ 2 / (4 * α * t))) y
        = ∫ z, Set.indicator {z : ℝ | δ ≤ |z|}
               (fun z => 1 / √(4 * Real.pi * α * t) * Real.exp (-z^2 / (4 * α * t))) z := by
          simp only [abs_sub_comm]
          exact integral_sub_left_eq_self (fun z =>
                 Set.indicator {z : ℝ | δ ≤ |z|} (fun z => 1 / √(4 * Real.pi * α * t) * Real.exp (-z^2 / (4 * α * t))) z)
                 (μ := volume) (x : ℝ)
      _ = ∫ z, Set.indicator {z : ℝ | δ / s ≤ |s⁻¹  * z|}
               (fun z => 1 / √(4 * Real.pi * α * t) * Real.exp (-(s⁻¹ * z)^2)) z := by
            congr 1; ext z;
            simp only [Set.indicator]
            congr 1
            · simp only [Set.mem_setOf_eq]
              rw [div_le_iff₀' s_pos, abs_mul, abs_inv, abs_of_pos s_pos]
              field_simp [s_pos.ne.symm]
            · congr 2
              field_simp [s_pos.ne.symm]; left; rw [Real.sq_sqrt]; positivity
      _ = 1 / √(4 * Real.pi * α * t) * ∫ z, Set.indicator {z : ℝ | δ / s ≤ |s⁻¹  * z|}
               (fun z => Real.exp (-(s⁻¹ * z)^2)) z := by
          simp [Set.indicator_const_mul]
          rw [integral_const_mul]
      _ =  1 / √(4 * Real.pi * α * t) * (s * ∫ z, Set.indicator {z : ℝ | δ / s ≤ |z|}
               (fun z => Real.exp (-z^2)) z) := by
          congr 1
          set f : ℝ → ℝ := fun u ↦ {u | δ / s ≤ |u|}.indicator (fun u => Real.exp (-u ^ 2)) u
          have hf : (fun z ↦ {z | δ / s ≤ |s⁻¹ * z|}.indicator (fun z => Real.exp (-(s⁻¹ * z) ^ 2)) z) =
            (fun z ↦ f (s⁻¹ * z)) := by
            ext z; dsimp [f]; rfl
          rw [hf, integral_comp_mul_left f s⁻¹, inv_inv, abs_of_pos]; rfl; exact s_pos
      _ = (1 / Real.sqrt Real.pi) * ∫ z, Set.indicator
           {z : ℝ | δ / s ≤ |z|}
           (fun z => Real.exp (-z^2)) z := by
           unfold s; rw [← mul_assoc]; field_simp; ring

def IsBoundedAbs (g : ℝ → ℝ) : Prop := ∃ B, ∀ y, |g y| ≤ B

/-- Integrability of z² exp(-z²). Used in Gaussian tail bounds. -/
lemma int_z_sq_exp_z_sq : Integrable (fun z : ℝ => |z|^2 * Real.exp (-z^2)) := by
      simpa [one_mul] using integrable_rpow_mul_exp_neg_mul_sq (by norm_num : 0 < (1 : ℝ))
          (by norm_num : (-1 : ℝ) < (2 : ℝ))

/-- The "far" region {y : |y - x| ≥ δ} is measurable. -/
lemma far_measurable (δ x : ℝ) : MeasurableSet ({y | δ ≤ |y - x|} : Set ℝ) := by
  simpa using measurableSet_le measurable_const (measurable_id.sub_const x).abs

/-- Helper lemma for splitting integrals into near and far regions. -/
lemma integral_split_near_far {α x t : ℝ} (g : ℝ → ℝ) (far : Set ℝ)
    (hα : 0 < α) (ht : 0 < t)
    (hg : Integrable g) (h_meas_far : MeasurableSet far):
    ∫ y, heatKernel α (x - y) t * (g y - g x) ∂volume =
      (∫ y in farᶜ, heatKernel α (x - y) t * (g y - g x) ∂volume) +
      ∫ y in far,  heatKernel α (x - y) t * (g y - g x) ∂volume := by

  have h_int : Integrable (fun y => heatKernel α (x - y) t * (g y - g x)) := by
    have h1 : Integrable (fun y => heatKernel α (x - y) t * g y) :=
      integrable_heatKernel_mul_of_L1 g hα ht hg
    have h2 : Integrable (fun y => heatKernel α (x - y) t * g x) :=
      (integrable_heatKernel_slice hα ht (x:= x)).mul_const (g x)
    have h_eq : (fun y => heatKernel α (x - y) t * (g y - g x)) =
                (fun y => heatKernel α (x - y) t * g y) - (fun y => heatKernel α (x - y) t * g x) := by
      ext y
      simp [mul_sub]
    rw [h_eq]
    exact Integrable.sub h1 h2

  exact (integral_add_compl (s := far) h_meas_far h_int).symm.trans (by rw [add_comm])

/-- For even functions, the two-sided tail integral equals twice the one-sided integral. -/
lemma integral_indicator_tail_even {f : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (heven : ∀ x, f (-x) = f x)
    (hint : IntegrableOn f (Set.Ici R)) :
    ∫ z, Set.indicator {z : ℝ | R ≤ |z|} f z
    = 2 * ∫ z in Set.Ici R, f z := by
  -- Split {z | R ≤ |z|} into two parts: (-∞, -R] ∪ [R, ∞)
  have h_split : {z : ℝ | R ≤ |z|} = Set.Iic (-R) ∪ Set.Ici R := by
    ext z
    simp only [Set.mem_setOf, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro h
      by_cases hz : z < 0
      · left
        simp [abs_of_neg hz] at h
        linarith
      · right
        push_neg at hz
        simp [abs_of_nonneg hz] at h
        exact h
    · intro h
      cases h with
      | inl h => simp [abs_of_nonpos (by linarith : z ≤ 0)]; linarith
      | inr h => simp [abs_of_nonneg (by linarith : 0 ≤ z)]; exact h

  have h_disj : Disjoint (Set.Iic (-R)) (Set.Ici R) := by
    rw [Set.disjoint_iff]
    intro z hz
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici] at hz
    obtain ⟨h1, h2⟩ := hz
    linarith

  rw [h_split, Set.indicator_union_of_disjoint h_disj]

  rw [integral_add]
  swap; · -- integrability on Iic (-R)
    have h_int_left : IntegrableOn f (Set.Iic (-R)) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, Set.neg_preimage, Set.neg_Iic, neg_neg]
      convert hint using 2
      aesop
    rw [integrable_indicator_iff measurableSet_Iic]
    exact h_int_left

  swap; ·
    rw [integrable_indicator_iff measurableSet_Ici]
    exact hint

  have h_left_eq_right :
      ∫ z, Set.indicator (Set.Iic (-R)) f z = ∫ z, Set.indicator (Set.Ici R) f z := by
    rw [integral_indicator measurableSet_Iic]
    rw [integral_indicator measurableSet_Ici]
    -- Strategy: show ∫_{Iic(-R)} f = ∫_{Ici R} f using negation and evenness
    have : ∫ x in Set.Iic (-R), f x = ∫ x in Set.Ici R, f (-x) := by
      calc ∫ x in Set.Iic (-R), f x
          = ∫ x in Set.Ioi R, f (-x) := by
              convert integral_comp_neg_Iic (c := -R) f using 2
              aesop
              aesop
              aesop
        _ = ∫ x in Set.Ici R, f (-x) := by
              rw [← integral_Ici_eq_integral_Ioi']
              aesop
    rw [this]
    apply setIntegral_congr_ae measurableSet_Ici
    filter_upwards with z hz
    exact heven z
  rw [h_left_eq_right, integral_indicator measurableSet_Ici, ← two_mul]

/-- Evaluation of ∫₀^∞ z exp(-z²) dz = 1/2. -/
lemma integral_mul_exp_neg_sq_Ici_zero : ∫ z in Set.Ici 0, z * Real.exp (-z^2) = 1 / 2 := by
  have Comp_exp_Real: ∫ x : ℝ in Set.Ioi 0, (x : ℂ) * Complex.exp (-(x : ℂ) ^ 2)
     = ∫ x : ℝ in Set.Ioi 0, x * Real.exp (-x ^ 2) := by
    simp_rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    exact integral_ofReal
  have Comp_exp_eval : ∫ x : ℝ in (Set.Ioi 0), (x : ℂ) * Complex.exp (-(x : ℂ) ^ 2) = 1/2 := by
    simpa using integral_mul_cexp_neg_mul_sq (by norm_num : (0 : ℝ) < (1 : ℂ).re)
  rw [integral_Ici_eq_integral_Ioi]
  apply Complex.ofReal_injective
  simpa [Comp_exp_Real] using Comp_exp_eval

/-- **Key Gaussian tail bound**:

    This is the analytical estimate that allows us to bound Gaussian tail integrals
    and prove convergence as t → 0. -/
lemma gaussian_tail_bound_by_weighted {R : ℝ} (hR : 0 < R) :
    ∫ z in Set.Ici R, Real.exp (-z^2) ≤ (1 / R) * ∫ z in Set.Ici 0, z * Real.exp (-z^2) := by
  have h_gauss_int : Integrable (fun z => Real.exp (-z^2)) := by
    have := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
    convert this using 1
    ext z; ring_nf

  have h_weighted_gauss_int : IntegrableOn (fun z => z * Real.exp (-z^2)) (Set.Ici 0) := by
    have h_full : Integrable (fun z : ℝ => z * Real.exp (-z^2)) := by
      have := integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
      convert this using 1
      ext z
      ring_nf
    exact h_full.integrableOn

  have h_extend : ∫ z in Set.Ici R, z * Real.exp (-z^2) ≤ ∫ z in Set.Ici 0, z * Real.exp (-z^2) := by
    apply setIntegral_mono_set h_weighted_gauss_int
    · filter_upwards [self_mem_ae_restrict (measurableSet_Ici : MeasurableSet (Set.Ici (0:ℝ)))] with z hz
      exact mul_nonneg hz (by positivity)
    · exact Eventually.of_forall (Set.Ici_subset_Ici.mpr (le_of_lt hR))

  have h_main : ∫ z in Set.Ici R, Real.exp (-z^2) ≤ (1 / R) * ∫ z in Set.Ici R, z * Real.exp (-z^2) := by
    have h_pointwise : ∀ z ∈ Set.Ici R, Real.exp (-z^2) ≤ (1 / R) * (z * Real.exp (-z^2)) := by
      intro z hz
      simp only [Set.mem_Ici] at hz
      have h_div : 1 ≤ z / R := by rw [le_div_iff₀ hR]; linarith
      calc Real.exp (-z^2)
          = 1 * Real.exp (-z^2) := by ring
        _ ≤ (z / R) * Real.exp (-z^2) := mul_le_mul_of_nonneg_right h_div (by positivity)
        _ = (1 / R) * (z * Real.exp (-z^2)) := by field_simp

    have h_int_right : IntegrableOn (fun z => (1 / R) * (z * Real.exp (-z^2))) (Set.Ici R) := by
      exact (h_weighted_gauss_int.mono_set (Set.Ici_subset_Ici.mpr (le_of_lt hR))).const_mul (1 / R)

    calc ∫ z in Set.Ici R, Real.exp (-z^2)
        ≤ ∫ z in Set.Ici R, (1 / R) * (z * Real.exp (-z^2)) :=
          setIntegral_mono_on h_gauss_int.integrableOn h_int_right measurableSet_Ici h_pointwise
      _ = (1 / R) * ∫ z in Set.Ici R, z * Real.exp (-z^2) := by
          rw [integral_const_mul]

  calc ∫ z in Set.Ici R, Real.exp (-z^2)
      ≤ (1 / R) * ∫ z in Set.Ici R, z * Real.exp (-z^2) := h_main
    _ ≤ (1 / R) * ∫ z in Set.Ici 0, z * Real.exp (-z^2) := by gcongr

/-! ## Convergence to Initial Data

This section proves that the solution u(x,t) → g(x) as t → 0⁺, establishing that
the convolution formula satisfies the initial condition.
-/

/-- **Main Theorem: The solution converges to the initial data as t → 0⁺**

Given bounded, continuous, integrable initial data g, the solution
u(x,t) = ∫ Φ(x-y,t) g(y) dy converges to g(x) as t → 0⁺.

### Proof Strategy

The proof follows the textbook approach:

1. **Rewrite using mass-one property**:
   |u(x,t) - g(x)| = |∫ Φ(x-y,t)[g(y) - g(x)] dy|

2. **Split into near and far regions**: Choose δ > 0 from continuity of g at x.
   - Near: |y-x| < δ where |g(y) - g(x)| < ε/2
   - Far: |y-x| ≥ δ where we use boundedness

3. **Estimate near integral**:
   ∫_{near} Φ |g(y) - g(x)| dy ≤ (ε/2) ∫_{near} Φ dy ≤ ε/2

4. **Estimate far integral using Gaussian tail bounds**:
   ∫_{far} Φ |g(y) - g(x)| dy ≤ 2B ∫_{far} Φ dy ≤ C√t

5. **Choose t small enough**: For t < δ₀, have C√t < ε/2, giving total < ε.
-/

theorem heatKernel_IVP_limit_textbook
    {α : ℝ} (g : ℝ → ℝ) (x : ℝ)
    (hα : 0 < α)
    (g_bounded : IsBoundedAbs g)
    (g_cont : Continuous g)
    (g_int : Integrable g) :
    Tendsto (fun t : ℝ => heatConvolutionHK α g x t) (𝓝[>] 0) (𝓝 (g x)) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε

  ------------------------------------------------------------------
  -- Step 0: Positivity and mass-one properties of the heat kernel
  ------------------------------------------------------------------
  have hk_nonneg : ∀ (t : ℝ), 0 < t → ∀ y, 0 < heatKernel α (x - y) t := by
    intro t ht y
    exact heatKernel_pos α t (x:= x - y) hα ht

  have hK_int : ∀ t > 0, Integrable (fun y ↦ heatKernel α (x - y) t) := by
        intro t ht_pos
        exact integrable_heatKernel_slice hα ht_pos x

  have hk_mass_one : ∀ (t : ℝ), 0 < t → ∫ y, heatKernel α (x - y) t = (1 : ℝ) := by
    intro t ht
    exact heatKernel_mass_one_x_sub_y_even x hα ht

  ------------------------------------------------------------------
  -- Step 1: Boundedness: ∃ B > 0 s.t. |g(y)| ≤ B for all y (textbook’s B)
  ------------------------------------------------------------------
  rcases g_bounded with ⟨B₀, hB₀_bound⟩
  let B := max B₀ 1
  have hB_bound : ∀ y, |g y| ≤ B := fun y => le_trans (hB₀_bound y) (le_max_left B₀ 1)
  have hB_pos : 0 < B := by
    simp only [B]
    exact zero_lt_one.trans_le (le_max_right B₀ 1)

  have g_diff_bound : ∀ x y : ℝ, |g y - g x| ≤ 2 * B := by
      intro x y
      linarith [hB_bound y, hB_bound x, abs_sub (g y) (g x)]

  have h_integrable : ∀ t > 0, Integrable (fun y ↦ heatKernel α (x - y) t * |g y - g x|) := by
          intro t ht_pos
          have h_diff_bdd : IsBoundedAbs (fun y ↦ |g y - g x|) := by
            use B + |g x|
            intro y
            simp only [abs_abs]
            calc |g y - g x|
              _ ≤ |g y| + |g x| := abs_sub _ _
              _ ≤ B + |g x|     := add_le_add_right (hB_bound y) _
          have h_diff_meas : AEStronglyMeasurable (fun y ↦ |g y - g x|) volume :=
            (Continuous.abs (Continuous.sub g_cont continuous_const)).aestronglyMeasurable
          have h_swapped := Integrable.bdd_mul (hK_int t ht_pos) h_diff_meas h_diff_bdd
          apply Integrable.congr h_swapped
          filter_upwards with y
          rw [mul_comm]
  ------------------------------------------------------------------
  -- Step 2: Continuity of g at x: find δ₁ with |y-x|<δ₁ ⇒ |g y - g x| < ε/2
  ------------------------------------------------------------------
  have hε4_pos : 0 < ε / 4 := by linarith
  have h_cont_at : ContinuousAt g x := g_cont.continuousAt

  obtain ⟨δ₁, hδ₁_pos, hδ₁_bound⟩ :
      ∃ δ₁ > 0, ∀ y, |y - x| < δ₁ → |g y - g x| < ε / 4 := by
    exact Metric.continuousAt_iff.mp h_cont_at (ε / 4) hε4_pos

  ------------------------------------------------------------------
  -- Define near / far regions with this δ₁:
  --   near := {y | |y - x| < δ₁}
  --   far  := {y | |y - x| ≥ δ₁}
  ------------------------------------------------------------------
  let near : Set ℝ := {y | |y - x| < δ₁}
  let far  : Set ℝ := {y | δ₁ ≤ |y - x|}

  have h_far_compl : far = nearᶜ := by
   simp [near, far, Set.compl_setOf]

  have h_meas_near : MeasurableSet near := by
    dsimp [near]
    exact measurableSet_lt (measurable_id.sub_const x).abs measurable_const

  have h_meas_far : MeasurableSet far := by
    dsimp [far]
    exact measurableSet_le measurable_const (measurable_id.sub_const x).abs

  ------------------------------------------------------------------
  -- Step 3: For each fixed t > 0, *rewrite* the difference
  --   |∫ Φ(x-y,t)g(y) dy - g(x)|,
  -- using the mass-one property of Φ and its positivity, exactly like the book:
  --
  -- g(x) = ∫ Φ(x-y,t) g(x) dy
  -- ⇒ difference = |∫ Φ(x-y,t)(g(y)-g(x)) dy|
  -- ≤ ∫ Φ(x-y,t)|g(y)-g(x)| dy.
  ------------------------------------------------------------------
  have main_ineq_for_t :
      ∀ t > 0,
        |(∫ y, heatKernel α (x - y) t * g y) - g x|
          ≤ ∫ y, heatKernel α (x - y) t * |g y - g x| := by
    intro t ht_pos
    have h_mass : ∫ y, heatKernel α (x - y) t = 1 := hk_mass_one t ht_pos
    have h_pos : ∀ y, 0 < heatKernel α (x - y) t := hk_nonneg t ht_pos
    calc
      |(∫ y, heatKernel α (x - y) t * g y )- g x|
        = |(∫ y, heatKernel α (x - y) t * g y) - g x| := by rfl
      _ = |(∫ y, heatKernel α (x - y) t * g y) - (g x * 1)| := by simp
      _ = |(∫ y, heatKernel α (x - y) t * g y) - (g x * ∫ y, heatKernel α (x - y) t)| := by rw [h_mass]
      _ = |(∫ y, heatKernel α (x - y) t * g y) - ∫ y, (g x) * heatKernel α (x - y) t| := by
          rw [integral_const_mul (g x)]
      _ = |∫ y, (heatKernel α (x - y) t * g y - (g x) * heatKernel α (x - y) t)| := by
          rw [integral_sub]
          · -- integrability of y ↦ heatKernel α (x - y) t * g y
            exact integrable_heatKernel_mul_of_L1 g hα ht_pos g_int
          · -- integrability of y ↦ g x * heatKernel α (x - y) t
            exact (integrable_heatKernel_slice hα ht_pos x).const_mul (g x)
      _ = |∫ y, heatKernel α (x - y) t * (g y - g x)| := by
          congr; ext y; ring
      _ ≤ ∫ y, |heatKernel α (x - y) t * (g y - g x)| := by
          simpa using abs_integral_le_integral_abs
      _ = ∫ y, heatKernel α (x - y) t * |g y - g x| := by
          refine integral_congr_ae ?_
          filter_upwards with y
          rw [abs_mul, abs_of_pos (h_pos y)]
  ------------------------------------------------------------------
  -- Step 4: Split the last integral into near and far pieces:
  --    ∫ Φ |g - g(x)| = ∫_{near} + ∫_{far}.
  ------------------------------------------------------------------
  have split_near_far :
      ∀ t > 0,
        ∫ y, heatKernel α (x - y) t * |g y - g x| ∂volume
          =
        ∫ y in near, heatKernel α (x - y) t * |g y - g x|∂volume +
        ∫ y in far,  heatKernel α (x - y) t * |g y - g x|∂volume := by
    intro t ht_pos
    rw [show far = nearᶜ from h_far_compl]
    simpa using (integral_add_compl h_meas_near (h_integrable t ht_pos)).symm

  ------------------------------------------------------------------
  -- Step 5: Estimate the *near* integral using continuity: on near,
  --   |g(y)-g(x)| < ε/2.
  -- Thus
  --   ∫_{near} Φ |g-g(x)|
  -- ≤ ε/2 ∫_{near} Φ
  -- ≤ ε/2.
  -----------------------------------------------------------------------------
  have near_bound :
      ∀ t > 0,
        ∫ y in near, heatKernel α (x - y) t * |g y - g x|
          ≤ ε / 4 := by
    intro t ht_pos

    have hφ_nonneg : ∀ y, 0 ≤ heatKernel α (x - y) t :=
      fun y => (hk_nonneg t ht_pos y).le

    have h_point :
        ∀ y ∈ near,
          heatKernel α (x - y) t * |g y - g x|
            ≤ heatKernel α (x - y) t * (ε / 4) := by
      intro y hy
      have hy_lt : |y - x| < δ₁ := by
        simpa [near] using hy
      have hcont : |g y - g x| ≤ ε / 4 := (hδ₁_bound y hy_lt).le
      exact mul_le_mul_of_nonneg_left hcont (hφ_nonneg y)

    have h_int_right :
        IntegrableOn
          (fun y => heatKernel α (x - y) t * (ε / 4)) near := by
      exact ((hK_int t ht_pos).mul_const (ε / 4)).integrableOn

    have h_int_left :
        IntegrableOn
          (fun y => heatKernel α (x - y) t * |g y - g x|) near := by
      exact (h_integrable t ht_pos).integrableOn

    calc
     ∫ y in near, heatKernel α (x - y) t * |g y - g x|
          ≤ ∫ y in near, heatKernel α (x - y) t * (ε / 4) := by
      exact setIntegral_mono_on h_int_left h_int_right h_meas_near h_point
     _ ≤ (ε / 4) * ∫ y in near, heatKernel α (x - y) t := by
       rw [integral_mul_const]
       linarith
     _ ≤ (ε / 4) * ∫ y, heatKernel α (x - y) t := by
       gcongr
       exact setIntegral_le_integral (hK_int t ht_pos) (ae_of_all _ hφ_nonneg)
     _ ≤ ε / 4 := by simp [hk_mass_one t ht_pos]

  ---------------------------------------------------------------------------------
  -- Step 6: Estimate the *far* integral using boundedness:
  -- for all y, |g(y)| ≤ B ⇒ |g(y) - g(x)| ≤ 2B.
  -- So
  --   ∫_{far} Φ |g-g(x)|
  -- ≤ 2B ∫_{far} Φ.
  ------------------------------------------------------------------
  have far_bound_reduction :
      ∀ t > 0,
        ∫ y in far, heatKernel α (x - y) t * |g y - g x|
          ≤ 2 * B *
              (∫ y in far, heatKernel α (x - y) t) := by
    intro t ht_pos

    have h_int_left : IntegrableOn (fun y => heatKernel α (x - y) t * |g y - g x|) far := by
      exact (h_integrable t ht_pos).integrableOn

    have h_int_right : IntegrableOn (fun y => heatKernel α (x - y) t * (2 * B)) far := by
      exact ((hK_int t ht_pos).mul_const (2 * B)).integrableOn

    calc
     ∫ y in far, heatKernel α (x - y) t * |g y - g x|
          ≤ ∫ y in far, heatKernel α (x - y) t * (2 * B) := by
      apply setIntegral_mono_on h_int_left h_int_right h_meas_far
      intro y hy
      exact mul_le_mul_of_nonneg_left (g_diff_bound x y) (hk_nonneg t ht_pos y).le
     _ = (2 * B) * ∫ y in far, heatKernel α (x - y) t := by
       rw [integral_mul_const, mul_comm (2 * B)]

  ------------------------------------------------------------------
  -- Step 7: Tail integral of the kernel on the far set:
  --
  --   ∫_{|y-x|≥δ₁} Φ(x-y,t) dy
  --
  -- rewrite Φ explicitly:
  --   (1 / √(4παt)) ∫_{|y-x|≥δ₁} e^{-(x-y)² / (4αt)} dy,
  --
  -- change variables z = (y-x)/√(4αt), dy = √(4αt) dz,
  --
  -- to get
  --
  --   (2 / √π) ∫_{δ₁ / √(4αt)}^∞ e^{-z²} dz,
  --
  -- exactly as in the textbook.
  ------------------------------------------------------------------
  have far_tail_as_gaussian :
      ∀ t > 0,
        ∫ y in far, heatKernel α (x - y) t
          =
        (2 / Real.sqrt Real.pi) *
          ∫ z in Set.Ici (δ₁ / Real.sqrt (4 * α * t)),
            Real.exp (-z^2) := by
    intro t ht_pos
    rw [← integral_indicator h_meas_far]
    rw [show far = {y : ℝ | δ₁ ≤ |y - x|} by rfl]
    rw [heatTail_changeOfVariables hα ht_pos]
    let R := δ₁ / Real.sqrt (4 * α * t)
    -- Use symmetry to convert two-sided tail to one-sided
    have h_symm_to_one_side :
      ∫ z, Set.indicator {z : ℝ | R ≤ |z|} (fun z => Real.exp (-z^2)) z
      = 2 * ∫ z in Set.Ici R, Real.exp (-z^2) := by
      refine integral_indicator_tail_even (by positivity) (fun x => by simp) ?_
      have h_integrable_all : Integrable (fun z : ℝ => Real.exp (-z^2)) := by
        have := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
        convert this using 1
        ext z
        ring_nf
      exact h_integrable_all.integrableOn
    rw [h_symm_to_one_side]
    ring

  ------------------------------------------------------------------
  -- Step 8: Analytic estimate on the Gaussian tail:
  --
  --   ∫_{a}^∞ e^{-z²}dz ≤ (1/a) ∫_{a}^∞ z e^{-z²}dz
  --                     = (1/(2a)) e^{-a²},
  --
  -- together giving a bound of the form
  --
  --   ∫_{|y-x|≥δ₁} Φ(x-y,t) dy ≤ C * √t * e^{-δ₁² / (4αt)},
  --
  -- exactly as in the book.
  ------------------------------------------------------------------
  have gaussian_tail_bound :
      ∃ C > 0,
        ∀ t > 0,
          ∫ y in far, heatKernel α (x - y) t
            ≤ C * Real.sqrt t := by
    use (2 / (Real.sqrt Real.pi * δ₁)) * Real.sqrt α
    constructor
    · positivity

    intro t ht_pos
    rw [far_tail_as_gaussian t ht_pos]

    let R := δ₁ / Real.sqrt (4 * α * t)
    have hR_pos : 0 < R := by positivity

    -- Key textbook inequality: ∫_a^∞ e^{-z²} dz ≤ (1/a) ∫_a^∞ z e^{-z²} dz ≤ (1/a) ∫_0^∞ z e^{-z²} dz
    have gauss_tail_simple :
        ∫ z in Set.Ici R, Real.exp (-z^2) ≤ (1 / R) * ∫ z in Set.Ici 0, z * Real.exp (-z^2) := by
      exact gaussian_tail_bound_by_weighted (by positivity : 0 < R)

    have integral_z_gauss : ∫ z in Set.Ici 0, z * Real.exp (-z^2) = 1 / 2 := by
      exact integral_mul_exp_neg_sq_Ici_zero

    calc (2 / Real.sqrt Real.pi) * ∫ z in Set.Ici R, Real.exp (-z^2)
        ≤ (2 / Real.sqrt Real.pi) * ((1 / R) * ∫ z in Set.Ici 0, z * Real.exp (-z^2)) := by
          apply mul_le_mul_of_nonneg_left gauss_tail_simple; positivity
      _ = (2 / Real.sqrt Real.pi) * ((1 / R) * (1 / 2)) := by rw [integral_z_gauss]
      _ = (1 / Real.sqrt Real.pi) * (1 / R) := by ring
      _ = (1 / Real.sqrt Real.pi) * (Real.sqrt (4 * α * t) / δ₁) := by
          congr 1; field_simp; unfold R; field_simp
      _ = (2 / Real.sqrt Real.pi) * (Real.sqrt (α * t) / δ₁) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
          ring_nf; field_simp
      _ = (2 / (Real.sqrt Real.pi * δ₁)) * Real.sqrt α * Real.sqrt t := by
          rw [Real.sqrt_mul (by positivity)]; ring

  ------------------------------------------------------------------
  -- Step 9: Combine near + far estimates for fixed t>0:
  --
  -- By main_ineq_for_t, split_near_far, near_bound, far_bound_reduction,
  -- and the Gaussian tail bound, we get
  --
  --   |∫ Φ g - g(x)|
  -- ≤ ε/2 + 2B * C * √t * e^{-δ₁² / (4αt)}.
  --
  -- This is the analogue of the final displayed inequality before
  -- choosing δ in the textbook.
  ------------------------------------------------------------------
  have total_bound_for_t :
      ∃ C' > 0,
        ∀ t > 0,
          |(∫ y, heatKernel α (x - y) t * g y) - g x|
            ≤ ε / 4 + C' * Real.sqrt t := by
    obtain ⟨C, hC_pos, hC_bound⟩ := gaussian_tail_bound
    use 2 * B * C
    constructor
    · positivity

    intro t ht_pos

    calc |(∫ y, heatKernel α (x - y) t * g y) - g x|
        ≤ ∫ y, heatKernel α (x - y) t * |g y - g x| := main_ineq_for_t t ht_pos
      _ = (∫ y in near, heatKernel α (x - y) t * |g y - g x|) +
          (∫ y in far, heatKernel α (x - y) t * |g y - g x|) := split_near_far t ht_pos
      _ ≤ ε / 4 + (∫ y in far, heatKernel α (x - y) t * |g y - g x|) := by
          gcongr
          exact near_bound t ht_pos
      _ ≤ ε / 4 + 2 * B * (∫ y in far, heatKernel α (x - y) t) := by
          gcongr
          exact far_bound_reduction t ht_pos
      _ ≤ ε / 4 + 2 * B * (C * Real.sqrt t) := by
          gcongr
          exact hC_bound t ht_pos
      _ = ε / 4 + (2 * B * C) * Real.sqrt t := by ring

  ------------------------------------------------------------------
  -- Step 10: Choose δ > 0 so that for 0 < t < δ we have
  --
  --   C' * √t * e^{-δ₁² / (4αt)} ≤ ε/2,
  --
  -- i.e. the tail term is ≤ ε/2. That’s exactly what the textbook does
  -- with the inequality
  --
  --   δ < (π δ₁² ε²) / (64 α B²),
  --
  -- though we don't need the explicit formula in Lean, just existence.
  ------------------------------------------------------------------
  obtain ⟨C', hC'_pos, hC'_bound⟩ := total_bound_for_t
  have : ∃ δ > 0,
      ∀ t, 0 < t → t < δ →
        C' * Real.sqrt t ≤ ε / 4 := by
    use (ε / (4 * C'))^2
    constructor
    · positivity
    intro t ht_pos ht_small
    calc C' * Real.sqrt t
        ≤ C' * Real.sqrt ((ε / (4 * C'))^2) := by gcongr
      _ = C' * (ε / (4 * C')) := by
          rw [Real.sqrt_sq]; positivity
      _ = ε / 4 := by field_simp; ring

  rcases this with ⟨δ, hδ_pos, hδ_small⟩

  ------------------------------------------------------------------
  -- Step 11: For 0 < t < δ, we now have
  --
  --   |∫ Φ g - g(x)| ≤ ε/2 + ε/2 = ε.
  --
  -- Turn that into the `∀ᶠ` statement required by `Metric.tendsto_nhds`.
  ------------------------------------------------------------------
  have h_eventually :
      ∀ᶠ t in 𝓝[>] 0,
        dist (heatConvolutionHK α g x t) (g x) < ε := by
    filter_upwards [Ioo_mem_nhdsGT_of_mem ⟨le_refl 0, hδ_pos⟩] with t ht
    simp only [Set.mem_Ioo] at ht
    obtain ⟨ht_pos, ht_lt⟩ := ht
    rw [heatConvolutionHK, dist_comm, Real.dist_eq]
    calc |g x - ∫ y, heatKernel α (x - y) t * g y|
        = |(∫ y, heatKernel α (x - y) t * g y) - g x| := by rw [abs_sub_comm]
      _ ≤ ε / 4 + C' * Real.sqrt t := hC'_bound t ht_pos
      _ ≤ ε / 4 + ε / 4 := by gcongr; exact hδ_small t ht_pos ht_lt
      _ = ε / 2 := by ring
      _ < ε := by linarith
  exact h_eventually

end Heat
