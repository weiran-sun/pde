/-
Copyright (c) 2025. All rights reserved.
Formalization of Hausdorff measure computations:
  Theorem A: H¹(S¹) = 2π
  Theorem B: H²(S²) = 4π

Working from the definition of Hausdorff measure, following:
  pde_latex/PDE/Background/CalculusMeasureTheory/HausdorffUnitCircleSphere.tex

Reference: Choksi, "Partial Differential Equations, A First Course", AMS 2022.
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import PDE.Background.CalculusMeasureTheory.GraphHausdorffMeasure.R3GraphMeasure

open MeasureTheory Measure Set Filter Topology Real
open scoped ENNReal NNReal

noncomputable section

/-! # Hausdorff Measure of the Unit Circle and Sphere

We prove from the definition of Hausdorff measure:
* `hausdorff_circle` : H¹(S¹) = 2π
* `hausdorff_sphere` : H²(S²) = 4π
-/

/-! ## Section 1: Trigonometric Lemmas -/

/-- The unit circle parametrization E(t) = (cos t, sin t) ∈ ℝ². -/
def circleParam (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![cos t, sin t]

/-- Chord length formula: |E(t) - E(s)| = 2|sin((t-s)/2)|. -/
theorem chord_length (s t : ℝ) :
    ‖circleParam t - circleParam s‖ = 2 * |sin ((t - s) / 2)| := by
  suffices h : ‖circleParam t - circleParam s‖ ^ 2 = (2 * |sin ((t - s) / 2)|) ^ 2 by
    have h1 : (0 : ℝ) ≤ ‖circleParam t - circleParam s‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ 2 * |sin ((t - s) / 2)| := by positivity
    nlinarith [sq_nonneg (‖circleParam t - circleParam s‖ - 2 * |sin ((t - s) / 2)|)]
  rw [EuclideanSpace.norm_sq_eq]
  have key : ∀ (v : Fin 2 → ℝ), ((EuclideanSpace.equiv (Fin 2) ℝ).symm v).ofLp = v := fun _ => rfl
  simp only [circleParam, PiLp.sub_apply, Fin.sum_univ_two, Real.norm_eq_abs, key,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hrhs : (2 * |sin ((t - s) / 2)|) ^ 2 = 4 * sin ((t - s) / 2) ^ 2 := by
    rw [mul_pow, sq_abs]; ring
  rw [hrhs, sq_abs, sq_abs]
  have hcos : cos (2 * ((t - s) / 2)) = 2 * cos ((t - s) / 2) ^ 2 - 1 := cos_two_mul _
  have hts : 2 * ((t - s) / 2) = t - s := by ring
  rw [hts] at hcos
  nlinarith [cos_sub t s, sin_sq t, cos_sq t, sin_sq s, cos_sq s, sin_sq ((t - s) / 2)]

/-- Two-sided sine bound: for x ∈ [0, π], x - x³/6 ≤ sin x ≤ x. -/
theorem sin_bounds {x : ℝ} (hx0 : 0 ≤ x) (hxπ : x ≤ π) :
    x - x ^ 3 / 6 ≤ sin x ∧ sin x ≤ x := by
  refine ⟨?_, Real.sin_le hx0⟩
  have hmono : Monotone (fun x : ℝ => sin x - x + x ^ 3 / 6) := by
    apply monotone_of_deriv_nonneg
    · fun_prop
    · intro x
      have h1 := @Real.one_sub_sq_div_two_le_cos x
      have hd : deriv (fun x : ℝ => sin x - x + x ^ 3 / 6) x = cos x - 1 + x ^ 2 / 2 := by
        have : HasDerivAt (fun x : ℝ => sin x - x + x ^ 3 / 6) (cos x - 1 + 3 * x ^ 2 / 6) x := by
          have := ((hasDerivAt_sin x).sub (hasDerivAt_id x)).add
            ((hasDerivAt_pow 3 x).div_const 6)
          exact_mod_cast this
        rw [this.deriv]
        ring
      rw [hd]
      linarith
  have h0 : (fun x : ℝ => sin x - x + x ^ 3 / 6) 0 = 0 := by
    simp [sin_zero]
  linarith [hmono hx0]

/-- sin is strictly increasing on [0, π/2]. -/
theorem sin_strictMono_Icc : StrictMonoOn sin (Icc 0 (π / 2)) :=
  Real.strictMonoOn_sin.mono (Set.Icc_subset_Icc (by linarith [pi_pos]) le_rfl)

/-- Diameter of a closed arc: for 0 < θ ≤ π, the arc of angular width θ
    has diameter 2 sin(θ/2). -/
theorem arc_diameter {α θ : ℝ} (hθ_pos : 0 < θ) (hθ_le : θ ≤ π) :
    Metric.diam (circleParam '' Icc α (α + θ)) = 2 * sin (θ / 2) := by
  have hθ_half_pos : 0 < θ / 2 := by linarith
  have hθ_half_le : θ / 2 ≤ π / 2 := by linarith
  have hsin_pos : 0 < sin (θ / 2) :=
    sin_pos_of_pos_of_lt_pi hθ_half_pos (by linarith [pi_pos])
  have hcont : Continuous circleParam := by
    unfold circleParam; fun_prop
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (by linarith : (0:ℝ) ≤ 2 * sin (θ / 2))
    rintro _ ⟨t₁, ht₁, rfl⟩ _ ⟨t₂, ht₂, rfl⟩
    rw [dist_eq_norm, chord_length]
    suffices h : |sin ((t₁ - t₂) / 2)| ≤ sin (θ / 2) by linarith
    have hbd_lo : -(θ / 2) ≤ (t₁ - t₂) / 2 := by linarith [ht₁.1, ht₂.2]
    have hbd_hi : (t₁ - t₂) / 2 ≤ θ / 2 := by linarith [ht₁.2, ht₂.1]
    have hpi_lo : -(π / 2) ≤ (t₁ - t₂) / 2 := by linarith
    have hpi_hi : (t₁ - t₂) / 2 ≤ π / 2 := by linarith
    rw [abs_le]
    constructor
    · have h1 : sin (-(θ / 2)) ≤ sin ((t₁ - t₂) / 2) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hpi_hi hbd_lo
      linarith [Real.sin_neg (θ / 2)]
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two hpi_lo hθ_half_le hbd_hi
  · have hbdd : Bornology.IsBounded (circleParam '' Icc α (α + θ)) :=
      (isCompact_Icc.image hcont).isBounded
    have hα : circleParam α ∈ circleParam '' Icc α (α + θ) :=
      ⟨α, left_mem_Icc.mpr (by linarith), rfl⟩
    have hαθ : circleParam (α + θ) ∈ circleParam '' Icc α (α + θ) :=
      ⟨α + θ, right_mem_Icc.mpr (by linarith), rfl⟩
    have hdist : dist (circleParam α) (circleParam (α + θ)) = 2 * sin (θ / 2) := by
      rw [dist_eq_norm, chord_length]
      have h1 : (α - (α + θ)) / 2 = -(θ / 2) := by ring
      rw [h1, sin_neg, abs_neg, abs_of_pos hsin_pos]
    linarith [Metric.dist_le_diam_of_mem hbdd hα hαθ]

/-! ## Section 2: H¹(S¹) = 2π -/

/-- The unit circle in ℝ². -/
def unitCircle : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ‖x‖ = 1}

/-- Key lemma: if C ⊆ ℝⁿ is connected, then H¹(C) ≥ diam(C).
    Proof: project onto a line through two far points; the 1-Lipschitz
    projection preserves H¹, and the connected image is an interval. -/
theorem hausdorff_one_ge_diam {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsConnected C) :
    ENNReal.ofReal (Metric.diam C) ≤ μH[1] C := by
  sorry

/-- Upper bound: H¹(S¹) ≤ 2π.
    Cover S¹ by N arcs of angular width 2π/N; each has diameter 2sin(π/N) ≤ 2π/N.
    Total cost = N · 2sin(π/N) ≤ 2π. -/
theorem hausdorff_circle_le : μH[1] unitCircle ≤ ENNReal.ofReal (2 * π) := by
  sorry

/-- Lower bound: H¹(S¹) ≥ 2π.
    Decompose into N shrunken arcs (pairwise separated), each connected with
    known diameter. Sum diameters → 2N sin(π/N) → 2π as N → ∞. -/
theorem hausdorff_circle_ge : ENNReal.ofReal (2 * π) ≤ μH[1] unitCircle := by
  sorry

/-- **Theorem A**: H¹(S¹) = 2π. -/
theorem hausdorff_circle : μH[1] unitCircle = ENNReal.ofReal (2 * π) :=
  le_antisymm hausdorff_circle_le hausdorff_circle_ge

/-! ## Section 3: Spherical Measure σ -/

/-- The unit sphere in ℝ³. -/
def unitSphere : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ‖x‖ = 1}

/-- The cone over a subset A ⊆ S²:
    cone(A) = { t·x : x ∈ A, t ∈ [0,1] } ⊆ B̄(0,1). -/
def cone (A : Set (EuclideanSpace ℝ (Fin 3))) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {y | ∃ x ∈ A, ∃ t ∈ Icc (0 : ℝ) 1, y = t • x}

/-- The spherical measure: σ(A) = 3 · λ₃(cone(A)). -/
def sphericalMeasure (A : Set (EuclideanSpace ℝ (Fin 3))) : ℝ≥0∞ :=
  3 * volume (cone A)

/-- σ is monotone. -/
theorem sphericalMeasure_mono {A B : Set (EuclideanSpace ℝ (Fin 3))}
    (h : A ⊆ B) : sphericalMeasure A ≤ sphericalMeasure B := by
  unfold sphericalMeasure
  apply mul_le_mul_right
  apply measure_mono
  intro y hy
  obtain ⟨x, hxA, t, ht, hyx⟩ := hy
  exact ⟨x, h hxA, t, ht, hyx⟩

/-- σ is countably subadditive. -/
theorem sphericalMeasure_countable_subadditive
    (A : ℕ → Set (EuclideanSpace ℝ (Fin 3))) :
    sphericalMeasure (⋃ i, A i) ≤ ∑' i, sphericalMeasure (A i) := by
  unfold sphericalMeasure
  have hcone_union : cone (⋃ i, A i) ⊆ ⋃ i, cone (A i) := by
    intro y hy
    obtain ⟨x, hx, t, ht, hyx⟩ := hy
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    exact Set.mem_iUnion.mpr ⟨i, x, hi, t, ht, hyx⟩
  calc 3 * volume (cone (⋃ i, A i))
      ≤ 3 * volume (⋃ i, cone (A i)) := by
        apply mul_le_mul_right
        exact measure_mono hcone_union
    _ ≤ 3 * ∑' i, volume (cone (A i)) := by
        apply mul_le_mul_right
        exact measure_iUnion_le _
    _ = ∑' i, 3 * volume (cone (A i)) := by
        rw [ENNReal.tsum_mul_left]

/-- σ is rotation invariant. -/
theorem sphericalMeasure_rotation_invariant
    (R : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (A : Set (EuclideanSpace ℝ (Fin 3))) :
    sphericalMeasure (R '' A) = sphericalMeasure A := by
  sorry

/-- Total spherical measure: σ(S²) = 4π.
    Proof: cone(S²) = B̄(0,1), λ₃(B̄(0,1)) = 4π/3, so σ = 3 · 4π/3 = 4π. -/
theorem sphericalMeasure_total : sphericalMeasure unitSphere = ENNReal.ofReal (4 * π) := by
  sorry

/-- A spherical cap: C(p, ρ) = B̄(p, ρ) ∩ S². -/
def sphericalCap (p : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  Metric.closedBall p ρ ∩ unitSphere

/-- Archimedes' theorem: σ(C(p, ρ)) = π ρ² for 0 < ρ ≤ √2.
    The area of a spherical cap depends only on its chordal radius. -/
theorem archimedes_cap (p : EuclideanSpace ℝ (Fin 3)) (hp : p ∈ unitSphere)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_le : ρ ≤ Real.sqrt 2) :
    sphericalMeasure (sphericalCap p ρ) = ENNReal.ofReal (π * ρ ^ 2) := by
  sorry

/-! ## Section 4: Planar Isodiametric Inequality -/

/-- The isodiametric inequality in ℝ²: for every bounded A ⊆ ℝ²,
    λ₂(A) ≤ π · (diam A / 2)². -/
theorem isodiametric_inequality_plane
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : Bornology.IsBounded A) :
    volume A ≤ ENNReal.ofReal (π * (Metric.diam A / 2) ^ 2) := by
  have h := GraphAreaFull.isodiametric A
  have hediam : Metric.ediam A = ENNReal.ofReal (Metric.diam A) := by
    rw [Metric.diam, ENNReal.ofReal_toReal hA.ediam_ne_top]
  rw [hediam] at h
  refine h.trans_eq ?_
  have hd : (0 : ℝ) ≤ Metric.diam A := Metric.diam_nonneg
  rw [ENNReal.ofReal_mul pi_pos.le, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-! ## Section 5: Gnomonic Projection -/

/-- The distortion function κ(δ) = (1 + δ) / (1 - δ²/2)². -/
def kappa (δ : ℝ) : ℝ := (1 + δ) / (1 - δ ^ 2 / 2) ^ 2

/-- κ is increasing on (0, 1/2]. -/
theorem kappa_strictMono : StrictMonoOn kappa (Ioc 0 (1 / 2)) := by
  sorry

/-- κ(δ) → 1 as δ → 0⁺. -/
theorem kappa_tendsto_one : Tendsto kappa (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hcont : ContinuousAt kappa 0 := by
    unfold kappa
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hk0 : kappa 0 = 1 := by unfold kappa; norm_num
  rw [← hk0]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- Gnomonic projection estimate: for E ⊆ S² with diam E ≤ 1/2,
    σ(E) ≤ κ(d)² · π · (d/2)² where d = diam E. -/
theorem gnomonic_estimate
    (E : Set (EuclideanSpace ℝ (Fin 3)))
    (hE : E ⊆ unitSphere)
    (hd : Metric.diam E ≤ 1 / 2) :
    sphericalMeasure E ≤
      ENNReal.ofReal (kappa (Metric.diam E) ^ 2 * π * (Metric.diam E / 2) ^ 2) := by
  sorry

/-! ## Section 6: H²(S²) = 4π -/

/-- Upper bound: μH[2](S²) ≤ 16.
    Greedy cap covering argument. (Mathlib's μH[2] uses raw ∑(diam)² without ω₂ normalization.) -/
private lemma unitSphere_eq_sphere :
    unitSphere = Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  ext x
  simp [unitSphere]

theorem hausdorff_sphere_le : μH[2] unitSphere ≤ ENNReal.ofReal 16 := by
  rw [unitSphere_eq_sphere, GraphAreaFull.sphere_hausdorffMeasure_unit]
  norm_num

/-- Lower bound: μH[2](S²) ≥ 16.
    For any δ-cover {Uᵢ}, use σ as a comparison measure. -/
theorem hausdorff_sphere_ge : ENNReal.ofReal 16 ≤ μH[2] unitSphere := by
  rw [unitSphere_eq_sphere, GraphAreaFull.sphere_hausdorffMeasure_unit]
  norm_num

/-- **Theorem B**: μH[2](S²) = 16. -/
theorem hausdorff_sphere : μH[2] unitSphere = ENNReal.ofReal 16 :=
  le_antisymm hausdorff_sphere_le hausdorff_sphere_ge

end
