import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import PDE.Basics.Laplace.LaplaceMeanValue

open Set Metric TopologicalSpace MeasureTheory

lemma volume_sphere (x : E) (r : ℝ) : volume (Metric.sphere x r) = 0 := by
  sorry

lemma volume_closed_ball_3d (x₀ : E) (R : ℝ) (hR : 0 < R) :
    volume.real (closedBall x₀ R) = (4 / 3) * Real.pi * R ^ 3 := by
  sorry

lemma integral_ball_polar (R : ℝ) (f : E → ℝ) :
    ∫ y in Metric.ball (0 : E) R, f y =
    ∫ r in Set.Ioo 0 R, ∫ y in sphere (0 : E) r, f y ∂surfaceArea := by
  sorry

lemma integral_Ioo_r_sq (R : ℝ) (hR : 0 < R) : ∫ r in Set.Ioo 0 R, r^2 = R^3 / 3 := by
  have h_le : 0 ≤ R := hR.le
  have h_symm : (Set.Ioo 0 R : Set ℝ) =ᶠ[ae volume] Set.Ioc 0 R := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · have h_diff1 : Set.Ioo 0 R \ Set.Ioc 0 R = ∅ := by
        rw [Set.diff_eq_empty]
        exact Set.Ioo_subset_Ioc_self
      rw [h_diff1]
      exact measure_empty
    · have h_diff2 : Set.Ioc 0 R \ Set.Ioo 0 R ⊆ {R} := by
        intro x hx
        rw [Set.mem_diff, Set.mem_Ioc, Set.mem_Ioo] at hx
        have hx_le : x ≤ R := hx.1.2
        have hx_not_lt : ¬(x < R) := fun h => hx.2 ⟨hx.1.1, h⟩
        have h_eq : x = R := le_antisymm hx_le (not_lt.mp hx_not_lt)
        rw [h_eq]
        exact Set.mem_singleton R
      exact measure_mono_null h_diff2 (measure_singleton R)

  have h_meas_eq : volume.restrict (Set.Ioo 0 R) = volume.restrict (Set.Ioc 0 R) :=
    MeasureTheory.Measure.restrict_congr_set h_symm
  rw [h_meas_eq]

  have h_interval : ∫ r in Set.Ioc 0 R, r^2 = ∫ r in (0:ℝ)..R, r^2 := by
    exact (intervalIntegral.integral_of_le h_le).symm

  rw [h_interval]

  have h_eval : ∫ r in (0:ℝ)..R, r^2 = (R ^ 3 - 0 ^ 3) / 3 := by
    simp_all only [integral_pow, Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      Nat.cast_ofNat]
    ring

  rw [h_eval]
  ring

theorem laplace_mean_value_property_3D_ball
    (u : E → ℝ) (Ω : Set E) (x₀ : E) (R : ℝ)
    (h_open : IsOpen Ω)
    (hR : 0 < R)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (h_harmonic : IsHarmonic u Ω) :
    u x₀ = (1 / ((4/3) * Real.pi * R^3)) * ∫ x in closedBall x₀ R, u x := by

  have h_surface_mvp : ∀ r ∈ Set.Ioo 0 R,
      ∫ x in sphere x₀ r, u x ∂surfaceArea = 4 * Real.pi * r^2 * u x₀ := by
    intro r hr
    have hr_pos : 0 < r := hr.1
    have hr_le : r ≤ R := le_of_lt hr.2

    have h_subset : Metric.closedBall x₀ r ⊆ Ω :=
      Set.Subset.trans (Metric.closedBall_subset_closedBall hr_le) h_closed_ball

    have h_surface := laplace_mean_value_property_3D u Ω x₀ r h_open hr_pos h_subset h_smooth h_harmonic

    have h_denom_ne_zero : 4 * Real.pi * r^2 ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact Real.pi_pos.ne'
      · exact pow_ne_zero 2 hr_pos.ne'

    have h_cancel : (4 * Real.pi * r^2) * (1 / (4 * Real.pi * r^2)) = 1 := by
      field_simp

    calc
      ∫ x in sphere x₀ r, u x ∂surfaceArea
        = 1 * ∫ x in sphere x₀ r, u x ∂surfaceArea := by
          simp
      _ = ((4 * Real.pi * r^2) * (1 / (4 * Real.pi * r^2))) * ∫ x in sphere x₀ r, u x ∂surfaceArea := by
          simp_rw [h_cancel]
      _ = (4 * Real.pi * r^2) * ((1 / (4 * Real.pi * r^2)) * ∫ x in sphere x₀ r, u x ∂surfaceArea) := by
          rw [mul_assoc]
      _ = (4 * Real.pi * r^2) * u x₀ := by
          rw [← h_surface]

  have h_polar_integration :
      ∫ x in closedBall x₀ R, u x = ∫ r in Set.Ioo 0 R, ∫ x in sphere x₀ r, u x ∂surfaceArea := by
    have h_vol_trans : ∫ x in Metric.closedBall x₀ R, u x = ∫ y in Metric.closedBall (0 : E) R, u (x₀ + y) := by
      let e_trans : E ≃ₜ E := Homeomorph.addLeft x₀
      have h_domain : e_trans ⁻¹' (Metric.closedBall x₀ R) = Metric.closedBall (0 : E) R := by
        ext y
        simp [e_trans, Metric.mem_closedBall, dist_eq_norm]
      have h_measure : MeasureTheory.Measure.map e_trans volume = volume := by
        simpa using map_add_left_eq_self _ _
      have h_cov : ∫ x in Metric.closedBall x₀ R, u x ∂(MeasureTheory.Measure.map e_trans volume) =
                   ∫ y in e_trans ⁻¹' (Metric.closedBall x₀ R), u (e_trans y) ∂volume := by
        have hg_emb : MeasurableEmbedding e_trans := e_trans.measurableEmbedding
        change ∫ x, u x ∂((MeasureTheory.Measure.map e_trans volume).restrict (Metric.closedBall x₀ R)) = _
        rw [MeasureTheory.Measure.restrict_map hg_emb.measurable isClosed_closedBall.measurableSet]
        rw [hg_emb.integral_map]
      rw [h_measure, h_domain] at h_cov
      exact h_cov

    have h_surf_trans : ∀ r, ∫ x in sphere x₀ r, u x ∂surfaceArea = ∫ y in sphere (0 : E) r, u (x₀ + y) ∂surfaceArea := by
      intro r'
      let e_trans : E ≃ₜ E := Homeomorph.addLeft x₀
      have h_domain : e_trans ⁻¹' (sphere x₀ r') = sphere (0 : E) r' := by
        ext y
        simp [e_trans]
      have h_measure : MeasureTheory.Measure.map e_trans surfaceArea = surfaceArea := by
        have h_iso : Isometry e_trans := IsometryEquiv.isometry (IsometryEquiv.addLeft x₀)
        erw [Isometry.map_hausdorffMeasure h_iso]
        rw [e_trans.surjective.range_eq, MeasureTheory.Measure.restrict_univ]
        aesop; left; norm_num
      have h_cov : ∫ x in sphere x₀ r', u x ∂(MeasureTheory.Measure.map e_trans surfaceArea) =
                   ∫ y in e_trans ⁻¹' (sphere x₀ r'), u (e_trans y) ∂surfaceArea := by
        have hg_emb : MeasurableEmbedding e_trans := e_trans.measurableEmbedding
        change ∫ x, u x ∂((MeasureTheory.Measure.map e_trans surfaceArea).restrict (sphere x₀ r')) = _
        rw [MeasureTheory.Measure.restrict_map hg_emb.measurable isClosed_sphere.measurableSet]
        rw [hg_emb.integral_map]
      rw [h_measure, h_domain] at h_cov
      exact h_cov

    have h_closed_to_open : ∫ y in Metric.closedBall (0 : E) R, u (x₀ + y) =
                            ∫ y in Metric.ball (0 : E) R, u (x₀ + y) := by
      have h_symm : (Metric.closedBall (0 : E) R : Set E) =ᶠ[ae volume] Metric.ball (0 : E) R := by
        rw [MeasureTheory.ae_eq_set]
        constructor
        · -- Goal 1: volume (closedBall \ ball) = 0
          have h_subset : Metric.closedBall (0 : E) R \ Metric.ball (0 : E) R ⊆ Metric.sphere (0 : E) R := by
            intro y hy
            rw [Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball] at hy
            rw [Metric.mem_sphere]
            exact le_antisymm hy.1 (not_lt.mp hy.2)
          have h_vol_sphere : volume (Metric.sphere (0 : E) R) = 0 := volume_sphere 0 R
          exact measure_mono_null h_subset h_vol_sphere

        · -- Goal 2: volume (ball \ closedBall) = 0
          have h_empty : Metric.ball (0 : E) R \ Metric.closedBall (0 : E) R = ∅ := by
            rw [Set.diff_eq_empty]
            exact Metric.ball_subset_closedBall
          rw [h_empty]
          exact measure_empty

      have h_meas_eq : volume.restrict (Metric.closedBall (0 : E) R) = volume.restrict (Metric.ball (0 : E) R) :=
        MeasureTheory.Measure.restrict_congr_set h_symm

      rw [h_meas_eq]

    have h_polar_open : ∫ y in Metric.ball (0 : E) R, u (x₀ + y) =
                        ∫ r in Set.Ioo 0 R, ∫ y in sphere (0 : E) r, u (x₀ + y) ∂surfaceArea := by
      exact integral_ball_polar R (fun y ↦ u (x₀ + y))

    rw [h_vol_trans]
    rw [h_closed_to_open]
    rw [h_polar_open]
    congr 1
    ext r
    exact (h_surf_trans r).symm



  have h_integral_substitution :
      ∫ r in Set.Ioo 0 R, ∫ x in sphere x₀ r, u x ∂surfaceArea = ∫ r in Set.Ioo 0 R, 4 * Real.pi * r^2 * u x₀ := by
    have h_ae_eq : ∀ᵐ r ∂volume, r ∈ Set.Ioo 0 R →
        ∫ x in sphere x₀ r, u x ∂surfaceArea = 4 * Real.pi * r^2 * u x₀ :=
      Filter.Eventually.of_forall h_surface_mvp
    exact MeasureTheory.setIntegral_congr_ae measurableSet_Ioo h_ae_eq

  have h_1d_integral_eval :
      ∫ r in Set.Ioo 0 R, 4 * Real.pi * r^2 * u x₀ = (4 / 3) * Real.pi * R^3 * u x₀ := by
    calc
      ∫ r in Set.Ioo 0 R, 4 * Real.pi * r^2 * u x₀
        = ∫ r in Set.Ioo 0 R, (4 * Real.pi * u x₀) * r^2 := by
          congr 1
          ext r
          ring
      _ = (4 * Real.pi * u x₀) * ∫ r in Set.Ioo 0 R, r^2 := by
          exact MeasureTheory.integral_const_mul (4 * Real.pi * u x₀) (fun r ↦ r^2)
      _ = (4 * Real.pi * u x₀) * (R^3 / 3) := by
          rw [integral_Ioo_r_sq R hR]
      _ = (4 / 3) * Real.pi * R^3 * u x₀ := by
          ring


  rw [h_polar_integration, h_integral_substitution, h_1d_integral_eval]
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_V_ne_zero : 4 / 3 * Real.pi * R ^ 3 ≠ 0 := by positivity
  field_simp [h_V_ne_zero]

/-- 3. Special Case: Strong Maximum Principle on a Ball
    This represents the proof from your second handwritten page.
    ∫ (u(x₀) - u(z)) dz = 0 ⇒ u(z) = u(x₀).
    Notice we replaced the abstract MVP class with the actual volume integral hypothesis. -/

lemma strong_mp_on_ball (u : E → ℝ) (Ω : Set E) (x₀ : E) (R : ℝ)
    (h_open : IsOpen Ω)
    (hR : 0 < R)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (h_harmonic : IsHarmonic u Ω)
    (h_max : ∀ x ∈ Metric.closedBall x₀ R, u x ≤ u x₀) :
    ∀ x ∈ Metric.closedBall x₀ R, u x = u x₀ := by

  have h_vol_mvp : u x₀ = (1 / ((4 / 3) * Real.pi * R ^ 3)) * ∫ x in Metric.closedBall x₀ R, u x :=
    laplace_mean_value_property_3D_ball u Ω x₀ R h_open hR h_closed_ball h_smooth h_harmonic

  have h_cont : ContinuousOn u (Metric.closedBall x₀ R) := h_smooth.continuousOn.mono h_closed_ball

  have h_diff_nonneg : ∀ x ∈ Metric.closedBall x₀ R, 0 ≤ u x₀ - u x :=
    fun x hx => sub_nonneg.mpr (h_max x hx)

  have h_diff_cont : ContinuousOn (fun x => u x₀ - u x) (Metric.closedBall x₀ R) :=
    continuousOn_const.sub h_cont

  have h_int_const : IntegrableOn (fun _ : E => u x₀) (Metric.closedBall x₀ R) :=
    continuousOn_const.integrableOn_compact (isCompact_closedBall x₀ R)

  have h_int_u : IntegrableOn u (Metric.closedBall x₀ R) :=
    h_cont.integrableOn_compact (isCompact_closedBall x₀ R)

  have h_integral_diff_zero : ∫ x in Metric.closedBall x₀ R, (u x₀ - u x) = 0 := by
    rw [integral_sub h_int_const h_int_u]
    have h_vol_ne : (4 / 3) * Real.pi * R ^ 3 ≠ 0 := ne_of_gt (mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos hR 3))
    have h_const_integral : ∫ _ in Metric.closedBall x₀ R, u x₀ = u x₀ * ((4 / 3) * Real.pi * R ^ 3) := by
      rw [setIntegral_const, volume_closed_ball_3d x₀ R hR, smul_eq_mul, mul_comm]
    rw [h_const_integral]
    have h_key : u x₀ * ((4 / 3) * Real.pi * R ^ 3) = ∫ x in Metric.closedBall x₀ R, u x := by
      rw [h_vol_mvp]
      field_simp [h_vol_ne]
    linarith

  have h_diff_eq_zero_interior : ∀ x ∈ Metric.ball x₀ R, u x₀ - u x = 0 := by
    have h_diff_integrable : IntegrableOn (fun x => u x₀ - u x) (Metric.closedBall x₀ R) := Integrable.sub h_int_const h_int_u
    have h_ae_eq_zero : ∀ᵐ x ∂(volume.restrict (Metric.closedBall x₀ R)), u x₀ - u x = 0 := by
      have h_meas : MeasurableSet (Metric.closedBall x₀ R) := isClosed_closedBall.measurableSet
      have h_ae_nonneg : ∀ᵐ x ∂(volume.restrict (Metric.closedBall x₀ R)), 0 ≤ u x₀ - u x := by
        filter_upwards [ae_restrict_mem h_meas] with x hx
        exact h_diff_nonneg x hx
      exact (integral_eq_zero_iff_of_nonneg_ae h_ae_nonneg h_diff_integrable).mp h_integral_diff_zero

    intro x hx
    have h_interior_subset : x ∈ Metric.closedBall x₀ R := Metric.ball_subset_closedBall hx
    by_contra h_neq
    have h_pos : 0 < u x₀ - u x := lt_of_le_of_ne (h_diff_nonneg x h_interior_subset) (fun h => h_neq h.symm)

    have h_subball_integral_pos : ∃ (r' : ℝ), 0 < r' ∧ Metric.closedBall x r' ⊆ Metric.closedBall x₀ R ∧ 0 < ∫ y in Metric.closedBall x r', (u x₀ - u y) := by
      have h_dist_pos : 0 < R - dist x x₀ := sub_pos.mpr hx
      have h_exists_delta : ∃ δ > 0, ∀ y ∈ Metric.closedBall x₀ R, dist x y ≤ δ → (u x₀ - u x) / 2 ≤ u x₀ - u y := by
        have h_eps_pos : 0 < (u x₀ - u x) / 2 := by linarith
        obtain ⟨δ, hδ_pos, hδ_bound⟩ := Metric.continuousOn_iff.mp h_diff_cont x h_interior_subset ((u x₀ - u x) / 2) h_eps_pos
        use δ / 2
        refine ⟨by linarith, ?_⟩
        intro y hy h_dist
        have h_bound := hδ_bound y hy (by rw [dist_comm]; linarith)
        rw [Real.dist_eq] at h_bound
        have h_abs := abs_lt.mp h_bound
        linarith

      obtain ⟨δ, hδ_pos, hδ_bound⟩ := h_exists_delta
      let r' := min δ (R - dist x x₀) / 2
      have hr'_pos : 0 < r' := by positivity
      have h_subset : Metric.closedBall x r' ⊆ Metric.closedBall x₀ R := by
        intro y hy
        rw [Metric.mem_closedBall] at hy ⊢
        have h_min : min δ (R - dist x x₀) ≤ R - dist x x₀ := min_le_right δ (R - dist x x₀)
        have h_tri := dist_triangle x₀ x y
        have h_symm1 : dist x₀ x = dist x x₀ := dist_comm x₀ x
        have h_symm2 : dist y x₀ = dist x₀ y := dist_comm y x₀
        have h_symm3 : dist x y = dist y x := dist_comm x y
        have hx_ball : dist x₀ x < R := by simpa [h_symm1] using hx
        have h_r_def : r' = min δ (R - dist x x₀) / 2 := rfl
        linarith

      have h_int_pos : 0 < ∫ y in Metric.closedBall x r', (u x₀ - u y) := by
        have h_pointwise_bound : ∀ y ∈ Metric.closedBall x r', (u x₀ - u x) / 2 ≤ u x₀ - u y := by
          intro y hy
          have hy_R : y ∈ Metric.closedBall x₀ R := h_subset hy
          rw [Metric.mem_closedBall] at hy
          have h_dist_symm : dist x y = dist y x := dist_comm x y
          have h_r_def : r' = min δ (R - dist x x₀) / 2 := rfl
          have h_min_le : min δ (R - dist x x₀) ≤ δ := min_le_left δ (R - dist x x₀)
          exact hδ_bound y hy_R (by linarith)

        have h_sub_integrable : IntegrableOn (fun y => u x₀ - u y) (Metric.closedBall x r') := IntegrableOn.mono_set h_diff_integrable h_subset
        have h_const_integral_pos : 0 < ∫ y in Metric.closedBall x r', (u x₀ - u x) / 2 := by
          rw [setIntegral_const, volume_closed_ball_3d x r' hr'_pos, smul_eq_mul]
          have h_vol_pos : 0 < (4 / 3) * Real.pi * r' ^ 3 := mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos hr'_pos 3)
          exact mul_pos h_vol_pos (by linarith)

        have h_integral_bound : ∫ y in Metric.closedBall x r', (u x₀ - u x) / 2 ≤ ∫ y in Metric.closedBall x r', (u x₀ - u y) := by
          have h_const_integrable : IntegrableOn (fun _ => (u x₀ - u x) / 2) (Metric.closedBall x r') :=
            continuousOn_const.integrableOn_compact (isCompact_closedBall x r')
          exact setIntegral_mono_on h_const_integrable h_sub_integrable (isClosed_closedBall.measurableSet) h_pointwise_bound

        exact lt_of_lt_of_le h_const_integral_pos h_integral_bound

      exact ⟨r', hr'_pos, h_subset, h_int_pos⟩

    have h_total_integral_pos : 0 < ∫ y in Metric.closedBall x₀ R, (u x₀ - u y) := by
      obtain ⟨r', hr'_pos, h_subset, h_int_pos⟩ := h_subball_integral_pos
      have h_meas : MeasurableSet (Metric.closedBall x₀ R) := isClosed_closedBall.measurableSet
      have h_ae_nonneg : 0 ≤ᵐ[volume.restrict (Metric.closedBall x₀ R)] fun y => u x₀ - u y := by
        filter_upwards [ae_restrict_mem h_meas] with y hy
        exact h_diff_nonneg y hy
      have h_integral_le : ∫ y in Metric.closedBall x r', (u x₀ - u y) ≤ ∫ y in Metric.closedBall x₀ R, (u x₀ - u y) :=
        setIntegral_mono_set h_diff_integrable h_ae_nonneg (Filter.Eventually.of_forall h_subset)
      exact lt_of_lt_of_le h_int_pos h_integral_le

    exact ne_of_gt h_total_integral_pos h_integral_diff_zero

  have h_diff_eq_zero : ∀ x ∈ Metric.closedBall x₀ R, u x₀ - u x = 0 := by
    intro x hx
    rcases eq_or_lt_of_le (Metric.mem_closedBall.mp hx) with h_eq | h_lt
    · have h_seq : ∃ (s : ℕ → E), (∀ n, s n ∈ Metric.ball x₀ R) ∧ Filter.Tendsto s Filter.atTop (nhds x) := by
        use fun n => x₀ + (1 - 1 / (n + 2 : ℝ)) • (x - x₀)
        constructor
        · intro n
          rw [Metric.mem_ball, dist_eq_norm]
          have h_cancel : x₀ + (1 - 1 / (n + 2 : ℝ)) • (x - x₀) - x₀ = (1 - 1 / (n + 2 : ℝ)) • (x - x₀) := by abel
          rw [h_cancel, norm_smul, Real.norm_eq_abs]
          have h_norm_x : ‖x - x₀‖ = R := by rw [← dist_eq_norm]; exact h_eq
          rw [h_norm_x]
          have h_n_pos : (0 : ℝ) < n + 2 := by positivity
          have h_abs : |1 - 1 / (n + 2 : ℝ)| = 1 - 1 / (n + 2 : ℝ) := by
            apply abs_of_nonneg
            have h_frac : 1 / (n + 2 : ℝ) ≤ 1 := by rw [div_le_iff₀ h_n_pos]; linarith
            linarith
          rw [h_abs]
          have h_frac_pos : (0 : ℝ) < 1 / (n + 2) := by positivity
          nlinarith [hR]

        · have h_target : nhds x = nhds (x₀ + (1 : ℝ) • (x - x₀)) := by congr 1; rw [one_smul]; abel
          rw [h_target]
          have h_lim_real : Filter.Tendsto (fun (n : ℕ) ↦ 1 - 1 / ((n : ℝ) + 2)) Filter.atTop (nhds 1) := by
            rw [show (nhds 1 : Filter ℝ) = nhds (1 - 0) by rw [sub_zero]]
            have h_frac_lim : Filter.Tendsto (fun (n : ℕ) ↦ 1 / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
              have h_inv_eq : (fun (n : ℕ) ↦ 1 / ((n : ℝ) + 2)) = (fun (n : ℕ) ↦ ((n : ℝ) + 2)⁻¹) := by ext n; exact one_div ((n : ℝ) + 2)
              rw [h_inv_eq]
              have h_atTop : Filter.Tendsto (fun (n : ℕ) ↦ (n : ℝ) + 2) Filter.atTop Filter.atTop := by
                refine Filter.tendsto_atTop_mono ?_ tendsto_natCast_atTop_atTop
                intro n; linarith
              exact tendsto_inv_atTop_zero.comp h_atTop
            exact Filter.Tendsto.sub tendsto_const_nhds h_frac_lim
          exact Filter.Tendsto.add tendsto_const_nhds (Filter.Tendsto.smul h_lim_real tendsto_const_nhds)

      obtain ⟨s, hs_ball, hs_tendsto⟩ := h_seq
      have h_seq_eq : (fun n => u x₀ - u (s n)) = (fun n => 0) := by
        ext n; exact h_diff_eq_zero_interior (s n) (hs_ball n)
      have h_tendsto_image : Filter.Tendsto (fun n => u x₀ - u (s n)) Filter.atTop (nhds (u x₀ - u x)) := by
        have h_tendsto_within : Filter.Tendsto s Filter.atTop (nhdsWithin x (Metric.closedBall x₀ R)) :=
          tendsto_nhdsWithin_iff.mpr ⟨hs_tendsto, Filter.Eventually.of_forall (fun n => Metric.ball_subset_closedBall (hs_ball n))⟩
        change Filter.Tendsto ((fun y => u x₀ - u y) ∘ s) Filter.atTop (nhds (u x₀ - u x))
        exact Filter.Tendsto.comp (h_diff_cont x hx) h_tendsto_within
      have h_tendsto_const : Filter.Tendsto (fun n => u x₀ - u (s n)) Filter.atTop (nhds 0) := by
        rw [h_seq_eq]; exact tendsto_const_nhds
      exact tendsto_nhds_unique h_tendsto_image h_tendsto_const
    · exact h_diff_eq_zero_interior x (Metric.mem_ball.mpr h_lt)

  intro x hx
  exact (sub_eq_zero.mp (h_diff_eq_zero x hx)).symm

/-- 4. Main Theorem: The Maximum Principle (Theorem 8.2)
    "Let u be a harmonic function on a bounded domain Ω which is continuous up
    to the boundary... If u attains its maximum... at a point in Ω, then u must
    be identically constant inside Ω." -/
theorem maximum_principle {u : E → ℝ} {Ω : Set E}
    (h_open : IsOpen Ω)
    (h_connected : IsConnected Ω)
    (h_harmonic : IsHarmonic u Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (h_cont : ContinuousOn u (closure Ω))
    (x₀ : E) (hx₀ : x₀ ∈ Ω)
    (h_max : ∀ x ∈ closure Ω, u x ≤ u x₀) :
    ∀ x ∈ Ω, u x = u x₀ := by

  let M := u x₀
  let S := {x ∈ Ω | u x = M}

  have h_cont_subtype : Continuous (u ∘ Subtype.val : Ω → ℝ) :=
    continuousOn_iff_continuous_restrict.mp (h_cont.mono subset_closure)

  have h_closed_in : IsClosed (Subtype.val ⁻¹' S : Set Ω) := by
    have h_eq : (Subtype.val ⁻¹' S : Set Ω) = (u ∘ Subtype.val) ⁻¹' {M} := by
      ext ⟨x, hx⟩
      simp [S, M]
    exact h_eq ▸ IsClosed.preimage h_cont_subtype isClosed_singleton

  have h_ball_subset : ∀ x ∈ S, ∃ R > 0, Metric.ball x R ⊆ S := by
    rintro x ⟨hx_mem, hx_eq⟩
    rcases Metric.isOpen_iff.mp h_open x hx_mem with ⟨ε, hε, h_ball⟩
    let R := ε / 2
    have hR_pos : 0 < R := by positivity
    have hR_lt : R < ε := by simp_all only [preimage_setOf_eq, Subtype.coe_prop, true_and, gt_iff_lt,
      div_pos_iff_of_pos_left, Nat.ofNat_pos, half_lt_self_iff, S, M, R]
    have h_closed_ball : Metric.closedBall x R ⊆ Ω := by
      intro y hy
      exact h_ball (lt_of_le_of_lt hy hR_lt)
    have h_max_local : ∀ y ∈ Metric.closedBall x R, u y ≤ u x := by
      intro y hy
      rw [hx_eq]
      exact h_max y (subset_closure (h_closed_ball hy))
    have h_const := strong_mp_on_ball u Ω x R h_open hR_pos h_closed_ball h_smooth h_harmonic h_max_local
    exact ⟨R, hR_pos, fun y hy => ⟨h_closed_ball (Metric.ball_subset_closedBall hy), Eq.trans (h_const y (Metric.ball_subset_closedBall hy)) hx_eq⟩⟩

  have h_open_S : IsOpen S := Metric.isOpen_iff.mpr h_ball_subset

  have h_clopen : IsClopen (Subtype.val ⁻¹' S : Set Ω) :=
    ⟨h_closed_in, h_open_S.preimage continuous_subtype_val⟩

  haveI h_subtype_connected : PreconnectedSpace Ω :=
    isPreconnected_iff_preconnectedSpace.mp h_connected.isPreconnected

  have h_univ : (Subtype.val ⁻¹' S : Set Ω) = Set.univ := by
    rcases isClopen_iff.mp h_clopen with h_empty | h_univ_eq
    · exfalso
      exact Set.notMem_empty (⟨x₀, hx₀⟩ : Ω) (h_empty ▸ ⟨hx₀, rfl⟩)
    · exact h_univ_eq

  intro x hx
  have hx_univ : (⟨x, hx⟩ : Ω) ∈ (Set.univ : Set Ω) := Set.mem_univ _
  exact (h_univ.symm ▸ hx_univ).2

lemma isHarmonic_sub {u₁ u₂ : E → ℝ} {Ω : Set E}
    (h_open : IsOpen Ω)
    (h_smooth₁ : ContDiffOn ℝ 2 u₁ Ω) (h_smooth₂ : ContDiffOn ℝ 2 u₂ Ω)
    (h₁ : IsHarmonic u₁ Ω) (h₂ : IsHarmonic u₂ Ω) :
    IsHarmonic (u₁ - u₂) Ω := by
  intro x hx
  have h_nhds : Ω ∈ nhds x := h_open.mem_nhds hx

  have h_contDiffAt₁ : ContDiffAt ℝ 2 u₁ x := h_smooth₁.contDiffAt h_nhds
  have h_contDiffAt_fderiv₁ : ContDiffAt ℝ 1 (fderiv ℝ u₁) x := h_contDiffAt₁.fderiv_right le_rfl
  have h_fderiv_diff₁ : DifferentiableAt ℝ (fderiv ℝ u₁) x := h_contDiffAt_fderiv₁.differentiableAt (by norm_num)
  have h_diff₁ : DifferentiableAt ℝ (gradient u₁) x := by
    unfold gradient
    exact (ContinuousLinearEquiv.differentiableAt ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv)).comp x h_fderiv_diff₁

  have h_contDiffAt₂ : ContDiffAt ℝ 2 u₂ x := h_smooth₂.contDiffAt h_nhds
  have h_contDiffAt_fderiv₂ : ContDiffAt ℝ 1 (fderiv ℝ u₂) x := h_contDiffAt₂.fderiv_right le_rfl
  have h_fderiv_diff₂ : DifferentiableAt ℝ (fderiv ℝ u₂) x := h_contDiffAt_fderiv₂.differentiableAt (by norm_num)
  have h_diff₂ : DifferentiableAt ℝ (gradient u₂) x := by
    unfold gradient
    exact (ContinuousLinearEquiv.differentiableAt ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv)).comp x h_fderiv_diff₂

  have h_grad_eq_on : Set.EqOn (gradient (u₁ - u₂)) (gradient u₁ - gradient u₂) Ω := by
    intro y hy
    have hd1 : DifferentiableAt ℝ u₁ y := (h_smooth₁.differentiableOn (by norm_num) y hy).differentiableAt (h_open.mem_nhds hy)
    have hd2 : DifferentiableAt ℝ u₂ y := (h_smooth₂.differentiableOn (by norm_num) y hy).differentiableAt (h_open.mem_nhds hy)
    unfold gradient
    rw [fderiv_sub hd1 hd2]
    exact map_sub _ _ _

  have h_eventually_eq : gradient (u₁ - u₂) =ᶠ[nhds x] (gradient u₁ - gradient u₂) :=
    h_grad_eq_on.eventuallyEq_of_mem h_nhds

  have h1x := h₁ x hx
  have h2x := h₂ x hx
  unfold laplacian div_field at h1x h2x ⊢

  rw [h_eventually_eq.fderiv_eq, fderiv_sub h_diff₁ h_diff₂]
  push_cast
  rw [LinearMap.map_sub, h1x, h2x]
  exact sub_zero 0

lemma isHarmonic_neg {u : E → ℝ} {Ω : Set E}
    (h_open : IsOpen Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (h_harmonic : IsHarmonic u Ω) :
    IsHarmonic (fun x => -u x) Ω := by
  intro x hx
  have h_nhds : Ω ∈ nhds x := h_open.mem_nhds hx

  have h_grad_eq : gradient (fun y => -u y) =ᶠ[nhds x] fun y => - gradient u y := by
    apply Filter.eventuallyEq_of_mem h_nhds
    intro y hy
    have hd : DifferentiableAt ℝ u y := (h_smooth.differentiableOn (by norm_num) y hy).differentiableAt (h_open.mem_nhds hy)
    unfold gradient
    change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (-u) y) = - (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u y)
    rw [fderiv_neg]
    exact map_neg _ _

  have h_contDiffAt : ContDiffAt ℝ 2 u x := h_smooth.contDiffAt h_nhds
  have h_contDiffAt_fderiv : ContDiffAt ℝ 1 (fderiv ℝ u) x := h_contDiffAt.fderiv_right le_rfl
  have h_fderiv_diff : DifferentiableAt ℝ (fderiv ℝ u) x := h_contDiffAt_fderiv.differentiableAt (by norm_num)
  have h_diff : DifferentiableAt ℝ (gradient u) x := by
    unfold gradient
    exact (ContinuousLinearEquiv.differentiableAt ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv)).comp x h_fderiv_diff

  have h_lap : laplacian u x = 0 := h_harmonic x hx
  unfold laplacian div_field at h_lap ⊢

  rw [h_grad_eq.fderiv_eq]
  change (LinearMap.trace ℝ E) ↑(fderiv ℝ (- gradient u) x) = 0
  rw [fderiv_neg]
  change (LinearMap.trace ℝ E) (- ↑(fderiv ℝ (gradient u) x)) = 0
  rw [LinearMap.map_neg, h_lap, neg_zero]

lemma minimum_principle {u : E → ℝ} {Ω : Set E}
    (h_open : IsOpen Ω)
    (h_connected : IsConnected Ω)
    (h_harmonic : IsHarmonic u Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (h_cont : ContinuousOn u (closure Ω))
    (x₀ : E) (hx₀ : x₀ ∈ Ω)
    (h_min : ∀ x ∈ closure Ω, u x₀ ≤ u x) :
    ∀ x ∈ Ω, u x = u x₀ := by

  let w : E → ℝ := fun x => - u x

  have h_harmonic_w : IsHarmonic w Ω :=
    isHarmonic_neg h_open h_smooth h_harmonic

  have h_smooth_w : ContDiffOn ℝ 2 w Ω :=
    h_smooth.neg

  have h_cont_w : ContinuousOn w (closure Ω) :=
    h_cont.neg

  have h_max_w : ∀ x ∈ closure Ω, w x ≤ w x₀ := by
    intro x hx
    have h_le := h_min x hx
    change - u x ≤ - u x₀
    linarith

  have h_const_w : ∀ x ∈ Ω, w x = w x₀ :=
    maximum_principle h_open h_connected h_harmonic_w h_smooth_w h_cont_w x₀ hx₀ h_max_w

  intro x hx
  have h_w_eq := h_const_w x hx
  change - u x = - u x₀ at h_w_eq
  linarith

lemma mem_of_mem_closure_not_mem_frontier {s : Set E}
    (h_open : IsOpen s) {x : E} (hx_clos : x ∈ closure s) (hx_front : x ∉ frontier s) :
    x ∈ s := by
  have h_diff : x ∈ closure s \ frontier s := ⟨hx_clos, hx_front⟩
  rw [closure_diff_frontier s] at h_diff
  rwa [h_open.interior_eq] at h_diff

lemma frontier_nonempty_of_bounded_open_nonempty {s : Set E}
    (h_open : IsOpen s) (h_bounded : Bornology.IsBounded s) (h_nonempty : s.Nonempty) :
    (frontier s).Nonempty := by
  by_contra h_empty
  rw [Set.not_nonempty_iff_eq_empty] at h_empty

  have h_closed : IsClosed s := by
    have h_clos : closure s = interior s ∪ frontier s := closure_eq_interior_union_frontier s
    rw [h_empty, Set.union_empty, h_open.interior_eq] at h_clos
    exact isClosed_of_closure_subset h_clos.subset

  have h_clopen : IsClopen s := ⟨h_closed, h_open⟩

  have h_univ : s = Set.univ := by
    rcases isClopen_iff.mp h_clopen with h_s_empty | h_s_univ
    · exfalso
      exact Set.nonempty_iff_ne_empty.mp h_nonempty h_s_empty
    · exact h_s_univ

  have h_bounded_univ : Bornology.IsBounded (Set.univ : Set E) := by
    rw [← h_univ]
    exact h_bounded

  have h_not_bounded_univ : ¬ Bornology.IsBounded (Set.univ : Set E) := by
    exact NormedSpace.unbounded_univ ℝ E

  exact h_not_bounded_univ h_bounded_univ

lemma constant_of_continuous_closure {u : E → ℝ} {Ω : Set E}
    (h_cont : ContinuousOn u (closure Ω)) {c : ℝ} (h_const : ∀ x ∈ Ω, u x = c)
    {y : E} (hy : y ∈ closure Ω) : u y = c := by
  have h1 : Filter.Tendsto u (nhdsWithin y Ω) (nhds (u y)) :=
    (h_cont y hy).mono subset_closure

  have h_eq : u =ᶠ[nhdsWithin y Ω] (fun _ => c) :=
    Filter.eventuallyEq_of_mem self_mem_nhdsWithin h_const

  have h2 : Filter.Tendsto u (nhdsWithin y Ω) (nhds c) :=
    Filter.Tendsto.congr' h_eq.symm tendsto_const_nhds

  haveI : Filter.NeBot (nhdsWithin y Ω) := mem_closure_iff_nhdsWithin_neBot.mp hy

  exact tendsto_nhds_unique h1 h2

theorem dirichlet_uniqueness {u₁ u₂ : E → ℝ} {Ω : Set E} {g : E → ℝ}
    (h_open : IsOpen Ω)
    (h_connected : IsConnected Ω)
    (h_bounded : Bornology.IsBounded Ω)
    (h_harmonic₁ : IsHarmonic u₁ Ω)
    (h_harmonic₂ : IsHarmonic u₂ Ω)
    (h_smooth₁ : ContDiffOn ℝ 2 u₁ Ω)
    (h_smooth₂ : ContDiffOn ℝ 2 u₂ Ω)
    (h_cont₁ : ContinuousOn u₁ (closure Ω))
    (h_cont₂ : ContinuousOn u₂ (closure Ω))
    (h_bound₁ : ∀ x ∈ frontier Ω, u₁ x = g x)
    (h_bound₂ : ∀ x ∈ frontier Ω, u₂ x = g x) :
    ∀ x ∈ closure Ω, u₁ x = u₂ x := by
  let v : E → ℝ := fun x => u₁ x - u₂ x

  have h_smooth_v : ContDiffOn ℝ 2 v Ω := h_smooth₁.sub h_smooth₂
  have h_cont_v : ContinuousOn v (closure Ω) := h_cont₁.sub h_cont₂
  have h_harmonic_v : IsHarmonic v Ω := isHarmonic_sub h_open h_smooth₁ h_smooth₂ h_harmonic₁ h_harmonic₂

  have h_boundary_v : ∀ x ∈ frontier Ω, v x = 0 := by
    intro x hx
    change u₁ x - u₂ x = 0
    rw [h_bound₁ x hx, h_bound₂ x hx, sub_self]

  have h_compact_closure : IsCompact (closure Ω) := Metric.isCompact_of_isClosed_isBounded isClosed_closure h_bounded.closure
  have h_nonempty_closure : (closure Ω).Nonempty := h_connected.nonempty.closure

  have h_max_exists : ∃ x_max ∈ closure Ω, ∀ x ∈ closure Ω, v x ≤ v x_max :=
    IsCompact.exists_isMaxOn h_compact_closure h_nonempty_closure h_cont_v

  have h_min_exists : ∃ x_min ∈ closure Ω, ∀ x ∈ closure Ω, v x_min ≤ v x :=
    IsCompact.exists_isMinOn h_compact_closure h_nonempty_closure h_cont_v

  have h_v_le_zero : ∀ x ∈ closure Ω, v x ≤ 0 := by
    rcases h_max_exists with ⟨x_max, hx_max_mem, h_max_prop⟩
    by_cases h_front : x_max ∈ frontier Ω
    · intro x hx
      have h_le := h_max_prop x hx
      rw [h_boundary_v x_max h_front] at h_le
      exact h_le
    · have h_in_omega : x_max ∈ Ω := mem_of_mem_closure_not_mem_frontier h_open hx_max_mem h_front
      have h_const : ∀ x ∈ Ω, v x = v x_max := maximum_principle h_open h_connected h_harmonic_v h_smooth_v h_cont_v x_max h_in_omega h_max_prop
      rcases frontier_nonempty_of_bounded_open_nonempty h_open h_bounded ⟨x_max, h_in_omega⟩ with ⟨x_front, hx_front⟩
      have h_max_zero : v x_max = 0 := by
        have h_val_front := constant_of_continuous_closure h_cont_v h_const (frontier_subset_closure hx_front)
        have h_bnd := h_boundary_v x_front hx_front
        linarith
      intro x hx
      have h_le := h_max_prop x hx
      rw [h_max_zero] at h_le
      exact h_le

  have h_v_ge_zero : ∀ x ∈ closure Ω, 0 ≤ v x := by
    rcases h_min_exists with ⟨x_min, hx_min_mem, h_min_prop⟩
    by_cases h_front : x_min ∈ frontier Ω
    · intro x hx
      have h_ge := h_min_prop x hx
      rw [h_boundary_v x_min h_front] at h_ge
      exact h_ge
    · have h_in_omega : x_min ∈ Ω := mem_of_mem_closure_not_mem_frontier h_open hx_min_mem h_front
      have h_const : ∀ x ∈ Ω, v x = v x_min := minimum_principle h_open h_connected h_harmonic_v h_smooth_v h_cont_v x_min h_in_omega h_min_prop
      rcases frontier_nonempty_of_bounded_open_nonempty h_open h_bounded ⟨x_min, h_in_omega⟩ with ⟨x_front, hx_front⟩
      have h_min_zero : v x_min = 0 := by
        have h_val_front := constant_of_continuous_closure h_cont_v h_const (frontier_subset_closure hx_front)
        have h_bnd := h_boundary_v x_front hx_front
        linarith
      intro x hx
      have h_ge := h_min_prop x hx
      rw [h_min_zero] at h_ge
      exact h_ge

  intro x hx
  have h_v_eq_zero : v x = 0 := le_antisymm (h_v_le_zero x hx) (h_v_ge_zero x hx)
  exact sub_eq_zero.mp h_v_eq_zero

theorem harmonic_bounds {u : E → ℝ} {Ω : Set E} {m M : ℝ}
    (h_open : IsOpen Ω)
    (h_connected : IsConnected Ω)
    (h_bounded : Bornology.IsBounded Ω)
    (h_harmonic : IsHarmonic u Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (h_cont : ContinuousOn u (closure Ω))
    (h_bound_min : ∀ x ∈ frontier Ω, m ≤ u x)
    (h_bound_max : ∀ x ∈ frontier Ω, u x ≤ M) :
    ∀ x ∈ closure Ω, m ≤ u x ∧ u x ≤ M := by

  have h_compact_closure : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure h_bounded.closure

  have h_nonempty_closure : (closure Ω).Nonempty :=
    h_connected.nonempty.closure

  have h_max_exists : ∃ x_max ∈ closure Ω, ∀ x ∈ closure Ω, u x ≤ u x_max :=
    IsCompact.exists_isMaxOn h_compact_closure h_nonempty_closure h_cont

  have h_min_exists : ∃ x_min ∈ closure Ω, ∀ x ∈ closure Ω, u x_min ≤ u x :=
    IsCompact.exists_isMinOn h_compact_closure h_nonempty_closure h_cont

  have h_upper : ∀ x ∈ closure Ω, u x ≤ M := by
    rcases h_max_exists with ⟨x_max, hx_max_mem, h_max_prop⟩
    by_cases h_front : x_max ∈ frontier Ω
    · intro x hx
      have h_le := h_max_prop x hx
      have h_max_bnd := h_bound_max x_max h_front
      linarith
    · have h_in_omega : x_max ∈ Ω := mem_of_mem_closure_not_mem_frontier h_open hx_max_mem h_front
      have h_const : ∀ x ∈ Ω, u x = u x_max := maximum_principle h_open h_connected h_harmonic h_smooth h_cont x_max h_in_omega h_max_prop
      rcases frontier_nonempty_of_bounded_open_nonempty h_open h_bounded ⟨x_max, h_in_omega⟩ with ⟨x_front, hx_front⟩
      have h_max_val : u x_max ≤ M := by
        have h_val_front := constant_of_continuous_closure h_cont h_const (frontier_subset_closure hx_front)
        have h_bnd := h_bound_max x_front hx_front
        linarith
      intro x hx
      have h_le := h_max_prop x hx
      linarith

  have h_lower : ∀ x ∈ closure Ω, m ≤ u x := by
    rcases h_min_exists with ⟨x_min, hx_min_mem, h_min_prop⟩
    by_cases h_front : x_min ∈ frontier Ω
    · intro x hx
      have h_ge := h_min_prop x hx
      have h_min_bnd := h_bound_min x_min h_front
      linarith
    · have h_in_omega : x_min ∈ Ω := mem_of_mem_closure_not_mem_frontier h_open hx_min_mem h_front
      have h_const : ∀ x ∈ Ω, u x = u x_min := minimum_principle h_open h_connected h_harmonic h_smooth h_cont x_min h_in_omega h_min_prop
      rcases frontier_nonempty_of_bounded_open_nonempty h_open h_bounded ⟨x_min, h_in_omega⟩ with ⟨x_front, hx_front⟩
      have h_min_val : m ≤ u x_min := by
        have h_val_front := constant_of_continuous_closure h_cont h_const (frontier_subset_closure hx_front)
        have h_bnd := h_bound_min x_front hx_front
        linarith
      intro x hx
      have h_ge := h_min_prop x hx
      linarith

  intro x hx
  exact ⟨h_lower x hx, h_upper x hx⟩

theorem dirichlet_stability {u₁ u₂ : E → ℝ} {Ω : Set E} {g₁ g₂ : E → ℝ}
    (h_open : IsOpen Ω)
    (h_connected : IsConnected Ω)
    (h_bounded : Bornology.IsBounded Ω)
    (h_harmonic₁ : IsHarmonic u₁ Ω)
    (h_harmonic₂ : IsHarmonic u₂ Ω)
    (h_smooth₁ : ContDiffOn ℝ 2 u₁ Ω)
    (h_smooth₂ : ContDiffOn ℝ 2 u₂ Ω)
    (h_cont₁ : ContinuousOn u₁ (closure Ω))
    (h_cont₂ : ContinuousOn u₂ (closure Ω))
    (h_bound₁ : ∀ x ∈ frontier Ω, u₁ x = g₁ x)
    (h_bound₂ : ∀ x ∈ frontier Ω, u₂ x = g₂ x) :
    ∃ y_max ∈ frontier Ω, ∀ x ∈ closure Ω,
      |u₁ x - u₂ x| ≤ |g₁ y_max - g₂ y_max| := by

  let v : E → ℝ := fun x => u₁ x - u₂ x

  have h_harmonic_v : IsHarmonic v Ω :=
    isHarmonic_sub h_open h_smooth₁ h_smooth₂ h_harmonic₁ h_harmonic₂

  have h_smooth_v : ContDiffOn ℝ 2 v Ω := h_smooth₁.sub h_smooth₂
  have h_cont_v : ContinuousOn v (closure Ω) := h_cont₁.sub h_cont₂

  have h_boundary_v : ∀ x ∈ frontier Ω, v x = g₁ x - g₂ x := by
    intro x hx
    show u₁ x - u₂ x = g₁ x - g₂ x
    rw [h_bound₁ x hx, h_bound₂ x hx]

  -- 1. Setup the frontier as a compact, non-empty set for the extremum
  have h_compact_front : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier (h_bounded.closure.subset frontier_subset_closure)

  have h_nonempty_front : (frontier Ω).Nonempty :=
    frontier_nonempty_of_bounded_open_nonempty h_open h_bounded h_connected.nonempty

  -- 2. Find the point on the boundary where |v| is maximized
  -- Find the point on the boundary where |v| is maximized
  have h_exists_max : ∃ y_max ∈ frontier Ω, ∀ y ∈ frontier Ω, |v y| ≤ |v y_max| :=
    IsCompact.exists_isMaxOn h_compact_front h_nonempty_front
      (h_cont_v.abs.mono frontier_subset_closure)

  rcases h_exists_max with ⟨y_max, hy_max_mem, h_abs_max⟩
  let M := |v y_max|

  -- 3. Define the bounds for harmonic_bounds
  have h_bound_max : ∀ y ∈ frontier Ω, v y ≤ M := by
    intro y hy
    exact (le_abs_self (v y)).trans (h_abs_max y hy)

  have h_bound_min : ∀ y ∈ frontier Ω, -M ≤ v y := by
    intro y hy
    rw [neg_le_iff_add_nonneg]
    have : -|v y| ≤ v y := neg_abs_le (v y)
    have : -M ≤ -|v y| := neg_le_neg (h_abs_max y hy)
    linarith

  -- 4. Apply the previous corollary (harmonic_bounds)
  have h_bounds := harmonic_bounds h_open h_connected h_bounded
                   h_harmonic_v h_smooth_v h_cont_v h_bound_min h_bound_max

  -- 5. Final assembly
  use y_max, hy_max_mem
  intro x hx
  specialize h_bounds x hx
  rw [abs_le]

  simp_all only [implies_true, tsub_le_iff_right, neg_le_sub_iff_le_add, and_self, v, M]
