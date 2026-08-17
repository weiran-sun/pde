import PDE.Basics.Laplace.LaplaceMeanValue


open Set Metric TopologicalSpace MeasureTheory


lemma integral_sphere_mvp (u : E → ℝ) (Ω : Set E) (x₀ : E) (R : ℝ)
    (h_open : IsOpen Ω) (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω) (h_harmonic : IsHarmonic u Ω) :
    ∀ r ∈ Set.Ioo 0 R, ∫ x in sphere x₀ r, u x ∂surfaceArea = 4 * Real.pi * r^2 * u x₀ := by
  intro r ⟨hr_pos, hr_lt⟩
  have h_surface := laplace_mean_value_property_3D u Ω x₀ r h_open hr_pos
    ((Metric.closedBall_subset_closedBall hr_lt.le).trans h_closed_ball) h_smooth h_harmonic
  rw [h_surface, ← mul_assoc, mul_one_div_cancel (by positivity), one_mul]

theorem laplace_mean_value_property_3D_ball
    (u : E → ℝ) (Ω : Set E) (x₀ : E) (R : ℝ)
    (h_open : IsOpen Ω)
    (hR : 0 < R)
    (h_closed_ball : Metric.closedBall x₀ R ⊆ Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (h_harmonic : IsHarmonic u Ω) :
    u x₀ = (1 / ((4/3) * Real.pi * R^3)) * ∫ x in Metric.closedBall x₀ R, u x := by
  rw [integral_closedBall_polar u x₀ R,
      MeasureTheory.setIntegral_congr_ae measurableSet_Ioo (Filter.Eventually.of_forall (integral_sphere_mvp u Ω x₀ R h_open h_closed_ball h_smooth h_harmonic)),
      integral_Ioo_r_sq_eval u x₀ R hR]
  have hV : 4 / 3 * Real.pi * R ^ 3 ≠ 0 := by positivity
  field_simp [hV]

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
    let f := fun x ↦ u x₀ - u x
    have h_cont : ContinuousOn u (Metric.closedBall x₀ R) := h_smooth.continuousOn.mono h_closed_ball
    have h_diff_cont : ContinuousOn f (Metric.closedBall x₀ R) := continuousOn_const.sub h_cont
    have h_int_const : IntegrableOn (fun _ : E ↦ u x₀) (Metric.closedBall x₀ R) := continuousOn_const.integrableOn_compact (isCompact_closedBall x₀ R)
    have h_int_u : IntegrableOn u (Metric.closedBall x₀ R) := h_cont.integrableOn_compact (isCompact_closedBall x₀ R)
    have h_integral_diff_zero : ∫ x in Metric.closedBall x₀ R, f x = 0 := by
      rw [integral_sub h_int_const h_int_u, setIntegral_const, volume_closed_ball_3d x₀ R hR, smul_eq_mul]
      rw [h_vol_mvp, ← mul_assoc, mul_one_div_cancel (by positivity), one_mul, sub_self]
    have h_diff_eq_zero_interior : ∀ x ∈ Metric.ball x₀ R, f x = 0 :=
      eq_zero_on_ball_of_nonneg_integral_zero f x₀ R h_diff_cont (Integrable.sub h_int_const h_int_u)
        (fun x hx ↦ sub_nonneg.mpr (h_max x hx)) h_integral_diff_zero
    have h_diff_eq_zero : ∀ x ∈ Metric.closedBall x₀ R, f x = 0 :=
      eq_zero_on_closedBall_of_eq_zero_on_ball f x₀ R hR h_diff_cont h_diff_eq_zero_interior
    intro x hx
    exact (sub_eq_zero.mp (h_diff_eq_zero x hx)).symm

theorem maximum_principle {u : E → ℝ} {Ω : Set E}
    (h_open : IsOpen Ω)
    (h_connected : IsConnected Ω)
    (h_harmonic : IsHarmonic u Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (h_cont : ContinuousOn u (closure Ω))
    (x₀ : E) (hx₀ : x₀ ∈ Ω)
    (h_max : ∀ x ∈ closure Ω, u x ≤ u x₀) :
    ∀ x ∈ Ω, u x = u x₀ := by
  let S := {x ∈ Ω | u x = u x₀}
  have h_cont_subtype : Continuous (u ∘ ((↑) : Ω → E)) :=
    continuousOn_iff_continuous_restrict.mp (h_cont.mono subset_closure)
  have h_closed_in : IsClosed (((↑) : Ω → E) ⁻¹' S) := by
    have h_eq : (((↑) : Ω → E) ⁻¹' S) = (u ∘ (↑)) ⁻¹' {u x₀} := by ext; simp [S]
    exact h_eq ▸ IsClosed.preimage h_cont_subtype isClosed_singleton
  have h_open_S : IsOpen S := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hx_mem, hx_eq⟩
    obtain ⟨ε, hε, h_ball⟩ := Metric.isOpen_iff.mp h_open x hx_mem
    refine ⟨ε / 2, by positivity, fun y hy ↦ ?_⟩
    have h_cball : Metric.closedBall x (ε / 2) ⊆ Ω := fun z hz ↦ by
      apply h_ball
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have h_max_local : ∀ z ∈ Metric.closedBall x (ε / 2), u z ≤ u x := fun z hz ↦ by
      rw [hx_eq]
      exact h_max z (subset_closure (h_cball hz))
    have h_const := strong_mp_on_ball u Ω x (ε / 2) h_open (by positivity) h_cball h_smooth h_harmonic h_max_local
    exact ⟨h_cball (Metric.ball_subset_closedBall hy), Eq.trans (h_const y (Metric.ball_subset_closedBall hy)) hx_eq⟩
  have h_clopen : IsClopen (((↑) : Ω → E) ⁻¹' S) :=
    ⟨h_closed_in, h_open_S.preimage continuous_subtype_val⟩
  have h_univ : (((↑) : Ω → E) ⁻¹' S) = Set.univ := by
    haveI : PreconnectedSpace Ω := isPreconnected_iff_preconnectedSpace.mp h_connected.isPreconnected
    rcases isClopen_iff.mp h_clopen with h_empty | h_univ_eq
    · exfalso; exact Set.notMem_empty (⟨x₀, hx₀⟩ : Ω) (h_empty ▸ ⟨hx₀, rfl⟩)
    · exact h_univ_eq
  intro x hx
  have hx_univ : (⟨x, hx⟩ : Ω) ∈ (((↑) : Ω → E) ⁻¹' S) := h_univ.symm ▸ Set.mem_univ _
  exact hx_univ.2

lemma isHarmonic_sub {u₁ u₂ : E → ℝ} {Ω : Set E}
    (h_open : IsOpen Ω)
    (h_smooth₁ : ContDiffOn ℝ 2 u₁ Ω) (h_smooth₂ : ContDiffOn ℝ 2 u₂ Ω)
    (h₁ : IsHarmonic u₁ Ω) (h₂ : IsHarmonic u₂ Ω) :
    IsHarmonic (u₁ - u₂) Ω := by
  intro x hx
  have h_nhds : Ω ∈ nhds x := h_open.mem_nhds hx
  have h_eq : gradient (u₁ - u₂) =ᶠ[nhds x] gradient u₁ - gradient u₂ := by
    filter_upwards [h_nhds] with y hy
    unfold gradient
    rw [fderiv_sub ((h_smooth₁.differentiableOn (by norm_num) y hy).differentiableAt (h_open.mem_nhds hy)) ((h_smooth₂.differentiableOn (by norm_num) y hy).differentiableAt (h_open.mem_nhds hy))]
    exact map_sub _ _ _
  have h1x := h₁ x hx
  have h2x := h₂ x hx
  unfold laplacian div_field at h1x h2x ⊢
  rw [h_eq.fderiv_eq, fderiv_sub (differentiableAt_gradient_of_contDiffOn h_smooth₁ h_nhds) (differentiableAt_gradient_of_contDiffOn h_smooth₂ h_nhds)]
  push_cast
  rw [LinearMap.map_sub, h1x, h2x, sub_zero]

lemma isHarmonic_neg {u : E → ℝ} {Ω : Set E}
    (h_open : IsOpen Ω)
    (h_harmonic : IsHarmonic u Ω) :
    IsHarmonic (fun x => -u x) Ω := by
  intro x hx
  have h_nhds : Ω ∈ nhds x := h_open.mem_nhds hx
  have h_eq : gradient (fun y ↦ -u y) =ᶠ[nhds x] fun y ↦ -gradient u y := by
    filter_upwards [h_nhds] with y hy
    unfold gradient
    erw [fderiv_neg]
    exact map_neg _ _
  have hx_lap := h_harmonic x hx
  unfold laplacian div_field at hx_lap ⊢
  erw [h_eq.fderiv_eq, fderiv_neg]
  push_cast
  rw [LinearMap.map_neg, hx_lap, neg_zero]

lemma minimum_principle {u : E → ℝ} {Ω : Set E}
    (h_open : IsOpen Ω)
    (h_connected : IsConnected Ω)
    (h_harmonic : IsHarmonic u Ω)
    (h_smooth : ContDiffOn ℝ 2 u Ω)
    (h_cont : ContinuousOn u (closure Ω))
    (x₀ : E) (hx₀ : x₀ ∈ Ω)
    (h_min : ∀ x ∈ closure Ω, u x₀ ≤ u x) :
    ∀ x ∈ Ω, u x = u x₀ := by
  intro x hx
  have h_const := maximum_principle h_open h_connected (isHarmonic_neg h_open h_harmonic)
    h_smooth.neg h_cont.neg x₀ hx₀ (fun y hy ↦ neg_le_neg (h_min y hy))
  exact neg_inj.mp (h_const x hx)

theorem dirichlet_uniqueness {u₁ u₂ : E → ℝ} {Ω : Set E} {g : E → ℝ}
    (h_open      : IsOpen Ω)
    (h_connected : IsConnected Ω)
    (h_bounded   : Bornology.IsBounded Ω)
    (h_harmonic₁ : IsHarmonic u₁ Ω)
    (h_harmonic₂ : IsHarmonic u₂ Ω)
    (h_smooth₁   : ContDiffOn ℝ 2 u₁ Ω)
    (h_smooth₂   : ContDiffOn ℝ 2 u₂ Ω)
    (h_cont₁     : ContinuousOn u₁ (closure Ω))
    (h_cont₂     : ContinuousOn u₂ (closure Ω))
    (h_bound₁    : ∀ x ∈ frontier Ω, u₁ x = g x)
    (h_bound₂    : ∀ x ∈ frontier Ω, u₂ x = g x) :
    ∀ x ∈ closure Ω, u₁ x = u₂ x := by
  let v : E → ℝ := fun x ↦ u₁ x - u₂ x
  have h_bound_v : ∀ x ∈ frontier Ω, v x = 0 := fun x hx ↦ by
    change u₁ x - u₂ x = 0
    rw [h_bound₁ x hx, h_bound₂ x hx, sub_self]
  have h_extremum_zero : ∀ x₀ ∈ closure Ω, (∀ x ∈ closure Ω, v x ≤ v x₀) ∨ (∀ x ∈ closure Ω, v x₀ ≤ v x) → v x₀ = 0 := by
    intro x₀ hx₀ h_ext
    by_cases h_fr : x₀ ∈ frontier Ω
    · exact h_bound_v x₀ h_fr
    · have h_int : x₀ ∈ Ω := mem_of_mem_closure_not_mem_frontier h_open hx₀ h_fr
      obtain ⟨x_fr, hx_fr⟩ := frontier_nonempty_of_bounded_open_nonempty h_open h_bounded ⟨x₀, h_int⟩
      have h_const : ∀ x ∈ Ω, v x = v x₀ := h_ext.elim
        (maximum_principle h_open h_connected (isHarmonic_sub h_open h_smooth₁ h_smooth₂ h_harmonic₁ h_harmonic₂) (h_smooth₁.sub h_smooth₂) (h_cont₁.sub h_cont₂) x₀ h_int)
        (minimum_principle h_open h_connected (isHarmonic_sub h_open h_smooth₁ h_smooth₂ h_harmonic₁ h_harmonic₂) (h_smooth₁.sub h_smooth₂) (h_cont₁.sub h_cont₂) x₀ h_int)
      have h_fr_eq : u₁ x_fr - u₂ x_fr = v x₀ := constant_of_continuous_closure (h_cont₁.sub h_cont₂) h_const (frontier_subset_closure hx_fr)
      have h_bound_val : u₁ x_fr - u₂ x_fr = 0 := h_bound_v x_fr hx_fr
      linarith
  have h_comp := Metric.isCompact_of_isClosed_isBounded isClosed_closure h_bounded.closure
  have h_ne := h_connected.nonempty.closure
  obtain ⟨x_max, hx_max, h_max⟩ := h_comp.exists_isMaxOn h_ne (h_cont₁.sub h_cont₂)
  obtain ⟨x_min, hx_min, h_min⟩ := h_comp.exists_isMinOn h_ne (h_cont₁.sub h_cont₂)
  intro x hx
  have h_max_zero : u₁ x_max - u₂ x_max = 0 := h_extremum_zero x_max hx_max (Or.inl h_max)
  have h_min_zero : u₁ x_min - u₂ x_min = 0 := h_extremum_zero x_min hx_min (Or.inr h_min)
  have h_upper : u₁ x - u₂ x ≤ u₁ x_max - u₂ x_max := h_max hx
  have h_lower : u₁ x_min - u₂ x_min ≤ u₁ x - u₂ x := h_min hx
  exact sub_eq_zero.mp (by linarith)

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
  have h_comp := Metric.isCompact_of_isClosed_isBounded isClosed_closure h_bounded.closure
  have h_ne := h_connected.nonempty.closure
  obtain ⟨x_max, hx_max, h_max⟩ := h_comp.exists_isMaxOn h_ne h_cont
  obtain ⟨x_min, hx_min, h_min⟩ := h_comp.exists_isMinOn h_ne h_cont
  have h_upper : ∀ x ∈ closure Ω, u x ≤ M := fun x hx ↦ by
    by_cases h_fr : x_max ∈ frontier Ω
    · exact le_trans (h_max hx) (h_bound_max x_max h_fr)
    · have h_int : x_max ∈ Ω := mem_of_mem_closure_not_mem_frontier h_open hx_max h_fr
      obtain ⟨x_fr, hx_fr⟩ := frontier_nonempty_of_bounded_open_nonempty h_open h_bounded ⟨x_max, h_int⟩
      have h_eq : u x_fr = u x_max := constant_of_continuous_closure h_cont
        (maximum_principle h_open h_connected h_harmonic h_smooth h_cont x_max h_int h_max) (frontier_subset_closure hx_fr)
      have h_le : u x ≤ u x_max := h_max hx
      rw [← h_eq] at h_le
      exact le_trans h_le (h_bound_max x_fr hx_fr)
  have h_lower : ∀ x ∈ closure Ω, m ≤ u x := fun x hx ↦ by
    by_cases h_fr : x_min ∈ frontier Ω
    · exact le_trans (h_bound_min x_min h_fr) (h_min hx)
    · have h_int : x_min ∈ Ω := mem_of_mem_closure_not_mem_frontier h_open hx_min h_fr
      obtain ⟨x_fr, hx_fr⟩ := frontier_nonempty_of_bounded_open_nonempty h_open h_bounded ⟨x_min, h_int⟩
      have h_eq : u x_fr = u x_min := constant_of_continuous_closure h_cont
        (minimum_principle h_open h_connected h_harmonic h_smooth h_cont x_min h_int h_min) (frontier_subset_closure hx_fr)
      have h_ge : u x_min ≤ u x := h_min hx
      rw [← h_eq] at h_ge
      exact le_trans (h_bound_min x_fr hx_fr) h_ge
  exact fun x hx ↦ ⟨h_lower x hx, h_upper x hx⟩

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
  have h_bound_v : ∀ x ∈ frontier Ω, u₁ x - u₂ x = g₁ x - g₂ x := fun x hx ↦ by
    rw [h_bound₁ x hx, h_bound₂ x hx]
  obtain ⟨y_max, hy_max, h_max⟩ := (Metric.isCompact_of_isClosed_isBounded isClosed_frontier (h_bounded.closure.subset frontier_subset_closure)).exists_isMaxOn
    (frontier_nonempty_of_bounded_open_nonempty h_open h_bounded h_connected.nonempty)
    ((h_cont₁.sub h_cont₂).abs.mono frontier_subset_closure)
  refine ⟨y_max, hy_max, fun x hx ↦ ?_⟩
  have h_bnds := harmonic_bounds h_open h_connected h_bounded
    (isHarmonic_sub h_open h_smooth₁ h_smooth₂ h_harmonic₁ h_harmonic₂)
    (h_smooth₁.sub h_smooth₂) (h_cont₁.sub h_cont₂)
    (fun y hy ↦ (abs_le.mp (h_max hy)).1)
    (fun y hy ↦ (abs_le.mp (h_max hy)).2)
    x hx
  have h_abs_le := abs_le.mpr h_bnds
  change |u₁ x - u₂ x| ≤ |u₁ y_max - u₂ y_max| at h_abs_le
  rw [h_bound_v y_max hy_max] at h_abs_le
  exact h_abs_le
