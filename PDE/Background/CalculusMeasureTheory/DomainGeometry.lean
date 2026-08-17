import PDE.Background.CalculusMeasureTheory.PDEDomains
import PDE.Background.CalculusMeasureTheory.DivergenceTheorem.GeneralizedDivergence

open Real Set Metric Filter Function Classical Topology Pointwise

open scoped Classical

open GeneralizedDivergenceStandalone

/-!
### General Topology and Metric Spaces
-/

lemma frontier_ball_eq_sphere (x₀ : E) (r : ℝ) (hr : 0 < r) :
    frontier (Metric.ball x₀ r) = sphere x₀ r := by
  exact frontier_ball x₀ (ne_of_gt hr)

lemma closure_ball_eq_closedBall (x₀ : E) (r : ℝ) (hr : 0 < r) :
    closure (Metric.ball x₀ r) = Metric.closedBall x₀ r := by
  exact closure_ball x₀ (ne_of_gt hr)

lemma closure_compl_closedBall_eq_compl_ball (x₀ : E) (ε : ℝ) (hε_pos : 0 < ε) :
  closure ((Metric.closedBall x₀ ε)ᶜ) = (Metric.ball x₀ ε)ᶜ := by
  rw [closure_compl, interior_closedBall x₀ (ne_of_gt hε_pos)]

lemma isClosed_setOf_dist_ge (x₀ : E) (ε : ℝ) :
    IsClosed {y : E | ε ≤ dist y x₀} :=
  isClosed_le continuous_const (continuous_id.dist continuous_const)

lemma closure_diff_subset_closure {A B : Set E} :
  closure (A \ B) ⊆ closure A := by
  exact closure_mono Set.sdiff_subset

lemma closure_subset_union_frontier (s : Set E) :
    closure s ⊆ s ∪ frontier s :=
  fun x hx => (Classical.em (x ∈ s)).elim Or.inl fun hx_not_s => Or.inr ⟨hx, fun h_int => hx_not_s (interior_subset h_int)⟩

lemma not_mem_interior_closedBall_of_mem_sphere {x x₀ : E} {ε : ℝ} (hε_pos : 0 < ε) (hx : x ∈ Metric.sphere x₀ ε) :
  x ∉ interior (Metric.closedBall x₀ ε) := by
  rw [interior_closedBall]
  exact fun h_in => ne_of_lt (Metric.mem_ball.mp h_in) (Metric.mem_sphere.mp hx)
  positivity

lemma isOpen_inter_closure_subset_closure_inter {U S : Set E} (hU : IsOpen U) :
  U ∩ closure S ⊆ closure (U ∩ S) := by
  rintro y ⟨hyU, hyS⟩
  rw [mem_closure_iff_nhds] at hyS ⊢
  intro V hV
  obtain ⟨z, ⟨hzU, hzV⟩, hzS⟩ := hyS (U ∩ V) (Filter.inter_mem (hU.mem_nhds hyU) hV)
  exact ⟨z, hzV, hzU, hzS⟩

lemma x_ne_x₀_of_dist_ge_pos {x x₀ : E} {ε : ℝ} (hε : 0 < ε) (h_dist : ε ≤ dist x x₀) :
    x ≠ x₀ :=
  dist_pos.mp (lt_of_lt_of_le hε h_dist)

lemma bounded_image_sub_subset_ball (Ω : Set E) (h_bounded : Bornology.IsBounded Ω) (x₀ : E) :
    ∃ R > 0, ((fun y => y - x₀) '' Ω) ⊆ Metric.closedBall 0 R := by
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall x₀).mp h_bounded
  refine ⟨max R 1, lt_max_iff.mpr (Or.inr Real.zero_lt_one), ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_closedBall, dist_zero_right, ← dist_eq_norm]
  exact le_trans (hR hy) (le_max_left R 1)

lemma mem_of_mem_closure_not_mem_frontier {s : Set E}
    (h_open : IsOpen s) {x : E} (hx_clos : x ∈ closure s) (hx_front : x ∉ frontier s) :
    x ∈ s := by
  have h_diff : x ∈ closure s \ frontier s := ⟨hx_clos, hx_front⟩
  rw [closure_sdiff_frontier s] at h_diff
  rwa [h_open.interior_eq] at h_diff

lemma frontier_nonempty_of_bounded_open_nonempty {s : Set E}[Nontrivial E] [ConnectedSpace E]
    (h_open : IsOpen s) (h_bounded : Bornology.IsBounded s) (h_nonempty : s.Nonempty) :
    (frontier s).Nonempty := by
  by_contra h_empty
  rw [Set.not_nonempty_iff_eq_empty] at h_empty
  have h_clopen : IsClopen s := ⟨isClosed_of_closure_subset (by rw [closure_eq_interior_union_frontier s, h_open.interior_eq, h_empty, Set.union_empty]), h_open⟩
  rcases isClopen_iff.mp h_clopen with h_empty_s | h_univ_s
  · exact h_nonempty.ne_empty h_empty_s
  · exact NormedSpace.unbounded_univ ℝ E (h_univ_s ▸ h_bounded)

lemma disjoint_closedBall_of_dist_lt (a b : E) (ε : ℝ) (h_dist : 2 * ε < dist a b) :
  Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  linarith [dist_triangle a x b, dist_comm x b, Metric.mem_closedBall'.mp hxa, Metric.mem_closedBall'.mp hxb]

lemma disjoint_spheres_of_disjoint_balls (a b : E) (ε : ℝ)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  Disjoint (Metric.sphere a ε) (Metric.sphere b ε) :=
  h_disjoint.mono Metric.sphere_subset_closedBall Metric.sphere_subset_closedBall

lemma isCompact_frontier_ball (c : E) (ε : ℝ) :
  IsCompact (frontier (Metric.ball c ε)) := by
  apply IsCompact.of_isClosed_subset (isCompact_closedBall c ε)
  · exact isClosed_frontier
  · exact fun x hx ↦ closure_minimal Metric.ball_subset_closedBall isClosed_closedBall (frontier_subset_closure hx)

lemma h_comp_front_a (a : E) (ε : ℝ) : IsCompact (frontier (Metric.ball a ε)) := isCompact_frontier_ball a ε

lemma h_comp_front_b (b : E) (ε : ℝ) : IsCompact (frontier (Metric.ball b ε)) := isCompact_frontier_ball b ε

/-!
### Affine Maps
-/

lemma affine_mem_closedBall (x₀ : E) {s R : ℝ} (hs_pos : 0 ≤ s) (hs_le : s ≤ R) {y : E} (hy : y ∈ sphere (0 : E) 1) :
    x₀ + s • y ∈ Metric.closedBall x₀ R := by
  simp [Metric.mem_closedBall, dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp hy, Real.norm_of_nonneg hs_pos]
  exact hs_le

lemma affine_mem_ball (x₀ : E) {s R : ℝ} (hs : s ∈ Set.Ioo 0 R) {y : E} (hy : y ∈ sphere (0 : E) 1) :
    x₀ + s • y ∈ Metric.ball x₀ R := by
  simp [Metric.mem_ball, dist_eq_norm, norm_smul, mem_sphere_zero_iff_norm.mp hy, Real.norm_of_nonneg hs.1.le]
  exact hs.2

lemma ray_outside_closedBall {x₀ x : E} {ε : ℝ} (hε_pos : 0 < ε) (hx : x ∈ Metric.sphere x₀ ε)
  {t : ℝ} (ht : 1 < t) : x₀ + t • (x - x₀) ∉ Metric.closedBall x₀ ε := fun h_in => by
  rw [Metric.mem_sphere, dist_eq_norm] at hx
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity), hx] at h_in
  nlinarith

lemma sphere_eq_image_add_zero (x₀ : E) (ε : ℝ) :
  Metric.sphere x₀ ε = (fun y : E => y + x₀) '' Metric.sphere (0 : E) ε := by
  ext x
  constructor
  · intro hx
    refine ⟨x - x₀, ?_, sub_add_cancel x x₀⟩
    simpa [Metric.mem_sphere, dist_eq_norm] using hx
  · rintro ⟨y, hy, rfl⟩
    simpa [Metric.mem_sphere, dist_eq_norm] using hy

lemma sphere_eq_homothety_image_unit_sphere (x₀ : E) {r : ℝ} (hr_pos : 0 < r) :
  Metric.sphere x₀ r = AffineMap.homothety x₀ r '' Metric.sphere x₀ 1 := by
  ext x
  simp only [Metric.mem_sphere, Set.mem_image, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  exact ⟨fun hx => ⟨r⁻¹ • (x - x₀) + x₀, by simp [norm_smul, abs_of_pos hr_pos, ← dist_eq_norm, hx, inv_mul_cancel₀ hr_pos.ne'], by simp [smul_smul, mul_inv_cancel₀ hr_pos.ne']⟩,
    fun ⟨y, hy, hyx⟩ => by simp [← hyx, norm_smul, abs_of_pos hr_pos, ← dist_eq_norm, hy]⟩

/-!
### Continuous Functions on Domains
-/

lemma eq_zero_on_closedBall_of_eq_zero_on_ball (f : E → ℝ) (x₀ : E) (R : ℝ) (hR : 0 < R)
    (hf_cont : ContinuousOn f (Metric.closedBall x₀ R))
    (h_interior : ∀ x ∈ Metric.ball x₀ R, f x = 0) :
    ∀ x ∈ Metric.closedBall x₀ R, f x = 0 := by
  intro x hx
  rcases eq_or_lt_of_le (Metric.mem_closedBall.mp hx) with h_eq | h_lt
  · let s := fun (n : ℕ) ↦ x₀ + (1 - 1 / (n + 2 : ℝ)) • (x - x₀)
    have hs_ball : ∀ n, s n ∈ Metric.ball x₀ R := by
      intro n
      rw [Metric.mem_ball, dist_eq_norm]
      have h_cancel : x₀ + (1 - 1 / (n + 2 : ℝ)) • (x - x₀) - x₀ = (1 - 1 / (n + 2 : ℝ)) • (x - x₀) := by abel
      rw [h_cancel, norm_smul, Real.norm_eq_abs]
      have h_norm : ‖x - x₀‖ = R := by rwa [← dist_eq_norm]
      rw [h_norm]
      have hn_pos : (0 : ℝ) < n + 2 := by positivity
      have h_frac_le : 1 / ((n : ℝ) + 2) ≤ 1 := by rw [div_le_iff₀ hn_pos]; linarith
      rw [abs_of_nonneg (by linarith)]
      exact mul_lt_of_lt_one_left hR (sub_lt_self 1 (one_div_pos.mpr hn_pos))
    have hs_tendsto : Filter.Tendsto s Filter.atTop (nhds x) := by
      have h_target : nhds x = nhds (x₀ + (1 : ℝ) • (x - x₀)) := by congr 1; simp
      rw [h_target]
      have h_tendsto_zero : Filter.Tendsto (fun (n : ℕ) ↦ 1 / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
        have h_eq_inv : (fun (n : ℕ) ↦ 1 / ((n : ℝ) + 2)) = (fun (n : ℕ) ↦ ((n : ℝ) + 2)⁻¹) := by ext n; exact one_div _
        rw [h_eq_inv]
        exact tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_mono (fun n ↦ by linarith) tendsto_natCast_atTop_atTop)
      have h_lim_real : Filter.Tendsto (fun n : ℕ ↦ 1 - 1 / (n + 2 : ℝ)) Filter.atTop (nhds 1) := by
        have h_sub := Filter.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ))) h_tendsto_zero
        rwa [sub_zero] at h_sub
      exact Filter.Tendsto.add (tendsto_const_nhds (x := x₀)) (Filter.Tendsto.smul h_lim_real (tendsto_const_nhds (x := x - x₀)))
    have h_tendsto_image : Filter.Tendsto (f ∘ s) Filter.atTop (nhds (f x)) :=
      (hf_cont x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hs_tendsto, Filter.Eventually.of_forall (fun n ↦ Metric.ball_subset_closedBall (hs_ball n))⟩)
    have h_tendsto_const : Filter.Tendsto (f ∘ s) Filter.atTop (nhds 0) := by
      have h_zero : f ∘ s = fun _ ↦ 0 := by ext n; exact h_interior (s n) (hs_ball n)
      rw [h_zero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h_tendsto_image h_tendsto_const
  · exact h_interior x h_lt

lemma constant_of_continuous_closure {u : E → ℝ} {Ω : Set E}
    (h_cont : ContinuousOn u (closure Ω)) {c : ℝ} (h_const : ∀ x ∈ Ω, u x = c)
    {y : E} (hy : y ∈ closure Ω) : u y = c := by
  haveI : Filter.NeBot (nhdsWithin y Ω) := mem_closure_iff_nhdsWithin_neBot.mp hy
  exact tendsto_nhds_unique ((h_cont y hy).mono subset_closure)
    (Filter.Tendsto.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h_const).symm tendsto_const_nhds)

lemma eventuallyEq_of_eqOn_open {s : Set E} (hs : IsOpen s) (x : E) (hx : x ∈ s)
  {f g : E → ℝ} (heq : ∀ y ∈ s, f y = g y) : f =ᶠ[𝓝 x] g := by
  have h_nhds : s ∈ 𝓝 x := IsOpen.mem_nhds hs hx
  exact Filter.eventually_of_mem h_nhds heq

lemma norm_continuous_bound_sphere {Ω : Set E}
  (n : E → E) (hn_cont : ContinuousOn n (closure Ω))
  (x₀ : E) (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω) :
  ∃ M₂ : ℝ, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ x ∈ Metric.sphere x₀ ε, ‖n x‖ ≤ M₂ := by
  obtain ⟨x_max, _, h_max_on⟩ := (isCompact_closedBall x₀ ε₀).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr hε₀_pos.le)
    ((ContinuousOn.norm hn_cont).mono (h_ball_subset.trans subset_closure))
  exact ⟨‖n x_max‖, fun ε hε x hx =>
    h_max_on (Metric.closedBall_subset_closedBall hε.2 (Metric.sphere_subset_closedBall hx))⟩

lemma exists_norm_bound_closedBall {Ω : Set E}
  (H : E → ℝ) (hH_cont : ContinuousOn H (closure Ω))
  (x₀ : E) (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) (h_ball_subset : Metric.closedBall x₀ ε₀ ⊆ Ω) :
  ∃ M_H : ℝ, 0 ≤ M_H ∧ ∀ x ∈ Metric.closedBall x₀ ε₀, ‖H x‖ ≤ M_H := by
  obtain ⟨x_max, _, h_max_on⟩ := (isCompact_closedBall x₀ ε₀).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr hε₀_pos.le)
    ((ContinuousOn.norm hH_cont).mono (h_ball_subset.trans subset_closure))
  exact ⟨‖H x_max‖, norm_nonneg _, h_max_on⟩

lemma continuousOn_normal_sphere (c : E) (ε : ℝ) (n : E → E) :
  ContinuousOn n (Metric.sphere c ε) := by
  sorry

lemma h_cont_n_sphere_a (a : E) (ε : ℝ) (n : E → E) : ContinuousOn n (Metric.sphere a ε) := continuousOn_normal_sphere a ε n

lemma h_cont_n_sphere_b (b : E) (ε : ℝ) (n : E → E) : ContinuousOn n (Metric.sphere b ε) := continuousOn_normal_sphere b ε n

/-!
### Opens sets and Eventual Properties
-/

lemma eventually_closedBall_subset_domain {Ω : Set E} (h_ball_1_subset : Metric.ball (0 : E) 1 ⊆ Ω) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Metric.closedBall (0 : E) ε ⊆ Ω := by
  have h_Iio_nhds : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds zero_lt_one
  filter_upwards [mem_nhdsWithin_of_mem_nhds h_Iio_nhds] with ε hε_lt
  exact Subset.trans (Metric.closedBall_subset_ball hε_lt) h_ball_1_subset

lemma eventually_closedBall_subset_of_isOpen {Ω : Set E} (h_open : IsOpen Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
  ∀ᶠ ε in 𝓝[>] 0, Metric.closedBall x₀ ε ⊆ Ω := by
  obtain ⟨ε₀, hε₀_pos, h_subset⟩ := Metric.isOpen_iff.mp h_open x₀ hx₀
  filter_upwards [Ico_mem_nhdsGT hε₀_pos] with ε hε
  exact (Metric.closedBall_subset_ball hε.2).trans h_subset

lemma eventually_disjoint_frontier_closedBall {Ω : Set E} (h_open : IsOpen Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
  ∀ᶠ ε in 𝓝[>] 0, Disjoint (frontier Ω) (Metric.closedBall x₀ ε) := by
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.mem_nhds_iff.mp (h_open.mem_nhds hx₀)
  filter_upwards [Ico_mem_nhdsGT hr_pos] with ε hε
  exact Disjoint.mono_right ((Metric.closedBall_subset_ball hε.2).trans hr_subset)
    (disjoint_frontier_iff_isOpen.mpr h_open)

lemma eventuallyEq_closure_diff_closedBall (Ω : Set E) (x₀ x : E) (ε : ℝ) (h_disj : x ∉ Metric.closedBall x₀ ε) :
  closure (Ω \ Metric.closedBall x₀ ε) =ᶠ[𝓝 x] closure Ω := by
  have h_open : IsOpen (Metric.closedBall x₀ ε)ᶜ := isOpen_compl_iff.mpr Metric.isClosed_closedBall
  filter_upwards [h_open.mem_nhds h_disj] with y hy
  exact propext ⟨fun h => closure_mono Set.sdiff_subset h, fun h => h_open.closure_inter ⟨h, hy⟩⟩

lemma exists_pos_closedBall_subset_of_isOpen {Ω : Set E} (h_open : IsOpen Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
  ∃ ε₀ > 0, Metric.closedBall x₀ ε₀ ⊆ Ω := by
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp h_open x₀ hx₀
  use r / 2
  constructor
  · linarith
  · intro y hy
    apply hr_subset
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    linarith

lemma greens_eps_separation_exists (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ha : a ∈ Ω) (hb : b ∈ Ω) (hne : a ≠ b) :
  ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
    2 * ε < dist a b ∧ Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε) ∧
    Metric.closedBall a ε ⊆ Ω ∧ Metric.closedBall b ε ⊆ Ω := by
  obtain ⟨r_a, hra_pos, ha_sub⟩ := Metric.isOpen_iff.mp HasPDEDomain.is_open a ha
  obtain ⟨r_b, hrb_pos, hb_sub⟩ := Metric.isOpen_iff.mp HasPDEDomain.is_open b hb
  have h_dist : 0 < dist a b / 3 := div_pos (dist_pos.mpr hne) (by norm_num)
  have h_eps₀_pos : 0 < min (dist a b / 3) (min r_a r_b) := lt_min h_dist (lt_min hra_pos hrb_pos)
  refine ⟨min (dist a b / 3) (min r_a r_b), h_eps₀_pos, fun ε _ hε_lt ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · linarith [lt_of_lt_of_le hε_lt (min_le_left (dist a b / 3) (min r_a r_b))]
  · apply disjoint_closedBall_of_dist_lt
    linarith [lt_of_lt_of_le hε_lt (min_le_left (dist a b / 3) (min r_a r_b))]
  · exact Set.Subset.trans (Metric.closedBall_subset_ball (lt_of_lt_of_le hε_lt (le_trans (min_le_right _ _) (min_le_left _ _)))) ha_sub
  · exact Set.Subset.trans (Metric.closedBall_subset_ball (lt_of_lt_of_le hε_lt (le_trans (min_le_right _ _) (min_le_right _ _)))) hb_sub

/-!
### Punctured Domains and Boundaries
-/

lemma frontier_diff_closedBall_gen (Ω : Set E) [HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε : 0 < ε)
    (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
    frontier (Ω \ Metric.closedBall x₀ ε) = frontier Ω ∪ Metric.sphere x₀ ε := by
  refine subset_antisymm (fun x hx ↦ ?_) (Set.union_subset (fun x ⟨hxC, hxI⟩ ↦ ?_) (fun x hx ↦ ?_))
  · rcases frontier_inter_subset Ω (Metric.closedBall x₀ ε)ᶜ (by rwa [sdiff_eq] at hx) with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl h1
    · exact Or.inr (by rwa [frontier_compl, frontier_closedBall x₀ hε.ne.symm] at h2)
  · refine ⟨_root_.mem_closure_iff.mpr fun V hV hxV ↦ ?_, fun h ↦ hxI (interior_mono Set.sdiff_subset h)⟩
    obtain ⟨y, hyV, hyΩ⟩ := _root_.mem_closure_iff.mp hxC _ (hV.inter isClosed_closedBall.isOpen_compl) ⟨hxV, fun h ↦ hxI ((HasPDEDomain.is_open (s := Ω)).interior_eq.symm ▸ h_subset h)⟩
    exact ⟨y, hyV.1, hyΩ, hyV.2⟩
  · refine ⟨_root_.mem_closure_iff.mpr fun V hV hxV ↦ ?_, fun h_int ↦ (interior_subset h_int).2 (Metric.sphere_subset_closedBall hx)⟩
    obtain ⟨y, hy_in, hy_compl⟩ := _root_.mem_closure_iff.mp (show x ∈ closure (Metric.closedBall x₀ ε)ᶜ by rw [closure_compl]; exact (frontier_closedBall x₀ hε.ne.symm ▸ hx).2) (V ∩ Ω) (hV.inter (HasPDEDomain.is_open (s := Ω))) ⟨hxV, h_subset (Metric.sphere_subset_closedBall hx)⟩
    exact ⟨y, hy_in.1, hy_in.2, hy_compl⟩

lemma mem_closure_diff_closedBall {Ω : Set E} {x₀ x : E} {ε : ℝ}
  (hx_closure : x ∈ closure Ω) (hx_not_mem : x ∉ Metric.closedBall x₀ ε) :
  x ∈ closure (Ω \ Metric.closedBall x₀ ε) := mem_closure_iff_nhds.mpr fun U hU => by
  obtain ⟨y, ⟨hy_U, hy_not⟩, hy_Ω⟩ := mem_closure_iff_nhds.mp hx_closure _
    (Filter.inter_mem hU (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx_not_mem))
  exact ⟨y, hy_U, hy_Ω, hy_not⟩

lemma dist_ge_of_mem_closure_excised {Ω : Set E} {x₀ : E} {ε : ℝ} (hε_pos : 0 < ε) {x : E}
  (hx : x ∈ closure (Ω \ Metric.closedBall x₀ ε)) :
  ε ≤ dist x x₀ := by
  have h_subset : closure (Ω \ Metric.closedBall x₀ ε) ⊆ closure ((Metric.closedBall x₀ ε)ᶜ) :=
    closure_mono (Set.sdiff_subset_compl Ω (Metric.closedBall x₀ ε))
  have h_compl := h_subset hx
  rwa [closure_compl_closedBall_eq_compl_ball x₀ ε hε_pos, Set.mem_compl_iff, Metric.mem_ball, not_lt] at h_compl

lemma dist_ge_of_mem_closure_punctured {x₀ : E} {ε : ℝ} {Ω : Set E} {x : E}
    (hx : x ∈ closure (Ω \ Metric.closedBall x₀ ε)) :
    ε ≤ dist x x₀ := by
  change x ∈ {y : E | ε ≤ dist y x₀}
  exact closure_minimal (fun y hy => le_of_lt (not_le.mp (fun h => hy.2 (Metric.mem_closedBall.mpr h)))) (isClosed_setOf_dist_ge x₀ ε) hx

lemma closure_diff_ball_subset_closure_punctured
  (Ω : Set E) (x₀ : E) (ε : ℝ) (hε : 0 < ε) :
  closure (Ω \ Metric.closedBall x₀ ε) ⊆ closure Ω \ {x₀} := by
  intro x hx
  refine ⟨closure_mono sdiff_subset hx, ?_⟩
  intro h_eq
  rw [h_eq] at hx
  obtain ⟨y, hy_ball, hy_diff⟩ := mem_closure_iff_nhds.mp hx _ (Metric.ball_mem_nhds x₀ hε)
  exact hy_diff.2 (Metric.ball_subset_closedBall hy_ball)

lemma mem_punctured_or_frontier_of_mem_closure {Ω : Set E} {x₀ : E} {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : x ∈ closure (Ω \ Metric.closedBall x₀ ε)) :
    x ∈ Ω \ {x₀} ∨ x ∈ frontier Ω :=
  (closure_subset_union_frontier Ω (closure_mono sdiff_subset hx)).elim
    (fun h_in_Omega => Or.inl ⟨h_in_Omega, x_ne_x₀_of_dist_ge_pos hε (dist_ge_of_mem_closure_punctured hx)⟩)
    Or.inr

lemma mem_diff_singleton_or_frontier_of_mem_closure_excised {Ω : Set E} {x₀ : E} {ε : ℝ} (hε_pos : 0 < ε)
  {y : E} (hy : y ∈ closure (Ω \ Metric.closedBall x₀ ε)) :
  y ∈ Ω \ {x₀} ∨ y ∈ frontier Ω := by
  have h_not_x₀ : y ≠ x₀ := dist_pos.mp (hε_pos.trans_le (dist_ge_of_mem_closure_punctured hy))
  by_cases hy_omega : y ∈ Ω
  · exact Or.inl ⟨hy_omega, h_not_x₀⟩
  · exact Or.inr ⟨closure_mono sdiff_subset hy, fun h_int => hy_omega (interior_subset h_int)⟩

lemma frontier_subset_compl_singleton {Ω : Set E} [HasPDEDomain Ω] {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    frontier Ω ⊆ ({x₀} : Set E)ᶜ :=
  fun _ hx h_eq => hx.2 ((Set.mem_singleton_iff.mp h_eq).symm ▸ (HasPDEDomain.is_open (s := Ω)).interior_eq.symm ▸ hx₀)

lemma disjoint_frontier_sphere {Ω : Set E} [HasPDEDomain Ω] {x₀ : E} {ε : ℝ}
  (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  Disjoint (frontier Ω) (Metric.sphere x₀ ε) := by
  exact Set.disjoint_left.mpr fun x hx hx_sph => hx.2 ((HasPDEDomain.is_open (s := Ω)).interior_eq.symm ▸ h_subset (Metric.sphere_subset_closedBall hx_sph))

lemma sphere_subset_diff_singleton {Ω : Set E} {x₀ : E} {ε : ℝ}
  (hε_pos : 0 < ε) (h_subset : Metric.sphere x₀ ε ⊆ Ω) :
  Metric.sphere x₀ ε ⊆ Ω \ {x₀} :=
  fun _ hx => ⟨h_subset hx, dist_pos.mp (hε_pos.trans_eq (Metric.mem_sphere.mp hx).symm)⟩

lemma sphere_subset_closure_excised (Ω : Set E) (x₀ : E) (ε : ℝ) (h_eps_pos : 0 < ε) (h_open : IsOpen Ω) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  Metric.sphere x₀ ε ⊆ closure (Ω \ Metric.closedBall x₀ ε) := fun x hx => mem_closure_iff_nhds.mpr fun V hV => by
  obtain ⟨t, ht_mem, ht_gt⟩ := Filter.nonempty_of_mem (Filter.inter_mem
    (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)) <| (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      ((show x = x₀ + (1 : ℝ) • (x - x₀) by simp) ▸ Filter.inter_mem (IsOpen.mem_nhds h_open (h_subset (Metric.sphere_subset_closedBall hx))) hV))
    (self_mem_nhdsWithin (s := Set.Ioi (1 : ℝ))))
  exact ⟨x₀ + t • (x - x₀), ht_mem.2, ht_mem.1, ray_outside_closedBall h_eps_pos hx ht_gt⟩

lemma sphere_subset_closure_compl_closedBall {x₀ : E} {ε : ℝ} (hε_pos : 0 < ε) :
  Metric.sphere x₀ ε ⊆ closure ((Metric.closedBall x₀ ε)ᶜ) := by
  rw [closure_compl_closedBall_eq_compl_ball x₀ ε hε_pos]
  refine Disjoint.subset_compl_left ?_
  exact Disjoint.symm sphere_disjoint_ball

lemma sphere_subset_closure_diff_ball {Ω : Set E} [HasPDEDomain Ω] (x₀ : E) (ε : ℝ)
  (hε_pos : 0 < ε) (h_ball_sub_omega : Metric.closedBall x₀ ε ⊆ Ω) :
  Metric.sphere x₀ ε ⊆ closure (Ω \ Metric.closedBall x₀ ε) :=
  fun _ hx => isOpen_inter_closure_subset_closure_inter HasPDEDomain.is_open
    ⟨h_ball_sub_omega (Metric.sphere_subset_closedBall hx),
     sphere_subset_closure_compl_closedBall hε_pos hx⟩

lemma sphere_subset_closure_annulus (Ω : Set E) [HasPDEDomain Ω] (x₀ : E) (ε ε₀ : ℝ)
  (hε : ε ∈ Set.Ioc 0 ε₀) (h_ball_subset_hyp : Metric.closedBall x₀ ε₀ ⊆ Ω) :
  Metric.sphere x₀ ε ⊆ closure (Ω \ Metric.closedBall x₀ ε) :=
  sphere_subset_closure_diff_ball x₀ ε hε.1 ((Metric.closedBall_subset_closedBall hε.2).trans h_ball_subset_hyp)

lemma mem_closure_annulus_of_mem_sphere {Ω : Set E} [HasPDEDomain Ω]
  {x₀ : E} {ε : ℝ} (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
  {x : E} (hx : x ∈ Metric.sphere x₀ ε) :
  x ∈ closure (Ω \ Metric.closedBall x₀ ε) :=
  sphere_subset_closure_diff_ball x₀ ε hε h_subset hx

lemma closure_ball_subset_punctured_omega (Ω : Set E) (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b)
  (h_ball_subset : Metric.closedBall a ε ⊆ Ω) :
  closure (Metric.ball a ε) ⊆ Ω \ {b} := by
  intro y hy
  have hy_closed : y ∈ Metric.closedBall a ε := closure_minimal Metric.ball_subset_closedBall isClosed_closedBall hy
  exact ⟨h_ball_subset hy_closed, fun e ↦ by linarith [show dist a b ≤ ε from Metric.mem_closedBall'.mp (e ▸ hy_closed), hε]⟩

/-!
### Domains with Two Punctures
-/

lemma frontier_closedBall_union (a b : E) (ε : ℝ)
  (h_disj : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  frontier (Metric.closedBall a ε ∪ Metric.closedBall b ε) =
  frontier (Metric.closedBall a ε) ∪ frontier (Metric.closedBall b ε) := by
  have h_interior_union : interior (Metric.closedBall a ε ∪ Metric.closedBall b ε) = interior (Metric.closedBall a ε) ∪ interior (Metric.closedBall b ε) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      rcases interior_subset hx with hxa | hxb
      · left
        refine mem_interior.mpr ⟨interior (Metric.closedBall a ε ∪ Metric.closedBall b ε) ∩ (Metric.closedBall b ε)ᶜ, ?_, IsOpen.inter isOpen_interior (isOpen_compl_iff.mpr isClosed_closedBall), ⟨hx, Set.disjoint_left.mp h_disj hxa⟩⟩
        rintro y ⟨hy_int, hy_not_b⟩
        rcases interior_subset hy_int with hya | hyb
        · exact hya
        · contradiction
      · right
        refine mem_interior.mpr ⟨interior (Metric.closedBall a ε ∪ Metric.closedBall b ε) ∩ (Metric.closedBall a ε)ᶜ, ?_, IsOpen.inter isOpen_interior (isOpen_compl_iff.mpr isClosed_closedBall), ⟨hx, Set.disjoint_right.mp h_disj hxb⟩⟩
        rintro y ⟨hy_int, hy_not_a⟩
        rcases interior_subset hy_int with hya | hyb
        · contradiction
        · exact hyb
    · rintro x (hx | hx)
      · exact interior_mono Set.subset_union_left hx
      · exact interior_mono Set.subset_union_right hx
  rw [← closure_sdiff_interior, ← closure_sdiff_interior, ← closure_sdiff_interior,
    (IsClosed.union isClosed_closedBall isClosed_closedBall).closure_eq,
    isClosed_closedBall.closure_eq, isClosed_closedBall.closure_eq, h_interior_union]
  ext x
  simp only [Set.mem_sdiff, Set.mem_union]
  constructor
  · rintro ⟨hxa | hxb, h_not_int⟩
    · exact Or.inl ⟨hxa, fun h => h_not_int (Or.inl h)⟩
    · exact Or.inr ⟨hxb, fun h => h_not_int (Or.inr h)⟩
  · rintro (⟨hxa, h_not_int_a⟩ | ⟨hxb, h_not_int_b⟩)
    · refine ⟨Or.inl hxa, ?_⟩
      rintro (h | h)
      · contradiction
      · exact Set.disjoint_left.mp h_disj hxa (interior_subset h)
    · refine ⟨Or.inr hxb, ?_⟩
      rintro (h | h)
      · exact Set.disjoint_right.mp h_disj hxb (interior_subset h)
      · contradiction

lemma frontier_sdiff_union (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (ha_sub : Metric.closedBall a ε ⊆ Ω) (hb_sub : Metric.closedBall b ε ⊆ Ω) :
  frontier (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) =
  frontier Ω ∪ frontier (Metric.closedBall a ε ∪ Metric.closedBall b ε) := by
  have h_closed_union : IsClosed (Metric.closedBall a ε ∪ Metric.closedBall b ε) :=
    IsClosed.union isClosed_closedBall isClosed_closedBall
  rw [← closure_sdiff_interior, ← closure_sdiff_interior, ← closure_sdiff_interior,
    (IsOpen.sdiff HasPDEDomain.is_open h_closed_union).interior_eq,
    HasPDEDomain.is_open.interior_eq, h_closed_union.closure_eq]
  ext x
  simp only [Set.mem_union, Set.mem_sdiff]
  constructor
  · rintro ⟨hx_clos, hx_not_diff⟩
    by_cases hx_omega : x ∈ Ω
    · right
      refine ⟨by_contra fun hK => hx_not_diff ⟨hx_omega, hK⟩, fun hx_int => ?_⟩
      rcases _root_.mem_closure_iff.mp hx_clos _ isOpen_interior hx_int with ⟨y, hy_int, hy_diff⟩
      exact hy_diff.2 (interior_subset hy_int)
    · left
      exact ⟨closure_mono Set.sdiff_subset hx_clos, hx_omega⟩
  · rintro (⟨hx_clos_omega, hx_not_omega⟩ | ⟨hx_in_K, hx_not_int_K⟩)
    · refine ⟨_root_.mem_closure_iff.mpr fun U hU hxU => ?_, fun h_diff => hx_not_omega h_diff.1⟩
      have hx_inter : x ∈ U ∩ (Metric.closedBall a ε ∪ Metric.closedBall b ε)ᶜ :=
        ⟨hxU, fun hxK => hx_not_omega (Set.union_subset ha_sub hb_sub hxK)⟩
      rcases _root_.mem_closure_iff.mp hx_clos_omega _ (IsOpen.inter hU (isOpen_compl_iff.mpr h_closed_union)) hx_inter with ⟨y, ⟨hyU, hyK_compl⟩, hyOmega⟩
      exact ⟨y, hyU, ⟨hyOmega, hyK_compl⟩⟩
    · refine ⟨_root_.mem_closure_iff.mpr fun U hU hxU => ?_, fun h_diff => h_diff.2 hx_in_K⟩
      by_contra h_not_nonempty
      have h_subset : U ∩ Ω ⊆ Metric.closedBall a ε ∪ Metric.closedBall b ε := by
        rintro y ⟨hyU, hyOmega⟩
        by_contra hyK
        exact h_not_nonempty ⟨y, hyU, hyOmega, hyK⟩
      exact hx_not_int_K (mem_interior.mpr ⟨U ∩ Ω, h_subset, IsOpen.inter hU HasPDEDomain.is_open, ⟨hxU, Set.union_subset ha_sub hb_sub hx_in_K⟩⟩)

lemma frontier_punctured_eq_union (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (hε : 0 < ε)
  (h_disj : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (ha_sub : Metric.closedBall a ε ⊆ Ω) (hb_sub : Metric.closedBall b ε ⊆ Ω) :
  frontier (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) =
  frontier Ω ∪ Metric.sphere a ε ∪ Metric.sphere b ε := by
  rw [frontier_sdiff_union Ω a b ε ha_sub hb_sub,
    frontier_closedBall_union a b ε h_disj,
    frontier_closedBall a (ne_of_gt hε),
    frontier_closedBall b (ne_of_gt hε),
    ← Set.union_assoc]

lemma exists_point_close_outside_balls (Ω : Set E) [HasPDEDomain Ω] (a b x : E) (ε δ : ℝ)
  (hε_pos : 0 < ε) (hδ_pos : 0 < δ)
  (hx_sphere : x ∈ Metric.sphere a ε)
  (hx_not_b : ε < dist x b)
  (hx_omega : x ∈ Ω) :
  ∃ y : E, dist x y < δ ∧ ε < dist y a ∧ y ∈ Ω ∧ ε < dist y b := by
  obtain ⟨r_omega, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp HasPDEDomain.is_open x hx_omega
  let r_min := min δ (min r_omega (dist x b - ε))
  have hr_pos' : 0 < r_min := lt_min hδ_pos (lt_min hr_pos (sub_pos.mpr hx_not_b))
  let t := r_min / (2 * ε)
  have ht_pos : 0 < t := div_pos hr_pos' (mul_pos (by norm_num) hε_pos)
  have h_norm : ‖x - a‖ = ε := by rw [← dist_eq_norm]; exact Metric.mem_sphere.mp hx_sphere
  have h_xy : dist x (x + t • (x - a)) = r_min / 2 := by
    have h_two : (2 : ℝ) ≠ 0 := by norm_num
    rw [dist_eq_norm, show x - (x + t • (x - a)) = -(t • (x - a)) by abel, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos, h_norm]
    linarith [div_mul_cancel₀ r_min (mul_ne_zero h_two (ne_of_gt hε_pos))]
  use x + t • (x - a)
  refine ⟨by linarith [hr_pos', min_le_left δ (min r_omega (dist x b - ε)), h_xy], ?_, ?_, ?_⟩
  · have h_ya : x + t • (x - a) - a = (1 + t) • (x - a) := by rw [add_smul, one_smul]; abel
    rw [dist_eq_norm, h_ya, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), h_norm]
    have : 0 < t * ε := mul_pos ht_pos hε_pos
    linarith
  · apply hr_subset
    rw [Metric.mem_ball, dist_comm, h_xy]
    linarith [hr_pos', min_le_right δ (min r_omega (dist x b - ε)), min_le_left r_omega (dist x b - ε)]
  · have h_tri := dist_triangle x (x + t • (x - a)) b
    have h_bound : r_min ≤ dist x b - ε := le_trans (min_le_right δ _) (min_le_right r_omega _)
    linarith [hr_pos', h_xy]

lemma sphere_subset_closure_punctured (Ω : Set E) [HasPDEDomain Ω] (c d : E) (ε : ℝ)
  (hε_pos : 0 < ε)
  (hc_subset : Metric.closedBall c ε ⊆ Ω)
  (h_disj : Disjoint (Metric.closedBall c ε) (Metric.closedBall d ε)) :
  Metric.sphere c ε ⊆ closure (Ω \ (Metric.closedBall c ε ∪ Metric.closedBall d ε)) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro δ hδ_pos
  have hx_not_d : ε < dist x d := not_le.mp (Set.disjoint_left.mp h_disj (Metric.sphere_subset_closedBall hx))
  obtain ⟨y, hy_dist, hy_c, hy_omega, hy_d⟩ :=
    exists_point_close_outside_balls Ω c d x ε δ hε_pos hδ_pos hx hx_not_d (hc_subset (Metric.sphere_subset_closedBall hx))
  exact ⟨y, ⟨hy_omega, fun h_or ↦ h_or.elim (not_le_of_gt hy_c) (not_le_of_gt hy_d)⟩, hy_dist⟩

lemma sphere_a_subset_closure (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (hε_pos : 0 < ε) (hra_subset : Metric.closedBall a ε ⊆ Ω) (h_disj : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  Metric.sphere a ε ⊆ closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) :=
  sphere_subset_closure_punctured Ω a b ε hε_pos hra_subset h_disj

lemma sphere_b_subset_closure_punctured (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (hε_pos : 0 < ε) (hb_subset : Metric.closedBall b ε ⊆ Ω) (h_disj : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  Metric.sphere b ε ⊆ closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) := by
  have h_sub := sphere_subset_closure_punctured Ω b a ε hε_pos hb_subset h_disj.symm
  rwa [Set.union_comm] at h_sub

lemma disjoint_frontier_union_sphere_a_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  Disjoint (frontier Ω ∪ Metric.sphere a ε) (Metric.sphere b ε) :=
  Disjoint.union_left (disjoint_frontier_sphere hb_subset) (disjoint_spheres_of_disjoint_balls a b ε h_disjoint)

lemma sphere_a_subset_closure_punctured (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (hε_pos : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (h_disj : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  Metric.sphere a ε ⊆ closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro δ hδ_pos
  have hx_not_b : ε < dist x b := not_le.mp (Set.disjoint_left.mp h_disj (Metric.sphere_subset_closedBall hx))
  obtain ⟨y, hy_dist, hy_a, hy_omega, hy_b⟩ :=
    exists_point_close_outside_balls Ω a b x ε δ hε_pos hδ_pos hx hx_not_b (ha_subset (Metric.sphere_subset_closedBall hx))
  exact ⟨y, ⟨hy_omega, fun h_or ↦ h_or.elim (not_le_of_gt hy_a) (not_le_of_gt hy_b)⟩, hy_dist⟩

/-!
### Domain Geometries and Normals
-/

lemma image_ball_E_to_EN2 (x₀ : E) (r : ℝ) :
    E_to_EN2 '' Metric.ball x₀ r = Metric.ball (E_to_EN2 x₀) r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Metric.mem_ball] at hz ⊢
    calc dist (E_to_EN2 z) (E_to_EN2 x₀)
      _ = ‖E_to_EN2 z - E_to_EN2 x₀‖ := dist_eq_norm _ _
      _ = ‖E_to_EN2 (z - x₀)‖ := by rw [map_sub]
      _ = ‖z - x₀‖ := LinearIsometryEquiv.norm_map _ _
      _ = dist z x₀ := (dist_eq_norm _ _).symm
      _ < r := hz
  · intro hy
    rw [Metric.mem_ball] at hy
    refine ⟨E_to_EN2.symm y, ?_, LinearIsometryEquiv.apply_symm_apply _ _⟩
    rw [Metric.mem_ball, dist_eq_norm, ← LinearIsometryEquiv.norm_map E_to_EN2]
    have h_sub : E_to_EN2 (E_to_EN2.symm y - x₀) = y - E_to_EN2 x₀ := by
      rw [map_sub, LinearIsometryEquiv.apply_symm_apply]
    rw [h_sub, ← dist_eq_norm]
    exact hy

lemma E_to_EN2_ball_normal (x₀ : E) (r : ℝ) (x : EN 2) :
    E_to_EN2 ((1 / r) • (E_to_EN2.symm x - x₀)) = r⁻¹ • (x - E_to_EN2 x₀) := by
  rw [map_smul, map_sub, LinearIsometryEquiv.apply_symm_apply, one_div]

lemma ball_normal_forward_ray_outside {x₀ : E} {r : ℝ} (hr : 0 < r) {x : EN 2}
    (hx : ‖x - E_to_EN2 x₀‖ = r) :
    ∀ᶠ (t : ℝ) in 𝓝[>] 0, x + t • r⁻¹ • (x - E_to_EN2 x₀) ∉ closure (Metric.ball (E_to_EN2 x₀) r) := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [closure_ball (E_to_EN2 x₀) (ne_of_gt hr)]
  intro h_in
  rw [Metric.mem_closedBall, dist_eq_norm] at h_in
  have h_add : x + t • r⁻¹ • (x - E_to_EN2 x₀) - E_to_EN2 x₀ = (1 + t * r⁻¹) • (x - E_to_EN2 x₀) := by
    calc x + t • r⁻¹ • (x - E_to_EN2 x₀) - E_to_EN2 x₀
      _ = (x - E_to_EN2 x₀) + (t * r⁻¹) • (x - E_to_EN2 x₀) := by rw [add_sub_right_comm, smul_smul]
      _ = (1 : ℝ) • (x - E_to_EN2 x₀) + (t * r⁻¹) • (x - E_to_EN2 x₀) := by rw [one_smul]
      _ = (1 + t * r⁻¹) • (x - E_to_EN2 x₀) := by rw [add_smul]
  rw [h_add, norm_smul, Real.norm_eq_abs, hx] at h_in
  have h_pos : 0 < 1 + t * r⁻¹ := by
    have h_t_pos : 0 < t * r⁻¹ := mul_pos ht (inv_pos.mpr hr)
    linarith
  rw [abs_of_pos h_pos] at h_in
  have h_lt : r < (1 + t * r⁻¹) * r := by
    rw [add_mul, one_mul]
    have h_t_pos : 0 < t * r⁻¹ * r := by
      calc 0 < t := ht
        _ = t * 1 := (mul_one t).symm
        _ = t * (r⁻¹ * r) := by rw [inv_mul_cancel₀ (ne_of_gt hr)]
        _ = t * r⁻¹ * r := by rw [← mul_assoc]
    linarith
  linarith

lemma ball_normal_backward_ray_inside {x₀ : E} {r : ℝ} (hr : 0 < r) {x : EN 2}
    (hx : ‖x - E_to_EN2 x₀‖ = r) :
    ∀ᶠ (t : ℝ) in 𝓝[>] 0, x - t • r⁻¹ • (x - E_to_EN2 x₀) ∈ Metric.ball (E_to_EN2 x₀) r := by
  have h_nhds : Set.Iio r ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hr
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h_nhds] with t ht htr
  rw [Metric.mem_ball, dist_eq_norm]
  have h_sub : x - t • r⁻¹ • (x - E_to_EN2 x₀) - E_to_EN2 x₀ = (1 - t * r⁻¹) • (x - E_to_EN2 x₀) := by
    calc x - t • r⁻¹ • (x - E_to_EN2 x₀) - E_to_EN2 x₀
      _ = (x - E_to_EN2 x₀) - (t * r⁻¹) • (x - E_to_EN2 x₀) := by rw [sub_right_comm, smul_smul]
      _ = (1 : ℝ) • (x - E_to_EN2 x₀) - (t * r⁻¹) • (x - E_to_EN2 x₀) := by rw [one_smul]
      _ = (1 - t * r⁻¹) • (x - E_to_EN2 x₀) := by rw [sub_smul]
  rw [h_sub, norm_smul, Real.norm_eq_abs, hx]
  have h_pos : 0 ≤ 1 - t * r⁻¹ := by
    have h_tr : t * r⁻¹ ≤ 1 := by
      calc t * r⁻¹ ≤ r * r⁻¹ := mul_le_mul_of_nonneg_right htr.le (inv_pos.mpr hr).le
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
    linarith
  rw [abs_of_nonneg h_pos]
  have h_lt : (1 - t * r⁻¹) * r < r := by
    rw [sub_mul, one_mul]
    have h_t_pos : 0 < t * r⁻¹ * r := by
      calc 0 < t := ht
        _ = t * 1 := (mul_one t).symm
        _ = t * (r⁻¹ * r) := by rw [inv_mul_cancel₀ (ne_of_gt hr)]
        _ = t * r⁻¹ * r := by rw [← mul_assoc]
    linarith
  exact h_lt

lemma ball_normal_tangent_cone_orthogonal {x₀ : E} {r : ℝ} (hr : 0 < r) {x : EN 2}
    (hx : ‖x - E_to_EN2 x₀‖ = r) {y : EN 2} (hy : y ∈ tangentConeAt ℝ (frontier (Metric.ball (E_to_EN2 x₀) r)) x) :
    inner ℝ (r⁻¹ • (x - E_to_EN2 x₀)) y = 0 := by
  rw [inner_smul_left]
  have h_zero : inner ℝ (x - E_to_EN2 x₀) y = 0 := by
    obtain ⟨α, l, hl, cs, d, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
    have h_norm_x : ‖x - E_to_EN2 x₀‖ = r := hx
    have h_sphere : ∀ᶠ (n : α) in l, ‖x + d n - E_to_EN2 x₀‖ = r := by
      filter_upwards [hds] with n hn
      rw [frontier_ball (E_to_EN2 x₀) (ne_of_gt hr)] at hn
      exact Metric.mem_sphere.mp hn
    have h_algebra : (fun n ↦ inner ℝ (x - E_to_EN2 x₀) (cs n • d n)) =ᶠ[l] (fun n ↦ -(cs n * ‖d n‖^2 / 2)) := by
      filter_upwards [h_sphere] with n hn
      have h_add : x - E_to_EN2 x₀ + d n = x + d n - E_to_EN2 x₀ := by abel
      have h_sq : ‖x - E_to_EN2 x₀ + d n‖ ^ 2 = r ^ 2 := by rw [h_add, hn]
      have h_expand := norm_add_sq_real (x - E_to_EN2 x₀) (d n)
      rw [h_sq, h_norm_x] at h_expand
      have h_inner : inner ℝ (x - E_to_EN2 x₀) (d n) = -(‖d n‖ ^ 2 / 2) := by linarith
      rw [inner_smul_right, h_inner]
      ring
    have h_lim_left : Filter.Tendsto (fun n ↦ inner ℝ (x - E_to_EN2 x₀) (cs n • d n)) l (𝓝 (inner ℝ (x - E_to_EN2 x₀) y)) := by
      exact Filter.Tendsto.inner tendsto_const_nhds hcd
    have h_lim_right : Filter.Tendsto (fun n ↦ -(cs n * ‖d n‖^2 / 2)) l (𝓝 0) := by
      have h_eq : (fun n ↦ -(cs n * ‖d n‖ ^ 2 / 2)) = (fun n ↦ inner ℝ (cs n • d n) (d n) * (-1 / 2)) := by
        ext n
        rw [real_inner_comm (d n) (cs n • d n), inner_smul_right, real_inner_self_eq_norm_sq]
        ring
      rw [h_eq]
      have h_lim : Filter.Tendsto (fun n ↦ inner ℝ (cs n • d n) (d n) * (-1 / 2)) l (𝓝 (inner ℝ y (0 : EN 2) * (-1 / 2))) :=
        Filter.Tendsto.mul (Filter.Tendsto.inner hcd hd0) tendsto_const_nhds
      have h_zero : inner ℝ y (0 : EN 2) * (-1 / 2) = 0 := by
        rw [inner_zero_right, zero_mul]
      rw [h_zero] at h_lim
      exact h_lim
    have h_lim_right_eq : Filter.Tendsto (fun n ↦ inner ℝ (x - E_to_EN2 x₀) (cs n • d n)) l (𝓝 0) :=
      Filter.Tendsto.congr' h_algebra.symm h_lim_right
    exact tendsto_nhds_unique h_lim_left h_lim_right_eq
  rw [h_zero, mul_zero]

lemma ball_outward_normal (x₀ : E) (r : ℝ) :
    IsOutwardUnitNormal (Metric.ball x₀ r) (fun x => (1 / r) • (x - x₀)) := by
  by_cases hr : (0 : ℝ) < r
  · unfold IsOutwardUnitNormal
    rw [image_ball_E_to_EN2]
    intro x hx
    unfold IsOutwardNormalAt
    simp_rw [E_to_EN2_ball_normal]
    have hx_sph : ‖x - E_to_EN2 x₀‖ = r := by
      have hx_sphere : x ∈ Metric.sphere (E_to_EN2 x₀) r := by
        rwa [frontier_ball (E_to_EN2 x₀) (ne_of_gt hr)] at hx
      exact Metric.mem_sphere.mp hx_sphere
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hx_sph, inv_mul_cancel₀ (ne_of_gt hr)]
    · intro y hy
      exact ball_normal_tangent_cone_orthogonal hr hx_sph hy
    · exact ball_normal_forward_ray_outside hr hx_sph
    · exact ball_normal_backward_ray_inside hr hx_sph
  · have h_empty : Metric.ball x₀ r = ∅ := Metric.ball_eq_empty.mpr (not_lt.mp hr)
    unfold IsOutwardUnitNormal IsOutwardNormal
    rw [h_empty, Set.image_empty, frontier_empty]
    intro x hx
    contradiction

theorem instHasPDEDomainBall (x₀ : E) (r : ℝ) (hr : 0 < r) : HasPDEDomain (Metric.ball x₀ r) where
  is_open := Metric.isOpen_ball
  is_connected := isConnected_ball hr
  unique_diff := by
    have h_closure : closure (Metric.ball x₀ r) = Metric.closedBall x₀ r := closure_ball x₀ hr.ne'
    rw [h_closure]
    refine uniqueDiffOn_convex ?_ ?_
    · exact convex_closedBall x₀ r
    · have h_nonempty : (Metric.ball x₀ r).Nonempty := Metric.nonempty_ball.mpr hr
      have h_subset : Metric.ball x₀ r ⊆ interior (Metric.closedBall x₀ r) :=
        interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      exact h_nonempty.mono h_subset
  has_normal := by
    use fun x => (1 / r) • (x - x₀)
    constructor
    · exact ball_outward_normal x₀ r
    · apply Continuous.continuousOn
      exact (continuous_id.sub continuous_const).const_smul (1 / r)

instance ball_has_div_domain (x₀ : E) (r : ℝ) :
    HasDivergenceTheoremDomain (Metric.ball x₀ r) := by
  constructor
  use fun x => (1 / r) • (x - x₀)
  constructor
  · exact ball_outward_normal x₀ r
  · apply Continuous.continuousOn
    exact (continuous_id.sub continuous_const).const_smul (1 / r)

lemma outward_normal_ball_exists (a : E) (ε : ℝ) :
  ∃ n_ball : E → E, IsOutwardUnitNormal (Metric.ball a ε) n_ball ∧ ContinuousOn n_ball (frontier (Metric.ball a ε)) := by
  use fun x => (1 / ε) • (x - a)
  constructor
  · exact ball_outward_normal a ε
  · apply Continuous.continuousOn
    exact (continuous_id.sub continuous_const).const_smul (1 / ε)

lemma isConnected_diff_closedBall (Ω : Set E) [HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  IsConnected (Ω \ Metric.closedBall x₀ ε) := by sorry

lemma uniqueDiffOn_diff_closedBall (Ω : Set E) [HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  UniqueDiffOn ℝ (closure (Ω \ Metric.closedBall x₀ ε)) := by sorry

lemma image_frontier_E_to_EN2 (S : Set E) :
  frontier (E_to_EN2 '' S) = E_to_EN2 '' frontier S := by
  have h_eq : E_to_EN2.toHomeomorph '' frontier S = frontier (E_to_EN2.toHomeomorph '' S) :=
    E_to_EN2.toHomeomorph.image_frontier S
  exact h_eq.symm

lemma hasNormal_diff_closedBall_outward (Ω : Set E) [HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
    (n_Ω : E → E) (hn_out : IsOutwardUnitNormal Ω n_Ω) :
    IsOutwardUnitNormal (Ω \ Metric.closedBall x₀ ε) (fun x => if x ∈ frontier Ω then n_Ω x else -(1 / ε) • (x - x₀)) := by
  unfold IsOutwardUnitNormal
  intro x hx
  rw [image_frontier_E_to_EN2] at hx
  rcases hx with ⟨x_orig, hx_orig, rfl⟩
  rw [frontier_diff_closedBall_gen Ω x₀ ε hε h_subset] at hx_orig
  rcases hx_orig with hx_omega | hx_sphere
  · have h_eq : (if x_orig ∈ frontier Ω then n_Ω x_orig else -(1 / ε) • (x_orig - x₀)) = n_Ω x_orig := if_pos hx_omega
    have h_symm : E_to_EN2.symm (E_to_EN2 x_orig) = x_orig := LinearIsometryEquiv.symm_apply_apply E_to_EN2 x_orig
    simp_rw [h_symm, h_eq]
    unfold IsOutwardUnitNormal at hn_out
    have hn_out_x := hn_out (E_to_EN2 x_orig) (by rw[image_frontier_E_to_EN2]; exact Set.mem_image_of_mem _ hx_omega)
    unfold IsOutwardNormalAt at hn_out_x ⊢
    dsimp only at hn_out_x
    rw [LinearIsometryEquiv.symm_apply_apply] at hn_out_x
    rcases hn_out_x with ⟨h_norm, h_ortho, h_out, h_in⟩
    refine ⟨h_norm, ?_, ?_, ?_⟩
    · sorry
    · filter_upwards [h_out] with t ht
      intro h_in_closure
      have h_subset_closure : closure (E_to_EN2 '' (Ω \ Metric.closedBall x₀ ε)) ⊆ closure (E_to_EN2 '' Ω) := by
        apply closure_mono
        exact Set.image_mono Set.sdiff_subset
      exact ht (h_subset_closure h_in_closure)
    · sorry
  · have h_not_omega : x_orig ∉ frontier Ω := Set.disjoint_right.mp (disjoint_frontier_sphere h_subset) hx_sphere
    have h_eq : (if x_orig ∈ frontier Ω then n_Ω x_orig else -(1 / ε) • (x_orig - x₀)) = -(1 / ε) • (x_orig - x₀) := if_neg h_not_omega
    have h_symm : E_to_EN2.symm (E_to_EN2 x_orig) = x_orig := LinearIsometryEquiv.symm_apply_apply E_to_EN2 x_orig
    simp_rw [h_symm, h_eq]
    unfold IsOutwardNormalAt
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [LinearIsometryEquiv.norm_map, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hε)]
      have hx_norm : ‖x_orig - x₀‖ = ε := Metric.mem_sphere.mp hx_sphere
      rw [hx_norm, div_mul_cancel₀ 1 (ne_of_gt hε)]
    · sorry
    · sorry
    · sorry

lemma hasNormal_diff_closedBall_continuous (Ω : Set E) [HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω)
    (n_Ω : E → E) (hn_cont : ContinuousOn n_Ω (frontier Ω)) :
    ContinuousOn (fun x => if x ∈ frontier Ω then n_Ω x else -(1 / ε) • (x - x₀)) (frontier Ω ∪ Metric.sphere x₀ ε) := by
  sorry

lemma hasNormal_diff_closedBall (Ω : Set E) [hΩ : HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  ∃ n : E → E, IsOutwardUnitNormal (Ω \ Metric.closedBall x₀ ε) n ∧ ContinuousOn n (frontier (Ω \ Metric.closedBall x₀ ε)) := by
  rcases hΩ.has_normal with ⟨n_Ω, hn_out, hn_cont⟩
  use fun x => if x ∈ frontier Ω then n_Ω x else -(1 / ε) • (x - x₀)
  constructor
  · exact hasNormal_diff_closedBall_outward Ω x₀ ε hε h_subset n_Ω hn_out
  · rw [frontier_diff_closedBall_gen Ω x₀ ε hε h_subset]
    exact hasNormal_diff_closedBall_continuous Ω x₀ ε hε h_subset n_Ω hn_cont


theorem annulus_has_pde_domain (Ω : Set E) [hΩ : HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  HasPDEDomain (Ω \ Metric.closedBall x₀ ε) where
  is_open := hΩ.is_open.sdiff isClosed_closedBall
  is_connected := isConnected_diff_closedBall Ω x₀ ε hε h_subset
  unique_diff := uniqueDiffOn_diff_closedBall Ω x₀ ε hε h_subset
  has_normal := hasNormal_diff_closedBall Ω x₀ ε hε h_subset

theorem annulus_has_pde_domain_gen (Ω : Set E) [hΩ : HasPDEDomain Ω] (x₀ : E) (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall x₀ ε ⊆ Ω) :
  HasPDEDomain (Ω \ Metric.closedBall x₀ ε) :=
  annulus_has_pde_domain Ω x₀ ε hε h_subset

lemma hasNormal_diff_ball_outward (Ω : Set E) [HasPDEDomain Ω] (ε : ℝ)
    (n_Ω : E → E) (hn_out : IsOutwardUnitNormal Ω n_Ω) :
    IsOutwardUnitNormal (Ω \ Metric.ball (0 : E) ε) (fun x => if x ∈ frontier Ω then n_Ω x else -(1 / ε) • x) := by
  sorry

lemma hasNormal_diff_ball_continuous (Ω : Set E) [HasPDEDomain Ω] (ε : ℝ)
    (n_Ω : E → E) (hn_cont : ContinuousOn n_Ω (frontier Ω)) :
    ContinuousOn (fun x => if x ∈ frontier Ω then n_Ω x else -(1 / ε) • x) (frontier (Ω \ Metric.ball (0 : E) ε)) := by
  sorry

lemma hasNormal_diff_ball (Ω : Set E) [hΩ : HasPDEDomain Ω] (ε : ℝ) :
  ∃ n : E → E, IsOutwardUnitNormal (Ω \ Metric.ball (0 : E) ε) n ∧ ContinuousOn n (frontier (Ω \ Metric.ball (0 : E) ε)) := by
  rcases hΩ.has_normal with ⟨n_Ω, hn_out, hn_cont⟩
  use fun x => if x ∈ frontier Ω then n_Ω x else -(1 / ε) • x
  constructor
  · exact hasNormal_diff_ball_outward Ω ε n_Ω hn_out
  · exact hasNormal_diff_ball_continuous Ω ε n_Ω hn_cont

instance annulus_has_div_domain (Ω : Set E) [HasPDEDomain Ω] (ε : ℝ) :
  HasDivergenceTheoremDomain (Ω \ Metric.ball (0 : E) ε) := by
  constructor
  exact hasNormal_diff_ball Ω ε

lemma frontier_diff_ball_gen (Ω : Set E) [HasPDEDomain Ω] (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall (0 : E) ε ⊆ Ω) :
    frontier (Ω \ Metric.ball (0 : E) ε) = frontier Ω ∪ Metric.sphere (0 : E) ε := by
  sorry

lemma tangentCone_frontier_diff_ball_omega {Ω : Set E} [HasPDEDomain Ω] (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall (0 : E) ε ⊆ Ω) {x : E} (hx : x ∈ frontier Ω) :
    tangentConeAt ℝ (frontier (E_to_EN2 '' (Ω \ Metric.ball (0 : E) ε))) (E_to_EN2 x) =
    tangentConeAt ℝ (frontier (E_to_EN2 '' Ω)) (E_to_EN2 x) := by
  sorry

lemma ray_inside_diff_ball {Ω : Set E} [HasPDEDomain Ω] (ε : ℝ) (h_subset : Metric.closedBall (0 : E) ε ⊆ Ω) {x : E} (hx : x ∈ frontier Ω) {v : E} (h_in : ∀ᶠ (t : ℝ) in 𝓝[>] 0, E_to_EN2 x - t • E_to_EN2 v ∈ E_to_EN2 '' Ω) :
    ∀ᶠ (t : ℝ) in 𝓝[>] 0, E_to_EN2 x - t • E_to_EN2 v ∈ E_to_EN2 '' (Ω \ Metric.ball (0 : E) ε) := by
  sorry

lemma sphere_normal_tangent_cone_orthogonal_diff_ball {Ω : Set E} [HasPDEDomain Ω] (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall (0 : E) ε ⊆ Ω) {x : E} (hx : x ∈ Metric.sphere (0 : E) ε) {y : EN 2} (hy : y ∈ tangentConeAt ℝ (frontier (E_to_EN2 '' (Ω \ Metric.ball (0 : E) ε))) (E_to_EN2 x)) :
    inner ℝ (E_to_EN2 (-(1 / ε) • x)) y = 0 := by
  sorry

lemma sphere_normal_forward_ray_outside_diff_ball {Ω : Set E} [HasPDEDomain Ω] (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall (0 : E) ε ⊆ Ω) {x : E} (hx : x ∈ Metric.sphere (0 : E) ε) :
    ∀ᶠ (t : ℝ) in 𝓝[>] 0, E_to_EN2 x + t • E_to_EN2 (-(1 / ε) • x) ∉ closure (E_to_EN2 '' (Ω \ Metric.ball (0 : E) ε)) := by
  sorry

lemma sphere_normal_backward_ray_inside_diff_ball {Ω : Set E} [HasPDEDomain Ω] (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall (0 : E) ε ⊆ Ω) {x : E} (hx : x ∈ Metric.sphere (0 : E) ε) :
    ∀ᶠ (t : ℝ) in 𝓝[>] 0, E_to_EN2 x - t • E_to_EN2 (-(1 / ε) • x) ∈ E_to_EN2 '' (Ω \ Metric.ball (0 : E) ε) := by
  sorry

lemma normal_diff_ball (Ω : Set E) [HasPDEDomain Ω] (ε : ℝ) (hε : 0 < ε) (h_subset : Metric.closedBall (0 : E) ε ⊆ Ω)
    (n_Ω : E → E) (hn_out : IsOutwardUnitNormal Ω n_Ω) :
    IsOutwardUnitNormal (Ω \ Metric.ball (0 : E) ε) (fun x => if x ∈ frontier Ω then n_Ω x else -(1 / ε) • x) := by
  unfold IsOutwardUnitNormal
  intro x hx
  rw [image_frontier_E_to_EN2] at hx
  rcases hx with ⟨x_orig, hx_orig, rfl⟩
  rw [frontier_diff_ball_gen Ω ε hε h_subset] at hx_orig
  rcases hx_orig with hx_omega | hx_sphere
  · have h_eq : (if x_orig ∈ frontier Ω then n_Ω x_orig else -(1 / ε) • x_orig) = n_Ω x_orig := if_pos hx_omega
    have h_symm : E_to_EN2.symm (E_to_EN2 x_orig) = x_orig := LinearIsometryEquiv.symm_apply_apply E_to_EN2 x_orig
    simp_rw [h_symm, h_eq]
    unfold IsOutwardUnitNormal at hn_out
    have hn_out_x := hn_out (E_to_EN2 x_orig) (by rw [image_frontier_E_to_EN2]; exact Set.mem_image_of_mem _ hx_omega)
    unfold IsOutwardNormalAt at hn_out_x ⊢
    dsimp only at hn_out_x
    rw [LinearIsometryEquiv.symm_apply_apply] at hn_out_x
    rcases hn_out_x with ⟨h_norm, h_ortho, h_out, h_in⟩
    refine ⟨h_norm, ?_, ?_, ?_⟩
    · intro y hy
      rw [tangentCone_frontier_diff_ball_omega ε hε h_subset hx_omega] at hy
      exact h_ortho y hy
    · filter_upwards [h_out] with t ht
      intro h_in_closure
      have h_subset_closure : closure (E_to_EN2 '' (Ω \ Metric.ball (0 : E) ε)) ⊆ closure (E_to_EN2 '' Ω) := by
        apply closure_mono
        exact Set.image_mono Set.sdiff_subset
      exact ht (h_subset_closure h_in_closure)
    · exact ray_inside_diff_ball ε h_subset hx_omega h_in
  · have h_not_omega : x_orig ∉ frontier Ω := Set.disjoint_right.mp (disjoint_frontier_sphere h_subset) hx_sphere
    have h_eq : (if x_orig ∈ frontier Ω then n_Ω x_orig else -(1 / ε) • x_orig) = -(1 / ε) • x_orig := if_neg h_not_omega
    have h_symm : E_to_EN2.symm (E_to_EN2 x_orig) = x_orig := LinearIsometryEquiv.symm_apply_apply E_to_EN2 x_orig
    simp_rw [h_symm, h_eq]
    unfold IsOutwardNormalAt
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [LinearIsometryEquiv.norm_map, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hε)]
      have hx_norm : ‖x_orig - 0‖ = ε := Metric.mem_sphere.mp hx_sphere
      rw [sub_zero] at hx_norm
      rw [hx_norm, div_mul_cancel₀ 1 (ne_of_gt hε)]
    · intro y hy
      exact sphere_normal_tangent_cone_orthogonal_diff_ball ε hε h_subset hx_sphere hy
    · exact sphere_normal_forward_ray_outside_diff_ball ε hε h_subset hx_sphere
    · exact sphere_normal_backward_ray_inside_diff_ball ε hε h_subset hx_sphere

lemma isConnected_diff_two_closedBalls (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  IsConnected (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) := by sorry

lemma uniqueDiffOn_diff_two_closedBalls (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  UniqueDiffOn ℝ (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) := by sorry

lemma hasNormal_diff_two_closedBalls (Ω : Set E) [hΩ : HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  ∃ n : E → E, IsOutwardUnitNormal (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) n ∧ ContinuousOn n (frontier (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) := by
  sorry

def double_annulus_has_pde_domain (Ω : Set E) [hΩ : HasPDEDomain Ω]
  (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  HasPDEDomain (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) where
  is_open := hΩ.is_open.sdiff (isClosed_closedBall.union isClosed_closedBall)
  is_connected := isConnected_diff_two_closedBalls Ω a b ε hε ha_subset hb_subset h_disjoint
  unique_diff := uniqueDiffOn_diff_two_closedBalls Ω a b ε hε ha_subset hb_subset h_disjoint
  has_normal := hasNormal_diff_two_closedBalls Ω a b ε hε ha_subset hb_subset h_disjoint

lemma normal_exists_punctured (Ω : Set E) [HasPDEDomain Ω] (a b : E) :
  ∀ ε > 0, Metric.closedBall a ε ⊆ Ω → Metric.closedBall b ε ⊆ Ω → Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε) →
  ∃ n : E → E, IsOutwardUnitNormal (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) n ∧ ContinuousOn n (frontier (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) := by
  intro ε hε ha_subset hb_subset h_disjoint
  exact hasNormal_diff_two_closedBalls Ω a b ε hε ha_subset hb_subset h_disjoint
