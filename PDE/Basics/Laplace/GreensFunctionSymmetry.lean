import PDE.Basics.Laplace.GreensFunction

open MeasureTheory Metric Set InnerProductSpace RealInnerProductSpace Topology Filter

lemma harmonic_le_zero_of_zero_boundary {Ω : Set E} [HasPDEDomain Ω] (hBounded : Bornology.IsBounded Ω)
    {u : E → ℝ} (h_cont : ContinuousOn u (closure Ω)) (h_diff : ContDiffOn ℝ 2 u Ω)
    (h_harm : IsHarmonic u Ω) (h_bdry : ∀ x ∈ frontier Ω, u x = 0) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∀ x ∈ closure Ω, u x ≤ 0 := by
  obtain ⟨x_max, hx_max_in, hx_max_prop⟩ := IsCompact.exists_isMaxOn
    (Bornology.IsBounded.isCompact_closure hBounded) ⟨x₀, subset_closure hx₀⟩ h_cont
  refine fun x hx ↦ (hx_max_prop hx).trans ?_
  rcases closure_subset_union_frontier Ω hx_max_in with h_in | h_bdry_case
  · obtain ⟨x_bdry, hx_bdry⟩ := frontier_nonempty_of_bounded_open_nonempty HasPDEDomain.is_open hBounded ⟨x₀, hx₀⟩
    have h_eq := Set.EqOn.of_subset_closure
      (maximum_principle HasPDEDomain.is_open HasPDEDomain.is_connected h_harm h_diff h_cont x_max h_in hx_max_prop)
      h_cont continuousOn_const subset_closure (fun _ hx ↦ hx)
    exact le_of_eq <| (h_eq (mem_of_mem_inter_left hx_bdry)).symm.trans (h_bdry x_bdry hx_bdry)
  · exact le_of_eq (h_bdry x_max h_bdry_case)

lemma harmonic_zero_of_zero_boundary {Ω : Set E} [HasPDEDomain Ω] (hBounded : Bornology.IsBounded Ω)
    {u : E → ℝ} (h_cont : ContinuousOn u (closure Ω)) (h_diff : ContDiffOn ℝ 2 u Ω)
    (h_harm : IsHarmonic u Ω) (h_bdry : ∀ x ∈ frontier Ω, u x = 0) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∀ x ∈ closure Ω, u x = 0 := fun x hx ↦
  le_antisymm (harmonic_le_zero_of_zero_boundary hBounded h_cont h_diff h_harm h_bdry hx₀ x hx)
    (neg_nonpos.mp (harmonic_le_zero_of_zero_boundary hBounded (ContinuousOn.neg h_cont)
      (ContDiffOn.neg h_diff) (isHarmonic_neg HasPDEDomain.is_open h_harm)
      (fun y hy ↦ by change - u y = 0; rw [h_bdry y hy, neg_zero]) hx₀ x hx))

theorem greens_function_unique {Ω : Set E} [HasPDEDomain Ω] (hBounded : Bornology.IsBounded Ω)
    {G₁ G₂ : E → E → ℝ} (hG₁ : IsGreensFunction G₁ Ω) (hG₂ : IsGreensFunction G₂ Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∀ x ∈ closure Ω \ {x₀}, G₁ x x₀ = G₂ x x₀ := by
  obtain ⟨H₁, hH₁_cont, hH₁_diff, hH₁_harm, hH₁_G, hH₁_G_bdry, hH₁_bdry⟩ := hG₁ x₀ hx₀
  obtain ⟨H₂, hH₂_cont, hH₂_diff, hH₂_harm, hH₂_G, hH₂_G_bdry, hH₂_bdry⟩ := hG₂ x₀ hx₀
  have hF_zero : ∀ x ∈ closure Ω, H₁ x - H₂ x = 0 :=
    harmonic_zero_of_zero_boundary hBounded (ContinuousOn.sub hH₁_cont hH₂_cont)
      (ContDiffOn.sub (hH₁_diff.of_le le_top) (hH₂_diff.of_le le_top))
      (fun x hx ↦ by
        have h2 := contDiffAt_of_contDiffOn_top HasPDEDomain.is_open x hx hH₂_diff
        have h_add := laplacian_add (fun y ↦ H₁ y - H₂ y) H₂ x
          (ContDiffAt.sub (contDiffAt_of_contDiffOn_top HasPDEDomain.is_open x hx hH₁_diff) h2) h2
        rw [funext (fun y ↦ sub_add_cancel (H₁ y) (H₂ y))] at h_add
        rw [eq_sub_of_add_eq h_add.symm, hH₁_harm x hx, hH₂_harm x hx, sub_zero])
      (fun x hx ↦ sub_eq_zero.mpr ((hH₁_bdry x hx).trans (hH₂_bdry x hx).symm)) hx₀
  rintro x ⟨hx_cl, hx_ne⟩
  rcases closure_subset_union_frontier Ω hx_cl with h_in | h_bdry
  · rw [hH₁_G x ⟨h_in, hx_ne⟩, hH₂_G x ⟨h_in, hx_ne⟩, sub_eq_zero.mp (hF_zero x hx_cl)]
  · rw [hH₁_G_bdry x h_bdry, hH₂_G_bdry x h_bdry]

lemma isHarmonic_greens_punctured {Ω : Set E} [HasPDEDomain Ω] {G : E → E → ℝ}
  (hG : IsGreensFunction G Ω) {c : E} (hc : c ∈ Ω) :
  IsHarmonic (fun y ↦ G y c) (Ω \ {c}) := by
  obtain ⟨H_c, _, hHc_diff, hHc_harm, hHc_G, _, _⟩ := hG c hc
  intro x hx
  have h_open : IsOpen (Ω \ {c}) := IsOpen.sdiff HasPDEDomain.is_open isClosed_singleton
  rw [laplacian_congr (Filter.eventuallyEq_of_mem (h_open.mem_nhds hx) hHc_G),
    laplacian_add _ _ _ (contDiffAt_fundamental_sol_3d c x hx.2)
    (contDiffAt_of_contDiffOn_top HasPDEDomain.is_open x hx.1 hHc_diff)]
  simp [fundamental_sol_3d_laplacian hx.2, hHc_harm x hx.1]

lemma laplacian_eq_zero_ball_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (hb : b ∈ Ω)
  (v : E → ℝ) (hv : v = fun y ↦ G y b)
  (H_a : E → ℝ) (hHa_harm : IsHarmonic H_a Ω) :
  Set.EqOn (fun x ↦ H_a x * laplacian v x - v x * laplacian H_a x) (fun _ ↦ 0) (Metric.ball a ε) := by
  intro x hx
  have hx_ne_b : x ≠ b := fun e ↦ Set.disjoint_left.mp h_disjoint (Metric.ball_subset_closedBall hx) (e ▸ Metric.mem_closedBall_self hε.le)
  have h_lap_v : laplacian v x = 0 := by
    rw [hv]
    exact isHarmonic_greens_punctured hG hb x ⟨ha_subset (Metric.ball_subset_closedBall hx), hx_ne_b⟩
  have h_lap_Ha : laplacian H_a x = 0 := hHa_harm x (ha_subset (Metric.ball_subset_closedBall hx))
  simp_rw [h_lap_v, h_lap_Ha]
  ring

lemma contDiffOn_greens_punctured {Ω : Set E} [HasPDEDomain Ω] {G : E → E → ℝ}
  (hG : IsGreensFunction G Ω) {c : E} (hc : c ∈ Ω) {S : Set E}
  (hS_sub : S ⊆ Ω) (hc_notin : c ∉ S) :
  ContDiffOn ℝ 2 (fun y ↦ G y c) S := by
  obtain ⟨H_c, _, hHc_diff, _, hGc_eq, _, _⟩ := hG c hc
  refine ContDiffOn.congr (ContDiffOn.add ?_ ((hHc_diff.of_le le_top).mono hS_sub)) fun y hy ↦ hGc_eq y ⟨hS_sub hy, fun e ↦ hc_notin (e ▸ hy)⟩
  unfold fundamental_sol_3d
  exact ContDiffOn.div contDiffOn_const
    (ContDiffOn.mul contDiffOn_const (ContDiffOn.norm ℝ (ContDiffOn.sub contDiffOn_id contDiffOn_const) fun x hx h_eq ↦ hc_notin (sub_eq_zero.mp h_eq ▸ hx)))
    (fun x hx h_eq ↦ hc_notin (sub_eq_zero.mp (norm_eq_zero.mp ((mul_eq_zero.mp h_eq).resolve_left (by positivity))) ▸ hx))

lemma contDiffOn_punctured_u (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  {G : E → E → ℝ} (hG : IsGreensFunction G Ω) (ha : a ∈ Ω) :
  ContDiffOn ℝ 2 (fun y ↦ G y a) (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) :=
  contDiffOn_greens_punctured hG ha Set.sdiff_subset fun h ↦ h.2 (Or.inl (Metric.mem_closedBall_self hε.le))

lemma contDiffOn_punctured_v (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  {G : E → E → ℝ} (hG : IsGreensFunction G Ω) (hb : b ∈ Ω) :
  ContDiffOn ℝ 2 (fun y ↦ G y b) (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) :=
  contDiffOn_greens_punctured hG hb Set.sdiff_subset fun h ↦ h.2 (Or.inr (Metric.mem_closedBall_self hε.le))

-- Abstracted metric/measure properties

-- Abstracted fundamental solution differentiability
lemma differentiableAt_fund_sphere (c : E) (ε : ℝ) (hε : 0 < ε) (x : E) (hx : x ∈ Metric.sphere c ε) :
  DifferentiableAt ℝ (fun y ↦ fundamental_sol_3d (y - c)) x := by
  have hx_ne_c : x ≠ c := by intro h_eq; rw [h_eq] at hx; linarith [Metric.mem_sphere.mp hx, dist_self c]
  exact (contDiffAt_fundamental_sol_3d c x hx_ne_c).differentiableAt (by decide)

-- Abstracted subset closure for a punctured domain (uses generic c and d
-- Abstracted integrability over a generic sphere c inside the double annulus

lemma v_diff_at_sphere (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b) (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (v : E → ℝ) (hv : v = fun y ↦ G y b)
  (h_ball_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_ball_subset : Metric.closedBall b ε ⊆ Ω)
  (x : E) (hx : x ∈ Metric.sphere a ε) :
  DifferentiableAt ℝ v x := by
  have hb_omega : b ∈ Ω := hb_ball_subset (Metric.mem_closedBall_self hε.le)
  obtain ⟨H_b, _, hH_diff, _, hGc_eq, _, _⟩ := hG b hb_omega
  have h_open : IsOpen (Ω \ {b}) := HasPDEDomain.is_open.sdiff isClosed_singleton
  have hx_ne_b : x ≠ b := by
    intro h_eq
    have h_xa : dist a x = ε := mem_sphere'.mp hx
    linarith [show dist a b = ε by rw [← h_eq]; exact h_xa]
  have hx_nhds : Ω \ {b} ∈ nhds x := IsOpen.mem_nhds h_open ⟨h_ball_subset (Metric.sphere_subset_closedBall hx), hx_ne_b⟩
  refine DifferentiableAt.congr_of_eventuallyEq (DifferentiableAt.add ?_ ?_) (Filter.eventuallyEq_of_mem hx_nhds (by intro y hy; rw [hv]; exact hGc_eq y hy))
  · refine diff_Phi_at b x (fun h_eq ↦ hx_ne_b (sub_eq_zero.mp h_eq)) fundamental_sol_3d (by exact fun y ↦ rfl)
  · exact ((hH_diff.of_le le_top).differentiableOn (by exact ne_zero_of_eq_one rfl)).differentiableAt (IsOpen.mem_nhds HasPDEDomain.is_open (h_ball_subset (Metric.sphere_subset_closedBall hx)))

lemma differentiableAt_fund_sphere_b (b : E) (ε : ℝ) (hε : 0 < ε) (x : E) (hx : x ∈ Metric.sphere b ε) :
  DifferentiableAt ℝ (fun y ↦ fundamental_sol_3d (y - b)) x :=
  differentiableAt_fund_sphere b ε hε x hx

lemma gradientWithin_greens_eq_gradient (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b) (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (v : E → ℝ) (hv : v = fun y ↦ G y b)
  (h_ball_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_ball_subset : Metric.closedBall b ε ⊆ Ω) :
  ∀ x ∈ Metric.sphere a ε, gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x = gradient v x := by
  intro x hx
  exact gradientWithin_eq_gradient_of_differentiableAt v _ x
    (v_diff_at_sphere Ω a b ε hε h_dist_ab G hG v hv h_ball_subset hb_ball_subset x hx)
    (uniqueDiffWithinAt_punctured_sphere Ω a b ε hε h_dist_ab h_ball_subset hb_ball_subset x hx)

lemma contDiffOn_grad_fund_ball (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b) :
  ContDiffOn ℝ 1 (fun y ↦ gradient (fun z ↦ fundamental_sol_3d (z - b)) y) (closure (Metric.ball a ε)) := by
  intro y hy
  have hy_closed : y ∈ Metric.closedBall a ε := closure_minimal Metric.ball_subset_closedBall isClosed_closedBall hy
  have hy_ne_b : y ≠ b := fun e ↦ by linarith [show dist a b ≤ ε from Metric.mem_closedBall'.mp (e ▸ hy_closed), hε]
  let c : (E →L[ℝ] ℝ) →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact (ContDiffAt.continuousLinearMap_comp c ((contDiffAt_fundamental_sol_3d b y hy_ne_b).fderiv_right le_rfl)).contDiffWithinAt

lemma contDiffOn_1_G_cross_ball (Ω : Set E) [HasPDEDomain Ω] (p q : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_pq : 2 * ε < dist p q) (hp_subset : Metric.closedBall p ε ⊆ Ω) (hq_subset : Metric.closedBall q ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) :
  ContDiffOn ℝ 1 (fun y ↦ G y p) (closure (Metric.ball q ε)) := by
  obtain ⟨H_p, _, hHp_diff, _, hHp_G, _, _⟩ := hG p (hp_subset (Metric.mem_closedBall_self hε.le))
  have h_ne : ∀ x ∈ Metric.closedBall q ε, x - p ≠ 0 := fun x hx h_zero => by
    have h_dist : dist q p ≤ ε := by rw [← sub_eq_zero.mp h_zero]; exact Metric.mem_closedBall.mp (by exact mem_closedBall_comm.mp hx)
    have h_dist_qp : 2 * ε < dist q p := by rw [dist_comm]; exact h_dist_pq
    linarith [h_dist_qp, h_dist, hε]
  have h_fund_diff : ContDiffOn ℝ 1 (fun y ↦ fundamental_sol_3d (y - p)) (Metric.closedBall q ε) := by
    have h_eq : ∀ y ∈ Metric.closedBall q ε, (fun z ↦ (-1 : ℝ) / (4 * Real.pi) * ‖z - p‖⁻¹) y = fundamental_sol_3d (y - p) := fun y hy => by
      unfold fundamental_sol_3d
      field_simp [norm_ne_zero_iff.mpr (h_ne y hy), ne_of_gt Real.pi_pos]
    exact ContDiffOn.congr (ContDiffOn.mul contDiffOn_const (ContDiffOn.inv (ContDiffOn.norm ℝ (ContDiffOn.sub contDiffOn_id contDiffOn_const) h_ne) fun x hx => norm_ne_zero_iff.mpr (h_ne x hx))) (by
    exact fun x a ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h_eq (id x) a))))
  refine ContDiffOn.mono (ContDiffOn.congr (ContDiffOn.add h_fund_diff ((hHp_diff.of_le le_top).mono hq_subset)) fun x hx => ?_) closure_ball_subset_closedBall
  exact (hHp_G x ⟨hq_subset hx, fun h => h_ne x hx (sub_eq_zero.mpr h)⟩)


lemma continuousOn_G_cross_closure_ball (Ω : Set E) [HasPDEDomain Ω] (p q : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_pq : 2 * ε < dist p q) (hp_subset : Metric.closedBall p ε ⊆ Ω) (hq_subset : Metric.closedBall q ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) :
  ContinuousOn (fun y ↦ G y p) (closure (Metric.ball q ε)) := by
  obtain ⟨H_p, hHp_cont, _, _, hHp_G, _, _⟩ := hG p (hp_subset (Metric.mem_closedBall_self hε.le))
  have h_ne : ∀ x ∈ Metric.closedBall q ε, x - p ≠ 0 := fun x hx h_zero => by
    have h_dist : dist q p ≤ ε := by rw [← sub_eq_zero.mp h_zero]; exact Metric.mem_closedBall.mp (by exact mem_closedBall_comm.mp hx)
    have h_dist_qp : 2 * ε < dist q p := by rw [dist_comm]; exact h_dist_pq
    linarith [h_dist_qp, h_dist, hε]
  have h_fund_cont : ContinuousOn (fun y ↦ fundamental_sol_3d (y - p)) (Metric.closedBall q ε) := by
    have h_eq : ∀ y ∈ Metric.closedBall q ε, (fun z ↦ (-1 : ℝ) / (4 * Real.pi) * ‖z - p‖⁻¹) y = fundamental_sol_3d (y - p) := fun y hy => by
      unfold fundamental_sol_3d
      field_simp [norm_ne_zero_iff.mpr (h_ne y hy), ne_of_gt Real.pi_pos]
    exact ContinuousOn.congr (ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (Continuous.continuousOn (Continuous.norm (Continuous.sub continuous_id continuous_const))) fun x hx => norm_ne_zero_iff.mpr (h_ne x hx))) (by exact fun x hx ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h_eq x hx))))
  refine ContinuousOn.mono (ContinuousOn.congr (ContinuousOn.add h_fund_cont (hHp_cont.mono fun x hx => subset_closure (hq_subset hx))) fun x hx => ?_) closure_ball_subset_closedBall
  exact (hHp_G x ⟨hq_subset hx, fun h => h_ne x hx (sub_eq_zero.mpr h)⟩)


lemma continuousOn_G_cross_closedBall (Ω : Set E) [HasPDEDomain Ω] (p q : E) (ε : ℝ) (hε : 0 < ε)
  (hp_subset : Metric.closedBall p ε ⊆ Ω) (hq_subset : Metric.closedBall q ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall p ε) (Metric.closedBall q ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) :
  ContinuousOn (fun y ↦ G y p) (Metric.closedBall q ε) := by
  obtain ⟨H_p, hHp_cont, _, _, hHp_G, _, _⟩ := hG p (hp_subset (Metric.mem_closedBall_self hε.le))
  have h_ne : ∀ x ∈ Metric.closedBall q ε, x - p ≠ 0 := fun x hx h_zero => by
    have hp_in_q : p ∈ Metric.closedBall q ε := by rw [← sub_eq_zero.mp h_zero]; exact hx
    exact Set.disjoint_right.mp h_disjoint hp_in_q (Metric.mem_closedBall_self hε.le)
  have h_fund_cont : ContinuousOn (fun y ↦ fundamental_sol_3d (y - p)) (Metric.closedBall q ε) := by
    have h_eq : ∀ y ∈ Metric.closedBall q ε, (fun z ↦ (-1 : ℝ) / (4 * Real.pi) * ‖z - p‖⁻¹) y = fundamental_sol_3d (y - p) := fun y hy => by
      unfold fundamental_sol_3d
      field_simp [norm_ne_zero_iff.mpr (h_ne y hy), ne_of_gt Real.pi_pos]
    exact ContinuousOn.congr (ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (Continuous.continuousOn (Continuous.norm (Continuous.sub continuous_id continuous_const))) fun x hx => norm_ne_zero_iff.mpr (h_ne x hx))) (by exact fun x hx ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h_eq x hx))))
  refine ContinuousOn.congr (ContinuousOn.add h_fund_cont (hHp_cont.mono fun x hx => subset_closure (hq_subset hx))) fun x hx => ?_
  exact (hHp_G x ⟨hq_subset hx, fun h => h_ne x hx (sub_eq_zero.mpr h)⟩)

lemma isHarmonic_G_punctured_pole (Ω : Set E) [HasPDEDomain Ω] (a b p : E) (ε : ℝ) (hε : 0 < ε)
  (hp_in_domain : p ∈ Ω) (hp_eq : p = a ∨ p = b) (G : E → E → ℝ) (hG : IsGreensFunction G Ω) :
  IsHarmonic (fun y ↦ G y p) (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) := by
  intro x hx
  exact isHarmonic_greens_punctured hG hp_in_domain x ⟨hx.1, fun e ↦ hx.2 (hp_eq.elim (fun h_eq ↦ Or.inl (e ▸ h_eq ▸ Metric.mem_closedBall_self hε.le)) (fun h_eq ↦ Or.inr (e ▸ h_eq ▸ Metric.mem_closedBall_self hε.le)))⟩

lemma u_harm_punctured (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  {G : E → E → ℝ} (hG : IsGreensFunction G Ω) (ha : a ∈ Ω) :
  IsHarmonic (fun y ↦ G y a) (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) :=
  isHarmonic_G_punctured_pole Ω a b a ε hε ha (Or.inl rfl) G hG

lemma v_harm_punctured (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  {G : E → E → ℝ} (hG : IsGreensFunction G Ω) (hb : b ∈ Ω) :
  IsHarmonic (fun y ↦ G y b) (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) :=
  isHarmonic_G_punctured_pole Ω a b b ε hε hb (Or.inr rfl) G hG

lemma differentiableAt_fundamental_sol_3d_sub (b y : E) (hy_ne_b : y ≠ b) :
  DifferentiableAt ℝ (fun z ↦ fundamental_sol_3d (z - b)) y := by
  unfold fundamental_sol_3d
  have h_sub : y - b ≠ 0 := sub_ne_zero.mpr hy_ne_b
  refine DifferentiableAt.mul (differentiableAt_const (-1 : ℝ)) (DifferentiableAt.inv ?_ ?_)
  · exact DifferentiableAt.mul (differentiableAt_const (4 * Real.pi)) (DifferentiableAt.norm ℝ (DifferentiableAt.sub differentiableAt_id (differentiableAt_const b)) h_sub)
  · exact ne_of_gt (mul_pos (by positivity) (norm_pos_iff.mpr h_sub))

lemma gradient_greens_punctured (Ω : Set E) [HasPDEDomain Ω] {G : E → E → ℝ} {b : E}
  (H_b : E → ℝ) (hG_eq : ∀ x ∈ Ω \ {b}, G x b = fundamental_sol_3d (x - b) + H_b x)
  (hH_diff : ContDiffOn ℝ 2 H_b Ω) {y : E} (hy_omega : y ∈ Ω) (hy_ne_b : y ≠ b) :
  gradient (fun z ↦ G z b) y = gradient (fun z ↦ fundamental_sol_3d (z - b)) y + gradient H_b y := by
  have h_nhds : (fun z ↦ G z b) =ᶠ[nhds y] (fun z ↦ fundamental_sol_3d (z - b) + H_b z) := by
    filter_upwards [(IsOpen.sdiff HasPDEDomain.is_open isClosed_singleton).mem_nhds ⟨hy_omega, hy_ne_b⟩] with z hz
    exact hG_eq z hz
  rw [h_nhds.gradient_eq]
  exact gradient_add (differentiableAt_fundamental_sol_3d_sub b y hy_ne_b) ((hH_diff.differentiableOn (by decide)).differentiableAt (HasPDEDomain.is_open.mem_nhds hy_omega))

lemma contDiffOn_gradient_greens_ball (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b) (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (v : E → ℝ) (hv : v = fun y ↦ G y b)
  (h_ball_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_ball_subset : Metric.closedBall b ε ⊆ Ω) :
  ContDiffOn ℝ 1 (gradient v) (closure (Metric.ball a ε)) := by
  obtain ⟨H_b, _, hH_diff, _, hG_eq, _, _⟩ := hG b (hb_ball_subset (Metric.mem_closedBall_self hε.le))
  have h_sub_punct := closure_ball_subset_punctured_omega Ω a b ε hε h_dist_ab h_ball_subset
  refine ContDiffOn.congr (ContDiffOn.add (contDiffOn_grad_fund_ball a b ε hε h_dist_ab) (contDiffOn_grad_Hb_ball Ω a ε h_ball_subset H_b (hH_diff.of_le le_top))) ?_
  intro y hy
  rw [hv]
  exact gradient_greens_punctured Ω H_b hG_eq (hH_diff.of_le le_top) (h_sub_punct hy).1 (h_sub_punct hy).2
------------------------------------------------------------------------------------

lemma integrand_algebra_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (n : E → E) (H_a u v : E → ℝ)
  (h_u_val : ∀ x ∈ Metric.sphere a ε, u x = fundamental_sol_3d (x - a) + H_a x)
  (h_grad_u : ∀ x ∈ Metric.sphere a ε, gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x =
    gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x +
    gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) :
  ∀ x ∈ Metric.sphere a ε,
    (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) =
    (fundamental_sol_3d (x - a) * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) +
    (H_a x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) -
    (v x * ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) :=
  fun x hx ↦ by rw [h_u_val x hx, h_grad_u x hx, inner_add_left]; ring

lemma integrable_fund_grad_v_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (v : E → ℝ) (n : E → E)
  (h_finite_area : surfaceArea (Metric.sphere a ε) ≠ ⊤)
  (h_cont_fund : ContinuousOn (fun x ↦ fundamental_sol_3d (x - a)) (Metric.sphere a ε))
  (h_cont_n : ContinuousOn n (Metric.sphere a ε))
  (h_cont_grad_v : ContinuousOn (fun x ↦ gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε)) :
  IntegrableOn (fun x ↦ fundamental_sol_3d (x - a) * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere a ε) surfaceArea := by
  exact integrableOn_compact_surface_of_continuousOn (isCompact_sphere a ε) h_finite_area _ (ContinuousOn.mul h_cont_fund (ContinuousOn.inner h_cont_grad_v h_cont_n))

lemma integrable_v_grad_fund_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (v : E → ℝ) (n : E → E)
  (h_finite_area : surfaceArea (Metric.sphere a ε) ≠ ⊤)
  (h_cont_v : ContinuousOn v (Metric.sphere a ε))
  (h_cont_n : ContinuousOn n (Metric.sphere a ε))
  (h_cont_grad_fund : ContinuousOn (fun x ↦ gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε)) :
  IntegrableOn (fun x ↦ v x * ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere a ε) surfaceArea := by
  exact integrableOn_compact_surface_of_continuousOn (isCompact_sphere a ε) h_finite_area _ (ContinuousOn.mul h_cont_v (ContinuousOn.inner h_cont_grad_fund h_cont_n))


lemma u_val_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (u H_a : E → ℝ) (G : E → E → ℝ)
  (hu : u = fun y ↦ G y a)
  (hHa_G : ∀ x ∈ Ω \ {a}, G x a = fundamental_sol_3d (x - a) + H_a x) :
  ∀ x ∈ Metric.sphere a ε, u x = fundamental_sol_3d (x - a) + H_a x := by
  intro x hx
  rw [hu]
  exact hHa_G x ⟨ha_subset (Metric.sphere_subset_closedBall hx), by
    intro h_eq
    rw [h_eq] at hx
    linarith [Metric.mem_sphere.mp hx, dist_self a]⟩

lemma uniqueDiffWithinAt_closure_punctured_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (x : E) (hx : x ∈ Metric.sphere a ε) :
  UniqueDiffWithinAt ℝ (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x := by
  haveI : HasPDEDomain (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) :=
    double_annulus_has_pde_domain Ω a b ε hε ha_subset hb_subset h_disjoint
  exact HasPDEDomain.unique_diff x (sphere_a_subset_closure Ω a b ε hε ha_subset h_disjoint hx)

lemma differentiableAt_fund_sphere_a (a : E) (ε : ℝ) (hε : 0 < ε) (x : E) (hx : x ∈ Metric.sphere a ε) :
  DifferentiableAt ℝ (fun y ↦ fundamental_sol_3d (y - a)) x :=
  differentiableAt_fund_sphere a ε hε x hx

lemma grad_u_val_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (u H_a : E → ℝ) (G : E → E → ℝ)
  (hu : u = fun y ↦ G y a)
  (hHa_G : ∀ x ∈ Ω \ {a}, G x a = fundamental_sol_3d (x - a) + H_a x)
  (hHa_diff : ContDiffOn ℝ 2 H_a Ω) :
  ∀ x ∈ Metric.sphere a ε, gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x =
    gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x +
    gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x := by
  intro x hx
  have h_uni := uniqueDiffWithinAt_closure_punctured_a Ω a b ε hε ha_subset hb_subset h_disjoint x hx
  have h_fund := differentiableAt_fund_sphere_a a ε hε x hx
  have h_Ha := differentiableAt_Ha_sphere_a Ω a ε ha_subset H_a hHa_diff x hx
  have hx_ne : x ≠ a := by intro h_eq; rw [h_eq] at hx; linarith [Metric.mem_sphere.mp hx, dist_self a]
  have h_eq : ∀ᶠ y in nhds x, u y = fundamental_sol_3d (y - a) + H_a y :=
    Filter.eventuallyEq_of_mem (IsOpen.mem_nhds (HasPDEDomain.is_open.sdiff isClosed_singleton) ⟨ha_subset (Metric.sphere_subset_closedBall hx), hx_ne⟩) (fun y hy ↦ by rw [hu]; exact hHa_G y hy)
  unfold gradientWithin
  erw [fderivWithin_eq_fderiv h_uni (DifferentiableAt.congr_of_eventuallyEq (h_fund.add h_Ha) h_eq),
    Filter.EventuallyEq.fderiv_eq h_eq,
    ← fderivWithin_eq_fderiv h_uni (h_fund.add h_Ha),
    fderivWithin_add h_uni h_fund.differentiableWithinAt h_Ha.differentiableWithinAt,
    map_add (InnerProductSpace.toDual ℝ E).symm]

lemma integral_split_u_v_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (n : E → E) (H_a u v : E → ℝ)
  (h_u_val : ∀ x ∈ Metric.sphere a ε, u x = fundamental_sol_3d (x - a) + H_a x)
  (h_grad_u : ∀ x ∈ Metric.sphere a ε, gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x =
    gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x +
    gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x)
  (h_int_fund_v : IntegrableOn (fun x ↦ fundamental_sol_3d (x - a) * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere a ε) surfaceArea)
  (h_int_H_v : IntegrableOn (fun x ↦ H_a x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere a ε) surfaceArea)
  (h_int_v_fund : IntegrableOn (fun x ↦ v x * ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere a ε) surfaceArea) :
  ∫ x in Metric.sphere a ε, (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea =
  (∫ x in Metric.sphere a ε, (fundamental_sol_3d (x - a) * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea) +
  (∫ x in Metric.sphere a ε, (H_a x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea) -
  (∫ x in Metric.sphere a ε, (v x * ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea) := by
  rw [MeasureTheory.setIntegral_congr_fun (isCompact_sphere a ε).measurableSet (integrand_algebra_sphere_a Ω a b ε n H_a u v h_u_val h_grad_u)]
  erw [MeasureTheory.integral_sub (Integrable.add h_int_fund_v h_int_H_v) h_int_v_fund, MeasureTheory.integral_add h_int_fund_v h_int_H_v]

lemma gradientWithin_v_eq_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (h_dist_ab : 2 * ε < dist a b)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (v : E → ℝ) (hv : v = fun y ↦ G y b)
  (x : E) (hx : x ∈ Metric.sphere a ε) :
  gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x =
  gradientWithin v (closure (Metric.ball a ε)) x := by
  have h_ext := gradientWithin_greens_eq_gradient Ω a b ε hε h_dist_ab G hG v hv ha_subset hb_subset x hx
  obtain ⟨H_b, _, hHb_diff, _, hGb_eq, _, _⟩ := hG b (hb_subset (Metric.mem_closedBall_self hε.le))
  have hx_ne_b : x ≠ b := fun e ↦ Set.disjoint_left.mp h_disjoint (Metric.sphere_subset_closedBall hx) (e ▸ Metric.mem_closedBall_self hε.le)
  have h_diff_v : DifferentiableAt ℝ v x := by
    refine DifferentiableAt.congr_of_eventuallyEq (DifferentiableAt.add ((contDiffAt_fundamental_sol_3d b x hx_ne_b).differentiableAt (by decide)) ((hHb_diff.differentiableOn (by decide)).differentiableAt (IsOpen.mem_nhds HasPDEDomain.is_open (ha_subset (Metric.sphere_subset_closedBall hx))))) (Filter.eventuallyEq_of_mem (IsOpen.mem_nhds (IsOpen.sdiff HasPDEDomain.is_open isClosed_singleton) ⟨ha_subset (Metric.sphere_subset_closedBall hx), hx_ne_b⟩) ?_)
    intro y hy; rw [hv]; exact hGb_eq y hy
  haveI : HasPDEDomain (Metric.ball a ε) := instHasPDEDomainBall a ε hε
  rw [h_ext, gradientWithin_eq_gradient_of_differentiableAt v (closure (Metric.ball a ε)) x h_diff_v (HasPDEDomain.unique_diff x (by rw [closure_ball a (ne_of_gt hε)]; exact Metric.sphere_subset_closedBall hx))]

lemma flux_eq_sphere_a_ball (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (h_dist_ab : 2 * ε < dist a b)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (v H_a : E → ℝ) (hv : v = fun y ↦ G y b)
  (hHa_diff : ContDiffOn ℝ 2 H_a Ω)
  (n n_ball : E → E) :
  ∫ x in Metric.sphere a ε, (H_a x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea =
  - ∫ x in frontier (Metric.ball a ε), (H_a x * ⟪gradientWithin v (closure (Metric.ball a ε)) x, n_ball x⟫_ℝ - v x * ⟪gradientWithin H_a (closure (Metric.ball a ε)) x, n_ball x⟫_ℝ) ∂surfaceArea := by

  have h_n_eq : ∀ x ∈ Metric.sphere a ε, n x = -n_ball x := sorry

  rw [frontier_ball a (ne_of_gt hε), ← integral_neg]
  exact MeasureTheory.setIntegral_congr_fun (isCompact_sphere a ε).measurableSet (integrand_eq_sphere_a_ball_flux Ω a b ε v H_a n n_ball h_n_eq (gradientWithin_v_eq_sphere_a Ω a b ε hε ha_subset hb_subset h_disjoint h_dist_ab G hG v hv) (gradientWithin_Ha_eq_sphere_a Ω a b ε hε ha_subset hb_subset h_disjoint H_a hHa_diff))

lemma integral_H_a_v_cancel_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (h_dist_ab : 2 * ε < dist a b)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E) (hb : b ∈ Ω)
  (v : E → ℝ) (hv : v = fun y ↦ G y b)
  (H_a : E → ℝ)
  (hHa_diff : ContDiffOn ℝ 2 H_a Ω)
  (hHa_harm : IsHarmonic H_a Ω)
  (hv_diff : ContDiffOn ℝ 1 v (Metric.ball a ε))
  (hv_cont : ContinuousOn v (closure (Metric.ball a ε)))
  (h_cont_grad_v : ContinuousOn (gradient v) (Metric.closedBall a ε))
  (h_cont_v_closed : ContinuousOn v (Metric.closedBall a ε))
  (h_cont_v_front : ContinuousOn v (frontier (Metric.ball a ε)))
  (hv_grad_diff : ContDiffOn ℝ 1 (gradient v) (Metric.ball a ε))
  (hv_grad_cont : ContinuousOn (fun x ↦ gradientWithin v (closure (Metric.ball a ε)) x) (closure (Metric.ball a ε)))
  (h_cont_lap_v : ContinuousOn (fun x ↦ laplacianWithin v (closure (Metric.ball a ε)) x) (Metric.closedBall a ε))
  (h_cont_grad_v_front : ContinuousOn (fun x ↦ gradientWithin v (closure (Metric.ball a ε)) x) (frontier (Metric.ball a ε)))
  (hHa_grad_diff : ContDiffOn ℝ 1 (gradient H_a) (Metric.ball a ε))
  (hHa_grad_cont : ContinuousOn (fun x ↦ gradientWithin H_a (closure (Metric.ball a ε)) x) (closure (Metric.ball a ε)))
  (h_cont_grad_Ha : ContinuousOn (gradient H_a) (Metric.closedBall a ε))
  (h_cont_lap_Ha : ContinuousOn (fun x ↦ laplacianWithin H_a (closure (Metric.ball a ε)) x) (Metric.closedBall a ε))
  (h_cont_grad_Ha_front : ContinuousOn (fun x ↦ gradientWithin H_a (closure (Metric.ball a ε)) x) (frontier (Metric.ball a ε)))
  (hHa_diff_1 : ContDiffOn ℝ 1 H_a (Metric.ball a ε))
  (hHa_cont_closure : ContinuousOn H_a (closure (Metric.ball a ε)))
  (hHa_cont_closed : ContinuousOn H_a (Metric.closedBall a ε))
  (hHa_cont_front : ContinuousOn H_a (frontier (Metric.ball a ε)))
  (h_comp_front : IsCompact (frontier (Metric.ball a ε)))
  (h_fin_area : surfaceArea (frontier (Metric.ball a ε)) ≠ ⊤) :
  ∫ x in Metric.sphere a ε, (H_a x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea = 0 := by
  obtain ⟨n_ball, hn_ball, _⟩ := outward_normal_ball_exists a ε
  have h_cont_n_front : ContinuousOn n_ball (frontier (Metric.ball a ε)) :=by
   (expose_names; exact right)

  haveI : HasPDEDomain (Metric.ball a ε) := instHasPDEDomainBall a ε hε

  have h1 := contDiffOn_v_smul_grad_Ha_ball Ω a ε v H_a hv_diff hHa_grad_diff
  have h2 := continuousOn_v_smul_gradWithin_Ha_ball Ω a ε v H_a hv_cont hHa_grad_cont
  have h3 := integrableOn_inner_grad_Ha_grad_v_ball Ω a ε v H_a h_cont_grad_Ha h_cont_grad_v
  have h4 := integrableOn_v_mul_laplacianWithin_Ha_ball Ω a ε v H_a h_cont_v_closed h_cont_lap_Ha
  have h5 := integrableOn_v_mul_inner_gradWithin_Ha_normal_ball Ω a ε v H_a n_ball h_comp_front h_fin_area h_cont_v_front h_cont_n_front h_cont_grad_Ha_front
  have h6 := contDiffOn_Ha_smul_grad_v_ball Ω a ε v H_a hHa_diff_1 hv_grad_diff
  have h7 := continuousOn_Ha_smul_gradWithin_v_ball Ω a ε v H_a hHa_cont_closure hv_grad_cont
  have h8 := integrableOn_Ha_mul_laplacianWithin_v_ball Ω a ε v H_a hHa_cont_closed h_cont_lap_v
  have h9 := integrableOn_Ha_mul_inner_gradWithin_v_normal_ball Ω a ε v H_a n_ball h_comp_front h_fin_area hHa_cont_front h_cont_n_front h_cont_grad_v_front

  rw [flux_eq_sphere_a_ball Ω a b ε hε ha_subset hb_subset h_disjoint h_dist_ab G hG v H_a hv hHa_diff n n_ball]
  rw [← greens_second_identity (Metric.ball a ε) H_a v n_ball hn_ball h1 h2 h3 h4 h5 h6 h7 h8 h9]
  rw [setIntegral_congr_fun isOpen_ball.measurableSet (laplacianWithin_eq_laplacian_ball_a a ε v H_a),
      setIntegral_congr_fun isOpen_ball.measurableSet (laplacian_eq_zero_ball_a Ω a b ε hε ha_subset h_disjoint G hG hb v hv H_a hHa_harm),
      integral_zero, neg_zero]

lemma fundamental_sol_3d_constant_on_sphere (a : E) (ε : ℝ) :
  ∀ x ∈ Metric.sphere a ε, fundamental_sol_3d (x - a) = -1 / (4 * Real.pi * ε) :=
  fun x hx ↦ by unfold fundamental_sol_3d; rw [← dist_eq_norm, Metric.mem_sphere.mp hx]

lemma flux_v_sphere_a_eq_laplacian_ball (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E) (ha : a ∈ Ω) (hb : b ∈ Ω)
  (h_dist_ab : 2 * ε < dist a b)
  (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ∫ x in Metric.sphere a ε, ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ ∂surfaceArea =
  - ∫ x in Metric.ball a ε, laplacian v x := by
  obtain ⟨n_ball, hn_ball, _⟩ := outward_normal_ball_exists a ε

  have h_n_eq : ∀ x ∈ Metric.sphere a ε, n x = -n_ball x := sorry

  haveI : HasDivergenceTheoremDomain (Metric.ball a ε) := ball_has_div_domain a ε
  have h_meas : Measure.hausdorffMeasure (Module.finrank ℝ E - 1) = surfaceArea := by unfold surfaceArea; simp; ring_nf
  have h_div := divergence_theorem (gradient v) (Metric.ball a ε) n_ball hn_ball (contDiffOn_gradient_greens_ball Ω a b ε hε h_dist_ab G hG v hv ha_subset hb_subset)
  rw [h_meas, frontier_ball a (ne_of_gt hε)] at h_div
  rw [MeasureTheory.setIntegral_congr_fun (isCompact_sphere a ε).measurableSet (fun x hx ↦ by rw [gradientWithin_greens_eq_gradient Ω a b ε hε h_dist_ab G hG v hv ha_subset hb_subset x hx, h_n_eq x hx, inner_neg_right]), integral_neg, ← h_div]
  rfl

lemma integral_flux_v_sphere_a_eq_zero (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E) (ha : a ∈ Ω) (hb : b ∈ Ω)
  (h_dist_ab : 2 * ε < dist a b)
  (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ∫ x in Metric.sphere a ε, ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ ∂surfaceArea = 0 := by
  rw [flux_v_sphere_a_eq_laplacian_ball Ω a b ε hε ha_subset hb_subset h_disjoint G hG n ha hb h_dist_ab v hv]
  have h_zero : Set.EqOn (fun x ↦ laplacian v x) (fun _ ↦ 0) (Metric.ball a ε) := fun x hx ↦ by
    rw [hv]
    exact isHarmonic_greens_punctured hG hb x ⟨ha_subset (Metric.ball_subset_closedBall hx), fun e ↦ Set.disjoint_left.mp h_disjoint (Metric.ball_subset_closedBall hx) (e ▸ Metric.mem_closedBall_self hε.le)⟩
  rw [MeasureTheory.setIntegral_congr_fun isOpen_ball.measurableSet h_zero, integral_zero, neg_zero]

lemma integral_fund_grad_v_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E) (ha : a ∈ Ω) (hb : b ∈ Ω)
  (h_dist_ab : 2 * ε < dist a b)
  (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ∫ x in Metric.sphere a ε, (fundamental_sol_3d (x - a) * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea = 0 := by
  rw [MeasureTheory.setIntegral_congr_fun (isCompact_sphere a ε).measurableSet (fun x hx ↦ by rw [fundamental_sol_3d_constant_on_sphere a ε x hx]),
      MeasureTheory.integral_const_mul,
      integral_flux_v_sphere_a_eq_zero Ω a b ε hε ha_subset hb_subset h_disjoint G hG n ha hb h_dist_ab v hv,
      mul_zero]

lemma gradient_fundamental_sol (a x : E) (hx : x ≠ a) :
  gradient (fun y ↦ fundamental_sol_3d (y - a)) x = (1 / (4 * Real.pi * ‖x - a‖^3)) • (x - a) := by
  have h_grad_scale : gradient (fun y ↦ fundamental_sol_3d (y - a)) x = (-1 / (4 * Real.pi : ℝ)) • gradient (fun y ↦ 1 / ‖y - a‖) x := by
    have h_smul : (fun y ↦ fundamental_sol_3d (y - a)) = (-1 / (4 * Real.pi : ℝ)) • (fun y ↦ 1 / ‖y - a‖) := by
      ext y; unfold fundamental_sol_3d; simp only [Pi.smul_apply, smul_eq_mul]; ring
    unfold gradient
    rw [h_smul, fderiv_const_smul (differentiableAt_inv_norm_sub (sub_ne_zero.mpr hx)), map_smul]
  rw [h_grad_scale, gradient_inv_norm_shift a x, gradient_inv_norm (x - a) (sub_ne_zero.mpr hx), smul_smul]
  congr 1
  field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx), ne_of_gt Real.pi_pos]

lemma gradientWithin_fundamental_sol_eq (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (x : E) (hx : x ∈ Metric.sphere a ε) :
  gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x = gradient (fun y ↦ fundamental_sol_3d (y - a)) x := by
  haveI : HasPDEDomain (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) := double_annulus_has_pde_domain Ω a b ε hε ha_subset hb_subset h_disjoint
  exact gradientWithin_eq_gradient_of_differentiableAt (fun y ↦ fundamental_sol_3d (y - a)) _ x (differentiableAt_fundamental_sol_shift a x ε hε hx) (HasPDEDomain.unique_diff x (sphere_a_subset_closure Ω a b ε hε ha_subset h_disjoint hx))

lemma fundamental_sol_3d_normal_deriv_eq (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (h_dist_ab : 2 * ε < dist a b)
  (n : E → E) :
  ∀ x ∈ Metric.sphere a ε, ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ = -1 / (4 * Real.pi * ε^2) := by
  intro x hx
  have h_norm : ‖x - a‖ = ε := hx
  have hx_ne : x ≠ a := by intro e; linarith [show ε = 0 by rw [← h_norm, e, sub_self, norm_zero]]

  have hn : n x = -(ε⁻¹) • (x - a) := by
    sorry

  rw [gradientWithin_fundamental_sol_eq Ω a b ε hε ha_subset hb_subset h_disjoint x hx,
      gradient_fundamental_sol a x hx_ne, hn, h_norm,
      real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, h_norm]
  have h_pi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h_eps : ε ≠ 0 := ne_of_gt hε
  field_simp

lemma integral_harmonic_mean_value (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ∫ x in Metric.sphere a ε, v x ∂surfaceArea = 4 * Real.pi * ε^2 * v a := by
  have hb_in : b ∈ Ω := hb_subset (Metric.mem_closedBall_self hε.le)
  have h_sub : Metric.closedBall a ε ⊆ Ω \ {b} := fun x hx ↦ ⟨ha_subset hx, fun e ↦ Set.disjoint_left.mp h_disjoint hx (e ▸ Metric.mem_closedBall_self hε.le)⟩
  rw [laplace_mean_value_property_3D v (Ω \ {b}) a ε (HasPDEDomain.is_open.sdiff isClosed_singleton) hε h_sub (by rw [hv]; exact contDiffOn_greens_punctured hG hb_in Set.sdiff_subset (Set.notMem_sdiff_of_mem (Set.mem_singleton b))) (by rw [hv]; exact isHarmonic_greens_punctured hG hb_in)]
  have h_pi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h_eps : ε ≠ 0 := ne_of_gt hε
  field_simp

lemma integral_v_grad_fund_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E)
  (h_dist_ab : 2 * ε < dist a b)
  (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ∫ x in Metric.sphere a ε, (v x * ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea = -(v a) := by
  rw [MeasureTheory.setIntegral_congr_fun (isCompact_sphere a ε).measurableSet (fun x hx ↦ by rw [fundamental_sol_3d_normal_deriv_eq Ω a b ε hε ha_subset hb_subset h_disjoint h_dist_ab n x hx, mul_comm]),
      MeasureTheory.integral_const_mul,
      integral_harmonic_mean_value Ω a b ε hε ha_subset hb_subset h_disjoint G hG v hv]
  have h_pi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h_eps : ε ≠ 0 := ne_of_gt hε
  field_simp

lemma contDiffOn_greens_ball (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b) (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (v : E → ℝ) (hv : v = fun y ↦ G y b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω) :
  ContDiffOn ℝ 1 v (closure (Metric.ball a ε)) := by
  obtain ⟨H_b, _, hHb_diff, _, hHb_G, _, _⟩ := hG b (hb_subset (Metric.mem_closedBall_self hε.le))
  have h_ne : ∀ x ∈ Metric.closedBall a ε, x - b ≠ 0 := fun x hx h_zero => by
    have h_dist : dist a b ≤ ε := by rw [← sub_eq_zero.mp h_zero]; exact Metric.mem_closedBall.mp (by exact mem_closedBall_comm.mp hx)
    linarith [h_dist_ab, h_dist, hε]
  have h_fund_diff : ContDiffOn ℝ 1 (fun y ↦ fundamental_sol_3d (y - b)) (Metric.closedBall a ε) := by
    have h_eq : ∀ y ∈ Metric.closedBall a ε, (fun z ↦ (-1 : ℝ) / (4 * Real.pi) * ‖z - b‖⁻¹) y = fundamental_sol_3d (y - b) := fun y hy => by
      unfold fundamental_sol_3d
      field_simp [norm_ne_zero_iff.mpr (h_ne y hy), ne_of_gt Real.pi_pos]
    exact ContDiffOn.congr (ContDiffOn.mul contDiffOn_const (ContDiffOn.inv (ContDiffOn.norm ℝ (ContDiffOn.sub contDiffOn_id contDiffOn_const) h_ne) fun x hx => norm_ne_zero_iff.mpr (h_ne x hx))) (by
    exact fun x a ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h_eq (id x) a))))
  refine ContDiffOn.mono (ContDiffOn.congr (ContDiffOn.add h_fund_diff ((hHb_diff.of_le le_top).mono ha_subset)) fun x hx => ?_) closure_ball_subset_closedBall
  rw [hv]
  exact (hHb_G x ⟨ha_subset hx, fun h => h_ne x hx (sub_eq_zero.mpr h)⟩)

lemma hv_diff (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ContDiffOn ℝ 1 v (Metric.ball a ε) := by
  apply ContDiffOn.mono (contDiffOn_greens_ball Ω a b ε hε h_dist_ab G hG v hv ha_subset hb_subset)
  exact subset_closure

lemma hv_cont (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b) (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (v : E → ℝ) (hv : v = fun y ↦ G y b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω) :
  ContinuousOn v (closure (Metric.ball a ε)) := by
  rw [hv]
  exact continuousOn_G_cross_closure_ball Ω b a ε hε (by rwa [dist_comm]) hb_subset ha_subset G hG

lemma hu_cont (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b) (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (u : E → ℝ) (hu : u = fun y ↦ G y a)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω) :
  ContinuousOn u (closure (Metric.ball b ε)) := by
  rw [hu]
  exact continuousOn_G_cross_closure_ball Ω a b ε hε h_dist_ab ha_subset hb_subset G hG

lemma hv_cont_closed (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ContinuousOn v (Metric.closedBall a ε) := by
  rw [hv]
  exact continuousOn_G_cross_closedBall Ω b a ε hε hb_subset ha_subset h_disjoint.symm G hG

lemma hu_cont_closed (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ContinuousOn u (Metric.closedBall b ε) := by
  rw [hu]
  exact continuousOn_G_cross_closedBall Ω a b ε hε ha_subset hb_subset h_disjoint G hG

lemma hv_cont_front (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ContinuousOn v (frontier (Metric.ball a ε)) := by
  have h_front_subset : frontier (Metric.ball a ε) ⊆ Metric.closedBall a ε := by
    intro x hx
    have h_closure : x ∈ closure (Metric.ball a ε) := frontier_subset_closure hx
    exact closure_ball_subset_closedBall h_closure
  exact ContinuousOn.mono (hv_cont_closed Ω a b ε hε ha_subset hb_subset h_disjoint G hG v hv) h_front_subset

lemma hv_cont_sphere (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ContinuousOn v (Metric.sphere a ε) := by
  have h_sphere_subset : Metric.sphere a ε ⊆ Metric.closedBall a ε := by
    exact Metric.sphere_subset_closedBall
  exact ContinuousOn.mono (hv_cont_closed Ω a b ε hε ha_subset hb_subset h_disjoint G hG v hv) h_sphere_subset

lemma hv_grad_diff (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ContDiffOn ℝ 1 (gradient v) (Metric.ball a ε) := by
  apply ContDiffOn.mono (contDiffOn_gradient_greens_ball Ω a b ε hε h_dist_ab G hG v hv ha_subset hb_subset)
  exact subset_closure

lemma hv_grad_cont (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b) (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (v : E → ℝ) (hv : v = fun y ↦ G y b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω) :
  ContinuousOn (fun x ↦ gradientWithin v (closure (Metric.ball a ε)) x) (closure (Metric.ball a ε)) := by
  have h_C1 : ContDiffOn ℝ 1 v (closure (Metric.ball a ε)) :=
    contDiffOn_greens_ball Ω a b ε hε h_dist_ab G hG v hv ha_subset hb_subset
  have h_unique_diff : UniqueDiffOn ℝ (closure (Metric.ball a ε)) := by
    exact (instHasPDEDomainBall a ε hε).unique_diff
  exact contDiffOn_1_gradientWithin_continuousOn h_C1 h_unique_diff

lemma h_cont_grad_v (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ContinuousOn (gradient v) (Metric.closedBall a ε) := by
  have h_subset : Metric.closedBall a ε ⊆ Ω \ {b} := fun x hx =>
    ⟨ha_subset hx, fun h => by
      have h_dist : dist a b ≤ ε := by { rw [← h]; exact Metric.mem_closedBall.mp (mem_closedBall_comm.mp hx) }
      linarith⟩
  obtain ⟨H_b, _, hHb_diff, _, hHb_G, _, _⟩ := hG b (hb_subset (Metric.mem_closedBall_self hε.le))
  have h_ne : ∀ x ∈ Ω \ {b}, x - b ≠ 0 := fun x hx h_zero => hx.2 (Set.mem_singleton_iff.mpr (sub_eq_zero.mp h_zero))
  have h_fund_diff : ContDiffOn ℝ 1 (fun y ↦ fundamental_sol_3d (y - b)) (Ω \ {b}) := by
    have h_eq : ∀ y ∈ Ω \ {b}, (fun z ↦ (-1 : ℝ) / (4 * Real.pi) * ‖z - b‖⁻¹) y = fundamental_sol_3d (y - b) := fun y hy => by
      unfold fundamental_sol_3d
      field_simp [norm_ne_zero_iff.mpr (h_ne y hy), ne_of_gt Real.pi_pos]
    exact ContDiffOn.congr (ContDiffOn.mul contDiffOn_const (ContDiffOn.inv (ContDiffOn.norm ℝ (ContDiffOn.sub contDiffOn_id contDiffOn_const) h_ne) fun x hx => norm_ne_zero_iff.mpr (h_ne x hx))) (by exact fun x hx ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h_eq x hx))))
  have h_C1 : ContDiffOn ℝ 1 v (Ω \ {b}) := by
    refine ContDiffOn.congr (ContDiffOn.add h_fund_diff ((hHb_diff.of_le le_top).mono Set.sdiff_subset)) fun x hx => ?_
    rw [hv]
    exact (hHb_G x hx)
  exact (contDiffOn_1_gradient_continuousOn h_C1 (HasPDEDomain.is_open.sdiff isClosed_singleton)).mono h_subset

lemma h_cont_grad_v_front (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ContinuousOn (fun x ↦ gradientWithin v (closure (Metric.ball a ε)) x) (frontier (Metric.ball a ε)) := by
  have h_front_subset : frontier (Metric.ball a ε) ⊆ closure (Metric.ball a ε) := frontier_subset_closure
  exact ContinuousOn.mono (hv_grad_cont Ω a b ε hε h_dist_ab G hG v hv ha_subset hb_subset) h_front_subset

lemma h_cont_grad_v_sphere (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ContinuousOn (fun x ↦ gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε) := by
  obtain ⟨H_b, _, _, _, hHb_G, h_G_front, h_H_front⟩ := hG b (hb_subset (Metric.mem_closedBall_self hε.le))

  have h_not_b : ∀ x ∈ closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)), x - b ≠ 0 := by
    intro x hx h_zero
    have hxb : x = b := sub_eq_zero.mp h_zero
    have h_subset : Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε) ⊆ (Metric.ball b ε)ᶜ := by
      intro y hy h_in_ball
      exact hy.2 (Or.inr (Metric.ball_subset_closedBall h_in_ball))
    have h_clos_subset : closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) ⊆ (Metric.ball b ε)ᶜ :=
      closure_minimal h_subset (isClosed_compl_iff.mpr Metric.isOpen_ball)
    have hx_not_in_ball : x ∉ Metric.ball b ε := h_clos_subset hx
    have hx_in_ball : x ∈ Metric.ball b ε := by
      rw [hxb]
      exact Metric.mem_ball_self hε
    exact hx_not_in_ball hx_in_ball

  have h_fund_diff : ContDiffOn ℝ 1 (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) := by
    have h_eq : ∀ y ∈ closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)), (fun z ↦ (-1 : ℝ) / (4 * Real.pi) * ‖z - b‖⁻¹) y = fundamental_sol_3d (y - b) := fun y hy => by
      unfold fundamental_sol_3d
      field_simp [norm_ne_zero_iff.mpr (h_not_b y hy), ne_of_gt Real.pi_pos]
    exact ContDiffOn.congr (ContDiffOn.mul contDiffOn_const (ContDiffOn.inv (ContDiffOn.norm ℝ (ContDiffOn.sub contDiffOn_id contDiffOn_const) h_not_b) fun x hx => norm_ne_zero_iff.mpr (h_not_b x hx))) (by exact fun x hx ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h_eq x hx))))

  have h_C1 : ContDiffOn ℝ 1 v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) := by
    have h_H_diff : ContDiffOn ℝ 1 H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) := sorry
    refine ContDiffOn.congr (ContDiffOn.add h_fund_diff h_H_diff) fun y hy => ?_
    by_cases hy_omega : y ∈ Ω
    · rw [hv]
      exact hHb_G y ⟨hy_omega, fun h => h_not_b y hy (sub_eq_zero.mpr h)⟩
    · have hy_front : y ∈ frontier Ω := ⟨closure_mono Set.sdiff_subset hy, fun h => hy_omega (interior_subset h)⟩
      simp_rw [hv, h_G_front y hy_front, h_H_front y hy_front]
      ring

  exact ContinuousOn.mono (ContinuousOn.congr (Continuous.comp_continuousOn (InnerProductSpace.toDual ℝ E).symm.continuous (h_C1.continuousOn_fderivWithin (double_annulus_has_pde_domain Ω a b ε hε ha_subset hb_subset h_disjoint).unique_diff le_rfl)) fun _ _ => rfl) (sphere_a_subset_closure Ω a b ε hε ha_subset h_disjoint)

lemma h_cont_lap_v (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ContinuousOn (fun x ↦ laplacianWithin v (closure (Metric.ball a ε)) x) (Metric.closedBall a ε) := by
  have h_C2 : ContDiffOn ℝ 2 v (closure (Metric.ball a ε)) := by
    obtain ⟨H_b, _, hHb_diff, _, hHb_G, _, _⟩ := hG b (hb_subset (Metric.mem_closedBall_self hε.le))
    have h_ne : ∀ x ∈ Metric.closedBall a ε, x - b ≠ 0 := fun x hx h_zero => by
      have h_dist : dist a b ≤ ε := by { rw [← sub_eq_zero.mp h_zero]; exact Metric.mem_closedBall.mp (mem_closedBall_comm.mp hx) }
      linarith
    have h_fund_diff : ContDiffOn ℝ 2 (fun y ↦ fundamental_sol_3d (y - b)) (Metric.closedBall a ε) := by
      have h_eq : ∀ y ∈ Metric.closedBall a ε, (fun z ↦ (-1 : ℝ) / (4 * Real.pi) * ‖z - b‖⁻¹) y = fundamental_sol_3d (y - b) := fun y hy => by
        unfold fundamental_sol_3d
        field_simp [norm_ne_zero_iff.mpr (h_ne y hy), ne_of_gt Real.pi_pos]
      exact ContDiffOn.congr (ContDiffOn.mul contDiffOn_const (ContDiffOn.inv (ContDiffOn.norm ℝ (ContDiffOn.sub contDiffOn_id contDiffOn_const) h_ne) fun x hx => norm_ne_zero_iff.mpr (h_ne x hx))) (by exact fun x hx ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h_eq x hx))))
    refine ContDiffOn.mono (ContDiffOn.congr (ContDiffOn.add h_fund_diff ((hHb_diff.of_le le_top).mono ha_subset)) fun x hx => ?_) closure_ball_subset_closedBall
    rw [hv]
    exact (hHb_G x ⟨ha_subset hx, fun h => h_ne x hx (sub_eq_zero.mpr h)⟩)
  have h_unique_diff : UniqueDiffOn ℝ (closure (Metric.ball a ε)) := (instHasPDEDomainBall a ε hε).unique_diff
  exact ContinuousOn.mono (ContinuousOn.congr (Continuous.comp_continuousOn continuous_trace ((contDiffOn_gradWithin (Metric.ball a ε) h_unique_diff v h_C2).continuousOn_fderivWithin h_unique_diff le_rfl)) fun _ _ => rfl) (fun x hx => by rw [closure_ball_eq_closedBall a ε hε]; exact hx)

lemma h_cont_n_sphere (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (n : E → E) :
  ContinuousOn n (Metric.sphere a ε) := by
  sorry

lemma h_cont_fund_sphere_a (a : E) (ε : ℝ) (hε : 0 < ε) :
  ContinuousOn (fun x ↦ fundamental_sol_3d (x - a)) (Metric.sphere a ε) := by
  exact continuousOn_Phi_sphere a ε hε fundamental_sol_3d (congrFun rfl)

lemma h_cont_grad_fund_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  ContinuousOn (fun x ↦ gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε) := by
  have h_ne : ∀ y ∈ Metric.sphere a ε, y ≠ a := fun y hy h_eq => by
    have h_dist : dist y a = ε := Metric.mem_sphere.mp hy
    rw [h_eq, dist_self] at h_dist
    exact ne_of_gt hε h_dist.symm
  have h_grad_cont : ContDiffOn ℝ 1 (gradient (fun y ↦ fundamental_sol_3d (y - a))) (Metric.sphere a ε) := fun y hy =>
    (ContDiffAt.continuousLinearMap_comp (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap ((contDiffAt_fundamental_sol_3d a y (h_ne y hy)).fderiv_right le_rfl)).contDiffWithinAt
  refine h_grad_cont.continuousOn.congr fun x hx => ?_
  unfold gradientWithin gradient
  rw [DifferentiableAt.fderivWithin (differentiableAt_fund_sphere_a a ε hε x hx) ((double_annulus_has_pde_domain Ω a b ε hε ha_subset hb_subset h_disjoint).unique_diff x (sphere_a_subset_closure_punctured Ω a b ε hε ha_subset h_disjoint hx))]

lemma integral_difference_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E) (ha : a ∈ Ω) (hb : b ∈ Ω)
  (h_dist_ab : 2 * ε < dist a b)
  (u v : E → ℝ) (hu : u = fun y ↦ G y a) (hv : v = fun y ↦ G y b) :
  ∫ x in Metric.sphere a ε, (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea = v a := by
  obtain ⟨H_a, _, hHa_diff, hHa_harm, hHa_G, _, _⟩ := hG a ha

  have hv_diff : ContDiffOn ℝ 1 v (Metric.ball a ε) :=
    (contDiffOn_greens_ball Ω a b ε hε h_dist_ab G hG v hv ha_subset hb_subset).mono subset_closure
  have hv_cont : ContinuousOn v (closure (Metric.ball a ε)) :=
    hv_cont Ω a b ε hε h_dist_ab G hG v hv ha_subset hb_subset
  have hv_cont_closed : ContinuousOn v (Metric.closedBall a ε) :=
    hv_cont_closed Ω a b ε hε ha_subset hb_subset h_disjoint G hG v hv
  have hv_cont_front : ContinuousOn v (frontier (Metric.ball a ε)) :=
    hv_cont_front Ω a b ε hε ha_subset hb_subset h_disjoint G hG v hv
  have hv_cont_sphere : ContinuousOn v (Metric.sphere a ε) :=
    hv_cont_sphere Ω a b ε hε ha_subset hb_subset h_disjoint G hG v hv
  have hv_grad_diff : ContDiffOn ℝ 1 (gradient v) (Metric.ball a ε) :=
    hv_grad_diff Ω a b ε hε h_dist_ab ha_subset hb_subset G hG v hv
  have hv_grad_cont : ContinuousOn (fun x ↦ gradientWithin v (closure (Metric.ball a ε)) x) (closure (Metric.ball a ε)) :=
    hv_grad_cont Ω a b ε hε h_dist_ab G hG v hv ha_subset hb_subset
  have h_cont_grad_v : ContinuousOn (gradient v) (Metric.closedBall a ε) :=
    h_cont_grad_v Ω a b ε hε h_dist_ab ha_subset hb_subset G hG v hv
  have h_cont_grad_v_front : ContinuousOn (fun x ↦ gradientWithin v (closure (Metric.ball a ε)) x) (frontier (Metric.ball a ε)) :=
    h_cont_grad_v_front Ω a b ε hε h_dist_ab ha_subset hb_subset G hG v hv
  have h_cont_grad_v_sphere : ContinuousOn (fun x ↦ gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε) :=
    h_cont_grad_v_sphere Ω a b ε hε ha_subset hb_subset h_disjoint G hG v hv
  have h_cont_lap_v : ContinuousOn (fun x ↦ laplacianWithin v (closure (Metric.ball a ε)) x) (Metric.closedBall a ε) :=
    h_cont_lap_v Ω a b ε hε h_dist_ab ha_subset hb_subset G hG v hv
  have h_cont_n_sphere : ContinuousOn n (Metric.sphere a ε) :=
    h_cont_n_sphere_a a ε n

  have hHa_diff_1 : ContDiffOn ℝ 1 H_a (Metric.ball a ε) :=
    hHa_diff_1 Ω a ε ha_subset H_a (hHa_diff.of_le le_top)
  have hHa_cont_closure : ContinuousOn H_a (closure (Metric.ball a ε)) :=
    hHa_cont_closure Ω a ε hε ha_subset H_a (hHa_diff.of_le le_top)
  have hHa_cont_closed : ContinuousOn H_a (Metric.closedBall a ε) :=
    hHa_cont_closed Ω a ε ha_subset H_a (hHa_diff.of_le le_top)
  have hHa_cont_front : ContinuousOn H_a (frontier (Metric.ball a ε)) :=
    hHa_cont_front Ω a ε ha_subset H_a (hHa_diff.of_le le_top)
  have hHa_cont_sphere : ContinuousOn H_a (Metric.sphere a ε) :=
    hHa_cont_sphere Ω a ε ha_subset H_a (hHa_diff.of_le le_top)
  have hHa_grad_diff : ContDiffOn ℝ 1 (gradient H_a) (Metric.ball a ε) :=
    hHa_grad_diff Ω a ε ha_subset H_a (hHa_diff.of_le le_top)
  have hHa_grad_cont : ContinuousOn (fun x ↦ gradientWithin H_a (closure (Metric.ball a ε)) x) (closure (Metric.ball a ε)) :=
    hHa_grad_cont Ω a ε hε ha_subset H_a (hHa_diff.of_le le_top)
  have h_cont_grad_Ha : ContinuousOn (gradient H_a) (Metric.closedBall a ε) :=
    h_cont_grad_Ha Ω a ε ha_subset H_a (hHa_diff.of_le le_top)
  have h_cont_grad_Ha_front : ContinuousOn (fun x ↦ gradientWithin H_a (closure (Metric.ball a ε)) x) (frontier (Metric.ball a ε)) :=
    h_cont_grad_Ha_front Ω a ε hε ha_subset H_a (hHa_diff.of_le le_top)
  have h_cont_grad_Ha_sphere : ContinuousOn (fun x ↦ gradientWithin H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε) :=
    h_cont_grad_Ha_sphere Ω a b ε hε ha_subset hb_subset h_disjoint H_a (hHa_diff.of_le le_top)
  have h_cont_lap_Ha : ContinuousOn (fun x ↦ laplacianWithin H_a (closure (Metric.ball a ε)) x) (Metric.closedBall a ε) :=
    h_cont_lap_Ha Ω a ε hε ha_subset H_a (hHa_diff.of_le le_top)

  have h_cont_fund_sphere : ContinuousOn (fun x ↦ fundamental_sol_3d (x - a)) (Metric.sphere a ε) :=
    h_cont_fund_sphere_a a ε hε
  have h_cont_grad_fund_sphere : ContinuousOn (fun x ↦ gradientWithin (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere a ε) :=
    h_cont_grad_fund_sphere_a Ω a b ε hε ha_subset hb_subset h_disjoint
  have h_comp_front : IsCompact (frontier (Metric.ball a ε)) :=
    h_comp_front_a a ε
  have h_fin_area : surfaceArea (frontier (Metric.ball a ε)) ≠ ⊤ :=
    h_fin_area_a a ε
  have h_fin_area_sphere : surfaceArea (Metric.sphere a ε) ≠ ⊤ :=
    h_fin_area_sphere_a a ε

  have h_int_1 := integrable_fund_grad_v_sphere_a Ω a b ε v n h_fin_area_sphere h_cont_fund_sphere h_cont_n_sphere h_cont_grad_v_sphere
  have h_int_2 := integrable_H_a_cross_term_sphere_a Ω a b ε H_a v n h_fin_area_sphere hHa_cont_sphere hv_cont_sphere h_cont_n_sphere h_cont_grad_Ha_sphere h_cont_grad_v_sphere
  have h_int_3 := integrable_v_grad_fund_sphere_a Ω a b ε v n h_fin_area_sphere hv_cont_sphere h_cont_n_sphere h_cont_grad_fund_sphere

  have h_cancel := integral_H_a_v_cancel_sphere_a Ω a b ε hε ha_subset hb_subset h_disjoint h_dist_ab G hG n hb v hv H_a (hHa_diff.of_le le_top) hHa_harm hv_diff hv_cont h_cont_grad_v hv_cont_closed hv_cont_front hv_grad_diff hv_grad_cont h_cont_lap_v h_cont_grad_v_front hHa_grad_diff hHa_grad_cont h_cont_grad_Ha h_cont_lap_Ha h_cont_grad_Ha_front hHa_diff_1 hHa_cont_closure hHa_cont_closed hHa_cont_front h_comp_front h_fin_area
  have h_split := integral_split_u_v_sphere_a Ω a b ε n H_a u v (u_val_sphere_a Ω a ε hε ha_subset u H_a G hu hHa_G) (grad_u_val_sphere_a Ω a b ε hε ha_subset hb_subset h_disjoint u H_a G hu hHa_G (hHa_diff.of_le le_top)) h_int_1 h_int_2 h_int_3
  have h_fund := integral_fund_grad_v_sphere_a Ω a b ε hε ha_subset hb_subset h_disjoint G hG n ha hb h_dist_ab v hv
  have h_v_fund := integral_v_grad_fund_sphere_a Ω a b ε hε ha_subset hb_subset h_disjoint G hG n h_dist_ab v hv

  simp only [h_split, h_cancel, h_fund, h_v_fund]
  ring



------------------------------------- VERSION FOR SYMMETRIC B ARGUMENTS-----------------------------

lemma integrand_algebra_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (n : E → E) (H_b u v : E → ℝ)
  (h_v_val : ∀ x ∈ Metric.sphere b ε, v x = fundamental_sol_3d (x - b) + H_b x)
  (h_grad_v : ∀ x ∈ Metric.sphere b ε, gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x =
    gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x +
    gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) :
  ∀ x ∈ Metric.sphere b ε,
    (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) =
    (u x * ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) +
    (u x * ⟪gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - H_b x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) -
    (fundamental_sol_3d (x - b) * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) := by
  intro x hx
  erw [h_v_val x hx, h_grad_v x hx, inner_add_left]
  ring

--------------------------------------INTEGRABILITY STUFF_------------------------------------------
lemma integrable_u_grad_fund_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (u : E → ℝ) (n : E → E)
  (h_finite_area : surfaceArea (Metric.sphere b ε) ≠ ⊤)
  (h_cont_u : ContinuousOn u (Metric.sphere b ε))
  (h_cont_n : ContinuousOn n (Metric.sphere b ε))
  (h_cont_grad_fund : ContinuousOn (fun x ↦ gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε)) :
  IntegrableOn (fun x ↦ u x * ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere b ε) surfaceArea := by
  have h_compact : IsCompact (Metric.sphere b ε) := isCompact_sphere b ε
  have h_cont_integrand : ContinuousOn (fun x ↦ u x * ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere b ε) := by
    apply ContinuousOn.mul h_cont_u
    apply ContinuousOn.inner h_cont_grad_fund h_cont_n
  exact integrableOn_compact_surface_of_continuousOn h_compact h_finite_area _ h_cont_integrand

lemma integrable_fund_grad_u_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (u : E → ℝ) (n : E → E)
  (h_finite_area : surfaceArea (Metric.sphere b ε) ≠ ⊤)
  (h_cont_fund : ContinuousOn (fun x ↦ fundamental_sol_3d (x - b)) (Metric.sphere b ε))
  (h_cont_n : ContinuousOn n (Metric.sphere b ε))
  (h_cont_grad_u : ContinuousOn (fun x ↦ gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε)) :
  IntegrableOn (fun x ↦ fundamental_sol_3d (x - b) * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere b ε) surfaceArea := by
  have h_compact : IsCompact (Metric.sphere b ε) := isCompact_sphere b ε
  have h_cont_integrand : ContinuousOn (fun x ↦ fundamental_sol_3d (x - b) * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere b ε) := by
    apply ContinuousOn.mul h_cont_fund
    apply ContinuousOn.inner h_cont_grad_u h_cont_n
  exact integrableOn_compact_surface_of_continuousOn h_compact h_finite_area _ h_cont_integrand
----------------------------------------------------------------------------------------------------

lemma v_val_sphere_b (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ) (hε : 0 < ε)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (v H_b : E → ℝ) (G : E → E → ℝ)
  (hv : v = fun y ↦ G y b)
  (hHb_G : ∀ x ∈ Ω \ {b}, G x b = fundamental_sol_3d (x - b) + H_b x) :
  ∀ x ∈ Metric.sphere b ε, v x = fundamental_sol_3d (x - b) + H_b x := by
  intro x hx
  rw [hv]
  exact hHb_G x ⟨hb_subset (Metric.sphere_subset_closedBall hx), by
    intro h_eq
    rw [h_eq] at hx
    linarith [Metric.mem_sphere.mp hx, dist_self b]⟩

lemma uniqueDiffWithinAt_closure_punctured_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (x : E) (hx : x ∈ Metric.sphere b ε) :
  UniqueDiffWithinAt ℝ (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x := by
  haveI : HasPDEDomain (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) :=
    double_annulus_has_pde_domain Ω a b ε hε ha_subset hb_subset h_disjoint
  have h_sub : Metric.sphere b ε ⊆ closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) := by
    rw [Set.union_comm]
    exact sphere_a_subset_closure Ω b a ε hε hb_subset h_disjoint.symm
  exact HasPDEDomain.unique_diff x (h_sub hx)

lemma grad_v_val_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (v H_b : E → ℝ) (G : E → E → ℝ)
  (hv : v = fun y ↦ G y b)
  (hHb_G : ∀ x ∈ Ω \ {b}, G x b = fundamental_sol_3d (x - b) + H_b x)
  (hHb_diff : ContDiffOn ℝ 2 H_b Ω) :
  ∀ x ∈ Metric.sphere b ε, gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x =
    gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x +
    gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x := by
  intro x hx
  have h_uni := uniqueDiffWithinAt_closure_punctured_b Ω a b ε hε ha_subset hb_subset h_disjoint x hx
  have h_fund := differentiableAt_fund_sphere_b b ε hε x hx
  have h_Hb := differentiableAt_Hb_sphere_b Ω b ε hb_subset H_b hHb_diff x hx
  have hx_ne : x ≠ b := by intro h_eq; rw [h_eq] at hx; linarith [Metric.mem_sphere.mp hx, dist_self b]
  have h_eq : ∀ᶠ y in nhds x, v y = fundamental_sol_3d (y - b) + H_b y :=
    Filter.eventuallyEq_of_mem (IsOpen.mem_nhds (HasPDEDomain.is_open.sdiff isClosed_singleton) ⟨hb_subset (Metric.sphere_subset_closedBall hx), hx_ne⟩) (fun y hy ↦ by rw [hv]; exact hHb_G y hy)
  unfold gradientWithin
  erw [fderivWithin_eq_fderiv h_uni (DifferentiableAt.congr_of_eventuallyEq (h_fund.add h_Hb) h_eq),
    Filter.EventuallyEq.fderiv_eq h_eq,
    ← fderivWithin_eq_fderiv h_uni (h_fund.add h_Hb),
    fderivWithin_add h_uni h_fund.differentiableWithinAt h_Hb.differentiableWithinAt,
    map_add (InnerProductSpace.toDual ℝ E).symm]

lemma integral_split_u_v_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ)
  (n : E → E) (H_b u v : E → ℝ)
  (h_v_val : ∀ x ∈ Metric.sphere b ε, v x = fundamental_sol_3d (x - b) + H_b x)
  (h_grad_v : ∀ x ∈ Metric.sphere b ε, gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x =
    gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x +
    gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x)
  (h_int_u_fund : IntegrableOn (fun x ↦ u x * ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere b ε) surfaceArea)
  (h_int_H_u : IntegrableOn (fun x ↦ u x * ⟪gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - H_b x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere b ε) surfaceArea)
  (h_int_fund_u : IntegrableOn (fun x ↦ fundamental_sol_3d (x - b) * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) (Metric.sphere b ε) surfaceArea) :
  ∫ x in Metric.sphere b ε, (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea =
  (∫ x in Metric.sphere b ε, (u x * ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea) +
  (∫ x in Metric.sphere b ε, (u x * ⟪gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - H_b x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea) -
  (∫ x in Metric.sphere b ε, (fundamental_sol_3d (x - b) * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea) := by
  rw [MeasureTheory.setIntegral_congr_fun (isCompact_sphere b ε).measurableSet (integrand_algebra_sphere_b Ω a b ε n H_b u v h_v_val h_grad_v)]
  erw [MeasureTheory.integral_sub (Integrable.add h_int_u_fund h_int_H_u) h_int_fund_u, MeasureTheory.integral_add h_int_u_fund h_int_H_u]

lemma hu_diff (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ContDiffOn ℝ 1 u (Metric.ball b ε) := by
  have h_dist_ba : 2 * ε < dist b a := by rw [dist_comm]; exact h_dist_ab
  apply ContDiffOn.mono (contDiffOn_greens_ball Ω b a ε hε h_dist_ba G hG u hu hb_subset ha_subset)
  exact subset_closure

lemma hu_cont_front (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ContinuousOn u (frontier (Metric.ball b ε)) := by
  have h_front_subset : frontier (Metric.ball b ε) ⊆ Metric.closedBall b ε := by
    intro x hx
    have h_closure : x ∈ closure (Metric.ball b ε) := frontier_subset_closure hx
    exact closure_ball_subset_closedBall h_closure
  exact ContinuousOn.mono (hu_cont_closed Ω a b ε hε ha_subset hb_subset h_disjoint G hG u hu) h_front_subset

lemma hu_cont_sphere (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ContinuousOn u (Metric.sphere b ε) := by
  have h_sphere_subset : Metric.sphere b ε ⊆ Metric.closedBall b ε := by
    exact Metric.sphere_subset_closedBall
  exact ContinuousOn.mono (hu_cont_closed Ω a b ε hε ha_subset hb_subset h_disjoint G hG u hu) h_sphere_subset

lemma hu_grad_diff (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ContDiffOn ℝ 1 (gradient u) (Metric.ball b ε) := by
  have h_dist_ba : 2 * ε < dist b a := by rw [dist_comm]; exact h_dist_ab
  apply ContDiffOn.mono (contDiffOn_gradient_greens_ball Ω b a ε hε h_dist_ba G hG u hu hb_subset ha_subset)
  exact subset_closure

lemma hu_grad_cont (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b) (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (u : E → ℝ) (hu : u = fun y ↦ G y a)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω) :
  ContinuousOn (fun x ↦ gradientWithin u (closure (Metric.ball b ε)) x) (closure (Metric.ball b ε)) := by
  have h_dist_ba : 2 * ε < dist b a := by rw [dist_comm]; exact h_dist_ab
  have h_C1 : ContDiffOn ℝ 1 u (closure (Metric.ball b ε)) :=
    contDiffOn_greens_ball Ω b a ε hε h_dist_ba G hG u hu hb_subset ha_subset
  have h_unique_diff : UniqueDiffOn ℝ (closure (Metric.ball b ε)) := by
    exact (instHasPDEDomainBall b ε hε).unique_diff
  exact contDiffOn_1_gradientWithin_continuousOn h_C1 h_unique_diff

lemma h_cont_grad_u (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ContinuousOn (gradient u) (Metric.closedBall b ε) := by
  have h_subset : Metric.closedBall b ε ⊆ Ω \ {a} := fun x hx =>
    ⟨hb_subset hx, fun h => by
      have h_dist : dist a b ≤ ε := by { rw [← h]; exact Metric.mem_closedBall.mp hx }
      linarith⟩
  obtain ⟨H_a, _, hHa_diff, _, hHa_G, _, _⟩ := hG a (ha_subset (Metric.mem_closedBall_self hε.le))
  have h_ne : ∀ x ∈ Ω \ {a}, x - a ≠ 0 := fun x hx h_zero => hx.2 (Set.mem_singleton_iff.mpr (sub_eq_zero.mp h_zero))
  have h_fund_diff : ContDiffOn ℝ 1 (fun y ↦ fundamental_sol_3d (y - a)) (Ω \ {a}) := by
    have h_eq : ∀ y ∈ Ω \ {a}, (fun z ↦ (-1 : ℝ) / (4 * Real.pi) * ‖z - a‖⁻¹) y = fundamental_sol_3d (y - a) := fun y hy => by
      unfold fundamental_sol_3d
      field_simp [norm_ne_zero_iff.mpr (h_ne y hy), ne_of_gt Real.pi_pos]
    exact ContDiffOn.congr (ContDiffOn.mul contDiffOn_const (ContDiffOn.inv (ContDiffOn.norm ℝ (ContDiffOn.sub contDiffOn_id contDiffOn_const) h_ne) fun x hx => norm_ne_zero_iff.mpr (h_ne x hx))) (by exact fun x hx ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h_eq x hx))))
  have h_C1 : ContDiffOn ℝ 1 u (Ω \ {a}) := by
    refine ContDiffOn.congr (ContDiffOn.add h_fund_diff ((hHa_diff.of_le le_top).mono Set.sdiff_subset)) fun x hx => ?_
    rw [hu]
    exact (hHa_G x hx)
  exact (contDiffOn_1_gradient_continuousOn h_C1 (HasPDEDomain.is_open.sdiff isClosed_singleton)).mono h_subset

lemma h_cont_grad_u_front (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ContinuousOn (fun x ↦ gradientWithin u (closure (Metric.ball b ε)) x) (frontier (Metric.ball b ε)) := by
  have h_front_subset : frontier (Metric.ball b ε) ⊆ closure (Metric.ball b ε) := frontier_subset_closure
  exact ContinuousOn.mono (hu_grad_cont Ω a b ε hε h_dist_ab G hG u hu ha_subset hb_subset) h_front_subset

lemma h_cont_grad_u_sphere (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ContinuousOn (fun x ↦ gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε) := by
  obtain ⟨H_a, _, _, _, hHa_G, h_G_front, h_H_front⟩ := hG a (ha_subset (Metric.mem_closedBall_self hε.le))

  have h_not_a : ∀ x ∈ closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)), x - a ≠ 0 := by
    intro x hx h_zero
    have hxa : x = a := sub_eq_zero.mp h_zero
    have h_subset : Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε) ⊆ (Metric.ball a ε)ᶜ := fun y hy h_in_ball => hy.2 (Or.inl (Metric.ball_subset_closedBall h_in_ball))
    have hx_not_in_ball : x ∉ Metric.ball a ε := closure_minimal h_subset (isClosed_compl_iff.mpr Metric.isOpen_ball) hx
    have hx_in_ball : x ∈ Metric.ball a ε := by { rw [hxa]; exact Metric.mem_ball_self hε }
    exact hx_not_in_ball hx_in_ball

  have h_fund_diff : ContDiffOn ℝ 1 (fun y ↦ fundamental_sol_3d (y - a)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) := by
    have h_eq : ∀ y ∈ closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)), (fun z ↦ (-1 : ℝ) / (4 * Real.pi) * ‖z - a‖⁻¹) y = fundamental_sol_3d (y - a) := fun y hy => by
      unfold fundamental_sol_3d
      field_simp [norm_ne_zero_iff.mpr (h_not_a y hy), ne_of_gt Real.pi_pos]
    exact ContDiffOn.congr (ContDiffOn.mul contDiffOn_const (ContDiffOn.inv (ContDiffOn.norm ℝ (ContDiffOn.sub contDiffOn_id contDiffOn_const) h_not_a) fun x hx => norm_ne_zero_iff.mpr (h_not_a x hx))) (by exact fun x hx ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h_eq x hx))))

  have h_C1 : ContDiffOn ℝ 1 u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) := by
    have h_H_diff : ContDiffOn ℝ 1 H_a (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) := sorry
    refine ContDiffOn.congr (ContDiffOn.add h_fund_diff h_H_diff) fun y hy => ?_
    by_cases hy_omega : y ∈ Ω
    · rw [hu]
      exact hHa_G y ⟨hy_omega, fun h => h_not_a y hy (sub_eq_zero.mpr h)⟩
    · have hy_front : y ∈ frontier Ω := ⟨closure_mono Set.sdiff_subset hy, fun h => hy_omega (interior_subset h)⟩
      simp_rw [hu, h_G_front y hy_front, h_H_front y hy_front]
      ring

  exact ContinuousOn.mono (ContinuousOn.congr (Continuous.comp_continuousOn (InnerProductSpace.toDual ℝ E).symm.continuous (h_C1.continuousOn_fderivWithin (double_annulus_has_pde_domain Ω a b ε hε ha_subset hb_subset h_disjoint).unique_diff le_rfl)) fun _ _ => rfl) (by
    rw [Set.union_comm (Metric.closedBall a ε) (Metric.closedBall b ε)]
    exact sphere_a_subset_closure Ω b a ε hε hb_subset h_disjoint.symm)

lemma h_cont_lap_u (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (h_dist_ab : 2 * ε < dist a b)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ContinuousOn (fun x ↦ laplacianWithin u (closure (Metric.ball b ε)) x) (Metric.closedBall b ε) := by
  have h_C2 : ContDiffOn ℝ 2 u (closure (Metric.ball b ε)) := by
    obtain ⟨H_a, _, hHa_diff, _, hHa_G, _, _⟩ := hG a (ha_subset (Metric.mem_closedBall_self hε.le))
    have h_ne : ∀ x ∈ Metric.closedBall b ε, x - a ≠ 0 := fun x hx h_zero => by
      have h_dist : dist a b ≤ ε := by { rw [← sub_eq_zero.mp h_zero]; exact Metric.mem_closedBall.mp hx }
      linarith
    have h_fund_diff : ContDiffOn ℝ 2 (fun y ↦ fundamental_sol_3d (y - a)) (Metric.closedBall b ε) := by
      have h_eq : ∀ y ∈ Metric.closedBall b ε, (fun z ↦ (-1 : ℝ) / (4 * Real.pi) * ‖z - a‖⁻¹) y = fundamental_sol_3d (y - a) := fun y hy => by
        unfold fundamental_sol_3d
        field_simp [norm_ne_zero_iff.mpr (h_ne y hy), ne_of_gt Real.pi_pos]
      exact ContDiffOn.congr (ContDiffOn.mul contDiffOn_const (ContDiffOn.inv (ContDiffOn.norm ℝ (ContDiffOn.sub contDiffOn_id contDiffOn_const) h_ne) fun x hx => norm_ne_zero_iff.mpr (h_ne x hx))) (by exact fun x hx ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h_eq x hx))))
    refine ContDiffOn.mono (ContDiffOn.congr (ContDiffOn.add h_fund_diff ((hHa_diff.of_le le_top).mono hb_subset)) fun x hx => ?_) closure_ball_subset_closedBall
    rw [hu]
    exact (hHa_G x ⟨hb_subset hx, fun h => h_ne x hx (sub_eq_zero.mpr h)⟩)
  have h_unique_diff : UniqueDiffOn ℝ (closure (Metric.ball b ε)) := (instHasPDEDomainBall b ε hε).unique_diff
  exact ContinuousOn.mono (ContinuousOn.congr (Continuous.comp_continuousOn continuous_trace ((contDiffOn_gradWithin (Metric.ball b ε) h_unique_diff u h_C2).continuousOn_fderivWithin h_unique_diff le_rfl)) fun _ _ => rfl) (fun x hx => by rw [closure_ball_eq_closedBall b ε hε]; exact hx)

lemma gradientWithin_u_eq_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (h_dist_ab : 2 * ε < dist a b)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (u : E → ℝ) (hu : u = fun y ↦ G y a)
  (x : E) (hx : x ∈ Metric.sphere b ε) :
  gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x =
  gradientWithin u (closure (Metric.ball b ε)) x := by
  obtain ⟨H_a, _, hHa_diff, _, hGa_eq, _, _⟩ := hG a (ha_subset (Metric.mem_closedBall_self hε.le))
  have hx_ne_a : x ≠ a := fun e ↦ Set.disjoint_left.mp h_disjoint (by rw [e]; exact Metric.mem_closedBall_self hε.le) (Metric.sphere_subset_closedBall hx)
  have h_diff_u : DifferentiableAt ℝ u x := DifferentiableAt.congr_of_eventuallyEq (DifferentiableAt.add ((contDiffAt_fundamental_sol_3d a x hx_ne_a).differentiableAt (by decide)) ((hHa_diff.differentiableOn (by decide)).differentiableAt (HasPDEDomain.is_open.mem_nhds (hb_subset (Metric.sphere_subset_closedBall hx))))) (Filter.eventuallyEq_of_mem ((HasPDEDomain.is_open.sdiff isClosed_singleton).mem_nhds ⟨hb_subset (Metric.sphere_subset_closedBall hx), hx_ne_a⟩) fun y hy => by rw [hu]; exact hGa_eq y hy)
  rw [Set.union_comm (Metric.closedBall a ε) (Metric.closedBall b ε)]
  exact (gradientWithin_greens_eq_gradient Ω b a ε hε (by rwa [dist_comm] at h_dist_ab) G hG u hu hb_subset ha_subset x hx).trans (gradientWithin_eq_gradient_of_differentiableAt u (closure (Metric.ball b ε)) x h_diff_u ((instHasPDEDomainBall b ε hε).unique_diff x (by rw [closure_ball b (ne_of_gt hε)]; exact Metric.sphere_subset_closedBall hx))).symm

lemma flux_eq_sphere_b_ball (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (h_dist_ab : 2 * ε < dist a b)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (u H_b : E → ℝ) (hu : u = fun y ↦ G y a)
  (hHb_diff : ContDiffOn ℝ 2 H_b Ω)
  (n n_ball : E → E) :
  ∫ x in Metric.sphere b ε, (u x * ⟪gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - H_b x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea =
  - ∫ x in frontier (Metric.ball b ε), (u x * ⟪gradientWithin H_b (closure (Metric.ball b ε)) x, n_ball x⟫_ℝ - H_b x * ⟪gradientWithin u (closure (Metric.ball b ε)) x, n_ball x⟫_ℝ) ∂surfaceArea := by

  have h_n_eq : ∀ x ∈ Metric.sphere b ε, n x = -n_ball x := sorry

  rw [frontier_ball b (ne_of_gt hε), ← integral_neg]
  exact MeasureTheory.setIntegral_congr_fun (isCompact_sphere b ε).measurableSet (integrand_eq_sphere_b_ball_flux Ω a b ε u H_b n n_ball h_n_eq (gradientWithin_u_eq_sphere_b Ω a b ε hε ha_subset hb_subset h_disjoint h_dist_ab G hG u hu) (gradientWithin_Hb_eq_sphere_b Ω a b ε hε ha_subset hb_subset h_disjoint H_b hHb_diff))

lemma laplacian_eq_zero_ball_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω) (ha : a ∈ Ω)
  (u : E → ℝ) (hu : u = fun y ↦ G y a)
  (H_b : E → ℝ) (hHb_harm : IsHarmonic H_b Ω) :
  Set.EqOn (fun x ↦ u x * laplacian H_b x - H_b x * laplacian u x) (fun _ ↦ 0) (Metric.ball b ε) := by
  intro x hx
  have hx_ne_a : x ≠ a := fun e ↦ Set.disjoint_left.mp h_disjoint (Metric.mem_closedBall_self hε.le) (e ▸ Metric.ball_subset_closedBall hx)
  have h_lap_u : laplacian u x = 0 := by
    rw [hu]
    exact isHarmonic_greens_punctured hG ha x ⟨hb_subset (Metric.ball_subset_closedBall hx), hx_ne_a⟩
  have h_lap_Hb : laplacian H_b x = 0 := hHb_harm x (hb_subset (Metric.ball_subset_closedBall hx))
  simp_rw [h_lap_u, h_lap_Hb]
  ring

lemma h_cont_fund_sphere (b : E) (ε : ℝ) (hε : 0 < ε) :
  ContinuousOn (fun x ↦ fundamental_sol_3d (x - b)) (Metric.sphere b ε) := by
  exact continuousOn_Phi_sphere b ε hε fundamental_sol_3d (congrFun rfl)

lemma h_cont_grad_fund_sphere (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω) (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :
  ContinuousOn (fun x ↦ gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε) := by
  have h_ne : ∀ y ∈ Metric.sphere b ε, y ≠ b := fun y hy h_eq => by
    have h_dist : dist y b = ε := Metric.mem_sphere.mp hy
    rw [h_eq, dist_self] at h_dist
    exact ne_of_gt hε h_dist.symm
  have h_grad_cont : ContDiffOn ℝ 1 (gradient (fun y ↦ fundamental_sol_3d (y - b))) (Metric.sphere b ε) := fun y hy =>
    (ContDiffAt.continuousLinearMap_comp (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap ((contDiffAt_fundamental_sol_3d b y (h_ne y hy)).fderiv_right le_rfl)).contDiffWithinAt
  refine h_grad_cont.continuousOn.congr fun x hx => ?_
  unfold gradientWithin gradient
  rw [DifferentiableAt.fderivWithin (differentiableAt_fund_sphere_b b ε hε x hx) ((double_annulus_has_pde_domain Ω a b ε hε ha_subset hb_subset h_disjoint).unique_diff x (sphere_b_subset_closure_punctured Ω a b ε hε hb_subset h_disjoint hx))]


lemma integral_H_b_u_cancel_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (h_dist_ab : 2 * ε < dist a b)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E) (ha : a ∈ Ω)
  (u : E → ℝ) (hu : u = fun y ↦ G y a)
  (H_b : E → ℝ)
  (hHb_diff : ContDiffOn ℝ 2 H_b Ω)
  (hHb_harm : IsHarmonic H_b Ω)
  (hu_diff : ContDiffOn ℝ 1 u (Metric.ball b ε))
  (hu_cont : ContinuousOn u (closure (Metric.ball b ε)))
  (h_cont_grad_u : ContinuousOn (gradient u) (Metric.closedBall b ε))
  (hu_cont_closed : ContinuousOn u (Metric.closedBall b ε))
  (hu_cont_front : ContinuousOn u (frontier (Metric.ball b ε)))
  (hu_grad_diff : ContDiffOn ℝ 1 (gradient u) (Metric.ball b ε))
  (hu_grad_cont : ContinuousOn (fun x ↦ gradientWithin u (closure (Metric.ball b ε)) x) (closure (Metric.ball b ε)))
  (h_cont_lap_u : ContinuousOn (fun x ↦ laplacianWithin u (closure (Metric.ball b ε)) x) (Metric.closedBall b ε))
  (h_cont_grad_u_front : ContinuousOn (fun x ↦ gradientWithin u (closure (Metric.ball b ε)) x) (frontier (Metric.ball b ε)))
  (hHb_grad_diff : ContDiffOn ℝ 1 (gradient H_b) (Metric.ball b ε))
  (hHb_grad_cont : ContinuousOn (fun x ↦ gradientWithin H_b (closure (Metric.ball b ε)) x) (closure (Metric.ball b ε)))
  (h_cont_grad_Hb : ContinuousOn (gradient H_b) (Metric.closedBall b ε))
  (h_cont_lap_Hb : ContinuousOn (fun x ↦ laplacianWithin H_b (closure (Metric.ball b ε)) x) (Metric.closedBall b ε))
  (h_cont_grad_Hb_front : ContinuousOn (fun x ↦ gradientWithin H_b (closure (Metric.ball b ε)) x) (frontier (Metric.ball b ε)))
  (hHb_diff_1 : ContDiffOn ℝ 1 H_b (Metric.ball b ε))
  (hHb_cont_closure : ContinuousOn H_b (closure (Metric.ball b ε)))
  (hHb_cont_closed : ContinuousOn H_b (Metric.closedBall b ε))
  (hHb_cont_front : ContinuousOn H_b (frontier (Metric.ball b ε)))
  (h_comp_front : IsCompact (frontier (Metric.ball b ε)))
  (h_fin_area : surfaceArea (frontier (Metric.ball b ε)) ≠ ⊤) :
  ∫ x in Metric.sphere b ε, (u x * ⟪gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - H_b x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea = 0 := by
  obtain ⟨n_ball, hn_ball, _⟩ := outward_normal_ball_exists b ε
  have h_cont_n_front : ContinuousOn n_ball (frontier (Metric.ball b ε)) := by
    (expose_names; exact right)

  haveI : HasPDEDomain (Metric.ball b ε) := instHasPDEDomainBall b ε hε

  have h1 := contDiffOn_u_smul_grad_Hb_ball Ω b ε u H_b hu_diff hHb_grad_diff
  have h2 := continuousOn_u_smul_gradWithin_Hb_ball Ω b ε u H_b hu_cont hHb_grad_cont
  have h3 := integrableOn_inner_grad_Hb_grad_u_ball Ω b ε u H_b h_cont_grad_Hb h_cont_grad_u
  have h4 := integrableOn_u_mul_laplacianWithin_Hb_ball Ω b ε u H_b hu_cont_closed h_cont_lap_Hb
  have h5 := integrableOn_u_mul_inner_gradWithin_Hb_normal_ball Ω b ε u H_b n_ball h_comp_front h_fin_area hu_cont_front h_cont_n_front h_cont_grad_Hb_front
  have h6 := contDiffOn_Hb_smul_grad_u_ball Ω b ε u H_b hHb_diff_1 hu_grad_diff
  have h7 := continuousOn_Hb_smul_gradWithin_u_ball Ω b ε u H_b hHb_cont_closure hu_grad_cont
  have h8 := integrableOn_Hb_mul_laplacianWithin_u_ball Ω b ε u H_b hHb_cont_closed h_cont_lap_u
  have h9 := integrableOn_Hb_mul_inner_gradWithin_u_normal_ball Ω b ε u H_b n_ball h_comp_front h_fin_area hHb_cont_front h_cont_n_front h_cont_grad_u_front

  rw [flux_eq_sphere_b_ball Ω a b ε hε ha_subset hb_subset h_disjoint h_dist_ab G hG u H_b hu hHb_diff n n_ball]
  rw [← greens_second_identity (Metric.ball b ε) u H_b n_ball hn_ball h6 h7 h3 h8 h9 h1 h2 h4 h5]
  rw [setIntegral_congr_fun isOpen_ball.measurableSet (laplacianWithin_eq_laplacian_ball_b b ε u H_b),
      setIntegral_congr_fun isOpen_ball.measurableSet (laplacian_eq_zero_ball_b Ω a b ε hε hb_subset h_disjoint G hG ha u hu H_b hHb_harm),
      integral_zero, neg_zero]


lemma flux_u_sphere_b_eq_laplacian_ball (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E) (ha : a ∈ Ω) (hb : b ∈ Ω)
  (h_dist_ab : 2 * ε < dist a b)
  (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ∫ x in Metric.sphere b ε, ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ ∂surfaceArea =
  - ∫ x in Metric.ball b ε, laplacian u x := by
  obtain ⟨n_ball, hn_ball, _⟩ := outward_normal_ball_exists b ε

  have h_n_eq : ∀ x ∈ Metric.sphere b ε, n x = -n_ball x := sorry

  haveI : HasDivergenceTheoremDomain (Metric.ball b ε) := ball_has_div_domain b ε
  have h_meas : Measure.hausdorffMeasure (Module.finrank ℝ E - 1) = surfaceArea := by unfold surfaceArea; simp; ring_nf
  have h_dist_ba : 2 * ε < dist b a := by rw [dist_comm]; exact h_dist_ab
  have h_div := divergence_theorem (gradient u) (Metric.ball b ε) n_ball hn_ball (contDiffOn_gradient_greens_ball Ω b a ε hε h_dist_ba G hG u hu hb_subset ha_subset)
  rw [h_meas, frontier_ball b (ne_of_gt hε)] at h_div
  rw [MeasureTheory.setIntegral_congr_fun (isCompact_sphere b ε).measurableSet (fun x hx ↦ by rw [Set.union_comm, gradientWithin_greens_eq_gradient Ω b a ε hε h_dist_ba G hG u hu hb_subset ha_subset x hx, h_n_eq x hx, inner_neg_right]), integral_neg, ← h_div]
  rfl

lemma integral_flux_u_sphere_b_eq_zero (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E) (ha : a ∈ Ω) (hb : b ∈ Ω)
  (h_dist_ab : 2 * ε < dist a b)
  (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ∫ x in Metric.sphere b ε, ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ ∂surfaceArea = 0 := by
  rw [flux_u_sphere_b_eq_laplacian_ball Ω a b ε hε ha_subset hb_subset h_disjoint G hG n ha hb h_dist_ab u hu]
  have h_zero : Set.EqOn (fun x ↦ laplacian u x) (fun _ ↦ 0) (Metric.ball b ε) := fun x hx ↦ by
    rw [hu]
    exact isHarmonic_greens_punctured hG ha x ⟨hb_subset (Metric.ball_subset_closedBall hx), fun e ↦ Set.disjoint_left.mp h_disjoint (e ▸ Metric.mem_closedBall_self hε.le) (Metric.ball_subset_closedBall hx)⟩
  rw [MeasureTheory.setIntegral_congr_fun isOpen_ball.measurableSet h_zero, integral_zero, neg_zero]

lemma integral_fund_grad_u_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E) (ha : a ∈ Ω) (hb : b ∈ Ω)
  (h_dist_ab : 2 * ε < dist a b)
  (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ∫ x in Metric.sphere b ε, (fundamental_sol_3d (x - b) * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea = 0 := by
  rw [MeasureTheory.setIntegral_congr_fun (isCompact_sphere b ε).measurableSet (fun x hx ↦ by rw [fundamental_sol_3d_constant_on_sphere b ε x hx]),
      MeasureTheory.integral_const_mul,
      integral_flux_u_sphere_b_eq_zero Ω a b ε hε ha_subset hb_subset h_disjoint G hG n ha hb h_dist_ab u hu,
      mul_zero]

lemma integral_u_grad_fund_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E) (ha : a ∈ Ω)
  (h_dist_ab : 2 * ε < dist a b)
  (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ∫ x in Metric.sphere b ε, (u x * ⟪gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea = -(u b) := by
  have h_sub : Metric.closedBall b ε ⊆ Ω \ {a} := fun x hx ↦ ⟨hb_subset hx, fun e ↦ Set.disjoint_left.mp h_disjoint (e ▸ Metric.mem_closedBall_self hε.le) hx⟩
  have h_dist_ba : 2 * ε < dist b a := by rw [dist_comm]; exact h_dist_ab
  rw [MeasureTheory.setIntegral_congr_fun (isCompact_sphere b ε).measurableSet (fun x hx ↦ by rw [Set.union_comm, fundamental_sol_3d_normal_deriv_eq Ω b a ε hε hb_subset ha_subset h_disjoint.symm h_dist_ba n x hx, mul_comm]),
      MeasureTheory.integral_const_mul,
      laplace_mean_value_property_3D u (Ω \ {a}) b ε (HasPDEDomain.is_open.sdiff isClosed_singleton) hε h_sub (by rw [hu]; exact contDiffOn_greens_punctured hG ha Set.sdiff_subset (Set.notMem_sdiff_of_mem (Set.mem_singleton a))) (by rw [hu]; exact isHarmonic_greens_punctured hG ha)]
  have h_pi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h_eps : ε ≠ 0 := ne_of_gt hε
  field_simp

lemma integral_difference_sphere_b (Ω : Set E) [HasPDEDomain Ω] (a b : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disjoint : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (n : E → E) (ha : a ∈ Ω) (hb : b ∈ Ω)
  (h_dist_ab : 2 * ε < dist a b)
  (u v : E → ℝ) (hu : u = fun y ↦ G y a) (hv : v = fun y ↦ G y b) :
  ∫ x in Metric.sphere b ε, (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea = -(u b) := by
  obtain ⟨H_b, _, hHb_diff, hHb_harm, hHb_G, _, _⟩ := hG b hb

  have hu_diff : ContDiffOn ℝ 1 u (Metric.ball b ε) :=
    hu_diff Ω a b ε hε h_dist_ab ha_subset hb_subset G hG u hu
  have hu_cont : ContinuousOn u (closure (Metric.ball b ε)) :=
    hu_cont Ω a b ε hε h_dist_ab G hG u hu ha_subset hb_subset
  have hu_cont_closed : ContinuousOn u (Metric.closedBall b ε) :=
    hu_cont_closed Ω a b ε hε ha_subset hb_subset h_disjoint G hG u hu
  have hu_cont_front : ContinuousOn u (frontier (Metric.ball b ε)) :=
    hu_cont_front Ω a b ε hε ha_subset hb_subset h_disjoint G hG u hu
  have hu_cont_sphere : ContinuousOn u (Metric.sphere b ε) :=
    hu_cont_sphere Ω a b ε hε ha_subset hb_subset h_disjoint G hG u hu
  have hu_grad_diff : ContDiffOn ℝ 1 (gradient u) (Metric.ball b ε) :=
    hu_grad_diff Ω a b ε hε h_dist_ab ha_subset hb_subset G hG u hu
  have hu_grad_cont : ContinuousOn (fun x ↦ gradientWithin u (closure (Metric.ball b ε)) x) (closure (Metric.ball b ε)) :=
    hu_grad_cont Ω a b ε hε h_dist_ab G hG u hu ha_subset hb_subset
  have h_cont_grad_u : ContinuousOn (gradient u) (Metric.closedBall b ε) :=
    h_cont_grad_u Ω a b ε hε h_dist_ab ha_subset hb_subset G hG u hu
  have h_cont_grad_u_front : ContinuousOn (fun x ↦ gradientWithin u (closure (Metric.ball b ε)) x) (frontier (Metric.ball b ε)) :=
    h_cont_grad_u_front Ω a b ε hε h_dist_ab ha_subset hb_subset G hG u hu
  have h_cont_grad_u_sphere : ContinuousOn (fun x ↦ gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε) :=
    h_cont_grad_u_sphere Ω a b ε hε ha_subset hb_subset h_disjoint G hG u hu
  have h_cont_lap_u : ContinuousOn (fun x ↦ laplacianWithin u (closure (Metric.ball b ε)) x) (Metric.closedBall b ε) :=
    h_cont_lap_u Ω a b ε hε h_dist_ab ha_subset hb_subset G hG u hu
  have h_cont_n_sphere : ContinuousOn n (Metric.sphere b ε) :=
    h_cont_n_sphere_b b ε n

  have hHb_diff_1 : ContDiffOn ℝ 1 H_b (Metric.ball b ε) :=
    hHb_diff_1 Ω b ε hb_subset H_b (hHb_diff.of_le le_top)
  have hHb_cont_closure : ContinuousOn H_b (closure (Metric.ball b ε)) :=
    hHb_cont_closure Ω b ε hε hb_subset H_b (hHb_diff.of_le le_top)
  have hHb_cont_closed : ContinuousOn H_b (Metric.closedBall b ε) :=
    hHb_cont_closed Ω b ε hb_subset H_b (hHb_diff.of_le le_top)
  have hHb_cont_front : ContinuousOn H_b (frontier (Metric.ball b ε)) :=
    hHb_cont_front Ω b ε hb_subset H_b (hHb_diff.of_le le_top)
  have hHb_cont_sphere : ContinuousOn H_b (Metric.sphere b ε) :=
    hHb_cont_sphere Ω b ε hb_subset H_b (hHb_diff.of_le le_top)
  have hHb_grad_diff : ContDiffOn ℝ 1 (gradient H_b) (Metric.ball b ε) :=
    hHb_grad_diff Ω b ε hb_subset H_b (hHb_diff.of_le le_top)
  have hHb_grad_cont : ContinuousOn (fun x ↦ gradientWithin H_b (closure (Metric.ball b ε)) x) (closure (Metric.ball b ε)) :=
    hHb_grad_cont Ω b ε hε hb_subset H_b (hHb_diff.of_le le_top)
  have h_cont_grad_Hb : ContinuousOn (gradient H_b) (Metric.closedBall b ε) :=
    h_cont_grad_Hb Ω b ε hb_subset H_b (hHb_diff.of_le le_top)
  have h_cont_grad_Hb_front : ContinuousOn (fun x ↦ gradientWithin H_b (closure (Metric.ball b ε)) x) (frontier (Metric.ball b ε)) :=
    h_cont_grad_Hb_front Ω b ε hε hb_subset H_b (hHb_diff.of_le le_top)
  have h_cont_grad_Hb_sphere : ContinuousOn (fun x ↦ gradientWithin H_b (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε) :=
    h_cont_grad_Hb_sphere Ω a b ε hε ha_subset hb_subset h_disjoint H_b (hHb_diff.of_le le_top)
  have h_cont_lap_Hb : ContinuousOn (fun x ↦ laplacianWithin H_b (closure (Metric.ball b ε)) x) (Metric.closedBall b ε) :=
    h_cont_lap_Hb Ω b ε hε hb_subset H_b (hHb_diff.of_le le_top)

  have h_cont_fund_sphere : ContinuousOn (fun x ↦ fundamental_sol_3d (x - b)) (Metric.sphere b ε) :=
    h_cont_fund_sphere b ε hε
  have h_cont_grad_fund_sphere : ContinuousOn (fun x ↦ gradientWithin (fun y ↦ fundamental_sol_3d (y - b)) (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) (Metric.sphere b ε) :=
    h_cont_grad_fund_sphere Ω a b ε hε ha_subset hb_subset h_disjoint
  have h_comp_front : IsCompact (frontier (Metric.ball b ε)) :=
    h_comp_front_b b ε
  have h_fin_area : surfaceArea (frontier (Metric.ball b ε)) ≠ ⊤ :=
    h_fin_area_b b ε
  have h_fin_area_sphere : surfaceArea (Metric.sphere b ε) ≠ ⊤ :=
    h_fin_area_sphere_b b ε

  have h_int_1 := integrable_u_grad_fund_sphere_b Ω a b ε u n h_fin_area_sphere hu_cont_sphere h_cont_n_sphere h_cont_grad_fund_sphere
  have h_int_2 := integrable_H_b_cross_term_sphere_b Ω a b ε H_b u n h_fin_area_sphere hHb_cont_sphere hu_cont_sphere h_cont_n_sphere h_cont_grad_Hb_sphere h_cont_grad_u_sphere
  have h_int_3 := integrable_fund_grad_u_sphere_b Ω a b ε u n h_fin_area_sphere h_cont_fund_sphere h_cont_n_sphere h_cont_grad_u_sphere

  have h_cancel := integral_H_b_u_cancel_sphere_b Ω a b ε hε ha_subset hb_subset h_disjoint h_dist_ab G hG n ha u hu H_b (hHb_diff.of_le le_top) hHb_harm hu_diff hu_cont h_cont_grad_u hu_cont_closed hu_cont_front hu_grad_diff hu_grad_cont h_cont_lap_u h_cont_grad_u_front hHb_grad_diff hHb_grad_cont h_cont_grad_Hb h_cont_lap_Hb h_cont_grad_Hb_front hHb_diff_1 hHb_cont_closure hHb_cont_closed hHb_cont_front h_comp_front h_fin_area
  have h_split := integral_split_u_v_sphere_b Ω a b ε n H_b u v (v_val_sphere_b Ω b ε hε hb_subset v H_b G hv hHb_G) (grad_v_val_sphere_b Ω a b ε hε ha_subset hb_subset h_disjoint v H_b G hv hHb_G (hHb_diff.of_le le_top)) h_int_1 h_int_2 h_int_3
  have h_fund := integral_u_grad_fund_sphere_b Ω a b ε hε ha_subset hb_subset h_disjoint G hG n ha h_dist_ab u hu
  have h_u_fund := integral_fund_grad_u_sphere_b Ω a b ε hε ha_subset hb_subset h_disjoint G hG n ha hb h_dist_ab u hu

  simp only [h_split, h_cancel, h_fund, h_u_fund]
  ring


lemma hu_cont_sphere_a (Ω : Set E) [HasPDEDomain Ω] (a : E) (ε : ℝ) (hε : 0 < ε)
  (ha_subset : Metric.closedBall a ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (ha : a ∈ Ω) (u : E → ℝ) (hu : u = fun y ↦ G y a) :
  ContinuousOn u (Metric.sphere a ε) := by
  obtain ⟨H_a, _, hHa_diff, _, hHa_G, _, _⟩ := hG a ha
  have h_ne : ∀ x ∈ Metric.sphere a ε, x ≠ a := fun x hx h_eq => by
    have h_dist : dist x a = ε := Metric.mem_sphere.mp hx
    rw [h_eq, dist_self] at h_dist
    exact ne_of_gt hε h_dist.symm
  refine ContinuousOn.congr ((h_cont_fund_sphere_a a ε hε).add (hHa_cont_sphere Ω a ε ha_subset H_a (hHa_diff.of_le le_top))) fun x hx => ?_
  rw [hu]
  exact (hHa_G x ⟨ha_subset (Metric.sphere_subset_closedBall hx), h_ne x hx⟩)

lemma h_cont_fund_sphere_b (b : E) (ε : ℝ) (hε : 0 < ε) :
  ContinuousOn (fun x ↦ fundamental_sol_3d (x - b)) (Metric.sphere b ε) := by
  exact continuousOn_Phi_sphere b ε hε fundamental_sol_3d (congrFun rfl)

lemma hv_cont_sphere_b (Ω : Set E) [HasPDEDomain Ω] (b : E) (ε : ℝ) (hε : 0 < ε)
  (hb_subset : Metric.closedBall b ε ⊆ Ω)
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (hb : b ∈ Ω) (v : E → ℝ) (hv : v = fun y ↦ G y b) :
  ContinuousOn v (Metric.sphere b ε) := by
  obtain ⟨H_b, _, hHb_diff, _, hHb_G, _, _⟩ := hG b hb
  have h_ne : ∀ x ∈ Metric.sphere b ε, x ≠ b := fun x hx h_eq => by
    have h_dist : dist x b = ε := Metric.mem_sphere.mp hx
    rw [h_eq, dist_self] at h_dist
    exact ne_of_gt hε h_dist.symm
  refine ContinuousOn.congr ((h_cont_fund_sphere_b b ε hε).add (hHb_cont_sphere Ω b ε hb_subset H_b (hHb_diff.of_le le_top))) fun x hx => ?_
  rw [hv]
  exact (hHb_G x ⟨hb_subset (Metric.sphere_subset_closedBall hx), h_ne x hx⟩)

lemma evaluate_boundary_integral (Ω : Set E) [HasPDEDomain Ω]
  (G : E → E → ℝ) (hG : IsGreensFunction G Ω)
  (a b : E) (ha : a ∈ Ω) (hb : b ∈ Ω)
  (ε : ℝ) (hε_pos : 0 < ε)
  (hra_subset : Metric.closedBall a ε ⊆ Ω)
  (hrb_subset : Metric.closedBall b ε ⊆ Ω)
  (h_disj : Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε))
  (h_dist_ab : 2 * ε < dist a b)
  (n : E → E)
  (u v : E → ℝ)
  (hu : u = fun y ↦ G y a)
  (hv : v = fun y ↦ G y b) :
  (∫ x in frontier (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)),
    (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ -
     v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea = 0) → u b = v a := by
  intro h_int_zero
  haveI h_domain := double_annulus_has_pde_domain Ω a b ε hε_pos hra_subset hrb_subset h_disj
  obtain ⟨_, _, _, _, _, hGa_bdry, _⟩ := hG a ha
  obtain ⟨_, _, _, _, _, hGb_bdry, _⟩ := hG b hb
  have h_int_outer : ∫ x in frontier Ω, (u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ) ∂surfaceArea = 0 := by
    have h_zero : ∀ x ∈ frontier Ω, u x * ⟪gradientWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ - v x * ⟪gradientWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x, n x⟫_ℝ = 0 := fun x hx => by
      simp_rw [hu, hv, hGa_bdry x hx, hGb_bdry x hx]
      ring
    rw [MeasureTheory.setIntegral_congr_fun isClosed_frontier.measurableSet h_zero]
    exact MeasureTheory.integral_zero E ℝ
  have h_int_sum := integral_boundary_sum Ω a b ε hε_pos hra_subset hrb_subset h_disj u v n
    (integrable_flux_diff_frontier Ω a b ε u v n (fun x hx => by simp_rw [hu, hGa_bdry x hx]) (fun x hx => by simp_rw [hv, hGb_bdry x hx]))
    (integrable_flux_diff_sphere_a Ω a b ε u v n (h_fin_area_sphere_a a ε) (hu_cont_sphere_a Ω a ε hε_pos hra_subset G hG ha u hu) (hv_cont_sphere Ω a b ε hε_pos hra_subset hrb_subset h_disj G hG v hv) (h_cont_n_sphere_a a ε n) sorry (h_cont_grad_v_sphere Ω a b ε hε_pos hra_subset hrb_subset h_disj G hG v hv))
    (integrable_flux_diff_sphere_b Ω a b ε u v n (h_fin_area_sphere_b b ε) (hu_cont_sphere Ω a b ε hε_pos hra_subset hrb_subset h_disj G hG u hu) (hv_cont_sphere_b Ω b ε hε_pos hrb_subset G hG hb v hv) (h_cont_n_sphere_b b ε n) (h_cont_grad_u_sphere Ω a b ε hε_pos hra_subset hrb_subset h_disj G hG u hu) sorry)
  rw [h_int_outer, integral_difference_sphere_a Ω a b ε hε_pos hra_subset hrb_subset h_disj G hG n ha hb h_dist_ab u v hu hv, integral_difference_sphere_b Ω a b ε hε_pos hra_subset hrb_subset h_disj G hG n ha hb h_dist_ab u v hu hv] at h_int_sum
  rw [h_int_zero] at h_int_sum
  linarith

lemma evaluate_symmetry_limit (Ω : Set E) [HasPDEDomain Ω]
  (h_bounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤)
  {G : E → E → ℝ} (hG : IsGreensFunction G Ω)
  {a b : E} (ha : a ∈ Ω) (hb : b ∈ Ω) (hne : a ≠ b)
  (h_eps_separation : ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
    2 * ε < dist a b ∧ Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε) ∧
    Metric.closedBall a ε ⊆ Ω ∧ Metric.closedBall b ε ⊆ Ω)
  (h_n_exists : ∀ ε > 0, ∃ n : E → E, IsOutwardUnitNormal (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) n ∧ ContinuousOn n (frontier (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)))) :
  G b a = G a b := by
  let u : E → ℝ := fun y ↦ G y a
  let v : E → ℝ := fun y ↦ G y b
  obtain ⟨ε₀, hε₀_pos, hε₀_prop⟩ := h_eps_separation
  have h_eps_exists : ∃ ε, 0 < ε ∧ ε < ε₀ := by
    use ε₀ / 2
    constructor
    · linarith
    · linarith
  obtain ⟨ε, hε_pos, hε_lt⟩ := h_eps_exists
  obtain ⟨h_dist_ab, h_disj, hra_subset, hrb_subset⟩ := hε₀_prop ε hε_pos hε_lt
  haveI h_domain := double_annulus_has_pde_domain Ω a b ε hε_pos hra_subset hrb_subset h_disj
  obtain ⟨n, hn, hn_cont⟩ := h_n_exists ε hε_pos
  have h_area_punctured : surfaceArea (frontier (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) ≠ ⊤ :=
    area_punctured_neq_top Ω a b ε hε_pos h_area

  have hu_diff : ContDiffOn ℝ 2 u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) := by
    sorry
  have hv_diff : ContDiffOn ℝ 2 v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) := by
    sorry

  have h_vol_int_zero : ∫ x in (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)),
    (u x * laplacianWithin v (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x -
     v x * laplacianWithin u (closure (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε))) x) = 0 :=
    vol_int_zero_punctured Ω a b ε u v (u_harm_punctured Ω a b ε hε_pos hG ha) (v_harm_punctured Ω a b ε hε_pos hG hb)
  have h_greens := greens_second_identity (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) u v n hn
    (smul_gradient_contDiffOn_one (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) u v hu_diff hv_diff)
    (smul_gradientWithin_continuousOn (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) u v (hu_diff.of_le (by decide)) hv_diff.continuousOn)
    (integrable_inner_gradient_of_c1 (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) (h_bounded.subset Set.sdiff_subset) u v (hu_diff.of_le (by decide)) (hv_diff.of_le (by decide)))
    (integrable_mul_laplacian_of_c2 (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) (h_bounded.subset Set.sdiff_subset) u v hu_diff hv_diff.continuousOn)
    (integrable_mul_inner_gradientWithin_normal (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) (h_bounded.subset Set.sdiff_subset) h_area_punctured u v (hu_diff.of_le (by decide)) hv_diff.continuousOn n hn_cont)
    (smul_gradient_contDiffOn_one (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) v u hv_diff hu_diff)
    (smul_gradientWithin_continuousOn (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) v u (hv_diff.of_le (by decide)) hu_diff.continuousOn)
    (integrable_mul_laplacian_of_c2 (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) (h_bounded.subset Set.sdiff_subset) v u hv_diff hu_diff.continuousOn)
    (integrable_mul_inner_gradientWithin_normal (Ω \ (Metric.closedBall a ε ∪ Metric.closedBall b ε)) (h_bounded.subset Set.sdiff_subset) h_area_punctured v u (hv_diff.of_le (by decide)) hu_diff.continuousOn n hn_cont)
  rw [h_vol_int_zero] at h_greens
  exact evaluate_boundary_integral Ω G hG a b ha hb ε hε_pos hra_subset hrb_subset h_disj h_dist_ab n u v rfl rfl h_greens.symm

theorem greens_function_symmetry {Ω : Set E} [HasPDEDomain Ω]
  (hBounded : Bornology.IsBounded Ω)
  (h_area : surfaceArea (frontier Ω) ≠ ⊤) {G : E → E → ℝ}
  (hG : IsGreensFunction G Ω) {a b : E} (ha : a ∈ Ω) (hb : b ∈ Ω) (hne : a ≠ b) :
  G a b = G b a :=
  (evaluate_symmetry_limit Ω hBounded h_area hG ha hb hne (greens_eps_separation_exists Ω a b ha hb hne) (fun ε hε => normal_exists_punctured Ω a b ε hε (sorry) (sorry) (sorry))).symm
