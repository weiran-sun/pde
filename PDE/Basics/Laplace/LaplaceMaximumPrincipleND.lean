import PDE.Basics.Heat.HeatMaximumPrincipleND

/-!
# Weak Maximum Principle for the Laplacian in n Dimensions

Blueprint chapter: `PDE_Basics_Laplace_LaplaceMaximumPrincipleND.tex`.

The weak maximum principle for subharmonic functions on an arbitrary open
bounded domain `Ω ⊆ ℝⁿ`, together with the companion minimum principle and
the pointwise boundary-bound corollaries. This is the elliptic
specialization of the perturbation argument carried out for the heat
equation in `PDE/Basics/Heat/HeatMaximumPrincipleND.lean`, whose Laplacian
toolkit (`local_max_implies_laplacian_nonpos`, `laplacian_add`,
`laplacian_norm_sq_smul`, `laplacian_neg`) is reused verbatim.
-/

open MeasureTheory Filter InnerProductSpace Measure Set
open scoped Topology ENNReal

open Heat

namespace Laplace

/-- **No interior maximum under strict subharmonicity** (blueprint
`lem:laplace-no-interior-max-nd`): if `v` is `C²` at every point of the open
set `Ω` with `Δ v > 0` on `Ω`, then no point of `Ω` is a local maximum of
`v`. Immediate from `local_max_implies_laplacian_nonpos`. -/
lemma elliptic_no_interior_max
    {n : ℕ} {Ω : Set (E n)} {v : E n → ℝ}
    (hv_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hv_pos : ∀ x ∈ Ω, 0 < laplacian v x) :
    ∀ x₀ ∈ Ω, ¬ IsLocalMax v x₀ := by
  intro x₀ hx₀ h_max
  exact absurd (local_max_implies_laplacian_nonpos n (hv_smooth x₀ hx₀) h_max)
    (not_le.mpr (hv_pos x₀ hx₀))

/-- **Nonempty topological boundary** (blueprint
`lem:laplace-boundary-nonempty`): a nonempty bounded open subset of `ℝⁿ`
(`n ≥ 1`) has nonempty topological boundary `closure Ω \ Ω`. Otherwise `Ω`
would be clopen, hence all of the connected space `ℝⁿ`, contradicting
boundedness. -/
lemma elliptic_boundary_nonempty
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (hΩ_ne : Ω.Nonempty) :
    (closure Ω \ Ω).Nonempty := by
  by_contra h_empty
  rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h_empty
  have h_cl : closure Ω = Ω := subset_antisymm h_empty subset_closure
  have h_clopen : IsClopen Ω := ⟨h_cl ▸ isClosed_closure, hΩ_open⟩
  have h_univ : Ω = Set.univ := h_clopen.eq_univ hΩ_ne
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (E n) :=
    ⟨0, EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ), by
      intro h
      have := congrFun (congrArg (WithLp.equiv 2 (Fin n → ℝ)) h) ⟨0, hn⟩
      simp [EuclideanSpace.single] at this⟩
  exact NormedSpace.unbounded_univ ℝ (E n) (h_univ ▸ hΩ_bdd)

/-- **Weak maximum principle for subharmonic functions** (blueprint
`thm:laplace-max-principle-nd`): if `Ω ⊆ ℝⁿ` (`n ≥ 1`) is open, bounded and
nonempty, and `u` is continuous on `closure Ω`, `C²` on `Ω` and subharmonic
(`Δ u ≥ 0` on `Ω`), then the supremum of `u` over `closure Ω` equals its
supremum over the topological boundary `closure Ω \ Ω`.

Proof: perturb `v = u + ε‖x‖²` with `ε = δ / M`; then `Δ v = Δ u + 2nε > 0`,
so the compact maximum of `v` cannot be interior
(`elliptic_no_interior_max`), and `u ≤ v ≤ sup_boundary u + δ` for every
`δ > 0`. -/
theorem elliptic_max_principle
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (hΩ_ne : Ω.Nonempty)
    {u : E n → ℝ}
    (h_cont : ContinuousOn u (closure Ω))
    (h_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (h_sub : ∀ x ∈ Ω, 0 ≤ laplacian u x) :
    sSup (u '' closure Ω) = sSup (u '' (closure Ω \ Ω)) := by
  have h_comp : IsCompact (closure Ω) := hΩ_bdd.isCompact_closure
  have h_cl_ne : (closure Ω).Nonempty := hΩ_ne.closure
  have h_Γ_ne : (closure Ω \ Ω).Nonempty :=
    elliptic_boundary_nonempty hn hΩ_open hΩ_bdd hΩ_ne
  have h_Γ_sub : closure Ω \ Ω ⊆ closure Ω := Set.sdiff_subset
  have h_Γ_closed : IsClosed (closure Ω \ Ω) := isClosed_closure.sdiff hΩ_open
  have h_Γ_comp : IsCompact (closure Ω \ Ω) :=
    h_comp.of_isClosed_subset h_Γ_closed h_Γ_sub
  have h_Γbdd : BddAbove (u '' (closure Ω \ Ω)) :=
    (h_Γ_comp.image_of_continuousOn (h_cont.mono h_Γ_sub)).bddAbove
  refine le_antisymm ?_ (csSup_le (h_Γ_ne.image _) <| by
    rintro y ⟨p, hp, rfl⟩
    exact le_csSup (h_comp.image_of_continuousOn h_cont).bddAbove
      ⟨p, h_Γ_sub hp, rfl⟩)
  apply le_of_forall_pos_le_add
  intro δ hδ
  set M := max (1 : ℝ) (sSup ((fun x : E n ↦ ‖x‖ ^ 2) '' closure Ω)) with hM_def
  have hM_pos : 0 < M := lt_max_iff.mpr (Or.inl zero_lt_one)
  set ε := δ / M with hε_def
  have hε : 0 < ε := div_pos hδ hM_pos
  have h_norm_sq_le : ∀ x ∈ closure Ω, ‖x‖ ^ 2 ≤ M := fun x hx ↦
    (le_csSup (h_comp.image_of_continuousOn
      (continuous_norm.pow 2).continuousOn).bddAbove
      (Set.mem_image_of_mem _ hx)).trans (le_max_right 1 _)
  set v := fun x : E n ↦ u x + ε * ‖x‖ ^ 2 with hv_def
  have h_v_cont : ContinuousOn v (closure Ω) :=
    h_cont.add (continuous_const.mul (continuous_norm.pow 2)).continuousOn
  have hv_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x := fun x hx ↦
    (h_smooth x hx).add (contDiffAt_const.mul (ContDiffAt.norm_sq ℝ contDiffAt_id))
  have hv_pos : ∀ x ∈ Ω, 0 < laplacian v x := by
    intro x hx
    have hc_norm : ContDiffAt ℝ 2 (fun x' : E n ↦ ε * ‖x'‖ ^ 2) x :=
      contDiffAt_const.mul (ContDiffAt.norm_sq ℝ contDiffAt_id)
    have h_lap : laplacian v x = laplacian u x + 2 * (n : ℝ) * ε := by
      rw [hv_def]
      rw [laplacian_add n _ _ x (h_smooth x hx) hc_norm, laplacian_norm_sq_smul]
    rw [h_lap]
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have := h_sub x hx
    nlinarith
  obtain ⟨p, hp_mem, hp_max⟩ := h_comp.exists_isMaxOn h_cl_ne h_v_cont
  have hp_Γ : p ∈ closure Ω \ Ω := by
    refine ⟨hp_mem, fun hp_int ↦ ?_⟩
    have h_nhds : closure Ω ∈ 𝓝 p :=
      mem_of_superset (hΩ_open.mem_nhds hp_int) subset_closure
    exact elliptic_no_interior_max hv_smooth hv_pos p hp_int
      (hp_max.isLocalMax h_nhds)
  refine csSup_le (h_cl_ne.image _) <| by
    rintro y ⟨q, hq, rfl⟩
    calc u q
        ≤ v q := le_add_of_nonneg_right (by positivity)
      _ ≤ v p := hp_max hq
      _ = u p + ε * ‖p‖ ^ 2 := rfl
      _ ≤ sSup (u '' (closure Ω \ Ω)) + ε * M :=
          add_le_add (le_csSup h_Γbdd ⟨p, hp_Γ, rfl⟩)
            (mul_le_mul_of_nonneg_left (h_norm_sq_le p hp_mem) hε.le)
      _ = sSup (u '' (closure Ω \ Ω)) + δ := by
          rw [hε_def, div_mul_cancel₀ δ hM_pos.ne']

/-- **Weak minimum principle for superharmonic functions** (blueprint
`cor:laplace-min-principle-nd`): under the same domain/regularity
hypotheses, if `Δ u ≤ 0` on `Ω` then the infimum of `u` over `closure Ω`
equals its infimum over the boundary. Apply `elliptic_max_principle` to
`-u` (subharmonic by `laplacian_neg`) and negate. -/
theorem elliptic_min_principle
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (hΩ_ne : Ω.Nonempty)
    {u : E n → ℝ}
    (h_cont : ContinuousOn u (closure Ω))
    (h_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (h_super : ∀ x ∈ Ω, laplacian u x ≤ 0) :
    sInf (u '' closure Ω) = sInf (u '' (closure Ω \ Ω)) := by
  have h_max := elliptic_max_principle hn hΩ_open hΩ_bdd hΩ_ne
    (u := fun x ↦ -u x) h_cont.neg
    (fun x hx ↦ (h_smooth x hx).neg)
    (fun x hx ↦ by
      rw [laplacian_neg n u x]
      linarith [h_super x hx])
  have h_img : ∀ A : Set (E n), (fun x ↦ -u x) '' A = -(u '' A) := by
    intro A
    ext y
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by ring⟩
    · rintro ⟨x, hx, hy⟩; exact ⟨x, hx, by linarith⟩
  rw [h_img, h_img, Real.sSup_neg, Real.sSup_neg, neg_inj] at h_max
  exact h_max

/-- **Pointwise boundary upper bound** (blueprint
`cor:laplace-subharmonic-le-boundary`): a subharmonic function is bounded
on `closure Ω` by the supremum of its boundary values. -/
theorem subharmonic_le_boundary_sup
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (hΩ_ne : Ω.Nonempty)
    {u : E n → ℝ}
    (h_cont : ContinuousOn u (closure Ω))
    (h_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (h_sub : ∀ x ∈ Ω, 0 ≤ laplacian u x)
    {x : E n} (hx : x ∈ closure Ω) :
    u x ≤ sSup (u '' (closure Ω \ Ω)) := by
  have h_comp : IsCompact (closure Ω) := hΩ_bdd.isCompact_closure
  have h_bdd : BddAbove (u '' closure Ω) :=
    (h_comp.image_of_continuousOn h_cont).bddAbove
  calc u x
      ≤ sSup (u '' closure Ω) := le_csSup h_bdd ⟨x, hx, rfl⟩
    _ = sSup (u '' (closure Ω \ Ω)) :=
        elliptic_max_principle hn hΩ_open hΩ_bdd hΩ_ne h_cont h_smooth h_sub

/-- **Pointwise boundary lower bound** (blueprint
`cor:laplace-superharmonic-ge-boundary`): a superharmonic function is
bounded below on `closure Ω` by the infimum of its boundary values. -/
theorem superharmonic_ge_boundary_inf
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (hΩ_ne : Ω.Nonempty)
    {u : E n → ℝ}
    (h_cont : ContinuousOn u (closure Ω))
    (h_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (h_super : ∀ x ∈ Ω, laplacian u x ≤ 0)
    {x : E n} (hx : x ∈ closure Ω) :
    sInf (u '' (closure Ω \ Ω)) ≤ u x := by
  have h_comp : IsCompact (closure Ω) := hΩ_bdd.isCompact_closure
  have h_bdd : BddBelow (u '' closure Ω) :=
    (h_comp.image_of_continuousOn h_cont).bddBelow
  calc sInf (u '' (closure Ω \ Ω))
      = sInf (u '' closure Ω) :=
        (elliptic_min_principle hn hΩ_open hΩ_bdd hΩ_ne h_cont h_smooth
          h_super).symm
    _ ≤ u x := csInf_le h_bdd ⟨x, hx, rfl⟩

end Laplace
