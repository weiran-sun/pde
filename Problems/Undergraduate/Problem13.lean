import Mathlib
import PDE
import PDE.Basics.Heat.HeatKernelND
import PDE.Basics.Heat.HeatMaximumPrincipleND

/-!
# Undergraduate Problem 13: Comparison Principle and L∞-Stability for the Heat Equation

Source: `pde_latex/problems/undergraduate/problem_13.tex` (Math 418, HW-5, Problem 3).

## Informal statement

> (Consequences of the weak maximum principle/comparison principle) Let
> `Ω ⊆ ℝⁿ` be an open and bounded set, `T > 0`, `Ω_T = Ω × (0, T]`, and
> `Γ_T = closure(Ω_T) \ Ω_T` the parabolic boundary. Suppose
> `u, v ∈ C²₁(Ω_T) ∩ C(closure(Ω_T))` satisfy the heat equation
> `u_t = Δu` and `v_t = Δv` in `Ω_T` with prescribed lateral data `g₁, g₂`
> and initial data `h₁, h₂`.
>
> (d) Write down the precise mathematical formulation (in terms of `ε, δ`) for
> the sentence "the heat equation above is stable in the `L∞`-norm". Prove that
> the heat equation above is indeed stable in the `L∞`-norm.
>
> (e) [...] Use the comparison principle.

Per the blueprint chapter `Problems_Undergraduate_Problem13.tex`, this file
formalizes the two reusable consequences of the weak maximum principle the
solution employs: the **comparison principle** (a subsolution dominated by a
supersolution on the parabolic boundary stays dominated on the closed
cylinder) and the **sup-norm stability estimate** (the sup-norm of the
difference of two solutions over the closed cylinder is bounded by its
sup-norm over the parabolic boundary).

## Semantic alignment

* The parabolic cylinder `Ω_T = Ω × (0, T]` is `Ω ×ˢ Set.Ioc 0 T ⊆ E n × ℝ`,
  and the parabolic boundary `Γ_T = closure(Ω_T) \ Ω_T` is spelled inline as
  `closure (Ω ×ˢ Set.Ioc 0 T) \ (Ω ×ˢ Set.Ioc 0 T)`, exactly as in
  `Problems/Undergraduate/Problem11.lean` (the named
  `Heat.parabolicCylinder` / `Heat.parabolicBoundary` are being
  introduced concurrently in `PDE/Basics/Heat/HeatMaximumPrincipleND.lean`;
  the sets are definitionally the same).
* `C²₁(Ω_T)` follows the project convention of the heat chapters: joint
  `ContDiffOn ℝ 2` of `(x, t) ↦ u x t` on the cylinder `Ω ×ˢ Ioc 0 T`
  (within-set differentiability, so the time derivative at the top edge
  `t = T` is the one-sided one).
* The time derivative on the cylinder is
  `derivWithin (fun t' ↦ u x t') (Set.Iic T) t` — the ordinary two-sided
  derivative for `0 < t < T` and the one-sided derivative from below at
  `t = T`. The Laplacian is the project's n-dimensional `Heat.laplacian`,
  genuinely two-sided in `x` since `Ω` is open. Diffusivity `α = 1` as in the
  source.
* Sub/supersolutions: the comparison principle is stated (per the blueprint's
  general form) for `∂ₜ u ≤ Δu` and `∂ₜ v ≥ Δv`; exact solutions of
  `∂ₜ u = Δu` are simultaneously sub- and supersolutions, so the source's
  two-solutions case is an instance.
* The `L∞`-norm of a continuous function over the compact sets
  `closure Ω_T` and `Γ_T` is `sSup` of the image of `(x,t) ↦ |u x t - v x t|`
  on the indicated set — both finite and attained (blueprint
  `lem:heat-parabolic-compact`). The stability statement
  `sSup (|u-v| '' closure Ω_T) ≤ sSup (|u-v| '' Γ_T)` is exactly the
  source's ε-δ stability with `δ = ε` (the reverse inequality is immediate
  from `Γ_T ⊆ closure Ω_T`, so the stated inequality is the substance).
* `Ω.Nonempty` is assumed so both suprema are genuinely attained maxima.
* Both proofs route through the generalized weak maximum principle
  `Heat.heat_equation_max_principle` (blueprint
  `thm:heat-max-principle-nd`), PROVED axiom-clean in
  `PDE/Basics/Heat/HeatMaximumPrincipleND.lean` (iter-029).
-/

open Set Bornology

namespace Problems.Undergraduate.Problem13

/-- The Laplacian of a constant function vanishes: the gradient of a constant
is the zero field, whose `fderiv` is the zero map with zero trace. Helper for
`stability` (constant vertical shifts of solutions are again solutions). -/
lemma laplacian_const {n : ℕ} (c : ℝ) (x : Heat.E n) :
    Heat.laplacian (fun _ ↦ c) x = 0 := by
  unfold Heat.laplacian Heat.div_field
  rw [gradient_fun_const' (F := Heat.E n) c, fderiv_fun_const]
  simp

/-- **Problem 13: comparison principle for the heat equation** (blueprint
`thm:problem13-comparison`).

Let `n ≥ 1`, let `Ω ⊆ ℝⁿ` be open, bounded and nonempty, and let `T > 0`.
Write `Ω_T = Ω ×ˢ Ioc 0 T` for the parabolic cylinder and
`Γ_T = closure Ω_T \ Ω_T` for the parabolic boundary. If
`u, v : ℝⁿ → ℝ → ℝ` are continuous on `closure Ω_T` and `C²₁` on `Ω_T`,
`u` is a subsolution (`∂ₜ u ≤ Δu`) and `v` a supersolution (`∂ₜ v ≥ Δv`) of
the heat equation on `Ω_T` (one-sided time derivative at the top edge
`t = T`), and `u ≤ v` on the parabolic boundary `Γ_T`, then `u ≤ v` on the
whole closed cylinder `closure Ω_T`. In particular this applies when `u` and
`v` are exact solutions of `∂ₜ u = Δu`. -/
theorem comparison
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (Heat.E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : IsBounded Ω)
    (hΩ_ne : Ω.Nonempty)
    {T : ℝ} (hT : 0 < T)
    (u v : Heat.E n → ℝ → ℝ)
    (hu_cont : ContinuousOn (fun p : Heat.E n × ℝ ↦ u p.1 p.2)
      (closure (Ω ×ˢ Ioc 0 T)))
    (hv_cont : ContinuousOn (fun p : Heat.E n × ℝ ↦ v p.1 p.2)
      (closure (Ω ×ˢ Ioc 0 T)))
    (hu_smooth : ContDiffOn ℝ 2 (fun p : Heat.E n × ℝ ↦ u p.1 p.2)
      (Ω ×ˢ Ioc 0 T))
    (hv_smooth : ContDiffOn ℝ 2 (fun p : Heat.E n × ℝ ↦ v p.1 p.2)
      (Ω ×ˢ Ioc 0 T))
    (hu_sub : ∀ x t, (x, t) ∈ Ω ×ˢ Ioc 0 T →
      derivWithin (fun t' ↦ u x t') (Iic T) t
        ≤ Heat.laplacian (fun x' ↦ u x' t) x)
    (hv_super : ∀ x t, (x, t) ∈ Ω ×ˢ Ioc 0 T →
      Heat.laplacian (fun x' ↦ v x' t) x
        ≤ derivWithin (fun t' ↦ v x t') (Iic T) t)
    (h_bdry : ∀ x t, (x, t) ∈ closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T) →
      u x t ≤ v x t) :
    ∀ x t, (x, t) ∈ closure (Ω ×ˢ Ioc 0 T) → u x t ≤ v x t := by
  -- `w = u - v` is a subsolution; apply the weak maximum principle (α = 1).
  have h_max := Heat.heat_equation_max_principle hn hΩ_open hΩ_bdd hΩ_ne hT
    one_pos (fun x t ↦ u x t - v x t)
    (hu_cont.sub hv_cont)
    (hu_smooth.sub hv_smooth)
    (fun x t hxt ↦ by
      obtain ⟨hx, ht⟩ := hxt
      -- near `t ∈ Ioc 0 T` the time slice sets `Iic T` and `Ioc 0 T` agree
      have hset : Iic T =ᶠ[nhds t] Ioc 0 T := by
        rw [Filter.eventuallyEq_set]
        filter_upwards [Ioi_mem_nhds ht.1] with s hs
        exact ⟨fun h ↦ ⟨hs, h⟩, fun h ↦ h.2⟩
      -- time slices of `u`, `v` are differentiable within `Iic T` at `t`
      have h_maps_t : MapsTo (fun t' : ℝ ↦ (x, t')) (Ioc 0 T) (Ω ×ˢ Ioc 0 T) :=
        fun t' ht' ↦ ⟨hx, ht'⟩
      have hu_t : DifferentiableWithinAt ℝ (fun t' ↦ u x t') (Iic T) t :=
        (differentiableWithinAt_congr_set hset).mpr
          ((hu_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
            h_maps_t).differentiableOn (by norm_num) t ht)
      have hv_t : DifferentiableWithinAt ℝ (fun t' ↦ v x t') (Iic T) t :=
        (differentiableWithinAt_congr_set hset).mpr
          ((hv_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
            h_maps_t).differentiableOn (by norm_num) t ht)
      -- spatial slices of `u`, `v` are C² at `x`
      have h_maps_x : MapsTo (fun x' ↦ (x', t)) Ω (Ω ×ˢ Ioc 0 T) :=
        fun x' hx' ↦ ⟨hx', ht⟩
      have hcu : ContDiffAt ℝ 2 (fun x' ↦ u x' t) x :=
        (hu_smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
          h_maps_x).contDiffAt (hΩ_open.mem_nhds hx)
      have hcv : ContDiffAt ℝ 2 (fun x' ↦ v x' t) x :=
        (hv_smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
          h_maps_x).contDiffAt (hΩ_open.mem_nhds hx)
      have h_lap : Heat.laplacian (fun x' ↦ u x' t - v x' t) x
          = Heat.laplacian (fun x' ↦ u x' t) x
            - Heat.laplacian (fun x' ↦ v x' t) x := by
        have h := Heat.laplacian_add n (fun x' ↦ u x' t) (fun x' ↦ -v x' t) x
          hcu hcv.neg
        rw [Heat.laplacian_neg] at h
        simpa [sub_eq_add_neg] using h
      have h_dt : derivWithin (fun t' ↦ u x t' - v x t') (Iic T) t
          = derivWithin (fun t' ↦ u x t') (Iic T) t
            - derivWithin (fun t' ↦ v x t') (Iic T) t :=
        derivWithin_fun_sub hu_t hv_t
      rw [one_mul, h_dt, h_lap]
      have h1 := hu_sub x t ⟨hx, ht⟩
      have h2 := hv_super x t ⟨hx, ht⟩
      linarith)
  -- compactness gives boundedness of the image over the closed cylinder
  obtain ⟨h_cl_comp, h_cl_ne, h_Γ_comp, h_Γ_ne⟩ :=
    Heat.parabolic_compact_nonempty n hΩ_open hΩ_bdd hΩ_ne hT
  have h_cl_comp' : IsCompact (closure (Ω ×ˢ Ioc 0 T)) := h_cl_comp
  have h_Γ_ne' : (closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T)).Nonempty := h_Γ_ne
  have h_bdd : BddAbove ((fun p : Heat.E n × ℝ ↦ u p.1 p.2 - v p.1 p.2) ''
      closure (Ω ×ˢ Ioc 0 T)) :=
    (h_cl_comp'.image_of_continuousOn (hu_cont.sub hv_cont)).bddAbove
  -- the boundary supremum is ≤ 0 by `h_bdry`
  have h_Γ_le : sSup ((fun p : Heat.E n × ℝ ↦ u p.1 p.2 - v p.1 p.2) ''
      (closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T))) ≤ 0 :=
    csSup_le (h_Γ_ne'.image _) (by
      rintro y ⟨p, hp, rfl⟩
      exact sub_nonpos.mpr (h_bdry p.1 p.2 hp))
  intro x t hxt
  have h_le_sup : u x t - v x t
      ≤ sSup ((fun p : Heat.E n × ℝ ↦ u p.1 p.2 - v p.1 p.2) ''
          closure (Ω ×ˢ Ioc 0 T)) :=
    le_csSup h_bdd ⟨(x, t), hxt, rfl⟩
  rw [h_max] at h_le_sup
  linarith

/-- **Problem 13: sup-norm stability for the heat equation** (blueprint
`thm:problem13-stability`).

Under the standing hypotheses (`n ≥ 1`, `Ω ⊆ ℝⁿ` open bounded nonempty,
`T > 0`), if `u, v : ℝⁿ → ℝ → ℝ` are continuous on `closure Ω_T`, `C²₁` on
`Ω_T`, and exact solutions of the heat equation `∂ₜ u = Δu`, `∂ₜ v = Δv` on
`Ω_T`, then the sup-norm of `u - v` over the closed cylinder is bounded by
its sup-norm over the parabolic boundary:
`sSup (|u - v| '' closure Ω_T) ≤ sSup (|u - v| '' Γ_T)` — both suprema of
images of a continuous function on compact sets, hence finite and attained.
This is the source's part (d): the heat equation is stable in the `L∞`-norm
(take `δ = ε`). -/
theorem stability
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (Heat.E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : IsBounded Ω)
    (hΩ_ne : Ω.Nonempty)
    {T : ℝ} (hT : 0 < T)
    (u v : Heat.E n → ℝ → ℝ)
    (hu_cont : ContinuousOn (fun p : Heat.E n × ℝ ↦ u p.1 p.2)
      (closure (Ω ×ˢ Ioc 0 T)))
    (hv_cont : ContinuousOn (fun p : Heat.E n × ℝ ↦ v p.1 p.2)
      (closure (Ω ×ˢ Ioc 0 T)))
    (hu_smooth : ContDiffOn ℝ 2 (fun p : Heat.E n × ℝ ↦ u p.1 p.2)
      (Ω ×ˢ Ioc 0 T))
    (hv_smooth : ContDiffOn ℝ 2 (fun p : Heat.E n × ℝ ↦ v p.1 p.2)
      (Ω ×ˢ Ioc 0 T))
    (hu_pde : ∀ x t, (x, t) ∈ Ω ×ˢ Ioc 0 T →
      derivWithin (fun t' ↦ u x t') (Iic T) t
        = Heat.laplacian (fun x' ↦ u x' t) x)
    (hv_pde : ∀ x t, (x, t) ∈ Ω ×ˢ Ioc 0 T →
      derivWithin (fun t' ↦ v x t') (Iic T) t
        = Heat.laplacian (fun x' ↦ v x' t) x) :
    sSup ((fun p : Heat.E n × ℝ ↦ |u p.1 p.2 - v p.1 p.2|) ''
        closure (Ω ×ˢ Ioc 0 T))
      ≤ sSup ((fun p : Heat.E n × ℝ ↦ |u p.1 p.2 - v p.1 p.2|) ''
          (closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T))) := by
  obtain ⟨h_cl_comp, h_cl_ne, h_Γ_comp, h_Γ_ne⟩ :=
    Heat.parabolic_compact_nonempty n hΩ_open hΩ_bdd hΩ_ne hT
  have h_cl_ne' : (closure (Ω ×ˢ Ioc 0 T)).Nonempty := h_cl_ne
  have h_Γ_comp' : IsCompact (closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T)) := h_Γ_comp
  have h_Γ_sub : closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T) ⊆
      closure (Ω ×ˢ Ioc 0 T) := Set.sdiff_subset
  -- `M` = sup of `|u - v|` over the parabolic boundary
  set M := sSup ((fun p : Heat.E n × ℝ ↦ |u p.1 p.2 - v p.1 p.2|) ''
      (closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T))) with hM_def
  have h_abs_cont : ContinuousOn
      (fun p : Heat.E n × ℝ ↦ |u p.1 p.2 - v p.1 p.2|)
      (closure (Ω ×ˢ Ioc 0 T)) := (hu_cont.sub hv_cont).abs
  have h_Γ_bdd : BddAbove ((fun p : Heat.E n × ℝ ↦ |u p.1 p.2 - v p.1 p.2|) ''
      (closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T))) :=
    (h_Γ_comp'.image_of_continuousOn (h_abs_cont.mono h_Γ_sub)).bddAbove
  have h_bd_le : ∀ x t, (x, t) ∈ closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T) →
      |u x t - v x t| ≤ M :=
    fun x t h ↦ le_csSup h_Γ_bdd ⟨(x, t), h, rfl⟩
  -- shifting a solution `w` by the constant `M` keeps it a supersolution
  have h_shift_super : ∀ w : Heat.E n → ℝ → ℝ,
      ContDiffOn ℝ 2 (fun p : Heat.E n × ℝ ↦ w p.1 p.2) (Ω ×ˢ Ioc 0 T) →
      (∀ x t, (x, t) ∈ Ω ×ˢ Ioc 0 T →
        derivWithin (fun t' ↦ w x t') (Iic T) t
          = Heat.laplacian (fun x' ↦ w x' t) x) →
      ∀ x t, (x, t) ∈ Ω ×ˢ Ioc 0 T →
        Heat.laplacian (fun x' ↦ w x' t + M) x
          ≤ derivWithin (fun t' ↦ w x t' + M) (Iic T) t := by
    intro w hw_smooth hw_pde x t hxt
    obtain ⟨hx, ht⟩ := hxt
    have h_maps_x : MapsTo (fun x' ↦ (x', t)) Ω (Ω ×ˢ Ioc 0 T) :=
      fun x' hx' ↦ ⟨hx', ht⟩
    have hcw : ContDiffAt ℝ 2 (fun x' ↦ w x' t) x :=
      (hw_smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        h_maps_x).contDiffAt (hΩ_open.mem_nhds hx)
    have h_lap : Heat.laplacian (fun x' ↦ w x' t + M) x
        = Heat.laplacian (fun x' ↦ w x' t) x := by
      rw [Heat.laplacian_add n (fun x' ↦ w x' t) (fun _ ↦ M) x hcw
        contDiffAt_const, laplacian_const, add_zero]
    rw [h_lap, derivWithin_add_const M]
    exact ge_of_eq (hw_pde x t ⟨hx, ht⟩)
  -- exact solutions are subsolutions
  have h_sub_of_pde : ∀ w : Heat.E n → ℝ → ℝ,
      (∀ x t, (x, t) ∈ Ω ×ˢ Ioc 0 T →
        derivWithin (fun t' ↦ w x t') (Iic T) t
          = Heat.laplacian (fun x' ↦ w x' t) x) →
      ∀ x t, (x, t) ∈ Ω ×ˢ Ioc 0 T →
        derivWithin (fun t' ↦ w x t') (Iic T) t
          ≤ Heat.laplacian (fun x' ↦ w x' t) x :=
    fun w hw x t hxt ↦ le_of_eq (hw x t hxt)
  -- comparison for the pair (u, v + M): u - v ≤ M on the closed cylinder
  have h_uv : ∀ x t, (x, t) ∈ closure (Ω ×ˢ Ioc 0 T) → u x t ≤ v x t + M :=
    comparison hn hΩ_open hΩ_bdd hΩ_ne hT u (fun x t ↦ v x t + M)
      hu_cont (hv_cont.add continuousOn_const)
      hu_smooth (hv_smooth.add contDiffOn_const)
      (h_sub_of_pde u hu_pde)
      (h_shift_super v hv_smooth hv_pde)
      (fun x t hxt ↦ by
        have := h_bd_le x t hxt
        have h1 : u x t - v x t ≤ |u x t - v x t| := le_abs_self _
        linarith)
  -- comparison for the pair (v, u + M): v - u ≤ M on the closed cylinder
  have h_vu : ∀ x t, (x, t) ∈ closure (Ω ×ˢ Ioc 0 T) → v x t ≤ u x t + M :=
    comparison hn hΩ_open hΩ_bdd hΩ_ne hT v (fun x t ↦ u x t + M)
      hv_cont (hu_cont.add continuousOn_const)
      hv_smooth (hu_smooth.add contDiffOn_const)
      (h_sub_of_pde v hv_pde)
      (h_shift_super u hu_smooth hu_pde)
      (fun x t hxt ↦ by
        have := h_bd_le x t hxt
        have h1 : -(u x t - v x t) ≤ |u x t - v x t| := neg_le_abs _
        linarith)
  -- pointwise `|u - v| ≤ M` on the closure, then pass to the supremum
  refine csSup_le (h_cl_ne'.image _) ?_
  rintro y ⟨p, hp, rfl⟩
  have h1 := h_uv p.1 p.2 hp
  have h2 := h_vu p.1 p.2 hp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Problems.Undergraduate.Problem13
