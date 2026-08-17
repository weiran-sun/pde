import Mathlib
import PDE.Basics.Laplace.LaplaceMaximumPrincipleND

/-!
# Undergraduate Problem 18: Comparison, Uniqueness, and Stability for Laplace's Equation

Source: `pde_latex/problems/undergraduate/problem_18.tex` (Math 418, HW-7, Problem 2).

## Informal statement

> Let `Ω ⊆ ℝⁿ` be open, bounded, and connected.
>
> (a) (Comparison Principle) If `u, v ∈ C²(Ω) ∩ C(closure Ω)` are both harmonic
> and `u ≥ v` on `∂Ω`, then `u ≥ v` on `closure Ω`.
>
> (b) (Uniqueness) If `u, v ∈ C²(Ω) ∩ C(closure Ω)` are both harmonic and
> `u = v` on `∂Ω`, then `u ≡ v` on `closure Ω`.
>
> (c) (Stability) For all `ε > 0` there exists `δ > 0` such that
> `‖u - v‖_{L^∞(∂Ω)} < δ` implies `‖u - v‖_{L^∞(closure Ω)} < ε`.

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem18.tex`:

* `Ω ⊆ ℝⁿ` is a set in `Heat.E n = EuclideanSpace ℝ (Fin n)`; the boundary
  `∂Ω` is spelled `closure Ω \ Ω` (for open `Ω` this is the topological
  frontier), as in the heat-side problems.
* "Harmonic on `Ω`" is `∀ x ∈ Ω, Heat.laplacian u x = 0` — the project's
  n-dimensional Laplacian (trace of the derivative of the gradient). A harmonic
  function is simultaneously subharmonic (`Δu ≥ 0`) and superharmonic
  (`Δu ≤ 0`), so both weak boundary-bound corollaries of the Laplace
  maximum-principle chapter apply to it.
* The `L^∞` norms of part (c) are spelled as `sSup` of the image of
  `fun x ↦ |u x - v x|` over `closure Ω` resp. `closure Ω \ Ω`; both sets are
  nonempty and compact and the function is continuous, so the suprema are
  attained.
* The statements carry the (unused) `IsConnected Ω` hypothesis to stay faithful
  to the problem as posed. The source names the *strong* maximum principle
  (which needs connectedness), but its actual solution uses only the weak
  boundary-supremum/infimum bounds
  (`Laplace.subharmonic_le_boundary_sup` / `Laplace.superharmonic_ge_boundary_inf`
  of `PDE/Basics/Laplace/LaplaceMaximumPrincipleND.lean`), which hold for any
  open bounded nonempty domain — per the blueprint chapter, the "strong
  maximum principle" phrasing is a proof hint whose applied corollary is
  exactly the weak boundary bound.
-/

open Set Bornology

namespace Problems.Undergraduate.Problem18

/-- The difference of two harmonic functions is harmonic: `Δ(u - v) = 0`
pointwise on `Ω`, by additivity of the Laplacian (`Heat.laplacian_add`)
and its commutation with negation (`Heat.laplacian_neg`). Shared helper
for `comparison` and `stability_estimate`. -/
private lemma laplacian_sub_eq_zero
    {n : ℕ} {Ω : Set (Heat.E n)}
    {u v : Heat.E n → ℝ}
    (hu_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hv_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hu_harm : ∀ x ∈ Ω, Heat.laplacian u x = 0)
    (hv_harm : ∀ x ∈ Ω, Heat.laplacian v x = 0) :
    ∀ x ∈ Ω, Heat.laplacian (fun y ↦ u y - v y) x = 0 := by
  intro x hx
  have h_eq : (fun y ↦ u y - v y) = fun y ↦ u y + (fun z ↦ -v z) y := by
    funext y
    simp [sub_eq_add_neg]
  rw [h_eq,
    Heat.laplacian_add n u (fun z ↦ -v z) x (hu_smooth x hx)
      (hv_smooth x hx).neg,
    Heat.laplacian_neg n v x, hu_harm x hx, hv_harm x hx]
  ring

/-- **Problem 18, part (a): comparison principle** (blueprint
`thm:problem18-comparison`).

Let `n ≥ 1`, let `Ω ⊆ ℝⁿ` be open, bounded, connected (and hence nonempty),
and let `u, v` be continuous on `closure Ω`, `C²` at every point of `Ω`, and
harmonic on `Ω`. If `u ≥ v` on the boundary `closure Ω \ Ω`, then `u ≥ v` on
all of `closure Ω`. -/
theorem comparison
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (Heat.E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : IsBounded Ω)
    (hΩ_conn : IsConnected Ω)
    {u v : Heat.E n → ℝ}
    (hu_cont : ContinuousOn u (closure Ω))
    (hv_cont : ContinuousOn v (closure Ω))
    (hu_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hv_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hu_harm : ∀ x ∈ Ω, Heat.laplacian u x = 0)
    (hv_harm : ∀ x ∈ Ω, Heat.laplacian v x = 0)
    (h_bdry : ∀ x ∈ closure Ω \ Ω, v x ≤ u x) :
    ∀ x ∈ closure Ω, v x ≤ u x := by
  intro x hx
  set w : Heat.E n → ℝ := fun y ↦ u y - v y with hw_def
  have hw_cont : ContinuousOn w (closure Ω) := hu_cont.sub hv_cont
  have hw_smooth : ∀ y ∈ Ω, ContDiffAt ℝ 2 w y :=
    fun y hy ↦ (hu_smooth y hy).sub (hv_smooth y hy)
  have hw_super : ∀ y ∈ Ω, Heat.laplacian w y ≤ 0 := fun y hy ↦
    (laplacian_sub_eq_zero hu_smooth hv_smooth hu_harm hv_harm y hy).le
  have h_bd_ne : (closure Ω \ Ω).Nonempty :=
    Laplace.elliptic_boundary_nonempty hn hΩ_open hΩ_bdd hΩ_conn.nonempty
  have h_inf_nonneg : 0 ≤ sInf (w '' (closure Ω \ Ω)) :=
    le_csInf (h_bd_ne.image w) (by
      rintro _ ⟨y, hy, rfl⟩
      exact sub_nonneg.mpr (h_bdry y hy))
  have h_ge := Laplace.superharmonic_ge_boundary_inf hn hΩ_open hΩ_bdd
    hΩ_conn.nonempty hw_cont hw_smooth hw_super hx
  have : 0 ≤ w x := le_trans h_inf_nonneg h_ge
  simpa [hw_def, sub_nonneg] using this

/-- **Problem 18, part (b): uniqueness for the Laplace equation** (blueprint
`thm:problem18-uniqueness`).

Under the domain hypotheses of `comparison`, two functions continuous on
`closure Ω`, `C²` and harmonic on `Ω`, that agree on the boundary
`closure Ω \ Ω` agree on all of `closure Ω`. -/
theorem uniqueness
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (Heat.E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : IsBounded Ω)
    (hΩ_conn : IsConnected Ω)
    {u v : Heat.E n → ℝ}
    (hu_cont : ContinuousOn u (closure Ω))
    (hv_cont : ContinuousOn v (closure Ω))
    (hu_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hv_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hu_harm : ∀ x ∈ Ω, Heat.laplacian u x = 0)
    (hv_harm : ∀ x ∈ Ω, Heat.laplacian v x = 0)
    (h_bdry : ∀ x ∈ closure Ω \ Ω, u x = v x) :
    ∀ x ∈ closure Ω, u x = v x := by
  intro x hx
  have h₁ : v x ≤ u x :=
    comparison hn hΩ_open hΩ_bdd hΩ_conn hu_cont hv_cont hu_smooth hv_smooth
      hu_harm hv_harm (fun y hy ↦ (h_bdry y hy).ge) x hx
  have h₂ : u x ≤ v x :=
    comparison hn hΩ_open hΩ_bdd hΩ_conn hv_cont hu_cont hv_smooth hu_smooth
      hv_harm hu_harm (fun y hy ↦ (h_bdry y hy).le) x hx
  exact le_antisymm h₂ h₁

/-- **Problem 18, part (c): sharp boundary estimate** (blueprint
`thm:problem18-stability-estimate`).

Under the domain hypotheses of `comparison`, for `u, v` continuous on
`closure Ω`, `C²` and harmonic on `Ω`, the supremum of `|u - v|` over
`closure Ω` is at most its supremum over the boundary `closure Ω \ Ω`.
(The reverse inequality is trivial by set inclusion, so this is the sharp
`L^∞` equality of the source; the `≤` direction is the one the stability
corollary uses.) -/
theorem stability_estimate
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (Heat.E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : IsBounded Ω)
    (hΩ_conn : IsConnected Ω)
    {u v : Heat.E n → ℝ}
    (hu_cont : ContinuousOn u (closure Ω))
    (hv_cont : ContinuousOn v (closure Ω))
    (hu_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hv_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hu_harm : ∀ x ∈ Ω, Heat.laplacian u x = 0)
    (hv_harm : ∀ x ∈ Ω, Heat.laplacian v x = 0) :
    sSup ((fun x ↦ |u x - v x|) '' closure Ω)
      ≤ sSup ((fun x ↦ |u x - v x|) '' (closure Ω \ Ω)) := by
  have hΩ_ne : Ω.Nonempty := hΩ_conn.nonempty
  set w : Heat.E n → ℝ := fun y ↦ u y - v y with hw_def
  have hw_cont : ContinuousOn w (closure Ω) := hu_cont.sub hv_cont
  have hw_smooth : ∀ y ∈ Ω, ContDiffAt ℝ 2 w y :=
    fun y hy ↦ (hu_smooth y hy).sub (hv_smooth y hy)
  have hw_harm : ∀ y ∈ Ω, Heat.laplacian w y = 0 :=
    laplacian_sub_eq_zero hu_smooth hv_smooth hu_harm hv_harm
  have h_bd_ne : (closure Ω \ Ω).Nonempty :=
    Laplace.elliptic_boundary_nonempty hn hΩ_open hΩ_bdd hΩ_ne
  -- the boundary is compact, so `|w|` has a supremum `B` on it
  have h_bd_comp : IsCompact (closure Ω \ Ω) :=
    hΩ_bdd.isCompact_closure.of_isClosed_subset
      (isClosed_closure.sdiff hΩ_open) sdiff_subset
  have h_abs_cont : ContinuousOn (fun y ↦ |w y|) (closure Ω \ Ω) :=
    (hw_cont.mono sdiff_subset).abs
  have h_abs_bdd : BddAbove ((fun y ↦ |w y|) '' (closure Ω \ Ω)) :=
    (h_bd_comp.image_of_continuousOn h_abs_cont).bddAbove
  set B : ℝ := sSup ((fun y ↦ |w y|) '' (closure Ω \ Ω)) with hB_def
  -- every boundary value of `w` lies in `[-B, B]`
  have h_bd_le : ∀ y ∈ closure Ω \ Ω, w y ≤ B := fun y hy ↦
    (le_abs_self (w y)).trans (le_csSup h_abs_bdd ⟨y, hy, rfl⟩)
  have h_bd_ge : ∀ y ∈ closure Ω \ Ω, -B ≤ w y := fun y hy ↦
    neg_le_neg (le_csSup h_abs_bdd ⟨y, hy, rfl⟩) |>.trans (neg_abs_le (w y))
  -- pointwise bound `|w x| ≤ B` on `closure Ω` via both weak principles
  have h_ptwise : ∀ x ∈ closure Ω, |w x| ≤ B := by
    intro x hx
    rw [abs_le]
    constructor
    · have h_inf : -B ≤ sInf (w '' (closure Ω \ Ω)) :=
        le_csInf (h_bd_ne.image w) (by rintro _ ⟨y, hy, rfl⟩; exact h_bd_ge y hy)
      exact h_inf.trans
        (Laplace.superharmonic_ge_boundary_inf hn hΩ_open hΩ_bdd hΩ_ne
          hw_cont hw_smooth (fun y hy ↦ (hw_harm y hy).le) hx)
    · have h_sup : sSup (w '' (closure Ω \ Ω)) ≤ B :=
        csSup_le (h_bd_ne.image w) (by rintro _ ⟨y, hy, rfl⟩; exact h_bd_le y hy)
      exact (Laplace.subharmonic_le_boundary_sup hn hΩ_open hΩ_bdd hΩ_ne
        hw_cont hw_smooth (fun y hy ↦ (hw_harm y hy).ge) hx).trans h_sup
  exact csSup_le ((hΩ_ne.mono subset_closure).image _)
    (by rintro _ ⟨x, hx, rfl⟩; exact h_ptwise x hx)

/-- **Problem 18, part (c): `ε`–`δ` stability** (blueprint
`cor:problem18-stability`).

The Laplace equation with the Dirichlet condition is stable: under the
hypotheses of `stability_estimate`, for every `ε > 0` there exists `δ > 0`
(namely `δ = ε`) such that if the boundary supremum of `|u - v|` is below `δ`
then the supremum over all of `closure Ω` is below `ε`. -/
theorem stability
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (Heat.E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : IsBounded Ω)
    (hΩ_conn : IsConnected Ω)
    {u v : Heat.E n → ℝ}
    (hu_cont : ContinuousOn u (closure Ω))
    (hv_cont : ContinuousOn v (closure Ω))
    (hu_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hv_smooth : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hu_harm : ∀ x ∈ Ω, Heat.laplacian u x = 0)
    (hv_harm : ∀ x ∈ Ω, Heat.laplacian v x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0,
      sSup ((fun x ↦ |u x - v x|) '' (closure Ω \ Ω)) < δ →
      sSup ((fun x ↦ |u x - v x|) '' closure Ω) < ε :=
  ⟨ε, hε, fun h ↦
    lt_of_le_of_lt
      (stability_estimate hn hΩ_open hΩ_bdd hΩ_conn hu_cont hv_cont hu_smooth
        hv_smooth hu_harm hv_harm) h⟩

end Problems.Undergraduate.Problem18
