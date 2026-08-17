import Mathlib
import PDE
import PDE.Basics.Heat.HeatKernelND
import PDE.Basics.Heat.HeatMaximumPrincipleND

/-!
# Undergraduate Problem 12: Supersolutions of the Heat Equation — the Minimum Principle Persists, the Maximum Principle Fails

Source: `pde_latex/problems/undergraduate/problem_12.tex` (Math 418, HW-5, Problem 2).

## Informal statement

> Let `Ω ⊆ ℝⁿ` be an open and bounded set, `T > 0`, `Ω_T = Ω × (0, T]`, and
> `Γ_T = closure(Ω_T) \ Ω_T` the parabolic boundary, as in Problem 1.
>
> (a) Suppose `u ∈ C²₁(Ω_T) ∩ C(closure(Ω_T))` satisfies the inequality
> ```
>   u_t(x, t) ≥ Δu(x, t),   (x, t) ∈ Ω_T,
> ```
> instead of the heat equation with the equal sign. Prove that
> ```
>   min_{closure(Ω_T)} u(x, t) = min_{Γ_T} u(x, t)
> ```
> still holds in this case.
>
> (b) Suppose `u` satisfies the inequality `u_t ≥ Δu` as above. Does the maximum
> version
> ```
>   max_{closure(Ω_T)} u(x, t) = max_{Γ_T} u(x, t)
> ```
> still hold? Prove it if your answer is yes or show a counterexample if your
> answer is no. You can work in the 1D setting where `u` satisfies `u_t ≥ u_xx`
> on `(a, b) × (0, T]`.

## Semantic alignment

* The parabolic cylinder `Ω_T = Ω × (0, T]` is `Ω ×ˢ Set.Ioc 0 T ⊆ E n × ℝ`,
  and the parabolic boundary is spelled out verbatim as
  `closure (Ω ×ˢ Set.Ioc 0 T) \ (Ω ×ˢ Set.Ioc 0 T)`, exactly as in Problem 11
  (inline, not through the named `Heat.parabolicCylinder` /
  `Heat.parabolicBoundary` of the Heat lane; the sets are definitionally
  the same).
* "Twice continuously differentiable in `x`, once in `t`, one-sided at `t = T`"
  is formalized, per the heat-chapter convention, as joint `ContDiffOn ℝ 2` on
  `Ω ×ˢ Ioc 0 T` (within-set differentiability, so the time derivative at the
  top edge is the one-sided one).
* The supersolution inequality `u_t ≥ Δu` on `Ω_T`: the time derivative is
  `derivWithin (fun t' ↦ u x t') (Set.Iic T) t` (ordinary two-sided derivative
  for `0 < t < T`, one-sided from below at `t = T`), and the Laplacian is the
  project's n-dimensional `Heat.laplacian` (trace of the derivative of the
  gradient), two-sided in `x` since `Ω` is open. The only change from
  Problem 11 is `=` → `≥` in the PDE hypothesis.
* Part (a): the informal problem asks only to indicate the modifications to the
  proof of Problem 1 (the `(∗)`-step of the perturbation argument turns from an
  equality contradiction into an inequality contradiction); per the blueprint's
  semantic-alignment note, the formal deliverable is the full true statement,
  to be derived from `Heat.heat_equation_min_principle` (blueprint
  `cor:heat-min-principle`, stated for supersolutions `u_t ≥ α Δu`) at `α = 1`.
* Part (b): the counterexample is stated concretely, following the blueprint
  theorem `thm:problem12-max-fails`: `n = 1`, `Ω = (0, 1)` (encoded as
  `{x : E 1 | x 0 ∈ Ioo 0 1}`), `u (x, t) = t + x(1 - x)` (encoded as
  `fun x t ↦ t + x 0 * (1 - x 0)`). The theorem asserts that this `u` has all
  the regularity and supersolution properties of part (a)'s hypotheses and yet
  `sSup (u '' closure Ω_T) ≠ sSup (u '' Γ_T)` — so the maximum version of the
  principle fails. (Informally: the sup over the closed cylinder is `T + 1/4`,
  attained only at `(1/2, T)`, a point of the open top edge not in `Γ_T`, while
  the sup over `Γ_T` is `max {T, 1/4} < T + 1/4`.)
* Each side of the min/max identities is `sInf`/`sSup` of the image of `u` on
  the indicated set; the sets are nonempty and compact and `u` is continuous
  there, so the images are nonempty compact subsets of `ℝ` and the infima /
  suprema are attained — the well-definedness discussion of the blueprint.
-/

open Set Bornology

namespace Problems.Undergraduate.Problem12

/-- **Problem 12 (a): weak minimum principle for supersolutions** (blueprint
`thm:problem12-min-supersolution`).

Let `n ≥ 1`, let `Ω ⊆ ℝⁿ` be open, bounded and nonempty, and let `T > 0`. Write
`Ω_T = Ω ×ˢ Ioc 0 T` for the parabolic cylinder and `Γ_T = closure Ω_T \ Ω_T`
for the parabolic boundary. If `u : ℝⁿ → ℝ → ℝ` is continuous on
`closure Ω_T`, is `C²₁` on `Ω_T`, and is a *supersolution* of the heat
equation, `∂ₜ u ≥ Δu` on `Ω_T` (one-sided time derivative at the top edge
`t = T`), then the infimum of `u` over `closure Ω_T` equals its infimum over
`Γ_T` — both attained, so they are genuine minima. -/
theorem min_principle_supersolution
    {n : ℕ} (hn : 0 < n)
    {Ω : Set (Heat.E n)} (hΩ_open : IsOpen Ω) (hΩ_bdd : IsBounded Ω)
    (hΩ_ne : Ω.Nonempty)
    {T : ℝ} (hT : 0 < T)
    (u : Heat.E n → ℝ → ℝ)
    (h_cont : ContinuousOn (fun p : Heat.E n × ℝ ↦ u p.1 p.2)
      (closure (Ω ×ˢ Ioc 0 T)))
    (h_smooth : ContDiffOn ℝ 2 (fun p : Heat.E n × ℝ ↦ u p.1 p.2)
      (Ω ×ˢ Ioc 0 T))
    (h_pde : ∀ x t, (x, t) ∈ Ω ×ˢ Ioc 0 T →
      derivWithin (fun t' ↦ u x t') (Iic T) t
        ≥ Heat.laplacian (fun x' ↦ u x' t) x) :
    sInf ((fun p : Heat.E n × ℝ ↦ u p.1 p.2) '' closure (Ω ×ˢ Ioc 0 T))
      = sInf ((fun p : Heat.E n × ℝ ↦ u p.1 p.2) ''
          (closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T))) := by
  exact Heat.heat_equation_min_principle hn hΩ_open hΩ_bdd hΩ_ne hT one_pos
    u h_cont h_smooth
    (fun x t hxt ↦ by rw [one_mul]; exact h_pde x t hxt)

/-- **Problem 12 (b): failure of the maximum principle for supersolutions**
(blueprint `thm:problem12-max-fails`).

The maximum version of the minimum principle for supersolutions fails.
Concretely, in dimension `n = 1` with `Ω = (0, 1)` and any `T > 0`, the
function `u (x, t) = t + x (1 - x)` is continuous on `closure Ω_T`, is `C²₁`
on `Ω_T` (indeed jointly smooth everywhere), and is a supersolution of the
heat equation (`∂ₜ u = 1 ≥ -2 = Δu`), and yet the supremum of `u` over the
closed cylinder differs from its supremum over the parabolic boundary:
`sup (u '' closure Ω_T) = T + 1/4`, attained only at the open top-edge point
`(1/2, T) ∉ Γ_T`, while `sup (u '' Γ_T) = max {T, 1/4} < T + 1/4`. -/
theorem max_principle_fails
    {T : ℝ} (hT : 0 < T)
    (Ω : Set (Heat.E 1)) (hΩ : Ω = {x : Heat.E 1 | x 0 ∈ Ioo (0 : ℝ) 1})
    (u : Heat.E 1 → ℝ → ℝ) (hu : u = fun x t ↦ t + x 0 * (1 - x 0)) :
    ContinuousOn (fun p : Heat.E 1 × ℝ ↦ u p.1 p.2)
        (closure (Ω ×ˢ Ioc 0 T))
      ∧ ContDiffOn ℝ 2 (fun p : Heat.E 1 × ℝ ↦ u p.1 p.2) (Ω ×ˢ Ioc 0 T)
      ∧ (∀ x t, (x, t) ∈ Ω ×ˢ Ioc 0 T →
          derivWithin (fun t' ↦ u x t') (Iic T) t
            ≥ Heat.laplacian (fun x' ↦ u x' t) x)
      ∧ sSup ((fun p : Heat.E 1 × ℝ ↦ u p.1 p.2) ''
            closure (Ω ×ˢ Ioc 0 T))
          ≠ sSup ((fun p : Heat.E 1 × ℝ ↦ u p.1 p.2) ''
              (closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T))) := by
  subst hΩ hu
  -- `u` is a polynomial in `(x 0, t)`, hence jointly smooth everywhere.
  have h_smooth : ContDiff ℝ 2
      (fun p : Heat.E 1 × ℝ ↦ p.2 + p.1 0 * (1 - p.1 0)) := by
    fun_prop
  refine ⟨h_smooth.continuous.continuousOn, h_smooth.contDiffOn, ?_, ?_⟩
  · -- Supersolution: `∂ₜ u = 1 ≥ -2 = Δu`.
    rintro x t ⟨-, -, htT⟩
    have hderiv : derivWithin (fun t' ↦ t' + x 0 * (1 - x 0)) (Iic T) t = 1 := by
      have huniq : UniqueDiffWithinAt ℝ (Iic T) t :=
        uniqueDiffOn_Iic T t htT
      exact (((hasDerivWithinAt_id t (Iic T)).add_const _)).derivWithin huniq
    have hlap : Heat.laplacian (fun x' : Heat.E 1 ↦ t + x' 0 * (1 - x' 0)) x
        = -2 := by
      rw [Heat.laplacian_eq_sum_deriv 1 (by fun_prop)]
      have hpt : ∀ s : ℝ,
          x + s • (WithLp.equiv 2 (Fin 1 → ℝ)).symm (Pi.single 0 (1 : ℝ)) =
            (WithLp.equiv 2 (Fin 1 → ℝ)).symm (Pi.single 0 (x 0 + s)) := by
        intro s
        apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
        funext i
        fin_cases i; simp
      have hinner : ∀ s : ℝ,
          (fun s : ℝ ↦ t + (x 0 + s) * (1 - (x 0 + s))) s =
            t + (x + s • (WithLp.equiv 2 (Fin 1 → ℝ)).symm
              (Pi.single 0 (1 : ℝ))) 0 * (1 - (x + s • (WithLp.equiv 2 (Fin 1 → ℝ)).symm
              (Pi.single 0 (1 : ℝ))) 0) := by
        intro s; rw [hpt s]; simp
      have hderiv1 : ∀ y : ℝ,
          deriv (fun s : ℝ ↦ t + (x 0 + s) * (1 - (x 0 + s))) y
            = 1 - 2 * x 0 - 2 * y := by
        intro y
        have h1 : HasDerivAt (fun s : ℝ ↦ x 0 + s) 1 y := by
          simpa using (hasDerivAt_id y).const_add (x 0)
        have h2 : HasDerivAt (fun s : ℝ ↦ 1 - (x 0 + s)) (-1) y := by
          simpa using h1.const_sub 1
        have h3 : HasDerivAt (fun s : ℝ ↦ t + (x 0 + s) * (1 - (x 0 + s)))
            (1 * (1 - (x 0 + y)) + (x 0 + y) * -1) y := (h1.mul h2).const_add t
        rw [h3.deriv]; ring
      rw [Fin.sum_univ_one]
      have hfun : (fun s : ℝ ↦ t + (x + s • (WithLp.equiv 2 (Fin 1 → ℝ)).symm
            (Pi.single 0 (1 : ℝ))) 0 * (1 - (x + s • (WithLp.equiv 2 (Fin 1 → ℝ)).symm
            (Pi.single 0 (1 : ℝ))) 0))
          = fun s : ℝ ↦ t + (x 0 + s) * (1 - (x 0 + s)) := by
        funext s; exact (hinner s).symm
      rw [hfun]
      have houter : (fun t' : ℝ ↦
            deriv (fun s : ℝ ↦ t + (x 0 + s) * (1 - (x 0 + s))) t')
          = fun t' : ℝ ↦ 1 - 2 * x 0 - 2 * t' := by
        funext t'; exact hderiv1 t'
      rw [houter]
      have : HasDerivAt (fun t' : ℝ ↦ 1 - 2 * x 0 - 2 * t') (-2) (0 : ℝ) := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).const_sub (1 - 2 * x 0)
      rw [this.deriv]
    rw [hderiv, hlap]
    norm_num
  · -- `sup` over the closed cylinder is `T + 1/4 > max {T, 1/4} =` sup over `Γ_T`.
    -- Step 0: identify the closed cylinder as `{x | x 0 ∈ [0,1]} ×ˢ [0,T]`.
    have hclos : closure ({x : Heat.E 1 | x 0 ∈ Ioo (0 : ℝ) 1} ×ˢ Ioc 0 T)
        = {x : Heat.E 1 | x 0 ∈ Icc (0 : ℝ) 1} ×ˢ Icc 0 T := by
      rw [closure_prod_eq, closure_Ioc hT.ne]
      congr 1
      set φ : Heat.E 1 ≃ₜ ℝ :=
        (EuclideanSpace.equiv (Fin 1) ℝ).toHomeomorph.trans
          (Homeomorph.funUnique (Fin 1) ℝ) with hφ
      have hcoe : ∀ x : Heat.E 1, φ x = x 0 := fun x ↦ rfl
      have h := φ.preimage_closure (Ioo (0 : ℝ) 1)
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at h
      have hpre_open : φ ⁻¹' Ioo (0 : ℝ) 1
          = {x : Heat.E 1 | x 0 ∈ Ioo (0 : ℝ) 1} := by
        ext x; simp [hcoe]
      have hpre_closed : φ ⁻¹' Icc (0 : ℝ) 1
          = {x : Heat.E 1 | x 0 ∈ Icc (0 : ℝ) 1} := by
        ext x; simp [hcoe]
      rw [← hpre_open, ← hpre_closed, ← h]
    rw [hclos]
    set f : Heat.E 1 × ℝ → ℝ := fun p ↦ p.2 + p.1 0 * (1 - p.1 0) with hf
    set K : Set (Heat.E 1 × ℝ) :=
      {x : Heat.E 1 | x 0 ∈ Icc (0 : ℝ) 1} ×ˢ Icc 0 T with hK
    -- Step 1: `f ≤ T + 1/4` on the closed cylinder (complete the square).
    have hbound : ∀ p ∈ K, f p ≤ T + 1 / 4 := by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      have h1 : x 0 * (1 - x 0) ≤ 1 / 4 := by nlinarith [sq_nonneg (x 0 - 1 / 2)]
      have h2 : t ≤ T := ht.2
      simpa [f] using add_le_add h2 h1
    -- Step 2: the value `T + 1/4` is attained at the top-edge point `(1/2, T)`.
    have hhalf : (EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℝ)) 0 = 1 / 2 := by
      simp
    have hmem_half : ((EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℝ)), T) ∈ K := by
      refine ⟨?_, le_of_lt hT, le_refl T⟩
      simp only [mem_setOf_eq, hhalf]
      norm_num
    have hval_half : f ((EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℝ)), T)
        = T + 1 / 4 := by
      simp only [f, hhalf]; norm_num
    -- Step 3: sup over the closed cylinder equals `T + 1/4`.
    have hLHS : sSup (f '' K) = T + 1 / 4 := by
      apply le_antisymm
      · exact csSup_le ⟨_, ⟨_, hmem_half, rfl⟩⟩ (by rintro y ⟨p, hp, rfl⟩; exact hbound p hp)
      · rw [← hval_half]
        exact le_csSup ⟨T + 1 / 4, by rintro y ⟨p, hp, rfl⟩; exact hbound p hp⟩
          ⟨_, hmem_half, rfl⟩
    -- Step 4: on the parabolic boundary, `f ≤ max T (1/4)`.
    have hbd_bound : ∀ p ∈ K \ ({x : Heat.E 1 | x 0 ∈ Ioo (0 : ℝ) 1} ×ˢ Ioc 0 T),
        f p ≤ max T (1 / 4) := by
      rintro ⟨x, t⟩ ⟨⟨hx, ht⟩, hnot⟩
      simp only [mem_prod, mem_setOf_eq, not_and, mem_Ioo, mem_Ioc] at hnot
      by_cases hxΩ : x 0 ∈ Ioo (0 : ℝ) 1
      · -- interior in space ⇒ the time coordinate must be `0` ⇒ `f = x(1-x) ≤ 1/4`.
        have ht0 : t = 0 := by
          have := hnot hxΩ
          rcases ht with ⟨ht0, htT⟩
          by_contra h0
          exact this (lt_of_le_of_ne ht0 (Ne.symm h0)) htT
        have h1 : x 0 * (1 - x 0) ≤ 1 / 4 := by nlinarith [sq_nonneg (x 0 - 1 / 2)]
        calc f (x, t) = x 0 * (1 - x 0) := by simp [f, ht0]
          _ ≤ 1 / 4 := h1
          _ ≤ max T (1 / 4) := le_max_right _ _
      · -- lateral wall: `x 0 ∈ {0, 1}` ⇒ `x(1-x) = 0` ⇒ `f = t ≤ T`.
        have hx01 : x 0 * (1 - x 0) = 0 := by
          rcases hx with ⟨hx0, hx1⟩
          rcases eq_or_lt_of_le hx0 with h | h
          · rw [← h]; ring
          · rcases eq_or_lt_of_le hx1 with h' | h'
            · rw [h']; ring
            · exact absurd ⟨h, h'⟩ hxΩ
        calc f (x, t) = t := by simp [f, hx01]
          _ ≤ T := ht.2
          _ ≤ max T (1 / 4) := le_max_left _ _
    -- Step 5: the boundary is nonempty (the corner `(0, 0)` lies on it).
    have hcorner : ((0 : Heat.E 1), (0 : ℝ)) ∈
        K \ ({x : Heat.E 1 | x 0 ∈ Ioo (0 : ℝ) 1} ×ˢ Ioc 0 T) := by
      constructor
      · exact ⟨by simp, le_refl 0, le_of_lt hT⟩
      · simp only [mem_prod, mem_setOf_eq, not_and, mem_Ioo, mem_Ioc]
        intro h
        simp at h
    -- Step 6: conclude, since `max T (1/4) < T + 1/4`.
    have hRHS : sSup (f '' (K \ ({x : Heat.E 1 | x 0 ∈ Ioo (0 : ℝ) 1} ×ˢ Ioc 0 T)))
        ≤ max T (1 / 4) := by
      exact csSup_le ⟨_, ⟨_, hcorner, rfl⟩⟩ (by rintro y ⟨p, hp, rfl⟩; exact hbd_bound p hp)
    have hmax : max T (1 / 4) < T + 1 / 4 := max_lt (by linarith) (by linarith)
    rw [hLHS]
    exact ne_of_gt (lt_of_le_of_lt hRHS hmax)

end Problems.Undergraduate.Problem12
