import Mathlib
import PDE
import PDE.Basics.Heat.HeatKernelND
import PDE.Basics.Heat.HeatMaximumPrincipleND

/-!
# Undergraduate Problem 11: The Weak Minimum Principle for the Multi-Dimensional Heat Equation

Source: `pde_latex/problems/undergraduate/problem_11.tex` (Math 418, HW-5, Problem 1).

## Informal statement

> Let `Ω ⊆ ℝⁿ` be an open and bounded set and `T > 0` a fixed number. Define the
> parabolic cylinder `Ω_T = Ω × (0, T]` and the parabolic boundary
> `Γ_T = closure(Ω_T) \ Ω_T`. Here `closure(U)` denotes the closure of a set `U`,
> and `C²₁(Ω_T)` denotes the space of functions on `Ω_T` that are twice
> continuously differentiable in `x` and once continuously differentiable in `t`.
>
> Prove the multi-dimensional weak minimum principle for the heat equation over
> bounded domains: suppose `u ∈ C²₁(Ω_T) ∩ C(closure(Ω_T))` satisfies the heat
> equation `u_t = Δu` in `Ω_T`. Then
> ```
>   min_{closure(Ω_T)} u(x, t) = min_{Γ_T} u(x, t).
> ```
> You need to explain why the two terms in the identity above are well-defined.

## Semantic alignment

* The parabolic cylinder `Ω_T = Ω × (0, T]` is `Ω ×ˢ Set.Ioc 0 T ⊆ E n × ℝ`, and
  the parabolic boundary `Γ_T = closure(Ω_T) \ Ω_T` is spelled out verbatim as
  `closure (Ω ×ˢ Set.Ioc 0 T) \ (Ω ×ˢ Set.Ioc 0 T)`. (These are stated inline
  rather than through named definitions: the named `Heat.parabolicCylinder` /
  `Heat.parabolicBoundary` of the generalized maximum-principle chapter are
  being introduced concurrently in `PDE/Basics/Heat/HeatMaximumPrincipleND.lean`;
  once they land, the statement below can be rewritten to use them — the sets are
  definitionally the same.)
* "Twice continuously differentiable in `x`, once in `t`, one-sided at `t = T`"
  is formalized, following the project convention of the heat maximum-principle
  chapter, as joint `ContDiffOn ℝ 2` on the parabolic cylinder `Ω ×ˢ Ioc 0 T`
  (within-set differentiability, so the time derivative at the top edge is the
  one-sided one).
* The heat equation `u_t = Δu` on `Ω_T`: the time derivative is
  `derivWithin (fun t' ↦ u x t') (Set.Iic T) t` — for `0 < t < T` the set
  `Iic T` is a neighbourhood of `t` so this is the ordinary two-sided derivative,
  and at `t = T` it is the one-sided derivative from below, exactly as the
  problem prescribes. The Laplacian is the project's n-dimensional
  `Heat.laplacian` (trace of the derivative of the gradient), genuine
  (two-sided) in `x` since `Ω` is open. The diffusivity is `α = 1` as in the
  source.
* "The two terms are well-defined": `closure(Ω_T)` and `Γ_T` are nonempty compact
  sets and `u` is continuous on `closure(Ω_T)`, so the images are nonempty
  compact subsets of `ℝ` whose infima are attained; in the formal statement each
  side is `sInf` of the image of `u` on the indicated set, per the blueprint
  chapter `Problems_Undergraduate_Problem11.tex`.
* `Ω.Nonempty` is assumed so that the minima are genuinely attained (the
  blueprint's well-definedness discussion; with `Ω = ∅` both sides would be
  `sInf ∅` and the identity would be vacuous).
* The informal problem asks for a from-scratch proof (the course had no
  multi-dimensional maximum version yet); per the blueprint's semantic-alignment
  note, the formal deliverable is the true statement, to be proved from the
  generalized minimum-principle corollary `Heat.heat_equation_min_principle`
  (blueprint `cor:heat-min-principle`) at `α = 1` once the Heat lane lands it.
-/

open Set Bornology

namespace Problems.Undergraduate.Problem11

/-- **Problem 11: weak minimum principle for the heat equation** (blueprint
`thm:problem11-min-principle`).

Let `n ≥ 1`, let `Ω ⊆ ℝⁿ` be open, bounded and nonempty, and let `T > 0`. Write
`Ω_T = Ω ×ˢ Ioc 0 T` for the parabolic cylinder and
`Γ_T = closure Ω_T \ Ω_T` for the parabolic boundary. If
`u : ℝⁿ → ℝ → ℝ` is continuous on `closure Ω_T`, is `C²₁` on `Ω_T`, and
satisfies the heat equation `∂ₜ u = Δu` on `Ω_T` (one-sided time derivative at
the top edge `t = T`), then the infimum of `u` over `closure Ω_T` equals its
infimum over `Γ_T` — both attained, so they are genuine minima. -/
theorem min_principle
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
        = Heat.laplacian (fun x' ↦ u x' t) x) :
    sInf ((fun p : Heat.E n × ℝ ↦ u p.1 p.2) '' closure (Ω ×ˢ Ioc 0 T))
      = sInf ((fun p : Heat.E n × ℝ ↦ u p.1 p.2) ''
          (closure (Ω ×ˢ Ioc 0 T) \ (Ω ×ˢ Ioc 0 T))) := by
  exact Heat.heat_equation_min_principle hn hΩ_open hΩ_bdd hΩ_ne hT one_pos u
    h_cont h_smooth
    (fun x t hxt ↦ by rw [one_mul]; exact ge_of_eq (h_pde x t hxt))

end Problems.Undergraduate.Problem11
