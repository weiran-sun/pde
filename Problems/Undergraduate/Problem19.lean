import Mathlib
import PDE.Background.CalculusMeasureTheory.DivergenceTheorem.GeneralizedDivergence

/-!
# Undergraduate Problem 19: Green's Second Identity from Green's First Identity

Source: `pde_latex/problems/undergraduate/problem_19.tex` (Math 418, HW-8, Problem 2).

## Informal statement

> Use Green's first identity to prove Green's second identity: suppose
> `Ω ⊆ ℝⁿ` is open and bounded with a `C¹` boundary. Suppose
> `u, v ∈ C²(Ω) ∩ C(closure Ω)` and `∇u, ∇v ∈ C(closure Ω)`. Then
>
> `∫_Ω (u Δv − v Δu) dx = ∫_{∂Ω} (u ∇v·n − v ∇u·n) dS`,
>
> where `n` is the outward normal to `∂Ω`.

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem19.tex`:

* The ambient space `ℝⁿ` with `n = m + 1 ≥ 2` is
  `GeneralizedDivergenceStandalone.EN m = WithLp 2 (EuclideanSpace ℝ (Fin m) × ℝ)`,
  the ℓ²-product presentation used throughout the divergence-theorem
  development; the dimension hypothesis `n ≥ 2` is `hm : 0 < m`.
* "Open and bounded with a `C¹` boundary" is `IsOpen Ω`,
  `Bornology.IsBounded Ω`, and `GeneralizedDivergenceStandalone.HasC1Boundary Ω`
  (a `C¹` cylinder chart at every boundary point).
* The surface measure `dS` on `∂Ω = frontier Ω` is the codimension-one
  Euclidean Hausdorff measure `μHE[m]`; the outward normal `n` is a field
  `ν` with `GeneralizedDivergenceStandalone.IsOutwardNormal Ω ν`.
* `Δ` is `GeneralizedDivergenceStandalone.laplacian` (divergence of the
  gradient field, blueprint `def:gd-laplacian`) and `∇` is Mathlib's
  `gradient`; the normal derivative `∂v/∂n` is `⟪gradient v x, ν x⟫`.
* **Regularity deviation (documented in the blueprint chapter):** the source
  assumes `u, v ∈ C²(Ω) ∩ C(closure Ω)` with `∇u, ∇v ∈ C(closure Ω)` —
  interior `C²` plus continuity of the functions and gradients up to the
  closure. The formalization instead assumes `u, v` are `C²` on an open
  neighborhood `O ⊇ closure Ω`: this is the regularity under which the
  library's divergence theorem, and hence Green's first identity
  (`thm:gd-green-first`), is established, and it implies the source's
  hypotheses. The derivation itself is unchanged.
* **The derivation IS the content**: the proof below does NOT invoke the
  library's `green_second_identity`; it re-runs the subtraction argument
  from `green_first_identity` — two instances (for the pairs `(u,v)` and
  `(v,u)`), integrability of both Green-I integrands via
  `integrableOn_of_continuousOn`, cancellation of the Dirichlet terms by
  `real_inner_comm`, and `integral_sub` — exactly the informal solution.
-/

open MeasureTheory Set Bornology
open scoped RealInnerProductSpace ENNReal Topology
open GeneralizedDivergenceStandalone

namespace Problems.Undergraduate.Problem19

/-- **Problem 19: Green's second identity** (blueprint
`thm:problem19-greens-second`).

Let `n = m + 1 ≥ 2`, let `Ω ⊆ ℝⁿ` be open and bounded with `C¹` boundary,
let `O ⊇ closure Ω` be open, let `u, v` be `C²` on `O`, and let `ν` be an
outward normal field on `∂Ω`. Then

`∫_Ω (u Δv − v Δu) = ∫_{∂Ω} u ⟪∇v, ν⟫ dμHE[m] − ∫_{∂Ω} v ⟪∇u, ν⟫ dμHE[m]`.

Derived from Green's first identity
(`GeneralizedDivergenceStandalone.green_first_identity`) by the subtraction
argument of the source: apply Green-I to `(u, v)` and to `(v, u)`, note the
Dirichlet terms `⟪∇u, ∇v⟫` and `⟪∇v, ∇u⟫` agree by symmetry of the real
inner product, and split the volume integral of the difference using the
integrability of each Green-I integrand (continuous on `O`, hence
integrable on the bounded `Ω`). -/
theorem greens_second_identity {m : ℕ} (hm : 0 < m) {Ω : Set (EN m)}
    (hΩ : IsOpen Ω) (hb : IsBounded Ω) (hC1 : HasC1Boundary Ω)
    {O : Set (EN m)} (hO : IsOpen O) (hΩO : closure Ω ⊆ O)
    {u v : EN m → ℝ} (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    {ν : EN m → EN m} (hν : IsOutwardNormal Ω ν) :
    ∫ x in Ω, (u x * laplacian v x - v x * laplacian u x)
      = (∫ x in frontier Ω, u x * ⟪gradient v x, ν x⟫ ∂μHE[m])
        - ∫ x in frontier Ω, v x * ⟪gradient u x, ν x⟫ ∂μHE[m] := by
  -- `C²` on `O` supplies the `C¹` regularity Green-I asks of its first slot.
  have hu1 : ContDiffOn ℝ 1 u O := hu.of_le (by norm_num)
  have hv1 : ContDiffOn ℝ 1 v O := hv.of_le (by norm_num)
  -- Green's first identity for the pair (u, v):
  --   ∫_Ω (u Δv + ⟪∇u, ∇v⟫) = ∫_{∂Ω} u ⟪∇v, ν⟫.
  have hG1 := green_first_identity hm hΩ hb hC1 hO hΩO hu1 hv hν
  -- Green's first identity for the pair (v, u):
  --   ∫_Ω (v Δu + ⟪∇v, ∇u⟫) = ∫_{∂Ω} v ⟪∇u, ν⟫.
  have hG2 := green_first_identity hm hΩ hb hC1 hO hΩO hv1 hu hν
  -- Each Green-I integrand is continuous on `O` (the gradients are `C¹`
  -- and the Laplacians are divergences of `C¹` fields), hence integrable
  -- on the bounded `Ω` — this is what lets the difference split.
  have hlap_u : ContinuousOn (laplacian u) O :=
    continuousOn_div hO (contDiffOn_gradient hO hu)
  have hlap_v : ContinuousOn (laplacian v) O :=
    continuousOn_div hO (contDiffOn_gradient hO hv)
  have hgradu : ContinuousOn (fun y => gradient u y) O :=
    (contDiffOn_gradient hO hu).continuousOn
  have hgradv : ContinuousOn (fun y => gradient v y) O :=
    (contDiffOn_gradient hO hv).continuousOn
  have hint1 : IntegrableOn
      (fun x => u x * laplacian v x + ⟪gradient u x, gradient v x⟫) Ω volume :=
    integrableOn_of_continuousOn hb hΩO
      ((hu1.continuousOn.mul hlap_v).add (hgradu.inner hgradv))
  have hint2 : IntegrableOn
      (fun x => v x * laplacian u x + ⟪gradient v x, gradient u x⟫) Ω volume :=
    integrableOn_of_continuousOn hb hΩO
      ((hv1.continuousOn.mul hlap_u).add (hgradv.inner hgradu))
  calc ∫ x in Ω, (u x * laplacian v x - v x * laplacian u x)
      -- The Dirichlet terms cancel pointwise: ⟪∇v, ∇u⟫ = ⟪∇u, ∇v⟫.
      = ∫ x in Ω, ((u x * laplacian v x + ⟪gradient u x, gradient v x⟫)
          - (v x * laplacian u x + ⟪gradient v x, gradient u x⟫)) := by
        refine setIntegral_congr_fun hΩ.measurableSet fun x _ => ?_
        rw [real_inner_comm (gradient v x) (gradient u x)]
        ring
    _ = (∫ x in Ω, (u x * laplacian v x + ⟪gradient u x, gradient v x⟫))
          - ∫ x in Ω, (v x * laplacian u x + ⟪gradient v x, gradient u x⟫) :=
        integral_sub hint1 hint2
    _ = (∫ x in frontier Ω, u x * ⟪gradient v x, ν x⟫ ∂μHE[m])
          - ∫ x in frontier Ω, v x * ⟪gradient u x, ν x⟫ ∂μHE[m] := by
        rw [hG1, hG2]

end Problems.Undergraduate.Problem19
