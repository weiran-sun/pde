/-
# Bridging the project Laplacians to Mathlib's `Δ`

Blueprint chapter: `blueprint/src/chapters/PDE_Basics_LaplacianBridge.tex`.

The project carries three Laplacian definitions, all of the form "trace of
the Fréchet derivative of the gradient" (or its basis-sum expansion):

* `Heat.laplacian` (trace form, on `EuclideanSpace ℝ (Fin n)`), with a
  `Within` variant;
* `GeneralizedDivergenceStandalone.laplacian` (orthonormal-basis-sum form,
  on `EN m = WithLp 2 (EuclideanSpace ℝ (Fin m) × ℝ)`);
* the root-namespace `laplacian` (trace form fixed at `E = EuclideanSpace ℝ
  (Fin 3)`, defined in `PDE/Basics/Laplace/CalculusBasic.lean` — the copy
  consumed by `IsHarmonic` and the 3-D Laplace development).

Mathlib's `Δ` (`Mathlib/Analysis/InnerProductSpace/Laplacian.lean`) is the
second iterated derivative applied to the canonical covariant tensor.  This
file records the bridge lemmas identifying the project Laplacians with `Δ`,
so new developments can be stated in Mathlib's API (and consume its
`Harmonic/` shelf).  The two global identifications are *unconditional*: a
non-differentiable map has `fderiv = 0`, and both sides are images of the
same (possibly zero) total-derivative object.  The within-set form needs
`UniqueDiffOn ℝ s` and `x ∈ s` (forced by `comp_fderivWithin`).
-/
import PDE.Basics.Heat.HeatKernelND
import PDE.Basics.Laplace.CalculusBasic
import PDE.Background.CalculusMeasureTheory.DivergenceTheorem.GeneralizedDivergence
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Trace

open InnerProductSpace Laplacian
open scoped RealInnerProductSpace

open Heat

namespace Basics

/-- **Trace form equals Mathlib's Laplacian** (`lem:laplacian-bridge-nd`).
For every `u : ℝⁿ → ℝ` and every `x`, unconditionally,
`tr (D(∇u)(x)) = Δ u x`. -/
lemma laplacian_eq_mathlib {n : ℕ} (u : Heat.E n → ℝ) (x : Heat.E n) :
    Heat.laplacian u x = Δ u x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis u]
  unfold Heat.laplacian Heat.div_field
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (Heat.E n))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  have hgrad : gradient u =
      ⇑(toDual ℝ (Heat.E n)).symm ∘ fderiv ℝ u := rfl
  rw [hgrad, LinearIsometryEquiv.comp_fderiv]
  rw [real_inner_comm]
  exact toDual_symm_apply

/-- **Within-form bridge** (`lem:laplacian-bridge-within`).  On a set `s`
with unique derivatives, at `x ∈ s`,
`tr (D_s(∇_s u)(x)) = Δ[s] u x`. -/
lemma laplacianWithin_eq_mathlib {n : ℕ} (u : Heat.E n → ℝ) {s : Set (Heat.E n)}
    (hs : UniqueDiffOn ℝ s) {x : Heat.E n} (hx : x ∈ s) :
    Heat.laplacianWithin u s x = (Δ[s] u) x := by
  rw [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis u hs hx]
  unfold Heat.laplacianWithin Heat.div_fieldWithin
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (Heat.E n))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDerivWithin_two_apply u hs hx]
  have hgrad : gradientWithin u s =
      ⇑(toDual ℝ (Heat.E n)).symm ∘ fderivWithin ℝ u s := rfl
  rw [hgrad, LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
  rw [real_inner_comm]
  exact toDual_symm_apply

namespace GeneralizedDivergenceStandalone

/-- **Basis-sum form equals Mathlib's Laplacian** (`lem:laplacian-bridge-gds`).
For every `u : ℝᵐ⁺¹ → ℝ` (product model `ℝᵐ × ℝ` with the `ℓ²` norm) and
every `x`, unconditionally,
`Σᵢ ⟪D(∇u)(x) eᵢ, eᵢ⟫ = Δ u x`. -/
lemma laplacian_eq_mathlib {m : ℕ}
    (u : _root_.GeneralizedDivergenceStandalone.EN m → ℝ)
    (x : _root_.GeneralizedDivergenceStandalone.EN m) :
    _root_.GeneralizedDivergenceStandalone.laplacian u x = Δ u x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis u]
  unfold _root_.GeneralizedDivergenceStandalone.laplacian
    _root_.GeneralizedDivergenceStandalone.div
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  have hgrad : (fun y => gradient u y) =
      ⇑(toDual ℝ (_root_.GeneralizedDivergenceStandalone.EN m)).symm ∘ fderiv ℝ u := rfl
  rw [hgrad, LinearIsometryEquiv.comp_fderiv]
  exact toDual_symm_apply

end GeneralizedDivergenceStandalone

/-- **Fixed three-dimensional trace form equals Mathlib's Laplacian**
(`lem:laplacian-bridge-root`).  For every `u : ℝ³ → ℝ` and every `x`,
unconditionally, `tr (D(∇u)(x)) = Δ u x`, where the left side is the
root-namespace `laplacian` — the project's fixed 3-D trace form. -/
/- Planner strategy: the root-namespace `laplacian`/`div_field`
(`PDE/Basics/Laplace/CalculusBasic.lean:29`, `:20`) are term-for-term
`Heat.laplacian`/`Heat.div_field` instantiated at `n = 3` on
`E = EuclideanSpace ℝ (Fin 3)` (`PDEDomains.lean:12`).  Try
`exact Basics.laplacian_eq_mathlib u x` behind an
`unfold laplacian div_field` (and/or a `show` recasting the goal into the
`Heat` spelling) — the two trace-of-derivative expressions should be
definitionally equal.  NB: the `_root_.` qualifier is required — `open
InnerProductSpace` (for `Δ`) also exports Mathlib's `laplacian`, making the
bare name ambiguous in this file. -/
lemma laplacian3d_eq_mathlib (u : E → ℝ) (x : E) :
    _root_.laplacian u x = Δ u x :=
  Basics.laplacian_eq_mathlib u x

end Basics
