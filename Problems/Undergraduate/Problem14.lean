import Mathlib
import PDE
import PDE.Basics.Heat.HeatKernel

/-!
# Undergraduate Problem 14: Four Properties of the One-Dimensional Heat Kernel

Source: `pde_latex/problems/undergraduate/problem_14.tex` (Math 418, HW-5, Problem 4).

## Informal statement

> Suppose `K(x, t)` is the heat kernel for `x ∈ ℝ` and `t > 0`, that is,
> `K(x, t) = (4πt)^{-1/2} e^{-x²/(4t)}`.
>
> (a) Prove that `∫_ℝ K(x, t) dx = 1` for all `t > 0`.
>
> (b) Prove that `K ∈ C^∞(ℝ × (0, ∞))` (meaning `C^k` for all `k ≥ 0`).
>
> (c) Prove that for any fixed `δ > 0`,
> `max_{δ ≤ |x| < ∞} K(x, t) → 0` as `t → 0`.
>
> (d) Is `K(x, t)` bounded on `ℝ × (0, ∞)`? Justify: if not, prove there is a
> sequence `(xₙ, tₙ)` with `K(xₙ, tₙ) → ∞` (so `K` has no upper bound).

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem14.tex`:

* The problem's kernel is the project's general one-dimensional heat kernel
  `Heat.heatKernel α x t = (1/√(4παt)) · exp(-(x²)/(4αt))`
  (`PDE/Basics/Heat/HeatKernel.lean`, blueprint `def:heatKernel-1d`)
  instantiated at diffusivity `α = 1`; all four theorems below are stated for
  `Heat.heatKernel 1` and follow from the corresponding general lemmas at
  `α > 0` (`Heat.integral_heatKernel_one_gaussian`,
  `Heat.contDiffOn_heatKernel`, `Heat.heatKernel_off_origin_bound` /
  `Heat.heatKernel_off_origin_tendsto_zero`, `Heat.heatKernel_not_bddAbove`).
* Part (b): the source's `C^∞` explicitly means `C^k` for all finite `k`;
  this is `ContDiffOn ℝ ∞` of the joint map `(x, t) ↦ K x t` on the open set
  `{p : ℝ × ℝ | 0 < p.2}` (= `ℝ × (0, ∞)`). The smoothness exponent is `∞`
  (infinite differentiability), NOT `⊤` (which on this toolchain means
  analytic).
* Part (c): the source's maximum over the noncompact region `{δ ≤ |x| < ∞}`
  is stated as the supremum `sSup` of the image of `K(·, t)` on
  `{x : ℝ | δ ≤ |x|}`; it is attained at `x = ±δ` (the even Gaussian profile
  is radially decreasing), so the supremum is a genuine maximum equal to
  `(4πt)^{-1/2} e^{-δ²/(4t)}`. The limit `t → 0⁺` is `𝓝[>] 0`.
* Part (d): the answer is *no*, and the formal statement is the explicit
  justification the source demands for a negative answer: `K` exceeds every
  proposed bound `M` at some point `(0, t)` with `t > 0` — equivalent to the
  source's sequence `(xₙ, tₙ) = (0, 1/n)` with `K(xₙ, tₙ) → ∞`.
-/

open Filter Set
open scoped Topology ContDiff

namespace Problems.Undergraduate.Problem14

/-- **Problem 14 (a): the heat kernel has unit mass** (blueprint
`thm:problem14-integral-one`).

For every `t > 0`, `∫_ℝ K(x, t) dx = 1`, where `K = Heat.heatKernel 1` is the
one-dimensional heat kernel at diffusivity `α = 1`. Thin instantiation of the
general normalization `Heat.integral_heatKernel_one_gaussian`; the content is
the substitution `y = x/(2√t)` reducing to the classical Gaussian integral. -/
theorem integral_one {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, Heat.heatKernel 1 x t = 1 :=
  Heat.integral_heatKernel_one_gaussian 1 t one_pos ht

/-- **Problem 14 (b): the heat kernel is jointly smooth** (blueprint
`thm:problem14-smooth`).

The joint map `(x, t) ↦ K(x, t)` at diffusivity `α = 1` is `C^∞` (i.e. `C^k`
for every finite `k`) on the open set `ℝ × (0, ∞)`, spelled
`{p : ℝ × ℝ | 0 < p.2}`. Thin instantiation of the general joint smoothness
`Heat.contDiffOn_heatKernel` (blueprint `lem:heatKernel-contDiff`); the content
is the source's product argument — prefactor, rational exponent, and `exp` are
each smooth where `t > 0`. -/
theorem smooth :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ Heat.heatKernel 1 p.1 p.2)
      {p : ℝ × ℝ | 0 < p.2} :=
  Heat.contDiffOn_heatKernel one_pos

/-- **Problem 14 (c): uniform decay off the origin as `t → 0⁺`** (blueprint
`thm:problem14-decay`).

For fixed `δ > 0`, the supremum of `K(·, t)` over `{x : δ ≤ |x|}` tends to `0`
as `t → 0⁺`. The supremum is attained at `x = ±δ` and equals
`(4πt)^{-1/2} e^{-δ²/(4t)}`, so this is the source's maximum. Proof: for each
`t > 0` the image supremum collapses to `K(δ, t)` via
`Heat.heatKernel_off_origin_bound` (`IsGreatest.csSup_eq`, witness `x = δ`),
then `Heat.heatKernel_off_origin_tendsto_zero` (exponential beats polynomial
under the substitution `s = 1/t`) gives the limit. -/
theorem decay_off_origin {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t ↦ sSup ((fun x ↦ Heat.heatKernel 1 x t) '' {x : ℝ | δ ≤ |x|}))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine Tendsto.congr' ?_ (Heat.heatKernel_off_origin_tendsto_zero one_pos hδ)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0:ℝ) < t := ht
  have hgr : IsGreatest ((fun x ↦ Heat.heatKernel 1 x t) '' {x : ℝ | δ ≤ |x|})
      (Heat.heatKernel 1 δ t) := by
    constructor
    · exact ⟨δ, le_abs_self δ, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      exact Heat.heatKernel_off_origin_bound one_pos ht' hδ hx
  exact hgr.csSup_eq.symm

/-- **Problem 14 (d): the heat kernel is unbounded** (blueprint
`thm:problem14-unbounded`).

`K` is *not* bounded on `ℝ × (0, ∞)`: for every `M : ℝ` there is `t > 0` with
`M < K(0, t)`. This is the explicit justification of the negative answer —
`K(0, t) = (4πt)^{-1/2} → ∞` along `t → 0⁺` (the source's sequence
`(xₙ, tₙ) = (0, 1/n)`). Thin instantiation of the general unboundedness
`Heat.heatKernel_not_bddAbove` (blueprint `lem:heatKernel-unbounded`); the
content is the explicit witness `t` small enough that `1/√(4πt) > M`. -/
theorem not_bounded :
    ∀ M : ℝ, ∃ t : ℝ, 0 < t ∧ M < Heat.heatKernel 1 0 t :=
  Heat.heatKernel_not_bddAbove one_pos

end Problems.Undergraduate.Problem14
