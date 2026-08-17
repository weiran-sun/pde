/-
# THE DIVERGENCE THEOREM IN R^3 -- the complete development in one file

EVERY THEOREM IS FULLY PROVEN -- no sorries, no axioms beyond Mathlib.
The ambient geometry (E2, E3, graphMap, jac) and the area formula for
C1 graphs are imported from the companion GraphArea project.

Headline results:
* `divergence_theorem` : for Omega in R^3 open bounded with C1
    boundary, u in C1(O) with O an open neighborhood of the closure,
    nu any outward unit normal field, and any direction w:
      integral over Omega of Du.w  =
      integral over the frontier of u <nu, w>  (against mu_HE[2]);
* `divergence_theorem_vector_field` : the classical flux form,
      integral of div F = boundary integral of <F, nu>;
* `isOutwardNormalAt_chart` / `IsOutwardNormalAt.eq_chart_normal` :
    existence and uniqueness of the geometric outward unit normal.
-/
import PDE.Background.CalculusMeasureTheory.GraphHausdorffMeasure.R3GraphMeasure
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section

open MeasureTheory Set GraphAreaFull Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology Manifold

namespace DivergenceFull

/-
# Divergence theorem — setup (paper §2, "Understanding the theorem")

Ambient space and graph vocabulary are inherited from the completed
GraphArea project (`E2 = ℝ²`, `E3 = ℝ² ×₂ ℝ` with the ℓ²-product norm,
`graphMap`, `graph`, `jac`).  This file adds the divergence-specific
vocabulary from `V2DivergenceProof.tex`:

* `horiz`/`vert` — the coordinate split `x = (x', x₃)`;
* `subgraphSet`, `cylinder` — the strict subgraph `{x₃ < g x'}` and the
  graph cylinder `{|x'| < r, |x₃ - g x'| < ht}` (paper proof step 2);
* `CylinderChart` — a local boundary description: after the rigid motion
  `T`, inside the cylinder, `Ω` is the strict subgraph of `g` and `∂Ω`
  is the graph (the paper's three displayed implications);
* `HasC1Boundary` — "Ω̄ has C¹ boundary" (paper's meaning of the
  hypothesis, made precise in proof step 2);
* `unitNormal` — the outward unit normal `(-∇g, 1)/√(1+|∇g|²)` of a
  graph (paper §2.2), and the predicate `IsOutwardNormal` for a normal
  field on `∂Ω`.

The outward normal is *characterized geometrically* (unit length,
orthogonal to the tangent cone of `∂Ω`, exits `Ω̄` forward and enters
`Ω` backward — paper §2.2's "perpendicular to the surface" and
"checking it points outward").  The two key facts proven here:

* `isOutwardNormalAt_chart` — the graph normal of any chart satisfies
  the characterization;
* `IsOutwardNormalAt.eq_chart_normal` — the characterization pins the
  vector down uniquely, so any outward normal field agrees with every
  chart's graph normal on the chart's patch.

Design note: we work concretely in ℝ³ (`n = 3`) to reuse GraphArea
verbatim; the paper is written for general `n`.
-/




/-! ### Coordinates -/

/-- Horizontal part `x'` of `x = (x', x₃) ∈ ℝ³`. -/
def horiz (x : E3) : E2 := (WithLp.ofLp x).1

/-- Vertical part `x₃` of `x = (x', x₃) ∈ ℝ³`. -/
def vert (x : E3) : ℝ := (WithLp.ofLp x).2

@[simp] lemma horiz_toLp (z : E2) (a : ℝ) : horiz (WithLp.toLp 2 (z, a)) = z := rfl

@[simp] lemma vert_toLp (z : E2) (a : ℝ) : vert (WithLp.toLp 2 (z, a)) = a := rfl

@[simp] lemma horiz_graphMap (g : E2 → ℝ) (z : E2) : horiz (graphMap g z) = z := rfl

@[simp] lemma vert_graphMap (g : E2 → ℝ) (z : E2) : vert (graphMap g z) = g z := rfl

@[simp] lemma toLp_horiz_vert (x : E3) : WithLp.toLp 2 (horiz x, vert x) = x := rfl

@[simp] lemma horiz_add (x y : E3) : horiz (x + y) = horiz x + horiz y := rfl

@[simp] lemma vert_add (x y : E3) : vert (x + y) = vert x + vert y := rfl

@[simp] lemma horiz_sub (x y : E3) : horiz (x - y) = horiz x - horiz y := rfl

@[simp] lemma vert_sub (x y : E3) : vert (x - y) = vert x - vert y := rfl

@[simp] lemma horiz_smul (t : ℝ) (x : E3) : horiz (t • x) = t • horiz x := rfl

@[simp] lemma vert_smul (t : ℝ) (x : E3) : vert (t • x) = t * vert x := rfl

@[simp] lemma horiz_neg (x : E3) : horiz (-x) = -horiz x := rfl

@[simp] lemma vert_neg (x : E3) : vert (-x) = -vert x := rfl

/-- Extensionality for `E3` in the `horiz`/`vert` coordinates. -/
lemma E3_ext {x y : E3} (h1 : horiz x = horiz y) (h2 : vert x = vert y) :
    x = y := by
  have h : WithLp.ofLp x = WithLp.ofLp y := Prod.ext h1 h2
  exact congrArg (WithLp.toLp 2) h

lemma continuous_horiz : Continuous horiz :=
  continuous_fst.comp (WithLp.prod_continuous_ofLp 2 E2 ℝ)

lemma continuous_vert : Continuous vert :=
  continuous_snd.comp (WithLp.prod_continuous_ofLp 2 E2 ℝ)

lemma continuous_graphMap {g : E2 → ℝ} (hg : Continuous g) :
    Continuous (graphMap g) :=
  (WithLp.prod_continuous_toLp 2 E2 ℝ).comp (continuous_id.prodMk hg)

/-- Pythagoras in the `horiz`/`vert` coordinates (GraphArea's
`norm_toLp_sq` re-read through the projections). -/
lemma norm_sq_eq (x : E3) : ‖x‖ ^ 2 = ‖horiz x‖ ^ 2 + (vert x) ^ 2 := by
  conv_lhs => rw [← toLp_horiz_vert x]
  exact norm_toLp_sq _ _

/-- The real inner product in the `horiz`/`vert` coordinates. -/
lemma inner_eq (x y : E3) :
    ⟪x, y⟫ = ⟪horiz x, horiz y⟫ + vert x * vert y := by
  rw [WithLp.prod_inner_apply (𝕜 := ℝ) x y]
  congr 1
  exact mul_comm _ _

/-! ### Subgraphs and cylinders (paper proof step 2) -/

/-- The strict subgraph `Σ_g = {x : x₃ < g x'}` — the region strictly
below the graph of `g`. -/
def subgraphSet (g : E2 → ℝ) : Set E3 := {x | vert x < g (horiz x)}

/-- The open graph cylinder `{x : |x'| < r and |x₃ - g x'| < ht}`
(the paper's neighborhood `U` from proof step 2, before the rigid
motion). -/
def cylinder (g : E2 → ℝ) (r ht : ℝ) : Set E3 :=
  {x | ‖horiz x‖ < r ∧ |vert x - g (horiz x)| < ht}

lemma isOpen_subgraphSet {g : E2 → ℝ} (hg : Continuous g) :
    IsOpen (subgraphSet g) :=
  isOpen_lt continuous_vert (hg.comp continuous_horiz)

lemma isOpen_cylinder {g : E2 → ℝ} (hg : Continuous g) (r ht : ℝ) :
    IsOpen (cylinder g r ht) := by
  have h1 : IsOpen {x : E3 | ‖horiz x‖ < r} :=
    isOpen_lt (continuous_norm.comp continuous_horiz) continuous_const
  have h2 : IsOpen {x : E3 | |vert x - g (horiz x)| < ht} :=
    isOpen_lt (continuous_vert.sub (hg.comp continuous_horiz)).abs continuous_const
  exact h1.inter h2

lemma graphMap_mem_cylinder {g : E2 → ℝ} {r ht : ℝ} (hht : 0 < ht) {z : E2}
    (hz : z ∈ Metric.ball (0 : E2) r) :
    graphMap g z ∈ cylinder g r ht := by
  refine ⟨by simpa [mem_ball_zero_iff] using hz, by simpa using hht⟩

/-- The graph piece inside a cylinder is the graph over the disk:
`{x ∈ cylinder : x₃ = g x'} = Φ_g '' B(0, r)` (for `0 < ht`). -/
lemma cylinder_inter_graph {g : E2 → ℝ} {r ht : ℝ} (hht : 0 < ht) :
    cylinder g r ht ∩ {x | vert x = g (horiz x)}
      = graph g (Metric.ball (0 : E2) r) := by
  ext x
  constructor
  · rintro ⟨⟨hr, -⟩, hx⟩
    refine ⟨horiz x, by simpa [mem_ball_zero_iff] using hr, ?_⟩
    show WithLp.toLp 2 (horiz x, g (horiz x)) = x
    rw [← hx]
    exact toLp_horiz_vert x
  · rintro ⟨z, hz, rfl⟩
    exact ⟨graphMap_mem_cylinder hht hz, by simp⟩

/-! ### C¹ boundary charts (paper proof step 2) -/

/-- A cylinder chart for `Ω`: a rigid motion `T` and a globally-C¹
function `g` such that, inside the cylinder of radius `r` and height
`ht` around the graph, the three displayed implications of the paper's
proof step 2 hold — on the graph lies `∂Ω`, strictly below lies `Ω`,
strictly above lies the complement of `Ω`.

The chart's neighborhood in space is `c.U = T '' cylinder`. -/
structure CylinderChart (Ω : Set E3) where
  /-- The rigid motion (rotation + translation + possibly a reflection). -/
  T : E3 ≃ᵃⁱ[ℝ] E3
  /-- The boundary is locally the graph of `g`. -/
  g : E2 → ℝ
  /-- Radius of the cylinder. -/
  r : ℝ
  /-- Half-height of the cylinder. -/
  ht : ℝ
  hr : 0 < r
  hht : 0 < ht
  /-- `g` is C¹ on all of ℝ² (the paper's `g : ℝ^{n-1} → ℝ` C¹). -/
  hg : ContDiff ℝ 1 g
  /-- `x₃ = g x'  ⟹  T x ∈ ∂Ω` inside the cylinder. -/
  mem_frontier : ∀ x ∈ cylinder g r ht, vert x = g (horiz x) → T x ∈ frontier Ω
  /-- `x₃ < g x'  ⟹  T x ∈ Ω` inside the cylinder. -/
  mem_inside : ∀ x ∈ cylinder g r ht, vert x < g (horiz x) → T x ∈ Ω
  /-- `x₃ > g x'  ⟹  T x ∉ Ω` inside the cylinder. -/
  mem_outside : ∀ x ∈ cylinder g r ht, g (horiz x) < vert x → T x ∉ Ω

variable {Ω : Set E3}

namespace CylinderChart

/-- The chart's neighborhood in space: the image of the cylinder under
the rigid motion. -/
def U (c : CylinderChart Ω) : Set E3 := c.T '' cylinder c.g c.r c.ht

lemma isOpen_U (c : CylinderChart Ω) : IsOpen c.U :=
  c.T.toHomeomorph.isOpen_image.mpr (isOpen_cylinder c.hg.continuous _ _)

/-- The rigid motion applied to a translated point:
`T(p + w) = T p + T₀ w`. -/
lemma map_add (c : CylinderChart Ω) (p w : E3) :
    c.T (p + w) = c.T p + c.T.linearIsometryEquiv w := by
  simpa [add_comm] using c.T.map_vadd p w

lemma map_sub (c : CylinderChart Ω) (p w : E3) :
    c.T (p - w) = c.T p - c.T.linearIsometryEquiv w := by
  rw [sub_eq_add_neg, sub_eq_add_neg, c.map_add p (-w), map_neg]

/-- The open upper region of a chart's cylinder is disjoint from the
closure of `Ω` (strengthens `mem_outside` from `Ω` to `Ω̄`, which is
what the frontier computation and the ray lemmas need). -/
lemma image_upper_disjoint_closure (c : CylinderChart Ω) :
    Disjoint (c.T '' (cylinder c.g c.r c.ht ∩ {x | c.g (horiz x) < vert x}))
      (closure Ω) := by
  set W := cylinder c.g c.r c.ht ∩ {x : E3 | c.g (horiz x) < vert x} with hW
  have hWopen : IsOpen W :=
    (isOpen_cylinder c.hg.continuous _ _).inter
      (isOpen_lt (c.hg.continuous.comp continuous_horiz) continuous_vert)
  have hTW : IsOpen (c.T '' W) := c.T.toHomeomorph.isOpen_image.mpr hWopen
  have hsub : Ω ⊆ (c.T '' W)ᶜ := by
    intro w hw
    rintro ⟨y, ⟨hyc, hyg⟩, rfl⟩
    exact c.mem_outside y hyc hyg hw
  have hcl : closure Ω ⊆ (c.T '' W)ᶜ :=
    closure_minimal hsub hTW.isClosed_compl
  exact Set.disjoint_left.mpr fun x hx hx' => hcl hx' hx

/-- Inside the chart, the boundary is exactly the (moved) graph over the
disk: `∂Ω ∩ c.U = T '' (Φ_g '' B(0, r))`.  The paper states only the
`⟸` implications; `⟹` follows because the three cases partition the
cylinder while `Ω`, `∂Ω`, exterior partition space (`Ω` open). -/
lemma frontier_inter_U (hΩ : IsOpen Ω) (c : CylinderChart Ω) :
    frontier Ω ∩ c.U = c.T '' graph c.g (Metric.ball (0 : E2) c.r) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxf, y, hy, rfl⟩
    rcases lt_trichotomy (vert y) (c.g (horiz y)) with h | h | h
    · exact absurd (c.mem_inside y hy h) (hΩ.frontier_eq ▸ hxf).2
    · rw [← cylinder_inter_graph c.hht]
      exact ⟨y, ⟨hy, h⟩, rfl⟩
    · exact absurd (frontier_subset_closure hxf)
        (Set.disjoint_left.mp c.image_upper_disjoint_closure ⟨y, ⟨hy, h⟩, rfl⟩)
  · rintro x ⟨y, hy, rfl⟩
    rw [← cylinder_inter_graph c.hht] at hy
    exact ⟨c.mem_frontier y hy.1 hy.2, Set.mem_image_of_mem _ hy.1⟩

/-- Inside the chart, `Ω` is exactly the (moved) strict subgraph part of
the cylinder: `Ω ∩ c.U = T '' (Σ_g ∩ cylinder)`. -/
lemma inter_U (hΩ : IsOpen Ω) (c : CylinderChart Ω) :
    Ω ∩ c.U = c.T '' (subgraphSet c.g ∩ cylinder c.g c.r c.ht) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxΩ, y, hy, rfl⟩
    refine ⟨y, ⟨?_, hy⟩, rfl⟩
    rcases lt_trichotomy (vert y) (c.g (horiz y)) with h | h | h
    · exact h
    · exact absurd hxΩ (hΩ.frontier_eq ▸ c.mem_frontier y hy h).2
    · exact absurd hxΩ (c.mem_outside y hy h)
  · rintro x ⟨y, ⟨hlt, hy⟩, rfl⟩
    exact ⟨c.mem_inside y hy hlt, Set.mem_image_of_mem _ hy⟩

end CylinderChart

/-- **The C¹-boundary hypothesis** (paper: "Ω̄ has C¹ boundary", made
precise in proof step 2): every boundary point admits a cylinder
chart. -/
def HasC1Boundary (Ω : Set E3) : Prop :=
  ∀ x₀ ∈ frontier Ω, ∃ c : CylinderChart Ω, x₀ ∈ c.U

/-- The boundary of a bounded set is compact (closed and bounded). -/
lemma isCompact_frontier (hb : Bornology.IsBounded Ω) :
    IsCompact (frontier Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)

/-! ### The outward unit normal (paper §2.2) -/

/-- The upward unit normal of the graph of `g` at the point above `z`:
`ν = (-∇g, 1)/√(1 + |∇g|²)`.  The normalizing factor is exactly
GraphArea's Jacobian `jac g z`. -/
def unitNormal (g : E2 → ℝ) (z : E2) : E3 :=
  (jac g z)⁻¹ • (WithLp.toLp 2 (-gradient g z, 1) : E3)

lemma horiz_unitNormal (g : E2 → ℝ) (z : E2) :
    horiz (unitNormal g z) = -((jac g z)⁻¹ • gradient g z) := by
  simp [unitNormal]

lemma vert_unitNormal (g : E2 → ℝ) (z : E2) :
    vert (unitNormal g z) = (jac g z)⁻¹ := by
  simp [unitNormal]

/-- The gradient and the Fréchet derivative have the same norm (the
gradient is the Riesz representative). -/
lemma norm_gradient_eq (g : E2 → ℝ) (z : E2) :
    ‖gradient g z‖ = ‖fderiv ℝ g z‖ := by
  rw [gradient]
  exact (InnerProductSpace.toDual ℝ E2).symm.norm_map _

/-- `⟪∇g, w⟫ = Dg(w)` (the defining property of the gradient). -/
lemma inner_gradient_eq (g : E2 → ℝ) (z : E2) (w : E2) :
    ⟪gradient g z, w⟫ = fderiv ℝ g z w := by
  rw [gradient]
  exact InnerProductSpace.toDual_symm_apply

/-- `J² = 1 + ‖∇g‖²`. -/
lemma jac_sq (g : E2 → ℝ) (z : E2) :
    jac g z ^ 2 = 1 + ‖gradient g z‖ ^ 2 := by
  rw [jac, Real.sq_sqrt (by positivity), norm_gradient_eq]

/-- The graph normal is a unit vector (paper §2.2, "divide by its
length"; no differentiability hypothesis is needed since `jac` and
`gradient` are built from the same junk-valued `fderiv`). -/
lemma norm_unitNormal (g : E2 → ℝ) (z : E2) : ‖unitNormal g z‖ = 1 := by
  have hpos : 0 < jac g z := jac_pos z
  have hsq : ‖(WithLp.toLp 2 (-gradient g z, 1) : E3)‖ ^ 2 = jac g z ^ 2 := by
    rw [norm_toLp_sq, norm_neg, jac_sq]
    ring
  have hnorm : ‖(WithLp.toLp 2 (-gradient g z, 1) : E3)‖ = jac g z := by
    have h := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hpos.le] at h
  rw [unitNormal, norm_smul, hnorm, norm_inv, Real.norm_eq_abs,
    abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

/-- The inner product of the graph normal with a graph-tangent direction
`(w, Dg·w)` vanishes — the algebraic heart of "perpendicular to the
surface" (paper §2.2). -/
lemma inner_unitNormal_graphDir (g : E2 → ℝ) (z : E2) (w : E2) :
    ⟪unitNormal g z, (WithLp.toLp 2 (w, fderiv ℝ g z w) : E3)⟫ = 0 := by
  rw [inner_eq, horiz_unitNormal, vert_unitNormal]
  simp only [horiz_toLp, vert_toLp, inner_neg_left, real_inner_smul_left,
    inner_gradient_eq]
  ring

/-- **The geometric characterization of the outward unit normal at a
boundary point** (paper §2.2): unit length, orthogonal to every tangent
direction of `∂Ω` at `x`, leaving `Ω̄` in the forward direction and
entering `Ω` in the backward direction. -/
def IsOutwardNormalAt (Ω : Set E3) (x v : E3) : Prop :=
  ‖v‖ = 1 ∧
  (∀ y ∈ tangentConeAt ℝ (frontier Ω) x, ⟪v, y⟫ = 0) ∧
  (∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • v ∉ closure Ω) ∧
  (∀ᶠ t in 𝓝[>] (0 : ℝ), x - t • v ∈ Ω)

/-- A choice of outward unit normal at every boundary point.  The main
theorem is stated for an arbitrary such field. -/
def IsOutwardNormal (Ω : Set E3) (ν : E3 → E3) : Prop :=
  ∀ x ∈ frontier Ω, IsOutwardNormalAt Ω x (ν x)

section NormalTheory

variable (c : CylinderChart Ω) {z : E2}

/-- The vertical overshoot (or undershoot) of the normal ray: for `ε = ±1`, the
point `Φz + t·(ε·ν)` stays in the cylinder and lies strictly above
(`ε = 1`) resp. strictly below (`ε = -1`) the graph for small `t > 0` —
the height difference has slope `ε²·J = J > 0` at `t = 0` (the paper's
"checking it points outward" Taylor computation). -/
private lemma eventually_ray_side (hz : z ∈ Metric.ball (0 : E2) c.r)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      graphMap c.g z + t • (ε • unitNormal c.g z) ∈ cylinder c.g c.r c.ht ∧
      0 < ε * (vert (graphMap c.g z + t • (ε • unitNormal c.g z))
        - c.g (horiz (graphMap c.g z + t • (ε • unitNormal c.g z)))) := by
  have hdiff : DifferentiableAt ℝ c.g z := (c.hg.differentiable one_ne_zero) z
  have hJ : 0 < jac c.g z := jac_pos z
  set ν := unitNormal c.g z with hν
  set q : ℝ → E3 := fun t => graphMap c.g z + t • (ε • ν) with hq
  have hq0 : q 0 = graphMap c.g z := by simp [hq]
  have hqcont : Continuous q :=
    continuous_const.add (continuous_id.smul continuous_const)
  -- (1) eventually in the (open) cylinder
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), q t ∈ cylinder c.g c.r c.ht := by
    have h0 : graphMap c.g z ∈ cylinder c.g c.r c.ht :=
      graphMap_mem_cylinder c.hht hz
    have ht : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (graphMap c.g z)) := by
      have := (hqcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      rwa [hq0] at this
    exact ht.eventually_mem
      ((isOpen_cylinder c.hg.continuous _ _).mem_nhds h0)
  -- (2) the signed height overshoot φ has derivative J > 0 at 0
  set φ : ℝ → ℝ := fun t => ε * (vert (q t) - c.g (horiz (q t))) with hφ
  have hφ0 : φ 0 = 0 := by simp [hφ, hq0]
  have hvert : ∀ t, vert (q t) = c.g z + t * (ε * (jac c.g z)⁻¹) := by
    intro t
    simp [hq, vert_unitNormal, hν]
  have hhoriz : ∀ t, horiz (q t)
      = z + t • (ε • -((jac c.g z)⁻¹ • gradient c.g z)) := by
    intro t
    simp [hq, horiz_unitNormal, hν]
  have hφd : HasDerivAt φ (jac c.g z) 0 := by
    set b : E2 := ε • -((jac c.g z)⁻¹ • gradient c.g z) with hb
    have hc : HasDerivAt (fun t : ℝ => z + t • b) b 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add z
    have hf' : HasFDerivAt c.g (fderiv ℝ c.g z) (z + (0 : ℝ) • b) := by
      simpa using hdiff.hasFDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => c.g (horiz (q t)))
        (fderiv ℝ c.g z b) 0 := by
      have h := hf'.comp_hasDerivAt (0 : ℝ) hc
      refine HasDerivAt.congr_of_eventuallyEq h (Eventually.of_forall fun t => ?_)
      show c.g (horiz (q t)) = c.g (z + t • b)
      rw [hhoriz t]
    have hv : HasDerivAt (fun t : ℝ => vert (q t)) (ε * (jac c.g z)⁻¹) 0 := by
      refine HasDerivAt.congr_of_eventuallyEq ?_ (Eventually.of_forall hvert)
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ε * (jac c.g z)⁻¹)).const_add (c.g z)
    have hd := (hv.sub hcomp).const_mul ε
    have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    have hDg : fderiv ℝ c.g z b
        = -(ε * ((jac c.g z)⁻¹ * ‖gradient c.g z‖ ^ 2)) := by
      rw [hb, map_smul, map_neg, map_smul, ← inner_gradient_eq,
        real_inner_self_eq_norm_sq]
      simp only [smul_eq_mul]
      ring
    have harith : ε * (ε * (jac c.g z)⁻¹
        - -(ε * ((jac c.g z)⁻¹ * ‖gradient c.g z‖ ^ 2))) = jac c.g z := by
      have hJsq := jac_sq c.g z
      field_simp
      nlinarith [hJ, hJsq]
    rw [hDg] at hd
    rwa [harith] at hd
  -- positive slope at 0 with φ 0 = 0 forces positivity on the right
  have hslope : Tendsto (fun t => φ t / t) (𝓝[>] (0 : ℝ)) (𝓝 (jac c.g z)) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hφd
    have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_mono _ fun t ht => ne_of_gt ht
    refine (h.mono_left hsub).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t _
    simp [slope_def_field, hφ0]
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < φ t := by
    filter_upwards [hslope.eventually_mem (Ioi_mem_nhds (half_lt_self hJ)),
      self_mem_nhdsWithin] with t hs ht
    have h1 : 0 < φ t / t := lt_trans (half_pos hJ) hs
    have h2 := mul_pos h1 (show (0:ℝ) < t from ht)
    rwa [div_mul_cancel₀ _ (ne_of_gt ht)] at h2
  filter_upwards [hmem, hpos] with t h1 h2 using ⟨h1, h2⟩

/-- Forward normal ray exits the closure of `Ω`. -/
private lemma eventually_ray_outside (hz : z ∈ Metric.ball (0 : E2) c.r) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      c.T (graphMap c.g z + t • unitNormal c.g z) ∉ closure Ω := by
  filter_upwards [eventually_ray_side c hz 1 (Or.inl rfl)] with t ht
  obtain ⟨hcyl, hup⟩ := ht
  simp only [one_smul, one_mul] at hcyl hup
  intro hcl
  exact Set.disjoint_left.mp c.image_upper_disjoint_closure
    ⟨_, ⟨hcyl, by simpa using sub_pos.mp hup⟩, rfl⟩ hcl

/-- Backward normal ray enters `Ω`. -/
private lemma eventually_ray_inside (hz : z ∈ Metric.ball (0 : E2) c.r) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      c.T (graphMap c.g z - t • unitNormal c.g z) ∈ Ω := by
  filter_upwards [eventually_ray_side c hz (-1) (Or.inr rfl)] with t ht
  obtain ⟨hcyl, hup⟩ := ht
  have heq : graphMap c.g z + t • ((-1 : ℝ) • unitNormal c.g z)
      = graphMap c.g z - t • unitNormal c.g z := by
    simp [sub_eq_add_neg]
  rw [heq] at hcyl hup
  refine c.mem_inside _ hcyl ?_
  nlinarith [hup]

/-- Every graph-tangent direction `T₀(w, Dg·w)` lies in the tangent cone
of `∂Ω` at the corresponding boundary point. -/
private lemma graphDir_mem_tangentCone (hz : z ∈ Metric.ball (0 : E2) c.r)
    (w : E2) :
    c.T.linearIsometryEquiv (WithLp.toLp 2 (w, fderiv ℝ c.g z w))
      ∈ tangentConeAt ℝ (frontier Ω) (c.T (graphMap c.g z)) := by
  have hdiff : DifferentiableAt ℝ c.g z := (c.hg.differentiable one_ne_zero) z
  set t : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ with ht
  have htpos : ∀ n, 0 < t n := fun n => by positivity
  have ht0 : Tendsto t atTop (𝓝 0) := by
    rw [ht]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  set zn : ℕ → E2 := fun n => z + t n • w with hzn
  have hzn0 : Tendsto zn atTop (𝓝 z) := by
    have hc : Continuous fun s : ℝ => s • w := by fun_prop
    have h : Tendsto (fun n => t n • w) atTop (𝓝 (0 : E2)) := by
      have h2 := (hc.tendsto 0).comp ht0
      simpa [Function.comp_def] using h2
    simpa using tendsto_const_nhds.add h
  refine mem_tangentConeAt_of_seq atTop (fun n => (t n)⁻¹)
    (fun n => c.T.linearIsometryEquiv (graphMap c.g (zn n) - graphMap c.g z))
    ?_ ?_ ?_
  · -- d n → 0
    have hg : Tendsto (fun n => graphMap c.g (zn n)) atTop (𝓝 (graphMap c.g z)) :=
      ((continuous_graphMap c.hg.continuous).tendsto z).comp hzn0
    have h := hg.sub (tendsto_const_nhds (x := graphMap c.g z))
    rw [sub_self] at h
    have h2 := (c.T.linearIsometryEquiv.continuous.tendsto' 0 0 (map_zero _)).comp h
    exact h2
  · -- x + d n ∈ frontier Ω eventually
    have hball : ∀ᶠ n in atTop, zn n ∈ Metric.ball (0 : E2) c.r :=
      hzn0.eventually_mem (Metric.isOpen_ball.mem_nhds hz)
    filter_upwards [hball] with n hn
    have heq : c.T (graphMap c.g z) + c.T.linearIsometryEquiv
        (graphMap c.g (zn n) - graphMap c.g z) = c.T (graphMap c.g (zn n)) := by
      rw [← c.map_add]
      congr 1
      abel
    rw [heq]
    exact c.mem_frontier _ (graphMap_mem_cylinder c.hht hn) (by simp)
  · -- (t n)⁻¹ • d n → T₀ (w, Dg w)
    have key : ∀ n, (t n)⁻¹ • (graphMap c.g (zn n) - graphMap c.g z)
        = (WithLp.toLp 2 ((t n)⁻¹ • (zn n - z), (c.g (zn n) - c.g z) / t n) : E3) := by
      intro n
      rw [div_eq_inv_mul]
      rfl
    have hzsub : ∀ n, (t n)⁻¹ • (zn n - z) = w := by
      intro n
      rw [hzn]
      simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (htpos n).ne', one_smul]
    have hslope : Tendsto (fun n => (c.g (zn n) - c.g z) / t n) atTop
        (𝓝 (fderiv ℝ c.g z w)) := by
      have hd : HasDerivAt (fun s : ℝ => c.g (z + s • w)) (fderiv ℝ c.g z w) 0 := by
        have hc : HasDerivAt (fun s : ℝ => z + s • w) w 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
        have hf' : HasFDerivAt c.g (fderiv ℝ c.g z) (z + (0 : ℝ) • w) := by
          simpa using hdiff.hasFDerivAt
        exact hf'.comp_hasDerivAt (0 : ℝ) hc
      have hs := hasDerivAt_iff_tendsto_slope.mp hd
      have htne : Tendsto t atTop (𝓝[≠] (0 : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨ht0, Eventually.of_forall fun n => (htpos n).ne'⟩
      have h := hs.comp htne
      refine h.congr fun n => ?_
      simp [slope_def_field, hzn]
    have hcont : Continuous fun p : ℝ => (WithLp.toLp 2 (w, p) : E3) :=
      (WithLp.prod_continuous_toLp 2 E2 ℝ).comp (continuous_const.prodMk continuous_id)
    have h := (c.T.linearIsometryEquiv.continuous.tendsto _).comp
      ((hcont.tendsto _).comp hslope)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [← map_smul, key n, hzsub n]

/-- Tangent vectors of `∂Ω` at a chart point are (moved) graph-tangent:
transported back through the rigid motion, their vertical component is
`Dg` of their horizontal component. -/
private lemma tangent_flat (hΩ : IsOpen Ω) (hz : z ∈ Metric.ball (0 : E2) c.r)
    {y : E3} (hy : y ∈ tangentConeAt ℝ (frontier Ω) (c.T (graphMap c.g z))) :
    vert (c.T.linearIsometryEquiv.symm y)
      = fderiv ℝ c.g z (horiz (c.T.linearIsometryEquiv.symm y)) := by
  have hdiff : DifferentiableAt ℝ c.g z := (c.hg.differentiable one_ne_zero) z
  obtain ⟨α, l, hl, cs, d, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
  set T₀ := c.T.linearIsometryEquiv with hT₀
  set d' : α → E3 := fun n => T₀.symm (d n) with hd'
  have hd'0 : Tendsto d' l (𝓝 0) := by
    have h := (T₀.symm.continuous.tendsto 0).comp hd0
    simpa [Function.comp_def, hd'] using h
  have hcd' : Tendsto (fun n => cs n • d' n) l (𝓝 (T₀.symm y)) := by
    have h := (T₀.symm.continuous.tendsto y).comp hcd
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, hd', map_smul]
  -- eventually the perturbed point sits on the graph piece of the chart
  have hgraph : ∀ᶠ n in l, vert (d' n) = c.g (z + horiz (d' n)) - c.g z := by
    have hcyl : ∀ᶠ n in l, graphMap c.g z + d' n ∈ cylinder c.g c.r c.ht := by
      have h0 : graphMap c.g z ∈ cylinder c.g c.r c.ht :=
        graphMap_mem_cylinder c.hht hz
      have htend : Tendsto (fun n => graphMap c.g z + d' n) l (𝓝 (graphMap c.g z)) := by
        simpa using (tendsto_const_nhds (x := graphMap c.g z)).add hd'0
      exact htend.eventually_mem
        ((isOpen_cylinder c.hg.continuous _ _).mem_nhds h0)
    filter_upwards [hds, hcyl] with n hn hcn
    have hTd : c.T (graphMap c.g z) + d n = c.T (graphMap c.g z + d' n) := by
      rw [c.map_add]
      simp only [hd', hT₀, LinearIsometryEquiv.apply_symm_apply]
    rw [hTd] at hn
    have hmem : c.T (graphMap c.g z + d' n) ∈ frontier Ω ∩ c.U :=
      ⟨hn, Set.mem_image_of_mem _ hcn⟩
    rw [c.frontier_inter_U hΩ] at hmem
    obtain ⟨p, hp, hEq⟩ := hmem
    have hpe : graphMap c.g z + d' n = p := (c.T.injective hEq).symm
    obtain ⟨ζ, -, rfl⟩ := hp
    have hh : z + horiz (d' n) = ζ := by
      have := congrArg horiz hpe
      simpa using this
    have hv : c.g z + vert (d' n) = c.g ζ := by
      have := congrArg vert hpe
      simpa using this
    rw [← hh] at hv
    linarith
  -- pass to the limit using differentiability of g at z
  have hw : Tendsto (fun n => cs n • horiz (d' n)) l (𝓝 (horiz (T₀.symm y))) := by
    have h := (continuous_horiz.tendsto _).comp hcd'
    refine h.congr fun n => ?_
    simp
  have hlittle : (fun w : E2 => c.g (z + w) - c.g z - fderiv ℝ c.g z w)
      =o[𝓝 0] fun w => w := by
    simpa using hasFDerivAt_iff_isLittleO_nhds_zero.mp hdiff.hasFDerivAt
  have hw0 : Tendsto (fun n => horiz (d' n)) l (𝓝 0) := by
    have h := (continuous_horiz.tendsto _).comp hd'0
    exact h
  have hro : Tendsto (fun n => cs n •
      (c.g (z + horiz (d' n)) - c.g z - fderiv ℝ c.g z (horiz (d' n)))) l (𝓝 0) := by
    have h1 : (fun n => c.g (z + horiz (d' n)) - c.g z - fderiv ℝ c.g z (horiz (d' n)))
        =o[l] fun n => horiz (d' n) := hlittle.comp_tendsto hw0
    have h2 := (Asymptotics.isBigO_refl cs l).smul_isLittleO h1
    have h3 : (fun n => cs n • horiz (d' n)) =O[l] fun _ => (1 : ℝ) :=
      hw.isBigO_one ℝ
    have h4 := h2.trans_isBigO h3
    rw [Asymptotics.isLittleO_one_iff] at h4
    exact h4
  have hDgw : Tendsto (fun n => fderiv ℝ c.g z (cs n • horiz (d' n))) l
      (𝓝 (fderiv ℝ c.g z (horiz (T₀.symm y)))) :=
    ((fderiv ℝ c.g z).continuous.tendsto _).comp hw
  have hv : Tendsto (fun n => cs n • vert (d' n)) l (𝓝 (vert (T₀.symm y))) := by
    have h := (continuous_vert.tendsto _).comp hcd'
    refine h.congr fun n => ?_
    simp
  have hv' : Tendsto (fun n => cs n • vert (d' n)) l
      (𝓝 (fderiv ℝ c.g z (horiz (T₀.symm y)))) := by
    have hsplit : (fun n => cs n • vert (d' n))
        =ᶠ[l] fun n => fderiv ℝ c.g z (cs n • horiz (d' n))
          + cs n • (c.g (z + horiz (d' n)) - c.g z - fderiv ℝ c.g z (horiz (d' n))) := by
      filter_upwards [hgraph] with n hn
      rw [hn]
      simp only [map_smul, smul_eq_mul]
      ring
    have h := hDgw.add hro
    rw [add_zero] at h
    exact Tendsto.congr' hsplit.symm h
  exact tendsto_nhds_unique hv hv'

/-- **The chart normal is an outward normal** (paper §2.2 in full): the
moved graph normal at any chart point satisfies the geometric
characterization. -/
theorem isOutwardNormalAt_chart (hΩ : IsOpen Ω) (c : CylinderChart Ω)
    {z : E2} (hz : z ∈ Metric.ball (0 : E2) c.r) :
    IsOutwardNormalAt Ω (c.T (graphMap c.g z))
      (c.T.linearIsometryEquiv (unitNormal c.g z)) := by
  refine ⟨by rw [c.T.linearIsometryEquiv.norm_map]; exact norm_unitNormal _ _,
    ?_, ?_, ?_⟩
  · -- orthogonal to the tangent cone
    intro y hy
    set T₀ := c.T.linearIsometryEquiv with hT₀
    have hflat := tangent_flat c hΩ hz hy
    have hy' : y = T₀ (WithLp.toLp 2 (horiz (T₀.symm y), vert (T₀.symm y))) := by
      rw [toLp_horiz_vert]
      simp
    rw [hy', T₀.inner_map_map, hflat]
    exact inner_unitNormal_graphDir c.g z _
  · -- forward ray exits Ω̄
    filter_upwards [eventually_ray_outside c hz] with t h
    rw [show c.T (graphMap c.g z) + t • c.T.linearIsometryEquiv (unitNormal c.g z)
        = c.T (graphMap c.g z + t • unitNormal c.g z) by rw [c.map_add, map_smul]]
    exact h
  · -- backward ray enters Ω
    filter_upwards [eventually_ray_inside c hz] with t h
    rw [show c.T (graphMap c.g z) - t • c.T.linearIsometryEquiv (unitNormal c.g z)
        = c.T (graphMap c.g z - t • unitNormal c.g z) by rw [c.map_sub, map_smul]]
    exact h

/-- **Uniqueness of the outward normal**: any vector satisfying the
geometric characterization at a chart point *is* the (moved) chart
normal.  The tangent-cone orthogonality forces `T₀⁻¹v = ±ν_g`; the
backward-ray condition kills the `−` sign (paper §2.2, "there are two
unit normals … we need to verify ours is the outward one"). -/
theorem IsOutwardNormalAt.eq_chart_normal (c : CylinderChart Ω)
    {z : E2} (hz : z ∈ Metric.ball (0 : E2) c.r) {v : E3}
    (hv : IsOutwardNormalAt Ω (c.T (graphMap c.g z)) v) :
    v = c.T.linearIsometryEquiv (unitNormal c.g z) := by
  obtain ⟨hv1, hv2, -, hv4⟩ := hv
  have hJ : 0 < jac c.g z := jac_pos z
  set T₀ := c.T.linearIsometryEquiv with hT₀
  set w₀ := T₀.symm v with hw₀
  have hvw : v = T₀ w₀ := by simp [hw₀]
  -- orthogonality against all graph directions
  have horth : ∀ w' : E2,
      ⟪horiz w₀, w'⟫ + vert w₀ * fderiv ℝ c.g z w' = 0 := by
    intro w'
    have h := hv2 _ (graphDir_mem_tangentCone c hz w')
    rw [hvw, T₀.inner_map_map, inner_eq] at h
    simpa using h
  have hkey : horiz w₀ = -(vert w₀ • gradient c.g z) := by
    have hall : ∀ w' : E2, ⟪horiz w₀ + vert w₀ • gradient c.g z, w'⟫ = 0 := by
      intro w'
      rw [inner_add_left, real_inner_smul_left, inner_gradient_eq]
      exact horth w'
    have h0 : horiz w₀ + vert w₀ • gradient c.g z = 0 := by
      have h := hall (horiz w₀ + vert w₀ • gradient c.g z)
      exact inner_self_eq_zero.mp h
    linear_combination (norm := module) h0
  -- unit length pins |vert w₀| = J⁻¹
  have hnorm : ‖w₀‖ = 1 := by
    rw [hw₀, T₀.symm.norm_map]
    exact hv1
  have hvert_sq : (vert w₀) ^ 2 * jac c.g z ^ 2 = 1 := by
    have hns := norm_sq_eq w₀
    rw [hkey, norm_neg, norm_smul, hnorm, Real.norm_eq_abs] at hns
    have h : (1 : ℝ) ^ 2 = (vert w₀) ^ 2 * ‖gradient c.g z‖ ^ 2 + (vert w₀) ^ 2 := by
      rw [hns]
      rw [mul_pow, sq_abs]
    rw [jac_sq]
    nlinarith [h]
  have hvert : vert w₀ = (jac c.g z)⁻¹ ∨ vert w₀ = -(jac c.g z)⁻¹ := by
    have h : (vert w₀ * jac c.g z) ^ 2 = 1 ^ 2 := by
      rw [mul_pow]
      simpa using hvert_sq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1
    · left
      field_simp at h1 ⊢
      linarith
    · right
      field_simp at h1 ⊢
      linarith
  rcases hvert with hpos | hneg
  · -- the positive sign: w₀ is the graph normal
    rw [hvw]
    congr 1
    refine E3_ext ?_ ?_
    · rw [hkey, hpos, horiz_unitNormal]
    · rw [hpos, vert_unitNormal]
  · -- the negative sign contradicts the backward-ray condition
    exfalso
    have hw₀eq : w₀ = -unitNormal c.g z := by
      refine E3_ext ?_ ?_
      · rw [hkey, hneg, horiz_neg, horiz_unitNormal]
        simp [neg_smul]
      · rw [hneg, vert_neg, vert_unitNormal]
    have hback : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        c.T (graphMap c.g z + t • unitNormal c.g z) ∈ Ω := by
      have h := hv4
      refine h.mono fun t ht => ?_
      have heq : c.T (graphMap c.g z) - t • v
          = c.T (graphMap c.g z + t • unitNormal c.g z) := by
        rw [hvw, hw₀eq, map_neg, smul_neg, sub_neg_eq_add, ← map_smul, ← c.map_add]
      rwa [heq] at ht
    obtain ⟨t, htin, htout⟩ := (hback.and (eventually_ray_outside c hz)).exists
    exact htout (subset_closure htin)

/-- A C¹ boundary admits an outward normal field (choose a chart at each
boundary point and take its graph normal). -/
lemma exists_isOutwardNormal (hΩ : IsOpen Ω) (hC1 : HasC1Boundary Ω) :
    ∃ ν : E3 → E3, IsOutwardNormal Ω ν := by
  have key : ∀ x ∈ frontier Ω, ∃ v, IsOutwardNormalAt Ω x v := by
    intro x hx
    obtain ⟨c, hc⟩ := hC1 x hx
    have hxg : x ∈ c.T '' graph c.g (Metric.ball (0 : E2) c.r) := by
      rw [← c.frontier_inter_U hΩ]
      exact ⟨hx, hc⟩
    obtain ⟨p, hp, rfl⟩ := hxg
    obtain ⟨w, hw, rfl⟩ := hp
    exact ⟨_, isOutwardNormalAt_chart hΩ c hw⟩
  choose! ν hν using key
  exact ⟨ν, hν⟩

end NormalTheory

/-
# Step 1: reduction to compactly supported functions (paper proof step 1, §3.1)

A smooth cutoff `φ ∈ C_c^∞(O)` with `φ ≡ 1` on the compact set `Ω̄ ⊆ O`
lets us replace `u ∈ C¹(O)` by `φu ∈ C¹_c(ℝ³)` without changing either
side of the divergence theorem.

This file also proves the **vanishing-integral lemma** (paper's Lemma
"Partial FTC for Compactly Supported C¹ Functions", total form): the
integral of a directional derivative of a compactly supported `C¹`
function is zero, on *any* finite-dimensional normed space.  Instead of
the paper's Fubini-and-FTC argument we integrate by parts
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) against a cutoff
that is `≡ 1` on a neighborhood of the support, so both sides collapse.

Everything is recorded at `C¹` regularity (mathlib's Urysohn lemma is
smoothness-polymorphic, so we can ask for `C¹` directly). -/




section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Smooth cutoff** (paper's Lemma "Smooth Cutoff Function", §3.1), on
any finite-dimensional normed space: for `K` compact inside open `O`
there is `φ ∈ C¹_c(O)`, `0 ≤ φ ≤ 1`, with `φ ≡ 1` on `K`. -/
theorem exists_cutoff' {K O : Set E} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) :
    ∃ φ : E → ℝ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧
      EqOn φ 1 K ∧ ∀ x, φ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨L, hL, hKL, hLO⟩ := exists_compact_between hK hO hKO
  have hdisj : Disjoint (interior L)ᶜ K :=
    Set.disjoint_left.mpr fun x hx hxK => hx (hKL hxK)
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (n := 1) 𝓘(ℝ, E)
      isOpen_interior.isClosed_compl hK.isClosed hdisj
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, ?_, ?_, hf1, hf01⟩
  · refine HasCompactSupport.intro hL fun x hx => ?_
    have hmem : x ∈ (interior L)ᶜ := fun hint => hx (interior_subset hint)
    simpa using hf0 hmem
  · refine subset_trans (closure_minimal ?_ hL.isClosed) hLO
    intro x hx
    by_contra hxL
    have hmem : x ∈ (interior L)ᶜ := fun hint => hxL (interior_subset hint)
    exact hx (by simpa using hf0 hmem)

omit [FiniteDimensional ℝ E] in
/-- Off the (closed) support, the derivative vanishes. -/
theorem fderiv_eq_zero_of_notMem_tsupport {u : E → ℝ} {x : E}
    (hx : x ∉ tsupport u) : fderiv ℝ u x = 0 := by
  have h : u =ᶠ[𝓝 x] 0 := by
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [h.fderiv_eq]
  simp

omit [FiniteDimensional ℝ E] in
/-- The directional derivative of a compactly supported function is
compactly supported. -/
theorem hasCompactSupport_fderiv_apply {u : E → ℝ}
    (hcs : HasCompactSupport u) (v : E) :
    HasCompactSupport fun x => fderiv ℝ u x v := by
  refine HasCompactSupport.intro hcs fun x hx => ?_
  rw [fderiv_eq_zero_of_notMem_tsupport hx]
  rfl

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The vanishing-integral lemma** (paper's "Partial FTC", total
form): `∫ Du·v = 0` for compactly supported `C¹` functions, on any
finite-dimensional space with a Haar measure.  Proof: integrate by
parts against a cutoff `φ ≡ 1` near `supp u`; both boundary-free sides
collapse. -/
theorem integral_fderiv_eq_zero' {u : E → ℝ} (hu : ContDiff ℝ 1 u)
    (hcs : HasCompactSupport u) (v : E) :
    ∫ x, fderiv ℝ u x v ∂μ = 0 := by
  obtain ⟨L, hL, hKL, -⟩ := exists_compact_between hcs isOpen_univ (subset_univ _)
  obtain ⟨φ, hφC, hφcs, -, hφ1, -⟩ := exists_cutoff' hL isOpen_univ (subset_univ _)
  have hφu : ∀ x, φ x * fderiv ℝ u x v = fderiv ℝ u x v := by
    intro x
    by_cases hx : x ∈ tsupport u
    · rw [hφ1 (interior_subset (hKL hx)), Pi.one_apply, one_mul]
    · rw [fderiv_eq_zero_of_notMem_tsupport hx]
      simp
  have hφ'u : ∀ x, fderiv ℝ φ x v * u x = 0 := by
    intro x
    by_cases hx : x ∈ tsupport u
    · have hloc : φ =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [isOpen_interior.mem_nhds (hKL hx)] with y hy
        exact hφ1 (interior_subset hy)
      rw [hloc.fderiv_eq]
      simp
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hDu : Continuous fun x => fderiv ℝ u x v :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have int1 : Integrable (fun x => fderiv ℝ φ x v * u x) μ :=
    (integrable_zero _ _ _).congr (ae_of_all _ fun x => (hφ'u x).symm)
  have int2' : Integrable (fun x => fderiv ℝ u x v) μ :=
    hDu.integrable_of_hasCompactSupport (hasCompactSupport_fderiv_apply hcs v)
  have int2 : Integrable (fun x => φ x * fderiv ℝ u x v) μ :=
    int2'.congr (ae_of_all _ fun x => (hφu x).symm)
  have int3 : Integrable (fun x => φ x * u x) μ :=
    (hφC.continuous.mul hu.continuous).integrable_of_hasCompactSupport hcs.mul_left
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable int1 int2 int3
    (fun x _ => (hφC.differentiable one_ne_zero) x)
    (fun x _ => (hu.differentiable one_ne_zero) x)
  calc ∫ x, fderiv ℝ u x v ∂μ
      = ∫ x, φ x * fderiv ℝ u x v ∂μ :=
        integral_congr_ae (ae_of_all _ fun x => (hφu x).symm)
    _ = - ∫ x, fderiv ℝ φ x v * u x ∂μ := key
    _ = 0 := by simp [hφ'u]

end Generic

/-- **Smooth cutoff on ℝ³** (paper's Lemma "Smooth Cutoff Function",
§3.1). -/
theorem exists_cutoff {K O : Set E3} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) :
    ∃ φ : E3 → ℝ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧
      EqOn φ 1 K ∧ ∀ x, φ x ∈ Icc (0 : ℝ) 1 :=
  exists_cutoff' hK hO hKO

/-- On `Ω`, `φ ≡ 1` forces `D(φu) = Du` (paper part 1: "Left side").
No differentiability of `u` is needed: `φ * u` and `u` agree on a
neighborhood of `x`, so their derivatives agree. -/
theorem fderiv_cutoff_mul {φ u : E3 → ℝ} {Ω : Set E3} (hΩ : IsOpen Ω)
    (hφ1 : EqOn φ 1 (closure Ω)) {x : E3} (hx : x ∈ Ω) :
    fderiv ℝ (fun y => φ y * u y) x = fderiv ℝ u x := by
  have hev : (fun y => φ y * u y) =ᶠ[𝓝 x] u := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [hφ1 (subset_closure hy), Pi.one_apply, one_mul]
  exact hev.fderiv_eq

/-- On `∂Ω ⊆ Ω̄`, `φ ≡ 1` gives `φu = u` (paper part 1: "Right side"). -/
theorem eqOn_cutoff_mul_frontier {φ u : E3 → ℝ} {Ω : Set E3}
    (hφ1 : EqOn φ 1 (closure Ω)) :
    EqOn (fun y => φ y * u y) u (frontier Ω) := by
  intro x hx
  show φ x * u x = u x
  rw [hφ1 (frontier_subset_closure hx), Pi.one_apply, one_mul]

/-- The cutoff product is `C¹` with compact support (paper part 1,
Claims 1–2: product rule plus `supp(φu) ⊆ supp φ`; the extension by
zero outside `O` is handled by gluing the two open regions `O` and
`(supp φ)ᶜ`, no explicit `tilde f` construction needed). -/
theorem contDiff_cutoff_mul {φ u : E3 → ℝ} {O : Set E3} (hO : IsOpen O)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφO : tsupport φ ⊆ O)
    (hu : ContDiffOn ℝ 1 u O) :
    ContDiff ℝ 1 (fun y => φ y * u y) ∧
      HasCompactSupport (fun y => φ y * u y) := by
  constructor
  · rw [← contDiffOn_univ]
    refine contDiffOn_of_locally_contDiffOn fun x _ => ?_
    by_cases hx : x ∈ O
    · exact ⟨O, hO, hx, (hφ.contDiffOn.mul hu).mono Set.inter_subset_right⟩
    · refine ⟨(tsupport φ)ᶜ, (isClosed_tsupport φ).isOpen_compl,
        fun h => hx (hφO h), ?_⟩
      refine (contDiffOn_const (c := (0 : ℝ))).congr fun y hy => ?_
      rw [image_eq_zero_of_notMem_tsupport hy.2, zero_mul]
  · exact hφc.mul_right

/-
# Step 3: the direct computation over a flat chart (paper proof step 3, §3.3)

The heart of the proof, with the rigid motion normalized away
(`T = id`): for `u ∈ C¹_c(ℝ³)` and `g ∈ C¹(ℝ²)`,

    ∫_{Σ_g} Du·w  =  ∫_{ℝ²} u(z, g z) ⟨(-∇g z, 1), w⟩ dz ,

split into the vertical direction (pure FTC) and the horizontal
directions (the shear `v(z, s) = u(z, g z + s)`, chain rule, and the
vanishing integral of `v_{x_i}` — the latter via the cutoff
integration-by-parts lemma from `Divergence.Cutoff`, sliced at fixed
height).

Everything here is stated for a *global* `C¹` function `g` and a
*globally* compactly supported `u` — no cylinder is needed at this
stage; localization happens in `Main`.
-/




/-! ### The product split `ℝ³ = ℝ² × ℝ` as a measure identity -/

/-- Lebesgue measure on `E3` is the product measure through the
`WithLp` identification — the Fubini workhorse for every iterated
integral in this file (paper: "By Fubini's theorem…"). -/
theorem measurePreserving_toLp :
    MeasurePreserving (WithLp.toLp 2 : E2 × ℝ → E3)
      (volume.prod volume) volume := by
  have h := WithLp.volume_preserving_toLp E2 ℝ
  rwa [Measure.volume_eq_prod] at h

/-! ### Elementary derivative helpers -/

/-- Derivative of an affine line `t ↦ p + t • v`. -/
private lemma hasDerivAt_line {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (p v : F) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => p + t • v) v t₀ := by
  simpa using ((hasDerivAt_id t₀).smul_const v).const_add p

private lemma contDiff_toLp_pair :
    ContDiff ℝ 1 fun q : E2 × ℝ => (WithLp.toLp 2 q : E3) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ).symm.contDiff

/-- The vertical line through `(z, ·)` as a curve in `E3` has constant
derivative `e₃ = (0, 1)`. -/
private lemma hasDerivAt_vertLine (z : E2) (a s : ℝ) :
    HasDerivAt (fun s' : ℝ => (WithLp.toLp 2 (z, a + s') : E3))
      (WithLp.toLp 2 (0, 1)) s := by
  have hEq : ∀ s' : ℝ, (WithLp.toLp 2 (z, a + s') : E3)
      = WithLp.toLp 2 (z, a) + s' • WithLp.toLp 2 (0, 1) := by
    intro s'
    apply E3_ext <;> simp
  refine HasDerivAt.congr_of_eventuallyEq ?_ (Eventually.of_forall hEq)
  exact hasDerivAt_line _ _ s

/-- Fixed-height slices of compactly supported functions on `E3` are
compactly supported on `E2`. -/
private lemma hasCompactSupport_slice_horiz {f : E3 → ℝ}
    (hcs : HasCompactSupport f) (s : ℝ) :
    HasCompactSupport fun z : E2 => f (WithLp.toLp 2 (z, s)) := by
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E2) R) fun z hz => ?_
  by_contra h0
  have hmem : (WithLp.toLp 2 (z, s) : E3) ∈ tsupport f := subset_closure h0
  have hnorm : ‖(WithLp.toLp 2 (z, s) : E3)‖ ≤ R := by
    simpa [mem_closedBall_zero_iff] using hR hmem
  exact hz (by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_fst_le_norm_toLp z s).trans hnorm)

/-- Vertical slices of compactly supported functions on `E3` are
compactly supported on `ℝ`. -/
private lemma hasCompactSupport_slice_vert {f : E3 → ℝ}
    (hcs : HasCompactSupport f) (z : E2) :
    HasCompactSupport fun s : ℝ => f (WithLp.toLp 2 (z, s)) := by
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R) fun s hs => ?_
  by_contra h0
  have hmem : (WithLp.toLp 2 (z, s) : E3) ∈ tsupport f := subset_closure h0
  have hnorm : ‖(WithLp.toLp 2 (z, s) : E3)‖ ≤ R := by
    simpa [mem_closedBall_zero_iff] using hR hmem
  exact hs (by
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact (abs_snd_le_norm_toLp z s).trans hnorm)

/-- Composition with `graphMap` preserves compact support (the graph of
`g` over a bounded set is bounded horizontally). -/
private lemma hasCompactSupport_comp_graphMap {f : E3 → ℝ}
    (hcs : HasCompactSupport f) (g : E2 → ℝ) :
    HasCompactSupport fun z : E2 => f (graphMap g z) := by
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E2) R) fun z hz => ?_
  by_contra h0
  have hmem : graphMap g z ∈ tsupport f := subset_closure h0
  have hnorm : ‖graphMap g z‖ ≤ R := by
    simpa [mem_closedBall_zero_iff] using hR hmem
  exact hz (by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_fst_le_norm_toLp z (g z)).trans hnorm)

/-- Differentiating a fixed-height slice: the slice derivative in the
direction `w'` is the ambient derivative in the direction `(w', 0)`. -/
private lemma fderiv_slice {f : E3 → ℝ} (hf : ContDiff ℝ 1 f) (s : ℝ)
    (z w' : E2) :
    fderiv ℝ (fun z' : E2 => f (WithLp.toLp 2 (z', s))) z w'
      = fderiv ℝ f (WithLp.toLp 2 (z, s)) (WithLp.toLp 2 (w', 0)) := by
  set ι : E2 → E3 := fun z' => WithLp.toLp 2 (z', s) with hι
  have hιC : ContDiff ℝ 1 ι :=
    contDiff_toLp_pair.comp (contDiff_id.prodMk contDiff_const)
  have hcurve : ∀ t : ℝ, ι (z + t • w') = ι z + t • (WithLp.toLp 2 (w', 0) : E3) := by
    intro t
    apply E3_ext <;> simp [hι]
  -- left side as a line derivative
  have hsliceC : ContDiff ℝ 1 fun z' => f (ι z') := hf.comp hιC
  have hf' : HasFDerivAt (fun z' => f (ι z'))
      (fderiv ℝ (fun z' => f (ι z')) z) (z + (0 : ℝ) • w') := by
    simpa using ((hsliceC.differentiable one_ne_zero) z).hasFDerivAt
  have hL := hf'.comp_hasDerivAt 0 (hasDerivAt_line z w' 0)
  -- right side as the line derivative of `f` along the moved line
  have hg' : HasFDerivAt f (fderiv ℝ f (ι z)) (ι z + (0 : ℝ) • WithLp.toLp 2 (w', 0)) := by
    simpa using ((hf.differentiable one_ne_zero) (ι z)).hasFDerivAt
  have hR := hg'.comp_hasDerivAt 0 (hasDerivAt_line (ι z) (WithLp.toLp 2 (w', 0)) 0)
  have hR' : HasDerivAt (fun t : ℝ => f (ι (z + t • w')))
      (fderiv ℝ f (ι z) (WithLp.toLp 2 (w', 0))) 0 := by
    refine HasDerivAt.congr_of_eventuallyEq hR (Eventually.of_forall fun t => ?_)
    show f (ι (z + t • w')) = f (ι z + t • WithLp.toLp 2 (w', 0))
    rw [hcurve t]
  exact hL.unique hR'

/-- The vertical shear `(z, s) ↦ (z, g z + s)` as a homeomorphism of
`ℝ² × ℝ`. -/
private def shearHomeo {g : E2 → ℝ} (hg : Continuous g) :
    (E2 × ℝ) ≃ₜ (E2 × ℝ) where
  toFun q := (q.1, g q.1 + q.2)
  invFun q := (q.1, q.2 - g q.1)
  left_inv q := by simp
  right_inv q := by simp
  continuous_toFun := continuous_fst.prodMk
    ((hg.comp continuous_fst).add continuous_snd)
  continuous_invFun := continuous_fst.prodMk
    (continuous_snd.sub (hg.comp continuous_fst))

/-! ### The shear map (paper part 3, "the function v") -/

/-- The shear `v(z, s) = u(z, g z + s)`, straightening the graph of `g`
to the plane `s = 0`. -/
def shear (g : E2 → ℝ) (u : E3 → ℝ) : E3 → ℝ :=
  fun p => u (WithLp.toLp 2 (horiz p, g (horiz p) + vert p))

private lemma contDiff_shearMap {g : E2 → ℝ} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 fun p : E3 => (WithLp.toLp 2 (horiz p, g (horiz p) + vert p) : E3) := by
  have hh : ContDiff ℝ 1 horiz :=
    contDiff_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ).contDiff
  have hv : ContDiff ℝ 1 vert :=
    contDiff_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ).contDiff
  exact contDiff_toLp_pair.comp (hh.prodMk ((hg.comp hh).add hv))

/-- The shear of a `C¹` function is `C¹` (composition of `C¹` maps;
paper's Lemma "Compact Support of v", first sentence). -/
theorem contDiff_shear {g : E2 → ℝ} (hg : ContDiff ℝ 1 g) {u : E3 → ℝ}
    (hu : ContDiff ℝ 1 u) : ContDiff ℝ 1 (shear g u) :=
  hu.comp (contDiff_shearMap hg)

/-- The shear of a compactly supported function is compactly supported.
(Unlike the paper, no cylinder is needed: `supp u ⊆ B(0, R)` forces
`‖z‖ ≤ R` and `|g z + s| ≤ R`, and `g` is bounded on the compact disk,
so `s` is bounded too.) -/
theorem hasCompactSupport_shear {g : E2 → ℝ} (hg : Continuous g)
    {u : E3 → ℝ} (hcs : HasCompactSupport u) :
    HasCompactSupport (shear g u) := by
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E2) R).exists_bound_of_continuousOn
    hg.continuousOn
  set K : Set E3 := {p | ‖horiz p‖ ≤ R ∧ |vert p| ≤ R + C} with hK
  have hKclosed : IsClosed K :=
    (isClosed_le (continuous_norm.comp continuous_horiz) continuous_const).inter
      (isClosed_le continuous_vert.abs continuous_const)
  have hKbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : E3)) (r := R + (R + C))).subset ?_
    rintro p ⟨h1, h2⟩
    have : ‖p‖ ≤ ‖horiz p‖ + |vert p| := by
      conv_lhs => rw [← toLp_horiz_vert p]
      exact norm_toLp_le _ _
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  refine HasCompactSupport.intro
    (Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd) fun p hp => ?_
  by_contra h0
  have hmem : (WithLp.toLp 2 (horiz p, g (horiz p) + vert p) : E3) ∈ tsupport u :=
    subset_closure h0
  have hnorm : ‖(WithLp.toLp 2 (horiz p, g (horiz p) + vert p) : E3)‖ ≤ R := by
    simpa [mem_closedBall_zero_iff] using hR hmem
  have h1 : ‖horiz p‖ ≤ R := (norm_fst_le_norm_toLp _ _).trans hnorm
  have h2 : |g (horiz p) + vert p| ≤ R := (abs_snd_le_norm_toLp _ _).trans hnorm
  have h3 : |g (horiz p)| ≤ C := by
    have := hC (horiz p) (by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact h1)
    simpa [Real.norm_eq_abs] using this
  have h4 : |vert p| ≤ |g (horiz p) + vert p| + |g (horiz p)| := by
    have heq : vert p = g (horiz p) + vert p + -g (horiz p) := by ring
    calc |vert p| = ‖g (horiz p) + vert p + -g (horiz p)‖ := by
          rw [Real.norm_eq_abs, ← heq]
      _ ≤ ‖g (horiz p) + vert p‖ + ‖-g (horiz p)‖ := norm_add_le _ _
      _ = |g (horiz p) + vert p| + |g (horiz p)| := by
          rw [norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
  exact hp ⟨h1, h4.trans (add_le_add h2 h3)⟩

/-- **Chain rule for the shear** (paper part 3, "By the chain rule"):
for a horizontal direction `w'`,
`D v (z,s) (w',0) = D u (z, g z + s) (w', ∇g z · w')`. -/
theorem fderiv_shear_horizontal {g : E2 → ℝ} (hg : ContDiff ℝ 1 g)
    {u : E3 → ℝ} (hu : ContDiff ℝ 1 u) (p : E3) (w' : E2) :
    fderiv ℝ (shear g u) p (WithLp.toLp 2 (w', 0))
      = fderiv ℝ u (WithLp.toLp 2 (horiz p, g (horiz p) + vert p))
          (WithLp.toLp 2 (w', fderiv ℝ g (horiz p) w')) := by
  set v : E3 := WithLp.toLp 2 (w', 0) with hv
  -- LHS as a line derivative
  have hL : HasDerivAt (fun t : ℝ => shear g u (p + t • v))
      (fderiv ℝ (shear g u) p v) 0 := by
    have hf' : HasFDerivAt (shear g u) (fderiv ℝ (shear g u) p) (p + (0 : ℝ) • v) := by
      simpa using (((contDiff_shear hg hu).differentiable one_ne_zero) p).hasFDerivAt
    have h := hf'.comp_hasDerivAt 0 (hasDerivAt_line p v 0)
    exact h
  -- the same curve written through the graph coordinates
  have hcurve : ∀ t : ℝ, shear g u (p + t • v)
      = u (WithLp.toLp 2 (horiz p + t • w', g (horiz p + t • w') + vert p)) := by
    intro t
    have h1 : horiz (p + t • v) = horiz p + t • w' := by simp [hv]
    have h2 : vert (p + t • v) = vert p := by simp [hv]
    show u (WithLp.toLp 2 (horiz (p + t • v), g (horiz (p + t • v)) + vert (p + t • v))) = _
    rw [h1, h2]
  -- RHS as the line derivative of `u` along the graph curve
  have hγ2 : HasDerivAt (fun t : ℝ => g (horiz p + t • w') + vert p)
      (fderiv ℝ g (horiz p) w') 0 := by
    have hgd : HasFDerivAt g (fderiv ℝ g (horiz p)) (horiz p + (0 : ℝ) • w') := by
      simpa using ((hg.differentiable one_ne_zero) (horiz p)).hasFDerivAt
    simpa using (hgd.comp_hasDerivAt 0 (hasDerivAt_line (horiz p) w' 0)).add_const (vert p)
  have hγ1 : HasDerivAt (fun t : ℝ => horiz p + t • w') w' 0 := hasDerivAt_line _ _ 0
  have hpair := hγ1.prodMk hγ2
  have htoLp : HasDerivAt
      (fun t : ℝ => (WithLp.toLp 2 (horiz p + t • w', g (horiz p + t • w') + vert p) : E3))
      (WithLp.toLp 2 (w', fderiv ℝ g (horiz p) w')) 0 := by
    have hP : HasFDerivAt (WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ).symm
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ).symm : (E2 × ℝ) →L[ℝ] E3)
        ((horiz p + (0 : ℝ) • w', g (horiz p + (0 : ℝ) • w') + vert p) : E2 × ℝ) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ).symm.hasFDerivAt
    exact hP.comp_hasDerivAt 0 hpair
  have hu' : HasFDerivAt u
      (fderiv ℝ u (WithLp.toLp 2 (horiz p, g (horiz p) + vert p)))
      (WithLp.toLp 2 (horiz p + (0 : ℝ) • w', g (horiz p + (0 : ℝ) • w') + vert p) : E3) := by
    simpa using ((hu.differentiable one_ne_zero)
      (WithLp.toLp 2 (horiz p, g (horiz p) + vert p))).hasFDerivAt
  have hR := hu'.comp_hasDerivAt 0 htoLp
  have hL' : HasDerivAt
      (fun t : ℝ => u (WithLp.toLp 2 (horiz p + t • w', g (horiz p + t • w') + vert p)))
      (fderiv ℝ (shear g u) p v) 0 := by
    refine HasDerivAt.congr_of_eventuallyEq hL ?_
    exact Eventually.of_forall fun t => (hcurve t).symm
  exact hL'.unique hR

/-! ### The two directional computations -/

/-- **Vertical direction** (paper part 3, "For i = n"): FTC along the
last coordinate, `∫_{Σ_g} ∂₃u = ∫_{ℝ²} u(z, g z) dz`. -/
theorem flat_vertical {g : E2 → ℝ} (hg : ContDiff ℝ 1 g) {u : E3 → ℝ}
    (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) :
    ∫ x in subgraphSet g, fderiv ℝ u x (WithLp.toLp 2 (0, 1))
      = ∫ z : E2, u (graphMap g z) := by
  set e3 : E3 := WithLp.toLp 2 (0, 1) with he3
  set F : E2 × ℝ → ℝ := fun q => fderiv ℝ u (WithLp.toLp 2 q) e3 with hF
  set R : Set (E2 × ℝ) := {q : E2 × ℝ | q.2 < g q.1} with hRdef
  -- Step A: transfer to the product space
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : E2 × ℝ → E3) :=
    (MeasurableEquiv.toLp 2 (E2 × ℝ)).measurableEmbedding
  have hstepA : ∫ x in subgraphSet g, fderiv ℝ u x e3
      = ∫ q in R, F q ∂(volume.prod volume) :=
    (measurePreserving_toLp.setIntegral_preimage_emb hemb
      (fun x => fderiv ℝ u x e3) (subgraphSet g)).symm
  -- continuity, support, measurability
  have hDu : Continuous fun x : E3 => fderiv ℝ u x e3 :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hFc : Continuous F :=
    hDu.comp (WithLp.prod_continuous_toLp 2 E2 ℝ)
  have hFcs : HasCompactSupport F :=
    (hasCompactSupport_fderiv_apply hcs e3).comp_homeomorph
      (WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ).toHomeomorph.symm
  have hR : MeasurableSet R :=
    measurableSet_lt measurable_snd (hg.continuous.measurable.comp measurable_fst)
  have hFint : Integrable F (volume.prod volume) :=
    hFc.integrable_of_hasCompactSupport hFcs
  -- Step B: Fubini
  have hstepB : ∫ q in R, F q ∂(volume.prod volume)
      = ∫ z : E2, ∫ s in Iio (g z), F (z, s) := by
    rw [← integral_indicator hR, integral_prod _ (hFint.indicator hR)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show (∫ s : ℝ, R.indicator F (z, s)) = ∫ s in Iio (g z), F (z, s)
    rw [← integral_indicator measurableSet_Iio]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp [Set.indicator_apply, hRdef, Set.mem_Iio, Set.mem_setOf_eq]
  -- Step C: the inner FTC
  have hstepC : ∀ z : E2, ∫ s in Iio (g z), F (z, s) = u (graphMap g z) := by
    intro z
    set h : ℝ → ℝ := fun s => u (WithLp.toLp 2 (z, s)) with hh
    have hhC : ContDiff ℝ 1 h :=
      hu.comp (contDiff_toLp_pair.comp (contDiff_const.prodMk contDiff_id))
    have hhcs : HasCompactSupport h := hasCompactSupport_slice_vert hcs z
    have hderiv : ∀ s, F (z, s) = deriv h s := by
      intro s
      have hcurve : HasDerivAt (fun s' : ℝ => (WithLp.toLp 2 (z, s') : E3)) e3 s := by
        have := hasDerivAt_vertLine z 0 s
        simpa using this
      have hu'' : HasFDerivAt u (fderiv ℝ u (WithLp.toLp 2 (z, s)))
          (WithLp.toLp 2 (z, s)) :=
        ((hu.differentiable one_ne_zero) _).hasFDerivAt
      exact ((hu''.comp_hasDerivAt s hcurve).deriv).symm
    calc ∫ s in Iio (g z), F (z, s)
        = ∫ s in Iio (g z), deriv h s :=
          setIntegral_congr_fun measurableSet_Iio fun s _ => hderiv s
      _ = ∫ s in Iic (g z), deriv h s := setIntegral_congr_set Iio_ae_eq_Iic
      _ = h (g z) := HasCompactSupport.integral_Iic_deriv_eq hhC hhcs (g z)
      _ = u (graphMap g z) := rfl
  rw [hstepA, hstepB]
  exact integral_congr_ae (ae_of_all _ fun z => hstepC z)

/-- **Horizontal directions** (paper part 3, "Now fix i ∈ {1,…,n−1}"):
shift by the shear, kill `∫ v_{x_i}` by the vanishing-integral lemma in
each horizontal slice, and what survives is the graph term,
`∫_{Σ_g} Du·(w',0) = −∫_{ℝ²} u(z, g z) (∇g z · w') dz`. -/
theorem flat_horizontal {g : E2 → ℝ} (hg : ContDiff ℝ 1 g) {u : E3 → ℝ}
    (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) (w' : E2) :
    ∫ x in subgraphSet g, fderiv ℝ u x (WithLp.toLp 2 (w', 0))
      = -∫ z : E2, u (graphMap g z) * fderiv ℝ g z w' := by
  set v : E3 := WithLp.toLp 2 (w', 0) with hv
  set e3 : E3 := WithLp.toLp 2 (0, 1) with he3
  set F : E2 × ℝ → ℝ := fun q => fderiv ℝ u (WithLp.toLp 2 q) v with hF
  set R : Set (E2 × ℝ) := {q : E2 × ℝ | q.2 < g q.1} with hRdef
  set R₀ : Set (E2 × ℝ) := {q : E2 × ℝ | q.2 < 0} with hR₀def
  -- Step A: transfer to the product space
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : E2 × ℝ → E3) :=
    (MeasurableEquiv.toLp 2 (E2 × ℝ)).measurableEmbedding
  have hstepA : ∫ x in subgraphSet g, fderiv ℝ u x v
      = ∫ q in R, F q ∂(volume.prod volume) :=
    (measurePreserving_toLp.setIntegral_preimage_emb hemb
      (fun x => fderiv ℝ u x v) (subgraphSet g)).symm
  -- Step B: the shear change of variables
  set Sh : E2 × ℝ → E2 × ℝ := fun q => (q.1, g q.1 + q.2) with hSh
  have hShmp : MeasurePreserving Sh (volume.prod volume) (volume.prod volume) := by
    have h := (MeasurePreserving.id (volume : Measure E2)).skew_product
      (g := fun z s => g z + s)
      ((hg.continuous.measurable.comp measurable_fst).add measurable_snd)
      (ae_of_all _ fun z => (measurePreserving_add_left volume (g z)).map_eq)
    exact h
  have hcoe : ⇑(shearHomeo hg.continuous) = Sh := rfl
  have hShemb : MeasurableEmbedding Sh := by
    have h := (shearHomeo hg.continuous).measurableEmbedding
    rwa [hcoe] at h
  have hShcont : Continuous Sh := by
    have h := (shearHomeo hg.continuous).continuous
    rwa [hcoe] at h
  have hSpre : Sh ⁻¹' R = R₀ := by
    ext q
    simp only [hSh, hRdef, hR₀def, Set.mem_preimage, Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  have hstepB : ∫ q in R, F q ∂(volume.prod volume)
      = ∫ q in R₀, F (Sh q) ∂(volume.prod volume) := by
    rw [← hShmp.setIntegral_preimage_emb hShemb F R, hSpre]
  -- Step C: the pointwise chain-rule split
  set A : E2 × ℝ → ℝ := fun q => fderiv ℝ (shear g u) (WithLp.toLp 2 q) v with hA
  set B : E2 × ℝ → ℝ :=
    fun q => fderiv ℝ g q.1 w' * fderiv ℝ u (WithLp.toLp 2 (Sh q)) e3 with hB
  have hsplit : ∀ q : E2 × ℝ, F (Sh q) = A q - B q := by
    intro q
    have hfsh := fderiv_shear_horizontal hg hu (WithLp.toLp 2 q) w'
    have hq1 : horiz (WithLp.toLp 2 q) = q.1 := rfl
    have hq2 : vert (WithLp.toLp 2 q) = q.2 := rfl
    rw [hq1, hq2] at hfsh
    have hdir : (WithLp.toLp 2 (w', fderiv ℝ g q.1 w') : E3)
        = v + (fderiv ℝ g q.1 w') • e3 := by
      apply E3_ext <;> simp [hv, he3]
    rw [hdir, map_add, map_smul, smul_eq_mul] at hfsh
    have hFq : F (Sh q)
        = fderiv ℝ u (WithLp.toLp 2 (q.1, g q.1 + q.2)) v := rfl
    have hAq : A q = fderiv ℝ (shear g u) (WithLp.toLp 2 q)
        (WithLp.toLp 2 (w', 0)) := rfl
    have hBq : B q = fderiv ℝ g q.1 w'
        * fderiv ℝ u (WithLp.toLp 2 (q.1, g q.1 + q.2)) e3 := rfl
    rw [hFq, hAq, hBq]
    linarith [hfsh]
  -- integrability of the pieces
  have hAc : Continuous A :=
    (((contDiff_shear hg hu).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).comp (WithLp.prod_continuous_toLp 2 E2 ℝ)
  have hAcs : HasCompactSupport A :=
    (hasCompactSupport_fderiv_apply
      (hasCompactSupport_shear hg.continuous hcs) v).comp_homeomorph
      (WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ).toHomeomorph.symm
  have hAint : Integrable A (volume.prod volume) :=
    hAc.integrable_of_hasCompactSupport hAcs
  have hB2c : Continuous fun q : E2 × ℝ => fderiv ℝ u (WithLp.toLp 2 (Sh q)) e3 :=
    ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      ((WithLp.prod_continuous_toLp 2 E2 ℝ).comp hShcont)
  have hB2cs : HasCompactSupport fun q : E2 × ℝ => fderiv ℝ u (WithLp.toLp 2 (Sh q)) e3 := by
    have h := (hasCompactSupport_fderiv_apply hcs e3).comp_homeomorph
      ((shearHomeo hg.continuous).trans
        (WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ).toHomeomorph.symm)
    have hcoe2 : ⇑((shearHomeo hg.continuous).trans
          (WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ).toHomeomorph.symm)
        = fun q : E2 × ℝ => (WithLp.toLp 2 (Sh q) : E3) := rfl
    rw [hcoe2] at h
    exact h
  have hBc : Continuous B :=
    (((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      continuous_fst).mul hB2c
  have hBcs : HasCompactSupport B := hB2cs.mul_left
  have hBint : Integrable B (volume.prod volume) :=
    hBc.integrable_of_hasCompactSupport hBcs
  have hR₀ : MeasurableSet R₀ := measurableSet_lt measurable_snd measurable_const
  -- Step D: the shear term integrates to zero, slice by slice
  have hregion : R₀ = (univ : Set E2) ×ˢ Iio (0 : ℝ) := by
    ext q
    simp [hR₀def]
  have hDzero : ∫ q in R₀, A q ∂(volume.prod volume) = 0 := by
    rw [hregion, ← Measure.prod_restrict, Measure.restrict_univ]
    have hAint' : Integrable A (volume.prod (volume.restrict (Iio (0 : ℝ)))) := by
      have h := hAint.restrict (s := (univ : Set E2) ×ˢ Iio (0 : ℝ))
      rwa [← Measure.prod_restrict, Measure.restrict_univ] at h
    have hswap := integral_integral_swap (f := fun z s => A (z, s)) hAint'
    -- ∫ z ∫ s, A = ∫ s ∫ z, A ; inner z-integral vanishes for each s
    have hinner : ∀ s : ℝ, ∫ z : E2, A (z, s) = 0 := by
      intro s
      have hψC : ContDiff ℝ 1 fun z : E2 => shear g u (WithLp.toLp 2 (z, s)) :=
        (contDiff_shear hg hu).comp
          (contDiff_toLp_pair.comp (contDiff_id.prodMk contDiff_const))
      have hψcs : HasCompactSupport fun z : E2 => shear g u (WithLp.toLp 2 (z, s)) :=
        hasCompactSupport_slice_horiz
          (hasCompactSupport_shear hg.continuous hcs) s
      have hcongr : ∀ z : E2, A (z, s)
          = fderiv ℝ (fun z' : E2 => shear g u (WithLp.toLp 2 (z', s))) z w' := by
        intro z
        exact (fderiv_slice (contDiff_shear hg hu) s z w').symm
      rw [integral_congr_ae (ae_of_all _ hcongr)]
      exact integral_fderiv_eq_zero' hψC hψcs w'
    calc ∫ q, A q ∂(volume.prod (volume.restrict (Iio (0:ℝ))))
        = ∫ z, ∫ s, A (z, s) ∂(volume.restrict (Iio (0:ℝ))) :=
          integral_prod _ hAint'
      _ = ∫ s, (∫ z : E2, A (z, s)) ∂(volume.restrict (Iio (0:ℝ))) := hswap
      _ = 0 := by simp [hinner]
  -- Step E: the graph term via FTC
  have hEterm : ∫ q in R₀, B q ∂(volume.prod volume)
      = ∫ z : E2, u (graphMap g z) * fderiv ℝ g z w' := by
    rw [hregion, ← Measure.prod_restrict, Measure.restrict_univ]
    have hBint' : Integrable B (volume.prod (volume.restrict (Iio (0 : ℝ)))) := by
      have := hBint.restrict (s := univ ×ˢ Iio (0:ℝ))
      rwa [← Measure.prod_restrict, Measure.restrict_univ] at this
    rw [integral_prod _ hBint']
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show (∫ s in Iio (0:ℝ), B (z, s)) = u (graphMap g z) * fderiv ℝ g z w'
    -- inner: ∫ s in Iio 0, Dg·w' * ∂₃u(z, gz+s) = Dg·w' * u(z, g z)
    have hk : ∀ s : ℝ, fderiv ℝ u (WithLp.toLp 2 (z, g z + s)) e3
        = deriv (fun s' => u (WithLp.toLp 2 (z, g z + s'))) s := by
      intro s
      have hcurve := hasDerivAt_vertLine z (g z) s
      have hu'' : HasFDerivAt u (fderiv ℝ u (WithLp.toLp 2 (z, g z + s)))
          (WithLp.toLp 2 (z, g z + s)) :=
        ((hu.differentiable one_ne_zero) _).hasFDerivAt
      exact ((hu''.comp_hasDerivAt s hcurve).deriv).symm
    have hkC : ContDiff ℝ 1 fun s' : ℝ => u (WithLp.toLp 2 (z, g z + s')) :=
      hu.comp (contDiff_toLp_pair.comp
        (contDiff_const.prodMk (contDiff_const.add contDiff_id)))
    have hkcs : HasCompactSupport fun s' : ℝ => u (WithLp.toLp 2 (z, g z + s')) := by
      have h := (hasCompactSupport_slice_vert hcs z).comp_homeomorph
        (Homeomorph.addLeft (g z))
      exact h
    calc ∫ s in Iio (0:ℝ), B (z, s)
        = ∫ s in Iio (0:ℝ), fderiv ℝ g z w'
            * deriv (fun s' => u (WithLp.toLp 2 (z, g z + s'))) s := by
          refine setIntegral_congr_fun measurableSet_Iio fun s _ => ?_
          have hBzs : B (z, s)
              = fderiv ℝ g z w' * fderiv ℝ u (WithLp.toLp 2 (z, g z + s)) e3 := rfl
          rw [hBzs, hk s]
      _ = fderiv ℝ g z w'
            * ∫ s in Iio (0:ℝ), deriv (fun s' => u (WithLp.toLp 2 (z, g z + s'))) s :=
          integral_const_mul _ _
      _ = fderiv ℝ g z w' * u (graphMap g z) := by
          rw [setIntegral_congr_set Iio_ae_eq_Iic,
            HasCompactSupport.integral_Iic_deriv_eq hkC hkcs 0]
          simp only [add_zero]
          rfl
      _ = u (graphMap g z) * fderiv ℝ g z w' := mul_comm _ _
  -- assemble
  calc ∫ x in subgraphSet g, fderiv ℝ u x v
      = ∫ q in R₀, F (Sh q) ∂(volume.prod volume) := by rw [hstepA, hstepB]
    _ = ∫ q in R₀, (A q - B q) ∂(volume.prod volume) :=
        setIntegral_congr_fun hR₀ fun q _ => hsplit q
    _ = (∫ q in R₀, A q ∂(volume.prod volume))
          - ∫ q in R₀, B q ∂(volume.prod volume) :=
        integral_sub hAint.integrableOn hBint.integrableOn
    _ = -∫ z : E2, u (graphMap g z) * fderiv ℝ g z w' := by
        rw [hDzero, hEterm, zero_sub]

/-- **The flat divergence identity** (paper part 3, "In summary"):
combining the two directions,

    ∫_{Σ_g} Du·w = ∫_{ℝ²} u(z, g z) · (⟨ν_g z, w⟩ · J_g z) dz ,

since `⟨ν_g z, w⟩ · J_g z = ⟨(-∇g z, 1), w⟩` — the paper's "1 = a/a
trick" run in reverse. -/
theorem flat_divergence {g : E2 → ℝ} (hg : ContDiff ℝ 1 g) {u : E3 → ℝ}
    (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) (w : E3) :
    ∫ x in subgraphSet g, fderiv ℝ u x w
      = ∫ z : E2, u (graphMap g z) * (⟪unitNormal g z, w⟫ * jac g z) := by
  have hw : w = WithLp.toLp 2 (horiz w, 0) + vert w • WithLp.toLp 2 (0, 1) := by
    apply E3_ext <;> simp
  -- pointwise split of the direction
  have hptsplit : ∀ x : E3, fderiv ℝ u x w
      = fderiv ℝ u x (WithLp.toLp 2 (horiz w, 0))
        + vert w * fderiv ℝ u x (WithLp.toLp 2 (0, 1)) := by
    intro x
    conv_lhs => rw [hw]
    rw [map_add, map_smul, smul_eq_mul]
  -- integrand algebra on the right side
  have halg : ∀ z : E2, u (graphMap g z) * (⟪unitNormal g z, w⟫ * jac g z)
      = -(u (graphMap g z) * fderiv ℝ g z (horiz w))
        + vert w * u (graphMap g z) := by
    intro z
    have hJ : jac g z ≠ 0 := (jac_pos z).ne'
    have hinner : ⟪unitNormal g z, w⟫ * jac g z
        = -fderiv ℝ g z (horiz w) + vert w := by
      rw [inner_eq, horiz_unitNormal, vert_unitNormal, inner_neg_left,
        real_inner_smul_left, inner_gradient_eq]
      field_simp
    rw [hinner]
    ring
  -- integrability of the two directional pieces on the subgraph
  have hDh : Continuous fun x : E3 => fderiv ℝ u x (WithLp.toLp 2 (horiz w, 0)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDv : Continuous fun x : E3 => fderiv ℝ u x (WithLp.toLp 2 (0, 1)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have int1 : IntegrableOn (fun x => fderiv ℝ u x (WithLp.toLp 2 (horiz w, 0)))
      (subgraphSet g) volume :=
    (hDh.integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply hcs _)).integrableOn
  have int2 : IntegrableOn (fun x => vert w * fderiv ℝ u x (WithLp.toLp 2 (0, 1)))
      (subgraphSet g) volume :=
    ((hDv.integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply hcs _)).integrableOn).const_mul _
  -- integrability of the two graph pieces
  have hgu : Continuous fun z : E2 => u (graphMap g z) :=
    hu.continuous.comp (continuous_graphMap hg.continuous)
  have hgucs : HasCompactSupport fun z : E2 => u (graphMap g z) :=
    hasCompactSupport_comp_graphMap hcs g
  have intR1 : Integrable (fun z : E2 => u (graphMap g z) * fderiv ℝ g z (horiz w))
      volume :=
    (hgu.mul ((hg.continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).integrable_of_hasCompactSupport hgucs.mul_right
  have intR2 : Integrable (fun z : E2 => u (graphMap g z)) volume :=
    hgu.integrable_of_hasCompactSupport hgucs
  calc ∫ x in subgraphSet g, fderiv ℝ u x w
      = ∫ x in subgraphSet g,
          (fderiv ℝ u x (WithLp.toLp 2 (horiz w, 0))
            + vert w * fderiv ℝ u x (WithLp.toLp 2 (0, 1))) :=
        setIntegral_congr_fun (isOpen_subgraphSet hg.continuous).measurableSet
          fun x _ => hptsplit x
    _ = (∫ x in subgraphSet g, fderiv ℝ u x (WithLp.toLp 2 (horiz w, 0)))
          + ∫ x in subgraphSet g, vert w * fderiv ℝ u x (WithLp.toLp 2 (0, 1)) :=
        integral_add int1 int2
    _ = (-∫ z : E2, u (graphMap g z) * fderiv ℝ g z (horiz w))
          + vert w * ∫ z : E2, u (graphMap g z) := by
        rw [flat_horizontal hg hu hcs (horiz w), integral_const_mul,
          flat_vertical hg hu hcs]
    _ = ∫ z : E2, (-(u (graphMap g z) * fderiv ℝ g z (horiz w))
          + vert w * u (graphMap g z)) := by
        have h1 : Integrable
            (fun z : E2 => -(u (graphMap g z) * fderiv ℝ g z (horiz w)))
            volume := intR1.neg
        have h2 : Integrable (fun z : E2 => vert w * u (graphMap g z)) volume :=
          intR2.const_mul (vert w)
        rw [integral_add h1 h2, integral_neg, integral_const_mul]
    _ = ∫ z : E2, u (graphMap g z) * (⟪unitNormal g z, w⟫ * jac g z) :=
        integral_congr_ae (ae_of_all _ fun z => (halg z).symm)

/-! ### Localization and rigid-motion transport -/

/-- If `f` is supported inside the cylinder, integrating over the full
subgraph or over its cylinder part is the same (needed to pass between
`flat_divergence` and the chart-local statement in `Main`). -/
theorem setIntegral_subgraph_of_support {g : E2 → ℝ} (hgc : Continuous g)
    {r ht : ℝ} {f : E3 → ℝ} (hsupp : tsupport f ⊆ cylinder g r ht) :
    ∫ x in subgraphSet g ∩ cylinder g r ht, f x
      = ∫ x in subgraphSet g, f x := by
  have hfeq : ∀ x, f x = (cylinder g r ht).indicator f x := by
    intro x
    by_cases hx : x ∈ cylinder g r ht
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)]
  calc ∫ x in subgraphSet g ∩ cylinder g r ht, f x
      = ∫ x in subgraphSet g, (cylinder g r ht).indicator f x :=
        (setIntegral_indicator (isOpen_cylinder hgc r ht).measurableSet).symm
    _ = ∫ x in subgraphSet g, f x :=
        setIntegral_congr_fun (isOpen_subgraphSet hgc).measurableSet
          fun x _ => (hfeq x).symm

/-- The affine decomposition `T x = T₀ x + T 0` of a rigid motion. -/
private lemma rigid_decomp (T : E3 ≃ᵃⁱ[ℝ] E3) (x : E3) :
    T x = T.linearIsometryEquiv x + T 0 := by
  simpa [add_comm] using T.map_vadd 0 x

/-- Rigid motions preserve Lebesgue measure: the linear part by
`LinearIsometryEquiv.measurePreserving`, the translation part by
right-invariance of Haar measure. -/
theorem measurePreserving_rigidMotion (T : E3 ≃ᵃⁱ[ℝ] E3) :
    MeasurePreserving T volume volume := by
  have hdec : (T : E3 → E3) = fun x => T.linearIsometryEquiv x + T 0 :=
    funext fun x => rigid_decomp T x
  rw [hdec]
  exact (measurePreserving_add_right volume (T 0)).comp
    T.linearIsometryEquiv.measurePreserving

/-- Rigid motions preserve Lebesgue integrals over images
(paper's Lemma "Invariance of the Divergence Theorem under Rigid
Motions", volume half): `∫_{T(S)} f = ∫_S f ∘ T`. -/
theorem setIntegral_image_rigidMotion (T : E3 ≃ᵃⁱ[ℝ] E3) (S : Set E3)
    (f : E3 → ℝ) :
    ∫ x in T '' S, f x = ∫ y in S, f (T y) :=
  (measurePreserving_rigidMotion T).setIntegral_image_emb
    T.toHomeomorph.measurableEmbedding f S

/-- Chain rule under a rigid motion: `D(u ∘ T) y w = D u (T y) (T₀ w)`
with `T₀` the linear part (invariance lemma, derivative half). -/
theorem fderiv_comp_rigidMotion (T : E3 ≃ᵃⁱ[ℝ] E3) {u : E3 → ℝ}
    (hu : ContDiff ℝ 1 u) (y : E3) (w : E3) :
    fderiv ℝ (fun x => u (T x)) y w
      = fderiv ℝ u (T y) (T.linearIsometryEquiv w) := by
  have hT : HasFDerivAt (T : E3 → E3)
      (T.linearIsometryEquiv.toContinuousLinearEquiv : E3 →L[ℝ] E3) y := by
    have h := (T.linearIsometryEquiv.toContinuousLinearEquiv.hasFDerivAt
      (x := y)).add_const (T 0)
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    exact rigid_decomp T x
  have hu' : HasFDerivAt u (fderiv ℝ u (T y)) (T y) :=
    ((hu.differentiable one_ne_zero) _).hasFDerivAt
  have hcomp := hu'.comp y hT
  have hfd : fderiv ℝ (fun x => u (T x)) y
      = (fderiv ℝ u (T y)).comp
          (T.linearIsometryEquiv.toContinuousLinearEquiv : E3 →L[ℝ] E3) :=
    hcomp.fderiv
  rw [hfd]
  rfl

/-
# Step 2: chart cover, partition of unity, and the interior case
(paper proof step 2, §3.2)

Compactness of `∂Ω` gives finitely many cylinder charts `U₁, …, U_N`;
`{Ω, U₁, …, U_N}` covers `Ω̄`; a partition of unity subordinate to this
cover splits `u = Σ ψₖ u` into pieces supported either inside `Ω` or
inside one chart.  The interior pieces contribute `0` to both sides
(the vanishing-integral lemma from `Divergence.Cutoff` on the left,
`u = 0` near `∂Ω` on the right).

The partition comes from mathlib's `SmoothPartitionOfUnity` (ℝ³ is
T2 + σ-compact, modelled by `𝓘(ℝ, E3)`); compact supports come for free
because every element of the cover is bounded (`Ω` by hypothesis, the
chart cylinders because `g` is bounded on the closed disk). -/




variable {Ω : Set E3}

/-- Graph cylinders are bounded sets. -/
private lemma isBounded_cylinder {g : E2 → ℝ} (hg : Continuous g) (r ht : ℝ) :
    Bornology.IsBounded (cylinder g r ht) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E2) r).exists_bound_of_continuousOn
    hg.continuousOn
  refine (Metric.isBounded_closedBall (x := (0 : E3)) (r := r + (C + ht))).subset ?_
  rintro p ⟨h1, h2⟩
  have hb1 : ‖horiz p‖ ≤ r := h1.le
  have hgb : |g (horiz p)| ≤ C := by
    have h := hC (horiz p) (by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact hb1)
    simpa [Real.norm_eq_abs] using h
  have hb2 : |vert p| ≤ C + ht := by
    have h3 : |vert p| ≤ |vert p - g (horiz p)| + |g (horiz p)| := by
      have heq : vert p = vert p - g (horiz p) + g (horiz p) := by ring
      calc |vert p| = ‖vert p - g (horiz p) + g (horiz p)‖ := by
            rw [Real.norm_eq_abs, ← heq]
        _ ≤ ‖vert p - g (horiz p)‖ + ‖g (horiz p)‖ := norm_add_le _ _
        _ = |vert p - g (horiz p)| + |g (horiz p)| := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith [h2.le]
  simp only [Metric.mem_closedBall, dist_zero_right]
  have hp : ‖p‖ ≤ ‖horiz p‖ + |vert p| := by
    conv_lhs => rw [← toLp_horiz_vert p]
    exact norm_toLp_le _ _
  linarith

/-- Chart neighborhoods are bounded sets (isometric images of bounded
cylinders). -/
private lemma isBounded_chart_U (c : CylinderChart Ω) :
    Bornology.IsBounded c.U :=
  (c.T.isometry.lipschitz.isBounded_image
    (isBounded_cylinder c.hg.continuous c.r c.ht))

/-- Finitely many cylinder charts cover the compact boundary
(paper: "Since ∂Ω is compact, we can cover ∂Ω with finitely many
neighborhoods U₁, …, U_N of the above form"). -/
theorem exists_finite_chart_cover (hb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) :
    ∃ (N : ℕ) (c : Fin N → CylinderChart Ω),
      frontier Ω ⊆ ⋃ i, (c i).U := by
  choose ch hch using fun x : frontier Ω => hC1 x x.2
  obtain ⟨t, ht⟩ := (isCompact_frontier hb).elim_finite_subcover
    (fun x : frontier Ω => (ch x).U) (fun x => (ch x).isOpen_U)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hch ⟨x, hx⟩⟩)
  refine ⟨t.card, fun i => ch (t.equivFin.symm i).1, fun x hx => ?_⟩
  obtain ⟨y, hyt, hyU⟩ := Set.mem_iUnion₂.mp (ht hx)
  refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
  simpa [Equiv.symm_apply_apply] using hyU

/-- **Partition of unity** (paper's Rudin 10.8, specialized): `C¹`
functions `ψ₀, …, ψ_N`, each compactly supported in one element of the
cover `{Ω, U₁, …, U_N}` (index `0` ↦ `Ω`, index `i.succ` ↦ `Uᵢ`),
with `Σ ψₖ = 1` on `Ω̄` and `0 ≤ ψₖ ≤ 1`.  Compact supports follow
from subordination since every element of the cover is bounded. -/
theorem exists_partition_of_unity (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {N : ℕ} (c : Fin N → CylinderChart Ω)
    (hcover : frontier Ω ⊆ ⋃ i, (c i).U) :
    ∃ ψ : Fin (N + 1) → E3 → ℝ,
      (∀ k, ContDiff ℝ 1 (ψ k)) ∧
      (∀ k, HasCompactSupport (ψ k)) ∧
      (∀ k x, ψ k x ∈ Icc (0 : ℝ) 1) ∧
      tsupport (ψ 0) ⊆ Ω ∧
      (∀ i : Fin N, tsupport (ψ i.succ) ⊆ (c i).U) ∧
      EqOn (fun x => ∑ k, ψ k x) 1 (closure Ω) := by
  set U : Fin (N + 1) → Set E3 := Fin.cons Ω (fun i => (c i).U) with hUdef
  have hUopen : ∀ k, IsOpen (U k) := by
    refine Fin.cases ?_ ?_
    · simpa [hUdef] using hΩ
    · intro i
      simpa [hUdef] using (c i).isOpen_U
  have hUbounded : ∀ k, Bornology.IsBounded (U k) := by
    refine Fin.cases ?_ ?_
    · simpa [hUdef] using hb
    · intro i
      simpa [hUdef] using isBounded_chart_U (c i)
  have hUcover : closure Ω ⊆ ⋃ k, U k := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · exact Set.mem_iUnion.mpr ⟨0, by simpa [hUdef] using hxΩ⟩
    · have hxf : x ∈ frontier Ω := hΩ.frontier_eq ▸ ⟨hx, hxΩ⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hxf)
      exact Set.mem_iUnion.mpr ⟨i.succ, by simpa [hUdef] using hi⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E3)
    isClosed_closure U hUopen hUcover
  refine ⟨fun k => f k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (contMDiff_iff_contDiff.mp (f k).contMDiff).of_le
      (by exact_mod_cast le_top)
  · intro k
    exact Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
      ((hUbounded k).subset (hf k))
  · exact fun k x => ⟨f.nonneg k x, f.le_one k x⟩
  · simpa [hUdef] using hf 0
  · intro i
    simpa [hUdef] using hf i.succ
  · intro x hx
    have h := f.sum_eq_one hx
    rw [finsum_eq_sum_of_fintype] at h
    simpa using h

/-! ### The interior case (paper part 2, "compact support in Ω") -/

/-- **Partial FTC** (paper's Lemma "Partial FTC for Compactly Supported
C¹ Functions", total form on ℝ³): a compactly supported `C¹` function
has vanishing total directional-derivative integral.  Specializes the
cutoff-and-integrate-by-parts lemma from `Divergence.Cutoff`. -/
theorem integral_fderiv_eq_zero {u : E3 → ℝ} (hu : ContDiff ℝ 1 u)
    (hcs : HasCompactSupport u) (w : E3) :
    ∫ x, fderiv ℝ u x w = 0 :=
  integral_fderiv_eq_zero' hu hcs w

/-- Interior case, left side: `∫_Ω Du·w = ∫_{ℝ³} Du·w = 0`
(paper part 2, first display). -/
theorem divergence_interior_case (hΩ : IsOpen Ω) {u : E3 → ℝ}
    (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u)
    (hsupp : tsupport u ⊆ Ω) (w : E3) :
    ∫ x in Ω, fderiv ℝ u x w = 0 := by
  have hout : ∀ x ∉ Ω, fderiv ℝ u x w = 0 := by
    intro x hx
    rw [fderiv_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)]
    rfl
  have hext : ∫ x in Ω, fderiv ℝ u x w = ∫ x, fderiv ℝ u x w := by
    rw [← integral_indicator hΩ.measurableSet]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ Ω
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, hout x hx]
  rw [hext]
  exact integral_fderiv_eq_zero hu hcs w

/-- Interior case, right side: `u` vanishes on `∂Ω`, so the boundary
integral vanishes (paper part 2, last display). -/
theorem boundary_integral_interior_case (hΩ : IsOpen Ω) {u : E3 → ℝ}
    (hsupp : tsupport u ⊆ Ω) (ν : E3 → E3) (w : E3) :
    ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[2] = 0 := by
  have hzero : ∀ x ∈ frontier Ω, u x * ⟪ν x, w⟫ = 0 := by
    intro x hx
    have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      (hΩ.frontier_eq ▸ hx).2 (hsupp h)
    rw [hu0, zero_mul]
  calc ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[2]
      = ∫ _ in frontier Ω, (0 : ℝ) ∂μHE[2] :=
        setIntegral_congr_fun isClosed_frontier.measurableSet hzero
    _ = 0 := by simp

/-
# The surface integral: from `μHE[2]` on `∂Ω` to parameterized integrals
(paper §2.3, §3.3 Steps 4–8, and the Lemma "Surface Element on a Graph")

The boundary integral `∫_{∂Ω} f dS` is interpreted against Mathlib's
Euclidean 2-dimensional Hausdorff measure `μHE[2]` restricted to
`frontier Ω` — the canonical, chart-free surface measure.  This file
connects it to the concrete parameterized form the paper computes with:

    ∫_{graph g V} f dμHE[2]  =  ∫_V f(z, g z) √(1+|∇g|²) dz .

**This is where the completed GraphArea project is loaded**: its
`area_formula` (`μHE[2](Γ_g|_U) = ∫_U jac g`), applied to every open
set, upgrades by π-system uniqueness to the pushforward identity
`restrict_graph_eq_map`, and the weighted integral formula follows via
`MeasureTheory.integral_map`.

Hypothesis convention: `g` is globally `C¹` and `V` is bounded — this
matches the cylinder charts (whose `g` is global and whose base is a
disk) and keeps both measures finite, so the π-system argument needs no
exhaustion.
-/




/-- Global continuity of the Jacobian factor of a `C¹` function. -/
lemma continuous_jac {g : E2 → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (jac g) := by
  have h : Continuous fun z => Real.sqrt (1 + ‖fderiv ℝ g z‖ ^ 2) :=
    Real.continuous_sqrt.comp
      (continuous_const.add ((hg.continuous_fderiv one_ne_zero).norm.pow 2))
  exact h

/-- The graph of a globally `C¹` function over a bounded set has finite
area (the Jacobian is bounded on the closure). -/
lemma graph_measure_lt_top {V : Set E2} {g : E2 → ℝ} (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) (hg : ContDiff ℝ 1 g) :
    μHE[2] (graph g V) < ∞ := by
  obtain ⟨C, hC⟩ := hVb.isCompact_closure.exists_bound_of_continuousOn
    (continuous_jac hg).continuousOn
  have hvol : volume V < ∞ :=
    lt_of_le_of_lt (measure_mono subset_closure) hVb.isCompact_closure.measure_lt_top
  calc μHE[2] (graph g V)
      = ∫⁻ z in V, ENNReal.ofReal (jac g z) := area_formula hV hg.contDiffOn
    _ ≤ ∫⁻ _ in V, ENNReal.ofReal C := by
        refine setLIntegral_mono measurable_const fun z hz => ?_
        exact ENNReal.ofReal_le_ofReal (by
          have := hC z (subset_closure hz)
          rwa [Real.norm_eq_abs, abs_of_pos (jac_pos z)] at this)
    _ = ENNReal.ofReal C * volume V := by rw [setLIntegral_const]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol

/-- **Weighted area formula** (the surface-element lemma, measure
form): on the graph of a `C¹` function over a bounded open base,
`μHE[2]` is the pushforward of the Jacobian-weighted Lebesgue measure.
Strengthens `GraphArea.area_formula` from a single measure identity to
a pushforward identity, by applying it to every open set and invoking
π-system uniqueness. -/
theorem restrict_graph_eq_map {V : Set E2} {g : E2 → ℝ} (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) (hg : ContDiff ℝ 1 g) :
    μHE[2].restrict (graph g V)
      = Measure.map (graphMap g)
          ((volume.restrict V).withDensity fun z => ENNReal.ofReal (jac g z)) := by
  have hΦcont : Continuous (graphMap g) := continuous_graphMap hg.continuous
  -- agreement on every open set, via the area formula
  have h_eq : ∀ O : Set E3, IsOpen O →
      μHE[2].restrict (graph g V) O
        = Measure.map (graphMap g)
            ((volume.restrict V).withDensity fun z => ENNReal.ofReal (jac g z)) O := by
    intro O hO
    have hpre : IsOpen (V ∩ graphMap g ⁻¹' O) := hV.inter (hO.preimage hΦcont)
    have himg : O ∩ graph g V = graph g (V ∩ graphMap g ⁻¹' O) := by
      show O ∩ graphMap g '' V = graphMap g '' (V ∩ graphMap g ⁻¹' O)
      rw [Set.image_inter_preimage, Set.inter_comm]
    calc μHE[2].restrict (graph g V) O
        = μHE[2] (O ∩ graph g V) := Measure.restrict_apply hO.measurableSet
      _ = μHE[2] (graph g (V ∩ graphMap g ⁻¹' O)) := by rw [himg]
      _ = ∫⁻ z in V ∩ graphMap g ⁻¹' O, ENNReal.ofReal (jac g z) :=
          area_formula hpre hg.contDiffOn
      _ = ∫⁻ z in graphMap g ⁻¹' O ∩ V, ENNReal.ofReal (jac g z) := by
          rw [Set.inter_comm]
      _ = ∫⁻ z in graphMap g ⁻¹' O, ENNReal.ofReal (jac g z) ∂(volume.restrict V) := by
          rw [Measure.restrict_restrict (hO.preimage hΦcont).measurableSet]
      _ = ((volume.restrict V).withDensity fun z => ENNReal.ofReal (jac g z))
            (graphMap g ⁻¹' O) :=
          (withDensity_apply _ (hO.preimage hΦcont).measurableSet).symm
      _ = Measure.map (graphMap g)
            ((volume.restrict V).withDensity fun z => ENNReal.ofReal (jac g z)) O :=
          (Measure.map_apply hΦcont.measurable hO.measurableSet).symm
  -- π-system extension
  refine Measure.ext_of_generateFrom_of_iUnion {s : Set E3 | IsOpen s}
    (fun _ => univ) BorelSpace.measurable_eq ?_ ?_ ?_ ?_ ?_
  · rintro s (hs : IsOpen s) t (ht : IsOpen t) -
    exact hs.inter ht
  · exact Set.iUnion_const _
  · intro i
    show IsOpen (univ : Set E3)
    exact isOpen_univ
  · intro _
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact (graph_measure_lt_top hV hVb hg).ne
  · exact fun s hs => h_eq s hs

/-- **Surface integral over a graph patch** (paper §3.3 Step 5, the
definition the paper takes; here it is a theorem about `μHE[2]`):
`∫_{Γ_g|_V} F dμHE[2] = ∫_V F(z, g z) · J_g z dz`. -/
theorem integral_graph {V : Set E2} {g : E2 → ℝ} (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) (hg : ContDiff ℝ 1 g) {F : E3 → ℝ}
    (hF : Continuous F) :
    ∫ x in graph g V, F x ∂μHE[2]
      = ∫ z in V, F (graphMap g z) * jac g z := by
  have hΦcont : Continuous (graphMap g) := continuous_graphMap hg.continuous
  rw [show (∫ x in graph g V, F x ∂μHE[2])
      = ∫ x, F x ∂(μHE[2].restrict (graph g V)) from rfl,
    restrict_graph_eq_map hV hVb hg,
    integral_map hΦcont.measurable.aemeasurable hF.aestronglyMeasurable]
  have hdens : (fun z : E2 => ENNReal.ofReal (jac g z))
      = fun z : E2 => ((Real.toNNReal (jac g z) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hdens, integral_withDensity_eq_integral_smul
    ((continuous_jac hg).measurable.real_toNNReal) fun z => F (graphMap g z)]
  refine setIntegral_congr_fun hV.measurableSet fun z _ => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (jac_pos z).le, smul_eq_mul, mul_comm]

/-- Rigid motions preserve `μHE[2]` (mathlib's
`Isometry.euclideanHausdorffMeasure_image` applied to the inverse). -/
theorem measurePreserving_rigidMotion_muHE (T : E3 ≃ᵃⁱ[ℝ] E3) :
    MeasurePreserving T (μHE[2] : Measure E3) μHE[2] := by
  have hm : Measurable (T : E3 → E3) := T.isometry.continuous.measurable
  refine ⟨hm, ?_⟩
  ext A hA
  rw [Measure.map_apply hm hA]
  have hpre : (T : E3 → E3) ⁻¹' A = T.symm '' A := by
    ext x
    constructor
    · intro hx
      exact ⟨T x, hx, T.symm_apply_apply x⟩
    · rintro ⟨a, ha, rfl⟩
      simpa [T.apply_symm_apply] using ha
  rw [hpre]
  exact T.symm.isometry.euclideanHausdorffMeasure_image A

/-- Rigid motions preserve `μHE[2]`-integrals over images (invariance
lemma, surface half). -/
theorem surfaceIntegral_image_rigidMotion (T : E3 ≃ᵃⁱ[ℝ] E3) (S : Set E3)
    (f : E3 → ℝ) :
    ∫ x in T '' S, f x ∂μHE[2] = ∫ y in S, f (T y) ∂μHE[2] :=
  (measurePreserving_rigidMotion_muHE T).setIntegral_image_emb
    T.toHomeomorph.measurableEmbedding f S

/-- **Chart-local surface integral** (paper §3.3 Steps 6–8): for `F`
supported inside a chart `c`, the boundary integral is the
parameterized integral over the disk.  Combines `frontier_inter_U`
(the boundary piece is the moved graph), rigid-motion invariance of
`μHE[2]`, and `integral_graph`. -/
theorem surface_integral_chart {Ω : Set E3} (hΩ : IsOpen Ω)
    (c : CylinderChart Ω) {F : E3 → ℝ} (hF : Continuous F)
    (hsupp : tsupport F ⊆ c.U) :
    ∫ x in frontier Ω, F x ∂μHE[2]
      = ∫ z in Metric.ball (0 : E2) c.r,
          F (c.T (graphMap c.g z)) * jac c.g z := by
  have hfeq : ∀ x, F x = (c.U).indicator F x := by
    intro x
    by_cases hx : x ∈ c.U
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)]
  have hsplit : ∫ x in frontier Ω, F x ∂μHE[2]
      = ∫ x in frontier Ω ∩ c.U, F x ∂μHE[2] := by
    calc ∫ x in frontier Ω, F x ∂μHE[2]
        = ∫ x in frontier Ω, (c.U).indicator F x ∂μHE[2] :=
          setIntegral_congr_fun isClosed_frontier.measurableSet
            fun x _ => hfeq x
      _ = ∫ x in frontier Ω ∩ c.U, F x ∂μHE[2] :=
          setIntegral_indicator c.isOpen_U.measurableSet
  have hFT : Continuous fun y : E3 => F (c.T y) :=
    hF.comp c.T.isometry.continuous
  rw [hsplit, c.frontier_inter_U hΩ,
    surfaceIntegral_image_rigidMotion c.T (graph c.g (Metric.ball (0 : E2) c.r)) F,
    integral_graph Metric.isOpen_ball Metric.isBounded_ball c.hg hFT]

/-
# The divergence theorem (paper Theorem + §3.3 Step 9, "Propagate back")

Assembly, following the paper's three reductions in reverse:

* `divergence_chart_case` — `u` compactly supported in one chart
  (Reduction A, second case): transport `flat_divergence` through the
  rigid motion and identify the right side by `surface_integral_chart`;
  the normal field agrees with the chart normal by the uniqueness
  theorem `IsOutwardNormalAt.eq_chart_normal`.
* `divergence_compact_support` — arbitrary `u ∈ C¹_c(ℝ³)`
  (Reduction B): split `u = Σ ψₖ u` by the partition of unity;
  the interior piece contributes zero to both sides.
* `divergence_theorem` — the paper's Theorem, `u ∈ C¹(O)`,
  `O ⊇ Ω̄` open (Reduction C): cut off by `φ`.
* `divergence_theorem_vector_field` — the classical `div`/flux form,
  by summing the scalar theorem over an orthonormal basis.

Statement conventions: `Ω ⊆ ℝ³` open, bounded, with C¹ boundary; the
volume integral is Lebesgue (`volume` on `E3`), the surface integral is
against `μHE[2]` restricted to `frontier Ω`; `ν` is any outward unit
normal field in the geometric sense (`IsOutwardNormal`); the scalar
theorem is stated directionally (`w ∈ ℝ³` arbitrary), which is the
paper's "equivalently, ∫ ∇u = ∫ u ν" form all at once.
-/




variable {Ω : Set E3}

/-! ### Infrastructure: the finite surface measure and integrability of
normal-field integrands on the boundary -/

/-- A bounded C¹ boundary has finite area: finitely many chart patches,
each an isometric image of a graph over a disk. -/
theorem measure_frontier_lt_top (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) : μHE[2] (frontier Ω) < ∞ := by
  obtain ⟨N, c, hcover⟩ := exists_finite_chart_cover hb hC1
  calc μHE[2] (frontier Ω)
      ≤ μHE[2] (⋃ i, frontier Ω ∩ (c i).U) := by
        refine measure_mono fun x hx => ?_
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
        exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
    _ ≤ ∑ i, μHE[2] (frontier Ω ∩ (c i).U) := measure_iUnion_fintype_le _ _
    _ < ∞ := by
        refine ENNReal.sum_lt_top.mpr fun i _ => ?_
        rw [(c i).frontier_inter_U hΩ,
          (c i).T.isometry.euclideanHausdorffMeasure_image]
        exact graph_measure_lt_top Metric.isOpen_ball Metric.isBounded_ball (c i).hg

/-- The graph normal, read back through the chart — a globally defined
*continuous* stand-in for the outward normal field on the chart patch. -/
private def chartNormalField (c : CylinderChart Ω) : E3 → E3 :=
  fun x => c.T.linearIsometryEquiv (unitNormal c.g (horiz (c.T.symm x)))

private lemma continuous_unitNormal {g : E2 → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous fun z => unitNormal g z := by
  have hgrad : Continuous fun z => gradient g z := by
    have h1 : Continuous fun z => fderiv ℝ g z := hg.continuous_fderiv one_ne_zero
    exact (InnerProductSpace.toDual ℝ E2).symm.continuous.comp h1
  have hjac : Continuous fun z => (jac g z)⁻¹ :=
    (continuous_jac hg).inv₀ fun z => (jac_pos z).ne'
  exact hjac.smul ((WithLp.prod_continuous_toLp 2 E2 ℝ).comp
    (hgrad.neg.prodMk continuous_const))

private lemma continuous_chartNormalField (c : CylinderChart Ω) :
    Continuous (chartNormalField c) :=
  c.T.linearIsometryEquiv.continuous.comp
    ((continuous_unitNormal c.hg).comp
      (continuous_horiz.comp c.T.symm.isometry.continuous))

/-- For `f` supported inside a chart, the true normal integrand agrees
with the continuous chart surrogate on the *whole* frontier: on the
patch by uniqueness of the outward normal, off the patch both vanish. -/
private lemma frontier_integrand_eq (hΩ : IsOpen Ω) (c : CylinderChart Ω)
    {f : E3 → ℝ} (hsupp : tsupport f ⊆ c.U) {ν : E3 → E3}
    (hν : IsOutwardNormal Ω ν) (w : E3) :
    ∀ x ∈ frontier Ω, f x * ⟪ν x, w⟫ = f x * ⟪chartNormalField c x, w⟫ := by
  intro x hx
  by_cases hxU : x ∈ c.U
  · have hmem : x ∈ frontier Ω ∩ c.U := ⟨hx, hxU⟩
    rw [c.frontier_inter_U hΩ] at hmem
    obtain ⟨p, hp, rfl⟩ := hmem
    obtain ⟨z, hz, rfl⟩ := hp
    rw [(hν _ hx).eq_chart_normal c hz]
    have hcf : chartNormalField c (c.T (graphMap c.g z))
        = c.T.linearIsometryEquiv (unitNormal c.g z) := by
      rw [chartNormalField, c.T.symm_apply_apply]
      simp
    rw [hcf]
  · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxU (hsupp h)
    rw [hf0, zero_mul, zero_mul]

/-- Chart-supported normal-field integrands are integrable on the
boundary (they agree with a continuous function there, and the surface
measure is finite). -/
private lemma integrableOn_frontier_piece (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    (c : CylinderChart Ω) {f : E3 → ℝ} (hf : Continuous f)
    (hsupp : tsupport f ⊆ c.U) {ν : E3 → E3} (hν : IsOutwardNormal Ω ν)
    (w : E3) :
    IntegrableOn (fun x => f x * ⟪ν x, w⟫) (frontier Ω) μHE[2] := by
  have hcont : Continuous fun x => f x * ⟪chartNormalField c x, w⟫ :=
    hf.mul ((continuous_chartNormalField c).inner continuous_const)
  haveI : IsFiniteMeasure (μHE[2].restrict (frontier Ω)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_frontier_lt_top hΩ hb hC1
  obtain ⟨C, hC⟩ := (isCompact_frontier hb).exists_bound_of_continuousOn
    hcont.continuousOn
  have hint : IntegrableOn (fun x => f x * ⟪chartNormalField c x, w⟫)
      (frontier Ω) μHE[2] := by
    refine (integrable_const C).mono' hcont.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem isClosed_frontier.measurableSet fun x hx => by
      simpa using hC x hx
  exact hint.congr_fun (fun x hx => (frontier_integrand_eq hΩ c hsupp hν w x hx).symm)
    isClosed_frontier.measurableSet

/-- Any continuous coefficient times a normal-field inner product is
integrable on the boundary: split by a partition of unity so each piece
is chart-supported. -/
private lemma integrableOn_frontier_inner (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {f : E3 → ℝ}
    (hf : Continuous f) {ν : E3 → E3} (hν : IsOutwardNormal Ω ν) (w : E3) :
    IntegrableOn (fun x => f x * ⟪ν x, w⟫) (frontier Ω) μHE[2] := by
  obtain ⟨N, c, hcover⟩ := exists_finite_chart_cover hb hC1
  obtain ⟨ψ, hψC, -, -, hψ0, hψsucc, hψsum⟩ :=
    exists_partition_of_unity hΩ hb c hcover
  have hpieces : ∀ k : Fin (N + 1),
      IntegrableOn (fun x => ψ k x * f x * ⟪ν x, w⟫) (frontier Ω) μHE[2] := by
    refine Fin.cases ?_ ?_
    · refine (integrableOn_zero.congr_fun (fun x hx => ?_)
        isClosed_frontier.measurableSet)
      have hψ00 : ψ 0 x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
        (hΩ.frontier_eq ▸ hx).2 (hψ0 h)
      simp [hψ00]
    · intro i
      have h := integrableOn_frontier_piece hΩ hb hC1 (c i)
        ((hψC i.succ).continuous.mul hf)
        (subset_trans tsupport_mul_subset_left (hψsucc i)) hν w
      exact h.congr_fun (fun x _ => by simp only [Pi.mul_apply])
        isClosed_frontier.measurableSet
  have hsum : IntegrableOn (fun x => ∑ k, ψ k x * f x * ⟪ν x, w⟫)
      (frontier Ω) μHE[2] :=
    integrable_finset_sum (Finset.univ : Finset (Fin (N + 1))) fun k _ => hpieces k
  refine IntegrableOn.congr_fun hsum (fun x hx => ?_) isClosed_frontier.measurableSet
  have h1 : (∑ k, ψ k x) = 1 := hψsum (frontier_subset_closure hx)
  calc (∑ k, ψ k x * f x * ⟪ν x, w⟫)
      = (∑ k, ψ k x) * (f x * ⟪ν x, w⟫) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = f x * ⟪ν x, w⟫ := by rw [h1, one_mul]

/-- The set integral over `A` localizes to `A ∩ O` when the integrand is
supported in `O`. -/
private lemma setIntegral_inter_of_tsupport {A O : Set E3} {μ : Measure E3}
    (hO : MeasurableSet O) {f : E3 → ℝ} (hsupp : tsupport f ⊆ O) :
    ∫ x in A, f x ∂μ = ∫ x in A ∩ O, f x ∂μ := by
  have hfeq : ∀ x, f x = O.indicator f x := by
    intro x
    by_cases hx : x ∈ O
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)]
  calc ∫ x in A, f x ∂μ
      = ∫ x in A, O.indicator f x ∂μ :=
        integral_congr_ae (ae_of_all _ fun x => hfeq x)
    _ = ∫ x in A ∩ O, f x ∂μ := setIntegral_indicator hO

/-! ### The three reductions, in reverse -/

/-- **Chart case** (paper Reduction A, chart half; §3.3 Steps 1–8):
the divergence identity for `u` compactly supported inside one cylinder
chart. -/
theorem divergence_chart_case (hΩ : IsOpen Ω) (c : CylinderChart Ω)
    {u : E3 → ℝ} (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u)
    (hsupp : tsupport u ⊆ c.U)
    {ν : E3 → E3} (hν : IsOutwardNormal Ω ν) (w : E3) :
    ∫ x in Ω, fderiv ℝ u x w
      = ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[2] := by
  set T₀ := c.T.linearIsometryEquiv with hT₀
  set w₀ : E3 := T₀.symm w with hw₀
  set u' : E3 → ℝ := fun y => u (c.T y) with hu'def
  -- regularity of the pulled-back function
  have hTC : ContDiff ℝ 1 (c.T : E3 → E3) := by
    have hdec : (c.T : E3 → E3) = fun x => T₀ x + c.T 0 := funext fun x => by
      simpa [add_comm] using c.T.map_vadd 0 x
    rw [hdec]
    have h1 : ContDiff ℝ 1 fun x : E3 => T₀ x :=
      T₀.toContinuousLinearEquiv.contDiff
    exact h1.add contDiff_const
  have hu'C : ContDiff ℝ 1 u' := hu.comp hTC
  have hu'cs : HasCompactSupport u' := by
    have h := hcs.comp_homeomorph c.T.toHomeomorph
    exact h
  have hu'supp : tsupport u' ⊆ cylinder c.g c.r c.ht := by
    have hsub : tsupport u' ⊆ (c.T : E3 → E3) ⁻¹' tsupport u := by
      refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport u).preimage
        c.T.isometry.continuous)
      exact subset_closure hx
    refine hsub.trans ?_
    rw [show cylinder c.g c.r c.ht = (c.T : E3 → E3) ⁻¹' c.U from
      (Set.preimage_image_eq _ c.T.injective).symm]
    exact Set.preimage_mono hsupp
  -- the derivative direction, pulled back
  have hDpull : ∀ y, fderiv ℝ u (c.T y) w = fderiv ℝ u' y w₀ := by
    intro y
    rw [fderiv_comp_rigidMotion c.T hu y w₀, hw₀, ← hT₀,
      T₀.apply_symm_apply]
  -- the derivative's support
  have hDsupp : tsupport (fun y => fderiv ℝ u' y w₀) ⊆ cylinder c.g c.r c.ht := by
    refine subset_trans (closure_minimal (fun x hx => ?_) (isClosed_tsupport u'))
      hu'supp
    by_contra hxs
    refine hx ?_
    show fderiv ℝ u' x w₀ = 0
    rw [fderiv_eq_zero_of_notMem_tsupport hxs]
    rfl
  -- LHS: transport to the flat picture
  have hLHS : ∫ x in Ω, fderiv ℝ u x w
      = ∫ z : E2, u' (graphMap c.g z) * (⟪unitNormal c.g z, w₀⟫ * jac c.g z) := by
    have hDusupp : tsupport (fun x => fderiv ℝ u x w) ⊆ c.U := by
      refine subset_trans (closure_minimal (fun x hx => ?_) (isClosed_tsupport u))
        hsupp
      by_contra hxs
      refine hx ?_
      show fderiv ℝ u x w = 0
      rw [fderiv_eq_zero_of_notMem_tsupport hxs]
      rfl
    calc ∫ x in Ω, fderiv ℝ u x w
        = ∫ x in Ω ∩ c.U, fderiv ℝ u x w :=
          setIntegral_inter_of_tsupport c.isOpen_U.measurableSet hDusupp
      _ = ∫ x in c.T '' (subgraphSet c.g ∩ cylinder c.g c.r c.ht),
            fderiv ℝ u x w := by rw [c.inter_U hΩ]
      _ = ∫ y in subgraphSet c.g ∩ cylinder c.g c.r c.ht,
            fderiv ℝ u (c.T y) w := setIntegral_image_rigidMotion _ _ _
      _ = ∫ y in subgraphSet c.g ∩ cylinder c.g c.r c.ht,
            fderiv ℝ u' y w₀ :=
          setIntegral_congr_fun
            (((isOpen_subgraphSet c.hg.continuous).inter
              (isOpen_cylinder c.hg.continuous _ _)).measurableSet)
            fun y _ => hDpull y
      _ = ∫ y in subgraphSet c.g, fderiv ℝ u' y w₀ :=
          setIntegral_subgraph_of_support c.hg.continuous hDsupp
      _ = ∫ z : E2, u' (graphMap c.g z) * (⟪unitNormal c.g z, w₀⟫ * jac c.g z) :=
          flat_divergence c.hg hu'C hu'cs w₀
  -- RHS: replace ν by the chart surrogate, localize, parameterize
  set Fc : E3 → ℝ := fun x => u x * ⟪chartNormalField c x, w⟫ with hFc
  have hFccont : Continuous Fc :=
    hu.continuous.mul ((continuous_chartNormalField c).inner continuous_const)
  have hFcsupp : tsupport Fc ⊆ c.U := by
    refine subset_trans (closure_minimal (fun x hx => ?_) (isClosed_tsupport u))
      hsupp
    by_contra hxs
    refine hx ?_
    show u x * ⟪chartNormalField c x, w⟫ = 0
    rw [image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  have hRHS : ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[2]
      = ∫ z : E2, u' (graphMap c.g z) * (⟪unitNormal c.g z, w₀⟫ * jac c.g z) := by
    calc ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[2]
        = ∫ x in frontier Ω, Fc x ∂μHE[2] :=
          setIntegral_congr_fun isClosed_frontier.measurableSet
            (frontier_integrand_eq hΩ c hsupp hν w)
      _ = ∫ z in Metric.ball (0 : E2) c.r, Fc (c.T (graphMap c.g z)) * jac c.g z :=
          surface_integral_chart hΩ c hFccont hFcsupp
      _ = ∫ z in Metric.ball (0 : E2) c.r,
            u' (graphMap c.g z) * (⟪unitNormal c.g z, w₀⟫ * jac c.g z) := by
          refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet
            fun z _ => ?_
          have hcf : chartNormalField c (c.T (graphMap c.g z))
              = T₀ (unitNormal c.g z) := by
            rw [chartNormalField, c.T.symm_apply_apply]
            simp [hT₀]
          have hinner : ⟪T₀ (unitNormal c.g z), w⟫ = ⟪unitNormal c.g z, w₀⟫ := by
            conv_lhs => rw [show w = T₀ w₀ by rw [hw₀]; exact (T₀.apply_symm_apply w).symm]
            exact T₀.inner_map_map _ _
          rw [hFc]
          simp only
          rw [hcf, hinner]
          ring
      _ = ∫ z : E2, u' (graphMap c.g z) * (⟪unitNormal c.g z, w₀⟫ * jac c.g z) := by
          -- the integrand is supported in the disk
          have hzero : ∀ z ∉ Metric.ball (0 : E2) c.r,
              u' (graphMap c.g z) * (⟪unitNormal c.g z, w₀⟫ * jac c.g z) = 0 := by
            intro z hz
            have hu'0 : u' (graphMap c.g z) = 0 := by
              refine image_eq_zero_of_notMem_tsupport fun h => hz ?_
              have := hu'supp h
              simpa [mem_ball_zero_iff] using this.1
            rw [hu'0, zero_mul]
          rw [← integral_indicator Metric.isOpen_ball.measurableSet]
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          by_cases hz : z ∈ Metric.ball (0 : E2) c.r
          · simp [Set.indicator_of_mem hz]
          · rw [Set.indicator_of_notMem hz]
            exact (hzero z hz).symm
  rw [hLHS, hRHS]

/-- **Globally C¹ case** (paper Reduction B, slightly stronger: the
partition pieces provide their own compact supports, so `u ∈ C¹(ℝ³)`
suffices — no global compact support needed): the divergence identity
for globally `C¹` functions. -/
theorem divergence_compact_support (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    {u : E3 → ℝ} (hu : ContDiff ℝ 1 u)
    {ν : E3 → E3} (hν : IsOutwardNormal Ω ν) (w : E3) :
    ∫ x in Ω, fderiv ℝ u x w
      = ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[2] := by
  obtain ⟨N, c, hcover⟩ := exists_finite_chart_cover hb hC1
  obtain ⟨ψ, hψC, hψcs, -, hψ0, hψsucc, hψsum⟩ :=
    exists_partition_of_unity hΩ hb c hcover
  set v : Fin (N + 1) → E3 → ℝ := fun k x => ψ k x * u x with hv
  have hvC : ∀ k, ContDiff ℝ 1 (v k) := fun k => (hψC k).mul hu
  have hvcs : ∀ k, HasCompactSupport (v k) := fun k => (hψcs k).mul_right
  have hvsupp0 : tsupport (v 0) ⊆ Ω :=
    subset_trans tsupport_mul_subset_left hψ0
  have hvsuppS : ∀ i : Fin N, tsupport (v i.succ) ⊆ (c i).U := fun i =>
    subset_trans tsupport_mul_subset_left (hψsucc i)
  -- each piece satisfies the identity
  have hpiece : ∀ k, ∫ x in Ω, fderiv ℝ (v k) x w
      = ∫ x in frontier Ω, v k x * ⟪ν x, w⟫ ∂μHE[2] := by
    refine Fin.cases ?_ ?_
    · rw [divergence_interior_case hΩ (hvC 0) (hvcs 0) hvsupp0 w,
        boundary_integral_interior_case hΩ hvsupp0 ν w]
    · intro i
      exact divergence_chart_case hΩ (c i) (hvC i.succ) (hvcs i.succ)
        (hvsuppS i) hν w
  -- u agrees with Σ v k on a neighborhood of Ω̄
  have husum : ∀ x ∈ closure Ω, u x = ∑ k, v k x := by
    intro x hx
    have h1 : (∑ k, ψ k x) = 1 := hψsum hx
    rw [hv]
    simp only
    rw [← Finset.sum_mul, h1, one_mul]
  -- LHS splits
  have hL : ∫ x in Ω, fderiv ℝ u x w = ∑ k, ∫ x in Ω, fderiv ℝ (v k) x w := by
    rw [← integral_finset_sum]
    · refine setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
      have hloc : u =ᶠ[𝓝 x] fun y => ∑ k, v k y := by
        filter_upwards [hΩ.mem_nhds hx] with y hy
        exact husum y (subset_closure hy)
      have hdiff : ∀ k ∈ Finset.univ, DifferentiableAt ℝ (v k) x := fun k _ =>
        ((hvC k).differentiable one_ne_zero) x
      rw [hloc.fderiv_eq, fderiv_fun_sum hdiff]
      rw [ContinuousLinearMap.sum_apply]
    · intro k _
      have hcont : Continuous fun x => fderiv ℝ (v k) x w :=
        ((hvC k).continuous_fderiv one_ne_zero).clm_apply continuous_const
      exact (hcont.integrable_of_hasCompactSupport
        (hasCompactSupport_fderiv_apply (hvcs k) w)).integrableOn
  -- RHS splits
  have hR : ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[2]
      = ∑ k, ∫ x in frontier Ω, v k x * ⟪ν x, w⟫ ∂μHE[2] := by
    rw [← integral_finset_sum]
    · refine setIntegral_congr_fun isClosed_frontier.measurableSet fun x hx => ?_
      rw [husum x (frontier_subset_closure hx), Finset.sum_mul]
    · intro k _
      have h := integrableOn_frontier_inner hΩ hb hC1
        ((hψC k).continuous.mul hu.continuous) hν w
      exact h.congr_fun (fun x _ => by simp only [hv, Pi.mul_apply])
        isClosed_frontier.measurableSet
  rw [hL, hR]
  exact Finset.sum_congr rfl fun k _ => hpiece k

/-- **The Divergence Theorem** (the paper's Theorem, directional form):
`Ω ⊆ ℝ³` open, bounded, with C¹ boundary, `u ∈ C¹(O)` for an open
`O ⊇ Ω̄`, `ν` an outward unit normal field.  Then for every `w ∈ ℝ³`

    ∫_Ω Du·w dV = ∫_{∂Ω} u ⟨ν, w⟩ dS .

Taking `w = eᵢ` recovers the component form
`∫_Ω u_{x_i} = ∫_{∂Ω} u νᵢ`. -/
theorem divergence_theorem (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {O : Set E3} (hO : IsOpen O)
    (hΩO : closure Ω ⊆ O) {u : E3 → ℝ} (hu : ContDiffOn ℝ 1 u O)
    {ν : E3 → E3} (hν : IsOutwardNormal Ω ν) (w : E3) :
    ∫ x in Ω, fderiv ℝ u x w
      = ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[2] := by
  have hcl : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  obtain ⟨φ, hφC, hφcs, hφO, hφ1, -⟩ := exists_cutoff hcl hO hΩO
  obtain ⟨hφuC, -⟩ := contDiff_cutoff_mul hO hφC hφcs hφO hu
  calc ∫ x in Ω, fderiv ℝ u x w
      = ∫ x in Ω, fderiv ℝ (fun y => φ y * u y) x w := by
        refine setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
        rw [fderiv_cutoff_mul hΩ hφ1 hx]
    _ = ∫ x in frontier Ω, (fun y => φ y * u y) x * ⟪ν x, w⟫ ∂μHE[2] :=
        divergence_compact_support hΩ hb hC1 hφuC hν w
    _ = ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[2] := by
        refine setIntegral_congr_fun isClosed_frontier.measurableSet
          fun x hx => ?_
        rw [eqOn_cutoff_mul_frontier hφ1 hx]

/-! ### The classical vector-field form -/

/-- The divergence `div F = Σᵢ ⟨DF(eᵢ), eᵢ⟩` of a vector field, via the
standard orthonormal basis (basis-independent: it is the trace of
`DF`). -/
def div (F : E3 → E3) (x : E3) : ℝ :=
  ∑ i, ⟪fderiv ℝ F x (stdOrthonormalBasis ℝ E3 i), stdOrthonormalBasis ℝ E3 i⟫

/-- The vector cutoff product is `C¹` with compact support (`smul`
version of `contDiff_cutoff_mul`). -/
private lemma contDiff_cutoff_smul {φ : E3 → ℝ} {F : E3 → E3} {O : Set E3}
    (hO : IsOpen O) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hF : ContDiffOn ℝ 1 F O) :
    ContDiff ℝ 1 (fun y => φ y • F y) ∧
      HasCompactSupport (fun y => φ y • F y) := by
  constructor
  · rw [← contDiffOn_univ]
    refine contDiffOn_of_locally_contDiffOn fun x _ => ?_
    by_cases hx : x ∈ O
    · exact ⟨O, hO, hx, (hφ.contDiffOn.smul hF).mono Set.inter_subset_right⟩
    · refine ⟨(tsupport φ)ᶜ, (isClosed_tsupport φ).isOpen_compl,
        fun h => hx (hφO h), ?_⟩
      refine (contDiffOn_const (c := (0 : E3))).congr fun y hy => ?_
      rw [image_eq_zero_of_notMem_tsupport hy.2, zero_smul]
  · exact hφc.smul_right

/-- **Divergence theorem, flux form**: `∫_Ω div F dV = ∫_{∂Ω} F·ν dS`. -/
theorem divergence_theorem_vector_field (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {O : Set E3}
    (hO : IsOpen O) (hΩO : closure Ω ⊆ O) {F : E3 → E3}
    (hF : ContDiffOn ℝ 1 F O) {ν : E3 → E3} (hν : IsOutwardNormal Ω ν) :
    ∫ x in Ω, div F x
      = ∫ x in frontier Ω, ⟪F x, ν x⟫ ∂μHE[2] := by
  set b := stdOrthonormalBasis ℝ E3 with hb'
  -- cut off to a global C¹ field agreeing with F near Ω̄
  have hcl : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  obtain ⟨φ, hφC, hφcs, hφO, hφ1, -⟩ := exists_cutoff hcl hO hΩO
  obtain ⟨hGC, hGcs⟩ := contDiff_cutoff_smul hO hφC hφcs hφO hF
  set G : E3 → E3 := fun y => φ y • F y with hGdef
  have hGF_val : ∀ x ∈ closure Ω, G x = F x := by
    intro x hx
    rw [hGdef]
    simp only
    rw [hφ1 hx, Pi.one_apply, one_smul]
  have hGF_der : ∀ x ∈ Ω, fderiv ℝ G x = fderiv ℝ F x := by
    intro x hx
    have hev : G =ᶠ[𝓝 x] F := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact hGF_val y (subset_closure hy)
    exact hev.fderiv_eq
  -- scalar components of G
  have hcompC : ∀ i, ContDiff ℝ 1 fun x => ⟪G x, b i⟫ := fun i =>
    hGC.inner ℝ contDiff_const
  have hcompcs : ∀ i, HasCompactSupport fun x => ⟪G x, b i⟫ := by
    intro i
    refine HasCompactSupport.intro hGcs fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_left]
  -- component derivative identity
  have hDcomp : ∀ i x, fderiv ℝ (fun y => ⟪G y, b i⟫) x (b i)
      = ⟪fderiv ℝ G x (b i), b i⟫ := by
    intro i x
    have hGd : DifferentiableAt ℝ G x := (hGC.differentiable one_ne_zero) x
    rw [fderiv_inner_apply ℝ hGd (differentiableAt_const (b i)) (b i)]
    simp
  -- scalar theorem, one basis direction at a time
  have hscalar : ∀ i, ∫ x in Ω, fderiv ℝ (fun y => ⟪G y, b i⟫) x (b i)
      = ∫ x in frontier Ω, ⟪G x, b i⟫ * ⟪ν x, b i⟫ ∂μHE[2] := fun i =>
    divergence_theorem hΩ hb hC1 isOpen_univ (subset_univ _)
      (hcompC i).contDiffOn hν (b i)
  -- integrability of the pieces on both sides
  have hintΩ : ∀ i, IntegrableOn
      (fun x => fderiv ℝ (fun y => ⟪G y, b i⟫) x (b i)) Ω volume := by
    intro i
    have hcont : Continuous fun x => fderiv ℝ (fun y => ⟪G y, b i⟫) x (b i) :=
      ((hcompC i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (hcont.integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply (hcompcs i) (b i))).integrableOn
  have hintFr : ∀ i, IntegrableOn
      (fun x => ⟪G x, b i⟫ * ⟪ν x, b i⟫) (frontier Ω) μHE[2] := fun i =>
    integrableOn_frontier_inner hΩ hb hC1 (hGC.continuous.inner continuous_const)
      hν (b i)
  -- assemble
  calc ∫ x in Ω, div F x
      = ∫ x in Ω, ∑ i, ⟪fderiv ℝ G x (b i), b i⟫ := by
        refine setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
        rw [div]
        exact Finset.sum_congr rfl fun i _ => by rw [hGF_der x hx]
    _ = ∫ x in Ω, ∑ i, fderiv ℝ (fun y => ⟪G y, b i⟫) x (b i) := by
        refine setIntegral_congr_fun hΩ.measurableSet fun x _ => ?_
        exact Finset.sum_congr rfl fun i _ => (hDcomp i x).symm
    _ = ∑ i, ∫ x in Ω, fderiv ℝ (fun y => ⟪G y, b i⟫) x (b i) :=
        integral_finset_sum _ fun i _ => hintΩ i
    _ = ∑ i, ∫ x in frontier Ω, ⟪G x, b i⟫ * ⟪ν x, b i⟫ ∂μHE[2] :=
        Finset.sum_congr rfl fun i _ => hscalar i
    _ = ∫ x in frontier Ω, (∑ i, ⟪G x, b i⟫ * ⟪ν x, b i⟫) ∂μHE[2] :=
        (integral_finset_sum _ fun i _ => hintFr i).symm
    _ = ∫ x in frontier Ω, ⟪F x, ν x⟫ ∂μHE[2] := by
        refine setIntegral_congr_fun isClosed_frontier.measurableSet
          fun x hx => ?_
        have hParseval : (∑ i, ⟪G x, b i⟫ * ⟪b i, ν x⟫) = ⟪G x, ν x⟫ :=
          b.sum_inner_mul_inner (G x) (ν x)
        calc (∑ i, ⟪G x, b i⟫ * ⟪ν x, b i⟫)
            = ∑ i, ⟪G x, b i⟫ * ⟪b i, ν x⟫ :=
              Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (ν x) (b i)]
          _ = ⟪G x, ν x⟫ := hParseval
          _ = ⟪F x, ν x⟫ := by
              rw [hGF_val x (frontier_subset_closure hx)]

end DivergenceFull
