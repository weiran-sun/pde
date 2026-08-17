/-
# THE DIVERGENCE THEOREM IN ℝⁿ — fully self-contained over Mathlib

ZERO local imports: this single file contains everything — the
hypersurface area formula (inlined from the GeneralizedGraph project:
Setup, Affine, Local, Cube, Main) followed by the complete divergence
theorem development (GeneralizedDivergence: Setup, Cutoff,
LocalComputation, PartitionOfUnity, SurfaceIntegral, Main,
Applications).  It compiles against Mathlib alone (toolchain and
Mathlib `v4.30.0-rc2`); drop it into any Lake project with that Mathlib
and `import` nothing else.

EVERY THEOREM IS FULLY PROVEN — no sorries, no axioms beyond Mathlib's
`propext`, `Classical.choice`, `Quot.sound`.

Conventions: `m` is the boundary dimension, `n = m + 1` the ambient
dimension; `EM m = ℝᵐ`, `EN m = ℝᵐ⁺¹` (as the ℓ²-product `ℝᵐ ×₂ ℝ`);
the main theorems require `0 < m` (that is, `n ≥ 2`).  Each inlined
module sits in its own `section` with its own `open`s; everything lives
in the single namespace `GeneralizedDivergenceStandalone`.

Headline results:
* `area_formula`      : `μHE[m] (graph f U) = ∫⁻ z in U, √(1+‖∇f‖²)`;
* `divergence_theorem`: for `Ω ⊆ ℝⁿ` open bounded with C¹ boundary,
    `u ∈ C¹(O)`, `O ⊇ Ω̄` open, `ν` any outward unit normal field:
      `∫ x in Ω, fderiv ℝ u x w = ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[m]`;
* `divergence_theorem_vector_field` : `∫ div F = ∫_{∂Ω} ⟪F, ν⟫`;
* `integration_by_parts`, `green_first_identity`,
  `green_second_identity`, `integral_laplacian_eq_flux`.
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Order.OrderClosed

noncomputable section

namespace GeneralizedDivergenceStandalone

/-
=== GeneralizedGraph.Setup ===

# The area formula for a C¹ graph in arbitrary dimension — setup

**What this file provides.**  The ambient spaces, the graph map, the
Jacobian factor, and the elementary "inequality (1)": the graph map
never decreases distances.

**The generalization.**  Where `GraphArea` worked with graphs of
`f : ℝ² → ℝ` inside ℝ³, everything here is parameterized by the base
dimension `m : ℕ`:

* the base space is `EM m := EuclideanSpace ℝ (Fin m)` (Euclidean ℝᵐ);
* the ambient space is `EN m := WithLp 2 (EM m × ℝ)`, the ℓ²-product
  of the base with a vertical line — Euclidean ℝᵐ⁺¹ with the
  horizontal/vertical splitting kept visible in the type;
* the graph of `f : EM m → ℝ` over `U ⊆ ℝᵐ` is an `m`-dimensional
  (that is, (n−1)-dimensional, `n = m + 1`) hypersurface in `EN m`.

Every proof in this file is dimension-generic: the ℓ²-Pythagoras
identity `‖(a, b)‖² = ‖a‖² + b²` for the product norm does all the
work, exactly as in the planar case.
-/

section


variable (m : ℕ)

/-- Euclidean ℝᵐ — the base space over which graphs are taken. -/
abbrev EM : Type := EuclideanSpace ℝ (Fin m)

/-- Euclidean ℝᵐ⁺¹, realized as the ℓ²-product of the base ℝᵐ and a
vertical line ℝ.  Isometric to `EuclideanSpace ℝ (Fin (m+1))`, but the
product form keeps the horizontal/vertical split visible: a point is
`(z, t)` with `z : ℝᵐ` horizontal and `t : ℝ` vertical. -/
abbrev EN : Type := WithLp 2 (EM m × ℝ)

variable {m}

/-! ### ℓ²-product norm helpers

Everything in the local analysis reduces to the Pythagoras identity for
the ℓ²-product norm on `EN m`; we record the four forms that get used.
These are all dimension-independent. -/

/-- Pythagoras for the ℓ²-product: `‖(a, b)‖² = ‖a‖² + b²`. -/
lemma norm_toLp_sq (a : EM m) (b : ℝ) :
    ‖(WithLp.toLp 2 (a, b) : EN m)‖ ^ 2 = ‖a‖ ^ 2 + b ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [WithLp.fst, WithLp.snd, sq_abs]

/-- The horizontal component is no longer than the vector. -/
lemma norm_fst_le_norm_toLp (a : EM m) (b : ℝ) :
    ‖a‖ ≤ ‖(WithLp.toLp 2 (a, b) : EN m)‖ := by
  have h := norm_toLp_sq a b
  calc ‖a‖ = Real.sqrt (‖a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖(WithLp.toLp 2 (a, b) : EN m)‖ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
    _ = _ := Real.sqrt_sq (norm_nonneg _)

/-- The vertical component is no longer than the vector. -/
lemma abs_snd_le_norm_toLp (a : EM m) (b : ℝ) :
    |b| ≤ ‖(WithLp.toLp 2 (a, b) : EN m)‖ := by
  have h := norm_toLp_sq a b
  calc |b| = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
    _ ≤ Real.sqrt (‖(WithLp.toLp 2 (a, b) : EN m)‖ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖a‖])
    _ = _ := Real.sqrt_sq (norm_nonneg _)

/-- The ℓ²-norm is at most the ℓ¹-norm (used for cheap Lipschitz bounds). -/
lemma norm_toLp_le (a : EM m) (b : ℝ) :
    ‖(WithLp.toLp 2 (a, b) : EN m)‖ ≤ ‖a‖ + |b| := by
  have h := norm_toLp_sq a b
  calc ‖(WithLp.toLp 2 (a, b) : EN m)‖
      = Real.sqrt (‖(WithLp.toLp 2 (a, b) : EN m)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((‖a‖ + |b|) ^ 2) := Real.sqrt_le_sqrt
        (by nlinarith [norm_nonneg a, abs_nonneg b, sq_abs b])
    _ = ‖a‖ + |b| := Real.sqrt_sq (by positivity)

variable (f : EM m → ℝ) (U : Set (EM m))

/-- The graph map `Φ(z) = (z, f z)` sending a base point to the point of
the hypersurface above it. -/
def graphMap (z : EM m) : EN m := WithLp.toLp 2 (z, f z)

/-- The graph `Γ_f` of `f` over a set `s ⊆ ℝᵐ` — the hypersurface whose
`m`-dimensional measure the main theorem computes. -/
def graph (s : Set (EM m)) : Set (EN m) := graphMap f '' s

/-- The Jacobian factor `J(z) = √(1 + ‖Df z‖²)`.
Since `f` is scalar-valued, the operator norm `‖fderiv ℝ f z‖` equals
the Euclidean norm of the gradient vector `∇f(z)`, so this is the
classical integrand `√(1 + |∇f|²)` of the hypersurface area formula. -/
def jac (z : EM m) : ℝ := Real.sqrt (1 + ‖fderiv ℝ f z‖ ^ 2)

variable {f U}

/-- Displacements of the graph map, componentwise: horizontal part
`z − z'`, vertical part `f z − f z'`. -/
lemma graphMap_sub (z z' : EM m) :
    graphMap f z - graphMap f z' = WithLp.toLp 2 (z - z', f z - f z') := by
  rw [graphMap, graphMap, ← WithLp.toLp_sub, Prod.mk_sub_mk]

/-- `J ≥ 1`: a graph always has at least as much area as its shadow. -/
lemma one_le_jac (z : EM m) : 1 ≤ jac f z := by
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖fderiv ℝ f z‖ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖fderiv ℝ f z‖])
    _ = jac f z := rfl

lemma jac_pos (z : EM m) : 0 < jac f z :=
  lt_of_lt_of_le one_pos (one_le_jac z)

/-- `J` is continuous on `U`: the derivative of a C¹ function is
continuous on the open set `U`, and `t ↦ √(1 + t²)` is continuous. -/
lemma continuousOn_jac (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    ContinuousOn (jac f) U := by
  have h : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  exact (continuousOn_const.add (h.norm.pow 2)).sqrt

/-- The Pythagoras identity behind all the local estimates: with the
ℓ²-product norm on `EN m`, `‖Φ z − Φ z'‖² = ‖z − z'‖² + |f z − f z'|²`. -/
lemma norm_graphMap_sub_sq (z z' : EM m) :
    ‖graphMap f z - graphMap f z'‖ ^ 2 = ‖z - z'‖ ^ 2 + (f z - f z') ^ 2 := by
  rw [graphMap_sub, norm_toLp_sq]

/-- **Inequality (1)**: the graph map never decreases distances — the
hypersurface is at least as "spread out" as its shadow in the base. -/
lemma norm_le_norm_graphMap_sub (z z' : EM m) :
    ‖z - z'‖ ≤ ‖graphMap f z - graphMap f z'‖ := by
  rw [graphMap_sub]
  exact norm_fst_le_norm_toLp _ _

/-- `Φ` is injective (clear from the horizontal coordinates). -/
lemma graphMap_injective : Function.Injective (graphMap f) := by
  intro z z' h
  simpa [graphMap] using congrArg (fun w : EN m => (WithLp.ofLp w).1) h

/-- `Φ` is continuous when `f` is; graphs of continuous functions over
compact sets are compact, which is how measurability of the graph
pieces is obtained for free in Lean. -/
lemma continuousOn_graphMap (hf : ContinuousOn f U) :
    ContinuousOn (graphMap f) U := by
  have h1 : ContinuousOn (fun z : EM m => (z, f z)) U := continuousOn_id.prodMk hf
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (EM m) ℝ).symm.continuous.comp_continuousOn h1

end


/-
=== GeneralizedGraph.Affine ===

# Affine graphs: the exact area of a tilted hyperplane

**Goal of this file.**  `μHE[m](Φ_aff(A)) = √(1 + ‖p‖²) · vol(A)` for
the affine graph map `Φ_aff(z) = (z, ⟪p, z⟫ + c)` — the exact
`m`-dimensional measure of a tilted hyperplane patch in ℝᵐ⁺¹.

**Proof structure** (same as the planar case, with one genuinely
`n`-dimensional upgrade):

1. kill the constant `c` by a vertical translation (an isometry of
   `EN m`, so `μHE` does not change);
2. flatten the image hyperplane `P = range L` by orthonormal
   coordinates (`stdOrthonormalBasis` gives a linear isometry
   `P ≃ ℝᵐ`), reducing to a linear self-map `T : ℝᵐ → ℝᵐ`;
3. `μHE[m] = volume` on ℝᵐ (Haar uniqueness, built into Mathlib's
   `μHE`) and linear maps scale `volume` by `|det|`;
4. **the Gram determinant**: `(det T)² = det(MᵀM) = det(I + p pᵀ)`,
   and the *matrix determinant lemma* — this is the step that in the
   planar case was a 2×2 computation — evaluates
   `det(I + p pᵀ) = 1 + ‖p‖²` in every dimension at once.
-/

section
open MeasureTheory Measure Module Matrix
open scoped RealInnerProductSpace

variable {m : ℕ} (p : EM m) (c : ℝ)

/-- The affine graph map `Φ_aff(z) = (z, ⟪p, z⟫ + c)`: the graph of the
affine function with (Riesz) gradient vector `p` and offset `c`. -/
def affGraphMap (z : EM m) : EN m := WithLp.toLp 2 (z, ⟪p, z⟫ + c)

/-- The linear part `L(z) = (z, ⟪p, z⟫)`, whose image is the hyperplane
`P ⊆ ℝᵐ⁺¹` spanned by the vectors `(eᵢ, pᵢ)`, `i < m`. -/
def affGraphLin (z : EM m) : EN m := WithLp.toLp 2 (z, ⟪p, z⟫)

/-- **The Gram determinant, isolated.**  The Gram matrix of the spanning
vectors `(eᵢ, pᵢ)` of the hyperplane is `I + p pᵀ` (identity plus the
outer product of the gradient with itself), and the matrix determinant
lemma gives `det (I + p pᵀ) = 1 + ⟨p, p⟩ = 1 + ‖p‖²`.

In the planar case this was a bare-hands 2×2 computation; the
rank-one structure (`f` is scalar-valued, so the outer product has rank
one) is what keeps the answer `√(1 + ‖∇f‖²)` in *every* dimension. -/
lemma gram_det :
    (1 + Matrix.replicateCol Unit (fun i => p i)
        * Matrix.replicateRow Unit (fun j => p j)).det = 1 + ‖p‖ ^ 2 := by
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow,
    EuclideanSpace.real_norm_sq_eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (sq (p i)).symm

/-- The linear part as a bundled linear map `ℝᵐ →ₗ ℝᵐ⁺¹`. -/
def affGraphLinₗ : EM m →ₗ[ℝ] EN m :=
  (WithLp.linearEquiv 2 ℝ (EM m × ℝ)).symm.toLinearMap.comp
    (LinearMap.prod LinearMap.id (innerSL ℝ p).toLinearMap)

@[simp] lemma affGraphLinₗ_apply (z : EM m) : affGraphLinₗ p z = affGraphLin p z := rfl

/-- `L` is injective (its first component is the identity). -/
lemma affGraphLinₗ_injective : Function.Injective (affGraphLinₗ p) := by
  intro z z' h
  simpa [affGraphLinₗ] using congrArg (fun w : EN m => (WithLp.ofLp w).1) h

/-- **The affine area formula**, for *every* subset `A ⊆ ℝᵐ` — Mathlib
measures applied to arbitrary sets are outer measures, so no
measurability hypothesis is needed:

    μHE[m] (Φ_aff '' A) = √(1 + ‖p‖²) · vol(A).

This is the exact statement the local estimates compare a C¹ graph
against; the factor `√(1 + ‖p‖²)` is `jac` at gradient `p`. -/
theorem affine_area (A : Set (EM m)) :
    μHE[m] (affGraphMap p c '' A)
      = ENNReal.ofReal (Real.sqrt (1 + ‖p‖ ^ 2)) * volume A := by
  -- Step 1 (remove the constant): vertical translation is an isometry
  -- of `EN m`, and `μHE` is isometry-invariant.
  have step0 : μHE[m] (affGraphMap p c '' A) = μHE[m] (affGraphLin p '' A) := by
    have himg : affGraphMap p c '' A
        = (fun w : EN m => w + WithLp.toLp 2 ((0 : EM m), c)) '' (affGraphLin p '' A) := by
      rw [Set.image_image]
      apply Set.image_congr
      intro z _
      simp only [affGraphMap, affGraphLin, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero]
    have hiso : Isometry (fun w : EN m => w + WithLp.toLp 2 ((0 : EM m), c)) :=
      Isometry.of_dist_eq fun w w' => dist_add_right w w' _
    rw [himg]
    exact hiso.euclideanHausdorffMeasure_image _
  -- The image hyperplane `P = range L` and its dimension: `L` is
  -- injective, so `P` is `m`-dimensional.
  set L : EM m →ₗ[ℝ] EN m := affGraphLinₗ p with hLdef
  have hrank : finrank ℝ (LinearMap.range L) = m := by
    rw [LinearMap.finrank_range_of_inj (affGraphLinₗ_injective p),
      finrank_euclideanSpace, Fintype.card_fin]
  -- Orthonormal coordinates on `P`: a linear isometry `R : P ≃ ℝᵐ`.
  set R : LinearMap.range L ≃ₗᵢ[ℝ] EM m :=
    ((stdOrthonormalBasis ℝ (LinearMap.range L)).reindex (finCongr hrank)).repr with hRdef
  -- The flattened linear map `T = R ∘ L : ℝᵐ → ℝᵐ`.
  set T : EM m →ₗ[ℝ] EM m := R.toLinearMap.comp L.rangeRestrict with hTdef
  -- Step 2 (flatten): `L '' A` is the image of `T '' A` under the
  -- isometry `val ∘ R.symm : ℝᵐ → ℝᵐ⁺¹`.
  have himg2 : (Subtype.val ∘ R.symm) '' (T '' A) = affGraphLin p '' A := by
    rw [Set.image_image]
    apply Set.image_congr
    intro z _
    show (R.symm (R (L.rangeRestrict z)) : EN m) = affGraphLin p z
    rw [LinearIsometryEquiv.symm_apply_apply]
    rfl
  have hiso2 : Isometry (Subtype.val ∘ R.symm : EM m → EN m) :=
    isometry_subtype_coe.comp R.symm.isometry
  -- Step 3 (Gram): `(det T)² = 1 + ‖p‖²` via `MᵀM = I + p pᵀ`.
  have hdet : |LinearMap.det T| = Real.sqrt (1 + ‖p‖ ^ 2) := by
    set b := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis with hbdef
    set M := LinearMap.toMatrix b b T with hMdef
    -- Standard-basis inner products evaluate to coordinates.
    have hip : ∀ (l : Fin m) (x : EM m), ⟪(b l : EM m), x⟫ = x l := by
      intro l x
      rw [hbdef, OrthonormalBasis.coe_toBasis]
      exact ((EuclideanSpace.basisFun (Fin m) ℝ).repr_apply_apply x l).symm
    -- Inner products of real numbers are products (definitionally).
    have hRinner : ∀ s t : ℝ, ⟪s, t⟫ = t * s := fun s t => rfl
    -- The transpose product `MᵀM` is the Gram matrix of the images
    -- `T eᵢ`, whose entries are the inner products `⟪L eᵢ, L eⱼ⟫`
    -- because the flattening `R` preserves inner products.
    have hentry : ∀ i j, (Mᵀ * M) i j = ⟪affGraphLin p (b i), affGraphLin p (b j)⟫ := by
      intro i j
      have hMcol : ∀ (k l : Fin m), M k l = T (b l) k := by
        intro k l
        rw [hMdef, LinearMap.toMatrix_apply, hbdef,
          OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
      have : (Mᵀ * M) i j = ⟪T (b i), T (b j)⟫ := by
        rw [Matrix.mul_apply, PiLp.inner_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.transpose_apply, hMcol, hMcol, hRinner]
        ring
      rw [this, hTdef]
      show ⟪R (L.rangeRestrict (b i)), R (L.rangeRestrict (b j))⟫ = _
      rw [LinearIsometryEquiv.inner_map_map, Submodule.coe_inner]
      rfl
    -- Assemble the Gram matrix `I + p pᵀ` entrywise.
    have hgram : Mᵀ * M
        = 1 + Matrix.replicateCol Unit (fun i => p i)
            * Matrix.replicateRow Unit (fun j => p j) := by
      -- `⟪L eᵢ, L eⱼ⟫ = ⟪eᵢ, eⱼ⟫ + pᵢ pⱼ`: split the ℓ²-product inner
      -- product into horizontal and vertical parts.
      have hinner : ∀ l l' : Fin m,
          ⟪affGraphLin p (b l), affGraphLin p (b l')⟫
            = (b l' : EM m) l + p l * p l' := by
        intro l l'
        have hsplit : ⟪affGraphLin p (b l), affGraphLin p (b l')⟫
            = ⟪(b l : EM m), (b l' : EM m)⟫ + ⟪(⟪p, (b l : EM m)⟫ : ℝ), (⟪p, (b l' : EM m)⟫ : ℝ)⟫ := rfl
        rw [hsplit, hRinner, hip l (b l'), ← real_inner_comm p (b l),
          ← real_inner_comm p (b l'), hip, hip]
        ring
      -- Coordinates of the standard basis vectors are Kronecker deltas.
      have hb01 : ∀ l l' : Fin m, ((b l' : EM m) l) = if l = l' then (1 : ℝ) else 0 := by
        intro l l'
        rw [← hip l (b l'), hbdef, OrthonormalBasis.coe_toBasis]
        exact orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin m) ℝ).orthonormal l l'
      ext i j
      rw [hentry i j, hinner i j, hb01 i j, Matrix.add_apply, Matrix.one_apply,
        Matrix.mul_apply]
      simp [Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    -- `det(MᵀM) = (det T)²` and the matrix determinant lemma finish.
    have h2 : LinearMap.det T ^ 2 = 1 + ‖p‖ ^ 2 := by
      have hdetc := congrArg Matrix.det hgram
      rw [Matrix.det_mul, Matrix.det_transpose, gram_det] at hdetc
      rw [← LinearMap.det_toMatrix b T, ← hMdef, sq]
      exact hdetc
    rw [← Real.sqrt_sq_eq_abs, h2]
  -- Chain everything: translate, flatten, scale by `|det|`.
  calc μHE[m] (affGraphMap p c '' A)
      = μHE[m] (affGraphLin p '' A) := step0
    _ = μHE[m] ((Subtype.val ∘ R.symm) '' (T '' A)) := by rw [himg2]
    _ = μHE[m] (T '' A) := hiso2.euclideanHausdorffMeasure_image _
    _ = volume (T '' A) := by
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    _ = ENNReal.ofReal |LinearMap.det T| * volume A :=
        addHaar_image_linearMap volume T A
    _ = ENNReal.ofReal (Real.sqrt (1 + ‖p‖ ^ 2)) * volume A := by rw [hdet]

end


/-
=== GeneralizedGraph.Local ===

# The local estimate: a C¹ graph is almost affine

**Standing local data**: a convex `Q ⊆ U` (in the sequel, a closed
`m`-cube), a base point `zQ ∈ Q`, and `ε ∈ (0,1)` with
`‖Df z − Df zQ‖ ≤ ε` on `Q` (small oscillation of the derivative).

**Output**: the two-sided area estimate

    (1−ε)ᵐ · J(zQ) · vol(S) ≤ μHE[m](Γ_f|_S) ≤ (1+ε)ᵐ · J(zQ) · vol(S)

for every `S ⊆ Q` — the engine of the Riemann-grid argument.

**What changes in dimension `m`**: the transport maps between the graph
and its tangent hyperplane are `(1+ε)`- resp. `(1−ε)⁻¹`-Lipschitz
exactly as in the plane (the Taylor estimate is dimension-free), but an
`L`-Lipschitz map scales `m`-dimensional Hausdorff measure by `Lᵐ`, so
the sandwich constants become `(1±ε)ᵐ`.
-/

section
open MeasureTheory Measure
open scoped ENNReal NNReal

/-- `μHE[m]` is by definition a constant multiple of the gauge Hausdorff
measure `μH[m]`, so multiplicative comparisons transfer verbatim from
`μH` to `μHE`.  Used to move the Lipschitz-image estimates (stated for
`μH` in Mathlib) to the Euclidean-normalized measure. -/
private lemma muHE_le_of_muH_le {m : ℕ} {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {A B : Set X} {k : ℝ≥0∞}
    (h : μH[(m : ℝ)] A ≤ k * μH[(m : ℝ)] B) :
    μHE[m] A ≤ k * μHE[m] B := by
  rw [Measure.euclideanHausdorffMeasure_def]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact le_trans (mul_le_mul_right h _) (le_of_eq (by ring))

variable {m : ℕ} (f : EM m → ℝ)

/-- The tangent affine graph map at `zQ`:
`Φ_Q(z) = (z, f(zQ) + Df(zQ)(z − zQ))` — the graph of the first-order
Taylor polynomial.  It is `affGraphMap p c` for `p` the (Riesz) gradient
of `f` at `zQ` and `c := f zQ − ⟪p, zQ⟫`, so `affine_area` applies. -/
def tangentMap (zQ z : EM m) : EN m :=
  WithLp.toLp 2 (z, f zQ + fderiv ℝ f zQ (z - zQ))

variable {f} {U Q : Set (EM m)} {zQ : EM m} {ε : ℝ}

/-- Displacements of the tangent map, componentwise. -/
lemma tangentMap_sub (z z' : EM m) :
    tangentMap f zQ z - tangentMap f zQ z'
      = WithLp.toLp 2 (z - z', fderiv ℝ f zQ (z - z')) := by
  rw [tangentMap, tangentMap, ← WithLp.toLp_sub, Prod.mk_sub_mk,
    add_sub_add_left_eq_sub, ← map_sub, sub_sub_sub_cancel_right]

/-- **First-order Taylor estimate along segments** (dimension-free).
In Mathlib this is the mean value inequality against the fixed
candidate derivative `φ := fderiv ℝ f zQ`
(`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`). -/
theorem taylor_estimate (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hQ : Convex ℝ Q) (hQU : Q ⊆ U) (_hzQ : zQ ∈ Q)
    (hgrad : ∀ z ∈ Q, ‖fderiv ℝ f z - fderiv ℝ f zQ‖ ≤ ε)
    {z z' : EM m} (hz : z ∈ Q) (hz' : z' ∈ Q) :
    |f z - f z' - fderiv ℝ f zQ (z - z')| ≤ ε * ‖z - z'‖ := by
  have hdiff : ∀ x ∈ Q, HasFDerivWithinAt f (fderiv ℝ f x) Q x := fun x hx =>
    (((hf.differentiableOn one_ne_zero).differentiableAt
      (hU.mem_nhds (hQU hx))).hasFDerivAt).hasFDerivWithinAt
  simpa [Real.norm_eq_abs] using
    hQ.norm_image_sub_le_of_norm_hasFDerivWithin_le' hdiff hgrad hz' hz

/-- **Bi-Lipschitz sandwich** (dimension-free).  The difference of the
displacement vectors of `Φ` and `Φ_Q` is purely vertical, equal to the
Taylor remainder; combine `taylor_estimate` with the fact that the
horizontal component bounds the tangent displacement from below, and
the triangle inequality. -/
theorem biLipschitz_sandwich (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hQ : Convex ℝ Q) (hQU : Q ⊆ U) (hzQ : zQ ∈ Q)
    (hgrad : ∀ z ∈ Q, ‖fderiv ℝ f z - fderiv ℝ f zQ‖ ≤ ε)
    {z z' : EM m} (hz : z ∈ Q) (hz' : z' ∈ Q) :
    (1 - ε) * ‖tangentMap f zQ z - tangentMap f zQ z'‖
        ≤ ‖graphMap f z - graphMap f z'‖ ∧
      ‖graphMap f z - graphMap f z'‖
        ≤ (1 + ε) * ‖tangentMap f zQ z - tangentMap f zQ z'‖ := by
  have hε0 : 0 ≤ ε := by
    have h := hgrad zQ hzQ
    simp only [sub_self, norm_zero] at h
    exact h
  -- The difference of displacements is purely vertical: the Taylor
  -- remainder.
  have hdiff : graphMap f z - graphMap f z' - (tangentMap f zQ z - tangentMap f zQ z')
      = WithLp.toLp 2 ((0 : EM m), f z - f z' - fderiv ℝ f zQ (z - z')) := by
    rw [graphMap_sub, tangentMap_sub, ← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self]
  -- ... and hence bounded by `ε ‖z - z'‖ ≤ ε ‖Φ_Q z - Φ_Q z'‖`.
  have hzT : ‖z - z'‖ ≤ ‖tangentMap f zQ z - tangentMap f zQ z'‖ := by
    rw [tangentMap_sub]; exact norm_fst_le_norm_toLp _ _
  have hvert : ‖graphMap f z - graphMap f z' - (tangentMap f zQ z - tangentMap f zQ z')‖
      ≤ ε * ‖tangentMap f zQ z - tangentMap f zQ z'‖ := by
    rw [hdiff]
    calc ‖(WithLp.toLp 2 ((0 : EM m), f z - f z' - fderiv ℝ f zQ (z - z')) : EN m)‖
        ≤ ‖(0 : EM m)‖ + |f z - f z' - fderiv ℝ f zQ (z - z')| := norm_toLp_le _ _
      _ = |f z - f z' - fderiv ℝ f zQ (z - z')| := by simp
      _ ≤ ε * ‖z - z'‖ := taylor_estimate hU hf hQ hQU hzQ hgrad hz hz'
      _ ≤ ε * ‖tangentMap f zQ z - tangentMap f zQ z'‖ :=
          mul_le_mul_of_nonneg_left hzT hε0
  -- Triangle inequality, both ways.
  set G := graphMap f z - graphMap f z'
  set T := tangentMap f zQ z - tangentMap f zQ z'
  constructor
  · have h1 : ‖T‖ - ‖G‖ ≤ ‖T - G‖ := norm_sub_norm_le T G
    have h2 : ‖T - G‖ = ‖G - T‖ := norm_sub_rev T G
    nlinarith [hvert]
  · have h1 : ‖G‖ - ‖T‖ ≤ ‖G - T‖ := norm_sub_norm_le G T
    nlinarith [hvert]

/-- **Local two-sided area estimate.**

The transport map `T := Φ ∘ Φ_Q⁻¹ : Φ_Q(S) → Φ(S)` — in Lean simply
`Φ` composed with the horizontal projection — is `(1+ε)`-Lipschitz with
`(1−ε)⁻¹`-Lipschitz inverse by the sandwich; an `L`-Lipschitz map
scales `μH[m]` by at most `Lᵐ` (`LipschitzOnWith.hausdorffMeasure_image_le`),
so applying this in both directions and evaluating the tangent patch by
`affine_area` squeezes the graph area between `(1±ε)ᵐ · J(zQ) · vol S`. -/
theorem local_area_estimate (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hQ : Convex ℝ Q) (hQU : Q ⊆ U) (hzQ : zQ ∈ Q)
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hgrad : ∀ z ∈ Q, ‖fderiv ℝ f z - fderiv ℝ f zQ‖ ≤ ε)
    (S : Set (EM m)) (hS : S ⊆ Q) :
    ENNReal.ofReal ((1 - ε) ^ m * jac f zQ) * volume S
        ≤ μHE[m] (graph f S) ∧
      μHE[m] (graph f S)
        ≤ ENNReal.ofReal ((1 + ε) ^ m * jac f zQ) * volume S := by
  obtain ⟨hε0, hε1⟩ := hε
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  -- Identify the tangent map as an affine graph map; its area is exact.
  set p : EM m := (InnerProductSpace.toDual ℝ (EM m)).symm (fderiv ℝ f zQ) with hpdef
  have hpz : ∀ w, inner ℝ p w = fderiv ℝ f zQ w := fun w =>
    InnerProductSpace.toDual_symm_apply
  have hjac : jac f zQ = Real.sqrt (1 + ‖p‖ ^ 2) := by
    rw [jac, hpdef, LinearIsometryEquiv.norm_map]
  have haff : μHE[m] (tangentMap f zQ '' S)
      = ENNReal.ofReal (jac f zQ) * volume S := by
    have himg : tangentMap f zQ '' S
        = affGraphMap p (f zQ - inner ℝ p zQ) '' S := by
      apply Set.image_congr
      intro w _
      rw [tangentMap, affGraphMap]
      have : f zQ + fderiv ℝ f zQ (w - zQ)
          = inner ℝ p w + (f zQ - inner ℝ p zQ) := by
        rw [map_sub, ← hpz w, ← hpz zQ]; ring
      rw [this]
    rw [himg, affine_area, hjac]
  -- The two transport maps (compose with the horizontal projection).
  have hgcomp : ∀ w : EM m,
      graphMap f ((WithLp.ofLp (tangentMap f zQ w)).1) = graphMap f w := fun w => rfl
  -- Upper bound: the forward transport is (1+ε)-Lipschitz.
  have hg_lip : LipschitzOnWith (1 + ε).toNNReal
      (fun w : EN m => graphMap f ((WithLp.ofLp w).1)) (tangentMap f zQ '' S) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    rintro x ⟨zx, hzx, rfl⟩ y ⟨zy, hzy, rfl⟩
    rw [Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ 1 + ε)]
    show dist (graphMap f zx) (graphMap f zy)
      ≤ (1 + ε) * dist (tangentMap f zQ zx) (tangentMap f zQ zy)
    rw [dist_eq_norm, dist_eq_norm]
    exact (biLipschitz_sandwich hU hf hQ hQU hzQ hgrad (hS hzx) (hS hzy)).2
  -- Lower bound: the backward transport is (1−ε)⁻¹-Lipschitz.
  have hh_lip : LipschitzOnWith (1 - ε)⁻¹.toNNReal
      (fun w : EN m => tangentMap f zQ ((WithLp.ofLp w).1)) (graph f S) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    rintro x ⟨zx, hzx, rfl⟩ y ⟨zy, hzy, rfl⟩
    rw [Real.coe_toNNReal _ (by positivity)]
    show dist (tangentMap f zQ zx) (tangentMap f zQ zy)
      ≤ (1 - ε)⁻¹ * dist (graphMap f zx) (graphMap f zy)
    rw [dist_eq_norm, dist_eq_norm]
    have hlow := (biLipschitz_sandwich hU hf hQ hQU hzQ hgrad (hS hzx) (hS hzy)).1
    calc ‖tangentMap f zQ zx - tangentMap f zQ zy‖
        = (1 - ε)⁻¹ * ((1 - ε) * ‖tangentMap f zQ zx - tangentMap f zQ zy‖) := by
          field_simp
      _ ≤ (1 - ε)⁻¹ * ‖graphMap f zx - graphMap f zy‖ :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
  -- Images of the transports.
  have himgg : (fun w : EN m => graphMap f ((WithLp.ofLp w).1)) '' (tangentMap f zQ '' S)
      = graph f S := by
    rw [Set.image_image]; rfl
  have himgh : (fun w : EN m => tangentMap f zQ ((WithLp.ofLp w).1)) '' (graph f S)
      = tangentMap f zQ '' S := by
    rw [graph, Set.image_image]; rfl
  -- Hausdorff-measure comparison (gauge measure `μH`, exponent `m`),
  -- then transfer to `μHE` by the constant scalar.
  have hupH := hg_lip.hausdorffMeasure_image_le
    (by positivity : (0:ℝ) ≤ (m : ℝ))
  have hlowH := hh_lip.hausdorffMeasure_image_le
    (by positivity : (0:ℝ) ≤ (m : ℝ))
  rw [himgg] at hupH
  rw [himgh] at hlowH
  -- Convert the Lipschitz constants `K^(m:ℝ)` (an `ℝ≥0∞`-rpow) to
  -- `ENNReal.ofReal` of real `m`-th powers.
  have hcast : ∀ (a : ℝ), 0 ≤ a → ((a.toNNReal : ℝ≥0∞) ^ ((m : ℕ) : ℝ)
      = ENNReal.ofReal (a ^ m)) := by
    intro a ha
    rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow ha]
    rfl
  constructor
  · -- Lower: (1−ε)ᵐ jac · vol S ≤ μHE (graph f S).
    -- From hlowH : μH (tangent '' S) ≤ (1−ε)⁻ᵐ μH (graph f S).
    have h1 : μHE[m] (tangentMap f zQ '' S)
        ≤ ENNReal.ofReal ((1 - ε)⁻¹ ^ m) * μHE[m] (graph f S) := by
      apply muHE_le_of_muH_le
      rw [← hcast _ (by positivity)]
      exact hlowH
    rw [haff] at h1
    -- Multiply through by (1−ε)ᵐ and simplify.
    have hkey : ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal (jac f zQ) * volume S)
        ≤ ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal ((1 - ε)⁻¹ ^ m)
            * μHE[m] (graph f S)) :=
      mul_le_mul_right h1 _
    calc ENNReal.ofReal ((1 - ε) ^ m * jac f zQ) * volume S
        = ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal (jac f zQ) * volume S) := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal ((1 - ε)⁻¹ ^ m)
            * μHE[m] (graph f S)) := hkey
      _ = μHE[m] (graph f S) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          rw [show (1 - ε) ^ m * (1 - ε)⁻¹ ^ m = 1 by
            rw [← mul_pow, mul_inv_cancel₀ h1ε.ne', one_pow]]
          simp
  · -- Upper: μHE (graph f S) ≤ (1+ε)ᵐ jac · vol S.
    have h2 : μHE[m] (graph f S)
        ≤ ENNReal.ofReal ((1 + ε) ^ m) * μHE[m] (tangentMap f zQ '' S) := by
      apply muHE_le_of_muH_le
      rw [← hcast _ (by positivity)]
      exact hupH
    rw [haff] at h2
    calc μHE[m] (graph f S)
        ≤ ENNReal.ofReal ((1 + ε) ^ m) * (ENNReal.ofReal (jac f zQ) * volume S) := h2
      _ = ENNReal.ofReal ((1 + ε) ^ m * jac f zQ) * volume S := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]

end


/-
=== GeneralizedGraph.Cube ===

# Dyadic cubes and the graph over a closed cube

This file carries the two heaviest pieces of the argument up to
dimension `m`:

* the **dyadic decomposition** of an open set `U ⊆ ℝᵐ` into countably
  many non-overlapping closed cubes (greedy maximal-cube selection,
  indexed by `ℕ × (Fin m → ℤ)` — a generation and an integer lattice
  point per coordinate);
* the **area formula over a single closed cube** `cube_area`, proven by
  the `Nᵐ`-cell Riemann-grid argument: grid the cube at a scale
  realizing gradient oscillation `ε`, apply the local `(1±ε)ᵐ`
  estimate per cell, and let `ε ↓ 0`.

**The one non-mechanical generalization.** In the planar development,
the final `ε ↓ 0` squeeze forcing `μ = I` was closed by `nlinarith`,
which could expand `(1±ε)²` into a polynomial. That is impossible for a
symbolic exponent `(1±ε)ᵐ`. Here the squeeze
(`eq_of_grid_estimates`) is instead closed by a genuine limit: both
`(1+ε)ᵐ(I+εV)` and `(1−ε)ᵐ I` tend to `I` as `ε → 0⁺`, so the two-sided
bound passes to `μ = I` by `le_of_tendsto_of_tendsto`.
-/

section
open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal

variable {m : ℕ}

/-- Closed axis-parallel `m`-cube with center `z₀` and side `s`.
Built from coordinate conditions — `Metric.closedBall` would be a
Euclidean ball, not a cube. -/
def closedCube (z₀ : EM m) (s : ℝ) : Set (EM m) :=
  {z | ∀ i, |z i - z₀ i| ≤ s / 2}

/-- Cubes are convex: a coordinatewise bound is preserved under convex
combinations coordinate by coordinate. -/
lemma convex_closedCube (z₀ : EM m) (s : ℝ) :
    Convex ℝ (closedCube z₀ s) := by
  intro x hx y hy a b ha hb hab i
  have hxi := hx i
  have hyi := hy i
  have hcoord : (a • x + b • y) i - z₀ i = a * (x i - z₀ i) + b * (y i - z₀ i) := by
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    linear_combination (z₀ i) * hab
  rw [hcoord]
  calc |a * (x i - z₀ i) + b * (y i - z₀ i)|
      ≤ |a * (x i - z₀ i)| + |b * (y i - z₀ i)| := abs_add_le _ _
    _ = a * |x i - z₀ i| + b * |y i - z₀ i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (s / 2) + b * (s / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hxi ha)
          (mul_le_mul_of_nonneg_left hyi hb)
    _ = s / 2 := by rw [← add_mul, hab, one_mul]

/-- Points of the cube are within `s√m/2` of the center — the cube sits
inside the circumscribed Euclidean ball.  (In `ℝᵐ` the diagonal is
`s√m`.) -/
lemma closedCube_subset_closedBall (z₀ : EM m) {s : ℝ} (hs : 0 ≤ s) :
    closedCube z₀ s ⊆ Metric.closedBall z₀ (s * Real.sqrt m / 2) := by
  intro z hz
  rw [Metric.mem_closedBall, EuclideanSpace.dist_eq]
  have hbound : ∑ i, dist (z i) (z₀ i) ^ 2 ≤ (m : ℝ) * (s / 2) ^ 2 := by
    calc ∑ i, dist (z i) (z₀ i) ^ 2
        ≤ ∑ _i : Fin m, (s / 2) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.dist_eq]
          have := hz i
          nlinarith [abs_nonneg (z i - z₀ i)]
      _ = (m : ℝ) * (s / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i, dist (z i) (z₀ i) ^ 2)
      ≤ Real.sqrt ((m : ℝ) * (s / 2) ^ 2) := Real.sqrt_le_sqrt hbound
    _ = s * Real.sqrt m / 2 := by
        rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq (by positivity)]
        ring

/-- Cubes with nonnegative side are compact (closed + bounded). -/
lemma isCompact_closedCube (z₀ : EM m) {s : ℝ} (hs : 0 ≤ s) :
    IsCompact (closedCube z₀ s) := by
  have hclosed : IsClosed (closedCube z₀ s) := by
    have hrw : closedCube z₀ s = ⋂ i, {z : EM m | |z i - z₀ i| ≤ s / 2} := by
      ext z; simp [closedCube, Set.mem_iInter]
    rw [hrw]
    refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
    have : Continuous fun z : EM m => z i :=
      (ContinuousLinearMap.continuous (EuclideanSpace.proj (𝕜 := ℝ) i))
    fun_prop
  exact Metric.isCompact_of_isClosed_isBounded hclosed
    ((Metric.isBounded_closedBall).subset (closedCube_subset_closedBall z₀ hs))

/-- `vol(cube) = sᵐ`: via the volume-preserving identification of `ℝᵐ`
with `Fin m → ℝ` and the product formula for boxes. -/
lemma volume_closedCube (z₀ : EM m) {s : ℝ} (hs : 0 ≤ s) :
    volume (closedCube z₀ s) = ENNReal.ofReal (s ^ m) := by
  have hpre : closedCube z₀ s
      = WithLp.ofLp ⁻¹' (Set.univ.pi fun i : Fin m =>
          Set.Icc (z₀ i - s / 2) (z₀ i + s / 2)) := by
    ext z
    simp only [closedCube, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, true_implies, Set.mem_Icc]
    refine forall_congr' fun i => ?_
    rw [abs_le]
    constructor
    · rintro ⟨ha, hb⟩; constructor <;> linarith
    · rintro ⟨ha, hb⟩; constructor <;> linarith
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
    ((MeasurableSet.univ_pi fun i => measurableSet_Icc).nullMeasurableSet),
    volume_pi_pi]
  have hval : ∀ i : Fin m, volume (Set.Icc (z₀ i - s / 2) (z₀ i + s / 2))
      = ENNReal.ofReal s := by
    intro i; rw [Real.volume_Icc]; congr 1; ring
  simp only [hval]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow hs]

/-! ## Open cubes and null frontiers -/

/-- Open axis-parallel `m`-cube. -/
def openCube (z₀ : EM m) (s : ℝ) : Set (EM m) :=
  {z | ∀ i, |z i - z₀ i| < s / 2}

lemma openCube_subset_closedCube (z₀ : EM m) (s : ℝ) :
    openCube z₀ s ⊆ closedCube z₀ s :=
  fun _z hz i => (hz i).le

lemma isOpen_openCube (z₀ : EM m) (s : ℝ) : IsOpen (openCube z₀ s) := by
  have hrw : openCube z₀ s = ⋂ i, {z : EM m | |z i - z₀ i| < s / 2} := by
    ext z; simp [openCube, Set.mem_iInter]
  rw [hrw]
  refine isOpen_iInter_of_finite fun i => isOpen_lt ?_ continuous_const
  have : Continuous fun z : EM m => z i :=
    (ContinuousLinearMap.continuous (EuclideanSpace.proj (𝕜 := ℝ) i))
  fun_prop

lemma volume_openCube (z₀ : EM m) {s : ℝ} (hs : 0 ≤ s) :
    volume (openCube z₀ s) = ENNReal.ofReal (s ^ m) := by
  have hpre : openCube z₀ s
      = WithLp.ofLp ⁻¹' (Set.univ.pi fun i : Fin m =>
          Set.Ioo (z₀ i - s / 2) (z₀ i + s / 2)) := by
    ext z
    simp only [openCube, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, true_implies, Set.mem_Ioo]
    refine forall_congr' fun i => ?_
    rw [abs_lt]
    constructor
    · rintro ⟨ha, hb⟩; constructor <;> linarith
    · rintro ⟨ha, hb⟩; constructor <;> linarith
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
    ((MeasurableSet.univ_pi fun i => measurableSet_Ioo).nullMeasurableSet),
    volume_pi_pi]
  have hval : ∀ i : Fin m, volume (Set.Ioo (z₀ i - s / 2) (z₀ i + s / 2))
      = ENNReal.ofReal s := by
    intro i; rw [Real.volume_Ioo]; congr 1; ring
  simp only [hval]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow hs]

/-- The frontier of a cube is volume-null: closed and open cubes have
the same (finite) volume `sᵐ`. -/
lemma volume_frontier_closedCube (z₀ : EM m) {s : ℝ} (hs : 0 ≤ s) :
    volume (closedCube z₀ s \ interior (closedCube z₀ s)) = 0 := by
  have h1 : volume (interior (closedCube z₀ s)) = ENNReal.ofReal (s ^ m) := by
    apply le_antisymm
    · calc volume (interior (closedCube z₀ s))
          ≤ volume (closedCube z₀ s) := measure_mono interior_subset
        _ = ENNReal.ofReal (s ^ m) := volume_closedCube z₀ hs
    · calc ENNReal.ofReal (s ^ m) = volume (openCube z₀ s) :=
          (volume_openCube z₀ hs).symm
        _ ≤ volume (interior (closedCube z₀ s)) := measure_mono
            (interior_maximal (openCube_subset_closedCube z₀ s)
              (isOpen_openCube z₀ s))
  rw [measure_diff interior_subset measurableSet_interior.nullMeasurableSet
    (by rw [h1]; exact ENNReal.ofReal_ne_top)]
  rw [volume_closedCube z₀ hs, h1, tsub_self]

/-- The interior of a (nondegenerate) closed cube is contained in the
open cube: any boundary point can be pushed outside along a coordinate
direction. -/
lemma interior_closedCube_subset (z₀ : EM m) {s : ℝ} (hs : 0 < s) :
    interior (closedCube z₀ s) ⊆ openCube z₀ s := by
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  intro l
  rcases eq_or_ne (x l) (z₀ l) with heq | hne
  · rw [heq, sub_self, abs_zero]
    exact half_pos hs
  · set c : ℝ := if 0 < x l - z₀ l then ε / 2 else -(ε / 2) with hc
    have hcabs : |c| = ε / 2 := by
      rw [hc]; split_ifs <;> simp [abs_of_pos (half_pos hε)]
    set y : EM m := x + c • EuclideanSpace.single l (1 : ℝ) with hydef
    have hy : y ∈ closedCube z₀ s := by
      apply hball
      rw [Metric.mem_ball, hydef, dist_eq_norm, add_sub_cancel_left, norm_smul,
        PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, hcabs]
      linarith
    have hcoord : y l = x l + c := by
      rw [hydef]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      have hsl : (EuclideanSpace.single l (1:ℝ)) l = 1 := by
        simp
      rw [hsl, mul_one]
    have hyl := hy l
    rw [hcoord] at hyl
    rcases (sub_ne_zero.mpr hne).lt_or_gt with hneg | hpos
    · have hcval : c = -(ε / 2) := by rw [hc, if_neg (by linarith)]
      rw [hcval] at hyl
      rw [abs_le] at hyl
      rw [abs_lt]
      constructor <;> linarith
    · have hcval : c = ε / 2 := by rw [hc, if_pos hpos]
      rw [hcval] at hyl
      rw [abs_le] at hyl
      rw [abs_lt]
      constructor <;> linarith

/-! ## The greedy dyadic decomposition

Dyadic cubes of generation `k` (side `σ/2ᵏ`) are indexed by a lattice
point `idx : Fin m → ℤ`, one integer per coordinate.  The greedy family
keeps a cube iff it lies in `U` but its parent does not; the nesting
dichotomy is per-coordinate integer arithmetic (`omega`). -/

section Dyadic

variable {U : Set (EM m)} {σ : ℝ}

/-- Side length of generation-`k` dyadic cubes. -/
private def dside (σ : ℝ) (k : ℕ) : ℝ := σ / 2 ^ k

/-- Center of the generation-`k` dyadic cube with lattice point `idx`. -/
private def dctr (σ : ℝ) (k : ℕ) (idx : Fin m → ℤ) : EM m :=
  (WithLp.toLp 2 (fun l => ((idx l : ℝ) + 1 / 2) * dside σ k) : EM m)

/-- The generation-`k` dyadic cube with lattice point `idx`. -/
private def dsq (σ : ℝ) (k : ℕ) (idx : Fin m → ℤ) : Set (EM m) :=
  closedCube (dctr σ k idx) (dside σ k)

private lemma dside_pos (hσ : 0 < σ) (k : ℕ) : 0 < dside σ k := by
  unfold dside; positivity

private lemma dside_le (hσ : 0 < σ) (k : ℕ) : dside σ k ≤ σ := by
  unfold dside
  rw [div_le_iff₀ (by positivity)]
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  nlinarith

private lemma dside_succ (σ : ℝ) (k : ℕ) : dside σ (k + 1) * 2 = dside σ k := by
  unfold dside
  rw [pow_succ]
  field_simp

private lemma dctr_apply (σ : ℝ) (k : ℕ) (idx : Fin m → ℤ) (l : Fin m) :
    (dctr σ k idx) l = ((idx l : ℝ) + 1 / 2) * dside σ k := rfl

/-- Coordinatewise membership in a dyadic cube. -/
private lemma mem_dsq {k : ℕ} {idx : Fin m → ℤ} {x : EM m} :
    x ∈ dsq σ k idx ↔
      ∀ l, (idx l : ℝ) * dside σ k ≤ x l ∧ x l ≤ ((idx l : ℝ) + 1) * dside σ k := by
  unfold dsq closedCube
  rw [Set.mem_setOf_eq]
  refine forall_congr' fun l => ?_
  rw [dctr_apply, abs_le]
  constructor
  · rintro ⟨ha, hb⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩; exact ⟨by linarith, by linarith⟩

/-- Coordinatewise membership in an open dyadic cube. -/
private lemma mem_dsq_open {k : ℕ} {idx : Fin m → ℤ} {x : EM m} :
    x ∈ openCube (dctr σ k idx) (dside σ k) ↔
      ∀ l, (idx l : ℝ) * dside σ k < x l ∧ x l < ((idx l : ℝ) + 1) * dside σ k := by
  unfold openCube
  rw [Set.mem_setOf_eq]
  refine forall_congr' fun l => ?_
  rw [dctr_apply, abs_lt]
  constructor
  · rintro ⟨ha, hb⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩; exact ⟨by linarith, by linarith⟩

/-- **Nesting, one axis**: if the open dyadic intervals of generations
`k ≤ k'` overlap, the finer one is contained in the coarser one. -/
private lemma interval_nest (hσ : 0 < σ) {k k' : ℕ} (hkk : k ≤ k') {i i' : ℤ} {t : ℝ}
    (h1 : (i : ℝ) * dside σ k < t) (h2 : t < ((i : ℝ) + 1) * dside σ k)
    (h1' : (i' : ℝ) * dside σ k' < t) (h2' : t < ((i' : ℝ) + 1) * dside σ k') :
    (i : ℝ) * dside σ k ≤ (i' : ℝ) * dside σ k'
      ∧ ((i' : ℝ) + 1) * dside σ k' ≤ ((i : ℝ) + 1) * dside σ k := by
  have hL'pos : 0 < dside σ k' := dside_pos hσ k'
  set n : ℕ := k' - k with hn
  have hLk : dside σ k = (2 : ℝ) ^ n * dside σ k' := by
    unfold dside
    rw [show k' = n + k by omega, pow_add]
    field_simp
  set q : ℤ := i * 2 ^ n with hq
  have hqL : (q : ℝ) * dside σ k' = (i : ℝ) * dside σ k := by
    rw [hq, hLk]; push_cast; ring
  have hq2L : ((q : ℝ) + 2 ^ n) * dside σ k' = ((i : ℝ) + 1) * dside σ k := by
    rw [hq, hLk]; push_cast; ring
  have hle1 : q ≤ i' := by
    have hlt : (q : ℝ) * dside σ k' < ((i' : ℝ) + 1) * dside σ k' := by
      rw [hqL]; exact h1.trans h2'
    have hqi : (q : ℝ) < (i' : ℝ) + 1 := lt_of_mul_lt_mul_right hlt hL'pos.le
    have hcast : (q : ℝ) < ((i' + 1 : ℤ) : ℝ) := by push_cast; linarith
    have : q < i' + 1 := by exact_mod_cast hcast
    omega
  have hle2 : i' + 1 ≤ q + 2 ^ n := by
    have hlt : (i' : ℝ) * dside σ k' < ((q : ℝ) + 2 ^ n) * dside σ k' := by
      rw [hq2L]; exact h1'.trans h2
    have hqi : (i' : ℝ) < (q : ℝ) + 2 ^ n := lt_of_mul_lt_mul_right hlt hL'pos.le
    have hcast : ((i' : ℤ) : ℝ) < ((q + 2 ^ n : ℤ) : ℝ) := by push_cast; linarith
    have : i' < q + 2 ^ n := by exact_mod_cast hcast
    omega
  constructor
  · rw [← hqL]
    have : ((q : ℤ) : ℝ) ≤ ((i' : ℤ) : ℝ) := by exact_mod_cast hle1
    exact mul_le_mul_of_nonneg_right this hL'pos.le
  · rw [← hq2L]
    have h : ((i' + 1 : ℤ) : ℝ) ≤ ((q + 2 ^ n : ℤ) : ℝ) := by exact_mod_cast hle2
    have h' : ((i' : ℝ) + 1) ≤ (q : ℝ) + 2 ^ n := by push_cast at h; linarith
    exact mul_le_mul_of_nonneg_right h' hL'pos.le

/-- Nesting for cubes: overlapping open cubes of generations `k ≤ k'`
force the finer closed cube inside the coarser one. -/
private lemma dsq_nest (hσ : 0 < σ) {k k' : ℕ} (hkk : k ≤ k') {idx idx' : Fin m → ℤ}
    {x : EM m}
    (hx : x ∈ openCube (dctr σ k idx) (dside σ k))
    (hx' : x ∈ openCube (dctr σ k' idx') (dside σ k')) :
    dsq σ k' idx' ⊆ dsq σ k idx := by
  rw [mem_dsq_open] at hx hx'
  intro y hy
  rw [mem_dsq] at hy ⊢
  intro l
  obtain ⟨hA, hB⟩ := interval_nest hσ hkk (hx l).1 (hx l).2 (hx' l).1 (hx' l).2
  exact ⟨hA.trans (hy l).1, (hy l).2.trans hB⟩

/-- Same-generation open cubes that overlap are identical. -/
private lemma dsq_eq_of_open_inter (hσ : 0 < σ) {k : ℕ} {idx idx' : Fin m → ℤ}
    {x : EM m}
    (hx : x ∈ openCube (dctr σ k idx) (dside σ k))
    (hx' : x ∈ openCube (dctr σ k idx') (dside σ k)) :
    idx = idx' := by
  have hLpos := dside_pos hσ k
  rw [mem_dsq_open] at hx hx'
  funext l
  obtain ⟨hA, -⟩ := interval_nest hσ le_rfl (hx l).1 (hx l).2 (hx' l).1 (hx' l).2
  obtain ⟨hA', -⟩ := interval_nest hσ le_rfl (hx' l).1 (hx' l).2 (hx l).1 (hx l).2
  have : (idx l : ℝ) = (idx' l : ℝ) :=
    mul_right_cancel₀ hLpos.ne' (le_antisymm hA hA')
  exact_mod_cast this

/-- Each dyadic cube is contained in its parent (coordinatewise halving
of the lattice point). -/
private lemma dsq_subset_parent (hσ : 0 < σ) (k : ℕ) (idx : Fin m → ℤ) :
    dsq σ (k + 1) idx ⊆ dsq σ k (fun l => idx l / 2) := by
  have hL := dside_succ σ k
  have hL'pos := dside_pos hσ (k + 1)
  intro y hy
  rw [mem_dsq] at hy ⊢
  intro l
  have hta := (hy l).1
  have htb := (hy l).2
  set a := idx l with ha
  set t := y l with ht
  have hdiv1 : ((a / 2 : ℤ) : ℝ) * 2 ≤ (a : ℝ) := by
    have : (a / 2) * 2 ≤ a := by omega
    exact_mod_cast this
  have hdiv2 : ((a : ℝ) + 1) ≤ (((a / 2 : ℤ) : ℝ) + 1) * 2 := by
    have : a + 1 ≤ (a / 2 + 1) * 2 := by omega
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · show ((idx l / 2 : ℤ) : ℝ) * dside σ k ≤ y l
    calc ((a / 2 : ℤ) : ℝ) * dside σ k
        = ((a / 2 : ℤ) : ℝ) * 2 * dside σ (k+1) := by rw [← hL]; ring
      _ ≤ (a : ℝ) * dside σ (k+1) := mul_le_mul_of_nonneg_right hdiv1 hL'pos.le
      _ ≤ t := hta
  · show y l ≤ (((idx l / 2 : ℤ) : ℝ) + 1) * dside σ k
    calc t ≤ ((a : ℝ) + 1) * dside σ (k+1) := htb
      _ ≤ (((a / 2 : ℤ) : ℝ) + 1) * 2 * dside σ (k+1) :=
          mul_le_mul_of_nonneg_right hdiv2 hL'pos.le
      _ = (((a / 2 : ℤ) : ℝ) + 1) * dside σ k := by rw [← hL]; ring

/-- The greedy dyadic family: generation-`k` cubes inside `U` whose
parent (for `k > 0`) is not inside `U`. -/
private def dFam (σ : ℝ) (U : Set (EM m)) : Set (ℕ × (Fin m → ℤ)) :=
  {p | dsq σ p.1 p.2 ⊆ U ∧
    ∀ k₀, p.1 = k₀ + 1 → ¬ dsq σ k₀ (fun l => p.2 l / 2) ⊆ U}

/-- Every point of the open set lies in a member of the greedy family. -/
private lemma exists_dsq_mem (hσ : 0 < σ) (hU : IsOpen U) {x : EM m} (hx : x ∈ U) :
    ∃ p ∈ dFam σ U, x ∈ dsq σ p.1 p.2 := by
  classical
  set I : ℕ → Fin m → ℤ := fun k l => ⌊x l / dside σ k⌋ with hI
  have hmem : ∀ k, x ∈ dsq σ k (I k) := by
    intro k
    have hL := dside_pos hσ k
    rw [mem_dsq]
    intro l
    constructor
    · exact (le_div_iff₀ hL).mp (Int.floor_le (x l / dside σ k))
    · have h1 := Int.lt_floor_add_one (x l / dside σ k)
      have h2 := (div_lt_iff₀ hL).mp h1
      push_cast at h2 ⊢
      linarith
  have hsmall : ∃ k, dsq σ k (I k) ⊆ U := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (σ * Real.sqrt m / r) one_lt_two
    refine ⟨n, fun y hy => hball ?_⟩
    have hLn := dside_pos hσ n
    rw [Metric.mem_ball]
    have hx' := hmem n
    rw [mem_dsq] at hy hx'
    -- Each coordinate deviates by at most one cell width.
    have ecoord : ∀ l, |y l - x l| ≤ dside σ n := by
      intro l
      rw [abs_le]
      exact ⟨by linarith [(hy l).1, (hx' l).2], by linarith [(hy l).2, (hx' l).1]⟩
    -- Hence the Euclidean distance is at most `dside · √m`.
    have hb : ∑ l, dist (y l) (x l) ^ 2 ≤ (m : ℝ) * dside σ n ^ 2 := by
      calc ∑ l, dist (y l) (x l) ^ 2
          ≤ ∑ _l : Fin m, dside σ n ^ 2 := by
            refine Finset.sum_le_sum fun l _ => ?_
            rw [Real.dist_eq]
            nlinarith [ecoord l, abs_nonneg (y l - x l)]
        _ = (m : ℝ) * dside σ n ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hdist : dist y x ≤ dside σ n * Real.sqrt m := by
      rw [EuclideanSpace.dist_eq]
      calc Real.sqrt (∑ l, dist (y l) (x l) ^ 2)
          ≤ Real.sqrt ((m : ℝ) * dside σ n ^ 2) := Real.sqrt_le_sqrt hb
        _ = dside σ n * Real.sqrt m := by
            rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hLn.le]
            ring
    have hfin : dside σ n * Real.sqrt m < r := by
      unfold dside
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hr] at hn
      linarith
    exact lt_of_le_of_lt hdist hfin
  set khat := Nat.find hsmall with hkhat
  have hspec : dsq σ khat (I khat) ⊆ U := Nat.find_spec hsmall
  refine ⟨(khat, I khat), ⟨hspec, ?_⟩, hmem khat⟩
  intro k₀ hk₀
  have hk : khat = k₀ + 1 := hk₀
  have hmin := Nat.find_min hsmall (show k₀ < khat by omega)
  have hdiv : (fun l => I khat l / 2) = I k₀ := by
    funext l
    have hstep : x l / dside σ k₀ = x l / dside σ khat / 2 := by
      rw [hk]; unfold dside; rw [pow_succ]; field_simp
    show ⌊x l / dside σ khat⌋ / 2 = ⌊x l / dside σ k₀⌋
    rw [hstep, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Int.floor_div_natCast]
    norm_num
  rw [hdiv]
  exact hmin

/-- Distinct members of the greedy family have disjoint open cubes. -/
private lemma dFam_open_disjoint (hσ : 0 < σ) {p q : ℕ × (Fin m → ℤ)}
    (hp : p ∈ dFam σ U) (hq : q ∈ dFam σ U) (hpq : p ≠ q) {x : EM m}
    (hxp : x ∈ openCube (dctr σ p.1 p.2) (dside σ p.1))
    (hxq : x ∈ openCube (dctr σ q.1 q.2) (dside σ q.1)) : False := by
  wlog hkk : p.1 ≤ q.1 generalizing p q with H
  · exact H hq hp (Ne.symm hpq) hxq hxp (le_of_not_ge hkk)
  rcases Nat.eq_or_lt_of_le hkk with heq | hlt
  · obtain ⟨pk, pidx⟩ := p
    obtain ⟨qk, qidx⟩ := q
    simp only at heq hxp hxq
    subst heq
    have hidx := dsq_eq_of_open_inter hσ hxp hxq
    exact hpq (by simp [hidx])
  · obtain ⟨k₀, hk₀⟩ : ∃ k₀, q.1 = k₀ + 1 := ⟨q.1 - 1, by omega⟩
    have hxparent : x ∈ openCube (dctr σ k₀ (fun l => q.2 l / 2)) (dside σ k₀) := by
      apply interior_closedCube_subset _ (dside_pos hσ _)
      have hsub : openCube (dctr σ q.1 q.2) (dside σ q.1)
          ⊆ dsq σ k₀ (fun l => q.2 l / 2) := by
        refine (openCube_subset_closedCube _ _).trans ?_
        intro y hy
        rw [hk₀] at hy
        exact dsq_subset_parent hσ k₀ q.2 hy
      exact interior_maximal hsub (isOpen_openCube _ _) hxq
    have hsubparent : dsq σ k₀ (fun l => q.2 l / 2) ⊆ dsq σ p.1 p.2 :=
      dsq_nest hσ (by omega) hxp hxparent
    exact (hq.2 k₀ hk₀) (hsubparent.trans hp.1)

/-- The greedy family is infinite: if it were finite, `U` would be a
finite union of compact cubes, hence closed; but a nonempty open set is
closed only if it is all of `ℝᵐ`, which (as `m > 0`) contains
infinitely many cubes.  This is the one step that needs `m > 0`. -/
private lemma dFam_infinite (hm : 0 < m) (hσ : 0 < σ) (hU : IsOpen U)
    (hne : U.Nonempty) : (dFam σ U).Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hUeq : U = ⋃ p ∈ dFam σ U, dsq σ p.1 p.2 := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := exists_dsq_mem hσ hU hx
      exact Set.mem_biUnion hp hxp
    · exact Set.iUnion₂_subset fun p hp => hp.1
  have hclosed : IsClosed U := by
    rw [hUeq]
    exact hfin.isClosed_biUnion fun p _ => (isCompact_closedCube _ (dside_pos hσ _).le).isClosed
  have huniv : U = Set.univ := IsClopen.eq_univ ⟨hclosed, hU⟩ hne
  -- Infinitely many generation-0 cubes, distinguished by their first
  -- coordinate.
  have hinf2 : (dFam σ U).Infinite := by
    apply Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => ((0 : ℕ),
        Function.update (fun _ : Fin m => (0 : ℤ)) ⟨0, hm⟩ (n : ℤ)))
    · intro a b hab
      have h2 := congrArg (fun p => (p.2 ⟨0, hm⟩)) hab
      simp only [Function.update_self] at h2
      exact_mod_cast h2
    · intro n
      refine ⟨?_, fun k₀ h => absurd h (by omega)⟩
      rw [huniv]
      exact Set.subset_univ _
  exact hinf2 hfin

/-- **Dyadic decomposition of open sets**: a nonempty open set (in `ℝᵐ`,
`m > 0`) is the union of countably many non-overlapping closed dyadic
cubes of side at most `σ`, all contained in it. -/
theorem dyadic_decomposition (hm : 0 < m) {U : Set (EM m)} (hU : IsOpen U)
    (hne : U.Nonempty) {σ : ℝ} (hσ : 0 < σ) :
    ∃ (z : ℕ → EM m) (s : ℕ → ℝ),
      (∀ n, 0 < s n ∧ s n ≤ σ ∧ closedCube (z n) (s n) ⊆ U) ∧
      (Pairwise fun a b =>
        interior (closedCube (z a) (s a)) ∩
          interior (closedCube (z b) (s b)) = ∅) ∧
      (⋃ n, closedCube (z n) (s n)) = U := by
  have hinf := dFam_infinite hm hσ hU hne
  have hctble : (dFam σ U).Countable := Set.to_countable _
  haveI := hctble.to_subtype
  haveI := hinf.to_subtype
  obtain ⟨d⟩ := nonempty_denumerable ↥(dFam σ U)
  set e : ℕ ≃ ↥(dFam σ U) := (Denumerable.eqv ↥(dFam σ U)).symm with he
  refine ⟨fun n => dctr σ (e n).1.1 (e n).1.2,
    fun n => dside σ (e n).1.1,
    fun n => ⟨dside_pos hσ _, dside_le hσ _, ((e n).2).1⟩, ?_, ?_⟩
  · intro a b hab
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxa, hxb⟩
    have hxa' := interior_closedCube_subset _ (dside_pos hσ (e a).1.1) hxa
    have hxb' := interior_closedCube_subset _ (dside_pos hσ (e b).1.1) hxb
    have hne' : ((e a) : ℕ × (Fin m → ℤ)) ≠ ((e b) : ℕ × (Fin m → ℤ)) := by
      intro h
      exact hab (e.injective (Subtype.ext h))
    exact dFam_open_disjoint hσ (e a).2 (e b).2 hne' hxa' hxb'
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun n => ((e n).2).1
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := exists_dsq_mem hσ hU hx
      refine Set.mem_iUnion.mpr ⟨e.symm ⟨p, hp⟩, ?_⟩
      simp only [Equiv.apply_symm_apply]
      exact hxp

end Dyadic

/-! ## Graphs over volume-null bases are area-null -/

/-- On a compact convex subset of `U`, a C¹ function has Lipschitz graph
map (bounded derivative + mean value inequality).  This is the tool for
transporting `μH`-nullness from the base to the graph. -/
lemma exists_lipschitzOnWith_graphMap {U : Set (EM m)} {f : EM m → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) {K : Set (EM m)} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKU : K ⊆ U) :
    ∃ L : ℝ≥0, LipschitzOnWith L (graphMap f) K := by
  have hcont : ContinuousOn (fderiv ℝ f) K :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  set C' := max C 0 with hC'def
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hflip : LipschitzOnWith C'.toNNReal f K := by
    refine hKc.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := fun x => fderiv ℝ f x) (fun x hx => ?_) (fun x hx => ?_)
    · exact (((hf.differentiableOn one_ne_zero).differentiableAt
        (hU.mem_nhds (hKU hx))).hasFDerivAt).hasFDerivWithinAt
    · rw [← norm_toNNReal]
      exact Real.toNNReal_mono ((hC x hx).trans (le_max_left _ _))
  refine ⟨1 + C'.toNNReal, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm, graphMap_sub]
  have hfxy : |f x - f y| ≤ C' * ‖x - y‖ := by
    have h := hflip.dist_le_mul x hx y hy
    rw [Real.dist_eq, Real.coe_toNNReal _ hC0, dist_eq_norm] at h
    exact h
  calc ‖(WithLp.toLp 2 (x - y, f x - f y) : EN m)‖
      ≤ ‖x - y‖ + |f x - f y| := norm_toLp_le _ _
    _ ≤ ‖x - y‖ + C' * ‖x - y‖ := by linarith
    _ = ((1 + C'.toNNReal : ℝ≥0) : ℝ) * dist x y := by
        rw [dist_eq_norm]
        push_cast [Real.coe_toNNReal _ hC0]
        ring

/-- **Graphs over volume-null bases are `μHE[m]`-null.**

If `S ⊆ K` has `volume S = 0`, then `μHE[m](Γ_f|_S) = 0`.  Proof:
`volume`-null implies `μH[m]`-null on `ℝᵐ` by *abstract* Haar
uniqueness (mutual absolute continuity of Haar measures — no explicit
normalization constant needed), and the Lipschitz graph map sends
`μH[m]`-null sets to `μH[m]`-null sets.  This is what makes the cube
frontiers (volume-null) negligible for the surface area. -/
lemma graph_null_of_volume_null {U : Set (EM m)} {f : EM m → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {K S : Set (EM m)} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKU : K ⊆ U) (hSK : S ⊆ K) (hS : volume S = 0) :
    μHE[m] (graph f S) = 0 := by
  have hμHS : μH[(m : ℝ)] S = 0 := by
    have key : (μH[((m : ℕ) : ℝ)] : Measure (EM m))
        = addHaarScalarFactor (μH[((m : ℕ) : ℝ)] : Measure (EM m)) volume • volume :=
      Measure.isAddLeftInvariant_eq_smul _ _
    rw [key, Measure.smul_apply, hS, smul_zero]
  obtain ⟨L, hlip⟩ := exists_lipschitzOnWith_graphMap hU hf hK hKc hKU
  have himg : μH[(m : ℝ)] (graph f S) = 0 := by
    refine le_antisymm ?_ zero_le
    calc μH[(m : ℝ)] (graphMap f '' S)
        ≤ (L : ℝ≥0∞) ^ (m : ℝ) * μH[(m : ℝ)] S :=
          (hlip.mono hSK).hausdorffMeasure_image_le (by positivity)
      _ = 0 := by rw [hμHS, mul_zero]
  rw [Measure.euclideanHausdorffMeasure_def]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [himg, mul_zero]

/-! ## Grid machinery for the Riemann-sum argument -/

/-- Coordinatewise membership in a closed cube. -/
private lemma mem_closedCube_iff {c : EM m} {t : ℝ} {x : EM m} :
    x ∈ closedCube c t ↔
      ∀ l, (c l - t / 2 ≤ x l ∧ x l ≤ c l + t / 2) := by
  unfold closedCube
  rw [Set.mem_setOf_eq]
  refine forall_congr' fun l => ?_
  rw [abs_le]
  constructor
  · rintro ⟨u1, u2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨u1, u2⟩; exact ⟨by linarith, by linarith⟩

/-- Coordinatewise membership in an open cube. -/
private lemma mem_openCube_iff {c : EM m} {t : ℝ} {x : EM m} :
    x ∈ openCube c t ↔
      ∀ l, (c l - t / 2 < x l ∧ x l < c l + t / 2) := by
  unfold openCube
  rw [Set.mem_setOf_eq]
  refine forall_congr' fun l => ?_
  rw [abs_lt]
  constructor
  · rintro ⟨u1, u2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨u1, u2⟩; exact ⟨by linarith, by linarith⟩

/-- 1-D grid selection: any `t ∈ [0, N·h]` lies in some cell
`[i·h, (i+1)·h]` with `i < N`. -/
private lemma exists_grid_index {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N) {t : ℝ}
    (h1 : 0 ≤ t) (h2 : t ≤ N * h) :
    ∃ i : ℕ, i < N ∧ i * h ≤ t ∧ t ≤ (i + 1) * h := by
  classical
  set i0 : ℤ := ⌊t / h⌋ with hi0
  have hi0nn : 0 ≤ i0 := Int.floor_nonneg.mpr (by positivity)
  have hi0le : i0 ≤ N := by
    have ht : t / h ≤ N := by rw [div_le_iff₀ hh]; linarith
    calc i0 ≤ ⌊(N : ℝ)⌋ := Int.floor_le_floor ht
      _ = N := Int.floor_natCast N
  rcases lt_or_ge i0 N with hlt | hge
  · refine ⟨i0.toNat, by omega, ?_, ?_⟩
    · have hfl : (i0 : ℝ) * h ≤ t := (le_div_iff₀ hh).mp (Int.floor_le _)
      have hcast : ((i0.toNat : ℕ) : ℝ) = (i0 : ℝ) := by
        exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (Int.toNat_of_nonneg hi0nn)
      rw [hcast]; exact hfl
    · have hfl := Int.lt_floor_add_one (t / h)
      have hfl2 : t < ((i0 : ℝ) + 1) * h := by rw [← div_lt_iff₀ hh]; exact hfl
      have hcast : ((i0.toNat : ℕ) : ℝ) = (i0 : ℝ) := by
        exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (Int.toNat_of_nonneg hi0nn)
      rw [hcast]; exact hfl2.le
  · have hi0N : i0 = N := le_antisymm hi0le hge
    have htop : (N : ℝ) ≤ t / h := by
      have hfl := Int.floor_le (t / h)
      rw [hi0] at hi0N
      rw [hi0N] at hfl
      exact_mod_cast hfl
    have hteq : t = N * h := le_antisymm h2 ((le_div_iff₀ hh).mp htop)
    refine ⟨N - 1, by omega, ?_, ?_⟩
    · have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        have : (1 : ℕ) ≤ N := hN
        push_cast [Nat.cast_sub this]; ring
      rw [hcast, hteq]; nlinarith
    · have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
        have : (1 : ℕ) ≤ N := hN
        push_cast [Nat.cast_sub this]; ring
      rw [hcast, hteq]

/-- 1-D grid cells with distinct indices have disjoint open interiors. -/
private lemma grid_index_eq {h : ℝ} (hh : 0 < h) {a t : ℝ} {i i' : ℕ}
    (H1 : a + i * h < t) (H2 : t < a + (i + 1) * h)
    (H1' : a + i' * h < t) (H2' : t < a + (i' + 1) * h) : i = i' := by
  have c1 : (i : ℝ) * h < ((i' : ℝ) + 1) * h := by nlinarith
  have c2 : (i' : ℝ) * h < ((i : ℝ) + 1) * h := by nlinarith
  have d1 : (i : ℝ) < (i' : ℝ) + 1 := lt_of_mul_lt_mul_right c1 hh.le
  have d2 : (i' : ℝ) < (i : ℝ) + 1 := lt_of_mul_lt_mul_right c2 hh.le
  have e1 : i < i' + 1 := by exact_mod_cast d1
  have e2 : i' < i + 1 := by exact_mod_cast d2
  omega

/-- The map `a ↦ √(1 + a²)` is 1-Lipschitz on nonnegative reals. -/
private lemma sqrt_one_add_sq_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt (1 + a ^ 2) - Real.sqrt (1 + b ^ 2)| ≤ |a - b| := by
  wlog hab : b ≤ a generalizing a b with H
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact H hb ha (by linarith)
  set u := Real.sqrt (1 + a ^ 2) with hu
  set v := Real.sqrt (1 + b ^ 2) with hv
  have hu2 : u ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = 1 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hupos : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hvpos : 0 < v := Real.sqrt_pos.mpr (by positivity)
  have hbv : b ≤ v := by nlinarith
  have hau : a ≤ u := by nlinarith
  have huv : v ≤ u := by rw [hu, hv]; exact Real.sqrt_le_sqrt (by nlinarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab)
    (by linarith : (0:ℝ) ≤ u + v - (a + b))]

/-- The Jacobian oscillates no more than the derivative. -/
private lemma abs_jac_sub_le {f : EM m → ℝ} {x y : EM m} {ε : ℝ}
    (h : ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ ε) : |jac f x - jac f y| ≤ ε := by
  unfold jac
  calc |Real.sqrt (1 + ‖fderiv ℝ f x‖ ^ 2) - Real.sqrt (1 + ‖fderiv ℝ f y‖ ^ 2)|
      ≤ |‖fderiv ℝ f x‖ - ‖fderiv ℝ f y‖| :=
        sqrt_one_add_sq_sub_le (norm_nonneg _) (norm_nonneg _)
    _ ≤ ‖fderiv ℝ f x - fderiv ℝ f y‖ := abs_norm_sub_norm_le _ _
    _ ≤ ε := h

/-- Splitting a set-lintegral along a finite tiling by cubes whose open
interiors are pairwise disjoint. -/
private lemma lintegral_grid_split {ι : Type*} [Fintype ι] {R : Set (EM m)}
    (c : ι → EM m) (t : ι → ℝ) (ht : ∀ p, 0 < t p)
    (hdisj : Pairwise fun p q =>
      openCube (c p) (t p) ∩ openCube (c q) (t q) = ∅)
    (hcover : (⋃ p, closedCube (c p) (t p)) = R) (g : EM m → ℝ≥0∞) :
    ∫⁻ z in R, g z = ∑ p, ∫⁻ z in closedCube (c p) (t p), g z := by
  have hfr : ∀ p, volume (closedCube (c p) (t p)
      \ interior (closedCube (c p) (t p))) = 0 :=
    fun p => volume_frontier_closedCube _ (ht p).le
  have hae : ∀ p, (closedCube (c p) (t p) : Set (EM m))
      =ᵐ[volume] interior (closedCube (c p) (t p)) := by
    intro p
    rw [MeasureTheory.ae_eq_set]
    exact ⟨hfr p, by
      rw [Set.diff_eq_empty.mpr interior_subset]
      exact measure_empty⟩
  have hdisj' : Pairwise (Function.onFun Disjoint
      fun p => interior (closedCube (c p) (t p))) := by
    intro p q hpq
    apply Set.disjoint_iff_inter_eq_empty.mpr
    apply Set.eq_empty_of_subset_empty
    rw [← hdisj hpq]
    exact Set.inter_subset_inter (interior_closedCube_subset _ (ht p))
      (interior_closedCube_subset _ (ht q))
  have hRae : (R : Set (EM m)) =ᵐ[volume] ⋃ p, interior (closedCube (c p) (t p)) := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (measure_iUnion_null hfr)
      intro x hx
      obtain ⟨hxR, hxint⟩ := hx
      rw [← hcover] at hxR
      obtain ⟨-, ⟨p, rfl⟩, hxp⟩ := hxR
      simp only [Set.mem_iUnion, not_exists] at hxint
      exact Set.mem_iUnion.mpr ⟨p, hxp, hxint p⟩
    · rw [Set.diff_eq_empty.mpr ?_]
      · exact measure_empty
      · rw [← hcover]
        exact Set.iUnion_mono fun p => interior_subset
  rw [setLIntegral_congr hRae,
    lintegral_iUnion (fun p => isOpen_interior.measurableSet) hdisj', tsum_fintype]
  exact Finset.sum_congr rfl fun p _ => (setLIntegral_congr (hae p)).symm

private lemma le_of_forall_pos_le_add' {a b : ℝ} (h : ∀ η, 0 < η → a ≤ b + η) :
    a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  have := h ((a - b) / 2) (by linarith)
  linarith

/-- The center of a closed cube belongs to it. -/
private lemma center_mem_closedCube (c : EM m) {h : ℝ} (hh : 0 ≤ h) :
    c ∈ closedCube c h := by
  intro l
  rw [sub_self, abs_zero]
  exact div_nonneg hh (by norm_num)

/-- The `Nᵐ` grid of closed subcubes of `closedCube z₀ s` (side `s/N`):
the cells sit inside the cube, tile it, and have pairwise disjoint
interiors.  Cells are indexed by lattice points `Fin m → Fin N`. -/
private lemma exists_grid (z₀ : EM m) {s : ℝ} (hs : 0 < s) {N : ℕ}
    (hNpos : 0 < N) :
    ∃ ctr : (Fin m → Fin N) → EM m,
      (∀ p, closedCube (ctr p) (s / N) ⊆ closedCube z₀ s) ∧
      (⋃ p : Fin m → Fin N, closedCube (ctr p) (s / N)) = closedCube z₀ s ∧
      Pairwise fun p q : Fin m → Fin N =>
        openCube (ctr p) (s / N) ∩ openCube (ctr q) (s / N) = ∅ := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set h := s / N with hh
  have hhpos : 0 < h := by rw [hh]; positivity
  have hNh : (N : ℝ) * h = s := by rw [hh]; field_simp
  set a : Fin m → ℝ := fun l => z₀ l - s / 2 with ha
  set ctr : (Fin m → Fin N) → EM m := fun p =>
    (WithLp.toLp 2 (fun l => a l + ((p l : ℝ) + 1 / 2) * h) : EM m) with hctr
  have hctrl : ∀ (p : Fin m → Fin N) (l : Fin m),
      (ctr p) l = a l + ((p l : ℝ) + 1 / 2) * h := fun p l => rfl
  have hmemQ : ∀ (p : Fin m → Fin N) (x : EM m), x ∈ closedCube (ctr p) h ↔
      ∀ l, (a l + (p l : ℝ) * h ≤ x l ∧ x l ≤ a l + ((p l : ℝ) + 1) * h) := by
    intro p x
    rw [mem_closedCube_iff]
    refine forall_congr' fun l => ?_
    rw [hctrl]
    constructor
    · rintro ⟨u1, u2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨u1, u2⟩; exact ⟨by linarith, by linarith⟩
  have hmemQopen : ∀ (p : Fin m → Fin N) (x : EM m), x ∈ openCube (ctr p) h ↔
      ∀ l, (a l + (p l : ℝ) * h < x l ∧ x l < a l + ((p l : ℝ) + 1) * h) := by
    intro p x
    rw [mem_openCube_iff]
    refine forall_congr' fun l => ?_
    rw [hctrl]
    constructor
    · rintro ⟨u1, u2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨u1, u2⟩; exact ⟨by linarith, by linarith⟩
  have hmemR : ∀ x : EM m, x ∈ closedCube z₀ s ↔
      ∀ l, (a l ≤ x l ∧ x l ≤ a l + s) := by
    intro x
    rw [mem_closedCube_iff]
    refine forall_congr' fun l => ?_
    rw [ha]
    constructor
    · rintro ⟨u1, u2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨u1, u2⟩; exact ⟨by linarith, by linarith⟩
  have hQR : ∀ p : Fin m → Fin N, closedCube (ctr p) h ⊆ closedCube z₀ s := by
    intro p x hx
    rw [hmemQ] at hx
    rw [hmemR]
    intro l
    have hp1 : (p l : ℝ) + 1 ≤ N := by exact_mod_cast (p l).is_lt
    have hm1 : (0 : ℝ) ≤ (p l : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hhpos.le
    have hm3 : ((p l : ℝ) + 1) * h ≤ (N : ℝ) * h :=
      mul_le_mul_of_nonneg_right hp1 hhpos.le
    exact ⟨by linarith [(hx l).1], by linarith [(hx l).2, hNh.le, hNh.ge]⟩
  have hcover : (⋃ p : Fin m → Fin N, closedCube (ctr p) h) = closedCube z₀ s := by
    apply Set.Subset.antisymm (Set.iUnion_subset hQR)
    intro x hx
    rw [hmemR] at hx
    choose i hiN hi1 hi2 using fun l => exists_grid_index hhpos hNpos
      (by linarith [(hx l).1] : (0:ℝ) ≤ x l - a l)
      (by rw [hNh]; linarith [(hx l).2] : x l - a l ≤ (N : ℝ) * h)
    refine Set.mem_iUnion.mpr ⟨fun l => ⟨i l, hiN l⟩, ?_⟩
    rw [hmemQ]
    intro l
    constructor
    · show a l + ((⟨i l, hiN l⟩ : Fin N) : ℝ) * h ≤ x l
      linarith [hi1 l]
    · show x l ≤ a l + (((⟨i l, hiN l⟩ : Fin N) : ℝ) + 1) * h
      linarith [hi2 l]
  have hodisj : Pairwise fun p q : Fin m → Fin N =>
      openCube (ctr p) h ∩ openCube (ctr q) h = ∅ := by
    intro p q hpq
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxp, hxq⟩
    rw [hmemQopen] at hxp hxq
    apply hpq
    funext l
    apply Fin.ext
    exact grid_index_eq hhpos (a := a l) (t := x l)
      (hxp l).1 (hxp l).2 (hxq l).1 (hxq l).2
  exact ⟨ctr, hQR, hcover, hodisj⟩

/-- Graphs over two subcubes of `U` with disjoint interiors overlap in a
`μHE[m]`-null set: the overlap lies over the (volume-null) cell
frontiers, and volume-null bases carry area-null graphs. -/
private lemma graph_inter_null {U : Set (EM m)} {f : EM m → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {c₁ c₂ : EM m} {h : ℝ} (hh : 0 < h)
    (h₁ : closedCube c₁ h ⊆ U) (h₂ : closedCube c₂ h ⊆ U)
    (hdisj : openCube c₁ h ∩ openCube c₂ h = ∅) :
    μHE[m] (graph f (closedCube c₁ h) ∩ graph f (closedCube c₂ h)) = 0 := by
  have hinter : graph f (closedCube c₁ h) ∩ graph f (closedCube c₂ h)
      = graph f (closedCube c₁ h ∩ closedCube c₂ h) := by
    rw [graph, graph, graph, ← Set.image_inter graphMap_injective]
  rw [hinter]
  refine le_antisymm ?_ zero_le
  have hsubfr : closedCube c₁ h ∩ closedCube c₂ h
      ⊆ (closedCube c₁ h \ interior (closedCube c₁ h))
        ∪ (closedCube c₂ h \ interior (closedCube c₂ h)) := by
    rintro x ⟨hxp, hxq⟩
    by_cases hx : x ∈ interior (closedCube c₁ h)
    · refine Or.inr ⟨hxq, fun hx' => ?_⟩
      have hi1 := interior_closedCube_subset _ hh hx
      have hi2 := interior_closedCube_subset _ hh hx'
      rw [Set.eq_empty_iff_forall_notMem] at hdisj
      exact hdisj x ⟨hi1, hi2⟩
    · exact Or.inl ⟨hxp, hx⟩
  calc μHE[m] (graph f (closedCube c₁ h ∩ closedCube c₂ h))
      ≤ μHE[m] (graph f (closedCube c₁ h \ interior (closedCube c₁ h))
        ∪ graph f (closedCube c₂ h \ interior (closedCube c₂ h))) := by
        refine measure_mono ?_
        rw [graph, graph, graph, ← Set.image_union]
        exact Set.image_mono hsubfr
    _ ≤ μHE[m] (graph f (closedCube c₁ h \ interior (closedCube c₁ h)))
        + μHE[m] (graph f (closedCube c₂ h \ interior (closedCube c₂ h))) :=
        measure_union_le _ _
    _ = 0 := by
        rw [graph_null_of_volume_null hU hf (isCompact_closedCube _ hh.le)
            (convex_closedCube _ _) h₁ Set.diff_subset
            (volume_frontier_closedCube _ hh.le),
          graph_null_of_volume_null hU hf (isCompact_closedCube _ hh.le)
            (convex_closedCube _ _) h₂ Set.diff_subset
            (volume_frontier_closedCube _ hh.le), add_zero]

/-- **The `ε ↓ 0` squeeze.** Two-sided `(1 ± ε)ᵐ` estimates with an
`ε·V` slack, for all `ε ∈ (0,1)`, force `μ = I`.

*This is where the dimension-generic argument genuinely differs from the
planar one.*  With a fixed exponent one can clear `(1±ε)²` by
`nlinarith`; with a symbolic exponent `m` that is impossible, so instead
we take the limit `ε → 0⁺`: the maps `ε ↦ (1+ε)ᵐ(I+εV)` and
`ε ↦ (1−ε)ᵐ I` are continuous with value `I` at `0`, and
`le_of_tendsto_of_tendsto` passes the two-sided bound to `μ = I`. -/
private lemma eq_of_grid_estimates {μ I V : ℝ≥0∞} (hIfin : I ≠ ⊤)
    (hVfin : V ≠ ⊤)
    (key : ∀ ε : ℝ, 0 < ε → ε < 1 →
      μ ≤ ENNReal.ofReal ((1 + ε) ^ m) * (I + ENNReal.ofReal ε * V) ∧
      ENNReal.ofReal ((1 - ε) ^ m) * I ≤ μ + ENNReal.ofReal ε * V) :
    μ = I := by
  have hμfin : μ ≠ ⊤ := by
    have h2 := (key (1 / 2) (by norm_num) (by norm_num)).1
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hIfin,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin⟩)) h2
  set a := μ.toReal with ha
  set b := I.toReal with hb
  set v := V.toReal with hv
  -- Real forms of the two ℝ≥0∞ estimates.
  have hup : ∀ ε : ℝ, 0 < ε → ε < 1 → a ≤ (1 + ε) ^ m * (b + ε * v) := by
    intro ε hε0 hε1
    have hk := (key ε hε0 hε1).1
    have hfin2 : ENNReal.ofReal ((1 + ε) ^ m) * (I + ENNReal.ofReal ε * V) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hIfin,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin⟩)
    have := ENNReal.toReal_mono hfin2 hk
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hIfin
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal hε0.le] at this
    exact this
  have hlow : ∀ ε : ℝ, 0 < ε → ε < 1 → (1 - ε) ^ m * b ≤ a + ε * v := by
    intro ε hε0 hε1
    have hk := (key ε hε0 hε1).2
    have hfin2 : μ + ENNReal.ofReal ε * V ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hμfin,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin⟩
    have := ENNReal.toReal_mono hfin2 hk
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by linarith) m),
      ENNReal.toReal_add hμfin
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hε0.le] at this
    exact this
  -- Eventually along `𝓝[>] 0`, `ε` lies in `(0,1)`.
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ ε < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (show (0:ℝ) ∈ Iio 1 by norm_num))]
      with ε h1 h2 using ⟨h1, h2⟩
  -- `a ≤ b`: the upper bound's RHS tends to `b`.
  have hab : a ≤ b := by
    have hg : Tendsto (fun ε : ℝ => (1 + ε) ^ m * (b + ε * v)) (𝓝[>] (0:ℝ)) (𝓝 b) := by
      have hcont : ContinuousAt (fun ε : ℝ => (1 + ε) ^ m * (b + ε * v)) 0 := by fun_prop
      have hlim := hcont.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))
      simpa using hlim
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hg ?_
    filter_upwards [hev] with ε hε using hup ε hε.1 hε.2
  -- `b ≤ a`: the lower bound's LHS tends to `b`, its RHS to `a`.
  have hba : b ≤ a := by
    have hh1 : Tendsto (fun ε : ℝ => (1 - ε) ^ m * b) (𝓝[>] (0:ℝ)) (𝓝 b) := by
      have hcont : ContinuousAt (fun ε : ℝ => (1 - ε) ^ m * b) 0 := by fun_prop
      have hlim := hcont.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))
      simpa using hlim
    have hk1 : Tendsto (fun ε : ℝ => a + ε * v) (𝓝[>] (0:ℝ)) (𝓝 a) := by
      have hcont : ContinuousAt (fun ε : ℝ => a + ε * v) 0 := by fun_prop
      have hlim := hcont.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))
      simpa using hlim
    refine le_of_tendsto_of_tendsto hh1 hk1 ?_
    filter_upwards [hev] with ε hε using hlow ε hε.1 hε.2
  have hfinal : a = b := le_antisymm hab hba
  have h1 : μ ≤ I := (ENNReal.toReal_le_toReal hμfin hIfin).mp (le_of_eq hfinal)
  have h2 : I ≤ μ := (ENNReal.toReal_le_toReal hIfin hμfin).mp (le_of_eq hfinal.symm)
  exact le_antisymm h1 h2

/-- The two-sided grid estimate at oscillation scale `ε` (the heart of
the cube area formula): grid at a scale realizing gradient oscillation
`ε` and apply `local_area_estimate` per cell, squeezing the graph area
between `(1 ± ε)ᵐ` multiples of the Riemann sums, which in turn sit
within `ε·V` of the integral. -/
private lemma cube_grid_estimate {U : Set (EM m)} {f : EM m → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (z₀ : EM m) {s : ℝ} (hs : 0 < s)
    (hsub : closedCube z₀ s ⊆ U) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    μHE[m] (graph f (closedCube z₀ s))
      ≤ ENNReal.ofReal ((1 + ε) ^ m)
        * ((∫⁻ z in closedCube z₀ s, ENNReal.ofReal (jac f z))
          + ENNReal.ofReal ε * volume (closedCube z₀ s)) ∧
    ENNReal.ofReal ((1 - ε) ^ m)
        * ∫⁻ z in closedCube z₀ s, ENNReal.ofReal (jac f z)
      ≤ μHE[m] (graph f (closedCube z₀ s))
        + ENNReal.ofReal ε * volume (closedCube z₀ s) := by
  set R := closedCube z₀ s with hRdef
  set I := ∫⁻ z in R, ENNReal.ofReal (jac f z) with hI
  set μ := μHE[m] (graph f R) with hμ
  set V := volume R with hV
  have hRcomp : IsCompact R := isCompact_closedCube z₀ hs.le
  -- Scale from uniform continuity of the derivative on `R`.
  have hcontD : ContinuousOn (fderiv ℝ f) R :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hsub
  have hucD := hRcomp.uniformContinuousOn_of_continuous hcontD
  rw [Metric.uniformContinuousOn_iff] at hucD
  obtain ⟨δ, hδ, hδspec⟩ := hucD ε hε0
  -- Grid size: choose `N` so each cell has diameter `< δ`.
  obtain ⟨N, hN⟩ := exists_nat_gt (s * Real.sqrt m / δ)
  have hNpos : 0 < N := by
    have hnn : (0 : ℝ) ≤ s * Real.sqrt m / δ := by positivity
    have : (0 : ℝ) < N := lt_of_le_of_lt hnn hN
    exact_mod_cast this
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  -- The grid.
  obtain ⟨ctr, hQR, hcover, hodisj⟩ := exists_grid z₀ hs hNpos
  rw [← hRdef] at hcover
  set h := s / N with hh
  have hhpos : 0 < h := by rw [hh]; positivity
  have hctrQ : ∀ p : Fin m → Fin N, ctr p ∈ closedCube (ctr p) h :=
    fun p => center_mem_closedCube _ hhpos.le
  -- Gradient oscillation on each cell.
  have hgrad : ∀ p : Fin m → Fin N, ∀ x ∈ closedCube (ctr p) h,
      ‖fderiv ℝ f x - fderiv ℝ f (ctr p)‖ ≤ ε := by
    intro p x hx
    have hd : dist x (ctr p) ≤ h * Real.sqrt m / 2 :=
      Metric.mem_closedBall.mp (closedCube_subset_closedBall (ctr p) hhpos.le hx)
    have hNδ : s * Real.sqrt m < N * δ := by
      rw [div_lt_iff₀ hδ] at hN; exact hN
    have hdlt : dist x (ctr p) < δ := by
      apply lt_of_le_of_lt hd
      rw [hh, div_mul_eq_mul_div, div_div, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hNR hδ]
    have := hδspec x (hQR p hx) (ctr p) (hQR p (hctrQ p)) hdlt
    rw [dist_eq_norm] at this
    exact this.le
  -- Per-cell area estimates and Jacobian oscillation.
  have hcell := fun p : Fin m → Fin N =>
    local_area_estimate hU hf (convex_closedCube _ _) ((hQR p).trans hsub)
      (hctrQ p) ⟨hε0, hε1⟩ (hgrad p) (closedCube (ctr p) h) subset_rfl
  have hJosc : ∀ p : Fin m → Fin N, ∀ x ∈ closedCube (ctr p) h,
      |jac f x - jac f (ctr p)| ≤ ε :=
    fun p x hx => abs_jac_sub_le (hgrad p x hx)
  -- Integral splitting along the grid.
  have hsplit : ∀ g : EM m → ℝ≥0∞,
      ∫⁻ z in R, g z = ∑ p : Fin m → Fin N, ∫⁻ z in closedCube (ctr p) h, g z :=
    fun g => lintegral_grid_split ctr (fun _ => h) (fun _ => hhpos) hodisj hcover g
  have hVsum : V = ∑ p : Fin m → Fin N, volume (closedCube (ctr p) h) := by
    have h1 := hsplit fun _ => 1
    rw [hV]
    simpa [setLIntegral_one] using h1
  have hIsum : I = ∑ p : Fin m → Fin N,
      ∫⁻ z in closedCube (ctr p) h, ENNReal.ofReal (jac f z) := by
    rw [hI]; exact hsplit _
  -- The Riemann sum.
  set S := ∑ p : Fin m → Fin N,
    ENNReal.ofReal (jac f (ctr p)) * volume (closedCube (ctr p) h) with hS
  -- S is squeezed between I ± εV.
  have hSle : S ≤ I + ENNReal.ofReal ε * V := by
    have hstep : ∀ p : Fin m → Fin N,
        ENNReal.ofReal (jac f (ctr p)) * volume (closedCube (ctr p) h)
          ≤ ∫⁻ z in closedCube (ctr p) h,
              (ENNReal.ofReal (jac f z) + ENNReal.ofReal ε) := by
      intro p
      rw [← setLIntegral_const]
      refine setLIntegral_mono'
        (isCompact_closedCube _ hhpos.le).isClosed.measurableSet fun x hx => ?_
      rw [← ENNReal.ofReal_add (jac_pos x).le hε0.le]
      apply ENNReal.ofReal_le_ofReal
      have := (abs_le.mp (hJosc p x hx)).1
      linarith
    calc S ≤ ∑ p : Fin m → Fin N, ∫⁻ z in closedCube (ctr p) h,
          (ENNReal.ofReal (jac f z) + ENNReal.ofReal ε) :=
        Finset.sum_le_sum fun p _ => hstep p
      _ = ∫⁻ z in R, (ENNReal.ofReal (jac f z) + ENNReal.ofReal ε) :=
        (hsplit _).symm
      _ = I + ENNReal.ofReal ε * V := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, hI, hV]
  have hIleS : I ≤ S + ENNReal.ofReal ε * V := by
    have hstep : ∀ p : Fin m → Fin N,
        ∫⁻ z in closedCube (ctr p) h, ENNReal.ofReal (jac f z)
          ≤ ENNReal.ofReal (jac f (ctr p)) * volume (closedCube (ctr p) h)
            + ENNReal.ofReal ε * volume (closedCube (ctr p) h) := by
      intro p
      calc ∫⁻ z in closedCube (ctr p) h, ENNReal.ofReal (jac f z)
          ≤ ∫⁻ _z in closedCube (ctr p) h,
              (ENNReal.ofReal (jac f (ctr p)) + ENNReal.ofReal ε) := by
            refine setLIntegral_mono'
              (isCompact_closedCube _ hhpos.le).isClosed.measurableSet fun x hx => ?_
            rw [← ENNReal.ofReal_add (jac_pos (ctr p)).le hε0.le]
            apply ENNReal.ofReal_le_ofReal
            have := (abs_le.mp (hJosc p x hx)).2
            linarith
        _ = ENNReal.ofReal (jac f (ctr p)) * volume (closedCube (ctr p) h)
            + ENNReal.ofReal ε * volume (closedCube (ctr p) h) := by
            rw [setLIntegral_const, add_mul]
    calc I = ∑ p : Fin m → Fin N,
          ∫⁻ z in closedCube (ctr p) h, ENNReal.ofReal (jac f z) := hIsum
      _ ≤ ∑ p : Fin m → Fin N,
          (ENNReal.ofReal (jac f (ctr p)) * volume (closedCube (ctr p) h)
            + ENNReal.ofReal ε * volume (closedCube (ctr p) h)) :=
        Finset.sum_le_sum fun p _ => hstep p
      _ = S + ENNReal.ofReal ε * ∑ p : Fin m → Fin N,
          volume (closedCube (ctr p) h) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, hS]
      _ = S + ENNReal.ofReal ε * V := by rw [← hVsum]
  -- The graph over `R` decomposes along the cells.
  have hgU : graph f R = ⋃ p : Fin m → Fin N, graph f (closedCube (ctr p) h) := by
    rw [graph, ← hcover, Set.image_iUnion]
    rfl
  constructor
  · -- Upper bound: countable subadditivity.
    calc μ = μHE[m] (⋃ p : Fin m → Fin N, graph f (closedCube (ctr p) h)) := by
          rw [hμ, hgU]
      _ ≤ ∑ p : Fin m → Fin N, μHE[m] (graph f (closedCube (ctr p) h)) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ p : Fin m → Fin N, ENNReal.ofReal ((1 + ε) ^ m * jac f (ctr p))
            * volume (closedCube (ctr p) h) :=
          Finset.sum_le_sum fun p _ => (hcell p).2
      _ = ENNReal.ofReal ((1 + ε) ^ m) * S := by
          rw [hS, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ ENNReal.ofReal ((1 + ε) ^ m) * (I + ENNReal.ofReal ε * V) :=
          mul_le_mul_right hSle _
  · -- Lower bound: a.e.-additivity of the (almost disjoint) graph pieces.
    have hAE : ((Finset.univ : Finset (Fin m → Fin N)) : Set (Fin m → Fin N)).Pairwise
        (Function.onFun (AEDisjoint μHE[m])
          fun p => graph f (closedCube (ctr p) h)) := by
      intro p _ q _ hpq
      exact graph_inter_null hU hf hhpos ((hQR p).trans hsub)
        ((hQR q).trans hsub) (hodisj hpq)
    have hmeasF : ∀ p ∈ (Finset.univ : Finset (Fin m → Fin N)),
        NullMeasurableSet (graph f (closedCube (ctr p) h)) μHE[m] := by
      intro p _
      exact (((isCompact_closedCube (ctr p) hhpos.le).image_of_continuousOn
        ((continuousOn_graphMap hf.continuousOn).mono
          ((hQR p).trans hsub))).measurableSet).nullMeasurableSet
    have hμsum : ∑ p : Fin m → Fin N,
        ENNReal.ofReal ((1 - ε) ^ m * jac f (ctr p))
          * volume (closedCube (ctr p) h) ≤ μ := by
      calc ∑ p : Fin m → Fin N, ENNReal.ofReal ((1 - ε) ^ m * jac f (ctr p))
            * volume (closedCube (ctr p) h)
          ≤ ∑ p : Fin m → Fin N, μHE[m] (graph f (closedCube (ctr p) h)) :=
            Finset.sum_le_sum fun p _ => (hcell p).1
        _ = μHE[m] (⋃ p ∈ (Finset.univ : Finset (Fin m → Fin N)),
              graph f (closedCube (ctr p) h)) :=
            (measure_biUnion_finset₀ hAE hmeasF).symm
        _ = μ := by
            rw [hμ, hgU]
            congr 1
            simp
    calc ENNReal.ofReal ((1 - ε) ^ m) * I
        ≤ ENNReal.ofReal ((1 - ε) ^ m) * (S + ENNReal.ofReal ε * V) :=
          mul_le_mul_right hIleS _
      _ = ENNReal.ofReal ((1 - ε) ^ m) * S
          + ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal ε * V) := mul_add _ _ _
      _ ≤ μ + ENNReal.ofReal ε * V := by
          refine add_le_add ?_ ?_
          · calc ENNReal.ofReal ((1 - ε) ^ m) * S
                = ∑ p : Fin m → Fin N,
                  ENNReal.ofReal ((1 - ε) ^ m * jac f (ctr p))
                    * volume (closedCube (ctr p) h) := by
                  rw [hS, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun p _ => ?_
                  rw [ENNReal.ofReal_mul (pow_nonneg (by linarith) m), mul_assoc]
              _ ≤ μ := hμsum
          · have hb1 : ENNReal.ofReal ((1 - ε) ^ m) ≤ 1 :=
              ENNReal.ofReal_le_one.mpr (pow_le_one₀ (by linarith) (by linarith))
            calc ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal ε * V)
                ≤ 1 * (ENNReal.ofReal ε * V) := by gcongr
              _ = ENNReal.ofReal ε * V := one_mul _

/-- **Area formula over a closed cube.** Grid the cube at a scale
realizing gradient oscillation `ε`, apply `local_area_estimate` per
cell, compare Riemann sums with the integral, and let the grid refine
and `ε ↓ 0`. -/
theorem cube_area {U : Set (EM m)} {f : EM m → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (z₀ : EM m) {s : ℝ} (hs : 0 < s)
    (hsub : closedCube z₀ s ⊆ U) :
    μHE[m] (graph f (closedCube z₀ s))
      = ∫⁻ z in closedCube z₀ s, ENNReal.ofReal (jac f z) := by
  have hVfin : volume (closedCube z₀ s) ≠ ⊤ := by
    rw [volume_closedCube z₀ hs.le]
    exact ENNReal.ofReal_ne_top
  have hRcomp : IsCompact (closedCube z₀ s) := isCompact_closedCube z₀ hs.le
  -- `J` is bounded on the compact cube, so the integral is finite.
  obtain ⟨C, hC⟩ := hRcomp.exists_bound_of_continuousOn
    ((continuousOn_jac hU hf).mono hsub)
  have hIfin : (∫⁻ z in closedCube z₀ s, ENNReal.ofReal (jac f z)) ≠ ⊤ := by
    have hle : (∫⁻ z in closedCube z₀ s, ENNReal.ofReal (jac f z))
        ≤ ENNReal.ofReal C * volume (closedCube z₀ s) := by
      rw [← setLIntegral_const]
      refine setLIntegral_mono' hRcomp.isClosed.measurableSet fun x hx => ?_
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC x hx))
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin) hle
  exact eq_of_grid_estimates hIfin hVfin fun ε hε0 hε1 =>
    cube_grid_estimate hU hf z₀ hs hsub hε0 hε1

end


/-
=== GeneralizedGraph.Main ===

# The main theorem: the area formula for a C¹ graph in `ℝᵐ⁺¹`

    μHE[m] (Γ_f) = ∫_U √(1 + ‖∇f‖²)

with `μHE[m]` Mathlib's Euclidean-normalized `m`-dimensional Hausdorff
measure — the honest `m`-dimensional area of the hypersurface `Γ_f` in
`ℝᵐ⁺¹`.

Both sides live in `[0,∞]` and are finite or infinite together — `ℝ≥0∞`
arithmetic handles this automatically, a genuine advantage over a
pen-and-paper case analysis.

The proof assembles the single-cube result `cube_area` over the dyadic
decomposition of the open base `U`.  The measurability/overlap
bookkeeping is entirely handled by `graph_null_of_volume_null`: the
cubes meet only along their (volume-null) frontiers, whose graphs carry
no area.
-/

section
open MeasureTheory Measure Set

variable {m : ℕ}

/-- **The area formula** (main theorem), for `m ≥ 1`.

Proof plan: decompose `U` into non-overlapping dyadic cubes `Qₙ`
(`dyadic_decomposition`), so `Γ_f = ⋃ₙ Φ(Qₙ)`.

* UPPER: countable subadditivity `measure_iUnion_le` + `cube_area` on
  each `Qₙ`, then `Σₙ ∫_{Qₙ} J = ∫_U J` — interiors are pairwise
  disjoint, the frontiers and the leftover are volume-null, and the
  `lintegral` ignores null sets.
* LOWER: for each finite subfamily `F`,
  `μHE[m](Γ_f) ≥ μHE[m](⋃_{n∈F} Φ(Qₙ)) = Σ_{n∈F} μHE[m](Φ(Qₙ))`
  — the pieces are compact hence measurable, pairwise overlaps are
  graphs over shared (volume-null) frontiers and hence null; then
  `cube_area` per piece and `ENNReal.tsum_eq_iSup_sum`. -/
theorem area_formula (hm : 0 < m) {U : Set (EM m)} {f : EM m → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) :
    μHE[m] (graph f U) = ∫⁻ z in U, ENNReal.ofReal (jac f z) := by
  rcases Set.eq_empty_or_nonempty U with rfl | hne
  · simp [graph]
  obtain ⟨z, s, hprop, hdisj, hunion⟩ := dyadic_decomposition hm hU hne one_pos
  set Q : ℕ → Set (EM m) := fun n => closedCube (z n) (s n) with hQdef
  have hQU : ∀ n, Q n ⊆ U := fun n => (hprop n).2.2
  have hQs : ∀ n, 0 < s n := fun n => (hprop n).1
  have hcompact : ∀ n, IsCompact (Q n) := fun n => isCompact_closedCube _ (hQs n).le
  have hconvex : ∀ n, Convex ℝ (Q n) := fun n => convex_closedCube _ _
  have hsq : ∀ n, μHE[m] (graph f (Q n)) = ∫⁻ w in Q n, ENNReal.ofReal (jac f w) :=
    fun n => cube_area hU hf (z n) (hQs n) (hQU n)
  -- The graph decomposes along the cubes.
  have hgraph : graph f U = ⋃ n, graph f (Q n) := by
    rw [graph, ← hunion, Set.image_iUnion]
    rfl
  -- Frontiers are volume-null, so cubes agree a.e. with their
  -- (pairwise disjoint) interiors.
  have hfr_null : ∀ n, volume (Q n \ interior (Q n)) = 0 := fun n =>
    volume_frontier_closedCube _ (hQs n).le
  have hae : ∀ n, (Q n : Set (EM m)) =ᵐ[volume] interior (Q n) := by
    intro n
    rw [MeasureTheory.ae_eq_set]
    exact ⟨hfr_null n, by
      rw [Set.diff_eq_empty.mpr interior_subset]
      exact measure_empty⟩
  have hdisj' : Pairwise (Function.onFun Disjoint fun n => interior (Q n)) :=
    fun a b hab => Set.disjoint_iff_inter_eq_empty.mpr (hdisj hab)
  -- The integral over `U` is the sum of the integrals over the cubes.
  have hUae : (U : Set (EM m)) =ᵐ[volume] ⋃ n, interior (Q n) := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (measure_iUnion_null hfr_null)
      intro x hx
      obtain ⟨hxU, hxint⟩ := hx
      rw [← hunion] at hxU
      obtain ⟨_, ⟨n, rfl⟩, hxn⟩ := hxU
      simp only [Set.mem_iUnion, not_exists] at hxint
      exact Set.mem_iUnion.mpr ⟨n, hxn, hxint n⟩
    · rw [Set.diff_eq_empty.mpr ?_]
      · exact measure_empty
      · exact Set.iUnion_subset fun n => interior_subset.trans (hQU n)
  have htotal : ∫⁻ w in U, ENNReal.ofReal (jac f w)
      = ∑' n, ∫⁻ w in Q n, ENNReal.ofReal (jac f w) := by
    rw [setLIntegral_congr hUae,
      lintegral_iUnion (fun n => isOpen_interior.measurableSet) hdisj']
    exact tsum_congr fun n => (setLIntegral_congr (hae n)).symm
  -- UPPER BOUND: countable subadditivity.
  have hupper : μHE[m] (graph f U) ≤ ∫⁻ w in U, ENNReal.ofReal (jac f w) := by
    rw [hgraph, htotal]
    calc μHE[m] (⋃ n, graph f (Q n)) ≤ ∑' n, μHE[m] (graph f (Q n)) :=
        measure_iUnion_le _
      _ = ∑' n, ∫⁻ w in Q n, ENNReal.ofReal (jac f w) := tsum_congr hsq
  -- LOWER BOUND: finite pieces are almost disjoint (overlaps are graphs
  -- over the null frontiers), so additivity applies.
  have hlower : ∫⁻ w in U, ENNReal.ofReal (jac f w) ≤ μHE[m] (graph f U) := by
    rw [htotal, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    have hAE : (F : Set ℕ).Pairwise (Function.onFun (AEDisjoint μHE[m])
        fun n => graph f (Q n)) := by
      intro a _ b _ hab
      show μHE[m] (graph f (Q a) ∩ graph f (Q b)) = 0
      have hinter : graph f (Q a) ∩ graph f (Q b) = graph f (Q a ∩ Q b) := by
        rw [graph, graph, graph, ← Set.image_inter graphMap_injective]
      rw [hinter]
      refine le_antisymm ?_ zero_le
      have hsub : Q a ∩ Q b ⊆ (Q a \ interior (Q a)) ∪ (Q b \ interior (Q b)) := by
        rintro x ⟨hxa, hxb⟩
        by_cases hx : x ∈ interior (Q a)
        · refine Or.inr ⟨hxb, fun hx' => ?_⟩
          have hmem : x ∈ interior (Q a) ∩ interior (Q b) := ⟨hx, hx'⟩
          rw [hdisj hab] at hmem
          exact hmem
        · exact Or.inl ⟨hxa, hx⟩
      calc μHE[m] (graph f (Q a ∩ Q b))
          ≤ μHE[m] (graph f (Q a \ interior (Q a)) ∪ graph f (Q b \ interior (Q b))) := by
            refine measure_mono ?_
            rw [graph, graph, graph, ← Set.image_union]
            exact Set.image_mono hsub
        _ ≤ μHE[m] (graph f (Q a \ interior (Q a)))
              + μHE[m] (graph f (Q b \ interior (Q b))) := measure_union_le _ _
        _ = 0 := by
            rw [graph_null_of_volume_null hU hf (hcompact a) (hconvex a) (hQU a)
                Set.sdiff_subset (hfr_null a),
              graph_null_of_volume_null hU hf (hcompact b) (hconvex b) (hQU b)
                Set.sdiff_subset (hfr_null b), add_zero]
    have hmeasF : ∀ n ∈ F, NullMeasurableSet (graph f (Q n)) μHE[m] := by
      intro n _
      exact (((hcompact n).image_of_continuousOn
        ((continuousOn_graphMap hf.continuousOn).mono (hQU n))).measurableSet).nullMeasurableSet
    calc ∑ n ∈ F, ∫⁻ w in Q n, ENNReal.ofReal (jac f w)
        = ∑ n ∈ F, μHE[m] (graph f (Q n)) :=
          Finset.sum_congr rfl fun n _ => (hsq n).symm
      _ = μHE[m] (⋃ n ∈ F, graph f (Q n)) :=
          (measure_biUnion_finset₀ hAE hmeasF).symm
      _ ≤ μHE[m] (graph f U) := by
          refine measure_mono (Set.iUnion₂_subset fun n _ => ?_)
          exact Set.image_mono (hQU n)
  exact le_antisymm hupper hlower

end


/-
=== GeneralizedDivergence.Setup ===

# Divergence theorem in ℝⁿ — setup (paper §2, "Understanding the theorem")

Ambient space and graph vocabulary are inherited from the completed
GeneralizedGraph project.  Throughout, `m` is the *boundary* dimension
and `n = m + 1` the ambient dimension:

* `EM m = EuclideanSpace ℝ (Fin m)` is the base ℝᵐ = ℝⁿ⁻¹;
* `EN m = WithLp 2 (EM m × ℝ)` is the ambient ℝᵐ⁺¹ = ℝⁿ, the ℓ²-product
  of the base with a vertical line, keeping the horizontal/vertical
  split `x = (x', xₙ)` visible in the type;
* `graphMap`, `graph`, `jac` are GeneralizedGraph's graph vocabulary.

This file adds the divergence-specific vocabulary from
`V2DivergenceProof.tex`, now in arbitrary dimension:

* `horiz`/`vert` — the coordinate split `x = (x', xₙ)`;
* `subgraphSet`, `cylinder` — the strict subgraph `{xₙ < g x'}` and the
  graph cylinder `{|x'| < r, |xₙ - g x'| < ht}` (paper proof step 2);
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

Design note: this is the `n`-dimensional development the paper is
actually written for.  The ℝ³ special case lives in the companion
`DivergenceTheorem` project; every proof here is the same argument with
the planar base ℝ² replaced by `EM m` — the ℓ²-Pythagoras identity for
the product norm does all the dimension-independent work.
-/

section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology

variable {m : ℕ}

/-! ### Coordinates -/

/-- Horizontal part `x'` of `x = (x', xₙ) ∈ ℝⁿ`. -/
def horiz (x : (EN m)) : (EM m) := (WithLp.ofLp x).1

/-- Vertical part `xₙ` of `x = (x', xₙ) ∈ ℝⁿ`. -/
def vert (x : (EN m)) : ℝ := (WithLp.ofLp x).2

@[simp] lemma horiz_toLp (z : (EM m)) (a : ℝ) : horiz (WithLp.toLp 2 (z, a)) = z := rfl

@[simp] lemma vert_toLp (z : (EM m)) (a : ℝ) : vert (WithLp.toLp 2 (z, a)) = a := rfl

@[simp] lemma horiz_graphMap (g : (EM m) → ℝ) (z : (EM m)) : horiz (graphMap g z) = z := rfl

@[simp] lemma vert_graphMap (g : (EM m) → ℝ) (z : (EM m)) : vert (graphMap g z) = g z := rfl

@[simp] lemma toLp_horiz_vert (x : (EN m)) : WithLp.toLp 2 (horiz x, vert x) = x := rfl

@[simp] lemma horiz_add (x y : (EN m)) : horiz (x + y) = horiz x + horiz y := rfl

@[simp] lemma vert_add (x y : (EN m)) : vert (x + y) = vert x + vert y := rfl

@[simp] lemma horiz_sub (x y : (EN m)) : horiz (x - y) = horiz x - horiz y := rfl

@[simp] lemma vert_sub (x y : (EN m)) : vert (x - y) = vert x - vert y := rfl

@[simp] lemma horiz_smul (t : ℝ) (x : (EN m)) : horiz (t • x) = t • horiz x := rfl

@[simp] lemma vert_smul (t : ℝ) (x : (EN m)) : vert (t • x) = t * vert x := rfl

@[simp] lemma horiz_neg (x : (EN m)) : horiz (-x) = -horiz x := rfl

@[simp] lemma vert_neg (x : (EN m)) : vert (-x) = -vert x := rfl

/-- Extensionality for `(EN m)` in the `horiz`/`vert` coordinates. -/
lemma EN_ext {x y : (EN m)} (h1 : horiz x = horiz y) (h2 : vert x = vert y) :
    x = y := by
  have h : WithLp.ofLp x = WithLp.ofLp y := Prod.ext h1 h2
  exact congrArg (WithLp.toLp 2) h

lemma continuous_horiz : Continuous (horiz : EN m → EM m) :=
  continuous_fst.comp (WithLp.prod_continuous_ofLp 2 (EM m) ℝ)

lemma continuous_vert : Continuous (vert : EN m → ℝ) :=
  continuous_snd.comp (WithLp.prod_continuous_ofLp 2 (EM m) ℝ)

lemma continuous_graphMap {g : (EM m) → ℝ} (hg : Continuous g) :
    Continuous (graphMap g) :=
  (WithLp.prod_continuous_toLp 2 (EM m) ℝ).comp (continuous_id.prodMk hg)

/-- Pythagoras in the `horiz`/`vert` coordinates (GeneralizedGraph's
`norm_toLp_sq` re-read through the projections). -/
lemma norm_sq_eq (x : (EN m)) : ‖x‖ ^ 2 = ‖horiz x‖ ^ 2 + (vert x) ^ 2 := by
  conv_lhs => rw [← toLp_horiz_vert x]
  exact norm_toLp_sq _ _

/-- The real inner product in the `horiz`/`vert` coordinates. -/
lemma inner_eq (x y : (EN m)) :
    ⟪x, y⟫ = ⟪horiz x, horiz y⟫ + vert x * vert y := by
  rw [WithLp.prod_inner_apply (𝕜 := ℝ) x y]
  congr 1
  exact mul_comm _ _

/-! ### Subgraphs and cylinders (paper proof step 2) -/

/-- The strict subgraph `Σ_g = {x : xₙ < g x'}` — the region strictly
below the graph of `g`. -/
def subgraphSet (g : (EM m) → ℝ) : Set (EN m) := {x | vert x < g (horiz x)}

/-- The open graph cylinder `{x : |x'| < r and |xₙ - g x'| < ht}`
(the paper's neighborhood `U` from proof step 2, before the rigid
motion). -/
def cylinder (g : (EM m) → ℝ) (r ht : ℝ) : Set (EN m) :=
  {x | ‖horiz x‖ < r ∧ |vert x - g (horiz x)| < ht}

lemma isOpen_subgraphSet {g : (EM m) → ℝ} (hg : Continuous g) :
    IsOpen (subgraphSet g) :=
  isOpen_lt continuous_vert (hg.comp continuous_horiz)

lemma isOpen_cylinder {g : (EM m) → ℝ} (hg : Continuous g) (r ht : ℝ) :
    IsOpen (cylinder g r ht) := by
  have h1 : IsOpen {x : (EN m) | ‖horiz x‖ < r} :=
    isOpen_lt (continuous_norm.comp continuous_horiz) continuous_const
  have h2 : IsOpen {x : (EN m) | |vert x - g (horiz x)| < ht} :=
    isOpen_lt (continuous_vert.sub (hg.comp continuous_horiz)).abs continuous_const
  exact h1.inter h2

lemma graphMap_mem_cylinder {g : (EM m) → ℝ} {r ht : ℝ} (hht : 0 < ht) {z : (EM m)}
    (hz : z ∈ Metric.ball (0 : (EM m)) r) :
    graphMap g z ∈ cylinder g r ht := by
  refine ⟨by simpa [mem_ball_zero_iff] using hz, by simpa using hht⟩

/-- The graph piece inside a cylinder is the graph over the disk:
`{x ∈ cylinder : xₙ = g x'} = Φ_g '' B(0, r)` (for `0 < ht`). -/
lemma cylinder_inter_graph {g : (EM m) → ℝ} {r ht : ℝ} (hht : 0 < ht) :
    cylinder g r ht ∩ {x | vert x = g (horiz x)}
      = graph g (Metric.ball (0 : (EM m)) r) := by
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
structure CylinderChart (Ω : Set (EN m)) where
  /-- The rigid motion (rotation + translation + possibly a reflection). -/
  T : (EN m) ≃ᵃⁱ[ℝ] (EN m)
  /-- The boundary is locally the graph of `g`. -/
  g : (EM m) → ℝ
  /-- Radius of the cylinder. -/
  r : ℝ
  /-- Half-height of the cylinder. -/
  ht : ℝ
  hr : 0 < r
  hht : 0 < ht
  /-- `g` is C¹ on all of ℝⁿ⁻¹ (the paper's `g : ℝ^{n-1} → ℝ` C¹). -/
  hg : ContDiff ℝ 1 g
  /-- `xₙ = g x'  ⟹  T x ∈ ∂Ω` inside the cylinder. -/
  mem_frontier : ∀ x ∈ cylinder g r ht, vert x = g (horiz x) → T x ∈ frontier Ω
  /-- `xₙ < g x'  ⟹  T x ∈ Ω` inside the cylinder. -/
  mem_inside : ∀ x ∈ cylinder g r ht, vert x < g (horiz x) → T x ∈ Ω
  /-- `xₙ > g x'  ⟹  T x ∉ Ω` inside the cylinder. -/
  mem_outside : ∀ x ∈ cylinder g r ht, g (horiz x) < vert x → T x ∉ Ω

variable {Ω : Set (EN m)}

namespace CylinderChart

/-- The chart's neighborhood in space: the image of the cylinder under
the rigid motion. -/
def U (c : CylinderChart Ω) : Set (EN m) := c.T '' cylinder c.g c.r c.ht

lemma isOpen_U (c : CylinderChart Ω) : IsOpen c.U :=
  c.T.toHomeomorph.isOpen_image.mpr (isOpen_cylinder c.hg.continuous _ _)

/-- The rigid motion applied to a translated point:
`T(p + w) = T p + T₀ w`. -/
lemma map_add (c : CylinderChart Ω) (p w : (EN m)) :
    c.T (p + w) = c.T p + c.T.linearIsometryEquiv w := by
  simpa [add_comm] using c.T.map_vadd p w

lemma map_sub (c : CylinderChart Ω) (p w : (EN m)) :
    c.T (p - w) = c.T p - c.T.linearIsometryEquiv w := by
  rw [sub_eq_add_neg, sub_eq_add_neg, c.map_add p (-w), map_neg]

/-- The open upper region of a chart's cylinder is disjoint from the
closure of `Ω` (strengthens `mem_outside` from `Ω` to `Ω̄`, which is
what the frontier computation and the ray lemmas need). -/
lemma image_upper_disjoint_closure (c : CylinderChart Ω) :
    Disjoint (c.T '' (cylinder c.g c.r c.ht ∩ {x | c.g (horiz x) < vert x}))
      (closure Ω) := by
  set W := cylinder c.g c.r c.ht ∩ {x : (EN m) | c.g (horiz x) < vert x} with hW
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
    frontier Ω ∩ c.U = c.T '' graph c.g (Metric.ball (0 : (EM m)) c.r) := by
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
def HasC1Boundary (Ω : Set (EN m)) : Prop :=
  ∀ x₀ ∈ frontier Ω, ∃ c : CylinderChart Ω, x₀ ∈ c.U

/-- The boundary of a bounded set is compact (closed and bounded). -/
lemma isCompact_frontier (hb : Bornology.IsBounded Ω) :
    IsCompact (frontier Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)

/-! ### The outward unit normal (paper §2.2) -/

/-- The upward unit normal of the graph of `g` at the point above `z`:
`ν = (-∇g, 1)/√(1 + |∇g|²)`.  The normalizing factor is exactly
GeneralizedGraph's Jacobian `jac g z`. -/
def unitNormal (g : (EM m) → ℝ) (z : (EM m)) : (EN m) :=
  (jac g z)⁻¹ • (WithLp.toLp 2 (-gradient g z, 1) : (EN m))

lemma horiz_unitNormal (g : (EM m) → ℝ) (z : (EM m)) :
    horiz (unitNormal g z) = -((jac g z)⁻¹ • gradient g z) := by
  simp [unitNormal]

lemma vert_unitNormal (g : (EM m) → ℝ) (z : (EM m)) :
    vert (unitNormal g z) = (jac g z)⁻¹ := by
  simp [unitNormal]

/-- The gradient and the Fréchet derivative have the same norm (the
gradient is the Riesz representative). -/
lemma norm_gradient_eq (g : (EM m) → ℝ) (z : (EM m)) :
    ‖gradient g z‖ = ‖fderiv ℝ g z‖ := by
  rw [gradient]
  exact (InnerProductSpace.toDual ℝ (EM m)).symm.norm_map _

/-- `⟪∇g, w⟫ = Dg(w)` (the defining property of the gradient). -/
lemma inner_gradient_eq (g : (EM m) → ℝ) (z : (EM m)) (w : (EM m)) :
    ⟪gradient g z, w⟫ = fderiv ℝ g z w := by
  rw [gradient]
  exact InnerProductSpace.toDual_symm_apply

/-- `J² = 1 + ‖∇g‖²`. -/
lemma jac_sq (g : (EM m) → ℝ) (z : (EM m)) :
    jac g z ^ 2 = 1 + ‖gradient g z‖ ^ 2 := by
  rw [jac, Real.sq_sqrt (by positivity), norm_gradient_eq]

/-- The graph normal is a unit vector (paper §2.2, "divide by its
length"; no differentiability hypothesis is needed since `jac` and
`gradient` are built from the same junk-valued `fderiv`). -/
lemma norm_unitNormal (g : (EM m) → ℝ) (z : (EM m)) : ‖unitNormal g z‖ = 1 := by
  have hpos : 0 < jac g z := jac_pos z
  have hsq : ‖(WithLp.toLp 2 (-gradient g z, 1) : (EN m))‖ ^ 2 = jac g z ^ 2 := by
    rw [norm_toLp_sq, norm_neg, jac_sq]
    ring
  have hnorm : ‖(WithLp.toLp 2 (-gradient g z, 1) : (EN m))‖ = jac g z := by
    have h := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hpos.le] at h
  rw [unitNormal, norm_smul, hnorm, norm_inv, Real.norm_eq_abs,
    abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

/-- The inner product of the graph normal with a graph-tangent direction
`(w, Dg·w)` vanishes — the algebraic heart of "perpendicular to the
surface" (paper §2.2). -/
lemma inner_unitNormal_graphDir (g : (EM m) → ℝ) (z : (EM m)) (w : (EM m)) :
    ⟪unitNormal g z, (WithLp.toLp 2 (w, fderiv ℝ g z w) : (EN m))⟫ = 0 := by
  rw [inner_eq, horiz_unitNormal, vert_unitNormal]
  simp only [horiz_toLp, vert_toLp, inner_neg_left, real_inner_smul_left,
    inner_gradient_eq]
  ring

/-- **The geometric characterization of the outward unit normal at a
boundary point** (paper §2.2): unit length, orthogonal to every tangent
direction of `∂Ω` at `x`, leaving `Ω̄` in the forward direction and
entering `Ω` in the backward direction. -/
def IsOutwardNormalAt (Ω : Set (EN m)) (x v : (EN m)) : Prop :=
  ‖v‖ = 1 ∧
  (∀ y ∈ tangentConeAt ℝ (frontier Ω) x, ⟪v, y⟫ = 0) ∧
  (∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • v ∉ closure Ω) ∧
  (∀ᶠ t in 𝓝[>] (0 : ℝ), x - t • v ∈ Ω)

/-- A choice of outward unit normal at every boundary point.  The main
theorem is stated for an arbitrary such field. -/
def IsOutwardNormal (Ω : Set (EN m)) (ν : (EN m) → (EN m)) : Prop :=
  ∀ x ∈ frontier Ω, IsOutwardNormalAt Ω x (ν x)

section NormalTheory

variable (c : CylinderChart Ω) {z : (EM m)}

/-- The vertical overshoot (or undershoot) of the normal ray: for `ε = ±1`, the
point `Φz + t·(ε·ν)` stays in the cylinder and lies strictly above
(`ε = 1`) resp. strictly below (`ε = -1`) the graph for small `t > 0` —
the height difference has slope `ε²·J = J > 0` at `t = 0` (the paper's
"checking it points outward" Taylor computation). -/
private lemma eventually_ray_side (hz : z ∈ Metric.ball (0 : (EM m)) c.r)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      graphMap c.g z + t • (ε • unitNormal c.g z) ∈ cylinder c.g c.r c.ht ∧
      0 < ε * (vert (graphMap c.g z + t • (ε • unitNormal c.g z))
        - c.g (horiz (graphMap c.g z + t • (ε • unitNormal c.g z)))) := by
  have hdiff : DifferentiableAt ℝ c.g z := (c.hg.differentiable one_ne_zero) z
  have hJ : 0 < jac c.g z := jac_pos z
  set ν := unitNormal c.g z with hν
  set q : ℝ → (EN m) := fun t => graphMap c.g z + t • (ε • ν) with hq
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
    set b : (EM m) := ε • -((jac c.g z)⁻¹ • gradient c.g z) with hb
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
private lemma eventually_ray_outside (hz : z ∈ Metric.ball (0 : (EM m)) c.r) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      c.T (graphMap c.g z + t • unitNormal c.g z) ∉ closure Ω := by
  filter_upwards [eventually_ray_side c hz 1 (Or.inl rfl)] with t ht
  obtain ⟨hcyl, hup⟩ := ht
  simp only [one_smul, one_mul] at hcyl hup
  intro hcl
  exact Set.disjoint_left.mp c.image_upper_disjoint_closure
    ⟨_, ⟨hcyl, by simpa using sub_pos.mp hup⟩, rfl⟩ hcl

/-- Backward normal ray enters `Ω`. -/
private lemma eventually_ray_inside (hz : z ∈ Metric.ball (0 : (EM m)) c.r) :
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
private lemma graphDir_mem_tangentCone (hz : z ∈ Metric.ball (0 : (EM m)) c.r)
    (w : (EM m)) :
    c.T.linearIsometryEquiv (WithLp.toLp 2 (w, fderiv ℝ c.g z w))
      ∈ tangentConeAt ℝ (frontier Ω) (c.T (graphMap c.g z)) := by
  have hdiff : DifferentiableAt ℝ c.g z := (c.hg.differentiable one_ne_zero) z
  set t : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ with ht
  have htpos : ∀ n, 0 < t n := fun n => by positivity
  have ht0 : Tendsto t atTop (𝓝 0) := by
    rw [ht]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  set zn : ℕ → (EM m) := fun n => z + t n • w with hzn
  have hzn0 : Tendsto zn atTop (𝓝 z) := by
    have hc : Continuous fun s : ℝ => s • w := by fun_prop
    have h : Tendsto (fun n => t n • w) atTop (𝓝 (0 : EM m)) := by
      have h2 := (hc.tendsto 0).comp ht0
      rw [zero_smul] at h2
      exact h2
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
    have hball : ∀ᶠ n in atTop, zn n ∈ Metric.ball (0 : (EM m)) c.r :=
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
        = (WithLp.toLp 2 ((t n)⁻¹ • (zn n - z), (c.g (zn n) - c.g z) / t n) : (EN m)) := by
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
    have hcont : Continuous fun p : ℝ => (WithLp.toLp 2 (w, p) : (EN m)) :=
      (WithLp.prod_continuous_toLp 2 (EM m) ℝ).comp (continuous_const.prodMk continuous_id)
    have h := (c.T.linearIsometryEquiv.continuous.tendsto _).comp
      ((hcont.tendsto _).comp hslope)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [← map_smul, key n, hzsub n]

/-- Tangent vectors of `∂Ω` at a chart point are (moved) graph-tangent:
transported back through the rigid motion, their vertical component is
`Dg` of their horizontal component. -/
private lemma tangent_flat (hΩ : IsOpen Ω) (hz : z ∈ Metric.ball (0 : (EM m)) c.r)
    {y : (EN m)} (hy : y ∈ tangentConeAt ℝ (frontier Ω) (c.T (graphMap c.g z))) :
    vert (c.T.linearIsometryEquiv.symm y)
      = fderiv ℝ c.g z (horiz (c.T.linearIsometryEquiv.symm y)) := by
  have hdiff : DifferentiableAt ℝ c.g z := (c.hg.differentiable one_ne_zero) z
  obtain ⟨α, l, hl, cs, d, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
  set T₀ := c.T.linearIsometryEquiv with hT₀
  set d' : α → (EN m) := fun n => T₀.symm (d n) with hd'
  have hd'0 : Tendsto d' l (𝓝 0) := by
    have h := (T₀.symm.continuous.tendsto 0).comp hd0
    simp only [map_zero] at h
    convert h
    ext n
    rw [hd']
    rfl
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
  have hlittle : (fun w : (EM m) => c.g (z + w) - c.g z - fderiv ℝ c.g z w)
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
    {z : (EM m)} (hz : z ∈ Metric.ball (0 : (EM m)) c.r) :
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
    {z : (EM m)} (hz : z ∈ Metric.ball (0 : (EM m)) c.r) {v : (EN m)}
    (hv : IsOutwardNormalAt Ω (c.T (graphMap c.g z)) v) :
    v = c.T.linearIsometryEquiv (unitNormal c.g z) := by
  obtain ⟨hv1, hv2, -, hv4⟩ := hv
  have hJ : 0 < jac c.g z := jac_pos z
  set T₀ := c.T.linearIsometryEquiv with hT₀
  set w₀ := T₀.symm v with hw₀
  have hvw : v = T₀ w₀ := by simp [hw₀]
  -- orthogonality against all graph directions
  have horth : ∀ w' : (EM m),
      ⟪horiz w₀, w'⟫ + vert w₀ * fderiv ℝ c.g z w' = 0 := by
    intro w'
    have h := hv2 _ (graphDir_mem_tangentCone c hz w')
    rw [hvw, T₀.inner_map_map, inner_eq] at h
    simpa using h
  have hkey : horiz w₀ = -(vert w₀ • gradient c.g z) := by
    have hall : ∀ w' : (EM m), ⟪horiz w₀ + vert w₀ • gradient c.g z, w'⟫ = 0 := by
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
    refine EN_ext ?_ ?_
    · rw [hkey, hpos, horiz_unitNormal]
    · rw [hpos, vert_unitNormal]
  · -- the negative sign contradicts the backward-ray condition
    exfalso
    have hw₀eq : w₀ = -unitNormal c.g z := by
      refine EN_ext ?_ ?_
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
    ∃ ν : (EN m) → (EN m), IsOutwardNormal Ω ν := by
  have key : ∀ x ∈ frontier Ω, ∃ v, IsOutwardNormalAt Ω x v := by
    intro x hx
    obtain ⟨c, hc⟩ := hC1 x hx
    have hxg : x ∈ c.T '' graph c.g (Metric.ball (0 : (EM m)) c.r) := by
      rw [← c.frontier_inter_U hΩ]
      exact ⟨hx, hc⟩
    obtain ⟨p, hp, rfl⟩ := hxg
    obtain ⟨w, hw, rfl⟩ := hp
    exact ⟨_, isOutwardNormalAt_chart hΩ c hw⟩
  choose! ν hν using key
  exact ⟨ν, hν⟩

end NormalTheory

end


/-
=== GeneralizedDivergence.Cutoff ===


-/

section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal Topology Manifold

/-
# Step 1: reduction to compactly supported functions (paper proof step 1, §3.1)

A smooth cutoff `φ ∈ C_c^∞(O)` with `φ ≡ 1` on the compact set `Ω̄ ⊆ O`
lets us replace `u ∈ C¹(O)` by `φu ∈ C¹_c(ℝⁿ)` without changing either
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

variable {m : ℕ}

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

/-- **Smooth cutoff on ℝⁿ** (paper's Lemma "Smooth Cutoff Function",
§3.1). -/
theorem exists_cutoff {K O : Set (EN m)} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) :
    ∃ φ : (EN m) → ℝ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧
      EqOn φ 1 K ∧ ∀ x, φ x ∈ Icc (0 : ℝ) 1 :=
  exists_cutoff' hK hO hKO

/-- On `Ω`, `φ ≡ 1` forces `D(φu) = Du` (paper part 1: "Left side").
No differentiability of `u` is needed: `φ * u` and `u` agree on a
neighborhood of `x`, so their derivatives agree. -/
theorem fderiv_cutoff_mul {φ u : (EN m) → ℝ} {Ω : Set (EN m)} (hΩ : IsOpen Ω)
    (hφ1 : EqOn φ 1 (closure Ω)) {x : (EN m)} (hx : x ∈ Ω) :
    fderiv ℝ (fun y => φ y * u y) x = fderiv ℝ u x := by
  have hev : (fun y => φ y * u y) =ᶠ[𝓝 x] u := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [hφ1 (subset_closure hy), Pi.one_apply, one_mul]
  exact hev.fderiv_eq

/-- On `∂Ω ⊆ Ω̄`, `φ ≡ 1` gives `φu = u` (paper part 1: "Right side"). -/
theorem eqOn_cutoff_mul_frontier {φ u : (EN m) → ℝ} {Ω : Set (EN m)}
    (hφ1 : EqOn φ 1 (closure Ω)) :
    EqOn (fun y => φ y * u y) u (frontier Ω) := by
  intro x hx
  show φ x * u x = u x
  rw [hφ1 (frontier_subset_closure hx), Pi.one_apply, one_mul]

/-- The cutoff product is `C¹` with compact support (paper part 1,
Claims 1–2: product rule plus `supp(φu) ⊆ supp φ`; the extension by
zero outside `O` is handled by gluing the two open regions `O` and
`(supp φ)ᶜ`, no explicit `tilde f` construction needed). -/
theorem contDiff_cutoff_mul {φ u : (EN m) → ℝ} {O : Set (EN m)} (hO : IsOpen O)
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

end


/-
=== GeneralizedDivergence.LocalComputation ===

# Step 3: the direct computation over a flat chart (paper proof step 3, §3.3)

The heart of the proof, with the rigid motion normalized away
(`T = id`): for `u ∈ C¹_c(ℝⁿ)` and `g ∈ C¹(ℝⁿ⁻¹)`,

    ∫_{Σ_g} Du·w  =  ∫_{ℝⁿ⁻¹} u(z, g z) ⟨(-∇g z, 1), w⟩ dz ,

split into the vertical direction (pure FTC) and the horizontal
directions (the shear `v(z, s) = u(z, g z + s)`, chain rule, and the
vanishing integral of `v_{x_i}` — the latter via the cutoff
integration-by-parts lemma from `Divergence.Cutoff`, sliced at fixed
height).

Everything here is stated for a *global* `C¹` function `g` and a
*globally* compactly supported `u` — no cylinder is needed at this
stage; localization happens in `Main`.
-/

section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal Topology

variable {m : ℕ}

/-! ### The product split `ℝⁿ = ℝⁿ⁻¹ × ℝ` as a measure identity -/

/-- Lebesgue measure on `(EN m)` is the product measure through the
`WithLp` identification — the Fubini workhorse for every iterated
integral in this file (paper: "By Fubini's theorem…"). -/
theorem measurePreserving_toLp :
    MeasurePreserving (WithLp.toLp 2 : (EM m) × ℝ → (EN m))
      (volume.prod volume) volume := by
  have h := WithLp.volume_preserving_toLp (EM m) ℝ
  rwa [Measure.volume_eq_prod] at h

/-! ### Elementary derivative helpers -/

/-- Derivative of an affine line `t ↦ p + t • v`. -/
private lemma hasDerivAt_line {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (p v : F) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => p + t • v) v t₀ := by
  simpa using ((hasDerivAt_id t₀).smul_const v).const_add p

private lemma contDiff_toLp_pair :
    ContDiff ℝ 1 fun q : (EM m) × ℝ => (WithLp.toLp 2 q : (EN m)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (EM m) ℝ).symm.contDiff

/-- The vertical line through `(z, ·)` as a curve in `(EN m)` has constant
derivative `e₃ = (0, 1)`. -/
private lemma hasDerivAt_vertLine (z : (EM m)) (a s : ℝ) :
    HasDerivAt (fun s' : ℝ => (WithLp.toLp 2 (z, a + s') : (EN m)))
      (WithLp.toLp 2 (0, 1)) s := by
  have hEq : ∀ s' : ℝ, (WithLp.toLp 2 (z, a + s') : (EN m))
      = WithLp.toLp 2 (z, a) + s' • WithLp.toLp 2 (0, 1) := by
    intro s'
    apply EN_ext <;> simp
  refine HasDerivAt.congr_of_eventuallyEq ?_ (Eventually.of_forall hEq)
  exact hasDerivAt_line _ _ s

/-- Fixed-height slices of compactly supported functions on `(EN m)` are
compactly supported on `(EM m)`. -/
private lemma hasCompactSupport_slice_horiz {f : (EN m) → ℝ}
    (hcs : HasCompactSupport f) (s : ℝ) :
    HasCompactSupport fun z : (EM m) => f (WithLp.toLp 2 (z, s)) := by
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : (EM m)) R) fun z hz => ?_
  by_contra h0
  have hmem : (WithLp.toLp 2 (z, s) : (EN m)) ∈ tsupport f := subset_closure h0
  have hnorm : ‖(WithLp.toLp 2 (z, s) : (EN m))‖ ≤ R := by
    simpa [mem_closedBall_zero_iff] using hR hmem
  exact hz (by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_fst_le_norm_toLp z s).trans hnorm)

/-- Vertical slices of compactly supported functions on `(EN m)` are
compactly supported on `ℝ`. -/
private lemma hasCompactSupport_slice_vert {f : (EN m) → ℝ}
    (hcs : HasCompactSupport f) (z : (EM m)) :
    HasCompactSupport fun s : ℝ => f (WithLp.toLp 2 (z, s)) := by
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R) fun s hs => ?_
  by_contra h0
  have hmem : (WithLp.toLp 2 (z, s) : (EN m)) ∈ tsupport f := subset_closure h0
  have hnorm : ‖(WithLp.toLp 2 (z, s) : (EN m))‖ ≤ R := by
    simpa [mem_closedBall_zero_iff] using hR hmem
  exact hs (by
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact (abs_snd_le_norm_toLp z s).trans hnorm)

/-- Composition with `graphMap` preserves compact support (the graph of
`g` over a bounded set is bounded horizontally). -/
private lemma hasCompactSupport_comp_graphMap {f : (EN m) → ℝ}
    (hcs : HasCompactSupport f) (g : (EM m) → ℝ) :
    HasCompactSupport fun z : (EM m) => f (graphMap g z) := by
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : (EM m)) R) fun z hz => ?_
  by_contra h0
  have hmem : graphMap g z ∈ tsupport f := subset_closure h0
  have hnorm : ‖graphMap g z‖ ≤ R := by
    simpa [mem_closedBall_zero_iff] using hR hmem
  exact hz (by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_fst_le_norm_toLp z (g z)).trans hnorm)

/-- Differentiating a fixed-height slice: the slice derivative in the
direction `w'` is the ambient derivative in the direction `(w', 0)`. -/
private lemma fderiv_slice {f : (EN m) → ℝ} (hf : ContDiff ℝ 1 f) (s : ℝ)
    (z w' : (EM m)) :
    fderiv ℝ (fun z' : (EM m) => f (WithLp.toLp 2 (z', s))) z w'
      = fderiv ℝ f (WithLp.toLp 2 (z, s)) (WithLp.toLp 2 (w', 0)) := by
  set ι : (EM m) → (EN m) := fun z' => WithLp.toLp 2 (z', s) with hι
  have hιC : ContDiff ℝ 1 ι :=
    contDiff_toLp_pair.comp (contDiff_id.prodMk contDiff_const)
  have hcurve : ∀ t : ℝ, ι (z + t • w') = ι z + t • (WithLp.toLp 2 (w', 0) : (EN m)) := by
    intro t
    apply EN_ext <;> simp [hι]
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
`ℝⁿ⁻¹ × ℝ`. -/
private def shearHomeo {g : (EM m) → ℝ} (hg : Continuous g) :
    ((EM m) × ℝ) ≃ₜ ((EM m) × ℝ) where
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
def shear (g : (EM m) → ℝ) (u : (EN m) → ℝ) : (EN m) → ℝ :=
  fun p => u (WithLp.toLp 2 (horiz p, g (horiz p) + vert p))

private lemma contDiff_shearMap {g : (EM m) → ℝ} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 fun p : (EN m) => (WithLp.toLp 2 (horiz p, g (horiz p) + vert p) : (EN m)) := by
  have hh : ContDiff ℝ 1 horiz :=
    contDiff_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ (EM m) ℝ).contDiff
  have hv : ContDiff ℝ 1 vert :=
    contDiff_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ (EM m) ℝ).contDiff
  exact contDiff_toLp_pair.comp (hh.prodMk ((hg.comp hh).add hv))

/-- The shear of a `C¹` function is `C¹` (composition of `C¹` maps;
paper's Lemma "Compact Support of v", first sentence). -/
theorem contDiff_shear {g : (EM m) → ℝ} (hg : ContDiff ℝ 1 g) {u : (EN m) → ℝ}
    (hu : ContDiff ℝ 1 u) : ContDiff ℝ 1 (shear g u) :=
  hu.comp (contDiff_shearMap hg)

/-- The shear of a compactly supported function is compactly supported.
(Unlike the paper, no cylinder is needed: `supp u ⊆ B(0, R)` forces
`‖z‖ ≤ R` and `|g z + s| ≤ R`, and `g` is bounded on the compact disk,
so `s` is bounded too.) -/
theorem hasCompactSupport_shear {g : (EM m) → ℝ} (hg : Continuous g)
    {u : (EN m) → ℝ} (hcs : HasCompactSupport u) :
    HasCompactSupport (shear g u) := by
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : (EM m)) R).exists_bound_of_continuousOn
    hg.continuousOn
  set K : Set (EN m) := {p | ‖horiz p‖ ≤ R ∧ |vert p| ≤ R + C} with hK
  have hKclosed : IsClosed K :=
    (isClosed_le (continuous_norm.comp continuous_horiz) continuous_const).inter
      (isClosed_le continuous_vert.abs continuous_const)
  have hKbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : (EN m))) (r := R + (R + C))).subset ?_
    rintro p ⟨h1, h2⟩
    have : ‖p‖ ≤ ‖horiz p‖ + |vert p| := by
      conv_lhs => rw [← toLp_horiz_vert p]
      exact norm_toLp_le _ _
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  refine HasCompactSupport.intro
    (Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd) fun p hp => ?_
  by_contra h0
  have hmem : (WithLp.toLp 2 (horiz p, g (horiz p) + vert p) : (EN m)) ∈ tsupport u :=
    subset_closure h0
  have hnorm : ‖(WithLp.toLp 2 (horiz p, g (horiz p) + vert p) : (EN m))‖ ≤ R := by
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
theorem fderiv_shear_horizontal {g : (EM m) → ℝ} (hg : ContDiff ℝ 1 g)
    {u : (EN m) → ℝ} (hu : ContDiff ℝ 1 u) (p : (EN m)) (w' : (EM m)) :
    fderiv ℝ (shear g u) p (WithLp.toLp 2 (w', 0))
      = fderiv ℝ u (WithLp.toLp 2 (horiz p, g (horiz p) + vert p))
          (WithLp.toLp 2 (w', fderiv ℝ g (horiz p) w')) := by
  set v : (EN m) := WithLp.toLp 2 (w', 0) with hv
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
      (fun t : ℝ => (WithLp.toLp 2 (horiz p + t • w', g (horiz p + t • w') + vert p) : (EN m)))
      (WithLp.toLp 2 (w', fderiv ℝ g (horiz p) w')) 0 := by
    have hP : HasFDerivAt (WithLp.prodContinuousLinearEquiv 2 ℝ (EM m) ℝ).symm
        ((WithLp.prodContinuousLinearEquiv 2 ℝ (EM m) ℝ).symm : ((EM m) × ℝ) →L[ℝ] (EN m))
        ((horiz p + (0 : ℝ) • w', g (horiz p + (0 : ℝ) • w') + vert p) : (EM m) × ℝ) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ (EM m) ℝ).symm.hasFDerivAt
    exact hP.comp_hasDerivAt 0 hpair
  have hu' : HasFDerivAt u
      (fderiv ℝ u (WithLp.toLp 2 (horiz p, g (horiz p) + vert p)))
      (WithLp.toLp 2 (horiz p + (0 : ℝ) • w', g (horiz p + (0 : ℝ) • w') + vert p) : (EN m)) := by
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
last coordinate, `∫_{Σ_g} ∂ₙu = ∫_{ℝⁿ⁻¹} u(z, g z) dz`. -/
theorem flat_vertical {g : (EM m) → ℝ} (hg : ContDiff ℝ 1 g) {u : (EN m) → ℝ}
    (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) :
    ∫ x in subgraphSet g, fderiv ℝ u x (WithLp.toLp 2 (0, 1))
      = ∫ z : (EM m), u (graphMap g z) := by
  set e3 : (EN m) := WithLp.toLp 2 (0, 1) with he3
  set F : (EM m) × ℝ → ℝ := fun q => fderiv ℝ u (WithLp.toLp 2 q) e3 with hF
  set R : Set ((EM m) × ℝ) := {q : (EM m) × ℝ | q.2 < g q.1} with hRdef
  -- Step A: transfer to the product space
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (EM m) × ℝ → (EN m)) :=
    (MeasurableEquiv.toLp 2 ((EM m) × ℝ)).measurableEmbedding
  have hstepA : ∫ x in subgraphSet g, fderiv ℝ u x e3
      = ∫ q in R, F q ∂(volume.prod volume) :=
    (measurePreserving_toLp.setIntegral_preimage_emb hemb
      (fun x => fderiv ℝ u x e3) (subgraphSet g)).symm
  -- continuity, support, measurability
  have hDu : Continuous fun x : (EN m) => fderiv ℝ u x e3 :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hFc : Continuous F :=
    hDu.comp (WithLp.prod_continuous_toLp 2 (EM m) ℝ)
  have hFcs : HasCompactSupport F :=
    (hasCompactSupport_fderiv_apply hcs e3).comp_homeomorph
      (WithLp.prodContinuousLinearEquiv 2 ℝ (EM m) ℝ).toHomeomorph.symm
  have hR : MeasurableSet R :=
    measurableSet_lt measurable_snd (hg.continuous.measurable.comp measurable_fst)
  have hFint : Integrable F (volume.prod volume) :=
    hFc.integrable_of_hasCompactSupport hFcs
  -- Step B: Fubini
  have hstepB : ∫ q in R, F q ∂(volume.prod volume)
      = ∫ z : (EM m), ∫ s in Iio (g z), F (z, s) := by
    rw [← integral_indicator hR, integral_prod _ (hFint.indicator hR)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show (∫ s : ℝ, R.indicator F (z, s)) = ∫ s in Iio (g z), F (z, s)
    rw [← integral_indicator measurableSet_Iio]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp [Set.indicator_apply, hRdef, Set.mem_Iio, Set.mem_setOf_eq]
  -- Step C: the inner FTC
  have hstepC : ∀ z : (EM m), ∫ s in Iio (g z), F (z, s) = u (graphMap g z) := by
    intro z
    set h : ℝ → ℝ := fun s => u (WithLp.toLp 2 (z, s)) with hh
    have hhC : ContDiff ℝ 1 h :=
      hu.comp (contDiff_toLp_pair.comp (contDiff_const.prodMk contDiff_id))
    have hhcs : HasCompactSupport h := hasCompactSupport_slice_vert hcs z
    have hderiv : ∀ s, F (z, s) = deriv h s := by
      intro s
      have hcurve : HasDerivAt (fun s' : ℝ => (WithLp.toLp 2 (z, s') : (EN m))) e3 s := by
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
`∫_{Σ_g} Du·(w',0) = −∫_{ℝⁿ⁻¹} u(z, g z) (∇g z · w') dz`. -/
theorem flat_horizontal {g : (EM m) → ℝ} (hg : ContDiff ℝ 1 g) {u : (EN m) → ℝ}
    (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) (w' : (EM m)) :
    ∫ x in subgraphSet g, fderiv ℝ u x (WithLp.toLp 2 (w', 0))
      = -∫ z : (EM m), u (graphMap g z) * fderiv ℝ g z w' := by
  set v : (EN m) := WithLp.toLp 2 (w', 0) with hv
  set e3 : (EN m) := WithLp.toLp 2 (0, 1) with he3
  set F : (EM m) × ℝ → ℝ := fun q => fderiv ℝ u (WithLp.toLp 2 q) v with hF
  set R : Set ((EM m) × ℝ) := {q : (EM m) × ℝ | q.2 < g q.1} with hRdef
  set R₀ : Set ((EM m) × ℝ) := {q : (EM m) × ℝ | q.2 < 0} with hR₀def
  -- Step A: transfer to the product space
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (EM m) × ℝ → (EN m)) :=
    (MeasurableEquiv.toLp 2 ((EM m) × ℝ)).measurableEmbedding
  have hstepA : ∫ x in subgraphSet g, fderiv ℝ u x v
      = ∫ q in R, F q ∂(volume.prod volume) :=
    (measurePreserving_toLp.setIntegral_preimage_emb hemb
      (fun x => fderiv ℝ u x v) (subgraphSet g)).symm
  -- Step B: the shear change of variables
  set Sh : (EM m) × ℝ → (EM m) × ℝ := fun q => (q.1, g q.1 + q.2) with hSh
  have hShmp : MeasurePreserving Sh (volume.prod volume) (volume.prod volume) := by
    have h := (MeasurePreserving.id (volume : Measure (EM m))).skew_product
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
  set A : (EM m) × ℝ → ℝ := fun q => fderiv ℝ (shear g u) (WithLp.toLp 2 q) v with hA
  set B : (EM m) × ℝ → ℝ :=
    fun q => fderiv ℝ g q.1 w' * fderiv ℝ u (WithLp.toLp 2 (Sh q)) e3 with hB
  have hsplit : ∀ q : (EM m) × ℝ, F (Sh q) = A q - B q := by
    intro q
    have hfsh := fderiv_shear_horizontal hg hu (WithLp.toLp 2 q) w'
    have hq1 : horiz (WithLp.toLp 2 q) = q.1 := rfl
    have hq2 : vert (WithLp.toLp 2 q) = q.2 := rfl
    rw [hq1, hq2] at hfsh
    have hdir : (WithLp.toLp 2 (w', fderiv ℝ g q.1 w') : (EN m))
        = v + (fderiv ℝ g q.1 w') • e3 := by
      apply EN_ext <;> simp [hv, he3]
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
      continuous_const).comp (WithLp.prod_continuous_toLp 2 (EM m) ℝ)
  have hAcs : HasCompactSupport A :=
    (hasCompactSupport_fderiv_apply
      (hasCompactSupport_shear hg.continuous hcs) v).comp_homeomorph
      (WithLp.prodContinuousLinearEquiv 2 ℝ (EM m) ℝ).toHomeomorph.symm
  have hAint : Integrable A (volume.prod volume) :=
    hAc.integrable_of_hasCompactSupport hAcs
  have hB2c : Continuous fun q : (EM m) × ℝ => fderiv ℝ u (WithLp.toLp 2 (Sh q)) e3 :=
    ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      ((WithLp.prod_continuous_toLp 2 (EM m) ℝ).comp hShcont)
  have hB2cs : HasCompactSupport fun q : (EM m) × ℝ => fderiv ℝ u (WithLp.toLp 2 (Sh q)) e3 := by
    have h := (hasCompactSupport_fderiv_apply hcs e3).comp_homeomorph
      ((shearHomeo hg.continuous).trans
        (WithLp.prodContinuousLinearEquiv 2 ℝ (EM m) ℝ).toHomeomorph.symm)
    have hcoe2 : ⇑((shearHomeo hg.continuous).trans
          (WithLp.prodContinuousLinearEquiv 2 ℝ (EM m) ℝ).toHomeomorph.symm)
        = fun q : (EM m) × ℝ => (WithLp.toLp 2 (Sh q) : (EN m)) := rfl
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
  have hregion : R₀ = (univ : Set (EM m)) ×ˢ Iio (0 : ℝ) := by
    ext q
    simp [hR₀def]
  have hDzero : ∫ q in R₀, A q ∂(volume.prod volume) = 0 := by
    rw [hregion, ← Measure.prod_restrict, Measure.restrict_univ]
    have hAint' : Integrable A (volume.prod (volume.restrict (Iio (0 : ℝ)))) := by
      have h := hAint.restrict (s := (univ : Set (EM m)) ×ˢ Iio (0 : ℝ))
      rwa [← Measure.prod_restrict, Measure.restrict_univ] at h
    have hswap := integral_integral_swap (f := fun z s => A (z, s)) hAint'
    -- ∫ z ∫ s, A = ∫ s ∫ z, A ; inner z-integral vanishes for each s
    have hinner : ∀ s : ℝ, ∫ z : (EM m), A (z, s) = 0 := by
      intro s
      have hψC : ContDiff ℝ 1 fun z : (EM m) => shear g u (WithLp.toLp 2 (z, s)) :=
        (contDiff_shear hg hu).comp
          (contDiff_toLp_pair.comp (contDiff_id.prodMk contDiff_const))
      have hψcs : HasCompactSupport fun z : (EM m) => shear g u (WithLp.toLp 2 (z, s)) :=
        hasCompactSupport_slice_horiz
          (hasCompactSupport_shear hg.continuous hcs) s
      have hcongr : ∀ z : (EM m), A (z, s)
          = fderiv ℝ (fun z' : (EM m) => shear g u (WithLp.toLp 2 (z', s))) z w' := by
        intro z
        exact (fderiv_slice (contDiff_shear hg hu) s z w').symm
      rw [integral_congr_ae (ae_of_all _ hcongr)]
      exact integral_fderiv_eq_zero' hψC hψcs w'
    calc ∫ q, A q ∂(volume.prod (volume.restrict (Iio (0:ℝ))))
        = ∫ z, ∫ s, A (z, s) ∂(volume.restrict (Iio (0:ℝ))) :=
          integral_prod _ hAint'
      _ = ∫ s, (∫ z : (EM m), A (z, s)) ∂(volume.restrict (Iio (0:ℝ))) := hswap
      _ = 0 := by simp [hinner]
  -- Step E: the graph term via FTC
  have hEterm : ∫ q in R₀, B q ∂(volume.prod volume)
      = ∫ z : (EM m), u (graphMap g z) * fderiv ℝ g z w' := by
    rw [hregion, ← Measure.prod_restrict, Measure.restrict_univ]
    have hBint' : Integrable B (volume.prod (volume.restrict (Iio (0 : ℝ)))) := by
      have := hBint.restrict (s := univ ×ˢ Iio (0:ℝ))
      rwa [← Measure.prod_restrict, Measure.restrict_univ] at this
    rw [integral_prod _ hBint']
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show (∫ s in Iio (0:ℝ), B (z, s)) = u (graphMap g z) * fderiv ℝ g z w'
    -- inner: ∫ s in Iio 0, Dg·w' * ∂ₙu(z, gz+s) = Dg·w' * u(z, g z)
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
    _ = -∫ z : (EM m), u (graphMap g z) * fderiv ℝ g z w' := by
        rw [hDzero, hEterm, zero_sub]

/-- **The flat divergence identity** (paper part 3, "In summary"):
combining the two directions,

    ∫_{Σ_g} Du·w = ∫_{ℝⁿ⁻¹} u(z, g z) · (⟨ν_g z, w⟩ · J_g z) dz ,

since `⟨ν_g z, w⟩ · J_g z = ⟨(-∇g z, 1), w⟩` — the paper's "1 = a/a
trick" run in reverse. -/
theorem flat_divergence {g : (EM m) → ℝ} (hg : ContDiff ℝ 1 g) {u : (EN m) → ℝ}
    (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) (w : (EN m)) :
    ∫ x in subgraphSet g, fderiv ℝ u x w
      = ∫ z : (EM m), u (graphMap g z) * (⟪unitNormal g z, w⟫ * jac g z) := by
  have hw : w = WithLp.toLp 2 (horiz w, 0) + vert w • WithLp.toLp 2 (0, 1) := by
    apply EN_ext <;> simp
  -- pointwise split of the direction
  have hptsplit : ∀ x : (EN m), fderiv ℝ u x w
      = fderiv ℝ u x (WithLp.toLp 2 (horiz w, 0))
        + vert w * fderiv ℝ u x (WithLp.toLp 2 (0, 1)) := by
    intro x
    conv_lhs => rw [hw]
    rw [map_add, map_smul, smul_eq_mul]
  -- integrand algebra on the right side
  have halg : ∀ z : (EM m), u (graphMap g z) * (⟪unitNormal g z, w⟫ * jac g z)
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
  have hDh : Continuous fun x : (EN m) => fderiv ℝ u x (WithLp.toLp 2 (horiz w, 0)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDv : Continuous fun x : (EN m) => fderiv ℝ u x (WithLp.toLp 2 (0, 1)) :=
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
  have hgu : Continuous fun z : (EM m) => u (graphMap g z) :=
    hu.continuous.comp (continuous_graphMap hg.continuous)
  have hgucs : HasCompactSupport fun z : (EM m) => u (graphMap g z) :=
    hasCompactSupport_comp_graphMap hcs g
  have intR1 : Integrable (fun z : (EM m) => u (graphMap g z) * fderiv ℝ g z (horiz w))
      volume :=
    (hgu.mul ((hg.continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).integrable_of_hasCompactSupport hgucs.mul_right
  have intR2 : Integrable (fun z : (EM m) => u (graphMap g z)) volume :=
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
    _ = (-∫ z : (EM m), u (graphMap g z) * fderiv ℝ g z (horiz w))
          + vert w * ∫ z : (EM m), u (graphMap g z) := by
        rw [flat_horizontal hg hu hcs (horiz w), integral_const_mul,
          flat_vertical hg hu hcs]
    _ = ∫ z : (EM m), (-(u (graphMap g z) * fderiv ℝ g z (horiz w))
          + vert w * u (graphMap g z)) := by
        have h1 : Integrable
            (fun z : (EM m) => -(u (graphMap g z) * fderiv ℝ g z (horiz w)))
            volume := intR1.neg
        have h2 : Integrable (fun z : (EM m) => vert w * u (graphMap g z)) volume :=
          intR2.const_mul (vert w)
        rw [integral_add h1 h2, integral_neg, integral_const_mul]
    _ = ∫ z : (EM m), u (graphMap g z) * (⟪unitNormal g z, w⟫ * jac g z) :=
        integral_congr_ae (ae_of_all _ fun z => (halg z).symm)

/-! ### Localization and rigid-motion transport -/

/-- If `f` is supported inside the cylinder, integrating over the full
subgraph or over its cylinder part is the same (needed to pass between
`flat_divergence` and the chart-local statement in `Main`). -/
theorem setIntegral_subgraph_of_support {g : (EM m) → ℝ} (hgc : Continuous g)
    {r ht : ℝ} {f : (EN m) → ℝ} (hsupp : tsupport f ⊆ cylinder g r ht) :
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
private lemma rigid_decomp (T : (EN m) ≃ᵃⁱ[ℝ] (EN m)) (x : (EN m)) :
    T x = T.linearIsometryEquiv x + T 0 := by
  simpa [add_comm] using T.map_vadd 0 x

/-- Rigid motions preserve Lebesgue measure: the linear part by
`LinearIsometryEquiv.measurePreserving`, the translation part by
right-invariance of Haar measure. -/
theorem measurePreserving_rigidMotion (T : (EN m) ≃ᵃⁱ[ℝ] (EN m)) :
    MeasurePreserving T volume volume := by
  have hdec : (T : (EN m) → (EN m)) = fun x => T.linearIsometryEquiv x + T 0 :=
    funext fun x => rigid_decomp T x
  rw [hdec]
  exact (measurePreserving_add_right volume (T 0)).comp
    T.linearIsometryEquiv.measurePreserving

/-- Rigid motions preserve Lebesgue integrals over images
(paper's Lemma "Invariance of the Divergence Theorem under Rigid
Motions", volume half): `∫_{T(S)} f = ∫_S f ∘ T`. -/
theorem setIntegral_image_rigidMotion (T : (EN m) ≃ᵃⁱ[ℝ] (EN m)) (S : Set (EN m))
    (f : (EN m) → ℝ) :
    ∫ x in T '' S, f x = ∫ y in S, f (T y) :=
  (measurePreserving_rigidMotion T).setIntegral_image_emb
    T.toHomeomorph.measurableEmbedding f S

/-- Chain rule under a rigid motion: `D(u ∘ T) y w = D u (T y) (T₀ w)`
with `T₀` the linear part (invariance lemma, derivative half). -/
theorem fderiv_comp_rigidMotion (T : (EN m) ≃ᵃⁱ[ℝ] (EN m)) {u : (EN m) → ℝ}
    (hu : ContDiff ℝ 1 u) (y : (EN m)) (w : (EN m)) :
    fderiv ℝ (fun x => u (T x)) y w
      = fderiv ℝ u (T y) (T.linearIsometryEquiv w) := by
  have hT : HasFDerivAt (T : (EN m) → (EN m))
      (T.linearIsometryEquiv.toContinuousLinearEquiv : (EN m) →L[ℝ] (EN m)) y := by
    have h := (T.linearIsometryEquiv.toContinuousLinearEquiv.hasFDerivAt
      (x := y)).add_const (T 0)
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    exact rigid_decomp T x
  have hu' : HasFDerivAt u (fderiv ℝ u (T y)) (T y) :=
    ((hu.differentiable one_ne_zero) _).hasFDerivAt
  have hcomp := hu'.comp y hT
  have hfd : fderiv ℝ (fun x => u (T x)) y
      = (fderiv ℝ u (T y)).comp
          (T.linearIsometryEquiv.toContinuousLinearEquiv : (EN m) →L[ℝ] (EN m)) :=
    hcomp.fderiv
  rw [hfd]
  rfl

end


/-
=== GeneralizedDivergence.PartitionOfUnity ===


-/

section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal Topology Manifold

/-
# Step 2: chart cover, partition of unity, and the interior case
(paper proof step 2, §3.2)

Compactness of `∂Ω` gives finitely many cylinder charts `U₁, …, U_N`;
`{Ω, U₁, …, U_N}` covers `Ω̄`; a partition of unity subordinate to this
cover splits `u = Σ ψₖ u` into pieces supported either inside `Ω` or
inside one chart.  The interior pieces contribute `0` to both sides
(the vanishing-integral lemma from `Divergence.Cutoff` on the left,
`u = 0` near `∂Ω` on the right).

The partition comes from mathlib's `SmoothPartitionOfUnity` (ℝⁿ is
T2 + σ-compact, modelled by `𝓘(ℝ, (EN m))`); compact supports come for free
because every element of the cover is bounded (`Ω` by hypothesis, the
chart cylinders because `g` is bounded on the closed disk). -/

variable {m : ℕ}

variable {Ω : Set (EN m)}

/-- Graph cylinders are bounded sets. -/
private lemma isBounded_cylinder {g : (EM m) → ℝ} (hg : Continuous g) (r ht : ℝ) :
    Bornology.IsBounded (cylinder g r ht) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : (EM m)) r).exists_bound_of_continuousOn
    hg.continuousOn
  refine (Metric.isBounded_closedBall (x := (0 : (EN m))) (r := r + (C + ht))).subset ?_
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
    ∃ ψ : Fin (N + 1) → (EN m) → ℝ,
      (∀ k, ContDiff ℝ 1 (ψ k)) ∧
      (∀ k, HasCompactSupport (ψ k)) ∧
      (∀ k x, ψ k x ∈ Icc (0 : ℝ) 1) ∧
      tsupport (ψ 0) ⊆ Ω ∧
      (∀ i : Fin N, tsupport (ψ i.succ) ⊆ (c i).U) ∧
      EqOn (fun x => ∑ k, ψ k x) 1 (closure Ω) := by
  set U : Fin (N + 1) → Set (EN m) := Fin.cons Ω (fun i => (c i).U) with hUdef
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
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, (EN m))
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
C¹ Functions", total form on ℝⁿ): a compactly supported `C¹` function
has vanishing total directional-derivative integral.  Specializes the
cutoff-and-integrate-by-parts lemma from `Divergence.Cutoff`. -/
theorem integral_fderiv_eq_zero {u : (EN m) → ℝ} (hu : ContDiff ℝ 1 u)
    (hcs : HasCompactSupport u) (w : (EN m)) :
    ∫ x, fderiv ℝ u x w = 0 :=
  integral_fderiv_eq_zero' hu hcs w

/-- Interior case, left side: `∫_Ω Du·w = ∫_{ℝⁿ} Du·w = 0`
(paper part 2, first display). -/
theorem divergence_interior_case (hΩ : IsOpen Ω) {u : (EN m) → ℝ}
    (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u)
    (hsupp : tsupport u ⊆ Ω) (w : (EN m)) :
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
theorem boundary_integral_interior_case (hΩ : IsOpen Ω) {u : (EN m) → ℝ}
    (hsupp : tsupport u ⊆ Ω) (ν : (EN m) → (EN m)) (w : (EN m)) :
    ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[m] = 0 := by
  have hzero : ∀ x ∈ frontier Ω, u x * ⟪ν x, w⟫ = 0 := by
    intro x hx
    have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      (hΩ.frontier_eq ▸ hx).2 (hsupp h)
    rw [hu0, zero_mul]
  calc ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[m]
      = ∫ _ in frontier Ω, (0 : ℝ) ∂μHE[m] :=
        setIntegral_congr_fun isClosed_frontier.measurableSet hzero
    _ = 0 := by simp

end


/-
=== GeneralizedDivergence.SurfaceIntegral ===

# The surface integral: from `μHE[m]` on `∂Ω` to parameterized integrals
(paper §2.3, §3.3 Steps 4–8, and the Lemma "Surface Element on a Graph")

The boundary integral `∫_{∂Ω} f dS` is interpreted against Mathlib's
Euclidean 2-dimensional Hausdorff measure `μHE[m]` restricted to
`frontier Ω` — the canonical, chart-free surface measure.  This file
connects it to the concrete parameterized form the paper computes with:

    ∫_{graph g V} f dμHE[m]  =  ∫_V f(z, g z) √(1+|∇g|²) dz .

**This is where the completed GeneralizedGraph project is loaded**: its
`area_formula` (`μHE[m](Γ_g|_U) = ∫_U jac g`), applied to every open
set, upgrades by π-system uniqueness to the pushforward identity
`restrict_graph_eq_map`, and the weighted integral formula follows via
`MeasureTheory.integral_map`.

Hypothesis convention: `g` is globally `C¹` and `V` is bounded — this
matches the cylinder charts (whose `g` is global and whose base is a
disk) and keeps both measures finite, so the π-system argument needs no
exhaustion.
-/

section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology

variable {m : ℕ}

/-- Global continuity of the Jacobian factor of a `C¹` function. -/
lemma continuous_jac {g : (EM m) → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (jac g) := by
  have h : Continuous fun z => Real.sqrt (1 + ‖fderiv ℝ g z‖ ^ 2) :=
    Real.continuous_sqrt.comp
      (continuous_const.add ((hg.continuous_fderiv one_ne_zero).norm.pow 2))
  exact h

/-- The graph of a globally `C¹` function over a bounded set has finite
area (the Jacobian is bounded on the closure). -/
lemma graph_measure_lt_top (hm : 0 < m) {V : Set (EM m)} {g : (EM m) → ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hg : ContDiff ℝ 1 g) :
    μHE[m] (graph g V) < ∞ := by
  obtain ⟨C, hC⟩ := hVb.isCompact_closure.exists_bound_of_continuousOn
    (continuous_jac hg).continuousOn
  have hvol : volume V < ∞ :=
    lt_of_le_of_lt (measure_mono subset_closure) hVb.isCompact_closure.measure_lt_top
  calc μHE[m] (graph g V)
      = ∫⁻ z in V, ENNReal.ofReal (jac g z) := area_formula hm hV hg.contDiffOn
    _ ≤ ∫⁻ _ in V, ENNReal.ofReal C := by
        refine setLIntegral_mono measurable_const fun z hz => ?_
        exact ENNReal.ofReal_le_ofReal (by
          have := hC z (subset_closure hz)
          rwa [Real.norm_eq_abs, abs_of_pos (jac_pos z)] at this)
    _ = ENNReal.ofReal C * volume V := by rw [setLIntegral_const]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol

/-- **Weighted area formula** (the surface-element lemma, measure
form): on the graph of a `C¹` function over a bounded open base,
`μHE[m]` is the pushforward of the Jacobian-weighted Lebesgue measure.
Strengthens `GeneralizedGraph.area_formula` from a single measure identity to
a pushforward identity, by applying it to every open set and invoking
π-system uniqueness. -/
theorem restrict_graph_eq_map (hm : 0 < m) {V : Set (EM m)} {g : (EM m) → ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hg : ContDiff ℝ 1 g) :
    μHE[m].restrict (graph g V)
      = Measure.map (graphMap g)
          ((volume.restrict V).withDensity fun z => ENNReal.ofReal (jac g z)) := by
  have hΦcont : Continuous (graphMap g) := continuous_graphMap hg.continuous
  -- agreement on every open set, via the area formula
  have h_eq : ∀ O : Set (EN m), IsOpen O →
      μHE[m].restrict (graph g V) O
        = Measure.map (graphMap g)
            ((volume.restrict V).withDensity fun z => ENNReal.ofReal (jac g z)) O := by
    intro O hO
    have hpre : IsOpen (V ∩ graphMap g ⁻¹' O) := hV.inter (hO.preimage hΦcont)
    have himg : O ∩ graph g V = graph g (V ∩ graphMap g ⁻¹' O) := by
      show O ∩ graphMap g '' V = graphMap g '' (V ∩ graphMap g ⁻¹' O)
      rw [Set.image_inter_preimage, Set.inter_comm]
    calc μHE[m].restrict (graph g V) O
        = μHE[m] (O ∩ graph g V) := Measure.restrict_apply hO.measurableSet
      _ = μHE[m] (graph g (V ∩ graphMap g ⁻¹' O)) := by rw [himg]
      _ = ∫⁻ z in V ∩ graphMap g ⁻¹' O, ENNReal.ofReal (jac g z) :=
          area_formula hm hpre hg.contDiffOn
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
  refine Measure.ext_of_generateFrom_of_iUnion {s : Set (EN m) | IsOpen s}
    (fun _ => univ) BorelSpace.measurable_eq ?_ ?_ ?_ ?_ ?_
  · rintro s (hs : IsOpen s) t (ht : IsOpen t) -
    exact hs.inter ht
  · exact Set.iUnion_const _
  · intro i
    show IsOpen (univ : Set (EN m))
    exact isOpen_univ
  · intro _
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact (graph_measure_lt_top hm hV hVb hg).ne
  · exact fun s hs => h_eq s hs

/-- **Surface integral over a graph patch** (paper §3.3 Step 5, the
definition the paper takes; here it is a theorem about `μHE[m]`):
`∫_{Γ_g|_V} F dμHE[m] = ∫_V F(z, g z) · J_g z dz`. -/
theorem integral_graph (hm : 0 < m) {V : Set (EM m)} {g : (EM m) → ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hg : ContDiff ℝ 1 g)
    {F : (EN m) → ℝ} (hF : Continuous F) :
    ∫ x in graph g V, F x ∂μHE[m]
      = ∫ z in V, F (graphMap g z) * jac g z := by
  have hΦcont : Continuous (graphMap g) := continuous_graphMap hg.continuous
  rw [show (∫ x in graph g V, F x ∂μHE[m])
      = ∫ x, F x ∂(μHE[m].restrict (graph g V)) from rfl,
    restrict_graph_eq_map hm hV hVb hg,
    integral_map hΦcont.measurable.aemeasurable hF.aestronglyMeasurable]
  have hdens : (fun z : (EM m) => ENNReal.ofReal (jac g z))
      = fun z : (EM m) => ((Real.toNNReal (jac g z) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hdens, integral_withDensity_eq_integral_smul
    ((continuous_jac hg).measurable.real_toNNReal) fun z => F (graphMap g z)]
  refine setIntegral_congr_fun hV.measurableSet fun z _ => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (jac_pos z).le, smul_eq_mul, mul_comm]

/-- Rigid motions preserve `μHE[m]` (mathlib's
`Isometry.euclideanHausdorffMeasure_image` applied to the inverse). -/
theorem measurePreserving_rigidMotion_muHE (T : (EN m) ≃ᵃⁱ[ℝ] (EN m)) :
    MeasurePreserving T (μHE[m] : Measure (EN m)) μHE[m] := by
  have hm : Measurable (T : (EN m) → (EN m)) := T.isometry.continuous.measurable
  refine ⟨hm, ?_⟩
  ext A hA
  rw [Measure.map_apply hm hA]
  have hpre : (T : (EN m) → (EN m)) ⁻¹' A = T.symm '' A := by
    ext x
    constructor
    · intro hx
      exact ⟨T x, hx, T.symm_apply_apply x⟩
    · rintro ⟨a, ha, rfl⟩
      simpa [T.apply_symm_apply] using ha
  rw [hpre]
  exact T.symm.isometry.euclideanHausdorffMeasure_image A

/-- Rigid motions preserve `μHE[m]`-integrals over images (invariance
lemma, surface half). -/
theorem surfaceIntegral_image_rigidMotion (T : (EN m) ≃ᵃⁱ[ℝ] (EN m)) (S : Set (EN m))
    (f : (EN m) → ℝ) :
    ∫ x in T '' S, f x ∂μHE[m] = ∫ y in S, f (T y) ∂μHE[m] :=
  (measurePreserving_rigidMotion_muHE T).setIntegral_image_emb
    T.toHomeomorph.measurableEmbedding f S

/-- **Chart-local surface integral** (paper §3.3 Steps 6–8): for `F`
supported inside a chart `c`, the boundary integral is the
parameterized integral over the disk.  Combines `frontier_inter_U`
(the boundary piece is the moved graph), rigid-motion invariance of
`μHE[m]`, and `integral_graph`. -/
theorem surface_integral_chart (hm : 0 < m) {Ω : Set (EN m)} (hΩ : IsOpen Ω)
    (c : CylinderChart Ω) {F : (EN m) → ℝ} (hF : Continuous F)
    (hsupp : tsupport F ⊆ c.U) :
    ∫ x in frontier Ω, F x ∂μHE[m]
      = ∫ z in Metric.ball (0 : (EM m)) c.r,
          F (c.T (graphMap c.g z)) * jac c.g z := by
  have hfeq : ∀ x, F x = (c.U).indicator F x := by
    intro x
    by_cases hx : x ∈ c.U
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)]
  have hsplit : ∫ x in frontier Ω, F x ∂μHE[m]
      = ∫ x in frontier Ω ∩ c.U, F x ∂μHE[m] := by
    calc ∫ x in frontier Ω, F x ∂μHE[m]
        = ∫ x in frontier Ω, (c.U).indicator F x ∂μHE[m] :=
          setIntegral_congr_fun isClosed_frontier.measurableSet
            fun x _ => hfeq x
      _ = ∫ x in frontier Ω ∩ c.U, F x ∂μHE[m] :=
          setIntegral_indicator c.isOpen_U.measurableSet
  have hFT : Continuous fun y : (EN m) => F (c.T y) :=
    hF.comp c.T.isometry.continuous
  rw [hsplit, c.frontier_inter_U hΩ,
    surfaceIntegral_image_rigidMotion c.T (graph c.g (Metric.ball (0 : (EM m)) c.r)) F,
    integral_graph hm Metric.isOpen_ball Metric.isBounded_ball c.hg hFT]

end


/-
=== GeneralizedDivergence.Main ===

# The divergence theorem (paper Theorem + §3.3 Step 9, "Propagate back")

Assembly, following the paper's three reductions in reverse:

* `divergence_chart_case` — `u` compactly supported in one chart
  (Reduction A, second case): transport `flat_divergence` through the
  rigid motion and identify the right side by `surface_integral_chart`;
  the normal field agrees with the chart normal by the uniqueness
  theorem `IsOutwardNormalAt.eq_chart_normal`.
* `divergence_compact_support` — arbitrary `u ∈ C¹_c(ℝⁿ)`
  (Reduction B): split `u = Σ ψₖ u` by the partition of unity;
  the interior piece contributes zero to both sides.
* `divergence_theorem` — the paper's Theorem, `u ∈ C¹(O)`,
  `O ⊇ Ω̄` open (Reduction C): cut off by `φ`.
* `divergence_theorem_vector_field` — the classical `div`/flux form,
  by summing the scalar theorem over an orthonormal basis.

Statement conventions: `Ω ⊆ ℝⁿ` open, bounded, with C¹ boundary; the
volume integral is Lebesgue (`volume` on `(EN m)`), the surface integral is
against `μHE[m]` restricted to `frontier Ω`; `ν` is any outward unit
normal field in the geometric sense (`IsOutwardNormal`); the scalar
theorem is stated directionally (`w ∈ ℝⁿ` arbitrary), which is the
paper's "equivalently, ∫ ∇u = ∫ u ν" form all at once.
-/

section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal Topology

variable {m : ℕ}

variable {Ω : Set (EN m)}

/-! ### Infrastructure: the finite surface measure and integrability of
normal-field integrands on the boundary -/

/-- A bounded C¹ boundary has finite area: finitely many chart patches,
each an isometric image of a graph over a disk. -/
theorem measure_frontier_lt_top (hm : 0 < m) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) : μHE[m] (frontier Ω) < ∞ := by
  obtain ⟨N, c, hcover⟩ := exists_finite_chart_cover hb hC1
  calc μHE[m] (frontier Ω)
      ≤ μHE[m] (⋃ i, frontier Ω ∩ (c i).U) := by
        refine measure_mono fun x hx => ?_
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
        exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
    _ ≤ ∑ i, μHE[m] (frontier Ω ∩ (c i).U) := measure_iUnion_fintype_le _ _
    _ < ∞ := by
        refine ENNReal.sum_lt_top.mpr fun i _ => ?_
        rw [(c i).frontier_inter_U hΩ,
          (c i).T.isometry.euclideanHausdorffMeasure_image]
        exact graph_measure_lt_top hm Metric.isOpen_ball Metric.isBounded_ball (c i).hg

/-- The graph normal, read back through the chart — a globally defined
*continuous* stand-in for the outward normal field on the chart patch. -/
private def chartNormalField (c : CylinderChart Ω) : (EN m) → (EN m) :=
  fun x => c.T.linearIsometryEquiv (unitNormal c.g (horiz (c.T.symm x)))

private lemma continuous_unitNormal {g : (EM m) → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous fun z => unitNormal g z := by
  have hgrad : Continuous fun z => gradient g z := by
    have h1 : Continuous fun z => fderiv ℝ g z := hg.continuous_fderiv one_ne_zero
    exact (InnerProductSpace.toDual ℝ (EM m)).symm.continuous.comp h1
  have hjac : Continuous fun z => (jac g z)⁻¹ :=
    (continuous_jac hg).inv₀ fun z => (jac_pos z).ne'
  exact hjac.smul ((WithLp.prod_continuous_toLp 2 (EM m) ℝ).comp
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
    {f : (EN m) → ℝ} (hsupp : tsupport f ⊆ c.U) {ν : (EN m) → (EN m)}
    (hν : IsOutwardNormal Ω ν) (w : (EN m)) :
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
private lemma integrableOn_frontier_piece (hm : 0 < m) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    (c : CylinderChart Ω) {f : (EN m) → ℝ} (hf : Continuous f)
    (hsupp : tsupport f ⊆ c.U) {ν : (EN m) → (EN m)} (hν : IsOutwardNormal Ω ν)
    (w : (EN m)) :
    IntegrableOn (fun x => f x * ⟪ν x, w⟫) (frontier Ω) μHE[m] := by
  have hcont : Continuous fun x => f x * ⟪chartNormalField c x, w⟫ :=
    hf.mul ((continuous_chartNormalField c).inner continuous_const)
  haveI : IsFiniteMeasure (μHE[m].restrict (frontier Ω)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_frontier_lt_top hm hΩ hb hC1
  obtain ⟨C, hC⟩ := (isCompact_frontier hb).exists_bound_of_continuousOn
    hcont.continuousOn
  have hint : IntegrableOn (fun x => f x * ⟪chartNormalField c x, w⟫)
      (frontier Ω) μHE[m] := by
    refine (integrable_const C).mono' hcont.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem isClosed_frontier.measurableSet fun x hx => by
      simpa using hC x hx
  exact hint.congr_fun (fun x hx => (frontier_integrand_eq hΩ c hsupp hν w x hx).symm)
    isClosed_frontier.measurableSet

/-- Any continuous coefficient times a normal-field inner product is
integrable on the boundary: split by a partition of unity so each piece
is chart-supported. -/
private lemma integrableOn_frontier_inner (hm : 0 < m) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {f : (EN m) → ℝ}
    (hf : Continuous f) {ν : (EN m) → (EN m)} (hν : IsOutwardNormal Ω ν) (w : (EN m)) :
    IntegrableOn (fun x => f x * ⟪ν x, w⟫) (frontier Ω) μHE[m] := by
  obtain ⟨N, c, hcover⟩ := exists_finite_chart_cover hb hC1
  obtain ⟨ψ, hψC, -, -, hψ0, hψsucc, hψsum⟩ :=
    exists_partition_of_unity hΩ hb c hcover
  have hpieces : ∀ k : Fin (N + 1),
      IntegrableOn (fun x => ψ k x * f x * ⟪ν x, w⟫) (frontier Ω) μHE[m] := by
    refine Fin.cases ?_ ?_
    · refine (integrableOn_zero.congr_fun (fun x hx => ?_)
        isClosed_frontier.measurableSet)
      have hψ00 : ψ 0 x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
        (hΩ.frontier_eq ▸ hx).2 (hψ0 h)
      simp [hψ00]
    · intro i
      have h := integrableOn_frontier_piece hm hΩ hb hC1 (c i)
        ((hψC i.succ).continuous.mul hf)
        (subset_trans tsupport_mul_subset_left (hψsucc i)) hν w
      exact h.congr_fun (fun x _ => by simp only [Pi.mul_apply])
        isClosed_frontier.measurableSet
  have hsum : IntegrableOn (fun x => ∑ k, ψ k x * f x * ⟪ν x, w⟫)
      (frontier Ω) μHE[m] :=
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
private lemma setIntegral_inter_of_tsupport {A O : Set (EN m)} {μ : Measure (EN m)}
    (hO : MeasurableSet O) {f : (EN m) → ℝ} (hsupp : tsupport f ⊆ O) :
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
theorem divergence_chart_case (hm : 0 < m) (hΩ : IsOpen Ω) (c : CylinderChart Ω)
    {u : (EN m) → ℝ} (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u)
    (hsupp : tsupport u ⊆ c.U)
    {ν : (EN m) → (EN m)} (hν : IsOutwardNormal Ω ν) (w : (EN m)) :
    ∫ x in Ω, fderiv ℝ u x w
      = ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[m] := by
  set T₀ := c.T.linearIsometryEquiv with hT₀
  set w₀ : (EN m) := T₀.symm w with hw₀
  set u' : (EN m) → ℝ := fun y => u (c.T y) with hu'def
  -- regularity of the pulled-back function
  have hTC : ContDiff ℝ 1 (c.T : (EN m) → (EN m)) := by
    have hdec : (c.T : (EN m) → (EN m)) = fun x => T₀ x + c.T 0 := funext fun x => by
      simpa [add_comm] using c.T.map_vadd 0 x
    rw [hdec]
    have h1 : ContDiff ℝ 1 fun x : (EN m) => T₀ x :=
      T₀.toContinuousLinearEquiv.contDiff
    exact h1.add contDiff_const
  have hu'C : ContDiff ℝ 1 u' := hu.comp hTC
  have hu'cs : HasCompactSupport u' := by
    have h := hcs.comp_homeomorph c.T.toHomeomorph
    exact h
  have hu'supp : tsupport u' ⊆ cylinder c.g c.r c.ht := by
    have hsub : tsupport u' ⊆ (c.T : (EN m) → (EN m)) ⁻¹' tsupport u := by
      refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport u).preimage
        c.T.isometry.continuous)
      exact subset_closure hx
    refine hsub.trans ?_
    rw [show cylinder c.g c.r c.ht = (c.T : (EN m) → (EN m)) ⁻¹' c.U from
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
      = ∫ z : (EM m), u' (graphMap c.g z) * (⟪unitNormal c.g z, w₀⟫ * jac c.g z) := by
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
      _ = ∫ z : (EM m), u' (graphMap c.g z) * (⟪unitNormal c.g z, w₀⟫ * jac c.g z) :=
          flat_divergence c.hg hu'C hu'cs w₀
  -- RHS: replace ν by the chart surrogate, localize, parameterize
  set Fc : (EN m) → ℝ := fun x => u x * ⟪chartNormalField c x, w⟫ with hFc
  have hFccont : Continuous Fc :=
    hu.continuous.mul ((continuous_chartNormalField c).inner continuous_const)
  have hFcsupp : tsupport Fc ⊆ c.U := by
    refine subset_trans (closure_minimal (fun x hx => ?_) (isClosed_tsupport u))
      hsupp
    by_contra hxs
    refine hx ?_
    show u x * ⟪chartNormalField c x, w⟫ = 0
    rw [image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  have hRHS : ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[m]
      = ∫ z : (EM m), u' (graphMap c.g z) * (⟪unitNormal c.g z, w₀⟫ * jac c.g z) := by
    calc ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[m]
        = ∫ x in frontier Ω, Fc x ∂μHE[m] :=
          setIntegral_congr_fun isClosed_frontier.measurableSet
            (frontier_integrand_eq hΩ c hsupp hν w)
      _ = ∫ z in Metric.ball (0 : (EM m)) c.r, Fc (c.T (graphMap c.g z)) * jac c.g z :=
          surface_integral_chart hm hΩ c hFccont hFcsupp
      _ = ∫ z in Metric.ball (0 : (EM m)) c.r,
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
      _ = ∫ z : (EM m), u' (graphMap c.g z) * (⟪unitNormal c.g z, w₀⟫ * jac c.g z) := by
          -- the integrand is supported in the disk
          have hzero : ∀ z ∉ Metric.ball (0 : (EM m)) c.r,
              u' (graphMap c.g z) * (⟪unitNormal c.g z, w₀⟫ * jac c.g z) = 0 := by
            intro z hz
            have hu'0 : u' (graphMap c.g z) = 0 := by
              refine image_eq_zero_of_notMem_tsupport fun h => hz ?_
              have := hu'supp h
              simpa [mem_ball_zero_iff] using this.1
            rw [hu'0, zero_mul]
          rw [← integral_indicator Metric.isOpen_ball.measurableSet]
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          by_cases hz : z ∈ Metric.ball (0 : (EM m)) c.r
          · simp [Set.indicator_of_mem hz]
          · rw [Set.indicator_of_notMem hz]
            exact (hzero z hz).symm
  rw [hLHS, hRHS]

/-- **Globally C¹ case** (paper Reduction B, slightly stronger: the
partition pieces provide their own compact supports, so `u ∈ C¹(ℝⁿ)`
suffices — no global compact support needed): the divergence identity
for globally `C¹` functions. -/
theorem divergence_compact_support (hm : 0 < m) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    {u : (EN m) → ℝ} (hu : ContDiff ℝ 1 u)
    {ν : (EN m) → (EN m)} (hν : IsOutwardNormal Ω ν) (w : (EN m)) :
    ∫ x in Ω, fderiv ℝ u x w
      = ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[m] := by
  obtain ⟨N, c, hcover⟩ := exists_finite_chart_cover hb hC1
  obtain ⟨ψ, hψC, hψcs, -, hψ0, hψsucc, hψsum⟩ :=
    exists_partition_of_unity hΩ hb c hcover
  set v : Fin (N + 1) → (EN m) → ℝ := fun k x => ψ k x * u x with hv
  have hvC : ∀ k, ContDiff ℝ 1 (v k) := fun k => (hψC k).mul hu
  have hvcs : ∀ k, HasCompactSupport (v k) := fun k => (hψcs k).mul_right
  have hvsupp0 : tsupport (v 0) ⊆ Ω :=
    subset_trans tsupport_mul_subset_left hψ0
  have hvsuppS : ∀ i : Fin N, tsupport (v i.succ) ⊆ (c i).U := fun i =>
    subset_trans tsupport_mul_subset_left (hψsucc i)
  -- each piece satisfies the identity
  have hpiece : ∀ k, ∫ x in Ω, fderiv ℝ (v k) x w
      = ∫ x in frontier Ω, v k x * ⟪ν x, w⟫ ∂μHE[m] := by
    refine Fin.cases ?_ ?_
    · rw [divergence_interior_case hΩ (hvC 0) (hvcs 0) hvsupp0 w,
        boundary_integral_interior_case hΩ hvsupp0 ν w]
    · intro i
      exact divergence_chart_case hm hΩ (c i) (hvC i.succ) (hvcs i.succ)
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
  have hR : ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[m]
      = ∑ k, ∫ x in frontier Ω, v k x * ⟪ν x, w⟫ ∂μHE[m] := by
    rw [← integral_finset_sum]
    · refine setIntegral_congr_fun isClosed_frontier.measurableSet fun x hx => ?_
      rw [husum x (frontier_subset_closure hx), Finset.sum_mul]
    · intro k _
      have h := integrableOn_frontier_inner hm hΩ hb hC1
        ((hψC k).continuous.mul hu.continuous) hν w
      exact h.congr_fun (fun x _ => by simp only [hv, Pi.mul_apply])
        isClosed_frontier.measurableSet
  rw [hL, hR]
  exact Finset.sum_congr rfl fun k _ => hpiece k

/-- **The Divergence Theorem** (the paper's Theorem, directional form):
`Ω ⊆ ℝⁿ` open, bounded, with C¹ boundary, `u ∈ C¹(O)` for an open
`O ⊇ Ω̄`, `ν` an outward unit normal field.  Then for every `w ∈ ℝⁿ`

    ∫_Ω Du·w dV = ∫_{∂Ω} u ⟨ν, w⟩ dS .

Taking `w = eᵢ` recovers the component form
`∫_Ω u_{x_i} = ∫_{∂Ω} u νᵢ`. -/
theorem divergence_theorem (hm : 0 < m) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {O : Set (EN m)} (hO : IsOpen O)
    (hΩO : closure Ω ⊆ O) {u : (EN m) → ℝ} (hu : ContDiffOn ℝ 1 u O)
    {ν : (EN m) → (EN m)} (hν : IsOutwardNormal Ω ν) (w : (EN m)) :
    ∫ x in Ω, fderiv ℝ u x w
      = ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[m] := by
  have hcl : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  obtain ⟨φ, hφC, hφcs, hφO, hφ1, -⟩ := exists_cutoff hcl hO hΩO
  obtain ⟨hφuC, -⟩ := contDiff_cutoff_mul hO hφC hφcs hφO hu
  calc ∫ x in Ω, fderiv ℝ u x w
      = ∫ x in Ω, fderiv ℝ (fun y => φ y * u y) x w := by
        refine setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
        rw [fderiv_cutoff_mul hΩ hφ1 hx]
    _ = ∫ x in frontier Ω, (fun y => φ y * u y) x * ⟪ν x, w⟫ ∂μHE[m] :=
        divergence_compact_support hm hΩ hb hC1 hφuC hν w
    _ = ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[m] := by
        refine setIntegral_congr_fun isClosed_frontier.measurableSet
          fun x hx => ?_
        rw [eqOn_cutoff_mul_frontier hφ1 hx]

/-! ### The classical vector-field form -/

/-- The divergence `div F = Σᵢ ⟨DF(eᵢ), eᵢ⟩` of a vector field, via the
standard orthonormal basis (basis-independent: it is the trace of
`DF`). -/
def div (F : (EN m) → (EN m)) (x : (EN m)) : ℝ :=
  ∑ i, ⟪fderiv ℝ F x (stdOrthonormalBasis ℝ (EN m) i), stdOrthonormalBasis ℝ (EN m) i⟫

/-- The vector cutoff product is `C¹` with compact support (`smul`
version of `contDiff_cutoff_mul`). -/
private lemma contDiff_cutoff_smul {φ : (EN m) → ℝ} {F : (EN m) → (EN m)} {O : Set (EN m)}
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
      refine (contDiffOn_const (c := (0 : (EN m)))).congr fun y hy => ?_
      rw [image_eq_zero_of_notMem_tsupport hy.2, zero_smul]
  · exact hφc.smul_right

/-- **Divergence theorem, flux form**: `∫_Ω div F dV = ∫_{∂Ω} F·ν dS`. -/
theorem divergence_theorem_vector_field (hm : 0 < m) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {O : Set (EN m)}
    (hO : IsOpen O) (hΩO : closure Ω ⊆ O) {F : (EN m) → (EN m)}
    (hF : ContDiffOn ℝ 1 F O) {ν : (EN m) → (EN m)} (hν : IsOutwardNormal Ω ν) :
    ∫ x in Ω, div F x
      = ∫ x in frontier Ω, ⟪F x, ν x⟫ ∂μHE[m] := by
  set b := stdOrthonormalBasis ℝ (EN m) with hb'
  -- cut off to a global C¹ field agreeing with F near Ω̄
  have hcl : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  obtain ⟨φ, hφC, hφcs, hφO, hφ1, -⟩ := exists_cutoff hcl hO hΩO
  obtain ⟨hGC, hGcs⟩ := contDiff_cutoff_smul hO hφC hφcs hφO hF
  set G : (EN m) → (EN m) := fun y => φ y • F y with hGdef
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
      = ∫ x in frontier Ω, ⟪G x, b i⟫ * ⟪ν x, b i⟫ ∂μHE[m] := fun i =>
    divergence_theorem hm hΩ hb hC1 isOpen_univ (subset_univ _)
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
      (fun x => ⟪G x, b i⟫ * ⟪ν x, b i⟫) (frontier Ω) μHE[m] := fun i =>
    integrableOn_frontier_inner hm hΩ hb hC1 (hGC.continuous.inner continuous_const)
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
    _ = ∑ i, ∫ x in frontier Ω, ⟪G x, b i⟫ * ⟪ν x, b i⟫ ∂μHE[m] :=
        Finset.sum_congr rfl fun i _ => hscalar i
    _ = ∫ x in frontier Ω, (∑ i, ⟪G x, b i⟫ * ⟪ν x, b i⟫) ∂μHE[m] :=
        (integral_finset_sum _ fun i _ => hintFr i).symm
    _ = ∫ x in frontier Ω, ⟪F x, ν x⟫ ∂μHE[m] := by
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

end


/-
=== GeneralizedDivergence.Applications ===

# Applying the divergence theorem — the PDE-facing API

This file is the part you actually reach for when you *use* the
divergence theorem: integration by parts, Green's identities, and the
flux form, packaged with the exact hypotheses you will have on hand in
a PDE argument (`Ω` open bounded with C¹ boundary, functions `C¹`/`C²`
on an open neighborhood `O ⊇ Ω̄`).

Contents:
* `integrableOn_of_continuousOn` — the integrability workhorse: anything
  continuous on `O` is integrable on the bounded `Ω`;
* `inner_gradient_apply`, `continuousOn_div`, `div_smul_eq` — pointwise
  calculus toolkit (`⟪∇u, w⟫ = Du·w`, continuity of `div`, and the
  product rule `div(u·F) = ⟪∇u, F⟫ + u·div F`);
* `integral_gradient_inner` — the scalar theorem in gradient form,
  `∫_Ω ⟪∇u, w⟫ = ∫_{∂Ω} u ⟪ν, w⟫`;
* `integration_by_parts` — `∫_Ω (Du·w) v = ∫_{∂Ω} u v ⟪ν, w⟫ − ∫_Ω u (Dv·w)`,
  THE identity behind every weak formulation and energy estimate;
* `laplacian` and `integral_laplacian_eq_flux` — `∫_Ω Δu = ∫_{∂Ω} ⟪∇u, ν⟫`;
* `green_first_identity` — `∫_Ω (u Δv + ⟪∇u, ∇v⟫) = ∫_{∂Ω} u ⟪∇v, ν⟫`;
* `green_second_identity` — `∫_Ω (u Δv − v Δu) = ∫_{∂Ω} u ⟪∇v,ν⟫ − ∫_{∂Ω} v ⟪∇u,ν⟫`.

See the `HOW TO USE` note at the bottom for the standard recipe.
-/

section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology

variable {m : ℕ} {Ω : Set (EN m)}

/-! ### Pointwise calculus toolkit -/

/-- `⟪∇u(x), w⟫ = Du(x)·w` — the gradient is the Riesz representative of
the Fréchet derivative (ambient-space version of `inner_gradient_eq`). -/
lemma inner_gradient_apply (u : EN m → ℝ) (x w : EN m) :
    ⟪gradient u x, w⟫ = fderiv ℝ u x w := by
  rw [gradient]
  exact InnerProductSpace.toDual_symm_apply

/-- A `C¹` function on an open set is differentiable at each of its
points (the form of differentiability every pointwise identity below
consumes). -/
lemma differentiableAt_of_contDiffOn {O : Set (EN m)} (hO : IsOpen O)
    {f : EN m → ℝ} (hf : ContDiffOn ℝ 1 f O) {x : EN m} (hx : x ∈ O) :
    DifferentiableAt ℝ f x :=
  (hf.contDiffAt (hO.mem_nhds hx)).differentiableAt one_ne_zero

/-- Vector-field version of `differentiableAt_of_contDiffOn`. -/
lemma differentiableAt_of_contDiffOn' {O : Set (EN m)} (hO : IsOpen O)
    {F : EN m → EN m} (hF : ContDiffOn ℝ 1 F O) {x : EN m} (hx : x ∈ O) :
    DifferentiableAt ℝ F x :=
  (hF.contDiffAt (hO.mem_nhds hx)).differentiableAt one_ne_zero

/-- The divergence of a `C¹` vector field is continuous on the open set
where the field is `C¹` (each summand `⟪DF·eᵢ, eᵢ⟫` is continuous
because `DF` is). -/
lemma continuousOn_div {O : Set (EN m)} (hO : IsOpen O) {F : EN m → EN m}
    (hF : ContDiffOn ℝ 1 F O) : ContinuousOn (div F) O := by
  have hDF : ContinuousOn (fderiv ℝ F) O :=
    hF.continuousOn_fderiv_of_isOpen hO le_rfl
  refine continuousOn_finset_sum _ fun i _ => ?_
  exact (hDF.clm_apply continuousOn_const).inner continuousOn_const

/-- **Product rule for the divergence**: at a point where `u` and `F`
are differentiable, `div (u • F) = ⟪∇u, F⟫ + u · div F`.  The gradient
term appears via Parseval: `Σᵢ (Du·eᵢ)⟪F, eᵢ⟫ = ⟪∇u, F⟫`. -/
theorem div_smul_eq {u : EN m → ℝ} {F : EN m → EN m} {x : EN m}
    (hu : DifferentiableAt ℝ u x) (hF : DifferentiableAt ℝ F x) :
    div (fun y => u y • F y) x = ⟪gradient u x, F x⟫ + u x * div F x := by
  set b := stdOrthonormalBasis ℝ (EN m) with hb
  have hfd : ∀ w : EN m, fderiv ℝ (fun y => u y • F y) x w
      = fderiv ℝ u x w • F x + u x • fderiv ℝ F x w := by
    intro w
    rw [fderiv_fun_smul hu hF]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [add_comm]
  calc div (fun y => u y • F y) x
      = ∑ i, ⟪fderiv ℝ (fun y => u y • F y) x (b i), b i⟫ := rfl
    _ = ∑ i, (fderiv ℝ u x (b i) * ⟪F x, b i⟫
          + u x * ⟪fderiv ℝ F x (b i), b i⟫) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hfd (b i), inner_add_left, real_inner_smul_left, real_inner_smul_left]
    _ = (∑ i, fderiv ℝ u x (b i) * ⟪F x, b i⟫)
          + u x * ∑ i, ⟪fderiv ℝ F x (b i), b i⟫ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ⟪gradient u x, F x⟫ + u x * div F x := by
        congr 1
        calc (∑ i, fderiv ℝ u x (b i) * ⟪F x, b i⟫)
            = ∑ i, ⟪gradient u x, b i⟫ * ⟪b i, F x⟫ := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [inner_gradient_apply, real_inner_comm (F x) (b i)]
          _ = ⟪gradient u x, F x⟫ := b.sum_inner_mul_inner _ _

/-! ### Integrability on a bounded region -/

/-- **The integrability workhorse**: on a bounded `Ω` with `Ω̄ ⊆ O`,
every function continuous on `O` is integrable on `Ω` (it is bounded on
the compact closure and `Ω` has finite volume).  This is what lets the
identities below split their integrals term by term. -/
lemma integrableOn_of_continuousOn (hb : Bornology.IsBounded Ω)
    {O : Set (EN m)} (hΩO : closure Ω ⊆ O) {f : EN m → ℝ}
    (hf : ContinuousOn f O) : IntegrableOn f Ω volume := by
  have hcl : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hint : IntegrableOn f (closure Ω) volume :=
    (hf.mono hΩO).integrableOn_compact hcl
  exact hint.mono_set subset_closure

/-! ### The gradient form of the theorem -/

variable {ν : EN m → EN m}

/-- **Divergence theorem, gradient form**: `∫_Ω ⟪∇u, w⟫ = ∫_{∂Ω} u ⟪ν, w⟫`.
The scalar theorem with the directional derivative rewritten through the
gradient — the form used when `∇u` is the object of interest (taking
`w = eᵢ` gives `∫_Ω ∂ᵢu = ∫_{∂Ω} u νᵢ`). -/
theorem integral_gradient_inner (hm : 0 < m) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {O : Set (EN m)}
    (hO : IsOpen O) (hΩO : closure Ω ⊆ O) {u : EN m → ℝ}
    (hu : ContDiffOn ℝ 1 u O) (hν : IsOutwardNormal Ω ν) (w : EN m) :
    ∫ x in Ω, ⟪gradient u x, w⟫
      = ∫ x in frontier Ω, u x * ⟪ν x, w⟫ ∂μHE[m] := by
  rw [← divergence_theorem hm hΩ hb hC1 hO hΩO hu hν w]
  exact setIntegral_congr_fun hΩ.measurableSet fun x _ => inner_gradient_apply u x w

/-! ### Integration by parts -/

/-- **Integration by parts** — the identity behind every weak
formulation and energy estimate in PDE theory:

    ∫_Ω (Du·w) v  =  ∫_{∂Ω} u v ⟪ν, w⟫  −  ∫_Ω u (Dv·w) .

Taking `w = eᵢ` gives the component form
`∫_Ω (∂ᵢu) v = ∫_{∂Ω} u v νᵢ − ∫_Ω u (∂ᵢv)`.  Proof: the divergence
theorem applied to the product `u·v`, split by the pointwise product
rule; both pieces are integrable because they are continuous on `O` and
`Ω` is bounded. -/
theorem integration_by_parts (hm : 0 < m) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {O : Set (EN m)}
    (hO : IsOpen O) (hΩO : closure Ω ⊆ O) {u v : EN m → ℝ}
    (hu : ContDiffOn ℝ 1 u O) (hv : ContDiffOn ℝ 1 v O)
    (hν : IsOutwardNormal Ω ν) (w : EN m) :
    ∫ x in Ω, fderiv ℝ u x w * v x
      = (∫ x in frontier Ω, u x * v x * ⟪ν x, w⟫ ∂μHE[m])
        - ∫ x in Ω, u x * fderiv ℝ v x w := by
  have hΩsub : Ω ⊆ O := subset_closure.trans hΩO
  -- the divergence theorem for the product u·v
  have hDT : ∫ x in Ω, fderiv ℝ (fun y => u y * v y) x w
      = ∫ x in frontier Ω, u x * v x * ⟪ν x, w⟫ ∂μHE[m] :=
    divergence_theorem hm hΩ hb hC1 hO hΩO (hu.mul hv) hν w
  -- pointwise product rule on Ω
  have hpt : ∀ x ∈ Ω, fderiv ℝ (fun y => u y * v y) x w
      = fderiv ℝ u x w * v x + u x * fderiv ℝ v x w := by
    intro x hx
    rw [fderiv_fun_mul (differentiableAt_of_contDiffOn hO hu (hΩsub hx))
      (differentiableAt_of_contDiffOn hO hv (hΩsub hx))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  -- integrability of the two pieces
  have hDucont : ContinuousOn (fun x => fderiv ℝ u x w) O :=
    (hu.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
  have hDvcont : ContinuousOn (fun x => fderiv ℝ v x w) O :=
    (hv.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
  have hint1 : IntegrableOn (fun x => fderiv ℝ u x w * v x) Ω volume :=
    integrableOn_of_continuousOn hb hΩO (hDucont.mul hv.continuousOn)
  have hint2 : IntegrableOn (fun x => u x * fderiv ℝ v x w) Ω volume :=
    integrableOn_of_continuousOn hb hΩO (hu.continuousOn.mul hDvcont)
  -- split and rearrange
  have hsplit : ∫ x in Ω, fderiv ℝ (fun y => u y * v y) x w
      = (∫ x in Ω, fderiv ℝ u x w * v x) + ∫ x in Ω, u x * fderiv ℝ v x w := by
    rw [← integral_add hint1 hint2]
    exact setIntegral_congr_fun hΩ.measurableSet hpt
  linarith [hDT, hsplit]

/-! ### The Laplacian and Green's identities -/

/-- The Laplacian `Δu = div (∇u)` — for `C²` functions this is the trace
of the Hessian, i.e. the classical `Σᵢ ∂²u/∂xᵢ²`. -/
def laplacian (u : EN m → ℝ) (x : EN m) : ℝ :=
  div (fun y => gradient u y) x

/-- The gradient field of a `C²` function is a `C¹` vector field (the
gradient is the Riesz transport of the — `C¹` — Fréchet derivative). -/
lemma contDiffOn_gradient {O : Set (EN m)} (hO : IsOpen O) {u : EN m → ℝ}
    (hu : ContDiffOn ℝ 2 u O) :
    ContDiffOn ℝ 1 (fun y => gradient u y) O := by
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ u) O :=
    hu.fderiv_of_isOpen hO (by norm_num)
  exact ((InnerProductSpace.toDual ℝ (EN m)).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    hfd :)

/-- **Gauss' theorem for the Laplacian**: `∫_Ω Δu = ∫_{∂Ω} ⟪∇u, ν⟫` —
the total Laplacian equals the outward flux of the gradient.  (So a
harmonic function has zero net gradient flux through the boundary.) -/
theorem integral_laplacian_eq_flux (hm : 0 < m) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {O : Set (EN m)}
    (hO : IsOpen O) (hΩO : closure Ω ⊆ O) {u : EN m → ℝ}
    (hu : ContDiffOn ℝ 2 u O) (hν : IsOutwardNormal Ω ν) :
    ∫ x in Ω, laplacian u x
      = ∫ x in frontier Ω, ⟪gradient u x, ν x⟫ ∂μHE[m] :=
  divergence_theorem_vector_field hm hΩ hb hC1 hO hΩO
    (contDiffOn_gradient hO hu) hν

/-- **Green's first identity** — the energy-estimate identity:

    ∫_Ω (u Δv + ⟪∇u, ∇v⟫)  =  ∫_{∂Ω} u ⟪∇v, ν⟫ .

Proof: the flux form applied to the field `u·∇v`, whose divergence is
`⟪∇u, ∇v⟫ + u Δv` by the product rule `div_smul_eq`. -/
theorem green_first_identity (hm : 0 < m) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {O : Set (EN m)}
    (hO : IsOpen O) (hΩO : closure Ω ⊆ O) {u v : EN m → ℝ}
    (hu : ContDiffOn ℝ 1 u O) (hv : ContDiffOn ℝ 2 v O)
    (hν : IsOutwardNormal Ω ν) :
    ∫ x in Ω, (u x * laplacian v x + ⟪gradient u x, gradient v x⟫)
      = ∫ x in frontier Ω, u x * ⟪gradient v x, ν x⟫ ∂μHE[m] := by
  have hΩsub : Ω ⊆ O := subset_closure.trans hΩO
  have hgrad : ContDiffOn ℝ 1 (fun y => gradient v y) O :=
    contDiffOn_gradient hO hv
  -- the flux form for F = u • ∇v
  have hflux : ∫ x in Ω, div (fun y => u y • gradient v y) x
      = ∫ x in frontier Ω, ⟪u x • gradient v x, ν x⟫ ∂μHE[m] :=
    divergence_theorem_vector_field hm hΩ hb hC1 hO hΩO (hu.smul hgrad) hν
  -- LHS: the pointwise product rule
  have hL : ∫ x in Ω, div (fun y => u y • gradient v y) x
      = ∫ x in Ω, (u x * laplacian v x + ⟪gradient u x, gradient v x⟫) := by
    refine setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
    rw [div_smul_eq (differentiableAt_of_contDiffOn hO hu (hΩsub hx))
      (differentiableAt_of_contDiffOn' hO hgrad (hΩsub hx))]
    rw [laplacian]
    ring
  -- RHS: pull the scalar out of the inner product
  have hR : ∫ x in frontier Ω, ⟪u x • gradient v x, ν x⟫ ∂μHE[m]
      = ∫ x in frontier Ω, u x * ⟪gradient v x, ν x⟫ ∂μHE[m] :=
    setIntegral_congr_fun isClosed_frontier.measurableSet fun x _ =>
      real_inner_smul_left _ _ _
  rw [← hL, hflux, hR]

/-- **Green's second identity** — the symmetry identity behind
representation formulas and adjointness of the Laplacian:

    ∫_Ω (u Δv − v Δu)  =  ∫_{∂Ω} u ⟪∇v, ν⟫  −  ∫_{∂Ω} v ⟪∇u, ν⟫ .

Proof: subtract the two first identities; the Dirichlet terms
`⟪∇u, ∇v⟫` cancel by symmetry of the inner product. -/
theorem green_second_identity (hm : 0 < m) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {O : Set (EN m)}
    (hO : IsOpen O) (hΩO : closure Ω ⊆ O) {u v : EN m → ℝ}
    (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    (hν : IsOutwardNormal Ω ν) :
    ∫ x in Ω, (u x * laplacian v x - v x * laplacian u x)
      = (∫ x in frontier Ω, u x * ⟪gradient v x, ν x⟫ ∂μHE[m])
        - ∫ x in frontier Ω, v x * ⟪gradient u x, ν x⟫ ∂μHE[m] := by
  have hΩsub : Ω ⊆ O := subset_closure.trans hΩO
  have hu1 : ContDiffOn ℝ 1 u O := hu.of_le (by norm_num)
  have hv1 : ContDiffOn ℝ 1 v O := hv.of_le (by norm_num)
  have hG1 := green_first_identity hm hΩ hb hC1 hO hΩO hu1 hv hν
  have hG2 := green_first_identity hm hΩ hb hC1 hO hΩO hv1 hu hν
  -- integrability of both Green-I integrands, to split the difference
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

/-!
## HOW TO USE — recipe

To apply the divergence theorem to a concrete region `Ω ⊆ ℝⁿ`
(`n = m + 1 ≥ 2`, so `hm : 0 < m`):

1. **Set up the region.**  Present `Ω : Set (EN m)` with
   * `hΩ : IsOpen Ω`, `hb : Bornology.IsBounded Ω`;
   * `hC1 : HasC1Boundary Ω` — for each boundary point, exhibit a
     `CylinderChart`: a rigid motion `T`, a `C¹` function
     `g : EM m → ℝ`, and a cylinder in which `Ω` is exactly the strict
     subgraph of `g` (fields `mem_frontier`, `mem_inside`,
     `mem_outside`).
   * A normal field `ν` with `hν : IsOutwardNormal Ω ν` — either your
     favorite explicit formula (verify it with
     `IsOutwardNormalAt.eq_chart_normal`, or directly from the
     characterization), or the abstract one from
     `exists_isOutwardNormal hΩ hC1`.

2. **Set up the data.**  Functions live on an open neighborhood
   `O ⊇ Ω̄` (take `O = univ` for globally defined ones):
   `hu : ContDiffOn ℝ 1 u O` (or `ℝ 2` for the Laplacian identities).

3. **Pick the identity.**
   * directional:  `divergence_theorem hm hΩ hb hC1 hO hΩO hu hν w`
     gives `∫_Ω Du·w = ∫_{∂Ω} u ⟪ν, w⟫`;
   * gradient:     `integral_gradient_inner` gives `∫_Ω ⟪∇u, w⟫ = …`;
   * flux:         `divergence_theorem_vector_field` gives
     `∫_Ω div F = ∫_{∂Ω} ⟪F, ν⟫`;
   * by parts:     `integration_by_parts` gives
     `∫_Ω (Du·w) v = ∫_{∂Ω} u v ⟪ν, w⟫ − ∫_Ω u (Dv·w)`;
   * Laplacian:    `integral_laplacian_eq_flux`, `green_first_identity`,
     `green_second_identity`.

4. **Evaluate the boundary integral.**  `surface_integral_chart` (for
   chart-supported integrands) or `integral_graph` (for a graph patch)
   turn `∫_{∂Ω} … dμHE[m]` into an ordinary Lebesgue integral
   `∫_V F(z, g z) · √(1+‖∇g‖²) dz` over the base — from there it is
   classical 1-lower-dimensional calculus.

Coordinates: `EN m = WithLp 2 (EM m × ℝ)` is ℝⁿ with the last
coordinate split off; `horiz`/`vert` project, `WithLp.toLp 2 (z, t)`
assembles.  Directional derivatives `fderiv ℝ u x w` with
`w = WithLp.toLp 2 (eᵢ, 0)` or `w = WithLp.toLp 2 (0, 1)` are the
partial derivatives `∂ᵢu` and `∂ₙu`.
-/

end

end GeneralizedDivergenceStandalone
