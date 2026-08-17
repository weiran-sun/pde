/-
# GeneralizedGraph — the complete formalization in a single file

The area formula for a C¹ graph of `f : ℝᵐ → ℝ` in `ℝᵐ⁺¹`
(an `(n−1)`-dimensional graph in `n` dimensions, `m = n − 1`):

    μHE[m] (Γ_f) = ∫_U √(1 + ‖∇f‖²),

together with surface integration of an arbitrary field:

    ∫_{Γ_f} g dμHE[m] = ∫_U g(z, f z) · √(1 + ‖∇f‖²) dz.

This file is the concatenation of the seven `Build/` modules, in one
namespace `GeneralizedGraphFull`, with zero `sorry`s.  See `Build/` for
the same content split into modules, and `Outline/` for the
sorry-filled skeleton.

Flagship results (search for them below):
* `affine_area`                 — exact area of a tilted hyperplane patch;
* `local_area_estimate`         — the `(1±ε)ᵐ` local sandwich;
* `dyadic_decomposition`        — open set = disjoint dyadic cubes;
* `cube_area`                   — area formula over one cube;
* `area_formula`                — THE main theorem (m ≥ 1);
* `area_formula_of_isometry`    — transported to any isometric copy;
* `area_flat_graph`, `area_affine_graph` — ready-to-use computations;
* `area_formula_measurable`     — area formula for any measurable base set;
* `euclideanHausdorff_graph_eq_map` — the pushforward (surface-measure) identity;
* `surface_lintegral`           — SURFACE INTEGRATION of an arbitrary field.
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

noncomputable section

open MeasureTheory Measure Module Matrix Set Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal

namespace GeneralizedGraphFull

/- ======================= from Build/Setup.lean ======================= -/

/-
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

/- ======================= from Build/Affine.lean ======================= -/

/-
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

/- ======================= from Build/Local.lean ======================= -/

/-
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

/- ======================= from Build/Cube.lean ======================= -/

/-
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
  rw [measure_sdiff interior_subset measurableSet_interior.nullMeasurableSet
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
      rw [Set.sdiff_eq_empty.mpr interior_subset]
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
    · rw [Set.sdiff_eq_empty.mpr ?_]
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
            (convex_closedCube _ _) h₁ Set.sdiff_subset
            (volume_frontier_closedCube _ hh.le),
          graph_null_of_volume_null hU hf (isCompact_closedCube _ hh.le)
            (convex_closedCube _ _) h₂ Set.sdiff_subset
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

/- ======================= from Build/Main.lean ======================= -/

/-
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
      rw [Set.sdiff_eq_empty.mpr interior_subset]
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
    · rw [Set.sdiff_eq_empty.mpr ?_]
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

/- ======================= from Build/Applications.lean ======================= -/

/-
# Applying the area formula — the user-facing API

This file is the part you actually reach for when you want to *compute*
the `m`-dimensional measure of a concrete `(n−1 = m)`-dimensional
surface sitting in `ℝⁿ` (`n = m + 1`).

Contents:
* `area_formula_of_isometry` — the area formula transported along any
  isometry, so it applies to a graph patch that has been rotated,
  translated, or re-embedded into another Euclidean/metric space.  This
  is the workhorse for a surface presented as an isometric image of a
  graph.
* `measure_split_two` — glue two graph patches across a null seam
  (e.g. two coordinate charts of a closed hypersurface meeting along a
  lower-dimensional set).
* Ready-to-use computations: `jac_const` / `area_flat_graph` (a flat
  graph has area equal to the base volume), and `area_affine_graph`
  (a tilted hyperplane patch has area `√(1+‖p‖²)·vol`).

See the `HOW TO USE` note at the bottom for the standard recipe.
-/




variable {m : ℕ}

/-! ## Transport and gluing -/

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The area formula for an isometric copy of a graph.**  If `ι` is an
isometry (e.g. the inclusion of a rotated/translated hyperplane patch,
or the identification `EN m ≃ᵢ EuclideanSpace ℝ (Fin (m+1))`), the
surface `ι '' Γ_f` has the same area integral.  This is what one uses on
a concrete surface presented as an isometric image of a graph. -/
theorem area_formula_of_isometry (hm : 0 < m) {U : Set (EM m)} {f : EM m → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {ι : EN m → X} (hι : Isometry ι) :
    μHE[m] (ι '' graph f U) = ∫⁻ z in U, ENNReal.ofReal (jac f z) := by
  rw [hι.euclideanHausdorffMeasure_image, area_formula hm hU hf]

omit [EMetricSpace X] [BorelSpace X] in
/-- **Gluing two patches across a null seam.**  `μ(A ∪ B ∪ N) = μ A + μ B`
when `A`, `B` are disjoint, `B` is measurable, and `N` is null.  For a
closed hypersurface: two coordinate charts `A`, `B` and their
(lower-dimensional, hence null) overlap `N`. -/
theorem measure_split_two {μ : Measure X} {A B N : Set X}
    (hAB : Disjoint A B) (hB : MeasurableSet B) (hN : μ N = 0) :
    μ (A ∪ B ∪ N) = μ A + μ B := by
  have h1 : μ (A ∪ B ∪ N) = μ (A ∪ B) := by
    apply le_antisymm
    · calc μ (A ∪ B ∪ N) ≤ μ (A ∪ B) + μ N := measure_union_le _ _
        _ = μ (A ∪ B) := by rw [hN, add_zero]
    · exact measure_mono Set.subset_union_left
  rw [h1, measure_union hAB hB]

/-! ## Ready-to-use computations -/

/-- The Jacobian of a constant function is `1` (a flat graph is
isometric to its shadow). -/
@[simp] theorem jac_const (c : ℝ) (z : EM m) : jac (fun _ => c) z = 1 := by
  have h0 : fderiv ℝ (fun _ : EM m => c) z = 0 := fderiv_const_apply c
  rw [jac, h0]
  simp

/-- **A flat graph has area equal to its base volume.**  Sanity check
and the simplest application: for `f ≡ c`, `√(1+‖∇f‖²) = 1`, so the
integral is just `volume U`. -/
theorem area_flat_graph (hm : 0 < m) {U : Set (EM m)} (hU : IsOpen U) (c : ℝ) :
    μHE[m] (graph (fun _ => c) U) = volume U := by
  rw [area_formula hm hU (contDiffOn_const)]
  simp

/-- **The area of a tilted-hyperplane patch.**  For the affine graph
`Φ_aff(z) = (z, ⟪p, z⟫ + c)` over a base `A`, the area is exactly
`√(1+‖p‖²)·vol(A)`.  (This holds for *every* set `A` — no openness or
measurability needed — because it is `affine_area` directly, not the
general C¹ theorem.)  Handy for computing areas of simplices,
parallelepipeds, and other flat pieces. -/
theorem area_affine_graph (p : EM m) (c : ℝ) (A : Set (EM m)) :
    μHE[m] (affGraphMap p c '' A)
      = ENNReal.ofReal (Real.sqrt (1 + ‖p‖ ^ 2)) * volume A :=
  affine_area p c A

/-- The area of a tilted-hyperplane patch over a closed `m`-cube of side
`s`: `√(1+‖p‖²)·sᵐ`.  A fully worked closed-form number, combining
`area_affine_graph` with `volume_closedCube`. -/
theorem area_affine_graph_cube (p : EM m) (c : ℝ) (z₀ : EM m) {s : ℝ}
    (hs : 0 ≤ s) :
    μHE[m] (affGraphMap p c '' closedCube z₀ s)
      = ENNReal.ofReal (Real.sqrt (1 + ‖p‖ ^ 2)) * ENNReal.ofReal (s ^ m) := by
  rw [area_affine_graph, volume_closedCube z₀ hs]

/-!
## HOW TO USE — recipe

To compute the `m`-dimensional area of a surface `S ⊆ ℝᵐ⁺¹`:

1. **Present `S` as (an isometric image of) a graph.**  Find an open
   `U ⊆ ℝᵐ`, a function `f : ℝᵐ → ℝ` with `ContDiffOn ℝ 1 f U`, and —
   if `S` is not already `Γ_f` in the standard `EN m` coordinates — an
   isometry `ι` with `S = ι '' graph f U`.

2. **Apply the theorem.**
   * `S = graph f U` in standard coordinates → `area_formula hm hU hf`.
   * `S = ι '' graph f U` → `area_formula_of_isometry hm hU hf hι`.
   Either yields `μHE[m] S = ∫⁻ z in U, ENNReal.ofReal (jac f z)`, where
   `jac f z = √(1 + ‖∇f(z)‖²)`.

3. **Evaluate the integral.**  `jac` is `Real.sqrt (1 + ‖fderiv ℝ f z‖^2)`;
   compute `fderiv ℝ f` and integrate.  For a flat piece use
   `area_flat_graph`; for a hyperplane piece use `area_affine_graph`
   (exact, no integral).

4. **Closed surfaces**: cover `S` by finitely many graph charts meeting
   along lower-dimensional (null) sets and add up with
   `measure_split_two`.

Here `m = n − 1`: the surface is `m`-dimensional and the ambient space
`EN m = ℝᵐ⁺¹` is `n`-dimensional.  The measure `μHE[m]` is Mathlib's
Euclidean-normalized Hausdorff measure, i.e. genuine `m`-dimensional
area/volume.
-/

/-- Restatement making the ambient dimension `n = m + 1` explicit: the
graph of `f : ℝⁿ⁻¹ → ℝ` is an `(n−1)`-dimensional surface in `ℝⁿ`, and
its `(n−1)`-area is `∫ √(1+‖∇f‖²)`.  Definitionally the same as
`area_formula`; provided for readability when thinking in terms of the
ambient dimension `n`. -/
theorem hypersurface_area {n : ℕ} (hn : 0 < n) {U : Set (EM n)} {f : EM n → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    μHE[n] (graph f U) = ∫⁻ z in U, ENNReal.ofReal (jac f z) :=
  area_formula hn hU hf

/- ======================= from Build/SurfaceIntegral.lean ======================= -/

/-
# Surface integration over a C¹ graph

**This is a genuinely separate result from the area formula.** The area
formula (`Main.area_formula`) computes the *measure of the graph* — i.e.
the surface integral of the constant function `1`. This file upgrades it
to the **surface integral of an arbitrary (measurable) field** `g`:

    ∫_{Γ_f} g dμHE[m]  =  ∫_U g(z, f z) · √(1 + ‖∇f‖²) dz.

The upgrade is a change-of-variables / pushforward statement. The route
(a standard measure-uniqueness argument) is:

1. `graphMap f` restricted to the base subtype `↥U` is a **measurable
   embedding** (a continuous injection on a Polish space).
2. The pullback (`comap`) of `μHE[m]` and the weighted base measure
   `√(1+‖∇f‖²)·volume` agree on the **open** sets — which is exactly
   `area_formula` — hence agree everywhere, by π-system uniqueness
   (`ext_of_generateFrom_of_iUnion`). This gives the **area formula for
   every measurable base set**.
3. Transporting the resulting measure identity through the embedding
   turns it into the surface-integral formula for every measurable `g`.

Everything inherits the hypothesis `0 < m` from `area_formula`.
-/




variable {m : ℕ} {U : Set (EM m)} {f : EM m → ℝ}

/-! ### The graph embedding of the base subtype -/

/-- The graph map viewed as a map out of the base subtype `↥U`. On `↥U`
it is a continuous injection, hence a measurable embedding. -/
def baseEmb (f : EM m → ℝ) (U : Set (EM m)) : ↥U → EN m := fun z => graphMap f z.1

/-- The graph over a set is the graph map's image (definitional, but
`graph` does not rewrite, so we record it). -/
lemma graph_eq_image (s : Set (EM m)) : graph f s = graphMap f '' s := rfl

/-- The image of a subtype set under `baseEmb` is the graph over its
projection. -/
lemma baseEmb_image (T : Set ↥U) :
    baseEmb f U '' T = graphMap f '' (Subtype.val '' T) :=
  (Set.image_image (graphMap f) Subtype.val T).symm

lemma baseEmb_continuous (hf : ContDiffOn ℝ 1 f U) :
    Continuous (baseEmb f U) :=
  (continuousOn_graphMap hf.continuousOn).comp_continuous continuous_subtype_val
    (fun z => z.2)

lemma baseEmb_injective : Function.Injective (baseEmb f U) := fun _a _b h =>
  Subtype.ext (graphMap_injective h)

lemma range_baseEmb : Set.range (baseEmb f U) = graph f U := by
  rw [← Set.image_univ, baseEmb_image, Set.image_univ, Subtype.range_coe, graph_eq_image]

/-- **`baseEmb` is a measurable embedding.** A continuous injection on a
Polish space (an open subset of Euclidean space) into a Borel space. -/
lemma measurableEmbedding_baseEmb (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    MeasurableEmbedding (baseEmb f U) := by
  haveI : PolishSpace (EM m) := inferInstance
  haveI : PolishSpace U := hU.polishSpace
  exact (baseEmb_continuous hf).measurableEmbedding baseEmb_injective

/-! ### The base measures on `↥U` -/

/-- `volume` on the base transported to the subtype `↥U`. -/
def baseVol (U : Set (EM m)) : Measure ↥U := Measure.comap Subtype.val volume

/-- The weighted base measure `√(1+‖∇f‖²) · volume` on `↥U`, whose
pushforward along `baseEmb` will be shown to equal the surface measure. -/
def baseArea (f : EM m → ℝ) (U : Set (EM m)) : Measure ↥U :=
  (baseVol U).withDensity (fun z => ENNReal.ofReal (jac f z.1))

/-- Converting a subtype integral back to a set integral on the base
(any integrand — measurable-embedding `lintegral_map` needs no
measurability of the integrand). -/
private lemma lintegral_baseVol (hU : IsOpen U) (H : EM m → ℝ≥0∞) :
    ∫⁻ a, H a.1 ∂(baseVol U) = ∫⁻ x in U, H x ∂volume := by
  rw [baseVol, ← (MeasurableEmbedding.subtype_coe hU.measurableSet).lintegral_map H,
    map_comap_subtype_coe hU.measurableSet]

/-- Restricted version of `lintegral_baseVol`. -/
private lemma setLIntegral_baseVol (hU : IsOpen U) {V : Set (EM m)}
    (hV : MeasurableSet V) (H : EM m → ℝ≥0∞) :
    ∫⁻ a in (Subtype.val ⁻¹' V : Set ↥U), H a.1 ∂(baseVol U)
      = ∫⁻ x in V ∩ U, H x ∂volume := by
  have hVU : MeasurableSet (Subtype.val ⁻¹' V : Set ↥U) :=
    hV.preimage measurable_subtype_coe
  rw [← lintegral_indicator hVU]
  have hpt : (fun a : ↥U => (Subtype.val ⁻¹' V).indicator (fun a => H a.1) a)
      = fun a : ↥U => (V.indicator H) a.1 := by
    funext a
    by_cases h : a.1 ∈ V <;> simp [Set.mem_preimage, h]
  rw [hpt, lintegral_baseVol hU (V.indicator H), ← lintegral_indicator hU.measurableSet,
    Set.indicator_indicator, Set.inter_comm U V,
    lintegral_indicator (hV.inter hU.measurableSet)]

/-! ### The area formula for measurable base sets (the pushforward core) -/

/-- **The pullback of `μHE[m]` along the graph embedding equals the
weighted base measure.** Proven by π-system uniqueness: both measures
agree on open sets by `area_formula`, and the base is covered by open
sets of finite weighted measure (where `jac` is bounded). This is the
technical heart — from it, both the measurable-set area formula and the
surface integral follow. -/
theorem comap_euclideanHausdorff_eq_baseArea (hm : 0 < m) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) :
    Measure.comap (baseEmb f U) μHE[m] = baseArea f U := by
  have hemb := measurableEmbedding_baseEmb hU hf
  -- Agreement on the open sets of `↥U`.
  have key : ∀ s : Set ↥U, IsOpen s →
      Measure.comap (baseEmb f U) μHE[m] s = baseArea f U s := by
    intro s hs
    obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hs
    -- `baseEmb '' (val⁻¹' V) = graph f (V ∩ U)`.
    have himg : baseEmb f U '' (Subtype.val ⁻¹' V) = graph f (V ∩ U) := by
      rw [baseEmb_image, Set.image_preimage_eq_inter_range, Subtype.range_coe, graph_eq_image]
    rw [hemb.comap_apply, himg,
      area_formula hm (hV.inter hU) (hf.mono Set.inter_subset_right),
      baseArea, withDensity_apply _ ((hV.preimage continuous_subtype_val).measurableSet),
      setLIntegral_baseVol hU hV.measurableSet (fun x => ENNReal.ofReal (jac f x))]
  -- Covering `↥U` by opens of finite weighted measure (where `jac < n`).
  set Wn : ℕ → Set (EM m) := fun n =>
    (U ∩ jac f ⁻¹' Set.Iio (n : ℝ)) ∩ Metric.ball 0 (n : ℝ) with hWn
  have hWn_open : ∀ n, IsOpen (Wn n) := fun n =>
    ((continuousOn_jac hU hf).isOpen_inter_preimage hU isOpen_Iio).inter Metric.isOpen_ball
  set B : ℕ → Set ↥U := fun n => Subtype.val ⁻¹' Wn n with hB
  have hB_open : ∀ n, IsOpen (B n) := fun n => (hWn_open n).preimage continuous_subtype_val
  have hB_cover : ⋃ n, B n = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro a
    obtain ⟨n, hn⟩ := exists_nat_gt (max (jac f a.1) ‖a.1‖)
    refine Set.mem_iUnion.mpr ⟨n, ⟨a.2, (le_max_left _ _).trans_lt hn⟩, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact (le_max_right _ _).trans_lt hn
  have hB_fin : ∀ n, baseArea f U (B n) ≠ ⊤ := by
    intro n
    rw [hB, baseArea, withDensity_apply _ ((hWn_open n).measurableSet.preimage
        measurable_subtype_coe),
      setLIntegral_baseVol hU (hWn_open n).measurableSet
        (fun x => ENNReal.ofReal (jac f x))]
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (n : ℝ)
        * volume (Metric.ball (0 : EM m) (n : ℝ)))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ((Metric.isBounded_ball : Bornology.IsBounded
          (Metric.ball (0 : EM m) (n : ℝ))).measure_lt_top (μ := volume)).ne) ?_
    calc ∫⁻ x in Wn n ∩ U, ENNReal.ofReal (jac f x) ∂volume
        ≤ ∫⁻ _x in Wn n ∩ U, ENNReal.ofReal (n : ℝ) ∂volume := by
          refine setLIntegral_mono_ae aemeasurable_const
            (Filter.Eventually.of_forall fun x hx => ?_)
          exact ENNReal.ofReal_le_ofReal (le_of_lt hx.1.1.2)
      _ = ENNReal.ofReal (n : ℝ) * volume (Wn n ∩ U) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (n : ℝ) * volume (Metric.ball (0 : EM m) (n : ℝ)) := by
          gcongr
          exact Set.inter_subset_left.trans Set.inter_subset_right
  -- π-system uniqueness. Finiteness must be stated for the LHS measure
  -- (`comap`), obtained from `baseArea` via `key`.
  have hμB : ∀ n, Measure.comap (baseEmb f U) μHE[m] (B n) ≠ ⊤ := by
    intro n; rw [key (B n) (hB_open n)]; exact hB_fin n
  exact ext_of_generateFrom_of_iUnion {s : Set ↥U | IsOpen s} B
    BorelSpace.measurable_eq isPiSystem_isOpen hB_cover hB_open hμB key

/-- **The area formula for an arbitrary measurable base set.**
`μHE[m](Γ_f|_S) = ∫_S √(1+‖∇f‖²)` for every measurable `S ⊆ U` — the
`area_formula` extended off open sets. -/
theorem area_formula_measurable (hm : 0 < m) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {S : Set (EM m)} (hS : MeasurableSet S) (hSU : S ⊆ U) :
    μHE[m] (graph f S) = ∫⁻ z in S, ENNReal.ofReal (jac f z) := by
  have hemb := measurableEmbedding_baseEmb hU hf
  have himg : baseEmb f U '' (Subtype.val ⁻¹' S) = graph f S := by
    rw [baseEmb_image, Set.image_preimage_eq_inter_range, Subtype.range_coe,
      Set.inter_eq_left.mpr hSU, graph_eq_image]
  rw [← himg, ← hemb.comap_apply, comap_euclideanHausdorff_eq_baseArea hm hU hf,
    baseArea, withDensity_apply _ (hS.preimage measurable_subtype_coe),
    setLIntegral_baseVol hU hS (fun x => ENNReal.ofReal (jac f x)),
    Set.inter_eq_left.mpr hSU]

/-! ### Surface integration -/

/-- **The pushforward (surface-measure) identity.** The surface measure
`μHE[m]` restricted to the graph is the pushforward, along the graph
map, of `√(1+‖∇f‖²) · volume` on the base. -/
theorem euclideanHausdorff_graph_eq_map (hm : 0 < m) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) :
    μHE[m].restrict (graph f U) = Measure.map (baseEmb f U) (baseArea f U) := by
  have hemb := measurableEmbedding_baseEmb hU hf
  rw [← comap_euclideanHausdorff_eq_baseArea hm hU hf, hemb.map_comap, range_baseEmb]

/-- **Surface integration.** For every measurable `g : ℝᵐ⁺¹ → [0,∞]`,

    ∫_{Γ_f} g dμHE[m]  =  ∫_U g(z, f z) · √(1 + ‖∇f‖²) dz.

The `g ≡ 1` case is `area_formula`; this is the full change-of-variables
statement. -/
theorem surface_lintegral (hm : 0 < m) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {g : EN m → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in graph f U, g x ∂μHE[m]
      = ∫⁻ z in U, g (graphMap f z) * ENNReal.ofReal (jac f z) ∂volume := by
  have hemb := measurableEmbedding_baseEmb hU hf
  have hw_cont : Continuous (fun z : ↥U => jac f z.1) :=
    (continuousOn_jac hU hf).comp_continuous continuous_subtype_val (fun z => z.2)
  have hw_meas : Measurable (fun z : ↥U => ENNReal.ofReal (jac f z.1)) :=
    (ENNReal.continuous_ofReal.comp hw_cont).measurable
  rw [euclideanHausdorff_graph_eq_map hm hU hf, hemb.lintegral_map, baseArea,
    lintegral_withDensity_eq_lintegral_mul (baseVol U) hw_meas
      (g := fun a => g (baseEmb f U a)) (hg.comp hemb.measurable),
    ← lintegral_baseVol hU (fun x => g (graphMap f x) * ENNReal.ofReal (jac f x))]
  refine lintegral_congr fun a => ?_
  simp only [Pi.mul_apply]
  exact mul_comm _ _

end GeneralizedGraphFull
