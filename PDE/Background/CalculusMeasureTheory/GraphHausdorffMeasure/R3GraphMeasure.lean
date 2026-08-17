/-
# THE AREA FORMULA FOR A C1 GRAPH -- the complete development in one file

EVERY THEOREM IS FULLY PROVEN -- no sorries, no axioms beyond
Mathlib.  In particular this file contains complete proofs of:
* the greedy dyadic decomposition of open sets (paper Lem 3.3);
* the Riemann-grid area formula over a square (paper Thm 8.2);
* the isodiametric inequality via Steiner symmetrization
  (paper Thm 4.1);
* the identification mu_H[2] = (4/pi) volume on the plane
  (paper Thm 5.1), resolving Mathlib's `proof_wanted`
  normalization constant in dimension 2.

Headline results:
* `area_formula` : the paper's Theorem 1.1,
    mu_HE[2] (Graph f U) = integral over U of sqrt(1 + |Df|^2);
* `sphere_area_unit` : mu_HE[2] (sphere 0 1) = 4 pi;
* `sphere_area` : mu_HE[2] (sphere x r) = 4 pi r^2;
* `sphere_hausdorffMeasure_unit` : mu_H[2] (sphere 0 1) = 16.
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Measure Module Matrix Set
open scoped RealInnerProductSpace ENNReal NNReal Real

namespace GraphAreaFull


/-
# The area formula for a C¹ graph — setup (paper §1, §7 preamble)

Ambient spaces, the graph map, the Jacobian factor, and the elementary
inequality (1) of the paper: the graph map never decreases distances.

See the skeleton version (`../GraphArea`) for the full design notes.
-/



/-- The Euclidean plane. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- Euclidean ℝ³, realized as the ℓ²-product of the plane and the line.
Isometric to `EuclideanSpace ℝ (Fin 3)` (see `GraphArea.Sphere.toE3'`),
but the product form keeps the horizontal/vertical split visible. -/
abbrev E3 : Type := WithLp 2 (E2 × ℝ)

/-! ### ℓ²-product norm helpers

Everything in §7 reduces to the Pythagoras identity for the ℓ²-product
norm on `E3`; we record the four forms that get used. -/

/-- Pythagoras for the ℓ²-product: `‖(a, b)‖² = ‖a‖² + b²`. -/
lemma norm_toLp_sq (a : E2) (b : ℝ) :
    ‖(WithLp.toLp 2 (a, b) : E3)‖ ^ 2 = ‖a‖ ^ 2 + b ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [WithLp.fst, WithLp.snd, sq_abs]

/-- The horizontal component is no longer than the vector. -/
lemma norm_fst_le_norm_toLp (a : E2) (b : ℝ) :
    ‖a‖ ≤ ‖(WithLp.toLp 2 (a, b) : E3)‖ := by
  have h := norm_toLp_sq a b
  calc ‖a‖ = Real.sqrt (‖a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖(WithLp.toLp 2 (a, b) : E3)‖ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
    _ = _ := Real.sqrt_sq (norm_nonneg _)

/-- The vertical component is no longer than the vector. -/
lemma abs_snd_le_norm_toLp (a : E2) (b : ℝ) :
    |b| ≤ ‖(WithLp.toLp 2 (a, b) : E3)‖ := by
  have h := norm_toLp_sq a b
  calc |b| = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
    _ ≤ Real.sqrt (‖(WithLp.toLp 2 (a, b) : E3)‖ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖a‖])
    _ = _ := Real.sqrt_sq (norm_nonneg _)

/-- The ℓ²-norm is at most the ℓ¹-norm (used for cheap Lipschitz bounds). -/
lemma norm_toLp_le (a : E2) (b : ℝ) :
    ‖(WithLp.toLp 2 (a, b) : E3)‖ ≤ ‖a‖ + |b| := by
  have h := norm_toLp_sq a b
  calc ‖(WithLp.toLp 2 (a, b) : E3)‖
      = Real.sqrt (‖(WithLp.toLp 2 (a, b) : E3)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((‖a‖ + |b|) ^ 2) := Real.sqrt_le_sqrt
        (by nlinarith [norm_nonneg a, abs_nonneg b, sq_abs b])
    _ = ‖a‖ + |b| := Real.sqrt_sq (by positivity)

variable (f : E2 → ℝ) (U : Set E2)

/-- The graph map `Φ(z) = (z, f z)` (paper §1.1 / §7). -/
def graphMap (z : E2) : E3 := WithLp.toLp 2 (z, f z)

/-- The graph `Γ_f` of `f` over a set `s ⊆ ℝ²` (paper §1.1). -/
def graph (s : Set E2) : Set E3 := graphMap f '' s

/-- The Jacobian factor `J(z) = √(1 + ‖Df z‖²)` (paper §7).
Since `f` is scalar, the operator norm `‖fderiv ℝ f z‖` equals the
Euclidean norm of the gradient, so this is the paper's `√(1 + |∇f|²)`. -/
def jac (z : E2) : ℝ := Real.sqrt (1 + ‖fderiv ℝ f z‖ ^ 2)

variable {f U}

/-- Displacements of the graph map, componentwise. -/
lemma graphMap_sub (z z' : E2) :
    graphMap f z - graphMap f z' = WithLp.toLp 2 (z - z', f z - f z') := by
  rw [graphMap, graphMap, ← WithLp.toLp_sub, Prod.mk_sub_mk]

/-- `J ≥ 1` (paper §7: "Note … J ≥ 1"). -/
lemma one_le_jac (z : E2) : 1 ≤ jac f z := by
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖fderiv ℝ f z‖ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖fderiv ℝ f z‖])
    _ = jac f z := rfl

lemma jac_pos (z : E2) : 0 < jac f z :=
  lt_of_lt_of_le one_pos (one_le_jac z)

/-- `J` is continuous on `U` (paper §7): the derivative of a C¹
function is continuous on the open set `U`, and `t ↦ √(1 + t²)` is
continuous. -/
lemma continuousOn_jac (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    ContinuousOn (jac f) U := by
  have h : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  exact (continuousOn_const.add (h.norm.pow 2)).sqrt

/-- The Pythagoras identity behind everything in §7: with the ℓ²-product
norm on `E3`, `‖Φ z - Φ z'‖² = ‖z - z'‖² + |f z - f z'|²`. -/
lemma norm_graphMap_sub_sq (z z' : E2) :
    ‖graphMap f z - graphMap f z'‖ ^ 2 = ‖z - z'‖ ^ 2 + (f z - f z') ^ 2 := by
  rw [graphMap_sub, norm_toLp_sq]

/-- **Inequality (1) of the paper**: the graph map never decreases
distances. -/
lemma norm_le_norm_graphMap_sub (z z' : E2) :
    ‖z - z'‖ ≤ ‖graphMap f z - graphMap f z'‖ := by
  rw [graphMap_sub]
  exact norm_fst_le_norm_toLp _ _

/-- `Φ` is injective (paper §7, after (1): "in particular Φ is
injective (also clear from the first two coordinates)"). -/
lemma graphMap_injective : Function.Injective (graphMap f) := by
  intro z z' h
  simpa [graphMap] using congrArg (fun w : E3 => (WithLp.ofLp w).1) h

/-- `Φ` is continuous when `f` is; graphs of continuous functions over
compact sets are compact, which is how measurability of the graph
pieces is obtained for free in Lean. -/
lemma continuousOn_graphMap (hf : ContinuousOn f U) :
    ContinuousOn (graphMap f) U := by
  have h1 : ContinuousOn (fun z : E2 => (z, f z)) U := continuousOn_id.prodMk hf
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ).symm.continuous.comp_continuousOn h1

/-
# Affine graphs: the exact area of a tilted plane (paper §6)

`μHE[2](Φ_aff(A)) = √(1 + |p|²) · m(A)` for the affine graph map
`Φ_aff(z) = (z, ⟨p, z⟩ + c)`.

Proof structure (paper §6): kill `c` by a vertical translation
(isometry), flatten the image plane by orthonormal coordinates
(paper Lem 6.2 = `stdOrthonormalBasis`), scale by `|det|`
(paper Thm 3.7 = `Measure.addHaar_image_linearMap`), and evaluate the
determinant via the 2×2 Gram matrix.
-/




variable (p : E2) (c : ℝ)

/-- The affine graph map `Φ_aff(z) = (z, ⟨p, z⟩ + c)` (paper §6). -/
def affGraphMap (z : E2) : E3 := WithLp.toLp 2 (z, ⟪p, z⟫ + c)

/-- The linear part `L(z) = (z, ⟨p, z⟩)`, whose image is the plane `P`
spanned by `u = (1,0,p₁)`, `v = (0,1,p₂)` (paper §6). -/
def affGraphLin (z : E2) : E3 := WithLp.toLp 2 (z, ⟪p, z⟫)

/-- **Paper §6, Step 3** (the Gram computation, isolated): the Gram
matrix of `u = (1,0,p₁)`, `v = (0,1,p₂)` has determinant `1 + |p|²`. -/
lemma gram_det :
    (Matrix.of ![![1 + p 0 ^ 2, p 0 * p 1], ![p 0 * p 1, 1 + p 1 ^ 2]]).det
      = 1 + ‖p‖ ^ 2 := by
  rw [Matrix.det_fin_two_of, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  ring

/-- The linear part as a bundled linear map. -/
def affGraphLinₗ : E2 →ₗ[ℝ] E3 :=
  (WithLp.linearEquiv 2 ℝ (E2 × ℝ)).symm.toLinearMap.comp
    (LinearMap.prod LinearMap.id (innerSL ℝ p).toLinearMap)

@[simp] lemma affGraphLinₗ_apply (z : E2) : affGraphLinₗ p z = affGraphLin p z := rfl

lemma affGraphLinₗ_injective : Function.Injective (affGraphLinₗ p) := by
  intro z z' h
  simpa [affGraphLinₗ] using congrArg (fun w : E3 => (WithLp.ofLp w).1) h

/-- **Paper Theorem 6.1** (affine area formula), for *every* subset
`A` — Mathlib measures applied to arbitrary sets are outer measures,
so this is faithful to the paper. -/
theorem affine_area (A : Set E2) :
    μHE[2] (affGraphMap p c '' A)
      = ENNReal.ofReal (Real.sqrt (1 + ‖p‖ ^ 2)) * volume A := by
  -- Step 0 (paper: "remove the constant"): vertical translation is an
  -- isometry of `E3`.
  have step0 : μHE[2] (affGraphMap p c '' A) = μHE[2] (affGraphLin p '' A) := by
    have himg : affGraphMap p c '' A
        = (fun w : E3 => w + WithLp.toLp 2 ((0 : E2), c)) '' (affGraphLin p '' A) := by
      rw [Set.image_image]
      apply Set.image_congr
      intro z _
      simp only [affGraphMap, affGraphLin, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero]
    have hiso : Isometry (fun w : E3 => w + WithLp.toLp 2 ((0 : E2), c)) :=
      Isometry.of_dist_eq fun w w' => dist_add_right w w' _
    rw [himg]
    exact hiso.euclideanHausdorffMeasure_image _
  -- The image plane `P = range L` and its dimension.
  set L : E2 →ₗ[ℝ] E3 := affGraphLinₗ p with hLdef
  have hrank : finrank ℝ (LinearMap.range L) = 2 := by
    rw [LinearMap.finrank_range_of_inj (affGraphLinₗ_injective p)]
    exact finrank_euclideanSpace_fin
  -- Orthonormal coordinates on `P` (paper Lemma 6.2).
  set R : LinearMap.range L ≃ₗᵢ[ℝ] E2 :=
    ((stdOrthonormalBasis ℝ (LinearMap.range L)).reindex (finCongr hrank)).repr with hRdef
  -- The flattened linear map `T = R ∘ L : ℝ² → ℝ²`.
  set T : E2 →ₗ[ℝ] E2 := R.toLinearMap.comp L.rangeRestrict with hTdef
  -- Step 1 (flatten): `L '' A` is the image of `T '' A` under the
  -- isometry `val ∘ R.symm`.
  have himg2 : (Subtype.val ∘ R.symm) '' (T '' A) = affGraphLin p '' A := by
    rw [Set.image_image]
    apply Set.image_congr
    intro z _
    show (R.symm (R (L.rangeRestrict z)) : E3) = affGraphLin p z
    rw [LinearIsometryEquiv.symm_apply_apply]
    rfl
  have hiso2 : Isometry (Subtype.val ∘ R.symm : E2 → E3) :=
    isometry_subtype_coe.comp R.symm.isometry
  -- Step 3 (Gram): `(det T)² = 1 + ‖p‖²`.
  have hdet : |LinearMap.det T| = Real.sqrt (1 + ‖p‖ ^ 2) := by
    set b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis with hbdef
    set M := LinearMap.toMatrix b b T with hMdef
    -- The transpose product is the Gram matrix of `T e₁, T e₂`, whose
    -- entries are the inner products `⟪L eᵢ, L eⱼ⟫` since `R` preserves
    -- inner products.
    -- Standard-basis inner products evaluate to coordinates.
    have hip : ∀ (m : Fin 2) (x : E2), ⟪(b m : E2), x⟫ = x m := by
      intro m x
      rw [hbdef, OrthonormalBasis.coe_toBasis]
      exact ((EuclideanSpace.basisFun (Fin 2) ℝ).repr_apply_apply x m).symm
    -- Inner products of real numbers are products (definitionally).
    have hRinner : ∀ s t : ℝ, ⟪s, t⟫ = t * s := fun s t => rfl
    have hentry : ∀ i j, (Mᵀ * M) i j = ⟪affGraphLin p (b i), affGraphLin p (b j)⟫ := by
      intro i j
      have hMcol : ∀ (k l : Fin 2), M k l = T (b l) k := by
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
    have hgram : Mᵀ * M
        = Matrix.of ![![1 + p 0 ^ 2, p 0 * p 1], ![p 0 * p 1, 1 + p 1 ^ 2]] := by
      have hinner : ∀ l m : Fin 2,
          ⟪affGraphLin p (b l), affGraphLin p (b m)⟫
            = (b m : E2) l + p l * p m := by
        intro l m
        have hsplit : ⟪affGraphLin p (b l), affGraphLin p (b m)⟫
            = ⟪(b l : E2), (b m : E2)⟫ + ⟪(⟪p, (b l : E2)⟫ : ℝ), (⟪p, (b m : E2)⟫ : ℝ)⟫ := rfl
        rw [hsplit, hRinner, hip l (b m), ← real_inner_comm p (b l),
          ← real_inner_comm p (b m), hip, hip]
        ring
      -- Coordinates of the standard basis vectors.
      have hb01 : ∀ l m : Fin 2, ((b m : E2) l) = if l = m then (1 : ℝ) else 0 := by
        intro l m
        rw [← hip l (b m), hbdef, OrthonormalBasis.coe_toBasis]
        exact orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal l m
      ext i j
      rw [hentry i j, hinner i j]
      fin_cases i <;> fin_cases j <;> simp [hb01] <;> ring
    have h2 : LinearMap.det T ^ 2 = 1 + ‖p‖ ^ 2 := by
      have hdetc := congrArg Matrix.det hgram
      rw [Matrix.det_mul, Matrix.det_transpose, gram_det] at hdetc
      rw [← LinearMap.det_toMatrix b T, ← hMdef, sq]
      exact hdetc
    rw [← Real.sqrt_sq_eq_abs, h2]
  -- Chain everything (Steps 1–2 of the paper).
  calc μHE[2] (affGraphMap p c '' A)
      = μHE[2] (affGraphLin p '' A) := step0
    _ = μHE[2] ((Subtype.val ∘ R.symm) '' (T '' A)) := by rw [himg2]
    _ = μHE[2] (T '' A) := hiso2.euclideanHausdorffMeasure_image _
    _ = volume (T '' A) := by
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    _ = ENNReal.ofReal |LinearMap.det T| * volume A :=
        addHaar_image_linearMap volume T A
    _ = ENNReal.ofReal (Real.sqrt (1 + ‖p‖ ^ 2)) * volume A := by rw [hdet]

/-
# The local estimate: a C¹ graph is almost affine (paper §7)

Standing local data (paper §7): a convex `Q ⊆ U` (in the paper, a
closed square), a base point `zQ ∈ Q`, and `ε ∈ (0,1)` with
`‖Df z − Df zQ‖ ≤ ε` on `Q` (hypothesis (2)).

The output is the two-sided area estimate Cor 7.3, the engine of §§8–9.
-/




/-- `μHE[2]` is by definition a constant multiple of `μH[2]`, so
multiplicative comparisons transfer verbatim from the gauge measure to
the Euclidean-normalized one.  Used to move the Lipschitz-image
estimates (stated for `μH`) to `μHE`. -/
private lemma muHE_le_of_muH_le {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {A B : Set X} {k : ℝ≥0∞}
    (h : μH[(2 : ℝ)] A ≤ k * μH[(2 : ℝ)] B) :
    μHE[2] A ≤ k * μHE[2] B := by
  rw [Measure.euclideanHausdorffMeasure_def]
  simp only [Nat.cast_ofNat, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact le_trans (mul_le_mul_right h _) (le_of_eq (by ring))

variable (f : E2 → ℝ)

/-- The tangent affine graph map at `zQ`:
`Φ_Q(z) = (z, f(zQ) + Df(zQ)(z − zQ))` (paper §7, `Φ_Q`).
It is `affGraphMap p c` for `p` the gradient of `f` at `zQ` and
`c := f zQ − ⟨p, zQ⟩`, so `affine_area` applies to it. -/
def tangentMap (zQ z : E2) : E3 :=
  WithLp.toLp 2 (z, f zQ + fderiv ℝ f zQ (z - zQ))

variable {f} {U Q : Set E2} {zQ : E2} {ε : ℝ}

/-- Displacements of the tangent map, componentwise (inequality (3) of
the paper follows via `norm_fst_le_norm_toLp`). -/
lemma tangentMap_sub (z z' : E2) :
    tangentMap f zQ z - tangentMap f zQ z'
      = WithLp.toLp 2 (z - z', fderiv ℝ f zQ (z - z')) := by
  rw [tangentMap, tangentMap, ← WithLp.toLp_sub, Prod.mk_sub_mk,
    add_sub_add_left_eq_sub, ← map_sub, sub_sub_sub_cancel_right]

/-- **Paper Lemma 7.1** (first-order Taylor estimate along segments).
In Mathlib this is the mean value inequality against the fixed
candidate derivative `φ := fderiv ℝ f zQ`
(`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`). -/
theorem taylor_estimate (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hQ : Convex ℝ Q) (hQU : Q ⊆ U) (_hzQ : zQ ∈ Q)
    (hgrad : ∀ z ∈ Q, ‖fderiv ℝ f z - fderiv ℝ f zQ‖ ≤ ε)
    {z z' : E2} (hz : z ∈ Q) (hz' : z' ∈ Q) :
    |f z - f z' - fderiv ℝ f zQ (z - z')| ≤ ε * ‖z - z'‖ := by
  have hdiff : ∀ x ∈ Q, HasFDerivWithinAt f (fderiv ℝ f x) Q x := fun x hx =>
    (((hf.differentiableOn one_ne_zero).differentiableAt
      (hU.mem_nhds (hQU hx))).hasFDerivAt).hasFDerivWithinAt
  simpa [Real.norm_eq_abs] using
    hQ.norm_image_sub_le_of_norm_hasFDerivWithin_le' hdiff hgrad hz' hz

/-- **Paper Proposition 7.2** (bi-Lipschitz sandwich).  The difference
of the displacement vectors of `Φ` and `Φ_Q` is purely vertical, equal
to the Taylor remainder; combine `taylor_estimate` with inequality (3)
and the triangle inequality. -/
theorem biLipschitz_sandwich (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hQ : Convex ℝ Q) (hQU : Q ⊆ U) (hzQ : zQ ∈ Q)
    (hgrad : ∀ z ∈ Q, ‖fderiv ℝ f z - fderiv ℝ f zQ‖ ≤ ε)
    {z z' : E2} (hz : z ∈ Q) (hz' : z' ∈ Q) :
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
      = WithLp.toLp 2 ((0 : E2), f z - f z' - fderiv ℝ f zQ (z - z')) := by
    rw [graphMap_sub, tangentMap_sub, ← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self]
  -- ... and hence bounded by `ε ‖z - z'‖ ≤ ε ‖Φ_Q z - Φ_Q z'‖` by
  -- Lemma 7.1 and inequality (3).
  have hzT : ‖z - z'‖ ≤ ‖tangentMap f zQ z - tangentMap f zQ z'‖ := by
    rw [tangentMap_sub]; exact norm_fst_le_norm_toLp _ _
  have hvert : ‖graphMap f z - graphMap f z' - (tangentMap f zQ z - tangentMap f zQ z')‖
      ≤ ε * ‖tangentMap f zQ z - tangentMap f zQ z'‖ := by
    rw [hdiff]
    calc ‖(WithLp.toLp 2 ((0 : E2), f z - f z' - fderiv ℝ f zQ (z - z')) : E3)‖
        ≤ ‖(0 : E2)‖ + |f z - f z' - fderiv ℝ f zQ (z - z')| := norm_toLp_le _ _
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

/-- **Paper Corollary 7.3** (local two-sided area estimate).

The transport map `T := Φ ∘ Φ_Q⁻¹ : Φ_Q(S) → Φ(S)` — which in Lean is
simply `Φ` composed with the first-coordinate projection — is
`(1+ε)`-Lipschitz with `(1−ε)⁻¹`-Lipschitz inverse by Prop 7.2; apply
the Lipschitz scaling of Hausdorff measure in both directions and
evaluate the tangent patch by `affine_area`. -/
theorem local_area_estimate (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hQ : Convex ℝ Q) (hQU : Q ⊆ U) (hzQ : zQ ∈ Q)
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hgrad : ∀ z ∈ Q, ‖fderiv ℝ f z - fderiv ℝ f zQ‖ ≤ ε)
    (S : Set E2) (hS : S ⊆ Q) :
    ENNReal.ofReal ((1 - ε) ^ 2 * jac f zQ) * volume S
        ≤ μHE[2] (graph f S) ∧
      μHE[2] (graph f S)
        ≤ ENNReal.ofReal ((1 + ε) ^ 2 * jac f zQ) * volume S := by
  obtain ⟨hε0, hε1⟩ := hε
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  -- Identify the tangent map as an affine graph map; its area is exact.
  set p : E2 := (InnerProductSpace.toDual ℝ E2).symm (fderiv ℝ f zQ) with hpdef
  have hpz : ∀ w, inner ℝ p w = fderiv ℝ f zQ w := fun w =>
    InnerProductSpace.toDual_symm_apply
  have hjac : jac f zQ = Real.sqrt (1 + ‖p‖ ^ 2) := by
    rw [jac, hpdef, LinearIsometryEquiv.norm_map]
  have haff : μHE[2] (tangentMap f zQ '' S)
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
  have hgcomp : ∀ w : E2,
      graphMap f ((WithLp.ofLp (tangentMap f zQ w)).1) = graphMap f w := fun w => rfl
  -- Upper bound: the forward transport is (1+ε)-Lipschitz.
  have hg_lip : LipschitzOnWith (1 + ε).toNNReal
      (fun w : E3 => graphMap f ((WithLp.ofLp w).1)) (tangentMap f zQ '' S) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    rintro x ⟨zx, hzx, rfl⟩ y ⟨zy, hzy, rfl⟩
    rw [Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ 1 + ε)]
    show dist (graphMap f zx) (graphMap f zy)
      ≤ (1 + ε) * dist (tangentMap f zQ zx) (tangentMap f zQ zy)
    rw [dist_eq_norm, dist_eq_norm]
    exact (biLipschitz_sandwich hU hf hQ hQU hzQ hgrad (hS hzx) (hS hzy)).2
  -- Lower bound: the backward transport is (1−ε)⁻¹-Lipschitz.
  have hh_lip : LipschitzOnWith (1 - ε)⁻¹.toNNReal
      (fun w : E3 => tangentMap f zQ ((WithLp.ofLp w).1)) (graph f S) := by
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
  have himgg : (fun w : E3 => graphMap f ((WithLp.ofLp w).1)) '' (tangentMap f zQ '' S)
      = graph f S := by
    rw [Set.image_image]; rfl
  have himgh : (fun w : E3 => tangentMap f zQ ((WithLp.ofLp w).1)) '' (graph f S)
      = tangentMap f zQ '' S := by
    rw [graph, Set.image_image]; rfl
  -- Hausdorff-measure comparison (gauge measure `μH`), then transfer to
  -- `μHE` by the constant scalar.
  have hupH := hg_lip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 2)
  have hlowH := hh_lip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 2)
  rw [himgg] at hupH
  rw [himgh] at hlowH
  -- Convert the Lipschitz constants to `ENNReal.ofReal` of real squares.
  have hcast : ∀ (a : ℝ), 0 ≤ a → ((a.toNNReal : ℝ≥0∞) ^ (2:ℝ)
      = ENNReal.ofReal (a ^ 2)) := by
    intro a ha
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.ofReal_pow ha]
    rfl
  constructor
  · -- Lower: (1−ε)² jac · vol S ≤ μHE (graph f S)
    -- From hlowH : μH (tangent '' S) ≤ (1−ε)⁻² μH (graph f S)
    have h1 : μHE[2] (tangentMap f zQ '' S)
        ≤ ENNReal.ofReal ((1 - ε)⁻¹ ^ 2) * μHE[2] (graph f S) := by
      apply muHE_le_of_muH_le
      rw [← hcast _ (by positivity)]
      exact hlowH
    rw [haff] at h1
    -- Multiply through by (1−ε)² and simplify.
    have hkey : ENNReal.ofReal ((1 - ε) ^ 2) * (ENNReal.ofReal (jac f zQ) * volume S)
        ≤ ENNReal.ofReal ((1 - ε) ^ 2) * (ENNReal.ofReal ((1 - ε)⁻¹ ^ 2)
            * μHE[2] (graph f S)) :=
      mul_le_mul_right h1 _
    calc ENNReal.ofReal ((1 - ε) ^ 2 * jac f zQ) * volume S
        = ENNReal.ofReal ((1 - ε) ^ 2) * (ENNReal.ofReal (jac f zQ) * volume S) := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ ENNReal.ofReal ((1 - ε) ^ 2) * (ENNReal.ofReal ((1 - ε)⁻¹ ^ 2)
            * μHE[2] (graph f S)) := hkey
      _ = μHE[2] (graph f S) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          rw [show (1 - ε) ^ 2 * (1 - ε)⁻¹ ^ 2 = 1 by field_simp]
          simp
  · -- Upper: μHE (graph f S) ≤ (1+ε)² jac · vol S
    have h2 : μHE[2] (graph f S)
        ≤ ENNReal.ofReal ((1 + ε) ^ 2) * μHE[2] (tangentMap f zQ '' S) := by
      apply muHE_le_of_muH_le
      rw [← hcast _ (by positivity)]
      exact hupH
    rw [haff] at h2
    calc μHE[2] (graph f S)
        ≤ ENNReal.ofReal ((1 + ε) ^ 2) * (ENNReal.ofReal (jac f zQ) * volume S) := h2
      _ = ENNReal.ofReal ((1 + ε) ^ 2 * jac f zQ) * volume S := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]

/-
# Dyadic squares and the graph over a closed square (paper §3.1, §8)

Contents:
* `closedSquare` and its elementary properties;
* the dyadic decomposition of open sets (paper Lem 3.3), proven by the
  greedy maximal-square selection;
* the Lean replacement for the paper's shrinking trick: 1-dimensional
  Lipschitz images (graphs over segments, and later the equator of the
  sphere) are `μHE[2]`-null, and graphs over volume-null sets are
  area-null;
* the area formula over a closed square (paper Thm 8.2), proven by the
  Riemann-grid argument.
-/




/-- Closed axis-parallel square with center `z₀` and side `s`
(paper's "square"; sides parallel to the axes).  Built from coordinate
conditions — `Metric.closedBall` in `E2` would be a *disk*. -/
def closedSquare (z₀ : E2) (s : ℝ) : Set E2 :=
  {z | ∀ i, |z i - z₀ i| ≤ s / 2}

lemma convex_closedSquare (z₀ : E2) (s : ℝ) :
    Convex ℝ (closedSquare z₀ s) := by
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

/-- Points of the square are within `s√2/2` of the center (paper §3.1);
in fact `diam = s√2`, but only this inclusion is ever used. -/
lemma closedSquare_subset_closedBall (z₀ : E2) {s : ℝ} (hs : 0 ≤ s) :
    closedSquare z₀ s ⊆ Metric.closedBall z₀ (s * Real.sqrt 2 / 2) := by
  intro z hz
  rw [Metric.mem_closedBall, EuclideanSpace.dist_eq, Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq]
  have h0 := hz 0
  have h1 := hz 1
  have hb : |z 0 - z₀ 0| ^ 2 + |z 1 - z₀ 1| ^ 2 ≤ (s / 2) ^ 2 + (s / 2) ^ 2 := by
    have := abs_nonneg (z 0 - z₀ 0)
    have := abs_nonneg (z 1 - z₀ 1)
    nlinarith
  calc Real.sqrt (|z 0 - z₀ 0| ^ 2 + |z 1 - z₀ 1| ^ 2)
      ≤ Real.sqrt ((s / 2) ^ 2 + (s / 2) ^ 2) := Real.sqrt_le_sqrt hb
    _ = s * Real.sqrt 2 / 2 := by
        rw [show (s / 2) ^ 2 + (s / 2) ^ 2 = (s * Real.sqrt 2 / 2) ^ 2 by
          linear_combination (-(s ^ 2) / 4) * Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
        exact Real.sqrt_sq (by positivity)

lemma isCompact_closedSquare (z₀ : E2) (s : ℝ) :
    IsCompact (closedSquare z₀ s) := by
  by_cases hs : 0 ≤ s
  case neg =>
    rw [not_le] at hs
    have hempty : closedSquare z₀ s = ∅ := by
      ext z
      simp only [closedSquare, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_forall]
      exact ⟨0, by intro h; linarith [abs_nonneg (z 0 - z₀ 0)]⟩
    rw [hempty]; exact isCompact_empty
  case pos =>
    have hclosed : IsClosed (closedSquare z₀ s) := by
      have hrw : closedSquare z₀ s = ⋂ i, {z : E2 | |z i - z₀ i| ≤ s / 2} := by
        ext z; simp [closedSquare, Set.mem_iInter]
      rw [hrw]
      refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
      have : Continuous fun z : E2 => z i :=
        (ContinuousLinearMap.continuous (EuclideanSpace.proj (𝕜 := ℝ) i))
      fun_prop
    exact Metric.isCompact_of_isClosed_isBounded hclosed
      ((Metric.isBounded_closedBall).subset (closedSquare_subset_closedBall z₀ hs))

/-- `m(Q) = s²` (paper (P1)); via the volume-preserving identification
of `E2` with `Fin 2 → ℝ` and Tonelli for boxes. -/
lemma volume_closedSquare (z₀ : E2) {s : ℝ} (hs : 0 ≤ s) :
    volume (closedSquare z₀ s) = ENNReal.ofReal (s ^ 2) := by
  have hpre : closedSquare z₀ s
      = WithLp.ofLp ⁻¹' (Set.univ.pi fun i : Fin 2 =>
          Set.Icc (z₀ i - s / 2) (z₀ i + s / 2)) := by
    ext z
    simp only [closedSquare, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, true_implies, Set.mem_Icc]
    refine forall_congr' fun i => ?_
    rw [abs_le]
    constructor
    · rintro ⟨ha, hb⟩; constructor <;> linarith
    · rintro ⟨ha, hb⟩; constructor <;> linarith
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    ((MeasurableSet.univ_pi fun i => measurableSet_Icc).nullMeasurableSet),
    volume_pi_pi]
  have hval : ∀ i : Fin 2, volume (Set.Icc (z₀ i - s / 2) (z₀ i + s / 2))
      = ENNReal.ofReal s := by
    intro i; rw [Real.volume_Icc]; congr 1; ring
  simp only [hval]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow hs]

/-! ## Open squares and null frontiers -/

/-- Open axis-parallel square. -/
def openSquare (z₀ : E2) (s : ℝ) : Set E2 :=
  {z | ∀ i, |z i - z₀ i| < s / 2}

lemma openSquare_subset_closedSquare (z₀ : E2) (s : ℝ) :
    openSquare z₀ s ⊆ closedSquare z₀ s :=
  fun _z hz i => (hz i).le

lemma isOpen_openSquare (z₀ : E2) (s : ℝ) : IsOpen (openSquare z₀ s) := by
  have hrw : openSquare z₀ s = ⋂ i, {z : E2 | |z i - z₀ i| < s / 2} := by
    ext z; simp [openSquare, Set.mem_iInter]
  rw [hrw]
  refine isOpen_iInter_of_finite fun i => isOpen_lt ?_ continuous_const
  have : Continuous fun z : E2 => z i :=
    (ContinuousLinearMap.continuous (EuclideanSpace.proj (𝕜 := ℝ) i))
  fun_prop

lemma volume_openSquare (z₀ : E2) {s : ℝ} (hs : 0 ≤ s) :
    volume (openSquare z₀ s) = ENNReal.ofReal (s ^ 2) := by
  have hpre : openSquare z₀ s
      = WithLp.ofLp ⁻¹' (Set.univ.pi fun i : Fin 2 =>
          Set.Ioo (z₀ i - s / 2) (z₀ i + s / 2)) := by
    ext z
    simp only [openSquare, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, true_implies, Set.mem_Ioo]
    refine forall_congr' fun i => ?_
    rw [abs_lt]
    constructor
    · rintro ⟨ha, hb⟩; constructor <;> linarith
    · rintro ⟨ha, hb⟩; constructor <;> linarith
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    ((MeasurableSet.univ_pi fun i => measurableSet_Ioo).nullMeasurableSet),
    volume_pi_pi]
  have hval : ∀ i : Fin 2, volume (Set.Ioo (z₀ i - s / 2) (z₀ i + s / 2))
      = ENNReal.ofReal s := by
    intro i; rw [Real.volume_Ioo]; congr 1; ring
  simp only [hval]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow hs]

/-- The frontier of a square is volume-null: closed and open squares
have the same (finite) volume `s²`. -/
lemma volume_frontier_closedSquare (z₀ : E2) {s : ℝ} (hs : 0 ≤ s) :
    volume (closedSquare z₀ s \ interior (closedSquare z₀ s)) = 0 := by
  have h1 : volume (interior (closedSquare z₀ s)) = ENNReal.ofReal (s ^ 2) := by
    apply le_antisymm
    · calc volume (interior (closedSquare z₀ s))
          ≤ volume (closedSquare z₀ s) := measure_mono interior_subset
        _ = ENNReal.ofReal (s ^ 2) := volume_closedSquare z₀ hs
    · calc ENNReal.ofReal (s ^ 2) = volume (openSquare z₀ s) :=
          (volume_openSquare z₀ hs).symm
        _ ≤ volume (interior (closedSquare z₀ s)) := measure_mono
            (interior_maximal (openSquare_subset_closedSquare z₀ s)
              (isOpen_openSquare z₀ s))
  rw [measure_diff interior_subset measurableSet_interior.nullMeasurableSet
    (by rw [h1]; exact ENNReal.ofReal_ne_top)]
  rw [volume_closedSquare z₀ hs, h1, tsub_self]

/-- The interior of a (nondegenerate) closed square is contained in the
open square: boundary points can be pushed outside along a coordinate
direction. -/
lemma interior_closedSquare_subset (z₀ : E2) {s : ℝ} (hs : 0 < s) :
    interior (closedSquare z₀ s) ⊆ openSquare z₀ s := by
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  intro l
  rcases eq_or_ne (x l) (z₀ l) with heq | hne
  · rw [heq, sub_self, abs_zero]
    exact half_pos hs
  · set c : ℝ := if 0 < x l - z₀ l then ε / 2 else -(ε / 2) with hc
    have hcabs : |c| = ε / 2 := by
      rw [hc]; split_ifs <;> simp [abs_of_pos (half_pos hε)]
    set y : E2 := x + c • EuclideanSpace.single l (1 : ℝ) with hydef
    have hy : y ∈ closedSquare z₀ s := by
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

/-! ## The greedy dyadic decomposition (paper §3.1, Lemmas 3.2 & 3.3)

Dyadic squares of generation `k` (side `σ/2^k`) are indexed by
`(k, i, j) : ℕ × ℤ × ℤ`.  The greedy family keeps a square iff it lies
in `U` but its parent does not; the nesting dichotomy (paper Lem 3.2)
is integer arithmetic. -/

section Dyadic

variable {U : Set E2} {σ : ℝ}

/-- Side length of generation-`k` dyadic squares. -/
private def dside (σ : ℝ) (k : ℕ) : ℝ := σ / 2 ^ k

/-- Center of the generation-`k` dyadic square with indices `(i, j)`. -/
private def dctr (σ : ℝ) (k : ℕ) (i j : ℤ) : E2 :=
  WithLp.toLp 2 ![(i + 1 / 2 : ℝ) * dside σ k, (j + 1 / 2 : ℝ) * dside σ k]

/-- The generation-`k` dyadic square with indices `(i, j)`. -/
private def dsq (σ : ℝ) (k : ℕ) (i j : ℤ) : Set E2 :=
  closedSquare (dctr σ k i j) (dside σ k)

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

private lemma mem_dsq {k : ℕ} {i j : ℤ} {x : E2} :
    x ∈ dsq σ k i j ↔
      (i * dside σ k ≤ x 0 ∧ x 0 ≤ (i + 1) * dside σ k) ∧
      (j * dside σ k ≤ x 1 ∧ x 1 ≤ (j + 1) * dside σ k) := by
  have h0 : (dctr σ k i j) 0 = (i + 1 / 2 : ℝ) * dside σ k := rfl
  have h1 : (dctr σ k i j) 1 = (j + 1 / 2 : ℝ) * dside σ k := rfl
  unfold dsq closedSquare
  rw [Set.mem_setOf_eq, Fin.forall_fin_two, h0, h1, abs_le, abs_le]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private lemma mem_dsq_open {k : ℕ} {i j : ℤ} {x : E2} :
    x ∈ openSquare (dctr σ k i j) (dside σ k) ↔
      (i * dside σ k < x 0 ∧ x 0 < (i + 1) * dside σ k) ∧
      (j * dside σ k < x 1 ∧ x 1 < (j + 1) * dside σ k) := by
  have h0 : (dctr σ k i j) 0 = (i + 1 / 2 : ℝ) * dside σ k := rfl
  have h1 : (dctr σ k i j) 1 = (j + 1 / 2 : ℝ) * dside σ k := rfl
  unfold openSquare
  rw [Set.mem_setOf_eq, Fin.forall_fin_two, h0, h1, abs_lt, abs_lt]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- **Paper Lemma 3.2**, one axis: if the open dyadic intervals of
generations `k ≤ k'` overlap, the finer one is contained in the
coarser one. -/
private lemma interval_nest (hσ : 0 < σ) {k k' : ℕ} (hkk : k ≤ k') {i i' : ℤ} {t : ℝ}
    (h1 : i * dside σ k < t) (h2 : t < (i + 1) * dside σ k)
    (h1' : i' * dside σ k' < t) (h2' : t < (i' + 1) * dside σ k') :
    i * dside σ k ≤ i' * dside σ k' ∧ (i' + 1) * dside σ k' ≤ (i + 1) * dside σ k := by
  have hL'pos : 0 < dside σ k' := dside_pos hσ k'
  set m : ℕ := k' - k with hm
  have hLk : dside σ k = (2 : ℝ) ^ m * dside σ k' := by
    unfold dside
    rw [show k' = m + k by omega, pow_add]
    field_simp
  set q : ℤ := i * 2 ^ m with hq
  have hqL : (q : ℝ) * dside σ k' = i * dside σ k := by
    rw [hq, hLk]; push_cast; ring
  have hq2L : ((q : ℝ) + 2 ^ m) * dside σ k' = (i + 1) * dside σ k := by
    rw [hq, hLk]; push_cast; ring
  have hle1 : q ≤ i' := by
    have hlt : (q : ℝ) * dside σ k' < ((i' : ℝ) + 1) * dside σ k' := by
      rw [hqL]; exact h1.trans h2'
    have hqi : (q : ℝ) < (i' : ℝ) + 1 := lt_of_mul_lt_mul_right hlt hL'pos.le
    have hcast : (q : ℝ) < ((i' + 1 : ℤ) : ℝ) := by push_cast; linarith
    have : q < i' + 1 := by exact_mod_cast hcast
    omega
  have hle2 : i' + 1 ≤ q + 2 ^ m := by
    have hlt : (i' : ℝ) * dside σ k' < ((q : ℝ) + 2 ^ m) * dside σ k' := by
      rw [hq2L]; exact h1'.trans h2
    have hqi : (i' : ℝ) < (q : ℝ) + 2 ^ m := lt_of_mul_lt_mul_right hlt hL'pos.le
    have hcast : ((i' : ℤ) : ℝ) < ((q + 2 ^ m : ℤ) : ℝ) := by push_cast; linarith
    have : i' < q + 2 ^ m := by exact_mod_cast hcast
    omega
  constructor
  · rw [← hqL]
    have : ((q : ℤ) : ℝ) ≤ ((i' : ℤ) : ℝ) := by exact_mod_cast hle1
    exact mul_le_mul_of_nonneg_right this hL'pos.le
  · rw [← hq2L]
    have h : ((i' + 1 : ℤ) : ℝ) ≤ ((q + 2 ^ m : ℤ) : ℝ) := by exact_mod_cast hle2
    have h' : ((i' : ℝ) + 1) ≤ (q : ℝ) + 2 ^ m := by push_cast at h; linarith
    exact mul_le_mul_of_nonneg_right h' hL'pos.le

/-- Nesting for squares: overlapping open squares of generations
`k ≤ k'` force the finer closed square inside the coarser one. -/
private lemma dsq_nest (hσ : 0 < σ) {k k' : ℕ} (hkk : k ≤ k') {i j i' j' : ℤ} {x : E2}
    (hx : x ∈ openSquare (dctr σ k i j) (dside σ k))
    (hx' : x ∈ openSquare (dctr σ k' i' j') (dside σ k')) :
    dsq σ k' i' j' ⊆ dsq σ k i j := by
  rw [mem_dsq_open] at hx hx'
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  obtain ⟨⟨h1', h2'⟩, h3', h4'⟩ := hx'
  obtain ⟨hA, hB⟩ := interval_nest hσ hkk h1 h2 h1' h2'
  obtain ⟨hC, hD⟩ := interval_nest hσ hkk h3 h4 h3' h4'
  intro y hy
  rw [mem_dsq] at hy ⊢
  obtain ⟨⟨g1, g2⟩, g3, g4⟩ := hy
  exact ⟨⟨hA.trans g1, g2.trans hB⟩, hC.trans g3, g4.trans hD⟩

/-- Same-generation open squares that overlap are identical. -/
private lemma dsq_eq_of_open_inter (hσ : 0 < σ) {k : ℕ} {i j i' j' : ℤ} {x : E2}
    (hx : x ∈ openSquare (dctr σ k i j) (dside σ k))
    (hx' : x ∈ openSquare (dctr σ k i' j') (dside σ k)) :
    i = i' ∧ j = j' := by
  have hLpos := dside_pos hσ k
  rw [mem_dsq_open] at hx hx'
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  obtain ⟨⟨h1', h2'⟩, h3', h4'⟩ := hx'
  obtain ⟨hA, -⟩ := interval_nest hσ le_rfl h1 h2 h1' h2'
  obtain ⟨hA', -⟩ := interval_nest hσ le_rfl h1' h2' h1 h2
  obtain ⟨hC, -⟩ := interval_nest hσ le_rfl h3 h4 h3' h4'
  obtain ⟨hC', -⟩ := interval_nest hσ le_rfl h3' h4' h3 h4
  constructor
  · have : (i : ℝ) = (i' : ℝ) := by
      have := le_antisymm hA hA'
      exact mul_right_cancel₀ hLpos.ne' this
    exact_mod_cast this
  · have : (j : ℝ) = (j' : ℝ) := by
      have := le_antisymm hC hC'
      exact mul_right_cancel₀ hLpos.ne' this
    exact_mod_cast this

/-- Each dyadic square is contained in its parent. -/
private lemma dsq_subset_parent (hσ : 0 < σ) (k : ℕ) (i j : ℤ) :
    dsq σ (k + 1) i j ⊆ dsq σ k (i / 2) (j / 2) := by
  have hL := dside_succ σ k
  have hL'pos := dside_pos hσ (k + 1)
  intro y hy
  rw [mem_dsq] at hy ⊢
  obtain ⟨⟨g1, g2⟩, g3, g4⟩ := hy
  have key : ∀ (a : ℤ) (t : ℝ), a * dside σ (k+1) ≤ t → t ≤ (a + 1) * dside σ (k+1) →
      (a / 2 : ℤ) * dside σ k ≤ t ∧ t ≤ ((a / 2 : ℤ) + 1) * dside σ k := by
    intro a t hta htb
    have hdiv1 : ((a / 2 : ℤ) : ℝ) * 2 ≤ (a : ℝ) := by
      have : (a / 2) * 2 ≤ a := by omega
      exact_mod_cast this
    have hdiv2 : ((a : ℝ) + 1) ≤ (((a / 2 : ℤ) : ℝ) + 1) * 2 := by
      have : a + 1 ≤ (a / 2 + 1) * 2 := by omega
      exact_mod_cast this
    constructor
    · calc ((a / 2 : ℤ) : ℝ) * dside σ k
          = ((a / 2 : ℤ) : ℝ) * 2 * dside σ (k+1) := by rw [← hL]; ring
        _ ≤ (a : ℝ) * dside σ (k+1) := mul_le_mul_of_nonneg_right hdiv1 hL'pos.le
        _ ≤ t := hta
    · calc t ≤ ((a : ℝ) + 1) * dside σ (k+1) := htb
        _ ≤ (((a / 2 : ℤ) : ℝ) + 1) * 2 * dside σ (k+1) :=
            mul_le_mul_of_nonneg_right hdiv2 hL'pos.le
        _ = (((a / 2 : ℤ) : ℝ) + 1) * dside σ k := by rw [← hL]; ring
  exact ⟨key i (y 0) g1 g2, key j (y 1) g3 g4⟩

/-- The greedy dyadic family: generation-`k` squares inside `U` whose
parent (for `k > 0`) is not inside `U`. -/
private def dFam (σ : ℝ) (U : Set E2) : Set (ℕ × ℤ × ℤ) :=
  {p | dsq σ p.1 p.2.1 p.2.2 ⊆ U ∧
    ∀ k₀, p.1 = k₀ + 1 → ¬ dsq σ k₀ (p.2.1 / 2) (p.2.2 / 2) ⊆ U}

/-- Every point of the open set lies in a member of the greedy family
(paper Lem 3.3, "S covers V"). -/
private lemma exists_dsq_mem (hσ : 0 < σ) (hU : IsOpen U) {x : E2} (hx : x ∈ U) :
    ∃ p ∈ dFam σ U, x ∈ dsq σ p.1 p.2.1 p.2.2 := by
  classical
  set I : ℕ → ℤ := fun k => ⌊x 0 / dside σ k⌋ with hI
  set J : ℕ → ℤ := fun k => ⌊x 1 / dside σ k⌋ with hJ
  have hmem : ∀ k, x ∈ dsq σ k (I k) (J k) := by
    intro k
    have hL := dside_pos hσ k
    rw [mem_dsq]
    constructor
    · constructor
      · exact (le_div_iff₀ hL).mp (Int.floor_le (x 0 / dside σ k))
      · have h1 := Int.lt_floor_add_one (x 0 / dside σ k)
        have h2 := (div_lt_iff₀ hL).mp h1
        push_cast at h2 ⊢
        linarith
    · constructor
      · exact (le_div_iff₀ hL).mp (Int.floor_le (x 1 / dside σ k))
      · have h1 := Int.lt_floor_add_one (x 1 / dside σ k)
        have h2 := (div_lt_iff₀ hL).mp h1
        push_cast at h2 ⊢
        linarith
  have hsmall : ∃ k, dsq σ k (I k) (J k) ⊆ U := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (σ * Real.sqrt 2 / r) one_lt_two
    refine ⟨n, fun y hy => hball ?_⟩
    have hLn := dside_pos hσ n
    rw [Metric.mem_ball]
    have hx' := hmem n
    rw [mem_dsq] at hy hx'
    have e0 : |y 0 - x 0| ≤ dside σ n := by
      rw [abs_le]
      constructor <;> [linarith [hy.1.1, hx'.1.2]; linarith [hy.1.2, hx'.1.1]]
    have e1 : |y 1 - x 1| ≤ dside σ n := by
      rw [abs_le]
      constructor <;> [linarith [hy.2.1, hx'.2.2]; linarith [hy.2.2, hx'.2.1]]
    have hb : |y 0 - x 0| ^ 2 + |y 1 - x 1| ^ 2 ≤ 2 * dside σ n ^ 2 := by
      nlinarith [abs_nonneg (y 0 - x 0), abs_nonneg (y 1 - x 1)]
    have hdist : dist y x ≤ dside σ n * Real.sqrt 2 := by
      rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
      calc Real.sqrt (|y 0 - x 0| ^ 2 + |y 1 - x 1| ^ 2)
          ≤ Real.sqrt (2 * dside σ n ^ 2) := Real.sqrt_le_sqrt hb
        _ = dside σ n * Real.sqrt 2 := by
            rw [show (2 : ℝ) * dside σ n ^ 2 = (dside σ n * Real.sqrt 2) ^ 2 by
              linear_combination (-(dside σ n ^ 2)) *
                Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
            exact Real.sqrt_sq (by positivity)
    have hfin : dside σ n * Real.sqrt 2 < r := by
      unfold dside
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hr] at hn
      linarith
    exact lt_of_le_of_lt hdist hfin
  set khat := Nat.find hsmall with hkhat
  have hspec : dsq σ khat (I khat) (J khat) ⊆ U := Nat.find_spec hsmall
  refine ⟨(khat, I khat, J khat), ⟨hspec, ?_⟩, hmem khat⟩
  intro k₀ hk₀
  have hk : khat = k₀ + 1 := hk₀
  have hmin := Nat.find_min hsmall (show k₀ < khat by omega)
  have hIdiv : I khat / 2 = I k₀ := by
    have hstep : x 0 / dside σ k₀ = x 0 / dside σ khat / 2 := by
      rw [hk]
      unfold dside
      rw [pow_succ]
      field_simp
    show ⌊x 0 / dside σ khat⌋ / 2 = ⌊x 0 / dside σ k₀⌋
    rw [hstep, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Int.floor_div_natCast]
    norm_num
  have hJdiv : J khat / 2 = J k₀ := by
    have hstep : x 1 / dside σ k₀ = x 1 / dside σ khat / 2 := by
      rw [hk]
      unfold dside
      rw [pow_succ]
      field_simp
    show ⌊x 1 / dside σ khat⌋ / 2 = ⌊x 1 / dside σ k₀⌋
    rw [hstep, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Int.floor_div_natCast]
    norm_num
  rw [hIdiv, hJdiv]
  exact hmin

/-- Distinct members of the greedy family have disjoint open squares. -/
private lemma dFam_open_disjoint (hσ : 0 < σ) {p q : ℕ × ℤ × ℤ}
    (hp : p ∈ dFam σ U) (hq : q ∈ dFam σ U) (hpq : p ≠ q) {x : E2}
    (hxp : x ∈ openSquare (dctr σ p.1 p.2.1 p.2.2) (dside σ p.1))
    (hxq : x ∈ openSquare (dctr σ q.1 q.2.1 q.2.2) (dside σ q.1)) : False := by
  wlog hkk : p.1 ≤ q.1 generalizing p q with H
  · exact H hq hp (Ne.symm hpq) hxq hxp (le_of_not_ge hkk)
  rcases Nat.eq_or_lt_of_le hkk with heq | hlt
  · obtain ⟨pk, pi, pj⟩ := p
    obtain ⟨qk, qi, qj⟩ := q
    simp only at heq hxp hxq
    subst heq
    obtain ⟨hi, hj⟩ := dsq_eq_of_open_inter hσ hxp hxq
    exact hpq (by simp [hi, hj])
  · obtain ⟨k₀, hk₀⟩ : ∃ k₀, q.1 = k₀ + 1 := ⟨q.1 - 1, by omega⟩
    have hxparent : x ∈ openSquare (dctr σ k₀ (q.2.1 / 2) (q.2.2 / 2)) (dside σ k₀) := by
      apply interior_closedSquare_subset _ (dside_pos hσ _)
      have hsub : openSquare (dctr σ q.1 q.2.1 q.2.2) (dside σ q.1)
          ⊆ dsq σ k₀ (q.2.1 / 2) (q.2.2 / 2) := by
        refine (openSquare_subset_closedSquare _ _).trans ?_
        intro y hy
        rw [hk₀] at hy
        exact dsq_subset_parent hσ k₀ q.2.1 q.2.2 hy
      exact interior_maximal hsub (isOpen_openSquare _ _) hxq
    have hsubparent : dsq σ k₀ (q.2.1 / 2) (q.2.2 / 2) ⊆ dsq σ p.1 p.2.1 p.2.2 :=
      dsq_nest hσ (by omega) hxp hxparent
    exact (hq.2 k₀ hk₀) (hsubparent.trans hp.1)

/-- The greedy family is infinite (a finite union of closed squares is
closed, but a nonempty open `U` is closed only if `U = ℝ²`, which
contains infinitely many squares). -/
private lemma dFam_infinite (hσ : 0 < σ) (hU : IsOpen U) (hne : U.Nonempty) :
    (dFam σ U).Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hUeq : U = ⋃ p ∈ dFam σ U, dsq σ p.1 p.2.1 p.2.2 := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := exists_dsq_mem hσ hU hx
      exact Set.mem_biUnion hp hxp
    · exact Set.iUnion₂_subset fun p hp => hp.1
  have hclosed : IsClosed U := by
    rw [hUeq]
    exact hfin.isClosed_biUnion fun p _ => (isCompact_closedSquare _ _).isClosed
  have huniv : U = Set.univ := IsClopen.eq_univ ⟨hclosed, hU⟩ hne
  have hinf2 : (dFam σ U).Infinite := by
    apply Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => ((0 : ℕ), (n : ℤ), (0 : ℤ)))
    · intro a b hab
      simpa using hab
    · intro n
      refine ⟨?_, fun k₀ h => absurd h (by omega)⟩
      rw [huniv]
      exact Set.subset_univ _
  exact hinf2 hfin

/-- **Paper Lemma 3.3** (dyadic decomposition of open sets): a nonempty
open set is the union of countably many non-overlapping closed dyadic
squares of side at most `σ`, all contained in it. -/
theorem dyadic_decomposition {U : Set E2} (hU : IsOpen U) (hne : U.Nonempty)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ (z : ℕ → E2) (s : ℕ → ℝ),
      (∀ n, 0 < s n ∧ s n ≤ σ ∧ closedSquare (z n) (s n) ⊆ U) ∧
      (Pairwise fun m n =>
        interior (closedSquare (z m) (s m)) ∩
          interior (closedSquare (z n) (s n)) = ∅) ∧
      (⋃ n, closedSquare (z n) (s n)) = U := by
  have hinf := dFam_infinite hσ hU hne
  have hctble : (dFam σ U).Countable := Set.to_countable _
  haveI := hctble.to_subtype
  haveI := hinf.to_subtype
  obtain ⟨d⟩ := nonempty_denumerable ↥(dFam σ U)
  set e : ℕ ≃ ↥(dFam σ U) := (Denumerable.eqv ↥(dFam σ U)).symm with he
  refine ⟨fun n => dctr σ (e n).1.1 (e n).1.2.1 (e n).1.2.2,
    fun n => dside σ (e n).1.1,
    fun n => ⟨dside_pos hσ _, dside_le hσ _, ((e n).2).1⟩, ?_, ?_⟩
  · intro m n hmn
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxm, hxn⟩
    have hxm' := interior_closedSquare_subset _ (dside_pos hσ (e m).1.1) hxm
    have hxn' := interior_closedSquare_subset _ (dside_pos hσ (e n).1.1) hxn
    have hne' : ((e m) : ℕ × ℤ × ℤ) ≠ ((e n) : ℕ × ℤ × ℤ) := by
      intro h
      exact hmn (e.injective (Subtype.ext h))
    exact dFam_open_disjoint hσ (e m).2 (e n).2 hne' hxm' hxn'
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun n => ((e n).2).1
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := exists_dsq_mem hσ hU hx
      refine Set.mem_iUnion.mpr ⟨e.symm ⟨p, hp⟩, ?_⟩
      simp only [Equiv.apply_symm_apply]
      exact hxp

end Dyadic

/-! ## One-dimensional pieces are area-null -/

/-- Lipschitz curves over finite-length parameter sets carry no
`μHE[2]`-measure: `μH[1]` of the image is finite by the Lipschitz
bound and `μH[1] = volume` on ℝ, so
`euclideanHausdorffMeasure_zero_or_top` (1 < 2) kills the area.  This
is the engine behind both `graph_segment_null` (grid edges) and the
sphere's `equator_null`. -/
lemma euclideanHausdorff_two_image_null {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {γ : ℝ → X} {s : Set ℝ} {K : ℝ≥0}
    (hγ : LipschitzOnWith K γ s) (hfin : volume s ≠ ⊤) :
    μHE[2] (γ '' s) = 0 := by
  rcases Measure.euclideanHausdorffMeasure_zero_or_top
    (by norm_num : (1:ℕ) < 2) (γ '' s) with h | h
  · exact h
  · exfalso
    have h1 : μH[(1:ℝ)] (γ '' s) ≤ (K : ℝ≥0∞) ^ (1:ℝ) * μH[(1:ℝ)] s :=
      hγ.hausdorffMeasure_image_le (by norm_num)
    have hs1 : μH[(1:ℝ)] s = volume s := by
      rw [hausdorffMeasure_real]
    have h2 : μHE[1] (γ '' s) < ⊤ := by
      rw [Measure.euclideanHausdorffMeasure_def]
      simp only [Nat.cast_one, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
      refine ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_of_le_of_lt h1 ?_)
      rw [hs1, ENNReal.rpow_one]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_top_iff_ne_top.mpr hfin)
    exact absurd h h2.ne

/-- The graph over a segment is `μHE[2]`-null.

This is the Lean replacement for the paper's boundary bookkeeping (the
`(1−θ)`-shrinking in §8–§9): shared edges of adjacent grid squares are
graphs over segments, and they carry no `μHE[2]`-measure, so additivity
of the Borel measure `μHE[2]` on the (disjointified) closed pieces is
available directly. -/
theorem graph_segment_null {U : Set E2} {f : E2 → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {a b : E2} (hseg : segment ℝ a b ⊆ U) :
    μHE[2] (graph f (segment ℝ a b)) = 0 := by
  -- Bound the derivative on the compact segment; `f` is Lipschitz there.
  have hσcont : Continuous fun t : ℝ => a + t • (b - a) := by fun_prop
  have hcomp : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image' ℝ a b]
    exact isCompact_Icc.image hσcont
  have hcont : ContinuousOn (fderiv ℝ f) (segment ℝ a b) :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hseg
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC a (left_mem_segment ℝ a b))
  have hflip : LipschitzOnWith C.toNNReal f (segment ℝ a b) := by
    refine (convex_segment a b).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := fun x => fderiv ℝ f x) (fun x hx => ?_) (fun x hx => ?_)
    · exact (((hf.differentiableOn one_ne_zero).differentiableAt
        (hU.mem_nhds (hseg hx))).hasFDerivAt).hasFDerivWithinAt
    · rw [← norm_toNNReal]
      exact Real.toNNReal_mono (hC x hx)
  -- ... hence so is the graph map.
  have hgraphlip : LipschitzOnWith (1 + C.toNNReal) (graphMap f) (segment ℝ a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, graphMap_sub]
    have hfxy : |f x - f y| ≤ C * ‖x - y‖ := by
      have h := hflip.dist_le_mul x hx y hy
      rw [Real.dist_eq, Real.coe_toNNReal _ hC0, dist_eq_norm] at h
      exact h
    calc ‖(WithLp.toLp 2 (x - y, f x - f y) : E3)‖
        ≤ ‖x - y‖ + |f x - f y| := norm_toLp_le _ _
      _ ≤ ‖x - y‖ + C * ‖x - y‖ := by linarith
      _ = ((1 + C.toNNReal : ℝ≥0) : ℝ) * dist x y := by
          rw [dist_eq_norm]
          push_cast [Real.coe_toNNReal _ hC0]
          ring
  -- Parameterize the segment by [0,1] and conclude.
  have hσlip : LipschitzWith ‖b - a‖₊ (fun t : ℝ => a + t • (b - a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro t t'
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
      Real.norm_eq_abs, coe_nnnorm]
    exact le_of_eq (mul_comm _ _)
  have himg : graph f (segment ℝ a b)
      = (graphMap f ∘ fun t : ℝ => a + t • (b - a)) '' Set.Icc 0 1 := by
    rw [graph, segment_eq_image' ℝ a b, Set.image_comp]
  rw [himg]
  refine euclideanHausdorff_two_image_null
    (hgraphlip.comp hσlip.lipschitzOnWith fun t ht => ?_) ?_
  · rw [segment_eq_image' ℝ a b]
    exact Set.mem_image_of_mem _ ht
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

/-- On a compact convex subset of `U`, a C¹ function has Lipschitz
graph map (bounded derivative + mean value inequality); extracted from
`graph_segment_null` for reuse. -/
lemma exists_lipschitzOnWith_graphMap {U : Set E2} {f : E2 → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {K : Set E2} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKU : K ⊆ U) : ∃ L : ℝ≥0, LipschitzOnWith L (graphMap f) K := by
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
  calc ‖(WithLp.toLp 2 (x - y, f x - f y) : E3)‖
      ≤ ‖x - y‖ + |f x - f y| := norm_toLp_le _ _
    _ ≤ ‖x - y‖ + C' * ‖x - y‖ := by linarith
    _ = ((1 + C'.toNNReal : ℝ≥0) : ℝ) * dist x y := by
        rw [dist_eq_norm]
        push_cast [Real.coe_toNNReal _ hC0]
        ring

/-- Graphs over *volume-null* subsets of compact convex pieces of `U`
are `μHE[2]`-null.

This is the second half of the Lean replacement for the paper's
`(1−θ)`-shrinking: on a compact convex `K ⊆ U` the graph map is
Lipschitz, so it maps `μH[2]`-null sets to `μH[2]`-null sets; and
`volume`-null implies `μH[2]`-null on the plane by **abstract** Haar
uniqueness (`Measure.isAddLeftInvariant_eq_smul`) — the value `π/4` of
the constant is *not* needed. -/
lemma graph_null_of_volume_null {U : Set E2} {f : E2 → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {K S : Set E2} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKU : K ⊆ U) (hSK : S ⊆ K) (hS : volume S = 0) :
    μHE[2] (graph f S) = 0 := by
  -- `volume`-null implies `μH[2]`-null (mutual absolute continuity of
  -- Haar measures; no constant needed).
  have hμHS : μH[(2:ℝ)] S = 0 := by
    have key : (μH[(((2:ℕ)):ℝ)] : Measure E2)
        = addHaarScalarFactor (μH[(((2:ℕ)):ℝ)] : Measure E2) volume • volume :=
      Measure.isAddLeftInvariant_eq_smul _ _
    simp only [Nat.cast_ofNat] at key
    rw [key, Measure.smul_apply, hS, smul_zero]
  obtain ⟨L, hlip⟩ := exists_lipschitzOnWith_graphMap hU hf hK hKc hKU
  have himg : μH[(2:ℝ)] (graph f S) = 0 := by
    apply le_antisymm ?_ zero_le
    calc μH[(2:ℝ)] (graphMap f '' S)
        ≤ (L : ℝ≥0∞) ^ (2:ℝ) * μH[(2:ℝ)] S :=
          (hlip.mono hSK).hausdorffMeasure_image_le (by norm_num)
      _ = 0 := by rw [hμHS, mul_zero]
  rw [Measure.euclideanHausdorffMeasure_def]
  simp only [Nat.cast_ofNat, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [himg, mul_zero]

/-! ## Grid machinery for the Riemann-sum argument (paper §8) -/

/-- Coordinatewise membership in a closed square. -/
private lemma mem_closedSquare_iff {c : E2} {t : ℝ} {x : E2} :
    x ∈ closedSquare c t ↔
      (c 0 - t / 2 ≤ x 0 ∧ x 0 ≤ c 0 + t / 2) ∧
      (c 1 - t / 2 ≤ x 1 ∧ x 1 ≤ c 1 + t / 2) := by
  unfold closedSquare
  rw [Set.mem_setOf_eq, Fin.forall_fin_two, abs_le, abs_le]
  constructor
  · rintro ⟨⟨u1, u2⟩, u3, u4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨u1, u2⟩, u3, u4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Coordinatewise membership in an open square. -/
private lemma mem_openSquare_iff {c : E2} {t : ℝ} {x : E2} :
    x ∈ openSquare c t ↔
      (c 0 - t / 2 < x 0 ∧ x 0 < c 0 + t / 2) ∧
      (c 1 - t / 2 < x 1 ∧ x 1 < c 1 + t / 2) := by
  unfold openSquare
  rw [Set.mem_setOf_eq, Fin.forall_fin_two, abs_lt, abs_lt]
  constructor
  · rintro ⟨⟨u1, u2⟩, u3, u4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨u1, u2⟩, u3, u4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

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
      rw [hcast]
      exact hfl
    · have hfl := Int.lt_floor_add_one (t / h)
      have hfl2 : t < ((i0 : ℝ) + 1) * h := by
        rw [← div_lt_iff₀ hh]
        exact hfl
      have hcast : ((i0.toNat : ℕ) : ℝ) = (i0 : ℝ) := by
        exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (Int.toNat_of_nonneg hi0nn)
      rw [hcast]
      exact hfl2.le
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
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast, hteq]
      nlinarith
    · have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
        have : (1 : ℕ) ≤ N := hN
        push_cast [Nat.cast_sub this]
        ring
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
  have huv : v ≤ u := by
    rw [hu, hv]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab)
    (by linarith : (0:ℝ) ≤ u + v - (a + b))]

/-- The Jacobian oscillates no more than the derivative. -/
private lemma abs_jac_sub_le {f : E2 → ℝ} {x y : E2} {ε : ℝ}
    (h : ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ ε) : |jac f x - jac f y| ≤ ε := by
  unfold jac
  calc |Real.sqrt (1 + ‖fderiv ℝ f x‖ ^ 2) - Real.sqrt (1 + ‖fderiv ℝ f y‖ ^ 2)|
      ≤ |‖fderiv ℝ f x‖ - ‖fderiv ℝ f y‖| :=
        sqrt_one_add_sq_sub_le (norm_nonneg _) (norm_nonneg _)
    _ ≤ ‖fderiv ℝ f x - fderiv ℝ f y‖ := abs_norm_sub_norm_le _ _
    _ ≤ ε := h

/-- Splitting a set-lintegral along a finite tiling by squares whose
open interiors are pairwise disjoint. -/
private lemma lintegral_grid_split {ι : Type*} [Fintype ι] {R : Set E2}
    (c : ι → E2) (t : ι → ℝ) (ht : ∀ p, 0 < t p)
    (hdisj : Pairwise fun p q =>
      openSquare (c p) (t p) ∩ openSquare (c q) (t q) = ∅)
    (hcover : (⋃ p, closedSquare (c p) (t p)) = R) (g : E2 → ℝ≥0∞) :
    ∫⁻ z in R, g z = ∑ p, ∫⁻ z in closedSquare (c p) (t p), g z := by
  have hfr : ∀ p, volume (closedSquare (c p) (t p)
      \ interior (closedSquare (c p) (t p))) = 0 :=
    fun p => volume_frontier_closedSquare _ (ht p).le
  have hae : ∀ p, (closedSquare (c p) (t p) : Set E2)
      =ᵐ[volume] interior (closedSquare (c p) (t p)) := by
    intro p
    rw [MeasureTheory.ae_eq_set]
    exact ⟨hfr p, by
      rw [Set.diff_eq_empty.mpr interior_subset]
      exact measure_empty⟩
  have hdisj' : Pairwise (Function.onFun Disjoint
      fun p => interior (closedSquare (c p) (t p))) := by
    intro p q hpq
    apply Set.disjoint_iff_inter_eq_empty.mpr
    apply Set.eq_empty_of_subset_empty
    rw [← hdisj hpq]
    exact Set.inter_subset_inter (interior_closedSquare_subset _ (ht p))
      (interior_closedSquare_subset _ (ht q))
  have hRae : (R : Set E2) =ᵐ[volume] ⋃ p, interior (closedSquare (c p) (t p)) := by
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

/-- The center of a closed square belongs to it. -/
private lemma center_mem_closedSquare (c : E2) {h : ℝ} (hh : 0 ≤ h) :
    c ∈ closedSquare c h := by
  intro l
  rw [sub_self, abs_zero]
  exact div_nonneg hh (by norm_num)

/-- The `N × N` grid of closed subcells of `closedSquare z₀ s` (side
`s/N`): the cells sit inside the square, tile it, and have pairwise
disjoint interiors (paper Thm 8.2, the grid construction). -/
private lemma exists_grid (z₀ : E2) {s : ℝ} (hs : 0 < s) {N : ℕ}
    (hNpos : 0 < N) :
    ∃ ctr : Fin N × Fin N → E2,
      (∀ p, closedSquare (ctr p) (s / N) ⊆ closedSquare z₀ s) ∧
      (⋃ p : Fin N × Fin N, closedSquare (ctr p) (s / N)) = closedSquare z₀ s ∧
      Pairwise fun p q : Fin N × Fin N =>
        openSquare (ctr p) (s / N) ∩ openSquare (ctr q) (s / N) = ∅ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set h := s / N with hh
  have hhpos : 0 < h := by rw [hh]; positivity
  have hNh : (N : ℝ) * h = s := by rw [hh]; field_simp
  set a0 := z₀ 0 - s / 2 with ha0
  set a1 := z₀ 1 - s / 2 with ha1
  set ctr : Fin N × Fin N → E2 := fun p =>
    WithLp.toLp 2 ![a0 + ((p.1 : ℝ) + 1 / 2) * h, a1 + ((p.2 : ℝ) + 1 / 2) * h]
    with hctr
  have hctr0 : ∀ p, (ctr p) 0 = a0 + ((p.1 : ℝ) + 1 / 2) * h := fun p => rfl
  have hctr1 : ∀ p, (ctr p) 1 = a1 + ((p.2 : ℝ) + 1 / 2) * h := fun p => rfl
  have hmemQ : ∀ (p : Fin N × Fin N) (x : E2), x ∈ closedSquare (ctr p) h ↔
      (a0 + (p.1 : ℝ) * h ≤ x 0 ∧ x 0 ≤ a0 + ((p.1 : ℝ) + 1) * h) ∧
      (a1 + (p.2 : ℝ) * h ≤ x 1 ∧ x 1 ≤ a1 + ((p.2 : ℝ) + 1) * h) := by
    intro p x
    rw [mem_closedSquare_iff, hctr0, hctr1]
    constructor
    · rintro ⟨⟨u1, u2⟩, u3, u4⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rintro ⟨⟨u1, u2⟩, u3, u4⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hmemR : ∀ x : E2, x ∈ closedSquare z₀ s ↔
      (a0 ≤ x 0 ∧ x 0 ≤ a0 + s) ∧ (a1 ≤ x 1 ∧ x 1 ≤ a1 + s) := by
    intro x
    rw [mem_closedSquare_iff, ha0, ha1]
    constructor
    · rintro ⟨⟨u1, u2⟩, u3, u4⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rintro ⟨⟨u1, u2⟩, u3, u4⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hQR : ∀ p : Fin N × Fin N, closedSquare (ctr p) h ⊆ closedSquare z₀ s := by
    intro p x hx
    rw [hmemQ] at hx
    rw [hmemR]
    have hp1 : (p.1 : ℝ) + 1 ≤ N := by exact_mod_cast p.1.is_lt
    have hp2 : (p.2 : ℝ) + 1 ≤ N := by exact_mod_cast p.2.is_lt
    have hm1 : (0 : ℝ) ≤ (p.1 : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hhpos.le
    have hm2 : (0 : ℝ) ≤ (p.2 : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hhpos.le
    have hm3 : ((p.1 : ℝ) + 1) * h ≤ (N : ℝ) * h :=
      mul_le_mul_of_nonneg_right hp1 hhpos.le
    have hm4 : ((p.2 : ℝ) + 1) * h ≤ (N : ℝ) * h :=
      mul_le_mul_of_nonneg_right hp2 hhpos.le
    exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2, hNh.le, hNh.ge]⟩,
      by linarith [hx.2.1], by linarith [hx.2.2, hNh.le, hNh.ge]⟩
  have hcover : (⋃ p : Fin N × Fin N, closedSquare (ctr p) h) = closedSquare z₀ s := by
    apply Set.Subset.antisymm (Set.iUnion_subset hQR)
    intro x hx
    rw [hmemR] at hx
    obtain ⟨i, hiN, hi1, hi2⟩ := exists_grid_index hhpos hNpos
      (by linarith [hx.1.1] : 0 ≤ x 0 - a0)
      (by rw [hNh]; linarith [hx.1.2] : x 0 - a0 ≤ (N : ℝ) * h)
    obtain ⟨j, hjN, hj1, hj2⟩ := exists_grid_index hhpos hNpos
      (by linarith [hx.2.1] : 0 ≤ x 1 - a1)
      (by rw [hNh]; linarith [hx.2.2] : x 1 - a1 ≤ (N : ℝ) * h)
    refine Set.mem_iUnion.mpr ⟨(⟨i, hiN⟩, ⟨j, hjN⟩), ?_⟩
    rw [hmemQ]
    constructor
    · constructor
      · show a0 + ((⟨i, hiN⟩ : Fin N) : ℝ) * h ≤ x 0
        linarith
      · show x 0 ≤ a0 + (((⟨i, hiN⟩ : Fin N) : ℝ) + 1) * h
        linarith
    · constructor
      · show a1 + ((⟨j, hjN⟩ : Fin N) : ℝ) * h ≤ x 1
        linarith
      · show x 1 ≤ a1 + (((⟨j, hjN⟩ : Fin N) : ℝ) + 1) * h
        linarith
  have hodisj : Pairwise fun p q : Fin N × Fin N =>
      openSquare (ctr p) h ∩ openSquare (ctr q) h = ∅ := by
    intro p q hpq
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxp, hxq⟩
    rw [mem_openSquare_iff, hctr0, hctr1] at hxp hxq
    have hi : (p.1 : ℕ) = (q.1 : ℕ) := by
      refine grid_index_eq hhpos (a := a0) (t := x 0) ?_ ?_ ?_ ?_
      · linarith [hxp.1.1]
      · linarith [hxp.1.2]
      · linarith [hxq.1.1]
      · linarith [hxq.1.2]
    have hj : (p.2 : ℕ) = (q.2 : ℕ) := by
      refine grid_index_eq hhpos (a := a1) (t := x 1) ?_ ?_ ?_ ?_
      · linarith [hxp.2.1]
      · linarith [hxp.2.2]
      · linarith [hxq.2.1]
      · linarith [hxq.2.2]
    exact hpq (Prod.ext (Fin.ext hi) (Fin.ext hj))
  exact ⟨ctr, hQR, hcover, hodisj⟩

/-- Graphs over two subsquares of `U` with disjoint interiors overlap in
a `μHE[2]`-null set: the overlap lies over the (volume-null) cell
frontiers, and volume-null bases carry area-null graphs. -/
private lemma graph_inter_null {U : Set E2} {f : E2 → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {c₁ c₂ : E2} {h : ℝ} (hh : 0 < h)
    (h₁ : closedSquare c₁ h ⊆ U) (h₂ : closedSquare c₂ h ⊆ U)
    (hdisj : openSquare c₁ h ∩ openSquare c₂ h = ∅) :
    μHE[2] (graph f (closedSquare c₁ h) ∩ graph f (closedSquare c₂ h)) = 0 := by
  have hinter : graph f (closedSquare c₁ h) ∩ graph f (closedSquare c₂ h)
      = graph f (closedSquare c₁ h ∩ closedSquare c₂ h) := by
    rw [graph, graph, graph, ← Set.image_inter graphMap_injective]
  rw [hinter]
  apply le_antisymm ?_ zero_le
  have hsubfr : closedSquare c₁ h ∩ closedSquare c₂ h
      ⊆ (closedSquare c₁ h \ interior (closedSquare c₁ h))
        ∪ (closedSquare c₂ h \ interior (closedSquare c₂ h)) := by
    rintro x ⟨hxp, hxq⟩
    by_cases hx : x ∈ interior (closedSquare c₁ h)
    · refine Or.inr ⟨hxq, fun hx' => ?_⟩
      have hi1 := interior_closedSquare_subset _ hh hx
      have hi2 := interior_closedSquare_subset _ hh hx'
      rw [Set.eq_empty_iff_forall_notMem] at hdisj
      exact hdisj x ⟨hi1, hi2⟩
    · exact Or.inl ⟨hxp, hx⟩
  calc μHE[2] (graph f (closedSquare c₁ h ∩ closedSquare c₂ h))
      ≤ μHE[2] (graph f (closedSquare c₁ h \ interior (closedSquare c₁ h))
        ∪ graph f (closedSquare c₂ h \ interior (closedSquare c₂ h))) := by
        refine measure_mono ?_
        rw [graph, graph, graph, ← Set.image_union]
        exact Set.image_mono hsubfr
    _ ≤ μHE[2] (graph f (closedSquare c₁ h \ interior (closedSquare c₁ h)))
        + μHE[2] (graph f (closedSquare c₂ h \ interior (closedSquare c₂ h))) :=
        measure_union_le _ _
    _ = 0 := by
        rw [graph_null_of_volume_null hU hf (isCompact_closedSquare _ _)
            (convex_closedSquare _ _) h₁ Set.diff_subset
            (volume_frontier_closedSquare _ hh.le),
          graph_null_of_volume_null hU hf (isCompact_closedSquare _ _)
            (convex_closedSquare _ _) h₂ Set.diff_subset
            (volume_frontier_closedSquare _ hh.le), add_zero]

/-- ℝ≥0∞ endgame for the grid squeeze: two-sided `(1 ± ε)²` estimates
with an `ε·V` slack, for all `ε ∈ (0,1)`, force `μ = I` (pass to
`toReal` and let `ε ↓ 0`). -/
private lemma eq_of_grid_estimates {μ I V : ℝ≥0∞} (hIfin : I ≠ ⊤)
    (hVfin : V ≠ ⊤)
    (key : ∀ ε : ℝ, 0 < ε → ε < 1 →
      μ ≤ ENNReal.ofReal ((1 + ε) ^ 2) * (I + ENNReal.ofReal ε * V) ∧
      ENNReal.ofReal ((1 - ε) ^ 2) * I ≤ μ + ENNReal.ofReal ε * V) :
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
  have hbnn : 0 ≤ b := ENNReal.toReal_nonneg
  have hvnn : 0 ≤ v := ENNReal.toReal_nonneg
  have hann : 0 ≤ a := ENNReal.toReal_nonneg
  have hup : ∀ ε : ℝ, 0 < ε → ε < 1 → a ≤ (1 + ε) ^ 2 * (b + ε * v) := by
    intro ε hε0 hε1
    have hk := (key ε hε0 hε1).1
    have hfin2 : ENNReal.ofReal ((1 + ε) ^ 2) * (I + ENNReal.ofReal ε * V) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hIfin,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin⟩)
    have := ENNReal.toReal_mono hfin2 hk
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hIfin
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal hε0.le] at this
    exact this
  have hlow : ∀ ε : ℝ, 0 < ε → ε < 1 → (1 - ε) ^ 2 * b ≤ a + ε * v := by
    intro ε hε0 hε1
    have hk := (key ε hε0 hε1).2
    have hfin2 : μ + ENNReal.ofReal ε * V ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hμfin,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin⟩
    have := ENNReal.toReal_mono hfin2 hk
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_add hμfin
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hε0.le] at this
    exact this
  have hab : a ≤ b := by
    apply le_of_forall_pos_le_add'
    intro η hη
    set ε := min (1 / 2) (η / (3 * b + 4 * v + 1)) with hε
    have hden : (0 : ℝ) < 3 * b + 4 * v + 1 := by linarith
    have hεpos : 0 < ε := lt_min (by norm_num) (by positivity)
    have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
    have hεlt1 : ε < 1 := lt_of_le_of_lt hεhalf (by norm_num)
    have hεb : ε * (3 * b + 4 * v + 1) ≤ η :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    have hval := hup ε hεpos hεlt1
    nlinarith [mul_le_mul_of_nonneg_left hεhalf hεpos.le,
      mul_nonneg hεpos.le hbnn, mul_nonneg hεpos.le hvnn,
      mul_nonneg (mul_nonneg hεpos.le hεpos.le) hbnn,
      mul_nonneg (mul_nonneg hεpos.le hεpos.le) hvnn,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεhalf hεpos.le) hvnn,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεhalf hεpos.le) hbnn,
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hεhalf hεpos.le) (mul_nonneg hεpos.le hvnn)]
  have hba : b ≤ a := by
    apply le_of_forall_pos_le_add'
    intro η hη
    set ε := min (1 / 2) (η / (2 * b + v + 1)) with hε
    have hden : (0 : ℝ) < 2 * b + v + 1 := by linarith
    have hεpos : 0 < ε := lt_min (by norm_num) (by positivity)
    have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
    have hεlt1 : ε < 1 := lt_of_le_of_lt hεhalf (by norm_num)
    have hεb : ε * (2 * b + v + 1) ≤ η :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    have hval := hlow ε hεpos hεlt1
    nlinarith [mul_nonneg hεpos.le hbnn, mul_nonneg hεpos.le hvnn,
      mul_nonneg (mul_nonneg hεpos.le hεpos.le) hbnn,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεhalf hεpos.le) hbnn]
  have hfinal : a = b := le_antisymm hab hba
  have h1 : μ ≤ I := (ENNReal.toReal_le_toReal hμfin hIfin).mp (le_of_eq hfinal)
  have h2 : I ≤ μ := (ENNReal.toReal_le_toReal hIfin hμfin).mp (le_of_eq hfinal.symm)
  exact le_antisymm h1 h2

/-- The two-sided grid estimate at oscillation scale `ε` (the heart of
paper Thm 8.2): gridding at a scale realizing gradient-oscillation `ε`
and applying `local_area_estimate` per cell squeezes the graph area
between `(1 ± ε)²` multiples of the Riemann sums, which in turn sit
within `ε·V` of the integral. -/
private lemma square_grid_estimate {U : Set E2} {f : E2 → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (z₀ : E2) {s : ℝ} (hs : 0 < s)
    (hsub : closedSquare z₀ s ⊆ U) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    μHE[2] (graph f (closedSquare z₀ s))
      ≤ ENNReal.ofReal ((1 + ε) ^ 2)
        * ((∫⁻ z in closedSquare z₀ s, ENNReal.ofReal (jac f z))
          + ENNReal.ofReal ε * volume (closedSquare z₀ s)) ∧
    ENNReal.ofReal ((1 - ε) ^ 2)
        * ∫⁻ z in closedSquare z₀ s, ENNReal.ofReal (jac f z)
      ≤ μHE[2] (graph f (closedSquare z₀ s))
        + ENNReal.ofReal ε * volume (closedSquare z₀ s) := by
  set R := closedSquare z₀ s with hRdef
  set I := ∫⁻ z in R, ENNReal.ofReal (jac f z) with hI
  set μ := μHE[2] (graph f R) with hμ
  set V := volume R with hV
  have hRcomp : IsCompact R := isCompact_closedSquare z₀ s
  -- Scale from uniform continuity of the derivative on `R`.
  have hcontD : ContinuousOn (fderiv ℝ f) R :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hsub
  have hucD := hRcomp.uniformContinuousOn_of_continuous hcontD
  rw [Metric.uniformContinuousOn_iff] at hucD
  obtain ⟨δ, hδ, hδspec⟩ := hucD ε hε0
  -- Grid size.
  obtain ⟨N, hN⟩ := exists_nat_gt (s * Real.sqrt 2 / δ)
  have hNpos : 0 < N := by
    by_contra hcon
    have hN0 : N = 0 := by omega
    rw [hN0] at hN
    norm_num at hN
    have : (0 : ℝ) < s * Real.sqrt 2 / δ := by positivity
    linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  -- The grid.
  obtain ⟨ctr, hQR, hcover, hodisj⟩ := exists_grid z₀ hs hNpos
  rw [← hRdef] at hcover
  set h := s / N with hh
  have hhpos : 0 < h := by rw [hh]; positivity
  have hctrQ : ∀ p : Fin N × Fin N, ctr p ∈ closedSquare (ctr p) h :=
    fun p => center_mem_closedSquare _ hhpos.le
  -- Gradient oscillation on each cell.
  have hgrad : ∀ p : Fin N × Fin N, ∀ x ∈ closedSquare (ctr p) h,
      ‖fderiv ℝ f x - fderiv ℝ f (ctr p)‖ ≤ ε := by
    intro p x hx
    have hd : dist x (ctr p) ≤ h * Real.sqrt 2 / 2 :=
      Metric.mem_closedBall.mp (closedSquare_subset_closedBall (ctr p) hhpos.le hx)
    have hNδ : s * Real.sqrt 2 < N * δ := by
      rw [div_lt_iff₀ hδ] at hN
      exact hN
    have hdlt : dist x (ctr p) < δ := by
      apply lt_of_le_of_lt hd
      rw [hh]
      rw [div_mul_eq_mul_div, div_div]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hNR hδ]
    have := hδspec x (hQR p hx) (ctr p) (hQR p (hctrQ p)) hdlt
    rw [dist_eq_norm] at this
    exact this.le
  -- Per-cell area estimates and Jacobian oscillation.
  have hcell := fun p : Fin N × Fin N =>
    local_area_estimate hU hf (convex_closedSquare _ _) ((hQR p).trans hsub)
      (hctrQ p) ⟨hε0, hε1⟩ (hgrad p) (closedSquare (ctr p) h) subset_rfl
  have hJosc : ∀ p : Fin N × Fin N, ∀ x ∈ closedSquare (ctr p) h,
      |jac f x - jac f (ctr p)| ≤ ε :=
    fun p x hx => abs_jac_sub_le (hgrad p x hx)
  -- Integral splitting along the grid.
  have hsplit : ∀ g : E2 → ℝ≥0∞,
      ∫⁻ z in R, g z = ∑ p : Fin N × Fin N, ∫⁻ z in closedSquare (ctr p) h, g z :=
    fun g => lintegral_grid_split ctr (fun _ => h) (fun _ => hhpos) hodisj hcover g
  have hVsum : V = ∑ p : Fin N × Fin N, volume (closedSquare (ctr p) h) := by
    have h1 := hsplit fun _ => 1
    rw [hV]
    simpa [setLIntegral_one] using h1
  have hIsum : I = ∑ p : Fin N × Fin N,
      ∫⁻ z in closedSquare (ctr p) h, ENNReal.ofReal (jac f z) := by
    rw [hI]; exact hsplit _
  -- The Riemann sum.
  set S := ∑ p : Fin N × Fin N,
    ENNReal.ofReal (jac f (ctr p)) * volume (closedSquare (ctr p) h) with hS
  -- S is squeezed between I ± εV.
  have hSle : S ≤ I + ENNReal.ofReal ε * V := by
    have hstep : ∀ p : Fin N × Fin N,
        ENNReal.ofReal (jac f (ctr p)) * volume (closedSquare (ctr p) h)
          ≤ ∫⁻ z in closedSquare (ctr p) h,
              (ENNReal.ofReal (jac f z) + ENNReal.ofReal ε) := by
      intro p
      rw [← setLIntegral_const]
      refine setLIntegral_mono'
        (isCompact_closedSquare _ _).isClosed.measurableSet fun x hx => ?_
      rw [← ENNReal.ofReal_add (jac_pos x).le hε0.le]
      apply ENNReal.ofReal_le_ofReal
      have := (abs_le.mp (hJosc p x hx)).1
      linarith
    calc S ≤ ∑ p : Fin N × Fin N, ∫⁻ z in closedSquare (ctr p) h,
          (ENNReal.ofReal (jac f z) + ENNReal.ofReal ε) :=
        Finset.sum_le_sum fun p _ => hstep p
      _ = ∫⁻ z in R, (ENNReal.ofReal (jac f z) + ENNReal.ofReal ε) :=
        (hsplit _).symm
      _ = I + ENNReal.ofReal ε * V := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, hI, hV]
  have hIleS : I ≤ S + ENNReal.ofReal ε * V := by
    have hstep : ∀ p : Fin N × Fin N,
        ∫⁻ z in closedSquare (ctr p) h, ENNReal.ofReal (jac f z)
          ≤ ENNReal.ofReal (jac f (ctr p)) * volume (closedSquare (ctr p) h)
            + ENNReal.ofReal ε * volume (closedSquare (ctr p) h) := by
      intro p
      calc ∫⁻ z in closedSquare (ctr p) h, ENNReal.ofReal (jac f z)
          ≤ ∫⁻ _z in closedSquare (ctr p) h,
              (ENNReal.ofReal (jac f (ctr p)) + ENNReal.ofReal ε) := by
            refine setLIntegral_mono'
              (isCompact_closedSquare _ _).isClosed.measurableSet fun x hx => ?_
            rw [← ENNReal.ofReal_add (jac_pos (ctr p)).le hε0.le]
            apply ENNReal.ofReal_le_ofReal
            have := (abs_le.mp (hJosc p x hx)).2
            linarith
        _ = ENNReal.ofReal (jac f (ctr p)) * volume (closedSquare (ctr p) h)
            + ENNReal.ofReal ε * volume (closedSquare (ctr p) h) := by
            rw [setLIntegral_const, add_mul]
    calc I = ∑ p : Fin N × Fin N,
          ∫⁻ z in closedSquare (ctr p) h, ENNReal.ofReal (jac f z) := hIsum
      _ ≤ ∑ p : Fin N × Fin N,
          (ENNReal.ofReal (jac f (ctr p)) * volume (closedSquare (ctr p) h)
            + ENNReal.ofReal ε * volume (closedSquare (ctr p) h)) :=
        Finset.sum_le_sum fun p _ => hstep p
      _ = S + ENNReal.ofReal ε * ∑ p : Fin N × Fin N,
          volume (closedSquare (ctr p) h) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, hS]
      _ = S + ENNReal.ofReal ε * V := by rw [← hVsum]
  -- The graph over `R` decomposes along the cells.
  have hgU : graph f R = ⋃ p : Fin N × Fin N, graph f (closedSquare (ctr p) h) := by
    rw [graph, ← hcover, Set.image_iUnion]
    rfl
  constructor
  · -- Upper bound.
    calc μ = μHE[2] (⋃ p : Fin N × Fin N, graph f (closedSquare (ctr p) h)) := by
          rw [hμ, hgU]
      _ ≤ ∑ p : Fin N × Fin N, μHE[2] (graph f (closedSquare (ctr p) h)) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ p : Fin N × Fin N, ENNReal.ofReal ((1 + ε) ^ 2 * jac f (ctr p))
            * volume (closedSquare (ctr p) h) :=
          Finset.sum_le_sum fun p _ => (hcell p).2
      _ = ENNReal.ofReal ((1 + ε) ^ 2) * S := by
          rw [hS, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ ENNReal.ofReal ((1 + ε) ^ 2) * (I + ENNReal.ofReal ε * V) :=
          mul_le_mul_right hSle _
  · -- Lower bound: a.e.-additivity of the graph pieces.
    have hAE : ((Finset.univ : Finset (Fin N × Fin N)) : Set (Fin N × Fin N)).Pairwise
        (Function.onFun (AEDisjoint μHE[2])
          fun p => graph f (closedSquare (ctr p) h)) := by
      intro p _ q _ hpq
      exact graph_inter_null hU hf hhpos ((hQR p).trans hsub)
        ((hQR q).trans hsub) (hodisj hpq)
    have hmeasF : ∀ p ∈ (Finset.univ : Finset (Fin N × Fin N)),
        NullMeasurableSet (graph f (closedSquare (ctr p) h)) μHE[2] := by
      intro p _
      exact (((isCompact_closedSquare (ctr p) h).image_of_continuousOn
        ((continuousOn_graphMap hf.continuousOn).mono
          ((hQR p).trans hsub))).measurableSet).nullMeasurableSet
    have hμsum : ∑ p : Fin N × Fin N,
        ENNReal.ofReal ((1 - ε) ^ 2 * jac f (ctr p))
          * volume (closedSquare (ctr p) h) ≤ μ := by
      calc ∑ p : Fin N × Fin N, ENNReal.ofReal ((1 - ε) ^ 2 * jac f (ctr p))
            * volume (closedSquare (ctr p) h)
          ≤ ∑ p : Fin N × Fin N, μHE[2] (graph f (closedSquare (ctr p) h)) :=
            Finset.sum_le_sum fun p _ => (hcell p).1
        _ = μHE[2] (⋃ p ∈ (Finset.univ : Finset (Fin N × Fin N)),
              graph f (closedSquare (ctr p) h)) :=
            (measure_biUnion_finset₀ hAE hmeasF).symm
        _ = μ := by
            rw [hμ, hgU]
            congr 1
            simp
    calc ENNReal.ofReal ((1 - ε) ^ 2) * I
        ≤ ENNReal.ofReal ((1 - ε) ^ 2) * (S + ENNReal.ofReal ε * V) :=
          mul_le_mul_right hIleS _
      _ = ENNReal.ofReal ((1 - ε) ^ 2) * S
          + ENNReal.ofReal ((1 - ε) ^ 2) * (ENNReal.ofReal ε * V) := mul_add _ _ _
      _ ≤ μ + ENNReal.ofReal ε * V := by
          refine add_le_add ?_ ?_
          · calc ENNReal.ofReal ((1 - ε) ^ 2) * S
                = ∑ p : Fin N × Fin N,
                  ENNReal.ofReal ((1 - ε) ^ 2 * jac f (ctr p))
                    * volume (closedSquare (ctr p) h) := by
                  rw [hS, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun p _ => ?_
                  rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
              _ ≤ μ := hμsum
          · calc ENNReal.ofReal ((1 - ε) ^ 2) * (ENNReal.ofReal ε * V)
                ≤ 1 * (ENNReal.ofReal ε * V) :=
                  mul_le_mul' (ENNReal.ofReal_le_one.mpr (by nlinarith)) le_rfl
              _ = ENNReal.ofReal ε * V := one_mul _

/-- **Paper Theorem 8.2** (area formula over a closed square): grid the
square at a scale realizing gradient-oscillation `ε`, apply
`local_area_estimate` per cell, compare Riemann sums with the integral,
and let the grid refine and `ε ↓ 0`. -/
theorem square_area {U : Set E2} {f : E2 → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (z₀ : E2) {s : ℝ} (hs : 0 < s)
    (hsub : closedSquare z₀ s ⊆ U) :
    μHE[2] (graph f (closedSquare z₀ s))
      = ∫⁻ z in closedSquare z₀ s, ENNReal.ofReal (jac f z) := by
  have hVfin : volume (closedSquare z₀ s) ≠ ⊤ := by
    rw [volume_closedSquare z₀ hs.le]
    exact ENNReal.ofReal_ne_top
  have hRcomp : IsCompact (closedSquare z₀ s) := isCompact_closedSquare z₀ s
  -- `J` is bounded on the compact square, so the integral is finite.
  obtain ⟨C, hC⟩ := hRcomp.exists_bound_of_continuousOn
    ((continuousOn_jac hU hf).mono hsub)
  have hIfin : (∫⁻ z in closedSquare z₀ s, ENNReal.ofReal (jac f z)) ≠ ⊤ := by
    have hle : (∫⁻ z in closedSquare z₀ s, ENNReal.ofReal (jac f z))
        ≤ ENNReal.ofReal C * volume (closedSquare z₀ s) := by
      rw [← setLIntegral_const]
      refine setLIntegral_mono' hRcomp.isClosed.measurableSet fun x hx => ?_
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC x hx))
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin) hle
  exact eq_of_grid_estimates hIfin hVfin fun ε hε0 hε1 =>
    square_grid_estimate hU hf z₀ hs hsub hε0 hε1

/-
# The main theorem (paper Thm 1.1 / §9) and the user-facing API

    μHE[2] (Γ_f) = ∫_U √(1 + |∇f|²)

with `μHE[2]` Mathlib's Euclidean-normalized 2-dimensional Hausdorff
measure — literally the paper's ℋ² (see `GraphArea.Normalization` for
the identification with the raw gauge measure `μH[2]`).

Both sides live in `[0,∞]` and are finite or infinite together — ℝ≥0∞
arithmetic handles this automatically, a genuine advantage of the Lean
setting over the paper's case analysis.

The second half of the file is "apply" API: transport along isometries
and a splitting lemma, designed so that computing the area of a concrete
surface (e.g. the sphere, `GraphArea.Sphere`) is a matter of exhibiting
it as isometric images of graphs up to a null set.
-/




/-- **Paper Theorem 1.1** (the main theorem).

Proof plan (paper §9): decompose `U` by `dyadic_decomposition`
(σ = 1), so `Γ_f = ⋃ₙ Φ(Qₙ)`.

* UPPER: `measure_iUnion_le` + `square_area` on each `Qₙ`, then
  `Σₙ ∫_{Qₙ} J = ∫_U J`: interiors are pairwise disjoint, boundaries
  and the leftover `U \ ⋃ₙ Qₙ°` are volume-null (finitely many
  segments per square), and `lintegral` over null sets vanishes.  All
  in ℝ≥0∞: no finiteness hypotheses, `tsum` handles divergence.
* LOWER: for each `N`,
  `μHE[2](Γ_f) ≥ μHE[2](⋃_{n<N} Φ(Qₙ)) = Σ_{n<N} μHE[2](Φ(Qₙ))`
  — the pieces are compact hence measurable, pairwise overlaps are
  graphs over shared boundary segments, null by `graph_segment_null`;
  no shrinking, no `θ`, none of the paper's §9 truncation bookkeeping.
  Then `square_area` on each piece and monotone convergence of the
  partial sums (`ENNReal.tendsto_nat_tsum`). -/
theorem area_formula {U : Set E2} {f : E2 → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) :
    μHE[2] (graph f U) = ∫⁻ z in U, ENNReal.ofReal (jac f z) := by
  rcases Set.eq_empty_or_nonempty U with rfl | hne
  · simp [graph]
  obtain ⟨z, s, hprop, hdisj, hunion⟩ := dyadic_decomposition hU hne one_pos
  set Q : ℕ → Set E2 := fun n => closedSquare (z n) (s n) with hQdef
  have hQU : ∀ n, Q n ⊆ U := fun n => (hprop n).2.2
  have hQs : ∀ n, 0 < s n := fun n => (hprop n).1
  have hcompact : ∀ n, IsCompact (Q n) := fun n => isCompact_closedSquare _ _
  have hconvex : ∀ n, Convex ℝ (Q n) := fun n => convex_closedSquare _ _
  have hsq : ∀ n, μHE[2] (graph f (Q n)) = ∫⁻ w in Q n, ENNReal.ofReal (jac f w) :=
    fun n => square_area hU hf (z n) (hQs n) (hQU n)
  -- The graph decomposes along the squares.
  have hgraph : graph f U = ⋃ n, graph f (Q n) := by
    rw [graph, ← hunion, Set.image_iUnion]
    rfl
  -- Frontiers are volume-null, so squares agree a.e. with their
  -- (pairwise disjoint) interiors.
  have hfr_null : ∀ n, volume (Q n \ interior (Q n)) = 0 := fun n =>
    volume_frontier_closedSquare _ (hQs n).le
  have hae : ∀ n, (Q n : Set E2) =ᵐ[volume] interior (Q n) := by
    intro n
    rw [MeasureTheory.ae_eq_set]
    exact ⟨hfr_null n, by
      rw [Set.diff_eq_empty.mpr interior_subset]
      exact measure_empty⟩
  have hdisj' : Pairwise (Function.onFun Disjoint fun n => interior (Q n)) :=
    fun m n hmn => Set.disjoint_iff_inter_eq_empty.mpr (hdisj hmn)
  -- The integral over `U` is the sum of the integrals over the squares.
  have hUae : (U : Set E2) =ᵐ[volume] ⋃ n, interior (Q n) := by
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
  have hupper : μHE[2] (graph f U) ≤ ∫⁻ w in U, ENNReal.ofReal (jac f w) := by
    rw [hgraph, htotal]
    calc μHE[2] (⋃ n, graph f (Q n)) ≤ ∑' n, μHE[2] (graph f (Q n)) :=
        measure_iUnion_le _
      _ = ∑' n, ∫⁻ w in Q n, ENNReal.ofReal (jac f w) := tsum_congr hsq
  -- LOWER BOUND: finite pieces are almost disjoint (their overlaps are
  -- graphs over the null frontiers), so additivity applies.
  have hlower : ∫⁻ w in U, ENNReal.ofReal (jac f w) ≤ μHE[2] (graph f U) := by
    rw [htotal, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    have hAE : (F : Set ℕ).Pairwise (Function.onFun (AEDisjoint μHE[2])
        fun n => graph f (Q n)) := by
      intro m _ n _ hmn
      show μHE[2] (graph f (Q m) ∩ graph f (Q n)) = 0
      have hinter : graph f (Q m) ∩ graph f (Q n) = graph f (Q m ∩ Q n) := by
        rw [graph, graph, graph, ← Set.image_inter graphMap_injective]
      rw [hinter]
      apply le_antisymm ?_ zero_le
      -- The overlap lies in the two frontiers.
      have hsub : Q m ∩ Q n ⊆ (Q m \ interior (Q m)) ∪ (Q n \ interior (Q n)) := by
        rintro x ⟨hxm, hxn⟩
        by_cases hx : x ∈ interior (Q m)
        · refine Or.inr ⟨hxn, fun hx' => ?_⟩
          have hmem : x ∈ interior (Q m) ∩ interior (Q n) := ⟨hx, hx'⟩
          rw [hdisj hmn] at hmem
          exact hmem
        · exact Or.inl ⟨hxm, hx⟩
      calc μHE[2] (graph f (Q m ∩ Q n))
          ≤ μHE[2] (graph f (Q m \ interior (Q m)) ∪ graph f (Q n \ interior (Q n))) := by
            refine measure_mono ?_
            rw [graph, graph, graph, ← Set.image_union]
            exact Set.image_mono hsub
        _ ≤ μHE[2] (graph f (Q m \ interior (Q m)))
              + μHE[2] (graph f (Q n \ interior (Q n))) := measure_union_le _ _
        _ = 0 := by
            rw [graph_null_of_volume_null hU hf (hcompact m) (hconvex m) (hQU m)
                Set.diff_subset (hfr_null m),
              graph_null_of_volume_null hU hf (hcompact n) (hconvex n) (hQU n)
                Set.diff_subset (hfr_null n), add_zero]
    have hmeasF : ∀ n ∈ F, NullMeasurableSet (graph f (Q n)) μHE[2] := by
      intro n _
      exact (((hcompact n).image_of_continuousOn
        ((continuousOn_graphMap hf.continuousOn).mono (hQU n))).measurableSet).nullMeasurableSet
    calc ∑ n ∈ F, ∫⁻ w in Q n, ENNReal.ofReal (jac f w)
        = ∑ n ∈ F, μHE[2] (graph f (Q n)) :=
          Finset.sum_congr rfl fun n _ => (hsq n).symm
      _ = μHE[2] (⋃ n ∈ F, graph f (Q n)) :=
          (measure_biUnion_finset₀ hAE hmeasF).symm
      _ ≤ μHE[2] (graph f U) := by
          refine measure_mono (Set.iUnion₂_subset fun n _ => ?_)
          exact Set.image_mono (hQU n)
  exact le_antisymm hupper hlower

/-! ## Apply functionality

Hausdorff measure is intrinsic to the metric (paper Prop 2.2(iii) +
Cor 2.4), so the area formula computes the measure of *any* isometric
copy of a graph, sitting in *any* metric space.  These wrappers are
what one actually uses on a concrete surface. -/

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The area formula for an isometric copy of a graph: if `ι` is an
isometry (e.g. the inclusion of a rotated/translated plane patch, or
the identification `E3 ≃ᵢ EuclideanSpace ℝ (Fin 3)`), then the surface
`ι '' Γ_f` has the same area integral.  This is the workhorse for
concrete surfaces. -/
theorem area_formula_of_isometry {U : Set E2} {f : E2 → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {ι : E3 → X} (hι : Isometry ι) :
    μHE[2] (ι '' graph f U) = ∫⁻ z in U, ENNReal.ofReal (jac f z) := by
  rw [hι.euclideanHausdorffMeasure_image, area_formula hU hf]

omit [EMetricSpace X] [BorelSpace X] in
/-- Splitting a surface into two graph patches and a null seam:
`μ(A ∪ B ∪ N) = μ A + μ B` when `A`, `B` are disjoint, `B` is
measurable and `N` is null.  (For the sphere: two open hemispheres and
the equator.) -/
theorem measure_split_two {μ : Measure X} {A B N : Set X}
    (hAB : Disjoint A B) (hB : MeasurableSet B) (hN : μ N = 0) :
    μ (A ∪ B ∪ N) = μ A + μ B := by
  have h1 : μ (A ∪ B ∪ N) = μ (A ∪ B) := by
    apply le_antisymm
    · calc μ (A ∪ B ∪ N) ≤ μ (A ∪ B) + μ N := measure_union_le _ _
        _ = μ (A ∪ B) := by rw [hN, add_zero]
    · exact measure_mono Set.subset_union_left
  rw [h1, measure_union hAB hB]

/-
# Normalization: identifying μHE[2], the paper's ℋ², and μH[2]
(paper §4 and §5)

Mathlib's `μHE[2]` is *defined* as `c • μH[2]` for the abstract Haar
scalar `c = addHaarScalarFactor volume μH[2]` on the model plane; the
concrete value of the constant is an open `proof_wanted` in Mathlib
(`MeasureTheory.Measure.addHaarScalarFactor_hausdorffMeasure_eq`).
This file states exactly the missing content: `c = π/4`, equivalently
paper Theorem 5.1 in the raw gauge, equivalently the isodiametric
inequality plus greedy disk-filling.

None of this is needed for `GraphArea.area_formula`; it is needed only
to restate results in terms of the unnormalized gauge measure `μH[2]`
(where every flat identity picks up `4/π`).  Everything here is now
fully proven: the isodiametric inequality via a lean Steiner
symmetrization (no convexity needed), and the constant via Besicovitch
coverings — resolving Mathlib's `proof_wanted` in dimension 2.
-/




/-! **Paper Theorem 4.1** (isodiametric inequality, Bieberbach):
`m(E) ≤ π (diam E / 2)²`.  Stated in `ℝ≥0∞` so that unbounded sets
(`diam = ∞`) are handled uniformly.

Proof plan (paper §4): reduce to the compact convex set
`K = conv (closure E)` (`convexHull`, `EMetric.diam_convexHull` — check
availability; closure/hull do not increase the diameter, Lem 4.2);
Steiner-symmetrize vertically then horizontally (Def 4.4, Lem 4.5:
volume preserved via Tonelli on slices, diameter non-increasing via the
two-point estimate, convexity/compactness preserved); a set symmetric
about both axes is centrally symmetric, hence contained in
`closedBall 0 (diam/2)`; finish with `EuclideanSpace.volume_ball`.
Steiner symmetrization is not in Mathlib — this is the deep part. -/
/-! ### Steiner symmetrization, formalized without convexity

The classical proof symmetrizes a *compact convex* set and tracks
convexity/semicontinuity through the construction.  Here we use a
leaner scheme: the symmetrized set is *defined* by witness pairs, so it
is a continuous image of a compact parameter set (compactness and
measurability are free), volumes are compared by a slicewise
*inequality* (`≤` is all that is needed — no interval structure), and
the diameter bound uses the witnesses instead of attained extrema. -/

/-- Points of the plane from coordinates. -/
private def mk2 (x y : ℝ) : E2 := WithLp.toLp 2 ![x, y]

private lemma mk2_zero (x y : ℝ) : (mk2 x y) 0 = x := rfl
private lemma mk2_one (x y : ℝ) : (mk2 x y) 1 = y := rfl

private lemma mk2_eta (p : E2) : mk2 (p 0) (p 1) = p := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

private lemma mk2_dist (a b c d : ℝ) :
    dist (mk2 a b) (mk2 c d) = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  have h0 : dist ((mk2 a b) 0) ((mk2 c d) 0) ^ 2 = (a - c) ^ 2 := by
    rw [show ((mk2 a b) 0) = a from rfl, show ((mk2 c d) 0) = c from rfl,
      Real.dist_eq, sq_abs]
  have h1 : dist ((mk2 a b) 1) ((mk2 c d) 1) ^ 2 = (b - d) ^ 2 := by
    rw [show ((mk2 a b) 1) = b from rfl, show ((mk2 c d) 1) = d from rfl,
      Real.dist_eq, sq_abs]
  rw [h0, h1]

private lemma mk2_continuous :
    Continuous fun v : (E2 × E2) × ℝ => mk2 ((v.1.1) 0) v.2 := by
  have heq : ∀ (x y : ℝ), mk2 x y
      = x • EuclideanSpace.single 0 (1:ℝ) + y • EuclideanSpace.single 1 (1:ℝ) := by
    intro x y
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [mk2]
  simp only [heq]
  have hc : Continuous fun v : (E2 × E2) × ℝ => (v.1.1) 0 := by
    exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous).comp
      (continuous_fst.comp continuous_fst)
  fun_prop

private lemma abs_coord_le_norm (p : E2) (i : Fin 2) : |p i| ≤ ‖p‖ := by
  have h := EuclideanSpace.real_norm_sq_eq p
  have h0 : p i ^ 2 ≤ ‖p‖ ^ 2 := by
    rw [h]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
  calc |p i| = Real.sqrt (p i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖p‖ ^ 2) := Real.sqrt_le_sqrt h0
    _ = ‖p‖ := Real.sqrt_sq (norm_nonneg _)

/-- Steiner symmetrization in the vertical direction, defined by
witness pairs: `(x, t)` belongs to the symmetrization iff `|t|` is at
most half the gap between two points of `K` on the vertical through
`x`. -/
private def symmSet (K : Set E2) : Set E2 :=
  {p | ∃ u ∈ K, ∃ w ∈ K, u 0 = p 0 ∧ w 0 = p 0 ∧ |p 1| ≤ (u 1 - w 1) / 2}

/-- The symmetrization of a compact set is compact. -/
private lemma symmSet_isCompact {K : Set E2} (hK : IsCompact K) :
    IsCompact (symmSet K) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  set A : Set ((E2 × E2) × ℝ) :=
    {v | v.1.1 ∈ K ∧ v.1.2 ∈ K ∧ v.1.1 0 = v.1.2 0
      ∧ |v.2| ≤ (v.1.1 1 - v.1.2 1) / 2} with hA
  -- coordinate maps are continuous
  have hc0 : Continuous fun v : (E2 × E2) × ℝ => (v.1.1) 0 :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous).comp
      (continuous_fst.comp continuous_fst)
  have hc0' : Continuous fun v : (E2 × E2) × ℝ => (v.1.2) 0 :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous).comp
      (continuous_snd.comp continuous_fst)
  have hc1 : Continuous fun v : (E2 × E2) × ℝ => (v.1.1) 1 :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous).comp
      (continuous_fst.comp continuous_fst)
  have hc1' : Continuous fun v : (E2 × E2) × ℝ => (v.1.2) 1 :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous).comp
      (continuous_snd.comp continuous_fst)
  have hAclosed : IsClosed A := by
    rw [hA, Set.setOf_and, Set.setOf_and, Set.setOf_and]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
    · exact hK.isClosed.preimage (continuous_fst.comp continuous_fst)
    · exact hK.isClosed.preimage (continuous_snd.comp continuous_fst)
    · exact isClosed_eq hc0 hc0'
    · exact isClosed_le (continuous_abs.comp continuous_snd)
        (Continuous.div_const (hc1.sub hc1') 2)
  have hAsub : A ⊆ (K ×ˢ K) ×ˢ Set.Icc (-C) C := by
    rintro ⟨⟨u, w⟩, t⟩ ⟨hu, hw, -, ht⟩
    have h1 := abs_le.mp (abs_coord_le_norm u 1)
    have h2 := abs_le.mp (abs_coord_le_norm w 1)
    have h3 := hC u hu
    have h4 := hC w hw
    have h5 : |t| ≤ C := by
      have h6 := le_abs_self t
      have h7 := neg_abs_le t
      rw [abs_le]
      constructor
      · simp only at ht
        nlinarith [abs_nonneg t]
      · simp only at ht
        nlinarith [abs_nonneg t]
    exact ⟨⟨hu, hw⟩, Set.mem_Icc.mpr (abs_le.mp h5)⟩
  have hAcomp : IsCompact A :=
    IsCompact.of_isClosed_subset ((hK.prod hK).prod isCompact_Icc) hAclosed hAsub
  have himg : symmSet K = (fun v : (E2 × E2) × ℝ => mk2 ((v.1.1) 0) v.2) '' A := by
    ext p
    constructor
    · rintro ⟨u, hu, w, hw, hux, hwx, ht⟩
      refine ⟨((u, w), p 1), ⟨hu, hw, by rw [hux, hwx], ht⟩, ?_⟩
      show mk2 (u 0) (p 1) = p
      rw [hux, mk2_eta]
    · rintro ⟨⟨⟨u, w⟩, t⟩, ⟨hu, hw, heq0, hle⟩, rfl⟩
      exact ⟨u, hu, w, hw, rfl, by rw [← heq0]; rfl, hle⟩
  rw [himg]
  exact hAcomp.image mk2_continuous

/-- The symmetrization does not increase the diameter (paper Lem
4.5(iii), via witness pairs). -/
private lemma symmSet_diam_le {K : Set E2} (hK : IsCompact K) :
    Metric.diam (symmSet K) ≤ Metric.diam K := by
  apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
  rintro p ⟨u, hu, w, hw, hux, hwx, ht⟩ q ⟨u', hu', w', hw', hux', hwx', ht'⟩
  -- `|p₁ - q₁| ≤ (A + B)/2` with `A := u₁ - w'₁`, `B := u'₁ - w₁`.
  have hkey : ∀ (a : E2) (b : E2), a ∈ K → b ∈ K → a 0 = p 0 → b 0 = q 0 →
      |p 1 - q 1| ≤ |a 1 - b 1| → dist p q ≤ Metric.diam K := by
    intro a b ha hb ha0 hb0 hab
    have hd : dist p q ≤ dist a b := by
      rw [← mk2_eta p, ← mk2_eta q, mk2_dist, ← mk2_eta a, ← mk2_eta b, mk2_dist]
      apply Real.sqrt_le_sqrt
      have e0 : (a 0 - b 0) ^ 2 = (p 0 - q 0) ^ 2 := by rw [ha0, hb0]
      have e1 : (p 1 - q 1) ^ 2 ≤ (a 1 - b 1) ^ 2 := by
        have h1 := mul_self_le_mul_self (abs_nonneg (p 1 - q 1)) hab
        nlinarith [sq_abs (p 1 - q 1), sq_abs (a 1 - b 1)]
      linarith
    exact hd.trans (Metric.dist_le_diam_of_mem hK.isBounded ha hb)
  have habs : |p 1 - q 1| ≤ |p 1| + |q 1| := by
    calc |p 1 - q 1| = |p 1 + -(q 1)| := by rw [sub_eq_add_neg]
      _ ≤ |p 1| + |-(q 1)| := abs_add_le _ _
      _ = |p 1| + |q 1| := by rw [abs_neg]
  rcases le_total (u' 1 - w 1) (u 1 - w' 1) with hcase | hcase
  · refine hkey u w' hu hw' hux (by rw [hwx']) ?_
    calc |p 1 - q 1| ≤ u 1 - w' 1 := by linarith
      _ ≤ |u 1 - w' 1| := le_abs_self _
  · refine hkey w u' hw hu' hwx (by rw [hux']) ?_
    calc |p 1 - q 1| ≤ u' 1 - w 1 := by linarith
      _ = |-(u' 1 - w 1)| := by rw [abs_neg, abs_of_nonneg (by linarith [abs_nonneg (p 1 - q 1)])]
      _ = |w 1 - u' 1| := by rw [neg_sub]

/-- The symmetrization does not decrease the volume (paper Lem 4.5(ii),
weakened to an inequality — all that is needed). -/
private lemma symmSet_volume_le {K : Set E2} (hK : IsCompact K) :
    volume K ≤ volume (symmSet K) := by
  classical
  -- Transport to `ℝ × ℝ` and slice.
  set Fm : (ℝ × ℝ) ≃ᵐ E2 :=
    (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.trans
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) with hFmdef
  have hFm : MeasurePreserving Fm volume volume := by
    have h1 : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := ℝ)).symm
        (volume : Measure (ℝ × ℝ)) volume := by
      have h := measurePreserving_finTwoArrow (volume : Measure ℝ)
      rw [← volume_pi, ← volume_eq_prod] at h
      exact h.symm
    exact (PiLp.volume_preserving_toLp (Fin 2)).comp h1
  have hFmapp : ∀ x y : ℝ, (Fm (x, y) : E2) = mk2 x y := fun x y => rfl
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hSm : MeasurableSet (symmSet K) :=
    (symmSet_isCompact hK).isClosed.measurableSet
  rw [← hFm.measure_preimage hKm.nullMeasurableSet,
    ← hFm.measure_preimage hSm.nullMeasurableSet,
    volume_eq_prod, Measure.prod_apply (hFm.measurable hKm),
    Measure.prod_apply (hFm.measurable hSm)]
  apply lintegral_mono
  intro x
  -- vertical slices
  set PK : Set ℝ := {y | mk2 x y ∈ K} with hPK
  set PS : Set ℝ := {y | mk2 x y ∈ symmSet K} with hPS
  show volume (Prod.mk x ⁻¹' (Fm ⁻¹' K)) ≤ volume (Prod.mk x ⁻¹' (Fm ⁻¹' symmSet K))
  have hpre1 : Prod.mk x ⁻¹' (Fm ⁻¹' K) = PK := rfl
  have hpre2 : Prod.mk x ⁻¹' (Fm ⁻¹' symmSet K) = PS := rfl
  rw [hpre1, hpre2]
  rcases Set.eq_empty_or_nonempty PK with hemp | hne
  · rw [hemp]
    simp
  -- the slice is compact
  have hPKcomp : IsCompact PK := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
    have hclosed : IsClosed PK := by
      have hcont : Continuous fun y : ℝ => mk2 x y := by
        have heq : ∀ y : ℝ, mk2 x y
            = x • EuclideanSpace.single 0 (1:ℝ) + y • EuclideanSpace.single 1 (1:ℝ) := by
          intro y
          apply PiLp.ext
          intro i
          fin_cases i <;> simp [mk2]
        simp only [heq]
        fun_prop
      exact hK.isClosed.preimage hcont
    have hbdd : PK ⊆ Set.Icc (-C) C := by
      intro y hy
      have h1 := abs_coord_le_norm (mk2 x y) 1
      rw [mk2_one] at h1
      have h2 := hC _ hy
      exact Set.mem_Icc.mpr (abs_le.mp (h1.trans h2))
    exact IsCompact.of_isClosed_subset isCompact_Icc hclosed hbdd
  have hMmem : sSup PK ∈ PK := hPKcomp.sSup_mem hne
  have hmmem : sInf PK ∈ PK := hPKcomp.sInf_mem hne
  set M := sSup PK
  set m := sInf PK
  have hsub1 : PK ⊆ Set.Icc m M := fun y hy =>
    Set.mem_Icc.mpr ⟨csInf_le hPKcomp.bddBelow hy, le_csSup hPKcomp.bddAbove hy⟩
  have hsub2 : Set.Icc (-((M - m) / 2)) ((M - m) / 2) ⊆ PS := by
    intro t ht
    rw [Set.mem_Icc] at ht
    refine ⟨mk2 x M, hMmem, mk2 x m, hmmem, rfl, rfl, ?_⟩
    rw [mk2_one, mk2_one, mk2_one]
    rw [abs_le]
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  calc volume PK ≤ volume (Set.Icc m M) := measure_mono hsub1
    _ = ENNReal.ofReal (M - m) := Real.volume_Icc
    _ = volume (Set.Icc (-((M - m) / 2)) ((M - m) / 2)) := by
        rw [Real.volume_Icc]
        congr 1
        ring
    _ ≤ volume PS := measure_mono hsub2

/-- The symmetrization is symmetric in the second coordinate. -/
private lemma symmSet_sym1 {K : Set E2} {p : E2} (hp : p ∈ symmSet K) :
    mk2 (p 0) (-(p 1)) ∈ symmSet K := by
  obtain ⟨u, hu, w, hw, hux, hwx, ht⟩ := hp
  exact ⟨u, hu, w, hw, by rw [mk2_zero, hux], by rw [mk2_zero, hwx],
    by rw [mk2_one, abs_neg]; exact ht⟩

/-- The symmetrization preserves symmetry in the first coordinate. -/
private lemma symmSet_preserves_sym0 {K : Set E2}
    (hKsym : ∀ p ∈ K, mk2 (-(p 0)) (p 1) ∈ K) {p : E2} (hp : p ∈ symmSet K) :
    mk2 (-(p 0)) (p 1) ∈ symmSet K := by
  obtain ⟨u, hu, w, hw, hux, hwx, ht⟩ := hp
  refine ⟨mk2 (-(u 0)) (u 1), hKsym u hu, mk2 (-(w 0)) (w 1), hKsym w hw, ?_, ?_, ?_⟩
  · rw [mk2_zero, mk2_zero, hux]
  · rw [mk2_zero, mk2_zero, hwx]
  · rw [mk2_one, mk2_one, mk2_one]
    exact ht

/-- The coordinate swap of the plane. -/
private def swap2 (p : E2) : E2 := mk2 (p 1) (p 0)

private lemma swap2_isometry : Isometry swap2 := by
  apply Isometry.of_dist_eq
  intro p q
  rw [show swap2 p = mk2 (p 1) (p 0) from rfl, show swap2 q = mk2 (q 1) (q 0) from rfl,
    mk2_dist, ← mk2_eta p, ← mk2_eta q, mk2_dist]
  rw [mk2_zero, mk2_one, mk2_zero, mk2_one]
  rw [add_comm]

private lemma swap2_swap2 (p : E2) : swap2 (swap2 p) = p := by
  rw [show swap2 p = mk2 (p 1) (p 0) from rfl,
    show swap2 (mk2 (p 1) (p 0)) = mk2 ((mk2 (p 1) (p 0)) 1) ((mk2 (p 1) (p 0)) 0) from rfl,
    mk2_zero, mk2_one, mk2_eta]

private lemma swap2_volume (A : Set E2) : volume (swap2 '' A) = volume A := by
  have h1 : (μHE[2] : Measure (EuclideanSpace ℝ (Fin 2))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2
  calc volume (swap2 '' A) = μHE[2] (swap2 '' A) := by rw [h1]
    _ = μHE[2] A := swap2_isometry.euclideanHausdorffMeasure_image A
    _ = volume A := by rw [h1]

private lemma swap2_diam (A : Set E2) :
    Metric.diam (swap2 '' A) = Metric.diam A := by
  unfold Metric.diam
  rw [swap2_isometry.ediam_image]

/-- **Paper Theorem 4.1** (isodiametric inequality, Bieberbach):
`m(E) ≤ π (diam E / 2)²`, proven by two Steiner symmetrizations. -/
theorem isodiametric (E : Set E2) :
    volume E ≤ ENNReal.ofReal Real.pi * (Metric.ediam E / 2) ^ 2 := by
  rcases eq_or_ne (Metric.ediam E) ⊤ with htop | hbdd
  · rw [htop]
    have h2 : (⊤ : ℝ≥0∞) / 2 = ⊤ := by
      rw [ENNReal.top_div]
      norm_num
    rw [h2]
    have h3 : (⊤ : ℝ≥0∞) ^ 2 = ⊤ := by norm_num
    rw [h3, ENNReal.mul_top (by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.pi_pos)]
    exact le_top
  -- the bounded case
  have hEb : Bornology.IsBounded E := Metric.isBounded_iff_ediam_ne_top.mpr hbdd
  set K := closure E with hKdef
  have hKcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded
    isClosed_closure hEb.closure
  have hdiamKE : Metric.diam K = Metric.diam E := by
    unfold Metric.diam
    rw [Metric.ediam_closure]
  -- the two symmetrizations
  set S1 := symmSet K with hS1
  set Q := swap2 '' S1 with hQ
  set S2 := symmSet Q with hS2
  set T := swap2 '' S2 with hT
  have hS1comp : IsCompact S1 := symmSet_isCompact hKcomp
  have hQcomp : IsCompact Q := hS1comp.image swap2_isometry.continuous
  have hS2comp : IsCompact S2 := symmSet_isCompact hQcomp
  have hTcomp : IsCompact T := hS2comp.image swap2_isometry.continuous
  -- volume chain
  have hvol : volume E ≤ volume T := by
    calc volume E ≤ volume K := measure_mono subset_closure
      _ ≤ volume S1 := symmSet_volume_le hKcomp
      _ = volume Q := (swap2_volume S1).symm
      _ ≤ volume S2 := symmSet_volume_le hQcomp
      _ = volume T := (swap2_volume S2).symm
  -- diameter chain
  have hdiam : Metric.diam T ≤ Metric.diam E := by
    calc Metric.diam T = Metric.diam S2 := swap2_diam S2
      _ ≤ Metric.diam Q := symmSet_diam_le hQcomp
      _ = Metric.diam S1 := swap2_diam S1
      _ ≤ Metric.diam K := symmSet_diam_le hKcomp
      _ = Metric.diam E := hdiamKE
  -- central symmetry of `T`
  have hTsym : ∀ p ∈ T, -p ∈ T := by
    intro p hp
    -- symmetry in coordinate 0 (coming from `symmSet_sym1` on `S2`)
    have hsym0 : mk2 (-(p 0)) (p 1) ∈ T := by
      obtain ⟨q, hq, rfl⟩ := hp
      have h1 := symmSet_sym1 (K := Q) hq
      refine ⟨mk2 (q 0) (-(q 1)), h1, ?_⟩
      show mk2 ((mk2 (q 0) (-(q 1))) 1) ((mk2 (q 0) (-(q 1))) 0)
        = mk2 (-((swap2 q) 0)) ((swap2 q) 1)
      rw [mk2_zero, mk2_one]
      rfl
    -- symmetry in coordinate 1 (coming from preserved symmetry of `Q`)
    have hQsym : ∀ r ∈ Q, mk2 (-(r 0)) (r 1) ∈ Q := by
      intro r hr
      obtain ⟨t, ht, rfl⟩ := hr
      have h2 := symmSet_sym1 (K := K) ht
      refine ⟨mk2 (t 0) (-(t 1)), h2, ?_⟩
      show mk2 ((mk2 (t 0) (-(t 1))) 1) ((mk2 (t 0) (-(t 1))) 0)
        = mk2 (-((swap2 t) 0)) ((swap2 t) 1)
      rw [mk2_zero, mk2_one]
      rfl
    have hsym1 : ∀ r ∈ T, mk2 (r 0) (-(r 1)) ∈ T := by
      intro r hr
      obtain ⟨q, hq, rfl⟩ := hr
      have h3 := symmSet_preserves_sym0 hQsym hq
      refine ⟨mk2 (-(q 0)) (q 1), h3, ?_⟩
      show mk2 ((mk2 (-(q 0)) (q 1)) 1) ((mk2 (-(q 0)) (q 1)) 0)
        = mk2 ((swap2 q) 0) (-((swap2 q) 1))
      rw [mk2_zero, mk2_one]
      rfl
    have h4 := hsym1 _ hsym0
    rw [mk2_zero, mk2_one] at h4
    have h5 : mk2 (-(p 0)) (-(p 1)) = -p := by
      apply PiLp.ext
      intro i
      fin_cases i <;> rfl
    rwa [h5] at h4
  -- `T` sits in the ball of radius `diam E / 2`
  have hTball : T ⊆ Metric.closedBall 0 (Metric.diam E / 2) := by
    intro p hp
    have h1 := hTsym p hp
    have h2 : dist p (-p) ≤ Metric.diam T :=
      Metric.dist_le_diam_of_mem hTcomp.isBounded hp h1
    have h3 : dist p (-p) = 2 * ‖p‖ := by
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ p, norm_smul]
      norm_num
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [hdiam]
  -- conclude
  have hfinal : volume E ≤ volume (Metric.closedBall (0:E2) (Metric.diam E / 2)) :=
    hvol.trans (measure_mono hTball)
  rw [Measure.addHaar_closedBall_eq_addHaar_ball,
    EuclideanSpace.volume_ball_fin_two] at hfinal
  have hediam : Metric.ediam E = ENNReal.ofReal (Metric.diam E) := by
    unfold Metric.diam
    rw [ENNReal.ofReal_toReal hbdd]
  rw [hediam]
  have hdiv : ENNReal.ofReal (Metric.diam E) / 2 = ENNReal.ofReal (Metric.diam E / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  rw [hdiv]
  calc volume E ≤ ENNReal.ofReal (Metric.diam E / 2) ^ 2 * ENNReal.ofReal Real.pi :=
      hfinal
    _ = ENNReal.ofReal Real.pi * ENNReal.ofReal (Metric.diam E / 2) ^ 2 := mul_comm _ _



/-! **Paper Theorem 5.1** in Mathlib's raw normalization:
on the Euclidean plane, `μH[2] = (4/π) • volume`.

Proof plan: Mathlib already knows `μH[2]` is an additive Haar measure
on `E2` (instance in `Mathlib.Geometry.Euclidean.Volume.Measure`), so
`μH[2] = c⁻¹ • volume` for a constant; pin the constant by evaluating
both sides on the closed unit disk `B`:
* `volume B = π` (`EuclideanSpace.volume_ball` / `EuclideanSpace.volume_ball_fin_two`);
* `μH[2] B ≥ 4`: for any cover `{Eᵢ}` of `B`,
  `Σ (diam Eᵢ)² ≥ (4/π) Σ vol Eᵢ ≥ (4/π) vol B = 4` by `isodiametric`
  and countable subadditivity (paper Prop 5.2);
* `μH[2] B ≤ 4`: cover `B` by small disjoint disks plus a null
  remainder — the greedy disk-filling Lemma 5.3 (or Mathlib's
  Besicovitch/Vitali covering machinery,
  `Besicovitch.exists_disjoint_closedBall_covering_ae`); a disk of
  radius `r` costs `(2r)² = (4/π)·(its area)` (paper Prop 5.4). -/

/-- Splitting an `ℝ≥0∞`-valued `tsum` over a sum type. -/
private lemma tsum_sum_type {α β : Type*} (f : α ⊕ β → ℝ≥0∞) :
    ∑' x, f x = (∑' a, f (Sum.inl a)) + ∑' b, f (Sum.inr b) := by
  have h1 : HasSum (fun x : Set.range (Sum.inl : α → α ⊕ β) => f x)
      (∑' a, f (Sum.inl a)) :=
    (Function.Injective.hasSum_range_iff Sum.inl_injective).mpr
      ENNReal.summable.hasSum
  have h2 : HasSum (fun x : Set.range (Sum.inr : β → α ⊕ β) => f x)
      (∑' b, f (Sum.inr b)) :=
    (Function.Injective.hasSum_range_iff Sum.inr_injective).mpr
      ENNReal.summable.hasSum
  exact (h1.add_isCompl Set.isCompl_range_inl_range_inr h2).tsum_eq

/-- Diameter bound for closed balls, in `ℝ≥0∞` form. -/
private lemma ediam_closedBall_le (x : E2) (r : ℝ) :
    Metric.ediam (Metric.closedBall x r) ≤ ENNReal.ofReal (2 * r) := by
  apply Metric.ediam_le
  intro y hy z hz
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
    _ ≤ r + r := add_le_add (Metric.mem_closedBall.mp hy)
        (by rw [dist_comm]; exact Metric.mem_closedBall.mp hz)
    _ = 2 * r := by ring

/-- Diameter bound for squares, in `ℝ≥0∞` form. -/
private lemma ediam_closedSquare_le (z₀ : E2) {t : ℝ} (ht : 0 ≤ t) :
    Metric.ediam (closedSquare z₀ t) ≤ ENNReal.ofReal (t * Real.sqrt 2) := by
  calc Metric.ediam (closedSquare z₀ t)
      ≤ Metric.ediam (Metric.closedBall z₀ (t * Real.sqrt 2 / 2)) :=
        Metric.ediam_mono (closedSquare_subset_closedBall z₀ ht)
    _ ≤ ENNReal.ofReal (2 * (t * Real.sqrt 2 / 2)) :=
        ediam_closedBall_le _ _
    _ = ENNReal.ofReal (t * Real.sqrt 2) := by ring_nf

/-- Volume-null sets admit square covers of arbitrarily small diameter
and arbitrarily small total Hausdorff price (paper: subdividing a cheap
open cover; here via `dyadic_decomposition`). -/
private lemma null_cover {Z : Set E2} (hZ : volume Z = 0) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ w : ℕ → Set E2, Z ⊆ (⋃ m, w m) ∧
      (∀ m, Metric.ediam (w m) ≤ ENNReal.ofReal δ) ∧
      ∑' m, Metric.ediam (w m) ^ 2 ≤ ENNReal.ofReal η := by
  obtain ⟨V, hZV, hVopen, hVvol⟩ := Set.exists_isOpen_lt_of_lt Z
    (ENNReal.ofReal (η / 4)) (by rw [hZ]; positivity)
  rcases Set.eq_empty_or_nonempty V with rfl | hVne
  · refine ⟨fun _ => ∅, by simpa using hZV, ?_, ?_⟩
    · intro m
      simp
    · simp
  obtain ⟨z, t, hprop, hdisj, hunion⟩ := dyadic_decomposition hVopen hVne
    (show 0 < δ / 2 by positivity)
  refine ⟨fun m => closedSquare (z m) (t m), ?_, ?_, ?_⟩
  · rw [hunion]
    exact hZV
  · intro m
    calc Metric.ediam (closedSquare (z m) (t m))
        ≤ ENNReal.ofReal (t m * Real.sqrt 2) :=
          ediam_closedSquare_le _ (hprop m).1.le
      _ ≤ ENNReal.ofReal δ := by
          apply ENNReal.ofReal_le_ofReal
          have h2 : Real.sqrt 2 ≤ 2 := by
            have := Real.sqrt_le_sqrt (show (2:ℝ) ≤ 4 by norm_num)
            rwa [show Real.sqrt 4 = 2 by
              rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
          nlinarith [(hprop m).2.1, (hprop m).1.le, Real.sqrt_nonneg 2]
  · -- total price: `Σ 2 t² = 2 Σ vol ≤ 2 vol V ≤ η/2`
    have hstep : ∀ m, Metric.ediam (closedSquare (z m) (t m)) ^ 2
        ≤ 2 * volume (closedSquare (z m) (t m)) := by
      intro m
      rw [volume_closedSquare _ (hprop m).1.le]
      calc Metric.ediam (closedSquare (z m) (t m)) ^ 2
          ≤ ENNReal.ofReal (t m * Real.sqrt 2) ^ 2 := by
            exact pow_le_pow_left' (ediam_closedSquare_le _ (hprop m).1.le) 2
        _ = 2 * ENNReal.ofReal (t m ^ 2) := by
            rw [← ENNReal.ofReal_pow (mul_nonneg (hprop m).1.le (Real.sqrt_nonneg 2))]
            rw [show (t m * Real.sqrt 2) ^ 2 = 2 * t m ^ 2 by
              rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring]
            rw [ENNReal.ofReal_mul (by norm_num)]
            norm_num
    have hvolsum : ∑' m, volume (closedSquare (z m) (t m)) ≤ volume V := by
      have hae : ∀ m, volume (closedSquare (z m) (t m))
          = volume (interior (closedSquare (z m) (t m))) := by
        intro m
        apply le_antisymm ?_ (measure_mono interior_subset)
        calc volume (closedSquare (z m) (t m))
            ≤ volume (interior (closedSquare (z m) (t m))
              ∪ (closedSquare (z m) (t m) \ interior (closedSquare (z m) (t m)))) := by
              refine measure_mono fun x hx => ?_
              by_cases h : x ∈ interior (closedSquare (z m) (t m))
              · exact Set.mem_union_left _ h
              · exact Set.mem_union_right _ ⟨hx, h⟩
          _ ≤ volume (interior (closedSquare (z m) (t m)))
              + volume (closedSquare (z m) (t m)
                \ interior (closedSquare (z m) (t m))) := measure_union_le _ _
          _ = volume (interior (closedSquare (z m) (t m))) := by
              rw [volume_frontier_closedSquare _ (hprop m).1.le, add_zero]
      calc ∑' m, volume (closedSquare (z m) (t m))
          = ∑' m, volume (interior (closedSquare (z m) (t m))) := by
            exact tsum_congr hae
        _ = volume (⋃ m, interior (closedSquare (z m) (t m))) := by
            rw [measure_iUnion ?_ fun m => isOpen_interior.measurableSet]
            intro m n hmn
            exact Set.disjoint_iff_inter_eq_empty.mpr (hdisj hmn)
        _ ≤ volume V := by
            apply measure_mono
            rw [← hunion]
            exact Set.iUnion_mono fun m => interior_subset
    calc ∑' m, Metric.ediam (closedSquare (z m) (t m)) ^ 2
        ≤ ∑' m, 2 * volume (closedSquare (z m) (t m)) := ENNReal.tsum_le_tsum hstep
      _ = 2 * ∑' m, volume (closedSquare (z m) (t m)) := ENNReal.tsum_mul_left
      _ ≤ 2 * ENNReal.ofReal (η / 4) := by
          exact mul_le_mul_right (hvolsum.trans hVvol.le) 2
      _ ≤ ENNReal.ofReal η := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num)]
          apply ENNReal.ofReal_le_ofReal
          linarith

/-- One Besicovitch stage: countably many disjoint closed balls of radius
`< 1/(n+1)` inside the unit ball, plus cheap squares `w` covering the
null remainder. -/
private lemma exists_besicovitch_stage (n : ℕ) :
    ∃ (T : Set E2) (rad : E2 → ℝ) (w : ℕ → Set E2),
      T.Countable ∧
      (∀ x ∈ T, 0 < rad x ∧ rad x < 1 / (n + 1)
        ∧ Metric.closedBall x (rad x) ⊆ Metric.ball (0 : E2) 1) ∧
      T.PairwiseDisjoint (fun x => Metric.closedBall x (rad x)) ∧
      (Metric.ball (0 : E2) 1
        ⊆ (⋃ x ∈ T, Metric.closedBall x (rad x)) ∪ ⋃ m, w m) ∧
      (∀ m, Metric.ediam (w m) ≤ ENNReal.ofReal (1 / (n + 1))) ∧
      ∑' m, Metric.ediam (w m) ^ 2 ≤ ENNReal.ofReal (1 / (n + 1)) := by
  have hn1 : (0:ℝ) < 1 / (n + 1) := by positivity
  obtain ⟨T, rad, hTc, hTsub, hTrad, hTnull, hTdisj⟩ :=
    Besicovitch.exists_disjoint_closedBall_covering_ae (volume : Measure E2)
      (fun x => Set.Ioo 0 (1 - dist x 0)) (Metric.ball 0 1)
      (fun x hx δ hδ => by
        have hd : dist x 0 < 1 := Metric.mem_ball.mp hx
        refine ⟨min ((1 - dist x 0) / 2) (δ / 2), ⟨?_, ?_⟩, ?_, ?_⟩
        · exact lt_min (by linarith) (by linarith)
        · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        · exact lt_min (by linarith) (by linarith)
        · exact lt_of_le_of_lt (min_le_right _ _) (by linarith))
      (fun _ => 1 / (n + 1)) (fun _ _ => hn1)
  obtain ⟨w, hwsub, hwdiam, hwsum⟩ := null_cover hTnull hn1 hn1
  refine ⟨T, rad, w, hTc, ?_, hTdisj, ?_, hwdiam, hwsum⟩
  · intro x hx
    obtain ⟨hfx, hlt⟩ := hTrad x hx
    have hd : dist x 0 < 1 := Metric.mem_ball.mp (hTsub hx)
    refine ⟨hfx.1, hlt.2, ?_⟩
    intro y hy
    rw [Metric.mem_ball]
    calc dist y 0 ≤ dist y x + dist x 0 := dist_triangle _ _ _
      _ ≤ rad x + dist x 0 := add_le_add (Metric.mem_closedBall.mp hy) le_rfl
      _ < (1 - dist x 0) + dist x 0 := by
          have := hfx.2
          linarith
      _ = 1 := by ring
  · intro y hy
    by_cases h : y ∈ ⋃ x ∈ T, Metric.closedBall x (rad x)
    · exact Set.mem_union_left _ h
    · refine Set.mem_union_right _ (hwsub ⟨hy, h⟩)

/-- Disjoint closed balls inside the unit ball have total squared
diameter at most `4`: `Σ (2r)² = (4/π)·Σ πr² = (4/π)·vol(⊔ balls)
≤ (4/π)·π` (the geometric heart of paper Prop 5.4). -/
private lemma tsum_ediam_sq_le_four {T : Set E2} {rad : E2 → ℝ}
    (hTc : T.Countable)
    (hsub : ∀ x ∈ T, Metric.closedBall x (rad x) ⊆ Metric.ball (0 : E2) 1)
    (hdisj : T.PairwiseDisjoint fun x => Metric.closedBall x (rad x)) :
    (∑' i : ↥T, Metric.ediam (Metric.closedBall (i : E2) (rad i)) ^ (2:ℕ))
      ≤ ENNReal.ofReal 4 := by
  haveI := hTc.to_subtype
  have hb1 : ∀ i : ↥T,
      Metric.ediam (Metric.closedBall (i : E2) (rad i)) ^ (2:ℕ)
      ≤ ENNReal.ofReal 4 * ENNReal.ofReal (rad i) ^ 2 := by
    intro i
    calc Metric.ediam (Metric.closedBall (i : E2) (rad i)) ^ (2:ℕ)
        ≤ ENNReal.ofReal (2 * rad i) ^ 2 :=
          pow_le_pow_left' (ediam_closedBall_le _ _) 2
      _ = ENNReal.ofReal 4 * ENNReal.ofReal (rad i) ^ 2 := by
          rw [ENNReal.ofReal_mul (by norm_num), mul_pow]
          norm_num
  have hvol : (∑' i : ↥T, ENNReal.ofReal (rad i) ^ 2)
      * ENNReal.ofReal Real.pi ≤ ENNReal.ofReal Real.pi := by
    have hveq : ∀ i : ↥T, ENNReal.ofReal (rad i) ^ 2 * ENNReal.ofReal Real.pi
        = volume (Metric.closedBall (i : E2) (rad i)) := by
      intro i
      rw [Measure.addHaar_closedBall_eq_addHaar_ball, EuclideanSpace.volume_ball_fin_two]
    calc (∑' i : ↥T, ENNReal.ofReal (rad i) ^ 2) * ENNReal.ofReal Real.pi
        = ∑' i : ↥T, volume (Metric.closedBall (i : E2) (rad i)) := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr hveq
      _ = volume (⋃ x ∈ T, Metric.closedBall x (rad x)) :=
          (measure_biUnion hTc hdisj
            fun x _ => Metric.isClosed_closedBall.measurableSet).symm
      _ ≤ volume (Metric.ball (0:E2) 1) := by
          apply measure_mono
          exact Set.iUnion₂_subset fun x hx => hsub x hx
      _ = ENNReal.ofReal 1 ^ 2 * ENNReal.ofReal Real.pi :=
          EuclideanSpace.volume_ball_fin_two 0 1
      _ = ENNReal.ofReal Real.pi := by norm_num
  have hsum1 : (∑' i : ↥T, ENNReal.ofReal (rad i) ^ 2) ≤ 1 := by
    have hπ0 : ENNReal.ofReal Real.pi ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.pi_pos
    have h1 : (∑' i : ↥T, ENNReal.ofReal (rad i) ^ 2)
        * ENNReal.ofReal Real.pi ≤ 1 * ENNReal.ofReal Real.pi := by
      rw [one_mul]
      exact hvol
    exact (ENNReal.mul_le_mul_iff_left hπ0 ENNReal.ofReal_ne_top).mp h1
  calc (∑' i : ↥T, Metric.ediam (Metric.closedBall (i : E2) (rad i)) ^ (2:ℕ))
      ≤ ∑' i : ↥T, ENNReal.ofReal 4 * ENNReal.ofReal (rad i) ^ 2 :=
        ENNReal.tsum_le_tsum hb1
    _ = ENNReal.ofReal 4 * ∑' i : ↥T, ENNReal.ofReal (rad i) ^ 2 :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal 4 * 1 := mul_le_mul_right hsum1 _
    _ = ENNReal.ofReal 4 := mul_one _

/-- The Besicovitch scales tend to zero. -/
private lemma tendsto_ofReal_two_div_atTop :
    Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (2 / (n + 1))) Filter.atTop
      (nhds 0) := by
  have h0 : Filter.Tendsto (fun n : ℕ => 2 * (1 / ((n:ℝ) + 1))) Filter.atTop
      (nhds (2 * 0)) :=
    Filter.Tendsto.const_mul 2 tendsto_one_div_add_atTop_nhds_zero_nat
  rw [mul_zero] at h0
  have h0' : (fun n : ℕ => 2 * (1 / ((n:ℝ) + 1)))
      = fun n : ℕ => 2 / ((n:ℝ) + 1) := by
    funext n
    rw [mul_one_div]
  rw [h0'] at h0
  have h2 := ENNReal.tendsto_ofReal h0
  rwa [ENNReal.ofReal_zero] at h2

/-- The stage prices `4 + 1/(n+1)` converge down to `4` in liminf. -/
private lemma liminf_four_add_one_div :
    Filter.liminf (fun n : ℕ =>
      ENNReal.ofReal 4 + ENNReal.ofReal (1 / (n + 1))) Filter.atTop
      = ENNReal.ofReal 4 := by
  apply Filter.Tendsto.liminf_eq
  have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := ENNReal.tendsto_ofReal h1
  rw [ENNReal.ofReal_zero] at h2
  have h3 := Filter.Tendsto.const_add (ENNReal.ofReal 4) h2
  rwa [add_zero] at h3

/-- The Besicovitch upper bound: `μH[2](B(0,1)) ≤ 4` (paper Prop 5.4:
covers by disjoint small disks cost their area, `(2r)² = (4/π)·πr²`). -/
private lemma hausdorff_ball_le :
    μH[(2:ℝ)] (Metric.ball (0 : E2) 1) ≤ ENNReal.ofReal 4 := by
  classical
  choose T rad w hTc hgood hdisj hcover hwdiam hwsum using exists_besicovitch_stage
  haveI hcnt : ∀ n : ℕ, Countable ↥(T n) := fun n => (hTc n).to_subtype
  -- Apply the liminf bound with the combined families.
  have hbound := hausdorffMeasure_le_liminf_tsum (2:ℝ) (Metric.ball (0:E2) 1)
    (l := Filter.atTop) (r := fun n : ℕ => ENNReal.ofReal (2 / (n + 1)))
    tendsto_ofReal_two_div_atTop
    (t := fun n => Sum.elim
      (fun i : ↥(T n) => Metric.closedBall (i : E2) (rad n i)) (w n))
    (Filter.Eventually.of_forall fun n => ?_)
    (Filter.Eventually.of_forall fun n => ?_)
  · refine le_trans hbound ?_
    -- Each total price is at most `4 + 1/(n+1)`.
    have hFle : ∀ n : ℕ, (∑' i : ↥(T n) ⊕ ℕ,
        Metric.ediam (Sum.elim
          (fun i : ↥(T n) => Metric.closedBall (i : E2) (rad n i)) (w n) i) ^ (2:ℝ))
        ≤ ENNReal.ofReal 4 + ENNReal.ofReal (1 / (n + 1)) := by
      intro n
      have hrw : ∀ i : ↥(T n) ⊕ ℕ,
          Metric.ediam (Sum.elim
            (fun i : ↥(T n) => Metric.closedBall (i : E2) (rad n i)) (w n) i) ^ (2:ℝ)
          = Metric.ediam (Sum.elim
            (fun i : ↥(T n) => Metric.closedBall (i : E2) (rad n i)) (w n) i) ^ (2:ℕ) := by
        intro i
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
      simp_rw [hrw]
      rw [tsum_sum_type]
      exact add_le_add
        (tsum_ediam_sq_le_four (hTc n) (fun x hx => (hgood n x hx).2.2) (hdisj n))
        (hwsum n)
    calc Filter.liminf (fun n : ℕ => ∑' i : ↥(T n) ⊕ ℕ,
          Metric.ediam (Sum.elim
            (fun i : ↥(T n) => Metric.closedBall (i : E2) (rad n i)) (w n) i) ^ (2:ℝ))
          Filter.atTop
        ≤ Filter.liminf (fun n : ℕ =>
            ENNReal.ofReal 4 + ENNReal.ofReal (1 / (n + 1))) Filter.atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hFle)
      _ = ENNReal.ofReal 4 := liminf_four_add_one_div
  · -- diameters bounded by the scale
    intro i
    rcases i with i | m
    · have h2 := (hgood n i i.2).2.1
      calc Metric.ediam (Metric.closedBall (i : E2) (rad n i))
          ≤ ENNReal.ofReal (2 * rad n i) := ediam_closedBall_le _ _
        _ ≤ ENNReal.ofReal (2 / (n + 1)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [show (2:ℝ) / ((n:ℝ) + 1) = 2 * (1 / ((n:ℝ) + 1)) by rw [mul_one_div]]
            linarith [h2]
    · calc Metric.ediam (w n m) ≤ ENNReal.ofReal (1 / (n + 1)) := hwdiam n m
        _ ≤ ENNReal.ofReal (2 / (n + 1)) := by
            apply ENNReal.ofReal_le_ofReal
            gcongr
            norm_num
  · -- the combined family covers
    intro y hy
    rw [Set.iUnion_sumElim]
    rcases hcover n hy with h | h
    · obtain ⟨x, hxT, hxball⟩ := Set.mem_iUnion₂.mp h
      exact Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨⟨x, hxT⟩, hxball⟩)
    · exact Set.mem_union_right _ h

theorem hausdorffMeasure_two_eq_smul_volume :
    (μH[2] : Measure E2) = ENNReal.ofReal (4 / Real.pi) • volume := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Lower bound: `(4/π)•volume ≤ μH[2]`, from the isodiametric inequality.
  have hlow : (ENNReal.ofReal (4 / Real.pi) • volume : Measure E2) ≤ μH[(2:ℝ)] := by
    apply le_hausdorffMeasure _ _ 1 one_pos
    intro u _
    rw [Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal (4 / Real.pi) * volume u
        ≤ ENNReal.ofReal (4 / Real.pi)
          * (ENNReal.ofReal Real.pi * (Metric.ediam u / 2) ^ 2) :=
          mul_le_mul_right (isodiametric u) _
      _ = Metric.ediam u ^ (2:ℝ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            show 4 / Real.pi * Real.pi = 4 by field_simp, ENNReal.ofReal_ofNat,
            div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow,
            show ((2:ℝ≥0∞)) ^ 2 = 4 by norm_num,
            mul_comm (Metric.ediam u ^ 2) _, ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul,
            show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  -- `μH[2]` of the unit ball is exactly 4.
  have hball_ge : ENNReal.ofReal 4 ≤ μH[(2:ℝ)] (Metric.ball (0:E2) 1) := by
    have h1 := hlow (Metric.ball (0:E2) 1)
    rw [Measure.smul_apply, smul_eq_mul, EuclideanSpace.volume_ball_fin_two] at h1
    calc ENNReal.ofReal 4
        = ENNReal.ofReal (4 / Real.pi) * (ENNReal.ofReal 1 ^ 2 * ENNReal.ofReal Real.pi) := by
          rw [ENNReal.ofReal_one, one_pow, one_mul,
            ← ENNReal.ofReal_mul (by positivity),
            show 4 / Real.pi * Real.pi = 4 by field_simp]
      _ ≤ μH[(2:ℝ)] (Metric.ball (0:E2) 1) := h1
  have hball : μH[(2:ℝ)] (Metric.ball (0:E2) 1) = ENNReal.ofReal 4 :=
    le_antisymm hausdorff_ball_le hball_ge
  -- Pin the abstract Haar scalar.
  have key : (volume : Measure E2)
      = addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2)))
          μH[(((2:ℕ)):ℝ)] • μH[(((2:ℕ)):ℝ)] :=
    Measure.isAddLeftInvariant_eq_smul _ _
  set c := addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    μH[(((2:ℕ)):ℝ)] with hcdef
  simp only [Nat.cast_ofNat] at key
  have hkey_ball := congrArg (fun m : Measure E2 => m (Metric.ball 0 1)) key
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hkey_ball
  rw [EuclideanSpace.volume_ball_fin_two, hball] at hkey_ball
  have hcval : (c : ℝ≥0∞) = ENNReal.ofReal (Real.pi / 4) := by
    have h4ne : (ENNReal.ofReal (4:ℝ)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      norm_num
    apply (ENNReal.mul_left_inj h4ne ENNReal.ofReal_ne_top).mp
    calc (c : ℝ≥0∞) * ENNReal.ofReal 4
        = ENNReal.ofReal 1 ^ 2 * ENNReal.ofReal Real.pi := hkey_ball.symm
      _ = ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal 4 := by
          rw [ENNReal.ofReal_one, one_pow, one_mul,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  -- Conclude the measure identity.
  apply Measure.ext
  intro A _
  have hAeq := congrArg (fun m : Measure E2 => m A) key
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hAeq
  rw [hcval] at hAeq
  rw [Measure.smul_apply, smul_eq_mul, hAeq, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity),
    show 4 / Real.pi * (Real.pi / 4) = 1 by field_simp, ENNReal.ofReal_one, one_mul]

/-- The scalar in Mathlib's `proof_wanted
addHaarScalarFactor_hausdorffMeasure_eq`, in dimension 2: `μHE[2]` is
`(π/4) • μH[2]` on **every** metric space — i.e. `μHE[2]` *is* the
paper's ℋ² of Definition 2.1 (gauge `π (diam/2)² = (π/4) diam²`).
Follows from `hausdorffMeasure_two_eq_smul_volume` by unfolding
`euclideanHausdorffMeasure_def` and `addHaarScalarFactor`. -/
theorem euclideanHausdorffMeasure_two_eq {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    (μHE[2] : Measure X) = ENNReal.ofReal (Real.pi / 4) • μH[2] := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Work in the ℕ-cast index, where Mathlib's Haar instance for `μH`
  -- on Euclidean space lives; convert to the plain-numeral index at
  -- the very end.
  have key : (volume : Measure E2)
      = addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2)))
          μH[(((2:ℕ)):ℝ)] • μH[(((2:ℕ)):ℝ)] :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hflat : (μH[(((2:ℕ)):ℝ)] : Measure E2)
      = ENNReal.ofReal (4 / Real.pi) • volume := by
    simp only [Nat.cast_ofNat]
    exact hausdorffMeasure_two_eq_smul_volume
  set c := addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    μH[(((2:ℕ)):ℝ)] with hcdef
  rw [hflat] at key
  -- Pin the scalar by evaluating on a ball.
  have hball := congrArg (fun μ : Measure E2 => μ (Metric.ball 0 1)) key
  simp only [ENNReal.smul_def, Measure.smul_apply, smul_eq_mul] at hball
  have hvol_pos : 0 < (volume : Measure E2) (Metric.ball 0 1) :=
    Metric.measure_ball_pos _ _ one_pos
  have hvol_ne_top : (volume : Measure E2) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hscalar : (c : ℝ≥0∞) * ENNReal.ofReal (4 / Real.pi) = 1 := by
    have hv : ((c : ℝ≥0∞) * ENNReal.ofReal (4 / Real.pi))
          * (volume : Measure E2) (Metric.ball 0 1)
        = 1 * (volume : Measure E2) (Metric.ball 0 1) := by
      rw [one_mul, mul_assoc]
      exact hball.symm
    exact (ENNReal.mul_left_inj hvol_pos.ne' hvol_ne_top).mp hv
  have hcval : (c : ℝ≥0∞) = ENNReal.ofReal (Real.pi / 4) := by
    have := ENNReal.eq_inv_of_mul_eq_one_left hscalar
    rw [this, ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]
  -- Unfold the definition of `μHE[2]` and substitute.
  rw [Measure.euclideanHausdorffMeasure_def, ENNReal.smul_def, ← hcdef, hcval]
  simp only [Nat.cast_ofNat]

/-- **Paper Theorem 1.1, raw-gauge form**: with Mathlib's unnormalized
`μH[2]`, the area formula reads
`μH[2](Γ_f) = (4/π) ∫_U √(1 + |∇f|²)`.
One-line consequence of `area_formula` and
`euclideanHausdorffMeasure_two_eq`. -/
theorem area_formula_hausdorffMeasure {U : Set E2} {f : E2 → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    μH[2] (graph f U)
      = ENNReal.ofReal (4 / Real.pi) * ∫⁻ z in U, ENNReal.ofReal (jac f z) := by
  have h := area_formula hU hf
  rw [euclideanHausdorffMeasure_two_eq, Measure.smul_apply, smul_eq_mul] at h
  rw [← h, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    (show 4 / Real.pi * (Real.pi / 4) = 1 by field_simp),
    ENNReal.ofReal_one, one_mul]

/-
# Application: the area of the sphere is 4π

    μHE[2] (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) = 4π,

`μHE[2]` being the geometrically-normalized (= the paper's ℋ²)
2-dimensional Hausdorff measure.  In the raw gauge normalization this
reads `μH[2](S²) = 16` (end of the file; that one statement — and only
that one — depends on the π/4 normalization constant of
`GraphArea.Normalization`).

Strategy: split the sphere into the two open hemispherical caps and the
equator.  Each open cap is an isometric copy of the graph of
`z ↦ √(1 − |z|²)` over the *open* unit disk — C¹ there, gradient blows
up at the boundary but the area integral `∫_D (1−|z|²)^{-1/2} = 2π`
converges, and `area_formula` holds for arbitrary open `U` with no
boundedness assumptions precisely so that this needs no extra argument.
The equator is a Lipschitz circle, hence `μHE[2]`-null.
-/




/-- Euclidean ℝ³ in its standard `EuclideanSpace` form. -/
abbrev E3' : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The explicit isometry `E3 ≃ E3'`

Needed because the graph machinery lives on the ℓ²-product
`E3 = WithLp 2 (E2 × ℝ)` while the sphere naturally lives in
`EuclideanSpace ℝ (Fin 3)`.  Coordinates must be tracked explicitly
(an abstract isometry would not identify the caps with graphs), so we
build it from the concatenated orthonormal basis. -/

/-- The standard orthonormal basis of `ℝ` (as a 1-element family). -/
def onbR : OrthonormalBasis (Fin 1) ℝ ℝ :=
  (Module.Basis.singleton (Fin 1) ℝ).toOrthonormalBasis (by
    constructor
    · intro i
      simp [Module.Basis.singleton_apply]
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij)

@[simp] lemma onbR_apply (i : Fin 1) : onbR i = 1 := by
  have h1 : onbR.toBasis = Module.Basis.singleton (Fin 1) ℝ :=
    Module.Basis.toBasis_toOrthonormalBasis _ _
  have h2 : onbR.toBasis i = Module.Basis.singleton (Fin 1) ℝ i := by rw [h1]
  rw [OrthonormalBasis.coe_toBasis] at h2
  rw [h2, Module.Basis.singleton_apply]

/-- The coordinate isometry `E3 ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)`,
`(z, t) ↦ (z 0, z 1, t)`: concatenate the standard bases of `E2` and
`ℝ` (`OrthonormalBasis.prod`) and take coordinates
(`OrthonormalBasis.repr`, the content of paper Lem 6.2). -/
def toE3' : E3 ≃ₗᵢ[ℝ] E3' :=
  (((EuclideanSpace.basisFun (Fin 2) ℝ).prod onbR).reindex finSumFinEquiv).repr

/-- `toE3'` in coordinates. -/
@[simp] lemma toE3'_apply (z : E2) (t : ℝ) :
    toE3' (WithLp.toLp 2 (z, t)) = WithLp.toLp 2 ![z 0, z 1, t] := by
  -- Inner products against the concatenated basis compute coordinates.
  have hsplit : ∀ (a : E2) (s : ℝ) (b : E2) (u : ℝ),
      (inner ℝ (WithLp.toLp 2 (a, s) : E3) (WithLp.toLp 2 (b, u)) : ℝ)
        = inner ℝ a b + u * s := fun a s b u => rfl
  have hip : ∀ (m : Fin 2) (x : E2),
      (inner ℝ ((EuclideanSpace.basisFun (Fin 2) ℝ) m) x : ℝ) = x m :=
    fun m x => ((EuclideanSpace.basisFun (Fin 2) ℝ).repr_apply_apply x m).symm
  apply PiLp.ext
  intro i
  show (((EuclideanSpace.basisFun (Fin 2) ℝ).prod onbR).reindex
      finSumFinEquiv).repr (WithLp.toLp 2 (z, t)) i = _
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.reindex_apply]
  fin_cases i
  · have h0 : finSumFinEquiv.symm (⟨0, by norm_num⟩ : Fin (2 + 1)) = Sum.inl 0 := by decide
    rw [h0, OrthonormalBasis.prod_apply]
    simp only [Sum.elim_inl, Function.comp_apply, LinearMap.coe_inl]
    show (inner ℝ ((EuclideanSpace.basisFun (Fin 2) ℝ) 0) z + t * 0 : ℝ) = z 0
    rw [hip 0 z]
    ring
  · have h1 : finSumFinEquiv.symm (⟨1, by norm_num⟩ : Fin (2 + 1)) = Sum.inl 1 := by decide
    rw [h1, OrthonormalBasis.prod_apply]
    simp only [Sum.elim_inl, Function.comp_apply, LinearMap.coe_inl]
    show (inner ℝ ((EuclideanSpace.basisFun (Fin 2) ℝ) 1) z + t * 0 : ℝ) = z 1
    rw [hip 1 z]
    ring
  · have h2 : finSumFinEquiv.symm (⟨2, by norm_num⟩ : Fin (2 + 1)) = Sum.inr 0 := by decide
    rw [h2, OrthonormalBasis.prod_apply]
    simp only [Sum.elim_inr, Function.comp_apply, LinearMap.coe_inr]
    show (inner ℝ (0 : E2) z + t * onbR 0 : ℝ) = t
    rw [inner_zero_left, onbR_apply]
    ring

/-! ## The cap as a graph -/

/-- The open unit disk in the plane. -/
def unitDisk : Set E2 := Metric.ball 0 1

lemma isOpen_unitDisk : IsOpen unitDisk := Metric.isOpen_ball

/-- The hemisphere function `f(z) = √(1 − |z|²)`. -/
def capFun (z : E2) : ℝ := Real.sqrt (1 - ‖z‖ ^ 2)

/-- `capFun` is C¹ on the *open* disk (the gradient blows up at the
boundary, which is why the main theorem was proved for arbitrary open
`U` with possibly-unbounded gradient). -/
lemma contDiffOn_capFun : ContDiffOn ℝ 1 capFun unitDisk := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  have hz1 : ‖z‖ < 1 := by simpa [unitDisk] using hz
  have hne : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
  exact (Real.contDiffAt_sqrt hne).comp z
    (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt)

/-- The derivative of the hemisphere function on the open disk:
`∇f(z) = -z/√(1-|z|²)` as a continuous linear functional. -/
lemma hasFDerivAt_capFun {z : E2} (hz : z ∈ unitDisk) :
    HasFDerivAt capFun ((-(1 / Real.sqrt (1 - ‖z‖ ^ 2))) • innerSL ℝ z) z := by
  have hz1 : ‖z‖ < 1 := by simpa [unitDisk] using hz
  have hpos : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hspos : 0 < Real.sqrt (1 - ‖z‖ ^ 2) := Real.sqrt_pos.mpr hpos
  have h1 : HasFDerivAt (fun w : E2 => ‖w‖ ^ 2) ((2 : ℕ) • innerSL ℝ z) z := by
    simpa using (hasFDerivAt_id z).norm_sq
  have hg : HasFDerivAt (fun w : E2 => 1 - ‖w‖ ^ 2) (-((2 : ℕ) • innerSL ℝ z)) z :=
    h1.const_sub 1
  have h2 := (Real.hasDerivAt_sqrt hpos.ne').comp_hasFDerivAt z hg
  have heq : (1 / (2 * Real.sqrt (1 - ‖z‖ ^ 2))) • (-((2 : ℕ) • innerSL ℝ z))
      = (-(1 / Real.sqrt (1 - ‖z‖ ^ 2))) • innerSL ℝ z := by
    ext w
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    field_simp
  rw [heq] at h2
  exact h2

/-- The Jacobian of the hemisphere graph:
`J(z) = √(1 + |∇f|²) = 1/√(1 − |z|²)` on the open disk. -/
lemma jac_capFun {z : E2} (hz : z ∈ unitDisk) :
    jac capFun z = 1 / Real.sqrt (1 - ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := by simpa [unitDisk] using hz
  have hpos : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hspos : 0 < Real.sqrt (1 - ‖z‖ ^ 2) := Real.sqrt_pos.mpr hpos
  have hderiv := (hasFDerivAt_capFun hz).fderiv
  have hnorm : ‖fderiv ℝ capFun z‖ = ‖z‖ / Real.sqrt (1 - ‖z‖ ^ 2) := by
    rw [hderiv, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity)]
    ring
  unfold jac
  rw [hnorm]
  have hkey : 1 + (‖z‖ / Real.sqrt (1 - ‖z‖ ^ 2)) ^ 2
      = (1 / Real.sqrt (1 - ‖z‖ ^ 2)) ^ 2 := by
    have hs2 : Real.sqrt (1 - ‖z‖ ^ 2) ^ 2 = 1 - ‖z‖ ^ 2 := Real.sq_sqrt hpos.le
    field_simp
    linarith
  rw [hkey, Real.sqrt_sq (by positivity)]

/-- The (improper, but ℝ≥0∞-valued) cap area integral:
`∫_D (1 − |z|²)^{-1/2} dz = 2π`, by polar coordinates and the
fundamental theorem of calculus for the improper integral
`∫₀¹ r(1−r²)^{-1/2} dr = 1`. -/
lemma lintegral_jac_capFun :
    ∫⁻ z in unitDisk, ENNReal.ofReal (jac capFun z)
      = ENNReal.ofReal (2 * Real.pi) := by
  -- Step 0: the elementary 1-D improper integral `∫₀¹ r/√(1-r²) dr = 1`,
  -- by the fundamental theorem of calculus with antiderivative `-√(1-r²)`.
  have hderiv : ∀ r ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => -Real.sqrt (1 - t ^ 2))
        (r / Real.sqrt (1 - r ^ 2)) r := by
    intro r hr
    have hpos : (0:ℝ) < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have hspos := Real.sqrt_pos.mpr hpos
    have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * r)) r := by
      simpa using ((hasDerivAt_pow 2 r).const_sub 1)
    have h2 := (Real.hasDerivAt_sqrt hpos.ne').comp r h1
    have h3 := h2.neg
    have heq : -(1 / (2 * Real.sqrt (1 - r ^ 2)) * -(2 * r))
        = r / Real.sqrt (1 - r ^ 2) := by
      field_simp
    simpa only [Function.comp_def, Pi.neg_def, heq] using h3
  have hcont : ContinuousOn (fun t : ℝ => -Real.sqrt (1 - t ^ 2)) (Set.Icc 0 1) := by
    fun_prop
  have hnonneg : ∀ r ∈ Set.Ioo (0:ℝ) 1, 0 ≤ r / Real.sqrt (1 - r ^ 2) := by
    intro r hr
    exact div_nonneg hr.1.le (Real.sqrt_nonneg _)
  have hIoo : IntegrableOn (fun r : ℝ => r / Real.sqrt (1 - r ^ 2))
      (Set.Ioo 0 1) volume :=
    (intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hnonneg).mono_set
      Set.Ioo_subset_Ioc_self
  have hval : ∫ r in (0:ℝ)..1, r / Real.sqrt (1 - r ^ 2) = 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hcont
      (fun x hx => (hderiv x hx).hasDerivWithinAt)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hIoo)]
    norm_num
  have hr_int : ∫⁻ r in Set.Ioo (0:ℝ) 1,
      ENNReal.ofReal (r / Real.sqrt (1 - r ^ 2)) = 1 := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIoo
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall hnonneg))]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one, hval, ENNReal.ofReal_one]
  -- Step 1: replace the integrand by its explicit form on the disk.
  have hcong : ∫⁻ z in unitDisk, ENNReal.ofReal (jac capFun z)
      = ∫⁻ z in unitDisk, ENNReal.ofReal (1 / Real.sqrt (1 - ‖z‖ ^ 2)) := by
    refine setLIntegral_congr_fun isOpen_unitDisk.measurableSet ?_
    intro z hz
    exact congrArg ENNReal.ofReal (jac_capFun hz)
  -- Step 2: transport to `ℝ × ℝ` by the volume-preserving coordinate map.
  set Fm : (ℝ × ℝ) ≃ᵐ E2 :=
    (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.trans
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) with hFmdef
  have hFm : MeasurePreserving Fm volume volume := by
    have h1 : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := ℝ)).symm
        (volume : Measure (ℝ × ℝ)) volume := by
      have h := measurePreserving_finTwoArrow (volume : Measure ℝ)
      rw [← volume_pi, ← volume_eq_prod] at h
      exact h.symm
    exact (PiLp.volume_preserving_toLp (Fin 2)).comp h1
  have hnormsq : ∀ p : ℝ × ℝ, ‖(Fm p : E2)‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    intro p
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    rfl
  have hpre : Fm ⁻¹' unitDisk = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} := by
    ext p
    simp only [Set.mem_preimage, unitDisk, Metric.mem_ball, dist_zero_right,
      Set.mem_setOf_eq]
    constructor
    · intro h
      have h2 : ‖(Fm p : E2)‖ ^ 2 < 1 := by nlinarith [norm_nonneg (Fm p : E2)]
      rw [hnormsq] at h2
      exact h2
    · intro h
      nlinarith [norm_nonneg (Fm p : E2), hnormsq p]
  have hDmeas : MeasurableSet {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} :=
    measurableSet_lt (by fun_prop) measurable_const
  rw [hcong, ← hFm.setLIntegral_comp_preimage_emb Fm.measurableEmbedding, hpre]
  have hcong2 : ∫⁻ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1},
      ENNReal.ofReal (1 / Real.sqrt (1 - ‖(Fm p : E2)‖ ^ 2))
      = ∫⁻ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1},
        ENNReal.ofReal (1 / Real.sqrt (1 - (p.1 ^ 2 + p.2 ^ 2))) := by
    refine setLIntegral_congr_fun hDmeas ?_
    intro p _
    exact congrArg (fun t : ℝ => ENNReal.ofReal (1 / Real.sqrt (1 - t))) (hnormsq p)
  rw [hcong2]
  -- Step 3: polar coordinates.
  rw [← lintegral_indicator hDmeas, ← lintegral_comp_polarCoord_symm]
  have htarget_eq : ∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 • ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}.indicator
        (fun q => ENNReal.ofReal (1 / Real.sqrt (1 - (q.1 ^ 2 + q.2 ^ 2))))
        (polarCoord.symm p))
      = ∫⁻ p in polarCoord.target,
        (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun q => ENNReal.ofReal (q.1 / Real.sqrt (1 - q.1 ^ 2))) p := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet ?_
    intro p hp
    have hp1 : (0:ℝ) < p.1 := hp.1
    have hsymm : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl
    have hsq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      have h := Real.sin_sq_add_cos_sq p.2
      nlinarith [h]
    by_cases hlt : p.1 < 1
    · have hm1 : ((p.1 * Real.cos p.2, p.1 * Real.sin p.2) : ℝ × ℝ)
          ∈ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} := by
        show (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 < 1
        rw [hsq]
        nlinarith
      have hm2 : p ∈ Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi :=
        ⟨⟨hp1, hlt⟩, hp.2⟩
      simp only [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2, hsymm,
        smul_eq_mul]
      rw [← ENNReal.ofReal_mul hp1.le]
      congr 1
      rw [hsq, mul_one_div]
    · have hm1 : ((p.1 * Real.cos p.2, p.1 * Real.sin p.2) : ℝ × ℝ)
          ∉ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} := by
        intro hmem
        rw [Set.mem_setOf_eq, hsq] at hmem
        exact hlt (by nlinarith)
      have hm2 : p ∉ Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro hmem
        exact hlt hmem.1.2
      simp only [hsymm, Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2,
        smul_zero]
  rw [htarget_eq, setLIntegral_indicator (by measurability)]
  have hint : (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi) ∩ polarCoord.target
      = Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi := by
    apply Set.inter_eq_left.mpr
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  rw [hint]
  -- Step 4: Fubini for the product set; the angular integral contributes 2π.
  have hmeas1 : Measurable fun r : ℝ => ENNReal.ofReal (r / Real.sqrt (1 - r ^ 2)) := by
    measurability
  rw [volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (by measurability)]
  calc ∫⁻ r in Set.Ioo (0:ℝ) 1, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (r / Real.sqrt (1 - r ^ 2))
      = ∫⁻ r in Set.Ioo (0:ℝ) 1,
          ENNReal.ofReal (r / Real.sqrt (1 - r ^ 2)) * ENNReal.ofReal (2 * Real.pi) := by
        refine lintegral_congr fun r => ?_
        rw [setLIntegral_const, Real.volume_Ioo]
        congr 2
        ring
    _ = (∫⁻ r in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (r / Real.sqrt (1 - r ^ 2)))
          * ENNReal.ofReal (2 * Real.pi) := lintegral_mul_const _ hmeas1
    _ = ENNReal.ofReal (2 * Real.pi) := by rw [hr_int, one_mul]

/-! ## Splitting the sphere -/

/-- The open upper hemispherical cap. -/
def upperCap : Set E3' := {ω | ‖ω‖ = 1 ∧ 0 < ω 2}

/-- The open lower hemispherical cap. -/
def lowerCap : Set E3' := {ω | ‖ω‖ = 1 ∧ ω 2 < 0}

/-- The equator. -/
def equator : Set E3' := {ω | ‖ω‖ = 1 ∧ ω 2 = 0}

/-- The sphere splits into the two open caps and the equator
(trichotomy on the last coordinate). -/
lemma sphere_eq_union :
    Metric.sphere (0 : E3') 1 = upperCap ∪ lowerCap ∪ equator := by
  ext ω
  simp only [mem_sphere_zero_iff_norm, upperCap, lowerCap, equator,
    Set.mem_union, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases lt_trichotomy (ω 2) 0 with h2 | h2 | h2
    · exact Or.inl (Or.inr ⟨h, h2⟩)
    · exact Or.inr ⟨h, h2⟩
    · exact Or.inl (Or.inl ⟨h, h2⟩)
  · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h

lemma upperCap_disjoint_lowerCap : Disjoint upperCap lowerCap := by
  rw [Set.disjoint_left]
  rintro ω ⟨-, h⟩ ⟨-, h'⟩
  exact absurd h (asymm h')

/-- The lower cap is Borel: intersection of the (closed) unit sphere
with an open half-space. -/
lemma measurableSet_lowerCap : MeasurableSet lowerCap := by
  have hset : lowerCap = Metric.sphere (0 : E3') 1 ∩ {ω : E3' | ω 2 < 0} := by
    ext ω
    simp [lowerCap]
  have hm : Measurable fun ω : E3' => ω 2 :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.measurable :
      Measurable fun ω : E3' => ω 2)
  rw [hset]
  exact Metric.isClosed_sphere.measurableSet.inter (measurableSet_lt hm measurable_const)

/-- The upper cap is exactly the image of the graph of `capFun` over
the open disk under the coordinate isometry. -/
lemma image_graph_capFun : toE3' '' graph capFun unitDisk = upperCap := by
  ext ω
  constructor
  · rintro ⟨-, ⟨z, hz, rfl⟩, rfl⟩
    have hz1 : ‖z‖ < 1 := by simpa [unitDisk] using hz
    have hpos : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have himg : toE3' (graphMap capFun z)
        = WithLp.toLp 2 ![z 0, z 1, capFun z] := toE3'_apply z (capFun z)
    rw [himg]
    constructor
    · -- unit norm
      have hsq : ‖(WithLp.toLp 2 ![z 0, z 1, capFun z] : E3')‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
        have hz2 : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
        have hcap2 : capFun z ^ 2 = 1 - ‖z‖ ^ 2 := Real.sq_sqrt hpos.le
        show z 0 ^ 2 + z 1 ^ 2 + capFun z ^ 2 = 1
        linarith
      rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one]
    · -- positive height
      show (0 : ℝ) < _
      have : (WithLp.toLp 2 ![z 0, z 1, capFun z] : E3') 2 = capFun z := rfl
      rw [this]
      exact Real.sqrt_pos.mpr hpos
  · rintro ⟨hn, hpos⟩
    set z : E2 := WithLp.toLp 2 ![ω 0, ω 1] with hzdef
    have hz0 : z 0 = ω 0 := rfl
    have hz1 : z 1 = ω 1 := rfl
    have hsum : ω 0 ^ 2 + ω 1 ^ 2 + ω 2 ^ 2 = 1 := by
      have h := congrArg (· ^ 2) hn
      simp only [one_pow] at h
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at h
      exact h
    have hznorm : ‖z‖ ^ 2 = 1 - ω 2 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, hz0, hz1]
      linarith
    have hzball : z ∈ unitDisk := by
      rw [unitDisk, Metric.mem_ball, dist_zero_right]
      nlinarith [norm_nonneg z, pow_pos hpos 2]
    have hcap : capFun z = ω 2 := by
      rw [capFun, hznorm, show (1 : ℝ) - (1 - ω 2 ^ 2) = ω 2 ^ 2 by ring,
        Real.sqrt_sq hpos.le]
    refine ⟨graphMap capFun z, ⟨z, hzball, rfl⟩, ?_⟩
    rw [show graphMap capFun z = WithLp.toLp 2 (z, capFun z) from rfl,
      toE3'_apply, hz0, hz1, hcap]
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl

/-- The equator is `μHE[2]`-null: it is contained in the image of the
compact interval `[-π, π]` under the Lipschitz circle curve
`θ ↦ (cos θ, sin θ, 0)`. -/
lemma equator_null : μHE[2] equator = 0 := by
  set γ : ℝ → E3' := fun θ => WithLp.toLp 2 ![Real.cos θ, Real.sin θ, 0] with hγdef
  -- The circle curve is √2-Lipschitz (coordinatewise 1-Lipschitz).
  have hlip : LipschitzWith (⟨Real.sqrt 2, Real.sqrt_nonneg 2⟩ : ℝ≥0) γ := by
    apply LipschitzWith.of_dist_le_mul
    intro θ θ'
    have hc : dist (Real.cos θ) (Real.cos θ') ≤ dist θ θ' := by
      simpa using Real.lipschitzWith_cos.dist_le_mul θ θ'
    have hs : dist (Real.sin θ) (Real.sin θ') ≤ dist θ θ' := by
      simpa using Real.lipschitzWith_sin.dist_le_mul θ θ'
    rw [hγdef, EuclideanSpace.dist_eq, Fin.sum_univ_three]
    have hcoord0 : dist ((WithLp.toLp 2 ![Real.cos θ, Real.sin θ, 0] : E3') 0)
        ((WithLp.toLp 2 ![Real.cos θ', Real.sin θ', 0] : E3') 0)
        = dist (Real.cos θ) (Real.cos θ') := rfl
    have hcoord1 : dist ((WithLp.toLp 2 ![Real.cos θ, Real.sin θ, 0] : E3') 1)
        ((WithLp.toLp 2 ![Real.cos θ', Real.sin θ', 0] : E3') 1)
        = dist (Real.sin θ) (Real.sin θ') := rfl
    have hcoord2 : dist ((WithLp.toLp 2 ![Real.cos θ, Real.sin θ, 0] : E3') 2)
        ((WithLp.toLp 2 ![Real.cos θ', Real.sin θ', 0] : E3') 2) = 0 := by
      show dist (0 : ℝ) 0 = 0
      simp
    rw [hcoord0, hcoord1, hcoord2]
    have hb : dist (Real.cos θ) (Real.cos θ') ^ 2 + dist (Real.sin θ) (Real.sin θ') ^ 2
        + (0:ℝ) ^ 2 ≤ 2 * dist θ θ' ^ 2 := by
      nlinarith [(dist_nonneg : (0:ℝ) ≤ dist (Real.cos θ) (Real.cos θ')),
        (dist_nonneg : (0:ℝ) ≤ dist (Real.sin θ) (Real.sin θ')),
        (dist_nonneg : (0:ℝ) ≤ dist θ θ')]
    calc Real.sqrt (dist (Real.cos θ) (Real.cos θ') ^ 2
          + dist (Real.sin θ) (Real.sin θ') ^ 2 + (0:ℝ) ^ 2)
        ≤ Real.sqrt (2 * dist θ θ' ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt 2 * dist θ θ' := by
          rw [show (2:ℝ) * dist θ θ' ^ 2 = (Real.sqrt 2 * dist θ θ') ^ 2 by
            linear_combination (-(dist θ θ' ^ 2))
              * Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
          exact Real.sqrt_sq (by positivity)
  -- Every equator point is `γ (arg)` of the corresponding complex number.
  have hsub : equator ⊆ γ '' Set.Icc (-Real.pi) Real.pi := by
    rintro ω ⟨hn, h2⟩
    have hsum : ω 0 ^ 2 + ω 1 ^ 2 + ω 2 ^ 2 = 1 := by
      have h := congrArg (· ^ 2) hn
      simp only [one_pow] at h
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at h
      exact h
    set c : ℂ := ⟨ω 0, ω 1⟩ with hcdef
    have hnormc : ‖c‖ = 1 := by
      have h1 : ‖c‖ ^ 2 = 1 := by
        rw [Complex.sq_norm, Complex.normSq_mk]
        linear_combination hsum - ω 2 * h2
      rw [← Real.sqrt_sq (norm_nonneg c), h1, Real.sqrt_one]
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnormc
      norm_num at hnormc
    refine ⟨Complex.arg c, ⟨(Complex.neg_pi_lt_arg c).le, Complex.arg_le_pi c⟩, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · show Real.cos (Complex.arg c) = ω 0
      rw [Complex.cos_arg hc0, hnormc]
      simp [hcdef]
    · show Real.sin (Complex.arg c) = ω 1
      rw [Complex.sin_arg, hnormc]
      simp [hcdef]
    · show (0 : ℝ) = ω 2
      exact h2.symm
  refine measure_mono_null hsub (euclideanHausdorff_two_image_null
    hlip.lipschitzOnWith ?_)
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- The two caps have equal area: the reflection
`ω ↦ (ω 0, ω 1, −(ω 2))` is a linear isometry of `E3'` exchanging
them. -/
lemma measure_lowerCap_eq_upperCap : μHE[2] lowerCap = μHE[2] upperCap := by
  -- The reflection in the third coordinate.
  set ρ : E3' ≃ₗᵢ[ℝ] E3' := LinearIsometryEquiv.piLpCongrRight 2
    (fun i : Fin 3 => if i = 2 then LinearIsometryEquiv.neg ℝ
      else LinearIsometryEquiv.refl ℝ ℝ) with hρdef
  have hρ2 : ∀ ω : E3', ρ ω 2 = -(ω 2) := by
    intro ω
    rw [hρdef, LinearIsometryEquiv.piLpCongrRight_apply]
    simp
  have hρ01 : ∀ (ω : E3') (i : Fin 3), i ≠ 2 → ρ ω i = ω i := by
    intro ω i hi
    rw [hρdef, LinearIsometryEquiv.piLpCongrRight_apply]
    simp [hi]
  have himg : ρ '' upperCap = lowerCap := by
    ext ω
    constructor
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
      refine ⟨by rw [LinearIsometryEquiv.norm_map]; exact hw1, ?_⟩
      rw [hρ2]
      linarith
    · rintro ⟨h1, h2⟩
      refine ⟨ρ ω, ⟨?_, ?_⟩, ?_⟩
      · rw [LinearIsometryEquiv.norm_map]; exact h1
      · rw [hρ2]; linarith
      · -- ρ is an involution
        apply PiLp.ext
        intro i
        by_cases hi : i = 2
        · subst hi; rw [hρ2, hρ2]; ring
        · rw [hρ01 _ _ hi, hρ01 _ _ hi]
  rw [← himg, ρ.isometry.euclideanHausdorffMeasure_image]

/-! ## The main computation -/

/-- **The area of the unit sphere is 4π** (in the paper's / geometric
normalization ℋ² = `μHE[2]`).

The assembly below is *complete*: every remaining gap is in the
supporting lemmas above. -/
theorem sphere_area_unit :
    μHE[2] (Metric.sphere (0 : E3') 1) = ENNReal.ofReal (4 * Real.pi) := by
  have hsplit : μHE[2] (Metric.sphere (0 : E3') 1)
      = μHE[2] upperCap + μHE[2] lowerCap := by
    rw [sphere_eq_union]
    exact measure_split_two upperCap_disjoint_lowerCap measurableSet_lowerCap
      equator_null
  have hupper : μHE[2] upperCap = ENNReal.ofReal (2 * Real.pi) := by
    rw [← image_graph_capFun,
      area_formula_of_isometry isOpen_unitDisk contDiffOn_capFun
        toE3'.isometry]
    exact lintegral_jac_capFun
  have hlower : μHE[2] lowerCap = ENNReal.ofReal (2 * Real.pi) := by
    rw [measure_lowerCap_eq_upperCap, hupper]
  rw [hsplit, hupper, hlower,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- The sphere of radius `r` has area `4πr²`: rescale by the homothety
centered at `x` (which multiplies `μHE[2]` by `r²`) and translate. -/
theorem sphere_area (x : E3') {r : ℝ} (hr : 0 < r) :
    μHE[2] (Metric.sphere x r) = ENNReal.ofReal (4 * Real.pi * r ^ 2) := by
  -- `sphere x r` is the homothety image of `sphere x 1`.
  have himg : Metric.sphere x r = AffineMap.homothety x r '' Metric.sphere x 1 := by
    ext ω
    simp only [Metric.mem_sphere, Set.mem_image]
    constructor
    · intro h
      refine ⟨AffineMap.homothety x r⁻¹ ω, ?_, ?_⟩
      · rw [AffineMap.homothety_apply, dist_eq_norm]
        simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← dist_eq_norm, h]
        field_simp
      · rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
        simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right]
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_add_cancel]
    · rintro ⟨y, hy, rfl⟩
      rw [AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add]
      rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, ← dist_eq_norm, hy, mul_one]
  -- `sphere x 1` is a translate of the unit sphere.
  have htrans : Metric.sphere x 1 = (fun w : E3' => x + w) '' Metric.sphere 0 1 := by
    ext ω
    simp only [Metric.mem_sphere, Set.mem_image]
    constructor
    · intro h
      refine ⟨ω - x, ?_, by rw [add_comm, sub_add_cancel]⟩
      rw [dist_zero_right, ← dist_eq_norm]
      exact h
    · rintro ⟨w, hw, rfl⟩
      rw [dist_eq_norm]
      simpa using hw
  have hiso : Isometry (fun w : E3' => x + w) :=
    Isometry.of_dist_eq fun a b => dist_add_left x a b
  rw [himg, MeasureTheory.euclideanHausdorffMeasure_homothety_image 2 x hr.ne',
    htrans, hiso.euclideanHausdorffMeasure_image, sphere_area_unit]
  -- `‖r‖₊² • 4π = 4πr²` in `ℝ≥0∞`.
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow, ← enorm_eq_nnnorm,
    Real.enorm_eq_ofReal_abs, abs_of_pos hr,
    ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The same statement in Mathlib's raw gauge normalization:
`μH[2](S²) = 16` — the `π/4` of `euclideanHausdorffMeasure_two_eq`
(paper §§4–5) exactly cancels the `4π`.  Unlike everything above, this
depends on the normalization constant (`GraphArea.Normalization`). -/
theorem sphere_hausdorffMeasure_unit :
    μH[2] (Metric.sphere (0 : E3') 1) = 16 := by
  have h := sphere_area_unit
  rw [euclideanHausdorffMeasure_two_eq, Measure.smul_apply, smul_eq_mul] at h
  have hne : ENNReal.ofReal (Real.pi / 4) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have h16 : ENNReal.ofReal (Real.pi / 4) * 16 = ENNReal.ofReal (4 * Real.pi) := by
    rw [show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by simp,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  exact (ENNReal.mul_right_inj hne ENNReal.ofReal_ne_top).mp (h.trans h16.symm)

end GraphAreaFull
