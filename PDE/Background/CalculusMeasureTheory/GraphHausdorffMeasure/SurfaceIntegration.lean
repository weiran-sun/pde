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
import PDE.Background.CalculusMeasureTheory.GraphHausdorffMeasure.RnGraphHausdorffMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

noncomputable section

open MeasureTheory Measure Set GeneralizedGraphFull
open scoped ENNReal NNReal

namespace GeneralizedGraph

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

end GeneralizedGraph
