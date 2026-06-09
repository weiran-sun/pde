import Mathlib.Geometry.Manifold.PartitionOfUnity
open MeasureTheory
open ENNReal


/-! ## Compactly supported smooth test functions -/

/-- Compactly supported smooth functions supported in an open set `U ⊆ ℝᵈ`.
    Elements satisfy: compact support, support contained in `U`, and `C^∞` regularity. -/
lemma HasCompactSupport.smul {α β : Type*}
    [TopologicalSpace α] [Zero β] [SMulWithZero ℝ β]
    {c : ℝ} {f : α → β} (hf : HasCompactSupport f) :
    HasCompactSupport (c • f) :=
     hf.mono (Function.support_const_smul_subset c f)

noncomputable def Cc_inftyU (d : ℕ+) (U : Set (Fin d → ℝ)) : Submodule ℝ ((Fin d → ℝ) → ℝ) where
  carrier := {f | HasCompactSupport f ∧ tsupport f ⊆ U ∧ ContDiff ℝ ((⊤: ℕ∞) : WithTop ℕ∞) f}

  zero_mem' := by
    refine ⟨HasCompactSupport.zero, ?_, contDiff_zero_fun⟩
    rw [tsupport_zero]
    exact Set.empty_subset U

  add_mem' hf hg :=
    ⟨hf.1.add hg.1,
     (tsupport_add _ _).trans (Set.union_subset hf.2.1 hg.2.1),
     hf.2.2.add hg.2.2⟩

  smul_mem' a f hf:= by
    refine ⟨hf.1.smul, ?_, contDiff_const.smul hf.2.2⟩
    calc tsupport (a • f)
      _ = tsupport ((fun _ => a) * f) := rfl
      _ ⊆ tsupport f := tsupport_mul_subset_right
      _ ⊆ U := hf.2.1


/-- Compactly supported smooth functions on all of `ℝᵈ`, as the special case `U = Set.univ`. -/
noncomputable abbrev Cc_infty (d : ℕ+) : Submodule ℝ ((Fin d → ℝ) → ℝ) :=
  Cc_inftyU d Set.univ


/-! ## Locally Lp function spaces -/

noncomputable def μU (d : ℕ+) (U : Set (Fin d → ℝ)) : Measure (Fin d → ℝ) :=
  volume.restrict U

/-- Functions locally in `Lᵖ` on an open set `U ⊆ ℝᵈ`: those lying in `Lᵖ(C)` for every
    compact `C ⊆ U`. -/
noncomputable def Lp_locU (d : ℕ+) (p : ℝ≥0∞) (U : Set (Fin d → ℝ)) :
    Submodule ℝ ((Fin d → ℝ) →ₘ[μU d U] ℝ) where
  carrier := {f | ∀ (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ U → MemLp f p (volume.restrict C)}

  zero_mem' _C _hC hCU :=
    (memLp_congr_ae (ae_mono (Measure.restrict_mono hCU le_rfl)
      AEEqFun.coeFn_zero)).2 MemLp.zero

  add_mem' hf hg C hC hCU :=
    (memLp_congr_ae (ae_mono (Measure.restrict_mono hCU le_rfl)
      (AEEqFun.coeFn_add _ _))).2 (MemLp.add (hf C hC hCU) (hg C hC hCU))

  smul_mem' a f hf C hC hCU :=
    (memLp_congr_ae (ae_mono (Measure.restrict_mono hCU le_rfl)
      (AEEqFun.coeFn_smul a f))).2 (MemLp.const_smul (hf C hC hCU) a)


/-- Functions locally in `Lᵖ` on all of `ℝᵈ`, as the special case `U = Set.univ`. -/
noncomputable abbrev Lp_loc (d : ℕ+) (p : ℝ≥0∞) : Submodule ℝ ((Fin d → ℝ) →ₘ[volume.restrict Set.univ] ℝ) :=
  Lp_locU d p Set.univ


/-- Membership in `Lp_loc` unfolds to: `MemLp f p (volume.restrict C)` for every compact `C`. -/
@[simp]
lemma mem_Lp_loc_iff {d : ℕ+} {p : ℝ≥0∞} {f : (Fin d → ℝ) →ₘ[μU d Set.univ] ℝ} :
    f ∈ Lp_loc d p ↔ ∀ C : Set (Fin d → ℝ), IsCompact C → MemLp f p (volume.restrict C) := by
  simp only [Lp_loc, Lp_locU]
  constructor
  · intro h C hC; exact h C hC (Set.subset_univ _)
  · intro h C hC _; exact h C hC


/-! ## Local integrability -/

/-- Every function in `Lp_locU d p U` (with `p ≥ 1`) is locally integrable on `U`. -/
lemma LplocLocallyIntegU (d : ℕ+) (p : ℝ≥0∞) (hp : 1 ≤ p) (U : Set (Fin d → ℝ)) (hU : IsOpen U)
    {f : (Fin d → ℝ) →ₘ[volume.restrict U] ℝ} (hf : f ∈ Lp_locU d p U) :
    LocallyIntegrableOn f U volume := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  intro K hKU hK
  letI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  simpa [IntegrableOn] using (hf K hK hKU).integrable (hq1 := hp)

/-- Every function in `Lp_loc d p` (with `p ≥ 1`) is locally integrable on `ℝᵈ`.
    Derived from `LplocLocallyIntegU` applied to `U = Set.univ`. -/
lemma LplocLocallyInteg (d : ℕ+) (p : ℝ≥0∞) (hp : 1 ≤ p)
    {f : (Fin d → ℝ) →ₘ[volume.restrict Set.univ] ℝ} (hf : f ∈ Lp_loc d p) :
    LocallyIntegrable f :=
  locallyIntegrableOn_univ.mp (LplocLocallyIntegU d p hp Set.univ isOpen_univ hf)
