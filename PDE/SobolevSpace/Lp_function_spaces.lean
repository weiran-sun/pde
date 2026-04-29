import Init.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Set.Function
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ENNReal.Basic

import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic

import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Support

import Mathlib.Order.Interval.Set.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Dynamics.Ergodic.MeasurePreserving

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Metrizable

open Real
open Finset
open Fin
open MeasureTheory
open Nat
open MeasurableEquiv
open ENNReal
open Filter Topology
open IntegrableOn
open NNReal


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

/-- Functions locally in `Lᵖ` on an open set `U ⊆ ℝᵈ`: those lying in `Lᵖ(C)` for every
    compact `C ⊆ U`. -/
noncomputable def Lp_locU (d : ℕ+) (p : ℝ≥0∞) (U : Set (Fin d → ℝ)) :
    Submodule ℝ ((Fin d → ℝ) →ₘ[volume] ℝ) where
  carrier := {f | ∀ (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ U → MemLp f p (volume.restrict C)}

  zero_mem' _C _hC _hCU :=
    (memLp_congr_ae AEEqFun.coeFn_zero.restrict).2 MemLp.zero

  add_mem' hf hg C hC hCU :=
    (memLp_congr_ae (AEEqFun.coeFn_add _ _).restrict).2 (MemLp.add (hf C hC hCU) (hg C hC hCU))

  smul_mem' a f hf C hC hCU :=
    (memLp_congr_ae (AEEqFun.coeFn_smul a f).restrict).2 (MemLp.const_smul (hf C hC hCU) a)


/-- Functions locally in `Lᵖ` on all of `ℝᵈ`, as the special case `U = Set.univ`. -/
noncomputable abbrev Lp_loc (d : ℕ+) (p : ℝ≥0∞) : Submodule ℝ ((Fin d → ℝ) →ₘ[volume] ℝ) :=
  Lp_locU d p Set.univ


/-- Membership in `Lp_loc` unfolds to: `MemLp f p (volume.restrict C)` for every compact `C`. -/
@[simp]
lemma mem_Lp_loc_iff {d : ℕ+} {p : ℝ≥0∞} {f : (Fin d → ℝ) →ₘ[volume] ℝ} :
    f ∈ Lp_loc d p ↔ ∀ C : Set (Fin d → ℝ), IsCompact C → MemLp f p (volume.restrict C) := by
  simp [Lp_loc, Lp_locU, Set.subset_univ]


/-! ## Local integrability -/

/-- Every function in `Lp_locU d p U` (with `p ≥ 1`) is locally integrable on `U`. -/
lemma LplocLocallyIntegU (d : ℕ+) (p : ℝ≥0∞) (hp : 1 ≤ p) (U : Set (Fin d → ℝ)) (hU : IsOpen U)
    {f : (Fin d → ℝ) →ₘ[volume] ℝ} (hf : f ∈ Lp_locU d p U) :
    LocallyIntegrableOn f U volume := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  intro K hKU hK
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa [Measure.restrict_apply, Set.inter_univ, MeasurableSet.univ]
        using hK.measure_lt_top⟩
  simpa [IntegrableOn] using (hf K hK hKU).integrable (hq1 := hp)

/-- Every function in `Lp_loc d p` (with `p ≥ 1`) is locally integrable on `ℝᵈ`.
    Derived from `LplocLocallyIntegU` applied to `U = Set.univ`. -/
lemma LplocLocallyInteg (d : ℕ+) (p : ℝ≥0∞) (hp : 1 ≤ p)
    {f : (Fin d → ℝ) →ₘ[volume] ℝ} (hf : f ∈ Lp_loc d p) :
    LocallyIntegrable f :=
  locallyIntegrableOn_univ.mp (LplocLocallyIntegU d p hp Set.univ isOpen_univ hf)
