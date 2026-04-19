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

#print Submodule


--namespace Galerkin


-----------Compact Support-------------

lemma HasCompactSupport.smul {α β : Type*}
    [TopologicalSpace α] [Zero β] [SMulWithZero ℝ β]
    {c : ℝ} {f : α → β} (hf : HasCompactSupport f) :
    HasCompactSupport (c • f) :=
     hf.mono (Function.support_const_smul_subset c f)


-- REUSABLE

--------------Lp_loc and Cc_infty in U ⊆ R^d--------------------------------

-- REUSABLE
@[reducible] -- https://proofassistants.stackexchange.com/a/2458
-- Local Lp functions https://en.wikipedia.org/wiki/Locally_integrable_function
-- An AddSubgroup of the (global) L¹ space ((Fin d → ℝ) →ₘ[volume] ℝ).
-- m is a notation of measure “almost everywhere”
-- "volume": mathlib built-in, whose dimension is automatically inferred

noncomputable def Lp_locU (d : ℕ+) (p : ℝ≥0∞) (U : Set (Fin d → ℝ)) : Submodule ℝ ((Fin d → ℝ) →ₘ[volume] ℝ) where
  -- A function belongs to Lp_loc if it lies in ℒᵖ after restricting the Lebesgue measure to every compact set.
  carrier := { f | (∀ (C : Set (Fin d → ℝ)), IsCompact C ∧ (C ⊆ U) → MemLp f p (volume.restrict C))}
  zero_mem' := by
   intro C hC
   exact
     (MeasureTheory.memLp_congr_ae
        (μ := volume.restrict C)
        ((MeasureTheory.AEEqFun.coeFn_zero).restrict)).2
        (MeasureTheory.MemLp.zero
         (α := Fin d → ℝ)
         (μ := volume.restrict C)
         (p := p))
  add_mem' {f g} hf hg := by
   intro C hC
   exact
    (MeasureTheory.memLp_congr_ae
      (μ := volume.restrict C)
      ((AEEqFun.coeFn_add f g).restrict)).2
      (MemLp.add (hf C hC) (hg C hC))
  smul_mem' a f hf:= by
    intro C hC
    exact
    (MeasureTheory.memLp_congr_ae
      (μ := volume.restrict C)
      ((AEEqFun.coeFn_smul a f).restrict)).2
      (MemLp.const_smul (hf C hC) a)

lemma LplocLocallyIntegU (d : ℕ+) (p : ℝ≥0∞) (hp : (1 : ℝ≥0∞) ≤ p)(U : Set (Fin d → ℝ)) (hU : IsOpen U)
   {f : (Fin d → ℝ) →ₘ[volume] ℝ} (Hf : f ∈ Lp_locU d p U)
 : LocallyIntegrableOn f U volume
 := by
  have LCU: IsLocallyClosed U := IsOpen.isLocallyClosed hU
  rw [locallyIntegrableOn_iff LCU]
  intro k hk hk1
  specialize Hf k ⟨hk1, hk⟩
  letI : IsFiniteMeasure (volume.restrict k) :=
    ⟨by
      simpa [Measure.restrict_apply, Set.inter_univ, MeasurableSet.univ]
        using (hk1.measure_lt_top : volume k < ∞)⟩
  simpa [IntegrableOn] using
    ((MemLp.integrable (μ := volume.restrict k) (hq1 := hp)) Hf)


noncomputable def Cc_inftyU (d : ℕ)(U : Set (Fin d → ℝ)) : Submodule ℝ ((Fin d → ℝ) → ℝ) where
  carrier := {f | HasCompactSupport f ∧ (tsupport f ⊆ U) ∧ ContDiff ℝ ((⊤: ℕ∞) : WithTop ℕ∞) f} -- ⊤ unbounded order. The “top” element of WithTop ℕ (natural numbers plus ∞). Upgrades “C^n” to “C^∞”.

  ------------------------
  zero_mem' := by
   refine ⟨HasCompactSupport.zero, ?_, contDiff_zero_fun⟩
   rw [tsupport_zero]
   exact Set.empty_subset U

------------------------
  add_mem' {f g} hf hg := by
    refine ⟨hf.1.add hg.1, ?_, hf.2.2.add hg.2.2⟩
    calc tsupport (f + g)
      _ ⊆ tsupport f ∪ tsupport g := tsupport_add f g
      _ ⊆ U ∪ U := Set.union_subset_union hf.2.1 hg.2.1
      _ = U := Set.union_self U

  ------------------------
  smul_mem' a f hf:= by
    refine ⟨hf.1.smul, ?_, contDiff_const.smul hf.2.2⟩
    have : a • f = (fun _ => a) * f := by
      ext x;
      simp [Pi.smul_apply]
    calc tsupport (a • f)
      _ = tsupport ((fun _ => a) * f) := rfl
      _ ⊆ tsupport f := tsupport_mul_subset_right
      _ ⊆ U := hf.2.1



--------------Lp_loc and Cc_infty in R^d--------------------------------

-- Make Lp_loc into a real vector space
noncomputable def Lp_loc (d : ℕ+) (p : ℝ≥0∞) : Submodule ℝ ((Fin d → ℝ) →ₘ[volume] ℝ) where
  -- A function belongs to Lp_loc if it lies in ℒᵖ after restricting the Lebesgue measure to every compact set.
  carrier := { f | (∀ (C : Set (Fin d → ℝ)), IsCompact C → MemLp f p (volume.restrict C))}
  ------------------------
  zero_mem' := by
    intro C hC
    exact
     (MeasureTheory.memLp_congr_ae
        (μ := volume.restrict C)
        ((MeasureTheory.AEEqFun.coeFn_zero).restrict)).2
        (MeasureTheory.MemLp.zero
         (α := Fin d → ℝ)
         (μ := volume.restrict C)
         (p := p))
  ------------------------
  add_mem' {f g} hf hg := by
    intro C hC
    exact
    (MeasureTheory.memLp_congr_ae
      (μ := volume.restrict C)
      ((AEEqFun.coeFn_add f g).restrict)).2
      (MemLp.add (hf C hC) (hg C hC))
  ------------------------
  smul_mem' a f hf:= by
   intro C hC
   exact
    (MeasureTheory.memLp_congr_ae
      (μ := volume.restrict C)
      ((AEEqFun.coeFn_smul a f).restrict)).2
      (MemLp.const_smul (hf C hC) a)


lemma LplocLocallyInteg (d : ℕ+) (p : ℝ≥0∞) (hp : (1 : ℝ≥0∞) ≤ p) {f : (Fin d → ℝ) →ₘ[volume] ℝ} (Hf : f ∈ Lp_loc d p)
 : LocallyIntegrable (↑f : (Fin ↑d → ℝ) → ℝ)
 := by
  rw [locallyIntegrable_iff]
  intro k hk
  specialize Hf k hk
  letI : IsFiniteMeasure (volume.restrict k) :=
    ⟨by
      simpa [Measure.restrict_apply, Set.inter_univ, MeasurableSet.univ]
        using (hk.measure_lt_top : volume k < ∞)⟩
  simpa [IntegrableOn] using
  ((MemLp.integrable
      (μ := volume.restrict k)
      (f := (↑f : (Fin ↑d → ℝ) → ℝ))
      (hq1 := hp))
      (by simpa [hp, Lp_loc]))





noncomputable def Cc_infty (d : ℕ) : Submodule ℝ ((Fin d → ℝ) → ℝ) where
  carrier := {f | HasCompactSupport f ∧ ContDiff ℝ (↑⊤ : ℕ∞) f} -- ⊤ unbounded order. The “top” element of WithTop ℕ (natural numbers plus ∞). Upgrades “C^n” to “C^∞”.

  ------------------------
  zero_mem' :=
    ⟨HasCompactSupport.zero, contDiff_zero_fun⟩
  ------------------------
  add_mem' hf hg := by
    exact ⟨HasCompactSupport.add hf.1 hg.1, ContDiff.add hf.2 hg.2⟩
  ------------------------
  smul_mem' a f hf:= by
    exact ⟨HasCompactSupport.smul hf.1, ContDiff.const_smul a hf.2⟩



-- theorem contDiff_infty_test : ContDiff 𝕜 ∞ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
--   simp [contDiffOn_univ.symm, contDiffOn_infty]
