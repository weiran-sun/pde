import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.MetricSpace.Sequences

import PDE.SobolevSpace.Lp_function_spaces
import PDE.SobolevSpace.weak_derivative
import PDE.SobolevSpace.SobolevSpaces

open MeasureTheory
open ENNReal
open Filter Topology

/-- Hilbert Sobolev space H^k(U) = W^{k,2}(U) on an open set U. -/
@[reducible]
noncomputable def HkU (d : ℕ+) (k : ℕ) (U : Set (Fin d → ℝ)) (hU : IsOpen U) :=
  WkpU d k 2 U hU

/-- The Hilbert Sobolev space on the whole of `ℝᵈ`, as the special case `U = Set.univ`. -/
@[reducible]
noncomputable def Hk (d : ℕ+) (k : ℕ) := Wkp d k 2

/-- product of `HkU` functions is integrable on U -/
lemma HkU.integrable_val_mul {d : ℕ+} {k : ℕ} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f g : HkU d k U hU) :
    Integrable (fun x => (f.val.val : (Fin d → ℝ) → ℝ) x
                       * (g.val.val : (Fin d → ℝ) → ℝ) x) (μU d U) :=
  MemLp.integrable_mul f.property.1 g.property.1

/-- product of weak derivatives of HkU functions is integrable on U -/
lemma HkU.integrable_weakDeriv_mul {d : ℕ+} {k : ℕ} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f g : HkU d k U hU)
    (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    Integrable (fun x => ((WkpU.weakDeriv f n hn s) : (Fin d → ℝ) → ℝ) x
                       * ((WkpU.weakDeriv g n hn s) : (Fin d → ℝ) → ℝ) x) (μU d U) :=
  MemLp.integrable_mul (WkpU.weakDeriv_memLp f n hn s)
                              (WkpU.weakDeriv_memLp g n hn s)

/-- AEEqFun.coeFn_add specialised so the LHS is in the `(f + g).val.val` form,
     matching how the inner-product proof presents its goals. -/
lemma HkU.coeFn_add {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} [Fact (1 ≤ p)] (f g : WkpU d k p U hU) :
    ((f + g).val.val : (Fin d → ℝ) → ℝ)
    =ᵐ[μU d U]
    fun x => (f.val.val : (Fin d → ℝ) → ℝ) x + (g.val.val : (Fin d → ℝ) → ℝ) x :=
  AEEqFun.coeFn_add f.val.val g.val.val

/-- AEEqFun.coeFn_smul similarly specialised -/
lemma HkU.coeFn_smul {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} [Fact (1 ≤ p)]
    (c : ℝ) (f : WkpU d k p U hU) :
    ((c • f).val.val : (Fin d → ℝ) → ℝ)
    =ᵐ[μU d U]
    fun x => c • (f.val.val : (Fin d → ℝ) → ℝ) x :=
  AEEqFun.coeFn_smul c f.val.val

/-- The weak derivative is additive -/
lemma WkpU.weakDeriv_add {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f g : WkpU d k p U hU) (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    ((WkpU.weakDeriv (f + g) n hn s) : (Fin d → ℝ) → ℝ)
    =ᵐ[μU d U]
    fun x => (WkpU.weakDeriv f n hn s : (Fin d → ℝ) → ℝ) x
           + (WkpU.weakDeriv g n hn s : (Fin d → ℝ) → ℝ) x := by
  obtain ⟨_, eq_add⟩ := WeakmultiDerivU_add U hU s f.val g.val
    (WkpU.hasWeakDeriv f n hn s) (WkpU.hasWeakDeriv g n hn s)
  exact eq_add.trans (AEEqFun.coeFn_add (WkpU.weakDeriv f n hn s) (WkpU.weakDeriv g n hn s))

/-- The weak derivative is scalar-linear -/
lemma WkpU.weakDeriv_smul {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (c : ℝ) (f : WkpU d k p U hU) (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    ((WkpU.weakDeriv (c • f) n hn s) : (Fin d → ℝ) → ℝ)
    =ᵐ[μU d U]
    fun x => c • (WkpU.weakDeriv f n hn s : (Fin d → ℝ) → ℝ) x := by
  obtain ⟨_, eq_smul⟩ := WeakmultiDerivU_smul U hU s f.val c (WkpU.hasWeakDeriv f n hn s)
  exact eq_smul.trans (AEEqFun.coeFn_smul c (WkpU.weakDeriv f n hn s))
