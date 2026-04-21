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

import PDE.SobolevSpace.Lp_function_spaces


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



def unitSeq {d : ℕ+} {n : ℕ} (s : Fin n → Fin d) : Fin n → (Fin d → ℝ) :=
  fun j => Pi.single (s j) (1 : ℝ)




/- --------------------------------------------------------------------------------
#                            Auxiliary Lemmas
# ---------------------------------------------------------------------------------

- Lemma: If f is locally integrable on U and ψ is C_c (U), then
-        f * ψ is integrable on ℝᵈ.

- Lemma: If ψ ∈ Cc_infty(U), then its iterated Frechet derivatives are in
         Cc_infty (U)

- Lemma: if ∫ f ψ = ∫ g ψ for all test functions ψ, then f =ᵐ[volume.restrict U] g

# ----------------------------------------------------------------------------------
----------------------------------------------------------------------------------- -/

lemma IntMulLocalintComp {d : ℕ+} (U : Set (Fin d → ℝ))
  {f : (Fin d → ℝ) →ₘ[volume] ℝ} {ψ : (Fin d → ℝ) → ℝ}
  (hf: LocallyIntegrableOn f U volume) (ψ_comp: HasCompactSupport ψ)
  (ψ_supp : tsupport ψ ⊆ U) (ψ_cont: Continuous ψ)
  : Integrable (fun x => ψ x * (f : (Fin d → ℝ) →ₘ[volume] ℝ) x) volume :=

    (integrableOn_iff_integrable_of_support_subset
      ((Function.support_smul_subset_left ψ f).trans (subset_tsupport ψ))).mp
      (((hf.integrableOn_compact_subset ψ_supp ψ_comp.isCompact).continuousOn_smul
        ψ_cont.continuousOn) ψ_comp)


lemma FderivCcinfty {d : ℕ+} {n : ℕ} {U : Set (Fin d → ℝ)} (s : Fin n → Fin d)
   {ψ : (Fin d → ℝ) → ℝ} (hψ : ψ ∈ Cc_inftyU d U)
   : (fun x => (iteratedFDeriv ℝ n ψ x) (unitSeq s)) ∈ Cc_inftyU d U := by

       let ψdev := fun x => (iteratedFDeriv ℝ n ψ x) (unitSeq s)
       obtain ⟨ψ_comp, ψ_supp, ψ_diff⟩ := hψ
       let eval_at_s := ContinuousMultilinearMap.apply (𝕜 := ℝ) (fun _ => Fin d → ℝ) ℝ (unitSeq s)

       have ψdev_comp : HasCompactSupport ψdev := by
        have h_comp := HasCompactSupport.iteratedFDeriv (𝕜 := ℝ) ψ_comp n
        exact HasCompactSupport.comp_left (hf := h_comp) (g := eval_at_s.toLinearMap) (hg := map_zero _)

       have ψdev_supp : tsupport ψdev ⊆ U :=
          (closure_mono (Function.support_comp_subset (map_zero eval_at_s) _)).trans
            ((tsupport_iteratedFDeriv_subset n).trans ψ_supp)

       have ψdev_diff : ContDiff ℝ ((⊤: ℕ∞) : WithTop ℕ∞) ψdev := by
         have h0 : ((⊤: ℕ∞): WithTop ℕ∞) + ((n : ℕ∞): WithTop ℕ∞) ≤ ((⊤: ℕ∞) : WithTop ℕ∞)
           := by simp only [← WithTop.coe_add, top_add]; rfl
         rw [show ψdev = eval_at_s ∘ iteratedFDeriv ℝ n ψ by rfl]
         exact (contDiff_const.clm_apply contDiff_id).comp
               (ContDiff.iteratedFDeriv_right ψ_diff h0)

       exact ⟨ψdev_comp, ψdev_supp, ψdev_diff⟩



lemma IsOpen.ae_eq_of_integral_contDiff_smul_eq {d : ℕ+} {U : Set (Fin d → ℝ)}{hU: IsOpen U}
  {f : (Fin d → ℝ) →ₘ[volume] ℝ} {g : (Fin d → ℝ) →ₘ[volume] ℝ}
  {hf: LocallyIntegrableOn f U volume}
  {hg: LocallyIntegrableOn g U volume}
  (h : ∀ ψ : (Fin d → ℝ) → ℝ, ψ ∈ Cc_inftyU d U →  ∫ x, ψ x • f x ∂volume
      = ∫ x, ψ x • g x ∂volume)
  : f =ᵐ[volume.restrict U] g := by

    have : ∀ᵐ (x : Fin ↑d → ℝ), x ∈ U → f x - g x = 0 := by
      apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hU (hf.sub hg)
      intro ψ ψ_diff ψ_comp ψ_supp
      have Cc_psi : ψ ∈ Cc_inftyU d U := by exact ⟨ψ_comp, ψ_supp, ψ_diff⟩
      simp only [Pi.sub_apply, smul_sub]

      rw [integral_sub, sub_eq_zero]
      · exact h ψ Cc_psi
      · exact IntMulLocalintComp U hf ψ_comp ψ_supp ψ_diff.continuous
      · exact IntMulLocalintComp U hg ψ_comp ψ_supp ψ_diff.continuous

    rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
    filter_upwards [this] with x hx
    simpa [sub_eq_zero] using hx







/- --------------------------------------------------------------------------------
#                           Weak Derivative in U
# ---------------------------------------------------------------------------------

- 1. Definition: weak derivatives

- 2. Main Lemma: Weak derivative is unique

# ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------- -/


noncomputable def IsWeakMultiDerivU {d : ℕ+} {n : ℕ} (U : Set (Fin d → ℝ)) (s : Fin n → Fin d)
  (f : Lp_locU d 1 U) (Df : Lp_locU d 1 U) : Prop :=
   ∀ ψ : (Fin d → ℝ) → ℝ, ψ ∈ Cc_inftyU d U →
    ∫ x, ((f : (Fin d → ℝ) → ℝ) x) •
          ((iteratedFDeriv ℝ n ψ x) (unitSeq (s := s))) ∂volume
      = (-1 : ℝ)^n •
        ∫ x, ((ψ : (Fin d → ℝ) → ℝ) x) • ((Df : (Fin d → ℝ) → ℝ) x) ∂volume


noncomputable def HasWeakMultiDerivU {d : ℕ+} {n : ℕ}(U : Set (Fin d → ℝ))
  (f : Lp_locU d 1 U) (s : Fin n → Fin d) :=
  ∃ (Df : Lp_locU d 1 U), IsWeakMultiDerivU U s f Df


theorem WeakDerivUniqU {d : ℕ+}{n : ℕ} {U : Set (Fin d → ℝ)}(hU: IsOpen U) {f : Lp_locU d 1 U} {s : Fin n → Fin d}
    {Df1 Df2 : Lp_locU d 1 U} (h1 : IsWeakMultiDerivU U s f Df1) (h2 : IsWeakMultiDerivU U s f Df2)
    : ((Df1 : (Fin d → ℝ) →ₘ[volume] ℝ) : (Fin d → ℝ) → ℝ) =ᵐ[volume.restrict U]
      ((Df2 : (Fin d → ℝ) →ₘ[volume] ℝ) : (Fin d → ℝ) → ℝ) := by
    classical
    have LocIntDf1 := by simpa using LplocLocallyIntegU (d := d) (p := 1) (U := U) (f := Df1)
    have LocIntDf2 := by simpa using LplocLocallyIntegU (d := d) (p := 1) (U := U) (f := Df2)
    have IntEqDf12 : ∀ ψ : (Fin d → ℝ) → ℝ, ψ ∈ Cc_inftyU d U →
        ∫ x, (ψ x • (Df1 : (Fin d → ℝ) →ₘ[volume] ℝ) x) ∂volume
        = ∫ x, (ψ x • (Df2 : (Fin d → ℝ) →ₘ[volume] ℝ) x) ∂volume := by
          intro ψ hψ
          have h2' := h2 ψ hψ
          rw [h1 ψ hψ] at h2'
          simpa [smul_eq_mul] using h2'
    exact IsOpen.ae_eq_of_integral_contDiff_smul_eq
           (d := d) (U := U) (hU := hU)
             (hf := LocIntDf1 hU) (hg := LocIntDf2 hU) (h := IntEqDf12)



noncomputable def WeakmultiderivU
    {d : ℕ+} {n : ℕ}(U : Set (Fin d → ℝ))
    (f : Lp_locU d 1 U) (s : Fin n → Fin d)
    (h : HasWeakMultiDerivU U f s) : Lp_locU d 1 U := Classical.choose h



theorem WeakmultiderivU_spec {d : ℕ+} {n : ℕ}(U : Set (Fin d → ℝ))
    (f : Lp_locU d 1 U) (s : Fin n → Fin d)
    (h : HasWeakMultiDerivU U f s) :
    IsWeakMultiDerivU U s f (WeakmultiderivU U f s h) :=
  Classical.choose_spec h


theorem WeakmultiderivU_unique {d : ℕ+} {n : ℕ} {U : Set (Fin d → ℝ)} (hU: IsOpen U)(s : Fin n → Fin d) (f : Lp_locU d 1 U)
  (h : HasWeakMultiDerivU U f s) (Df : Lp_locU d 1 U)
    (hDf : IsWeakMultiDerivU U s f Df) :
    (WeakmultiderivU U f s h : (Fin d → ℝ) →ₘ[volume] ℝ)
    =ᵐ[volume.restrict U] (Df : (Fin d → ℝ) →ₘ[volume] ℝ) := by

    simpa using WeakDerivUniqU hU (WeakmultiderivU_spec U f s h) hDf





/- --------------------------------------------------------------------------------
#                 Linear operations for weak derivatives on U
# ---------------------------------------------------------------------------------

- Lemma.  Zero is weakly differentiable

- Lemma.  If f, g are weakly differentiable then f + g is weakly differentiable

- Lemma. If f is weakly differentiable, then c * f is weakly differentiable

# ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------- -/


lemma zeroWeakmultiDerivU
     {d : ℕ+} {n : ℕ+} (U : Set (Fin d → ℝ)) (hU: IsOpen U) (s : Fin n → Fin d) :
    ∃ h : HasWeakMultiDerivU U (0 : Lp_locU d 1 U) s,
       WeakmultiderivU U (0 : Lp_locU d 1 U) s h =ᵐ[volume.restrict U] (0 : (Fin d → ℝ) →ₘ[volume] ℝ)
      := by
    classical
    have h0 : HasWeakMultiDerivU U (0 : Lp_locU d 1 U) s :=
         ⟨(0 : Lp_locU d 1 U), by intro ψ; simp⟩
    use h0
    have : IsWeakMultiDerivU U s 0 0 := by intro ψ; simp
    apply WeakmultiderivU_unique hU s (0 : Lp_locU d 1 U) h0 (0 : Lp_locU d 1 U) this


lemma WeakmultiDerivU_add
     {d : ℕ+} {n : ℕ+} (U : Set (Fin d → ℝ)) (hU: IsOpen U) (s : Fin n → Fin d)
     (f : Lp_locU d 1 U) (g : Lp_locU d 1 U)
     (hf : HasWeakMultiDerivU U f s) (hg : HasWeakMultiDerivU U g s)
     : ∃ (h_add : HasWeakMultiDerivU U (f+g) s),
         WeakmultiderivU U (f+g) s h_add
          =ᵐ[volume.restrict U]  (WeakmultiderivU U f s hf + WeakmultiderivU U g s hg : (Fin d → ℝ) →ₘ[volume] ℝ)
      := by
      classical

      have fint : LocallyIntegrableOn (f: (Fin d → ℝ) →ₘ[volume] ℝ) U volume
        := LplocLocallyIntegU d 1 (le_refl 1) U hU f.prop
      have gint : LocallyIntegrableOn (g: (Fin d → ℝ) →ₘ[volume] ℝ) U volume
        := LplocLocallyIntegU d 1 (le_refl 1) U hU g.prop

      let fdev := WeakmultiderivU U f s hf
      let gdev := WeakmultiderivU U g s hg

      have fdev_int : LocallyIntegrableOn (fdev: (Fin d → ℝ) →ₘ[volume] ℝ) U volume
        := LplocLocallyIntegU d 1 (le_refl 1) U hU fdev.prop
      have gdev_int : LocallyIntegrableOn (gdev: (Fin d → ℝ) →ₘ[volume] ℝ) U volume
        := LplocLocallyIntegU d 1 (le_refl 1) U hU gdev.prop

      have f1 : IsWeakMultiDerivU U s f (fdev) := Classical.choose_spec hf
      have f2 : IsWeakMultiDerivU U s g (gdev) := Classical.choose_spec hg

      have dev_sum : IsWeakMultiDerivU U s (f+g) (fdev + gdev)  := by
         intro ψ hψ
         simp only [IsWeakMultiDerivU] at f1 f2
         specialize f1 ψ hψ; specialize f2 ψ hψ

         let ψdev := fun x => (iteratedFDeriv ℝ n ψ x) (unitSeq s)
         have ψdev_comp : HasCompactSupport ψdev := (FderivCcinfty s hψ).1
         have ψdev_supp : tsupport ψdev ⊆ U := (FderivCcinfty s hψ).2.1
         have ψdev_cont : Continuous ψdev := (FderivCcinfty s hψ).2.2.continuous

         have hf_int: Integrable (fun x => (f : (Fin d → ℝ) →ₘ[volume] ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s)) volume
           := by
           convert IntMulLocalintComp U fint ψdev_comp ψdev_supp ψdev_cont using 1
           simp_rw [smul_eq_mul, mul_comm]; rfl

         have hg_int: Integrable (fun x => (g : (Fin d → ℝ) →ₘ[volume] ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s)) volume
           := by
           convert IntMulLocalintComp U gint ψdev_comp ψdev_supp ψdev_cont using 1
           simp_rw [smul_eq_mul, mul_comm]; rfl

         rcases hψ with ⟨ψ_comp, ψ_supp, ψ_diff⟩

         have hfdev_int: Integrable (fun x => ψ x * (fdev : (Fin d → ℝ) →ₘ[volume] ℝ) x) volume := by
            exact IntMulLocalintComp U fdev_int ψ_comp ψ_supp ψ_diff.continuous

         have hgdev_int: Integrable (fun x => ψ x * (gdev : (Fin d → ℝ) →ₘ[volume] ℝ) x) volume := by
            exact IntMulLocalintComp U gdev_int ψ_comp ψ_supp ψ_diff.continuous

         calc ∫ x, (f + g : (Fin d → ℝ) →ₘ[volume] ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s)
              = ∫ (x : Fin ↑d → ℝ), ((f : (Fin d → ℝ) →ₘ[volume] ℝ) x + (g : (Fin d → ℝ) →ₘ[volume] ℝ) x)
                                      • (iteratedFDeriv ℝ n ψ x) (unitSeq s) := by
                  apply integral_congr_ae
                  filter_upwards [AEEqFun.coeFn_add f.1 g.1] with x hx
                  rw [hx, Pi.add_apply]
            _ = (-1 : ℝ)^(n:ℕ) • ∫ x, ψ x • (fdev + gdev : (Fin d → ℝ) →ₘ[volume] ℝ) x := by
                  simp_rw [add_smul]; rw [integral_add hf_int hg_int, f1, f2, ← smul_add]
                  rw [← integral_add (by simpa [smul_eq_mul] using hfdev_int)
                                     (by simpa [smul_eq_mul] using hgdev_int)]
                  congr 1
                  apply integral_congr_ae
                  filter_upwards [AEEqFun.coeFn_add fdev.1 gdev.1] with x hx
                  simp [hx, Pi.add_apply, mul_add]
            _ = _ := by simp

      exact ⟨⟨fdev + gdev, dev_sum⟩,
               WeakmultiderivU_unique hU s (f+g) ⟨fdev + gdev, dev_sum⟩ (fdev + gdev) dev_sum⟩



lemma WeakmultiDerivU_smul
     {d : ℕ+} {n : ℕ} (U : Set (Fin d → ℝ)) (hU: IsOpen U) (s : Fin n → Fin d)
     (f : Lp_locU d 1 U) (c : ℝ)
     (hf : HasWeakMultiDerivU U f s)
     : ∃ (h_smul : HasWeakMultiDerivU U (c • f) s),
         WeakmultiderivU U (c • f) s h_smul
          =ᵐ[volume.restrict U]  (c • WeakmultiderivU U f s hf : (Fin d → ℝ) →ₘ[volume] ℝ)
      := by
      classical

      have fint : LocallyIntegrableOn (f: (Fin d → ℝ) →ₘ[volume] ℝ) U volume
        := LplocLocallyIntegU d 1 (le_refl 1) U hU f.prop
      let fdev := WeakmultiderivU U f s hf
      have fdev_int : LocallyIntegrableOn (fdev: (Fin d → ℝ) →ₘ[volume] ℝ) U volume
        := LplocLocallyIntegU d 1 (le_refl 1) U hU fdev.prop
      have f1 : IsWeakMultiDerivU U s f (fdev) := Classical.choose_spec hf

      have dev_smul : IsWeakMultiDerivU U s (c • f) (c • fdev)  := by
         intro ψ hψ
         simp only [IsWeakMultiDerivU] at f1
         specialize f1 ψ hψ

         let ψdev := fun x => (iteratedFDeriv ℝ n ψ x) (unitSeq s)
         have ψdev_comp : HasCompactSupport ψdev := (FderivCcinfty s hψ).1
         have ψdev_supp : tsupport ψdev ⊆ U := (FderivCcinfty s hψ).2.1
         have ψdev_cont : Continuous ψdev := (FderivCcinfty s hψ).2.2.continuous

         rcases hψ with ⟨ψ_comp, ψ_supp, ψ_diff⟩

         have hfdev_int: Integrable (fun x => ψ x * (fdev : (Fin d → ℝ) →ₘ[volume] ℝ) x) volume := by
            exact IntMulLocalintComp U fdev_int ψ_comp ψ_supp ψ_diff.continuous

         calc
           ∫ (x : Fin ↑d → ℝ), (c • f : (Fin d → ℝ) →ₘ[volume] ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s)
            = ∫ (x : Fin ↑d → ℝ), c • ((f : (Fin d → ℝ) →ₘ[volume] ℝ) x
                                      • (iteratedFDeriv ℝ n ψ x) (unitSeq s))
             := by
              apply integral_congr_ae
              filter_upwards [AEEqFun.coeFn_smul c f.1] with x hx
              simp [hx]; linarith
           _ = _ := by
             rw [integral_smul, f1, smul_comm]; congr 1; rw [← integral_smul];
             apply integral_congr_ae
             filter_upwards [AEEqFun.coeFn_smul c fdev.1] with x hx
             rw [smul_comm]; congr 1; convert hx.symm using 1

      exact ⟨⟨c • fdev, dev_smul⟩,
            WeakmultiderivU_unique hU s (c • f) ⟨c • fdev, dev_smul⟩ (c • fdev) dev_smul⟩






/- -----------------------------------------------------------------------------------
#                          Weak Derivative in ℝᵈ
# ------------------------------------------------------------------------------------

- Companion theory on the whole space: existence, uniqueness, and linear structure

# ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------- -/



noncomputable def IsWeakMultiDeriv {d : ℕ+} {n : ℕ} (s : Fin n → Fin d)
  (f : Lp_loc d 1) (Df : Lp_loc d 1) : Prop :=
   ∀ ψ : (Fin d → ℝ) → ℝ, ψ ∈ Cc_infty d →
    ∫ x, ((f : (Fin d → ℝ) → ℝ) x) •
          ((iteratedFDeriv ℝ n ψ x) (unitSeq (s := s))) ∂volume
      = (-1 : ℝ)^n •
        ∫ x, ((ψ : (Fin d → ℝ) → ℝ) x) • ((Df : (Fin d → ℝ) → ℝ) x) ∂volume



noncomputable def HasWeakMultiDeriv {d : ℕ+} {n : ℕ}
  (f : Lp_loc d 1) (s : Fin n → Fin d) :=
  ∃ (Df : Lp_loc d 1), IsWeakMultiDeriv s f Df


-- Uniqueness of weak derivatives
theorem WeakDerivUniq {d : ℕ+} {n : ℕ} {f : Lp_loc d 1} {s : Fin n → Fin d}
    {Df1 Df2 : Lp_loc d 1} (h1 : IsWeakMultiDeriv s f Df1) (h2 : IsWeakMultiDeriv s f Df2) :
    ((Df1 : (Fin d → ℝ) →ₘ[volume] ℝ) : (Fin d → ℝ) → ℝ) =ᵐ[volume]
    ((Df2 : (Fin d → ℝ) →ₘ[volume] ℝ) : (Fin d → ℝ) → ℝ) := by
  classical
  have LocIntDf1 := by simpa using LplocLocallyInteg (d := d) (p := 1) (f := Df1)
  have LocIntDf2 := by simpa using LplocLocallyInteg (d := d) (p := 1) (f := Df2)
  have IntEqDf12 : ∀ ψ : (Fin d → ℝ) → ℝ, ContDiff ℝ (↑⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, (ψ x • (Df1 : (Fin d → ℝ) →ₘ[volume] ℝ) x) ∂volume
      = ∫ x, (ψ x • (Df2 : (Fin d → ℝ) →ₘ[volume] ℝ) x) ∂volume := by
    intro ψ hψ_cont hψ_supp
    have h1_eq := h1 ψ ⟨hψ_supp, hψ_cont⟩
    have h2_eq := h2 ψ ⟨hψ_supp, hψ_cont⟩
    rw [h1_eq] at h2_eq
    simp only [smul_eq_mul] at h2_eq
    exact mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) h2_eq
  simpa using
    ae_eq_of_integral_contDiff_smul_eq
          (μ := volume)
          (hf := LocIntDf1) (hf' := LocIntDf2) (h := IntEqDf12)


noncomputable def weakmultideriv
    {d : ℕ+} {n : ℕ}
    (f : Lp_loc d 1) (s : Fin n → Fin d)
    (h : HasWeakMultiDeriv f s) : Lp_loc d 1 := Classical.choose h


theorem weakmultideriv_spec {d : ℕ+} {n : ℕ}
    (f : Lp_loc d 1) (s : Fin n → Fin d)
    (h : HasWeakMultiDeriv f s) :
    IsWeakMultiDeriv s f (weakmultideriv f s h) := Classical.choose_spec h


theorem weakmultideriv_unique {d : ℕ+} {n : ℕ} (s : Fin n → Fin d) (f : Lp_loc d 1)
  (h : HasWeakMultiDeriv f s) (Df : Lp_loc d 1)
    (hDf : IsWeakMultiDeriv s f Df) :
    (weakmultideriv f s h : (Fin d → ℝ) →ₘ[volume] ℝ) =ᵐ[volume]
    (Df : (Fin d → ℝ) →ₘ[volume] ℝ)
    := by simpa using WeakDerivUniq (weakmultideriv_spec f s h) hDf
