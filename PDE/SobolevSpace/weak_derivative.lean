import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

import PDE.SobolevSpace.Lp_function_spaces

open MeasureTheory


/-- Standard basis vector sequence in `ℝᵈ` indexed by `s : Fin n → Fin d`,
    used to evaluate iterated Fréchet derivatives along coordinate directions. -/
def unitSeq {d : ℕ+} {n : ℕ} (s : Fin n → Fin d) : Fin n → (Fin d → ℝ) :=
  fun j => Pi.single (s j) (1 : ℝ)


/-! ## Auxiliary Lemmas-/

/-- If `f` is locally integrable on `U` and `ψ ∈ Cc^∞(U)`, then `ψ · f` is integrable
    on all of `ℝᵈ`. This is the key integrability bridge between local and global theories. -/
lemma IntMulLocalintComp {d : ℕ+} (U : Set (Fin d → ℝ))
    {f : (Fin d → ℝ) →ₘ[μU d U] ℝ} {ψ : (Fin d → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f U volume) (ψ_comp : HasCompactSupport ψ)
    (ψ_supp : tsupport ψ ⊆ U) (ψ_cont : Continuous ψ)
    : Integrable (fun x => ψ x * (f : (Fin d → ℝ) →ₘ[μU d U] ℝ) x) volume :=
  (integrableOn_iff_integrable_of_support_subset
    ((Function.support_smul_subset_left ψ f).trans (subset_tsupport ψ))).mp
    (((hf.integrableOn_compact_subset ψ_supp ψ_comp.isCompact).continuousOn_smul
      ψ_cont.continuousOn) ψ_comp)

@[simp]
lemma integral_muU_eq_volume_of_Cc
    {d : ℕ+} {U : Set (Fin d → ℝ)}
    {ψ : (Fin d → ℝ) → ℝ} (hU : IsOpen U) (hψ : ψ ∈ Cc_inftyU d U)
    (g : (Fin d → ℝ) → ℝ) :
    ∫ x, ψ x • g x ∂ μU d U = ∫ x, ψ x • g x ∂ volume := by
      classical
      rw [μU]
      rw [← MeasureTheory.integral_indicator hU.measurableSet]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ U
      · simp [Set.indicator_of_mem hx]
      · have hψx : ψ x = 0 := by
          have hsupp : tsupport ψ ⊆ U := hψ.2.1
          by_contra hne
          exact hx (hsupp (subset_tsupport ψ hne))
        simp [Set.indicator_of_notMem hx, hψx]


/-- The Fréchet derivative `x ↦ (∂ˢψ(x))(unitSeq s)` of a test function `ψ ∈ Cc^∞(U)` again
    lies in `Cc^∞(U)`. This is used to compose the weak derivative definition with itself. -/
lemma FderivCcinfty {d : ℕ+} {n : ℕ} {U : Set (Fin d → ℝ)} (s : Fin n → Fin d)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : ψ ∈ Cc_inftyU d U)
    : (fun x => (iteratedFDeriv ℝ n ψ x) (unitSeq s)) ∈ Cc_inftyU d U := by
       obtain ⟨ψ_comp, ψ_supp, ψ_diff⟩ := hψ
       let eval_at_s := ContinuousMultilinearMap.apply (𝕜 := ℝ) (fun _ => Fin d → ℝ) ℝ (unitSeq s)
       refine ⟨?_, ?_, ?_⟩
       · exact HasCompactSupport.comp_left (hf := HasCompactSupport.iteratedFDeriv (𝕜 := ℝ) ψ_comp n)
                (g := eval_at_s.toLinearMap) (hg := map_zero _)
       · exact (closure_mono (Function.support_comp_subset (map_zero eval_at_s)
                (iteratedFDeriv ℝ n ψ))).trans ((tsupport_iteratedFDeriv_subset n).trans ψ_supp)
       · have h0 : ((⊤: ℕ∞): WithTop ℕ∞) + ((n : ℕ∞): WithTop ℕ∞) ≤ ((⊤: ℕ∞) : WithTop ℕ∞) := by
           simp only [← WithTop.coe_add, top_add]; rfl
         exact (show ContDiff ℝ ((⊤: ℕ∞) : WithTop ℕ∞) (eval_at_s ∘ iteratedFDeriv ℝ n ψ) from
           (contDiff_const.clm_apply contDiff_id).comp (ContDiff.iteratedFDeriv_right ψ_diff h0))


/-- If `∫ ψ · f = ∫ ψ · g` for all `ψ ∈ Cc^∞(U)`, then `f =ᵃᵉ g` on `U`.
    This is the du Bois-Reymond lemma, the key uniqueness engine for weak derivatives. -/
lemma IsOpen.ae_eq_of_integral_contDiff_smul_eq {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
  {f : (Fin d → ℝ) →ₘ[μU d U] ℝ} {g : (Fin d → ℝ) →ₘ[μU d U] ℝ}
  {hf : LocallyIntegrableOn f U volume}
  {hg : LocallyIntegrableOn g U volume}
  (h : ∀ ψ : (Fin d → ℝ) → ℝ, ψ ∈ Cc_inftyU d U →
      ∫ x, ψ x • (f : (Fin d → ℝ) → ℝ) x ∂volume
    = ∫ x, ψ x • (g : (Fin d → ℝ) → ℝ) x ∂volume)
  : f =ᵐ[μU d U] g := by
    have : ∀ᵐ (x : Fin ↑d → ℝ), x ∈ U → f x - g x = 0 := by
      apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hU (hf.sub hg)
      intro ψ ψ_diff ψ_comp ψ_supp
      simp only [Pi.sub_apply, smul_sub]
      rw [integral_sub, sub_eq_zero]
      · exact h ψ ⟨ψ_comp, ψ_supp, ψ_diff⟩
      · exact IntMulLocalintComp U hf ψ_comp ψ_supp ψ_diff.continuous
      · exact IntMulLocalintComp U hg ψ_comp ψ_supp ψ_diff.continuous
    show f =ᵐ[volume.restrict U] g
    rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
    filter_upwards [this] with x hx
    simpa [sub_eq_zero] using hx


/-! ## Weak Derivative in U-/

/-- `IsWeakMultiDerivU U s f Df` asserts that `Df` is the weak derivative of `f` in the
    directions encoded by `s : Fin n → Fin d` on the open set `U`:
    `∫_U f · ∂ˢψ = (-1)ⁿ · ∫_U Df · ψ` for all test functions `ψ ∈ Cc^∞(U)`. -/
noncomputable def IsWeakMultiDerivU {d : ℕ+} {n : ℕ} (U : Set (Fin d → ℝ))
    (s : Fin n → Fin d) (f Df : Lp_locU d 1 U) : Prop :=
  ∀ ψ : (Fin d → ℝ) → ℝ, ψ ∈ Cc_inftyU d U →
    ∫ x, (f : (Fin d → ℝ) → ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s) ∂ μU d U
    = (-1 : ℝ)^n • ∫ x, ψ x • (Df : (Fin d → ℝ) → ℝ) x ∂ μU d U

@[simp]
lemma isWeakMultiDerivU_iff {d : ℕ+} {n : ℕ} {U : Set (Fin d → ℝ)}
    {s : Fin n → Fin d} {f Df : Lp_locU d 1 U} :
    IsWeakMultiDerivU U s f Df ↔
    ∀ ψ : (Fin d → ℝ) → ℝ, ψ ∈ Cc_inftyU d U →
      ∫ x, (f : (Fin d → ℝ) → ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s) ∂ μU d U
      = (-1 : ℝ)^n • ∫ x, ψ x • (Df : (Fin d → ℝ) → ℝ) x ∂ μU d U := Iff.rfl

/-- `f` has a weak multi-derivative in directions `s` on `U` if there exists a locally
    integrable function satisfying the integration-by-parts identity. -/
noncomputable def HasWeakMultiDerivU {d : ℕ+} {n : ℕ} (U : Set (Fin d → ℝ))
    (f : Lp_locU d 1 U) (s : Fin n → Fin d) : Prop :=
  ∃ Df : Lp_locU d 1 U, IsWeakMultiDerivU U s f Df

/-- Uniqueness of weak multi-derivatives on `U`: any two candidates must agree almost everywhere
    on `U`. The proof reduces to the du Bois-Reymond lemma via the defining identity. -/
theorem WeakDerivUniqU {d : ℕ+} {n : ℕ} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {f : Lp_locU d 1 U} {s : Fin n → Fin d}
    {Df1 Df2 : Lp_locU d 1 U}
    (h1 : IsWeakMultiDerivU U s f Df1) (h2 : IsWeakMultiDerivU U s f Df2)
    : ((Df1 : (Fin d → ℝ) →ₘ[μU d U] ℝ) : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict U]
      ((Df2 : (Fin d → ℝ) →ₘ[μU d U] ℝ) : (Fin d → ℝ) → ℝ) := by
      classical

      have LocIntDf1 := by simpa using LplocLocallyIntegU d 1 (le_refl 1) U hU Df1.prop
      have LocIntDf2 := by simpa using LplocLocallyIntegU d 1 (le_refl 1) U hU Df2.prop

      apply IsOpen.ae_eq_of_integral_contDiff_smul_eq
        (hU := hU) (hf := LocIntDf1) (hg := LocIntDf2)
      intro ψ hψ
      have := h2 ψ hψ; rw [h1 ψ hψ] at this
      rw [integral_muU_eq_volume_of_Cc hU hψ (Df1),
          integral_muU_eq_volume_of_Cc hU hψ (Df2)] at this
      simpa using this


/-- The canonical weak multi-derivative on `U`, chosen by `Classical.choose`. -/
noncomputable def WeakmultiderivU {d : ℕ+} {n : ℕ} (U : Set (Fin d → ℝ))
    (f : Lp_locU d 1 U) (s : Fin n → Fin d) (h : HasWeakMultiDerivU U f s) : Lp_locU d 1 U :=
  Classical.choose h

theorem WeakmultiderivU_spec {d : ℕ+} {n : ℕ} (U : Set (Fin d → ℝ))
    (f : Lp_locU d 1 U) (s : Fin n → Fin d) (h : HasWeakMultiDerivU U f s) :
    IsWeakMultiDerivU U s f (WeakmultiderivU U f s h) :=
  Classical.choose_spec h

/-- Any weak multi-derivative `Df` on `U` agrees a.e. with the canonical choice. -/

theorem WeakmultiderivU_unique {d : ℕ+} {n : ℕ} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (s : Fin n → Fin d) (f : Lp_locU d 1 U) (h : HasWeakMultiDerivU U f s)
    (Df : Lp_locU d 1 U) (hDf : IsWeakMultiDerivU U s f Df) :
    (WeakmultiderivU U f s h : (Fin d → ℝ) →ₘ[μU d U] ℝ) =ᵐ[volume.restrict U]
    (Df : (Fin d → ℝ) →ₘ[μU d U] ℝ) := by

    simpa using WeakDerivUniqU hU (WeakmultiderivU_spec U f s h) hDf



/-! ## Linear structure of weak derivatives on U-/

lemma zeroWeakmultiDerivU {d : ℕ+} {n : ℕ} (U : Set (Fin d → ℝ)) (hU : IsOpen U)
    (s : Fin n → Fin d) :
    ∃ h : HasWeakMultiDerivU U (0 : Lp_locU d 1 U) s,
      WeakmultiderivU U (0 : Lp_locU d 1 U) s h
      =ᵐ[μU d U] (0 : (Fin d → ℝ) →ₘ[μU d U] ℝ) := by
    classical
    have hzero : IsWeakMultiDerivU U s (0 : Lp_locU d 1 U) 0 := by
        intro ψ hψ
        have h0_ae : ∀ᵐ x ∂μU d U, ((0 : Lp_locU d 1 U) : (Fin d → ℝ) → ℝ) x = 0 := by
          simpa using AEEqFun.coeFn_zero
        rw [integral_eq_zero_of_ae (h0_ae.mono fun x hx => by rw [hx, zero_smul, Pi.zero_apply]),
            integral_eq_zero_of_ae (h0_ae.mono fun x hx => by rw [hx, smul_zero, Pi.zero_apply]),
          smul_zero]
    let h0 : HasWeakMultiDerivU U (0 : Lp_locU d 1 U) s := ⟨0, hzero⟩
    exact ⟨h0, WeakmultiderivU_unique hU s 0 h0 0 hzero⟩


lemma WeakmultiDerivU_add {d : ℕ+} {n : ℕ} (U : Set (Fin d → ℝ)) (hU : IsOpen U)
    (s : Fin n → Fin d) (f g : Lp_locU d 1 U)
    (hf : HasWeakMultiDerivU U f s) (hg : HasWeakMultiDerivU U g s) :
    ∃ h_add : HasWeakMultiDerivU U (f + g) s,
      WeakmultiderivU U (f + g) s h_add
      =ᵐ[μU d U]
      (WeakmultiderivU U f s hf + WeakmultiderivU U g s hg : (Fin d → ℝ) →ₘ[μU d U] ℝ) := by
      let fdev := WeakmultiderivU U f s hf
      let gdev := WeakmultiderivU U g s hg
      have f1 : IsWeakMultiDerivU U s f (fdev) := Classical.choose_spec hf
      have f2 : IsWeakMultiDerivU U s g (gdev) := Classical.choose_spec hg
      have LI := fun h : Lp_locU d 1 U => LplocLocallyIntegU d 1 le_rfl U hU h.prop
      have dev_sum : IsWeakMultiDerivU U s (f+g) (fdev + gdev)  := by
         intro ψ hψ
         specialize f1 ψ hψ; specialize f2 ψ hψ
         let ψdev := fun x => (iteratedFDeriv ℝ n ψ x) (unitSeq s)
         obtain ⟨ψdev_comp, ψdev_supp, ψdev_diff⟩ := FderivCcinfty s hψ
         have hle : μU d U ≤ volume := by unfold μU; exact Measure.restrict_le_self
         have hf_int : ∀ h : Lp_locU d 1 U, Integrable (fun x =>
              (h : (Fin d → ℝ) →ₘ[μU d U] ℝ) x • ψdev x) (μU d U) := fun h => by
            apply Integrable.mono_measure _ hle
            convert IntMulLocalintComp U (LI h) ψdev_comp ψdev_supp ψdev_diff.continuous using 2
            simp [ψdev, smul_eq_mul, mul_comm]
         rcases hψ with ⟨ψ_comp, ψ_supp, ψ_diff⟩
         have hdev_int : ∀ h : Lp_locU d 1 U, Integrable (fun x =>
            ψ x • (h : (Fin d → ℝ) →ₘ[μU d U] ℝ) x) (μU d U) := fun h => by
          refine Integrable.mono_measure ?_ hle
          convert IntMulLocalintComp U (LI h) ψ_comp ψ_supp ψ_diff.continuous using 2
         calc ∫ x, (f + g : (Fin d → ℝ) →ₘ[μU d U] ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s) ∂ μU d U
              = ∫ x, ((f : (Fin d → ℝ) →ₘ[μU d U] ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s)
                    + (g : (Fin d → ℝ) →ₘ[μU d U] ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s)) ∂ μU d U := by
                  refine integral_congr_ae ?_
                  filter_upwards [AEEqFun.coeFn_add f.1 g.1] with x hx
                  rw [hx, Pi.add_apply, add_smul]
            _ = (-1 : ℝ)^n • ∫ x, ψ x • (fdev + gdev : (Fin d → ℝ) →ₘ[μU d U] ℝ) x ∂ μU d U := by
                  rw [integral_add (hf_int f) (hf_int g), f1, f2, ← smul_add,
                      ← integral_add (μ := μU d U) (by simpa [smul_eq_mul] using hdev_int fdev)
                        (by simpa [smul_eq_mul] using hdev_int gdev)]
                  refine congrArg _ (integral_congr_ae ?_)
                  filter_upwards [AEEqFun.coeFn_add fdev.1 gdev.1] with x hx
                  simp [hx, Pi.add_apply, mul_add]
      exact ⟨⟨fdev + gdev, dev_sum⟩,
               WeakmultiderivU_unique hU s (f+g) ⟨fdev + gdev, dev_sum⟩ (fdev + gdev) dev_sum⟩


lemma WeakmultiDerivU_smul {d : ℕ+} {n : ℕ} (U : Set (Fin d → ℝ)) (hU : IsOpen U)
    (s : Fin n → Fin d) (f : Lp_locU d 1 U) (c : ℝ)
    (hf : HasWeakMultiDerivU U f s) :
    ∃ h_smul : HasWeakMultiDerivU U (c • f) s,
      WeakmultiderivU U (c • f) s h_smul
      =ᵐ[μU d U] (c • WeakmultiderivU U f s hf : (Fin d → ℝ) →ₘ[μU d U] ℝ) := by
      classical
      let fdev := WeakmultiderivU U f s hf
      have f1 : IsWeakMultiDerivU U s f (fdev) := Classical.choose_spec hf
      have dev_smul : IsWeakMultiDerivU U s (c • f) (c • fdev)  := by
         intro ψ hψ
         specialize f1 ψ hψ
         calc ∫ x, (c • f : (Fin d → ℝ) →ₘ[μU d U] ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s) ∂ μU d U
              = ∫ x, c • ((f : (Fin d → ℝ) →ₘ[μU d U] ℝ) x
                    • (iteratedFDeriv ℝ n ψ x) (unitSeq s)) ∂ μU d U := by
                  refine integral_congr_ae ?_
                  filter_upwards [AEEqFun.coeFn_smul c f.1] with x hx
                  simp [hx]; linarith
            _ = _ := by
                  rw [integral_smul, f1, smul_comm, ← integral_smul]
                  refine congrArg _ (integral_congr_ae ?_)
                  filter_upwards [AEEqFun.coeFn_smul c fdev.1] with x hx
                  rw [smul_comm]; congr 1; convert hx.symm using 1
      exact ⟨⟨c • fdev, dev_smul⟩,
            WeakmultiderivU_unique hU s (c • f) ⟨c • fdev, dev_smul⟩ (c • fdev) dev_smul⟩


/-! ## Weak Derivative on ℝᵈ (global theory) -/

/-- `IsWeakMultiDeriv s f Df` asserts that `Df` is the weak multi-derivative of `f` in
    directions `s` on all of `ℝᵈ`. Definitionally equal to `IsWeakMultiDerivU Set.univ s f Df`. -/
noncomputable abbrev IsWeakMultiDeriv {d : ℕ+} {n : ℕ} (s : Fin n → Fin d)
    (f Df : Lp_loc d 1) : Prop :=
  IsWeakMultiDerivU Set.univ s f Df

/-- `f` has a weak multi-derivative in directions `s` on `ℝᵈ`. -/
noncomputable abbrev HasWeakMultiDeriv {d : ℕ+} {n : ℕ} (f : Lp_loc d 1)
    (s : Fin n → Fin d) : Prop :=
  HasWeakMultiDerivU Set.univ f s

/-- Uniqueness of weak multi-derivatives on `ℝᵈ`: follows from `WeakDerivUniqU` applied to
    `U = Set.univ`. The a.e. equality is on `volume` rather than `volume.restrict Set.univ`. -/
theorem WeakDerivUniq {d : ℕ+} {n : ℕ} {f : Lp_loc d 1} {s : Fin n → Fin d}
    {Df1 Df2 : Lp_loc d 1}
    (h1 : IsWeakMultiDeriv s f Df1) (h2 : IsWeakMultiDeriv s f Df2) :
    ((Df1 : (Fin d → ℝ) →ₘ[volume.restrict Set.univ] ℝ) : (Fin d → ℝ) → ℝ)
    =ᵐ[volume]
    ((Df2 : (Fin d → ℝ) →ₘ[volume.restrict Set.univ] ℝ) : (Fin d → ℝ) → ℝ) := by
  have := WeakDerivUniqU isOpen_univ h1 h2
  rwa [Measure.restrict_univ] at this

/-- The canonical weak multi-derivative on `ℝᵈ`. -/
noncomputable abbrev weakmultideriv {d : ℕ+} {n : ℕ} (f : Lp_loc d 1)
    (s : Fin n → Fin d) (h : HasWeakMultiDeriv f s) : Lp_loc d 1 :=
  WeakmultiderivU Set.univ f s h

theorem weakmultideriv_spec {d : ℕ+} {n : ℕ} (f : Lp_loc d 1)
    (s : Fin n → Fin d) (h : HasWeakMultiDeriv f s) :
    IsWeakMultiDeriv s f (weakmultideriv f s h) :=
  WeakmultiderivU_spec Set.univ f s h

/-- Any weak multi-derivative `Df` on `ℝᵈ` agrees a.e. with the canonical choice. -/
theorem weakmultideriv_unique {d : ℕ+} {n : ℕ} (s : Fin n → Fin d) (f : Lp_loc d 1)
    (h : HasWeakMultiDeriv f s) (Df : Lp_loc d 1) (hDf : IsWeakMultiDeriv s f Df) :
    (weakmultideriv f s h : (Fin d → ℝ) →ₘ[volume.restrict Set.univ] ℝ) =ᵐ[volume] (Df : (Fin d → ℝ) →ₘ[volume.restrict Set.univ] ℝ) := by
  have := WeakmultiderivU_unique isOpen_univ s f h Df hDf
  rwa [Measure.restrict_univ] at this
