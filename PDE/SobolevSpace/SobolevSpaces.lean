import PDE.SobolevSpace.Lp_function_spaces
import PDE.SobolevSpace.weak_derivative

open MeasureTheory
open ENNReal
open Filter Topology
open NNReal


/-! ## Definition of Sobolev Spaces W^{k,p}(U)-/

section Sobolev

variable {d : ℕ+} {k : ℕ} {p : ℝ≥0∞} {U : Set (Fin d → ℝ)} {hU : IsOpen U}

/-- The Sobolev space `W^{k,p}(U)` of locally integrable functions on the open set `U`
whose weak derivatives up to order `k` lie in `L^p(U)`. Defined as a submodule of
the locally integrable functions `Lp_locU d 1 U`. -/
noncomputable def WkpU (d : ℕ+) (k : ℕ) (p : ℝ≥0∞) (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    Submodule ℝ (Lp_locU d 1 U) where
  carrier := {f | MemLp (f : (Fin d → ℝ) → ℝ) p (μU d U) ∧
              ∀ (n : ℕ+), n ≤ k → ∀ (s : Fin (n : ℕ) → Fin d),
              ∃ (h : HasWeakMultiDerivU U f s),
                MemLp ((WeakmultiderivU U f s h) : (Fin d → ℝ) → ℝ) p (μU d U)}

  zero_mem' := by
    refine ⟨(memLp_congr_ae AEEqFun.coeFn_zero).mpr MemLp.zero, fun n _ s => ?_⟩
    obtain ⟨h, h_eq⟩ := zeroWeakmultiDerivU U hU s
    exact ⟨h, (memLp_congr_ae h_eq).mpr ((memLp_congr_ae AEEqFun.coeFn_zero).mpr MemLp.zero)⟩

  add_mem' {f g} hf hg := by
    refine ⟨(memLp_congr_ae (AEEqFun.coeFn_add f.1 g.1)).mpr (hf.1.add hg.1),
            fun n hn s => ?_⟩
    obtain ⟨hf_h, hf_lp⟩ := hf.2 n hn s
    obtain ⟨hg_h, hg_lp⟩ := hg.2 n hn s
    obtain ⟨h_sum, h_sum_ae⟩ := WeakmultiDerivU_add U hU s f g hf_h hg_h
    have sum_lp : MemLp (↑(WeakmultiderivU U f s hf_h + WeakmultiderivU U g s hg_h) :
        (Fin d → ℝ) → ℝ) p (μU d U) :=
      (memLp_congr_ae (AEEqFun.coeFn_add _ _)).mpr (hf_lp.add hg_lp)
    exact ⟨h_sum, (memLp_congr_ae h_sum_ae).mpr sum_lp⟩

  smul_mem' c f hf := by
    refine ⟨(memLp_congr_ae (AEEqFun.coeFn_smul c f.1)).mpr (hf.1.const_smul c),
            fun n hn s => ?_⟩
    obtain ⟨hf_h, hf_lp⟩ := hf.2 n hn s
    obtain ⟨h_smul, h_smul_ae⟩ := WeakmultiDerivU_smul U hU s f c hf_h
    have smul_lp : MemLp (↑(c • WeakmultiderivU U f s hf_h) : (Fin d → ℝ) → ℝ) p (μU d U) :=
      (memLp_congr_ae (AEEqFun.coeFn_smul c _)).mpr (hf_lp.const_smul c)
    exact ⟨h_smul, (memLp_congr_ae h_smul_ae).mpr smul_lp⟩

/-- The Sobolev space `W^{k,p}(ℝᵈ)`, defined as `WkpU d k p` on the whole space. -/
noncomputable def Wkp (d : ℕ+) (k : ℕ) (p : ℝ≥0∞) :
    Submodule ℝ (Lp_locU d 1 Set.univ) :=
     WkpU d k p Set.univ isOpen_univ


/-- `f` has a weak `n`-th derivative along the multi-index `s` of length `n`. -/
noncomputable def WkpU.hasWeakDeriv (f : WkpU d k p U hU) (n : ℕ+) (hn : n ≤ k)
    (s : Fin n → Fin d) : HasWeakMultiDerivU U f.val s :=
  Classical.choose (f.property.2 n hn s)

/-- The `n`-th weak derivative of `f : WkpU d k p U hU` along the multi-index `s`. -/
noncomputable def WkpU.weakDeriv (f : WkpU d k p U hU) (n : ℕ+) (hn : n ≤ k)
    (s : Fin n → Fin d) : (Fin d → ℝ) →ₘ[μU d U] ℝ :=
  WeakmultiderivU U f.val s (WkpU.hasWeakDeriv f n hn s)

/-- The weak derivative `f.weakDeriv n hn s` lies in `Lᵖ(U)`. -/
lemma WkpU.weakDeriv_memLp (f : WkpU d k p U hU) (n : ℕ+) (hn : n ≤ k)
    (s : Fin n → Fin d) :
    MemLp (WkpU.weakDeriv f n hn s : (Fin d → ℝ) → ℝ) p (μU d U) :=
  Classical.choose_spec (f.property.2 n hn s)

/-- The underlying function of an element of `WkpU d k p U hU` is in `ℒp`. -/
lemma WkpU.memLp (f : WkpU d k p U hU) : MemLp f.val.val p (μU d U) :=
  f.property.1

/-- The underlying function of an element of `WkpU d k p U hU` is a.e. strongly measurable. -/
lemma WkpU.aestronglyMeasurable (f : WkpU d k p U hU) :
    AEStronglyMeasurable f.val.val (μU d U) :=
  f.property.1.1


/-! ## Sobolev Space W^{k, p}(U) as a normed space -/

/-- The `eLpNorm` of the `n`-th weak derivative of `f` along the multi-index `s`. -/
noncomputable def WkpU.derivELpNorm {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} (f : WkpU d k p U hU) :
    ∀ (n : ℕ), (Fin n → Fin d) → ℝ≥0∞
  | 0, _ =>
      eLpNorm (f.val : (Fin d → ℝ) → ℝ) p (μU d U)
  | n + 1, s =>
      let nm : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
      if hn : nm ≤ k then
        eLpNorm (WkpU.weakDeriv f nm hn s : (Fin d → ℝ) → ℝ) p (μU d U)
      else 0

/-- The `eLpNorm` of the `n`-th weak derivative of `f` along the multi-index `s`. -/
lemma WkpU.derivELpNorm_ne_top {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} (f : WkpU d k p U hU)
    (n : Fin (k + 1)) (s : Fin n.val → Fin d) :
    WkpU.derivELpNorm f n.val s ≠ ⊤ := by
      rcases n with ⟨n, hn⟩
      cases n with
      | zero => exact f.property.1.eLpNorm_lt_top.ne
      | succ m =>
          simp only [WkpU.derivELpNorm]
          have hn' : (⟨m + 1, Nat.succ_pos m⟩ : ℕ+) ≤ k := Nat.lt_succ_iff.mp hn
          split_ifs with h
          · exact (WkpU.weakDeriv_memLp f _ hn' s).eLpNorm_lt_top.ne
          · contradiction


/-- The W^{k,p}(U) norm as an ENNReal value:
    - `p < ∞`: `(∑_{|s| ≤ k} ‖D^s f‖_{Lp}^p)^{1/p}`
    - `p = ∞`:  `sup_{|s| ≤ k} ‖D^s f‖_{L∞}` -/
noncomputable def WkpU.eNorm {d : ℕ+} (k : ℕ) (p : ℝ≥0∞)
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} (f : WkpU d k p U hU) : ℝ≥0∞ :=
  if p = ⊤ then
    ⨆ n : Fin (k + 1), ⨆ s : Fin n.val → Fin d, WkpU.derivELpNorm f n.val s
  else
    (∑ n : Fin (k + 1), ∑ s : Fin n.val → Fin d,
       WkpU.derivELpNorm f n.val s ^ p.toReal) ^ (1 / p.toReal)

/-- The W^{k,p}(U) norm is finite. -/
lemma WkpU.eNorm_ne_top (f : WkpU d k p U hU) : WkpU.eNorm k p f ≠ ⊤ := by
  simp only [WkpU.eNorm]
  split_ifs
  · have hinner : ∀ n : Fin (k + 1),
        ⨆ s : Fin n.val → Fin d, derivELpNorm f n.val s < ⊤ := fun n => by
      conv_lhs =>
        arg 1; ext s
        rw [← ENNReal.coe_toNNReal (WkpU.derivELpNorm_ne_top f n s)]
      exact ENNReal.iSup_coe_lt_top.mpr (Set.finite_range _).bddAbove
    have houter : ⨆ n : Fin (k + 1),
        ⨆ s : Fin n.val → Fin d, derivELpNorm f n.val s < ⊤ := by
      conv_lhs =>
        arg 1; ext n
        rw [← ENNReal.coe_toNNReal (hinner n).ne]
      exact ENNReal.iSup_coe_lt_top.mpr (Set.finite_range _).bddAbove
    exact houter.ne
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.sum_ne_top.mpr (fun n _ => ENNReal.sum_ne_top.mpr (fun s _ =>
        ENNReal.rpow_ne_top_of_nonneg (by positivity) (WkpU.derivELpNorm_ne_top f n s))))

/-- The W^{k,p}(U) norm as a real value -/
noncomputable def WkpUNorm {d : ℕ+} (k : ℕ) (p : ℝ≥0∞)
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} (f : WkpU d k p U hU) : ℝ :=
    (WkpU.eNorm k p f).toNNReal

/-- The `Norm` instance on `WkpU d k p U hU` -/
noncomputable instance WkpU.instNorm {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} : Norm (WkpU d k p U hU) where
  norm f := WkpUNorm k p f


/-- The W^{k,p}(U) norm is nonnegative -/
lemma WkpUNorm_nonneg {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} (f : WkpU d k p U hU) :
    0 ≤ WkpUNorm k p f := NNReal.coe_nonneg _


/-- If `f` vanishes a.e. on `U` and `g` is supported in `U`, then `∫ f • g ∂μU = 0`. -/
lemma integral_smul_aezero_tsupport
    {U : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ} {g : (Fin d → ℝ) → ℝ}
    (hU : MeasurableSet U)
    (hf : f =ᶠ[ae (μU d U)] 0) (hg : tsupport g ⊆ U) :
    ∫ x, f x • g x ∂ μU d U = 0 := by
  refine integral_eq_zero_of_ae <| ae_of_ae_restrict_of_ae_restrict_compl U ?_ ?_
  · filter_upwards [ae_restrict_of_ae hf] with x hx; simp [hx]
  · rw [ae_restrict_iff' hU.compl]
    refine ae_of_all _ fun x hxc => ?_
    simp [image_eq_zero_of_notMem_tsupport (fun h => hxc (hg h))]

/-- If `f : WkpU d k p U hU` is almost everywhere zero on `U`, then its
Sobolev `eNorm` is zero. -/
lemma WkpU.eNorm_eq_zero_of_ae_zero (hp : p ≠ 0) (f : WkpU d k p U hU)
    (hf : (↑↑↑f : (Fin d → ℝ) → ℝ) =ᶠ[ae (μU d U)] 0) :
    WkpU.eNorm k p f = 0 := by
  have h_zero : ∀ n s, WkpU.derivELpNorm f n s = 0 := by
    intro n s
    cases n with
    | zero =>
        exact (eLpNorm_congr_ae hf).trans eLpNorm_zero
    | succ m =>
        dsimp only [WkpU.derivELpNorm]
        split_ifs with hnk
        · have hweak0 :
              (WkpU.weakDeriv f ⟨m+1, Nat.succ_pos _⟩ hnk s)
              =ᵐ[μU d U] (0 : (Fin d → ℝ) →ₘ[μU d U] ℝ) := by
            apply WeakmultiderivU_unique hU s f.val _ 0
            intro ψ hψ
            rw [integral_smul_aezero_tsupport hU.measurableSet hf
                  (FderivCcinfty s hψ).2.1]
            have hint : ∫ x : Fin ↑d → ℝ,
                    ψ x • ((0 : ((Fin ↑d → ℝ) →ₘ[μU d U] ℝ)) x) ∂ μU d U = 0 := by
              apply integral_eq_zero_of_ae
              filter_upwards [AEEqFun.coeFn_zero
                  (α := Fin ↑d → ℝ) (μ := μU d U) (β := ℝ)] with x hx
              simp [hx]
            simpa [smul_eq_mul] using hint
          rw [eLpNorm_congr_ae (hweak0.trans AEEqFun.coeFn_zero)]
          exact eLpNorm_zero
        · rfl
  simp only [WkpU.eNorm]
  split_ifs with h_top
  · simp [h_zero]
  · have p_pos : 0 < p.toReal := ENNReal.toReal_pos hp h_top
    simp [h_zero, ENNReal.zero_rpow_of_pos p_pos, p_pos]

/-- The W^{k,p}(U) `eNorm` of zero is zero. -/
lemma WkpU.eNorm_zero (hp : p ≠ 0) :
    WkpU.eNorm k p (0 : WkpU d k p U hU) = 0 := by
  apply WkpU.eNorm_eq_zero_of_ae_zero hp
  simpa using
    (AEEqFun.coeFn_zero
      (α := Fin d → ℝ) (μ := μU d U) (β := ℝ))


/-- The W^{k,p}(U) norm of zero is zero. -/
lemma WkpUNorm_zero (hp : p ≠ 0) : WkpUNorm k p (0 : WkpU d k p U hU) = 0 := by
  simp [WkpUNorm, WkpU.eNorm_zero hp]

/-- The W^{k,p}(U) norm is zero iff `eNorm` is zero. -/
lemma WkpUNorm_eq_zero_iff' (f : WkpU d k p U hU) :
    WkpUNorm k p f = 0 ↔ WkpU.eNorm k p f = 0 := by
  simp [WkpUNorm, ENNReal.toNNReal_eq_zero_iff, WkpU.eNorm_ne_top]


/-- The W^{k,p}(U) norm vanishes iff the function is zero a.e.. -/
lemma WkpUNorm_eq_zero_iff (hp : 1 ≤ p) {f : WkpU d k p U hU} :
    WkpUNorm k p f = 0 ↔ f.val.val =ᵐ[μU d U] 0 := by
  have hp0 : p ≠ 0 := (one_pos.trans_le hp).ne'
  rw [WkpUNorm_eq_zero_iff']
  constructor
  · intro hf
    have h0 : eLpNorm (f.val : (Fin d → ℝ) → ℝ) p (μU d U) = 0 := by
      simp only [WkpU.eNorm] at hf
      split_ifs at hf with hpt
      · exact ENNReal.iSup_eq_zero.mp
          (ENNReal.iSup_eq_zero.mp hf ⟨0, k.succ_pos⟩) Fin.elim0
      · rcases ENNReal.rpow_eq_zero_iff.mp hf with ⟨hS, _⟩ | ⟨_, h⟩
        · exact (ENNReal.rpow_eq_zero_iff_of_pos (ENNReal.toReal_pos hp0 hpt)).mp
              (Finset.sum_eq_zero_iff.mp
                (Finset.sum_eq_zero_iff.mp hS ⟨0, k.succ_pos⟩ (Finset.mem_univ _))
                Fin.elim0 (Finset.mem_univ _))
        · exact absurd h (not_lt.mpr (by positivity))
    exact (eLpNorm_eq_zero_iff (WkpU.aestronglyMeasurable f) hp0).mp h0
  · exact fun hf => WkpU.eNorm_eq_zero_of_ae_zero hp0 f hf


/-- Triangle inequality for a single weak-derivative `eLpNorm`. -/
lemma WkpU.derivELpNorm_add_le {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} (hp1 : 1 ≤ p)
    (f g : WkpU d k p U hU) (n : ℕ) (s : Fin n → Fin d) :
    WkpU.derivELpNorm (f + g) n s ≤
      WkpU.derivELpNorm f n s + WkpU.derivELpNorm g n s := by
  match n with
  | 0 =>
    simp only [WkpU.derivELpNorm]
    have hcoe : ((f + g).val : (Fin d → ℝ) → ℝ)
        =ᵐ[μU d U]
        (f.val : (Fin d → ℝ) → ℝ) + (g.val : (Fin d → ℝ) → ℝ) :=
      AEEqFun.coeFn_add f.val.1 g.val.1
    rw [eLpNorm_congr_ae hcoe]
    exact eLpNorm_add_le
      (WkpU.aestronglyMeasurable f)
      (WkpU.aestronglyMeasurable g) hp1
  | n + 1 =>
    simp only [WkpU.derivELpNorm]
    split_ifs with hn
    · set nm : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
      obtain ⟨_, eq_add⟩ := WeakmultiDerivU_add U hU s f.val g.val
        (WkpU.hasWeakDeriv f nm hn s) (WkpU.hasWeakDeriv g nm hn s)
      have heq :
          (WkpU.weakDeriv (f + g) nm hn s : (Fin d → ℝ) → ℝ)
          =ᵐ[μU d U]
          (WkpU.weakDeriv f nm hn s : (Fin d → ℝ) → ℝ)
            + (WkpU.weakDeriv g nm hn s : (Fin d → ℝ) → ℝ) :=
        eq_add.trans (AEEqFun.coeFn_add _ _)
      rw [eLpNorm_congr_ae heq]
      exact eLpNorm_add_le
        (WkpU.weakDeriv_memLp f nm hn s).aestronglyMeasurable
        (WkpU.weakDeriv_memLp g nm hn s).aestronglyMeasurable hp1
    · exact le_self_add

/-- Triangle inequality for `eLpNorm`. -/
lemma WkpU.eNorm_add_le {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} (hp1 : 1 ≤ p)
    (f g : WkpU d k p U hU) :
    WkpU.eNorm k p (f + g) ≤ WkpU.eNorm k p f + WkpU.eNorm k p g := by
    unfold WkpU.eNorm
    split_ifs with hp_top
    · refine iSup_le fun n => iSup_le fun s => ?_
      refine (WkpU.derivELpNorm_add_le hp1 f g n.val s).trans ?_
      exact add_le_add (le_iSup_of_le n (le_iSup _ s)) (le_iSup_of_le n (le_iSup _ s))
    · have hp_pos : 0 < p.toReal :=
        ENNReal.toReal_pos (one_pos.trans_le hp1).ne' hp_top
      let σ := Σ n : Fin (k + 1), Fin n.val → Fin d
      have reindex  := fun h : WkpU d k p U hU =>
        (Fintype.sum_sigma
          (fun i : σ => WkpU.derivELpNorm h i.1.val i.2 ^ p.toReal)).symm
      rw [reindex (f + g), reindex f, reindex g]
      refine le_trans ?_
        (ENNReal.Lp_add_le Finset.univ
          (fun i : σ => WkpU.derivELpNorm f i.1.val i.2)
          (fun i : σ => WkpU.derivELpNorm g i.1.val i.2)
          (ENNReal.toReal_mono hp_top hp1))
      exact ENNReal.rpow_le_rpow
        (Finset.sum_le_sum fun i _ =>
          ENNReal.rpow_le_rpow
            (WkpU.derivELpNorm_add_le hp1 f g i.1.val i.2)
            hp_pos.le)
        (by positivity)

/-- Triangle inequality for the W^{k,p} norm. -/
lemma WkpUNorm_add_le (hp : 1 ≤ p) (f g : WkpU d k p U hU) :
    WkpUNorm k p (f + g) ≤ WkpUNorm k p f + WkpUNorm k p g := by
    unfold WkpUNorm
    exact ENNReal.toReal_le_add
      (WkpU.eNorm_add_le hp f g)
      (WkpU.eNorm_ne_top f)
      (WkpU.eNorm_ne_top g)


/-- Absolute homogeneity for the `Lᵖ norm` of a single weak-derivative `‖c • Dˢf‖ = |c| * ‖Dˢf‖`. -/
lemma WkpU.derivELpNorm_smul {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (c : ℝ) (f : WkpU d k p U hU) (n : ℕ) (s : Fin n → Fin d) :
    WkpU.derivELpNorm (c • f) n s = ‖c‖ₑ * WkpU.derivELpNorm f n s := by
  match n with
  | 0 =>
    simp only [WkpU.derivELpNorm]
    have hcoe : ((c • f).val : (Fin d → ℝ) → ℝ)
        =ᵐ[μU d U] c • (f.val : (Fin d → ℝ) → ℝ) :=
        AEEqFun.coeFn_smul c f.val.1
    rw [eLpNorm_congr_ae hcoe, eLpNorm_const_smul]
  | n + 1 =>
    simp only [WkpU.derivELpNorm]
    split_ifs with hn
    · set nm : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
      obtain ⟨_, eq_smul⟩ := WeakmultiDerivU_smul U hU s f.val c
        (WkpU.hasWeakDeriv f nm hn s)
      have heq : (WkpU.weakDeriv (c • f) nm hn s : (Fin d → ℝ) → ℝ)
          =ᵐ[μU d U] c • (WkpU.weakDeriv f nm hn s : (Fin d → ℝ) → ℝ) :=
        eq_smul.trans (AEEqFun.coeFn_smul c _)
      rw [eLpNorm_congr_ae heq, eLpNorm_const_smul]
    · simp

/-- Absolute homogeneity for `eNorm` . -/
lemma WkpU.eNorm_smul {d : ℕ+} {k : ℕ}{p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (hp1 : p ≥ 1)
    (c : ℝ) (f : WkpU d k p U hU) :
    WkpU.eNorm k p (c • f) = ‖c‖ₑ * WkpU.eNorm k p f := by
  simp only [WkpU.eNorm]
  split_ifs with hp
  · simp_rw [WkpU.derivELpNorm_smul c f]
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun n => ?_
    rw [ENNReal.mul_iSup]
  · have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos
       (ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)) hp
    simp_rw [WkpU.derivELpNorm_smul c f,
             ENNReal.mul_rpow_of_nonneg _ _ hp_pos.le,
             ← Finset.mul_sum]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / p.toReal),
        ← ENNReal.rpow_mul, mul_one_div, div_self hp_pos.ne', ENNReal.rpow_one]

/-- Absolute homogeneity for the W^{k,p} norm. -/
lemma WkpUNorm_smul (hp1 : 1 ≤ p) (c : ℝ) (f : WkpU d k p U hU) :
    WkpUNorm k p (c • f) = |c| * WkpUNorm k p f := by
  simp only [WkpUNorm]
  rw [WkpU.eNorm_smul hp1 c f]
  simp [ENNReal.toNNReal_mul, Real.norm_eq_abs]

/-- The W^{k,p} norm is invariant under negation. -/
lemma WkpUNorm_neg (hp1 : 1 ≤ p) (f : WkpU d k p U hU) :
  WkpUNorm k p (-f) = WkpUNorm k p f := by
    rw [← neg_one_smul ℝ f, WkpUNorm_smul hp1 (-1 : ℝ) f]
    norm_num

/-- Wkp norm equals zero only if the function is zero. -/
lemma WkpU.eq_zero_of_norm_zero (hp : 1 ≤ p) {f : WkpU d k p U hU}
    (hf : WkpUNorm k p f = 0) : f = 0 := by
  apply Subtype.ext; apply Subtype.ext
  exact AEEqFun.ext (((WkpUNorm_eq_zero_iff hp).mp hf).trans
    AEEqFun.coeFn_zero.symm)

/-- The W^{k,p} norm defines an AddGroupNorm on `WkpU d k p U hU`. -/
noncomputable def WkpU.addGroupNorm {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} (hp : 1 ≤ p) :
    AddGroupNorm (WkpU d k p U hU) where
  toFun := WkpUNorm k p
  map_zero' := WkpUNorm_zero (one_pos.trans_le hp).ne'
  add_le' f g := WkpUNorm_add_le hp f g
  neg' := WkpUNorm_neg hp
  eq_zero_of_map_eq_zero' := fun _ => WkpU.eq_zero_of_norm_zero hp


noncomputable instance instNormedAddCommGroup {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} [hp : Fact (1 ≤ p)] :
    NormedAddCommGroup (WkpU d k p U hU) :=
     (WkpU.addGroupNorm hp.out).toNormedAddCommGroup

noncomputable instance instNormedSpace {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} [hp : Fact (1 ≤ p)] :
    NormedSpace ℝ (WkpU d k p U hU) where
  norm_smul_le c f := (WkpUNorm_smul hp.out c f).le

noncomputable instance instCoeFunWkpU {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    CoeFun (WkpU d k p U hU) (fun _ ↦ (Fin d → ℝ) → ℝ) where
  coe := fun f ↦ ↑f.val.val


/-! ## Sobolev Space W^{k, p}(U) as a Banach space -/


/-- The projection `WkpU d k p U hU` → `Lp ℝ p (μU d U)` -/
noncomputable def WkpU.toLp {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f : WkpU d k p U hU) : Lp ℝ p (μU d U) :=
   (WkpU.memLp f).toLp f.val.val

/-- The projection of each single weak-derivative to `Lp ℝ p (μU d U)`. -/
noncomputable def WkpU.derivtoLp {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f : WkpU d k p U hU)
    (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) : Lp ℝ p (μU d U) :=
   (WkpU.weakDeriv_memLp f n hn s).toLp (WkpU.weakDeriv f n hn s)

/-- The `eLpNorm` of `f` is bounded by the Sobolev `eNorm`. -/
lemma WkpU.derivELpNorm_zero_le_eNorm [Fact (1 ≤ p)] (f : WkpU d k p U hU) :
    WkpU.derivELpNorm f 0 Fin.elim0 ≤ WkpU.eNorm k p f := by
  simp only [WkpU.eNorm]
  split_ifs with hp
  · exact le_iSup_of_le ⟨0, k.succ_pos⟩ (le_iSup _ Fin.elim0)
  · simp only [WkpU.derivELpNorm]
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (one_pos.trans_le (Fact.out : 1 ≤ p)).ne' hp
    have hpinv : p.toReal * (1 / p.toReal) = 1 := by field_simp
    conv_lhs =>
      rw [← ENNReal.rpow_one (eLpNorm _ p _), ← hpinv, ENNReal.rpow_mul]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    exact le_trans (b := ∑ s : Fin 0 → Fin d, WkpU.derivELpNorm f 0 s ^ p.toReal)
      (Finset.single_le_sum
        (f := fun s => WkpU.derivELpNorm f 0 s ^ p.toReal)
        (fun _ _ => by positivity) (Finset.mem_univ Fin.elim0))
      (Finset.single_le_sum
        (f := fun n : Fin (k + 1) => ∑ s : Fin n.val → Fin d,
              WkpU.derivELpNorm f n.val s ^ p.toReal)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
        (Finset.mem_univ (⟨0, k.succ_pos⟩ : Fin (k + 1))))

/-- The `Lp` norm of `f` is bounded by the W^{k,p} norm. -/
lemma WkpU.norm_toLp_le [Fact (1 ≤ p)] (f : WkpU d k p U hU) :
    ‖WkpU.toLp f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def]
  simp only [WkpU.toLp]
  rw [eLpNorm_congr_ae (WkpU.memLp f).coeFn_toLp]
  show (eLpNorm (f.val : (Fin d → ℝ) → ℝ) p (μU d U)).toReal ≤ WkpUNorm k p f
  apply (ENNReal.toNNReal_le_toNNReal
       ((WkpU.memLp f).eLpNorm_lt_top.ne)
       (WkpU.eNorm_ne_top f)).mpr
  exact WkpU.derivELpNorm_zero_le_eNorm f


/-- The eLpNorm of a weak derivative equals its derivELpNorm contribution. -/
lemma WkpU.eLpNorm_weakDeriv_eq {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f : WkpU d k p U hU) (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    eLpNorm (WkpU.weakDeriv f n hn s : (Fin d → ℝ) → ℝ) p (μU d U) =
    WkpU.derivELpNorm f n.val s := by
    rcases n with ⟨m | m, hm⟩
    · cases hm
    · simp only [WkpU.weakDeriv, WkpU.derivELpNorm]
      dsimp;
      split_ifs with h
      · rfl
      · exact (h hn).elim


/-- Each weak-derivative eLpNorm is bounded by the Sobolev eNorm. -/
lemma WkpU.derivELpNorm_le_eNorm [Fact (1 ≤ p)]
    (f : WkpU d k p U hU) (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    WkpU.derivELpNorm f n.val s ≤ WkpU.eNorm k p f := by
  simp only [WkpU.eNorm]
  split_ifs with hp
  · exact le_iSup_of_le ⟨n.val, Nat.lt_succ_of_le hn⟩ (le_iSup _ s)
  · have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos (one_pos.trans_le (Fact.out : 1 ≤ p)).ne' hp
    have hpinv : p.toReal * (1 / p.toReal) = 1 := by field_simp
    conv_lhs =>
      rw [← ENNReal.rpow_one (WkpU.derivELpNorm f n.val s), ← hpinv, ENNReal.rpow_mul]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    exact le_trans
      (Finset.single_le_sum (f := fun s' => WkpU.derivELpNorm f n.val s' ^ p.toReal)
        (fun _ _ => by positivity) (Finset.mem_univ s))
      (Finset.single_le_sum
        (f := fun m : Fin (k + 1) => ∑ s' : Fin m.val → Fin d,
              WkpU.derivELpNorm f m.val s' ^ p.toReal)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
        (Finset.mem_univ (⟨n.val, Nat.lt_succ_of_le hn⟩ : Fin (k + 1))))

/-- The `Lp` norm of the `n`-th weak derivative of `f` is bounded by the W^{k,p} norm. -/
lemma WkpU.norm_derivtoLp_le
    [Fact (1 ≤ p)]
    (f : WkpU d k p U hU)
    (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    ‖WkpU.derivtoLp f n hn s‖ ≤ ‖f‖ := by
    rw [Lp.norm_def]
    simp only [WkpU.derivtoLp]
    rw [eLpNorm_congr_ae (WkpU.weakDeriv_memLp f n hn s).coeFn_toLp]
    show (eLpNorm (WkpU.weakDeriv f n hn s : (Fin d → ℝ) → ℝ) p (μU d U)).toReal ≤ WkpUNorm k p f
    apply (ENNReal.toNNReal_le_toNNReal
        (WkpU.weakDeriv_memLp f n hn s).eLpNorm_lt_top.ne
        (WkpU.eNorm_ne_top f)).mpr
    rw [WkpU.eLpNorm_weakDeriv_eq f n hn s]
    exact WkpU.derivELpNorm_le_eNorm f n hn s


lemma WkpU.toLp_sub (f g : WkpU d k p U hU) :
    WkpU.toLp (f - g) = WkpU.toLp f - WkpU.toLp g := by
  apply Lp.ext
  filter_upwards [(WkpU.memLp (f - g)).coeFn_toLp,
                  (WkpU.memLp f).coeFn_toLp,
                  (WkpU.memLp g).coeFn_toLp,
                  Lp.coeFn_sub ((WkpU.memLp f).toLp) ((WkpU.memLp g).toLp),
                  AEEqFun.coeFn_sub f.val.1 g.val.1] with x h1 h2 h3 h4 h5
  simp only [WkpU.toLp, Submodule.coe_sub, Pi.sub_apply] at *
  linarith

/-- The projection of the weak derivative of `f - g` to `Lp` equals the difference
of the projections of the weak derivatives of `f` and `g`. -/
lemma WkpU.derivToLp_sub
    (f g : WkpU d k p U hU)
    (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    WkpU.derivtoLp (f - g) n hn s =
      WkpU.derivtoLp f n hn s - WkpU.derivtoLp g n hn s := by
  apply Lp.ext
  obtain ⟨h_neg, eq_neg⟩ := WeakmultiDerivU_smul U hU s g.val (-1) (WkpU.hasWeakDeriv g n hn s)
  obtain ⟨h_add, eq_add⟩ := WeakmultiDerivU_add U hU s f.val _ (WkpU.hasWeakDeriv f n hn s) h_neg
  have his : IsWeakMultiDerivU U s (f - g).val
      (WeakmultiderivU U (f.val + (-1 : ℝ) • g.val) s h_add) := by
      have hfg : (f - g).val = f.val + (-1 : ℝ) • g.val := by
        ext1; simp [sub_eq_add_neg]
      rw [hfg]; exact Classical.choose_spec h_add
  have key : (WkpU.weakDeriv (f - g) n hn s : (Fin d → ℝ) → ℝ) =ᵐ[μU d U]
      (WkpU.weakDeriv f n hn s : (Fin d → ℝ) → ℝ) - WkpU.weakDeriv g n hn s := by
      have step := WeakmultiderivU_unique hU s _ (WkpU.hasWeakDeriv (f - g) n hn s) _ his
      filter_upwards [step, eq_add, eq_neg,
        AEEqFun.coeFn_add (WeakmultiderivU U f.val s (WkpU.hasWeakDeriv f n hn s) : (Fin d → ℝ) →ₘ[μU d U] ℝ)
                          (WeakmultiderivU U ((-1 : ℝ) • g.val) s h_neg : (Fin d → ℝ) →ₘ[μU d U] ℝ),
        AEEqFun.coeFn_smul (-1 : ℝ) (WeakmultiderivU U g.val s (WkpU.hasWeakDeriv g n hn s) : (Fin d → ℝ) →ₘ[μU d U] ℝ),
        AEEqFun.coeFn_sub (WkpU.weakDeriv f n hn s : (Fin d → ℝ) →ₘ[μU d U] ℝ)
                          (WkpU.weakDeriv g n hn s : (Fin d → ℝ) →ₘ[μU d U] ℝ)]
        with x h1 h2 h3 h4 h5 h6
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, WkpU.weakDeriv] at *
      linarith
  filter_upwards [
    (WkpU.weakDeriv_memLp (f - g) n hn s).coeFn_toLp,
    (WkpU.weakDeriv_memLp f n hn s).coeFn_toLp,
    (WkpU.weakDeriv_memLp g n hn s).coeFn_toLp,
    Lp.coeFn_sub (WkpU.weakDeriv_memLp f n hn s).toLp
                 (WkpU.weakDeriv_memLp g n hn s).toLp,
    key] with x h1 h2 h3 h4 h5
  simp only [WkpU.derivtoLp, Pi.sub_apply] at *
  linarith

/-- If `f i` converges to `g` in `Lᵖ(U)`, then for any test function `ψ ∈ C_c^∞(U)`,
the integrals `∫ f i * ψ ∂μU` converge to `∫ g * ψ ∂μU`. -/
lemma integral_tendsto_of_Lploc_tendsto
    {U : Set (Fin d → ℝ)}
    {p : ℝ≥0∞}
    {ψ : (Fin d → ℝ) → ℝ}
    {f : ℕ → (Fin d → ℝ) → ℝ}
    {g : (Fin d → ℝ) → ℝ}
    (hp : 1 ≤ p)
    (hf : ∀ i, MemLp (f i) p (μU d U))
    (hg : MemLp g p (μU d U))
    (hψ : ψ ∈ Cc_inftyU d U)
    (hconv : Tendsto (fun i => eLpNorm (fun x => f i x - g x) p (μU d U))
            atTop (𝓝 0))
    : Tendsto (fun i => ∫ x, f i x * ψ x ∂μU d U) atTop (𝓝 (∫ x, g x * ψ x ∂μU d U))
    := by

    let q : ℝ≥0∞ := ENNReal.conjExponent p
    haveI : Fact (1 ≤ p) := ⟨hp⟩
    have hpq : p.HolderConjugate q := inferInstance
    letI : p.HolderTriple q 1 := hpq

    have hψ_Lq : MemLp ψ q (μU d U) := by
      haveI : IsFiniteMeasureOnCompacts (μU d U) := by
        unfold μU; infer_instance
      exact (hψ.2.2.continuous).memLp_of_hasCompactSupport hψ.1

    have hInt_g : Integrable (fun x => g x * ψ x) (μU d U) := by
      simpa [Pi.mul_apply] using MemLp.integrable_mul hg hψ_Lq

    have hfg : ∀ i, MemLp (fun x => f i x - g x) p (μU d U)
      := fun i => (hf i).sub hg

    have hInt_diff : ∀ i, Integrable (fun x => (f i x - g x) * ψ x) (μU d U) := by
      intro i
      simpa [Pi.mul_apply] using MemLp.integrable_mul (hfg i) hψ_Lq

    have hstep2 : Tendsto (fun i => ∫ x, (f i x - g x) * ψ x ∂μU d U) atTop (𝓝 0) := by
      set C := eLpNorm ψ q (μU d U)
      have hC_fin : C ≠ ⊤ := hψ_Lq.eLpNorm_lt_top.ne

      have hHolder : ∀ i, ‖∫ x, (f i x - g x) * ψ x ∂μU d U‖ ≤
        (eLpNorm (fun x => f i x - g x) p (μU d U) * C).toReal := fun i => by
        have h1 : ‖∫ x, (f i x - g x) * ψ x ∂μU d U‖ ≤
                  ∫ x, ‖f i x - g x‖ * ‖ψ x‖ ∂μU d U :=
          (norm_integral_le_integral_norm _).trans (le_of_eq (by congr 1; ext x; exact norm_mul _ _))
        have h2 : ∫ x, ‖f i x - g x‖ * ‖ψ x‖ ∂μU d U ≤
                (eLpNorm (fun x => f i x - g x) p (μU d U) * C).toReal := by
              simp_rw [← norm_mul]
              have h_int := hInt_diff i
              calc ∫ x, ‖(f i x - g x) * ψ x‖ ∂μU d U
                  = (eLpNorm (fun x => (f i x - g x) * ψ x) 1 (μU d U)).toReal := by
                      rw [eLpNorm_one_eq_lintegral_enorm]
                      exact (integral_norm_eq_lintegral_enorm h_int.aestronglyMeasurable)
                _ ≤ (eLpNorm (fun x => f i x - g x) p (μU d U) * C).toReal := by
                      have hR_ne_top :
                          eLpNorm (fun x => f i x - g x) p (μU d U) * C ≠ ⊤ := by
                        exact ENNReal.mul_ne_top (hfg i).eLpNorm_lt_top.ne hC_fin
                      exact
                        (ENNReal.toReal_le_toReal
                          (memLp_one_iff_integrable.mpr h_int).eLpNorm_lt_top.ne
                          hR_ne_top).mpr
                          (by
                            simpa [C, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
                              (MeasureTheory.eLpNorm_smul_le_mul_eLpNorm
                                (μ := μU d U)
                                (p := p) (q := q) (r := 1)
                                (f := ψ)
                                hψ_Lq.aestronglyMeasurable
                                (hfg i).aestronglyMeasurable))
        exact h1.trans h2
      exact squeeze_zero_norm hHolder (by
        simp_rw [ENNReal.toReal_mul]
        simpa using ((ENNReal.tendsto_toReal zero_ne_top).comp hconv).mul_const C.toReal)

    have heq : ∀ i, ∫ x, f i x * ψ x ∂μU d U =
        ∫ x, (f i x - g x) * ψ x ∂μU d U + ∫ x, g x * ψ x ∂μU d U := fun i => by
      rw [← integral_add (hInt_diff i) hInt_g]
      congr 1; ext x; ring
    simp_rw [heq]
    simpa using hstep2.add tendsto_const_nhds

/-- A discrete Minkowski inequality: for `p ≥ 1` and a finite sequence `a : Fin n → ℝ≥0`,
the `ℓᵖ` norm of `a` is bounded above by the sum of its entries. -/
lemma NNReal.rpow_sum_le_sum {p : ℝ} (hp : 1 ≤ p) :
    ∀ n : ℕ, 1 ≤ n → ∀ a : Fin n → ℝ≥0,
    Real.rpow (∑ i : Fin n, Real.rpow (a i : ℝ) p) (1 / p) ≤ ∑ i : Fin n, (a i : ℝ) := by
  intro n hn a
  have hp0 : p ≠ 0 := by linarith
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    show ((a 0 : ℝ) ^ p) ^ (1 / p) ≤ (a 0 : ℝ)
    rw [← Real.rpow_mul (NNReal.coe_nonneg _), mul_one_div, div_self hp0, Real.rpow_one]
  | succ n hn ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    set A := ∑ i : Fin n, (a i.castSucc : ℝ) ^ p
    set B := (a (Fin.last n) : ℝ)
    have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _
    have hB : 0 ≤ B := NNReal.coe_nonneg _
    have hApow : (A ^ (1 / p)) ^ p = A := by
      rw [← Real.rpow_mul hA, one_div, inv_mul_cancel₀ hp0, Real.rpow_one]
    have hsub : (A + B ^ p) ^ (1 / p) ≤ A ^ (1 / p) + B := by
      have h := Real.rpow_add_rpow_le_add (Real.rpow_nonneg hA (1 / p)) hB hp
      rwa [hApow] at h
    calc (A + B ^ p) ^ (1 / p)
        ≤ A ^ (1 / p) + B := hsub
      _ ≤ ∑ i : Fin n, (a i.castSucc : ℝ) + B :=
          add_le_add_left
            (show A ^ (1 / p) ≤ ∑ i : Fin n, (a i.castSucc : ℝ) from ih (a ∘ Fin.castSucc)) _

/-- Convergence in `W^{k,p}(U)` is equivalent to convergence of each weak-derivative
`eLpNorm` component to zero: `fₙ → f` in `W^{k,p}` if and only if
`‖D^s(fₙ - f)‖_{Lp} → 0` for all multi-indices `s` with `|s| ≤ k`. -/
lemma WkpU.tendsto_iff_all_derivELpNorm
    [Fact (1 ≤ p)] {fₙ : ℕ → WkpU d k p U hU} {f : WkpU d k p U hU} :
    Tendsto fₙ atTop (𝓝 f) ↔
      ∀ (n : Fin (k + 1)) (s : Fin n.val → Fin d),
        Tendsto (fun j => WkpU.derivELpNorm (fₙ j - f) n.val s) atTop (𝓝 0) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_iff_norm_sub_tendsto_zero]; simp only [sub_zero]
  have hle : ∀ (g : WkpU d k p U hU) (n : Fin (k + 1)) (s : Fin n.val → Fin d),
      (WkpU.derivELpNorm g n.val s).toReal ≤ ‖g‖ := fun g n s =>
    (ENNReal.toNNReal_le_toNNReal (WkpU.derivELpNorm_ne_top g n s) (WkpU.eNorm_ne_top g)).mpr <| by
      rcases n with ⟨m, hm⟩; cases m with
      | zero   => exact WkpU.derivELpNorm_zero_le_eNorm g
      | succ m => exact WkpU.derivELpNorm_le_eNorm g ⟨m+1, Nat.succ_pos m⟩ (Nat.lt_succ_iff.mp hm) s
  have hnorm : ∀ (g : WkpU d k p U hU), ‖g‖ ≤
      ∑ n : Fin (k+1), ∑ s : Fin n.val → Fin d, (WkpU.derivELpNorm g n.val s).toReal := by
    intro g
    show (WkpU.eNorm k p g).toReal ≤ _
    simp only [WkpU.eNorm]
    split_ifs with hp_top
    · have hmono := ENNReal.toReal_mono
        (ENNReal.sum_ne_top.mpr fun n _ => ENNReal.sum_ne_top.mpr fun s _ =>
          WkpU.derivELpNorm_ne_top g n s)
        (iSup_le fun n => iSup_le fun s =>
          (Finset.single_le_sum (f := fun s' : Fin n.val → Fin ↑d => WkpU.derivELpNorm g n.val s')
            (fun _ _ => zero_le) (Finset.mem_univ s)).trans
          (Finset.single_le_sum (f := fun n' : Fin (k+1) =>
            ∑ s' : Fin n'.val → Fin ↑d, WkpU.derivELpNorm g n'.val s')
            (fun _ _ => Finset.sum_nonneg fun _ _ => zero_le) (Finset.mem_univ n)))
      simp_rw [ENNReal.toReal_sum (fun n _ => ENNReal.sum_ne_top.mpr fun s _ =>
          WkpU.derivELpNorm_ne_top g n s),
        ENNReal.toReal_sum (fun s _ => WkpU.derivELpNorm_ne_top g _ s)] at hmono; exact hmono
    · have hp1 : 1 ≤ p.toReal := ENNReal.toReal_mono hp_top (Fact.out : 1 ≤ p)
      have hp_pos : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hp1
      rw [← ENNReal.toReal_rpow, ENNReal.toReal_sum (fun n _ => ENNReal.sum_ne_top.mpr fun s _ =>
          ENNReal.rpow_ne_top_of_nonneg hp_pos.le (WkpU.derivELpNorm_ne_top g n s))]
      simp_rw [ENNReal.toReal_sum (fun s _ => ENNReal.rpow_ne_top_of_nonneg hp_pos.le
          (WkpU.derivELpNorm_ne_top g _ s)), ← ENNReal.toReal_rpow]
      haveI : Nonempty (Σ n : Fin (k+1), Fin n.val → Fin ↑d) := ⟨⟨⟨0, k.succ_pos⟩, Fin.elim0⟩⟩
      let e := Fintype.equivFin (Σ n : Fin (k + 1), Fin n.val → Fin ↑d)
      rw [(Fintype.sum_sigma (fun i : Σ n : Fin (k+1), Fin n.val → Fin ↑d =>
              (WkpU.derivELpNorm g i.1.val i.2).toReal ^ p.toReal)).symm,
          (Fintype.sum_sigma (fun i : Σ n : Fin (k+1), Fin n.val → Fin ↑d =>
              (WkpU.derivELpNorm g i.1.val i.2).toReal)).symm,
          ← e.symm.sum_comp _, ← e.symm.sum_comp _]
      exact NNReal.rpow_sum_le_sum hp1 _ Fintype.card_pos
        (fun j => ⟨(WkpU.derivELpNorm g (e.symm j).1.val (e.symm j).2).toReal,
                    ENNReal.toReal_nonneg⟩)
  constructor
  · intro h n s
    have hreal : Tendsto (fun j =>
          (WkpU.derivELpNorm (fₙ j - f) n.val s).toReal) atTop (𝓝 0) :=
        squeeze_zero (fun _ => ENNReal.toReal_nonneg)
          (fun j => by exact_mod_cast hle (fₙ j - f) n s) h
    simpa [ENNReal.ofReal_toReal (WkpU.derivELpNorm_ne_top _ n s)] using
        ENNReal.tendsto_ofReal hreal
  · intro h
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => hnorm (fₙ j - f)) ?_
    simpa using tendsto_finsetSum Finset.univ fun n _ =>
      tendsto_finsetSum Finset.univ fun s _ =>
        (ENNReal.tendsto_toReal zero_ne_top).comp (h n s)

lemma WkpU.derivELpNorm_zero_sub_eq_toLp_norm
    [Fact (1 ≤ p)]
    (f g : WkpU d k p U hU) :
    WkpU.derivELpNorm (f - g) 0 Fin.elim0 =
      ENNReal.ofReal ‖WkpU.toLp f - WkpU.toLp g‖ := by
  rw [← WkpU.toLp_sub, Lp.norm_def]
  simp only [WkpU.derivELpNorm]
  rw [← eLpNorm_congr_ae (f - g).property.1.coeFn_toLp]
  exact (ENNReal.ofReal_toReal
    (Lp.memLp (WkpU.toLp (f - g))).eLpNorm_lt_top.ne).symm

lemma WkpU.derivELpNorm_sub_eq_derivtoLp_norm
    [Fact (1 ≤ p)]
    (f g : WkpU d k p U hU)
    (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    WkpU.derivELpNorm (f - g) n.val s =
      ENNReal.ofReal ‖WkpU.derivtoLp f n hn s -
        WkpU.derivtoLp g n hn s‖ := by
  rw [← WkpU.derivToLp_sub, Lp.norm_def]
  simp only [WkpU.derivtoLp]
  rw [eLpNorm_congr_ae
    (WkpU.weakDeriv_memLp (f - g) n hn s).coeFn_toLp,
    WkpU.eLpNorm_weakDeriv_eq]
  exact (ENNReal.ofReal_toReal
    (WkpU.derivELpNorm_ne_top (f - g)
      ⟨n.val, Nat.lt_succ_of_le hn⟩ s)).symm


lemma Lp.mem_Lp_locU [Fact (1 ≤ p)]
    (f : Lp ℝ p (μU d U)) :
    (f : (Fin d → ℝ) →ₘ[μU d U] ℝ) ∈ Lp_locU d 1 U :=
  fun C hC hCU => by
    haveI : IsFiniteMeasure (volume.restrict C) :=
      ⟨by simpa using hC.measure_lt_top⟩
    exact (Lp.memLp f).mono_measure
      (Measure.restrict_mono hCU le_rfl) |>.mono_exponent Fact.out


/-- A Cauchy sequence in `W^{k,p}(U)` induces a Cauchy sequence in `Lp` via `toLp`. -/
lemma WkpU.cauchySeq_toLp [Fact (1 ≤ p)]
    {fₙ : ℕ → WkpU d k p U hU}
    (hcauchy : CauchySeq fₙ) :
    CauchySeq (fun n => WkpU.toLp (fₙ n)) :=
  hcauchy.map <| LipschitzWith.uniformContinuous (K := 1) fun f g => by
    rw [edist_dist, edist_dist, ENNReal.coe_one, one_mul,
        dist_eq_norm, dist_eq_norm, ← WkpU.toLp_sub]
    exact ENNReal.ofReal_le_ofReal (WkpU.norm_toLp_le (f - g))


/-- A Cauchy sequence in `W^{k,p}(U)` induces a Cauchy sequence in `Lp`
for each weak derivative component. -/
lemma WkpU.cauchySeq_derivtoLp [Fact (1 ≤ p)]
    {fₙ : ℕ → WkpU d k p U hU}
    (hcauchy : CauchySeq fₙ)
    (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    CauchySeq (fun j => WkpU.derivtoLp (fₙ j) n hn s) := by
  have huc : UniformContinuous (fun f : WkpU d k p U hU =>
      WkpU.derivtoLp f n hn s) :=
    LipschitzWith.uniformContinuous (K := 1) fun f g => by
      rw [edist_dist, edist_dist, ENNReal.coe_one, one_mul,
          dist_eq_norm, dist_eq_norm, ← WkpU.derivToLp_sub f g n hn s]
      exact ENNReal.ofReal_le_ofReal (WkpU.norm_derivtoLp_le (f - g) n hn s)
  have key := hcauchy.map huc
  rwa [Filter.map_map] at key


/-- The IBP identity passes to the limit. -/
lemma WkpU.ibp_tendsto [Fact (1 ≤ p)]
    {fₙ : ℕ → WkpU d k p U hU}
    (g : Lp ℝ p (μU d U))
    (hg : Tendsto (fun n => WkpU.toLp (fₙ n)) atTop (𝓝 g))
    (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d)
    (g_ns : Lp ℝ p (μU d U))
    (hg_ns : Tendsto (fun j => WkpU.derivtoLp (fₙ j) n hn s) atTop (𝓝 g_ns))
    (ψ : (Fin d → ℝ) → ℝ) (hψ : ψ ∈ Cc_inftyU d U) :
    ∫ x, (g : (Fin d → ℝ) → ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s) ∂ μU d U =
    (-1 : ℝ)^(n : ℕ) • ∫ x, ψ x • (g_ns : (Fin d → ℝ) → ℝ) x ∂ μU d U := by
  have hconv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ g).mp hg
  have hconv_ns := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ g_ns).mp hg_ns
  have hibp_j : ∀ j,
      ∫ x, (fₙ j : (Fin d → ℝ) → ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s) ∂ μU d U =
      (-1 : ℝ)^(n : ℕ) • ∫ x, ψ x •
        (WkpU.derivtoLp (fₙ j) n hn s : (Fin d → ℝ) → ℝ) x ∂ μU d U := fun j => by
    rw [WeakmultiderivU_spec U (fₙ j).val s (WkpU.hasWeakDeriv (fₙ j) n hn s) ψ hψ]
    congr 1; apply integral_congr_ae
    filter_upwards [(WkpU.weakDeriv_memLp (fₙ j) n hn s).coeFn_toLp] with x hx
    simp only [WkpU.derivtoLp, WkpU.weakDeriv] at hx ⊢; rw [hx]
  have hlhs : Tendsto (fun j => ∫ x, (fₙ j : (Fin d → ℝ) → ℝ) x •
        (iteratedFDeriv ℝ n ψ x) (unitSeq s) ∂ μU d U) atTop
      (𝓝 (∫ x, (g : (Fin d → ℝ) → ℝ) x •
        (iteratedFDeriv ℝ n ψ x) (unitSeq s) ∂ μU d U)) := by
    have h := integral_tendsto_of_Lploc_tendsto Fact.out
      (fun j => Lp.memLp (WkpU.toLp (fₙ j))) (Lp.memLp g)
      (FderivCcinfty s hψ) hconv
    simp_rw [← smul_eq_mul] at h
    have hae : ∀ j, (WkpU.toLp (fₙ j) : (Fin d → ℝ) → ℝ) =ᵐ[μU d U]
      (fₙ j : (Fin d → ℝ) → ℝ) := fun j =>
        (WkpU.memLp (fₙ j)).coeFn_toLp
    exact h.congr fun j => integral_congr_ae
      ((hae j).mono fun x hx => by simp [hx])
  have hrhs : Tendsto (fun j =>
        (-1 : ℝ)^(n : ℕ) • ∫ x, ψ x •
          (WkpU.derivtoLp (fₙ j) n hn s : (Fin d → ℝ) → ℝ) x ∂ μU d U) atTop
      (𝓝 ((-1 : ℝ)^(n : ℕ) •
        ∫ x, ψ x • (g_ns : (Fin d → ℝ) → ℝ) x ∂ μU d U)) := by
    apply Filter.Tendsto.const_smul
    have h := integral_tendsto_of_Lploc_tendsto Fact.out
      (fun j => Lp.memLp (WkpU.derivtoLp (fₙ j) n hn s))
      (Lp.memLp g_ns) hψ hconv_ns
    simp_rw [smul_eq_mul, mul_comm] at h ⊢
    exact h
  exact (tendsto_nhds_unique (hrhs.congr fun j => (hibp_j j).symm) hlhs).symm

/-- Given an `Lp` limit `g` and derivative limits `g_ns`, package them into
a `WkpU` element. -/
lemma WkpU.limit_mem [Fact (1 ≤ p)]
    (g : Lp ℝ p (μU d U))
    (g_ns : ∀ (n : ℕ+), n ≤ k → (Fin n → Fin d) → Lp ℝ p (μU d U))
    (hid : ∀ (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d),
      ∀ ψ ∈ Cc_inftyU d U,
        ∫ x, (g : (Fin d → ℝ) → ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s) ∂ μU d U =
        (-1 : ℝ)^(n : ℕ) • ∫ x, ψ x •
          (g_ns n hn s : (Fin d → ℝ) → ℝ) x ∂ μU d U) :
    (⟨g, Lp.mem_Lp_locU g⟩ : Lp_locU d 1 U) ∈ (WkpU d k p U hU : Submodule ℝ _) := by
  refine ⟨Lp.memLp g, fun n hn s => ?_⟩
  have hg_ns_loc : (g_ns n hn s : (Fin d → ℝ) →ₘ[μU d U] ℝ) ∈ Lp_locU d 1 U :=
    Lp.mem_Lp_locU (g_ns n hn s)
  let g_ns_loc : Lp_locU d 1 U := ⟨g_ns n hn s, hg_ns_loc⟩
  let hhas : HasWeakMultiDerivU U ⟨g, Lp.mem_Lp_locU g⟩ s := ⟨g_ns_loc, hid n hn s⟩
  exact ⟨hhas, (memLp_congr_ae
    (WeakmultiderivU_unique hU s _ hhas g_ns_loc (hid n hn s))).mpr
    (Lp.memLp (g_ns n hn s))⟩

/-- A Cauchy sequence in `W^{k,p}(U)` has a limit `f_lim` in `W^{k,p}(U)`, with the `toLp`
and `derivtoLp` projections of the sequence converging to those of `f_lim`. -/
lemma WkpU.limit_of_cauchySeq [Fact (1 ≤ p)]
    {fₙ : ℕ → WkpU d k p U hU}
    (hcauchy : CauchySeq fₙ) :
    ∃ f_lim : WkpU d k p U hU,
      Tendsto (fun n => WkpU.toLp (fₙ n)) atTop (𝓝 (WkpU.toLp f_lim)) ∧
      ∀ (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d),
        Tendsto (fun j => WkpU.derivtoLp (fₙ j) n hn s) atTop
          (𝓝 (WkpU.derivtoLp f_lim n hn s)) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (WkpU.cauchySeq_toLp hcauchy)
  have hg_ns : ∀ (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d),
      ∃ g_ns : Lp ℝ p (μU d U),
        Tendsto (fun j => WkpU.derivtoLp (fₙ j) n hn s) atTop (𝓝 g_ns)
        ∧ ∀ ψ ∈ Cc_inftyU d U,
          ∫ x, (g : (Fin d → ℝ) → ℝ) x • (iteratedFDeriv ℝ n ψ x) (unitSeq s) ∂ μU d U
          = (-1 : ℝ)^(n : ℕ) • ∫ x, ψ x • (g_ns : (Fin d → ℝ) → ℝ) x ∂ μU d U :=
    fun n hn s => by
      obtain ⟨g_ns, hg_ns_lim⟩ :=
        cauchySeq_tendsto_of_complete (WkpU.cauchySeq_derivtoLp hcauchy n hn s)
      exact ⟨g_ns, hg_ns_lim, WkpU.ibp_tendsto g hg n hn s g_ns hg_ns_lim⟩
  let f_lim : WkpU d k p U hU := ⟨⟨g, Lp.mem_Lp_locU g⟩,
    WkpU.limit_mem g
      (fun n hn s => (hg_ns n hn s).choose)
      (fun n hn s => (hg_ns n hn s).choose_spec.2)⟩
  refine ⟨f_lim,
    by simp_rw [show WkpU.toLp f_lim = g from Lp.ext (Lp.memLp g).coeFn_toLp]; exact hg,
    fun n hn s => ?_⟩
  have hfl_deriv : WkpU.derivtoLp f_lim n hn s = (hg_ns n hn s).choose := by
    let g_ns := (hg_ns n hn s).choose
    have hid := (hg_ns n hn s).choose_spec.2
    have hg_ns_loc : (g_ns : (Fin d → ℝ) →ₘ[μU d U] ℝ) ∈ Lp_locU d 1 U :=
      Lp.mem_Lp_locU g_ns
    apply Lp.ext
    filter_upwards [(WkpU.weakDeriv_memLp f_lim n hn s).coeFn_toLp,
        WeakmultiderivU_unique hU s f_lim.val (WkpU.hasWeakDeriv f_lim n hn s)
          ⟨(g_ns : (Fin d → ℝ) →ₘ[μU d U] ℝ), hg_ns_loc⟩ hid,
        (Lp.memLp g_ns).coeFn_toLp] with x h1 h2 h3
    simp only [WkpU.derivtoLp, WkpU.weakDeriv] at h1 ⊢
    rw [h1]; exact h2
  rw [hfl_deriv]
  exact (hg_ns n hn s).choose_spec.1

/-- Each `derivELpNorm` component of `fₙ - f_lim` tends to zero. -/
lemma WkpU.derivELpNorm_tendsto_zero [Fact (1 ≤ p)]
    {fₙ : ℕ → WkpU d k p U hU}
    (f_lim : WkpU d k p U hU)
    (hg : Tendsto (fun n => WkpU.toLp (fₙ n)) atTop (𝓝 (WkpU.toLp f_lim)))
    (hg_ns : ∀ (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d),
      Tendsto (fun j => WkpU.derivtoLp (fₙ j) n hn s) atTop
        (𝓝 (WkpU.derivtoLp f_lim n hn s))) :
    ∀ (n : Fin (k + 1)) (s : Fin n.val → Fin d),
      Tendsto (fun j => WkpU.derivELpNorm (fₙ j - f_lim) n.val s) atTop (𝓝 0) := by
  intro ⟨m, hm⟩ s
  cases m with
  | zero =>
    have hs : s = Fin.elim0 := Subsingleton.elim _ _
    subst hs
    have h0 : Tendsto (fun j => ‖WkpU.toLp (fₙ j) - WkpU.toLp f_lim‖) atTop (𝓝 0) := by
      simp_rw [← dist_eq_norm]
      exact tendsto_iff_dist_tendsto_zero.mp hg
    have hz : Tendsto (fun j =>
        ENNReal.ofReal ‖WkpU.toLp (fₙ j) - WkpU.toLp f_lim‖) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h0
    exact hz.congr' <| Eventually.of_forall fun j =>
      (WkpU.derivELpNorm_zero_sub_eq_toLp_norm (fₙ j) f_lim).symm
  | succ m =>
    let nm : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    have hnm : nm ≤ k := Nat.lt_succ_iff.mp hm
    have key : Tendsto (fun j => ‖WkpU.derivtoLp (fₙ j) nm hnm s -
        WkpU.derivtoLp f_lim nm hnm s‖) atTop (𝓝 0) := by
      simp_rw [← dist_eq_norm]
      exact tendsto_iff_dist_tendsto_zero.mp (hg_ns nm hnm s)
    have hz : Tendsto (fun j =>
        ENNReal.ofReal ‖WkpU.derivtoLp (fₙ j) nm hnm s -
          WkpU.derivtoLp f_lim nm hnm s‖) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal key
    exact hz.congr' <| Eventually.of_forall fun j =>
      (WkpU.derivELpNorm_sub_eq_derivtoLp_norm (fₙ j) f_lim nm hnm s).symm

/-- The Sobolev space `W^{k,p}(U)` is complete. -/
instance instCompleteSpace {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} [Fact (1 ≤ p)] :
    CompleteSpace (WkpU d k p U hU) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro fₙ hcauchy
  obtain ⟨f_lim, hf_toLp, hf_deriv⟩ := WkpU.limit_of_cauchySeq hcauchy
  exact ⟨f_lim, (WkpU.tendsto_iff_all_derivELpNorm).mpr
    (WkpU.derivELpNorm_tendsto_zero f_lim hf_toLp hf_deriv)⟩


end Sobolev
