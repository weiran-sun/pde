import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.MetricSpace.Sequences

import PDE.Background.FunctionalAnalysis.HilbertWeakCompactness

import PDE.FunctionSpaces.SobolevSpace.SobolevSpaces

open MeasureTheory
open ENNReal
open Filter Topology



/-- Hilbert Sobolev space H^k(U) = W^{k,2}(U) on an open set U.-/
@[reducible]
noncomputable def HkU (d : ℕ+) (k : ℕ) (U : Set (Fin d → ℝ)) (hU : IsOpen U) :=
  WkpU d k 2 U hU

/-- The Hilbert Sobolev space on the whole of `ℝᵈ`, as the special case `U = Set.univ`. -/
noncomputable def Hk (d : ℕ+) (k : ℕ) := Wkp d k 2

lemma eLpNorm_sq_toReal_mul {d : ℕ+}
    {μ : Measure (Fin d → ℝ)} (phi : (Fin d → ℝ) → ℝ) (hphi : MemLp phi 2 μ) :
    (eLpNorm phi 2 μ ^ (2 : ℝ)).toReal = ∫ x, phi x * phi x ∂μ := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hphi,
      show (2 : ℝ≥0∞).toReal = 2 from by norm_num,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.toReal_ofReal (by positivity),
      Real.rpow_inv_rpow (integral_nonneg fun _ => by positivity) two_ne_zero]
  simp only [Real.rpow_two, pow_two, Real.norm_eq_abs, abs_mul_abs_self]

/-- product of HkU functions is integrable on U -/
lemma HkU.integrable_val_mul {d : ℕ+} {k : ℕ} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f g : HkU d k U hU) :
    Integrable (fun x => f x * g x) (μU d U) :=
  MemLp.integrable_mul f.property.1 g.property.1

/-- product of weak derivatives of HkU functions is integrable on U -/
lemma HkU.integrable_weakDeriv_mul {d : ℕ+} {k : ℕ} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f g : HkU d k U hU)
    (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    Integrable (fun x => ((WkpU.weakDeriv f n hn s) : (Fin d → ℝ) → ℝ) x
                       * ((WkpU.weakDeriv g n hn s) : (Fin d → ℝ) → ℝ) x) (μU d U) :=
  MemLp.integrable_mul (WkpU.weakDeriv_memLp f n hn s)
                              (WkpU.weakDeriv_memLp g n hn s)

/-- `AEEqFun.coeFn_add` specialised to the `WkpU` coercion `⇑(f + g)`,
    matching how the inner-product proof presents its goals. -/
lemma HkU.coeFn_add {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} [Fact (1 ≤ p)] (f g : WkpU d k p U hU) :
    ⇑(f + g) =ᵐ[μU d U] fun x => f x + g x :=
  WkpU.coeFn_add f g

/-- `AEEqFun.coeFn_smul` similarly specialised. -/
lemma HkU.coeFn_smul {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} [Fact (1 ≤ p)]
    (c : ℝ) (f : WkpU d k p U hU) :
    ⇑(c • f) =ᵐ[μU d U] fun x => c • f x :=
  WkpU.coeFn_smul c f

/-- The weak derivative is additive: -/
lemma WkpU.weakDeriv_add {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f g : WkpU d k p U hU) (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    ((WkpU.weakDeriv (f + g) n hn s) : (Fin d → ℝ) → ℝ)
    =ᵐ[μU d U]
    fun x => (WkpU.weakDeriv f n hn s : (Fin d → ℝ) → ℝ) x
           + (WkpU.weakDeriv g n hn s : (Fin d → ℝ) → ℝ) x := by
  obtain ⟨h_add, eq_add⟩ := WeakmultiDerivU_add U hU s f.val g.val
                              (WkpU.hasWeakDeriv f n hn s)
                              (WkpU.hasWeakDeriv g n hn s)
  have huniq := WeakmultiderivU_unique hU s (f + g).val
                  (WkpU.hasWeakDeriv (f + g) n hn s)
                  (WeakmultiderivU U (f + g).val s h_add)
                  (WeakmultiderivU_spec U (f + g).val s h_add)
  exact (huniq.trans eq_add).trans
    (AEEqFun.coeFn_add (WkpU.weakDeriv f n hn s) (WkpU.weakDeriv g n hn s))

/-- The weak derivative is scalar-linear -/
lemma WkpU.weakDeriv_smul {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (c : ℝ) (f : WkpU d k p U hU) (n : ℕ+) (hn : n ≤ k) (s : Fin n → Fin d) :
    ((WkpU.weakDeriv (c • f) n hn s) : (Fin d → ℝ) → ℝ)
    =ᵐ[μU d U]
    fun x => c • (WkpU.weakDeriv f n hn s : (Fin d → ℝ) → ℝ) x := by
  obtain ⟨h_smul, eq_smul⟩ := WeakmultiDerivU_smul U hU s f.val c
                                (WkpU.hasWeakDeriv f n hn s)
  have huniq := WeakmultiderivU_unique hU s (c • f).val
                  (WkpU.hasWeakDeriv (c • f) n hn s)
                  (WeakmultiderivU U (c • f).val s h_smul)
                  (WeakmultiderivU_spec U (c • f).val s h_smul)
  exact (huniq.trans eq_smul).trans
    (AEEqFun.coeFn_smul c (WkpU.weakDeriv f n hn s))

noncomputable def HkU.innerFormula {d : ℕ+} {k : ℕ}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} (f g : HkU d k U hU) : ℝ :=
  (∫ x, f x * g x ∂(μU d U)) +
  ∑ n : Fin k, ∑ s : Fin (n.val + 1) → Fin d,
    let nm : ℕ+ := ⟨n.val + 1, Nat.succ_pos _⟩
    let hnk : nm ≤ k := Nat.succ_le_of_lt n.isLt
    ∫ x, ((WkpU.weakDeriv f nm hnk s) : (Fin d → ℝ) → ℝ) x
       * ((WkpU.weakDeriv g nm hnk s) : (Fin d → ℝ) → ℝ) x ∂(μU d U)

-- Inner product on H^k(U) = W^{k,2}(U): ∫_U fg + ∑ ∫_U D^s f · D^s g.
-- The four `InnerProductSpace` axioms are proved as standalone lemmas, then assembled
-- into `instInnerProductSpaceHkU` below.

/-- The Hᵏ inner product recovers the squared Hᵏ-norm: `‖f‖² = ⟪f, f⟫`. -/
lemma HkU.innerFormula_norm_sq {d : ℕ+} {k : ℕ} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f : HkU d k U hU) :
    ‖f‖ ^ 2 = RCLike.re (HkU.innerFormula f f) := by
  -- Block A -- conj is identity on ℝ; B -- name-and-unfold the inner product.
  simp only [RCLike.re_to_real]
  change (WkpUNorm k 2 f)^2 = HkU.innerFormula f f
  simp only [HkU.innerFormula, WkpUNorm, WkpU.eNorm]
  rw [if_neg (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]

  -- Block D — Fold `((X^(1/2)).toNNReal)²` to `X.toReal` (the algebraic identity
  -- (√X)² = X via `ENNReal.rpow_inv_rpow`), then distribute `.toReal` across the
  -- double sum.
  have hne : ∀ (n : Fin (k+1)) (s : Fin n.val → Fin d),
      WkpU.derivELpNorm f n.val s ^ (2:ℝ) ≠ ⊤ := fun n s =>
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (WkpU.derivELpNorm_ne_top f n s)
  have key : ∀ X : ℝ≥0∞, ((X ^ ((1:ℝ)/2)).toNNReal : ℝ)^2 = X.toReal := fun X => by
    show ((X ^ ((1:ℝ)/2)).toReal)^2 = X.toReal
    rw [← ENNReal.toReal_pow, ← ENNReal.rpow_two, one_div,
        ENNReal.rpow_inv_rpow two_ne_zero]
  simp only [show (2 : ℝ≥0∞).toReal = 2 from by norm_num]
  rw [key, ENNReal.toReal_sum (fun n _ => ENNReal.sum_ne_top.mpr fun s _ => hne n s),
      Finset.sum_congr rfl (fun n _ => ENNReal.toReal_sum fun s _ => hne n s),
      Fin.sum_univ_succ]

  congr 1
  · haveI : IsEmpty (Fin ((0 : Fin (k + 1)) : ℕ)) := Fin.isEmpty
    exact (Fintype.sum_unique _).trans (eLpNorm_sq_toReal_mul _ f.property.1)
  · apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro s _
    set nm : ℕ+ := ⟨n.val + 1, Nat.succ_pos _⟩
    have hnk : nm ≤ k := Nat.succ_le_of_lt n.isLt
    have key_eq : WkpU.derivELpNorm f n.succ.val s
                = eLpNorm (WkpU.weakDeriv f nm hnk s : (Fin d → ℝ) → ℝ) 2 (μU d U) :=
      (WkpU.eLpNorm_weakDeriv_eq f nm hnk s).symm
    rw [key_eq]
    exact eLpNorm_sq_toReal_mul _ (WkpU.weakDeriv_memLp f _ hnk s)

/-- The Hᵏ inner product is symmetric (`conj`-symmetric, trivially over ℝ). -/
lemma HkU.innerFormula_conj_symm {d : ℕ+} {k : ℕ} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f g : HkU d k U hU) :
    (starRingEnd ℝ) (HkU.innerFormula g f) = HkU.innerFormula f g := by
  simp only [RCLike.conj_to_real, HkU.innerFormula]
  refine congrArg₂ (· + ·)
    (integral_congr_ae (.of_forall fun _ => mul_comm _ _)) ?_
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    integral_congr_ae (.of_forall fun _ => mul_comm _ _)

/-- The Hᵏ inner product is additive in the first argument. -/
lemma HkU.innerFormula_add_left {d : ℕ+} {k : ℕ} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f g h : HkU d k U hU) :
    HkU.innerFormula (f + g) h = HkU.innerFormula f h + HkU.innerFormula g h := by
  simp only [HkU.innerFormula, add_add_add_comm]
  congr 1
  · rw [← integral_add (HkU.integrable_val_mul f h) (HkU.integrable_val_mul g h)]
    apply integral_congr_ae
    filter_upwards [HkU.coeFn_add f g] with x hx
    rw [hx]; ring
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    set nm : ℕ+ := ⟨n.val + 1, Nat.succ_pos _⟩
    have hnk : nm ≤ k := Nat.succ_le_of_lt n.isLt
    rw [← integral_add (HkU.integrable_weakDeriv_mul f h nm hnk s)
                       (HkU.integrable_weakDeriv_mul g h nm hnk s)]
    apply integral_congr_ae
    filter_upwards [WkpU.weakDeriv_add f g nm hnk s] with x hx
    rw [hx]; ring

/-- The Hᵏ inner product is ℝ-linear in the first argument. -/
lemma HkU.innerFormula_smul_left {d : ℕ+} {k : ℕ} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f g : HkU d k U hU) (r : ℝ) :
    HkU.innerFormula (r • f) g = (starRingEnd ℝ) r * HkU.innerFormula f g := by
  simp only [RCLike.conj_to_real, HkU.innerFormula, mul_add]
  congr 1
  · rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [HkU.coeFn_smul r f] with x hx
    rw [hx, smul_eq_mul]; ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    set nm : ℕ+ := ⟨n.val + 1, Nat.succ_pos _⟩
    have hnk : nm ≤ k := Nat.succ_le_of_lt n.isLt
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [WkpU.weakDeriv_smul r f nm hnk s] with x hx
    rw [hx, smul_eq_mul]; ring

/-- Inner product on `H^k(U) = W^{k,2}(U)`: `∫_U f g + ∑ ∫_U Dˢf · Dˢg`. -/
noncomputable instance instInnerProductSpaceHkU
    {d : ℕ+} {k : ℕ} {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    InnerProductSpace ℝ (HkU d k U hU) where
  inner := HkU.innerFormula
  norm_sq_eq_re_inner := HkU.innerFormula_norm_sq
  conj_inner_symm := HkU.innerFormula_conj_symm
  add_left := HkU.innerFormula_add_left
  smul_left := HkU.innerFormula_smul_left



-- Sec. 5.2.2
-- A subspace with zero trace: closure of smooth compactly supported functions in W^{k,p}.

/-- Generating set for `Wᵏᵖ₀(U)`: Sobolev functions agreeing a.e. with a smooth
compactly supported test function. `WkpU0` is its closure. -/
def WkpU0.baseSet (d : ℕ+) (k : ℕ) (p : ℝ≥0∞)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) [Fact (1 ≤ p)] : Set (WkpU d k p U hU) :=
  {f | ∃ phi ∈ Cc_inftyU d U, ⇑f =ᵐ[μU d U] phi}

/-- `0` lies in `closure (WkpU0.baseSet …)`. -/
lemma WkpU0.zero_mem' {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} [Fact (1 ≤ p)] :
    (0 : WkpU d k p U hU) ∈ closure (WkpU0.baseSet d k p U hU) :=
  subset_closure ⟨0, (Cc_inftyU d U).zero_mem, AEEqFun.coeFn_zero⟩

/-- `closure (WkpU0.baseSet …)` is closed under addition. -/
lemma WkpU0.add_mem' {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} [Fact (1 ≤ p)] {f g : WkpU d k p U hU}
    (hf : f ∈ closure (WkpU0.baseSet d k p U hU))
    (hg : g ∈ closure (WkpU0.baseSet d k p U hU)) :
    f + g ∈ closure (WkpU0.baseSet d k p U hU) := by
  -- mem_closure_iff_seq_limit converts membership to "there exists a sequence X_n → f+g"
  rw [mem_closure_iff_seq_limit] at hf hg ⊢
  obtain ⟨ψ, hψ_mem, hψ_lim⟩ := hf
  obtain ⟨ω, hω_mem, hω_lim⟩ := hg
  -- Candidate sequence: ψₙ + ωₙ. The W^{k,p}-convergence is just additivity of limits.
  refine ⟨fun n => ψ n + ω n, ?_, hψ_lim.add hω_lim⟩
  intro n
  obtain ⟨phi_psi, hψ_in, hψ_ae⟩ := hψ_mem n
  obtain ⟨phi_omega, hω_in, hω_ae⟩ := hω_mem n
  -- The sum of test functions is a test function (Cc_inftyU is a submodule).
  refine ⟨phi_psi + phi_omega, (Cc_inftyU d U).add_mem hψ_in hω_in, ?_⟩
  filter_upwards [HkU.coeFn_add (ψ n) (ω n), hψ_ae, hω_ae]
    with x hsum hψx hωx
  simp only [Pi.add_apply, ← hψx, ← hωx]; exact hsum

/-- `closure (WkpU0.baseSet …)` is closed under scalar multiplication. -/
lemma WkpU0.smul_mem' {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} [Fact (1 ≤ p)] (c : ℝ) {f : WkpU d k p U hU}
    (hf : f ∈ closure (WkpU0.baseSet d k p U hU)) :
    c • f ∈ closure (WkpU0.baseSet d k p U hU) := by
  rw [mem_closure_iff_seq_limit] at hf ⊢
  obtain ⟨ψ, hψ_mem, hψ_lim⟩ := hf
  refine ⟨fun n => c • ψ n, ?_, hψ_lim.const_smul c⟩
  intro n
  obtain ⟨phi_psi, hψ_in, hψ_ae⟩ := hψ_mem n
  refine ⟨c • phi_psi, (Cc_inftyU d U).smul_mem c hψ_in, ?_⟩
  filter_upwards [HkU.coeFn_smul c (ψ n), hψ_ae]
    with x hsmul hψx
  simp only [Pi.smul_apply, ← hψx]; exact hsmul

noncomputable def WkpU0 (d : ℕ+) (k : ℕ) (p : ℝ≥0∞)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) [Fact (1 ≤ p)] :
    Submodule ℝ (WkpU d k p U hU) where
  carrier := closure (WkpU0.baseSet d k p U hU)
  zero_mem' := WkpU0.zero_mem'
  add_mem' := WkpU0.add_mem'
  smul_mem' := WkpU0.smul_mem'

-- W^{k,p}_0 over the whole space `ℝᵈ`, as the special case `U = Set.univ`.
noncomputable def Wkp0 (d : ℕ+) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule ℝ (Wkp d k p) :=
  WkpU0 d k p Set.univ isOpen_univ

-- Coerce `f : WkpU0 d k p U hU` down to a function ℝᵈ → ℝ.
noncomputable instance instCoeFunWkpU0 {d : ℕ+} {k : ℕ} {p : ℝ≥0∞}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} [Fact (1 ≤ p)] :
    CoeFun (WkpU0 d k p U hU) (fun _ ↦ (Fin d → ℝ) → ℝ) where
  coe := fun f ↦ ⇑(f.val)

-- REUSABLE
-- Sec. 5.2.2
noncomputable def Hk0 (d : ℕ+) (k : ℕ) := Wkp0 d k 2

-- The Hilbert version H^k_0(U) on an open set U.
noncomputable def HkU0 (d : ℕ+) (k : ℕ) (U : Set (Fin d → ℝ)) (hU : IsOpen U) :=
  WkpU0 d k 2 U hU

instance instCompleteHKU0 {d : ℕ+} {k : ℕ} {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    CompleteSpace (HkU0 d k U hU) :=
    isClosed_closure.completeSpace_coe


noncomputable abbrev HkU0_dual
    (d : ℕ+) (k : ℕ) (U : Set (Fin d → ℝ)) (hU : IsOpen U) :=
    HkU0 d k U hU →L[ℝ] ℝ

-- The Riesz isomorphism (for converting functionals to representers and back)

noncomputable def HkU0_riesz {d : ℕ+} {k : ℕ}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    HkU0 d k U hU ≃ₗᵢ⋆[ℝ] HkU0_dual d k U hU :=
  InnerProductSpace.toDual ℝ _

noncomputable abbrev H1U0 (d : ℕ+) (U : Set (Fin d → ℝ)) (hU : IsOpen U) :=
  HkU0 d 1 U hU

noncomputable abbrev H1U0_dual (d : ℕ+) (U : Set (Fin d → ℝ)) (hU : IsOpen U) :=
  HkU0_dual d 1 U hU

-- Cache typeclass instances to avoid repeated deep Submodule propagation when
-- elaborating Bochner spaces below.
instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

noncomputable instance instNormedAddCommGroupH1U0 {d : ℕ+}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    NormedAddCommGroup (H1U0 d U hU) := inferInstance

noncomputable instance instNormedSpaceH1U0 {d : ℕ+}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    NormedSpace ℝ (H1U0 d U hU) := inferInstance

-- Cache typeclass instances on `H1U0_dual` analogous to those on `H1U0`, so
-- that downstream Bochner-space elaboration (`Lp (H1U0_dual ...) p μ`) does not
-- repeatedly chase the CLM instance chain through `HkU0 →L[ℝ] ℝ`.
noncomputable instance instNormedAddCommGroupH1U0_dual {d : ℕ+}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    NormedAddCommGroup (H1U0_dual d U hU) := inferInstance

noncomputable instance instNormedSpaceH1U0_dual {d : ℕ+}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    NormedSpace ℝ (H1U0_dual d U hU) := inferInstance

noncomputable instance instCompleteSpaceH1U0_dual {d : ℕ+}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    CompleteSpace (H1U0_dual d U hU) := inferInstance

set_option maxHeartbeats 4000000 in
/-- The dual `H⁻¹ = (H¹₀)'` is itself a Hilbert space: its inner product is transported from
`H¹₀` along the Riesz isometry `HkU0_riesz : H¹₀ ≃ₗᵢ⋆[ℝ] (H¹₀)'`. Because the Riesz map is an
isometry, the induced inner product is compatible with the *existing* operator norm on the dual
(no competing norm is introduced, unlike `InnerProductSpace.induced`). -/
noncomputable instance instInnerProductSpaceH1U0_dual {d : ℕ+}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    InnerProductSpace ℝ (H1U0_dual d U hU) where
  inner f g := inner ℝ (HkU0_riesz.symm f) (HkU0_riesz.symm g)
  norm_sq_eq_re_inner f := by
    rw [← HkU0_riesz.symm.norm_map f]
    exact norm_sq_eq_re_inner (HkU0_riesz.symm f)
  conj_inner_symm f g := inner_conj_symm (HkU0_riesz.symm f) (HkU0_riesz.symm g)
  add_left f g h := by
    show inner ℝ (HkU0_riesz.symm (f + g)) (HkU0_riesz.symm h)
        = inner ℝ (HkU0_riesz.symm f) (HkU0_riesz.symm h)
          + inner ℝ (HkU0_riesz.symm g) (HkU0_riesz.symm h)
    rw [map_add, inner_add_left]
  smul_left f g r := by
    show inner ℝ (HkU0_riesz.symm (r • f)) (HkU0_riesz.symm g)
        = (starRingEnd ℝ) r * inner ℝ (HkU0_riesz.symm f) (HkU0_riesz.symm g)
    rw [map_smulₛₗ, inner_smul_left]
    simp [starRingEnd_apply, star_trivial]

set_option maxHeartbeats 4000000 in
/-- The Riesz map `HkU0_riesz : H¹₀ → (H¹₀)'` preserves the inner product (by construction of the
dual inner product, which is transported back through `HkU0_riesz.symm`). -/
lemma HkU0_riesz_inner {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (x y : H1U0 d U hU) :
    (inner ℝ (HkU0_riesz x) (HkU0_riesz y) : ℝ) = inner ℝ x y := by
  show (inner ℝ (HkU0_riesz.symm (HkU0_riesz x)) (HkU0_riesz.symm (HkU0_riesz y)) : ℝ)
      = inner ℝ x y
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]

set_option maxHeartbeats 4000000 in
/-- **Gelfand pairing = dual inner product with a Riesz image.**  For a dual element `F` and an
`H¹₀` element `x`, the dual inner product of `F` with `HkU0_riesz x` equals the pairing `F x`.
This is the pointwise identity underlying the Riesz→Gelfand bridge. -/
lemma dual_inner_riesz {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (F : H1U0_dual d U hU) (x : H1U0 d U hU) :
    (inner ℝ F (HkU0_riesz x) : ℝ) = F x := by
  show (inner ℝ (HkU0_riesz.symm F) (HkU0_riesz.symm (HkU0_riesz x)) : ℝ) = F x
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact InnerProductSpace.toDual_symm_apply

instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩

/-- The L two norm of the underlying L two representative of a Sobolev function is bounded
above by its Sobolev norm. Specialisation of the workhorse W k p norm comparison lemma to
the H one zero subspace, using that the submodule norm agrees with the ambient norm. -/
lemma H1U0.l2_norm_le_norm {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (u : H1U0 d U hU) :
    ‖WkpU.toLp u.val‖ ≤ ‖u‖ :=
  WkpU.norm_toLp_le u.val

-- Cache the Sobolev norm instance on `Hk0 d 1` so that `‖·‖` on it is found directly.
-- Synthesis does not reuse `instNormedAddCommGroupH1U0` here because that instance is
-- keyed on the `H1U0`/`HkU0` head, whereas `Hk0 d 1` presents as `Wkp0 d 1 2`; both
-- reduce to `WkpU0 d 1 2 Set.univ isOpen_univ`, so we hand the cached instance over by
-- defeq.
noncomputable instance instNormedAddCommGroupHk0_one {d : ℕ+} :
    NormedAddCommGroup (Hk0 d 1) :=
  instNormedAddCommGroupH1U0 (U := Set.univ) (hU := isOpen_univ)

noncomputable def Hinv_norm {d : ℕ+} (f : Hk0 d 1 → ℝ) : ℝ :=
  ⨆ (u : {u : Hk0 d 1 // ‖u‖ ≤ 1}), f u

/-- Unbundled L two to H minus one inclusion. Sends an L two function to the H minus one
functional that pairs a test vector against it via the L two inner product, after
projecting the test vector to its L two representative. Continuity comes from Cauchy
Schwarz combined with the L two norm bound on H one zero. -/
noncomputable def L2ToHinv {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f : Lp ℝ 2 (μU d U)) : H1U0_dual d U hU :=
  LinearMap.mkContinuous
    { toFun     := fun v => inner ℝ f (WkpU.toLp v.val)
      map_add'  := fun v₁ v₂ => by
        simp only [Submodule.coe_add, WkpU.toLp_add, inner_add_right]
      map_smul' := fun c v => by
        simp only [Submodule.coe_smul, WkpU.toLp_smul, inner_smul_right, RingHom.id_apply,
          smul_eq_mul] }
    ‖f‖
    (fun v => by
      calc ‖inner ℝ f (WkpU.toLp v.val)‖
          ≤ ‖f‖ * ‖WkpU.toLp v.val‖ := norm_inner_le_norm _ _
        _ ≤ ‖f‖ * ‖v‖                := by
              gcongr; exact H1U0.l2_norm_le_norm v)

/-- The L two to H minus one inclusion bundled as a continuous linear map in the source,
with operator norm bounded by one. -/
noncomputable def L2ToHinvCLM {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    Lp ℝ 2 (μU d U) →L[ℝ] H1U0_dual d U hU :=
  LinearMap.mkContinuous
    { toFun     := L2ToHinv
      map_add'  := fun f₁ f₂ => by
        ext v
        show inner ℝ (f₁ + f₂) (WkpU.toLp v.val)
          = inner ℝ f₁ (WkpU.toLp v.val) + inner ℝ f₂ (WkpU.toLp v.val)
        exact inner_add_left _ _ _
      map_smul' := fun c f => by
        ext v
        show inner ℝ (c • f) (WkpU.toLp v.val) = c * inner ℝ f (WkpU.toLp v.val)
        exact real_inner_smul_left _ _ _ }
    1
    (fun f => by
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun v => ?_
      show ‖inner ℝ f (WkpU.toLp v.val)‖ ≤ ‖f‖ * ‖v‖
      calc ‖inner ℝ f (WkpU.toLp v.val)‖
          ≤ ‖f‖ * ‖WkpU.toLp v.val‖ := norm_inner_le_norm _ _
        _ ≤ ‖f‖ * ‖v‖                := by
              gcongr; exact H1U0.l2_norm_le_norm v)

/-- Real valued H minus one norm of an H one zero element, obtained by passing the L two
representative through the L two to H minus one inclusion and taking its operator norm.
Returned as a real number so downstream surface goals avoid the dual type and the
associated typeclass cascade. -/
noncomputable def hinvNormOfH1 {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (u : H1U0 d U hU) : ℝ :=
  ‖(L2ToHinvCLM (d := d) (U := U) (hU := hU)) (WkpU.toLp u.val)‖

lemma hinvNormOfH1_nonneg {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (u : H1U0 d U hU) : 0 ≤ hinvNormOfH1 u := norm_nonneg _

/-- Unbundled direct Gelfand triple inclusion of H one zero into its own dual via L two
pairing. Same underlying map as composing the L two embedding with the L two to H minus
one inclusion, but presented directly. -/
noncomputable def H1U0_to_Hinv
    {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (u : H1U0 d U hU) : H1U0_dual d U hU :=
  LinearMap.mkContinuous
    { toFun     := fun v => inner ℝ (WkpU.toLp u.val) (WkpU.toLp v.val)
      map_add'  := fun v₁ v₂ => by
        simp only [Submodule.coe_add, WkpU.toLp_add, inner_add_right]
      map_smul' := fun c v => by
        simp only [Submodule.coe_smul, WkpU.toLp_smul, inner_smul_right, RingHom.id_apply,
          smul_eq_mul] }
    (‖WkpU.toLp u.val‖)
    (fun v => by
      calc ‖inner ℝ (WkpU.toLp u.val) (WkpU.toLp v.val)‖
          ≤ ‖WkpU.toLp u.val‖ * ‖WkpU.toLp v.val‖ := norm_inner_le_norm _ _
        _ ≤ ‖WkpU.toLp u.val‖ * ‖v‖                := by
              gcongr; exact H1U0.l2_norm_le_norm v)

/-- The Gelfand triple inclusion of H one zero into its own dual bundled as a continuous
linear map, with operator norm bounded by one. -/
noncomputable def H1U0_inclusion_Hinv
    {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    H1U0 d U hU →L[ℝ] H1U0_dual d U hU :=
  LinearMap.mkContinuous
    { toFun     := H1U0_to_Hinv
      map_add'  := fun u v => by
        ext w
        show inner ℝ (WkpU.toLp (u + v).val) (WkpU.toLp w.val)
          = inner ℝ (WkpU.toLp u.val) (WkpU.toLp w.val)
            + inner ℝ (WkpU.toLp v.val) (WkpU.toLp w.val)
        rw [Submodule.coe_add, WkpU.toLp_add, inner_add_left]
      map_smul' := fun c u => by
        ext w
        show inner ℝ (WkpU.toLp (c • u).val) (WkpU.toLp w.val)
          = c * inner ℝ (WkpU.toLp u.val) (WkpU.toLp w.val)
        rw [Submodule.coe_smul, WkpU.toLp_smul, real_inner_smul_left] }
    1
    (fun u => by
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) fun v => ?_
      show ‖inner ℝ (WkpU.toLp u.val) (WkpU.toLp v.val)‖ ≤ ‖u‖ * ‖v‖
      calc ‖inner ℝ (WkpU.toLp u.val) (WkpU.toLp v.val)‖
          ≤ ‖WkpU.toLp u.val‖ * ‖WkpU.toLp v.val‖ := norm_inner_le_norm _ _
        _ ≤ ‖u‖ * ‖v‖                              := by
              gcongr
              · exact H1U0.l2_norm_le_norm u
              · exact H1U0.l2_norm_le_norm v)

noncomputable abbrev L2TH10U (d : ℕ+) (U : Set (Fin d → ℝ)) (hU : IsOpen U) (T : ℝ) :=
  Lp (H1U0 d U hU) (2 : ℝ≥0∞) (volume.restrict (Set.Icc 0 T))

noncomputable abbrev L2TH10U_dual (d : ℕ+) (U : Set (Fin d → ℝ)) (hU : IsOpen U) (T : ℝ) :=
  Lp (H1U0_dual d U hU) (2 : ℝ≥0∞) (volume.restrict (Set.Icc 0 T))

noncomputable abbrev L2TL2 (d : ℕ+) (U : Set (Fin d → ℝ)) (T : ℝ) :=
  Lp (Lp ℝ (2 : ℝ≥0∞) (μU d U)) (2 : ℝ≥0∞) (volume.restrict (Set.Icc 0 T))

noncomputable abbrev LinfTL2 (d : ℕ+) (U : Set (Fin d → ℝ)) (T : ℝ) :=
  Lp (Lp ℝ (2 : ℝ≥0∞) (μU d U)) (⊤ : ℝ≥0∞) (volume.restrict (Set.Icc 0 T))

/-- Second countability of the L two space over an open subset of euclidean space with the
restricted Lebesgue measure. Follows from mathlib's general lemma once we supply the chain
of instances that the underlying measurable space is countably generated and the measure
is sigma finite. -/
noncomputable instance instSecondCountableTopologyLp_ℝ_2_μU
    {d : ℕ+} (U : Set (Fin d → ℝ)) :
    SecondCountableTopology (Lp ℝ 2 (μU d U)) := by
  unfold μU
  haveI : SecondCountableTopology (Fin d → ℝ) := inferInstance
  haveI : BorelSpace (Fin d → ℝ) := Pi.borelSpace
  haveI : MeasurableSpace.CountablyGenerated (Fin d → ℝ) :=
    BorelSpace.countablyGenerated
  haveI : SFinite ((volume : Measure (Fin d → ℝ)).restrict U) := inferInstance
  exact inferInstance

noncomputable instance instSeparableSpaceLp_ℝ_2_μU
    {d : ℕ+} (U : Set (Fin d → ℝ)) :
    TopologicalSpace.SeparableSpace (Lp ℝ 2 (μU d U)) :=
  inferInstance

/-- Separability of the H one zero space. Sketched proof recipe is to embed the W one two
space isometrically into a finite product of L two spaces by sending a function to its
underlying L two representative together with its weak derivatives, inherit second
countability for the W one two space from the product, and then for the H one zero closed
subspace. The detailed embedding is deferred. -/
noncomputable instance instSeparableSpaceH1U0 {d : ℕ+}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    TopologicalSpace.SeparableSpace (H1U0 d U hU) := by
  sorry

/-- Separability of the H minus one dual transfers from H one zero via the Riesz
isomorphism, which is a linear isometric equivalence and in particular a continuous map
with dense range. Not a generic instance because duals of separable Banach spaces need not
be separable, but for Hilbert spaces it holds via Riesz. -/
noncomputable instance instSeparableSpaceH1U0_dual {d : ℕ+}
    {U : Set (Fin d → ℝ)} {hU : IsOpen U} :
    TopologicalSpace.SeparableSpace (H1U0_dual d U hU) :=
  (InnerProductSpace.toDual ℝ (H1U0 d U hU)).toContinuousLinearEquiv.surjective.denseRange.separableSpace
    (InnerProductSpace.toDual ℝ (H1U0 d U hU)).continuous
