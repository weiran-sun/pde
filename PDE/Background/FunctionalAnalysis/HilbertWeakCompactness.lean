import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.MetricSpace.Sequences

open Filter Topology
open scoped ENNReal

/-! ## Helper lemmas for `bounded_seq_weak_subseq_in_hilbert` -/

/-- Construct a countable orthonormal sequence in a separable infinite dimensional complete
real Hilbert space whose closed linear span is the whole space. The construction takes the
set indexed Hilbert basis from mathlib, shows the index set is countable because any two
distinct basis vectors are at distance root two so open balls of radius one half around
them are pairwise disjoint and a separable space can hold at most countably many pairwise
disjoint open sets, shows the index set is infinite because a finite basis would span a
closed finite dimensional subspace equal to the whole space contradicting infinite
dimensionality, and reindexes by the natural numbers using the standard chain that
countable plus infinite gives a bijection with the natural numbers. -/
private lemma bdd_seq_step1_basis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (h_inf_dim : ¬ FiniteDimensional ℝ H) :
    ∃ b : ℕ → H, Orthonormal ℝ b ∧
      (Submodule.span ℝ (Set.range b)).topologicalClosure = ⊤ := by
  obtain ⟨w, hb_basis, _hb_eq⟩ := exists_hilbertBasis ℝ H
  have hw_countable : Countable ↥w := by
    obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense H
    choose f hf_mem hf_close using fun e : ↥w =>
      hD_dense.exists_dist_lt (hb_basis e) (by norm_num : (0 : ℝ) < 1/3)
    have h_inj : Function.Injective f := by
      intro e₁ e₂ heq
      by_contra h_ne
      have h_ortho := hb_basis.orthonormal
      have h_dist_sq : dist (hb_basis e₁) (hb_basis e₂) ^ 2 = 2 := by
        rw [dist_eq_norm, norm_sub_sq_real, h_ortho.norm_eq_one e₁,
            h_ortho.norm_eq_one e₂, h_ortho.inner_eq_zero h_ne]
        ring
      have h_tri : dist (hb_basis e₁) (hb_basis e₂) < 2/3 := by
        calc dist (hb_basis e₁) (hb_basis e₂)
            ≤ dist (hb_basis e₁) (f e₁) + dist (f e₁) (hb_basis e₂) := dist_triangle _ _ _
          _ = dist (hb_basis e₁) (f e₁) + dist (f e₂) (hb_basis e₂) := by rw [heq]
          _ = dist (hb_basis e₁) (f e₁) + dist (hb_basis e₂) (f e₂) := by rw [dist_comm (f e₂)]
          _ < 1/3 + 1/3 := add_lt_add (hf_close e₁) (hf_close e₂)
          _ = 2/3 := by norm_num
      have h_d_nn : 0 ≤ dist (hb_basis e₁) (hb_basis e₂) := dist_nonneg
      nlinarith
    haveI : Countable D := hD_count.to_subtype
    exact Function.Injective.countable (f := fun e => (⟨f e, hf_mem e⟩ : D))
      (fun _ _ heq => h_inj (congrArg Subtype.val heq))
  have hw_infinite : Infinite ↥w := by
    rw [← not_finite_iff_infinite]
    intro _
    haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range hb_basis)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range hb_basis)
    have h_closed_eq :
        (Submodule.span ℝ (Set.range hb_basis)).topologicalClosure =
          Submodule.span ℝ (Set.range hb_basis) :=
      (Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq
    have h_top : Submodule.span ℝ (Set.range hb_basis) = ⊤ := by
      rw [← h_closed_eq, hb_basis.dense_span]
    haveI : FiniteDimensional ℝ (⊤ : Submodule ℝ H) := h_top ▸ inferInstance
    exact h_inf_dim (Module.Finite.equiv Submodule.topEquiv)
  obtain ⟨e⟩ : Nonempty (ℕ ≃ ↥w) := by
    haveI : Encodable ↥w := Encodable.ofCountable _
    haveI : Denumerable ↥w := Denumerable.ofEncodableOfInfinite _
    exact ⟨(Denumerable.eqv ↥w).symm⟩
  refine ⟨hb_basis ∘ e, hb_basis.orthonormal.comp _ e.injective, ?_⟩
  rw [Set.range_comp, e.range_eq_univ, Set.image_univ]
  exact hb_basis.dense_span

/-- Each Fourier coefficient of a bounded sequence against an orthonormal basis vector is
bounded by the same uniform bound. Immediate from Cauchy Schwarz applied to the inner
product combined with orthonormality giving each basis vector unit norm. -/
private lemma bdd_seq_step2_coef_bounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : ℕ → H} {b : ℕ → H} {C : ℝ}
    (h_bdd : ∀ n, ‖x n‖ ≤ C) (hb : Orthonormal ℝ b) :
    ∀ i n, |inner ℝ (x n) (b i)| ≤ C := by
  intro i n
  have h_xn : 0 ≤ ‖x n‖ := norm_nonneg _
  have h_bi : ‖b i‖ = 1 := hb.1 i
  calc |inner ℝ (x n) (b i)|
      ≤ ‖x n‖ * ‖b i‖ := abs_real_inner_le_norm _ _
    _ = ‖x n‖ * 1 := by rw [h_bi]
    _ = ‖x n‖ := by ring
    _ ≤ C := h_bdd n

/-- Cantor diagonal extraction. Given a doubly indexed family of bounded real valued
coefficients, extract a single strictly monotone subsequence along which every column
converges. The construction applies the Bolzano Weierstrass theorem on each column to
refine the subsequence column by column, building a chain of refined subsequences by
primitive recursion on the natural numbers, then takes the diagonal of this chain as the
desired single subsequence. The diagonal is strictly monotone because each refinement is
itself a subsequence of the previous one, and per column convergence transfers because
the diagonal is eventually a subsequence of the relevant column's first refinement. -/
private lemma bdd_seq_step3_diagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : ℕ → H} {b : ℕ → H} {C : ℝ}
    (h_coef_bdd : ∀ i n, |inner ℝ (x n) (b i)| ≤ C) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∀ i, ∃ c : ℝ, Tendsto (fun k => inner ℝ (x (subseq k)) (b i)) atTop (𝓝 c) := by
  have bw : ∀ g : ℕ → ℝ, (∀ n, |g n| ≤ C) →
            ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ c : ℝ, Tendsto (g ∘ ψ) atTop (𝓝 c) := by
    intro g hg
    obtain ⟨c, _, ψ, hψ_mono, hψ_lim⟩ :=
      tendsto_subseq_of_bounded (s := Set.Icc (-C) C) isCompact_Icc.isBounded
        (fun n => Set.mem_Icc.mpr (abs_le.mp (hg n)))
    exact ⟨ψ, hψ_mono, c, hψ_lim⟩
  let pick : (ℕ → ℕ) → ℕ → (ℕ → ℕ) := fun τ n =>
    Classical.choose (bw (fun k => inner ℝ (x (τ k)) (b n)) (fun k => h_coef_bdd n (τ k)))
  have pick_spec : ∀ τ n, StrictMono (pick τ n) ∧
      ∃ c, Tendsto ((fun k => inner ℝ (x (τ k)) (b n)) ∘ pick τ n) atTop (𝓝 c) :=
    fun τ n => Classical.choose_spec
      (bw (fun k => inner ℝ (x (τ k)) (b n)) (fun k => h_coef_bdd n (τ k)))
  let τs : ℕ → ℕ → ℕ := fun n =>
    Nat.rec (motive := fun _ => ℕ → ℕ) id (fun n τ_n => τ_n ∘ pick τ_n n) n
  have τs_mono : ∀ n, StrictMono (τs n) := by
    intro n
    induction n with
    | zero => exact strictMono_id
    | succ n ih => exact ih.comp (pick_spec (τs n) n).1
  have refines : ∀ m n, m ≤ n → ∃ σ : ℕ → ℕ, StrictMono σ ∧ τs n = τs m ∘ σ := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, rfl⟩
    | succ n _ ih =>
      obtain ⟨σ, hσ, heq⟩ := ih
      refine ⟨σ ∘ pick (τs n) n, hσ.comp (pick_spec (τs n) n).1, ?_⟩
      show τs n ∘ pick (τs n) n = τs m ∘ (σ ∘ pick (τs n) n)
      rw [heq]; rfl
  refine ⟨fun k => τs k k, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ (fun k => ?_)
    show τs k (pick (τs k) k (k+1)) > τs k k
    exact τs_mono k (lt_of_lt_of_le (Nat.lt_succ_self k)
      ((pick_spec (τs k) k).1.id_le (k+1)))
  · intro i
    obtain ⟨c, hc⟩ := (pick_spec (τs i) i).2
    refine ⟨c, ?_⟩
    rw [Metric.tendsto_atTop] at hc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨max N (i+1), fun k hk => ?_⟩
    obtain ⟨σ, hσ_mono, hσ_eq⟩ := refines (i+1) k (le_of_max_le_right hk)
    have h_phi : τs k k = τs i (pick (τs i) i (σ k)) := by
      show τs k k = (τs i ∘ pick (τs i) i) (σ k); rw [hσ_eq]; rfl
    rw [show (fun k => τs k k) k = τs k k from rfl, h_phi]
    exact hN (σ k) ((le_of_max_le_left hk).trans (hσ_mono.id_le k))

/-- Show that the per column limit coefficients form an l two sequence. For any finite set
of indices, the corresponding finite sum of squared limit coefficients is bounded by C
squared, obtained by writing each squared limit as the limit of squared inner products,
summing over the finite set, applying Bessel's inequality at each subsequence step to
bound the finite sum by the squared norm and then by C squared, and passing through the
sequential limit using that limits preserve non strict inequalities. Mathlib's lemma
turning a partial sum bound into summability then upgrades this to summability of the
squared limit coefficients. -/
private lemma bdd_seq_step4_l2
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : ℕ → H} {b : ℕ → H} {C : ℝ}
    (h_bdd : ∀ n, ‖x n‖ ≤ C) (hb_ortho : Orthonormal ℝ b)
    {subseq : ℕ → ℕ} {c : ℕ → ℝ}
    (hc_lim : ∀ i, Tendsto (fun k => inner ℝ (x (subseq k)) (b i)) atTop (𝓝 (c i))) :
    (∀ u : Finset ℕ, (∑ i ∈ u, c i ^ 2) ≤ C^2) ∧ Summable (fun i => c i ^ 2) := by
  have h_c_sum_le : ∀ u : Finset ℕ, (∑ i ∈ u, c i ^ 2) ≤ C^2 := fun u => by
    refine le_of_tendsto' (tendsto_finsetSum u
      (fun i _ => (hc_lim i).pow 2)) (fun k => ?_)
    have h_bessel := hb_ortho.sum_inner_products_le (𝕜 := ℝ) (x := x (subseq k)) (s := u)
    simp_rw [show ∀ i, ‖inner ℝ (b i) (x (subseq k))‖ ^ 2
                    = (inner ℝ (x (subseq k)) (b i)) ^ 2 from
              fun i => by rw [real_inner_comm, Real.norm_eq_abs, sq_abs]] at h_bessel
    calc (∑ i ∈ u, (inner ℝ (x (subseq k)) (b i)) ^ 2)
        ≤ ‖x (subseq k)‖ ^ 2 := h_bessel
      _ ≤ C ^ 2 := by nlinarith [h_bdd (subseq k), norm_nonneg (x (subseq k))]
  exact ⟨h_c_sum_le, summable_of_sum_le (fun i => sq_nonneg _) h_c_sum_le⟩

/-- Assemble the candidate weak limit element of the Hilbert space as the inverse image of
the l two coefficient sequence under the Riesz Fischer isomorphism associated to the
orthonormal basis. Returns the limit element, its series representation as the sum of
scaled basis vectors, and the norm bound that its norm is at most C. The norm bound uses
that the Riesz Fischer map is a linear isometric equivalence and that the l p norm of the
coefficient sequence is bounded by C via the partial sum bound from step four. -/
private lemma bdd_seq_step5_assemble
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {b : ℕ → H}
    (hb_ortho : Orthonormal ℝ b)
    (hb_dense : (Submodule.span ℝ (Set.range b)).topologicalClosure = ⊤)
    {c : ℕ → ℝ} {C : ℝ} (hC_nn : 0 ≤ C)
    (h_c_sum_le : ∀ u : Finset ℕ, (∑ i ∈ u, c i ^ 2) ≤ C^2)
    (h_l2 : Summable (fun i => c i ^ 2)) :
    ∃ a : H, HasSum (fun i => c i • b i) a ∧ ‖a‖ ≤ C := by
  let B : HilbertBasis ℕ ℝ H := HilbertBasis.mk hb_ortho hb_dense.ge
  have h_pow2 : ∀ y : ℝ, ‖y‖ ^ (2 : ℝ) = y ^ 2 := fun y => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        Real.norm_eq_abs, sq_abs]
  have h_p2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have h_c_memℓp : Memℓp (c : ∀ _ : ℕ, ℝ) 2 := memℓp_gen (by
    convert h_l2 using 1
    ext i; rw [h_p2]; exact h_pow2 (c i))
  let c_lp : lp (fun _ : ℕ => ℝ) 2 := ⟨c, h_c_memℓp⟩
  refine ⟨B.repr.symm c_lp, ?_, ?_⟩
  · have h := B.hasSum_repr_symm c_lp
    convert h using 1
    ext i; congr 1
    exact (HilbertBasis.coe_mk hb_ortho hb_dense.ge ▸ rfl : b i = B i)
  · rw [LinearIsometryEquiv.norm_map]
    refine lp.norm_le_of_forall_sum_le (h_p2 ▸ (by norm_num : (0 : ℝ) < 2)) hC_nn fun s => ?_
    rw [h_p2, Finset.sum_congr rfl (fun i _ => h_pow2 (c i)),
        ← Real.norm_of_nonneg hC_nn, h_pow2 C]
    exact h_c_sum_le s

/-- Show weak convergence by an epsilon over two plus epsilon over two split. For an
arbitrary test vector, expand it as a sum of scaled basis vectors and truncate at some
finite index to obtain a partial sum plus a remainder of arbitrarily small norm.
Decompose the difference of inner products at the inner product level into the head
over the truncation and a tail against the remainder. The tail is bounded uniformly in
 the subsequence index by Cauchy-Schwarz on a single inner product followed by the
uniform two-C bound on the difference of the sequence value and the limit, allowing us
to choose the truncation index so the tail is below epsilon over two for every
subsequence index. The head is a finite linear combination of pointwise convergent
scalar sequences, so mathlib's lemma for the limit of a finite sum of convergent
sequences gives a threshold beyond which the head is below epsilon over two. Combining
the two bounds via the triangle inequality finishes the proof. -/
private lemma bdd_seq_step6_weak_conv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {x : ℕ → H} {b : ℕ → H} {C : ℝ}
    (h_bdd : ∀ n, ‖x n‖ ≤ C) (hC_nn : 0 ≤ C)
    (hb_ortho : Orthonormal ℝ b)
    (hb_dense : (Submodule.span ℝ (Set.range b)).topologicalClosure = ⊤)
    {subseq : ℕ → ℕ} {c : ℕ → ℝ} {a : H}
    (hc_lim : ∀ i, Tendsto (fun k => inner ℝ (x (subseq k)) (b i)) atTop (𝓝 (c i)))
    (h_l2 : Summable (fun i => c i ^ 2))
    (ha_sum : HasSum (fun i => c i • b i) a)
    (h_a_norm_le : ‖a‖ ≤ C) :
    ∀ v : H, Tendsto (fun k => inner ℝ (x (subseq k)) v) atTop
                     (𝓝 (inner ℝ a v)) := by
  let B : HilbertBasis ℕ ℝ H := HilbertBasis.mk hb_ortho hb_dense.ge
  have h_c_memℓp : Memℓp (c : ∀ _ : ℕ, ℝ) 2 := by
    refine memℓp_gen ?_
    convert h_l2 using 1
    ext i
    rw [show (2 : ℝ≥0∞).toReal = 2 from by norm_num, Real.norm_eq_abs,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    exact sq_abs (c i)
  let c_lp : lp (fun _ : ℕ => ℝ) 2 := ⟨c, h_c_memℓp⟩
  have ha_alt_sum : HasSum (fun i => c i • b i) (B.repr.symm c_lp) := by
    have h := B.hasSum_repr_symm c_lp
    convert h using 1
    ext i
    congr 1
    exact (HilbertBasis.coe_mk hb_ortho hb_dense.ge ▸ rfl : b i = B i)
  have h_a_eq : a = B.repr.symm c_lp := ha_sum.unique ha_alt_sum
  intro v
  have h_c_eq_inner_a : ∀ i, c i = inner ℝ a (b i) := by
    intro i
    have h_repr_a : B.repr a = c_lp := by
      rw [h_a_eq]
      exact LinearIsometryEquiv.apply_symm_apply _ _
    have h_inner_form : inner ℝ (B i) a = c i := by
      rw [← B.repr_apply_apply a i, h_repr_a]
    have h_B_eq_b : (B : ℕ → H) i = b i := by
      rw [HilbertBasis.coe_mk hb_ortho hb_dense.ge]
    rw [h_B_eq_b] at h_inner_form
    rw [← h_inner_form, real_inner_comm]
  have h_termwise :
      ∀ i, Tendsto (fun k => inner ℝ (x (subseq k)) (B i)) atTop
                   (𝓝 (inner ℝ a (B i))) := by
    intro i
    have h_B_eq_b : (B : ℕ → H) i = b i := by
      rw [HilbertBasis.coe_mk hb_ortho hb_dense.ge]
    rw [h_B_eq_b, show inner ℝ a (b i) = c i from (h_c_eq_inner_a i).symm]
    exact hc_lim i
  have h_rN_norm_tendsto :
      Tendsto (fun N => ‖v - ∑ i ∈ Finset.range N, B.repr v i • (B i : H)‖)
              atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := v) (f := atTop)).sub
              (B.hasSum_repr v).tendsto_sum_nat).norm
    simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  let M : ℝ := C + 1
  have hM_pos : 0 < M := by linarith [hC_nn]
  rw [Metric.tendsto_atTop] at h_rN_norm_tendsto
  obtain ⟨N, hN⟩ := h_rN_norm_tendsto (ε / (4 * M)) (by positivity)
  set v_N := ∑ i ∈ Finset.range N, B.repr v i • (B i : H) with hv_N
  set r_N := v - v_N with hr_N
  have h_rN_bd : ‖r_N‖ < ε / (4 * M) := by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hN N le_rfl
  have h_head_tendsto :
      Tendsto (fun k => ∑ i ∈ Finset.range N,
                  B.repr v i * (inner ℝ (x (subseq k)) (B i) - inner ℝ a (B i)))
              atTop (𝓝 0) := by
    have h_each : ∀ i ∈ Finset.range N,
        Tendsto (fun k => B.repr v i *
                  (inner ℝ (x (subseq k)) (B i) - inner ℝ a (B i)))
                atTop (𝓝 0) := fun i _ => by
      have h_sub := (h_termwise i).sub_const (inner ℝ a (B i))
      simpa using h_sub.const_mul (B.repr v i)
    simpa using tendsto_finsetSum (Finset.range N) h_each
  rw [Metric.tendsto_atTop] at h_head_tendsto
  obtain ⟨K, h_K⟩ := h_head_tendsto (ε / 2) (by linarith)
  refine ⟨K, fun k hk => ?_⟩
  have h_decomp :
      inner ℝ (x (subseq k)) v - inner ℝ a v =
        (∑ i ∈ Finset.range N,
            B.repr v i * (inner ℝ (x (subseq k)) (B i) - inner ℝ a (B i))) +
        inner ℝ (x (subseq k) - a) r_N := by
    rw [← inner_sub_left]
    have h_v_split : v = v_N + r_N := by show v = v_N + (v - v_N); abel
    conv_lhs => rw [h_v_split]
    rw [inner_add_right, hv_N, inner_sum]
    refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
    rw [inner_smul_right, inner_sub_left]
  have h_xk_a_norm : ‖x (subseq k) - a‖ ≤ 2 * M := by
    have := (norm_sub_le (x (subseq k)) a).trans (add_le_add (h_bdd _) h_a_norm_le)
    linarith
  have h_tail_bd : |inner ℝ (x (subseq k) - a) r_N| < ε / 2 := by
    calc |inner ℝ (x (subseq k) - a) r_N|
        ≤ ‖x (subseq k) - a‖ * ‖r_N‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * M) * ‖r_N‖ :=
            mul_le_mul_of_nonneg_right h_xk_a_norm (norm_nonneg _)
      _ < (2 * M) * (ε / (4 * M)) := mul_lt_mul_of_pos_left h_rN_bd (by linarith)
      _ = ε / 2 := by
            have : (4 * M : ℝ) ≠ 0 := by positivity
            field_simp; ring
  have h_head_bd :
      |∑ i ∈ Finset.range N,
          B.repr v i * (inner ℝ (x (subseq k)) (B i) - inner ℝ a (B i))| < ε / 2 := by
    simpa [Real.dist_eq, abs_sub_comm] using h_K k hk
  rw [Real.dist_eq, h_decomp]
  calc |(∑ i ∈ Finset.range N,
            B.repr v i * (inner ℝ (x (subseq k)) (B i) - inner ℝ a (B i))) +
        inner ℝ (x (subseq k) - a) r_N|
      ≤ |∑ i ∈ Finset.range N,
            B.repr v i * (inner ℝ (x (subseq k)) (B i) - inner ℝ a (B i))| +
        |inner ℝ (x (subseq k) - a) r_N| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h_head_bd h_tail_bd
    _ = ε := by ring

/-- **Bounded sequences in a Hilbert space have weakly convergent
subsequences.**  Sequential form of Banach–Alaoglu for the reflexive Hilbert
case.  Weak convergence is characterised by the inner product:
`x_{φ k} ⇀ a ↔ ∀ v, ⟨x_{φ k}, v⟩ → ⟨a, v⟩`.

Construction (in the proof): pick a Hilbert basis `b` of `H`; the Fourier
coefficients `⟨x n, b i⟩` are bounded in `ℝ` (Cauchy-Schwarz + the norm
bound); apply Bolzano-Weierstrass coordinate-by-coordinate and Cantor diagonal
to extract a single subseq `φ` along which every Fourier coefficient
converges; Bessel ⇒ the limit coefficients are ℓ²; assemble the limit `a` as
the Hilbert series; density ⇒ pairing with any `v ∈ H` converges.

The proof factors through six helper lemmas (`bdd_seq_step1_basis` through
`bdd_seq_step6_weak_conv`), each documented with its math role.  Step 6 uses
the Kreyszig-style ε/2 + ε/2 split (truncate `v` to a finite-rank partial sum
in the basis; bound the tail via single-inner-product Cauchy–Schwarz). -/
theorem bounded_seq_weak_subseq_in_hilbert
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (h_inf_dim : ¬ FiniteDimensional ℝ H)
    {x : ℕ → H} {C : ℝ} (h_bdd : ∀ n, ‖x n‖ ≤ C) :
    ∃ (subseq : ℕ → ℕ) (a : H), StrictMono subseq ∧
      ∀ v : H, Tendsto (fun k => inner ℝ (x (subseq k)) v) atTop
                       (𝓝 (inner ℝ a v)) := by
  -- Step 1: ℕ-indexed orthonormal basis with dense span.
  obtain ⟨b, hb_ortho, hb_dense⟩ := bdd_seq_step1_basis h_inf_dim
  -- Step 2: each Fourier coefficient is bounded by C.
  have h_coef_bdd := bdd_seq_step2_coef_bounded h_bdd hb_ortho
  -- Step 3: Cantor-diagonal extract a subsequence converging on every column.
  obtain ⟨subseq, hsubseq_mono, h_coef_conv⟩ := bdd_seq_step3_diagonal h_coef_bdd
  -- Extract per-column limits via Classical.choose.
  let c : ℕ → ℝ := fun i => Classical.choose (h_coef_conv i)
  have hc_lim : ∀ i, Tendsto (fun k => inner ℝ (x (subseq k)) (b i)) atTop (𝓝 (c i)) :=
    fun i => Classical.choose_spec (h_coef_conv i)
  -- Step 4: the limit coefficients form an ℓ² sequence.
  obtain ⟨h_c_sum_le, h_l2⟩ := bdd_seq_step4_l2 h_bdd hb_ortho hc_lim
  -- Step 5: assemble the candidate weak limit `a`, with norm bound `‖a‖ ≤ C`.
  have hC_nn : 0 ≤ C := (norm_nonneg _).trans (h_bdd 0)
  obtain ⟨a, ha_sum, h_a_norm_le⟩ :=
    bdd_seq_step5_assemble hb_ortho hb_dense hC_nn h_c_sum_le h_l2
  -- Step 6: the 3-ε weak-convergence argument.
  exact ⟨subseq, a, hsubseq_mono,
    bdd_seq_step6_weak_conv h_bdd hC_nn hb_ortho hb_dense
      hc_lim h_l2 ha_sum h_a_norm_le⟩
