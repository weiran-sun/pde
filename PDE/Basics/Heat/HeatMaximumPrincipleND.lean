import PDE.Basics.Heat.HeatSolutionPropertyND
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Pi


open MeasureTheory Filter InnerProductSpace Measure Set
open scoped Topology ENNReal Interval

namespace Heat

variable (n : ℕ) (l T α : ℝ)
variable (hl : 0 < l) (hT : 0 < T) (hα : 0 < α)

def Ω_spatial (n : ℕ) (l : ℝ) : Set (E n) :=
  WithLp.ofLp ⁻¹' Set.pi univ (fun _ ↦ Icc 0 l)

def Ω_spatial_int (n : ℕ) (l : ℝ) : Set (E n) :=
  WithLp.ofLp ⁻¹' Set.pi univ (fun _ ↦ Ioo 0 l)

def Ω_T (n : ℕ) (l T : ℝ) : Set (E n × ℝ) :=
  Ω_spatial n l ×ˢ Icc 0 T

def S_boundary (n : ℕ) (l T : ℝ) : Set (E n × ℝ) :=
  (Ω_spatial n l ×ˢ {0}) ∪ (frontier (Ω_spatial n l) ×ˢ Icc 0 T)

def Top_Edge (n : ℕ) (l T : ℝ) : Set (E n × ℝ) :=
  Ω_spatial_int n l ×ˢ {T}

def Interior (n : ℕ) (l T : ℝ) : Set (E n × ℝ) :=
  Ω_spatial_int n l ×ˢ Ioo 0 T

lemma local_max_implies_second_deriv_nonpos
    {f : ℝ → ℝ} {x₀ : ℝ}
    (h_smooth : ContDiffAt ℝ 2 f x₀)
    (h_max : IsLocalMax f x₀) :
    deriv f x₀ = 0 ∧ deriv (deriv f) x₀ ≤ 0 := by
  have h_deriv : deriv f x₀ = 0 :=
    h_max.hasDerivAt_eq_zero (h_smooth.differentiableAt (by exact Ne.symm (NeZero.ne' 2))).hasDerivAt
  refine ⟨h_deriv, le_of_not_gt fun hpos ↦ ne_of_gt hpos ?_⟩
  simpa using (Filter.EventuallyLE.antisymm h_max <|
    isLocalMin_of_deriv_deriv_pos hpos h_deriv h_smooth.continuousAt).deriv.deriv_eq

lemma differentiableAt_gradient_of_contDiffAt (f : E n → ℝ) (x : E n) (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (gradient f) x :=
  ((LinearIsometryEquiv.contDiff _).contDiffAt.comp x (ContDiffAt.fderiv (f := fun _ y ↦ f y) (g := fun p ↦ p) (hf.comp (x, x) contDiffAt_snd) contDiffAt_id (by norm_num) : ContDiffAt ℝ 1 _ x)).differentiableAt (by norm_num)

lemma laplacian_eq_sum_deriv
    {f : E n → ℝ} {x₀ : E n}
    (h_smooth : ContDiffAt ℝ 2 f x₀) :
    laplacian f x₀ = ∑ i : Fin n, deriv (fun t : ℝ ↦ deriv (fun s : ℝ ↦ f (x₀ + s • (WithLp.equiv 2 (Fin n → ℝ)).symm (Pi.single i (1 : ℝ)))) t) (0 : ℝ) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have h_basis_eq : ∀ i : Fin n, (WithLp.equiv 2 (Fin n → ℝ)).symm (Pi.single i (1 : ℝ)) = b i := fun _ ↦ by aesop
  rw [show laplacian f x₀ = ∑ i : Fin n, ⟪b i, fderiv ℝ (gradient f) x₀ (b i)⟫_ℝ from
    LinearMap.trace_eq_sum_inner (fderiv ℝ (gradient f) x₀) b]
  apply Finset.sum_congr rfl
  intro i _
  rw [h_basis_eq]
  have h_cont : Continuous (fun t : ℝ ↦ x₀ + t • b i) := continuous_const.add (continuous_id.smul continuous_const)
  have h_nhds_diff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (x₀ + t • b i) := by
    have h_tendsto : Tendsto (fun t : ℝ ↦ x₀ + t • b i) (𝓝 (0 : ℝ)) (𝓝 x₀) := by simpa using h_cont.tendsto (0 : ℝ)
    exact h_tendsto.eventually (h_smooth.eventually (by norm_num) |>.mono fun _ hy ↦ hy.differentiableAt (by norm_num))
  have h_eventually_eq : ∀ᶠ t in 𝓝 (0 : ℝ), deriv (fun s : ℝ ↦ f (x₀ + s • b i)) t = ⟪gradient f (x₀ + t • b i), b i⟫_ℝ := by
    filter_upwards [h_nhds_diff] with t ht
    have h_path : HasDerivAt (fun s : ℝ ↦ x₀ + s • b i) (b i) t := by
      simpa using HasDerivAt.const_add x₀ (HasDerivAt.smul_const (hasDerivAt_id t) (b i))
    erw [HasDerivAt.deriv (ht.hasFDerivAt.comp_hasDerivAt t h_path)]
    unfold gradient
    rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [Filter.EventuallyEq.deriv_eq h_eventually_eq]
  have h_grad_diff : DifferentiableAt ℝ (gradient f) x₀ := differentiableAt_gradient_of_contDiffAt n f x₀ h_smooth
  have h_path_deriv : HasDerivAt (fun t : ℝ ↦ x₀ + t • b i) (b i) (0 : ℝ) := by
    simpa using HasDerivAt.const_add x₀ (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) (b i))
  have h_grad_diff_eval : HasFDerivAt (gradient f) (fderiv ℝ (gradient f) x₀) (x₀ + (0 : ℝ) • b i) := by
    simpa using h_grad_diff.hasFDerivAt
  have h_inner_map : (fun t : ℝ ↦ ⟪gradient f (x₀ + t • b i), b i⟫_ℝ) =
      (InnerProductSpace.toDual ℝ (E n) (b i)) ∘ (fun t : ℝ ↦ gradient f (x₀ + t • b i)) := by
    ext t; rw [real_inner_comm, ← InnerProductSpace.toDual_apply_apply]; exact rfl
  have h_chain := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h_grad_diff_eval h_path_deriv
  have h_full_chain := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (InnerProductSpace.toDual ℝ (E n) (b i)).hasFDerivAt h_chain
  erw [h_inner_map, HasDerivAt.deriv h_full_chain]
  exact rfl

lemma local_max_implies_laplacian_nonpos
    {f : E n → ℝ} {x₀ : E n}
    (h_smooth : ContDiffAt ℝ 2 f x₀)
    (h_max : IsLocalMax f x₀) :
    laplacian f x₀ ≤ 0 := by
  rw [laplacian_eq_sum_deriv n h_smooth]
  apply Finset.sum_nonpos
  intro i _
  let v := (WithLp.equiv 2 (Fin n → ℝ)).symm (Pi.single i (1 : ℝ))
  have h_cont : Continuous (fun (t : ℝ) ↦ x₀ + t • v) := continuous_const.add (continuous_id.smul continuous_const)
  have h_tendsto : Tendsto (fun (t : ℝ) ↦ x₀ + t • v) (𝓝 (0 : ℝ)) (𝓝 x₀) := by simpa using h_cont.tendsto (0 : ℝ)
  have h_slice_max : IsLocalMax (fun (t : ℝ) ↦ f (x₀ + t • v)) (0 : ℝ) :=
    h_tendsto.eventually h_max |>.mono fun t ht ↦ by simpa using ht
  have hg_smooth : ContDiffAt ℝ 2 (fun (t : ℝ) ↦ x₀ + t • v) (0 : ℝ) := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have h_slice_smooth : ContDiffAt ℝ 2 (fun (t : ℝ) ↦ f (x₀ + t • v)) (0 : ℝ) :=
    (show ContDiffAt ℝ 2 f (x₀ + (0 : ℝ) • v) by simpa using h_smooth).comp (0 : ℝ) hg_smooth
  exact (local_max_implies_second_deriv_nonpos h_slice_smooth h_slice_max).2

lemma laplacianWithin_eq_laplacian {u : E n → ℝ} {s : Set (E n)} {x : E n}
    (hx : x ∈ interior s) :
    laplacianWithin u s x = laplacian u x := by
  have hs_nhds : s ∈ 𝓝 x := mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset
  unfold laplacianWithin div_fieldWithin gradientWithin laplacian div_field gradient
  have h_grad_eq : (fun y ↦ (InnerProductSpace.toDual ℝ (E n)).symm (fderivWithin ℝ u s y)) =ᶠ[𝓝 x]
                   (fun y ↦ (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ u y)) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [fderivWithin_of_mem_nhds (mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)]
  rw [fderivWithin_of_mem_nhds hs_nhds, Filter.EventuallyEq.fderiv_eq h_grad_eq]

lemma hΩ {l T : ℝ} (hl : 0 < l) (hT : 0 < T) : UniqueDiffOn ℝ (Ω_T n l T) := by
  unfold Ω_T Ω_spatial
  apply UniqueDiffOn.prod
  · refine (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).uniqueDiffOn_preimage_iff.mpr ?_
    apply UniqueDiffOn.pi
    intro i _
    exact uniqueDiffOn_Icc hl
  · exact uniqueDiffOn_Icc hT

lemma h_int_nhds {l T : ℝ} : ∀ p ∈ Interior n l T, Ω_T n l T ∈ 𝓝 p := by
  intro p hp
  have h_subset : Interior n l T ⊆ Ω_T n l T := by
    unfold Interior Ω_T Ω_spatial_int Ω_spatial
    apply Set.prod_mono
    · exact Set.preimage_mono (Set.pi_mono fun _ _ ↦ Ioo_subset_Icc_self)
    · exact Ioo_subset_Icc_self
  have h_open : IsOpen (Interior n l T) := by
    unfold Interior Ω_spatial_int
    apply IsOpen.prod
    · exact IsOpen.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ)) (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo)
    · exact isOpen_Ioo
  exact Filter.mem_of_superset (h_open.mem_nhds hp) h_subset

lemma perturb_dt
    {l T ε : ℝ} {u : E n → ℝ → ℝ} {v : E n → ℝ → ℝ}
    (hv_def : v = fun x t ↦ u x t + ε * ‖x‖ ^ 2) :
    ∀ x t, (x, t) ∈ Interior n l T
    → deriv (fun t' ↦ v x t') t = deriv (fun t' ↦ u x t') t :=
  fun x t _ ↦ by simp [hv_def]

lemma gradient_add_eventually {f g : E n → ℝ} {x : E n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (fun y => gradient (fun z => f z + g z) y) =ᶠ[𝓝 x] (fun y => gradient f y + gradient g y) := by
  filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
  unfold gradient
  erw [fderiv_add (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num)), map_add]

lemma laplacian_add (f g : E n → ℝ) (x : E n)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    laplacian (fun y => f y + g y) x = laplacian f x + laplacian g x := by
  unfold laplacian div_field
  erw [EventuallyEq.fderiv_eq (gradient_add_eventually n hf hg),
    fderiv_add (differentiableAt_gradient_of_contDiffAt n f x hf) (differentiableAt_gradient_of_contDiffAt n g x hg),
    map_add]

lemma laplacian_neg (f : E n → ℝ) (x : E n) :
    laplacian (fun y => -f y) x = -laplacian f x := by
  have hgradient : gradient (fun y ↦ -f y) =ᶠ[nhds x] fun y ↦ -gradient f y := by
    filter_upwards with y
    unfold gradient
    erw [fderiv_neg]
    exact map_neg _ _
  unfold laplacian div_field
  erw [hgradient.fderiv_eq, fderiv_neg]
  push_cast
  rw [LinearMap.map_neg]

lemma diff_shifted_f (f : E n → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (y x' : E n) :
  DifferentiableAt ℝ (fun x'' => f (x'' - y)) x' := by
  exact Differentiable.differentiableAt ((hf_smooth.differentiable (by exact WithTop.top_ne_zero)).comp (differentiable_id.sub (differentiable_const y)))

lemma gradient_const_mul (Φ f : E n → ℝ) (hf_smooth : ContDiff ℝ ⊤ f) (y : E n) (x' : E n) :
    gradient (fun x'' => Φ y * f (x'' - y)) x' = Φ y • gradient (fun x'' => f (x'' - y)) x' := by
  simp_rw [← smul_eq_mul]
  unfold gradient
  rw [fderiv_fun_const_smul (diff_shifted_f n f hf_smooth y x') (Φ y)]
  exact map_smul (InnerProductSpace.toDual ℝ (E n)).symm (Φ y) (fderiv ℝ (fun x'' => f (x'' - y)) x')

lemma gradient_const_mul_scalar {c : ℝ} {f : E n → ℝ} {x : E n} (hf : DifferentiableAt ℝ f x) :
    gradient (fun x' ↦ c * f x') x = c • gradient f x := by
  unfold gradient
  rw [fderiv_const_mul]
  exact map_smul (InnerProductSpace.toDual ℝ (E n)).symm c (fderiv ℝ f x)
  · exact hf

lemma gradient_norm_sq (x : E n) :
    gradient (fun x' ↦ ‖x'‖ ^ 2) x = (2 : ℝ) • x := by
  unfold gradient
  rw [show fderiv ℝ (fun x' ↦ ‖x'‖ ^ 2) x = (2 : ℝ) • InnerProductSpace.toDual ℝ (E n) x by
    ext y
    rw [fderiv_norm_sq_apply]
    simp]
  rw [map_smul]
  rw [LinearIsometryEquiv.symm_apply_apply]

lemma fderiv_smul_id {c : ℝ} (x : E n) :
    fderiv ℝ (fun x' : E n ↦ c • x') x = c • ContinuousLinearMap.id ℝ (E n) := by
  have h_diff : DifferentiableAt ℝ (fun x' : E n ↦ x') x := differentiableAt_id
  erw [fderiv_const_smul h_diff c]
  erw [fderiv_id]

lemma trace_id_E :
    LinearMap.trace ℝ (E n) (ContinuousLinearMap.id ℝ (E n)) = n := by
  have h_coe : (ContinuousLinearMap.id ℝ (E n) : E n →ₗ[ℝ] E n) = LinearMap.id := rfl
  rw [h_coe]
  rw [LinearMap.trace_id]
  simp

lemma trace_smul_id {c : ℝ} :
    LinearMap.trace ℝ (E n) (c • ContinuousLinearMap.id ℝ (E n)) = c * (n : ℝ) := by
  rw [← ContinuousLinearMap.toLinearMap_smul]
  erw [LinearMap.map_smul]
  rw [trace_id_E]
  rw [smul_eq_mul]

lemma gradient_norm_sq_smul {ε : ℝ} (x : E n) :
    gradient (fun x' ↦ ε * ‖x'‖ ^ 2) x = (2 * ε) • x := by
  have hd : DifferentiableAt ℝ (fun x' : E n ↦ ‖x'‖ ^ 2) x :=
    DifferentiableAt.norm_sq ℝ (differentiableAt_id : DifferentiableAt ℝ (fun x' : E n ↦ x') x)
  rw [gradient_const_mul_scalar n hd]
  rw [gradient_norm_sq n x]
  simp [smul_smul, mul_comm]

lemma laplacian_norm_sq_smul {ε : ℝ} (x : E n) :
    laplacian (fun x' ↦ ε * ‖x'‖ ^ 2) x = 2 * (n : ℝ) * ε := by
  unfold laplacian div_field
  have h_grad : (fun x' : E n ↦ gradient (fun y ↦ ε * ‖y‖ ^ 2) x') = (fun x' : E n ↦ (2 * ε) • x') := by
    funext x'
    exact gradient_norm_sq_smul n x'
  simp_rw [h_grad]
  have h_fderiv : fderiv ℝ (fun x' : E n ↦ (2 * ε) • x') x = (2 * ε) • ContinuousLinearMap.id ℝ (E n) := by
    exact fderiv_smul_id n x
  rw [h_fderiv]
  erw [trace_smul_id]
  ring

lemma perturb_laplacian
    {l T ε : ℝ} {u : E n → ℝ → ℝ} {v : E n → ℝ → ℝ}
    (hv_def : v = fun x t ↦ u x t + ε * ‖x‖ ^ 2)
    (h_smooth : ContDiffOn ℝ 2 (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T)) :
    ∀ x t, (x, t) ∈ Interior n l T
    → laplacian (fun x' ↦ v x' t) x = laplacian (fun x' ↦ u x' t) x + 2 * (n : ℝ) * ε := by
  intro x t ht
  rw [hv_def]
  have hc_u : ContDiffAt ℝ 2 (fun x' ↦ u x' t) x := by
    exact (h_smooth.contDiffAt (h_int_nhds n (x, t) ht)).comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hc_norm : ContDiffAt ℝ 2 (fun x' ↦ ε * ‖x'‖ ^ 2) x := by
    apply ContDiffAt.mul
    · exact contDiffAt_const
    · exact ContDiffAt.norm_sq ℝ (contDiffAt_id : ContDiffAt ℝ 2 (fun x' : E n ↦ x') x)
  rw [laplacian_add n (fun x' ↦ u x' t) (fun x' ↦ ε * ‖x'‖ ^ 2) x hc_u hc_norm]
  rw [laplacian_norm_sq_smul]

lemma heat_equation_perturbation_ineq_nd
    {l T α ε : ℝ} {u : E n → ℝ → ℝ} {v : E n → ℝ → ℝ}
    (hn : 0 < n) (hα : 0 < α) (hε : 0 < ε)
    (hv_def : v = fun x t ↦ u x t + ε * ‖x‖ ^ 2)
    (h_smooth : ContDiffOn ℝ 2 (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T))
    (h_pde : ∀ (x : E n) (t : ℝ), (x, t) ∈ Interior n l T →
      deriv (fun t' ↦ u x t') t = α * laplacian (fun x' ↦ u x' t) x) :
    ∀ x t, (x, t) ∈ Interior n l T →
    deriv (fun t' ↦ v x t') t - α * laplacian (fun x' ↦ v x' t) x < 0 :=
  fun x t ht_interior ↦ by
    rw [perturb_dt n hv_def x t ht_interior]
    rw [perturb_laplacian n hv_def h_smooth x t ht_interior]
    rw [h_pde x t ht_interior]
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    aesop

lemma mem_Omega_spatial_of_int {l : ℝ} {x₀ : E n} (hx0_in : x₀ ∈ Ω_spatial_int n l) :
    x₀ ∈ Ω_spatial n l := by
  unfold Ω_spatial_int at hx0_in
  unfold Ω_spatial
  intro i hi
  exact Ioo_subset_Icc_self (hx0_in i hi)

lemma fderivWithin_slice_eq_comp_inl {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {t : Set ℝ}
    {f : E × ℝ → F} {p : E × ℝ}
    (h_unique : UniqueDiffWithinAt ℝ s p.1)
    (hp2 : p.2 ∈ t)
    (hf : DifferentiableWithinAt ℝ f (s ×ˢ t) p) :
    fderivWithin ℝ (fun x' ↦ f (x', p.2)) s p.1 =
    (fderivWithin ℝ f (s ×ˢ t) p).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
  have h_ix_diff : DifferentiableWithinAt ℝ (fun x' ↦ (x', p.2)) s p.1 :=
    differentiableWithinAt_id.prodMk (differentiableWithinAt_const p.2)
  have h_maps : Set.MapsTo (fun x' ↦ (x', p.2)) s (s ×ˢ t) := fun x' hx' ↦ Set.mk_mem_prod hx' hp2
  erw [fderivWithin_comp p.1 hf h_ix_diff h_maps h_unique]
  have h_has : HasFDerivAt (fun x' ↦ (x', p.2)) (ContinuousLinearMap.inl ℝ E ℝ) p.1 := by
    have h_eq : (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ) = ContinuousLinearMap.inl ℝ E ℝ := by ext x <;> rfl
    exact h_eq ▸ HasFDerivAt.prodMk (hasFDerivAt_id p.1) (hasFDerivAt_const p.2 p.1)
  rw [h_has.hasFDerivWithinAt.fderivWithin h_unique]

lemma continuousOn_second_spatial_fderiv {n : ℕ} {l T : ℝ} {u : E n → ℝ → ℝ} (hl : 0 < l) (hT : 0 < T)
    (h_smooth : ContDiffOn ℝ 2 (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T)) :
    ContinuousOn (fun p : E n × ℝ ↦
      fderivWithin ℝ (fun x' ↦ fderivWithin ℝ (fun y ↦ u y p.2) (Ω_spatial n l) x') (Ω_spatial n l) p.1) (Ω_T n l T) := by
  have h_unique_spatial : UniqueDiffOn ℝ (Ω_spatial n l) := by
    unfold Ω_spatial
    refine (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).uniqueDiffOn_preimage_iff.mpr ?_
    apply UniqueDiffOn.pi (𝕜 := ℝ)
    intro i _
    exact uniqueDiffOn_Icc hl
  let u_1 := fun p' : E n × ℝ ↦ fderivWithin ℝ (fun x' ↦ u x' p'.2) (Ω_spatial n l) p'.1
  have h_unique_T : UniqueDiffOn ℝ (Ω_T n l T) := hΩ n hl hT
  let CompL1 := (ContinuousLinearMap.compL ℝ (E n) (E n × ℝ) ℝ).flip (ContinuousLinearMap.inl ℝ (E n) ℝ)
  have h_u1_eq : Set.EqOn u_1 (fun p' ↦ CompL1 (fderivWithin ℝ (fun p'' : E n × ℝ ↦ u p''.1 p''.2) (Ω_T n l T) p')) (Ω_T n l T) := by
    intro p hp
    exact fderivWithin_slice_eq_comp_inl (h_unique_spatial p.1 hp.1) hp.2 (h_smooth.differentiableOn (by norm_num) p hp)
  have h_fderiv_u_C1 : ContDiffOn ℝ 1 (fun p ↦ fderivWithin ℝ (fun p' : E n × ℝ ↦ u p'.1 p'.2) (Ω_T n l T) p) (Ω_T n l T) :=
    h_smooth.fderivWithin h_unique_T (by norm_num)
  have h_u1_C1 : ContDiffOn ℝ 1 u_1 (Ω_T n l T) :=
    (CompL1.contDiff.contDiffOn.comp h_fderiv_u_C1 (Set.mapsTo_univ _ _)).congr h_u1_eq
  let CompL1_u1 := (ContinuousLinearMap.compL ℝ (E n) (E n × ℝ) (E n →L[ℝ] ℝ)).flip (ContinuousLinearMap.inl ℝ (E n) ℝ)
  have h_partial_u1_eq : Set.EqOn (fun p ↦ fderivWithin ℝ (fun x' ↦ u_1 (x', p.2)) (Ω_spatial n l) p.1)
      (fun p ↦ CompL1_u1 (fderivWithin ℝ u_1 (Ω_T n l T) p)) (Ω_T n l T) := by
    intro p hp
    exact fderivWithin_slice_eq_comp_inl (h_unique_spatial p.1 hp.1) hp.2 (h_u1_C1.differentiableOn (by norm_num) p hp)
  have h_fderiv_u1_cont : ContinuousOn (fun p ↦ fderivWithin ℝ u_1 (Ω_T n l T) p) (Ω_T n l T) :=
    h_u1_C1.continuousOn_fderivWithin h_unique_T (by norm_num)
  exact (CompL1_u1.continuous.comp_continuousOn h_fderiv_u1_cont).congr h_partial_u1_eq

lemma fderivWithin_clm_comp_of_inv {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (L_inv : G →L[ℝ] F) (h_inv : ∀ y, L_inv (L y) = y)
    (f : E → F) (s : Set E) (x : E) (hx : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (L ∘ f) s x = L.comp (fderivWithin ℝ f s x) := by
  by_cases h_diff : DifferentiableWithinAt ℝ f s x
  · have h_maps : Set.MapsTo f s Set.univ := by exact fun ⦃x⦄ a ↦ trivial
    have h_L_diff : DifferentiableWithinAt ℝ L Set.univ (f x) := L.differentiableAt.differentiableWithinAt
    rw [fderivWithin_comp x h_L_diff h_diff h_maps hx, fderivWithin_univ, ContinuousLinearMap.fderiv]
  · have h_not_diff : ¬ DifferentiableWithinAt ℝ (L ∘ f) s x := by
      intro h
      have h_maps : Set.MapsTo (L ∘ f) s Set.univ := by exact fun ⦃x⦄ a ↦ trivial
      have h_L_inv_diff : DifferentiableWithinAt ℝ L_inv Set.univ (L (f x)) := L_inv.differentiableAt.differentiableWithinAt
      have h_comp := DifferentiableWithinAt.comp x h_L_inv_diff h h_maps
      have h_eq : (L_inv ∘ L ∘ f) = f := by ext y; exact h_inv (f y)
      rw [h_eq] at h_comp
      exact h_diff h_comp
    rw [fderivWithin_zero_of_not_differentiableWithinAt h_diff,
        fderivWithin_zero_of_not_differentiableWithinAt h_not_diff]
    ext; simp

lemma continuousOn_spatial_laplacian {n : ℕ} {l T : ℝ} {u : E n → ℝ → ℝ} (hl : 0 < l) (hT : 0 < T)
    (h_smooth : ContDiffOn ℝ 2 (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T)) :
    ContinuousOn (fun p : E n × ℝ ↦ laplacianWithin (fun x' ↦ u x' p.2) (Ω_spatial n l) p.1) (Ω_T n l T) := by
  unfold laplacianWithin div_fieldWithin
  have h_unique_spatial : UniqueDiffOn ℝ (Ω_spatial n l) := by
    unfold Ω_spatial
    refine (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).uniqueDiffOn_preimage_iff.mpr ?_
    apply UniqueDiffOn.pi (𝕜 := ℝ)
    exact?
  let L := (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearMap
  let L_inv := (InnerProductSpace.toDual ℝ (E n)).toContinuousLinearMap
  let CompL := ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) (E n) L
  have h_fderiv_grad_eq : Set.EqOn (fun p : E n × ℝ ↦ fderivWithin ℝ (fun x' ↦ gradientWithin (fun y ↦ u y p.2) (Ω_spatial n l) x') (Ω_spatial n l) p.1)
      (fun p ↦ CompL (fderivWithin ℝ (fun x' ↦ fderivWithin ℝ (fun y ↦ u y p.2) (Ω_spatial n l) x') (Ω_spatial n l) p.1)) (Ω_T n l T) := by
    intro p hp
    have h_grad : (fun x' ↦ gradientWithin (fun y ↦ u y p.2) (Ω_spatial n l) x') = L ∘ (fun x' ↦ fderivWithin ℝ (fun y ↦ u y p.2) (Ω_spatial n l) x') := rfl
    simp_rw [h_grad]
    exact fderivWithin_clm_comp_of_inv L L_inv (fun y ↦ (InnerProductSpace.toDual ℝ (E n)).apply_symm_apply y)
      (fun x' ↦ fderivWithin ℝ (fun y ↦ u y p.2) (Ω_spatial n l) x') (Ω_spatial n l) p.1 (h_unique_spatial p.1 hp.1)
  have h_continuous_second_fderiv := continuousOn_second_spatial_fderiv hl hT h_smooth
  have h_continuous_fderiv_grad := (CompL.continuous.comp_continuousOn h_continuous_second_fderiv).congr h_fderiv_grad_eq
  have h_continuous_trace : Continuous (fun (M : E n →L[ℝ] E n) ↦ LinearMap.trace ℝ (E n) M) := by
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    have h_eq : (fun (M : E n →L[ℝ] E n) ↦ LinearMap.trace ℝ (E n) M) = fun M ↦ ∑ i : Fin n, ⟪b i, M (b i)⟫_ℝ := by
      ext M; exact LinearMap.trace_eq_sum_inner (M : E n →ₗ[ℝ] E n) b
    rw [h_eq]
    exact continuous_finsetSum _ fun i _ ↦ continuous_const.inner (ContinuousLinearMap.apply ℝ (E n) (b i)).continuous
  exact h_continuous_trace.comp_continuousOn h_continuous_fderiv_grad

lemma u_laplacian_continuous {l T : ℝ} {x₀ : E n} {u : E n → ℝ → ℝ}
    (hT : 0 < T) (hl : 0 < l)
    (hx0_in : x₀ ∈ Ω_spatial_int n l)
    (h_smooth : ContDiffOn ℝ 2 (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T)) :
    ContinuousWithinAt (fun t ↦ laplacian (fun x' ↦ u x' t) x₀) (Iic T) T := by
  have h_int : x₀ ∈ interior (Ω_spatial n l) := by
    have h1 : IsOpen (Ω_spatial_int n l) :=
      IsOpen.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ)) (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo)
    have h2 : Ω_spatial_int n l ⊆ Ω_spatial n l := by
      intro y hy i hi
      exact Ioo_subset_Icc_self (hy i hi)
    exact interior_maximal h2 h1 hx0_in
  have h_eq : (fun t ↦ laplacian (fun x' ↦ u x' t) x₀) = (fun t ↦ laplacianWithin (fun x' ↦ u x' t) (Ω_spatial n l) x₀) := by
    funext t
    exact (laplacianWithin_eq_laplacian n h_int).symm
  rw [h_eq]
  apply ContinuousWithinAt.mono_of_mem_nhdsWithin (t := Icc 0 T)
  · have h_cont_lapl := continuousOn_spatial_laplacian hl hT h_smooth
    have h_pt : (x₀, T) ∈ Ω_T n l T := by
      unfold Ω_T
      exact Set.mk_mem_prod (mem_Omega_spatial_of_int n hx0_in) (Set.right_mem_Icc.mpr hT.le)
    have h_comp : ContinuousWithinAt (fun t ↦ (x₀, t)) (Icc 0 T) T :=
      continuousWithinAt_const.prodMk continuousWithinAt_id
    have h_mapsTo : Set.MapsTo (fun t ↦ (x₀, t)) (Icc 0 T) (Ω_T n l T) := by
      intro t ht
      unfold Ω_T
      exact Set.mk_mem_prod (mem_Omega_spatial_of_int n hx0_in) ht
    change ContinuousWithinAt ((fun p : E n × ℝ ↦ laplacianWithin (fun x' ↦ u x' p.2) (Ω_spatial n l) p.1) ∘ (fun t ↦ (x₀, t))) (Icc 0 T) T
    exact ContinuousWithinAt.comp (h_cont_lapl (x₀, T) h_pt) h_comp h_mapsTo
  · exact Icc_mem_nhdsLE hT

lemma derivWithin_slice_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {t : Set ℝ}
    {f : E × ℝ → F} {p : E × ℝ}
    (h_unique : UniqueDiffWithinAt ℝ t p.2)
    (hp1 : p.1 ∈ s)
    (hf : DifferentiableWithinAt ℝ f (s ×ˢ t) p) :
    derivWithin (fun y ↦ f (p.1, y)) t p.2 =
    fderivWithin ℝ f (s ×ˢ t) p (0, 1) := by
  have h_ix_diff : DifferentiableWithinAt ℝ (fun y ↦ (p.1, y)) t p.2 :=
    (differentiableWithinAt_const p.1).prodMk differentiableWithinAt_id
  have h_maps : Set.MapsTo (fun y ↦ (p.1, y)) t (s ×ˢ t) := fun y hy ↦ Set.mk_mem_prod hp1 hy
  unfold derivWithin
  erw [fderivWithin_comp p.2 hf h_ix_diff h_maps h_unique]
  have h_has : HasFDerivAt (fun y ↦ (p.1, y)) (ContinuousLinearMap.inr ℝ E ℝ) p.2 := by
    have h_eq : (0 : ℝ →L[ℝ] E).prod (ContinuousLinearMap.id ℝ ℝ) = ContinuousLinearMap.inr ℝ E ℝ := by ext <;> rfl
    exact h_eq ▸ HasFDerivAt.prodMk (hasFDerivAt_const p.1 p.2) (hasFDerivAt_id p.2)
  rw [h_has.hasFDerivWithinAt.fderivWithin h_unique]
  rfl

lemma u_t_continuous {l T : ℝ} {x₀ : E n} {u : E n → ℝ → ℝ}
    (hT : 0 < T) (hl : 0 < l) (hx0_in : x₀ ∈ Ω_spatial_int n l)
    (h_smooth : ContDiffOn ℝ 2 (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T)) :
    ContinuousWithinAt (fun t ↦ derivWithin (fun s ↦ u x₀ s) (Iic T) t) (Iic T) T := by
  have h_nhds_eq : 𝓝[Iic T] T = 𝓝[Icc 0 T] T := by
    have hs : Ici (0 : ℝ) ∈ 𝓝 T := mem_of_superset (Ioi_mem_nhds hT) fun x (hx : 0 < x) ↦ (le_of_lt hx : 0 ≤ x)
    rw [← nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hs)]
    congr 1
  have h_deriv_eq_Ioc : ∀ t ∈ Ioc 0 T, derivWithin (fun s ↦ u x₀ s) (Iic T) t = derivWithin (fun s ↦ u x₀ s) (Icc 0 T) t := fun t ht ↦ by
    rw [← derivWithin_inter (mem_of_superset (Ioi_mem_nhds ht.1) Ioi_subset_Ici_self)]
    congr 1
    exact inter_comm (Iic T) (Ici 0)
  have h_deriv_eq : ∀ t ∈ Icc 0 T, derivWithin (fun s ↦ u x₀ s) (Icc 0 T) t =
      (fderivWithin ℝ (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T) (x₀, t)) (0, 1) := fun t ht ↦ by
    exact derivWithin_slice_eq (uniqueDiffOn_Icc hT t ht) (mem_Omega_spatial_of_int n hx0_in)
      (h_smooth.differentiableOn (by norm_num) (x₀, t) (Set.mk_mem_prod (mem_Omega_spatial_of_int n hx0_in) ht))
  have h_F_cont : ContinuousOn (fun p ↦ fderivWithin ℝ (fun p' : E n × ℝ ↦ u p'.1 p'.2) (Ω_T n l T) p) (Ω_T n l T) :=
    h_smooth.continuousOn_fderivWithin (hΩ n hl hT) (by norm_num)
  have h_H_cont : ContinuousOn (fun t ↦ (fderivWithin ℝ (fun p' : E n × ℝ ↦ u p'.1 p'.2) (Ω_T n l T) (x₀, t)) (0, 1)) (Icc 0 T) := by
    let eval_map : (E n × ℝ →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (0, 1)
    exact eval_map.continuous.comp_continuousOn (h_F_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ Set.mk_mem_prod (mem_Omega_spatial_of_int n hx0_in) ht))
  have h_Ioc_nhds : Ioc 0 T ∈ 𝓝[Icc 0 T] T := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Ioi 0, Ioi_mem_nhds hT, fun _ hx ↦ ⟨hx.1, hx.2.2⟩⟩
  have h_eventually_eq : (fun t ↦ derivWithin (fun s ↦ u x₀ s) (Iic T) t) =ᶠ[𝓝[Icc 0 T] T] (fun t ↦ (fderivWithin ℝ (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T) (x₀, t)) (0, 1)) := by
    apply EventuallyEq.trans
    · exact Eventually.mono h_Ioc_nhds h_deriv_eq_Ioc
    · exact Eventually.mono self_mem_nhdsWithin h_deriv_eq
  have h_cont_Icc : ContinuousWithinAt (fun t ↦ (fderivWithin ℝ (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T) (x₀, t)) (0, 1)) (Icc 0 T) T :=
    h_H_cont T ⟨hT.le, le_rfl⟩
  have h_eq_at_T : derivWithin (fun s ↦ u x₀ s) (Iic T) T = (fderivWithin ℝ (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T) (x₀, T)) (0, 1) := by
    rw [h_deriv_eq_Ioc T ⟨hT, le_rfl⟩, h_deriv_eq T ⟨hT.le, le_rfl⟩]
  have h_res := h_cont_Icc.congr_of_eventuallyEq h_eventually_eq h_eq_at_T
  unfold ContinuousWithinAt at h_res ⊢
  rw [h_nhds_eq]
  exact h_res

lemma pde_boundary_val {l T α ε : ℝ} {x₀ : E n} {u : E n → ℝ → ℝ}
    (hT : 0 < T) (hl : 0 < l) (hx0_in : x₀ ∈ Ω_spatial_int n l)
    (h_smooth : ContDiffOn ℝ 2 (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T))
    (h_pde : ∀ (x : E n) (t : ℝ), (x, t) ∈ Interior n l T →
      deriv (fun t' ↦ u x t') t = α * laplacian (fun x' ↦ u x' t) x) :
    let v := fun x t ↦ u x t + ε * ‖x‖ ^ 2
    derivWithin (fun t ↦ v x₀ t) (Iic T) T - α * laplacian (fun x ↦ v x T) x₀ = -2 * (n : ℝ) * α * ε := by
  intro v
  have h_v_t : derivWithin (fun t ↦ v x₀ t) (Iic T) T = derivWithin (fun t ↦ u x₀ t) (Iic T) T :=
    derivWithin_add_const (ε * ‖x₀‖ ^ 2)
  have h_v_lapl : laplacian (fun x ↦ v x T) x₀ = laplacian (fun x ↦ u x T) x₀ + 2 * (n : ℝ) * ε := by
    change laplacian (fun x ↦ u x T + ε * ‖x‖ ^ 2) x₀ = _
    have h_open_int : IsOpen (Ω_spatial_int n l) :=
      IsOpen.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ)) (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo)
    have h_nhds : Ω_spatial_int n l ∈ 𝓝 x₀ := h_open_int.mem_nhds hx0_in
    have hc_u : ContDiffAt ℝ 2 (fun x' ↦ u x' T) x₀ := (h_smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun x' hx' ↦ ⟨mem_Omega_spatial_of_int n hx', hT.le, le_rfl⟩)).contDiffAt h_nhds
    have hc_norm : ContDiffAt ℝ 2 (fun x' ↦ ε * ‖x'‖ ^ 2) x₀ :=
      contDiffAt_const.mul <| ContDiffAt.norm_sq ℝ contDiffAt_id
    rw [laplacian_add n _ _ x₀ hc_u hc_norm, laplacian_norm_sq_smul]
  have h_pde_T : derivWithin (fun t ↦ u x₀ t) (Iic T) T = α * laplacian (fun x ↦ u x T) x₀ := by
    have h_lhs_cont : ContinuousWithinAt (fun t ↦ derivWithin (fun t' ↦ u x₀ t') (Iic T) t) (Iio T) T :=
      (u_t_continuous n hT hl hx0_in h_smooth).mono Iio_subset_Iic_self
    have h_rhs_cont : ContinuousWithinAt (fun t ↦ α * laplacian (fun x ↦ u x t) x₀) (Iio T) T :=
      (continuousWithinAt_const.mul (u_laplacian_continuous n hT hl hx0_in h_smooth)).mono Iio_subset_Iic_self
    have h_ev_eq : (fun t ↦ derivWithin (fun t' ↦ u x₀ t') (Iic T) t) =ᶠ[𝓝[<] T] (fun t ↦ α * laplacian (fun x ↦ u x t) x₀) := by
      filter_upwards [Ioo_mem_nhdsLT_of_mem (Set.right_mem_Ioc.mpr hT)] with t ht
      rw [derivWithin_of_mem_nhds (Iic_mem_nhds ht.2)]
      exact h_pde x₀ t ⟨hx0_in, ht⟩
    have h_ne_bot : NeBot (𝓝[<] T) := nhdsWithin_Iio_neBot (by exact Preorder.le_refl T)
    exact tendsto_nhds_unique h_lhs_cont.tendsto (h_rhs_cont.tendsto.congr' (by exact id (EventuallyEq.symm h_ev_eq)))
  rw [h_v_t, h_v_lapl, h_pde_T]
  ring

lemma heat_equation_no_interior_max
    {l T α ε : ℝ} {u : E n → ℝ → ℝ} {v : E n → ℝ → ℝ}
    (hα : 0 < α)
    (hv_def : v = fun x t ↦ u x t + ε * ‖x‖ ^ 2)
    (h_smooth : ContDiffOn ℝ 2 (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T))
    (h_int_nhds : ∀ p ∈ Interior n l T, Ω_T n l T ∈ 𝓝 p)
    (h_v_pde_ineq : ∀ x t, (x, t) ∈ Interior n l T →
      deriv (fun t' ↦ v x t') t - α * laplacian (fun x' ↦ v x' t) x < 0) :
    ∀ x₀ t₀, (x₀, t₀) ∈ Interior n l T → ¬ IsMaxOn (fun p ↦ v p.1 p.2) (Ω_T n l T) (x₀, t₀) := by
  intro x₀ t₀ h_int h_max
  have h_local_max : IsLocalMax (fun p ↦ v p.1 p.2) (x₀, t₀) := h_max.isLocalMax (h_int_nhds _ h_int)
  have hc_v : ContDiffAt ℝ 2 (fun p : E n × ℝ ↦ v p.1 p.2) (x₀, t₀) := by
    rw [hv_def]
    exact (h_smooth.contDiffAt (h_int_nhds _ h_int)).add (contDiffAt_const.mul <| ContDiffAt.norm_sq ℝ contDiffAt_fst)
  have h_v_t_zero : deriv (fun t' ↦ v x₀ t') t₀ = 0 :=
    IsLocalMax.hasDerivAt_eq_zero
      (h_local_max.comp_tendsto (g := fun t' ↦ (x₀, t')) ((continuous_const.prodMk continuous_id).tendsto t₀))
      ((hc_v.comp t₀ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num)).hasDerivAt
  have h_v_lapl_nonpos : laplacian (fun x' ↦ v x' t₀) x₀ ≤ 0 :=
    local_max_implies_laplacian_nonpos n (hc_v.comp x₀ (contDiffAt_id.prodMk contDiffAt_const))
      (h_local_max.comp_tendsto (g := fun x' ↦ (x', t₀)) ((continuous_id.prodMk continuous_const).tendsto x₀))
  have h_ineq := h_v_pde_ineq x₀ t₀ h_int
  rw [h_v_t_zero] at h_ineq
  nlinarith

lemma Omega_T_decompose {l T : ℝ} {p : E n × ℝ} (hp : p ∈ Ω_T n l T) :
    p ∈ S_boundary n l T ∨ p ∈ Interior n l T ∨ p ∈ Top_Edge n l T := by
  obtain ⟨x, t⟩ := p
  simp only [Ω_T, S_boundary, Interior, Top_Edge, Set.mem_prod,
    Set.mem_union, Set.mem_singleton_iff] at hp ⊢
  rcases hp with ⟨hx, ht⟩
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · exact Or.inl (Or.inl ⟨hx, rfl⟩)
  by_cases hx_int : x ∈ Ω_spatial_int n l
  · rcases eq_or_lt_of_le ht.2 with rfl | htT
    · exact Or.inr (Or.inr ⟨hx_int, rfl⟩)
    · exact Or.inr (Or.inl ⟨hx_int, ⟨ht0, htT⟩⟩)
  · apply Or.inl; apply Or.inr
    refine ⟨?_, ht⟩
    change x ∈ closure (Ω_spatial n l) \ interior (Ω_spatial n l)
    have h_int_eq : interior (Ω_spatial n l) = Ω_spatial_int n l := by
      unfold Ω_spatial Ω_spatial_int
      have h_homeo := (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).preimage_interior (Set.pi univ (fun _ ↦ Icc 0 l))
      exact h_homeo.symm.trans (by
        rw [interior_pi_set]
        · simp_rw [interior_Icc]
          exact preimage_congr (congrFun rfl)
        · exact Set.finite_univ
      )
    rw [h_int_eq]
    exact ⟨subset_closure hx, hx_int⟩

lemma deriv_nonneg_of_isLocalMaxOn_Icc_right_S
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hC1 : ContDiffOn ℝ 1 f (Icc 0 T))
    (hmax : IsLocalMaxOn f (Icc 0 T) T) :
    0 ≤ derivWithin f (Icc 0 T) T := by
  have hy : (-T : ℝ) ∈ posTangentConeAt (Icc 0 T) T := by
    apply mem_posTangentConeAt_of_segment_subset
    rintro _ ⟨c, d, hc, hd, hsum, rfl⟩
    exact ⟨by simp only [smul_eq_mul]; nlinarith, by simp only [smul_eq_mul]; nlinarith⟩
  have h_eq : fderivWithin ℝ f (Icc 0 T) T (-T) = derivWithin f (Icc 0 T) T * -T := by
    rw [show (-T : ℝ) = -T • (1 : ℝ) by simp, map_smul]
    simp [fderivWithin_derivWithin, mul_comm]
  have hnonpos := hmax.hasFDerivWithinAt_nonpos ((hC1 T ⟨hT.le, le_rfl⟩).differentiableWithinAt (by
  exact
    Ne.symm (zero_ne_one' (WithTop ℕ∞)))).hasFDerivWithinAt hy
  rw [h_eq] at hnonpos
  nlinarith

lemma heat_equation_no_top_edge_max
    {l T α ε : ℝ} {u v : E n → ℝ → ℝ}
    (hn : 0 < n) (hl : 0 < l)
    (hT : 0 < T) (hα : 0 < α) (hε : 0 < ε)
    (hv_def : v = fun x t ↦ u x t + ε * ‖x‖ ^ 2)
    (h_smooth : ContDiffOn ℝ 2 (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T))
    (h_pde : ∀ x t, (x, t) ∈ Interior n l T →
      deriv (fun t' ↦ u x t') t = α * laplacian (fun x' ↦ u x' t) x) :
    ∀ x₀, x₀ ∈ Ω_spatial_int n l → ¬ IsMaxOn (fun p ↦ v p.1 p.2) (Ω_T n l T) (x₀, T) := by
  intro x₀ hx0_int hmax
  subst hv_def
  have h_open_int : IsOpen (Ω_spatial_int n l) :=
    IsOpen.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ)) (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo)
  have h_nhds : Ω_spatial_int n l ∈ 𝓝 x₀ := h_open_int.mem_nhds hx0_int
  have h_vxx_le : laplacian (fun x ↦ u x T + ε * ‖x‖ ^ 2) x₀ ≤ 0 := by
    have h_map : Set.MapsTo (fun x' ↦ (x', T)) (Ω_spatial_int n l) (Ω_T n l T) := fun x' hx' ↦ Set.mk_mem_prod (mem_Omega_spatial_of_int n hx') (Set.right_mem_Icc.mpr hT.le)
    have hc_u : ContDiffAt ℝ 2 (fun x' ↦ u x' T) x₀ := (h_smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn h_map).contDiffAt h_nhds
    have hc_v : ContDiffAt ℝ 2 (fun x ↦ u x T + ε * ‖x‖ ^ 2) x₀ := hc_u.add (contDiffAt_const.mul (ContDiffAt.norm_sq ℝ contDiffAt_id))
    have h_max_x : IsLocalMax (fun x ↦ u x T + ε * ‖x‖ ^ 2) x₀ :=
      (show IsMaxOn (fun x ↦ u x T + ε * ‖x‖ ^ 2) (Ω_spatial_int n l) x₀ from fun x hx ↦ hmax (Set.mk_mem_prod (mem_Omega_spatial_of_int n hx) (Set.right_mem_Icc.mpr hT.le))).isLocalMax h_nhds
    exact local_max_implies_laplacian_nonpos n hc_v h_max_x
  have h_vt_ge : 0 ≤ derivWithin (fun t ↦ u x₀ t + ε * ‖x₀‖ ^ 2) (Iic T) T := by
    erw [derivWithin_congr_set' T (eventually_of_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)) fun y hy ↦ propext (Iff.intro (fun (h : y ∈ Iic T) ↦ And.intro (le_of_lt hy) h) (fun (h : y ∈ Icc 0 T) ↦ h.2)))]
    apply deriv_nonneg_of_isLocalMaxOn_Icc_right_S hT
    · have h_map_t : Set.MapsTo (fun t ↦ (x₀, t)) (Icc 0 T) (Ω_T n l T) := fun t ht ↦ Set.mk_mem_prod (mem_Omega_spatial_of_int n hx0_int) ht
      exact ((h_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn h_map_t).of_le (by norm_num)).add contDiffOn_const
    · exact eventually_of_mem self_mem_nhdsWithin fun t ht ↦ hmax (Set.mk_mem_prod (mem_Omega_spatial_of_int n hx0_int) ht)
  have hpde_eq := pde_boundary_val (ε := ε) n hT hl hx0_int h_smooth h_pde
  change derivWithin (fun t ↦ u x₀ t + ε * ‖x₀‖ ^ 2) (Iic T) T - α * laplacian (fun x ↦ u x T + ε * ‖x‖ ^ 2) x₀ = -2 * (n : ℝ) * α * ε at hpde_eq
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_rhs_neg : -2 * (n : ℝ) * α * ε < 0 := by
    have h_pos : 0 < 2 * (n : ℝ) * α * ε := by positivity
    linarith
  nlinarith

lemma max_v_on_S_boundary
  {l T : ℝ} {v : E n → ℝ → ℝ}
  (hT : 0 < T)
  (h_compact : IsCompact (Ω_T n l T))
  (h_nonempty : (Ω_T n l T).Nonempty)
  (h_v_cont : ContinuousOn (fun p : E n × ℝ ↦ v p.1 p.2) (Ω_T n l T))
  (h_no_int : ∀ x₀ t₀, (x₀, t₀) ∈ Interior n l T → ¬ IsMaxOn (fun p ↦ v p.1 p.2) (Ω_T n l T) (x₀, t₀))
  (h_no_top : ∀ x₀, x₀ ∈ Ω_spatial_int n l → ¬ IsMaxOn (fun p ↦ v p.1 p.2) (Ω_T n l T) (x₀, T)) :
  ∃ s_max ∈ S_boundary n l T, ∀ p ∈ Ω_T n l T, v p.1 p.2 ≤ v s_max.1 s_max.2 := by
  obtain ⟨⟨x₀, t₀⟩, hp_max_in, hp_max_val⟩ := h_compact.exists_isMaxOn h_nonempty h_v_cont
  rcases Omega_T_decompose n hp_max_in with h_S | h_Int | h_Top
  · exact ⟨(x₀, t₀), h_S, hp_max_val⟩
  · exact False.elim (h_no_int x₀ t₀ h_Int hp_max_val)
  · simp only [Top_Edge, Set.mem_prod, Set.mem_singleton_iff] at h_Top
    rcases h_Top with ⟨hx0_in, rfl⟩
    exact False.elim (h_no_top x₀ hx0_in hp_max_val)

theorem heat_equation_max_principle
    (u : E n → ℝ → ℝ) (hn : 0 < n) (hl : 0 < l) (hT : 0 < T) (hα : 0 < α)
    (h_smooth : ContDiffOn ℝ 2 (fun p : E n × ℝ ↦ u p.1 p.2) (Ω_T n l T))
    (h_pde : ∀ x t, (x, t) ∈ Interior n l T →
      deriv (fun t' ↦ u x t') t = α * laplacian (fun x' ↦ u x' t) x) :
    sSup ((fun p : E n × ℝ ↦ u p.1 p.2) '' (Ω_T n l T)) =
      sSup ((fun p : E n × ℝ ↦ u p.1 p.2) '' (S_boundary n l T)) := by
  have h_closed : IsClosed (Ω_spatial n l) :=
    IsClosed.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ)) (isClosed_set_pi fun _ _ ↦ isClosed_Icc)
  have h_sub : S_boundary n l T ⊆ Ω_T n l T := by
    rintro ⟨x, t⟩ (⟨hx, rfl⟩ | h)
    · exact ⟨hx, le_rfl, hT.le⟩
    · exact ⟨h_closed.closure_eq ▸ frontier_subset_closure h.1, h.2⟩
  have h_zero_in : (0 : E n) ∈ Ω_spatial n l := fun _ _ ↦ ⟨le_rfl, hl.le⟩
  have h_ne : (Ω_T n l T).Nonempty := ⟨(0, 0), h_zero_in, le_rfl, hT.le⟩
  have h_Sne : (S_boundary n l T).Nonempty := ⟨(0, 0), Or.inl ⟨h_zero_in, rfl⟩⟩
  have h_comp_spatial : IsCompact (Ω_spatial n l) :=
    (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isCompact_preimage.mpr (isCompact_univ_pi fun _ ↦ isCompact_Icc)
  have h_comp_front : IsCompact (frontier (Ω_spatial n l)) :=
    h_comp_spatial.of_isClosed_subset isClosed_frontier (fun _ hx ↦ h_closed.closure_eq ▸ frontier_subset_closure hx)
  have h_comp_T : IsCompact (Ω_T n l T) := h_comp_spatial.prod isCompact_Icc
  have h_Scomp : IsCompact (S_boundary n l T) :=
    (h_comp_spatial.prod isCompact_singleton).union (h_comp_front.prod isCompact_Icc)
  have h_Sbdd : BddAbove ((fun p : E n × ℝ ↦ u p.1 p.2) '' S_boundary n l T) :=
    (h_Scomp.image_of_continuousOn (h_smooth.continuousOn.mono h_sub)).bddAbove
  refine le_antisymm ?_ (csSup_le (h_Sne.image _) <| by
    rintro y ⟨p, hp, rfl⟩
    exact le_csSup (h_comp_T.image_of_continuousOn h_smooth.continuousOn).bddAbove ⟨p, h_sub hp, rfl⟩)
  apply le_of_forall_pos_le_add
  intro δ hδ
  let M := max (1 : ℝ) (sSup ((fun x : E n ↦ ‖x‖ ^ 2) '' Ω_spatial n l))
  have hM_pos : 0 < M := lt_max_iff.mpr (Or.inl zero_lt_one)
  let ε := δ / M
  have hε : 0 < ε := div_pos hδ hM_pos
  have h_norm_sq_le : ∀ x ∈ Ω_spatial n l, ‖x‖ ^ 2 ≤ M := fun x hx ↦
    (le_csSup (h_comp_spatial.image_of_continuousOn (continuous_norm.pow 2).continuousOn).bddAbove (Set.mem_image_of_mem _ hx)).trans (le_max_right 1 _)
  let v := fun x t ↦ u x t + ε * ‖x‖ ^ 2
  have hc_v_term : ContinuousOn (fun p : E n × ℝ ↦ ε * ‖p.1‖ ^ 2) (Ω_T n l T) :=
    (continuous_const.mul ((continuous_norm.comp continuous_fst).pow 2)).continuousOn
  obtain ⟨s, hs_in, hs_val⟩ := max_v_on_S_boundary n (v := v) hT h_comp_T h_ne
    (h_smooth.continuousOn.add hc_v_term)
    (heat_equation_no_interior_max (ε := ε) (u := u) (v := v) n hα rfl h_smooth (h_int_nhds n) <| heat_equation_perturbation_ineq_nd n hn hα hε rfl h_smooth h_pde)
    (heat_equation_no_top_edge_max (ε := ε) (u := u) (v := v) n hn hl hT hα hε rfl h_smooth h_pde)
  refine csSup_le (h_ne.image _) <| by
    rintro y ⟨p, hp, rfl⟩
    calc u p.1 p.2
      _ ≤ v p.1 p.2 := le_add_of_nonneg_right (by positivity)
      _ ≤ v s.1 s.2 := hs_val p hp
      _ = u s.1 s.2 + ε * ‖s.1‖ ^ 2 := rfl
      _ ≤ sSup ((fun p ↦ u p.1 p.2) '' S_boundary n l T) + ε * M :=
            add_le_add (le_csSup h_Sbdd ⟨s, hs_in, rfl⟩) (mul_le_mul_of_nonneg_left (h_norm_sq_le s.1 (h_sub hs_in).1) hε.le)
      _ = sSup ((fun p ↦ u p.1 p.2) '' S_boundary n l T) + δ := by
            rw [div_mul_cancel₀ δ hM_pos.ne']

end Heat
