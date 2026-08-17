import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import PDE.FunctionSpaces.SobolevSpace.HkSpaces
import PDE.Background.FunctionalAnalysis.HilbertWeakCompactness

open MeasureTheory ENNReal Filter Topology NNReal


variable {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}


--use weak derivative to define the partial derivatives of u, which are in Lp space, so we can integrate them against the coefficients aij, bi, c
noncomputable def partialU (i : Fin d) (u : H1U0 d U hU) : (Fin d → ℝ) → ℝ :=
  ((WkpU.weakDeriv u.val 1 (by norm_num) (fun _ => i)
      : (Fin d → ℝ) →ₘ[μU d U] ℝ) : (Fin d → ℝ) → ℝ)




--bookkeeping coefficients, aij matrix of spatially dependent functions, bi vector, c single func
structure ParabolicCoeffs (d : ℕ+) where
  a : Fin d → Fin d → (Fin d → ℝ) → ℝ
  b : Fin d → (Fin d → ℝ) → ℝ
  c : (Fin d → ℝ) → ℝ
  -- Coefficients are measurable (Evans assumes `L∞`); needed for the bilinear-form integrals
  -- to be honest (not Bochner junk) and to split/bound them.
  aMeasurable : ∀ i j, Measurable (a i j)
  bMeasurable : ∀ i, Measurable (b i)
  cMeasurable : Measurable c

namespace ParabolicCoeffs

variable (P : ParabolicCoeffs d)

--Evan's takes aij=aji as asumption for symmetry
def IsSymmetric : Prop := ∀ i j : Fin d, P.a i j = P.a j i

--Linf bound
def IsBounded (M : ℝ) : Prop :=
  (∀ i j : Fin d, ∀ x, |P.a i j x| ≤ M) ∧
  (∀ i : Fin d, ∀ x, |P.b i x| ≤ M) ∧
  (∀ x, |P.c x| ≤ M)

--Defn uniform parabolic
def IsUniformlyParabolic (U : Set (Fin d → ℝ)) (θ : ℝ) : Prop :=
  0 < θ ∧
    ∀ᵐ x ∂(μU d U),
      ∀ ξ : Fin d → ℝ,
        θ * ∑ i : Fin d, ξ i ^ 2
          ≤ ∑ i : Fin d, ∑ j : Fin d, P.a i j x * ξ i * ξ j

end ParabolicCoeffs





--Bilinear form of parabolic operator L
noncomputable def parabilinform
    (P : ParabolicCoeffs d) (u v : H1U0 d U hU) : ℝ :=
  ∫ x,
      (∑ i : Fin d, ∑ j : Fin d, P.a i j x * partialU i u x * partialU j v x)
    + (∑ i : Fin d, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x)
    + P.c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x
    ∂(μU d U)


--proof structure that it is a Bilinear form

variable (P : ParabolicCoeffs d)

-- Bilinearity of `parabilinform`: see after the B-foundation lemmas (needs `coeff_integrable`).

--Bilinear form bound: see `parabilinform_bound` after the B-foundation lemmas (needs A2/BB1).



-- Evans Def 5 §7.1.1.b: weak solution to `∂_t u + L(t) u = f`, `u(0) = g`, homogeneous Dirichlet
-- on `∂U`.  The Gelfand-triple pair is `u ∈ L²(0,T;H¹₀)`, `u' ∈ L²(0,T;H⁻¹)`.  The relation that
-- `u'` is the weak time derivative of `u` (§5.9.2 Bochner-IBP identification) is now PART of
-- `IsWeakSolution` (the `IsWeakTimeDeriv` conjunct), discharged at the Galerkin limit by
-- `isWeakTimeDeriv_of_weak_limits`.  Only the initial condition `u(0) = g` (needing the
-- `u ∈ C([0,T];L²)` regularity) remains omitted; `g` is retained as its placeholder.

/-- Admissible time test function: `C¹`, compactly supported inside the open interval `(0,T)`. -/
def IsTimeTestFn (T : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Set.Ioo 0 T

/-- `w` is the **weak time derivative** of `u` in the Gelfand triple `H¹₀ ⊂ L² ⊂ H⁻¹`: for every
`H¹₀` test vector `v` and every admissible time bump `φ`, integration by parts holds,
`∫₀ᵀ φ'(t)·⟨u(t),v⟩ dt = −∫₀ᵀ φ(t)·⟨w(t),v⟩ dt`. -/
def IsWeakTimeDeriv (T : ℝ)
    (u : L2TH10U d U hU T) (w : L2TH10U_dual d U hU T) : Prop :=
  ∀ (v : H1U0 d U hU) (φ : ℝ → ℝ), IsTimeTestFn T φ →
    (∫ t in Set.Icc (0:ℝ) T, deriv φ t * ((H1U0_inclusion_Hinv (u t)) v))
      = - ∫ t in Set.Icc (0:ℝ) T, φ t * ((w t) v)

/-- **Weak solution (Evans §7.1.2).**  A pair `(u, u')` where `u'` is the weak time derivative of
`u` (Gelfand-triple sense) *and* the weak formulation `⟨u'(t),v⟩ + B(t)[u,v] = ⟨f(t),v⟩` holds
a.e. `t` for every test vector `v`. -/
noncomputable def IsWeakSolution
    (P : ℝ → ParabolicCoeffs d) (T : ℝ)
    (f : L2TL2 d U T) (_g : Lp ℝ 2 (μU d U))
    (u : L2TH10U d U hU T) (u' : L2TH10U_dual d U hU T) : Prop :=
  IsWeakTimeDeriv T u u' ∧
  ∀ (v : H1U0 d U hU),
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
      (u' t) v + parabilinform (P t) (u t) v
        = inner ℝ (f t) (WkpU.toLp v.val)




-- A basis suitable for Evans's Galerkin approximations L^2 orthonormal and H^1 orthogonal
structure GalerkinBasis (d : ℕ+) (U : Set (Fin d → ℝ)) (hU : IsOpen U) where

  w : ℕ → H1U0 d U hU
  orthonormal_L2 :
    Orthonormal ℝ (fun k : ℕ => WkpU.toLp (w k).val)
  orthogonal_H1 :
    ∀ {k j : ℕ}, k ≠ j → inner ℝ (w k) (w j) = (0 : ℝ)
  dense_L2 :
    (Submodule.span ℝ
      (Set.range (fun k : ℕ => WkpU.toLp (w k).val))).topologicalClosure = ⊤
  dense_H1 :
    (Submodule.span ℝ (Set.range w)).topologicalClosure = ⊤
  -- The L²-orthogonal projection onto span{w₀,…,w_{m-1}} is non-expansive in the H¹ norm.
  -- (Holds for the eigenfunction basis Evans uses; not derivable from the two orthogonalities
  -- alone, so it is recorded as a defining property of the Galerkin basis.)
  projL2_H1_le :
    ∀ (m : ℕ) (v : H1U0 d U hU),
      ‖∑ k : Fin m,
          (inner ℝ (WkpU.toLp v.val) (WkpU.toLp (w (k : ℕ)).val) : ℝ) • w (k : ℕ)‖ ≤ ‖v‖


--Proof that such a basis exists
theorem exists_galerkinBasis
    (d : ℕ+) (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    Nonempty (GalerkinBasis d U hU) := by
  sorry



def GalerkinODE
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U))
    {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ) : Prop :=
  (∀ k : Fin m,
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
        deriv (dCoeffs k) t
          + ∑ j : Fin m, dCoeffs j t * parabilinform (P t) (G.w j.val) (G.w k.val)
        = inner ℝ (f t) (WkpU.toLp (G.w k.val).val))
  ∧ (∀ k : Fin m, dCoeffs k 0 = inner ℝ g (WkpU.toLp (G.w k.val).val))


--finite subspace approximants by hilbert space decompisition
noncomputable def uapprox
    (G : GalerkinBasis d U hU) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ) :
    ℝ → H1U0 d U hU :=
  fun t => ∑ k : Fin m, dCoeffs k t • G.w k.val

noncomputable def u'approx
    (G : GalerkinBasis d U hU) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ) :
    ℝ → H1U0 d U hU :=
  fun t => ∑ k : Fin m, deriv (dCoeffs k) t • G.w k.val

--theorem 1
-- The Galerkin system is the linear ODE  d'(t) = F(t) - A(t)·d(t),  where
--   A(t)_{kj} = parabilinform (P t) (G.w j) (G.w k)   and   F(t)_k = ⟨f t, toLp (G.w k)⟩.
-- Mathlib only has classical Picard–Lindelöf (`IsPicardLindelof`, which needs the vector field
-- CONTINUOUS in t), not Carathéodory existence (measurable-in-t, the honest L∞/L² regime).
-- DUCT TAPE: we assume the coefficient-matrix entries A(t) and the forcing F(t) are continuous
-- in t on [0,T] (`hAcont`, `hFcont`).  Then v t d = F(t) - A(t)·d is continuous in t and affine
-- (hence Lipschitz) in d, so `IsPicardLindelof` holds and classical PL applies (locally; the
-- linear structure extends it to all of [0,T] by continuation).
theorem galerkin_ode_solvable
    {θ M : ℝ} (hθ : 0 < θ)
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ)
    (hP_bdd : ∀ t, (P t).IsBounded M)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U)) (m : ℕ)
    (hFcont : ∀ k : Fin m,
        ContinuousOn (fun t => inner ℝ (f t) (WkpU.toLp (G.w k.val).val)) (Set.Icc 0 T))
    (hAcont : ∀ j k : Fin m,
        ContinuousOn (fun t => parabilinform (P t) (G.w j.val) (G.w k.val)) (Set.Icc 0 T)) :
    ∃! dCoeffs : Fin m → ℝ → ℝ, GalerkinODE G P T f g dCoeffs := by
  sorry


-- u'_m(t) = ∑ d_k'(t) w_k, the pointwise time derivative of the Galerkin approx




/-- Cauchy/Young's inequality-/
lemma cauchy_eps {a b ε : ℝ} (hε : 0 < ε) : a * b ≤ ε * a ^ 2 + b ^ 2 / (4 * ε) := by
  have h4ε : (0:ℝ) < 4 * ε := by linarith
  rw [← sub_nonneg]
  have hid : ε * a ^ 2 + b ^ 2 / (4 * ε) - a * b = (2 * ε * a - b) ^ 2 / (4 * ε) := by
    field_simp
    ring
  rw [hid]
  exact div_nonneg (sq_nonneg _) h4ε.le

/-- To LP -/
lemma norm_toLp_sq {d : ℕ+} {U : Set (Fin d → ℝ)} (φ : (Fin d → ℝ) → ℝ)
    (hφ : MemLp φ 2 (μU d U)) :
    ‖hφ.toLp φ‖ ^ 2 = ∫ x, φ x * φ x ∂(μU d U) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hφ.coeFn_toLp] with x hx
  simp only [Real.inner_apply, hx]

/-- Here to split norm, can remove when wkp.tolp is fixed -/
lemma H1_norm_sq_split {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U} (u : H1U0 d U hU) :
    ‖u‖ ^ 2 = ‖WkpU.toLp u.val‖ ^ 2
      + ∑ s : Fin 1 → Fin d, ‖WkpU.derivtoLp u.val (1 : ℕ+) (le_refl 1) s‖ ^ 2 := by
  have hnorm : ‖u‖ ^ 2 = HkU.innerFormula u.val u.val := by
    have h := HkU.innerFormula_norm_sq u.val
    rwa [RCLike.re_to_real] at h
  rw [hnorm]
  simp only [HkU.innerFormula, Fin.sum_univ_one]
  congr 1
  · exact (norm_toLp_sq _ (WkpU.memLp u.val)).symm
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    exact (norm_toLp_sq _ (WkpU.weakDeriv_memLp u.val (1 : ℕ+) (le_refl 1) s)).symm


-- `WkpU.toLp_smul` / `toLp_add` / `toLpₗ` / `toLp_sum` (and the new CLM packaging
-- `WkpU.toLpCLM`) now live in `V3_sobolev` next to `WkpU.toLp` itself.

/--Tolp only applies on basis vectors-/
lemma galerkin_combo_toLp {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (G : GalerkinBasis d U hU) {m : ℕ} (a : Fin m → ℝ) :
    WkpU.toLp (∑ k : Fin m, a k • G.w (k : ℕ)).val
      = ∑ k : Fin m, a k • WkpU.toLp (G.w (k : ℕ)).val := by
  have hval : (∑ k : Fin m, a k • G.w (k : ℕ)).val = ∑ k : Fin m, a k • (G.w (k : ℕ)).val := by
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [hval, WkpU.toLp_sum]

/-- Parsevals for galerkin basis -/
lemma galerkin_combo_normSq {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (G : GalerkinBasis d U hU) {m : ℕ} (a : Fin m → ℝ) :
    ‖WkpU.toLp (∑ k : Fin m, a k • G.w (k : ℕ)).val‖ ^ 2 = ∑ k : Fin m, a k ^ 2 := by
  have hon : Orthonormal ℝ (fun k : Fin m => WkpU.toLp (G.w (k : ℕ)).val) :=
    G.orthonormal_L2.comp _ Fin.val_injective
  rw [galerkin_combo_toLp, ← real_inner_self_eq_norm_sq, hon.inner_sum a a Finset.univ]
  simp only [RCLike.conj_to_real, pow_two]

/-- Orthonormal pairing of basis vectors -/
lemma galerkin_combo_inner {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (G : GalerkinBasis d U hU) {m : ℕ} (a : Fin m → ℝ) (j : Fin m) :
    inner ℝ (WkpU.toLp (∑ k : Fin m, a k • G.w (k : ℕ)).val) (WkpU.toLp (G.w (j : ℕ)).val)
      = a j := by
  have hon : Orthonormal ℝ (fun k : Fin m => WkpU.toLp (G.w (k : ℕ)).val) :=
    G.orthonormal_L2.comp _ Fin.val_injective
  rw [galerkin_combo_toLp, hon.inner_left_fintype a j]
  simp only [RCLike.conj_to_real]

/-- u_approxl2norm -/
lemma uapprox_L2_normSq {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (G : GalerkinBasis d U hU) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ) (t : ℝ) :
    ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2 = ∑ k : Fin m, dCoeffs k t ^ 2 :=
  galerkin_combo_normSq G (fun k => dCoeffs k t)

/-- u_approx inner prod with basis vecs -/
lemma uapprox_inner_basis {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (G : GalerkinBasis d U hU) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ) (t : ℝ) (j : Fin m) :
    inner ℝ (WkpU.toLp (uapprox G dCoeffs t).val) (WkpU.toLp (G.w (j : ℕ)).val) = dCoeffs j t :=
  galerkin_combo_inner G (fun k => dCoeffs k t) j

/-- u'approxwithbasisvecs-/
lemma u'approx_inner_basis {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (G : GalerkinBasis d U hU) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ) (t : ℝ) (j : Fin m) :
    inner ℝ (WkpU.toLp (u'approx G dCoeffs t).val) (WkpU.toLp (G.w (j : ℕ)).val)
      = deriv (dCoeffs j) t :=
  galerkin_combo_inner G (fun k => deriv (dCoeffs k) t) j

/-- differentiation of Galerkin basis in l2norm -/
lemma uapprox_L2_normSq_hasDerivAt {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (G : GalerkinBasis d U hU) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ) (t : ℝ)
    (hd : ∀ k, HasDerivAt (dCoeffs k) (deriv (dCoeffs k) t) t) :
    HasDerivAt (fun t => ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2)
      (2 * ∑ k : Fin m, deriv (dCoeffs k) t * dCoeffs k t) t := by
  have hfun : (fun t => ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2)
      = fun t => ∑ k : Fin m, dCoeffs k t ^ 2 := by
    funext s; exact uapprox_L2_normSq G dCoeffs s
  have hpow : ∀ k, HasDerivAt (fun t => dCoeffs k t ^ 2)
      (2 * dCoeffs k t * deriv (dCoeffs k) t) t :=
    fun k => ((hd k).pow 2).congr_deriv (by norm_num)
  rw [hfun, show (2 * ∑ k : Fin m, deriv (dCoeffs k) t * dCoeffs k t)
        = ∑ k : Fin m, 2 * dCoeffs k t * deriv (dCoeffs k) t from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring]
  have h := HasDerivAt.sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) => hpow k)
  have hfn : (∑ k ∈ (Finset.univ : Finset (Fin m)), fun t => dCoeffs k t ^ 2)
      = fun t => ∑ k : Fin m, dCoeffs k t ^ 2 := by
    funext s; simp only [Finset.sum_apply]
  rw [hfn] at h
  exact h

/--partial derivative of u in L2 norm bound by u in h1 norm -/
lemma partialU_derivtoLp_le {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (u : H1U0 d U hU) (i : Fin d) :
    ‖WkpU.derivtoLp u.val (1 : ℕ+) (le_refl 1) (fun _ => i)‖ ≤ ‖u‖ := by
  have hsq : ‖WkpU.derivtoLp u.val (1 : ℕ+) (le_refl 1) (fun _ => i)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [H1_norm_sq_split u]
    have hmem : ‖WkpU.derivtoLp u.val (1 : ℕ+) (le_refl 1) (fun _ => i)‖ ^ 2
        ≤ ∑ s : Fin 1 → Fin d, ‖WkpU.derivtoLp u.val (1 : ℕ+) (le_refl 1) s‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun s : Fin 1 → Fin d => ‖WkpU.derivtoLp u.val (1 : ℕ+) (le_refl 1) s‖ ^ 2)
        (fun s _ => sq_nonneg _) (Finset.mem_univ (fun _ : Fin 1 => i))
    nlinarith [sq_nonneg ‖WkpU.toLp u.val‖, hmem]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-- L2 CS, mathlib version does not work well -/
lemma integral_mul_le_L2 {d : ℕ+} {U : Set (Fin d → ℝ)} (f g : (Fin d → ℝ) → ℝ)
    (hf : MemLp f 2 (μU d U)) (hg : MemLp g 2 (μU d U)) :
    |∫ x, f x * g x ∂(μU d U)| ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have heq : ∫ x, f x * g x ∂(μU d U) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    rw [Real.inner_apply, hfx, hgx]
  rw [heq]
  exact abs_real_inner_le_norm _ _

/-- a,b,c parabolic coefficients bound in bilinear form -/
lemma coeff_integral_bound {d : ℕ+} {U : Set (Fin d → ℝ)}
    (a : (Fin d → ℝ) → ℝ) (ha : Measurable a) {M : ℝ} (hM : ∀ x, |a x| ≤ M)
    (f g : (Fin d → ℝ) → ℝ) (hf : MemLp f 2 (μU d U)) (hg : MemLp g 2 (μU d U)) :
    |∫ x, a x * f x * g x ∂(μU d U)| ≤ M * (‖hf.toLp f‖ * ‖hg.toLp g‖) := by
  have hfg : Integrable (fun x => f x * g x) (μU d U) := hf.integrable_mul hg
  have hafg : Integrable (fun x => a x * f x * g x) (μU d U) := by
    have h := Integrable.bdd_mul hfg ha.aestronglyMeasurable
      (Eventually.of_forall fun x => (Real.norm_eq_abs (a x)).le.trans (hM x))
    simpa [mul_assoc] using h
  have habs : Integrable (fun x => |f x| * |g x|) (μU d U) := by
    simpa [abs_mul] using hfg.abs
  have step1 : |∫ x, a x * f x * g x ∂(μU d U)| ≤ ∫ x, M * (|f x| * |g x|) ∂(μU d U) := by
    refine abs_integral_le_integral_abs.trans (integral_mono hafg.abs (habs.const_mul M) ?_)
    intro x
    show |a x * f x * g x| ≤ M * (|f x| * |g x|)
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hM x) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [integral_const_mul] at step1
  have hf' : MemLp (fun x => |f x|) 2 (μU d U) := by simpa [Real.norm_eq_abs] using hf.norm
  have hg' : MemLp (fun x => |g x|) 2 (μU d U) := by simpa [Real.norm_eq_abs] using hg.norm
  have hcs : ∫ x, |f x| * |g x| ∂(μU d U) ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
    have hpos : 0 ≤ ∫ x, |f x| * |g x| ∂(μU d U) :=
      integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hcs0 := integral_mul_le_L2 (fun x => |f x|) (fun x => |g x|) hf' hg'
    rw [abs_of_nonneg hpos] at hcs0
    have e1 : ‖hf'.toLp (fun x => |f x|)‖ = ‖hf.toLp f‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (hf'.toLp _)), ← Real.sqrt_sq (norm_nonneg (hf.toLp f)),
          norm_toLp_sq, norm_toLp_sq]
      simp only [abs_mul_abs_self]
    have e2 : ‖hg'.toLp (fun x => |g x|)‖ = ‖hg.toLp g‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (hg'.toLp _)), ← Real.sqrt_sq (norm_nonneg (hg.toLp g)),
          norm_toLp_sq, norm_toLp_sq]
      simp only [abs_mul_abs_self]
    rwa [e1, e2] at hcs0
  calc |∫ x, a x * f x * g x ∂(μU d U)|
      ≤ M * ∫ x, |f x| * |g x| ∂(μU d U) := step1
    _ ≤ M * (‖hf.toLp f‖ * ‖hg.toLp g‖) := by
        have hMnn : 0 ≤ M := (abs_nonneg (a 0)).trans (hM 0)
        gcongr

/-- Integrability of a single bilinear-form term `a·f·g` (bounded measurable `a`, `f g ∈ L²`). -/
lemma coeff_integrable {d : ℕ+} {U : Set (Fin d → ℝ)}
    (a : (Fin d → ℝ) → ℝ) (ha : Measurable a) {M : ℝ} (hM : ∀ x, |a x| ≤ M)
    (f g : (Fin d → ℝ) → ℝ) (hf : MemLp f 2 (μU d U)) (hg : MemLp g 2 (μU d U)) :
    Integrable (fun x => a x * f x * g x) (μU d U) := by
  have h := Integrable.bdd_mul (hf.integrable_mul hg) ha.aestronglyMeasurable
    (Eventually.of_forall fun x => (Real.norm_eq_abs (a x)).le.trans (hM x))
  simpa [mul_assoc] using h

/-- **(B1) Bilinear-form boundedness** `b(u,v) < M(d^2+d+1)*uv norms .-/
lemma parabilinform_bound (M : ℝ) (hM : P.IsBounded M) (u v : H1U0 d U hU) :
    |parabilinform P u v| ≤ M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖u‖ * ‖v‖ := by
  obtain ⟨hMa, hMb, hMc⟩ := hM
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hMc 0)
  -- MemLp of the building functions
  have hpu : ∀ i, MemLp (partialU i u) 2 (μU d U) := fun i =>
    WkpU.weakDeriv_memLp u.val 1 (le_refl 1) (fun _ => i)
  have hpv : ∀ j, MemLp (partialU j v) 2 (μU d U) := fun j =>
    WkpU.weakDeriv_memLp v.val 1 (le_refl 1) (fun _ => j)
  have huf : MemLp (fun x => (u : (Fin d → ℝ) → ℝ) x) 2 (μU d U) := WkpU.memLp u.val
  have hvf : MemLp (fun x => (v : (Fin d → ℝ) → ℝ) x) 2 (μU d U) := WkpU.memLp v.val
  -- per-term bounds, all ≤ M‖u‖‖v‖
  have key_a : ∀ i j, |∫ x, P.a i j x * partialU i u x * partialU j v x ∂(μU d U)|
      ≤ M * ‖u‖ * ‖v‖ := by
    intro i j
    refine (coeff_integral_bound (P.a i j) (P.aMeasurable i j) (hMa i j)
      (partialU i u) (partialU j v) (hpu i) (hpv j)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (partialU_derivtoLp_le u i) (partialU_derivtoLp_le v j)
        (norm_nonneg _) (norm_nonneg _)) hMnn
  have key_b : ∀ i, |∫ x, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x ∂(μU d U)|
      ≤ M * ‖u‖ * ‖v‖ := by
    intro i
    refine (coeff_integral_bound (P.b i) (P.bMeasurable i) (hMb i)
      (partialU i u) (fun x => (v : (Fin d → ℝ) → ℝ) x) (hpu i) hvf).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (partialU_derivtoLp_le u i) (H1U0.l2_norm_le_norm v)
        (norm_nonneg _) (norm_nonneg _)) hMnn
  have key_c : |∫ x, P.c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x ∂(μU d U)|
      ≤ M * ‖u‖ * ‖v‖ := by
    refine (coeff_integral_bound P.c P.cMeasurable hMc
      (fun x => (u : (Fin d → ℝ) → ℝ) x) (fun x => (v : (Fin d → ℝ) → ℝ) x) huf hvf).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (H1U0.l2_norm_le_norm u) (H1U0.l2_norm_le_norm v)
        (norm_nonneg _) (norm_nonneg _)) hMnn
  -- integrability for the integral splits
  have hIa : ∀ i j, Integrable
      (fun x => P.a i j x * partialU i u x * partialU j v x) (μU d U) :=
    fun i j => coeff_integrable (P.a i j) (P.aMeasurable i j) (hMa i j) _ _ (hpu i) (hpv j)
  have hIaj : ∀ i, Integrable
      (fun x => ∑ j, P.a i j x * partialU i u x * partialU j v x) (μU d U) :=
    fun i => integrable_finsetSum _ (fun j _ => hIa i j)
  have hIA : Integrable
      (fun x => ∑ i, ∑ j, P.a i j x * partialU i u x * partialU j v x) (μU d U) :=
    integrable_finsetSum _ (fun i _ => hIaj i)
  have hIb : ∀ i, Integrable
      (fun x => P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x) (μU d U) :=
    fun i => coeff_integrable (P.b i) (P.bMeasurable i) (hMb i) _ _ (hpu i) hvf
  have hIB : Integrable
      (fun x => ∑ i, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x) (μU d U) :=
    integrable_finsetSum _ (fun i _ => hIb i)
  have hIC : Integrable
      (fun x => P.c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x) (μU d U) :=
    coeff_integrable P.c P.cMeasurable hMc _ _ huf hvf
  -- single-lambda integrability for the `A+B` group (so `integral_add` β-matches the goal)
  have hIAB : Integrable
      (fun x => (∑ i, ∑ j, P.a i j x * partialU i u x * partialU j v x)
        + (∑ i, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x)) (μU d U) := hIA.add hIB
  -- split the integral into the three groups
  have heq : parabilinform P u v
      = (∑ i, ∑ j, ∫ x, P.a i j x * partialU i u x * partialU j v x ∂(μU d U))
        + (∑ i, ∫ x, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x ∂(μU d U))
        + (∫ x, P.c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x ∂(μU d U)) := by
    unfold parabilinform
    rw [integral_add hIAB hIC, integral_add hIA hIB,
        integral_finsetSum Finset.univ (fun i _ => hIaj i),
        integral_finsetSum Finset.univ (fun i _ => hIb i),
        Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
          integral_finsetSum Finset.univ (fun j _ => hIa i j))]
  rw [heq]
  -- bound each group
  have bound_a :
      |∑ i, ∑ j, ∫ x, P.a i j x * partialU i u x * partialU j v x ∂(μU d U)|
        ≤ (d : ℝ) ^ 2 * (M * ‖u‖ * ‖v‖) := by
    have heval : (∑ _i : Fin d, ∑ _j : Fin d, M * ‖u‖ * ‖v‖)
        = (d : ℝ) ^ 2 * (M * ‖u‖ * ‖v‖) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    calc |∑ i, ∑ j, ∫ x, P.a i j x * partialU i u x * partialU j v x ∂(μU d U)|
        ≤ ∑ i, |∑ j, ∫ x, P.a i j x * partialU i u x * partialU j v x ∂(μU d U)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |∫ x, P.a i j x * partialU i u x * partialU j v x ∂(μU d U)| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, M * ‖u‖ * ‖v‖ :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => key_a i j))
      _ = (d : ℝ) ^ 2 * (M * ‖u‖ * ‖v‖) := heval
  have bound_b :
      |∑ i, ∫ x, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x ∂(μU d U)|
        ≤ (d : ℝ) * (M * ‖u‖ * ‖v‖) := by
    have heval : (∑ _i : Fin d, M * ‖u‖ * ‖v‖) = (d : ℝ) * (M * ‖u‖ * ‖v‖) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc |∑ i, ∫ x, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x ∂(μU d U)|
        ≤ ∑ i, |∫ x, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x ∂(μU d U)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, M * ‖u‖ * ‖v‖ := Finset.sum_le_sum (fun i _ => key_b i)
      _ = (d : ℝ) * (M * ‖u‖ * ‖v‖) := heval
  calc |(∑ i, ∑ j, ∫ x, P.a i j x * partialU i u x * partialU j v x ∂(μU d U))
          + (∑ i, ∫ x, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x ∂(μU d U))
          + (∫ x, P.c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x ∂(μU d U))|
      ≤ |∑ i, ∑ j, ∫ x, P.a i j x * partialU i u x * partialU j v x ∂(μU d U)|
        + |∑ i, ∫ x, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x ∂(μU d U)|
        + |∫ x, P.c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x ∂(μU d U)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (d : ℝ) ^ 2 * (M * ‖u‖ * ‖v‖) + (d : ℝ) * (M * ‖u‖ * ‖v‖) + M * ‖u‖ * ‖v‖ :=
        add_le_add (add_le_add bound_a bound_b) key_c
    _ = M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖u‖ * ‖v‖ := by ring

/-- Reindex a sum over `Fin 1 → Fin d` (the A2 derivative index) as a sum over `Fin d`. -/
lemma sum_funUnique_fin {d : ℕ+} {M : Type*} [AddCommMonoid M] (F : (Fin 1 → Fin d) → M) :
    ∑ s : Fin 1 → Fin d, F s = ∑ i : Fin d, F (fun _ => i) := by
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin d))
  intro s
  congr 1
  funext k
  exact congrArg s (Subsingleton.elim k _)

/-- parabolic condition applied to ej,ei = diu,dju -/
lemma parabilinform_principal_lower {θ M : ℝ}
    (hP_para : P.IsUniformlyParabolic U θ) (hMa : ∀ i j, ∀ x, |P.a i j x| ≤ M)
    (u : H1U0 d U hU) :
    θ * (∑ i : Fin d, ∫ x, partialU i u x * partialU i u x ∂(μU d U))
      ≤ ∫ x, (∑ i, ∑ j, P.a i j x * partialU i u x * partialU j u x) ∂(μU d U) := by
  have hpu : ∀ i, MemLp (partialU i u) 2 (μU d U) := fun i =>
    WkpU.weakDeriv_memLp u.val 1 (le_refl 1) (fun _ => i)
  have hIsq : ∀ i, Integrable (fun x => partialU i u x * partialU i u x) (μU d U) :=
    fun i => (hpu i).integrable_mul (hpu i)
  have hIa : ∀ i j, Integrable
      (fun x => P.a i j x * partialU i u x * partialU j u x) (μU d U) :=
    fun i j => coeff_integrable (P.a i j) (P.aMeasurable i j) (hMa i j) _ _ (hpu i) (hpu j)
  have hIA : Integrable
      (fun x => ∑ i, ∑ j, P.a i j x * partialU i u x * partialU j u x) (μU d U) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hIa i j))
  have hIsum : Integrable (fun x => ∑ i, partialU i u x * partialU i u x) (μU d U) :=
    integrable_finsetSum _ (fun i _ => hIsq i)
  rw [← integral_finsetSum Finset.univ (fun i _ => hIsq i), ← integral_const_mul]
  refine integral_mono_ae (hIsum.const_mul θ) hIA ?_
  filter_upwards [hP_para.2] with x hx
  have h := hx (fun i => partialU i u x)
  simpa only [pow_two] using h

/-- Gårding coercivity -/
lemma parabilinform_garding {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (hP_para : P.IsUniformlyParabolic U θ) (hP_bdd : P.IsBounded M) (u : H1U0 d U hU) :
    (θ / 2) * ‖u‖ ^ 2 - (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ)) * ‖WkpU.toLp u.val‖ ^ 2
      ≤ parabilinform P u u := by
  obtain ⟨hMa, hMb, hMc⟩ := hP_bdd
  have hM0 : M ≠ 0 := hMpos.ne'
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hpu : ∀ i, MemLp (partialU i u) 2 (μU d U) := fun i =>
    WkpU.weakDeriv_memLp u.val 1 (le_refl 1) (fun _ => i)
  have huf : MemLp (fun x => (u : (Fin d → ℝ) → ℝ) x) 2 (μU d U) := WkpU.memLp u.val
  have hLb : ‖huf.toLp (fun x => (u : (Fin d → ℝ) → ℝ) x)‖ = ‖WkpU.toLp u.val‖ := rfl
  -- integrability of each group
  have hIa : ∀ i j, Integrable
      (fun x => P.a i j x * partialU i u x * partialU j u x) (μU d U) :=
    fun i j => coeff_integrable (P.a i j) (P.aMeasurable i j) (hMa i j) _ _ (hpu i) (hpu j)
  have hIA : Integrable
      (fun x => ∑ i, ∑ j, P.a i j x * partialU i u x * partialU j u x) (μU d U) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hIa i j))
  have hIb_term : ∀ i, Integrable
      (fun x => P.b i x * partialU i u x * (u : (Fin d → ℝ) → ℝ) x) (μU d U) :=
    fun i => coeff_integrable (P.b i) (P.bMeasurable i) (hMb i) _ _ (hpu i) huf
  have hIB : Integrable
      (fun x => ∑ i, P.b i x * partialU i u x * (u : (Fin d → ℝ) → ℝ) x) (μU d U) :=
    integrable_finsetSum _ (fun i _ => hIb_term i)
  have hIC : Integrable
      (fun x => P.c x * (u : (Fin d → ℝ) → ℝ) x * (u : (Fin d → ℝ) → ℝ) x) (μU d U) :=
    coeff_integrable P.c P.cMeasurable hMc _ _ huf huf
  have hIAB : Integrable
      (fun x => (∑ i, ∑ j, P.a i j x * partialU i u x * partialU j u x)
        + (∑ i, P.b i x * partialU i u x * (u : (Fin d → ℝ) → ℝ) x)) (μU d U) := hIA.add hIB
  -- the three groups
  have hsplit : parabilinform P u u
      = (∫ x, (∑ i, ∑ j, P.a i j x * partialU i u x * partialU j u x) ∂(μU d U))
        + (∫ x, (∑ i, P.b i x * partialU i u x * (u : (Fin d → ℝ) → ℝ) x) ∂(μU d U))
        + (∫ x, P.c x * (u : (Fin d → ℝ) → ℝ) x * (u : (Fin d → ℝ) → ℝ) x ∂(μU d U)) := by
    unfold parabilinform
    rw [integral_add hIAB hIC, integral_add hIA hIB]
  -- principal lower bound (G1), restated with L² norms
  have hIa_lb : θ * (∑ i : Fin d, ‖(hpu i).toLp (partialU i u)‖ ^ 2)
      ≤ ∫ x, (∑ i, ∑ j, P.a i j x * partialU i u x * partialU j u x) ∂(μU d U) := by
    have hg := parabilinform_principal_lower (P := P) hP_para hMa u
    rwa [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      (norm_toLp_sq (partialU i u) (hpu i)).symm)] at hg
  -- b-term: |I_b| ≤ (θ/2) S + (M²d/2θ) L
  have hIb_ub : |∫ x, (∑ i, P.b i x * partialU i u x * (u : (Fin d → ℝ) → ℝ) x) ∂(μU d U)|
      ≤ (θ / 2) * (∑ i : Fin d, ‖(hpu i).toLp (partialU i u)‖ ^ 2)
        + M ^ 2 * (d : ℝ) / (2 * θ) * ‖WkpU.toLp u.val‖ ^ 2 := by
    have hε : (0:ℝ) < θ / (2 * M) := div_pos hθ (by positivity)
    have hstep : ∀ i : Fin d,
        |∫ x, P.b i x * partialU i u x * (u : (Fin d → ℝ) → ℝ) x ∂(μU d U)|
        ≤ M * ((θ / (2 * M)) * ‖(hpu i).toLp (partialU i u)‖ ^ 2
            + ‖WkpU.toLp u.val‖ ^ 2 / (4 * (θ / (2 * M)))) := by
      intro i
      refine (coeff_integral_bound (P.b i) (P.bMeasurable i) (hMb i)
        (partialU i u) (fun x => (u : (Fin d → ℝ) → ℝ) x) (hpu i) huf).trans ?_
      rw [hLb]
      exact mul_le_mul_of_nonneg_left (cauchy_eps hε) hMpos.le
    have hterm : ∀ i : Fin d, M * ((θ / (2 * M)) * ‖(hpu i).toLp (partialU i u)‖ ^ 2
          + ‖WkpU.toLp u.val‖ ^ 2 / (4 * (θ / (2 * M))))
        = (θ / 2) * ‖(hpu i).toLp (partialU i u)‖ ^ 2
          + M ^ 2 / (2 * θ) * ‖WkpU.toLp u.val‖ ^ 2 := by
      intro i; field_simp; ring
    rw [integral_finsetSum Finset.univ (fun i _ => hIb_term i)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun i _ => hstep i)).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- c-term: |I_c| ≤ M L
  have hIc_ub : |∫ x, P.c x * (u : (Fin d → ℝ) → ℝ) x * (u : (Fin d → ℝ) → ℝ) x ∂(μU d U)|
      ≤ M * ‖WkpU.toLp u.val‖ ^ 2 := by
    have h := coeff_integral_bound P.c P.cMeasurable hMc
      (fun x => (u : (Fin d → ℝ) → ℝ) x) (fun x => (u : (Fin d → ℝ) → ℝ) x) huf huf
    simp only [hLb] at h
    rwa [← pow_two] at h
  -- A2 with the partials reindexed over `Fin d`
  have hA2 : ‖u‖ ^ 2
      = ‖WkpU.toLp u.val‖ ^ 2 + ∑ i : Fin d, ‖(hpu i).toLp (partialU i u)‖ ^ 2 := by
    rw [H1_norm_sq_split u,
        sum_funUnique_fin (fun s => ‖WkpU.derivtoLp u.val 1 (le_refl 1) s‖ ^ 2)]
    exact congrArg (‖WkpU.toLp u.val‖ ^ 2 + ·) (Finset.sum_congr rfl (fun i _ => rfl))
  -- combine
  rw [hsplit]
  have hval : (θ / 2) * ‖u‖ ^ 2
        - (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ)) * ‖WkpU.toLp u.val‖ ^ 2
      = θ * (∑ i : Fin d, ‖(hpu i).toLp (partialU i u)‖ ^ 2)
        - ((θ / 2) * (∑ i : Fin d, ‖(hpu i).toLp (partialU i u)‖ ^ 2)
            + M ^ 2 * (d : ℝ) / (2 * θ) * ‖WkpU.toLp u.val‖ ^ 2)
        - M * ‖WkpU.toLp u.val‖ ^ 2 := by
    rw [hA2]; ring
  rw [hval]
  have hb := neg_abs_le (∫ x, (∑ i, P.b i x * partialU i u x * (u : (Fin d → ℝ) → ℝ) x) ∂(μU d U))
  have hc := neg_abs_le (∫ x, P.c x * (u : (Fin d → ℝ) → ℝ) x * (u : (Fin d → ℝ) → ℝ) x ∂(μU d U))
  linarith [hIa_lb, hIb_ub, hIc_ub, hb, hc]

/-- The full bilinear-form integrand is integrable  -/
lemma parabilinform_integrand_integrable {M : ℝ} (hP_bdd : P.IsBounded M) (u v : H1U0 d U hU) :
    Integrable (fun x => (∑ i, ∑ j, P.a i j x * partialU i u x * partialU j v x)
      + (∑ i, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x)
      + P.c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x) (μU d U) := by
  obtain ⟨hMa, hMb, hMc⟩ := hP_bdd
  have hA : Integrable
      (fun x => ∑ i, ∑ j, P.a i j x * partialU i u x * partialU j v x) (μU d U) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      coeff_integrable (P.a i j) (P.aMeasurable i j) (hMa i j) _ _
        (WkpU.weakDeriv_memLp u.val 1 (le_refl 1) (fun _ => i))
        (WkpU.weakDeriv_memLp v.val 1 (le_refl 1) (fun _ => j))))
  have hB : Integrable
      (fun x => ∑ i, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x) (μU d U) :=
    integrable_finsetSum _ (fun i _ => coeff_integrable (P.b i) (P.bMeasurable i) (hMb i) _ _
      (WkpU.weakDeriv_memLp u.val 1 (le_refl 1) (fun _ => i)) (WkpU.memLp v.val))
  have hC : Integrable
      (fun x => P.c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x) (μU d U) :=
    coeff_integrable P.c P.cMeasurable hMc _ _ (WkpU.memLp u.val) (WkpU.memLp v.val)
  exact (hA.add hB).add hC
/--Bilinear form is bilinear-/
lemma parabilinform_add_left {M : ℝ} (hP_bdd : P.IsBounded M) (u₁ u₂ v : H1U0 d U hU) :
    parabilinform P (u₁ + u₂) v = parabilinform P u₁ v + parabilinform P u₂ v := by
  have partialU_add : ∀ i, (fun x => partialU i (u₁ + u₂) x)
      =ᵐ[μU d U] fun x => partialU i u₁ x + partialU i u₂ x :=
    fun i => WkpU.weakDeriv_add u₁.val u₂.val 1 (le_refl 1) (fun _ => i)
  have hcoeFn_add : (fun x => ((u₁ + u₂ : H1U0 d U hU) : (Fin d → ℝ) → ℝ) x)
      =ᵐ[μU d U] fun x => (u₁ : (Fin d → ℝ) → ℝ) x + (u₂ : (Fin d → ℝ) → ℝ) x :=
    HkU.coeFn_add u₁.val u₂.val
  have hae : (fun x => (∑ i, ∑ j, P.a i j x * partialU i (u₁ + u₂) x * partialU j v x)
        + (∑ i, P.b i x * partialU i (u₁ + u₂) x * (v : (Fin d → ℝ) → ℝ) x)
        + P.c x * ((u₁ + u₂ : H1U0 d U hU) : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x)
      =ᵐ[μU d U] fun x =>
        ((∑ i, ∑ j, P.a i j x * partialU i u₁ x * partialU j v x)
          + (∑ i, P.b i x * partialU i u₁ x * (v : (Fin d → ℝ) → ℝ) x)
          + P.c x * (u₁ : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x)
        + ((∑ i, ∑ j, P.a i j x * partialU i u₂ x * partialU j v x)
          + (∑ i, P.b i x * partialU i u₂ x * (v : (Fin d → ℝ) → ℝ) x)
          + P.c x * (u₂ : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x) := by
    filter_upwards [ae_all_iff.2 partialU_add, hcoeFn_add] with x hx hxu
    simp only [hx, hxu, mul_add, add_mul, Finset.sum_add_distrib]
    ring
  unfold parabilinform
  rw [integral_congr_ae hae,
      integral_add (parabilinform_integrand_integrable (P := P) hP_bdd u₁ v)
        (parabilinform_integrand_integrable (P := P) hP_bdd u₂ v)]

lemma parabilinform_smul_left (k : ℝ) (u v : H1U0 d U hU) :
    parabilinform P (k • u) v = k * parabilinform P u v := by
  have partialU_smul : ∀ i, (fun x => partialU i (k • u) x)
      =ᵐ[μU d U] fun x => k • partialU i u x :=
    fun i => WkpU.weakDeriv_smul k u.val 1 (le_refl 1) (fun _ => i)
  have hcoeFn_smul : (fun x => ((k • u : H1U0 d U hU) : (Fin d → ℝ) → ℝ) x)
      =ᵐ[μU d U] fun x => k • (u : (Fin d → ℝ) → ℝ) x :=
    HkU.coeFn_smul k u.val
  have hae : (fun x => (∑ i, ∑ j, P.a i j x * partialU i (k • u) x * partialU j v x)
        + (∑ i, P.b i x * partialU i (k • u) x * (v : (Fin d → ℝ) → ℝ) x)
        + P.c x * ((k • u : H1U0 d U hU) : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x)
      =ᵐ[μU d U] fun x => k * ((∑ i, ∑ j, P.a i j x * partialU i u x * partialU j v x)
        + (∑ i, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x)
        + P.c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x) := by
    filter_upwards [ae_all_iff.2 partialU_smul, hcoeFn_smul] with x hx hxu
    simp only [hx, hxu, smul_eq_mul]
    simp_rw [show ∀ a b c : ℝ, a * (k * b) * c = k * (a * b * c) from fun a b c => by ring]
    simp only [← Finset.mul_sum]
    ring
  unfold parabilinform
  rw [integral_congr_ae hae, integral_const_mul]

lemma parabilinform_add_right {M : ℝ} (hP_bdd : P.IsBounded M) (u v₁ v₂ : H1U0 d U hU) :
    parabilinform P u (v₁ + v₂) = parabilinform P u v₁ + parabilinform P u v₂ := by
  have partialU_add : ∀ j, (fun x => partialU j (v₁ + v₂) x)
      =ᵐ[μU d U] fun x => partialU j v₁ x + partialU j v₂ x :=
    fun j => WkpU.weakDeriv_add v₁.val v₂.val 1 (le_refl 1) (fun _ => j)
  have hcoeFn_add : (fun x => ((v₁ + v₂ : H1U0 d U hU) : (Fin d → ℝ) → ℝ) x)
      =ᵐ[μU d U] fun x => (v₁ : (Fin d → ℝ) → ℝ) x + (v₂ : (Fin d → ℝ) → ℝ) x :=
    HkU.coeFn_add v₁.val v₂.val
  have hae : (fun x => (∑ i, ∑ j, P.a i j x * partialU i u x * partialU j (v₁ + v₂) x)
        + (∑ i, P.b i x * partialU i u x * ((v₁ + v₂ : H1U0 d U hU) : (Fin d → ℝ) → ℝ) x)
        + P.c x * (u : (Fin d → ℝ) → ℝ) x * ((v₁ + v₂ : H1U0 d U hU) : (Fin d → ℝ) → ℝ) x)
      =ᵐ[μU d U] fun x =>
        ((∑ i, ∑ j, P.a i j x * partialU i u x * partialU j v₁ x)
          + (∑ i, P.b i x * partialU i u x * (v₁ : (Fin d → ℝ) → ℝ) x)
          + P.c x * (u : (Fin d → ℝ) → ℝ) x * (v₁ : (Fin d → ℝ) → ℝ) x)
        + ((∑ i, ∑ j, P.a i j x * partialU i u x * partialU j v₂ x)
          + (∑ i, P.b i x * partialU i u x * (v₂ : (Fin d → ℝ) → ℝ) x)
          + P.c x * (u : (Fin d → ℝ) → ℝ) x * (v₂ : (Fin d → ℝ) → ℝ) x) := by
    filter_upwards [ae_all_iff.2 partialU_add, hcoeFn_add] with x hx hxv
    simp only [hx, hxv, mul_add, add_mul, Finset.sum_add_distrib]
    ring
  unfold parabilinform
  rw [integral_congr_ae hae,
      integral_add (parabilinform_integrand_integrable (P := P) hP_bdd u v₁)
        (parabilinform_integrand_integrable (P := P) hP_bdd u v₂)]

lemma parabilinform_smul_right (k : ℝ) (u v : H1U0 d U hU) :
    parabilinform P u (k • v) = k * parabilinform P u v := by
  have partialU_smul : ∀ j, (fun x => partialU j (k • v) x)
      =ᵐ[μU d U] fun x => k • partialU j v x :=
    fun j => WkpU.weakDeriv_smul k v.val 1 (le_refl 1) (fun _ => j)
  have hcoeFn_smul : (fun x => ((k • v : H1U0 d U hU) : (Fin d → ℝ) → ℝ) x)
      =ᵐ[μU d U] fun x => k • (v : (Fin d → ℝ) → ℝ) x :=
    HkU.coeFn_smul k v.val
  have hae : (fun x => (∑ i, ∑ j, P.a i j x * partialU i u x * partialU j (k • v) x)
        + (∑ i, P.b i x * partialU i u x * ((k • v : H1U0 d U hU) : (Fin d → ℝ) → ℝ) x)
        + P.c x * (u : (Fin d → ℝ) → ℝ) x * ((k • v : H1U0 d U hU) : (Fin d → ℝ) → ℝ) x)
      =ᵐ[μU d U] fun x => k * ((∑ i, ∑ j, P.a i j x * partialU i u x * partialU j v x)
        + (∑ i, P.b i x * partialU i u x * (v : (Fin d → ℝ) → ℝ) x)
        + P.c x * (u : (Fin d → ℝ) → ℝ) x * (v : (Fin d → ℝ) → ℝ) x) := by
    filter_upwards [ae_all_iff.2 partialU_smul, hcoeFn_smul] with x hx hxv
    simp only [hx, hxv, smul_eq_mul]
    simp_rw [show ∀ a b c : ℝ, a * b * (k * c) = k * (a * b * c) from fun a b c => by ring]
    simp only [← Finset.mul_sum]
    ring
  unfold parabilinform
  rw [integral_congr_ae hae, integral_const_mul]

lemma parabilinform_zero_left (v : H1U0 d U hU) : parabilinform P 0 v = 0 := by
  rw [show (0 : H1U0 d U hU) = (0 : ℝ) • v from (zero_smul ℝ v).symm,
      parabilinform_smul_left, zero_mul]

lemma parabilinform_zero_right (u : H1U0 d U hU) : parabilinform P u 0 = 0 := by
  rw [show (0 : H1U0 d U hU) = (0 : ℝ) • u from (zero_smul ℝ u).symm,
      parabilinform_smul_right, zero_mul]

/-- Left slot expands over a finite linear combination. -/
lemma parabilinform_sum_left {M : ℝ} (hP_bdd : P.IsBounded M) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (w : ι → H1U0 d U hU) (v : H1U0 d U hU) :
    parabilinform P (∑ j ∈ s, a j • w j) v = ∑ j ∈ s, a j * parabilinform P (w j) v := by
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, parabilinform_zero_left]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, parabilinform_add_left (P := P) hP_bdd,
        parabilinform_smul_left, ih]

/-- Right slot expands over a finite linear combination. -/
lemma parabilinform_sum_right {M : ℝ} (hP_bdd : P.IsBounded M) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (w : ι → H1U0 d U hU) (u : H1U0 d U hU) :
    parabilinform P u (∑ j ∈ s, a j • w j) = ∑ j ∈ s, a j * parabilinform P u (w j) := by
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, parabilinform_zero_right]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, parabilinform_add_right (P := P) hP_bdd,
        parabilinform_smul_right, ih]

/-- `B[uₘ, uₘ] = ∑ⱼ∑ₖ dⱼ dₖ B[wⱼ, wₖ]` — the quadratic-form expansion used in the energy identity. -/
lemma parabilinform_uapprox {M : ℝ} (hP_bdd : P.IsBounded M) (G : GalerkinBasis d U hU)
    {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ) (t : ℝ) :
    parabilinform P (uapprox G dCoeffs t) (uapprox G dCoeffs t)
      = ∑ j : Fin m, ∑ k : Fin m,
          dCoeffs j t * dCoeffs k t * parabilinform P (G.w j.val) (G.w k.val) := by
  unfold uapprox
  rw [parabilinform_sum_left (P := P) hP_bdd]
  simp only [parabilinform_sum_right (P := P) hP_bdd, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))

/-- Galerkin energy identity. -/
lemma galerkin_energy_identity (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U)) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ)
    {M : ℝ} (hP_bdd : ∀ t, (P t).IsBounded M) (hdiff : ∀ k, Differentiable ℝ (dCoeffs k))
    (hODE : GalerkinODE G P T f g dCoeffs) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
      (1 / 2) * deriv (fun t => ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2) t
        + parabilinform (P t) (uapprox G dCoeffs t) (uapprox G dCoeffs t)
      = inner ℝ (f t) (WkpU.toLp (uapprox G dCoeffs t).val) := by
  obtain ⟨hODE1, _⟩ := hODE
  filter_upwards [ae_all_iff.2 hODE1] with t ht
  have hderiv : (1 / 2 : ℝ) * deriv (fun t => ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2) t
      = ∑ k, dCoeffs k t * deriv (dCoeffs k) t := by
    rw [(uapprox_L2_normSq_hasDerivAt G dCoeffs t
        (fun k => (hdiff k).differentiableAt.hasDerivAt)).deriv,
      ← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 from by norm_num, one_mul]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have hquad : parabilinform (P t) (uapprox G dCoeffs t) (uapprox G dCoeffs t)
      = ∑ k, dCoeffs k t * ∑ j, dCoeffs j t * parabilinform (P t) (G.w j.val) (G.w k.val) := by
    rw [parabilinform_uapprox (P := P t) (hP_bdd t), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hf : inner ℝ (f t) (WkpU.toLp (uapprox G dCoeffs t).val)
      = ∑ k, dCoeffs k t * inner ℝ (f t) (WkpU.toLp (G.w k.val).val) := by
    unfold uapprox
    rw [galerkin_combo_toLp G (fun k => dCoeffs k t), inner_sum]
    exact Finset.sum_congr rfl (fun k _ => real_inner_smul_right _ _ _)
  rw [hderiv, hquad, hf, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by rw [← mul_add, ht k])

/-- `d/dt η + θ‖uₘ‖²_{H¹} ≤ (1+2γ)η + ‖f‖²`,
`η = ‖uₘ‖²_{L²}`, `γ = θ/2 + M + M²d/(2θ)`.  From the energy identity (C1): substitute the
Gårding lower bound (B2) for `B[uₘ,uₘ]` and Cauchy–Young `(f,uₘ) ≤ ½‖f‖² + ½η`. -/
lemma galerkin_diff_ineq {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U)) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ) (hP_bdd : ∀ t, (P t).IsBounded M)
    (hdiff : ∀ k, Differentiable ℝ (dCoeffs k))
    (hODE : GalerkinODE G P T f g dCoeffs) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
      deriv (fun t => ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2) t
        + θ * ‖uapprox G dCoeffs t‖ ^ 2
      ≤ (1 + 2 * (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ)))
          * ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2 + ‖f t‖ ^ 2 := by
  filter_upwards [galerkin_energy_identity G P T f g dCoeffs hP_bdd hdiff hODE] with t hC1
  have hgard := parabilinform_garding (P := P t) hθ hMpos (hP_para t) (hP_bdd t)
    (uapprox G dCoeffs t)
  have hload : inner ℝ (f t) (WkpU.toLp (uapprox G dCoeffs t).val)
      ≤ (1 / 2) * ‖f t‖ ^ 2 + (1 / 2) * ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2 := by
    refine (real_inner_le_norm _ _).trans ?_
    have h := cauchy_eps (a := ‖f t‖) (b := ‖WkpU.toLp (uapprox G dCoeffs t).val‖)
      (ε := 1 / 2) (by norm_num)
    rw [show (4 : ℝ) * (1 / 2) = 2 from by norm_num] at h
    linarith [h]
  linarith [hC1, hgard, hload]

/-- (Bessel): `‖uₘ(0)‖²_{L²} = ∑ₖ (g, wₖ)² ≤ ‖g‖²`.  Uses the Galerkin
initial condition `dₖ(0) = (g, wₖ)` and finite Bessel for the orthonormal basis. -/
lemma uapprox_init (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U)) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ)
    (hODE : GalerkinODE G P T f g dCoeffs) :
    ‖WkpU.toLp (uapprox G dCoeffs 0).val‖ ^ 2 ≤ ‖g‖ ^ 2 := by
  obtain ⟨_, hinit⟩ := hODE
  have hon : Orthonormal ℝ (fun k : Fin m => WkpU.toLp (G.w (k : ℕ)).val) :=
    G.orthonormal_L2.comp _ Fin.val_injective
  rw [uapprox_L2_normSq]
  refine le_trans (le_of_eq ?_) (hon.sum_inner_products_le (x := g) (s := Finset.univ))
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hinit k, Real.norm_eq_abs, sq_abs, real_inner_comm]

/-- Bochner norm as integral saves us from having to rewrite in line -/
lemma L2TL2_norm_sq {d : ℕ+} {U : Set (Fin d → ℝ)} {T : ℝ} (f : L2TL2 d U T) :
      ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(volume.restrict (Set.Icc (0:ℝ) T)) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (ae_of_all _ (fun t => real_inner_self_eq_norm_sq (f t)))

/-- Bochner `L²(0,T;H¹₀)` norm as an integral: `‖F‖² = ∫₀ᵀ ‖F t‖²_{H¹}`. -/
lemma L2TH10U_norm_sq {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U} {T : ℝ}
    (F : L2TH10U d U hU T) :
    ‖F‖ ^ 2 = ∫ t, ‖F t‖ ^ 2 ∂(volume.restrict (Set.Icc (0:ℝ) T)) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (ae_of_all _ (fun t => real_inner_self_eq_norm_sq (F t)))

set_option maxHeartbeats 800000 in
/-- Bochner `L²(0,T;H⁻¹)` norm as an integral: `‖F‖² = ∫₀ᵀ ‖F t‖²_{H⁻¹}`.  Same proof as
`L2TH10U_norm_sq`, now unblocked by the dual inner-product instance. -/
lemma L2TH10U_dual_norm_sq {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U} {T : ℝ}
    (F : L2TH10U_dual d U hU T) :
    ‖F‖ ^ 2 = ∫ t, ‖F t‖ ^ 2 ∂(volume.restrict (Set.Icc (0:ℝ) T)) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (ae_of_all _ (fun t => real_inner_self_eq_norm_sq (F t)))

/-- Integrating-factor Grönwall.  If `η' ≤ K η + φ` on `[0,T]` (`η` C¹, `φ ≥ 0`
integrable, `η 0 ≤ δ`), then `η t ≤ e^{KT}(δ + ∫₀ᵀ φ)`.  Proof: `ψ = η e^{-Kt}` has
`ψ' = (η'-Kη)e^{-Kt} ≤ φ`, integrate (FTC). -/
lemma gronwall_integrating_factor {η η' φ : ℝ → ℝ} {K T δ : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hηderiv : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt η (η' t) t)
    (hη'cont : ContinuousOn η' (Set.Icc (0:ℝ) T))
    (hφint : IntervalIntegrable φ MeasureTheory.volume 0 T)
    (hineq : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)), η' t ≤ K * η t + φ t)
    (hφnn : ∀ t ∈ Set.Icc (0:ℝ) T, 0 ≤ φ t)
    (hδ : η 0 ≤ δ) (hδnn : 0 ≤ δ) :
    ∀ t ∈ Set.Icc (0:ℝ) T, η t ≤ Real.exp (K * T) * (δ + ∫ s in (0:ℝ)..T, φ s) := by
  have hηcont : ContinuousOn η (Set.Icc (0:ℝ) T) :=
    fun s hs => (hηderiv s hs).continuousAt.continuousWithinAt
  have hexp : ∀ s : ℝ, HasDerivAt (fun s => Real.exp (-K * s)) (Real.exp (-K * s) * (-K)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -K * s) (-K) s := by
      simpa using (hasDerivAt_id s).const_mul (-K)
    simpa using h1.exp
  have hψderiv : ∀ s ∈ Set.Icc (0:ℝ) T,
      HasDerivAt (fun s => η s * Real.exp (-K * s))
        ((η' s - K * η s) * Real.exp (-K * s)) s := by
    intro s hs
    have h := (hηderiv s hs).mul (hexp s)
    exact h.congr_deriv (by ring)
  have hexpcont : Continuous (fun s : ℝ => Real.exp (-K * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hψ'cont : ContinuousOn (fun s => (η' s - K * η s) * Real.exp (-K * s)) (Set.Icc (0:ℝ) T) :=
    (hη'cont.sub (continuousOn_const.mul hηcont)).mul hexpcont.continuousOn
  have hintφnn : 0 ≤ ∫ s in (0:ℝ)..T, φ s :=
    intervalIntegral.integral_nonneg hT (fun s hs => hφnn s ⟨hs.1, hs.2⟩)
  intro t ht
  obtain ⟨ht0, htT⟩ := ht
  have hsub : Set.Icc (0:ℝ) t ⊆ Set.Icc (0:ℝ) T := Set.Icc_subset_Icc le_rfl htT
  have hψ'int : IntervalIntegrable (fun s => (η' s - K * η s) * Real.exp (-K * s))
      MeasureTheory.volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht0 (hψ'cont.mono hsub)
  have hψderiv_t : ∀ s ∈ Set.uIcc (0:ℝ) t, HasDerivAt (fun s => η s * Real.exp (-K * s))
      ((η' s - K * η s) * Real.exp (-K * s)) s := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    exact hψderiv s (hsub hs)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hψderiv_t hψ'int
  have hφint_t : IntervalIntegrable φ MeasureTheory.volume 0 t :=
    hφint.mono_set (by rw [Set.uIcc_of_le ht0, Set.uIcc_of_le hT]; exact hsub)
  have hφint_tT : IntervalIntegrable φ MeasureTheory.volume t T :=
    hφint.mono_set (by rw [Set.uIcc_of_le htT, Set.uIcc_of_le hT]
                       exact Set.Icc_subset_Icc ht0 le_rfl)
  have hcompare : (∫ s in (0:ℝ)..t, (η' s - K * η s) * Real.exp (-K * s))
      ≤ ∫ s in (0:ℝ)..t, φ s := by
    refine intervalIntegral.integral_mono_ae_restrict ht0 hψ'int hφint_t ?_
    have hae : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) t)),
        η' s ≤ K * η s + φ s :=
      ae_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) hineq
    filter_upwards [hae, MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs hs_mem
    have hsT := hsub hs_mem
    have h1 : η' s - K * η s ≤ φ s := by linarith [hs]
    have hexp1 : Real.exp (-K * s) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hs_mem.1, hK]
    calc (η' s - K * η s) * Real.exp (-K * s)
        ≤ φ s * Real.exp (-K * s) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ φ s := mul_le_of_le_one_right (hφnn s hsT) hexp1
  have hmono : (∫ s in (0:ℝ)..t, φ s) ≤ ∫ s in (0:ℝ)..T, φ s := by
    have hadj := intervalIntegral.integral_add_adjacent_intervals hφint_t
      (hφint.mono_set (by rw [Set.uIcc_of_le htT, Set.uIcc_of_le hT]
                          exact Set.Icc_subset_Icc ht0 le_rfl))
    have hrest : 0 ≤ ∫ s in t..T, φ s :=
      intervalIntegral.integral_nonneg htT (fun s hs => hφnn s ⟨le_trans ht0 hs.1, hs.2⟩)
    linarith [hadj]
  have hψt : η t * Real.exp (-K * t) ≤ δ + ∫ s in (0:ℝ)..T, φ s := by
    have hchain : η t * Real.exp (-K * t) - η 0 * Real.exp (-K * 0) ≤ ∫ s in (0:ℝ)..T, φ s := by
      rw [← hFTC]; exact hcompare.trans hmono
    simp only [mul_zero, Real.exp_zero, mul_one] at hchain
    linarith [hδ]
  have hcancel : Real.exp (-K * t) * Real.exp (K * t) = 1 := by
    rw [← Real.exp_add, show -K * t + K * t = 0 from by ring, Real.exp_zero]
  have key : η t ≤ (δ + ∫ s in (0:ℝ)..T, φ s) * Real.exp (K * t) := by
    have h2 := mul_le_mul_of_nonneg_right hψt (Real.exp_pos (K * t)).le
    rwa [mul_assoc, hcancel, mul_one] at h2
  calc η t ≤ (δ + ∫ s in (0:ℝ)..T, φ s) * Real.exp (K * t) := key
    _ ≤ (δ + ∫ s in (0:ℝ)..T, φ s) * Real.exp (K * T) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hK))
          (by linarith [hintφnn])
    _ = Real.exp (K * T) * (δ + ∫ s in (0:ℝ)..T, φ s) := mul_comm _ _

-- Energy bound 1: pointwise L² of u_m  ‖u_m(t)‖²_L² ≤ C(‖f‖² + ‖g‖²)  a.e. t
-- Proof: energy identity + Gronwall on ‖u_m(t)‖²_L² with IC ≤ ‖g‖²
lemma galerkin_bound_L2_pointwise
    {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ)
    (hP_bdd : ∀ t, (P t).IsBounded M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U)) {m : ℕ}
        (dCoeffs : Fin m → ℝ → ℝ), (∀ k, ContDiff ℝ 1 (dCoeffs k)) →
        GalerkinODE G P T f g dCoeffs →
        ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
          ‖WkpU.toLp (uapprox G dCoeffs t).val‖^2
            ≤ C * (‖f‖^2 + ‖g‖^2) := by
  refine ⟨Real.exp ((1 + 2 * (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ))) * T),
    (Real.exp_pos _).le, ?_⟩
  intro f g m dCoeffs hdiff hODE
  have hdderiv : ∀ k t, HasDerivAt (dCoeffs k) (deriv (dCoeffs k) t) t :=
    fun k t => ((hdiff k).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hKnn : 0 ≤ 1 + 2 * (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ)) := by
    have h2 : 0 ≤ M ^ 2 * (d : ℝ) / (2 * θ) := div_nonneg (by positivity) (by linarith)
    nlinarith [hMpos, hθ, h2]
  have hηderiv : ∀ t ∈ Set.Icc (0:ℝ) T,
      HasDerivAt (fun t => ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2)
        (2 * ∑ k, deriv (dCoeffs k) t * dCoeffs k t) t :=
    fun t _ => uapprox_L2_normSq_hasDerivAt G dCoeffs t (fun k => hdderiv k t)
  have hη'cont : ContinuousOn (fun t => 2 * ∑ k : Fin m, deriv (dCoeffs k) t * dCoeffs k t)
      (Set.Icc (0:ℝ) T) :=
    (continuous_const.mul (continuous_finsetSum _ (fun k _ =>
      ((hdiff k).continuous_deriv (by norm_num)).mul (hdiff k).continuous))).continuousOn
  have hφint : IntervalIntegrable (fun t => ‖f t‖ ^ 2) MeasureTheory.volume 0 T := by
    apply MeasureTheory.IntegrableOn.intervalIntegrable
    rw [Set.uIcc_of_le hT.le]
    have hnorm : MemLp (fun t => ‖f t‖) 2 (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)) :=
      (Lp.memLp f).norm
    simp only [pow_two]
    exact hnorm.integrable_mul hnorm
  have hineq : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)),
      (2 * ∑ k, deriv (dCoeffs k) t * dCoeffs k t)
        ≤ (1 + 2 * (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ)))
            * ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2 + ‖f t‖ ^ 2 := by
    filter_upwards [galerkin_diff_ineq hθ hMpos G P T f g dCoeffs hP_para hP_bdd
      (fun k => (hdiff k).differentiable (by norm_num)) hODE] with t hC2
    rw [(uapprox_L2_normSq_hasDerivAt G dCoeffs t (fun k => hdderiv k t)).deriv] at hC2
    nlinarith [hC2, mul_nonneg hθ.le (sq_nonneg ‖uapprox G dCoeffs t‖)]
  have hgron := gronwall_integrating_factor hT.le hKnn hηderiv hη'cont hφint hineq
    (fun t _ => sq_nonneg _) (uapprox_init G P T f g dCoeffs hODE) (sq_nonneg _)
  have hfnorm : (∫ s in (0:ℝ)..T, ‖f s‖ ^ 2) = ‖f‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hT.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← L2TL2_norm_sq]
  rw [hfnorm] at hgron
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  have h := hgron t ht
  rwa [add_comm (‖g‖ ^ 2) (‖f‖ ^ 2)] at h


-- Energy bound 2: L²(0,T;H¹₀) integral  ∫ ‖u_m(t)‖²_H¹ ≤ C(‖f‖² + ‖g‖²)
lemma galerkin_bound_H1_integral
    {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ)
    (hP_bdd : ∀ t, (P t).IsBounded M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U)) {m : ℕ}
        (dCoeffs : Fin m → ℝ → ℝ), (∀ k, ContDiff ℝ 1 (dCoeffs k)) →
        GalerkinODE G P T f g dCoeffs →
        (∫ t in Set.Icc (0:ℝ) T, ‖uapprox G dCoeffs t‖^2)
          ≤ C * (‖f‖^2 + ‖g‖^2) := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ := galerkin_bound_L2_pointwise hθ hMpos G P T hT hP_para hP_bdd
  have hKnn : 0 ≤ 1 + 2 * (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ)) := by
    have h2 : 0 ≤ M ^ 2 * (d : ℝ) / (2 * θ) := div_nonneg (by positivity) (by linarith)
    nlinarith [hMpos, hθ, h2]
  refine ⟨((1 + 2 * (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ))) * T * C₁ + 1) / θ,
    div_nonneg (by nlinarith [mul_nonneg (mul_nonneg hKnn hT.le) hC₁nn]) hθ.le, ?_⟩
  intro f g m dCoeffs hdiff hODE
  have hdderiv : ∀ k t, HasDerivAt (dCoeffs k) (deriv (dCoeffs k) t) t :=
    fun k t => ((hdiff k).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hηderiv : ∀ t, HasDerivAt (fun t => ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2)
      (2 * ∑ k, deriv (dCoeffs k) t * dCoeffs k t) t :=
    fun t => uapprox_L2_normSq_hasDerivAt G dCoeffs t (fun k => hdderiv k t)
  have hηcont : Continuous (fun t => ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2) :=
    continuous_iff_continuousAt.mpr (fun t => (hηderiv t).continuousAt)
  have hη'cont : Continuous (fun t => 2 * ∑ k : Fin m, deriv (dCoeffs k) t * dCoeffs k t) :=
    continuous_const.mul (continuous_finsetSum _ (fun k _ =>
      ((hdiff k).continuous_deriv (by norm_num)).mul (hdiff k).continuous))
  have hHcont : Continuous (fun t => ‖uapprox G dCoeffs t‖ ^ 2) :=
    (continuous_finsetSum _
      (fun k _ => (hdiff k).continuous.smul continuous_const)).norm.pow 2
  have hηint : IntegrableOn (fun t => ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2)
      (Set.Icc (0:ℝ) T) := hηcont.integrableOn_Icc
  have hη'int : IntegrableOn (fun t => 2 * ∑ k, deriv (dCoeffs k) t * dCoeffs k t)
      (Set.Icc (0:ℝ) T) := hη'cont.integrableOn_Icc
  have hHint : IntegrableOn (fun t => ‖uapprox G dCoeffs t‖ ^ 2)
      (Set.Icc (0:ℝ) T) := hHcont.integrableOn_Icc
  have hφint : IntegrableOn (fun t => ‖f t‖ ^ 2) (Set.Icc (0:ℝ) T) := by
    have hnorm : MemLp (fun t => ‖f t‖) 2 (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)) :=
      (Lp.memLp f).norm
    simp only [pow_two]
    exact hnorm.integrable_mul hnorm
  have hae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)),
      θ * ‖uapprox G dCoeffs t‖ ^ 2
        ≤ (1 + 2 * (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ)))
            * ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2 + ‖f t‖ ^ 2
          - 2 * ∑ k, deriv (dCoeffs k) t * dCoeffs k t := by
    filter_upwards [galerkin_diff_ineq hθ hMpos G P T f g dCoeffs hP_para hP_bdd
      (fun k => (hdiff k).differentiable (by norm_num)) hODE] with t ht
    rw [(hηderiv t).deriv] at ht
    linarith [ht]
  have hKη_int : IntegrableOn (fun t => (1 + 2 * (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ)))
      * ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2) (Set.Icc (0:ℝ) T) := hηint.const_mul _
  have hKηφ_int : IntegrableOn (fun t => (1 + 2 * (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ)))
      * ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2 + ‖f t‖ ^ 2) (Set.Icc (0:ℝ) T) :=
    hKη_int.add hφint
  have hmono : (∫ t in Set.Icc (0:ℝ) T, θ * ‖uapprox G dCoeffs t‖ ^ 2)
      ≤ ∫ t in Set.Icc (0:ℝ) T, ((1 + 2 * (θ / 2 + M + M ^ 2 * (d : ℝ) / (2 * θ)))
          * ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2 + ‖f t‖ ^ 2
          - 2 * ∑ k, deriv (dCoeffs k) t * dCoeffs k t) :=
    MeasureTheory.integral_mono_ae (hHint.const_mul θ) (hKηφ_int.sub hη'int) hae
  rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub hKηφ_int hη'int,
      MeasureTheory.integral_add hKη_int hφint,
      MeasureTheory.integral_const_mul] at hmono
  have hFTCη : (∫ t in Set.Icc (0:ℝ) T, 2 * ∑ k, deriv (dCoeffs k) t * dCoeffs k t)
      = ‖WkpU.toLp (uapprox G dCoeffs T).val‖ ^ 2
        - ‖WkpU.toLp (uapprox G dCoeffs 0).val‖ ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hηderiv x)
      (hη'cont.intervalIntegrable 0 T)
  have hφnorm : (∫ t in Set.Icc (0:ℝ) T, ‖f t‖ ^ 2) = ‖f‖ ^ 2 := (L2TL2_norm_sq f).symm
  have hvol : MeasureTheory.volume.real (Set.Icc (0:ℝ) T) = T := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hT.le]
  have hηbound : (∫ t in Set.Icc (0:ℝ) T, ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2)
      ≤ T * (C₁ * (‖f‖ ^ 2 + ‖g‖ ^ 2)) := by
    calc (∫ t in Set.Icc (0:ℝ) T, ‖WkpU.toLp (uapprox G dCoeffs t).val‖ ^ 2)
        ≤ ∫ _t in Set.Icc (0:ℝ) T, C₁ * (‖f‖ ^ 2 + ‖g‖ ^ 2) :=
          MeasureTheory.integral_mono_ae hηint
            (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
            (hC₁ f g dCoeffs hdiff hODE)
      _ = T * (C₁ * (‖f‖ ^ 2 + ‖g‖ ^ 2)) := by
          rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
  rw [hFTCη, hφnorm] at hmono
  have hη0 : ‖WkpU.toLp (uapprox G dCoeffs 0).val‖ ^ 2 ≤ ‖g‖ ^ 2 :=
    uapprox_init G P T f g dCoeffs hODE
  have hKη := mul_le_mul_of_nonneg_left hηbound hKnn
  rw [div_mul_eq_mul_div, le_div_iff₀ hθ]
  nlinarith [hmono, hKη, sq_nonneg ‖WkpU.toLp (uapprox G dCoeffs T).val‖, hη0]


/-- The L²→H⁻¹ inclusion pairs against `v ∈ H¹₀` by the `L²` inner product. -/
lemma L2ToHinvCLM_apply {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (f : Lp ℝ 2 (μU d U)) (v : H1U0 d U hU) :
    (L2ToHinvCLM f) v = inner ℝ f (WkpU.toLp v.val) := rfl

/-- **(E1)** L²-orthogonal projection of `v` onto `span{w₀,…,w_{m-1}}`, as an `H¹₀` element. -/
noncomputable def galerkinProj (G : GalerkinBasis d U hU) (m : ℕ) (v : H1U0 d U hU) :
    H1U0 d U hU :=
  ∑ k : Fin m, (inner ℝ (WkpU.toLp v.val) (WkpU.toLp (G.w (k : ℕ)).val) : ℝ) • G.w (k : ℕ)

lemma galerkinProj_toLp (G : GalerkinBasis d U hU) (m : ℕ) (v : H1U0 d U hU) :
    WkpU.toLp (galerkinProj G m v).val
      = ∑ k : Fin m, (inner ℝ (WkpU.toLp v.val) (WkpU.toLp (G.w (k : ℕ)).val) : ℝ)
          • WkpU.toLp (G.w (k : ℕ)).val :=
  galerkin_combo_toLp G (fun k => inner ℝ (WkpU.toLp v.val) (WkpU.toLp (G.w (k : ℕ)).val))

/-- The projection is `L²`-non-expansive: `‖P_m v‖_{L²} ≤ ‖v‖_{H¹}` (Parseval + Bessel). -/
lemma galerkinProj_L2_le (G : GalerkinBasis d U hU) (m : ℕ) (v : H1U0 d U hU) :
    ‖WkpU.toLp (galerkinProj G m v).val‖ ≤ ‖v‖ := by
  have hon : Orthonormal ℝ (fun k : Fin m => WkpU.toLp (G.w (k : ℕ)).val) :=
    G.orthonormal_L2.comp _ Fin.val_injective
  have hnorm_eq : ‖WkpU.toLp (galerkinProj G m v).val‖ ^ 2
      = ∑ k : Fin m, (inner ℝ (WkpU.toLp v.val) (WkpU.toLp (G.w (k : ℕ)).val) : ℝ) ^ 2 :=
    galerkin_combo_normSq G (fun k => inner ℝ (WkpU.toLp v.val) (WkpU.toLp (G.w (k : ℕ)).val))
  have hbessel : (∑ k : Fin m,
      (inner ℝ (WkpU.toLp v.val) (WkpU.toLp (G.w (k : ℕ)).val) : ℝ) ^ 2)
      ≤ ‖WkpU.toLp v.val‖ ^ 2 := by
    refine le_trans (le_of_eq ?_) (hon.sum_inner_products_le (x := WkpU.toLp v.val)
      (s := Finset.univ))
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, real_inner_comm]
  have hL2 := H1U0.l2_norm_le_norm v
  nlinarith [hnorm_eq, hbessel, hL2, norm_nonneg (WkpU.toLp (galerkinProj G m v).val),
    norm_nonneg (WkpU.toLp v.val), norm_nonneg v]

/-- The projection is `H¹`-non-expansive (the added basis property). -/
lemma galerkinProj_H1_le (G : GalerkinBasis d U hU) (m : ℕ) (v : H1U0 d U hU) :
    ‖galerkinProj G m v‖ ≤ ‖v‖ := G.projL2_H1_le m v

/-- **(E1 pairing)** From the Galerkin ODE, `(u'ₘ, v)_{L²} = (f, Pₘv)_{L²} − B[uₘ, Pₘv]`. -/
lemma galerkin_uprime_pairing {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (G : GalerkinBasis d U hU) (P : ParabolicCoeffs d) {M : ℝ} (hP_bdd : P.IsBounded M)
    {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ) (t : ℝ) (fL2 : Lp ℝ 2 (μU d U))
    (hODE : ∀ k : Fin m, deriv (dCoeffs k) t
      + ∑ j : Fin m, dCoeffs j t * parabilinform P (G.w (j : ℕ)) (G.w (k : ℕ))
      = inner ℝ fL2 (WkpU.toLp (G.w (k : ℕ)).val))
    (v : H1U0 d U hU) :
    inner ℝ (WkpU.toLp (u'approx G dCoeffs t).val) (WkpU.toLp v.val)
      = inner ℝ fL2 (WkpU.toLp (galerkinProj G m v).val)
        - parabilinform P (uapprox G dCoeffs t) (galerkinProj G m v) := by
  have e1 : inner ℝ (WkpU.toLp (u'approx G dCoeffs t).val) (WkpU.toLp v.val)
      = ∑ k : Fin m, deriv (dCoeffs k) t
          * inner ℝ (WkpU.toLp v.val) (WkpU.toLp (G.w (k : ℕ)).val) := by
    unfold u'approx
    rw [galerkin_combo_toLp G (fun k => deriv (dCoeffs k) t), sum_inner]
    exact Finset.sum_congr rfl (fun k _ => by rw [real_inner_smul_left, real_inner_comm])
  have e2 : inner ℝ fL2 (WkpU.toLp (galerkinProj G m v).val)
      = ∑ k : Fin m, inner ℝ (WkpU.toLp v.val) (WkpU.toLp (G.w (k : ℕ)).val)
          * inner ℝ fL2 (WkpU.toLp (G.w (k : ℕ)).val) := by
    rw [galerkinProj_toLp, inner_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [real_inner_smul_right])
  have e3 : parabilinform P (uapprox G dCoeffs t) (galerkinProj G m v)
      = ∑ k : Fin m, inner ℝ (WkpU.toLp v.val) (WkpU.toLp (G.w (k : ℕ)).val)
          * ∑ j : Fin m, dCoeffs j t * parabilinform P (G.w (j : ℕ)) (G.w (k : ℕ)) := by
    unfold galerkinProj uapprox
    rw [parabilinform_sum_right (P := P) hP_bdd]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [parabilinform_sum_left (P := P) hP_bdd]
  rw [e1, e2, e3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  linear_combination (inner ℝ (WkpU.toLp v.val) (WkpU.toLp (G.w (k : ℕ)).val) : ℝ) * hODE k

-- Energy bound 3: L²(0,T; H⁻¹) integral on u'_m  ∫ ‖u'_m(t)‖²_H⁻¹ ≤ C(‖f‖² + ‖g‖²)
--complication by needing to show u'm is in H^-1, but that causes a heartbeat blowup where it cannot refer that far up the tree
lemma galerkin_bound_Hinv_integral
    {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ)
    (hP_bdd : ∀ t, (P t).IsBounded M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U)) {m : ℕ}
        (dCoeffs : Fin m → ℝ → ℝ), (∀ k, ContDiff ℝ 1 (dCoeffs k)) →
        GalerkinODE G P T f g dCoeffs →
        (∫ t in Set.Icc (0:ℝ) T,
            (hinvNormOfH1 (u'approx G dCoeffs t))^2)
          ≤ C * (‖f‖^2 + ‖g‖^2) := by
  obtain ⟨C₂, hC₂nn, hC₂⟩ := galerkin_bound_H1_integral hθ hMpos G P T hT hP_para hP_bdd
  refine ⟨2 + 2 * (M * ((d : ℝ) ^ 2 + (d : ℝ) + 1)) ^ 2 * C₂, by positivity, ?_⟩
  intro f g m dCoeffs hdiff hODE
  -- pointwise bound: hinvNormOfH1(u'ₘ) ≤ ‖f t‖ + C'‖uₘ‖_{H¹}
  have hpoint : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)),
      hinvNormOfH1 (u'approx G dCoeffs t)
        ≤ ‖f t‖ + M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖uapprox G dCoeffs t‖ := by
    obtain ⟨hODE1, _⟩ := hODE
    filter_upwards [ae_all_iff.2 hODE1] with t ht
    rw [hinvNormOfH1]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [L2ToHinvCLM_apply, galerkin_uprime_pairing G (P t) (hP_bdd t) dCoeffs t (f t) ht v]
    have hb1 : |inner ℝ (f t) (WkpU.toLp (galerkinProj G m v).val)| ≤ ‖f t‖ * ‖v‖ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (galerkinProj_L2_le G m v) (norm_nonneg _))
    have hb2 : |parabilinform (P t) (uapprox G dCoeffs t) (galerkinProj G m v)|
        ≤ M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖uapprox G dCoeffs t‖ * ‖v‖ :=
      (parabilinform_bound (P := P t) M (hP_bdd t) (uapprox G dCoeffs t)
        (galerkinProj G m v)).trans
        (mul_le_mul_of_nonneg_left (galerkinProj_H1_le G m v)
          (by positivity))
    calc ‖inner ℝ (f t) (WkpU.toLp (galerkinProj G m v).val)
            - parabilinform (P t) (uapprox G dCoeffs t) (galerkinProj G m v)‖
        ≤ ‖inner ℝ (f t) (WkpU.toLp (galerkinProj G m v).val)‖
            + ‖parabilinform (P t) (uapprox G dCoeffs t) (galerkinProj G m v)‖ := norm_sub_le _ _
      _ ≤ ‖f t‖ * ‖v‖ + M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖uapprox G dCoeffs t‖ * ‖v‖ := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact add_le_add hb1 hb2
      _ = (‖f t‖ + M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖uapprox G dCoeffs t‖) * ‖v‖ := by ring
  -- continuity → integrability of hinvNormOfH1(u'ₘ·)²
  have hcont : Continuous (fun t => hinvNormOfH1 (u'approx G dCoeffs t)) := by
    have heq : (fun t => hinvNormOfH1 (u'approx G dCoeffs t))
        = fun t => ‖∑ k : Fin m,
            deriv (dCoeffs k) t
              • L2ToHinvCLM (d := d) (U := U) (hU := hU) (WkpU.toLp (G.w (k : ℕ)).val)‖ := by
      funext t
      rw [hinvNormOfH1]
      refine congrArg norm ?_
      unfold u'approx
      rw [galerkin_combo_toLp G (fun k => deriv (dCoeffs k) t), map_sum]
      exact Finset.sum_congr rfl (fun k _ => map_smul _ _ _)
    rw [heq]
    exact (continuous_finsetSum _ (fun k _ =>
      ((hdiff k).continuous_deriv (by norm_num)).smul continuous_const)).norm
  have hHinvint : IntegrableOn (fun t => hinvNormOfH1 (u'approx G dCoeffs t) ^ 2)
      (Set.Icc (0:ℝ) T) := (hcont.pow 2).integrableOn_Icc
  have hφint : IntegrableOn (fun t => ‖f t‖ ^ 2) (Set.Icc (0:ℝ) T) := by
    have hnorm : MemLp (fun t => ‖f t‖) 2 (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)) :=
      (Lp.memLp f).norm
    simp only [pow_two]
    exact hnorm.integrable_mul hnorm
  have hHint : IntegrableOn (fun t => ‖uapprox G dCoeffs t‖ ^ 2) (Set.Icc (0:ℝ) T) :=
    ((continuous_finsetSum _
      (fun k _ => (hdiff k).continuous.smul continuous_const)).norm.pow 2).integrableOn_Icc
  -- square bound
  have hsq : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)),
      hinvNormOfH1 (u'approx G dCoeffs t) ^ 2
        ≤ 2 * ‖f t‖ ^ 2
          + 2 * (M * ((d : ℝ) ^ 2 + (d : ℝ) + 1)) ^ 2 * ‖uapprox G dCoeffs t‖ ^ 2 := by
    filter_upwards [hpoint] with t hpt
    have h0 := hinvNormOfH1_nonneg (u'approx G dCoeffs t)
    nlinarith [hpt, h0, sq_nonneg (‖f t‖ - M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖uapprox G dCoeffs t‖)]
  have hRHSint : IntegrableOn (fun t => 2 * ‖f t‖ ^ 2
      + 2 * (M * ((d : ℝ) ^ 2 + (d : ℝ) + 1)) ^ 2 * ‖uapprox G dCoeffs t‖ ^ 2)
      (Set.Icc (0:ℝ) T) := (hφint.const_mul 2).add (hHint.const_mul _)
  calc (∫ t in Set.Icc (0:ℝ) T, hinvNormOfH1 (u'approx G dCoeffs t) ^ 2)
      ≤ ∫ t in Set.Icc (0:ℝ) T, (2 * ‖f t‖ ^ 2
          + 2 * (M * ((d : ℝ) ^ 2 + (d : ℝ) + 1)) ^ 2 * ‖uapprox G dCoeffs t‖ ^ 2) :=
        MeasureTheory.integral_mono_ae hHinvint hRHSint hsq
    _ = 2 * (∫ t in Set.Icc (0:ℝ) T, ‖f t‖ ^ 2)
          + 2 * (M * ((d : ℝ) ^ 2 + (d : ℝ) + 1)) ^ 2
            * (∫ t in Set.Icc (0:ℝ) T, ‖uapprox G dCoeffs t‖ ^ 2) := by
        rw [MeasureTheory.integral_add (hφint.const_mul 2) (hHint.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ (2 + 2 * (M * ((d : ℝ) ^ 2 + (d : ℝ) + 1)) ^ 2 * C₂) * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
        rw [(L2TL2_norm_sq f).symm]
        have hD2 := hC₂ f g dCoeffs hdiff hODE
        have hfg : (0:ℝ) ≤ ‖f‖ ^ 2 := sq_nonneg _
        have hCnn : 0 ≤ 2 * (M * ((d : ℝ) ^ 2 + (d : ℝ) + 1)) ^ 2 := by positivity
        nlinarith [hD2, hfg, sq_nonneg ‖g‖, hCnn]



--Theorem 2: combined energy estimate (pointwise L² + L²(0,T;H¹₀) + L²(0,T;H⁻¹) on u'_m)
theorem galerkin_energy_estimate
    {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ)
    (hP_bdd : ∀ t, (P t).IsBounded M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U)) {m : ℕ}
        (dCoeffs : Fin m → ℝ → ℝ), (∀ k, ContDiff ℝ 1 (dCoeffs k)) →
        GalerkinODE G P T f g dCoeffs →
        (∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
            ‖WkpU.toLp (uapprox G dCoeffs t).val‖^2
              ≤ C * (‖f‖^2 + ‖g‖^2))
        ∧
        ((∫ t in Set.Icc (0:ℝ) T, ‖uapprox G dCoeffs t‖^2)
            ≤ C * (‖f‖^2 + ‖g‖^2))
        ∧
        ((∫ t in Set.Icc (0:ℝ) T,
            (hinvNormOfH1 (u'approx G dCoeffs t))^2)
            ≤ C * (‖f‖^2 + ‖g‖^2)) := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ := galerkin_bound_L2_pointwise hθ hMpos G P T hT hP_para hP_bdd
  obtain ⟨C₂, hC₂nn, hC₂⟩ := galerkin_bound_H1_integral hθ hMpos G P T hT hP_para hP_bdd
  obtain ⟨C₃, hC₃nn, hC₃⟩ := galerkin_bound_Hinv_integral hθ hMpos G P T hT hP_para hP_bdd
  refine ⟨max C₁ (max C₂ C₃), le_trans hC₁nn (le_max_left _ _), ?_⟩
  intro f g m dCoeffs hdiff hODE
  have hfgnn : (0:ℝ) ≤ ‖f‖ ^ 2 + ‖g‖ ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hC₁ f g dCoeffs hdiff hODE] with t ht
    exact ht.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hfgnn)
  · exact (hC₂ f g dCoeffs hdiff hODE).trans
      (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hfgnn)
  · exact (hC₃ f g dCoeffs hdiff hODE).trans
      (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) hfgnn)


-- =================== HELPER LEMMAS FOR EXISTENCE ===================


noncomputable def uapproxLift
    (G : GalerkinBasis d U hU) (T : ℝ)
    {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ)
    (h_cont : ∀ k, Continuous (dCoeffs k)) :
    L2TH10U d U hU T := by
  -- (1) `uapprox G dCoeffs` is continuous in `t`: finite sum of continuous things.
  have h_uapprox_cont : Continuous (fun t => uapprox G dCoeffs t) := by
    unfold uapprox
    exact continuous_finsetSum _ (fun k _ => (h_cont k).smul continuous_const)
  -- (2) On the compact interval `[0, T]`, `‖uapprox _ _ _‖` is bounded above.
  -- Use `Classical.choose` since we are eliminating `∃` into a `Type`-valued goal.
  have h_bdd_above :
      BddAbove ((fun t => ‖uapprox G dCoeffs t‖) '' Set.Icc (0:ℝ) T) :=
    (isCompact_Icc.image_of_continuousOn h_uapprox_cont.norm.continuousOn).bddAbove
  let C : ℝ := Classical.choose h_bdd_above
  have hC : C ∈ upperBounds ((fun t => ‖uapprox G dCoeffs t‖) '' Set.Icc (0:ℝ) T) :=
    Classical.choose_spec h_bdd_above
  -- (3) The bound holds a.e. on `volume.restrict (Set.Icc 0 T)`.
  have h_ae_bound :
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
        ‖uapprox G dCoeffs t‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards with t ht
    exact hC ⟨t, ht, rfl⟩
  -- (4) Strong measurability follows from continuity.

  have h_aesm :
      AEStronglyMeasurable (fun t => uapprox G dCoeffs t)
        (volume.restrict (Set.Icc (0:ℝ) T)) := by
    haveI : SecondCountableTopologyEither ℝ (H1U0 d U hU) := ⟨Or.inl inferInstance⟩
    exact h_uapprox_cont.aestronglyMeasurable
  -- (5) Bounded + AE-measurable on a finite-measure space ⟹ `MemLp`.
  have h_memLp :
      MemLp (fun t => uapprox G dCoeffs t) 2
        (volume.restrict (Set.Icc (0:ℝ) T)) :=
    MemLp.of_bound h_aesm C h_ae_bound
  -- (6) Package as an `Lp` element.
  exact h_memLp.toLp _


noncomputable def u'approxLift
    (G : GalerkinBasis d U hU) (T : ℝ)
    {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ)
    (h_C1 : ∀ k, ContDiff ℝ 1 (dCoeffs k)) :
    L2TH10U_dual d U hU T := by
  -- (1) Continuity of each derivative (from `C¹`).
  have h_deriv_cont : ∀ k, Continuous (deriv (dCoeffs k)) := fun k =>
    (h_C1 k).continuous_deriv_one
  -- (2) `u'approx` is continuous in `t`: finite sum of `(continuous scalar) •
  -- (constant H¹₀ vector)` summands.
  have h_u'approx_cont : Continuous (fun t => u'approx G dCoeffs t) := by
    unfold u'approx
    exact continuous_finsetSum _
      (fun k _ => (h_deriv_cont k).smul continuous_const)
  -- (3) `‖u'approx _ _‖_{H¹}` is bounded above on the compact interval `[0,T]`.
  have h_bdd_above :
      BddAbove ((fun t => ‖u'approx G dCoeffs t‖) '' Set.Icc (0:ℝ) T) :=
    (isCompact_Icc.image_of_continuousOn h_u'approx_cont.norm.continuousOn).bddAbove
  let C : ℝ := Classical.choose h_bdd_above
  have hC : C ∈ upperBounds ((fun t => ‖u'approx G dCoeffs t‖) '' Set.Icc (0:ℝ) T) :=
    Classical.choose_spec h_bdd_above
  -- (4) The bound holds a.e. on the restricted measure.
  have h_ae_bound :
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
        ‖u'approx G dCoeffs t‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards with t ht
    exact hC ⟨t, ht, rfl⟩
  -- (5) Strong measurability, with the second-countability hint on reals
  have h_aesm :
      AEStronglyMeasurable (fun t => u'approx G dCoeffs t)
        (volume.restrict (Set.Icc (0:ℝ) T)) := by
    haveI : SecondCountableTopologyEither ℝ (H1U0 d U hU) := ⟨Or.inl inferInstance⟩
    exact h_u'approx_cont.aestronglyMeasurable
  -- (6) `MemLp` ⟹ `L²(0,T; H¹₀)` element.
  have h_memLp :
      MemLp (fun t => u'approx G dCoeffs t) 2
        (volume.restrict (Set.Icc (0:ℝ) T)) :=
    MemLp.of_bound h_aesm C h_ae_bound

  let vL2 : L2TH10U d U hU T := h_memLp.toLp _
  exact ContinuousLinearMap.compLp H1U0_inclusion_Hinv vL2

/-- ulift to pointwise -/
lemma uapproxLift_coeFn (G : GalerkinBasis d U hU) (T : ℝ) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ)
    (h_cont : ∀ k, Continuous (dCoeffs k)) :
    (uapproxLift G T dCoeffs h_cont)
      =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)] fun t => uapprox G dCoeffs t := by
  unfold uapproxLift
  exact MemLp.coeFn_toLp _

/-- `‖uapproxLift‖²_{L²(0,T;H¹₀)} = ∫₀ᵀ ‖uₘ(t)‖²_{H¹}`. -/
lemma uapproxLift_norm_sq (G : GalerkinBasis d U hU) (T : ℝ) {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ)
    (h_cont : ∀ k, Continuous (dCoeffs k)) :
    ‖uapproxLift G T dCoeffs h_cont‖ ^ 2
      = ∫ t in Set.Icc (0:ℝ) T, ‖uapprox G dCoeffs t‖ ^ 2 := by
  rw [L2TH10U_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [uapproxLift_coeFn G T dCoeffs h_cont] with t ht
  rw [ht]

/-- `H¹₀` is infinite-dimensional: the Galerkin basis supplies infinitely many H¹-orthogonal
(hence, once normalized, orthonormal, hence linearly independent) vectors. -/
lemma galerkin_H1U0_infinite (G : GalerkinBasis d U hU) :
    ¬ FiniteDimensional ℝ (H1U0 d U hU) := by
  have hne : ∀ k, (0:ℝ) < ‖G.w k‖ := by
    intro k
    rw [norm_pos_iff]
    intro h
    have h1 : ‖WkpU.toLp (G.w k).val‖ = 1 := G.orthonormal_L2.1 k
    have hle : ‖WkpU.toLp (G.w k).val‖ ≤ ‖(G.w k).val‖ := WkpU.norm_toLp_le _
    have h0 : ‖(G.w k).val‖ = 0 := by
      have hv : (G.w k).val = 0 := by rw [h]; exact Submodule.coe_zero
      rw [hv]; exact norm_zero
    rw [h1, h0] at hle
    linarith
  have horth : Orthonormal ℝ (fun k : ℕ => (‖G.w k‖)⁻¹ • G.w k) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [real_inner_smul_left, real_inner_smul_right]
    by_cases hij : i = j
    · subst hij
      have hi : ‖G.w i‖ ≠ 0 := (hne i).ne'
      rw [if_pos rfl, real_inner_self_eq_norm_sq]
      field_simp
    · rw [if_neg hij, G.orthogonal_H1 hij, mul_zero, mul_zero]
  intro hfd
  haveI := hfd
  exact Module.Finite.not_linearIndependent_of_infinite _ horth.linearIndependent

/-- Infinite dimesionality of Basis otherwise Galerkin approx fails (NEED TO CONSTRUCT GALERKIN BASIS IN SOBOLEV) -/
lemma galerkin_L2TH10U_infinite (G : GalerkinBasis d U hU) (T : ℝ) (hT : 0 < T) :
    ¬ FiniteDimensional ℝ (L2TH10U d U hU T) := by
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  haveI hnz : NeZero (volume.restrict (Set.Icc (0:ℝ) T)) := by
    refine ⟨fun h => ?_⟩
    have h0 : (volume.restrict (Set.Icc (0:ℝ) T)) Set.univ = 0 := by rw [h]; rfl
    rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_eq_zero] at h0
    linarith
  have hpos : (0:ℝ) <
      (volume.restrict (Set.Icc (0:ℝ) T)).real Set.univ ^ (1 / (2:ℝ≥0∞).toReal) := by
    apply Real.rpow_pos_of_pos
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
        ENNReal.toReal_ofReal hT.le]
    exact hT
  have hinj : Function.Injective
      (Lp.constₗ (2:ℝ≥0∞) (volume.restrict (Set.Icc (0:ℝ) T)) ℝ : H1U0 d U hU →ₗ[ℝ] _) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hc0 : Lp.const (2:ℝ≥0∞) (volume.restrict (Set.Icc (0:ℝ) T)) c = 0 := hc
    have hnorm := Lp.norm_const (2:ℝ≥0∞) (volume.restrict (Set.Icc (0:ℝ) T)) c
      (by norm_num)
    rw [hc0, norm_zero] at hnorm
    have hc_zero : ‖c‖ = 0 := by
      rcases mul_eq_zero.mp hnorm.symm with h | h
      · exact h
      · exact absurd h hpos.ne'
    exact norm_eq_zero.mp hc_zero
  intro hfd
  haveI := hfd
  exact galerkin_H1U0_infinite G (FiniteDimensional.of_injective _ hinj)

/-- dual is infinite dimensional -/
lemma galerkin_H1U0_dual_infinite (G : GalerkinBasis d U hU) :
    ¬ FiniteDimensional ℝ (H1U0_dual d U hU) := by
  have hne : ∀ k, (0:ℝ) < ‖G.w k‖ := by
    intro k
    rw [norm_pos_iff]
    intro h
    have h1 : ‖WkpU.toLp (G.w k).val‖ = 1 := G.orthonormal_L2.1 k
    have hle : ‖WkpU.toLp (G.w k).val‖ ≤ ‖(G.w k).val‖ := WkpU.norm_toLp_le _
    have h0 : ‖(G.w k).val‖ = 0 := by
      have hv : (G.w k).val = 0 := by rw [h]; exact Submodule.coe_zero
      rw [hv]; exact norm_zero
    rw [h1, h0] at hle
    linarith
  have horth : Orthonormal ℝ (fun k : ℕ => HkU0_riesz ((‖G.w k‖)⁻¹ • G.w k)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [HkU0_riesz_inner, real_inner_smul_left, real_inner_smul_right]
    by_cases hij : i = j
    · subst hij
      have hi : ‖G.w i‖ ≠ 0 := (hne i).ne'
      rw [if_pos rfl, real_inner_self_eq_norm_sq]
      field_simp
    · rw [if_neg hij, G.orthogonal_H1 hij, mul_zero, mul_zero]
  intro hfd
  haveI := hfd
  exact Module.Finite.not_linearIndependent_of_infinite _ horth.linearIndependent

/-- Bochner of galerkin dual infinite dimensional-/
lemma galerkin_L2TH10U_dual_infinite (G : GalerkinBasis d U hU) (T : ℝ) (hT : 0 < T) :
    ¬ FiniteDimensional ℝ (L2TH10U_dual d U hU T) := by
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  haveI hnz : NeZero (volume.restrict (Set.Icc (0:ℝ) T)) := by
    refine ⟨fun h => ?_⟩
    have h0 : (volume.restrict (Set.Icc (0:ℝ) T)) Set.univ = 0 := by rw [h]; rfl
    rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_eq_zero] at h0
    linarith
  have hpos : (0:ℝ) <
      (volume.restrict (Set.Icc (0:ℝ) T)).real Set.univ ^ (1 / (2:ℝ≥0∞).toReal) := by
    apply Real.rpow_pos_of_pos
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
        ENNReal.toReal_ofReal hT.le]
    exact hT
  have hinj : Function.Injective
      (Lp.constₗ (2:ℝ≥0∞) (volume.restrict (Set.Icc (0:ℝ) T)) ℝ : H1U0_dual d U hU →ₗ[ℝ] _) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hc0 : Lp.const (2:ℝ≥0∞) (volume.restrict (Set.Icc (0:ℝ) T)) c = 0 := hc
    have hnorm := Lp.norm_const (2:ℝ≥0∞) (volume.restrict (Set.Icc (0:ℝ) T)) c
      (by norm_num)
    rw [hc0, norm_zero] at hnorm
    have hc_zero : ‖c‖ = 0 := by
      rcases mul_eq_zero.mp hnorm.symm with h | h
      · exact h
      · exact absurd h hpos.ne'
    exact norm_eq_zero.mp hc_zero
  intro hfd
  haveI := hfd
  exact galerkin_H1U0_dual_infinite G (FiniteDimensional.of_injective _ hinj)

lemma H1U0_inclusion_Hinv_apply (a b : H1U0 d U hU) :
    (H1U0_inclusion_Hinv a) b = inner ℝ (WkpU.toLp a.val) (WkpU.toLp b.val) := rfl


lemma H1U0_inclusion_Hinv_comm (a b : H1U0 d U hU) :
    (H1U0_inclusion_Hinv a) b = (H1U0_inclusion_Hinv b) a := by
  rw [H1U0_inclusion_Hinv_apply, H1U0_inclusion_Hinv_apply, real_inner_comm]


attribute [local irreducible] H1U0_inclusion_Hinv

/-- norm bridges Proved only through the
apply lemmas (never unfolding the cursed type), so it stays clear of the
heartbeat tree. -/
lemma hinv_incl_norm (a : H1U0 d U hU) :
    ‖H1U0_inclusion_Hinv a‖ = hinvNormOfH1 a := by
  have h : H1U0_inclusion_Hinv a = L2ToHinvCLM (WkpU.toLp a.val) := by
    ext b
    rw [H1U0_inclusion_Hinv_apply, L2ToHinvCLM_apply]
  rw [h, hinvNormOfH1]

/-- `u'approx` is `MemLp 2` on `[0,T]` (continuous ⟹ bounded on the compact interval).  Named so
`u'approxLift_coeFn` can reference the exact `toLp`. -/
lemma u'approx_memLp (G : GalerkinBasis d U hU) (T : ℝ) {m : ℕ}
    (dCoeffs : Fin m → ℝ → ℝ) (h_C1 : ∀ k, ContDiff ℝ 1 (dCoeffs k)) :
    MemLp (fun t => u'approx G dCoeffs t) 2 (volume.restrict (Set.Icc (0:ℝ) T)) := by
  have h_deriv_cont : ∀ k, Continuous (deriv (dCoeffs k)) := fun k =>
    (h_C1 k).continuous_deriv_one
  have h_u'approx_cont : Continuous (fun t => u'approx G dCoeffs t) := by
    unfold u'approx
    exact continuous_finsetSum _ (fun k _ => (h_deriv_cont k).smul continuous_const)
  have h_bdd_above :
      BddAbove ((fun t => ‖u'approx G dCoeffs t‖) '' Set.Icc (0:ℝ) T) :=
    (isCompact_Icc.image_of_continuousOn h_u'approx_cont.norm.continuousOn).bddAbove
  obtain ⟨C, hC⟩ := h_bdd_above
  have h_ae_bound :
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)), ‖u'approx G dCoeffs t‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards with t ht
    exact hC ⟨t, ht, rfl⟩
  have h_aesm :
      AEStronglyMeasurable (fun t => u'approx G dCoeffs t)
        (volume.restrict (Set.Icc (0:ℝ) T)) := by
    haveI : SecondCountableTopologyEither ℝ (H1U0 d U hU) := ⟨Or.inl inferInstance⟩
    exact h_u'approx_cont.aestronglyMeasurable
  exact MemLp.of_bound h_aesm C h_ae_bound

/-- The `u'approxLift` coerces to the pointwise Gelfand image `t ↦ H1U0_inclusion_Hinv (u'ₘ t)`. -/
lemma u'approxLift_coeFn (G : GalerkinBasis d U hU) (T : ℝ) {m : ℕ}
    (dCoeffs : Fin m → ℝ → ℝ) (h_C1 : ∀ k, ContDiff ℝ 1 (dCoeffs k)) :
    (u'approxLift G T dCoeffs h_C1)
      =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)]
      fun t => H1U0_inclusion_Hinv (u'approx G dCoeffs t) := by
  unfold u'approxLift
  dsimp only
  refine (ContinuousLinearMap.coeFn_compLp' H1U0_inclusion_Hinv _).trans ?_
  filter_upwards [MemLp.coeFn_toLp (u'approx_memLp G T dCoeffs h_C1)] with t ht
  exact congrArg (fun x => H1U0_inclusion_Hinv x) ht

set_option maxHeartbeats 800000 in
/-- `‖u'approxLift‖²_{L²(0,T;H⁻¹)} = ∫₀ᵀ hinvNormOfH1(u'ₘ(t))²` — the identity E2 bounds. -/
lemma u'approxLift_norm_sq (G : GalerkinBasis d U hU) (T : ℝ) {m : ℕ}
    (dCoeffs : Fin m → ℝ → ℝ) (h_C1 : ∀ k, ContDiff ℝ 1 (dCoeffs k)) :
    ‖u'approxLift G T dCoeffs h_C1‖ ^ 2
      = ∫ t in Set.Icc (0:ℝ) T, hinvNormOfH1 (u'approx G dCoeffs t) ^ 2 := by
  rw [L2TH10U_dual_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [u'approxLift_coeFn G T dCoeffs h_C1] with t ht
  rw [ht, hinv_incl_norm]

/-- u'approx = weak derivative of u -/
lemma galerkin_approx_isWeakTimeDeriv (G : GalerkinBasis d U hU) (T : ℝ) (hT : 0 ≤ T) {m : ℕ}
    (dCoeffs : Fin m → ℝ → ℝ) (h_C1 : ∀ k, ContDiff ℝ 1 (dCoeffs k)) :
    IsWeakTimeDeriv T (uapproxLift G T dCoeffs (fun k => (h_C1 k).continuous))
      (u'approxLift G T dCoeffs h_C1) := by
  intro v φ hφ
  obtain ⟨hφC1, hφsupp, hφsub⟩ := hφ
  set A : ℝ → ℝ := fun t => ∑ k : Fin m,
    dCoeffs k t * inner ℝ (WkpU.toLp (G.w (k : ℕ)).val) (WkpU.toLp v.val) with hA
  set B : ℝ → ℝ := fun t => ∑ k : Fin m,
    deriv (dCoeffs k) t * inner ℝ (WkpU.toLp (G.w (k : ℕ)).val) (WkpU.toLp v.val) with hB
  -- The two pairings against `v` are `A` and `B`.
  have ha : ∀ t, inner ℝ (WkpU.toLp (uapprox G dCoeffs t).val) (WkpU.toLp v.val) = A t :=
    fun t => by
      show inner ℝ (WkpU.toLp (uapprox G dCoeffs t).val) (WkpU.toLp v.val)
        = ∑ k : Fin m, dCoeffs k t * inner ℝ (WkpU.toLp (G.w (k : ℕ)).val) (WkpU.toLp v.val)
      unfold uapprox; rw [galerkin_combo_toLp, sum_inner]
      exact Finset.sum_congr rfl (fun k _ => by rw [real_inner_smul_left])
  have hb : ∀ t, inner ℝ (WkpU.toLp (u'approx G dCoeffs t).val) (WkpU.toLp v.val) = B t :=
    fun t => by
      show inner ℝ (WkpU.toLp (u'approx G dCoeffs t).val) (WkpU.toLp v.val)
        = ∑ k : Fin m, deriv (dCoeffs k) t *
            inner ℝ (WkpU.toLp (G.w (k : ℕ)).val) (WkpU.toLp v.val)
      unfold u'approx; rw [galerkin_combo_toLp, sum_inner]
      exact Finset.sum_congr rfl (fun k _ => by rw [real_inner_smul_left])
  -- `A` is `C¹` with `A' = B`; `B`, `φ`, `φ'` are continuous.
  have hAderiv : ∀ t, HasDerivAt A (B t) t := by
    intro t
    have hAeq : A = ∑ k : Fin m,
        (fun z => dCoeffs k z * inner ℝ (WkpU.toLp (G.w (k : ℕ)).val) (WkpU.toLp v.val)) := by
      funext y; simp only [hA, Finset.sum_apply]
    rw [hAeq]
    exact HasDerivAt.sum (fun k _ =>
      (((h_C1 k).differentiable (by norm_num)).differentiableAt.hasDerivAt).mul_const _)
  have hBcont : Continuous B :=
    continuous_finsetSum _ (fun k _ =>
      ((h_C1 k).continuous_deriv_one).mul continuous_const)
  have hφderiv : ∀ x, HasDerivAt φ (deriv φ x) x :=
    fun x => (hφC1.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hφ'cont : Continuous (deriv φ) := hφC1.continuous_deriv_one
  -- `φ` vanishes at the endpoints (outside `Ioo 0 T`, hence outside `tsupport`).
  have hφ0 : φ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => absurd (hφsub h).1 (lt_irrefl 0))
  have hφT : φ T = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => absurd (hφsub h).2 (lt_irrefl T))
  -- Rewrite both integrals to the scalar `A`, `B`.
  have hLHS : (∫ t in Set.Icc (0:ℝ) T, deriv φ t *
        ((H1U0_inclusion_Hinv ((uapproxLift G T dCoeffs (fun k => (h_C1 k).continuous)) t)) v))
      = ∫ t in Set.Icc (0:ℝ) T, deriv φ t * A t := by
    refine integral_congr_ae ?_
    filter_upwards [uapproxLift_coeFn G T dCoeffs (fun k => (h_C1 k).continuous)] with t ht
    rw [ht, H1U0_inclusion_Hinv_apply, ha t]
  have hRHS : (∫ t in Set.Icc (0:ℝ) T, φ t * ((u'approxLift G T dCoeffs h_C1 t) v))
      = ∫ t in Set.Icc (0:ℝ) T, φ t * B t := by
    refine integral_congr_ae ?_
    filter_upwards [u'approxLift_coeFn G T dCoeffs h_C1] with t ht
    rw [ht, H1U0_inclusion_Hinv_apply, hb t]
  rw [hLHS, hRHS]
  -- Scalar integration by parts on `[0,T]`.
  have hconv : ∀ g : ℝ → ℝ, (∫ t in Set.Icc (0:ℝ) T, g t) = ∫ t in (0:ℝ)..T, g t := fun g => by
    rw [intervalIntegral.integral_of_le hT, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hconv, hconv]
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hφderiv x) (fun x _ => hAderiv x)
    (hφ'cont.intervalIntegrable 0 T) (hBcont.intervalIntegrable 0 T)
  rw [hφ0, hφT] at hibp
  simp only [zero_mul, sub_zero, zero_sub] at hibp
  linarith [hibp]


lemma clm_tendsto_of_tendsto_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Λ : E →L[ℝ] ℝ) {xseq : ℕ → E} {x : E}
    (hweak : ∀ ψ : E, Tendsto (fun n => inner ℝ (xseq n) ψ) atTop (𝓝 (inner ℝ x ψ))) :
    Tendsto (fun n => Λ (xseq n)) atTop (𝓝 (Λ x)) := by
  set ψ : E := LinearIsometryEquiv.symm (InnerProductSpace.toDual ℝ E) Λ with hψ
  have hΛ : ∀ y : E, Λ y = inner ℝ y ψ := by
    intro y
    rw [hψ, real_inner_comm]
    exact Eq.symm InnerProductSpace.toDual_symm_apply
  simp_rw [hΛ]
  exact hweak ψ

/-- If `Λ (xₙ) = bₙ → c` and `xₙ ⇀ x` weakly, then `Λ x = c`.  Abstract (no deep types), so it
absorbs the weak-limit uniqueness step without any heartbeat risk. -/
lemma weak_limit_eq_of_clm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Λ : E →L[ℝ] ℝ) {xseq : ℕ → E} {x : E} {b : ℕ → ℝ} {c : ℝ}
    (hweak : ∀ ψ : E, Tendsto (fun n => inner ℝ (xseq n) ψ) atTop (𝓝 (inner ℝ x ψ)))
    (hb : Tendsto b atTop (𝓝 c)) (hkey : ∀ n, Λ (xseq n) = b n) :
    Λ x = c :=
  tendsto_nhds_unique (clm_tendsto_of_tendsto_inner Λ hweak)
    (Filter.Tendsto.congr (fun n => Eq.symm (hkey n)) hb)


lemma gelfand_pairing_clm_apply {T : ℝ} (v : H1U0 d U hU)
    (g : Lp ℝ 2 (volume.restrict (Set.Icc (0:ℝ) T))) (gfun : ℝ → ℝ)
    (hg : g =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)] gfun) (x : L2TH10U d U hU T) :
    ContinuousLinearMap.comp (innerSL ℝ g)
        (ContinuousLinearMap.compLpL 2 (volume.restrict (Set.Icc (0:ℝ) T))
          (H1U0_inclusion_Hinv v)) x
      = ∫ t in Set.Icc (0:ℝ) T, gfun t * ((H1U0_inclusion_Hinv (x t)) v) := by

  conv_lhs =>
    rw [ContinuousLinearMap.comp_apply]
    simp only [coe_innerSL_apply]
    rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg, ContinuousLinearMap.coeFn_compLpL (H1U0_inclusion_Hinv v) x]
    with t ht1 ht2

  exact Eq.trans (Real.inner_apply _ _)
    (congrArg₂ (· * ·) ht1 (Eq.trans ht2 (H1U0_inclusion_Hinv_comm v (x t))))

set_option maxHeartbeats 4000000 in

lemma isWeakTimeDeriv_of_weak_limits {T : ℝ}
    {Useq : ℕ → L2TH10U d U hU T} {Wseq : ℕ → L2TH10U_dual d U hU T}
    {u : L2TH10U d U hU T} {w : L2TH10U_dual d U hU T}
    (hpair : ∀ n, IsWeakTimeDeriv T (Useq n) (Wseq n))
    (hu : ∀ ψ : L2TH10U d U hU T,
      Tendsto (fun n => inner ℝ (Useq n) ψ) atTop (𝓝 (inner ℝ u ψ)))
    (hw : ∀ ψ : L2TH10U d U hU T,
      Tendsto (fun n => ∫ t in Set.Icc (0:ℝ) T, (Wseq n t) (ψ t)) atTop
        (𝓝 (∫ t in Set.Icc (0:ℝ) T, (w t) (ψ t)))) :
    IsWeakTimeDeriv T u w := by
  intro v φ hφ
  obtain ⟨hφ_C1, hφ_supp, hφ_sub⟩ := hφ
  -- (A) `deriv φ` as an `L²(0,T)` element and `Vφ := (t ↦ φ t • v)` as an `L²(0,T;H¹₀)` element.

  have hderiv_cont : Continuous (deriv φ) := ContDiff.continuous_deriv_one hφ_C1
  have hderiv_supp : HasCompactSupport (deriv φ) := HasCompactSupport.deriv hφ_supp
  have hVφ_cont : Continuous (fun t : ℝ => φ t • v) :=
    Continuous.smul (ContDiff.continuous hφ_C1) continuous_const
  have hVφ_supp : HasCompactSupport (fun t : ℝ => φ t • v) :=
    HasCompactSupport.comp_left (g := fun s : ℝ => s • v) hφ_supp (zero_smul ℝ v)
  have hderiv_mem : MemLp (deriv φ) 2 (volume.restrict (Set.Icc (0:ℝ) T)) :=
    Continuous.memLp_of_hasCompactSupport hderiv_cont hderiv_supp
  have hVφ_mem : MemLp (fun t : ℝ => φ t • v) 2 (volume.restrict (Set.Icc (0:ℝ) T)) :=
    Continuous.memLp_of_hasCompactSupport hVφ_cont hVφ_supp
  -- `let` (not `set`): `set` runs `kabstract` over the goal, which holds the deep
  -- `H1U0_inclusion_Hinv (u t) v` and is ruinously expensive to scan; `let` just binds.
  let φ'Lp : Lp ℝ 2 (volume.restrict (Set.Icc (0:ℝ) T)) := MemLp.toLp (deriv φ) hderiv_mem
  let Vφ : L2TH10U d U hU T := MemLp.toLp (fun t : ℝ => φ t • v) hVφ_mem
  have hφ'_ae : φ'Lp =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)] deriv φ := MemLp.coeFn_toLp hderiv_mem
  have hVφ_ae : Vφ =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)] fun t : ℝ => φ t • v :=
    MemLp.coeFn_toLp hVφ_mem
  -- (B) RHS rewrite: `∫ (W t)(Vφ t) = ∫ φ(t)·(W t v)`.
  have hVφ_rhs : ∀ (W : L2TH10U_dual d U hU T),
      (∫ t in Set.Icc (0:ℝ) T, (W t) (Vφ t))
        = ∫ t in Set.Icc (0:ℝ) T, φ t * ((W t) v) := by
    intro W
    refine integral_congr_ae ?_
    filter_upwards [hVφ_ae] with t ht
    rw [ht, map_smul, smul_eq_mul]
  -- (C) LHS functional bundled as a CLM via `compLpL`/`innerSL`.
  let Λ : L2TH10U d U hU T →L[ℝ] ℝ :=
    ContinuousLinearMap.comp (innerSL ℝ φ'Lp)
      (ContinuousLinearMap.compLpL 2 (volume.restrict (Set.Icc (0:ℝ) T))
        (H1U0_inclusion_Hinv v))
  have hΛ_eq : ∀ x : L2TH10U d U hU T,
      Λ x = ∫ t in Set.Icc (0:ℝ) T, deriv φ t * ((H1U0_inclusion_Hinv (x t)) v) := fun x =>
    gelfand_pairing_clm_apply v φ'Lp (deriv φ) hφ'_ae x
  -- (D) Per-`n` IBP identity, as an explicit term.
  have hkey : ∀ n, Λ (Useq n) = - ∫ t in Set.Icc (0:ℝ) T, (Wseq n t) (Vφ t) := fun n =>
    Eq.trans (hΛ_eq (Useq n))
      (Eq.trans (hpair n v φ ⟨hφ_C1, hφ_supp, hφ_sub⟩)
        (congrArg Neg.neg (Eq.symm (hVφ_rhs (Wseq n)))))
  -- (E) Identify limits via the abstract lemma, then assemble as an explicit term.
  have hΛu : Λ u = - ∫ t in Set.Icc (0:ℝ) T, (w t) (Vφ t) :=
    weak_limit_eq_of_clm Λ hu (Filter.Tendsto.neg (hw Vφ)) hkey
  exact Eq.trans (Eq.symm (hΛ_eq u)) (Eq.trans hΛu (congrArg Neg.neg (hVφ_rhs w)))


set_option maxHeartbeats 1000000 in
/-- Extract weakly convergent subsequence using our HK lemma for um -/
lemma galerkin_uapprox_weak_subseq
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ)
    (hP_bdd : ∀ t, (P t).IsBounded M)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U))
    (dCoeffsSeq : (m : ℕ) → Fin m → ℝ → ℝ)
    (h_galerkin : ∀ m, GalerkinODE G P T f g (dCoeffsSeq m))
    (h_C1 : ∀ m k, ContDiff ℝ 1 (dCoeffsSeq m k)) :
    ∃ (subseq : ℕ → ℕ), StrictMono subseq ∧
    ∃ (u : L2TH10U d U hU T),
      (∀ ψ : L2TH10U d U hU T,
        Tendsto
          (fun k => inner ℝ
                      (uapproxLift G T (dCoeffsSeq (subseq k))
                        (fun n => (h_C1 (subseq k) n).continuous)) ψ)
          atTop
          (𝓝 (inner ℝ u ψ))) := by
  obtain ⟨C₂, hC₂nn, hC₂⟩ := galerkin_bound_H1_integral hθ hMpos G P T hT hP_para hP_bdd
  have hbdd : ∀ m, ‖uapproxLift G T (dCoeffsSeq m) (fun n => (h_C1 m n).continuous)‖
      ≤ Real.sqrt (C₂ * (‖f‖ ^ 2 + ‖g‖ ^ 2)) := by
    intro m
    have hsq : ‖uapproxLift G T (dCoeffsSeq m) (fun n => (h_C1 m n).continuous)‖ ^ 2
        ≤ C₂ * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
      rw [uapproxLift_norm_sq]
      exact hC₂ f g (dCoeffsSeq m) (h_C1 m) (h_galerkin m)
    calc ‖uapproxLift G T (dCoeffsSeq m) (fun n => (h_C1 m n).continuous)‖
        = Real.sqrt (‖uapproxLift G T (dCoeffsSeq m) (fun n => (h_C1 m n).continuous)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (C₂ * (‖f‖ ^ 2 + ‖g‖ ^ 2)) := Real.sqrt_le_sqrt hsq
  obtain ⟨subseq, u, hmono, hconv⟩ :=
    bounded_seq_weak_subseq_in_hilbert (galerkin_L2TH10U_infinite G T hT) hbdd
  exact ⟨subseq, hmono, u, hconv⟩

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- same for u'm -/
lemma galerkin_uprime_weak_subseq
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ)
    (hP_bdd : ∀ t, (P t).IsBounded M)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U))
    (dCoeffsSeq : (m : ℕ) → Fin m → ℝ → ℝ)
    (h_galerkin : ∀ m, GalerkinODE G P T f g (dCoeffsSeq m))
    (h_C1 : ∀ m k, ContDiff ℝ 1 (dCoeffsSeq m k)) :
    ∃ (subseq : ℕ → ℕ), StrictMono subseq ∧
    ∃ (w : L2TH10U_dual d U hU T),
      (∀ φ : L2TH10U_dual d U hU T,
        Tendsto
          (fun k => inner ℝ (u'approxLift G T (dCoeffsSeq (subseq k)) (h_C1 (subseq k))) φ)
          atTop
          (𝓝 (inner ℝ w φ))) := by
  obtain ⟨C₃, hC₃nn, hC₃⟩ := galerkin_bound_Hinv_integral hθ hMpos G P T hT hP_para hP_bdd
  have hbdd : ∀ m, ‖u'approxLift G T (dCoeffsSeq m) (h_C1 m)‖
      ≤ Real.sqrt (C₃ * (‖f‖ ^ 2 + ‖g‖ ^ 2)) := by
    intro m
    have hsq : ‖u'approxLift G T (dCoeffsSeq m) (h_C1 m)‖ ^ 2
        ≤ C₃ * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
      rw [u'approxLift_norm_sq]
      exact hC₃ f g (dCoeffsSeq m) (h_C1 m) (h_galerkin m)
    calc ‖u'approxLift G T (dCoeffsSeq m) (h_C1 m)‖
        = Real.sqrt (‖u'approxLift G T (dCoeffsSeq m) (h_C1 m)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (C₃ * (‖f‖ ^ 2 + ‖g‖ ^ 2)) := Real.sqrt_le_sqrt hsq
  obtain ⟨subseq, w, hmono, hconv⟩ :=
    bounded_seq_weak_subseq_in_hilbert (galerkin_L2TH10U_dual_infinite G T hT) hbdd
  exact ⟨subseq, hmono, w, hconv⟩

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Disgusting gelfand bridge and full extraction here -/
lemma gelfand_bridge {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U} {T : ℝ}
    (v : L2TH10U d U hU T) :
    ∃ φ : L2TH10U_dual d U hU T, ∀ F : L2TH10U_dual d U hU T,
      (inner ℝ F φ : ℝ) = ∫ t in Set.Icc (0:ℝ) T, (F t) (v t) := by
  refine ⟨(HkU0_riesz.toLinearIsometry.toContinuousLinearMap).compLp v, ?_⟩
  intro F
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLp'
    (HkU0_riesz.toLinearIsometry.toContinuousLinearMap) v] with t ht
  rw [ht]
  exact dual_inner_riesz (F t) (v t)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma galerkin_seq_extract_limits
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ)
    (hP_bdd : ∀ t, (P t).IsBounded M)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U))
    (dCoeffsSeq : (m : ℕ) → Fin m → ℝ → ℝ)
    (h_galerkin : ∀ m, GalerkinODE G P T f g (dCoeffsSeq m))
    (h_C1 : ∀ m k, ContDiff ℝ 1 (dCoeffsSeq m k)) :
    ∃ (subseq : ℕ → ℕ), StrictMono subseq ∧
    ∃ (u : L2TH10U d U hU T) (w : L2TH10U_dual d U hU T),
      -- u_m → u weakly in L²(0,T; H¹₀): Hilbert weak convergence
      (∀ ψ : L2TH10U d U hU T,
        Tendsto
          (fun k => inner ℝ
                      (uapproxLift G T (dCoeffsSeq (subseq k))
                        (fun n => (h_C1 (subseq k) n).continuous)) ψ)
          atTop
          (𝓝 (inner ℝ u ψ)))
      ∧
      -- u'_m → w weakly in L²(0,T; H⁻¹): Gelfand-triple pairing against L²H¹₀
      (∀ v : L2TH10U d U hU T,
        Tendsto
          (fun k =>
            ∫ t in Set.Icc (0:ℝ) T,
              (u'approxLift G T (dCoeffsSeq (subseq k)) (h_C1 (subseq k)) t) (v t))
          atTop
          (𝓝 (∫ t in Set.Icc (0:ℝ) T, (w t) (v t)))) := by
  -- First extraction: `uₘ → u` weakly in `L²(0,T;H¹₀)` along a subsequence `s1`.
  obtain ⟨s1, hs1mono, u, hconv1⟩ :=
    galerkin_uapprox_weak_subseq G P T hT hθ hMpos hP_para hP_bdd f g dCoeffsSeq h_galerkin h_C1
  -- Uniform E2 bound on `u'ₘ`, so we can extract from the `s1`-reindexed sequence.
  obtain ⟨C₃, hC₃nn, hC₃⟩ := galerkin_bound_Hinv_integral hθ hMpos G P T hT hP_para hP_bdd
  have hby : ∀ m, ‖u'approxLift G T (dCoeffsSeq m) (h_C1 m)‖
      ≤ Real.sqrt (C₃ * (‖f‖ ^ 2 + ‖g‖ ^ 2)) := by
    intro m
    have hsq : ‖u'approxLift G T (dCoeffsSeq m) (h_C1 m)‖ ^ 2
        ≤ C₃ * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
      rw [u'approxLift_norm_sq]
      exact hC₃ f g (dCoeffsSeq m) (h_C1 m) (h_galerkin m)
    calc ‖u'approxLift G T (dCoeffsSeq m) (h_C1 m)‖
        = Real.sqrt (‖u'approxLift G T (dCoeffsSeq m) (h_C1 m)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (C₃ * (‖f‖ ^ 2 + ‖g‖ ^ 2)) := Real.sqrt_le_sqrt hsq
  -- Second extraction: `u'ₘ → w` weakly in `L²(0,T;H⁻¹)` along a further subsequence `s2` of `s1`.
  obtain ⟨s2, w, hs2mono, hconv2⟩ :=
    bounded_seq_weak_subseq_in_hilbert (galerkin_L2TH10U_dual_infinite G T hT)
      (fun k => hby (s1 k))
  refine ⟨s1 ∘ s2, hs1mono.comp hs2mono, u, w, ?_, ?_⟩
  · -- `uₘ → u` along `s1 ∘ s2` (subsequence of a weakly convergent sequence).
    intro ψ
    exact (hconv1 ψ).comp hs2mono.tendsto_atTop
  · -- `u'ₘ → w` in the Gelfand pairing, via the Riesz bridge.
    intro v
    obtain ⟨φ, hφ⟩ := gelfand_bridge v
    have hc := hconv2 φ
    simp only [hφ] at hc
    exact hc


/-- The `L²`-orthogonal projection fixes each basis vector: `galerkinProj G m (wₖ) = wₖ` for
`k : Fin m` (the `wⱼ` are `L²`-orthonormal). -/
lemma galerkinProj_basis (G : GalerkinBasis d U hU) {m : ℕ} (k : Fin m) :
    galerkinProj G m (G.w (k : ℕ)) = G.w (k : ℕ) := by
  have hcoef : ∀ j : Fin m,
      (inner ℝ (WkpU.toLp (G.w (k : ℕ)).val) (WkpU.toLp (G.w (j : ℕ)).val) : ℝ)
        = if (k : ℕ) = (j : ℕ) then 1 else 0 :=
    fun j => orthonormal_iff_ite.mp G.orthonormal_L2 (k : ℕ) (j : ℕ)
  unfold galerkinProj
  rw [Finset.sum_eq_single k
    (fun j _ hjk => by
      rw [hcoef j,
        if_neg (show ¬((k : ℕ) = (j : ℕ)) from fun h => hjk (Fin.val_injective h).symm),
        zero_smul])
    (fun hk => absurd (Finset.mem_univ k) hk)]
  rw [hcoef k, if_pos rfl, one_smul]

/-- Galerkin identity for basis functions (pairing form).For a solution of the finite
Galerkin ODE, the `L²`-pairing of `u'ₘ` against a basis vector `wₖ` (`k < m`) plus the bilinear
form recovers the forcing, a.e. in `t`. -/
lemma galerkin_basis_identity
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) {M : ℝ}
    (hP_bdd : ∀ t, (P t).IsBounded M)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U))
    {m : ℕ} (dCoeffs : Fin m → ℝ → ℝ) (hODE : GalerkinODE G P T f g dCoeffs) (k : Fin m) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
      inner ℝ (WkpU.toLp (u'approx G dCoeffs t).val) (WkpU.toLp (G.w (k : ℕ)).val)
        + parabilinform (P t) (uapprox G dCoeffs t) (G.w (k : ℕ))
        = inner ℝ (f t) (WkpU.toLp (G.w (k : ℕ)).val) := by
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)), ∀ j : Fin m,
      deriv (dCoeffs j) t
        + ∑ i : Fin m, dCoeffs i t * parabilinform (P t) (G.w (i : ℕ)) (G.w (j : ℕ))
        = inner ℝ (f t) (WkpU.toLp (G.w (j : ℕ)).val) :=
    ae_all_iff.2 hODE.1
  filter_upwards [hae] with t ht
  have hp := galerkin_uprime_pairing G (P t) (hP_bdd t) dCoeffs t (f t) ht (G.w (k : ℕ))
  rw [galerkinProj_basis G k] at hp
  linarith [hp]

/-- The bilinear form `parabilinform (P)(u) ·`, as a **continuous linear functional** on `H¹₀`
in its second argument (linear by `parabilinform_add_right`/`_smul_right`, bounded by
`parabilinform_bound`).  Used to build the defect functional in the density argument. -/
noncomputable def parabilinform_clm {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (P : ParabolicCoeffs d) {M : ℝ} (hP_bdd : P.IsBounded M) (u : H1U0 d U hU) :
    H1U0 d U hU →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => parabilinform P u v
      map_add' := parabilinform_add_right (P := P) hP_bdd u
      map_smul' := fun k v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact parabilinform_smul_right (P := P) k u v }
    (M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖u‖)
    (fun v => by
      rw [Real.norm_eq_abs]
      exact parabilinform_bound (P := P) M hP_bdd u v)

@[simp] lemma parabilinform_clm_apply {d : ℕ+} {U : Set (Fin d → ℝ)} {hU : IsOpen U}
    (P : ParabolicCoeffs d) {M : ℝ} (hP_bdd : P.IsBounded M) (u v : H1U0 d U hU) :
    parabilinform_clm P hP_bdd u v = parabilinform P u v := rfl

/-- Density extension If the weak identity holds
against every Galerkin basis function `wₖ` (a.e. in `t`), then it holds against *every* `v ∈ H¹₀`:
for a.e.  -/
lemma weaksol_of_basis
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) {M : ℝ}
    (hP_bdd : ∀ t, (P t).IsBounded M)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U))
    (u : L2TH10U d U hU T) (u' : L2TH10U_dual d U hU T)
    (hbasis : ∀ k : ℕ, ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
      (u' t) (G.w k) + parabilinform (P t) (u t) (G.w k)
        = inner ℝ (f t) (WkpU.toLp (G.w k).val)) :
    ∀ (v : H1U0 d U hU), ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
      (u' t) v + parabilinform (P t) (u t) v = inner ℝ (f t) (WkpU.toLp v.val) := by
  intro v
  filter_upwards [ae_all_iff.2 hbasis] with t ht
  -- Defect functional `Λ = u'(t) + B(t)[u(t),·] − L2ToHinvCLM (f t)`.
  set Λ : H1U0 d U hU →L[ℝ] ℝ :=
    (u' t) + parabilinform_clm (P t) (hP_bdd t) (u t) - L2ToHinvCLM (f t) with hΛ
  have hΛapply : ∀ x : H1U0 d U hU,
      Λ x = (u' t) x + parabilinform (P t) (u t) x - inner ℝ (f t) (WkpU.toLp x.val) := by
    intro x
    rw [hΛ]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      parabilinform_clm_apply, L2ToHinvCLM_apply]
  -- `Λ` vanishes on every basis vector, hence on `span (range w) ≤ ker Λ`.
  have hker : Submodule.span ℝ (Set.range G.w)
      ≤ LinearMap.ker (Λ : H1U0 d U hU →ₗ[ℝ] ℝ) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    rw [hΛapply]
    linarith [ht k]
  -- `ker Λ` is closed, so it contains the closure of the span, which is `⊤`.
  have htop : (Submodule.span ℝ (Set.range G.w)).topologicalClosure
      ≤ LinearMap.ker (Λ : H1U0 d U hU →ₗ[ℝ] ℝ) :=
    Submodule.topologicalClosure_minimal (Submodule.span ℝ (Set.range G.w)) hker
      (ContinuousLinearMap.isClosed_ker Λ)
  rw [G.dense_H1] at htop
  have hv : Λ v = 0 := by
    have hmem : v ∈ LinearMap.ker (Λ : H1U0 d U hU →ₗ[ℝ] ℝ) := htop Submodule.mem_top
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hmem
    exact hmem
  rw [hΛapply] at hv
  linarith [hv]

/-- **(Fielded analytic lemma) Fundamental lemma of the calculus of variations on `[0,T]`.**  A
locally integrable `h` whose integral against every `C¹` bump supported in `(0,T)` vanishes is
zero a.e.  This is Mathlib's `ae_eq_zero_of_integral_contDiff_smul_eq_zero` transported to the
restricted measure on `[0,T]`; the `C¹`-vs-`C∞` and boundary bookkeeping is the reason it is
fielded here. -/
lemma fundamental_lemma_cov {T : ℝ} (h : ℝ → ℝ)
    (hint : IntegrableOn h (Set.Icc (0:ℝ) T))
    (H : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Set.Ioo 0 T →
      ∫ t in Set.Icc (0:ℝ) T, φ t * h t = 0) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)), h t = 0 := by
  -- `h = 0` a.e. on the open interior `Ioo 0 T` (Mathlib's fundamental lemma on open sets; the
  -- `C¹` test functions of `H` include all `C∞` ones).
  have hres : ∀ᵐ x ∂(volume.restrict (Set.Icc (0:ℝ) T)), x ∈ Set.Ioo (0:ℝ) T → h x = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hint.locallyIntegrable.locallyIntegrableOn _) ?_
    intro g g_diff g_supp g_tsupp
    simpa only [smul_eq_mul] using H g (g_diff.of_le (by norm_num)) g_supp g_tsupp
  -- a.e. point of `Icc 0 T` lies in `Ioo 0 T` (the boundary `{0,T}` is null).
  have haeIoo : ∀ᵐ x ∂(volume.restrict (Set.Icc (0:ℝ) T)), x ∈ Set.Ioo (0:ℝ) T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [Ioo_ae_eq_Icc (a := (0:ℝ)) (b := T)] with x hx hxIcc
    exact (iff_of_eq hx).mpr hxIcc
  filter_upwards [hres, haeIoo] with x h1 h2
  exact h1 h2

/-- On a real Hilbert space a continuous linear functional is sequentially weakly continuous:
if `xₙ ⇀ a` weakly (`⟪xₙ, ψ⟫ → ⟪a, ψ⟫` for all `ψ`), then `Ψ xₙ → Ψ a`.  Proof: Riesz-represent
`Ψ` and test the weak convergence against the representative.  Kept abstract over `E` so
`InnerProductSpace.toDual` stays cheap (instantiating at concrete Bochner spaces is done later). -/
lemma clm_tendsto_of_weak {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (Ψ : E →L[ℝ] ℝ) {x : ℕ → E} {a : E}
    (h : ∀ ψ : E, Tendsto (fun n => inner ℝ (x n) ψ) atTop (𝓝 (inner ℝ a ψ))) :
    Tendsto (fun n => Ψ (x n)) atTop (𝓝 (Ψ a)) := by
  have key : ∀ z : E, Ψ z = inner ℝ z ((InnerProductSpace.toDual ℝ E).symm Ψ) := fun z => by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simp only [key]
  exact h ((InnerProductSpace.toDual ℝ E).symm Ψ)

/-- Finiteness of the restricted time measure on `[0,T]`. -/
instance isFiniteMeasure_restrict_Icc {T : ℝ} :
    IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) T)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩

/-- Under the `L^∞`-coefficient (measurability) hypothesis, `t ↦ φ(t)·B(t)[z(t),w₀]` is integrable
on `[0,T]`: `φ` is bounded and `B(t)[z(t),w₀]` is dominated by the `L¹` function `‖z(t)‖`
(Bochner integrability of an `L²` element on a finite measure). -/
lemma parabilinform_time_integrable {T M : ℝ}
    (P : ℝ → ParabolicCoeffs d) (hP_bdd : ∀ t, (P t).IsBounded M)
    (z : L2TH10U d U hU T) (w0 : H1U0 d U hU) (φ : ℝ → ℝ)
    (hφm : Measurable φ) (C : ℝ) (hφb : ∀ t, |φ t| ≤ C)
    (hmeas : AEStronglyMeasurable (fun t => parabilinform (P t) (z t) w0)
      (volume.restrict (Set.Icc (0:ℝ) T))) :
    IntegrableOn (fun t => φ t * parabilinform (P t) (z t) w0) (Set.Icc (0:ℝ) T) := by
  have hz_int : Integrable (fun t => ‖z t‖) (volume.restrict (Set.Icc (0:ℝ) T)) :=
    ((MeasureTheory.Lp.memLp z).integrable (by norm_num)).norm
  have hg_int : Integrable (fun t => parabilinform (P t) (z t) w0)
      (volume.restrict (Set.Icc (0:ℝ) T)) := by
    refine Integrable.mono' (hz_int.const_mul (M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖w0‖)) hmeas ?_
    filter_upwards with t
    rw [Real.norm_eq_abs]
    calc |parabilinform (P t) (z t) w0|
        ≤ M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖z t‖ * ‖w0‖ :=
          parabilinform_bound (P := P t) M (hP_bdd t) (z t) w0
      _ = M * ((d : ℝ) ^ 2 + (d : ℝ) + 1) * ‖w0‖ * ‖z t‖ := by ring
  refine Integrable.mono' (hg_int.norm.const_mul C)
    (hφm.aestronglyMeasurable.mul hg_int.aestronglyMeasurable) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hφb t) (abs_nonneg _)

/-- int(f*g) = 0 and f not 0, implies g = 0 a.e.-/
lemma dominated_time_integrable {T : ℝ} (φ h g : ℝ → ℝ) (C : ℝ)
    (hφm : Measurable φ) (hφb : ∀ t, |φ t| ≤ C)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Set.Icc (0:ℝ) T)))
    (hg : Integrable g (volume.restrict (Set.Icc (0:ℝ) T)))
    (hbound : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)), |h t| ≤ g t) :
    IntegrableOn (fun t => φ t * h t) (Set.Icc (0:ℝ) T) := by
  have hh_int : Integrable h (volume.restrict (Set.Icc (0:ℝ) T)) := by
    refine Integrable.mono' hg hmeas ?_
    filter_upwards [hbound] with t ht
    rw [Real.norm_eq_abs]; exact ht
  refine Integrable.mono' (hh_int.norm.const_mul C)
    (hφm.aestronglyMeasurable.mul hmeas) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hφb t) (abs_nonneg _)


--theorem 3

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Combined weak limit of the tested Galerkin terms.For a fixed basis index  and a
bounded test function, we get bilinear form weak limit -/
lemma galerkin_bilinear_weak_limit
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) {M : ℝ}
    (hP_bdd : ∀ t, (P t).IsBounded M)
    (hP_tmeas : ∀ (z : L2TH10U d U hU T) (w0 : H1U0 d U hU),
      AEStronglyMeasurable (fun t => parabilinform (P t) (z t) w0)
        (volume.restrict (Set.Icc (0:ℝ) T)))
    (hP_riesz : ∀ (φ : ℝ → ℝ) (w0 : H1U0 d U hU),
      ∃ R : L2TH10U d U hU T, ∀ (z : L2TH10U d U hU T),
        (∫ t in Set.Icc (0:ℝ) T, φ t * parabilinform (P t) (z t) w0) = inner ℝ z R)
    (f : L2TL2 d U T)
    (dCoeffsSeq : (m : ℕ) → Fin m → ℝ → ℝ) (h_C1 : ∀ m k, ContDiff ℝ 1 (dCoeffsSeq m k))
    (subseq : ℕ → ℕ) (u : L2TH10U d U hU T) (u' : L2TH10U_dual d U hU T)
    (hconv_u : ∀ ψ : L2TH10U d U hU T,
      Tendsto (fun j => inner ℝ (uapproxLift G T (dCoeffsSeq (subseq j))
        (fun n => (h_C1 (subseq j) n).continuous)) ψ) atTop (𝓝 (inner ℝ u ψ)))
    (hconv_u' : ∀ v : L2TH10U d U hU T,
      Tendsto (fun j => ∫ t in Set.Icc (0:ℝ) T,
        (u'approxLift G T (dCoeffsSeq (subseq j)) (h_C1 (subseq j)) t) (v t)) atTop
        (𝓝 (∫ t in Set.Icc (0:ℝ) T, (u' t) (v t))))
    (k : ℕ) (φ : ℝ → ℝ) (hφcont : Continuous φ) (hφm : Measurable φ)
    (Cφ : ℝ) (hCφ : ∀ t, |φ t| ≤ Cφ) :
    Tendsto (fun j => ∫ t in Set.Icc (0:ℝ) T,
        φ t * (inner ℝ (WkpU.toLp (u'approx G (dCoeffsSeq (subseq j)) t).val)
                  (WkpU.toLp (G.w k).val)
                + parabilinform (P t) (uapprox G (dCoeffsSeq (subseq j)) t) (G.w k)))
      atTop (𝓝 (∫ t in Set.Icc (0:ℝ) T,
        φ t * ((u' t) (G.w k) + parabilinform (P t) (u t) (G.w k)))) := by
  -- B-term limit via the Riesz representative `R` of the bilinear-form functional + `hconv_u`.
  obtain ⟨R, hR⟩ := hP_riesz φ (G.w k)
  have hBterm : Tendsto
      (fun j => ∫ t in Set.Icc (0:ℝ) T,
        φ t * parabilinform (P t) (uapprox G (dCoeffsSeq (subseq j)) t) (G.w k))
      atTop (𝓝 (∫ t in Set.Icc (0:ℝ) T, φ t * parabilinform (P t) (u t) (G.w k))) := by
    have heqj : ∀ j, (∫ t in Set.Icc (0:ℝ) T,
          φ t * parabilinform (P t) (uapprox G (dCoeffsSeq (subseq j)) t) (G.w k))
        = inner ℝ (uapproxLift G T (dCoeffsSeq (subseq j))
            (fun n => (h_C1 (subseq j) n).continuous)) R := by
      intro j
      rw [← hR (uapproxLift G T (dCoeffsSeq (subseq j))
            (fun n => (h_C1 (subseq j) n).continuous))]
      refine integral_congr_ae ?_
      filter_upwards [uapproxLift_coeFn G T (dCoeffsSeq (subseq j))
        (fun n => (h_C1 (subseq j) n).continuous)] with t ht
      rw [ht]
    simp only [heqj, hR u]
    exact hconv_u R
  -- u'-term limit (test `hconv_u'` against the L²-lift of `t ↦ φ(t)·wₖ`).
  have hu'term : Tendsto
      (fun j => ∫ t in Set.Icc (0:ℝ) T,
        φ t * inner ℝ (WkpU.toLp (u'approx G (dCoeffsSeq (subseq j)) t).val)
          (WkpU.toLp (G.w k).val))
      atTop (𝓝 (∫ t in Set.Icc (0:ℝ) T, φ t * (u' t) (G.w k))) := by
    haveI : SecondCountableTopologyEither ℝ (H1U0 d U hU) := ⟨Or.inl inferInstance⟩
    have hVmem : MemLp (fun t => φ t • G.w k) 2 (volume.restrict (Set.Icc (0:ℝ) T)) := by
      refine MemLp.of_bound (hφcont.smul continuous_const).aestronglyMeasurable
        (Cφ * ‖G.w k‖) ?_
      filter_upwards with t
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hCφ t) (norm_nonneg _)
    set V : L2TH10U d U hU T := hVmem.toLp _ with hVdef
    have hVcoe : ⇑V =ᵐ[volume.restrict (Set.Icc (0:ℝ) T)] fun t => φ t • G.w k :=
      MemLp.coeFn_toLp _
    have hrhs : (∫ t in Set.Icc (0:ℝ) T, (u' t) (V t))
        = ∫ t in Set.Icc (0:ℝ) T, φ t * (u' t) (G.w k) := by
      refine integral_congr_ae ?_
      filter_upwards [hVcoe] with t hVt
      rw [hVt, map_smul, smul_eq_mul]
    have hlhs : ∀ j, (∫ t in Set.Icc (0:ℝ) T,
          (u'approxLift G T (dCoeffsSeq (subseq j)) (h_C1 (subseq j)) t) (V t))
        = ∫ t in Set.Icc (0:ℝ) T,
          φ t * inner ℝ (WkpU.toLp (u'approx G (dCoeffsSeq (subseq j)) t).val)
            (WkpU.toLp (G.w k).val) := by
      intro j
      refine integral_congr_ae ?_
      filter_upwards [hVcoe, u'approxLift_coeFn G T (dCoeffsSeq (subseq j))
        (h_C1 (subseq j))] with t hVt hLt
      rw [hVt, map_smul, hLt, H1U0_inclusion_Hinv_apply, smul_eq_mul]
    rw [← hrhs]
    simp only [← hlhs]
    exact hconv_u' V
  -- Split `∫ φ·(A + B)` and add the two limits.
  have hφA_int : ∀ j, IntegrableOn
      (fun t => φ t * inner ℝ (WkpU.toLp (u'approx G (dCoeffsSeq (subseq j)) t).val)
        (WkpU.toLp (G.w k).val)) (Set.Icc (0:ℝ) T) := by
    intro j
    have huj : Integrable (fun t => (u'approxLift G T (dCoeffsSeq (subseq j))
        (h_C1 (subseq j)) t) (G.w k)) (volume.restrict (Set.Icc (0:ℝ) T)) :=
      ((MeasureTheory.Lp.memLp (u'approxLift G T (dCoeffsSeq (subseq j))
        (h_C1 (subseq j)))).integrable (by norm_num)).apply_continuousLinearMap (G.w k)
    refine (dominated_time_integrable φ
      (fun t => (u'approxLift G T (dCoeffsSeq (subseq j)) (h_C1 (subseq j)) t) (G.w k))
      (fun t => ‖(u'approxLift G T (dCoeffsSeq (subseq j)) (h_C1 (subseq j)) t) (G.w k)‖)
      Cφ hφm hCφ huj.aestronglyMeasurable huj.norm
      (ae_of_all _ (fun t => le_of_eq (Real.norm_eq_abs _).symm))).congr ?_
    filter_upwards [u'approxLift_coeFn G T (dCoeffsSeq (subseq j))
      (h_C1 (subseq j))] with t ht
    rw [ht, H1U0_inclusion_Hinv_apply]
  have hφB_int : ∀ j, IntegrableOn
      (fun t => φ t * parabilinform (P t) (uapprox G (dCoeffsSeq (subseq j)) t) (G.w k))
      (Set.Icc (0:ℝ) T) := by
    intro j
    refine (parabilinform_time_integrable P hP_bdd
      (uapproxLift G T (dCoeffsSeq (subseq j)) (fun n => (h_C1 (subseq j) n).continuous))
      (G.w k) φ hφm Cφ hCφ
      (hP_tmeas (uapproxLift G T (dCoeffsSeq (subseq j))
        (fun n => (h_C1 (subseq j) n).continuous)) (G.w k))).congr ?_
    filter_upwards [uapproxLift_coeFn G T (dCoeffsSeq (subseq j))
      (fun n => (h_C1 (subseq j) n).continuous)] with t ht
    rw [ht]
  have hφu'_int : IntegrableOn (fun t => φ t * (u' t) (G.w k)) (Set.Icc (0:ℝ) T) := by
    have hui : Integrable (fun t => (u' t) (G.w k)) (volume.restrict (Set.Icc (0:ℝ) T)) :=
      ((MeasureTheory.Lp.memLp u').integrable (by norm_num)).apply_continuousLinearMap (G.w k)
    exact dominated_time_integrable φ (fun t => (u' t) (G.w k))
      (fun t => ‖(u' t) (G.w k)‖) Cφ hφm hCφ hui.aestronglyMeasurable hui.norm
      (ae_of_all _ (fun t => le_of_eq (Real.norm_eq_abs _).symm))
  have hφBu_int : IntegrableOn
      (fun t => φ t * parabilinform (P t) (u t) (G.w k)) (Set.Icc (0:ℝ) T) :=
    parabilinform_time_integrable P hP_bdd u (G.w k) φ hφm Cφ hCφ (hP_tmeas u (G.w k))
  have hLsplit : (fun j => ∫ t in Set.Icc (0:ℝ) T,
        φ t * (inner ℝ (WkpU.toLp (u'approx G (dCoeffsSeq (subseq j)) t).val)
                  (WkpU.toLp (G.w k).val)
                + parabilinform (P t) (uapprox G (dCoeffsSeq (subseq j)) t) (G.w k)))
      = fun j => (∫ t in Set.Icc (0:ℝ) T,
            φ t * inner ℝ (WkpU.toLp (u'approx G (dCoeffsSeq (subseq j)) t).val)
              (WkpU.toLp (G.w k).val))
          + ∫ t in Set.Icc (0:ℝ) T,
              φ t * parabilinform (P t) (uapprox G (dCoeffsSeq (subseq j)) t) (G.w k) := by
    funext j
    rw [← integral_add (hφA_int j) (hφB_int j)]
    exact integral_congr_ae (ae_of_all _ (fun t => by ring))
  have htarget : (∫ t in Set.Icc (0:ℝ) T,
        φ t * ((u' t) (G.w k) + parabilinform (P t) (u t) (G.w k)))
      = (∫ t in Set.Icc (0:ℝ) T, φ t * (u' t) (G.w k))
        + ∫ t in Set.Icc (0:ℝ) T, φ t * parabilinform (P t) (u t) (G.w k) := by
    rw [← integral_add hφu'_int hφBu_int]
    exact integral_congr_ae (ae_of_all _ (fun t => by ring))
  rw [hLsplit, htarget]
  exact hu'term.add hBterm


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- force Galerkin operator A(x) = 0 a.e for w_k go to v -/
lemma galerkin_weaklimit_basis
    (G : GalerkinBasis d U hU) (P : ℝ → ParabolicCoeffs d) (T : ℝ) {M : ℝ}
    (hP_bdd : ∀ t, (P t).IsBounded M)
    (hP_tmeas : ∀ (z : L2TH10U d U hU T) (w0 : H1U0 d U hU),
      AEStronglyMeasurable (fun t => parabilinform (P t) (z t) w0)
        (volume.restrict (Set.Icc (0:ℝ) T)))
    (hP_riesz : ∀ (φ : ℝ → ℝ) (w0 : H1U0 d U hU),
      ∃ R : L2TH10U d U hU T, ∀ (z : L2TH10U d U hU T),
        (∫ t in Set.Icc (0:ℝ) T, φ t * parabilinform (P t) (z t) w0) = inner ℝ z R)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U))
    (dCoeffsSeq : (m : ℕ) → Fin m → ℝ → ℝ)
    (h_galerkin : ∀ m, GalerkinODE G P T f g (dCoeffsSeq m))
    (h_C1 : ∀ m k, ContDiff ℝ 1 (dCoeffsSeq m k))
    (subseq : ℕ → ℕ) (hmono : StrictMono subseq)
    (u : L2TH10U d U hU T) (u' : L2TH10U_dual d U hU T)
    (hconv_u : ∀ ψ : L2TH10U d U hU T,
      Tendsto (fun j => inner ℝ (uapproxLift G T (dCoeffsSeq (subseq j))
        (fun n => (h_C1 (subseq j) n).continuous)) ψ) atTop (𝓝 (inner ℝ u ψ)))
    (hconv_u' : ∀ v : L2TH10U d U hU T,
      Tendsto (fun j => ∫ t in Set.Icc (0:ℝ) T,
        (u'approxLift G T (dCoeffsSeq (subseq j)) (h_C1 (subseq j)) t) (v t)) atTop
        (𝓝 (∫ t in Set.Icc (0:ℝ) T, (u' t) (v t)))) :
    ∀ k : ℕ, ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
      (u' t) (G.w k) + parabilinform (P t) (u t) (G.w k)
        = inner ℝ (f t) (WkpU.toLp (G.w k).val) := by
  intro k
  -- Basis-function weak identity, via the (a.e.) vanishing of the defect
  --   `D t = ⟨u'(t),wₖ⟩ + B(t)[u,wₖ] − ⟨f,wₖ⟩`.
  have hD : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)),
      (u' t) (G.w k) + parabilinform (P t) (u t) (G.w k)
        - inner ℝ (f t) (WkpU.toLp (G.w k).val) = 0 := by
    refine fundamental_lemma_cov _ ?_ ?_
    · -- `D` integrable on `[0,T]`: each term dominated by an `L¹` majorant.
      have hui : Integrable (fun t => (u' t) (G.w k)) (volume.restrict (Set.Icc (0:ℝ) T)) :=
        ((MeasureTheory.Lp.memLp u').integrable (by norm_num)).apply_continuousLinearMap (G.w k)
      have hBu : Integrable (fun t => parabilinform (P t) (u t) (G.w k))
          (volume.restrict (Set.Icc (0:ℝ) T)) := by
        refine Integrable.mono'
          (((MeasureTheory.Lp.memLp u).integrable (by norm_num)).norm.const_mul
            (M * ((d:ℝ)^2 + (d:ℝ) + 1) * ‖G.w k‖)) (hP_tmeas u (G.w k)) ?_
        filter_upwards with t
        rw [Real.norm_eq_abs]
        calc |parabilinform (P t) (u t) (G.w k)|
            ≤ M * ((d:ℝ)^2 + (d:ℝ) + 1) * ‖u t‖ * ‖G.w k‖ :=
              parabilinform_bound (P := P t) M (hP_bdd t) (u t) (G.w k)
          _ = M * ((d:ℝ)^2 + (d:ℝ) + 1) * ‖G.w k‖ * ‖u t‖ := by ring
      have hfi : Integrable (fun t => inner ℝ (f t) (WkpU.toLp (G.w k).val))
          (volume.restrict (Set.Icc (0:ℝ) T)) := by
        refine Integrable.mono'
          (((MeasureTheory.Lp.memLp f).integrable (by norm_num)).norm.mul_const
            ‖WkpU.toLp (G.w k).val‖)
          ((MeasureTheory.Lp.aestronglyMeasurable f).inner aestronglyMeasurable_const) ?_
        filter_upwards with t
        rw [Real.norm_eq_abs]
        exact abs_real_inner_le_norm _ _
      exact (hui.add hBu).sub hfi
    · intro φ hφc hφcs hφsub
      have hφcont : Continuous φ := hφc.continuous
      have hφm : Measurable φ := hφcont.measurable
      -- `φ` is bounded (continuous with compact support).
      obtain ⟨Cφ, hCφ⟩ : ∃ C : ℝ, ∀ t, |φ t| ≤ C := by
        obtain ⟨C, hC⟩ := (hφcs.image_of_continuousOn hφcont.abs.continuousOn).bddAbove
        refine ⟨max C 0, fun t => ?_⟩
        by_cases ht : t ∈ tsupport φ
        · exact le_trans (hC ⟨t, ht, rfl⟩) (le_max_left _ _)
        · rw [image_eq_zero_of_notMem_tsupport ht, abs_zero]; exact le_max_right _ _
      -- `L j := ∫₀ᵀ φ·(⟨u'ₘ,wₖ⟩ + B[uₘ,wₖ])` along the extracted subsequence.
      set L : ℕ → ℝ := fun j => ∫ t in Set.Icc (0:ℝ) T,
        φ t * (inner ℝ (WkpU.toLp (u'approx G (dCoeffsSeq (subseq j)) t).val)
                  (WkpU.toLp (G.w k).val)
                + parabilinform (P t) (uapprox G (dCoeffsSeq (subseq j)) t) (G.w k)) with hL
      -- For `subseq j > k`, the integrated Galerkin identity gives `L j = ∫₀ᵀ φ·⟨f,wₖ⟩`.
      have hev : ∀ᶠ j in atTop, L j
          = ∫ t in Set.Icc (0:ℝ) T, φ t * inner ℝ (f t) (WkpU.toLp (G.w k).val) := by
        rw [Filter.eventually_atTop]
        refine ⟨k + 1, fun j hj => ?_⟩
        have hjk : k < subseq j :=
          lt_of_lt_of_le (Nat.lt_of_succ_le hj) hmono.le_apply
        rw [hL]
        refine integral_congr_ae ?_
        filter_upwards [galerkin_basis_identity G P T hP_bdd f g (dCoeffsSeq (subseq j))
          (h_galerkin (subseq j)) ⟨k, hjk⟩] with t ht
        have ht' : inner ℝ (WkpU.toLp (u'approx G (dCoeffsSeq (subseq j)) t).val)
              (WkpU.toLp (G.w k).val)
            + parabilinform (P t) (uapprox G (dCoeffsSeq (subseq j)) t) (G.w k)
            = inner ℝ (f t) (WkpU.toLp (G.w k).val) := ht
        rw [ht']
      have hLC : Tendsto L atTop
          (𝓝 (∫ t in Set.Icc (0:ℝ) T, φ t * inner ℝ (f t) (WkpU.toLp (G.w k).val))) :=
        Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
      -- `L` also converges to the limit integrand (the combined weak limit).
      have hLlim : Tendsto L atTop (𝓝 (∫ t in Set.Icc (0:ℝ) T,
          φ t * ((u' t) (G.w k) + parabilinform (P t) (u t) (G.w k)))) :=
        galerkin_bilinear_weak_limit G P T hP_bdd hP_tmeas hP_riesz f dCoeffsSeq h_C1 subseq u u'
          hconv_u hconv_u' k φ hφcont hφm Cφ hCφ
      have huniq := tendsto_nhds_unique hLC hLlim
      -- Split the defect integral and conclude it is zero.
      have hφX_int : IntegrableOn
          (fun t => φ t * ((u' t) (G.w k) + parabilinform (P t) (u t) (G.w k)))
          (Set.Icc (0:ℝ) T) := by
        have hui : Integrable (fun t => (u' t) (G.w k)) (volume.restrict (Set.Icc (0:ℝ) T)) :=
          ((MeasureTheory.Lp.memLp u').integrable (by norm_num)).apply_continuousLinearMap (G.w k)
        have h1 : IntegrableOn (fun t => φ t * (u' t) (G.w k)) (Set.Icc (0:ℝ) T) :=
          dominated_time_integrable φ (fun t => (u' t) (G.w k)) (fun t => ‖(u' t) (G.w k)‖)
            Cφ hφm hCφ hui.aestronglyMeasurable hui.norm
            (ae_of_all _ (fun t => le_of_eq (Real.norm_eq_abs _).symm))
        have h2 : IntegrableOn (fun t => φ t * parabilinform (P t) (u t) (G.w k))
            (Set.Icc (0:ℝ) T) :=
          parabilinform_time_integrable P hP_bdd u (G.w k) φ hφm Cφ hCφ (hP_tmeas u (G.w k))
        exact (h1.add h2).congr (ae_of_all _ (fun t => by simp only [Pi.add_apply]; ring))
      have hφY_int : IntegrableOn
          (fun t => φ t * inner ℝ (f t) (WkpU.toLp (G.w k).val)) (Set.Icc (0:ℝ) T) := by
        exact dominated_time_integrable φ (fun t => inner ℝ (f t) (WkpU.toLp (G.w k).val))
          (fun t => ‖f t‖ * ‖WkpU.toLp (G.w k).val‖) Cφ hφm hCφ
          ((MeasureTheory.Lp.aestronglyMeasurable f).inner aestronglyMeasurable_const)
          ((((MeasureTheory.Lp.memLp f).integrable (by norm_num)).norm).mul_const _)
          (ae_of_all _ (fun t => abs_real_inner_le_norm _ _))
      have hsplit : ∫ t in Set.Icc (0:ℝ) T,
            φ t * ((u' t) (G.w k) + parabilinform (P t) (u t) (G.w k)
              - inner ℝ (f t) (WkpU.toLp (G.w k).val))
          = (∫ t in Set.Icc (0:ℝ) T, φ t * ((u' t) (G.w k) + parabilinform (P t) (u t) (G.w k)))
            - ∫ t in Set.Icc (0:ℝ) T, φ t * inner ℝ (f t) (WkpU.toLp (G.w k).val) := by
        rw [← integral_sub hφX_int hφY_int]
        exact integral_congr_ae (ae_of_all _ (fun t => by ring))
      rw [hsplit, huniq, sub_self]
  filter_upwards [hD] with t ht
  linarith [ht]


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem exists_weakSolution
    {θ M : ℝ} (hθ : 0 < θ) (hMpos : 0 < M)
    (P : ℝ → ParabolicCoeffs d) (T : ℝ) (hT : 0 < T)
    (hP_para : ∀ t, (P t).IsUniformlyParabolic U θ)
    (hP_bdd : ∀ t, (P t).IsBounded M)
    -- The two consequences of Evans's `L^∞(U_T)` coefficient hypothesis, absent from the purely
    -- pointwise-in-`t` `ParabolicCoeffs` data:
    -- (i) the time-dependent bilinear form is measurable in `t` (from joint `(t,x)`-measurability);
    (hP_tmeas : ∀ (z : L2TH10U d U hU T) (w0 : H1U0 d U hU),
      AEStronglyMeasurable (fun t => parabilinform (P t) (z t) w0)
        (volume.restrict (Set.Icc (0:ℝ) T)))
    -- (ii) its time-integral against a test function is a bounded functional on `L²(0,T;H¹₀)`,
    -- so (Riesz) has a representative `R` — the Bochner–Riesz representation of the form.
    (hP_riesz : ∀ (φ : ℝ → ℝ) (w0 : H1U0 d U hU),
      ∃ R : L2TH10U d U hU T, ∀ (z : L2TH10U d U hU T),
        (∫ t in Set.Icc (0:ℝ) T, φ t * parabilinform (P t) (z t) w0) = inner ℝ z R)
    (f : L2TL2 d U T) (g : Lp ℝ 2 (μU d U)) :
    ∃ (u : L2TH10U d U hU T) (u' : L2TH10U_dual d U hU T),
      IsWeakSolution P T f g u u' := by
  -- A Galerkin basis exists (L²-orthonormal, H¹-orthogonal; existence fielded).
  obtain ⟨G⟩ := exists_galerkinBasis d U hU
  -- For every `m` the finite Galerkin ODE has a (C¹) solution `dCoeffsSeq m`.  This rests on
  -- `galerkin_ode_solvable` (Carathéodory/continuity duct-tape) together with the C¹ regularity
  -- of ODE solutions; the packaged construction is fielded.
  obtain ⟨dCoeffsSeq, h_galerkin, h_C1⟩ :
      ∃ dCoeffsSeq : (m : ℕ) → Fin m → ℝ → ℝ,
        (∀ m, GalerkinODE G P T f g (dCoeffsSeq m))
        ∧ (∀ m k, ContDiff ℝ 1 (dCoeffsSeq m k)) := by
    sorry
  -- Energy estimates + weak compactness extract weak limits `u ∈ L²(0,T;H¹₀)` and
  -- `u' ∈ L²(0,T;H⁻¹)` along a common subsequence.  (This step is fully proven.)
  obtain ⟨subseq, hmono, u, u', hconv_u, hconv_u'⟩ :=
    galerkin_seq_extract_limits G P T hT hθ hMpos hP_para hP_bdd f g dCoeffsSeq h_galerkin h_C1
  refine ⟨u, u', ?_, ?_⟩
  · -- `u'` is the weak time derivative of `u`: each approximant satisfies the IBP identity
    -- (`galerkin_approx_isWeakTimeDeriv`), preserved under the weak limits.
    exact isWeakTimeDeriv_of_weak_limits
      (fun n => galerkin_approx_isWeakTimeDeriv G T hT.le (dCoeffsSeq (subseq n)) (h_C1 (subseq n)))
      hconv_u hconv_u'
  · -- The weak formulation for ALL `v ∈ H¹₀` reduces (density extension `weaksol_of_basis`) to the
    -- weak identity against each basis function `wₖ`, which is `galerkin_weaklimit_basis`.
    exact weaksol_of_basis G P T hP_bdd f g u u'
      (galerkin_weaklimit_basis G P T hP_bdd hP_tmeas hP_riesz f g dCoeffsSeq h_galerkin h_C1
        subseq hmono u u' hconv_u hconv_u')
