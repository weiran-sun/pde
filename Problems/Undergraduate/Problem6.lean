import Mathlib
import PDE
import PDE.Basics.Wave.WaveIVP1D

/-!
# Undergraduate Problem 6: Sharp Regularity for the 1D Wave Equation

Source: `pde_latex/problems/undergraduate/problem_6.tex` (Math 418, HW-2, Problem 4).

## Informal statement

> Suppose `u` is the solution to the wave equation
> ```
>   u_tt - c² u_xx = 0,
>   u(x, 0) = φ(x),
>   u_t(x, 0) = ψ(x).
> ```
> (a) Show that if `φ ∈ Cᵏ(ℝ)` and `ψ ∈ C^{k-1}(ℝ)` for `k ≥ 2`, then
> `u ∈ Cᵏ(ℝ × ℝ)`.
>
> (b) Give an example to show that in general if `φ ∈ Cᵏ(ℝ)` and
> `ψ ∈ C^{k-1}(ℝ)`, then `u` cannot be smoother than `Cᵏ(ℝ × ℝ)`. In other
> words, find some explicit initial data `φ` and `ψ` where the corresponding
> solution `u` is in `Cᵏ` (by (a)) but not in `C^{k+1}`.

## Semantic alignment

* `Cᵏ` regularity of a function of one variable is `ContDiff ℝ k` with `k : ℕ`;
  joint `Cᵏ` regularity on `ℝ × ℝ` is `ContDiff ℝ k (Function.uncurry u)`.
* "the solution to the wave equation" — the library classical-solution
  predicate `Wave.IsSolutionWaveIVP1D c φ ψ u` (`PDE/Basics/Wave/WaveIVP1D.lean`):
  joint `C²` regularity, `u_tt = c² u_xx` on all of `ℝ²`, initial data at
  `t = 0`. (As in the library, solutions live on all of `ℝ²`; the wave
  equation is time reversible.)
* Part (a) — `solution_contDiff`: every classical solution with
  `φ ∈ Cᵏ`, `ψ ∈ C^{k-1}`, `k ≥ 2`, is jointly `Cᵏ`. It goes through
  D'Alembert's formula (`Wave.IsSolutionWaveIVP1D.eq_dAlembert`) and the
  regularity of the D'Alembert expression (`contDiff_dAlembert`), which in
  turn rests on the `C^{k-1} → Cᵏ` antiderivative step (`contDiff_primitive`).
* Part (b) — `sharpness`: for the explicit data `φ = x₊^{k+1}` (`pplus (k+1)`),
  `ψ ≡ 0`, the function `u(x,t) = ½[φ(x+ct) + φ(x-ct)]` is a classical
  solution, is jointly `Cᵏ`, and is NOT `C^{k+1}`. The one-variable facts
  `x₊^{k+1} ∈ Cᵏ \ C^{k+1}` are `contDiff_pplus` / `not_contDiff_pplus`,
  driven by the derivative recursion `deriv_pplus` and the
  non-differentiability of `x₊` at `0` (`not_differentiableAt_pplus_one`,
  reduced to Mathlib's `not_differentiableAt_abs_zero`).
-/

open Real Wave

namespace Problems.Undergraduate.Problem6

/-! ## Part (a): regularity transfer -/

/-- **Antiderivative regularity** (`lem:problem6-antideriv`). If
`ψ ∈ C^{k-1}(ℝ)` with `k ≥ 1`, then `Ψ(α) = ∫_0^α ψ(s) ds` is of class `Cᵏ`
on `ℝ`, with `Ψ' = ψ`. -/
theorem contDiff_primitive {k : ℕ} (hk : 1 ≤ k) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (k - 1 : ℕ) ψ) :
    ContDiff ℝ k (fun α => ∫ s in (0:ℝ)..α, ψ s) ∧
      ∀ α : ℝ, HasDerivAt (fun α => ∫ s in (0:ℝ)..α, ψ s) (ψ α) α := by
  have hcont : Continuous ψ := hψ.continuous
  have hderiv : ∀ α : ℝ, HasDerivAt (fun α => ∫ s in (0:ℝ)..α, ψ s) (ψ α) α :=
    fun α => (hcont.integral_hasStrictDerivAt 0 α).hasDerivAt
  refine ⟨?_, hderiv⟩
  have hd : deriv (fun α => ∫ s in (0:ℝ)..α, ψ s) = ψ :=
    funext fun α => (hderiv α).deriv
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : ℕ) + 1 by push_cast; ring,
    contDiff_succ_iff_deriv]
  refine ⟨fun α => (hderiv α).differentiableAt, by simp, ?_⟩
  rw [hd]
  simpa using hψ

/-- **`Cᵏ` regularity of the D'Alembert expression**
(`lem:problem6-dalembert-contDiff`). For `c > 0`, `k ≥ 2`, `φ ∈ Cᵏ(ℝ)`,
`ψ ∈ C^{k-1}(ℝ)`, the D'Alembert expression is of class `Cᵏ` jointly on
`ℝ × ℝ`. -/
theorem contDiff_dAlembert {k : ℕ} (hk : 2 ≤ k) {c : ℝ} (_hc : 0 < c)
    {φ ψ : ℝ → ℝ} (hφ : ContDiff ℝ k φ) (hψ : ContDiff ℝ (k - 1 : ℕ) ψ) :
    ContDiff ℝ k (Function.uncurry (Wave.dAlembert c φ ψ)) := by
  obtain ⟨hΨ, hΨ'⟩ := contDiff_primitive (le_trans one_le_two hk) hψ
  set Ψ : ℝ → ℝ := fun α => ∫ s in (0:ℝ)..α, ψ s with hΨdef
  -- Rewrite the D'Alembert expression through the primitive `Ψ`.
  have hsplit : Function.uncurry (Wave.dAlembert c φ ψ) = fun p : ℝ × ℝ =>
      (φ (p.1 + c * p.2) + φ (p.1 - c * p.2)) / 2
        + (1 / (2 * c)) * (Ψ (p.1 + c * p.2) - Ψ (p.1 - c * p.2)) := by
    funext p
    have hint : (∫ s in (p.1 - c * p.2)..(p.1 + c * p.2), ψ s)
        = Ψ (p.1 + c * p.2) - Ψ (p.1 - c * p.2) := by
      rw [hΨdef]
      rw [← intervalIntegral.integral_interval_sub_left
        (hψ.continuous.intervalIntegrable _ _) (hψ.continuous.intervalIntegrable _ _)]
    simp only [Function.uncurry, Wave.dAlembert, hint]
  rw [hsplit]
  -- The characteristic coordinates are `Cᵏ` maps `ℝ² → ℝ`.
  have hplus : ContDiff ℝ k (fun p : ℝ × ℝ => p.1 + c * p.2) := by fun_prop
  have hminus : ContDiff ℝ k (fun p : ℝ × ℝ => p.1 - c * p.2) := by fun_prop
  exact (((hφ.comp hplus).add (hφ.comp hminus)).div_const 2).add
    (((hΨ.comp hplus).sub (hΨ.comp hminus)).const_smul (1 / (2 * c)))

/-- **Regularity of solutions** (`thm:problem6-regularity`, part (a)). For
`c > 0`, `k ≥ 2`, `φ ∈ Cᵏ(ℝ)`, `ψ ∈ C^{k-1}(ℝ)`, every classical solution of
the whole-line IVP with data `(φ, ψ)` is jointly `Cᵏ` on `ℝ × ℝ`. -/
theorem solution_contDiff {k : ℕ} (hk : 2 ≤ k) {c : ℝ} (hc : 0 < c)
    {φ ψ : ℝ → ℝ} (hφ : ContDiff ℝ k φ) (hψ : ContDiff ℝ (k - 1 : ℕ) ψ)
    {u : ℝ → ℝ → ℝ} (hu : Wave.IsSolutionWaveIVP1D c φ ψ u) :
    ContDiff ℝ k (Function.uncurry u) := by
  have heq : u = Wave.dAlembert c φ ψ := by
    funext x t
    exact hu.eq_dAlembert hc x t
  rw [heq]
  exact contDiff_dAlembert hk hc hφ hψ

/-! ## Part (b): sharpness -/

/-- **The truncated power** (`def:problem6-pplus`):
`pplus n x = max (x, 0) ^ n = x₊ⁿ`. -/
noncomputable def pplus (n : ℕ) : ℝ → ℝ := fun x => max x 0 ^ n

/-- The truncated powers are continuous (the continuity half of
`lem:problem6-pplus-one-not-diff`). -/
theorem continuous_pplus (n : ℕ) : Continuous (pplus n) := by
  unfold pplus
  fun_prop

/-- **`x₊` is not differentiable at `0`** (`lem:problem6-pplus-one-not-diff`).
Since `x₊ = (x + |x|)/2`, differentiability of `pplus 1` at `0` would make
`|x| = 2 x₊ - x` differentiable at `0`, contradicting
`not_differentiableAt_abs_zero`. -/
theorem not_differentiableAt_pplus_one :
    ¬ DifferentiableAt ℝ (pplus 1) 0 := by
  intro h
  apply not_differentiableAt_abs_zero
  have habs : (abs : ℝ → ℝ) = fun x : ℝ => 2 * pplus 1 x - x := by
    funext x
    simp only [pplus, pow_one]
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx, abs_of_nonpos hx]; ring
    · rw [max_eq_left hx, abs_of_nonneg hx]; ring
  rw [habs]
  exact ((h.const_mul 2).sub differentiableAt_id)

/-- **Derivative recursion for truncated powers** (`lem:problem6-pplus-deriv`).
For `n ≥ 2`, `pplus n` is differentiable everywhere with derivative
`n * pplus (n-1)`. -/
theorem deriv_pplus {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    HasDerivAt (pplus n) (n * pplus (n - 1) x) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- `x < 0`: `pplus n` vanishes on a neighborhood of `x`.
    have hval : pplus (n - 1) x = 0 := by
      simp [pplus, max_eq_right hx.le, zero_pow (by omega : n - 1 ≠ 0)]
    rw [hval, mul_zero]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y (hy : y < 0)
    simp [pplus, max_eq_right hy.le, zero_pow (by omega : n ≠ 0)]
  · -- `x = 0`: paste the one-sided derivatives, both equal to `0`.
    subst hx
    have hval : pplus (n - 1) 0 = 0 := by
      simp [pplus, zero_pow (by omega : n - 1 ≠ 0)]
    rw [hval, mul_zero]
    have hleft : HasDerivWithinAt (pplus n) 0 (Set.Iic (0 : ℝ)) 0 := by
      refine ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt).congr
        (fun y (hy : y ≤ 0) => ?_) ?_
      · simp [pplus, max_eq_right hy, zero_pow (by omega : n ≠ 0)]
      · simp [pplus, zero_pow (by omega : n ≠ 0)]
    have hright : HasDerivWithinAt (pplus n) 0 (Set.Ici (0 : ℝ)) 0 := by
      have hpow : HasDerivAt (fun y : ℝ => y ^ n) 0 0 := by
        simpa [zero_pow (by omega : n - 1 ≠ 0)] using hasDerivAt_pow n (0 : ℝ)
      refine (hpow.hasDerivWithinAt).congr (fun y (hy : 0 ≤ y) => ?_) ?_
      · simp [pplus, max_eq_left hy]
      · simp [pplus, zero_pow (by omega : n ≠ 0)]
    have hunion := hleft.union hright
    rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hunion
  · -- `x > 0`: `pplus n` agrees with `y ^ n` on a neighborhood of `x`.
    have hval : pplus (n - 1) x = x ^ (n - 1) := by
      simp [pplus, max_eq_left hx.le]
    rw [hval]
    refine (hasDerivAt_pow n x).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y (hy : 0 < y)
    simp [pplus, max_eq_left hy.le]

/-- **`x₊^{k+1} ∈ Cᵏ`** (first half of `lem:problem6-pplus-sharp`). For every
`k ≥ 1`, the truncated power `pplus (k+1)` is of class `Cᵏ` on `ℝ`. -/
theorem contDiff_pplus (k : ℕ) : ContDiff ℝ k (pplus (k + 1)) := by
  induction k with
  | zero => simpa [contDiff_zero] using continuous_pplus 1
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : ℕ) + 1 by push_cast; ring,
      contDiff_succ_iff_deriv]
    have hd : deriv (pplus (m + 2)) = fun x => (m + 2 : ℕ) * pplus (m + 1) x := by
      funext x
      simpa using (deriv_pplus (n := m + 2) (by omega) x).deriv
    refine ⟨fun x => (deriv_pplus (n := m + 2) (by omega) x).differentiableAt, by simp, ?_⟩
    rw [hd]
    exact ih.const_smul ((m + 2 : ℕ) : ℝ)

/-- **`x₊^{k+1} ∉ C^{k+1}`** (second half of `lem:problem6-pplus-sharp`). For
every `k ≥ 1`, the truncated power `pplus (k+1)` is not of class `C^{k+1}`:
its `k`-th derivative is `(k+1)!/1! ⬝ pplus 1`, which is not differentiable
at `0`. -/
theorem not_contDiff_pplus (k : ℕ) :
    ¬ ContDiff ℝ (k + 1 : ℕ) (pplus (k + 1)) := by
  induction k with
  | zero =>
    intro h
    exact not_differentiableAt_pplus_one ((h.differentiable (by norm_num)) 0)
  | succ m ih =>
    intro h
    apply ih
    rw [show ((m + 1 + 1 : ℕ) : WithTop ℕ∞) = ((m + 1 : ℕ) : WithTop ℕ∞) + 1
      by push_cast; ring, contDiff_succ_iff_deriv] at h
    have hd : deriv (pplus (m + 2)) = fun x => (m + 2 : ℕ) * pplus (m + 1) x := by
      funext x
      simpa using (deriv_pplus (n := m + 2) (by omega) x).deriv
    rw [hd] at h
    have hval : pplus (m + 1) = fun x =>
        (((m + 2 : ℕ) : ℝ))⁻¹ * ((m + 2 : ℕ) * pplus (m + 1) x) := by
      funext x
      rw [inv_mul_cancel_left₀ (by positivity)]
    rw [hval]
    exact h.2.2.const_smul (((m + 2 : ℕ) : ℝ))⁻¹

/-- The candidate sharp solution of part (b): with data `φ = x₊^{k+1}`,
`ψ ≡ 0`, the D'Alembert expression collapses to
`u(x,t) = ½ [φ(x+ct) + φ(x-ct)]`. (Helper definition; the blueprint block
`thm:problem6-sharp` states its properties.) -/
noncomputable def sharpSolution (k : ℕ) (c : ℝ) : ℝ → ℝ → ℝ := fun x t =>
  (pplus (k + 1) (x + c * t) + pplus (k + 1) (x - c * t)) / 2

/-- **Sharpness of the regularity transfer** (`thm:problem6-sharp`, part (b)).
Fix `k ≥ 2` and `c > 0`, and take `φ = x₊^{k+1}`, `ψ ≡ 0`. Then
`u(x,t) = ½ [φ(x+ct) + φ(x-ct)]` is a classical solution of the IVP, is
jointly `Cᵏ` on `ℝ²`, and is not `C^{k+1}` — so the conclusion of part (a)
cannot be improved. -/
theorem sharpness {k : ℕ} (hk : 2 ≤ k) {c : ℝ} (hc : 0 < c) :
    Wave.IsSolutionWaveIVP1D c (pplus (k + 1)) (fun _ => 0) (sharpSolution k c) ∧
      ContDiff ℝ k (Function.uncurry (sharpSolution k c)) ∧
      ¬ ContDiff ℝ (k + 1 : ℕ) (Function.uncurry (sharpSolution k c)) := by
  have hφ : ContDiff ℝ k (pplus (k + 1)) := contDiff_pplus k
  -- With `ψ ≡ 0` the integral term of the D'Alembert expression vanishes.
  have hda : Wave.dAlembert c (pplus (k + 1)) (fun _ => 0) = sharpSolution k c := by
    funext x t
    simp [Wave.dAlembert, sharpSolution, add_div]
  refine ⟨?_, ?_, ?_⟩
  · -- A classical solution, by the existence half of D'Alembert.
    have h := Wave.isSolutionWaveIVP1D_dAlembert (c := c) (ψ := fun _ => 0) hc
      (hφ.of_le (by exact_mod_cast hk)) contDiff_const
    rwa [hda] at h
  · -- Jointly `Cᵏ`: each summand is `pplus (k+1)` composed with a linear map.
    have hplus : ContDiff ℝ k (fun p : ℝ × ℝ => p.1 + c * p.2) := by fun_prop
    have hminus : ContDiff ℝ k (fun p : ℝ × ℝ => p.1 - c * p.2) := by fun_prop
    exact ((hφ.comp hplus).add (hφ.comp hminus)).div_const 2
  · -- Not `C^{k+1}`: the restriction to the line `t = 0` is `pplus (k+1)`.
    intro h
    apply not_contDiff_pplus k
    have hrestrict : pplus (k + 1) =
        fun x : ℝ => Function.uncurry (sharpSolution k c) (x, 0) := by
      funext x
      simp [Function.uncurry, sharpSolution]
    rw [hrestrict]
    exact h.comp (by fun_prop : ContDiff ℝ (k + 1 : ℕ) fun x : ℝ => (x, (0:ℝ)))

end Problems.Undergraduate.Problem6
