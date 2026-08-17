/-
# THE CARATHÉODORY EXISTENCE THEOREM — the complete development in one file

Verbatim concatenation of the five modules of `Caratheodory` (in dependency
order: Aux, Measurability, Existence, Limit, Main), so the whole proof can be
read and compiled in a single place.  The namespace is `CaratheodoryFull` so
that this file can coexist with the modular version inside the same library.

EVERY THEOREM IS FULLY PROVEN — no sorries, no axioms beyond Mathlib
(`propext`, `Classical.choice`, `Quot.sound`).

Headline result — `caratheodory_existence`: let `E` be a finite-dimensional
real normed space and `f : ℝ → E → E` be measurable in `t` for each `x` in
`closedBall x0 b`, continuous in `x` on the ball for a.e. `t ∈ [t0-a, t0+a]`,
and dominated by an integrable `m`.  Then there are `0 < h ≤ a` and a
continuous `x : ℝ → E` with `x t0 = x0`, ball-valued on `[t0-h, t0+h]`,
satisfying the integral equation `x t = x0 + ∫ s in t0..t, f s (x s)` there
(absolute continuity) and `HasDerivAt x (f t (x t)) t` for a.e. `t`.

Since Schauder's fixed-point theorem is not in Mathlib, the proof uses the
Tonelli delayed-approximation scheme: the delayed integral operator with
delay `δ` reaches a genuine fixed point after finitely many iterations
(shell-by-shell bootstrap), the approximations are uniformly bounded and
equicontinuous, Arzelà–Ascoli extracts a uniform subsequential limit,
dominated convergence passes the fixed-point identity to the limit, and the
a.e. derivative comes from the Lebesgue differentiation theorem applied
coordinatewise in a basis of `E`.
-/
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Free

open Set Filter Metric MeasureTheory BoundedContinuousFunction
open scoped Topology Interval

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CaratheodoryFull

/-
== MODULE ==

Auxiliary real-valued functions for the Tonelli approximation scheme:

* `clampI t0 h` : the 1-Lipschitz retraction of `ℝ` onto `[t0 - h, t0 + h]`;
* `pull t0 δ`   : the 1-Lipschitz map moving a point towards `t0` by distance
  (at most) `δ`, stopping at `t0`;
* `delayedProj t0 h δ = pull t0 δ ∘ clampI t0 h` : the delayed projection used
  to define the delayed integral operator.
-/

section

/-- Clamp a real number into the interval `[t0 - h, t0 + h]`. -/
def clampI (t0 h t : ℝ) : ℝ := max (t0 - h) (min (t0 + h) t)

/-- Move `τ` towards `t0` by distance at most `δ`, stopping at `t0`. -/
def pull (t0 δ τ : ℝ) : ℝ := max (τ - δ) (min (τ + δ) t0)

/-- The delayed projection: clamp into `[t0 - h, t0 + h]`, then pull towards
`t0` by `δ`. -/
def delayedProj (t0 h δ t : ℝ) : ℝ := pull t0 δ (clampI t0 h t)

section Lemmas

variable {t0 h δ t τ : ℝ}

lemma lipschitzWith_clampI (t0 h : ℝ) : LipschitzWith 1 (clampI t0 h) := by
  have : LipschitzWith 1 fun t : ℝ => min (t0 + h) t := by
    simpa using (LipschitzWith.const' (K := 1) (t0 + h)).min LipschitzWith.id
  have h3 := (LipschitzWith.const' (K := 1) (t0 - h)).max this
  rwa [max_self] at h3

lemma lipschitzWith_pull (t0 δ : ℝ) : LipschitzWith 1 (pull t0 δ) := by
  have h1 : LipschitzWith 1 fun τ : ℝ => τ - δ :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp [Real.dist_eq, sub_sub_sub_cancel_right]
  have h2 : LipschitzWith 1 fun τ : ℝ => min (τ + δ) t0 := by
    have ha : LipschitzWith 1 fun τ : ℝ => τ + δ :=
      LipschitzWith.of_dist_le_mul fun x y => by
        simp [Real.dist_eq, add_sub_add_right_eq_sub]
    simpa using ha.min (LipschitzWith.const' (K := 1) t0)
  have h3 := h1.max h2
  rwa [max_self] at h3

lemma lipschitzWith_delayedProj (t0 h δ : ℝ) :
    LipschitzWith 1 (delayedProj t0 h δ) := by
  have h3 := (lipschitzWith_pull t0 δ).comp (lipschitzWith_clampI t0 h)
  rwa [mul_one] at h3

lemma continuous_delayedProj (t0 h δ : ℝ) : Continuous (delayedProj t0 h δ) :=
  (lipschitzWith_delayedProj t0 h δ).continuous

/-- On `ℝ`, `LipschitzWith 1` gives the plain distance bound. -/
lemma abs_delayedProj_sub_delayedProj (t0 h δ s t : ℝ) :
    |delayedProj t0 h δ s - delayedProj t0 h δ t| ≤ |s - t| := by
  have := (lipschitzWith_delayedProj t0 h δ).dist_le_mul s t
  simpa [Real.dist_eq] using this

lemma clampI_mem (hh : 0 ≤ h) (t : ℝ) : clampI t0 h t ∈ Icc (t0 - h) (t0 + h) := by
  unfold clampI
  refine ⟨le_max_left _ _, ?_⟩
  rw [max_le_iff]
  exact ⟨by linarith, min_le_left _ _⟩

lemma clampI_of_mem (ht : t ∈ Icc (t0 - h) (t0 + h)) : clampI t0 h t = t := by
  obtain ⟨h1, h2⟩ := ht
  unfold clampI
  rw [min_eq_right h2, max_eq_right h1]

lemma abs_clampI_sub_center (hh : 0 ≤ h) (t : ℝ) : |clampI t0 h t - t0| ≤ h := by
  have := clampI_mem (t0 := t0) hh t
  rw [abs_le]
  constructor
  · linarith [this.1]
  · linarith [this.2]

lemma pull_eq_of_le (hδ : 0 ≤ δ) (hτ : τ ≤ t0) : pull t0 δ τ = min (τ + δ) t0 := by
  unfold pull
  exact max_eq_right (le_min (by linarith) (by linarith))

lemma pull_eq_of_ge (hδ : 0 ≤ δ) (hτ : t0 ≤ τ) : pull t0 δ τ = max (τ - δ) t0 := by
  unfold pull
  rw [min_eq_right (show t0 ≤ τ + δ by linarith)]

/-- The pulled point is closer to the center: `|pull t0 δ τ - t0| = max (|τ - t0| - δ) 0`. -/
lemma abs_pull_sub_center (hδ : 0 ≤ δ) (τ : ℝ) :
    |pull t0 δ τ - t0| = max (|τ - t0| - δ) 0 := by
  rcases le_total τ t0 with hτ | hτ
  · rw [pull_eq_of_le hδ hτ, abs_of_nonpos (by simp), abs_of_nonpos (by linarith)]
    rcases le_total (τ + δ) t0 with h' | h'
    · rw [min_eq_left h', max_eq_left (by linarith)]; ring
    · rw [min_eq_right h', max_eq_right (by linarith)]; ring
  · rw [pull_eq_of_ge hδ hτ, abs_of_nonneg (by linarith [le_max_right (τ - δ) t0]),
      abs_of_nonneg (show (0:ℝ) ≤ τ - t0 by linarith)]
    rcases le_total (τ - δ) t0 with h' | h'
    · rw [max_eq_right h', max_eq_right (by linarith)]; ring
    · rw [max_eq_left h', max_eq_left (by linarith)]; ring

/-- Pulling moves a point by at most `δ`. -/
lemma abs_pull_sub_self (hδ : 0 ≤ δ) (τ : ℝ) : |pull t0 δ τ - τ| ≤ δ := by
  rcases le_total τ t0 with hτ | hτ
  · rw [pull_eq_of_le hδ hτ, abs_le]
    rcases le_total (τ + δ) t0 with h' | h'
    · rw [min_eq_left h']; constructor <;> linarith
    · rw [min_eq_right h']; constructor <;> linarith
  · rw [pull_eq_of_ge hδ hτ, abs_le]
    rcases le_total (τ - δ) t0 with h' | h'
    · rw [max_eq_right h']; constructor <;> linarith
    · rw [max_eq_left h']; constructor <;> linarith

lemma abs_delayedProj_sub_center (hδ : 0 ≤ δ) (t : ℝ) :
    |delayedProj t0 h δ t - t0| = max (|clampI t0 h t - t0| - δ) 0 :=
  abs_pull_sub_center hδ _

lemma abs_delayedProj_sub_center_le (hh : 0 ≤ h) (hδ : 0 ≤ δ) (t : ℝ) :
    |delayedProj t0 h δ t - t0| ≤ h := by
  rw [abs_delayedProj_sub_center hδ]
  have := abs_clampI_sub_center (t0 := t0) hh t
  rw [max_le_iff]
  exact ⟨by linarith, hh⟩

lemma delayedProj_mem (hh : 0 ≤ h) (hδ : 0 ≤ δ) (t : ℝ) :
    delayedProj t0 h δ t ∈ Icc (t0 - h) (t0 + h) := by
  have := abs_delayedProj_sub_center_le (t0 := t0) hh hδ t
  rw [abs_le] at this
  constructor <;> linarith [this.1, this.2]

/-- On the interval itself, the delayed projection moves points by at most `δ`. -/
lemma abs_delayedProj_sub_self (hδ : 0 ≤ δ) (ht : t ∈ Icc (t0 - h) (t0 + h)) :
    |delayedProj t0 h δ t - t| ≤ δ := by
  rw [delayedProj, clampI_of_mem ht]
  exact abs_pull_sub_self hδ t

/-- Any point of `uIcc t0 c` is at distance at most `|c - t0|` from `t0`. -/
lemma abs_sub_center_le_of_mem_uIcc {c s : ℝ} (hs : s ∈ uIcc t0 c) :
    |s - t0| ≤ |c - t0| := by
  rw [Set.mem_uIcc] at hs
  rw [abs_le]
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by linarith [abs_nonneg (c - t0)], by linarith [le_abs_self (c - t0)]⟩
  · exact ⟨by linarith [neg_abs_le (c - t0)], by linarith [abs_nonneg (c - t0)]⟩

/-- Points of `uIcc t0 c` lie in `Icc (t0 - h) (t0 + h)` whenever `|c - t0| ≤ h`. -/
lemma mem_Icc_of_mem_uIcc {c s : ℝ} (hc : |c - t0| ≤ h) (hs : s ∈ uIcc t0 c) :
    s ∈ Icc (t0 - h) (t0 + h) := by
  have := abs_sub_center_le_of_mem_uIcc hs
  have habs : |s - t0| ≤ h := le_trans this hc
  rw [abs_le] at habs
  constructor <;> linarith [habs.1, habs.2]

end Lemmas

end

/-
== MODULE ==

The Carathéodory composition lemma: if `f t x` is (a.e.-strongly-)measurable in
`t` for each fixed `x` in a closed ball, and continuous in `x` on that ball for
a.e. `t`, then for every continuous `u` taking values in the ball, the map
`s ↦ f s (u s)` is a.e. strongly measurable.

The proof approximates `u` by the countably-valued functions
`s ↦ u (⌊s * (n + 1)⌋ / (n + 1))` and passes to the limit.
-/

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The grid-snap map used to approximate the identity from a countable set. -/
private noncomputable def snap (n : ℕ) (s : ℝ) : ℝ := (⌊s * ((n : ℝ) + 1)⌋ : ℤ) / ((n : ℝ) + 1)

private lemma abs_snap_sub_le (n : ℕ) (s : ℝ) : |snap n s - s| ≤ 1 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : (⌊s * ((n : ℝ) + 1)⌋ : ℝ) ≤ s * ((n : ℝ) + 1) := Int.floor_le _
  have h2 : s * ((n : ℝ) + 1) < (⌊s * ((n : ℝ) + 1)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have : snap n s - s = ((⌊s * ((n : ℝ) + 1)⌋ : ℝ) - s * ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
    rw [snap]
    field_simp
  rw [this, abs_div, abs_of_pos hn, div_le_div_iff_of_pos_right hn]
  rw [abs_le]
  constructor <;> linarith

private lemma tendsto_snap (s : ℝ) : Tendsto (fun n => snap n s) atTop (𝓝 s) := by
  have h0 : Tendsto (fun n : ℕ => snap n s - s) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => abs_snap_sub_le n s)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have := h0.add_const s
  simpa using this

/-- **Carathéodory composition lemma.** If `f t x` is a.e. strongly measurable in `t`
for each `x` in the closed ball, continuous in `x` on the ball for a.e. `t`, and
`u` is continuous with values in the ball, then `s ↦ f s (u s)` is a.e. strongly
measurable. -/
theorem aestronglyMeasurable_comp_of_continuous (μ : Measure ℝ) {x0 : E} {b : ℝ}
    {f : ℝ → E → F}
    (hf_meas : ∀ x ∈ closedBall x0 b, AEStronglyMeasurable (fun t => f t x) μ)
    (hf_cont : ∀ᵐ t ∂μ, ContinuousOn (f t) (closedBall x0 b))
    {u : ℝ → E} (hu : Continuous u) (hub : ∀ s, u s ∈ closedBall x0 b) :
    AEStronglyMeasurable (fun s => f s (u s)) μ := by
  classical
  -- the countably-valued approximations
  set g : ℕ → ℝ → F := fun n s => f s (u (snap n s)) with hg
  have hgm : ∀ n, AEStronglyMeasurable (g n) μ := by
    intro n
    -- family of measurable-in-`t` slices, indexed by the countable type `ℤ`
    set Ffam : ℤ → ℝ → F := fun j s => f s (u ((j : ℝ) / ((n : ℝ) + 1))) with hFfam
    have hFj : ∀ j : ℤ, AEStronglyMeasurable (Ffam j) μ := fun j =>
      hf_meas _ (hub _)
    set mkF : ℤ → ℝ → F := fun j => (hFj j).mk _ with hmkF
    have hmk_sm : ∀ j, StronglyMeasurable (mkF j) := fun j => (hFj j).stronglyMeasurable_mk
    have h_uncurry : StronglyMeasurable (Function.uncurry mkF) :=
      stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
        (fun s => continuous_of_discreteTopology) hmk_sm
    have hjm : Measurable fun s : ℝ => (⌊s * ((n : ℝ) + 1)⌋ : ℤ) :=
      (measurable_id.mul_const _).floor
    have hG_sm : StronglyMeasurable fun s => mkF (⌊s * ((n : ℝ) + 1)⌋ : ℤ) s := by
      have : (fun s => mkF (⌊s * ((n : ℝ) + 1)⌋ : ℤ) s) =
          (Function.uncurry mkF) ∘ fun s : ℝ => ((⌊s * ((n : ℝ) + 1)⌋ : ℤ), s) := rfl
      rw [this]
      exact h_uncurry.comp_measurable (hjm.prodMk measurable_id)
    refine ⟨fun s => mkF (⌊s * ((n : ℝ) + 1)⌋ : ℤ) s, hG_sm, ?_⟩
    have hall : ∀ᵐ s ∂μ, ∀ j : ℤ, Ffam j s = mkF j s :=
      ae_all_iff.mpr fun j => (hFj j).ae_eq_mk
    filter_upwards [hall] with s hs
    exact hs _
  have hlim : ∀ᵐ s ∂μ, Tendsto (fun n => g n s) atTop (𝓝 (f s (u s))) := by
    filter_upwards [hf_cont] with s hs
    have h1 : Tendsto (fun n => u (snap n s)) atTop (𝓝 (u s)) :=
      (hu.tendsto s).comp (tendsto_snap s)
    have h2 : Tendsto (fun n => u (snap n s)) atTop (𝓝[closedBall x0 b] (u s)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h1, Eventually.of_forall fun n => hub _⟩
    exact ((hs (u s) (hub s)).tendsto).comp h2
  exact aestronglyMeasurable_of_tendsto_ae atTop hgm hlim

end

/-
== MODULE ==

The Tonelli approximation scheme for the Carathéodory existence theorem.

Given Carathéodory data `f` on `[t0 - h, t0 + h] × closedBall x0 b` with
`∫_{[t0-h,t0+h]} m ≤ b`, we construct for each `k` the delayed approximation
`tonelli k` solving
  `tonelli k t = x0 + ∫_{t0}^{ρ_k t} f (s, tonelli k s) ds`,
where `ρ_k` is the delayed projection with delay `h / (k + 1)`.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The Carathéodory data on the interval `[t0 - h, t0 + h]`, together with the
smallness condition `∫ m ≤ b` making the closed ball invariant. -/
structure IsSetup (t0 h b : ℝ) (x0 : E) (f : ℝ → E → E) (m : ℝ → ℝ) : Prop where
  h_pos : 0 < h
  b_nonneg : 0 ≤ b
  meas : ∀ x ∈ closedBall x0 b,
    AEStronglyMeasurable (fun t => f t x) (volume.restrict (Icc (t0 - h) (t0 + h)))
  cont : ∀ᵐ t ∂volume.restrict (Icc (t0 - h) (t0 + h)),
    ContinuousOn (f t) (closedBall x0 b)
  m_nonneg : ∀ s, 0 ≤ m s
  m_int : IntegrableOn m (Icc (t0 - h) (t0 + h))
  bound : ∀ᵐ t ∂volume.restrict (Icc (t0 - h) (t0 + h)),
    ∀ x ∈ closedBall x0 b, ‖f t x‖ ≤ m t
  small : ∫ s in Icc (t0 - h) (t0 + h), m s ≤ b

/-- A candidate curve: continuous and valued in the closed ball. -/
def GoodFun (x0 : E) (b : ℝ) (u : ℝ → E) : Prop :=
  Continuous u ∧ ∀ t, u t ∈ closedBall x0 b

variable {t0 h b δ : ℝ} {x0 : E} {f : ℝ → E → E} {m : ℝ → ℝ}

namespace IsSetup

section Basic

variable (S : IsSetup t0 h b x0 f m)
include S

lemma t0_mem : t0 ∈ Icc (t0 - h) (t0 + h) := by
  have := S.h_pos
  constructor <;> linarith

lemma uIcc_subset {c d : ℝ} (hc : c ∈ Icc (t0 - h) (t0 + h))
    (hd : d ∈ Icc (t0 - h) (t0 + h)) : uIcc c d ⊆ Icc (t0 - h) (t0 + h) :=
  Set.ordConnected_Icc.uIcc_subset hc hd

/-- Composition with a good curve is integrable on the base interval. -/
lemma integrableOn_comp {u : ℝ → E} (hu : GoodFun x0 b u) :
    IntegrableOn (fun s => f s (u s)) (Icc (t0 - h) (t0 + h)) := by
  have hm : AEStronglyMeasurable (fun s => f s (u s))
      (volume.restrict (Icc (t0 - h) (t0 + h))) :=
    aestronglyMeasurable_comp_of_continuous _ S.meas S.cont hu.1 hu.2
  refine Integrable.mono' S.m_int hm ?_
  filter_upwards [S.bound] with s hs
  exact hs _ (hu.2 s)

lemma intervalIntegrable_comp {u : ℝ → E} (hu : GoodFun x0 b u) {c d : ℝ}
    (hc : c ∈ Icc (t0 - h) (t0 + h)) (hd : d ∈ Icc (t0 - h) (t0 + h)) :
    IntervalIntegrable (fun s => f s (u s)) volume c d := by
  rw [intervalIntegrable_iff]
  exact (S.integrableOn_comp hu).mono_set
    (le_trans uIoc_subset_uIcc (S.uIcc_subset hc hd))

lemma intervalIntegrable_m {c d : ℝ}
    (hc : c ∈ Icc (t0 - h) (t0 + h)) (hd : d ∈ Icc (t0 - h) (t0 + h)) :
    IntervalIntegrable m volume c d := by
  rw [intervalIntegrable_iff]
  exact S.m_int.mono_set (le_trans uIoc_subset_uIcc (S.uIcc_subset hc hd))

end Basic

end IsSetup

/-- The primitive (from `t0`) of the zero-extension of `m` outside the base
interval. This is the modulus of continuity for all approximations. -/
noncomputable def prim (t0 h : ℝ) (m : ℝ → ℝ) : ℝ → ℝ :=
  fun τ => ∫ s in t0..τ, (Icc (t0 - h) (t0 + h)).indicator m s

namespace IsSetup

section Prim

variable (S : IsSetup t0 h b x0 f m)
include S

lemma integrable_indicator_m :
    Integrable ((Icc (t0 - h) (t0 + h)).indicator m) volume :=
  (integrable_indicator_iff measurableSet_Icc).mpr S.m_int

lemma continuous_prim : Continuous (prim t0 h m) :=
  S.integrable_indicator_m.continuous_primitive t0

lemma prim_sub_eq {c d : ℝ} :
    prim t0 h m d - prim t0 h m c =
      ∫ s in c..d, (Icc (t0 - h) (t0 + h)).indicator m s := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (S.integrable_indicator_m.intervalIntegrable (a := t0) (b := c))
    (S.integrable_indicator_m.intervalIntegrable (a := c) (b := d))
  unfold prim
  linarith [h1]

/-- On the base interval, the primitive increments compute `∫ m`. -/
lemma integral_m_eq_prim {c d : ℝ} (hc : c ∈ Icc (t0 - h) (t0 + h))
    (hd : d ∈ Icc (t0 - h) (t0 + h)) :
    (∫ s in c..d, m s) = prim t0 h m d - prim t0 h m c := by
  rw [S.prim_sub_eq]
  refine intervalIntegral.integral_congr fun s hs => ?_
  exact (indicator_of_mem (S.uIcc_subset hc hd hs) m).symm

/-- The core estimate: interval integrals of `f (s, u s)` against a good curve
are controlled by increments of the primitive of `m`. -/
lemma norm_integral_comp_le {u : ℝ → E} (hu : GoodFun x0 b u) {c d : ℝ}
    (hc : c ∈ Icc (t0 - h) (t0 + h)) (hd : d ∈ Icc (t0 - h) (t0 + h)) :
    ‖∫ s in c..d, f s (u s)‖ ≤ |prim t0 h m d - prim t0 h m c| := by
  have key : ∀ c' d' : ℝ, c' ∈ Icc (t0 - h) (t0 + h) → d' ∈ Icc (t0 - h) (t0 + h) →
      c' ≤ d' → ‖∫ s in c'..d', f s (u s)‖ ≤ |prim t0 h m d' - prim t0 h m c'| := by
    intro c' d' hc' hd' hcd
    have hsub : Ioc c' d' ⊆ Icc (t0 - h) (t0 + h) :=
      le_trans Ioc_subset_Icc_self (Icc_subset_Icc hc'.1 hd'.2)
    have hint : IntegrableOn (fun s => f s (u s)) (Ioc c' d') :=
      (S.integrableOn_comp hu).mono_set hsub
    have hmint : IntegrableOn m (Ioc c' d') := S.m_int.mono_set hsub
    have h1 : ‖∫ s in c'..d', f s (u s)‖ ≤ ∫ s in Ioc c' d', ‖f s (u s)‖ := by
      rw [intervalIntegral.integral_of_le hcd]
      exact norm_integral_le_integral_norm _
    have h2 : (∫ s in Ioc c' d', ‖f s (u s)‖) ≤ ∫ s in Ioc c' d', m s := by
      refine setIntegral_mono_ae_restrict hint.norm hmint ?_
      have hb : ∀ᵐ s ∂volume.restrict (Ioc c' d'), ∀ x ∈ closedBall x0 b, ‖f s x‖ ≤ m s :=
        ae_mono (Measure.restrict_mono hsub le_rfl) S.bound
      filter_upwards [hb] with s hs
      exact hs _ (hu.2 s)
    have h3 : (∫ s in Ioc c' d', m s) = prim t0 h m d' - prim t0 h m c' := by
      rw [← intervalIntegral.integral_of_le hcd]
      exact S.integral_m_eq_prim hc' hd'
    calc ‖∫ s in c'..d', f s (u s)‖ ≤ ∫ s in Ioc c' d', m s := le_trans h1 h2
      _ = prim t0 h m d' - prim t0 h m c' := h3
      _ ≤ |prim t0 h m d' - prim t0 h m c'| := le_abs_self _
  rcases le_total c d with hcd | hdc
  · exact key c d hc hd hcd
  · have := key d c hd hc hdc
    rw [intervalIntegral.integral_symm, norm_neg, abs_sub_comm]
    exact this

/-- The primitive is bounded by the total mass, hence by `b`. -/
lemma abs_prim_le (τ : ℝ) : |prim t0 h m τ| ≤ ∫ s in Icc (t0 - h) (t0 + h), m s := by
  have hnn : ∀ s, 0 ≤ (Icc (t0 - h) (t0 + h)).indicator m s := fun s =>
    indicator_nonneg (fun s' _ => S.m_nonneg s') s
  have htotal : ∀ s : Set ℝ, (∫ x in s, (Icc (t0 - h) (t0 + h)).indicator m x) ≤
      ∫ x in Icc (t0 - h) (t0 + h), m x := by
    intro s
    calc (∫ x in s, (Icc (t0 - h) (t0 + h)).indicator m x)
        ≤ ∫ x, (Icc (t0 - h) (t0 + h)).indicator m x :=
          setIntegral_le_integral S.integrable_indicator_m
            (Eventually.of_forall hnn)
      _ = ∫ x in Icc (t0 - h) (t0 + h), m x := integral_indicator measurableSet_Icc
  rcases le_total t0 τ with hle | hge
  · have h0 : 0 ≤ prim t0 h m τ := by
      rw [prim, intervalIntegral.integral_of_le hle]
      exact setIntegral_nonneg measurableSet_Ioc fun s _ => hnn s
    rw [abs_of_nonneg h0, prim, intervalIntegral.integral_of_le hle]
    exact htotal _
  · have h0 : prim t0 h m τ ≤ 0 := by
      rw [prim, intervalIntegral.integral_of_ge hge]
      simp only [neg_nonpos]
      exact setIntegral_nonneg measurableSet_Ioc fun s _ => hnn s
    rw [abs_of_nonpos h0, prim, intervalIntegral.integral_of_ge hge, neg_neg]
    exact htotal _

end Prim

end IsSetup

/-- The delayed integral operator of the Tonelli scheme. -/
noncomputable def delayOp (t0 h δ : ℝ) (x0 : E) (f : ℝ → E → E) (u : ℝ → E) : ℝ → E :=
  fun t => x0 + ∫ s in t0..(delayedProj t0 h δ t), f s (u s)

/-- Iterates of the delayed operator, starting from the constant curve. -/
noncomputable def delayIter (t0 h δ : ℝ) (x0 : E) (f : ℝ → E → E) (k : ℕ) : ℝ → E :=
  (delayOp t0 h δ x0 f)^[k] (fun _ => x0)

lemma delayIter_succ (t0 h δ : ℝ) (x0 : E) (f : ℝ → E → E) (k : ℕ) :
    delayIter t0 h δ x0 f (k + 1) = delayOp t0 h δ x0 f (delayIter t0 h δ x0 f k) := by
  rw [delayIter, delayIter, Function.iterate_succ_apply']

namespace IsSetup

section Iterates

variable (S : IsSetup t0 h b x0 f m)
include S

lemma delayedProj_mem_Icc (hδ : 0 ≤ δ) (t : ℝ) :
    delayedProj t0 h δ t ∈ Icc (t0 - h) (t0 + h) :=
  delayedProj_mem S.h_pos.le hδ t

/-- The operator preserves good curves. -/
lemma goodFun_delayOp (hδ : 0 ≤ δ) {u : ℝ → E} (hu : GoodFun x0 b u) :
    GoodFun x0 b (delayOp t0 h δ x0 f u) := by
  have hcont : Continuous (delayOp t0 h δ x0 f u) := by
    have hind : Integrable ((Icc (t0 - h) (t0 + h)).indicator fun s => f s (u s)) volume :=
      (integrable_indicator_iff measurableSet_Icc).mpr (S.integrableOn_comp hu)
    have heq : delayOp t0 h δ x0 f u = fun t =>
        x0 + ∫ s in t0..(delayedProj t0 h δ t),
          (Icc (t0 - h) (t0 + h)).indicator (fun s' => f s' (u s')) s := by
      funext t
      unfold delayOp
      congr 1
      refine intervalIntegral.integral_congr fun s hs => ?_
      exact (indicator_of_mem
        (S.uIcc_subset S.t0_mem (S.delayedProj_mem_Icc hδ t) hs)
        (fun s' => f s' (u s'))).symm
    rw [heq]
    exact continuous_const.add
      ((hind.continuous_primitive t0).comp (continuous_delayedProj t0 h δ))
  refine ⟨hcont, fun t => ?_⟩
  rw [mem_closedBall, dist_eq_norm]
  have h1 : ‖delayOp t0 h δ x0 f u t - x0‖ =
      ‖∫ s in t0..(delayedProj t0 h δ t), f s (u s)‖ := by
    unfold delayOp; congr 1; abel
  rw [h1]
  calc ‖∫ s in t0..(delayedProj t0 h δ t), f s (u s)‖
      ≤ |prim t0 h m (delayedProj t0 h δ t) - prim t0 h m t0| :=
        S.norm_integral_comp_le hu S.t0_mem (S.delayedProj_mem_Icc hδ t)
    _ = |prim t0 h m (delayedProj t0 h δ t)| := by
        rw [show prim t0 h m t0 = 0 from intervalIntegral.integral_same, sub_zero]
    _ ≤ ∫ s in Icc (t0 - h) (t0 + h), m s := S.abs_prim_le _
    _ ≤ b := S.small

lemma goodFun_delayIter (hδ : 0 ≤ δ) (k : ℕ) : GoodFun x0 b (delayIter t0 h δ x0 f k) := by
  induction k with
  | zero =>
    exact ⟨continuous_const, fun t => mem_closedBall_self S.b_nonneg⟩
  | succ k ih =>
    rw [delayIter, Function.iterate_succ_apply']
    exact S.goodFun_delayOp hδ ih

/-- The bootstrap: successive iterates agree on the region where the delayed
projection has already stabilized. -/
lemma delayIter_agree (hδ : 0 ≤ δ) (j : ℕ) :
    ∀ t, |clampI t0 h t - t0| ≤ j * δ →
      delayIter t0 h δ x0 f (j + 1) t = delayIter t0 h δ x0 f j t := by
  induction j with
  | zero =>
    intro t ht
    have hc : clampI t0 h t = t0 := by
      have h0 : |clampI t0 h t - t0| ≤ 0 := by push_cast at ht; linarith
      have := abs_nonneg (clampI t0 h t - t0)
      have habs : |clampI t0 h t - t0| = 0 := le_antisymm h0 this
      rw [abs_eq_zero] at habs
      linarith [habs]
    have hproj : delayedProj t0 h δ t = t0 := by
      rw [delayedProj, hc, pull_eq_of_ge hδ le_rfl]
      simpa using max_eq_right (by linarith : t0 - δ ≤ t0)
    rw [delayIter_succ]
    show delayOp t0 h δ x0 f (fun _ => x0) t = x0
    unfold delayOp
    rw [hproj]
    simp
  | succ j ih =>
    intro t ht
    have hmemρ : delayedProj t0 h δ t ∈ Icc (t0 - h) (t0 + h) :=
      S.delayedProj_mem_Icc hδ t
    -- every point of the integration range satisfies the inductive smallness
    have hrange : ∀ s ∈ uIcc t0 (delayedProj t0 h δ t),
        |clampI t0 h s - t0| ≤ j * δ := by
      intro s hs
      have h1 : |s - t0| ≤ |delayedProj t0 h δ t - t0| :=
        abs_sub_center_le_of_mem_uIcc hs
      have h2 : |delayedProj t0 h δ t - t0| = max (|clampI t0 h t - t0| - δ) 0 :=
        abs_delayedProj_sub_center hδ t
      have h3 : |s - t0| ≤ j * δ := by
        rw [h2] at h1
        have hjδ : 0 ≤ (j : ℝ) * δ := mul_nonneg (Nat.cast_nonneg j) hδ
        have hmax : max (|clampI t0 h t - t0| - δ) 0 ≤ (j : ℝ) * δ := by
          rw [max_le_iff]
          refine ⟨?_, hjδ⟩
          push_cast at ht
          linarith
        exact le_trans h1 hmax
      have hsI : s ∈ Icc (t0 - h) (t0 + h) := by
        have hρh : |delayedProj t0 h δ t - t0| ≤ h :=
          abs_delayedProj_sub_center_le S.h_pos.le hδ t
        exact mem_Icc_of_mem_uIcc hρh hs
      rw [clampI_of_mem hsI]
      exact h3
    have hcongr : (∫ s in t0..(delayedProj t0 h δ t),
          f s (delayIter t0 h δ x0 f (j + 1) s)) =
        ∫ s in t0..(delayedProj t0 h δ t), f s (delayIter t0 h δ x0 f j s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [ih s (hrange s hs)]
    rw [delayIter_succ t0 h δ x0 f (j + 1)]
    conv_rhs => rw [delayIter_succ]
    unfold delayOp
    rw [hcongr]

end Iterates

end IsSetup

/-- The `k`-th Tonelli approximation: delay `h / (k + 1)`, iterated to
stabilization. -/
noncomputable def tonelli (t0 h : ℝ) (x0 : E) (f : ℝ → E → E) (k : ℕ) : ℝ → E :=
  delayIter t0 h (h / ((k : ℝ) + 1)) x0 f (k + 2)

namespace IsSetup

section Tonelli

variable (S : IsSetup t0 h b x0 f m)
include S

lemma delta_pos (k : ℕ) : 0 < h / ((k : ℝ) + 1) :=
  div_pos S.h_pos (by positivity)

lemma goodFun_tonelli (k : ℕ) : GoodFun x0 b (tonelli t0 h x0 f k) :=
  S.goodFun_delayIter (S.delta_pos k).le (k + 2)

/-- The Tonelli approximation is a genuine fixed point of the delayed operator:
`tonelli k t = x0 + ∫_{t0}^{ρ_k t} f (s, tonelli k s) ds` for every `t`. -/
lemma tonelli_eq (k : ℕ) (t : ℝ) :
    tonelli t0 h x0 f k t =
      x0 + ∫ s in t0..(delayedProj t0 h (h / ((k : ℝ) + 1)) t),
        f s (tonelli t0 h x0 f k s) := by
  have hδ : 0 ≤ h / ((k : ℝ) + 1) := (S.delta_pos k).le
  have hne : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hall : ∀ s, delayIter t0 h (h / ((k : ℝ) + 1)) x0 f (k + 2) s
      = delayIter t0 h (h / ((k : ℝ) + 1)) x0 f (k + 1) s := by
    intro s
    refine S.delayIter_agree hδ (k + 1) s ?_
    have h1 : |clampI t0 h s - t0| ≤ h := abs_clampI_sub_center S.h_pos.le s
    have heq : ((k + 1 : ℕ) : ℝ) * (h / ((k : ℝ) + 1)) = h := by
      push_cast
      rw [mul_comm, div_mul_cancel₀ _ hne]
    rw [heq]
    exact h1
  have h1 : tonelli t0 h x0 f k t = delayOp t0 h (h / ((k : ℝ) + 1)) x0 f
      (delayIter t0 h (h / ((k : ℝ) + 1)) x0 f (k + 1)) t := by
    rw [tonelli, delayIter_succ]
  rw [h1]
  unfold delayOp
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [show delayIter t0 h (h / ((k : ℝ) + 1)) x0 f (k + 1) s
      = tonelli t0 h x0 f k s from (hall s).symm]

/-- Differences of the Tonelli approximation are integrals between the delayed
projections. -/
lemma tonelli_sub (k : ℕ) (t1 t2 : ℝ) :
    tonelli t0 h x0 f k t2 - tonelli t0 h x0 f k t1 =
      ∫ s in (delayedProj t0 h (h / ((k : ℝ) + 1)) t1)..(delayedProj t0 h
        (h / ((k : ℝ) + 1)) t2), f s (tonelli t0 h x0 f k s) := by
  have hδ : 0 ≤ h / ((k : ℝ) + 1) := (S.delta_pos k).le
  have hint : ∀ t : ℝ, IntervalIntegrable (fun s => f s (tonelli t0 h x0 f k s))
      volume t0 (delayedProj t0 h (h / ((k : ℝ) + 1)) t) :=
    fun t => S.intervalIntegrable_comp (S.goodFun_tonelli k) S.t0_mem
      (S.delayedProj_mem_Icc hδ t)
  rw [S.tonelli_eq k t1, S.tonelli_eq k t2]
  have := intervalIntegral.integral_interval_sub_left (hint t2) (hint t1)
  rw [add_sub_add_left_eq_sub, this]

/-- The uniform modulus of continuity for all Tonelli approximations. -/
lemma norm_tonelli_sub_le (k : ℕ) (t1 t2 : ℝ) :
    ‖tonelli t0 h x0 f k t2 - tonelli t0 h x0 f k t1‖ ≤
      |prim t0 h m (delayedProj t0 h (h / ((k : ℝ) + 1)) t2) -
        prim t0 h m (delayedProj t0 h (h / ((k : ℝ) + 1)) t1)| := by
  rw [S.tonelli_sub k t1 t2]
  exact S.norm_integral_comp_le (S.goodFun_tonelli k)
    (S.delayedProj_mem_Icc (S.delta_pos k).le t1)
    (S.delayedProj_mem_Icc (S.delta_pos k).le t2)

end Tonelli

end IsSetup

end

/-
== MODULE ==

Extraction of a solution from the Tonelli approximations.

The approximations `tonelli k` are uniformly bounded (values in the closed
ball) and equicontinuous (their oscillation is controlled by increments of the
primitive of `m`). By Arzelà–Ascoli, a subsequence converges uniformly on
`[t0 - h, t0 + h]`; the delayed fixed-point identity passes to the limit by
dominated convergence, giving a solution of the integral equation.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {t0 h b : ℝ} {x0 : E} {f : ℝ → E → E} {m : ℝ → ℝ}

namespace IsSetup

/-- **Solution of the integral equation on the base interval.** A uniform
subsequential limit of the Tonelli approximations solves
`x t = x0 + ∫_{t0}^t f (s, x s) ds` on `[t0 - h, t0 + h]`. -/
theorem exists_solution (S : IsSetup t0 h b x0 f m) :
    ∃ x : ℝ → E, Continuous x ∧ (∀ t, x t ∈ closedBall x0 b) ∧
      ∀ t ∈ Icc (t0 - h) (t0 + h), x t = x0 + ∫ s in t0..t, f s (x s) := by
  classical
  -- restrict the approximations to the compact base interval
  let F : ℕ → (Icc (t0 - h) (t0 + h) →ᵇ E) := fun k =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun τ => tonelli t0 h x0 f k ↑τ,
        ((S.goodFun_tonelli k).1).comp continuous_subtype_val⟩
  have hFapp : ∀ (k : ℕ) (τ : Icc (t0 - h) (t0 + h)),
      F k τ = tonelli t0 h x0 f k ↑τ := fun k τ => rfl
  -- equicontinuity of the family, from the uniform modulus `prim`
  have hEqui : Equicontinuous fun k : ℕ => (F k : Icc (t0 - h) (t0 + h) → E) := by
    intro τ0
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    have huc : UniformContinuousOn (prim t0 h m) (Icc (t0 - h) (t0 + h)) :=
      isCompact_Icc.uniformContinuousOn_of_continuous S.continuous_prim.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨d, hd, hduc⟩ := huc ε hε
    refine ⟨d, hd, fun τ hτ k => ?_⟩
    have hδ : 0 ≤ h / ((k : ℝ) + 1) := (S.delta_pos k).le
    have hmem1 : delayedProj t0 h (h / ((k : ℝ) + 1)) ↑τ ∈ Icc (t0 - h) (t0 + h) :=
      S.delayedProj_mem_Icc hδ _
    have hmem0 : delayedProj t0 h (h / ((k : ℝ) + 1)) ↑τ0 ∈ Icc (t0 - h) (t0 + h) :=
      S.delayedProj_mem_Icc hδ _
    have hclose : dist (delayedProj t0 h (h / ((k : ℝ) + 1)) ↑τ)
        (delayedProj t0 h (h / ((k : ℝ) + 1)) ↑τ0) < d := by
      rw [Real.dist_eq]
      calc |delayedProj t0 h (h / ((k : ℝ) + 1)) ↑τ -
            delayedProj t0 h (h / ((k : ℝ) + 1)) ↑τ0| ≤ |(↑τ : ℝ) - ↑τ0| :=
            abs_delayedProj_sub_delayedProj t0 h _ ↑τ ↑τ0
        _ = dist τ τ0 := by rw [Subtype.dist_eq, Real.dist_eq]
        _ < d := hτ
    calc dist (F k τ0) (F k τ)
        = ‖tonelli t0 h x0 f k ↑τ0 - tonelli t0 h x0 f k ↑τ‖ := by
          rw [hFapp, hFapp, dist_eq_norm]
      _ ≤ |prim t0 h m (delayedProj t0 h (h / ((k : ℝ) + 1)) ↑τ0) -
            prim t0 h m (delayedProj t0 h (h / ((k : ℝ) + 1)) ↑τ)| :=
          S.norm_tonelli_sub_le k ↑τ ↑τ0
      _ = dist (prim t0 h m (delayedProj t0 h (h / ((k : ℝ) + 1)) ↑τ0))
            (prim t0 h m (delayedProj t0 h (h / ((k : ℝ) + 1)) ↑τ)) :=
          (Real.dist_eq _ _).symm
      _ < ε := hduc _ hmem0 _ hmem1 (by rwa [dist_comm])
  -- Arzelà–Ascoli and subsequence extraction
  have hin_s : ∀ (g : Icc (t0 - h) (t0 + h) →ᵇ E) (τ : Icc (t0 - h) (t0 + h)),
      g ∈ Set.range F → g τ ∈ closedBall x0 b := by
    rintro g τ ⟨k, rfl⟩
    exact (S.goodFun_tonelli k).2 ↑τ
  have hAe : Equicontinuous ((↑) : Set.range F → Icc (t0 - h) (t0 + h) → E) := by
    intro τ0 U hU
    filter_upwards [hEqui τ0 U hU] with τ hτ
    rintro ⟨g, k, rfl⟩
    exact hτ k
  have hcomp : IsCompact (closure (Set.range F)) :=
    arzela_ascoli (closedBall x0 b) (isCompact_closedBall x0 b) (Set.range F) hin_s hAe
  obtain ⟨xhat, -, φ, hφ, htend⟩ :=
    hcomp.tendsto_subseq fun k => subset_closure (Set.mem_range_self k)
  have htu : TendstoUniformly (fun k => (F (φ k) : Icc (t0 - h) (t0 + h) → E))
      (xhat : Icc (t0 - h) (t0 + h) → E) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htend
  -- the limit curve, extended to `ℝ` by clamping
  set x : ℝ → E := fun t => xhat ⟨clampI t0 h t, clampI_mem S.h_pos.le t⟩ with hxdef
  have hxcont : Continuous x :=
    xhat.continuous.comp (((lipschitzWith_clampI t0 h).continuous).subtype_mk _)
  have hxhat_ball : ∀ τ : Icc (t0 - h) (t0 + h), xhat τ ∈ closedBall x0 b := fun τ =>
    isClosed_closedBall.mem_of_tendsto (htu.tendsto_at τ)
      (Eventually.of_forall fun k => (S.goodFun_tonelli (φ k)).2 ↑τ)
  have hxball : ∀ t, x t ∈ closedBall x0 b := fun t => hxhat_ball _
  have hxeq : ∀ t (ht : t ∈ Icc (t0 - h) (t0 + h)), x t = xhat ⟨t, ht⟩ := by
    intro t ht
    rw [hxdef]
    exact congrArg xhat (Subtype.ext (clampI_of_mem ht))
  -- pointwise convergence on the base interval
  have hptw : ∀ t (ht : t ∈ Icc (t0 - h) (t0 + h)),
      Tendsto (fun k => tonelli t0 h x0 f (φ k) t) atTop (𝓝 (x t)) := by
    intro t ht
    rw [hxeq t ht]
    have := htu.tendsto_at ⟨t, ht⟩
    simpa [hFapp] using this
  refine ⟨x, hxcont, hxball, fun t ht => ?_⟩
  -- pass to the limit in the fixed-point identity at the point `t`
  have hsub : Ι t0 t ⊆ Icc (t0 - h) (t0 + h) :=
    le_trans uIoc_subset_uIcc (S.uIcc_subset S.t0_mem ht)
  -- the delayed projections at `t` converge to `t`
  have hδbase : Tendsto (fun n : ℕ => h / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul h
    simpa only [one_div, one_mul, mul_zero, div_eq_mul_inv] using this
  have hρtend : Tendsto (fun k => delayedProj t0 h (h / ((φ k : ℝ) + 1)) t) atTop (𝓝 t) := by
    have hzero : Tendsto (fun k => delayedProj t0 h (h / ((φ k : ℝ) + 1)) t - t) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (hδbase.comp hφ.tendsto_atTop)
      exact abs_delayedProj_sub_self (S.delta_pos (φ k)).le ht
    simpa using hzero.add_const t
  have hprim_tend : Tendsto
      (fun k => prim t0 h m (delayedProj t0 h (h / ((φ k : ℝ) + 1)) t)) atTop
      (𝓝 (prim t0 h m t)) := (S.continuous_prim.tendsto t).comp hρtend
  -- the tail integrals vanish
  have htail_tend : Tendsto
      (fun k => ∫ s in (delayedProj t0 h (h / ((φ k : ℝ) + 1)) t)..t,
        f s (tonelli t0 h x0 f (φ k) s)) atTop (𝓝 0) := by
    refine squeeze_zero_norm
      (a := fun k => |prim t0 h m t -
        prim t0 h m (delayedProj t0 h (h / ((φ k : ℝ) + 1)) t)|)
      (fun k => ?_) ?_
    · exact S.norm_integral_comp_le (S.goodFun_tonelli (φ k))
        (S.delayedProj_mem_Icc (S.delta_pos (φ k)).le t) ht
    · have h1 : Tendsto (fun k => prim t0 h m t -
          prim t0 h m (delayedProj t0 h (h / ((φ k : ℝ) + 1)) t)) atTop
          (𝓝 (prim t0 h m t - prim t0 h m t)) :=
        tendsto_const_nhds.sub hprim_tend
      rw [sub_self] at h1
      simpa using h1.abs
  -- dominated convergence for the main integrals
  have hmain_tend : Tendsto
      (fun k => ∫ s in t0..t, f s (tonelli t0 h x0 f (φ k) s)) atTop
      (𝓝 (∫ s in t0..t, f s (x s))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence m
      (Eventually.of_forall fun k => ?_) (Eventually.of_forall fun k => ?_) ?_ ?_
    · exact (aestronglyMeasurable_comp_of_continuous _ S.meas S.cont
        (S.goodFun_tonelli (φ k)).1 (S.goodFun_tonelli (φ k)).2).mono_measure
        (Measure.restrict_mono hsub le_rfl)
    · have hb := (ae_restrict_iff' measurableSet_Icc).mp S.bound
      filter_upwards [hb] with s hs hmem
      exact hs (hsub hmem) _ ((S.goodFun_tonelli (φ k)).2 s)
    · exact S.intervalIntegrable_m S.t0_mem ht
    · have hc := (ae_restrict_iff' measurableSet_Icc).mp S.cont
      filter_upwards [hc] with s hs hmem
      have hsI : s ∈ Icc (t0 - h) (t0 + h) := hsub hmem
      have h1 : Tendsto (fun k => tonelli t0 h x0 f (φ k) s) atTop
          (𝓝[closedBall x0 b] (x s)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨hptw s hsI, Eventually.of_forall fun k => (S.goodFun_tonelli (φ k)).2 s⟩
      exact ((hs hsI (x s) (hxball s)).tendsto).comp h1
  -- split the fixed-point identity and pass to the limit
  have hsplit : ∀ k, tonelli t0 h x0 f (φ k) t =
      x0 + ((∫ s in t0..t, f s (tonelli t0 h x0 f (φ k) s)) -
        ∫ s in (delayedProj t0 h (h / ((φ k : ℝ) + 1)) t)..t,
          f s (tonelli t0 h x0 f (φ k) s)) := by
    intro k
    have hδ : 0 ≤ h / ((φ k : ℝ) + 1) := (S.delta_pos (φ k)).le
    have hint1 : IntervalIntegrable (fun s => f s (tonelli t0 h x0 f (φ k) s)) volume t0 t :=
      S.intervalIntegrable_comp (S.goodFun_tonelli (φ k)) S.t0_mem ht
    have hint2 : IntervalIntegrable (fun s => f s (tonelli t0 h x0 f (φ k) s)) volume t0
        (delayedProj t0 h (h / ((φ k : ℝ) + 1)) t) :=
      S.intervalIntegrable_comp (S.goodFun_tonelli (φ k)) S.t0_mem
        (S.delayedProj_mem_Icc hδ t)
    have hsubst := intervalIntegral.integral_interval_sub_left hint1 hint2
    rw [S.tonelli_eq (φ k) t]
    congr 1
    rw [← hsubst]
    abel
  have hLHS : Tendsto (fun k => tonelli t0 h x0 f (φ k) t) atTop (𝓝 (x t)) := hptw t ht
  have hRHS : Tendsto (fun k => tonelli t0 h x0 f (φ k) t) atTop
      (𝓝 (x0 + ((∫ s in t0..t, f s (x s)) - 0))) := by
    rw [funext hsplit]
    exact tendsto_const_nhds.add (hmain_tend.sub htail_tend)
  have := tendsto_nhds_unique hLHS hRHS
  simpa using this

end IsSetup

end

/-
== MODULE ==

# The Carathéodory existence theorem

Let `f : [t0 - a, t0 + a] × closedBall x0 b → ℝ^n` satisfy

1. for every fixed `x` in the ball, `t ↦ f t x` is measurable;
2. for almost every fixed `t`, `x ↦ f t x` is continuous on the ball;
3. `‖f t x‖ ≤ m t` for a.e. `t` and every `x` in the ball, with `m` integrable.

Then there is `0 < h ≤ a` and an absolutely continuous
`x : [t0 - h, t0 + h] → ℝ^n` with `x t0 = x0`, satisfying the integral
equation `x t = x0 + ∫_{t0}^t f (s, x s) ds` (this is the absolute-continuity
statement) and hence `x' t = f t (x t)` for almost every `t`.

The solution is obtained as a uniform subsequential limit of the Tonelli
delayed approximations (`Caratheodory.Limit`); the almost-everywhere
derivative comes from the Lebesgue differentiation theorem applied
coordinatewise in a basis of `E`.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {t0 h b : ℝ} {x0 : E} {f : ℝ → E → E} {m : ℝ → ℝ}

/-- Almost every real number differs from a given constant. -/
private lemma ae_ne_const (c : ℝ) : ∀ᵐ τ : ℝ, τ ≠ c := by
  rw [ae_iff]
  have hset : {τ : ℝ | ¬τ ≠ c} = {c} := by ext τ; simp
  rw [hset]
  exact measure_singleton c

/-- Any solution of the integral equation is differentiable almost everywhere
with derivative `f t (x t)`, by the Lebesgue differentiation theorem applied
coordinatewise. -/
theorem IsSetup.ae_hasDerivAt (S : IsSetup t0 h b x0 f m) {x : ℝ → E}
    (hxcont : Continuous x) (hxball : ∀ t, x t ∈ closedBall x0 b)
    (hxeq : ∀ t ∈ Icc (t0 - h) (t0 + h), x t = x0 + ∫ s in t0..t, f s (x s)) :
    ∀ᵐ t ∂volume.restrict (Icc (t0 - h) (t0 + h)), HasDerivAt x (f t (x t)) t := by
  classical
  set g : ℝ → E := fun s => f s (x s) with hg
  have hgood : GoodFun x0 b x := ⟨hxcont, hxball⟩
  have huIcc : uIcc (t0 - h) (t0 + h) = Icc (t0 - h) (t0 + h) :=
    uIcc_of_le (by linarith [S.h_pos])
  have hgInt : IntervalIntegrable g volume (t0 - h) (t0 + h) := by
    rw [intervalIntegrable_iff]
    refine (S.integrableOn_comp hgood).mono_set ?_
    rw [← huIcc]
    exact uIoc_subset_uIcc
  -- coordinates with respect to a continuous linear identification with `ℝ^n`
  set n : ℕ := Module.finrank ℝ E with hn
  set e : E ≃L[ℝ] (Fin n → ℝ) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv with he
  set L : Fin n → (E →L[ℝ] ℝ) := fun i =>
    (ContinuousLinearMap.proj i).comp (e : E →L[ℝ] (Fin n → ℝ)) with hL
  have hLg : ∀ i, IntervalIntegrable (fun s => L i (g s)) volume (t0 - h) (t0 + h) := by
    intro i
    rw [intervalIntegrable_iff] at hgInt ⊢
    exact (L i).integrable_comp hgInt
  have hFTC : ∀ᵐ τ ∂volume, ∀ i : Fin n, τ ∈ uIcc (t0 - h) (t0 + h) →
      ∀ c ∈ uIcc (t0 - h) (t0 + h),
        HasDerivAt (fun u => ∫ s in c..u, L i (g s)) (L i (g τ)) τ :=
    ae_all_iff.mpr fun i => (hLg i).ae_hasDerivAt_integral
  have hne1 : ∀ᵐ τ : ℝ, τ ≠ t0 - h := ae_ne_const _
  have hne2 : ∀ᵐ τ : ℝ, τ ≠ t0 + h := ae_ne_const _
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hFTC, hne1, hne2] with τ hτFTC hτ1 hτ2 hτI
  have hlt1 : t0 - h < τ := lt_of_le_of_ne hτI.1 (Ne.symm hτ1)
  have hlt2 : τ < t0 + h := lt_of_le_of_ne hτI.2 hτ2
  -- coordinatewise derivatives
  have hcoord : ∀ i : Fin n, HasDerivAt (fun u => L i (x u)) (L i (g τ)) τ := by
    intro i
    have hi := hτFTC i (huIcc ▸ hτI) t0 (huIcc ▸ S.t0_mem)
    have heq : (fun u => L i (x u)) =ᶠ[𝓝 τ]
        fun u => L i x0 + ∫ s in t0..u, L i (g s) := by
      filter_upwards [Ioo_mem_nhds hlt1 hlt2] with u hu
      have hu' : u ∈ Icc (t0 - h) (t0 + h) := Ioo_subset_Icc_self hu
      have hgu : IntervalIntegrable g volume t0 u :=
        S.intervalIntegrable_comp hgood S.t0_mem hu'
      rw [hxeq u hu', map_add, ← (L i).intervalIntegral_comp_comm hgu]
    have hconst : HasDerivAt (fun u => L i x0 + ∫ s in t0..u, L i (g s))
        (L i (g τ)) τ := hi.const_add _
    exact hconst.congr_of_eventuallyEq heq
  -- assemble the coordinates and transfer back through the identification
  have hPi : HasDerivAt (fun u => e (x u)) (e (g τ)) τ := by
    rw [hasDerivAt_pi]
    intro i
    exact hcoord i
  have h2 : HasDerivAt (fun u => e.symm (e (x u))) (e.symm (e (g τ))) τ :=
    (e.symm.hasFDerivAt).comp_hasDerivAt τ hPi
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h2
  exact h2

/-- Shrinking the time interval makes the mass of `m` as small as desired. -/
lemma exists_shrink (t0 : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m : ℝ → ℝ}
    (hm : IntegrableOn m (Icc (t0 - a) (t0 + a))) :
    ∃ h : ℝ, 0 < h ∧ h ≤ a ∧ ∫ s in Icc (t0 - h) (t0 + h), |m s| ≤ b := by
  classical
  set ν := volume.restrict (Icc (t0 - a) (t0 + a)) with hν
  have habs_int : Integrable (fun s => |m s|) ν := hm.abs
  have hsubn : ∀ n : ℕ,
      Icc (t0 - a / ((n : ℝ) + 1)) (t0 + a / ((n : ℝ) + 1)) ⊆ Icc (t0 - a) (t0 + a) := by
    intro n
    have hle : a / ((n : ℝ) + 1) ≤ a := div_le_self ha.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact Icc_subset_Icc (by linarith) (by linarith)
  -- the integrals over the shrinking intervals tend to `0`
  have hbound : ∀ k : ℕ, ∀ᵐ s ∂ν,
      ‖(Icc (t0 - a / ((k : ℝ) + 1)) (t0 + a / ((k : ℝ) + 1))).indicator
        (fun s' => |m s'|) s‖ ≤ |m s| := by
    intro k
    refine Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs,
      abs_of_nonneg (indicator_nonneg (fun s' _ => abs_nonneg (m s')) s)]
    exact Set.indicator_le_self' (fun s' _ => abs_nonneg (m s')) s
  have hlim : ∀ᵐ s ∂ν, Tendsto (fun k : ℕ =>
      (Icc (t0 - a / ((k : ℝ) + 1)) (t0 + a / ((k : ℝ) + 1))).indicator
        (fun s' => |m s'|) s) atTop (𝓝 0) := by
    have hne : ∀ᵐ s ∂ν, s ≠ t0 :=
      ae_mono Measure.restrict_le_self (ae_ne_const t0)
    filter_upwards [hne] with s hs
    have hpos : 0 < |s - t0| := abs_pos.mpr (sub_ne_zero.mpr hs)
    obtain ⟨N, hN⟩ := exists_nat_gt (a / |s - t0|)
    have hev : ∀ᶠ k : ℕ in atTop,
        (Icc (t0 - a / ((k : ℝ) + 1)) (t0 + a / ((k : ℝ) + 1))).indicator
          (fun s' => |m s'|) s = 0 := by
      rw [eventually_atTop]
      refine ⟨N, fun k hk => indicator_of_notMem ?_ _⟩
      intro hmem
      have h1 : |s - t0| ≤ a / ((k : ℝ) + 1) :=
        abs_le.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      have hk' : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
      have h2 : a / |s - t0| < (k : ℝ) + 1 := by linarith
      have h3 : a < ((k : ℝ) + 1) * |s - t0| := by
        rwa [div_lt_iff₀ hpos] at h2
      have h4 : a / ((k : ℝ) + 1) < |s - t0| := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1), mul_comm]
        exact h3
      linarith
    exact Tendsto.congr' (hev.mono fun k hk => hk.symm) tendsto_const_nhds
  have htend : Tendsto (fun k : ℕ =>
      ∫ s, (Icc (t0 - a / ((k : ℝ) + 1)) (t0 + a / ((k : ℝ) + 1))).indicator
        (fun s' => |m s'|) s ∂ν) atTop (𝓝 0) := by
    have hmain := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun k s => (Icc (t0 - a / ((k : ℝ) + 1))
        (t0 + a / ((k : ℝ) + 1))).indicator (fun s' => |m s'|) s)
      (f := fun _ => (0 : ℝ)) (fun s => |m s|)
      (fun k => habs_int.aestronglyMeasurable.indicator measurableSet_Icc)
      habs_int hbound hlim
    simpa using hmain
  -- rewrite as set integrals over the shrinking intervals
  have hseq : ∀ k : ℕ,
      (∫ s, (Icc (t0 - a / ((k : ℝ) + 1)) (t0 + a / ((k : ℝ) + 1))).indicator
        (fun s' => |m s'|) s ∂ν) =
      ∫ s in Icc (t0 - a / ((k : ℝ) + 1)) (t0 + a / ((k : ℝ) + 1)), |m s| := by
    intro k
    rw [integral_indicator measurableSet_Icc, hν,
      Measure.restrict_restrict measurableSet_Icc,
      inter_eq_self_of_subset_left (hsubn k)]
  rw [funext hseq] at htend
  obtain ⟨k, hk⟩ := (htend.eventually_lt_const hb).exists
  exact ⟨a / ((k : ℝ) + 1), by positivity,
    div_le_self ha.le (by linarith [Nat.cast_nonneg (α := ℝ) k]), hk.le⟩

/-- **Carathéodory existence theorem.** Let `f` be defined on
`[t0 - a, t0 + a] × closedBall x0 b` with values in a finite-dimensional real
normed space, such that

* `t ↦ f t x` is (a.e. strongly) measurable for every `x` in the ball,
* `x ↦ f t x` is continuous on the ball for a.e. `t`,
* `‖f t x‖ ≤ m t` for a.e. `t` and all `x` in the ball, with `m` integrable.

Then there are `0 < h ≤ a` and a continuous curve `x` with `x t0 = x0`,
taking values in the closed ball on `[t0 - h, t0 + h]`, satisfying the
integral equation `x t = x0 + ∫_{t0}^t f (s, x s) ds` there (in particular `x`
is absolutely continuous), and hence `x' t = f t (x t)` for almost every
`t ∈ [t0 - h, t0 + h]`. -/
theorem caratheodory_existence (t0 : ℝ) (x0 : E) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {f : ℝ → E → E} {m : ℝ → ℝ}
    (hf_meas : ∀ x ∈ closedBall x0 b, AEStronglyMeasurable (fun t => f t x)
      (volume.restrict (Icc (t0 - a) (t0 + a))))
    (hf_cont : ∀ᵐ t ∂volume.restrict (Icc (t0 - a) (t0 + a)),
      ContinuousOn (f t) (closedBall x0 b))
    (hm_int : IntegrableOn m (Icc (t0 - a) (t0 + a)))
    (hf_bound : ∀ᵐ t ∂volume.restrict (Icc (t0 - a) (t0 + a)),
      ∀ x ∈ closedBall x0 b, ‖f t x‖ ≤ m t) :
    ∃ h : ℝ, 0 < h ∧ h ≤ a ∧ ∃ x : ℝ → E, Continuous x ∧ x t0 = x0 ∧
      (∀ t ∈ Icc (t0 - h) (t0 + h), x t ∈ closedBall x0 b) ∧
      (∀ t ∈ Icc (t0 - h) (t0 + h), x t = x0 + ∫ s in t0..t, f s (x s)) ∧
      ∀ᵐ t ∂volume.restrict (Icc (t0 - h) (t0 + h)), HasDerivAt x (f t (x t)) t := by
  obtain ⟨h, hh_pos, hha, hsmall⟩ := exists_shrink t0 ha hb hm_int
  have hsub : Icc (t0 - h) (t0 + h) ⊆ Icc (t0 - a) (t0 + a) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hmono : volume.restrict (Icc (t0 - h) (t0 + h)) ≤
      volume.restrict (Icc (t0 - a) (t0 + a)) :=
    Measure.restrict_mono hsub le_rfl
  have S : IsSetup t0 h b x0 f (fun s => |m s|) :=
    { h_pos := hh_pos
      b_nonneg := hb.le
      meas := fun x hx => (hf_meas x hx).mono_measure hmono
      cont := ae_mono hmono hf_cont
      m_nonneg := fun s => abs_nonneg _
      m_int := (hm_int.mono_set hsub).abs
      bound := by
        filter_upwards [ae_mono hmono hf_bound] with t ht x hx
        exact le_trans (ht x hx) (le_abs_self _)
      small := hsmall }
  obtain ⟨x, hxcont, hxball, hxeq⟩ := S.exists_solution
  refine ⟨h, hh_pos, hha, x, hxcont, ?_, fun t _ => hxball t, hxeq,
    S.ae_hasDerivAt hxcont hxball hxeq⟩
  have := hxeq t0 S.t0_mem
  simpa using this

end

end CaratheodoryFull
