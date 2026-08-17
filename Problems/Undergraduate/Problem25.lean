import Mathlib
import PDE.Basics.Laplace.FundamentalSolutionND
import PDE.Basics.Heat.HeatMaximumPrincipleND

/-!
# Undergraduate Problem 25: The Green's Function of the Laplacian on the First Quadrant

Source: `pde_latex/problems/undergraduate/problem_25.tex` (Math 418 Fall 2022,
HW-8, Problem 2).

## Informal statement

> Find the Green's function for the Laplacian on the first quadrant in `ℝ²`.

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem25.tex`:

* The ambient space is `Heat.E 2 = EuclideanSpace ℝ (Fin 2)`; the open
  first quadrant is `Ω = {x | 0 < x 0 ∧ 0 < x 1}` (hypotheses are carried
  pointwise, no set is introduced).
* `Φ₂` is the project's dimension-parametric fundamental solution
  `Laplace.fundamentalSolution 2` (`PDE/Basics/Laplace/FundamentalSolutionND.lean`,
  blueprint `def:fundamentalSolutionND`); by
  `Laplace.fundamentalSolution_two` it is the logarithmic kernel
  `(1/(2π)) log ‖·‖`.
* The three image poles of `y = (y₁, y₂)` follow the source's four-image
  sign pattern: `y₁* = (-y₁, y₂)` and `y₃* = (y₁, -y₂)` (single reflections,
  entering with sign `−`) and `y₂* = (-y₁, -y₂)` (double reflection,
  entering with sign `+`), so
  `G(x, y) = Φ₂(x−y) − Φ₂(x−y₁*) − Φ₂(x−y₃*) + Φ₂(x−y₂*)`.
* The formalization is a definition verification in the decomposition sense:
  `G = Φ₂(x−y) + h(x,y)` with `h` the image corrector
  (`lem:problem25-corrector-harmonic`: `Δ h(·,y) = 0` on the closed quadrant,
  via `Laplace.laplacian_fundamentalSolution_eq_zero` transported by
  `Laplace.laplacian_comp_smul_sub_eq_zero` at `c = 1`), and `G(·,y) = 0` on
  both boundary half-axes (`thm:problem25-boundary-vanish`, pairwise
  cancellation of equal-norm log terms). The distributional pole condition
  `Δ_x G = δ_y` is out of scope for this chapter.
-/

open Set
open scoped ContDiff

namespace Problems.Undergraduate.Problem25

/-! ## The reflected image poles -/

/-- **First image pole** (blueprint `def:problem25-reflections`):
`y₁* = (-y₁, y₂)`, the reflection of `y` across the vertical axis. -/
def reflect1 (y : Heat.E 2) : Heat.E 2 := !₂[-(y 0), y 1]

/-- **Second image pole** (blueprint `def:problem25-reflections`):
`y₂* = (-y₁, -y₂)`, the reflection of `y` through the origin
(the composition of the two axis reflections). -/
def reflect2 (y : Heat.E 2) : Heat.E 2 := !₂[-(y 0), -(y 1)]

/-- **Third image pole** (blueprint `def:problem25-reflections`):
`y₃* = (y₁, -y₂)`, the reflection of `y` across the horizontal axis. -/
def reflect3 (y : Heat.E 2) : Heat.E 2 := !₂[y 0, -(y 1)]

@[simp] lemma reflect1_apply_zero (y : Heat.E 2) : reflect1 y 0 = -(y 0) := rfl

@[simp] lemma reflect1_apply_one (y : Heat.E 2) : reflect1 y 1 = y 1 := rfl

@[simp] lemma reflect2_apply_zero (y : Heat.E 2) : reflect2 y 0 = -(y 0) := rfl

@[simp] lemma reflect2_apply_one (y : Heat.E 2) : reflect2 y 1 = -(y 1) := rfl

@[simp] lemma reflect3_apply_zero (y : Heat.E 2) : reflect3 y 0 = y 0 := rfl

@[simp] lemma reflect3_apply_one (y : Heat.E 2) : reflect3 y 1 = -(y 1) := rfl

/-! ## The corrector and the candidate Green's function -/

/-- **The image corrector** (blueprint `def:problem25-corrector`):
`h(x, y) = -Φ₂(x - y₁*) - Φ₂(x - y₃*) + Φ₂(x - y₂*)`. The signs follow the
parity of the number of reflections. -/
noncomputable def corrector (x y : Heat.E 2) : ℝ :=
  -Laplace.fundamentalSolution 2 (x - reflect1 y)
    - Laplace.fundamentalSolution 2 (x - reflect3 y)
    + Laplace.fundamentalSolution 2 (x - reflect2 y)

/-- **The candidate Green's function of the first quadrant**
(blueprint `def:problem25-greens`):
`G(x, y) = Φ₂(x - y) + h(x, y)
         = Φ₂(x - y) - Φ₂(x - y₁*) - Φ₂(x - y₃*) + Φ₂(x - y₂*)`. -/
noncomputable def G (x y : Heat.E 2) : ℝ :=
  Laplace.fundamentalSolution 2 (x - y) + corrector x y

/-! ## Harmonicity of the corrector -/

/-- Each translate `x' ↦ Φ₂(x' - p)` is `C²` at any `x` with `x - p ≠ 0`
(smoothness of `Φ₂` away from the origin composed with the translation). -/
lemma contDiffAt_translate {x p : Heat.E 2} (hp : x - p ≠ 0) :
    ContDiffAt ℝ 2 (fun x' => Laplace.fundamentalSolution 2 (x' - p)) x := by
  have hΦ : ContDiffAt ℝ ∞ (Laplace.fundamentalSolution 2) (x - p) :=
    (Laplace.contDiffOn_fundamentalSolution le_rfl).contDiffAt
      (isOpen_ne.mem_nhds hp)
  have hsub : ContDiffAt ℝ ∞ (fun x' : Heat.E 2 => x' - p) x :=
    contDiffAt_id.sub contDiffAt_const
  exact contDiffAt_infty.mp (hΦ.comp x hsub) 2

/-- Each translate `x' ↦ Φ₂(x' - p)` is harmonic at any `x` with `x - p ≠ 0`
(harmonicity of `Φ₂` transported through the scaled translate at `c = 1`). -/
lemma laplacian_translate_eq_zero {x p : Heat.E 2} (hp : x - p ≠ 0) :
    Heat.laplacian (fun x' => Laplace.fundamentalSolution 2 (x' - p)) x = 0 := by
  have h0 : Heat.laplacian (Laplace.fundamentalSolution 2) ((1 : ℝ) • (x - p)) = 0 := by
    rw [one_smul]
    exact Laplace.laplacian_fundamentalSolution_eq_zero le_rfl hp
  have h := Laplace.laplacian_comp_smul_sub_eq_zero
    (Laplace.fundamentalSolution 2) one_ne_zero p x h0
  simpa [one_smul] using h

/-- **The corrector is harmonic on the (closed) quadrant**
(blueprint `lem:problem25-corrector-harmonic`): for a pole `y` in the open
first quadrant and any `x` in the closed quadrant, `Δ(h(·, y))(x) = 0`. -/
theorem laplacian_corrector_eq_zero (y : Heat.E 2)
    (hy1 : 0 < y 0) (hy2 : 0 < y 1)
    (x : Heat.E 2) (hx1 : 0 ≤ x 0) (hx2 : 0 ≤ x 1) :
    Heat.laplacian (fun x' => corrector x' y) x = 0 := by
  -- Step 1: the three image poles avoid `x`.
  have h1 : x - reflect1 y ≠ 0 := by
    intro h
    have h0 : (x - reflect1 y) 0 = 0 := by rw [h]; rfl
    rw [PiLp.sub_apply, reflect1_apply_zero, sub_neg_eq_add] at h0
    linarith
  have h2 : x - reflect2 y ≠ 0 := by
    intro h
    have h0 : (x - reflect2 y) 0 = 0 := by rw [h]; rfl
    rw [PiLp.sub_apply, reflect2_apply_zero, sub_neg_eq_add] at h0
    linarith
  have h3 : x - reflect3 y ≠ 0 := by
    intro h
    have h0 : (x - reflect3 y) 1 = 0 := by rw [h]; rfl
    rw [PiLp.sub_apply, reflect3_apply_one, sub_neg_eq_add] at h0
    linarith
  -- Step 2: each translate is `C²` and harmonic at `x`.
  have s1 := contDiffAt_translate h1
  have s2 := contDiffAt_translate h2
  have s3 := contDiffAt_translate h3
  -- Step 3: additivity of the Laplacian.
  have hfun : (fun x' => corrector x' y) =
      fun x' => (-Laplace.fundamentalSolution 2 (x' - reflect1 y) +
        -Laplace.fundamentalSolution 2 (x' - reflect3 y)) +
        Laplace.fundamentalSolution 2 (x' - reflect2 y) := by
    funext x'
    simp only [corrector]
    ring
  rw [hfun,
    Heat.laplacian_add 2
      (fun x' => -Laplace.fundamentalSolution 2 (x' - reflect1 y) +
        -Laplace.fundamentalSolution 2 (x' - reflect3 y))
      (fun x' => Laplace.fundamentalSolution 2 (x' - reflect2 y)) x
      (s1.neg.add s3.neg) s2,
    Heat.laplacian_add 2
      (fun x' => -Laplace.fundamentalSolution 2 (x' - reflect1 y))
      (fun x' => -Laplace.fundamentalSolution 2 (x' - reflect3 y)) x
      s1.neg s3.neg,
    Heat.laplacian_neg 2 (fun x' => Laplace.fundamentalSolution 2 (x' - reflect1 y)) x,
    Heat.laplacian_neg 2 (fun x' => Laplace.fundamentalSolution 2 (x' - reflect3 y)) x,
    laplacian_translate_eq_zero h1, laplacian_translate_eq_zero h2,
    laplacian_translate_eq_zero h3]
  ring

/-! ## Vanishing on the boundary -/

/-- **Zero boundary data on both half-axes**
(blueprint `thm:problem25-boundary-vanish`): for every pole `y` and every
boundary point `x` (i.e. `x 0 = 0` or `x 1 = 0`), `G(x, y) = 0`. The four
log terms cancel in pairs of equal norm. -/
theorem G_eq_zero_boundary (y x : Heat.E 2) (hx : x 0 = 0 ∨ x 1 = 0) :
    G x y = 0 := by
  -- `Φ₂` depends on its argument only through the norm.
  have Φcongr : ∀ v w : Heat.E 2, ‖v‖ = ‖w‖ →
      Laplace.fundamentalSolution 2 v = Laplace.fundamentalSolution 2 w := by
    intro v w hvw
    rw [Laplace.fundamentalSolution_two, Laplace.fundamentalSolution_two, hvw]
  -- norms agree as soon as the coordinate squares agree
  have hnorm : ∀ v w : Heat.E 2,
      (v 0) ^ 2 + (v 1) ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 → ‖v‖ = ‖w‖ := by
    intro v w hvw
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two,
      Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [hvw]
  rcases hx with h | h
  · -- Case `x 0 = 0`: pair `y ↔ y₁*` and `y₃* ↔ y₂*` (flip the first coordinate).
    have e1 : Laplace.fundamentalSolution 2 (x - y) =
        Laplace.fundamentalSolution 2 (x - reflect1 y) := by
      refine Φcongr _ _ (hnorm _ _ ?_)
      simp only [PiLp.sub_apply, reflect1_apply_zero, reflect1_apply_one, h]
      ring
    have e2 : Laplace.fundamentalSolution 2 (x - reflect3 y) =
        Laplace.fundamentalSolution 2 (x - reflect2 y) := by
      refine Φcongr _ _ (hnorm _ _ ?_)
      simp only [PiLp.sub_apply, reflect3_apply_zero, reflect3_apply_one,
        reflect2_apply_zero, reflect2_apply_one, h]
      ring
    simp only [G, corrector, e1, e2]
    ring
  · -- Case `x 1 = 0`: pair `y ↔ y₃*` and `y₁* ↔ y₂*` (flip the second coordinate).
    have e1 : Laplace.fundamentalSolution 2 (x - y) =
        Laplace.fundamentalSolution 2 (x - reflect3 y) := by
      refine Φcongr _ _ (hnorm _ _ ?_)
      simp only [PiLp.sub_apply, reflect3_apply_zero, reflect3_apply_one, h]
      ring
    have e2 : Laplace.fundamentalSolution 2 (x - reflect1 y) =
        Laplace.fundamentalSolution 2 (x - reflect2 y) := by
      refine Φcongr _ _ (hnorm _ _ ?_)
      simp only [PiLp.sub_apply, reflect1_apply_zero, reflect1_apply_one,
        reflect2_apply_zero, reflect2_apply_one, h]
      ring
    simp only [G, corrector, e1, e2]
    ring

/-! ## The verification theorem -/

/-- **Problem 25: the Green's function of the first quadrant**
(blueprint `thm:problem25-greens-function`): for a pole `y` in the open
first quadrant, the candidate `G` verifies the three defining properties of
a Dirichlet Green's function for the Laplacian on the quadrant:
(1) the fundamental-solution-plus-corrector decomposition,
(2) harmonicity of the corrector on the (closed) quadrant, and
(3) zero boundary data on both half-axes. -/
theorem greens_function (y : Heat.E 2) (hy1 : 0 < y 0) (hy2 : 0 < y 1) :
    (∀ x : Heat.E 2,
      G x y = Laplace.fundamentalSolution 2 (x - y) + corrector x y) ∧
    (∀ x : Heat.E 2, 0 ≤ x 0 → 0 ≤ x 1 →
      Heat.laplacian (fun x' => corrector x' y) x = 0) ∧
    (∀ x : Heat.E 2, x 0 = 0 ∨ x 1 = 0 → G x y = 0) :=
  ⟨fun _ => rfl,
    fun x hx1 hx2 => laplacian_corrector_eq_zero y hy1 hy2 x hx1 hx2,
    fun x hx => G_eq_zero_boundary y x hx⟩

end Problems.Undergraduate.Problem25
