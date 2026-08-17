import Mathlib
import PDE.Basics.Laplace.FundamentalSolutionND
import PDE.Basics.Heat.HeatMaximumPrincipleND

/-!
# Undergraduate Problem 21: Green's Functions for the Half Ball and the Quarter Plane

Source: `pde_latex/problems/undergraduate/problem_21.tex` (Math 418/718, HW-10,
Problem 1).

## Informal statement

> (a) Find the Green's function with the Dirichlet boundary condition for the
> half ball `B⁺(0,R) = {x ∈ ℝ³ | |x| < R, x₃ > 0}`.
> (b) Find the Green's function with the Neumann boundary condition for the
> quarter plane `Ω = {(x₁,x₂) ∈ ℝ² | x₁ > 0, x₂ > 0}`.

## Semantic alignment

Per the blueprint chapter `Problems_Undergraduate_Problem21.tex`:

* The ambient spaces are `Heat.E 3` (part (a)) and `Heat.E 2`
  (part (b)); `Φ_N` is the dimension-parametric fundamental solution
  `Laplace.fundamentalSolution N` (blueprint `def:fundamentalSolutionND`).
* Part (a) is a *definition verification* in the decomposition sense, exactly
  as in Problem 25: `G(x,y) = Φ₃(x−y) + h(x,y)` where the corrector `h` is a
  signed sum of three scaled translates of `Φ₃` with poles at the images
  `x₁* = (R²/‖x‖²)x` (sphere inversion), `x₂* = (x₁,x₂,−x₃)` (plane
  reflection), `x₃* = (R²/‖x‖²)x₂*` (composite). The corrector is harmonic in
  `y` on the closed half ball (`lem:problem21-corrector-harmonic`, via the
  proved kit `Laplace.laplacian_comp_smul_sub_eq_zero` +
  `Laplace.laplacian_fundamentalSolution_eq_zero`), and `G(x,·) = 0` on both
  boundary pieces (`thm:problem21-dirichlet-boundary-vanish`): on the spherical
  cap by the Kelvin identity `(‖x‖/R)‖x₁*−y‖ = ‖x−y‖`
  (`lem:problem21-kelvin-identity`, applied at `x` and at `x₂*`), on the flat
  disk face by third-coordinate flips.
* Part (b): the quarter-plane Neumann function
  `N(x,y) = Φ₂(x−y) + Φ₂(x₁*−y) + Φ₂(x₂*−y) + Φ₂(x₃*−y)` (all plus signs) with
  `x₁* = (−x₁,x₂)`, `x₂* = (x₁,−x₂)`, `x₃* = (−x₁,−x₂)`. The corrector is
  harmonic on the closed quadrant, and the normal derivative of `N(x,·)`
  vanishes on both open boundary half-lines: on `Γ₁ = {y₁ = 0, y₂ > 0}` the
  outer normal is `(−1,0)`, so vanishing of `∂νN` is stated as vanishing of the
  first component of the gradient (`thm:problem21-neumann-boundary`); similarly
  on `Γ₂` with normal `(0,−1)` and the second component. The source's
  unbounded-domain Neumann convention applies: `∂νN = 0` with no volume
  correction.
* The distributional pole condition `Δ_y G(x,·) = δ_x` is out of scope, as in
  Problems 19/25.
-/

open Heat Laplace
open scoped ContDiff

namespace Problems.Undergraduate.Problem21

/-! ## Part (a): the half ball `B⁺(0,R) ⊆ ℝ³` with Dirichlet data

The three image poles of `x` (with `x₃ > 0`, hence `x ≠ 0` automatically). -/

/-- **The sphere-inversion image** (blueprint `def:problem21-reflections`):
`x₁* = (R²/‖x‖²) x`, the reflection of the pole `x` across the sphere
`∂B(0,R)`. (Junk value `0` at `x = 0`; every statement below carries
`x₃ > 0`, which forces `x ≠ 0`.) -/
noncomputable def sphereImage (R : ℝ) (x : E 3) : E 3 :=
  (R ^ 2 / ‖x‖ ^ 2) • x

/-- **The plane-reflection image** (blueprint `def:problem21-plane-image`):
`x₂* = (x₁, x₂, −x₃)`, the reflection of `x` across the plane `{x₃ = 0}`. -/
def planeImage (x : E 3) : E 3 := !₂[x 0, x 1, -(x 2)]

/-- **The composite image** (blueprint `def:problem21-composite-image`):
`x₃* = (R²/‖x‖²) x₂*`, the sphere inversion of the plane reflection — using
`‖x₂*‖ = ‖x‖` to write the scaling factor in terms of `‖x‖`. -/
noncomputable def compositeImage (R : ℝ) (x : E 3) : E 3 :=
  (R ^ 2 / ‖x‖ ^ 2) • planeImage x

@[simp] lemma planeImage_apply_zero (x : E 3) : planeImage x 0 = x 0 := rfl

@[simp] lemma planeImage_apply_one (x : E 3) : planeImage x 1 = x 1 := rfl

@[simp] lemma planeImage_apply_two (x : E 3) : planeImage x 2 = -(x 2) := rfl

/-- The plane reflection is an isometry fixing the origin: `‖x₂*‖ = ‖x‖`
(blueprint `lem:problem21-plane-image-norm`). -/
lemma norm_planeImage (x : E 3) : ‖planeImage x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three,
    Fin.sum_univ_three]
  simp [planeImage]

/-- The composite image is the sphere inversion of the plane reflection
(blueprint `lem:problem21-composite-as-inversion`); this is how the Kelvin
identity gets applied a second time, at the point `x₂*`. -/
lemma compositeImage_eq_sphereImage_planeImage (R : ℝ) (x : E 3) :
    compositeImage R x = sphereImage R (planeImage x) := by
  rw [compositeImage, sphereImage, norm_planeImage]

/-- **`Φ_N` is even** (blueprint `lem:problem21-even`): `Φ_N(−v) = Φ_N(v)`,
since `Φ_N` depends on its argument only through the norm and `‖−v‖ = ‖v‖`.
Needed to put translates `Φ(c(p−y))` into the kit shape `Φ(c(y−p))`. -/
lemma fundamentalSolution_neg (N : ℕ) (v : E N) :
    fundamentalSolution N (-v) = fundamentalSolution N v := by
  simp [fundamentalSolution]

/-- **The image corrector for the half ball** (blueprint
`def:problem21-corrector`):
`h(x,y) = −Φ₃((‖x‖/R)(x₁*−y)) − Φ₃(x₂*−y) + Φ₃((‖x‖/R)(x₃*−y))`. -/
noncomputable def corrector (R : ℝ) (x y : E 3) : ℝ :=
  -fundamentalSolution 3 ((‖x‖ / R) • (sphereImage R x - y))
    - fundamentalSolution 3 (planeImage x - y)
    + fundamentalSolution 3 ((‖x‖ / R) • (compositeImage R x - y))

/-- **The candidate Dirichlet Green's function of the half ball** (blueprint
`def:problem21-greens-dirichlet`):
`G(x,y) = Φ₃(x−y) − Φ₃((‖x‖/R)(x₁*−y)) − Φ₃(x₂*−y) + Φ₃((‖x‖/R)(x₃*−y))`. -/
noncomputable def greensDirichlet (R : ℝ) (x y : E 3) : ℝ :=
  fundamentalSolution 3 (x - y) + corrector R x y

/-- **The three images avoid the closed half ball** (blueprint
`lem:problem21-images-outside`): for a pole `x` in the open half ball
(`‖x‖ < R`, `x₃ > 0`), the sphere image lies outside the closed ball
(`‖x₁*‖ = R²/‖x‖ > R`) and the plane and composite images lie strictly below
the plane (`(x₂*)₃ = −x₃ < 0`, `(x₃*)₃ = −(R²/‖x‖²)x₃ < 0`). -/
lemma images_outside {R : ℝ} (hR : 0 < R) {x : E 3}
    (hxR : ‖x‖ < R) (hx3 : 0 < x 2) :
    R < ‖sphereImage R x‖ ∧ planeImage x 2 < 0 ∧ compositeImage R x 2 < 0 := by
  /- Planner strategy:
  (1) `x ≠ 0` from `hx3`: if `x = 0` then `x 2 = 0`, contradicting `0 < x 2`
      (e.g. `have hx0 : x ≠ 0 := fun h => by simp [h] at hx3`); hence
      `0 < ‖x‖` by `norm_pos_iff.mpr`.
  (2) Sphere-image norm: unfold `sphereImage`, then `norm_smul` +
      `Real.norm_eq_abs` + `abs_of_pos` (the scalar `R ^ 2 / ‖x‖ ^ 2 > 0`
      by `positivity`) give `‖sphereImage R x‖ = (R ^ 2 / ‖x‖ ^ 2) * ‖x‖
      = R ^ 2 / ‖x‖`; then `R < R ^ 2 / ‖x‖ ↔ ‖x‖ < R` via `lt_div_iff₀`
      (with `0 < ‖x‖`) and `nlinarith`/`field_simp` on `‖x‖ < R`, `0 < R`.
  (3) Plane component: `planeImage_apply_two` gives `planeImage x 2 = -(x 2)`,
      negative by `linarith`/`neg_neg`.
  (4) Composite component: `compositeImage R x = (R ^ 2 / ‖x‖ ^ 2) • planeImage x`
      is a smul, so `compositeImage R x 2 = (R ^ 2 / ‖x‖ ^ 2) * (-(x 2))` via
      `PiLp.smul_apply` + `planeImage_apply_two` + `smul_eq_mul` (Problem 25
      precedent for `PiLp` component simp); conclude `< 0` by
      `mul_neg_of_pos_of_neg` (scalar `> 0` by `positivity`, `-(x 2) < 0`
      by `linarith`). -/
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx3
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  refine ⟨?_, ?_, ?_⟩
  · -- sphere image norm
    have hnorm : ‖sphereImage R x‖ = R ^ 2 / ‖x‖ := by
      rw [sphereImage, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < R ^ 2 / ‖x‖ ^ 2)]
      field_simp
    rw [hnorm, lt_div_iff₀ hxn]
    nlinarith
  · rw [planeImage_apply_two]; linarith
  · have hcomp : compositeImage R x 2 = (R ^ 2 / ‖x‖ ^ 2) * (-(x 2)) := by
      rw [compositeImage, PiLp.smul_apply, planeImage_apply_two, smul_eq_mul]
    rw [hcomp]
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith)

/-- **The corrector is harmonic on the closed half ball** (blueprint
`lem:problem21-corrector-harmonic`): for a pole `x` in the open half ball and
any `y` in the closed half ball (`‖y‖ ≤ R`, `y₃ ≥ 0`),
`Δ_y (h(x,·))(y) = 0`. Each term is a scaled translate of `Φ₃` (scaling
`c = ‖x‖/R ≠ 0`, or `c = 1` for the `x₂*` term) whose pole avoids the closed
half ball, transported by the proved kit. -/
theorem laplacian_corrector_eq_zero {R : ℝ} (hR : 0 < R) {x : E 3}
    (hxR : ‖x‖ < R) (hx3 : 0 < x 2) {y : E 3}
    (hyR : ‖y‖ ≤ R) (hy3 : 0 ≤ y 2) :
    Heat.laplacian (fun y' => corrector R x y') y = 0 := by
  /- Planner strategy: MIRROR `Problems.Undergraduate.Problem25.laplacian_corrector_eq_zero`
  (Problem25.lean:118) — same three-step skeleton, now in `E 3` with variable `y`.
  (i) Poles avoid `y`. From `images_outside hR hxR hx3`:
      * `y - sphereImage R x ≠ 0`: `‖y‖ ≤ R < ‖sphereImage R x‖`, so
        `y ≠ sphereImage R x` (`fun h => absurd ... (by rw [h]; linarith)` on
        norms), then `sub_ne_zero.mpr`. Note the kit shape is
        `c • (y - p) ≠ 0` arguments — see (ii) for the direction used.
      * plane/composite poles: 2-component `< 0 ≤ y 2` (from `images_outside`
        and `hy3`), mirror Problem 25's coordinate proof: suppose the
        difference is `0`, apply at index `2`, rewrite with `PiLp.sub_apply`
        and conclude by `linarith`.
  (ii) Each corrector term into kit shape. The terms are
      `Φ₃((‖x‖/R) • (p - y'))` with `p` a pole — flip to
      `Φ₃((-(‖x‖/R)) • (y' - p))` via `neg_smul`, `smul_neg`, `neg_sub`
      (or use `fundamentalSolution_neg` from this file). Then
      `Laplace.laplacian_comp_smul_sub_eq_zero` with `c = -(‖x‖/R) ≠ 0`
      (`neg_ne_zero.mpr`, `div_ne_zero`, `norm_pos_iff`, `hR.ne'`), whose
      harmonicity input is
      `Laplace.laplacian_fundamentalSolution_eq_zero (by norm_num : (2:ℕ) ≤ 3)`
      at the nonzero point `c • (y - p)` (nonzero by `smul_ne_zero` from
      `c ≠ 0` and step (i)). The middle term has `c = 1`: mirror Problem 25's
      `laplacian_translate_eq_zero` (Problem25.lean:106) verbatim but with
      argument `p - y'` flipped to `(1 : ℝ) • (y' - p)` — sign handled by
      `fundamentalSolution_neg` or `neg_sub` + evenness.
  (iii) Linearity: `Heat.laplacian_add` (HeatMaximumPrincipleND.lean:152 —
      takes explicit `n` first arg and TWO `ContDiffAt ℝ 2` side conditions)
      plus `Heat.laplacian_neg` (HeatMaximumPrincipleND.lean:1214, explicit
      `n` arg, unconditional). Get `ContDiffAt ℝ 2` of each scaled translate by
      mirroring Problem 25's `contDiffAt_translate` (Problem25.lean:95): compose
      `(Laplace.contDiffOn_fundamentalSolution (by norm_num : (2:ℕ) ≤ 3)).contDiffAt
      (isOpen_ne.mem_nhds h)` with the affine map
      `contDiffAt_id.sub contDiffAt_const` (and `.const_smul` for the scaling),
      then `contDiffAt_infty.mp ... 2` — NEVER `.of_le` across `∞`/`⊤`.
      Reassociate the 3-term sum with a `funext ... ; ring` `hfun` first, as in
      Problem 25 lines 143–149. Qualify `Heat.laplacian` everywhere (bare
      `laplacian` is shadowed by `open InnerProductSpace`). -/
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx3
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨himg1, himg2, himg3⟩ := images_outside hR hxR hx3
  have hc : ‖x‖ / R ≠ 0 := ne_of_gt (div_pos hxn hR)
  have hcneg : -(‖x‖ / R) ≠ 0 := neg_ne_zero.mpr hc
  -- Step 1: the three image poles avoid `y`.
  have h1 : y - sphereImage R x ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hyR
    linarith
  have h2 : y - planeImage x ≠ 0 := by
    intro h
    have h0 : (y - planeImage x) 2 = 0 := by rw [h]; rfl
    rw [PiLp.sub_apply] at h0
    linarith
  have h3 : y - compositeImage R x ≠ 0 := by
    intro h
    have h0 : (y - compositeImage R x) 2 = 0 := by rw [h]; rfl
    rw [PiLp.sub_apply] at h0
    linarith
  -- the transported base points are nonzero
  have hs1 : (-(‖x‖ / R)) • (y - sphereImage R x) ≠ 0 := smul_ne_zero hcneg h1
  have hs2 : (-1 : ℝ) • (y - planeImage x) ≠ 0 := smul_ne_zero (by norm_num) h2
  have hs3 : (-(‖x‖ / R)) • (y - compositeImage R x) ≠ 0 := smul_ne_zero hcneg h3
  -- Step 2: each scaled translate is `C²` and harmonic at `y`.
  have hcd : ∀ (c : ℝ) (p : E 3), c • (y - p) ≠ 0 →
      ContDiffAt ℝ 2 (fun y' => fundamentalSolution 3 (c • (y' - p))) y := by
    intro c p h
    have hΦ : ContDiffAt ℝ ∞ (fundamentalSolution 3) (c • (y - p)) :=
      (Laplace.contDiffOn_fundamentalSolution (by norm_num)).contDiffAt
        (isOpen_ne.mem_nhds h)
    have hsub : ContDiffAt ℝ ∞ (fun y' : E 3 => c • (y' - p)) y :=
      (contDiffAt_id.sub contDiffAt_const).const_smul c
    exact contDiffAt_infty.mp (hΦ.comp y hsub) 2
  have hlap : ∀ (c : ℝ), c ≠ 0 → ∀ (p : E 3), c • (y - p) ≠ 0 →
      Heat.laplacian (fun y' => fundamentalSolution 3 (c • (y' - p))) y = 0 :=
    fun c hc' p h =>
      Laplace.laplacian_comp_smul_sub_eq_zero (fundamentalSolution 3) hc' p y
        (Laplace.laplacian_fundamentalSolution_eq_zero (by norm_num) h)
  -- Step 3: rewrite the corrector into kit shape (`c • (y' - p)` arguments).
  have hfun : (fun y' => corrector R x y') =
      fun y' => (-fundamentalSolution 3 ((-(‖x‖ / R)) • (y' - sphereImage R x)) +
        -fundamentalSolution 3 ((-1 : ℝ) • (y' - planeImage x))) +
        fundamentalSolution 3 ((-(‖x‖ / R)) • (y' - compositeImage R x)) := by
    funext y'
    have e1 : (‖x‖ / R) • (sphereImage R x - y')
        = (-(‖x‖ / R)) • (y' - sphereImage R x) := by
      rw [← neg_sub y' (sphereImage R x), smul_neg, ← neg_smul]
    have e2 : planeImage x - y' = (-1 : ℝ) • (y' - planeImage x) := by
      rw [neg_one_smul, neg_sub]
    have e3 : (‖x‖ / R) • (compositeImage R x - y')
        = (-(‖x‖ / R)) • (y' - compositeImage R x) := by
      rw [← neg_sub y' (compositeImage R x), smul_neg, ← neg_smul]
    simp only [corrector, e1, e2, e3]
    ring
  -- Step 4: additivity of the Laplacian.
  rw [hfun,
    Heat.laplacian_add 3
      (fun y' => -fundamentalSolution 3 ((-(‖x‖ / R)) • (y' - sphereImage R x)) +
        -fundamentalSolution 3 ((-1 : ℝ) • (y' - planeImage x)))
      (fun y' => fundamentalSolution 3 ((-(‖x‖ / R)) • (y' - compositeImage R x))) y
      ((hcd _ _ hs1).neg.add (hcd _ _ hs2).neg) (hcd _ _ hs3),
    Heat.laplacian_add 3
      (fun y' => -fundamentalSolution 3 ((-(‖x‖ / R)) • (y' - sphereImage R x)))
      (fun y' => -fundamentalSolution 3 ((-1 : ℝ) • (y' - planeImage x))) y
      (hcd _ _ hs1).neg (hcd _ _ hs2).neg,
    Heat.laplacian_neg 3
      (fun y' => fundamentalSolution 3 ((-(‖x‖ / R)) • (y' - sphereImage R x))) y,
    Heat.laplacian_neg 3
      (fun y' => fundamentalSolution 3 ((-1 : ℝ) • (y' - planeImage x))) y,
    hlap _ hcneg _ hs1, hlap _ (by norm_num) _ hs2, hlap _ hcneg _ hs3]
  ring

/-- **The Kelvin identity** (blueprint `lem:problem21-kelvin-identity`): for
`‖y‖ = R` and `x ≠ 0`, `(‖x‖/R) ‖x₁* − y‖ = ‖x − y‖`. Expand
`‖x₁* − y‖² = R⁴/‖x‖² − 2(R²/‖x‖²)⟨x,y⟩ + R²` and multiply by `‖x‖²/R²`. -/
lemma kelvin_identity {R : ℝ} (hR : 0 < R) {x : E 3} (hx : x ≠ 0)
    {y : E 3} (hy : ‖y‖ = R) :
    (‖x‖ / R) * ‖sphereImage R x - y‖ = ‖x - y‖ := by
  /- Planner strategy: reduce to squares — both sides are `≥ 0`
  (`by positivity` / `norm_nonneg`), so it suffices to prove the squared
  identity via `← sq_eq_sq₀ (by positivity) (norm_nonneg _)` (project
  precedent: CalculusBasic.lean:797 uses `sq_eq_sq₀` the same way).
  Then:
  * LHS² = `(‖x‖ / R) ^ 2 * ‖sphereImage R x - y‖ ^ 2` by `mul_pow`.
  * Expand both squared norms with `norm_sub_sq_real`
    (Mathlib/Analysis/InnerProductSpace/Basic.lean:
    `‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * ⟪a, b⟫_ℝ + ‖b‖ ^ 2`).
  * `‖sphereImage R x‖ ^ 2 = (R ^ 2 / ‖x‖ ^ 2) ^ 2 * ‖x‖ ^ 2`: unfold
    `sphereImage`, `norm_smul`, `Real.norm_eq_abs`, `abs_of_pos` (scalar
    positive by `positivity` — needs `0 < ‖x‖` from `norm_pos_iff.mpr hx`),
    then `mul_pow`.
  * `⟪sphereImage R x, y⟫_ℝ = (R ^ 2 / ‖x‖ ^ 2) * ⟪x, y⟫_ℝ` by
    `real_inner_smul_left`.
  * Replace `‖y‖` by `R` via `hy`.
  Finally `field_simp` (facts: `‖x‖ ≠ 0` from `hx`/`norm_pos_iff`,
  `R ≠ 0` from `hR.ne'`) + `ring` closes the polynomial identity. -/
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  rw [← sq_eq_sq₀ (by positivity) (norm_nonneg _), mul_pow,
    norm_sub_sq_real, norm_sub_sq_real]
  have h1 : ‖sphereImage R x‖ = R ^ 2 / ‖x‖ := by
    rw [sphereImage, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < R ^ 2 / ‖x‖ ^ 2)]
    field_simp
  have h2 : inner ℝ (sphereImage R x) y = (R ^ 2 / ‖x‖ ^ 2) * inner ℝ x y := by
    rw [sphereImage, real_inner_smul_left]
  rw [h1, h2, hy]
  have hxne : ‖x‖ ≠ 0 := hxn.ne'
  field_simp
  ring

/-- **Zero Dirichlet data on the boundary of the half ball** (blueprint
`thm:problem21-dirichlet-boundary-vanish`): for a pole `x` in the open half
ball and `y` on either boundary piece — the spherical cap (`‖y‖ = R`,
`y₃ ≥ 0`) or the flat disk face (`y₃ = 0`, `‖y‖ ≤ R`) — `G(x,y) = 0`.
On the cap, terms 1–2 cancel by the Kelvin identity at `x` and terms 3–4 by
the Kelvin identity at `x₂*` (using `‖x₂*‖ = ‖x‖` and `(x₂*)₁* = x₃*`); on
the disk face `‖x−y‖ = ‖x₂*−y‖` and `‖x₁*−y‖ = ‖x₃*−y‖` (third-coordinate
flips), so the terms cancel pairwise. -/
theorem greensDirichlet_boundary_vanish {R : ℝ} (hR : 0 < R) {x : E 3}
    (_hxR : ‖x‖ < R) (hx3 : 0 < x 2) {y : E 3}
    (hy : (‖y‖ = R ∧ 0 ≤ y 2) ∨ (y 2 = 0 ∧ ‖y‖ ≤ R)) :
    greensDirichlet R x y = 0 := by
  /- Planner strategy: unfold `greensDirichlet`, `corrector`; mirror Problem 25's
  `G_eq_zero_boundary` (Problem25.lean:172) congruence style.
  Start with an in-proof norm-congruence helper (Φ₃ depends only on the norm):
    `have hcongr : ∀ v w : E 3, ‖v‖ = ‖w‖ →
        fundamentalSolution 3 v = fundamentalSolution 3 w := fun v w h => by
      rw [fundamentalSolution_of_three_le (by norm_num),
          fundamentalSolution_of_three_le (by norm_num), h]`
  (a bare `simp [Laplace.fundamentalSolution, h]` may also close it since the
  `if` branch is decided by `3 = 2` being false — try the `rw` route first).
  Also `hx0 : x ≠ 0` from `hx3` (as in `images_outside`) and `0 < ‖x‖`.

  Case cap (`hy = inl ⟨hyR, hy3⟩`: `‖y‖ = R`, `0 ≤ y 2`):
  * Terms 1–2 cancel: term 2's argument norm is
    `‖(‖x‖/R) • (sphereImage R x - y)‖ = (‖x‖/R) * ‖sphereImage R x - y‖`
    (`norm_smul`, `Real.norm_eq_abs`, `abs_of_pos` with `0 < ‖x‖/R` by
    `positivity`) `= ‖x - y‖` by `kelvin_identity hR hx0 hyR`; apply `hcongr`.
  * Terms 3–4 cancel: apply `kelvin_identity` AT the point `planeImage x`.
    Needs: `planeImage x ≠ 0` (its 2-component is `-(x 2) ≠ 0` by `hx3`;
    coordinate argument as in `images_outside`), `‖planeImage x‖ = ‖x‖` by
    `norm_planeImage`, and
    `sphereImage R (planeImage x) = compositeImage R x` by
    `compositeImage_eq_sphereImage_planeImage.symm`. Result:
    `(‖x‖/R) * ‖compositeImage R x - y‖ = ‖planeImage x - y‖`, so term 4's
    norm equals term 3's; `hcongr` + `ring` finish.

  Case disk (`hy = inr ⟨hy2, hyR⟩`: `y 2 = 0`, `‖y‖ ≤ R`):
  * `‖x - y‖ = ‖planeImage x - y‖`: both by `EuclideanSpace.norm_eq` +
    `Fin.sum_univ_three`, simp with `PiLp.sub_apply`,
    `planeImage_apply_zero/one/two`, and `hy2` — third components are
    `x 2 - 0` vs `-(x 2) - 0`, whose squares agree (`ring_nf` /
    `neg_sub` bookkeeping); mirror Problem 25's `hnorm` helper
    (Problem25.lean:180) adapted to three coordinates.
  * `‖sphereImage R x - y‖ = ‖compositeImage R x - y‖`: same coordinate
    computation — `sphereImage R x i = (R^2/‖x‖^2) * x i` and
    `compositeImage R x i = (R^2/‖x‖^2) * planeImage x i` via
    `PiLp.smul_apply` + `smul_eq_mul`; first two coordinates equal, third
    differs by sign, squares agree.
  * Then term 1 cancels term 3 and term 2 cancels term 4 (for the 2–4 pair
    also rewrite both smul-norms with `norm_smul` so the common factor
    `‖x‖/R` multiplies equal norms); finish by `hcongr` on each pair and
    `ring` on the signed sum (+, −, −, +). -/
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx3
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  -- Φ₃ depends on its argument only through the norm.
  have hcongr : ∀ v w : E 3, ‖v‖ = ‖w‖ →
      fundamentalSolution 3 v = fundamentalSolution 3 w := fun v w h => by
    rw [fundamentalSolution_of_three_le (by norm_num),
      fundamentalSolution_of_three_le (by norm_num), h]
  rcases hy with ⟨hyR, _hy3⟩ | ⟨hy2, _hyR⟩
  · -- Case cap: `‖y‖ = R`.
    -- Terms 1–2 cancel via the Kelvin identity at `x`.
    have e1 : fundamentalSolution 3 ((‖x‖ / R) • (sphereImage R x - y)) =
        fundamentalSolution 3 (x - y) := by
      refine hcongr _ _ ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ / R)]
      exact kelvin_identity hR hx0 hyR
    -- Terms 3–4 cancel via the Kelvin identity at `planeImage x`.
    have hpx0 : planeImage x ≠ 0 := by
      intro h
      have h2 : planeImage x 2 = 0 := by rw [h]; rfl
      rw [planeImage_apply_two] at h2
      linarith
    have e2 : fundamentalSolution 3 ((‖x‖ / R) • (compositeImage R x - y)) =
        fundamentalSolution 3 (planeImage x - y) := by
      refine hcongr _ _ ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ / R),
        compositeImage_eq_sphereImage_planeImage]
      have := kelvin_identity hR hpx0 hyR (x := planeImage x)
      rwa [norm_planeImage] at this
    simp only [greensDirichlet, corrector, e1, e2]
    ring
  · -- Case disk face: `y 2 = 0`.
    -- norms agree as soon as the coordinate squares agree
    have hnorm : ∀ v w : E 3,
        (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 →
        ‖v‖ = ‖w‖ := by
      intro v w hvw
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three,
        Fin.sum_univ_three]
      simp only [Real.norm_eq_abs, sq_abs]
      rw [hvw]
    -- Term 1 cancels term 3 (plane reflection flips the third coordinate).
    have e1 : fundamentalSolution 3 (x - y) =
        fundamentalSolution 3 (planeImage x - y) := by
      refine hcongr _ _ (hnorm _ _ ?_)
      simp only [PiLp.sub_apply, planeImage_apply_zero, planeImage_apply_one,
        planeImage_apply_two, hy2]
      ring
    -- Term 2 cancels term 4 (their arguments' norms agree after `norm_smul`).
    have e2 : fundamentalSolution 3 ((‖x‖ / R) • (sphereImage R x - y)) =
        fundamentalSolution 3 ((‖x‖ / R) • (compositeImage R x - y)) := by
      refine hcongr _ _ ?_
      rw [norm_smul, norm_smul]
      congr 1
      refine hnorm _ _ ?_
      simp only [PiLp.sub_apply, sphereImage, compositeImage, PiLp.smul_apply,
        planeImage_apply_zero, planeImage_apply_one, planeImage_apply_two,
        smul_eq_mul, hy2]
      ring
    simp only [greensDirichlet, corrector, e1, e2]
    ring

/-! ## Part (b): the quarter plane `Ω = {x₁ > 0, x₂ > 0} ⊆ ℝ²` with Neumann data -/

/-- **First Neumann image** (blueprint `def:problem21-neumann-image1`):
`x₁* = (−x₁, x₂)`, the reflection across the vertical axis. (The source's
part-(b) numbering — followed verbatim here — differs from Problem 25's.) -/
def neumannImage1 (x : E 2) : E 2 := !₂[-(x 0), x 1]

/-- **Second Neumann image** (blueprint `def:problem21-neumann-image2`):
`x₂* = (x₁, −x₂)`, the reflection across the horizontal axis. -/
def neumannImage2 (x : E 2) : E 2 := !₂[x 0, -(x 1)]

/-- **Third Neumann image** (blueprint `def:problem21-neumann-image3`):
`x₃* = (−x₁, −x₂)`, the reflection through the origin. -/
def neumannImage3 (x : E 2) : E 2 := !₂[-(x 0), -(x 1)]

@[simp] lemma neumannImage1_apply_zero (x : E 2) : neumannImage1 x 0 = -(x 0) := rfl

@[simp] lemma neumannImage1_apply_one (x : E 2) : neumannImage1 x 1 = x 1 := rfl

@[simp] lemma neumannImage2_apply_zero (x : E 2) : neumannImage2 x 0 = x 0 := rfl

@[simp] lemma neumannImage2_apply_one (x : E 2) : neumannImage2 x 1 = -(x 1) := rfl

@[simp] lemma neumannImage3_apply_zero (x : E 2) : neumannImage3 x 0 = -(x 0) := rfl

@[simp] lemma neumannImage3_apply_one (x : E 2) : neumannImage3 x 1 = -(x 1) := rfl

/-- **The Neumann corrector** (blueprint `def:problem21-neumann-corrector`):
`h(x,y) = Φ₂(x₁*−y) + Φ₂(x₂*−y) + Φ₂(x₃*−y)` — all plus signs, so that the
*normal derivatives* (not the values) cancel on the boundary. -/
noncomputable def neumannCorrector (x y : E 2) : ℝ :=
  fundamentalSolution 2 (neumannImage1 x - y)
    + fundamentalSolution 2 (neumannImage2 x - y)
    + fundamentalSolution 2 (neumannImage3 x - y)

/-- **The candidate Neumann Green's function of the quarter plane** (blueprint
`def:problem21-greens-neumann`):
`N(x,y) = Φ₂(x−y) + Φ₂(x₁*−y) + Φ₂(x₂*−y) + Φ₂(x₃*−y)`. Per the source's
unbounded-domain Neumann convention, the defining conditions are
`Δ N = δ_x` and `∂νN = 0`, with no volume correction. -/
noncomputable def greensNeumann (x y : E 2) : ℝ :=
  fundamentalSolution 2 (x - y) + neumannCorrector x y

/-- **The Neumann corrector is harmonic on the closed quadrant** (blueprint
`lem:problem21-neumann-corrector-harmonic`): for a pole `x` in the open
quadrant and `y` in the closed quadrant, `Δ_y (h(x,·))(y) = 0`. Same kit route
as part (a), with `c = 1` translates and poles outside the closed quadrant. -/
theorem laplacian_neumannCorrector_eq_zero {x : E 2}
    (hx1 : 0 < x 0) (hx2 : 0 < x 1) {y : E 2}
    (hy1 : 0 ≤ y 0) (hy2 : 0 ≤ y 1) :
    Heat.laplacian (fun y' => neumannCorrector x y') y = 0 := by
  /- Planner strategy: DIRECT mirror of Problem 25's
  `laplacian_corrector_eq_zero` (Problem25.lean:118) — same `E 2`, `c = 1`
  translates, all-plus signs (so no `Heat.laplacian_neg` needed here,
  only two applications of `Heat.laplacian_add`).
  (i) Poles avoid `y` coordinatewise: each image has a strictly negative
      coordinate where `y` is `≥ 0` —
      `(neumannImage1 x) 0 = -(x 0) < 0 ≤ y 0`,
      `(neumannImage2 x) 1 = -(x 1) < 0 ≤ y 1`,
      `(neumannImage3 x) 0 = -(x 0) < 0 ≤ y 0`.
      So `y - neumannImage_i x ≠ 0`: suppose `= 0`, apply at the index,
      rewrite `PiLp.sub_apply` + the `neumannImage*_apply_*` simp lemmas
      (+ `sub_neg_eq_add`), `linarith` — exactly Problem 25 lines 123–137.
  (ii) Re-derive the two Problem 25 helpers locally (they live in namespace
      `Problems.Undergraduate.Problem25`, so inline analogous `have`s or
      private lemmas — note argument order here is `p - y'` vs P25's
      `x' - p`, so first flip via `fundamentalSolution_neg` / `neg_sub`):
      * ContDiffAt: `(Laplace.contDiffOn_fundamentalSolution le_rfl).contDiffAt
        (isOpen_ne.mem_nhds h)` composed with
        `contDiffAt_id.sub contDiffAt_const`, then
        `contDiffAt_infty.mp ... 2` (NEVER `.of_le` across `∞`/`⊤`).
      * Harmonicity of each translate:
        `Laplace.laplacian_comp_smul_sub_eq_zero _ one_ne_zero` (+ `one_smul`)
        with input `Laplace.laplacian_fundamentalSolution_eq_zero le_rfl`
        at the nonzero point from (i) — Problem25.lean:106-113 verbatim.
  (iii) Assemble: `hfun`-style `funext`/`ring` regrouping, then two
      `Heat.laplacian_add 2 ...` rewrites (explicit `n = 2` first arg,
      TWO `ContDiffAt ℝ 2` side conditions each) and the three translate
      harmonicity facts; `ring`. Qualify `Heat.laplacian` everywhere. -/
  -- Step 1: the three image poles avoid `y`.
  have h1 : y - neumannImage1 x ≠ 0 := by
    intro h
    have h0 : (y - neumannImage1 x) 0 = 0 := by rw [h]; rfl
    rw [PiLp.sub_apply, neumannImage1_apply_zero, sub_neg_eq_add] at h0
    linarith
  have h2 : y - neumannImage2 x ≠ 0 := by
    intro h
    have h0 : (y - neumannImage2 x) 1 = 0 := by rw [h]; rfl
    rw [PiLp.sub_apply, neumannImage2_apply_one, sub_neg_eq_add] at h0
    linarith
  have h3 : y - neumannImage3 x ≠ 0 := by
    intro h
    have h0 : (y - neumannImage3 x) 0 = 0 := by rw [h]; rfl
    rw [PiLp.sub_apply, neumannImage3_apply_zero, sub_neg_eq_add] at h0
    linarith
  have hs1 : (-1 : ℝ) • (y - neumannImage1 x) ≠ 0 := smul_ne_zero (by norm_num) h1
  have hs2 : (-1 : ℝ) • (y - neumannImage2 x) ≠ 0 := smul_ne_zero (by norm_num) h2
  have hs3 : (-1 : ℝ) • (y - neumannImage3 x) ≠ 0 := smul_ne_zero (by norm_num) h3
  -- Step 2: each translate (in kit shape) is `C²` and harmonic at `y`.
  have hcd : ∀ p : E 2, (-1 : ℝ) • (y - p) ≠ 0 →
      ContDiffAt ℝ 2 (fun y' => fundamentalSolution 2 ((-1 : ℝ) • (y' - p))) y := by
    intro p h
    have hΦ : ContDiffAt ℝ ∞ (fundamentalSolution 2) ((-1 : ℝ) • (y - p)) :=
      (Laplace.contDiffOn_fundamentalSolution le_rfl).contDiffAt
        (isOpen_ne.mem_nhds h)
    have hsub : ContDiffAt ℝ ∞ (fun y' : E 2 => (-1 : ℝ) • (y' - p)) y :=
      (contDiffAt_id.sub contDiffAt_const).const_smul (-1 : ℝ)
    exact contDiffAt_infty.mp (hΦ.comp y hsub) 2
  have hlap : ∀ p : E 2, (-1 : ℝ) • (y - p) ≠ 0 →
      Heat.laplacian (fun y' => fundamentalSolution 2 ((-1 : ℝ) • (y' - p))) y = 0 :=
    fun p h =>
      Laplace.laplacian_comp_smul_sub_eq_zero (fundamentalSolution 2)
        (by norm_num : (-1 : ℝ) ≠ 0) p y
        (Laplace.laplacian_fundamentalSolution_eq_zero le_rfl h)
  -- Step 3: rewrite the corrector into kit shape.
  have hfun : (fun y' => neumannCorrector x y') =
      fun y' => (fundamentalSolution 2 ((-1 : ℝ) • (y' - neumannImage1 x)) +
        fundamentalSolution 2 ((-1 : ℝ) • (y' - neumannImage2 x))) +
        fundamentalSolution 2 ((-1 : ℝ) • (y' - neumannImage3 x)) := by
    funext y'
    have e : ∀ p : E 2, p - y' = (-1 : ℝ) • (y' - p) := fun p => by
      rw [neg_one_smul, neg_sub]
    simp only [neumannCorrector, e]
  -- Step 4: additivity of the Laplacian.
  rw [hfun,
    Heat.laplacian_add 2
      (fun y' => fundamentalSolution 2 ((-1 : ℝ) • (y' - neumannImage1 x)) +
        fundamentalSolution 2 ((-1 : ℝ) • (y' - neumannImage2 x)))
      (fun y' => fundamentalSolution 2 ((-1 : ℝ) • (y' - neumannImage3 x))) y
      ((hcd _ hs1).add (hcd _ hs2)) (hcd _ hs3),
    Heat.laplacian_add 2
      (fun y' => fundamentalSolution 2 ((-1 : ℝ) • (y' - neumannImage1 x)))
      (fun y' => fundamentalSolution 2 ((-1 : ℝ) • (y' - neumannImage2 x))) y
      (hcd _ hs1) (hcd _ hs2),
    hlap _ hs1, hlap _ hs2, hlap _ hs3]
  ring

/-- **The normal derivative vanishes on both boundary half-lines** (blueprint
`thm:problem21-neumann-boundary`): for a pole `x` in the open quadrant, on
`Γ₁ = {y₁ = 0, y₂ > 0}` (outer normal `(−1,0)`) the normal derivative
`∂νN(x,·)(y) = −(∇_y N(x,·)(y))₁` vanishes — stated as vanishing of the first
gradient component — and symmetrically on `Γ₂ = {y₂ = 0, y₁ > 0}` (outer
normal `(0,−1)`) the second gradient component vanishes.

Route: `∇Φ₂(v) = v/(2π‖v‖²)` (`Laplace.gradient_fundamentalSolution` at
`N = 2`), gradients of the translates via
`Laplace.gradient_comp_smul_sub` at `c = −1` plus the even lemma; on `Γ₁`
the first components of the four `pole − y` vectors are `x₁, −x₁, x₁, −x₁`
with `‖x−y‖ = ‖x₁*−y‖` and `‖x₂*−y‖ = ‖x₃*−y‖`, so the four contributions
cancel pairwise. -/
theorem greensNeumann_normal_deriv_vanish {x : E 2}
    (hx1 : 0 < x 0) (hx2 : 0 < x 1) (y : E 2) :
    (y 0 = 0 → 0 < y 1 → gradient (greensNeumann x) y 0 = 0) ∧
    (y 1 = 0 → 0 < y 0 → gradient (greensNeumann x) y 1 = 0) := by
  /- Planner strategy (hardest sorry — gradient computation):
  Core reusable step — prove once, apply 4×:
    `have hgrad : ∀ p : E 2, y - p ≠ 0 →
        gradient (fun y' => fundamentalSolution 2 (p - y')) y
          = -((1 / (2 * Real.pi * ‖y - p‖ ^ 2)) • (y - p))`
  (equivalently `(1/(2π‖p-y‖²)) • (p - y)` — pick the sign convention that
  falls out and keep it consistent). Proof of `hgrad`:
  * Rewrite the function into kit shape: `p - y' = (-1 : ℝ) • (y' - p)` via
    `neg_smul`, `one_smul`, `neg_sub` (`funext` first).
  * `Laplace.gradient_comp_smul_sub (fundamentalSolution 2)
      (neg_ne_zero.mpr one_ne_zero) p y` gives
    `∇ = (-1) • gradient (fundamentalSolution 2) ((-1) • (y - p))`
    (unconditional equality of gradients).
  * Evaluate the inner gradient with
    `(Laplace.gradient_fundamentalSolution le_rfl hv).gradient` (the theorem
    is a `HasGradientAt`; `.gradient` is `HasGradientAt.gradient`); at `N = 2`
    the vector is `(1 / (2 * unitBallVolume 2 * ‖v‖ ^ 2)) • v` with
    `Laplace.unitBallVolume_two : unitBallVolume 2 = Real.pi`; the point is
    `v = (-1) • (y - p) = p - y ≠ 0` (`neg_smul`/`neg_sub`; nonzero from the
    hypothesis via `neg_ne_zero`/`sub_ne_zero`), and `‖p - y‖ = ‖y - p‖` by
    `norm_sub_rev`.
  Gradient of the 4-term sum: NO `HasGradientAt.add`/`gradient_add` exists in
  Mathlib's Gradient/Basic (verified absent), and CalculusBasic.lean:102
  `gradient_add` is for `E 3` only. Options:
  * [preferred] fderiv-level: `gradient` unfolds to
    `(toDual ℝ _).symm (fderiv ℝ f y)`; use `fderiv_add` (+ `map_add`) with
    `DifferentiableAt` of each translate from
    `Laplace.differentiableAt_comp_smul_sub_iff` (after the same `(-1) •`
    rewrite) + differentiability of `fundamentalSolution 2` at the nonzero
    point from `(Laplace.contDiffOn_fundamentalSolution le_rfl).contDiffAt
    (isOpen_ne.mem_nhds _)` and `.differentiableAt (by norm_num)`.
  * Alternative: `Heat.gradient_add_eventually`
    (HeatMaximumPrincipleND.lean:145, works in `E n`, needs `ContDiffAt ℝ 2`
    of each summand) evaluated at `y` via `Filter.EventuallyEq.eq_of_nhds`.
  Boundary poles differ from y: on `Γ₁` (`y 0 = 0`, `0 < y 1`) all four of
  `x, neumannImage1 x, neumannImage2 x, neumannImage3 x` differ from `y` in
  some coordinate (`x 0 > 0 = y 0`; image2 likewise at index 0; image1/image3
  have `-(x 0) < 0 = y 0`) — coordinate proofs via `PiLp.sub_apply` +
  `neumannImage*_apply_*` + `linarith`, as in `laplacian_neumannCorrector_eq_zero`.
  Final cancellation on `Γ₁`: apply `hgrad` to the four terms of
  `greensNeumann`/`neumannCorrector` (unfold first; note the first term is
  `x - y'`, i.e. `p = x`), then take component 0 (`PiLp.smul_apply`,
  `PiLp.sub_apply`, `smul_eq_mul`, `PiLp.neg_apply`). With `y 0 = 0` the
  first components of `p - y` are `x 0, -(x 0), x 0, -(x 0)` and the norms
  pair up: `‖x - y‖ = ‖neumannImage1 x - y‖` and
  `‖neumannImage2 x - y‖ = ‖neumannImage3 x - y‖` — prove by
  `EuclideanSpace.norm_eq` + `Fin.sum_univ_two` + the apply-lemmas
  (first-coordinate sign flip, squares agree; mirror Problem25.lean:180
  `hnorm`). The four scalar contributions then cancel pairwise by `ring`
  (coefficients equal, first components opposite). Symmetric argument on
  `Γ₂` (`y 1 = 0`, `0 < y 0`) with component 1 and the pairing
  `x ↔ neumannImage2 x`, `neumannImage1 x ↔ neumannImage3 x`.
  Constructor split: `refine ⟨fun hy0 hy1 => ?_, fun hy1 hy0 => ?_⟩`.
  Qualify `Heat.laplacian`/kit names; here `gradient` in the STATEMENT is
  Mathlib's `gradient` (from `Mathlib.Analysis.Calculus.Gradient.Basic`),
  the same one the PDE kit lemmas talk about. -/
  -- Gradients add (via `hasGradientAt_iff_hasFDerivAt` and linearity of `toDual`).
  have hadd : ∀ {f g : E 2 → ℝ} {a b : E 2},
      HasGradientAt f a y → HasGradientAt g b y →
      HasGradientAt (fun y' => f y' + g y') (a + b) y := by
    intro f g a b hf hg
    rw [hasGradientAt_iff_hasFDerivAt] at hf hg ⊢
    rw [map_add]
    exact hf.add hg
  -- Gradient of a single reflected translate `y' ↦ Φ₂(p - y')` at `y ≠ p`:
  -- `∇ = (1/(2π‖y-p‖²)) • (y - p)`.
  have hterm : ∀ p : E 2, y - p ≠ 0 →
      HasGradientAt (fun y' => fundamentalSolution 2 (p - y'))
        ((1 / (2 * Real.pi * ‖y - p‖ ^ 2)) • (y - p)) y := by
    intro p hp
    have hp' : p - y ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hp).symm
    have hΦ := Laplace.gradient_fundamentalSolution le_rfl hp'
    rw [hasGradientAt_iff_hasFDerivAt] at hΦ ⊢
    have hA : HasFDerivAt (fun y' : E 2 => p - y')
        (-(ContinuousLinearMap.id ℝ (E 2))) y := (hasFDerivAt_id y).const_sub p
    have hcomp := hΦ.comp y hA
    apply hcomp.congr_fderiv
    ext w
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      neg_apply, ContinuousLinearMap.coe_id', id_eq,
      InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      inner_neg_right, Laplace.unitBallVolume_two, norm_sub_rev p y,
      inner_sub_left]
    push_cast
    ring
  -- The four poles and the shape of the total gradient.
  refine ⟨fun hy0 _hy1 => ?_, fun hy1 _hy0 => ?_⟩
  · -- Γ₁: `y 0 = 0`. All four poles differ from `y` in the first coordinate.
    have hne : ∀ p : E 2, p 0 ≠ 0 → y - p ≠ 0 := by
      intro p hp h
      have h0 : (y - p) 0 = 0 := by rw [h]; rfl
      rw [PiLp.sub_apply, hy0] at h0
      exact hp (by linarith)
    have hx' := hne x hx1.ne'
    have h1' := hne (neumannImage1 x) (by rw [neumannImage1_apply_zero]; exact (neg_lt_zero.mpr hx1).ne)
    have h2' := hne (neumannImage2 x) (by rw [neumannImage2_apply_zero]; exact hx1.ne')
    have h3' := hne (neumannImage3 x) (by rw [neumannImage3_apply_zero]; exact (neg_lt_zero.mpr hx1).ne)
    have hGall : HasGradientAt (greensNeumann x)
        ((1 / (2 * Real.pi * ‖y - x‖ ^ 2)) • (y - x) +
          ((1 / (2 * Real.pi * ‖y - neumannImage1 x‖ ^ 2)) • (y - neumannImage1 x) +
            (1 / (2 * Real.pi * ‖y - neumannImage2 x‖ ^ 2)) • (y - neumannImage2 x) +
            (1 / (2 * Real.pi * ‖y - neumannImage3 x‖ ^ 2)) • (y - neumannImage3 x))) y :=
      hadd (hterm x hx') (hadd (hadd (hterm _ h1') (hterm _ h2')) (hterm _ h3'))
    have hgeq := hGall.gradient
    -- Norm pairings on `Γ₁`: flip the first coordinate.
    have hnorm2 : ∀ v w : E 2, (v 0) ^ 2 + (v 1) ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 →
        ‖v‖ = ‖w‖ := by
      intro v w hvw
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two,
        Fin.sum_univ_two]
      simp only [Real.norm_eq_abs, sq_abs]
      rw [hvw]
    have hn1 : ‖y - neumannImage1 x‖ = ‖y - x‖ := by
      refine hnorm2 _ _ ?_
      simp only [PiLp.sub_apply, neumannImage1_apply_zero, neumannImage1_apply_one, hy0]
      ring
    have hn3 : ‖y - neumannImage3 x‖ = ‖y - neumannImage2 x‖ := by
      refine hnorm2 _ _ ?_
      simp only [PiLp.sub_apply, neumannImage3_apply_zero, neumannImage3_apply_one,
        neumannImage2_apply_zero, neumannImage2_apply_one, hy0]
      ring
    rw [hgeq]
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      neumannImage1_apply_zero, neumannImage2_apply_zero, neumannImage3_apply_zero,
      hn1, hn3, hy0]
    ring
  · -- Γ₂: `y 1 = 0`. All four poles differ from `y` in the second coordinate.
    have hne : ∀ p : E 2, p 1 ≠ 0 → y - p ≠ 0 := by
      intro p hp h
      have h0 : (y - p) 1 = 0 := by rw [h]; rfl
      rw [PiLp.sub_apply, hy1] at h0
      exact hp (by linarith)
    have hx' := hne x hx2.ne'
    have h1' := hne (neumannImage1 x) (by rw [neumannImage1_apply_one]; exact hx2.ne')
    have h2' := hne (neumannImage2 x) (by rw [neumannImage2_apply_one]; exact (neg_lt_zero.mpr hx2).ne)
    have h3' := hne (neumannImage3 x) (by rw [neumannImage3_apply_one]; exact (neg_lt_zero.mpr hx2).ne)
    have hGall : HasGradientAt (greensNeumann x)
        ((1 / (2 * Real.pi * ‖y - x‖ ^ 2)) • (y - x) +
          ((1 / (2 * Real.pi * ‖y - neumannImage1 x‖ ^ 2)) • (y - neumannImage1 x) +
            (1 / (2 * Real.pi * ‖y - neumannImage2 x‖ ^ 2)) • (y - neumannImage2 x) +
            (1 / (2 * Real.pi * ‖y - neumannImage3 x‖ ^ 2)) • (y - neumannImage3 x))) y :=
      hadd (hterm x hx') (hadd (hadd (hterm _ h1') (hterm _ h2')) (hterm _ h3'))
    have hgeq := hGall.gradient
    -- Norm pairings on `Γ₂`: flip the second coordinate.
    have hnorm2 : ∀ v w : E 2, (v 0) ^ 2 + (v 1) ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 →
        ‖v‖ = ‖w‖ := by
      intro v w hvw
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two,
        Fin.sum_univ_two]
      simp only [Real.norm_eq_abs, sq_abs]
      rw [hvw]
    have hn2 : ‖y - neumannImage2 x‖ = ‖y - x‖ := by
      refine hnorm2 _ _ ?_
      simp only [PiLp.sub_apply, neumannImage2_apply_zero, neumannImage2_apply_one, hy1]
      ring
    have hn3 : ‖y - neumannImage3 x‖ = ‖y - neumannImage1 x‖ := by
      refine hnorm2 _ _ ?_
      simp only [PiLp.sub_apply, neumannImage3_apply_zero, neumannImage3_apply_one,
        neumannImage1_apply_zero, neumannImage1_apply_one, hy1]
      ring
    rw [hgeq]
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      neumannImage1_apply_one, neumannImage2_apply_one, neumannImage3_apply_one,
      hn2, hn3, hy1]
    ring

end Problems.Undergraduate.Problem21
