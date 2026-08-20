# Lean Formalization of PDE Topics

This repository formalizes selected topics in partial differential equations in [Lean](https://lean-lang.org/). Its goal is to provide a reusable toolbox for formal PDE analysis in research and education.

The current development covers analytic background, the heat, Laplace, and wave equations, Sobolev spaces, ODE existence theory, and the Galerkin method for parabolic equations. It targets Lean and Mathlib `v4.33.0-rc1`. The project is under active development: some declarations still contain `sorry`, and the code is not always optimized for compilation speed or idiomatic Lean usage.


## Reference

["Partial Differential Equations, A First Course"](https://bookstore.ams.org/amstext-54/) by [Rustom Choksi](https://scholar.google.com/citations?user=Fk1zaTgAAAAJ&hl=en), AMS, 2022.


## Formalized Topics

### Background

#### Calculus, geometry, and measure theory

- [DomainGeometry](PDE/Background/CalculusMeasureTheory/DomainGeometry.lean): Topological and metric lemmas for balls, spheres, frontiers, and punctured domains.
- [PDEDomains](PDE/Background/CalculusMeasureTheory/PDEDomains.lean): Domain classes for PDE arguments, together with support and convolution estimates.
- [HausdorffUnitCircleSphere](PDE/Background/CalculusMeasureTheory/HausdorffUnitCircleSphere.lean): Hausdorff measure calculations for the unit circle and sphere.
- [SphereSurfaceMeasure](PDE/Background/CalculusMeasureTheory/SphereSurfaceMeasure.lean): Surface measure, Hausdorff measure, and scaling formulas for spheres in three dimensions.
- [R3GraphMeasure](PDE/Background/CalculusMeasureTheory/GraphHausdorffMeasure/R3GraphMeasure.lean): Area formula for a `C¹` graph in three dimensions.
- [RnGraphHausdorffMeasure](PDE/Background/CalculusMeasureTheory/GraphHausdorffMeasure/RnGraphHausdorffMeasure.lean): Area formula for a `C¹` graph in arbitrary dimension.
- [SurfaceIntegration](PDE/Background/CalculusMeasureTheory/GraphHausdorffMeasure/SurfaceIntegration.lean): Integration of scalar and vector-valued functions over `C¹` graphs.
- [R3Divergence](PDE/Background/CalculusMeasureTheory/DivergenceTheorem/R3Divergence.lean): A complete divergence theorem development in three dimensions.
- [GeneralizedDivergence](PDE/Background/CalculusMeasureTheory/DivergenceTheorem/GeneralizedDivergence.lean): The divergence theorem in arbitrary finite dimension.

#### Functional analysis

- [DistributionPairing1D](PDE/Background/FunctionalAnalysis/DistributionPairing1D.lean): Shared one-dimensional distribution pairings and integration-by-parts tools.
- [HilbertWeakCompactness](PDE/Background/FunctionalAnalysis/HilbertWeakCompactness.lean): Weak sequential compactness for bounded sequences in separable Hilbert spaces.
- [OrthonormalBasis](PDE/Background/FunctionalAnalysis/OrthonormalBasis.lean): Orthogonality and normalization of the sine system on `[0, π]`.

### Function Spaces

#### Sobolev spaces

- [LpFunctionSpaces](PDE/FunctionSpaces/SobolevSpace/LpFunctionSpaces.lean): Compactly supported smooth test functions and local `Lᵖ` spaces.
- [WeakDerivative](PDE/FunctionSpaces/SobolevSpace/WeakDerivative.lean): Weak derivatives defined through test-function pairings.
- [SobolevSpaces](PDE/FunctionSpaces/SobolevSpace/SobolevSpaces.lean): The spaces `W^{k,p}(U)`, their weak derivatives, and normed-space structure.
- [HkSpaces](PDE/FunctionSpaces/SobolevSpace/HkSpaces.lean): Hilbert Sobolev spaces `H^k(U) = W^{k,2}(U)` and their inner-product structure.
- [Mollification](PDE/FunctionSpaces/SobolevSpace/Mollification.lean): Zero extension, convolution mollification, smoothness, and approximation tools.

### Basic PDEs

- [LaplacianBridge](PDE/Basics/LaplacianBridge.lean): Equivalence between the project's trace-based Laplacians and Mathlib's Laplacian.

#### Heat equation

- [HeatKernel](PDE/Basics/Heat/HeatKernel.lean): The one-dimensional heat kernel, its positivity, normalization, derivatives, and the heat equation.
- [HeatConvolutionAbstract](PDE/Basics/Heat/HeatConvolutionAbstract.lean): An abstract differentiation-under-the-integral theorem showing that convolution solves the heat equation.
- [HeatSolution](PDE/Basics/Heat/HeatSolution.lean): The heat-kernel convolution solution and its derivative formulas.
- [HeatSolutionProperty](PDE/Basics/Heat/HeatSolutionProperty.lean): Symmetry, mass, maximum-principle, and initial-value properties of the heat solution.
- [HeatDecay](PDE/Basics/Heat/HeatDecay.lean): Large-time decay for heat solutions with integrable initial data.
- [HeatMaximumPrinciple](PDE/Basics/Heat/HeatMaximumPrinciple.lean): The maximum principle on a finite space-time cylinder in one dimension.
- [HeatKernelND](PDE/Basics/Heat/HeatKernelND.lean): The heat kernel and Gaussian identities in arbitrary finite dimension.
- [HeatSolutionND](PDE/Basics/Heat/HeatSolutionND.lean): The heat-kernel convolution solution in arbitrary finite dimension.
- [HeatSolutionPropertyND](PDE/Basics/Heat/HeatSolutionPropertyND.lean): Mass, maximum-principle, and initial-value properties in arbitrary finite dimension.
- [HeatMaximumPrincipleND](PDE/Basics/Heat/HeatMaximumPrincipleND.lean): The maximum principle on finite-dimensional rectangular space-time cylinders.

#### Laplace equation

- [CalculusBasic](PDE/Basics/Laplace/CalculusBasic.lean): Calculus, compact-support, inverse-norm, and punctured-domain lemmas used throughout the Laplace theory.
- [GreensIdentities](PDE/Basics/Laplace/GreensIdentities.lean): Spherical integration, punctured-domain flux, and Green's identities.
- [SphericalMeans](PDE/Basics/Laplace/SphericalMeans.lean): Spherical integrands, radial derivatives, spherical means, and related bounds.
- [LaplaceMeanValue](PDE/Basics/Laplace/LaplaceMeanValue.lean): The mean-value property for harmonic functions in three dimensions.
- [LaplaceMaximumPrinciple](PDE/Basics/Laplace/LaplaceMaximumPrinciple.lean): Maximum principles and uniqueness for harmonic functions in three dimensions.
- [LaplaceMaximumPrincipleND](PDE/Basics/Laplace/LaplaceMaximumPrincipleND.lean): Weak maximum and minimum principles in arbitrary finite dimension.
- [LaplaceDirichletPrinciple](PDE/Basics/Laplace/LaplaceDirichletPrinciple.lean): Dirichlet-energy minimization and harmonicity.
- [FundamentalSolution](PDE/Basics/Laplace/FundamentalSolution.lean): The three-dimensional fundamental solution and its differential properties.
- [FundamentalSolutionND](PDE/Basics/Laplace/FundamentalSolutionND.lean): Fundamental solutions and harmonicity away from the origin in dimension `N ≥ 2`.
- [LaplaceDistributionalLaplacian](PDE/Basics/Laplace/LaplaceDistributionalLaplacian.lean): The distributional Laplacian of `1/‖x‖` in three dimensions.
- [PoissonEquation](PDE/Basics/Laplace/PoissonEquation.lean): Convolution with the fundamental solution for Poisson's equation.
- [RepresentationFormula](PDE/Basics/Laplace/RepresentationFormula.lean): Green's representation formula on PDE domains.
- [GreensFunction](PDE/Basics/Laplace/GreensFunction.lean): Green's functions, harmonic correctors, and representation results.
- [GreensFunctionSymmetry](PDE/Basics/Laplace/GreensFunctionSymmetry.lean): Symmetry of Green's functions.

#### Wave equation

- [WaveGeneralSolution1D](PDE/Basics/Wave/WaveGeneralSolution1D.lean): Traveling-wave characterization of general one-dimensional solutions.
- [WaveIVP1D](PDE/Basics/Wave/WaveIVP1D.lean): D'Alembert's formula for the one-dimensional initial-value problem.
- [WaveIVPSource1D](PDE/Basics/Wave/WaveIVPSource1D.lean): D'Alembert's formula with a source term and the dependence triangle.
- [WaveBVP1D](PDE/Basics/Wave/WaveBVP1D.lean): The fixed-end half-line problem via odd reflection.
- [WaveEnergyConservation1D](PDE/Basics/Wave/WaveEnergyConservation1D.lean): Conservation and balance laws for the total energy.
- [WaveIVP2D](PDE/Basics/Wave/WaveIVP2D.lean): Poisson's solution formula for the two-dimensional initial-value problem.

### Methods

#### ODE methods

- [CaratheodoryExistence](PDE/Methods/ODEMethods/CaratheodoryExistence.lean): A self-contained proof of the Carathéodory existence theorem for ODEs.

#### Galerkin method for parabolic equations

- [ParabolicOperator](PDE/Methods/Galerkin/Parabolic/ParabolicOperator.lean): Parabolic coefficients, bilinear forms, weak solutions, energy estimates, and Galerkin limits.
- [ParabolicExistence](PDE/Methods/Galerkin/Parabolic/ParabolicExistence.lean): Galerkin ODE solvability and weak-solution existence for continuous-in-time data.
- [ParabolicExistenceCaratheodory](PDE/Methods/Galerkin/Parabolic/ParabolicExistenceCaratheodory.lean): Galerkin ODE solvability under measurable-in-time Carathéodory assumptions.


## Other Resources

- [Web page for this project](https://weiran-sun.github.io/pde/)
<!-- - [Blog post announcing this project](https://), XXX, May 31 2025. -->
<!-- - [Lean Zulip discussion about this project](https://leanprover.zulipchat.com/#narrow/channel/) -->
<!-- - [Notes for contributors](./CONTRIBUTING.md) -->


## Building the Project

To build this project after [installing Lean](https://lean-lang.org/documentation/setup/) and cloning this repository, follow these steps:

```
% ./build.sh
```

You can then serve the documentation locally as a webpage by executing `python3 serve.py`

### Updating the Lean/Mathlib version

Because this project uses a deprecated method to conditionally require `doc-gen4`
in order to update the version of Lean and Mathlib used in the project you need to:
* edit the `lakefile.lean` to change the `require` lines for Mathlib and doc-gen4,
  to pin to the tag corresponding to the next Lean version
  (it is highly recommended that you update in incremental steps)
* edit the `lean-toolchain` to change the Lean version to the next version
* run `lake update -R -Kenv=dev`
* this may have the side effect of setting your `lean-toolchain` to the *latest* Lean version;
  if so, revert it to the intended version


## General Lean Resources

**This list is largely inherited from, and thus credited to, Professor Tao's [Analysis](https://github.com/teorth/analysis).**

- [The Lean community](https://leanprover-community.github.io/)
  - [Lean4 web playground](https://live.lean-lang.org/)
  - [How to run a project in Lean locally](https://leanprover-community.github.io/install/project.html)
  - [The Lean community Zulip chat](https://leanprover.zulipchat.com/)
  - [Learning Lean4](https://leanprover-community.github.io/learn.html)
    - [The natural number game](https://adam.math.hhu.de/)
    - [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) - Lean textbook by Jeremy Avigad and Patrick Massot
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
  - [Mathlib help files](https://seasawher.github.io/mathlib4-help/)
  - [LeanFinder](https://leanfinder.github.io/) - Natural language search engine for Mathlib
  - [List of Mathlib tactics](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)
    - [Lean tactics cheat sheet](https://github.com/fpvandoorn/LeanCourse24/blob/master/lean-tactics.pdf)
- Lean extensions:
  - [Canonical](https://github.com/chasenorman/Canonical)
  - [Duper](https://github.com/leanprover-community/duper)
  - [LeanCopilot](https://github.com/lean-dojo/LeanCopilot)
- [Common Lean pitfalls](https://github.com/nielsvoss/lean-pitfalls)
- [Lean4 questions in Proof Stack Exchange](https://proofassistants.stackexchange.com/questions/tagged/lean4)
- [The mechanics of proof](https://hrmacbeth.github.io/math2001/) - introductory Lean textbook by Heather Macbeth
- A [broader list](https://docs.google.com/document/d/1kD7H4E28656ua8jOGZ934nbH2HcBLyxcRgFDduH5iQ0) of AI and formal mathematics resources.

More resource suggestions welcome!


## Acknowledgment

* Professor Terence Tao's [Analysis](https://github.com/teorth/analysis)
