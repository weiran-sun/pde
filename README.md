# Lean Formalization of PDE Topics

The files in this directory contain formalizations of selected topics of PDE (partial differential equations) into [Lean](https://lean-lang.org/).
The ultimate goal of this formalization is to prepare a comprehensive toolbox for formal analysis of PDEs, for both research and education purposes.
This formalization may _not_ be fully optimized for efficient Lean compilation, and may have compatibility issues with the latest Lean and mahtlib versions (which evolve very rapidly).


## References
["Partial Differential Equations, A First Course"](https://bookstore.ams.org/amstext-54/),  [Rustom Choksi](https://scholar.google.com/citations?user=Fk1zaTgAAAAJ&hl=en), AMS, 2022.


## Sections

### Basics

#### Heat

- [HeatKernel](https://weiran-sun.github.io/pde/PDE/Basics/Heat/HeatKernel.html): The Fundamental Solution/Heat Kernel and Its Properties.
- [HeatSolution](https://weiran-sun.github.io/pde/PDE/Basics/Heat/HeatSolution.html): The convolution solution of the heat kernel.
- [HeatSolutionProperty](https://weiran-sun.github.io/pde/PDE/Basics/Heat/HeatSolutionProperty.html): Properties of the heat solution, involving the convolution of the heat kernel and the initial condition


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
