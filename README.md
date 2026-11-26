# When Do Randomized Sketches Match Gaussian Sketches in Randomized SVD?

This repository is the Lean 4 companion to the paper. It formalizes all six numbered results, including both directions of the main theorem, its explicit convergence rates, and the three corollaries.

The [statement and proof correspondence](CORRESPONDENCE.md) gives manuscript locations and Lean declarations for revision `fce1834`.

## Build and verify

Install [Elan](https://github.com/leanprover/elan), then clone and build the project.

```sh
git clone https://github.com/yuningyang19/rsvd-typical-orientations-lean.git
cd rsvd-typical-orientations-lean
lake exe cache get
lake build
lake env lean checks/PaperStatements.lean
lake env lean checks/ClaimBoundaries.lean
lake env lean checks/Axioms.lean
```

`lean-toolchain` pins Lean 4.33.0, and `lake-manifest.json` pins Mathlib and the other dependencies. With the Lean 4 extension in VS Code, open [PaperStatements.lean](checks/PaperStatements.lean) and use Go to Definition on a declaration named in a `#check` command to see its statement and proof.

Import `TypicalOrientations` to use the six results from the `TypicalOrientations` namespace in your own Lean files.

The build and all three checks passed from a fresh public clone. The axiom audit covered 113 declarations and found only `propext`, `Classical.choice`, and `Quot.sound`. [Verification records](evidence/lean-checks.json)

## Dependencies

All paper-specific Lean definitions and proofs are included in this repository. `TypicalOrientations/` contains the proofs for this paper. `SketchOrientation/` contains the Lean sources for supporting results, including Gaussian and Haar calculations, projector and residual identities, and Walsh and DCT results. Lake fetches Mathlib and its transitive dependencies at the revisions recorded in `lake-manifest.json`.

## Follow the paper in Lean

Use the [correspondence table](CORRESPONDENCE.md) to look up a result by its number or TeX label. Each entry links to the Lean declaration and traces the proof steps. For Theorem 1.1, start at `TypicalOrientations.theorem_1_1`. The definitions `conditionalMean`, `gaussianMean`, and `meanDiscrepancy` give the sketch mean at a fixed orientation, the Gaussian benchmark, and the supremum over spectra of the mean absolute discrepancy over Haar orientations, respectively.
