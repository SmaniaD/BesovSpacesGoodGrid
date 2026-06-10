# BesovSpacesGoodGrid

[Read the PDF documentation](docpdf/documentation.pdf)

A Lean 4/mathlib project formalizing parts of the theory of Besov spaces built
from atomic decompositions over weak grids and good grids.  The development is
based on the framework of

Daniel Smania, *Besov-ish spaces through atomic decomposition*,
Analysis & PDE 15 (2022), no. 1, 123-174.
DOI: <https://doi.org/10.2140/apde.2022.15.123>

[Doc-Gen documentation](https://smaniad.github.io/BesovSpacesGoodGrid/BesovSpacesGoodGrid.html)

## Current State

The aggregate root module is `BesovSpacesGoodGrid.lean`.  Its source imports
the weak-grid API, atom families, Besov-ish spaces, scale inclusions,
completeness theorems, induced grids, weak-grid transmutation, the good-grid
Besov-atom comparison layer, and the current Haar/standard/oscillation
comparison files.  The repository also contains auxiliary indexed-sum
infrastructure.

The formalization currently includes:

- `GoodGrid` and `GoodGridSpace`: quantitative good grids extending the
  grid API from `UnbalancedHaarWavelet`.
- `WeakGrid` and `WeakGridSpace`: finite same-level cell families with positive
  measure and uniformly bounded overlap multiplicity.
- `WeakGridCell`, `LocalBanachSpace`, and `AtomFamily`: the local Banach-space
  and atom-family abstraction used for atomic decompositions.
- `LevelBlock` and `LpGridRepresentation`: levelwise atomic blocks and
  `L^p` representations with finite `(p,q)` coefficient cost.
- `standardRepresentationNorm`: the abstract `(p,q)` cost of the canonical
  standard coefficients for an integrable function, without requiring a
  packaged `L^p` representation or a `HasSum` proof.
- `BesovishSpace` and `BesovishSpace.Norm_Costpq`: the Besov-ish subspace of
  `L^p`, together with its coefficient-cost gauge.
- Structural theorems showing that `Norm_Costpq` is nonnegative, subadditive,
  homogeneous, controls `L^t` norms, and yields a local normed-space structure.
- Scale constructions for atom families, including smoothness scaling and the
  inclusion
  `smoothnessScaleBesovishSpaceInclusion`.
- Representation-limit theorems, compactness statements for closed
  coefficient-cost balls, and completeness of `BesovishSpace` for the
  coefficient-cost norm.
- Transmutation definitions and theorems `ClaimI`, `ClaimII`, and `ClaimIII`,
  together with endpoint versions for `q = infinity`, plus the explicit
  identity-level Claim C embedding used by the good-grid comparison theorem.
- Good-grid/Souza specializations in `GoodGrid/BesovSpace.lean`, including the
  induced weak grid, Souza atoms, the Souza Besov space, compactness of closed
  balls, and density theorems.
- Good-grid Besov atoms in `GoodGrid/BesovAtoms.lean`, including the
  transmutation of Besov atoms into Souza atoms and the theorem
  `atoms_between_souza_atoms_and_besov_atoms`, which identifies the Besov-ish
  spaces associated to Souza atoms, any atom family sandwiched between Souza
  and Besov atoms, and Besov atoms themselves, with the norm constants from
  the paper.
- Haar and standard representation gauges on good grids, including the
  comparison
  `exists_standardRepresentationNorm_le_const_mul_haarL2RepresentationNorm`.
- Finite-norm endpoint results showing that finite standard norm gives
  `L^p` membership, a canonical standard representation, finite cost, and
  Souza-Besov membership, and that finite Haar norm gives `L^p` membership
  and Haar expansion convergence.
- Mean-oscillation results connecting the standard representation norm,
  `meanOscillationNorm`, and the Haar representation norm by finite-constant
  comparison theorems.
- A pointwise-multiplier layer on good grids (`GoodGrid/Multipliers/`):
  the level-tail Souza `selfs` classes (`SouzaPointwiseSelfsTailBound`,
  `SouzaPointwiseSelfsTailClass`) and the `selfs` seminorm; the proof that
  tail-`selfs` multipliers are bounded, i.e. `souzaPointwiseSelfsTailBound_norm_ae_le`
  and `souzaPointwiseSelfsTailNorm_norm_ae_le_add` give an `L^infinity` bound
  uniform in the tail level `t`; the `B^s_{1,1}` characterization
  `souzaPointwiseMultiplier_iff_souzaPointwiseSelfsClass_one_one`; and the
  non-Archimedean multiplier estimate `souzaNonArchimedeanPropertyLambdaFinite`
  and its infinite-index pointwise form `souzaNonArchimedeanProperty`.
- A positive-cone version of the non-Archimedean estimate
  (`souzaNonArchimedeanPropertyPositiveCone`) is in progress: the statement and
  the assembly core are in place, with the support consequence and the
  cone-positivity consequence proved at the with-errors and `N > 0` layers; two
  `sorry`s remain (the `N = 0` degenerate case and the positive local
  transmutation-data builder).

At this snapshot, a full `lake build` succeeds: the aggregate root module and
all imported modules compile.  The previous root import/name issue involving
`GoodGridSpace.GoodGridCell.toLevelCell` has been resolved.  Project Lean files
outside `.lake/packages` contain no `admit` and no project-local `axiom` or
`constant` declarations; the only Lean `sorry`s are the two in the in-progress
positive-cone multiplier file `GoodGrid/Multipliers/NonArchimedeanProperty.lean`
(they build as `sorry` warnings).  See `status.md` for the current
verification log.

## Build

This project uses the Lean toolchain pinned in `lean-toolchain`, currently
`leanprover/lean4:v4.30.0-rc2`, and mathlib through Lake.

The full-project check is:

```sh
lake build
```

At the current snapshot this succeeds (the only warnings come from the two
`sorry`s in the in-progress positive-cone multiplier file).

To check an individual module in isolation, for example the multiplier files:

```sh
lake build BesovSpacesGoodGrid.GoodGrid.Multipliers
lake env lean BesovSpacesGoodGrid/GoodGrid/Multipliers/MultipliersareBounded.lean
```

## Project Files

- `BesovSpacesGoodGrid.lean`: aggregate library entry point for the weak-grid,
  good-grid, Haar, standard-representation, and oscillation layers.
- `BesovSpacesGoodGrid/GoodGrid/Definition.lean`: good grids with quantitative
  parent-child measure-ratio bounds.
- `BesovSpacesGoodGrid/WeakGrid/Definition.lean`: weak grids and overlap
  counting estimates.
- `BesovSpacesGoodGrid/WeakGrid/Atoms.lean`: cells, local Banach
  spaces, atom families, and basic atom lemmas.
- `BesovSpacesGoodGrid/WeakGrid/BesovishSpaces.lean`: level blocks,
  representations, coefficient costs, Besov-ish spaces, and the cost gauge.
- `BesovSpacesGoodGrid/WeakGrid/Scales.lean`: scaled atom families
  and smoothness-scale inclusions.
- `BesovSpacesGoodGrid/WeakGrid/Completeness.lean`:
  representation limits, compactness of cost balls, and completeness.
- `BesovSpacesGoodGrid/WeakGrid/InducedGrid.lean`: induced weak grids on a
  fixed cell and the contraction into the ambient Besov-ish space.
- `BesovSpacesGoodGrid/WeakGrid/Transmutation.lean`: weak-grid transmutation and
  the formal versions of Claims I, II, and III.
- `BesovSpacesGoodGrid/GoodGrid/BesovSpace.lean`: Souza atoms and good-grid
  Besov-space consequences.
- `BesovSpacesGoodGrid/GoodGrid/BesovAtoms.lean`: Besov atoms on good grids and
  the Souza/Besov atom comparison theorem.
- `BesovSpacesGoodGrid/GoodGrid/Multipliers.lean`: public aggregator for the
  good-grid pointwise-multiplier files.
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/Definition.lean`: the level-tail
  Souza `selfs` classes and seminorm.
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/Besovspq.lean`: induced-cell Souza
  representations and restriction/transmutation infrastructure for multipliers.
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/Besovs11.lean`: the `B^s_{1,1}`
  pointwise-multiplier characterization.
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/MultipliersareBounded.lean`:
  boundedness (`L^infinity`) of tail-`selfs` multipliers, uniform in the tail
  level.
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/NonArchimedeanProperty.lean`: the
  non-Archimedean multiplier estimate and the in-progress positive-cone version.
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/NonArchimedeanPropertyPositiveStandalone.lean`:
  the user-facing positive-cone statement, forwarding to the assembly core.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms.lean`: public
  aggregator for the Haar, standard, and mean-oscillation representation and
  norm-comparison files.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/HaarRepresentationNorm.lean`: normalized Haar
  coefficients and the Haar representation gauge.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/standardRepresentation.lean`: standard atomic
  coefficients and the standard representation gauge.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/standardNormleqHaarRepresenstionNorm.lean`:
  control of the standard representation norm by the Haar representation norm.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/FiniteStandardNormimpliesBesov.lean`: finite
  standard norm implies `L^p`, a canonical representation, finite cost, and
  Souza-Besov membership.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/FiniteHaarNormimpliesLp.lean`: finite Haar norm
  implies `L^p` membership and Haar expansion convergence.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/MeanOscillationNorm.lean`: mean-oscillation
  definitions and reusable oscillation lemmas.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/OscillationNormleqBesovNorm.lean`: control of
  mean oscillation by the standard representation norm.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/HaarNormleqOscillationNorm.lean`: control of
  the Haar representation norm by mean oscillation.
- `BesovSpacesGoodGrid/GoodGrid/Distribution.lean`: test functions
  and distributions associated with a good grid.
- `BesovSpacesGoodGrid/Sums.lean`: reusable block-index and block-sum
  notation.
- `docpdf/documentation.tex` and `docpdf/documentation.pdf`:
  the unified documentation — the results of the paper formalized in Lean,
  organized to mirror the repository (Part I: weak-grid library, Part II:
  good-grid library, sections in file-dependency order, each opened by a
  box with the Lean file and its imports), with in-text descriptions of the
  Lean declarations, code snapshots, mathematical overviews of each file,
  the purpose of the formalization, and a guide to the repository files.
  References to numbered statements follow the published version of the
  paper (Analysis & PDE 15 (2022), no. 1).
- `lakefile.toml`: Lake package configuration.
- `lean-toolchain`: Lean toolchain pin.
- `lake-manifest.json`: resolved dependency manifest.

## Next Work

The project currently builds with **zero `sorry`** (the positive-cone
non-Archimedean theorems, finite and infinite, are fully proved with axioms
checked). Likely next steps are:

- continue polishing public docstrings around the large transmutation,
  completeness, and multiplier files;
- factor large proof-heavy files (notably `Multipliers/NonArchimedeanProperty.lean`
  and `WeakGrid/Transmutation.lean`) into smaller topic-focused modules if
  compilation time or navigation becomes cumbersome;
- clean deprecation/style warnings in the newer files.
