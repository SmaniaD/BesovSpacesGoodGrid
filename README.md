# BesovSpacesGoodGrid

[Read the PDF documentation](docpdf/Documentation.pdf)

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

At this snapshot, project Lean files outside `.lake/packages` contain no Lean
`sorry`, no Lean `admit`, and no project-local `axiom` or `constant`
declarations.  The main comparison modules check individually.  The aggregate
root module currently has a known import/name organization issue involving
`GoodGridSpace.GoodGridCell.toLevelCell`; see `status.md` for the current
verification log.

## Build

This project uses the Lean toolchain pinned in `lean-toolchain`, currently
`leanprover/lean4:v4.30.0-rc2`, and mathlib through Lake.

The intended full-project check is:

```sh
lake build
```

At the current snapshot, the aggregate root import still needs the
`GoodGridCell.toLevelCell` issue recorded in `status.md` to be resolved before
that full build is expected to pass.

For focused checks of the most recent comparison modules:

```sh
lake env lean BesovSpacesGoodGrid/GoodGrid/OscillationNormleqBesovNorm.lean
lake env lean BesovSpacesGoodGrid/GoodGrid/HaarNormleqOscillationNorm.lean
```

The aggregate root check is the intended final smoke test, but it currently
needs the import/name issue recorded in `status.md` to be resolved first.

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
- `BesovSpacesGoodGrid/GoodGrid/HaarRepresentationNorm.lean`: normalized Haar
  coefficients and the Haar representation gauge.
- `BesovSpacesGoodGrid/GoodGrid/standardRepresentation.lean`: standard atomic
  coefficients and the standard representation gauge.
- `BesovSpacesGoodGrid/GoodGrid/standardNormleqHaarRepresenstionNorm.lean`:
  control of the standard representation norm by the Haar representation norm.
- `BesovSpacesGoodGrid/GoodGrid/FiniteStandardNormimpliesBesov.lean`: finite
  standard norm implies `L^p`, a canonical representation, finite cost, and
  Souza-Besov membership.
- `BesovSpacesGoodGrid/GoodGrid/FiniteHaarNormimpliesLp.lean`: finite Haar norm
  implies `L^p` membership and Haar expansion convergence.
- `BesovSpacesGoodGrid/GoodGrid/MeanOscillationNorm.lean`: mean-oscillation
  definitions and reusable oscillation lemmas.
- `BesovSpacesGoodGrid/GoodGrid/OscillationNormleqBesovNorm.lean`: control of
  mean oscillation by the standard representation norm.
- `BesovSpacesGoodGrid/GoodGrid/HaarNormleqOscillationNorm.lean`: control of
  the Haar representation norm by mean oscillation.
- `BesovSpacesGoodGrid/GoodGrid/Distribution.lean`: test functions
  and distributions associated with a good grid.
- `BesovSpacesGoodGrid/Sums.lean`: reusable block-index and block-sum
  notation.
- `docpdf/Documentation.tex` and `docpdf/Documentation.pdf`: narrative
  documentation for the current formalization.
- `lakefile.toml`: Lake package configuration.
- `lean-toolchain`: Lean toolchain pin.
- `lake-manifest.json`: resolved dependency manifest.

## Next Work

Likely next steps are:

- resolve the aggregate root import/name collision around
  `GoodGridSpace.GoodGridCell.toLevelCell`;
- run a full `lake build` once the root module imports cleanly;
- decide whether `GoodGrid.Distribution` and `Sums` should be imported by the
  root module or kept as opt-in modules;
- continue polishing public docstrings around the large transmutation and
  completeness files;
- factor large proof-heavy files into smaller topic-focused modules if
  compilation time or navigation becomes cumbersome;
- clean deprecation/style warnings in the new comparison files.
