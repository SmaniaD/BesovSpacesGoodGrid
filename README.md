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

The root module is `BesovSpacesGoodGrid.lean`.  It currently imports the weak
grid API, atom families, Besov-ish spaces, scale inclusions, completeness
theorems, and weak-grid transmutation.  The repository also contains ongoing
good-grid specializations and auxiliary indexed-sum infrastructure.

The formalization currently includes:

- `GoodGrid` and `GoodGridSpace`: quantitative good grids extending the
  grid API from `UnbalancedHaarWavelet`.
- `WeakGrid` and `WeakGridSpace`: finite same-level cell families with positive
  measure and uniformly bounded overlap multiplicity.
- `WeakGridCell`, `LocalBanachSpace`, and `AtomFamily`: the local Banach-space
  and atom-family abstraction used for atomic decompositions.
- `LevelBlock` and `LpGridRepresentation`: levelwise atomic blocks and
  `L^p` representations with finite `(p,q)` coefficient cost.
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
  together with endpoint versions for `q = infinity`.
- Good-grid/Souza specializations in `GoodGrid/BesovSpace.lean`, including the
  induced weak grid, Souza atoms, the Souza Besov space, compactness of closed
  balls, and density theorems.

At this snapshot, the repository has no `sorry`, `admit`, or project-local
axiom declarations.

## Build

This project uses the Lean toolchain pinned in `lean-toolchain`, currently
`leanprover/lean4:v4.30.0-rc2`, and mathlib through Lake.

```sh
lake build
```

For a quick check of the root module:

```sh
lake env lean BesovSpacesGoodGrid.lean
```

## Project Files

- `BesovSpacesGoodGrid.lean`: library entry point for the main weak-grid
  development.
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

- decide whether `GoodGrid.BesovSpace`, `GoodGrid.Distribution`, and
  `Sums` should be imported by the root module or kept as opt-in modules;
- continue polishing public docstrings around the large transmutation and
  completeness files;
- factor large proof-heavy files into smaller topic-focused modules if
  compilation time or navigation becomes cumbersome;
- add downstream examples showing how the weak-grid theorems specialize to
  concrete good-grid Besov spaces.
