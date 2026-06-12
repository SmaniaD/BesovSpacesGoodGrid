# BesovSpacesGoodGrid

[Read the PDF documentation](docpdf/Documentation.pdf)

A Lean 4/mathlib project formalizing parts of the theory of Besov spaces built
from atomic decompositions over weak grids and good grids.  The development is
based on the framework of

Daniel Smania, *Besov-ish spaces through atomic decomposition*,
Analysis & PDE 15 (2022), no. 1, 123-174.
DOI: <https://doi.org/10.2140/apde.2022.15.123>


## Current State

The aggregate root module is `BesovSpacesGoodGrid.lean`.  Its source imports
the weak-grid API, atom families, Besov-ish spaces, scale inclusions,
completeness theorems, weak-grid multipliers, induced grids, weak-grid
transmutation, the good-grid Besov-atom comparison layer, the
Haar/standard/oscillation comparison files, the Dirac-approximation layer,
the good-grid multiplier layer, and the positive cone.  The repository also
contains auxiliary indexed-sum infrastructure.

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
- Pointwise-multiplier definitions on weak grids
  (`WeakGrid/Multipliers.lean`): pointwise multiplication packaged as a
  bounded operation on an atomic Besov-ish space, together with the
  Triebel-style `selfs` condition obtained by testing on unit atoms.
- Haar and standard representation gauges on good grids, including the
  comparison
  `exists_standardRepresentationNorm_le_const_mul_haarL2RepresentationNorm`,
  a second, parametrized Haar representation whose atoms carry the Besov
  parameter directly, the two-sided comparison between the `L^2`-normalized
  and parametrized Haar gauges, and the packaged bound
  `N_st(f) <= C * ||f||_Besov` of the standard representation norm by the
  Souza-Besov gauge.
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
- The positive cone for Souza-Besov spaces (`GoodGrid/PositiveCone.lean`):
  positive level blocks and representations with canonical Souza atoms and
  nonnegative real coefficients, and the associated positive coefficient-cost
  gauge.
- The fully proved positive-cone version of the non-Archimedean estimate
  (`souzaNonArchimedeanPropertyPositiveCone`, public statement in
  `NonArchimedeanPropertyPositiveStandalone.lean`), following Remark `posrem`
  of the paper, with the two consequences separated by their true strengths:
  the support consequence is unconditional (a.e. nonvanishing on active
  cells), and cone positivity of the product representation follows from
  positivity of the input representation.
- The continuous inclusion of the tail `selfs` classes in the multiplier
  space (`GoodGrid/Multipliers/SelfsSubsetMultipliers.lean`, paper
  Corollary 18.6): `exists_souzaSelfsMultiplierConstant` and the inclusion
  and continuity forms, via a level-lowering step and the non-Archimedean
  estimate applied to a one-element family.
- Strongly regular domains and Pointwise Multipliers I
  (`GoodGrid/Multipliers/StronglyRegularDomains.lean`, paper 18.7-18.9):
  the `StronglyRegularDomain` definition, the positive tail-`selfs` bound
  `K^{1/p}` for indicators of strongly regular domains (Proposition `pos2`),
  and the multiplier theorems `souzaPointwiseMultipliersI` and
  `souzaPointwiseMultipliersIInfinite` for finite and countable weighted
  sums of such indicators, with support localization and preservation of
  positivity.
- Dirac approximations (`GoodGrid/DiracApproximations.lean`, paper
  Section 17): the grid Dirac kernels `1_Q/m(Q)`, the evaluation of the
  partial sums of the standard representation as cell averages
  (`partialHaarSum_eq_integral_mul_diracKernel`, `claimB`), and the
  `L^infinity` bounds of Proposition 17.1.A for the standard representation
  (`claimA_standard`) and for positive Souza representations
  (`claimA_positive`).
- Pointwise Multipliers II, **complete**
  (`GoodGrid/Multipliers/Bp1overpinftyisMultiplier.lean`, paper
  Proposition 18.10 and Remark `pos3`): every `g` in
  `B^{1/p}_{p,infinity} ∩ L^infinity` is a pointwise multiplier of
  `B^s_{p,q}` for `0 < s < 1/p`, with operator bound
  `Cmult·|g|_{B^{1/p}_{p,infinity}} + |g|_infinity`
  (`souzaPointwiseMultipliersII`).  The proof comprises the input sublemma
  `exists_fouRepresentation` (the canonical standard representation of `g`
  with cost control and ancestor-tower sums bounded by `|g|_infinity`, via
  Corollary `fou` and Proposition 17.1.B), and the `u₁ + u₂` product
  construction `exists_mult_product_representation` (block form
  `exists_mult_product_blocks`): a discrete Young inequality with geometric
  kernel for the `u₁` convolution cost, the tower-sum `L^infinity` bound for
  `u₂`, `L^p` convergence of the block series, and the identification
  `g·f = u₁ + u₂` through the exact pointwise identity of truncated products
  passed to the limit along a.e.-convergent subsequences.  The positive-cone
  version of the paper's Remark `pos3` is `souzaPointwiseMultipliersIIPositive`
  (bound in the positive gauges `souzaPositiveNorm`; representation form
  `exists_mult_product_representation_pos`), where the canonical-atom
  hypothesis and the ancestor-tower bound are derived from positivity (the
  positive form of Proposition 17.1.B).

At this snapshot, a full `lake build` succeeds (3458 jobs) and the
repository compiles with **zero `sorry`**: every project module, including
`Bp1overpinftyisMultiplier.lean`, is imported by the aggregate root.
Project Lean files outside `.lake/packages` contain no `admit` and no
project-local `axiom` or `constant` declarations; the main theorems — the
non-Archimedean estimates (finite, infinite, and positive-cone versions),
the `selfs` multiplier inclusion, Pointwise Multipliers I (finite and
countable), the Dirac-approximation claims, and Pointwise Multipliers II
with its positive version — check with only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).  See `status.md` for the current
verification log.

## Build

This project uses the Lean toolchain pinned in `lean-toolchain`, currently
`leanprover/lean4:v4.30.0-rc2`, and mathlib through Lake.

The full-project check is:

```sh
lake build
```

At the current snapshot this succeeds with no `sorry` warnings.

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
- `BesovSpacesGoodGrid/WeakGrid/Multipliers.lean`: pointwise multiplication as
  a bounded operation on Besov-ish spaces and the `selfs` condition on weak
  grids.
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
  non-Archimedean multiplier estimate and the cores of its positive-cone
  versions.
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/NonArchimedeanPropertyPositiveStandalone.lean`:
  the user-facing positive-cone statement, forwarding to the assembly core.
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/SelfsSubsetMultipliers.lean`: the
  continuous inclusion of the tail `selfs` classes in the multiplier space
  (paper Corollary 18.6).
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/StronglyRegularDomains.lean`:
  strongly regular domains, the positive tail-`selfs` bound for their
  indicators, and Pointwise Multipliers I (paper 18.7-18.9).
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/Bp1overpinftyisMultiplier.lean`:
  Pointwise Multipliers II (paper Proposition 18.10): `B^{1/p}_{p,infinity} ∩
  L^infinity` consists of pointwise multipliers of `B^s_{p,q}`, via the
  `u₁ + u₂` atomic product construction, a discrete Young inequality with
  geometric kernel, and the truncated-product identity; includes the
  positive-cone version of the paper's Remark `pos3`.
- `BesovSpacesGoodGrid/GoodGrid/DiracApproximations.lean`: the grid Dirac
  kernels, evaluation of partial standard sums as cell averages, and the
  bounds of paper Proposition 17.1.
- `BesovSpacesGoodGrid/GoodGrid/PositiveCone.lean`: positive Souza
  representations and the positive coefficient-cost gauge for Souza-Besov
  spaces.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms.lean`: public
  aggregator for the Haar, standard, and mean-oscillation representation and
  norm-comparison files.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/HaarRepresentationNorm.lean`: normalized Haar
  coefficients and the Haar representation gauge.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/HaarParametrizedRepresentation.lean`: the
  parametrized Haar representation whose atoms carry the Besov parameter, with
  its unweighted coefficient gauge.
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/ComparingHaarRepresentationsl.lean`: two-sided
  comparison between the `L^2`-normalized and parametrized Haar gauges.
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
- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/StandarRepresentationNormleqBesovNorm.lean`:
  the packaged bound of the standard representation norm by the Souza-Besov
  gauge, chaining the standard/Haar, Haar/oscillation, and oscillation/Besov
  comparisons.
- `BesovSpacesGoodGrid/GoodGrid/Distribution.lean`: test functions
  and distributions associated with a good grid.
- `BesovSpacesGoodGrid/Sums.lean`: reusable block-index and block-sum
  notation.
- `docpdf/Documentation.tex` and `docpdf/Documentation.pdf`:
  the unified documentation — the results of the paper formalized in Lean,
  organized to mirror the repository (Part I: weak-grid library, Part II:
  good-grid library, sections in file-dependency order, each opened by a
  box with the Lean file and its imports), with in-text descriptions of the
  Lean declarations, code snapshots, mathematical overviews of each file,
  the purpose of the formalization, and a guide to the repository files.
  References to numbered statements follow the published version of the
  paper (Analysis & PDE 15 (2022), no. 1).
- `status.md`: current verification log and progress notes.
- `paper-map.md`: correspondence between the paper's statements and the Lean
  declarations.
- `lakefile.toml`: Lake package configuration.
- `lean-toolchain`: Lean toolchain pin.
- `lake-manifest.json`: resolved dependency manifest.

## Next Work

The repository currently builds with **zero `sorry`**.  Likely next steps
(see `todo.md` for details) are:

- the wrap-up equivalence theorem for paper Theorem 15.1 (packaging the
  proved inequality cycle) and the `L¹` functional of Corollary 15.2;
- the Section 16 examples: the Holder atom family with Proposition 16.2, and
  bounded-variation atoms with Proposition 16.3 (applications of
  `atoms_between_souza_atoms_and_besov_atoms`);
- paper Sections 19-21 (the quasialgebra structure, `B^{1-s} = B^s_{1,1}`,
  and left compositions);
- continue polishing public docstrings around the large transmutation,
  completeness, and multiplier files;
- factor large proof-heavy files (notably `Multipliers/NonArchimedeanProperty.lean`
  and `WeakGrid/Transmutation.lean`) into smaller topic-focused modules if
  compilation time or navigation becomes cumbersome;
- clean deprecation/style warnings in the newer files.
