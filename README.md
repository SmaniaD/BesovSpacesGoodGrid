# BesovSpacesGoodGrid

[Read the PDF documentation](docpdf/Documentation.pdf)

[Paper-to-Lean map](paper-map.md)

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
the good-grid multiplier layer, the quasi-algebra layer, and the positive
cone.  The repository also contains auxiliary indexed-sum infrastructure.

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
  `K^{1/p}` for indicators `\mathbbm{1}_Ω` of strongly regular domains
  (Proposition `pos2`),
  and the multiplier theorems `souzaPointwiseMultipliersI` and
  `souzaPointwiseMultipliersIInfinite` for finite and countable weighted
  sums of such indicators, with support localization and preservation of
  positivity.
- Dirac approximations (`GoodGrid/DiracApproximations.lean`, paper
  Section 17): the grid Dirac kernels `\mathbbm{1}_Q/m(Q)`, the evaluation of the
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
- Pointwise Multipliers III, **complete**
  (`GoodGrid/QuasiAlgebra.lean`, paper Proposition 19.1, `mult33`): the
  bounded Souza-Besov space `B^s_{p,q} ∩ L^infinity` is closed under
  pointwise multiplication, with the bilinear bound
  `|fg|_B + |fg|_infinity ≤ Cqa (|f|_B + |f|_infinity)(|g|_B + |g|_infinity)`
  (`souzaPointwiseMultipliersIII`).  The technical core
  `exists_quasiAlgebra_product_representation` runs the `u₁ + u₂`
  construction for two `(s,p)` Souza representations, with the mixed bound
  `Cprod (|f|_B·Mg + |g|_B·Mf)`: weighted and strict weighted ancestor
  towers (`weightedAncestorCoeffSum`) replace the tower sums of Pointwise
  Multipliers II, a weighted `fou` representation is extracted from the
  standard-representation machinery and Proposition 17.1.B, and the finite
  truncation identity is passed to the limit in `L^p`.
- Regular domains, **complete** (`GoodGrid/RegularDomains.lean`, paper
  subsection `cf`): the formal `k_0(Ω)` (`firstContainedLevel`), the
  `RegularFamily` (countable disjoint families indexed by `Λ ⊆ ℕ`) and
  `RegularDomain` (one-set) definitions carrying the geometric level cost
  `dom`, the bridge `RegularDomain.toRegularFamily_singleton` and the union
  construction `RegularFamily.regularDomain_union`.  It proves that every
  strongly regular domain is regular
  (`regularDomain_of_stronglyRegularDomain`, ratio `λ₂^{(β-s)p}`), the
  indicator Besov bound `estG` — finite `q`
  (`regularDomain_indicator_besov_norm_bound`) and the `q = ∞` endpoint
  (`regularDomain_indicator_besov_norm_bound_top`), where the geometric
  series collapses to a supremum and the bound simplifies to
  `C^{1/p}·μ(Ω)^{1/p-s}`, both folded into
  `regularDomain_indicator_besov_norm_bound_all` with explicit constant
  `regularDomainIndicatorCost` — together with the bounded multiplier
  `g ↦ g·1_Ω` on `B^s_{p,q} ∩ L^infinity`, again for finite `q`
  (`regularDomain_indicator_multiplier_on_bounded_souzaBesov`) and at the
  endpoint (`..._top`), unified as `..._all`, plus the family wrappers
  `regularFamilyUnion_indicator_*_all` (each handling both cases internally),
  and the localized restriction representation estimate `pdd`/`hiip1`
  (`regularFamily_restriction_representations`): each `g·1_{Ωᵣ}` gets a
  Souza representation whose nonzero level-`j` coefficients live on cells
  contained in `Ωᵣ`, with the mixed `(p,q)` coefficient cost controlled by
  `Crel·(|g|_{B^s_{p,q}} + M)` — uniformly in `q ∈ [1,∞]`, the `q = ∞` cost
  read as the supremum of the level roots.
- A remarkable description of `B^s_{1,1}`, **complete**
  (`GoodGrid/AlternativeDescriptionBs11.lean`, paper Section 20,
  Proposition `rema`): the regular-domain indicator representation
  `DomainAtomicRepresentation`, the predicate `DomainBesovSpace`, and the
  gauge `domainBesovGauge`, with both inclusions
  `domainBesovSpace_to_souzaBesov11` and
  `souzaBesov11_to_domainBesovSpace` packaged as
  `domainBesovSpace_equiv_souzaBesov11`.

At this snapshot, a full `lake build` succeeds (3462 jobs) and the whole
repository compiles with **zero `sorry`**: every project module, including
`Bp1overpinftyisMultiplier.lean`, `QuasiAlgebra.lean`,
`RegularDomains.lean`, and `AlternativeDescriptionBs11.lean`, is imported by
the aggregate root `BesovSpacesGoodGrid.lean` and is `sorry`-free.
Project Lean files outside `.lake/packages` contain no `admit` and no
project-local `axiom` or `constant` declarations; the main theorems — the
non-Archimedean estimates (finite, infinite, and positive-cone versions),
the `selfs` multiplier inclusion, Pointwise Multipliers I (finite and
countable), the Dirac-approximation claims, Pointwise Multipliers II with
its positive version, and Pointwise Multipliers III — check with only the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).  See
`status.md` for the current verification log.

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
- `BesovSpacesGoodGrid/GoodGrid/QuasiAlgebra.lean`: the quasi-algebra
  property of `B^s_{p,q} ∩ L^infinity` — Pointwise Multipliers III (paper
  Proposition 19.1), via the two-sided `u₁ + u₂` construction with weighted
  ancestor towers.
- `BesovSpacesGoodGrid/GoodGrid/RegularDomains.lean`: regular families and
  regular domains (paper subsection `cf`) — the definitions and union
  construction, the strongly-regular ⇒ regular comparison, the indicator
  Besov/multiplier bounds `estG`, and the localized restriction
  representation estimate `pdd`/`hiip1`
  (`regularFamily_restriction_representations`).
- `BesovSpacesGoodGrid/GoodGrid/AlternativeDescriptionBs11.lean`: the
  regular-domain indicator-series description of `B^s_{1,1}` from paper
  Section 20 / Proposition `rema`, including `DomainAtomicRepresentation`,
  `DomainBesovSpace`, `domainBesovGauge`, and the final two-sided theorem
  `domainBesovSpace_equiv_souzaBesov11`.
- `BesovSpacesGoodGrid/GoodGrid/LeftCompositions.lean`: partial Section 21
  infrastructure for left compositions.  For a Lipschitz map
  `g : ℂ → ℂ` with constant `K`, the file proves the pointwise analytic
  estimates used by paper Proposition `expo`: `eLpNorm_comp_le_of_lipschitzWith`
  (`|g ∘ f|_p ≤ K |f|_p`, assuming `g 0 = 0`),
  `eLpNorm_comp_sub_const_le_of_lipschitzWith` (distance to constants on
  restricted measures), `osc_comp_le_of_lipschitzWith` (cell oscillation),
  `levelOscillationBlock_comp_le_of_lipschitzWith` and
  `levelOscillationBlock_root_comp_le_of_lipschitzWith` (level-block forms),
  `oscillationSeminorm_comp_le_of_lipschitzWith` (finite `q` and `q = ∞`),
  and `meanOscillationNorm_comp_le_of_lipschitzWith` (the full
  mean-oscillation gauge).  The remaining Section 21 task is to package these
  estimates as the full Souza-Besov left-composition theorem.
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

The repository currently builds with **zero `sorry`**.  Likely next steps are:

- the wrap-up equivalence theorem for paper Theorem 15.1 (packaging the
  proved inequality cycle) and the `L¹` functional of Corollary 15.2;
- the Section 16 examples: the Holder atom family with Proposition 16.2, and
  bounded-variation atoms with Proposition 16.3 (applications of
  `atoms_between_souza_atoms_and_besov_atoms`);
- finish paper Section 21 by upgrading the incorporated mean-oscillation
  estimates in `GoodGrid/LeftCompositions.lean` to the full Souza-Besov
  left-composition theorem; Section 20 and the quasialgebra result of
  Section 19 are done;
- continue polishing public docstrings around the large transmutation,
  completeness, and multiplier files;
- factor large proof-heavy files (notably `Multipliers/NonArchimedeanProperty.lean`
  and `WeakGrid/Transmutation.lean`) into smaller topic-focused modules if
  compilation time or navigation becomes cumbersome;
- clean deprecation/style warnings in the newer files.
