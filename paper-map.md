# Paper Map

This file maps the published paper

Daniel Smania, *Besov-ish spaces through atomic decomposition*,
Analysis & PDE 15 (2022), no. 1

to the current Lean formalization in this repository (last revised 2026-06-12,
zero `sorry`, full `lake build` green).

The numbering X.Y below follows the order of the theorem-like environments in
`latex/besovish-2021-07-19.tex` within each section; for Sections 6, 7, 8, 15
and 16 it agrees with the published numbering. For Sections 17-21 the LaTeX
`\label`s (`boup`, `sepa`, `posrem`, `23er`, `pm1`, `mult`, `mult33`, `rema`,
`expo`) are the reliable reference.

Status labels:

- `proved`: there is a Lean theorem or definition covering the item.
- `partial`: the main infrastructure exists, but the published statement is not
  yet formalized as a matching theorem.
- `not started`: no substantial Lean formalization is currently present here.
- `external`: the topic comes from another library or repository.
- `documentation`: mathematical motivation or notation rather than a formal target.

## Published Table of Contents

| Paper section | Title | Current Lean status |
|---|---|---|
| 1 | Introduction | documentation |
| 2 | Notation | documentation |
| Part I | Divide and rule | mostly proved |
| 3 | Measure spaces and grids | proved (weak-grid form) |
| 4 | A bag of tricks | inlined in proofs, no standalone statements |
| 5 | Atoms | proved |
| 6 | Besov-ish spaces | proved |
| 7 | Scales of spaces | proved |
| 8 | Transmutation of atoms | proved |
| 9 | Good grids | proved |
| 10 | Induced spaces | proved for the needed form |
| 11 | Examples of classes of atoms | Souza atoms proved; Holder/BV not started |
| Part II | Spaces defined by Souza's atoms | mostly proved |
| 12 | Besov spaces in a measure space with a good grid | proved |
| 13 | Positive cone | proved (goes beyond the paper) |
| 14 | Unbalanced Haar wavelets | external (SmaniaD repos) + local Haar API |
| 15 | Alternative characterizations, I: Messing with norms | proved in pieces |
| 16 | Alternative characterizations, II: Messing with atoms | Prop 16.1 proved; 16.2-16.3 not started |
| 17 | Dirac's approximations | Prop 17.1 proved (evaluation/average forms A and B; distributional form not formalized) |
| Part III | Applications | Sections 18-19 proved; 20-21 not started |
| 18 | Pointwise multipliers acting on \(B^s_{p,q}\) | fully proved: Props 18.1, 18.3, 18.4, Remark posrem, Cor 18.6, Def/Prop 18.7-18.8, Prop 18.9, Prop 18.10 + Remark pos3 |
| 19 | \(B^s_{p,q} \cap L^\infty\) is a quasialgebra | Prop 19.1 (`mult33`) proved |
| 20 | A remarkable description of \(B^s_{1,1}\) | not started |
| 21 | Left compositions | not started |

## Part I — Divide and rule

| Paper item | Mathematical content | Lean item | File | Status |
|---|---|---|---|---|
| Section 3 | Measure spaces and grids | `WeakGrid`, `WeakGridSpace` | `BesovSpacesGoodGrid/WeakGrid/Definition.lean` | proved (weak-grid form) |
| Proposition 4.1 (`holder`) | Holder-like trick | none standalone; estimates inlined in Scales/Transmutation proofs | — | inlined |
| Proposition 4.2 (`young`) | Convolution trick | none standalone; block-sum infrastructure `blockTsum` etc. | `BesovSpacesGoodGrid/Sums.lean` | inlined |
| Section 5 (A1-A7) | Classes of \((s,p,u)\)-atoms | `LocalVectorSpace`, `AtomFamily`, `IsAtom` | `BesovSpacesGoodGrid/WeakGrid/Atoms.lean` | proved |
| Section 6 (definitions) | Besov-ish spaces, cost norm | `BesovishSpace`, `LpGridRepresentation`, `pqCost`, `Norm_Costpq` | `BesovSpacesGoodGrid/WeakGrid/BesovishSpaces.lean` | proved |
| Proposition 6.1 (`lp`) | Embedding \(\mathcal B^s_{p,q}(\mathcal A) \subset L^p\) | `lp_embedding_adapted_statement` | `BesovSpacesGoodGrid/WeakGrid/BesovishSpaces.lean` | proved (adapted form) |
| Proposition 6.3 | Linear space, \(\rho\)-norm | `levelBlocksLinear` + cost-norm API | `BesovSpacesGoodGrid/WeakGrid/BesovishSpaces.lean` | partial |
| Proposition 6.4 (`compa2`) | Limit of representations | `representation_limit`, `representation_limit_strong` | `BesovSpacesGoodGrid/WeakGrid/Completeness.lean` | proved |
| Corollary 6.5 (`compa1`) | Existence of strong/weak limits | `representation_limit_strong_existence`, `representation_limit_weak_existence` | `BesovSpacesGoodGrid/WeakGrid/Completeness.lean` | proved |
| Corollary 6.6 (`compa12`) | Sequential compactness of cost balls | `exists_strongly_convergent_subseq_of_uniform_pqCost`, `closed_Norm_Costpq_ball_strongly_seqCompact` | `BesovSpacesGoodGrid/WeakGrid/Completeness.lean` | proved |
| Corollary 6.7 | Completeness (closed / finite-dimensional atoms) | `besovishSpace_costNorm_completeSpace` | `BesovSpacesGoodGrid/WeakGrid/Completeness.lean` | proved |
| Proposition 7.1 (`compa`) | Scale inclusions for smoothness parameters | `smoothnessScaleBesovishSpace_subset`, `smoothnessScaleBesovishSpaceInclusion_Norm_Costpq_le` | `BesovSpacesGoodGrid/WeakGrid/Scales.lean` | proved |
| Proposition 8.1 (`trans`) | Transmutation of atoms (Claims A/B/C) | `Transmutation_of_Atoms_Claim_A`, `_Claim_B`, `_Claim_B_sharp`, `_Claim_C_explicit`, `_continuous_embedding_explicit` | `BesovSpacesGoodGrid/WeakGrid/Transmutation.lean` | proved |
| Section 9 | Good grids | `GoodGrid`, `GoodGridSpace` (extends `UnbalancedHaarWavelet.Grid`) | `BesovSpacesGoodGrid/GoodGrid/Definition.lean` | proved |
| Section 10 | Induced grids and induced decompositions | `inducedWeakGrid`, `inducedWeakGridSpace`, `inducedAtomFamily`, `inducedRepresentationToAmbient` | `BesovSpacesGoodGrid/WeakGrid/InducedGrid.lean` | proved for the needed form |
| Section 11A | Souza atoms | `IsSouzaAtom`, `canonicalSouzaAtom_isSouzaAtom`, Souza atom family | `BesovSpacesGoodGrid/GoodGrid/BesovSpace.lean` | proved |
| Sections 11B-11C | Holder atoms and bounded variation atoms | none | — | not started |

## Part II — Spaces defined by Souza's atoms

| Paper item | Mathematical content | Lean item | File | Status |
|---|---|---|---|---|
| Section 12 | Souza Besov spaces: completeness, compactness, density | `SouzaBesovSpace`, `souzaBesovSpace_costNorm_completeSpace`, `souza_closedCostBallInLp_isCompact`, `souza_closedCostBallInL1_isCompact`, `souzaBesovSpace_dense`, `souzaBesovSpace_dense_inL1` | `BesovSpacesGoodGrid/GoodGrid/BesovSpace.lean` | proved |
| Proposition 13.1 | Support of \(f \in \mathcal B^{s+}_{p,q}\) is a union of cells | `support_ae_countable_iUnion_goodGridCells_of_souzaPositiveFunction`, `souzaPositiveRepresentation_coeff_eq_zero_of_not_subset_cell` | `BesovSpacesGoodGrid/GoodGrid/PositiveCone.lean` | proved |
| Section 13 (beyond the paper) | Density of the positive cone, positive decompositions | `souzaPositiveCone_dense_in_LpNonnegativeCone`, `exists_souzaPositive_decomposition_of_aeRealValued` / `_aeComplexValued` | `BesovSpacesGoodGrid/GoodGrid/PositiveCone.lean` | proved |
| Section 14 | Unbalanced Haar wavelets (Girardi-Sweldens basis) | external deps `UnbalancedHaarWavelet`, `UnconditionalSchauderBasis`, `LaminarFamiliesMaximalBinaryTrees`, `Burkholder`; local API `L2normalizedHaar`, `Coeff` | external SmaniaD repos + `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/HaarRepresentationNorm.lean` | external / partial here |
| Theorem 15.1 (`alte`) | Equivalence of \(\|f\|_{\mathcal B}\), \(N_{st}\), \(N_{haar}\), \(N_{osc}\) | inequality cycle: `exists_standardRepresentationNorm_le_const_mul_souzaBesovNorm`, `exists_standardRepresentationNorm_le_const_mul_haarL2RepresentationNorm`, `exists_haarL2RepresentationNorm_le_const_mul_meanOscillationNorm`, `exists_meanOscillationNorm_le_const_mul_souzaBesovNorm`, `finite_standardRepresentationNorm_implies_memBesov_and_standardRepresentation`, `finite_haarL2RepresentationNorm_implies_memLp_and_hasSum`, `exists_haarRepresentationNorms_equivalent` | `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/` (StandarRepresentationNormleqBesovNorm, standardNormleqHaarRepresenstionNorm, HaarNormleqOscillationNorm, OscillationNormleqBesovNorm, FiniteStandardNormimpliesBesov, FiniteHaarNormimpliesLp, ComparingHaarRepresentationsl) | proved in pieces; no single wrap-up equivalence theorem |
| Corollary 15.2 (`fou`) | Linear functional reading a Haar coefficient | `Coeff`, `hasSum_coeff_smul_l2normalizedHaar_toLp` | `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/HaarRepresentationNorm.lean` | partial (coefficient yes, \(L^1\) functional no) |
| Proposition 16.1 (`besova`) | Souza atoms vs. Besov atoms (sandwich hypotheses) | `atoms_between_souza_atoms_and_besov_atoms` + decay claims `besovAtom_to_souza_representation_decay`, `besovAtom_to_induced_souzaS_representation_decay_claimC` | `BesovSpacesGoodGrid/GoodGrid/BesovAtoms.lean` | proved |
| Proposition 16.2 (`hold`) | Holder atoms case | none | — | not started |
| Proposition 16.3 | Bounded variation atoms case | none | — | not started |
| Proposition 17.1 (`boup`) | Dirac's approximations | `diracKernel`, `partialHaarSum_eq_integral_mul_diracKernel` (evaluation as cell average), `claimA_standard` and `claimA_positive` (item A, standard and positive-representation forms), `claimB` (item B), `standardLevelSum_eq_ancestor_term` (levelwise ancestor collapse); the distributional convergence form is not formalized (infrastructure: `TestFunctions`, `Distributions` in Distribution.lean) | `BesovSpacesGoodGrid/GoodGrid/DiracApproximations.lean` | proved (2026-06-11; axioms: `propext, Classical.choice, Quot.sound`) |

## Part III — Section 18: Pointwise multipliers

| Paper item | Mathematical content | Lean item | File | Status |
|---|---|---|---|---|
| Proposition 18.1 | \(M(\mathcal B^s_{1,1}) = \mathcal B^s_{1,1,selfs}\) | `souzaPointwiseMultiplier_iff_souzaPointwiseSelfsClass_one_one` (⟸ in Besovs11; ⟹ via `souzaPointwiseSelfsClass_of_souzaPointwiseMultiplier` in Besovspq) | `BesovSpacesGoodGrid/GoodGrid/Multipliers/Besovs11.lean`, `BesovSpacesGoodGrid/GoodGrid/Multipliers/Besovspq.lean` | proved |
| Lemma 18.2 (`incint3`) | Restriction to \(W \in \mathcal P\) is bounded | restriction machinery: `souzaCellIndicatorRestrictsToInduced`, `souzaIndicatorRestrictionBound_of_ambientRestrictionTransmutation_*`, `souzaCellIndicatorPointwiseMultiplier` | `BesovSpacesGoodGrid/GoodGrid/Multipliers/Besovspq.lean` | proved (grid-cell version) |
| Proposition 18.3 | \(\mathcal B^{s,t}_{p,q,selfs} \subset L^\infty\) continuously, uniformly in \(t\) | `souzaPointwiseSelfsTailBound_norm_ae_le`, `souzaPointwiseSelfsTailNorm_norm_ae_le`, `souzaPointwiseSelfsTailClass_norm_ae_bounded` | `BesovSpacesGoodGrid/GoodGrid/Multipliers/MultipliersareBounded.lean` | proved |
| Proposition 18.4 (`sepa`) | Non-Archimedean behaviour in \(\mathcal B^\beta_{p,\tilde q,selfs}\) | `souzaNonArchimedeanPropertyLambdaFinite` (finite \(\Lambda\)), `souzaNonArchimedeanProperty` (infinite \(\Lambda\)) | `BesovSpacesGoodGrid/GoodGrid/Multipliers/NonArchimedeanProperty.lean` | proved |
| Remark 18.5 (`posrem`) | Positive version of the non-Archimedean theorem | `souzaNonArchimedeanPropertyPositiveCone`, `souzaNonArchimedeanPropertyPositiveConeInfinite`, `exists_nonArchimedeanProductRepresentation_positive` | `BesovSpacesGoodGrid/GoodGrid/Multipliers/NonArchimedeanPropertyPositiveStandalone.lean` (cores in NonArchimedeanProperty.lean) | proved (2026-06-09; axioms checked: `propext, Classical.choice, Quot.sound`) |
| Corollary 18.6 (`23er`) | \(\mathcal B^{\beta,t}_{p,\tilde q,selfs} \subset M(\mathcal B^s_{p,q})\) continuously | `exists_souzaSelfsMultiplierConstant` (quantitative), `souzaPointwiseMultiplier_of_souzaPointwiseSelfsTailClass` (inclusion), `souzaPointwiseMultiplierNorm_le_const_mul_selfsTailNorm` (continuity), plus the level-lowering lemma `souzaPointwiseSelfsTailBound_levelZero` | `BesovSpacesGoodGrid/GoodGrid/Multipliers/SelfsSubsetMultipliers.lean` | proved (2026-06-10; axioms: `propext, Classical.choice, Quot.sound`) |
| Definition/Proposition 18.7-18.8 (`pos2`) | Strongly regular domains; positive tail `selfs` bound for \(\chi_\Omega\) | `StronglyRegularDomain` / `StronglyRegularDecomposition` (definition), `souzaPositiveSelfsTailBound_of_stronglyRegularDomain` (`pos2`), plus `souzaPositiveSelfsTailBound_smul_of_stronglyRegularDomain` and `souzaPositiveFunction_of_stronglyRegularDomain`; earlier grid-cell special case in Besovspq.lean | `BesovSpacesGoodGrid/GoodGrid/Multipliers/StronglyRegularDomains.lean` | proved (2026-06-10) |
| Proposition 18.9 (`pm1`) | Pointwise Multipliers I | `souzaPointwiseMultipliersI` (finite `Λ`) and `souzaPointwiseMultipliersIInfinite` (arbitrary `Λ ⊆ ℕ`; support conclusion in the a.e. form, positivity as cone-positivity, via the positive non-Archimedean theorems) | `BesovSpacesGoodGrid/GoodGrid/Multipliers/StronglyRegularDomains.lean` | proved (2026-06-10) |
| Proposition 18.10 (`mult`) | Pointwise Multipliers II (\(\mathcal B^{1/p}_{p,\infty} \cap L^\infty\)) | `souzaPointwiseMultipliersII`; input sublemma `exists_fouRepresentation` (Cor 15.2 `fou` + Prop 17.1 `boup`.B via the Dirac-approximation API), `u₁+u₂` construction `exists_mult_product_representation` (block core `exists_mult_product_blocks`, discrete Young inequality `geometric_conv_rpow_summable_and_tsum_le`, truncated-product identity passed to the limit) | `BesovSpacesGoodGrid/GoodGrid/Multipliers/Bp1overpinftyisMultiplier.lean` | proved (2026-06-12; axioms: `propext, Classical.choice, Quot.sound`) |
| Remark after 18.10 (`pos3`) | Positive version of Pointwise Multipliers II (positive gauges) | `souzaPointwiseMultipliersIIPositive`, representation form `exists_mult_product_representation_pos`; tower bound derived from positivity (`ancestorCoeffSum_norm_le_essBound_of_positive`) | `BesovSpacesGoodGrid/GoodGrid/Multipliers/Bp1overpinftyisMultiplier.lean` | proved (2026-06-12; axioms: `propext, Classical.choice, Quot.sound`) |

## Part III — Sections 19-21

| Paper item | Mathematical content | Lean item | Status |
|---|---|---|---|
| Proposition 19.1 (`mult33`) | Pointwise Multipliers III: \(\mathcal B^s_{p,q} \cap L^\infty\) is a quasialgebra | `souzaPointwiseMultipliersIII` (bilinear bound `|fg|_B + |fg|∞ ≤ Cqa (|f|_B + Mf)(|g|_B + Mg)`), core `exists_quasiAlgebra_product_representation` (two-sided `u₁+u₂` with weighted ancestor towers `weightedAncestorCoeffSum` and `exists_weighted_fouRepresentation`), `L∞` part `ae_norm_mul_le_mul_bounds`; in `BesovSpacesGoodGrid/GoodGrid/QuasiAlgebra.lean` | proved (2026-06-12; axioms: `propext, Classical.choice, Quot.sound`) |
| Definition/Proposition 19.x | Regular families of domains | none | not started |
| Proposition 20.1 (`rema`) | \(B^{1-s} = \mathcal B^s_{1,1}\) (description via sums of indicators) | none (related: Besovs11.lean, but it treats multipliers, not this characterization) | not started |
| Proposition 21.1 (`expo`) | Left compositions | none | not started |

## Next Formalization Targets

Natural candidates, in rough order of leverage:

1. A single wrap-up equivalence theorem for Theorem 15.1, packaging the
   already-proved inequality cycle, plus the \(L^1\) functional of
   Corollary 15.2.
2. Section 16 examples: formalize the Holder atom family (Section 11B) and
   prove Proposition 16.2 by applying
   `atoms_between_souza_atoms_and_besov_atoms`; same for bounded variation
   atoms and Proposition 16.3.
3. The remaining items of Section 19 (regular families of domains) and
   Sections 20-21 (`B^{1-s} = B^s_{1,1}`, left compositions).
4. The distributional form of Proposition 17.1, on top of the proved
   claims A/B and the `TestFunctions`/`Distributions` infrastructure.
