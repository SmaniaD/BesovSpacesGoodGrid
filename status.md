# Current status

Last updated: 2026-06-17.

This repository currently builds successfully through the aggregate root
`BesovSpacesGoodGrid.lean`.

## Verification

- `lake env lean BesovSpacesGoodGrid/GoodGrid/AlternativeDescriptionBs11.lean`
  succeeds with no warnings from that file.
- `lake env lean BesovSpacesGoodGrid/GoodGrid/LeftCompositions.lean`
  succeeds with no warnings from that file.
- `lake build` succeeds:
  `Build completed successfully (3462 jobs).`
- A project-source search found no active Lean `sorry` or `admit` proofs and
  no project-local `axiom` or `constant` declarations.  The remaining hits for
  those words are prose/docstring uses such as "sorry-free", "admit a finite
  bound", and mathematical uses of "constant".

The full build still reports existing style/deprecation warnings in older
project files and dependencies, notably unused simp arguments, unnecessary
`simpa`, deprecated `push_neg`, duplicated namespace lints for the grid-space
structures, and deprecated `mul_le_mul_*'` names.  These are warnings, not
failed proofs.

## Main Completed Areas

- Weak-grid foundations: weak grids, cells, atom families, level blocks,
  `LpGridRepresentation`, coefficient costs, Besov-ish spaces, scale
  inclusions, transmutation, compactness, and completeness.
- Good-grid Souza theory: good grids, Souza atoms, Souza Besov spaces,
  compactness/density, positive cone, and the Souza/Besov atom comparison.
- Alternative representation and norm infrastructure: Haar, standard, and
  mean-oscillation gauges, with the main inequality cycle for Theorem 15.1
  proved in pieces.
- Dirac approximations: the grid Dirac kernels, cell-average identity for
  partial Haar/standard sums, and the proved forms of Proposition 17.1.A/B.
- Pointwise multipliers: Section 18 through Pointwise Multipliers I/II, the
  `selfs` multiplier inclusion, non-Archimedean estimates, positive-cone
  variants, and the quasialgebra theorem of Section 19.
- Regular domains: regular families/domains, strongly regular implies regular,
  the indicator estimate `estG`, bounded multiplier wrappers, and localized
  restriction representations `pdd`/`hiip1`.
- Section 20 / Proposition `rema`: the alternative description of
  `B^s_{1,1}` by regular-domain indicator series is formalized in
  `BesovSpacesGoodGrid/GoodGrid/AlternativeDescriptionBs11.lean`.
- Section 21 / Proposition `expo` is formalized in
  `BesovSpacesGoodGrid/GoodGrid/LeftCompositions.lean`: Lipschitz maps fixing
  zero control the `L^p` term, local oscillations, the oscillation seminorm,
  and the full mean-oscillation gauge; the file also packages this as
  Souza-Besov membership and a quantitative Souza-Besov gauge bound.

## Section 20 Status

`AlternativeDescriptionBs11.lean` introduces the endpoint exponent
`domainEndpointExponent s`, normalized domain indicators
`normalizedDomainIndicator`, domain atomic representations
`DomainAtomicRepresentation`, the predicate `DomainBesovSpace`, and the gauge
`domainBesovGauge`.

The file proves both inclusions needed for the norm equivalence:

- `domainBesovSpace_to_souzaBesov11`: a regular-domain indicator
  representation gives a Souza `B^s_{1,1}` element, with the bound controlled
  by `regularDomainIndicatorCost / (1 - c)` through the indicator estimate
  from `RegularDomains.lean`.
- `souzaBesov11_to_domainBesovSpace`: a Souza representation is flattened into
  a natural-number series of normalized grid-cell indicators, with
  domain-gauge cost bounded by the Souza coefficient-cost gauge.

The final packaged theorem is:

- `domainBesovSpace_equiv_souzaBesov11`

It states the two-sided equivalence between the regular-domain indicator
description and Souza `B^s_{1,1}` in the repository's representative-function
form, together with the corresponding norm/gauge estimates.

Key supporting infrastructure now includes:

- `domainAtomicRepresentation_to_souzaBesov11`, which turns a full domain
  atomic representation into a Souza element via Cauchy finite truncations and
  the finite-measure embedding into `L^1`;
- `exists_Lt_representative_hasSum_of_lp_embedding` in
  `WeakGrid/BesovishSpaces.lean`, exposing the `L^t` block `HasSum` produced by
  an `L^p -> L^t` embedding;
- private flattening helpers around `decode₂WithZero` and
  `souzaDomainFlattenedCoeff`, which reindex Souza cell coefficients into a
  natural-number series and keep the `l^1` cost bounded by the original Souza
  representation cost.

## Remaining Mathematical Targets

Natural next formalization targets are:

- package Theorem 15.1 as one public equivalence theorem, using the existing
  inequality cycle, and add the missing `L^1` functional form of Corollary
  15.2;
- formalize the Holder and bounded-variation atom examples from Section 16 and
  apply the existing Souza/Besov atom comparison theorem;
- formalize the distributional version of Proposition 17.1 on top of the
  existing `TestFunctions`/`Distributions` infrastructure;
- clean existing style/deprecation warnings when they become relevant to files
  already being edited.
