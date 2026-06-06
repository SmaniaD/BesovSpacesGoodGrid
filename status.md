# Repository Status

Last updated: 2026-06-05.

Current branch: `main`.

The working tree is intentionally dirty from the current development pass.
Treat uncommitted changes as meaningful unless explicitly told otherwise.

## Proof Sanity

For project Lean files, excluding `.lake/packages`, the current text/code
search finds no proof holes or project-local unsafe declarations:

- no Lean `sorry`;
- no Lean `admit`;
- no project-local `axiom` declarations;
- no project-local `constant` declarations;
- no `unsafe` or `opaque` declarations.

There are still textual mentions of words such as `sorry` in documentation and
scripts, and dependency/test files under `.lake/packages` contain their own
examples.  Those are not proof holes in this project.

## Verification

Recently checked successfully:

- `lake build BesovSpacesGoodGrid.GoodGrid.Multipliers`
- `lake env lean BesovSpacesGoodGrid/GoodGrid/Multipliers/MultipliersareBounded.lean`
- `lake build BesovSpacesGoodGrid.GoodGrid.Multipliers.Definition`
- `lake build BesovSpacesGoodGrid.GoodGrid.Multipliers.Besovspq`
- `lake build BesovSpacesGoodGrid.GoodGrid.Multipliers.Besovs11`
- `lake env lean BesovSpacesGoodGrid/GoodGrid/Multipliers.lean`
- `lake env lean BesovSpacesGoodGrid/WeakGrid/BesovishSpaces.lean`
- `lake build`
- `lake build BesovSpacesGoodGrid.GoodGrid.BesovAtoms`
- `lake env lean BesovSpacesGoodGrid/GoodGrid/BesovAtoms.lean`
- `lake env lean BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/OscillationNormleqBesovNorm.lean`
- `lake env lean BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/HaarNormleqOscillationNorm.lean`
- `lake env lean BesovSpacesGoodGrid.lean`

The last file currently reports only deprecation warnings for
`mul_le_mul_left'`/`mul_le_mul_right'`.  `BesovAtoms.lean` reports one
style-only `unnecessarySimpa` warning.

The previous aggregate-root collision around
`GoodGridSpace.GoodGridCell.toLevelCell` has been resolved by rebuilding the
stale `BesovAtoms` artifact after the definition was centralized in
`GoodGrid/BesovSpace.lean`.  The root module now imports cleanly.

## Current Pass: Multipliers, Restriction, And Selfs Boundedness

The current active development pass is the restriction lemma for good-grid cells
and Souza atoms, plus the next target: proving that Souza `selfs` multipliers
belong continuously to `L∞`.

Modified files in this pass:

- `BesovSpacesGoodGrid/GoodGrid/BesovAtoms.lean`
- `BesovSpacesGoodGrid/WeakGrid/Transmutation.lean`
- `BesovSpacesGoodGrid/WeakGrid/BesovishSpaces.lean`
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/Definition.lean`
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/Besovspq.lean`
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/Besovs11.lean`
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/MultipliersareBounded.lean`
- `BesovSpacesGoodGrid/GoodGrid/Multipliers.lean`

### What Was Done

In `WeakGrid/Transmutation.lean`:

- Added reusable window/partial-sum coefficient lemmas around
  `PartialSumLevels`, including the identity of a window with a difference of
  initial segments.
- Added general finite-window coefficient-cost lemmas, including
  `CoeffFinitePQCost_window` and `CoeffPQCost_window_eq_Ico`.
- Added bridge lemmas applying the abstract transmutation theorem to initial
  segments and windows.

In `WeakGrid/BesovishSpaces.lean`:

- Added `LevelBlock.singleAtom`, a level block supported on one prescribed cell.
- Proved that the corresponding one-block representation agrees a.e. with the
  scalar atom:
  `LevelBlock.singleAtom_ae_eq`.
- Proved the coefficient power is concentrated at the active level:
  `LevelBlock.singleAtom_levelCoeffPower` and
  `LevelBlock.singleAtom_singleBlock_levelCoeffPower`.
- Added the public zero representation:
  `LpGridRepresentation.zero`, with zero level coefficient power.

In `GoodGrid/Multipliers/Definition.lean`:

- Added the Souza pointwise multiplier bound, pointwise multiplier class,
  multiplier set, `selfs` class, and `selfs` seminorm definitions.

In `GoodGrid/Multipliers/Besovspq.lean`:

- Added the induced restriction level map
  `GoodGridCell.restrictionLevel W i = i - W.level`.
- Proved this level map is almost linear:
  `GoodGridCell.restrictionLevel_almostLinear`.
- Added a real-power monotonicity helper for non-positive exponent:
  if `0 < x <= y` and `e <= 0`, then `y^e <= x^e`.
- Proved the two local Souza atom transport lemmas:
  - `souzaAtom_mem_inducedCell_of_subset` for `Q ⊆ W`;
  - `souzaAtom_mem_inducedRoot_of_subset` for `W ⊆ Q`, assuming
    `s <= (p.toReal)⁻¹`.
- Proved the key local representation lemma
  `restrict_souzaAtomFamily_toFunction_oneBlockRepresentation`:
  each restricted Souza atom `1_W a_Q` has an induced representation
  concentrated in at most one level, with level coefficient power bounded by
  `1`, together with the support/cutoff vanishing conditions needed by
  transmutation.
- Packaged the local one-atom representations into global transmutation data:
  `restrict_souzaRepresentation_transmutationAtomData`.
- Proved the finite-sum identity saying these local representatives represent
  pointwise multiplication by `1_W` on each ambient initial segment:
  `restrict_souzaRepresentation_partialSum_representsPointwiseProduct`.
- Combined both ingredients into the exact `hdata` input required by the
  abstract transmutation bridge:
  `restrict_souzaRepresentation_transmutationData`.
- Proved the public all-`q` cell-indicator multiplier theorem
  `souzaIndicatorPointwiseMultiplier_of_restrictionTransmutation`, with private
  finite-`q` and `q = ∞` branches.
- Proved the general implication from pointwise multiplier to Souza `selfs`
  class and the induced-cell restriction criteria.

In `GoodGrid/Multipliers/Besovs11.lean`:

- Proved the special endpoint `p = q = 1` equivalence between Souza pointwise
  multipliers and the Souza atom `selfs` tests.

In `GoodGrid/BesovAtoms.lean`:

- Promoted `induced_cCoefficient_le_geometric` from private to public, with a
  docstring.  This is the quantitative estimate saying that the coefficient
  constant on the grid induced by a cell is controlled by the ambient
  geometric model with the expected factor `μ(Q)^β`.

In `GoodGrid/Multipliers/MultipliersareBounded.lean`:

- Created the new topic file for the proof that Souza `selfs` multipliers are
  essentially bounded.
- Added the ambient and induced Souza Besov-to-`L^p` embedding constants:
  `souzaBesovLpEmbeddingConstant`,
  `inducedSouzaBesovLpEmbeddingConstant`, and
  `souzaBesovLpLocalEmbeddingConstant`.
- Proved the scale estimate
  `inducedSouzaBesovLpEmbeddingConstant_le_cellScale`, giving the crucial
  cell factor `μ(Q)^s`.
- Proved that the canonical Souza atom is an admissible normalized `selfs`
  test:
  `exists_canonicalSouzaAtomicUnit`.
- Proved that a `selfs` bound controls the `L^p` norm of the product with any
  normalized atom:
  `souzaPointwiseSelfsBound_atomicUnit_product_eLpNorm_le`.
- Specialized this to the canonical Souza atom on a cell:
  `souzaPointwiseSelfsBound_canonicalAtom_product_eLpNorm_le`.
- Proved the induced-grid `L^p` estimate:
  `inducedSouzaBesov_eLpNorm_le`.
- Proved the main intermediate local estimate
  `souzaPointwiseSelfsBound_restrictedCanonicalAtom_eLpNorm_le_of_restrictsToInduced`:
  assuming a quantitative restriction operator bound into the grid induced by
  `Q`, the restricted product `1_Q * (m * a_Q)` has local `L^p` norm bounded
  with the correct factor `μ(Q)^s`.

`GoodGrid/Multipliers.lean` is now the compatibility aggregator for the split
multiplier modules.

The alternative representation and comparison-norm files now live under
`GoodGrid/AlternativeRepresentationsAndNorms/`, grouping the Haar, standard,
and mean-oscillation representation/norm theory away from the core good-grid
files.  The module `GoodGrid/AlternativeRepresentationsAndNorms.lean` is the
public aggregator for this group.

### Mathematical Status

The local geometry of restricting one Souza atom is now formalized:

- If `Q ∩ W = ∅`, then the restriction is represented by the zero
  representation.
- If `Q ⊆ W`, then the atom is transported to the corresponding induced cell at
  level `Q.level - W.level`.
- If `W ⊆ Q`, then the restriction is represented on the induced root cell.
  This case needs the natural hypothesis
  `s <= 1 / p.toReal`, because Souza atoms scale like
  `μ(Q)^(s - 1/p)`, and the exponent must be non-positive to pass from `Q` to
  the smaller cell `W` with uniform coefficient.

The abstract functional-analytic/transmutation bridge is already present and
has now been connected to the concrete Souza restriction construction for every
`q >= 1`, including `q = ∞`.

The concrete bridge now uses `k i = i - W.level`, `A = -W.level`, `B = 0`,
`r = 1`, and `C = 1`.  The corresponding simplified constant is named
`souzaRestrictionMultiplierConstant` and is
`G.Cmult1 * cCoefficientInt p ∞ (transmutationKernelZ lam (-W.level) 1)`.

For the `selfs ⊂ L∞` goal, the current formalized chain is:

- test the `selfs` bound on the canonical Souza atom `a_Q`;
- restrict the resulting product to the grid induced by `Q`;
- use the induced `L^p` embedding;
- use the geometric coefficient estimate to recover the necessary `μ(Q)^s`
  factor.

This is the right scale for the paper proof.  The remaining mathematical
conversion is to divide by the canonical atom amplitude and turn the uniform
cell-average bound into an essential-supremum bound, via the grid generators
and the martingale/differentiation argument.

### What Remains

1. If a quantitative final statement is desired, add a `PointwiseMultiplierBound`
   version of the transmutation bridge so the named constant can be exposed as
   the bound rather than only used internally to prove multiplier membership.
2. Expose a quantitative restriction-to-induced-grid lemma in the exact form
   needed by `souzaPointwiseSelfsBound_restrictedCanonicalAtom_eLpNorm_le_of_restrictsToInduced`.
3. Finish the final public theorem that
   `SouzaPointwiseSelfsClass G s p q hs hp hp_top m` implies `m ∈ L∞`
   continuously, by deriving uniform cell-average bounds and applying the
   grid-generator/differentiation step.

## Current Main Line

The good-grid comparison layer now contains the following formal chain.

1. Haar representation norm controls the standard atomic representation norm:
   `exists_standardRepresentationNorm_le_const_mul_haarL2RepresentationNorm`.
2. Finite standard representation norm gives `MemLp`, the canonical standard
   `LpGridRepresentation`, finite `(p,q)` cost, and Souza-Besov membership:
   `finite_standardRepresentationNorm_implies_memBesov_and_standardRepresentation`.
3. Finite Haar norm gives `MemLp` and identifies the Haar expansion with the
   original function:
   `finite_haarL2RepresentationNorm_implies_memLp_and_hasSum`.
4. Standard representation norm controls the mean-oscillation norm:
   `exists_meanOscillationNorm_le_const_mul_standardRepresentationNorm`.
5. Mean-oscillation norm controls the Haar representation norm:
   `exists_haarL2RepresentationNorm_le_const_mul_meanOscillationNorm`.

Thus the standard, Haar, and mean-oscillation gauges are now connected by
finite-constant comparison theorems under the hypotheses encoded in the
corresponding Lean statements.

## Recently Added Or Renamed Files

- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/FiniteStandardNormimpliesBesov.lean`

  Replaces the old `FiniteStandardNormimpliesLp.lean` name.  Finite standard
  norm now gives not only `L^p` membership, but also a canonical Souza-Besov
  representation with finite `(p,q)` cost.

- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/FiniteHaarNormimpliesLp.lean`

  Uses the standard-norm comparison to prove the finite Haar norm endpoint.

- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/OscillationNormleqBesovNorm.lean`

  Proves the direction
  `meanOscillationNorm ≤ C * standardRepresentationNorm`, including the
  oscillation-seminorm tail estimate.

- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/HaarNormleqOscillationNorm.lean`

  Proves the reverse analytic direction
  `haarL2RepresentationNorm ≤ C * meanOscillationNorm`, using the zero-mean
  Haar wavelet estimate against local oscillation constants.

## Proven Standard-Norm Results

In `FiniteStandardNormimpliesBesov.lean`:

- `canonicalStandardBlockSeq`;
- `abstractFinitePQCost_canonicalStandardBlockSeq_of_standardRepresentationNorm_ne_top`;
- `finite_standardRepresentationNorm_has_Lp_standard_limit`;
- `finite_standardRepresentationNorm_implies_memLp_and_hasSum`;
- `finite_standardRepresentationNorm_implies_memBesov_and_standardRepresentation`.

The endpoint theorem packages `MemLp`, convergence of the canonical standard
block sequence to `f`, finite coefficient cost, equality of the extended
canonical cost with `standardRepresentationNorm`, and the corresponding
Souza-Besov membership/cost bound.

## Proven Haar Results

In `FiniteHaarNormimpliesLp.lean`:

- finite `haarL2RepresentationNorm` implies finite `standardRepresentationNorm`;
- finite Haar norm implies `MemLp f p`;
- the normalized Haar expansion has sum `f` in `L^p`;
- the endpoint `p = 1` is handled through the existing `L^β` embedding route.

In `HaarNormleqOscillationNorm.lean`:

- father coefficient term is controlled by the `L^p` part of the
  mean-oscillation norm;
- each cellwise Haar coefficient block is controlled by the cell oscillation;
- levelwise Haar blocks are controlled by levelwise oscillation blocks;
- the full Haar representation norm is bounded by a finite constant times
  `meanOscillationNorm`.

## Proven Oscillation-Norm Results

In `OscillationNormleqBesovNorm.lean`:

- almost-minimizing Souza-Besov representations are available in additive and
  multiplicative forms;
- finite standard norm gives the Souza-Besov representation needed by the
  oscillation estimates;
- the `L^p` term

  ```text
  μ(I)^(-s) * ‖f‖_p
  ```

  is bounded by a finite constant times `standardRepresentationNorm`;
- the oscillation seminorm is bounded by a finite constant times
  `standardRepresentationNorm`;
- the assembled theorem
  `exists_meanOscillationNorm_le_const_mul_standardRepresentationNorm` is
  proved without `sorry`.

The core mathematical step is the discrete tail estimate from the manuscript:
low-frequency standard/Souza blocks are constant on finer cells, and the
oscillation is bounded by the high-frequency tail.  The resulting levelwise
bound is summed using the geometric kernel coming from the good-grid measure
ratio.

## Older Completed Main Comparison

The main Souza/Besov atom comparison is formalized as

- `GoodGridSpace.atoms_between_souza_atoms_and_besov_atoms`.

It states that if an atom family `A` is sandwiched between Souza atoms and
Besov atoms, then the Besov-ish spaces generated by Souza atoms, by `A`, and
by Besov atoms coincide, with the expected norm bounds and the geometric
constant

```text
C2 / (1 - G.grid.lambda2 ^ (β - s)).
```

## Important Files

- `BesovSpacesGoodGrid.lean`

  Aggregate root module.  The source imports the weak-grid layer, good-grid
  atom comparison, standard/Haar comparisons, finite-norm endpoint files, and
  oscillation/Haar comparison files.  Its current Lean check succeeds.

- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/standardRepresentation.lean`

  Standard atomic representation bookkeeping, standard coefficients, and
  `standardRepresentationNorm`.

- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/standardNormleqHaarRepresenstionNorm.lean`

  Main comparison showing Haar representation norm controls the standard
  representation norm.

- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/FiniteStandardNormimpliesBesov.lean`

  Finite standard norm implies `L^p`, canonical standard
  `LpGridRepresentation`, finite cost, and Souza-Besov membership.

- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/FiniteHaarNormimpliesLp.lean`

  Finite Haar representation norm implies `L^p` membership and Haar expansion
  convergence to `f`.

- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/MeanOscillationNorm.lean`

  Definitions of `osc`, `levelOscillationBlock`, `oscillationSeminorm`, and
  `meanOscillationNorm`.

- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/OscillationNormleqBesovNorm.lean`

  Proves control of mean oscillation by the standard representation norm.

- `BesovSpacesGoodGrid/GoodGrid/AlternativeRepresentationsAndNorms/HaarNormleqOscillationNorm.lean`

  Proves control of the Haar representation norm by mean oscillation.

## Next Steps

1. Finish the global `h`/`Rt` construction for the GoodGrid/Souza restriction
   lemma.
2. Close the `RepresentationWsubGandALS` proof using the one-block local
   representation theorem.
3. Prove the restricted-initial-segment identity and call the existing
   transmutation bridge.
4. Clean deprecation/style warnings in the new comparison and transmutation
   files.
5. Consider factoring large proof-heavy comparison files into smaller
   topic-focused modules if compilation or navigation becomes cumbersome.

## Notes

- No destructive git operation has been used.
- Existing dirty files were treated as intentional worktree state.
- The project still has pre-existing warnings in older modules; these are
  separate from the closed proof holes.
