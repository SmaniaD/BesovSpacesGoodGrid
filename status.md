# Repository Status

Last updated: 2026-06-03.

Current branch: `main`.

The working tree is intentionally dirty from the current development pass.
Treat uncommitted changes as meaningful unless explicitly told otherwise.

## Verification

Recently checked successfully:

- `lake build BesovSpacesGoodGrid.GoodGrid.FiniteStandardNormimpliesBesov`
- `lake build BesovSpacesGoodGrid.GoodGrid.FiniteHaarNormimpliesLp`
- `lake build BesovSpacesGoodGrid.GoodGrid.OscillationNormleqBesovNorm`
- `lake env lean BesovSpacesGoodGrid.lean`

The oscillation module builds with one known `sorry`, described below.  The
other checked modules above have no new `sorry`.

## Current Main Line

The current formalization path is:

1. Haar representation norm controls the standard atomic representation norm.
2. Finite standard norm gives a genuine `L^p` standard representation and
   Souza-Besov membership.
3. The `L^p` part of the mean-oscillation norm is controlled by the standard
   norm.
4. It remains to prove the oscillation seminorm estimate, which will complete
   the mean-oscillation comparison.

## Recently Added Or Renamed Files

- `BesovSpacesGoodGrid/GoodGrid/FiniteStandardNormimpliesBesov.lean`

  This replaces the old `FiniteStandardNormimpliesLp.lean` name.  The new name
  reflects the stronger result now proved in the file: finite standard norm
  gives not only `L^p` membership, but also a canonical Souza-Besov
  representation with finite `(p,q)` cost.

- `BesovSpacesGoodGrid/GoodGrid/FiniteHaarNormimpliesLp.lean`

  Uses the standard-norm comparison to prove the finite Haar norm endpoint.

- `BesovSpacesGoodGrid/GoodGrid/OscillationNormleqBesovNorm.lean`

  Contains the current oscillation/standard-norm comparison work.  The filename
  is the grammatically corrected version of the requested
  `OscillationNormLeStandardRepresentationNorm` direction.

The root module `BesovSpacesGoodGrid.lean` imports these current filenames.
There should be no source imports of `FiniteStandardNormimpliesLp`.

## Proven Standard-Norm Results

In `FiniteStandardNormimpliesBesov.lean`:

- `canonicalStandardBlockSeq`

  The canonical standard block sequence associated to an integrable function.

- `abstractFinitePQCost_canonicalStandardBlockSeq_of_standardRepresentationNorm_ne_top`

  If `standardRepresentationNorm G F s hs p hp_top q f hf ≠ ∞`, then the
  bare canonical standard block sequence has finite abstract `(p,q)` cost.

- `finite_standardRepresentationNorm_has_Lp_standard_limit`

  Finite standard norm gives an `L^p` limit for the canonical standard block
  sequence.

- `finite_standardRepresentationNorm_implies_memLp_and_hasSum`

  If `f ∈ L^1` and `standardRepresentationNorm` is finite, then in fact
  `f ∈ L^p`, and the canonical standard block sequence has sum `f` in `L^p`.

- `finite_standardRepresentationNorm_implies_memBesov_and_standardRepresentation`

  Finite standard norm gives a Souza-Besov element representing `f`, together
  with the canonical standard `LpGridRepresentation`.  The theorem also proves:

  - the representation has finite `FinitePQCost`;
  - its extended cost `pqCostENNReal` is exactly `standardRepresentationNorm`;
  - its real cost `pqCost` is bounded by `standardRepresentationNorm.toReal`;
  - the abstract Besov cost `Norm_Costpq` is bounded by
    `standardRepresentationNorm.toReal`.

## Proven Haar Endpoint Results

In `FiniteHaarNormimpliesLp.lean`:

- finite `haarL2RepresentationNorm` implies finite `standardRepresentationNorm`;
- finite Haar norm implies `MemLp f p`;
- the Haar representation has sum `f` in `L^p`;
- the endpoint `p = 1` is handled through the existing `L^β` embedding route,
  so the theorem does not require `p > 1`.

## Proven Oscillation-Norm Results

In `OscillationNormleqBesovNorm.lean`:

- almost-minimizing Souza-Besov representations are available in both additive
  and multiplicative forms;
- finite standard norm gives a Souza-Besov representation of `f` in the form
  needed by the oscillation estimates;
- the `L^p` term

  ```text
  μ(I)^(-s) * ‖f‖_p
  ```

  is bounded by a finite constant times `standardRepresentationNorm`;
- the final mean-oscillation theorem is assembled from the `L^p` term and the
  oscillation seminorm estimate.

## Known Remaining Sorry

There is currently one planned `sorry`:

- `exists_oscillationSeminorm_le_const_mul_standardRepresentationNorm`
  in `BesovSpacesGoodGrid/GoodGrid/OscillationNormleqBesovNorm.lean`.

Mathematically, this is the discrete convolution estimate from the preprint:
for each cell `J ∈ P^k0`, choose a constant value from the low-frequency part
of the standard representation, bound the oscillation by the tail

```text
sum_{k > k0} sum_{R ∈ P^k, R ⊆ J} k_R a_R,
```

then sum over cells and levels to obtain convolution with the geometric kernel
`lambda2^(s * (k - k0))`.  The expected constant is of the form

```text
1 / (1 - G.grid.lambda2 ^ s)
```

up to the already-existing embedding/constants infrastructure.

The supporting Lean work still needed for this `sorry` is likely:

1. basic lemmas for `osc` and `levelOscillationBlock`, especially bounding
   `osc G p f J` by a chosen constant on `J`;
2. a clean statement identifying the low-frequency part of the standard
   representation as constant on a level-`k0` cell;
3. a tail estimate for the standard representation restricted to descendants
   of a fixed cell;
4. an `ℓ^q` convolution/geometric-kernel estimate in the current `ENNReal`
   norm format.

## Older Completed Main Comparison

The main Souza/Besov atom comparison is already formalized:

- `GoodGridSpace.atoms_between_souza_atoms_and_besov_atoms`

It states that if an atom family `A` is sandwiched between Souza atoms and
Besov atoms, then the Besov-ish spaces generated by Souza atoms, by `A`, and
by Besov atoms coincide, with the expected norm bounds and the geometric
constant

```text
C2 / (1 - G.grid.lambda2 ^ (β - s)).
```

The standard-vs-Haar comparison is also complete:

- `exists_standardRepresentationNorm_le_const_mul_haarL2RepresentationNorm`

in `GoodGrid/standardNormleqHaarRepresenstionNorm.lean` has no internal
`sorry`.

## Important Files

- `BesovSpacesGoodGrid.lean`

  Root module.  Imports the weak-grid layer, good-grid atom comparison,
  standard/Haar comparisons, finite-norm endpoint files, and the current
  oscillation comparison file.

- `BesovSpacesGoodGrid/GoodGrid/standardRepresentation.lean`

  Standard atomic representation bookkeeping, standard coefficients, and
  `standardRepresentationNorm`.

- `BesovSpacesGoodGrid/GoodGrid/standardNormleqHaarRepresenstionNorm.lean`

  Main comparison showing Haar representation norm controls the standard
  representation norm.

- `BesovSpacesGoodGrid/GoodGrid/FiniteStandardNormimpliesBesov.lean`

  Finite standard norm implies `L^p`, canonical standard `LpGridRepresentation`,
  finite cost, and Souza-Besov membership.

- `BesovSpacesGoodGrid/GoodGrid/FiniteHaarNormimpliesLp.lean`

  Finite Haar representation norm implies `L^p` membership and Haar expansion
  convergence to `f`.

- `BesovSpacesGoodGrid/GoodGrid/OscillationNormleqBesovNorm.lean`

  Current file for proving the oscillation norm is controlled by the standard
  representation norm.  Contains one planned `sorry`.

- `BesovSpacesGoodGrid/GoodGrid/MeanOscillationNorm.lean`

  Definitions of `osc`, `levelOscillationBlock`, `oscillationSeminorm`, and
  `meanOscillationNorm`.

## Next Steps

1. Prove `exists_oscillationSeminorm_le_const_mul_standardRepresentationNorm`.
2. After that, the assembled theorem
   `exists_meanOscillationNorm_le_const_mul_standardRepresentationNorm` should
   become sorry-free.
3. Consider factoring reusable oscillation lemmas into `MeanOscillationNorm.lean`
   if they are not specific to the standard representation.
4. Run a full `lake build` after closing the remaining oscillation `sorry`.

## Notes

- No destructive git operation has been used.
- Existing unrelated dirty files such as `README.md`, `standardRepresentation.lean`,
  and `standardNormleqHaarRepresenstionNorm.lean` were treated as intentional
  worktree state.
- The project still has many pre-existing warnings in older modules; these are
  separate from the current endpoint/oscillation work.
