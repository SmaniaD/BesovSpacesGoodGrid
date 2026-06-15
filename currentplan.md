# Current Plan: Regular-domain non-Archimedean multiplier estimates

## Summary

Prove the four proposed theorems in
`BesovSpacesGoodGrid/GoodGrid/RegularDomainsNonArchimedean.lean`.
The proof should follow the paper's levelwise estimates for the `u₁ + u₂`
product construction, not an atom-by-atom triangle estimate.

The target output estimate is the bounded Besov gauge

```lean
pqCost S + ‖h‖∞ ≤ Cna * N * (pqCost R + M)
```

together with the a.e. bound `‖h z‖ ≤ Cna * N * M`.

## Mathematical Setup

The input is a bounded Souza-Besov function:

- `f : α → ℂ`;
- `x : BesovishSpace (souzaAtomFamily G s p hs hp hp_top) q`;
- `R : LpGridRepresentation ... (x : Lp ℂ p μ)`;
- `R` represents `f`, has finite `(p,q)` cost, and is canonical;
- `‖f z‖ ≤ M` almost everywhere.

For the non-positive statements, add explicit tower hypotheses on the chosen
canonical representation `R`:

```lean
∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
  ‖weightedAncestorCoeffSum G R Q‖ ≤ M

∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
  ‖strictWeightedAncestorCoeffSum G R Q‖ ≤ M
```

These hypotheses are needed because a bounded function can have a canonical
complex representation with large cancelling ancestral partial sums.

## Core Proof Strategy

Use the `u₁ + u₂` product construction level by level.

For the uniform `RegularFamily` version, represent each `1_{Ωᵢ}` by the
canonical regular-family indicator blocks already built in `RegularDomains`.
For each active index `i`, form the product blocks

```lean
quasiU1Block G s p hs hp hp_top (Rind i) R
quasiU2Block G s p hs hp hp_top (Rind i) R
```

where `Rind i` is the regular-family indicator representation and `R` is the
given representation of `f`.

Do not estimate every product `1_{Ωᵢ} a_Q` separately.  Instead, fix a level
`k` and estimate the `ℓ^p` sum of all output coefficients at that level.

### `u₁` estimate

The coefficients have the form

```text
indicator coefficient/tower contribution times source coefficient c_Q
```

After summing over indices with weights `Θᵢ`, the local overlap hypothesis
should give a bound by `N` on the multiplier tower seen by every active source
cell.  Hence the level root is bounded by

```text
N * (source level coefficient power)^(1/p)
```

and the `(p,q)` cost contributes `≤ C * N * pqCost R`.

### `u₂` estimate

The coefficients contain the strict ancestor tower of the source
representation `R`.  Use the explicit tower hypothesis

```lean
‖strictWeightedAncestorCoeffSum G R Q‖ ≤ M
```

to bound the source tower.  The remaining coefficient sum is the weighted
regular-family indicator cost at level `k`.  After taking the `(p,q)` gauge,
this contributes `≤ C * N * M`.

### Combining levels

Use the existing `(a + b)^p` block estimate style from `RegularDomains`
to combine `u₁` and `u₂`:

```text
pqCost S ≤ C * N * pqCost R + C * N * M
```

Then enlarge constants to state

```text
pqCost S + ‖h‖∞ ≤ Cna * N * (pqCost R + M)
```

In Lean, `‖h‖∞` is represented by a witness
`hmemInf : MemLp h (∞ : ℝ≥0∞) μ` and the term
`‖MemLp.toLp h hmemInf‖`.

## Infinite Families

First prove finite versions for `Finset ℕ`.  Then use the standard initial
finite subsets

```lean
nonArchimedeanLambdaInitial Λ n
```

and pass to the limit with the compactness helpers already used in
`NonArchimedeanProperty.lean`.  If those helpers are private, either publicize
the generic versions or reproduce small local variants.

Pointwise convergence and the a.e. `L∞` estimate come from the absolute
overlap bound:

```text
∑ᵢ |Θᵢ 1_{Ωᵢ}(z)| ≤ C * N
```

on points relevant to the active cells of `R`, hence

```text
|h z| ≤ C * N * |f z| ≤ C * N * M.
```

## Positive Variants

Assume `Θᵢ ≥ 0` and `SouzaPositiveRepresentation R`.  Use positivity of the
regular indicator blocks and positive closure of the `u₁ + u₂` construction to
obtain `SouzaConePositiveRepresentation S`.  The support conclusion is the same
as in the non-positive case.

## Order of Work

1. Add the source tower hypotheses to the four proposed statements.
2. Prove local overlap extraction lemmas:
   - a single non-uniform summand is bounded by
     `regularDomainOverlapCostInfinite`;
   - a single uniform summand is bounded by
     `regularFamilyOverlapCostInfinite`.
3. Prove weighted level estimates for the uniform family:
   - `u₁` level coefficient power;
   - `u₂` level coefficient power;
   - combined product block estimate.
4. Prove the finite uniform theorem.
5. Pass to infinite uniform theorem by the existing compactness/limit pattern.
6. Add the positive uniform theorem.
7. Prove non-uniform versions by applying the same argument to singleton
   regular families and using the hypothesis with
   `1 + regularDomainIndicatorCost`.
8. Update `status.md` after each completed theorem and report remaining
   `sorry`s.

## Implementation Status

Completed:

- the four proposal statements have the bounded Besov gauge and explicit tower
  hypotheses for the chosen canonical representation;
- the bounded gauge is stated with a genuine `L∞` witness for the output:
  `pqCost S + ‖MemLp.toLp h hmemInf‖ ≤ Cna * N * (pqCost R + M)`;
- `regularDomainOverlapCostInfinite_term_le` extracts a single non-uniform
  summand from the overlap series;
- `regularFamilyOverlapCostInfinite_term_le` extracts a single uniform
  summand from the overlap series.
- `linftyMemLp_and_norm_le_of_representsFunction_bound` converts the a.e.
  output bound plus a concrete representation of `h` into the formal `L∞`
  witness and norm estimate needed by the bounded gauge.
- `exists_finset_weighted_sum_representation` builds a finite weighted sum of
  already-represented functions, preserving finite `(p,q)` cost with the crude
  triangle bound `sum |Theta_i| * pqCost(R_i)`.
- `levelBlock_smul_coeff_ne_zero` and
  `lpGridRepresentation_smul_coeff_ne_zero` record that scaling cannot create
  new nonzero coefficients; these are the support-transfer pieces needed for
  weighted finite sums.
- `exists_finset_weighted_sum_representation_support` builds the same crude
  finite weighted sum while also proving that every nonzero output coefficient
  comes from a nonzero coefficient of one active input representation.
- `exists_finset_weighted_sum_positive_representation_support` does the
  corresponding finite positive assembly for nonnegative weights, using the
  positive finite-sum construction and preserving support.
- `regularFamily_productBlock_coeff_ne_zero_subset_domain_local` exposes, in
  this file, the product-block support fact needed later: a nonzero coefficient
  of the `u₁ + u₂` block for `Ω_i` lives on a cell contained in `Ω_i`.
- `regularDomain_weightedIndicatorCost_le_of_overlap_subset` and
  `regularFamily_weight_abs_le_of_overlap_subset` convert overlap hypotheses
  from `ℝ≥0∞` back into real inequalities for active cells.
- `regularFamily_unique_index_of_levelCell_subset` records uniqueness of the
  active domain containing a whole level cell.
- `lpGridRepresentation_smul_levelCoeffPower`,
  `lpGridRepresentation_add_levelCoeffPower_eq_of_disjoint_support`, and
  `exists_finset_weighted_sum_representation_disjoint_levelCoeffPower` provide
  the exact finite weighted level-power algebra under disjoint support.
- `exists_finset_weighted_sum_regularFamily_levelCoeffPower` packages that
  exact algebra for representations localized in a regular family, and
  `finset_weighted_levelCoeffPower_le_of_weight_bound` gives the finite
  numerical `N ^ p` level bound from uniform weight bounds.
- `pqCost_le_mul_of_levelCoeffPower_le` and
  `pqCost_le_mul_regularFamilyRestrictionCost_of_levelCoeffPower_le` convert
  levelwise `N ^ p` bounds into `pqCost` bounds.
- `regularFamily_weight_abs_le_of_productBlock_overlap` applies the overlap
  hypothesis directly to a nonzero coefficient of a regular-family product
  block.
- `finset_weighted_levelCoeffPower_le_of_weight_bound_on_support` proves the
  finite level estimate when the weight bound is only known on indices whose
  level contribution is nonzero.
- `exists_finset_weighted_sum_regularFamily_pqCost_le_of_level_weight_bound`
  upgrades that support-local level estimate to a finite regular-family
  `pqCost` estimate.
- `regularFamily_productBlock_coeff_ne_zero_exists_source_meeting_domain`,
  `regularFamily_weight_abs_le_of_productBlock_source_overlap`, and
  `regularFamily_weight_abs_le_of_productLevel_source_overlap` connect a
  nonzero product coefficient/level to a nonzero source coefficient of the
  input representation and then apply the source-cell overlap hypothesis.
- `exists_finset_weighted_sum_regularFamily_product_pqCost_le_of_source_overlap`
  proves the finite uniform core: for supplied `u₁+u₂` product
  representations over a finite subfamily, the weighted sum has
  `pqCost ≤ N * regularFamilyRestrictionCost`.
- In `RegularDomains.lean`, the geometric restriction-cost API needed by this
  file is now public:
  `regularFamilyGeomLevel`, `regularFamilyGeomRootCost`,
  `regularFamilyGeomLevel_nonneg`, `regularFamilyGeomRootCost_nonneg`,
  `regularFamilyGeomLevel_rpow_summable`,
  `regularFamilyGeomLevel_root_le_rootCost`, and
  `regularFamilyRestrictionCost_le_of_level_bound`.
- The regular-family indicator positivity API is checked:
  `regularFamilyIndicatorBlock_positive` proves positivity of each canonical
  indicator block, and `regularFamilyIndicator_besov_positive_representation`
  returns an active indicator representation with
  `SouzaPositiveRepresentation`.
- `regularFamily_product_restriction_representations_from_tower` builds the
  regular-family product restrictions from the prescribed source
  representation `R`, records the exact `u₁ + u₂` block identities, and proves
  `regularFamilyRestrictionCost ≤ Crel * (pqCost R + M)`.
- `regularFamilyIndicator_quasiProductBlock_aggregate_summable` is now public
  in `RegularDomains.lean`; it exposes the levelwise summability in the active
  index that is needed to compare finite truncations with the full
  regular-family restriction level power.
- `regularFamilyIndicator_quasiProductBlock_finset_levelCoeffPower_le` proves
  the explicit finite-subfamily product-block level estimate.
- `regularFamily_product_restriction_finset_levelCoeffPower_le` translates
  that explicit finite estimate into the formal
  `regularFamilyRestrictionLevelCoeffPower` notation for finite truncations.
- `regularFamilyRestrictionCost_le_of_global_level_bound` upgrades a levelwise
  estimate on an arbitrary restriction index set `Λcost` to a mixed
  restriction-cost estimate using the ambient regular family geometry.
- `exists_finset_weighted_sum_regularFamily_product_pqCost_le_global` combines
  the finite source-cell overlap estimate with the finite product-block level
  estimate and the global cost comparison.
- `exists_finset_weighted_sum_regularFamily_product_pqCost_le_global_bounded`
  gives the finite uniform partial-sum estimate in the same bounded-gauge
  shape as the final theorem:
  `pqCost S ≤ Cna * N * (pqCost R + M)`, with
  `Cna = 2^{(p-1)/p} (regularFamilyGeomRootCost + 1)`.
- In `Multipliers/NonArchimedeanProperty.lean`, the generic compactness and
  limit-passage API is now public:
  `exists_active_cell_of_representsFunction_ne_zero_ae`,
  `tendsto_nonArchimedean_partial_sums_of_hasSum`,
  `ae_eq_partialFun_on_composed_subseq`,
  `representsFunction_of_tendsto_subseq`,
  `exists_subseq_tendsto_ae_of_tendsto_Lp`,
  `exists_limit_representation_of_finite_sequence`, and
  `exists_limit_representation_of_finite_sequence_with_support`.
- `exists_regularFamily_nonArchimedean_infinite_besov_representation` proves
  the infinite uniform representation step assuming the pointwise `HasSum` is
  supplied: it applies finite initial truncations, passes to the representation
  limit, keeps the support conclusion, and preserves the `pqCost` bound.
- `regularFamily_weight_abs_le_of_overlap_meet`,
  `regularFamily_weightedIndicator_summable_pointwise`, and
  `regularFamily_weightedIndicator_hasSum_tsum_pointwise` start the remaining
  pointwise side: the weighted indicator series has a canonical sum because
  active regular-family domains are disjoint.
- `regularFamily_weightedIndicator_norm_tsum_le_of_active_cell`,
  `regularFamily_weightedIndicator_product_tsum_norm_le_of_active_cell`, and
  `regularFamily_weightedIndicator_product_tsum_bounds_ae` prove the needed
  pointwise and a.e. `L∞` bounds for the canonical uniform regular-family sum.
- `regularFamily_nonArchimedean_indicator_multipliers` is now proved.  The
  final constant is `Cbase + 1`, where `Cbase` is the finite/infinite
  representation constant; the `+1` pays for the `L∞` term in
  `pqCost S + ‖h‖∞`.
- `exists_limit_representation_of_finite_sequence_pos_with_support` is now
  public in `Multipliers/NonArchimedeanProperty.lean`; it is the reusable
  positive compactness step with support transfer.
- `regularDomainIndicatorCost_nonneg` and
  `regularDomain_weight_abs_le_of_overlap_meet` are checked.  These close the
  basic non-uniform overlap extraction:
  `regularDomainOverlapCostInfinite ≤ ofReal N` plus `Q ∩ Ω_i ≠ ∅` gives
  `|Θ_i| ≤ N`, because `regularDomainIndicatorCost` is nonnegative.
- The non-uniform pointwise side is now checked:
  `regularDomain_weightedIndicator_norm_tsum_le_of_active_cell`,
  `regularDomain_weightedIndicator_product_tsum_norm_le_of_active_cell`, and
  `regularDomain_weightedIndicator_product_tsum_bounds_ae` give absolute
  summability and the bounds `‖∑ Θ_i 1_{Ω_i} f‖ ≤ N ‖f‖` and `≤ N M`
  almost everywhere.  This does not require pairwise disjoint domains; it uses
  the `ℝ≥0∞` overlap sum directly.
- The positive quasialgebra block side has advanced:
  `souzaPositiveLevelBlock_atom_nonneg_real` extracts a nonnegative real local
  atom scalar from a positive Souza block, the weighted and strict ancestor
  towers are now proved to be nonnegative real scalars for positive
  representations, and `quasiU1Block_conePositive_of_positive` /
  `quasiU2Block_conePositive_of_positive` prove cone-positivity of the two
  product blocks.  The stronger `quasiU1Block_positive_of_positive` and
  `quasiU2Block_positive_of_positive` are also checked, so each product half is
  Souza-positive before the final `u₁ + u₂` assembly.

Remaining:

- add the positive finite/infinite assembly needed for
  `SouzaConePositiveRepresentation`, now mainly the cone-positive transport
  through the generic `WeakGridSpace.LevelBlock.add` / finite product-block
  assembly and then the already-public positive compactness limit;
- prove the non-uniform representation assembly using the individual
  `regularDomainIndicatorCost` overlap hypothesis.  The pointwise extraction
  and a.e. bounds are now available, but we still need finite product/restriction
  representations for arbitrary regular domains with a cost bound that sums
  over the domains meeting each active source cell;
- the positive cone transport for the two positive variants.

## Checks

After each meaningful Lean edit, run:

```bash
/Users/smania/.elan/bin/lake env lean BesovSpacesGoodGrid/GoodGrid/RegularDomainsNonArchimedean.lean
```

At the end, run:

```bash
rg -n "\bsorry\b" BesovSpacesGoodGrid/GoodGrid/RegularDomainsNonArchimedean.lean
```
