# Current status

This file summarizes the recent state of the central files in
`BesovSpacesGoodGrid/GoodGrid`.

## DONE: positive version of the non-Archimedean theorem (2026-06-09)

**The whole project compiles with no `sorry`** (`lake build` green, 3454 jobs,
now including `NonArchimedeanPropertyPositiveStandalone`, which is imported by
the umbrella `GoodGrid/Multipliers.lean`).

Axiom check (no `sorryAx`, only the standard axioms
`propext, Classical.choice, Quot.sound`):

```lean
souzaNonArchimedeanProperty                       -- infinite non-positive version
souzaNonArchimedeanPropertyLambdaFinite           -- finite non-positive version
souzaNonArchimedeanPropertyPositiveCone           -- positive version (public, Standalone)
exists_nonArchimedeanProductRepresentation_positive
```

Files:

- `BesovSpacesGoodGrid/GoodGrid/PositiveCone.lean`
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/NonArchimedeanProperty.lean`
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/NonArchimedeanPropertyPositiveStandalone.lean`
- `BesovSpacesGoodGrid/WeakGrid/InducedGrid.lean`

The final statement of `souzaNonArchimedeanPropertyPositiveCone` follows
Remark `posrem` of the paper, with the two consequences separated according to
their true strengths:

- hypothesis on `R`: only `SouzaCanonicalRepresentation` (canonical atoms,
  arbitrary complex coefficients);
- **[ii]** support: unconditional, weakened to a.e. —
  active cell `Q` of `S` ⟹ `∃ i ∈ Λ`, `g i ≠ 0` a.e. on `Q`;
- **[i]** positivity: `SouzaPositiveRepresentation R →
  SouzaConePositiveRepresentation S` (positive cone: real coefficients ≥ 0,
  atoms with real values ≥ 0 a.e.).

### How the last piece was closed (Sub-lemma 1)

`exists_nonArchimedeanLocalTransmutationData_pos` (previously the last `sorry`)
was proved by **additive assembly, one multiplier at a time**:

- Per-multiplier brick
  (`exists_souzaPositiveTailProduct_single_s_atom_geometric`): chain
  positive tail bound → extraction of a positive representation with
  controlled cost → exact support in `Q` (support theorem + `hbefore` by
  measure separation) → reading on the induced grid (positivity transfer) →
  β→s transmutation → ambient reindexing → scaling by `μ(Q)^{s-β}` →
  canonicalization.
- Sum over `Λ` with `exists_souzaPositiveRepresentation_finset_sum`
  (coefficients add, canonical atoms, levelwise Minkowski); the constants add
  up to `N + |Λ|·εTail`.
- Support witness: nonzero coefficient of the sum ⟹ some summand is nonzero
  (nnreals) ⟹ linchpin
  `souzaPositiveRepresentation_ae_ne_zero_on_active_cell` ⟹ `g_r ≠ 0` a.e.
  on the cell.

New / exposed reusable infrastructure:

- `PositiveCone.lean`: public positive sum/zero
  (`souzaPositiveRepresentationAdd*`, `souzaPositiveZeroRepresentation*`),
  `souzaPositiveRepresentationAdd_levelCoeffRoot_le` (Minkowski),
  `exists_souzaPositiveRepresentation_finset_sum`,
  `exists_souzaPositivePointwiseSelfsTailBound_lt_norm_add`,
  `exists_souzaPositiveRepresentation_pqCostENNReal_lt`,
  `pqCost_le_of_pqCostENNReal_le`, `goodGridCell_not_subset_of_level_lt`,
  `souzaPositiveRepresentation_block_toLp_eq_zero_of_level_lt`.
- `InducedGrid.lean`: `cast_levelBlock_atom_toFunction`,
  `inducedRepresentationToAmbient_atom_toFunction_pos`.
- `NonArchimedeanProperty.lean`: `canonicalSouzaAtom_eq_smul_beta`,
  `ambientSupportedRepresentationToInduced_souzaPositive`,
  `souzaPositiveRepresentation_block_pos_clause`.

## Earlier result: tail `selfs` implies `L∞` uniformly in `t`

Main files:

- `BesovSpacesGoodGrid/GoodGrid/Multipliers/Definition.lean`
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/MultipliersareBounded.lean`

Proved: `SouzaPointwiseSelfsTailClass`,
`ae_le_of_eventually_goodGridLevelAverage_le`, the local tail estimates
(product with the canonical atom, local `MemLp`, `eLpNorm` bounds at exponents
`p` and `1`, integral of `‖m‖` on a tail cell), and

```lean
souzaPointwiseSelfsTailBound_norm_ae_le
souzaPointwiseSelfsTailNorm_norm_ae_le
souzaPointwiseSelfsTailClass_norm_ae_bounded
```

that is, `‖m(x)‖ ≤ C(G,s,p,q) · |m|_{B^{s,t}_{p,q,selfs}}` a.e., with a
constant independent of `t`.

## Earlier results in PositiveCone.lean

No `sorry`; main statements:

- `exists_souzaPositive_decomposition_of_aeRealValued`
- `exists_souzaPositive_decomposition_of_aeComplexValued`
- `souzaPositiveCone_dense_in_LpNonnegativeCone`
- `support_ae_countable_iUnion_goodGridCells_of_souzaPositiveFunction`
- the linchpin `souzaPositiveRepresentation_ae_ne_zero_on_active_cell` and the
  support theorem
  `souzaPositiveRepresentation_coeff_eq_zero_of_not_subset_cell`.

## Non-positive versions (NonArchimedeanProperty.lean)

- `souzaNonArchimedeanPropertyLambdaFinite` (finite) — proved.
- `souzaNonArchimedeanProperty` (infinite, condition A with a witnessed
  `HasSum`) — proved, via `exists_nonArchimedeanInfinite_pointwise_hasSum`
  (pointwise part), compactness of representations with uniform cost
  (`exists_strongly_convergent_subseq_of_uniform_pqCost`), and identification
  of the limit through the a.e. partial sums.

## DONE: INFINITE version of the positive theorem (2026-06-09)

`souzaNonArchimedeanPropertyPositiveConeInfinite` (Standalone; core in
NonArchimedeanProperty.lean) — the infinite-index analogue (`Λ : Set ℕ`) of
the positive theorem, with axioms checked
(`propext, Classical.choice, Quot.sound`).

Statement: the infinite condition A is an `ℝ≥0∞`-valued series bound
(`∑' i : Λ, nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm ≤ ofReal N`,
no summability witness needed); the conclusions are those of the non-positive
infinite version (pointwise absolute summability with bound `Cgen·N` on
`{f ≠ 0}`, the limit function `h`, `MemLp`, a representation `S` with
`pqCost S ≤ Cgen·N·pqCost R`) **plus**:

- **[ii]** support: active cell of `S` ⟹ `∃ i ∈ Λ`, `g i ≠ 0` a.e. on it;
- **[i]** `R` positive ⟹ `S` cone-positive.

Proof architecture:

- **Canonical refactor of the tail `L∞`** (MultipliersareBounded): new
  `SouzaPointwiseCanonicalSelfsTailBound` (only products with canonical
  atoms); the internal chain of 8 tail lemmas was generalized to this
  hypothesis (their proofs only ever test the multiplier against canonical
  atoms); `Bound.toCanonical` and
  `SouzaPositivePointwiseSelfsTailBound.toCanonical` (given `C ≠ ∞`) provide
  the bridges.  This yields `souzaPositivePointwiseSelfsTailNorm_norm_ae_le`:
  `‖m‖ ≤ K·(positive tail seminorm).toReal` a.e.
- **Pointwise part** (`exists_nonArchimedeanInfinite_pointwise_hasSum_pos`):
  mirrors the non-positive one; summability by comparison with
  `(Term i).toReal` (`ENNReal.summable_toReal`/`tsum_toReal_eq`);
  measurability of the partial products via the finite positive theorem.
- **Extended compactness** (Completeness):
  `exists_strongly_convergent_subseq_of_uniform_pqCost` now also returns the
  convergence of coefficients and of atoms (`atomLp`) to the limit.
- **Truncations** (`exists_nonArchimedean_finite_representation_initial_pos`):
  the finite positive theorem on `nonArchimedeanLambdaInitial Λ n` (which now
  exposes `FinitePQCost S`), uniform cost
  `nonArchimedeanPositiveRepresentationConstant·N·pqCost R`.
- **Limit** (`exists_limit_representation_of_finite_sequence_pos`):
  [ii] passes through the coefficient convergence (limit ≠ 0 ⟹ some n with
  a nonzero coefficient ⟹ finite witness); [i] passes through the closedness
  of the nonnegative real ray in ℂ (`complex_nonnegReal_isClosed`) for the
  coefficients, and a.e. convergence of a subsequence of the atoms in `Lp`
  for the atoms.

## What remains

Nothing pending: **zero `sorry` in the project**, full build green
(3454 jobs), axioms of the main theorems (finite/infinite,
positive/non-positive) verified.

Possible next steps (to be decided):

- Stylistic cleanup: linter warnings (`simpa`→`simp`, unused `simp`
  arguments, deprecated `push_neg`) scattered across the files.
- Commit the changes (sorry 1 + the Standalone import + the infinite
  positive version are in the working tree, uncommitted).

## Recent checks (2026-06-09)

```bash
lake build                      # green, 3454 jobs, whole project
grep -rn "sorry" BesovSpacesGoodGrid --include="*.lean"   # empty
#print axioms souzaNonArchimedeanPropertyPositiveConeInfinite
#  → [propext, Classical.choice, Quot.sound]
#print axioms souzaNonArchimedeanPropertyPositiveCone
#  → [propext, Classical.choice, Quot.sound]
```
