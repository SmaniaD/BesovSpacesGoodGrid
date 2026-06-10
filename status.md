# Current status

This file summarizes the recent state of the central files in
`BesovSpacesGoodGrid/GoodGrid`.

## DONE: Strongly regular domains + Pointwise Multipliers I (2026-06-10)

New file `BesovSpacesGoodGrid/GoodGrid/Multipliers/StronglyRegularDomains.lean`
(imported by the umbrella `GoodGrid/Multipliers.lean`), formalizing the
paper's subsection `srd`:

- `StronglyRegularDecomposition` / `StronglyRegularDomain`: the definition of
  an `(a, K, k₁)`-strongly regular domain (exact disjoint tiling of `Q ∩ Ω`
  by grid cells, with the level-by-level cost `∑_P μ(P)^a ≤ K·μ(Q)^a`).
- `souzaPositiveSelfsTailBound_of_stronglyRegularDomain` — **Prop 18.7/18.8
  (`pos2`)**: `|1_Ω|_{B^{β+,k₁}_{p,∞,selfs}} ≤ K^{1/p}` for a
  `(1−βp, K, k₁)`-strongly regular `Ω`, as a positive tail `selfs` bound.
  Weighted variant `souzaPositiveSelfsTailBound_smul_of_stronglyRegularDomain`
  (`Θ·1_Ω`, constant `Θ·K^{1/p}`).
- `souzaPositiveFunction_of_stronglyRegularDomain`: `Θ·1_Ω` lies in the
  positive Souza-Besov cone `B^{β+}_{p,∞}` (sum of the `pos2` pieces over the
  level-`k₁` cells, glued with `exists_souzaPositiveRepresentation_finset_sum`).
- `souzaPointwiseMultipliersI` — **Prop 18.9 (`pm1`)**: for finite families of
  `(1−βp, K_i, t_i)`-strongly regular domains with weights `Θ_i > 0` and a
  canonical finite-cost representation `R` of `f` satisfying conditions A
  (`stronglyRegularOverlapCost ≤ N` on active cells) and B, the product
  `(∑ Θ_i·1_{Ω_i})·f` has a representation `S` with
  `pqCost S ≤ Cgen2·N·pqCost R`, every active cell of `S` lies a.e. in some
  `Ω_i`, and positivity of `R` gives cone-positivity of `S`.  Derived from
  `souzaNonArchimedeanPropertyPositiveCone` with `qtilde = ∞`.
- `souzaPointwiseMultipliersIInfinite` — **Prop 18.9 (`pm1`), infinite `Λ`**:
  the family may be indexed by an arbitrary `Λ ⊆ ℕ`; condition A is the
  `ℝ≥0∞`-series bound `stronglyRegularOverlapCostInfinite ≤ N` (no
  summability witness).  Conclusions: a.e. absolute convergence of
  `∑ Θ_i·1_{Ω_i}(z)` on `{f ≠ 0}` with bound `Cgen2·N`, the limit function
  `h ∈ L^p`, a representation `S` of `h` with finite cost and
  `pqCost S ≤ Cgen2·N·pqCost R`, plus the same [i]/[ii] as the finite case.
  Derived from `souzaNonArchimedeanPropertyPositiveConeInfinite`.

Proof core of `pos2` (`exists_souzaPositiveElement_indicator_mul_atom`): the
representation of `Θ·1_Ω·a_Q` has, at level `k`, coefficients
`Θ·(μP/μQ)^{1/p−β}` on the cells `P ∈ ℱ^k` with canonical atoms; its level
cost is `≤ Θ^p·K` by the decomposition cost; the `hasSum` field is the new
`L^p` convergence lemma `hasSum_indicatorConstLp_iUnion` (indicators of
countably many disjoint sets sum in `L^p` to the indicator of the union — the
remainder measure tends to zero by countable additivity).  Other reusable
private helpers: `sum_indicatorConstLp_disjoint` (finite case),
`grid_level_eq_of_mem_mem` (a set is a grid cell at only one level).

Notes on fidelity to the paper: the support conclusion [i] of `pm1` is stated
in the a.e. form (`Q ⊆ Ω_i` up to measure zero), matching the formalized
Remark `posrem`; positivity [ii] is cone-positivity of `S`, as in `posrem`.

## DONE: Corollary 18.6 (`23er`) — selfs classes are multipliers (2026-06-10)

New file `BesovSpacesGoodGrid/GoodGrid/Multipliers/SelfsSubsetMultipliers.lean`
(imported by the umbrella `GoodGrid/Multipliers.lean`), proving the paper's
Corollary `23er`: for `0 < s < β < 1/p` and `q, qtilde ∈ [1,∞]`,
`B^{β,t}_{p,qtilde,selfs} ⊂ M(B^s_{p,q})`, and the inclusion is continuous.
Note: the formal statement carries `β < 1/p` (inherited from the formalized
non-Archimedean property `sepa`), consistent with the Part III standing box.

Public theorems (axioms checked: `propext, Classical.choice, Quot.sound`):

```lean
souzaPointwiseSelfsTailBound_levelZero            -- tail bound at t ⟹ at 0, constant ·|P^t|
exists_souzaSelfsMultiplierConstant               -- quantitative: tail bound C ⟹ multiplier bound Cmult·C
souzaPointwiseMultiplier_of_souzaPointwiseSelfsTailClass  -- the inclusion
souzaPointwiseMultiplierNorm_le_const_mul_selfsTailNorm   -- continuity (norm form)
```

Proof structure:

- **Core (cutoff `t = 0`)**: `souzaNonArchimedeanPropertyLambdaFinite` applied
  to the singleton family `Λ = {0}`, `g_0 = g`, all cutoffs `0`, `N = C`;
  conditions A and B hold trivially (A reduces to
  `souzaPointwiseSelfsTailNorm ≤ C`, B to `0 ≤ k`).  The product representative
  is unique in `Lp` (a.e. equality), so optimizing over near-optimal
  representations of `x` (`exists_cost_lt_Norm_Costpq_add` + ε-argument)
  upgrades the cost bound to `Norm_Costpq y ≤ Cgen·C·Norm_Costpq x`.
- **Level lowering** (`souzaPointwiseSelfsTailBound_levelZero`): an atom on a
  cell `Q` of level `< t` is exactly the finite sum of its restrictions to the
  level-`t` cells `P ⊆ Q` (nested partitions: covering + disjointness +
  `partition_subset_or_disjoint_of_le`).  Each piece is `λ_P · (atom on P)`
  with `λ_P = (μQ/μP)^(β−1/p) ≤ 1`, so the tail hypothesis applies on each
  `P`; the candidate is `Σ λ_P • y_P`, with cost `≤ |P^t| · C` by a finite-sum
  triangle inequality for `Norm_Costpq`.
- The general corollary composes the two; constant `Cgen · |P^t|`.

Supporting changes:

- `souzaNonArchimedeanPropertyLambdaFinite` (NonArchimedeanProperty.lean) now
  also returns `FinitePQCost S` in its conclusion (the inner private lemmas
  already provided it; one internal use adapted).
- New API in `WeakGrid/Multipliers.lean`:
  `pointwiseMultiplierBoundSet_bddBelow`, `pointwiseMultiplierNorm_le_of_bound`.
- New generic private helpers in SelfsSubsetMultipliers.lean: zero
  representation has finite/zero cost, finite-sum triangle inequality for
  `Norm_Costpq` (any atom family).

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

## Recent checks (2026-06-10)

```bash
lake build                      # green, whole project (now 3455 jobs)
grep -rn "sorry" BesovSpacesGoodGrid --include="*.lean"   # empty
#print axioms souzaNonArchimedeanPropertyPositiveConeInfinite
#  → [propext, Classical.choice, Quot.sound]
#print axioms souzaNonArchimedeanPropertyPositiveCone
#  → [propext, Classical.choice, Quot.sound]
#print axioms exists_souzaSelfsMultiplierConstant            (and the other
#  three public theorems of SelfsSubsetMultipliers.lean)
#  → [propext, Classical.choice, Quot.sound]
```
