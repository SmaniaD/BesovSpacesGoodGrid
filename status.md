# Current status

This file summarizes the recent state of the central files in
`BesovSpacesGoodGrid/GoodGrid`.

## DONE: Regular domains (`cf`) — 0 sorry (2026-06-14)

New file `BesovSpacesGoodGrid/GoodGrid/RegularDomains.lean` introduces the
formal API for the paper's subsection `Regular domains`:

- `firstContainedLevel`, the formal `k₀(Ω)`;
- `RegularFamily`, for countable disjoint families indexed by `Λ ⊆ ℕ`;
- `RegularDomain`, the one-set version;
- both regularity structures now record `C ≥ 0` and `0 ≤ c < 1` as part of
  the definition, matching the geometric use of `c` in the paper;
- `RegularDomain.toRegularFamily_singleton`, proved bridge from one regular
  domain to the singleton-family formulation;
- supporting proved API for the union construction:
  `RegularFamily.cell_subset_domain`, `cell_subset_union`,
  `selected_cells_disjoint`, `cost_summable`, `measurable_union`,
  `unionFamily`, `unionFamily_cover`, `unionFamily_pairwise_disjoint`, and
  `unionFamily_empty_before`;
- `RegularFamily.regularDomain_union`, proved from the finite cell selection
  at each level, with the cost estimate obtained by assigning each union cell
  to one active index and applying the summable active-family cost series;
- structural API for the strongly-regular-to-regular construction:
  `StronglyRegularDecomposition.cell_subset_inter`,
  `cell_subset_cell`, `cell_subset_domain`, plus the private candidate family
  assembled over the `k₀(Ω)` partition, with proved `family_subset`,
  `empty_before`, `cover`, and pairwise-disjoint cells;
- proved quantitative strongly-regular-to-regular theorem with ratio
  `λ₂^((β-s)p)`, the indicator norm estimate `(estG)`, and the bounded
  multiplier operator `g ↦ g·1_Ω` on `B^s_{p,q} ∩ L∞`;
- added the endpoint `q = ∞` wrappers
  `regularDomain_indicator_besov_norm_bound_top` and
  `regularDomain_indicator_multiplier_on_bounded_souzaBesov_top`;
- added the all-`q` wrapper constant `regularDomainIndicatorCost` and the
  domain/family wrappers `regularDomain_indicator_besov_norm_bound_all`,
  `regularDomain_indicator_multiplier_on_bounded_souzaBesov_all`,
  `regularFamilyUnion_indicator_besov_norm_bound_all`, and
  `regularFamilyUnion_indicator_multiplier_on_bounded_souzaBesov_all`;
- proved localized restriction representation estimate `(pdd)/(hiip1)`:
  `regularFamily_restriction_representations`.
- added the proposal file
  `BesovSpacesGoodGrid/GoodGrid/RegularDomainsNonArchimedean.lean`, containing
  the non-uniform and uniform regular-domain non-Archimedean statements, each
  with a positive variant.  This new file currently has 4 intentional
  `sorry`s, one for each proposed main theorem.

`RegularDomains.lean` is currently `sorry`-free.  No axioms or executable
admits were added there.  The new non-Archimedean proposal file is intentionally
not complete yet, as recorded above.

The theorem `regularDomain_of_stronglyRegularDomain` now explicitly assumes
`hΩcell : ContainsGridCell G Ω`, matching the LaTeX proof's use of `k₀(Ω)`.
It constructs the regular-domain decomposition from the strong decompositions
of `Q ∩ Ω` over all `Q ∈ P^{k₀(Ω)}`; the quantitative comparison turning the
strong `1-βp` costs into the regular `1-sp` geometric cost is now proved.

The theorem `regularFamily_restriction_representations` is now proved.  It
produces Souza representations of `g · 1_{Ωᵣ}` with localized nonzero
coefficients and the mixed coefficient bound `(hiip1)`.  Its Lean statement
uses the bounded version suggested by the paper: the input comes with an
essential bound `∀ᵐ z, ‖g z‖ ≤ M`, and the target estimate is controlled by the
bounded Besov gauge `Norm_Costpq xg + M`.

Resolved attempt note (2026-06-14): the LaTeX proof uses the `u₁ + u₂`
product construction from Proposition `mult33`.  The needed formal route was
to expose concrete product representations with block identities, then prove
the regular-family aggregate estimate before taking the mixed `(p,q)` gauge.

Follow-up refactor (2026-06-14): `QuasiAlgebra.lean` now exposes the
`quasiU1Block`, `quasiU2Block`, `weightedAncestorCoeffSum`,
`strictWeightedAncestorCoeffSum`, and `exists_weighted_fouRepresentation`
definitions/theorems.  The theorem
`exists_quasi_product_of_tower_representations` returns a concrete finite-cost
`LpGridRepresentation` together with the explicit block identity
`R.block k = LevelBlock.add (quasiU1Block ... k) (quasiU2Block ... k)`.
New support lemmas show that nonzero coefficients in `u₁`/`u₂` and in
weighted ancestor towers come from nonzero source coefficients.  The remaining
work is to build the regular-family indicator representations indexed by
`r ∈ Λ`, prove their tower/support estimates, and feed those estimates into a
localized product-cost argument for `(hiip1)`.

Continuation (2026-06-14): `RegularDomains.lean` now has the reusable block
API for the regular-family indicators:

- `regularFamilyIndicatorBlock`, the canonical level block attached to
  `ℱᵏ(Ωᵢ)`;
- `regularFamilyIndicatorBlock_coeff_ne_zero_mem` and
  `regularFamilyIndicatorBlock_coeff_ne_zero_subset_domain`, the support
  bookkeeping for selected cells;
- `regularFamilyIndicatorBlock_levelCoeffPower`, identifying the level
  coefficient power with `∑_{Q∈ℱᵏ(Ωᵢ)} μ(Q)^(1-sp)`;
- `regularFamilyIndicatorBlock_represents_levelTile`, showing the block
  represents the finite level tile `⋃_{Q∈ℱᵏ(Ωᵢ)} Q`.
- `regularFamilyIndicatorBlock_aggregate_levelCoeffPower_le`, the levelwise
  aggregate `(dom)` estimate rewritten directly for the indicator blocks.
- `regularFamilyIndicator_quasiU1Block_coeff_ne_zero_subset_domain` and
  `regularFamilyIndicator_quasiU2Block_coeff_ne_zero_subset_domain`, the
  formal support step from the `u₁+u₂` construction: when the indicator blocks
  for `Ωᵢ` are the first product input, every nonzero output coefficient is on
  a cell contained in `Ωᵢ`.
- `regularFamilyIndicator_strictWeightedAncestorCoeffSum_norm_le_one`, the
  strict ancestor tower bound for the canonical indicator representation.
- `regularFamilyIndicator_quasiU1Block_aggregate_levelCoeffPower_le`, the
  aggregate level estimate for the `u₁` contribution over all active indices.
- `regularFamilyIndicator_quasiU2Block_unique_active_index` and
  `regularFamilyIndicator_quasiU2Block_coeff_norm_rpow_le`, the two local
  ingredients for the `u₂` aggregate estimate: uniqueness of the active index
  for a fixed output cell and domination by the corresponding coefficient of
  the representation of `g`.
- `regularFamilyIndicator_quasiU2Block_aggregate_levelCoeffPower_le`, the
  aggregate level estimate for the `u₂` contribution:
  the sum over all active indices is bounded by the level coefficient power of
  the representation of `g`.

These compile and are used by the completed indexed restriction theorem.

Technical note: the existing single-domain indicator estimates require
`q ≠ ∞` to turn levelwise geometric control into a finite global `(p,q)` cost;
the `0 ≤ c` and `c^(q/p) < 1` facts are now derived from the regular-domain
field `0 ≤ c < 1`.  The completed
`regularFamily_restriction_representations` theorem estimates the aggregate
level-power before taking the `(p,q)` gauge, using the pairwise disjointness of
the regular family.  Mathematically this gives a bound of the form
`C * (pqCost Rg + M * indicatorFamilyCost)`, which is then absorbed into the
bounded-Besov right hand side.

Formal note: `RegularFamily.cost_summable` is now a theorem, not a field.  The
proof does not rely on the real-valued `tsum` in `cost`; it uses the stronger
structural fact that, at each fixed level, the partition is finite and
pairwise-disjoint active domains cannot select the same level cell.  Hence the
active level-cost function has finite support.

Notation note: the mathematical documentation writes characteristic functions
as `\mathbbm{1}_E` (with LaTeX package `bbm`); Lean code continues to use
`Set.indicator` and related `indicatorConstLp` names.

## DONE: Pointwise Multipliers III (`mult33`, Prop 19.1) — 0 sorry (2026-06-12)

New file `BesovSpacesGoodGrid/GoodGrid/QuasiAlgebra.lean` (imported by the
root module) formalizes the paper's quasi-algebra result
`B^s_{p,q} ∩ L∞`.

Public API:

- `ae_norm_mul_le_mul_bounds`: the elementary `L∞` estimate
  `‖f·g‖ ≤ Mf·Mg` almost everywhere from the two almost-everywhere bounds.
- `exists_quasiAlgebra_product_representation`: technical core for the
  paper's `u₁ + u₂` construction with two `(s,p)` Souza representations.
  The proof constructs the two triangular block families directly, controls
  their costs by the full and strict weighted ancestor towers, and passes the
  finite truncation identity to the limit in `L^p`.
- `souzaPointwiseMultipliersIII`: outer quantitative quasi-algebra statement,
  proved from the core and the `L∞` product estimate:
  `|fg|_B + |fg|∞ ≤ Cqa (|f|_B + Mf)(|g|_B + Mg)`.

Axioms checked (`propext, Classical.choice, Quot.sound`) for
`souzaPointwiseMultipliersIII` and
`exists_quasiAlgebra_product_representation`.

Reusable internal infrastructure added in `QuasiAlgebra.lean`: weighted and
strict weighted ancestor towers for `(s,p)` Souza atoms, pointwise collapse of
finite product truncations, abstract cost transfer for the two block families,
and the general weighted `fou` representation extracted from the standard
representation machinery plus Proposition `boup`.B.

## DONE: Pointwise Multipliers II (`mult`, Prop 18.10) — 0 sorry (2026-06-12)

File `BesovSpacesGoodGrid/GoodGrid/Multipliers/Bp1overpinftyisMultiplier.lean`
(imported by the umbrella) is now **complete and `sorry`-free**.  Main
statement `souzaPointwiseMultipliersII`: for `0 < s < 1/p`, every `g`
represented by `xg ∈ B^{1/p}_{p,∞}` with `‖g‖ ≤ M` a.e. is a pointwise
multiplier of `B^s_{p,q}` with operator bound
`Cmult · |xg|_{B^{1/p}_{p,∞}} + M`.  Axioms checked
(`propext, Classical.choice, Quot.sound`) for
`souzaPointwiseMultipliersII`, `exists_mult_product_representation` and
`exists_fouRepresentation`.

Structure:

1. `exists_fouRepresentation` (Corollary `fou` + Prop `boup`.B): canonical
   representation `Rg` of `g` with `pqCost_{(p,∞)} Rg ≤ Cfou·|xg|` and all
   ancestor-tower coefficient sums (`ancestorCoeffSum`) bounded by `M`, via
   the standard representation machinery and Dirac approximations.
2. `exists_mult_product_representation` — the `u₁ + u₂` construction, now
   proved, with constant `Cconv = λ₂^θ/(1−λ₂^θ)`, `θ = 1/p − s`:
   - **`u₁` cost**: from `multU1Block_coeff_norm_le` plus the
     single-ancestor collapse (`ancestor_ite_coeff_sum_le_levelRoot`), the
     level roots obey `root(u₁)_j ≤ pqCost_∞(Rg) · ∑_{k<j} λ₂^{(j−k)θ}
     root(Rf)_k`; the `(p,q)` cost follows from a self-contained discrete
     Young inequality with geometric kernel
     (`geometric_conv_rpow_summable_and_tsum_le`, proved by iterated
     Minkowski `Real.Lp_add_le_tsum_of_nonneg'` on shifted blocks), with a
     separate uniform bound at `q = ∞`.
   - **`u₂` cost**: `multU2Block_levelCoeffPower_le` gives
     `cost(u₂) ≤ M · pqCost(Rf)` (helpers
     `souza_abstract_cost_{top,finite}_of_blockLvlCoeff_le`).
   - **Convergence**: both block families have finite abstract `(p,q)` cost,
     so their series converge in `L^p` by
     `WeakGridSpace.formalBlockSeq_hasRepresentation` (no compactness
     needed); `Norm_Costpq` of each piece is bounded through
     `Norm_Costpq_le_cost`, and the two pieces are glued by the triangle
     inequality `Norm_Costpq_add_le`.
   - **Identity `g·f = u₁ + u₂`**: the truncations satisfy the *exact*
     pointwise identity `(∑_{j<n} Rg_j)(∑_{k<n} Rf_k) = ∑_{j<n} u₁_j +
     ∑_{k<n} u₂_k` (`mult_truncated_pointwise_identity`, proved along the
     tower of cells containing each point, with the scalar triangular-split
     identity `truncation_scalar_identity` by induction); the identity
     passes to the limit by
     `representsPointwiseProduct_of_tendsto_Lp_varying`, a varying-multiplier
     version of `RepresentsPointwiseProduct.of_tendsto_Lp` via three nested
     a.e.-convergent subsequences.  (The `L¹`/`compa1` route from the paper
     was not needed.)
3. The outer proof (ε-optimization over near-optimal representations of `f`,
   uniqueness of the product representative in `L^p`) as before.

Reusable new infrastructure (private in the file, can be publicized later):
the geometric discrete Young inequality, the pointwise evaluation lemma
`souza_toFunLt_eq_coeff_mul_atom` (a Souza level block at a point collapses
to `coeff·atom` of the unique cell), the tower collapse
`tower_ite_sum_collapse`, `ancestorCoeffSum_tower_eq`, and
`coeFn_finset_range_sum_toLp`.

**Remark `pos3` (positive version) — DONE (2026-06-12).**  New theorems in
the same file, axioms checked (`propext, Classical.choice, Quot.sound`):

- `souzaPointwiseMultipliersIIPositive` — the paper's Remark `pos3`
  (`B^a_{p,b}` replaced by `B^{a+}_{p,b}` everywhere): if `g` is represented
  by `xg` in the positive cone of `B^{1/p}_{p,∞}` with finite positive gauge
  and `‖g‖ ≤ M` a.e., then for every `x` in the positive cone of `B^s_{p,q}`
  with finite positive gauge there is a positive product representative `y`
  (`SouzaPositiveElement`) with
  `souzaPositiveNorm y ≤ (ofReal Cmult · souzaPositiveNorm xg + ofReal M) ·
  souzaPositiveNorm x` — `ℝ≥0∞` arithmetic with a double ε-optimization
  (`ENNReal.le_of_forall_pos_le_add`, δ := min 1 (ε/D)), uniqueness of the
  product representative fixing `y` across runs.
- `exists_mult_product_representation_pos` — representation form: positive
  finite-cost `Rg`, `Rf` give a positive representation `Ry` of the product
  with `pqCost Ry ≤ (Cconv·pqCost_∞ Rg + M)·pqCost_q Rf`.

Proof architecture: the core was refactored into
`exists_mult_product_blocks` (block form, exposing `R1.block = multU1Block`,
`R2.block = multU2Block`), shared by the non-positive and positive wrappers.
For the positive side: `multU1Block_positive`/`multU2Block_positive`
(positivity is inherited by the `u₁`/`u₂` coefficients, the `u₁` atoms are
canonical by construction); the canonical hypothesis comes from
`souzaPositiveRepresentation_canonical` (positive blocks have canonical
atoms by definition); and the ancestor-tower bound `≤ M` is **derived** from
positivity (`ancestorCoeffSum_norm_le_essBound_of_positive`, the positive
form of Prop `boup`.B: the tower partial sums are nondecreasing with an
a.e.-convergent subsequence to `g`, so they are `≤ M` on a point of each
cell, hence everywhere by constancy on cells).  The two pieces are summed by
`souzaPositiveRepresentationAdd` with its cost triangle inequality.

## DONE: Strongly regular domains + Pointwise Multipliers I (2026-06-10)

New file `BesovSpacesGoodGrid/GoodGrid/Multipliers/StronglyRegularDomains.lean`
(imported by the umbrella `GoodGrid/Multipliers.lean`), formalizing the
paper's subsection `srd`:

- `StronglyRegularDecomposition` / `StronglyRegularDomain`: the definition of
  an `(a, K, k₁)`-strongly regular domain (exact disjoint tiling of `Q ∩ Ω`
  by grid cells, with the level-by-level cost `∑_P μ(P)^a ≤ K·μ(Q)^a`).
- `souzaPositiveSelfsTailBound_of_stronglyRegularDomain` — **Prop 18.7/18.8
  (`pos2`)**: `|\mathbbm{1}_Ω|_{B^{β+,k₁}_{p,∞,selfs}} ≤ K^{1/p}` for a
  `(1−βp, K, k₁)`-strongly regular `Ω`, as a positive tail `selfs` bound.
  Weighted variant `souzaPositiveSelfsTailBound_smul_of_stronglyRegularDomain`
  (`Θ·\mathbbm{1}_Ω`, constant `Θ·K^{1/p}`).
- `souzaPositiveFunction_of_stronglyRegularDomain`: `Θ·\mathbbm{1}_Ω` lies in the
  positive Souza-Besov cone `B^{β+}_{p,∞}` (sum of the `pos2` pieces over the
  level-`k₁` cells, glued with `exists_souzaPositiveRepresentation_finset_sum`).
- `souzaPointwiseMultipliersI` — **Prop 18.9 (`pm1`)**: for finite families of
  `(1−βp, K_i, t_i)`-strongly regular domains with weights `Θ_i > 0` and a
  canonical finite-cost representation `R` of `f` satisfying conditions A
  (`stronglyRegularOverlapCost ≤ N` on active cells) and B, the product
  `(∑ Θ_i·\mathbbm{1}_{Ω_i})·f` has a representation `S` with
  `pqCost S ≤ Cgen2·N·pqCost R`, every active cell of `S` lies a.e. in some
  `Ω_i`, and positivity of `R` gives cone-positivity of `S`.  Derived from
  `souzaNonArchimedeanPropertyPositiveCone` with `qtilde = ∞`.
- `souzaPointwiseMultipliersIInfinite` — **Prop 18.9 (`pm1`), infinite `Λ`**:
  the family may be indexed by an arbitrary `Λ ⊆ ℕ`; condition A is the
  `ℝ≥0∞`-series bound `stronglyRegularOverlapCostInfinite ≤ N` (no
  summability witness).  Conclusions: a.e. absolute convergence of
  `∑ Θ_i·\mathbbm{1}_{Ω_i}(z)` on `{f ≠ 0}` with bound `Cgen2·N`, the limit function
  `h ∈ L^p`, a representation `S` of `h` with finite cost and
  `pqCost S ≤ Cgen2·N·pqCost R`, plus the same [i]/[ii] as the finite case.
  Derived from `souzaNonArchimedeanPropertyPositiveConeInfinite`.

Proof core of `pos2` (`exists_souzaPositiveElement_indicator_mul_atom`): the
representation of `Θ·\mathbbm{1}_Ω·a_Q` has, at level `k`, coefficients
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

At that time the whole project compiled with no `sorry` (`lake build` green,
3454 jobs, now including `NonArchimedeanPropertyPositiveStandalone`, which is
imported by the umbrella `GoodGrid/Multipliers.lean`).  Section 19 is now also
complete in `QuasiAlgebra.lean`.

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

The multiplier files through Proposition 19.1 remain complete, and the full
project build is green after the Section 19 completion.

Regular domains update (2026-06-14):

- `RegularDomains.lean` is now `sorry`-free, including
  `regularFamily_restriction_representations`.
- Proved infrastructure for that theorem:
  `regularFamilyIndicatorBlock_levelCoeffPower_le_familyCost`,
  summability of the aggregate `u₁` and `u₂` level costs, the aggregate
  product-block estimate for `u₁ + u₂`, and
  `regularFamilyIndicator_besov_representation` for each active member of a
  regular family.
- The theorem has been moved below the indicator/union helper lemmas so the
  final proof can use the `indicatorConstLp` countable-union summation tools.
- The remaining mathematical step is to turn the product-block level estimate
  into the mixed `regularFamilyRestrictionCost` bound, separately for
  `q = ∞` and `q < ∞`, then assemble the per-index product representations.

Possible next steps (see `todo.md`):

- Theorem 15.1 wrap-up equivalence + the `L¹` functional of Cor 15.2;
  Section 16 examples; Sections 20–21 (the quasialgebra result of
  Section 19 is done).
- Stylistic cleanup: linter warnings (`simpa`→`simp`, unused `simp`
  arguments, deprecated `push_neg`) scattered across the files.

## Recent checks (2026-06-12)

```bash
lake build                      # green, whole project (3459 jobs)
lake env lean BesovSpacesGoodGrid/GoodGrid/QuasiAlgebra.lean  # green, no sorry
rg -n "\bsorry\b" BesovSpacesGoodGrid --glob "*.lean"         # only documentation text
#print axioms souzaPointwiseMultipliersIII
#  → [propext, Classical.choice, Quot.sound]
#print axioms exists_quasiAlgebra_product_representation
#  → [propext, Classical.choice, Quot.sound]
#print axioms souzaPointwiseMultipliersII
#  → [propext, Classical.choice, Quot.sound]
#print axioms souzaPointwiseMultipliersIIPositive
#  → [propext, Classical.choice, Quot.sound]
#print axioms exists_mult_product_representation
#  → [propext, Classical.choice, Quot.sound]
#print axioms exists_mult_product_representation_pos
#  → [propext, Classical.choice, Quot.sound]
#print axioms exists_fouRepresentation
#  → [propext, Classical.choice, Quot.sound]
#print axioms souzaNonArchimedeanPropertyPositiveConeInfinite
#  → [propext, Classical.choice, Quot.sound]
#print axioms souzaNonArchimedeanPropertyPositiveCone
#  → [propext, Classical.choice, Quot.sound]
#print axioms exists_souzaSelfsMultiplierConstant            (and the other
#  three public theorems of SelfsSubsetMultipliers.lean)
#  → [propext, Classical.choice, Quot.sound]
```
