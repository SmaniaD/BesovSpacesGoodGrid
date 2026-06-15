# TODO

Pending formalization work, in rough priority order.  See `status.md` for
what is already done and `paper-map.md` for the paper-wide picture.

## 1. Pointwise Multipliers II (Prop 18.10, `mult`) — DONE (2026-06-12)

File: `BesovSpacesGoodGrid/GoodGrid/Multipliers/Bp1overpinftyisMultiplier.lean`.
The main theorem `souzaPointwiseMultipliersII` is fully proved (no `sorry`),
including:

- [x] `exists_mult_product_representation` (the `u₁ + u₂` construction),
      via the block-form core `exists_mult_product_blocks`: level `ℓ^p`
      aggregation with single-ancestor counting, discrete Young convolution
      bound (`geometric_conv_rpow_summable_and_tsum_le`), `L^p` convergence
      of the block series (`formalBlockSeq_hasRepresentation`), and the
      exact truncated-product identity passed to the limit along
      a.e.-convergent subsequences (no `compa1` needed).
- [x] `exists_fouRepresentation` (input from Cor 15.2 `fou` + Prop 17.1
      `boup`.B via the Dirac-approximation machinery).
- [x] Remark `pos3`: positive version of `mult`
      (`souzaPointwiseMultipliersIIPositive`, representation form
      `exists_mult_product_representation_pos`); the tower bound is derived
      from positivity (`ancestorCoeffSum_norm_le_essBound_of_positive`).

## 2. Proposition 17.1 (`boup`, Dirac approximations)

The special case needed for `exists_fouRepresentation` (tower sums of the
standard representation are cell averages of `g`, claims A/B) is proved in
`DiracApproximations.lean`; the full distributional statement of Prop 17.1
is not formalized.  Infrastructure:
`Distribution.lean` (test functions/distributions) and
`AlternativeRepresentationsAndNorms` (standard representation).

## 3. Regular domains (`cf`) — DONE (2026-06-14)

File: `BesovSpacesGoodGrid/GoodGrid/RegularDomains.lean`.

Current target:

- [x] Finish `regularFamily_restriction_representations`.

Follow-up file:

- [ ] Finish the three remaining proposed regular-domain non-Archimedean
      statements in
      `BesovSpacesGoodGrid/GoodGrid/RegularDomainsNonArchimedean.lean`.
      The uniform regular-family non-positive theorem is now proved; the
      remaining `sorry`s are the non-uniform theorem, the positive non-uniform
      theorem, and the positive uniform theorem.

Already done for this target:

- [x] `RegularFamily.cost_summable` is derived from the structure, so the
      structure no longer needs a separate summability field.
- [x] The theorem statement includes the paper's bounded-input hypothesis:
      `g` is controlled a.e. by an `L∞` bound `M`, and the target estimate
      uses the natural bounded Besov gauge
      `Norm_Costpq xg + M`.
- [x] Product-construction internals in `QuasiAlgebra.lean` expose the block
      identity
      `R.block k = LevelBlock.add ... (quasiU1Block ...) (quasiU2Block ...)`,
      so support and aggregate estimates can be proved in `RegularDomains`.
- [x] Canonical regular-family indicator blocks are localized:
      nonzero coefficients of `u₁`, `u₂`, and their product live inside the
      corresponding active domain.
- [x] The strict ancestor tower of the canonical indicator representation is
      bounded by `1`.
- [x] Aggregate level estimates are proved for `u₁`, `u₂`, and the product
      block `u₁ + u₂`.
- [x] For each active `i ∈ Λ`, `regularFamilyIndicator_besov_representation`
      constructs a finite-cost Souza representation of `1_{Ω i}` with the
      canonical indicator blocks.
- [x] The non-uniform overlap hypothesis has been reformulated in the bounded
      Besov gauge:
      `|Θ i| * (1 + regularDomainIndicatorCost Ω_i)` for domains meeting an
      active source cell.
- [x] Pointwise/a.e. bounds are proved for both uniform regular families and
      non-uniform regular domains:
      the weighted indicator product series has the expected `HasSum` and
      satisfies `‖∑ Θ_i 1_{Ω_i} f‖ ≤ N ‖f‖` and `≤ N M` a.e.
- [x] The finite uniform non-Archimedean core and infinite compactness passage
      are in place for regular families, including support transfer.
- [x] The uniform non-positive regular-family theorem
      `regularFamily_nonArchimedean_indicator_multipliers` is proved with the
      bounded-gauge estimate
      `pqCost S + ‖h‖∞ ≤ Cna * N * (pqCost R + M)`.
- [x] Positive product-block infrastructure is checked: positive input
      representations make the weighted and strict ancestor towers
      nonnegative real scalars, and the two product halves `quasiU1Block` and
      `quasiU2Block` are Souza-positive.

Remaining proof steps for the follow-up file:

- [ ] Prove the positive finite/infinite assembly for the uniform regular-family
      theorem.  The next local obstacle is the final `u₁ + u₂` product
      assembly: the generic `WeakGridSpace.LevelBlock.add` is not by itself a
      positive-cone constructor in zero-coefficient cells, so the likely route
      is canonicalization after assembling the two positive product halves.
- [ ] Prove the non-uniform representation assembly using the individual
      `regularDomainIndicatorCost` overlap hypothesis.  The pointwise bounds
      are done; what remains is the finite/infinite representation construction
      for arbitrary regular domains whose costs are summed over domains meeting
      each active source cell.
- [ ] Use the non-uniform assembly plus nonnegative weights to finish the
      positive non-uniform variant.

Completed proof steps:

- [x] Assembled, for each active `i`, the quasi-product representation of
      `1_{Ω i} * g` using the canonical indicator representation and the
      weighted representation of `g`.
- [x] Converted the proved level-by-level aggregate product estimate into the
      mixed `regularFamilyRestrictionCost` bound.
- [x] Handled the two cost cases:
      `q = ∞` via supremum control, and `q < ∞` via the geometric tail and
      finite `q` summability of the chosen representation of `g`.
- [x] Removed the final `sorry` and rechecked with
      `lake env lean BesovSpacesGoodGrid/GoodGrid/RegularDomains.lean`.

## 4. Other targets from `paper-map.md`

- [ ] Wrap-up equivalence theorem for Theorem 15.1 (package the proved
      inequality cycle) + the `L¹` functional of Cor 15.2.
- [ ] Section 16 examples: Holder atom family (11B) + Prop 16.2; bounded
      variation atoms + Prop 16.3 (apply
      `atoms_between_souza_atoms_and_besov_atoms`).
- [x] Section 19 (quasialgebra, Prop 19.1 `mult33`) — DONE (2026-06-12),
      see `GoodGrid/QuasiAlgebra.lean` and `status.md`.
- [ ] Sections 20–21 (`B^{1-s} = B^s_{1,1}`, left compositions) — after
      the above.

## Possible cleanups (low priority)

- [ ] Linter warnings across the multiplier files (`simpa`→`simp`, unused
      `simp` args, deprecated `push_neg`).
- [ ] Corollary 23er: sharpen the level-lowering constant from `#𝒫^t` to a
      local geometric bound (`n ≤ λ₁^{-t}` per cell), if ever needed.
