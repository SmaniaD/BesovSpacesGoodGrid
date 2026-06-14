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

## 3. Regular domains (`cf`) — in progress (2026-06-14)

File: `BesovSpacesGoodGrid/GoodGrid/RegularDomains.lean`.

Current target:

- [ ] Finish `regularFamily_restriction_representations`.

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

Remaining proof steps:

- [ ] Assemble, for each active `i`, the quasi-product representation of
      `1_{Ω i} * g` using the canonical indicator representation and the
      weighted representation of `g`.
- [ ] Convert the proved level-by-level aggregate product estimate into the
      mixed `regularFamilyRestrictionCost` bound.
- [ ] Handle the two cost cases separately:
      `q = ∞` via supremum control, and `q < ∞` via the geometric tail and
      the finite `q` summability of the chosen representation of `g`.
- [ ] Remove the final `sorry` and recheck with
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
