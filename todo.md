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

## 3. Other targets from `paper-map.md`

- [ ] Wrap-up equivalence theorem for Theorem 15.1 (package the proved
      inequality cycle) + the `L¹` functional of Cor 15.2.
- [ ] Section 16 examples: Holder atom family (11B) + Prop 16.2; bounded
      variation atoms + Prop 16.3 (apply
      `atoms_between_souza_atoms_and_besov_atoms`).
- [ ] Sections 19–21 (quasialgebra, `B^{1-s} = B^s_{1,1}`, left
      compositions) — after the above.

## Possible cleanups (low priority)

- [ ] Linter warnings across the multiplier files (`simpa`→`simp`, unused
      `simp` args, deprecated `push_neg`).
- [ ] Corollary 23er: sharpen the level-lowering constant from `#𝒫^t` to a
      local geometric bound (`n ≤ λ₁^{-t}` per cell), if ever needed.
