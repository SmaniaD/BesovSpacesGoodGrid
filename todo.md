# TODO

Pending formalization work, in rough priority order.  See `status.md` for
what is already done and `paper-map.md` for the paper-wide picture.

## 1. Finish Pointwise Multipliers II (Prop 18.10, `mult`)

File: `BesovSpacesGoodGrid/GoodGrid/Multipliers/Bp1overpinftyisMultiplier.lean`.
The main theorem `souzaPointwiseMultipliersII` is proved modulo two `sorry`s.

- [ ] `exists_mult_product_representation` (the `u₁ + u₂` construction):
  - [x] `u₂` block + levelwise cost bound (`multU2Block`,
        `multU2Block_levelCoeffPower_le`).
  - [x] `u₁` block + pointwise coefficient bound (`multU1Block`,
        `multU1Block_coeff_norm_le`).
  - [ ] Aggregate the `u₁` pointwise bound into the level `ℓ^p` estimate:
        Minkowski over `k < j` plus single-ancestor counting
        (the inner sum over `Q ⊇ J` at level `k` has one nonzero term).
  - [ ] `(p,q)`-cost convolution bound for `u₁` (discrete Young with the
        geometric kernel `λ₂^{(j−k)(1/p−s)}`; cf. `cCoefficientInt` /
        `transmutationKernelZ` machinery in `WeakGrid/BesovishSpaces.lean`).
  - [ ] `hasSum` of the `u₁`/`u₂` block series in `L^p` (geometric level
        weights, in the spirit of Prop 6.1 `lp`).
  - [ ] Identity `f_{k₀}·g_{k₀} = (u₁ + u₂)-partial sums` (exact atom algebra
        `a_Q·b_J`), then the `L¹` limit via
        `representation_limit_strong_existence` (Cor `compa1`).
- [ ] `exists_fouRepresentation` (input from Cor 15.2 `fou` + Prop 17.1
      `boup`.B): canonical-atom representation of `g` with `(p,∞)`-cost
      `≤ Cfou·|g|_{B^{1/p}_{p,∞}}` and ancestor-tower sums `≤ ‖g‖_∞`.
      Blocked on formalizing Prop 17.1 (`boup`) — see item 2.
- [ ] Remark `pos3`: positive version of `mult` (replace `B^a_{p,b}` by
      `B^{a+}_{p,b}` everywhere).

## 2. Proposition 17.1 (`boup`, Dirac approximations)

Not started.  Needed for `exists_fouRepresentation` (tower sums of the
standard representation are cell averages of `g`).  Infrastructure:
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
