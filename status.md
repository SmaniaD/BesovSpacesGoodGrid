# Direct `L^p` Besov Refactor Status

This document is a handoff note for continuing the `ConvexLp` branch work on
the local-Banach-free, direct `L^p` version of the repository.

## Objective

The goal is to reformulate the Besov/Besov-ish construction so that atoms are
defined directly as subsets of the ambient space

```lean
MeasureTheory.Lp ℂ p G.measure
```

rather than as elements of local Banach spaces attached to grid cells.

In the direct version, an atom over a cell `Q` is an ambient `L^p` vector whose
support is contained in `Q` modulo null sets, and whose `L^p` norm satisfies
the appropriate size bound.  This should eventually replace or parallel the old
local-Banach-space API.

The current branch is:

```text
ConvexLp
```

## Main Direct Files

The direct API currently lives in these files:

```text
BesovSpacesGoodGrid/WeakGridDirectAtoms.lean
BesovSpacesGoodGrid/WeakGridDirectBesovishSpaces.lean
BesovSpacesGoodGrid/WeakGridDirectCompletenessBesovishSpaces.lean
BesovSpacesGoodGrid/GoodGridDirectBesovSpace.lean
```

The root import file `BesovSpacesGoodGrid.lean` imports the direct modules.

## What Has Been Done

### Direct Atom API

`WeakGridDirectAtoms.lean` defines:

```lean
LpSupportedOn
LpAtomFamily
IsLpSizeAtom
lpSizeAtomFamily
```

`LpAtomFamily` is the direct replacement for the old `AtomFamily` local-space
data.  Its atoms are sets:

```lean
WeakGridCell G → Set (MeasureTheory.Lp ℂ p G.measure)
```

The support condition is:

```lean
(f : α → ℂ) =ᵐ[G.measure.restrict Q.cellᶜ] 0
```

This means the `L^p` class is zero outside `Q`, modulo the restricted measure.

### Direct Besov-ish Space API

`WeakGridDirectBesovishSpaces.lean` defines:

```lean
LpLevelBlock
DirectLpGridRepresentation
DirectLpMemBesovish
DirectLpMemBesovishCoeffCost
DirectLpBesovishSpace
LpSizeBesovishSpace
```

It also proves the algebraic structure:

```lean
DirectLpBesovishSpace : Submodule ℂ (Lp ℂ p G.measure)
```

and defines the direct cost gauge:

```lean
Norm_Costpq
```

with the expected basic properties:

```lean
Norm_Costpq_nonneg
Norm_Costpq_le_cost
exists_cost_lt_Norm_Costpq_add
Norm_Costpq_add_le
Norm_Costpq_smul_le
Norm_Costpq_smul_eq
```

### Direct Souza/GoodGrid API

`GoodGridDirectBesovSpace.lean` defines direct Souza atoms and direct Souza
Besov-ish spaces:

```lean
directSouzaOneAtom
IsDirectSouzaAtom
directSouzaAtomFamily
DirectSouzaBesovishSpace
DirectLpSizeBesovishSpace
```

The direct Souza atoms are ambient `L^p` vectors of the form a scalar multiple
of the normalized cell indicator.

### Direct `L^p` Embedding

`WeakGridDirectCompletenessBesovishSpaces.lean` now proves the direct ambient
`L^p` embedding.

Important definitions and theorems:

```lean
directLevelLpWeight
direct_weighted_coeff_summable
direct_weighted_sum_le_cCoefficient_mul_pqCost
lp_embedding_of_representation
costNormControlsLp_of_cCoefficientFinite
```

The main representation-level estimate is:

```lean
lp_embedding_of_representation
```

It proves, for all `1 ≤ q ≤ ∞`, under the direct coefficient condition,

```lean
‖g‖ ≤
  LpGridRepresentation.cCoefficient p q
    (fun k => (directLevelLpWeight G s p k) ^ p.toReal)
  * DirectLpGridRepresentation.pqCost (q := q) R
```

The space-level control is:

```lean
costNormControlsLp_of_cCoefficientFinite
```

This proves:

```lean
CostNormControlsLp (A := A) q
```

assuming:

```lean
LpGridRepresentation.cCoefficientFinite p q
  (fun k => (directLevelLpWeight G s p k) ^ p.toReal)
```

The older special case `q = ∞` is also present:

```lean
lp_embedding_top_of_representation
costNormControlsLp_top
```

### Direct Normed Group and Completeness Criterion

`WeakGridDirectCompletenessBesovishSpaces.lean` defines:

```lean
CostNormControlsLp
costNormedAddCommGroup
ClosedCostBallStrongSeqCompact
```

and proves:

```lean
eq_zero_of_Norm_Costpq_eq_zero
costNormedAddCommGroup_norm
Norm_Costpq_cauchySeq_tendsto_of_closedBallStrongSeqCompact
costNorm_completeSpace_of_closedBallStrongSeqCompact
```

This means the direct cost norm is a genuine normed additive group whenever the
cost controls the ambient `L^p` norm, and the direct space is complete assuming
closed cost balls are strongly sequentially compact in ambient `L^p`.

### Port of the Old `A5/G2` Compactness Machinery

Work has begun on porting the old theorem

```lean
closed_Norm_Costpq_ball_strongly_seqCompact
```

to the direct API.

The direct assumptions now introduced are:

```lean
DirectAssumptionA5
DirectAssumptionG2
```

`DirectAssumptionA5` says each direct atom set is sequentially compact in the
ambient strong `L^p` topology:

```lean
∀ Q : WeakGridCell G, IsSeqCompact (A.atoms Q)
```

`DirectAssumptionG2` currently packages:

```lean
LpGridRepresentation.cCoefficientFinite p q
  (fun k => (directLevelLpWeight G s p k) ^ p.toReal)

∀ N, LpGridRepresentation.cCoefficientFinite p q
  (directTailCoefficientWeight G s p N)

Tendsto (fun N => directTailCCoefficient G s p q N) atTop (𝓝 0)
```

The following ported components already compile:

```lean
directTailCoefficientWeight
directTailCCoefficient
directTailCoefficientWeight_nonneg
direct_weighted_sum_le_cCoefficient_mul_pqCost_of_weight
DirectCoefficientsTendsto
DirectAtomsTendstoStrong
DirectRepresentationLimitStrongHypotheses
direct_representation_limit_levelCoeffPower_tendsto
direct_representation_limit_pqCostENNReal_le
direct_pqCost_le_of_pqCostENNReal_le
direct_pqCostENNReal_le_of_finitePQCost_pqCost_le
exists_direct_subseq_coeff_tendsto_of_coord_bounded
exists_direct_subseq_atoms_tendsto_of_abstract
direct_coeff_bounded_of_uniform_pqCostENNReal_le
exists_direct_subseq_blocks_tendsto_of_uniform_pqCostENNReal
direct_tail_embedding_bound
```

These are the main ingredients needed to finish the direct compactness theorem.

## Current Verification Status

The direct completeness file checks:

```bash
lake env lean BesovSpacesGoodGrid/WeakGridDirectCompletenessBesovishSpaces.lean
```

The direct completeness module builds:

```bash
lake build BesovSpacesGoodGrid.WeakGridDirectCompletenessBesovishSpaces
```

The root import file checks:

```bash
lake env lean BesovSpacesGoodGrid.lean
```

No `sorry` has been added in the direct files:

```text
WeakGridDirectAtoms.lean
WeakGridDirectBesovishSpaces.lean
WeakGridDirectCompletenessBesovishSpaces.lean
GoodGridDirectBesovSpace.lean
```

There are pre-existing unrelated `sorry`s in older non-direct files.

## What Still Needs To Be Done

### 1. Finish the Direct Closed-Ball Compactness Theorem

The main missing theorem is the direct analogue of the old:

```lean
closed_Norm_Costpq_ball_strongly_seqCompact
```

The desired direct statement should prove:

```lean
ClosedCostBallStrongSeqCompact A q
```

from:

```lean
DirectAssumptionA5 A
DirectAssumptionG2 G s p q
```

The remaining work is to assemble the already ported ingredients:

1. Choose almost-minimizing direct representations for a sequence in a closed
   `Norm_Costpq` ball.
2. Convert their cost bounds into uniform extended-cost bounds.
3. Use
   ```lean
   exists_direct_subseq_blocks_tendsto_of_uniform_pqCostENNReal
   ```
   to extract convergent coefficients and atoms.
4. Build the formal limiting block sequence.
5. Prove that the formal block sequence is summable in ambient `L^p`, using
   ```lean
   direct_tail_embedding_bound
   ```
   and `directTailCCoefficient → 0`.
6. Construct the limiting `DirectLpGridRepresentation`.
7. Prove finite cost and the cost bound for the limit.
8. Prove strong `L^p` convergence of the subsequence to the limit.
9. Conclude `ClosedCostBallStrongSeqCompact A q`.

### 2. Use Compactness To Prove Direct Completeness Under `DirectA5/G2`

Once the direct closed-ball compactness theorem is proved, combine it with:

```lean
costNormControlsLp_of_cCoefficientFinite
costNorm_completeSpace_of_closedBallStrongSeqCompact
```

to get a final theorem of the form:

```lean
direct_costNorm_completeSpace_of_A5_G2
```

or similar.

### 3. Specialize `DirectAssumptionA5/G2` To Direct Souza Atoms

For the direct Souza atom family:

```lean
directSouzaAtomFamily
```

we still need concrete proofs of:

```lean
DirectAssumptionA5 (directSouzaAtomFamily ...)
DirectAssumptionG2 G s p q
```

The `A5` proof should be much simpler than the old local-space version, because
direct Souza atoms are essentially scalar multiples of one fixed normalized
indicator per cell.  The compactness problem should reduce to compactness of a
closed scalar disk.

The `G2` proof should be derived from GoodGrid geometric estimates for the
direct level weights and their tails.

### 4. Package Final User-Facing Direct Theorems

After compactness and completeness are closed, add convenient public theorems
for the direct Souza space, for example:

```lean
directSouza_costNormControlsLp
directSouza_closedCostBallStrongSeqCompact
directSouza_costNorm_completeSpace
```

The goal is for downstream files to use the direct API without unfolding
`LpAtomFamily`, direct weights, or compactness hypotheses manually.

## Useful Commands

Check the direct completeness file:

```bash
lake env lean BesovSpacesGoodGrid/WeakGridDirectCompletenessBesovishSpaces.lean
```

Build the direct completeness module:

```bash
lake build BesovSpacesGoodGrid.WeakGridDirectCompletenessBesovishSpaces
```

Check root imports:

```bash
lake env lean BesovSpacesGoodGrid.lean
```

Search for unfinished proofs in direct files:

```bash
rg -n "sorry" \
  BesovSpacesGoodGrid/WeakGridDirectAtoms.lean \
  BesovSpacesGoodGrid/WeakGridDirectBesovishSpaces.lean \
  BesovSpacesGoodGrid/WeakGridDirectCompletenessBesovishSpaces.lean \
  BesovSpacesGoodGrid/GoodGridDirectBesovSpace.lean
```

## Notes For The Next Session

- Do not reintroduce local Banach spaces in the direct files.
- Keep the direct files parallel to the old files, but avoid copying old local
  structures blindly.
- The old proof in `WeakGridCompletenessBesovishSpaces.lean` is the blueprint,
  especially the block beginning around the old
  `closed_Norm_Costpq_ball_strongly_seqCompact`.
- The current direct port intentionally strengthened `DirectAssumptionG2` to
  include finite tail coefficient conditions for every `N`.  This keeps the
  direct tail embedding theorem honest and avoids deriving tail finiteness
  separately during the compactness proof.
- The final missing mathematical bridge is not the embedding anymore; it is the
  construction of a summable limiting direct block sequence from the extracted
  coefficient/atom limits.

