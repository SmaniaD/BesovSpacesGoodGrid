import BesovSpacesGoodGrid.GoodGrid.Multipliers.NonArchimedeanProperty

/-!
# Positive-cone non-Archimedean multiplier theorem

This file proves the positive-cone version of the non-Archimedean multiplier
estimate.  The key additional structure compared to the non-positive version is
that the source representation `R` uses canonical Souza atoms (i.e. is a
`SouzaPositiveRepresentation`), and the multipliers satisfy a
`SouzaPositivePointwiseSelfsTailBound` that controls products with those
canonical atoms. The output representation inherits the positivity structure.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/-!
## Auxiliary lemmas about the positive tail selfs sum

These use `nonArchimedeanRelevantPositiveTailSelfsSum` which is already defined
in `NonArchimedeanProperty.lean`.
-/

private theorem nonArchimedeanRelevantPositiveTailSelfsSum_nonneg
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    0 ≤ nonArchimedeanRelevantPositiveTailSelfsSum
      G β p qtilde hβ hp hp_top Λ t g Q := by
  classical
  unfold nonArchimedeanRelevantPositiveTailSelfsSum
  refine Finset.sum_nonneg ?_
  intro i _
  by_cases hmeet : goodGridLevelCellMeetsSupport G Q (g i)
  · simp [hmeet]
  · simp [hmeet]

private theorem nonArchimedeanRelevantPositiveTailSelfsSum_eq_zero_of_nonpos
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {N : ℝ} (hN_nonpos : N ≤ 0)
    (hQ : nonArchimedeanRelevantPositiveTailSelfsSum
      G β p qtilde hβ hp hp_top Λ t g Q ≤ ENNReal.ofReal N) :
    nonArchimedeanRelevantPositiveTailSelfsSum
      G β p qtilde hβ hp hp_top Λ t g Q = 0 := by
  have hle0 : nonArchimedeanRelevantPositiveTailSelfsSum
      G β p qtilde hβ hp hp_top Λ t g Q ≤ 0 :=
    hQ.trans (le_of_eq (ENNReal.ofReal_of_nonpos hN_nonpos))
  exact le_antisymm hle0
    (nonArchimedeanRelevantPositiveTailSelfsSum_nonneg
      G β p qtilde hβ hp hp_top Λ t g Q)

/-!
## Bridging positive tail bounds to real tail bounds

When `R` is a `SouzaPositiveRepresentation`, each active level-cell atom is the
canonical Souza s-atom.  The `SouzaPositivePointwiseSelfsTailBound` hypothesis
controls products with canonical β-atoms (obtained from the canonical s-atom via
`exists_beta_souzaAtom_of_s_souzaAtom`).  The next private lemma extracts a real
`SouzaPointwiseSelfsTailBound` from a positive one when the bound is finite.

This derivation uses `souzaBesovNorm_le_souzaPositiveNorm`: the standard Besov
norm is at most the positive gauge, so a finite positive gauge gives a finite real
bound.
-/

/--
A finite positive pointwise-selfs tail bound implies a real pointwise-selfs
tail bound with value `C.toReal`.

The proof proceeds cell by cell: `SouzaPositivePointwiseSelfsTailBound` provides
a positive Besov representative with `souzaPositiveNorm ≤ C`; the inequality
`souzaBesovNorm_le_souzaPositiveNorm` then yields `Norm_Costpq ≤ C.toReal`.
Note that this only covers the canonical atom at each cell, not all atoms.  The
full `SouzaPointwiseSelfsTailBound` (which quantifies over all atoms) cannot be
derived from the positive bound alone.  The proof of the main theorem works
around this restriction by using the fact that `R` only contains canonical atoms.
-/
private theorem SouzaPositivePointwiseSelfsTailBound_toReal_of_ne_top
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {t : ℕ} {m : α → ℂ} {C : ℝ≥0∞} (hCne : C ≠ ∞)
    (hbound : SouzaPositivePointwiseSelfsTailBound G β p qtilde hβ hp hp_top t m C) :
    ∀ Q : GoodGridCell G, t ≤ Q.level →
      ∃ y : WeakGridSpace.BesovishSpace (souzaAtomFamily G β p hβ hp hp_top) qtilde,
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun x => m x * canonicalSouzaAtom G β p Q x)
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G β p hβ hp hp_top) qtilde y ≤ C.toReal := by
  intro Q htQ
  rcases hbound Q htQ with ⟨y, hyrep, _hypos, hynorm⟩
  refine ⟨y, hyrep, ?_⟩
  have hle : ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
      (souzaAtomFamily G β p hβ hp hp_top) qtilde y) ≤ C :=
    (souzaBesovNorm_le_souzaPositiveNorm G β p qtilde hβ hp hp_top y).trans hynorm
  exact ENNReal.ofReal_le_iff_le_toReal hCne |>.mp hle


/-!
## Main theorem: positive-cone non-Archimedean estimate
-/

/--
Positive-cone non-Archimedean estimate for finite multiplier sums.

This is the positive analogue of `souzaNonArchimedeanPropertyLambdaFinite`, with
the two consequences of Remark `posrem` separated according to their true
strengths.  We only assume that the source representation `R` is **canonical**
(`SouzaCanonicalRepresentation`: all atoms are canonical Souza atoms), with
**arbitrary** complex coefficients, and that each multiplier `g i` is a
`SouzaPositiveFunction`.  Under the per-cell overlap bound `N` we obtain a single
output representation `S` of `(∑ᵢ gᵢ)·f` such that:

* `pqCost S ≤ Cgen · N · pqCost R` (the cost bound);
* **[ii]** every active cell of `S` is contained in the support of some `g i`
  (this needs only canonical atoms on `R`, **not** sign conditions on `c_Q`);
* **[i]** *if* `R` is in addition fully positive (`SouzaPositiveRepresentation`,
  i.e. canonical atoms **and** nonnegative real coefficients) then so is `S`.

The separation is essential: the output atom `d_P` is a normalised signed
combination `m_P⁻¹ ∑ c_Q s_{P,Q} b_{P,Q}`, so its canonicity (hence positivity of
`S`) requires `c_Q ≥ 0`; the support statement does not.  This mirrors the
transmutation `Claim B` (support) versus `Claim B_sharp` (positivity).

The intended proof is independent of the non-positive core: it builds positive
local transmutation data (`RepresentationWsubGandALS_pos`) from the positive
multipliers and canonical source atoms, and reads off cost / support / positivity
from `Transmutation_of_Atoms_Claim_A` / `_Claim_B` / `_Claim_B_sharp`.
-/
theorem souzaNonArchimedeanPropertyPositiveCone
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)] :
    ∃ Cgen : ℝ,
      0 ≤ Cgen ∧
      ∀ (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) (N : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
          0 ≤ N →
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) f
            (x : Lp ℂ p G.toWeakGridSpace.measure) →
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
          SouzaCanonicalRepresentation G s p hs hp hp_top R →
          (∀ i ∈ Λ,
            SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i)) →
          (∀ i ∈ Λ,
            ∃ C : ℝ≥0∞,
              SouzaPositivePointwiseSelfsTailBound
                G β p qtilde hβ hp hp_top (t i) (g i) C) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            (R.block k).coeff Q ≠ 0 →
              nonArchimedeanRelevantPositiveTailSelfsSum
                G β p qtilde hβ hp hp_top Λ t g Q ≤ ENNReal.ofReal N) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
            i ∈ Λ →
              (R.block k).coeff Q ≠ 0 →
                goodGridLevelCellMeetsSupport G Q (g i) →
                  t i ≤ k) →
          ∃ y : WeakGridSpace.BesovishSpace
              (souzaAtomFamily G s p hs hp hp_top) q,
            ∃ S : WeakGridSpace.LpGridRepresentation
                (souzaAtomFamily G s p hs hp hp_top)
                (y : Lp ℂ p G.toWeakGridSpace.measure),
              WeakGridSpace.RepresentsFunction
                (G := G.toWeakGridSpace) (p := p)
                (fun z => (∑ i ∈ Λ, g i z) * f z)
                (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
                Cgen * N *
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
              -- [ii] support: holds with only canonical atoms on `R` (no sign on `c_Q`).
              (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
                (S.block k).coeff Q ≠ 0 →
                  ∃ i ∈ Λ, Q.1 ⊆ {z | g i z ≠ 0}) ∧
              -- [i] positivity: only when `R` is fully positive (canonical + `c_Q ≥ 0`).
              (SouzaPositiveRepresentation G s p hs hp hp_top R →
                SouzaConePositiveRepresentation G s p hs hp hp_top S) :=
  souzaNonArchimedeanPropertyPositiveCone_core
    G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top

end

end GoodGridSpace
