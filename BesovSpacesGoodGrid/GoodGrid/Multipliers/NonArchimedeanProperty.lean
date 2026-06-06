import BesovSpacesGoodGrid.GoodGrid.Multipliers.Definition

/-!
# Non-Archimedean estimate for multiplier sums

This file records the non-Archimedean estimate from the multiplier section in
a form adapted to the existing atomic representation API.  The proof is left as
a separate task: the statement packages the hypotheses about level-tail
`selfs` bounds, support separation, and compatible representation levels, and
asserts the existence of a controlled Souza Besov representation of the product
with a finite sum of multipliers.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
The support of `g` meets the level cell `Q`.
-/
def goodGridLevelCellMeetsSupport
    (G : GoodGridSpace (α := α)) {k : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) (g : α → ℂ) : Prop :=
  (Q.1 ∩ {x | g x ≠ 0}).Nonempty

/--
For one active representation cell `Q`, this is the sum of the level-tail
`selfs` seminorms of precisely those multipliers whose support meets `Q`.
-/
noncomputable def nonArchimedeanRelevantTailSelfsSum
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℝ := by
  classical
  exact
    ∑ i ∈ Λ,
      if goodGridLevelCellMeetsSupport G Q (g i) then
        souzaPointwiseSelfsTailNorm G β p qtilde hβ hp hp_top (t i) (g i)
      else
        0

/--
Non-Archimedean control for a finite sum of level-tail `selfs` multipliers.

Let `β > s`.  There is a constant `Cgen` such that, whenever a finite family
`g i` has level-tail `selfs` control from levels `t i` onward, and a Souza
representation `R` of `f` satisfies the two separation hypotheses below, the
product `(∑ i in Λ, g i) * f` has a Souza representation whose coefficient
cost is bounded by `Cgen * N` times the coefficient cost of `R`.

Hypothesis `hA` is the formal version of the paper's condition A: for each
active coefficient cell, the sum of the relevant tail `selfs` seminorms is at
most `N`.  Hypothesis `hB` is condition B: every relevant active cell lies at a
level where the corresponding multiplier is already in its allowed tail.
-/
theorem souzaNonArchimedeanProperty
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
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
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) f
            (x : Lp ℂ p G.toWeakGridSpace.measure) →
          (∀ i ∈ Λ,
            ∃ C : ℝ,
              SouzaPointwiseSelfsTailBound
                G β p qtilde hβ hp hp_top (t i) (g i) C) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            (R.block k).coeff Q ≠ 0 →
              nonArchimedeanRelevantTailSelfsSum
                G β p qtilde hβ hp hp_top Λ t g Q ≤ N) →
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
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  sorry

end

end GoodGridSpace
