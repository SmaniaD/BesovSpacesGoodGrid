import BesovSpacesGoodGrid.WeakGrid.Multipliers
import BesovSpacesGoodGrid.GoodGrid.BesovSpace

/-!
# Souza multiplier definitions on good grids

This file contains the basic pointwise multiplier and `selfs` classes for
Souza Besov spaces on good grids.  The analytic multiplier theorems live in the
neighboring `Besovspq` and `Besovs11` files.
-/

open scoped ENNReal Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
A quantitative pointwise multiplier bound for the Souza Besov space associated
to a good grid.
-/
abbrev SouzaPointwiseMultiplierBound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (m : α → ℂ) (C : ℝ) : Prop :=
  WeakGridSpace.PointwiseMultiplierBound
    (A := souzaAtomFamily G s p hs hp hp_top) q m C

/--
Pointwise multipliers of the Souza Besov space associated to a good grid.
-/
abbrev SouzaPointwiseMultiplier
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (m : α → ℂ) : Prop :=
  WeakGridSpace.IsPointwiseMultiplier
    (A := souzaAtomFamily G s p hs hp hp_top) q m

/--
The class of all pointwise multipliers of the Souza Besov space associated to a
good grid.
-/
abbrev SouzaPointwiseMultiplierClass
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    Set (α → ℂ) :=
  WeakGridSpace.PointwiseMultiplierClass
    (A := souzaAtomFamily G s p hs hp hp_top) q

/--
The `selfs` atom-test class for the Souza Besov space on a good grid.
-/
abbrev SouzaPointwiseSelfsClass
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (m : α → ℂ) : Prop :=
  WeakGridSpace.PointwiseSelfsClass
    (A := souzaAtomFamily G s p hs hp hp_top) q m

/--
The `selfs` seminorm specialized to Souza atoms on a good grid.
-/
noncomputable abbrev souzaPointwiseSelfsNorm
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (m : α → ℂ) : ℝ :=
  WeakGridSpace.pointwiseSelfsNorm
    (A := souzaAtomFamily G s p hs hp hp_top) q m

/--
A quantitative bound for the level-tail Souza `selfs` tests.

For a fixed level cutoff `t`, this says that multiplication by `m` sends every
Souza atom on a cell `Q`, with `Q.level >= t`, into the Souza Besov space with
Besov seminorm at most `C`.  This is the bound-set formulation of the
tail `selfs` test, where the supremum is taken over all Souza atoms in the
allowed tail levels.
-/
def SouzaPointwiseSelfsTailBound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (t : ℕ) (m : α → ℂ) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ Q : GoodGridCell G,
      t ≤ Q.level →
        ∀ φ : ((souzaAtomFamily G s p hs hp hp_top).localSpace Q.toWeakGridCell).carrier,
        φ ∈ (souzaAtomFamily G s p hs hp hp_top).atoms Q.toWeakGridCell →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun x => m x *
              (souzaAtomFamily G s p hs hp hp_top).toFunction Q.toWeakGridCell φ x)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q y ≤ C

/--
The level-tail Souza `selfs` class.  A function belongs to this class when the
tail atom tests from level `t` onward admit some finite real bound.
-/
def SouzaPointwiseSelfsTailClass
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (t : ℕ) (m : α → ℂ) : Prop :=
  ∃ C : ℝ, SouzaPointwiseSelfsTailBound G s p q hs hp hp_top t m C

/--
The set of all bounds for the level-tail Souza `selfs` tests over all Souza
atoms in the allowed tail levels.
-/
def souzaPointwiseSelfsTailBoundSet
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (t : ℕ) (m : α → ℂ) : Set ℝ :=
  { C | SouzaPointwiseSelfsTailBound G s p q hs hp hp_top t m C }

/-- The level-tail Souza `selfs` bound set is bounded below by zero. -/
theorem souzaPointwiseSelfsTailBoundSet_bddBelow
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (t : ℕ) (m : α → ℂ) :
    BddBelow (souzaPointwiseSelfsTailBoundSet G s p q hs hp hp_top t m) := by
  refine ⟨0, ?_⟩
  intro C hC
  exact hC.1

/--
The level-tail Souza `selfs` seminorm.

Mathematically this is
`sup |m a_Q|_{B^s_{p,q}}`, where `Q.level >= t` and `a_Q` ranges over all Souza
atoms on `Q`.  As with `pointwiseSelfsNorm`, we define it as the infimum of all
valid uniform bounds, which is more convenient in Lean when products are
represented by existential `Lp` representatives.
-/
noncomputable def souzaPointwiseSelfsTailNorm
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (t : ℕ) (m : α → ℂ) : ℝ :=
  sInf (souzaPointwiseSelfsTailBoundSet G s p q hs hp hp_top t m)

/--
Every concrete level-tail `selfs` bound is an upper bound for the tail seminorm.
-/
theorem souzaPointwiseSelfsTailNorm_le_of_bound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {t : ℕ} {m : α → ℂ} {C : ℝ}
    (hC : SouzaPointwiseSelfsTailBound G s p q hs hp hp_top t m C) :
    souzaPointwiseSelfsTailNorm G s p q hs hp hp_top t m ≤ C := by
  exact csInf_le
    (souzaPointwiseSelfsTailBoundSet_bddBelow G s p q hs hp hp_top t m) hC

/--
If at least one level-tail `selfs` bound exists, then the tail seminorm can be
approximated from above by a concrete bound.
-/
theorem exists_souzaPointwiseSelfsTailBound_lt_norm_add
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {t : ℕ} {m : α → ℂ}
    (hNonempty : ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G s p q hs hp hp_top t m C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G s p q hs hp hp_top t m C ∧
        C < souzaPointwiseSelfsTailNorm G s p q hs hp hp_top t m + ε := by
  have hset_nonempty :
      (souzaPointwiseSelfsTailBoundSet G s p q hs hp hp_top t m).Nonempty := by
    rcases hNonempty with ⟨C, hC⟩
    exact ⟨C, hC⟩
  have hlt :
      sInf (souzaPointwiseSelfsTailBoundSet G s p q hs hp hp_top t m) <
        sInf (souzaPointwiseSelfsTailBoundSet G s p q hs hp hp_top t m) + ε :=
    lt_add_of_pos_right _ hε
  rcases exists_lt_of_csInf_lt hset_nonempty hlt with ⟨C, hCmem, hClt⟩
  exact ⟨C, hCmem, by
    simpa [souzaPointwiseSelfsTailNorm] using hClt⟩

end

end GoodGridSpace
