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
canonical Souza atom `a_Q`, with `Q.level >= t`, into the Souza Besov space with
Besov seminorm at most `C`.  This is the bound-set formulation of
`sup_{Q.level >= t} |m a_Q|_{B^s_{p,q}} <= C`.
-/
def SouzaPointwiseSelfsTailBound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (t : ℕ) (m : α → ℂ) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ Q : GoodGridCell G,
      t ≤ Q.level →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun x => m x * canonicalSouzaAtom G s p Q x)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q y ≤ C

/--
The set of all bounds for the level-tail Souza `selfs` tests.
-/
def souzaPointwiseSelfsTailBoundSet
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (t : ℕ) (m : α → ℂ) : Set ℝ :=
  { C | SouzaPointwiseSelfsTailBound G s p q hs hp hp_top t m C }

/--
The level-tail Souza `selfs` seminorm.

Mathematically this is
`sup_{Q.level >= t} |m a_Q|_{B^s_{p,q}}`, where `a_Q` is the canonical Souza
atom on `Q`.  As with `pointwiseSelfsNorm`, we define it as the infimum of all
valid uniform bounds, which is more convenient in Lean when products are
represented by existential `Lp` representatives.
-/
noncomputable def souzaPointwiseSelfsTailNorm
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (t : ℕ) (m : α → ℂ) : ℝ :=
  sInf (souzaPointwiseSelfsTailBoundSet G s p q hs hp hp_top t m)

end

end GoodGridSpace
