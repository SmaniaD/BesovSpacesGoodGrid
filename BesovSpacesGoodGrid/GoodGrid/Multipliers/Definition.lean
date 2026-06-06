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

end

end GoodGridSpace
