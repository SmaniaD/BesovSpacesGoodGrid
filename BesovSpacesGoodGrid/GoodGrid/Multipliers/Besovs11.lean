import BesovSpacesGoodGrid.GoodGrid.Multipliers.Definition

/-!
# Endpoint Souza multiplier theorem at p = q = 1

This file contains the special endpoint comparison between pointwise
multipliers and the Souza atom `selfs` tests.
-/

open scoped ENNReal Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
For Souza atoms on a good grid, the endpoint `selfs` class is contained in the
pointwise multiplier class.

This is the converse direction of the multiplier theorem at `p = q = 1`.
-/
theorem souzaPointwiseMultiplier_of_souzaPointwiseSelfsClass_one_one
    (G : GoodGridSpace (α := α)) (s : ℝ)
    (hs : 0 < s) {m : α → ℂ}
    (hm : SouzaPointwiseSelfsClass G s (1 : ℝ≥0∞) (1 : ℝ≥0∞)
      hs le_rfl ENNReal.one_ne_top m) :
    SouzaPointwiseMultiplier G s (1 : ℝ≥0∞) (1 : ℝ≥0∞)
      hs le_rfl ENNReal.one_ne_top m := by
  classical
  let A := souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top
  exact WeakGridSpace.isPointwiseMultiplier_of_pointwiseSelfsClass_one_one
    (G := G.toWeakGridSpace) (s := s) (u := ∞) (A := A) (m := m)
    hm
    (souza_assumptionG2 G s (1 : ℝ≥0∞) (1 : ℝ≥0∞)
      hs le_rfl ENNReal.one_ne_top)
    (souza_assumptionA5 G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)

/--
Endpoint Souza multiplier theorem: for `p = q = 1`, pointwise multipliers are
exactly the functions satisfying the Souza atom `selfs` tests.
-/
theorem souzaPointwiseMultiplier_iff_souzaPointwiseSelfsClass_one_one
    (G : GoodGridSpace (α := α)) (s : ℝ)
    (hs : 0 < s) {m : α → ℂ} :
    SouzaPointwiseMultiplier G s (1 : ℝ≥0∞) (1 : ℝ≥0∞)
      hs le_rfl ENNReal.one_ne_top m ↔
    SouzaPointwiseSelfsClass G s (1 : ℝ≥0∞) (1 : ℝ≥0∞)
      hs le_rfl ENNReal.one_ne_top m := by
  exact WeakGridSpace.isPointwiseMultiplier_iff_pointwiseSelfsClass_one_one
    (G := G.toWeakGridSpace) (s := s) (u := ∞)
    (A := souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
    (m := m)
    (souza_assumptionG2 G s (1 : ℝ≥0∞) (1 : ℝ≥0∞)
      hs le_rfl ENNReal.one_ne_top)
    (souza_assumptionA5 G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)

end

end GoodGridSpace
