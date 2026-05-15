import BesovSpacesGoodGrid.GoodGridDefinition
import Mathlib.MeasureTheory.Function.SimpleFunc

/-!
Test functions and distributions associated to a good grid.
-/

namespace GoodGridSpace

variable {α : Type*} [MeasurableSpace α]

/--
The indicator of a partition atom, viewed as a real-valued simple function.
-/
noncomputable def atomIndicator
    (S : GoodGrid (α := α)) (m : ℕ) (A : Set α)
    (hA : A ∈ S.grid.partitions m) : MeasureTheory.SimpleFunc α ℝ :=
  MeasureTheory.SimpleFunc.piecewise A (S.grid.measurable m A hA)
    (MeasureTheory.SimpleFunc.const α (1 : ℝ))
    (MeasureTheory.SimpleFunc.const α (0 : ℝ))

/--
The set of all indicator simple functions attached to partition atoms of the
good grid, at all levels.
-/
def atomIndicators (S : GoodGrid (α := α)) : Set (MeasureTheory.SimpleFunc α ℝ) :=
  { f |
    ∃ (m : ℕ) (A : Set α) (hA : A ∈ S.grid.partitions m),
      f = atomIndicator S m A hA }

/--
The space of test functions associated to a good grid: the real submodule of
`SimpleFunc α ℝ` spanned by the indicators of all partition atoms.
-/
def TestFunctions (S : GoodGrid (α := α)) : Submodule ℝ (MeasureTheory.SimpleFunc α ℝ) :=
  Submodule.span ℝ (atomIndicators S)

/--
Distributions on a good grid are defined as real-linear functionals on the
space of test functions.
-/
def Distributions (S : GoodGrid (α := α)) : Type _ :=
  Module.Dual ℝ (TestFunctions S)

end GoodGridSpace
