import UnbalancedHaarWavelet.GridDefinition
import UnbalancedHaarWavelet.HaarWaveletsDefinition
import UnbalancedHaarWavelet.HaarWaveletsLinearCombinations
import UnbalancedHaarWavelet.HaarWaveletsOrthogonality
import UnbalancedHaarWavelet.HaarWaveletsDefinition
import UnbalancedHaarWavelet.HaarWaveletsInducedBinaryGrid
import UnbalancedHaarWavelet.HaarWavelets_def_Martingale
import BesovSpacesGoodGrid.GoodGridDefinition

namespace UnbalancedHaarWavelet

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/--
The indicator simple function of a partition atom `A` at level `m` of a good
grid. It is equal to `1` on `A` and to `0` outside `A`.
-/
noncomputable def atomIndicator
    (S : GoodGrid (α := α)) (m : ℕ) (A : Set α)
    (hA : A ∈ S.grid.partitions m) : SimpleFunc α ℝ :=
  SimpleFunc.piecewise A (S.grid.measurable m A hA)
    (SimpleFunc.const α (1 : ℝ))
    (SimpleFunc.const α (0 : ℝ))

/--
The set of all indicator simple functions attached to partition atoms of the
good grid, at all levels.
-/
def atomIndicators (S : GoodGrid (α := α)) : Set (SimpleFunc α ℝ) :=
  { f |
    ∃ (m : ℕ) (A : Set α) (hA : A ∈ S.grid.partitions m),
      f = atomIndicator S m A hA }

/--
The space of test functions associated to a good grid: the real submodule of
`SimpleFunc α ℝ` spanned by the indicators of all partition atoms.
-/
def TestFunctions (S : GoodGrid (α := α)) : Submodule ℝ (SimpleFunc α ℝ) :=
  Submodule.span ℝ (atomIndicators S)

/--
Distributions on a good grid are defined as real-linear functionals on the
space of test functions.
-/
def Distributions (S : GoodGrid (α := α)) : Type _ :=
  Module.Dual ℝ (TestFunctions S)

end UnbalancedHaarWavelet
