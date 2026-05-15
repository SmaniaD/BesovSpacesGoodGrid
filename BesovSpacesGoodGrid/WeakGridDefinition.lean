import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
Defines weak grids.

Here a weak grid is a sequence of finite families of measurable sets with
positive measure, not an extension of the `UnbalancedHaarWavelet.Grid` or
`GoodGrid` structures.
-/


variable {α : Type*} [MeasurableSpace α]

namespace WeakGridSpace


variable {α : Type*} [MeasurableSpace α]

/--
A finite family at level `k` gives a finite overlap neighborhood
`Ω_Q^k = {P ∈ P^k : P ∩ Q ≠ ∅}`.
-/
noncomputable def overlapFinset (P : Finset (Set α)) (Q : Set α) : Finset (Set α) :=
  by
    classical
    exact P.filter fun R => (R ∩ Q).Nonempty

/--
A weak grid is a sequence of finite families of measurable sets with positive
measure, with at least one nonempty family and uniformly bounded same-level
overlap multiplicity. The term "partition" is used in the definition, but
 the sets are not required to be disjoint or to cover the whole space.
-/
structure WeakGrid where
        /-- The measure on `α`. -/
        μ : MeasureTheory.Measure α
        /-- The measure is finite on the whole space. -/
        isFinite : MeasureTheory.IsFiniteMeasure μ
        /-- The finite family `P^k` at each level `k`. -/
        partitions : ℕ → Finset (Set α)
        /-- Every cell is measurable. -/
        measurable : ∀ k Q, Q ∈ partitions k → MeasurableSet Q
        /-- Every cell has positive measure. -/
        positive_measure : ∀ k Q, Q ∈ partitions k → 0 < μ Q
        /-- At least one level is nonempty. -/
        exists_nonempty : ∃ k, (partitions k).Nonempty
        /-- Uniform same-level overlap multiplicity bound. -/
        Cmult1 : ℕ
        /-- `# Ω_Q^k ≤ Cmult1` for every `Q ∈ P^k`. -/
        overlap_card_le :
          ∀ k Q, Q ∈ partitions k → (overlapFinset (partitions k) Q).card ≤ Cmult1


/--
Ambient object used in the project: a measurable space with a fixed Weak grid.
-/
structure WeakGridSpace where
        grid : WeakGrid (α := α)

/-- The measure attached to a `WeakGridSpace`. -/
def WeakGridSpace.measure (G : WeakGridSpace (α := α)) : MeasureTheory.Measure α :=
        G.grid.μ

end WeakGridSpace
