import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Defines weak grids.

Here a weak grid is a sequence of finite families of measurable sets with
positive measure, not an extension of the `UnbalancedHaarWavelet.Grid` or
`GoodGrid` structures.
-/


variable {α : Type*} [MeasurableSpace α]

namespace WeakGridSpace

open scoped BigOperators

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

namespace WeakGrid

omit [MeasurableSpace α] in
theorem overlapFinset_mem_comm (P : Finset (Set α)) {Q R : Set α} (hQ : Q ∈ P) :
    R ∈ overlapFinset P Q ↔ R ∈ P ∧ Q ∈ overlapFinset P R := by
  classical
  simp [overlapFinset, hQ, Set.inter_comm]

/--
Double-counting estimate for the same-level overlap relation.

Each fixed cell appears in at most `Cmult1` overlap neighborhoods, by symmetry
of nonempty intersection and `overlap_card_le`.
-/
theorem overlap_double_sum_le (W : WeakGrid (α := α)) (k : ℕ)
    (f : Set α → ℝ) (hf_nonneg : ∀ Q ∈ W.partitions k, 0 ≤ f Q) :
    (W.partitions k).sum
        (fun Q => (overlapFinset (W.partitions k) Q).sum fun P => f P) ≤
      (W.Cmult1 : ℝ) * (W.partitions k).sum f := by
  classical
  let S := W.partitions k
  have hpoint :
      ∀ P ∈ S,
        (S.filter (fun Q => (P ∩ Q).Nonempty)).sum (fun _ => f P)
          ≤ (W.Cmult1 : ℝ) * f P := by
    intro P hP
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard :
        (S.filter (fun Q => (P ∩ Q).Nonempty)).card ≤ W.Cmult1 := by
      simpa [S, overlapFinset, Set.inter_comm] using W.overlap_card_le k P hP
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard)
      (hf_nonneg P hP)
  calc
    (W.partitions k).sum
        (fun Q => (overlapFinset (W.partitions k) Q).sum fun P => f P)
        = S.sum (fun Q => (S.filter (fun P => (P ∩ Q).Nonempty)).sum fun P => f P) := by
          simp [S, overlapFinset]
    _ = S.sum (fun P => (S.filter (fun Q => (P ∩ Q).Nonempty)).sum fun _ => f P) := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
    _ ≤ S.sum (fun P => (W.Cmult1 : ℝ) * f P) :=
          Finset.sum_le_sum hpoint
    _ = (W.Cmult1 : ℝ) * (W.partitions k).sum f := by
          simp [S, Finset.mul_sum]

end WeakGrid

end WeakGridSpace
