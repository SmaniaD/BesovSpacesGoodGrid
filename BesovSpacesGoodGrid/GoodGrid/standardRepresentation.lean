import BesovSpacesGoodGrid.GoodGrid.HaarRepresentationNorm
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import UnbalancedHaarWavelet.HaarWaveletsLinearCombinations

/-!
# Standard atomic representation on a good grid

This file records the coefficient bookkeeping behind the standard atomic
representation associated with the Haar representation.  Haar functions are the
`L²`-normalized functions from `HaarRepresentationNorm`; Souza atoms are the
canonical atoms from `BesovSpace`.

The main analytic statements from the manuscript, such as unconditional
convergence and the proof that the intermediate atoms are Souza atoms, require
local constancy facts for the Haar wavelets on the binary-refinement leaves.
Here we keep the reusable finite formulas and the `N_st` gauge.
-/

open scoped ENNReal BigOperators
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace StandardAtomicRepresentation

/--
Children of a good-grid cell at the next level.

This is the formal version of the family
`{P ∈ P^{k+1} | P ⊆ Q}`.  The underlying finite set is the
`childrenFinset` already provided by `UnbalancedHaarWavelet`; this wrapper only
repackages each child as a level cell of the weak grid induced by the good
grid.
-/
def childrenOfCell (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) :
    Finset (WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) :=
  ((HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell).attach.image fun P =>
    ⟨P.1, ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell P.1).1 P.2 |>.1⟩

/-- Membership in `childrenOfCell` is exactly membership in the grid `childrenFinset`. -/
theorem mem_childrenOfCell_iff (G : GoodGridSpace (α := α)) (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) :
    P ∈ childrenOfCell G Q ↔
      P.1 ∈ (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell := by
  classical
  constructor
  · intro hP
    rcases Finset.mem_image.1 hP with ⟨s, hs, hsP⟩
    rw [← hsP]
    exact s.2
  · intro hP
    refine Finset.mem_image.2 ?_
    refine ⟨⟨P.1, hP⟩, by simp, ?_⟩
    ext
    rfl

/-- A child level cell, repackaged as a `GoodGridCell`. -/
def childToGoodGridCell {G : GoodGridSpace (α := α)} {Q : GoodGridCell G}
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) : GoodGridCell G where
  level := Q.level + 1
  cell := P.1
  mem := P.2

/--
The finite set `S₁ ∪ S₂` attached to a Haar branch.

The branch is represented in the dependency as a pair of finite sets of cells.
-/
def branchCells {G : GoodGridSpace (α := α)} [DecidableEq (Set α)]
    {F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G)}
    {Q : GoodGridCell G}
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    Finset (Set α) :=
  b.1.1 ∪ b.1.2

/-- The predicate `P ∈ S₁ ∪ S₂` for a branch `S = (S₁, S₂)`. -/
def branchContainsCell (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    Prop :=
  P.1 ∈ branchCells (G := G) (F := F) (Q := Q) b

/--
The father coefficient `k_I^f`.

With normalized Haar functions this is
`μ(I)^(1/p - s - 1/2) d_I^f`.
-/
def fatherCoeff (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) : ℂ :=
  (((G.grid.μ Set.univ).toReal ^ (1 / p.toReal - s - 1 / 2) : ℝ) : ℂ) *
    HaarRepresentation.Coeff G F f hf .alpha

/--
The normalization constant `c₂` from the manuscript.

It is written in terms of the good-grid structural constants: `lambda2` is the
manuscript's `maior`, and `lambda1` is the manuscript's `menor`.  This constant
is used below when turning restricted Haar wavelets into Souza atoms.
-/
noncomputable def c₂ (G : GoodGridSpace (α := α)) : ℝ :=
  G.grid.lambda2 ^ ((1 : ℝ) / 2) /
      (Real.sqrt 2 * G.grid.lambda1 ^ ((3 : ℝ) / 2)) + 1

/-- The constant `c₂` is strictly positive. -/
theorem c₂_pos (G : GoodGridSpace (α := α)) : 0 < c₂ G := by
  have hlambda2_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  have hnum_nonneg : 0 ≤ G.grid.lambda2 ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg hlambda2_pos.le _
  have hden_pos :
      0 < Real.sqrt 2 * G.grid.lambda1 ^ ((3 : ℝ) / 2) := by
    exact mul_pos (Real.sqrt_pos.2 (by norm_num))
      (Real.rpow_pos_of_pos G.grid.hlambda1_pos _)
  have hfrac_nonneg :
      0 ≤ G.grid.lambda2 ^ ((1 : ℝ) / 2) /
        (Real.sqrt 2 * G.grid.lambda1 ^ ((3 : ℝ) / 2)) :=
    div_nonneg hnum_nonneg hden_pos.le
  dsimp [c₂]
  linarith

/-- The constant `c₂` is at least one. -/
theorem one_le_c₂ (G : GoodGridSpace (α := α)) : 1 ≤ c₂ G := by
  have hlambda2_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  have hnum_nonneg : 0 ≤ G.grid.lambda2 ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg hlambda2_pos.le _
  have hden_pos :
      0 < Real.sqrt 2 * G.grid.lambda1 ^ ((3 : ℝ) / 2) := by
    exact mul_pos (Real.sqrt_pos.2 (by norm_num))
      (Real.rpow_pos_of_pos G.grid.hlambda1_pos _)
  have hfrac_nonneg :
      0 ≤ G.grid.lambda2 ^ ((1 : ℝ) / 2) /
        (Real.sqrt 2 * G.grid.lambda1 ^ ((3 : ℝ) / 2)) :=
    div_nonneg hnum_nonneg hden_pos.le
  dsimp [c₂]
  linarith

/--
The atom-side coefficient `c_{S,P}^f`.

The constant `c₂` is left explicit: it is the manuscript's normalization
constant used to turn the restricted Haar wavelet into a Souza atom.
-/
def branchCellCoeff (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (c₂ : ℝ) (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) : ℂ :=
  ((c₂ * (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) *
      (G.grid.μ P.1).toReal ^ (1 / p.toReal - s) : ℝ) : ℂ) *
    HaarRepresentation.Coeff G F f hf (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))

/--
The restricted Haar atom `a_{S,P}` from the manuscript.

The formula is zero off `P` and equals a scalar multiple of `φ_S` on `P`.
Showing that this is a Souza atom uses local constancy of `φ_S` on the cells in
`S₁ ∪ S₂`; that proof is intentionally kept separate from this definition.
-/
def branchCellAtom (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (c₂ : ℝ) (p : ℝ≥0∞) (s : ℝ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    (x : α) : ℂ := by
  classical
  exact if x ∈ P.1 then
    (((G.grid.μ Q.cell).toReal ^ ((1 : ℝ) / 2) / c₂ *
        (G.grid.μ P.1).toReal ^ (s - 1 / p.toReal) : ℝ) : ℂ) *
      HaarRepresentation.normalizedFunction G F (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x
  else
    0

/-- The zero function is a Souza atom on every good-grid cell. -/
theorem zero_isSouzaAtom (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G) :
    IsSouzaAtom G s p Q (fun _ : α => 0) := by
  refine ⟨fun _ _ => rfl, 0, fun _ _ => rfl, ?_⟩
  have hnonneg :
      0 ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  simpa using hnonneg

/-- The restricted branch atom vanishes outside its child cell. -/
theorem branchCellAtom_eq_zero_of_not_mem
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (c₂ : ℝ) (p : ℝ≥0∞) (s : ℝ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    {x : α} (hx : x ∉ P.1) :
    branchCellAtom G F c₂ p s Q P b x = 0 := by
  simp [branchCellAtom, hx]

/-- A normalized Haar wavelet is zero away from the union of the two sides of its branch. -/
theorem normalizedFunction_eq_zero_of_not_mem_branchCells
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    {x : α}
    (hx : x ∉ UnbalancedHaarWavelet.branchSupport
      (branchCells (G := G) (F := F) (Q := Q) b)) :
    HaarRepresentation.normalizedFunction G F
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x = 0 := by
  classical
  have hsupport :
      UnbalancedHaarWavelet.branchSupport
          (branchCells (G := G) (F := F) (Q := Q) b) =
        UnbalancedHaarWavelet.branchSupport b.1.1 ∪
          UnbalancedHaarWavelet.branchSupport b.1.2 := by
    simp [branchCells, UnbalancedHaarWavelet.branchSupport_union]
  have hxleft :
      x ∉ UnbalancedHaarWavelet.branchSupport b.1.1 := by
    intro hxleft
    exact hx (by
      rw [hsupport]
      exact Or.inl hxleft)
  have hxright :
      x ∉ UnbalancedHaarWavelet.branchSupport b.1.2 := by
    intro hxright
    exact hx (by
      rw [hsupport]
      exact Or.inr hxright)
  simp [HaarRepresentation.normalizedFunction, HaarRepresentation.indexOfCellBranch,
    UnbalancedHaarWavelet.FullHaarSystem.function, UnbalancedHaarWavelet.HaarSystem.wavelet,
    F.toHaarSystem.haarWavelets_def, UnbalancedHaarWavelet.haarWavelet, hxleft, hxright]

/--
On a child cell carried by a branch, the corresponding normalized Haar wavelet
is constant.

The reason is exactly the branch geometry: a branch is a pair of disjoint
unions of children, and the Haar wavelet takes one constant value on the first
union and another constant value on the second union.
-/
theorem normalizedFunction_eq_on_cell_of_branchContainsCell
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    (hbP : branchContainsCell G F Q P b)
    {x y : α} (hx : x ∈ P.1) (hy : y ∈ P.1) :
    HaarRepresentation.normalizedFunction G F
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x =
      HaarRepresentation.normalizedFunction G F
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) y := by
  classical
  rw [branchContainsCell, branchCells, Finset.mem_union] at hbP
  rcases hbP with hbP | hbP
  · have hxA :
        x ∈ UnbalancedHaarWavelet.branchSupport b.1.1 :=
      UnbalancedHaarWavelet.subset_branchSupport_of_mem hbP hx
    have hyA :
        y ∈ UnbalancedHaarWavelet.branchSupport b.1.1 :=
      UnbalancedHaarWavelet.subset_branchSupport_of_mem hbP hy
    have hdisj :
        Disjoint (UnbalancedHaarWavelet.branchSupport b.1.1)
          (UnbalancedHaarWavelet.branchSupport b.1.2) :=
      F.toHaarSystem.branchSupport_components_disjoint (HaarRepresentation.GridOf G) b
    have hxB :
        x ∉ UnbalancedHaarWavelet.branchSupport b.1.2 := by
      exact fun hxB => (Set.disjoint_left.1 hdisj) hxA hxB
    have hyB :
        y ∉ UnbalancedHaarWavelet.branchSupport b.1.2 := by
      exact fun hyB => (Set.disjoint_left.1 hdisj) hyA hyB
    simp [HaarRepresentation.normalizedFunction, HaarRepresentation.indexOfCellBranch,
      UnbalancedHaarWavelet.FullHaarSystem.function, UnbalancedHaarWavelet.HaarSystem.wavelet,
      F.toHaarSystem.haarWavelets_def, UnbalancedHaarWavelet.haarWavelet,
      hxA, hxB, hyA, hyB]
  · have hxB :
        x ∈ UnbalancedHaarWavelet.branchSupport b.1.2 :=
      UnbalancedHaarWavelet.subset_branchSupport_of_mem hbP hx
    have hyB :
        y ∈ UnbalancedHaarWavelet.branchSupport b.1.2 :=
      UnbalancedHaarWavelet.subset_branchSupport_of_mem hbP hy
    have hdisj :
        Disjoint (UnbalancedHaarWavelet.branchSupport b.1.1)
          (UnbalancedHaarWavelet.branchSupport b.1.2) :=
      F.toHaarSystem.branchSupport_components_disjoint (HaarRepresentation.GridOf G) b
    have hxA :
        x ∉ UnbalancedHaarWavelet.branchSupport b.1.1 := by
      exact fun hxA => (Set.disjoint_left.1 hdisj) hxA hxB
    have hyA :
        y ∉ UnbalancedHaarWavelet.branchSupport b.1.1 := by
      exact fun hyA => (Set.disjoint_left.1 hdisj) hyA hyB
    simp [HaarRepresentation.normalizedFunction, HaarRepresentation.indexOfCellBranch,
      UnbalancedHaarWavelet.FullHaarSystem.function, UnbalancedHaarWavelet.HaarSystem.wavelet,
      F.toHaarSystem.haarWavelets_def, UnbalancedHaarWavelet.haarWavelet,
      hxA, hxB, hyA, hyB]

/-- Explicit value of the normalized Haar wavelet on a child in the left side. -/
theorem normalizedFunction_eq_left_of_mem
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    (hbP : P.1 ∈ b.1.1)
    {x : α} (hx : x ∈ P.1) :
    HaarRepresentation.normalizedFunction G F
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x =
      ((HaarRepresentation.l2NormalizationFactor G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) : ℝ) : ℂ) *
        ((1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal : ℝ) : ℂ) := by
  classical
  have hxA :
      x ∈ UnbalancedHaarWavelet.branchSupport b.1.1 :=
    UnbalancedHaarWavelet.subset_branchSupport_of_mem hbP hx
  have hdisj :
      Disjoint (UnbalancedHaarWavelet.branchSupport b.1.1)
        (UnbalancedHaarWavelet.branchSupport b.1.2) :=
    F.toHaarSystem.branchSupport_components_disjoint (HaarRepresentation.GridOf G) b
  have hxB :
      x ∉ UnbalancedHaarWavelet.branchSupport b.1.2 := by
    exact fun hxB => (Set.disjoint_left.1 hdisj) hxA hxB
  simp [HaarRepresentation.normalizedFunction, HaarRepresentation.indexOfCellBranch,
    UnbalancedHaarWavelet.FullHaarSystem.function, UnbalancedHaarWavelet.HaarSystem.wavelet,
    F.toHaarSystem.haarWavelets_def, UnbalancedHaarWavelet.haarWavelet, hxA, hxB]

/-- Explicit value of the normalized Haar wavelet on a child in the right side. -/
theorem normalizedFunction_eq_right_of_mem
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    (hbP : P.1 ∈ b.1.2)
    {x : α} (hx : x ∈ P.1) :
    HaarRepresentation.normalizedFunction G F
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x =
      -(((HaarRepresentation.l2NormalizationFactor G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) : ℝ) : ℂ) *
        ((1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal : ℝ) : ℂ)) := by
  classical
  have hxB :
      x ∈ UnbalancedHaarWavelet.branchSupport b.1.2 :=
    UnbalancedHaarWavelet.subset_branchSupport_of_mem hbP hx
  have hdisj :
      Disjoint (UnbalancedHaarWavelet.branchSupport b.1.1)
        (UnbalancedHaarWavelet.branchSupport b.1.2) :=
    F.toHaarSystem.branchSupport_components_disjoint (HaarRepresentation.GridOf G) b
  have hxA :
      x ∉ UnbalancedHaarWavelet.branchSupport b.1.1 := by
    exact fun hxA => (Set.disjoint_left.1 hdisj) hxA hxB
  simp [HaarRepresentation.normalizedFunction, HaarRepresentation.indexOfCellBranch,
    UnbalancedHaarWavelet.FullHaarSystem.function, UnbalancedHaarWavelet.HaarSystem.wavelet,
    F.toHaarSystem.haarWavelets_def, UnbalancedHaarWavelet.haarWavelet, hxA, hxB]

/-- The restricted branch atom is constant on its child cell. -/
theorem branchCellAtom_eq_on_cell_of_branchContainsCell
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (c₂ : ℝ) (p : ℝ≥0∞) (s : ℝ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    (hbP : branchContainsCell G F Q P b)
    {x y : α} (hx : x ∈ P.1) (hy : y ∈ P.1) :
    branchCellAtom G F c₂ p s Q P b x =
      branchCellAtom G F c₂ p s Q P b y := by
  simp [branchCellAtom, hx, hy,
    normalizedFunction_eq_on_cell_of_branchContainsCell G F Q P b hbP hx hy]

/--
Each side of a Haar branch has measure at least `lambda1 * μ(Q)`.

Both sides are nonempty unions of children of `Q`; choosing one child inside
the side and using the lower good-grid ratio gives the estimate.
-/
theorem branchSupport_measure_lower_left
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    ENNReal.ofReal G.grid.lambda1 * G.grid.μ Q.cell ≤
      G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1) := by
  classical
  let T := F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem
  have hb_childs : b.1.1 ⊆ T.Childs ∧ b.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds b.1 b.2
  have hb_nonempty : b.1.1.Nonempty ∧ b.1.2.Nonempty :=
    T.NonemptyPairs b.1 b.2
  obtain ⟨s, hs⟩ := hb_nonempty.1
  have hs_child : s ∈ G.grid.children Q.level Q.cell :=
    (F.toHaarSystem.binaryRefinement.childs_are_children Q.level Q.cell Q.mem s).1
      (hb_childs.1 hs)
  have hs_lower :
      ENNReal.ofReal G.grid.lambda1 * G.grid.μ Q.cell ≤ G.grid.μ s :=
    G.grid.ratio_lower Q.level s Q.cell hs_child.1 Q.mem hs_child.2
  have hs_subset :
      s ⊆ UnbalancedHaarWavelet.branchSupport b.1.1 :=
    UnbalancedHaarWavelet.subset_branchSupport_of_mem hs
  exact hs_lower.trans (MeasureTheory.measure_mono hs_subset)

/-- Right-side version of `branchSupport_measure_lower_left`. -/
theorem branchSupport_measure_lower_right
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    ENNReal.ofReal G.grid.lambda1 * G.grid.μ Q.cell ≤
      G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2) := by
  classical
  let T := F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem
  have hb_childs : b.1.1 ⊆ T.Childs ∧ b.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds b.1 b.2
  have hb_nonempty : b.1.1.Nonempty ∧ b.1.2.Nonempty :=
    T.NonemptyPairs b.1 b.2
  obtain ⟨s, hs⟩ := hb_nonempty.2
  have hs_child : s ∈ G.grid.children Q.level Q.cell :=
    (F.toHaarSystem.binaryRefinement.childs_are_children Q.level Q.cell Q.mem s).1
      (hb_childs.2 hs)
  have hs_lower :
      ENNReal.ofReal G.grid.lambda1 * G.grid.μ Q.cell ≤ G.grid.μ s :=
    G.grid.ratio_lower Q.level s Q.cell hs_child.1 Q.mem hs_child.2
  have hs_subset :
      s ⊆ UnbalancedHaarWavelet.branchSupport b.1.2 :=
    UnbalancedHaarWavelet.subset_branchSupport_of_mem hs
  exact hs_lower.trans (MeasureTheory.measure_mono hs_subset)

/-- Real-valued lower bound for the measure of the left side of a branch. -/
theorem branchSupport_toReal_lower_left
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    G.grid.lambda1 * (G.grid.μ Q.cell).toReal ≤
      (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal := by
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have h :=
    ENNReal.toReal_mono
      (MeasureTheory.measure_ne_top G.grid.μ
        (UnbalancedHaarWavelet.branchSupport b.1.1))
      (branchSupport_measure_lower_left G F Q b)
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal G.grid.hlambda1_pos.le,
    GoodGridCell.measure_ne_top Q] using h

/-- Real-valued lower bound for the measure of the right side of a branch. -/
theorem branchSupport_toReal_lower_right
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    G.grid.lambda1 * (G.grid.μ Q.cell).toReal ≤
      (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal := by
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have h :=
    ENNReal.toReal_mono
      (MeasureTheory.measure_ne_top G.grid.μ
        (UnbalancedHaarWavelet.branchSupport b.1.2))
      (branchSupport_measure_lower_right G F Q b)
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal G.grid.hlambda1_pos.le,
    GoodGridCell.measure_ne_top Q] using h

/-- The left side of a branch has positive real measure. -/
theorem branchSupport_toReal_pos_left
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    0 < (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal := by
  have hQ_pos :
      0 < (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have hlower := branchSupport_toReal_lower_left G F Q b
  have hmul_pos : 0 < G.grid.lambda1 * (G.grid.μ Q.cell).toReal :=
    mul_pos G.grid.hlambda1_pos hQ_pos
  exact lt_of_lt_of_le hmul_pos hlower

/-- The right side of a branch has positive real measure. -/
theorem branchSupport_toReal_pos_right
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    0 < (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal := by
  have hQ_pos :
      0 < (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have hlower := branchSupport_toReal_lower_right G F Q b
  have hmul_pos : 0 < G.grid.lambda1 * (G.grid.μ Q.cell).toReal :=
    mul_pos G.grid.hlambda1_pos hQ_pos
  exact lt_of_lt_of_le hmul_pos hlower

/-- The left support of a branch is measurable. -/
theorem measurableSet_branchSupport_left
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    MeasurableSet (UnbalancedHaarWavelet.branchSupport b.1.1) := by
  classical
  let T := F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem
  have hb_childs : b.1.1 ⊆ T.Childs ∧ b.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds b.1 b.2
  have hpart : ∀ s, s ∈ b.1.1 → s ∈ G.grid.grid.partitions (Q.level + 1) := by
    intro s hs
    exact (F.toHaarSystem.binaryRefinement.childs_are_children Q.level Q.cell Q.mem s).1
      (hb_childs.1 hs) |>.1
  exact UnbalancedHaarWavelet.measurableSet_branchSupport_of_partition
    (HaarRepresentation.GridOf G) Q.level b.1.1 hpart

/-- The right support of a branch is measurable. -/
theorem measurableSet_branchSupport_right
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    MeasurableSet (UnbalancedHaarWavelet.branchSupport b.1.2) := by
  classical
  let T := F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem
  have hb_childs : b.1.1 ⊆ T.Childs ∧ b.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds b.1 b.2
  have hpart : ∀ s, s ∈ b.1.2 → s ∈ G.grid.grid.partitions (Q.level + 1) := by
    intro s hs
    exact (F.toHaarSystem.binaryRefinement.childs_are_children Q.level Q.cell Q.mem s).1
      (hb_childs.2 hs) |>.1
  exact UnbalancedHaarWavelet.measurableSet_branchSupport_of_partition
    (HaarRepresentation.GridOf G) Q.level b.1.2 hpart

/--
The two real measures of a branch side add up to at most the parent-cell
measure.

This is the geometric input behind the scalar estimate for the normalized Haar
wavelet: the two supports are disjoint and their union is contained in `Q`.
-/
theorem branchSupport_toReal_add_le_parent
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal +
        (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal ≤
      (G.grid.μ Q.cell).toReal := by
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  let A := UnbalancedHaarWavelet.branchSupport b.1.1
  let B := UnbalancedHaarWavelet.branchSupport b.1.2
  have hdisj : Disjoint A B := by
    simpa [A, B] using
      F.toHaarSystem.branchSupport_components_disjoint (HaarRepresentation.GridOf G) b
  have hB_meas : MeasurableSet B := by
    simpa [B] using measurableSet_branchSupport_right G F Q b
  have hmeasure_union : G.grid.μ (A ∪ B) = G.grid.μ A + G.grid.μ B :=
    MeasureTheory.measure_union hdisj hB_meas
  have hleft_ne_top : G.grid.μ A ≠ ∞ := MeasureTheory.measure_ne_top G.grid.μ A
  have hright_ne_top : G.grid.μ B ≠ ∞ := MeasureTheory.measure_ne_top G.grid.μ B
  have hsum_eq :
      (G.grid.μ A).toReal + (G.grid.μ B).toReal =
        (G.grid.μ (A ∪ B)).toReal := by
    rw [hmeasure_union, ENNReal.toReal_add hleft_ne_top hright_ne_top]
  have hunion_subset : A ∪ B ⊆ Q.cell := by
    have hsupport_subset :
        UnbalancedHaarWavelet.haarBranchSupport b.1 ⊆ Q.cell :=
      F.toHaarSystem.haarBranchSupport_subset_cell (HaarRepresentation.GridOf G) b
    simpa [A, B, UnbalancedHaarWavelet.haarBranchSupport_eq_union_branchSupport] using
      hsupport_subset
  have hmono :
      (G.grid.μ (A ∪ B)).toReal ≤ (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_mono (GoodGridCell.measure_ne_top Q) (MeasureTheory.measure_mono hunion_subset)
  simpa [A, B, hsum_eq] using hmono

/--
The manuscript constant dominates the coarse reciprocal lower-grid factor.

This is a scalar consequence of the displayed definition of `c₂`; it is kept
separate from the Haar estimate so the remaining arithmetic is easy to audit.
-/
private theorem inv_two_mul_lambda1_le_c₂
    (G : GoodGridSpace (α := α)) :
    (2 * G.grid.lambda1)⁻¹ ≤ c₂ G := by
  let l₁ := G.grid.lambda1
  let l₂ := G.grid.lambda2
  have hl₁_pos : 0 < l₁ := G.grid.hlambda1_pos
  have hl₂_pos : 0 < l₂ := lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  have hroot_le : l₁ ^ ((1 : ℝ) / 2) ≤ l₂ ^ ((1 : ℝ) / 2) := by
    exact Real.rpow_le_rpow hl₁_pos.le (by simpa [l₁, l₂] using G.grid.hlambda1_le_lambda2)
      (by norm_num)
  have hsqrt_two_le_two : Real.sqrt 2 ≤ (2 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hroot_nonneg : 0 ≤ l₁ ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg hl₁_pos.le _
  have hroot₂_nonneg : 0 ≤ l₂ ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg hl₂_pos.le _
  have hmul_root :
      Real.sqrt 2 * l₁ ^ ((1 : ℝ) / 2) ≤
        2 * l₂ ^ ((1 : ℝ) / 2) := by
    exact mul_le_mul hsqrt_two_le_two hroot_le hroot_nonneg (by norm_num)
  have hl₁_three_halves :
      l₁ ^ ((3 : ℝ) / 2) = l₁ ^ ((1 : ℝ) / 2) * l₁ := by
    calc
      l₁ ^ ((3 : ℝ) / 2) = l₁ ^ (((1 : ℝ) / 2) + 1) := by norm_num
      _ = l₁ ^ ((1 : ℝ) / 2) * l₁ ^ (1 : ℝ) := by
          rw [Real.rpow_add hl₁_pos]
      _ = l₁ ^ ((1 : ℝ) / 2) * l₁ := by rw [Real.rpow_one]
  have hden_pos :
      0 < Real.sqrt 2 * l₁ ^ ((3 : ℝ) / 2) := by
    exact mul_pos (Real.sqrt_pos.2 (by norm_num))
      (Real.rpow_pos_of_pos hl₁_pos _)
  have htwol₁_pos : 0 < 2 * l₁ := mul_pos (by norm_num) hl₁_pos
  have hfrac_lower :
      (2 * l₁)⁻¹ ≤
        l₂ ^ ((1 : ℝ) / 2) / (Real.sqrt 2 * l₁ ^ ((3 : ℝ) / 2)) := by
    rw [inv_eq_one_div]
    rw [div_le_div_iff₀ htwol₁_pos hden_pos]
    rw [hl₁_three_halves]
    nlinarith [mul_nonneg (Real.sqrt_nonneg 2) hroot_nonneg, hmul_root, hl₁_pos]
  have hfrac_nonneg :
      0 ≤ l₂ ^ ((1 : ℝ) / 2) / (Real.sqrt 2 * l₁ ^ ((3 : ℝ) / 2)) :=
    div_nonneg hroot₂_nonneg hden_pos.le
  calc
    (2 * G.grid.lambda1)⁻¹ = (2 * l₁)⁻¹ := by rfl
    _ ≤ l₂ ^ ((1 : ℝ) / 2) / (Real.sqrt 2 * l₁ ^ ((3 : ℝ) / 2)) := hfrac_lower
    _ ≤ l₂ ^ ((1 : ℝ) / 2) / (Real.sqrt 2 * l₁ ^ ((3 : ℝ) / 2)) + 1 := by
      linarith
    _ = c₂ G := by
      simp [c₂, l₁, l₂]

/--
Pure real inequality used by the normalized-Haar estimate.

If two positive branch-side measures `a` and `b` have total mass at most `q`,
and the comparison set has mass at least `lambda * q`, then the normalized Haar
amplitude times the reciprocal comparison mass is bounded by
`K * q^(-1/2)`, provided `K` dominates `(2 * lambda)⁻¹`.
-/
private theorem real_l2NormalizationFactor_mul_inv_measure_le
    {a b c q lambda K : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : 0 < q)
    (hlambda : 0 < lambda)
    (hsum : a + b ≤ q)
    (hc_lower : lambda * q ≤ c)
    (hK : (2 * lambda)⁻¹ ≤ K) :
    |(Real.sqrt (1 / a + 1 / b))⁻¹ * (1 / c)| ≤
      K * q ^ (-(1 : ℝ) / 2) := by
  let S := 1 / a + 1 / b
  have hS_pos : 0 < S := by
    exact add_pos (one_div_pos.2 ha) (one_div_pos.2 hb)
  have hS_nonneg : 0 ≤ S := hS_pos.le
  have hsqrtS_pos : 0 < Real.sqrt S := Real.sqrt_pos.2 hS_pos
  have hsqrtq_pos : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hleft_nonneg : 0 ≤ (Real.sqrt S)⁻¹ * (1 / c) := by
    exact mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg S)) (one_div_nonneg.2 hc.le)
  have hAMHM : 4 ≤ S * (a + b) := by
    dsimp [S]
    field_simp [ha.ne', hb.ne']
    nlinarith [sq_nonneg (a - b)]
  have hfour_le_Sq : 4 ≤ S * q := by
    exact hAMHM.trans (mul_le_mul_of_nonneg_left hsum hS_nonneg)
  have htwo_le_sqrt_mul :
      2 ≤ Real.sqrt S * Real.sqrt q := by
    have htwo_le_sqrt : 2 ≤ Real.sqrt (S * q) := by
      have hsqrt_four_le : Real.sqrt 4 ≤ Real.sqrt (S * q) :=
        Real.sqrt_le_sqrt hfour_le_Sq
      have hsqrt_four_eq : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      simpa [hsqrt_four_eq] using hsqrt_four_le
    simpa [Real.sqrt_mul hS_nonneg] using htwo_le_sqrt
  have hl2_le : (Real.sqrt S)⁻¹ ≤ Real.sqrt q / 2 := by
    rw [inv_eq_one_div]
    rw [div_le_div_iff₀ hsqrtS_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hc_inv_le : 1 / c ≤ (lambda * q)⁻¹ := by
    rw [one_div]
    exact inv_anti₀ (mul_pos hlambda hq) hc_lower
  have hcoarse :
      (Real.sqrt S)⁻¹ * (1 / c) ≤
        (Real.sqrt q / 2) * (lambda * q)⁻¹ := by
    exact mul_le_mul hl2_le hc_inv_le (one_div_nonneg.2 hc.le)
      (div_nonneg (Real.sqrt_nonneg q) (by norm_num))
  have hq_neg_half :
      q ^ (-(1 : ℝ) / 2) = (Real.sqrt q)⁻¹ := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring]
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hq.le]
  have hcoarse_eq :
      (Real.sqrt q / 2) * (lambda * q)⁻¹ =
        (2 * lambda)⁻¹ * q ^ (-(1 : ℝ) / 2) := by
    rw [hq_neg_half]
    field_simp [hlambda.ne', hq.ne', (Real.sqrt_pos.2 hq).ne']
    rw [Real.sq_sqrt hq.le]
  have htoK :
      (2 * lambda)⁻¹ * q ^ (-(1 : ℝ) / 2) ≤
        K * q ^ (-(1 : ℝ) / 2) := by
    exact mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hq.le _)
  calc
    |(Real.sqrt (1 / a + 1 / b))⁻¹ * (1 / c)|
        = (Real.sqrt S)⁻¹ * (1 / c) := by
          rw [abs_of_nonneg hleft_nonneg]
    _ ≤ (Real.sqrt q / 2) * (lambda * q)⁻¹ := hcoarse
    _ = (2 * lambda)⁻¹ * q ^ (-(1 : ℝ) / 2) := hcoarse_eq
    _ ≤ K * q ^ (-(1 : ℝ) / 2) := htoK

/--
Scalar estimate behind the pointwise Haar bound.

If a branch side `C` has measure at least `lambda1 * μ(Q)`, then the product of
the `L²` normalization factor and the reciprocal measure of `C` is controlled
by the manuscript constant `c₂`.
-/
theorem l2NormalizationFactor_mul_inv_measure_le_c₂_mul_parent_rpow
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    (C : Set α)
    (hC_lower : G.grid.lambda1 * (G.grid.μ Q.cell).toReal ≤ (G.grid.μ C).toReal) :
    ‖(((HaarRepresentation.l2NormalizationFactor G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) : ℝ) : ℂ) *
        ((1 / (G.grid.μ C).toReal : ℝ) : ℂ))‖ ≤
      c₂ G * (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) := by
  classical
  let A := UnbalancedHaarWavelet.branchSupport b.1.1
  let B := UnbalancedHaarWavelet.branchSupport b.1.2
  let a := (G.grid.μ A).toReal
  let bμ := (G.grid.μ B).toReal
  let c := (G.grid.μ C).toReal
  let q := (G.grid.μ Q.cell).toReal
  have ha : 0 < a := by
    simpa [a, A] using branchSupport_toReal_pos_left G F Q b
  have hb : 0 < bμ := by
    simpa [bμ, B] using branchSupport_toReal_pos_right G F Q b
  have hq : 0 < q := by
    exact ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have hc : 0 < c := by
    have hmul_pos : 0 < G.grid.lambda1 * q :=
      mul_pos G.grid.hlambda1_pos hq
    exact lt_of_lt_of_le hmul_pos (by simpa [c, q] using hC_lower)
  have hsum : a + bμ ≤ q := by
    simpa [a, bμ, q, A, B] using branchSupport_toReal_add_le_parent G F Q b
  have hreal :
      |(Real.sqrt (1 / a + 1 / bμ))⁻¹ * (1 / c)| ≤
        c₂ G * q ^ (-(1 : ℝ) / 2) :=
    real_l2NormalizationFactor_mul_inv_measure_le ha hb hc hq G.grid.hlambda1_pos hsum
      (by simpa [c, q] using hC_lower)
      (inv_two_mul_lambda1_le_c₂ G)
  have hrewrite :
      HaarRepresentation.l2NormalizationFactor G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) =
        (Real.sqrt (1 / a + 1 / bμ))⁻¹ := by
    simp [HaarRepresentation.l2NormalizationFactor, HaarRepresentation.indexOfCellBranch,
      a, bμ, A, B]
  calc
    ‖(((HaarRepresentation.l2NormalizationFactor G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) : ℝ) : ℂ) *
        ((1 / (G.grid.μ C).toReal : ℝ) : ℂ))‖
        =
      |(Real.sqrt (1 / a + 1 / bμ))⁻¹ * (1 / c)| := by
        rw [hrewrite]
        simp [c]
    _ ≤ c₂ G * (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) := by
        simpa [q] using hreal

/--
Pointwise bound for the normalized Haar wavelet on a child carried by a branch.

This is where the quantitative good-grid estimate for `c₂` enters.
-/
theorem normalizedFunction_norm_le_c₂_mul_parent_rpow
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    (hbP : branchContainsCell G F Q P b)
    {x : α} (hx : x ∈ P.1) :
    ‖HaarRepresentation.normalizedFunction G F
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x‖ ≤
      c₂ G * (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) := by
  classical
  rw [branchContainsCell, branchCells, Finset.mem_union] at hbP
  rcases hbP with hleft | hright
  · rw [normalizedFunction_eq_left_of_mem G F Q P b hleft hx]
    exact l2NormalizationFactor_mul_inv_measure_le_c₂_mul_parent_rpow
      G F Q b (UnbalancedHaarWavelet.branchSupport b.1.1)
      (branchSupport_toReal_lower_left G F Q b)
  · rw [normalizedFunction_eq_right_of_mem G F Q P b hright hx]
    rw [norm_neg]
    exact l2NormalizationFactor_mul_inv_measure_le_c₂_mul_parent_rpow
      G F Q b (UnbalancedHaarWavelet.branchSupport b.1.2)
      (branchSupport_toReal_lower_right G F Q b)

/--
Pointwise size bound for one restricted branch atom.

This is the quantitative Haar estimate where the good-grid constant `c₂` is
used: after restricting a normalized Haar wavelet to a child cell, the
normalization makes it no larger than the Souza atom size on that child.
-/
theorem branchCellAtom_norm_bound
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    (hbP : branchContainsCell G F Q P b)
    {x : α} (hx : x ∈ P.1) :
    ‖branchCellAtom G F (c₂ G) p s Q P b x‖ ≤
      (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) := by
  classical
  let q := (G.grid.μ Q.cell).toReal
  let a := (G.grid.μ P.1).toReal ^ (s - 1 / p.toReal)
  let scale := q ^ ((1 : ℝ) / 2) / c₂ G * a
  have hhaar :=
    normalizedFunction_norm_le_c₂_mul_parent_rpow G F Q P b hbP hx
  have hq_pos : 0 < q := by
    exact ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have ha_nonneg : 0 ≤ a := by
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hc_pos : 0 < c₂ G := c₂_pos G
  have hscale_nonneg : 0 ≤ scale := by
    exact mul_nonneg
      (div_nonneg (Real.rpow_nonneg hq_pos.le _) hc_pos.le)
      ha_nonneg
  have hq_cancel : q ^ ((1 : ℝ) / 2) * q ^ (-(1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hq_pos]
    norm_num
  have hbranch_eq :
      branchCellAtom G F (c₂ G) p s Q P b x =
        (((scale : ℝ) : ℂ) *
          HaarRepresentation.normalizedFunction G F
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x) := by
    rw [branchCellAtom]
    simp only [hx, if_true]
    change (((q ^ ((1 : ℝ) / 2) / c₂ G * a : ℝ) : ℂ) *
        HaarRepresentation.normalizedFunction G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x) =
      (((scale : ℝ) : ℂ) *
        HaarRepresentation.normalizedFunction G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x)
    rw [show scale = q ^ ((1 : ℝ) / 2) / c₂ G * a by rfl]
  calc
    ‖branchCellAtom G F (c₂ G) p s Q P b x‖
        =
      ‖(((scale : ℝ) : ℂ) *
        HaarRepresentation.normalizedFunction G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x)‖ := by
        rw [hbranch_eq]
    _ = scale *
        ‖HaarRepresentation.normalizedFunction G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x‖ := by
        rw [norm_mul, Complex.norm_of_nonneg hscale_nonneg]
    _ ≤ scale *
        (c₂ G * q ^ (-(1 : ℝ) / 2)) := by
        exact mul_le_mul_of_nonneg_left (by simpa [q] using hhaar) hscale_nonneg
    _ = a := by
        calc
          scale *
              (c₂ G * q ^ (-(1 : ℝ) / 2))
              = a * ((q ^ ((1 : ℝ) / 2) * q ^ (-(1 : ℝ) / 2)) *
                  (c₂ G / c₂ G)) := by
                    simp [scale]
                    field_simp [hc_pos.ne']
          _ = a := by
              rw [hq_cancel, div_self hc_pos.ne']
              ring
    _ = (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) := by
        simp [a, one_div]

/--
The finite coefficient mass `\tilde{k}_P^f`.

Only the branches whose `S₁ ∪ S₂` contains `P` contribute.
-/
def tildeCoeff (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (c₂ : ℝ) (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) : ℝ := by
  classical
  exact ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
    if branchContainsCell G F Q P b then
      ‖branchCellCoeff G F c₂ p s f hf Q P b‖
    else
      0

/--
The averaged atom `\tilde{a}_P^f`.

When the normalizing mass is zero, this definition returns the zero function.
For positive mass it is exactly the convex average from the manuscript.
-/
def tildeAtom (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (c₂ : ℝ) (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (x : α) : ℂ := by
  classical
  exact if hzero : tildeCoeff G F c₂ p s f hf Q P = 0 then
    0
  else
    ((tildeCoeff G F c₂ p s f hf Q P)⁻¹ : ℂ) *
      ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
        if branchContainsCell G F Q P b then
          branchCellCoeff G F c₂ p s f hf Q P b *
            branchCellAtom G F c₂ p s Q P b x
        else
          0

/-- The averaged atom `\tilde{a}_P^f` vanishes outside its child cell. -/
theorem tildeAtom_eq_zero_of_not_mem
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (c₂ : ℝ) (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    {x : α} (hx : x ∉ P.1) :
    tildeAtom G F c₂ p s f hf Q P x = 0 := by
  classical
  by_cases hzero : tildeCoeff G F c₂ p s f hf Q P = 0
  · simp [tildeAtom, hzero]
  · simp [tildeAtom, hzero, branchCellAtom_eq_zero_of_not_mem G F c₂ p s Q P, hx]

/-- A distinguished point of a good-grid cell. -/
def cellPoint (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) : α :=
  Classical.choose (G.grid.partition_nonempty Q.level Q.cell Q.mem)

/-- The chosen point really belongs to its cell. -/
theorem cellPoint_mem (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) :
    cellPoint G Q ∈ Q.cell :=
  Classical.choose_spec (G.grid.partition_nonempty Q.level Q.cell Q.mem)

/--
On a contributing child cell, the artificial coefficient and atom
normalizations cancel.

This is the pointwise algebra behind the standard representation: the factor
`c₂`, the parent measure, and the child-measure powers were chosen precisely so
that a restricted branch atom multiplied by its branch-cell coefficient
recovers the corresponding Haar coefficient times the normalized Haar
function.
-/
theorem branchCellCoeff_mul_branchCellAtom_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    {x : α} (hx : x ∈ P.1) :
    branchCellCoeff G F (c₂ G) p s f hf Q P b *
        branchCellAtom G F (c₂ G) p s Q P b x =
      HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
        HaarRepresentation.normalizedFunction G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x := by
  classical
  let q := (G.grid.μ Q.cell).toReal
  let m := (G.grid.μ P.1).toReal
  let d :=
    HaarRepresentation.Coeff G F f hf
      (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))
  let φ :=
    HaarRepresentation.normalizedFunction G F
      (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hq_pos : 0 < q := by
    exact ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have hm_pos : 0 < m := by
    have hm_pos_en :
        0 < G.grid.μ P.1 :=
      G.grid.positive_measure (Q.level + 1) P.1 P.2
    have hm_ne_top :
        G.grid.μ P.1 ≠ ∞ :=
      MeasureTheory.measure_ne_top G.grid.μ P.1
    exact ENNReal.toReal_pos hm_pos_en.ne' hm_ne_top
  have hc_pos : 0 < c₂ G := c₂_pos G
  have hq_cancel :
      q ^ (-(1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hq_pos]
    norm_num
  have hm_cancel :
      m ^ (1 / p.toReal - s) * m ^ (s - 1 / p.toReal) = 1 := by
    rw [← Real.rpow_add hm_pos]
    ring_nf
    simp
  let r₁ := c₂ G * q ^ (-(1 : ℝ) / 2) * m ^ (1 / p.toReal - s)
  let r₂ := q ^ ((1 : ℝ) / 2) / c₂ G * m ^ (s - 1 / p.toReal)
  have hscalar : r₁ * r₂ = 1 := by
    calc
      r₁ * r₂
          =
        (c₂ G / c₂ G) *
          ((q ^ (-(1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2)) *
            (m ^ (1 / p.toReal - s) * m ^ (s - 1 / p.toReal))) := by
            simp [r₁, r₂]
            field_simp [hc_pos.ne']
      _ = 1 := by
        rw [div_self hc_pos.ne', hq_cancel, hm_cancel]
        ring
  have hscalarC : ((r₁ : ℝ) : ℂ) * ((r₂ : ℝ) : ℂ) = 1 := by
    norm_num [← Complex.ofReal_mul, hscalar]
  rw [branchCellCoeff, branchCellAtom]
  simp only [hx, if_true]
  change ((r₁ : ℂ) * d) * ((r₂ : ℂ) * φ) =
    d * φ
  calc
    ((r₁ : ℂ) * d) * ((r₂ : ℂ) * φ)
        = ((r₁ : ℂ) * (r₂ : ℂ)) * (d * φ) := by ring
    _ = d * φ := by
      rw [hscalarC]
      simp

/--
The normalization in `tildeAtom` cancels the mass `tildeCoeff`.

This lemma is only bookkeeping: if the normalizing mass is nonzero, it is the
usual inverse cancellation; if it is zero, every contributing branch-cell
coefficient is zero because the mass is a sum of nonnegative norms.
-/
theorem tildeCoeff_mul_tildeAtom_eq_sum_branchCell
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (x : α) :
    ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
        tildeAtom G F (c₂ G) p s f hf Q P x =
      (by
        classical
        exact
          ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
            if branchContainsCell G F Q P b then
              branchCellCoeff G F (c₂ G) p s f hf Q P b *
                branchCellAtom G F (c₂ G) p s Q P b x
            else
              0) := by
  classical
  let S := HaarRepresentation.indicesInCell G F Q
  let T := tildeCoeff G F (c₂ G) p s f hf Q P
  let inner :=
    ∑ b ∈ S,
      if branchContainsCell G F Q P b then
        branchCellCoeff G F (c₂ G) p s f hf Q P b *
          branchCellAtom G F (c₂ G) p s Q P b x
      else
        0
  change
    ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
        tildeAtom G F (c₂ G) p s f hf Q P x = inner
  by_cases hzero : T = 0
  · have hzero' : tildeCoeff G F (c₂ G) p s f hf Q P = 0 := by
      simpa [T] using hzero
    have hmass_zero :
        (∑ b ∈ S,
          (if branchContainsCell G F Q P b then
              ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖
            else
              0)) = 0 := by
      simpa [S, T, tildeCoeff] using hzero
    have hterms_zero :
        ∀ b ∈ S,
          (if branchContainsCell G F Q P b then
              branchCellCoeff G F (c₂ G) p s f hf Q P b *
                branchCellAtom G F (c₂ G) p s Q P b x
            else
              0) = 0 := by
      have hnonneg :
          ∀ b ∈ S,
            0 ≤
              (if branchContainsCell G F Q P b then
                  ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖
                else
                  0) := by
        intro b hb
        by_cases hbP : branchContainsCell G F Q P b
        · simp [hbP]
        · simp [hbP]
      have hall :=
        (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hmass_zero
      intro b hb
      by_cases hbP : branchContainsCell G F Q P b
      · have hnorm_zero :
            ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖ = 0 := by
          simpa [hbP] using hall b hb
        have hcoeff_zero :
            branchCellCoeff G F (c₂ G) p s f hf Q P b = 0 :=
          norm_eq_zero.1 hnorm_zero
        simp [hbP, hcoeff_zero]
      · simp [hbP]
    have hinner_zero : inner = 0 := by
      simpa [inner] using Finset.sum_eq_zero hterms_zero
    calc
      ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
          tildeAtom G F (c₂ G) p s f hf Q P x
          = 0 := by
            simp [tildeAtom, hzero']
      _ = inner := by
        rw [hinner_zero]
  · have hzero' : ¬ tildeCoeff G F (c₂ G) p s f hf Q P = 0 := by
      simpa [T] using hzero
    have hcancel :
        ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
            (((tildeCoeff G F (c₂ G) p s f hf Q P)⁻¹ : ℝ) : ℂ) = 1 := by
      have hne :
          ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hzero'
      simpa using mul_inv_cancel₀ hne
    calc
      ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
          tildeAtom G F (c₂ G) p s f hf Q P x
          =
        ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
          (((tildeCoeff G F (c₂ G) p s f hf Q P)⁻¹ : ℝ) : ℂ) *
            inner := by
            simp [tildeAtom, hzero', inner, S]
      _ = inner := by
        rw [hcancel]
        simp

/--
For a fixed branch, summing the restricted branch-cell pieces over the children
of `Q` recovers the corresponding Haar coefficient times the normalized Haar
function.
-/
theorem sum_children_branchCell_eq_coeff_normalizedFunction
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    (x : α) :
    (by
      classical
      exact
        ∑ P ∈ childrenOfCell G Q,
          if branchContainsCell G F Q P b then
            branchCellCoeff G F (c₂ G) p s f hf Q P b *
              branchCellAtom G F (c₂ G) p s Q P b x
          else
            0) =
      HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
        HaarRepresentation.normalizedFunction G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x := by
  classical
  let C := childrenOfCell G Q
  let support :=
    UnbalancedHaarWavelet.branchSupport
      (branchCells (G := G) (F := F) (Q := Q) b)
  have hbranch_childs :
      ∀ t, t ∈ branchCells (G := G) (F := F) (Q := Q) b →
        t ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell := by
    intro t ht
    have htree_childs :=
      (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).TreeStructureChilds b.1 b.2
    rw [branchCells, Finset.mem_union] at ht
    rcases ht with ht | ht
    · exact (F.toHaarSystem.binaryRefinement.childs_are_children
        Q.level Q.cell Q.mem t).1 (htree_childs.1 ht)
    · exact (F.toHaarSystem.binaryRefinement.childs_are_children
        Q.level Q.cell Q.mem t).1 (htree_childs.2 ht)
  have hpoint_mem_branch :
      ∀ P ∈ C, x ∈ P.1 → x ∈ support →
        branchContainsCell G F Q P b := by
    intro P hP hxP hx_support
    rcases (by simpa [support, UnbalancedHaarWavelet.branchSupport] using hx_support) with
      ⟨t, ht, hxt⟩
    have hP_fin :
        P.1 ∈ (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell :=
      (mem_childrenOfCell_iff G Q P).1 (by simpa [C] using hP)
    have hP_child :
        P.1 ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell :=
      ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell P.1).1 hP_fin
    have ht_child :
        t ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell :=
      hbranch_childs t ht
    by_cases hPt : P.1 = t
    · simpa [branchContainsCell, branchCells, hPt] using ht
    · have hdisj :
          Disjoint P.1 t :=
        (HaarRepresentation.GridOf G).grid.disjoint (Q.level + 1)
          P.1 t hP_child.1 ht_child.1 hPt
      exact False.elim ((Set.disjoint_left.1 hdisj) hxP hxt)
  change
    (∑ P ∈ C,
      if branchContainsCell G F Q P b then
        branchCellCoeff G F (c₂ G) p s f hf Q P b *
          branchCellAtom G F (c₂ G) p s Q P b x
      else
        0) =
      HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
        HaarRepresentation.normalizedFunction G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x
  by_cases hx_support : x ∈ support
  · rcases (by simpa [support, UnbalancedHaarWavelet.branchSupport] using hx_support) with
      ⟨t, ht, hxt⟩
    have ht_child :
        t ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell :=
      hbranch_childs t ht
    let P₀ : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1) :=
      ⟨t, ht_child.1⟩
    have hP₀_mem : P₀ ∈ C := by
      have ht_fin :
          t ∈ (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell :=
        ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell t).2 ht_child
      change P₀ ∈ childrenOfCell G Q
      rw [mem_childrenOfCell_iff]
      simpa [P₀] using ht_fin
    have hP₀_branch : branchContainsCell G F Q P₀ b := by
      simpa [P₀, branchContainsCell, branchCells] using ht
    have hxP₀ : x ∈ P₀.1 := by
      simpa [P₀] using hxt
    rw [Finset.sum_eq_single P₀]
    · simp [hP₀_branch]
      exact branchCellCoeff_mul_branchCellAtom_eq G F p s f hf Q P₀ b hxP₀
    · intro P hP hne
      by_cases hbP : branchContainsCell G F Q P b
      · have hx_not_P : x ∉ P.1 := by
          intro hxP
          have hP_fin :
              P.1 ∈ (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell :=
            (mem_childrenOfCell_iff G Q P).1 (by simpa [C] using hP)
          have hP_child :
              P.1 ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell :=
            ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell P.1).1 hP_fin
          by_cases hcell : P.1 = P₀.1
          · apply hne
            exact Subtype.ext hcell
          · have hdisj :
                Disjoint P.1 P₀.1 :=
              (HaarRepresentation.GridOf G).grid.disjoint (Q.level + 1)
                P.1 P₀.1 hP_child.1 ht_child.1 hcell
            exact (Set.disjoint_left.1 hdisj) hxP hxP₀
        simp [hbP, branchCellAtom_eq_zero_of_not_mem G F (c₂ G) p s Q P b hx_not_P]
      · simp [hbP]
    · intro hnot
      exact False.elim (hnot hP₀_mem)
  · have hsum_zero :
        (∑ P ∈ C,
          if branchContainsCell G F Q P b then
            branchCellCoeff G F (c₂ G) p s f hf Q P b *
              branchCellAtom G F (c₂ G) p s Q P b x
          else
            0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro P hP
      by_cases hbP : branchContainsCell G F Q P b
      · have hx_not_P : x ∉ P.1 := by
          intro hxP
          exact hx_support
            (UnbalancedHaarWavelet.subset_branchSupport_of_mem
              (by simpa [branchContainsCell] using hbP) hxP)
        simp [hbP, branchCellAtom_eq_zero_of_not_mem G F (c₂ G) p s Q P b hx_not_P]
      · simp [hbP]
    have hφ_zero :
        HaarRepresentation.normalizedFunction G F
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x = 0 := by
      exact normalizedFunction_eq_zero_of_not_mem_branchCells G F Q b (by simpa [support] using hx_support)
    rw [hsum_zero, hφ_zero, mul_zero]

/--
Pointwise bookkeeping identity for the standard atomic representation inside a
fixed good-grid cell.

The Haar block over the branches of `Q` is rewritten as the sum over the
children `P ⊆ Q` of the normalized coefficients `\tilde{k}_P^f` times the
averaged atoms `\tilde{a}_P^f`.  This is the Lean counterpart of the manuscript
formula
`∑_{S ∈ H_Q} d_S^f φ_S = ∑_{P ∈ P^{k+1}, P ⊆ Q} \tilde{k}_P^f \tilde{a}_P^f`.
-/
theorem haarBlock_eq_sum_tildeCoeff_tildeAtom_pointwise
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G) (x : α) :
    (∑ b ∈ HaarRepresentation.indicesInCell G F Q,
      HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
        HaarRepresentation.normalizedFunction G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x) =
    ∑ P ∈ childrenOfCell G Q,
      ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
        tildeAtom G F (c₂ G) p s f hf Q P x := by
  classical
  symm
  calc
    (∑ P ∈ childrenOfCell G Q,
      ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
        tildeAtom G F (c₂ G) p s f hf Q P x)
        =
      ∑ P ∈ childrenOfCell G Q,
        ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
          if branchContainsCell G F Q P b then
            branchCellCoeff G F (c₂ G) p s f hf Q P b *
              branchCellAtom G F (c₂ G) p s Q P b x
          else
            0 := by
          refine Finset.sum_congr rfl ?_
          intro P hP
          exact tildeCoeff_mul_tildeAtom_eq_sum_branchCell G F p s f hf Q P x
    _ =
      ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
        ∑ P ∈ childrenOfCell G Q,
          if branchContainsCell G F Q P b then
            branchCellCoeff G F (c₂ G) p s f hf Q P b *
              branchCellAtom G F (c₂ G) p s Q P b x
          else
            0 := by
          rw [Finset.sum_comm]
    _ =
      ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
        HaarRepresentation.Coeff G F f hf
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
          HaarRepresentation.normalizedFunction G F
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          exact sum_children_branchCell_eq_coeff_normalizedFunction G F p s f hf Q b x

/--
The Haar block over the branches attached to one good-grid cell.

This is the left-hand side of
`haarBlock_eq_sum_tildeCoeff_tildeAtom_pointwise`, packaged as a reusable
function.
-/
def haarCellBlockFunction (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (Q : GoodGridCell G) (x : α) : ℂ :=
  ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
    HaarRepresentation.Coeff G F f hf
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
      HaarRepresentation.normalizedFunction G F
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x

/--
The standard atomic block produced by one good-grid cell.

For a cell `Q ∈ P^k`, this is the formal version of
`∑_{P ∈ P^{k+1}, P ⊆ Q} \tilde{k}_P^f \tilde{a}_P^f`.
-/
def standardCellBlockFunction (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G) (x : α) : ℂ :=
  ∑ P ∈ childrenOfCell G Q,
    ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
      tildeAtom G F (c₂ G) p s f hf Q P x

/-- The one-cell Haar block belongs to `L^β`. -/
theorem haarCellBlock_memLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (Q : GoodGridCell G) :
    MemLp (haarCellBlockFunction G F f hf Q) β G.grid.μ := by
  classical
  unfold haarCellBlockFunction
  refine MeasureTheory.memLp_finsetSum _ ?_
  intro b hb
  simpa [HaarRepresentation.normalizedFunction, HaarRepresentation.L2normalizedHaar,
    smul_eq_mul] using
    (HaarRepresentation.l2normalizedHaar_memLp G F β
      (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))).const_smul
        (HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)))

/--
The standard one-cell block belongs to `L^β`.

The proof deliberately transports membership from the corresponding finite
Haar block using the pointwise block identity.
-/
theorem standardCellBlock_memLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G) :
    MemLp (standardCellBlockFunction G F p s f hf Q) β G.grid.μ := by
  classical
  refine (memLp_congr_ae ?_).1 (haarCellBlock_memLp G F β f hf Q)
  exact Filter.Eventually.of_forall fun x => by
    exact (haarBlock_eq_sum_tildeCoeff_tildeAtom_pointwise G F p s f hf Q x)

/--
In `L^β`, the Haar block attached to `Q` is the standard atomic block attached
to `Q`.

This is the `Lp` form of `haarBlock_eq_sum_tildeCoeff_tildeAtom_pointwise` and
is the main intermediate step for converting the unconditional Haar
representation into the standard representation.
-/
theorem haarCellBlock_toLp_eq_standardCellBlock_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G) :
    (haarCellBlock_memLp G F β f hf Q).toLp (haarCellBlockFunction G F f hf Q) =
      (standardCellBlock_memLp G F β p s f hf Q).toLp
        (standardCellBlockFunction G F p s f hf Q) := by
  classical
  refine MeasureTheory.MemLp.toLp_congr
    (haarCellBlock_memLp G F β f hf Q)
    (standardCellBlock_memLp G F β p s f hf Q) ?_
  exact Filter.Eventually.of_forall fun x => by
    exact (haarBlock_eq_sum_tildeCoeff_tildeAtom_pointwise G F p s f hf Q x)

/--
The `Lp` representative of one Haar cell block is the finite sum of the
corresponding individual Haar basis vectors.
-/
theorem haarCellBlock_toLp_eq_finsetSum
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (Q : GoodGridCell G) :
    (haarCellBlock_memLp G F β f hf Q).toLp (haarCellBlockFunction G F f hf Q) =
      ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
        HaarRepresentation.Coeff G F f hf
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) •
          (HaarRepresentation.l2normalizedHaar_memLp G F β
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))).toLp
            (HaarRepresentation.L2normalizedHaar G F
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))) := by
  classical
  rw [UnbalancedHaarWavelet.toLp_finsetSum_const_smul_complex β
    (HaarRepresentation.indicesInCell G F Q)
    (fun b => HaarRepresentation.L2normalizedHaar G F
      (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)))
    (fun b => HaarRepresentation.l2normalizedHaar_memLp G F β
      (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)))
    (fun b => HaarRepresentation.Coeff G F f hf
      (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)))]
  apply MeasureTheory.MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun x => by
    simp [haarCellBlockFunction, HaarRepresentation.normalizedFunction,
      HaarRepresentation.L2normalizedHaar]

/-- The Haar wavelet block at one level of the grid. -/
def haarLevelBlockFunction (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) (x : α) : ℂ :=
  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    haarCellBlockFunction G F f hf
      ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) x

/-- The standard atomic block at one level of the grid. -/
def standardLevelBlockFunction (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) (x : α) : ℂ :=
  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    standardCellBlockFunction G F p s f hf
      ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) x

/-- The Haar level block belongs to `L^β`. -/
theorem haarLevelBlock_memLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) :
    MemLp (haarLevelBlockFunction G F f hf k) β G.grid.μ := by
  classical
  unfold haarLevelBlockFunction
  refine MeasureTheory.memLp_finsetSum _ ?_
  intro Q hQ
  exact haarCellBlock_memLp G F β f hf
    ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G)

/-- The standard level block belongs to `L^β`. -/
theorem standardLevelBlock_memLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) :
    MemLp (standardLevelBlockFunction G F p s f hf k) β G.grid.μ := by
  classical
  refine (memLp_congr_ae ?_).1 (haarLevelBlock_memLp G F β f hf k)
  exact Filter.Eventually.of_forall fun x => by
    unfold haarLevelBlockFunction standardLevelBlockFunction
    refine Finset.sum_congr rfl ?_
    intro Q hQ
    exact haarBlock_eq_sum_tildeCoeff_tildeAtom_pointwise G F p s f hf
      ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) x

/--
In `L^β`, the Haar level block is the standard atomic level block.

After applying this lemma at every level, the only remaining global step is to
group the unconditional Haar expansion by level and add the father term.
-/
theorem haarLevelBlock_toLp_eq_standardLevelBlock_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) :
    (haarLevelBlock_memLp G F β f hf k).toLp (haarLevelBlockFunction G F f hf k) =
      (standardLevelBlock_memLp G F β p s f hf k).toLp
        (standardLevelBlockFunction G F p s f hf k) := by
  classical
  refine MeasureTheory.MemLp.toLp_congr
    (haarLevelBlock_memLp G F β f hf k)
    (standardLevelBlock_memLp G F β p s f hf k) ?_
  exact Filter.Eventually.of_forall fun x => by
    unfold haarLevelBlockFunction standardLevelBlockFunction
    refine Finset.sum_congr rfl ?_
    intro Q hQ
    exact haarBlock_eq_sum_tildeCoeff_tildeAtom_pointwise G F p s f hf
      ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) x

/--
The `Lp` representative of one Haar level block is the finite sum, over all
cells in that level and all branches in each cell, of the corresponding Haar
basis vectors.
-/
theorem haarLevelBlock_toLp_eq_finsetSum
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) :
    (haarLevelBlock_memLp G F β f hf k).toLp (haarLevelBlockFunction G F f hf k) =
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ∑ b ∈ HaarRepresentation.indicesInCell G F
            ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G),
          HaarRepresentation.Coeff G F f hf
              (.wavelet (HaarRepresentation.indexOfCellBranch G F
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) •
            (HaarRepresentation.l2normalizedHaar_memLp G F β
                (.wavelet (HaarRepresentation.indexOfCellBranch G F
                  ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b))).toLp
              (HaarRepresentation.L2normalizedHaar G F
                (.wavelet (HaarRepresentation.indexOfCellBranch G F
                  ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b))) := by
  classical
  let cellFun :
      WeakGridSpace.LevelCell G.toWeakGridSpace k → α → ℂ := fun Q =>
    haarCellBlockFunction G F f hf
      ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G)
  let cellMem :
      ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k, MemLp (cellFun Q) β G.grid.μ := fun Q =>
    haarCellBlock_memLp G F β f hf
      ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G)
  have hcongr :
      (haarLevelBlock_memLp G F β f hf k).toLp (haarLevelBlockFunction G F f hf k) =
        ((MeasureTheory.memLp_finsetSum
          (Finset.univ : Finset (WeakGridSpace.LevelCell G.toWeakGridSpace k))
          (fun Q _ => (cellMem Q).const_smul (1 : ℂ)))).toLp
          (fun x =>
            ∑ Q ∈ (Finset.univ : Finset (WeakGridSpace.LevelCell G.toWeakGridSpace k)),
              (1 : ℂ) * cellFun Q x) := by
    apply MeasureTheory.MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      simp [haarLevelBlockFunction, cellFun]
  rw [hcongr]
  rw [← UnbalancedHaarWavelet.toLp_finsetSum_const_smul_complex β
    (Finset.univ : Finset (WeakGridSpace.LevelCell G.toWeakGridSpace k))
    cellFun
    cellMem
    (fun _ => (1 : ℂ))]
  simp only [one_smul]
  refine Finset.sum_congr rfl ?_
  intro Q hQ
  dsimp [cellFun, cellMem]
  exact haarCellBlock_toLp_eq_finsetSum G F β f hf
    ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G)

/--
Fibers for the global standard expansion.

The `none` fiber contains the father Haar function.  The `some k` fiber
contains all branches attached to cells in level `k`.
-/
def standardExpansionFiber (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G)) :
    Option ℕ → Sort (max (u + 1) 1)
  | none => PUnit.{u + 1}
  | some k =>
      Σ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        {b : Finset (Set α) × Finset (Set α) //
          b ∈ (F.toHaarSystem.binaryRefinement.tree k Q.1 Q.2).Branches}

/--
The global standard-expansion indices are equivalent to the full Haar indices.

This is only bookkeeping: `none` corresponds to `.alpha`, and a branch in a
level cell corresponds to the matching wavelet index.
-/
noncomputable def standardExpansionIndexEquiv
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G)) :
    (Σ ok : Option ℕ, standardExpansionFiber G F ok) ≃ F.Index where
  toFun i :=
    match i with
    | ⟨none, _⟩ => .alpha
    | ⟨some k, ⟨Q, b⟩⟩ =>
        .wavelet
          (HaarRepresentation.indexOfCellBranch G F
            ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)
  invFun i :=
    match i with
    | .alpha => ⟨none, PUnit.unit⟩
    | .wavelet j => ⟨some j.level, ⟨⟨j.cell, j.hcell⟩, j.branch⟩⟩
  left_inv i := by
    cases i with
    | mk ok fiber =>
        cases ok with
        | none =>
            cases fiber
            rfl
        | some k =>
            rcases fiber with ⟨Q, b⟩
            rcases Q with ⟨cell, hcell⟩
            rfl
  right_inv i := by
    cases i with
    | alpha => rfl
    | wavelet j =>
        cases j
        rfl

@[simp]
theorem standardExpansionIndexEquiv_none
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G)) :
    (standardExpansionIndexEquiv G F) ⟨none, PUnit.unit⟩ =
      (UnbalancedHaarWavelet.FullHaarSystem.Index.alpha : F.Index) := rfl

@[simp]
theorem standardExpansionIndexEquiv_some
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree k Q.1 Q.2).Branches}) :
    (standardExpansionIndexEquiv G F) ⟨some k, ⟨Q, b⟩⟩ =
      .wavelet
        (HaarRepresentation.indexOfCellBranch G F
          ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b) := rfl

/-- The father term of the normalized Haar expansion, viewed in `L^β`. -/
def fatherHaarTermToLp (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) : Lp ℂ β G.grid.μ :=
  HaarRepresentation.Coeff G F f hf .alpha •
    (HaarRepresentation.l2normalizedHaar_memLp G F β .alpha).toLp
      (HaarRepresentation.L2normalizedHaar G F .alpha)

/-- The standard atomic block at level `k`, viewed in `L^β`. -/
def standardLevelBlockToLp (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) : Lp ℂ β G.grid.μ :=
  (standardLevelBlock_memLp G F β p s f hf k).toLp
    (standardLevelBlockFunction G F p s f hf k)

/--
The global standard expansion indexed by `Option ℕ`.

The `none` term is the father Haar term; `some k` is the standard atomic block
at level `k`.
-/
def standardExpansionTermToLp (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    Option ℕ → Lp ℂ β G.grid.μ
  | none => fatherHaarTermToLp G F β f hf
  | some k => standardLevelBlockToLp G F β p s f hf k

/--
For `1 < β < ∞`, the father term plus the standard atomic blocks converge in
`L^β` to `f`.

This is the standard representation obtained by grouping the unconditional
Haar expansion by level and replacing each Haar cell block by the corresponding
standard atomic block.
-/
theorem hasSum_standardExpansionTermToLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (β : ℝ≥0∞) (hβ_one : 1 < β) (hβ_top : β < ∞)
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : MemLp f β G.grid.μ) :
    letI : Fact (1 ≤ β) := ⟨le_of_lt hβ_one⟩
    HasSum
      (standardExpansionTermToLp G F β p s f
        (by
          letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
          exact hf.integrable (le_of_lt hβ_one)))
      (hf.toLp f) := by
  classical
  letI : Fact (1 ≤ β) := ⟨le_of_lt hβ_one⟩
  let hfint : Integrable f G.grid.μ := by
    letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
    exact hf.integrable (le_of_lt hβ_one)
  let haarTerm : F.Index → Lp ℂ β G.grid.μ := fun i =>
    HaarRepresentation.Coeff G F f hfint i •
      (HaarRepresentation.l2normalizedHaar_memLp G F β i).toLp
        (HaarRepresentation.L2normalizedHaar G F i)
  let indexedTerm :
      (Σ ok : Option ℕ, standardExpansionFiber G F ok) → Lp ℂ β G.grid.μ := fun i =>
    haarTerm ((standardExpansionIndexEquiv G F) i)
  have hhaar :
      HasSum haarTerm (hf.toLp f) := by
    simpa [haarTerm, hfint] using
      HaarRepresentation.hasSum_coeff_smul_l2normalizedHaar_toLp
        G F β hβ_one hβ_top f hf
  have hindexed :
      HasSum indexedTerm (hf.toLp f) := by
    simpa [indexedTerm, haarTerm, Function.comp_def] using
      ((standardExpansionIndexEquiv G F).hasSum_iff).2 hhaar
  refine hindexed.sigma ?_
  intro ok
  cases ok with
  | none =>
      letI : Fintype (standardExpansionFiber G F none) := by
        dsimp [standardExpansionFiber]
        infer_instance
      letI : Unique (standardExpansionFiber G F none) := by
        dsimp [standardExpansionFiber]
        infer_instance
      have hsum :
          (∑ u : standardExpansionFiber G F none, indexedTerm ⟨none, u⟩) =
            standardExpansionTermToLp G F β p s f hfint none := by
        rw [Fintype.sum_unique]
        change indexedTerm ⟨none, PUnit.unit⟩ =
          standardExpansionTermToLp G F β p s f hfint none
        dsimp [indexedTerm, haarTerm, standardExpansionTermToLp, fatherHaarTermToLp]
      convert
        (hasSum_fintype
          (fun u : standardExpansionFiber G F none => indexedTerm ⟨none, u⟩))
        using 1
      exact hsum.symm
  | some k =>
      letI : Fintype (standardExpansionFiber G F (some k)) := by
        dsimp [standardExpansionFiber]
        infer_instance
      have hsum :
          (∑ u : standardExpansionFiber G F (some k), indexedTerm ⟨some k, u⟩) =
            (standardLevelBlockToLp G F β p s f hfint k) := by
        calc
          (∑ u : standardExpansionFiber G F (some k), indexedTerm ⟨some k, u⟩)
              =
            (haarLevelBlock_memLp G F β f hfint k).toLp
              (haarLevelBlockFunction G F f hfint k) := by
                rw [haarLevelBlock_toLp_eq_finsetSum G F β f hfint k]
                change
                  (∑ u :
                    (Σ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
                      {b : Finset (Set α) × Finset (Set α) //
                        b ∈ (F.toHaarSystem.binaryRefinement.tree k Q.1 Q.2).Branches}),
                    indexedTerm ⟨some k, u⟩) =
                    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
                      ∑ b ∈ HaarRepresentation.indicesInCell G F
                          ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G),
                        HaarRepresentation.Coeff G F f hfint
                            (.wavelet (HaarRepresentation.indexOfCellBranch G F
                              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) •
                          (HaarRepresentation.l2normalizedHaar_memLp G F β
                              (.wavelet (HaarRepresentation.indexOfCellBranch G F
                                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b))).toLp
                            (HaarRepresentation.L2normalizedHaar G F
                              (.wavelet (HaarRepresentation.indexOfCellBranch G F
                                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)))
                rw [Fintype.sum_sigma]
                dsimp [indexedTerm, haarTerm]
                rfl
          _ = standardLevelBlockToLp G F β p s f hfint k := by
                rw [haarLevelBlock_toLp_eq_standardLevelBlock_toLp G F β p s f hfint k]
                rfl
      convert
        (hasSum_fintype
          (fun u : standardExpansionFiber G F (some k) => indexedTerm ⟨some k, u⟩))
        using 1
      exact hsum.symm

/--
The size estimate needed for the averaged atom.

This is the remaining analytic estimate in the proof that `\tilde{a}_P^f` is a
Souza atom: the normalized average is bounded by the Souza atom size on `P`.
The proof should combine the pointwise Haar-wavelet bound coming from the
good-grid constant `c₂` with the triangle inequality for the convex average.
-/
theorem tildeAtom_norm_bound
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) :
    ‖tildeAtom G F (c₂ G) p s f hf Q P
        (cellPoint G (childToGoodGridCell (G := G) (Q := Q) P))‖ ≤
      (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) := by
  classical
  let x₀ := cellPoint G (childToGoodGridCell (G := G) (Q := Q) P)
  let S := HaarRepresentation.indicesInCell G F Q
  let T := tildeCoeff G F (c₂ G) p s f hf Q P
  let A := (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹)
  have hx₀ : x₀ ∈ P.1 :=
    cellPoint_mem G (childToGoodGridCell (G := G) (Q := Q) P)
  have hA_nonneg : 0 ≤ A := by
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  by_cases hzero : T = 0
  · have hzero' : tildeCoeff G F (c₂ G) p s f hf Q P = 0 := by
      simpa [T] using hzero
    simpa [x₀, A, tildeAtom, hzero'] using hA_nonneg
  · have hT_nonneg : 0 ≤ T := by
      simp [T, tildeCoeff]
      exact Finset.sum_nonneg fun b _ => by
        by_cases hbP : branchContainsCell G F Q P b
        · simp [hbP]
        · simp [hbP]
    have hT_pos : 0 < T := lt_of_le_of_ne hT_nonneg (Ne.symm hzero)
    have hzero' : ¬ tildeCoeff G F (c₂ G) p s f hf Q P = 0 := by
      simpa [T] using hzero
    have hnorm_sum :
        ‖∑ b ∈ S,
            if branchContainsCell G F Q P b then
              branchCellCoeff G F (c₂ G) p s f hf Q P b *
                branchCellAtom G F (c₂ G) p s Q P b x₀
            else
              0‖
          ≤
        ∑ b ∈ S,
          ‖if branchContainsCell G F Q P b then
              branchCellCoeff G F (c₂ G) p s f hf Q P b *
                branchCellAtom G F (c₂ G) p s Q P b x₀
            else
              0‖ := by
      exact norm_sum_le _ _
    have hterm_le :
        (∑ b ∈ S,
          ‖if branchContainsCell G F Q P b then
              branchCellCoeff G F (c₂ G) p s f hf Q P b *
                branchCellAtom G F (c₂ G) p s Q P b x₀
            else
              0‖)
          ≤
        ∑ b ∈ S,
          if branchContainsCell G F Q P b then
            ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖ * A
          else
            0 := by
      refine Finset.sum_le_sum ?_
      intro b hb
      by_cases hbP : branchContainsCell G F Q P b
      · have hbranch :=
          branchCellAtom_norm_bound G F p s Q P b hbP hx₀
        simp [hbP, A] at hbranch ⊢
        exact mul_le_mul_of_nonneg_left hbranch (norm_nonneg _)
      · simp [hbP]
    have hweighted_sum :
        (∑ b ∈ S,
          if branchContainsCell G F Q P b then
            ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖ * A
          else
            0) = T * A := by
      simp [S, T, A, tildeCoeff, Finset.sum_mul]
    calc
      ‖tildeAtom G F (c₂ G) p s f hf Q P
          (cellPoint G (childToGoodGridCell (G := G) (Q := Q) P))‖
          =
        ‖((T)⁻¹ : ℂ) *
          ∑ b ∈ S,
            if branchContainsCell G F Q P b then
              branchCellCoeff G F (c₂ G) p s f hf Q P b *
                branchCellAtom G F (c₂ G) p s Q P b x₀
            else
              0‖ := by
            simp [tildeAtom, hzero', x₀, S, T]
      _ = ‖((T)⁻¹ : ℂ)‖ *
          ‖∑ b ∈ S,
            if branchContainsCell G F Q P b then
              branchCellCoeff G F (c₂ G) p s f hf Q P b *
                branchCellAtom G F (c₂ G) p s Q P b x₀
            else
              0‖ := norm_mul _ _
      _ ≤ ‖((T)⁻¹ : ℂ)‖ *
          (∑ b ∈ S,
            if branchContainsCell G F Q P b then
              ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖ * A
            else
              0) := by
            exact mul_le_mul_of_nonneg_left (hnorm_sum.trans hterm_le) (norm_nonneg _)
      _ = ‖((T)⁻¹ : ℂ)‖ * (T * A) := by
            rw [hweighted_sum]
      _ = A := by
            rw [norm_inv, Complex.norm_of_nonneg hT_nonneg]
            rw [← mul_assoc, inv_mul_cancel₀ hT_pos.ne', one_mul]

/--
The averaged atom `\tilde{a}_P^f` is a Souza atom on the child cell `P`.

This is the atomhood assertion needed to turn the finite identity above into an
actual Souza atomic representation.  Its proof uses the local constancy of Haar
wavelets on the child cells and the normalization encoded by `c₂`.
-/
theorem tildeAtom_isSouzaAtom
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) :
    IsSouzaAtom G s p (childToGoodGridCell (G := G) (Q := Q) P)
      (tildeAtom G F (c₂ G) p s f hf Q P) := by
  classical
  by_cases hzero : tildeCoeff G F (c₂ G) p s f hf Q P = 0
  · have hfun :
        tildeAtom G F (c₂ G) p s f hf Q P = fun _ : α => 0 := by
      funext x
      simp [tildeAtom, hzero]
    simpa [hfun] using
      zero_isSouzaAtom G s p (childToGoodGridCell (G := G) (Q := Q) P)
  · refine ⟨?support, ?constant⟩
    · intro x hx
      exact tildeAtom_eq_zero_of_not_mem G F (c₂ G) p s f hf Q P hx
    · let Pcell := childToGoodGridCell (G := G) (Q := Q) P
      refine ⟨tildeAtom G F (c₂ G) p s f hf Q P (cellPoint G Pcell), ?const_on_cell, ?bound⟩
      · intro x hx
        have hpoint : cellPoint G Pcell ∈ P.1 :=
          cellPoint_mem G Pcell
        rw [tildeAtom, dif_neg hzero, tildeAtom, dif_neg hzero]
        congr 1
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hbP : branchContainsCell G F Q P b
        · simp only [hbP, if_true]
          rw [branchCellAtom_eq_on_cell_of_branchContainsCell G F (c₂ G) p s Q P b hbP
            hx hpoint]
        · simp [hbP]
      · simpa [Pcell] using tildeAtom_norm_bound G F p s f hf Q P

/--
The standard coefficient `k_P^f` associated with a child `P ⊆ Q`.

This is the point-evaluation formula from the manuscript, using the chosen
representative point `x_P`.
-/
def standardChildCoeff (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) : ℂ := by
  classical
  let Pcell := childToGoodGridCell (G := G) (Q := Q) P
  exact (((G.grid.μ P.1).toReal ^ (-(s - 1 / p.toReal)) : ℝ) : ℂ) *
    ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
      if branchContainsCell G F Q P b then
        HaarRepresentation.Coeff G F f hf (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
          HaarRepresentation.normalizedFunction G F (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))
            (cellPoint G Pcell)
      else
        0

/--
The standard coefficient is the manuscript's finite Haar formula at the
representative point of the child cell.

This is mostly a naming lemma: `standardChildCoeff` was defined with the
compatibility alias `normalizedFunction`, while the paper-facing notation in
`HaarRepresentationNorm` is `L2normalizedHaar`.
-/
theorem standardChildCoeff_eq_sum_l2normalizedHaar_at_cellPoint
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) :
    standardChildCoeff G F s p f hf Q P = by
      classical
      exact
        (((G.grid.μ P.1).toReal ^ (-(s - 1 / p.toReal)) : ℝ) : ℂ) *
          ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
            if branchContainsCell G F Q P b then
              HaarRepresentation.Coeff G F f hf
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
                HaarRepresentation.L2normalizedHaar G F
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))
                  (cellPoint G (childToGoodGridCell (G := G) (Q := Q) P))
            else
              0 := by
  classical
  simp only [standardChildCoeff, HaarRepresentation.normalizedFunction,
    HaarRepresentation.L2normalizedHaar]

/--
The same coefficient formula with the Haar coefficients expanded as concrete
integrals.

This is the finite-sum version of the kernel formula
`∫ f · (Σ φ_S(x_P) φ_S)`.  Keeping the sum outside the integral makes the
statement line up directly with `HaarRepresentation.Coeff`.
-/
theorem standardChildCoeff_eq_sum_integral_l2normalizedHaar_at_cellPoint
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) :
    standardChildCoeff G F s p f hf Q P = by
      classical
      exact
        (((G.grid.μ P.1).toReal ^ (-(s - 1 / p.toReal)) : ℝ) : ℂ) *
          ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
            if branchContainsCell G F Q P b then
              (∫ x, f x *
                HaarRepresentation.L2normalizedHaar G F
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x ∂G.grid.μ) *
                HaarRepresentation.L2normalizedHaar G F
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))
                  (cellPoint G (childToGoodGridCell (G := G) (Q := Q) P))
            else
              0 := by
  rw [standardChildCoeff_eq_sum_l2normalizedHaar_at_cellPoint]
  simp only [HaarRepresentation.Coeff]

/--
The `L¹` functional represented by the standard coefficient on a fixed child
cell.

The kernel is a finite linear combination of bounded normalized Haar functions,
so the formula extends from concrete integrable functions to a continuous
linear functional on `L¹`.
-/
def standardChildCoeffFunctionalL1
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) :
    Lp ℂ (1 : ℝ≥0∞) G.grid.μ →L[ℂ] ℂ := by
  classical
  haveI : ENNReal.HolderConjugate (1 : ℝ≥0∞) (∞ : ℝ≥0∞) := by
    rw [ENNReal.holderConjugate_iff]
    simp
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  letI : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  exact
    (((G.grid.μ P.1).toReal ^ (-(s - 1 / p.toReal)) : ℝ) : ℂ) •
      ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
        if branchContainsCell G F Q P b then
          HaarRepresentation.L2normalizedHaar G F
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))
              (cellPoint G (childToGoodGridCell (G := G) (Q := Q) P)) •
            (((ContinuousLinearMap.mul ℂ ℂ).lpPairing G.grid.μ
                  (1 : ℝ≥0∞) (∞ : ℝ≥0∞)).flip
              ((HaarRepresentation.l2normalizedHaar_memLp G F (∞ : ℝ≥0∞)
                    (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))).toLp
                (HaarRepresentation.L2normalizedHaar G F
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)))))
        else
          0

/--
On an `L¹` representative, the continuous functional is the concrete standard
coefficient `k_P^f`.
-/
theorem standardChildCoeffFunctionalL1_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : MemLp f (1 : ℝ≥0∞) G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) :
    standardChildCoeffFunctionalL1 G F s p Q P (hf.toLp f) =
      (by
        letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
        exact standardChildCoeff G F s p f (hf.integrable le_rfl) Q P) := by
  classical
  letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  haveI : ENNReal.HolderConjugate (1 : ℝ≥0∞) (∞ : ℝ≥0∞) := by
    rw [ENNReal.holderConjugate_iff]
    simp
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  letI : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  have hpair
      (b : {r : Finset (Set α) × Finset (Set α) //
        r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
      (((ContinuousLinearMap.mul ℂ ℂ).lpPairing G.grid.μ
            (1 : ℝ≥0∞) (∞ : ℝ≥0∞)).flip
        ((HaarRepresentation.l2normalizedHaar_memLp G F (∞ : ℝ≥0∞)
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))).toLp
          (HaarRepresentation.L2normalizedHaar G F
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)))))
          (hf.toLp f) =
        HaarRepresentation.Coeff G F f (hf.integrable le_rfl)
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) := by
    rw [HaarRepresentation.Coeff]
    change (ContinuousLinearMap.mul ℂ ℂ).lpPairing G.grid.μ
        (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (hf.toLp f)
          ((HaarRepresentation.l2normalizedHaar_memLp G F (∞ : ℝ≥0∞)
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))).toLp
            (HaarRepresentation.L2normalizedHaar G F
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)))) =
        ∫ x, f x *
          HaarRepresentation.L2normalizedHaar G F
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x ∂G.grid.μ
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards
      [MemLp.coeFn_toLp hf,
        MemLp.coeFn_toLp
          (HaarRepresentation.l2normalizedHaar_memLp G F (∞ : ℝ≥0∞)
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)))] with x hxf hxhaar
    simp [hxf, hxhaar]
  rw [standardChildCoeff_eq_sum_l2normalizedHaar_at_cellPoint]
  unfold standardChildCoeffFunctionalL1
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  apply congrArg
    (fun z : ℂ =>
      (((G.grid.μ P.1).toReal ^ (-(s - 1 / p.toReal)) : ℝ) : ℂ) * z)
  refine Finset.sum_congr rfl ?_
  intro b hb
  by_cases hbP : branchContainsCell G F Q P b
  · simp [hbP, hpair b, mul_comm]
  · simp [hbP]

/--
The canonical coefficient and the canonical Souza atom recover the older
`tildeCoeff * tildeAtom` term.

This is the formal version of replacing `\tilde{k}_P^f \tilde{a}_P^f` by
`k_P^f a_P`, where `a_P` is the canonical Souza atom on `P`.
-/
theorem standardChildCoeff_mul_canonicalSouzaAtom_eq_tildeCoeff_mul_tildeAtom
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) (x : α) :
    standardChildCoeff G F s p f hf Q P *
        canonicalSouzaAtom G s p (childToGoodGridCell (G := G) (Q := Q) P) x =
      ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
        tildeAtom G F (c₂ G) p s f hf Q P x := by
  classical
  let Pcell := childToGoodGridCell (G := G) (Q := Q) P
  by_cases hx : x ∈ P.1
  · have hpoint : cellPoint G Pcell ∈ P.1 := by
      simpa [Pcell] using cellPoint_mem G Pcell
    have htilde_const :
        tildeAtom G F (c₂ G) p s f hf Q P x =
          tildeAtom G F (c₂ G) p s f hf Q P (cellPoint G Pcell) := by
      rcases tildeAtom_isSouzaAtom G F p s f hf Q P with ⟨_, c, hc, _⟩
      rw [hc x (by simpa [Pcell] using hx),
        hc (cellPoint G Pcell) (by simpa [Pcell] using hpoint)]
    have hsum_point :
        ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
            tildeAtom G F (c₂ G) p s f hf Q P (cellPoint G Pcell) =
          ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
            if branchContainsCell G F Q P b then
              HaarRepresentation.Coeff G F f hf
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
                HaarRepresentation.normalizedFunction G F
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))
                  (cellPoint G Pcell)
            else
              0 := by
      rw [tildeCoeff_mul_tildeAtom_eq_sum_branchCell G F p s f hf Q P (cellPoint G Pcell)]
      refine Finset.sum_congr rfl ?_
      intro b hb
      by_cases hbP : branchContainsCell G F Q P b
      · simp [hbP, branchCellCoeff_mul_branchCellAtom_eq G F p s f hf Q P b hpoint]
      · simp [hbP]
    let m := (G.grid.μ P.1).toReal
    let r := s - (p.toReal)⁻¹
    have hm_pos : 0 < m := by
      have hm_pos_en : 0 < G.grid.μ P.1 :=
        G.grid.positive_measure (Q.level + 1) P.1 P.2
      letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
      have hm_ne_top : G.grid.μ P.1 ≠ ∞ :=
        MeasureTheory.measure_ne_top G.grid.μ P.1
      exact ENNReal.toReal_pos hm_pos_en.ne' hm_ne_top
    have hcancelC :
        (((m ^ (-r) : ℝ) : ℂ) * ((m ^ r : ℝ) : ℂ)) = 1 := by
      norm_num [← Complex.ofReal_mul]
      rw [← Real.rpow_add hm_pos]
      ring_nf
      simp
    have hcanon_on :
        canonicalSouzaAtom G s p Pcell x = (((m ^ r : ℝ) : ℂ)) := by
      have hxPcell : x ∈ Pcell.cell := by
        simpa [Pcell] using hx
      simp [canonicalSouzaAtom, hxPcell, Pcell, m, r]
      change (G.grid.μ P.1).toReal ^ (s - p.toReal⁻¹) =
        (G.grid.μ P.1).toReal ^ (s - p.toReal⁻¹)
      rfl
    have hcoeff_def :
        standardChildCoeff G F s p f hf Q P =
          ((m ^ (-r) : ℝ) : ℂ) *
            ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
              if branchContainsCell G F Q P b then
                HaarRepresentation.Coeff G F f hf
                    (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
                  HaarRepresentation.normalizedFunction G F
                    (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))
                    (cellPoint G Pcell)
              else
                0 := by
      simp [standardChildCoeff, Pcell, m, r, one_div]
    calc
      standardChildCoeff G F s p f hf Q P *
          canonicalSouzaAtom G s p Pcell x
          =
        (((m ^ (-r) : ℝ) : ℂ) *
          ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
            if branchContainsCell G F Q P b then
              HaarRepresentation.Coeff G F f hf
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
                HaarRepresentation.normalizedFunction G F
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))
                  (cellPoint G Pcell)
            else
              0) * ((m ^ r : ℝ) : ℂ) := by
            rw [hcanon_on, hcoeff_def]
      _ =
        ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
          if branchContainsCell G F Q P b then
            HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
              HaarRepresentation.normalizedFunction G F
                (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))
                (cellPoint G Pcell)
          else
            0 := by
          rw [mul_assoc, mul_comm _ (((m ^ r : ℝ) : ℂ)), ← mul_assoc, hcancelC]
          simp
      _ =
        ((tildeCoeff G F (c₂ G) p s f hf Q P : ℝ) : ℂ) *
          tildeAtom G F (c₂ G) p s f hf Q P x := by
          rw [htilde_const]
          exact hsum_point.symm
  · have hcanon :
        canonicalSouzaAtom G s p Pcell x = 0 := by
      have hxPcell : x ∉ Pcell.cell := by
        simpa [Pcell] using hx
      simp [canonicalSouzaAtom, hxPcell]
    have htilde :
        tildeAtom G F (c₂ G) p s f hf Q P x = 0 :=
      tildeAtom_eq_zero_of_not_mem G F (c₂ G) p s f hf Q P hx
    rw [hcanon, htilde]
    simp

/--
The standard block over one parent cell, written with canonical Souza atoms.
-/
def canonicalStandardCellBlockFunction
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G) (x : α) : ℂ :=
  ∑ P ∈ childrenOfCell G Q,
    standardChildCoeff G F s p f hf Q P *
      canonicalSouzaAtom G s p (childToGoodGridCell (G := G) (Q := Q) P) x

/--
The canonical-Souza version of one parent-cell block agrees pointwise with the
previous `tildeCoeff * tildeAtom` block.
-/
theorem canonicalStandardCellBlock_eq_standardCellBlock_pointwise
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G) (x : α) :
    canonicalStandardCellBlockFunction G F p s f hf Q x =
      standardCellBlockFunction G F p s f hf Q x := by
  classical
  unfold canonicalStandardCellBlockFunction standardCellBlockFunction
  refine Finset.sum_congr rfl ?_
  intro P hP
  exact standardChildCoeff_mul_canonicalSouzaAtom_eq_tildeCoeff_mul_tildeAtom
    G F p s f hf Q P x

/--
The standard level block, written with canonical Souza atoms on the children of
level-`k` cells.
-/
def canonicalStandardLevelBlockFunction
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) (x : α) : ℂ :=
  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    canonicalStandardCellBlockFunction G F p s f hf
      ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) x

/--
The canonical-Souza level block agrees pointwise with the previous standard
level block.
-/
theorem canonicalStandardLevelBlock_eq_standardLevelBlock_pointwise
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) (x : α) :
    canonicalStandardLevelBlockFunction G F p s f hf k x =
      standardLevelBlockFunction G F p s f hf k x := by
  classical
  unfold canonicalStandardLevelBlockFunction standardLevelBlockFunction
  refine Finset.sum_congr rfl ?_
  intro Q hQ
  exact canonicalStandardCellBlock_eq_standardCellBlock_pointwise G F p s f hf
    ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) x

/-- The canonical-Souza level block belongs to `L^β`. -/
theorem canonicalStandardLevelBlock_memLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) :
    MemLp (canonicalStandardLevelBlockFunction G F p s f hf k) β G.grid.μ := by
  refine (memLp_congr_ae ?_).1 (standardLevelBlock_memLp G F β p s f hf k)
  exact Filter.Eventually.of_forall fun x =>
    (canonicalStandardLevelBlock_eq_standardLevelBlock_pointwise G F p s f hf k x).symm

/-- The canonical-Souza standard block at level `k`, viewed in `L^β`. -/
def canonicalStandardLevelBlockToLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) : Lp ℂ β G.grid.μ :=
  (canonicalStandardLevelBlock_memLp G F β p s f hf k).toLp
    (canonicalStandardLevelBlockFunction G F p s f hf k)

/--
The canonical-Souza `Lp` level block is the same vector as the earlier standard
level block.
-/
theorem canonicalStandardLevelBlockToLp_eq_standardLevelBlockToLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) :
    canonicalStandardLevelBlockToLp G F β p s f hf k =
      standardLevelBlockToLp G F β p s f hf k := by
  refine MeasureTheory.MemLp.toLp_congr
    (canonicalStandardLevelBlock_memLp G F β p s f hf k)
    (standardLevelBlock_memLp G F β p s f hf k) ?_
  exact Filter.Eventually.of_forall fun x =>
    canonicalStandardLevelBlock_eq_standardLevelBlock_pointwise G F p s f hf k x

/--
The global standard expansion using canonical Souza atoms.

The `none` term is the father Haar term; `some k` is the level-`k` sum of
canonical Souza atoms.
-/
def canonicalStandardExpansionTermToLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    Option ℕ → Lp ℂ β G.grid.μ
  | none => fatherHaarTermToLp G F β f hf
  | some k => canonicalStandardLevelBlockToLp G F β p s f hf k

/--
For `1 < β < ∞`, the father term plus the canonical-Souza standard blocks
converge in `L^β` to `f`.
-/
theorem hasSum_canonicalStandardExpansionTermToLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (β : ℝ≥0∞) (hβ_one : 1 < β) (hβ_top : β < ∞)
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : MemLp f β G.grid.μ) :
    letI : Fact (1 ≤ β) := ⟨le_of_lt hβ_one⟩
    HasSum
      (canonicalStandardExpansionTermToLp G F β p s f
        (by
          letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
          exact hf.integrable (le_of_lt hβ_one)))
      (hf.toLp f) := by
  classical
  letI : Fact (1 ≤ β) := ⟨le_of_lt hβ_one⟩
  let hfint : Integrable f G.grid.μ := by
    letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
    exact hf.integrable (le_of_lt hβ_one)
  have h :
      canonicalStandardExpansionTermToLp G F β p s f hfint =
        standardExpansionTermToLp G F β p s f hfint := by
    funext ok
    cases ok with
    | none => rfl
    | some k =>
        exact canonicalStandardLevelBlockToLp_eq_standardLevelBlockToLp G F β p s f hfint k
  rw [h]
  exact hasSum_standardExpansionTermToLp G F β hβ_one hβ_top p s f hf

/--
The canonical Souza level block at level `k + 1` associated with the standard
Haar block over parents at level `k`.

For a child cell `P`, the coefficient is written as a finite sum over all
level-`k` parents, with the summand zero unless `P` is a child of that parent.
This avoids choosing a parent function and makes later finite-sum rewrites
straightforward.
-/
def canonicalStandardPositiveLevelBlock
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) (k + 1) where
  coeff := fun P =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      let Qg : GoodGridCell G := { level := k, cell := Q.1, mem := Q.2 }
      if hP : P ∈ childrenOfCell G Qg then
        standardChildCoeff G F s p f hf Qg P
      else
        0
  atom := fun P =>
    (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)
  atom_mem := by
    intro P
    change ‖((((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ))‖ ≤
      (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹)
    have hnonneg :
        0 ≤ (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    simp [Complex.norm_real, Real.norm_of_nonneg hnonneg]

/--
The pointwise function represented by the positive standard `LevelBlock` is the
canonical-Souza level block already used in the Haar regrouping proof.
-/
theorem canonicalStandardPositiveLevelBlock_toFunLt
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) (x : α) :
    (canonicalStandardPositiveLevelBlock G F s p hs hp hp_top f hf k).toFunLt
        (souzaAtomFamily G s p hs hp hp_top) x =
      canonicalStandardLevelBlockFunction G F p s f hf k x := by
  classical
  unfold WeakGridSpace.LevelBlock.toFunLt canonicalStandardPositiveLevelBlock
    canonicalStandardLevelBlockFunction canonicalStandardCellBlockFunction
  simp only [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
    WeakGridSpace.levelCellToWeakGridCell, WeakGridSpace.AtomFamily.toFunction,
    souzaAtomFamily, souzaLocalVectorSpace]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro Q hQ
  let Qg : GoodGridCell G := { level := k, cell := Q.1, mem := Q.2 }
  have hchildren :
      (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
          if P ∈ childrenOfCell G Qg then
            standardChildCoeff G F s p f hf Qg P *
              (Set.indicator P.1
                (fun _ =>
                  (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x)
          else
            0) =
        ∑ P ∈ childrenOfCell G Qg,
          standardChildCoeff G F s p f hf Qg P *
            canonicalSouzaAtom G s p (childToGoodGridCell (G := G) (Q := Qg) P) x := by
    let term : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1) → ℂ := fun P =>
      standardChildCoeff G F s p f hf Qg P *
        (Set.indicator P.1
          (fun _ => (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x)
    calc
      (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
          if P ∈ childrenOfCell G Qg then term P else 0)
          =
        ∑ P ∈ (Finset.univ :
            Finset (WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1))),
          if P ∈ childrenOfCell G Qg then term P else 0 := by
          simp
      _ =
        ∑ P ∈ ((Finset.univ :
            Finset (WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1))).filter
              (fun P => P ∈ childrenOfCell G Qg)),
          term P := by
          rw [Finset.sum_filter]
      _ =
        ∑ P ∈ childrenOfCell G Qg,
          term P := by
          refine Finset.sum_congr ?_ ?_
          · ext P
            simp
          · intro P hP
            rfl
      _ =
        ∑ P ∈ childrenOfCell G Qg,
          standardChildCoeff G F s p f hf Qg P *
            canonicalSouzaAtom G s p (childToGoodGridCell (G := G) (Q := Qg) P) x := by
          refine Finset.sum_congr rfl ?_
          intro P hP
          simp [term, canonicalSouzaAtom, childToGoodGridCell, Set.indicator_apply]
  have hleft :
      (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
          (if hP : P ∈ childrenOfCell G Qg then
            standardChildCoeff G F s p f hf Qg P
          else
            0) *
            (Set.indicator P.1
              (fun _ =>
                (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x)) =
        ∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
          if P ∈ childrenOfCell G Qg then
            standardChildCoeff G F s p f hf Qg P *
              (Set.indicator P.1
                (fun _ =>
                  (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x)
          else
            0 := by
    refine Finset.sum_congr rfl ?_
    intro P hP
    by_cases h : P ∈ childrenOfCell G Qg <;> simp [h]
  change
    (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
        (if hP : P ∈ childrenOfCell G Qg then
          standardChildCoeff G F s p f hf Qg P
        else
          0) *
          (Set.indicator P.1
            (fun _ =>
              (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x)) =
      ∑ P ∈ childrenOfCell G Qg,
        standardChildCoeff G F s p f hf Qg P *
          canonicalSouzaAtom G s p (childToGoodGridCell (G := G) (Q := Qg) P) x
  rw [hleft]
  exact hchildren

/--
The positive standard `LevelBlock` gives the same `Lp` element as the
canonical-Souza level block used in the regrouped Haar expansion.
-/
theorem canonicalStandardPositiveLevelBlock_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) :
    (canonicalStandardPositiveLevelBlock G F s p hs hp hp_top f hf k).toLp
        (souzaAtomFamily G s p hs hp hp_top) =
      canonicalStandardLevelBlockToLp G F p p s f hf k := by
  apply MeasureTheory.Lp.ext
  refine
    (WeakGridSpace.LevelBlock.coeFn_toLp
      (souzaAtomFamily G s p hs hp hp_top)
      (canonicalStandardPositiveLevelBlock G F s p hs hp hp_top f hf k)).trans ?_
  have hfun :
      (canonicalStandardPositiveLevelBlock G F s p hs hp hp_top f hf k).toFunLt
          (souzaAtomFamily G s p hs hp hp_top)
        =ᵐ[G.grid.μ]
      canonicalStandardLevelBlockFunction G F p s f hf k :=
    Filter.Eventually.of_forall fun x =>
      canonicalStandardPositiveLevelBlock_toFunLt G F s p hs hp hp_top f hf k x
  exact hfun.trans
    (MemLp.coeFn_toLp (canonicalStandardLevelBlock_memLp G F p p s f hf k)).symm

private theorem l2normalizedHaar_alpha_const
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (x y : α) :
    HaarRepresentation.L2normalizedHaar G F
        (UnbalancedHaarWavelet.FullHaarSystem.Index.alpha : F.Index) x =
      HaarRepresentation.L2normalizedHaar G F
        (UnbalancedHaarWavelet.FullHaarSystem.Index.alpha : F.Index) y := by
  simp [HaarRepresentation.L2normalizedHaar, HaarRepresentation.l2NormalizationFactor,
    UnbalancedHaarWavelet.FullHaarSystem.function, F.alphaFunction_def,
    UnbalancedHaarWavelet.normalizedAlphaFunction]

/-- The Souza level block which represents the normalized Haar father term. -/
def canonicalStandardFatherLevelBlock
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) 0 where
  coeff := fun Q =>
    let Qg : GoodGridCell G := { level := 0, cell := Q.1, mem := Q.2 }
    let r : ℝ := (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹)
    HaarRepresentation.Coeff G F f hf .alpha *
      HaarRepresentation.L2normalizedHaar G F .alpha (cellPoint G Qg) / (r : ℂ)
  atom := fun Q =>
    (((G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)
  atom_mem := by
    intro Q
    change ‖((((G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ))‖ ≤
      (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹)
    have hnonneg :
        0 ≤ (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    simp [Complex.norm_real, Real.norm_of_nonneg hnonneg]

/--
The level-zero Souza block represents the father Haar term in `Lp`.
-/
theorem canonicalStandardFatherLevelBlock_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    (canonicalStandardFatherLevelBlock G F s p hs hp hp_top f hf).toLp
        (souzaAtomFamily G s p hs hp hp_top) =
      fatherHaarTermToLp G F p f hf := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let B := canonicalStandardFatherLevelBlock G F s p hs hp hp_top f hf
  apply MeasureTheory.Lp.ext
  refine (WeakGridSpace.LevelBlock.coeFn_toLp A B).trans ?_
  have hpoint :
      B.toFunLt A =ᵐ[G.grid.μ]
        fun x =>
          HaarRepresentation.Coeff G F f hf .alpha *
            HaarRepresentation.L2normalizedHaar G F .alpha x := by
    refine Filter.Eventually.of_forall ?_
    intro x
    unfold WeakGridSpace.LevelBlock.toFunLt
    simp only [A, B, canonicalStandardFatherLevelBlock, GoodGridSpace.toWeakGridSpace,
      GoodGridSpace.toWeakGrid, WeakGridSpace.levelCellToWeakGridCell,
      WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily, souzaLocalVectorSpace]
    let Qw : WeakGridSpace.LevelCell G.toWeakGridSpace 0 :=
      ⟨Set.univ, by
        change Set.univ ∈ G.grid.grid.partitions 0
        simp [G.grid.grid.first_partition_eq_univ]⟩
    have hsum :
        (∑ x_1 ∈ (G.grid.grid.partitions 0).attach,
            HaarRepresentation.Coeff G F f hf .alpha *
                  HaarRepresentation.L2normalizedHaar G F .alpha
                    (cellPoint G { level := 0, cell := x_1.1, mem := x_1.2 }) /
                (((G.grid.μ x_1.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ) *
              Set.indicator x_1.1
                (fun _ =>
                  (((G.grid.μ x_1.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x) =
          HaarRepresentation.Coeff G F f hf .alpha *
                HaarRepresentation.L2normalizedHaar G F .alpha
                  (cellPoint G { level := 0, cell := Qw.1, mem := Qw.2 }) /
              (((G.grid.μ Qw.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ) *
            Set.indicator Qw.1
              (fun _ =>
                (((G.grid.μ Qw.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x := by
      exact Finset.sum_eq_single Qw
        (by
          intro P hP hne
          have hP_univ : P.1 = Set.univ := by
            have hP_mem : P.1 ∈ G.grid.grid.partitions 0 := P.2
            rw [G.grid.grid.first_partition_eq_univ] at hP_mem
            exact Finset.mem_singleton.mp hP_mem
          exact False.elim (hne (Subtype.ext hP_univ))
        )
        (by
          intro hnot
          exact False.elim (hnot (Finset.mem_attach _ Qw))
        )
    change
      (∑ x_1 ∈ (G.grid.grid.partitions 0).attach,
          HaarRepresentation.Coeff G F f hf .alpha *
                HaarRepresentation.L2normalizedHaar G F .alpha
                  (cellPoint G { level := 0, cell := x_1.1, mem := x_1.2 }) /
              (((G.grid.μ x_1.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ) *
            Set.indicator x_1.1
              (fun _ =>
                (((G.grid.μ x_1.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x) =
        HaarRepresentation.Coeff G F f hf .alpha *
          HaarRepresentation.L2normalizedHaar G F .alpha x
    rw [hsum]
    simp only [Qw, Set.mem_univ, Set.indicator_of_mem]
    let Q : GoodGridCell G :=
      { level := 0, cell := Set.univ,
        mem := by simp [G.grid.grid.first_partition_eq_univ] }
    let r : ℝ := (G.grid.μ Set.univ).toReal ^ (s - (p.toReal)⁻¹)
    have hr_pos : 0 < r := by
      have hμ_pos : 0 < G.grid.μ Set.univ :=
        G.grid.positive_measure 0 Set.univ
          (by simp [G.grid.grid.first_partition_eq_univ])
      letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
      have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ :=
        MeasureTheory.measure_ne_top G.grid.μ Set.univ
      have hμ_toReal_pos : 0 < (G.grid.μ Set.univ).toReal :=
        ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
      exact Real.rpow_pos_of_pos hμ_toReal_pos _
    have halpha :
        HaarRepresentation.L2normalizedHaar G F .alpha (cellPoint G Q) =
          HaarRepresentation.L2normalizedHaar G F .alpha x :=
      l2normalizedHaar_alpha_const G F (cellPoint G Q) x
    change
      (HaarRepresentation.Coeff G F f hf .alpha *
          HaarRepresentation.L2normalizedHaar G F .alpha (cellPoint G Q) / (r : ℂ)) *
        (r : ℂ) =
      HaarRepresentation.Coeff G F f hf .alpha *
        HaarRepresentation.L2normalizedHaar G F .alpha x
    rw [halpha]
    field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt hr_pos)]
  have hfather :
      (fatherHaarTermToLp G F p f hf : α → ℂ) =ᵐ[G.grid.μ]
        fun x =>
          HaarRepresentation.Coeff G F f hf .alpha *
            HaarRepresentation.L2normalizedHaar G F .alpha x := by
    unfold fatherHaarTermToLp
    exact
      (Lp.coeFn_smul (HaarRepresentation.Coeff G F f hf .alpha)
        ((HaarRepresentation.l2normalizedHaar_memLp G F p .alpha).toLp
          (HaarRepresentation.L2normalizedHaar G F .alpha))).trans
        ((MemLp.coeFn_toLp
          (HaarRepresentation.l2normalizedHaar_memLp G F p .alpha)).fun_const_smul
            (HaarRepresentation.Coeff G F f hf .alpha))
  exact hpoint.trans hfather.symm

/-- Reindex the father term and positive levels as ordinary natural levels. -/
private def natEquivOptionNat : ℕ ≃ Option ℕ where
  toFun
    | 0 => none
    | k + 1 => some k
  invFun
    | none => 0
    | some k => k + 1
  left_inv := by
    intro n
    cases n with
    | zero => rfl
    | succ k => rfl
  right_inv := by
    intro ok
    cases ok with
    | none => rfl
    | some k => rfl

/--
The standard Souza blocks indexed by the actual grid level.

Level `0` is the father term; level `k + 1` is the canonical Souza form of the
standard Haar block coming from parents at level `k`.
-/
def canonicalStandardLpGridBlock
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    (n : ℕ) → WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) n
  | 0 => canonicalStandardFatherLevelBlock G F s p hs hp hp_top f hf
  | k + 1 => canonicalStandardPositiveLevelBlock G F s p hs hp hp_top f hf k

/--
The natural-level blocks evaluate to the corresponding terms of the already
proved `Option ℕ` expansion.
-/
theorem canonicalStandardLpGridBlock_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (n : ℕ) :
    (canonicalStandardLpGridBlock G F s p hs hp hp_top f hf n).toLp
        (souzaAtomFamily G s p hs hp hp_top) =
      canonicalStandardExpansionTermToLp G F p p s f hf (natEquivOptionNat n) := by
  cases n with
  | zero =>
      exact canonicalStandardFatherLevelBlock_toLp G F s p hs hp hp_top f hf
  | succ k =>
      exact canonicalStandardPositiveLevelBlock_toLp G F s p hs hp hp_top f hf k

/--
For `1 < p < ∞`, the standard canonical-Souza blocks form an
`LpGridRepresentation` of `f`.

This is the packaged form of the standard representation: the level-zero block
is the Haar father term, and each positive level is the regrouped Haar block
written with canonical Souza atoms.
-/
def standardLpGridRepresentation
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp_one : 1 < p) (hp_top : p < ∞)
    (f : α → ℂ) (hf : MemLp f p G.grid.μ) :
    letI : Fact (1 ≤ p) := ⟨le_of_lt hp_one⟩
    WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs (le_of_lt hp_one) (ne_of_lt hp_top))
      (hf.toLp f) := by
  classical
  letI : Fact (1 ≤ p) := ⟨le_of_lt hp_one⟩
  let hp : 1 ≤ p := le_of_lt hp_one
  let hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
  let hfint : Integrable f G.grid.μ := by
    letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
    exact hf.integrable (le_of_lt hp_one)
  refine
    { block := canonicalStandardLpGridBlock G F s p hs hp hp_ne_top f hfint
      hasSum := ?_ }
  have hoption :
      HasSum (canonicalStandardExpansionTermToLp G F p p s f hfint) (hf.toLp f) := by
    simpa [hfint] using
      hasSum_canonicalStandardExpansionTermToLp G F p hp_one hp_top p s f hf
  have hnat :
      HasSum
        (canonicalStandardExpansionTermToLp G F p p s f hfint ∘ natEquivOptionNat)
        (hf.toLp f) :=
    natEquivOptionNat.hasSum_iff.mpr hoption
  exact hnat.congr_fun fun n =>
    canonicalStandardLpGridBlock_toLp G F s p hs hp hp_ne_top f hfint n

/--
The level contribution in the standard atomic gauge.

Level `0` is handled by the father term in `standardRepresentationNorm`; this
block records the child coefficients created from Haar blocks at level `k`.
-/
def standardLevelCoeffPower (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) : ℝ≥0∞ :=
  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    ∑ P ∈ childrenOfCell G
        ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G),
      ENNReal.ofReal
        (‖standardChildCoeff G F s p f hf
          ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P‖ ^ p.toReal)

/--
The standard atomic representation gauge `N_st`.

It is allowed to take the value `∞`, since the coefficient series need not be
finite for an arbitrary input function.
-/
def standardRepresentationNorm (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p q : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖fatherCoeff G F s p f hf‖ +
    if q = ∞ then
      sSup (Set.range fun k => (standardLevelCoeffPower G F s p f hf k) ^ (1 / p.toReal))
    else
      (∑' k, (standardLevelCoeffPower G F s p f hf k) ^ (q.toReal / p.toReal)) ^
        (1 / q.toReal)

end StandardAtomicRepresentation

end

end GoodGridSpace
