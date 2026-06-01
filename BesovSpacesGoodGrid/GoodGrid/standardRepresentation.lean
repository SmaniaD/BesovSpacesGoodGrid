import BesovSpacesGoodGrid.GoodGrid.HaarRepresentationNorm

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
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) : ℂ :=
  (((G.grid.μ Set.univ).toReal ^ (1 / p.toReal - s - 1 / 2) : ℝ) : ℂ) *
    HaarRepresentation.coeff G F f .alpha

/--
The atom-side coefficient `c_{S,P}^f`.

The constant `c₂` is left explicit: it is the manuscript's normalization
constant used to turn the restricted Haar wavelet into a Souza atom.
-/
def branchCellCoeff (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (c₂ : ℝ) (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) : ℂ :=
  ((c₂ * (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) *
      (G.grid.μ P.1).toReal ^ (1 / p.toReal - s) : ℝ) : ℂ) *
    HaarRepresentation.coeff G F f (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))

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
    (((G.grid.μ Q.cell).toReal ^ (1 / 2) / c₂ *
        (G.grid.μ P.1).toReal ^ (s - 1 / p.toReal) : ℝ) : ℂ) *
      HaarRepresentation.normalizedFunction G F (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x
  else
    0

/--
The finite coefficient mass `\tilde{k}_P^f`.

Only the branches whose `S₁ ∪ S₂` contains `P` contribute.
-/
def tildeCoeff (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (c₂ : ℝ) (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) : ℝ := by
  classical
  exact ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
    if branchContainsCell G F Q P b then
      ‖branchCellCoeff G F c₂ p s f Q P b‖
    else
      0

/--
The averaged atom `\tilde{a}_P^f`.

When the normalizing mass is zero, this definition returns the zero function.
For positive mass it is exactly the convex average from the manuscript.
-/
def tildeAtom (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (c₂ : ℝ) (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (x : α) : ℂ := by
  classical
  exact if hzero : tildeCoeff G F c₂ p s f Q P = 0 then
    0
  else
    ((tildeCoeff G F c₂ p s f Q P)⁻¹ : ℂ) *
      ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
        if branchContainsCell G F Q P b then
          branchCellCoeff G F c₂ p s f Q P b *
            branchCellAtom G F c₂ p s Q P b x
        else
          0

/-- A distinguished point of a good-grid cell. -/
def cellPoint (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) : α :=
  Classical.choose (G.grid.partition_nonempty Q.level Q.cell Q.mem)

/-- The chosen point really belongs to its cell. -/
theorem cellPoint_mem (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) :
    cellPoint G Q ∈ Q.cell :=
  Classical.choose_spec (G.grid.partition_nonempty Q.level Q.cell Q.mem)

/--
The standard coefficient `k_P^f` associated with a child `P ⊆ Q`.

This is the point-evaluation formula from the manuscript, using the chosen
representative point `x_P`.
-/
def standardChildCoeff (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) : ℂ := by
  classical
  let Pcell := childToGoodGridCell (G := G) (Q := Q) P
  exact (((G.grid.μ P.1).toReal ^ (-(s - 1 / p.toReal)) : ℝ) : ℂ) *
    ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
      if branchContainsCell G F Q P b then
        HaarRepresentation.coeff G F f (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
          HaarRepresentation.normalizedFunction G F (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))
            (cellPoint G Pcell)
      else
        0

/--
The level contribution in the standard atomic gauge.

Level `0` is handled by the father term in `standardRepresentationNorm`; this
block records the child coefficients created from Haar blocks at level `k`.
-/
def standardLevelCoeffPower (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (k : ℕ) : ℝ≥0∞ :=
  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    ∑ P ∈ childrenOfCell G
        ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G),
      ENNReal.ofReal
        (‖standardChildCoeff G F s p f
          ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P‖ ^ p.toReal)

/--
The standard atomic representation gauge `N_st`.

It is allowed to take the value `∞`, since the coefficient series need not be
finite for an arbitrary input function.
-/
def standardRepresentationNorm (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p q : ℝ≥0∞) (f : α → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖fatherCoeff G F s p f‖ +
    if q = ∞ then
      sSup (Set.range fun k => (standardLevelCoeffPower G F s p f k) ^ (1 / p.toReal))
    else
      (∑' k, (standardLevelCoeffPower G F s p f k) ^ (q.toReal / p.toReal)) ^
        (1 / q.toReal)

end StandardAtomicRepresentation

end

end GoodGridSpace
