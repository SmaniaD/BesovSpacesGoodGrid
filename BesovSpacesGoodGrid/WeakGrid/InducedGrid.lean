import BesovSpacesGoodGrid.WeakGrid.BesovishSpaces

/-!
# Induced Besov-ish spaces on a cell

This file formalizes the induced grid construction from a fixed grid cell.  If
`Q ∈ P^{k₀}`, the induced level `i` consists of the cells
`P ∈ P^{k₀+i}` with `P ⊆ Q`.  The induced atom family is simply the original
atom family restricted to those induced cells.

The main result is `InducedBesovishWeakContraction`: the identity inclusion
from the induced Besov-ish space on `Q` into the ambient Besov-ish space is
well-defined and has norm at most `1`.  The proof is by direct reindexing of
atomic representations:

* an induced block at level `i` is embedded into the ambient level `k₀+i`;
* ambient cells outside `Q` receive coefficient `0`;
* an induced representation is shifted by `k₀`, with zero blocks before `k₀`;
* the `(p,q)` coefficient cost does not increase, so the Besov-ish gauge does
  not increase.

The induced grid is modeled on the same ambient type and measure as the original
weak grid.  This is the most lightweight representation compatible with the
current `WeakGridSpace` API, where `Lp` spaces are attached to measures on the
ambient type `α`.

The file also contains the pointwise helper `restrictFunctionToCell` for the
operator `f ↦ f * 1_Q`.  Its boundedness as an operator into `L^p`, and the
negative examples where it does not land in the induced Besov-ish space, are not
proved in this file.
-/

namespace WeakGridSpace

open scoped ENNReal BigOperators
open MeasureTheory

universe u v

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/-- The level-`i` family of the grid induced by a cell `Q ∈ P^{k₀}`. -/
def inducedPartitions (G : WeakGridSpace (α := α)) {k₀ : ℕ}
    (Q : LevelCell G k₀) (i : ℕ) : Finset (Set α) :=
  by
    classical
    exact (G.grid.partitions (k₀ + i)).filter fun P => P ⊆ Q.1

theorem mem_inducedPartitions_iff
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {i : ℕ} {P : Set α} :
    P ∈ inducedPartitions G Q i ↔ P ∈ G.grid.partitions (k₀ + i) ∧ P ⊆ Q.1 := by
  simp [inducedPartitions]

/-- Every induced cell is contained in the parent cell `Q`. -/
theorem induced_cell_subset_parent
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {i : ℕ} {P : Set α} (hP : P ∈ inducedPartitions G Q i) :
    P ⊆ Q.1 :=
  (mem_inducedPartitions_iff G Q).mp hP |>.2

/--
The weak grid induced by a cell `Q ∈ P^{k₀}`.

Its `i`-th level is `P_Q^i = {P ∈ P^{k₀+i} | P ⊆ Q}`.  The measure is kept as
the ambient measure; all cells are still subsets of `Q`, so this realizes the
induced space as a sub-grid of the original ambient measurable space.
-/
def inducedWeakGrid (G : WeakGridSpace (α := α)) {k₀ : ℕ}
    (Q : LevelCell G k₀) : WeakGrid (α := α) where
  μ := G.measure
  isFinite := G.grid.isFinite
  partitions := inducedPartitions G Q
  measurable := by
    intro i P hP
    exact G.grid.measurable (k₀ + i) P ((mem_inducedPartitions_iff G Q).mp hP).1
  positive_measure := by
    intro i P hP
    exact G.grid.positive_measure (k₀ + i) P ((mem_inducedPartitions_iff G Q).mp hP).1
  exists_nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨Q.1, ?_⟩
    simp [inducedPartitions, Q.2]
  Cmult1 := G.grid.Cmult1
  overlap_card_le := by
    intro i P hP
    have hP_ambient : P ∈ G.grid.partitions (k₀ + i) :=
      ((mem_inducedPartitions_iff G Q).mp hP).1
    refine (Finset.card_le_card ?_).trans
      (G.grid.overlap_card_le (k₀ + i) P hP_ambient)
    intro R hR
    simp only [overlapFinset, Finset.mem_filter] at hR ⊢
    exact ⟨((mem_inducedPartitions_iff G Q).mp hR.1).1, hR.2⟩

/-- The weak-grid space induced by a cell. -/
def inducedWeakGridSpace (G : WeakGridSpace (α := α)) {k₀ : ℕ}
    (Q : LevelCell G k₀) : WeakGridSpace (α := α) where
  grid := inducedWeakGrid G Q

/-- A level cell in the induced grid, viewed as the corresponding ambient cell. -/
def inducedLevelCellToAmbient
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    (P : LevelCell (inducedWeakGridSpace G Q) i) : LevelCell G (k₀ + i) :=
  ⟨P.1, ((mem_inducedPartitions_iff G Q).mp P.2).1⟩

/-- Rebuilding an induced cell from its ambient cell data gives back the same induced cell. -/
@[simp]
theorem inducedLevelCell_mk_inducedLevelCellToAmbient
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    (P : LevelCell (inducedWeakGridSpace G Q) i)
    (hP : (inducedLevelCellToAmbient G Q P).1 ∈
      (inducedWeakGridSpace G Q).grid.partitions i) :
    (⟨(inducedLevelCellToAmbient G Q P).1, hP⟩ :
      LevelCell (inducedWeakGridSpace G Q) i) = P := by
  ext
  rfl

theorem inducedLevelCell_subset_parent
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    (P : LevelCell (inducedWeakGridSpace G Q) i) :
    P.1 ⊆ Q.1 :=
  ((mem_inducedPartitions_iff G Q (i := i)).mp P.2).2

/-- A cell of the ambient level `k₀+i` lying inside `Q`, viewed as an induced cell. -/
def ambientLevelCellToInduced
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    (P : LevelCell G (k₀ + i)) (hP : P.1 ⊆ Q.1) :
    LevelCell (inducedWeakGridSpace G Q) i :=
  ⟨P.1, by
    simp [inducedWeakGridSpace, inducedWeakGrid, inducedPartitions, hP, P.2]⟩

/-- Viewing an induced cell as ambient and then back as induced is the identity. -/
@[simp]
theorem ambientLevelCellToInduced_inducedLevelCellToAmbient
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    (P : LevelCell (inducedWeakGridSpace G Q) i)
    (hP : (inducedLevelCellToAmbient G Q P).1 ⊆ Q.1) :
    ambientLevelCellToInduced G Q (inducedLevelCellToAmbient G Q P) hP = P := by
  ext
  rfl

/-- Induced cells at level `i` are exactly ambient cells at level `k₀+i`
contained in the parent `Q`. -/
def inducedLevelCellEquivSubtype
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀) :
    LevelCell (inducedWeakGridSpace G Q) i ≃
      {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1} where
  toFun P :=
    ⟨inducedLevelCellToAmbient G Q P, inducedLevelCell_subset_parent G Q P⟩
  invFun P :=
    ambientLevelCellToInduced G Q P.1 P.2
  left_inv P := by
    ext
    rfl
  right_inv P := by
    ext
    rfl

/-- A weak-grid cell in the induced grid, viewed as an ambient weak-grid cell. -/
def inducedWeakGridCellToAmbient
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    (P : WeakGridCell (inducedWeakGridSpace G Q)) : WeakGridCell G where
  level := k₀ + P.level
  cell := P.cell
  mem := ((mem_inducedPartitions_iff G Q).mp P.mem).1

/-- The ambient weak-grid cell associated to an induced level cell is the expected level shift. -/
@[simp]
theorem inducedWeakGridCellToAmbient_levelCellToWeakGridCell
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    (P : LevelCell (inducedWeakGridSpace G Q) i) :
    inducedWeakGridCellToAmbient G Q
        (levelCellToWeakGridCell (inducedWeakGridSpace G Q) i P) =
      levelCellToWeakGridCell G (k₀ + i) (inducedLevelCellToAmbient G Q P) := by
  rfl

/--
The atom family induced on `Q`, obtained by restricting the ambient atom family
to the induced cells.
-/
def inducedAtomFamily
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} (A : AtomFamily G s p u) :
    AtomFamily (inducedWeakGridSpace G Q) s p u where
  uConj := A.uConj
  s_pos := A.s_pos
  one_le_p := A.one_le_p
  p_ne_top := A.p_ne_top
  one_le_u := A.one_le_u
  holder_conjugate := A.holder_conjugate
  localSpace := fun P => A.localSpace (inducedWeakGridCellToAmbient G Q P)
  atoms := fun P => A.atoms (inducedWeakGridCellToAmbient G Q P)
  atoms_nonempty := fun P => A.atoms_nonempty (inducedWeakGridCellToAmbient G Q P)
  local_memLp := by
    intro P φ
    exact A.local_memLp (inducedWeakGridCellToAmbient G Q P) φ
  local_support := by
    intro P φ x hx
    exact A.local_support (inducedWeakGridCellToAmbient G Q P) φ x hx
  atoms_convex := fun P => A.atoms_convex (inducedWeakGridCellToAmbient G Q P)
  atoms_phase_invariant := by
    intro P φ σ hφ hσ
    exact A.atoms_phase_invariant (inducedWeakGridCellToAmbient G Q P) φ σ hφ hσ
  atom_bound := by
    intro P φ hφ
    simpa [atomMeasureScale, inducedWeakGridSpace, inducedWeakGrid,
      inducedWeakGridCellToAmbient, WeakGridSpace.measure] using
      A.atom_bound (inducedWeakGridCellToAmbient G Q P) φ hφ

/--
Embed one induced level block into the corresponding ambient level `k₀+i`.

Cells outside the parent `Q` receive coefficient `0`; their atom choice is
irrelevant but needed to build a full ambient `LevelBlock`.
-/
def inducedLevelBlockToAmbient
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} (A : AtomFamily G s p u)
    (B : LevelBlock (inducedAtomFamily G Q A) i) : LevelBlock A (k₀ + i) := by
  classical
  refine
    { coeff := fun P =>
        if hP : P.1 ⊆ Q.1 then
          B.coeff (ambientLevelCellToInduced G Q P hP)
        else
          0
      atom := fun P =>
        if hP : P.1 ⊆ Q.1 then
          B.atom (ambientLevelCellToInduced G Q P hP)
        else
          Classical.choose (A.atoms_nonempty_on (levelCellToWeakGridCell G (k₀ + i) P))
      atom_mem := ?_ }
  intro P
  by_cases hP : P.1 ⊆ Q.1
  · simpa [inducedAtomFamily, inducedWeakGridCellToAmbient, ambientLevelCellToInduced,
      levelCellToWeakGridCell, hP]
      using B.atom_mem (ambientLevelCellToInduced G Q P hP)
  · simp [hP, Classical.choose_spec (A.atoms_nonempty_on (levelCellToWeakGridCell G (k₀ + i) P))]

/-- On an induced cell, the embedded ambient block has exactly the original coefficient. -/
@[simp]
theorem inducedLevelBlockToAmbient_coeff_inducedLevelCellToAmbient
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} (A : AtomFamily G s p u)
    (B : LevelBlock (inducedAtomFamily G Q A) i)
    (P : LevelCell (inducedWeakGridSpace G Q) i) :
    (inducedLevelBlockToAmbient G Q A B).coeff (inducedLevelCellToAmbient G Q P) =
      B.coeff P := by
  by_cases h : (inducedLevelCellToAmbient G Q P).1 ⊆ Q.1
  · have hcell : ambientLevelCellToInduced G Q (inducedLevelCellToAmbient G Q P) h = P := by
      ext
      rfl
    simp [inducedLevelBlockToAmbient, h, hcell]
  · exact False.elim (h (inducedLevelCell_subset_parent G Q P))

/--
On an induced cell, the embedded ambient block contributes exactly the original
`L^p` term.  The proof uses `MemLp.toLp_congr` only to ignore proof-irrelevant
choices of `MemLp` witnesses.
-/
@[simp]
theorem inducedLevelBlockToAmbient_term_inducedLevelCellToAmbient
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    (B : LevelBlock (inducedAtomFamily G Q A) i)
    (P : LevelCell (inducedWeakGridSpace G Q) i) :
    (inducedLevelBlockToAmbient G Q A B).term A (inducedLevelCellToAmbient G Q P) =
      B.term (inducedAtomFamily G Q A) P := by
  by_cases h : (inducedLevelCellToAmbient G Q P).1 ⊆ Q.1
  · have hcell : ambientLevelCellToInduced G Q (inducedLevelCellToAmbient G Q P) h = P := by
      ext
      rfl
    simp only [LevelBlock.term, inducedLevelBlockToAmbient]
    simp only [dif_pos h]
    cases hcell
    have hraw :
        (⟨(inducedLevelCellToAmbient G Q P).1, by
            simpa [inducedLevelCellToAmbient] using P.2⟩ :
          LevelCell (inducedWeakGridSpace G Q) i) = P := by
      ext
      rfl
    cases hraw
    simp only [AtomFamily.toFunction, inducedAtomFamily, inducedWeakGridCellToAmbient,
      ambientLevelCellToInduced, levelCellToWeakGridCell, inducedLevelCellToAmbient]
    apply congrArg (fun z : Lp ℂ p G.measure => B.coeff P • z)
    apply MeasureTheory.MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun _ => rfl
  · exact False.elim (h (inducedLevelCell_subset_parent G Q P))

/-- The embedded level block has the same `L^p` value as the induced block. -/
theorem inducedLevelBlockToAmbient_toLp
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    (B : LevelBlock (inducedAtomFamily G Q A) i) :
    (inducedLevelBlockToAmbient G Q A B).toLp A =
      B.toLp (inducedAtomFamily G Q A) := by
  classical
  let F : LevelCell G (k₀ + i) → Lp ℂ p G.measure :=
    fun P => (inducedLevelBlockToAmbient G Q A B).term A P
  have hcomp : (∑ P : {P : LevelCell G (k₀ + i) // ¬ P.1 ⊆ Q.1}, F P) = 0 := by
    apply Finset.sum_eq_zero
    intro P _hP
    exact by
      simp [F, LevelBlock.term, inducedLevelBlockToAmbient, P.2]
  have hsub :
      (∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P) =
        B.toLp (inducedAtomFamily G Q A) := by
    symm
    rw [LevelBlock.toLp]
    refine Fintype.sum_equiv (inducedLevelCellEquivSubtype G Q)
      (fun P => B.term (inducedAtomFamily G Q A) P)
      (fun P => F P.1) ?_
    intro P
    simpa [F, inducedLevelCellEquivSubtype] using
      (inducedLevelBlockToAmbient_term_inducedLevelCellToAmbient
        (G := G) Q A B P).symm
  calc
    (inducedLevelBlockToAmbient G Q A B).toLp A
        = ∑ P : LevelCell G (k₀ + i), F P := by
          simp [F, LevelBlock.toLp]
    _ = (∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P) +
          ∑ P : {P : LevelCell G (k₀ + i) // ¬ P.1 ⊆ Q.1}, F P := by
          rw [Fintype.sum_subtype_add_sum_subtype (fun P : LevelCell G (k₀ + i) => P.1 ⊆ Q.1) F]
    _ = ∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P := by
          simp [hcomp]
    _ = B.toLp (inducedAtomFamily G Q A) := hsub

/-- The embedded level block has exactly the same coefficient power. -/
theorem inducedLevelBlockToAmbient_levelCoeffPower
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    (B : LevelBlock (inducedAtomFamily G Q A) i) :
    ∑ P : LevelCell G (k₀ + i),
        ‖(inducedLevelBlockToAmbient G Q A B).coeff P‖ ^ p.toReal =
      ∑ P : LevelCell (inducedWeakGridSpace G Q) i,
        ‖B.coeff P‖ ^ p.toReal := by
  classical
  let F : LevelCell G (k₀ + i) → ℝ :=
    fun P => ‖(inducedLevelBlockToAmbient G Q A B).coeff P‖ ^ p.toReal
  have hp_toReal_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le A.one_le_p).ne' A.p_ne_top
  have hcomp : (∑ P : {P : LevelCell G (k₀ + i) // ¬ P.1 ⊆ Q.1}, F P) = 0 := by
    apply Finset.sum_eq_zero
    intro P _hP
    exact by
      simp [F, inducedLevelBlockToAmbient, P.2, Real.zero_rpow hp_toReal_pos.ne']
  have hsub :
      (∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P) =
        ∑ P : LevelCell (inducedWeakGridSpace G Q) i, ‖B.coeff P‖ ^ p.toReal := by
    symm
    refine Fintype.sum_equiv (inducedLevelCellEquivSubtype G Q)
      (fun P => ‖B.coeff P‖ ^ p.toReal)
      (fun P => F P.1) ?_
    intro P
    simpa [F, inducedLevelCellEquivSubtype] using
      congrArg (fun z : ℂ => ‖z‖ ^ p.toReal)
        (inducedLevelBlockToAmbient_coeff_inducedLevelCellToAmbient
          (G := G) Q A B P).symm
  calc
    ∑ P : LevelCell G (k₀ + i),
        ‖(inducedLevelBlockToAmbient G Q A B).coeff P‖ ^ p.toReal
        = ∑ P : LevelCell G (k₀ + i), F P := rfl
    _ = (∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P) +
          ∑ P : {P : LevelCell G (k₀ + i) // ¬ P.1 ⊆ Q.1}, F P := by
          rw [Fintype.sum_subtype_add_sum_subtype (fun P : LevelCell G (k₀ + i) => P.1 ⊆ Q.1) F]
    _ = ∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P := by
          simp [hcomp]
    _ = ∑ P : LevelCell (inducedWeakGridSpace G Q) i, ‖B.coeff P‖ ^ p.toReal := hsub

/--
One-level weak contraction for the induced inclusion.

Embedding an induced level block into the ambient level `k₀+i` is just a
reindexing of the cells contained in `Q`, with zero coefficients elsewhere.
Consequently the `L^p` block value and the coefficient power are preserved
with constant `1`.
-/
theorem inducedLevelBlockToAmbient_weakContraction
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    (B : LevelBlock (inducedAtomFamily G Q A) i) :
    (inducedLevelBlockToAmbient G Q A B).toLp A =
        B.toLp (inducedAtomFamily G Q A) ∧
      ∑ P : LevelCell G (k₀ + i),
          ‖(inducedLevelBlockToAmbient G Q A B).coeff P‖ ^ p.toReal =
        ∑ P : LevelCell (inducedWeakGridSpace G Q) i,
          ‖B.coeff P‖ ^ p.toReal :=
  ⟨inducedLevelBlockToAmbient_toLp G Q A B,
    inducedLevelBlockToAmbient_levelCoeffPower G Q A B⟩

/--
Restrict an ambient level block to the descendants of a parent cell.

If `Q` is a level-`k₀` cell and `B` lives on ambient level `k₀+i`, this keeps
exactly the coefficients and atoms on cells contained in `Q`, now regarded as a
level-`i` block for the induced grid on `Q`.
-/
def ambientLevelBlockToInduced
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} (A : AtomFamily G s p u)
    (B : LevelBlock A (k₀ + i)) :
    LevelBlock (inducedAtomFamily G Q A) i where
  coeff P := B.coeff (inducedLevelCellToAmbient G Q P)
  atom P := B.atom (inducedLevelCellToAmbient G Q P)
  atom_mem P := by
    simpa [inducedAtomFamily, inducedWeakGridCellToAmbient_levelCellToWeakGridCell]
      using B.atom_mem (inducedLevelCellToAmbient G Q P)

@[simp]
theorem ambientLevelBlockToInduced_coeff
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} (A : AtomFamily G s p u)
    (B : LevelBlock A (k₀ + i))
    (P : LevelCell (inducedWeakGridSpace G Q) i) :
    (ambientLevelBlockToInduced G Q A B).coeff P =
      B.coeff (inducedLevelCellToAmbient G Q P) :=
  rfl

@[simp]
theorem ambientLevelBlockToInduced_atom
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} (A : AtomFamily G s p u)
    (B : LevelBlock A (k₀ + i))
    (P : LevelCell (inducedWeakGridSpace G Q) i) :
    (ambientLevelBlockToInduced G Q A B).atom P =
      B.atom (inducedLevelCellToAmbient G Q P) :=
  rfl

/-- The atom of the induced-from-ambient block has the same `toFunction` as the
original ambient atom on the corresponding ambient cell. -/
theorem ambientLevelBlockToInduced_atom_toFunction
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} (A : AtomFamily G s p u)
    (B : LevelBlock A (k₀ + i))
    (P : LevelCell (inducedWeakGridSpace G Q) i) (x : α) :
    (inducedAtomFamily G Q A).toFunction
        (levelCellToWeakGridCell (inducedWeakGridSpace G Q) i P)
        ((ambientLevelBlockToInduced G Q A B).atom P) x =
      A.toFunction
        (levelCellToWeakGridCell G (k₀ + i) (inducedLevelCellToAmbient G Q P))
        (B.atom (inducedLevelCellToAmbient G Q P)) x :=
  rfl

/--
The coefficient power of the block restricted to an induced cell is bounded by
the coefficient power of the full ambient block.
-/
theorem ambientLevelBlockToInduced_coeffPower_le
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} (A : AtomFamily G s p u)
    (B : LevelBlock A (k₀ + i)) :
    (∑ P : LevelCell (inducedWeakGridSpace G Q) i,
        ‖(ambientLevelBlockToInduced G Q A B).coeff P‖ ^ p.toReal)
      ≤ ∑ P : LevelCell G (k₀ + i), ‖B.coeff P‖ ^ p.toReal := by
  classical
  let F : LevelCell G (k₀ + i) → ℝ := fun P => ‖B.coeff P‖ ^ p.toReal
  have hsub :
      (∑ P : LevelCell (inducedWeakGridSpace G Q) i,
          ‖(ambientLevelBlockToInduced G Q A B).coeff P‖ ^ p.toReal)
        =
          ∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P := by
    refine Fintype.sum_equiv (inducedLevelCellEquivSubtype G Q)
      (fun P : LevelCell (inducedWeakGridSpace G Q) i =>
        ‖(ambientLevelBlockToInduced G Q A B).coeff P‖ ^ p.toReal)
      (fun P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1} => F P.1) ?_
    intro P
    rfl
  have hsplit :
      (∑ P : LevelCell G (k₀ + i), F P) =
        (∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P) +
          ∑ P : {P : LevelCell G (k₀ + i) // ¬ P.1 ⊆ Q.1}, F P := by
    rw [Fintype.sum_subtype_add_sum_subtype (fun P : LevelCell G (k₀ + i) => P.1 ⊆ Q.1) F]
  have hcomp_nonneg :
      0 ≤ ∑ P : {P : LevelCell G (k₀ + i) // ¬ P.1 ⊆ Q.1}, F P :=
    Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [hsub, hsplit]
  exact le_add_of_nonneg_right hcomp_nonneg

/--
Restricting an ambient block to an induced grid does not change a cell term on
cells contained in the parent cell.
-/
@[simp]
theorem ambientLevelBlockToInduced_term
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    (B : LevelBlock A (k₀ + i))
    (P : LevelCell (inducedWeakGridSpace G Q) i) :
    (ambientLevelBlockToInduced G Q A B).term (inducedAtomFamily G Q A) P =
      B.term A (inducedLevelCellToAmbient G Q P) := by
  simp only [LevelBlock.term, ambientLevelBlockToInduced_coeff,
    ambientLevelBlockToInduced_atom]
  apply congrArg (fun z : Lp ℂ p G.measure =>
    B.coeff (inducedLevelCellToAmbient G Q P) • z)
  apply MeasureTheory.MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun _ => rfl

/--
If an ambient block has zero coefficients outside the parent cell, then reading
it as an induced block preserves its `L^p` value.
-/
theorem ambientLevelBlockToInduced_toLp_of_coeff_eq_zero
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    (B : LevelBlock A (k₀ + i))
    (hzero : ∀ P : LevelCell G (k₀ + i), ¬ P.1 ⊆ Q.1 → B.coeff P = 0) :
    (ambientLevelBlockToInduced G Q A B).toLp (inducedAtomFamily G Q A) =
      B.toLp A := by
  classical
  let F : LevelCell G (k₀ + i) → Lp ℂ p G.measure := fun P => B.term A P
  have hcomp : (∑ P : {P : LevelCell G (k₀ + i) // ¬ P.1 ⊆ Q.1}, F P) = 0 := by
    apply Finset.sum_eq_zero
    intro P _hP
    simp [F, LevelBlock.term, hzero P.1 P.2]
  have hsub :
      (ambientLevelBlockToInduced G Q A B).toLp (inducedAtomFamily G Q A) =
        ∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P := by
    rw [LevelBlock.toLp]
    refine Fintype.sum_equiv (inducedLevelCellEquivSubtype G Q)
      (fun P => (ambientLevelBlockToInduced G Q A B).term
        (inducedAtomFamily G Q A) P)
      (fun P => F P.1) ?_
    intro P
    exact ambientLevelBlockToInduced_term G Q A B P
  have hsplit :
      (∑ P : LevelCell G (k₀ + i), F P) =
        (∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P) +
          ∑ P : {P : LevelCell G (k₀ + i) // ¬ P.1 ⊆ Q.1}, F P := by
    rw [Fintype.sum_subtype_add_sum_subtype (fun P : LevelCell G (k₀ + i) => P.1 ⊆ Q.1) F]
  calc
    (ambientLevelBlockToInduced G Q A B).toLp (inducedAtomFamily G Q A)
        = ∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P := hsub
    _ = ∑ P : LevelCell G (k₀ + i), F P := by
          rw [hsplit, hcomp, add_zero]
    _ = B.toLp A := by
          simp [F, LevelBlock.toLp]

/--
If an ambient block has zero coefficients outside the parent cell, then its
coefficient power is unchanged when it is read as an induced block.
-/
theorem ambientLevelBlockToInduced_coeffPower_eq_of_coeff_eq_zero
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} (A : AtomFamily G s p u)
    (B : LevelBlock A (k₀ + i))
    (hzero : ∀ P : LevelCell G (k₀ + i), ¬ P.1 ⊆ Q.1 → B.coeff P = 0) :
    (∑ P : LevelCell (inducedWeakGridSpace G Q) i,
        ‖(ambientLevelBlockToInduced G Q A B).coeff P‖ ^ p.toReal) =
      ∑ P : LevelCell G (k₀ + i), ‖B.coeff P‖ ^ p.toReal := by
  classical
  let F : LevelCell G (k₀ + i) → ℝ := fun P => ‖B.coeff P‖ ^ p.toReal
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le A.one_le_p).ne' A.p_ne_top
  have hcomp : (∑ P : {P : LevelCell G (k₀ + i) // ¬ P.1 ⊆ Q.1}, F P) = 0 := by
    apply Finset.sum_eq_zero
    intro P _hP
    simp [F, hzero P.1 P.2, Real.zero_rpow hp_pos.ne']
  have hsub :
      (∑ P : LevelCell (inducedWeakGridSpace G Q) i,
          ‖(ambientLevelBlockToInduced G Q A B).coeff P‖ ^ p.toReal)
        =
          ∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P := by
    refine Fintype.sum_equiv (inducedLevelCellEquivSubtype G Q)
      (fun P : LevelCell (inducedWeakGridSpace G Q) i =>
        ‖(ambientLevelBlockToInduced G Q A B).coeff P‖ ^ p.toReal)
      (fun P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1} => F P.1) ?_
    intro P
    rfl
  have hsplit :
      (∑ P : LevelCell G (k₀ + i), F P) =
        (∑ P : {P : LevelCell G (k₀ + i) // P.1 ⊆ Q.1}, F P) +
          ∑ P : {P : LevelCell G (k₀ + i) // ¬ P.1 ⊆ Q.1}, F P := by
    rw [Fintype.sum_subtype_add_sum_subtype (fun P : LevelCell G (k₀ + i) => P.1 ⊆ Q.1) F]
  rw [hsub, hsplit, hcomp, add_zero]

/--
An ambient representation supported in the parent cell, with zero `L^p` blocks
before the parent level, can be read as a representation on the induced grid.

This is the representation-level version of the paper bookkeeping: first build
the restricted representation in the original grid, with coefficients zero
before and outside the cell, and only then reindex it as an induced
representation.
-/
def ambientSupportedRepresentationToInduced
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p G.measure}
    (R : LpGridRepresentation A f)
    (hbefore : ∀ n, n < k₀ → (R.block n).toLp A = 0)
    (houtside : ∀ n (P : LevelCell G n), ¬ P.1 ⊆ Q.1 → (R.block n).coeff P = 0) :
    LpGridRepresentation (inducedAtomFamily G Q A) f := by
  classical
  let B : (i : ℕ) → LevelBlock (inducedAtomFamily G Q A) i :=
    fun i => ambientLevelBlockToInduced G Q A (R.block (k₀ + i))
  refine
    { block := B
      hasSum := ?_ }
  let F : ℕ → Lp ℂ p G.measure := fun n => (R.block n).toLp A
  have hprefix : (∑ n ∈ Finset.range k₀, F n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact hbefore n (Finset.mem_range.mp hn)
  have hfull : HasSum F (f + ∑ n ∈ Finset.range k₀, F n) := by
    simpa [F, hprefix] using R.hasSum
  have htail : HasSum (fun n => F (n + k₀)) f := by
    simpa [hprefix] using (hasSum_nat_add_iff k₀).mpr hfull
  have hrewrite :
      (fun i => (B i).toLp (inducedAtomFamily G Q A)) =
        fun i => F (i + k₀) := by
    funext i
    simp [B, F, Nat.add_comm,
      ambientLevelBlockToInduced_toLp_of_coeff_eq_zero G Q A
        (R.block (k₀ + i)) (fun P hP => houtside (k₀ + i) P hP)]
  simpa [hrewrite]
    using htail

/--
The induced representation obtained from an ambient supported representation
has exactly the shifted ambient coefficient power.
-/
@[simp]
theorem ambientSupportedRepresentationToInduced_levelCoeffPower
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p G.measure}
    (R : LpGridRepresentation A f)
    (hbefore : ∀ n, n < k₀ → (R.block n).toLp A = 0)
    (houtside : ∀ n (P : LevelCell G n), ¬ P.1 ⊆ Q.1 → (R.block n).coeff P = 0) :
    (ambientSupportedRepresentationToInduced G Q A R hbefore houtside).levelCoeffPower i =
      R.levelCoeffPower (k₀ + i) := by
  simpa [ambientSupportedRepresentationToInduced, LpGridRepresentation.levelCoeffPower]
    using
      ambientLevelBlockToInduced_coeffPower_eq_of_coeff_eq_zero G Q A
        (R.block (k₀ + i)) (fun P hP => houtside (k₀ + i) P hP)

/--
Finite `(p,q)` coefficient cost passes from an ambient supported
representation to the induced representation read from it.
-/
theorem ambientSupportedRepresentationToInduced_finitePQCost
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A : AtomFamily G s p u)
    {f : Lp ℂ p G.measure}
    (R : LpGridRepresentation A f)
    (hbefore : ∀ n, n < k₀ → (R.block n).toLp A = 0)
    (houtside : ∀ n (P : LevelCell G n), ¬ P.1 ⊆ Q.1 → (R.block n).coeff P = 0)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R) :
    LpGridRepresentation.FinitePQCost (q := q)
      (ambientSupportedRepresentationToInduced G Q A R hbefore houtside) := by
  classical
  let Ri := ambientSupportedRepresentationToInduced G Q A R hbefore houtside
  by_cases hq : q = ∞
  · simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin ⊢
    rcases hRfin with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro x ⟨i, rfl⟩
    change Ri.levelCoeffPower i ^ (1 / p.toReal) ≤ C
    simpa [Ri, ambientSupportedRepresentationToInduced_levelCoeffPower
      (G := G) Q A R hbefore houtside] using hC ⟨k₀ + i, rfl⟩
  · simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin ⊢
    have htail :
        Summable fun i =>
          (R.levelCoeffPower (i + k₀)) ^ (q.toReal / p.toReal) :=
      (summable_nat_add_iff k₀).mpr hRfin
    refine htail.congr ?_
    intro i
    rw [ambientSupportedRepresentationToInduced_levelCoeffPower
      (G := G) Q A R hbefore houtside]
    rw [Nat.add_comm]

/--
Reading an ambient supported representation on the induced grid does not
increase its `(p,q)` coefficient cost.
-/
theorem ambientSupportedRepresentationToInduced_pqCost_le
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A : AtomFamily G s p u)
    {f : Lp ℂ p G.measure}
    (R : LpGridRepresentation A f)
    (hbefore : ∀ n, n < k₀ → (R.block n).toLp A = 0)
    (houtside : ∀ n (P : LevelCell G n), ¬ P.1 ⊆ Q.1 → (R.block n).coeff P = 0)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R) :
    LpGridRepresentation.pqCost (q := q)
        (ambientSupportedRepresentationToInduced G Q A R hbefore houtside) ≤
      LpGridRepresentation.pqCost (q := q) R := by
  classical
  let Ri := ambientSupportedRepresentationToInduced G Q A R hbefore houtside
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le A.one_le_p).ne' A.p_ne_top
  by_cases hq : q = ∞
  · simp only [LpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨i, rfl⟩
    change Ri.levelCoeffPower i ^ (1 / p.toReal) ≤
      sSup (Set.range fun k => R.levelCoeffPower k ^ (1 / p.toReal))
    simpa [Ri, ambientSupportedRepresentationToInduced_levelCoeffPower
      (G := G) Q A R hbefore houtside] using
        le_csSup hRfin ⟨k₀ + i, rfl⟩
  · simp only [LpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    let aI : ℕ → ℝ := fun i => (Ri.levelCoeffPower i) ^ (q.toReal / p.toReal)
    let a : ℕ → ℝ := fun n => (R.levelCoeffPower n) ^ (q.toReal / p.toReal)
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq
    have htail : HasSum aI (∑' i, a (k₀ + i)) := by
      have hrewrite : aI = fun i => a (k₀ + i) := by
        funext i
        dsimp [aI, a]
        rw [ambientSupportedRepresentationToInduced_levelCoeffPower
          (G := G) Q A R hbefore houtside]
      simpa [hrewrite, Nat.add_comm] using ((summable_nat_add_iff k₀).mpr hRfin).hasSum
    have htsumI : (∑' i, aI i) = ∑' i, a (k₀ + i) := htail.tsum_eq
    have hsplit :
        (∑ i ∈ Finset.range k₀, a i) + (∑' i, a (k₀ + i)) = ∑' i, a i := by
      simpa [a, Nat.add_comm] using Summable.sum_add_tsum_nat_add (f := a) k₀ hRfin
    have hprefix_nonneg : 0 ≤ ∑ i ∈ Finset.range k₀, a i :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (R.levelCoeffPower_nonneg i) _
    have htail_le : (∑' i, a (k₀ + i)) ≤ ∑' i, a i := by
      linarith
    have hsumI_nonneg : 0 ≤ ∑' i, aI i := by
      rw [htsumI]
      exact tsum_nonneg fun i => Real.rpow_nonneg (R.levelCoeffPower_nonneg (k₀ + i)) _
    exact Real.rpow_le_rpow hsumI_nonneg (by simpa [htsumI] using htail_le)
      (one_div_pos.mpr hq_pos).le

/-- Transporting a `LevelBlock` along an equality of levels does not change its `L^p` value. -/
@[simp]
theorem cast_levelBlock_toLp
    (G : WeakGridSpace (α := α)) {m n : ℕ}
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    (h : m = n) (B : LevelBlock A m) :
    (cast (congrArg (LevelBlock A) h) B).toLp A = B.toLp A := by
  subst h
  rfl

/-- Transporting a `LevelBlock` along an equality of levels does not change its coefficient power. -/
@[simp]
theorem cast_levelBlock_levelCoeffPower
    (G : WeakGridSpace (α := α)) {m n : ℕ}
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    (h : m = n) (B : LevelBlock A m) :
    ∑ P : LevelCell G n, ‖(cast (congrArg (LevelBlock A) h) B).coeff P‖ ^ p.toReal =
      ∑ P : LevelCell G m, ‖B.coeff P‖ ^ p.toReal := by
  subst h
  rfl

@[simp]
theorem cast_levelBlock_coeff
    (G : WeakGridSpace (α := α)) {m n : ℕ}
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    (h : m = n) (B : LevelBlock A m) (P : LevelCell G n) :
    (cast (congrArg (LevelBlock A) h) B).coeff P =
      B.coeff (cast (congrArg (LevelCell G) h.symm) P) := by
  subst h
  rfl

@[simp]
theorem cast_levelCell_coe
    (G : WeakGridSpace (α := α)) {m n : ℕ}
    (h : m = n) (P : LevelCell G m) :
    (cast (congrArg (LevelCell G) h) P).1 = P.1 := by
  subst h
  rfl

/-- Transporting a `LevelBlock` along an equality of levels does not change the
function realized by its atom at a transported cell. -/
theorem cast_levelBlock_atom_toFunction
    (G : WeakGridSpace (α := α)) {m n : ℕ}
    {s : ℝ} {p u : ℝ≥0∞} (A : AtomFamily G s p u)
    (h : m = n) (B : LevelBlock A m) (P : LevelCell G n) :
    A.toFunction (levelCellToWeakGridCell G n P)
        ((cast (congrArg (LevelBlock A) h) B).atom P) =
      A.toFunction
        (levelCellToWeakGridCell G m (cast (congrArg (LevelCell G) h.symm) P))
        (B.atom (cast (congrArg (LevelCell G) h.symm) P)) := by
  subst h
  rfl

/-- The same `L^p` element, viewed from the induced grid as an ambient element. -/
abbrev inducedLpToAmbient
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {p : ℝ≥0∞} (f : Lp ℂ p (inducedWeakGridSpace G Q).measure) :
    Lp ℂ p G.measure :=
  f

/--
The ambient block sequence obtained from an induced representation.

Before the parent level `k₀` all blocks are zero.  At a level `n ≥ k₀`, the
block is the induced block at level `n - k₀`, transported from ambient level
`k₀ + (n - k₀)` to the definitionally required level `n`.
-/
def inducedRepresentationBlockToAmbient
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f)
    (n : ℕ) : LevelBlock A n := by
  classical
  by_cases hn : k₀ ≤ n
  · exact cast (congrArg (LevelBlock A) (by omega : k₀ + (n - k₀) = n))
      (inducedLevelBlockToAmbient G Q A (R.block (n - k₀)))
  · exact LevelBlock.zero A n

/-- The reindexed ambient representation has zero `L^p` block value before level `k₀`. -/
@[simp]
theorem inducedRepresentationBlockToAmbient_toLp_lt
    (G : WeakGridSpace (α := α)) {k₀ n : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f)
    (hn : n < k₀) :
    (inducedRepresentationBlockToAmbient G Q A R n).toLp A = 0 := by
  have hnot : ¬ k₀ ≤ n := Nat.not_le_of_gt hn
  simp [inducedRepresentationBlockToAmbient, hnot]

/-- At ambient level `k₀+i`, the reindexed representation has the original induced block value. -/
@[simp]
theorem inducedRepresentationBlockToAmbient_toLp_add
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f) :
    (inducedRepresentationBlockToAmbient G Q A R (k₀ + i)).toLp A =
      (R.block i).toLp (inducedAtomFamily G Q A) := by
  have hle : k₀ ≤ k₀ + i := Nat.le_add_right k₀ i
  simp only [inducedRepresentationBlockToAmbient, dif_pos hle]
  rw [cast_levelBlock_toLp (G := G) (A := A)
    (h := (by omega : k₀ + (k₀ + i - k₀) = k₀ + i))]
  rw [show k₀ + i - k₀ = i by omega]
  exact inducedLevelBlockToAmbient_toLp G Q A (R.block i)

/-- The reindexed ambient representation has zero coefficient power before level `k₀`. -/
@[simp]
theorem inducedRepresentationBlockToAmbient_levelCoeffPower_lt
    (G : WeakGridSpace (α := α)) {k₀ n : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f)
    (hn : n < k₀) :
    ∑ P : LevelCell G n,
        ‖(inducedRepresentationBlockToAmbient G Q A R n).coeff P‖ ^ p.toReal = 0 := by
  have hnot : ¬ k₀ ≤ n := Nat.not_le_of_gt hn
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le A.one_le_p).ne' A.p_ne_top
  simp [inducedRepresentationBlockToAmbient, hnot, LevelBlock.zero,
    Real.zero_rpow hp_pos.ne']

/-- At ambient level `k₀+i`, the reindexed representation has the original induced coefficient power. -/
@[simp]
theorem inducedRepresentationBlockToAmbient_levelCoeffPower_add
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f) :
    ∑ P : LevelCell G (k₀ + i),
        ‖(inducedRepresentationBlockToAmbient G Q A R (k₀ + i)).coeff P‖ ^ p.toReal =
      R.levelCoeffPower i := by
  have hle : k₀ ≤ k₀ + i := Nat.le_add_right k₀ i
  simp only [inducedRepresentationBlockToAmbient, dif_pos hle]
  rw [cast_levelBlock_levelCoeffPower (G := G) (A := A)
    (h := (by omega : k₀ + (k₀ + i - k₀) = k₀ + i))]
  rw [show k₀ + i - k₀ = i by omega]
  simpa [LpGridRepresentation.levelCoeffPower] using
    inducedLevelBlockToAmbient_levelCoeffPower G Q A (R.block i)

/--
An induced atomic representation, viewed as an ambient atomic representation.

The represented `L^p` element is unchanged.  The proof of `hasSum` shifts the
series by `k₀` and uses that all earlier ambient blocks are zero.
-/
def inducedRepresentationToAmbient
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f) :
    LpGridRepresentation A (inducedLpToAmbient G Q f) := by
  classical
  let B : (n : ℕ) → LevelBlock A n :=
    inducedRepresentationBlockToAmbient G Q A R
  refine
    { block := B
      hasSum := ?_ }
  let F : ℕ → Lp ℂ p G.measure := fun n => (B n).toLp A
  have htail : HasSum (fun n => F (n + k₀)) (inducedLpToAmbient G Q f) := by
    have hrewrite : (fun n => F (n + k₀)) =
        fun n => (R.block n).toLp (inducedAtomFamily G Q A) := by
      funext n
      simpa [F, B, Nat.add_comm] using
        inducedRepresentationBlockToAmbient_toLp_add (G := G) Q A R (i := n)
    simpa [hrewrite, inducedLpToAmbient] using R.hasSum
  have hprefix : (∑ n ∈ Finset.range k₀, F n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact inducedRepresentationBlockToAmbient_toLp_lt (G := G) Q A R
      (Finset.mem_range.mp hn)
  have hambient : HasSum F
      ((inducedLpToAmbient G Q f) + ∑ n ∈ Finset.range k₀, F n) :=
    (hasSum_nat_add_iff k₀).mp htail
  simpa [F, hprefix, zero_add] using hambient

/-- The ambient representation obtained from an induced one has zero level power before `k₀`. -/
@[simp]
theorem inducedRepresentationToAmbient_levelCoeffPower_lt
    (G : WeakGridSpace (α := α)) {k₀ n : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f)
    (hn : n < k₀) :
    (inducedRepresentationToAmbient G Q A R).levelCoeffPower n = 0 := by
  unfold LpGridRepresentation.levelCoeffPower
  exact inducedRepresentationBlockToAmbient_levelCoeffPower_lt (G := G) Q A R hn

/-- The ambient representation obtained from an induced one has the shifted induced level power. -/
@[simp]
theorem inducedRepresentationToAmbient_levelCoeffPower_add
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f) :
    (inducedRepresentationToAmbient G Q A R).levelCoeffPower (k₀ + i) =
      R.levelCoeffPower i := by
  unfold LpGridRepresentation.levelCoeffPower
  exact inducedRepresentationBlockToAmbient_levelCoeffPower_add (G := G) Q A R

@[simp]
theorem inducedRepresentationToAmbient_coeff_lt
    (G : WeakGridSpace (α := α)) {k₀ n : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f)
    (hn : n < k₀) (S : LevelCell G n) :
    ((inducedRepresentationToAmbient G Q A R).block n).coeff S = 0 := by
  have hnot : ¬ k₀ ≤ n := Nat.not_le_of_gt hn
  simp [inducedRepresentationToAmbient, inducedRepresentationBlockToAmbient, hnot,
    LevelBlock.zero]

@[simp]
theorem inducedRepresentationToAmbient_coeff_eq_zero_of_not_subset
    (G : WeakGridSpace (α := α)) {k₀ n : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f)
    (S : LevelCell G n) (hS : ¬ S.1 ⊆ Q.1) :
    ((inducedRepresentationToAmbient G Q A R).block n).coeff S = 0 := by
  by_cases hn : k₀ ≤ n
  · simp [inducedRepresentationToAmbient, inducedRepresentationBlockToAmbient, hn,
      inducedLevelBlockToAmbient, cast_levelBlock_coeff, cast_levelCell_coe, hS]
  · exact inducedRepresentationToAmbient_coeff_lt G Q A R (Nat.lt_of_not_ge hn) S

/-- The induced-to-ambient block embedding preserves nonnegative-real
coefficients: every embedded coefficient is either an original (induced)
coefficient or `0`. -/
theorem inducedLevelBlockToAmbient_coeff_nnreal
    (G : WeakGridSpace (α := α)) {k₀ i : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} (A : AtomFamily G s p u)
    (B : LevelBlock (inducedAtomFamily G Q A) i)
    (hB : ∀ P : LevelCell (inducedWeakGridSpace G Q) i,
      ∃ r : NNReal, B.coeff P = (r : ℂ))
    (P : LevelCell G (k₀ + i)) :
    ∃ r : NNReal, (inducedLevelBlockToAmbient G Q A B).coeff P = (r : ℂ) := by
  classical
  by_cases hP : P.1 ⊆ Q.1
  · obtain ⟨r, hr⟩ := hB (ambientLevelCellToInduced G Q P hP)
    refine ⟨r, ?_⟩
    simp only [inducedLevelBlockToAmbient, dif_pos hP]
    exact hr
  · refine ⟨0, ?_⟩
    simp [inducedLevelBlockToAmbient, dif_neg hP]

/-- The reindexed ambient representation preserves nonnegative-real
coefficients. -/
theorem inducedRepresentationToAmbient_coeff_nnreal
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f)
    (hpos : ∀ (i : ℕ) (P : LevelCell (inducedWeakGridSpace G Q) i),
      ∃ r : NNReal, (R.block i).coeff P = (r : ℂ))
    (n : ℕ) (S : LevelCell G n) :
    ∃ r : NNReal,
      ((inducedRepresentationToAmbient G Q A R).block n).coeff S = (r : ℂ) := by
  classical
  by_cases hn : k₀ ≤ n
  · have heq :
        ((inducedRepresentationToAmbient G Q A R).block n).coeff S =
          (inducedLevelBlockToAmbient G Q A (R.block (n - k₀))).coeff
            (cast (congrArg (LevelCell G) (by omega : n = k₀ + (n - k₀))) S) := by
      simp only [inducedRepresentationToAmbient, inducedRepresentationBlockToAmbient,
        dif_pos hn]
      rw [cast_levelBlock_coeff (G := G) (A := A)
        (h := show k₀ + (n - k₀) = n by omega)]
    rw [heq]
    exact inducedLevelBlockToAmbient_coeff_nnreal G Q A (R.block (n - k₀))
      (fun P => hpos (n - k₀) P) _
  · refine ⟨0, ?_⟩
    simp only [inducedRepresentationToAmbient, inducedRepresentationBlockToAmbient,
      dif_neg hn, LevelBlock.zero, NNReal.coe_zero, Complex.ofReal_zero]

/-- Pointwise positivity of atoms passes from an induced representation to its
ambient reindexing, on cells inside the parent at levels `≥ k₀`.  (At cells
outside the parent or at levels `< k₀` the reindexed coefficients vanish, so no
positivity information is needed there.) -/
theorem inducedRepresentationToAmbient_atom_toFunction_pos
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u : ℝ≥0∞} [Fact (1 ≤ p)] (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f)
    (hatom : ∀ (i : ℕ) (P : LevelCell (inducedWeakGridSpace G Q) i) (x : α),
      x ∈ P.1 →
      ∃ a : NNReal, 0 < a ∧
        (inducedAtomFamily G Q A).toFunction
          (levelCellToWeakGridCell (inducedWeakGridSpace G Q) i P)
          ((R.block i).atom P) x = (a : ℂ))
    {n : ℕ} (hn : k₀ ≤ n) (S : LevelCell G n) (hS : S.1 ⊆ Q.1)
    (x : α) (hx : x ∈ S.1) :
    ∃ a : NNReal, 0 < a ∧
      A.toFunction (levelCellToWeakGridCell G n S)
        (((inducedRepresentationToAmbient G Q A R).block n).atom S) x = (a : ℂ) := by
  classical
  have h : k₀ + (n - k₀) = n := by omega
  have hblock :
      (inducedRepresentationToAmbient G Q A R).block n =
        cast (congrArg (LevelBlock A) h)
          (inducedLevelBlockToAmbient G Q A (R.block (n - k₀))) := by
    simp only [inducedRepresentationToAmbient, inducedRepresentationBlockToAmbient,
      dif_pos hn]
  rw [hblock, cast_levelBlock_atom_toFunction (G := G) A h]
  have hS' : (cast (congrArg (LevelCell G) h.symm) S).1 ⊆ Q.1 := by
    rw [cast_levelCell_coe G h.symm S]
    exact hS
  have hatom_eq :
      (inducedLevelBlockToAmbient G Q A (R.block (n - k₀))).atom
          (cast (congrArg (LevelCell G) h.symm) S) =
        (R.block (n - k₀)).atom
          (ambientLevelCellToInduced G Q
            (cast (congrArg (LevelCell G) h.symm) S) hS') := by
    simp only [inducedLevelBlockToAmbient, dif_pos hS']
  rw [hatom_eq]
  have hx' : x ∈ (ambientLevelCellToInduced G Q
      (cast (congrArg (LevelCell G) h.symm) S) hS').1 := by
    show x ∈ (cast (congrArg (LevelCell G) h.symm) S).1
    rw [cast_levelCell_coe G h.symm S]
    exact hx
  obtain ⟨a, ha, hval⟩ := hatom (n - k₀)
    (ambientLevelCellToInduced G Q (cast (congrArg (LevelCell G) h.symm) S) hS') x hx'
  exact ⟨a, ha, hval⟩

/--
Reindexing an induced representation into the ambient grid preserves finite
`(p,q)` cost.  For `q = ∞` this is boundedness of the shifted supremum; for
`q < ∞` it is summability of the shifted series with finitely many initial zeros.
-/
theorem inducedRepresentationToAmbient_finitePQCost
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R) :
    LpGridRepresentation.FinitePQCost (q := q)
      (inducedRepresentationToAmbient G Q A R) := by
  classical
  let RA := inducedRepresentationToAmbient G Q A R
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le A.one_le_p).ne' A.p_ne_top
  by_cases hq : q = ∞
  · simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin ⊢
    rcases hRfin with ⟨C, hC⟩
    refine ⟨max C 0, ?_⟩
    rintro x ⟨n, rfl⟩
    by_cases hn : n < k₀
    · have hinv_pos : 0 < 1 / p.toReal := div_pos one_pos hp_pos
      have hzero : (0 : ℝ) ^ p.toReal⁻¹ = 0 := by
        simpa [one_div] using Real.zero_rpow hinv_pos.ne'
      calc
        (RA.levelCoeffPower n) ^ (1 / p.toReal) = 0 := by
          simp [RA, inducedRepresentationToAmbient_levelCoeffPower_lt (G := G) Q A R hn,
            hzero, one_div]
        _ ≤ max C 0 := le_max_right C 0
    · have hle : k₀ ≤ n := Nat.le_of_not_gt hn
      let i := n - k₀
      have hn_eq : n = k₀ + i := by omega
      calc
        (RA.levelCoeffPower n) ^ (1 / p.toReal)
            = (R.levelCoeffPower i) ^ (1 / p.toReal) := by
              rw [hn_eq]
              simp [RA, i, one_div]
        _ ≤ C := hC ⟨i, by simp [one_div]⟩
        _ ≤ max C 0 := le_max_left C 0
  · simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin ⊢
    have htail :
        Summable (fun n => (RA.levelCoeffPower (n + k₀)) ^ (q.toReal / p.toReal)) := by
      refine hRfin.congr ?_
      intro n
      simpa [RA, Nat.add_comm] using
        congrArg (fun z : ℝ => z ^ (q.toReal / p.toReal))
          (inducedRepresentationToAmbient_levelCoeffPower_add (G := G) Q A R (i := n))
    exact (summable_nat_add_iff k₀).mp htail

/--
Reindexing an induced representation into the ambient grid has `(p,q)` cost at
most the original induced representation.  This is the representation-level
constant `1` estimate used in the final weak contraction theorem.
-/
theorem inducedRepresentationToAmbient_pqCost_le
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A : AtomFamily G s p u)
    {f : Lp ℂ p (inducedWeakGridSpace G Q).measure}
    (R : LpGridRepresentation (inducedAtomFamily G Q A) f)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R) :
    LpGridRepresentation.pqCost (q := q) (inducedRepresentationToAmbient G Q A R) ≤
      LpGridRepresentation.pqCost (q := q) R := by
  classical
  let RA := inducedRepresentationToAmbient G Q A R
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le A.one_le_p).ne' A.p_ne_top
  by_cases hq : q = ∞
  · simp only [LpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨n, rfl⟩
    by_cases hn : n < k₀
    · have hinv_pos : 0 < 1 / p.toReal := div_pos one_pos hp_pos
      have hzero : (0 : ℝ) ^ p.toReal⁻¹ = 0 := by
        simpa [one_div] using Real.zero_rpow hinv_pos.ne'
      have horig_nonneg : 0 ≤ (R.levelCoeffPower 0) ^ (1 / p.toReal) :=
        Real.rpow_nonneg (R.levelCoeffPower_nonneg 0) _
      have hsup_nonneg :
          0 ≤ sSup (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)) :=
        horig_nonneg.trans (le_csSup hRfin ⟨0, by simp [one_div]⟩)
      simpa [RA, inducedRepresentationToAmbient_levelCoeffPower_lt (G := G) Q A R hn,
        hzero, one_div] using hsup_nonneg
    · have hle : k₀ ≤ n := Nat.le_of_not_gt hn
      let i := n - k₀
      have hn_eq : n = k₀ + i := by omega
      have hterm :
          (RA.levelCoeffPower n) ^ (1 / p.toReal) =
            (R.levelCoeffPower (n - k₀)) ^ (1 / p.toReal) := by
        rw [hn_eq]
        simp [RA, i, one_div]
      change (RA.levelCoeffPower n) ^ (1 / p.toReal) ≤
        sSup (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal))
      rw [hterm]
      exact le_csSup hRfin ⟨n - k₀, by simp [one_div]⟩
  · simp only [LpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    let aA : ℕ → ℝ := fun n => (RA.levelCoeffPower n) ^ (q.toReal / p.toReal)
    let a : ℕ → ℝ := fun n => (R.levelCoeffPower n) ^ (q.toReal / p.toReal)
    have htail : HasSum (fun n => aA (n + k₀)) (∑' n, a n) := by
      have hrewrite : (fun n => aA (n + k₀)) = a := by
        funext n
        dsimp [aA, a]
        simpa [RA, Nat.add_comm] using
          congrArg (fun z : ℝ => z ^ (q.toReal / p.toReal))
            (inducedRepresentationToAmbient_levelCoeffPower_add (G := G) Q A R (i := n))
      simpa [hrewrite] using hRfin.hasSum
    have hprefix : (∑ n ∈ Finset.range k₀, aA n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < k₀ := Finset.mem_range.mp hn
      have hq_pos : 0 < q.toReal :=
        ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq
      have hpow_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
      simp [aA, RA, inducedRepresentationToAmbient_levelCoeffPower_lt (G := G) Q A R hnlt,
        Real.zero_rpow hpow_pos.ne']
    have hAHas : HasSum aA ((∑' n, a n) + ∑ n ∈ Finset.range k₀, aA n) :=
      (hasSum_nat_add_iff k₀).mp htail
    have htsum : (∑' n, aA n) = ∑' n, a n := by
      simpa [hprefix] using hAHas.tsum_eq
    have hsum_nonneg : 0 ≤ ∑' n, aA n := by
      exact tsum_nonneg fun n => Real.rpow_nonneg (RA.levelCoeffPower_nonneg n) _
    have hsum_eq : (∑' n, aA n) ^ (1 / q.toReal) =
        (∑' n, a n) ^ (1 / q.toReal) := by
      rw [htsum]
    exact le_of_eq hsum_eq

/--
The canonical inclusion from the Besov-ish space induced on `Q` into the
ambient Besov-ish space is a weak contraction.

The proof is direct: every induced representation is reindexed into the ambient
grid by adding `k₀` to levels and putting zero blocks before `k₀`.  The
one-level reindexing lemmas above show that the coefficient cost does not
increase, and taking the infimum over representations gives constant `1`.
-/
theorem InducedBesovishWeakContraction
    (G : WeakGridSpace (α := α)) {k₀ : ℕ} (Q : LevelCell G k₀)
    {s : ℝ} {p u q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A : AtomFamily G s p u) :
    ∀ f : BesovishSpace (inducedAtomFamily G Q A) q,
      ∃ hf : MemBesovishCoeffCost A q (inducedLpToAmbient G Q (f : Lp ℂ p _)),
        BesovishSpace.Norm_Costpq A q
            (⟨inducedLpToAmbient G Q (f : Lp ℂ p _),
              by simpa [BesovishSpace] using hf⟩ : BesovishSpace A q) ≤
          BesovishSpace.Norm_Costpq (inducedAtomFamily G Q A) q f := by
  intro f
  rcases f.property with ⟨R₀, hR₀fin⟩
  let RA₀ := inducedRepresentationToAmbient G Q A R₀
  have hRA₀fin : LpGridRepresentation.FinitePQCost (q := q) RA₀ :=
    inducedRepresentationToAmbient_finitePQCost G Q A R₀ hR₀fin
  let hf : MemBesovishCoeffCost A q (inducedLpToAmbient G Q (f : Lp ℂ p _)) :=
    ⟨RA₀, hRA₀fin⟩
  refine ⟨hf, ?_⟩
  let gAmbient : BesovishSpace A q :=
    ⟨inducedLpToAmbient G Q (f : Lp ℂ p _), by
      simpa [BesovishSpace] using hf⟩
  change BesovishSpace.Norm_Costpq A q gAmbient ≤
    BesovishSpace.Norm_Costpq (inducedAtomFamily G Q A) q f
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hInducedFinite :
      BesovishSpace.HasFiniteCostRepresentations
        (A := inducedAtomFamily G Q A) q :=
    BesovishSpace.hasFiniteCostRepresentations
      (A := inducedAtomFamily G Q A) (q := q)
  rcases BesovishSpace.exists_cost_lt_Norm_Costpq_add
      (A := inducedAtomFamily G Q A) (q := q) hInducedFinite f hε with
    ⟨R, hRfin, hRlt⟩
  let RA := inducedRepresentationToAmbient G Q A R
  have hRAfin : LpGridRepresentation.FinitePQCost (q := q) RA :=
    inducedRepresentationToAmbient_finitePQCost G Q A R hRfin
  have hmem :
      MemBesovishCoeffCost A q (inducedLpToAmbient G Q (f : Lp ℂ p _)) :=
    ⟨RA, hRAfin⟩
  let gAmbient' : BesovishSpace A q :=
    ⟨inducedLpToAmbient G Q (f : Lp ℂ p _), by
      simpa [BesovishSpace] using hmem⟩
  have hg_eq : gAmbient = gAmbient' := by
    ext
    rfl
  have hnorm_le :
      BesovishSpace.Norm_Costpq A q gAmbient ≤
        LpGridRepresentation.pqCost (q := q) RA := by
    simpa [hg_eq, gAmbient'] using
      BesovishSpace.Norm_Costpq_le_cost
        (A := A) (q := q) (g := gAmbient') RA hRAfin
  have hcost_le :
      LpGridRepresentation.pqCost (q := q) RA ≤
        LpGridRepresentation.pqCost (q := q) R :=
    inducedRepresentationToAmbient_pqCost_le G Q A R hRfin
  exact le_of_lt <| lt_of_le_of_lt (le_trans hnorm_le hcost_le) hRlt

/--
The pointwise representative of the restriction `f · 1_Q`.

This is only the raw function-level operation.  No boundedness or membership in
the induced Besov-ish space is asserted here.
-/
def restrictFunctionToCell (Q : Set α) (f : α → ℂ) : α → ℂ :=
  by
    classical
    exact fun x => if x ∈ Q then f x else 0





end

end WeakGridSpace
