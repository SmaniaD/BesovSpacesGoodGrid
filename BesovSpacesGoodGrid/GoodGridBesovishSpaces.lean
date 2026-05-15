import BesovSpacesGoodGrid.GoodGridAtomsDefinition
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
Besov-ish spaces associated to a good grid and a family of atoms.

The paper defines a Besov-ish element by an atomic expansion whose level
blocks converge absolutely in `L^p`.  A level block is explicitly indexed by
the cells of the level-`k` partition: for each cell there is one coefficient
and one atom.  This matches the paper's finite inner sum
`∑_{Q ∈ P^k} s_Q a_Q`.
-/

namespace UnbalancedHaarWavelet

open scoped ENNReal Topology
open MeasureTheory

universe u v

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace GoodGridAtomFamily

variable {S : GoodGrid (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
variable [Fact (1 ≤ p)]

/--
The grid cells at level `k`, as a finite type.
-/
abbrev LevelCell (S : GoodGrid (α := α)) (k : ℕ) :=
  { Q : Set α // Q ∈ S.grid.partitions k }

/--
The `GoodGridCell` associated to a level cell.
-/
def levelCellToGoodGridCell (S : GoodGrid (α := α)) (k : ℕ)
    (Q : LevelCell S k) : GoodGridCell S :=
  ⟨k, Q.1, Q.2⟩

/--
A level-`k` atomic block.

For each cell `Q ∈ S.grid.partitions k`, it chooses exactly one coefficient
and exactly one atom supported on `Q`.  Its value in `L^p` is the finite sum
over the partition cells.
-/
structure LevelAtomicBlock (A : GoodGridAtomFamily S s p u) (k : ℕ) where
  coeff : LevelCell S k → ℂ
  atom : ∀ Q : LevelCell S k, (A.localSpace (levelCellToGoodGridCell S k Q)).carrier
  atom_mem : ∀ Q : LevelCell S k,
    A.IsAtom (levelCellToGoodGridCell S k Q) (atom Q)
  atom_memLp : ∀ Q : LevelCell S k,
    MemLp (A.toFunction (levelCellToGoodGridCell S k Q) (atom Q)) p S.μ

namespace LevelAtomicBlock

/-- A zero-valued level block, obtained by choosing one atom on each cell. -/
def zero (A : GoodGridAtomFamily S s p u) (k : ℕ) : LevelAtomicBlock A k where
  coeff := fun _ => 0
  atom := fun Q =>
    Classical.choose (A.atoms_nonempty_on (levelCellToGoodGridCell S k Q))
  atom_mem := fun Q =>
    Classical.choose_spec (A.atoms_nonempty_on (levelCellToGoodGridCell S k Q))
  atom_memLp := fun Q =>
    A.local_memLp_p (levelCellToGoodGridCell S k Q)
      (Classical.choose (A.atoms_nonempty_on (levelCellToGoodGridCell S k Q)))

/-- The `L^p` term attached to one cell in a level block. -/
def term (A : GoodGridAtomFamily S s p u) {k : ℕ}
    (B : LevelAtomicBlock A k) (Q : LevelCell S k) : Lp ℂ p S.μ :=
  B.coeff Q • MemLp.toLp
    (A.toFunction (levelCellToGoodGridCell S k Q) (B.atom Q))
    (B.atom_memLp Q)

/--
The value of a level block in `L^p`, namely the finite sum over the level-`k`
partition.
-/
def toLp (A : GoodGridAtomFamily S s p u) {k : ℕ}
    (B : LevelAtomicBlock A k) : Lp ℂ p S.μ :=
  (S.grid.partitions k).attach.sum fun Q => B.term A Q

@[simp]
theorem zero_toLp (A : GoodGridAtomFamily S s p u) (k : ℕ) :
    (zero A k).toLp A = 0 := by
  simp [toLp, term, zero]

/-- Scalar multiplication of a level block, keeping the same atom on each cell. -/
def smul (A : GoodGridAtomFamily S s p u) {k : ℕ} (c : ℂ)
    (B : LevelAtomicBlock A k) : LevelAtomicBlock A k where
  coeff := fun Q => c * B.coeff Q
  atom := B.atom
  atom_mem := B.atom_mem
  atom_memLp := B.atom_memLp

@[simp]
theorem smul_toLp (A : GoodGridAtomFamily S s p u) {k : ℕ} (c : ℂ)
    (B : LevelAtomicBlock A k) :
    (smul A c B).toLp A = c • B.toLp A := by
  simp [toLp, term, smul, Finset.smul_sum, mul_smul]

end LevelAtomicBlock

/--
The set of all genuine level-`k` atomic blocks, viewed as elements of `L^p`.
-/
def levelAtomicBlockSet (A : GoodGridAtomFamily S s p u) (k : ℕ) :
    Set (Lp ℂ p S.μ) :=
  { f | ∃ B : LevelAtomicBlock A k, B.toLp A = f }

theorem zero_mem_levelAtomicBlockSet (A : GoodGridAtomFamily S s p u) (k : ℕ) :
    (0 : Lp ℂ p S.μ) ∈ A.levelAtomicBlockSet k :=
  ⟨LevelAtomicBlock.zero A k, by simp⟩

theorem smul_mem_levelAtomicBlockSet (A : GoodGridAtomFamily S s p u) (k : ℕ)
    (c : ℂ) {x : Lp ℂ p S.μ} (hx : x ∈ A.levelAtomicBlockSet k) :
    c • x ∈ A.levelAtomicBlockSet k := by
  rcases hx with ⟨B, rfl⟩
  exact ⟨LevelAtomicBlock.smul A c B, by simp⟩

/--
Closure of genuine level blocks under addition and scalar multiplication.

Mathematically, addition is the cellwise operation
`s_Q a_Q + t_Q b_Q`, repackaged as one coefficient times one atom using the
convexity and phase-invariance of `A(Q)`.  This predicate isolates that local
repackaging step.
-/
def LevelBlocksLinear (A : GoodGridAtomFamily S s p u) : Prop :=
  (∀ k, (0 : Lp ℂ p S.μ) ∈ A.levelAtomicBlockSet k) ∧
  (∀ k x y, x ∈ A.levelAtomicBlockSet k → y ∈ A.levelAtomicBlockSet k →
    x + y ∈ A.levelAtomicBlockSet k) ∧
  (∀ k (c : ℂ) x, x ∈ A.levelAtomicBlockSet k →
    c • x ∈ A.levelAtomicBlockSet k)

/-- Choose a concrete atomic block representing a member of `levelAtomicBlockSet`. -/
def chooseLevelAtomicBlock {A : GoodGridAtomFamily S s p u} {k : ℕ}
    {f : Lp ℂ p S.μ} (hf : f ∈ A.levelAtomicBlockSet k) :
    LevelAtomicBlock A k :=
  Classical.choose hf

omit [Fact (1 ≤ p)] in
theorem chooseLevelAtomicBlock_toLp {A : GoodGridAtomFamily S s p u} {k : ℕ}
    {f : Lp ℂ p S.μ} (hf : f ∈ A.levelAtomicBlockSet k) :
    (chooseLevelAtomicBlock hf).toLp A = f :=
  Classical.choose_spec hf

/--
A Besov-ish representation of `g`: an absolutely summable series of atomic
level blocks whose sum is `g` in `L^p`.

The parameter `q` is present because the space is indexed by `(s,p,q)`.  The
field `abs_summable` formalizes the paper's "absolutely convergent series in
`L^p`" condition for the level blocks.
-/
structure BesovishRepresentation
    (A : GoodGridAtomFamily S s p u) (q : ℝ≥0∞) (g : Lp ℂ p S.μ) where
  block : (k : ℕ) → LevelAtomicBlock A k
  abs_summable : Summable fun k => ‖(block k).toLp A‖
  hasSum : HasSum (fun k => (block k).toLp A) g

/-- The `L^p` absolute-convergence cost of a representation. -/
def BesovishRepresentation.lpCost
    {A : GoodGridAtomFamily S s p u} {g : Lp ℂ p S.μ}
    (R : BesovishRepresentation A q g) : ℝ :=
  ∑' k, ‖(R.block k).toLp A‖

/--
The Besov-ish predicate on `L^p`: `g` has an atomic Besov-ish representation.
-/
def MemBesovish (A : GoodGridAtomFamily S s p u) (q : ℝ≥0∞)
    (g : Lp ℂ p S.μ) : Prop :=
  Nonempty (BesovishRepresentation A q g)

theorem memBesovish_zero (A : GoodGridAtomFamily S s p u)
    (hlin : LevelBlocksLinear A) :
    MemBesovish A q (0 : Lp ℂ p S.μ) := by
  let B : (k : ℕ) → LevelAtomicBlock A k :=
    fun k => chooseLevelAtomicBlock (hlin.1 k)
  have hB : ∀ k, (B k).toLp A = 0 := by
    intro k
    exact chooseLevelAtomicBlock_toLp (hlin.1 k)
  refine ⟨?_⟩
  refine
    { block := B
      abs_summable := ?_
      hasSum := ?_ }
  · simp [B, hB]
  · simp [B, hB]

theorem memBesovish_add {A : GoodGridAtomFamily S s p u}
    (hlin : LevelBlocksLinear A) {g h : Lp ℂ p S.μ}
    (hg : MemBesovish A q g) (hh : MemBesovish A q h) :
    MemBesovish A q (g + h) := by
  rcases hg with ⟨Rg⟩
  rcases hh with ⟨Rh⟩
  let B : (k : ℕ) → LevelAtomicBlock A k := fun k =>
    chooseLevelAtomicBlock
      (hlin.2.1 k ((Rg.block k).toLp A) ((Rh.block k).toLp A)
        ⟨Rg.block k, rfl⟩ ⟨Rh.block k, rfl⟩)
  have hB : ∀ k, (B k).toLp A = (Rg.block k).toLp A + (Rh.block k).toLp A := by
    intro k
    exact chooseLevelAtomicBlock_toLp
      (hlin.2.1 k ((Rg.block k).toLp A) ((Rh.block k).toLp A)
        ⟨Rg.block k, rfl⟩ ⟨Rh.block k, rfl⟩)
  refine ⟨?_⟩
  refine
    { block := B
      abs_summable := ?_
      hasSum := ?_ }
  · refine Summable.of_nonneg_of_le
      (fun k => norm_nonneg ((B k).toLp A)) ?_ (Rg.abs_summable.add Rh.abs_summable)
    intro k
    rw [hB k]
    exact norm_add_le ((Rg.block k).toLp A) ((Rh.block k).toLp A)
  · simpa [B, hB] using Rg.hasSum.add Rh.hasSum

theorem memBesovish_smul {A : GoodGridAtomFamily S s p u}
    (hlin : LevelBlocksLinear A) (c : ℂ) {g : Lp ℂ p S.μ}
    (hg : MemBesovish A q g) :
    MemBesovish A q (c • g) := by
  rcases hg with ⟨Rg⟩
  let B : (k : ℕ) → LevelAtomicBlock A k := fun k =>
    chooseLevelAtomicBlock
      (hlin.2.2 k c ((Rg.block k).toLp A) ⟨Rg.block k, rfl⟩)
  have hB : ∀ k, (B k).toLp A = c • (Rg.block k).toLp A := by
    intro k
    exact chooseLevelAtomicBlock_toLp
      (hlin.2.2 k c ((Rg.block k).toLp A) ⟨Rg.block k, rfl⟩)
  refine ⟨?_⟩
  refine
    { block := B
      abs_summable := ?_
      hasSum := ?_ }
  · refine (Summable.mul_left ‖c‖ Rg.abs_summable).congr ?_
    intro k
    rw [hB k, norm_smul]
  · simpa [B, hB] using Rg.hasSum.const_smul c

/--
The Besov-ish space as a complex linear subspace of `L^p`.
-/
def BesovishSpace (A : GoodGridAtomFamily S s p u) (q : ℝ≥0∞)
    (hlin : LevelBlocksLinear A) :
    Submodule ℂ (Lp ℂ p S.μ) where
  carrier := { g | MemBesovish A q g }
  zero_mem' := memBesovish_zero (A := A) (q := q) hlin
  add_mem' := by
    intro g h hg hh
    exact memBesovish_add (A := A) (q := q) hlin hg hh
  smul_mem' := by
    intro c g hg
    exact memBesovish_smul (A := A) (q := q) hlin c hg

/--
The Besov-ish space is a linear subspace of `L^p`.
-/
theorem besovishSpace_is_linear_subspace
    (A : GoodGridAtomFamily S s p u) (q : ℝ≥0∞)
    (hlin : LevelBlocksLinear A) :
    ∃ E : Submodule ℂ (Lp ℂ p S.μ), E = BesovishSpace A q hlin :=
  ⟨BesovishSpace A q hlin, rfl⟩

end GoodGridAtomFamily

end

end UnbalancedHaarWavelet
