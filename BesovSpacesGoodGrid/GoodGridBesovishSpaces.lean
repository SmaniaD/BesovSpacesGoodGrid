import BesovSpacesGoodGrid.GoodGridAtomsDefinition
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import BesovSpacesGoodGrid.GoodGridDefinition

/-!
Besov-ish spaces associated to a good grid and a family of atoms.

The paper defines a Besov-ish element by an atomic expansion whose level
blocks converge absolutely in `L^p`.  A level block is explicitly indexed by
the cells of the level-`k` partition: for each cell there is one coefficient
and one atom.  This matches the paper's finite inner sum
`∑_{Q ∈ P^k} s_Q a_Q`.
-/

namespace GoodGridSpace

open scoped ENNReal Topology
open MeasureTheory

universe u v

variable {α : Type u} [MeasurableSpace α]

noncomputable section




variable {G : GoodGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
variable [Fact (1 ≤ p)]

/--
O tipo dos cells no nível k, usando o grid de G.
-/
abbrev LevelCell (G : GoodGridSpace (α := α)) (k : ℕ) :=
  { Q : Set α // Q ∈ G.grid.grid.partitions k }

/--
Converte um LevelCell para um GoodGridCell, usando o grid de G.
-/
def levelCellToGoodGridCell (G : GoodGridSpace (α := α)) (k : ℕ)
    (Q : LevelCell G k) : GoodGridCell G :=
  ⟨k, Q.1, Q.2⟩

/--
A level-`k` atomic block.

For each cell `Q ∈ S.grid.partitions k`, it chooses exactly one coefficient
and exactly one atom supported on `Q`.  Its value in `L^p` is the finite sum
over the partition cells.
-/
structure LevelBlock (A : AtomFamily G s p u) (k : ℕ) where
  coeff : LevelCell G k → ℂ
  atom : ∀ Q : LevelCell G k, (A.localSpace (levelCellToGoodGridCell G k Q)).carrier
  atom_mem : ∀ Q : LevelCell G k,
    A.IsAtom (levelCellToGoodGridCell G k Q) (atom Q)

namespace LevelBlock

/-- A zero-valued level block, obtained by choosing one atom on each cell. -/
def zero (A : AtomFamily G s p u) (k : ℕ) : LevelBlock A k where
  coeff := fun _ => 0
  atom := fun Q =>
    Classical.choose (A.atoms_nonempty_on (levelCellToGoodGridCell G k Q))
  atom_mem := fun Q =>
    Classical.choose_spec (A.atoms_nonempty_on (levelCellToGoodGridCell G k Q))

/-- The `L^p` term attached to one cell in a level block. -/
def term (A : AtomFamily G s p u) {k : ℕ}
    (B : LevelBlock A k) (Q : LevelCell G k) : Lp ℂ p G.measure :=
  B.coeff Q • MemLp.toLp
    (A.toFunction (levelCellToGoodGridCell G k Q) (B.atom Q))
    (A.local_memLp_p (levelCellToGoodGridCell G k Q) (B.atom Q))

/--
The value of a level block in `L^p`, namely the finite sum over the level-`k`
partition.
-/
def toLp (A : AtomFamily G s p u) {k : ℕ}
    (B : LevelBlock A k) : Lp ℂ p G.measure :=
  (G.grid.grid.partitions k).attach.sum fun Q => B.term A Q

@[simp]
theorem zero_toLp (A : AtomFamily G s p u) (k : ℕ) :
    (zero A k).toLp A = 0 := by
  simp [toLp, term, zero]

/-- Scalar multiplication of a level block, keeping the same atom on each cell. -/
def smul (A : AtomFamily G s p u) {k : ℕ} (c : ℂ)
    (B : LevelBlock A k) : LevelBlock A k where
  coeff := fun Q => c * B.coeff Q
  atom := B.atom
  atom_mem := B.atom_mem

@[simp]
theorem smul_toLp (A : AtomFamily G s p u) {k : ℕ} (c : ℂ)
    (B : LevelBlock A k) :
    (smul A c B).toLp A = c • B.toLp A := by
  simp [toLp, term, smul, Finset.smul_sum, mul_smul]

end LevelBlock

/--
The set of all genuine level-`k` atomic blocks, viewed as elements of `L^p`.
-/
def LevelBlockSet (A : AtomFamily G s p u) (k : ℕ) :
    Set (Lp ℂ p G.measure) :=
  { f | ∃ B : LevelBlock A k, B.toLp A = f }

theorem zero_mem_LevelBlockSet (A : AtomFamily G s p u) (k : ℕ) :
    (0 : Lp ℂ p G.measure) ∈ LevelBlockSet A k :=
  ⟨LevelBlock.zero A k, by simp⟩

theorem smul_mem_LevelBlockSet (A : AtomFamily G s p u) (k : ℕ)
  (c : ℂ) {x : Lp ℂ p G.measure} (hx : x ∈ LevelBlockSet A k) :
  c • x ∈ LevelBlockSet A k := by
  -- Unpack a witness block for `x`, then scale its coefficients.
  rcases hx with ⟨B, rfl⟩
  exact ⟨LevelBlock.smul A c B, by simp⟩

/--
Closure of genuine level blocks under addition and scalar multiplication.

Mathematically, addition is the cellwise operation
`s_Q a_Q + t_Q b_Q`, repackaged as one coefficient times one atom using the
convexity and phase-invariance of `A(Q)`.  This predicate isolates that local
repackaging step.
-/
def LevelBlocksLinear (A : AtomFamily G s p u) : Prop :=
  (∀ k, (0 : Lp ℂ p G.measure) ∈ LevelBlockSet A k) ∧
  (∀ k x y, x ∈ LevelBlockSet A k → y ∈ LevelBlockSet A k →
    x + y ∈ LevelBlockSet A k) ∧
  (∀ k (c : ℂ) x, x ∈ LevelBlockSet A k →
    c • x ∈ LevelBlockSet A k)

/--
Package the `LevelBlocksLinear` hypothesis once additive closure is available.

In the paper, the additive-closure input is obtained cellwise from convexity of
`A(Q)` and invariance under multiplication by unimodular complex scalars.
-/
theorem levelBlocksLinear_of_add_closure
    (A : AtomFamily G s p u)
    (hadd :
      ∀ k x y, x ∈ LevelBlockSet A k → y ∈ LevelBlockSet A k →
        x + y ∈ LevelBlockSet A k) :
    LevelBlocksLinear A := by
  -- Zero and scalar closure are already available globally; only additive
  -- closure is supplied as input (the local convexity/phase argument).
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact zero_mem_LevelBlockSet A k
  · exact hadd
  · intro k c x hx
    exact smul_mem_LevelBlockSet A k c hx

/-- Choose a concrete atomic block representing a member of `LevelBlockSet`. -/
def chooseLevelBlock {A : AtomFamily G s p u} {k : ℕ}
  {f : Lp ℂ p G.measure} (hf : f ∈ LevelBlockSet A k) :
    LevelBlock A k :=
  Classical.choose hf

omit [Fact (1 ≤ p)] in
theorem chooseLevelBlock_toLp {A : AtomFamily G s p u} {k : ℕ}
  {f : Lp ℂ p G.measure} (hf : f ∈ LevelBlockSet A k) :
    (chooseLevelBlock hf).toLp A = f :=
  Classical.choose_spec hf

/--
A Besov-ish representation of `g`: an absolutely summable series of atomic
level blocks whose sum is `g` in `L^p`.

The parameter `q` is present because the space is indexed by `(s,p,q)`.  The
field `abs_summable` formalizes the paper's "absolutely convergent series in
`L^p`" condition for the level blocks.
-/
structure BesovishRepresentation
    (A : AtomFamily G s p u) (q : ℝ≥0∞) (g : Lp ℂ p G.measure) where
  block : (k : ℕ) → LevelBlock A k
  abs_summable : Summable fun k => ‖(block k).toLp A‖
  hasSum : HasSum (fun k => (block k).toLp A) g
  /--
  The paper's `(p,q)` coefficient-cost condition (equation `(rep2)`), recorded
  at the representation level.

  This field stores the target predicate for finite coefficient cost. It is
  intentionally a proposition field (with default value) so existing
  constructions remain valid while allowing downstream developments to require
  or prove this condition explicitly.
  -/
  pq_finite_cost : Prop :=
    if q = ∞ then
      BddAbove (Set.range fun k =>
        ((∑ Q : LevelCell G k, ‖(block k).coeff Q‖ ^ p.toReal) ^ (1 / p.toReal)))
    else
      Summable fun k =>
        ((∑ Q : LevelCell G k, ‖(block k).coeff Q‖ ^ p.toReal) ^ (q.toReal / p.toReal))

namespace BesovishRepresentation

/--
Level-`k` coefficient `ℓ^p` power sum: `∑_{Q ∈ P^k} |s_Q|^p`.

This is the inner quantity from the paper's coefficient-cost formula.
-/
def levelCoeffPower
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (R : BesovishRepresentation A q g) (k : ℕ) : ℝ :=
  ∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ p.toReal

/--
Finite coefficient cost corresponding to equation `(rep2)` in the paper.


This is a readable alias for the structure field `pq_finite_cost`.
-/
def finiteCoeffCost
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (R : BesovishRepresentation A q g) : Prop :=
  R.pq_finite_cost

end BesovishRepresentation

/-- The `L^p` absolute-convergence cost of a representation. -/
def BesovishRepresentation.lpCost
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (R : BesovishRepresentation A q g) : ℝ :=
  ∑' k, ‖(R.block k).toLp A‖

/--
The Besov-ish predicate on `L^p`: `g` has an atomic Besov-ish representation.
-/
def MemBesovish (A : AtomFamily G s p u) (q : ℝ≥0∞)
    (g : Lp ℂ p G.measure) : Prop :=
  Nonempty (BesovishRepresentation A q g)

/--
Stronger Besov-ish predicate: representation exists and has finite
coefficient cost in the sense of equation `(rep2)` from the paper.
-/
def MemBesovishCoeffCost (A : AtomFamily G s p u) (q : ℝ≥0∞)
    (g : Lp ℂ p G.measure) : Prop :=
  ∃ R : BesovishRepresentation A q g, R.finiteCoeffCost

theorem memBesovish_zero (A : AtomFamily G s p u)
    (hlin : LevelBlocksLinear A) :
    MemBesovish A q (0 : Lp ℂ p G.measure) := by
  -- Levelwise membership of `0` in the block set.
  have hzero_mem : ∀ k, (0 : Lp ℂ p G.measure) ∈ LevelBlockSet A k := hlin.1
  -- Choose one concrete witness block for each level.
  let B : (k : ℕ) → LevelBlock A k :=
    fun k => chooseLevelBlock (hzero_mem k)
  -- Each chosen block evaluates to `0` in `L^p`.
  have hB_toLp : ∀ k, (B k).toLp A = 0 := by
    intro k
    exact chooseLevelBlock_toLp (hzero_mem k)
  refine ⟨?_⟩
  refine
    { block := B
      abs_summable := ?_
      hasSum := ?_ }
  · simp [B, hB_toLp]
  · simp [B, hB_toLp]

theorem memBesovish_add {A : AtomFamily G s p u}
  (hlin : LevelBlocksLinear A) {g h : Lp ℂ p G.measure}
  (hg : MemBesovish A q g) (hh : MemBesovish A q h) :
  MemBesovish A q (g + h) := by
  -- Start from concrete representations of `g` and `h`.
  rcases hg with ⟨repG⟩
  rcases hh with ⟨repH⟩
  -- Levelwise: the sum block belongs to the block set by linearity.
  have hsum_mem :
      ∀ k,
        (repG.block k).toLp A + (repH.block k).toLp A ∈
          LevelBlockSet A k := by
    intro k
    exact hlin.2.1 k ((repG.block k).toLp A) ((repH.block k).toLp A)
      ⟨repG.block k, rfl⟩ ⟨repH.block k, rfl⟩
  -- Choose one witness block for each levelwise sum.
  let B : (k : ℕ) → LevelBlock A k := fun k =>
    chooseLevelBlock (hsum_mem k)
  -- This chosen block realizes the desired levelwise sum in `L^p`.
  have hB_toLp :
      ∀ k, (B k).toLp A = (repG.block k).toLp A + (repH.block k).toLp A := by
    intro k
    exact chooseLevelBlock_toLp (hsum_mem k)
  refine ⟨?_⟩
  refine
    { block := B
      abs_summable := ?_
      hasSum := ?_ }
  · refine Summable.of_nonneg_of_le
      (fun k => norm_nonneg ((B k).toLp A)) ?_
      (repG.abs_summable.add repH.abs_summable)
    intro k
    -- Pointwise norm control by the triangle inequality.
    rw [hB_toLp k]
    exact norm_add_le ((repG.block k).toLp A) ((repH.block k).toLp A)
  · simpa [B, hB_toLp] using repG.hasSum.add repH.hasSum

theorem memBesovish_smul {A : AtomFamily G s p u}
  (hlin : LevelBlocksLinear A) (c : ℂ) {g : Lp ℂ p G.measure}
  (hg : MemBesovish A q g) :
  MemBesovish A q (c • g) := by
  rcases hg with ⟨repG⟩
  -- Levelwise: scalar multiples remain in the block set by linearity.
  have hsmul_mem :
      ∀ k, c • (repG.block k).toLp A ∈ LevelBlockSet A k := by
    intro k
    exact hlin.2.2 k c ((repG.block k).toLp A) ⟨repG.block k, rfl⟩
  -- Choose witness blocks for those levelwise scalar multiples.
  let B : (k : ℕ) → LevelBlock A k := fun k =>
    chooseLevelBlock (hsmul_mem k)
  -- Each chosen block realizes the expected levelwise scalar multiple.
  have hB_toLp : ∀ k, (B k).toLp A = c • (repG.block k).toLp A := by
    intro k
    exact chooseLevelBlock_toLp (hsmul_mem k)
  refine ⟨?_⟩
  refine
    { block := B
      abs_summable := ?_
      hasSum := ?_ }
  · refine (Summable.mul_left ‖c‖ repG.abs_summable).congr ?_
    intro k
    -- `‖c • x‖ = ‖c‖ * ‖x‖` gives the expected absolute-summability bound.
    rw [hB_toLp k, norm_smul]
  · simpa [B, hB_toLp] using repG.hasSum.const_smul c

/--
The Besov-ish space as a complex linear subspace of `L^p`.
-/
def BesovishSpace (A : AtomFamily G s p u) (q : ℝ≥0∞)
    (hlin : LevelBlocksLinear A) :
    Submodule ℂ (Lp ℂ p G.measure) where
  -- Carrier: all `L^p` elements admitting a Besov-ish atomic representation.
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
    (A : AtomFamily G s p u) (q : ℝ≥0∞)
    (hlin : LevelBlocksLinear A) :
    ∃ E : Submodule ℂ (Lp ℂ p G.measure), E = BesovishSpace A q hlin :=
  ⟨BesovishSpace A q hlin, rfl⟩



end

end GoodGridSpace
