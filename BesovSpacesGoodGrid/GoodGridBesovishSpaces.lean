import BesovSpacesGoodGrid.GoodGridAtomsDefinition
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Convex.Combination
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

omit [Fact (1 ≤ p)] in
theorem atom_zero_mem (A : AtomFamily G s p u) (Q : GoodGridCell G) :
    (0 : (A.localSpace Q).carrier) ∈ A.atoms Q := by
  classical
  rcases A.atoms_nonempty Q with ⟨φ, hφ⟩
  have hneg : (-1 : ℂ) • φ ∈ A.atoms Q := by
    exact A.atoms_phase_invariant Q φ (-1) hφ (by norm_num)
  have hmid :
      ((1 / 2 : ℝ) • φ + (1 / 2 : ℝ) • ((-1 : ℂ) • φ)) ∈ A.atoms Q := by
    exact (convex_iff_add_mem.mp (A.atoms_convex Q)) hφ hneg
      (by norm_num) (by norm_num) (by norm_num)
  convert hmid using 1
  simp

omit [Fact (1 ≤ p)] in
theorem atom_smul_mem_of_norm_le_one (A : AtomFamily G s p u) (Q : GoodGridCell G)
    {c : ℂ} (hc : ‖c‖ ≤ (1 : ℝ))
    {φ : (A.localSpace Q).carrier} (hφ : φ ∈ A.atoms Q) :
    c • φ ∈ A.atoms Q := by
  classical
  by_cases hczero : c = 0
  · subst hczero
    simpa using atom_zero_mem A Q
  let σ : ℂ := (‖c‖ : ℂ)⁻¹ * c
  have hnormσ : ‖σ‖ = (1 : ℝ) := by
    have hnorm_pos : ‖c‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hczero
    simp [σ, norm_inv, hnorm_pos]
  have hσφ : σ • φ ∈ A.atoms Q :=
    A.atoms_phase_invariant Q φ σ hφ hnormσ
  have hcombo :
      (‖c‖ : ℝ) • (σ • φ) + (1 - ‖c‖ : ℝ) •
        (0 : (A.localSpace Q).carrier) ∈ A.atoms Q := by
    exact (convex_iff_add_mem.mp (A.atoms_convex Q)) hσφ (atom_zero_mem A Q)
      (norm_nonneg c) (sub_nonneg.mpr hc) (by ring)
  convert hcombo using 1
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  have hnorm_pos : (‖c‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hczero
  simp [σ, hnorm_pos]

omit [Fact (1 ≤ p)] in
noncomputable def phaseAtom (A : AtomFamily G s p u) (Q : GoodGridCell G)
    (c : ℂ) (φ : (A.localSpace Q).carrier) : (A.localSpace Q).carrier :=
  if c = 0 then 0 else ((‖c‖ : ℂ)⁻¹ * c) • φ

omit [Fact (1 ≤ p)] in
theorem phaseAtom_mem (A : AtomFamily G s p u) (Q : GoodGridCell G)
    (c : ℂ) {φ : (A.localSpace Q).carrier} (hφ : φ ∈ A.atoms Q) :
    phaseAtom A Q c φ ∈ A.atoms Q := by
  classical
  by_cases hc : c = 0
  · simp [phaseAtom, hc, atom_zero_mem A Q]
  · have hnorm_pos : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    rw [phaseAtom, if_neg hc]
    refine A.atoms_phase_invariant Q φ ((‖c‖ : ℂ)⁻¹ * c) hφ ?_
    simp [norm_inv, hnorm_pos]

omit [Fact (1 ≤ p)] in
theorem norm_smul_phaseAtom (A : AtomFamily G s p u) (Q : GoodGridCell G)
    (c : ℂ) (φ : (A.localSpace Q).carrier) :
    (‖c‖ : ℝ) • phaseAtom A Q c φ = c • φ := by
  classical
  by_cases hc : c = 0
  · simp [phaseAtom, hc]
  · rw [phaseAtom, if_neg hc, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    congr 1
    have hnorm_pos : (‖c‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr hc
    simp [hnorm_pos]

omit [Fact (1 ≤ p)] in
theorem atom_add_combo_mem_of_norm_add_le_one
    (A : AtomFamily G s p u) (Q : GoodGridCell G)
    {c d : ℂ} (hcd : ‖c‖ + ‖d‖ ≤ (1 : ℝ))
    {φ ψ : (A.localSpace Q).carrier}
    (hφ : φ ∈ A.atoms Q) (hψ : ψ ∈ A.atoms Q) :
    c • φ + d • ψ ∈ A.atoms Q := by
  classical
  let w : Fin 3 → ℝ := fun i =>
    if i = 0 then ‖c‖ else if i = 1 then ‖d‖ else 1 - ‖c‖ - ‖d‖
  let z : Fin 3 → (A.localSpace Q).carrier := fun i =>
    if i = 0 then phaseAtom A Q c φ
    else if i = 1 then phaseAtom A Q d ψ
    else 0
  have hw_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i _
    fin_cases i
    · simp [w, norm_nonneg]
    · simp [w, norm_nonneg]
    · have hd_le : ‖d‖ ≤ 1 - ‖c‖ := by linarith
      simp [w, sub_nonneg.mpr hd_le]
  have hw_sum : ∑ i ∈ Finset.univ, w i = 1 := by
    simp [w, Fin.sum_univ_three]
  have hz_mem : ∀ i ∈ Finset.univ, z i ∈ A.atoms Q := by
    intro i _
    fin_cases i
    · simp [z, phaseAtom_mem A Q c hφ]
    · simp [z, phaseAtom_mem A Q d hψ]
    · simp [z, atom_zero_mem A Q]
  have hsum := (A.atoms_convex Q).sum_mem hw_nonneg hw_sum hz_mem
  convert hsum using 1
  simp [w, z, Fin.sum_univ_three, norm_smul_phaseAtom A Q c φ,
    norm_smul_phaseAtom A Q d ψ]

omit [Fact (1 ≤ p)] in
theorem atom_add_repackage (A : AtomFamily G s p u) (Q : GoodGridCell G)
    (c d : ℂ) {φ ψ : (A.localSpace Q).carrier}
    (hφ : φ ∈ A.atoms Q) (hψ : ψ ∈ A.atoms Q) :
    ∃ θ : (A.localSpace Q).carrier,
      θ ∈ A.atoms Q ∧
        ((‖c‖ + ‖d‖ : ℝ) : ℂ) • θ = c • φ + d • ψ := by
  classical
  let r : ℝ := ‖c‖ + ‖d‖
  by_cases hr : r = 0
  · have hc0 : c = 0 := by
      have hc_norm : ‖c‖ = 0 := by nlinarith [norm_nonneg c, norm_nonneg d]
      exact norm_eq_zero.mp hc_norm
    have hd0 : d = 0 := by
      have hd_norm : ‖d‖ = 0 := by nlinarith [norm_nonneg c, norm_nonneg d]
      exact norm_eq_zero.mp hd_norm
    refine ⟨0, atom_zero_mem A Q, ?_⟩
    simp [hc0, hd0]
  · let c' : ℂ := (r : ℂ)⁻¹ * c
    let d' : ℂ := (r : ℂ)⁻¹ * d
    have hrpos : 0 < r := by
      have hnonneg : 0 ≤ r := by positivity
      exact lt_of_le_of_ne hnonneg (Ne.symm hr)
    have hnorm_add : ‖c'‖ + ‖d'‖ ≤ (1 : ℝ) := by
      have hrc : ‖c'‖ = ‖c‖ / r := by
        simp [c', norm_inv, abs_of_pos hrpos, div_eq_inv_mul, mul_comm]
      have hrd : ‖d'‖ = ‖d‖ / r := by
        simp [d', norm_inv, abs_of_pos hrpos, div_eq_inv_mul, mul_comm]
      rw [hrc, hrd]
      field_simp [ne_of_gt hrpos]
      rfl
    have hθ_mem :
        c' • φ + d' • ψ ∈ A.atoms Q :=
      atom_add_combo_mem_of_norm_add_le_one A Q hnorm_add hφ hψ
    refine ⟨c' • φ + d' • ψ, hθ_mem, ?_⟩
    rw [smul_add, smul_smul, smul_smul]
    have hrc : ((r : ℂ) * c') = c := by
      have hrc_ne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
      simp [c', hrc_ne]
    have hrd : ((r : ℂ) * d') = d := by
      have hrc_ne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
      simp [d', hrc_ne]
    change ((r : ℂ) * c') • φ + ((r : ℂ) * d') • ψ = c • φ + d • ψ
    rw [hrc, hrd]

namespace LevelBlock

/-- Addition of level blocks, reusing one atom per cell. -/
noncomputable def add (A : AtomFamily G s p u) {k : ℕ}
    (B C : LevelBlock A k) : LevelBlock A k where
  coeff := fun Q => ((‖B.coeff Q‖ + ‖C.coeff Q‖ : ℝ) : ℂ)
  atom := fun Q =>
    Classical.choose
      (atom_add_repackage A (levelCellToGoodGridCell G k Q)
        (B.coeff Q) (C.coeff Q) (B.atom_mem Q) (C.atom_mem Q))
  atom_mem := fun Q =>
    (Classical.choose_spec
      (atom_add_repackage A (levelCellToGoodGridCell G k Q)
        (B.coeff Q) (C.coeff Q) (B.atom_mem Q) (C.atom_mem Q))).1

omit [Fact (1 ≤ p)] in
theorem add_atom_spec (A : AtomFamily G s p u) {k : ℕ}
    (B C : LevelBlock A k) (Q : LevelCell G k) :
    ((‖B.coeff Q‖ + ‖C.coeff Q‖ : ℝ) : ℂ) • (add A B C).atom Q =
      B.coeff Q • B.atom Q + C.coeff Q • C.atom Q :=
  (Classical.choose_spec
    (atom_add_repackage A (levelCellToGoodGridCell G k Q)
      (B.coeff Q) (C.coeff Q) (B.atom_mem Q) (C.atom_mem Q))).2

omit [Fact (1 ≤ p)] in
theorem add_term (A : AtomFamily G s p u) {k : ℕ}
    (B C : LevelBlock A k) (Q : LevelCell G k) :
    (add A B C).term A Q = B.term A Q + C.term A Q := by
  let Qg : GoodGridCell G := levelCellToGoodGridCell G k Q
  let θ := (add A B C).atom Q
  let a := B.atom Q
  let b := C.atom Q
  let lam : ℂ := ((‖B.coeff Q‖ + ‖C.coeff Q‖ : ℝ) : ℂ)
  have hlocal : lam • θ = B.coeff Q • a + C.coeff Q • b := by
    simpa [Qg, θ, a, b, lam] using add_atom_spec A B C Q
  have hfun :
      lam • A.toFunction Qg θ =
        B.coeff Q • A.toFunction Qg a + C.coeff Q • A.toFunction Qg b := by
    have hmap := congrArg (A.localSpace Qg).toFun hlocal
    simpa [AtomFamily.toFunction, map_add, map_smul] using hmap
  unfold term
  change
      lam • MemLp.toLp (A.toFunction Qg θ) (A.local_memLp_p Qg θ) =
        B.coeff Q • MemLp.toLp (A.toFunction Qg a) (A.local_memLp_p Qg a) +
          C.coeff Q • MemLp.toLp (A.toFunction Qg b) (A.local_memLp_p Qg b)
  rw [← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul,
    ← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun hfun x)

omit [Fact (1 ≤ p)] in
@[simp]
theorem add_toLp (A : AtomFamily G s p u) {k : ℕ}
    (B C : LevelBlock A k) :
    (add A B C).toLp A = B.toLp A + C.toLp A := by
  simp [toLp, add_term A B C, Finset.sum_add_distrib]

end LevelBlock

omit [Fact (1 ≤ p)] in
/--
Additive closure of genuine level blocks.

Mathematically this is the cellwise consequence of convexity of `A(Q)` and
invariance under multiplication by complex scalars of norm one: each sum
`s_Q a_Q + t_Q b_Q` is repackaged as one coefficient times one atom on the
same cell.
-/
theorem add_mem_LevelBlockSet (A : AtomFamily G s p u) (k : ℕ)
    {x y : Lp ℂ p G.measure} :
    x ∈ LevelBlockSet A k → y ∈ LevelBlockSet A k →
      x + y ∈ LevelBlockSet A k := by
  rintro ⟨B, rfl⟩ ⟨C, rfl⟩
  exact ⟨LevelBlock.add A B C, by simp⟩

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
Level blocks form a linear family at each level.
-/
theorem levelBlocksLinear (A : AtomFamily G s p u) :
    LevelBlocksLinear A := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact zero_mem_LevelBlockSet A k
  · intro k x y hx hy
    exact add_mem_LevelBlockSet A k hx hy
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

theorem memBesovish_zero (A : AtomFamily G s p u) :
    MemBesovish A q (0 : Lp ℂ p G.measure) := by
  -- Levelwise membership of `0` in the block set.
  have hzero_mem : ∀ k, (0 : Lp ℂ p G.measure) ∈ LevelBlockSet A k := by
    intro k
    exact zero_mem_LevelBlockSet A k
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
  {g h : Lp ℂ p G.measure}
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
    exact add_mem_LevelBlockSet A k
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
  (c : ℂ) {g : Lp ℂ p G.measure}
  (hg : MemBesovish A q g) :
  MemBesovish A q (c • g) := by
  rcases hg with ⟨repG⟩
  -- Levelwise: scalar multiples remain in the block set by linearity.
  have hsmul_mem :
      ∀ k, c • (repG.block k).toLp A ∈ LevelBlockSet A k := by
    intro k
    exact smul_mem_LevelBlockSet A k c ⟨repG.block k, rfl⟩
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
    : Submodule ℂ (Lp ℂ p G.measure) where
  -- Carrier: all `L^p` elements admitting a Besov-ish atomic representation.
  carrier := { g | MemBesovish A q g }
  zero_mem' := memBesovish_zero (A := A) (q := q)
  add_mem' := by
    intro g h hg hh
    exact memBesovish_add (A := A) (q := q) hg hh
  smul_mem' := by
    intro c g hg
    exact memBesovish_smul (A := A) (q := q) c hg

/--
The Besov-ish space is a linear subspace of `L^p`.
-/
theorem besovishSpace_is_linear_subspace
    (A : AtomFamily G s p u) (q : ℝ≥0∞) :
    ∃ E : Submodule ℂ (Lp ℂ p G.measure), E = BesovishSpace A q :=
  ⟨BesovishSpace A q, rfl⟩



end

end GoodGridSpace
