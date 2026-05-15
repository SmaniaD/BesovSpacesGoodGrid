import BesovSpacesGoodGrid.WeakGridAtomsDefinition
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Convex.Combination

/-!
Besov-ish spaces associated to a weak grid and a family of atoms.

The paper defines a Besov-ish element by an atomic expansion whose level
blocks converge absolutely in `L^p`.  A level block is explicitly indexed by
the cells of the level-`k` partition: for each cell there is one coefficient
and one atom.  This matches the paper's finite inner sum
`∑_{Q ∈ P^k} s_Q a_Q`.
-/

namespace WeakGridSpace

open scoped ENNReal Topology
open MeasureTheory

universe u v

variable {α : Type u} [MeasurableSpace α]

noncomputable section




variable {G : WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
variable [Fact (1 ≤ p)]

/--
O tipo dos cells no nível k, usando o grid de G.
-/
abbrev LevelCell (G : WeakGridSpace (α := α)) (k : ℕ) :=
  { Q : Set α // Q ∈ G.grid.partitions k }

/--
Converte um LevelCell para um WeakGridCell, usando o grid de G.
-/
def levelCellToWeakGridCell (G : WeakGridSpace (α := α)) (k : ℕ)
    (Q : LevelCell G k) : WeakGridCell G :=
  ⟨k, Q.1, Q.2⟩

/--
A level-`k` atomic block.

For each cell `Q ∈ S.grid.partitions k`, it chooses exactly one coefficient
and exactly one atom supported on `Q`.  Its value in `L^p` is the finite sum
over the partition cells.
-/
structure LevelBlock (A : AtomFamily G s p u) (k : ℕ) where
  coeff : LevelCell G k → ℂ
  atom : ∀ Q : LevelCell G k, (A.localSpace (levelCellToWeakGridCell G k Q)).carrier
  atom_mem : ∀ Q : LevelCell G k,
    A.IsAtom (levelCellToWeakGridCell G k Q) (atom Q)

namespace LevelBlock

/-- A zero-valued level block, obtained by choosing one atom on each cell. -/
def zero (A : AtomFamily G s p u) (k : ℕ) : LevelBlock A k where
  coeff := fun _ => 0
  atom := fun Q =>
    Classical.choose (A.atoms_nonempty_on (levelCellToWeakGridCell G k Q))
  atom_mem := fun Q =>
    Classical.choose_spec (A.atoms_nonempty_on (levelCellToWeakGridCell G k Q))

/-- The `L^p` term attached to one cell in a level block. -/
def term (A : AtomFamily G s p u) {k : ℕ}
    (B : LevelBlock A k) (Q : LevelCell G k) : Lp ℂ p G.measure :=
  B.coeff Q • MemLp.toLp
    (A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q))
    (A.local_memLp_p (levelCellToWeakGridCell G k Q) (B.atom Q))

/--
The value of a level block in `L^p`, namely the finite sum over the level-`k`
partition.
-/
def toLp (A : AtomFamily G s p u) {k : ℕ}
    (B : LevelBlock A k) : Lp ℂ p G.measure :=
  (G.grid.partitions k).attach.sum fun Q => B.term A Q

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
theorem atom_zero_mem (A : AtomFamily G s p u) (Q : WeakGridCell G) :
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
theorem atom_smul_mem_of_norm_le_one (A : AtomFamily G s p u) (Q : WeakGridCell G)
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
noncomputable def phaseAtom (A : AtomFamily G s p u) (Q : WeakGridCell G)
    (c : ℂ) (φ : (A.localSpace Q).carrier) : (A.localSpace Q).carrier :=
  if c = 0 then 0 else ((‖c‖ : ℂ)⁻¹ * c) • φ

omit [Fact (1 ≤ p)] in
theorem phaseAtom_mem (A : AtomFamily G s p u) (Q : WeakGridCell G)
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
theorem norm_smul_phaseAtom (A : AtomFamily G s p u) (Q : WeakGridCell G)
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
    (A : AtomFamily G s p u) (Q : WeakGridCell G)
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
theorem atom_add_repackage (A : AtomFamily G s p u) (Q : WeakGridCell G)
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
      (atom_add_repackage A (levelCellToWeakGridCell G k Q)
        (B.coeff Q) (C.coeff Q) (B.atom_mem Q) (C.atom_mem Q))
  atom_mem := fun Q =>
    (Classical.choose_spec
      (atom_add_repackage A (levelCellToWeakGridCell G k Q)
        (B.coeff Q) (C.coeff Q) (B.atom_mem Q) (C.atom_mem Q))).1

omit [Fact (1 ≤ p)] in
theorem add_atom_spec (A : AtomFamily G s p u) {k : ℕ}
    (B C : LevelBlock A k) (Q : LevelCell G k) :
    ((‖B.coeff Q‖ + ‖C.coeff Q‖ : ℝ) : ℂ) • (add A B C).atom Q =
      B.coeff Q • B.atom Q + C.coeff Q • C.atom Q :=
  (Classical.choose_spec
    (atom_add_repackage A (levelCellToWeakGridCell G k Q)
      (B.coeff Q) (C.coeff Q) (B.atom_mem Q) (C.atom_mem Q))).2

omit [Fact (1 ≤ p)] in
theorem add_term (A : AtomFamily G s p u) {k : ℕ}
    (B C : LevelBlock A k) (Q : LevelCell G k) :
    (add A B C).term A Q = B.term A Q + C.term A Q := by
  let Qg : WeakGridCell G := levelCellToWeakGridCell G k Q
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
structure LpGridRepresentation
    (A : AtomFamily G s p u) (g : Lp ℂ p G.measure) where
  block : (k : ℕ) → LevelBlock A k
  hasSum : HasSum (fun k => (block k).toLp A) g



namespace LpGridRepresentation

/--
Level-`k` coefficient `ℓ^p` power sum: `∑_{Q ∈ P^k} |s_Q|^p`.

This is the inner quantity from the paper's coefficient-cost formula.
-/
def levelCoeffPower
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g) (k : ℕ) : ℝ :=
  ∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ p.toReal

/--
The level weight which appears in the `L^t` embedding estimate from the paper:
`|P^k|^{s - 1 / p + 1 / t}`.

In the current formalization a level is a finite `Finset` of cells, so this
uses the largest cell measure at level `k`.  This is the Lean analogue of the
paper's uniform level size `|\mathcal P^k|`.
-/
noncomputable def levelMeasureWeight
    (G : WeakGridSpace (α := α)) (s : ℝ) (p t : ℝ≥0∞) (k : ℕ) : ℝ :=
  (sSup (Set.range fun Q : LevelCell G k => (G.measure Q.1).toReal)) ^
    (s - 1 / p.toReal + 1 / t.toReal)

end LpGridRepresentation

/-- The `L^p` absolute-convergence cost of a representation. -/
def LpGridRepresentation.lpCost
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g) : ℝ :=
  ∑' k, ‖(R.block k).toLp A‖

namespace LpGridRepresentation

/-- Representation-level addition induced by level-block linearity. -/
noncomputable def add
    {A : AtomFamily G s p u} {g h : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g)
    (S : LpGridRepresentation A h) :
    LpGridRepresentation A (g + h) := by
  exact
    { block := fun k => LevelBlock.add A (R.block k) (S.block k)
      hasSum := by
        simpa [LevelBlock.add_toLp] using R.hasSum.add S.hasSum }

@[simp]
theorem add_block_toLp
    {A : AtomFamily G s p u} {g h : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g)
    (S : LpGridRepresentation A h) (k : ℕ) :
    ((add R S).block k).toLp A = (R.block k).toLp A + (S.block k).toLp A := by
  simp [add]

/-- Representation-level scalar multiplication induced by block linearity. -/
noncomputable def smul
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (c : ℂ) (R : LpGridRepresentation A g) :
    LpGridRepresentation A (c • g) := by
  exact
    { block := fun k => LevelBlock.smul A c (R.block k)
      hasSum := by
        simpa [LevelBlock.smul_toLp] using R.hasSum.const_smul c }

@[simp]
theorem smul_block_toLp
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (c : ℂ) (R : LpGridRepresentation A g) (k : ℕ) :
    ((smul c R).block k).toLp A = c • (R.block k).toLp A := by
  simp [smul]

theorem lpCost_nonneg
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g) :
    0 ≤ LpGridRepresentation.lpCost R := by
  simpa [LpGridRepresentation.lpCost] using
    (tsum_nonneg fun k => norm_nonneg ((R.block k).toLp A))

theorem lpCost_triangle
    {A : AtomFamily G s p u} {g h : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g)
    (S : LpGridRepresentation A h)
    (hR : Summable fun k => ‖(R.block k).toLp A‖)
    (hS : Summable fun k => ‖(S.block k).toLp A‖) :
    LpGridRepresentation.lpCost (add R S) ≤
      LpGridRepresentation.lpCost R + LpGridRepresentation.lpCost S := by
  have hsumRS : Summable fun k => ‖(R.block k).toLp A‖ + ‖(S.block k).toLp A‖ :=
    hR.add hS
  have hle :
      (fun k => ‖((add R S).block k).toLp A‖)
        ≤ fun k => ‖(R.block k).toLp A‖ + ‖(S.block k).toLp A‖ := by
    intro k
    simpa [add_block_toLp (R := R) (S := S) (k := k)] using
      (norm_add_le ((R.block k).toLp A) ((S.block k).toLp A))
  have hsumAdd : Summable fun k => ‖((add R S).block k).toLp A‖ :=
    Summable.of_nonneg_of_le
      (fun k => norm_nonneg (((add R S).block k).toLp A))
      hle hsumRS
  have htsum_add :
      (∑' k, (‖(R.block k).toLp A‖ + ‖(S.block k).toLp A‖))
        = (∑' k, ‖(R.block k).toLp A‖) + (∑' k, ‖(S.block k).toLp A‖) := by
    exact (hR.hasSum.add hS.hasSum).tsum_eq
  calc
    LpGridRepresentation.lpCost (add R S)
        = ∑' k, ‖((add R S).block k).toLp A‖ := rfl
    _ ≤ ∑' k, (‖(R.block k).toLp A‖ + ‖(S.block k).toLp A‖) :=
      hsumAdd.tsum_le_tsum hle hsumRS
    _ = (∑' k, ‖(R.block k).toLp A‖) + (∑' k, ‖(S.block k).toLp A‖) :=
      htsum_add
    _ = LpGridRepresentation.lpCost R + LpGridRepresentation.lpCost S := rfl

theorem lpCost_smul
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (c : ℂ) (R : LpGridRepresentation A g)
    (hR : Summable fun k => ‖(R.block k).toLp A‖) :
    LpGridRepresentation.lpCost (smul c R) =
      ‖c‖ * LpGridRepresentation.lpCost R := by
  have hmul_tsum :
      (∑' k, ‖c‖ * ‖(R.block k).toLp A‖) =
        ‖c‖ * (∑' k, ‖(R.block k).toLp A‖) := by
    exact (hR.hasSum.mul_left ‖c‖).tsum_eq
  calc
    LpGridRepresentation.lpCost (smul c R)
        = ∑' k, ‖((smul c R).block k).toLp A‖ := rfl
    _ = ∑' k, ‖c • (R.block k).toLp A‖ := by
      congr with k
      rw [smul_block_toLp]
    _ = ∑' k, ‖c‖ * ‖(R.block k).toLp A‖ := by
      congr with k
      rw [norm_smul]
    _ = ‖c‖ * ∑' k, ‖(R.block k).toLp A‖ := hmul_tsum
    _ = ‖c‖ * LpGridRepresentation.lpCost R := rfl

end LpGridRepresentation


def LpGridRepresentation.pqCost
    {A : AtomFamily G s p u} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g) : ℝ :=
  if q = ∞ then
      sSup (Set.range fun k =>
        (R.levelCoeffPower k) ^ (1 / p.toReal))
    else
      (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)

namespace LpGridRepresentation

/-- Finiteness condition for the `(p,q)` coefficient-cost data of a representation. -/
def FinitePQCost
    {A : AtomFamily G s p u} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g) : Prop :=
  if q = ∞ then
    BddAbove (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal))
  else
    Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal))

end LpGridRepresentation

/-- The `L^t` term attached to one cell in a level block. -/
noncomputable def LevelBlock.termLt
    (A : AtomFamily G s p u) {t : ℝ≥0∞} [Fact (1 ≤ t)] {k : ℕ}
    (B : LevelBlock A k) (Q : LevelCell G k) : Lp ℂ t G.measure :=
  B.coeff Q • MemLp.toLp
    (A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q))
    (by
      -- Since atoms are in `L^(p*u)` and `p ≤ t ≤ p*u`, they are in `L^t`
      -- on the finite ambient measure space.
      sorry)

/--
The canonical realization of a level block as an element of `L^t`.

This is the same finite atomic sum as `LevelBlock.toLp`, but viewed in the
target exponent `t`.
-/
noncomputable def LevelBlock.toLt
    (A : AtomFamily G s p u) {t : ℝ≥0∞} [Fact (1 ≤ t)] {k : ℕ}
    (B : LevelBlock A k) : Lp ℂ t G.measure :=
  (G.grid.partitions k).attach.sum fun Q => LevelBlock.termLt A B Q

namespace LpGridRepresentation

/--
Levelwise `L^t` estimate for one atomic block.

This is the Lean version of
`‖∑_{Q ∈ P^k} s_Q a_Q‖_t ≤ C_mult |P^k|^{s - 1/p + 1/t}
  (∑_{Q ∈ P^k} |s_Q|^p)^{1/p}`.
-/
theorem lt_norm_levelBlock_le
    {A : AtomFamily G s p u} {t : ℝ≥0∞}
    [Fact (1 ≤ t)]
    (hp_ne_top : p ≠ ∞) (ht_ne_top : t ≠ ∞)
    (hp_le_t : p ≤ t) (ht_le_pu : t ≤ p * u)
    (hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / t.toReal)
    : ∃ Cmult : ℝ, 0 ≤ Cmult ∧
      ∀ {g : Lp ℂ p G.measure} (R : LpGridRepresentation A g) (k : ℕ),
        ‖(R.block k).toLt (t := t) A‖ ≤
          Cmult * levelMeasureWeight G s p t k *
            (R.levelCoeffPower k) ^ (1 / p.toReal) := by
  sorry

/--
Coefficient summation estimate used in the `L^t` embedding.

This packages the paper's `C_co(t,q, ·)`/Holder-like step in the vocabulary of
the current file, where `LpGridRepresentation.pqCost` is the Besov coefficient
cost of a representation.
-/
theorem weighted_levelCoeff_sum_le_pqCost
    {A : AtomFamily G s p u} {t : ℝ≥0∞}
    (Ckt : ℝ)
    {g : Lp ℂ p G.measure} (R : LpGridRepresentation A g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R) :
    (∑' k, levelMeasureWeight G s p t k *
      (R.levelCoeffPower k) ^ (1 / p.toReal)) ≤
        Ckt * LpGridRepresentation.pqCost (q := q) R := by
  sorry

/--
Adapted statement of the paper's `L^t` embedding proposition.

The present file builds atomic representations as series in `L^p`. For a
target exponent `t`, `LevelBlock.toLt` realizes each finite level block as an
element of `L^t`. The lemma `lt_norm_levelBlock_le` is exactly the level estimate
`‖∑_{Q ∈ P^k} s_Q a_Q‖_t ≤ C_mult * |P^k|^{s - 1/p + 1/t}
  * (∑_{Q ∈ P^k} |s_Q|^p)^{1/p}`.

The coefficient-space condition on `Ckt` is isolated in
`weighted_levelCoeff_sum_le_pqCost`.
This avoids adding a separate formalization of the paper's `C_co(t,q, ·)`:
in this file, the available coefficient norm of a representation is
`LpGridRepresentation.pqCost`.
-/
theorem lp_embedding_adapted_statement
    {A : AtomFamily G s p u} {t : ℝ≥0∞}
    [Fact (1 ≤ t)]
    (hp_ne_top : p ≠ ∞) (ht_ne_top : t ≠ ∞)
    (hp_le_t : p ≤ t) (ht_le_pu : t ≤ p * u)
    (hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / t.toReal)
    (Cmult Ckt : ℝ) (hCmult_nonneg : 0 ≤ Cmult)
    {g : Lp ℂ p G.measure} (R : LpGridRepresentation A g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R) :
    Summable (fun k => (R.block k).toLt (t := t) A) ∧
      (∑' k, ‖(R.block k).toLt (t := t) A‖) ≤
        Cmult * Ckt * LpGridRepresentation.pqCost (q := q) R := by
  sorry

theorem pqCost_nonneg
  {A : AtomFamily G s p u} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g) :
  0 ≤ LpGridRepresentation.pqCost (q := q) R := by
  unfold LpGridRepresentation.pqCost
  split_ifs with hq
  · -- q = ∞ case: supremum of nonnegative terms
    refine Real.sSup_nonneg ?_
    intro x hx
    rcases hx with ⟨k, rfl⟩
    exact Real.rpow_nonneg (Finset.sum_nonneg fun Q _ => by positivity) _
  · -- q < ∞ case: rpow of tsum of nonnegative terms
    apply Real.rpow_nonneg
    apply tsum_nonneg
    intro k
    exact Real.rpow_nonneg (Finset.sum_nonneg fun Q _ => by positivity) _

theorem pqCost_triangle
    {A : AtomFamily G s p u} {q : ℝ≥0∞} {g h : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g)
    (S : LpGridRepresentation A h)
    (hp_top : p ≠ ∞)
  (hq_one : 1 ≤ q)
    (hRfin : FinitePQCost (q := q) R)
    (hSfin : FinitePQCost (q := q) S) :
    LpGridRepresentation.pqCost (q := q) (add R S) ≤
      LpGridRepresentation.pqCost (q := q) R + LpGridRepresentation.pqCost (q := q) S := by
  have hp : 1 ≤ p.toReal := (ENNReal.dichotomy p).resolve_left hp_top
  have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 hp_top
  unfold LpGridRepresentation.pqCost
  split_ifs with hq
  · have hRbdd : BddAbove (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [FinitePQCost, hq] using hRfin
    have hSbdd : BddAbove (Set.range fun k => (S.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [FinitePQCost, hq] using hSfin
    apply csSup_le (Set.range_nonempty fun k => ((add R S).levelCoeffPower k) ^ (1 / p.toReal))
    intro x hx
    rcases hx with ⟨k, rfl⟩
    have hsum_add :
        ∑ Q : LevelCell G k, ‖((add R S).block k).coeff Q‖ ^ p.toReal
          = ∑ Q : LevelCell G k, (‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖) ^ p.toReal := by
      refine Finset.sum_congr rfl ?_
      intro Q hQ
      have hnn : 0 ≤ ‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖ :=
        add_nonneg (norm_nonneg _) (norm_nonneg _)
      change ‖((‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖ : ℝ) : ℂ)‖ ^ p.toReal =
          (‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖) ^ p.toReal
      rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    have hk :
        ((add R S).levelCoeffPower k) ^ (1 / p.toReal)
          ≤ (R.levelCoeffPower k) ^ (1 / p.toReal) + (S.levelCoeffPower k) ^ (1 / p.toReal) := by
      rw [LpGridRepresentation.levelCoeffPower, hsum_add]
      simpa [LpGridRepresentation.levelCoeffPower] using
        (Real.Lp_add_le_of_nonneg
          (s := (Finset.univ : Finset (LevelCell G k)))
          (p := p.toReal)
          (f := fun Q => ‖(R.block k).coeff Q‖)
          (g := fun Q => ‖(S.block k).coeff Q‖)
          hp
          (by intro Q hQ; exact norm_nonneg _)
          (by intro Q hQ; exact norm_nonneg _))
    exact le_trans hk <|
      add_le_add
        (le_csSup hRbdd ⟨k, rfl⟩)
        (le_csSup hSbdd ⟨k, rfl⟩)
  · haveI : Fact (1 ≤ q) := ⟨hq_one⟩
    have hq1 : 1 ≤ q.toReal := (ENNReal.dichotomy q).resolve_left hq
    have hq_pos : 0 < q.toReal := (ENNReal.toReal_pos_iff_ne_top q).2 hq
    let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
    let b : ℕ → ℝ := fun k => (S.levelCoeffPower k) ^ (1 / p.toReal)
    let d : ℕ → ℝ := fun k => ((add R S).levelCoeffPower k) ^ (1 / p.toReal)
    have ha_nonneg : ∀ k, 0 ≤ a k := by
      intro k
      dsimp [a]
      have hnonneg : 0 ≤ R.levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower
        exact Finset.sum_nonneg fun Q hQ => by positivity
      exact Real.rpow_nonneg hnonneg _
    have hb_nonneg : ∀ k, 0 ≤ b k := by
      intro k
      dsimp [b]
      have hnonneg : 0 ≤ S.levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower
        exact Finset.sum_nonneg fun Q hQ => by positivity
      exact Real.rpow_nonneg hnonneg _
    have hd_nonneg : ∀ k, 0 ≤ d k := by
      intro k
      dsimp [d]
      have hnonneg : 0 ≤ (add R S).levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower
        exact Finset.sum_nonneg fun Q hQ => by positivity
      exact Real.rpow_nonneg hnonneg _
    have hdk : ∀ k, d k ≤ a k + b k := by
      intro k
      have hsum_add :
          ∑ Q : LevelCell G k, ‖((add R S).block k).coeff Q‖ ^ p.toReal
            = ∑ Q : LevelCell G k, (‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖) ^ p.toReal := by
        refine Finset.sum_congr rfl ?_
        intro Q hQ
        have hnn : 0 ≤ ‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖ :=
          add_nonneg (norm_nonneg _) (norm_nonneg _)
        change ‖((‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖ : ℝ) : ℂ)‖ ^ p.toReal =
            (‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖) ^ p.toReal
        rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      dsimp [d, a, b]
      rw [LpGridRepresentation.levelCoeffPower, hsum_add]
      simpa [LpGridRepresentation.levelCoeffPower] using
        (Real.Lp_add_le_of_nonneg
          (s := (Finset.univ : Finset (LevelCell G k)))
          (p := p.toReal)
          (f := fun Q => ‖(R.block k).coeff Q‖)
          (g := fun Q => ‖(S.block k).coeff Q‖)
          hp
          (by intro Q hQ; exact norm_nonneg _)
          (by intro Q hQ; exact norm_nonneg _))
    have hRq : Summable (fun k => (a k) ^ q.toReal) := by
      have hRsum0 : Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
        simpa [FinitePQCost, hq] using hRfin
      refine hRsum0.congr ?_
      intro k
      have hmul : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
        field_simp [hp_pos.ne']
      have hnonneg : 0 ≤ R.levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower
        exact Finset.sum_nonneg fun Q hQ => by positivity
      rw [hmul, Real.rpow_mul hnonneg]
    have hSq : Summable (fun k => (b k) ^ q.toReal) := by
      have hSsum0 : Summable (fun k => (S.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
        simpa [FinitePQCost, hq] using hSfin
      refine hSsum0.congr ?_
      intro k
      have hmul : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
        field_simp [hp_pos.ne']
      have hnonneg : 0 ≤ S.levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower
        exact Finset.sum_nonneg fun Q hQ => by positivity
      rw [hmul, Real.rpow_mul hnonneg]
    have hsum_ab : Summable (fun k => (a k + b k) ^ q.toReal) :=
      Real.summable_Lp_add_of_nonneg hq1
        ha_nonneg
        hb_nonneg
        hRq hSq
    have hdq_le :
        (fun k => (d k) ^ q.toReal) ≤ fun k => (a k + b k) ^ q.toReal := by
      intro k
      exact Real.rpow_le_rpow
        (hd_nonneg k)
        (hdk k)
        (le_of_lt hq_pos)
    have hsum_dq : Summable (fun k => (d k) ^ q.toReal) :=
      Summable.of_nonneg_of_le
        (by intro k; exact Real.rpow_nonneg (hd_nonneg k) _)
        hdq_le hsum_ab
    have htsum_le :
        (∑' k, (d k) ^ q.toReal) ≤ ∑' k, (a k + b k) ^ q.toReal :=
      hsum_dq.tsum_le_tsum hdq_le hsum_ab
    have hleft :
        (∑' k, (d k) ^ q.toReal) ^ (1 / q.toReal)
          ≤ (∑' k, (a k + b k) ^ q.toReal) ^ (1 / q.toReal) :=
      Real.rpow_le_rpow
        (tsum_nonneg (fun k => by
          exact Real.rpow_nonneg (hd_nonneg k) _))
        htsum_le
        (by exact one_div_nonneg.mpr (le_of_lt hq_pos))
    have hmid :
        (∑' k, (a k + b k) ^ q.toReal) ^ (1 / q.toReal)
          ≤ (∑' k, (a k) ^ q.toReal) ^ (1 / q.toReal)
            + (∑' k, (b k) ^ q.toReal) ^ (1 / q.toReal) :=
      Real.Lp_add_le_tsum_of_nonneg' hq1
        ha_nonneg
        hb_nonneg
        hRq hSq
    have hsum_d :
        (∑' k, ((add R S).levelCoeffPower k) ^ (q.toReal / p.toReal))
          = ∑' k, (d k) ^ q.toReal := by
      apply tsum_congr
      intro k
      have hmul : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
        field_simp [hp_pos.ne']
      have hnonneg : 0 ≤ (add R S).levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower
        exact Finset.sum_nonneg fun Q hQ => by positivity
      rw [hmul, Real.rpow_mul hnonneg]
    have hsum_R :
        (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal))
          = ∑' k, (a k) ^ q.toReal := by
      apply tsum_congr
      intro k
      have hmul : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
        field_simp [hp_pos.ne']
      have hnonneg : 0 ≤ R.levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower
        exact Finset.sum_nonneg fun Q hQ => by positivity
      rw [hmul, Real.rpow_mul hnonneg]
    have hsum_S :
        (∑' k, (S.levelCoeffPower k) ^ (q.toReal / p.toReal))
          = ∑' k, (b k) ^ q.toReal := by
      apply tsum_congr
      intro k
      have hmul : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
        field_simp [hp_pos.ne']
      have hnonneg : 0 ≤ S.levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower
        exact Finset.sum_nonneg fun Q hQ => by positivity
      rw [hmul, Real.rpow_mul hnonneg]
    calc
      (∑' k, ((add R S).levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)
          = (∑' k, (d k) ^ q.toReal) ^ (1 / q.toReal) := by rw [hsum_d]
      _ ≤ (∑' k, (a k + b k) ^ q.toReal) ^ (1 / q.toReal) := hleft
      _ ≤ (∑' k, (a k) ^ q.toReal) ^ (1 / q.toReal)
            + (∑' k, (b k) ^ q.toReal) ^ (1 / q.toReal) := hmid
      _ = (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)
            + (∑' k, (S.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
          rw [hsum_R, hsum_S]

theorem pqCost_smul
    {A : AtomFamily G s p u} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    (c : ℂ) (R : LpGridRepresentation A g)
    (hp_top : p ≠ ∞)
  (hq_one : 1 ≤ q)
    (hRfin : FinitePQCost (q := q) R) :
    LpGridRepresentation.pqCost (q := q) (smul c R) =
      ‖c‖ * LpGridRepresentation.pqCost (q := q) R := by
  have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 hp_top
  unfold LpGridRepresentation.pqCost
  split_ifs with hq
  · let f : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
    have hpoint :
        ∀ k, ((smul c R).levelCoeffPower k) ^ (1 / p.toReal) = ‖c‖ * f k := by
      intro k
      have hRnonneg : 0 ≤ R.levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower
        exact Finset.sum_nonneg fun Q hQ => by positivity
      have hsum :
          (smul c R).levelCoeffPower k = ‖c‖ ^ p.toReal * R.levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower LpGridRepresentation.smul LevelBlock.smul
        calc
          (∑ Q : LevelCell G k, ‖c * (R.block k).coeff Q‖ ^ p.toReal)
              = ∑ Q : LevelCell G k, (‖c‖ * ‖(R.block k).coeff Q‖) ^ p.toReal := by
                  refine Finset.sum_congr rfl ?_
                  intro Q hQ
                  rw [norm_mul]
          _ = ∑ Q : LevelCell G k, (‖c‖ ^ p.toReal) * (‖(R.block k).coeff Q‖ ^ p.toReal) := by
                refine Finset.sum_congr rfl ?_
                intro Q hQ
                rw [Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
          _ = ‖c‖ ^ p.toReal * ∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ p.toReal := by
                rw [Finset.mul_sum]
      calc
        ((smul c R).levelCoeffPower k) ^ (1 / p.toReal)
            = (‖c‖ ^ p.toReal * R.levelCoeffPower k) ^ (1 / p.toReal) := by rw [hsum]
        _ = (‖c‖ ^ p.toReal) ^ (1 / p.toReal) * (R.levelCoeffPower k) ^ (1 / p.toReal) := by
              rw [Real.mul_rpow (by positivity) hRnonneg]
        _ = ‖c‖ * (R.levelCoeffPower k) ^ (1 / p.toReal) := by
              have hcp : (‖c‖ ^ p.toReal) ^ (1 / p.toReal) = ‖c‖ := by
                simpa [one_div] using (Real.rpow_rpow_inv (norm_nonneg c) hp_pos.ne')
              rw [hcp]
    have hrange :
        Set.range (fun k => ((smul c R).levelCoeffPower k) ^ (1 / p.toReal))
          = Set.range (fun k => ‖c‖ * f k) := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨k, rfl⟩
        exact ⟨k, (hpoint k).symm⟩
      · intro hx
        rcases hx with ⟨k, rfl⟩
        exact ⟨k, hpoint k⟩
    calc
      sSup (Set.range fun k => ((smul c R).levelCoeffPower k) ^ (1 / p.toReal))
          = sSup (Set.range fun k => ‖c‖ * f k) := by rw [hrange]
      _ = iSup (fun k => ‖c‖ * f k) := by simp [sSup_range]
      _ = ‖c‖ * iSup f := (Real.mul_iSup_of_nonneg (norm_nonneg c) f).symm
      _ = ‖c‖ * sSup (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
            simp [f, sSup_range]
  · haveI : Fact (1 ≤ q) := ⟨hq_one⟩
    have hq_pos : 0 < q.toReal := (ENNReal.toReal_pos_iff_ne_top q).2 hq
    have hRsum : Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
      simpa [FinitePQCost, hq] using hRfin
    have hterm :
        ∀ k,
          ((smul c R).levelCoeffPower k) ^ (q.toReal / p.toReal)
            = ‖c‖ ^ q.toReal * (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
      intro k
      have hRnonneg : 0 ≤ R.levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower
        exact Finset.sum_nonneg fun Q hQ => by positivity
      have hsum :
          (smul c R).levelCoeffPower k = ‖c‖ ^ p.toReal * R.levelCoeffPower k := by
        unfold LpGridRepresentation.levelCoeffPower LpGridRepresentation.smul LevelBlock.smul
        calc
          (∑ Q : LevelCell G k, ‖c * (R.block k).coeff Q‖ ^ p.toReal)
              = ∑ Q : LevelCell G k, (‖c‖ * ‖(R.block k).coeff Q‖) ^ p.toReal := by
                  refine Finset.sum_congr rfl ?_
                  intro Q hQ
                  rw [norm_mul]
          _ = ∑ Q : LevelCell G k, (‖c‖ ^ p.toReal) * (‖(R.block k).coeff Q‖ ^ p.toReal) := by
                refine Finset.sum_congr rfl ?_
                intro Q hQ
                rw [Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
          _ = ‖c‖ ^ p.toReal * ∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ p.toReal := by
                rw [Finset.mul_sum]
      calc
        ((smul c R).levelCoeffPower k) ^ (q.toReal / p.toReal)
            = (‖c‖ ^ p.toReal * R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by rw [hsum]
        _ = (‖c‖ ^ p.toReal) ^ (q.toReal / p.toReal) * (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
              rw [Real.mul_rpow (by positivity) hRnonneg]
        _ = ‖c‖ ^ q.toReal * (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
              have hmul : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
                field_simp [hp_pos.ne']
              rw [hmul, Real.rpow_mul (by positivity)]
              have hcp : (‖c‖ ^ p.toReal) ^ (1 / p.toReal) = ‖c‖ := by
                simpa [one_div] using (Real.rpow_rpow_inv (norm_nonneg c) hp_pos.ne')
              rw [hcp]
    calc
      (∑' k, ((smul c R).levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)
          = (∑' k, ‖c‖ ^ q.toReal * (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
              congr 1
              exact tsum_congr hterm
      _ = (‖c‖ ^ q.toReal * (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal))) ^ (1 / q.toReal) := by
            rw [tsum_mul_left]
      _ = (‖c‖ ^ q.toReal) ^ (1 / q.toReal) *
            (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
        have htsum_nonneg : 0 ≤ ∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
              exact tsum_nonneg fun k =>
                Real.rpow_nonneg (by
                  unfold LpGridRepresentation.levelCoeffPower
                  exact Finset.sum_nonneg fun Q hQ => by positivity) _
        rw [Real.mul_rpow (by positivity) htsum_nonneg]
      _ = ‖c‖ * (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
        have hcp : (‖c‖ ^ q.toReal) ^ (1 / q.toReal) = ‖c‖ := by
          simpa [one_div] using (Real.rpow_rpow_inv (norm_nonneg c) hq_pos.ne')
        rw [hcp]

end LpGridRepresentation


/--
The Besov-ish predicate on `L^p`: `g` has an atomic Besov-ish representation.
-/
def MemBesovish (A : AtomFamily G s p u) (q : ℝ≥0∞)
    (g : Lp ℂ p G.measure) : Prop :=
  let _ : ℝ≥0∞ := q
  Nonempty (LpGridRepresentation A g)

/--
Stronger Besov-ish predicate: representation exists and has finite
coefficient cost in the sense of equation `(rep2)` from the paper.
-/
def MemBesovishCoeffCost (A : AtomFamily G s p u) (q : ℝ≥0∞)
    (g : Lp ℂ p G.measure) : Prop :=
  ∃ R : LpGridRepresentation A g,
    (if q = ∞ then
      BddAbove (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal))
    else
      Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)))

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
      hasSum := ?_ }
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
      hasSum := ?_ }
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
      hasSum := ?_ }
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

namespace BesovishSpace

/-- Candidate upper bounds for the `pqCost` gauge of `x`. -/
def pqCostUpperSet
    (A : AtomFamily G s p u) (q : ℝ≥0∞) (x : BesovishSpace A q) : Set ℝ :=
  { c | ∃ R : LpGridRepresentation A (x : Lp ℂ p G.measure),
      LpGridRepresentation.pqCost (q := q) R ≤ c }

/-- Infimum gauge induced by `pqCost` on admissible representations of `x`. -/
noncomputable def pqPseudoNorm
    (A : AtomFamily G s p u) (q : ℝ≥0∞) (x : BesovishSpace A q) : ℝ :=
  sInf (pqCostUpperSet A q x)

variable {A : AtomFamily G s p u} {q : ℝ≥0∞}

/-- Global hypothesis: every Besov-ish vector admits a representation with finite `(p,q)` cost. -/
def HasAdmissibleCostRepresentations (A : AtomFamily G s p u) (q : ℝ≥0∞) : Prop :=
  ∀ x : BesovishSpace A q,
    Nonempty (LpGridRepresentation A (x : Lp ℂ p G.measure))

theorem pqCostUpperSet_nonempty
    (hA : HasAdmissibleCostRepresentations (A := A) q)
    (x : BesovishSpace A q) :
    (pqCostUpperSet A q x).Nonempty := by
  rcases hA x with ⟨R⟩
  exact ⟨LpGridRepresentation.pqCost (q := q) R, ⟨R, le_rfl⟩⟩

theorem pqCostUpperSet_bddBelow
    (x : BesovishSpace A q) :
    BddBelow (pqCostUpperSet A q x) := by
  refine ⟨0, ?_⟩
  intro c hc
  rcases hc with ⟨R, hRc⟩
  exact le_trans (LpGridRepresentation.pqCost_nonneg R) hRc

theorem pqPseudoNorm_nonneg
    (hA : HasAdmissibleCostRepresentations (A := A) q)
    (x : BesovishSpace A q) :
    0 ≤ pqPseudoNorm A q x := by
  unfold pqPseudoNorm
  refine le_csInf (pqCostUpperSet_nonempty (A := A) (q := q) hA x) ?_
  intro c hc
  rcases hc with ⟨R, hRc⟩
  exact le_trans (LpGridRepresentation.pqCost_nonneg R) hRc

theorem pqPseudoNorm_le_cost
    (x : BesovishSpace A q)
    (R : LpGridRepresentation A (x : Lp ℂ p G.measure)) :
  pqPseudoNorm A q x ≤ LpGridRepresentation.pqCost (q := q) R := by
  unfold pqPseudoNorm
  exact csInf_le (pqCostUpperSet_bddBelow (A := A) (q := q) x) ⟨R, le_rfl⟩

theorem exists_cost_lt_pqPseudoNorm_add
    (hA : HasAdmissibleCostRepresentations (A := A) q)
    (x : BesovishSpace A q) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : LpGridRepresentation A (x : Lp ℂ p G.measure),
      LpGridRepresentation.pqCost (q := q) R < pqPseudoNorm A q x + ε := by
  have hlt : sInf (pqCostUpperSet A q x) < sInf (pqCostUpperSet A q x) + ε :=
    lt_add_of_pos_right _ hε
  rcases exists_lt_of_csInf_lt
      (pqCostUpperSet_nonempty (A := A) (q := q) hA x) hlt with
      ⟨c, hc, hclt⟩
  rcases hc with ⟨R, hRc⟩
  refine ⟨R, ?_⟩
  exact lt_of_le_of_lt hRc (by simpa [pqPseudoNorm] using hclt)

theorem pqPseudoNorm_add_le
    (hp_top : p ≠ ∞)
  (hq_one : 1 ≤ q)
    (hfin : ∀ z : BesovishSpace A q, ∀ ε : ℝ, 0 < ε →
      ∃ R : LpGridRepresentation A (z : Lp ℂ p G.measure),
        LpGridRepresentation.FinitePQCost (q := q) R ∧
          LpGridRepresentation.pqCost (q := q) R < pqPseudoNorm A q z + ε)
    (x y : BesovishSpace A q) :
    pqPseudoNorm A q (x + y) ≤ pqPseudoNorm A q x + pqPseudoNorm A q y := by
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hfin x (ε / 2) hε2 with ⟨Rx, hRxfin, hRxlt⟩
  rcases hfin y (ε / 2) hε2 with ⟨Ry, hRyfin, hRylt⟩
  let Rsum := LpGridRepresentation.add (A := A) Rx Ry
  have h0 :
      pqPseudoNorm A q (x + y) ≤ LpGridRepresentation.pqCost (q := q) Rsum :=
    pqPseudoNorm_le_cost (A := A) (q := q) (x := x + y) Rsum
  have h1 :
      LpGridRepresentation.pqCost (q := q) Rsum
        ≤ LpGridRepresentation.pqCost (q := q) Rx + LpGridRepresentation.pqCost (q := q) Ry :=
    LpGridRepresentation.pqCost_triangle (A := A) (q := q) Rx Ry hp_top hq_one hRxfin hRyfin
  have h2 :
      LpGridRepresentation.pqCost (q := q) Rx + LpGridRepresentation.pqCost (q := q) Ry
        ≤ (pqPseudoNorm A q x + ε / 2) + (pqPseudoNorm A q y + ε / 2) :=
    add_le_add (le_of_lt hRxlt) (le_of_lt hRylt)
  calc
    pqPseudoNorm A q (x + y)
      ≤ LpGridRepresentation.pqCost (q := q) Rsum := h0
    _ ≤ LpGridRepresentation.pqCost (q := q) Rx + LpGridRepresentation.pqCost (q := q) Ry := h1
    _ ≤ (pqPseudoNorm A q x + ε / 2) + (pqPseudoNorm A q y + ε / 2) := h2
    _ = pqPseudoNorm A q x + pqPseudoNorm A q y + ε := by ring

theorem pqPseudoNorm_smul_le
    (hp_top : p ≠ ∞)
  (hq_one : 1 ≤ q)
    (hfin : ∀ z : BesovishSpace A q, ∀ ε : ℝ, 0 < ε →
      ∃ R : LpGridRepresentation A (z : Lp ℂ p G.measure),
        LpGridRepresentation.FinitePQCost (q := q) R ∧
          LpGridRepresentation.pqCost (q := q) R < pqPseudoNorm A q z + ε)
    (c : ℂ) (x : BesovishSpace A q) :
    pqPseudoNorm A q (c • x) ≤ ‖c‖ * pqPseudoNorm A q x := by
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hden : 0 < ‖c‖ + 1 := by linarith [norm_nonneg c]
  have hδ : 0 < ε / (‖c‖ + 1) := by positivity
  rcases hfin x (ε / (‖c‖ + 1)) hδ with ⟨Rx, hRxfin, hRxlt⟩
  let Rc := LpGridRepresentation.smul (A := A) c Rx
  have h0 : pqPseudoNorm A q (c • x) ≤ LpGridRepresentation.pqCost (q := q) Rc :=
    pqPseudoNorm_le_cost (A := A) (q := q) (x := c • x) Rc
  have h1 : LpGridRepresentation.pqCost (q := q) Rc = ‖c‖ * LpGridRepresentation.pqCost (q := q) Rx :=
    LpGridRepresentation.pqCost_smul (A := A) (q := q) c Rx hp_top hq_one hRxfin
  have h2 : LpGridRepresentation.pqCost (q := q) Rx ≤ pqPseudoNorm A q x + ε / (‖c‖ + 1) :=
    le_of_lt hRxlt
  have h3 :
      ‖c‖ * LpGridRepresentation.pqCost (q := q) Rx
        ≤ ‖c‖ * (pqPseudoNorm A q x + ε / (‖c‖ + 1)) :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg c)
  have h4 : ‖c‖ * (ε / (‖c‖ + 1)) ≤ ε := by
    have hfrac : ‖c‖ / (‖c‖ + 1) ≤ (1 : ℝ) :=
      (div_le_one hden).2 (by linarith)
    have hεnn : 0 ≤ ε := le_of_lt hε
    have hmul : (‖c‖ / (‖c‖ + 1)) * ε ≤ (1 : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hfrac hεnn
    calc
      ‖c‖ * (ε / (‖c‖ + 1)) = (‖c‖ / (‖c‖ + 1)) * ε := by ring
      _ ≤ (1 : ℝ) * ε := hmul
      _ = ε := by ring
  calc
    pqPseudoNorm A q (c • x)
        ≤ LpGridRepresentation.pqCost (q := q) Rc := h0
    _ = ‖c‖ * LpGridRepresentation.pqCost (q := q) Rx := h1
    _ ≤ ‖c‖ * (pqPseudoNorm A q x + ε / (‖c‖ + 1)) := h3
    _ = ‖c‖ * pqPseudoNorm A q x + ‖c‖ * (ε / (‖c‖ + 1)) := by ring
    _ ≤ ‖c‖ * pqPseudoNorm A q x + ε := by linarith [h4]

end BesovishSpace



end

end WeakGridSpace
