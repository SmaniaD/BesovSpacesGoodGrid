import BesovSpacesGoodGrid.WeakGridAtomsDefinition
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.MeanInequalitiesPow

/-!
Besov-ish spaces associated to a weak grid and a family of atoms.

The paper defines a Besov-ish element as a function in L^p
that has a representaion as a sum of level
blocks converge  in `L^p` and with finite pq-cost.  A level block is explicitly indexed by
the cells of the level-`k` partition: for each cell there is one coefficient
and one atom.  This matches the paper's finite inner sum
`∑_{Q ∈ P^k} s_Q a_Q`. We also define a norm of the Besovish space,
 that is the infimum of the pq-costs of all representations.
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

/-- The zero level block represents the zero element of `L^p`. -/
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

/-- Evaluating a scaled level block in `L^p` agrees with scalar multiplication. -/
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

/-- The zero element belongs to the set of level-`k` atomic blocks. -/
theorem zero_mem_LevelBlockSet (A : AtomFamily G s p u) (k : ℕ) :
    (0 : Lp ℂ p G.measure) ∈ LevelBlockSet A k :=
  ⟨LevelBlock.zero A k, by simp⟩

/-- Level block sets are closed under scalar multiplication. -/
theorem smul_mem_LevelBlockSet (A : AtomFamily G s p u) (k : ℕ)
  (c : ℂ) {x : Lp ℂ p G.measure} (hx : x ∈ LevelBlockSet A k) :
  c • x ∈ LevelBlockSet A k := by
  -- Unpack a witness block for `x`, then scale its coefficients.
  rcases hx with ⟨B, rfl⟩
  exact ⟨LevelBlock.smul A c B, by simp⟩

omit [Fact (1 ≤ p)] in
/-- The zero vector is an atom on every weak grid cell. -/
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
/-- Atoms are stable under scalar multiplication by complex scalars of norm at most one. -/
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
/-- Normalize a coefficient to a phase and apply it to an atom, using zero at coefficient zero. -/
noncomputable def phaseAtom (A : AtomFamily G s p u) (Q : WeakGridCell G)
    (c : ℂ) (φ : (A.localSpace Q).carrier) : (A.localSpace Q).carrier :=
  if c = 0 then 0 else ((‖c‖ : ℂ)⁻¹ * c) • φ

omit [Fact (1 ≤ p)] in
/-- The phase-normalized atom remains in the atom set. -/
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
/-- Multiplying the phase-normalized atom by the coefficient norm recovers the original scalar multiple. -/
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
/-- A convex combination with total coefficient norm at most one is again an atom. -/
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
/--
Repackage a sum of two coefficient-times-atom terms as one nonnegative
coefficient times a single atom on the same cell.
-/
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
/-- The atom chosen for the sum block has the expected cellwise scalar identity. -/
theorem add_atom_spec (A : AtomFamily G s p u) {k : ℕ}
    (B C : LevelBlock A k) (Q : LevelCell G k) :
    ((‖B.coeff Q‖ + ‖C.coeff Q‖ : ℝ) : ℂ) • (add A B C).atom Q =
      B.coeff Q • B.atom Q + C.coeff Q • C.atom Q :=
  (Classical.choose_spec
    (atom_add_repackage A (levelCellToWeakGridCell G k Q)
      (B.coeff Q) (C.coeff Q) (B.atom_mem Q) (C.atom_mem Q))).2

omit [Fact (1 ≤ p)] in
/-- The `L^p` cell term of a sum block is the sum of the two original cell terms. -/
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
/-- Evaluating the sum block in `L^p` gives the sum of the represented blocks. -/
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
/-- The chosen level block evaluates to the element it was chosen to represent. -/
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
Finite `ℓ^p`-to-`ℓ^t` monotonicity for nonnegative real families.

This elementary inequality is used to pass from coefficient `p`-powers to
coefficient `t`-powers on one finite level.
-/
theorem finset_sum_rpow_le_sum_rpow_of_le
    {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    {p t : ℝ} (hp_pos : 0 < p) (hpt : p ≤ t)
    (ha_nonneg : ∀ i ∈ S, 0 ≤ a i) :
    (∑ i ∈ S, a i ^ t) ≤ (∑ i ∈ S, a i ^ p) ^ (t / p) := by
  classical
  have hr : 1 ≤ t / p := by
    rw [le_div_iff₀ hp_pos]
    simpa using hpt
  revert ha_nonneg
  refine Finset.induction_on S ?base ?step
  · intro ha_nonneg
    simp only [Finset.sum_empty]
    exact Real.rpow_nonneg (le_refl 0) _
  · intro x S hx ih ha_nonneg
    have hS_nonneg : ∀ i ∈ S, 0 ≤ a i := by
      intro i hi
      exact ha_nonneg i (Finset.mem_insert_of_mem hi)
    have hx_nonneg : 0 ≤ a x := ha_nonneg x (Finset.mem_insert_self x S)
    have hsum_p_nonneg : 0 ≤ ∑ i ∈ S, a i ^ p :=
      Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hS_nonneg i hi) _
    have hpow_step :
        (∑ i ∈ S, a i ^ p) ^ (t / p) + (a x ^ p) ^ (t / p)
          ≤ ((∑ i ∈ S, a i ^ p) + a x ^ p) ^ (t / p) :=
      Real.add_rpow_le_rpow_add hsum_p_nonneg (Real.rpow_nonneg hx_nonneg _) hr
    have hx_pow : (a x ^ p) ^ (t / p) = a x ^ t := by
      rw [← Real.rpow_mul hx_nonneg]
      field_simp [hp_pos.ne']
    calc
      ∑ i ∈ insert x S, a i ^ t
          = (∑ i ∈ S, a i ^ t) + a x ^ t := by
            rw [Finset.sum_insert hx]
            abel
      _ ≤ (∑ i ∈ S, a i ^ p) ^ (t / p) + a x ^ t :=
            add_le_add (ih hS_nonneg) le_rfl
      _ = (∑ i ∈ S, a i ^ p) ^ (t / p) + (a x ^ p) ^ (t / p) := by
            rw [hx_pow]
      _ ≤ ((∑ i ∈ S, a i ^ p) + a x ^ p) ^ (t / p) := hpow_step
      _ = (∑ i ∈ insert x S, a i ^ p) ^ (t / p) := by
            rw [Finset.sum_insert hx]
            abel_nf

/--
Level-`k` coefficient `ℓ^p` power sum: `∑_{Q ∈ P^k} |s_Q|^p`.

This is the inner quantity from the paper's coefficient-cost formula.
-/
def levelCoeffPower
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g) (k : ℕ) : ℝ :=
  ∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ p.toReal

/-- The level coefficient power is nonnegative. -/
theorem levelCoeffPower_nonneg
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g) (k : ℕ) :
    0 ≤ R.levelCoeffPower k := by
  unfold levelCoeffPower
  exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _

/--
Finite coefficient monotonicity: since `p ≤ t`, the finite `ℓ^t` coefficient
power is controlled by the `ℓ^p` coefficient power.

This is the coefficient step used after the overlap estimate in the paper.
-/
theorem levelCoeffPower_t_le_levelCoeffPower_rpow
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    {t : ℝ≥0∞} (R : LpGridRepresentation A g) (k : ℕ)
    (hp_ne_top : p ≠ ∞) (ht_ne_top : t ≠ ∞) (hp_le_t : p ≤ t) :
    (∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ t.toReal)
      ≤ (R.levelCoeffPower k) ^ (t.toReal / p.toReal) := by
  have hp_ne_zero : p ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ p))
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hp_le_t_real : p.toReal ≤ t.toReal := ENNReal.toReal_mono ht_ne_top hp_le_t
  simpa [levelCoeffPower] using
    finset_sum_rpow_le_sum_rpow_of_le
      (S := (Finset.univ : Finset (LevelCell G k)))
      (a := fun Q => ‖(R.block k).coeff Q‖)
      hp_pos hp_le_t_real
      (fun Q _ => norm_nonneg ((R.block k).coeff Q))

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

/-- The level measure weight is nonnegative. -/
theorem levelMeasureWeight_nonneg
    (G : WeakGridSpace (α := α)) (s : ℝ) (p t : ℝ≥0∞) (k : ℕ) :
    0 ≤ levelMeasureWeight G s p t k := by
  unfold levelMeasureWeight
  have hbase :
      0 ≤ sSup (Set.range fun Q : LevelCell G k => (G.measure Q.1).toReal) := by
    classical
    by_cases hne : Nonempty (LevelCell G k)
    · obtain ⟨Q⟩ := hne
      exact le_trans ENNReal.toReal_nonneg
        (le_csSup (Finite.bddAbove_range fun Q : LevelCell G k => (G.measure Q.1).toReal)
          ⟨Q, rfl⟩)
    · have hempty :
          Set.range (fun Q : LevelCell G k => (G.measure Q.1).toReal) = ∅ := by
        ext x
        constructor
        · rintro ⟨Q, rfl⟩
          exact False.elim (hne ⟨Q⟩)
        · intro hx
          cases hx
      simp [hempty]
  exact Real.rpow_nonneg hbase _

/-- Each cell's measure factor is bounded by the level measure weight. -/
theorem levelCellMeasure_rpow_le_levelMeasureWeight
    (G : WeakGridSpace (α := α)) (s : ℝ) (p t : ℝ≥0∞) (k : ℕ)
    (hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / t.toReal)
    (Q : LevelCell G k) :
    (G.measure Q.1).toReal ^ (s - 1 / p.toReal + 1 / t.toReal)
      ≤ levelMeasureWeight G s p t k := by
  unfold levelMeasureWeight
  exact Real.rpow_le_rpow ENNReal.toReal_nonneg
    (le_csSup (Finite.bddAbove_range fun Q : LevelCell G k => (G.measure Q.1).toReal)
      ⟨Q, rfl⟩)
    hs_nonneg

/--
Weighted level coefficient estimate after replacing each cell weight by the
level weight and using finite `ℓ^p`-to-`ℓ^t` monotonicity.
-/
theorem weighted_levelCoeffPower_t_le
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    {t : ℝ≥0∞} (R : LpGridRepresentation A g) (k : ℕ)
    (hp_ne_top : p ≠ ∞) (ht_ne_top : t ≠ ∞) (hp_le_t : p ≤ t)
    (hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / t.toReal) :
    (∑ Q : LevelCell G k,
        ((G.measure Q.1).toReal ^ (s - 1 / p.toReal + 1 / t.toReal) *
          ‖(R.block k).coeff Q‖) ^ t.toReal)
      ≤ (levelMeasureWeight G s p t k *
          (R.levelCoeffPower k) ^ (1 / p.toReal)) ^ t.toReal := by
  have hp_ne_zero : p ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ p))
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have ht_ne_zero : t ≠ 0 := by
    exact ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le
      ((Fact.out : 1 ≤ p).trans hp_le_t))
  have ht_pos : 0 < t.toReal := ENNReal.toReal_pos ht_ne_zero ht_ne_top
  let W := levelMeasureWeight G s p t k
  have hW_nonneg : 0 ≤ W := levelMeasureWeight_nonneg G s p t k
  have hL_nonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
  have hterm_le :
      ∀ Q : LevelCell G k,
        ((G.measure Q.1).toReal ^ (s - 1 / p.toReal + 1 / t.toReal) *
            ‖(R.block k).coeff Q‖) ^ t.toReal
          ≤ (W * ‖(R.block k).coeff Q‖) ^ t.toReal := by
    intro Q
    have hcell_nonneg :
        0 ≤ (G.measure Q.1).toReal ^ (s - 1 / p.toReal + 1 / t.toReal) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hmul_nonneg :
        0 ≤ (G.measure Q.1).toReal ^ (s - 1 / p.toReal + 1 / t.toReal) *
            ‖(R.block k).coeff Q‖ :=
      mul_nonneg hcell_nonneg (norm_nonneg _)
    have hbase_le :
        (G.measure Q.1).toReal ^ (s - 1 / p.toReal + 1 / t.toReal) *
            ‖(R.block k).coeff Q‖
          ≤ W * ‖(R.block k).coeff Q‖ :=
      mul_le_mul_of_nonneg_right
        (levelCellMeasure_rpow_le_levelMeasureWeight G s p t k hs_nonneg Q)
        (norm_nonneg _)
    exact Real.rpow_le_rpow hmul_nonneg hbase_le ht_pos.le
  have hcoeff :
      (∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ t.toReal)
        ≤ (R.levelCoeffPower k) ^ (t.toReal / p.toReal) :=
    levelCoeffPower_t_le_levelCoeffPower_rpow
      (A := A) (t := t) R k hp_ne_top ht_ne_top hp_le_t
  calc
    (∑ Q : LevelCell G k,
        ((G.measure Q.1).toReal ^ (s - 1 / p.toReal + 1 / t.toReal) *
          ‖(R.block k).coeff Q‖) ^ t.toReal)
        ≤ ∑ Q : LevelCell G k, (W * ‖(R.block k).coeff Q‖) ^ t.toReal :=
          Finset.sum_le_sum fun Q _ => hterm_le Q
    _ = W ^ t.toReal *
          (∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ t.toReal) := by
          simp_rw [Real.mul_rpow hW_nonneg (norm_nonneg _)]
          rw [Finset.mul_sum]
    _ ≤ W ^ t.toReal * (R.levelCoeffPower k) ^ (t.toReal / p.toReal) :=
          mul_le_mul_of_nonneg_left hcoeff (Real.rpow_nonneg hW_nonneg _)
    _ = (W * (R.levelCoeffPower k) ^ (1 / p.toReal)) ^ t.toReal := by
          rw [Real.mul_rpow hW_nonneg (Real.rpow_nonneg hL_nonneg _)]
          congr 1
          rw [← Real.rpow_mul hL_nonneg]
          congr 1
          field_simp [hp_pos.ne']

/--
Algebraic exponent identity coming from the Hölder conjugacy of `u` and
`uConj`.
-/
theorem holderConjugate_atom_exponent_identity
    {u uConj : ℝ≥0∞} (hu : ENNReal.HolderConjugate u uConj)
    (hp_ne_top : p ≠ ∞) :
    (uConj.toReal * p.toReal)⁻¹ + (p * u).toReal⁻¹ = p.toReal⁻¹ := by
  have hp_ne_zero : p ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ p))
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hholder : u⁻¹ + uConj⁻¹ = 1 := ENNReal.holderConjugate_iff.mp hu
  have huinv_ne_top : u⁻¹ ≠ ∞ := by
    intro htop
    have hbad : u⁻¹ + uConj⁻¹ = ∞ := by simp [htop]
    rw [hholder] at hbad
    exact ENNReal.one_ne_top hbad
  have huConjinv_ne_top : uConj⁻¹ ≠ ∞ := by
    intro htop
    have hbad : u⁻¹ + uConj⁻¹ = ∞ := by simp [htop]
    rw [hholder] at hbad
    exact ENNReal.one_ne_top hbad
  have hreal :
      u.toReal⁻¹ + uConj.toReal⁻¹ = 1 := by
    have h := congrArg ENNReal.toReal hholder
    rw [ENNReal.toReal_add huinv_ne_top huConjinv_ne_top] at h
    simpa using h
  calc
    (uConj.toReal * p.toReal)⁻¹ + (p * u).toReal⁻¹
        = uConj.toReal⁻¹ * p.toReal⁻¹ + p.toReal⁻¹ * u.toReal⁻¹ := by
          rw [ENNReal.toReal_mul]
          field_simp [mul_inv_rev]
    _ = p.toReal⁻¹ * (u.toReal⁻¹ + uConj.toReal⁻¹) := by ring
    _ = p.toReal⁻¹ := by rw [hreal, mul_one]

/--
Combining the atom measure exponent with the finite-measure embedding exponent
gives the level embedding exponent.
-/
theorem atomMeasureExponent_add_embeddingExponent
    {u uConj t : ℝ≥0∞} (hu : ENNReal.HolderConjugate u uConj)
    (hp_ne_top : p ≠ ∞) :
    atomMeasureExponent s p uConj + (1 / t.toReal - 1 / (p * u).toReal)
      = s - 1 / p.toReal + 1 / t.toReal := by
  have hholder :=
    holderConjugate_atom_exponent_identity (p := p) (u := u) (uConj := uConj)
      hu hp_ne_top
  unfold atomMeasureExponent
  simp only [one_div]
  linarith

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

/-- The block of a sum representation evaluates levelwise to the sum of blocks. -/
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

/-- The block of a scaled representation evaluates levelwise to the scaled block. -/
@[simp]
theorem smul_block_toLp
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (c : ℂ) (R : LpGridRepresentation A g) (k : ℕ) :
    ((smul c R).block k).toLp A = c • (R.block k).toLp A := by
  simp [smul]

/-- The absolute-convergence cost is nonnegative. -/
theorem lpCost_nonneg
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g) :
    0 ≤ LpGridRepresentation.lpCost R := by
  simpa [LpGridRepresentation.lpCost] using
    (tsum_nonneg fun k => norm_nonneg ((R.block k).toLp A))

/-- The `lpCost` of the sum of two summable representations satisfies the triangle inequality. -/
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

/-- The `lpCost` of a scaled summable representation scales by the scalar norm. -/
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


/-- The `(p,q)` coefficient gauge of a representation. -/
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

/--
The paper's `C_co(t,q,b)` coefficient-cost function for `t ≥ 1`, `q ≥ 1`.

Given exponents `t` and `q`, and a coefficient sequence `b : ℕ → ℝ`:
- If `q = 1`: `C_co(t,1,b) = sup_k b_k^{1/t}`
- If `q > 1`: `C_co(t,q,b) = (∑_k b_k^{q'/t})^{1/q'}` where `q' = q/(q-1)` is the Hölder conjugate.

This measures the coefficient cost used in the `L^t` embedding theorem.
-/
noncomputable def cCoefficient (t q : ℝ≥0∞) (b : ℕ → ℝ) : ℝ :=
  if q = 1 then
    -- Supremum case for q = 1
    sSup (Set.range fun k => b k ^ (1 / t.toReal))
  else if q = ∞ then
    -- `q = ∞` gives the `ℓ¹` weight appearing in the paper.
    ∑' k, b k ^ (1 / t.toReal)
  else
    -- General case for q > 1, using conjugate exponent q' = q / (q - 1)
    let q' := q / (q - 1)
    (∑' k, b k ^ (q'.toReal / t.toReal)) ^ (1 / q'.toReal)

/-- Finiteness side-condition for the coefficient cost `C_co(t,q,b)`. -/
def cCoefficientFinite (t q : ℝ≥0∞) (b : ℕ → ℝ) : Prop :=
  if q = 1 then
    BddAbove (Set.range fun k => b k ^ (1 / t.toReal))
  else if q = ∞ then
    Summable (fun k => b k ^ (1 / t.toReal))
  else
    let q' := q / (q - 1)
    Summable (fun k => b k ^ (q'.toReal / t.toReal))

/-- The coefficient-cost function is nonnegative for nonnegative input data. -/
theorem cCoefficient_nonneg (t q : ℝ≥0∞) (b : ℕ → ℝ)
    (hb_nonneg : ∀ k, 0 ≤ b k) :
    0 ≤ cCoefficient t q b := by
  unfold cCoefficient
  split_ifs with hq1 hqtop
  · refine Real.sSup_nonneg ?_
    intro x hx
    rcases hx with ⟨k, rfl⟩
    exact Real.rpow_nonneg (hb_nonneg k) _
  · exact tsum_nonneg fun k => Real.rpow_nonneg (hb_nonneg k) _
  · exact Real.rpow_nonneg (tsum_nonneg fun k => Real.rpow_nonneg (hb_nonneg k) _) _

end LpGridRepresentation

/-- The `L^t` term attached to one cell in a level block. -/
noncomputable def LevelBlock.termLt
    (A : AtomFamily G s p u) {t : ℝ≥0∞} [Fact (1 ≤ t)] {k : ℕ}
    (ht_le_pu : t ≤ p * u)
    (B : LevelBlock A k) (Q : LevelCell G k) : Lp ℂ t G.measure :=
  B.coeff Q • MemLp.toLp
    (A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q))
    (by
      -- Since atoms are in `L^(p*u)` and `t ≤ p*u`, they are in `L^t`
      -- on the finite ambient measure space.
      have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
        dsimp [WeakGridSpace.measure]
        exact G.grid.isFinite
      letI := hfinite
      exact (A.local_memLp (levelCellToWeakGridCell G k Q) (B.atom Q)).mono_exponent ht_le_pu)

/--
The canonical realization of a level block as an element of `L^t`.

This is the same finite atomic sum as `LevelBlock.toLp`, but viewed in the
target exponent `t`.
-/
noncomputable def LevelBlock.toLt
    (A : AtomFamily G s p u) {t : ℝ≥0∞} [Fact (1 ≤ t)] {k : ℕ}
    (ht_le_pu : t ≤ p * u)
    (B : LevelBlock A k) : Lp ℂ t G.measure :=
  (G.grid.partitions k).attach.sum fun Q => LevelBlock.termLt A ht_le_pu B Q

/-- The pointwise function represented by a level block in the target exponent. -/
noncomputable def LevelBlock.toFunLt
    (A : AtomFamily G s p u) {k : ℕ} (B : LevelBlock A k) : α → ℂ :=
  fun x => (G.grid.partitions k).attach.sum fun Q =>
    B.coeff Q * A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x

omit [Fact (1 ≤ p)] in
/-- The pointwise target-exponent realization of a level block belongs to `L^t`. -/
theorem LevelBlock.toFunLt_memLp
    (A : AtomFamily G s p u) {t : ℝ≥0∞} [Fact (1 ≤ t)] {k : ℕ}
    (ht_le_pu : t ≤ p * u)
    (B : LevelBlock A k) :
    MeasureTheory.MemLp (B.toFunLt A) t G.measure := by
  classical
  unfold LevelBlock.toFunLt
  refine MeasureTheory.memLp_finsetSum (G.grid.partitions k).attach ?_
  intro Q hQ
  have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
    dsimp [WeakGridSpace.measure]
    exact G.grid.isFinite
  letI := hfinite
  exact ((A.local_memLp (levelCellToWeakGridCell G k Q) (B.atom Q)).mono_exponent
    ht_le_pu).const_smul (B.coeff Q)

omit [Fact (1 ≤ p)] in
/-- The coefficient function of a single `L^p` cell term is the expected scalar atom. -/
theorem LevelBlock.coeFn_term
    (A : AtomFamily G s p u) {k : ℕ}
    (B : LevelBlock A k) (Q : LevelCell G k) :
    (B.term A Q : α → ℂ) =ᵐ[G.measure]
      fun x => B.coeff Q *
        A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x := by
  unfold LevelBlock.term
  exact (Lp.coeFn_smul (B.coeff Q)
    (MemLp.toLp
      (A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q))
      (A.local_memLp_p (levelCellToWeakGridCell G k Q) (B.atom Q)))).trans
    ((MemLp.coeFn_toLp
      (A.local_memLp_p (levelCellToWeakGridCell G k Q) (B.atom Q))).fun_const_smul
        (B.coeff Q))

omit [Fact (1 ≤ p)] in
/-- The `L^p` representative of a level block agrees a.e. with its pointwise finite sum. -/
theorem LevelBlock.coeFn_toLp
    (A : AtomFamily G s p u) {k : ℕ}
    (B : LevelBlock A k) :
    (B.toLp A : α → ℂ) =ᵐ[G.measure] B.toFunLt A := by
  classical
  unfold LevelBlock.toLp LevelBlock.toFunLt
  induction (G.grid.partitions k).attach using Finset.induction_on with
  | empty =>
      exact Lp.coeFn_zero ℂ p G.measure
  | insert Q S hQS ih =>
      simp only [Finset.sum_insert hQS]
      exact (Lp.coeFn_add _ _).trans <|
        (LevelBlock.coeFn_term A B Q).add ih

omit [Fact (1 ≤ p)] in
/-- The coefficient function of a single `L^t` cell term is the expected scalar atom. -/
theorem LevelBlock.coeFn_termLt
    (A : AtomFamily G s p u) {t : ℝ≥0∞} [Fact (1 ≤ t)] {k : ℕ}
    (ht_le_pu : t ≤ p * u)
    (B : LevelBlock A k) (Q : LevelCell G k) :
    (LevelBlock.termLt A ht_le_pu B Q : α → ℂ) =ᵐ[G.measure]
      fun x => B.coeff Q *
        A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x := by
  have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
    dsimp [WeakGridSpace.measure]
    exact G.grid.isFinite
  letI := hfinite
  unfold LevelBlock.termLt
  exact (Lp.coeFn_smul (B.coeff Q)
    (MemLp.toLp
      (A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q))
      (by
        have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
          dsimp [WeakGridSpace.measure]
          exact G.grid.isFinite
        letI := hfinite
        exact (A.local_memLp (levelCellToWeakGridCell G k Q) (B.atom Q)).mono_exponent
          ht_le_pu))).trans
    ((MemLp.coeFn_toLp
      ((A.local_memLp (levelCellToWeakGridCell G k Q) (B.atom Q)).mono_exponent
        ht_le_pu)).fun_const_smul (B.coeff Q))

omit [Fact (1 ≤ p)] in
/-- The `L^t` representative of a level block agrees a.e. with its pointwise finite sum. -/
theorem LevelBlock.coeFn_toLt
    (A : AtomFamily G s p u) {t : ℝ≥0∞} [Fact (1 ≤ t)] {k : ℕ}
    (ht_le_pu : t ≤ p * u)
    (B : LevelBlock A k) :
    (B.toLt A ht_le_pu : α → ℂ) =ᵐ[G.measure] B.toFunLt A := by
  classical
  unfold LevelBlock.toLt LevelBlock.toFunLt
  induction (G.grid.partitions k).attach using Finset.induction_on with
  | empty =>
      exact Lp.coeFn_zero ℂ t G.measure
  | insert Q S hQS ih =>
      simp only [Finset.sum_insert hQS]
      exact (Lp.coeFn_add _ _).trans <|
        (LevelBlock.coeFn_termLt A ht_le_pu B Q).add ih

omit [Fact (1 ≤ p)] in
/-- At each point, at most `Cmult1` cells of a level contribute nontrivially. -/
theorem LevelBlock.active_card_le_Cmult1
    (A : AtomFamily G s p u) {k : ℕ}
    (B : LevelBlock A k) (x : α) :
    ((G.grid.partitions k).attach.filter fun Q =>
      B.coeff Q * A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x ≠ 0).card
        ≤ G.grid.Cmult1 := by
  classical
  let S := (G.grid.partitions k).attach.filter fun Q =>
    B.coeff Q * A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x ≠ 0
  by_cases hS : S.Nonempty
  · rcases hS with ⟨Q₀, hQ₀S⟩
    have hQ₀mem : Q₀.1 ∈ G.grid.partitions k := Q₀.2
    have hxQ₀ : x ∈ Q₀.1 := by
      have hprod : B.coeff Q₀ *
          A.toFunction (levelCellToWeakGridCell G k Q₀) (B.atom Q₀) x ≠ 0 := by
        simpa [S] using (Finset.mem_filter.mp hQ₀S).2
      by_contra hxnot
      have hzero :
          A.toFunction (levelCellToWeakGridCell G k Q₀) (B.atom Q₀) x = 0 := by
        simpa using A.local_support (levelCellToWeakGridCell G k Q₀) (B.atom Q₀) x hxnot
      exact hprod (by simp [hzero])
    have hmap :
        Set.MapsTo (fun Q : LevelCell G k => Q.1) (S : Set (LevelCell G k))
          (overlapFinset (G.grid.partitions k) Q₀.1 : Set (Set α)) := by
      intro Q hQS
      have hprod : B.coeff Q *
          A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x ≠ 0 := by
        simpa [S] using (Finset.mem_filter.mp hQS).2
      have hxQ : x ∈ Q.1 := by
        by_contra hxnot
        have hzero :
            A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x = 0 := by
          simpa using A.local_support (levelCellToWeakGridCell G k Q) (B.atom Q) x hxnot
        exact hprod (by simp [hzero])
      simp [overlapFinset, Q.2, Set.Nonempty]
      exact ⟨x, hxQ, hxQ₀⟩
    have hinj :
        Set.InjOn (fun Q : LevelCell G k => Q.1) (S : Set (LevelCell G k)) := by
      intro Q hQS R hRS hQR
      cases Q
      cases R
      simp at hQR
      simp [hQR]
    exact (Finset.card_le_card_of_injOn (fun Q : LevelCell G k => Q.1) hmap hinj).trans
      (G.grid.overlap_card_le k Q₀.1 hQ₀mem)
  · have hEmpty : S = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hS
    have hcard :
        ((G.grid.partitions k).attach.filter fun Q =>
          B.coeff Q * A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x ≠ 0).card = 0 := by
      simpa [S] using congrArg Finset.card hEmpty
    omega

omit [Fact (1 ≤ p)] in
/--
Pointwise overlap estimate for a level block, bounding the norm of the finite
sum by `Cmult1` times the sum of powered cell contributions.
-/
theorem LevelBlock.norm_toFunLt_rpow_le_Cmult1
    (A : AtomFamily G s p u) {t : ℝ≥0∞} [Fact (1 ≤ t)] {k : ℕ}
    (ht_ne_top : t ≠ ∞)
    (B : LevelBlock A k) (x : α) :
    ‖B.toFunLt A x‖ ^ t.toReal ≤
      (G.grid.Cmult1 : ℝ) ^ t.toReal *
        ∑ Q : LevelCell G k,
          ‖B.coeff Q *
            A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x‖ ^ t.toReal := by
  classical
  let S := (G.grid.partitions k).attach.filter fun Q =>
    B.coeff Q * A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x ≠ 0
  let term : LevelCell G k → ℂ := fun Q =>
    B.coeff Q * A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x
  have ht_one : (1 : ℝ) ≤ t.toReal := by
    have h := ENNReal.toReal_mono ht_ne_top (Fact.out : (1 : ℝ≥0∞) ≤ t)
    simpa using h
  have ht_nonneg : 0 ≤ t.toReal := le_trans (zero_le_one : (0 : ℝ) ≤ 1) ht_one
  have hsum_eq : (G.grid.partitions k).attach.sum term = S.sum term := by
    simpa [S, term] using (Finset.sum_filter_ne_zero (s := (G.grid.partitions k).attach)
      (f := term)).symm
  have hnorm_sum :
      ‖B.toFunLt A x‖ ≤ ∑ Q ∈ S, ‖term Q‖ := by
    calc
      ‖B.toFunLt A x‖
          = ‖(G.grid.partitions k).attach.sum term‖ := by
              simp [LevelBlock.toFunLt, term]
      _ = ‖S.sum term‖ := by rw [hsum_eq]
      _ ≤ ∑ Q ∈ S, ‖term Q‖ := norm_sum_le S term
  have hpow_sum :
      (∑ Q ∈ S, ‖term Q‖) ^ t.toReal ≤
        (S.card : ℝ) ^ (t.toReal - 1) *
          ∑ Q ∈ S, ‖term Q‖ ^ t.toReal :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S ht_one
      (fun Q _ => norm_nonneg (term Q))
  have hcardC_nat : S.card ≤ G.grid.Cmult1 := by
    simpa [S, term] using LevelBlock.active_card_le_Cmult1 A B x
  have hcardC : (S.card : ℝ) ≤ (G.grid.Cmult1 : ℝ) := by exact_mod_cast hcardC_nat
  have hsum_nonneg : 0 ≤ ∑ Q ∈ S, ‖term Q‖ := by
    exact Finset.sum_nonneg fun Q _ => norm_nonneg (term Q)
  have hleft :
      ‖B.toFunLt A x‖ ^ t.toReal ≤ (∑ Q ∈ S, ‖term Q‖) ^ t.toReal :=
    Real.rpow_le_rpow (norm_nonneg _) hnorm_sum ht_nonneg
  have hSsum_le :
      ∑ Q ∈ S, ‖term Q‖ ^ t.toReal ≤
        ∑ Q : LevelCell G k, ‖term Q‖ ^ t.toReal := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro Q hQ; exact (Finset.mem_filter.mp hQ).1)
      (by intro Q hQ _; exact Real.rpow_nonneg (norm_nonneg (term Q)) _)
  have hCnonneg : 0 ≤ (G.grid.Cmult1 : ℝ) := by exact_mod_cast Nat.zero_le G.grid.Cmult1
  by_cases hSempty : S.card = 0
  · have hS : S = ∅ := Finset.card_eq_zero.mp hSempty
    have hzero : ∑ Q ∈ S, ‖term Q‖ = 0 := by simp [hS]
    have hnorm_zero : ‖B.toFunLt A x‖ = 0 := by
      exact le_antisymm (by simpa [hzero] using hnorm_sum) (norm_nonneg _)
    rw [hnorm_zero, Real.zero_rpow (lt_of_lt_of_le zero_lt_one ht_one).ne']
    exact mul_nonneg (Real.rpow_nonneg hCnonneg _)
      (Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _)
  · have hSpos_nat : 1 ≤ S.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hSempty)
    have hSpos : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hSpos_nat
    have hcard_pow_le_C :
        (S.card : ℝ) ^ (t.toReal - 1) ≤ (G.grid.Cmult1 : ℝ) ^ t.toReal := by
      calc
        (S.card : ℝ) ^ (t.toReal - 1)
            ≤ (S.card : ℝ) ^ t.toReal :=
              Real.rpow_le_rpow_of_exponent_le hSpos (by linarith)
        _ ≤ (G.grid.Cmult1 : ℝ) ^ t.toReal :=
              Real.rpow_le_rpow (by positivity) hcardC ht_nonneg
    calc
      ‖B.toFunLt A x‖ ^ t.toReal
          ≤ (∑ Q ∈ S, ‖term Q‖) ^ t.toReal := hleft
      _ ≤ (S.card : ℝ) ^ (t.toReal - 1) *
            ∑ Q ∈ S, ‖term Q‖ ^ t.toReal := hpow_sum
      _ ≤ (G.grid.Cmult1 : ℝ) ^ t.toReal *
            ∑ Q : LevelCell G k, ‖term Q‖ ^ t.toReal :=
          mul_le_mul hcard_pow_le_C hSsum_le
            (Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg (term Q)) _)
            (Real.rpow_nonneg hCnonneg _)
      _ = (G.grid.Cmult1 : ℝ) ^ t.toReal *
            ∑ Q : LevelCell G k,
              ‖B.coeff Q *
                A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x‖ ^ t.toReal := by
          simp [term]

namespace LpGridRepresentation

/--
Single-atom `L^t` estimate used in the level embedding.

This is the formal target corresponding to the first Hölder computation:
`‖a_P‖_t ≤ |P|^(s - 1/p + 1/t)`.
-/
theorem lt_norm_atom_le_levelMeasureWeight
    {A : AtomFamily G s p u} {t : ℝ≥0∞}
    [Fact (1 ≤ t)] {k : ℕ} (Q : LevelCell G k)
    (hp_ne_top : p ≠ ∞) (ht_ne_top : t ≠ ∞)
    (_hp_le_t : p ≤ t) (ht_le_pu : t ≤ p * u)
    (hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / t.toReal)
    (φ : (A.localSpace (levelCellToWeakGridCell G k Q)).carrier)
    (hφ : A.IsAtom (levelCellToWeakGridCell G k Q) φ) :
    ‖MemLp.toLp
        (A.toFunction (levelCellToWeakGridCell G k Q) φ)
        (by
          have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
            dsimp [WeakGridSpace.measure]
            exact G.grid.isFinite
          letI := hfinite
          exact (A.local_memLp (levelCellToWeakGridCell G k Q) φ).mono_exponent ht_le_pu)‖
      ≤ levelMeasureWeight G s p t k := by
  let Qg : WeakGridCell G := levelCellToWeakGridCell G k Q
  let f : α → ℂ := A.toFunction Qg φ
  have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
    dsimp [WeakGridSpace.measure]
    exact G.grid.isFinite
  letI := hfinite
  have ht_ne_zero : t ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ t))
  have ht_pos : 0 < t.toReal := ENNReal.toReal_pos ht_ne_zero ht_ne_top
  have hQ_meas : MeasurableSet Q.1 := G.grid.measurable k Q.1 Q.2
  have hQ_pos : 0 < G.measure Q.1 := by
    simpa [WeakGridSpace.measure] using G.grid.positive_measure k Q.1 Q.2
  have hQ_ne_zero : G.measure Q.1 ≠ 0 := ne_of_gt hQ_pos
  have hQ_ne_top : G.measure Q.1 ≠ ∞ := by finiteness
  have hsupport : Function.support f ⊆ Q.1 := by
    intro x hx
    by_contra hxQ
    exact hx (by simpa [f, Qg] using A.local_support Qg φ x hxQ)
  have hrestr_t :
      MeasureTheory.eLpNorm f t (G.measure.restrict Q.1) =
        MeasureTheory.eLpNorm f t G.measure :=
    MeasureTheory.eLpNorm_restrict_eq_of_support_subset (μ := G.measure) hsupport
  have hcompare :
      MeasureTheory.eLpNorm f t G.measure ≤
        MeasureTheory.eLpNorm f (p * u) G.measure *
          (G.measure Q.1) ^ (1 / t.toReal - 1 / (p * u).toReal) := by
    calc
      MeasureTheory.eLpNorm f t G.measure
          = MeasureTheory.eLpNorm f t (G.measure.restrict Q.1) := hrestr_t.symm
      _ ≤ MeasureTheory.eLpNorm f (p * u) (G.measure.restrict Q.1) *
            (G.measure.restrict Q.1 Set.univ) ^
              (1 / t.toReal - 1 / (p * u).toReal) :=
          MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
            (μ := G.measure.restrict Q.1) ht_le_pu
            ((A.local_memLp Qg φ).aestronglyMeasurable.mono_measure
              Measure.restrict_le_self)
      _ = MeasureTheory.eLpNorm f (p * u) (G.measure.restrict Q.1) *
            (G.measure Q.1) ^ (1 / t.toReal - 1 / (p * u).toReal) := by
          rw [Measure.restrict_apply_univ]
      _ ≤ MeasureTheory.eLpNorm f (p * u) G.measure *
            (G.measure Q.1) ^ (1 / t.toReal - 1 / (p * u).toReal) := by
          exact mul_le_mul_right'
            (MeasureTheory.eLpNorm_mono_measure f Measure.restrict_le_self)
            _
  have hatom :
      MeasureTheory.eLpNorm f (p * u) G.measure ≤
        (G.measure Q.1) ^ atomMeasureExponent s p A.uConj := by
    simpa [f, Qg, atomMeasureScale] using A.atom_norm_bound hφ
  have hpow :
      (G.measure Q.1) ^ atomMeasureExponent s p A.uConj *
          (G.measure Q.1) ^ (1 / t.toReal - 1 / (p * u).toReal)
        =
        (G.measure Q.1) ^ (s - 1 / p.toReal + 1 / t.toReal) := by
    rw [← ENNReal.rpow_add _ _ hQ_ne_zero hQ_ne_top]
    congr 1
    simpa [sub_eq_add_neg, one_div] using
      atomMeasureExponent_add_embeddingExponent
        (p := p) (s := s) (u := u) (uConj := A.uConj) (t := t)
        A.holder_conjugate hp_ne_top
  have h_enn :
      MeasureTheory.eLpNorm f t G.measure ≤
        (G.measure Q.1) ^ (s - 1 / p.toReal + 1 / t.toReal) := by
    calc
      MeasureTheory.eLpNorm f t G.measure
          ≤ MeasureTheory.eLpNorm f (p * u) G.measure *
              (G.measure Q.1) ^ (1 / t.toReal - 1 / (p * u).toReal) := hcompare
      _ ≤ (G.measure Q.1) ^ atomMeasureExponent s p A.uConj *
              (G.measure Q.1) ^ (1 / t.toReal - 1 / (p * u).toReal) :=
          mul_le_mul_right' hatom _
      _ = (G.measure Q.1) ^ (s - 1 / p.toReal + 1 / t.toReal) := hpow
  have hreal :
      (MeasureTheory.eLpNorm f t G.measure).toReal ≤
        (G.measure Q.1).toReal ^ (s - 1 / p.toReal + 1 / t.toReal) := by
    rw [ENNReal.toReal_rpow]
    exact ENNReal.toReal_mono
      (ENNReal.rpow_ne_top_of_ne_zero hQ_ne_zero hQ_ne_top) h_enn
  calc
    ‖MemLp.toLp
        (A.toFunction (levelCellToWeakGridCell G k Q) φ)
        (by
          have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
            dsimp [WeakGridSpace.measure]
            exact G.grid.isFinite
          letI := hfinite
          exact (A.local_memLp (levelCellToWeakGridCell G k Q) φ).mono_exponent ht_le_pu)‖
        = (MeasureTheory.eLpNorm f t G.measure).toReal := by
          simp [f, Qg]
    _ ≤ (G.measure Q.1).toReal ^ (s - 1 / p.toReal + 1 / t.toReal) := hreal
    _ ≤ levelMeasureWeight G s p t k :=
          levelCellMeasure_rpow_le_levelMeasureWeight G s p t k hs_nonneg Q

/--
Level-block `L^t` estimate after the single-atom estimate.

This is the formal target corresponding to the overlap computation with
`Ω_Q^k` and `G.grid.Cmult1`.
-/
theorem lt_norm_levelBlock_le_of_atom_bound
    {A : AtomFamily G s p u} {t : ℝ≥0∞}
    [Fact (1 ≤ t)]
    (hp_ne_top : p ≠ ∞) (ht_ne_top : t ≠ ∞)
    (hp_le_t : p ≤ t) (ht_le_pu : t ≤ p * u)
    (hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / t.toReal)
    : ∀ {g : Lp ℂ p G.measure} (R : LpGridRepresentation A g) (k : ℕ),
        ‖(R.block k).toLt (t := t) A ht_le_pu‖ ≤
          ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / t.toReal)) *
            levelMeasureWeight G s p t k *
              (R.levelCoeffPower k) ^ (1 / p.toReal) := by
  /-
  Paper proof:
    1. support of each atom reduces the integral on `Q` to
       `P ∈ overlapFinset (G.grid.partitions k) Q`;
    2. finite triangle / convexity gives the `Cmult1` factor;
    3. `G.grid.overlap_card_le` changes the double sum into a single sum;
    4. because `p ≤ t`, the finite `ℓ^t` norm of coefficients is bounded by
       their finite `ℓ^p` norm.

  This keeps the constant from the paper, namely `Cmult1^(1+1/t)`.
  -/
  intro g R k
  classical
  let B := R.block k
  let C : ℝ := G.grid.Cmult1
  let W : ℝ := levelMeasureWeight G s p t k
  have hp_ne_zero : p ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ p))
  have ht_ne_zero : t ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le
      ((Fact.out : 1 ≤ p).trans hp_le_t))
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have ht_pos : 0 < t.toReal := ENNReal.toReal_pos ht_ne_zero ht_ne_top
  have ht_nonneg : 0 ≤ t.toReal := ht_pos.le
  have hW_nonneg : 0 ≤ W := levelMeasureWeight_nonneg G s p t k
  have hL_nonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
  have htarget_nonneg :
      0 ≤ C ^ (1 + 1 / t.toReal) * W *
          (R.levelCoeffPower k) ^ (1 / p.toReal) := by
    positivity
  have hcoeff_int :
      (∑ Q : LevelCell G k,
          (W * ‖B.coeff Q‖) ^ t.toReal)
        ≤ (W * (R.levelCoeffPower k) ^ (1 / p.toReal)) ^ t.toReal := by
    have hcoeff :
        (∑ Q : LevelCell G k, ‖B.coeff Q‖ ^ t.toReal)
          ≤ (R.levelCoeffPower k) ^ (t.toReal / p.toReal) := by
      simpa [B] using
        levelCoeffPower_t_le_levelCoeffPower_rpow
          (A := A) (t := t) R k hp_ne_top ht_ne_top hp_le_t
    calc
      (∑ Q : LevelCell G k, (W * ‖B.coeff Q‖) ^ t.toReal)
          = W ^ t.toReal *
              ∑ Q : LevelCell G k, ‖B.coeff Q‖ ^ t.toReal := by
            simp_rw [Real.mul_rpow hW_nonneg (norm_nonneg _)]
            rw [Finset.mul_sum]
      _ ≤ W ^ t.toReal * (R.levelCoeffPower k) ^ (t.toReal / p.toReal) :=
            mul_le_mul_of_nonneg_left hcoeff (Real.rpow_nonneg hW_nonneg _)
      _ = (W * (R.levelCoeffPower k) ^ (1 / p.toReal)) ^ t.toReal := by
            rw [Real.mul_rpow hW_nonneg (Real.rpow_nonneg hL_nonneg _)]
            congr 1
            rw [← Real.rpow_mul hL_nonneg]
            congr 1
            field_simp [hp_pos.ne']
  have hterm_eLp :
      ∀ Q : LevelCell G k,
        MeasureTheory.eLpNorm
            (fun x => B.coeff Q *
              A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x)
            t G.measure
          ≤ ENNReal.ofReal
              (W * ‖B.coeff Q‖) := by
    intro Q
    let f : α → ℂ := A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q)
    have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
      dsimp [WeakGridSpace.measure]
      exact G.grid.isFinite
    letI := hfinite
    have hmem : MeasureTheory.MemLp f t G.measure :=
      (A.local_memLp (levelCellToWeakGridCell G k Q) (B.atom Q)).mono_exponent ht_le_pu
    have hcell_bound :
        MeasureTheory.eLpNorm f t G.measure ≤
          ENNReal.ofReal W := by
      have hnorm :
          ‖MeasureTheory.MemLp.toLp f hmem‖ ≤ W := by
        simpa [f, W] using
          lt_norm_atom_le_levelMeasureWeight
            (A := A) (t := t) Q hp_ne_top ht_ne_top hp_le_t ht_le_pu
            hs_nonneg (B.atom Q) (B.atom_mem Q)
      rw [MeasureTheory.Lp.norm_toLp] at hnorm
      exact (ENNReal.le_ofReal_iff_toReal_le hmem.eLpNorm_ne_top hW_nonneg).2 hnorm
    calc
      MeasureTheory.eLpNorm
          (fun x => B.coeff Q *
            A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x)
          t G.measure
          = MeasureTheory.eLpNorm (B.coeff Q • f) t G.measure := by
              rfl
      _ = ‖B.coeff Q‖ₑ * MeasureTheory.eLpNorm f t G.measure := by
              rw [MeasureTheory.eLpNorm_const_smul]
      _ ≤ ‖B.coeff Q‖ₑ *
            ENNReal.ofReal W :=
              mul_le_mul_left' hcell_bound _
      _ = ENNReal.ofReal (W * ‖B.coeff Q‖) := by
              rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg (B.coeff Q))]
              ring_nf
  have heLp_bound :
      MeasureTheory.eLpNorm (B.toFunLt A) t G.measure ≤
        ENNReal.ofReal
          (C ^ (1 + 1 / t.toReal) * W *
            (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal ht_ne_zero ht_ne_top]
    have hCpow_ne_top : ENNReal.ofReal (C ^ t.toReal) ≠ ∞ := by simp
    have hpoint :
        ∀ x,
          ‖B.toFunLt A x‖ₑ ^ t.toReal ≤
            ENNReal.ofReal (C ^ t.toReal) *
              ∑ Q : LevelCell G k,
                ‖B.coeff Q *
                  A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x‖ₑ ^
                  t.toReal := by
      intro x
      have hreal := LevelBlock.norm_toFunLt_rpow_le_Cmult1
        (A := A) (t := t) ht_ne_top B x
      have hrhs_nonneg :
          0 ≤ C ^ t.toReal *
            ∑ Q : LevelCell G k,
              ‖B.coeff Q *
                A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x‖ ^
                t.toReal := by
        positivity
      have h := (ENNReal.ofReal_le_ofReal_iff hrhs_nonneg).2 (by simpa [C] using hreal)
      have hleft :
          ENNReal.ofReal (‖B.toFunLt A x‖ ^ t.toReal)
            = ‖B.toFunLt A x‖ₑ ^ t.toReal := by
        rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ht_nonneg]
        simp
      have hsum :
          ENNReal.ofReal
            (∑ Q ∈ (G.grid.partitions k).attach,
              (‖B.coeff Q‖ *
                ‖A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x‖) ^
                  t.toReal)
            =
            ∑ Q ∈ (G.grid.partitions k).attach,
              ‖B.coeff Q *
                A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x‖ₑ ^
                t.toReal := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · apply Finset.sum_congr rfl
          intro Q _
          rw [← ENNReal.ofReal_rpow_of_nonneg
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ht_nonneg]
          simp
        · intro Q _
          exact Real.rpow_nonneg
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
      rw [hleft] at h
      simpa [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : 0 ≤ C) _),
        hsum, ENNReal.ofReal_rpow_of_nonneg, norm_mul, ht_nonneg] using h
    calc
      (∫⁻ x, ‖B.toFunLt A x‖ₑ ^ t.toReal ∂G.measure) ^ (1 / t.toReal)
          ≤ (∫⁻ x, ENNReal.ofReal (C ^ t.toReal) *
              ∑ Q : LevelCell G k,
                ‖B.coeff Q *
                  A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x‖ₑ ^
                    t.toReal ∂G.measure) ^ (1 / t.toReal) :=
            ENNReal.rpow_le_rpow (lintegral_mono hpoint) (by positivity)
      _ = (ENNReal.ofReal (C ^ t.toReal) *
              ∑ Q : LevelCell G k,
                ∫⁻ x,
                  ‖B.coeff Q *
                    A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x‖ₑ ^
          t.toReal ∂G.measure) ^ (1 / t.toReal) := by
            congr 1
            rw [MeasureTheory.lintegral_const_mul'
              (ENNReal.ofReal (C ^ t.toReal))
              (fun x =>
                ∑ Q : LevelCell G k,
                  ‖B.coeff Q *
                    A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x‖ₑ ^
                    t.toReal)
              hCpow_ne_top]
            rw [MeasureTheory.lintegral_finsetSum' (Finset.univ : Finset (LevelCell G k))]
            intro Q _
            have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
              dsimp [WeakGridSpace.measure]
              exact G.grid.isFinite
            letI := hfinite
            have hmem :
                MeasureTheory.MemLp
                  (fun x => B.coeff Q *
                    A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x)
                  t G.measure := by
              simpa [Pi.smul_apply] using
                ((A.local_memLp (levelCellToWeakGridCell G k Q) (B.atom Q)).mono_exponent
                  ht_le_pu).const_smul (B.coeff Q)
            simpa [enorm_mul] using hmem.aestronglyMeasurable.enorm.pow_const t.toReal
      _ ≤ (ENNReal.ofReal (C ^ t.toReal) *
              ∑ Q : LevelCell G k,
                (ENNReal.ofReal
                  (W * ‖B.coeff Q‖)) ^
                    t.toReal) ^ (1 / t.toReal) := by
            refine ENNReal.rpow_le_rpow (mul_le_mul_left' ?_ _) (by positivity)
            refine Finset.sum_le_sum fun Q _ => ?_
            have hQ := hterm_eLp Q
            have hInt :
                ∫⁻ x,
                  ‖B.coeff Q *
                    A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x‖ₑ ^
                    t.toReal ∂G.measure =
                MeasureTheory.eLpNorm
                  (fun x => B.coeff Q *
                    A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x)
                  t G.measure ^ t.toReal := by
              rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
                ht_ne_zero ht_ne_top
                (f := fun x => B.coeff Q *
                  A.toFunction (levelCellToWeakGridCell G k Q) (B.atom Q) x)
                (μ := G.measure)]
              rw [one_div, ENNReal.rpow_inv_rpow ht_pos.ne']
            rw [hInt]
            exact ENNReal.rpow_le_rpow hQ ht_nonneg
      _ ≤ (ENNReal.ofReal (C ^ t.toReal) *
              ENNReal.ofReal
                ((W * (R.levelCoeffPower k) ^ (1 / p.toReal)) ^ t.toReal)) ^
              (1 / t.toReal) := by
            refine ENNReal.rpow_le_rpow (mul_le_mul_left' ?_ _) (by positivity)
            have hsum_ofReal :
                (∑ Q : LevelCell G k,
                  (ENNReal.ofReal
                    (W * ‖B.coeff Q‖)) ^
                      t.toReal)
                  =
                  ENNReal.ofReal
                    (∑ Q : LevelCell G k,
                      ((W * ‖B.coeff Q‖) ^
                        t.toReal)) := by
              rw [ENNReal.ofReal_sum_of_nonneg]
              · apply Finset.sum_congr rfl
                intro Q _
                rw [← ENNReal.ofReal_rpow_of_nonneg
                  (mul_nonneg hW_nonneg (norm_nonneg _)) ht_nonneg]
              · intro Q _
                exact Real.rpow_nonneg (mul_nonneg hW_nonneg (norm_nonneg _)) _
            rw [hsum_ofReal]
            exact (ENNReal.ofReal_le_ofReal_iff
              (Real.rpow_nonneg (mul_nonneg hW_nonneg
                (Real.rpow_nonneg hL_nonneg _)) _)).2 (by simpa [B, W] using hcoeff_int)
      _ ≤ ENNReal.ofReal
            (C ^ (1 + 1 / t.toReal) * W *
              (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
            let D : ℝ := W * (R.levelCoeffPower k) ^ (1 / p.toReal)
            have hC_nonneg : 0 ≤ C := by
              dsimp [C]
              exact_mod_cast Nat.zero_le G.grid.Cmult1
            have hD_nonneg : 0 ≤ D := by
              dsimp [D]
              exact mul_nonneg hW_nonneg (Real.rpow_nonneg hL_nonneg _)
            have hroot_eq :
                (ENNReal.ofReal (C ^ t.toReal) *
                    ENNReal.ofReal (D ^ t.toReal)) ^ (1 / t.toReal)
                  = ENNReal.ofReal (C * D) := by
              rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hC_nonneg _)]
              rw [← Real.mul_rpow hC_nonneg hD_nonneg]
              rw [← ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC_nonneg hD_nonneg)
                ht_nonneg]
              rw [one_div, ← ENNReal.rpow_mul, mul_inv_cancel₀ ht_pos.ne',
                ENNReal.rpow_one]
            rw [show W * (R.levelCoeffPower k) ^ (1 / p.toReal) = D by rfl]
            rw [hroot_eq]
            have hC_le :
                C ≤ C ^ (1 + 1 / t.toReal) := by
              by_cases hCzero : C = 0
              · rw [hCzero]
                exact Real.rpow_nonneg le_rfl _
              · have hCnat_ne : G.grid.Cmult1 ≠ 0 := by
                  intro hnat
                  apply hCzero
                  dsimp [C]
                  exact_mod_cast hnat
                have hC_one : (1 : ℝ) ≤ C := by
                  dsimp [C]
                  exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hCnat_ne)
                have hexp : (1 : ℝ) ≤ 1 + 1 / t.toReal := by
                  linarith [one_div_pos.mpr ht_pos]
                simpa using Real.rpow_le_rpow_of_exponent_le hC_one hexp
            have hreal :
                C * D ≤ C ^ (1 + 1 / t.toReal) * W *
                    (R.levelCoeffPower k) ^ (1 / p.toReal) := by
              dsimp [D]
              calc
                C * (W * R.levelCoeffPower k ^ (1 / p.toReal))
                    ≤ C ^ (1 + 1 / t.toReal) *
                        (W * R.levelCoeffPower k ^ (1 / p.toReal)) :=
                      mul_le_mul_of_nonneg_right hC_le
                        (mul_nonneg hW_nonneg (Real.rpow_nonneg hL_nonneg _))
                _ = C ^ (1 + 1 / t.toReal) * W *
                        R.levelCoeffPower k ^ (1 / p.toReal) := by
                      ring
            exact (ENNReal.ofReal_le_ofReal_iff htarget_nonneg).2 hreal
  have hcoe :
      ((B.toLt (t := t) A ht_le_pu : Lp ℂ t G.measure) : α → ℂ)
        =ᵐ[G.measure] B.toFunLt A :=
    LevelBlock.coeFn_toLt A ht_le_pu B
  have hnorm_toReal :
      ‖B.toLt (t := t) A ht_le_pu‖
        ≤ (ENNReal.ofReal
          (C ^ (1 + 1 / t.toReal) * W *
            (R.levelCoeffPower k) ^ (1 / p.toReal))).toReal := by
    rw [Lp.norm_def]
    rw [MeasureTheory.eLpNorm_congr_ae hcoe]
    exact ENNReal.toReal_mono (by simp) heLp_bound
  rw [ENNReal.toReal_ofReal htarget_nonneg] at hnorm_toReal
  simpa [B, C, W] using hnorm_toReal

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
    : ∃ C : ℝ, 0 ≤ C ∧
      ∀ {g : Lp ℂ p G.measure} (R : LpGridRepresentation A g) (k : ℕ),
        ‖(R.block k).toLt (t := t) A ht_le_pu‖ ≤
          C * levelMeasureWeight G s p t k *
            (R.levelCoeffPower k) ^ (1 / p.toReal) := by
  refine ⟨(G.grid.Cmult1 : ℝ) ^ (1 + 1 / t.toReal), by positivity, ?_⟩
  intro g R k
  exact lt_norm_levelBlock_le_of_atom_bound
    (A := A) (t := t) hp_ne_top ht_ne_top hp_le_t ht_le_pu hs_nonneg R k

/--
The real exponent `q / (q - 1)` is Hölder conjugate to `q` when `1 < q < ∞`.
-/
lemma holderConjugate_q_div_qsub1_toReal (hq_one : 1 < q.toReal) (hq_ne_top : q ≠ ∞) :
    (q / (q - 1)).toReal.HolderConjugate q.toReal := by
  have hq_gt : (1 : ℝ≥0∞) < q := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_iff_lt_toReal zero_le_one hq_ne_top).2 hq_one
  have hqdiv : (q / (q - 1)).toReal = q.toReal / (q.toReal - 1) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le hq_gt.le hq_ne_top,
      ENNReal.toReal_one]
  have hreal : (q.toReal / (q.toReal - 1)).HolderConjugate q.toReal := by
    have hq : 0 < q.toReal := by linarith
    have hqsub : q.toReal - 1 ≠ 0 := by linarith
    have hqsubpos : 0 < q.toReal - 1 := by linarith
    rw [Real.holderConjugate_iff]
    constructor
    · rw [lt_div_iff₀ hqsubpos]
      linarith
    · field_simp [hq.ne', hqsub]
      ring
  simpa [hqdiv] using hreal

/--
Hölder estimate for the weighted coefficient sum when `q` is finite.

The `q = 1` branch is treated as an `ℓ¹`-`ℓ^∞` estimate; the remaining
finite cases use the conjugate exponent `q / (q - 1)`.
-/
theorem weighted_sum_le_cCoefficient_mul_pqCost
    {A : AtomFamily G s p u} {t : ℝ≥0∞}
    [Fact (1 ≤ t)]
    (ht_ne_top : t ≠ ∞)
    (hq_one : 1 ≤ q) (hq_ne_top : q ≠ ∞)
    {g : Lp ℂ p G.measure} (R : LpGridRepresentation A g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R)
    (hCco_fin : cCoefficientFinite t q (fun k =>
      (levelMeasureWeight G s p t k) ^ t.toReal)) :
    (∑' k, levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal)) ≤
      cCoefficient t q (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
        LpGridRepresentation.pqCost (q := q) R := by
  let w : ℕ → ℝ := fun k => levelMeasureWeight G s p t k
  let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
  have ht_pos : 0 < t.toReal := (ENNReal.toReal_pos_iff_ne_top t).2 ht_ne_top
  by_cases hq1 : q = 1
  · have hC_bdd : BddAbove (Set.range fun k => ((w k) ^ t.toReal) ^ (1 / t.toReal)) := by
      simpa [cCoefficientFinite, hq1] using hCco_fin
    let C : ℝ := cCoefficient t q (fun k => (w k) ^ t.toReal)
    have hC_def : C = sSup (Set.range fun k => ((w k) ^ t.toReal) ^ (1 / t.toReal)) := by
      simp [C, cCoefficient, hq1]
    have hw_le_C : ∀ k, w k ≤ C := by
      intro k
      have hk_nonneg : 0 ≤ w k := by
        dsimp [w]
        exact levelMeasureWeight_nonneg G s p t k
      have hk_pow : ((w k) ^ t.toReal) ^ (1 / t.toReal) = w k := by
        simpa [one_div] using (Real.rpow_rpow_inv hk_nonneg ht_pos.ne')
      have hC_bdd' : BddAbove (Set.range fun k => ((w k) ^ t.toReal) ^ t.toReal⁻¹) := by
        simpa [one_div] using hC_bdd
      have hk_pow' : ((w k) ^ t.toReal) ^ t.toReal⁻¹ = w k := by
        simpa [one_div] using hk_pow
      have hk_le : ((w k) ^ t.toReal) ^ t.toReal⁻¹ ≤
          sSup (Set.range fun k => ((w k) ^ t.toReal) ^ t.toReal⁻¹) :=
        le_csSup hC_bdd' ⟨k, rfl⟩
      simpa [hC_def] using hk_pow' ▸ hk_le
    have hRsum : Summable a := by
      simpa [LpGridRepresentation.FinitePQCost, hq1, a] using hRfin
    have hprod_le :
        (fun k => w k * a k) ≤ (fun k => C * a k) := by
      intro k
      have ha_nonneg : 0 ≤ a k := by
        dsimp [a]
        exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
      exact mul_le_mul_of_nonneg_right (hw_le_C k) ha_nonneg
    have hprod_sum : Summable (fun k => w k * a k) :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg
          (by dsimp [w]; exact levelMeasureWeight_nonneg G s p t k)
          (by dsimp [a]; exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
        hprod_le
        (hRsum.mul_left C)
    have htsum_le :
        (∑' k, w k * a k) ≤ (∑' k, C * a k) :=
      hprod_sum.tsum_le_tsum hprod_le (hRsum.mul_left C)
    have htsum_scaled : (∑' k, C * a k) = C * (∑' k, a k) :=
      (hRsum.hasSum.mul_left C).tsum_eq
    have hpq_q1 : LpGridRepresentation.pqCost (q := q) R = (∑' k, a k) := by
      simp [LpGridRepresentation.pqCost, hq1, a]
    calc
      (∑' k, levelMeasureWeight G s p t k *
          (R.levelCoeffPower k) ^ (1 / p.toReal))
          = ∑' k, w k * a k := by rfl
      _ ≤ (∑' k, C * a k) := htsum_le
      _ = C * (∑' k, a k) := htsum_scaled
      _ = cCoefficient t q (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
            LpGridRepresentation.pqCost (q := q) R := by
          simpa [C, w, hpq_q1]
  · let q' : ℝ≥0∞ := q / (q - 1)
    have hq_toReal_le : (1 : ℝ) ≤ q.toReal := by
      have h := ENNReal.toReal_mono hq_ne_top hq_one
      simpa using h
    have hq_toReal_ne_one : q.toReal ≠ 1 := by
      intro hreal
      apply hq1
      have hqeq : (1 : ℝ≥0∞) = q := by
        exact (ENNReal.toReal_eq_toReal ENNReal.one_ne_top hq_ne_top).mp (by simpa [hreal])
      exact hqeq.symm
    have hq_toReal_one : 1 < q.toReal :=
      lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
    have hCsum : Summable (fun k => ((w k) ^ t.toReal) ^ (q'.toReal / t.toReal)) := by
      simpa [cCoefficientFinite, hq1, hq_ne_top, q'] using hCco_fin
    have hAsum_raw : Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
      simpa [LpGridRepresentation.FinitePQCost, hq_ne_top] using hRfin
    have hwpow : ∀ k, ((w k) ^ t.toReal) ^ (q'.toReal / t.toReal) = (w k) ^ q'.toReal := by
      intro k
      have hw_nonneg : 0 ≤ w k := by
        dsimp [w]
        exact levelMeasureWeight_nonneg G s p t k
      have hdiv : q'.toReal / t.toReal = (1 / t.toReal) * q'.toReal := by
        field_simp [ht_pos.ne']
      calc
        ((w k) ^ t.toReal) ^ (q'.toReal / t.toReal)
            = ((w k) ^ t.toReal) ^ ((1 / t.toReal) * q'.toReal) := by rw [hdiv]
        _ = (((w k) ^ t.toReal) ^ (1 / t.toReal)) ^ q'.toReal := by
              rw [Real.rpow_mul (Real.rpow_nonneg hw_nonneg _)]
        _ = (w k) ^ q'.toReal := by
              congr 1
              simpa [one_div] using (Real.rpow_rpow_inv hw_nonneg ht_pos.ne')
    have hApow : ∀ k, (a k) ^ q.toReal = (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
      intro k
      have hA_nonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
      by_cases hp_zero : p.toReal = 0
      · simp [a, hp_zero]
      · have hp_pos : 0 < p.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hp_zero)
        have hdiv : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
          field_simp [hp_pos.ne']
        calc
          (a k) ^ q.toReal
              = ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ q.toReal := by rfl
          _ = (R.levelCoeffPower k) ^ ((1 / p.toReal) * q.toReal) := by
                rw [← Real.rpow_mul hA_nonneg]
          _ = (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by rw [hdiv]
    have hWsum : Summable (fun k => (w k) ^ q'.toReal) :=
      hCsum.congr hwpow
    have hAsum : Summable (fun k => (a k) ^ q.toReal) :=
      hAsum_raw.congr (fun k => (hApow k).symm)
    have hw_nonneg : ∀ k, 0 ≤ w k := by
      intro k
      dsimp [w]
      exact levelMeasureWeight_nonneg G s p t k
    have ha_nonneg : ∀ k, 0 ≤ a k := by
      intro k
      dsimp [a]
      exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
    have hq_conj : q'.toReal.HolderConjugate q.toReal := by
      simpa [q'] using holderConjugate_q_div_qsub1_toReal
        (q := q) hq_toReal_one hq_ne_top
    have hholder :=
      Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
        (p := q'.toReal) (q := q.toReal)
        hq_conj hw_nonneg ha_nonneg hWsum hAsum
    have hC_rhs :
        (∑' k, (w k) ^ q'.toReal) ^ (1 / q'.toReal)
          = cCoefficient t q (fun k => (w k) ^ t.toReal) := by
      rw [cCoefficient, if_neg hq1, if_neg hq_ne_top]
      dsimp [q']
      congr 1
      exact (tsum_congr fun k => (hwpow k).symm)
    have hA_rhs :
        (∑' k, (a k) ^ q.toReal) ^ (1 / q.toReal)
          = LpGridRepresentation.pqCost (q := q) R := by
      rw [LpGridRepresentation.pqCost, if_neg hq_ne_top]
      congr 1
      exact tsum_congr hApow
    calc
      (∑' k, levelMeasureWeight G s p t k *
          (R.levelCoeffPower k) ^ (1 / p.toReal))
          = ∑' k, w k * a k := by rfl
      _ ≤ (∑' k, (w k) ^ q'.toReal) ^ (1 / q'.toReal) *
              (∑' k, (a k) ^ q.toReal) ^ (1 / q.toReal) := hholder
      _ = cCoefficient t q (fun k => (w k) ^ t.toReal) *
            LpGridRepresentation.pqCost (q := q) R := by
          rw [hC_rhs, hA_rhs]
      _ = cCoefficient t q (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
            LpGridRepresentation.pqCost (q := q) R := by
          rfl

/--
Weighted coefficient estimate for the endpoint `q = ∞`.

Here `pqCost` is a supremum and `cCoefficient` contributes the summable
weight sequence.
-/
theorem weighted_sum_le_cCoefficient_mul_pqCost_top
    {A : AtomFamily G s p u} {t : ℝ≥0∞}
    [Fact (1 ≤ t)]
    (ht_ne_top : t ≠ ∞)
    {g : Lp ℂ p G.measure} (R : LpGridRepresentation A g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := ∞) R)
    (hCco_fin : cCoefficientFinite t ∞ (fun k =>
      (levelMeasureWeight G s p t k) ^ t.toReal)) :
    (∑' k, levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal)) ≤
      cCoefficient t ∞ (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
        LpGridRepresentation.pqCost (q := ∞) R := by
  let w : ℕ → ℝ := fun k => levelMeasureWeight G s p t k
  let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
  have ht_pos : 0 < t.toReal := (ENNReal.toReal_pos_iff_ne_top t).2 ht_ne_top
  have hRbdd : BddAbove (Set.range a) := by
    simpa [LpGridRepresentation.FinitePQCost, a] using hRfin
  let C : ℝ := LpGridRepresentation.pqCost (q := ∞) R
  have hC_def : C = sSup (Set.range a) := by
    simp [C, LpGridRepresentation.pqCost, a]
  have ha_le_C : ∀ k, a k ≤ C := by
    intro k
    simpa [hC_def] using le_csSup hRbdd ⟨k, rfl⟩
  have hWsum_raw : Summable (fun k => ((w k) ^ t.toReal) ^ (1 / t.toReal)) := by
    simpa [cCoefficientFinite] using hCco_fin
  have hwpow : ∀ k, ((w k) ^ t.toReal) ^ (1 / t.toReal) = w k := by
    intro k
    have hw_nonneg : 0 ≤ w k := by
      dsimp [w]
      exact levelMeasureWeight_nonneg G s p t k
    simpa [one_div] using (Real.rpow_rpow_inv hw_nonneg ht_pos.ne')
  have hWsum : Summable w := hWsum_raw.congr hwpow
  have hprod_le :
      (fun k => w k * a k) ≤ (fun k => w k * C) := by
    intro k
    exact mul_le_mul_of_nonneg_left (ha_le_C k)
      (by dsimp [w]; exact levelMeasureWeight_nonneg G s p t k)
  have hprod_sum : Summable (fun k => w k * a k) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg
        (by dsimp [w]; exact levelMeasureWeight_nonneg G s p t k)
        (by dsimp [a]; exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
      hprod_le
      (hWsum.mul_right C)
  have htsum_le :
      (∑' k, w k * a k) ≤ (∑' k, w k * C) :=
    hprod_sum.tsum_le_tsum hprod_le (hWsum.mul_right C)
  have htsum_scaled : (∑' k, w k * C) = (∑' k, w k) * C := by
    simpa [mul_comm] using (hWsum.hasSum.mul_right C).tsum_eq
  have hCco_rhs :
      cCoefficient t ∞ (fun k => (w k) ^ t.toReal) = ∑' k, w k := by
    rw [cCoefficient, if_neg (by simp), if_pos rfl]
    simpa using tsum_congr hwpow
  calc
    (∑' k, levelMeasureWeight G s p t k *
        (R.levelCoeffPower k) ^ (1 / p.toReal))
        = ∑' k, w k * a k := by rfl
    _ ≤ (∑' k, w k * C) := htsum_le
    _ = (∑' k, w k) * C := htsum_scaled
    _ = cCoefficient t ∞ (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
          LpGridRepresentation.pqCost (q := ∞) R := by
        simp [hCco_rhs, C, w]

/-- Uniform wrapper for the weighted coefficient estimate for all `1 ≤ q ≤ ∞`. -/
theorem weighted_sum_le_cCoefficient_mul_pqCost_of_one_le
    {A : AtomFamily G s p u} {t : ℝ≥0∞}
    [Fact (1 ≤ t)]
    (ht_ne_top : t ≠ ∞)
    (hq_one : 1 ≤ q)
    {g : Lp ℂ p G.measure} (R : LpGridRepresentation A g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R)
    (hCco_fin : cCoefficientFinite t q (fun k =>
      (levelMeasureWeight G s p t k) ^ t.toReal)) :
    (∑' k, levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal)) ≤
      cCoefficient t q (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
        LpGridRepresentation.pqCost (q := q) R := by
  by_cases hq_top : q = ∞
  · subst hq_top
    exact weighted_sum_le_cCoefficient_mul_pqCost_top
      (G := G) (s := s) (p := p) (u := u) (A := A) (t := t)
      ht_ne_top R hRfin hCco_fin
  · exact weighted_sum_le_cCoefficient_mul_pqCost
      (G := G) (s := s) (p := p) (u := u) (q := q) (A := A) (t := t)
      ht_ne_top hq_one hq_top R hRfin hCco_fin

/--
Auxiliary summability lemma for the level-block `L^t` norms.

This keeps summability out of the final embedding statement: if the weighted
coefficient sequence is summable, then the series of `L^t` norms of level
blocks is summable.
-/
theorem summable_blockLt_norm_of_summable_weighted_coeff
    {A : AtomFamily G s p u} {t : ℝ≥0∞}
    [Fact (1 ≤ t)]
    (hp_ne_top : p ≠ ∞) (ht_ne_top : t ≠ ∞)
    (hp_le_t : p ≤ t) (ht_le_pu : t ≤ p * u)
    (hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / t.toReal)
    {g : Lp ℂ p G.measure} (R : LpGridRepresentation A g)
    (hWeightedSummable : Summable (fun k =>
      levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal)))
    (hWeightedBound :
      (∑' k, levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal)) ≤
        cCoefficient t q (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
          LpGridRepresentation.pqCost (q := q) R) :
    Summable (fun k => ‖(R.block k).toLt (t := t) A ht_le_pu‖) ∧
      (∑' k, ‖(R.block k).toLt (t := t) A ht_le_pu‖) ≤
        ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / t.toReal)) *
          cCoefficient t q (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
            LpGridRepresentation.pqCost (q := q) R := by
  let C : ℝ := ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / t.toReal))
  have hle :
      (fun k => ‖(R.block k).toLt (t := t) A ht_le_pu‖)
        ≤ (fun k => C * (levelMeasureWeight G s p t k *
            (R.levelCoeffPower k) ^ (1 / p.toReal))) := by
    intro k
    have hk := lt_norm_levelBlock_le_of_atom_bound
      (A := A) (t := t) hp_ne_top ht_ne_top hp_le_t ht_le_pu hs_nonneg R k
    simpa [C, mul_assoc] using hk
  have hScaledSummable : Summable (fun k =>
      C * (levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal))) :=
    hWeightedSummable.mul_left C
  have hSummableLt : Summable (fun k => ‖(R.block k).toLt (t := t) A ht_le_pu‖) :=
    Summable.of_nonneg_of_le
    (fun k => norm_nonneg ((R.block k).toLt (t := t) A ht_le_pu))
    hle hScaledSummable
  have htsum_le :
      (∑' k, ‖(R.block k).toLt (t := t) A ht_le_pu‖)
        ≤ (∑' k, C * (levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal))) :=
    hSummableLt.tsum_le_tsum hle hScaledSummable
  have htsum_scaled :
      (∑' k, C * (levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal)))
        = C * (∑' k, levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
    exact (hWeightedSummable.hasSum.mul_left C).tsum_eq
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound_scaled :
      C * (∑' k, levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal))
        ≤ C *
          (cCoefficient t q (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
            LpGridRepresentation.pqCost (q := q) R) :=
    mul_le_mul_of_nonneg_left hWeightedBound hC_nonneg
  refine ⟨hSummableLt, ?_⟩
  calc
    (∑' k, ‖(R.block k).toLt (t := t) A ht_le_pu‖)
        ≤ (∑' k, C * (levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal))) :=
          htsum_le
    _ = C * (∑' k, levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal)) :=
          htsum_scaled
    _ ≤ C *
          (cCoefficient t q (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
            LpGridRepresentation.pqCost (q := q) R) :=
          hbound_scaled
    _ = ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / t.toReal)) *
          cCoefficient t q (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
            LpGridRepresentation.pqCost (q := q) R := by
          dsimp [C]
          ring

/--
Continuous inclusion `L^t → L^p` on the finite measure space when `p ≤ t`.

This is used to compare the `L^t` reconstruction of an atomic series with its
original `L^p` representation.
-/
noncomputable def lpInclusion
    {t : ℝ≥0∞} [Fact (1 ≤ t)]
    (hp_ne_top : p ≠ ∞) (ht_ne_top : t ≠ ∞) (hp_le_t : p ≤ t) :
    Lp ℂ t G.measure →L[ℂ] Lp ℂ p G.measure := by
  have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
    dsimp [WeakGridSpace.measure]
    exact G.grid.isFinite
  letI := hfinite
  have hp_ne_zero : p ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ p))
  have ht_ne_zero : t ≠ 0 := by
    exact ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le
      ((Fact.out : 1 ≤ p).trans hp_le_t))
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hpt_real : p.toReal ≤ t.toReal := ENNReal.toReal_mono ht_ne_top hp_le_t
  let C : ℝ := (G.measure Set.univ ^ (1 / p.toReal - 1 / t.toReal)).toReal
  refine LinearMap.mkContinuous
    { toFun := fun f => MemLp.toLp f ((Lp.memLp f).mono_exponent hp_le_t)
      map_add' := by
        intro f g
        let hf : MeasureTheory.MemLp f p G.measure := (Lp.memLp f).mono_exponent hp_le_t
        let hg : MeasureTheory.MemLp g p G.measure := (Lp.memLp g).mono_exponent hp_le_t
        let hfg : MeasureTheory.MemLp (f + g) p G.measure :=
          (Lp.memLp (f + g)).mono_exponent hp_le_t
        change hfg.toLp (f + g) = hf.toLp f + hg.toLp g
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_add f g)
      map_smul' := by
        intro c f
        let hf : MeasureTheory.MemLp f p G.measure := (Lp.memLp f).mono_exponent hp_le_t
        let hcf : MeasureTheory.MemLp (c • f) p G.measure :=
          (Lp.memLp (c • f)).mono_exponent hp_le_t
        change hcf.toLp (c • f) = c • hf.toLp f
        rw [← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_smul c f) }
    C ?_
  intro f
  have hexp_nonneg : 0 ≤ 1 / p.toReal - 1 / t.toReal := by
    have hinv : 1 / t.toReal ≤ 1 / p.toReal := one_div_le_one_div_of_le hp_pos hpt_real
    exact sub_nonneg.mpr hinv
  have hpow_ne_top :
      G.measure Set.univ ^ (1 / p.toReal - 1 / t.toReal) ≠ ∞ := by
    exact (ENNReal.rpow_lt_top_of_nonneg hexp_nonneg G.grid.isFinite.measure_univ_lt_top.ne).ne
  have hle :
      MeasureTheory.eLpNorm f p G.measure ≤
        MeasureTheory.eLpNorm f t G.measure *
          G.measure Set.univ ^ (1 / p.toReal - 1 / t.toReal) :=
    MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp_le_t (Lp.aestronglyMeasurable f)
  have hmul_ne_top :
      MeasureTheory.eLpNorm f t G.measure *
        G.measure Set.univ ^ (1 / p.toReal - 1 / t.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hpow_ne_top
  calc
    ‖MemLp.toLp f ((Lp.memLp f).mono_exponent hp_le_t)‖
        = (MeasureTheory.eLpNorm f p G.measure).toReal := by
          rw [Lp.norm_def]
          exact congrArg ENNReal.toReal <|
            MeasureTheory.eLpNorm_congr_ae
              (MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hp_le_t))
    _ ≤
        (MeasureTheory.eLpNorm f t G.measure *
          G.measure Set.univ ^ (1 / p.toReal - 1 / t.toReal)).toReal :=
          ENNReal.toReal_mono hmul_ne_top hle
    _ = (G.measure Set.univ ^ (1 / p.toReal - 1 / t.toReal)).toReal * ‖f‖ := by
          rw [ENNReal.toReal_mul, Lp.norm_def, mul_comm]
    _ = C * ‖f‖ := by
          rfl

/-- The continuous inclusion `lpInclusion` preserves the underlying function a.e. -/
theorem coeFn_lpInclusion
    {t : ℝ≥0∞} [Fact (1 ≤ t)]
    (hp_ne_top : p ≠ ∞) (ht_ne_top : t ≠ ∞) (hp_le_t : p ≤ t)
    (f : Lp ℂ t G.measure) :
    lpInclusion (G := G) (p := p) (t := t) hp_ne_top ht_ne_top hp_le_t f =ᵐ[G.measure] f := by
  have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
    dsimp [WeakGridSpace.measure]
    exact G.grid.isFinite
  letI := hfinite
  change
    (((Lp.memLp f).mono_exponent hp_le_t).toLp f : α → ℂ) =ᵐ[G.measure] f
  exact MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hp_le_t)

/-- Applying `lpInclusion` to the `L^t` realization of a level block recovers its `L^p` value. -/
theorem lpInclusion_levelBlock_toLt
    {A : AtomFamily G s p u} {t : ℝ≥0∞} [Fact (1 ≤ t)]
    (hp_ne_top : p ≠ ∞) (ht_ne_top : t ≠ ∞)
    (hp_le_t : p ≤ t) (ht_le_pu : t ≤ p * u)
    {k : ℕ} (B : LevelBlock A k) :
    lpInclusion (G := G) (p := p) (t := t) hp_ne_top ht_ne_top hp_le_t
        (B.toLt A ht_le_pu) = B.toLp A := by
  apply Lp.ext
  exact ((coeFn_lpInclusion (G := G) (p := p) (t := t)
    hp_ne_top ht_ne_top hp_le_t (B.toLt A ht_le_pu)).trans
      (LevelBlock.coeFn_toLt A ht_le_pu B)).trans
        (LevelBlock.coeFn_toLp A B).symm
/--
Paper's `L^t` embedding theorem: coefficient-cost formulation.

**Main Result**: If `C_co(t, q, (|P^k|^{t(s - 1/p + 1/t)})_k)` is finite,
then $$‖g‖_t ≤ C_{kt} ‖g‖_{B^s_{p,q}(A)}$$

where:
- `C_mult` and the constant `C_{k,t}` depend on the level weights via `cCoefficient`
- `pqCost` measures the representation's coefficient cost in `(p,q)` coordinates
- Summability of the level blocks in `L^t` is guaranteed by finite coefficient cost
-/
theorem lp_embedding_adapted_statement
    {A : AtomFamily G s p u} {t : ℝ≥0∞}
    [Fact (1 ≤ t)]
    (hp_ne_top : p ≠ ∞) (ht_ne_top : t ≠ ∞)
    (hq_one : 1 ≤ q)
    (hp_le_t : p ≤ t) (ht_le_pu : t ≤ p * u)
    (hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / t.toReal)
    {g : Lp ℂ p G.measure} (R : LpGridRepresentation A g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R)
    (hCco_fin : cCoefficientFinite t q (fun k =>
      (levelMeasureWeight G s p t k) ^ t.toReal)) :
        (MeasureTheory.eLpNorm (g : α → ℂ) t G.measure).toReal ≤
        ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / t.toReal)) *
        cCoefficient t q (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
          LpGridRepresentation.pqCost (q := q) R := by
  have hWeightedBound :=
    weighted_sum_le_cCoefficient_mul_pqCost_of_one_le
      (G := G) (s := s) (p := p) (u := u) (q := q) (A := A) (t := t)
      ht_ne_top hq_one R hRfin hCco_fin
  have hWeightSummable : Summable (fun k =>
      levelMeasureWeight G s p t k * (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
    let w : ℕ → ℝ := fun k => levelMeasureWeight G s p t k
    let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
    by_cases hq1 : q = 1
    · have ht_pos : 0 < t.toReal := (ENNReal.toReal_pos_iff_ne_top t).2 ht_ne_top
      have hC_bdd : BddAbove (Set.range fun k => ((w k) ^ t.toReal) ^ (1 / t.toReal)) := by
        simpa [cCoefficientFinite, hq1] using hCco_fin
      let C : ℝ := cCoefficient t q (fun k => (w k) ^ t.toReal)
      have hC_def : C = sSup (Set.range fun k => ((w k) ^ t.toReal) ^ (1 / t.toReal)) := by
        simp [C, cCoefficient, hq1]
      have hw_le_C : ∀ k, w k ≤ C := by
        intro k
        have hk_nonneg : 0 ≤ w k := by
          dsimp [w]
          exact levelMeasureWeight_nonneg G s p t k
        have hk_pow : ((w k) ^ t.toReal) ^ (1 / t.toReal) = w k := by
          simpa [one_div] using (Real.rpow_rpow_inv hk_nonneg ht_pos.ne')
        have hC_bdd' : BddAbove (Set.range fun k => ((w k) ^ t.toReal) ^ t.toReal⁻¹) := by
          simpa [one_div] using hC_bdd
        have hk_pow' : ((w k) ^ t.toReal) ^ t.toReal⁻¹ = w k := by
          simpa [one_div] using hk_pow
        have hk_le : ((w k) ^ t.toReal) ^ t.toReal⁻¹ ≤
            sSup (Set.range fun k => ((w k) ^ t.toReal) ^ t.toReal⁻¹) :=
          le_csSup hC_bdd' ⟨k, rfl⟩
        simpa [hC_def] using hk_pow' ▸ hk_le
      have hRsum : Summable a := by
        simpa [LpGridRepresentation.FinitePQCost, hq1, a] using hRfin
      have hprod_le :
          (fun k => w k * a k) ≤ (fun k => C * a k) := by
        intro k
        have ha_nonneg : 0 ≤ a k := by
          dsimp [a]
          exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
        exact mul_le_mul_of_nonneg_right (hw_le_C k) ha_nonneg
      exact Summable.of_nonneg_of_le
        (fun k => mul_nonneg
          (levelMeasureWeight_nonneg G s p t k)
          (Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
        hprod_le
        (hRsum.mul_left C)
    · by_cases hq_top : q = ∞
      · subst hq_top
        have ht_pos : 0 < t.toReal := (ENNReal.toReal_pos_iff_ne_top t).2 ht_ne_top
        have hRbdd : BddAbove (Set.range a) := by
          simpa [LpGridRepresentation.FinitePQCost, a] using hRfin
        let C : ℝ := LpGridRepresentation.pqCost (q := ∞) R
        have hC_def : C = sSup (Set.range a) := by
          simp [C, LpGridRepresentation.pqCost, a]
        have ha_le_C : ∀ k, a k ≤ C := by
          intro k
          simpa [hC_def] using le_csSup hRbdd ⟨k, rfl⟩
        have hWsum_raw : Summable (fun k => ((w k) ^ t.toReal) ^ (1 / t.toReal)) := by
          simpa [cCoefficientFinite] using hCco_fin
        have hwpow : ∀ k, ((w k) ^ t.toReal) ^ (1 / t.toReal) = w k := by
          intro k
          have hw_nonneg : 0 ≤ w k := by
            dsimp [w]
            exact levelMeasureWeight_nonneg G s p t k
          simpa [one_div] using (Real.rpow_rpow_inv hw_nonneg ht_pos.ne')
        have hWsum : Summable w := hWsum_raw.congr hwpow
        have hprod_le :
            (fun k => w k * a k) ≤ (fun k => w k * C) := by
          intro k
          exact mul_le_mul_of_nonneg_left (ha_le_C k)
            (by dsimp [w]; exact levelMeasureWeight_nonneg G s p t k)
        exact Summable.of_nonneg_of_le
          (fun k => mul_nonneg
            (levelMeasureWeight_nonneg G s p t k)
            (Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
          hprod_le
          (hWsum.mul_right C)
      · let q' : ℝ≥0∞ := q / (q - 1)
        have ht_pos : 0 < t.toReal := (ENNReal.toReal_pos_iff_ne_top t).2 ht_ne_top
        have hq_toReal_le : (1 : ℝ) ≤ q.toReal := by
          have h := ENNReal.toReal_mono hq_top hq_one
          simpa using h
        have hq_toReal_ne_one : q.toReal ≠ 1 := by
          intro hreal
          apply hq1
          have hqeq : (1 : ℝ≥0∞) = q := by
            exact (ENNReal.toReal_eq_toReal ENNReal.one_ne_top hq_top).mp (by simpa [hreal])
          exact hqeq.symm
        have hq_toReal_one : 1 < q.toReal :=
          lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
        have hCsum : Summable (fun k => ((w k) ^ t.toReal) ^ (q'.toReal / t.toReal)) := by
          simpa [cCoefficientFinite, hq1, hq_top, q'] using hCco_fin
        have hAsum_raw : Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
          simpa [LpGridRepresentation.FinitePQCost, hq_top] using hRfin
        have hwpow : ∀ k, ((w k) ^ t.toReal) ^ (q'.toReal / t.toReal) = (w k) ^ q'.toReal := by
          intro k
          have hw_nonneg : 0 ≤ w k := by
            dsimp [w]
            exact levelMeasureWeight_nonneg G s p t k
          have hdiv : q'.toReal / t.toReal = (1 / t.toReal) * q'.toReal := by
            field_simp [ht_pos.ne']
          calc
            ((w k) ^ t.toReal) ^ (q'.toReal / t.toReal)
                = ((w k) ^ t.toReal) ^ ((1 / t.toReal) * q'.toReal) := by rw [hdiv]
            _ = (((w k) ^ t.toReal) ^ (1 / t.toReal)) ^ q'.toReal := by
                  rw [Real.rpow_mul (Real.rpow_nonneg hw_nonneg _)]
            _ = (w k) ^ q'.toReal := by
                  congr 1
                  simpa [one_div] using (Real.rpow_rpow_inv hw_nonneg ht_pos.ne')
        have hApow : ∀ k, (a k) ^ q.toReal = (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
          intro k
          have hA_nonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
          by_cases hp_zero : p.toReal = 0
          · simp [a, hp_zero]
          · have hp_pos : 0 < p.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hp_zero)
            have hdiv : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
              field_simp [hp_pos.ne']
            calc
              (a k) ^ q.toReal
                  = ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ q.toReal := by rfl
              _ = (R.levelCoeffPower k) ^ ((1 / p.toReal) * q.toReal) := by
                    rw [← Real.rpow_mul hA_nonneg]
              _ = (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by rw [hdiv]
        have hWsum : Summable (fun k => (w k) ^ q'.toReal) := hCsum.congr hwpow
        have hAsum : Summable (fun k => (a k) ^ q.toReal) := hAsum_raw.congr (fun k => (hApow k).symm)
        have hw_nonneg : ∀ k, 0 ≤ w k := by
          intro k
          dsimp [w]
          exact levelMeasureWeight_nonneg G s p t k
        have ha_nonneg : ∀ k, 0 ≤ a k := by
          intro k
          dsimp [a]
          exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
        have hq_conj : q'.toReal.HolderConjugate q.toReal := by
          simpa [q'] using holderConjugate_q_div_qsub1_toReal (q := q) hq_toReal_one hq_top
        exact Real.summable_mul_of_Lp_Lq_of_nonneg hq_conj hw_nonneg ha_nonneg hWsum hAsum
  have hBlocks :=
    summable_blockLt_norm_of_summable_weighted_coeff
      (G := G) (s := s) (p := p) (q := q) (t := t)
      hp_ne_top ht_ne_top hp_le_t ht_le_pu hs_nonneg R hWeightSummable hWeightedBound
  rcases hBlocks with ⟨hSummableNorm, hNormSumBound⟩
  let F : ℕ → Lp ℂ t G.measure := fun k => (R.block k).toLt (t := t) A ht_le_pu
  have hSummableF : Summable F := hSummableNorm.of_norm
  let h : Lp ℂ t G.measure := ∑' k, F k
  let I := lpInclusion (G := G) (p := p) (t := t) hp_ne_top ht_ne_top hp_le_t
  have hHasSumI : HasSum (fun k => I (F k)) (I h) := by
    simpa [F, h] using hSummableF.hasSum.mapL I
  have hHasSumP : HasSum (fun k => (R.block k).toLp A) (I h) := by
    refine hHasSumI.congr_fun ?_
    intro k
    simpa [F] using (lpInclusion_levelBlock_toLt
      (G := G) (s := s) (p := p) (u := u) (A := A) (t := t)
      hp_ne_top ht_ne_top hp_le_t ht_le_pu (R.block k)).symm
  have hIg : I h = g := HasSum.unique hHasSumP R.hasSum
  have hg_ae : (g : α → ℂ) =ᵐ[G.measure] h := by
    exact ((show (I h : α → ℂ) =ᵐ[G.measure] (g : α → ℂ) by simpa [hIg])).symm.trans
      (coeFn_lpInclusion (G := G) (p := p) (t := t) hp_ne_top ht_ne_top hp_le_t h)
  have hnorm_h : ‖h‖ ≤ ∑' k, ‖F k‖ := by
    simpa [F, h] using norm_tsum_le_tsum_norm hSummableNorm
  calc
    (MeasureTheory.eLpNorm (g : α → ℂ) t G.measure).toReal
        = (MeasureTheory.eLpNorm (h : α → ℂ) t G.measure).toReal := by
          exact congrArg ENNReal.toReal (MeasureTheory.eLpNorm_congr_ae hg_ae)
    _ = ‖h‖ := by
          symm
          rw [Lp.norm_def]
    _ ≤ ∑' k, ‖F k‖ := hnorm_h
    _ = ∑' k, ‖(R.block k).toLt (t := t) A ht_le_pu‖ := by
      rfl
    _ ≤ ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / t.toReal)) *
          cCoefficient t q (fun k => (levelMeasureWeight G s p t k) ^ t.toReal) *
            LpGridRepresentation.pqCost (q := q) R := hNormSumBound

/-- The representation coefficient gauge `pqCost` is nonnegative. -/
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

/--
The representation coefficient gauge satisfies the triangle inequality for
finite-cost representations.
-/
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

/-- Finite `(p,q)` coefficient cost is preserved under addition of representations. -/
theorem add_finitePQCost
    {A : AtomFamily G s p u} {q : ℝ≥0∞} {g h : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g)
    (S : LpGridRepresentation A h)
    (hp_top : p ≠ ∞)
    (hq_one : 1 ≤ q)
    (hRfin : FinitePQCost (q := q) R)
    (hSfin : FinitePQCost (q := q) S) :
    FinitePQCost (q := q) (add R S) := by
  by_cases hq : q = ∞
  · have hRbdd : BddAbove (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [FinitePQCost, hq] using hRfin
    have hSbdd : BddAbove (Set.range fun k => (S.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [FinitePQCost, hq] using hSfin
    rcases hRbdd with ⟨CR, hCR⟩
    rcases hSbdd with ⟨CS, hCS⟩
    have hBdd : BddAbove (Set.range fun k => ((add R S).levelCoeffPower k) ^ (1 / p.toReal)) := by
      refine ⟨CR + CS, ?_⟩
      rintro x ⟨k, rfl⟩
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
            ((ENNReal.dichotomy p).resolve_left hp_top)
            (by intro Q hQ; exact norm_nonneg _)
            (by intro Q hQ; exact norm_nonneg _))
      exact le_trans hk (add_le_add (hCR ⟨k, rfl⟩) (hCS ⟨k, rfl⟩))
    simpa [FinitePQCost, hq] using hBdd
  · have hsum :
        Summable (fun k => ((add R S).levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
      haveI : Fact (1 ≤ q) := ⟨hq_one⟩
      have hRq : Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
        simpa [FinitePQCost, hq] using hRfin
      have hSq : Summable (fun k => (S.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
        simpa [FinitePQCost, hq] using hSfin
      let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
      let b : ℕ → ℝ := fun k => (S.levelCoeffPower k) ^ (1 / p.toReal)
      let d : ℕ → ℝ := fun k => ((add R S).levelCoeffPower k) ^ (1 / p.toReal)
      have hq1 : 1 ≤ q.toReal := (ENNReal.dichotomy q).resolve_left hq
      have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 hp_top
      have ha_nonneg : ∀ k, 0 ≤ a k := by
        intro k; dsimp [a]; exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
      have hb_nonneg : ∀ k, 0 ≤ b k := by
        intro k; dsimp [b]; exact Real.rpow_nonneg (S.levelCoeffPower_nonneg k) _
      have hd_nonneg : ∀ k, 0 ≤ d k := by
        intro k; dsimp [d]; exact Real.rpow_nonneg ((add R S).levelCoeffPower_nonneg k) _
      have hRq' : Summable (fun k => (a k) ^ q.toReal) := by
        refine hRq.congr ?_
        intro k
        rw [show q.toReal / p.toReal = (1 / p.toReal) * q.toReal by field_simp [hp_pos.ne']]
        rw [Real.rpow_mul (R.levelCoeffPower_nonneg k)]
      have hSq' : Summable (fun k => (b k) ^ q.toReal) := by
        refine hSq.congr ?_
        intro k
        rw [show q.toReal / p.toReal = (1 / p.toReal) * q.toReal by field_simp [hp_pos.ne']]
        rw [Real.rpow_mul (S.levelCoeffPower_nonneg k)]
      have hsum_ab := Real.summable_Lp_add_of_nonneg hq1 ha_nonneg hb_nonneg hRq' hSq'
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
            ((ENNReal.dichotomy p).resolve_left hp_top)
            (by intro Q hQ; exact norm_nonneg _)
            (by intro Q hQ; exact norm_nonneg _))
      have hdq_le : (fun k => (d k) ^ q.toReal) ≤ fun k => (a k + b k) ^ q.toReal := by
        intro k
        exact Real.rpow_le_rpow (hd_nonneg k) (hdk k) (by positivity)
      have hsum_dq := Summable.of_nonneg_of_le
        (by intro k; exact Real.rpow_nonneg (hd_nonneg k) _)
        hdq_le hsum_ab
      refine hsum_dq.congr ?_
      intro k
      rw [show q.toReal / p.toReal = (1 / p.toReal) * q.toReal by field_simp [hp_pos.ne']]
      rw [Real.rpow_mul ((add R S).levelCoeffPower_nonneg k)]
    simpa [FinitePQCost, hq] using hsum

/-- Scaling a representation scales its `pqCost` by the scalar norm. -/
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

/-- Finite `(p,q)` coefficient cost is preserved under scalar multiplication of representations. -/
theorem smul_finitePQCost
    {A : AtomFamily G s p u} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    (c : ℂ) {R : LpGridRepresentation A g}
    (hRfin : FinitePQCost (q := q) R) :
    FinitePQCost (q := q) (smul c R) := by
  by_cases hq : q = ∞
  · have hRbdd : BddAbove (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [FinitePQCost, hq] using hRfin
    rcases hRbdd with ⟨C, hC⟩
    have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
    have hBdd : BddAbove (Set.range fun k => ((smul c R).levelCoeffPower k) ^ (1 / p.toReal)) := by
      refine ⟨‖c‖ * C, ?_⟩
      rintro x ⟨k, rfl⟩
      have hRnonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
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
        _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left (hC ⟨k, rfl⟩) (norm_nonneg c)
    simpa [FinitePQCost, hq] using hBdd
  · have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
    have hRsum : Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
      simpa [FinitePQCost, hq] using hRfin
    have hsum : Summable (fun k => ((smul c R).levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
      have hterm :
          ∀ k,
            ((smul c R).levelCoeffPower k) ^ (q.toReal / p.toReal)
              = ‖c‖ ^ q.toReal * (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
        intro k
        have hRnonneg : 0 ≤ R.levelCoeffPower k := by
          exact R.levelCoeffPower_nonneg k
        have hpow :
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
              = (‖c‖ ^ p.toReal * R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by rw [hpow]
          _ = (‖c‖ ^ p.toReal) ^ (q.toReal / p.toReal) * (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
                rw [Real.mul_rpow (by positivity) hRnonneg]
          _ = ‖c‖ ^ q.toReal * (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
                have hdiv : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
                  field_simp [hp_pos.ne']
                rw [hdiv, Real.rpow_mul (by positivity)]
                have hcp : (‖c‖ ^ p.toReal) ^ (1 / p.toReal) = ‖c‖ := by
                  simpa [one_div] using (Real.rpow_rpow_inv (norm_nonneg c) hp_pos.ne')
                rw [hcp]
      refine (hRsum.mul_left (‖c‖ ^ q.toReal)).congr ?_
      intro k
      symm
      exact hterm k
    simpa [FinitePQCost, hq] using hsum

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

/-- The zero vector admits a Besov-ish atomic representation. -/
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

/-- Besov-ish representations are closed under addition. -/
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

/-- Besov-ish representations are closed under complex scalar multiplication. -/
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
The zero vector has finite `(p,q)` coefficient cost.

The witness representation is the zero Besov-ish representation, whose
levelwise coefficient powers all vanish.
-/
theorem memBesovishCoeffCost_zero (A : AtomFamily G s p u) [Fact (1 ≤ q)] :
    MemBesovishCoeffCost A q (0 : Lp ℂ p G.measure) := by
  let R : LpGridRepresentation A (0 : Lp ℂ p G.measure) :=
    { block := fun k => LevelBlock.zero A k
      hasSum := by simp }
  refine ⟨R, ?_⟩
  have hp_pos : 0 < p.toReal :=
    (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  have hzero : ∀ k, R.levelCoeffPower k = 0 := by
    intro k
    unfold LpGridRepresentation.levelCoeffPower
    simp [R, LevelBlock.zero, Real.zero_rpow hp_pos.ne']
  by_cases hq : q = ∞
  · rw [if_pos hq]
    refine ⟨0, ?_⟩
    rintro x ⟨k, rfl⟩
    have hinv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
    simpa [hzero k, Real.zero_rpow hinv_pos.ne']
  · have : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
    have hq_pos : 0 < q.toReal := by
      linarith [(ENNReal.dichotomy q).resolve_left hq]
    have hpow_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
    rw [if_neg hq]
    simpa [hzero, Real.zero_rpow hpow_pos.ne'] using this

/-- Finite-cost Besov-ish representations are closed under addition. -/
theorem memBesovishCoeffCost_add {A : AtomFamily G s p u}
    {g h : Lp ℂ p G.measure}
    [Fact (1 ≤ q)]
    (hg : MemBesovishCoeffCost A q g) (hh : MemBesovishCoeffCost A q h) :
    MemBesovishCoeffCost A q (g + h) := by
  rcases hg with ⟨Rg, hRgfin⟩
  rcases hh with ⟨Rh, hRhfin⟩
  refine ⟨LpGridRepresentation.add (A := A) Rg Rh, ?_⟩
  exact LpGridRepresentation.add_finitePQCost
    (A := A) (q := q) Rg Rh A.p_ne_top Fact.out hRgfin hRhfin

/-- Finite-cost Besov-ish representations are closed under scalar multiplication. -/
theorem memBesovishCoeffCost_smul {A : AtomFamily G s p u}
    (c : ℂ) {g : Lp ℂ p G.measure}
    (hg : MemBesovishCoeffCost A q g) :
    MemBesovishCoeffCost A q (c • g) := by
  rcases hg with ⟨R, hRfin⟩
  refine ⟨LpGridRepresentation.smul (A := A) c R, ?_⟩
  exact LpGridRepresentation.smul_finitePQCost (A := A) (q := q) c hRfin

/--
The Besov-ish space as a complex linear subspace of `L^p`.
-/
def BesovishSpace (A : AtomFamily G s p u) (q : ℝ≥0∞)
    [Fact (1 ≤ q)]
    : Submodule ℂ (Lp ℂ p G.measure) where
  -- Carrier: all `L^p` elements admitting a Besov-ish atomic representation with finite p q cost.
  carrier := { g | MemBesovishCoeffCost A q g }
  zero_mem' := memBesovishCoeffCost_zero (A := A) (q := q)
  add_mem' := by
    intro g h hg hh
    exact memBesovishCoeffCost_add (A := A) (q := q) hg hh
  smul_mem' := by
    intro c g hg
    exact memBesovishCoeffCost_smul (A := A) (q := q) c hg

/--
The Besov-ish space is a linear subspace of `L^p`.
-/
theorem besovishSpace_is_linear_subspace
    (A : AtomFamily G s p u) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ E : Submodule ℂ (Lp ℂ p G.measure), E = BesovishSpace A q :=
  ⟨BesovishSpace A q, rfl⟩

/--
As a submodule of `L^p`, `BesovishSpace A q` carries the ambient complex
normed-space structure supplied by Mathlib.

This is the inherited `L^p` norm, not the coefficient-cost gauge
`BesovishSpace.Norm_Costpq`.
-/
theorem besovishSpace_has_normedSpace
    (A : AtomFamily G s p u) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Nonempty (NormedSpace ℂ (BesovishSpace A q)) :=
  ⟨inferInstance⟩

variable [Fact (1 ≤ q)]

namespace BesovishSpace

/-- Candidate upper bounds for the `pqCost` gauge of `x`. -/
def pqCostUpperSet
    (A : AtomFamily G s p u) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (x : BesovishSpace A q) : Set ℝ :=
  { c | ∃ R : LpGridRepresentation A (x : Lp ℂ p G.measure),
      LpGridRepresentation.FinitePQCost (q := q) R ∧
      LpGridRepresentation.pqCost (q := q) R ≤ c }

/-- Infimum gauge induced by `pqCost` on admissible representations of `x`. -/
noncomputable def pqPseudoNorm
    (A : AtomFamily G s p u) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (x : BesovishSpace A q) : ℝ :=
  sInf (pqCostUpperSet A q x)

/--
`Norm_Costpq(g)` is the infimum of the `(p,q)` costs of all admissible
finite-cost representations of `g` in the Besov-ish space.
-/
noncomputable def Norm_Costpq
    (A : AtomFamily G s p u) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (g : BesovishSpace A q) : ℝ :=
  pqPseudoNorm A q g

variable {A : AtomFamily G s p u} {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Global hypothesis: every Besov-ish vector admits a representation with finite `(p,q)` cost. -/
def HasFiniteCostRepresentations (A : AtomFamily G s p u) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] : Prop :=
  ∀ x : BesovishSpace A q,
    ∃ R : LpGridRepresentation A (x : Lp ℂ p G.measure),
      LpGridRepresentation.FinitePQCost (q := q) R

/-- The set of admissible `pqCost` upper bounds is nonempty under the global hypothesis. -/
theorem pqCostUpperSet_nonempty
    (hA : HasFiniteCostRepresentations (A := A) q)
    (x : BesovishSpace A q) :
    (pqCostUpperSet A q x).Nonempty := by
  rcases hA x with ⟨R, hRfin⟩
  exact ⟨LpGridRepresentation.pqCost (q := q) R, ⟨R, hRfin, le_rfl⟩⟩

/-- Every `pqCost` upper set is bounded below by `0`. -/
theorem pqCostUpperSet_bddBelow
    (x : BesovishSpace A q) :
    BddBelow (pqCostUpperSet A q x) := by
  refine ⟨0, ?_⟩
  intro c hc
  rcases hc with ⟨R, -, hRc⟩
  exact le_trans (LpGridRepresentation.pqCost_nonneg R) hRc

/-- The gauge `Norm_Costpq` is nonnegative whenever finite-cost representations exist. -/
theorem Norm_Costpq_nonneg
    (hA : HasFiniteCostRepresentations (A := A) q)
    (g : BesovishSpace A q) :
    0 ≤ Norm_Costpq A q g := by
  unfold Norm_Costpq pqPseudoNorm
  refine le_csInf (pqCostUpperSet_nonempty (A := A) (q := q) hA g) ?_
  intro c hc
  rcases hc with ⟨R, -, hRc⟩
  exact le_trans (LpGridRepresentation.pqCost_nonneg R) hRc

/-- The infimum gauge is bounded above by the cost of any admissible representation. -/
theorem Norm_Costpq_le_cost
    (g : BesovishSpace A q)
    (R : LpGridRepresentation A (g : Lp ℂ p G.measure))
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R) :
    Norm_Costpq A q g ≤ LpGridRepresentation.pqCost (q := q) R := by
  unfold Norm_Costpq pqPseudoNorm
  exact csInf_le (pqCostUpperSet_bddBelow (A := A) (q := q) g) ⟨R, hRfin, le_rfl⟩

/--
For every `ε > 0`, there is an admissible representation whose `(p,q)` cost
is within `ε` of `Norm_Costpq`.
-/
theorem exists_cost_lt_Norm_Costpq_add
    (hA : HasFiniteCostRepresentations (A := A) q)
    (g : BesovishSpace A q) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : LpGridRepresentation A (g : Lp ℂ p G.measure),
      LpGridRepresentation.FinitePQCost (q := q) R ∧
      LpGridRepresentation.pqCost (q := q) R < Norm_Costpq A q g + ε := by
  have hlt : sInf (pqCostUpperSet A q g) < sInf (pqCostUpperSet A q g) + ε :=
    lt_add_of_pos_right _ hε
  rcases exists_lt_of_csInf_lt
      (pqCostUpperSet_nonempty (A := A) (q := q) hA g) hlt with
      ⟨c, hc, hclt⟩
  rcases hc with ⟨R, hRfin, hRc⟩
  refine ⟨R, hRfin, ?_⟩
  exact lt_of_le_of_lt hRc (by simpa [pqPseudoNorm, Norm_Costpq] using hclt)

/-- The gauge `Norm_Costpq` satisfies the triangle inequality. -/
theorem Norm_Costpq_add_le
    (hp_top : p ≠ ∞)
    (hA : HasFiniteCostRepresentations (A := A) q)
    (x y : BesovishSpace A q) :
    Norm_Costpq A q (x + y) ≤ Norm_Costpq A q x + Norm_Costpq A q y := by
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases exists_cost_lt_Norm_Costpq_add (A := A) (q := q) hA x hε2 with
    ⟨Rx, hRxfin, hRxlt⟩
  rcases exists_cost_lt_Norm_Costpq_add (A := A) (q := q) hA y hε2 with
    ⟨Ry, hRyfin, hRylt⟩
  let Rsum := LpGridRepresentation.add (A := A) Rx Ry
  have h0 :
      Norm_Costpq A q (x + y) ≤ LpGridRepresentation.pqCost (q := q) Rsum :=
    Norm_Costpq_le_cost (A := A) (q := q) (g := x + y) Rsum
      (LpGridRepresentation.add_finitePQCost (A := A) (q := q) Rx Ry hp_top Fact.out hRxfin hRyfin)
  have h1 :
      LpGridRepresentation.pqCost (q := q) Rsum
        ≤ LpGridRepresentation.pqCost (q := q) Rx + LpGridRepresentation.pqCost (q := q) Ry :=
    LpGridRepresentation.pqCost_triangle (A := A) (q := q) Rx Ry hp_top Fact.out hRxfin hRyfin
  have h2 :
      LpGridRepresentation.pqCost (q := q) Rx + LpGridRepresentation.pqCost (q := q) Ry
        ≤ (Norm_Costpq A q x + ε / 2) + (Norm_Costpq A q y + ε / 2) :=
    add_le_add (le_of_lt hRxlt) (le_of_lt hRylt)
  calc
    Norm_Costpq A q (x + y)
      ≤ LpGridRepresentation.pqCost (q := q) Rsum := h0
    _ ≤ LpGridRepresentation.pqCost (q := q) Rx + LpGridRepresentation.pqCost (q := q) Ry := h1
    _ ≤ (Norm_Costpq A q x + ε / 2) + (Norm_Costpq A q y + ε / 2) := h2
    _ = Norm_Costpq A q x + Norm_Costpq A q y + ε := by ring_nf

/-- The gauge `Norm_Costpq` is homogeneous with respect to complex scalars. -/
theorem Norm_Costpq_smul_le
    (hp_top : p ≠ ∞)
    (hA : HasFiniteCostRepresentations (A := A) q)
    (c : ℂ) (x : BesovishSpace A q) :
    Norm_Costpq A q (c • x) ≤ ‖c‖ * Norm_Costpq A q x := by
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hden : 0 < ‖c‖ + 1 := by linarith [norm_nonneg c]
  have hδ : 0 < ε / (‖c‖ + 1) := by positivity
  rcases exists_cost_lt_Norm_Costpq_add (A := A) (q := q) hA x hδ with
    ⟨Rx, hRxfin, hRxlt⟩
  let Rc := LpGridRepresentation.smul (A := A) c Rx
  have h0 : Norm_Costpq A q (c • x) ≤ LpGridRepresentation.pqCost (q := q) Rc :=
    Norm_Costpq_le_cost (A := A) (q := q) (g := c • x) Rc
      (LpGridRepresentation.smul_finitePQCost (A := A) (q := q) c hRxfin)
  have h1 : LpGridRepresentation.pqCost (q := q) Rc = ‖c‖ * LpGridRepresentation.pqCost (q := q) Rx :=
    LpGridRepresentation.pqCost_smul (A := A) (q := q) c Rx hp_top Fact.out hRxfin
  have h2 : LpGridRepresentation.pqCost (q := q) Rx ≤ Norm_Costpq A q x + ε / (‖c‖ + 1) :=
    le_of_lt hRxlt
  have h3 :
      ‖c‖ * LpGridRepresentation.pqCost (q := q) Rx
        ≤ ‖c‖ * (Norm_Costpq A q x + ε / (‖c‖ + 1)) :=
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
    Norm_Costpq A q (c • x)
        ≤ LpGridRepresentation.pqCost (q := q) Rc := h0
    _ = ‖c‖ * LpGridRepresentation.pqCost (q := q) Rx := h1
    _ ≤ ‖c‖ * (Norm_Costpq A q x + ε / (‖c‖ + 1)) := h3
    _ = ‖c‖ * Norm_Costpq A q x + ‖c‖ * (ε / (‖c‖ + 1)) := by ring
    _ ≤ ‖c‖ * Norm_Costpq A q x + ε := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right h4 (‖c‖ * Norm_Costpq A q x)

/-- The gauge `Norm_Costpq` is exactly homogeneous with respect to complex scalars. -/
theorem Norm_Costpq_smul_eq
    (hp_top : p ≠ ∞)
    (hA : HasFiniteCostRepresentations (A := A) q)
    (c : ℂ) (x : BesovishSpace A q) :
    Norm_Costpq A q (c • x) = ‖c‖ * Norm_Costpq A q x := by
  refine le_antisymm
    (Norm_Costpq_smul_le (A := A) (q := q) hp_top hA c x) ?_
  by_cases hc : c = 0
  · subst c
    simpa using Norm_Costpq_nonneg (A := A) (q := q) hA ((0 : ℂ) • x)
  · have hcx :
        c⁻¹ • (c • x) = x := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hle :
        Norm_Costpq A q x ≤ ‖c⁻¹‖ * Norm_Costpq A q (c • x) := by
      simpa [hcx] using
        Norm_Costpq_smul_le (A := A) (q := q) hp_top hA c⁻¹ (c • x)
    have hc_norm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hmul :
        ‖c‖ * Norm_Costpq A q x ≤
          ‖c‖ * (‖c⁻¹‖ * Norm_Costpq A q (c • x)) :=
      mul_le_mul_of_nonneg_left hle (norm_nonneg c)
    have hnorm_inv : ‖c‖ * ‖c⁻¹‖ = (1 : ℝ) := by
      rw [norm_inv, mul_inv_cancel₀ (ne_of_gt hc_norm_pos)]
    calc
      ‖c‖ * Norm_Costpq A q x
          ≤ ‖c‖ * (‖c⁻¹‖ * Norm_Costpq A q (c • x)) := hmul
      _ = Norm_Costpq A q (c • x) := by
        rw [← mul_assoc, hnorm_inv, one_mul]

/--
`Norm_Costpq` controls the `L^t` size of a Besov-ish vector by passing the
representation estimate `lp_embedding_adapted_statement` to almost-minimizing
representations.
-/
theorem lp_norm_le_const_mul_Norm_Costpq
    {t : ℝ≥0∞} [Fact (1 ≤ t)]
    (hp_top : p ≠ ∞) (ht_top : t ≠ ∞)
    (hp_le_t : p ≤ t) (ht_le_pu : t ≤ p * u)
    (hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / t.toReal)
    (hCco_fin : LpGridRepresentation.cCoefficientFinite t q (fun k =>
      (LpGridRepresentation.levelMeasureWeight G s p t k) ^ t.toReal))
    (hA : HasFiniteCostRepresentations (A := A) q)
    (g : BesovishSpace A q) :
    (MeasureTheory.eLpNorm ((g : Lp ℂ p G.measure) : α → ℂ) t G.measure).toReal ≤
      ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / t.toReal)) *
        LpGridRepresentation.cCoefficient t q
          (fun k => (LpGridRepresentation.levelMeasureWeight G s p t k) ^ t.toReal) *
          Norm_Costpq A q g := by
  let C : ℝ :=
    ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / t.toReal)) *
      LpGridRepresentation.cCoefficient t q
        (fun k => (LpGridRepresentation.levelMeasureWeight G s p t k) ^ t.toReal)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (by positivity)
      (LpGridRepresentation.cCoefficient_nonneg t q
        (fun k => (LpGridRepresentation.levelMeasureWeight G s p t k) ^ t.toReal)
        (fun k => Real.rpow_nonneg
          (LpGridRepresentation.levelMeasureWeight_nonneg G s p t k) _))
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hεC : 0 < ε / (C + 1) := by
    have : 0 < C + 1 := by linarith
    positivity
  rcases exists_cost_lt_Norm_Costpq_add (A := A) (q := q) hA g hεC with
    ⟨R, hRfin, hRlt⟩
  have hEmb :
      (MeasureTheory.eLpNorm ((g : Lp ℂ p G.measure) : α → ℂ) t G.measure).toReal ≤
        C * LpGridRepresentation.pqCost (q := q) R := by
    simpa [C] using
      LpGridRepresentation.lp_embedding_adapted_statement
        (G := G) (s := s) (p := p) (u := u) (q := q) (A := A) (t := t)
        hp_top ht_top Fact.out hp_le_t ht_le_pu hs_nonneg R hRfin hCco_fin
  have hRle : LpGridRepresentation.pqCost (q := q) R ≤ Norm_Costpq A q g + ε / (C + 1) :=
    le_of_lt hRlt
  have hmul :
      C * LpGridRepresentation.pqCost (q := q) R ≤
        C * (Norm_Costpq A q g + ε / (C + 1)) :=
    mul_le_mul_of_nonneg_left hRle hC_nonneg
  have hsmall : C * (ε / (C + 1)) ≤ ε := by
    have hfrac : C / (C + 1) ≤ (1 : ℝ) := by
      have hden : 0 < C + 1 := by linarith
      exact (div_le_one hden).2 (by linarith)
    have hεnn : 0 ≤ ε := le_of_lt hε
    have hmul' : (C / (C + 1)) * ε ≤ (1 : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hfrac hεnn
    calc
      C * (ε / (C + 1)) = (C / (C + 1)) * ε := by ring
      _ ≤ (1 : ℝ) * ε := hmul'
      _ = ε := by ring
  calc
    (MeasureTheory.eLpNorm ((g : Lp ℂ p G.measure) : α → ℂ) t G.measure).toReal
        ≤ C * LpGridRepresentation.pqCost (q := q) R := hEmb
    _ ≤ C * (Norm_Costpq A q g + ε / (C + 1)) := hmul
    _ = C * Norm_Costpq A q g + C * (ε / (C + 1)) := by ring
    _ ≤ C * Norm_Costpq A q g + ε := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hsmall (C * Norm_Costpq A q g)

/--
If the Besov gauge vanishes, then the vector is zero. This is obtained by
specializing the `L^t` embedding bound to `t = p`.
-/
theorem eq_zero_of_Norm_Costpq_eq_zero
    (hp_top : p ≠ ∞)
    (hCco_fin : LpGridRepresentation.cCoefficientFinite p q (fun k =>
      (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal))
    (hA : HasFiniteCostRepresentations (A := A) q)
    {g : BesovishSpace A q}
    (hg : Norm_Costpq A q g = 0) :
    g = 0 := by
  have hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / p.toReal := by
    linarith [A.s_pos.le]
  have ht_le_pu : p ≤ p * u := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * u := by exact mul_le_mul_right A.one_le_u p
  have hLp :
      (MeasureTheory.eLpNorm ((g : Lp ℂ p G.measure) : α → ℂ) p G.measure).toReal ≤ 0 := by
    calc
      (MeasureTheory.eLpNorm ((g : Lp ℂ p G.measure) : α → ℂ) p G.measure).toReal
          ≤ ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
              LpGridRepresentation.cCoefficient p q
                (fun k => (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) *
                Norm_Costpq A q g := by
              exact lp_norm_le_const_mul_Norm_Costpq
                (G := G) (s := s) (p := p) (u := u) (q := q) (A := A) (t := p)
                hp_top hp_top le_rfl ht_le_pu hs_nonneg hCco_fin hA g
      _ = 0 := by rw [hg, mul_zero]
  have hnorm_zero : ‖(g : Lp ℂ p G.measure)‖ = 0 := by
    rw [Lp.norm_def]
    exact le_antisymm hLp ENNReal.toReal_nonneg
  apply Subtype.ext
  exact norm_eq_zero.mp hnorm_zero

/--
The metric/normed additive group structure induced by the coefficient-cost
gauge `Norm_Costpq`.

This is deliberately a named definition rather than a global instance, because
`BesovishSpace A q` already inherits Mathlib's ambient `L^p` normed-space
structure as a submodule.
-/
@[reducible]
noncomputable def costNormedAddCommGroup
    (hp_top : p ≠ ∞)
    (hCco_fin : LpGridRepresentation.cCoefficientFinite p q (fun k =>
      (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal))
    (hA : HasFiniteCostRepresentations (A := A) q) :
    NormedAddCommGroup (BesovishSpace A q) where
  norm := Norm_Costpq A q
  dist x y := Norm_Costpq A q (-x + y)
  dist_self := by
    intro x
    have h0 := Norm_Costpq_smul_eq (A := A) (q := q) hp_top hA 0 x
    simpa using h0
  dist_comm := by
    intro x y
    have hcomm : x + -y = -y + x := by
      abel
    calc
      Norm_Costpq A q (-x + y)
          = Norm_Costpq A q ((-1 : ℂ) • (-x + y)) := by
              rw [Norm_Costpq_smul_eq (A := A) (q := q) hp_top hA (-1) (-x + y)]
              simp
      _ = Norm_Costpq A q (-y + x) := by
        simpa [hcomm]
  dist_triangle := by
    intro x y z
    have hsum :
        -x + z = (-x + y) + (-y + z) := by
      abel
    calc
      Norm_Costpq A q (-x + z)
          = Norm_Costpq A q ((-x + y) + (-y + z)) := by rw [hsum]
      _ ≤ Norm_Costpq A q (-x + y) + Norm_Costpq A q (-y + z) :=
        Norm_Costpq_add_le (A := A) (q := q) hp_top hA (-x + y) (-y + z)
  eq_of_dist_eq_zero := by
    intro x y hxy
    have hzero : -x + y = 0 :=
      eq_zero_of_Norm_Costpq_eq_zero (A := A) (q := q) hp_top hCco_fin hA hxy
    have h := congrArg (fun z : BesovishSpace A q => x + z) hzero
    symm
    simpa [add_assoc] using h
  dist_eq := by
    intro x y
    rfl

/-- The coefficient-cost norm is definitionally the norm in `costNormedAddCommGroup`. -/
theorem costNormedAddCommGroup_norm
    (hp_top : p ≠ ∞)
    (hCco_fin : LpGridRepresentation.cCoefficientFinite p q (fun k =>
      (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal))
    (hA : HasFiniteCostRepresentations (A := A) q)
    (x : BesovishSpace A q) :
    @norm (BesovishSpace A q)
      (costNormedAddCommGroup (A := A) (q := q) hp_top hCco_fin hA).toNorm x =
      Norm_Costpq A q x :=
  rfl

/--
The complex normed-space structure associated to the coefficient-cost norm.
Use it locally with `letI := costNormedAddCommGroup ...` and
`letI := costNormedSpace ...` when this norm, rather than the inherited `L^p`
norm, is intended.
-/
@[reducible]
noncomputable def costNormedSpace
    (hp_top : p ≠ ∞)
    (hCco_fin : LpGridRepresentation.cCoefficientFinite p q (fun k =>
      (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal))
    (hA : HasFiniteCostRepresentations (A := A) q) :
    @NormedSpace ℂ (BesovishSpace A q) _
      ({ costNormedAddCommGroup (A := A) (q := q) hp_top hCco_fin hA with } :
        SeminormedAddCommGroup (BesovishSpace A q)) := by
  exact
    @NormedSpace.mk ℂ (BesovishSpace A q) _
      ({ costNormedAddCommGroup (A := A) (q := q) hp_top hCco_fin hA with } :
        SeminormedAddCommGroup (BesovishSpace A q))
      inferInstance
      (by
        intro c x
        change Norm_Costpq A q (c • x) ≤ ‖c‖ * Norm_Costpq A q x
        rw [Norm_Costpq_smul_eq (A := A) (q := q) hp_top hA])

/--
Packaged existence statement: under the hypotheses used in
`normedSpace_and_lp_embedding_summary`, `BesovishSpace A q` admits a complex
normed-space structure whose norm is exactly `Norm_Costpq`.
-/
theorem besovishSpace_has_cost_normedSpace
    (hp_top : p ≠ ∞)
    (hCco_fin : LpGridRepresentation.cCoefficientFinite p q (fun k =>
      (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal))
    (hA : HasFiniteCostRepresentations (A := A) q) :
    ∃ N : NormedAddCommGroup (BesovishSpace A q),
      (∀ x : BesovishSpace A q, @norm (BesovishSpace A q) N.toNorm x = Norm_Costpq A q x) ∧
      Nonempty
        (@NormedSpace ℂ (BesovishSpace A q) _
          ({ N with } : SeminormedAddCommGroup (BesovishSpace A q))) := by
  refine ⟨costNormedAddCommGroup (A := A) (q := q) hp_top hCco_fin hA, ?_, ?_⟩
  · intro x
    rfl
  · exact ⟨costNormedSpace (A := A) (q := q) hp_top hCco_fin hA⟩

/--
Main structural summary for the Besov-ish space endowed with `Norm_Costpq`.

Under the standard finite-cost approximation hypothesis, `Norm_Costpq` satisfies
the norm axioms on `BesovishSpace A q`; moreover every admissible exponent
`t` with `p ≤ t ≤ p*u` yields the continuous embedding estimate
`‖g‖_{L^t} ≤ C_t * Norm_Costpq(g)` with the explicit constant `C_t`.
-/
theorem normedSpace_and_lp_embedding
    (hp_top : p ≠ ∞)
    (hA : HasFiniteCostRepresentations (A := A) q)
    (hCco_fin_p : LpGridRepresentation.cCoefficientFinite p q (fun k =>
      (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal)) :
    (∀ g : BesovishSpace A q, 0 ≤ Norm_Costpq A q g) ∧
    (∀ x y : BesovishSpace A q,
      Norm_Costpq A q (x + y) ≤ Norm_Costpq A q x + Norm_Costpq A q y) ∧
    (∀ c : ℂ, ∀ x : BesovishSpace A q,
      Norm_Costpq A q (c • x) = ‖c‖ * Norm_Costpq A q x) ∧
    (∀ g : BesovishSpace A q, Norm_Costpq A q g = 0 → g = 0) ∧
    (∀ {t : ℝ≥0∞} [Fact (1 ≤ t)]
        (ht_top : t ≠ ∞) (hp_le_t : p ≤ t) (ht_le_pu : t ≤ p * u)
        (hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / t.toReal)
        (hCco_fin_t : LpGridRepresentation.cCoefficientFinite t q (fun k =>
          (LpGridRepresentation.levelMeasureWeight G s p t k) ^ t.toReal)),
      let C_t : ℝ :=
        ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / t.toReal)) *
          LpGridRepresentation.cCoefficient t q
            (fun k => (LpGridRepresentation.levelMeasureWeight G s p t k) ^ t.toReal)
      0 ≤ C_t ∧
      ∀ g : BesovishSpace A q,
        (MeasureTheory.eLpNorm ((g : Lp ℂ p G.measure) : α → ℂ) t G.measure).toReal ≤
          C_t * Norm_Costpq A q g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g
    exact Norm_Costpq_nonneg (A := A) (q := q) hA g
  · intro x y
    exact Norm_Costpq_add_le (A := A) (q := q) hp_top hA x y
  · intro c x
    exact Norm_Costpq_smul_eq (A := A) (q := q) hp_top hA c x
  · intro g hg
    exact eq_zero_of_Norm_Costpq_eq_zero (A := A) (q := q)
      hp_top hCco_fin_p hA hg
  · intro t _ ht_top hp_le_t ht_le_pu hs_nonneg hCco_fin_t
    dsimp
    refine ⟨?_, ?_⟩
    · exact mul_nonneg
        (by positivity)
        (LpGridRepresentation.cCoefficient_nonneg t q
          (fun k => (LpGridRepresentation.levelMeasureWeight G s p t k) ^ t.toReal)
          (fun k => Real.rpow_nonneg
            (LpGridRepresentation.levelMeasureWeight_nonneg G s p t k) _))
    · intro g
      exact lp_norm_le_const_mul_Norm_Costpq
        (G := G) (s := s) (p := p) (u := u) (q := q) (A := A) (t := t)
        hp_top ht_top hp_le_t ht_le_pu hs_nonneg hCco_fin_t hA g

end BesovishSpace



end

end WeakGridSpace
