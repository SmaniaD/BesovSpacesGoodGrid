import BesovSpacesGoodGrid.WeakGridDirectAtoms
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Direct Besov-ish spaces on weak grids

This file contains the local-Banach-free Besov-ish construction.  Level blocks,
representations, and coefficient costs are stated directly for atom families
whose atoms already live in the ambient `L^p` space.
-/

namespace WeakGridSpace

open scoped ENNReal Topology
open MeasureTheory

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

variable {G : WeakGridSpace (α := α)} {s : ℝ} {p q : ℝ≥0∞}
variable [Fact (1 ≤ p)]

/--
A level-`k` block for the direct `L^p` atom API.

For each cell in the level-`k` partition it chooses one scalar coefficient
and one atom, already realized as an element of ambient `L^p`. Its value is
therefore just the finite `L^p` sum `∑ s_Q • a_Q`.
-/
structure LpLevelBlock (A : LpAtomFamily G s p) (k : ℕ) where
  coeff : LevelCell G k → ℂ
  atom : LevelCell G k → Lp ℂ p G.measure
  atom_mem : ∀ Q : LevelCell G k,
    A.IsAtom (levelCellToWeakGridCell G k Q) (atom Q)

namespace LpLevelBlock

/-- A zero-valued direct `L^p` level block, obtained by choosing one atom on each cell. -/
def zero (A : LpAtomFamily G s p) (k : ℕ) : LpLevelBlock A k where
  coeff := fun _ => 0
  atom := fun Q =>
    Classical.choose (A.atoms_nonempty_on (levelCellToWeakGridCell G k Q))
  atom_mem := fun Q =>
    Classical.choose_spec (A.atoms_nonempty_on (levelCellToWeakGridCell G k Q))

/-- The `L^p` term attached to one cell in a direct `L^p` level block. -/
def term (A : LpAtomFamily G s p) {k : ℕ}
    (B : LpLevelBlock A k) (Q : LevelCell G k) : Lp ℂ p G.measure :=
  B.coeff Q • B.atom Q

/-- The value of a direct `L^p` level block as a finite sum over level cells. -/
def toLp (A : LpAtomFamily G s p) {k : ℕ}
    (B : LpLevelBlock A k) : Lp ℂ p G.measure :=
  (G.grid.partitions k).attach.sum fun Q => B.term A Q

/-- The zero direct `L^p` level block represents the zero element of `L^p`. -/
@[simp]
theorem zero_toLp (A : LpAtomFamily G s p) (k : ℕ) :
    (zero A k).toLp A = 0 := by
  simp [toLp, term, zero]

/-- Scalar multiplication of a direct `L^p` level block, keeping the same atoms. -/
def smul (A : LpAtomFamily G s p) {k : ℕ} (c : ℂ)
    (B : LpLevelBlock A k) : LpLevelBlock A k where
  coeff := fun Q => c * B.coeff Q
  atom := B.atom
  atom_mem := B.atom_mem

/-- Evaluating a scaled direct `L^p` block agrees with scalar multiplication. -/
@[simp]
theorem smul_toLp (A : LpAtomFamily G s p) {k : ℕ} (c : ℂ)
    (B : LpLevelBlock A k) :
    (smul A c B).toLp A = c • B.toLp A := by
  simp [toLp, term, smul, Finset.smul_sum, mul_smul]

end LpLevelBlock

/--
The set of all direct `L^p` level-`k` atomic blocks, viewed as elements of
ambient `L^p`.
-/
def LpLevelBlockSet (A : LpAtomFamily G s p) (k : ℕ) :
    Set (Lp ℂ p G.measure) :=
  { f | ∃ B : LpLevelBlock A k, B.toLp A = f }

/-- The zero element belongs to every direct `L^p` level-block set. -/
theorem zero_mem_LpLevelBlockSet (A : LpAtomFamily G s p) (k : ℕ) :
    (0 : Lp ℂ p G.measure) ∈ LpLevelBlockSet A k :=
  ⟨LpLevelBlock.zero A k, by simp⟩

/-- Direct `L^p` level-block sets are closed under scalar multiplication. -/
theorem smul_mem_LpLevelBlockSet (A : LpAtomFamily G s p) (k : ℕ)
    (c : ℂ) {x : Lp ℂ p G.measure} (hx : x ∈ LpLevelBlockSet A k) :
    c • x ∈ LpLevelBlockSet A k := by
  rcases hx with ⟨B, rfl⟩
  exact ⟨LpLevelBlock.smul A c B, by simp⟩

/--
A direct `L^p` grid representation of `g`.

It is a series of direct `L^p` level blocks whose sum is `g` in the ambient
`L^p` space.
-/
structure DirectLpGridRepresentation
    (A : LpAtomFamily G s p) (g : Lp ℂ p G.measure) where
  block : (k : ℕ) → LpLevelBlock A k
  hasSum : HasSum (fun k => (block k).toLp A) g

namespace DirectLpGridRepresentation

/--
Level-`k` coefficient `ℓ^p` power sum for a direct `L^p` representation:
`∑_{Q ∈ P^k} |s_Q|^p`.
-/
def levelCoeffPower
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g) (k : ℕ) : ℝ :=
  ∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ p.toReal

/-- The direct `L^p` level coefficient power is nonnegative. -/
theorem levelCoeffPower_nonneg
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g) (k : ℕ) :
    0 ≤ R.levelCoeffPower k := by
  unfold levelCoeffPower
  exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _

/--
Finite `(p,q)` coefficient cost for direct `L^p` representations.

This is the same coefficient condition as for the legacy representation, but
it no longer refers to any local Banach space data.
-/
def FinitePQCost
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (q : ℝ≥0∞) (R : DirectLpGridRepresentation A g) : Prop :=
  if q = ∞ then
    BddAbove (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal))
  else
    Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal))

/-- The `(p,q)` coefficient gauge of a direct `L^p` representation. -/
def pqCost
    {A : LpAtomFamily G s p} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g) : ℝ :=
  if q = ∞ then
    sSup (Set.range fun k =>
      (R.levelCoeffPower k) ^ (1 / p.toReal))
  else
    (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)

/--
Extended `(p,q)` coefficient cost of a direct `L^p` representation.

This `ℝ≥0∞`-valued version records non-summable coefficient data as `∞`, which
is the form needed for compactness and completeness arguments.
-/
def pqCostENNReal
    {A : LpAtomFamily G s p} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g) : ℝ≥0∞ :=
  if q = ∞ then
    sSup (Set.range fun k =>
      ENNReal.ofReal ((R.levelCoeffPower k) ^ (1 / p.toReal)))
  else
    (∑' k, ENNReal.ofReal ((R.levelCoeffPower k) ^ (q.toReal / p.toReal))) ^
      (1 / q.toReal)

/--
If the extended coefficient cost is finite, then the direct representation has
finite `(p,q)` coefficient cost in the real-valued sense.
-/
theorem finitePQCost_of_pqCostENNReal_ne_top
    {A : LpAtomFamily G s p} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g) (hq_one : 1 ≤ q)
    (hR : pqCostENNReal (q := q) R ≠ ∞) :
    FinitePQCost q R := by
  by_cases hq : q = ∞
  · simp only [FinitePQCost, hq, ↓reduceIte]
    simp only [pqCostENNReal, hq, ↓reduceIte] at hR
    refine ⟨(sSup (Set.range fun k =>
        ENNReal.ofReal ((R.levelCoeffPower k) ^ (1 / p.toReal)))).toReal, ?_⟩
    rintro x ⟨k, rfl⟩
    rw [← ENNReal.ofReal_le_iff_le_toReal hR]
    exact le_sSup ⟨k, rfl⟩
  · simp only [FinitePQCost, hq, ↓reduceIte]
    simp only [pqCostENNReal, hq, ↓reduceIte] at hR
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le hq_one).ne' hq
    have h_inv_pos : 0 < 1 / q.toReal := div_pos one_pos hq_pos
    have htsum_ne_top :
        ∑' k, ENNReal.ofReal ((R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ≠ ∞ := by
      intro heq
      apply hR
      rw [heq, ENNReal.top_rpow_of_pos h_inv_pos]
    exact (ENNReal.summable_toReal htsum_ne_top).congr
      (fun k => ENNReal.toReal_ofReal (Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))

/--
A finite upper bound on the extended direct coefficient cost forces finite
`(p,q)` cost.
-/
theorem finitePQCost_of_pqCostENNReal_le
    {A : LpAtomFamily G s p} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g) (hq_one : 1 ≤ q) {C : ℝ}
    (hR : pqCostENNReal (q := q) R ≤ ENNReal.ofReal C) :
    FinitePQCost q R := by
  apply finitePQCost_of_pqCostENNReal_ne_top (R := R) hq_one
  exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hR ENNReal.ofReal_lt_top)

/-- The zero direct `L^p` representation. -/
def zero (A : LpAtomFamily G s p) :
    DirectLpGridRepresentation A (0 : Lp ℂ p G.measure) where
  block := fun k => LpLevelBlock.zero A k
  hasSum := by
    simp

/-- Representation-level scalar multiplication for direct `L^p` atomic representations. -/
noncomputable def smul
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (c : ℂ) (R : DirectLpGridRepresentation A g) :
    DirectLpGridRepresentation A (c • g) where
  block := fun k => LpLevelBlock.smul A c (R.block k)
  hasSum := by
    simpa [LpLevelBlock.smul_toLp] using R.hasSum.const_smul c

/-- The block of a direct scaled representation evaluates levelwise to the scaled block. -/
@[simp]
theorem smul_block_toLp
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (c : ℂ) (R : DirectLpGridRepresentation A g) (k : ℕ) :
    ((smul c R).block k).toLp A = c • (R.block k).toLp A := by
  simp [smul]

/-- Scaling a direct representation scales each level coefficient power. -/
theorem smul_levelCoeffPower
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (c : ℂ) (R : DirectLpGridRepresentation A g) (k : ℕ) :
    (smul c R).levelCoeffPower k = ‖c‖ ^ p.toReal * R.levelCoeffPower k := by
  unfold levelCoeffPower smul LpLevelBlock.smul
  calc
    (∑ Q : LevelCell G k, ‖c * (R.block k).coeff Q‖ ^ p.toReal)
        = ∑ Q : LevelCell G k, (‖c‖ * ‖(R.block k).coeff Q‖) ^ p.toReal := by
            refine Finset.sum_congr rfl ?_
            intro Q hQ
            rw [norm_mul]
    _ = ∑ Q : LevelCell G k, ‖c‖ ^ p.toReal *
          ‖(R.block k).coeff Q‖ ^ p.toReal := by
          refine Finset.sum_congr rfl ?_
          intro Q hQ
          rw [Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
    _ = ‖c‖ ^ p.toReal *
          ∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ p.toReal := by
          rw [Finset.mul_sum]

/-- The zero direct `L^p` representation has finite coefficient cost. -/
theorem zero_finitePQCost (A : LpAtomFamily G s p) {q : ℝ≥0∞}
    [Fact (1 ≤ q)] :
    FinitePQCost q (zero A) := by
  have hp_pos : 0 < p.toReal :=
    (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  have hzero : ∀ k, (zero A).levelCoeffPower k = 0 := by
    intro k
    unfold levelCoeffPower
    simp [zero, LpLevelBlock.zero, Real.zero_rpow hp_pos.ne']
  by_cases hq : q = ∞
  · rw [FinitePQCost, if_pos hq]
    refine ⟨0, ?_⟩
    rintro x ⟨k, rfl⟩
    have hinv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
    simp [hzero k, Real.zero_rpow hinv_pos.ne']
  · have hq_pos : 0 < q.toReal := by
      linarith [(ENNReal.dichotomy q).resolve_left hq]
    have hpow_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
    rw [FinitePQCost, if_neg hq]
    simp [hzero, Real.zero_rpow hpow_pos.ne']

/-- Finite coefficient cost is preserved under scalar multiplication. -/
theorem smul_finitePQCost
    {A : LpAtomFamily G s p} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    (c : ℂ) {R : DirectLpGridRepresentation A g}
    (hRfin : FinitePQCost q R) :
    FinitePQCost q (smul c R) := by
  by_cases hq : q = ∞
  · have hRbdd : BddAbove (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [FinitePQCost, hq] using hRfin
    rcases hRbdd with ⟨C, hC⟩
    have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
    have hBdd : BddAbove
        (Set.range fun k => ((smul c R).levelCoeffPower k) ^ (1 / p.toReal)) := by
      refine ⟨‖c‖ * C, ?_⟩
      rintro x ⟨k, rfl⟩
      have hRnonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
      have hsum :
          (smul c R).levelCoeffPower k = ‖c‖ ^ p.toReal * R.levelCoeffPower k := by
        unfold levelCoeffPower smul LpLevelBlock.smul
        calc
          (∑ Q : LevelCell G k, ‖c * (R.block k).coeff Q‖ ^ p.toReal)
              = ∑ Q : LevelCell G k, (‖c‖ * ‖(R.block k).coeff Q‖) ^ p.toReal := by
                  refine Finset.sum_congr rfl ?_
                  intro Q hQ
                  rw [norm_mul]
          _ = ∑ Q : LevelCell G k, (‖c‖ ^ p.toReal) *
                (‖(R.block k).coeff Q‖ ^ p.toReal) := by
                refine Finset.sum_congr rfl ?_
                intro Q hQ
                rw [Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
          _ = ‖c‖ ^ p.toReal *
                ∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ p.toReal := by
                rw [Finset.mul_sum]
      calc
        ((smul c R).levelCoeffPower k) ^ (1 / p.toReal)
            = (‖c‖ ^ p.toReal * R.levelCoeffPower k) ^ (1 / p.toReal) := by
                rw [hsum]
        _ = (‖c‖ ^ p.toReal) ^ (1 / p.toReal) *
              (R.levelCoeffPower k) ^ (1 / p.toReal) := by
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
    have hsum : Summable
        (fun k => ((smul c R).levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
      have hterm :
          ∀ k,
            ((smul c R).levelCoeffPower k) ^ (q.toReal / p.toReal)
              = ‖c‖ ^ q.toReal * (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
        intro k
        have hRnonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
        have hpow :
            (smul c R).levelCoeffPower k = ‖c‖ ^ p.toReal * R.levelCoeffPower k := by
          unfold levelCoeffPower smul LpLevelBlock.smul
          calc
            (∑ Q : LevelCell G k, ‖c * (R.block k).coeff Q‖ ^ p.toReal)
                = ∑ Q : LevelCell G k, (‖c‖ * ‖(R.block k).coeff Q‖) ^ p.toReal := by
                    refine Finset.sum_congr rfl ?_
                    intro Q hQ
                    rw [norm_mul]
            _ = ∑ Q : LevelCell G k, (‖c‖ ^ p.toReal) *
                  (‖(R.block k).coeff Q‖ ^ p.toReal) := by
                  refine Finset.sum_congr rfl ?_
                  intro Q hQ
                  rw [Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
            _ = ‖c‖ ^ p.toReal *
                  ∑ Q : LevelCell G k, ‖(R.block k).coeff Q‖ ^ p.toReal := by
                  rw [Finset.mul_sum]
        calc
          ((smul c R).levelCoeffPower k) ^ (q.toReal / p.toReal)
              = (‖c‖ ^ p.toReal * R.levelCoeffPower k) ^
                  (q.toReal / p.toReal) := by rw [hpow]
          _ = (‖c‖ ^ p.toReal) ^ (q.toReal / p.toReal) *
                (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
                rw [Real.mul_rpow (by positivity) hRnonneg]
          _ = ‖c‖ ^ q.toReal * (R.levelCoeffPower k) ^
                (q.toReal / p.toReal) := by
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

end DirectLpGridRepresentation

/--
The direct `L^p` Besov-ish predicate: `g` has a representation by direct
`L^p` atomic level blocks.
-/
def DirectLpMemBesovish (A : LpAtomFamily G s p) (q : ℝ≥0∞)
    (g : Lp ℂ p G.measure) : Prop :=
  let _ : ℝ≥0∞ := q
  Nonempty (DirectLpGridRepresentation A g)

/--
The finite-cost direct `L^p` Besov-ish predicate.

This is the direct analogue of `MemBesovishCoeffCost`, but it uses atoms that
already live in ambient `L^p`.
-/
def DirectLpMemBesovishCoeffCost (A : LpAtomFamily G s p) (q : ℝ≥0∞)
    (g : Lp ℂ p G.measure) : Prop :=
  ∃ R : DirectLpGridRepresentation A g,
    DirectLpGridRepresentation.FinitePQCost q R

omit [Fact (1 ≤ p)] in
/-- The zero vector is a direct `L^p` atom on every weak-grid cell. -/
theorem directLpAtom_zero_mem (A : LpAtomFamily G s p) (Q : WeakGridCell G) :
    (0 : Lp ℂ p G.measure) ∈ A.atoms Q := by
  classical
  rcases A.atoms_nonempty Q with ⟨φ, hφ⟩
  have hneg : (-1 : ℂ) • φ ∈ A.atoms Q :=
    A.atoms_phase_invariant Q φ (-1) hφ (by norm_num)
  have hmid :
      ((1 / 2 : ℝ) • φ + (1 / 2 : ℝ) • ((-1 : ℂ) • φ)) ∈ A.atoms Q := by
    exact (convex_iff_add_mem.mp (A.atoms_convex Q)) hφ hneg
      (by norm_num) (by norm_num) (by norm_num)
  convert hmid using 1
  simp

omit [Fact (1 ≤ p)] in
/-- Direct `L^p` atoms are stable under scalars of norm at most one. -/
theorem directLpAtom_smul_mem_of_norm_le_one
    (A : LpAtomFamily G s p) (Q : WeakGridCell G)
    {c : ℂ} (hc : ‖c‖ ≤ (1 : ℝ))
    {φ : Lp ℂ p G.measure} (hφ : φ ∈ A.atoms Q) :
    c • φ ∈ A.atoms Q := by
  classical
  by_cases hczero : c = 0
  · subst hczero
    simpa using directLpAtom_zero_mem A Q
  let σ : ℂ := (‖c‖ : ℂ)⁻¹ * c
  have hnormσ : ‖σ‖ = (1 : ℝ) := by
    have hnorm_pos : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hczero
    simp [σ, norm_inv, hnorm_pos]
  have hσφ : σ • φ ∈ A.atoms Q :=
    A.atoms_phase_invariant Q φ σ hφ hnormσ
  have hcombo :
      (‖c‖ : ℝ) • (σ • φ) + (1 - ‖c‖ : ℝ) •
        (0 : Lp ℂ p G.measure) ∈ A.atoms Q := by
    exact (convex_iff_add_mem.mp (A.atoms_convex Q)) hσφ (directLpAtom_zero_mem A Q)
      (norm_nonneg c) (sub_nonneg.mpr hc) (by ring)
  convert hcombo using 1
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  have hnorm_pos : (‖c‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hczero
  simp [σ, hnorm_pos]

omit [Fact (1 ≤ p)] in
/-- Normalize a coefficient to a phase and apply it to a direct `L^p` atom. -/
noncomputable def directLpPhaseAtom
    (_A : LpAtomFamily G s p) (_Q : WeakGridCell G)
    (c : ℂ) (φ : Lp ℂ p G.measure) : Lp ℂ p G.measure :=
  if c = 0 then 0 else ((‖c‖ : ℂ)⁻¹ * c) • φ

omit [Fact (1 ≤ p)] in
/-- The phase-normalized direct `L^p` atom remains in the atom set. -/
theorem directLpPhaseAtom_mem
    (A : LpAtomFamily G s p) (Q : WeakGridCell G)
    (c : ℂ) {φ : Lp ℂ p G.measure} (hφ : φ ∈ A.atoms Q) :
    directLpPhaseAtom A Q c φ ∈ A.atoms Q := by
  classical
  by_cases hc : c = 0
  · simp [directLpPhaseAtom, hc, directLpAtom_zero_mem A Q]
  · have hnorm_pos : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    rw [directLpPhaseAtom, if_neg hc]
    refine A.atoms_phase_invariant Q φ ((‖c‖ : ℂ)⁻¹ * c) hφ ?_
    simp [norm_inv, hnorm_pos]

omit [Fact (1 ≤ p)] in
/-- Multiplying the phase-normalized atom by the coefficient norm recovers the scalar multiple. -/
theorem norm_smul_directLpPhaseAtom
    (A : LpAtomFamily G s p) (Q : WeakGridCell G)
    (c : ℂ) (φ : Lp ℂ p G.measure) :
    (‖c‖ : ℝ) • directLpPhaseAtom A Q c φ = c • φ := by
  classical
  by_cases hc : c = 0
  · simp [directLpPhaseAtom, hc]
  · rw [directLpPhaseAtom, if_neg hc, RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_smul]
    congr 1
    have hnorm_pos : (‖c‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr hc
    simp [hnorm_pos]

omit [Fact (1 ≤ p)] in
/-- A small linear combination of two direct `L^p` atoms is again an atom. -/
theorem directLpAtom_add_combo_mem_of_norm_add_le_one
    (A : LpAtomFamily G s p) (Q : WeakGridCell G)
    {c d : ℂ} (hcd : ‖c‖ + ‖d‖ ≤ (1 : ℝ))
    {φ ψ : Lp ℂ p G.measure}
    (hφ : φ ∈ A.atoms Q) (hψ : ψ ∈ A.atoms Q) :
    c • φ + d • ψ ∈ A.atoms Q := by
  classical
  let w : Fin 3 → ℝ := fun i =>
    if i = 0 then ‖c‖ else if i = 1 then ‖d‖ else 1 - ‖c‖ - ‖d‖
  let z : Fin 3 → Lp ℂ p G.measure := fun i =>
    if i = 0 then directLpPhaseAtom A Q c φ
    else if i = 1 then directLpPhaseAtom A Q d ψ
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
    · simp [z, directLpPhaseAtom_mem A Q c hφ]
    · simp [z, directLpPhaseAtom_mem A Q d hψ]
    · simp [z, directLpAtom_zero_mem A Q]
  have hsum := (A.atoms_convex Q).sum_mem hw_nonneg hw_sum hz_mem
  convert hsum using 1
  simp [w, z, Fin.sum_univ_three, norm_smul_directLpPhaseAtom A Q c φ,
    norm_smul_directLpPhaseAtom A Q d ψ]

omit [Fact (1 ≤ p)] in
/--
Repackage a sum of two coefficient-times-direct-atom terms as one nonnegative
coefficient times a single direct atom on the same cell.
-/
theorem directLpAtom_add_repackage
    (A : LpAtomFamily G s p) (Q : WeakGridCell G)
    (c d : ℂ) {φ ψ : Lp ℂ p G.measure}
    (hφ : φ ∈ A.atoms Q) (hψ : ψ ∈ A.atoms Q) :
    ∃ θ : Lp ℂ p G.measure,
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
    refine ⟨0, directLpAtom_zero_mem A Q, ?_⟩
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
      directLpAtom_add_combo_mem_of_norm_add_le_one A Q hnorm_add hφ hψ
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

namespace LpLevelBlock

/-- Addition of direct `L^p` level blocks, reusing one atom per cell. -/
noncomputable def add (A : LpAtomFamily G s p) {k : ℕ}
    (B C : LpLevelBlock A k) : LpLevelBlock A k where
  coeff := fun Q => ((‖B.coeff Q‖ + ‖C.coeff Q‖ : ℝ) : ℂ)
  atom := fun Q =>
    Classical.choose
      (directLpAtom_add_repackage A (levelCellToWeakGridCell G k Q)
        (B.coeff Q) (C.coeff Q) (B.atom_mem Q) (C.atom_mem Q))
  atom_mem := fun Q =>
    (Classical.choose_spec
      (directLpAtom_add_repackage A (levelCellToWeakGridCell G k Q)
        (B.coeff Q) (C.coeff Q) (B.atom_mem Q) (C.atom_mem Q))).1

omit [Fact (1 ≤ p)] in
/-- The atom chosen for the direct sum block has the expected scalar identity. -/
theorem add_atom_spec (A : LpAtomFamily G s p) {k : ℕ}
    (B C : LpLevelBlock A k) (Q : LevelCell G k) :
    ((‖B.coeff Q‖ + ‖C.coeff Q‖ : ℝ) : ℂ) • (add A B C).atom Q =
      B.coeff Q • B.atom Q + C.coeff Q • C.atom Q :=
  (Classical.choose_spec
    (directLpAtom_add_repackage A (levelCellToWeakGridCell G k Q)
      (B.coeff Q) (C.coeff Q) (B.atom_mem Q) (C.atom_mem Q))).2

omit [Fact (1 ≤ p)] in
/-- The direct `L^p` cell term of a sum block is the sum of the two cell terms. -/
theorem add_term (A : LpAtomFamily G s p) {k : ℕ}
    (B C : LpLevelBlock A k) (Q : LevelCell G k) :
    (add A B C).term A Q = B.term A Q + C.term A Q := by
  exact add_atom_spec A B C Q

omit [Fact (1 ≤ p)] in
/-- Evaluating a direct sum block in `L^p` gives the sum of represented blocks. -/
@[simp]
theorem add_toLp (A : LpAtomFamily G s p) {k : ℕ}
    (B C : LpLevelBlock A k) :
    (add A B C).toLp A = B.toLp A + C.toLp A := by
  simp [toLp, add_term A B C, Finset.sum_add_distrib]

end LpLevelBlock

omit [Fact (1 ≤ p)] in
/-- Additive closure of direct `L^p` level-block sets. -/
theorem add_mem_LpLevelBlockSet (A : LpAtomFamily G s p) (k : ℕ)
    {x y : Lp ℂ p G.measure} :
    x ∈ LpLevelBlockSet A k → y ∈ LpLevelBlockSet A k →
      x + y ∈ LpLevelBlockSet A k := by
  intro hx hy
  rcases hx with ⟨B, rfl⟩
  rcases hy with ⟨C, rfl⟩
  exact ⟨LpLevelBlock.add A B C, by simp⟩

namespace DirectLpGridRepresentation

/-- Representation-level addition for direct `L^p` atomic representations. -/
noncomputable def add
    {A : LpAtomFamily G s p} {g h : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g)
    (S : DirectLpGridRepresentation A h) :
    DirectLpGridRepresentation A (g + h) where
  block := fun k => LpLevelBlock.add A (R.block k) (S.block k)
  hasSum := by
    simpa [LpLevelBlock.add_toLp] using R.hasSum.add S.hasSum

/-- The block of a direct sum representation evaluates levelwise to the sum of blocks. -/
@[simp]
theorem add_block_toLp
    {A : LpAtomFamily G s p} {g h : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g)
    (S : DirectLpGridRepresentation A h) (k : ℕ) :
    ((add R S).block k).toLp A = (R.block k).toLp A + (S.block k).toLp A := by
  simp [add]

/-- Levelwise Minkowski inequality for direct representation coefficient powers. -/
theorem add_levelCoeffPower_rpow_inv_le
    {A : LpAtomFamily G s p} {g h : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g)
    (S : DirectLpGridRepresentation A h) (k : ℕ) :
    ((add R S).levelCoeffPower k) ^ (1 / p.toReal)
      ≤ (R.levelCoeffPower k) ^ (1 / p.toReal) +
          (S.levelCoeffPower k) ^ (1 / p.toReal) := by
  have hsum_add :
      ∑ Q : LevelCell G k, ‖((add R S).block k).coeff Q‖ ^ p.toReal
        = ∑ Q : LevelCell G k,
            (‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖) ^ p.toReal := by
    refine Finset.sum_congr rfl ?_
    intro Q hQ
    have hnn : 0 ≤ ‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    change ‖((‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖ : ℝ) : ℂ)‖ ^
        p.toReal =
      (‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖) ^ p.toReal
    rw [Complex.norm_real, Real.norm_of_nonneg hnn]
  rw [levelCoeffPower, hsum_add]
  simpa [levelCoeffPower] using
    (Real.Lp_add_le_of_nonneg
      (s := (Finset.univ : Finset (LevelCell G k)))
      (p := p.toReal)
      (f := fun Q => ‖(R.block k).coeff Q‖)
      (g := fun Q => ‖(S.block k).coeff Q‖)
      ((ENNReal.dichotomy p).resolve_left A.p_ne_top)
      (by intro Q hQ; exact norm_nonneg _)
      (by intro Q hQ; exact norm_nonneg _))

/-- Finite coefficient cost is preserved under addition of direct `L^p` representations. -/
theorem add_finitePQCost
    {A : LpAtomFamily G s p} {q : ℝ≥0∞} {g h : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g)
    (S : DirectLpGridRepresentation A h)
    [Fact (1 ≤ q)]
    (hRfin : FinitePQCost q R)
    (hSfin : FinitePQCost q S) :
    FinitePQCost q (add R S) := by
  by_cases hq : q = ∞
  · have hRbdd : BddAbove (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [FinitePQCost, hq] using hRfin
    have hSbdd : BddAbove (Set.range fun k => (S.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [FinitePQCost, hq] using hSfin
    rcases hRbdd with ⟨CR, hCR⟩
    rcases hSbdd with ⟨CS, hCS⟩
    have hBdd : BddAbove
        (Set.range fun k => ((add R S).levelCoeffPower k) ^ (1 / p.toReal)) := by
      refine ⟨CR + CS, ?_⟩
      rintro x ⟨k, rfl⟩
      have hsum_add :
          ∑ Q : LevelCell G k, ‖((add R S).block k).coeff Q‖ ^ p.toReal
            = ∑ Q : LevelCell G k,
                (‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖) ^ p.toReal := by
        refine Finset.sum_congr rfl ?_
        intro Q hQ
        have hnn : 0 ≤ ‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖ :=
          add_nonneg (norm_nonneg _) (norm_nonneg _)
        change ‖((‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖ : ℝ) : ℂ)‖ ^
            p.toReal =
          (‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖) ^ p.toReal
        rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      have hk :
          ((add R S).levelCoeffPower k) ^ (1 / p.toReal)
            ≤ (R.levelCoeffPower k) ^ (1 / p.toReal) +
                (S.levelCoeffPower k) ^ (1 / p.toReal) := by
        rw [levelCoeffPower, hsum_add]
        simpa [levelCoeffPower] using
          (Real.Lp_add_le_of_nonneg
            (s := (Finset.univ : Finset (LevelCell G k)))
            (p := p.toReal)
            (f := fun Q => ‖(R.block k).coeff Q‖)
            (g := fun Q => ‖(S.block k).coeff Q‖)
            ((ENNReal.dichotomy p).resolve_left A.p_ne_top)
            (by intro Q hQ; exact norm_nonneg _)
            (by intro Q hQ; exact norm_nonneg _))
      exact le_trans hk (add_le_add (hCR ⟨k, rfl⟩) (hCS ⟨k, rfl⟩))
    simpa [FinitePQCost, hq] using hBdd
  · have hsum :
        Summable (fun k => ((add R S).levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
      have hRq : Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
        simpa [FinitePQCost, hq] using hRfin
      have hSq : Summable (fun k => (S.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
        simpa [FinitePQCost, hq] using hSfin
      let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
      let b : ℕ → ℝ := fun k => (S.levelCoeffPower k) ^ (1 / p.toReal)
      let d : ℕ → ℝ := fun k => ((add R S).levelCoeffPower k) ^ (1 / p.toReal)
      have hq1 : 1 ≤ q.toReal := (ENNReal.dichotomy q).resolve_left hq
      have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
      have ha_nonneg : ∀ k, 0 ≤ a k := by
        intro k
        dsimp [a]
        exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
      have hb_nonneg : ∀ k, 0 ≤ b k := by
        intro k
        dsimp [b]
        exact Real.rpow_nonneg (S.levelCoeffPower_nonneg k) _
      have hd_nonneg : ∀ k, 0 ≤ d k := by
        intro k
        dsimp [d]
        exact Real.rpow_nonneg ((add R S).levelCoeffPower_nonneg k) _
      have hRq' : Summable (fun k => (a k) ^ q.toReal) := by
        refine hRq.congr ?_
        intro k
        rw [show q.toReal / p.toReal = (1 / p.toReal) * q.toReal by
          field_simp [hp_pos.ne']]
        rw [Real.rpow_mul (R.levelCoeffPower_nonneg k)]
      have hSq' : Summable (fun k => (b k) ^ q.toReal) := by
        refine hSq.congr ?_
        intro k
        rw [show q.toReal / p.toReal = (1 / p.toReal) * q.toReal by
          field_simp [hp_pos.ne']]
        rw [Real.rpow_mul (S.levelCoeffPower_nonneg k)]
      have hsum_ab := Real.summable_Lp_add_of_nonneg hq1 ha_nonneg hb_nonneg hRq' hSq'
      have hdk : ∀ k, d k ≤ a k + b k := by
        intro k
        have hsum_add :
            ∑ Q : LevelCell G k, ‖((add R S).block k).coeff Q‖ ^ p.toReal
              = ∑ Q : LevelCell G k,
                  (‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖) ^ p.toReal := by
          refine Finset.sum_congr rfl ?_
          intro Q hQ
          have hnn : 0 ≤ ‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖ :=
            add_nonneg (norm_nonneg _) (norm_nonneg _)
          change ‖((‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖ : ℝ) : ℂ)‖ ^
              p.toReal =
            (‖(R.block k).coeff Q‖ + ‖(S.block k).coeff Q‖) ^ p.toReal
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
        dsimp [d, a, b]
        rw [levelCoeffPower, hsum_add]
        simpa [levelCoeffPower] using
          (Real.Lp_add_le_of_nonneg
            (s := (Finset.univ : Finset (LevelCell G k)))
            (p := p.toReal)
            (f := fun Q => ‖(R.block k).coeff Q‖)
            (g := fun Q => ‖(S.block k).coeff Q‖)
            ((ENNReal.dichotomy p).resolve_left A.p_ne_top)
            (by intro Q hQ; exact norm_nonneg _)
            (by intro Q hQ; exact norm_nonneg _))
      have hdq_le :
          (fun k => (d k) ^ q.toReal) ≤ fun k => (a k + b k) ^ q.toReal := by
        intro k
        exact Real.rpow_le_rpow (hd_nonneg k) (hdk k) (by positivity)
      have hsum_dq := Summable.of_nonneg_of_le
        (by intro k; exact Real.rpow_nonneg (hd_nonneg k) _)
        hdq_le hsum_ab
      refine hsum_dq.congr ?_
      intro k
      rw [show q.toReal / p.toReal = (1 / p.toReal) * q.toReal by
        field_simp [hp_pos.ne']]
      rw [Real.rpow_mul ((add R S).levelCoeffPower_nonneg k)]
    simpa [FinitePQCost, hq] using hsum

/-- The direct representation coefficient gauge is nonnegative. -/
theorem pqCost_nonneg
    {A : LpAtomFamily G s p} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g) :
    0 ≤ pqCost (q := q) R := by
  unfold pqCost
  split_ifs with hq
  · refine Real.sSup_nonneg ?_
    rintro x ⟨k, rfl⟩
    exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
  · exact Real.rpow_nonneg
      (tsum_nonneg fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _) _

/-- Scaling a direct representation scales its `pqCost` by the scalar norm. -/
theorem pqCost_smul
    {A : LpAtomFamily G s p} {q : ℝ≥0∞} {g : Lp ℂ p G.measure}
    [Fact (1 ≤ q)]
    (c : ℂ) (R : DirectLpGridRepresentation A g) :
    pqCost (q := q) (smul c R) = ‖c‖ * pqCost (q := q) R := by
  have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  unfold pqCost
  split_ifs with hq
  · let f : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
    have hpoint :
        ∀ k, ((smul c R).levelCoeffPower k) ^ (1 / p.toReal) = ‖c‖ * f k := by
      intro k
      have hRnonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
      calc
        ((smul c R).levelCoeffPower k) ^ (1 / p.toReal)
            = (‖c‖ ^ p.toReal * R.levelCoeffPower k) ^ (1 / p.toReal) := by
                rw [smul_levelCoeffPower]
        _ = (‖c‖ ^ p.toReal) ^ (1 / p.toReal) *
              (R.levelCoeffPower k) ^ (1 / p.toReal) := by
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
  · have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have hterm :
        ∀ k,
          ((smul c R).levelCoeffPower k) ^ (q.toReal / p.toReal)
            = ‖c‖ ^ q.toReal * (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
      intro k
      have hRnonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
      calc
        ((smul c R).levelCoeffPower k) ^ (q.toReal / p.toReal)
            = (‖c‖ ^ p.toReal * R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
                rw [smul_levelCoeffPower]
        _ = (‖c‖ ^ p.toReal) ^ (q.toReal / p.toReal) *
              (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
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
          = (∑' k, ‖c‖ ^ q.toReal *
              (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
              congr 1
              exact tsum_congr hterm
      _ = (‖c‖ ^ q.toReal *
            (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal))) ^ (1 / q.toReal) := by
          rw [tsum_mul_left]
      _ = (‖c‖ ^ q.toReal) ^ (1 / q.toReal) *
            (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
          have htsum_nonneg :
              0 ≤ ∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal) :=
            tsum_nonneg fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
          rw [Real.mul_rpow (by positivity) htsum_nonneg]
      _ = ‖c‖ *
            (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
          have hcp : (‖c‖ ^ q.toReal) ^ (1 / q.toReal) = ‖c‖ := by
            simpa [one_div] using (Real.rpow_rpow_inv (norm_nonneg c) hq_pos.ne')
          rw [hcp]

/--
The direct representation coefficient gauge satisfies the triangle inequality
for finite-cost representations.
-/
theorem pqCost_triangle
    {A : LpAtomFamily G s p} {q : ℝ≥0∞} {g h : Lp ℂ p G.measure}
    [Fact (1 ≤ q)]
    (R : DirectLpGridRepresentation A g)
    (S : DirectLpGridRepresentation A h)
    (hRfin : FinitePQCost q R)
    (hSfin : FinitePQCost q S) :
    pqCost (q := q) (add R S) ≤ pqCost (q := q) R + pqCost (q := q) S := by
  have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  unfold pqCost
  split_ifs with hq
  · have hRbdd : BddAbove (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [FinitePQCost, hq] using hRfin
    have hSbdd : BddAbove (Set.range fun k => (S.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [FinitePQCost, hq] using hSfin
    apply csSup_le
      (Set.range_nonempty fun k => ((add R S).levelCoeffPower k) ^ (1 / p.toReal))
    rintro x ⟨k, rfl⟩
    exact le_trans (add_levelCoeffPower_rpow_inv_le R S k)
      (add_le_add (le_csSup hRbdd ⟨k, rfl⟩) (le_csSup hSbdd ⟨k, rfl⟩))
  · have hq1 : 1 ≤ q.toReal := (ENNReal.dichotomy q).resolve_left hq
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
    let b : ℕ → ℝ := fun k => (S.levelCoeffPower k) ^ (1 / p.toReal)
    let d : ℕ → ℝ := fun k => ((add R S).levelCoeffPower k) ^ (1 / p.toReal)
    have ha_nonneg : ∀ k, 0 ≤ a k := by
      intro k
      dsimp [a]
      exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
    have hb_nonneg : ∀ k, 0 ≤ b k := by
      intro k
      dsimp [b]
      exact Real.rpow_nonneg (S.levelCoeffPower_nonneg k) _
    have hd_nonneg : ∀ k, 0 ≤ d k := by
      intro k
      dsimp [d]
      exact Real.rpow_nonneg ((add R S).levelCoeffPower_nonneg k) _
    have hdk : ∀ k, d k ≤ a k + b k := by
      intro k
      exact add_levelCoeffPower_rpow_inv_le R S k
    have hRq : Summable (fun k => (a k) ^ q.toReal) := by
      have hRsum0 : Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
        simpa [FinitePQCost, hq] using hRfin
      refine hRsum0.congr ?_
      intro k
      rw [show q.toReal / p.toReal = (1 / p.toReal) * q.toReal by
        field_simp [hp_pos.ne']]
      rw [Real.rpow_mul (R.levelCoeffPower_nonneg k)]
    have hSq : Summable (fun k => (b k) ^ q.toReal) := by
      have hSsum0 : Summable (fun k => (S.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
        simpa [FinitePQCost, hq] using hSfin
      refine hSsum0.congr ?_
      intro k
      rw [show q.toReal / p.toReal = (1 / p.toReal) * q.toReal by
        field_simp [hp_pos.ne']]
      rw [Real.rpow_mul (S.levelCoeffPower_nonneg k)]
    have hsum_ab : Summable (fun k => (a k + b k) ^ q.toReal) :=
      Real.summable_Lp_add_of_nonneg hq1 ha_nonneg hb_nonneg hRq hSq
    have hdq_le :
        (fun k => (d k) ^ q.toReal) ≤ fun k => (a k + b k) ^ q.toReal := by
      intro k
      exact Real.rpow_le_rpow (hd_nonneg k) (hdk k) (le_of_lt hq_pos)
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
        (tsum_nonneg fun k => Real.rpow_nonneg (hd_nonneg k) _)
        htsum_le
        (one_div_nonneg.mpr (le_of_lt hq_pos))
    have hmid :
        (∑' k, (a k + b k) ^ q.toReal) ^ (1 / q.toReal)
          ≤ (∑' k, (a k) ^ q.toReal) ^ (1 / q.toReal)
            + (∑' k, (b k) ^ q.toReal) ^ (1 / q.toReal) :=
      Real.Lp_add_le_tsum_of_nonneg' hq1 ha_nonneg hb_nonneg hRq hSq
    have hsum_d :
        (∑' k, ((add R S).levelCoeffPower k) ^ (q.toReal / p.toReal))
          = ∑' k, (d k) ^ q.toReal := by
      apply tsum_congr
      intro k
      rw [show q.toReal / p.toReal = (1 / p.toReal) * q.toReal by
        field_simp [hp_pos.ne']]
      rw [Real.rpow_mul ((add R S).levelCoeffPower_nonneg k)]
    have hsum_R :
        (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal))
          = ∑' k, (a k) ^ q.toReal := by
      apply tsum_congr
      intro k
      rw [show q.toReal / p.toReal = (1 / p.toReal) * q.toReal by
        field_simp [hp_pos.ne']]
      rw [Real.rpow_mul (R.levelCoeffPower_nonneg k)]
    have hsum_S :
        (∑' k, (S.levelCoeffPower k) ^ (q.toReal / p.toReal))
          = ∑' k, (b k) ^ q.toReal := by
      apply tsum_congr
      intro k
      rw [show q.toReal / p.toReal = (1 / p.toReal) * q.toReal by
        field_simp [hp_pos.ne']]
      rw [Real.rpow_mul (S.levelCoeffPower_nonneg k)]
    calc
      (∑' k, ((add R S).levelCoeffPower k) ^ (q.toReal / p.toReal)) ^
          (1 / q.toReal)
          = (∑' k, (d k) ^ q.toReal) ^ (1 / q.toReal) := by rw [hsum_d]
      _ ≤ (∑' k, (a k + b k) ^ q.toReal) ^ (1 / q.toReal) := hleft
      _ ≤ (∑' k, (a k) ^ q.toReal) ^ (1 / q.toReal)
            + (∑' k, (b k) ^ q.toReal) ^ (1 / q.toReal) := hmid
      _ = (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)
            + (∑' k, (S.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
          rw [hsum_R, hsum_S]

end DirectLpGridRepresentation

/-- The zero vector has a direct `L^p` Besov-ish representation. -/
theorem directLpMemBesovish_zero (A : LpAtomFamily G s p) :
    DirectLpMemBesovish A q (0 : Lp ℂ p G.measure) := by
  exact ⟨DirectLpGridRepresentation.zero A⟩

/-- Direct `L^p` Besov-ish representations are closed under scalar multiplication. -/
theorem directLpMemBesovish_smul {A : LpAtomFamily G s p}
    (c : ℂ) {g : Lp ℂ p G.measure}
    (hg : DirectLpMemBesovish A q g) :
    DirectLpMemBesovish A q (c • g) := by
  rcases hg with ⟨R⟩
  exact ⟨DirectLpGridRepresentation.smul c R⟩

/-- Direct `L^p` Besov-ish representations are closed under addition. -/
theorem directLpMemBesovish_add {A : LpAtomFamily G s p}
    {g h : Lp ℂ p G.measure}
    (hg : DirectLpMemBesovish A q g) (hh : DirectLpMemBesovish A q h) :
    DirectLpMemBesovish A q (g + h) := by
  rcases hg with ⟨R⟩
  rcases hh with ⟨S⟩
  exact ⟨DirectLpGridRepresentation.add R S⟩

/-- The zero vector has a finite-cost direct `L^p` Besov-ish representation. -/
theorem directLpMemBesovishCoeffCost_zero
    (A : LpAtomFamily G s p) [Fact (1 ≤ q)] :
    DirectLpMemBesovishCoeffCost A q (0 : Lp ℂ p G.measure) := by
  exact ⟨DirectLpGridRepresentation.zero A,
    DirectLpGridRepresentation.zero_finitePQCost (A := A) (q := q)⟩

/-- Finite-cost direct `L^p` representations are closed under scalar multiplication. -/
theorem directLpMemBesovishCoeffCost_smul {A : LpAtomFamily G s p}
    (c : ℂ) {g : Lp ℂ p G.measure}
    (hg : DirectLpMemBesovishCoeffCost A q g) :
    DirectLpMemBesovishCoeffCost A q (c • g) := by
  rcases hg with ⟨R, hRfin⟩
  exact ⟨DirectLpGridRepresentation.smul c R,
    DirectLpGridRepresentation.smul_finitePQCost (A := A) (q := q) c hRfin⟩

/-- Finite-cost direct `L^p` Besov-ish representations are closed under addition. -/
theorem directLpMemBesovishCoeffCost_add {A : LpAtomFamily G s p}
    {g h : Lp ℂ p G.measure}
    [Fact (1 ≤ q)]
    (hg : DirectLpMemBesovishCoeffCost A q g)
    (hh : DirectLpMemBesovishCoeffCost A q h) :
    DirectLpMemBesovishCoeffCost A q (g + h) := by
  rcases hg with ⟨R, hRfin⟩
  rcases hh with ⟨S, hSfin⟩
  exact ⟨DirectLpGridRepresentation.add R S,
    DirectLpGridRepresentation.add_finitePQCost (A := A) (q := q) R S hRfin hSfin⟩

/--
The direct `L^p` Besov-ish space as a complex linear subspace of ambient `L^p`.

Its elements are exactly the ambient `L^p` classes admitting a finite-cost
direct atomic representation.
-/
def DirectLpBesovishSpace (A : LpAtomFamily G s p) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] :
    Submodule ℂ (Lp ℂ p G.measure) where
  carrier := {g | DirectLpMemBesovishCoeffCost A q g}
  zero_mem' := directLpMemBesovishCoeffCost_zero (A := A) (q := q)
  add_mem' := by
    intro g h hg hh
    exact directLpMemBesovishCoeffCost_add (A := A) (q := q) hg hh
  smul_mem' := by
    intro c g hg
    exact directLpMemBesovishCoeffCost_smul (A := A) (q := q) c hg

/--
The direct Besov-ish space generated by all supported `L^p` atoms with
`μ(Q)^s` size bound.
-/
noncomputable def LpSizeBesovishSpace
    (G : WeakGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) [Fact (1 ≤ p)] (hp_top : p ≠ ∞) [Fact (1 ≤ q)] :
    Submodule ℂ (Lp ℂ p G.measure) :=
  DirectLpBesovishSpace (lpSizeAtomFamily G s p hs hp_top) q

namespace DirectLpBesovishSpace

/-- Candidate upper bounds for the direct `pqCost` gauge of `x`. -/
def pqCostUpperSet
    (A : LpAtomFamily G s p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (x : DirectLpBesovishSpace A q) : Set ℝ :=
  { c | ∃ R : DirectLpGridRepresentation A (x : Lp ℂ p G.measure),
      DirectLpGridRepresentation.FinitePQCost q R ∧
      DirectLpGridRepresentation.pqCost (q := q) R ≤ c }

/-- Infimum gauge induced by direct `pqCost` on admissible representations of `x`. -/
noncomputable def pqPseudoNorm
    (A : LpAtomFamily G s p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (x : DirectLpBesovishSpace A q) : ℝ :=
  sInf (pqCostUpperSet A q x)

/--
`Norm_Costpq(g)` is the infimum of the `(p,q)` costs of all admissible
finite-cost direct `L^p` representations of `g`.
-/
noncomputable def Norm_Costpq
    (A : LpAtomFamily G s p) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (g : DirectLpBesovishSpace A q) : ℝ :=
  pqPseudoNorm A q g

variable {A : LpAtomFamily G s p} {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Global hypothesis: every direct Besov-ish vector admits a finite-cost representation. -/
def HasFiniteCostRepresentations (A : LpAtomFamily G s p) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] : Prop :=
  ∀ x : DirectLpBesovishSpace A q,
    ∃ R : DirectLpGridRepresentation A (x : Lp ℂ p G.measure),
      DirectLpGridRepresentation.FinitePQCost q R

/--
Every element of `DirectLpBesovishSpace A q` already carries a finite-cost
direct representation by definition.
-/
theorem hasFiniteCostRepresentations (A : LpAtomFamily G s p) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] :
    HasFiniteCostRepresentations (A := A) q := by
  intro x
  have hx := x.property
  change DirectLpMemBesovishCoeffCost A q (x : Lp ℂ p G.measure) at hx
  exact hx

/-- The set of admissible direct `pqCost` upper bounds is nonempty. -/
theorem pqCostUpperSet_nonempty
    (hA : HasFiniteCostRepresentations (A := A) q)
    (x : DirectLpBesovishSpace A q) :
    (pqCostUpperSet A q x).Nonempty := by
  rcases hA x with ⟨R, hRfin⟩
  exact ⟨DirectLpGridRepresentation.pqCost (q := q) R, ⟨R, hRfin, le_rfl⟩⟩

/-- Every direct `pqCost` upper set is bounded below by `0`. -/
theorem pqCostUpperSet_bddBelow
    (x : DirectLpBesovishSpace A q) :
    BddBelow (pqCostUpperSet A q x) := by
  refine ⟨0, ?_⟩
  intro c hc
  rcases hc with ⟨R, -, hRc⟩
  exact le_trans (DirectLpGridRepresentation.pqCost_nonneg R) hRc

/-- The direct gauge `Norm_Costpq` is nonnegative. -/
theorem Norm_Costpq_nonneg
    (hA : HasFiniteCostRepresentations (A := A) q)
    (g : DirectLpBesovishSpace A q) :
    0 ≤ Norm_Costpq A q g := by
  unfold Norm_Costpq pqPseudoNorm
  refine le_csInf (pqCostUpperSet_nonempty (A := A) (q := q) hA g) ?_
  intro c hc
  rcases hc with ⟨R, -, hRc⟩
  exact le_trans (DirectLpGridRepresentation.pqCost_nonneg R) hRc

/-- The infimum gauge is bounded above by the cost of any admissible representation. -/
theorem Norm_Costpq_le_cost
    (g : DirectLpBesovishSpace A q)
    (R : DirectLpGridRepresentation A (g : Lp ℂ p G.measure))
    (hRfin : DirectLpGridRepresentation.FinitePQCost q R) :
    Norm_Costpq A q g ≤ DirectLpGridRepresentation.pqCost (q := q) R := by
  unfold Norm_Costpq pqPseudoNorm
  exact csInf_le (pqCostUpperSet_bddBelow (A := A) (q := q) g) ⟨R, hRfin, le_rfl⟩

/--
For every `ε > 0`, there is an admissible direct representation whose
`(p,q)` cost is within `ε` of `Norm_Costpq`.
-/
theorem exists_cost_lt_Norm_Costpq_add
    (hA : HasFiniteCostRepresentations (A := A) q)
    (g : DirectLpBesovishSpace A q) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : DirectLpGridRepresentation A (g : Lp ℂ p G.measure),
      DirectLpGridRepresentation.FinitePQCost q R ∧
      DirectLpGridRepresentation.pqCost (q := q) R < Norm_Costpq A q g + ε := by
  have hlt : sInf (pqCostUpperSet A q g) < sInf (pqCostUpperSet A q g) + ε :=
    lt_add_of_pos_right _ hε
  rcases exists_lt_of_csInf_lt
      (pqCostUpperSet_nonempty (A := A) (q := q) hA g) hlt with
    ⟨c, hc, hclt⟩
  rcases hc with ⟨R, hRfin, hRc⟩
  refine ⟨R, hRfin, ?_⟩
  exact lt_of_le_of_lt hRc (by simpa [pqPseudoNorm, Norm_Costpq] using hclt)

/-- The direct gauge `Norm_Costpq` satisfies the triangle inequality. -/
theorem Norm_Costpq_add_le
    (hA : HasFiniteCostRepresentations (A := A) q)
    (x y : DirectLpBesovishSpace A q) :
    Norm_Costpq A q (x + y) ≤ Norm_Costpq A q x + Norm_Costpq A q y := by
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases exists_cost_lt_Norm_Costpq_add (A := A) (q := q) hA x hε2 with
    ⟨Rx, hRxfin, hRxlt⟩
  rcases exists_cost_lt_Norm_Costpq_add (A := A) (q := q) hA y hε2 with
    ⟨Ry, hRyfin, hRylt⟩
  let Rsum := DirectLpGridRepresentation.add (A := A) Rx Ry
  have h0 :
      Norm_Costpq A q (x + y) ≤ DirectLpGridRepresentation.pqCost (q := q) Rsum :=
    Norm_Costpq_le_cost (A := A) (q := q) (g := x + y) Rsum
      (DirectLpGridRepresentation.add_finitePQCost
        (A := A) (q := q) Rx Ry hRxfin hRyfin)
  have h1 :
      DirectLpGridRepresentation.pqCost (q := q) Rsum
        ≤ DirectLpGridRepresentation.pqCost (q := q) Rx +
            DirectLpGridRepresentation.pqCost (q := q) Ry :=
    DirectLpGridRepresentation.pqCost_triangle
      (A := A) (q := q) Rx Ry hRxfin hRyfin
  have h2 :
      DirectLpGridRepresentation.pqCost (q := q) Rx +
          DirectLpGridRepresentation.pqCost (q := q) Ry
        ≤ (Norm_Costpq A q x + ε / 2) + (Norm_Costpq A q y + ε / 2) :=
    add_le_add (le_of_lt hRxlt) (le_of_lt hRylt)
  calc
    Norm_Costpq A q (x + y)
        ≤ DirectLpGridRepresentation.pqCost (q := q) Rsum := h0
    _ ≤ DirectLpGridRepresentation.pqCost (q := q) Rx +
          DirectLpGridRepresentation.pqCost (q := q) Ry := h1
    _ ≤ (Norm_Costpq A q x + ε / 2) + (Norm_Costpq A q y + ε / 2) := h2
    _ = Norm_Costpq A q x + Norm_Costpq A q y + ε := by ring_nf

/-- The direct gauge `Norm_Costpq` is homogeneous up to `≤`. -/
theorem Norm_Costpq_smul_le
    (hA : HasFiniteCostRepresentations (A := A) q)
    (c : ℂ) (x : DirectLpBesovishSpace A q) :
    Norm_Costpq A q (c • x) ≤ ‖c‖ * Norm_Costpq A q x := by
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hden : 0 < ‖c‖ + 1 := by linarith [norm_nonneg c]
  have hδ : 0 < ε / (‖c‖ + 1) := by positivity
  rcases exists_cost_lt_Norm_Costpq_add (A := A) (q := q) hA x hδ with
    ⟨Rx, hRxfin, hRxlt⟩
  let Rc := DirectLpGridRepresentation.smul (A := A) c Rx
  have h0 :
      Norm_Costpq A q (c • x) ≤ DirectLpGridRepresentation.pqCost (q := q) Rc :=
    Norm_Costpq_le_cost (A := A) (q := q) (g := c • x) Rc
      (DirectLpGridRepresentation.smul_finitePQCost (A := A) (q := q) c hRxfin)
  have h1 :
      DirectLpGridRepresentation.pqCost (q := q) Rc =
        ‖c‖ * DirectLpGridRepresentation.pqCost (q := q) Rx :=
    DirectLpGridRepresentation.pqCost_smul (A := A) (q := q) c Rx
  have h2 :
      DirectLpGridRepresentation.pqCost (q := q) Rx
        ≤ Norm_Costpq A q x + ε / (‖c‖ + 1) :=
    le_of_lt hRxlt
  have h3 :
      ‖c‖ * DirectLpGridRepresentation.pqCost (q := q) Rx
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
        ≤ DirectLpGridRepresentation.pqCost (q := q) Rc := h0
    _ = ‖c‖ * DirectLpGridRepresentation.pqCost (q := q) Rx := h1
    _ ≤ ‖c‖ * (Norm_Costpq A q x + ε / (‖c‖ + 1)) := h3
    _ = ‖c‖ * Norm_Costpq A q x + ‖c‖ * (ε / (‖c‖ + 1)) := by ring
    _ ≤ ‖c‖ * Norm_Costpq A q x + ε := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right h4 (‖c‖ * Norm_Costpq A q x)

/-- The direct gauge `Norm_Costpq` is exactly homogeneous. -/
theorem Norm_Costpq_smul_eq
    (hA : HasFiniteCostRepresentations (A := A) q)
    (c : ℂ) (x : DirectLpBesovishSpace A q) :
    Norm_Costpq A q (c • x) = ‖c‖ * Norm_Costpq A q x := by
  refine le_antisymm
    (Norm_Costpq_smul_le (A := A) (q := q) hA c x) ?_
  by_cases hc : c = 0
  · subst c
    simpa using Norm_Costpq_nonneg (A := A) (q := q) hA ((0 : ℂ) • x)
  · have hcx : c⁻¹ • (c • x) = x := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hle :
        Norm_Costpq A q x ≤ ‖c⁻¹‖ * Norm_Costpq A q (c • x) := by
      simpa [hcx] using
        Norm_Costpq_smul_le (A := A) (q := q) hA c⁻¹ (c • x)
    have hc_norm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hmul :
        ‖c‖ * Norm_Costpq A q x
          ≤ ‖c‖ * (‖c⁻¹‖ * Norm_Costpq A q (c • x)) :=
      mul_le_mul_of_nonneg_left hle (norm_nonneg c)
    have hnorm_inv : ‖c‖ * ‖c⁻¹‖ = (1 : ℝ) := by
      rw [norm_inv, mul_inv_cancel₀ (ne_of_gt hc_norm_pos)]
    calc
      ‖c‖ * Norm_Costpq A q x
          ≤ ‖c‖ * (‖c⁻¹‖ * Norm_Costpq A q (c • x)) := hmul
      _ = Norm_Costpq A q (c • x) := by
          rw [← mul_assoc, hnorm_inv, one_mul]

end DirectLpBesovishSpace

end

end WeakGridSpace
