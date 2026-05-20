import BesovSpacesGoodGrid.WeakGridAtomsDefinition
import BesovSpacesGoodGrid.WeakGridBesovishSpaces
import BesovSpacesGoodGrid.WeakGridCompletenessBesovishSpaces
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order





variable {α : Type*} [MeasurableSpace α]

namespace WeakGridSpace

open scoped ENNReal BigOperators Topology
open MeasureTheory Filter

attribute [local instance] Classical.propDecidable



noncomputable section

variable {G : WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
variable [Fact (1 ≤ p)] [Fact (1 ≤ u)] [Fact (1 ≤ q)]



/-- Source coefficient `p`-power for the source grid `GIn`. -/
noncomputable def CoeffPLevel
    (G : WeakGridSpace (α := α))
    (c : (i : ℕ) → LevelCell G i → ℂ) (i : ℕ) : ℝ :=
  ∑ Q : LevelCell G i, ‖c i Q‖ ^ p.toReal

/-- Source coefficient `(p,q)` cost for the source grid `GIn`. -/
noncomputable def  CoeffPQCost
    (G : WeakGridSpace (α := α))
    (c : (i : ℕ) → LevelCell G i → ℂ) : ℝ :=
  if q = ∞ then
    sSup (Set.range fun i =>
      (CoeffPLevel  (p := p) G c i) ^ (1 / p.toReal))
  else
    (∑' i, (CoeffPLevel  (p := p) G c i) ^
      (q.toReal / p.toReal)) ^ (1 / q.toReal)

/--
Finiteness of the source coefficient `(p,q)` cost, matching
`(∑ᵢ (∑_{Q∈𝓖ⁱ}|c_Q|^p)^{q/p})^{1/q} < ∞`.
-/
def CoeffFinitePQCost
    (G : WeakGridSpace (α := α))
    (c : (i : ℕ) → LevelCell G i → ℂ) : Prop :=
  if q = ∞ then
    BddAbove (Set.range fun i =>
      (CoeffPLevel  (p := p) G c i) ^ (1 / p.toReal))
  else
    Summable fun i =>
      (CoeffPLevel  (p := p) G c i) ^ (q.toReal / p.toReal)

def AlmostLinearSequence (k : ℕ → ℕ) : Prop :=
  ∃ (A B : NNReal) (r : NNReal), r > 0 ∧ ∀ i : ℕ,
    (k i : NNReal) ≤ r * (i : NNReal) + B ∧
    r * (i : NNReal) + A ≤ (k i : NNReal)

lemma almostLinearSequence_finite_le_level
    {k : ℕ → ℕ} (hk : AlmostLinearSequence k) (j : ℕ) :
    {i : ℕ | k i ≤ j}.Finite := by
  classical
  obtain ⟨A, B, r, hr, hk_bound⟩ := hk
  let M : ℕ := Nat.ceil (((j : NNReal) / r)) + 1
  refine (Set.finite_lt_nat M).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  have hlower : r * (i : NNReal) + A ≤ (k i : NNReal) := (hk_bound i).2
  have hkj : (k i : NNReal) ≤ (j : NNReal) := by exact_mod_cast hi
  have hri_le_j : r * (i : NNReal) ≤ (j : NNReal) := by
    calc
      r * (i : NNReal) ≤ r * (i : NNReal) + A := le_add_of_nonneg_right A.2
      _ ≤ (k i : NNReal) := hlower
      _ ≤ (j : NNReal) := hkj
  have hi_div : (i : NNReal) ≤ (j : NNReal) / r := by
    rw [le_div_iff₀ hr]
    simpa [mul_comm] using hri_le_j
  have hi_ceil_nn : (i : NNReal) ≤ (Nat.ceil ((j : NNReal) / r) : ℕ) :=
    hi_div.trans (Nat.le_ceil ((j : NNReal) / r))
  have hi_ceil : i ≤ Nat.ceil ((j : NNReal) / r) := by
    exact_mod_cast hi_ceil_nn
  omega

def PartialSumLevels
    (G W : WeakGridSpace (α := α))
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) : Lp ℂ p W.measure :=
  ∑ i ∈ Finset.range N, (G.grid.partitions i).attach.sum (fun Q => c i Q • h i Q)




def RepresentationWsubGandALS
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (_hk : AlmostLinearSequence k)
    (lam : ℝ) (_hlam_pos : 0 < lam) (_hlam_lt : lam < 1)
    (C : ℝ) (_hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    : Prop :=
  ∀ i : ℕ, ∀ Q : LevelCell G i,
      CoeffFinitePQCost (p := p) (q := q) W (fun j S => ((R i Q).block j).coeff S) ∧
      (∀ j : ℕ, ∀ S : LevelCell W j,
        (¬ S.1 ⊆ Q.1 → ((R i Q).block j).coeff S = 0) ∧
        (j < k i → ((R i Q).block j).coeff S = 0)) ∧
      ∀ j : ℕ, k i ≤ j → ((R i Q).levelCoeffPower j) ≤ C * lam ^ (j - k i)

/-- Transmutation coefficient for `P ∈ W^j`:
    `m_{P,N} = ∑_{i<N} ∑_{Q ∈ G^i, P ⊆ Q} |c_Q · s_{P,Q}|`
    where `s_{P,Q} = ((R i Q).block j).coeff P`. -/
noncomputable def TransmutationCoeff
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) {j : ℕ} (P : LevelCell W j) : ℝ :=
  ∑ i ∈ Finset.range N,
    ∑ Q ∈ (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1),
      ‖c i Q * ((R i Q).block j).coeff P‖

/-- Transmutation atom `d_{P,N}` for `P ∈ W^j`: the normalised convex combination
    of the atoms `b_{P,Q}` weighted by `c_Q · s_{P,Q}`.
    When `m_{P,N} = 0` it is defined to be `0`.
    Otherwise `d_{P,N} = (1/m_{P,N}) · ∑_{i<N} ∑_{Q∈G^i,P⊆Q} c_Q·s_{P,Q}·b_{P,Q}`. -/
noncomputable def TransmutationAtom
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) {j : ℕ} (P : LevelCell W j) : Lp ℂ p W.measure :=
  let m := TransmutationCoeff G W AW h R c N P
  let num := ∑ i ∈ Finset.range N,
    ∑ Q ∈ (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1),
      c i Q • ((R i Q).block j).term AW P
  if m = 0 then 0 else (m : ℂ)⁻¹ • num







/-- The transmutation atom `d_{P,N}` as an element of the local Banach space
    `AW.localSpace (levelCellToWeakGridCell W j P)`.
    It is the normalised complex combination
    `(1/m) · ∑_{i<N} ∑_{Q∈Gⁱ,P⊆Q} c_Q · s_{P,Q} · b_{P,Q}`
    computed *inside* the local space, where `b_{P,Q}` is the atom stored in
    `(R i Q).block j` and `s_{P,Q} = ((R i Q).block j).coeff P`.
    When `m = 0` it is defined to be `0`. -/
noncomputable def TransmutationAtomLocal
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) {j : ℕ} (P : LevelCell W j) :
    (AW.localSpace (levelCellToWeakGridCell W j P)).carrier :=
  let m := TransmutationCoeff G W AW h R c N P
  -- Flat (sigma) index set: pairs (level i, cell Q) with i < N and P ⊆ Q
  let FS : Finset (Σ i : ℕ, LevelCell G i) :=
    (Finset.range N).sigma
      (fun i => (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1))
  let num :=
    ∑ iQ ∈ FS,
      (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
        ((R iQ.1 iQ.2).block j).atom P
  if m = 0 then 0 else (m : ℂ)⁻¹ • num

/-- `TransmutationAtomLocal G W AW h R c N P` is an atom of `AW` on cell `P`.
    **Proof**: when `m = 0` the element is `0`, which is an atom
    (`atom_zero_mem`).  When `m ≠ 0` the element equals
    `∑ (c_Q · s_{P,Q} / m) · b_{P,Q}`,
    a weighted sum of AW-atoms with coefficient-norms summing to `1`;
    convexity of `AW.atoms P` (together with phase-invariance used inside
    `atom_finsum_mem`) shows the sum is still an atom. -/
theorem TransmutationAtomLocal_isAtom
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) {j : ℕ} (P : LevelCell W j) :
    AW.IsAtom (levelCellToWeakGridCell W j P)
      (TransmutationAtomLocal G W AW h R c N P) := by
  set Pg := levelCellToWeakGridCell W j P
  set m  := TransmutationCoeff G W AW h R c N P
  -- Local alias for the flat index set (same expression as in TransmutationAtomLocal)
  let FS : Finset (Σ i : ℕ, LevelCell G i) :=
    (Finset.range N).sigma
      (fun i => (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1))
  show TransmutationAtomLocal G W AW h R c N P ∈ AW.atoms Pg
  -- Rewrite using the explicit form of TransmutationAtomLocal (holds by rfl)
  have hdef : TransmutationAtomLocal G W AW h R c N P =
      if m = 0 then 0
      else (m : ℂ)⁻¹ • ∑ iQ ∈ FS,
        (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
          ((R iQ.1 iQ.2).block j).atom P := rfl
  rw [hdef]
  by_cases hm : m = 0
  · -- m = 0: the atom is 0, which is in A.atoms Pg
    rw [if_pos hm]; exact atom_zero_mem AW Pg
  · -- m ≠ 0
    rw [if_neg hm]
    have hm_nonneg : 0 ≤ m :=
      Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun _Q _ => norm_nonneg _
    have hm_pos : 0 < m := lt_of_le_of_ne hm_nonneg (Ne.symm hm)
    -- Distribute m⁻¹ into the sum, then apply atom_finsum_mem
    rw [show (m : ℂ)⁻¹ • ∑ iQ ∈ FS,
          (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
            ((R iQ.1 iQ.2).block j).atom P =
        ∑ iQ ∈ FS,
          ((m : ℂ)⁻¹ * (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P)) •
            ((R iQ.1 iQ.2).block j).atom P from by
      rw [Finset.smul_sum]; congr 1; ext iQ; rw [smul_smul]]
    apply atom_finsum_mem AW Pg FS
        (fun iQ => (m : ℂ)⁻¹ * (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P))
        (fun iQ => ((R iQ.1 iQ.2).block j).atom P)
    · -- Every b_{P,Q} is in AW.atoms Pg
      intro ⟨i, Q⟩ _
      exact (R i Q).block j |>.atom_mem P
    · -- Norm bound: ∑ ‖m⁻¹ · c_Q · s_{P,Q}‖ ≤ 1
      -- Flatten the sigma sum back to the nested form to get TransmutationCoeff = m
      have h_flat : ∑ iQ ∈ FS, ‖c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P‖ = m := by
        show ∑ iQ ∈ (Finset.range N).sigma
            (fun i => (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1)),
            ‖c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P‖ = m
        rw [Finset.sum_sigma]
        rfl
      -- ‖(m : ℂ)‖ = m (since m > 0)
      have hm_norm : ‖(m : ℂ)‖ = m :=
        (RCLike.norm_ofReal (K := ℂ) m).trans (abs_of_pos hm_pos)
      -- Prove equality then use .le
      have hbound : ∑ iQ ∈ FS,
          ‖(m : ℂ)⁻¹ * (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P)‖ = 1 := by
        have h_expand : ∀ iQ ∈ FS,
            ‖(m : ℂ)⁻¹ * (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P)‖ =
            m⁻¹ * ‖c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P‖ :=
          fun iQ _ => by rw [norm_mul, norm_inv, hm_norm]
        rw [Finset.sum_congr rfl h_expand, ← Finset.mul_sum, h_flat,
          inv_mul_cancel₀ hm_pos.ne']
      exact hbound.le

/-- **Claim I**: `∑_j ∑_{P∈W^j} m_{P,N} · d_{P,N} = ∑_{i<N} ∑_{Q∈G^i} c_Q · h_Q` in Lp.
    Proof: exchange summation order using `h_Q = ∑_j ∑_{P⊆Q} s_{P,Q}·b_{P,Q}` (from `hR`)
    and the identity `m_{P,N} · d_{P,N} = ∑_{i<N} ∑_{Q∈G^i,P⊆Q} c_Q·s_{P,Q}·b_{P,Q}`. -/
theorem ClaimI
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (hk : AlmostLinearSequence k)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k hk lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := q) G c)
    (N : ℕ) :
    ∑' j : ℕ, ∑ P ∈ (W.grid.partitions j).attach,
        (↑(TransmutationCoeff G W AW h R c N P) : ℂ) •
          TransmutationAtom G W AW h R c N P =
    PartialSumLevels G W h c N := by
  -- Step 1: m_{P,N} · d_{P,N} = ∑_{i<N} ∑_{Q∈G^i} c_Q · term_{j,P,Q}
  have mD_eq : ∀ (j : ℕ) (P : LevelCell W j),
      (↑(TransmutationCoeff G W AW h R c N P) : ℂ) • TransmutationAtom G W AW h R c N P =
      ∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach,
        c i Q • ((R i Q).block j).term AW P := by
    intro j P
    -- P ⊄ Q → coeff = 0 → term = 0  (localization from hR)
    have hterm : ∀ i ∈ Finset.range N, ∀ Q ∈ (G.grid.partitions i).attach,
        ¬ P.1 ⊆ Q.1 → c i Q • ((R i Q).block j).term AW P = 0 := by
      intro i _ Q _ hPQ
      simp [LevelBlock.term, ((hR i Q).2.1 j P).1 hPQ]
    -- Removing the filter doesn't change the term sum (non-subset terms vanish)
    have hfilt_term : ∀ i ∈ Finset.range N,
        ∑ Q ∈ (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1),
            c i Q • ((R i Q).block j).term AW P =
        ∑ Q ∈ (G.grid.partitions i).attach,
            c i Q • ((R i Q).block j).term AW P := by
      intro i hi
      apply Finset.sum_filter_of_ne
      intro Q hQ hne
      by_contra h
      exact hne (hterm i hi Q hQ h)
    -- Removing the filter doesn't change the norm sum (non-subset coeff = 0)
    have hfilt_norm : ∀ i ∈ Finset.range N,
        ∑ Q ∈ (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1),
            ‖c i Q * ((R i Q).block j).coeff P‖ =
        ∑ Q ∈ (G.grid.partitions i).attach,
            ‖c i Q * ((R i Q).block j).coeff P‖ := by
      intro i hi
      apply Finset.sum_filter_of_ne
      intro Q hQ hne
      by_contra h
      simp [((hR i Q).2.1 j P).1 h] at hne
    -- Rewrite TransmutationCoeff and TransmutationAtom
    simp only [TransmutationAtom, TransmutationCoeff]
    set m := ∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach,
        ‖c i Q * ((R i Q).block j).coeff P‖
    rw [show (∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach.filter
            (fun Q => P.1 ⊆ Q.1), ‖c i Q * ((R i Q).block j).coeff P‖) = m from
      Finset.sum_congr rfl hfilt_norm]
    by_cases hm : m = 0
    · -- m = 0: all ‖c_Q s_{P,Q}‖ = 0, so all terms are 0
      simp only [hm, ↓reduceIte, smul_zero]
      symm
      apply Finset.sum_eq_zero; intro i hi
      apply Finset.sum_eq_zero; intro Q hQ
      have hle : ‖c i Q * ((R i Q).block j).coeff P‖ ≤ m :=
        calc ‖c i Q * ((R i Q).block j).coeff P‖
            ≤ ∑ Q' ∈ (G.grid.partitions i).attach,
                ‖c i Q' * ((R i Q').block j).coeff P‖ :=
              Finset.single_le_sum
                (f := fun Q' => ‖c i Q' * ((R i Q').block j).coeff P‖)
                (fun Q' _ => norm_nonneg _) hQ
          _ ≤ m :=
              Finset.single_le_sum
                (f := fun i' => ∑ Q' ∈ (G.grid.partitions i').attach,
                  ‖c i' Q' * ((R i' Q').block j).coeff P‖)
                (fun i' _ => Finset.sum_nonneg (fun Q' _ => norm_nonneg _)) hi
      have hzero : c i Q * ((R i Q).block j).coeff P = 0 :=
        norm_eq_zero.mp (le_antisymm (hm ▸ hle) (norm_nonneg _))
      simp only [LevelBlock.term, smul_smul, hzero, zero_smul]
    · -- m ≠ 0: (↑m) · (↑m)⁻¹ · num = num
      simp only [hm, ↓reduceIte]
      have hm_C : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      rw [smul_smul, mul_inv_cancel₀ hm_C, one_smul]
      exact Finset.sum_congr rfl hfilt_term
  -- Step 2: rewrite LHS using mD_eq, then exchange sums
  simp only [PartialSumLevels]
  -- Rewrite each summand via mD_eq
  have lhs_rw : ∀ j : ℕ,
      ∑ P ∈ (W.grid.partitions j).attach,
          (↑(TransmutationCoeff G W AW h R c N P) : ℂ) • TransmutationAtom G W AW h R c N P =
      ∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach,
          c i Q • ((R i Q).block j).toLp AW := by
    intro j
    simp_rw [Finset.sum_congr rfl (fun P _ => mD_eq j P)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro Q _
    rw [← Finset.smul_sum]
    simp only [LevelBlock.toLp]
  simp_rw [lhs_rw]
  -- Step 3: ∑' j, ∑_{i,Q} c_Q · (block j).toLp = ∑_{i,Q} c_Q · h i Q  -- using HasSum for each (i,Q) and linearity over the finite sum
  have hasSum_iQ : HasSum
      (fun j => ∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach,
          c i Q • ((R i Q).block j).toLp AW)
      (∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach,
          c i Q • h i Q) := by
    apply hasSum_sum; intro i _
    apply hasSum_sum; intro Q _
    exact ((R i Q).hasSum.const_smul (c i Q))
  rw [hasSum_iQ.tsum_eq]


/-- The level-`k` block of the transmutation atomic decomposition with respect to
    the target atom family `AW` on `W`.  For each cell `P ∈ W^k`:
    - coefficient: `m_{P,N} := TransmutationCoeff G W AW h R c N P ∈ ℝ≥0` (cast to ℂ),
    - atom: `d_{P,N} := TransmutationAtomLocal G W AW h R c N P`,
    which is a genuine `AW`-atom by `TransmutationAtomLocal_isAtom`. -/
noncomputable def TransmutationBlock
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) (k : ℕ) : LevelBlock AW k where
  coeff P := (TransmutationCoeff G W AW h R c N P : ℂ)
  atom P  := TransmutationAtomLocal G W AW h R c N P
  atom_mem P := TransmutationAtomLocal_isAtom G W AW h R c N P

/-- The local normalized transmutation block has the same `L^p` value as the
external formula using `TransmutationAtom`.

This is the bookkeeping identity
`∑_P m_{P,N} d_{P,N}` at a fixed level. -/
lemma transmutationBlock_toLp_eq
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N j : ℕ) :
    (TransmutationBlock G W AW h R c N j).toLp AW =
      ∑ P ∈ (W.grid.partitions j).attach,
        (TransmutationCoeff G W AW h R c N P : ℂ) •
          TransmutationAtom G W AW h R c N P := by
  unfold LevelBlock.toLp
  apply Finset.sum_congr rfl
  intro P hP
  set m := TransmutationCoeff G W AW h R c N P with hm_def
  set Pg := levelCellToWeakGridCell W j P
  set FS : Finset (Σ i : ℕ, LevelCell G i) :=
    (Finset.range N).sigma
      (fun i => (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1))
  subst Pg
  have hnum_sigma :
      (∑ iQ ∈ FS, c iQ.1 iQ.2 • ((R iQ.1 iQ.2).block j).term AW P) =
        ∑ i ∈ Finset.range N,
          ∑ Q ∈ (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1),
            c i Q • ((R i Q).block j).term AW P := by
    rw [Finset.sum_sigma]
  by_cases hm : m = 0
  · have hcoeffR : TransmutationCoeff G W AW h R c N P = 0 := by
      rw [← hm_def, hm]
    simp [LevelBlock.term, TransmutationBlock, hcoeffR]
    rw [hm]
    exact (zero_smul ℂ (TransmutationAtom G W AW h R c N P)).symm
  · have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    simp only [LevelBlock.term, TransmutationBlock]
    rw [show TransmutationCoeff G W AW h R c N P = m by rw [hm_def]]
    simp only [TransmutationAtom, TransmutationAtomLocal, ← hm_def, hm, ↓reduceIte]
    rw [smul_smul, mul_inv_cancel₀ hmC, one_smul]
    rw [← hnum_sigma]
    apply Lp.ext
    -- The finite sum of external terms has the expected pointwise representative.
    have hsum_ae :
        ⇑(∑ iQ ∈ FS, c iQ.1 iQ.2 • ((R iQ.1 iQ.2).block j).term AW P)
          =ᵐ[W.measure]
        fun x => ∑ iQ ∈ FS,
          (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) *
            AW.toFunction (levelCellToWeakGridCell W j P)
              (((R iQ.1 iQ.2).block j).atom P) x := by
      induction FS using Finset.induction_on with
      | empty =>
          exact (Lp.coeFn_zero ℂ p W.measure).trans
            (Filter.Eventually.of_forall (fun x => by simp))
      | insert iQ S hiQ ih =>
          simp only [Finset.sum_insert hiQ]
          refine (Lp.coeFn_add _ _).trans ?_
          have hhead :
              ⇑(c iQ.1 iQ.2 • ((R iQ.1 iQ.2).block j).term AW P)
                =ᵐ[W.measure]
              fun x => (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) *
                AW.toFunction (levelCellToWeakGridCell W j P)
                  (((R iQ.1 iQ.2).block j).atom P) x :=
            ((Lp.coeFn_smul _ _).trans
              ((LevelBlock.coeFn_term AW ((R iQ.1 iQ.2).block j) P).fun_const_smul _)).trans
              (Filter.Eventually.of_forall (fun x => by
                simp only [smul_eq_mul]
                ring))
          exact (hhead.add ih).trans
            (Filter.Eventually.of_forall (fun x => by
              simp only [Pi.add_apply]))
    filter_upwards
      [Lp.coeFn_smul (m : ℂ)
        (MemLp.toLp
          (AW.toFunction (levelCellToWeakGridCell W j P)
            ((m : ℂ)⁻¹ •
              ∑ iQ ∈ FS,
                (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
                  ((R iQ.1 iQ.2).block j).atom P))
          (AW.local_memLp_p (levelCellToWeakGridCell W j P) _)),
       MemLp.coeFn_toLp
          (AW.local_memLp_p (levelCellToWeakGridCell W j P)
            ((m : ℂ)⁻¹ •
              ∑ iQ ∈ FS,
                (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
                  ((R iQ.1 iQ.2).block j).atom P)),
       hsum_ae] with x hsmul htoLp hsum
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul ⊢
    rw [hsmul, htoLp, hsum]
    simp only [AtomFamily.toFunction, map_smul, map_sum, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hmC, one_mul]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- If a fixed target cell `P` is contained in cells `Q` of one source level,
then those `Q`s form an overlap family. Hence their number is bounded by
`G.grid.Cmult1`.

This is the geometric multiplicity used in Claim II at the step
`(∑_{Q:P⊆Q} a_Q)^p ≤ Cmult1^p ∑_{Q:P⊆Q} a_Q^p`. -/
lemma containing_cells_card_le_Cmult1
    (G W : WeakGridSpace (α := α)) (i j : ℕ) (P : LevelCell W j) :
    ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1).card
      ≤ G.grid.Cmult1 := by
  classical
  let S := (G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1
  by_cases hS : S.Nonempty
  · rcases hS with ⟨Q₀, hQ₀S⟩
    have hPne : P.1.Nonempty := by
      by_contra hne
      have hEmpty : P.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hpos : 0 < W.measure P.1 := by
        simpa [WeakGridSpace.measure] using W.grid.positive_measure j P.1 P.2
      rw [hEmpty, measure_empty] at hpos
      exact (lt_irrefl (0 : ℝ≥0∞)) hpos
    have hQ₀mem : Q₀.1 ∈ G.grid.partitions i := Q₀.2
    have hQ₀contains : P.1 ⊆ Q₀.1 := by
      simpa [S] using (Finset.mem_filter.mp hQ₀S).2
    have hmap :
        Set.MapsTo (fun Q : LevelCell G i => Q.1) (S : Set (LevelCell G i))
          (overlapFinset (G.grid.partitions i) Q₀.1 : Set (Set α)) := by
      intro Q hQS
      have hQcontains : P.1 ⊆ Q.1 := by
        simpa [S] using (Finset.mem_filter.mp hQS).2
      rcases hPne with ⟨x, hxP⟩
      simp [overlapFinset, Q.2]
      exact ⟨x, hQcontains hxP, hQ₀contains hxP⟩
    have hinj :
        Set.InjOn (fun Q : LevelCell G i => Q.1) (S : Set (LevelCell G i)) := by
      intro Q hQS R hRS hQR
      cases Q
      cases R
      simp at hQR
      simp [hQR]
    simpa [S] using
      (Finset.card_le_card_of_injOn (fun Q : LevelCell G i => Q.1) hmap hinj).trans
        (G.grid.overlap_card_le i Q₀.1 hQ₀mem)
  · have hEmpty : S = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hS
    have hcard :
        ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1).card = 0 := by
      simpa [S] using congrArg Finset.card hEmpty
    omega

/-- Power-sum estimate for the cells of one source level that contain a fixed
target cell.

This is the formal version of the Claim II step
`(∑_{Q:P⊆Q} a_Q)^p ≤ Cmult1^p ∑_{Q:P⊆Q} a_Q^p`. -/
lemma containing_cells_sum_rpow_le_Cmult1
    (G W : WeakGridSpace (α := α)) (i j : ℕ) (P : LevelCell W j)
    (a : LevelCell G i → ℝ)
    (hp_ne_top : p ≠ ∞)
    (ha_nonneg : ∀ Q ∈
      ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
        0 ≤ a Q) :
    (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
        a Q) ^ p.toReal ≤
      (G.grid.Cmult1 : ℝ) ^ p.toReal *
        ∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          a Q ^ p.toReal := by
  classical
  let S := (G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1
  have hp_one : (1 : ℝ) ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp_ne_top (Fact.out : (1 : ℝ≥0∞) ≤ p)
    simpa using h
  have hp_nonneg : 0 ≤ p.toReal := le_trans (zero_le_one : (0 : ℝ) ≤ 1) hp_one
  have hpow_sum :
      (∑ Q ∈ S, a Q) ^ p.toReal ≤
        (S.card : ℝ) ^ (p.toReal - 1) *
          ∑ Q ∈ S, a Q ^ p.toReal :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S hp_one
      (by simpa [S] using ha_nonneg)
  have hcardC_nat : S.card ≤ G.grid.Cmult1 := by
    simpa [S] using containing_cells_card_le_Cmult1 G W i j P
  have hcardC : (S.card : ℝ) ≤ (G.grid.Cmult1 : ℝ) := by exact_mod_cast hcardC_nat
  have hCnonneg : 0 ≤ (G.grid.Cmult1 : ℝ) := by exact_mod_cast Nat.zero_le G.grid.Cmult1
  by_cases hSempty : S.card = 0
  · have hS : S = ∅ := Finset.card_eq_zero.mp hSempty
    change (∑ Q ∈ S, a Q) ^ p.toReal ≤
      (G.grid.Cmult1 : ℝ) ^ p.toReal * ∑ Q ∈ S, a Q ^ p.toReal
    rw [hS]
    simp [Real.zero_rpow (lt_of_lt_of_le zero_lt_one hp_one).ne']
  · have hSpos_nat : 1 ≤ S.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hSempty)
    have hSpos : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hSpos_nat
    have hcard_pow_le_C :
        (S.card : ℝ) ^ (p.toReal - 1) ≤ (G.grid.Cmult1 : ℝ) ^ p.toReal := by
      calc
        (S.card : ℝ) ^ (p.toReal - 1)
            ≤ (S.card : ℝ) ^ p.toReal :=
              Real.rpow_le_rpow_of_exponent_le hSpos (by linarith)
        _ ≤ (G.grid.Cmult1 : ℝ) ^ p.toReal :=
              Real.rpow_le_rpow (by positivity) hcardC hp_nonneg
    exact hpow_sum.trans
      (mul_le_mul_of_nonneg_right hcard_pow_le_C
        (Finset.sum_nonneg fun Q hQ => Real.rpow_nonneg (ha_nonneg Q (by simpa [S] using hQ)) _))

/-- Fixed-source-level estimate after applying the multiplicity bound to each
target cell and exchanging the finite sums. -/
lemma transmutation_fixed_i_power_bound
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (i j : ℕ) (hp_ne_top : p ≠ ∞) :
    (∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal) ≤
      (G.grid.Cmult1 : ℝ) ^ p.toReal *
        ∑ Q : LevelCell G i,
          ‖c i Q‖ ^ p.toReal * (R i Q).levelCoeffPower j := by
  classical
  have hCnonneg : 0 ≤ (G.grid.Cmult1 : ℝ) := by exact_mod_cast Nat.zero_le G.grid.Cmult1
  have hpoint : ∀ P : LevelCell W j,
      (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
        ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal ≤
      (G.grid.Cmult1 : ℝ) ^ p.toReal *
        ∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖ ^ p.toReal := by
    intro P
    exact containing_cells_sum_rpow_le_Cmult1 (p := p) G W i j P
      (fun Q => ‖c i Q * ((R i Q).block j).coeff P‖) hp_ne_top
      (fun Q hQ => norm_nonneg _)
  calc
    (∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal)
        ≤ ∑ P : LevelCell W j,
            (G.grid.Cmult1 : ℝ) ^ p.toReal *
              ∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
                ‖c i Q * ((R i Q).block j).coeff P‖ ^ p.toReal := by
          exact Finset.sum_le_sum fun P _ => hpoint P
    _ = (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ∑ P : LevelCell W j,
            ∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
              ‖c i Q * ((R i Q).block j).coeff P‖ ^ p.toReal := by
          rw [Finset.mul_sum]
    _ = (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ∑ Q : LevelCell G i,
            ∑ P : LevelCell W j,
              if P.1 ⊆ Q.1 then
                ‖c i Q * ((R i Q).block j).coeff P‖ ^ p.toReal else 0 := by
          congr 1
          rw [Finset.sum_comm]
          simp [Finset.sum_filter]
    _ ≤ (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ∑ Q : LevelCell G i,
            ∑ P : LevelCell W j,
              ‖c i Q * ((R i Q).block j).coeff P‖ ^ p.toReal := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun Q _ =>
              Finset.sum_le_sum fun P _ => by
              by_cases hPQ : P.1 ⊆ Q.1
              · simp [hPQ]
              · simp [hPQ, Real.rpow_nonneg
                  (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _])
            (Real.rpow_nonneg hCnonneg _)
    _ = (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ∑ Q : LevelCell G i,
            ‖c i Q‖ ^ p.toReal * (R i Q).levelCoeffPower j := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro Q hQ
          rw [LpGridRepresentation.levelCoeffPower, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro P hP
          rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

/-- Fixed-source-level root estimate, after inserting the representation decay
bound `levelCoeffPower j ≤ C * lam^(j-k i)`. -/
lemma transmutation_fixed_i_root_bound
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (hk : AlmostLinearSequence k)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k hk lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (i j : ℕ) (hp_ne_top : p ≠ ∞) (hki : k i ≤ j) :
    (∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal) ^ (1 / p.toReal) ≤
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) := by
  classical
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos
      (fun h0 => absurd (h0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)) (by norm_num))
      hp_ne_top
  have hp_inv_nonneg : 0 ≤ 1 / p.toReal := by positivity
  have hCmult_nonneg : 0 ≤ (G.grid.Cmult1 : ℝ) := by exact_mod_cast Nat.zero_le G.grid.Cmult1
  have hlam_nonneg : 0 ≤ lam ^ ((↑(j - k i) : ℝ) / p.toReal) :=
    Real.rpow_nonneg hlam_pos.le _
  have hcoeff_nonneg : 0 ≤ CoeffPLevel (p := p) G c i :=
    Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
  have hfixed := transmutation_fixed_i_power_bound
    (p := p) G W AW h R c i j hp_ne_top
  have hdecay_sum :
      ∑ Q : LevelCell G i,
          ‖c i Q‖ ^ p.toReal * (R i Q).levelCoeffPower j
        ≤
      (C * lam ^ (j - k i)) * CoeffPLevel (p := p) G c i := by
    calc
      ∑ Q : LevelCell G i,
          ‖c i Q‖ ^ p.toReal * (R i Q).levelCoeffPower j
          ≤ ∑ Q : LevelCell G i,
              ‖c i Q‖ ^ p.toReal * (C * lam ^ (j - k i)) := by
            exact Finset.sum_le_sum fun Q _ =>
              mul_le_mul_of_nonneg_left ((hR i Q).2.2 j hki)
                (Real.rpow_nonneg (norm_nonneg _) _)
      _ = (C * lam ^ (j - k i)) * CoeffPLevel (p := p) G c i := by
            simp only [CoeffPLevel]
            rw [← Finset.sum_mul]
            ring_nf
  have hpower :
      ∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal
        ≤
      ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal)) ^ p.toReal := by
    have h1 :
        ∑ P : LevelCell W j,
          (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
            ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal
          ≤
        (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ((C * lam ^ (j - k i)) * CoeffPLevel (p := p) G c i) := by
      exact hfixed.trans
        (mul_le_mul_of_nonneg_left hdecay_sum
          (Real.rpow_nonneg hCmult_nonneg _))
    have hfactor_nonneg : 0 ≤ C * lam ^ (j - k i) :=
      mul_nonneg hC (pow_nonneg hlam_pos.le _)
    have htarget_eq :
        ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
            (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal)) ^ p.toReal =
        (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ((C * lam ^ (j - k i)) * CoeffPLevel (p := p) G c i) := by
      calc
        ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
            (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal)) ^ p.toReal
            =
          (G.grid.Cmult1 : ℝ) ^ p.toReal *
            (C ^ (1 / p.toReal)) ^ p.toReal *
            (lam ^ ((↑(j - k i) : ℝ) / p.toReal)) ^ p.toReal *
            ((CoeffPLevel (p := p) G c i) ^ (1 / p.toReal)) ^ p.toReal := by
              rw [Real.mul_rpow
                    (mul_nonneg (mul_nonneg hCmult_nonneg (Real.rpow_nonneg hC _))
                      hlam_nonneg)
                    (Real.rpow_nonneg hcoeff_nonneg _),
                  Real.mul_rpow
                    (mul_nonneg hCmult_nonneg (Real.rpow_nonneg hC _))
                    hlam_nonneg,
                  Real.mul_rpow hCmult_nonneg (Real.rpow_nonneg hC _)]
        _ = (G.grid.Cmult1 : ℝ) ^ p.toReal *
            C *
            lam ^ (j - k i) *
            CoeffPLevel (p := p) G c i := by
              rw [← Real.rpow_mul hC, ← Real.rpow_mul hlam_pos.le,
                ← Real.rpow_mul hcoeff_nonneg]
              field_simp [hp_pos.ne']
              simp
        _ = (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ((C * lam ^ (j - k i)) * CoeffPLevel (p := p) G c i) := by ring
    simpa [← htarget_eq] using h1
  have hleft_nonneg :
      0 ≤ ∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal :=
    Finset.sum_nonneg fun P _ => Real.rpow_nonneg
      (Finset.sum_nonneg fun Q _ => norm_nonneg _) _
  have htarget_nonneg :
      0 ≤ (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hCmult_nonneg (Real.rpow_nonneg hC _))
        hlam_nonneg)
      (Real.rpow_nonneg hcoeff_nonneg _)
  have hroot := Real.rpow_le_rpow hleft_nonneg hpower hp_inv_nonneg
  calc
    (∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal) ^ (1 / p.toReal)
        ≤
      (((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal)) ^ p.toReal) ^
        (1 / p.toReal) := hroot
    _ = (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) := by
          rw [← Real.rpow_mul htarget_nonneg]
          field_simp [hp_pos.ne']
          rw [Real.rpow_one]

/-- Finite Minkowski inequality for nonnegative arrays. -/
lemma finset_Lp_sum_le_sum_Lp
    {ι κ : Type*} (S : Finset ι) (T : Finset κ) (a : ι → κ → ℝ)
    (hp_ne_top : p ≠ ∞)
    (ha_nonneg : ∀ i ∈ S, ∀ k ∈ T, 0 ≤ a i k) :
    (∑ k ∈ T, (∑ i ∈ S, a i k) ^ p.toReal) ^ (1 / p.toReal) ≤
      ∑ i ∈ S, (∑ k ∈ T, (a i k) ^ p.toReal) ^ (1 / p.toReal) := by
  classical
  have hp_one : (1 : ℝ) ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp_ne_top (Fact.out : (1 : ℝ≥0∞) ≤ p)
    simpa using h
  have hp_pos : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hp_one
  revert ha_nonneg
  refine Finset.induction_on S ?base ?step
  · intro ha_nonneg
    simp only [Finset.sum_empty]
    rw [Real.zero_rpow hp_pos.ne']
    simp only [Finset.sum_const_zero]
    rw [Real.zero_rpow (one_div_pos.mpr hp_pos).ne']
  · intro i S hi ih ha_nonneg
    have hi_nonneg : ∀ k ∈ T, 0 ≤ a i k := by
      intro k hk
      exact ha_nonneg i (Finset.mem_insert_self i S) k hk
    have hS_nonneg : ∀ i' ∈ S, ∀ k ∈ T, 0 ≤ a i' k := by
      intro i' hi' k hk
      exact ha_nonneg i' (Finset.mem_insert_of_mem hi') k hk
    have hsumS_nonneg : ∀ k ∈ T, 0 ≤ ∑ i' ∈ S, a i' k := by
      intro k hk
      exact Finset.sum_nonneg fun i' hi' => hS_nonneg i' hi' k hk
    calc
      (∑ k ∈ T, (∑ i' ∈ insert i S, a i' k) ^ p.toReal) ^ (1 / p.toReal)
          =
        (∑ k ∈ T, (a i k + ∑ i' ∈ S, a i' k) ^ p.toReal) ^ (1 / p.toReal) := by
          congr 2
          ext k
          rw [Finset.sum_insert hi]
      _ ≤
        (∑ k ∈ T, (a i k) ^ p.toReal) ^ (1 / p.toReal) +
          (∑ k ∈ T, (∑ i' ∈ S, a i' k) ^ p.toReal) ^ (1 / p.toReal) := by
          exact Real.Lp_add_le_of_nonneg
            (s := T) (p := p.toReal)
            (f := fun k => a i k)
            (g := fun k => ∑ i' ∈ S, a i' k)
            hp_one hi_nonneg hsumS_nonneg
      _ ≤
        (∑ k ∈ T, (a i k) ^ p.toReal) ^ (1 / p.toReal) +
          ∑ i' ∈ S, (∑ k ∈ T, (a i' k) ^ p.toReal) ^ (1 / p.toReal) := by
          exact add_le_add_right (ih hS_nonneg)
            ((∑ k ∈ T, (a i k) ^ p.toReal) ^ (1 / p.toReal))
      _ =
        ∑ i' ∈ insert i S, (∑ k ∈ T, (a i' k) ^ p.toReal) ^ (1 / p.toReal) := by
          rw [Finset.sum_insert hi]

/-- The per-level estimate in Claim II, corresponding to the chain ending at
equation `(for)` in the paper.

It packages Minkowski, the same-level multiplicity bound, localization
`P ⊆ Q`, and the representation decay
`levelCoeffPower j ≤ C * lam^(j-k i)`. -/
lemma transmutation_level_bound
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (hk : AlmostLinearSequence k)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k hk lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N j : ℕ) (hp_ne_top : p ≠ ∞) :
    (CoeffPLevel (p := p) W
        (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j) ^ (1 / p.toReal) ≤
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        (∑' i, if k i ≤ j then
          lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
            (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0) := by
  classical
  let S : Finset ℕ := Finset.range N
  let T : Finset (LevelCell W j) := Finset.univ
  let a : ℕ → LevelCell W j → ℝ := fun i P =>
    if k i ≤ j then
      ∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
        ‖c i Q * ((R i Q).block j).coeff P‖
    else 0
  have ha_nonneg : ∀ i ∈ S, ∀ P ∈ T, 0 ≤ a i P := by
    intro i hi P hP
    dsimp [a]
    split_ifs
    · exact Finset.sum_nonneg fun Q hQ => norm_nonneg _
    · exact le_rfl
  have hm_eq : ∀ P : LevelCell W j,
      TransmutationCoeff G W AW h R c N P = ∑ i ∈ S, a i P := by
    intro P
    dsimp [S, a, TransmutationCoeff]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hki : k i ≤ j
    · simp [hki]
    · have hjlt : j < k i := Nat.lt_of_not_ge hki
      have hinner_zero :
          (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
            ‖c i Q * ((R i Q).block j).coeff P‖) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro Q hQ
        have hcoeff_zero := ((hR i Q).2.1 j P).2 hjlt
        simp [hcoeff_zero]
      simpa [hki, norm_mul] using hinner_zero
  have hleft_eq :
      CoeffPLevel (p := p) W
          (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j =
        ∑ P : LevelCell W j, (∑ i ∈ S, a i P) ^ p.toReal := by
    unfold CoeffPLevel
    refine Finset.sum_congr rfl ?_
    intro P hP
    change ‖((TransmutationCoeff G W AW h R c N P : ℝ) : ℂ)‖ ^ p.toReal =
      (∑ i ∈ S, a i P) ^ p.toReal
    rw [hm_eq P]
    have hsum_nonneg : 0 ≤ ∑ i ∈ S, a i P :=
      Finset.sum_nonneg fun i hi => ha_nonneg i hi P (by simp [T])
    rw [Complex.norm_of_nonneg hsum_nonneg]
  have hMinkowski :
      (∑ P : LevelCell W j, (∑ i ∈ S, a i P) ^ p.toReal) ^ (1 / p.toReal) ≤
        ∑ i ∈ S, (∑ P : LevelCell W j, (a i P) ^ p.toReal) ^ (1 / p.toReal) := by
    simpa [T] using
      finset_Lp_sum_le_sum_Lp (p := p) S T a hp_ne_top ha_nonneg
  have hterm_bound : ∀ i ∈ S,
      (∑ P : LevelCell W j, (a i P) ^ p.toReal) ^ (1 / p.toReal) ≤
        (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          (if k i ≤ j then
            lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
              (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0) := by
    intro i hi
    by_cases hki : k i ≤ j
    · have hfixed := transmutation_fixed_i_root_bound
        (p := p) G W AW k hk lam hlam_pos hlam_lt C hC h R hR c i j hp_ne_top hki
      simpa [a, hki, mul_assoc] using hfixed
    · have hzero_sum :
          (∑ P : LevelCell W j, (a i P) ^ p.toReal) = 0 := by
        have hp_pos : 0 < p.toReal :=
          ENNReal.toReal_pos
            (fun h0 => absurd (h0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)) (by norm_num))
            hp_ne_top
        refine Finset.sum_eq_zero ?_
        intro P hP
        simp [a, hki, Real.zero_rpow hp_pos.ne']
      have hp_pos : 0 < p.toReal :=
        ENNReal.toReal_pos
          (fun h0 => absurd (h0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)) (by norm_num))
          hp_ne_top
      rw [hzero_sum, Real.zero_rpow (one_div_pos.mpr hp_pos).ne']
      simp [hki]
  have hfinite_le :
      ∑ i ∈ S, (∑ P : LevelCell W j, (a i P) ^ p.toReal) ^ (1 / p.toReal) ≤
        ∑ i ∈ S,
          (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
            (if k i ≤ j then
              lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
                (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0) :=
    Finset.sum_le_sum fun i hi => hterm_bound i hi
  have hfinite_tsum :
      ∑ i ∈ S,
          (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
            (if k i ≤ j then
              lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
                (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0)
        ≤
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        (∑' i, if k i ≤ j then
          lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
            (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0) := by
    let K : ℝ := (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal)
    let g : ℕ → ℝ := fun i =>
      if k i ≤ j then
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0
    have hg_nonneg : ∀ i, 0 ≤ g i := by
      intro i
      dsimp [g]
      split_ifs
      · exact mul_nonneg (Real.rpow_nonneg hlam_pos.le _)
          (Real.rpow_nonneg
            (Finset.sum_nonneg fun Q hQ => Real.rpow_nonneg (norm_nonneg _) _) _)
      · exact le_rfl
    have hg_support : Function.support g ⊆ {i : ℕ | k i ≤ j} := by
      intro i hi
      by_contra hki
      have hki' : ¬ k i ≤ j := by simpa using hki
      have : g i = 0 := by simp [g, hki']
      exact hi this
    have hg_finite : (Function.support g).Finite :=
      (almostLinearSequence_finite_le_level hk j).subset hg_support
    have hgsum : Summable g := summable_of_hasFiniteSupport hg_finite
    have hsum_le : ∑ i ∈ S, g i ≤ ∑' i, g i :=
      hgsum.sum_le_tsum S (fun i hi => hg_nonneg i)
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hC _)
    calc
      ∑ i ∈ S,
          (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
            (if k i ≤ j then
              lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
                (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0)
          = K * ∑ i ∈ S, g i := by
            simp [K, g, Finset.mul_sum]
      _ ≤ K * (∑' i, g i) := mul_le_mul_of_nonneg_left hsum_le hK_nonneg
      _ =
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        (∑' i, if k i ≤ j then
          lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
            (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0) := by
            simp [K, g]
  rw [hleft_eq]
  exact hMinkowski.trans (hfinite_le.trans hfinite_tsum)

/-- The convolution/ALS estimate used in Claim II.

This is the Lean statement of the paper's residue-class decomposition and
Young convolution trick with `b_n = lam^(r*n)`. -/
lemma transmutation_convolution_bound
    (k : ℕ → ℕ)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (B_als r_als : NNReal) (hr_als : 0 < r_als)
    (hk_upper : ∀ i : ℕ, (k i : NNReal) ≤ r_als * (i : NNReal) + B_als)
    (vL : ℕ → ℝ)
    (hvL_nn : ∀ i, 0 ≤ vL i)
    (hsource : Summable fun i => vL i ^ (q.toReal / p.toReal))
    (hq_ne_top : q ≠ ∞) :
    Summable (fun j =>
      (∑' i, if k i ≤ j then
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (vL i) ^ (1 / p.toReal) else 0) ^ q.toReal) ∧
    (∑' j, (∑' i, if k i ≤ j then
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (vL i) ^ (1 / p.toReal) else 0) ^ q.toReal) ^ (1 / q.toReal) ≤
      lam ^ (-(B_als : ℝ) / p.toReal) *
      LpGridRepresentation.cCoefficient p ∞
        (fun n => lam ^ ((r_als : ℝ) * (n : ℝ))) *
      (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
      (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
  sorry

/-- Finite abstract cost for the transmutation blocks.

This is obtained from the per-level estimate and the convolution/ALS estimate:
the transmuted coefficients are dominated by a summable sequence. -/
lemma transmutationBlock_abstractFinitePQCost
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (hk : AlmostLinearSequence k)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k hk lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := q) G c)
    (N : ℕ) (hp_ne_top : p ≠ ∞) (hq_ne_top : q ≠ ∞) :
    AbstractFinitePQCost (q := q) (TransmutationBlock G W AW h R c N) := by
  have hq_pos : (0 : ℝ) < q.toReal :=
    ENNReal.toReal_pos (fun h0 => absurd (h0 ▸ (Fact.out : 1 ≤ q)) (by norm_num)) hq_ne_top
  obtain ⟨_, B_als, r_als, hr_als, hk_bound⟩ := hk
  let uL : ℕ → ℝ :=
    fun j => CoeffPLevel (p := p) W
      (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j
  let vL : ℕ → ℝ := fun i => CoeffPLevel (p := p) G c i
  let convL : ℕ → ℝ :=
    fun j => ∑' i, if k i ≤ j then
      lam ^ ((↑(j - k i) : ℝ) / p.toReal) * (vL i) ^ (1 / p.toReal) else 0
  have huL_nn : ∀ j, 0 ≤ uL j := fun j =>
    Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _
  have hvL_nn : ∀ i, 0 ≤ vL i := fun i =>
    Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
  have hconvL_nn : ∀ j, 0 ≤ convL j := fun j =>
    tsum_nonneg fun i => by
      split_ifs
      · exact mul_nonneg (Real.rpow_nonneg hlam_pos.le _) (Real.rpow_nonneg (hvL_nn i) _)
      · exact le_rfl
  have hvL_sum : Summable fun i => vL i ^ (q.toReal / p.toReal) := by
    simpa [CoeffFinitePQCost, hq_ne_top, vL] using hc
  have hk0 : AlmostLinearSequence k := ⟨_, B_als, r_als, hr_als, hk_bound⟩
  have hLevelBound : ∀ j, uL j ^ (1 / p.toReal) ≤
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j := by
    intro j
    simpa [uL, vL, convL] using
      transmutation_level_bound
        G W AW k hk0 lam hlam_pos hlam_lt C hC h R hR c N j hp_ne_top
  have hk_upper : ∀ i : ℕ, (k i : NNReal) ≤ r_als * (i : NNReal) + B_als :=
    fun i => (hk_bound i).1
  have hConv :
      Summable (fun j => convL j ^ q.toReal) ∧
      (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) ≤
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficient p ∞
          (fun n => lam ^ ((r_als : ℝ) * (n : ℝ))) *
        (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
        (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
    simpa [convL] using
      transmutation_convolution_bound
        (p := p) (q := q) k lam hlam_pos hlam_lt B_als r_als hr_als
        hk_upper vL hvL_nn hvL_sum hq_ne_top
  have hterm_le : ∀ j,
      uL j ^ (q.toReal / p.toReal) ≤
      (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
      convL j ^ q.toReal := by
    intro j
    have h1 : uL j ^ (q.toReal / p.toReal) ≤
        ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j) ^ q.toReal := by
      have hmono := Real.rpow_le_rpow
        (Real.rpow_nonneg (huL_nn j) (1 / p.toReal))
        (hLevelBound j) hq_pos.le
      rwa [← Real.rpow_mul (huL_nn j),
           show 1 / p.toReal * q.toReal = q.toReal / p.toReal from by ring] at hmono
    have h2 : ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j) ^ q.toReal =
        (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
        convL j ^ q.toReal := by
      rw [Real.mul_rpow
            (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hC (1 / p.toReal)))
            (hconvL_nn j),
          Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hC (1 / p.toReal)),
          ← Real.rpow_mul hC,
          show 1 / p.toReal * q.toReal = q.toReal / p.toReal from by ring]
    exact h1.trans h2.le
  have huL_sum : Summable (fun j => uL j ^ (q.toReal / p.toReal)) :=
    Summable.of_nonneg_of_le
      (fun j => Real.rpow_nonneg (huL_nn j) _)
      hterm_le
      (hConv.1.mul_left _)
  simp only [AbstractFinitePQCost, hq_ne_top, ↓reduceIte]
  simpa [uL, blockLvlCoeff, CoeffPLevel, TransmutationBlock] using huL_sum

/-- **Claim II**: For every `N : ℕ`, the transmutation level blocks
    `TransmutationBlock G W AW h R c N k` form a `Bˢ_{p,q}(AW)`-representation of
    `PartialSumLevels G W h c N`, and the `(p,q)` coefficient cost satisfies

        pqCost(m_{P,N}) ≤ Cmult1 * C^(1/p) * lam^(-B/p) * Cco2(p,b) * Cm1^(1/q)
                          * pqCost(c_Q)

    where `Cmult1 = G.grid.Cmult1` (multiplicity of G), `C` and `lam` are the
    decay constants from `hR`, `B` and `r` are the ALS upper-offset and slope from `hk`,
    `Cco2(p,b) = LpGridRepresentation.cCoefficient p ∞ (fun n => lam ^ (r * n))`
    is the convolution trick constant (Prop 4.2, Case A) with `b_n = lam ^ (r * n)`,
    and `Cm1 = Nat.ceil r` accounts for the `⌈r⌉` residue classes.

    Both the ALS upper-offset `B` and slope `r` are witnessed from `hk`:
    `AlmostLinearSequence k` gives `∃ A B r, r > 0 ∧ ∀ i, k(i) ≤ r*i + B ∧ r*i+A ≤ k(i)`,
    so the existential in Part 2 is witnessed by `B` and `r`. -/
theorem ClaimII
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (hk : AlmostLinearSequence k)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k hk lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := q) G c)
    (N : ℕ)
    (hq_ne_top : q ≠ ∞)
    -- Hypotheses needed for Part 1 (formalBlockSeq_summable)
    (hG2_W : AssumptionG2 W s p u q)
    (hp_ne_top : p ≠ ∞)
    (hs_pos : 0 < s) :
    /- Part 1: the transmutation level blocks sum to `PartialSumLevels` in Lp. -/
    HasSum (fun j => (TransmutationBlock G W AW h R c N j).toLp AW)
           (PartialSumLevels G W h c N) ∧
    /- Part 2: ∃ ALS upper-offset B and slope r (from `hk`) such that the (p,q)-cost satisfies -/
    ∃ (B_als r_als : NNReal), 0 < r_als ∧
      CoeffPQCost (p := p) (q := q) W (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) ≤
        (G.grid.Cmult1 : ℝ) *
        C ^ (1 / p.toReal) *
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficient p ∞
          (fun n => lam ^ ((r_als : ℝ) * (n : ℝ))) *
        (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
        CoeffPQCost (p := p) (q := q) G c := by
  have hq_pos : (0 : ℝ) < q.toReal :=
    ENNReal.toReal_pos (fun h => absurd (h ▸ (Fact.out : 1 ≤ q)) (by norm_num)) hq_ne_top
  have hp_pos : (0 : ℝ) < p.toReal :=
    ENNReal.toReal_pos (fun h => absurd (h ▸ AW.one_le_p) (by norm_num)) AW.p_ne_top
  constructor
  · -- Part 1: HasSum
    -- Strategy: (a) AbstractFinitePQCost (TransmutationBlock) from coefficient bound + hc;
    --           (b) formalBlockSeq_summable gives Summable;
    --           (c) identify the sum as PartialSumLevels via ClaimI.
    --
    -- (a) Finite abstract pq-cost
    -- blockLvlCoeff (TransmutationBlock j) k = CoeffPLevel W (TransmutationCoeff) k,
    -- so AbstractFinitePQCost = CoeffFinitePQCost W (TransmutationCoeff),
    -- which follows from Part 2's bound (CoeffPQCost W ≤ K · CoeffPQCost G c) + hc.
    have hfin : AbstractFinitePQCost (q := q) (TransmutationBlock G W AW h R c N) := by
      exact transmutationBlock_abstractFinitePQCost
        G W AW k hk lam hlam_pos hlam_lt C hC h R hR c hc N hp_ne_top hq_ne_top
    -- (b) Summable via formalBlockSeq_summable (no atom convergence needed!)
    have hsum : Summable (fun j => (TransmutationBlock G W AW h R c N j).toLp AW) :=
      formalBlockSeq_summable (G := W) (A := AW) hG2_W hp_ne_top hs_pos Fact.out
        (TransmutationBlock G W AW h R c N) hfin
    -- (c) Identity: (TransmutationBlock j).toLp AW = ∑_P m_P · TransmutationAtom P
    -- follows from atomLp being linear and the definitions of TransmutationAtomLocal/Atom.
    have hblock_eq : ∀ j, (TransmutationBlock G W AW h R c N j).toLp AW =
        ∑ P ∈ (W.grid.partitions j).attach,
          (TransmutationCoeff G W AW h R c N P : ℂ) •
            TransmutationAtom G W AW h R c N P := by
      intro j
      exact transmutationBlock_toLp_eq G W AW h R c N j
    -- (d) The tsum equals PartialSumLevels by ClaimI
    have htsum_eq : ∑' j, (TransmutationBlock G W AW h R c N j).toLp AW =
        PartialSumLevels G W h c N := by
      simp_rw [hblock_eq]
      exact ClaimI G W AW k hk lam hlam_pos hlam_lt C hC h R hR c hc N
    -- Conclude: HasSum from Summable + sum identity
    rw [← htsum_eq]
    exact hsum.hasSum
  · -- Part 2: Coefficient bound (paper Prop 8.1)
    have hk0 : AlmostLinearSequence k := hk
    obtain ⟨_, B_als, r_als, hr_als, hk_bound⟩ := hk
    refine ⟨B_als, r_als, hr_als, ?_⟩
    -- Since q ≠ ∞, unpack CoeffPQCost on both sides as (∑' ...)^{1/q}
    have hLHS_eq :
        CoeffPQCost (p := p) (q := q) W
          (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) =
        (∑' j, CoeffPLevel (p := p) W
            (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j ^
          (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
      simp [CoeffPQCost, hq_ne_top]
    have hRHS_eq :
        CoeffPQCost (p := p) (q := q) G c =
        (∑' i, CoeffPLevel (p := p) G c i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
      simp [CoeffPQCost, hq_ne_top]
    rw [hLHS_eq, hRHS_eq]
    -- Working abbreviations
    set uL : ℕ → ℝ :=
      fun j => CoeffPLevel (p := p) W
        (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j
    set vL : ℕ → ℝ := fun i => CoeffPLevel (p := p) G c i
    -- Convolution sequence:  convL_j = ∑_i [k_i ≤ j] · lam^{(j - k_i)/p} · vL_i^{1/p}
    -- (the per-level bound from Minkowski applied term-by-term; includes 1/p powers)
    set convL : ℕ → ℝ :=
      fun j => ∑' i, if k i ≤ j then
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) * (vL i) ^ (1 / p.toReal) else 0
    -- Basic nonnegativity
    have huL_nn : ∀ j, 0 ≤ uL j := fun j =>
      Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _
    have hvL_nn : ∀ i, 0 ≤ vL i := fun i =>
      Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
    have hconvL_nn : ∀ j, 0 ≤ convL j := fun j =>
      tsum_nonneg fun i => by
        split_ifs with hi
        · exact mul_nonneg (Real.rpow_nonneg hlam_pos.le _) (Real.rpow_nonneg (hvL_nn i) _)
        · exact le_refl 0
    -- STEP A: Level-by-level bound (Minkowski + decay + multiplicity)
    -- For each j: u_j^{1/p} ≤ Cmult1 · C^{1/p} · convL_j
    -- where convL_j = ∑_i [k_i ≤ j] lam^{(j-k_i)/p} · vL_i^{1/p}
    -- Proof sketch:
    --   m_{P,N} = ∑_{i<N} ∑_{Q∈G^i, P⊆Q} |c_Q · s_{P,Q}|
    --   Minkowski: (∑_P m_P^p)^{1/p} ≤ ∑_{i: k_i≤j} (∑_P (∑_{Q:P⊆Q} |c_Q s_{P,Q}|)^p)^{1/p}
    --   Each term ≤ Cmult1 · (C · lam^{j-k_i})^{1/p} · vL_i^{1/p}
    --   (using multiplicity bound + decay bound from hR)
    have hLevelBound : ∀ j, uL j ^ (1 / p.toReal) ≤
        (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j := by
      intro j
      simpa [uL, vL, convL] using
        transmutation_level_bound
          G W AW k hk0 lam hlam_pos hlam_lt C hC h R hR c N j hp_ne_top
    -- STEP D: Convolution + ALS bound (paper Prop 4.2, Case A)
    -- Uses k i ≤ r · i + B (ALS upper bound):
    --   lam^{j - k i} ≤ lam^{j - r·i - B} = lam^{-B} · lam^{j - r·i}
    -- Decomposes i into ⌈r⌉ residue classes mod ⌈r⌉,
    -- applies Young's ℓ^{q/p} convolution with b_n = lam^{r·n}
    -- (the C_co2(p,q,b) constant of Prop 4.2).
    have hvL_sum : Summable fun i => vL i ^ (q.toReal / p.toReal) := by
      simpa [CoeffFinitePQCost, hq_ne_top, vL] using hc
    have hk_upper : ∀ i : ℕ, (k i : NNReal) ≤ r_als * (i : NNReal) + B_als :=
      fun i => (hk_bound i).1
    have hConv :
        Summable (fun j => convL j ^ q.toReal) ∧
        (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) ≤
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficient p ∞
          (fun n => lam ^ ((r_als : ℝ) * (n : ℝ))) *
        (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
        (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
      simpa [convL] using
        transmutation_convolution_bound
          (p := p) (q := q) k lam hlam_pos hlam_lt B_als r_als hr_als
          hk_upper vL hvL_nn hvL_sum hq_ne_top
    have hConvBound :
        (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) ≤
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficient p ∞
          (fun n => lam ^ ((r_als : ℝ) * (n : ℝ))) *
        (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
        (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) :=
      hConv.2
    -- STEP B+C: From hLevelBound, bound ∑' j, u_j^{q/p}
    -- u_j^{1/p} ≤ Cm1 · C^{1/p} · convL_j  ⟹  u_j^{q/p} = (u_j^{1/p})^q ≤ (Cm1 · C^{1/p} · convL_j)^q
    --                                            = Cm1^q · C^{q/p} · convL_j^q
    -- Summing: ∑' j, u_j^{q/p} ≤ Cm1^q · C^{q/p} · ∑' j, convL_j^q
    have hterm_le : ∀ j,
        uL j ^ (q.toReal / p.toReal) ≤
        (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
        convL j ^ q.toReal := by
      intro j
      -- uL j^{q/p} = (uL j^{1/p})^q ≤ (Cmult1 * C^{1/p} * convL j)^q  [rpow monotone]
      have h1 : uL j ^ (q.toReal / p.toReal) ≤
          ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j) ^ q.toReal := by
        have hmono := Real.rpow_le_rpow
          (Real.rpow_nonneg (huL_nn j) (1 / p.toReal))
          (hLevelBound j) hq_pos.le
        rwa [← Real.rpow_mul (huL_nn j),
             show 1 / p.toReal * q.toReal = q.toReal / p.toReal from by ring] at hmono
      -- (Cmult1 * C^{1/p} * convL j)^q = Cmult1^q * C^{q/p} * convL j^q
      have h2 : ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j) ^ q.toReal =
          (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
          convL j ^ q.toReal := by
        rw [Real.mul_rpow
              (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hC (1 / p.toReal)))
              (hconvL_nn j),
            Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hC (1 / p.toReal)),
            ← Real.rpow_mul hC,
            show 1 / p.toReal * q.toReal = q.toReal / p.toReal from by ring]
      exact h1.trans h2.le
    -- Sum the term-by-term bound
    have hStepBC :
        ∑' j, uL j ^ (q.toReal / p.toReal) ≤
        (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
        ∑' j, convL j ^ q.toReal := by
      -- Summability of convL^q follows from hConvBound (finite upper bound)
      have hconv_sum : Summable (fun j => convL j ^ q.toReal) := by
        exact hConv.1
      -- The RHS term (pointwise scaled by the constant factor) is summable
      have hKsumm : Summable (fun j =>
            (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
            convL j ^ q.toReal) :=
        hconv_sum.mul_left _
      -- uL^{q/p} is summable because it is dominated term-by-term by hKsumm
      have huL_sum : Summable (fun j => uL j ^ (q.toReal / p.toReal)) :=
        Summable.of_nonneg_of_le
          (fun j => Real.rpow_nonneg (huL_nn j) _)
          hterm_le
          hKsumm
      rw [← tsum_mul_left]
      exact huL_sum.tsum_le_tsum hterm_le hKsumm
    -- STEP E: Extract the 1/q root:
    -- (Cm1^q · C^{q/p} · X)^{1/q} = Cm1 · C^{1/p} · X^{1/q}
    have hX_nn : (0 : ℝ) ≤ ∑' j, convL j ^ q.toReal :=
      tsum_nonneg fun j => Real.rpow_nonneg (hconvL_nn j) _
    have hStepE :
        (∑' j, uL j ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) ≤
        (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) := by
      have hstep1 :
          (∑' j, uL j ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) ≤
          ((G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
           ∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) :=
        Real.rpow_le_rpow
          (tsum_nonneg fun j => Real.rpow_nonneg (huL_nn j) _)
          hStepBC
          (div_nonneg zero_le_one hq_pos.le)
      -- Algebra: (Cm1^q · C^{q/p} · X)^{1/q} = Cm1 · C^{1/p} · X^{1/q}
      have hstep2 :
          ((G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
           ∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) =
          (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) := by
        rw [Real.mul_rpow
              (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hC _))
              hX_nn,
            Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hC _)]
        -- (Cm1^q)^{1/q} = Cm1
        congr 2
        · rw [← Real.rpow_mul (Nat.cast_nonneg _)]
          rw [mul_one_div_cancel hq_pos.ne', Real.rpow_one]
        -- (C^{q/p})^{1/q} = C^{1/p}
        · rw [← Real.rpow_mul hC]
          congr 1; field_simp [hp_pos.ne', hq_pos.ne']
      exact hstep1.trans hstep2.le
    -- Final combination
    calc (∑' j, uL j ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)
        ≤ (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) :=
          hStepE
      _ ≤ (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          (lam ^ (-(B_als : ℝ) / p.toReal) *
           LpGridRepresentation.cCoefficient p ∞
             (fun n => lam ^ ((r_als : ℝ) * (n : ℝ))) *
           (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
           (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)) :=
          mul_le_mul_of_nonneg_left hConvBound
            (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hC _))
      _ = (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * lam ^ (-(B_als : ℝ) / p.toReal) *
          LpGridRepresentation.cCoefficient p ∞
            (fun n => lam ^ ((r_als : ℝ) * (n : ℝ))) *
          (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
          (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by ring


end -- closes noncomputable section

end WeakGridSpace
