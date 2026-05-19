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

/-- **Claim II**: For every `N : ℕ`, the transmutation level blocks
    `TransmutationBlock G W AW h R c N k` form a `Bˢ_{p,q}(AW)`-representation of
    `PartialSumLevels G W h c N`, and the `(p,q)` coefficient cost satisfies

        pqCost(m_{P,N}) ≤ Cmult1 * C^(1/p) * lam^(-B/p) * Cco2(p,q) * (1-lam^(q/p))^(-1/q)
                          * pqCost(c_Q)

    where `Cmult1 = G.grid.Cmult1` (multiplicity of G), `C` and `lam` are the
    decay constants from `hR`, `B` is the ALS upper-offset witnessing `k(i) ≤ r*i + B`,
    and `Cco2(p,q) = LpGridRepresentation.cCoefficient p q` applied to the
    level measure weight sequence of `W`. -/
theorem ClaimII
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (hk : AlmostLinearSequence k)
    /- ALS upper-offset: ∃ r > 0 such that k(i) ≤ r·i + B for all i. -/
    (B_als : NNReal) (r_als : NNReal) (hr_als : 0 < r_als)
    (hk_upper : ∀ i : ℕ, (k i : NNReal) ≤ r_als * (i : NNReal) + B_als)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k hk lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := q) G c)
    (N : ℕ)
    /- Finiteness of q (the q = ∞ case is analogous). -/
    (hq_ne_top : q ≠ ∞)
    /- Finiteness of the level-measure weight coefficient cost for W. -/
    (hCco_fin : LpGridRepresentation.cCoefficientFinite p q
        (fun j => LpGridRepresentation.levelMeasureWeight W s p p j ^ p.toReal))
    /- Convergence of the geometric series: λ^{q/p} < 1. -/
    (hlam_qp : lam ^ (q.toReal / p.toReal) < 1) :
    /- Part 1: the transmutation level blocks sum to `PartialSumLevels` in Lp. -/
    HasSum (fun j => (TransmutationBlock G W AW h R c N j).toLp AW)
           (PartialSumLevels G W h c N) ∧
    /- Part 2: the (p,q)-cost of the transmutation coefficient sequence `(m_{P,N})` obeys -/
    CoeffPQCost (p := p) (q := q) W (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) ≤
      (G.grid.Cmult1 : ℝ) *
      C ^ (1 / p.toReal) *
      lam ^ (-(B_als : ℝ) / p.toReal) *
      LpGridRepresentation.cCoefficient p q (fun j => LpGridRepresentation.levelMeasureWeight W s p p j ^ p.toReal) *
      (1 - lam ^ (q.toReal / p.toReal)) ^ (-(1 / q.toReal)) *
      CoeffPQCost (p := p) (q := q) G c := by
  constructor
  · -- Part 1: HasSum
    -- The key identity is (TransmutationBlock k).toLp = ∑_{P ∈ W^k} m_{P,N} · d_{P,N} in Lp,
    -- and then ∑' k, (∑_{P ∈ W^k} m_{P,N} · d_{P,N}) = PartialSumLevels by ClaimI
    -- (reversing the role of the two grids in the sum-exchange argument).
    sorry
  · -- Part 2: coefficient cost bound
    -- Proof sketch:
    -- 1. Minkowski/triangle in ℓ^p: m_{P,N} ≤ ∑_i ∑_{Q ⊇ P, Q ∈ G^i} |c_Q| |s_{P,Q}|
    -- 2. Bound |s_{P,Q}| = |coeff (R i Q) P| using hR: |s_{P,Q}| ≤ √(C · λ^{j-k(i)})^{1/p}
    --    (via levelCoeffPower ≤ C · λ^{j - k(i)})
    -- 3. Use the multiplicity bound G.grid.Cmult1 to control ∑_{Q ⊇ P}
    -- 4. Use hk_upper (k(i) ≤ r·i + B) to get λ^{-B} factor
    -- 5. Sum over P ∈ W^k, then over k, using cCoefficient for the weight sequence
    --    and geometric series for the λ decay
    sorry


end -- closes noncomputable section

end WeakGridSpace
