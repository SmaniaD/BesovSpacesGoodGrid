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


end -- closes noncomputable section

end WeakGridSpace
