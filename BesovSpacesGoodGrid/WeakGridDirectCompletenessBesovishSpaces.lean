import BesovSpacesGoodGrid.WeakGridBesovishSpaces
import BesovSpacesGoodGrid.WeakGridDirectBesovishSpaces

/-!
# Completeness layer for direct `L^p` Besov-ish spaces

This file is the parallel home for the completeness development of the direct
`L^p` Besov-ish API.  The current layer records the coefficient-cost gauge
facts that will be used to build the direct cost norm and, later, the complete
space instance.
-/

namespace WeakGridSpace

open scoped ENNReal Topology
open MeasureTheory
open Filter

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

variable {G : WeakGridSpace (α := α)} {s : ℝ} {p q : ℝ≥0∞}
variable [Fact (1 ≤ p)] [Fact (1 ≤ q)]

namespace DirectLpBesovishSpace

/-- Level weight for the direct `L^p` embedding at exponent `p`. -/
noncomputable def directLevelLpWeight
    (G : WeakGridSpace (α := α)) (s : ℝ) (_p : ℝ≥0∞) (k : ℕ) : ℝ :=
  ∑ Q : LevelCell G k, (G.measure Q.1).toReal ^ s

/-- The direct level weight is nonnegative. -/
theorem directLevelLpWeight_nonneg
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) (k : ℕ) :
    0 ≤ directLevelLpWeight G s p k := by
  unfold directLevelLpWeight
  exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg ENNReal.toReal_nonneg _

/--
Direct analogue of assumption `A5`: each cell atom set is sequentially compact
in the ambient strong `L^p` topology.
-/
def DirectAssumptionA5 (A : LpAtomFamily G s p) : Prop :=
  1 ≤ p ∧ p ≠ ∞ ∧
    ∀ Q : WeakGridCell G, IsSeqCompact (A.atoms Q)

/-- Direct tail coefficient weight, zero below level `N`. -/
noncomputable def directTailCoefficientWeight
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) (N k : ℕ) : ℝ :=
  if k < N then 0 else (directLevelLpWeight G s p k) ^ p.toReal

/-- The direct tail `C_co` coefficient for levels `k ≥ N`. -/
noncomputable def directTailCCoefficient
    (G : WeakGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) : ℝ :=
  LpGridRepresentation.cCoefficient p q (directTailCoefficientWeight G s p N)

/-- Direct tail weights are nonnegative. -/
theorem directTailCoefficientWeight_nonneg
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) (N k : ℕ) :
    0 ≤ directTailCoefficientWeight G s p N k := by
  unfold directTailCoefficientWeight
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (directLevelLpWeight_nonneg G s p k) _

/--
Direct analogue of assumption `G2` for the `L^p`-ambient API.

The first component is the global direct `C_co` finiteness needed for the
embedding.  The second component is the tail vanishing needed for strong
compactness of closed cost balls.
-/
def DirectAssumptionG2
    (G : WeakGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞) : Prop :=
  LpGridRepresentation.cCoefficientFinite p q
      (fun k => (directLevelLpWeight G s p k) ^ p.toReal) ∧
    (∀ N, LpGridRepresentation.cCoefficientFinite p q
      (directTailCoefficientWeight G s p N)) ∧
    Tendsto (fun N => directTailCCoefficient G s p q N) atTop (𝓝 0)

/-- A single coefficient is controlled by the level `ℓ^p` coefficient power. -/
theorem coeff_norm_le_levelCoeffPower_rpow
    {A : LpAtomFamily G s p} {k : ℕ}
    (B : LpLevelBlock A k) (Q : LevelCell G k) :
    ‖B.coeff Q‖ ≤
      (∑ R : LevelCell G k, ‖B.coeff R‖ ^ p.toReal) ^ (1 / p.toReal) := by
  have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  have hterm_le :
      ‖B.coeff Q‖ ^ p.toReal ≤
        ∑ R : LevelCell G k, ‖B.coeff R‖ ^ p.toReal := by
    exact Finset.single_le_sum
      (fun R _ => Real.rpow_nonneg (norm_nonneg (B.coeff R)) _)
      (Finset.mem_univ Q)
  calc
    ‖B.coeff Q‖
        = (‖B.coeff Q‖ ^ p.toReal) ^ (1 / p.toReal) := by
            symm
            simpa [one_div] using
              (Real.rpow_rpow_inv (norm_nonneg (B.coeff Q)) hp_pos.ne')
    _ ≤ (∑ R : LevelCell G k, ‖B.coeff R‖ ^ p.toReal) ^ (1 / p.toReal) :=
        Real.rpow_le_rpow
          (Real.rpow_nonneg (norm_nonneg (B.coeff Q)) _)
          hterm_le
          (one_div_nonneg.mpr hp_pos.le)

/--
A direct level block is bounded in ambient `L^p` by the level weight times its
coefficient `ℓ^p` size.
-/
theorem norm_LpLevelBlock_toLp_le_directLevelLpWeight_mul
    {A : LpAtomFamily G s p} {k : ℕ}
    (B : LpLevelBlock A k) :
    ‖B.toLp A‖ ≤
      directLevelLpWeight G s p k *
        (∑ Q : LevelCell G k, ‖B.coeff Q‖ ^ p.toReal) ^ (1 / p.toReal) := by
  let a : ℝ := (∑ Q : LevelCell G k, ‖B.coeff Q‖ ^ p.toReal) ^ (1 / p.toReal)
  have ha_nonneg : 0 ≤ a :=
    Real.rpow_nonneg (Finset.sum_nonneg fun Q _ =>
      Real.rpow_nonneg (norm_nonneg (B.coeff Q)) _) _
  have hterm :
      ∀ Q : LevelCell G k,
        ‖B.term A Q‖ ≤ a * ((G.measure Q.1).toReal ^ s) := by
    intro Q
    calc
      ‖B.term A Q‖ = ‖B.coeff Q‖ * ‖B.atom Q‖ := by
          simp [LpLevelBlock.term, norm_smul]
      _ ≤ a * ((G.measure Q.1).toReal ^ s) :=
          mul_le_mul
            (by simpa [a] using coeff_norm_le_levelCoeffPower_rpow (A := A) B Q)
            (A.atom_norm_bound (B.atom_mem Q))
            (norm_nonneg _)
            ha_nonneg
  calc
    ‖B.toLp A‖
        ≤ ∑ Q : LevelCell G k, ‖B.term A Q‖ := by
            simpa [LpLevelBlock.toLp] using
              norm_sum_le (G.grid.partitions k).attach (fun Q => B.term A Q)
    _ ≤ ∑ Q : LevelCell G k, a * ((G.measure Q.1).toReal ^ s) :=
        Finset.sum_le_sum fun Q _ => hterm Q
    _ = directLevelLpWeight G s p k * a := by
        simp [directLevelLpWeight, Finset.mul_sum, mul_comm]

/--
Direct `L^p` embedding for representations with `q = ∞`.

The constant is the summable series of direct level weights
`∑_k ∑_{Q ∈ P_k} μ(Q)^s`.  This theorem is deliberately direct: it uses only
ambient `L^p` atom bounds and does not pass through local Banach spaces.
-/
theorem lp_embedding_top_of_representation
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g)
    (hRfin : DirectLpGridRepresentation.FinitePQCost ∞ R)
    (hWeight : Summable fun k => directLevelLpWeight G s p k) :
    ‖g‖ ≤
      (∑' k, directLevelLpWeight G s p k) *
        DirectLpGridRepresentation.pqCost (q := ∞) R := by
  let w : ℕ → ℝ := fun k => directLevelLpWeight G s p k
  let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ p.toReal⁻¹
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact directLevelLpWeight_nonneg G s p k
  have ha_nonneg : ∀ k, 0 ≤ a k := by
    intro k
    exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
  have hC_def :
      DirectLpGridRepresentation.pqCost (q := ∞) R = sSup (Set.range a) := by
    simp [DirectLpGridRepresentation.pqCost, a]
  have ha_le_C : ∀ k, a k ≤ DirectLpGridRepresentation.pqCost (q := ∞) R := by
    intro k
    simpa [hC_def] using le_csSup hRfin ⟨k, rfl⟩
  have hprod_le :
      (fun k => w k * a k) ≤
        fun k => w k * DirectLpGridRepresentation.pqCost (q := ∞) R := by
    intro k
    exact mul_le_mul_of_nonneg_left (ha_le_C k) (hw_nonneg k)
  have hprod_sum : Summable (fun k => w k * a k) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (hw_nonneg k) (ha_nonneg k))
      hprod_le
      (hWeight.mul_right (DirectLpGridRepresentation.pqCost (q := ∞) R))
  have hblock_le : ∀ k, ‖(R.block k).toLp A‖ ≤ w k * a k := by
    intro k
    simpa [w, a, DirectLpGridRepresentation.levelCoeffPower, one_div] using
      norm_LpLevelBlock_toLp_le_directLevelLpWeight_mul (A := A) (R.block k)
  have hblock_sum : Summable fun k => ‖(R.block k).toLp A‖ :=
    Summable.of_nonneg_of_le
      (fun k => norm_nonneg ((R.block k).toLp A))
      hblock_le
      hprod_sum
  have hnorm_tsum :
      ‖g‖ ≤ ∑' k, ‖(R.block k).toLp A‖ := by
    have htsum_eq : (∑' k, (R.block k).toLp A) = g := R.hasSum.tsum_eq
    calc
      ‖g‖ = ‖∑' k, (R.block k).toLp A‖ := by rw [htsum_eq]
      _ ≤ ∑' k, ‖(R.block k).toLp A‖ :=
          norm_tsum_le_tsum_norm hblock_sum
  have htsum_block_le :
      (∑' k, ‖(R.block k).toLp A‖) ≤ ∑' k, w k * a k :=
    hblock_sum.tsum_le_tsum hblock_le hprod_sum
  have htsum_prod_le :
      (∑' k, w k * a k) ≤
        ∑' k, w k * DirectLpGridRepresentation.pqCost (q := ∞) R :=
    hprod_sum.tsum_le_tsum hprod_le
      (hWeight.mul_right (DirectLpGridRepresentation.pqCost (q := ∞) R))
  have htsum_scaled :
      (∑' k, w k * DirectLpGridRepresentation.pqCost (q := ∞) R) =
        (∑' k, w k) * DirectLpGridRepresentation.pqCost (q := ∞) R := by
    simpa [mul_comm] using
      (hWeight.hasSum.mul_right
        (DirectLpGridRepresentation.pqCost (q := ∞) R)).tsum_eq
  calc
    ‖g‖ ≤ ∑' k, ‖(R.block k).toLp A‖ := hnorm_tsum
    _ ≤ ∑' k, w k * a k := htsum_block_le
    _ ≤ ∑' k, w k * DirectLpGridRepresentation.pqCost (q := ∞) R := htsum_prod_le
    _ = (∑' k, w k) * DirectLpGridRepresentation.pqCost (q := ∞) R := htsum_scaled

/--
The direct weighted coefficient sequence is summable whenever the direct
`C_co(p,q,·)` weight condition and finite `(p,q)` representation cost hold.
-/
theorem direct_weighted_coeff_summable
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g)
    (hRfin : DirectLpGridRepresentation.FinitePQCost q R)
    (hCco_fin : LpGridRepresentation.cCoefficientFinite p q
      (fun k => (directLevelLpWeight G s p k) ^ p.toReal)) :
    Summable fun k =>
      directLevelLpWeight G s p k * (R.levelCoeffPower k) ^ (1 / p.toReal) := by
  let w : ℕ → ℝ := fun k => directLevelLpWeight G s p k
  let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
  have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  by_cases hq1 : q = 1
  · have hC_bdd :
        BddAbove (Set.range fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
      simpa [LpGridRepresentation.cCoefficientFinite, hq1, w] using hCco_fin
    let C : ℝ := LpGridRepresentation.cCoefficient p q (fun k => (w k) ^ p.toReal)
    have hC_def :
        C = sSup (Set.range fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
      simp [C, LpGridRepresentation.cCoefficient, hq1]
    have hw_le_C : ∀ k, w k ≤ C := by
      intro k
      have hk_nonneg : 0 ≤ w k := by
        simpa [w] using directLevelLpWeight_nonneg G s p k
      have hk_pow : ((w k) ^ p.toReal) ^ (1 / p.toReal) = w k := by
        simpa [one_div] using (Real.rpow_rpow_inv hk_nonneg hp_pos.ne')
      have hC_bdd' :
          BddAbove (Set.range fun k => ((w k) ^ p.toReal) ^ p.toReal⁻¹) := by
        simpa [one_div] using hC_bdd
      have hk_pow' : ((w k) ^ p.toReal) ^ p.toReal⁻¹ = w k := by
        simpa [one_div] using hk_pow
      have hk_le : ((w k) ^ p.toReal) ^ p.toReal⁻¹ ≤
          sSup (Set.range fun k => ((w k) ^ p.toReal) ^ p.toReal⁻¹) :=
        le_csSup hC_bdd' ⟨k, rfl⟩
      simpa [hC_def] using hk_pow' ▸ hk_le
    have hRsum : Summable a := by
      simpa [DirectLpGridRepresentation.FinitePQCost, hq1, a] using hRfin
    have hprod_le :
        (fun k => w k * a k) ≤ fun k => C * a k := by
      intro k
      have ha_nonneg : 0 ≤ a k := by
        simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
      exact mul_le_mul_of_nonneg_right (hw_le_C k) ha_nonneg
    exact Summable.of_nonneg_of_le
      (fun k => mul_nonneg
        (by simpa [w] using directLevelLpWeight_nonneg G s p k)
        (by simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
      hprod_le
      (hRsum.mul_left C)
  · by_cases hq_top : q = ∞
    · subst hq_top
      have hRbdd : BddAbove (Set.range a) := by
        simpa [DirectLpGridRepresentation.FinitePQCost, a] using hRfin
      let C : ℝ := DirectLpGridRepresentation.pqCost (q := ∞) R
      have hC_def : C = sSup (Set.range a) := by
        simp [C, DirectLpGridRepresentation.pqCost, a]
      have ha_le_C : ∀ k, a k ≤ C := by
        intro k
        simpa [hC_def] using le_csSup hRbdd ⟨k, rfl⟩
      have hWsum_raw :
          Summable fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal) := by
        simpa [LpGridRepresentation.cCoefficientFinite, w] using hCco_fin
      have hwpow : ∀ k, ((w k) ^ p.toReal) ^ (1 / p.toReal) = w k := by
        intro k
        have hw_nonneg : 0 ≤ w k := by
          simpa [w] using directLevelLpWeight_nonneg G s p k
        simpa [one_div] using (Real.rpow_rpow_inv hw_nonneg hp_pos.ne')
      have hWsum : Summable w := hWsum_raw.congr hwpow
      have hprod_le :
          (fun k => w k * a k) ≤ fun k => w k * C := by
        intro k
        exact mul_le_mul_of_nonneg_left (ha_le_C k)
          (by simpa [w] using directLevelLpWeight_nonneg G s p k)
      exact Summable.of_nonneg_of_le
        (fun k => mul_nonneg
          (by simpa [w] using directLevelLpWeight_nonneg G s p k)
          (by simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
        hprod_le
        (hWsum.mul_right C)
    · let q' : ℝ≥0∞ := q / (q - 1)
      have hq_one : 1 ≤ q := Fact.out
      have hq_toReal_le : (1 : ℝ) ≤ q.toReal := by
        have h := ENNReal.toReal_mono hq_top hq_one
        simpa using h
      have hq_toReal_ne_one : q.toReal ≠ 1 := by
        intro hreal
        apply hq1
        have hqeq : (1 : ℝ≥0∞) = q := by
          exact (ENNReal.toReal_eq_toReal_iff' ENNReal.one_ne_top hq_top).mp
            (by simp [hreal])
        exact hqeq.symm
      have hq_toReal_one : 1 < q.toReal :=
        lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
      have hCsum :
          Summable fun k => ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) := by
        simpa [LpGridRepresentation.cCoefficientFinite, hq1, hq_top, q', w] using hCco_fin
      have hAsum_raw :
          Summable fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
        simpa [DirectLpGridRepresentation.FinitePQCost, hq_top] using hRfin
      have hwpow :
          ∀ k, ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) = (w k) ^ q'.toReal := by
        intro k
        have hw_nonneg : 0 ≤ w k := by
          simpa [w] using directLevelLpWeight_nonneg G s p k
        have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
          field_simp [hp_pos.ne']
        calc
          ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal)
              = ((w k) ^ p.toReal) ^ ((1 / p.toReal) * q'.toReal) := by rw [hdiv]
          _ = (((w k) ^ p.toReal) ^ (1 / p.toReal)) ^ q'.toReal := by
                rw [Real.rpow_mul (Real.rpow_nonneg hw_nonneg _)]
          _ = (w k) ^ q'.toReal := by
                congr 1
                simpa [one_div] using (Real.rpow_rpow_inv hw_nonneg hp_pos.ne')
      have hApow :
          ∀ k, (a k) ^ q.toReal = (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
        intro k
        have hA_nonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
        have hdiv : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
          field_simp [hp_pos.ne']
        calc
          (a k) ^ q.toReal
              = ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ q.toReal := by rfl
          _ = (R.levelCoeffPower k) ^ ((1 / p.toReal) * q.toReal) := by
                rw [← Real.rpow_mul hA_nonneg]
          _ = (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by rw [hdiv]
      have hWsum : Summable fun k => (w k) ^ q'.toReal :=
        hCsum.congr hwpow
      have hAsum : Summable fun k => (a k) ^ q.toReal :=
        hAsum_raw.congr fun k => (hApow k).symm
      have hw_nonneg : ∀ k, 0 ≤ w k := by
        intro k
        simpa [w] using directLevelLpWeight_nonneg G s p k
      have ha_nonneg : ∀ k, 0 ≤ a k := by
        intro k
        simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
      have hq_conj : q'.toReal.HolderConjugate q.toReal := by
        simpa [q'] using LpGridRepresentation.holderConjugate_q_div_qsub1_toReal
          (q := q) hq_toReal_one hq_top
      exact Real.summable_mul_of_Lp_Lq_of_nonneg hq_conj hw_nonneg ha_nonneg hWsum hAsum

/--
Hölder estimate for the direct weighted coefficient sum, valid for all
`1 ≤ q ≤ ∞`.
-/
theorem direct_weighted_sum_le_cCoefficient_mul_pqCost
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g)
    (hRfin : DirectLpGridRepresentation.FinitePQCost q R)
    (hCco_fin : LpGridRepresentation.cCoefficientFinite p q
      (fun k => (directLevelLpWeight G s p k) ^ p.toReal)) :
    (∑' k, directLevelLpWeight G s p k *
        (R.levelCoeffPower k) ^ (1 / p.toReal)) ≤
      LpGridRepresentation.cCoefficient p q
          (fun k => (directLevelLpWeight G s p k) ^ p.toReal) *
        DirectLpGridRepresentation.pqCost (q := q) R := by
  let w : ℕ → ℝ := fun k => directLevelLpWeight G s p k
  let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
  have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  by_cases hq1 : q = 1
  · have hC_bdd :
        BddAbove (Set.range fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
      simpa [LpGridRepresentation.cCoefficientFinite, hq1, w] using hCco_fin
    let C : ℝ := LpGridRepresentation.cCoefficient p q (fun k => (w k) ^ p.toReal)
    have hC_def :
        C = sSup (Set.range fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
      simp [C, LpGridRepresentation.cCoefficient, hq1]
    have hw_le_C : ∀ k, w k ≤ C := by
      intro k
      have hk_nonneg : 0 ≤ w k := by
        simpa [w] using directLevelLpWeight_nonneg G s p k
      have hk_pow : ((w k) ^ p.toReal) ^ (1 / p.toReal) = w k := by
        simpa [one_div] using (Real.rpow_rpow_inv hk_nonneg hp_pos.ne')
      have hC_bdd' :
          BddAbove (Set.range fun k => ((w k) ^ p.toReal) ^ p.toReal⁻¹) := by
        simpa [one_div] using hC_bdd
      have hk_pow' : ((w k) ^ p.toReal) ^ p.toReal⁻¹ = w k := by
        simpa [one_div] using hk_pow
      have hk_le : ((w k) ^ p.toReal) ^ p.toReal⁻¹ ≤
          sSup (Set.range fun k => ((w k) ^ p.toReal) ^ p.toReal⁻¹) :=
        le_csSup hC_bdd' ⟨k, rfl⟩
      simpa [hC_def] using hk_pow' ▸ hk_le
    have hRsum : Summable a := by
      simpa [DirectLpGridRepresentation.FinitePQCost, hq1, a] using hRfin
    have hprod_le :
        (fun k => w k * a k) ≤ fun k => C * a k := by
      intro k
      have ha_nonneg : 0 ≤ a k := by
        simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
      exact mul_le_mul_of_nonneg_right (hw_le_C k) ha_nonneg
    have hprod_sum : Summable fun k => w k * a k :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg
          (by simpa [w] using directLevelLpWeight_nonneg G s p k)
          (by simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
        hprod_le
        (hRsum.mul_left C)
    have htsum_le :
        (∑' k, w k * a k) ≤ ∑' k, C * a k :=
      hprod_sum.tsum_le_tsum hprod_le (hRsum.mul_left C)
    have htsum_scaled : (∑' k, C * a k) = C * ∑' k, a k :=
      (hRsum.hasSum.mul_left C).tsum_eq
    have hpq_q1 : DirectLpGridRepresentation.pqCost (q := q) R = ∑' k, a k := by
      simp [DirectLpGridRepresentation.pqCost, hq1, a]
    calc
      (∑' k, directLevelLpWeight G s p k * (R.levelCoeffPower k) ^ (1 / p.toReal))
          = ∑' k, w k * a k := by rfl
      _ ≤ ∑' k, C * a k := htsum_le
      _ = C * ∑' k, a k := htsum_scaled
      _ = LpGridRepresentation.cCoefficient p q
            (fun k => (directLevelLpWeight G s p k) ^ p.toReal) *
          DirectLpGridRepresentation.pqCost (q := q) R := by
          simp [C, w, hpq_q1]
  · by_cases hq_top : q = ∞
    · subst hq_top
      have hRbdd : BddAbove (Set.range a) := by
        simpa [DirectLpGridRepresentation.FinitePQCost, a] using hRfin
      let C : ℝ := DirectLpGridRepresentation.pqCost (q := ∞) R
      have hC_def : C = sSup (Set.range a) := by
        simp [C, DirectLpGridRepresentation.pqCost, a]
      have ha_le_C : ∀ k, a k ≤ C := by
        intro k
        simpa [hC_def] using le_csSup hRbdd ⟨k, rfl⟩
      have hWsum_raw :
          Summable fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal) := by
        simpa [LpGridRepresentation.cCoefficientFinite, w] using hCco_fin
      have hwpow : ∀ k, ((w k) ^ p.toReal) ^ (1 / p.toReal) = w k := by
        intro k
        have hw_nonneg : 0 ≤ w k := by
          simpa [w] using directLevelLpWeight_nonneg G s p k
        simpa [one_div] using (Real.rpow_rpow_inv hw_nonneg hp_pos.ne')
      have hWsum : Summable w := hWsum_raw.congr hwpow
      have hprod_le :
          (fun k => w k * a k) ≤ fun k => w k * C := by
        intro k
        exact mul_le_mul_of_nonneg_left (ha_le_C k)
          (by simpa [w] using directLevelLpWeight_nonneg G s p k)
      have hprod_sum : Summable fun k => w k * a k :=
        Summable.of_nonneg_of_le
          (fun k => mul_nonneg
            (by simpa [w] using directLevelLpWeight_nonneg G s p k)
            (by simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
          hprod_le
          (hWsum.mul_right C)
      have htsum_le :
          (∑' k, w k * a k) ≤ ∑' k, w k * C :=
        hprod_sum.tsum_le_tsum hprod_le (hWsum.mul_right C)
      have htsum_scaled : (∑' k, w k * C) = (∑' k, w k) * C := by
        simpa [mul_comm] using (hWsum.hasSum.mul_right C).tsum_eq
      have hCco_rhs :
          LpGridRepresentation.cCoefficient p ∞ (fun k => (w k) ^ p.toReal) =
            ∑' k, w k := by
        rw [LpGridRepresentation.cCoefficient, if_neg (by simp), if_pos rfl]
        simpa using tsum_congr hwpow
      calc
        (∑' k, directLevelLpWeight G s p k * (R.levelCoeffPower k) ^ (1 / p.toReal))
            = ∑' k, w k * a k := by rfl
        _ ≤ ∑' k, w k * C := htsum_le
        _ = (∑' k, w k) * C := htsum_scaled
        _ = LpGridRepresentation.cCoefficient p ∞
              (fun k => (directLevelLpWeight G s p k) ^ p.toReal) *
            DirectLpGridRepresentation.pqCost (q := ∞) R := by
            simp [hCco_rhs, C, w]
    · let q' : ℝ≥0∞ := q / (q - 1)
      have hq_one : 1 ≤ q := Fact.out
      have hq_toReal_le : (1 : ℝ) ≤ q.toReal := by
        have h := ENNReal.toReal_mono hq_top hq_one
        simpa using h
      have hq_toReal_ne_one : q.toReal ≠ 1 := by
        intro hreal
        apply hq1
        have hqeq : (1 : ℝ≥0∞) = q := by
          exact (ENNReal.toReal_eq_toReal_iff' ENNReal.one_ne_top hq_top).mp
            (by simp [hreal])
        exact hqeq.symm
      have hq_toReal_one : 1 < q.toReal :=
        lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
      have hCsum :
          Summable fun k => ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) := by
        simpa [LpGridRepresentation.cCoefficientFinite, hq1, hq_top, q', w] using hCco_fin
      have hAsum_raw :
          Summable fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
        simpa [DirectLpGridRepresentation.FinitePQCost, hq_top] using hRfin
      have hwpow :
          ∀ k, ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) = (w k) ^ q'.toReal := by
        intro k
        have hw_nonneg : 0 ≤ w k := by
          simpa [w] using directLevelLpWeight_nonneg G s p k
        have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
          field_simp [hp_pos.ne']
        calc
          ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal)
              = ((w k) ^ p.toReal) ^ ((1 / p.toReal) * q'.toReal) := by rw [hdiv]
          _ = (((w k) ^ p.toReal) ^ (1 / p.toReal)) ^ q'.toReal := by
                rw [Real.rpow_mul (Real.rpow_nonneg hw_nonneg _)]
          _ = (w k) ^ q'.toReal := by
                congr 1
                simpa [one_div] using (Real.rpow_rpow_inv hw_nonneg hp_pos.ne')
      have hApow :
          ∀ k, (a k) ^ q.toReal = (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
        intro k
        have hA_nonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
        have hdiv : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
          field_simp [hp_pos.ne']
        calc
          (a k) ^ q.toReal
              = ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ q.toReal := by rfl
          _ = (R.levelCoeffPower k) ^ ((1 / p.toReal) * q.toReal) := by
                rw [← Real.rpow_mul hA_nonneg]
          _ = (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by rw [hdiv]
      have hWsum : Summable fun k => (w k) ^ q'.toReal :=
        hCsum.congr hwpow
      have hAsum : Summable fun k => (a k) ^ q.toReal :=
        hAsum_raw.congr fun k => (hApow k).symm
      have hw_nonneg : ∀ k, 0 ≤ w k := by
        intro k
        simpa [w] using directLevelLpWeight_nonneg G s p k
      have ha_nonneg : ∀ k, 0 ≤ a k := by
        intro k
        simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
      have hq_conj : q'.toReal.HolderConjugate q.toReal := by
        simpa [q'] using LpGridRepresentation.holderConjugate_q_div_qsub1_toReal
          (q := q) hq_toReal_one hq_top
      have hholder :=
        Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
          (p := q'.toReal) (q := q.toReal)
          hq_conj hw_nonneg ha_nonneg hWsum hAsum
      have hC_rhs :
          (∑' k, (w k) ^ q'.toReal) ^ (1 / q'.toReal) =
            LpGridRepresentation.cCoefficient p q (fun k => (w k) ^ p.toReal) := by
        rw [LpGridRepresentation.cCoefficient, if_neg hq1, if_neg hq_top]
        dsimp [q']
        congr 1
        exact tsum_congr fun k => (hwpow k).symm
      have hA_rhs :
          (∑' k, (a k) ^ q.toReal) ^ (1 / q.toReal) =
            DirectLpGridRepresentation.pqCost (q := q) R := by
        rw [DirectLpGridRepresentation.pqCost, if_neg hq_top]
        congr 1
        exact tsum_congr hApow
      calc
        (∑' k, directLevelLpWeight G s p k *
            (R.levelCoeffPower k) ^ (1 / p.toReal))
            = ∑' k, w k * a k := by rfl
        _ ≤ (∑' k, (w k) ^ q'.toReal) ^ (1 / q'.toReal) *
              (∑' k, (a k) ^ q.toReal) ^ (1 / q.toReal) := hholder
        _ = LpGridRepresentation.cCoefficient p q (fun k => (w k) ^ p.toReal) *
              DirectLpGridRepresentation.pqCost (q := q) R := by
            rw [hC_rhs, hA_rhs]
        _ = LpGridRepresentation.cCoefficient p q
              (fun k => (directLevelLpWeight G s p k) ^ p.toReal) *
              DirectLpGridRepresentation.pqCost (q := q) R := by
            rfl

/--
Weighted direct Hölder estimate with an arbitrary nonnegative weight sequence.
This is used for tail estimates by taking `b` to be zero below level `N`.
-/
theorem direct_weighted_sum_le_cCoefficient_mul_pqCost_of_weight
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (b : ℕ → ℝ) (hb_nonneg : ∀ k, 0 ≤ b k)
    (R : DirectLpGridRepresentation A g)
    (hRfin : DirectLpGridRepresentation.FinitePQCost q R)
    (hb_fin : LpGridRepresentation.cCoefficientFinite p q b) :
    Summable (fun k => b k ^ (1 / p.toReal) *
      (R.levelCoeffPower k) ^ (1 / p.toReal)) ∧
      (∑' k, b k ^ (1 / p.toReal) *
          (R.levelCoeffPower k) ^ (1 / p.toReal)) ≤
        LpGridRepresentation.cCoefficient p q b *
          DirectLpGridRepresentation.pqCost (q := q) R := by
  let w : ℕ → ℝ := fun k => b k ^ (1 / p.toReal)
  let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
  have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  by_cases hq1 : q = 1
  · have hC_bdd : BddAbove (Set.range fun k => b k ^ (1 / p.toReal)) := by
      simpa [LpGridRepresentation.cCoefficientFinite, hq1] using hb_fin
    let C : ℝ := LpGridRepresentation.cCoefficient p q b
    have hC_def : C = sSup (Set.range fun k => b k ^ (1 / p.toReal)) := by
      simp [C, LpGridRepresentation.cCoefficient, hq1]
    have hw_le_C : ∀ k, w k ≤ C := by
      intro k
      simpa [w, hC_def] using le_csSup hC_bdd ⟨k, rfl⟩
    have hRsum : Summable a := by
      simpa [DirectLpGridRepresentation.FinitePQCost, hq1, a] using hRfin
    have hprod_le :
        (fun k => w k * a k) ≤ fun k => C * a k := by
      intro k
      exact mul_le_mul_of_nonneg_right (hw_le_C k)
        (by simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _)
    have hprod_sum : Summable fun k => w k * a k :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg
          (by simpa [w] using Real.rpow_nonneg (hb_nonneg k) _)
          (by simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
        hprod_le
        (hRsum.mul_left C)
    have htsum_le :
        (∑' k, w k * a k) ≤ ∑' k, C * a k :=
      hprod_sum.tsum_le_tsum hprod_le (hRsum.mul_left C)
    have htsum_scaled : (∑' k, C * a k) = C * ∑' k, a k :=
      (hRsum.hasSum.mul_left C).tsum_eq
    have hpq_q1 : DirectLpGridRepresentation.pqCost (q := q) R = ∑' k, a k := by
      simp [DirectLpGridRepresentation.pqCost, hq1, a]
    refine ⟨by simpa [w, a] using hprod_sum, ?_⟩
    calc
      (∑' k, b k ^ (1 / p.toReal) *
          (R.levelCoeffPower k) ^ (1 / p.toReal))
          = ∑' k, w k * a k := by rfl
      _ ≤ ∑' k, C * a k := htsum_le
      _ = C * ∑' k, a k := htsum_scaled
      _ = LpGridRepresentation.cCoefficient p q b *
          DirectLpGridRepresentation.pqCost (q := q) R := by
          simp [C, hpq_q1]
  · by_cases hq_top : q = ∞
    · subst hq_top
      have hRbdd : BddAbove (Set.range a) := by
        simpa [DirectLpGridRepresentation.FinitePQCost, a] using hRfin
      let C : ℝ := DirectLpGridRepresentation.pqCost (q := ∞) R
      have hC_def : C = sSup (Set.range a) := by
        simp [C, DirectLpGridRepresentation.pqCost, a]
      have ha_le_C : ∀ k, a k ≤ C := by
        intro k
        simpa [hC_def] using le_csSup hRbdd ⟨k, rfl⟩
      have hWsum : Summable w := by
        simpa [LpGridRepresentation.cCoefficientFinite, w] using hb_fin
      have hprod_le :
          (fun k => w k * a k) ≤ fun k => w k * C := by
        intro k
        exact mul_le_mul_of_nonneg_left (ha_le_C k)
          (by simpa [w] using Real.rpow_nonneg (hb_nonneg k) _)
      have hprod_sum : Summable fun k => w k * a k :=
        Summable.of_nonneg_of_le
          (fun k => mul_nonneg
            (by simpa [w] using Real.rpow_nonneg (hb_nonneg k) _)
            (by simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
          hprod_le
          (hWsum.mul_right C)
      have htsum_le :
          (∑' k, w k * a k) ≤ ∑' k, w k * C :=
        hprod_sum.tsum_le_tsum hprod_le (hWsum.mul_right C)
      have htsum_scaled : (∑' k, w k * C) = (∑' k, w k) * C := by
        simpa [mul_comm] using (hWsum.hasSum.mul_right C).tsum_eq
      have hCco_rhs : LpGridRepresentation.cCoefficient p ∞ b = ∑' k, w k := by
        rw [LpGridRepresentation.cCoefficient, if_neg (by simp), if_pos rfl]
      refine ⟨by simpa [w, a] using hprod_sum, ?_⟩
      calc
        (∑' k, b k ^ (1 / p.toReal) *
            (R.levelCoeffPower k) ^ (1 / p.toReal))
            = ∑' k, w k * a k := by rfl
        _ ≤ ∑' k, w k * C := htsum_le
        _ = (∑' k, w k) * C := htsum_scaled
        _ = LpGridRepresentation.cCoefficient p ∞ b *
            DirectLpGridRepresentation.pqCost (q := ∞) R := by
            simp [hCco_rhs, C]
    · let q' : ℝ≥0∞ := q / (q - 1)
      have hq_one : 1 ≤ q := Fact.out
      have hq_toReal_le : (1 : ℝ) ≤ q.toReal := by
        have h := ENNReal.toReal_mono hq_top hq_one
        simpa using h
      have hq_toReal_ne_one : q.toReal ≠ 1 := by
        intro hreal
        apply hq1
        have hqeq : (1 : ℝ≥0∞) = q := by
          exact (ENNReal.toReal_eq_toReal_iff' ENNReal.one_ne_top hq_top).mp
            (by simp [hreal])
        exact hqeq.symm
      have hq_toReal_one : 1 < q.toReal :=
        lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
      have hCsum :
          Summable fun k => b k ^ (q'.toReal / p.toReal) := by
        simpa [LpGridRepresentation.cCoefficientFinite, hq1, hq_top, q'] using hb_fin
      have hAsum_raw :
          Summable fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
        simpa [DirectLpGridRepresentation.FinitePQCost, hq_top] using hRfin
      have hwpow : ∀ k, (w k) ^ q'.toReal = b k ^ (q'.toReal / p.toReal) := by
        intro k
        have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
          field_simp [hp_pos.ne']
        calc
          (w k) ^ q'.toReal
              = (b k ^ (1 / p.toReal)) ^ q'.toReal := by rfl
          _ = b k ^ ((1 / p.toReal) * q'.toReal) := by
                rw [← Real.rpow_mul (hb_nonneg k)]
          _ = b k ^ (q'.toReal / p.toReal) := by rw [hdiv]
      have hApow : ∀ k, (a k) ^ q.toReal =
          (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
        intro k
        have hdiv : q.toReal / p.toReal = (1 / p.toReal) * q.toReal := by
          field_simp [hp_pos.ne']
        calc
          (a k) ^ q.toReal
              = ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ q.toReal := by rfl
          _ = (R.levelCoeffPower k) ^ ((1 / p.toReal) * q.toReal) := by
                rw [← Real.rpow_mul (R.levelCoeffPower_nonneg k)]
          _ = (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by rw [hdiv]
      have hWsum : Summable fun k => (w k) ^ q'.toReal :=
        hCsum.congr fun k => (hwpow k).symm
      have hAsum : Summable fun k => (a k) ^ q.toReal :=
        hAsum_raw.congr fun k => (hApow k).symm
      have hw_nonneg : ∀ k, 0 ≤ w k := by
        intro k
        simpa [w] using Real.rpow_nonneg (hb_nonneg k) _
      have ha_nonneg : ∀ k, 0 ≤ a k := by
        intro k
        simpa [a] using Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
      have hq_conj : q'.toReal.HolderConjugate q.toReal := by
        simpa [q'] using LpGridRepresentation.holderConjugate_q_div_qsub1_toReal
          (q := q) hq_toReal_one hq_top
      have hprod_sum : Summable fun k => w k * a k :=
        Real.summable_mul_of_Lp_Lq_of_nonneg hq_conj hw_nonneg ha_nonneg hWsum hAsum
      have hholder :=
        Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
          (p := q'.toReal) (q := q.toReal)
          hq_conj hw_nonneg ha_nonneg hWsum hAsum
      have hC_rhs :
          (∑' k, (w k) ^ q'.toReal) ^ (1 / q'.toReal) =
            LpGridRepresentation.cCoefficient p q b := by
        rw [LpGridRepresentation.cCoefficient, if_neg hq1, if_neg hq_top]
        dsimp [q']
        congr 1
        exact tsum_congr hwpow
      have hA_rhs :
          (∑' k, (a k) ^ q.toReal) ^ (1 / q.toReal) =
            DirectLpGridRepresentation.pqCost (q := q) R := by
        rw [DirectLpGridRepresentation.pqCost, if_neg hq_top]
        congr 1
        exact tsum_congr hApow
      refine ⟨by simpa [w, a] using hprod_sum, ?_⟩
      calc
        (∑' k, b k ^ (1 / p.toReal) *
            (R.levelCoeffPower k) ^ (1 / p.toReal))
            = ∑' k, w k * a k := by rfl
        _ ≤ (∑' k, (w k) ^ q'.toReal) ^ (1 / q'.toReal) *
              (∑' k, (a k) ^ q.toReal) ^ (1 / q.toReal) := hholder
        _ = LpGridRepresentation.cCoefficient p q b *
              DirectLpGridRepresentation.pqCost (q := q) R := by
            rw [hC_rhs, hA_rhs]

/-- Coefficients of a direct representation sequence converge cellwise. -/
def DirectCoefficientsTendsto
    {A : LpAtomFamily G s p} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure}
    (Rseq : ∀ n, DirectLpGridRepresentation A (gseq n))
    (Rlim : DirectLpGridRepresentation A gLim) : Prop :=
  ∀ (k : ℕ) (Q : LevelCell G k),
    Tendsto (fun n => ((Rseq n).block k).coeff Q) atTop
      (𝓝 ((Rlim.block k).coeff Q))

/-- Atoms of a direct representation sequence converge strongly cellwise. -/
def DirectAtomsTendstoStrong
    {A : LpAtomFamily G s p} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure}
    (Rseq : ∀ n, DirectLpGridRepresentation A (gseq n))
    (Rlim : DirectLpGridRepresentation A gLim) : Prop :=
  ∀ (k : ℕ) (Q : LevelCell G k),
    Tendsto (fun n => ((Rseq n).block k).atom Q) atTop
      (𝓝 ((Rlim.block k).atom Q))

/-- Direct representation-limit hypotheses in the strong ambient topology. -/
structure DirectRepresentationLimitStrongHypotheses
    (A : LpAtomFamily G s p) (q : ℝ≥0∞)
    (gseq : ℕ → Lp ℂ p G.measure) (gLim : Lp ℂ p G.measure) (C : ℝ) where
  Rseq : ∀ n, DirectLpGridRepresentation A (gseq n)
  Rlim : DirectLpGridRepresentation A gLim
  uniform_bound :
    ∀ n, DirectLpGridRepresentation.pqCostENNReal (q := q) (Rseq n) ≤ ENNReal.ofReal C
  coeff_tendsto : DirectCoefficientsTendsto Rseq Rlim
  atom_tendsto : DirectAtomsTendstoStrong Rseq Rlim

omit [Fact (1 ≤ q)] in
/-- Level coefficient powers converge under cellwise coefficient convergence. -/
lemma direct_representation_limit_levelCoeffPower_tendsto
    {A : LpAtomFamily G s p} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : DirectRepresentationLimitStrongHypotheses A q gseq gLim C) (k : ℕ) :
    Tendsto (fun n => (H.Rseq n).levelCoeffPower k) atTop
      (𝓝 (H.Rlim.levelCoeffPower k)) := by
  unfold DirectLpGridRepresentation.levelCoeffPower
  refine tendsto_finsetSum Finset.univ ?_
  intro Q _hQ
  have hcoeff : Tendsto (fun n => ((H.Rseq n).block k).coeff Q) atTop
      (𝓝 ((H.Rlim.block k).coeff Q)) :=
    H.coeff_tendsto k Q
  have hnorm : Tendsto (fun n => ‖((H.Rseq n).block k).coeff Q‖) atTop
      (𝓝 ‖((H.Rlim.block k).coeff Q)‖) :=
    tendsto_norm.comp hcoeff
  exact (Real.continuousAt_rpow_const
      (x := ‖((H.Rlim.block k).coeff Q)‖) (q := p.toReal)
      (Or.inr ENNReal.toReal_nonneg)).tendsto.comp hnorm

/--
The extended direct coefficient cost of a limit representation is bounded by
the uniform extended-cost bound along the approximating sequence.
-/
private lemma direct_representation_limit_pqCostENNReal_le
    {A : LpAtomFamily G s p} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : DirectRepresentationLimitStrongHypotheses A q gseq gLim C) :
    DirectLpGridRepresentation.pqCostENNReal (q := q) H.Rlim ≤ ENNReal.ofReal C := by
  have hterm : ∀ (r : ℝ) (hr : 0 ≤ r) (k : ℕ),
      Tendsto (fun n => ENNReal.ofReal ((H.Rseq n).levelCoeffPower k ^ r)) atTop
        (𝓝 (ENNReal.ofReal (H.Rlim.levelCoeffPower k ^ r))) := fun r hr k => by
    exact (ENNReal.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const (x := H.Rlim.levelCoeffPower k)
        (q := r) (Or.inr hr))).tendsto.comp
      (direct_representation_limit_levelCoeffPower_tendsto H k)
  by_cases hq : q = ∞
  · simp only [DirectLpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    apply sSup_le
    rintro x ⟨k, rfl⟩
    apply le_of_tendsto' (hterm (1 / p.toReal)
      (div_nonneg zero_le_one ENNReal.toReal_nonneg) k)
    intro n
    have hbound := H.uniform_bound n
    simp only [DirectLpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hbound
    exact (le_sSup (Set.mem_range.mpr ⟨k, rfl⟩)).trans hbound
  · simp only [DirectLpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have hp_nonneg : 0 ≤ p.toReal := ENNReal.toReal_nonneg
    have h_tsum_le :
        ∑' k, ENNReal.ofReal (H.Rlim.levelCoeffPower k ^ (q.toReal / p.toReal))
          ≤ (ENNReal.ofReal C) ^ q.toReal := by
      rw [ENNReal.tsum_eq_iSup_nat]
      apply iSup_le
      intro N
      apply le_of_tendsto'
        (tendsto_finsetSum (Finset.range N) fun k _ =>
          hterm (q.toReal / p.toReal) (div_nonneg hq_pos.le hp_nonneg) k)
      intro n
      have hbound := H.uniform_bound n
      simp only [DirectLpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hbound
      have h1 := ENNReal.rpow_le_rpow hbound hq_pos.le
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hq_pos.ne', ENNReal.rpow_one] at h1
      exact (ENNReal.sum_le_tsum _).trans h1
    calc
      (∑' k, ENNReal.ofReal (H.Rlim.levelCoeffPower k ^ (q.toReal / p.toReal))) ^
          (1 / q.toReal)
          ≤ ((ENNReal.ofReal C) ^ q.toReal) ^ (1 / q.toReal) :=
            ENNReal.rpow_le_rpow h_tsum_le (div_nonneg zero_le_one hq_pos.le)
      _ = ENNReal.ofReal C := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hq_pos.ne', ENNReal.rpow_one]

/-- A finite extended-cost bound gives the same real direct `pqCost` bound. -/
private lemma direct_pqCost_le_of_pqCostENNReal_le
    {A : LpAtomFamily G s p} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {g : Lp ℂ p G.measure} {C : ℝ}
    (R : DirectLpGridRepresentation A g)
    (hENNReal : DirectLpGridRepresentation.pqCostENNReal (q := q) R ≤ ENNReal.ofReal C)
    (hC : 0 ≤ C) :
    DirectLpGridRepresentation.pqCost (q := q) R ≤ C := by
  have hfin := DirectLpGridRepresentation.finitePQCost_of_pqCostENNReal_le R
    (Fact.out : 1 ≤ q) hENNReal
  by_cases hq : q = ∞
  · simp only [DirectLpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [DirectLpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hfin
    simp only [DirectLpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hENNReal
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨k, rfl⟩
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp
      ((le_sSup (Set.mem_range.mpr ⟨k, rfl⟩)).trans hENNReal)
  · simp only [DirectLpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [DirectLpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hfin
    simp only [DirectLpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hENNReal
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have h_nonneg : ∀ k, 0 ≤ R.levelCoeffPower k ^ (q.toReal / p.toReal) :=
      fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
    rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg hfin,
        ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg h_nonneg)
          (div_nonneg zero_le_one hq_pos.le)] at hENNReal
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp hENNReal

/-- Real-cost and finite-cost data imply an extended direct cost bound. -/
private lemma direct_pqCostENNReal_le_of_finitePQCost_pqCost_le
    {A : LpAtomFamily G s p} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {g : Lp ℂ p G.measure} {C : ℝ}
    (R : DirectLpGridRepresentation A g)
    (hRfin : DirectLpGridRepresentation.FinitePQCost q R)
    (hcost : DirectLpGridRepresentation.pqCost (q := q) R ≤ C) :
    DirectLpGridRepresentation.pqCostENNReal (q := q) R ≤ ENNReal.ofReal C := by
  by_cases hq : q = ∞
  · simp only [DirectLpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    simp only [DirectLpGridRepresentation.pqCost, hq, ↓reduceIte] at hcost
    simp only [DirectLpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    apply sSup_le
    rintro x ⟨k, rfl⟩
    exact ENNReal.ofReal_le_ofReal ((le_csSup hRfin ⟨k, rfl⟩).trans hcost)
  · simp only [DirectLpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    simp only [DirectLpGridRepresentation.pqCost, hq, ↓reduceIte] at hcost
    simp only [DirectLpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have h_nonneg : ∀ k, 0 ≤ R.levelCoeffPower k ^ (q.toReal / p.toReal) :=
      fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
    rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg hRfin,
        ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg h_nonneg)
          (div_nonneg zero_le_one hq_pos.le)]
    exact ENNReal.ofReal_le_ofReal hcost

set_option maxHeartbeats 800000

omit [Fact (1 ≤ p)] in
/-- Direct coefficient diagonal compactness under coordinatewise boundedness. -/
lemma exists_direct_subseq_coeff_tendsto_of_coord_bounded
    {A : LpAtomFamily G s p}
    (Rseq : ℕ → (k : ℕ) → LpLevelBlock A k)
    (hbounded : ∀ (k : ℕ) (Q : LevelCell G k),
      BddAbove (Set.range fun n : ℕ => ‖(Rseq n k).coeff Q‖)) :
    ∃ (φ : ℕ → ℕ) (_hφ : StrictMono φ) (Rlim : (k : ℕ) → LpLevelBlock A k),
      ∀ (k : ℕ) (Q : LevelCell G k),
        Tendsto (fun n => (Rseq (φ n) k).coeff Q) atTop
          (𝓝 ((Rlim k).coeff Q)) := by
  classical
  let coord := Σ k : ℕ, LevelCell G k
  let radius : coord → ℝ := fun i => sSup (Set.range fun n : ℕ => ‖(Rseq n i.1).coeff i.2‖)
  have hmem : ∀ n i,
      (Rseq n i.1).coeff i.2 ∈ Metric.closedBall (0 : ℂ) (radius i) := by
    intro n i
    simp only [Metric.mem_closedBall, dist_zero_right, radius]
    exact le_csSup (hbounded i.1 i.2) ⟨n, rfl⟩
  let K : coord → Type _ := fun i => Metric.closedBall (0 : ℂ) (radius i)
  haveI : ∀ i : coord, CompactSpace (K i) := by
    intro i
    exact isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) (radius i))
  let xseq : ℕ → (∀ i : coord, K i) := fun n i => ⟨(Rseq n i.1).coeff i.2, hmem n i⟩
  rcases CompactSpace.tendsto_subseq xseq with ⟨xlim, φ, hφ, hxlim⟩
  let Rlim : (k : ℕ) → LpLevelBlock A k := fun k =>
    { coeff := fun Q => (xlim ⟨k, Q⟩ : K ⟨k, Q⟩)
      atom := fun Q => (Rseq 0 k).atom Q
      atom_mem := fun Q => (Rseq 0 k).atom_mem Q }
  refine ⟨φ, hφ, Rlim, ?_⟩
  intro k Q
  have hcoord :
      Tendsto (fun n => (xseq (φ n) ⟨k, Q⟩ : K ⟨k, Q⟩)) atTop
        (𝓝 (xlim ⟨k, Q⟩)) :=
    (continuous_apply ⟨k, Q⟩).continuousAt.tendsto.comp hxlim
  exact (continuous_subtype_val.tendsto _).comp hcoord

/-- Direct atom diagonal compactness from `DirectAssumptionA5`. -/
lemma exists_direct_subseq_atoms_tendsto_of_abstract
    {A : LpAtomFamily G s p}
    (hA5 : DirectAssumptionA5 (A := A))
    (Rseq : ℕ → (k : ℕ) → LpLevelBlock A k) :
    ∃ (φ : ℕ → ℕ) (_hφ : StrictMono φ) (Rlim : (k : ℕ) → LpLevelBlock A k),
      ∀ (k : ℕ) (Q : LevelCell G k),
        Tendsto (fun n => (Rseq (φ n) k).atom Q) atTop
          (𝓝 ((Rlim k).atom Q)) := by
  classical
  let coord := Σ k : ℕ, LevelCell G k
  let cell : coord → WeakGridCell G := fun i => levelCellToWeakGridCell G i.1 i.2
  have hmem : ∀ n i, (Rseq n i.1).atom i.2 ∈ A.atoms (cell i) := by
    intro n i
    exact (Rseq n i.1).atom_mem i.2
  let K : coord → Type _ := fun i => A.atoms (cell i)
  haveI : ∀ i : coord, CompactSpace (K i) := by
    intro i
    exact isCompact_iff_compactSpace.mp ((hA5.2.2 (cell i)).isCompact)
  let xseq : ℕ → (∀ i : coord, K i) := fun n i =>
    ⟨(Rseq n i.1).atom i.2, hmem n i⟩
  rcases CompactSpace.tendsto_subseq xseq with ⟨xlim, φ, hφ, hxlim⟩
  let Rlim : (k : ℕ) → LpLevelBlock A k := fun k =>
    { coeff := fun Q => (Rseq 0 k).coeff Q
      atom := fun Q => (xlim ⟨k, Q⟩ : K ⟨k, Q⟩)
      atom_mem := fun Q => (xlim ⟨k, Q⟩).2 }
  refine ⟨φ, hφ, Rlim, ?_⟩
  intro k Q
  have hcoord :
      Tendsto (fun n => (xseq (φ n) ⟨k, Q⟩ : K ⟨k, Q⟩)) atTop
        (𝓝 (xlim ⟨k, Q⟩)) :=
    (continuous_apply ⟨k, Q⟩).continuousAt.tendsto.comp hxlim
  exact (continuous_subtype_val.tendsto _).comp hcoord

/--
Uniform extended direct cost bounds give coordinatewise bounded coefficients.
-/
lemma direct_coeff_bounded_of_uniform_pqCostENNReal_le
    {A : LpAtomFamily G s p} {gseq : ℕ → Lp ℂ p G.measure}
    (Rseq : ∀ n, DirectLpGridRepresentation A (gseq n))
    {C : ℝ} (hC : 0 ≤ C)
    (uniform_bound : ∀ n,
      DirectLpGridRepresentation.pqCostENNReal (q := q) (Rseq n) ≤ ENNReal.ofReal C) :
    ∀ (k : ℕ) (Q : LevelCell G k),
      BddAbove (Set.range fun n : ℕ => ‖((Rseq n).block k).coeff Q‖) := by
  intro k Q
  refine ⟨C, ?_⟩
  rintro x ⟨n, rfl⟩
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' A.p_ne_top
  have hcoeff_power_le :
      ‖((Rseq n).block k).coeff Q‖ ^ p.toReal ≤ (Rseq n).levelCoeffPower k := by
    unfold DirectLpGridRepresentation.levelCoeffPower
    exact Finset.single_le_sum
      (fun Q _ => Real.rpow_nonneg (norm_nonneg (((Rseq n).block k).coeff Q)) _)
      (Finset.mem_univ Q)
  have hcoeff_le_level :
      ‖((Rseq n).block k).coeff Q‖ ≤
        (Rseq n).levelCoeffPower k ^ (1 / p.toReal) := by
    calc
      ‖((Rseq n).block k).coeff Q‖
          = (‖((Rseq n).block k).coeff Q‖ ^ p.toReal) ^ (1 / p.toReal) := by
            simpa [one_div] using
              (Real.rpow_rpow_inv (norm_nonneg (((Rseq n).block k).coeff Q))
                hp_pos.ne').symm
      _ ≤ ((Rseq n).levelCoeffPower k) ^ (1 / p.toReal) :=
          Real.rpow_le_rpow
            (Real.rpow_nonneg (norm_nonneg _) _) hcoeff_power_le
            (div_nonneg zero_le_one hp_pos.le)
  have hlevel_le_C :
      (Rseq n).levelCoeffPower k ^ (1 / p.toReal) ≤ C := by
    by_cases hq : q = ∞
    · have hbound := uniform_bound n
      simp only [DirectLpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hbound
      exact (ENNReal.ofReal_le_ofReal_iff hC).mp
        ((le_sSup (Set.mem_range.mpr ⟨k, rfl⟩)).trans hbound)
    · have hq_pos : 0 < q.toReal :=
        ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
      have hbound := uniform_bound n
      simp only [DirectLpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hbound
      have hpow := ENNReal.rpow_le_rpow hbound hq_pos.le
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hq_pos.ne', ENNReal.rpow_one] at hpow
      have hterm :
          ENNReal.ofReal ((Rseq n).levelCoeffPower k ^ (q.toReal / p.toReal))
            ≤ ENNReal.ofReal (C ^ q.toReal) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hC hq_pos.le]
        exact (ENNReal.le_tsum k).trans hpow
      have hreal :
          (Rseq n).levelCoeffPower k ^ (q.toReal / p.toReal) ≤ C ^ q.toReal :=
        (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hC _)).mp hterm
      have hroot := Real.rpow_le_rpow
        (Real.rpow_nonneg ((Rseq n).levelCoeffPower_nonneg k) _) hreal
        (div_nonneg zero_le_one hq_pos.le)
      calc
        (Rseq n).levelCoeffPower k ^ (1 / p.toReal)
            = ((Rseq n).levelCoeffPower k ^ (q.toReal / p.toReal)) ^
                (1 / q.toReal) := by
              rw [← Real.rpow_mul ((Rseq n).levelCoeffPower_nonneg k)]
              congr 1
              field_simp [hp_pos.ne', hq_pos.ne']
        _ ≤ (C ^ q.toReal) ^ (1 / q.toReal) := hroot
        _ = C := by
          simpa [one_div] using Real.rpow_rpow_inv hC hq_pos.ne'
  exact hcoeff_le_level.trans hlevel_le_C

/--
Sequential compactness core for uniformly bounded direct representations,
up to the construction of the represented `L^p` limit.

This extracts one subsequence along which all scalar coefficients and all
ambient atoms converge cellwise in the strong topology.
-/
theorem exists_direct_subseq_blocks_tendsto_of_uniform_pqCostENNReal
    {A : LpAtomFamily G s p}
    (hA5 : DirectAssumptionA5 (A := A))
    {gseq : ℕ → Lp ℂ p G.measure}
    (Rseq : ∀ n, DirectLpGridRepresentation A (gseq n))
    {C : ℝ}
    (hC : 0 ≤ C)
    (uniform_bound : ∀ n,
      DirectLpGridRepresentation.pqCostENNReal (q := q) (Rseq n) ≤ ENNReal.ofReal C) :
    ∃ (φ : ℕ → ℕ) (_hφ : StrictMono φ) (Rlim : (k : ℕ) → LpLevelBlock A k),
      (∀ (k : ℕ) (Q : LevelCell G k),
        Tendsto (fun n => ((Rseq (φ n)).block k).coeff Q) atTop
          (𝓝 ((Rlim k).coeff Q))) ∧
      (∀ (k : ℕ) (Q : LevelCell G k),
        Tendsto (fun n => ((Rseq (φ n)).block k).atom Q) atTop
          (𝓝 ((Rlim k).atom Q))) := by
  let Bseq : ℕ → (k : ℕ) → LpLevelBlock A k := fun n => (Rseq n).block
  have coeff_bounded : ∀ (k : ℕ) (Q : LevelCell G k),
      BddAbove (Set.range fun n : ℕ => ‖(Bseq n k).coeff Q‖) := by
    simpa [Bseq] using
      direct_coeff_bounded_of_uniform_pqCostENNReal_le
        (A := A) (q := q) Rseq hC uniform_bound
  rcases exists_direct_subseq_coeff_tendsto_of_coord_bounded
      (A := A) Bseq coeff_bounded with
    ⟨φc, hφc, RcoeffLim, hcoeff_lim⟩
  let Bseqc : ℕ → (k : ℕ) → LpLevelBlock A k := fun n => Bseq (φc n)
  rcases exists_direct_subseq_atoms_tendsto_of_abstract
      (A := A) hA5 Bseqc with
    ⟨φa, hφa, RatomLim, hatom_lim⟩
  let φ : ℕ → ℕ := φc ∘ φa
  have hφ : StrictMono φ := hφc.comp hφa
  let Rlim : (k : ℕ) → LpLevelBlock A k := fun k =>
    { coeff := (RcoeffLim k).coeff
      atom := (RatomLim k).atom
      atom_mem := (RatomLim k).atom_mem }
  have hcoeff_lim' : ∀ (k : ℕ) (Q : LevelCell G k),
      Tendsto (fun n => ((Rseq (φ n)).block k).coeff Q) atTop
        (𝓝 ((Rlim k).coeff Q)) := by
    intro k Q
    have hcoeff_to_Rcoeff :
        Tendsto (fun n => (Bseq (φc n) k).coeff Q) atTop
          (𝓝 ((RcoeffLim k).coeff Q)) :=
      hcoeff_lim k Q
    have hcoeff_to_Rcoeff_sub :
        Tendsto (fun n => (Bseq (φc (φa n)) k).coeff Q) atTop
          (𝓝 ((RcoeffLim k).coeff Q)) :=
      hcoeff_to_Rcoeff.comp hφa.tendsto_atTop
    simpa [φ, Bseq, Rlim] using hcoeff_to_Rcoeff_sub
  have hatom_lim' : ∀ (k : ℕ) (Q : LevelCell G k),
      Tendsto (fun n => ((Rseq (φ n)).block k).atom Q) atTop
        (𝓝 ((Rlim k).atom Q)) := by
    intro k Q
    simpa [φ, Bseq, Bseqc, Rlim] using hatom_lim k Q
  exact ⟨φ, hφ, Rlim, hcoeff_lim', hatom_lim'⟩

/--
Direct ambient `L^p` embedding for representations, valid for every
`1 ≤ q ≤ ∞` under the direct `C_co` finiteness condition.
-/
theorem lp_embedding_of_representation
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (R : DirectLpGridRepresentation A g)
    (hRfin : DirectLpGridRepresentation.FinitePQCost q R)
    (hCco_fin : LpGridRepresentation.cCoefficientFinite p q
      (fun k => (directLevelLpWeight G s p k) ^ p.toReal)) :
    ‖g‖ ≤
      LpGridRepresentation.cCoefficient p q
          (fun k => (directLevelLpWeight G s p k) ^ p.toReal) *
        DirectLpGridRepresentation.pqCost (q := q) R := by
  let w : ℕ → ℝ := fun k => directLevelLpWeight G s p k
  let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
  have hprod_sum : Summable fun k => w k * a k := by
    simpa [w, a] using
      direct_weighted_coeff_summable (A := A) (q := q) R hRfin hCco_fin
  have hweighted_bound :
      (∑' k, w k * a k) ≤
        LpGridRepresentation.cCoefficient p q (fun k => (w k) ^ p.toReal) *
          DirectLpGridRepresentation.pqCost (q := q) R := by
    simpa [w, a] using
      direct_weighted_sum_le_cCoefficient_mul_pqCost
        (A := A) (q := q) R hRfin hCco_fin
  have hblock_le : ∀ k, ‖(R.block k).toLp A‖ ≤ w k * a k := by
    intro k
    simpa [w, a, DirectLpGridRepresentation.levelCoeffPower, one_div] using
      norm_LpLevelBlock_toLp_le_directLevelLpWeight_mul (A := A) (R.block k)
  have hblock_sum : Summable fun k => ‖(R.block k).toLp A‖ :=
    Summable.of_nonneg_of_le
      (fun k => norm_nonneg ((R.block k).toLp A))
      hblock_le
      hprod_sum
  have hnorm_tsum :
      ‖g‖ ≤ ∑' k, ‖(R.block k).toLp A‖ := by
    have htsum_eq : (∑' k, (R.block k).toLp A) = g := R.hasSum.tsum_eq
    calc
      ‖g‖ = ‖∑' k, (R.block k).toLp A‖ := by rw [htsum_eq]
      _ ≤ ∑' k, ‖(R.block k).toLp A‖ :=
          norm_tsum_le_tsum_norm hblock_sum
  have htsum_block_le :
      (∑' k, ‖(R.block k).toLp A‖) ≤ ∑' k, w k * a k :=
    hblock_sum.tsum_le_tsum hblock_le hprod_sum
  calc
    ‖g‖ ≤ ∑' k, ‖(R.block k).toLp A‖ := hnorm_tsum
    _ ≤ ∑' k, w k * a k := htsum_block_le
    _ ≤ LpGridRepresentation.cCoefficient p q (fun k => (w k) ^ p.toReal) *
        DirectLpGridRepresentation.pqCost (q := q) R := hweighted_bound

/--
Direct tail embedding. If a representation has no coefficient mass below
level `N`, its ambient `L^p` norm is bounded by the direct tail coefficient.
-/
theorem direct_tail_embedding_bound
    {A : LpAtomFamily G s p} {g : Lp ℂ p G.measure}
    (hG2 : DirectAssumptionG2 G s p q)
    (R : DirectLpGridRepresentation A g)
    (hRfin : DirectLpGridRepresentation.FinitePQCost q R)
    (N : ℕ)
    (hzero : ∀ k, k < N → R.levelCoeffPower k = 0) :
    ‖g‖ ≤
      directTailCCoefficient G s p q N *
        DirectLpGridRepresentation.pqCost (q := q) R := by
  let b : ℕ → ℝ := directTailCoefficientWeight G s p N
  have hb_nonneg : ∀ k, 0 ≤ b k := by
    intro k
    exact directTailCoefficientWeight_nonneg G s p N k
  have hb_fin : LpGridRepresentation.cCoefficientFinite p q b := by
    simpa [b] using hG2.2.1 N
  have hweighted :=
    direct_weighted_sum_le_cCoefficient_mul_pqCost_of_weight
      (A := A) (q := q) b hb_nonneg R hRfin hb_fin
  have hprod_sum : Summable fun k =>
      b k ^ (1 / p.toReal) * (R.levelCoeffPower k) ^ (1 / p.toReal) :=
    hweighted.1
  have hp_pos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  let w : ℕ → ℝ := fun k => directLevelLpWeight G s p k
  let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
  have hblock_le : ∀ k,
      ‖(R.block k).toLp A‖ ≤ b k ^ (1 / p.toReal) * a k := by
    intro k
    by_cases hk : k < N
    · have ha_zero : a k = 0 := by
        simpa [a, hzero k hk, one_div] using
          Real.zero_rpow (inv_pos.mpr hp_pos).ne'
      calc
        ‖(R.block k).toLp A‖ ≤ w k * a k := by
          simpa [w, a, DirectLpGridRepresentation.levelCoeffPower, one_div] using
            norm_LpLevelBlock_toLp_le_directLevelLpWeight_mul (A := A) (R.block k)
        _ = b k ^ (1 / p.toReal) * a k := by simp [ha_zero]
    · have hkN : ¬ k < N := hk
      have hb_root : b k ^ (1 / p.toReal) = w k := by
        have hw_nonneg : 0 ≤ w k := by
          simpa [w] using directLevelLpWeight_nonneg G s p k
        simp [b, directTailCoefficientWeight, hkN, w]
        simpa [one_div] using (Real.rpow_rpow_inv hw_nonneg hp_pos.ne')
      calc
        ‖(R.block k).toLp A‖ ≤ w k * a k := by
          simpa [w, a, DirectLpGridRepresentation.levelCoeffPower, one_div] using
            norm_LpLevelBlock_toLp_le_directLevelLpWeight_mul (A := A) (R.block k)
        _ = b k ^ (1 / p.toReal) * a k := by rw [hb_root]
  have hblock_sum : Summable fun k => ‖(R.block k).toLp A‖ :=
    Summable.of_nonneg_of_le
      (fun k => norm_nonneg ((R.block k).toLp A))
      hblock_le
      (by simpa [b, a] using hprod_sum)
  have hnorm_tsum :
      ‖g‖ ≤ ∑' k, ‖(R.block k).toLp A‖ := by
    have htsum_eq : (∑' k, (R.block k).toLp A) = g := R.hasSum.tsum_eq
    calc
      ‖g‖ = ‖∑' k, (R.block k).toLp A‖ := by rw [htsum_eq]
      _ ≤ ∑' k, ‖(R.block k).toLp A‖ :=
          norm_tsum_le_tsum_norm hblock_sum
  have htsum_block_le :
      (∑' k, ‖(R.block k).toLp A‖) ≤
        ∑' k, b k ^ (1 / p.toReal) * a k :=
    hblock_sum.tsum_le_tsum hblock_le (by simpa [b, a] using hprod_sum)
  calc
    ‖g‖ ≤ ∑' k, ‖(R.block k).toLp A‖ := hnorm_tsum
    _ ≤ ∑' k, b k ^ (1 / p.toReal) * a k := htsum_block_le
    _ ≤ directTailCCoefficient G s p q N *
        DirectLpGridRepresentation.pqCost (q := q) R := by
          simpa [directTailCCoefficient, b, a] using hweighted.2

/--
The direct coefficient-cost gauge is available on every direct Besov-ish
vector, and it is nonnegative.

This is the first reusable package needed for the direct completeness proof:
the space already stores finite-cost direct representations in its carrier, so
the infimum defining `Norm_Costpq` is taken over a nonempty set.
-/
theorem costGauge_basic_properties (A : LpAtomFamily G s p) :
    HasFiniteCostRepresentations (A := A) q ∧
      (∀ g : DirectLpBesovishSpace A q, 0 ≤ Norm_Costpq A q g) ∧
      (∀ x y : DirectLpBesovishSpace A q,
        Norm_Costpq A q (x + y) ≤ Norm_Costpq A q x + Norm_Costpq A q y) ∧
      (∀ (c : ℂ) (x : DirectLpBesovishSpace A q),
        Norm_Costpq A q (c • x) = ‖c‖ * Norm_Costpq A q x) := by
  refine ⟨hasFiniteCostRepresentations A q, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g
    exact Norm_Costpq_nonneg
      (A := A) (q := q) (hasFiniteCostRepresentations A q) g
  · intro x y
    exact Norm_Costpq_add_le
      (A := A) (q := q) (hasFiniteCostRepresentations A q) x y
  · intro c x
    exact Norm_Costpq_smul_eq
      (A := A) (q := q) (hasFiniteCostRepresentations A q) c x

/--
Any admissible direct representation gives an upper bound for the direct
coefficient-cost gauge.
-/
theorem costGauge_le_representation
    {A : LpAtomFamily G s p} (g : DirectLpBesovishSpace A q)
    (R : DirectLpGridRepresentation A (g : Lp ℂ p G.measure))
    (hRfin : DirectLpGridRepresentation.FinitePQCost q R) :
    Norm_Costpq A q g ≤ DirectLpGridRepresentation.pqCost (q := q) R :=
  Norm_Costpq_le_cost (A := A) (q := q) g R hRfin

/--
Analytic separation hypothesis for the direct cost norm.

The algebraic gauge is already subadditive and homogeneous.  To turn it into a
genuine norm, we additionally require that it controls the ambient `L^p` norm.
This keeps the direct completeness layer honest: concrete atom families can
prove this bound from their size estimates and coefficient summability.
-/
def CostNormControlsLp (A : LpAtomFamily G s p) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : DirectLpBesovishSpace A q,
      ‖(g : Lp ℂ p G.measure)‖ ≤ C * Norm_Costpq A q g

/--
The direct `q = ∞` coefficient gauge controls the ambient `L^p` norm whenever
the direct level weights are summable.

This is the first concrete direct embedding theorem in the completeness layer.
It works only from the direct atom norm bound and the summability of
`∑_k ∑_{Q ∈ P_k} μ(Q)^s`; no local Banach-space norm is involved.
-/
theorem costNormControlsLp_top
    {A : LpAtomFamily G s p}
    (hWeight : Summable fun k => directLevelLpWeight G s p k) :
    CostNormControlsLp (A := A) ∞ := by
  let C : ℝ := ∑' k, directLevelLpWeight G s p k
  have hC_nonneg : 0 ≤ C := by
    exact tsum_nonneg fun k => directLevelLpWeight_nonneg G s p k
  refine ⟨C, hC_nonneg, ?_⟩
  intro g
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hεC : 0 < ε / (C + 1) := by
    have hden : 0 < C + 1 := by linarith
    positivity
  rcases exists_cost_lt_Norm_Costpq_add (A := A) (q := ∞)
      (hasFiniteCostRepresentations A ∞) g hεC with
    ⟨R, hRfin, hRlt⟩
  have hEmb :
      ‖(g : Lp ℂ p G.measure)‖ ≤
        C * DirectLpGridRepresentation.pqCost (q := ∞) R := by
    simpa [C] using
      lp_embedding_top_of_representation (A := A) R hRfin hWeight
  have hRle :
      DirectLpGridRepresentation.pqCost (q := ∞) R ≤
        Norm_Costpq A ∞ g + ε / (C + 1) :=
    le_of_lt hRlt
  have hmul :
      C * DirectLpGridRepresentation.pqCost (q := ∞) R ≤
        C * (Norm_Costpq A ∞ g + ε / (C + 1)) :=
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
    ‖(g : Lp ℂ p G.measure)‖
        ≤ C * DirectLpGridRepresentation.pqCost (q := ∞) R := hEmb
    _ ≤ C * (Norm_Costpq A ∞ g + ε / (C + 1)) := hmul
    _ = C * Norm_Costpq A ∞ g + C * (ε / (C + 1)) := by ring
    _ ≤ C * Norm_Costpq A ∞ g + ε := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hsmall (C * Norm_Costpq A ∞ g)

/--
The direct coefficient-cost gauge controls the ambient `L^p` norm for every
`1 ≤ q ≤ ∞`, provided the corresponding direct `C_co(p,q,·)` coefficient is
finite.
-/
theorem costNormControlsLp_of_cCoefficientFinite
    {A : LpAtomFamily G s p}
    (hCco_fin : LpGridRepresentation.cCoefficientFinite p q
      (fun k => (directLevelLpWeight G s p k) ^ p.toReal)) :
    CostNormControlsLp (A := A) q := by
  let C : ℝ :=
    LpGridRepresentation.cCoefficient p q
      (fun k => (directLevelLpWeight G s p k) ^ p.toReal)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact LpGridRepresentation.cCoefficient_nonneg p q
      (fun k => (directLevelLpWeight G s p k) ^ p.toReal)
      (fun k => Real.rpow_nonneg (directLevelLpWeight_nonneg G s p k) _)
  refine ⟨C, hC_nonneg, ?_⟩
  intro g
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hεC : 0 < ε / (C + 1) := by
    have hden : 0 < C + 1 := by linarith
    positivity
  rcases exists_cost_lt_Norm_Costpq_add (A := A) (q := q)
      (hasFiniteCostRepresentations A q) g hεC with
    ⟨R, hRfin, hRlt⟩
  have hEmb :
      ‖(g : Lp ℂ p G.measure)‖ ≤
        C * DirectLpGridRepresentation.pqCost (q := q) R := by
    simpa [C] using
      lp_embedding_of_representation (A := A) (q := q) R hRfin hCco_fin
  have hRle :
      DirectLpGridRepresentation.pqCost (q := q) R ≤
        Norm_Costpq A q g + ε / (C + 1) :=
    le_of_lt hRlt
  have hmul :
      C * DirectLpGridRepresentation.pqCost (q := q) R ≤
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
    ‖(g : Lp ℂ p G.measure)‖
        ≤ C * DirectLpGridRepresentation.pqCost (q := q) R := hEmb
    _ ≤ C * (Norm_Costpq A q g + ε / (C + 1)) := hmul
    _ = C * Norm_Costpq A q g + C * (ε / (C + 1)) := by ring
    _ ≤ C * Norm_Costpq A q g + ε := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hsmall (C * Norm_Costpq A q g)

/--
If the direct cost gauge controls the ambient `L^p` norm, then vanishing gauge
forces the represented `L^p` class to be zero.
-/
theorem eq_zero_of_Norm_Costpq_eq_zero
    {A : LpAtomFamily G s p}
    (hcontrol : CostNormControlsLp (A := A) q)
    {g : DirectLpBesovishSpace A q}
    (hg : Norm_Costpq A q g = 0) :
    g = 0 := by
  rcases hcontrol with ⟨C, _hC_nonneg, hC⟩
  have hLp : ‖(g : Lp ℂ p G.measure)‖ ≤ 0 := by
    calc
      ‖(g : Lp ℂ p G.measure)‖ ≤ C * Norm_Costpq A q g := hC g
      _ = 0 := by rw [hg, mul_zero]
  have hnorm_zero : ‖(g : Lp ℂ p G.measure)‖ = 0 :=
    le_antisymm hLp (norm_nonneg _)
  apply Subtype.ext
  exact norm_eq_zero.mp hnorm_zero

/--
The metric/normed additive group structure induced by the direct coefficient
cost gauge.

This is a named structure, not a global instance, because the submodule already
inherits the ambient `L^p` normed structure from Mathlib.
-/
@[reducible]
noncomputable def costNormedAddCommGroup
    {A : LpAtomFamily G s p}
    (hcontrol : CostNormControlsLp (A := A) q) :
    NormedAddCommGroup (DirectLpBesovishSpace A q) where
  norm := Norm_Costpq A q
  dist x y := Norm_Costpq A q (-x + y)
  dist_self := by
    intro x
    have h0 := Norm_Costpq_smul_eq (A := A) (q := q)
      (hasFiniteCostRepresentations (A := A) q) 0 x
    simpa using h0
  dist_comm := by
    intro x y
    have hcomm : x + -y = -y + x := by
      abel
    calc
      Norm_Costpq A q (-x + y)
          = Norm_Costpq A q ((-1 : ℂ) • (-x + y)) := by
              rw [Norm_Costpq_smul_eq (A := A) (q := q)
                (hasFiniteCostRepresentations (A := A) q) (-1) (-x + y)]
              simp
      _ = Norm_Costpq A q (-y + x) := by
        simp [hcomm]
  dist_triangle := by
    intro x y z
    have hsum : -x + z = (-x + y) + (-y + z) := by
      abel
    calc
      Norm_Costpq A q (-x + z)
          = Norm_Costpq A q ((-x + y) + (-y + z)) := by rw [hsum]
      _ ≤ Norm_Costpq A q (-x + y) + Norm_Costpq A q (-y + z) :=
        Norm_Costpq_add_le (A := A) (q := q)
          (hasFiniteCostRepresentations (A := A) q) (-x + y) (-y + z)
  eq_of_dist_eq_zero := by
    intro x y hxy
    have hzero : -x + y = 0 :=
      eq_zero_of_Norm_Costpq_eq_zero (A := A) (q := q) hcontrol hxy
    have h := congrArg (fun z : DirectLpBesovishSpace A q => x + z) hzero
    symm
    simpa [add_assoc] using h
  dist_eq := by
    intro x y
    rfl

/-- The direct coefficient-cost norm is definitionally the norm in `costNormedAddCommGroup`. -/
theorem costNormedAddCommGroup_norm
    {A : LpAtomFamily G s p}
    (hcontrol : CostNormControlsLp (A := A) q)
    (x : DirectLpBesovishSpace A q) :
    @norm (DirectLpBesovishSpace A q)
      (costNormedAddCommGroup (A := A) (q := q) hcontrol).toNorm x =
      Norm_Costpq A q x :=
  rfl

/--
Direct compactness hypothesis for closed coefficient-cost balls.

This is the local-Banach-free replacement for the old compactness input used
in the completeness proof.  It says that every sequence in a closed direct
cost ball has a subsequence converging strongly in the ambient `L^p` space to
another point of the same closed ball.
-/
def ClosedCostBallStrongSeqCompact (A : LpAtomFamily G s p) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] : Prop :=
  ∀ C : ℝ, 0 ≤ C →
    ∀ gseq : ℕ → DirectLpBesovishSpace A q,
      (∀ n, Norm_Costpq A q (gseq n) ≤ C) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ gLim : DirectLpBesovishSpace A q,
            Norm_Costpq A q gLim ≤ C ∧
              Tendsto
                (fun n => ((gseq (φ n) : DirectLpBesovishSpace A q) :
                  Lp ℂ p G.measure))
                atTop
                (𝓝 ((gLim : DirectLpBesovishSpace A q) : Lp ℂ p G.measure))

/--
A direct cost-Cauchy sequence converges in `Norm_Costpq` if closed direct cost
balls are strongly sequentially compact in ambient `L^p`.
-/
theorem Norm_Costpq_cauchySeq_tendsto_of_closedBallStrongSeqCompact
    {A : LpAtomFamily G s p}
    (hcompact : ClosedCostBallStrongSeqCompact (A := A) q)
    (gseq : ℕ → DirectLpBesovishSpace A q)
    (hcauchy : ∀ η > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      Norm_Costpq A q (gseq n - gseq m) < η) :
    ∃ gLim : DirectLpBesovishSpace A q,
      ∀ η > 0, ∃ N, ∀ n ≥ N,
        Norm_Costpq A q (gLim - gseq n) < η := by
  classical
  rcases hcauchy 1 zero_lt_one with ⟨N0, hN0⟩
  let C : ℝ :=
    Norm_Costpq A q (gseq N0) + 1 +
      ∑ n ∈ Finset.range N0, Norm_Costpq A q (gseq n)
  have hC_nonneg : 0 ≤ C := by
    have hbase : 0 ≤ Norm_Costpq A q (gseq N0) :=
      Norm_Costpq_nonneg (A := A) (q := q)
        (hasFiniteCostRepresentations (A := A) q) (gseq N0)
    have hsum_nonneg :
        0 ≤ ∑ n ∈ Finset.range N0, Norm_Costpq A q (gseq n) :=
      Finset.sum_nonneg fun n _ =>
        Norm_Costpq_nonneg (A := A) (q := q)
          (hasFiniteCostRepresentations (A := A) q) (gseq n)
    linarith
  have hball : ∀ n, Norm_Costpq A q (gseq n) ≤ C := by
    intro n
    by_cases hn : N0 ≤ n
    · have hdiff : Norm_Costpq A q (gseq n - gseq N0) < 1 :=
        hN0 N0 le_rfl n hn
      have htri :=
        Norm_Costpq_add_le
          (A := A) (q := q)
          (hasFiniteCostRepresentations (A := A) q)
          (gseq n - gseq N0) (gseq N0)
      have hsum_nonneg :
          0 ≤ ∑ n ∈ Finset.range N0, Norm_Costpq A q (gseq n) :=
        Finset.sum_nonneg fun n _ =>
          Norm_Costpq_nonneg (A := A) (q := q)
            (hasFiniteCostRepresentations (A := A) q) (gseq n)
      calc
        Norm_Costpq A q (gseq n)
            = Norm_Costpq A q ((gseq n - gseq N0) + gseq N0) := by
                congr 1
                abel
        _ ≤ Norm_Costpq A q (gseq n - gseq N0) +
              Norm_Costpq A q (gseq N0) := htri
        _ ≤ C := by
              dsimp [C]
              linarith
    · have hnmem : n ∈ Finset.range N0 := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
      have hterm_le :
          Norm_Costpq A q (gseq n) ≤
            ∑ m ∈ Finset.range N0, Norm_Costpq A q (gseq m) := by
        exact Finset.single_le_sum
          (fun m _ => Norm_Costpq_nonneg (A := A) (q := q)
            (hasFiniteCostRepresentations (A := A) q) (gseq m))
          hnmem
      have hbase_nonneg : 0 ≤ Norm_Costpq A q (gseq N0) :=
        Norm_Costpq_nonneg (A := A) (q := q)
          (hasFiniteCostRepresentations (A := A) q) (gseq N0)
      dsimp [C]
      linarith
  rcases hcompact C hC_nonneg gseq hball with
    ⟨φ, hφ, gLim, _hLim_ball, hLp_tendsto⟩
  refine ⟨gLim, ?_⟩
  intro η hη
  let δ : ℝ := η / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  rcases hcauchy δ hδ_pos with ⟨N, hN⟩
  refine ⟨N, fun i hi => ?_⟩
  have hφ_eventually : ∀ᶠ k in atTop, N ≤ φ k :=
    hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
  rcases eventually_atTop.1 hφ_eventually with ⟨K, hK⟩
  let dseq : ℕ → DirectLpBesovishSpace A q := fun k => gseq (φ (k + K)) - gseq i
  have hdseq_ball : ∀ k, Norm_Costpq A q (dseq k) ≤ δ := by
    intro k
    have hφN : N ≤ φ (k + K) := hK (k + K) (Nat.le_add_left K k)
    exact le_of_lt (by simpa [dseq] using hN i hi (φ (k + K)) hφN)
  rcases hcompact δ hδ_pos.le dseq hdseq_ball with
    ⟨χ, hχ, hDiffLim, hDiffNorm, hDiffLp_tendsto⟩
  have hidx_tendsto : Tendsto (fun n : ℕ => χ n + K) atTop atTop :=
    (tendsto_add_atTop_nat K).comp hχ.tendsto_atTop
  have hLp_diff_to_expected :
      Tendsto
        (fun n => ((dseq (χ n) : DirectLpBesovishSpace A q) : Lp ℂ p G.measure))
        atTop
        (𝓝 (((gLim - gseq i : DirectLpBesovishSpace A q) : Lp ℂ p G.measure))) := by
    have hsubseq :
        Tendsto
          (fun n => ((gseq (φ (χ n + K)) : DirectLpBesovishSpace A q) :
            Lp ℂ p G.measure))
          atTop
          (𝓝 ((gLim : DirectLpBesovishSpace A q) : Lp ℂ p G.measure)) :=
      hLp_tendsto.comp hidx_tendsto
    simpa [dseq] using hsubseq.sub tendsto_const_nhds
  have hDiff_eq : hDiffLim = gLim - gseq i := by
    apply Subtype.ext
    exact tendsto_nhds_unique hDiffLp_tendsto hLp_diff_to_expected
  have htarget_norm :
      Norm_Costpq A q (gLim - gseq i) ≤ δ := by
    simpa [hDiff_eq] using hDiffNorm
  have hδ_lt_eta : δ < η := by
    dsimp [δ]
    linarith
  exact lt_of_le_of_lt htarget_norm hδ_lt_eta

/--
Completeness criterion for the direct Besov-ish coefficient-cost norm.

The theorem is intentionally stated with `ClosedCostBallStrongSeqCompact` as a
separate hypothesis.  For concrete direct atom families, such as the Souza
atoms, the next task is to prove that compactness hypothesis from the geometry
of the atom sets.
-/
theorem costNorm_completeSpace_of_closedBallStrongSeqCompact
    {A : LpAtomFamily G s p}
    (hcontrol : CostNormControlsLp (A := A) q)
    (hcompact : ClosedCostBallStrongSeqCompact (A := A) q) :
    @CompleteSpace (DirectLpBesovishSpace A q)
      (costNormedAddCommGroup
        (A := A) (q := q) hcontrol).toMetricSpace.toPseudoMetricSpace.toUniformSpace := by
  classical
  letI : NormedAddCommGroup (DirectLpBesovishSpace A q) :=
    costNormedAddCommGroup (A := A) (q := q) hcontrol
  refine @Metric.complete_of_cauchySeq_tendsto (DirectLpBesovishSpace A q)
    (costNormedAddCommGroup
      (A := A) (q := q) hcontrol).toMetricSpace.toPseudoMetricSpace ?_
  intro gseq hgseq
  have hcauchy : ∀ η > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      Norm_Costpq A q (gseq n - gseq m) < η := by
    intro η hη
    have hgseq' :
        @CauchySeq (DirectLpBesovishSpace A q) ℕ
          (costNormedAddCommGroup
            (A := A) (q := q) hcontrol).toMetricSpace.toPseudoMetricSpace.toUniformSpace
          SemilatticeSup.toPartialOrder.toPreorder gseq := by
      exact hgseq
    rcases (@Metric.cauchySeq_iff (DirectLpBesovishSpace A q) ℕ
        (costNormedAddCommGroup
          (A := A) (q := q) hcontrol).toMetricSpace.toPseudoMetricSpace
        _ _ gseq).mp hgseq' η hη with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdist := hN m hm n hn
    change Norm_Costpq A q (-gseq m + gseq n) < η at hdist
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdist
  rcases Norm_Costpq_cauchySeq_tendsto_of_closedBallStrongSeqCompact
      (A := A) (q := q) hcompact gseq hcauchy with
    ⟨gLim, hlim⟩
  refine ⟨gLim, ?_⟩
  refine (@Metric.tendsto_atTop (DirectLpBesovishSpace A q) ℕ
    (costNormedAddCommGroup
      (A := A) (q := q) hcontrol).toMetricSpace.toPseudoMetricSpace
    _ _ gseq gLim).mpr ?_
  intro η hη
  rcases hlim η hη with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hcost : Norm_Costpq A q (gLim - gseq n) < η := hN n hn
  have hdist_cost :
      Norm_Costpq A q (-gseq n + gLim) < η := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hcost
  change Norm_Costpq A q (-gseq n + gLim) < η
  exact hdist_cost

end DirectLpBesovishSpace

end

end WeakGridSpace
