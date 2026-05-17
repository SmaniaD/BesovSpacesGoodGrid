import BesovSpacesGoodGrid.WeakGridAtomsDefinition
import BesovSpacesGoodGrid.WeakGridBesovishSpaces
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Topology.Algebra.InfiniteSum.NatInt




variable {α : Type*} [MeasurableSpace α]

namespace WeakGridSpace

open scoped BigOperators ENNReal Topology
open MeasureTheory
open Filter

noncomputable section

variable {G : WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
variable [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/--
Assumption G2: the coefficient-weight series `cCoefficientFinite p q (fun k => w_k ^ p.toReal)`
is finite, where `w_k = levelMeasureWeight G s p p k`, and the maximal level-cell
measure tends to zero.

This is needed to apply `lp_embedding_adapted_statement` with `t = p` and control the tail
of the atomic representation via the uniform pqCost bound.
-/
def AssumptionG2 (G : WeakGridSpace (α := α)) (s : ℝ) (p _u q : ℝ≥0∞) : Prop :=
  LpGridRepresentation.cCoefficientFinite p q
      (fun k => (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ∧
    Tendsto
      (fun k => sSup (Set.range fun Q : LevelCell G k => (G.measure Q.1).toReal))
      atTop
      (𝓝 0)

/-- Level weight used by the `t = p` embedding. -/
noncomputable def levelWeightP
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) (k : ℕ) : ℝ :=
  LpGridRepresentation.levelMeasureWeight G s p p k

/-- The `t = p` embedding coefficient weight, truncated to levels `k ≥ N`. -/
noncomputable def tailCoefficientWeight
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) (N k : ℕ) : ℝ :=
  if k < N then 0 else (levelWeightP G s p k) ^ p.toReal

/-- The `cCoefficient` of the level weights restricted to the tail `k ≥ N`. -/
noncomputable def tailCCoefficient
    (G : WeakGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) : ℝ :=
  LpGridRepresentation.cCoefficient p q (tailCoefficientWeight G s p N)

lemma levelWeightP_eq_mesh_rpow
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) (k : ℕ) :
    levelWeightP G s p k =
      (sSup (Set.range fun Q : LevelCell G k => (G.measure Q.1).toReal)) ^ s := by
  unfold levelWeightP LpGridRepresentation.levelMeasureWeight
  congr 1
  ring

lemma tailCoefficientWeight_nonneg
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) (N k : ℕ) :
    0 ≤ tailCoefficientWeight G s p N k := by
  unfold tailCoefficientWeight
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (LpGridRepresentation.levelMeasureWeight_nonneg G s p p k) _

private lemma weighted_sum_le_cCoefficient_mul_pqCost_of_weight
    {A : AtomFamily G s p u} {g : Lp ℂ p G.measure}
    (hp_ne_top : p ≠ ∞)
    (b : ℕ → ℝ) (hb_nonneg : ∀ k, 0 ≤ b k)
    (hq_one : 1 ≤ q)
    (R : LpGridRepresentation A g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R)
    (hb_fin : LpGridRepresentation.cCoefficientFinite p q b) :
    Summable (fun k => b k ^ (1 / p.toReal) *
      (R.levelCoeffPower k) ^ (1 / p.toReal)) ∧
      (∑' k, b k ^ (1 / p.toReal) *
          (R.levelCoeffPower k) ^ (1 / p.toReal)) ≤
        LpGridRepresentation.cCoefficient p q b *
          LpGridRepresentation.pqCost (q := q) R := by
  let w : ℕ → ℝ := fun k => b k ^ (1 / p.toReal)
  let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_ne_top
  by_cases hq1 : q = 1
  · have hb_bdd : BddAbove (Set.range fun k => b k ^ (1 / p.toReal)) := by
      simpa [LpGridRepresentation.cCoefficientFinite, hq1] using hb_fin
    let C : ℝ := LpGridRepresentation.cCoefficient p q b
    have hC_def : C = sSup (Set.range fun k => b k ^ (1 / p.toReal)) := by
      simp [C, LpGridRepresentation.cCoefficient, hq1]
    have hw_le_C : ∀ k, w k ≤ C := by
      intro k
      simpa [w, hC_def] using le_csSup hb_bdd ⟨k, rfl⟩
    have hRsum : Summable a := by
      simpa [LpGridRepresentation.FinitePQCost, hq1, a] using hRfin
    have hprod_le : (fun k => w k * a k) ≤ fun k => C * a k := by
      intro k
      exact mul_le_mul_of_nonneg_right (hw_le_C k)
        (by dsimp [a]; exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _)
    have hprod_sum : Summable (fun k => w k * a k) :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg
          (by dsimp [w]; exact Real.rpow_nonneg (hb_nonneg k) _)
          (by dsimp [a]; exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
        hprod_le
        (hRsum.mul_left C)
    have htsum_le : (∑' k, w k * a k) ≤ ∑' k, C * a k :=
      hprod_sum.tsum_le_tsum hprod_le (hRsum.mul_left C)
    have htsum_scaled : (∑' k, C * a k) = C * ∑' k, a k :=
      (hRsum.hasSum.mul_left C).tsum_eq
    have hpq_q1 : LpGridRepresentation.pqCost (q := q) R = ∑' k, a k := by
      simp [LpGridRepresentation.pqCost, hq1, a]
    refine ⟨by simpa [w, a] using hprod_sum, ?_⟩
    calc
      (∑' k, b k ^ (1 / p.toReal) * (R.levelCoeffPower k) ^ (1 / p.toReal))
          = ∑' k, w k * a k := by rfl
      _ ≤ ∑' k, C * a k := htsum_le
      _ = C * ∑' k, a k := htsum_scaled
      _ = LpGridRepresentation.cCoefficient p q b *
            LpGridRepresentation.pqCost (q := q) R := by
          simpa [C, hpq_q1]
  · by_cases hq_top : q = ∞
    · subst hq_top
      have hRbdd : BddAbove (Set.range a) := by
        simpa [LpGridRepresentation.FinitePQCost, a] using hRfin
      let C : ℝ := LpGridRepresentation.pqCost (q := ∞) R
      have hC_def : C = sSup (Set.range a) := by
        simp [C, LpGridRepresentation.pqCost, a]
      have ha_le_C : ∀ k, a k ≤ C := by
        intro k
        simpa [hC_def] using le_csSup hRbdd ⟨k, rfl⟩
      have hWsum : Summable w := by
        simpa [LpGridRepresentation.cCoefficientFinite, w] using hb_fin
      have hprod_le : (fun k => w k * a k) ≤ fun k => w k * C := by
        intro k
        exact mul_le_mul_of_nonneg_left (ha_le_C k)
          (by dsimp [w]; exact Real.rpow_nonneg (hb_nonneg k) _)
      have hprod_sum : Summable (fun k => w k * a k) :=
        Summable.of_nonneg_of_le
          (fun k => mul_nonneg
            (by dsimp [w]; exact Real.rpow_nonneg (hb_nonneg k) _)
            (by dsimp [a]; exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _))
          hprod_le
          (hWsum.mul_right C)
      have htsum_le : (∑' k, w k * a k) ≤ ∑' k, w k * C :=
        hprod_sum.tsum_le_tsum hprod_le (hWsum.mul_right C)
      have htsum_scaled : (∑' k, w k * C) = (∑' k, w k) * C := by
        simpa [mul_comm] using (hWsum.hasSum.mul_right C).tsum_eq
      have hCco_rhs : LpGridRepresentation.cCoefficient p ∞ b = ∑' k, w k := by
        simp [LpGridRepresentation.cCoefficient, w]
      refine ⟨by simpa [w, a] using hprod_sum, ?_⟩
      calc
        (∑' k, b k ^ (1 / p.toReal) * (R.levelCoeffPower k) ^ (1 / p.toReal))
            = ∑' k, w k * a k := by rfl
        _ ≤ ∑' k, w k * C := htsum_le
        _ = (∑' k, w k) * C := htsum_scaled
        _ = LpGridRepresentation.cCoefficient p ∞ b *
              LpGridRepresentation.pqCost (q := ∞) R := by
            simp [hCco_rhs, C]
    · let q' : ℝ≥0∞ := q / (q - 1)
      have hq_toReal_le : (1 : ℝ) ≤ q.toReal := by
        have h := ENNReal.toReal_mono hq_top hq_one
        simpa using h
      have hq_toReal_ne_one : q.toReal ≠ 1 := by
        intro hreal
        apply hq1
        have hqeq : (1 : ℝ≥0∞) = q :=
          (ENNReal.toReal_eq_toReal ENNReal.one_ne_top hq_top).mp (by simpa [hreal])
        exact hqeq.symm
      have hq_toReal_one : 1 < q.toReal :=
        lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
      have hBsum : Summable (fun k => b k ^ (q'.toReal / p.toReal)) := by
        simpa [LpGridRepresentation.cCoefficientFinite, hq1, hq_top, q'] using hb_fin
      have hAsum_raw : Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
        simpa [LpGridRepresentation.FinitePQCost, hq_top] using hRfin
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
      have hWsum : Summable (fun k => (w k) ^ q'.toReal) :=
        hBsum.congr (fun k => (hwpow k).symm)
      have hAsum : Summable (fun k => (a k) ^ q.toReal) :=
        hAsum_raw.congr (fun k => (hApow k).symm)
      have hq_conj : q'.toReal.HolderConjugate q.toReal := by
        simpa [q'] using LpGridRepresentation.holderConjugate_q_div_qsub1_toReal
          (q := q) hq_toReal_one hq_top
      have hw_nonneg : ∀ k, 0 ≤ w k := fun k => Real.rpow_nonneg (hb_nonneg k) _
      have ha_nonneg : ∀ k, 0 ≤ a k :=
        fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
      have hprod_sum : Summable (fun k => w k * a k) :=
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
            LpGridRepresentation.pqCost (q := q) R := by
        rw [LpGridRepresentation.pqCost, if_neg hq_top]
        congr 1
        exact tsum_congr hApow
      refine ⟨by simpa [w, a] using hprod_sum, ?_⟩
      calc
        (∑' k, b k ^ (1 / p.toReal) * (R.levelCoeffPower k) ^ (1 / p.toReal))
            = ∑' k, w k * a k := by rfl
        _ ≤ (∑' k, (w k) ^ q'.toReal) ^ (1 / q'.toReal) *
              (∑' k, (a k) ^ q.toReal) ^ (1 / q.toReal) := hholder
        _ = LpGridRepresentation.cCoefficient p q b *
              LpGridRepresentation.pqCost (q := q) R := by
            rw [hC_rhs, hA_rhs]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
lemma levelWeightP_tendsto_zero
    (hG2 : AssumptionG2 G s p u q) (hs_pos : 0 < s) :
    Tendsto (fun k => levelWeightP G s p k) atTop (𝓝 0) := by
  have hmesh := hG2.2
  have hpow :
      Tendsto
        (fun k => (sSup (Set.range fun Q : LevelCell G k => (G.measure Q.1).toReal)) ^ s)
        atTop (𝓝 ((0 : ℝ) ^ s)) :=
    (Real.continuousAt_rpow_const 0 s (Or.inr hs_pos.le)).tendsto.comp hmesh
  simpa [levelWeightP_eq_mesh_rpow, Real.zero_rpow hs_pos.ne'] using hpow

-- Lean's @[to_additive] of `tendsto_prod_nat_add` in NatInt.lean
-- gives `_root_.tendsto_sum_nat_add : Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0)`.
-- We alias it here under the cleaner name for use in `tailCCoefficient_tendsto_zero`.
private lemma tailSum_tendsto_zero (f : ℕ → ℝ) :
    Tendsto (fun N => ∑' k, f (k + N)) atTop (𝓝 0) :=
  tendsto_sum_nat_add f

private lemma tailCoefficientFinite
    (hG2 : AssumptionG2 G s p u q) (hp_ne_top : p ≠ ∞) (N : ℕ) :
    LpGridRepresentation.cCoefficientFinite p q (tailCoefficientWeight G s p N) := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_ne_top
  let b : ℕ → ℝ := fun k =>
    (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal
  have hb_nonneg : ∀ k, 0 ≤ b k := by
    intro k
    dsimp [b]
    exact Real.rpow_nonneg (LpGridRepresentation.levelMeasureWeight_nonneg G s p p k) _
  by_cases hq1 : q = 1
  · have hfull : BddAbove (Set.range fun k => b k ^ (1 / p.toReal)) := by
      simpa [AssumptionG2, LpGridRepresentation.cCoefficientFinite, hq1, b] using hG2.1
    have htailbdd :
        BddAbove (Set.range fun k => tailCoefficientWeight G s p N k ^ (1 / p.toReal)) := by
      rcases hfull with ⟨M, hM⟩
      refine ⟨max 0 M, ?_⟩
      intro x hx
      rcases hx with ⟨k, rfl⟩
      by_cases hk : k < N
      · have hzero : tailCoefficientWeight G s p N k ^ (1 / p.toReal) = 0 := by
          simp [tailCoefficientWeight, hk, Real.zero_rpow (inv_pos.mpr hp_pos).ne']
        calc
          (fun k => tailCoefficientWeight G s p N k ^ (1 / p.toReal)) k
              = 0 := hzero
          _ ≤ max 0 M := le_max_left 0 M
      · have heq : tailCoefficientWeight G s p N k = b k := by
          simp [tailCoefficientWeight, levelWeightP, b, hk]
        calc
          tailCoefficientWeight G s p N k ^ (1 / p.toReal)
              = b k ^ (1 / p.toReal) := by rw [heq]
          _ ≤ M := hM ⟨k, rfl⟩
          _ ≤ max 0 M := le_max_right 0 M
    simpa [LpGridRepresentation.cCoefficientFinite, hq1] using htailbdd
  · by_cases hq_top : q = ∞
    · have hfull : Summable (fun k => b k ^ (1 / p.toReal)) := by
        simpa [AssumptionG2, LpGridRepresentation.cCoefficientFinite, hq1, hq_top, b] using hG2.1
      have hle :
          (fun k => tailCoefficientWeight G s p N k ^ (1 / p.toReal)) ≤
            fun k => b k ^ (1 / p.toReal) := by
        intro k
        by_cases hk : k < N
        · simp [tailCoefficientWeight, hk, Real.zero_rpow (inv_pos.mpr hp_pos).ne',
            Real.rpow_nonneg (hb_nonneg k) _]
        · simp [tailCoefficientWeight, levelWeightP, b, hk]
      have hnonneg : ∀ k, 0 ≤ tailCoefficientWeight G s p N k ^ (1 / p.toReal) :=
        fun k => Real.rpow_nonneg (tailCoefficientWeight_nonneg G s p N k) _
      simpa [LpGridRepresentation.cCoefficientFinite, hq1, hq_top] using
        Summable.of_nonneg_of_le hnonneg hle hfull
    · let q' : ℝ≥0∞ := q / (q - 1)
      have hq_toReal_le : (1 : ℝ) ≤ q.toReal := by
        have h := ENNReal.toReal_mono hq_top (Fact.out : 1 ≤ q)
        simpa using h
      have hq_toReal_ne_one : q.toReal ≠ 1 := by
        intro hreal
        apply hq1
        have hqeq : (1 : ℝ≥0∞) = q :=
          (ENNReal.toReal_eq_toReal ENNReal.one_ne_top hq_top).mp (by simpa [hreal])
        exact hqeq.symm
      have hq_toReal_one : 1 < q.toReal :=
        lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
      have hq_conj : q'.toReal.HolderConjugate q.toReal := by
        simpa [q'] using LpGridRepresentation.holderConjugate_q_div_qsub1_toReal
          (q := q) hq_toReal_one hq_top
      have hq'_pos : 0 < q'.toReal := by
        rw [Real.holderConjugate_iff] at hq_conj
        exact zero_lt_one.trans hq_conj.1
      have hexp_pos : 0 < q'.toReal / p.toReal := div_pos hq'_pos hp_pos
      have hfull : Summable (fun k => b k ^ (q'.toReal / p.toReal)) := by
        simpa [AssumptionG2, LpGridRepresentation.cCoefficientFinite, hq1, hq_top, q', b]
          using hG2.1
      have hle :
          (fun k => tailCoefficientWeight G s p N k ^ (q'.toReal / p.toReal)) ≤
            fun k => b k ^ (q'.toReal / p.toReal) := by
        intro k
        by_cases hk : k < N
        · simp [tailCoefficientWeight, hk, Real.zero_rpow hexp_pos.ne',
            Real.rpow_nonneg (hb_nonneg k) _]
        · simp [tailCoefficientWeight, levelWeightP, b, hk]
      have hnonneg : ∀ k, 0 ≤ tailCoefficientWeight G s p N k ^ (q'.toReal / p.toReal) :=
        fun k => Real.rpow_nonneg (tailCoefficientWeight_nonneg G s p N k) _
      simpa [LpGridRepresentation.cCoefficientFinite, hq1, hq_top, q'] using
        Summable.of_nonneg_of_le hnonneg hle hfull

private lemma sharp_tail_embedding_bound
    {A : AtomFamily G s p u}
    (hG2 : AssumptionG2 G s p u q)
    (hp_ne_top : p ≠ ∞) (hu_one : 1 ≤ u) (hs_pos : 0 < s)
    {g : Lp ℂ p G.measure} (R : LpGridRepresentation A g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R)
    (N : ℕ) (hzero : ∀ k, k < N → R.levelCoeffPower k = 0) :
    ‖g‖ ≤
      ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
        tailCCoefficient G s p q N *
          LpGridRepresentation.pqCost (q := q) R := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_ne_top
  have ht_le_pu : p ≤ p * u := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * u := by exact mul_le_mul_right hu_one p
  have hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / p.toReal := by linarith [hs_pos.le]
  have htail_fin := tailCoefficientFinite (G := G) (s := s) (p := p) (u := u) (q := q)
    hG2 hp_ne_top N
  have hsharp :=
    weighted_sum_le_cCoefficient_mul_pqCost_of_weight
      (G := G) (s := s) (p := p) (u := u) (q := q) (A := A)
      hp_ne_top (tailCoefficientWeight G s p N)
      (tailCoefficientWeight_nonneg G s p N) (Fact.out : 1 ≤ q)
      R hRfin htail_fin
  have hterm_eq : ∀ k,
      LpGridRepresentation.levelMeasureWeight G s p p k *
          (R.levelCoeffPower k) ^ (1 / p.toReal) =
        tailCoefficientWeight G s p N k ^ (1 / p.toReal) *
          (R.levelCoeffPower k) ^ (1 / p.toReal) := by
    intro k
    by_cases hk : k < N
    · have hA0 : (R.levelCoeffPower k) ^ (1 / p.toReal) = 0 := by
        rw [hzero k hk]
        exact Real.zero_rpow (by positivity : 1 / p.toReal ≠ 0)
      rw [hA0, mul_zero, mul_zero]
    · have htail_pow :
          tailCoefficientWeight G s p N k ^ (1 / p.toReal) =
            LpGridRepresentation.levelMeasureWeight G s p p k := by
        have hw_nonneg : 0 ≤ LpGridRepresentation.levelMeasureWeight G s p p k :=
          LpGridRepresentation.levelMeasureWeight_nonneg G s p p k
        simp [tailCoefficientWeight, levelWeightP, hk,
          Real.rpow_rpow_inv hw_nonneg hp_pos.ne']
      rw [htail_pow]
  have hWeightSummable : Summable (fun k =>
      LpGridRepresentation.levelMeasureWeight G s p p k *
        (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
    exact hsharp.1.congr fun k => (hterm_eq k).symm
  have hWeightedBound :
      (∑' k, LpGridRepresentation.levelMeasureWeight G s p p k *
          (R.levelCoeffPower k) ^ (1 / p.toReal)) ≤
        tailCCoefficient G s p q N *
          LpGridRepresentation.pqCost (q := q) R := by
    calc
      (∑' k, LpGridRepresentation.levelMeasureWeight G s p p k *
          (R.levelCoeffPower k) ^ (1 / p.toReal))
          = ∑' k, tailCoefficientWeight G s p N k ^ (1 / p.toReal) *
              (R.levelCoeffPower k) ^ (1 / p.toReal) := tsum_congr hterm_eq
      _ ≤ tailCCoefficient G s p q N *
            LpGridRepresentation.pqCost (q := q) R := by
          simpa [tailCCoefficient] using hsharp.2
  let Cemb : ℝ := (G.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)
  have hCemb_nonneg : 0 ≤ Cemb := by positivity
  have hblock_bound : ∀ k,
      ‖(R.block k).toLt (t := p) A ht_le_pu‖ ≤
        Cemb * (LpGridRepresentation.levelMeasureWeight G s p p k *
          (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
    intro k
    have h :=
      LpGridRepresentation.lt_norm_levelBlock_le_of_atom_bound
        (G := G) (s := s) (p := p) (u := u) (A := A) (t := p)
        hp_ne_top hp_ne_top le_rfl ht_le_pu hs_nonneg R k
    simpa [Cemb, mul_assoc] using h
  have hSummableNorm : Summable fun k => ‖(R.block k).toLt (t := p) A ht_le_pu‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) hblock_bound ?_
    exact hWeightSummable.mul_left Cemb
  have hNormSumBound :
      (∑' k, ‖(R.block k).toLt (t := p) A ht_le_pu‖) ≤
        Cemb * tailCCoefficient G s p q N *
          LpGridRepresentation.pqCost (q := q) R := by
    have htsum_le :
        (∑' k, ‖(R.block k).toLt (t := p) A ht_le_pu‖) ≤
          ∑' k, Cemb * (LpGridRepresentation.levelMeasureWeight G s p p k *
            (R.levelCoeffPower k) ^ (1 / p.toReal)) :=
      hSummableNorm.tsum_le_tsum hblock_bound (hWeightSummable.mul_left Cemb)
    have hscaled :
        (∑' k, Cemb * (LpGridRepresentation.levelMeasureWeight G s p p k *
            (R.levelCoeffPower k) ^ (1 / p.toReal))) =
          Cemb * ∑' k, LpGridRepresentation.levelMeasureWeight G s p p k *
            (R.levelCoeffPower k) ^ (1 / p.toReal) :=
      (hWeightSummable.hasSum.mul_left Cemb).tsum_eq
    calc
      (∑' k, ‖(R.block k).toLt (t := p) A ht_le_pu‖)
          ≤ ∑' k, Cemb * (LpGridRepresentation.levelMeasureWeight G s p p k *
              (R.levelCoeffPower k) ^ (1 / p.toReal)) := htsum_le
      _ = Cemb * ∑' k, LpGridRepresentation.levelMeasureWeight G s p p k *
            (R.levelCoeffPower k) ^ (1 / p.toReal) := hscaled
      _ ≤ Cemb * (tailCCoefficient G s p q N *
            LpGridRepresentation.pqCost (q := q) R) :=
          mul_le_mul_of_nonneg_left hWeightedBound hCemb_nonneg
      _ = Cemb * tailCCoefficient G s p q N *
            LpGridRepresentation.pqCost (q := q) R := by ring
  let F : ℕ → Lp ℂ p G.measure := fun k => (R.block k).toLt (t := p) A ht_le_pu
  have hSummableF : Summable F := hSummableNorm.of_norm
  let h : Lp ℂ p G.measure := ∑' k, F k
  let I := LpGridRepresentation.lpInclusion (G := G) (p := p) (t := p)
    hp_ne_top hp_ne_top le_rfl
  have hHasSumI : HasSum (fun k => I (F k)) (I h) := by
    simpa [F, h] using hSummableF.hasSum.mapL I
  have hHasSumP : HasSum (fun k => (R.block k).toLp A) (I h) := by
    refine hHasSumI.congr_fun ?_
    intro k
    simpa [F] using (LpGridRepresentation.lpInclusion_levelBlock_toLt
      (G := G) (s := s) (p := p) (u := u) (A := A) (t := p)
      hp_ne_top hp_ne_top le_rfl ht_le_pu (R.block k)).symm
  have hIg : I h = g := HasSum.unique hHasSumP R.hasSum
  have hg_ae : (g : α → ℂ) =ᵐ[G.measure] h := by
    exact ((show (I h : α → ℂ) =ᵐ[G.measure] (g : α → ℂ) by simpa [hIg])).symm.trans
      (LpGridRepresentation.coeFn_lpInclusion (G := G) (p := p) (t := p)
        hp_ne_top hp_ne_top le_rfl h)
  have hnorm_h : ‖h‖ ≤ ∑' k, ‖F k‖ := by
    simpa [F, h] using norm_tsum_le_tsum_norm hSummableNorm
  calc
    ‖g‖ = (MeasureTheory.eLpNorm (g : α → ℂ) p G.measure).toReal := by
      rw [Lp.norm_def]
    _ = (MeasureTheory.eLpNorm (h : α → ℂ) p G.measure).toReal := by
      exact congrArg ENNReal.toReal (MeasureTheory.eLpNorm_congr_ae hg_ae)
    _ = ‖h‖ := by
      symm
      rw [Lp.norm_def]
    _ ≤ ∑' k, ‖F k‖ := hnorm_h
    _ = ∑' k, ‖(R.block k).toLt (t := p) A ht_le_pu‖ := by rfl
    _ ≤ ((G.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          tailCCoefficient G s p q N *
            LpGridRepresentation.pqCost (q := q) R := by
        simpa [Cemb] using hNormSumBound

/--
The `q = ∞` case of `tailCCoefficient → 0`:
`tailCCoefficient G s p ∞ N = ∑_{k≥N} w_k` and summability (from `AssumptionG2`) plus
`tendsto_sum_nat_add` give convergence to 0.
-/
lemma tailCCoefficient_tendsto_zero_q_top
    (hG2 : AssumptionG2 G s p u ∞) (hp_ne_top : p ≠ ∞) :
    Tendsto (fun N => tailCCoefficient G s p ∞ N) atTop (𝓝 0) := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_ne_top
  have hSummable_w : Summable (fun k => levelWeightP G s p k) := by
    have hfin : Summable fun k =>
        ((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
          (1 / p.toReal) := by
      simpa [AssumptionG2, LpGridRepresentation.cCoefficientFinite] using hG2.1
    convert hfin using 1
    ext k
    dsimp only [levelWeightP]
    have hw_nonneg : 0 ≤ LpGridRepresentation.levelMeasureWeight G s p p k :=
      LpGridRepresentation.levelMeasureWeight_nonneg G s p p k
    simpa [one_div] using (Real.rpow_rpow_inv hw_nonneg hp_pos.ne').symm
  have htCC_eq : ∀ N, tailCCoefficient G s p ∞ N =
      ∑' k, if k < N then 0 else levelWeightP G s p k := by
    intro N
    unfold tailCCoefficient LpGridRepresentation.cCoefficient tailCoefficientWeight levelWeightP
    simp only
    apply tsum_congr
    intro k
    by_cases hk : k < N
    · rw [if_pos hk, if_pos hk]
      simpa [one_div] using Real.zero_rpow (inv_pos.mpr hp_pos).ne'
    · simp only [hk, ↓reduceIte]
      have hw_nonneg : 0 ≤ LpGridRepresentation.levelMeasureWeight G s p p k :=
        LpGridRepresentation.levelMeasureWeight_nonneg G s p p k
      simpa [one_div] using Real.rpow_rpow_inv hw_nonneg hp_pos.ne'
  have htail_eq_shift : ∀ N,
      (∑' k, if k < N then 0 else levelWeightP G s p k) =
        ∑' k, levelWeightP G s p (k + N) := by
    intro N
    let f : ℕ → ℝ := fun k => levelWeightP G s p k
    let g : ℕ → ℝ := fun k => if k < N then 0 else f k
    have hg_summable : Summable g := by
      refine hSummable_w.norm.of_norm_bounded_eventually_nat ?_
      filter_upwards with k
      by_cases hk : k < N
      · simp [g, hk]
      · dsimp [g, f]
        rw [if_neg hk]
    have hsum_zero : (∑ k ∈ Finset.range N, g k) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      simp [g, Finset.mem_range.mp hk]
    have hshift_g : (fun k => g (k + N)) = fun k => f (k + N) := by
      funext k
      simp [g, f]
    have h := hg_summable.sum_add_tsum_nat_add N
    rw [hsum_zero, zero_add, hshift_g] at h
    exact h.symm
  rw [show (fun N => tailCCoefficient G s p ∞ N) =
      fun N => ∑' k, levelWeightP G s p (k + N) by
        funext N
        rw [htCC_eq N, htail_eq_shift N]]
  exact tailSum_tendsto_zero (fun k => levelWeightP G s p k)

/--
The `1 < q < ∞` case of `tailCCoefficient → 0`:
`tailCCoefficient G s p q N = (∑_{k≥N} w_k^{q'})^{1/q'}` and summability of `w_k^{q'}`
(from `AssumptionG2`) plus `tendsto_sum_nat_add` give convergence to 0.
-/
private lemma tailCCoefficient_tendsto_zero_q_pos
    (hG2 : AssumptionG2 G s p u q) (hp_ne_top : p ≠ ∞)
    (hq1 : q ≠ 1) (hqtop : q ≠ ∞) :
    Tendsto (fun N => tailCCoefficient G s p q N) atTop (𝓝 0) := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_ne_top
  have hq_toReal_one : 1 < q.toReal := by
    have h := ENNReal.toReal_mono hqtop (Fact.out : 1 ≤ q)
    simp at h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact hlt
    · exfalso
      exact hq1 ((ENNReal.toReal_eq_toReal_iff' ENNReal.one_ne_top hqtop).mp heq).symm
  let q' : ℝ≥0∞ := q / (q - 1)
  have hholder : q'.toReal.HolderConjugate q.toReal :=
    LpGridRepresentation.holderConjugate_q_div_qsub1_toReal hq_toReal_one hqtop
  have hq'_pos : 0 < q'.toReal := by
    rw [Real.holderConjugate_iff] at hholder
    exact zero_lt_one.trans hholder.1
  have hroot_pow : ∀ k,
      ((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
          (q'.toReal / p.toReal) =
        (levelWeightP G s p k) ^ q'.toReal := by
    intro k
    dsimp only [levelWeightP]
    have hw_nonneg : 0 ≤ LpGridRepresentation.levelMeasureWeight G s p p k :=
      LpGridRepresentation.levelMeasureWeight_nonneg G s p p k
    have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
      field_simp [hp_pos.ne']
    calc
      ((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
          (q'.toReal / p.toReal)
          = ((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
              ((1 / p.toReal) * q'.toReal) := by rw [hdiv]
      _ = (((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
              (1 / p.toReal)) ^ q'.toReal := by
            rw [Real.rpow_mul (Real.rpow_nonneg hw_nonneg _)]
      _ = (LpGridRepresentation.levelMeasureWeight G s p p k) ^ q'.toReal := by
            have hroot :
                ((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
                    (1 / p.toReal) =
                  LpGridRepresentation.levelMeasureWeight G s p p k := by
              simpa [one_div] using Real.rpow_rpow_inv hw_nonneg hp_pos.ne'
            rw [hroot]
  have hSummable_wq' : Summable (fun k => (levelWeightP G s p k) ^ q'.toReal) := by
    have hfin : Summable fun k =>
        ((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
          (q'.toReal / p.toReal) := by
      simpa [AssumptionG2, LpGridRepresentation.cCoefficientFinite, hq1, hqtop, q'] using hG2.1
    convert hfin using 1
    ext k
    exact (hroot_pow k).symm
  have htCC_eq : ∀ N, tailCCoefficient G s p q N =
      (∑' k, if k < N then 0 else (levelWeightP G s p k) ^ q'.toReal) ^
        (1 / q'.toReal) := by
    intro N
    unfold tailCCoefficient LpGridRepresentation.cCoefficient tailCoefficientWeight
    simp only [if_neg hq1, if_neg hqtop]
    congr 1
    apply tsum_congr
    intro k
    by_cases hk : k < N
    · rw [if_pos hk, if_pos hk]
      exact Real.zero_rpow (div_pos hq'_pos hp_pos).ne'
    · rw [if_neg hk, if_neg hk]
      exact hroot_pow k
  have htail_eq_shift : ∀ N,
      (∑' k, if k < N then 0 else (levelWeightP G s p k) ^ q'.toReal) =
        ∑' k, (levelWeightP G s p (k + N)) ^ q'.toReal := by
    intro N
    let f : ℕ → ℝ := fun k => (levelWeightP G s p k) ^ q'.toReal
    let g : ℕ → ℝ := fun k => if k < N then 0 else f k
    have hg_summable : Summable g := by
      refine hSummable_wq'.norm.of_norm_bounded_eventually_nat ?_
      filter_upwards with k
      by_cases hk : k < N
      · simp [g, hk]
      · dsimp [g, f]
        rw [if_neg hk]
    have hsum_zero : (∑ k ∈ Finset.range N, g k) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      simp [g, Finset.mem_range.mp hk]
    have hshift_g : (fun k => g (k + N)) = fun k => f (k + N) := by
      funext k
      simp [g, f]
    have h := hg_summable.sum_add_tsum_nat_add N
    rw [hsum_zero, zero_add, hshift_g] at h
    exact h.symm
  rw [show (fun N => tailCCoefficient G s p q N) =
      fun N => (∑' k, (levelWeightP G s p (k + N)) ^ q'.toReal) ^
        (1 / q'.toReal) by
        funext N
        rw [htCC_eq N, htail_eq_shift N]]
  have hshift_tendsto :
      Tendsto (fun N => ∑' k, (levelWeightP G s p (k + N)) ^ q'.toReal)
        atTop (𝓝 0) :=
    tailSum_tendsto_zero (fun k => (levelWeightP G s p k) ^ q'.toReal)
  have hcont : ContinuousAt (fun x : ℝ => x ^ (1 / q'.toReal)) 0 :=
    Real.continuousAt_rpow_const 0 (1 / q'.toReal)
      (Or.inr (div_pos one_pos hq'_pos).le)
  have hzero_rpow : (0 : ℝ) ^ (1 / q'.toReal) = 0 :=
    Real.zero_rpow (div_pos one_pos hq'_pos).ne'
  have htend := hcont.tendsto.comp hshift_tendsto
  change Tendsto
      (fun N => (∑' k, (levelWeightP G s p (k + N)) ^ q'.toReal) ^
        (1 / q'.toReal)) atTop (𝓝 ((0 : ℝ) ^ (1 / q'.toReal))) at htend
  have hzero_rpow_inv : (0 : ℝ) ^ q'.toReal⁻¹ = 0 := by
    simpa [one_div] using hzero_rpow
  simpa [one_div, hzero_rpow_inv] using htend

omit [Fact (1 ≤ q)] in
lemma tailCCoefficient_tendsto_zero_q_one
    (hG2 : AssumptionG2 G s p u q) (hp_ne_top : p ≠ ∞) (hs_pos : 0 < s) :
    Tendsto (fun N => tailCCoefficient G s p 1 N) atTop (𝓝 0) := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_ne_top
  have hinv_pos : 0 < 1 / p.toReal := div_pos one_pos hp_pos
  have hweight := levelWeightP_tendsto_zero (G := G) (s := s) (p := p) (u := u) (q := q)
    hG2 hs_pos
  rw [Metric.tendsto_atTop] at hweight ⊢
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rcases hweight (ε / 2) hε2 with ⟨N, hN⟩
  refine ⟨N, fun M hNM => ?_⟩
  have hC_nonneg : 0 ≤ tailCCoefficient G s p 1 M := by
    unfold tailCCoefficient
    exact LpGridRepresentation.cCoefficient_nonneg p 1 (tailCoefficientWeight G s p M)
      (tailCoefficientWeight_nonneg G s p M)
  have hC_le : tailCCoefficient G s p 1 M ≤ ε / 2 := by
    unfold tailCCoefficient LpGridRepresentation.cCoefficient
    simp only
    refine csSup_le (Set.range_nonempty _) ?_
    rintro x ⟨k, rfl⟩
    by_cases hk : k < M
    · have hzero : tailCoefficientWeight G s p M k = 0 := by
        simp [tailCoefficientWeight, hk]
      have hroot_zero : (tailCoefficientWeight G s p M k) ^ (1 / p.toReal) = 0 := by
        rw [hzero]
        exact Real.zero_rpow hinv_pos.ne'
      calc
        (fun k => tailCoefficientWeight G s p M k ^ (1 / p.toReal)) k = 0 := by
          simpa using hroot_zero
        _ ≤ ε / 2 := le_of_lt hε2
    · have hMk : M ≤ k := le_of_not_gt hk
      have hNk : N ≤ k := hNM.trans hMk
      have htail : tailCoefficientWeight G s p M k = (levelWeightP G s p k) ^ p.toReal := by
        simp [tailCoefficientWeight, hk]
      have hw_nonneg : 0 ≤ levelWeightP G s p k := by
        exact LpGridRepresentation.levelMeasureWeight_nonneg G s p p k
      have hroot :
          (tailCoefficientWeight G s p M k) ^ (1 / p.toReal) = levelWeightP G s p k := by
        rw [htail]
        simpa [one_div] using Real.rpow_rpow_inv hw_nonneg hp_pos.ne'
      have hk_small : levelWeightP G s p k < ε / 2 := by
        have := hN k hNk
        simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hw_nonneg] using this
      calc
        (fun k => tailCoefficientWeight G s p M k ^ (1 / p.toReal)) k =
            levelWeightP G s p k := by
          simpa using hroot
        _ ≤ ε / 2 := le_of_lt hk_small
  have hhalf_lt : ε / 2 < ε := by linarith
  calc
    dist (tailCCoefficient G s p 1 M) 0 = |tailCCoefficient G s p 1 M| := by
      simp
    _ = tailCCoefficient G s p 1 M := abs_of_nonneg hC_nonneg
    _ ≤ ε / 2 := hC_le
    _ < ε := hhalf_lt

/-- Unified: `tailCCoefficient G s p q N → 0` for all `q ≥ 1`. -/
private lemma tailCCoefficient_tendsto_zero
    (hG2 : AssumptionG2 G s p u q) (hp_ne_top : p ≠ ∞) (hs_pos : 0 < s) :
    Tendsto (fun N => tailCCoefficient G s p q N) atTop (𝓝 0) := by
  by_cases hq1 : q = 1
  · subst hq1
    exact tailCCoefficient_tendsto_zero_q_one hG2 hp_ne_top hs_pos
  · by_cases hqtop : q = ∞
    · subst hqtop
      exact tailCCoefficient_tendsto_zero_q_top hG2 hp_ne_top
    · exact tailCCoefficient_tendsto_zero_q_pos hG2 hp_ne_top hq1 hqtop

/--
The set of atoms on one weak-grid cell, realized in the ambient `L^p` space.

This is the object that appears in the compactness assumptions for
completeness: although atoms are stored in their local Banach spaces, the paper
states compactness after viewing them as `L^p` functions.
-/
def atomSetLp (A : AtomFamily G s p u) (Q : WeakGridCell G) :
    Set (Lp ℂ p G.measure) :=
  { f | ∃ φ : (A.localSpace Q).carrier,
      A.IsAtom Q φ ∧
        MemLp.toLp (A.toFunction Q φ) (A.local_memLp_p Q φ) = f }

/--
Assumption A6 (`compactw`): `p ∈ [1,∞)` and, for every grid cell `Q`, the atom
set `A(Q)`, realized in `L^p`, is sequentially compact for the weak topology.

The weak topology is represented by Mathlib's type synonym
`WeakSpace ℂ (Lp ℂ p G.measure)`, and the canonical identity map
`toWeakSpace` sends the strong `L^p` realization into that weak space.
-/
def AssumptionA6 (A : AtomFamily G s p u) : Prop :=
  1 ≤ p ∧ p ≠ ∞ ∧
    ∀ Q : WeakGridCell G,
      IsSeqCompact
        ((toWeakSpace ℂ (Lp ℂ p G.measure)) '' atomSetLp A Q :
          Set (WeakSpace ℂ (Lp ℂ p G.measure)))

/--
An atom on a cell, realized as an element of the ambient `L^p` space.

This is the single-cell term used to state strong and weak convergence of the
atoms in Proposition `compa2`.
-/
def atomLp (A : AtomFamily G s p u) (Q : WeakGridCell G)
    (φ : (A.localSpace Q).carrier) : Lp ℂ p G.measure :=
  MemLp.toLp (A.toFunction Q φ) (A.local_memLp_p Q φ)

/-- Coefficients of a sequence of representations converge cellwise to those of `Rlim`. -/
def CoefficientsTendsto
    {A : AtomFamily G s p u} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure}
    (Rseq : ∀ n, LpGridRepresentation A (gseq n))
    (Rlim : LpGridRepresentation A gLim) : Prop :=
  ∀ (k : ℕ) (Q : LevelCell G k),
    Tendsto (fun n => ((Rseq n).block k).coeff Q) atTop
      (𝓝 ((Rlim.block k).coeff Q))

/--
Atoms of a sequence of representations converge weakly in ambient `L^p`,
cell by cell, to the atoms of `Rlim`.
-/
def AtomsTendstoWeak
    {A : AtomFamily G s p u} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure}
    (Rseq : ∀ n, LpGridRepresentation A (gseq n))
    (Rlim : LpGridRepresentation A gLim) : Prop :=
  ∀ (k : ℕ) (Q : LevelCell G k),
    Tendsto
      (fun n =>
        toWeakSpace ℂ (Lp ℂ p G.measure)
          (atomLp A (levelCellToWeakGridCell G k Q) (((Rseq n).block k).atom Q)))
      atTop
      (𝓝 (toWeakSpace ℂ (Lp ℂ p G.measure)
        (atomLp A (levelCellToWeakGridCell G k Q) ((Rlim.block k).atom Q))))

/--
Atoms of a sequence of representations converge strongly in ambient `L^p`,
cell by cell, to the atoms of `Rlim`.
-/
def AtomsTendstoStrong
    {A : AtomFamily G s p u} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure}
    (Rseq : ∀ n, LpGridRepresentation A (gseq n))
    (Rlim : LpGridRepresentation A gLim) : Prop :=
  ∀ (k : ℕ) (Q : LevelCell G k),
    Tendsto
      (fun n => atomLp A (levelCellToWeakGridCell G k Q) (((Rseq n).block k).atom Q))
      atTop
      (𝓝 (atomLp A (levelCellToWeakGridCell G k Q) ((Rlim.block k).atom Q)))

/--
Data for Proposition `compa2` in the `1 ≤ p < ∞` formalization used here.

The paper allows either strong or weak convergence of the atoms. In this Lean
file we keep only the weak-convergence branch, since the ambient theory is used
only in the reflexive/weak-convergence setting for `L^p`.
-/
structure RepresentationLimitHypotheses
    (A : AtomFamily G s p u) (q : ℝ≥0∞)
    (gseq : ℕ → Lp ℂ p G.measure) (gLim : Lp ℂ p G.measure) (C : ℝ) where
  Rseq : ∀ n, LpGridRepresentation A (gseq n)
  Rlim : LpGridRepresentation A gLim
  uniform_bound : ∀ n, LpGridRepresentation.pqCostENNReal (q := q) (Rseq n) ≤ ENNReal.ofReal C
  coeff_tendsto : CoefficientsTendsto Rseq Rlim
  atom_tendsto : AtomsTendstoWeak Rseq Rlim

/--
Strong-topology variant of the representation-limit hypotheses.

This is the same coefficient/cost data as `RepresentationLimitHypotheses`, but
the atoms are assumed to converge in the norm topology of ambient `L^p`.
-/
structure RepresentationLimitStrongHypotheses
    (A : AtomFamily G s p u) (q : ℝ≥0∞)
    (gseq : ℕ → Lp ℂ p G.measure) (gLim : Lp ℂ p G.measure) (C : ℝ) where
  Rseq : ∀ n, LpGridRepresentation A (gseq n)
  Rlim : LpGridRepresentation A gLim
  uniform_bound : ∀ n, LpGridRepresentation.pqCostENNReal (q := q) (Rseq n) ≤ ENNReal.ofReal C
  coeff_tendsto : CoefficientsTendsto Rseq Rlim
  atom_tendsto : AtomsTendstoStrong Rseq Rlim

/-- Strong atom convergence implies the weak atom convergence hypotheses. -/
def RepresentationLimitStrongHypotheses.toWeak
    {A : AtomFamily G s p u} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : RepresentationLimitStrongHypotheses A q gseq gLim C) :
    RepresentationLimitHypotheses A q gseq gLim C where
  Rseq := H.Rseq
  Rlim := H.Rlim
  uniform_bound := H.uniform_bound
  coeff_tendsto := H.coeff_tendsto
  atom_tendsto := by
    intro k Q
    exact (map_continuous (toWeakSpaceCLM ℂ (Lp ℂ p G.measure))).continuousAt.tendsto.comp
      (H.atom_tendsto k Q)

omit [Fact (1 ≤ q)] in
/--
For each fixed level, the inner `ℓ^p` coefficient sum converges along the
representation sequence.

This is the finite-dimensional part of Proposition `compa2`: once the cells in
one level are fixed, the level cost is just a finite sum of continuous
functions of the coefficients.
-/
lemma representation_limit_levelCoeffPower_tendsto
    {A : AtomFamily G s p u} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : RepresentationLimitHypotheses A q gseq gLim C) (k : ℕ) :
    Tendsto (fun n => (H.Rseq n).levelCoeffPower k) atTop
      (𝓝 (H.Rlim.levelCoeffPower k)) := by
  unfold LpGridRepresentation.levelCoeffPower
  refine tendsto_finsetSum (Finset.univ) ?_
  intro Q hQ
  have hcoeff : Tendsto (fun n => ((H.Rseq n).block k).coeff Q) atTop
      (𝓝 ((H.Rlim.block k).coeff Q)) :=
    H.coeff_tendsto k Q
  have hnorm : Tendsto (fun n => ‖((H.Rseq n).block k).coeff Q‖) atTop
      (𝓝 ‖((H.Rlim.block k).coeff Q)‖) :=
    tendsto_norm.comp hcoeff
  have hp_nonneg : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  exact (Real.continuousAt_rpow_const
      (x := ‖((H.Rlim.block k).coeff Q)‖) (q := p.toReal) (Or.inr hp_nonneg)).tendsto.comp hnorm

/--
The extended ENNReal coefficient cost of the limit representation is bounded
by `ENNReal.ofReal C`, inherited from the uniform bound on the sequence.
-/
private lemma representation_limit_pqCostENNReal_le
    {A : AtomFamily G s p u} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : RepresentationLimitHypotheses A q gseq gLim C) :
    LpGridRepresentation.pqCostENNReal (q := q) H.Rlim ≤ ENNReal.ofReal C := by
  have hterm : ∀ (r : ℝ) (hr : 0 ≤ r) (k : ℕ),
      Tendsto (fun n => ENNReal.ofReal ((H.Rseq n).levelCoeffPower k ^ r)) atTop
        (𝓝 (ENNReal.ofReal (H.Rlim.levelCoeffPower k ^ r))) := fun r hr k => by
    exact (ENNReal.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const (x := H.Rlim.levelCoeffPower k) (q := r) (Or.inr hr))).tendsto.comp
      (representation_limit_levelCoeffPower_tendsto H k)
  by_cases hq : q = ∞
  · simp only [LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    apply sSup_le
    rintro x ⟨k, rfl⟩
    apply le_of_tendsto' (hterm (1 / p.toReal) (div_nonneg zero_le_one ENNReal.toReal_nonneg) k)
    intro n
    have hbound := H.uniform_bound n
    simp only [LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hbound
    exact (le_sSup (Set.mem_range.mpr ⟨k, rfl⟩)).trans hbound
  · simp only [LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have hp_nonneg : 0 ≤ p.toReal := ENNReal.toReal_nonneg
    have h_tsum_le : ∑' k, ENNReal.ofReal (H.Rlim.levelCoeffPower k ^ (q.toReal / p.toReal))
        ≤ (ENNReal.ofReal C) ^ q.toReal := by
      rw [ENNReal.tsum_eq_iSup_nat]
      apply iSup_le
      intro N
      apply le_of_tendsto'
        (tendsto_finsetSum (Finset.range N) fun k _ =>
          hterm (q.toReal / p.toReal) (div_nonneg hq_pos.le hp_nonneg) k)
      intro n
      have hbound := H.uniform_bound n
      simp only [LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hbound
      have h1 := ENNReal.rpow_le_rpow hbound hq_pos.le
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hq_pos.ne', ENNReal.rpow_one] at h1
      exact (ENNReal.sum_le_tsum _).trans h1
    calc (∑' k, ENNReal.ofReal (H.Rlim.levelCoeffPower k ^ (q.toReal / p.toReal))) ^ (1 / q.toReal)
        ≤ ((ENNReal.ofReal C) ^ q.toReal) ^ (1 / q.toReal) :=
          ENNReal.rpow_le_rpow h_tsum_le (div_nonneg zero_le_one hq_pos.le)
      _ = ENNReal.ofReal C := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hq_pos.ne', ENNReal.rpow_one]

/--
Proposition `compa2` in the weak `L^p` topology.

If a sequence of Besov-ish representations has uniformly bounded coefficient
cost, pointwise-convergent coefficients, and weakly convergent atoms on each
cell, then the limiting atomic representation defines a Besov-ish function,
satisfies the same coefficient bound, and is the weak `L^p` limit.
-/
lemma representation_limit_finitePQCost
    {A : AtomFamily G s p u} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : RepresentationLimitHypotheses A q gseq gLim C) :
    LpGridRepresentation.FinitePQCost (q := q) H.Rlim := by
  exact LpGridRepresentation.finitePQCost_of_pqCostENNReal_le H.Rlim (Fact.out : 1 ≤ q)
    (representation_limit_pqCostENNReal_le H)

/--
A finite ENNReal upper bound on the extended coefficient cost gives the same
real upper bound for `pqCost`.
-/
private lemma pqCost_le_of_pqCostENNReal_le
    {A : AtomFamily G s p u} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {g : Lp ℂ p G.measure} {C : ℝ}
    (R : LpGridRepresentation A g)
    (hENNReal : LpGridRepresentation.pqCostENNReal (q := q) R ≤ ENNReal.ofReal C)
    (hC : 0 ≤ C) :
    LpGridRepresentation.pqCost (q := q) R ≤ C := by
  have hfin := LpGridRepresentation.finitePQCost_of_pqCostENNReal_le R
    (Fact.out : 1 ≤ q) hENNReal
  by_cases hq : q = ∞
  · simp only [LpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hENNReal
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨k, rfl⟩
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp
      ((le_sSup (Set.mem_range.mpr ⟨k, rfl⟩)).trans hENNReal)
  · simp only [LpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hfin
    simp only [LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hENNReal
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have h_nonneg : ∀ k, 0 ≤ R.levelCoeffPower k ^ (q.toReal / p.toReal) :=
      fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
    rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg hfin,
        ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg h_nonneg)
          (div_nonneg zero_le_one hq_pos.le)] at hENNReal
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp hENNReal

/--
If finite initial segments converge termwise and the two series tails are
uniformly small, then the represented sums converge.
-/
private lemma tendsto_of_termwise_of_uniform_tails
    {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → ℕ → E} {F : ℕ → E} {sn : ℕ → E} {S : E}
    (hterm : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (F k)))
    (htail : ∀ ε > 0, ∃ N, ∀ n,
      ‖(sn n - ∑ k ∈ Finset.range N, f n k) -
          (S - ∑ k ∈ Finset.range N, F k)‖ < ε) :
    Tendsto sn atTop (𝓝 S) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  rcases htail (ε / 3) hε3 with ⟨N, hN⟩
  have hprefix : Tendsto
      (fun n => ∑ k ∈ Finset.range N, f n k) atTop
      (𝓝 (∑ k ∈ Finset.range N, F k)) := by
    exact tendsto_finsetSum (Finset.range N) fun k _ => hterm k
  rcases (Metric.tendsto_atTop.mp hprefix) (ε / 3) hε3 with ⟨n0, hn0⟩
  refine ⟨n0, fun n hn => ?_⟩
  have htail_n := hN n
  have hprefix_n : ‖(∑ k ∈ Finset.range N, f n k) - (∑ k ∈ Finset.range N, F k)‖ < ε / 3 := by
    simpa [dist_eq_norm] using hn0 n hn
  have hdecomp :
      sn n - S =
        ((sn n - ∑ k ∈ Finset.range N, f n k) -
          (S - ∑ k ∈ Finset.range N, F k)) +
        ((∑ k ∈ Finset.range N, f n k) - (∑ k ∈ Finset.range N, F k)) := by
    abel
  calc
    dist (sn n) S = ‖sn n - S‖ := by rw [dist_eq_norm]
    _ = ‖((sn n - ∑ k ∈ Finset.range N, f n k) -
          (S - ∑ k ∈ Finset.range N, F k)) +
        ((∑ k ∈ Finset.range N, f n k) - (∑ k ∈ Finset.range N, F k))‖ := by
          rw [hdecomp]
    _ ≤ ‖(sn n - ∑ k ∈ Finset.range N, f n k) -
          (S - ∑ k ∈ Finset.range N, F k)‖ +
        ‖(∑ k ∈ Finset.range N, f n k) - (∑ k ∈ Finset.range N, F k)‖ :=
          norm_add_le _ _
    _ < ε / 3 + ε / 3 := add_lt_add htail_n hprefix_n
    _ < ε := by linarith

/--
The coefficient-cost bound passes to the limit representation.
Requires `C ≥ 0` since `pqCost` is nonneg and `ENNReal.ofReal C = 0` for negative `C`.
-/
lemma representation_limit_pqCost_le
    {A : AtomFamily G s p u} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : RepresentationLimitHypotheses A q gseq gLim C) (hC : 0 ≤ C) :
    LpGridRepresentation.pqCost (q := q) H.Rlim ≤ C := by
  exact pqCost_le_of_pqCostENNReal_le H.Rlim (representation_limit_pqCostENNReal_le H) hC

/--
The limit representation defines a Besov-ish element with finite coefficient
cost.
-/
lemma representation_limit_memBesovishCoeffCost
    {A : AtomFamily G s p u} {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : RepresentationLimitHypotheses A q gseq gLim C) :
    MemBesovishCoeffCost A q gLim := by
  exact ⟨H.Rlim, representation_limit_finitePQCost H⟩

/--
The represented functions converge weakly in ambient `L^p`.

Proof sketch (3ε argument):
  Write `g_n - g = (finite sum k ≤ N) + (tail k > N)`.
  The tail has a new atomic representation with coefficients `|s_Q^n| + |s_Q|`
  and atoms that are convex combinations (hence atoms by `atom_add_combo_mem_of_norm_add_le_one`).
  By `lp_embedding_adapted_statement` + `AssumptionG2`, the tail L^p norm is
  bounded by `C_mult · cCoefficient(tail_weights_N) · 2C → 0` as N → ∞.
  The finite sum converges weakly term-by-term via `coeff_tendsto` + `atom_tendsto`.
-/
lemma representation_limit_weak_tendsto
    (A : AtomFamily G s p u)(hG2 : AssumptionG2 G s p u q)
    {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : RepresentationLimitHypotheses A q gseq gLim C)
    (hp_ne_top : p ≠ ∞) (hs_pos : 0 < s) (hu_one : 1 ≤ u)
    [Fact (1 ≤ u)] (hC : 0 ≤ C) :
    Tendsto (fun n => toWeakSpace ℂ (Lp ℂ p G.measure) (gseq n)) atTop
      (𝓝 (toWeakSpace ℂ (Lp ℂ p G.measure) gLim)) := by
  -- Injectivity of the dual pairing flip (Hahn-Banach / SeparatingDual)
  have h_inj : Function.Injective (topDualPairing ℂ (Lp ℂ p G.measure)).flip := by
    intro x y hxy
    by_contra h
    obtain ⟨Λ, hΛ⟩ := SeparatingDual.exists_separating_of_ne (R := ℂ) h
    exact hΛ (DFunLike.congr_fun hxy Λ)
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto _ h_inj).mpr ?_
  intro Λ
  -- After unfolding: goal is to show Λ(gseq n) → Λ(gLim)
  -- Apply Λ to the HasSum equations via the continuous linear map
  have hΛgseq : ∀ n, HasSum (fun k => Λ ((H.Rseq n).block k |>.toLp A)) (Λ (gseq n)) :=
    fun n => (H.Rseq n).hasSum.map Λ.toAddMonoidHom Λ.continuous
  have hΛgLim : HasSum (fun k => Λ (H.Rlim.block k |>.toLp A)) (Λ gLim) :=
    H.Rlim.hasSum.map Λ.toAddMonoidHom Λ.continuous
  -- Term-by-term convergence of Λ applied to each level block
  have hterm : ∀ k, Tendsto (fun n => Λ ((H.Rseq n).block k |>.toLp A)) atTop
      (𝓝 (Λ (H.Rlim.block k |>.toLp A))) := by
    intro k
    simp only [LevelBlock.toLp, map_sum, LevelBlock.term, map_smul]
    refine tendsto_finsetSum (G.grid.partitions k).attach fun Q _ => ?_
    -- Each term: coeff_n(Q) · Λ(atom_n(Q)) → coeff(Q) · Λ(atom(Q)).
    apply Filter.Tendsto.smul
    · exact H.coeff_tendsto k Q
    · have hatom := H.atom_tendsto k Q
      have heval : Continuous fun (x : WeakSpace ℂ (Lp ℂ p G.measure)) =>
          (topDualPairing ℂ (Lp ℂ p G.measure)).flip x Λ :=
        WeakBilin.eval_continuous _ Λ
      simpa [atomLp] using heval.continuousAt.tendsto.comp hatom
  have hseq_fin : ∀ n, LpGridRepresentation.FinitePQCost (q := q) (H.Rseq n) := by
    intro n
    exact LpGridRepresentation.finitePQCost_of_pqCostENNReal_le (H.Rseq n)
      (Fact.out : 1 ≤ q) (H.uniform_bound n)
  have hseq_cost_le : ∀ n, LpGridRepresentation.pqCost (q := q) (H.Rseq n) ≤ C := by
    intro n
    exact pqCost_le_of_pqCostENNReal_le (H.Rseq n) (H.uniform_bound n) hC
  have hlim_cost_le : LpGridRepresentation.pqCost (q := q) H.Rlim ≤ C :=
    representation_limit_pqCost_le H hC
  let Dtail := fun (N n : ℕ) =>
      LpGridRepresentation.add
        (LpGridRepresentation.tail (H.Rseq n) N)
        (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N))
  have hDtail_cost_le : ∀ N n,
      LpGridRepresentation.pqCost (q := q) (Dtail N n) ≤ 2 * C := by
    intro N n
    have htail_seq_fin :
        LpGridRepresentation.FinitePQCost (q := q)
          (LpGridRepresentation.tail (H.Rseq n) N) :=
      LpGridRepresentation.tail_finitePQCost (H.Rseq n) N (Fact.out : 1 ≤ q) (hseq_fin n)
    have htail_lim_fin :
        LpGridRepresentation.FinitePQCost (q := q)
          (LpGridRepresentation.tail H.Rlim N) :=
      LpGridRepresentation.tail_finitePQCost H.Rlim N (Fact.out : 1 ≤ q)
        (representation_limit_finitePQCost H)
    have hsmul_tail_lim_fin :
        LpGridRepresentation.FinitePQCost (q := q)
          (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N)) :=
      LpGridRepresentation.smul_finitePQCost
        (A := A) (q := q) (-1 : ℂ) htail_lim_fin
    have htri :=
      LpGridRepresentation.pqCost_triangle
        (A := A) (q := q)
        (LpGridRepresentation.tail (H.Rseq n) N)
        (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N))
        hp_ne_top (Fact.out : 1 ≤ q) htail_seq_fin hsmul_tail_lim_fin
    have htail_seq_cost :
        LpGridRepresentation.pqCost (q := q)
          (LpGridRepresentation.tail (H.Rseq n) N) ≤ C :=
      (LpGridRepresentation.pqCost_tail_le (H.Rseq n) N (Fact.out : 1 ≤ q)
        (hseq_fin n)).trans (hseq_cost_le n)
    have htail_lim_cost :
        LpGridRepresentation.pqCost (q := q)
          (LpGridRepresentation.tail H.Rlim N) ≤ C :=
      (LpGridRepresentation.pqCost_tail_le H.Rlim N (Fact.out : 1 ≤ q)
        (representation_limit_finitePQCost H)).trans hlim_cost_le
    have hsmul_cost :
        LpGridRepresentation.pqCost (q := q)
          (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N)) =
          LpGridRepresentation.pqCost (q := q) (LpGridRepresentation.tail H.Rlim N) := by
      have h :=
        LpGridRepresentation.pqCost_smul
          (A := A) (q := q) (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N)
          hp_ne_top (Fact.out : 1 ≤ q) htail_lim_fin
      simpa using h
    calc
      LpGridRepresentation.pqCost (q := q) (Dtail N n)
          ≤ LpGridRepresentation.pqCost (q := q) (LpGridRepresentation.tail (H.Rseq n) N) +
              LpGridRepresentation.pqCost (q := q)
                (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N)) := by
            simpa [Dtail] using htri
      _ = LpGridRepresentation.pqCost (q := q) (LpGridRepresentation.tail (H.Rseq n) N) +
            LpGridRepresentation.pqCost (q := q) (LpGridRepresentation.tail H.Rlim N) := by
            rw [hsmul_cost]
      _ ≤ C + C := add_le_add htail_seq_cost htail_lim_cost
      _ = 2 * C := by ring
  have htail_uniform : ∀ ε > 0, ∃ N, ∀ n,
      ‖(Λ (gseq n) - ∑ k ∈ Finset.range N, Λ ((H.Rseq n).block k |>.toLp A)) -
          (Λ gLim - ∑ k ∈ Finset.range N, Λ (H.Rlim.block k |>.toLp A))‖ < ε := by
    have htail_norm_uniform : ∀ ε > 0, ∃ N, ∀ n,
        ‖((gseq n - ∑ k ∈ Finset.range N, ((H.Rseq n).block k).toLp A) -
            (gLim - ∑ k ∈ Finset.range N, (H.Rlim.block k).toLp A))‖ < ε := by
      intro ε hε
      let Cemb : ℝ := (G.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)
      let K : ℝ := Cemb * (2 * C) + 1
      have hCemb_nonneg : 0 ≤ Cemb := by positivity
      have htwoC_nonneg : 0 ≤ 2 * C := by positivity
      have hK_pos : 0 < K := by
        dsimp [K]
        nlinarith [mul_nonneg hCemb_nonneg htwoC_nonneg]
      have hη_pos : 0 < ε / K := by positivity
      have htail_tendsto :
          Tendsto (fun N => tailCCoefficient G s p q N) atTop (𝓝 0) :=
        tailCCoefficient_tendsto_zero (G := G) (s := s) (p := p) (u := u) (q := q)
          hG2 hp_ne_top hs_pos
      rw [Metric.tendsto_atTop] at htail_tendsto
      rcases htail_tendsto (ε / K) hη_pos with ⟨N, hN⟩
      refine ⟨N, fun n => ?_⟩
      have htail_nonneg : 0 ≤ tailCCoefficient G s p q N :=
        LpGridRepresentation.cCoefficient_nonneg p q (tailCoefficientWeight G s p N)
          (tailCoefficientWeight_nonneg G s p N)
      have htail_small : tailCCoefficient G s p q N < ε / K := by
        have hdist := hN N le_rfl
        simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg htail_nonneg] using hdist
      have htail_seq_fin :
          LpGridRepresentation.FinitePQCost (q := q)
            (LpGridRepresentation.tail (H.Rseq n) N) :=
        LpGridRepresentation.tail_finitePQCost (H.Rseq n) N (Fact.out : 1 ≤ q) (hseq_fin n)
      have htail_lim_fin :
          LpGridRepresentation.FinitePQCost (q := q)
            (LpGridRepresentation.tail H.Rlim N) :=
        LpGridRepresentation.tail_finitePQCost H.Rlim N (Fact.out : 1 ≤ q)
          (representation_limit_finitePQCost H)
      have hsmul_tail_lim_fin :
          LpGridRepresentation.FinitePQCost (q := q)
            (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N)) :=
        LpGridRepresentation.smul_finitePQCost
          (A := A) (q := q) (-1 : ℂ) htail_lim_fin
      have hDtail_fin :
          LpGridRepresentation.FinitePQCost (q := q) (Dtail N n) :=
        LpGridRepresentation.add_finitePQCost
          (A := A) (q := q)
          (LpGridRepresentation.tail (H.Rseq n) N)
          (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N))
          hp_ne_top (Fact.out : 1 ≤ q) htail_seq_fin hsmul_tail_lim_fin
      have hzeroD : ∀ k, k < N → (Dtail N n).levelCoeffPower k = 0 := by
        intro k hk
        have hp_pos : 0 < p.toReal :=
          ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_ne_top
        simp [Dtail, LpGridRepresentation.levelCoeffPower, LpGridRepresentation.add,
          LpGridRepresentation.tail, LpGridRepresentation.smul, LevelBlock.add,
          LevelBlock.smul, LevelBlock.zero, hk, Real.zero_rpow hp_pos.ne']
      have hbound :=
        sharp_tail_embedding_bound
          (G := G) (s := s) (p := p) (u := u) (q := q) (A := A)
          hG2 hp_ne_top hu_one hs_pos (Dtail N n) hDtail_fin N hzeroD
      have hcost := hDtail_cost_le N n
      have hbound' :
          ‖((gseq n - ∑ k ∈ Finset.range N, ((H.Rseq n).block k).toLp A) -
              (gLim - ∑ k ∈ Finset.range N, (H.Rlim.block k).toLp A))‖ ≤
            Cemb * tailCCoefficient G s p q N *
              LpGridRepresentation.pqCost (q := q) (Dtail N n) := by
        have hx :
            ((gseq n - ∑ k ∈ Finset.range N, ((H.Rseq n).block k).toLp A) -
                (gLim - ∑ k ∈ Finset.range N, (H.Rlim.block k).toLp A)) =
              (gseq n - ∑ k ∈ Finset.range N, ((H.Rseq n).block k).toLp A) +
                (-1 : ℂ) •
                  (gLim - ∑ k ∈ Finset.range N, (H.Rlim.block k).toLp A) := by
          simp [sub_eq_add_neg]
          abel
        rw [hx]
        simpa [Cemb, Dtail] using hbound
      have hcost_nonneg : 0 ≤ LpGridRepresentation.pqCost (q := q) (Dtail N n) :=
        LpGridRepresentation.pqCost_nonneg (Dtail N n)
      have htailcost_le :
          Cemb * tailCCoefficient G s p q N *
              LpGridRepresentation.pqCost (q := q) (Dtail N n) ≤
            Cemb * tailCCoefficient G s p q N * (2 * C) := by
        exact mul_le_mul_of_nonneg_left hcost
          (mul_nonneg hCemb_nonneg htail_nonneg)
      have hmain_lt :
          Cemb * tailCCoefficient G s p q N * (2 * C) < ε := by
        have hcoef_le_K : Cemb * (2 * C) ≤ K := by
          dsimp [K]
          linarith
        have htail_nonneg' := htail_nonneg
        calc
          Cemb * tailCCoefficient G s p q N * (2 * C)
              = (Cemb * (2 * C)) * tailCCoefficient G s p q N := by ring
          _ ≤ K * tailCCoefficient G s p q N :=
              mul_le_mul_of_nonneg_right hcoef_le_K htail_nonneg'
          _ < K * (ε / K) :=
              mul_lt_mul_of_pos_left htail_small hK_pos
          _ = ε := by field_simp [hK_pos.ne']
      exact lt_of_le_of_lt (hbound'.trans htailcost_le) hmain_lt
    intro ε hε
    let δ : ℝ := ε / (2 * (‖Λ‖ + 1))
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    rcases htail_norm_uniform δ hδ_pos with ⟨N, hN⟩
    refine ⟨N, fun n => ?_⟩
    let x : Lp ℂ p G.measure :=
      (gseq n - ∑ k ∈ Finset.range N, ((H.Rseq n).block k).toLp A) -
        (gLim - ∑ k ∈ Finset.range N, (H.Rlim.block k).toLp A)
    have hxsmall : ‖x‖ < δ := by
      simpa [x] using hN n
    have hmap :
        (Λ (gseq n) - ∑ k ∈ Finset.range N, Λ ((H.Rseq n).block k |>.toLp A)) -
            (Λ gLim - ∑ k ∈ Finset.range N, Λ (H.Rlim.block k |>.toLp A)) =
          Λ x := by
      simp [x, map_sub, map_sum]
    have hop : ‖Λ x‖ ≤ ‖Λ‖ * ‖x‖ := ContinuousLinearMap.le_opNorm Λ x
    have hmul_le_delta : ‖Λ‖ * ‖x‖ ≤ ‖Λ‖ * δ := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hxsmall) (norm_nonneg Λ)
    have hmul_le : ‖Λ‖ * δ ≤ ε / 2 := by
      have hΛ_le : ‖Λ‖ ≤ ‖Λ‖ + 1 := by linarith [norm_nonneg Λ]
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      calc
        ‖Λ‖ * δ ≤ (‖Λ‖ + 1) * δ := mul_le_mul_of_nonneg_right hΛ_le hδ_nonneg
        _ = ε / 2 := by
          dsimp [δ]
          field_simp [show 2 * (‖Λ‖ + 1) ≠ 0 by positivity]
    have hhalf_lt : ε / 2 < ε := by linarith
    calc
      ‖(Λ (gseq n) - ∑ k ∈ Finset.range N, Λ ((H.Rseq n).block k |>.toLp A)) -
          (Λ gLim - ∑ k ∈ Finset.range N, Λ (H.Rlim.block k |>.toLp A))‖
          = ‖Λ x‖ := by rw [hmap]
      _ ≤ ‖Λ‖ * ‖x‖ := hop
      _ ≤ ‖Λ‖ * δ := hmul_le_delta
      _ ≤ ε / 2 := hmul_le
      _ < ε := hhalf_lt
  simpa using
    tendsto_of_termwise_of_uniform_tails
      (f := fun n k => Λ ((H.Rseq n).block k |>.toLp A))
      (F := fun k => Λ (H.Rlim.block k |>.toLp A))
      (sn := fun n => Λ (gseq n))
      (S := Λ gLim)
      hterm htail_uniform

/--
Strong-topology version of `representation_limit_weak_tendsto`.

If the atoms converge strongly in ambient `L^p`, then the represented functions
`gseq n` converge to `gLim` in the norm topology of `L^p`.
-/
lemma representation_limit_strong_tendsto
    (A : AtomFamily G s p u)(hG2 : AssumptionG2 G s p u q)
    {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : RepresentationLimitStrongHypotheses A q gseq gLim C)
    (hp_ne_top : p ≠ ∞) (hs_pos : 0 < s) (hu_one : 1 ≤ u)
    [Fact (1 ≤ u)] (hC : 0 ≤ C) :
    Tendsto gseq atTop (𝓝 gLim) := by
  let Hw : RepresentationLimitHypotheses A q gseq gLim C := H.toWeak
  have hterm : ∀ k, Tendsto (fun n => ((H.Rseq n).block k).toLp A) atTop
      (𝓝 ((H.Rlim.block k).toLp A)) := by
    intro k
    simp only [LevelBlock.toLp, LevelBlock.term]
    refine tendsto_finsetSum (G.grid.partitions k).attach fun Q _ => ?_
    exact Filter.Tendsto.smul (H.coeff_tendsto k Q)
      (by simpa [atomLp] using H.atom_tendsto k Q)
  have hseq_fin : ∀ n, LpGridRepresentation.FinitePQCost (q := q) (H.Rseq n) := by
    intro n
    exact LpGridRepresentation.finitePQCost_of_pqCostENNReal_le (H.Rseq n)
      (Fact.out : 1 ≤ q) (H.uniform_bound n)
  have hseq_cost_le : ∀ n, LpGridRepresentation.pqCost (q := q) (H.Rseq n) ≤ C := by
    intro n
    exact pqCost_le_of_pqCostENNReal_le (H.Rseq n) (H.uniform_bound n) hC
  have hlim_cost_le : LpGridRepresentation.pqCost (q := q) H.Rlim ≤ C :=
    representation_limit_pqCost_le Hw hC
  let Dtail := fun (N n : ℕ) =>
      LpGridRepresentation.add
        (LpGridRepresentation.tail (H.Rseq n) N)
        (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N))
  have hDtail_cost_le : ∀ N n,
      LpGridRepresentation.pqCost (q := q) (Dtail N n) ≤ 2 * C := by
    intro N n
    have htail_seq_fin :
        LpGridRepresentation.FinitePQCost (q := q)
          (LpGridRepresentation.tail (H.Rseq n) N) :=
      LpGridRepresentation.tail_finitePQCost (H.Rseq n) N (Fact.out : 1 ≤ q) (hseq_fin n)
    have htail_lim_fin :
        LpGridRepresentation.FinitePQCost (q := q)
          (LpGridRepresentation.tail H.Rlim N) :=
      LpGridRepresentation.tail_finitePQCost H.Rlim N (Fact.out : 1 ≤ q)
        (representation_limit_finitePQCost Hw)
    have hsmul_tail_lim_fin :
        LpGridRepresentation.FinitePQCost (q := q)
          (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N)) :=
      LpGridRepresentation.smul_finitePQCost
        (A := A) (q := q) (-1 : ℂ) htail_lim_fin
    have htri :=
      LpGridRepresentation.pqCost_triangle
        (A := A) (q := q)
        (LpGridRepresentation.tail (H.Rseq n) N)
        (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N))
        hp_ne_top (Fact.out : 1 ≤ q) htail_seq_fin hsmul_tail_lim_fin
    have htail_seq_cost :
        LpGridRepresentation.pqCost (q := q)
          (LpGridRepresentation.tail (H.Rseq n) N) ≤ C :=
      (LpGridRepresentation.pqCost_tail_le (H.Rseq n) N (Fact.out : 1 ≤ q)
        (hseq_fin n)).trans (hseq_cost_le n)
    have htail_lim_cost :
        LpGridRepresentation.pqCost (q := q)
          (LpGridRepresentation.tail H.Rlim N) ≤ C :=
      (LpGridRepresentation.pqCost_tail_le H.Rlim N (Fact.out : 1 ≤ q)
        (representation_limit_finitePQCost Hw)).trans hlim_cost_le
    have hsmul_cost :
        LpGridRepresentation.pqCost (q := q)
          (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N)) =
          LpGridRepresentation.pqCost (q := q) (LpGridRepresentation.tail H.Rlim N) := by
      have h :=
        LpGridRepresentation.pqCost_smul
          (A := A) (q := q) (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N)
          hp_ne_top (Fact.out : 1 ≤ q) htail_lim_fin
      simpa using h
    calc
      LpGridRepresentation.pqCost (q := q) (Dtail N n)
          ≤ LpGridRepresentation.pqCost (q := q) (LpGridRepresentation.tail (H.Rseq n) N) +
              LpGridRepresentation.pqCost (q := q)
                (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N)) := by
            simpa [Dtail] using htri
      _ = LpGridRepresentation.pqCost (q := q) (LpGridRepresentation.tail (H.Rseq n) N) +
            LpGridRepresentation.pqCost (q := q) (LpGridRepresentation.tail H.Rlim N) := by
            rw [hsmul_cost]
      _ ≤ C + C := add_le_add htail_seq_cost htail_lim_cost
      _ = 2 * C := by ring
  have htail_uniform : ∀ ε > 0, ∃ N, ∀ n,
      ‖((gseq n - ∑ k ∈ Finset.range N, ((H.Rseq n).block k).toLp A) -
          (gLim - ∑ k ∈ Finset.range N, (H.Rlim.block k).toLp A))‖ < ε := by
    intro ε hε
    let Cemb : ℝ := (G.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)
    let K : ℝ := Cemb * (2 * C) + 1
    have hCemb_nonneg : 0 ≤ Cemb := by positivity
    have htwoC_nonneg : 0 ≤ 2 * C := by positivity
    have hK_pos : 0 < K := by
      dsimp [K]
      nlinarith [mul_nonneg hCemb_nonneg htwoC_nonneg]
    have hη_pos : 0 < ε / K := by positivity
    have htail_tendsto :
        Tendsto (fun N => tailCCoefficient G s p q N) atTop (𝓝 0) :=
      tailCCoefficient_tendsto_zero (G := G) (s := s) (p := p) (u := u) (q := q)
        hG2 hp_ne_top hs_pos
    rw [Metric.tendsto_atTop] at htail_tendsto
    rcases htail_tendsto (ε / K) hη_pos with ⟨N, hN⟩
    refine ⟨N, fun n => ?_⟩
    have htail_nonneg : 0 ≤ tailCCoefficient G s p q N :=
      LpGridRepresentation.cCoefficient_nonneg p q (tailCoefficientWeight G s p N)
        (tailCoefficientWeight_nonneg G s p N)
    have htail_small : tailCCoefficient G s p q N < ε / K := by
      have hdist := hN N le_rfl
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg htail_nonneg] using hdist
    have htail_seq_fin :
        LpGridRepresentation.FinitePQCost (q := q)
          (LpGridRepresentation.tail (H.Rseq n) N) :=
      LpGridRepresentation.tail_finitePQCost (H.Rseq n) N (Fact.out : 1 ≤ q) (hseq_fin n)
    have htail_lim_fin :
        LpGridRepresentation.FinitePQCost (q := q)
          (LpGridRepresentation.tail H.Rlim N) :=
      LpGridRepresentation.tail_finitePQCost H.Rlim N (Fact.out : 1 ≤ q)
        (representation_limit_finitePQCost Hw)
    have hsmul_tail_lim_fin :
        LpGridRepresentation.FinitePQCost (q := q)
          (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N)) :=
      LpGridRepresentation.smul_finitePQCost
        (A := A) (q := q) (-1 : ℂ) htail_lim_fin
    have hDtail_fin :
        LpGridRepresentation.FinitePQCost (q := q) (Dtail N n) :=
      LpGridRepresentation.add_finitePQCost
        (A := A) (q := q)
        (LpGridRepresentation.tail (H.Rseq n) N)
        (LpGridRepresentation.smul (-1 : ℂ) (LpGridRepresentation.tail H.Rlim N))
        hp_ne_top (Fact.out : 1 ≤ q) htail_seq_fin hsmul_tail_lim_fin
    have hzeroD : ∀ k, k < N → (Dtail N n).levelCoeffPower k = 0 := by
      intro k hk
      have hp_pos : 0 < p.toReal :=
        ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_ne_top
      simp [Dtail, LpGridRepresentation.levelCoeffPower, LpGridRepresentation.add,
        LpGridRepresentation.tail, LpGridRepresentation.smul, LevelBlock.add,
        LevelBlock.smul, LevelBlock.zero, hk, Real.zero_rpow hp_pos.ne']
    have hbound :=
      sharp_tail_embedding_bound
        (G := G) (s := s) (p := p) (u := u) (q := q) (A := A)
        hG2 hp_ne_top hu_one hs_pos (Dtail N n) hDtail_fin N hzeroD
    have hbound' :
        ‖((gseq n - ∑ k ∈ Finset.range N, ((H.Rseq n).block k).toLp A) -
            (gLim - ∑ k ∈ Finset.range N, (H.Rlim.block k).toLp A))‖ ≤
          Cemb * tailCCoefficient G s p q N *
            LpGridRepresentation.pqCost (q := q) (Dtail N n) := by
      have hx :
          ((gseq n - ∑ k ∈ Finset.range N, ((H.Rseq n).block k).toLp A) -
              (gLim - ∑ k ∈ Finset.range N, (H.Rlim.block k).toLp A)) =
            (gseq n - ∑ k ∈ Finset.range N, ((H.Rseq n).block k).toLp A) +
              (-1 : ℂ) •
                (gLim - ∑ k ∈ Finset.range N, (H.Rlim.block k).toLp A) := by
        simp [sub_eq_add_neg]
        abel
      rw [hx]
      simpa [Cemb, Dtail] using hbound
    have hcost := hDtail_cost_le N n
    have htailcost_le :
        Cemb * tailCCoefficient G s p q N *
            LpGridRepresentation.pqCost (q := q) (Dtail N n) ≤
          Cemb * tailCCoefficient G s p q N * (2 * C) := by
      exact mul_le_mul_of_nonneg_left hcost
        (mul_nonneg hCemb_nonneg htail_nonneg)
    have hmain_lt :
        Cemb * tailCCoefficient G s p q N * (2 * C) < ε := by
      have hcoef_le_K : Cemb * (2 * C) ≤ K := by
        dsimp [K]
        linarith
      calc
        Cemb * tailCCoefficient G s p q N * (2 * C)
            = (Cemb * (2 * C)) * tailCCoefficient G s p q N := by ring
        _ ≤ K * tailCCoefficient G s p q N :=
            mul_le_mul_of_nonneg_right hcoef_le_K htail_nonneg
        _ < K * (ε / K) :=
            mul_lt_mul_of_pos_left htail_small hK_pos
        _ = ε := by field_simp [hK_pos.ne']
    exact lt_of_le_of_lt (hbound'.trans htailcost_le) hmain_lt
  simpa using
    tendsto_of_termwise_of_uniform_tails
      (f := fun n k => ((H.Rseq n).block k).toLp A)
      (F := fun k => (H.Rlim.block k).toLp A)
      (sn := fun n => gseq n)
      (S := gLim)
      hterm htail_uniform

/--
Proposition `compa2` in the weak `L^p` topology.

If a sequence of Besov-ish representations has uniformly bounded coefficient
cost, pointwise-convergent coefficients, and weakly convergent atoms on each
cell, then the limiting atomic representation defines a Besov-ish function,
satisfies the same coefficient bound, and is the weak `L^p` limit.
-/
theorem representation_limit
    (A : AtomFamily G s p u)(hG2 : AssumptionG2 G s p u q)
     {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : RepresentationLimitHypotheses A q gseq gLim C)
    (hp_ne_top : p ≠ ∞) (hs_pos : 0 < s) (hu_one : 1 ≤ u)
    [Fact (1 ≤ u)] (hC : 0 ≤ C) :
    MemBesovishCoeffCost A q gLim ∧
      LpGridRepresentation.FinitePQCost (q := q) H.Rlim ∧
      LpGridRepresentation.pqCost (q := q) H.Rlim ≤ C ∧
      Tendsto (fun n => toWeakSpace ℂ (Lp ℂ p G.measure) (gseq n)) atTop
        (𝓝 (toWeakSpace ℂ (Lp ℂ p G.measure) gLim)) := by
  exact ⟨representation_limit_memBesovishCoeffCost H,
    representation_limit_finitePQCost H,
    representation_limit_pqCost_le H hC,
    representation_limit_weak_tendsto A hG2 H hp_ne_top hs_pos hu_one hC⟩

/--
Proposition `compa2` in the strong `L^p` topology.

This is the strong-convergence branch: if the atoms converge in ambient `L^p`
norm, then the represented functions converge to the limiting representation in
the norm topology of `L^p`.
-/
theorem representation_limit_strong
    (A : AtomFamily G s p u)(hG2 : AssumptionG2 G s p u q)
     {gseq : ℕ → Lp ℂ p G.measure}
    {gLim : Lp ℂ p G.measure} {C : ℝ}
    (H : RepresentationLimitStrongHypotheses A q gseq gLim C)
    (hp_ne_top : p ≠ ∞) (hs_pos : 0 < s) (hu_one : 1 ≤ u)
    [Fact (1 ≤ u)] (hC : 0 ≤ C) :
    MemBesovishCoeffCost A q gLim ∧
      LpGridRepresentation.FinitePQCost (q := q) H.Rlim ∧
      LpGridRepresentation.pqCost (q := q) H.Rlim ≤ C ∧
      Tendsto gseq atTop (𝓝 gLim) := by
  let Hw : RepresentationLimitHypotheses A q gseq gLim C := H.toWeak
  exact ⟨representation_limit_memBesovishCoeffCost Hw,
    representation_limit_finitePQCost Hw,
    representation_limit_pqCost_le Hw hC,
    representation_limit_strong_tendsto A hG2 H hp_ne_top hs_pos hu_one hC⟩




end

end WeakGridSpace
