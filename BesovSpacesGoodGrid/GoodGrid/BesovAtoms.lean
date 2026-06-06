import BesovSpacesGoodGrid.GoodGrid.BesovSpace
import BesovSpacesGoodGrid.WeakGrid.InducedGrid
import BesovSpacesGoodGrid.WeakGrid.Transmutation

/-!
# Besov atoms on a good grid

This file introduces the non-smooth, or Besov, atoms used to compare Souza's
atomic Besov space with larger atom classes.  A Besov atom on a cell `Q` is a
function supported on `Q` whose induced Besov norm of order `β` is controlled
by the scale factor `μ(Q)^(s - β)`.

The construction is deliberately phrased in terms of the existing induced-grid
and transmutation APIs.  The main comparison theorem below is the formal target
corresponding to the paper's proposition that any atom family squeezed between
Souza atoms and Besov atoms gives the same Besov space, with continuous norm
control in both directions.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
The conjugate exponent used in the geometric part of the Besov-atom
normalization.

Here `qtilde` remains the exponent used by the coefficient cost.  The geometric
sequence is paired against that cost by Hölder, so it uses the conjugate
exponent `qtilde'`: `∞` when `qtilde = 1`, `1` when `qtilde = ∞`, and
`qtilde / (qtilde - 1)` in the remaining finite case.
-/
noncomputable def besovAtomGeometricExponent (qtilde : ℝ≥0∞) : ℝ≥0∞ :=
  if qtilde = 1 then ∞ else if qtilde = ∞ then 1 else qtilde / (qtilde - 1)

/-- The model geometric weight used in the Besov-atom embedding estimate. -/
noncomputable def besovAtomGeometricWeight
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞) (k : ℕ) : ℝ :=
  ((G.grid.lambda2 ^ k) ^ β) ^ p.toReal

/--
The geometric constant used in the normalization of Besov atoms.

In the paper this is
`Cmult1^(1+1/p) * ‖(maior^(kβ))_k‖_{ℓ^{qtilde'}}`, where `qtilde'` is the
Hölder conjugate of the coefficient-cost exponent.  The `cCoefficient` helper
implements this conjugate-exponent norm by cases; the displayed weight is
raised to `p` because that helper is parameterized by the target exponent.
-/
noncomputable def besovAtomConstant
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞) : ℝ :=
  ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
    WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
      (besovAtomGeometricWeight G β p)

/-- The Besov-atom normalization constant is nonnegative. -/
theorem besovAtomConstant_nonneg
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞) :
    0 ≤ besovAtomConstant G β p qtilde := by
  unfold besovAtomConstant
  refine mul_nonneg (Real.rpow_nonneg (by positivity) _) ?_
  exact WeakGridSpace.LpGridRepresentation.cCoefficient_nonneg p qtilde
    (besovAtomGeometricWeight G β p)
    (fun k => Real.rpow_nonneg
      (Real.rpow_nonneg
        (pow_nonneg (le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2) k) _) _)

private theorem besovAtomGeometric_cCoefficientFinite
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞) [Fact (1 ≤ qtilde)] :
    WeakGridSpace.LpGridRepresentation.cCoefficientFinite p qtilde
      (besovAtomGeometricWeight G β p) := by
  let ρ : ℝ := G.grid.lambda2 ^ β
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp.out).ne' hp_top
  have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
    le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hρ_nonneg : 0 ≤ ρ := Real.rpow_nonneg hlam_nonneg _
  have hρ_lt_one : ρ < 1 := by
    simpa [ρ] using Real.rpow_lt_one hlam_nonneg G.grid.hlambda2_lt_one hβ
  have hgeom_root :
      ∀ k, (besovAtomGeometricWeight G β p k) ^ (1 / p.toReal) = ρ ^ k := by
    intro k
    have hgeom_nonneg : 0 ≤ (G.grid.lambda2 ^ k : ℝ) ^ β :=
      Real.rpow_nonneg (pow_nonneg hlam_nonneg k) _
    calc
      (besovAtomGeometricWeight G β p k) ^ (1 / p.toReal)
          = (((G.grid.lambda2 ^ k : ℝ) ^ β) ^ p.toReal) ^ (1 / p.toReal) := by
              rfl
      _ = (G.grid.lambda2 ^ k : ℝ) ^ β := by
              simpa [one_div] using Real.rpow_rpow_inv hgeom_nonneg hp_pos.ne'
      _ = ρ ^ k := by
              calc
                (G.grid.lambda2 ^ k : ℝ) ^ β =
                    G.grid.lambda2 ^ ((k : ℝ) * β) := by
                    simpa [mul_comm] using
                      (Real.rpow_natCast_mul hlam_nonneg k β).symm
                _ = G.grid.lambda2 ^ (β * k) := by ring_nf
                _ = (G.grid.lambda2 ^ β) ^ k := by
                    simpa [ρ, mul_comm] using
                      (Real.rpow_mul_natCast hlam_nonneg β k)
  have hgeom_sum : Summable (fun k : ℕ => ρ ^ k) :=
    summable_geometric_of_lt_one hρ_nonneg hρ_lt_one
  by_cases hq1 : qtilde = 1
  · have hbdd : BddAbove
        (Set.range fun k => besovAtomGeometricWeight G β p k ^ (1 / p.toReal)) := by
      refine ⟨∑' k, ρ ^ k, ?_⟩
      intro x hx
      rcases hx with ⟨k, rfl⟩
      change besovAtomGeometricWeight G β p k ^ (1 / p.toReal) ≤ ∑' k, ρ ^ k
      rw [hgeom_root k]
      simpa using
        sum_le_hasSum ({k} : Finset ℕ)
          (fun n _ => pow_nonneg hρ_nonneg n) hgeom_sum.hasSum
    simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1] using hbdd
  · by_cases hqtop : qtilde = ∞
    · have hsum : Summable
          (fun k => besovAtomGeometricWeight G β p k ^ (1 / p.toReal)) :=
        hgeom_sum.congr fun k => (hgeom_root k).symm
      simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop] using hsum
    · let q' : ℝ≥0∞ := qtilde / (qtilde - 1)
      have hq_toReal_le : (1 : ℝ) ≤ qtilde.toReal := by
        have h := ENNReal.toReal_mono hqtop (Fact.out : 1 ≤ qtilde)
        simpa using h
      have hq_toReal_ne_one : qtilde.toReal ≠ 1 := by
        intro hreal
        apply hq1
        exact ((ENNReal.toReal_eq_toReal_iff' ENNReal.one_ne_top hqtop).mp
          (by simp [hreal])).symm
      have hq_toReal_one : 1 < qtilde.toReal :=
        lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
      have hq_conj : q'.toReal.HolderConjugate qtilde.toReal := by
        simpa [q'] using
          WeakGridSpace.LpGridRepresentation.holderConjugate_q_div_qsub1_toReal
            (q := qtilde) hq_toReal_one hqtop
      have hq'_pos : 0 < q'.toReal := by
        rw [Real.holderConjugate_iff] at hq_conj
        exact zero_lt_one.trans hq_conj.1
      have hρq_nonneg : 0 ≤ ρ ^ q'.toReal := Real.rpow_nonneg hρ_nonneg _
      have hρq_lt_one : ρ ^ q'.toReal < 1 :=
        Real.rpow_lt_one hρ_nonneg hρ_lt_one hq'_pos
      have hsum_qgeom : Summable (fun k : ℕ => (ρ ^ q'.toReal) ^ k) :=
        summable_geometric_of_lt_one hρq_nonneg hρq_lt_one
      have hroot_q : ∀ k,
          besovAtomGeometricWeight G β p k ^ (q'.toReal / p.toReal) =
            (ρ ^ q'.toReal) ^ k := by
        intro k
        have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
          field_simp [hp_pos.ne']
        calc
          besovAtomGeometricWeight G β p k ^ (q'.toReal / p.toReal)
              = besovAtomGeometricWeight G β p k ^ ((1 / p.toReal) * q'.toReal) := by
                  rw [hdiv]
          _ = (besovAtomGeometricWeight G β p k ^ (1 / p.toReal)) ^ q'.toReal := by
                  rw [Real.rpow_mul]
                  exact Real.rpow_nonneg
                    (Real.rpow_nonneg (pow_nonneg hlam_nonneg k) _) _
          _ = (ρ ^ k) ^ q'.toReal := by rw [hgeom_root k]
          _ = (ρ ^ q'.toReal) ^ k := by
              calc
                (ρ ^ k : ℝ) ^ q'.toReal = ρ ^ ((k : ℝ) * q'.toReal) := by
                    simpa [mul_comm] using
                      (Real.rpow_natCast_mul hρ_nonneg k q'.toReal).symm
                _ = ρ ^ (q'.toReal * k) := by ring_nf
                _ = (ρ ^ q'.toReal) ^ k := by
                    simpa [mul_comm] using
                      (Real.rpow_mul_natCast hρ_nonneg q'.toReal k)
      have hsum : Summable
          (fun k => besovAtomGeometricWeight G β p k ^ (q'.toReal / p.toReal)) :=
        hsum_qgeom.congr fun k => (hroot_q k).symm
      simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, q'] using hsum

/--
The geometric normalization coefficient for Besov atoms is at least one.

The reason is simple: its underlying geometric weight has first term equal to
one, and each of the coefficient-cost cases dominates that first term.
-/
private theorem one_le_besovAtomGeometric_cCoefficient
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞) [Fact (1 ≤ qtilde)] :
    1 ≤ WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
      (besovAtomGeometricWeight G β p) := by
  classical
  let b : ℕ → ℝ := besovAtomGeometricWeight G β p
  have hb_nonneg : ∀ k, 0 ≤ b k := by
    intro k
    exact Real.rpow_nonneg
      (Real.rpow_nonneg
        (pow_nonneg (le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2) k) _) _
  have hb0 : b 0 = 1 := by
    simp [b, besovAtomGeometricWeight]
  have hfin := besovAtomGeometric_cCoefficientFinite G β p qtilde hβ hp hp_top
  by_cases hq1 : qtilde = 1
  · have hbdd :
        BddAbove (Set.range fun k => b k ^ (1 / p.toReal)) := by
      simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, b] using hfin
    have hone_mem : (1 : ℝ) ∈ Set.range fun k => b k ^ (1 / p.toReal) := by
      refine ⟨0, ?_⟩
      simp [hb0]
    simpa [WeakGridSpace.LpGridRepresentation.cCoefficient, hq1, b] using
      le_csSup hbdd hone_mem
  · by_cases hqtop : qtilde = ∞
    · have hsum : Summable fun k => b k ^ (1 / p.toReal) := by
        simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, b] using hfin
      have hsingle :
          (∑ k ∈ ({0} : Finset ℕ), b k ^ (1 / p.toReal)) = 1 := by
        simp [hb0]
      calc
        1 = ∑ k ∈ ({0} : Finset ℕ), b k ^ (1 / p.toReal) := hsingle.symm
        _ ≤ ∑' k, b k ^ (1 / p.toReal) :=
            hsum.sum_le_tsum ({0} : Finset ℕ)
              (fun k _ => Real.rpow_nonneg (hb_nonneg k) _)
        _ = WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
              (besovAtomGeometricWeight G β p) := by
            simp [WeakGridSpace.LpGridRepresentation.cCoefficient, hqtop, b]
    · let q' : ℝ≥0∞ := qtilde / (qtilde - 1)
      have hq_toReal_le : (1 : ℝ) ≤ qtilde.toReal := by
        have h := ENNReal.toReal_mono hqtop (Fact.out : 1 ≤ qtilde)
        simpa using h
      have hq_toReal_ne_one : qtilde.toReal ≠ 1 := by
        intro hreal
        apply hq1
        exact ((ENNReal.toReal_eq_toReal_iff' ENNReal.one_ne_top hqtop).mp
          (by simp [hreal])).symm
      have hq_toReal_one : 1 < qtilde.toReal :=
        lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
      have hq_conj : q'.toReal.HolderConjugate qtilde.toReal := by
        simpa [q'] using
          WeakGridSpace.LpGridRepresentation.holderConjugate_q_div_qsub1_toReal
            (q := qtilde) hq_toReal_one hqtop
      have hq'_pos : 0 < q'.toReal := by
        rw [Real.holderConjugate_iff] at hq_conj
        exact zero_lt_one.trans hq_conj.1
      have hsum : Summable fun k => b k ^ (q'.toReal / p.toReal) := by
        simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, q', b]
          using hfin
      have hsingle :
          (∑ k ∈ ({0} : Finset ℕ), b k ^ (q'.toReal / p.toReal)) = 1 := by
        simp [hb0]
      have hsum_ge_one : 1 ≤ ∑' k, b k ^ (q'.toReal / p.toReal) := by
        calc
          1 = ∑ k ∈ ({0} : Finset ℕ), b k ^ (q'.toReal / p.toReal) := hsingle.symm
          _ ≤ ∑' k, b k ^ (q'.toReal / p.toReal) :=
              hsum.sum_le_tsum ({0} : Finset ℕ)
                (fun k _ => Real.rpow_nonneg (hb_nonneg k) _)
      have hsum_nonneg : 0 ≤ ∑' k, b k ^ (q'.toReal / p.toReal) :=
        tsum_nonneg fun k => Real.rpow_nonneg (hb_nonneg k) _
      calc
        1 ≤ (∑' k, b k ^ (q'.toReal / p.toReal)) ^ (1 / q'.toReal) := by
          simpa using
            Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num)
              hsum_ge_one (one_div_pos.mpr hq'_pos).le
        _ = WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
              (besovAtomGeometricWeight G β p) := by
            simp [WeakGridSpace.LpGridRepresentation.cCoefficient, hq1, hqtop, q', b]

/-- The Besov-atom normalizing constant is at least one on a good grid. -/
theorem one_le_besovAtomConstant
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞) [Fact (1 ≤ qtilde)] :
    1 ≤ besovAtomConstant G β p qtilde := by
  have hcoeff :=
    one_le_besovAtomGeometric_cCoefficient G β p qtilde hβ hp hp_top
  simpa [besovAtomConstant, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid] using
    hcoeff

private theorem induced_cCoefficientFinite
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G)
    (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞) [Fact (1 ≤ qtilde)] :
    WeakGridSpace.LpGridRepresentation.cCoefficientFinite p qtilde
      (fun k =>
        (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell)
          β p p k) ^ p.toReal) := by
  let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  let w : ℕ → ℝ := fun k =>
    WeakGridSpace.LpGridRepresentation.levelMeasureWeight W β p p k
  let M : ℝ := (G.grid.μ Q.cell).toReal ^ β
  let ρ : ℝ := G.grid.lambda2 ^ β
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp.out).ne' hp_top
  have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
    le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hρ_nonneg : 0 ≤ ρ := Real.rpow_nonneg hlam_nonneg _
  have hρ_lt_one : ρ < 1 := by
    simpa [ρ] using Real.rpow_lt_one hlam_nonneg G.grid.hlambda2_lt_one hβ
  have hM_nonneg : 0 ≤ M := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg W β p p k
  have hgeom_eq : ∀ k, (G.grid.lambda2 ^ k : ℝ) ^ β = ρ ^ k := by
    intro k
    calc
      (G.grid.lambda2 ^ k : ℝ) ^ β =
          G.grid.lambda2 ^ ((k : ℝ) * β) := by
          simpa [mul_comm] using (Real.rpow_natCast_mul hlam_nonneg k β).symm
      _ = G.grid.lambda2 ^ (β * k) := by ring_nf
      _ = (G.grid.lambda2 ^ β) ^ k := by
          simpa [ρ, mul_comm] using (Real.rpow_mul_natCast hlam_nonneg β k)
  have hw_bound : ∀ k, w k ≤ M * ρ ^ k := by
    intro k
    simpa [W, w, M, hgeom_eq k] using
      induced_levelMeasureWeight_le_geometric G Q β p hβ k
  have hgeom_sum : Summable (fun k : ℕ => M * ρ ^ k) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (summable_geometric_of_lt_one hρ_nonneg hρ_lt_one).mul_left M
  have hroot : ∀ k, ((w k) ^ p.toReal) ^ (1 / p.toReal) = w k := by
    intro k
    simpa [one_div] using Real.rpow_rpow_inv (hw_nonneg k) hp_pos.ne'
  by_cases hq1 : qtilde = 1
  · have hbdd : BddAbove (Set.range fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
      refine ⟨∑' k, M * ρ ^ k, ?_⟩
      intro x hx
      rcases hx with ⟨k, rfl⟩
      change (w k ^ p.toReal) ^ (1 / p.toReal) ≤ ∑' k, M * ρ ^ k
      rw [hroot k]
      exact le_trans (hw_bound k)
        (by
          simpa using
            sum_le_hasSum ({k} : Finset ℕ)
              (fun n _ => mul_nonneg hM_nonneg (pow_nonneg hρ_nonneg n))
              hgeom_sum.hasSum)
    simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, W, w] using hbdd
  · by_cases hqtop : qtilde = ∞
    · have hsum_root : Summable (fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
        refine Summable.of_nonneg_of_le
          (fun k => by rw [hroot k]; exact hw_nonneg k)
          (fun k => by rw [hroot k]; exact hw_bound k)
          hgeom_sum
      simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, W, w]
        using hsum_root
    · let q' : ℝ≥0∞ := qtilde / (qtilde - 1)
      have hq_toReal_le : (1 : ℝ) ≤ qtilde.toReal := by
        have h := ENNReal.toReal_mono hqtop (Fact.out : 1 ≤ qtilde)
        simpa using h
      have hq_toReal_ne_one : qtilde.toReal ≠ 1 := by
        intro hreal
        apply hq1
        exact ((ENNReal.toReal_eq_toReal_iff' ENNReal.one_ne_top hqtop).mp
          (by simp [hreal])).symm
      have hq_toReal_one : 1 < qtilde.toReal :=
        lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
      have hq_conj : q'.toReal.HolderConjugate qtilde.toReal := by
        simpa [q'] using
          WeakGridSpace.LpGridRepresentation.holderConjugate_q_div_qsub1_toReal
            (q := qtilde) hq_toReal_one hqtop
      have hq'_pos : 0 < q'.toReal := by
        rw [Real.holderConjugate_iff] at hq_conj
        exact zero_lt_one.trans hq_conj.1
      have hsum_qgeom : Summable (fun k : ℕ => M ^ q'.toReal * (ρ ^ q'.toReal) ^ k) := by
        have hρq_nonneg : 0 ≤ ρ ^ q'.toReal := Real.rpow_nonneg hρ_nonneg _
        have hρq_lt_one : ρ ^ q'.toReal < 1 :=
          Real.rpow_lt_one hρ_nonneg hρ_lt_one hq'_pos
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (summable_geometric_of_lt_one hρq_nonneg hρq_lt_one).mul_left (M ^ q'.toReal)
      have hroot_pow : ∀ k,
          ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) = (w k) ^ q'.toReal := by
        intro k
        have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
          field_simp [hp_pos.ne']
        calc
          ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal)
              = ((w k) ^ p.toReal) ^ ((1 / p.toReal) * q'.toReal) := by rw [hdiv]
          _ = (((w k) ^ p.toReal) ^ (1 / p.toReal)) ^ q'.toReal := by
                rw [Real.rpow_mul (Real.rpow_nonneg (hw_nonneg k) _)]
          _ = (w k) ^ q'.toReal := by rw [hroot k]
      have hpow_geom : ∀ k, (ρ ^ k : ℝ) ^ q'.toReal = (ρ ^ q'.toReal) ^ k := by
        intro k
        calc
          (ρ ^ k : ℝ) ^ q'.toReal = ρ ^ ((k : ℝ) * q'.toReal) := by
              simpa [mul_comm] using (Real.rpow_natCast_mul hρ_nonneg k q'.toReal).symm
          _ = ρ ^ (q'.toReal * k) := by ring_nf
          _ = (ρ ^ q'.toReal) ^ k := by
              simpa [mul_comm] using (Real.rpow_mul_natCast hρ_nonneg q'.toReal k)
      have hle_q :
          (fun k => ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal)) ≤
            fun k => M ^ q'.toReal * (ρ ^ q'.toReal) ^ k := by
        intro k
        change (w k ^ p.toReal) ^ (q'.toReal / p.toReal) ≤
          M ^ q'.toReal * (ρ ^ q'.toReal) ^ k
        rw [hroot_pow k]
        calc
          (w k) ^ q'.toReal ≤ (M * ρ ^ k) ^ q'.toReal := by
            exact Real.rpow_le_rpow (hw_nonneg k) (hw_bound k) hq'_pos.le
          _ = M ^ q'.toReal * (ρ ^ k : ℝ) ^ q'.toReal := by
                rw [Real.mul_rpow hM_nonneg (pow_nonneg hρ_nonneg k)]
          _ = M ^ q'.toReal * (ρ ^ q'.toReal) ^ k := by rw [hpow_geom k]
      have hnonneg_q : ∀ k, 0 ≤ ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) := by
        intro k
        exact Real.rpow_nonneg (Real.rpow_nonneg (hw_nonneg k) _) _
      have hsum := Summable.of_nonneg_of_le hnonneg_q hle_q hsum_qgeom
      simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, q', W, w]
        using hsum

/--
The coefficient constant on the grid induced by a cell is controlled by the
ambient geometric model, with the expected factor `μ(Q)^β`.

This is the quantitative part of the induced-grid embedding estimate.  It is
useful whenever a local Besov norm on `Q` has to be converted into a uniform
ambient constant.
-/
theorem induced_cCoefficient_le_geometric
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G)
    (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞) [Fact (1 ≤ qtilde)] :
    WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
        (fun k =>
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell)
            β p p k) ^ p.toReal)
      ≤ (G.grid.μ Q.cell).toReal ^ β *
          WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
            (besovAtomGeometricWeight G β p) := by
  let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  let w : ℕ → ℝ := fun k =>
    WeakGridSpace.LpGridRepresentation.levelMeasureWeight W β p p k
  let geom : ℕ → ℝ := fun k => (G.grid.lambda2 ^ k : ℝ) ^ β
  let M : ℝ := (G.grid.μ Q.cell).toReal ^ β
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp.out).ne' hp_top
  have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
    le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hM_nonneg : 0 ≤ M := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg W β p p k
  have hgeom_nonneg : ∀ k, 0 ≤ geom k := by
    intro k
    exact Real.rpow_nonneg (pow_nonneg hlam_nonneg k) _
  have hw_bound : ∀ k, w k ≤ M * geom k := by
    intro k
    simpa [W, w, geom, M] using
      induced_levelMeasureWeight_le_geometric G Q β p hβ k
  have hroot_actual :
      ∀ k, ((w k) ^ p.toReal) ^ (1 / p.toReal) = w k := by
    intro k
    simpa [one_div] using Real.rpow_rpow_inv (hw_nonneg k) hp_pos.ne'
  have hroot_geom :
      ∀ k, (besovAtomGeometricWeight G β p k) ^ (1 / p.toReal) = geom k := by
    intro k
    simpa [besovAtomGeometricWeight, geom, one_div] using
      Real.rpow_rpow_inv (hgeom_nonneg k) hp_pos.ne'
  have hactual_fin := induced_cCoefficientFinite G Q β p qtilde hβ hp hp_top
  have hgeom_fin := besovAtomGeometric_cCoefficientFinite G β p qtilde hβ hp hp_top
  by_cases hq1 : qtilde = 1
  · let Cgeom : ℝ :=
      sSup (Set.range fun k => besovAtomGeometricWeight G β p k ^ (1 / p.toReal))
    have hgeom_bdd : BddAbove
        (Set.range fun k => besovAtomGeometricWeight G β p k ^ (1 / p.toReal)) := by
      simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1] using hgeom_fin
    have hCgeom_nonneg : 0 ≤ Cgeom := by
      refine Real.sSup_nonneg ?_
      intro x hx
      rcases hx with ⟨k, rfl⟩
      exact Real.rpow_nonneg (Real.rpow_nonneg (hgeom_nonneg k) _) _
    have hpoint :
        ∀ x ∈ Set.range (fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)),
          x ≤ M * Cgeom := by
      intro x hx
      rcases hx with ⟨k, rfl⟩
      change (w k ^ p.toReal) ^ (1 / p.toReal) ≤ M * Cgeom
      rw [hroot_actual k]
      calc
        w k ≤ M * geom k := hw_bound k
        _ ≤ M * Cgeom := by
          refine mul_le_mul_of_nonneg_left ?_ hM_nonneg
          change geom k ≤ Cgeom
          rw [← hroot_geom k]
          exact le_csSup hgeom_bdd ⟨k, rfl⟩
    calc
      WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
          (fun k => (WeakGridSpace.LpGridRepresentation.levelMeasureWeight W β p p k) ^ p.toReal)
          = sSup (Set.range fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
              simp [WeakGridSpace.LpGridRepresentation.cCoefficient, hq1, W, w]
      _ ≤ M * Cgeom := Real.sSup_le hpoint (mul_nonneg hM_nonneg hCgeom_nonneg)
      _ = M *
            WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
              (besovAtomGeometricWeight G β p) := by
          simp [Cgeom, WeakGridSpace.LpGridRepresentation.cCoefficient, hq1]
  · by_cases hqtop : qtilde = ∞
    · have hactual_sum :
          Summable (fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
        simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, W, w]
          using hactual_fin
      have hgeom_sum :
          Summable (fun k => besovAtomGeometricWeight G β p k ^ (1 / p.toReal)) := by
        simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop]
          using hgeom_fin
      have hactual_sum_w : Summable w := hactual_sum.congr hroot_actual
      have hgeom_sum_geom : Summable geom := hgeom_sum.congr hroot_geom
      have htsum_le :
          (∑' k, w k) ≤ ∑' k, M * geom k :=
        hactual_sum_w.tsum_le_tsum hw_bound (hgeom_sum_geom.mul_left M)
      calc
        WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
          (fun k => (WeakGridSpace.LpGridRepresentation.levelMeasureWeight W β p p k) ^ p.toReal)
            = ∑' k, w k := by
                rw [WeakGridSpace.LpGridRepresentation.cCoefficient, if_neg hq1, if_pos hqtop]
                exact tsum_congr hroot_actual
        _ ≤ ∑' k, M * geom k := htsum_le
        _ = M * ∑' k, geom k := (hgeom_sum_geom.hasSum.mul_left M).tsum_eq
        _ = M *
              WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
                (besovAtomGeometricWeight G β p) := by
            rw [WeakGridSpace.LpGridRepresentation.cCoefficient, if_neg hq1, if_pos hqtop]
            congr 1
            exact (tsum_congr hroot_geom).symm
    · let q' : ℝ≥0∞ := qtilde / (qtilde - 1)
      have hq_toReal_le : (1 : ℝ) ≤ qtilde.toReal := by
        have h := ENNReal.toReal_mono hqtop (Fact.out : 1 ≤ qtilde)
        simpa using h
      have hq_toReal_ne_one : qtilde.toReal ≠ 1 := by
        intro hreal
        apply hq1
        exact ((ENNReal.toReal_eq_toReal_iff' ENNReal.one_ne_top hqtop).mp
          (by simp [hreal])).symm
      have hq_toReal_one : 1 < qtilde.toReal :=
        lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
      have hq_conj : q'.toReal.HolderConjugate qtilde.toReal := by
        simpa [q'] using
          WeakGridSpace.LpGridRepresentation.holderConjugate_q_div_qsub1_toReal
            (q := qtilde) hq_toReal_one hqtop
      have hq'_pos : 0 < q'.toReal := by
        rw [Real.holderConjugate_iff] at hq_conj
        exact zero_lt_one.trans hq_conj.1
      have hactual_qroot : ∀ k,
          ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) = (w k) ^ q'.toReal := by
        intro k
        have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
          field_simp [hp_pos.ne']
        calc
          ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal)
              = ((w k) ^ p.toReal) ^ ((1 / p.toReal) * q'.toReal) := by rw [hdiv]
          _ = (((w k) ^ p.toReal) ^ (1 / p.toReal)) ^ q'.toReal := by
                rw [Real.rpow_mul (Real.rpow_nonneg (hw_nonneg k) _)]
          _ = (w k) ^ q'.toReal := by rw [hroot_actual k]
      have hgeom_qroot : ∀ k,
          besovAtomGeometricWeight G β p k ^ (q'.toReal / p.toReal) =
            (geom k) ^ q'.toReal := by
        intro k
        have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
          field_simp [hp_pos.ne']
        calc
          besovAtomGeometricWeight G β p k ^ (q'.toReal / p.toReal)
              = besovAtomGeometricWeight G β p k ^ ((1 / p.toReal) * q'.toReal) := by
                  rw [hdiv]
          _ = (besovAtomGeometricWeight G β p k ^ (1 / p.toReal)) ^ q'.toReal := by
                  rw [Real.rpow_mul]
                  simpa [besovAtomGeometricWeight, geom] using
                    Real.rpow_nonneg (hgeom_nonneg k) p.toReal
          _ = (geom k) ^ q'.toReal := by rw [hroot_geom k]
      have hactual_sum :
          Summable (fun k => (w k) ^ q'.toReal) := by
        have hraw : Summable
            (fun k => ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal)) := by
          simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, q', W, w]
            using hactual_fin
        exact hraw.congr hactual_qroot
      have hgeom_sum :
          Summable (fun k => (geom k) ^ q'.toReal) := by
        have hraw : Summable
            (fun k => besovAtomGeometricWeight G β p k ^ (q'.toReal / p.toReal)) := by
          simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, q']
            using hgeom_fin
        exact hraw.congr hgeom_qroot
      have hpoint_q :
          (fun k => (w k) ^ q'.toReal) ≤
            fun k => M ^ q'.toReal * (geom k) ^ q'.toReal := by
        intro k
        calc
          (w k) ^ q'.toReal ≤ (M * geom k) ^ q'.toReal := by
            exact Real.rpow_le_rpow (hw_nonneg k) (hw_bound k) hq'_pos.le
          _ = M ^ q'.toReal * (geom k) ^ q'.toReal := by
                rw [Real.mul_rpow hM_nonneg (hgeom_nonneg k)]
      have hscaled_sum : Summable (fun k => M ^ q'.toReal * (geom k) ^ q'.toReal) :=
        hgeom_sum.mul_left (M ^ q'.toReal)
      have hsum_le :
          (∑' k, (w k) ^ q'.toReal)
            ≤ ∑' k, M ^ q'.toReal * (geom k) ^ q'.toReal :=
        hactual_sum.tsum_le_tsum hpoint_q hscaled_sum
      have hsum_scaled :
          (∑' k, M ^ q'.toReal * (geom k) ^ q'.toReal)
            = M ^ q'.toReal * ∑' k, (geom k) ^ q'.toReal :=
        (hgeom_sum.hasSum.mul_left (M ^ q'.toReal)).tsum_eq
      have hactual_nonneg : 0 ≤ ∑' k, (w k) ^ q'.toReal :=
        tsum_nonneg fun k => Real.rpow_nonneg (hw_nonneg k) _
      have hgeom_tsum_nonneg : 0 ≤ ∑' k, (geom k) ^ q'.toReal :=
        tsum_nonneg fun k => Real.rpow_nonneg (hgeom_nonneg k) _
      have hroot_scaled :
          (M ^ q'.toReal * ∑' k, (geom k) ^ q'.toReal) ^ (1 / q'.toReal)
            = M * (∑' k, (geom k) ^ q'.toReal) ^ (1 / q'.toReal) := by
        rw [Real.mul_rpow
          (Real.rpow_nonneg hM_nonneg _) hgeom_tsum_nonneg]
        congr 1
        simpa [one_div] using Real.rpow_rpow_inv hM_nonneg hq'_pos.ne'
      have hCactual :
          WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
            (fun k => (WeakGridSpace.LpGridRepresentation.levelMeasureWeight W β p p k) ^ p.toReal)
            = (∑' k, (w k) ^ q'.toReal) ^ (1 / q'.toReal) := by
        rw [WeakGridSpace.LpGridRepresentation.cCoefficient, if_neg hq1, if_neg hqtop]
        dsimp [q']
        congr 1
        exact tsum_congr hactual_qroot
      have hCgeom :
          WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
            (besovAtomGeometricWeight G β p)
            = (∑' k, (geom k) ^ q'.toReal) ^ (1 / q'.toReal) := by
        rw [WeakGridSpace.LpGridRepresentation.cCoefficient, if_neg hq1, if_neg hqtop]
        dsimp [q']
        congr 1
        exact tsum_congr hgeom_qroot
      calc
        WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
          (fun k => (WeakGridSpace.LpGridRepresentation.levelMeasureWeight W β p p k) ^ p.toReal)
            = (∑' k, (w k) ^ q'.toReal) ^ (1 / q'.toReal) := hCactual
        _ ≤ (∑' k, M ^ q'.toReal * (geom k) ^ q'.toReal) ^ (1 / q'.toReal) := by
              exact Real.rpow_le_rpow hactual_nonneg hsum_le (by positivity)
        _ = (M ^ q'.toReal * ∑' k, (geom k) ^ q'.toReal) ^ (1 / q'.toReal) := by
              rw [hsum_scaled]
        _ = M * (∑' k, (geom k) ^ q'.toReal) ^ (1 / q'.toReal) := hroot_scaled
        _ = M *
              WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
                (besovAtomGeometricWeight G β p) := by
            rw [hCgeom]

private theorem levelCoeffPower_root_le_pqCost
    {G : WeakGridSpace.WeakGridSpace (α := α)}
    {s : ℝ} {p u q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {A : WeakGridSpace.AtomFamily G s p u}
    {g : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A g)
    (hp_top : p ≠ ∞)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (k : ℕ) :
    (R.levelCoeffPower k) ^ (1 / p.toReal) ≤
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  classical
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_top
  by_cases hqtop : q = ∞
  · have hbdd : BddAbove
        (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hRfin
    rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos hqtop]
    exact le_csSup hbdd ⟨k, rfl⟩
  · have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hqtop
    have hsum_nonneg :
        0 ≤ ∑' n, (R.levelCoeffPower n) ^ (q.toReal / p.toReal) :=
      tsum_nonneg fun n => Real.rpow_nonneg (R.levelCoeffPower_nonneg n) _
    have hterm_le :
        (R.levelCoeffPower k) ^ (q.toReal / p.toReal)
          ≤ ∑' n, (R.levelCoeffPower n) ^ (q.toReal / p.toReal) := by
      have hsum : Summable fun n => (R.levelCoeffPower n) ^ (q.toReal / p.toReal) := by
        simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hRfin
      simpa using
        sum_le_hasSum ({k} : Finset ℕ)
          (fun n _ => Real.rpow_nonneg (R.levelCoeffPower_nonneg n) _) hsum.hasSum
    have hpow_le :=
      Real.rpow_le_rpow (Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _)
        hterm_le (div_nonneg zero_le_one hq_pos.le)
    have hleft :
        ((R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) =
          (R.levelCoeffPower k) ^ (1 / p.toReal) := by
      have hdiv : q.toReal / p.toReal * (1 / q.toReal) = 1 / p.toReal := by
        field_simp [hq_pos.ne']
      calc
        ((R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)
            = (R.levelCoeffPower k) ^ ((q.toReal / p.toReal) * (1 / q.toReal)) := by
                rw [← Real.rpow_mul (R.levelCoeffPower_nonneg k)]
        _ = (R.levelCoeffPower k) ^ (1 / p.toReal) := by rw [hdiv]
    rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hqtop]
    rw [hleft] at hpow_le
    exact hpow_le

private theorem levelCoeffPower_le_pqCost_rpow
    {G : WeakGridSpace.WeakGridSpace (α := α)}
    {s : ℝ} {p u q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {A : WeakGridSpace.AtomFamily G s p u}
    {g : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A g)
    (hp_top : p ≠ ∞)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (k : ℕ) :
    R.levelCoeffPower k ≤
      (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) ^ p.toReal := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_top
  have hroot := levelCoeffPower_root_le_pqCost R hp_top hRfin k
  have hcost_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
    WeakGridSpace.LpGridRepresentation.pqCost_nonneg R
  have hpow :
      ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal ≤
        (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) ^ p.toReal :=
    Real.rpow_le_rpow (Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _)
      hroot hp_pos.le
  have hleft :
      ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal =
        R.levelCoeffPower k := by
    have hmul : (1 / p.toReal) * p.toReal = 1 := by
      field_simp [hp_pos.ne']
    calc
      ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal =
          (R.levelCoeffPower k) ^ ((1 / p.toReal) * p.toReal) := by
          rw [← Real.rpow_mul (R.levelCoeffPower_nonneg k)]
      _ = R.levelCoeffPower k := by
          rw [hmul, Real.rpow_one]
  rw [hleft] at hpow
  exact hpow

private noncomputable def souzaBetaBlockToSouzaS
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    {n : ℕ}
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G β p hβ hp.out hp_top) n) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp.out hp_top) n where
  coeff := fun P =>
    B.coeff P * (((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ)
  atom := fun P => by
    let b : ℂ := B.atom P
    exact (((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) * b
  atom_mem := by
    intro P
    have hP_pos : 0 < G.grid.μ P.1 :=
      G.grid.positive_measure n P.1 P.2
    have hP_finite : G.grid.μ P.1 ≠ ∞ := by
      letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ P.1
    have hP_toReal_pos : 0 < (G.grid.μ P.1).toReal :=
      ENNReal.toReal_pos hP_pos.ne' hP_finite
    have hscale_nonneg : 0 ≤ (G.grid.μ P.1).toReal ^ (s - β) :=
      Real.rpow_nonneg hP_toReal_pos.le _
    let b : ℂ := B.atom P
    have hB :
        ‖b‖ ≤ (G.grid.μ P.1).toReal ^ (β - p.toReal⁻¹) := by
      dsimp [b]
      simpa [souzaAtomFamily, souzaAtomsSet] using B.atom_mem P
    change
      ‖(((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) * b‖ ≤
        (G.grid.μ P.1).toReal ^ (s - p.toReal⁻¹)
    calc
      ‖(((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) * b‖
          = (G.grid.μ P.1).toReal ^ (s - β) * ‖b‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hscale_nonneg]
      _ ≤ (G.grid.μ P.1).toReal ^ (s - β) *
            (G.grid.μ P.1).toReal ^ (β - p.toReal⁻¹) := by
              exact mul_le_mul_of_nonneg_left hB hscale_nonneg
      _ = (G.grid.μ P.1).toReal ^ (s - p.toReal⁻¹) := by
              rw [← Real.rpow_add hP_toReal_pos]
              ring_nf

private theorem souzaBetaBlockToSouzaS_toFunLt
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    {n : ℕ}
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G β p hβ hp.out hp_top) n) :
    (souzaBetaBlockToSouzaS G s β p hs hβ hp hp_top B).toFunLt
        (souzaAtomFamily G s p hs hp.out hp_top) =
      B.toFunLt (souzaAtomFamily G β p hβ hp.out hp_top) := by
  classical
  funext x
  unfold WeakGridSpace.LevelBlock.toFunLt souzaBetaBlockToSouzaS
  refine Finset.sum_congr rfl ?_
  intro P _hP
  have hP_pos : 0 < G.grid.μ P.1 :=
    G.grid.positive_measure n P.1 P.2
  have hP_finite : G.grid.μ P.1 ≠ ∞ := by
    letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ P.1
  have hP_toReal_pos : 0 < (G.grid.μ P.1).toReal :=
    ENNReal.toReal_pos hP_pos.ne' hP_finite
  have hscale :
      ((G.grid.μ P.1).toReal ^ (β - s) : ℝ) *
          (G.grid.μ P.1).toReal ^ (s - β) = 1 := by
    calc
      ((G.grid.μ P.1).toReal ^ (β - s) : ℝ) *
          (G.grid.μ P.1).toReal ^ (s - β)
          = (G.grid.μ P.1).toReal ^ ((β - s) + (s - β)) := by
              rw [← Real.rpow_add hP_toReal_pos]
      _ = (G.grid.μ P.1).toReal ^ (0 : ℝ) := by ring_nf
      _ = 1 := by rw [Real.rpow_zero]
  have hscaleC :
      (((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ) *
          (((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hscale
  by_cases hx : x ∈ P.1
  · dsimp [WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily,
      souzaLocalVectorSpace, WeakGridSpace.levelCellToWeakGridCell]
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    let b : ℂ := B.atom P
    change
      B.coeff P * (((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ) *
          ((((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) * b)
        = B.coeff P * b
    calc
      B.coeff P * (((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ) *
          ((((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) * b)
          = B.coeff P *
              (((((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ) *
                  (((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ)) * b) := by
              ring
      _ = B.coeff P * b := by
              rw [hscaleC]
              ring
  · dsimp [WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily,
      souzaLocalVectorSpace, WeakGridSpace.levelCellToWeakGridCell]
    simp [hx]

private theorem souzaBetaBlockToSouzaS_toLp
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    {n : ℕ}
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G β p hβ hp.out hp_top) n) :
    (souzaBetaBlockToSouzaS G s β p hs hβ hp hp_top B).toLp
        (souzaAtomFamily G s p hs hp.out hp_top) =
      B.toLp (souzaAtomFamily G β p hβ hp.out hp_top) := by
  apply Lp.ext
  have hleft :
      ((souzaBetaBlockToSouzaS G s β p hs hβ hp hp_top B).toLp
          (souzaAtomFamily G s p hs hp.out hp_top) : α → ℂ)
        =ᵐ[G.toWeakGridSpace.measure]
      (souzaBetaBlockToSouzaS G s β p hs hβ hp hp_top B).toFunLt
        (souzaAtomFamily G s p hs hp.out hp_top) :=
    WeakGridSpace.LevelBlock.coeFn_toLp
      (souzaAtomFamily G s p hs hp.out hp_top)
      (souzaBetaBlockToSouzaS G s β p hs hβ hp hp_top B)
  have hmid :
      (souzaBetaBlockToSouzaS G s β p hs hβ hp hp_top B).toFunLt
          (souzaAtomFamily G s p hs hp.out hp_top)
        =ᵐ[G.toWeakGridSpace.measure]
      B.toFunLt (souzaAtomFamily G β p hβ hp.out hp_top) :=
    Filter.Eventually.of_forall
      (fun x => congrFun
        (souzaBetaBlockToSouzaS_toFunLt G s β p hs hβ hp hp_top B) x)
  have hright :
      (B.toLp (souzaAtomFamily G β p hβ hp.out hp_top) : α → ℂ)
        =ᵐ[G.toWeakGridSpace.measure]
      B.toFunLt (souzaAtomFamily G β p hβ hp.out hp_top) :=
    WeakGridSpace.LevelBlock.coeFn_toLp
      (souzaAtomFamily G β p hβ hp.out hp_top) B
  exact hleft.trans (hmid.trans hright.symm)

private noncomputable def souzaBetaRepresentationToSouzaS
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G β p hβ hp.out hp_top) g) :
    WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp.out hp_top) g where
  block n := souzaBetaBlockToSouzaS G s β p hs hβ hp hp_top (R.block n)
  hasSum := by
    refine HasSum.congr_fun R.hasSum ?_
    intro n
    exact souzaBetaBlockToSouzaS_toLp G s β p hs hβ hp hp_top (R.block n)

/--
The induced Souza atom family of smoothness `β` on a parent cell `Q`.

This is the local model used to measure the Besov regularity of an atom
supported on `Q`.
-/
abbrev inducedSouzaAtomFamily
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) :
    WeakGridSpace.AtomFamily
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell) β p ∞ :=
  WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
    (souzaAtomFamily G β p hβ hp.out hp_top)

private noncomputable def besovToSouzaScaledCoeffPower
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G)
    {g : Lp ℂ p
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure}
    (R : WeakGridSpace.LpGridRepresentation
      (inducedSouzaAtomFamily G β p hβ hp hp_top Q) g)
    (k : ℕ) : ℝ :=
  ∑ P : WeakGridSpace.LevelCell
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell) k,
    ‖(R.block k).coeff P *
      (((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ)‖ ^ p.toReal

private noncomputable def inducedSouzaBetaBlockToSouzaS
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) {n : ℕ}
    (B : WeakGridSpace.LevelBlock
      (inducedSouzaAtomFamily G β p hβ hp hp_top Q) n) :
    WeakGridSpace.LevelBlock
      (inducedSouzaAtomFamily G s p hs hp hp_top Q) n where
  coeff := fun P =>
    B.coeff P * (((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ)
  atom := fun P => by
    let b : ℂ := B.atom P
    exact (((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) * b
  atom_mem := by
    intro P
    let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
    have hP_pos : 0 < G.grid.μ P.1 := by
      simpa [W, WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid,
        GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
        WeakGridSpace.WeakGridSpace.measure] using W.grid.positive_measure n P.1 P.2
    have hP_finite : G.grid.μ P.1 ≠ ∞ := by
      letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ P.1
    have hP_toReal_pos : 0 < (G.grid.μ P.1).toReal :=
      ENNReal.toReal_pos hP_pos.ne' hP_finite
    have hscale_nonneg : 0 ≤ (G.grid.μ P.1).toReal ^ (s - β) :=
      Real.rpow_nonneg hP_toReal_pos.le _
    let b : ℂ := B.atom P
    have hB :
        ‖b‖ ≤ (G.grid.μ P.1).toReal ^ (β - p.toReal⁻¹) := by
      dsimp [b]
      simpa [inducedSouzaAtomFamily, WeakGridSpace.inducedAtomFamily,
        WeakGridSpace.inducedWeakGridCellToAmbient, WeakGridSpace.levelCellToWeakGridCell,
        souzaAtomFamily, souzaAtomsSet] using B.atom_mem P
    change
      ‖(((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) * b‖ ≤
        (G.grid.μ P.1).toReal ^ (s - p.toReal⁻¹)
    calc
      ‖(((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) * b‖
          = (G.grid.μ P.1).toReal ^ (s - β) * ‖b‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hscale_nonneg]
      _ ≤ (G.grid.μ P.1).toReal ^ (s - β) *
            (G.grid.μ P.1).toReal ^ (β - p.toReal⁻¹) := by
              exact mul_le_mul_of_nonneg_left hB hscale_nonneg
      _ = (G.grid.μ P.1).toReal ^ (s - p.toReal⁻¹) := by
              rw [← Real.rpow_add hP_toReal_pos]
              ring_nf

private theorem inducedSouzaBetaBlockToSouzaS_toFunLt
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) {n : ℕ}
    (B : WeakGridSpace.LevelBlock
      (inducedSouzaAtomFamily G β p hβ hp hp_top Q) n) :
    (inducedSouzaBetaBlockToSouzaS G s β p hs hβ hp hp_top Q B).toFunLt
        (inducedSouzaAtomFamily G s p hs hp hp_top Q) =
      B.toFunLt (inducedSouzaAtomFamily G β p hβ hp hp_top Q) := by
  classical
  funext x
  unfold WeakGridSpace.LevelBlock.toFunLt inducedSouzaBetaBlockToSouzaS
  refine Finset.sum_congr rfl ?_
  intro P _hP
  let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  have hP_pos : 0 < G.grid.μ P.1 := by
    simpa [W, WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid,
      GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
      WeakGridSpace.WeakGridSpace.measure] using W.grid.positive_measure n P.1 P.2
  have hP_finite : G.grid.μ P.1 ≠ ∞ := by
    letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ P.1
  have hP_toReal_pos : 0 < (G.grid.μ P.1).toReal :=
    ENNReal.toReal_pos hP_pos.ne' hP_finite
  have hscale :
      ((G.grid.μ P.1).toReal ^ (β - s) : ℝ) *
          (G.grid.μ P.1).toReal ^ (s - β) = 1 := by
    calc
      ((G.grid.μ P.1).toReal ^ (β - s) : ℝ) *
          (G.grid.μ P.1).toReal ^ (s - β)
          = (G.grid.μ P.1).toReal ^ ((β - s) + (s - β)) := by
              rw [← Real.rpow_add hP_toReal_pos]
      _ = (G.grid.μ P.1).toReal ^ (0 : ℝ) := by ring_nf
      _ = 1 := by rw [Real.rpow_zero]
  have hscaleC :
      (((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ) *
          (((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hscale
  by_cases hx : x ∈ P.1
  · dsimp [WeakGridSpace.AtomFamily.toFunction, inducedSouzaAtomFamily,
      WeakGridSpace.inducedAtomFamily, WeakGridSpace.inducedWeakGridCellToAmbient,
      souzaAtomFamily, souzaLocalVectorSpace, WeakGridSpace.levelCellToWeakGridCell]
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    let b : ℂ := B.atom P
    change
      B.coeff P * (((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ) *
          ((((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) * b)
        = B.coeff P * b
    calc
      B.coeff P * (((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ) *
          ((((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ) * b)
          = B.coeff P *
              (((((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ) *
                  (((G.grid.μ P.1).toReal ^ (s - β) : ℝ) : ℂ)) * b) := by
              ring
      _ = B.coeff P * b := by
              rw [hscaleC]
              ring
  · dsimp [WeakGridSpace.AtomFamily.toFunction, inducedSouzaAtomFamily,
      WeakGridSpace.inducedAtomFamily, WeakGridSpace.inducedWeakGridCellToAmbient,
      souzaAtomFamily, souzaLocalVectorSpace, WeakGridSpace.levelCellToWeakGridCell]
    simp [hx]

private theorem inducedSouzaBetaBlockToSouzaS_toLp
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) {n : ℕ}
    (B : WeakGridSpace.LevelBlock
      (inducedSouzaAtomFamily G β p hβ hp hp_top Q) n) :
    (inducedSouzaBetaBlockToSouzaS G s β p hs hβ hp hp_top Q B).toLp
        (inducedSouzaAtomFamily G s p hs hp hp_top Q) =
      B.toLp (inducedSouzaAtomFamily G β p hβ hp hp_top Q) := by
  apply Lp.ext
  let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  have hleft :
      ((inducedSouzaBetaBlockToSouzaS G s β p hs hβ hp hp_top Q B).toLp
          (inducedSouzaAtomFamily G s p hs hp hp_top Q) : α → ℂ)
        =ᵐ[W.measure]
      (inducedSouzaBetaBlockToSouzaS G s β p hs hβ hp hp_top Q B).toFunLt
        (inducedSouzaAtomFamily G s p hs hp hp_top Q) :=
    WeakGridSpace.LevelBlock.coeFn_toLp
      (inducedSouzaAtomFamily G s p hs hp hp_top Q)
      (inducedSouzaBetaBlockToSouzaS G s β p hs hβ hp hp_top Q B)
  have hmid :
      (inducedSouzaBetaBlockToSouzaS G s β p hs hβ hp hp_top Q B).toFunLt
          (inducedSouzaAtomFamily G s p hs hp hp_top Q)
        =ᵐ[W.measure]
      B.toFunLt (inducedSouzaAtomFamily G β p hβ hp hp_top Q) :=
    Filter.Eventually.of_forall
      (fun x => congrFun
        (inducedSouzaBetaBlockToSouzaS_toFunLt G s β p hs hβ hp hp_top Q B) x)
  have hright :
      (B.toLp (inducedSouzaAtomFamily G β p hβ hp hp_top Q) : α → ℂ)
        =ᵐ[W.measure]
      B.toFunLt (inducedSouzaAtomFamily G β p hβ hp hp_top Q) :=
    WeakGridSpace.LevelBlock.coeFn_toLp
      (inducedSouzaAtomFamily G β p hβ hp hp_top Q) B
  exact hleft.trans (hmid.trans hright.symm)

private noncomputable def inducedSouzaBetaRepresentationToSouzaS
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G)
    {g : Lp ℂ p
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure}
    (R : WeakGridSpace.LpGridRepresentation
      (inducedSouzaAtomFamily G β p hβ hp hp_top Q) g) :
    WeakGridSpace.LpGridRepresentation
      (inducedSouzaAtomFamily G s p hs hp hp_top Q) g where
  block n := inducedSouzaBetaBlockToSouzaS G s β p hs hβ hp hp_top Q (R.block n)
  hasSum := by
    refine HasSum.congr_fun R.hasSum ?_
    intro n
    exact inducedSouzaBetaBlockToSouzaS_toLp G s β p hs hβ hp hp_top Q (R.block n)

private theorem inducedSouzaBetaRepresentationToSouzaS_levelCoeffPower
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G)
    {g : Lp ℂ p
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure}
    (R : WeakGridSpace.LpGridRepresentation
      (inducedSouzaAtomFamily G β p hβ hp hp_top Q) g)
    (k : ℕ) :
    (inducedSouzaBetaRepresentationToSouzaS G s β p hs hβ hp hp_top Q R).levelCoeffPower k =
      besovToSouzaScaledCoeffPower G s β p hβ hp hp_top Q R k := by
  unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
  unfold inducedSouzaBetaRepresentationToSouzaS inducedSouzaBetaBlockToSouzaS
  rfl

/--
An `(s, β, p, qtilde)` Besov atom representative supported on `Q`.

The predicate is stated for a concrete function on the ambient good-grid
measure.  It asks that the function has an `L^p` class admitting an induced
Besov representation of order `β` on the grid inside `Q`, with coefficient
gauge bounded by `C_ba⁻¹ μ(Q)^(s-β)`.
-/
def IsBesovAtom
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) (a : α → ℂ) : Prop :=
  ∃ ha : MemLp a p G.grid.μ,
  ∃ R : WeakGridSpace.LpGridRepresentation
      (inducedSouzaAtomFamily G β p hβ hp hp_top Q) ha.toLp,
    WeakGridSpace.LpGridRepresentation.FinitePQCost (q := qtilde) R ∧
      WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R
        ≤ (besovAtomConstant G β p qtilde)⁻¹ *
            (G.grid.μ Q.cell).toReal ^ (s - β)

private theorem besovToSouzaScaledCoeffPower_root_le
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (hβ : 0 < β) (hβs : s < β) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G)
    {g : Lp ℂ p
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure}
    (R : WeakGridSpace.LpGridRepresentation
      (inducedSouzaAtomFamily G β p hβ (inferInstance : Fact (1 ≤ p)) hp_top Q) g)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := qtilde) R)
    (k : ℕ) :
    (besovToSouzaScaledCoeffPower G s β p hβ
        (inferInstance : Fact (1 ≤ p)) hp_top Q R k) ^ (1 / p.toReal)
      ≤ WeakGridSpace.LpGridRepresentation.levelMeasureWeight
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell)
          (β - s) p p k *
        WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R := by
  classical
  let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  let A := inducedSouzaAtomFamily G β p hβ (inferInstance : Fact (1 ≤ p)) hp_top Q
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_top
  have hdelta_nonneg : 0 ≤ β - s := sub_nonneg.mpr hβs.le
  have hs_weight : 0 ≤ (β - s) - 1 / p.toReal + 1 / p.toReal := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdelta_nonneg
  have hweighted :
      (∑ P : WeakGridSpace.LevelCell W k,
          ((W.measure P.1).toReal ^ ((β - s) - 1 / p.toReal + 1 / p.toReal) *
            ‖(R.block k).coeff P‖) ^ p.toReal)
        ≤ (WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k *
            (R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal := by
    let M : ℝ := WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k
    have hM_nonneg : 0 ≤ M :=
      WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg W (β - s) p p k
    have hL_nonneg : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
    have hsum_le :
        (∑ P : WeakGridSpace.LevelCell W k,
            ((W.measure P.1).toReal ^ ((β - s) - 1 / p.toReal + 1 / p.toReal) *
              ‖(R.block k).coeff P‖) ^ p.toReal)
          ≤ ∑ P : WeakGridSpace.LevelCell W k,
              (M * ‖(R.block k).coeff P‖) ^ p.toReal := by
      refine Finset.sum_le_sum fun P _ => ?_
      have hcell_nonneg :
          0 ≤ (W.measure P.1).toReal ^
            ((β - s) - 1 / p.toReal + 1 / p.toReal) :=
        Real.rpow_nonneg ENNReal.toReal_nonneg _
      have hcell_le :
          (W.measure P.1).toReal ^ ((β - s) - 1 / p.toReal + 1 / p.toReal)
            ≤ M := by
        exact WeakGridSpace.LpGridRepresentation.levelCellMeasure_rpow_le_levelMeasureWeight
          W (β - s) p p k hs_weight P
      exact Real.rpow_le_rpow
        (mul_nonneg hcell_nonneg (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hcell_le (norm_nonneg _))
        hp_pos.le
    calc
      (∑ P : WeakGridSpace.LevelCell W k,
          ((W.measure P.1).toReal ^ ((β - s) - 1 / p.toReal + 1 / p.toReal) *
            ‖(R.block k).coeff P‖) ^ p.toReal)
          ≤ ∑ P : WeakGridSpace.LevelCell W k,
              (M * ‖(R.block k).coeff P‖) ^ p.toReal := hsum_le
      _ = M ^ p.toReal * R.levelCoeffPower k := by
          simp_rw [Real.mul_rpow hM_nonneg (norm_nonneg _)]
          rw [← Finset.mul_sum]
          rfl
      _ = (M * (R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal := by
          have hroot_cancel :
              ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal =
                R.levelCoeffPower k := by
            calc
              ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal
                  = (R.levelCoeffPower k) ^ ((1 / p.toReal) * p.toReal) := by
                      rw [← Real.rpow_mul hL_nonneg]
              _ = R.levelCoeffPower k := by
                      have hmul : (1 / p.toReal) * p.toReal = 1 := by
                        field_simp [hp_pos.ne']
                      rw [hmul, Real.rpow_one]
          rw [Real.mul_rpow hM_nonneg (Real.rpow_nonneg hL_nonneg _)]
          rw [hroot_cancel]
  have hscaled_eq :
      besovToSouzaScaledCoeffPower G s β p hβ
          (inferInstance : Fact (1 ≤ p)) hp_top Q R k =
        ∑ P : WeakGridSpace.LevelCell W k,
          ((W.measure P.1).toReal ^ ((β - s) - 1 / p.toReal + 1 / p.toReal) *
            ‖(R.block k).coeff P‖) ^ p.toReal := by
    unfold besovToSouzaScaledCoeffPower
    refine Finset.sum_congr rfl ?_
    intro P _hP
    have hfactor_nonneg :
        0 ≤ (G.grid.μ P.1).toReal ^ (β - s) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hexp : (β - s) - 1 / p.toReal + 1 / p.toReal = β - s := by
      ring
    calc
      ‖(R.block k).coeff P *
        (((G.grid.μ P.1).toReal ^ (β - s) : ℝ) : ℂ)‖ ^ p.toReal
          = ((G.grid.μ P.1).toReal ^ (β - s) *
              ‖(R.block k).coeff P‖) ^ p.toReal := by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hfactor_nonneg]
              ring_nf
      _ = ((W.measure P.1).toReal ^
            ((β - s) - 1 / p.toReal + 1 / p.toReal) *
              ‖(R.block k).coeff P‖) ^ p.toReal := by
              simp [W, WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid,
                GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
                WeakGridSpace.WeakGridSpace.measure]
  have hscaled_nonneg :
      0 ≤ besovToSouzaScaledCoeffPower G s β p hβ
        (inferInstance : Fact (1 ≤ p)) hp_top Q R k := by
    unfold besovToSouzaScaledCoeffPower
    exact Finset.sum_nonneg fun P _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  have hright_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k *
          (R.levelCoeffPower k) ^ (1 / p.toReal) := by
    exact mul_nonneg
      (WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg W (β - s) p p k)
      (Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _)
  have hpow_le :
      (besovToSouzaScaledCoeffPower G s β p hβ
          (inferInstance : Fact (1 ≤ p)) hp_top Q R k) ^ (1 / p.toReal)
        ≤ ((WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k *
            (R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal) ^ (1 / p.toReal) := by
    exact Real.rpow_le_rpow hscaled_nonneg (by simpa [hscaled_eq] using hweighted)
      (div_nonneg zero_le_one hp_pos.le)
  have hcancel :
      ((WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k *
          (R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal) ^ (1 / p.toReal)
        = WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k *
          (R.levelCoeffPower k) ^ (1 / p.toReal) := by
    simpa [one_div] using
      Real.rpow_rpow_inv hright_nonneg hp_pos.ne'
  calc
    (besovToSouzaScaledCoeffPower G s β p hβ
        (inferInstance : Fact (1 ≤ p)) hp_top Q R k) ^ (1 / p.toReal)
        ≤ ((WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k *
            (R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal) ^ (1 / p.toReal) := hpow_le
    _ = WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k *
          (R.levelCoeffPower k) ^ (1 / p.toReal) := hcancel
    _ ≤ WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k *
          WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R := by
          exact mul_le_mul_of_nonneg_left
            (levelCoeffPower_root_le_pqCost R hp_top hRfin k)
            (WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg W (β - s) p p k)

/--
The coefficient decay behind the conversion of a Besov atom into Souza atoms.

For a Besov atom on `Q`, the defining induced `β`-Souza representation has the
rescaled coefficients `m_P = c_P μ(P)^(β-s)` controlled level by level by the
geometric factor `lambda2^(β-s)`. This is the formal version of the claim used
in the paper before applying the transmutation theorem.
-/
theorem besovAtom_to_souza_representation_decay
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (hβ : 0 < β) (hβs : s < β) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) {a : α → ℂ}
    (ha : IsBesovAtom G s β p qtilde hβ
      (inferInstance : Fact (1 ≤ p)) hp_top Q a) :
    ∃ haLp : MemLp a p G.grid.μ,
    ∃ R : WeakGridSpace.LpGridRepresentation
      (inducedSouzaAtomFamily G β p hβ (inferInstance : Fact (1 ≤ p)) hp_top Q)
      haLp.toLp,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := qtilde) R ∧
      WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R
        ≤ (besovAtomConstant G β p qtilde)⁻¹ *
            (G.grid.μ Q.cell).toReal ^ (s - β) ∧
      ∀ k : ℕ,
        (besovToSouzaScaledCoeffPower G s β p hβ
            (inferInstance : Fact (1 ≤ p)) hp_top Q R k) ^ (1 / p.toReal)
          ≤ (besovAtomConstant G β p qtilde)⁻¹ *
              (G.grid.lambda2 ^ k : ℝ) ^ (β - s) := by
  classical
  rcases ha with ⟨haLp, R, hRfin, hRcost⟩
  refine ⟨haLp, R, hRfin, hRcost, ?_⟩
  intro k
  let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  let Cba : ℝ := besovAtomConstant G β p qtilde
  let μQ : ℝ := (G.grid.μ Q.cell).toReal
  let geom : ℝ := (G.grid.lambda2 ^ k : ℝ) ^ (β - s)
  have hdelta_pos : 0 < β - s := sub_pos.mpr hβs
  have hroot :=
    besovToSouzaScaledCoeffPower_root_le G s β p qtilde hβ hβs hp_top Q R hRfin k
  have hweight :
      WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k
        ≤ μQ ^ (β - s) * geom := by
    simpa [W, μQ, geom] using
      induced_levelMeasureWeight_le_geometric G Q (β - s) p hdelta_pos k
  have hcost_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R :=
    WeakGridSpace.LpGridRepresentation.pqCost_nonneg R
  have hweight_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k :=
    WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg W (β - s) p p k
  have hμQ_pos : 0 < μQ := by
    have hQ_pos : 0 < G.grid.μ Q.cell :=
      G.grid.positive_measure Q.level Q.cell Q.mem
    have hQ_finite : G.grid.μ Q.cell ≠ ∞ := by
      letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Q.cell
    exact ENNReal.toReal_pos hQ_pos.ne' hQ_finite
  have hμQ_nonneg : 0 ≤ μQ := hμQ_pos.le
  have hgeom_nonneg : 0 ≤ geom := by
    dsimp [geom]
    exact Real.rpow_nonneg (pow_nonneg
      (le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2) k) _
  have hCba_nonneg : 0 ≤ Cba := by
    dsimp [Cba]
    exact besovAtomConstant_nonneg G β p qtilde
  have hscale_nonneg : 0 ≤ Cba⁻¹ * μQ ^ (s - β) := by
    exact mul_nonneg (inv_nonneg.mpr hCba_nonneg)
      (Real.rpow_nonneg hμQ_nonneg _)
  have hmul_cost :
      WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k *
          WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R
        ≤ (μQ ^ (β - s) * geom) * (Cba⁻¹ * μQ ^ (s - β)) := by
    calc
      WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k *
          WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R
          ≤ (μQ ^ (β - s) * geom) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R := by
              exact mul_le_mul_of_nonneg_right hweight hcost_nonneg
      _ ≤ (μQ ^ (β - s) * geom) * (Cba⁻¹ * μQ ^ (s - β)) := by
              exact mul_le_mul_of_nonneg_left hRcost
                (mul_nonneg (Real.rpow_nonneg hμQ_nonneg _) hgeom_nonneg)
  have hcancel : μQ ^ (β - s) * μQ ^ (s - β) = 1 := by
    calc
      μQ ^ (β - s) * μQ ^ (s - β)
          = μQ ^ ((β - s) + (s - β)) := by
              rw [← Real.rpow_add hμQ_pos]
      _ = μQ ^ (0 : ℝ) := by ring_nf
      _ = 1 := by rw [Real.rpow_zero]
  have htarget :
      (μQ ^ (β - s) * geom) * (Cba⁻¹ * μQ ^ (s - β)) =
        Cba⁻¹ * geom := by
    calc
      (μQ ^ (β - s) * geom) * (Cba⁻¹ * μQ ^ (s - β))
          = Cba⁻¹ * geom * (μQ ^ (β - s) * μQ ^ (s - β)) := by
              ring
      _ = Cba⁻¹ * geom := by
              rw [hcancel]
              ring
  calc
    (besovToSouzaScaledCoeffPower G s β p hβ
        (inferInstance : Fact (1 ≤ p)) hp_top Q R k) ^ (1 / p.toReal)
        ≤ WeakGridSpace.LpGridRepresentation.levelMeasureWeight W (β - s) p p k *
            WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R := hroot
    _ ≤ (μQ ^ (β - s) * geom) * (Cba⁻¹ * μQ ^ (s - β)) := hmul_cost
    _ = Cba⁻¹ * geom := htarget

theorem besovAtom_to_induced_souzaS_representation_decay
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) {a : α → ℂ}
    (ha : IsBesovAtom G s β p qtilde hβ
      (inferInstance : Fact (1 ≤ p)) hp_top Q a) :
    ∃ haLp : MemLp a p G.grid.μ,
    ∃ R : WeakGridSpace.LpGridRepresentation
      (inducedSouzaAtomFamily G s p hs (inferInstance : Fact (1 ≤ p)) hp_top Q)
      haLp.toLp,
      ∀ k : ℕ,
        R.levelCoeffPower k ≤
          ((besovAtomConstant G β p qtilde)⁻¹ *
              (G.grid.lambda2 ^ k : ℝ) ^ (β - s)) ^ p.toReal := by
  classical
  rcases besovAtom_to_souza_representation_decay
      G s β p qtilde hβ hβs hp_top Q ha with
    ⟨haLp, Rβ, _hRβfin, _hRβcost, hdecay⟩
  let R := inducedSouzaBetaRepresentationToSouzaS G s β p hs hβ
    (inferInstance : Fact (1 ≤ p)) hp_top Q Rβ
  refine ⟨haLp, R, ?_⟩
  intro k
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hroot :
      (R.levelCoeffPower k) ^ (1 / p.toReal)
        ≤ (besovAtomConstant G β p qtilde)⁻¹ *
            (G.grid.lambda2 ^ k : ℝ) ^ (β - s) := by
    simpa [R, inducedSouzaBetaRepresentationToSouzaS_levelCoeffPower] using hdecay k
  have hleft :
      ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal =
        R.levelCoeffPower k := by
    have hmul : (1 / p.toReal) * p.toReal = 1 := by
      field_simp [hp_pos.ne']
    calc
      ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal =
          (R.levelCoeffPower k) ^ ((1 / p.toReal) * p.toReal) := by
          rw [← Real.rpow_mul (R.levelCoeffPower_nonneg k)]
      _ = R.levelCoeffPower k := by
          rw [hmul, Real.rpow_one]
  have hpow :=
    Real.rpow_le_rpow
      (Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _)
      hroot hp_pos.le
  rwa [hleft] at hpow

theorem besovAtom_to_induced_souzaS_representation_decay_claimC
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) {a : α → ℂ}
    (ha : IsBesovAtom G s β p qtilde hβ
      (inferInstance : Fact (1 ≤ p)) hp_top Q a) :
    ∃ haLp : MemLp a p G.grid.μ,
    ∃ R : WeakGridSpace.LpGridRepresentation
      (inducedSouzaAtomFamily G s p hs (inferInstance : Fact (1 ≤ p)) hp_top Q)
      haLp.toLp,
      ∀ k : ℕ,
        R.levelCoeffPower k ≤
          ((besovAtomConstant G β p qtilde)⁻¹) ^ p.toReal *
            ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) ^ k := by
  classical
  rcases besovAtom_to_induced_souzaS_representation_decay
      G s β p qtilde hs hβ hβs hp_top Q ha with
    ⟨haLp, R, hdecay⟩
  refine ⟨haLp, R, ?_⟩
  intro k
  let Cinv : ℝ := (besovAtomConstant G β p qtilde)⁻¹
  let lamRoot : ℝ := G.grid.lambda2 ^ (β - s)
  have hdelta_pos : 0 < β - s := sub_pos.mpr hβs
  have hlam_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  have hlam_nonneg : 0 ≤ G.grid.lambda2 := hlam_pos.le
  have hlamRoot_pos : 0 < lamRoot := Real.rpow_pos_of_pos hlam_pos (β - s)
  have hCinv_nonneg : 0 ≤ Cinv := by
    dsimp [Cinv]
    exact inv_nonneg.mpr (besovAtomConstant_nonneg G β p qtilde)
  have hgeom_eq :
      (G.grid.lambda2 ^ k : ℝ) ^ (β - s) = lamRoot ^ k := by
    calc
      (G.grid.lambda2 ^ k : ℝ) ^ (β - s) =
          G.grid.lambda2 ^ ((k : ℝ) * (β - s)) := by
            simpa [mul_comm] using
              (Real.rpow_natCast_mul hlam_nonneg k (β - s)).symm
      _ = G.grid.lambda2 ^ ((β - s) * k) := by ring_nf
      _ = lamRoot ^ k := by
            simpa [lamRoot, mul_comm] using
              Real.rpow_mul_natCast hlam_nonneg (β - s) k
  have hpow_geom :
      (lamRoot ^ k : ℝ) ^ p.toReal = (lamRoot ^ p.toReal) ^ k := by
    calc
      (lamRoot ^ k : ℝ) ^ p.toReal =
          lamRoot ^ ((k : ℝ) * p.toReal) := by
            simpa [mul_comm] using
              (Real.rpow_natCast_mul hlamRoot_pos.le k p.toReal).symm
      _ = lamRoot ^ (p.toReal * k) := by ring_nf
      _ = (lamRoot ^ p.toReal) ^ k := by
            simpa [mul_comm] using
              Real.rpow_mul_natCast hlamRoot_pos.le p.toReal k
  have htarget :
      ((besovAtomConstant G β p qtilde)⁻¹ *
          (G.grid.lambda2 ^ k : ℝ) ^ (β - s)) ^ p.toReal =
        Cinv ^ p.toReal * (lamRoot ^ p.toReal) ^ k := by
    calc
      ((besovAtomConstant G β p qtilde)⁻¹ *
          (G.grid.lambda2 ^ k : ℝ) ^ (β - s)) ^ p.toReal =
          (Cinv * lamRoot ^ k) ^ p.toReal := by
            simp [Cinv, hgeom_eq]
      _ = Cinv ^ p.toReal * (lamRoot ^ k : ℝ) ^ p.toReal := by
            rw [Real.mul_rpow hCinv_nonneg (pow_nonneg hlamRoot_pos.le k)]
      _ = Cinv ^ p.toReal * (lamRoot ^ p.toReal) ^ k := by
            rw [hpow_geom]
  calc
    R.levelCoeffPower k
        ≤ ((besovAtomConstant G β p qtilde)⁻¹ *
              (G.grid.lambda2 ^ k : ℝ) ^ (β - s)) ^ p.toReal := hdecay k
    _ = Cinv ^ p.toReal * (lamRoot ^ p.toReal) ^ k := htarget
    _ = ((besovAtomConstant G β p qtilde)⁻¹) ^ p.toReal *
            ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) ^ k := by
          simp [Cinv, lamRoot]

/-- The local space of concrete `L^p` representatives supported on a cell. -/
def besovAtomLocalSubmodule
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞) (Q : GoodGridCell G) :
    Submodule ℂ (α → ℂ) where
  carrier := { a | MemLp a p G.grid.μ ∧ ∀ x, x ∉ Q.cell → a x = 0 }
  zero_mem' := by
    constructor
    · exact MemLp.zero
    · intro x hx
      rfl
  add_mem' := by
    intro a b ha hb
    constructor
    · exact ha.1.add hb.1
    · intro x hx
      simp [ha.2 x hx, hb.2 x hx]
  smul_mem' := by
    intro c a ha
    constructor
    · exact ha.1.const_smul c
    · intro x hx
      simp [ha.2 x hx]

/-- Local vector space used for Besov atoms on a fixed good-grid cell. -/
def besovAtomLocalVectorSpace
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞) (Q : GoodGridCell G) :
    WeakGridSpace.LocalVectorSpace α where
  carrier := besovAtomLocalSubmodule G p Q
  toFun :=
    { toFun := fun a => a
      map_add' := by
        intro a b
        rfl
      map_smul' := by
        intro c a
        rfl }
  injective_toFun := by
    intro a b hab
    ext x
    exact congrFun hab x

/-- The zero representative is a Besov atom. -/
theorem zero_isBesovAtom
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞) [Fact (1 ≤ qtilde)]
    (Q : GoodGridCell G) :
    IsBesovAtom G s β p qtilde hβ hp hp_top Q 0 := by
  let A := inducedSouzaAtomFamily G β p hβ hp hp_top Q
  let R : WeakGridSpace.LpGridRepresentation A (0 : Lp ℂ p G.grid.μ) :=
    { block := fun k => WeakGridSpace.LevelBlock.zero A k
      hasSum := by
        have hterms :
            (fun k => (WeakGridSpace.LevelBlock.zero A k).toLp A) =
              fun _ : ℕ => (0 : Lp ℂ p G.grid.μ) := by
          funext k
          exact WeakGridSpace.LevelBlock.zero_toLp A k
        rw [hterms]
        exact (hasSum_zero : HasSum (fun _ : ℕ => (0 : Lp ℂ p G.grid.μ)) 0) }
  refine ⟨MemLp.zero, R, ?_, ?_⟩
  · have hp_pos : 0 < p.toReal :=
      (ENNReal.toReal_pos_iff_ne_top p).2 hp_top
    have hzero : ∀ k, R.levelCoeffPower k = 0 := by
      intro k
      unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
      simp [R, WeakGridSpace.LevelBlock.zero, Real.zero_rpow hp_pos.ne']
    by_cases hq : qtilde = ∞
    · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_pos hq]
      refine ⟨0, ?_⟩
      rintro x ⟨k, rfl⟩
      have hinv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
      simp [hzero k, Real.zero_rpow hinv_pos.ne']
    · have hq_pos : 0 < qtilde.toReal :=
        ENNReal.toReal_pos ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le
          (Fact.out : 1 ≤ qtilde)).ne' hq
      have hpow_pos : 0 < qtilde.toReal / p.toReal := div_pos hq_pos hp_pos
      rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hq]
      simp [hzero, Real.zero_rpow hpow_pos.ne']
  · have hp_pos : 0 < p.toReal :=
      (ENNReal.toReal_pos_iff_ne_top p).2 hp_top
    have hzero : ∀ k, R.levelCoeffPower k = 0 := by
      intro k
      unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
      simp [R, WeakGridSpace.LevelBlock.zero, Real.zero_rpow hp_pos.ne']
    have hcost_zero :
        WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R = 0 := by
      by_cases hq : qtilde = ∞
      · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos hq]
        have hinv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
        have hfun :
            (fun k => R.levelCoeffPower k ^ (1 / p.toReal)) = fun _ : ℕ => 0 := by
          funext k
          simpa [hzero k] using Real.zero_rpow hinv_pos.ne'
        rw [hfun]
        simp
      · have hq_pos : 0 < qtilde.toReal :=
          ENNReal.toReal_pos ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le
            (Fact.out : 1 ≤ qtilde)).ne' hq
        have hpow_pos : 0 < qtilde.toReal / p.toReal := div_pos hq_pos hp_pos
        rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hq]
        have hinv_pos : 0 < qtilde.toReal⁻¹ := inv_pos.mpr hq_pos
        simp [hzero, Real.zero_rpow hpow_pos.ne', Real.zero_rpow hinv_pos.ne']
    calc
      R.pqCost = 0 := hcost_zero
      _ ≤ (besovAtomConstant G β p qtilde)⁻¹ * (G.grid.μ Q.cell).toReal ^ (s - β) :=
        mul_nonneg (inv_nonneg.mpr (besovAtomConstant_nonneg G β p qtilde))
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-- Besov atoms are convex as a set of concrete representatives. -/
theorem convex_isBesovAtom
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    [Fact (1 ≤ qtilde)]
    (Q : GoodGridCell G) :
    Convex ℝ { a : (besovAtomLocalVectorSpace G p Q).carrier |
      IsBesovAtom G s β p qtilde hβ hp hp_top Q
        ((besovAtomLocalVectorSpace G p Q).toFun a) } := by
  classical
  let A := inducedSouzaAtomFamily G β p hβ hp hp_top Q
  rw [convex_iff_add_mem]
  intro a ha b hb r t hr ht hrt
  rcases ha with ⟨haLp, Ra, hRa_fin, hRa_cost⟩
  rcases hb with ⟨hbLp, Rb, hRb_fin, hRb_cost⟩
  have hmem :
      MemLp
        ((besovAtomLocalVectorSpace G p Q).toFun (r • a + t • b))
        p G.grid.μ := by
    simpa [map_add, map_smul] using
      (haLp.const_smul (r : ℂ)).add (hbLp.const_smul (t : ℂ))
  let Rr := WeakGridSpace.LpGridRepresentation.smul (A := A) (r : ℂ) Ra
  let Rt := WeakGridSpace.LpGridRepresentation.smul (A := A) (t : ℂ) Rb
  let Rsum₀ := WeakGridSpace.LpGridRepresentation.add (A := A) Rr Rt
  have htarget :
      (r : ℂ) • haLp.toLp + (t : ℂ) • hbLp.toLp = hmem.toLp := by
    rw [← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      simp [map_add]
  let Rsum : WeakGridSpace.LpGridRepresentation A hmem.toLp := htarget ▸ Rsum₀
  refine ⟨hmem, Rsum, ?_, ?_⟩
  · subst Rsum
    exact WeakGridSpace.LpGridRepresentation.add_finitePQCost
      (A := A) (q := qtilde) Rr Rt hp_top Fact.out
      (WeakGridSpace.LpGridRepresentation.smul_finitePQCost
        (A := A) (q := qtilde) (r : ℂ) hRa_fin)
      (WeakGridSpace.LpGridRepresentation.smul_finitePQCost
        (A := A) (q := qtilde) (t : ℂ) hRb_fin)
  · subst Rsum
    have hRr_fin :
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := qtilde) Rr :=
      WeakGridSpace.LpGridRepresentation.smul_finitePQCost
        (A := A) (q := qtilde) (r : ℂ) hRa_fin
    have hRt_fin :
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := qtilde) Rt :=
      WeakGridSpace.LpGridRepresentation.smul_finitePQCost
        (A := A) (q := qtilde) (t : ℂ) hRb_fin
    have htri :
        WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rsum₀ ≤
          WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rr +
            WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rt :=
      WeakGridSpace.LpGridRepresentation.pqCost_triangle
        (A := A) (q := qtilde) Rr Rt hp_top Fact.out hRr_fin hRt_fin
    have hRr_cost :
        WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rr =
          r * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Ra := by
      rw [WeakGridSpace.LpGridRepresentation.pqCost_smul
        (A := A) (q := qtilde) (r : ℂ) Ra hp_top Fact.out hRa_fin]
      simp [abs_of_nonneg hr]
    have hRt_cost :
        WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rt =
          t * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rb := by
      rw [WeakGridSpace.LpGridRepresentation.pqCost_smul
        (A := A) (q := qtilde) (t : ℂ) Rb hp_top Fact.out hRb_fin]
      simp [abs_of_nonneg ht]
    let C : ℝ :=
      (besovAtomConstant G β p qtilde)⁻¹ *
        (G.grid.μ Q.cell).toReal ^ (s - β)
    have hweighted :
        r * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Ra +
            t * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rb ≤
          r * C + t * C := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hRa_cost hr)
        (mul_le_mul_of_nonneg_left hRb_cost ht)
    have hconvex_scale : r * C + t * C = C := by
      calc
        r * C + t * C = (r + t) * C := by ring
        _ = C := by rw [hrt, one_mul]
    calc
      WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rsum₀
          ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rr +
              WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rt := htri
      _ = r * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Ra +
            t * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rb := by
            rw [hRr_cost, hRt_cost]
      _ ≤ (besovAtomConstant G β p qtilde)⁻¹ *
            (G.grid.μ Q.cell).toReal ^ (s - β) := by
            calc
              r * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Ra +
                  t * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rb
                  ≤ r * C + t * C := hweighted
              _ = C := hconvex_scale

/-- Besov atoms are invariant under complex scalars of modulus one. -/
theorem isBesovAtom_smul_of_norm_eq_one
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    [Fact (1 ≤ qtilde)]
    (Q : GoodGridCell G) {a : α → ℂ} (σ : ℂ)
    (ha : IsBesovAtom G s β p qtilde hβ hp hp_top Q a)
    (hσ : ‖σ‖ = (1 : ℝ)) :
    IsBesovAtom G s β p qtilde hβ hp hp_top Q (σ • a) := by
  classical
  let A := inducedSouzaAtomFamily G β p hβ hp hp_top Q
  rcases ha with ⟨haLp, R, hR_fin, hR_cost⟩
  have hmem : MemLp (σ • a) p G.grid.μ := haLp.const_smul σ
  let Rσ₀ := WeakGridSpace.LpGridRepresentation.smul (A := A) σ R
  have htarget : σ • haLp.toLp = hmem.toLp := by
    rw [← MemLp.toLp_const_smul]
  let Rσ : WeakGridSpace.LpGridRepresentation A hmem.toLp := htarget ▸ Rσ₀
  refine ⟨hmem, Rσ, ?_, ?_⟩
  · subst Rσ
    exact WeakGridSpace.LpGridRepresentation.smul_finitePQCost
      (A := A) (q := qtilde) σ hR_fin
  · subst Rσ
    calc
      WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rσ₀
          = ‖σ‖ * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R := by
            exact WeakGridSpace.LpGridRepresentation.pqCost_smul
              (A := A) (q := qtilde) σ R hp_top Fact.out hR_fin
      _ = WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R := by
            simp [hσ]
      _ ≤ (besovAtomConstant G β p qtilde)⁻¹ *
            (G.grid.μ Q.cell).toReal ^ (s - β) := hR_cost

/-- The defining Besov normalization gives the ordinary atom size bound. -/
theorem isBesovAtom_eLpNorm_le
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    [Fact (1 ≤ qtilde)]
    (Q : GoodGridCell G) {a : α → ℂ}
    (ha : IsBesovAtom G s β p qtilde hβ hp hp_top Q a) :
    eLpNorm a p G.grid.μ ≤ (G.grid.μ Q.cell) ^ s := by
  classical
  letI : Fact (1 ≤ p) := hp
  let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  let A := inducedSouzaAtomFamily G β p hβ hp hp_top Q
  rcases ha with ⟨haLp, R, hR_fin, hR_cost⟩
  have hp_ne_zero : p ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le hp.out)
  have hp_mul_top : p * ∞ = ∞ := ENNReal.mul_top hp_ne_zero
  have hs_emb : 0 ≤ β - 1 / p.toReal + 1 / p.toReal := by
    linarith [hβ.le]
  have hCfin :
      WeakGridSpace.LpGridRepresentation.cCoefficientFinite p qtilde
        (fun k =>
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight W β p p k) ^ p.toReal) :=
    induced_cCoefficientFinite G Q β p qtilde hβ hp hp_top
  have hEmb :
      (eLpNorm (haLp.toLp : α → ℂ) p W.measure).toReal ≤
        ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
            (fun k =>
              (WeakGridSpace.LpGridRepresentation.levelMeasureWeight W β p p k) ^ p.toReal) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R := by
    simpa [W, A, hp_mul_top] using
      WeakGridSpace.LpGridRepresentation.lp_embedding_adapted_statement
        (G := W) (s := β) (p := p) (u := ∞) (q := qtilde)
        (A := A) (t := p)
        hp_top hp_top Fact.out le_rfl (by rw [hp_mul_top]; exact le_top)
        hs_emb R hR_fin hCfin
  let Cemb : ℝ := ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal))
  let Cind : ℝ :=
    WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
      (fun k =>
        (WeakGridSpace.LpGridRepresentation.levelMeasureWeight W β p p k) ^ p.toReal)
  let Cgeom : ℝ :=
    WeakGridSpace.LpGridRepresentation.cCoefficient p qtilde
      (besovAtomGeometricWeight G β p)
  let Mβ : ℝ := (G.grid.μ Q.cell).toReal ^ β
  let Msβ : ℝ := (G.grid.μ Q.cell).toReal ^ (s - β)
  let Cba : ℝ := besovAtomConstant G β p qtilde
  have hCemb_nonneg : 0 ≤ Cemb := by
    dsimp [Cemb]
    positivity
  have hCind_nonneg : 0 ≤ Cind := by
    dsimp [Cind]
    exact WeakGridSpace.LpGridRepresentation.cCoefficient_nonneg p qtilde
      (fun k =>
        (WeakGridSpace.LpGridRepresentation.levelMeasureWeight W β p p k) ^ p.toReal)
      (fun k => Real.rpow_nonneg
        (WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg W β p p k) _)
  have hCba_nonneg : 0 ≤ Cba := by
    dsimp [Cba]
    exact besovAtomConstant_nonneg G β p qtilde
  have hMβ_nonneg : 0 ≤ Mβ := by
    dsimp [Mβ]
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hMsβ_nonneg : 0 ≤ Msβ := by
    dsimp [Msβ]
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hcost_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R :=
    WeakGridSpace.LpGridRepresentation.pqCost_nonneg R
  have hCind_le : Cind ≤ Mβ * Cgeom := by
    simpa [Cind, Cgeom, Mβ, W] using
      induced_cCoefficient_le_geometric G Q β p qtilde hβ hp hp_top
  have hCemb_one : Cemb = 1 := by
    dsimp [Cemb, W, WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid,
      GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid]
    norm_num
  have hCba_eq_Cgeom : Cba = Cgeom := by
    dsimp [Cba, Cgeom, besovAtomConstant, GoodGridSpace.toWeakGridSpace,
      GoodGridSpace.toWeakGrid]
    norm_num
  have hconst_le : Cemb * Cind ≤ Mβ * Cba := by
    calc
      Cemb * Cind ≤ Cemb * (Mβ * Cgeom) :=
        mul_le_mul_of_nonneg_left hCind_le hCemb_nonneg
      _ = Mβ * Cba := by
        rw [hCemb_one, hCba_eq_Cgeom]
        ring
  have hnorm_real :
      (eLpNorm a p G.grid.μ).toReal ≤ (G.grid.μ Q.cell).toReal ^ s := by
    have htoLp :
        (eLpNorm a p G.grid.μ).toReal =
          (eLpNorm (haLp.toLp : α → ℂ) p W.measure).toReal := by
      simpa [W, WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.WeakGridSpace.measure,
        WeakGridSpace.inducedWeakGrid, GoodGridSpace.toWeakGridSpace,
        GoodGridSpace.toWeakGrid] using
        congrArg ENNReal.toReal
          (MeasureTheory.eLpNorm_congr_ae (MemLp.coeFn_toLp haLp).symm)
    have hprod_bound :
        Cemb * Cind * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R
          ≤ Mβ * Cba * (Cba⁻¹ * Msβ) := by
      calc
        Cemb * Cind * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R
            ≤ Mβ * Cba * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R := by
              exact mul_le_mul_of_nonneg_right hconst_le hcost_nonneg
        _ ≤ Mβ * Cba * (Cba⁻¹ * Msβ) := by
              refine mul_le_mul_of_nonneg_left hR_cost ?_
              exact mul_nonneg hMβ_nonneg hCba_nonneg
    have hcancel_le : Cba * Cba⁻¹ ≤ 1 := by
      by_cases hCba_zero : Cba = 0
      · simp [hCba_zero]
      · rw [mul_inv_cancel₀ hCba_zero]
    have hscale_bound : Mβ * Cba * (Cba⁻¹ * Msβ) ≤ Mβ * Msβ := by
      calc
        Mβ * Cba * (Cba⁻¹ * Msβ) = Mβ * (Cba * Cba⁻¹) * Msβ := by ring
        _ ≤ Mβ * 1 * Msβ := by
              gcongr
        _ = Mβ * Msβ := by ring
    have hQpos : 0 < G.grid.μ Q.cell :=
      G.grid.positive_measure Q.level Q.cell Q.mem
    have hQfinite : G.grid.μ Q.cell ≠ ∞ := by
      letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Q.cell
    have hQtoReal_pos : 0 < (G.grid.μ Q.cell).toReal :=
      ENNReal.toReal_pos hQpos.ne' hQfinite
    have hpow : Mβ * Msβ = (G.grid.μ Q.cell).toReal ^ s := by
      calc
        Mβ * Msβ =
            (G.grid.μ Q.cell).toReal ^ β *
              (G.grid.μ Q.cell).toReal ^ (s - β) := by rfl
        _ = (G.grid.μ Q.cell).toReal ^ (β + (s - β)) := by
              rw [← Real.rpow_add hQtoReal_pos]
        _ = (G.grid.μ Q.cell).toReal ^ s := by ring_nf
    calc
      (eLpNorm a p G.grid.μ).toReal
          = (eLpNorm (haLp.toLp : α → ℂ) p W.measure).toReal := htoLp
      _ ≤ Cemb * Cind * WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R := by
            simpa [Cemb, Cind] using hEmb
      _ ≤ Mβ * Cba * (Cba⁻¹ * Msβ) := hprod_bound
      _ ≤ Mβ * Msβ := hscale_bound
      _ = (G.grid.μ Q.cell).toReal ^ s := hpow
  have hQpos : 0 < G.grid.μ Q.cell :=
    G.grid.positive_measure Q.level Q.cell Q.mem
  have hQfinite : G.grid.μ Q.cell ≠ ∞ := by
    letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ Q.cell
  have hQtoReal_pos : 0 < (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_pos hQpos.ne' hQfinite
  have hscale :
      ENNReal.ofReal ((G.grid.μ Q.cell).toReal ^ s) =
        (G.grid.μ Q.cell) ^ s := by
    rw [← ENNReal.ofReal_rpow_of_pos hQtoReal_pos, ENNReal.ofReal_toReal hQfinite]
  rw [← hscale]
  exact (ENNReal.le_ofReal_iff_toReal_le haLp.eLpNorm_ne_top
    (Real.rpow_nonneg hQtoReal_pos.le _)).2 hnorm_real

/--
The family of Besov atoms as an `AtomFamily`.

This is the formal package corresponding to
`A^{bs}_{s,β,p,qtilde}`.  The local carrier is intentionally packaged as an
`AtomFamily` so it can be passed directly to the existing Besov-ish and
transmutation theorems.
-/
noncomputable def besovAtomFamily
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    [Fact (1 ≤ qtilde)] :
    WeakGridSpace.AtomFamily.{u, u} G.toWeakGridSpace s p 1 := by
  classical
  refine
    { uConj := ∞
      s_pos := hs
      one_le_p := hp.out
      p_ne_top := hp_top
      one_le_u := by simp
      holder_conjugate := by
        rw [ENNReal.holderConjugate_iff]
        simp
      localSpace := fun Q =>
        besovAtomLocalVectorSpace G p ⟨Q.level, Q.cell, Q.mem⟩
      atoms := fun Q =>
        { a | IsBesovAtom G s β p qtilde hβ hp hp_top ⟨Q.level, Q.cell, Q.mem⟩
            ((besovAtomLocalVectorSpace G p ⟨Q.level, Q.cell, Q.mem⟩).toFun a) }
      atoms_nonempty := ?_
      local_memLp := ?_
      local_support := ?_
      atoms_convex := ?_
      atoms_phase_invariant := ?_
      atom_bound := ?_ }
  · intro Q
    refine ⟨0, ?_⟩
    simpa [besovAtomLocalVectorSpace] using
      zero_isBesovAtom G s β p qtilde hβ hp hp_top ⟨Q.level, Q.cell, Q.mem⟩
  · intro Q a
    rw [mul_one]
    exact a.2.1
  · intro Q a x hx
    exact a.2.2 x hx
  · intro Q
    simpa using
      convex_isBesovAtom G s β p qtilde hβ hp hp_top ⟨Q.level, Q.cell, Q.mem⟩
  · intro Q a σ ha hσ
    exact isBesovAtom_smul_of_norm_eq_one G s β p qtilde hβ hp hp_top
      ⟨Q.level, Q.cell, Q.mem⟩ σ ha hσ
  · intro Q a ha
    rw [mul_one]
    calc
      eLpNorm
          ((besovAtomLocalVectorSpace G p ⟨Q.level, Q.cell, Q.mem⟩).toFun a)
          p G.toWeakGridSpace.measure
          ≤ (G.grid.μ Q.cell) ^ s := by
            exact isBesovAtom_eLpNorm_le G s β p qtilde hβ hp hp_top
              ⟨Q.level, Q.cell, Q.mem⟩ ha
      _ = WeakGridSpace.atomMeasureScale G.toWeakGridSpace s p ∞ Q := by
            simp [WeakGridSpace.atomMeasureScale, WeakGridSpace.atomMeasureExponent,
              GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
              WeakGridSpace.WeakGridSpace.measure]

/--
Besov atoms are ordinary `(s,p,1)` atoms.

This is the formal version of the estimate
`|a|_p ≤ |Q|^s`, obtained from the induced `L^p` embedding and the defining
Besov-atom normalization.
-/
theorem besovAtom_is_sp_one_atom
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (_hβs : s < β)
    (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞) [Fact (1 ≤ qtilde)]
    (Q : GoodGridCell G) :
    ∀ φ,
      (besovAtomFamily G s β p qtilde hs hβ hp hp_top).IsAtom Q.toWeakGridCell φ →
      eLpNorm
          ((besovAtomFamily G s β p qtilde hs hβ hp hp_top).toFunction
            Q.toWeakGridCell φ)
          p G.grid.μ ≤ (G.grid.μ Q.cell) ^ s := by
  intro φ hφ
  simpa [besovAtomFamily, WeakGridSpace.AtomFamily.IsAtom,
    WeakGridSpace.AtomFamily.toFunction] using
    isBesovAtom_eLpNorm_le G s β p qtilde hβ hp hp_top Q hφ

/--
Hypothesis saying that an atom family lies between Souza atoms and Besov atoms,
up to fixed constants.

This is the Lean analogue of
`C1⁻¹ A_sz(Q) ⊆ A(Q) ⊆ C2 A_bs(Q)`, with positive constants.
-/
def SouzaBesovSandwich
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p u qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    [Fact (1 ≤ qtilde)]
    (A : WeakGridSpace.AtomFamily G.toWeakGridSpace s p u)
    (C1 C2 : ℝ) : Prop :=
  0 < C1 ∧ 0 < C2 ∧
  (∀ Q φ,
      (souzaAtomFamily G s p hs hp.out hp_top).IsAtom Q φ →
        ∃ ψ, A.IsAtom Q ψ ∧
          A.toFunction Q ψ =
            (C1⁻¹ : ℂ) •
              (souzaAtomFamily G s p hs hp.out hp_top).toFunction Q φ) ∧
  (∀ Q φ,
      A.IsAtom Q φ →
        ∃ ψ : ((besovAtomFamily G s β p qtilde hs hβ hp hp_top).localSpace Q).carrier,
          (besovAtomFamily G s β p qtilde hs hβ hp hp_top).IsAtom Q ψ ∧
            A.toFunction Q φ =
              (C2 : ℂ) •
                (besovAtomFamily G s β p qtilde hs hβ hp hp_top).toFunction Q ψ)

private noncomputable def scaledAtomInclusionBlock
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u₁ u₂ : ℝ≥0∞}
    [Fact (1 ≤ p)]
    (A₁ : WeakGridSpace.AtomFamily G s p u₁)
    (A₂ : WeakGridSpace.AtomFamily G s p u₂)
    (C : ℝ)
    (hA₁A₂ : ∀ Q φ, A₁.IsAtom Q φ →
      ∃ ψ, A₂.IsAtom Q ψ ∧
        A₁.toFunction Q φ = (C : ℂ) • A₂.toFunction Q ψ)
    {k : ℕ} (B : WeakGridSpace.LevelBlock A₁ k) :
    WeakGridSpace.LevelBlock A₂ k where
  coeff := fun Q => (C : ℂ) * B.coeff Q
  atom := fun Q =>
    Classical.choose (hA₁A₂ (WeakGridSpace.levelCellToWeakGridCell G k Q)
      (B.atom Q) (B.atom_mem Q))
  atom_mem := fun Q =>
    (Classical.choose_spec (hA₁A₂ (WeakGridSpace.levelCellToWeakGridCell G k Q)
      (B.atom Q) (B.atom_mem Q))).1

private theorem scaledAtomInclusionBlock_toLp
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u₁ u₂ : ℝ≥0∞}
    [Fact (1 ≤ p)]
    (A₁ : WeakGridSpace.AtomFamily G s p u₁)
    (A₂ : WeakGridSpace.AtomFamily G s p u₂)
    (C : ℝ)
    (hA₁A₂ : ∀ Q φ, A₁.IsAtom Q φ →
      ∃ ψ, A₂.IsAtom Q ψ ∧
        A₁.toFunction Q φ = (C : ℂ) • A₂.toFunction Q ψ)
    {k : ℕ} (B : WeakGridSpace.LevelBlock A₁ k) :
    (scaledAtomInclusionBlock A₁ A₂ C hA₁A₂ B).toLp A₂ = B.toLp A₁ := by
  classical
  unfold WeakGridSpace.LevelBlock.toLp
  refine Finset.sum_congr rfl ?_
  intro Q _hQ
  unfold WeakGridSpace.LevelBlock.term scaledAtomInclusionBlock
  let Qw := WeakGridSpace.levelCellToWeakGridCell G k Q
  let ψ := Classical.choose (hA₁A₂ Qw (B.atom Q) (B.atom_mem Q))
  have hψ :=
    Classical.choose_spec (hA₁A₂ Qw (B.atom Q) (B.atom_mem Q))
  have htoLp :
      MeasureTheory.MemLp.toLp (A₁.toFunction Qw (B.atom Q)) (A₁.local_memLp_p Qw (B.atom Q)) =
        (C : ℂ) •
          MeasureTheory.MemLp.toLp (A₂.toFunction Qw ψ) (A₂.local_memLp_p Qw ψ) := by
    rw [← MeasureTheory.MemLp.toLp_const_smul]
    exact MeasureTheory.MemLp.toLp_congr _ _
      (Filter.Eventually.of_forall fun x => congrFun hψ.2 x)
  calc
    ((C : ℂ) * B.coeff Q) •
        MeasureTheory.MemLp.toLp (A₂.toFunction Qw ψ) (A₂.local_memLp_p Qw ψ)
        = B.coeff Q •
            ((C : ℂ) •
              MeasureTheory.MemLp.toLp (A₂.toFunction Qw ψ) (A₂.local_memLp_p Qw ψ)) := by
            rw [smul_smul]
            ring_nf
    _ = B.coeff Q •
        MeasureTheory.MemLp.toLp (A₁.toFunction Qw (B.atom Q)) (A₁.local_memLp_p Qw (B.atom Q)) := by
          rw [htoLp]

private noncomputable def scaledAtomInclusionRepresentation
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u₁ u₂ : ℝ≥0∞}
    [Fact (1 ≤ p)]
    (A₁ : WeakGridSpace.AtomFamily G s p u₁)
    (A₂ : WeakGridSpace.AtomFamily G s p u₂)
    (C : ℝ)
    (hA₁A₂ : ∀ Q φ, A₁.IsAtom Q φ →
      ∃ ψ, A₂.IsAtom Q ψ ∧
        A₁.toFunction Q φ = (C : ℂ) • A₂.toFunction Q ψ)
    {g : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A₁ g) :
    WeakGridSpace.LpGridRepresentation A₂ g where
  block k := scaledAtomInclusionBlock A₁ A₂ C hA₁A₂ (R.block k)
  hasSum := by
    refine HasSum.congr_fun R.hasSum ?_
    intro k
    exact scaledAtomInclusionBlock_toLp A₁ A₂ C hA₁A₂ (R.block k)

private theorem scaledAtomInclusionRepresentation_levelCoeffPower
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u₁ u₂ : ℝ≥0∞}
    [Fact (1 ≤ p)]
    (A₁ : WeakGridSpace.AtomFamily G s p u₁)
    (A₂ : WeakGridSpace.AtomFamily G s p u₂)
    (C : ℝ)
    (hA₁A₂ : ∀ Q φ, A₁.IsAtom Q φ →
      ∃ ψ, A₂.IsAtom Q ψ ∧
        A₁.toFunction Q φ = (C : ℂ) • A₂.toFunction Q ψ)
    {g : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A₁ g) (k : ℕ) :
    (scaledAtomInclusionRepresentation A₁ A₂ C hA₁A₂ R).levelCoeffPower k =
      ((WeakGridSpace.LpGridRepresentation.smul (A := A₁) (C : ℂ) R).levelCoeffPower k) := by
  unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
  rfl

private theorem scaledAtomInclusionRepresentation_finitePQCost
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u₁ u₂ q : ℝ≥0∞}
    [Fact (1 ≤ p)]
    (A₁ : WeakGridSpace.AtomFamily G s p u₁)
    (A₂ : WeakGridSpace.AtomFamily G s p u₂)
    (C : ℝ)
    (hA₁A₂ : ∀ Q φ, A₁.IsAtom Q φ →
      ∃ ψ, A₂.IsAtom Q ψ ∧
        A₁.toFunction Q φ = (C : ℂ) • A₂.toFunction Q ψ)
    {g : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A₁ g)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R) :
    WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
      (scaledAtomInclusionRepresentation A₁ A₂ C hA₁A₂ R) := by
  have hfin :=
    WeakGridSpace.LpGridRepresentation.smul_finitePQCost
      (A := A₁) (q := q) (C : ℂ) hRfin
  simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost,
    scaledAtomInclusionRepresentation_levelCoeffPower (A₁ := A₁) (A₂ := A₂)
      (C := C) (hA₁A₂ := hA₁A₂) (R := R)] using hfin

private theorem scaledAtomInclusionRepresentation_pqCost
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u₁ u₂ q : ℝ≥0∞}
    [Fact (1 ≤ p)]
    (A₁ : WeakGridSpace.AtomFamily G s p u₁)
    (A₂ : WeakGridSpace.AtomFamily G s p u₂)
    (C : ℝ)
    (hA₁A₂ : ∀ Q φ, A₁.IsAtom Q φ →
      ∃ ψ, A₂.IsAtom Q ψ ∧
        A₁.toFunction Q φ = (C : ℂ) • A₂.toFunction Q ψ)
    {g : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A₁ g) :
    WeakGridSpace.LpGridRepresentation.pqCost (q := q)
        (scaledAtomInclusionRepresentation A₁ A₂ C hA₁A₂ R) =
      WeakGridSpace.LpGridRepresentation.pqCost (q := q)
        (WeakGridSpace.LpGridRepresentation.smul (A := A₁) (C : ℂ) R) := by
  unfold WeakGridSpace.LpGridRepresentation.pqCost
  simp [scaledAtomInclusionRepresentation_levelCoeffPower
    (A₁ := A₁) (A₂ := A₂) (C := C) (hA₁A₂ := hA₁A₂) (R := R)]

private theorem lpGridRepresentation_smul_levelCoeffPower
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u : ℝ≥0∞}
    [Fact (1 ≤ p)] {A : WeakGridSpace.AtomFamily G s p u}
    {g : Lp ℂ p G.measure} (c : ℂ)
    (R : WeakGridSpace.LpGridRepresentation A g) (k : ℕ) :
    (WeakGridSpace.LpGridRepresentation.smul (A := A) c R).levelCoeffPower k =
      ‖c‖ ^ p.toReal * R.levelCoeffPower k := by
  unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
  unfold WeakGridSpace.LpGridRepresentation.smul WeakGridSpace.LevelBlock.smul
  calc
    (∑ Q : WeakGridSpace.LevelCell G k, ‖c * (R.block k).coeff Q‖ ^ p.toReal)
        = ∑ Q : WeakGridSpace.LevelCell G k,
            (‖c‖ * ‖(R.block k).coeff Q‖) ^ p.toReal := by
          refine Finset.sum_congr rfl ?_
          intro Q _hQ
          rw [norm_mul]
    _ = ∑ Q : WeakGridSpace.LevelCell G k,
          ‖c‖ ^ p.toReal * ‖(R.block k).coeff Q‖ ^ p.toReal := by
          refine Finset.sum_congr rfl ?_
          intro Q _hQ
          rw [Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
    _ = ‖c‖ ^ p.toReal *
          ∑ Q : WeakGridSpace.LevelCell G k, ‖(R.block k).coeff Q‖ ^ p.toReal := by
          rw [Finset.mul_sum]

private theorem finitePQCost_of_levelCoeffPower_geometric_decay
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {A : WeakGridSpace.AtomFamily G s p u}
    {g : Lp ℂ p G.measure} (R : WeakGridSpace.LpGridRepresentation A g)
    (C lam : ℝ) (hC_nonneg : 0 ≤ C) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (hdecay : ∀ k : ℕ, R.levelCoeffPower k ≤ C * lam ^ k) :
    WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R := by
  classical
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le A.one_le_p).ne' A.p_ne_top
  have hgeom_nonneg : ∀ k : ℕ, 0 ≤ C * lam ^ k :=
    fun k => mul_nonneg hC_nonneg (pow_nonneg hlam_pos.le k)
  have hroot_bound :
      ∀ k : ℕ, (R.levelCoeffPower k) ^ (1 / p.toReal) ≤ C ^ (1 / p.toReal) := by
    intro k
    have hpow_le_one : lam ^ k ≤ (1 : ℝ) := pow_le_one₀ hlam_pos.le hlam_lt.le
    have hCgeom_le_C : C * lam ^ k ≤ C := by
      calc
        C * lam ^ k ≤ C * 1 := mul_le_mul_of_nonneg_left hpow_le_one hC_nonneg
        _ = C := by ring
    calc
      (R.levelCoeffPower k) ^ (1 / p.toReal)
          ≤ (C * lam ^ k) ^ (1 / p.toReal) :=
            Real.rpow_le_rpow (R.levelCoeffPower_nonneg k) (hdecay k)
              (div_nonneg zero_le_one hp_pos.le)
      _ ≤ C ^ (1 / p.toReal) :=
            Real.rpow_le_rpow (hgeom_nonneg k) hCgeom_le_C
              (div_nonneg zero_le_one hp_pos.le)
  by_cases hqtop : q = ∞
  · have hbdd :
        BddAbove (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
      refine ⟨C ^ (1 / p.toReal), ?_⟩
      rintro x ⟨k, rfl⟩
      exact hroot_bound k
    simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hbdd
  · have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hqtop
    let r : ℝ := q.toReal / p.toReal
    have hr_pos : 0 < r := div_pos hq_pos hp_pos
    have hratio_nonneg : 0 ≤ lam ^ r := Real.rpow_nonneg hlam_pos.le _
    have hratio_lt_one : lam ^ r < 1 := Real.rpow_lt_one hlam_pos.le hlam_lt hr_pos
    have hgeom_sum : Summable (fun k : ℕ => C ^ r * (lam ^ r) ^ k) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (summable_geometric_of_lt_one hratio_nonneg hratio_lt_one).mul_left (C ^ r)
    have hpow_geom : ∀ k : ℕ, (lam ^ k : ℝ) ^ r = (lam ^ r) ^ k := by
      intro k
      calc
        (lam ^ k : ℝ) ^ r = lam ^ ((k : ℝ) * r) := by
          simpa [mul_comm] using (Real.rpow_natCast_mul hlam_pos.le k r).symm
        _ = lam ^ (r * k) := by ring_nf
        _ = (lam ^ r) ^ k := by
          simpa [mul_comm] using Real.rpow_mul_natCast hlam_pos.le r k
    have hterm_le :
        (fun k : ℕ => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ≤
          fun k : ℕ => C ^ r * (lam ^ r) ^ k := by
      intro k
      dsimp [r]
      calc
        (R.levelCoeffPower k) ^ (q.toReal / p.toReal)
            ≤ (C * lam ^ k) ^ (q.toReal / p.toReal) :=
              Real.rpow_le_rpow (R.levelCoeffPower_nonneg k) (hdecay k) hr_pos.le
        _ = C ^ r * (lam ^ k : ℝ) ^ r := by
              rw [Real.mul_rpow hC_nonneg (pow_nonneg hlam_pos.le k)]
        _ = C ^ r * (lam ^ r) ^ k := by rw [hpow_geom k]
    have hterm_nonneg :
        ∀ k : ℕ, 0 ≤ (R.levelCoeffPower k) ^ (q.toReal / p.toReal) :=
      fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
    simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using
      Summable.of_nonneg_of_le hterm_nonneg hterm_le hgeom_sum

private theorem scaledAtomInclusionEmbedding
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u₁ u₂ q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A₁ : WeakGridSpace.AtomFamily G s p u₁)
    (A₂ : WeakGridSpace.AtomFamily G s p u₂)
    (C : ℝ) (hC_nonneg : 0 ≤ C)
    (hA₁A₂ : ∀ Q φ, A₁.IsAtom Q φ →
      ∃ ψ, A₂.IsAtom Q ψ ∧
        A₁.toFunction Q φ = (C : ℂ) • A₂.toFunction Q ψ) :
    ∀ f : WeakGridSpace.BesovishSpace A₁ q,
      ∃ hf₂ : WeakGridSpace.MemBesovishCoeffCost A₂ q
          (f : Lp ℂ p G.measure),
        WeakGridSpace.BesovishSpace.Norm_Costpq A₂ q
            (⟨(f : Lp ℂ p G.measure), hf₂⟩ :
              WeakGridSpace.BesovishSpace A₂ q) ≤
          C * WeakGridSpace.BesovishSpace.Norm_Costpq A₁ q f := by
  classical
  intro f
  have hfinite₁ :
      WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations (A := A₁) q :=
    WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A₁ q
  have hnormC : ‖(C : ℂ)‖ = C := by
    rw [Complex.norm_real, Real.norm_of_nonneg hC_nonneg]
  refine ⟨?_, ?_⟩
  · rcases f.property with ⟨R, hRfin⟩
    exact ⟨scaledAtomInclusionRepresentation A₁ A₂ C hA₁A₂ R,
      scaledAtomInclusionRepresentation_finitePQCost A₁ A₂ C hA₁A₂ R hRfin⟩
  · let hf₂ : WeakGridSpace.MemBesovishCoeffCost A₂ q
        (f : Lp ℂ p G.measure) := by
        rcases f.property with ⟨R, hRfin⟩
        exact ⟨scaledAtomInclusionRepresentation A₁ A₂ C hA₁A₂ R,
          scaledAtomInclusionRepresentation_finitePQCost A₁ A₂ C hA₁A₂ R hRfin⟩
    change
      WeakGridSpace.BesovishSpace.Norm_Costpq A₂ q
          (⟨(f : Lp ℂ p G.measure), hf₂⟩ :
            WeakGridSpace.BesovishSpace A₂ q) ≤
        C * WeakGridSpace.BesovishSpace.Norm_Costpq A₁ q f
    refine le_iff_forall_pos_le_add.mpr ?_
    intro ε hε
    have hden : 0 < C + 1 := by linarith
    have hδ : 0 < ε / (C + 1) := by positivity
    rcases WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add
        (A := A₁) (q := q) hfinite₁ f hδ with
      ⟨R, hRfin, hRlt⟩
    let R₂ := scaledAtomInclusionRepresentation A₁ A₂ C hA₁A₂ R
    have hR₂fin :
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R₂ :=
      scaledAtomInclusionRepresentation_finitePQCost A₁ A₂ C hA₁A₂ R hRfin
    let f₂ : WeakGridSpace.BesovishSpace A₂ q :=
      ⟨(f : Lp ℂ p G.measure), ⟨R₂, hR₂fin⟩⟩
    have hf_eq :
        (⟨(f : Lp ℂ p G.measure), hf₂⟩ :
          WeakGridSpace.BesovishSpace A₂ q) = f₂ := by
      ext
      rfl
    have hnorm_le :
        WeakGridSpace.BesovishSpace.Norm_Costpq A₂ q
            (⟨(f : Lp ℂ p G.measure), hf₂⟩ :
              WeakGridSpace.BesovishSpace A₂ q)
          ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) R₂ := by
      simpa [hf_eq, f₂] using
        WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
          (A := A₂) (q := q) (g := f₂) R₂ hR₂fin
    have hcost :
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R₂ =
          C * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
      calc
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R₂ =
            WeakGridSpace.LpGridRepresentation.pqCost (q := q)
              (WeakGridSpace.LpGridRepresentation.smul (A := A₁) (C : ℂ) R) :=
          scaledAtomInclusionRepresentation_pqCost A₁ A₂ C hA₁A₂ R
        _ = ‖(C : ℂ)‖ *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
          WeakGridSpace.LpGridRepresentation.pqCost_smul
            (A := A₁) (q := q) (C : ℂ) R A₁.p_ne_top Fact.out hRfin
        _ = C * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
          rw [hnormC]
    have hcost_le :
        C * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R
          ≤ C * (WeakGridSpace.BesovishSpace.Norm_Costpq A₁ q f + ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hRlt) hC_nonneg
    have hsmall : C * (ε / (C + 1)) ≤ ε := by
      have hfrac : C / (C + 1) ≤ (1 : ℝ) :=
        (div_le_one hden).2 (by linarith)
      have hε_nonneg : 0 ≤ ε := le_of_lt hε
      have hmul := mul_le_mul_of_nonneg_right hfrac hε_nonneg
      calc
        C * (ε / (C + 1)) = (C / (C + 1)) * ε := by ring
        _ ≤ 1 * ε := hmul
        _ = ε := by ring
    calc
      WeakGridSpace.BesovishSpace.Norm_Costpq A₂ q
          (⟨(f : Lp ℂ p G.measure), hf₂⟩ :
            WeakGridSpace.BesovishSpace A₂ q)
        ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) R₂ := hnorm_le
      _ = C * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := hcost
      _ ≤ C * (WeakGridSpace.BesovishSpace.Norm_Costpq A₁ q f + ε / (C + 1)) :=
        hcost_le
      _ = C * WeakGridSpace.BesovishSpace.Norm_Costpq A₁ q f + C * (ε / (C + 1)) := by
        ring
      _ ≤ C * WeakGridSpace.BesovishSpace.Norm_Costpq A₁ q f + ε := by
        exact add_le_add le_rfl hsmall

private theorem cast_levelBlock_coeff
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u : ℝ≥0∞}
    {m n : ℕ} [Fact (1 ≤ p)]
    (A : WeakGridSpace.AtomFamily G s p u) (h : m = n)
    (B : WeakGridSpace.LevelBlock A m) (P : WeakGridSpace.LevelCell G n) :
    (cast (congrArg (WeakGridSpace.LevelBlock A) h) B).coeff P =
      B.coeff (cast (congrArg (WeakGridSpace.LevelCell G) h.symm) P) := by
  subst h
  rfl

private theorem cast_levelCell_coe
    {G : WeakGridSpace.WeakGridSpace (α := α)} {m n : ℕ}
    (h : m = n) (P : WeakGridSpace.LevelCell G m) :
    (cast (congrArg (WeakGridSpace.LevelCell G) h) P).1 = P.1 := by
  subst h
  rfl

/--
Besov-atom comparison theorem.

If a family `A` sits between Souza atoms and Besov atoms, then the three
Besov-ish spaces built from Souza atoms, `A`, and Besov atoms coincide as
subspaces of the ambient `L^p`.  The quantitative bounds are the two estimates
from the paper: the first follows from the lower inclusion, while the second
comes from transmuting each Besov atom into Souza atoms with geometric decay
`lambda2^(β-s)`.
-/
theorem atoms_between_souza_atoms_and_besov_atoms
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p u q qtilde : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ u)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β) (hp_top : p ≠ ∞)
    (A : WeakGridSpace.AtomFamily G.toWeakGridSpace s p u)
    (C1 C2 : ℝ)
    (hSandwich :
      SouzaBesovSandwich G s β p u qtilde hs hβ (inferInstance : Fact (1 ≤ p))
        hp_top A C1 C2) :
    (WeakGridSpace.BesovishSpace (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q =
        WeakGridSpace.BesovishSpace A q) ∧
      (WeakGridSpace.BesovishSpace A q =
        WeakGridSpace.BesovishSpace
          (besovAtomFamily G s β p qtilde hs hβ inferInstance hp_top) q) ∧
      (∀ f : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q,
        ∃ hfA : WeakGridSpace.MemBesovishCoeffCost A q
            (f : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.BesovishSpace.Norm_Costpq A q
              (⟨(f : Lp ℂ p G.toWeakGridSpace.measure), hfA⟩ :
                WeakGridSpace.BesovishSpace A q)
            ≤ C1 *
              WeakGridSpace.BesovishSpace.Norm_Costpq
                (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q f) ∧
      (∀ f : WeakGridSpace.BesovishSpace A q,
        ∃ hfS : WeakGridSpace.MemBesovishCoeffCost
            (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q
            (f : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q
              (⟨(f : Lp ℂ p G.toWeakGridSpace.measure), hfS⟩ :
                WeakGridSpace.BesovishSpace
                  (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q)
            ≤ (C2 / (1 - G.grid.lambda2 ^ (β - s))) *
              WeakGridSpace.BesovishSpace.Norm_Costpq A q f) := by
  classical
  rcases hSandwich with ⟨hC1_pos, hC2_pos, hSouza_to_A_raw, hA_to_Besov_raw⟩
  let AS := souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top
  let AB := besovAtomFamily G s β p qtilde hs hβ (inferInstance : Fact (1 ≤ p)) hp_top
  have hSouza_to_A_atoms :
      ∀ Q φ, AS.IsAtom Q φ →
        ∃ ψ, A.IsAtom Q ψ ∧
          AS.toFunction Q φ = (C1 : ℂ) • A.toFunction Q ψ := by
    intro Q φ hφ
    rcases hSouza_to_A_raw Q φ hφ with ⟨ψ, hψ_atom, hψ_eq⟩
    refine ⟨ψ, hψ_atom, ?_⟩
    have hC1_ne : (C1 : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hC1_pos
    rw [hψ_eq]
    ext x
    simp [AS, Pi.smul_apply, hC1_ne]
  have hSouza_to_A :
      ∀ f : WeakGridSpace.BesovishSpace AS q,
        ∃ hfA : WeakGridSpace.MemBesovishCoeffCost A q
            (f : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.BesovishSpace.Norm_Costpq A q
              (⟨(f : Lp ℂ p G.toWeakGridSpace.measure), hfA⟩ :
                WeakGridSpace.BesovishSpace A q)
            ≤ C1 * WeakGridSpace.BesovishSpace.Norm_Costpq AS q f :=
    scaledAtomInclusionEmbedding AS A C1 hC1_pos.le hSouza_to_A_atoms
  have hA_to_Besov :
      ∀ f : WeakGridSpace.BesovishSpace A q,
        ∃ hfB : WeakGridSpace.MemBesovishCoeffCost AB q
            (f : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.BesovishSpace.Norm_Costpq AB q
              (⟨(f : Lp ℂ p G.toWeakGridSpace.measure), hfB⟩ :
                WeakGridSpace.BesovishSpace AB q)
            ≤ C2 * WeakGridSpace.BesovishSpace.Norm_Costpq A q f :=
    scaledAtomInclusionEmbedding A AB C2 hC2_pos.le hA_to_Besov_raw
  let lamRoot : ℝ := G.grid.lambda2 ^ (β - s)
  let lamClaim : ℝ := lamRoot ^ p.toReal
  have hdelta_pos : 0 < β - s := sub_pos.mpr hβs
  have hlambda2_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  have hlamRoot_pos : 0 < lamRoot := by
    exact Real.rpow_pos_of_pos hlambda2_pos (β - s)
  have hlamRoot_lt_one : lamRoot < 1 := by
    exact Real.rpow_lt_one hlambda2_pos.le G.grid.hlambda2_lt_one hdelta_pos
  have hp_toReal_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hlamClaim_pos : 0 < lamClaim := by
    exact Real.rpow_pos_of_pos hlamRoot_pos p.toReal
  have hlamClaim_lt_one : lamClaim < 1 := by
    exact Real.rpow_lt_one hlamRoot_pos.le hlamRoot_lt_one hp_toReal_pos
  have hG2Souza : WeakGridSpace.AssumptionG2 G.toWeakGridSpace s p ∞ q :=
    souza_assumptionG2 G s p q hs (Fact.out : 1 ≤ p) hp_top
  let Cclaim : ℝ := ((besovAtomConstant G β p qtilde)⁻¹) ^ p.toReal
  have hCclaim_nonneg : 0 ≤ Cclaim := by
    dsimp [Cclaim]
    exact Real.rpow_nonneg
      (inv_nonneg.mpr (besovAtomConstant_nonneg G β p qtilde)) _
  have hBesov_to_Souza_atoms_claimC :
      ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
      ∀ g : Lp ℂ p G.toWeakGridSpace.measure,
        (∃ φ : (AB.localSpace (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)).carrier,
          AB.IsAtom (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) φ ∧
            g = WeakGridSpace.atomLp AB
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) φ) →
          ∃ Rg : WeakGridSpace.LpGridRepresentation AS g,
            WeakGridSpace.CoeffFinitePQCost (p := p) (q := q) G.toWeakGridSpace
              (fun j S => (Rg.block j).coeff S) ∧
            (∀ j : ℕ, ∀ S : WeakGridSpace.LevelCell G.toWeakGridSpace j,
              (¬ S.1 ⊆ Q.1 → (Rg.block j).coeff S = 0) ∧
              (j < i → (Rg.block j).coeff S = 0)) ∧
            ∀ j : ℕ, i ≤ j → Rg.levelCoeffPower j ≤ Cclaim * lamClaim ^ (j - i) := by
    intro i Q g hg
    rcases hg with ⟨φ, hφ_atom, hg_eq⟩
    subst g
    let QG : GoodGridCell G := ⟨i, Q.1, Q.2⟩
    have hφ_besov :
        IsBesovAtom G s β p qtilde hβ (inferInstance : Fact (1 ≤ p)) hp_top QG
          (AB.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) φ) := by
      simpa [AB, besovAtomFamily, WeakGridSpace.AtomFamily.IsAtom,
        WeakGridSpace.AtomFamily.toFunction, QG] using hφ_atom
    rcases besovAtom_to_induced_souzaS_representation_decay_claimC
        G s β p qtilde hs hβ hβs hp_top QG hφ_besov with
      ⟨haLp, Rind, hRind_decay⟩
    let RA0 :=
      WeakGridSpace.inducedRepresentationToAmbient G.toWeakGridSpace QG.toLevelCell AS Rind
    have htoLp_atom :
        haLp.toLp =
          WeakGridSpace.atomLp AB
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) φ := by
      unfold WeakGridSpace.atomLp
      exact MeasureTheory.MemLp.toLp_congr _ _
        (Filter.Eventually.of_forall fun _ => rfl)
    let Rg : WeakGridSpace.LpGridRepresentation AS
        (WeakGridSpace.atomLp AB
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) φ) :=
      { block := RA0.block
        hasSum := by
          simpa [RA0, WeakGridSpace.inducedLpToAmbient, htoLp_atom] using RA0.hasSum }
    have hRind_fin :
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rind :=
      finitePQCost_of_levelCoeffPower_geometric_decay
        Rind Cclaim lamClaim hCclaim_nonneg hlamClaim_pos hlamClaim_lt_one hRind_decay
    have hRg_fin :
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rg := by
      simpa [Rg, RA0] using
        WeakGridSpace.inducedRepresentationToAmbient_finitePQCost
          G.toWeakGridSpace QG.toLevelCell AS Rind hRind_fin
    refine ⟨Rg, ?_, ?_, ?_⟩
    · simpa [WeakGridSpace.CoeffFinitePQCost,
        WeakGridSpace.LpGridRepresentation.FinitePQCost,
        WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hRg_fin
    · intro j S
      constructor
      · intro hS
        simpa [Rg, RA0, QG] using
          WeakGridSpace.inducedRepresentationToAmbient_coeff_eq_zero_of_not_subset
            G.toWeakGridSpace QG.toLevelCell AS Rind S hS
      · intro hj
        simpa [Rg, RA0, QG] using
          WeakGridSpace.inducedRepresentationToAmbient_coeff_lt
            G.toWeakGridSpace QG.toLevelCell AS Rind hj S
    · intro j hij
      let k : ℕ := j - i
      have hj_eq : j = i + k := by
        dsimp [k]
        omega
      calc
        Rg.levelCoeffPower j =
            Rind.levelCoeffPower k := by
              rw [hj_eq]
              change RA0.levelCoeffPower (i + k) = Rind.levelCoeffPower k
              simpa [RA0, QG, k] using
                WeakGridSpace.inducedRepresentationToAmbient_levelCoeffPower_add
                  G.toWeakGridSpace QG.toLevelCell AS Rind
        _ ≤ Cclaim * lamClaim ^ k := hRind_decay k
        _ = Cclaim * lamClaim ^ (j - i) := by simp [k]
  have hBesov_to_Souza_claimC :
      ∀ f : WeakGridSpace.BesovishSpace AB q,
        ∃ hfS : WeakGridSpace.MemBesovishCoeffCost AS q
            (f : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.BesovishSpace.Norm_Costpq AS q
              (⟨(f : Lp ℂ p G.toWeakGridSpace.measure), hfS⟩ :
                WeakGridSpace.BesovishSpace AS q) ≤
            WeakGridSpace.transmutationClaimCEmbeddingConstant
                G.toWeakGridSpace p q lamClaim Cclaim *
              WeakGridSpace.BesovishSpace.Norm_Costpq AB q f := by
    exact
      (WeakGridSpace.Transmutation_of_Atoms_continuous_embedding_explicit
        (G := G.toWeakGridSpace) (s := s) (p := p) (q := q)
        (u1 := 1) (u2 := ∞) AB AS lamClaim hlamClaim_pos hlamClaim_lt_one
        Cclaim hCclaim_nonneg hBesov_to_Souza_atoms_claimC hG2Souza hp_top hs).2
  have hA_to_Souza_claimC :
      ∀ f : WeakGridSpace.BesovishSpace A q,
        ∃ hfS : WeakGridSpace.MemBesovishCoeffCost AS q
            (f : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.BesovishSpace.Norm_Costpq AS q
              (⟨(f : Lp ℂ p G.toWeakGridSpace.measure), hfS⟩ :
                WeakGridSpace.BesovishSpace AS q) ≤
            WeakGridSpace.transmutationClaimCEmbeddingConstant
                G.toWeakGridSpace p q lamClaim Cclaim *
              C2 * WeakGridSpace.BesovishSpace.Norm_Costpq A q f := by
    intro f
    rcases hA_to_Besov f with ⟨hfB, hnormB⟩
    let fB : WeakGridSpace.BesovishSpace AB q :=
      ⟨(f : Lp ℂ p G.toWeakGridSpace.measure), hfB⟩
    rcases hBesov_to_Souza_claimC fB with ⟨hfS, hnormS⟩
    refine ⟨hfS, ?_⟩
    have hconst_nonneg :
        0 ≤ WeakGridSpace.transmutationClaimCEmbeddingConstant
            G.toWeakGridSpace p q lamClaim Cclaim :=
      (WeakGridSpace.Transmutation_of_Atoms_continuous_embedding_explicit
        (G := G.toWeakGridSpace) (s := s) (p := p) (q := q)
        (u1 := 1) (u2 := ∞) AB AS lamClaim hlamClaim_pos hlamClaim_lt_one
        Cclaim hCclaim_nonneg hBesov_to_Souza_atoms_claimC hG2Souza hp_top hs).1
    calc
      WeakGridSpace.BesovishSpace.Norm_Costpq AS q
          (⟨(f : Lp ℂ p G.toWeakGridSpace.measure), hfS⟩ :
            WeakGridSpace.BesovishSpace AS q)
        ≤ WeakGridSpace.transmutationClaimCEmbeddingConstant
            G.toWeakGridSpace p q lamClaim Cclaim *
          WeakGridSpace.BesovishSpace.Norm_Costpq AB q fB := hnormS
      _ ≤ WeakGridSpace.transmutationClaimCEmbeddingConstant
            G.toWeakGridSpace p q lamClaim Cclaim *
          (C2 * WeakGridSpace.BesovishSpace.Norm_Costpq A q f) := by
            exact mul_le_mul_of_nonneg_left hnormB hconst_nonneg
      _ = WeakGridSpace.transmutationClaimCEmbeddingConstant
            G.toWeakGridSpace p q lamClaim Cclaim *
          C2 * WeakGridSpace.BesovishSpace.Norm_Costpq A q f := by
            ring
  have hAS_subset_A :
      WeakGridSpace.BesovishSpace AS q ≤ WeakGridSpace.BesovishSpace A q := by
    intro f hf
    let fS : WeakGridSpace.BesovishSpace AS q := ⟨f, hf⟩
    exact (hSouza_to_A fS).choose
  have hA_subset_AB :
      WeakGridSpace.BesovishSpace A q ≤ WeakGridSpace.BesovishSpace AB q := by
    intro f hf
    let fA : WeakGridSpace.BesovishSpace A q := ⟨f, hf⟩
    exact (hA_to_Besov fA).choose
  have hAB_subset_AS :
      WeakGridSpace.BesovishSpace AB q ≤ WeakGridSpace.BesovishSpace AS q := by
    intro f hf
    let fB : WeakGridSpace.BesovishSpace AB q := ⟨f, hf⟩
    exact (hBesov_to_Souza_claimC fB).choose
  have hA_subset_AS :
      WeakGridSpace.BesovishSpace A q ≤ WeakGridSpace.BesovishSpace AS q := by
    intro f hf
    exact hAB_subset_AS (hA_subset_AB hf)
  have hAS_eq_A :
      WeakGridSpace.BesovishSpace AS q = WeakGridSpace.BesovishSpace A q :=
    le_antisymm hAS_subset_A hA_subset_AS
  have hA_eq_AB :
      WeakGridSpace.BesovishSpace A q = WeakGridSpace.BesovishSpace AB q := by
    refine le_antisymm hA_subset_AB ?_
    intro f hf
    exact hAS_subset_A (hAB_subset_AS hf)
  have hA_to_Souza_target :
      ∀ f : WeakGridSpace.BesovishSpace A q,
        ∃ hfS : WeakGridSpace.MemBesovishCoeffCost AS q
            (f : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.BesovishSpace.Norm_Costpq AS q
              (⟨(f : Lp ℂ p G.toWeakGridSpace.measure), hfS⟩ :
                WeakGridSpace.BesovishSpace AS q)
            ≤ (C2 / (1 - G.grid.lambda2 ^ (β - s))) *
              WeakGridSpace.BesovishSpace.Norm_Costpq A q f := by
    intro f
    rcases hA_to_Souza_claimC f with ⟨hfS, hnormS⟩
    refine ⟨hfS, le_trans hnormS ?_⟩
    have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
        hp_top
    have hCba_one : 1 ≤ besovAtomConstant G β p qtilde :=
      one_le_besovAtomConstant G β p qtilde hβ (inferInstance : Fact (1 ≤ p))
        hp_top
    have hCba_pos : 0 < besovAtomConstant G β p qtilde :=
      zero_lt_one.trans_le hCba_one
    have hCclaim_root :
        Cclaim ^ (1 / p.toReal) = (besovAtomConstant G β p qtilde)⁻¹ := by
      dsimp [Cclaim]
      simpa [one_div] using
        Real.rpow_rpow_inv (inv_nonneg.mpr hCba_pos.le) hp_pos.ne'
    have hCclaim_root_le_one : Cclaim ^ (1 / p.toReal) ≤ 1 := by
      rw [hCclaim_root]
      exact inv_le_one_of_one_le₀ hCba_one
    have hgeom_coeff :
        WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
            (WeakGridSpace.transmutationKernelZ lamClaim 0 1)
          = (1 - lamRoot)⁻¹ := by
      simpa [lamClaim] using
        WeakGridSpace.LpGridRepresentation.cCoefficientInt_transmutationKernelZ_zero_one
          (p := p) hp_top (rho := lamRoot) hlamRoot_pos hlamRoot_lt_one
    have hden_nonneg : 0 ≤ (1 - lamRoot)⁻¹ := by
      exact inv_nonneg.mpr (sub_nonneg.mpr hlamRoot_lt_one.le)
    have hclaim_const_eq :
        WeakGridSpace.transmutationClaimCEmbeddingConstant
            G.toWeakGridSpace p q lamClaim Cclaim =
          Cclaim ^ (1 / p.toReal) * (1 - lamRoot)⁻¹ := by
      simp [WeakGridSpace.transmutationClaimCEmbeddingConstant,
        GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid, hgeom_coeff]
    have hclaim_const_le :
        WeakGridSpace.transmutationClaimCEmbeddingConstant
            G.toWeakGridSpace p q lamClaim Cclaim
          ≤ (1 - lamRoot)⁻¹ := by
      rw [hclaim_const_eq]
      calc
        Cclaim ^ (1 / p.toReal) * (1 - lamRoot)⁻¹
            ≤ 1 * (1 - lamRoot)⁻¹ :=
              mul_le_mul_of_nonneg_right hCclaim_root_le_one hden_nonneg
        _ = (1 - lamRoot)⁻¹ := by ring
    have hconst_le :
        WeakGridSpace.transmutationClaimCEmbeddingConstant
            G.toWeakGridSpace p q lamClaim Cclaim * C2
          ≤ C2 / (1 - lamRoot) := by
      calc
        WeakGridSpace.transmutationClaimCEmbeddingConstant
            G.toWeakGridSpace p q lamClaim Cclaim * C2
            ≤ (1 - lamRoot)⁻¹ * C2 :=
              mul_le_mul_of_nonneg_right hclaim_const_le hC2_pos.le
        _ = C2 / (1 - lamRoot) := by ring
    have hnormA_nonneg :
        0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A q f :=
      WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
        (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A q) f
    calc
      WeakGridSpace.transmutationClaimCEmbeddingConstant
          G.toWeakGridSpace p q lamClaim Cclaim * C2 *
            WeakGridSpace.BesovishSpace.Norm_Costpq A q f
          ≤ (C2 / (1 - lamRoot)) *
              WeakGridSpace.BesovishSpace.Norm_Costpq A q f :=
            mul_le_mul_of_nonneg_right hconst_le hnormA_nonneg
      _ = (C2 / (1 - G.grid.lambda2 ^ (β - s))) *
              WeakGridSpace.BesovishSpace.Norm_Costpq A q f := by
            simp [lamRoot]
  simpa [AS, AB] using
    And.intro hAS_eq_A
      (And.intro hA_eq_AB (And.intro hSouza_to_A hA_to_Souza_target))

end

end GoodGridSpace
