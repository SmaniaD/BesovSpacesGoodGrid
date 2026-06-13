import BesovSpacesGoodGrid.GoodGrid.Multipliers.Bp1overpinftyisMultiplier

/-!
# The bounded Souza-Besov space as a quasi-algebra

This file starts the formalization of Proposition `mult33` (Pointwise
Multipliers III) from the paper: if two functions lie in
`B^s_{p,q} ∩ L^∞`, then their pointwise product lies in the same class, with
the expected bilinear estimate.

The public theorem below packages the proposition in the same style as the
multiplier files: concrete functions represent `Lp` classes, and `L^∞` data is
recorded as an almost-everywhere norm bound.  The remaining technical lemma is
the paper's `u₁ + u₂` construction for two `(s,p)` Souza representations.
In the paper notation, the canonical Souza atom on `Q` is
`|Q|^{s-1/p} \mathbbm{1}_Q`; in Lean this characteristic function is
implemented as `Set.indicator`.
-/

open scoped ENNReal Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

private theorem ae_norm_bound_nonneg
    (G : GoodGridSpace (α := α)) {f : α → ℂ} {M : ℝ}
    (hM : ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ M) :
    0 ≤ M := by
  have hμpos : 0 < G.grid.μ Set.univ := by
    refine G.grid.positive_measure 0 Set.univ ?_
    rw [G.grid.grid.first_partition_eq_univ]
    exact Finset.mem_singleton_self _
  have hμne : G.toWeakGridSpace.measure ≠ 0 := by
    intro h0
    rw [show G.toWeakGridSpace.measure = G.grid.μ from rfl] at h0
    rw [h0] at hμpos
    simp at hμpos
  haveI : Filter.NeBot (ae G.toWeakGridSpace.measure) :=
    ae_neBot.mpr hμne
  obtain ⟨z, hz⟩ := hM.exists
  exact le_trans (norm_nonneg (f z)) hz

/--
The elementary `L∞` part of Proposition `mult33`: if `f` and `g` are bounded
almost everywhere by `Mf` and `Mg`, respectively, then their pointwise product
is bounded almost everywhere by `Mf * Mg`.
-/
theorem ae_norm_mul_le_mul_bounds
    (G : GoodGridSpace (α := α)) {f g : α → ℂ} {Mf Mg : ℝ}
    (hfM : ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ Mf)
    (hgM : ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ Mg) :
    ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z * g z‖ ≤ Mf * Mg := by
  have hMf0 : 0 ≤ Mf := ae_norm_bound_nonneg G hfM
  filter_upwards [hfM, hgM] with z hfz hgz
  calc
    ‖f z * g z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ Mf * Mg := mul_le_mul hfz hgz (norm_nonneg (g z)) hMf0

/--
The weighted ancestor tower of a Souza representation at a cell `Q`.

For a canonical `(s,p)` representation this is exactly the value at any point
of `Q` of the truncated standard expansion through the level of `Q`: every
ancestor contributes its coefficient times the local value
`|J|^{s-1/p}` of the canonical atom `|J|^{s-1/p} \mathbbm{1}_J` on that
ancestor.
-/
def weightedAncestorCoeffSum
    (G : GoodGridSpace (α := α)) {s : ℝ} {p : ℝ≥0∞}
    {hs : 0 < s} {hp : 1 ≤ p} {hp_top : p ≠ ∞}
    [Fact (1 ≤ p)]
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℂ := by
  classical
  exact ∑ j ∈ Finset.range (k + 1),
    ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      if Q.1 ⊆ J.1 then (R.block j).coeff J * (show ℂ from (R.block j).atom J) else 0

/-- The `u₁` block: collect the product terms where the `g` cell contains the
`f` cell, including equality. -/
private noncomputable def quasiU1Block
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {xf xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xf)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (k : ℕ) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k where
  coeff := fun Q => (Rf.block k).coeff Q * weightedAncestorCoeffSum G Rg Q
  atom := (Rf.block k).atom
  atom_mem := (Rf.block k).atom_mem

/-- Strict weighted ancestor tower, excluding the current level. -/
private def strictWeightedAncestorCoeffSum
    (G : GoodGridSpace (α := α)) {s : ℝ} {p : ℝ≥0∞}
    {hs : 0 < s} {hp : 1 ≤ p} {hp_top : p ≠ ∞}
    [Fact (1 ≤ p)]
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    {j : ℕ} (J : WeakGridSpace.LevelCell G.toWeakGridSpace j) : ℂ := by
  classical
  exact ∑ k ∈ Finset.range j,
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      if J.1 ⊆ Q.1 then
        (R.block k).coeff Q * (show ℂ from (R.block k).atom Q)
      else 0

/-- The `u₂` block: collect the product terms where the `f` cell strictly
contains the `g` cell. -/
private noncomputable def quasiU2Block
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {xf xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xf)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (j : ℕ) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) j :=
  { coeff := fun J =>
      (Rg.block j).coeff J * strictWeightedAncestorCoeffSum G Rf J
    atom := (Rg.block j).atom
    atom_mem := (Rg.block j).atom_mem }

/-- Levelwise cost of `quasiU1Block` from the `L∞` tower bound on `g`. -/
private theorem quasiU1Block_levelCoeffPower_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {xf xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xf)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    {M : ℝ} (hM0 : 0 ≤ M)
    (htower : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G Rg Q‖ ≤ M)
    (k : ℕ) :
    (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(quasiU1Block G s p hs hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal) ≤
      M ^ p.toReal * Rf.levelCoeffPower k := by
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hterm : ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ‖(quasiU1Block G s p hs hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal ≤
        M ^ p.toReal * ‖(Rf.block k).coeff Q‖ ^ p.toReal := by
    intro Q
    have hnorm :
        ‖(quasiU1Block G s p hs hp hp_top Rf Rg k).coeff Q‖ =
          ‖(Rf.block k).coeff Q‖ * ‖weightedAncestorCoeffSum G Rg Q‖ :=
      norm_mul _ _
    have hle :
        ‖(Rf.block k).coeff Q‖ * ‖weightedAncestorCoeffSum G Rg Q‖ ≤
          ‖(Rf.block k).coeff Q‖ * M :=
      mul_le_mul_of_nonneg_left (htower k Q) (norm_nonneg _)
    calc
      ‖(quasiU1Block G s p hs hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal
          ≤ (‖(Rf.block k).coeff Q‖ * M) ^ p.toReal := by
        rw [hnorm]
        exact Real.rpow_le_rpow
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hle hpt_pos.le
      _ = M ^ p.toReal * ‖(Rf.block k).coeff Q‖ ^ p.toReal := by
        rw [Real.mul_rpow (norm_nonneg _) hM0, mul_comm]
  calc
    (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(quasiU1Block G s p hs hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal)
        ≤ ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            M ^ p.toReal * ‖(Rf.block k).coeff Q‖ ^ p.toReal :=
      Finset.sum_le_sum fun Q _ => hterm Q
    _ = M ^ p.toReal *
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            ‖(Rf.block k).coeff Q‖ ^ p.toReal := by
      rw [Finset.mul_sum]
    _ = M ^ p.toReal * Rf.levelCoeffPower k := rfl

/-- Levelwise cost of `quasiU2Block` from the strict ancestor tower bound on
`f`.  The strict tower is bounded by the full weighted tower. -/
private theorem quasiU2Block_levelCoeffPower_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {xf xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xf)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hstrict : ∀ (j : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace j),
      ‖strictWeightedAncestorCoeffSum G Rf J‖ ≤ M)
    (j : ℕ) :
    (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
        ‖(quasiU2Block G s p hs hp hp_top Rf Rg j).coeff J‖ ^ p.toReal) ≤
      M ^ p.toReal * Rg.levelCoeffPower j := by
  classical
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hterm : ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      ‖(quasiU2Block G s p hs hp hp_top Rf Rg j).coeff J‖ ^ p.toReal ≤
        M ^ p.toReal * ‖(Rg.block j).coeff J‖ ^ p.toReal := by
    intro J
    have hcoeff :
        (quasiU2Block G s p hs hp hp_top Rf Rg j).coeff J =
          (Rg.block j).coeff J * strictWeightedAncestorCoeffSum G Rf J := rfl
    have hnorm :
        ‖(quasiU2Block G s p hs hp hp_top Rf Rg j).coeff J‖ =
          ‖(Rg.block j).coeff J‖ * ‖strictWeightedAncestorCoeffSum G Rf J‖ := by
      rw [hcoeff, norm_mul]
    have hle :
        ‖(Rg.block j).coeff J‖ * ‖strictWeightedAncestorCoeffSum G Rf J‖ ≤
          ‖(Rg.block j).coeff J‖ * M :=
      mul_le_mul_of_nonneg_left (hstrict j J) (norm_nonneg _)
    calc
      ‖(quasiU2Block G s p hs hp hp_top Rf Rg j).coeff J‖ ^ p.toReal
          ≤ (‖(Rg.block j).coeff J‖ * M) ^ p.toReal := by
        rw [hnorm]
        exact Real.rpow_le_rpow
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hle hpt_pos.le
      _ = M ^ p.toReal * ‖(Rg.block j).coeff J‖ ^ p.toReal := by
        rw [Real.mul_rpow (norm_nonneg _) hM0, mul_comm]
  calc
    (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
        ‖(quasiU2Block G s p hs hp hp_top Rf Rg j).coeff J‖ ^ p.toReal)
        ≤ ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            M ^ p.toReal * ‖(Rg.block j).coeff J‖ ^ p.toReal :=
      Finset.sum_le_sum fun J _ => hterm J
    _ = M ^ p.toReal *
          ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            ‖(Rg.block j).coeff J‖ ^ p.toReal := by
      rw [Finset.mul_sum]
    _ = M ^ p.toReal * Rg.levelCoeffPower j := rfl

private theorem quasi_rpow_one_div_rpow {x : ℝ} (hx : 0 ≤ x) {e : ℝ} (he : e ≠ 0) :
    (x ^ (1 / e)) ^ e = x := by
  rw [← Real.rpow_mul hx, one_div, inv_mul_cancel₀ he, Real.rpow_one]

private theorem quasi_rpow_rpow_one_div {x : ℝ} (hx : 0 ≤ x) {e : ℝ} (he : e ≠ 0) :
    (x ^ e) ^ (1 / e) = x := by
  rw [← Real.rpow_mul hx, mul_one_div, div_self he, Real.rpow_one]

/-- Cost transfer at `q = ∞` for a bare Souza block sequence. -/
private theorem quasi_abstract_cost_top_of_blockLvlCoeff_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    (B : (k : ℕ) → WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    {b : ℕ → ℝ} {D : ℝ} (_hD : 0 ≤ D)
    (hb0 : ∀ k, 0 ≤ b k) (hbD : ∀ k, b k ≤ D)
    (hroot : ∀ k, WeakGridSpace.blockLvlCoeff
      (A := souzaAtomFamily G s p hs hp hp_top) B k ≤ b k ^ p.toReal) :
    WeakGridSpace.AbstractFinitePQCost (q := (∞ : ℝ≥0∞)) B ∧
      WeakGridSpace.abstractPQCost (q := (∞ : ℝ≥0∞)) B ≤ D := by
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hroot' : ∀ k,
      (WeakGridSpace.blockLvlCoeff
        (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (1 / p.toReal) ≤ D := by
    intro k
    calc
      (WeakGridSpace.blockLvlCoeff
          (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (1 / p.toReal)
          ≤ (b k ^ p.toReal) ^ (1 / p.toReal) :=
        Real.rpow_le_rpow
          (WeakGridSpace.blockLvlCoeff_nonneg
            (A := souzaAtomFamily G s p hs hp hp_top) B k)
          (hroot k) (by positivity)
      _ = b k := quasi_rpow_rpow_one_div (hb0 k) hpt_pos.ne'
      _ ≤ D := hbD k
  constructor
  · rw [WeakGridSpace.AbstractFinitePQCost, if_pos rfl]
    exact ⟨D, by rintro x ⟨k, rfl⟩; exact hroot' k⟩
  · rw [WeakGridSpace.abstractPQCost, if_pos rfl]
    exact csSup_le (Set.range_nonempty _) (by rintro x ⟨k, rfl⟩; exact hroot' k)

/-- Cost transfer at `q ≠ ∞` for a bare Souza block sequence. -/
private theorem quasi_abstract_cost_finite_of_blockLvlCoeff_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hq_top : q ≠ ∞)
    (B : (k : ℕ) → WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    {b : ℕ → ℝ}
    (hb0 : ∀ k, 0 ≤ b k)
    (hbsum : Summable fun k => b k ^ q.toReal)
    (hroot : ∀ k, WeakGridSpace.blockLvlCoeff
      (A := souzaAtomFamily G s p hs hp hp_top) B k ≤ b k ^ p.toReal) :
    WeakGridSpace.AbstractFinitePQCost (q := q) B ∧
      WeakGridSpace.abstractPQCost (q := q) B ≤
        (∑' k, b k ^ q.toReal) ^ (1 / q.toReal) := by
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hqt_pos : 0 < q.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq_top
  have hterm : ∀ k,
      (WeakGridSpace.blockLvlCoeff
        (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (q.toReal / p.toReal) ≤
        b k ^ q.toReal := by
    intro k
    calc
      (WeakGridSpace.blockLvlCoeff
          (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (q.toReal / p.toReal)
          ≤ (b k ^ p.toReal) ^ (q.toReal / p.toReal) :=
        Real.rpow_le_rpow
          (WeakGridSpace.blockLvlCoeff_nonneg
            (A := souzaAtomFamily G s p hs hp hp_top) B k)
          (hroot k) (by positivity)
      _ = b k ^ q.toReal := by
        rw [← Real.rpow_mul (hb0 k)]
        congr 1
        field_simp
  have hterm_nonneg : ∀ k,
      0 ≤ (WeakGridSpace.blockLvlCoeff
        (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (q.toReal / p.toReal) :=
    fun k => Real.rpow_nonneg
      (WeakGridSpace.blockLvlCoeff_nonneg
        (A := souzaAtomFamily G s p hs hp hp_top) B k) _
  have hsum : Summable (fun k =>
      (WeakGridSpace.blockLvlCoeff
        (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (q.toReal / p.toReal)) :=
    Summable.of_nonneg_of_le hterm_nonneg hterm hbsum
  constructor
  · rw [WeakGridSpace.AbstractFinitePQCost, if_neg hq_top]
    exact hsum
  · rw [WeakGridSpace.abstractPQCost, if_neg hq_top]
    refine Real.rpow_le_rpow (tsum_nonneg hterm_nonneg) ?_ (by positivity)
    exact hsum.tsum_le_tsum hterm hbsum

/-- If the level roots of a block family are bounded by `M` times those of an
existing finite-cost representation, then its abstract cost is bounded by the
same multiple of the representation cost. -/
private theorem quasi_abstract_cost_le_mul_rep_cost
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (B : (k : ℕ) → WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hroot : ∀ k, WeakGridSpace.blockLvlCoeff
      (A := souzaAtomFamily G s p hs hp hp_top) B k ≤
        (M * (R.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal) :
    WeakGridSpace.AbstractFinitePQCost (q := q) B ∧
      WeakGridSpace.abstractPQCost (q := q) B ≤
        M * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hlvl_nonneg : ∀ k, 0 ≤ R.levelCoeffPower k := fun k =>
    Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
  let r : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
  have hr0 : ∀ k, 0 ≤ r k := fun k => Real.rpow_nonneg (hlvl_nonneg k) _
  let Rcost : ℝ := WeakGridSpace.LpGridRepresentation.pqCost (q := q) R
  have hRcost0 : 0 ≤ Rcost := WeakGridSpace.LpGridRepresentation.pqCost_nonneg R
  have hrootR : ∀ k, r k ≤ Rcost := fun k =>
    WeakGridSpace.AtomFamily.levelCoeffRoot_le_pqCost
      (souzaAtomFamily G s p hs hp hp_top) R hRfin k
  have hr_pow_eq : ∀ (_ : q ≠ ∞),
      (fun k => r k ^ q.toReal) =
        fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
    intro _
    funext k
    simp only [r]
    rw [← Real.rpow_mul (hlvl_nonneg k), one_div, inv_mul_eq_div]
  have hr_sum : ∀ (_ : q ≠ ∞), Summable (fun k => r k ^ q.toReal) := by
    intro hq_top
    rw [hr_pow_eq hq_top]
    have h := hRfin
    rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hq_top] at h
    exact h
  have hr_tsum_root : ∀ (hq_top : q ≠ ∞),
      (∑' k, r k ^ q.toReal) ^ (1 / q.toReal) = Rcost := by
    intro hq_top
    dsimp [Rcost]
    rw [hr_pow_eq hq_top,
      WeakGridSpace.LpGridRepresentation.pqCost, if_neg hq_top]
  by_cases hq_top : q = ∞
  · subst hq_top
    exact quasi_abstract_cost_top_of_blockLvlCoeff_le G s p hs hp hp_top B
      (mul_nonneg hM0 hRcost0) (fun k => mul_nonneg hM0 (hr0 k))
      (fun k => mul_le_mul_of_nonneg_left (hrootR k) hM0) hroot
  · have hqt1 : 1 ≤ q.toReal := by
      have h := ENNReal.toReal_mono hq_top (Fact.out : (1 : ℝ≥0∞) ≤ q)
      simpa using h
    have hqt_pos : 0 < q.toReal := lt_of_lt_of_le zero_lt_one hqt1
    have hMr_sum : Summable (fun k => (M * r k) ^ q.toReal) := by
      have heq : (fun k => (M * r k) ^ q.toReal) =
          fun k => M ^ q.toReal * r k ^ q.toReal := by
        funext k
        exact Real.mul_rpow hM0 (hr0 k)
      rw [heq]
      exact (hr_sum hq_top).mul_left _
    obtain ⟨hfin, hcost⟩ := quasi_abstract_cost_finite_of_blockLvlCoeff_le
      G s p q hs hp hp_top hq_top B (fun k => mul_nonneg hM0 (hr0 k))
      hMr_sum hroot
    refine ⟨hfin, le_trans hcost ?_⟩
    have htsum_eq : (∑' k, (M * r k) ^ q.toReal) =
        M ^ q.toReal * ∑' k, r k ^ q.toReal := by
      rw [← tsum_mul_left]
      exact tsum_congr fun k => Real.mul_rpow hM0 (hr0 k)
    rw [htsum_eq, Real.mul_rpow (Real.rpow_nonneg hM0 _)
      (tsum_nonneg fun k => Real.rpow_nonneg (hr0 k) _),
      quasi_rpow_rpow_one_div hM0 hqt_pos.ne', hr_tsum_root hq_top]

/-- Pointwise evaluation of a Souza level block at a point in a level cell. -/
private theorem quasi_toFunLt_eq_coeff_mul_atom
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {k : ℕ}
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k)
    {z : α} {Q : WeakGridSpace.LevelCell G.toWeakGridSpace k} (hz : z ∈ Q.1) :
    B.toFunLt (souzaAtomFamily G s p hs hp hp_top) z =
      B.coeff Q * (show ℂ from B.atom Q) := by
  classical
  simp only [WeakGridSpace.LevelBlock.toFunLt]
  have hother : ∀ Q' ∈ (G.toWeakGridSpace.grid.partitions k).attach, Q' ≠ Q →
      B.coeff Q' * (souzaAtomFamily G s p hs hp hp_top).toFunction
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q')
        (B.atom Q') z = 0 := by
    intro Q' _ hQ'Q
    have hzQ' : z ∉ Q'.1 := by
      intro hzin
      exact hQ'Q (Subtype.ext
        (DiracApproximation.cell_eq_of_mem_of_mem G Q'.2 Q.2 hzin hz))
    have hfn : (souzaAtomFamily G s p hs hp hp_top).toFunction
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q')
        (B.atom Q') z = 0 := by
      change Q'.1.indicator (fun _ => (show ℂ from B.atom Q')) z = 0
      exact Set.indicator_of_notMem hzQ' _
    rw [hfn, mul_zero]
  rw [Finset.sum_eq_single Q hother
    (fun h => absurd (Finset.mem_attach _ _) h)]
  have hfn : (souzaAtomFamily G s p hs hp hp_top).toFunction
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
      (B.atom Q) z = (show ℂ from B.atom Q) := by
    change Q.1.indicator (fun _ => (show ℂ from B.atom Q)) z = _
    exact Set.indicator_of_mem hz _
  rw [hfn]

open Classical in
/-- Collapse a guarded ancestor sum along the tower of cells containing a point. -/
private theorem quasi_tower_ite_sum_collapse
    (G : GoodGridSpace (α := α))
    {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) {z : α}
    {Qlow : WeakGridSpace.LevelCell G.toWeakGridSpace m₂} (hzlow : z ∈ Qlow.1)
    {Qhigh : WeakGridSpace.LevelCell G.toWeakGridSpace m₁} (hzhigh : z ∈ Qhigh.1)
    (F : WeakGridSpace.LevelCell G.toWeakGridSpace m₁ → ℂ) :
    (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace m₁,
        if Qlow.1 ⊆ Q.1 then F Q else 0) = F Qhigh := by
  classical
  have hsub : Qlow.1 ⊆ Qhigh.1 := by
    rcases GoodGridCell.subset_or_disjoint_of_le
        (⟨m₁, Qhigh.1, Qhigh.2⟩ : GoodGridCell G)
        (⟨m₂, Qlow.1, Qlow.2⟩ : GoodGridCell G) h with hsub | hdis
    · exact hsub
    · exact absurd hzhigh (Set.disjoint_left.mp hdis hzlow)
  have hother : ∀ Q' : WeakGridSpace.LevelCell G.toWeakGridSpace m₁,
      Q' ∈ Finset.univ → Q' ≠ Qhigh →
        (if Qlow.1 ⊆ Q'.1 then F Q' else 0) = 0 := by
    intro Q' _ hQ'
    by_cases hss : Qlow.1 ⊆ Q'.1
    · exact absurd (Subtype.ext
        (DiracApproximation.cell_eq_of_mem_of_mem G Q'.2 Qhigh.2
          (hss hzlow) hzhigh)) hQ'
    · exact if_neg hss
  rw [Finset.sum_eq_single Qhigh hother
    (fun h' => absurd (Finset.mem_univ _) h'), if_pos hsub]

/-- The full weighted ancestor tower is the partial sum along a point's cell
tower. -/
private theorem weightedAncestorCoeffSum_tower_eq
    (G : GoodGridSpace (α := α)) {s : ℝ} {p : ℝ≥0∞}
    {hs : 0 < s} {hp : 1 ≤ p} {hp_top : p ≠ ∞} [Fact (1 ≤ p)]
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    {k : ℕ} (Qz : ∀ m : ℕ, WeakGridSpace.LevelCell G.toWeakGridSpace m)
    {z : α} (hQz : ∀ m, z ∈ (Qz m).1) :
    weightedAncestorCoeffSum G R (Qz k) =
      ∑ j ∈ Finset.range (k + 1),
        (R.block j).coeff (Qz j) * (show ℂ from (R.block j).atom (Qz j)) := by
  unfold weightedAncestorCoeffSum
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact quasi_tower_ite_sum_collapse G hjk (hQz k) (hQz j)
    (fun J => (R.block j).coeff J * (show ℂ from (R.block j).atom J))

/-- The strict weighted ancestor tower is the strict partial sum along a
point's cell tower. -/
private theorem strictWeightedAncestorCoeffSum_tower_eq
    (G : GoodGridSpace (α := α)) {s : ℝ} {p : ℝ≥0∞}
    {hs : 0 < s} {hp : 1 ≤ p} {hp_top : p ≠ ∞} [Fact (1 ≤ p)]
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    {k : ℕ} (Qz : ∀ m : ℕ, WeakGridSpace.LevelCell G.toWeakGridSpace m)
    {z : α} (hQz : ∀ m, z ∈ (Qz m).1) :
    strictWeightedAncestorCoeffSum G R (Qz k) =
      ∑ j ∈ Finset.range k,
        (R.block j).coeff (Qz j) * (show ℂ from (R.block j).atom (Qz j)) := by
  unfold strictWeightedAncestorCoeffSum
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjk : j ≤ k := le_of_lt (Finset.mem_range.mp hj)
  exact quasi_tower_ite_sum_collapse G hjk (hQz k) (hQz j)
    (fun J => (R.block j).coeff J * (show ℂ from (R.block j).atom J))

/-- Triangular split of a finite product of scalar partial sums. -/
private theorem quasi_truncation_scalar_identity (v w : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, v k) * (∑ j ∈ Finset.range n, w j) =
      (∑ k ∈ Finset.range n, v k * ∑ j ∈ Finset.range (k + 1), w j) +
        ∑ j ∈ Finset.range n, w j * ∑ k ∈ Finset.range j, v k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      linear_combination ih

/-- Pointwise identity for the truncated quasi-algebra product blocks. -/
private theorem quasi_truncated_pointwise_identity
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {xf xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xf)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (n : ℕ) (z : α) :
    (∑ k ∈ Finset.range n,
        (Rf.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) z) *
      (∑ j ∈ Finset.range n,
        (Rg.block j).toFunLt (souzaAtomFamily G s p hs hp hp_top) z) =
      (∑ k ∈ Finset.range n,
          (quasiU1Block G s p hs hp hp_top Rf Rg k).toFunLt
            (souzaAtomFamily G s p hs hp hp_top) z) +
        ∑ j ∈ Finset.range n,
          (quasiU2Block G s p hs hp hp_top Rf Rg j).toFunLt
            (souzaAtomFamily G s p hs hp hp_top) z := by
  classical
  have hex : ∀ m : ℕ,
      ∃ Q : WeakGridSpace.LevelCell G.toWeakGridSpace m, z ∈ Q.1 := by
    intro m
    have hz : z ∈ ⋃ t ∈ G.grid.grid.partitions m, t := by
      rw [G.grid.grid.covering m]
      trivial
    rcases Set.mem_iUnion₂.mp hz with ⟨Qs, hQs, hzQ⟩
    exact ⟨⟨Qs, hQs⟩, hzQ⟩
  choose Qz hQz using hex
  let v : ℕ → ℂ := fun k =>
    (Rf.block k).coeff (Qz k) * (show ℂ from (Rf.block k).atom (Qz k))
  let w : ℕ → ℂ := fun j =>
    (Rg.block j).coeff (Qz j) * (show ℂ from (Rg.block j).atom (Qz j))
  have hf_val : ∀ k, (Rf.block k).toFunLt
      (souzaAtomFamily G s p hs hp hp_top) z = v k := by
    intro k
    exact quasi_toFunLt_eq_coeff_mul_atom G s p hs hp hp_top
      (Rf.block k) (hQz k)
  have hg_val : ∀ j, (Rg.block j).toFunLt
      (souzaAtomFamily G s p hs hp hp_top) z = w j := by
    intro j
    exact quasi_toFunLt_eq_coeff_mul_atom G s p hs hp hp_top
      (Rg.block j) (hQz j)
  have hu1_val : ∀ k, (quasiU1Block G s p hs hp hp_top Rf Rg k).toFunLt
      (souzaAtomFamily G s p hs hp hp_top) z =
      v k * ∑ j ∈ Finset.range (k + 1), w j := by
    intro k
    rw [quasi_toFunLt_eq_coeff_mul_atom G s p hs hp hp_top
      (quasiU1Block G s p hs hp hp_top Rf Rg k) (hQz k)]
    change ((Rf.block k).coeff (Qz k) * weightedAncestorCoeffSum G Rg (Qz k)) *
        (show ℂ from (Rf.block k).atom (Qz k)) =
      v k * ∑ j ∈ Finset.range (k + 1), w j
    rw [weightedAncestorCoeffSum_tower_eq G Rg Qz hQz]
    ring
  have hu2_val : ∀ j, (quasiU2Block G s p hs hp hp_top Rf Rg j).toFunLt
      (souzaAtomFamily G s p hs hp hp_top) z =
      w j * ∑ k ∈ Finset.range j, v k := by
    intro j
    rw [quasi_toFunLt_eq_coeff_mul_atom G s p hs hp hp_top
      (quasiU2Block G s p hs hp hp_top Rf Rg j) (hQz j)]
    change ((Rg.block j).coeff (Qz j) * strictWeightedAncestorCoeffSum G Rf (Qz j)) *
        (show ℂ from (Rg.block j).atom (Qz j)) =
      w j * ∑ k ∈ Finset.range j, v k
    rw [strictWeightedAncestorCoeffSum_tower_eq G Rf Qz hQz]
    ring
  simp only [hf_val, hg_val, hu1_val, hu2_val]
  exact quasi_truncation_scalar_identity v w n

/-- The `L^p` representative of a finite block sum agrees a.e. with the
pointwise sum of the block functions. -/
private theorem quasi_coeFn_finset_range_sum_toLp
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u : ℝ≥0∞}
    [Fact (1 ≤ p)]
    (A : WeakGridSpace.AtomFamily G' s p u)
    (B : (k : ℕ) → WeakGridSpace.LevelBlock A k) (n : ℕ) :
    ((∑ k ∈ Finset.range n, (B k).toLp A : Lp ℂ p G'.measure) : α → ℂ)
      =ᵐ[G'.measure] fun z => ∑ k ∈ Finset.range n, (B k).toFunLt A z := by
  induction n with
  | zero =>
      simpa using Lp.coeFn_zero ℂ p G'.measure
  | succ n ih =>
      rw [Finset.sum_range_succ]
      refine (Lp.coeFn_add _ _).trans ?_
      filter_upwards [ih, WeakGridSpace.LevelBlock.coeFn_toLp A (B n)]
        with z hz1 hz2
      simp only [Pi.add_apply, Finset.sum_range_succ, hz1, hz2]

/-- Pointwise-product representation under simultaneous `L^p` limits with a
varying multiplier sequence. -/
private theorem quasi_representsProduct_of_tendsto_Lp_varying
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {g : α → ℂ} {mseq xseq yseq : ℕ → Lp ℂ p G'.measure}
    {xg x y : Lp ℂ p G'.measure}
    (hgrep : ((xg : α → ℂ)) =ᵐ[G'.measure] g)
    (hm : Filter.Tendsto mseq Filter.atTop (𝓝 xg))
    (hx : Filter.Tendsto xseq Filter.atTop (𝓝 x))
    (hy : Filter.Tendsto yseq Filter.atTop (𝓝 y))
    (hprod : ∀ n, (yseq n : α → ℂ) =ᵐ[G'.measure]
      fun z => (mseq n : α → ℂ) z * (xseq n : α → ℂ) z) :
    WeakGridSpace.RepresentsPointwiseProduct (G := G') (p := p) g x y := by
  classical
  have hxm : TendstoInMeasure G'.measure (fun n => xseq n)
      Filter.atTop x := tendstoInMeasure_of_tendsto_Lp hx
  rcases hxm.exists_seq_tendsto_ae with ⟨φ, hφ_mono, hx_ae⟩
  have hm_sub : Filter.Tendsto (fun n => mseq (φ n)) Filter.atTop (𝓝 xg) :=
    hm.comp hφ_mono.tendsto_atTop
  have hmm : TendstoInMeasure G'.measure (fun n => mseq (φ n))
      Filter.atTop xg := tendstoInMeasure_of_tendsto_Lp hm_sub
  rcases hmm.exists_seq_tendsto_ae with ⟨ψ, hψ_mono, hm_ae⟩
  have hy_sub : Filter.Tendsto (fun n => yseq (φ (ψ n))) Filter.atTop (𝓝 y) :=
    hy.comp (hφ_mono.comp hψ_mono).tendsto_atTop
  have hym : TendstoInMeasure G'.measure
      (fun n => yseq (φ (ψ n))) Filter.atTop y :=
    tendstoInMeasure_of_tendsto_Lp hy_sub
  rcases hym.exists_seq_tendsto_ae with ⟨ρ, hρ_mono, hy_ae⟩
  have hprod_ae : ∀ᵐ z ∂G'.measure, ∀ n : ℕ,
      (yseq (φ (ψ (ρ n))) : α → ℂ) z =
        (mseq (φ (ψ (ρ n))) : α → ℂ) z * (xseq (φ (ψ (ρ n))) : α → ℂ) z := by
    have hsets : (⋂ n : ℕ, {z : α |
        (yseq (φ (ψ (ρ n))) : α → ℂ) z =
          (mseq (φ (ψ (ρ n))) : α → ℂ) z *
            (xseq (φ (ψ (ρ n))) : α → ℂ) z}) ∈ ae G'.measure :=
      countable_iInter_mem.mpr fun n => hprod (φ (ψ (ρ n)))
    filter_upwards [hsets] with z hz n
    exact Set.mem_iInter.mp hz n
  filter_upwards [hx_ae, hm_ae, hy_ae, hprod_ae, hgrep]
    with z hxz hmz hyz hpz hgz
  have hx_sub2 : Filter.Tendsto (fun n => (xseq (φ (ψ (ρ n))) : α → ℂ) z)
      Filter.atTop (𝓝 ((x : α → ℂ) z)) :=
    hxz.comp (hψ_mono.comp hρ_mono).tendsto_atTop
  have hm_sub2 : Filter.Tendsto (fun n => (mseq (φ (ψ (ρ n))) : α → ℂ) z)
      Filter.atTop (𝓝 ((xg : α → ℂ) z)) :=
    hmz.comp hρ_mono.tendsto_atTop
  have hmul : Filter.Tendsto (fun n => (yseq (φ (ψ (ρ n))) : α → ℂ) z)
      Filter.atTop (𝓝 ((xg : α → ℂ) z * (x : α → ℂ) z)) := by
    refine (hm_sub2.mul hx_sub2).congr ?_
    intro n
    exact (hpz n).symm
  have huniq : (y : α → ℂ) z = (xg : α → ℂ) z * (x : α → ℂ) z :=
    tendsto_nhds_unique hyz hmul
  rw [huniq, hgz]

/-- Product construction from two concrete representations whose weighted
ancestor towers satisfy the `L∞` bounds required in the proof of `mult33`. -/
private theorem exists_quasi_product_of_tower_representations
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f g : α → ℂ) (Mf Mg : ℝ)
    (hMf0 : 0 ≤ Mf) (hMg0 : 0 ≤ Mg)
    (xf xg : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (xf : Lp ℂ p G.toWeakGridSpace.measure))
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (xg : Lp ℂ p G.toWeakGridSpace.measure))
    (hfrep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (xf : Lp ℂ p G.toWeakGridSpace.measure))
    (hgrep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) g
      (xg : Lp ℂ p G.toWeakGridSpace.measure))
    (hRffin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rf)
    (hRgfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rg)
    (htower_g : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G Rg Q‖ ≤ Mg)
    (hstrict_f : ∀ (j : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace j),
      ‖strictWeightedAncestorCoeffSum G Rf J‖ ≤ Mf) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => f z * g z)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs hp hp_top) q y ≤
        Mg * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf +
          Mf * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg := by
  classical
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hU1lvl : ∀ k, WeakGridSpace.blockLvlCoeff
      (A := souzaAtomFamily G s p hs hp hp_top)
      (fun k => quasiU1Block G s p hs hp hp_top Rf Rg k) k ≤
      (Mg * (Rf.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal := by
    intro k
    have h1 := quasiU1Block_levelCoeffPower_le G s p hs hp hp_top Rf Rg
      hMg0 htower_g k
    have hlvl_nonneg : 0 ≤ Rf.levelCoeffPower k :=
      Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
    have h2 :
        (Mg * (Rf.levelCoeffPower k) ^ (1 / p.toReal)) ^ p.toReal =
          Mg ^ p.toReal * Rf.levelCoeffPower k := by
      rw [Real.mul_rpow hMg0 (Real.rpow_nonneg hlvl_nonneg _)]
      rw [quasi_rpow_one_div_rpow hlvl_nonneg hpt_pos.ne']
    rwa [h2]
  have hU2lvl : ∀ j, WeakGridSpace.blockLvlCoeff
      (A := souzaAtomFamily G s p hs hp hp_top)
      (fun j => quasiU2Block G s p hs hp hp_top Rf Rg j) j ≤
      (Mf * (Rg.levelCoeffPower j) ^ (1 / p.toReal)) ^ p.toReal := by
    intro j
    have h1 := quasiU2Block_levelCoeffPower_le G s p hs hp hp_top Rf Rg
      hMf0 hstrict_f j
    have hlvl_nonneg : 0 ≤ Rg.levelCoeffPower j :=
      Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
    have h2 :
        (Mf * (Rg.levelCoeffPower j) ^ (1 / p.toReal)) ^ p.toReal =
          Mf ^ p.toReal * Rg.levelCoeffPower j := by
      rw [Real.mul_rpow hMf0 (Real.rpow_nonneg hlvl_nonneg _)]
      rw [quasi_rpow_one_div_rpow hlvl_nonneg hpt_pos.ne']
    rwa [h2]
  obtain ⟨hU1fin, hU1cost⟩ :=
    quasi_abstract_cost_le_mul_rep_cost G s p q hs hp hp_top Rf hRffin
      (fun k => quasiU1Block G s p hs hp hp_top Rf Rg k) hMg0 hU1lvl
  obtain ⟨hU2fin, hU2cost⟩ :=
    quasi_abstract_cost_le_mul_rep_cost G s p q hs hp hp_top Rg hRgfin
      (fun j => quasiU2Block G s p hs hp hp_top Rf Rg j) hMf0 hU2lvl
  have hG2 := souza_assumptionG2 G s p q hs hp hp_top
  obtain ⟨y1Lp, hy1ne⟩ := WeakGridSpace.formalBlockSeq_hasRepresentation
    hG2 hp_top hs le_top
    (fun k => quasiU1Block G s p hs hp hp_top Rf Rg k) hU1fin
  obtain ⟨⟨R1, hR1block⟩⟩ := hy1ne
  obtain ⟨y2Lp, hy2ne⟩ := WeakGridSpace.formalBlockSeq_hasRepresentation
    hG2 hp_top hs le_top
    (fun j => quasiU2Block G s p hs hp hp_top Rf Rg j) hU2fin
  obtain ⟨⟨R2, hR2block⟩⟩ := hy2ne
  have hR1fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R1 := by
    simpa [WeakGridSpace.AbstractFinitePQCost,
      WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower, hR1block]
      using hU1fin
  have hR2fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R2 := by
    simpa [WeakGridSpace.AbstractFinitePQCost,
      WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower, hR2block]
      using hU2fin
  have hR1cost : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R1 ≤
      Mg * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf := by
    have hlevel : ∀ k, R1.levelCoeffPower k =
        WeakGridSpace.blockLvlCoeff
          (A := souzaAtomFamily G s p hs hp hp_top)
          (fun j => quasiU1Block G s p hs hp hp_top Rf Rg j) k := by
      intro k
      simp [WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        WeakGridSpace.blockLvlCoeff, hR1block]
    have heq : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R1 =
        WeakGridSpace.abstractPQCost (q := q)
          (fun j => quasiU1Block G s p hs hp hp_top Rf Rg j) := by
      simp [WeakGridSpace.LpGridRepresentation.pqCost,
        WeakGridSpace.abstractPQCost, hlevel]
    rw [heq]
    exact hU1cost
  have hR2cost : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R2 ≤
      Mf * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg := by
    have hlevel : ∀ k, R2.levelCoeffPower k =
        WeakGridSpace.blockLvlCoeff
          (A := souzaAtomFamily G s p hs hp hp_top)
          (fun j => quasiU2Block G s p hs hp hp_top Rf Rg j) k := by
      intro k
      simp [WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        WeakGridSpace.blockLvlCoeff, hR2block]
    have heq : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R2 =
        WeakGridSpace.abstractPQCost (q := q)
          (fun j => quasiU2Block G s p hs hp hp_top Rf Rg j) := by
      simp [WeakGridSpace.LpGridRepresentation.pqCost,
        WeakGridSpace.abstractPQCost, hlevel]
    rw [heq]
    exact hU2cost
  let y1 : WeakGridSpace.BesovishSpace (souzaAtomFamily G s p hs hp hp_top) q :=
    ⟨y1Lp, ⟨R1, hR1fin⟩⟩
  let y2 : WeakGridSpace.BesovishSpace (souzaAtomFamily G s p hs hp hp_top) q :=
    ⟨y2Lp, ⟨R2, hR2fin⟩⟩
  let y : WeakGridSpace.BesovishSpace (souzaAtomFamily G s p hs hp hp_top) q := y1 + y2
  have h1sum : HasSum (fun k =>
      (quasiU1Block G s p hs hp hp_top Rf Rg k).toLp
        (souzaAtomFamily G s p hs hp hp_top)) y1Lp := by
    simpa [hR1block] using R1.hasSum
  have h2sum : HasSum (fun j =>
      (quasiU2Block G s p hs hp hp_top Rf Rg j).toLp
        (souzaAtomFamily G s p hs hp hp_top)) y2Lp := by
    simpa [hR2block] using R2.hasSum
  have hf_tend : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n,
      (Rf.block k).toLp (souzaAtomFamily G s p hs hp hp_top))
      Filter.atTop (𝓝 (xf : Lp ℂ p G.toWeakGridSpace.measure)) :=
    Rf.hasSum.tendsto_sum_nat
  have hg_tend : Filter.Tendsto (fun n => ∑ j ∈ Finset.range n,
      (Rg.block j).toLp (souzaAtomFamily G s p hs hp hp_top))
      Filter.atTop (𝓝 (xg : Lp ℂ p G.toWeakGridSpace.measure)) :=
    Rg.hasSum.tendsto_sum_nat
  have hy_tend : Filter.Tendsto (fun n =>
      (∑ k ∈ Finset.range n,
        (quasiU1Block G s p hs hp hp_top Rf Rg k).toLp
          (souzaAtomFamily G s p hs hp hp_top)) +
        ∑ j ∈ Finset.range n,
          (quasiU2Block G s p hs hp hp_top Rf Rg j).toLp
            (souzaAtomFamily G s p hs hp hp_top))
      Filter.atTop (𝓝 (y1Lp + y2Lp)) :=
    h1sum.tendsto_sum_nat.add h2sum.tendsto_sum_nat
  have hprodn : ∀ n,
      ((((∑ k ∈ Finset.range n,
          (quasiU1Block G s p hs hp hp_top Rf Rg k).toLp
            (souzaAtomFamily G s p hs hp hp_top)) +
          ∑ j ∈ Finset.range n,
            (quasiU2Block G s p hs hp hp_top Rf Rg j).toLp
              (souzaAtomFamily G s p hs hp hp_top)) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
        =ᵐ[G.toWeakGridSpace.measure]
      fun z => ((∑ j ∈ Finset.range n,
          (Rg.block j).toLp (souzaAtomFamily G s p hs hp hp_top) :
            Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z *
        ((∑ k ∈ Finset.range n,
          (Rf.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
            Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z := by
    intro n
    filter_upwards [Lp.coeFn_add
        (∑ k ∈ Finset.range n,
          (quasiU1Block G s p hs hp hp_top Rf Rg k).toLp
            (souzaAtomFamily G s p hs hp hp_top))
        (∑ j ∈ Finset.range n,
          (quasiU2Block G s p hs hp hp_top Rf Rg j).toLp
            (souzaAtomFamily G s p hs hp hp_top)),
      quasi_coeFn_finset_range_sum_toLp (souzaAtomFamily G s p hs hp hp_top)
        (fun k => quasiU1Block G s p hs hp hp_top Rf Rg k) n,
      quasi_coeFn_finset_range_sum_toLp (souzaAtomFamily G s p hs hp hp_top)
        (fun j => quasiU2Block G s p hs hp hp_top Rf Rg j) n,
      quasi_coeFn_finset_range_sum_toLp (souzaAtomFamily G s p hs hp hp_top)
        Rf.block n,
      quasi_coeFn_finset_range_sum_toLp (souzaAtomFamily G s p hs hp hp_top)
        Rg.block n] with z h0 h1 h2 hfz hgz
    rw [h0, Pi.add_apply, h1, h2, hfz, hgz]
    rw [mul_comm]
    exact (quasi_truncated_pointwise_identity G s p hs hp hp_top Rf Rg n z).symm
  have hyprod_gf : WeakGridSpace.RepresentsPointwiseProduct
      (G := G.toWeakGridSpace) (p := p) g
      (xf : Lp ℂ p G.toWeakGridSpace.measure)
      ((y1Lp + y2Lp) : Lp ℂ p G.toWeakGridSpace.measure) :=
    quasi_representsProduct_of_tendsto_Lp_varying
      (G' := G.toWeakGridSpace) hgrep hg_tend hf_tend hy_tend hprodn
  have hyrep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p)
      (fun z => f z * g z)
      (y : Lp ℂ p G.toWeakGridSpace.measure) := by
    change ((y1Lp + y2Lp : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
        =ᵐ[G.toWeakGridSpace.measure] fun z => f z * g z
    filter_upwards [hyprod_gf, hfrep] with z hyz hfz
    rw [hyz, hfz]
    ring
  refine ⟨y, hyrep, ?_⟩
  have htriangle := WeakGridSpace.BesovishSpace.Norm_Costpq_add_le
    (A := souzaAtomFamily G s p hs hp hp_top) (q := q) hp_top
    (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations
      (souzaAtomFamily G s p hs hp hp_top) q) y1 y2
  have hy1n : WeakGridSpace.BesovishSpace.Norm_Costpq
      (souzaAtomFamily G s p hs hp hp_top) q y1 ≤
      Mg * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf :=
    le_trans (WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost y1 R1 hR1fin)
      hR1cost
  have hy2n : WeakGridSpace.BesovishSpace.Norm_Costpq
      (souzaAtomFamily G s p hs hp hp_top) q y2 ≤
      Mf * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg :=
    le_trans (WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost y2 R2 hR2fin)
      hR2cost
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s p hs hp hp_top) q y
        ≤ WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q y1 +
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q y2 := htriangle
    _ ≤ Mg * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf +
          Mf * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg :=
      add_le_add hy1n hy2n

private theorem quasi_l2normalizedHaar_alpha_const
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (x y : α) :
    HaarRepresentation.L2normalizedHaar G F
        (UnbalancedHaarWavelet.FullHaarSystem.Index.alpha : F.Index) x =
      HaarRepresentation.L2normalizedHaar G F
        (UnbalancedHaarWavelet.FullHaarSystem.Index.alpha : F.Index) y := by
  simp [HaarRepresentation.L2normalizedHaar, HaarRepresentation.l2NormalizationFactor,
    UnbalancedHaarWavelet.FullHaarSystem.function, F.alphaFunction_def,
    UnbalancedHaarWavelet.normalizedAlphaFunction]

/-- Pointwise form of the level-zero standard Souza block. -/
private theorem canonicalStandardFatherLevelBlock_toFunLt
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (z : α) :
    (StandardAtomicRepresentation.canonicalStandardFatherLevelBlock
        G F s p hs hp hp_top f hf).toFunLt
        (souzaAtomFamily G s p hs hp hp_top) z =
      HaarRepresentation.Coeff G F f hf .alpha *
        HaarRepresentation.normalizedFunction G F .alpha z := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let B := StandardAtomicRepresentation.canonicalStandardFatherLevelBlock
    G F s p hs hp hp_top f hf
  unfold WeakGridSpace.LevelBlock.toFunLt
  simp only [StandardAtomicRepresentation.canonicalStandardFatherLevelBlock,
    GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
    WeakGridSpace.levelCellToWeakGridCell, WeakGridSpace.AtomFamily.toFunction,
    souzaAtomFamily, souzaLocalVectorSpace]
  let Qw : WeakGridSpace.LevelCell G.toWeakGridSpace 0 :=
    ⟨Set.univ, by
      change Set.univ ∈ G.grid.grid.partitions 0
      simp [G.grid.grid.first_partition_eq_univ]⟩
  have hsum :
      (∑ x_1 ∈ (G.grid.grid.partitions 0).attach,
          HaarRepresentation.Coeff G F f hf .alpha *
                HaarRepresentation.L2normalizedHaar G F .alpha
                  (StandardAtomicRepresentation.cellPoint G
                    { level := 0, cell := x_1.1, mem := x_1.2 }) /
              (((G.grid.μ x_1.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ) *
            Set.indicator x_1.1
              (fun _ =>
                (((G.grid.μ x_1.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) z) =
        HaarRepresentation.Coeff G F f hf .alpha *
              HaarRepresentation.L2normalizedHaar G F .alpha
                (StandardAtomicRepresentation.cellPoint G
                  { level := 0, cell := Qw.1, mem := Qw.2 }) /
            (((G.grid.μ Qw.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ) *
          Set.indicator Qw.1
            (fun _ =>
              (((G.grid.μ Qw.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) z := by
    exact Finset.sum_eq_single Qw
      (by
        intro P _ hne
        have hP_univ : P.1 = Set.univ := by
          have hP_mem : P.1 ∈ G.grid.grid.partitions 0 := P.2
          rw [G.grid.grid.first_partition_eq_univ] at hP_mem
          exact Finset.mem_singleton.mp hP_mem
        exact False.elim (hne (Subtype.ext hP_univ)))
      (by
        intro hnot
        exact False.elim (hnot (Finset.mem_attach _ Qw)))
  change
    (∑ x_1 ∈ (G.grid.grid.partitions 0).attach,
        HaarRepresentation.Coeff G F f hf .alpha *
              HaarRepresentation.L2normalizedHaar G F .alpha
                (StandardAtomicRepresentation.cellPoint G
                  { level := 0, cell := x_1.1, mem := x_1.2 }) /
            (((G.grid.μ x_1.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ) *
          Set.indicator x_1.1
            (fun _ =>
              (((G.grid.μ x_1.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) z) =
      HaarRepresentation.Coeff G F f hf .alpha *
        HaarRepresentation.normalizedFunction G F .alpha z
  rw [hsum]
  simp only [Qw, Set.mem_univ, Set.indicator_of_mem]
  let Q : GoodGridCell G :=
    { level := 0, cell := Set.univ,
      mem := by simp [G.grid.grid.first_partition_eq_univ] }
  let r : ℝ := (G.grid.μ Set.univ).toReal ^ (s - (p.toReal)⁻¹)
  have hr_pos : 0 < r := by
    have hμ_pos : 0 < G.grid.μ Set.univ :=
      G.grid.positive_measure 0 Set.univ
        (by simp [G.grid.grid.first_partition_eq_univ])
    letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
    have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ :=
      MeasureTheory.measure_ne_top G.grid.μ Set.univ
    have hμ_toReal_pos : 0 < (G.grid.μ Set.univ).toReal :=
      ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
    exact Real.rpow_pos_of_pos hμ_toReal_pos _
  have halpha :
      HaarRepresentation.L2normalizedHaar G F .alpha
          (StandardAtomicRepresentation.cellPoint G Q) =
        HaarRepresentation.normalizedFunction G F .alpha z :=
    (quasi_l2normalizedHaar_alpha_const G F
      (StandardAtomicRepresentation.cellPoint G Q) z).trans rfl
  change
    (HaarRepresentation.Coeff G F f hf .alpha *
        HaarRepresentation.L2normalizedHaar G F .alpha
          (StandardAtomicRepresentation.cellPoint G Q) / (r : ℂ)) *
      (r : ℂ) =
    HaarRepresentation.Coeff G F f hf .alpha *
      HaarRepresentation.normalizedFunction G F .alpha z
  rw [halpha]
  field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt hr_pos)]

private theorem canonicalStandardBlock_range_sum_toFunLt_eq_partialStandardSum
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) (z : α) :
    (∑ j ∈ Finset.range (k + 1),
        (StandardAtomicRepresentation.canonicalStandardLpGridBlock
          G F s p hs hp hp_top f hf j).toFunLt
          (souzaAtomFamily G s p hs hp hp_top) z) =
      DiracApproximation.partialStandardSum G F p s f hf k z := by
  classical
  rw [Finset.sum_range_succ']
  unfold DiracApproximation.partialStandardSum
  have hfather :
      (StandardAtomicRepresentation.canonicalStandardLpGridBlock
        G F s p hs hp hp_top f hf 0).toFunLt
          (souzaAtomFamily G s p hs hp hp_top) z =
        HaarRepresentation.Coeff G F f hf .alpha *
          HaarRepresentation.normalizedFunction G F .alpha z := by
    simpa [StandardAtomicRepresentation.canonicalStandardLpGridBlock] using
      canonicalStandardFatherLevelBlock_toFunLt G F s p hs hp hp_top f hf z
  rw [hfather, add_comm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _hj
  calc
    (StandardAtomicRepresentation.canonicalStandardLpGridBlock
        G F s p hs hp hp_top f hf (j + 1)).toFunLt
        (souzaAtomFamily G s p hs hp hp_top) z
        = StandardAtomicRepresentation.canonicalStandardLevelBlockFunction
            G F p s f hf j z := by
          exact StandardAtomicRepresentation.canonicalStandardPositiveLevelBlock_toFunLt
            G F s p hs hp hp_top f hf j z
    _ = StandardAtomicRepresentation.standardLevelBlockFunction
            G F p s f hf j z := by
          exact StandardAtomicRepresentation.canonicalStandardLevelBlock_eq_standardLevelBlock_pointwise
            G F p s f hf j z
    _ = ∑ Q ∈ (G.grid.grid.partitions j).attach,
          StandardAtomicRepresentation.standardCellBlockFunction G F p s f hf
            { level := j, cell := Q.1, mem := Q.2 } z := by
          change (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
              StandardAtomicRepresentation.standardCellBlockFunction G F p s f hf
                { level := j, cell := Q.1, mem := Q.2 } z) =
            ∑ Q ∈ (G.grid.grid.partitions j).attach,
              StandardAtomicRepresentation.standardCellBlockFunction G F p s f hf
                { level := j, cell := Q.1, mem := Q.2 } z
          rw [show
            (Finset.univ : Finset (WeakGridSpace.LevelCell G.toWeakGridSpace j)) =
              (G.grid.grid.partitions j).attach by
              ext Q
              constructor
              · intro _h
                exact Finset.mem_attach _ Q
              · intro _h
                exact Finset.mem_univ Q]
          rfl

private theorem weightedAncestorCoeffSum_canonicalStandard_eq_partialStandardSum
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (hblock : ∀ j, R.block j =
      StandardAtomicRepresentation.canonicalStandardLpGridBlock G F
        s p hs hp hp_top f hf j)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {z : α} (hz : z ∈ Q.1) :
    weightedAncestorCoeffSum G R Q =
      DiracApproximation.partialStandardSum G F p s f hf k z := by
  classical
  have hex : ∀ m : ℕ,
      ∃ P : WeakGridSpace.LevelCell G.toWeakGridSpace m, z ∈ P.1 := by
    intro m
    have hzmem : z ∈ ⋃ t ∈ G.grid.grid.partitions m, t := by
      rw [G.grid.grid.covering m]
      trivial
    rcases Set.mem_iUnion₂.mp hzmem with ⟨P, hP, hzP⟩
    exact ⟨⟨P, hP⟩, hzP⟩
  choose Qz hQz using hex
  have hQzk : Qz k = Q :=
    Subtype.ext (DiracApproximation.cell_eq_of_mem_of_mem G (Qz k).2 Q.2 (hQz k) hz)
  rw [← hQzk, weightedAncestorCoeffSum_tower_eq G R Qz hQz]
  calc
    (∑ j ∈ Finset.range (k + 1),
        (R.block j).coeff (Qz j) * (show ℂ from (R.block j).atom (Qz j)))
        =
      ∑ j ∈ Finset.range (k + 1),
        (R.block j).toFunLt (souzaAtomFamily G s p hs hp hp_top) z := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact (quasi_toFunLt_eq_coeff_mul_atom G s p hs hp hp_top
          (R.block j) (hQz j)).symm
    _ =
      ∑ j ∈ Finset.range (k + 1),
        (StandardAtomicRepresentation.canonicalStandardLpGridBlock
          G F s p hs hp hp_top f hf j).toFunLt
          (souzaAtomFamily G s p hs hp hp_top) z := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        rw [hblock j]
    _ = DiracApproximation.partialStandardSum G F p s f hf k z :=
      canonicalStandardBlock_range_sum_toFunLt_eq_partialStandardSum
        G F s p hs hp hp_top f hf k z

private theorem strictWeightedAncestorCoeffSum_canonicalStandard_bound
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (hblock : ∀ j, R.block j =
      StandardAtomicRepresentation.canonicalStandardLpGridBlock G F
        s p hs hp hp_top f hf j)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hpartial : ∀ (n : ℕ) (P : WeakGridSpace.LevelCell G.toWeakGridSpace n)
      {z : α}, z ∈ P.1 →
        ‖DiracApproximation.partialStandardSum G F p s f hf n z‖ ≤ M)
    (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    ‖strictWeightedAncestorCoeffSum G R Q‖ ≤ M := by
  classical
  cases k with
  | zero =>
      unfold strictWeightedAncestorCoeffSum
      simpa using hM0
  | succ n =>
      obtain ⟨z, hz⟩ := G.grid.partition_nonempty (n + 1) Q.1 Q.2
      have hex : ∀ m : ℕ,
          ∃ P : WeakGridSpace.LevelCell G.toWeakGridSpace m, z ∈ P.1 := by
        intro m
        have hzmem : z ∈ ⋃ t ∈ G.grid.grid.partitions m, t := by
          rw [G.grid.grid.covering m]
          trivial
        rcases Set.mem_iUnion₂.mp hzmem with ⟨P, hP, hzP⟩
        exact ⟨⟨P, hP⟩, hzP⟩
      choose Qz hQz using hex
      have hQzk : Qz (n + 1) = Q :=
        Subtype.ext (DiracApproximation.cell_eq_of_mem_of_mem G
          (Qz (n + 1)).2 Q.2 (hQz (n + 1)) hz)
      have hstrict_eq :
          strictWeightedAncestorCoeffSum G R Q =
            DiracApproximation.partialStandardSum G F p s f hf n z := by
        rw [← hQzk, strictWeightedAncestorCoeffSum_tower_eq G R Qz hQz]
        calc
          (∑ j ∈ Finset.range (n + 1),
              (R.block j).coeff (Qz j) * (show ℂ from (R.block j).atom (Qz j)))
              =
            ∑ j ∈ Finset.range (n + 1),
              (R.block j).toFunLt (souzaAtomFamily G s p hs hp hp_top) z := by
              refine Finset.sum_congr rfl ?_
              intro j _hj
              exact (quasi_toFunLt_eq_coeff_mul_atom G s p hs hp hp_top
                (R.block j) (hQz j)).symm
          _ =
            ∑ j ∈ Finset.range (n + 1),
              (StandardAtomicRepresentation.canonicalStandardLpGridBlock
                G F s p hs hp hp_top f hf j).toFunLt
                (souzaAtomFamily G s p hs hp hp_top) z := by
              refine Finset.sum_congr rfl ?_
              intro j _hj
              rw [hblock j]
          _ = DiracApproximation.partialStandardSum G F p s f hf n z :=
            canonicalStandardBlock_range_sum_toFunLt_eq_partialStandardSum
              G F s p hs hp hp_top f hf n z
      rw [hstrict_eq]
      exact hpartial n (Qz n) (hQz n)

private theorem norm_partialStandardSum_le_essBound
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ)
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    {M : ℝ} (hM0 : 0 ≤ M) (hMae : ∀ᵐ z ∂G.grid.μ, ‖f z‖ ≤ M)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {z : α} (hz : z ∈ Q.1) :
    ‖DiracApproximation.partialStandardSum G F p s f hf k z‖ ≤ M := by
  have h1 := DiracApproximation.claimA_standard G F f hf ⟨k, Q.1, Q.2⟩ hz
  rw [DiracApproximation.partialHaarSum_eq_partialStandardSum G F p s f hf] at h1
  have h2 : eLpNorm (Set.indicator Q.1 f) ∞ G.grid.μ ≤ ENNReal.ofReal M := by
    refine le_trans (eLpNorm_indicator_le f) ?_
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound hMae
  exact (ENNReal.ofReal_le_ofReal_iff hM0).1 (le_trans h1 h2)

private theorem exists_weighted_fouRepresentation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cfou : ℝ,
      0 ≤ Cfou ∧
      ∀ (f : α → ℂ) (M : ℝ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) f
          (x : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ M) →
        ∃ R : WeakGridSpace.LpGridRepresentation
            (souzaAtomFamily G s p hs hp hp_top)
            (x : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
            Cfou * WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q x ∧
          (∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            ‖weightedAncestorCoeffSum G R Q‖ ≤ M) ∧
          ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            ‖strictWeightedAncestorCoeffSum G R Q‖ ≤ M := by
  classical
  letI : DecidableEq (Set α) := Classical.decEq (Set α)
  haveI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hp_lt_top : p < ∞ := lt_top_iff_ne_top.mpr hp_top
  let H : UnbalancedHaarWavelet.HaarSystem (HaarRepresentation.GridOf G) :=
    Classical.choice
      (UnbalancedHaarWavelet.exists_haarSystem (HaarRepresentation.GridOf G))
  let F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G) :=
    { toHaarSystem := H
      alphaFunction := UnbalancedHaarWavelet.normalizedAlphaFunction
        (HaarRepresentation.GridOf G)
      alphaFunction_def := rfl }
  letI : DecidableEq F.Index := Classical.decEq F.Index
  obtain ⟨Cst, hCst_ne_top, hstandard_le⟩ :=
    StandardAtomicRepresentation.exists_standardRepresentationNorm_le_const_mul_souzaBesovNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p)
      (hp_top := hp_lt_top) (q := q)
  refine ⟨Cst.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro f M x hfrep hfM
  let A := souzaAtomFamily G s p hs hp hp_top
  let fFun : α → ℂ := ((x : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
  have hfMemLp : MemLp fFun p G.grid.μ := by
    simpa [fFun, GoodGridSpace.toWeakGridSpace] using
      (Lp.memLp (x : Lp ℂ p G.toWeakGridSpace.measure))
  have hfint : Integrable fFun G.grid.μ := hfMemLp.integrable (Fact.out : 1 ≤ p)
  have hM0 : 0 ≤ M := ae_norm_bound_nonneg G hfM
  have hstd :
      StandardAtomicRepresentation.standardRepresentationNorm G F
          s hs p hp_lt_top q fFun hfint ≠ ∞ ∧
        StandardAtomicRepresentation.standardRepresentationNorm G F
            s hs p hp_lt_top q fFun hfint ≤
          Cst * ENNReal.ofReal
            (WeakGridSpace.BesovishSpace.Norm_Costpq A q x) := by
    simpa [A, fFun, GoodGridSpace.toWeakGridSpace] using
      hstandard_le x fFun hfint Filter.EventuallyEq.rfl
  rcases hstd with ⟨hstd_ne_top, hstd_le⟩
  rcases StandardAtomicRepresentation.finite_standardRepresentationNorm_implies_memBesov_and_standardRepresentation
      (G := G) (F := F) (s := s) (hs := hs) (p := p)
      (hp_top := hp_lt_top) (q := q) fFun hfint hstd_ne_top with
    ⟨hfLp, xstd, Rstd, hxstdLp, hRstd_block, hRstd_fin, _hRstd_enn,
      hRstd_cost, _hxstd_cost⟩
  have hLp_eq : (xstd : Lp ℂ p G.toWeakGridSpace.measure) =
      (x : Lp ℂ p G.toWeakGridSpace.measure) := by
    have hto : hfLp.toLp fFun = (x : Lp ℂ p G.toWeakGridSpace.measure) := by
      change hfLp.toLp ((x : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =
        (x : Lp ℂ p G.toWeakGridSpace.measure)
      exact Lp.toLp_coeFn (x : Lp ℂ p G.toWeakGridSpace.measure) hfLp
    exact hxstdLp.trans hto
  let R : WeakGridSpace.LpGridRepresentation A
      (x : Lp ℂ p G.toWeakGridSpace.measure) :=
    { block := Rstd.block
      hasSum := hLp_eq ▸ Rstd.hasSum }
  have hR_block : ∀ j, R.block j =
      StandardAtomicRepresentation.canonicalStandardLpGridBlock G F
        s p hs hp hp_top fFun hfint j := fun j =>
    congrFun hRstd_block j
  have hR_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R :=
    hRstd_fin
  have hR_cost : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
      Cst.toReal * WeakGridSpace.BesovishSpace.Norm_Costpq A q x := by
    have hNx0 : 0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A q x :=
      WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg (A := A) (q := q)
        (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A q) x
    have h2 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hCst_ne_top ENNReal.ofReal_ne_top) hstd_le
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hNx0] at h2
    exact le_trans hRstd_cost h2
  have hMae : ∀ᵐ z ∂G.grid.μ, ‖fFun z‖ ≤ M := by
    have h1 : (fFun : α → ℂ) =ᵐ[G.grid.μ] f := by
      simpa [fFun, GoodGridSpace.toWeakGridSpace] using hfrep
    have h2 : ∀ᵐ z ∂G.grid.μ, ‖f z‖ ≤ M := by
      simpa [GoodGridSpace.toWeakGridSpace] using hfM
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1]
    exact hz2
  have hpartial : ∀ (n : ℕ) (P : WeakGridSpace.LevelCell G.toWeakGridSpace n)
      {z : α}, z ∈ P.1 →
        ‖DiracApproximation.partialStandardSum G F p s fFun hfint n z‖ ≤ M :=
    fun n P {z} hz => norm_partialStandardSum_le_essBound G F p s fFun hfint
      hM0 hMae P (z := z) hz
  have hR_tower : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G R Q‖ ≤ M := by
    intro k Q
    obtain ⟨z, hz⟩ := G.grid.partition_nonempty k Q.1 Q.2
    rw [weightedAncestorCoeffSum_canonicalStandard_eq_partialStandardSum
      G F s p hs hp hp_top fFun hfint R hR_block Q hz]
    exact hpartial k Q hz
  have hR_strict : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖strictWeightedAncestorCoeffSum G R Q‖ ≤ M :=
    strictWeightedAncestorCoeffSum_canonicalStandard_bound
      G F s p hs hp hp_top fFun hfint R hR_block hM0 hpartial
  exact ⟨R, hR_fin, hR_cost, hR_tower, hR_strict⟩

/--
Technical core of Proposition `mult33`.

Given two Souza-Besov representatives of smoothness `s`, together with
almost-everywhere `L∞` bounds, the pointwise product has a Souza-Besov
representative whose coefficient-cost gauge is controlled by the two mixed
terms

`|f|_{B^s_{p,q}} |g|∞ + |g|_{B^s_{p,q}} |f|∞`.

This is the formal home for the paper's two-block construction
`u₁ + u₂`, using canonical `(s,p)` Souza representations obtained from
Corollary `fou` and the tower estimates from Proposition `boup`.
-/
theorem exists_quasiAlgebra_product_representation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (_hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cprod : ℝ,
      0 ≤ Cprod ∧
      ∀ (f g : α → ℂ) (Mf Mg : ℝ)
        (xf xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) f
          (xf : Lp ℂ p G.toWeakGridSpace.measure) →
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ Mf) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ Mg) →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => f z * g z)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q y ≤
            Cprod *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                  (souzaAtomFamily G s p hs hp hp_top) q xf * Mg +
          WeakGridSpace.BesovishSpace.Norm_Costpq
                  (souzaAtomFamily G s p hs hp hp_top) q xg * Mf) := by
  obtain ⟨Cfou, hCfou0, hfou⟩ :=
    exists_weighted_fouRepresentation G s p q hs hp hp_top
  refine ⟨Cfou, hCfou0, ?_⟩
  intro f g Mf Mg xf xg hfrep hgrep hfM hgM
  let A := souzaAtomFamily G s p hs hp hp_top
  have hMf0 : 0 ≤ Mf := ae_norm_bound_nonneg G hfM
  have hMg0 : 0 ≤ Mg := ae_norm_bound_nonneg G hgM
  obtain ⟨Rf, hRffin, hRfcost, _htower_f, hstrict_f⟩ :=
    hfou f Mf xf hfrep hfM
  obtain ⟨Rg, hRgfin, hRgcost, htower_g, _hstrict_g⟩ :=
    hfou g Mg xg hgrep hgM
  obtain ⟨y, hyrep, hycost⟩ :=
    exists_quasi_product_of_tower_representations G s p q hs hp hp_top
      f g Mf Mg hMf0 hMg0 xf xg Rf Rg hfrep hgrep hRffin hRgfin
      htower_g hstrict_f
  refine ⟨y, hyrep, le_trans hycost ?_⟩
  let Nf := WeakGridSpace.BesovishSpace.Norm_Costpq A q xf
  let Ng := WeakGridSpace.BesovishSpace.Norm_Costpq A q xg
  have hleft :
      Mg * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf ≤
        Mg * (Cfou * Nf) :=
    mul_le_mul_of_nonneg_left hRfcost hMg0
  have hright :
      Mf * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg ≤
        Mf * (Cfou * Ng) :=
    mul_le_mul_of_nonneg_left hRgcost hMf0
  calc
    Mg * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf +
        Mf * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg
        ≤ Mg * (Cfou * Nf) + Mf * (Cfou * Ng) := add_le_add hleft hright
    _ = Cfou * (Nf * Mg + Ng * Mf) := by ring

/--
**Proposition `mult33` of the paper (Pointwise Multipliers III).**

For `0 < s < 1/p`, the class `B^s_{p,q} ∩ L∞` is closed under pointwise
multiplication.  More quantitatively, there is a constant `Cqa` depending only
on the grid and the exponents such that, whenever concrete functions `f` and
`g` represent Souza-Besov elements and are bounded almost everywhere by `Mf`
and `Mg`, the product has a Souza-Besov representative `y` and satisfies

`|fg|_B + |fg|∞ ≤ Cqa (|f|_B + Mf) (|g|_B + Mg)`.

The final almost-everywhere bound records the `|fg|∞ ≤ |f|∞ |g|∞` part.
-/
theorem souzaPointwiseMultipliersIII
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cqa : ℝ,
      0 ≤ Cqa ∧
      ∀ (f g : α → ℂ) (Mf Mg : ℝ)
        (xf xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) f
          (xf : Lp ℂ p G.toWeakGridSpace.measure) →
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ Mf) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ Mg) →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => f z * g z)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q y + Mf * Mg ≤
            Cqa *
              ((WeakGridSpace.BesovishSpace.Norm_Costpq
                    (souzaAtomFamily G s p hs hp hp_top) q xf + Mf) *
                (WeakGridSpace.BesovishSpace.Norm_Costpq
                    (souzaAtomFamily G s p hs hp hp_top) q xg + Mg)) ∧
          (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z * g z‖ ≤ Mf * Mg) := by
  classical
  obtain ⟨Cprod, hCprod0, hprod⟩ :=
    exists_quasiAlgebra_product_representation G s p q hs hs_lt_inv hp hp_top
  refine ⟨max Cprod 1, ?_, ?_⟩
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right Cprod 1)
  intro f g Mf Mg xf xg hfrep hgrep hfM hgM
  obtain ⟨y, hyrep, hynorm⟩ := hprod f g Mf Mg xf xg hfrep hgrep hfM hgM
  refine ⟨y, hyrep, ?_, ae_norm_mul_le_mul_bounds G hfM hgM⟩
  let A := souzaAtomFamily G s p hs hp hp_top
  let Nf : ℝ := WeakGridSpace.BesovishSpace.Norm_Costpq A q xf
  let Ng : ℝ := WeakGridSpace.BesovishSpace.Norm_Costpq A q xg
  let S : ℝ := Nf * Mg + Ng * Mf
  let P : ℝ := Mf * Mg
  let T : ℝ := (Nf + Mf) * (Ng + Mg)
  have hNf0 : 0 ≤ Nf :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
      (A := A) (q := q)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A q) xf
  have hNg0 : 0 ≤ Ng :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
      (A := A) (q := q)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A q) xg
  have hMf0 : 0 ≤ Mf := ae_norm_bound_nonneg G hfM
  have hMg0 : 0 ≤ Mg := ae_norm_bound_nonneg G hgM
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (mul_nonneg hNf0 hMg0) (mul_nonneg hNg0 hMf0)
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg hMf0 hMg0
  have hCprod_le : Cprod ≤ max Cprod 1 := le_max_left Cprod 1
  have hOne_le : (1 : ℝ) ≤ max Cprod 1 := le_max_right Cprod 1
  have hC0 : 0 ≤ max Cprod 1 :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) hOne_le
  have hSP_le_T : S + P ≤ T := by
    dsimp [S, P, T]
    nlinarith [mul_nonneg hNf0 hNg0]
  have hmixed :
      Cprod * S + P ≤ max Cprod 1 * (S + P) := by
    calc
      Cprod * S + P ≤ max Cprod 1 * S + max Cprod 1 * P := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hCprod_le hS0)
          (by
            calc
              P = (1 : ℝ) * P := by ring
              _ ≤ max Cprod 1 * P :=
                mul_le_mul_of_nonneg_right hOne_le hP0)
      _ = max Cprod 1 * (S + P) := by ring
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq A q y + Mf * Mg
        ≤ Cprod * S + P := by
          dsimp [A, Nf, Ng, S, P] at hynorm ⊢
          linarith
    _ ≤ max Cprod 1 * (S + P) := hmixed
    _ ≤ max Cprod 1 * T := mul_le_mul_of_nonneg_left hSP_le_T hC0
    _ = max Cprod 1 * ((Nf + Mf) * (Ng + Mg)) := rfl

end

end GoodGridSpace
