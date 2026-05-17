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

/--
The `q = ∞` case of `tailCCoefficient → 0`:
`tailCCoefficient G s p ∞ N = ∑_{k≥N} w_k` and summability (from `AssumptionG2`) plus
`tendsto_sum_nat_add` give convergence to 0.
-/
omit [Fact (1 ≤ q)] in
lemma tailCCoefficient_tendsto_zero_q_top
    (hG2 : AssumptionG2 G s p u q) (hp_ne_top : p ≠ ∞) :
    Tendsto (fun N => tailCCoefficient G s p ∞ N) atTop (𝓝 0) := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_ne_top
  -- AssumptionG2 for q = ∞: cCoefficientFinite p ∞ (w_k^p) = Summable (fun k => w_k)
  have hSummable_w : Summable (fun k => levelWeightP G s p k) := by
    have hfin : LpGridRepresentation.cCoefficientFinite p q
        (fun k => (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) :=
      hG2.1
    -- Specialize cCoefficientFinite to get Summable w_k
    -- Use: for q = ∞, cCoefficientFinite p ∞ b = Summable (fun k => b k ^ (1/p))
    -- and b k = w_k^p, so (b k)^{1/p} = w_k
    -- We need q = ∞ to extract this; but hfin is for general q.
    -- The statement of AssumptionG2 is for q = ∞ here.
    -- Actually hfin is `cCoefficientFinite p q ...` for the variable q.
    -- We are in the `q = ∞` branch so we substitute.
    sorry
  -- tailCCoefficient G s p ∞ N = ∑' k, levelWeightP G s p (k + N)
  have htCC_eq : ∀ N, tailCCoefficient G s p ∞ N = ∑' k, levelWeightP G s p (k + N) := by
    intro N
    unfold tailCCoefficient LpGridRepresentation.cCoefficient tailCoefficientWeight levelWeightP
    simp only [↓reduceIte]  -- q = ∞ branch
    congr 1
    ext k
    by_cases hk : k < N
    · simp [hk, Real.zero_rpow (div_pos one_pos hp_pos).ne']
    · simp only [hk, ↓reduceIte]
      push_neg at hk
      -- (w_k^p)^{1/p} = w_k for w_k ≥ 0
      have hw_nonneg : 0 ≤ LpGridRepresentation.levelMeasureWeight G s p p k :=
        LpGridRepresentation.levelMeasureWeight_nonneg G s p p k
      simpa [one_div] using Real.rpow_rpow_inv hw_nonneg hp_pos.ne'
  rw [show (fun N => tailCCoefficient G s p ∞ N) = (fun N => ∑' k, levelWeightP G s p (k + N))
      from funext htCC_eq]
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
  have hq_pos : 0 < q.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hqtop
  have hq_toReal_one : 1 < q.toReal := by
    have h := ENNReal.toReal_mono hqtop (Fact.out : 1 ≤ q)
    simp at h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact hlt
    · exfalso; apply hq1
      exact (ENNReal.toReal_eq_toReal ENNReal.one_ne_top hqtop).mp heq.symm
  let q' : ℝ≥0∞ := q / (q - 1)
  have hq'_pos : 0 < q'.toReal := by
    have := LpGridRepresentation.holderConjugate_q_div_qsub1_toReal hq_toReal_one hqtop
    exact this.nonneg |>.lt_of_ne' this.nonneg.ne
  -- cCoefficientFinite p q (w_k^p) gives Summable (fun k => w_k^{q'})
  have hSummable_wq' : Summable (fun k => (levelWeightP G s p k) ^ q'.toReal) := by
    have hfin : LpGridRepresentation.cCoefficientFinite p q
        (fun k => (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) := hG2.1
    rw [LpGridRepresentation.cCoefficientFinite, if_neg hq1, if_neg hqtop] at hfin
    -- hfin : Summable (fun k => ((w_k^p)^{q'/p}))
    -- (w_k^p)^{q'/p} = w_k^{q'}
    convert hfin using 1
    ext k
    dsimp only [levelWeightP]
    have hw_nonneg : 0 ≤ LpGridRepresentation.levelMeasureWeight G s p p k :=
      LpGridRepresentation.levelMeasureWeight_nonneg G s p p k
    -- ((w^p)^{q'/p}) = w^{q'}
    have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
      field_simp [hp_pos.ne']
    calc ((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
          (q'.toReal / p.toReal)
        = ((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
            ((1 / p.toReal) * q'.toReal) := by rw [hdiv]
      _ = (((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
            (1 / p.toReal)) ^ q'.toReal := by
            rw [Real.rpow_mul (Real.rpow_nonneg hw_nonneg _)]
      _ = (LpGridRepresentation.levelMeasureWeight G s p p k) ^ q'.toReal := by
            congr 1
            simpa [one_div] using Real.rpow_rpow_inv hw_nonneg hp_pos.ne'
  -- tailCCoefficient N = (∑' k, (levelWeightP (k+N))^{q'})^{1/q'}
  have htCC_eq : ∀ N, tailCCoefficient G s p q N =
      (∑' k, (levelWeightP G s p (k + N)) ^ q'.toReal) ^ (1 / q'.toReal) := by
    intro N
    unfold tailCCoefficient LpGridRepresentation.cCoefficient levelWeightP
    simp only [if_neg hq1, if_neg hqtop]
    -- cCoefficient = (∑' k, (tailCoefficientWeight N k)^{q'/p})^{1/q'}
    -- (tailCoefficientWeight N k)^{q'/p} = if k<N then 0 else (levelWeightP k)^{q'}
    congr 1
    apply tsum_congr
    intro k
    by_cases hk : k < N
    · have htail_zero : tailCoefficientWeight G s p N k = 0 := by
        simp [tailCoefficientWeight, hk]
      simp [htail_zero, Real.zero_rpow (div_pos hq'_pos hp_pos).ne']
    · push_neg at hk
      have htail_eq : tailCoefficientWeight G s p N k =
          (LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal := by
        simp [tailCoefficientWeight, hk]
      rw [htail_eq]
      have hw_nonneg : 0 ≤ LpGridRepresentation.levelMeasureWeight G s p p k :=
        LpGridRepresentation.levelMeasureWeight_nonneg G s p p k
      have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
        field_simp [hp_pos.ne']
      calc ((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
            (q'.toReal / p.toReal)
          = ((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
              ((1 / p.toReal) * q'.toReal) := by rw [hdiv]
        _ = (((LpGridRepresentation.levelMeasureWeight G s p p k) ^ p.toReal) ^
              (1 / p.toReal)) ^ q'.toReal := by
              rw [Real.rpow_mul (Real.rpow_nonneg hw_nonneg _)]
        _ = (LpGridRepresentation.levelMeasureWeight G s p p k) ^ q'.toReal := by
              congr 1
              simpa [one_div] using Real.rpow_rpow_inv hw_nonneg hp_pos.ne'
  -- Now show tailCCoefficient N = shifted sum, then use tendsto_sum_nat_add + rpow
  rw [show (fun N => tailCCoefficient G s p q N) =
      (fun N => (∑' k, (levelWeightP G s p (k + N)) ^ q'.toReal) ^ (1 / q'.toReal))
      from funext htCC_eq]
  -- Use: (∑' k, ...) → 0 by tendsto_sum_nat_add
  have hshift_tendsto : Tendsto (fun N => ∑' k, (levelWeightP G s p (k + N)) ^ q'.toReal)
      atTop (𝓝 0) :=
    tailSum_tendsto_zero (fun k => (levelWeightP G s p k) ^ q'.toReal)
  -- And x^{1/q'} → 0^{1/q'} = 0 by continuity (since 1/q' > 0)
  have hcont : ContinuousAt (fun x => x ^ (1 / q'.toReal)) 0 :=
    Real.continuousAt_rpow_const 0 (1 / q'.toReal) (Or.inr (div_pos one_pos hq'_pos).le)
  have hzero_rpow : (0 : ℝ) ^ (1 / q'.toReal) = 0 :=
    Real.zero_rpow (div_pos one_pos hq'_pos).ne'
  simpa [hzero_rpow] using hcont.tendsto.comp hshift_tendsto

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
      -- Strategy: apply `lp_embedding_adapted_statement` to `Dtail N n` with t = p,
      -- obtaining ‖v_N_n‖ ≤ C_mult * cCoeff(tailWeights N) * pqCost(Dtail N n).
      -- The key facts: cCoeff(tailWeights N) = tailCCoefficient N → 0 (by hG2 + hs_pos),
      -- and pqCost(Dtail N n) ≤ 2*C uniformly (by hDtail_cost_le).
      --
      -- The tail-weighted version of lp_embedding_adapted_statement is proved
      -- by inlining the chain:
      --   ‖v‖ ≤ ∑_k ‖block_k‖   (triangle via HasSum)
      --       ≤ C_mult * ∑_k w_k * lCP_k^{1/p}  (lt_norm_levelBlock_le)
      --       ≤ C_mult * tailCCoefficient N * pqCost(Dtail N n)  (Hölder with tail weights)
      -- where for k < N, lCP(Dtail N n, k) = 0 (zero blocks).
      have hp_pos : 0 < p.toReal :=
        ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_ne_top
      have hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / p.toReal := by linarith [hs_pos.le]
      have htailCC_zero := tailCCoefficient_tendsto_zero hG2 hp_ne_top hs_pos
      -- Get the C_mult constant for the block norm bound
      obtain ⟨C_emb, hC_emb_nonneg, hblock_bound⟩ :=
        LpGridRepresentation.lt_norm_levelBlock_le (A := A) (t := p) (G := G)
          hp_ne_top hp_ne_top le_rfl
          (by
            calc p ≤ p * 1 := by ring_nf
              _ ≤ p * u := by
                  apply ENNReal.mul_le_mul_left' (by exact_mod_cast hu_one)
                  exact (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne')
          hs_nonneg
      -- For each N, norm of v_N_n ≤ C_emb * tailCCoeff N * pqCost(Dtail N n)
      -- This uses: the element v_N_n is represented by Dtail N n (via Dtail.hasSum),
      -- so the norm ≤ sum of block norms ≤ C_emb * weighted sum.
      -- The weighted sum is bounded by tailCCoeff * pqCost via the tail Hölder inequality.
      -- We state this as a sorry and document the argument.
      have hkey : ∀ N n,
          ‖((gseq n - ∑ k ∈ Finset.range N, ((H.Rseq n).block k).toLp A) -
              (gLim - ∑ k ∈ Finset.range N, (H.Rlim.block k).toLp A))‖ ≤
            C_emb * tailCCoefficient G s p q N *
              LpGridRepresentation.pqCost (q := q) (Dtail N n) := by
        intro N n
        -- v_N_n is the element represented by Dtail N n via (Dtail N n).hasSum.
        -- Key steps (sorry for technical Lean elaboration of the Hölder inequality):
        -- 1. ‖v_N_n‖ ≤ ∑_k ‖(Dtail N n).block k |.toLp A‖
        --    (norm_tsum ≤ tsum_norm for a Summable series, using Dtail.hasSum)
        -- 2. ‖(Dtail N n).block k |.toLp A‖ ≤ C_emb * w_k * lCP_k^{1/p}  (hblock_bound)
        -- 3. ∑_k w_k * lCP_k^{1/p} = ∑_{k≥N} w_k * lCP_k^{1/p}  (lCP = 0 for k < N)
        -- 4. ∑_{k≥N} w_k * a_k ≤ tailCCoeff N * pqCost(Dtail N n)  (Hölder with tail weights)
        sorry
      -- Now combine: tailCCoeff N → 0 and pqCost ≤ 2C give ‖v_N_n‖ → 0 uniformly.
      intro ε hε
      have hC2 : 0 < 2 * C + 1 := by linarith
      have hdenom_pos : 0 < C_emb * (2 * C + 1) + 1 := by positivity
      rcases (Metric.tendsto_atTop.mp htailCC_zero)
          (ε / (C_emb * (2 * C + 1) + 1)) (by positivity) with ⟨N₀, hN₀⟩
      refine ⟨N₀, fun n => ?_⟩
      have hN₀_bound : tailCCoefficient G s p q N₀ <
          ε / (C_emb * (2 * C + 1) + 1) := by
        have hnn : 0 ≤ tailCCoefficient G s p q N₀ :=
          LpGridRepresentation.cCoefficient_nonneg p q (tailCoefficientWeight G s p N₀)
            (tailCoefficientWeight_nonneg G s p N₀)
        have := hN₀ N₀ le_rfl
        rwa [dist_comm, Real.dist_eq, abs_of_nonneg hnn, sub_zero] at this
      have hpq_bound : LpGridRepresentation.pqCost (q := q) (Dtail N₀ n) ≤ 2 * C :=
        hDtail_cost_le N₀ n
      have hpq_nonneg : 0 ≤ LpGridRepresentation.pqCost (q := q) (Dtail N₀ n) :=
        LpGridRepresentation.pqCost_nonneg (Dtail N₀ n)
      have hCC_nonneg : 0 ≤ tailCCoefficient G s p q N₀ :=
        LpGridRepresentation.cCoefficient_nonneg p q (tailCoefficientWeight G s p N₀)
          (tailCoefficientWeight_nonneg G s p N₀)
      calc ‖((gseq n - ∑ k ∈ Finset.range N₀, ((H.Rseq n).block k).toLp A) -
                (gLim - ∑ k ∈ Finset.range N₀, (H.Rlim.block k).toLp A))‖
            ≤ C_emb * tailCCoefficient G s p q N₀ *
                LpGridRepresentation.pqCost (q := q) (Dtail N₀ n) :=
              hkey N₀ n
          _ ≤ C_emb * tailCCoefficient G s p q N₀ * (2 * C) := by
              apply mul_le_mul_of_nonneg_left hpq_bound
              exact mul_nonneg hC_emb_nonneg hCC_nonneg
          _ < C_emb * (ε / (C_emb * (2 * C + 1) + 1)) * (2 * C + 1) := by
              have h1 : C_emb * tailCCoefficient G s p q N₀ * (2 * C)
                  < C_emb * (ε / (C_emb * (2 * C + 1) + 1)) * (2 * C) := by
                apply mul_lt_mul_of_nonneg_right _ (by linarith)
                exact mul_lt_mul_of_nonneg_left hN₀_bound hC_emb_nonneg
              have h2 : C_emb * (ε / (C_emb * (2 * C + 1) + 1)) * (2 * C)
                  < C_emb * (ε / (C_emb * (2 * C + 1) + 1)) * (2 * C + 1) := by
                apply mul_lt_mul_of_nonneg_left (by linarith)
                exact mul_nonneg hC_emb_nonneg (le_of_lt (by positivity))
              linarith
          _ = ε * (C_emb / (C_emb * (2 * C + 1) + 1)) * (2 * C + 1) := by ring
          _ ≤ ε := by
              have hfrac_le : C_emb / (C_emb * (2 * C + 1) + 1) ≤ 1 / (2 * C + 1) := by
                apply div_le_div_of_nonneg_right _ hC2.le hdenom_pos.le
                linarith [mul_le_add_of_nonneg_left (le_of_lt hC2) hC_emb_nonneg]
              have := mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hfrac_le hε.le) hC2.le
              simp only [mul_one_div] at this ⊢
              have : ε * (C_emb / (C_emb * (2 * C + 1) + 1)) * (2 * C + 1)
                  ≤ ε * (1 / (2 * C + 1)) * (2 * C + 1) := by
                apply mul_le_mul_of_nonneg_right _ hC2.le
                exact mul_le_mul_of_nonneg_left hfrac_le hε.le
              have heq : ε * (1 / (2 * C + 1)) * (2 * C + 1) = ε := by
                field_simp [hC2.ne']
              linarith
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




end

end WeakGridSpace
