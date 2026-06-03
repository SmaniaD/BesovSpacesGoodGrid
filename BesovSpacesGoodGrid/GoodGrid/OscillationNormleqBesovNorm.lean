import BesovSpacesGoodGrid.GoodGrid.FiniteStandardNormimpliesBesov
import BesovSpacesGoodGrid.GoodGrid.MeanOscillationNorm

/-!
# Oscillation norm controlled by the standard representation norm

This file records the comparison corresponding to inequality `(in4)` in the
preprint.  The intended estimate says that the mean-oscillation gauge is
controlled by the standard atomic coefficient gauge.  The proof is organized in
the same two pieces as the manuscript:

* the `L^p` part of the oscillation norm is controlled by the atomic Besov
  gauge, via the existing `L^p` embedding estimate;
* the oscillation seminorm is controlled by the tail of an almost-minimizing
  standard atomic representation, followed by the geometric convolution
  estimate.

The final theorem packages these two estimates and also returns the `L^p`
membership supplied by the finite-standard-norm theorem.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace MeanOscillation

/--
A finite `ENNReal` upper bound on the extended coefficient cost gives the same
real upper bound for `pqCost`.

This local helper mirrors the private conversion lemma used in the weak-grid
completeness machinery.
-/
theorem pqCost_le_of_pqCostENNReal_le
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {A : WeakGridSpace.AtomFamily G s p u} {g : Lp ℂ p G.measure} {C : ℝ}
    (R : WeakGridSpace.LpGridRepresentation A g)
    (hENNReal : WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R ≤
      ENNReal.ofReal C)
    (hC : 0 ≤ C) :
    WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤ C := by
  have hfin :
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R :=
    WeakGridSpace.LpGridRepresentation.finitePQCost_of_pqCostENNReal_le
      (G := G) (s := s) (p := p) (u := u) (q := q) (A := A) R
      (Fact.out : 1 ≤ q) hENNReal
  by_cases hq : q = ∞
  · simp only [WeakGridSpace.LpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [WeakGridSpace.LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hENNReal
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨k, rfl⟩
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp
      ((le_sSup (Set.mem_range.mpr ⟨k, rfl⟩)).trans hENNReal)
  · simp only [WeakGridSpace.LpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hfin
    simp only [WeakGridSpace.LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hENNReal
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have h_nonneg : ∀ k, 0 ≤ R.levelCoeffPower k ^ (q.toReal / p.toReal) :=
      fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
    rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg hfin,
        ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg h_nonneg)
          (div_nonneg zero_le_one hq_pos.le)] at hENNReal
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp hENNReal

/-- The zero `LpGridRepresentation` has zero coefficient cost. -/
private theorem zero_lpgGridRepresentation_pqCost
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A : WeakGridSpace.AtomFamily G s p u) :
    let R : WeakGridSpace.LpGridRepresentation A (0 : Lp ℂ p G.measure) :=
      { block := fun k => WeakGridSpace.LevelBlock.zero A k
        hasSum := by simp }
    WeakGridSpace.LpGridRepresentation.pqCost (q := q) R = 0 := by
  classical
  intro R
  have hp_pos : 0 < p.toReal :=
    (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  have hp_inv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
  have hzero : ∀ k, R.levelCoeffPower k = 0 := by
    intro k
    unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
    simp [R, WeakGridSpace.LevelBlock.zero, Real.zero_rpow hp_pos.ne']
  by_cases hq : q = ∞
  · simp [WeakGridSpace.LpGridRepresentation.pqCost, hq, hzero,
      Real.zero_rpow hp_inv_pos.ne']
  · have hq_zero_ne : q ≠ 0 :=
      ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ q))
    have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq_zero_ne hq
    have hpow_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
    have hq_inv_pos : 0 < q.toReal⁻¹ := inv_pos.mpr hq_pos
    simp [WeakGridSpace.LpGridRepresentation.pqCost, hq, hzero,
      Real.zero_rpow hpow_pos.ne', Real.zero_rpow hq_inv_pos.ne']

/--
Souza-Besov elements admit almost-minimizing atomic representations.

This is the Lean version of the manuscript's sentence saying that, for every
`ε > 0`, one may choose a Besov representation whose coefficient cost is within
`ε` of the Besov gauge.  The statement is additive, which is the form supplied
by the abstract infimum lemma; the usual multiplicative `(1 + ε)` version
follows from this by a routine case split on whether the gauge vanishes.
-/
theorem exists_souzaBesovSpace_representation_cost_lt_norm_add
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (g : SouzaBesovSpace G s p q hs hp hp_top) {ε : ℝ} (hε : 0 < ε) :
    ∃ R :
        WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (g : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R <
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q g + ε := by
  simpa [SouzaBesovSpace] using
    (WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add
      (A := souzaAtomFamily G s p hs hp hp_top) (q := q)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations
        (A := souzaAtomFamily G s p hs hp hp_top) q)
      g hε)

/--
Multiplicative almost-minimizing form away from the zero-gauge case.

When the Besov gauge of `g` is positive, the additive approximation lemma gives
a representation with cost at most `(1 + ε)` times that gauge.  This is the
form used in the paper's displayed estimate.
-/
theorem exists_souzaBesovSpace_representation_cost_le_one_add_mul_norm
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (g : SouzaBesovSpace G s p q hs hp hp_top) {ε : ℝ} (hε : 0 < ε)
    (hg_pos :
      0 <
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs hp hp_top) q g) :
    ∃ R :
        WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (g : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
          (1 + ε) *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q g := by
  let N : ℝ :=
    WeakGridSpace.BesovishSpace.Norm_Costpq
      (souzaAtomFamily G s p hs hp hp_top) q g
  have hδ : 0 < ε * N := mul_pos hε (by simpa [N] using hg_pos)
  rcases exists_souzaBesovSpace_representation_cost_lt_norm_add
      (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
      (q := q) g hδ with
    ⟨R, hRfin, hRlt⟩
  refine ⟨R, hRfin, ?_⟩
  calc
    WeakGridSpace.LpGridRepresentation.pqCost (q := q) R
        ≤ N + ε * N := le_of_lt (by simpa [N] using hRlt)
    _ = (1 + ε) * N := by ring
    _ =
          (1 + ε) *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q g := by
        rfl

/--
Full multiplicative almost-minimizing representation.

This is the exact formal version of the preprint's displayed choice of
representation with cost bounded by `(1 + ε)` times the Besov gauge.
-/
theorem exists_souzaBesovSpace_representation_cost_le_one_add_mul_norm'
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (g : SouzaBesovSpace G s p q hs hp hp_top) {ε : ℝ} (hε : 0 < ε) :
    ∃ R :
        WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (g : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
          (1 + ε) *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q g := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let N : ℝ := WeakGridSpace.BesovishSpace.Norm_Costpq A q g
  rcases lt_or_eq_of_le
      (WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
        (A := A) (q := q)
        (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := A) q) g) with
    hN_pos | hN_zero
  · simpa [A, N] using
      exists_souzaBesovSpace_representation_cost_le_one_add_mul_norm
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
        (q := q) g hε hN_pos
  · have hCco :
        WeakGridSpace.LpGridRepresentation.cCoefficientFinite p q
          (fun k => (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s p p k) ^ p.toReal) :=
      (souza_assumptionG2 G s p q hs hp hp_top).1
    have hg_zero : g = 0 :=
      WeakGridSpace.BesovishSpace.eq_zero_of_Norm_Costpq_eq_zero
        (A := A) (q := q) hp_top hCco
        (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := A) q)
        (by simpa [A, N] using hN_zero.symm)
    subst g
    let R : WeakGridSpace.LpGridRepresentation A (0 : Lp ℂ p G.toWeakGridSpace.measure) :=
      { block := fun k => WeakGridSpace.LevelBlock.zero A k
        hasSum := by simp }
    refine ⟨R, ?_, ?_⟩
    · have hp_pos : 0 < p.toReal :=
        (ENNReal.toReal_pos_iff_ne_top p).2 hp_top
      have hp_inv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
      have hzero : ∀ k, R.levelCoeffPower k = 0 := by
        intro k
        unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
        simp [R, WeakGridSpace.LevelBlock.zero, Real.zero_rpow hp_pos.ne']
      by_cases hq : q = ∞
      · simp [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, hzero,
          Real.zero_rpow hp_inv_pos.ne']
      · have hq_zero_ne : q ≠ 0 :=
          ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ q))
        have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq_zero_ne hq
        have hpow_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
        simp [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, hzero,
          Real.zero_rpow hpow_pos.ne']
    · have hcost : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R = 0 := by
        simpa [R, A] using zero_lpgGridRepresentation_pqCost (A := A) (q := q)
      rw [hcost]
      exact mul_nonneg (by linarith)
        (WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
          (A := souzaAtomFamily G s p hs hp hp_top) (q := q)
          (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations
            (A := souzaAtomFamily G s p hs hp hp_top) q)
          (0 : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q))

/--
Finite standard representation norm supplies a Souza-Besov element.

This packages the canonical standard block sequence as an abstract
`LpGridRepresentation` with finite coefficient cost.  It is the bridge between
the concrete standard coefficient gauge `N_st(f)` and the abstract Besov
machinery used by the embedding theorems.
-/
theorem exists_souzaBesovSpace_of_standardRepresentationNorm_ne_top
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (hN :
      StandardAtomicRepresentation.standardRepresentationNorm
        G F s hs p hp_top q f hf ≠ ∞) :
    ∃ hfLp : MemLp f p G.grid.μ,
      ∃ g : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top),
        (g : Lp ℂ p G.toWeakGridSpace.measure) = hfLp.toLp f := by
  classical
  rcases
    StandardAtomicRepresentation.finite_standardRepresentationNorm_implies_memLp_and_hasSum
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q)
      f hf hN with
    ⟨hfLp, hstandard_sum⟩
  have hfin :
      WeakGridSpace.AbstractFinitePQCost
        (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) (q := q)
        (StandardAtomicRepresentation.canonicalStandardBlockSeq
          G F s hs p hp_top f hf) :=
    StandardAtomicRepresentation.abstractFinitePQCost_canonicalStandardBlockSeq_of_standardRepresentationNorm_ne_top
        (G := G) (F := F) (s := s) (hs := hs) (p := p)
        (hp_top := hp_top) (q := q) f hf hN
  let R :
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
        (hfLp.toLp f) :=
    { block :=
        StandardAtomicRepresentation.canonicalStandardBlockSeq
          G F s hs p hp_top f hf
      hasSum := hstandard_sum }
  have hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R := by
    simpa [R, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.AbstractFinitePQCost,
      WeakGridSpace.blockLvlCoeff_eq_levelCoeffPower] using hfin
  have hmem :
      hfLp.toLp f ∈ SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top) := by
    change
      WeakGridSpace.MemBesovishCoeffCost
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q (hfLp.toLp f)
    exact ⟨R, by simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost] using hRfin⟩
  exact ⟨hfLp, ⟨hfLp.toLp f, hmem⟩, rfl⟩

/--
The canonical standard representation has real coefficient cost bounded by
the standard coefficient gauge.

This is the cost-refined version of
`exists_souzaBesovSpace_of_standardRepresentationNorm_ne_top`: the Souza-Besov
element is represented by the actual canonical standard blocks, and the
abstract real cost of that representation is no larger than `N_st(f)`.
-/
theorem exists_souzaBesovSpace_representation_of_standardRepresentationNorm_ne_top
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (hN :
      StandardAtomicRepresentation.standardRepresentationNorm
        G F s hs p hp_top q f hf ≠ ∞) :
    ∃ hfLp : MemLp f p G.grid.μ,
      ∃ g : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top),
        ∃ R :
          WeakGridSpace.LpGridRepresentation
            (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
            (g : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
            (g : Lp ℂ p G.toWeakGridSpace.measure) = hfLp.toLp f ∧
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
                (StandardAtomicRepresentation.standardRepresentationNorm
                  G F s hs p hp_top q f hf).toReal := by
  classical
  rcases
    StandardAtomicRepresentation.finite_standardRepresentationNorm_implies_memLp_and_hasSum
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q)
      f hf hN with
    ⟨hfLp, hstandard_sum⟩
  let R₀ :
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
        (hfLp.toLp f) :=
    { block :=
        StandardAtomicRepresentation.canonicalStandardBlockSeq
          G F s hs p hp_top f hf
      hasSum := hstandard_sum }
  have hRenn_eq :
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R₀ =
        StandardAtomicRepresentation.standardRepresentationNorm
          G F s hs p hp_top q f hf := by
    by_cases hq : q = ∞
    · simp [WeakGridSpace.LpGridRepresentation.pqCostENNReal,
        StandardAtomicRepresentation.standardRepresentationNorm, hq, R₀,
        WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        StandardAtomicRepresentation.standardBlockCoeffPower,
        StandardAtomicRepresentation.canonicalStandardBlockSeq]
    · simp [WeakGridSpace.LpGridRepresentation.pqCostENNReal,
        StandardAtomicRepresentation.standardRepresentationNorm, hq, R₀,
        WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        StandardAtomicRepresentation.standardBlockCoeffPower,
        StandardAtomicRepresentation.canonicalStandardBlockSeq]
  have hRenn_le :
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R₀ ≤
        ENNReal.ofReal
          (StandardAtomicRepresentation.standardRepresentationNorm
            G F s hs p hp_top q f hf).toReal := by
    rw [hRenn_eq, ENNReal.ofReal_toReal hN]
  have hRcost_le :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R₀ ≤
        (StandardAtomicRepresentation.standardRepresentationNorm
          G F s hs p hp_top q f hf).toReal :=
    pqCost_le_of_pqCostENNReal_le
      (R := R₀) hRenn_le ENNReal.toReal_nonneg
  have hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R₀ :=
    WeakGridSpace.LpGridRepresentation.finitePQCost_of_pqCostENNReal_le
      R₀ (Fact.out : 1 ≤ q) hRenn_le
  have hmem :
      hfLp.toLp f ∈ SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top) := by
    change
      WeakGridSpace.MemBesovishCoeffCost
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q (hfLp.toLp f)
    exact ⟨R₀, by simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost] using hRfin⟩
  refine ⟨hfLp, ⟨hfLp.toLp f, hmem⟩, ?_⟩
  let R :
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
        ((⟨hfLp.toLp f, hmem⟩ :
          SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure) := R₀
  exact ⟨R, by simpa [R] using hRfin, rfl, by simpa [R] using hRcost_le⟩

/--
The `L^p` term in the mean-oscillation norm is bounded by the standard atomic
coefficient gauge.

This is the formal counterpart of the manuscript's use of Proposition `lp`:
after viewing the standard atomic expansion as a Souza-Besov representation,
the existing `L^p` embedding estimate bounds `‖f‖_p` by the representation
cost, and hence by the standard gauge.
-/
theorem exists_lpnorm_term_le_const_mul_standardRepresentationNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ),
        StandardAtomicRepresentation.standardRepresentationNorm
            G F s hs p hp_top q f hf ≠ ∞ →
          (G.grid.μ Set.univ) ^ (-s) * eLpNorm f p G.grid.μ ≤
            C *
              StandardAtomicRepresentation.standardRepresentationNorm
                G F s hs p hp_top q f hf := by
  classical
  let K : ℝ :=
    ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
      WeakGridSpace.LpGridRepresentation.cCoefficient p q
        (fun k =>
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s p p k) ^ p.toReal)
  let μI : ℝ := (G.grid.μ Set.univ).toReal
  refine ⟨ENNReal.ofReal (μI ^ (-s) * K), ENNReal.ofReal_ne_top, ?_⟩
  intro f hf hN
  rcases exists_souzaBesovSpace_representation_of_standardRepresentationNorm_ne_top
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top)
      (q := q) f hf hN with
    ⟨hfLp, g, R, hRfin, hg_eq, hRcost⟩
  have hCco :
      WeakGridSpace.LpGridRepresentation.cCoefficientFinite p q
        (fun k =>
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s p p k) ^ p.toReal) :=
    (souza_assumptionG2 G s p q hs Fact.out (ne_of_lt hp_top)).1
  have ht_le_pu : p ≤ p * ∞ := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * ∞ := mul_le_mul_right le_top p
  have hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / p.toReal := by
    linarith [hs.le]
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (by positivity)
      (WeakGridSpace.LpGridRepresentation.cCoefficient_nonneg p q
        (fun k =>
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s p p k) ^ p.toReal)
        (fun k => Real.rpow_nonneg
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg
            G.toWeakGridSpace s p p k) _))
  have hg_ae :
      ((g : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =ᵐ[G.grid.μ] f := by
    rw [hg_eq]
    exact MemLp.coeFn_toLp hfLp
  have heLp_toReal :
      (eLpNorm ((g : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
          p G.grid.μ).toReal =
        (eLpNorm f p G.grid.μ).toReal :=
    congrArg ENNReal.toReal (MeasureTheory.eLpNorm_congr_ae hg_ae)
  have hNorm_le_cost :
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q g ≤
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
      (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
      (q := q) g R hRfin
  have hLp_real :
      (eLpNorm f p G.grid.μ).toReal ≤ K *
        (StandardAtomicRepresentation.standardRepresentationNorm
          G F s hs p hp_top q f hf).toReal := by
    calc
      (eLpNorm f p G.grid.μ).toReal
          =
            (eLpNorm ((g : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
              p G.grid.μ).toReal := heLp_toReal.symm
      _ ≤ K *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q g := by
          simpa [K, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid] using
            WeakGridSpace.BesovishSpace.lp_norm_le_const_mul_Norm_Costpq
              (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
              (q := q) (t := p)
              (hp_top := ne_of_lt hp_top) (ht_top := ne_of_lt hp_top)
              (hp_le_t := le_rfl) (ht_le_pu := ht_le_pu)
              (hs_nonneg := hs_nonneg) (hCco_fin := hCco)
              (hA :=
                WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations
                  (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q)
              g
      _ ≤ K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
          mul_le_mul_of_nonneg_left hNorm_le_cost hK_nonneg
      _ ≤ K *
            (StandardAtomicRepresentation.standardRepresentationNorm
              G F s hs p hp_top q f hf).toReal :=
          mul_le_mul_of_nonneg_left hRcost hK_nonneg
  have hμ_pos : 0 < G.grid.μ Set.univ :=
    G.grid.positive_measure 0 Set.univ
      (by simp [G.grid.grid.first_partition_eq_univ])
  letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ :=
    MeasureTheory.measure_ne_top G.grid.μ Set.univ
  have hμ_toReal_pos : 0 < μI := by
    simpa [μI] using ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
  have hμ_toReal_pos' : 0 < (G.grid.μ Set.univ).toReal := by
    simpa [μI] using hμ_toReal_pos
  have hμpow_nonneg : 0 ≤ μI ^ (-s) :=
    Real.rpow_nonneg hμ_toReal_pos.le _
  have hμpow_eq : ENNReal.ofReal (μI ^ (-s)) = (G.grid.μ Set.univ) ^ (-s) := by
    change ENNReal.ofReal ((G.grid.μ Set.univ).toReal ^ (-s)) =
      (G.grid.μ Set.univ) ^ (-s)
    rw [← ENNReal.ofReal_rpow_of_pos hμ_toReal_pos',
      ENNReal.ofReal_toReal hμ_ne_top]
  have heLp_eq :
      ENNReal.ofReal (eLpNorm f p G.grid.μ).toReal =
        eLpNorm f p G.grid.μ :=
    ENNReal.ofReal_toReal hfLp.eLpNorm_ne_top
  have hreal :
      μI ^ (-s) * (eLpNorm f p G.grid.μ).toReal ≤
        μI ^ (-s) * K *
          (StandardAtomicRepresentation.standardRepresentationNorm
            G F s hs p hp_top q f hf).toReal := by
    calc
      μI ^ (-s) * (eLpNorm f p G.grid.μ).toReal
          ≤ μI ^ (-s) *
              (K *
                (StandardAtomicRepresentation.standardRepresentationNorm
                  G F s hs p hp_top q f hf).toReal) :=
            mul_le_mul_of_nonneg_left hLp_real hμpow_nonneg
      _ =
          μI ^ (-s) * K *
            (StandardAtomicRepresentation.standardRepresentationNorm
              G F s hs p hp_top q f hf).toReal := by ring
  calc
    (G.grid.μ Set.univ) ^ (-s) * eLpNorm f p G.grid.μ
        =
          ENNReal.ofReal (μI ^ (-s) * (eLpNorm f p G.grid.μ).toReal) := by
        rw [← hμpow_eq, ← heLp_eq]
        rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
        exact (ENNReal.ofReal_mul hμpow_nonneg).symm
    _ ≤
          ENNReal.ofReal
            (μI ^ (-s) * K *
              (StandardAtomicRepresentation.standardRepresentationNorm
                G F s hs p hp_top q f hf).toReal) :=
        ENNReal.ofReal_le_ofReal hreal
    _ =
          ENNReal.ofReal (μI ^ (-s) * K) *
            StandardAtomicRepresentation.standardRepresentationNorm
              G F s hs p hp_top q f hf := by
        rw [← ENNReal.ofReal_toReal hN]
        rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
        rw [← ENNReal.ofReal_mul (mul_nonneg hμpow_nonneg hK_nonneg)]

/--
The oscillation seminorm is bounded by the standard atomic coefficient gauge.

This is the discrete convolution estimate from the preprint.  Given an
almost-minimizing representation, the part of the atomic series above a cell
level `k₀` bounds the local oscillation on that cell.  Summing over cells and
then over levels gives convolution with the geometric kernel
`λ₂^{s n}`, whose sum is bounded by `(1 - λ₂^s)⁻¹`.
-/
theorem exists_oscillationSeminorm_le_const_mul_standardRepresentationNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ),
        StandardAtomicRepresentation.standardRepresentationNorm
            G F s hs p hp_top q f hf ≠ ∞ →
          oscillationSeminorm G s p q f ≤
            C *
              StandardAtomicRepresentation.standardRepresentationNorm
                G F s hs p hp_top q f hf := by
  sorry

/--
Finite standard representation norm forces membership in `L^p` and controls
the full mean-oscillation norm.

This is the packaged comparison
`N_osc(f) ≤ C N_st(f)`.  The proof is just bookkeeping once the two analytic
pieces above are available: the full mean-oscillation norm is the sum of the
`L^p` term and the oscillation seminorm.
-/
theorem exists_meanOscillationNorm_le_const_mul_standardRepresentationNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ),
        StandardAtomicRepresentation.standardRepresentationNorm
            G F s hs p hp_top q f hf ≠ ∞ →
          ∃ _hfLp : MemLp f p G.grid.μ,
            meanOscillationNorm G s p q f ≤
              C *
                StandardAtomicRepresentation.standardRepresentationNorm
                  G F s hs p hp_top q f hf := by
  classical
  rcases exists_lpnorm_term_le_const_mul_standardRepresentationNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q) with
    ⟨CLp, hCLp_fin, hLp_le⟩
  rcases exists_oscillationSeminorm_le_const_mul_standardRepresentationNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q) with
    ⟨Cosc, hCosc_fin, hosc_le⟩
  refine ⟨CLp + Cosc, ENNReal.add_ne_top.mpr ⟨hCLp_fin, hCosc_fin⟩, ?_⟩
  intro f hf hN
  rcases StandardAtomicRepresentation.finite_standardRepresentationNorm_implies_memLp_and_hasSum
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q)
      f hf hN with
    ⟨hfLp, _hstandard_sum⟩
  refine ⟨hfLp, ?_⟩
  calc
    meanOscillationNorm G s p q f
        =
          (G.grid.μ Set.univ) ^ (-s) * eLpNorm f p G.grid.μ +
            oscillationSeminorm G s p q f := rfl
    _ ≤
          CLp *
              StandardAtomicRepresentation.standardRepresentationNorm
                G F s hs p hp_top q f hf +
            Cosc *
              StandardAtomicRepresentation.standardRepresentationNorm
                G F s hs p hp_top q f hf :=
        add_le_add (hLp_le f hf hN) (hosc_le f hf hN)
    _ =
          (CLp + Cosc) *
            StandardAtomicRepresentation.standardRepresentationNorm
              G F s hs p hp_top q f hf := by
        rw [add_mul]

end MeanOscillation

end

end GoodGridSpace
