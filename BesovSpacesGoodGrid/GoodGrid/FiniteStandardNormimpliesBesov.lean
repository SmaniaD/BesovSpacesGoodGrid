import BesovSpacesGoodGrid.GoodGrid.standardRepresentation

/-!
# Finite standard norm forces Besov membership

This file proves the endpoint upgrade for the standard atomic representation:
if an integrable function has finite abstract standard coefficient cost, then
the canonical standard block sequence is an `L^p` representation with finite
`(p,q)` cost, it represents the original function, and the corresponding
Souza-Besov cost is controlled by the standard coefficient gauge.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace StandardAtomicRepresentation

/-- The canonical standard block sequence attached to an integrable function. -/
def canonicalStandardBlockSeq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    (k : ℕ) →
      WeakGridSpace.LevelBlock
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) k :=
  canonicalStandardLpGridBlock G F s p hs Fact.out (ne_of_lt hp_top) f hf

/--
The abstract coefficient power of the canonical standard block sequence is
exactly the standard coefficient power used by `standardRepresentationNorm`.
-/
theorem blockLvlCoeff_canonicalStandardBlockSeq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) :
    WeakGridSpace.blockLvlCoeff
        (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
        (canonicalStandardBlockSeq G F s hs p hp_top f hf) k =
      standardBlockCoeffPower G F s hs p hp_top f hf k := by
  rfl

/--
Finite standard coefficient norm gives finite abstract `(p,q)` cost for the
bare canonical standard block sequence.
-/
theorem abstractFinitePQCost_canonicalStandardBlockSeq_of_standardRepresentationNorm_ne_top
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (hN : standardRepresentationNorm G F s hs p hp_top q f hf ≠ ∞) :
    WeakGridSpace.AbstractFinitePQCost
      (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) (q := q)
      (canonicalStandardBlockSeq G F s hs p hp_top f hf) := by
  classical
  let block := canonicalStandardBlockSeq G F s hs p hp_top f hf
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
      hp_top.ne
  by_cases hq : q = ∞
  · simp only [WeakGridSpace.AbstractFinitePQCost, hq, ↓reduceIte]
    refine ⟨(standardRepresentationNorm G F s hs p hp_top q f hf).toReal, ?_⟩
    rintro x ⟨k, rfl⟩
    rw [← ENNReal.ofReal_le_iff_le_toReal hN]
    rw [standardRepresentationNorm, hq]
    exact le_sSup (Set.mem_range_self k)
  · simp only [WeakGridSpace.AbstractFinitePQCost, hq, ↓reduceIte]
    rw [standardRepresentationNorm, if_neg hq] at hN
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    have hinv_pos : 0 < 1 / q.toReal := one_div_pos.mpr hq_pos
    have htsum_ne_top :
        (∑' k, ENNReal.ofReal
          (standardBlockCoeffPower G F s hs p hp_top f hf k ^
            (q.toReal / p.toReal))) ≠ ∞ := by
      intro htop
      apply hN
      rw [htop, ENNReal.top_rpow_of_pos hinv_pos]
    have hsum :
        Summable fun k =>
          (standardBlockCoeffPower G F s hs p hp_top f hf k) ^
            (q.toReal / p.toReal) :=
      (ENNReal.summable_toReal htsum_ne_top).congr fun k => by
        rw [ENNReal.toReal_ofReal]
        exact Real.rpow_nonneg
          (standardBlockCoeffPower_nonneg G F s hs p hp_top f hf k) _
    refine hsum.congr ?_
    intro k
    rw [blockLvlCoeff_canonicalStandardBlockSeq G F s hs p hp_top f hf k]

/--
A finite `ENNReal` upper bound on the extended coefficient cost gives the same
real upper bound for `pqCost`.

The weak-grid completeness file uses this conversion internally; we keep this
local version here so the standard representation comparison can state a real
Besov norm bound.
-/
private theorem pqCost_le_of_pqCostENNReal_le
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

/--
If the abstract standard norm is finite, the canonical standard blocks converge
as a series in `L^p`.

This is the first analytic part of the desired endpoint theorem.  It does not
yet identify the `L^p` limit with the original integrable function.
-/
theorem finite_standardRepresentationNorm_has_Lp_standard_limit
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (hN : standardRepresentationNorm G F s hs p hp_top q f hf ≠ ∞) :
    ∃ g : Lp ℂ p G.grid.μ,
      Nonempty
        { R :
            WeakGridSpace.LpGridRepresentation
              (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) g //
          R.block = canonicalStandardBlockSeq G F s hs p hp_top f hf } := by
  classical
  haveI : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  have hfin :=
    abstractFinitePQCost_canonicalStandardBlockSeq_of_standardRepresentationNorm_ne_top
      G F s hs p hp_top q f hf hN
  have hG2 : WeakGridSpace.AssumptionG2 G.toWeakGridSpace s p ∞ q :=
    souza_assumptionG2 G s p q hs Fact.out (ne_of_lt hp_top)
  simpa [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid] using
    (WeakGridSpace.formalBlockSeq_hasRepresentation
      (G := G.toWeakGridSpace)
      (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
      (q := q)
      hG2 (ne_of_lt hp_top) hs le_top
      (canonicalStandardBlockSeq G F s hs p hp_top f hf) hfin)

private theorem l2NormalizationFactor_ne_zero
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (i : F.Index) :
    HaarRepresentation.l2NormalizationFactor G F i ≠ 0 := by
  have hnonneg :
      0 ≤ F.indexL2NormSq (HaarRepresentation.GridOf G) i := by
    rw [← F.integral_function_mul_self_eq_indexL2NormSq (HaarRepresentation.GridOf G) i]
    exact integral_nonneg fun x => mul_self_nonneg _
  have hpos : 0 < F.indexL2NormSq (HaarRepresentation.GridOf G) i :=
    lt_of_le_of_ne hnonneg (F.indexL2NormSq_ne_zero (HaarRepresentation.GridOf G) i).symm
  simp [HaarRepresentation.l2NormalizationFactor, Real.sqrt_ne_zero'.mpr hpos]

private theorem integral_mul_fullHaar_eq_of_haarCoeff_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (f g : α → ℂ) (hf : Integrable f G.grid.μ) (hg : Integrable g G.grid.μ)
    (hhaar :
      ∀ i : F.Index,
        HaarRepresentation.Coeff G F f hf i =
          HaarRepresentation.Coeff G F g hg i)
    (i : F.Index) :
    ∫ x, f x *
        (UnbalancedHaarWavelet.FullHaarSystem.function
          (HaarRepresentation.GridOf G) F i x : ℂ) ∂G.grid.μ =
      ∫ x, g x *
        (UnbalancedHaarWavelet.FullHaarSystem.function
          (HaarRepresentation.GridOf G) F i x : ℂ) ∂G.grid.μ := by
  classical
  let c : ℂ := ((HaarRepresentation.l2NormalizationFactor G F i : ℝ) : ℂ)
  let ψ : α → ℂ :=
    fun x =>
      (UnbalancedHaarWavelet.FullHaarSystem.function
        (HaarRepresentation.GridOf G) F i x : ℂ)
  have hc : c ≠ 0 := by
    change (((HaarRepresentation.l2NormalizationFactor G F i : ℝ) : ℂ)) ≠ 0
    exact_mod_cast l2NormalizationFactor_ne_zero G F i
  have hfcoeff :
      HaarRepresentation.Coeff G F f hf i = c * ∫ x, f x * ψ x ∂G.grid.μ := by
    calc
      HaarRepresentation.Coeff G F f hf i
          = ∫ x, f x * (c * ψ x) ∂G.grid.μ := by
              simp [HaarRepresentation.Coeff, HaarRepresentation.L2normalizedHaar, c, ψ]
      _ = ∫ x, c * (f x * ψ x) ∂G.grid.μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun x => by ring
      _ = c * ∫ x, f x * ψ x ∂G.grid.μ := by
              rw [integral_const_mul]
  have hgcoeff :
      HaarRepresentation.Coeff G F g hg i = c * ∫ x, g x * ψ x ∂G.grid.μ := by
    calc
      HaarRepresentation.Coeff G F g hg i
          = ∫ x, g x * (c * ψ x) ∂G.grid.μ := by
              simp [HaarRepresentation.Coeff, HaarRepresentation.L2normalizedHaar, c, ψ]
      _ = ∫ x, c * (g x * ψ x) ∂G.grid.μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun x => by ring
      _ = c * ∫ x, g x * ψ x ∂G.grid.μ := by
              rw [integral_const_mul]
  have h := hhaar i
  rw [hfcoeff, hgcoeff] at h
  exact mul_left_cancel₀ hc h

private theorem integrable_mul_fullHaar_of_integrable
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (i : F.Index) :
    Integrable
      (fun x =>
        f x *
          (UnbalancedHaarWavelet.FullHaarSystem.function
            (HaarRepresentation.GridOf G) F i x : ℂ))
      G.grid.μ := by
  haveI : ENNReal.HolderTriple (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (1 : ℝ≥0∞) :=
    ENNReal.HolderTriple.instInfty 1
  exact (memLp_one_iff_integrable.mpr hf).integrable_mul
    ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function
      (HaarRepresentation.GridOf G) F (∞ : ℝ≥0∞) i).ofReal (K := ℂ))

private theorem setIntegral_eq_of_forall_haarCoeff_eq_gridGenerating
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (f g : α → ℂ) (hf : Integrable f G.grid.μ) (hg : Integrable g G.grid.μ)
    (hhaar :
      ∀ i : F.Index,
        HaarRepresentation.Coeff G F f hf i =
          HaarRepresentation.Coeff G F g hg i)
    {A : Set α} (hA : A ∈ gridGeneratingSets G) :
    ∫ x in A, f x ∂G.grid.μ = ∫ x in A, g x ∂G.grid.μ := by
  classical
  rcases Set.mem_iUnion.mp hA with ⟨n, hAn⟩
  have hAm : MeasurableSet A := G.grid.grid.measurable n A hAn
  have hspan :
      (fun x => Set.indicator A (fun _ => (1 : ℝ)) x)
        ∈ Submodule.span ℝ
          (Set.range (UnbalancedHaarWavelet.FullHaarSystem.function
            (HaarRepresentation.GridOf G) F)) :=
    UnbalancedHaarWavelet.indicator_partition_mem_span_FullHaarSystem
      (HaarRepresentation.GridOf G) F A n hAn
  rcases (Submodule.mem_span_iff_exists_finset_subset).mp hspan with
    ⟨a, S, hS, -, hrepr⟩
  have hpair (u : α → ℝ) (hu : u ∈ S) :
      ∫ x, f x * (u x : ℂ) ∂G.grid.μ =
        ∫ x, g x * (u x : ℂ) ∂G.grid.μ := by
    rcases hS hu with ⟨i, rfl⟩
    exact integral_mul_fullHaar_eq_of_haarCoeff_eq G F f g hf hg hhaar i
  have hreprC :
      ∀ x,
        ((∑ u ∈ S, a u * u x : ℝ) : ℂ) =
          Set.indicator A (fun _ => (1 : ℂ)) x := by
    intro x
    have hx := congrFun hrepr x
    have hx' :
        (∑ u ∈ S, a u * u x : ℝ) =
          Set.indicator A (fun _ => (1 : ℝ)) x := by
      simpa [Pi.smul_apply, smul_eq_mul] using hx
    by_cases hmem : x ∈ A
    · simp [hx', hmem]
    · simp [hx', hmem]
  have hleft :
      ∫ x in A, f x ∂G.grid.μ =
        ∑ u ∈ S, (a u : ℂ) * ∫ x, f x * (u x : ℂ) ∂G.grid.μ := by
    calc
      ∫ x in A, f x ∂G.grid.μ
          = ∫ x, Set.indicator A f x ∂G.grid.μ := by
              rw [MeasureTheory.integral_indicator hAm]
      _ = ∫ x, f x * Set.indicator A (fun _ => (1 : ℂ)) x ∂G.grid.μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun x => by
                by_cases hx : x ∈ A <;> simp [hx]
      _ = ∫ x, ∑ u ∈ S, (a u : ℂ) * (f x * (u x : ℂ)) ∂G.grid.μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun x => by
                calc
                  f x * Set.indicator A (fun _ => (1 : ℂ)) x
                      = f x * ((∑ u ∈ S, a u * u x : ℝ) : ℂ) := by
                          rw [hreprC x]
                  _ = f x * (∑ u ∈ S, (a u : ℂ) * (u x : ℂ)) := by
                          simp only [Complex.ofReal_sum, Complex.ofReal_mul]
                  _ = ∑ u ∈ S, (a u : ℂ) * (f x * (u x : ℂ)) := by
                          rw [Finset.mul_sum]
                          refine Finset.sum_congr rfl ?_
                          intro u hu
                          ring
      _ = ∑ u ∈ S, ∫ x, (a u : ℂ) * (f x * (u x : ℂ)) ∂G.grid.μ := by
              rw [MeasureTheory.integral_finsetSum]
              intro u hu
              rcases hS hu with ⟨i, hi⟩
              have hint :=
                (integrable_mul_fullHaar_of_integrable G F f hf i).const_mul (a u : ℂ)
              simpa [hi] using hint
      _ = ∑ u ∈ S, (a u : ℂ) * ∫ x, f x * (u x : ℂ) ∂G.grid.μ := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              rw [integral_const_mul]
  have hright :
      ∫ x in A, g x ∂G.grid.μ =
        ∑ u ∈ S, (a u : ℂ) * ∫ x, g x * (u x : ℂ) ∂G.grid.μ := by
    calc
      ∫ x in A, g x ∂G.grid.μ
          = ∫ x, Set.indicator A g x ∂G.grid.μ := by
              rw [MeasureTheory.integral_indicator hAm]
      _ = ∫ x, g x * Set.indicator A (fun _ => (1 : ℂ)) x ∂G.grid.μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun x => by
                by_cases hx : x ∈ A <;> simp [hx]
      _ = ∫ x, ∑ u ∈ S, (a u : ℂ) * (g x * (u x : ℂ)) ∂G.grid.μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun x => by
                calc
                  g x * Set.indicator A (fun _ => (1 : ℂ)) x
                      = g x * ((∑ u ∈ S, a u * u x : ℝ) : ℂ) := by
                          rw [hreprC x]
                  _ = g x * (∑ u ∈ S, (a u : ℂ) * (u x : ℂ)) := by
                          simp only [Complex.ofReal_sum, Complex.ofReal_mul]
                  _ = ∑ u ∈ S, (a u : ℂ) * (g x * (u x : ℂ)) := by
                          rw [Finset.mul_sum]
                          refine Finset.sum_congr rfl ?_
                          intro u hu
                          ring
      _ = ∑ u ∈ S, ∫ x, (a u : ℂ) * (g x * (u x : ℂ)) ∂G.grid.μ := by
              rw [MeasureTheory.integral_finsetSum]
              intro u hu
              rcases hS hu with ⟨i, hi⟩
              have hint :=
                (integrable_mul_fullHaar_of_integrable G F g hg i).const_mul (a u : ℂ)
              simpa [hi] using hint
      _ = ∑ u ∈ S, (a u : ℂ) * ∫ x, g x * (u x : ℂ) ∂G.grid.μ := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              rw [integral_const_mul]
  rw [hleft, hright]
  refine Finset.sum_congr rfl ?_
  intro u hu
  rw [hpair u hu]

/--
Equality of all normalized Haar coefficients forces equality of all set
integrals.

The proof uses the density infrastructure from `UnbalancedHaarWavelet`: grid
cell indicators belong to the algebraic span of the full Haar family, and the
grid cells generate the ambient sigma-algebra.  This is the measure-theoretic
half of the `L¹` uniqueness argument.
-/
theorem setIntegral_eq_of_forall_haarCoeff_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (f g : α → ℂ) (hf : Integrable f G.grid.μ) (hg : Integrable g G.grid.μ)
    (hhaar :
      ∀ i : F.Index,
        HaarRepresentation.Coeff G F f hf i =
          HaarRepresentation.Coeff G F g hg i) :
    ∀ A : Set α, MeasurableSet A → G.grid.μ A < ∞ →
      ∫ x in A, f x ∂G.grid.μ = ∫ x in A, g x ∂G.grid.μ := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  let C : ∀ A : Set α, MeasurableSet A → Prop :=
    fun A _ => ∫ x in A, f x ∂G.grid.μ = ∫ x in A, g x ∂G.grid.μ
  have hempty : C ∅ MeasurableSet.empty := by
    simp [C]
  have hbasic :
      ∀ A (hA : A ∈ gridGeneratingSets G),
        C A ((grid_generates_eq_generateFrom_gridGeneratingSets G) ▸
          MeasurableSpace.GenerateMeasurable.basic A hA) := by
    intro A hA
    exact setIntegral_eq_of_forall_haarCoeff_eq_gridGenerating G F f g hf hg hhaar hA
  have huniv : C Set.univ MeasurableSet.univ := by
    have huniv_mem : Set.univ ∈ gridGeneratingSets G := by
      refine Set.mem_iUnion.mpr ⟨0, ?_⟩
      simp [G.grid.grid.first_partition_eq_univ]
    exact setIntegral_eq_of_forall_haarCoeff_eq_gridGenerating
      G F f g hf hg hhaar huniv_mem
  have hcompl :
      ∀ A (hAm : MeasurableSet A), C A hAm → C Aᶜ hAm.compl := by
    intro A hAm hA
    have htotal : ∫ x, f x ∂G.grid.μ = ∫ x, g x ∂G.grid.μ := by
      simpa [C] using huniv
    calc
      ∫ x in Aᶜ, f x ∂G.grid.μ
          = ∫ x, f x ∂G.grid.μ - ∫ x in A, f x ∂G.grid.μ := by
              rw [MeasureTheory.setIntegral_compl hAm hf]
      _ = ∫ x, g x ∂G.grid.μ - ∫ x in A, g x ∂G.grid.μ := by
              rw [hA, htotal]
      _ = ∫ x in Aᶜ, g x ∂G.grid.μ := by
              rw [MeasureTheory.setIntegral_compl hAm hg]
  have hiUnion :
      ∀ A : ℕ → Set α, Pairwise (fun i j => Disjoint (A i) (A j)) →
        ∀ hmeas : ∀ i, MeasurableSet (A i),
          (∀ i, C (A i) (hmeas i)) →
          C (⋃ i, A i) (MeasurableSet.iUnion hmeas) := by
    intro A hdisj hmeas hA
    calc
      ∫ x in ⋃ i, A i, f x ∂G.grid.μ
          = ∑' i, ∫ x in A i, f x ∂G.grid.μ := by
              rw [MeasureTheory.integral_iUnion hmeas hdisj hf.integrableOn]
      _ = ∑' i, ∫ x in A i, g x ∂G.grid.μ := by
              exact tsum_congr fun i => hA i
      _ = ∫ x in ⋃ i, A i, g x ∂G.grid.μ := by
              exact (MeasureTheory.integral_iUnion hmeas hdisj hg.integrableOn).symm
  intro A hAm hAfinite
  exact MeasurableSpace.induction_on_inter
    (grid_generates_eq_generateFrom_gridGeneratingSets G)
    (isPiSystem_gridGeneratingSets G) hempty hbasic hcompl hiUnion A hAm

private theorem canonicalStandardPositiveLevelBlock_toFunLt_eq_haarLevelBlockFunction
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) (x : α) :
    (canonicalStandardPositiveLevelBlock G F s p hs Fact.out (ne_of_lt hp_top) f hf k).toFunLt
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) x =
      haarLevelBlockFunction G F f hf k x := by
  classical
  calc
    (canonicalStandardPositiveLevelBlock G F s p hs Fact.out (ne_of_lt hp_top) f hf k).toFunLt
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) x
        = canonicalStandardLevelBlockFunction G F p s f hf k x := by
            exact canonicalStandardPositiveLevelBlock_toFunLt
              G F s p hs Fact.out (ne_of_lt hp_top) f hf k x
    _ = standardLevelBlockFunction G F p s f hf k x := by
            exact canonicalStandardLevelBlock_eq_standardLevelBlock_pointwise
              G F p s f hf k x
    _ = haarLevelBlockFunction G F f hf k x := by
            unfold standardLevelBlockFunction haarLevelBlockFunction
            refine Finset.sum_congr rfl ?_
            intro Q hQ
            exact (haarBlock_eq_sum_tildeCoeff_tildeAtom_pointwise G F p s f hf
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) x).symm

private theorem l2NormalizationFactor_mul_self_mul_indexL2NormSq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (i : F.Index) :
    (((HaarRepresentation.l2NormalizationFactor G F i : ℝ) : ℂ) *
        ((HaarRepresentation.l2NormalizationFactor G F i : ℝ) : ℂ)) *
      (F.indexL2NormSq (HaarRepresentation.GridOf G) i : ℂ) = 1 := by
  let N : ℝ := F.indexL2NormSq (HaarRepresentation.GridOf G) i
  have hN_nonneg : 0 ≤ N := by
    have h :
        0 ≤ F.indexL2NormSq (HaarRepresentation.GridOf G) i := by
      rw [← F.integral_function_mul_self_eq_indexL2NormSq (HaarRepresentation.GridOf G) i]
      exact integral_nonneg fun x => mul_self_nonneg _
    simpa [N] using h
  have hN_pos : 0 < N :=
    lt_of_le_of_ne hN_nonneg (by
      simpa [N] using (F.indexL2NormSq_ne_zero (HaarRepresentation.GridOf G) i).symm)
  have hsqrt_mul : Real.sqrt N * Real.sqrt N = N := by
    simpa [pow_two] using Real.sq_sqrt hN_pos.le
  have hsqrt_ne : Real.sqrt N ≠ 0 := Real.sqrt_ne_zero'.mpr hN_pos
  have hreal : ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) * N = 1 := by
    calc
      ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) * N
          = (Real.sqrt N * Real.sqrt N)⁻¹ * N := by
              rw [← mul_inv_rev]
      _ = N⁻¹ * N := by
              rw [hsqrt_mul]
      _ = 1 := inv_mul_cancel₀ hN_pos.ne'
  calc
    (((HaarRepresentation.l2NormalizationFactor G F i : ℝ) : ℂ) *
        ((HaarRepresentation.l2NormalizationFactor G F i : ℝ) : ℂ)) *
      (F.indexL2NormSq (HaarRepresentation.GridOf G) i : ℂ)
        = ((((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) * N : ℝ) : ℂ) := by
            simp [HaarRepresentation.l2NormalizationFactor, N, mul_assoc]
    _ = 1 := by
            simp [hreal]

private theorem integrable_complex_fullHaar_mul_fullHaar
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (i j : F.Index) :
    Integrable
      (fun x : α =>
        (UnbalancedHaarWavelet.FullHaarSystem.function
            (HaarRepresentation.GridOf G) F i x : ℂ) *
          (UnbalancedHaarWavelet.FullHaarSystem.function
            (HaarRepresentation.GridOf G) F j x : ℂ))
      G.grid.μ := by
  simpa [map_mul] using
    (F.integrable_function_mul_function (HaarRepresentation.GridOf G) i j).ofReal (𝕜 := ℂ)

private theorem integral_const_mul_l2normalizedHaar_mul_l2normalizedHaar
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (a : ℂ) (i j : F.Index) :
    ∫ x,
      (a * HaarRepresentation.L2normalizedHaar G F i x) *
        HaarRepresentation.L2normalizedHaar G F j x ∂G.grid.μ =
      if i = j then a else 0 := by
  classical
  let ni : ℂ := ((HaarRepresentation.l2NormalizationFactor G F i : ℝ) : ℂ)
  let nj : ℂ := ((HaarRepresentation.l2NormalizationFactor G F j : ℝ) : ℂ)
  let ψi : α → ℂ :=
    fun x =>
      (UnbalancedHaarWavelet.FullHaarSystem.function
        (HaarRepresentation.GridOf G) F i x : ℂ)
  let ψj : α → ℂ :=
    fun x =>
      (UnbalancedHaarWavelet.FullHaarSystem.function
        (HaarRepresentation.GridOf G) F j x : ℂ)
  have hraw :
      (∫ x, ψi x * ψj x ∂G.grid.μ) =
        ((∫ x,
          UnbalancedHaarWavelet.FullHaarSystem.function
              (HaarRepresentation.GridOf G) F i x *
            UnbalancedHaarWavelet.FullHaarSystem.function
              (HaarRepresentation.GridOf G) F j x ∂G.grid.μ : ℝ) : ℂ) := by
    simpa [ψi, ψj, map_mul] using
      (integral_ofReal
        (𝕜 := ℂ)
        (f := fun x =>
          UnbalancedHaarWavelet.FullHaarSystem.function
              (HaarRepresentation.GridOf G) F i x *
            UnbalancedHaarWavelet.FullHaarSystem.function
              (HaarRepresentation.GridOf G) F j x)
        (μ := G.grid.μ))
  calc
    ∫ x,
      (a * HaarRepresentation.L2normalizedHaar G F i x) *
        HaarRepresentation.L2normalizedHaar G F j x ∂G.grid.μ
        = ∫ x, (a * ni * nj) * (ψi x * ψj x) ∂G.grid.μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by
              simp [HaarRepresentation.L2normalizedHaar, ni, nj, ψi, ψj]
              ring
    _ = (a * ni * nj) * ∫ x, ψi x * ψj x ∂G.grid.μ := by
            rw [integral_const_mul]
    _ = (a * ni * nj) *
          ((if i = j then F.indexL2NormSq (HaarRepresentation.GridOf G) i else 0 : ℝ) : ℂ) := by
            rw [hraw]
            rw [F.integral_function_mul_function_eq (HaarRepresentation.GridOf G) i j]
    _ = if i = j then a else 0 := by
            by_cases hij : i = j
            · subst j
              simp [ni, nj, mul_assoc,
                l2NormalizationFactor_mul_self_mul_indexL2NormSq G F i]
            · simp [hij]

private theorem integrable_const_mul_l2normalizedHaar_mul_l2normalizedHaar
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (a : ℂ) (i j : F.Index) :
    Integrable
      (fun x =>
        (a * HaarRepresentation.L2normalizedHaar G F i x) *
          HaarRepresentation.L2normalizedHaar G F j x)
      G.grid.μ := by
  let ni : ℂ := ((HaarRepresentation.l2NormalizationFactor G F i : ℝ) : ℂ)
  let nj : ℂ := ((HaarRepresentation.l2NormalizationFactor G F j : ℝ) : ℂ)
  let ψi : α → ℂ :=
    fun x =>
      (UnbalancedHaarWavelet.FullHaarSystem.function
        (HaarRepresentation.GridOf G) F i x : ℂ)
  let ψj : α → ℂ :=
    fun x =>
      (UnbalancedHaarWavelet.FullHaarSystem.function
        (HaarRepresentation.GridOf G) F j x : ℂ)
  have h :
      Integrable (fun x => (a * ni * nj) * (ψi x * ψj x)) G.grid.μ :=
    (integrable_complex_fullHaar_mul_fullHaar G F i j).const_mul (a * ni * nj)
  refine h.congr ?_
  exact Filter.Eventually.of_forall fun x => by
    simp [HaarRepresentation.L2normalizedHaar, ni, nj, ψi, ψj]
    ring

/-- The continuous `Lp` functional extracting one normalized Haar coefficient. -/
private def haarCoeffFunctionalLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (i : F.Index) :
    Lp ℂ p G.grid.μ →L[ℂ] ℂ :=
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing G.grid.μ p q).flip
    ((HaarRepresentation.l2normalizedHaar_memLp G F q i).toLp
      (HaarRepresentation.L2normalizedHaar G F i))

/-- On concrete representatives, `haarCoeffFunctionalLp` is the Haar coefficient integral. -/
private theorem haarCoeffFunctionalLp_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (f : α → ℂ) (hf : MemLp f p G.grid.μ) (i : F.Index) :
    haarCoeffFunctionalLp G F p q i (hf.toLp f) =
      ∫ x, f x * HaarRepresentation.L2normalizedHaar G F i x ∂G.grid.μ := by
  rw [haarCoeffFunctionalLp]
  change (ContinuousLinearMap.mul ℂ ℂ).lpPairing G.grid.μ p q (hf.toLp f)
      ((HaarRepresentation.l2normalizedHaar_memLp G F q i).toLp
        (HaarRepresentation.L2normalizedHaar G F i)) =
    ∫ x, f x * HaarRepresentation.L2normalizedHaar G F i x ∂G.grid.μ
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards
    [MemLp.coeFn_toLp hf,
      MemLp.coeFn_toLp (HaarRepresentation.l2normalizedHaar_memLp G F q i)] with x hxf hxi
  simp [hxf, hxi]

private theorem haarCoeffFunctionalLp_coeff_smul_l2normalizedHaar_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (a : ℂ) (i j : F.Index) :
    haarCoeffFunctionalLp G F p q i
        (a • (HaarRepresentation.l2normalizedHaar_memLp G F p j).toLp
          (HaarRepresentation.L2normalizedHaar G F j)) =
      if j = i then a else 0 := by
  rw [← MeasureTheory.MemLp.toLp_const_smul]
  rw [haarCoeffFunctionalLp_toLp]
  exact integral_const_mul_l2normalizedHaar_mul_l2normalizedHaar G F a j i

private theorem integral_haarLevelBlockFunction_mul_l2normalizedHaar_eq_coeff
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (j : F.toHaarSystem.Index) :
    ∫ x,
      haarLevelBlockFunction G F f hf j.level x *
        HaarRepresentation.L2normalizedHaar G F (.wavelet j) x ∂G.grid.μ =
      HaarRepresentation.Coeff G F f hf (.wavelet j) := by
  classical
  let Qj : WeakGridSpace.LevelCell G.toWeakGridSpace j.level := ⟨j.cell, j.hcell⟩
  let Qgj : GoodGridCell G := { level := j.level, cell := Qj.1, mem := Qj.2 }
  let bj :
      {r : Finset (Set α) × Finset (Set α) //
        r ∈ (F.toHaarSystem.binaryRefinement.tree Qgj.level Qgj.cell Qgj.mem).Branches} :=
    j.branch
  have hidxj : HaarRepresentation.indexOfCellBranch G F Qgj bj = j := by
    cases j
    rfl
  unfold haarLevelBlockFunction haarCellBlockFunction
  have hfun :
      (fun x =>
        (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j.level,
          ∑ b ∈ HaarRepresentation.indicesInCell G F
              ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G),
            HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F
                  ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) *
              HaarRepresentation.normalizedFunction G F
                (.wavelet (HaarRepresentation.indexOfCellBranch G F
                  ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) x) *
          HaarRepresentation.L2normalizedHaar G F (.wavelet j) x)
        =
      fun x =>
        ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j.level,
          ∑ b ∈ HaarRepresentation.indicesInCell G F
              ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G),
            (HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F
                  ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) *
              HaarRepresentation.L2normalizedHaar G F
                (.wavelet (HaarRepresentation.indexOfCellBranch G F
                  ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) x) *
              HaarRepresentation.L2normalizedHaar G F (.wavelet j) x := by
    funext x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro Q hQ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro b hb
    simp [HaarRepresentation.normalizedFunction, HaarRepresentation.L2normalizedHaar]
  rw [hfun]
  rw [MeasureTheory.integral_finsetSum]
  · calc
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j.level,
          ∫ x,
            (∑ b ∈ HaarRepresentation.indicesInCell G F
                ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G),
              (HaarRepresentation.Coeff G F f hf
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F
                    ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) *
                HaarRepresentation.L2normalizedHaar G F
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F
                    ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) x) *
                HaarRepresentation.L2normalizedHaar G F (.wavelet j) x) ∂G.grid.μ
          =
        ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j.level,
          ∑ b ∈ HaarRepresentation.indicesInCell G F
              ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G),
            ∫ x,
              (HaarRepresentation.Coeff G F f hf
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F
                    ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) *
                HaarRepresentation.L2normalizedHaar G F
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F
                    ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) x) *
                HaarRepresentation.L2normalizedHaar G F (.wavelet j) x ∂G.grid.μ := by
            refine Finset.sum_congr rfl ?_
            intro Q hQ
            rw [MeasureTheory.integral_finsetSum]
            intro b hb
            exact integrable_const_mul_l2normalizedHaar_mul_l2normalizedHaar G F
              (HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F
                  ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)))
              (.wavelet (HaarRepresentation.indexOfCellBranch G F
                ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b))
              (.wavelet j)
      _ =
        ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j.level,
          ∑ b ∈ HaarRepresentation.indicesInCell G F
              ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G),
            if (.wavelet (HaarRepresentation.indexOfCellBranch G F
                    ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b) :
                F.Index) = .wavelet j then
              HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F
                  ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b))
            else
              0 := by
            refine Finset.sum_congr rfl ?_
            intro Q hQ
            refine Finset.sum_congr rfl ?_
            intro b hb
            exact integral_const_mul_l2normalizedHaar_mul_l2normalizedHaar G F
              (HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F
                  ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)))
              (.wavelet (HaarRepresentation.indexOfCellBranch G F
                ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b))
              (.wavelet j)
      _ = HaarRepresentation.Coeff G F f hf (.wavelet j) := by
            rw [Finset.sum_eq_single Qj]
            · change
                (∑ b ∈ HaarRepresentation.indicesInCell G F Qgj,
                  if (.wavelet (HaarRepresentation.indexOfCellBranch G F Qgj b) :
                      F.Index) = .wavelet j then
                    HaarRepresentation.Coeff G F f hf
                      (.wavelet (HaarRepresentation.indexOfCellBranch G F Qgj b))
                  else
                    0) = HaarRepresentation.Coeff G F f hf (.wavelet j)
              rw [Finset.sum_eq_single bj]
              · simp [hidxj]
              · intro b hb hb_ne
                have hne :
                    (.wavelet (HaarRepresentation.indexOfCellBranch G F Qgj b) :
                      F.Index) ≠ .wavelet j := by
                  intro h
                  injection h with hindex
                  apply hb_ne
                  cases j
                  cases b
                  simpa [HaarRepresentation.indexOfCellBranch, Qj, Qgj, bj] using hindex
                simp [hne]
              · intro hbj
                exact False.elim (hbj (by simp [HaarRepresentation.indicesInCell, Qgj, bj]))
            · intro Q hQ hQ_ne
              apply Finset.sum_eq_zero
              intro b hb
              have hne :
                  (.wavelet (HaarRepresentation.indexOfCellBranch G F
                      ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b) :
                    F.Index) ≠ .wavelet j := by
                intro h
                injection h with hindex
                have hcell :=
                  congrArg (fun t : F.toHaarSystem.Index => t.cell) hindex
                exact hQ_ne (Subtype.ext hcell)
              simp [hne]
            · intro hQj
              exact False.elim (hQj (Finset.mem_univ Qj))
  · intro Q hQ
    refine integrable_finsetSum (μ := G.grid.μ) (HaarRepresentation.indicesInCell G F
      ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G)) ?_
    intro b hb
    exact integrable_const_mul_l2normalizedHaar_mul_l2normalizedHaar G F
      (HaarRepresentation.Coeff G F f hf
        (.wavelet (HaarRepresentation.indexOfCellBranch G F
          ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)))
      (.wavelet (HaarRepresentation.indexOfCellBranch G F
        ({ level := j.level, cell := Q.1, mem := Q.2 } : GoodGridCell G) b))
      (.wavelet j)

/--
Coefficient extraction from a finite Haar level block.

This is the local orthogonality step: if two level-`k` Haar blocks agree as
functions, then every normalized Haar coefficient attached to level `k` agrees.
-/
private theorem haarCoeff_wavelet_eq_of_haarLevelBlockFunction_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (f g : α → ℂ) (hf : Integrable f G.grid.μ) (hg : Integrable g G.grid.μ)
    (j : F.toHaarSystem.Index)
    (hlevel :
      haarLevelBlockFunction G F f hf j.level =
        haarLevelBlockFunction G F g hg j.level) :
    HaarRepresentation.Coeff G F f hf (.wavelet j) =
      HaarRepresentation.Coeff G F g hg (.wavelet j) := by
  have hpair :
      ∫ x,
        haarLevelBlockFunction G F f hf j.level x *
          HaarRepresentation.L2normalizedHaar G F (.wavelet j) x ∂G.grid.μ =
        ∫ x,
          haarLevelBlockFunction G F g hg j.level x *
            HaarRepresentation.L2normalizedHaar G F (.wavelet j) x ∂G.grid.μ := by
    rw [hlevel]
  rw [integral_haarLevelBlockFunction_mul_l2normalizedHaar_eq_coeff G F f hf j,
    integral_haarLevelBlockFunction_mul_l2normalizedHaar_eq_coeff G F g hg j] at hpair
  exact hpair

/--
Coefficient extraction from the level-zero standard block.

The level-zero block is the normalized father Haar term, so equality of these
blocks forces equality of the father coefficient.
-/
private theorem haarCoeff_alpha_eq_of_fatherBlock_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f g : α → ℂ) (hf : Integrable f G.grid.μ) (hg : Integrable g G.grid.μ)
    (hblock :
      canonicalStandardFatherLevelBlock G F s p hs Fact.out (ne_of_lt hp_top) f hf =
        canonicalStandardFatherLevelBlock G F s p hs Fact.out (ne_of_lt hp_top) g hg) :
    HaarRepresentation.Coeff G F f hf .alpha =
      HaarRepresentation.Coeff G F g hg .alpha := by
  classical
  let Qw : WeakGridSpace.LevelCell G.toWeakGridSpace 0 :=
    ⟨Set.univ, by
      change Set.univ ∈ G.grid.grid.partitions 0
      simp [G.grid.grid.first_partition_eq_univ]⟩
  let Qg : GoodGridCell G := { level := 0, cell := Qw.1, mem := Qw.2 }
  let r : ℝ := (G.grid.μ Qw.1).toReal ^ (s - (p.toReal)⁻¹)
  let c : ℂ := HaarRepresentation.L2normalizedHaar G F .alpha (cellPoint G Qg) / (r : ℂ)
  have hr_pos : 0 < r := by
    have hμ_pos : 0 < G.grid.μ Qw.1 :=
      G.grid.positive_measure 0 Qw.1 Qw.2
    letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
    have hμ_ne_top : G.grid.μ Qw.1 ≠ ∞ :=
      MeasureTheory.measure_ne_top G.grid.μ Qw.1
    have hμ_toReal_pos : 0 < (G.grid.μ Qw.1).toReal :=
      ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
    exact Real.rpow_pos_of_pos hμ_toReal_pos _
  have halpha_ne :
      HaarRepresentation.L2normalizedHaar G F .alpha (cellPoint G Qg) ≠ 0 := by
    have hμ_pos : 0 < G.grid.μ Set.univ :=
      G.grid.positive_measure 0 Set.univ
        (by simp [G.grid.grid.first_partition_eq_univ])
    letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
    have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ :=
      MeasureTheory.measure_ne_top G.grid.μ Set.univ
    have hμ_toReal_pos : 0 < (G.grid.μ Set.univ).toReal :=
      ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
    have hμ_toReal_ne : (G.grid.μ Set.univ).toReal ≠ 0 := ne_of_gt hμ_toReal_pos
    simp [HaarRepresentation.L2normalizedHaar, HaarRepresentation.l2NormalizationFactor,
      UnbalancedHaarWavelet.FullHaarSystem.function, F.alphaFunction_def,
      UnbalancedHaarWavelet.normalizedAlphaFunction, hμ_toReal_ne]
  have hc : c ≠ 0 := by
    simp [c, halpha_ne, show (r : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt hr_pos)]
  have hcoeff :
      HaarRepresentation.Coeff G F f hf .alpha * c =
        HaarRepresentation.Coeff G F g hg .alpha * c := by
    have hQ := congrArg (fun B => B.coeff Qw) hblock
    simpa [canonicalStandardFatherLevelBlock, Qw, Qg, r, c, div_eq_mul_inv, mul_assoc]
      using hQ
  exact mul_right_cancel₀ hc hcoeff

/--
The canonical standard blocks determine all normalized Haar coefficients.

This is the algebraic half of the `L¹` uniqueness argument.  Level zero gives
the father coefficient.  At positive levels, the canonical standard block is
the same `Lp` vector as the corresponding finite Haar level block; pairing
with the Haar functions and using finite orthogonality recovers each Haar
coefficient.
-/
theorem haarCoeff_eq_of_same_canonicalStandardBlockSeq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f g : α → ℂ) (hf : Integrable f G.grid.μ) (hg : Integrable g G.grid.μ)
    (hcoeff :
      canonicalStandardBlockSeq G F s hs p hp_top f hf =
        canonicalStandardBlockSeq G F s hs p hp_top g hg) :
    ∀ i : F.Index,
      HaarRepresentation.Coeff G F f hf i =
        HaarRepresentation.Coeff G F g hg i := by
  classical
  intro i
  cases i with
  | alpha =>
      have hblock :
          canonicalStandardFatherLevelBlock G F s p hs Fact.out (ne_of_lt hp_top) f hf =
            canonicalStandardFatherLevelBlock G F s p hs Fact.out (ne_of_lt hp_top) g hg := by
        simpa [canonicalStandardBlockSeq, canonicalStandardLpGridBlock] using congrFun hcoeff 0
      exact haarCoeff_alpha_eq_of_fatherBlock_eq G F s hs p hp_top f g hf hg hblock
  | wavelet j =>
      have hblock :
          canonicalStandardPositiveLevelBlock G F s p hs Fact.out (ne_of_lt hp_top) f hf j.level =
            canonicalStandardPositiveLevelBlock G F s p hs Fact.out (ne_of_lt hp_top) g hg j.level := by
        simpa [canonicalStandardBlockSeq, canonicalStandardLpGridBlock] using
          congrFun hcoeff (j.level + 1)
      have hlevel :
          haarLevelBlockFunction G F f hf j.level =
            haarLevelBlockFunction G F g hg j.level := by
        funext x
        have hx :=
          congrArg
            (fun B =>
              B.toFunLt (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) x)
            hblock
        simpa [canonicalStandardPositiveLevelBlock_toFunLt_eq_haarLevelBlockFunction
          G F s hs p hp_top f hf j.level x,
          canonicalStandardPositiveLevelBlock_toFunLt_eq_haarLevelBlockFunction
            G F s hs p hp_top g hg j.level x] using hx
      exact haarCoeff_wavelet_eq_of_haarLevelBlockFunction_eq G F f g hf hg j hlevel

/--
Uniqueness of the standard representation at the `L^1` endpoint.

This is the key missing identification lemma: if two integrable functions have
the same canonical standard coefficients, then they are equal almost
everywhere.  Mathematically, this should follow from the fact that the
standard coefficients recover all integrals over grid cells, and the grid cells
generate the measurable space.
-/
theorem ae_eq_of_same_canonicalStandardBlockSeq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f g : α → ℂ) (hf : Integrable f G.grid.μ) (hg : Integrable g G.grid.μ)
    (hcoeff :
      canonicalStandardBlockSeq G F s hs p hp_top f hf =
        canonicalStandardBlockSeq G F s hs p hp_top g hg) :
    f =ᵐ[G.grid.μ] g := by
  classical
  have hhaar :
      ∀ i : F.Index,
        HaarRepresentation.Coeff G F f hf i =
          HaarRepresentation.Coeff G F g hg i :=
    haarCoeff_eq_of_same_canonicalStandardBlockSeq G F s hs p hp_top f g hf hg hcoeff
  exact hf.ae_eq_of_forall_setIntegral_eq f g hg
    (setIntegral_eq_of_forall_haarCoeff_eq G F f g hf hg hhaar)

private def natEquivOptionNat : ℕ ≃ Option ℕ where
  toFun
    | 0 => none
    | n + 1 => some n
  invFun
    | none => 0
    | some n => n + 1
  left_inv n := by
    cases n <;> rfl
  right_inv o := by
    cases o <;> rfl

private theorem standardExpansionTermToLp_none_eq_fiber_sum
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    standardExpansionTermToLp G F β p s f hf none =
      ∑ u ∈ (@Finset.univ (standardExpansionFiber G F none) (by
          dsimp [standardExpansionFiber]
          infer_instance)),
        HaarRepresentation.Coeff G F f hf ((standardExpansionIndexEquiv G F) ⟨none, u⟩) •
          (HaarRepresentation.l2normalizedHaar_memLp G F β
              ((standardExpansionIndexEquiv G F) ⟨none, u⟩)).toLp
            (HaarRepresentation.L2normalizedHaar G F
              ((standardExpansionIndexEquiv G F) ⟨none, u⟩)) := by
  classical
  letI : Unique (standardExpansionFiber G F none) := by
    dsimp [standardExpansionFiber]
    infer_instance
  rw [Fintype.sum_unique]
  rfl

private theorem standardExpansionTermToLp_some_eq_fiber_sum
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) :
    standardExpansionTermToLp G F β p s f hf (some k) =
      ∑ u ∈ (@Finset.univ (standardExpansionFiber G F (some k)) (by
          dsimp [standardExpansionFiber]
          infer_instance)),
        HaarRepresentation.Coeff G F f hf ((standardExpansionIndexEquiv G F) ⟨some k, u⟩) •
          (HaarRepresentation.l2normalizedHaar_memLp G F β
              ((standardExpansionIndexEquiv G F) ⟨some k, u⟩)).toLp
            (HaarRepresentation.L2normalizedHaar G F
              ((standardExpansionIndexEquiv G F) ⟨some k, u⟩)) := by
  classical
  symm
  calc
    (∑ u ∈ (@Finset.univ (standardExpansionFiber G F (some k)) (by
          dsimp [standardExpansionFiber]
          infer_instance)),
        HaarRepresentation.Coeff G F f hf
            ((standardExpansionIndexEquiv G F) ⟨some k, u⟩) •
          (HaarRepresentation.l2normalizedHaar_memLp G F β
              ((standardExpansionIndexEquiv G F) ⟨some k, u⟩)).toLp
            (HaarRepresentation.L2normalizedHaar G F
              ((standardExpansionIndexEquiv G F) ⟨some k, u⟩)))
      =
        (haarLevelBlock_memLp G F β f hf k).toLp
          (haarLevelBlockFunction G F f hf k) := by
          rw [haarLevelBlock_toLp_eq_finsetSum G F β f hf k]
          change
            (∑ u ∈
              (@Finset.univ
                (Σ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
                  {b : Finset (Set α) × Finset (Set α) //
                    b ∈ (F.toHaarSystem.binaryRefinement.tree k Q.1 Q.2).Branches})
                (by infer_instance)),
              HaarRepresentation.Coeff G F f hf
                  ((standardExpansionIndexEquiv G F) ⟨some k, u⟩) •
                (HaarRepresentation.l2normalizedHaar_memLp G F β
                    ((standardExpansionIndexEquiv G F) ⟨some k, u⟩)).toLp
                  (HaarRepresentation.L2normalizedHaar G F
                    ((standardExpansionIndexEquiv G F) ⟨some k, u⟩))) =
              ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
                ∑ b ∈ HaarRepresentation.indicesInCell G F
                    ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G),
                  HaarRepresentation.Coeff G F f hf
                      (.wavelet (HaarRepresentation.indexOfCellBranch G F
                        ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) •
                    (HaarRepresentation.l2normalizedHaar_memLp G F β
                        (.wavelet (HaarRepresentation.indexOfCellBranch G F
                          ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b))).toLp
                      (HaarRepresentation.L2normalizedHaar G F
                        (.wavelet (HaarRepresentation.indexOfCellBranch G F
                          ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)))
          rw [Fintype.sum_sigma]
          rfl
    _ = standardExpansionTermToLp G F β p s f hf (some k) := by
          rw [haarLevelBlock_toLp_eq_standardLevelBlock_toLp G F β p s f hf k]
          rfl

private theorem canonicalStandardExpansionTermToLp_eq_standardExpansionTermToLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (ok : Option ℕ) :
    canonicalStandardExpansionTermToLp G F β p s f hf ok =
      standardExpansionTermToLp G F β p s f hf ok := by
  cases ok with
  | none => rfl
  | some k =>
      exact canonicalStandardLevelBlockToLp_eq_standardLevelBlockToLp G F β p s f hf k

private theorem haarCoeffFunctionalLp_standardExpansionTermToLp_alpha
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (β q : ℝ≥0∞) [Fact (1 ≤ β)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate β q]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (ok : Option ℕ) :
    haarCoeffFunctionalLp G F β q .alpha
        (standardExpansionTermToLp G F β p s f hf ok) =
      if ok = none then HaarRepresentation.Coeff G F f hf .alpha else 0 := by
  classical
  cases ok with
  | none =>
      rw [standardExpansionTermToLp_none_eq_fiber_sum G F β p s f hf]
      letI : Unique (standardExpansionFiber G F none) := by
        dsimp [standardExpansionFiber]
        infer_instance
      rw [Fintype.sum_unique]
      simpa using
        haarCoeffFunctionalLp_coeff_smul_l2normalizedHaar_toLp G F β q
          (HaarRepresentation.Coeff G F f hf .alpha) .alpha .alpha
  | some k =>
      rw [standardExpansionTermToLp_some_eq_fiber_sum G F β p s f hf k]
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro u hu
      rcases u with ⟨Q, b⟩
      change
        haarCoeffFunctionalLp G F β q .alpha
          (HaarRepresentation.Coeff G F f hf
              (.wavelet (HaarRepresentation.indexOfCellBranch G F
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)) •
            (HaarRepresentation.l2normalizedHaar_memLp G F β
                (.wavelet (HaarRepresentation.indexOfCellBranch G F
                  ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b))).toLp
              (HaarRepresentation.L2normalizedHaar G F
                (.wavelet (HaarRepresentation.indexOfCellBranch G F
                  ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)))) = 0
      simpa using
        haarCoeffFunctionalLp_coeff_smul_l2normalizedHaar_toLp G F β q
          (HaarRepresentation.Coeff G F f hf
            (.wavelet (HaarRepresentation.indexOfCellBranch G F
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b)))
          .alpha
          (.wavelet (HaarRepresentation.indexOfCellBranch G F
            ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) b))

private theorem haarCoeffFunctionalLp_standardExpansionTermToLp_wavelet
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (β q : ℝ≥0∞) [Fact (1 ≤ β)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate β q]
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (j : F.toHaarSystem.Index) (ok : Option ℕ) :
    haarCoeffFunctionalLp G F β q (.wavelet j)
        (standardExpansionTermToLp G F β p s f hf ok) =
      if ok = some j.level then HaarRepresentation.Coeff G F f hf (.wavelet j) else 0 := by
  classical
  cases ok with
  | none =>
      rw [standardExpansionTermToLp_none_eq_fiber_sum G F β p s f hf]
      letI : Unique (standardExpansionFiber G F none) := by
        dsimp [standardExpansionFiber]
        infer_instance
      rw [Fintype.sum_unique]
      simpa using
        haarCoeffFunctionalLp_coeff_smul_l2normalizedHaar_toLp G F β q
          (HaarRepresentation.Coeff G F f hf .alpha) (.wavelet j) .alpha
  | some k =>
      rw [standardExpansionTermToLp_some_eq_fiber_sum G F β p s f hf k]
      rw [map_sum]
      by_cases hk : k = j.level
      · subst k
        let uj : standardExpansionFiber G F (some j.level) :=
          ⟨⟨j.cell, j.hcell⟩, j.branch⟩
        rw [if_pos rfl]
        rw [Finset.sum_eq_single uj]
        · change
            haarCoeffFunctionalLp G F β q (.wavelet j)
              (HaarRepresentation.Coeff G F f hf
                  ((standardExpansionIndexEquiv G F) ⟨some j.level, uj⟩) •
                (HaarRepresentation.l2normalizedHaar_memLp G F β
                    ((standardExpansionIndexEquiv G F) ⟨some j.level, uj⟩)).toLp
                  (HaarRepresentation.L2normalizedHaar G F
                    ((standardExpansionIndexEquiv G F) ⟨some j.level, uj⟩))) =
              HaarRepresentation.Coeff G F f hf (.wavelet j)
          simpa [uj] using
            haarCoeffFunctionalLp_coeff_smul_l2normalizedHaar_toLp G F β q
              (HaarRepresentation.Coeff G F f hf (.wavelet j)) (.wavelet j) (.wavelet j)
        · intro u hu hune
          have hneidx :
              (standardExpansionIndexEquiv G F) ⟨some j.level, u⟩ ≠
                (.wavelet j : F.Index) := by
            intro hidx
            apply hune
            have hpre :
                (standardExpansionIndexEquiv G F).symm
                    ((standardExpansionIndexEquiv G F) ⟨some j.level, u⟩) =
                  (standardExpansionIndexEquiv G F).symm (.wavelet j : F.Index) := by
              rw [hidx]
            have hpair := by
              simpa [uj] using hpre
            cases hpair
            rfl
          change
            haarCoeffFunctionalLp G F β q (.wavelet j)
              (HaarRepresentation.Coeff G F f hf
                  ((standardExpansionIndexEquiv G F) ⟨some j.level, u⟩) •
                (HaarRepresentation.l2normalizedHaar_memLp G F β
                    ((standardExpansionIndexEquiv G F) ⟨some j.level, u⟩)).toLp
                  (HaarRepresentation.L2normalizedHaar G F
                    ((standardExpansionIndexEquiv G F) ⟨some j.level, u⟩))) = 0
          simpa [hneidx] using
            haarCoeffFunctionalLp_coeff_smul_l2normalizedHaar_toLp G F β q
              (HaarRepresentation.Coeff G F f hf
                ((standardExpansionIndexEquiv G F) ⟨some j.level, u⟩))
              (.wavelet j)
              ((standardExpansionIndexEquiv G F) ⟨some j.level, u⟩)
        · intro hnot
          exact False.elim (hnot (by simp))
      · rw [if_neg (by intro h; exact hk (Option.some.inj h))]
        apply Finset.sum_eq_zero
        intro u hu
        have hneidx :
            (standardExpansionIndexEquiv G F) ⟨some k, u⟩ ≠
              (.wavelet j : F.Index) := by
          intro hidx
          have hidx' :
              (standardExpansionIndexEquiv G F) ⟨some k, u⟩ =
                (standardExpansionIndexEquiv G F)
                  ⟨some j.level, (⟨⟨j.cell, j.hcell⟩, j.branch⟩ :
                    standardExpansionFiber G F (some j.level))⟩ := by
            simpa using hidx
          have hpre :=
            congrArg Sigma.fst ((standardExpansionIndexEquiv G F).injective hidx')
          exact hk (Option.some.inj hpre)
        change
          haarCoeffFunctionalLp G F β q (.wavelet j)
            (HaarRepresentation.Coeff G F f hf
                ((standardExpansionIndexEquiv G F) ⟨some k, u⟩) •
              (HaarRepresentation.l2normalizedHaar_memLp G F β
                  ((standardExpansionIndexEquiv G F) ⟨some k, u⟩)).toLp
                (HaarRepresentation.L2normalizedHaar G F
                  ((standardExpansionIndexEquiv G F) ⟨some k, u⟩))) = 0
        simpa [hneidx] using
          haarCoeffFunctionalLp_coeff_smul_l2normalizedHaar_toLp G F β q
            (HaarRepresentation.Coeff G F f hf
              ((standardExpansionIndexEquiv G F) ⟨some k, u⟩))
            (.wavelet j)
            ((standardExpansionIndexEquiv G F) ⟨some k, u⟩)

/--
The `L^p` limit of the canonical standard block sequence is the original
integrable function, viewed at the `L^1` endpoint.

The intended proof is: the partial sums have the same standard coefficients as
their finite block data; the coefficient functionals are continuous on `L^1`;
therefore the `L^p` limit, included into `L^1`, has the same standard
coefficients as `f`.  Then `ae_eq_of_same_canonicalStandardBlockSeq` identifies
the two functions.
-/
theorem canonicalStandardBlockSeq_Lp_limit_ae_eq_original
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (g : Lp ℂ p G.grid.μ)
    (hgsum :
      HasSum
        (fun k =>
          (canonicalStandardBlockSeq G F s hs p hp_top f hf k).toLp
            (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)))
        g) :
    (g : α → ℂ) =ᵐ[G.grid.μ] f := by
  classical
  let q : ℝ≥0∞ := ENNReal.conjExponent p
  haveI : ENNReal.HolderConjugate p q := ENNReal.HolderConjugate.conjExponent Fact.out
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  haveI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hgMemLp : MemLp (g : α → ℂ) p G.grid.μ := Lp.memLp g
  have hg : Integrable (g : α → ℂ) G.grid.μ := hgMemLp.integrable Fact.out
  have hnat :
      HasSum
        (fun n =>
          canonicalStandardExpansionTermToLp G F p p s f hf (natEquivOptionNat n))
        g := by
    refine hgsum.congr_fun ?_
    intro n
    cases n with
    | zero =>
        simpa [canonicalStandardBlockSeq, natEquivOptionNat] using
          (canonicalStandardLpGridBlock_toLp G F s p hs Fact.out
            (ne_of_lt hp_top) f hf 0).symm
    | succ n =>
        simpa [canonicalStandardBlockSeq, natEquivOptionNat] using
          (canonicalStandardLpGridBlock_toLp G F s p hs Fact.out
            (ne_of_lt hp_top) f hf (n + 1)).symm
  have hcanonicalOption :
      HasSum (canonicalStandardExpansionTermToLp G F p p s f hf) g :=
    natEquivOptionNat.hasSum_iff.mp hnat
  have hoption :
      HasSum (standardExpansionTermToLp G F p p s f hf) g := by
    refine hcanonicalOption.congr_fun ?_
    intro ok
    exact (canonicalStandardExpansionTermToLp_eq_standardExpansionTermToLp
      G F p p s f hf ok).symm
  have hcoeff_g_eq_f :
      ∀ i : F.Index,
        HaarRepresentation.Coeff G F (g : α → ℂ) hg i =
          HaarRepresentation.Coeff G F f hf i := by
    intro i
    cases i with
    | alpha =>
        let L : Lp ℂ p G.grid.μ →L[ℂ] ℂ :=
          haarCoeffFunctionalLp G F p q .alpha
        have hLsum :
            HasSum
              (fun ok =>
                L (standardExpansionTermToLp G F p p s f hf ok))
              (L g) :=
          hoption.mapL L
        have hsingle :
            HasSum
              (fun ok : Option ℕ =>
                if ok = none then HaarRepresentation.Coeff G F f hf .alpha else 0)
              (L g) := by
          refine hLsum.congr_fun ?_
          intro ok
          exact (haarCoeffFunctionalLp_standardExpansionTermToLp_alpha
            G F p q p s f hf ok).symm
        have hL_eq_f :
            L g = HaarRepresentation.Coeff G F f hf .alpha :=
          HasSum.unique hsingle
            (hasSum_ite_eq (none : Option ℕ) (HaarRepresentation.Coeff G F f hf .alpha))
        have hL_eq_g :
            L g = HaarRepresentation.Coeff G F (g : α → ℂ) hg .alpha := by
          have hto : hgMemLp.toLp (g : α → ℂ) = g := Lp.toLp_coeFn g hgMemLp
          calc
            L g = L (hgMemLp.toLp (g : α → ℂ)) := congrArg L hto.symm
            _ = HaarRepresentation.Coeff G F (g : α → ℂ) hg .alpha :=
                haarCoeffFunctionalLp_toLp G F p q (g : α → ℂ) hgMemLp .alpha
        exact hL_eq_g.symm.trans hL_eq_f
    | wavelet j =>
        let L : Lp ℂ p G.grid.μ →L[ℂ] ℂ :=
          haarCoeffFunctionalLp G F p q (.wavelet j)
        have hLsum :
            HasSum
              (fun ok =>
                L (standardExpansionTermToLp G F p p s f hf ok))
              (L g) :=
          hoption.mapL L
        have hsingle :
            HasSum
              (fun ok : Option ℕ =>
                if ok = some j.level then
                  HaarRepresentation.Coeff G F f hf (.wavelet j)
                else
                  0)
              (L g) := by
          refine hLsum.congr_fun ?_
          intro ok
          exact (haarCoeffFunctionalLp_standardExpansionTermToLp_wavelet
            G F p q p s f hf j ok).symm
        have hL_eq_f :
            L g = HaarRepresentation.Coeff G F f hf (.wavelet j) :=
          HasSum.unique hsingle
            (hasSum_ite_eq (some j.level)
              (HaarRepresentation.Coeff G F f hf (.wavelet j)))
        have hL_eq_g :
            L g = HaarRepresentation.Coeff G F (g : α → ℂ) hg (.wavelet j) := by
          have hto : hgMemLp.toLp (g : α → ℂ) = g := Lp.toLp_coeFn g hgMemLp
          calc
            L g = L (hgMemLp.toLp (g : α → ℂ)) := congrArg L hto.symm
            _ = HaarRepresentation.Coeff G F (g : α → ℂ) hg (.wavelet j) :=
                haarCoeffFunctionalLp_toLp G F p q (g : α → ℂ) hgMemLp (.wavelet j)
        exact hL_eq_g.symm.trans hL_eq_f
  have hfg : f =ᵐ[G.grid.μ] (g : α → ℂ) :=
    hf.ae_eq_of_forall_setIntegral_eq f (g : α → ℂ) hg
      (setIntegral_eq_of_forall_haarCoeff_eq G F f (g : α → ℂ) hf hg
        (fun i => (hcoeff_g_eq_f i).symm))
  exact hfg.symm

/--
Finite standard norm should force the standard expansion to sum to `f` in
`L^p`, hence `f ∈ L^p`.

The only remaining ingredients are the two endpoint-identification lemmas
above; the construction of the `L^p` limit is already proved by
`finite_standardRepresentationNorm_has_Lp_standard_limit`.
-/
theorem finite_standardRepresentationNorm_implies_memLp_and_hasSum
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (hN : standardRepresentationNorm G F s hs p hp_top q f hf ≠ ∞) :
    ∃ hfLp : MemLp f p G.grid.μ,
      HasSum
        (fun k =>
          (canonicalStandardBlockSeq G F s hs p hp_top f hf k).toLp
            (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)))
        (hfLp.toLp f) := by
  classical
  rcases finite_standardRepresentationNorm_has_Lp_standard_limit
      G F s hs p hp_top q f hf hN with
    ⟨g, ⟨R, hRblock⟩⟩
  have hgsum :
      HasSum
        (fun k =>
          (canonicalStandardBlockSeq G F s hs p hp_top f hf k).toLp
            (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)))
        g := by
    simpa [hRblock] using R.hasSum
  have hgf :
      (g : α → ℂ) =ᵐ[G.grid.μ] f :=
    canonicalStandardBlockSeq_Lp_limit_ae_eq_original G F s hs p hp_top f hf g hgsum
  have hfLp : MemLp f p G.grid.μ := by
    exact (Lp.memLp g).congr_norm hf.aestronglyMeasurable
      (hgf.mono fun x hx => by rw [← hx])
  refine ⟨hfLp, ?_⟩
  have hg_eq : g = hfLp.toLp f := by
    apply Lp.ext
    exact hgf.trans (MemLp.coeFn_toLp hfLp).symm
  simpa [hg_eq] using hgsum

/--
Finite standard norm gives the canonical Souza-Besov representation of `f`.

More concretely, the canonical standard blocks form an `LpGridRepresentation`
of the `L^p` class of `f`; this representation has finite `(p,q)` cost; its
extended coefficient cost is exactly `standardRepresentationNorm`; and the
abstract Souza-Besov cost of `f` is bounded by the real value of that standard
norm.
-/
theorem finite_standardRepresentationNorm_implies_memBesov_and_standardRepresentation
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (hN : standardRepresentationNorm G F s hs p hp_top q f hf ≠ ∞) :
    ∃ hfLp : MemLp f p G.grid.μ,
      ∃ g : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top),
        ∃ R :
          WeakGridSpace.LpGridRepresentation
            (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
            (g : Lp ℂ p G.toWeakGridSpace.measure),
          (g : Lp ℂ p G.toWeakGridSpace.measure) = hfLp.toLp f ∧
            R.block = canonicalStandardBlockSeq G F s hs p hp_top f hf ∧
              WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
                WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R =
                  standardRepresentationNorm G F s hs p hp_top q f hf ∧
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
                    (standardRepresentationNorm G F s hs p hp_top q f hf).toReal ∧
                    WeakGridSpace.BesovishSpace.Norm_Costpq
                        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q g ≤
                      (standardRepresentationNorm G F s hs p hp_top q f hf).toReal := by
  classical
  rcases finite_standardRepresentationNorm_implies_memLp_and_hasSum
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q)
      f hf hN with
    ⟨hfLp, hstandard_sum⟩
  let R₀ :
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
        (hfLp.toLp f) :=
    { block := canonicalStandardBlockSeq G F s hs p hp_top f hf
      hasSum := hstandard_sum }
  have hRenn_eq :
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R₀ =
        standardRepresentationNorm G F s hs p hp_top q f hf := by
    by_cases hq : q = ∞
    · simp [WeakGridSpace.LpGridRepresentation.pqCostENNReal,
        standardRepresentationNorm, hq, R₀,
        WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        standardBlockCoeffPower, canonicalStandardBlockSeq]
    · simp [WeakGridSpace.LpGridRepresentation.pqCostENNReal,
        standardRepresentationNorm, hq, R₀,
        WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        standardBlockCoeffPower, canonicalStandardBlockSeq]
  have hRenn_le :
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R₀ ≤
        ENNReal.ofReal (standardRepresentationNorm G F s hs p hp_top q f hf).toReal := by
    rw [hRenn_eq, ENNReal.ofReal_toReal hN]
  have hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R₀ :=
    WeakGridSpace.LpGridRepresentation.finitePQCost_of_pqCostENNReal_le
      R₀ (Fact.out : 1 ≤ q) hRenn_le
  have hRcost_le :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R₀ ≤
        (standardRepresentationNorm G F s hs p hp_top q f hf).toReal :=
    pqCost_le_of_pqCostENNReal_le R₀ hRenn_le ENNReal.toReal_nonneg
  have hmem :
      hfLp.toLp f ∈ SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top) := by
    change
      WeakGridSpace.MemBesovishCoeffCost
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q (hfLp.toLp f)
    exact ⟨R₀, by simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost] using hRfin⟩
  let g : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top) := ⟨hfLp.toLp f, hmem⟩
  let R :
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
        (g : Lp ℂ p G.toWeakGridSpace.measure) := R₀
  have hBesov_le_cost :
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q g ≤
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
      (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
      (q := q) g R (by simpa [R] using hRfin)
  refine ⟨hfLp, g, R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa [R] using hRfin
  · simpa [R] using hRenn_eq
  · simpa [R] using hRcost_le
  · exact hBesov_le_cost.trans (by simpa [R] using hRcost_le)

end StandardAtomicRepresentation

end

end GoodGridSpace
