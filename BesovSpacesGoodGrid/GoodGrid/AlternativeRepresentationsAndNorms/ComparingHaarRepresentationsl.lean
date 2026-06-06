import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.HaarParametrizedRepresentation
import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.standardRepresentation

/-!
# Comparing the two Haar coefficient gauges

This file records the comparison between the paper's `L²`-normalized Haar
coefficient gauge and the parametrized Haar gauge.  The intended consequence is
that finite `N_haar` cost for an integrable function forces finite
parametrized Haar cost, and conversely, with uniform multiplicative bounds.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

private theorem indexL2NormSq_pos (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (i : F.Index) :
    0 < F.indexL2NormSq (HaarRepresentation.GridOf G) i := by
  have hnonneg :
      0 ≤ F.indexL2NormSq (HaarRepresentation.GridOf G) i := by
    rw [← F.integral_function_mul_self_eq_indexL2NormSq (HaarRepresentation.GridOf G) i]
    exact integral_nonneg fun x => mul_self_nonneg _
  exact lt_of_le_of_ne hnonneg
    (F.indexL2NormSq_ne_zero (HaarRepresentation.GridOf G) i).symm

private theorem l2NormalizationFactor_alpha
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G)) :
    HaarRepresentation.l2NormalizationFactor G F .alpha =
      Real.sqrt (G.grid.μ Set.univ).toReal := by
  let μI := (G.grid.μ Set.univ).toReal
  have hμI_pos : 0 < μI := by
    have hμ_pos : 0 < G.grid.μ Set.univ :=
      G.grid.positive_measure 0 Set.univ (by simp [G.grid.grid.first_partition_eq_univ])
    have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ := by
      letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Set.univ
    exact ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
  have hμI_ne : μI ≠ 0 := hμI_pos.ne'
  calc
    HaarRepresentation.l2NormalizationFactor G F .alpha
        = (Real.sqrt (1 / μI))⁻¹ := by
          simp [HaarRepresentation.l2NormalizationFactor, μI]
    _ = Real.sqrt μI := by
        have hsqrt_inv : Real.sqrt (1 / μI) = (Real.sqrt μI)⁻¹ := by
          rw [show 1 / μI = μI⁻¹ by ring, Real.sqrt_inv μI]
        rw [hsqrt_inv, inv_inv]

private theorem l2Scale_alpha
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) :
    HaarParametrizedRepresentation.l2Scale G F s p .alpha =
      (G.grid.μ Set.univ).toReal ^ (s - 1 / p.toReal - 1 / 2) := by
  let μI := (G.grid.μ Set.univ).toReal
  have hμI_pos : 0 < μI := by
    have hμ_pos : 0 < G.grid.μ Set.univ :=
      G.grid.positive_measure 0 Set.univ (by simp [G.grid.grid.first_partition_eq_univ])
    have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ := by
      letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Set.univ
    exact ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
  calc
    HaarParametrizedRepresentation.l2Scale G F s p .alpha
        = μI ^ (s - 1 / p.toReal) / Real.sqrt μI := by
          simp [HaarParametrizedRepresentation.l2Scale,
            HaarParametrizedRepresentation.rawScale,
            HaarParametrizedRepresentation.supportMeasure,
            HaarRepresentation.support, l2NormalizationFactor_alpha G F, μI]
    _ = μI ^ (s - 1 / p.toReal - 1 / 2) := by
        rw [Real.sqrt_eq_rpow]
        rw [div_eq_mul_inv, ← Real.rpow_neg hμI_pos.le,
          ← Real.rpow_add hμI_pos]
        ring_nf

private theorem ennreal_toReal_pos_of_one_le_lt_top (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp_top : p < ∞) :
    0 < p.toReal := by
  exact ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp_top.ne

private theorem goodGridCell_toReal_pos
    {G : GoodGridSpace (α := α)} (Q : GoodGridCell G) :
    0 < (G.grid.μ Q.cell).toReal :=
  ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)

private theorem univ_toReal_pos (G : GoodGridSpace (α := α)) :
    0 < (G.grid.μ Set.univ).toReal := by
  have hμ_pos : 0 < G.grid.μ Set.univ :=
    G.grid.positive_measure 0 Set.univ (by simp [G.grid.grid.first_partition_eq_univ])
  have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ := by
    letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ Set.univ
  exact ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top

private theorem fatherParametrizedCoeff_norm_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    ‖HaarParametrizedRepresentation.parametrizedCoeff G F s p f hf .alpha‖ =
      (G.grid.μ Set.univ).toReal *
        ((G.grid.μ Set.univ).toReal ^ (1 / p.toReal - s - 1 / 2) *
          ‖HaarRepresentation.Coeff G F f hf .alpha‖) := by
  let μI := (G.grid.μ Set.univ).toReal
  have hμI_pos : 0 < μI := by
    simpa [μI] using univ_toReal_pos G
  have hscale_pos : 0 < μI ^ (s - 1 / p.toReal - 1 / 2) :=
    Real.rpow_pos_of_pos hμI_pos _
  rw [HaarParametrizedRepresentation.parametrizedCoeff, l2Scale_alpha G F s p]
  rw [norm_div]
  simp only [Complex.norm_real]
  rw [Real.norm_of_nonneg hscale_pos.le]
  calc
    ‖HaarRepresentation.Coeff G F f hf .alpha‖ /
        μI ^ (s - 1 / p.toReal - 1 / 2)
        =
      ‖HaarRepresentation.Coeff G F f hf .alpha‖ *
          μI ^ (-(s - 1 / p.toReal - 1 / 2)) := by
        rw [div_eq_mul_inv, Real.rpow_neg hμI_pos.le]
    _ = μI * (μI ^ (1 / p.toReal - s - 1 / 2) *
            ‖HaarRepresentation.Coeff G F f hf .alpha‖) := by
        have hpow :
            μI ^ (-(s - 1 / p.toReal - 1 / 2)) =
              μI * μI ^ (1 / p.toReal - s - 1 / 2) := by
          calc
            μI ^ (-(s - 1 / p.toReal - 1 / 2))
                = μI ^ (1 + (1 / p.toReal - s - 1 / 2)) := by
                  congr 1
                  ring
            _ = μI ^ (1 : ℝ) * μI ^ (1 / p.toReal - s - 1 / 2) := by
                  rw [Real.rpow_add hμI_pos]
            _ = μI * μI ^ (1 / p.toReal - s - 1 / 2) := by
                  rw [Real.rpow_one]
        rw [hpow]
        ring
    _ = (G.grid.μ Set.univ).toReal *
        ((G.grid.μ Set.univ).toReal ^ (1 / p.toReal - s - 1 / 2) *
          ‖HaarRepresentation.Coeff G F f hf .alpha‖) := by
          simp [μI]

private theorem fatherCoeffNorm_eq_univ_mul_fatherTerm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    HaarParametrizedRepresentation.fatherCoeffNorm G F s p f hf =
      ENNReal.ofReal (G.grid.μ Set.univ).toReal *
        HaarRepresentation.fatherTerm G F s p f hf := by
  let μI := (G.grid.μ Set.univ).toReal
  have hμI_pos : 0 < μI := by
    simpa [μI] using univ_toReal_pos G
  calc
    HaarParametrizedRepresentation.fatherCoeffNorm G F s p f hf
        =
      ENNReal.ofReal
        (μI *
          (μI ^ (1 / p.toReal - s - 1 / 2) *
            ‖HaarRepresentation.Coeff G F f hf .alpha‖)) := by
        simp [HaarParametrizedRepresentation.fatherCoeffNorm,
          fatherParametrizedCoeff_norm_eq G F s p f hf, μI]
    _ =
      ENNReal.ofReal μI *
        ENNReal.ofReal
          (μI ^ (1 / p.toReal - s - 1 / 2) *
            ‖HaarRepresentation.Coeff G F f hf .alpha‖) := by
        rw [ENNReal.ofReal_mul hμI_pos.le]
    _ =
      ENNReal.ofReal (G.grid.μ Set.univ).toReal *
        HaarRepresentation.fatherTerm G F s p f hf := by
        simp [HaarRepresentation.fatherTerm, μI]

private theorem wavelet_l2Scale_eq_sqrt_indexL2NormSq_mul_support_rpow
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (i : F.toHaarSystem.Index) :
    HaarParametrizedRepresentation.l2Scale G F s p (.wavelet i) =
      Real.sqrt (F.indexL2NormSq (HaarRepresentation.GridOf G) (.wavelet i)) *
        (G.grid.μ (HaarRepresentation.support G F (.wavelet i))).toReal ^
          (s + 1 - 1 / p.toReal) := by
  simp [HaarParametrizedRepresentation.l2Scale, HaarParametrizedRepresentation.rawScale,
    HaarParametrizedRepresentation.supportMeasure, HaarRepresentation.l2NormalizationFactor,
    div_eq_mul_inv, mul_comm, inv_inv]

private theorem wavelet_l2Scale_eq_branch_measures
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    HaarParametrizedRepresentation.l2Scale G F s p
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) =
      Real.sqrt
          ((1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal) +
            (1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal)) *
        (G.grid.μ
            (UnbalancedHaarWavelet.branchSupport b.1.1 ∪
              UnbalancedHaarWavelet.branchSupport b.1.2)).toReal ^
          (s + 1 - 1 / p.toReal) := by
  classical
  simp [wavelet_l2Scale_eq_sqrt_indexL2NormSq_mul_support_rpow,
    HaarRepresentation.indexOfCellBranch, HaarRepresentation.support,
    UnbalancedHaarWavelet.HaarSystem.Index.branchSupport,
    UnbalancedHaarWavelet.haarBranchSupport_eq_union_branchSupport]

private theorem rpow_comparable_of_mul_le_le
    {c x q e : ℝ} (hc : 0 < c) (hx : 0 < x) (hq : 0 < q)
    (hcx : c * q ≤ x) (hxq : x ≤ q) :
    min (c ^ e) 1 * q ^ e ≤ x ^ e ∧
      x ^ e ≤ max (c ^ e) 1 * q ^ e := by
  have hcq_pos : 0 < c * q := mul_pos hc hq
  have hc_le_one : c ≤ 1 := by
    have h : c * q ≤ 1 * q := by
      simpa using hcx.trans hxq
    nlinarith
  have hratio_pos : 0 < x / q := div_pos hx hq
  have hc_le_ratio : c ≤ x / q := by
    exact (le_div_iff₀ hq).2 hcx
  have hratio_le_one : x / q ≤ 1 := by
    exact (div_le_one hq).2 hxq
  have hx_eq : (x / q) * q = x := by
    field_simp [hq.ne']
  have hpow_eq : x ^ e = (x / q) ^ e * q ^ e := by
    calc
      x ^ e = ((x / q) * q) ^ e := by rw [hx_eq]
      _ = (x / q) ^ e * q ^ e := by
          rw [Real.mul_rpow hratio_pos.le hq.le]
  have hqpow_nonneg : 0 ≤ q ^ e := Real.rpow_nonneg hq.le e
  constructor
  · rw [hpow_eq]
    refine mul_le_mul_of_nonneg_right ?_ hqpow_nonneg
    by_cases he : 0 ≤ e
    · have hc_pow_le : c ^ e ≤ (x / q) ^ e :=
        Real.rpow_le_rpow hc.le hc_le_ratio he
      exact (min_le_left (c ^ e) 1).trans (hc_pow_le)
    · have he_nonpos : e ≤ 0 := le_of_not_ge he
      have hratio_pow_le : (x / q) ^ e ≤ c ^ e :=
        Real.rpow_le_rpow_of_nonpos hc hc_le_ratio he_nonpos
      have hone_le_ratio_pow : 1 ≤ (x / q) ^ e := by
        have h := Real.rpow_le_rpow_of_nonpos hratio_pos hratio_le_one he_nonpos
        simpa using h
      exact (min_le_right (c ^ e) 1).trans hone_le_ratio_pow
  · rw [hpow_eq]
    refine mul_le_mul_of_nonneg_right ?_ hqpow_nonneg
    by_cases he : 0 ≤ e
    · have hratio_pow_le_one : (x / q) ^ e ≤ 1 := by
        have h := Real.rpow_le_rpow hratio_pos.le hratio_le_one he
        simpa using h
      exact hratio_pow_le_one.trans (le_max_right (c ^ e) 1)
    · have he_nonpos : e ≤ 0 := le_of_not_ge he
      have hratio_pow_le : (x / q) ^ e ≤ c ^ e :=
        Real.rpow_le_rpow_of_nonpos hc hc_le_ratio he_nonpos
      exact hratio_pow_le.trans (le_max_left (c ^ e) 1)

private theorem rpow_neg_half_eq_sqrt_inv {q : ℝ} (hq : 0 < q) :
    q ^ (-(1 : ℝ) / 2) = Real.sqrt q⁻¹ := by
  calc
    q ^ (-(1 : ℝ) / 2) = (q ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring]
      rw [Real.rpow_neg hq.le]
    _ = (Real.sqrt q)⁻¹ := by rw [Real.sqrt_eq_rpow]
    _ = Real.sqrt q⁻¹ := by rw [← Real.sqrt_inv]

/--
The scale relating the parametrized wavelet to the `L²`-normalized wavelet is
uniformly comparable with the parent-cell factor
`μ(Q)^(s + 1 / 2 - 1 / p)`.

This is the geometric heart of the comparison.  The proof uses that the two
branch supports are nonempty unions of children of `Q`: each child has measure
bounded below by `lambda1 * μ(Q)`, while the union of the two branch supports is
contained in `Q`.  Consequently the `L²` square norm
`1 / μ(left) + 1 / μ(right)` is comparable with `1 / μ(Q)`.
-/
theorem exists_wavelet_l2Scale_comparable_parent
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp_top : p < ∞) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (Q : GoodGridCell G)
        (b : {r : Finset (Set α) × Finset (Set α) //
          r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}),
        let μQ := (G.grid.μ Q.cell).toReal
        A * μQ ^ (s + 1 / 2 - 1 / p.toReal) ≤
          ‖((HaarParametrizedRepresentation.l2Scale G F s p
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) : ℝ) : ℂ)‖ ∧
        ‖((HaarParametrizedRepresentation.l2Scale G F s p
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) : ℝ) : ℂ)‖ ≤
          B * μQ ^ (s + 1 / 2 - 1 / p.toReal) := by
  classical
  let lam := G.grid.lambda1
  let e := s + 1 - 1 / p.toReal
  refine ⟨min ((2 * lam) ^ e) 1, Real.sqrt (2 / lam) * max ((2 * lam) ^ e) 1, ?_, ?_, ?_⟩
  · exact lt_min (Real.rpow_pos_of_pos (mul_pos (by norm_num) G.grid.hlambda1_pos) e)
      zero_lt_one
  · exact mul_pos (Real.sqrt_pos.2 (div_pos (by norm_num) G.grid.hlambda1_pos))
      (lt_max_of_lt_right zero_lt_one)
  · intro Q b
    let A := UnbalancedHaarWavelet.branchSupport b.1.1
    let B := UnbalancedHaarWavelet.branchSupport b.1.2
    let a := (G.grid.μ A).toReal
    let bμ := (G.grid.μ B).toReal
    let u := (G.grid.μ (A ∪ B)).toReal
    let q := (G.grid.μ Q.cell).toReal
    have hq_pos : 0 < q := by
      simpa [q] using goodGridCell_toReal_pos Q
    have ha_pos : 0 < a := by
      simpa [a, A] using StandardAtomicRepresentation.branchSupport_toReal_pos_left G F Q b
    have hb_pos : 0 < bμ := by
      simpa [bμ, B] using StandardAtomicRepresentation.branchSupport_toReal_pos_right G F Q b
    have hleft_lower : lam * q ≤ a := by
      simpa [lam, q, a, A] using
        StandardAtomicRepresentation.branchSupport_toReal_lower_left G F Q b
    have hright_lower : lam * q ≤ bμ := by
      simpa [lam, q, bμ, B] using
        StandardAtomicRepresentation.branchSupport_toReal_lower_right G F Q b
    have hsum_upper : a + bμ ≤ q := by
      simpa [q, a, bμ, A, B] using
        StandardAtomicRepresentation.branchSupport_toReal_add_le_parent G F Q b
    have hdisj : Disjoint A B := by
      simpa [A, B] using
        F.toHaarSystem.branchSupport_components_disjoint (HaarRepresentation.GridOf G) b
    have hB_meas : MeasurableSet B := by
      simpa [B] using StandardAtomicRepresentation.measurableSet_branchSupport_right G F Q b
    have hu_eq_sum : u = a + bμ := by
      letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
      have hmeasure_union : G.grid.μ (A ∪ B) = G.grid.μ A + G.grid.μ B :=
        MeasureTheory.measure_union hdisj hB_meas
      have hleft_ne_top : G.grid.μ A ≠ ∞ := MeasureTheory.measure_ne_top G.grid.μ A
      have hright_ne_top : G.grid.μ B ≠ ∞ := MeasureTheory.measure_ne_top G.grid.μ B
      simp [u, a, bμ, hmeasure_union, ENNReal.toReal_add hleft_ne_top hright_ne_top]
    have hu_pos : 0 < u := by
      rw [hu_eq_sum]
      exact add_pos ha_pos hb_pos
    have hu_upper : u ≤ q := by
      rw [hu_eq_sum]
      exact hsum_upper
    have hu_lower : (2 * lam) * q ≤ u := by
      rw [hu_eq_sum]
      nlinarith [hleft_lower, hright_lower]
    have hrpow := rpow_comparable_of_mul_le_le
      (mul_pos (by norm_num) G.grid.hlambda1_pos) hu_pos hq_pos hu_lower hu_upper
      (e := e)
    have hsqrt_lower : q ^ (-(1 : ℝ) / 2) ≤ Real.sqrt (1 / a + 1 / bμ) := by
      have ha_le_q : a ≤ q := le_trans (by nlinarith [hb_pos]) hsum_upper
      have hinv_le : 1 / q ≤ 1 / a := by
        exact one_div_le_one_div_of_le ha_pos ha_le_q
      have hsum_le : 1 / q ≤ 1 / a + 1 / bμ := by
        exact hinv_le.trans (le_add_of_nonneg_right (one_div_nonneg.2 hb_pos.le))
      have hqpow_eq : q ^ (-(1 : ℝ) / 2) = Real.sqrt (1 / q) := by
        simpa [one_div] using rpow_neg_half_eq_sqrt_inv hq_pos
      rw [hqpow_eq]
      exact Real.sqrt_le_sqrt hsum_le
    have hsqrt_upper :
        Real.sqrt (1 / a + 1 / bμ) ≤ Real.sqrt (2 / lam) * q ^ (-(1 : ℝ) / 2) := by
      have hlamq_pos : 0 < lam * q := mul_pos G.grid.hlambda1_pos hq_pos
      have hinv_a : 1 / a ≤ 1 / (lam * q) :=
        one_div_le_one_div_of_le hlamq_pos hleft_lower
      have hinv_b : 1 / bμ ≤ 1 / (lam * q) :=
        one_div_le_one_div_of_le hlamq_pos hright_lower
      have hsum_inv : 1 / a + 1 / bμ ≤ 2 / (lam * q) := by
        calc
          1 / a + 1 / bμ ≤ 1 / (lam * q) + 1 / (lam * q) :=
            add_le_add hinv_a hinv_b
          _ = 2 / (lam * q) := by ring
      have hrewrite :
          Real.sqrt (2 / lam) * q ^ (-(1 : ℝ) / 2) = Real.sqrt (2 / (lam * q)) := by
        have h2lam_nonneg : 0 ≤ 2 / lam := div_nonneg (by norm_num) G.grid.hlambda1_pos.le
        rw [rpow_neg_half_eq_sqrt_inv hq_pos]
        rw [← Real.sqrt_mul h2lam_nonneg]
        congr 1
        field_simp [G.grid.hlambda1_pos.ne', hq_pos.ne']
      rw [hrewrite]
      exact Real.sqrt_le_sqrt hsum_inv
    have hscale :
        HaarParametrizedRepresentation.l2Scale G F s p
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) =
          Real.sqrt (1 / a + 1 / bμ) * u ^ e := by
      simpa [a, bμ, u, A, B, e] using wavelet_l2Scale_eq_branch_measures G F s p Q b
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 / a + 1 / bμ) := Real.sqrt_nonneg _
    have hu_pow_nonneg : 0 ≤ u ^ e := Real.rpow_nonneg hu_pos.le e
    have hscale_nonneg :
        0 ≤ HaarParametrizedRepresentation.l2Scale G F s p
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) := by
      rw [hscale]
      exact mul_nonneg hsqrt_nonneg hu_pow_nonneg
    have hnorm :
        ‖((HaarParametrizedRepresentation.l2Scale G F s p
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) : ℝ) : ℂ)‖ =
          HaarParametrizedRepresentation.l2Scale G F s p
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) := by
      simp [Complex.norm_real, Real.norm_of_nonneg hscale_nonneg]
    constructor
    · rw [hnorm, hscale]
      have hprod :
          min ((2 * lam) ^ e) 1 * q ^ e * q ^ (-(1 : ℝ) / 2) ≤
            u ^ e * Real.sqrt (1 / a + 1 / bμ) := by
        exact mul_le_mul hrpow.1 hsqrt_lower (Real.rpow_nonneg hq_pos.le _)
          hu_pow_nonneg
      calc
        min ((2 * lam) ^ e) 1 * q ^ (s + 1 / 2 - 1 / p.toReal)
            =
          min ((2 * lam) ^ e) 1 * q ^ e * q ^ (-(1 : ℝ) / 2) := by
            calc
              min ((2 * lam) ^ e) 1 * q ^ (s + 1 / 2 - 1 / p.toReal)
                  = min ((2 * lam) ^ e) 1 * (q ^ e * q ^ (-(1 : ℝ) / 2)) := by
                    rw [← Real.rpow_add hq_pos]
                    congr 2
                    simp [e]
                    ring
              _ = min ((2 * lam) ^ e) 1 * q ^ e * q ^ (-(1 : ℝ) / 2) := by ring
        _ ≤ u ^ e * Real.sqrt (1 / a + 1 / bμ) := hprod
        _ = Real.sqrt (1 / a + 1 / bμ) * u ^ e := by ring
    · rw [hnorm, hscale]
      have hprod :
          Real.sqrt (1 / a + 1 / bμ) * u ^ e ≤
            (Real.sqrt (2 / lam) * q ^ (-(1 : ℝ) / 2)) *
              (max ((2 * lam) ^ e) 1 * q ^ e) := by
        exact mul_le_mul hsqrt_upper hrpow.2 hu_pow_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hq_pos.le _))
      calc
        Real.sqrt (1 / a + 1 / bμ) * u ^ e
            ≤ (Real.sqrt (2 / lam) * q ^ (-(1 : ℝ) / 2)) *
                (max ((2 * lam) ^ e) 1 * q ^ e) := hprod
        _ = Real.sqrt (2 / lam) * max ((2 * lam) ^ e) 1 *
              q ^ (s + 1 / 2 - 1 / p.toReal) := by
            calc
              (Real.sqrt (2 / lam) * q ^ (-(1 : ℝ) / 2)) *
                  (max ((2 * lam) ^ e) 1 * q ^ e)
                  = Real.sqrt (2 / lam) * max ((2 * lam) ^ e) 1 *
                      (q ^ e * q ^ (-(1 : ℝ) / 2)) := by ring
              _ = Real.sqrt (2 / lam) * max ((2 * lam) ^ e) 1 *
                    q ^ (s + 1 / 2 - 1 / p.toReal) := by
                    rw [← Real.rpow_add hq_pos]
                    congr 2
                    simp [e]
                    ring

/--
The father-function scale is comparable with the father weight used by the
paper's `L²`-normalized Haar gauge.

The extra factor is only a fixed power of `μ(univ)`, so it is absorbed into a
constant depending on the grid and the parameters.
-/
theorem exists_fatherCoeffNorm_comparable_fatherTerm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp_top : p < ∞) :
    ∃ A B : ℝ≥0∞, A ≠ ∞ ∧ B ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ),
        HaarParametrizedRepresentation.fatherCoeffNorm G F s p f hf ≤
          A * HaarRepresentation.fatherTerm G F s p f hf ∧
        HaarRepresentation.fatherTerm G F s p f hf ≤
          B * HaarParametrizedRepresentation.fatherCoeffNorm G F s p f hf := by
  let μI := (G.grid.μ Set.univ).toReal
  have hμI_pos : 0 < μI := by
    simpa [μI] using univ_toReal_pos G
  refine ⟨ENNReal.ofReal μI, ENNReal.ofReal μI⁻¹, ?_, ?_, ?_⟩
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_ne_top
  · intro f hf
    have hfather := fatherCoeffNorm_eq_univ_mul_fatherTerm G F s p f hf
    constructor
    · rw [hfather]
    · rw [hfather]
      calc
        HaarRepresentation.fatherTerm G F s p f hf
            = 1 * HaarRepresentation.fatherTerm G F s p f hf := by simp
        _ ≤
            (ENNReal.ofReal μI⁻¹ * ENNReal.ofReal μI) *
              HaarRepresentation.fatherTerm G F s p f hf := by
              have hone_le :
                  (1 : ℝ≥0∞) ≤ ENNReal.ofReal μI⁻¹ * ENNReal.ofReal μI := by
                rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hμI_pos.le)]
                rw [inv_mul_cancel₀ hμI_pos.ne']
                simp
              exact mul_le_mul_left hone_le _
        _ =
            ENNReal.ofReal μI⁻¹ *
              (ENNReal.ofReal μI * HaarRepresentation.fatherTerm G F s p f hf) := by
              rw [mul_assoc]

private theorem wavelet_parametrizedCoeff_norm_eq_coeff_norm_div_scale_norm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    ‖HaarParametrizedRepresentation.parametrizedCoeff G F s p f hf
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ =
      ‖HaarRepresentation.Coeff G F f hf
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ /
        ‖((HaarParametrizedRepresentation.l2Scale G F s p
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) : ℝ) : ℂ)‖ := by
  simp [HaarParametrizedRepresentation.parametrizedCoeff]

private theorem real_coeff_div_scale_pow_le
    {A q scale d pR r : ℝ} (hA : 0 < A) (hq : 0 < q) (hp : 0 < pR)
    (hd_nonneg : 0 ≤ d) (hscale : A * q ^ r ≤ scale) :
    (d / scale) ^ pR ≤ A ^ (-pR) * q ^ (-r * pR) * d ^ pR := by
  have hweight_pos : 0 < A * q ^ r :=
    mul_pos hA (Real.rpow_pos_of_pos hq r)
  have hscale_pos : 0 < scale := lt_of_lt_of_le hweight_pos hscale
  have hscale_inv_le : scale⁻¹ ≤ (A * q ^ r)⁻¹ :=
    inv_anti₀ hweight_pos hscale
  have hdiv_le : d / scale ≤ d / (A * q ^ r) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hscale_inv_le hd_nonneg
  have hdiv_nonneg : 0 ≤ d / scale := div_nonneg hd_nonneg hscale_pos.le
  have htarget_nonneg : 0 ≤ d / (A * q ^ r) :=
    div_nonneg hd_nonneg hweight_pos.le
  calc
    (d / scale) ^ pR ≤ (d / (A * q ^ r)) ^ pR :=
      Real.rpow_le_rpow hdiv_nonneg hdiv_le hp.le
    _ = A ^ (-pR) * q ^ (-r * pR) * d ^ pR := by
      rw [div_eq_mul_inv]
      rw [Real.mul_rpow hd_nonneg (inv_nonneg.2 hweight_pos.le)]
      rw [Real.inv_rpow hweight_pos.le]
      rw [Real.mul_rpow hA.le (Real.rpow_pos_of_pos hq r).le]
      rw [Real.rpow_mul hq.le]
      rw [Real.rpow_neg hA.le]
      have hq_r_pos : 0 < q ^ r := Real.rpow_pos_of_pos hq r
      have hq_target : (q ^ r) ^ pR = q ^ (r * pR) := by
        rw [← Real.rpow_mul hq.le]
      rw [hq_target]
      have hq_rhs : (q ^ (-r)) ^ pR = (q ^ (r * pR))⁻¹ := by
        calc
          (q ^ (-r)) ^ pR = q ^ ((-r) * pR) := by
            rw [← Real.rpow_mul hq.le]
          _ = q ^ (-(r * pR)) := by
            congr 1
            ring
          _ = (q ^ (r * pR))⁻¹ := by
            rw [Real.rpow_neg hq.le]
      rw [hq_rhs]
      field_simp [Real.rpow_pos_of_pos hA pR |>.ne',
        Real.rpow_pos_of_pos hq (r * pR) |>.ne']

private theorem real_weighted_coeff_pow_le_scale_div
    {B q scale d pR r : ℝ} (hB : 0 < B) (hq : 0 < q) (hscale_pos : 0 < scale)
    (hp : 0 < pR) (hd_nonneg : 0 ≤ d) (hscale : scale ≤ B * q ^ r) :
    q ^ (-r * pR) * d ^ pR ≤ B ^ pR * (d / scale) ^ pR := by
  have hscale_nonneg : 0 ≤ scale := hscale_pos.le
  have hBqr_pos : 0 < B * q ^ r := mul_pos hB (Real.rpow_pos_of_pos hq r)
  have hscale_pow_le : scale ^ pR ≤ (B * q ^ r) ^ pR :=
    Real.rpow_le_rpow hscale_nonneg hscale hp.le
  have hdiv_nonneg : 0 ≤ d / scale := div_nonneg hd_nonneg hscale_pos.le
  have hscale_pow_nonneg : 0 ≤ scale ^ pR := Real.rpow_nonneg hscale_pos.le _
  have hd_eq : (d / scale) * scale = d := by
    field_simp [hscale_pos.ne']
  have hd_pow_eq : d ^ pR = (d / scale) ^ pR * scale ^ pR := by
    calc
      d ^ pR = ((d / scale) * scale) ^ pR := by rw [hd_eq]
      _ = (d / scale) ^ pR * scale ^ pR := by
        rw [Real.mul_rpow hdiv_nonneg hscale_pos.le]
  calc
    q ^ (-r * pR) * d ^ pR
        = q ^ (-r * pR) * ((d / scale) ^ pR * scale ^ pR) := by rw [hd_pow_eq]
    _ ≤ q ^ (-r * pR) * ((d / scale) ^ pR * (B * q ^ r) ^ pR) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hscale_pow_le (Real.rpow_nonneg hdiv_nonneg _))
        (Real.rpow_nonneg hq.le _)
    _ = B ^ pR * (d / scale) ^ pR := by
      rw [Real.mul_rpow hB.le (Real.rpow_pos_of_pos hq r).le]
      rw [← Real.rpow_mul hq.le]
      have hcancel : q ^ (-r * pR) * q ^ (r * pR) = 1 := by
        rw [← Real.rpow_add hq]
        ring_nf
        rw [Real.rpow_zero]
      calc
        q ^ (-r * pR) * ((d / scale) ^ pR * (B ^ pR * q ^ (r * pR)))
            = B ^ pR * (d / scale) ^ pR *
                (q ^ (-r * pR) * q ^ (r * pR)) := by ring
        _ = B ^ pR * (d / scale) ^ pR := by rw [hcancel, mul_one]

/--
The wavelet part of the parametrized gauge is controlled level by level by the
wavelet part of the paper's `L²`-normalized Haar gauge.
-/
theorem exists_levelCoeffNorm_le_const_mul_levelHaarBlock_root
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ),
        HaarParametrizedRepresentation.levelCoeffNorm G F s p f hf k ≤
          C * (HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / p.toReal) := by
  classical
  rcases exists_wavelet_l2Scale_comparable_parent G F s p hp_top with
    ⟨A, B, hA_pos, _hB_pos, hscale⟩
  let C : ℝ≥0∞ := ENNReal.ofReal A⁻¹
  refine ⟨C, ENNReal.ofReal_ne_top, ?_⟩
  intro f hf k
  let pR := p.toReal
  have hpR_pos : 0 < pR := ennreal_toReal_pos_of_one_le_lt_top p hp_top
  have hpR_nonneg : 0 ≤ pR := hpR_pos.le
  have hpower :
      HaarParametrizedRepresentation.levelCoeffPower G F s p f hf k ≤
        (ENNReal.ofReal A) ^ (-pR) *
          HaarRepresentation.levelHaarBlock G F s p f hf k := by
    simp only [HaarParametrizedRepresentation.levelCoeffPower,
      HaarRepresentation.levelHaarBlock]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro Q hQ
    let Qcell : GoodGridCell G :=
      { level := k
        cell := Q.1
        mem := Q.2 }
    let μQ := (G.grid.μ Q.1).toReal
    have hμQ_pos : 0 < μQ := by
      simpa [μQ, Qcell] using goodGridCell_toReal_pos (G := G) Qcell
    simp only [HaarParametrizedRepresentation.cellCoeffPower,
      HaarRepresentation.cellCoeffPower]
    rw [← mul_assoc]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro b hb
    let scaleNorm :=
      ‖((HaarParametrizedRepresentation.l2Scale G F s p
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Qcell b)) : ℝ) : ℂ)‖
    let d :=
      ‖HaarRepresentation.Coeff G F f hf
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Qcell b))‖
    have hscale_lower :
        A * μQ ^ (s + 1 / 2 - 1 / pR) ≤ scaleNorm := by
      simpa [μQ, Qcell, scaleNorm, pR] using (hscale Qcell b).1
    have hreal :
        (d / scaleNorm) ^ pR ≤
          A ^ (-pR) * μQ ^ (1 - s * pR - pR / 2) * d ^ pR := by
      have hexp : -(s + 1 / 2 - 1 / pR) * pR = 1 - s * pR - pR / 2 := by
        field_simp [hpR_pos.ne']
        ring
      calc
        (d / scaleNorm) ^ pR ≤
            A ^ (-pR) * μQ ^ (-(s + 1 / 2 - 1 / pR) * pR) * d ^ pR :=
          real_coeff_div_scale_pow_le hA_pos hμQ_pos hpR_pos (norm_nonneg _) hscale_lower
        _ = A ^ (-pR) * μQ ^ (1 - s * pR - pR / 2) * d ^ pR := by
          rw [hexp]
    have hterm :
        ENNReal.ofReal
            (‖HaarParametrizedRepresentation.parametrizedCoeff G F s p f hf
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Qcell b))‖ ^ pR)
          ≤
        (ENNReal.ofReal A) ^ (-pR) *
          (ENNReal.ofReal (μQ ^ (1 - s * pR - pR / 2)) *
            ENNReal.ofReal (d ^ pR)) := by
      rw [wavelet_parametrizedCoeff_norm_eq_coeff_norm_div_scale_norm]
      change ENNReal.ofReal ((d / scaleNorm) ^ pR) ≤
        (ENNReal.ofReal A) ^ (-pR) *
          (ENNReal.ofReal (μQ ^ (1 - s * pR - pR / 2)) *
            ENNReal.ofReal (d ^ pR))
      calc
        ENNReal.ofReal ((d / scaleNorm) ^ pR)
            ≤ ENNReal.ofReal (A ^ (-pR) * μQ ^ (1 - s * pR - pR / 2) * d ^ pR) :=
              ENNReal.ofReal_le_ofReal hreal
        _ =
          (ENNReal.ofReal A) ^ (-pR) *
            (ENNReal.ofReal (μQ ^ (1 - s * pR - pR / 2)) *
              ENNReal.ofReal (d ^ pR)) := by
            have hA_nonneg : 0 ≤ A ^ (-pR) := Real.rpow_nonneg hA_pos.le _
            have hμ_nonneg : 0 ≤ μQ ^ (1 - s * pR - pR / 2) :=
              Real.rpow_nonneg hμQ_pos.le _
            have hd_pow_nonneg : 0 ≤ d ^ pR := Real.rpow_nonneg (norm_nonneg _) _
            rw [ENNReal.ofReal_mul (mul_nonneg hA_nonneg hμ_nonneg)]
            rw [ENNReal.ofReal_mul hA_nonneg]
            rw [ENNReal.ofReal_rpow_of_pos hA_pos]
            ring
    simpa [HaarParametrizedRepresentation.cellCoeffPower,
      HaarRepresentation.cellCoeffPower, HaarRepresentation.indicesInCell, Qcell, μQ, d, pR,
      mul_assoc] using hterm
  have hroot :
      HaarParametrizedRepresentation.levelCoeffNorm G F s p f hf k ≤
        ((ENNReal.ofReal A) ^ (-pR) *
          HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / pR) := by
    simp [HaarParametrizedRepresentation.levelCoeffNorm, pR]
    exact ENNReal.rpow_le_rpow hpower (by positivity)
  calc
    HaarParametrizedRepresentation.levelCoeffNorm G F s p f hf k
        ≤ ((ENNReal.ofReal A) ^ (-pR) *
            HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / pR) := hroot
    _ = C * (HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / pR) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hpR_pos.le)]
      rw [← ENNReal.rpow_mul]
      have hcancel : -pR * (1 / pR) = -1 := by
        field_simp [hpR_pos.ne']
      rw [hcancel]
      rw [ENNReal.rpow_neg_one]
      rw [← ENNReal.ofReal_inv_of_pos hA_pos]

/--
The wavelet part of the paper's `L²`-normalized Haar gauge is controlled level
by level by the parametrized gauge.
-/
theorem exists_levelHaarBlock_root_le_const_mul_levelCoeffNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ),
        (HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / p.toReal) ≤
          C * HaarParametrizedRepresentation.levelCoeffNorm G F s p f hf k := by
  classical
  rcases exists_wavelet_l2Scale_comparable_parent G F s p hp_top with
    ⟨A, B, hA_pos, hB_pos, hscale⟩
  let C : ℝ≥0∞ := ENNReal.ofReal B
  refine ⟨C, ENNReal.ofReal_ne_top, ?_⟩
  intro f hf k
  let pR := p.toReal
  have hpR_pos : 0 < pR := ennreal_toReal_pos_of_one_le_lt_top p hp_top
  have hpR_nonneg : 0 ≤ pR := hpR_pos.le
  have hpower :
      HaarRepresentation.levelHaarBlock G F s p f hf k ≤
        (ENNReal.ofReal B) ^ pR *
          HaarParametrizedRepresentation.levelCoeffPower G F s p f hf k := by
    simp only [HaarRepresentation.levelHaarBlock,
      HaarParametrizedRepresentation.levelCoeffPower]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro Q hQ
    let Qcell : GoodGridCell G :=
      { level := k
        cell := Q.1
        mem := Q.2 }
    let μQ := (G.grid.μ Q.1).toReal
    have hμQ_pos : 0 < μQ := by
      simpa [μQ, Qcell] using goodGridCell_toReal_pos (G := G) Qcell
    simp only [HaarRepresentation.cellCoeffPower,
      HaarParametrizedRepresentation.cellCoeffPower]
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro b hb
    let scaleNorm :=
      ‖((HaarParametrizedRepresentation.l2Scale G F s p
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Qcell b)) : ℝ) : ℂ)‖
    let d :=
      ‖HaarRepresentation.Coeff G F f hf
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Qcell b))‖
    have hscale_upper :
        scaleNorm ≤ B * μQ ^ (s + 1 / 2 - 1 / pR) := by
      simpa [μQ, Qcell, scaleNorm, pR] using (hscale Qcell b).2
    have hscale_lower :
        A * μQ ^ (s + 1 / 2 - 1 / pR) ≤ scaleNorm := by
      simpa [μQ, Qcell, scaleNorm, pR] using (hscale Qcell b).1
    have hscale_pos : 0 < scaleNorm := by
      exact lt_of_lt_of_le
        (mul_pos hA_pos (Real.rpow_pos_of_pos hμQ_pos _)) hscale_lower
    have hreal :
        μQ ^ (1 - s * pR - pR / 2) * d ^ pR ≤
          B ^ pR * (d / scaleNorm) ^ pR := by
      have hexp : 1 - s * pR - pR / 2 = -(s + 1 / 2 - 1 / pR) * pR := by
        field_simp [hpR_pos.ne']
        ring
      calc
        μQ ^ (1 - s * pR - pR / 2) * d ^ pR
            = μQ ^ (-(s + 1 / 2 - 1 / pR) * pR) * d ^ pR := by rw [hexp]
        _ ≤ B ^ pR * (d / scaleNorm) ^ pR :=
          real_weighted_coeff_pow_le_scale_div hB_pos hμQ_pos hscale_pos hpR_pos
            (norm_nonneg _) hscale_upper
    have hterm :
        ENNReal.ofReal (μQ ^ (1 - s * pR - pR / 2)) *
            ENNReal.ofReal (d ^ pR)
          ≤
        (ENNReal.ofReal B) ^ pR *
          ENNReal.ofReal
            (‖HaarParametrizedRepresentation.parametrizedCoeff G F s p f hf
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Qcell b))‖ ^ pR) := by
      rw [wavelet_parametrizedCoeff_norm_eq_coeff_norm_div_scale_norm]
      change ENNReal.ofReal (μQ ^ (1 - s * pR - pR / 2)) *
          ENNReal.ofReal (d ^ pR) ≤
        (ENNReal.ofReal B) ^ pR * ENNReal.ofReal ((d / scaleNorm) ^ pR)
      calc
        ENNReal.ofReal (μQ ^ (1 - s * pR - pR / 2)) *
            ENNReal.ofReal (d ^ pR)
            =
          ENNReal.ofReal (μQ ^ (1 - s * pR - pR / 2) * d ^ pR) := by
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg hμQ_pos.le _)]
        _ ≤ ENNReal.ofReal (B ^ pR * (d / scaleNorm) ^ pR) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = (ENNReal.ofReal B) ^ pR * ENNReal.ofReal ((d / scaleNorm) ^ pR) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hB_pos.le _)]
          rw [ENNReal.ofReal_rpow_of_pos hB_pos]
    simpa [HaarRepresentation.cellCoeffPower, HaarParametrizedRepresentation.cellCoeffPower,
      HaarRepresentation.indicesInCell, Qcell, μQ, d, pR, mul_assoc] using hterm
  have hroot :
      (HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / pR) ≤
        ((ENNReal.ofReal B) ^ pR *
          HaarParametrizedRepresentation.levelCoeffPower G F s p f hf k) ^ (1 / pR) := by
    exact ENNReal.rpow_le_rpow hpower (one_div_nonneg.2 hpR_pos.le)
  calc
    (HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / p.toReal)
        = (HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / pR) := by simp [pR]
    _ ≤ ((ENNReal.ofReal B) ^ pR *
          HaarParametrizedRepresentation.levelCoeffPower G F s p f hf k) ^ (1 / pR) := hroot
    _ = C * HaarParametrizedRepresentation.levelCoeffNorm G F s p f hf k := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hpR_pos.le)]
      rw [← ENNReal.rpow_mul]
      have hcancel : pR * (1 / pR) = 1 := by
        field_simp [hpR_pos.ne']
      rw [hcancel]
      simp [C, HaarParametrizedRepresentation.levelCoeffNorm, pR]

private theorem qGauge_le_const_mul
    (C : ℝ≥0∞) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (u v : ℕ → ℝ≥0∞) (huv : ∀ k, u k ≤ C * v k) :
    (if q = ∞ then
        sSup (Set.range u)
      else
        (∑' k, (u k) ^ q.toReal) ^ (1 / q.toReal))
      ≤
    C *
      (if q = ∞ then
        sSup (Set.range v)
      else
        (∑' k, (v k) ^ q.toReal) ^ (1 / q.toReal)) := by
  by_cases hq_top : q = ∞
  · simp [hq_top]
    intro k
    exact (huv k).trans (mul_le_mul_right (le_iSup v k) C)
  · have hq_lt_top : q < ∞ := lt_top_iff_ne_top.2 hq_top
    have hqR_pos : 0 < q.toReal := ennreal_toReal_pos_of_one_le_lt_top q hq_lt_top
    simp [hq_top]
    have hpow :
        (∑' k, (u k) ^ q.toReal) ≤
          C ^ q.toReal * ∑' k, (v k) ^ q.toReal := by
      calc
        (∑' k, (u k) ^ q.toReal)
            ≤ ∑' k, (C * v k) ^ q.toReal := by
              exact ENNReal.tsum_le_tsum fun k =>
                ENNReal.rpow_le_rpow (huv k) hqR_pos.le
        _ = ∑' k, C ^ q.toReal * (v k) ^ q.toReal := by
              simp [ENNReal.mul_rpow_of_nonneg _ _ hqR_pos.le]
        _ = C ^ q.toReal * ∑' k, (v k) ^ q.toReal := by
              rw [ENNReal.tsum_mul_left]
    calc
      (∑' k, (u k) ^ q.toReal) ^ q.toReal⁻¹
          ≤ (C ^ q.toReal * ∑' k, (v k) ^ q.toReal) ^ q.toReal⁻¹ := by
            exact ENNReal.rpow_le_rpow hpow (inv_nonneg.2 hqR_pos.le)
      _ = C * (∑' k, (v k) ^ q.toReal) ^ q.toReal⁻¹ := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hqR_pos.le)]
            rw [← ENNReal.rpow_mul]
            have hcancel : q.toReal * q.toReal⁻¹ = 1 := by
              field_simp [hqR_pos.ne']
            rw [hcancel]
            simp

/--
The parametrized Haar coefficient gauge is controlled by the paper's
`L²`-normalized Haar gauge.

More precisely, for fixed grid, Haar system, and Besov parameters, there is a
finite constant `C` such that every integrable `f` with finite
`haarL2RepresentationNorm` has finite `haarParametrizedNorm`, and the latter is
at most `C` times the former.
-/
theorem exists_haarParametrizedNorm_le_const_mul_haarL2RepresentationNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ),
        HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≠ ∞ →
          HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf ≠ ∞ ∧
            HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf ≤
              C * HaarRepresentation.haarL2RepresentationNorm G F s p q f hf := by
  classical
  rcases exists_fatherCoeffNorm_comparable_fatherTerm G F s p hp_top with
    ⟨Cf, Cf', hCf_fin, _hCf'_fin, hfather⟩
  rcases exists_levelCoeffNorm_le_const_mul_levelHaarBlock_root G F s p hp_top with
    ⟨Cw, hCw_fin, hlevel⟩
  let C := Cf + Cw
  refine ⟨C, ENNReal.Finiteness.add_ne_top hCf_fin hCw_fin, ?_⟩
  intro f hf hhaar_fin
  let fatherP := HaarParametrizedRepresentation.fatherCoeffNorm G F s p f hf
  let fatherH := HaarRepresentation.fatherTerm G F s p f hf
  let waveP :=
    if q = ∞ then
      sSup (Set.range fun k => HaarParametrizedRepresentation.levelCoeffNorm G F s p f hf k)
    else
      (∑' k, (HaarParametrizedRepresentation.levelCoeffNorm G F s p f hf k) ^ q.toReal) ^
        (1 / q.toReal)
  let waveH :=
    if q = ∞ then
      sSup (Set.range fun k => (HaarRepresentation.levelHaarBlock G F s p f hf k) ^
        (1 / p.toReal))
    else
      (∑' k, ((HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / p.toReal)) ^
        q.toReal) ^
        (1 / q.toReal)
  have hfather_le : fatherP ≤ Cf * fatherH := (hfather f hf).1
  have hwave_le : waveP ≤ Cw * waveH := by
    simpa [waveP, waveH, ENNReal.rpow_mul, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using
      qGauge_le_const_mul Cw q
        (fun k => HaarParametrizedRepresentation.levelCoeffNorm G F s p f hf k)
        (fun k => (HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / p.toReal))
        (hlevel f hf)
  have hmain :
      HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf ≤
        C * HaarRepresentation.haarL2RepresentationNorm G F s p q f hf := by
    calc
      HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf
          = fatherP + waveP := by simp [HaarParametrizedRepresentation.haarParametrizedNorm, fatherP, waveP]
      _ ≤ Cf * fatherH + Cw * waveH := add_le_add hfather_le hwave_le
      _ ≤ (Cf + Cw) * (fatherH + waveH) := by
        calc
          Cf * fatherH + Cw * waveH
              ≤ Cf * fatherH + Cw * waveH + (Cf * waveH + Cw * fatherH) := by
                exact le_self_add
          _ = (Cf + Cw) * (fatherH + waveH) := by
                ring_nf
      _ = C * HaarRepresentation.haarL2RepresentationNorm G F s p q f hf := by
        by_cases hq : q = ∞
        · simp [C, HaarRepresentation.haarL2RepresentationNorm, fatherH, waveH, hq]
        · simp [C, HaarRepresentation.haarL2RepresentationNorm, fatherH, waveH, hq]
          congr 3
          apply tsum_congr
          intro k
          rw [← ENNReal.rpow_mul]
          congr 1
          ring
  have hparam_fin : HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simpa [C] using ENNReal.Finiteness.add_ne_top hCf_fin hCw_fin)
      hhaar_fin) hmain
  exact ⟨hparam_fin, hmain⟩

/--
The paper's `L²`-normalized Haar gauge is controlled by the parametrized Haar
coefficient gauge.

This is the reverse comparison to
`exists_haarParametrizedNorm_le_const_mul_haarL2RepresentationNorm`: for fixed
grid, Haar system, and Besov parameters, there is a finite constant `C` such
that every integrable `f` with finite parametrized Haar norm has finite
`haarL2RepresentationNorm`, and the latter is at most `C` times the former.
-/
theorem exists_haarL2RepresentationNorm_le_const_mul_haarParametrizedNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ),
        HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf ≠ ∞ →
          HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≠ ∞ ∧
            HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≤
              C * HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf := by
  rcases exists_fatherCoeffNorm_comparable_fatherTerm G F s p hp_top with
    ⟨_Cf, Cf', _hCf_fin, hCf'_fin, hfather⟩
  rcases exists_levelHaarBlock_root_le_const_mul_levelCoeffNorm G F s p hp_top with
    ⟨Cw, hCw_fin, hlevel⟩
  let C := Cf' + Cw
  refine ⟨C, by simpa [C] using ENNReal.Finiteness.add_ne_top hCf'_fin hCw_fin, ?_⟩
  intro f hf hparam_fin
  let fatherH := HaarRepresentation.fatherTerm G F s p f hf
  let fatherP := HaarParametrizedRepresentation.fatherCoeffNorm G F s p f hf
  let waveH :=
    if q = ∞ then
      sSup (Set.range fun k => (HaarRepresentation.levelHaarBlock G F s p f hf k) ^
        (1 / p.toReal))
    else
      (∑' k, ((HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / p.toReal)) ^
        q.toReal) ^
        (1 / q.toReal)
  let waveP :=
    if q = ∞ then
      sSup (Set.range (HaarParametrizedRepresentation.levelCoeffNorm G F s p f hf))
    else
      (∑' k, (HaarParametrizedRepresentation.levelCoeffNorm G F s p f hf k) ^ q.toReal) ^
        (1 / q.toReal)
  have hfather_le : fatherH ≤ Cf' * fatherP := (hfather f hf).2
  have hwave_le : waveH ≤ Cw * waveP := by
    simpa [waveH, waveP, ENNReal.rpow_mul, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using
      qGauge_le_const_mul Cw q
        (fun k => (HaarRepresentation.levelHaarBlock G F s p f hf k) ^ (1 / p.toReal))
        (fun k => HaarParametrizedRepresentation.levelCoeffNorm G F s p f hf k)
        (hlevel f hf)
  have hmain :
      HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≤
        C * HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf := by
    calc
      HaarRepresentation.haarL2RepresentationNorm G F s p q f hf
          = fatherH + waveH := by
            by_cases hq : q = ∞
            · simp [HaarRepresentation.haarL2RepresentationNorm, fatherH, waveH, hq]
            · simp [HaarRepresentation.haarL2RepresentationNorm, fatherH, waveH, hq]
              congr 3
              funext k
              rw [← ENNReal.rpow_mul]
              congr 1
              ring
      _ ≤ Cf' * fatherP + Cw * waveP := add_le_add hfather_le hwave_le
      _ ≤ (Cf' + Cw) * (fatherP + waveP) := by
        calc
          Cf' * fatherP + Cw * waveP
              ≤ Cf' * fatherP + Cw * waveP + (Cf' * waveP + Cw * fatherP) := by
                exact le_self_add
          _ = (Cf' + Cw) * (fatherP + waveP) := by
                ring_nf
      _ = C * HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf := by
        simp [C, HaarParametrizedRepresentation.haarParametrizedNorm, fatherP, waveP]
  have hhaar_fin : HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top
        (by simpa [C] using ENNReal.Finiteness.add_ne_top hCf'_fin hCw_fin)
        hparam_fin)
      hmain
  exact ⟨hhaar_fin, hmain⟩

/--
The two Haar coefficient gauges are equivalent up to finite constants.

This packages the two one-sided comparisons into a single statement.  The
constant `C₁` controls the parametrized gauge by the paper's `L²`-normalized
gauge, while `C₂` controls the paper's gauge by the parametrized one.
-/
theorem exists_haarRepresentationNorms_equivalent
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞) [Fact (1 ≤ q)] :
    ∃ C₁ C₂ : ℝ≥0∞, C₁ ≠ ∞ ∧ C₂ ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ),
        (HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≠ ∞ →
          HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf ≠ ∞ ∧
            HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf ≤
              C₁ * HaarRepresentation.haarL2RepresentationNorm G F s p q f hf) ∧
        (HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf ≠ ∞ →
          HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≠ ∞ ∧
            HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≤
              C₂ * HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf) := by
  rcases exists_haarParametrizedNorm_le_const_mul_haarL2RepresentationNorm
    G F s p q hp_top with ⟨C₁, hC₁_fin, hC₁⟩
  rcases exists_haarL2RepresentationNorm_le_const_mul_haarParametrizedNorm
    G F s p q hp_top with ⟨C₂, hC₂_fin, hC₂⟩
  exact ⟨C₁, C₂, hC₁_fin, hC₂_fin, fun f hf => ⟨hC₁ f hf, hC₂ f hf⟩⟩

/--
The paper's `L²`-normalized Haar gauge is finite exactly when the
parametrized Haar gauge is finite.
-/
theorem haarL2RepresentationNorm_finite_iff_haarParametrizedNorm_finite
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞) [Fact (1 ≤ q)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≠ ∞ ↔
      HaarParametrizedRepresentation.haarParametrizedNorm G F s p q f hf ≠ ∞ := by
  rcases exists_haarRepresentationNorms_equivalent G F s p q hp_top with
    ⟨C₁, C₂, hC₁_fin, hC₂_fin, hcomp⟩
  exact ⟨fun h => (hcomp f hf).1 h |>.1, fun h => (hcomp f hf).2 h |>.1⟩

end

end GoodGridSpace
