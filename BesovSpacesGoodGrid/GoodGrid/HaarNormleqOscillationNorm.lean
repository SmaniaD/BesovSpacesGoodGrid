import BesovSpacesGoodGrid.GoodGrid.HaarRepresentationNorm
import BesovSpacesGoodGrid.GoodGrid.MeanOscillationNorm
import BesovSpacesGoodGrid.GoodGrid.standardRepresentation
import BesovSpacesGoodGrid.GoodGrid.standardNormleqHaarRepresenstionNorm
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Haar norm is controlled by the mean-oscillation norm

This file records the comparison in the direction
`N_haar(f) ≤ C N_osc(f)`.  The proof is organized in the same way as the
manuscript: first the father coefficient is controlled by the global `L^p`
term, then every Haar block over a grid level is controlled by the
corresponding oscillation block, and finally the `q`-summation is just an
abstract bookkeeping step.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace HaarRepresentation

private theorem univ_measure_toReal_pos
    (G : GoodGridSpace (α := α)) :
    0 < (G.grid.μ Set.univ).toReal := by
  have hμ_pos : 0 < G.grid.μ Set.univ :=
    G.grid.positive_measure 0 Set.univ (by simp [G.grid.grid.first_partition_eq_univ])
  have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ := by
    letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ Set.univ
  exact ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top

private theorem univ_measure_ne_top
    (G : GoodGridSpace (α := α)) :
    G.grid.μ Set.univ ≠ ∞ := by
  letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  exact MeasureTheory.measure_ne_top G.grid.μ Set.univ

private theorem ofReal_univ_measure_toReal_rpow
    (G : GoodGridSpace (α := α)) (a : ℝ) :
    ENNReal.ofReal ((G.grid.μ Set.univ).toReal ^ a) =
      (G.grid.μ Set.univ) ^ a := by
  have hμ_pos := univ_measure_toReal_pos G
  rw [← ENNReal.ofReal_rpow_of_pos hμ_pos]
  rw [ENNReal.ofReal_toReal (univ_measure_ne_top G)]

private theorem ofReal_cell_measure_toReal_rpow
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) (a : ℝ) :
    ENNReal.ofReal ((G.grid.μ Q.cell).toReal ^ a) =
      (G.grid.μ Q.cell) ^ a := by
  have hμ_pos : 0 < (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  rw [← ENNReal.ofReal_rpow_of_pos hμ_pos]
  rw [ENNReal.ofReal_toReal (GoodGridCell.measure_ne_top Q)]

private theorem l2NormalizationFactor_alpha
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G)) :
    l2NormalizationFactor G F .alpha =
      Real.sqrt (G.grid.μ Set.univ).toReal := by
  let μI := (G.grid.μ Set.univ).toReal
  have hμI_pos : 0 < μI := univ_measure_toReal_pos G
  calc
    l2NormalizationFactor G F .alpha
        = (Real.sqrt (1 / μI))⁻¹ := by
          simp [l2NormalizationFactor, μI]
    _ = Real.sqrt μI := by
          have hsqrt_inv : Real.sqrt (1 / μI) = (Real.sqrt μI)⁻¹ := by
            rw [show 1 / μI = μI⁻¹ by ring, Real.sqrt_inv μI]
          rw [hsqrt_inv, inv_inv]

private theorem l2normalizedHaar_alpha_norm_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (x : α) :
    ‖L2normalizedHaar G F .alpha x‖ =
      (G.grid.μ Set.univ).toReal ^ (-(1 : ℝ) / 2) := by
  let μI := (G.grid.μ Set.univ).toReal
  have hμI_pos : 0 < μI := univ_measure_toReal_pos G
  have hnorm :
      ‖L2normalizedHaar G F .alpha x‖ =
        Real.sqrt μI * (1 / μI) := by
    rw [L2normalizedHaar, l2NormalizationFactor_alpha G F]
    simp [UnbalancedHaarWavelet.FullHaarSystem.function, F.alphaFunction_def,
      UnbalancedHaarWavelet.normalizedAlphaFunction, μI, Real.sqrt_nonneg]
  calc
    ‖L2normalizedHaar G F .alpha x‖
        = Real.sqrt μI * (1 / μI) := hnorm
    _ = μI ^ (-(1 : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow]
          rw [show 1 / μI = μI⁻¹ by ring]
          rw [show μI⁻¹ = μI ^ (-(1 : ℝ)) by
            have h := Real.rpow_neg hμI_pos.le (1 : ℝ)
            rw [Real.rpow_one] at h
            exact h.symm]
          rw [← Real.rpow_add hμI_pos]
          ring_nf

private theorem l2normalizedHaar_alpha_enorm_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (x : α) :
    ‖L2normalizedHaar G F .alpha x‖ₑ =
      (G.grid.μ Set.univ) ^ (-(1 : ℝ) / 2) := by
  rw [← ofReal_norm_eq_enorm, l2normalizedHaar_alpha_norm_eq G F x]
  exact ofReal_univ_measure_toReal_rpow G (-(1 : ℝ) / 2)

private theorem l2normalizedHaar_wavelet_norm_le_c₂_mul_parent_rpow
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    (x : α) :
    ‖L2normalizedHaar G F (.wavelet (indexOfCellBranch G F Q b)) x‖ ≤
      StandardAtomicRepresentation.c₂ G *
        (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) := by
  classical
  let A := UnbalancedHaarWavelet.branchSupport b.1.1
  let B := UnbalancedHaarWavelet.branchSupport b.1.2
  have hdisj : Disjoint A B := by
    simpa [A, B] using
      F.toHaarSystem.branchSupport_components_disjoint (GridOf G) b
  by_cases hxA : x ∈ A
  · have hxB : x ∉ B := fun hxB => (Set.disjoint_left.1 hdisj) hxA hxB
    have hvalue :
        L2normalizedHaar G F (.wavelet (indexOfCellBranch G F Q b)) x =
          (((l2NormalizationFactor G F (.wavelet (indexOfCellBranch G F Q b)) : ℝ) : ℂ) *
            ((1 / (G.grid.μ A).toReal : ℝ) : ℂ)) := by
      simp [L2normalizedHaar, indexOfCellBranch,
        UnbalancedHaarWavelet.FullHaarSystem.function,
        UnbalancedHaarWavelet.HaarSystem.wavelet,
        F.toHaarSystem.haarWavelets_def, UnbalancedHaarWavelet.haarWavelet,
        A, B, hxA, hxB]
    rw [hvalue]
    exact StandardAtomicRepresentation.l2NormalizationFactor_mul_inv_measure_le_c₂_mul_parent_rpow
      G F Q b A (by
        simpa [A] using StandardAtomicRepresentation.branchSupport_toReal_lower_left G F Q b)
  · by_cases hxB : x ∈ B
    · have hvalue :
          L2normalizedHaar G F (.wavelet (indexOfCellBranch G F Q b)) x =
            -(((l2NormalizationFactor G F (.wavelet (indexOfCellBranch G F Q b)) : ℝ) : ℂ) *
              ((1 / (G.grid.μ B).toReal : ℝ) : ℂ)) := by
        simp [L2normalizedHaar, indexOfCellBranch,
          UnbalancedHaarWavelet.FullHaarSystem.function,
          UnbalancedHaarWavelet.HaarSystem.wavelet,
          F.toHaarSystem.haarWavelets_def, UnbalancedHaarWavelet.haarWavelet,
          A, B, hxA, hxB]
      rw [hvalue, norm_neg]
      exact StandardAtomicRepresentation.l2NormalizationFactor_mul_inv_measure_le_c₂_mul_parent_rpow
        G F Q b B (by
          simpa [B] using StandardAtomicRepresentation.branchSupport_toReal_lower_right G F Q b)
    · have hvalue :
          L2normalizedHaar G F (.wavelet (indexOfCellBranch G F Q b)) x = 0 := by
        simp [L2normalizedHaar, indexOfCellBranch,
          UnbalancedHaarWavelet.FullHaarSystem.function,
          UnbalancedHaarWavelet.HaarSystem.wavelet,
          F.toHaarSystem.haarWavelets_def, UnbalancedHaarWavelet.haarWavelet,
          A, B, hxA, hxB]
      rw [hvalue, norm_zero]
      exact mul_nonneg (StandardAtomicRepresentation.c₂_pos G).le
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)

private theorem l2normalizedHaar_wavelet_enorm_le_c₂_mul_parent_rpow
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    (x : α) :
    ‖L2normalizedHaar G F (.wavelet (indexOfCellBranch G F Q b)) x‖ₑ ≤
      ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
        (G.grid.μ Q.cell) ^ (-(1 : ℝ) / 2) := by
  rw [← ofReal_norm_eq_enorm]
  have hreal :=
    l2normalizedHaar_wavelet_norm_le_c₂_mul_parent_rpow G F Q b x
  calc
    ENNReal.ofReal ‖L2normalizedHaar G F (.wavelet (indexOfCellBranch G F Q b)) x‖
        ≤ ENNReal.ofReal
            (StandardAtomicRepresentation.c₂ G *
              (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2)) :=
          ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
          (G.grid.μ Q.cell) ^ (-(1 : ℝ) / 2) := by
          rw [ENNReal.ofReal_mul (StandardAtomicRepresentation.c₂_pos G).le]
          rw [ofReal_cell_measure_toReal_rpow G Q (-(1 : ℝ) / 2)]

private theorem l2normalizedHaar_wavelet_eq_zero_of_not_mem_parent
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    {x : α} (hx : x ∉ Q.cell) :
    L2normalizedHaar G F (.wavelet (indexOfCellBranch G F Q b)) x = 0 := by
  classical
  let A := UnbalancedHaarWavelet.branchSupport b.1.1
  let B := UnbalancedHaarWavelet.branchSupport b.1.2
  have hsupport_subset :
      A ∪ B ⊆ Q.cell := by
    have hbranch :
        UnbalancedHaarWavelet.haarBranchSupport b.1 ⊆ Q.cell :=
      F.toHaarSystem.haarBranchSupport_subset_cell (GridOf G) b
    simpa [A, B, UnbalancedHaarWavelet.haarBranchSupport_eq_union_branchSupport] using
      hbranch
  have hxA : x ∉ A := fun hxA => hx (hsupport_subset (Or.inl hxA))
  have hxB : x ∉ B := fun hxB => hx (hsupport_subset (Or.inr hxB))
  simp [L2normalizedHaar, indexOfCellBranch,
    UnbalancedHaarWavelet.FullHaarSystem.function,
    UnbalancedHaarWavelet.HaarSystem.wavelet,
    F.toHaarSystem.haarWavelets_def, UnbalancedHaarWavelet.haarWavelet,
    A, B, hxA, hxB]

private theorem integral_l2normalizedHaar_wavelet_eq_zero
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    ∫ x, L2normalizedHaar G F (.wavelet (indexOfCellBranch G F Q b)) x ∂G.grid.μ = 0 := by
  let i := indexOfCellBranch G F Q b
  let n : ℂ := ((l2NormalizationFactor G F (.wavelet i) : ℝ) : ℂ)
  have hreal :
      ∫ x, UnbalancedHaarWavelet.HaarSystem.wavelet (GridOf G) F.toHaarSystem i x
          ∂G.grid.μ = 0 :=
    UnbalancedHaarWavelet.HaarSystem.integral_wavelet_eq_zero (GridOf G) F.toHaarSystem i
  have hcomplex :
      ∫ x, ((UnbalancedHaarWavelet.HaarSystem.wavelet (GridOf G) F.toHaarSystem i x : ℝ) : ℂ)
          ∂G.grid.μ = 0 := by
    rw [integral_complex_ofReal, hreal]
    norm_num
  calc
    ∫ x, L2normalizedHaar G F (.wavelet i) x ∂G.grid.μ
        = ∫ x,
            n *
              ((UnbalancedHaarWavelet.HaarSystem.wavelet (GridOf G) F.toHaarSystem i x : ℝ) :
                ℂ) ∂G.grid.μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp [L2normalizedHaar, n, i,
              UnbalancedHaarWavelet.FullHaarSystem.function]
    _ = n *
          ∫ x, ((UnbalancedHaarWavelet.HaarSystem.wavelet (GridOf G) F.toHaarSystem i x : ℝ) :
            ℂ) ∂G.grid.μ := by
          rw [MeasureTheory.integral_const_mul]
    _ = 0 := by
          rw [hcomplex, mul_zero]

private theorem coeff_wavelet_sub_const_eq_coeff
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (c : ℂ)
    (hfsub : Integrable (fun x => f x - c) G.grid.μ)
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    Coeff G F (fun x => f x - c) hfsub (.wavelet (indexOfCellBranch G F Q b)) =
      Coeff G F f hf (.wavelet (indexOfCellBranch G F Q b)) := by
  classical
  let φ : α → ℂ := L2normalizedHaar G F (.wavelet (indexOfCellBranch G F Q b))
  have hphi_top : MemLp φ ∞ G.grid.μ := by
    simpa [φ] using
      (l2normalizedHaar_memLp G F ∞ (.wavelet (indexOfCellBranch G F Q b)))
  have hfφ_int : Integrable (fun x => f x * φ x) G.grid.μ := by
    have h := hf.mul_of_top_right hphi_top
    simpa [Pi.mul_apply, mul_comm, φ] using h
  have hcφ_int : Integrable (fun x => c * φ x) G.grid.μ := by
    letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
    have hphi_one : MemLp φ 1 G.grid.μ := by
      simpa [φ] using
        (l2normalizedHaar_memLp G F 1 (.wavelet (indexOfCellBranch G F Q b)))
    have hphi_int : Integrable φ G.grid.μ :=
      hphi_one.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    exact hphi_int.const_mul c
  have hzero :
      ∫ x, c * φ x ∂G.grid.μ = 0 := by
    calc
      ∫ x, c * φ x ∂G.grid.μ
          = c * ∫ x, φ x ∂G.grid.μ := by rw [MeasureTheory.integral_const_mul]
      _ = 0 := by
          rw [integral_l2normalizedHaar_wavelet_eq_zero G F Q b]
          simp
  calc
    Coeff G F (fun x => f x - c)
        hfsub
        (.wavelet (indexOfCellBranch G F Q b))
        = ∫ x, (f x * φ x - c * φ x) ∂G.grid.μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp [φ]
            ring
    _ = ∫ x, f x * φ x ∂G.grid.μ - ∫ x, c * φ x ∂G.grid.μ := by
          rw [MeasureTheory.integral_sub hfφ_int hcφ_int]
    _ = Coeff G F f hf (.wavelet (indexOfCellBranch G F Q b)) := by
          rw [hzero, sub_zero]
          rfl

private theorem coeff_wavelet_enorm_le_c₂_mul_cell_rpow_mul_eLpNorm_sub_const
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (hfLp : MemLp f p G.grid.μ) (c : ℂ)
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    ENNReal.ofReal ‖Coeff G F f hf (.wavelet (indexOfCellBranch G F Q b))‖ ≤
      ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
        (G.grid.μ Q.cell) ^ (1 / 2 - 1 / p.toReal) *
          MeasureTheory.eLpNorm (fun x => f x - c) p (G.grid.μ.restrict Q.cell) := by
  classical
  let μQ : ℝ≥0∞ := G.grid.μ Q.cell
  let φ : α → ℂ := L2normalizedHaar G F (.wavelet (indexOfCellBranch G F Q b))
  let g : α → ℂ := fun x => f x - c
  have hpR_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp_top.ne
  have hμQ_ne_zero : μQ ≠ 0 := by
    dsimp [μQ]
    exact ne_of_gt (GoodGridCell.measure_pos Q)
  have hμQ_ne_top : μQ ≠ ∞ := by
    dsimp [μQ]
    exact GoodGridCell.measure_ne_top Q
  have hK_ne_top :
      ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
          μQ ^ (-(1 : ℝ) / 2) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero hμQ_ne_zero hμQ_ne_top)
  have hQmeas : MeasurableSet Q.cell :=
    G.grid.grid.measurable Q.level Q.cell Q.mem
  have hfsub : Integrable g G.grid.μ := by
    letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact hf.sub (integrable_const c)
  have hcoeff_eq :
      Coeff G F f hf (.wavelet (indexOfCellBranch G F Q b)) =
        Coeff G F g hfsub (.wavelet (indexOfCellBranch G F Q b)) := by
    exact (coeff_wavelet_sub_const_eq_coeff G F f hf c hfsub Q b).symm
  have hsupport_indicator :
      (fun x => ‖g x * φ x‖ₑ) =
        fun x => Q.cell.indicator (fun y => ‖g y * φ y‖ₑ) x := by
    funext x
    by_cases hx : x ∈ Q.cell
    · simp [Set.indicator, hx]
    · have hφ_zero :
          φ x = 0 := by
        simpa [φ] using l2normalizedHaar_wavelet_eq_zero_of_not_mem_parent G F Q b hx
      simp [Set.indicator, hx, hφ_zero]
  have hgLp_restrict :
      MemLp g p (G.grid.μ.restrict Q.cell) := by
    letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
    letI : IsFiniteMeasure (G.grid.μ.restrict Q.cell) := by infer_instance
    exact (hfLp.mono_measure Measure.restrict_le_self).sub (memLp_const c)
  calc
    ENNReal.ofReal ‖Coeff G F f hf (.wavelet (indexOfCellBranch G F Q b))‖
        = ‖Coeff G F g hfsub (.wavelet (indexOfCellBranch G F Q b))‖ₑ := by
          rw [hcoeff_eq, ofReal_norm_eq_enorm]
    _ ≤ ∫⁻ x, ‖g x * φ x‖ₑ ∂G.grid.μ := by
          simpa [Coeff, g, φ] using
            (MeasureTheory.enorm_integral_le_lintegral_enorm
              (fun x => g x * φ x)
              (μ := G.grid.μ))
    _ = ∫⁻ x in Q.cell, ‖g x * φ x‖ₑ ∂G.grid.μ := by
          rw [← MeasureTheory.lintegral_indicator hQmeas]
          rw [← hsupport_indicator]
    _ ≤ ∫⁻ x in Q.cell,
          ‖g x‖ₑ *
            (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
              μQ ^ (-(1 : ℝ) / 2)) ∂G.grid.μ := by
          refine MeasureTheory.setLIntegral_mono' hQmeas ?_
          intro x hx
          rw [enorm_mul]
          exact mul_le_mul_left'
            (by
              simpa [μQ, φ] using
                l2normalizedHaar_wavelet_enorm_le_c₂_mul_parent_rpow G F Q b x)
            ‖g x‖ₑ
    _ = (∫⁻ x in Q.cell, ‖g x‖ₑ ∂G.grid.μ) *
          (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
            μQ ^ (-(1 : ℝ) / 2)) := by
          exact MeasureTheory.lintegral_mul_const'
            (μ := G.grid.μ.restrict Q.cell)
            (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
              μQ ^ (-(1 : ℝ) / 2))
            (fun x => ‖g x‖ₑ) hK_ne_top
    _ = MeasureTheory.eLpNorm g 1 (G.grid.μ.restrict Q.cell) *
          (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
            μQ ^ (-(1 : ℝ) / 2)) := by
          rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
    _ ≤ (MeasureTheory.eLpNorm g p (G.grid.μ.restrict Q.cell) *
          μQ ^ (1 - 1 / p.toReal)) *
          (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
            μQ ^ (-(1 : ℝ) / 2)) := by
          have hLp1 :
              MeasureTheory.eLpNorm g 1 (G.grid.μ.restrict Q.cell) ≤
                MeasureTheory.eLpNorm g p (G.grid.μ.restrict Q.cell) *
                  μQ ^ (1 - 1 / p.toReal) := by
            simpa [μQ, Measure.restrict_apply_univ] using
              (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
                (μ := G.grid.μ.restrict Q.cell)
                (p := (1 : ℝ≥0∞)) (q := p)
                (by simpa using (Fact.out : (1 : ℝ≥0∞) ≤ p))
                hgLp_restrict.1)
          exact mul_le_mul_right' hLp1
            (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
              μQ ^ (-(1 : ℝ) / 2))
    _ = ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
          μQ ^ (1 / 2 - 1 / p.toReal) *
            MeasureTheory.eLpNorm g p (G.grid.μ.restrict Q.cell) := by
          calc
            (MeasureTheory.eLpNorm g p (G.grid.μ.restrict Q.cell) *
                μQ ^ (1 - 1 / p.toReal)) *
                (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
                  μQ ^ (-(1 : ℝ) / 2))
                = ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
                    (μQ ^ (1 - 1 / p.toReal) * μQ ^ (-(1 : ℝ) / 2)) *
                      MeasureTheory.eLpNorm g p (G.grid.μ.restrict Q.cell) := by
                    ac_rfl
            _ = ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
                  μQ ^ (1 / 2 - 1 / p.toReal) *
                    MeasureTheory.eLpNorm g p (G.grid.μ.restrict Q.cell) := by
                    rw [← ENNReal.rpow_add (1 - 1 / p.toReal) (-(1 : ℝ) / 2)
                      hμQ_ne_zero hμQ_ne_top]
                    ring_nf

private theorem one_le_branchCells_card
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    1 ≤ (StandardAtomicRepresentation.branchCells (G := G) (F := F) (Q := Q) b).card := by
  classical
  let T := F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem
  rcases (T.NonemptyPairs b.1 b.2).1 with ⟨P, hP⟩
  have hP_union :
      P ∈ StandardAtomicRepresentation.branchCells (G := G) (F := F) (Q := Q) b := by
    simp [StandardAtomicRepresentation.branchCells, hP]
  exact Finset.card_pos.2 ⟨P, hP_union⟩

private theorem cellCoeffPower_le_const_mul_cellOscillationPower_of_const
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    {M : ℕ}
    (hM :
      ∀ Q : GoodGridCell G,
        (∑ b ∈ indicesInCell G F Q,
          (StandardAtomicRepresentation.branchCells (G := G) (F := F) (Q := Q) b).card) ≤ M)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (hfLp : MemLp f p G.grid.μ)
    (Q : GoodGridCell G) (c : ℂ) :
    cellCoeffPower G F p f hf Q ≤
      (M : ℝ≥0∞) *
        (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal *
          ((G.grid.μ Q.cell) ^ (p.toReal / 2 - 1) *
            MeasureTheory.eLpNorm (fun x => f x - c) p
              (G.grid.μ.restrict Q.cell) ^ p.toReal)) := by
  classical
  let μQ : ℝ≥0∞ := G.grid.μ Q.cell
  let K : ℝ≥0∞ :=
    ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) *
      μQ ^ (1 / 2 - 1 / p.toReal)
  let E : ℝ≥0∞ :=
    MeasureTheory.eLpNorm (fun x => f x - c) p (G.grid.μ.restrict Q.cell)
  have hpR_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp_top.ne
  have hpR_nonneg : 0 ≤ p.toReal := hpR_pos.le
  have hμQ_ne_zero : μQ ≠ 0 := by
    dsimp [μQ]
    exact ne_of_gt (GoodGridCell.measure_pos Q)
  have hμQ_ne_top : μQ ≠ ∞ := by
    dsimp [μQ]
    exact GoodGridCell.measure_ne_top Q
  have hterm :
      ∀ b ∈ indicesInCell G F Q,
        ENNReal.ofReal (‖Coeff G F f hf (.wavelet (indexOfCellBranch G F Q b))‖ ^ p.toReal)
          ≤
        ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal *
          (μQ ^ (p.toReal / 2 - 1) * E ^ p.toReal) := by
    intro b hb
    have hcoeff :
        ENNReal.ofReal ‖Coeff G F f hf (.wavelet (indexOfCellBranch G F Q b))‖ ≤
          K * E := by
      simpa [K, E, μQ, mul_assoc] using
        coeff_wavelet_enorm_le_c₂_mul_cell_rpow_mul_eLpNorm_sub_const
          G F p hp_top f hf hfLp c Q b
    calc
      ENNReal.ofReal (‖Coeff G F f hf (.wavelet (indexOfCellBranch G F Q b))‖ ^ p.toReal)
          = (ENNReal.ofReal ‖Coeff G F f hf (.wavelet (indexOfCellBranch G F Q b))‖) ^
              p.toReal := by
            rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpR_nonneg]
      _ ≤ (K * E) ^ p.toReal := ENNReal.rpow_le_rpow hcoeff hpR_nonneg
      _ =
          ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal *
            (μQ ^ (p.toReal / 2 - 1) * E ^ p.toReal) := by
            dsimp [K]
            rw [mul_assoc]
            rw [ENNReal.mul_rpow_of_nonneg _ _ hpR_nonneg]
            rw [ENNReal.mul_rpow_of_nonneg _ _ hpR_nonneg]
            rw [← ENNReal.rpow_mul]
            have hexp :
                (1 / 2 - 1 / p.toReal) * p.toReal = p.toReal / 2 - 1 := by
              field_simp [hpR_pos.ne']
            rw [hexp]
  calc
    cellCoeffPower G F p f hf Q
        ≤ ∑ b ∈ indicesInCell G F Q,
            ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal *
              (μQ ^ (p.toReal / 2 - 1) * E ^ p.toReal) := by
          simp only [cellCoeffPower]
          exact Finset.sum_le_sum hterm
    _ =
        ((indicesInCell G F Q).card : ℝ≥0∞) *
          (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal *
            (μQ ^ (p.toReal / 2 - 1) * E ^ p.toReal)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤
        (∑ b ∈ indicesInCell G F Q,
          ((StandardAtomicRepresentation.branchCells (G := G) (F := F) (Q := Q) b).card :
            ℝ≥0∞)) *
          (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal *
            (μQ ^ (p.toReal / 2 - 1) * E ^ p.toReal)) := by
          refine mul_le_mul_right' ?_ _
          calc
            ((indicesInCell G F Q).card : ℝ≥0∞)
                = ∑ b ∈ indicesInCell G F Q, (1 : ℝ≥0∞) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
                  simp
            _ ≤ ∑ b ∈ indicesInCell G F Q,
                  ((StandardAtomicRepresentation.branchCells (G := G) (F := F) (Q := Q) b).card :
                    ℝ≥0∞) := by
                  exact Finset.sum_le_sum fun b hb => by
                    exact_mod_cast one_le_branchCells_card G F Q b
    _ ≤
        (M : ℝ≥0∞) *
          (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal *
            (μQ ^ (p.toReal / 2 - 1) * E ^ p.toReal)) := by
          exact mul_le_mul_right' (by exact_mod_cast hM Q) _

private theorem ennreal_toReal_pos_of_one_le_lt_top (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp_top : p < ∞) :
    0 < p.toReal := by
  exact ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp_top.ne

private theorem iInf_rpow_of_pos {ι : Type*} [Nonempty ι]
    (u : ι → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    (⨅ i, u i) ^ r = ⨅ i, (u i) ^ r := by
  apply le_antisymm
  · exact le_iInf fun i =>
      ENNReal.monotone_rpow_of_nonneg hr.le (iInf_le u i)
  · rw [← ENNReal.rpow_le_rpow_iff (one_div_pos.2 hr)]
    rw [show 1 / r = r⁻¹ by ring, ENNReal.rpow_rpow_inv hr.ne']
    refine le_iInf (f := u) fun i => ?_
    exact (ENNReal.rpow_inv_le_iff (x := ⨅ i, (u i) ^ r) (y := u i) hr).2
      (iInf_le (fun i => (u i) ^ r) i)

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
If the father term and each level root satisfy the expected pointwise
estimates, then the whole Haar gauge is bounded by the mean-oscillation gauge.

This lemma contains only the `q = ∞` / `q < ∞` bookkeeping.  The analytic
content is isolated in the hypotheses: the father estimate is the manuscript's
`|d_I| ≤ ‖f‖_p μ(I)^{1/2-1/p}`, while the level estimate is the oscillation
bound obtained from zero mean and Hölder on each parent cell.
-/
theorem haarL2RepresentationNorm_le_of_level_bounds
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (C0 Cpos : ℝ≥0∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    fatherTerm G F s p f hf ≤
        C0 * ((G.grid.μ Set.univ) ^ (-s) * MeasureTheory.eLpNorm f p G.grid.μ) →
    (∀ k,
      (levelHaarBlock G F s p f hf k) ^ (1 / p.toReal) ≤
        Cpos * (MeanOscillation.levelOscillationBlock G s p f k) ^ (1 / p.toReal)) →
      haarL2RepresentationNorm G F s p q f hf ≤
        (C0 + Cpos) * MeanOscillation.meanOscillationNorm G s p q f := by
  classical
  intro hfather hlevels
  let lpTerm : ℝ≥0∞ :=
    (G.grid.μ Set.univ) ^ (-s) * MeasureTheory.eLpNorm f p G.grid.μ
  let haarWave : ℝ≥0∞ :=
    if q = ∞ then
      sSup (Set.range fun k => (levelHaarBlock G F s p f hf k) ^ (1 / p.toReal))
    else
      (∑' k, ((levelHaarBlock G F s p f hf k) ^ (1 / p.toReal)) ^ q.toReal) ^
        (1 / q.toReal)
  let oscWave : ℝ≥0∞ :=
    if q = ∞ then
      sSup (Set.range fun k => (MeanOscillation.levelOscillationBlock G s p f k) ^
        (1 / p.toReal))
    else
      (∑' k, ((MeanOscillation.levelOscillationBlock G s p f k) ^
        (1 / p.toReal)) ^ q.toReal) ^ (1 / q.toReal)
  have hpR_pos : 0 < p.toReal := ennreal_toReal_pos_of_one_le_lt_top p hp_top
  have hpInv_nonneg : 0 ≤ 1 / p.toReal := one_div_nonneg.2 hpR_pos.le
  have hhaar_wave_def :
      (if q = ∞ then
          sSup (Set.range fun k => (levelHaarBlock G F s p f hf k) ^ (1 / p.toReal))
        else
          (∑' k, (levelHaarBlock G F s p f hf k) ^ (q.toReal / p.toReal)) ^
            (1 / q.toReal)) = haarWave := by
    by_cases hq : q = ∞
    · simp [haarWave, hq]
    · simp [haarWave, hq]
      congr 2
      ext k
      rw [← ENNReal.rpow_mul]
      congr 1
      field_simp [hpR_pos.ne']
  have hosc_wave_def :
      MeanOscillation.oscillationSeminorm G s p q f = oscWave := by
    by_cases hq : q = ∞
    · simp [MeanOscillation.oscillationSeminorm, oscWave, hq]
    · simp [MeanOscillation.oscillationSeminorm, oscWave, hq]
      congr 2
      ext k
      rw [← ENNReal.rpow_mul]
      congr 1
      field_simp [hpR_pos.ne']
  have hwave_le : haarWave ≤ Cpos * oscWave := by
    simpa [haarWave, oscWave] using
      qGauge_le_const_mul Cpos q
        (fun k => (levelHaarBlock G F s p f hf k) ^ (1 / p.toReal))
        (fun k => (MeanOscillation.levelOscillationBlock G s p f k) ^ (1 / p.toReal))
        hlevels
  have hnorm_le :
      haarL2RepresentationNorm G F s p q f hf ≤ fatherTerm G F s p f hf + haarWave := by
    rw [haarL2RepresentationNorm]
    rw [hhaar_wave_def]
  calc
    haarL2RepresentationNorm G F s p q f hf
        ≤ fatherTerm G F s p f hf + haarWave := hnorm_le
    _ ≤ C0 * lpTerm + Cpos * oscWave := add_le_add hfather hwave_le
    _ ≤ (C0 + Cpos) * (lpTerm + oscWave) := by
          calc
            C0 * lpTerm + Cpos * oscWave
                ≤ C0 * lpTerm + Cpos * oscWave + (C0 * oscWave + Cpos * lpTerm) := by
                  exact le_self_add
            _ = (C0 + Cpos) * (lpTerm + oscWave) := by
                  ring_nf
    _ = (C0 + Cpos) * MeanOscillation.meanOscillationNorm G s p q f := by
          simp [MeanOscillation.meanOscillationNorm, lpTerm, hosc_wave_def]

/--
Father coefficient estimate used in the comparison with oscillation.

Mathematically this is the step
`|d_I| ≤ ∫_I |f| |φ_I| ≤ ‖f‖_p μ(I)^{1/2-1/p}`, after multiplying by the
father weight in `N_haar`.
-/
theorem exists_fatherTerm_le_const_mul_meanOscillationLpTerm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞) :
    ∃ C0 : ℝ≥0∞, C0 ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ), MemLp f p G.grid.μ →
        fatherTerm G F s p f hf ≤
          C0 * ((G.grid.μ Set.univ) ^ (-s) * MeasureTheory.eLpNorm f p G.grid.μ) := by
  classical
  refine ⟨1, by simp, ?_⟩
  intro f hf hfLp
  let μI : ℝ≥0∞ := G.grid.μ Set.univ
  let a : ℝ := 1 / p.toReal - s - 1 / 2
  have hpR_pos : 0 < p.toReal := ennreal_toReal_pos_of_one_le_lt_top p hp_top
  have hp_ne_zero : p ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hμI_pos : 0 < μI := by
    dsimp [μI]
    exact G.grid.positive_measure 0 Set.univ (by simp [G.grid.grid.first_partition_eq_univ])
  have hμI_ne_zero : μI ≠ 0 := ne_of_gt hμI_pos
  have hμI_ne_top : μI ≠ ∞ := by
    dsimp [μI]
    exact univ_measure_ne_top G
  have hμ_pos_real : 0 < (G.grid.μ Set.univ).toReal := univ_measure_toReal_pos G
  have hweight_nonneg : 0 ≤ (G.grid.μ Set.univ).toReal ^ a :=
    (Real.rpow_pos_of_pos hμ_pos_real a).le
  have hfather_eq :
      fatherTerm G F s p f hf =
        μI ^ a * ENNReal.ofReal ‖Coeff G F f hf .alpha‖ := by
    calc
      fatherTerm G F s p f hf
          = ENNReal.ofReal
              (((G.grid.μ Set.univ).toReal ^ a) *
                ‖Coeff G F f hf .alpha‖) := by
                simp [fatherTerm, a]
      _ = ENNReal.ofReal ((G.grid.μ Set.univ).toReal ^ a) *
            ENNReal.ofReal ‖Coeff G F f hf .alpha‖ := by
              rw [ENNReal.ofReal_mul hweight_nonneg]
      _ = μI ^ a * ENNReal.ofReal ‖Coeff G F f hf .alpha‖ := by
              rw [ofReal_univ_measure_toReal_rpow G a]
  have hcoeff :
      ENNReal.ofReal ‖Coeff G F f hf .alpha‖ ≤
        μI ^ (1 / 2 - 1 / p.toReal) * MeasureTheory.eLpNorm f p G.grid.μ := by
    calc
      ENNReal.ofReal ‖Coeff G F f hf .alpha‖
          = ‖Coeff G F f hf .alpha‖ₑ := by rw [ofReal_norm_eq_enorm]
      _ ≤ ∫⁻ x, ‖f x * L2normalizedHaar G F .alpha x‖ₑ ∂G.grid.μ := by
            simpa [Coeff] using
              (MeasureTheory.enorm_integral_le_lintegral_enorm
                (fun x => f x * L2normalizedHaar G F .alpha x)
                (μ := G.grid.μ))
      _ = ∫⁻ x, ‖f x‖ₑ * μI ^ (-(1 : ℝ) / 2) ∂G.grid.μ := by
            congr 1
            ext x
            rw [enorm_mul, l2normalizedHaar_alpha_enorm_eq G F x]
      _ = (∫⁻ x, ‖f x‖ₑ ∂G.grid.μ) * μI ^ (-(1 : ℝ) / 2) := by
            rw [MeasureTheory.lintegral_mul_const']
            exact ENNReal.rpow_ne_top_of_ne_zero hμI_ne_zero hμI_ne_top
      _ = MeasureTheory.eLpNorm f 1 G.grid.μ * μI ^ (-(1 : ℝ) / 2) := by
            rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      _ ≤ (MeasureTheory.eLpNorm f p G.grid.μ *
              μI ^ (1 - 1 / p.toReal)) * μI ^ (-(1 : ℝ) / 2) := by
            have hLp1 :
                MeasureTheory.eLpNorm f 1 G.grid.μ ≤
                  MeasureTheory.eLpNorm f p G.grid.μ * μI ^ (1 - 1 / p.toReal) := by
              simpa [μI] using
                (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
                (p := (1 : ℝ≥0∞)) (q := p)
                (by simpa using (Fact.out : (1 : ℝ≥0∞) ≤ p))
                hfLp.1)
            exact mul_le_mul_right' hLp1 (μI ^ (-(1 : ℝ) / 2))
      _ = μI ^ (1 / 2 - 1 / p.toReal) * MeasureTheory.eLpNorm f p G.grid.μ := by
            calc
              (MeasureTheory.eLpNorm f p G.grid.μ *
                    μI ^ (1 - 1 / p.toReal)) * μI ^ (-(1 : ℝ) / 2)
                  = MeasureTheory.eLpNorm f p G.grid.μ *
                      (μI ^ (1 - 1 / p.toReal) * μI ^ (-(1 : ℝ) / 2)) := by
                        ac_rfl
              _ = MeasureTheory.eLpNorm f p G.grid.μ *
                    μI ^ (1 / 2 - 1 / p.toReal) := by
                        rw [← ENNReal.rpow_add (1 - 1 / p.toReal)
                          (-(1 : ℝ) / 2) hμI_ne_zero hμI_ne_top]
                        ring_nf
              _ = μI ^ (1 / 2 - 1 / p.toReal) *
                    MeasureTheory.eLpNorm f p G.grid.μ := by
                        rw [mul_comm]
  calc
    fatherTerm G F s p f hf
        = μI ^ a * ENNReal.ofReal ‖Coeff G F f hf .alpha‖ := hfather_eq
    _ ≤ μI ^ a *
          (μI ^ (1 / 2 - 1 / p.toReal) * MeasureTheory.eLpNorm f p G.grid.μ) := by
          exact mul_le_mul_left' hcoeff (μI ^ a)
    _ = μI ^ (-s) * MeasureTheory.eLpNorm f p G.grid.μ := by
          calc
            μI ^ a *
                (μI ^ (1 / 2 - 1 / p.toReal) * MeasureTheory.eLpNorm f p G.grid.μ)
                = (μI ^ a * μI ^ (1 / 2 - 1 / p.toReal)) *
                    MeasureTheory.eLpNorm f p G.grid.μ := by
                    ac_rfl
            _ = μI ^ (-s) * MeasureTheory.eLpNorm f p G.grid.μ := by
                    rw [← ENNReal.rpow_add a (1 / 2 - 1 / p.toReal)
                      hμI_ne_zero hμI_ne_top]
                    congr 1
                    simp [a]
    _ = 1 * (μI ^ (-s) * MeasureTheory.eLpNorm f p G.grid.μ) := by simp

/--
Analytic cell estimate behind the levelwise Haar/oscillation comparison.

For each parent cell `Q`, the sum of the `p`-powers of all Haar coefficients
inside `Q` is controlled by the local oscillation of `f` on `Q`, with the
scaling predicted by the manuscript:
`|d_S| ≤ C osc_p(f,Q) μ(Q)^(1/p' - 1/2)`.

This is the only genuinely analytic ingredient still isolated in this file.
Its proof should choose an almost-minimizing constant for `osc_p(f,Q)`, use the
zero mean of the wavelets in `H_Q`, apply Hölder, and finally use the uniform
finite bound for the number of branches over a good-grid cell.
-/
theorem exists_cellCoeffPower_le_const_mul_cellOscillationPower
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞) :
    ∃ Ccell : ℝ≥0∞, Ccell ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ), MemLp f p G.grid.μ →
        ∀ Q : GoodGridCell G,
          cellCoeffPower G F p f hf Q ≤
            Ccell *
              ((G.grid.μ Q.cell) ^ (p.toReal / 2 - 1) *
                (MeanOscillation.osc G p f Q) ^ p.toReal) := by
  classical
  rcases StandardAtomicRepresentation.exists_branchIncidenceBound G F with ⟨M, hM⟩
  let Ccell : ℝ≥0∞ :=
    ((M + 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal
  have hpR_pos : 0 < p.toReal := ennreal_toReal_pos_of_one_le_lt_top p hp_top
  have hpR_nonneg : 0 ≤ p.toReal := hpR_pos.le
  have hc₂_ofReal_pos : 0 < ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) := by
    exact ENNReal.ofReal_pos.2 (StandardAtomicRepresentation.c₂_pos G)
  have hc₂pow_ne_zero :
      ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal ≠ 0 :=
    (ENNReal.rpow_pos hc₂_ofReal_pos ENNReal.ofReal_ne_top).ne'
  have hc₂pow_ne_top :
      ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hpR_nonneg ENNReal.ofReal_ne_top
  have hCcell_ne_zero : Ccell ≠ 0 := by
    dsimp [Ccell]
    exact mul_ne_zero (by simp) hc₂pow_ne_zero
  have hCcell_ne_top : Ccell ≠ ∞ := by
    dsimp [Ccell]
    exact ENNReal.mul_ne_top (by simp) hc₂pow_ne_top
  refine ⟨Ccell, hCcell_ne_top, ?_⟩
  intro f hf hfLp Q
  let μfac : ℝ≥0∞ := (G.grid.μ Q.cell) ^ (p.toReal / 2 - 1)
  let E : ℂ → ℝ≥0∞ := fun c =>
    MeasureTheory.eLpNorm (fun x => f x - c) p (G.grid.μ.restrict Q.cell)
  have hμfac_ne_zero : μfac ≠ 0 := by
    dsimp [μfac]
    exact (ENNReal.rpow_pos (GoodGridCell.measure_pos Q) (GoodGridCell.measure_ne_top Q)).ne'
  have hμfac_ne_top : μfac ≠ ∞ := by
    dsimp [μfac]
    exact ENNReal.rpow_ne_top_of_ne_zero (ne_of_gt (GoodGridCell.measure_pos Q))
      (GoodGridCell.measure_ne_top Q)
  let A : ℝ≥0∞ := Ccell * μfac
  have hA_ne_zero : A ≠ 0 := by
    dsimp [A]
    exact mul_ne_zero hCcell_ne_zero hμfac_ne_zero
  have hA_ne_top : A ≠ ∞ := by
    dsimp [A]
    exact ENNReal.mul_ne_top hCcell_ne_top hμfac_ne_top
  have hle_all :
      ∀ c : ℂ,
        cellCoeffPower G F p f hf Q ≤ Ccell * (μfac * (E c) ^ p.toReal) := by
    intro c
    have hbase :=
      cellCoeffPower_le_const_mul_cellOscillationPower_of_const
        G F p hp_top hM f hf hfLp Q c
    have hM_le : ((M : ℕ) : ℝ≥0∞) ≤ ((M + 1 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast Nat.le_succ M
    calc
      cellCoeffPower G F p f hf Q
          ≤ (M : ℝ≥0∞) *
              (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal *
                (μfac * (E c) ^ p.toReal)) := by
            simpa [μfac, E] using hbase
      _ ≤ ((M + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal (StandardAtomicRepresentation.c₂ G) ^ p.toReal *
                (μfac * (E c) ^ p.toReal)) := by
            exact mul_le_mul_right' hM_le _
      _ = Ccell * (μfac * (E c) ^ p.toReal) := by
            simp [Ccell, mul_assoc]
  have hle_iInf :
      cellCoeffPower G F p f hf Q ≤
        ⨅ c : ℂ, Ccell * (μfac * (E c) ^ p.toReal) :=
    le_iInf hle_all
  have hosc_iInf :
      MeanOscillation.osc G p f Q = ⨅ c : ℂ, E c := by
    rw [MeanOscillation.osc]
    exact sInf_range
  have hpow_iInf :
      (MeanOscillation.osc G p f Q) ^ p.toReal =
        ⨅ c : ℂ, (E c) ^ p.toReal := by
    rw [hosc_iInf]
    exact iInf_rpow_of_pos E hpR_pos
  have hiInf_const :
      (⨅ c : ℂ, Ccell * (μfac * (E c) ^ p.toReal)) =
        Ccell * (μfac * (MeanOscillation.osc G p f Q) ^ p.toReal) := by
    calc
      (⨅ c : ℂ, Ccell * (μfac * (E c) ^ p.toReal))
          = ⨅ c : ℂ, A * (E c) ^ p.toReal := by
            congr
            ext c
            simp [A, mul_assoc]
      _ = A * (⨅ c : ℂ, (E c) ^ p.toReal) := by
            rw [← ENNReal.mul_iInf_of_ne hA_ne_zero hA_ne_top]
      _ = Ccell * (μfac * (MeanOscillation.osc G p f Q) ^ p.toReal) := by
            rw [← hpow_iInf]
            simp [A, mul_assoc]
  calc
    cellCoeffPower G F p f hf Q
        ≤ ⨅ c : ℂ, Ccell * (μfac * (E c) ^ p.toReal) := hle_iInf
    _ = Ccell *
          ((G.grid.μ Q.cell) ^ (p.toReal / 2 - 1) *
            (MeanOscillation.osc G p f Q) ^ p.toReal) := by
          rw [hiInf_const]

/--
If the analytic estimate is known on every cell, then the corresponding
level-`k` Haar block is controlled by the level-`k` oscillation block.

This lemma is just the exponent bookkeeping
`1 - sp - p/2 + (p/2 - 1) = -sp` and summation over the level.
-/
theorem levelHaarBlock_le_const_mul_levelOscillationBlock_of_cell_bound
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp_top : p < ∞)
    (Ccell : ℝ≥0∞)
    (hcell :
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ), MemLp f p G.grid.μ →
        ∀ Q : GoodGridCell G,
          cellCoeffPower G F p f hf Q ≤
            Ccell *
              ((G.grid.μ Q.cell) ^ (p.toReal / 2 - 1) *
                (MeanOscillation.osc G p f Q) ^ p.toReal)) :
    ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ), MemLp f p G.grid.μ →
      ∀ k,
        levelHaarBlock G F s p f hf k ≤
          Ccell * MeanOscillation.levelOscillationBlock G s p f k := by
  classical
  intro f hf hfLp k
  simp only [levelHaarBlock, MeanOscillation.levelOscillationBlock]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro Q _hQ
  let Qcell : GoodGridCell G :=
    { level := k
      cell := Q.1
      mem := Q.2 }
  let μQ : ℝ≥0∞ := G.grid.μ Q.1
  let a : ℝ := 1 - s * p.toReal - p.toReal / 2
  let b : ℝ := p.toReal / 2 - 1
  have hμQ_ne_zero : μQ ≠ 0 := by
    dsimp [μQ, Qcell]
    exact ne_of_gt (GoodGridCell.measure_pos Qcell)
  have hμQ_ne_top : μQ ≠ ∞ := by
    dsimp [μQ, Qcell]
    exact GoodGridCell.measure_ne_top Qcell
  have hweight :
      ENNReal.ofReal ((G.grid.μ Q.1).toReal ^ a) = μQ ^ a := by
    simpa [μQ, Qcell, a] using ofReal_cell_measure_toReal_rpow G Qcell a
  have hcellQ := hcell f hf hfLp Qcell
  calc
    ENNReal.ofReal ((G.grid.μ Q.1).toReal ^ a) *
        cellCoeffPower G F p f hf Qcell
        ≤ μQ ^ a *
            (Ccell *
              (μQ ^ b *
                (MeanOscillation.osc G p f Qcell) ^ p.toReal)) := by
          rw [hweight]
          exact mul_le_mul_left' hcellQ (μQ ^ a)
    _ = Ccell *
          (μQ ^ (-(s * p.toReal)) *
            (MeanOscillation.osc G p f Qcell) ^ p.toReal) := by
          calc
            μQ ^ a *
                (Ccell *
                  (μQ ^ b *
                    (MeanOscillation.osc G p f Qcell) ^ p.toReal))
                = Ccell *
                    ((μQ ^ a * μQ ^ b) *
                      (MeanOscillation.osc G p f Qcell) ^ p.toReal) := by
                    ac_rfl
            _ = Ccell *
                  (μQ ^ (-(s * p.toReal)) *
                    (MeanOscillation.osc G p f Qcell) ^ p.toReal) := by
                    rw [← ENNReal.rpow_add a b hμQ_ne_zero hμQ_ne_top]
                    congr 2
                    simp [a, b]

/--
Levelwise Haar block estimate used in the comparison with oscillation.

This is the formal target for the manuscript argument: choose an almost
minimizing constant `c_Q` for `osc_p(f,Q)`, use that every wavelet in `H_Q`
has zero mean on `Q`, apply Hölder to
`∫_Q (f - c_Q) φ_S`, and sum over `S ∈ H_Q`.
-/
theorem exists_levelHaarBlockRoot_le_const_mul_levelOscillationBlockRoot
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞) :
    ∃ Cpos : ℝ≥0∞, Cpos ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ), MemLp f p G.grid.μ →
        ∀ k,
          (levelHaarBlock G F s p f hf k) ^ (1 / p.toReal) ≤
            Cpos * (MeanOscillation.levelOscillationBlock G s p f k) ^
              (1 / p.toReal) := by
  classical
  rcases exists_cellCoeffPower_le_const_mul_cellOscillationPower G F p hp_top with
    ⟨Ccell, hCcell_fin, hcell⟩
  let Cpos : ℝ≥0∞ := Ccell ^ (1 / p.toReal)
  have hpR_pos : 0 < p.toReal := ennreal_toReal_pos_of_one_le_lt_top p hp_top
  refine ⟨Cpos, ?_, ?_⟩
  · exact ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 hpR_pos.le) hCcell_fin
  · intro f hf hfLp k
    have hlevel :=
      levelHaarBlock_le_const_mul_levelOscillationBlock_of_cell_bound
        G F s p hp_top Ccell hcell f hf hfLp k
    calc
      (levelHaarBlock G F s p f hf k) ^ (1 / p.toReal)
          ≤ (Ccell * MeanOscillation.levelOscillationBlock G s p f k) ^
              (1 / p.toReal) := by
            exact ENNReal.rpow_le_rpow hlevel (one_div_nonneg.2 hpR_pos.le)
      _ = Cpos * (MeanOscillation.levelOscillationBlock G s p f k) ^
            (1 / p.toReal) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hpR_pos.le)]

/--
There is a finite constant controlling the Haar representation norm by the
mean-oscillation norm.

The hypotheses match the analytic content of the paper: `f` is an `L^p`
function and its mean-oscillation norm is finite.  The finiteness assumption is
kept in the statement because this is the intended application, although the
formal inequality is meaningful even when the right-hand side is infinite.
-/
theorem exists_haarL2RepresentationNorm_le_const_mul_meanOscillationNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ), MemLp f p G.grid.μ →
        MeanOscillation.meanOscillationNorm G s p q f ≠ ∞ →
          haarL2RepresentationNorm G F s p q f hf ≤
            C * MeanOscillation.meanOscillationNorm G s p q f := by
  classical
  rcases exists_fatherTerm_le_const_mul_meanOscillationLpTerm G F s p hp_top with
    ⟨C0, hC0_fin, hfather⟩
  rcases exists_levelHaarBlockRoot_le_const_mul_levelOscillationBlockRoot G F s p hp_top with
    ⟨Cpos, hCpos_fin, hlevels⟩
  refine ⟨C0 + Cpos, ENNReal.add_ne_top.mpr ⟨hC0_fin, hCpos_fin⟩, ?_⟩
  intro f hf hfLp _hfinite
  exact haarL2RepresentationNorm_le_of_level_bounds G F s p hp_top q C0 Cpos f hf
    (hfather f hf hfLp) (hlevels f hf hfLp)

end HaarRepresentation

end

end GoodGridSpace
