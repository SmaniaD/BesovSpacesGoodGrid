import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.MeanOscillationNorm

/-!
# Left compositions

This file formalizes the elementary estimate behind the paper's left
composition result for the mean-oscillation model of Souza-Besov spaces.

If `g : ℂ → ℂ` is Lipschitz and fixes zero, then composing a function on the
left by `g` does not increase the `L^p` term or the mean-oscillation seminorm
by more than the Lipschitz constant.  The proof is the direct one from the
manuscript: test the oscillation of `g ∘ f` against the constants `g c`, and
use the pointwise Lipschitz inequality.
-/

open scoped ENNReal BigOperators
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace MeanOscillation

/--
The `L^p` seminorm of a Lipschitz composition is controlled by the Lipschitz
constant, provided the function fixes zero.

This is the formal version of `|g ∘ f|_p ≤ K |f|_p`.
-/
theorem eLpNorm_comp_le_of_lipschitzWith
    {K : NNReal} {g : ℂ → ℂ} (hg : LipschitzWith K g) (hg_zero : g 0 = 0)
    (μ : Measure α) (p : ℝ≥0∞) (f : α → ℂ) :
    eLpNorm (fun x => g (f x)) p μ ≤
      (K : ℝ≥0∞) * eLpNorm f p μ := by
  calc
    eLpNorm (fun x => g (f x)) p μ
        = eLpNorm (fun x => g (f x) - g 0) p μ := by
            refine eLpNorm_congr_ae ?_
            filter_upwards with x
            simp only [hg_zero, sub_zero]
    _ ≤ eLpNorm (fun x => (K : ℂ) • f x) p μ := by
          refine eLpNorm_mono_ae ?_
          filter_upwards with x
          have hdist := hg.dist_le_mul (f x) 0
          simpa [dist_eq_norm, sub_zero, norm_smul, Complex.norm_real,
            Real.norm_of_nonneg K.coe_nonneg] using hdist
    _ = (K : ℝ≥0∞) * eLpNorm f p μ := by
          change eLpNorm ((K : ℂ) • f) p μ = (K : ℝ≥0∞) * eLpNorm f p μ
          rw [eLpNorm_const_smul]
          simp [enorm]

/--
The restricted `L^p` distance from `g ∘ f` to the constant `g c` is controlled
by the corresponding distance from `f` to `c`.
-/
theorem eLpNorm_comp_sub_const_le_of_lipschitzWith
    {K : NNReal} {g : ℂ → ℂ} (hg : LipschitzWith K g)
    (μ : Measure α) (p : ℝ≥0∞) (f : α → ℂ) (c : ℂ) :
    eLpNorm (fun x => g (f x) - g c) p μ ≤
      (K : ℝ≥0∞) * eLpNorm (fun x => f x - c) p μ := by
  calc
    eLpNorm (fun x => g (f x) - g c) p μ
        ≤ eLpNorm (fun x => (K : ℂ) • (f x - c)) p μ := by
          refine eLpNorm_mono_ae ?_
          filter_upwards with x
          have hdist := hg.dist_le_mul (f x) c
          simpa [dist_eq_norm, norm_smul, Complex.norm_real,
            Real.norm_of_nonneg K.coe_nonneg] using hdist
    _ = (K : ℝ≥0∞) * eLpNorm (fun x => f x - c) p μ := by
          change eLpNorm ((K : ℂ) • fun x => f x - c) p μ =
            (K : ℝ≥0∞) * eLpNorm (fun x => f x - c) p μ
          rw [eLpNorm_const_smul]
          simp [enorm]

/--
Local oscillation is Lipschitz-stable under left composition.

This is the displayed estimate `osc_p(g ∘ f, Q) ≤ K osc_p(f, Q)` in the paper.
-/
theorem osc_comp_le_of_lipschitzWith
    (G : GoodGridSpace (α := α)) {K : NNReal} {g : ℂ → ℂ}
    (hg : LipschitzWith K g) (p : ℝ≥0∞) (f : α → ℂ) (Q : GoodGridCell G) :
    osc G p (fun x => g (f x)) Q ≤ (K : ℝ≥0∞) * osc G p f Q := by
  by_cases hK : K = 0
  · have hg_const : ∀ z : ℂ, g z = g 0 := by
      intro z
      have hdist := hg.dist_le_mul z 0
      have hdist_zero : dist (g z) (g 0) = 0 := by
        apply le_antisymm
        · simpa [hK] using hdist
        · exact dist_nonneg
      exact dist_eq_zero.mp hdist_zero
    rw [osc_eq_zero_of_eq_const_on_cell G p (fun x => g (f x)) Q (g 0)]
    · simp [hK]
    · intro x _hx
      exact hg_const (f x)
  · unfold osc
    rw [sInf_range, sInf_range]
    rw [ENNReal.mul_iInf_of_ne (ENNReal.coe_ne_zero.mpr hK) ENNReal.coe_ne_top]
    refine le_iInf fun c => ?_
    exact iInf_le_of_le (g c)
      (eLpNorm_comp_sub_const_le_of_lipschitzWith
        (α := α) hg (G.grid.μ.restrict Q.cell) p f c)

/--
Each level of the oscillation gauge is controlled by the `p`-th power of the
Lipschitz constant.
-/
theorem levelOscillationBlock_comp_le_of_lipschitzWith
    (G : GoodGridSpace (α := α)) {K : NNReal} {g : ℂ → ℂ}
    (hg : LipschitzWith K g) (s : ℝ) (p : ℝ≥0∞) (hp : 0 ≤ p.toReal)
    (f : α → ℂ) (k : ℕ) :
    levelOscillationBlock G s p (fun x => g (f x)) k ≤
      ((K : ℝ≥0∞) ^ p.toReal) * levelOscillationBlock G s p f k := by
  unfold levelOscillationBlock
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro Q _hQ
  let Qcell : GoodGridCell G := { level := k, cell := Q.1, mem := Q.2 }
  have hosc :
      osc G p (fun x => g (f x)) Qcell ^ p.toReal ≤
        ((K : ℝ≥0∞) * osc G p f Qcell) ^ p.toReal :=
    ENNReal.rpow_le_rpow (osc_comp_le_of_lipschitzWith G hg p f Qcell) hp
  calc
    (G.grid.μ Q.1) ^ (-(s * p.toReal)) *
        osc G p (fun x => g (f x)) Qcell ^ p.toReal
        ≤ (G.grid.μ Q.1) ^ (-(s * p.toReal)) *
            ((K : ℝ≥0∞) * osc G p f Qcell) ^ p.toReal :=
          mul_le_mul' le_rfl hosc
    _ = (K : ℝ≥0∞) ^ p.toReal *
          ((G.grid.μ Q.1) ^ (-(s * p.toReal)) *
            osc G p f Qcell ^ p.toReal) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
          ac_rfl

/--
The level-root form of the previous estimate.  This is the shape used directly
in the `q = ∞` oscillation seminorm.
-/
theorem levelOscillationBlock_root_comp_le_of_lipschitzWith
    (G : GoodGridSpace (α := α)) {K : NNReal} {g : ℂ → ℂ}
    (hg : LipschitzWith K g) (s : ℝ) (p : ℝ≥0∞) (hp : 0 < p.toReal)
    (f : α → ℂ) (k : ℕ) :
    (levelOscillationBlock G s p (fun x => g (f x)) k) ^ (1 / p.toReal) ≤
      (K : ℝ≥0∞) * (levelOscillationBlock G s p f k) ^ (1 / p.toReal) := by
  have hlevel :=
    levelOscillationBlock_comp_le_of_lipschitzWith G hg s p hp.le f k
  have hroot := ENNReal.rpow_le_rpow hlevel (one_div_nonneg.mpr hp.le)
  calc
    (levelOscillationBlock G s p (fun x => g (f x)) k) ^ (1 / p.toReal)
        ≤ (((K : ℝ≥0∞) ^ p.toReal) *
            levelOscillationBlock G s p f k) ^ (1 / p.toReal) := hroot
    _ = (K : ℝ≥0∞) *
          (levelOscillationBlock G s p f k) ^ (1 / p.toReal) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le)]
          rw [← ENNReal.rpow_mul]
          have hp_cancel : p.toReal * (1 / p.toReal) = 1 := by
            field_simp [hp.ne']
          rw [hp_cancel, ENNReal.rpow_one]

/--
The mean-oscillation seminorm is Lipschitz-stable under left composition.

For `q = ∞` this is the supremum over the level roots.  For finite `q`, the
same level estimate is summed before taking the `q`-root.
-/
theorem oscillationSeminorm_comp_le_of_lipschitzWith
    (G : GoodGridSpace (α := α)) {K : NNReal} {g : ℂ → ℂ}
    (hg : LipschitzWith K g) (s : ℝ) (p q : ℝ≥0∞)
    (hp : 0 < p.toReal) (hq : q ≠ ∞ → 0 < q.toReal) (f : α → ℂ) :
    oscillationSeminorm G s p q (fun x => g (f x)) ≤
      (K : ℝ≥0∞) * oscillationSeminorm G s p q f := by
  by_cases hqtop : q = ∞
  · simp only [oscillationSeminorm, hqtop, ↓reduceIte]
    rw [sSup_range, sSup_range, ENNReal.mul_iSup]
    exact iSup_mono fun k =>
      levelOscillationBlock_root_comp_le_of_lipschitzWith G hg s p hp f k
  · have hqpos : 0 < q.toReal := hq hqtop
    have hq_div_p_nonneg : 0 ≤ q.toReal / p.toReal :=
      div_nonneg hqpos.le hp.le
    have hlevel : ∀ k,
        (levelOscillationBlock G s p (fun x => g (f x)) k) ^
            (q.toReal / p.toReal) ≤
          ((K : ℝ≥0∞) ^ q.toReal) *
            (levelOscillationBlock G s p f k) ^
              (q.toReal / p.toReal) := by
      intro k
      have hbase :=
        levelOscillationBlock_comp_le_of_lipschitzWith G hg s p hp.le f k
      have hpow := ENNReal.rpow_le_rpow hbase hq_div_p_nonneg
      calc
        (levelOscillationBlock G s p (fun x => g (f x)) k) ^
            (q.toReal / p.toReal)
            ≤ (((K : ℝ≥0∞) ^ p.toReal) *
                levelOscillationBlock G s p f k) ^
                  (q.toReal / p.toReal) := hpow
        _ = ((K : ℝ≥0∞) ^ q.toReal) *
              (levelOscillationBlock G s p f k) ^
                (q.toReal / p.toReal) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hq_div_p_nonneg]
              rw [← ENNReal.rpow_mul]
              have hp_cancel :
                  p.toReal * (q.toReal / p.toReal) = q.toReal := by
                field_simp [hp.ne']
              rw [hp_cancel]
    simp only [oscillationSeminorm, hqtop, ↓reduceIte]
    change
      (∑' k, (levelOscillationBlock G s p (fun x => g (f x)) k) ^
          (q.toReal / p.toReal)) ^ (1 / q.toReal) ≤
        (K : ℝ≥0∞) *
          ((∑' k, (levelOscillationBlock G s p f k) ^
            (q.toReal / p.toReal)) ^ (1 / q.toReal))
    have hsum :
        (∑' k, (levelOscillationBlock G s p (fun x => g (f x)) k) ^
            (q.toReal / p.toReal)) ≤
          ((K : ℝ≥0∞) ^ q.toReal) *
            (∑' k, (levelOscillationBlock G s p f k) ^
              (q.toReal / p.toReal)) := by
      rw [← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum hlevel
    have hroot := ENNReal.rpow_le_rpow hsum (one_div_nonneg.mpr hqpos.le)
    calc
      (∑' k, (levelOscillationBlock G s p (fun x => g (f x)) k) ^
          (q.toReal / p.toReal)) ^ (1 / q.toReal)
          ≤ (((K : ℝ≥0∞) ^ q.toReal) *
              (∑' k, (levelOscillationBlock G s p f k) ^
                (q.toReal / p.toReal))) ^ (1 / q.toReal) := hroot
      _ = (K : ℝ≥0∞) *
            (∑' k, (levelOscillationBlock G s p f k) ^
              (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hqpos.le)]
            rw [← ENNReal.rpow_mul]
            have hq_cancel : q.toReal * (1 / q.toReal) = 1 := by
              field_simp [hqpos.ne']
            rw [hq_cancel, ENNReal.rpow_one]

/--
The full mean-oscillation gauge of a left composition is controlled by the
Lipschitz constant.  This packages the two estimates from the proof:
`|g ∘ f|_p ≤ K |f|_p` and
`osc^s_{p,q}(g ∘ f) ≤ K osc^s_{p,q}(f)`.
-/
theorem meanOscillationNorm_comp_le_of_lipschitzWith
    (G : GoodGridSpace (α := α)) {K : NNReal} {g : ℂ → ℂ}
    (hg : LipschitzWith K g) (hg_zero : g 0 = 0)
    (s : ℝ) (p q : ℝ≥0∞)
    (hp : 0 < p.toReal) (hq : q ≠ ∞ → 0 < q.toReal) (f : α → ℂ) :
    meanOscillationNorm G s p q (fun x => g (f x)) ≤
      (K : ℝ≥0∞) * meanOscillationNorm G s p q f := by
  unfold meanOscillationNorm
  have hLp :=
    eLpNorm_comp_le_of_lipschitzWith (α := α) hg hg_zero G.grid.μ p f
  have hOsc :=
    oscillationSeminorm_comp_le_of_lipschitzWith G hg s p q hp hq f
  calc
    (G.grid.μ Set.univ) ^ (-s) *
          eLpNorm (fun x => g (f x)) p G.grid.μ +
        oscillationSeminorm G s p q (fun x => g (f x))
        ≤ (G.grid.μ Set.univ) ^ (-s) *
              ((K : ℝ≥0∞) * eLpNorm f p G.grid.μ) +
            (K : ℝ≥0∞) * oscillationSeminorm G s p q f := by
          exact add_le_add (mul_le_mul' le_rfl hLp) hOsc
    _ = (K : ℝ≥0∞) *
          ((G.grid.μ Set.univ) ^ (-s) * eLpNorm f p G.grid.μ +
            oscillationSeminorm G s p q f) := by
          rw [mul_add]
          ac_rfl

end MeanOscillation

end

end GoodGridSpace
