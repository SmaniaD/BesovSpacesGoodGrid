import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.StandarRepresentationNormleqBesovNorm
import BesovSpacesGoodGrid.WeakGrid.Multipliers

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

/--
Finite mean oscillation supplies a Souza-Besov element.

This is the packaging bridge used for left compositions: once a concrete
integrable representative has finite mean-oscillation gauge, the existing
Haar and standard-representation comparison theorems turn it into an element
of the Souza-Besov space.
-/
theorem exists_souzaBesovSpace_of_meanOscillationNorm_ne_top
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem
      (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (hfLp : MemLp f p G.grid.μ)
    (hmean : meanOscillationNorm G s p q f ≠ ∞) :
    ∃ y : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top),
      (y : Lp ℂ p G.toWeakGridSpace.measure) = hfLp.toLp f := by
  classical
  rcases HaarRepresentation.exists_haarL2RepresentationNorm_le_const_mul_meanOscillationNorm
      (G := G) (F := F) (s := s) (p := p) (hp_top := hp_top) (q := q) with
    ⟨Chaar, hChaar_fin, hhaar_le_mean⟩
  rcases StandardAtomicRepresentation.exists_standardRepresentationNorm_le_const_mul_haarL2RepresentationNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q) with
    ⟨Cst, hCst_fin, hstandard_le_haar⟩
  have hhaar_le :
      HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≤
        Chaar * meanOscillationNorm G s p q f :=
    hhaar_le_mean f hf hfLp hmean
  have hhaar_ne_top :
      HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hChaar_fin hmean) hhaar_le
  rcases hstandard_le_haar f hf hhaar_ne_top with ⟨hstandard_ne_top, _hstandard_le⟩
  rcases exists_souzaBesovSpace_of_standardRepresentationNorm_ne_top
      (G := G) (F := F) (s := s) (hs := hs) (p := p)
      (hp_top := hp_top) (q := q) f hf hstandard_ne_top with
    ⟨hfLp', y, hy⟩
  refine ⟨y, ?_⟩
  rw [hy]

/--
Finite mean oscillation controls the Souza-Besov gauge, up to a finite
constant.

This is the quantitative version of
`exists_souzaBesovSpace_of_meanOscillationNorm_ne_top`.  The bound is stated in
`ℝ≥0∞` using `ENNReal.ofReal` because the comparison norms in the
Haar/oscillation layer are naturally extended nonnegative reals.
-/
theorem exists_souzaBesovSpace_norm_le_const_mul_meanOscillationNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem
      (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (_ : Integrable f G.grid.μ) (_ : MemLp f p G.grid.μ),
        meanOscillationNorm G s p q f ≠ ∞ →
          ∃ y : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top),
            WeakGridSpace.RepresentsFunction (G := G.toWeakGridSpace) (p := p)
              f (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
            ENNReal.ofReal
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q y) ≤
              C * meanOscillationNorm G s p q f := by
  classical
  rcases HaarRepresentation.exists_haarL2RepresentationNorm_le_const_mul_meanOscillationNorm
      (G := G) (F := F) (s := s) (p := p) (hp_top := hp_top) (q := q) with
    ⟨Chaar, hChaar_fin, hhaar_le_mean⟩
  rcases StandardAtomicRepresentation.exists_standardRepresentationNorm_le_const_mul_haarL2RepresentationNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q) with
    ⟨Cst, hCst_fin, hstandard_le_haar⟩
  refine ⟨Cst * Chaar, ENNReal.mul_ne_top hCst_fin hChaar_fin, ?_⟩
  intro f hf hfLp hmean
  have hhaar_le :
      HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≤
        Chaar * meanOscillationNorm G s p q f :=
    hhaar_le_mean f hf hfLp hmean
  have hhaar_ne_top :
      HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hChaar_fin hmean) hhaar_le
  rcases hstandard_le_haar f hf hhaar_ne_top with
    ⟨hstandard_ne_top, hstandard_le⟩
  rcases exists_souzaBesovSpace_representation_of_standardRepresentationNorm_ne_top
      (G := G) (F := F) (s := s) (hs := hs) (p := p)
      (hp_top := hp_top) (q := q) f hf hstandard_ne_top with
    ⟨hfLp', y, R, hRfin, hy, hRcost⟩
  have hrep :
      WeakGridSpace.RepresentsFunction (G := G.toWeakGridSpace) (p := p)
        f (y : Lp ℂ p G.toWeakGridSpace.measure) := by
    change ((y : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =ᵐ[G.grid.μ] f
    rw [hy]
    exact MemLp.coeFn_toLp hfLp'
  have hNorm_le_cost :
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q y ≤
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
      (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
      (q := q) y R hRfin
  have hNorm_ofReal_le_cost :
      ENNReal.ofReal
          (WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q y) ≤
        ENNReal.ofReal (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) :=
    ENNReal.ofReal_le_ofReal hNorm_le_cost
  have hcost_le_standard :
      ENNReal.ofReal (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) ≤
        StandardAtomicRepresentation.standardRepresentationNorm
          G F s hs p hp_top q f hf := by
    calc
      ENNReal.ofReal (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R)
          ≤ ENNReal.ofReal
              (StandardAtomicRepresentation.standardRepresentationNorm
                G F s hs p hp_top q f hf).toReal :=
        ENNReal.ofReal_le_ofReal hRcost
      _ =
          StandardAtomicRepresentation.standardRepresentationNorm
            G F s hs p hp_top q f hf := by
        exact ENNReal.ofReal_toReal hstandard_ne_top
  have hstandard_le_mean :
      StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_top q f hf ≤
        (Cst * Chaar) * meanOscillationNorm G s p q f := by
    calc
      StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_top q f hf
          ≤ Cst * HaarRepresentation.haarL2RepresentationNorm G F s p q f hf :=
        hstandard_le
      _ ≤ Cst * (Chaar * meanOscillationNorm G s p q f) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_right hhaar_le Cst
      _ = (Cst * Chaar) * meanOscillationNorm G s p q f := by
        rw [mul_assoc]
  refine ⟨y, hrep, ?_⟩
  exact le_trans hNorm_ofReal_le_cost (le_trans hcost_le_standard hstandard_le_mean)

/--
Left composition is well-defined on the Souza-Besov space.

If a concrete representative `f` represents a Souza-Besov element and `g` is
Lipschitz with `g 0 = 0`, then `g ∘ f` also represents a Souza-Besov element.
This packages the paper's Proposition `expo` at the space-membership level;
the pointwise analytic estimate is
`meanOscillationNorm_comp_le_of_lipschitzWith`.
-/
theorem exists_souzaBesovSpace_leftComposition_of_lipschitzWith
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem
      (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    {K : NNReal} {g : ℂ → ℂ} (hg : LipschitzWith K g) (hg_zero : g 0 = 0)
    (x : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top))
    (f : α → ℂ)
    (hxf :
      f =ᵐ[G.grid.μ] ((x : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)) :
    ∃ y : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top),
      WeakGridSpace.RepresentsFunction (G := G.toWeakGridSpace) (p := p)
        (fun z => g (f z)) (y : Lp ℂ p G.toWeakGridSpace.measure) := by
  classical
  let μ := G.grid.μ
  letI : IsFiniteMeasure μ := G.grid.isFinite
  have hfLp : MemLp f p μ := by
    exact MeasureTheory.MemLp.ae_eq hxf.symm
      (Lp.memLp (x : Lp ℂ p G.toWeakGridSpace.measure))
  have hgfLp : MemLp (fun z => g (f z)) p μ :=
    hg.comp_memLp hg_zero hfLp
  have hgf : Integrable (fun z => g (f z)) μ :=
    hgfLp.integrable (Fact.out : 1 ≤ p)
  rcases exists_meanOscillationNorm_le_const_mul_souzaBesovNorm
      (G := G) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q) with
    ⟨Cosc, hCosc_fin, hmean_le_besov⟩
  have hmean_f_le :
      meanOscillationNorm G s p q f ≤
        Cosc *
          ENNReal.ofReal
            (WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q x) := by
    exact hmean_le_besov x f hxf
  have hmean_f_ne_top : meanOscillationNorm G s p q f ≠ ∞ := by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hCosc_fin ENNReal.ofReal_ne_top) hmean_f_le
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
      hp_top.ne
  have hq_pos : q ≠ ∞ → 0 < q.toReal := by
    intro hq_top
    exact ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq_top
  have hmean_comp_le :
      meanOscillationNorm G s p q (fun z => g (f z)) ≤
        (K : ℝ≥0∞) * meanOscillationNorm G s p q f :=
    meanOscillationNorm_comp_le_of_lipschitzWith G hg hg_zero s p q hp_pos hq_pos f
  have hmean_comp_ne_top :
      meanOscillationNorm G s p q (fun z => g (f z)) ≠ ∞ := by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hmean_f_ne_top) hmean_comp_le
  rcases exists_souzaBesovSpace_of_meanOscillationNorm_ne_top
      (G := G) (F := F) (s := s) (hs := hs) (p := p)
      (hp_top := hp_top) (q := q) (fun z => g (f z)) hgf hgfLp
      hmean_comp_ne_top with
    ⟨y, hy⟩
  refine ⟨y, ?_⟩
  change ((y : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =ᵐ[μ] fun z => g (f z)
  rw [hy]
  exact MemLp.coeFn_toLp hgfLp

/--
Quantitative Souza-Besov boundedness of left composition.

For every Lipschitz map `g : ℂ → ℂ` fixing zero, composition on the left sends
Souza-Besov representatives to Souza-Besov representatives, with the
Souza-Besov gauge bounded by a grid/exponent constant times the Lipschitz
constant times the original gauge.
-/
theorem exists_souzaBesovSpace_leftComposition_norm_le_of_lipschitzWith
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem
      (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ {K : NNReal} {g : ℂ → ℂ},
        LipschitzWith K g → g 0 = 0 →
          ∀ (x : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top))
            (f : α → ℂ),
            f =ᵐ[G.grid.μ] ((x : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) →
              ∃ y : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top),
                WeakGridSpace.RepresentsFunction (G := G.toWeakGridSpace) (p := p)
                  (fun z => g (f z)) (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
                ENNReal.ofReal
                    (WeakGridSpace.BesovishSpace.Norm_Costpq
                      (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q y) ≤
                  C * (K : ℝ≥0∞) *
                    ENNReal.ofReal
                      (WeakGridSpace.BesovishSpace.Norm_Costpq
                        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q x) := by
  classical
  rcases exists_souzaBesovSpace_norm_le_const_mul_meanOscillationNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p)
      (hp_top := hp_top) (q := q) with
    ⟨Cmo, hCmo_fin, hmo_to_besov⟩
  rcases exists_meanOscillationNorm_le_const_mul_souzaBesovNorm
      (G := G) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q) with
    ⟨Cbesov, hCbesov_fin, hbesov_to_mo⟩
  refine ⟨Cmo * Cbesov, ENNReal.mul_ne_top hCmo_fin hCbesov_fin, ?_⟩
  intro K g hg hg_zero x f hxf
  let μ := G.grid.μ
  letI : IsFiniteMeasure μ := G.grid.isFinite
  let A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)
  let Nx : ℝ≥0∞ := ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq A q x)
  have hfLp : MemLp f p μ := by
    exact MeasureTheory.MemLp.ae_eq hxf.symm
      (Lp.memLp (x : Lp ℂ p G.toWeakGridSpace.measure))
  have hgfLp : MemLp (fun z => g (f z)) p μ :=
    hg.comp_memLp hg_zero hfLp
  have hgf : Integrable (fun z => g (f z)) μ :=
    hgfLp.integrable (Fact.out : 1 ≤ p)
  have hmean_f_le :
      meanOscillationNorm G s p q f ≤ Cbesov * Nx := by
    simpa [A, Nx] using hbesov_to_mo x f hxf
  have hmean_f_ne_top : meanOscillationNorm G s p q f ≠ ∞ := by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hCbesov_fin ENNReal.ofReal_ne_top) hmean_f_le
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
      hp_top.ne
  have hq_pos : q ≠ ∞ → 0 < q.toReal := by
    intro hq_top
    exact ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq_top
  have hmean_comp_le :
      meanOscillationNorm G s p q (fun z => g (f z)) ≤
        (K : ℝ≥0∞) * meanOscillationNorm G s p q f :=
    meanOscillationNorm_comp_le_of_lipschitzWith G hg hg_zero s p q hp_pos hq_pos f
  have hmean_comp_ne_top :
      meanOscillationNorm G s p q (fun z => g (f z)) ≠ ∞ := by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hmean_f_ne_top) hmean_comp_le
  rcases hmo_to_besov (fun z => g (f z)) hgf hgfLp hmean_comp_ne_top with
    ⟨y, hy_rep, hy_norm⟩
  refine ⟨y, hy_rep, ?_⟩
  calc
    ENNReal.ofReal
        (WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q y)
        ≤ Cmo * meanOscillationNorm G s p q (fun z => g (f z)) := hy_norm
    _ ≤ Cmo * ((K : ℝ≥0∞) * meanOscillationNorm G s p q f) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_right hmean_comp_le Cmo
    _ ≤ Cmo * ((K : ℝ≥0∞) * (Cbesov * Nx)) := by
        have hmul := mul_le_mul_right hmean_f_le (K : ℝ≥0∞)
        have hmul' := mul_le_mul_right hmul Cmo
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
    _ = (Cmo * Cbesov) * (K : ℝ≥0∞) * Nx := by
        ac_rfl
    _ =
        (Cmo * Cbesov) * (K : ℝ≥0∞) *
          ENNReal.ofReal
            (WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q x) := by
        rfl

end MeanOscillation

end

end GoodGridSpace
