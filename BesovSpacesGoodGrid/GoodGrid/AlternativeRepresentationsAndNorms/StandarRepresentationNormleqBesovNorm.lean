import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.standardNormleqHaarRepresenstionNorm
import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.HaarNormleqOscillationNorm
import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.OscillationNormleqBesovNorm

/-!
# The standard representation norm is controlled by the Souza-Besov norm

This file packages the comparison

`N_st(f) ≤ C ‖f‖_Besov`.

The proof is only bookkeeping from previously established comparisons:

* `N_st ≤ C N_Haar`;
* `N_Haar ≤ C N_osc`;
* `N_osc ≤ C ‖·‖_Besov`.

The statement is formulated for a concrete representative `f` of a
Souza-Besov element `g`, since the standard coefficient norm is defined for
functions with an explicit integrability proof.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace StandardAtomicRepresentation

/--
The standard atomic coefficient norm is controlled by the Souza-Besov gauge.

If `f` is an integrable representative of the `Lp` class `g`, and `g` belongs
to the Souza-Besov space, then the standard representation norm of `f` is at
most a grid-dependent constant times the abstract Souza-Besov cost of `g`.
The theorem also records that this standard norm is finite.
-/
theorem exists_standardRepresentationNorm_le_const_mul_souzaBesovNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (g : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top))
        (f : α → ℂ) (hf : Integrable f G.grid.μ),
          f =ᵐ[G.grid.μ] ((g : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) →
            standardRepresentationNorm G F s hs p hp_top q f hf ≠ ∞ ∧
              standardRepresentationNorm G F s hs p hp_top q f hf ≤
                C * ENNReal.ofReal
                  (WeakGridSpace.BesovishSpace.Norm_Costpq
                    (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q g) := by
  classical
  rcases exists_standardRepresentationNorm_le_const_mul_haarL2RepresentationNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q) with
    ⟨Cst, hCst_fin, hst_le_haar⟩
  rcases HaarRepresentation.exists_haarL2RepresentationNorm_le_const_mul_meanOscillationNorm
      (G := G) (F := F) (s := s) (p := p) (hp_top := hp_top) (q := q) with
    ⟨Chaar, hChaar_fin, hhaar_le_osc⟩
  rcases MeanOscillation.exists_meanOscillationNorm_le_const_mul_souzaBesovNorm
      (G := G) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q) with
    ⟨Cosc, hCosc_fin, hosc_le_besov⟩
  refine ⟨Cst * Chaar * Cosc,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hCst_fin hChaar_fin) hCosc_fin, ?_⟩
  intro g f hf hfg
  let N : ℝ≥0∞ :=
    ENNReal.ofReal
      (WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q g)
  have hfLp : MemLp f p G.grid.μ := by
    exact (Lp.memLp (g : Lp ℂ p G.toWeakGridSpace.measure)).congr_norm
      hf.aestronglyMeasurable
      (hfg.mono fun x hx => by rw [hx])
  have hosc_le : MeanOscillation.meanOscillationNorm G s p q f ≤ Cosc * N := by
    simpa [N] using hosc_le_besov g f hfg
  have hosc_ne_top : MeanOscillation.meanOscillationNorm G s p q f ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hCosc_fin ENNReal.ofReal_ne_top) hosc_le
  have hhaar_le :
      HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≤
        Chaar * MeanOscillation.meanOscillationNorm G s p q f :=
    hhaar_le_osc f hf hfLp hosc_ne_top
  have hhaar_ne_top :
      HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hChaar_fin hosc_ne_top) hhaar_le
  rcases hst_le_haar f hf hhaar_ne_top with ⟨hst_fin, hst_le⟩
  refine ⟨hst_fin, ?_⟩
  calc
    standardRepresentationNorm G F s hs p hp_top q f hf
        ≤ Cst * HaarRepresentation.haarL2RepresentationNorm G F s p q f hf :=
      hst_le
    _ ≤ Cst * (Chaar * MeanOscillation.meanOscillationNorm G s p q f) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_right hhaar_le Cst
    _ ≤ Cst * (Chaar * (Cosc * N)) := by
      have hmul := mul_le_mul_right hosc_le Chaar
      have hmul' := mul_le_mul_right hmul Cst
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
    _ = (Cst * Chaar * Cosc) * N := by
      rw [← mul_assoc Chaar Cosc N]
      rw [← mul_assoc Cst (Chaar * Cosc) N]
      rw [← mul_assoc Cst Chaar Cosc]
    _ =
        (Cst * Chaar * Cosc) *
          ENNReal.ofReal
            (WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q g) := by
      rfl

end StandardAtomicRepresentation

end

end GoodGridSpace
