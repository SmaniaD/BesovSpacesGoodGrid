import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.FiniteStandardNormimpliesBesov
import BesovSpacesGoodGrid.GoodGrid.BesovSpace
import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.standardNormleqHaarRepresenstionNorm

/-!
# Finite Haar norm forces an `L^p` Haar expansion

This file packages the endpoint consequence for the `L²`-normalized Haar
coefficient gauge.  The proof first transfers finiteness of the Haar gauge to
the standard atomic gauge, then uses the standard endpoint theorem to obtain
`L^p` membership.  Once `f` is known to be in `L^p`, the existing Haar basis
theorem gives the Haar expansion itself.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace StandardAtomicRepresentation

/--
Finite Haar representation norm forces membership in `L^p` and identifies the
normalized Haar expansion with the original function.

For `p > 1`, this is the existing unconditional Haar expansion theorem after
the finite-norm comparison.  At the endpoint `p = 1`, the standard atomic
representation first gives a Souza-Besov element, hence an `L^β` representative
for some `β > 1`; the Haar expansion in `L^β` is then included back into `L^1`.
-/
theorem finite_haarL2RepresentationNorm_implies_memLp_and_hasSum
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (hN : HaarRepresentation.haarL2RepresentationNorm G F s p q f hf ≠ ∞) :
    ∃ hfLp : MemLp f p G.grid.μ,
      HasSum
        (fun i : F.Index =>
          HaarRepresentation.Coeff G F f hf i •
            (HaarRepresentation.l2normalizedHaar_memLp G F p i).toLp
              (HaarRepresentation.L2normalizedHaar G F i))
        (hfLp.toLp f) := by
  classical
  rcases
    exists_standardRepresentationNorm_le_const_mul_haarL2RepresentationNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q) with
    ⟨C, hC_fin, hstandard_le⟩
  have hstandard_fin :
      standardRepresentationNorm G F s hs p hp_top q f hf ≠ ∞ :=
    (hstandard_le f hf hN).1
  rcases
    finite_standardRepresentationNorm_implies_memLp_and_hasSum
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q)
      f hf hstandard_fin with
    ⟨hfLp, hstandard_sum⟩
  refine ⟨hfLp, ?_⟩
  by_cases hp_one : 1 < p
  · have hhaar :
        HasSum
          (fun i : F.Index =>
            HaarRepresentation.Coeff G F f
                (by
                  letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
                  exact hfLp.integrable (le_of_lt hp_one))
                i •
              (HaarRepresentation.l2normalizedHaar_memLp G F p i).toLp
                (HaarRepresentation.L2normalizedHaar G F i))
          (hfLp.toLp f) :=
      HaarRepresentation.hasSum_coeff_smul_l2normalizedHaar_toLp G F p hp_one hp_top f hfLp
    refine hhaar.congr_fun ?_
    intro i
    rfl
  · have hp_le_one : p ≤ 1 := le_of_not_gt hp_one
    have hp_eq_one : p = 1 := le_antisymm hp_le_one (Fact.out : (1 : ℝ≥0∞) ≤ p)
    subst p
    have hfin :
        WeakGridSpace.AbstractFinitePQCost
          (A := souzaAtomFamily G s (1 : ℝ≥0∞) hs Fact.out (ne_of_lt hp_top))
          (q := q)
          (canonicalStandardBlockSeq G F s hs (1 : ℝ≥0∞) hp_top f hf) :=
      abstractFinitePQCost_canonicalStandardBlockSeq_of_standardRepresentationNorm_ne_top
        (G := G) (F := F) (s := s) (hs := hs) (p := (1 : ℝ≥0∞))
        (hp_top := hp_top) (q := q) f hf hstandard_fin
    let R :
        WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s (1 : ℝ≥0∞) hs Fact.out (ne_of_lt hp_top))
          (hfLp.toLp f) :=
      { block := canonicalStandardBlockSeq G F s hs (1 : ℝ≥0∞) hp_top f hf
        hasSum := hstandard_sum }
    have hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R := by
      simpa [R, WeakGridSpace.LpGridRepresentation.FinitePQCost,
        WeakGridSpace.AbstractFinitePQCost,
        WeakGridSpace.blockLvlCoeff_eq_levelCoeffPower] using hfin
    have hmem :
        (hfLp.toLp f) ∈
          SouzaBesovSpace G s (1 : ℝ≥0∞) q hs Fact.out (ne_of_lt hp_top) := by
      change
        WeakGridSpace.MemBesovishCoeffCost
          (souzaAtomFamily G s (1 : ℝ≥0∞) hs Fact.out (ne_of_lt hp_top))
          q (hfLp.toLp f)
      exact ⟨R, by simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost] using hRfin⟩
    let g :
        SouzaBesovSpace G s (1 : ℝ≥0∞) q hs Fact.out (ne_of_lt hp_top) :=
      ⟨hfLp.toLp f, hmem⟩
    rcases
      souzaBesovSpace_exists_Lp_one_add_epsilon
        (G := G) (s := s) (p := (1 : ℝ≥0∞)) (q := q)
        (hs := hs) (hp := Fact.out) (hp_top := ne_of_lt hp_top) g with
      ⟨ε, hε, hβ, hβ_ae⟩
    let β : ℝ≥0∞ := ENNReal.ofReal (1 + ε)
    have hβ_one : 1 < β := by
      change 1 < ENNReal.ofReal (1 + ε)
      exact ENNReal.one_lt_ofReal.mpr (by linarith)
    have hβ_top : β < ∞ := by
      simp [β]
    letI : Fact (1 ≤ β) := ⟨le_of_lt hβ_one⟩
    have hβ_ae_f : (hβ : α → ℂ) =ᵐ[G.grid.μ] f := by
      exact hβ_ae.trans (MemLp.coeFn_toLp hfLp)
    have hfβ : MemLp f β G.grid.μ := by
      refine (Lp.memLp hβ).congr_norm hf.aestronglyMeasurable ?_
      exact hβ_ae_f.mono fun x hx => by rw [← hx]
    have hhaarβ :
        HasSum
          (fun i : F.Index =>
            HaarRepresentation.Coeff G F f
                (by
                  letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
                  exact hfβ.integrable (le_of_lt hβ_one))
                i •
              (HaarRepresentation.l2normalizedHaar_memLp G F β i).toLp
                (HaarRepresentation.L2normalizedHaar G F i))
          (hfβ.toLp f) :=
      HaarRepresentation.hasSum_coeff_smul_l2normalizedHaar_toLp G F β hβ_one hβ_top f hfβ
    let I :=
      WeakGridSpace.LpGridRepresentation.lpInclusion
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞)) (t := β)
        (ne_of_lt hp_top) (ne_of_lt hβ_top) (le_of_lt hβ_one)
    have hI_hasSum :
        HasSum
          (fun i : F.Index =>
            I
              (HaarRepresentation.Coeff G F f
                  (by
                    letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
                    exact hfβ.integrable (le_of_lt hβ_one))
                  i •
                (HaarRepresentation.l2normalizedHaar_memLp G F β i).toLp
                  (HaarRepresentation.L2normalizedHaar G F i)))
          (I (hfβ.toLp f)) :=
      hhaarβ.mapL I
    have htarget : I (hfβ.toLp f) = hfLp.toLp f := by
      apply Lp.ext
      exact
        (WeakGridSpace.LpGridRepresentation.coeFn_lpInclusion
          (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞)) (t := β)
          (ne_of_lt hp_top) (ne_of_lt hβ_top) (le_of_lt hβ_one)
          (hfβ.toLp f)).trans
          ((MemLp.coeFn_toLp hfβ).trans (MemLp.coeFn_toLp hfLp).symm)
    have hterms :
        ∀ i : F.Index,
          I
            (HaarRepresentation.Coeff G F f
                (by
                  letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
                  exact hfβ.integrable (le_of_lt hβ_one))
                i •
              (HaarRepresentation.l2normalizedHaar_memLp G F β i).toLp
                (HaarRepresentation.L2normalizedHaar G F i)) =
            HaarRepresentation.Coeff G F f hf i •
              (HaarRepresentation.l2normalizedHaar_memLp G F (1 : ℝ≥0∞) i).toLp
                (HaarRepresentation.L2normalizedHaar G F i) := by
      intro i
      apply Lp.ext
      have hI_ae :=
        WeakGridSpace.LpGridRepresentation.coeFn_lpInclusion
          (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞)) (t := β)
          (ne_of_lt hp_top) (ne_of_lt hβ_top) (le_of_lt hβ_one)
          (HaarRepresentation.Coeff G F f
              (by
                letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
                exact hfβ.integrable (le_of_lt hβ_one))
              i •
            (HaarRepresentation.l2normalizedHaar_memLp G F β i).toLp
              (HaarRepresentation.L2normalizedHaar G F i))
      have hβ_term :
          ((HaarRepresentation.Coeff G F f
              (by
                letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
                exact hfβ.integrable (le_of_lt hβ_one))
              i •
            (HaarRepresentation.l2normalizedHaar_memLp G F β i).toLp
              (HaarRepresentation.L2normalizedHaar G F i) :
              Lp ℂ β G.grid.μ) : α → ℂ)
            =ᵐ[G.grid.μ]
          fun x =>
            HaarRepresentation.Coeff G F f hf i *
              HaarRepresentation.L2normalizedHaar G F i x := by
        have hcoeff :
            HaarRepresentation.Coeff G F f
                (by
                  letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
                  exact hfβ.integrable (le_of_lt hβ_one))
                i =
              HaarRepresentation.Coeff G F f hf i := rfl
        simpa [hcoeff] using
          (Lp.coeFn_smul
            (HaarRepresentation.Coeff G F f
              (by
                letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
                exact hfβ.integrable (le_of_lt hβ_one))
              i)
            ((HaarRepresentation.l2normalizedHaar_memLp G F β i).toLp
              (HaarRepresentation.L2normalizedHaar G F i))).trans
            ((MemLp.coeFn_toLp
              (HaarRepresentation.l2normalizedHaar_memLp G F β i)).fun_const_smul
                (HaarRepresentation.Coeff G F f
                  (by
                    letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
                    exact hfβ.integrable (le_of_lt hβ_one))
                  i))
      have hp_term :
          ((HaarRepresentation.Coeff G F f hf i •
            (HaarRepresentation.l2normalizedHaar_memLp G F (1 : ℝ≥0∞) i).toLp
              (HaarRepresentation.L2normalizedHaar G F i) :
              Lp ℂ (1 : ℝ≥0∞) G.grid.μ) : α → ℂ)
            =ᵐ[G.grid.μ]
          fun x =>
            HaarRepresentation.Coeff G F f hf i *
              HaarRepresentation.L2normalizedHaar G F i x := by
        exact
          (Lp.coeFn_smul (HaarRepresentation.Coeff G F f hf i)
            ((HaarRepresentation.l2normalizedHaar_memLp G F (1 : ℝ≥0∞) i).toLp
              (HaarRepresentation.L2normalizedHaar G F i))).trans
            ((MemLp.coeFn_toLp
              (HaarRepresentation.l2normalizedHaar_memLp G F (1 : ℝ≥0∞) i)).fun_const_smul
                (HaarRepresentation.Coeff G F f hf i))
      simpa [GoodGridSpace.toWeakGridSpace] using
        hI_ae.trans (hβ_term.trans hp_term.symm)
    rw [htarget] at hI_hasSum
    exact hI_hasSum.congr_fun fun i => (hterms i).symm

end StandardAtomicRepresentation

end

end GoodGridSpace
