import BesovSpacesGoodGrid.GoodGrid.BesovSpace
import UnbalancedHaarWavelet.HaarWaveletsCoeffs
import UnbalancedHaarWavelet.HaarWavelets_def_Martingale
import UnconditionalSchauderBasis

/-!
# Haar representation norm on a good grid

This file records the concrete Haar-coefficient gauge used in the paper's
Haar representation section.  The underlying Haar wavelets are the concrete
non-normalized wavelets from `UnbalancedHaarWavelet`; this file exposes the
paper's normalized functions `φ_i = ψ_i / ‖ψ_i‖₂`, so the coefficient
`d_i^f = ∫ f φ_i dμ` is the usual orthonormal Haar coefficient.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory
open Filter

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace HaarRepresentation

abbrev GridOf (G : GoodGridSpace (α := α)) : UnbalancedHaarWavelet.Grid (α := α) :=
  G.grid.toGrid

/--
The support used for full Haar indices.

The father function is supported on the whole space.  A wavelet index uses its
ordinary branch support from `UnbalancedHaarWavelet`.
-/
def support (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G)) :
    F.Index → Set α
  | .alpha => Set.univ
  | .wavelet i => i.branchSupport (GridOf G) F.toHaarSystem

/--
The scalar that turns the concrete Haar function into an `L²`-normalized one.

The dependency's wavelet is denoted here by `ψ_i`; this is `1 / ‖ψ_i‖₂`, using
the square norm supplied by `UnbalancedHaarWavelet`.
-/
def l2NormalizationFactor (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G)) (i : F.Index) : ℝ :=
  (Real.sqrt (F.indexL2NormSq (GridOf G) i))⁻¹

/--
The `L²`-normalized full Haar function `φ_i`.

The function `F.function` is the concrete non-normalized Haar function from
`UnbalancedHaarWavelet` (with the dependency's father-function convention).
This definition rescales it by `1 / ‖ψ_i‖₂`.
-/
def L2normalizedHaar (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (i : F.Index) (x : α) : ℂ :=
  ((l2NormalizationFactor G F i : ℝ) : ℂ) *
    (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)

/--
Compatibility name for the normalized Haar function.

Older downstream files in this project call the same object
`normalizedFunction`; the paper-facing name in this file is
`L2normalizedHaar`.
-/
def normalizedFunction (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (i : F.Index) (x : α) : ℂ :=
  ((l2NormalizationFactor G F i : ℝ) : ℂ) *
    (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)

/--
Each normalized Haar function belongs to `L^β`.

This is the local, normalized version of
`UnbalancedHaarWavelet.FullHaarSystem.memLp_function`: the dependency proves
the concrete real Haar function is in `L^β`, and the present function differs
from its complexification by a scalar.
-/
theorem l2normalizedHaar_memLp (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)] (i : F.Index) :
    MemLp (L2normalizedHaar G F i) β G.grid.μ := by
  let hψ :
      MemLp
        (fun x : α =>
          (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ))
        β G.grid.μ :=
    (UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F β i).ofReal (K := ℂ)
  simpa [L2normalizedHaar, smul_eq_mul] using
    hψ.const_smul (((l2NormalizationFactor G F i : ℝ) : ℂ))

/--
The dependency's concrete real coefficient theorem gives the real-valued Haar
expansion directly.

This lemma is intentionally stated over the same grid wrapper as the rest of
this file.  It is the real part of the complex argument: after splitting a
complex-valued function into real and imaginary parts, this is the theorem that
identifies the abstract unconditional-basis coordinates with the integral
coefficients supplied by `UnbalancedHaarWavelet`.
-/
private theorem hasSum_real_coeff_smul_haar_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    [DecidableEq F.Index]
    (β : ℝ≥0∞) (hβ_one : 1 < β) (hβ_top : β < ∞)
    (g : α → ℝ) (hg : MemLp g β G.grid.μ) :
    letI : Fact (1 ≤ β) := ⟨le_of_lt hβ_one⟩
    HasSum
      (fun i : F.Index =>
        UnbalancedHaarWavelet.FullHaarSystem.coeff (GridOf G) F g i •
          (UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F β i).toLp
            (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i))
      (hg.toLp g) := by
  letI : Fact (1 ≤ β) := ⟨le_of_lt hβ_one⟩
  let q : ℝ≥0∞ := ENNReal.conjExponent β
  haveI : ENNReal.HolderConjugate β q := ENNReal.HolderConjugate.conjExponent Fact.out
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q β⟩
  rcases
    UnbalancedHaarWavelet.exists_fullHaarSystem_unconditionalSchauderBasisAbstractIndex_of_BurkholderSignBound_Real
      (GridOf G) F β hβ_one hβ_top with ⟨b, hb⟩
  have hsum_basis :
      HasSum
        (fun i : F.Index =>
          b.coeff i (hg.toLp g) •
            (UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F β i).toLp
              (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i))
        (hg.toLp g) := by
    simpa [hb, UnbalancedHaarWavelet.fullHaarLpFamily] using
      UnconditionalSchauderBasisAbstractIndex.hasSum_repr_apply b (hg.toLp g)
  exact
    UnbalancedHaarWavelet.FullHaarSystem.hasSum_coeff_of_hasSum_Lp
      (GridOf G) F β q g hg (fun i => b.coeff i (hg.toLp g)) hsum_basis

/-- The square norm denominator of every full Haar vector is positive. -/
private theorem indexL2NormSq_pos (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G)) (i : F.Index) :
    0 < F.indexL2NormSq (GridOf G) i := by
  have hnonneg :
      0 ≤ F.indexL2NormSq (GridOf G) i := by
    rw [← F.integral_function_mul_self_eq_indexL2NormSq (GridOf G) i]
    exact integral_nonneg fun x => mul_self_nonneg _
  exact lt_of_le_of_ne hnonneg (F.indexL2NormSq_ne_zero (GridOf G) i).symm

/-- The complex coefficient for the dependency's non-normalized Haar vectors. -/
private def complexHaarCoeff (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (f : α → ℂ) (i : F.Index) : ℂ :=
  (∫ x,
      f x *
        (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ) /
    (F.indexL2NormSq (GridOf G) i : ℂ)

/-- Products of two complexified full Haar functions are integrable. -/
private theorem integrable_complex_function_mul_function
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (i j : F.Index) :
    Integrable
      (fun x : α =>
        (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) *
          (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ))
      G.grid.μ := by
  simpa [map_mul] using
    (F.integrable_function_mul_function (GridOf G) i j).ofReal (𝕜 := ℂ)

/--
Finite coefficient recovery for complex coefficients and complexified
non-normalized Haar vectors.
-/
private theorem integral_finset_sum_mul_complex_function_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    [DecidableEq F.Index]
    (s : Finset F.Index) (a : F.Index → ℂ) (i : F.Index) :
    ∫ x,
      (∑ j ∈ s,
          a j *
            (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ)) *
        (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ =
      if i ∈ s then a i * (F.indexL2NormSq (GridOf G) i : ℂ) else 0 := by
  classical
  have hfun :
      (fun x =>
          (∑ j ∈ s,
              a j *
                (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ)) *
            (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ))
        =
      fun x =>
        ∑ j ∈ s,
          a j *
            ((UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ) *
              (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)) := by
    funext x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  rw [hfun]
  rw [MeasureTheory.integral_finsetSum]
  · calc
      ∑ j ∈ s,
          ∫ x,
            a j *
              ((UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ) *
                (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)) ∂G.grid.μ
          =
        ∑ j ∈ s,
          a j *
            (∫ x,
              (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ) *
                (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [MeasureTheory.integral_const_mul]
      _ =
        ∑ j ∈ s,
          a j * (if j = i then (F.indexL2NormSq (GridOf G) j : ℂ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hint :
                  (∫ x,
                    (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ) *
                      (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ)
                    =
                  ((∫ x,
                    UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x *
                      UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x ∂G.grid.μ :
                    ℝ) : ℂ) := by
                simpa [map_mul] using
                  (integral_ofReal
                    (𝕜 := ℂ)
                    (f := fun x =>
                      UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x *
                        UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x)
                    (μ := G.grid.μ))
              rw [hint]
              rw [F.integral_function_mul_function_eq (GridOf G) j i]
              by_cases hji : j = i <;> simp [hji]
      _ = if i ∈ s then a i * (F.indexL2NormSq (GridOf G) i : ℂ) else 0 := by
              by_cases hi : i ∈ s
              · rw [Finset.sum_eq_single i]
                · simp [hi]
                · intro j hj hji
                  simp [hji]
                · intro hi_not
                  exact (hi_not hi).elim
              · rw [Finset.sum_eq_zero]
                · simp [hi]
                · intro j hj
                  have hji : j ≠ i := by
                    intro h
                    exact hi (h ▸ hj)
                  simp [hji]
  · intro j hj
    exact (integrable_complex_function_mul_function G F j i).const_mul (a j)

/-- Coefficient identification from convergence of complex integral pairings. -/
private theorem complexHaarCoeff_eq_of_tendsto_integrals
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    [DecidableEq F.Index]
    (f : α → ℂ) (a : F.Index → ℂ)
    (hlim : ∀ i : F.Index,
      Tendsto
        (fun s : Finset F.Index =>
          ∫ x,
            (∑ j ∈ s,
                a j *
                  (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ)) *
              (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ)
        atTop
        (𝓝 (∫ x,
          f x *
            (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ))) :
    ∀ i : F.Index, a i = complexHaarCoeff G F f i := by
  classical
  intro i
  have h_event_mem : ∀ᶠ s : Finset F.Index in atTop, i ∈ s := by
    exact eventually_atTop.2 ⟨{i}, by
      intro s hs
      exact hs (by simp)⟩
  have h_event_integral :
      (fun s : Finset F.Index =>
          ∫ x,
            (∑ j ∈ s,
                a j *
                  (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ)) *
              (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ)
        =ᶠ[atTop]
      (fun _ : Finset F.Index => a i * (F.indexL2NormSq (GridOf G) i : ℂ)) := by
    filter_upwards [h_event_mem] with s his
    simpa [his] using integral_finset_sum_mul_complex_function_eq G F s a i
  have hlim_coeff :
      Tendsto
        (fun s : Finset F.Index =>
          ∫ x,
            (∑ j ∈ s,
                a j *
                  (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ)) *
              (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ)
        atTop
        (𝓝 (a i * (F.indexL2NormSq (GridOf G) i : ℂ))) := by
    exact (tendsto_const_nhds.congr' h_event_integral.symm)
  have hpair :
      a i * (F.indexL2NormSq (GridOf G) i : ℂ) =
        ∫ x,
          f x *
            (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ :=
    tendsto_nhds_unique hlim_coeff (hlim i)
  have hden : (F.indexL2NormSq (GridOf G) i : ℂ) ≠ 0 := by
    exact_mod_cast F.indexL2NormSq_ne_zero (GridOf G) i
  calc
    a i = (a i * (F.indexL2NormSq (GridOf G) i : ℂ)) /
        (F.indexL2NormSq (GridOf G) i : ℂ) := by
      field_simp [hden]
    _ =
        (∫ x,
          f x *
            (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ) /
          (F.indexL2NormSq (GridOf G) i : ℂ) := by
      rw [hpair]
    _ = complexHaarCoeff G F f i := rfl

/-- The complex `Lp` pairing functional against the `i`th full Haar function. -/
private def complexLpPairingFunctional
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (i : F.Index) :
    UnbalancedHaarWavelet.FullHaarLpSpaceComplex (GridOf G) p →L[ℂ] ℂ :=
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing G.grid.μ p q).flip
    (((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F q i).ofReal
      (K := ℂ)).toLp
        (fun x => (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)))

/-- On representatives, the complex `Lp` pairing is the concrete integral. -/
private theorem complexLpPairingFunctional_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (g : α → ℂ) (hg : MemLp g p G.grid.μ) (i : F.Index) :
    complexLpPairingFunctional G F p q i (hg.toLp g) =
      ∫ x,
        g x *
          (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ := by
  let htest : MemLp
      (fun x : α => (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ))
      q G.grid.μ :=
    (UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F q i).ofReal
      (K := ℂ)
  rw [complexLpPairingFunctional]
  change (ContinuousLinearMap.mul ℂ ℂ).lpPairing G.grid.μ p q (hg.toLp g)
      (htest.toLp
        (fun x => (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ))) =
    ∫ x,
      g x *
        (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hg, MemLp.coeFn_toLp htest] with x hxg hxi
  simp [hxg, hxi]

/--
Any complex full-Haar `Lp` expansion has the concrete complex coefficient
formula.
-/
private theorem complexHaarCoeff_eq_of_hasSum_Lp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    [DecidableEq F.Index]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (f : α → ℂ) (hf : MemLp f p G.grid.μ)
    (a : F.Index → ℂ)
    (hsum :
      HasSum
        (fun i : F.Index =>
          a i •
            ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F p i).ofReal
              (K := ℂ)).toLp
                (fun x =>
                  (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)))
        (hf.toLp f)) :
    ∀ i : F.Index, a i = complexHaarCoeff G F f i := by
  classical
  refine complexHaarCoeff_eq_of_tendsto_integrals G F f a ?_
  intro i
  let hhaar : ∀ i : F.Index, MemLp
      (fun x : α => (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ))
      p G.grid.μ :=
    fun i =>
      (UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F p i).ofReal
        (K := ℂ)
  let L :
      UnbalancedHaarWavelet.FullHaarLpSpaceComplex (GridOf G) p →L[ℂ] ℂ :=
    complexLpPairingFunctional G F p q i
  have hsumL :
      HasSum
        (fun j : F.Index =>
          L (a j • (hhaar j).toLp
            (fun x =>
              (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ))))
        (L (hf.toLp f)) :=
    hsum.mapL L
  have htarget :
      L (hf.toLp f) =
        ∫ x,
          f x *
            (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ := by
    exact complexLpPairingFunctional_toLp G F p q f hf i
  have hpartial :
      (fun s : Finset F.Index =>
          ∑ j ∈ s,
            L (a j • (hhaar j).toLp
              (fun x =>
                (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ))))
        =
      (fun s : Finset F.Index =>
          ∫ x,
            (∑ j ∈ s,
                a j *
                  (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ)) *
              (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ) := by
    funext s
    calc
      ∑ j ∈ s,
          L (a j • (hhaar j).toLp
            (fun x =>
              (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ)))
          =
        L (∑ j ∈ s,
          a j • (hhaar j).toLp
            (fun x =>
              (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ))) := by
              rw [map_sum]
      _ =
        L (((MeasureTheory.memLp_finsetSum s
              (fun j _ => (hhaar j).const_smul (a j)))).toLp
              (fun x =>
                ∑ j ∈ s,
                  a j *
                    (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ))) := by
              rw [UnbalancedHaarWavelet.toLp_finsetSum_const_smul_complex p s
                (fun j x =>
                  (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ))
                hhaar a]
      _ =
        ∫ x,
          (∑ j ∈ s,
              a j *
                (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ)) *
            (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ) ∂G.grid.μ := by
              exact complexLpPairingFunctional_toLp G F p q
                (fun x =>
                  ∑ j ∈ s,
                    a j *
                      (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F j x : ℂ))
                (MeasureTheory.memLp_finsetSum s
                  (fun j _ => (hhaar j).const_smul (a j))) i
  rw [← htarget]
  rw [← hpartial]
  exact hsumL

/--
Consequently, any complex full-Haar `Lp` representation is the one with the
concrete complex coefficient formula.
-/
private theorem hasSum_complexHaarCoeff_of_hasSum_Lp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    [DecidableEq F.Index]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (f : α → ℂ) (hf : MemLp f p G.grid.μ)
    (a : F.Index → ℂ)
    (hsum :
      HasSum
        (fun i : F.Index =>
          a i •
            ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F p i).ofReal
              (K := ℂ)).toLp
                (fun x =>
                  (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)))
        (hf.toLp f)) :
    HasSum
      (fun i : F.Index =>
        complexHaarCoeff G F f i •
          ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F p i).ofReal
            (K := ℂ)).toLp
              (fun x =>
                (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)))
      (hf.toLp f) := by
  let hcoeff := complexHaarCoeff_eq_of_hasSum_Lp G F p q f hf a hsum
  have hterms :
      (fun i : F.Index =>
        a i •
          ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F p i).ofReal
            (K := ℂ)).toLp
              (fun x =>
                (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)))
        =
      (fun i : F.Index =>
        complexHaarCoeff G F f i •
          ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F p i).ofReal
            (K := ℂ)).toLp
              (fun x =>
                (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ))) := by
    funext i
    rw [hcoeff i]
  simpa [hterms] using hsum

/-- The square of the `L²` normalization factor is the inverse square norm. -/
private theorem l2NormalizationFactor_mul_self
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G)) (i : F.Index) :
    (((l2NormalizationFactor G F i : ℝ) : ℂ) *
        ((l2NormalizationFactor G F i : ℝ) : ℂ)) =
      ((F.indexL2NormSq (GridOf G) i : ℂ))⁻¹ := by
  let N : ℝ := F.indexL2NormSq (GridOf G) i
  have hNpos : 0 < N := by
    simpa [N] using indexL2NormSq_pos G F i
  have hsqrt_ne : Real.sqrt N ≠ 0 := Real.sqrt_ne_zero'.mpr hNpos
  have hsqrt_sq : Real.sqrt N * Real.sqrt N = N := by
    simpa [pow_two] using Real.sq_sqrt hNpos.le
  have hreal : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = N⁻¹ := by
    rw [← mul_inv_rev, hsqrt_sq]
  calc
    (((l2NormalizationFactor G F i : ℝ) : ℂ) *
        ((l2NormalizationFactor G F i : ℝ) : ℂ))
        = (((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ : ℝ) : ℂ) := by
            simp [l2NormalizationFactor, N]
    _ = ((N⁻¹ : ℝ) : ℂ) := by
            rw [hreal]
    _ = ((N : ℂ))⁻¹ := by
            norm_num

/--
The Haar coefficient against the normalized Haar function, with the
integrability hypothesis explicit in the API.

This is the manuscript's convention `d_i^f = ∫ f φ_i dm`, as a complex integral.
Since `φ_i` has `L²` norm `1`, no extra division by `‖ψ_i‖₂²` appears.
-/
def Coeff (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (f : α → ℂ) (_hf : Integrable f G.grid.μ) (i : F.Index) : ℂ :=
  ∫ x, f x * L2normalizedHaar G F i x ∂G.grid.μ

/--
One normalized coefficient term equals the corresponding non-normalized complex
Haar coefficient term.
-/
private theorem coeff_smul_l2normalizedHaar_toLp_eq_complexHaarCoeff_smul_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (β : ℝ≥0∞) [Fact (1 ≤ β)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (i : F.Index) :
    Coeff G F f hf i •
          (l2normalizedHaar_memLp G F β i).toLp (L2normalizedHaar G F i)
      =
        complexHaarCoeff G F f i •
          ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F β i).ofReal
            (K := ℂ)).toLp
              (fun x =>
                (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)) := by
  let ψ : α → ℂ :=
    fun x => (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)
  let n : ℂ := ((l2NormalizationFactor G F i : ℝ) : ℂ)
  let A : ℂ := ∫ x, f x * ψ x ∂G.grid.μ
  have hCoeff : Coeff G F f hf i = n * A := by
    calc
      Coeff G F f hf i
          = ∫ x, n * (f x * ψ x) ∂G.grid.μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun x => by
                simp [L2normalizedHaar, ψ, n]
                ring
      _ = n * A := by
              rw [MeasureTheory.integral_const_mul]
  have hcomplexCoeff : complexHaarCoeff G F f i = A / (F.indexL2NormSq (GridOf G) i : ℂ) := by
    rfl
  have hscalar :
      Coeff G F f hf i * n = complexHaarCoeff G F f i := by
    rw [hCoeff, hcomplexCoeff]
    calc
      (n * A) * n = A * (n * n) := by ring
      _ = A * ((F.indexL2NormSq (GridOf G) i : ℂ))⁻¹ := by
            rw [l2NormalizationFactor_mul_self G F i]
      _ = A / (F.indexL2NormSq (GridOf G) i : ℂ) := by
            rw [div_eq_mul_inv]
  rw [← MeasureTheory.MemLp.toLp_const_smul]
  rw [← MeasureTheory.MemLp.toLp_const_smul]
  apply MeasureTheory.MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun x => by
    change
      Coeff G F f hf i * L2normalizedHaar G F i x =
        complexHaarCoeff G F f i * ψ x
    calc
      Coeff G F f hf i * L2normalizedHaar G F i x
          = Coeff G F f hf i * (n * ψ x) := by
              simp [L2normalizedHaar, ψ, n]
      _ = (Coeff G F f hf i * n) * ψ x := by
              ring
      _ = complexHaarCoeff G F f i * ψ x := by
              rw [hscalar]

/--
The full `L²`-normalized Haar expansion converges unconditionally in `L^β`.

For `1 < β < ∞`, every `f ∈ L^β` is the unconditional sum of its normalized
Haar coefficients times the corresponding normalized Haar functions.  The
coefficient used here is the paper's `d_i^f = ∫ f φ_i dμ`, implemented as
`Coeff`, and the convergence is stated as a `HasSum` in `Lp`.

The proof is a thin wrapper around the unconditional Haar-basis theorem in
`UnbalancedHaarWavelet`; the remaining bridge is the standard identification
of that basis's coordinate functional with the concrete normalized integral
coefficient.
-/
theorem hasSum_coeff_smul_l2normalizedHaar_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    [DecidableEq F.Index]
    (β : ℝ≥0∞) (hβ_one : 1 < β) (hβ_top : β < ∞)
    (f : α → ℂ) (hf : MemLp f β G.grid.μ) :
    letI : Fact (1 ≤ β) := ⟨le_of_lt hβ_one⟩
    HasSum
      (fun i : F.Index =>
        Coeff G F f
            (by
              letI : IsFiniteMeasure G.grid.μ := (GridOf G).isFinite
              exact hf.integrable (le_of_lt hβ_one))
            i •
          (l2normalizedHaar_memLp G F β i).toLp (L2normalizedHaar G F i))
      (hf.toLp f) := by
  letI : Fact (1 ≤ β) := ⟨le_of_lt hβ_one⟩
  let q : ℝ≥0∞ := ENNReal.conjExponent β
  haveI : ENNReal.HolderConjugate β q := ENNReal.HolderConjugate.conjExponent Fact.out
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q β⟩
  rcases
    UnbalancedHaarWavelet.exists_fullHaarSystem_unconditionalSchauderBasis_of_BurkholderSignBound_Complex
      (GridOf G) F β hβ_one hβ_top with ⟨e, b, hb⟩
  have hsum_nat :
      HasSum
        (fun n : ℕ =>
          b.coeff n (hf.toLp f) • b.basis n)
        (hf.toLp f) :=
    b.unconditional (hf.toLp f)
  have hsum_reindexed :
      HasSum
        (fun i : F.Index =>
          b.coeff (e.symm i) (hf.toLp f) • b.basis (e.symm i))
        (hf.toLp f) := by
    simpa [Function.comp_def] using (e.symm.hasSum_iff).2 hsum_nat
  have hb_apply :
      ∀ i : F.Index,
        b.basis (e.symm i) =
          ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F β i).ofReal
            (K := ℂ)).toLp
              (fun x =>
                (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)) := by
    intro i
    have h := congrFun hb (e.symm i)
    simpa using h
  have hsum_unnormalized :
      HasSum
        (fun i : F.Index =>
          b.coeff (e.symm i) (hf.toLp f) •
            ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F β i).ofReal
              (K := ℂ)).toLp
                (fun x =>
                  (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)))
        (hf.toLp f) := by
    have hterms :
        (fun i : F.Index =>
          b.coeff (e.symm i) (hf.toLp f) • b.basis (e.symm i))
          =
        (fun i : F.Index =>
          b.coeff (e.symm i) (hf.toLp f) •
            ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F β i).ofReal
              (K := ℂ)).toLp
                (fun x =>
                  (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ))) := by
      funext i
      rw [hb_apply i]
    simpa [hterms] using hsum_reindexed
  have hsum_complex_coeff :
      HasSum
        (fun i : F.Index =>
          complexHaarCoeff G F f i •
            ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F β i).ofReal
              (K := ℂ)).toLp
                (fun x =>
                  (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)))
        (hf.toLp f) :=
    hasSum_complexHaarCoeff_of_hasSum_Lp G F β q f hf
      (fun i => b.coeff (e.symm i) (hf.toLp f)) hsum_unnormalized
  have hterm :
      (fun i : F.Index =>
        Coeff G F f
            (by
              letI : IsFiniteMeasure G.grid.μ := (GridOf G).isFinite
              exact hf.integrable (le_of_lt hβ_one))
            i •
          (l2normalizedHaar_memLp G F β i).toLp (L2normalizedHaar G F i))
        =
      (fun i : F.Index =>
        complexHaarCoeff G F f i •
          ((UnbalancedHaarWavelet.FullHaarSystem.memLp_function (GridOf G) F β i).ofReal
            (K := ℂ)).toLp
              (fun x =>
                (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ))) := by
    funext i
    exact coeff_smul_l2normalizedHaar_toLp_eq_complexHaarCoeff_smul_toLp G F β f
      (by
        letI : IsFiniteMeasure G.grid.μ := (GridOf G).isFinite
        exact hf.integrable (le_of_lt hβ_one))
      i
  simpa [hterm] using hsum_complex_coeff

/--
Wavelet indices whose parent cell is `Q`.

This is the formal version of the finite family `H_Q` in the paper.
-/
def indicesInCell (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (Q : GoodGridCell G) :
    Finset {b : Finset (Set α) × Finset (Set α) //
      b ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches} :=
  (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches.attach

/-- Turn a branch of the binary refinement tree over `Q` into a global Haar index. -/
def indexOfCellBranch (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    F.toHaarSystem.Index where
  level := Q.level
  cell := Q.cell
  hcell := Q.mem
  branch := b

/--
The `p`-power contribution of Haar coefficients over one cell `Q`.

This is the inner finite sum `∑_{S ∈ H_Q} |d_S^f|^p`, written using the
normalized Haar coefficient convention fixed above.
-/
def cellCoeffPower (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) (Q : GoodGridCell G) :
    ℝ≥0∞ :=
  ∑ b ∈ indicesInCell G F Q,
    ENNReal.ofReal (‖Coeff G F f hf (.wavelet (indexOfCellBranch G F Q b))‖ ^ p.toReal)

/--
The level-`k` Haar block appearing in `N_haar`.

It is
`∑_{Q ∈ P^k} μ(Q)^(1 - s p - p/2) ∑_{S ∈ H_Q} |d_S^f|^p`.
-/
def levelHaarBlock (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) :
    ℝ≥0∞ :=
  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    ENNReal.ofReal ((G.grid.μ Q.1).toReal ^ (1 - s * p.toReal - p.toReal / 2)) *
      cellCoeffPower G F p f hf
        { level := k
          cell := Q.1
          mem := Q.2 }

/--
The father-function term in `N_haar`.

This is `μ(I)^(1/p - s - 1/2) |d_I^f|`, with `I = univ`.
-/
def fatherTerm (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((G.grid.μ Set.univ).toReal ^ (1 / p.toReal - s - 1 / 2) *
      ‖Coeff G F f hf .alpha‖)

/--
The Haar representation gauge from the paper, using `L²`-normalized Haar
functions.
-/
def haarL2RepresentationNorm (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (s : ℝ) (p q : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) : ℝ≥0∞ :=
  fatherTerm G F s p f hf +
    if q = ∞ then
      sSup (Set.range fun k => (levelHaarBlock G F s p f hf k) ^ (1 / p.toReal))
    else
      (∑' k, (levelHaarBlock G F s p f hf k) ^ (q.toReal / p.toReal)) ^
        (1 / q.toReal)

end HaarRepresentation

end

end GoodGridSpace
