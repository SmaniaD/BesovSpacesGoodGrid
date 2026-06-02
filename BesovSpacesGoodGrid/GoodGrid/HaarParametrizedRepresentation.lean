import BesovSpacesGoodGrid.GoodGrid.HaarRepresentationNorm

/-!
# Parametrized Haar representation on a good grid

This file keeps the existing `L²`-normalized Haar representation intact and
adds a second representation whose atoms carry the Besov parameter directly.

For a wavelet, the raw Haar function is multiplied by
`μ(support ψ)^(s + 1 - 1 / p)`.  The father function uses the corresponding
characteristic-function scaling `μ(univ)^(s - 1 / p)`.  The coefficients are
chosen so that every term agrees with the already proved `L²` Haar expansion.

The coefficient gauge here is deliberately unweighted: first take the `p` cost
of coefficients inside each level, and then take the `q` cost over the levels.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace HaarParametrizedRepresentation

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

private theorem l2NormalizationFactor_pos
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (i : F.Index) :
    0 < HaarRepresentation.l2NormalizationFactor G F i := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (indexL2NormSq_pos G F i))

/--
The support measure attached to a full Haar index.

For a wavelet, this is the measure of the support of that Haar wavelet.  For
the father index, it is the measure of the whole first cell, namely `univ`.
-/
def supportMeasure (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G)) :
    F.Index → ℝ≥0∞
  | i => G.grid.μ (HaarRepresentation.support G F i)

/--
The raw parametrizing factor for the new Haar atoms.

Wavelets are multiplied by `μ(support ψ)^(s + 1 - 1 / p)`.  The father
function is multiplied by `μ(univ)^(s - 1 / p)`.
-/
def rawScale (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (i : F.Index) : ℝ :=
  match i with
  | .alpha => (supportMeasure G F .alpha).toReal ^ (s - 1 / p.toReal)
  | .wavelet j => (supportMeasure G F (.wavelet j)).toReal ^ (s + 1 - 1 / p.toReal)

private theorem rawScale_pos (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (i : F.Index) :
    0 < rawScale G F s p i := by
  cases i with
  | alpha =>
      have hμ_pos : 0 < supportMeasure G F .alpha := by
        exact
          G.grid.positive_measure 0 Set.univ
            (by simp [G.grid.grid.first_partition_eq_univ])
      have hμ_ne_top : supportMeasure G F .alpha ≠ ∞ := by
        letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
        exact MeasureTheory.measure_ne_top G.grid.μ Set.univ
      have hμ_toReal_pos : 0 < (supportMeasure G F .alpha).toReal :=
        ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
      exact Real.rpow_pos_of_pos hμ_toReal_pos _
  | wavelet j =>
      have hμ_pos : 0 < supportMeasure G F (.wavelet j) := by
        simpa [supportMeasure, HaarRepresentation.support] using
          UnbalancedHaarWavelet.HaarSystem.Index.measure_branchSupport_pos
            (HaarRepresentation.GridOf G) F.toHaarSystem j
      have hμ_ne_top : supportMeasure G F (.wavelet j) ≠ ∞ := by
        letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
        exact MeasureTheory.measure_ne_top G.grid.μ (HaarRepresentation.support G F (.wavelet j))
      have hμ_toReal_pos : 0 < (supportMeasure G F (.wavelet j)).toReal :=
        ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
      exact Real.rpow_pos_of_pos hμ_toReal_pos _

private theorem rawScale_ne_zero (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (i : F.Index) :
    rawScale G F s p i ≠ 0 :=
  (rawScale_pos G F s p i).ne'

/--
The scalar relating the parametrized atom to the existing `L²`-normalized Haar.

The parametrized atom is the raw Haar function times `rawScale`; since
`L2normalizedHaar` is the raw Haar function times `l2NormalizationFactor`, this
is the factor by which one multiplies the `L²` atom.
-/
def l2Scale (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (i : F.Index) : ℝ :=
  rawScale G F s p i / HaarRepresentation.l2NormalizationFactor G F i

private theorem l2Scale_ne_zero (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (i : F.Index) :
    l2Scale G F s p i ≠ 0 := by
  exact div_ne_zero (rawScale_ne_zero G F s p i)
    (l2NormalizationFactor_pos G F i).ne'

/--
The parametrized Haar function.

For wavelet indices this is exactly the raw Haar function multiplied by
`μ(support ψ)^(s + 1 - 1 / p)`; for the father index it is the raw father
function multiplied by `μ(univ)^(s - 1 / p)`.
-/
def parametrizedHaar (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (i : F.Index) (x : α) : ℂ :=
  ((rawScale G F s p i : ℝ) : ℂ) *
    (UnbalancedHaarWavelet.FullHaarSystem.function (HaarRepresentation.GridOf G) F i x : ℂ)

/-- Each parametrized Haar function belongs to `L^β`. -/
theorem parametrizedHaar_memLp (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p β : ℝ≥0∞) [Fact (1 ≤ β)] (i : F.Index) :
    MemLp (parametrizedHaar G F s p i) β G.grid.μ := by
  let hψ :
      MemLp
        (fun x : α =>
          (UnbalancedHaarWavelet.FullHaarSystem.function (HaarRepresentation.GridOf G) F i x :
            ℂ))
        β G.grid.μ :=
    (UnbalancedHaarWavelet.FullHaarSystem.memLp_function
      (HaarRepresentation.GridOf G) F β i).ofReal (K := ℂ)
  simpa [parametrizedHaar, smul_eq_mul] using
    hψ.const_smul (((rawScale G F s p i : ℝ) : ℂ))

/--
The parametrized Haar vector in `L^β`, expressed through the already available
`L²`-normalized Haar vector.
-/
def parametrizedHaarToLp (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p β : ℝ≥0∞) [Fact (1 ≤ β)] (i : F.Index) :
    Lp ℂ β G.grid.μ :=
  (((l2Scale G F s p i : ℝ) : ℂ)) •
    (HaarRepresentation.l2normalizedHaar_memLp G F β i).toLp
      (HaarRepresentation.L2normalizedHaar G F i)

/--
The coefficient of `f` in the parametrized Haar representation.

It is the old `L²` Haar coefficient divided by the scalar that turns the
`L²` atom into the new parametrized atom.  With this definition, every
coefficient times atom is definitionally the same `Lp` vector as before, up to
the elementary scalar identity `(d / a) * a = d`.
-/
def parametrizedCoeff (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) (i : F.Index) :
    ℂ :=
  HaarRepresentation.Coeff G F f hf i / (((l2Scale G F s p i : ℝ) : ℂ))

private theorem coeff_smul_parametrizedHaarToLp_eq_coeff_smul_l2normalizedHaar_toLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p β : ℝ≥0∞) [Fact (1 ≤ β)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (i : F.Index) :
    parametrizedCoeff G F s p f hf i • parametrizedHaarToLp G F s p β i =
      HaarRepresentation.Coeff G F f hf i •
        (HaarRepresentation.l2normalizedHaar_memLp G F β i).toLp
          (HaarRepresentation.L2normalizedHaar G F i) := by
  rw [parametrizedCoeff, parametrizedHaarToLp, smul_smul]
  congr 1
  have hscale_ne :
      (((l2Scale G F s p i : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast l2Scale_ne_zero G F s p i
  field_simp [hscale_ne]

/--
Every `L^β` function, with `1 < β < ∞`, has the parametrized Haar expansion.

The proof reuses the existing `L²` Haar expansion and rewrites each term using
the parametrized coefficient and parametrized atom.
-/
theorem hasSum_parametrizedCoeff_smul_parametrizedHaarToLp
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (p β : ℝ≥0∞) (hβ_one : 1 < β) (hβ_top : β < ∞)
    (f : α → ℂ) (hf : MemLp f β G.grid.μ) :
    letI : Fact (1 ≤ β) := ⟨le_of_lt hβ_one⟩
    HasSum
      (fun i : F.Index =>
        parametrizedCoeff G F s p f
            (by
              letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
              exact hf.integrable (le_of_lt hβ_one))
            i •
          parametrizedHaarToLp G F s p β i)
      (hf.toLp f) := by
  letI : Fact (1 ≤ β) := ⟨le_of_lt hβ_one⟩
  have hbase :=
    HaarRepresentation.hasSum_coeff_smul_l2normalizedHaar_toLp G F β hβ_one hβ_top f hf
  refine hbase.congr_fun ?_
  intro i
  exact
    (coeff_smul_parametrizedHaarToLp_eq_coeff_smul_l2normalizedHaar_toLp
      G F s p β f
        (by
          letI : IsFiniteMeasure G.grid.μ := (HaarRepresentation.GridOf G).isFinite
          exact hf.integrable (le_of_lt hβ_one))
        i)

/--
The coefficient `p`-power inside one grid cell, with no measure weight.
-/
def cellCoeffPower (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G) : ℝ≥0∞ :=
  ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
    ENNReal.ofReal
      (‖parametrizedCoeff G F s p f hf (.wavelet
        (HaarRepresentation.indexOfCellBranch G F Q b))‖ ^ p.toReal)

/--
The unweighted coefficient `p`-power at level `k`.
-/
def levelCoeffPower (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) :
    ℝ≥0∞ :=
  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    cellCoeffPower G F s p f hf
      { level := k
        cell := Q.1
        mem := Q.2 }

/--
The unweighted coefficient `p`-norm at level `k`.
-/
def levelCoeffNorm (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) :
    ℝ≥0∞ :=
  (levelCoeffPower G F s p f hf k) ^ (1 / p.toReal)

/--
The father coefficient contribution for the parametrized representation.
-/
def fatherCoeffNorm (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖parametrizedCoeff G F s p f hf .alpha‖

/--
The coefficient norm of the parametrized Haar representation.

There are no measure weights in this cost: take the coefficient `p`-norm at
each level and then the `q`-norm of the resulting sequence of level norms.
-/
def haarParametrizedNorm (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p q : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) : ℝ≥0∞ :=
  fatherCoeffNorm G F s p f hf +
    if q = ∞ then
      sSup (Set.range fun k => levelCoeffNorm G F s p f hf k)
    else
      (∑' k, (levelCoeffNorm G F s p f hf k) ^ q.toReal) ^ (1 / q.toReal)

end HaarParametrizedRepresentation

end

end GoodGridSpace
