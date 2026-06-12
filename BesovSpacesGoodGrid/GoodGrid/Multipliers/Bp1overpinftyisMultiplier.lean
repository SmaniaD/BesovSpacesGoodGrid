import BesovSpacesGoodGrid.GoodGrid.Multipliers.NonArchimedeanProperty
import BesovSpacesGoodGrid.GoodGrid.DiracApproximations
import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.FiniteStandardNormimpliesBesov

/-!
# Pointwise Multipliers II: `B^{1/p}_{p,∞} ∩ L^∞` consists of multipliers

This file formalizes Proposition `mult` (Pointwise Multipliers II) of the
paper *Besov-ish spaces through atomic decomposition*: every function `g` in
`B^{1/p}_{p,∞} ∩ L^∞` is a pointwise multiplier of the Souza Besov space
`B^s_{p,q}` for `0 < s < 1/p`, with operator bound of the shape
`C · |g|_{B^{1/p}_{p,∞}} + |g|_∞`.

The paper's proof splits the product `g·f` into two atomic pieces: for
near-optimal representations `f = ∑ c_Q a_Q` and `g = ∑ e_J b_J` (the latter
given by Corollary `fou`, with canonical `(1/p, p)`-atoms `b_J = 1_J`),

* `u₁` collects the terms with `J ⊊ Q`, whose level coefficient norms form a
  convolution with the geometric kernel `λ₂^{(j-k)(1/p-s)}` — this yields the
  factor `|g|_{B^{1/p}_{p,∞}} / (1 - λ₂^{1/p-s})`;
* `u₂` collects the terms with `Q ⊆ J`, whose coefficients are
  `c_Q · (∑_{J ⊇ Q} e_J)`; by Proposition `boup`.B the tower sums
  `∑_{J ⊇ Q} e_J` are bounded by `|g|_∞`, giving the factor `|g|_∞`;

and the identity `g·f = u₁ + u₂` is obtained from truncations converging in
`L¹` together with the compactness/limit machinery of Corollary `compa1`.

## Main result

* `souzaPointwiseMultipliersII`: the quantitative multiplier bound.

## Current state of the proof

The input from Corollary `fou` and Proposition `boup`.B is now proved in
`exists_fouRepresentation`: a canonical-atom representation of `g` has
`(p,∞)`-cost controlled by `|g|_{B^{1/p}_{p,∞}}`, and all ancestor-tower
coefficient sums are bounded by `|g|_∞`.  The proof uses the standard
representation machinery in `AlternativeRepresentationsAndNorms` and proves
the needed tower-sum estimate locally from the Dirac-approximation API.

The outer proof (the ε-optimization over near-optimal representations of `f`
and the uniqueness of the product representative in `L^p`) is complete.  One
inner sublemma is still `sorry`, with its mathematical content clearly
delimited:

* `exists_mult_product_representation` — the `u₁ + u₂` construction: the
  convolution estimate for `u₁`, the `L^∞` estimate for `u₂`, and the `L¹`
  truncation argument identifying `g·f = u₁ + u₂` via
  `representation_limit_strong_existence` (Corollary `compa1`).
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
The ancestor-tower coefficient sum of a representation at a cell `Q`: the sum
of the coefficients of all cells `J` of level at most `Q.level` containing
`Q`.  For the canonical-atom representation of `g` produced by Corollary
`fou`, this is the quantity `∑_{J ⊇ Q} e_J` controlled by `|g|_∞` in the
paper (Proposition `boup`.B); since the cells containing `Q` at each level
are unique, the inner sums have a single nonzero term.
-/
def ancestorCoeffSum
    (G : GoodGridSpace (α := α)) {s' : ℝ} {p' : ℝ≥0∞}
    {hs' : 0 < s'} {hp' : 1 ≤ p'} {hp'_top : p' ≠ ∞}
    [Fact (1 ≤ p')]
    {x : Lp ℂ p' G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s' p' hs' hp' hp'_top) x)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℂ := by
  classical
  exact ∑ j ∈ Finset.range (k + 1),
    ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      if Q.1 ⊆ J.1 then (R.block j).coeff J else 0

/--
The canonical Souza atom of a cell, as the element of the local space `ℂ`
attached to the cell (the constant `μ(Q)^{s−1/p}`).  Local copy of the
homonymous private definition of `PositiveCone`.
-/
private noncomputable def fouCanonicalLocalAtom
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G) : ℂ :=
  ((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) : ℝ)

/-- The local canonical atom represents the canonical Souza atom function. -/
private theorem fouCanonicalLocalAtom_toFunction
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (Q : WeakGridSpace.WeakGridCell G.toWeakGridSpace) :
    (souzaAtomFamily G s p hs hp hp_top).toFunction Q
        (fouCanonicalLocalAtom G s p ⟨Q.level, Q.cell, Q.mem⟩) =
      canonicalSouzaAtom G s p ⟨Q.level, Q.cell, Q.mem⟩ := by
  funext x
  by_cases hx : x ∈ Q.cell
  · change Q.cell.indicator
        (fun _ => fouCanonicalLocalAtom G s p ⟨Q.level, Q.cell, Q.mem⟩) x =
      canonicalSouzaAtom G s p ⟨Q.level, Q.cell, Q.mem⟩ x
    simp [canonicalSouzaAtom, fouCanonicalLocalAtom, hx]
  · change Q.cell.indicator
        (fun _ => fouCanonicalLocalAtom G s p ⟨Q.level, Q.cell, Q.mem⟩) x =
      canonicalSouzaAtom G s p ⟨Q.level, Q.cell, Q.mem⟩ x
    simp [canonicalSouzaAtom, fouCanonicalLocalAtom, hx]

/--
The `α`-indexed normalized Haar function (the father function of the full
Haar system) is constant: it does not depend on the evaluation point.
-/
private theorem fou_l2normalizedHaar_alpha_const
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (x y : α) :
    HaarRepresentation.L2normalizedHaar G F
        (UnbalancedHaarWavelet.FullHaarSystem.Index.alpha : F.Index) x =
      HaarRepresentation.L2normalizedHaar G F
        (UnbalancedHaarWavelet.FullHaarSystem.Index.alpha : F.Index) y := by
  simp [HaarRepresentation.L2normalizedHaar, HaarRepresentation.l2NormalizationFactor,
    UnbalancedHaarWavelet.FullHaarSystem.function, F.alphaFunction_def,
    UnbalancedHaarWavelet.normalizedAlphaFunction]

/--
**Proposition `boup`.B, coefficient form.**  For the canonical standard
representation of `f` in the `(1/p, p)` Souza family, the ancestor-tower
coefficient sum at a cell `Q` of level `k` coincides with the partial
standard sum of `f` at scale `k`, evaluated at any point of `Q`.

This is where `s = 1/p` is used: the canonical Souza atoms `b_J` have the
constant value `μ(J)^{1/p − 1/p} = 1` on their cells, so the tower sum of
coefficients is literally the pointwise partial sum of the representation.
-/
private theorem ancestorCoeffSum_canonicalStandard_eq_partialStandardSum
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) x)
    (hblock : ∀ j, R.block j =
      StandardAtomicRepresentation.canonicalStandardLpGridBlock G F
        (p.toReal)⁻¹ p h1p hp hp_top f hf j)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {x₀ : α} (hx₀ : x₀ ∈ Q.1) :
    ancestorCoeffSum G R Q =
      DiracApproximation.partialStandardSum G F p (p.toReal)⁻¹ f hf k x₀ := by
  classical
  -- The level-zero term is the father Haar term.
  have h0 :
      (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace 0,
          if Q.1 ⊆ J.1 then (R.block 0).coeff J else 0) =
        HaarRepresentation.Coeff G F f hf .alpha *
          HaarRepresentation.normalizedFunction G F .alpha x₀ := by
    have hUmem : Set.univ ∈ G.grid.grid.partitions 0 := by
      rw [G.grid.grid.first_partition_eq_univ]
      exact Finset.mem_singleton_self _
    let U : WeakGridSpace.LevelCell G.toWeakGridSpace 0 := ⟨Set.univ, hUmem⟩
    rw [Finset.sum_eq_single U
      (fun J _ hJU => by
        have hJ1 : J.1 = Set.univ := by
          have hJ : J.1 ∈ G.grid.grid.partitions 0 := J.2
          rw [G.grid.grid.first_partition_eq_univ] at hJ
          exact Finset.mem_singleton.mp hJ
        exact (hJU (Subtype.ext hJ1)).elim)
      (fun h => (h (Finset.mem_univ U)).elim)]
    rw [if_pos (Set.subset_univ _), hblock 0]
    have hconst : ∀ z : α,
        HaarRepresentation.L2normalizedHaar G F
            (UnbalancedHaarWavelet.FullHaarSystem.Index.alpha : F.Index) z =
          HaarRepresentation.normalizedFunction G F .alpha x₀ := fun z =>
      (fou_l2normalizedHaar_alpha_const G F z x₀).trans rfl
    simp only [StandardAtomicRepresentation.canonicalStandardLpGridBlock,
      StandardAtomicRepresentation.canonicalStandardFatherLevelBlock,
      sub_self, Real.rpow_zero, Complex.ofReal_one, div_one]
    rw [hconst]
  -- Each positive level collapses to the unique ancestor pair.
  have hsucc : ∀ j ∈ Finset.range k,
      (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace (j + 1),
          if Q.1 ⊆ J.1 then (R.block (j + 1)).coeff J else 0) =
        ∑ c' ∈ (G.grid.grid.partitions j).attach,
          StandardAtomicRepresentation.standardCellBlockFunction G F p
            (p.toReal)⁻¹ f hf ⟨j, c'.1, c'.2⟩ x₀ := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    obtain ⟨Pc, hPmem, hQP⟩ :=
      DiracApproximation.exists_ancestor G ⟨k, Q.1, Q.2⟩ (Nat.succ_le_of_lt hjk)
    obtain ⟨c, hcmem, hQc⟩ :=
      DiracApproximation.exists_ancestor G ⟨k, Q.1, Q.2⟩ (le_of_lt hjk)
    have hx₀P : x₀ ∈ Pc := hQP hx₀
    have hx₀c : x₀ ∈ c := hQc hx₀
    have hPsubc : Pc ⊆ c := by
      obtain ⟨t, htmem, hPt⟩ := G.grid.grid.nested j Pc hPmem
      have ht : t = c :=
        DiracApproximation.cell_eq_of_mem_of_mem G htmem hcmem (hPt hx₀P) hx₀c
      rwa [ht] at hPt
    let P : WeakGridSpace.LevelCell G.toWeakGridSpace (j + 1) := ⟨Pc, hPmem⟩
    let C : WeakGridSpace.LevelCell G.toWeakGridSpace j := ⟨c, hcmem⟩
    -- Collapse the cell sum to the unique level-`(j+1)` ancestor `P`.
    rw [Finset.sum_eq_single P
      (fun J _ hJP => by
        by_cases hQJ : Q.1 ⊆ J.1
        · exact ((hJP (Subtype.ext
            (DiracApproximation.cell_eq_of_mem_of_mem G J.2 hPmem
              (hQJ hx₀) hx₀P))).elim)
        · rw [if_neg hQJ])
      (fun h => (h (Finset.mem_univ P)).elim)]
    rw [if_pos hQP, hblock (j + 1)]
    -- The block coefficient collapses to the contribution of the parent `c`.
    have hPchild : P ∈ StandardAtomicRepresentation.childrenOfCell G ⟨j, c, hcmem⟩ := by
      rw [StandardAtomicRepresentation.mem_childrenOfCell_iff]
      rw [UnbalancedHaarWavelet.Grid.mem_childrenFinset_iff]
      exact ⟨hPmem, hPsubc⟩
    have hcoeff :
        (StandardAtomicRepresentation.canonicalStandardLpGridBlock G F
            (p.toReal)⁻¹ p h1p hp hp_top f hf (j + 1)).coeff P =
          StandardAtomicRepresentation.standardChildCoeff G F (p.toReal)⁻¹ p
            f hf ⟨j, c, hcmem⟩ P := by
      show (∑ Q' : WeakGridSpace.LevelCell G.toWeakGridSpace j,
          let Qg : GoodGridCell G := { level := j, cell := Q'.1, mem := Q'.2 }
          if _ : P ∈ StandardAtomicRepresentation.childrenOfCell G Qg then
            StandardAtomicRepresentation.standardChildCoeff G F (p.toReal)⁻¹ p
              f hf Qg P
          else 0) = _
      rw [Finset.sum_eq_single C
        (fun Q' _ hQ'C => by
          simp only []
          by_cases hmem : P ∈ StandardAtomicRepresentation.childrenOfCell G
            ({ level := j, cell := Q'.1, mem := Q'.2 } : GoodGridCell G)
          · have hPsub : Pc ⊆ Q'.1 := by
              have := ((HaarRepresentation.GridOf G).mem_childrenFinset_iff
                j Q'.1 Pc).1
                ((StandardAtomicRepresentation.mem_childrenOfCell_iff G
                  ⟨j, Q'.1, Q'.2⟩ P).1 hmem)
              exact this.2
            have : Q'.1 = c :=
              DiracApproximation.cell_eq_of_mem_of_mem G Q'.2 hcmem
                (hPsub hx₀P) hx₀c
            exact ((hQ'C (Subtype.ext this)).elim)
          · rw [dif_neg hmem])
        (fun h => (h (Finset.mem_univ C)).elim)]
      simp only []
      rw [dif_pos hPchild]
    rw [hcoeff]
    -- Pass to the tilde form and collapse the level sum.
    have hone :
        canonicalSouzaAtom G (p.toReal)⁻¹ p
            (StandardAtomicRepresentation.childToGoodGridCell (G := G) (Q := ⟨j, c, hcmem⟩) P) x₀ = 1 := by
      have hx : x₀ ∈ (StandardAtomicRepresentation.childToGoodGridCell
          (G := G) (Q := ⟨j, c, hcmem⟩) P).cell := hx₀P
      simp [canonicalSouzaAtom, hx, sub_self, Real.rpow_zero]
    calc
      StandardAtomicRepresentation.standardChildCoeff G F (p.toReal)⁻¹ p
          f hf ⟨j, c, hcmem⟩ P
          = StandardAtomicRepresentation.standardChildCoeff G F (p.toReal)⁻¹ p
              f hf ⟨j, c, hcmem⟩ P *
              canonicalSouzaAtom G (p.toReal)⁻¹ p
                (StandardAtomicRepresentation.childToGoodGridCell (G := G) (Q := ⟨j, c, hcmem⟩) P) x₀ := by
        rw [hone, mul_one]
      _ = ((StandardAtomicRepresentation.tildeCoeff G F
              (StandardAtomicRepresentation.c₂ G) p (p.toReal)⁻¹ f hf
              ⟨j, c, hcmem⟩ P : ℝ) : ℂ) *
            StandardAtomicRepresentation.tildeAtom G F
              (StandardAtomicRepresentation.c₂ G) p (p.toReal)⁻¹ f hf
              ⟨j, c, hcmem⟩ P x₀ :=
        StandardAtomicRepresentation.standardChildCoeff_mul_canonicalSouzaAtom_eq_tildeCoeff_mul_tildeAtom
          G F p (p.toReal)⁻¹ f hf ⟨j, c, hcmem⟩ P x₀
      _ = ∑ c' ∈ (G.grid.grid.partitions j).attach,
            StandardAtomicRepresentation.standardCellBlockFunction G F p
              (p.toReal)⁻¹ f hf ⟨j, c'.1, c'.2⟩ x₀ :=
        (DiracApproximation.standardLevelSum_eq_ancestor_term G F p
          (p.toReal)⁻¹ f hf hcmem P hPsubc hx₀P).symm
  -- Assemble the two computations.
  unfold ancestorCoeffSum DiracApproximation.partialStandardSum
  rw [Finset.sum_range_succ', h0, Finset.sum_congr rfl hsucc]
  exact add_comm _ _

/--
**Proposition `boup`.B, bound form.**  The partial standard sums of `f` at
scale `k`, evaluated inside a cell of level `k`, are bounded by any essential
bound for `f` — they are averages of `f` over cells (`claimB`).
-/
private theorem norm_partialStandardSum_le_essBound
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ)
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    {M : ℝ} (hM0 : 0 ≤ M) (hMae : ∀ᵐ z ∂G.grid.μ, ‖f z‖ ≤ M)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {x₀ : α} (hx₀ : x₀ ∈ Q.1) :
    ‖DiracApproximation.partialStandardSum G F p s f hf k x₀‖ ≤ M := by
  have h1 := DiracApproximation.claimA_standard G F f hf ⟨k, Q.1, Q.2⟩ hx₀
  rw [DiracApproximation.partialHaarSum_eq_partialStandardSum G F p s f hf] at h1
  have h2 : eLpNorm (Set.indicator Q.1 f) ∞ G.grid.μ ≤ ENNReal.ofReal M := by
    refine le_trans (eLpNorm_indicator_le f) ?_
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound hMae
  exact (ENNReal.ofReal_le_ofReal_iff hM0).1 (le_trans h1 h2)

/--
**Input from Corollary `fou` and Proposition `boup`.B.**

Every `g ∈ B^{1/p}_{p,∞} ∩ L^∞` admits a canonical-atom Souza representation
`R_g` whose `(p,∞)`-coefficient cost is controlled by a universal constant
times `|g|_{B^{1/p}_{p,∞}}`, and whose ancestor-tower coefficient sums are
all bounded by the essential bound `M` of `g`.

The representation is the canonical standard representation of `g`
(Theorem 15.1 and Corollary `fou`, from
`AlternativeRepresentationsAndNorms`); its tower sums are partial standard
sums of `g`, hence averages of `g` over cells, hence bounded by `|g|_∞` —
Proposition 17.1 (`boup`).B, from the Dirac-approximation machinery.
-/
theorem exists_fouRepresentation
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] :
    ∃ Cfou : ℝ,
      0 ≤ Cfou ∧
      ∀ (g : α → ℂ) (M : ℝ)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        ∃ Rg : WeakGridSpace.LpGridRepresentation
            (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top)
            (xg : Lp ℂ p G.toWeakGridSpace.measure),
          SouzaCanonicalRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg ∧
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := ∞) Rg ∧
          WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg ≤
            Cfou * WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞ xg ∧
          ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            ‖ancestorCoeffSum G Rg Q‖ ≤ M := by
  classical
  letI : DecidableEq (Set α) := Classical.decEq (Set α)
  haveI : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  haveI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hp_lt_top : p < ∞ := lt_top_iff_ne_top.mpr hp_top
  -- The full Haar system underlying the standard representation.
  let H : UnbalancedHaarWavelet.HaarSystem (HaarRepresentation.GridOf G) :=
    Classical.choice
      (UnbalancedHaarWavelet.exists_haarSystem (HaarRepresentation.GridOf G))
  let F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G) :=
    { toHaarSystem := H
      alphaFunction := UnbalancedHaarWavelet.normalizedAlphaFunction
        (HaarRepresentation.GridOf G)
      alphaFunction_def := rfl }
  letI : DecidableEq F.Index := Classical.decEq F.Index
  obtain ⟨Cst, hCst_ne_top, hstandard_le⟩ :=
    StandardAtomicRepresentation.exists_standardRepresentationNorm_le_const_mul_souzaBesovNorm
      (G := G) (F := F) (s := (p.toReal)⁻¹) (hs := h1p) (p := p)
      (hp_top := hp_lt_top) (q := (∞ : ℝ≥0∞))
  refine ⟨Cst.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro g M xg hgrep hgM
  let A := souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top
  let fFun : α → ℂ := ((xg : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
  have hfMemLp : MemLp fFun p G.grid.μ := by
    simpa [fFun, GoodGridSpace.toWeakGridSpace] using
      (Lp.memLp (xg : Lp ℂ p G.toWeakGridSpace.measure))
  have hfint : Integrable fFun G.grid.μ := hfMemLp.integrable (Fact.out : 1 ≤ p)
  -- The essential bound is nonnegative, since the measure is nonzero.
  have hM0 : 0 ≤ M := by
    have hμpos : 0 < G.grid.μ Set.univ := by
      refine G.grid.positive_measure 0 Set.univ ?_
      rw [G.grid.grid.first_partition_eq_univ]
      exact Finset.mem_singleton_self _
    have hμne : G.toWeakGridSpace.measure ≠ 0 := by
      intro h0
      rw [show G.toWeakGridSpace.measure = G.grid.μ from rfl] at h0
      rw [h0] at hμpos
      simp at hμpos
    haveI : (Filter.NeBot (MeasureTheory.ae G.toWeakGridSpace.measure)) :=
      MeasureTheory.ae_neBot.mpr hμne
    obtain ⟨z, hz⟩ := hgM.exists
    exact le_trans (norm_nonneg (g z)) hz
  -- Cost control: Corollary `fou`.
  have hstd :
      StandardAtomicRepresentation.standardRepresentationNorm G F
          (p.toReal)⁻¹ h1p p hp_lt_top ∞ fFun hfint ≠ ∞ ∧
        StandardAtomicRepresentation.standardRepresentationNorm G F
            (p.toReal)⁻¹ h1p p hp_lt_top ∞ fFun hfint ≤
          Cst * ENNReal.ofReal
            (WeakGridSpace.BesovishSpace.Norm_Costpq A ∞ xg) := by
    simpa [A, fFun, GoodGridSpace.toWeakGridSpace] using
      hstandard_le xg fFun hfint Filter.EventuallyEq.rfl
  rcases hstd with ⟨hstd_ne_top, hstd_le⟩
  rcases StandardAtomicRepresentation.finite_standardRepresentationNorm_implies_memBesov_and_standardRepresentation
      (G := G) (F := F) (s := (p.toReal)⁻¹) (hs := h1p) (p := p)
      (hp_top := hp_lt_top) (q := (∞ : ℝ≥0∞)) fFun hfint hstd_ne_top with
    ⟨hfLp, gstd, Rstd, hgstdLp, hRstd_block, hRstd_fin, _hRstd_enn,
      hRstd_cost, _hgstd_cost⟩
  -- The represented element is `xg` itself.
  have hLp_eq : (gstd : Lp ℂ p G.toWeakGridSpace.measure) =
      (xg : Lp ℂ p G.toWeakGridSpace.measure) := by
    have hto : hfLp.toLp fFun = (xg : Lp ℂ p G.toWeakGridSpace.measure) := by
      change hfLp.toLp ((xg : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =
        (xg : Lp ℂ p G.toWeakGridSpace.measure)
      exact Lp.toLp_coeFn (xg : Lp ℂ p G.toWeakGridSpace.measure) hfLp
    exact hgstdLp.trans hto
  -- Transport the representation to `xg` (only the target is rewritten).
  let Rg : WeakGridSpace.LpGridRepresentation A
      (xg : Lp ℂ p G.toWeakGridSpace.measure) :=
    { block := Rstd.block
      hasSum := hLp_eq ▸ Rstd.hasSum }
  have hRg_block : ∀ j, Rg.block j =
      StandardAtomicRepresentation.canonicalStandardLpGridBlock G F
        (p.toReal)⁻¹ p h1p hp hp_top fFun hfint j := fun j =>
    congrFun hRstd_block j
  -- The standard representation uses canonical atoms.
  have hRg_canon : SouzaCanonicalRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg := by
    intro k
    have hb := hRg_block k
    intro Q
    rw [hb]
    cases k with
    | zero =>
        simpa [A, StandardAtomicRepresentation.canonicalStandardLpGridBlock,
          StandardAtomicRepresentation.canonicalStandardFatherLevelBlock,
          fouCanonicalLocalAtom, goodGridCellOfLevelCell] using
          fouCanonicalLocalAtom_toFunction G (p.toReal)⁻¹ p h1p hp hp_top
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace 0 Q)
    | succ k =>
        simpa [A, StandardAtomicRepresentation.canonicalStandardLpGridBlock,
          StandardAtomicRepresentation.canonicalStandardPositiveLevelBlock,
          fouCanonicalLocalAtom, goodGridCellOfLevelCell] using
          fouCanonicalLocalAtom_toFunction G (p.toReal)⁻¹ p h1p hp hp_top
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace (k + 1) Q)
  -- Finite cost and the `fou` cost bound.
  have hRg_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := ∞) Rg :=
    hRstd_fin
  have hRg_cost : WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg ≤
      Cst.toReal * WeakGridSpace.BesovishSpace.Norm_Costpq A ∞ xg := by
    have hNg0 : 0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A ∞ xg :=
      WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg (A := A) (q := ∞)
        (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A ∞) xg
    have h2 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hCst_ne_top ENNReal.ofReal_ne_top) hstd_le
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hNg0] at h2
    exact le_trans hRstd_cost h2
  -- Tower bound: Proposition `boup`.B.
  have hMae : ∀ᵐ z ∂G.grid.μ, ‖fFun z‖ ≤ M := by
    have h1 : (fFun : α → ℂ) =ᵐ[G.grid.μ] g := by
      simpa [fFun, GoodGridSpace.toWeakGridSpace] using hgrep
    have h2 : ∀ᵐ z ∂G.grid.μ, ‖g z‖ ≤ M := by
      simpa [GoodGridSpace.toWeakGridSpace] using hgM
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1]
    exact hz2
  have hRg_tower : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖ancestorCoeffSum G Rg Q‖ ≤ M := by
    intro k Q
    obtain ⟨x₀, hx₀⟩ := G.grid.partition_nonempty k Q.1 Q.2
    rw [ancestorCoeffSum_canonicalStandard_eq_partialStandardSum G F p h1p hp
      hp_top fFun hfint Rg hRg_block Q hx₀]
    exact norm_partialStandardSum_le_essBound G F p (p.toReal)⁻¹ fFun hfint
      hM0 hMae Q hx₀
  exact ⟨Rg, hRg_canon, hRg_fin, hRg_cost, hRg_tower⟩

/--
The level-`k` block of the piece `u₂` of the paper's proof: it reuses the
atoms of the representation of `f`, and multiplies each coefficient `c_Q` by
the ancestor-tower sum `∑_{J ⊇ Q} e_J` of the representation of `g`.

This realizes the paper's identity `a_Q · b_J = a_Q` for `Q ⊆ J`: collecting
all such terms attaches to the cell `Q` the coefficient
`c_Q · ∑_{J ⊇ Q} e_J`, with the original atom of `f` unchanged.
-/
private noncomputable def multU2Block
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg)
    (k : ℕ) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k where
  coeff := fun Q => (Rf.block k).coeff Q * ancestorCoeffSum G Rg Q
  atom := (Rf.block k).atom
  atom_mem := (Rf.block k).atom_mem

/--
Levelwise cost of the `u₂` blocks: when all ancestor-tower sums of `Rg` are
bounded by `M`, the `p`-th power coefficient sum of `multU2Block` at each
level is at most `M^p` times that of `Rf`.

This is the paper's estimate
`(∑_Q |c_Q · ∑_{J ⊇ Q} e_J|^p)^{1/p} ≤ |g|_∞ · (∑_Q |c_Q|^p)^{1/p}`.
-/
private theorem multU2Block_levelCoeffPower_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg)
    {M : ℝ} (hM0 : 0 ≤ M)
    (htower : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖ancestorCoeffSum G Rg Q‖ ≤ M)
    (k : ℕ) :
    (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(multU2Block G s p hs h1p hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal) ≤
      M ^ p.toReal * Rf.levelCoeffPower k := by
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hterm : ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ‖(multU2Block G s p hs h1p hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal ≤
        M ^ p.toReal * ‖(Rf.block k).coeff Q‖ ^ p.toReal := by
    intro Q
    have hnorm :
        ‖(multU2Block G s p hs h1p hp hp_top Rf Rg k).coeff Q‖ =
          ‖(Rf.block k).coeff Q‖ * ‖ancestorCoeffSum G Rg Q‖ :=
      norm_mul _ _
    have hle :
        ‖(Rf.block k).coeff Q‖ * ‖ancestorCoeffSum G Rg Q‖ ≤
          ‖(Rf.block k).coeff Q‖ * M :=
      mul_le_mul_of_nonneg_left (htower k Q) (norm_nonneg _)
    calc
      ‖(multU2Block G s p hs h1p hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal
          ≤ (‖(Rf.block k).coeff Q‖ * M) ^ p.toReal := by
        rw [hnorm]
        exact Real.rpow_le_rpow
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hle hpt_pos.le
      _ = M ^ p.toReal * ‖(Rf.block k).coeff Q‖ ^ p.toReal := by
        rw [Real.mul_rpow (norm_nonneg _) hM0, mul_comm]
  calc
    (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(multU2Block G s p hs h1p hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal)
        ≤ ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            M ^ p.toReal * ‖(Rf.block k).coeff Q‖ ^ p.toReal :=
      Finset.sum_le_sum fun Q _ => hterm Q
    _ = M ^ p.toReal *
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            ‖(Rf.block k).coeff Q‖ ^ p.toReal := by
      rw [Finset.mul_sum]
    _ = M ^ p.toReal * Rf.levelCoeffPower k := rfl

/--
The level-`j` block of the piece `u₁` of the paper's proof: on each cell `J`
it carries the coefficient `e_J · ∑_{Q ⊋ J} c_Q v_Q μ(J)^{1/p−s}` over the
canonical `(s,p)`-Souza atom on `J`, where `v_Q` is the value of the atom of
`Rf` at `Q`.  This realizes the paper's identity
`a_Q · b_J = (value of a_Q) · μ(J)^{1/p−s} · (canonical a_J)` for `J ⊊ Q`:
the strict ancestors `Q ⊋ J` are exactly the cells of levels `k < j`
containing `J`.
-/
private noncomputable def multU1Block
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg)
    (j : ℕ) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) j := by
  classical
  exact
  { coeff := fun J =>
      (Rg.block j).coeff J *
        ∑ k ∈ Finset.range j,
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            if J.1 ⊆ Q.1 then
              (Rf.block k).coeff Q *
                (show ℂ from (Rf.block k).atom Q) *
                (((G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
            else 0
    atom := fun J =>
      (((G.grid.μ J.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)
    atom_mem := fun J => by
      change ‖(((G.grid.μ J.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)‖ ≤
        (G.grid.μ J.1).toReal ^ (s - (p.toReal)⁻¹)
      rw [Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)] }

open Classical in
/--
Pointwise coefficient bound for the `u₁` blocks: the transmutation factor of
each strict ancestor at level `k < j` is at most `λ₂^{(j−k)(1/p−s)}`, so

`‖coeff(u₁)_J‖ ≤ ‖e_J‖ · ∑_{k<j} λ₂^{(j−k)(1/p−s)} ·
  (∑_{Q ∈ P^k, Q ⊇ J} ‖c_Q‖)`.

The inner sum over `Q` has at most one nonzero term (the level-`k` ancestor
of `J`).  This is the per-cell input to the paper's convolution estimate.
-/
private theorem multU1Block_coeff_norm_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg)
    (j : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace j) :
    ‖(multU1Block G s p hs h1p hp hp_top Rf Rg j).coeff J‖ ≤
      ‖(Rg.block j).coeff J‖ *
        ∑ k ∈ Finset.range j,
          (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) *
            ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              (if J.1 ⊆ Q.1 then ‖(Rf.block k).coeff Q‖ else 0) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hθ : 0 < (p.toReal)⁻¹ - s := sub_pos.mpr hs_lt_inv
  have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
    le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hcoeff :
      (multU1Block G s p hs h1p hp hp_top Rf Rg j).coeff J =
        (Rg.block j).coeff J *
          ∑ k ∈ Finset.range j,
            ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              if J.1 ⊆ Q.1 then
                (Rf.block k).coeff Q *
                  (show ℂ from (Rf.block k).atom Q) *
                  (((G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
              else 0 := rfl
  rw [hcoeff, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun k hk => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun Q _ => ?_
  by_cases hJQ : J.1 ⊆ Q.1
  · rw [if_pos hJQ, if_pos hJQ]
    -- The measure-ratio estimate for the level-`k` ancestor.
    have hkj : k ≤ j := (Finset.mem_range.mp hk).le
    have hJmem : J.1 ∈ G.grid.grid.partitions (k + (j - k)) := by
      rw [Nat.add_sub_cancel' hkj]
      exact J.2
    have hμJ_le :
        G.grid.μ J.1 ≤
          (ENNReal.ofReal G.grid.lambda2) ^ (j - k) * G.grid.μ Q.1 :=
      cell_measure_le_lambda2_pow_mul_cell G ⟨k, Q.1, Q.2⟩ (j - k) J.1
        hJmem hJQ
    have hμQ_pos : 0 < (G.grid.μ Q.1).toReal :=
      ENNReal.toReal_pos
        (G.grid.positive_measure k Q.1 Q.2).ne'
        (MeasureTheory.measure_ne_top G.grid.μ Q.1)
    have hμJ_real :
        (G.grid.μ J.1).toReal ≤
          G.grid.lambda2 ^ (j - k) * (G.grid.μ Q.1).toReal := by
      have hRHS_ne :
          (ENNReal.ofReal G.grid.lambda2) ^ (j - k) * G.grid.μ Q.1 ≠ ∞ :=
        ENNReal.mul_ne_top
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          (MeasureTheory.measure_ne_top G.grid.μ Q.1)
      have := ENNReal.toReal_mono hRHS_ne hμJ_le
      rwa [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hlam_nonneg] at this
    -- The atom value is controlled by the Souza normalization.
    have hatom_le :
        ‖(show ℂ from (Rf.block k).atom Q)‖ ≤
          (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) :=
      (Rf.block k).atom_mem Q
    -- The transmutation factor estimate.
    have hfactor :
        ‖(show ℂ from (Rf.block k).atom Q)‖ *
            (G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) ≤
          (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) := by
      have hμJθ :
          (G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) ≤
            (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) *
              (G.grid.μ Q.1).toReal ^ ((p.toReal)⁻¹ - s) := by
        rw [← Real.mul_rpow (pow_nonneg hlam_nonneg _) hμQ_pos.le]
        exact Real.rpow_le_rpow ENNReal.toReal_nonneg hμJ_real hθ.le
      calc
        ‖(show ℂ from (Rf.block k).atom Q)‖ *
            (G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s)
            ≤ (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) *
                ((G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) *
                  (G.grid.μ Q.1).toReal ^ ((p.toReal)⁻¹ - s)) :=
          mul_le_mul hatom_le hμJθ
            (Real.rpow_nonneg ENNReal.toReal_nonneg _)
            (Real.rpow_nonneg ENNReal.toReal_nonneg _)
        _ = (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) *
              ((G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) *
                (G.grid.μ Q.1).toReal ^ ((p.toReal)⁻¹ - s)) := by ring
        _ = (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) := by
          rw [← Real.rpow_add hμQ_pos]
          have hzero : (s - (p.toReal)⁻¹) + ((p.toReal)⁻¹ - s) = 0 := by
            ring
          rw [hzero, Real.rpow_zero, mul_one]
    -- Assemble the per-term bound.
    have hμJθ_nonneg :
        (0 : ℝ) ≤ (G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    calc
      ‖(Rf.block k).coeff Q * (show ℂ from (Rf.block k).atom Q) *
          (((G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)‖
          = ‖(Rf.block k).coeff Q‖ *
              (‖(show ℂ from (Rf.block k).atom Q)‖ *
                (G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s)) := by
        rw [norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hμJθ_nonneg, mul_assoc]
      _ ≤ ‖(Rf.block k).coeff Q‖ *
            (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) :=
        mul_le_mul_of_nonneg_left hfactor (norm_nonneg _)
      _ = (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) *
            ‖(Rf.block k).coeff Q‖ := by ring
  · rw [if_neg hJQ, if_neg hJQ]
    simp

/--
**The `u₁ + u₂` construction** (still `sorry`).

Given a finite-cost representation `R_f` of `x` and a canonical-atom
representation `R_g` of `g` with bounded ancestor-tower sums, the product
`g·f` has a Besov representative `y` with

`‖y‖ ≤ (Cconv · pqCost_{(p,∞)} R_g + M) · pqCost_{(p,q)} R_f`,

where `Cconv = Cconv(G, s, p)` reflects the geometric series
`∑_n λ₂^{n(1/p−s)} = (1 − λ₂^{1/p−s})⁻¹`.

Mathematical content (the body of the paper's proof): split
`a_Q · b_J = a_Q` for `Q ⊆ J` and `a_Q · b_J = (|J|/|Q|)^{1/p−s} a_J` for
`J ⊊ Q`; assemble `u₁` (convolution estimate over levels, Young's
inequality) and `u₂` (tower-sum estimate); identify `g·f = u₁ + u₂` through
`L¹`-convergent truncations and `representation_limit_strong_existence`.
-/
theorem exists_mult_product_representation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cconv : ℝ,
      0 ≤ Cconv ∧
      ∀ (g : α → ℂ) (M : ℝ) (hM : 0 ≤ M)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞)
        (Rg : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top)
          (xg : Lp ℂ p G.toWeakGridSpace.measure))
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (Rf : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        SouzaCanonicalRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := ∞) Rg →
        (∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          ‖ancestorCoeffSum G Rg Q‖ ≤ M) →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rf →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsPointwiseProduct
            (G := G.toWeakGridSpace) (p := p) g
            (x : Lp ℂ p G.toWeakGridSpace.measure)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q y ≤
            (Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg
                + M) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf := by
  sorry

/--
**Proposition `mult` of the paper (Pointwise Multipliers II).**

Let `0 < s < 1/p`.  There is a constant `Cmult` such that every function
`g ∈ B^{1/p}_{p,∞} ∩ L^∞` — formally: `g` is represented by a Besov-ish
element `xg` of the `(1/p, p, ∞)` Souza space and `‖g‖ ≤ M` almost
everywhere — is a pointwise multiplier of `B^s_{p,q}` with operator bound

`|G|_{B^s_{p,q}} ≤ Cmult · |g|_{B^{1/p}_{p,∞}} + M`,

the formal counterpart of the paper's bound
`Ce·Cno·|g|_{B^{1/p}_{p,∞}}/(1 − λ₂^{1/p−s}) + |g|_∞`.
-/
theorem souzaPointwiseMultipliersII
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cmult : ℝ,
      0 ≤ Cmult ∧
      ∀ (g : α → ℂ) (M : ℝ)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        SouzaPointwiseMultiplierBound G s p q hs hp hp_top g
          (Cmult * WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞ xg
            + M) := by
  classical
  obtain ⟨Cfou, hCfou0, hCfou⟩ :=
    exists_fouRepresentation G p h1p hp hp_top
  obtain ⟨Cconv, hCconv0, hCconv⟩ :=
    exists_mult_product_representation G s p q hs hs_lt_inv h1p hp hp_top
  refine ⟨Cconv * Cfou, mul_nonneg hCconv0 hCfou0, ?_⟩
  intro g M xg hgrep hgM
  set Ng : ℝ := WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞ xg with hNg
  -- The essential bound is nonnegative, since the measure is nonzero.
  have hM0 : 0 ≤ M := by
    have hμpos : 0 < G.grid.μ Set.univ := by
      refine G.grid.positive_measure 0 Set.univ ?_
      rw [G.grid.grid.first_partition_eq_univ]
      exact Finset.mem_singleton_self _
    have hμne : G.toWeakGridSpace.measure ≠ 0 := by
      intro h0
      rw [show G.toWeakGridSpace.measure = G.grid.μ from rfl] at h0
      rw [h0] at hμpos
      simp at hμpos
    haveI : (Filter.NeBot (MeasureTheory.ae G.toWeakGridSpace.measure)) :=
      MeasureTheory.ae_neBot.mpr hμne
    obtain ⟨z, hz⟩ := hgM.exists
    exact le_trans (norm_nonneg (g z)) hz
  have hNg0 : 0 ≤ Ng :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg (A := souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) (q := ∞)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞) xg
  -- The `fou` representation of `g`.
  obtain ⟨Rg, hRgcanon, hRgfin, hRgcost, hRgtower⟩ := hCfou g M xg hgrep hgM
  have hCbound :
      Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg + M ≤
        Cconv * Cfou * Ng + M := by
    have := mul_le_mul_of_nonneg_left hRgcost hCconv0
    calc
      Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg + M
          ≤ Cconv * (Cfou * Ng) + M := by linarith
      _ = Cconv * Cfou * Ng + M := by ring
  have hK0 : 0 ≤ Cconv * Cfou * Ng + M := by positivity
  refine ⟨hK0, ?_⟩
  intro x
  -- One run of the product construction for an arbitrary finite-cost
  -- representation of `x`.
  have key :
      ∀ Rf : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rf →
        ∃ y : WeakGridSpace.BesovishSpace (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsPointwiseProduct
            (G := G.toWeakGridSpace) (p := p) g
            (x : Lp ℂ p G.toWeakGridSpace.measure)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q y ≤
            (Cconv * Cfou * Ng + M) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf := by
    intro Rf hRffin
    obtain ⟨y, hyprod, hynorm⟩ :=
      hCconv g M hM0 xg Rg x Rf hgrep hgM hRgcanon hRgfin hRgtower hRffin
    refine ⟨y, hyprod, hynorm.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hCbound
      (WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rf)
  -- Fix the product representative once, then optimize the cost bound.
  obtain ⟨R₁, hR₁fin, _⟩ :=
    WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add (A := souzaAtomFamily G s p hs hp hp_top)
      (q := q)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (souzaAtomFamily G s p hs hp hp_top) q) x
      one_pos
  obtain ⟨y, hyProd, _⟩ := key R₁ hR₁fin
  refine ⟨y, hyProd, ?_⟩
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hden : (0 : ℝ) < Cconv * Cfou * Ng + M + 1 := by linarith
  have hδ : 0 < ε / (Cconv * Cfou * Ng + M + 1) := by positivity
  obtain ⟨Rf, hRffin, hRflt⟩ :=
    WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add (A := souzaAtomFamily G s p hs hp hp_top)
      (q := q)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (souzaAtomFamily G s p hs hp hp_top) q) x hδ
  obtain ⟨y', hy'Prod, hy'Norm⟩ := key Rf hRffin
  have hyy' : y' = y := by
    apply Subtype.ext
    apply Lp.ext
    exact hy'Prod.trans hyProd.symm
  have hcost_le :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf ≤
        WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q x +
          ε / (Cconv * Cfou * Ng + M + 1) :=
    hRflt.le
  have hmul :
      (Cconv * Cfou * Ng + M) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf ≤
        (Cconv * Cfou * Ng + M) *
          (WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q x +
            ε / (Cconv * Cfou * Ng + M + 1)) :=
    mul_le_mul_of_nonneg_left hcost_le hK0
  have hfrac :
      (Cconv * Cfou * Ng + M) *
          (ε / (Cconv * Cfou * Ng + M + 1)) ≤ ε := by
    have hratio :
        (Cconv * Cfou * Ng + M) / (Cconv * Cfou * Ng + M + 1) ≤ (1 : ℝ) :=
      (div_le_one hden).2 (by linarith)
    have hmul' := mul_le_mul_of_nonneg_right hratio hε.le
    calc
      (Cconv * Cfou * Ng + M) * (ε / (Cconv * Cfou * Ng + M + 1))
          = ((Cconv * Cfou * Ng + M) / (Cconv * Cfou * Ng + M + 1)) * ε := by
        ring
      _ ≤ 1 * ε := hmul'
      _ = ε := one_mul ε
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q y
        = WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q y' := by rw [hyy']
    _ ≤ (Cconv * Cfou * Ng + M) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf := hy'Norm
    _ ≤ (Cconv * Cfou * Ng + M) *
          (WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q x +
            ε / (Cconv * Cfou * Ng + M + 1)) := hmul
    _ = (Cconv * Cfou * Ng + M) *
          WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q x +
          (Cconv * Cfou * Ng + M) *
            (ε / (Cconv * Cfou * Ng + M + 1)) := by ring
    _ ≤ (Cconv * Cfou * Ng + M) *
          WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q x + ε := by
      linarith

end

end GoodGridSpace
