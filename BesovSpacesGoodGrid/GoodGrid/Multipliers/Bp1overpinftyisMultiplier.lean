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

## Main results

* `souzaPointwiseMultipliersII`: the quantitative multiplier bound.
* `souzaPointwiseMultipliersIIPositive` (Remark `pos3`): the positive-cone
  version, with the bound stated for the positive gauges `souzaPositiveNorm`;
  its representation form is `exists_mult_product_representation_pos`.

## Structure of the proof

The input from Corollary `fou` and Proposition `boup`.B is proved in
`exists_fouRepresentation`: a canonical-atom representation of `g` has
`(p,∞)`-cost controlled by `|g|_{B^{1/p}_{p,∞}}`, and all ancestor-tower
coefficient sums are bounded by `|g|_∞`.  The proof uses the standard
representation machinery in `AlternativeRepresentationsAndNorms` and proves
the needed tower-sum estimate locally from the Dirac-approximation API.

The core `u₁ + u₂` construction is `exists_mult_product_representation`: the
block families `multU1Block`/`multU2Block` realize the atom algebra
`a_Q · b_J`, their costs are controlled by a discrete Young inequality with
geometric kernel (`u₁`) and by the tower-sum `L^∞` bound (`u₂`), the block
series converge in `L^p` through `formalBlockSeq_hasRepresentation`, and the
identity `g·f = u₁ + u₂` follows from the exact pointwise identity of
truncated products passed to the limit along a.e.-convergent subsequences.

The outer proof (the ε-optimization over near-optimal representations of `f`
and the uniqueness of the product representative in `L^p`) then yields the
multiplier bound.

For Remark `pos3`, the same block construction is reused: positivity of the
representations of `f` and `g` is inherited by the `u₁`/`u₂` blocks, the
canonical-atom hypothesis and the ancestor-tower bound are derived from
positivity (positive form of Proposition `boup`.B), and the two pieces are
summed inside the positive cone.  The file is `sorry`-free.
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

/-!
### Analytic toolbox: real `rpow` cancellation, the geometric `ℓ^q` Young
inequality, and cost comparison for bare block families.
-/

private theorem rpow_one_div_rpow {x : ℝ} (hx : 0 ≤ x) {e : ℝ} (he : e ≠ 0) :
    (x ^ (1 / e)) ^ e = x := by
  rw [← Real.rpow_mul hx, one_div, inv_mul_cancel₀ he, Real.rpow_one]

private theorem rpow_rpow_one_div {x : ℝ} (hx : 0 ≤ x) {e : ℝ} (he : e ≠ 0) :
    (x ^ e) ^ (1 / e) = x := by
  rw [← Real.rpow_mul hx, mul_one_div, div_self he, Real.rpow_one]

/--
**Discrete Young inequality with geometric kernel.**  If `r ≥ 0` has
summable `qt`-th powers and `0 ≤ a`, with all partial sums
`∑_{n<N} a^{n+1}` bounded by `W`, then the level convolution
`c_j = ∑_{k<j} a^{j−k} r_k` has summable `qt`-th powers and

`∑_j c_j^qt ≤ W^qt · ∑_k r_k^qt`.

This is the `ℓ^1 * ℓ^q ⊆ ℓ^q` convolution inequality specialized to the
geometric kernel of the paper's `u₁` estimate, proved by iterated Minkowski
(`Real.Lp_add_le_tsum_of_nonneg'`) on the shifted blocks.
-/
private theorem geometric_conv_rpow_summable_and_tsum_le
    {qt : ℝ} (hqt : 1 ≤ qt) {a : ℝ} (ha0 : 0 ≤ a)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (hrs : Summable fun k => r k ^ qt)
    {W : ℝ} (hW : ∀ N : ℕ, (∑ n ∈ Finset.range N, a ^ (n + 1)) ≤ W) :
    Summable (fun j => (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ qt) ∧
      (∑' j, (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ qt) ≤
        W ^ qt * ∑' k, r k ^ qt := by
  classical
  have hqt0 : (0 : ℝ) < qt := lt_of_lt_of_le zero_lt_one hqt
  have hW0 : 0 ≤ W := le_trans (by simp) (hW 0)
  set R : ℝ := (∑' k, r k ^ qt) ^ (1 / qt) with hR
  have hRq_nonneg : 0 ≤ ∑' k, r k ^ qt :=
    tsum_nonneg fun k => Real.rpow_nonneg (hr k) _
  have hR0 : 0 ≤ R := Real.rpow_nonneg hRq_nonneg _
  -- The shifted kernel blocks.
  set t : ℕ → ℕ → ℝ :=
    fun n j => if n + 1 ≤ j then a ^ (n + 1) * r (j - (n + 1)) else 0 with ht
  have ht_nonneg : ∀ n j, 0 ≤ t n j := by
    intro n j
    simp only [ht]
    split
    · exact mul_nonneg (pow_nonneg ha0 _) (hr _)
    · exact le_refl 0
  set c : ℕ → ℝ := fun j => ∑ k ∈ Finset.range j, a ^ (j - k) * r k with hc
  have hc_nonneg : ∀ j, 0 ≤ c j := fun j =>
    Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg ha0 _) (hr k)
  -- `c j` agrees with the partial kernel sums of length `≥ j`.
  have hc_eq_part : ∀ N j, j ≤ N → c j = ∑ n ∈ Finset.range N, t n j := by
    intro N j hjN
    have hsubset :
        ∑ n ∈ Finset.range N, t n j = ∑ n ∈ Finset.range j, t n j := by
      refine (Finset.sum_subset (Finset.range_subset_range.mpr hjN) ?_).symm
      intro n _ hn
      have hnj : ¬ (n + 1 ≤ j) := by
        intro hcon
        exact hn (Finset.mem_range.mpr (Nat.lt_of_succ_le hcon))
      simp only [ht]
      exact if_neg hnj
    have hreflect :
        ∑ n ∈ Finset.range j, t n j =
          ∑ k ∈ Finset.range j, a ^ (j - k) * r k := by
      have := Finset.sum_range_reflect (fun k => a ^ (j - k) * r k) j
      rw [← this]
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hnj : n < j := Finset.mem_range.mp hn
      have h1 : j - (j - 1 - n) = n + 1 := by omega
      have h2 : j - 1 - n = j - (n + 1) := by omega
      have h3 : n + 1 ≤ j := hnj
      rw [h1, h2]
      simp only [ht]
      exact if_pos h3
    rw [hsubset, hreflect]
  -- Each shifted block has summable powers with the geometric root bound.
  have hblock : ∀ n : ℕ,
      Summable (fun j => t n j ^ qt) ∧
        (∑' j, t n j ^ qt) = (a ^ (n + 1)) ^ qt * ∑' k, r k ^ qt := by
    intro n
    have hshift : (fun j : ℕ => t n (j + (n + 1)) ^ qt) =
        fun j : ℕ => (a ^ (n + 1)) ^ qt * r j ^ qt := by
      funext j
      have h1 : n + 1 ≤ j + (n + 1) := Nat.le_add_left _ _
      have h2 : j + (n + 1) - (n + 1) = j := by omega
      simp only [ht, if_pos h1, h2]
      exact Real.mul_rpow (pow_nonneg ha0 _) (hr j)
    have hsum_shift : Summable (fun j : ℕ => t n (j + (n + 1)) ^ qt) := by
      rw [hshift]
      exact hrs.mul_left _
    have hsum : Summable (fun j => t n j ^ qt) :=
      (summable_nat_add_iff (n + 1)).mp hsum_shift
    refine ⟨hsum, ?_⟩
    have hsplit := hsum.sum_add_tsum_nat_add (n + 1)
    have hzero : (∑ i ∈ Finset.range (n + 1), t n i ^ qt) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hii : ¬ (n + 1 ≤ i) := by
        have := Finset.mem_range.mp hi
        omega
      simp only [ht, if_neg hii]
      exact Real.zero_rpow hqt0.ne'
    rw [hzero, zero_add] at hsplit
    rw [← hsplit, hshift]
    exact (hrs.hasSum.mul_left _).tsum_eq
  have hblock_root : ∀ n : ℕ,
      (∑' j, t n j ^ qt) ^ (1 / qt) ≤ a ^ (n + 1) * R := by
    intro n
    rw [(hblock n).2, Real.mul_rpow (Real.rpow_nonneg (pow_nonneg ha0 _) _)
      hRq_nonneg, rpow_rpow_one_div (pow_nonneg ha0 _) hqt0.ne']
  -- Minkowski induction on the partial kernel sums.
  set part : ℕ → ℕ → ℝ := fun N j => ∑ n ∈ Finset.range N, t n j with hpartdef
  have hpart_nonneg : ∀ N j, 0 ≤ part N j := fun N j =>
    Finset.sum_nonneg fun n _ => ht_nonneg n j
  have hpart : ∀ N : ℕ,
      Summable (fun j => part N j ^ qt) ∧
        (∑' j, part N j ^ qt) ^ (1 / qt) ≤
          (∑ n ∈ Finset.range N, a ^ (n + 1)) * R := by
    intro N
    induction N with
    | zero =>
        constructor
        · simp [part, Real.zero_rpow hqt0.ne']
        · have h0 : (∑' j : ℕ, part 0 j ^ qt) = 0 := by
            have hz : ∀ j : ℕ, part 0 j ^ qt = 0 := by
              intro j
              simp [part, Real.zero_rpow hqt0.ne']
            simp [hz]
          rw [h0, Real.zero_rpow (one_div_ne_zero hqt0.ne')]
          simp
    | succ N ih =>
        rcases ih with ⟨ih_sum, ih_bound⟩
        have hsucc_fun : ∀ j, part (N + 1) j = part N j + t N j := by
          intro j
          simp [part, Finset.sum_range_succ]
        have hsum_succ : Summable (fun j => part (N + 1) j ^ qt) := by
          simp only [hsucc_fun]
          exact Real.summable_Lp_add_of_nonneg hqt
            (fun j => hpart_nonneg N j) (fun j => ht_nonneg N j)
            ih_sum (hblock N).1
        refine ⟨hsum_succ, ?_⟩
        have hLp := Real.Lp_add_le_tsum_of_nonneg' hqt
          (fun j => hpart_nonneg N j) (fun j => ht_nonneg N j)
          ih_sum (hblock N).1
        calc
          (∑' j, part (N + 1) j ^ qt) ^ (1 / qt)
              = (∑' j, (part N j + t N j) ^ qt) ^ (1 / qt) := by
            simp only [hsucc_fun]
          _ ≤ (∑' j, part N j ^ qt) ^ (1 / qt) +
                (∑' j, t N j ^ qt) ^ (1 / qt) := hLp
          _ ≤ (∑ n ∈ Finset.range N, a ^ (n + 1)) * R +
                a ^ (N + 1) * R := add_le_add ih_bound (hblock_root N)
          _ = (∑ n ∈ Finset.range (N + 1), a ^ (n + 1)) * R := by
            rw [Finset.sum_range_succ]
            ring
  -- Uniform bound for the partial sums of `c^qt`.
  have hWR : ∀ N : ℕ, (∑' j, part N j ^ qt) ≤ (W * R) ^ qt := by
    intro N
    have htsum_nonneg : 0 ≤ ∑' j, part N j ^ qt :=
      tsum_nonneg fun j => Real.rpow_nonneg (hpart_nonneg N j) _
    have h2 : (∑' j, part N j ^ qt) ^ (1 / qt) ≤ W * R :=
      le_trans (hpart N).2 (mul_le_mul_of_nonneg_right (hW N) hR0)
    calc
      (∑' j, part N j ^ qt)
          = ((∑' j, part N j ^ qt) ^ (1 / qt)) ^ qt :=
        (rpow_one_div_rpow htsum_nonneg hqt0.ne').symm
      _ ≤ (W * R) ^ qt :=
        Real.rpow_le_rpow (Real.rpow_nonneg htsum_nonneg _) h2 hqt0.le
  have hpartial : ∀ N : ℕ,
      (∑ j ∈ Finset.range N, c j ^ qt) ≤ (W * R) ^ qt := by
    intro N
    have hceq : ∀ j ∈ Finset.range N, c j ^ qt = part N j ^ qt := by
      intro j hj
      rw [hc_eq_part N j (le_of_lt (Finset.mem_range.mp hj))]
    rw [Finset.sum_congr rfl hceq]
    exact le_trans
      ((hpart N).1.sum_le_tsum (Finset.range N)
        (fun j _ => Real.rpow_nonneg (hpart_nonneg N j) _))
      (hWR N)
  have hc_sum : Summable (fun j => c j ^ qt) :=
    summable_of_sum_range_le
      (fun j => Real.rpow_nonneg (hc_nonneg j) _) hpartial
  have hc_tsum : (∑' j, c j ^ qt) ≤ (W * R) ^ qt :=
    Real.tsum_le_of_sum_range_le
      (fun j => Real.rpow_nonneg (hc_nonneg j) _) hpartial
  refine ⟨hc_sum, ?_⟩
  calc
    (∑' j, c j ^ qt) ≤ (W * R) ^ qt := hc_tsum
    _ = W ^ qt * R ^ qt := Real.mul_rpow hW0 hR0
    _ = W ^ qt * ∑' k, r k ^ qt := by
      rw [hR, rpow_one_div_rpow hRq_nonneg hqt0.ne']

/--
Cost transfer at `q = ∞`: a bare block family whose level coefficient powers
are dominated by `(b k)^p` with `b ≤ D` has finite abstract `(p,∞)`-cost at
most `D`.
-/
private theorem souza_abstract_cost_top_of_blockLvlCoeff_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    (B : (k : ℕ) → WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    {b : ℕ → ℝ} {D : ℝ} (_hD : 0 ≤ D)
    (hb0 : ∀ k, 0 ≤ b k) (hbD : ∀ k, b k ≤ D)
    (hroot : ∀ k, WeakGridSpace.blockLvlCoeff
      (A := souzaAtomFamily G s p hs hp hp_top) B k ≤ b k ^ p.toReal) :
    WeakGridSpace.AbstractFinitePQCost (q := (∞ : ℝ≥0∞)) B ∧
      WeakGridSpace.abstractPQCost (q := (∞ : ℝ≥0∞)) B ≤ D := by
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hroot' : ∀ k,
      (WeakGridSpace.blockLvlCoeff
        (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (1 / p.toReal) ≤ D := by
    intro k
    calc
      (WeakGridSpace.blockLvlCoeff
          (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (1 / p.toReal)
          ≤ (b k ^ p.toReal) ^ (1 / p.toReal) :=
        Real.rpow_le_rpow
          (WeakGridSpace.blockLvlCoeff_nonneg
            (A := souzaAtomFamily G s p hs hp hp_top) B k)
          (hroot k) (by positivity)
      _ = b k := rpow_rpow_one_div (hb0 k) hpt_pos.ne'
      _ ≤ D := hbD k
  constructor
  · rw [WeakGridSpace.AbstractFinitePQCost, if_pos rfl]
    exact ⟨D, by rintro x ⟨k, rfl⟩; exact hroot' k⟩
  · rw [WeakGridSpace.abstractPQCost, if_pos rfl]
    exact csSup_le (Set.range_nonempty _) (by rintro x ⟨k, rfl⟩; exact hroot' k)

/--
Cost transfer at `q ≠ ∞`: a bare block family whose level coefficient powers
are dominated by `(b k)^p` with `∑ b^q < ∞` has finite abstract `(p,q)`-cost
at most `(∑ b^q)^{1/q}`.
-/
private theorem souza_abstract_cost_finite_of_blockLvlCoeff_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hq_top : q ≠ ∞)
    (B : (k : ℕ) → WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    {b : ℕ → ℝ}
    (hb0 : ∀ k, 0 ≤ b k)
    (hbsum : Summable fun k => b k ^ q.toReal)
    (hroot : ∀ k, WeakGridSpace.blockLvlCoeff
      (A := souzaAtomFamily G s p hs hp hp_top) B k ≤ b k ^ p.toReal) :
    WeakGridSpace.AbstractFinitePQCost (q := q) B ∧
      WeakGridSpace.abstractPQCost (q := q) B ≤
        (∑' k, b k ^ q.toReal) ^ (1 / q.toReal) := by
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hqt_pos : 0 < q.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq_top
  have hterm : ∀ k,
      (WeakGridSpace.blockLvlCoeff
        (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (q.toReal / p.toReal) ≤
        b k ^ q.toReal := by
    intro k
    calc
      (WeakGridSpace.blockLvlCoeff
          (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (q.toReal / p.toReal)
          ≤ (b k ^ p.toReal) ^ (q.toReal / p.toReal) :=
        Real.rpow_le_rpow
          (WeakGridSpace.blockLvlCoeff_nonneg
            (A := souzaAtomFamily G s p hs hp hp_top) B k)
          (hroot k) (by positivity)
      _ = b k ^ q.toReal := by
        rw [← Real.rpow_mul (hb0 k)]
        congr 1
        field_simp
  have hterm_nonneg : ∀ k,
      0 ≤ (WeakGridSpace.blockLvlCoeff
        (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (q.toReal / p.toReal) :=
    fun k => Real.rpow_nonneg
      (WeakGridSpace.blockLvlCoeff_nonneg
        (A := souzaAtomFamily G s p hs hp hp_top) B k) _
  have hsum : Summable (fun k =>
      (WeakGridSpace.blockLvlCoeff
        (A := souzaAtomFamily G s p hs hp hp_top) B k) ^ (q.toReal / p.toReal)) :=
    Summable.of_nonneg_of_le hterm_nonneg hterm hbsum
  constructor
  · rw [WeakGridSpace.AbstractFinitePQCost, if_neg hq_top]
    exact hsum
  · rw [WeakGridSpace.abstractPQCost, if_neg hq_top]
    refine Real.rpow_le_rpow (tsum_nonneg hterm_nonneg) ?_ (by positivity)
    exact hsum.tsum_le_tsum hterm hbsum

open Classical in
/--
Single-ancestor collapse for the inner coefficient sums of the `u₁` blocks:
the sum of `‖c_Q‖` over the level-`k` cells containing a fixed cell `J` of
level `j ≥ k` is at most the level-`k` coefficient `ℓ^p` root of `Rf`.
-/
private theorem ancestor_ite_coeff_sum_le_levelRoot
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    {j k : ℕ} (hkj : k ≤ j)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace j) :
    (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        if J.1 ⊆ Q.1 then ‖(Rf.block k).coeff Q‖ else 0) ≤
      (Rf.levelCoeffPower k) ^ (1 / p.toReal) := by
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  obtain ⟨Qc, hQmem, hJQ⟩ :=
    DiracApproximation.exists_ancestor G ⟨j, J.1, J.2⟩ hkj
  obtain ⟨z, hzJ⟩ := G.grid.partition_nonempty j J.1 J.2
  have hcollapse :
      (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
          if J.1 ⊆ Q.1 then ‖(Rf.block k).coeff Q‖ else 0) =
        ‖(Rf.block k).coeff ⟨Qc, hQmem⟩‖ := by
    rw [Finset.sum_eq_single (⟨Qc, hQmem⟩ :
        WeakGridSpace.LevelCell G.toWeakGridSpace k)
      (fun Q' _ hQ' => by
        by_cases hsub : J.1 ⊆ Q'.1
        · exact absurd (Subtype.ext
            (DiracApproximation.cell_eq_of_mem_of_mem G Q'.2 hQmem
              (hsub hzJ) (hJQ hzJ))) hQ'
        · rw [if_neg hsub])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [if_pos hJQ]
  rw [hcollapse]
  have hsingle :
      ‖(Rf.block k).coeff ⟨Qc, hQmem⟩‖ ^ p.toReal ≤ Rf.levelCoeffPower k :=
    Finset.single_le_sum
      (f := fun Q : WeakGridSpace.LevelCell G.toWeakGridSpace k =>
        ‖(Rf.block k).coeff Q‖ ^ p.toReal)
      (fun Q _ => Real.rpow_nonneg (norm_nonneg _) _)
      (Finset.mem_univ _)
  calc
    ‖(Rf.block k).coeff ⟨Qc, hQmem⟩‖
        = (‖(Rf.block k).coeff ⟨Qc, hQmem⟩‖ ^ p.toReal) ^ (1 / p.toReal) :=
      (rpow_rpow_one_div (norm_nonneg _) hpt_pos.ne').symm
    _ ≤ (Rf.levelCoeffPower k) ^ (1 / p.toReal) :=
      Real.rpow_le_rpow
        (Real.rpow_nonneg (norm_nonneg _) _) hsingle (by positivity)

/-!
### Pointwise atom algebra: evaluation of Souza level blocks along the tower
of cells containing a fixed point, and the truncated product identity.
-/

/--
Pointwise evaluation of a Souza level block: at a point of the cell `Q`, the
block function collapses to `coeff Q · atom Q` (all other cells of the level
are disjoint from `Q`).
-/
private theorem souza_toFunLt_eq_coeff_mul_atom
    (G : GoodGridSpace (α := α)) (s' : ℝ) (p : ℝ≥0∞)
    (hs' : 0 < s') (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {k : ℕ}
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G s' p hs' hp hp_top) k)
    {z : α} {Q : WeakGridSpace.LevelCell G.toWeakGridSpace k} (hz : z ∈ Q.1) :
    B.toFunLt (souzaAtomFamily G s' p hs' hp hp_top) z =
      B.coeff Q * (show ℂ from B.atom Q) := by
  classical
  simp only [WeakGridSpace.LevelBlock.toFunLt]
  have hother : ∀ Q' ∈ (G.toWeakGridSpace.grid.partitions k).attach, Q' ≠ Q →
      B.coeff Q' * (souzaAtomFamily G s' p hs' hp hp_top).toFunction
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q')
        (B.atom Q') z = 0 := by
    intro Q' _ hQ'Q
    have hzQ' : z ∉ Q'.1 := by
      intro hzin
      exact hQ'Q (Subtype.ext
        (DiracApproximation.cell_eq_of_mem_of_mem G Q'.2 Q.2 hzin hz))
    have hfn : (souzaAtomFamily G s' p hs' hp hp_top).toFunction
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q')
        (B.atom Q') z = 0 := by
      change Q'.1.indicator (fun _ => (show ℂ from B.atom Q')) z = 0
      exact Set.indicator_of_notMem hzQ' _
    rw [hfn, mul_zero]
  rw [Finset.sum_eq_single Q hother
    (fun h => absurd (Finset.mem_attach _ _) h)]
  have hfn : (souzaAtomFamily G s' p hs' hp hp_top).toFunction
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
      (B.atom Q) z = (show ℂ from B.atom Q) := by
    change Q.1.indicator (fun _ => (show ℂ from B.atom Q)) z = _
    exact Set.indicator_of_mem hz _
  rw [hfn]

/--
The local atom element of a canonical representation in the `(1/p, p, ∞)`
Souza family is the constant `1` on every cell (the canonical atom value is
`μ(J)^{1/p − 1/p} = 1`).
-/
private theorem souzaCanonical_atom_eq_one
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg)
    (hcanon : SouzaCanonicalRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg)
    {j : ℕ} (J : WeakGridSpace.LevelCell G.toWeakGridSpace j) :
    (show ℂ from (Rg.block j).atom J) = 1 := by
  obtain ⟨z, hz⟩ := G.grid.partition_nonempty j J.1 J.2
  have hcj := congrFun (hcanon j J) z
  have hLHS : (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top).toFunction
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace j J)
      ((Rg.block j).atom J) z = (show ℂ from (Rg.block j).atom J) := by
    change J.1.indicator (fun _ => (show ℂ from (Rg.block j).atom J)) z = _
    exact Set.indicator_of_mem hz _
  have hRHS : canonicalSouzaAtom G (p.toReal)⁻¹ p
      (goodGridCellOfLevelCell G J) z = 1 := by
    have hzc : z ∈ (goodGridCellOfLevelCell G J).cell := hz
    simp [canonicalSouzaAtom, hzc, sub_self, Real.rpow_zero]
  rw [hLHS, hRHS] at hcj
  exact hcj

open Classical in
/--
Tower collapse for level sums guarded by the ancestor condition: if `z` lies
both in the fine cell `Qlow` (level `m₂`) and in the cell `Qhigh` of level
`m₁ ≤ m₂`, then the only level-`m₁` cell containing `Qlow` is `Qhigh`.
-/
private theorem tower_ite_sum_collapse
    (G : GoodGridSpace (α := α))
    {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) {z : α}
    {Qlow : WeakGridSpace.LevelCell G.toWeakGridSpace m₂} (hzlow : z ∈ Qlow.1)
    {Qhigh : WeakGridSpace.LevelCell G.toWeakGridSpace m₁} (hzhigh : z ∈ Qhigh.1)
    (F : WeakGridSpace.LevelCell G.toWeakGridSpace m₁ → ℂ) :
    (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace m₁,
        if Qlow.1 ⊆ Q.1 then F Q else 0) = F Qhigh := by
  classical
  have hsub : Qlow.1 ⊆ Qhigh.1 := by
    rcases GoodGridCell.subset_or_disjoint_of_le
        (⟨m₁, Qhigh.1, Qhigh.2⟩ : GoodGridCell G)
        (⟨m₂, Qlow.1, Qlow.2⟩ : GoodGridCell G) h with hsub | hdis
    · exact hsub
    · exact absurd hzhigh (Set.disjoint_left.mp hdis hzlow)
  have hother : ∀ Q' : WeakGridSpace.LevelCell G.toWeakGridSpace m₁,
      Q' ∈ Finset.univ → Q' ≠ Qhigh →
        (if Qlow.1 ⊆ Q'.1 then F Q' else 0) = 0 := by
    intro Q' _ hQ'
    by_cases hss : Qlow.1 ⊆ Q'.1
    · exact absurd (Subtype.ext
        (DiracApproximation.cell_eq_of_mem_of_mem G Q'.2 Qhigh.2
          (hss hzlow) hzhigh)) hQ'
    · exact if_neg hss
  rw [Finset.sum_eq_single Qhigh hother
    (fun h' => absurd (Finset.mem_univ _) h'), if_pos hsub]

/--
Along the tower of cells containing a point, the ancestor coefficient sum is
the plain partial sum of the tower coefficients.
-/
private theorem ancestorCoeffSum_tower_eq
    (G : GoodGridSpace (α := α)) {s' : ℝ} {p' : ℝ≥0∞}
    {hs' : 0 < s'} {hp' : 1 ≤ p'} {hp'_top : p' ≠ ∞} [Fact (1 ≤ p')]
    {x : Lp ℂ p' G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s' p' hs' hp' hp'_top) x)
    {k : ℕ} (Qz : ∀ m : ℕ, WeakGridSpace.LevelCell G.toWeakGridSpace m)
    {z : α} (hQz : ∀ m, z ∈ (Qz m).1) :
    ancestorCoeffSum G R (Qz k) =
      ∑ j ∈ Finset.range (k + 1), (R.block j).coeff (Qz j) := by
  unfold ancestorCoeffSum
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact tower_ite_sum_collapse G hjk (hQz k) (hQz j) _

/--
The truncated scalar identity behind `g·f = u₁ + u₂`: for any coefficient
sequences `e`, `v`,

`(∑_{j<n} e_j)(∑_{k<n} v_k) = ∑_{j<n} e_j (∑_{k<j} v_k) +
  ∑_{k<n} v_k (∑_{j≤k} e_j)`,

splitting the double sum into the strictly-upper and lower-triangular parts.
-/
private theorem truncation_scalar_identity (e v : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n, e j) * (∑ k ∈ Finset.range n, v k) =
      (∑ j ∈ Finset.range n, e j * ∑ k ∈ Finset.range j, v k) +
        ∑ k ∈ Finset.range n, v k * ∑ j ∈ Finset.range (k + 1), e j := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hE := Finset.sum_range_succ e n
      have hV := Finset.sum_range_succ v n
      have hU1 := Finset.sum_range_succ
        (fun j => e j * ∑ k ∈ Finset.range j, v k) n
      have hU2 := Finset.sum_range_succ
        (fun k => v k * ∑ j ∈ Finset.range (k + 1), e j) n
      rw [hU1, hU2, hE, hV]
      linear_combination ih

/--
**Pointwise truncated product identity.**  At every point `z`, the product of
the level-`< n` partial sums of `Rg` and `Rf` equals the sum of the level-`< n`
partial sums of the `u₁` and `u₂` block families.  This is the atom algebra
`a_Q · b_J` of the paper's proof, organized along the tower of cells
containing `z`.
-/
private theorem mult_truncated_pointwise_identity
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (h1p : 0 < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {x xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg)
    (hRgcanon : SouzaCanonicalRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg)
    (n : ℕ) (z : α) :
    (∑ j ∈ Finset.range n,
        (Rg.block j).toFunLt (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) z) *
      (∑ k ∈ Finset.range n,
        (Rf.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) z) =
      (∑ j ∈ Finset.range n,
          (multU1Block G s p hs h1p hp hp_top Rf Rg j).toFunLt
            (souzaAtomFamily G s p hs hp hp_top) z) +
        ∑ k ∈ Finset.range n,
          (multU2Block G s p hs h1p hp hp_top Rf Rg k).toFunLt
            (souzaAtomFamily G s p hs hp hp_top) z := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  -- The tower of cells containing `z`.
  have hex : ∀ m : ℕ,
      ∃ Q : WeakGridSpace.LevelCell G.toWeakGridSpace m, z ∈ Q.1 := by
    intro m
    have hz : z ∈ ⋃ t ∈ G.grid.grid.partitions m, t := by
      rw [G.grid.grid.covering m]
      trivial
    rcases Set.mem_iUnion₂.mp hz with ⟨Qs, hQs, hzQ⟩
    exact ⟨⟨Qs, hQs⟩, hzQ⟩
  choose Qz hQz using hex
  -- Pointwise values of the four block families along the tower.
  have hg_val : ∀ j, (Rg.block j).toFunLt
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) z =
      (Rg.block j).coeff (Qz j) := by
    intro j
    rw [souza_toFunLt_eq_coeff_mul_atom G (p.toReal)⁻¹ p h1p hp hp_top
      (Rg.block j) (hQz j),
      souzaCanonical_atom_eq_one G p h1p hp hp_top Rg hRgcanon (Qz j),
      mul_one]
  have hf_val : ∀ k, (Rf.block k).toFunLt
      (souzaAtomFamily G s p hs hp hp_top) z =
      (Rf.block k).coeff (Qz k) * (show ℂ from (Rf.block k).atom (Qz k)) :=
    fun k => souza_toFunLt_eq_coeff_mul_atom G s p hs hp hp_top
      (Rf.block k) (hQz k)
  have hu2_val : ∀ k, (multU2Block G s p hs h1p hp hp_top Rf Rg k).toFunLt
      (souzaAtomFamily G s p hs hp hp_top) z =
      ((Rf.block k).coeff (Qz k) * (show ℂ from (Rf.block k).atom (Qz k))) *
        ∑ j ∈ Finset.range (k + 1), (Rg.block j).coeff (Qz j) := by
    intro k
    rw [souza_toFunLt_eq_coeff_mul_atom G s p hs hp hp_top
      (multU2Block G s p hs h1p hp hp_top Rf Rg k) (hQz k)]
    have hcoeff : (multU2Block G s p hs h1p hp hp_top Rf Rg k).coeff (Qz k) =
        (Rf.block k).coeff (Qz k) * ancestorCoeffSum G Rg (Qz k) := rfl
    have hatom : (show ℂ from
        (multU2Block G s p hs h1p hp hp_top Rf Rg k).atom (Qz k)) =
        (show ℂ from (Rf.block k).atom (Qz k)) := rfl
    rw [hcoeff, hatom, ancestorCoeffSum_tower_eq G Rg Qz hQz]
    ring
  have hu1_val : ∀ j, (multU1Block G s p hs h1p hp hp_top Rf Rg j).toFunLt
      (souzaAtomFamily G s p hs hp hp_top) z =
      (Rg.block j).coeff (Qz j) *
        ∑ k ∈ Finset.range j,
          (Rf.block k).coeff (Qz k) * (show ℂ from (Rf.block k).atom (Qz k)) := by
    intro j
    rw [souza_toFunLt_eq_coeff_mul_atom G s p hs hp hp_top
      (multU1Block G s p hs h1p hp hp_top Rf Rg j) (hQz j)]
    have hatom : (show ℂ from
        (multU1Block G s p hs h1p hp hp_top Rf Rg j).atom (Qz j)) =
        (((G.grid.μ (Qz j).1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ) := rfl
    have hcoeff : (multU1Block G s p hs h1p hp hp_top Rf Rg j).coeff (Qz j) =
        (Rg.block j).coeff (Qz j) *
          ∑ k ∈ Finset.range j,
            ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              if (Qz j).1 ⊆ Q.1 then
                (Rf.block k).coeff Q *
                  (show ℂ from (Rf.block k).atom Q) *
                  (((G.grid.μ (Qz j).1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
              else 0 := rfl
    have hinner : ∀ k ∈ Finset.range j,
        (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            if (Qz j).1 ⊆ Q.1 then
              (Rf.block k).coeff Q *
                (show ℂ from (Rf.block k).atom Q) *
                (((G.grid.μ (Qz j).1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
            else 0) =
          ((Rf.block k).coeff (Qz k) *
              (show ℂ from (Rf.block k).atom (Qz k))) *
            (((G.grid.μ (Qz j).1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ) := by
      intro k hk
      have hkj : k ≤ j := le_of_lt (Finset.mem_range.mp hk)
      exact tower_ite_sum_collapse G hkj (hQz j) (hQz k)
        (fun Q => (Rf.block k).coeff Q *
          (show ℂ from (Rf.block k).atom Q) *
          (((G.grid.μ (Qz j).1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ))
    rw [hcoeff, hatom, Finset.sum_congr rfl hinner, ← Finset.sum_mul]
    have hμpos : 0 < (G.grid.μ (Qz j).1).toReal :=
      ENNReal.toReal_pos
        (G.grid.positive_measure j (Qz j).1 (Qz j).2).ne'
        (MeasureTheory.measure_ne_top G.grid.μ (Qz j).1)
    have hcancel :
        (((G.grid.μ (Qz j).1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ) *
          (((G.grid.μ (Qz j).1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hμpos]
      norm_num
    calc
      (Rg.block j).coeff (Qz j) *
          ((∑ k ∈ Finset.range j,
              (Rf.block k).coeff (Qz k) *
                (show ℂ from (Rf.block k).atom (Qz k))) *
            (((G.grid.μ (Qz j).1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)) *
          (((G.grid.μ (Qz j).1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)
          = (Rg.block j).coeff (Qz j) *
              (∑ k ∈ Finset.range j,
                (Rf.block k).coeff (Qz k) *
                  (show ℂ from (Rf.block k).atom (Qz k))) *
              ((((G.grid.μ (Qz j).1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ) *
                (((G.grid.μ (Qz j).1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) := by
        ring
      _ = (Rg.block j).coeff (Qz j) *
            ∑ k ∈ Finset.range j,
              (Rf.block k).coeff (Qz k) *
                (show ℂ from (Rf.block k).atom (Qz k)) := by
        rw [hcancel, mul_one]
  simp only [hg_val, hf_val, hu1_val, hu2_val]
  exact truncation_scalar_identity
    (fun j => (Rg.block j).coeff (Qz j))
    (fun k => (Rf.block k).coeff (Qz k) *
      (show ℂ from (Rf.block k).atom (Qz k))) n

/-!
### Limit plumbing: representatives of partial block sums, and pointwise
products under simultaneous `L^p` limits with a varying multiplier.
-/

/--
The `L^p` representative of a finite sum of level blocks agrees a.e. with the
pointwise sum of the block functions.
-/
private theorem coeFn_finset_range_sum_toLp
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' : ℝ≥0∞} [Fact (1 ≤ p')]
    (A : WeakGridSpace.AtomFamily G' s' p' u')
    (B : (k : ℕ) → WeakGridSpace.LevelBlock A k) (n : ℕ) :
    ((∑ k ∈ Finset.range n, (B k).toLp A : Lp ℂ p' G'.measure) : α → ℂ)
      =ᵐ[G'.measure] fun z => ∑ k ∈ Finset.range n, (B k).toFunLt A z := by
  induction n with
  | zero =>
      simpa using Lp.coeFn_zero ℂ p' G'.measure
  | succ n ih =>
      rw [Finset.sum_range_succ]
      refine (Lp.coeFn_add _ _).trans ?_
      filter_upwards [ih, WeakGridSpace.LevelBlock.coeFn_toLp A (B n)]
        with z hz1 hz2
      simp only [Pi.add_apply, Finset.sum_range_succ, hz1, hz2]

/--
Pointwise-product representation under simultaneous `L^p` limits with a
varying multiplier sequence: if `mseq → xg`, `xseq → x` and `yseq → y` in
`L^p`, each `yseq n` represents the product `mseq n · xseq n` a.e., and `xg`
represents the function `g`, then `y` represents the product `g·x`.

This extends `RepresentsPointwiseProduct.of_tendsto_Lp` to a varying
multiplier by passing to three nested a.e.-convergent subsequences.
-/
private theorem representsPointwiseProduct_of_tendsto_Lp_varying
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {p' : ℝ≥0∞} [Fact (1 ≤ p')]
    {g : α → ℂ} {mseq xseq yseq : ℕ → Lp ℂ p' G'.measure}
    {xg x y : Lp ℂ p' G'.measure}
    (hgrep : ((xg : α → ℂ)) =ᵐ[G'.measure] g)
    (hm : Filter.Tendsto mseq Filter.atTop (𝓝 xg))
    (hx : Filter.Tendsto xseq Filter.atTop (𝓝 x))
    (hy : Filter.Tendsto yseq Filter.atTop (𝓝 y))
    (hprod : ∀ n, (yseq n : α → ℂ) =ᵐ[G'.measure]
      fun z => (mseq n : α → ℂ) z * (xseq n : α → ℂ) z) :
    WeakGridSpace.RepresentsPointwiseProduct (G := G') (p := p') g x y := by
  classical
  have hxm : MeasureTheory.TendstoInMeasure G'.measure (fun n => xseq n)
      Filter.atTop x := tendstoInMeasure_of_tendsto_Lp hx
  rcases hxm.exists_seq_tendsto_ae with ⟨φ, hφ_mono, hx_ae⟩
  have hm_sub : Filter.Tendsto (fun n => mseq (φ n)) Filter.atTop (𝓝 xg) :=
    hm.comp hφ_mono.tendsto_atTop
  have hmm : MeasureTheory.TendstoInMeasure G'.measure (fun n => mseq (φ n))
      Filter.atTop xg := tendstoInMeasure_of_tendsto_Lp hm_sub
  rcases hmm.exists_seq_tendsto_ae with ⟨ψ, hψ_mono, hm_ae⟩
  have hy_sub : Filter.Tendsto (fun n => yseq (φ (ψ n))) Filter.atTop (𝓝 y) :=
    hy.comp (hφ_mono.comp hψ_mono).tendsto_atTop
  have hym : MeasureTheory.TendstoInMeasure G'.measure
      (fun n => yseq (φ (ψ n))) Filter.atTop y :=
    tendstoInMeasure_of_tendsto_Lp hy_sub
  rcases hym.exists_seq_tendsto_ae with ⟨ρ, hρ_mono, hy_ae⟩
  have hprod_ae : ∀ᵐ z ∂G'.measure, ∀ n : ℕ,
      (yseq (φ (ψ (ρ n))) : α → ℂ) z =
        (mseq (φ (ψ (ρ n))) : α → ℂ) z * (xseq (φ (ψ (ρ n))) : α → ℂ) z := by
    have hsets : (⋂ n : ℕ, {z : α |
        (yseq (φ (ψ (ρ n))) : α → ℂ) z =
          (mseq (φ (ψ (ρ n))) : α → ℂ) z *
            (xseq (φ (ψ (ρ n))) : α → ℂ) z}) ∈ ae G'.measure :=
      countable_iInter_mem.mpr fun n => hprod (φ (ψ (ρ n)))
    filter_upwards [hsets] with z hz n
    exact Set.mem_iInter.mp hz n
  filter_upwards [hx_ae, hm_ae, hy_ae, hprod_ae, hgrep]
    with z hxz hmz hyz hpz hgz
  have hx_sub2 : Filter.Tendsto (fun n => (xseq (φ (ψ (ρ n))) : α → ℂ) z)
      Filter.atTop (𝓝 ((x : α → ℂ) z)) :=
    hxz.comp (hψ_mono.comp hρ_mono).tendsto_atTop
  have hm_sub2 : Filter.Tendsto (fun n => (mseq (φ (ψ (ρ n))) : α → ℂ) z)
      Filter.atTop (𝓝 ((xg : α → ℂ) z)) :=
    hmz.comp hρ_mono.tendsto_atTop
  have hmul : Filter.Tendsto (fun n => (yseq (φ (ψ (ρ n))) : α → ℂ) z)
      Filter.atTop (𝓝 ((xg : α → ℂ) z * (x : α → ℂ) z)) := by
    refine (hm_sub2.mul hx_sub2).congr ?_
    intro n
    exact (hpz n).symm
  have huniq : (y : α → ℂ) z = (xg : α → ℂ) z * (x : α → ℂ) z :=
    tendsto_nhds_unique hyz hmul
  rw [huniq, hgz]

/--
**The `u₁ + u₂` construction, block form.**

Given a finite-cost representation `R_f` of `x` and a canonical-atom
representation `R_g` of `g` with bounded ancestor-tower sums, the block
families `multU1Block`/`multU2Block` converge in `L^p` to functions
`u₁`, `u₂` carrying representations `R1`, `R2` with those exact blocks,
finite `(p,q)` cost and

`pqCost R1 ≤ Cconv · pqCost_{(p,∞)} R_g · pqCost_{(p,q)} R_f`,
`pqCost R2 ≤ M · pqCost_{(p,q)} R_f`,

and `u₁ + u₂` represents the pointwise product `g·f`.  Here
`Cconv = λ₂^{1/p−s} / (1 − λ₂^{1/p−s})` is the sum of the geometric series
`∑_{n≥1} λ₂^{n(1/p−s)}`.  Exposing the blocks themselves lets the positive
version (Remark `pos3`) reuse this construction verbatim, since positivity
of `R_f` and `R_g` is inherited by the `u₁`/`u₂` blocks.

Proof outline (the body of the paper's proof of Proposition `mult`): the
split `a_Q · b_J = a_Q` for `Q ⊆ J` and
`a_Q · b_J = (value of a_Q) · μ(J)^{1/p−s} · a_J` for `J ⊊ Q` is realized by
the block families `multU2Block` and `multU1Block`.  The `u₁` family obeys
the levelwise convolution bound `root(u₁)_j ≤ K ∑_{k<j} λ₂^{(j−k)(1/p−s)}
root(R_f)_k` (single-ancestor counting), whose `(p,q)`-cost is controlled by
the discrete Young inequality `geometric_conv_rpow_summable_and_tsum_le`;
the `u₂` family obeys the tower-sum `L^∞` bound.  Both families converge in
`L^p` by `formalBlockSeq_hasRepresentation`, and the identity
`g·f = u₁ + u₂` follows from the exact pointwise identity of truncations
`mult_truncated_pointwise_identity` passed to the `L^p` limit along
a.e.-convergent subsequences (`representsPointwiseProduct_of_tendsto_Lp_varying`).
-/
private theorem exists_mult_product_blocks
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cconv : ℝ,
      0 ≤ Cconv ∧
      ∀ (g : α → ℂ) (M : ℝ) (_hM : 0 ≤ M)
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
        ∃ (y1Lp y2Lp : Lp ℂ p G.toWeakGridSpace.measure)
          (R1 : WeakGridSpace.LpGridRepresentation
            (souzaAtomFamily G s p hs hp hp_top) y1Lp)
          (R2 : WeakGridSpace.LpGridRepresentation
            (souzaAtomFamily G s p hs hp hp_top) y2Lp),
          R1.block = (fun j => multU1Block G s p hs h1p hp hp_top Rf Rg j) ∧
          R2.block = (fun k => multU2Block G s p hs h1p hp hp_top Rf Rg k) ∧
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R1 ∧
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R2 ∧
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) R1 ≤
            Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf ∧
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) R2 ≤
            M * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf ∧
          WeakGridSpace.RepresentsPointwiseProduct
            (G := G.toWeakGridSpace) (p := p) g
            (x : Lp ℂ p G.toWeakGridSpace.measure) (y1Lp + y2Lp) := by
  classical
  haveI : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  haveI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hθ : 0 < (p.toReal)⁻¹ - s := sub_pos.mpr hs_lt_inv
  have hlam_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  have hlam_lt : G.grid.lambda2 < 1 := G.grid.hlambda2_lt_one
  set a : ℝ := G.grid.lambda2 ^ ((p.toReal)⁻¹ - s) with hadef
  have ha0 : 0 ≤ a := Real.rpow_nonneg hlam_pos.le _
  have ha1 : a < 1 := Real.rpow_lt_one hlam_pos.le hlam_lt hθ
  have hCconv0 : 0 ≤ a / (1 - a) := div_nonneg ha0 (by linarith)
  -- Partial sums of the geometric kernel are bounded by `a/(1−a)`.
  have hW : ∀ N : ℕ, (∑ n ∈ Finset.range N, a ^ (n + 1)) ≤ a / (1 - a) := by
    intro N
    have hgeom : (∑ n ∈ Finset.range N, a ^ n) ≤ (1 - a)⁻¹ := by
      have hsum := summable_geometric_of_lt_one ha0 ha1
      have hle := hsum.sum_le_tsum (Finset.range N)
        (fun i _ => pow_nonneg ha0 i)
      rwa [tsum_geometric_of_lt_one ha0 ha1] at hle
    calc
      (∑ n ∈ Finset.range N, a ^ (n + 1))
          = a * ∑ n ∈ Finset.range N, a ^ n := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ a * (1 - a)⁻¹ := mul_le_mul_of_nonneg_left hgeom ha0
      _ = a / (1 - a) := by rw [div_eq_mul_inv]
  have hkernel : ∀ j : ℕ,
      (∑ k ∈ Finset.range j, a ^ (j - k)) ≤ a / (1 - a) := by
    intro j
    have hreflect : (∑ k ∈ Finset.range j, a ^ (j - k)) =
        ∑ n ∈ Finset.range j, a ^ (n + 1) := by
      rw [← Finset.sum_range_reflect (fun k => a ^ (j - k)) j]
      refine Finset.sum_congr rfl ?_
      intro n hn
      have h1 : j - (j - 1 - n) = n + 1 := by
        have := Finset.mem_range.mp hn
        omega
      rw [h1]
    rw [hreflect]
    exact hW j
  refine ⟨a / (1 - a), hCconv0, ?_⟩
  intro g M hM xg Rg x Rf hgrep hgM hRgcanon hRgfin htower hRffin
  -- Level roots and reference costs.
  have hlvlRf_nonneg : ∀ k, 0 ≤ Rf.levelCoeffPower k := fun k =>
    Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
  have hlvlRg_nonneg : ∀ j, 0 ≤ Rg.levelCoeffPower j := fun j =>
    Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
  set r : ℕ → ℝ := fun k => (Rf.levelCoeffPower k) ^ (1 / p.toReal) with hrdef
  have hr0 : ∀ k, 0 ≤ r k := fun k => Real.rpow_nonneg (hlvlRf_nonneg k) _
  set K : ℝ := WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg with hKdef
  have hK0 : 0 ≤ K := WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rg
  have hrootRg : ∀ j, (Rg.levelCoeffPower j) ^ (1 / p.toReal) ≤ K := fun j =>
    WeakGridSpace.AtomFamily.levelCoeffRoot_le_pqCost
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) Rg hRgfin j
  set RfCost : ℝ := WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf
    with hRfCdef
  have hRfC0 : 0 ≤ RfCost := WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rf
  have hrootRf : ∀ k, r k ≤ RfCost := fun k =>
    WeakGridSpace.AtomFamily.levelCoeffRoot_le_pqCost
      (souzaAtomFamily G s p hs hp hp_top) Rf hRffin k
  -- The `r^q` summability package for `q ≠ ∞`.
  have hr_pow_eq : ∀ (_ : q ≠ ∞),
      (fun k => r k ^ q.toReal) =
        fun k => (Rf.levelCoeffPower k) ^ (q.toReal / p.toReal) := by
    intro _
    funext k
    simp only [hrdef]
    rw [← Real.rpow_mul (hlvlRf_nonneg k), one_div, inv_mul_eq_div]
  have hr_sum : ∀ (_ : q ≠ ∞), Summable (fun k => r k ^ q.toReal) := by
    intro hq_top
    rw [hr_pow_eq hq_top]
    have h := hRffin
    rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hq_top] at h
    exact h
  have hr_tsum_root : ∀ (hq_top : q ≠ ∞),
      (∑' k, r k ^ q.toReal) ^ (1 / q.toReal) = RfCost := by
    intro hq_top
    rw [hr_pow_eq hq_top, hRfCdef,
      WeakGridSpace.LpGridRepresentation.pqCost, if_neg hq_top]
  -- ## The `u₂` piece: levelwise bound and cost.
  have hU2lvl : ∀ k, WeakGridSpace.blockLvlCoeff
      (A := souzaAtomFamily G s p hs hp hp_top)
      (fun k => multU2Block G s p hs h1p hp hp_top Rf Rg k) k ≤
      (M * r k) ^ p.toReal := by
    intro k
    have h1 := multU2Block_levelCoeffPower_le G s p hs h1p hp hp_top Rf Rg
      hM htower k
    have h2 : (M * r k) ^ p.toReal = M ^ p.toReal * Rf.levelCoeffPower k := by
      rw [Real.mul_rpow hM (hr0 k)]
      congr 1
      simp only [hrdef]
      exact rpow_one_div_rpow (hlvlRf_nonneg k) hpt_pos.ne'
    rw [h2]
    exact h1
  have hU2pair : WeakGridSpace.AbstractFinitePQCost (q := q)
      (fun k => multU2Block G s p hs h1p hp hp_top Rf Rg k) ∧
      WeakGridSpace.abstractPQCost (q := q)
        (fun k => multU2Block G s p hs h1p hp hp_top Rf Rg k) ≤ M * RfCost := by
    by_cases hq_top : q = ∞
    · subst hq_top
      exact souza_abstract_cost_top_of_blockLvlCoeff_le G s p hs hp hp_top _
        (mul_nonneg hM hRfC0) (fun k => mul_nonneg hM (hr0 k))
        (fun k => mul_le_mul_of_nonneg_left (hrootRf k) hM) hU2lvl
    · have hqt1 : 1 ≤ q.toReal := by
        have h := ENNReal.toReal_mono hq_top (Fact.out : (1 : ℝ≥0∞) ≤ q)
        simpa using h
      have hqt_pos : 0 < q.toReal := lt_of_lt_of_le zero_lt_one hqt1
      have hMr_sum : Summable (fun k => (M * r k) ^ q.toReal) := by
        have heq : (fun k => (M * r k) ^ q.toReal) =
            fun k => M ^ q.toReal * r k ^ q.toReal := by
          funext k
          exact Real.mul_rpow hM (hr0 k)
        rw [heq]
        exact (hr_sum hq_top).mul_left _
      obtain ⟨h1, h2⟩ := souza_abstract_cost_finite_of_blockLvlCoeff_le
        G s p q hs hp hp_top hq_top _ (fun k => mul_nonneg hM (hr0 k))
        hMr_sum hU2lvl
      refine ⟨h1, le_trans h2 ?_⟩
      have htsum_eq : (∑' k, (M * r k) ^ q.toReal) =
          M ^ q.toReal * ∑' k, r k ^ q.toReal := by
        rw [← tsum_mul_left]
        exact tsum_congr fun k => Real.mul_rpow hM (hr0 k)
      rw [htsum_eq, Real.mul_rpow (Real.rpow_nonneg hM _)
        (tsum_nonneg fun k => Real.rpow_nonneg (hr0 k) _),
        rpow_rpow_one_div hM hqt_pos.ne', hr_tsum_root hq_top]
  -- ## The `u₁` piece: levelwise convolution bound and cost.
  have hU1lvl : ∀ j, WeakGridSpace.blockLvlCoeff
      (A := souzaAtomFamily G s p hs hp hp_top)
      (fun j => multU1Block G s p hs h1p hp hp_top Rf Rg j) j ≤
      (K * ∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ p.toReal := by
    intro j
    have hc0 : 0 ≤ ∑ k ∈ Finset.range j, a ^ (j - k) * r k :=
      Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg ha0 _) (hr0 k)
    have hcoeffJ : ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
        ‖(multU1Block G s p hs h1p hp hp_top Rf Rg j).coeff J‖ ≤
          ‖(Rg.block j).coeff J‖ *
            ∑ k ∈ Finset.range j, a ^ (j - k) * r k := by
      intro J
      refine (multU1Block_coeff_norm_le G s p hs hs_lt_inv h1p hp hp_top
        Rf Rg j J).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine Finset.sum_le_sum ?_
      intro k hk
      have hkj : k ≤ j := le_of_lt (Finset.mem_range.mp hk)
      have hpow : (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) =
          a ^ (j - k) := by
        rw [← Real.rpow_natCast G.grid.lambda2 (j - k),
          ← Real.rpow_mul hlam_pos.le,
          mul_comm ((j - k : ℕ) : ℝ) ((p.toReal)⁻¹ - s),
          Real.rpow_mul hlam_pos.le, Real.rpow_natCast, ← hadef]
      rw [hpow]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ha0 _)
      simp only [hrdef]
      exact ancestor_ite_coeff_sum_le_levelRoot G s p hs hp hp_top Rf hkj J
    show (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
        ‖(multU1Block G s p hs h1p hp hp_top Rf Rg j).coeff J‖ ^ p.toReal) ≤
      (K * ∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ p.toReal
    calc
      (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
          ‖(multU1Block G s p hs h1p hp hp_top Rf Rg j).coeff J‖ ^ p.toReal)
          ≤ ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
              (‖(Rg.block j).coeff J‖ *
                ∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ p.toReal :=
        Finset.sum_le_sum fun J _ =>
          Real.rpow_le_rpow (norm_nonneg _) (hcoeffJ J) hpt_pos.le
      _ = ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            ‖(Rg.block j).coeff J‖ ^ p.toReal *
              (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ p.toReal :=
        Finset.sum_congr rfl fun J _ => Real.mul_rpow (norm_nonneg _) hc0
      _ = Rg.levelCoeffPower j *
            (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ p.toReal := by
        rw [← Finset.sum_mul]
        rfl
      _ ≤ K ^ p.toReal *
            (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ p.toReal := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hc0 _)
        calc
          Rg.levelCoeffPower j
              = ((Rg.levelCoeffPower j) ^ (1 / p.toReal)) ^ p.toReal :=
            (rpow_one_div_rpow (hlvlRg_nonneg j) hpt_pos.ne').symm
          _ ≤ K ^ p.toReal :=
            Real.rpow_le_rpow
              (Real.rpow_nonneg (hlvlRg_nonneg j) _) (hrootRg j) hpt_pos.le
      _ = (K * ∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ p.toReal :=
        (Real.mul_rpow hK0 hc0).symm
  have hU1pair : WeakGridSpace.AbstractFinitePQCost (q := q)
      (fun j => multU1Block G s p hs h1p hp hp_top Rf Rg j) ∧
      WeakGridSpace.abstractPQCost (q := q)
        (fun j => multU1Block G s p hs h1p hp hp_top Rf Rg j) ≤
        a / (1 - a) * K * RfCost := by
    have hc0 : ∀ j, 0 ≤ ∑ k ∈ Finset.range j, a ^ (j - k) * r k := fun j =>
      Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg ha0 _) (hr0 k)
    have hb0 : ∀ j, 0 ≤ K * ∑ k ∈ Finset.range j, a ^ (j - k) * r k :=
      fun j => mul_nonneg hK0 (hc0 j)
    by_cases hq_top : q = ∞
    · subst hq_top
      refine souza_abstract_cost_top_of_blockLvlCoeff_le G s p hs hp hp_top _
        (by positivity) hb0 ?_ hU1lvl
      intro j
      have hcj : (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ≤
          a / (1 - a) * RfCost := by
        calc
          (∑ k ∈ Finset.range j, a ^ (j - k) * r k)
              ≤ ∑ k ∈ Finset.range j, a ^ (j - k) * RfCost :=
            Finset.sum_le_sum fun k _ =>
              mul_le_mul_of_nonneg_left (hrootRf k) (pow_nonneg ha0 _)
          _ = (∑ k ∈ Finset.range j, a ^ (j - k)) * RfCost := by
            rw [Finset.sum_mul]
          _ ≤ a / (1 - a) * RfCost :=
            mul_le_mul_of_nonneg_right (hkernel j) hRfC0
      calc
        K * ∑ k ∈ Finset.range j, a ^ (j - k) * r k
            ≤ K * (a / (1 - a) * RfCost) :=
          mul_le_mul_of_nonneg_left hcj hK0
        _ = a / (1 - a) * K * RfCost := by ring
    · have hqt1 : 1 ≤ q.toReal := by
        have h := ENNReal.toReal_mono hq_top (Fact.out : (1 : ℝ≥0∞) ≤ q)
        simpa using h
      have hqt_pos : 0 < q.toReal := lt_of_lt_of_le zero_lt_one hqt1
      obtain ⟨hcsum, hctsum⟩ := geometric_conv_rpow_summable_and_tsum_le
        hqt1 ha0 hr0 (hr_sum hq_top) hW
      have hKc_sum : Summable (fun j =>
          (K * ∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ q.toReal) := by
        have heq : (fun j =>
            (K * ∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ q.toReal) =
            fun j => K ^ q.toReal *
              (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ q.toReal := by
          funext j
          exact Real.mul_rpow hK0 (hc0 j)
        rw [heq]
        exact hcsum.mul_left _
      obtain ⟨h1, h2⟩ := souza_abstract_cost_finite_of_blockLvlCoeff_le
        G s p q hs hp hp_top hq_top _ hb0 hKc_sum hU1lvl
      refine ⟨h1, le_trans h2 ?_⟩
      have htsum_eq : (∑' j,
          (K * ∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ q.toReal) =
          K ^ q.toReal *
            ∑' j, (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ q.toReal := by
        rw [← tsum_mul_left]
        exact tsum_congr fun j => Real.mul_rpow hK0 (hc0 j)
      have hconv_nonneg : 0 ≤
          ∑' j, (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ q.toReal :=
        tsum_nonneg fun j => Real.rpow_nonneg (hc0 j) _
      rw [htsum_eq, Real.mul_rpow (Real.rpow_nonneg hK0 _) hconv_nonneg,
        rpow_rpow_one_div hK0 hqt_pos.ne']
      have hbound : (∑' j,
          (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ q.toReal) ^
            (1 / q.toReal) ≤ a / (1 - a) * RfCost := by
        have hr_tsum_nonneg : 0 ≤ ∑' k, r k ^ q.toReal :=
          tsum_nonneg fun k => Real.rpow_nonneg (hr0 k) _
        calc
          (∑' j, (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ q.toReal) ^
              (1 / q.toReal)
              ≤ ((a / (1 - a)) ^ q.toReal * ∑' k, r k ^ q.toReal) ^
                  (1 / q.toReal) :=
            Real.rpow_le_rpow hconv_nonneg hctsum (by positivity)
          _ = a / (1 - a) * (∑' k, r k ^ q.toReal) ^ (1 / q.toReal) := by
            rw [Real.mul_rpow (Real.rpow_nonneg hCconv0 _) hr_tsum_nonneg,
              rpow_rpow_one_div hCconv0 hqt_pos.ne']
          _ = a / (1 - a) * RfCost := by rw [hr_tsum_root hq_top]
      calc
        K * (∑' j,
            (∑ k ∈ Finset.range j, a ^ (j - k) * r k) ^ q.toReal) ^
              (1 / q.toReal)
            ≤ K * (a / (1 - a) * RfCost) :=
          mul_le_mul_of_nonneg_left hbound hK0
        _ = a / (1 - a) * K * RfCost := by ring
  -- ## Build the two Besov pieces from the block families.
  have hG2 := souza_assumptionG2 G s p q hs hp hp_top
  obtain ⟨y1Lp, hy1ne⟩ := WeakGridSpace.formalBlockSeq_hasRepresentation
    hG2 hp_top hs le_top
    (fun j => multU1Block G s p hs h1p hp hp_top Rf Rg j) hU1pair.1
  obtain ⟨⟨R1, hR1block⟩⟩ := hy1ne
  obtain ⟨y2Lp, hy2ne⟩ := WeakGridSpace.formalBlockSeq_hasRepresentation
    hG2 hp_top hs le_top
    (fun k => multU2Block G s p hs h1p hp hp_top Rf Rg k) hU2pair.1
  obtain ⟨⟨R2, hR2block⟩⟩ := hy2ne
  have hR1fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R1 := by
    simpa [WeakGridSpace.AbstractFinitePQCost,
      WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower, hR1block]
      using hU1pair.1
  have hR2fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R2 := by
    simpa [WeakGridSpace.AbstractFinitePQCost,
      WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower, hR2block]
      using hU2pair.1
  have hR1cost : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R1 ≤
      a / (1 - a) * K * RfCost := by
    have hlevel : ∀ k, R1.levelCoeffPower k =
        WeakGridSpace.blockLvlCoeff
          (A := souzaAtomFamily G s p hs hp hp_top)
          (fun j => multU1Block G s p hs h1p hp hp_top Rf Rg j) k := by
      intro k
      simp [WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        WeakGridSpace.blockLvlCoeff, hR1block]
    have heq : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R1 =
        WeakGridSpace.abstractPQCost (q := q)
          (fun j => multU1Block G s p hs h1p hp hp_top Rf Rg j) := by
      simp [WeakGridSpace.LpGridRepresentation.pqCost,
        WeakGridSpace.abstractPQCost, hlevel]
    rw [heq]
    exact hU1pair.2
  have hR2cost : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R2 ≤
      M * RfCost := by
    have hlevel : ∀ k, R2.levelCoeffPower k =
        WeakGridSpace.blockLvlCoeff
          (A := souzaAtomFamily G s p hs hp hp_top)
          (fun k => multU2Block G s p hs h1p hp hp_top Rf Rg k) k := by
      intro k
      simp [WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        WeakGridSpace.blockLvlCoeff, hR2block]
    have heq : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R2 =
        WeakGridSpace.abstractPQCost (q := q)
          (fun k => multU2Block G s p hs h1p hp hp_top Rf Rg k) := by
      simp [WeakGridSpace.LpGridRepresentation.pqCost,
        WeakGridSpace.abstractPQCost, hlevel]
    rw [heq]
    exact hU2pair.2
  refine ⟨y1Lp, y2Lp, R1, R2, hR1block, hR2block, hR1fin, hR2fin,
    hR1cost, hR2cost, ?_⟩
  · -- The product identification through truncations.
    have hm_tend : Filter.Tendsto (fun n => ∑ j ∈ Finset.range n,
        (Rg.block j).toLp (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top))
        Filter.atTop (𝓝 (xg : Lp ℂ p G.toWeakGridSpace.measure)) :=
      Rg.hasSum.tendsto_sum_nat
    have hx_tend : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n,
        (Rf.block k).toLp (souzaAtomFamily G s p hs hp hp_top))
        Filter.atTop (𝓝 (x : Lp ℂ p G.toWeakGridSpace.measure)) :=
      Rf.hasSum.tendsto_sum_nat
    have h1sum : HasSum (fun j =>
        (multU1Block G s p hs h1p hp hp_top Rf Rg j).toLp
          (souzaAtomFamily G s p hs hp hp_top)) y1Lp := by
      simpa [hR1block] using R1.hasSum
    have h2sum : HasSum (fun k =>
        (multU2Block G s p hs h1p hp hp_top Rf Rg k).toLp
          (souzaAtomFamily G s p hs hp hp_top)) y2Lp := by
      simpa [hR2block] using R2.hasSum
    have hy_tend : Filter.Tendsto (fun n =>
        (∑ j ∈ Finset.range n,
          (multU1Block G s p hs h1p hp hp_top Rf Rg j).toLp
            (souzaAtomFamily G s p hs hp hp_top)) +
          ∑ k ∈ Finset.range n,
            (multU2Block G s p hs h1p hp hp_top Rf Rg k).toLp
              (souzaAtomFamily G s p hs hp hp_top))
        Filter.atTop (𝓝 (y1Lp + y2Lp)) :=
      h1sum.tendsto_sum_nat.add h2sum.tendsto_sum_nat
    have hprodn : ∀ n,
        ((((∑ j ∈ Finset.range n,
            (multU1Block G s p hs h1p hp hp_top Rf Rg j).toLp
              (souzaAtomFamily G s p hs hp hp_top)) +
            ∑ k ∈ Finset.range n,
              (multU2Block G s p hs h1p hp hp_top Rf Rg k).toLp
                (souzaAtomFamily G s p hs hp hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
          =ᵐ[G.toWeakGridSpace.measure]
        fun z => ((∑ j ∈ Finset.range n,
            (Rg.block j).toLp (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) :
              Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z *
          ((∑ k ∈ Finset.range n,
            (Rf.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
              Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z := by
      intro n
      filter_upwards [Lp.coeFn_add
          (∑ j ∈ Finset.range n,
            (multU1Block G s p hs h1p hp hp_top Rf Rg j).toLp
              (souzaAtomFamily G s p hs hp hp_top))
          (∑ k ∈ Finset.range n,
            (multU2Block G s p hs h1p hp hp_top Rf Rg k).toLp
              (souzaAtomFamily G s p hs hp hp_top)),
        coeFn_finset_range_sum_toLp (souzaAtomFamily G s p hs hp hp_top)
          (fun j => multU1Block G s p hs h1p hp hp_top Rf Rg j) n,
        coeFn_finset_range_sum_toLp (souzaAtomFamily G s p hs hp hp_top)
          (fun k => multU2Block G s p hs h1p hp hp_top Rf Rg k) n,
        coeFn_finset_range_sum_toLp
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) Rg.block n,
        coeFn_finset_range_sum_toLp (souzaAtomFamily G s p hs hp hp_top)
          Rf.block n] with z h0 h1 h2 h3 h4
      rw [h0, Pi.add_apply, h1, h2, h3, h4]
      exact (mult_truncated_pointwise_identity G s p hs h1p hp hp_top
        Rf Rg hRgcanon n z).symm
    exact representsPointwiseProduct_of_tendsto_Lp_varying
      (G' := G.toWeakGridSpace) hgrep hm_tend hx_tend hy_tend hprodn

/--
**The `u₁ + u₂` construction.**

Given a finite-cost representation `R_f` of `x` and a canonical-atom
representation `R_g` of `g` with bounded ancestor-tower sums, the product
`g·f` has a Besov representative `y` with

`‖y‖ ≤ (Cconv · pqCost_{(p,∞)} R_g + M) · pqCost_{(p,q)} R_f`,

where `Cconv = λ₂^{1/p−s} / (1 − λ₂^{1/p−s})` is the sum of the geometric
series `∑_{n≥1} λ₂^{n(1/p−s)}`.  Wrapper around the block form
`exists_mult_product_blocks`: the two pieces are glued by the triangle
inequality for `Norm_Costpq`.
-/
theorem exists_mult_product_representation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cconv : ℝ,
      0 ≤ Cconv ∧
      ∀ (g : α → ℂ) (M : ℝ) (_hM : 0 ≤ M)
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
  obtain ⟨Cconv, hCconv0, hcore⟩ :=
    exists_mult_product_blocks G s p q hs hs_lt_inv h1p hp hp_top
  refine ⟨Cconv, hCconv0, ?_⟩
  intro g M hM xg Rg x Rf hgrep hgM hRgcanon hRgfin htower hRffin
  obtain ⟨y1Lp, y2Lp, R1, R2, _, _, hR1fin, hR2fin, hR1cost, hR2cost, hprod⟩ :=
    hcore g M hM xg Rg x Rf hgrep hgM hRgcanon hRgfin htower hRffin
  let y1 : WeakGridSpace.BesovishSpace (souzaAtomFamily G s p hs hp hp_top) q :=
    ⟨y1Lp, ⟨R1, hR1fin⟩⟩
  let y2 : WeakGridSpace.BesovishSpace (souzaAtomFamily G s p hs hp hp_top) q :=
    ⟨y2Lp, ⟨R2, hR2fin⟩⟩
  refine ⟨y1 + y2, hprod, ?_⟩
  have htriangle := WeakGridSpace.BesovishSpace.Norm_Costpq_add_le
    (A := souzaAtomFamily G s p hs hp hp_top) (q := q) hp_top
    (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations
      (souzaAtomFamily G s p hs hp hp_top) q) y1 y2
  have hy1n : WeakGridSpace.BesovishSpace.Norm_Costpq
      (souzaAtomFamily G s p hs hp hp_top) q y1 ≤
      Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg *
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf :=
    le_trans (WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost y1 R1 hR1fin)
      hR1cost
  have hy2n : WeakGridSpace.BesovishSpace.Norm_Costpq
      (souzaAtomFamily G s p hs hp hp_top) q y2 ≤
      M * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf :=
    le_trans (WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost y2 R2 hR2fin)
      hR2cost
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s p hs hp hp_top) q (y1 + y2)
        ≤ WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q y1 +
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q y2 := htriangle
    _ ≤ Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf +
        M * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf :=
      add_le_add hy1n hy2n
    _ = (Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg
          + M) *
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf := by ring

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

/-!
### Remark `pos3`: the positive version of Pointwise Multipliers II

Replacing `B^a_{p,b}` by the positive cones `B^{a+}_{p,b}` everywhere: if `g`
and `f` carry positive Souza representations, the `u₁`/`u₂` block families
inherit positivity, so the product `g·f` carries a positive representation
with the same cost bound.  The ancestor-tower bound `≤ |g|_∞` required by the
`u₂` estimate is *derived* from positivity (the partial tower sums are
nondecreasing and converge a.e. to `g`), which is the positive form of
Proposition `boup`.B.
-/

/-- A set of nonzero measure meets every full-measure event. -/
private theorem exists_mem_of_ae_of_measure_ne_zero
    {μ : MeasureTheory.Measure α} {S : Set α} {P : α → Prop}
    (hS : μ S ≠ 0) (hP : ∀ᵐ z ∂μ, P z) : ∃ z ∈ S, P z := by
  have hnull : μ {z | ¬ P z} = 0 := (MeasureTheory.ae_iff).mp hP
  have hdiff : μ (S \ {z | P z}) = 0 :=
    MeasureTheory.measure_mono_null (fun z hz => hz.2) hnull
  have hinter : μ (S ∩ {z | P z}) ≠ 0 := by
    intro h0
    have hcover : S ⊆ (S ∩ {z | P z}) ∪ (S \ {z | P z}) := by
      intro z hz
      by_cases h : P z
      · exact Set.mem_union_left _ ⟨hz, h⟩
      · exact Set.mem_union_right _ ⟨hz, h⟩
    have hle : μ S ≤ μ (S ∩ {z | P z}) + μ (S \ {z | P z}) :=
      (measure_mono hcover).trans (measure_union_le _ _)
    rw [h0, hdiff, add_zero] at hle
    exact hS (le_antisymm hle bot_le)
  obtain ⟨z, hz⟩ := MeasureTheory.nonempty_of_measure_ne_zero hinter
  exact ⟨z, hz.1, hz.2⟩

/-- Positive Souza representations are in particular canonical. -/
private theorem souzaPositiveRepresentation_canonical
    (G : GoodGridSpace (α := α)) (s' : ℝ) (p : ℝ≥0∞)
    (hs' : 0 < s') (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s' p hs' hp hp_top) x}
    (hR : SouzaPositiveRepresentation G s' p hs' hp hp_top R) :
    SouzaCanonicalRepresentation G s' p hs' hp hp_top R := by
  intro k Q
  obtain ⟨c, _, _, hatom⟩ := hR k Q
  exact hatom

/--
The local atom element of a canonical Souza level block is the constant
`μ(Q)^{s−1/p}` (the value of the canonical Souza atom on its cell).
-/
private theorem souzaCanonical_atom_value
    (G : GoodGridSpace (α := α)) (s' : ℝ) (p : ℝ≥0∞)
    (hs' : 0 < s') (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {k : ℕ}
    {B : WeakGridSpace.LevelBlock (souzaAtomFamily G s' p hs' hp hp_top) k}
    {Q : WeakGridSpace.LevelCell G.toWeakGridSpace k}
    (hatom : (souzaAtomFamily G s' p hs' hp hp_top).toFunction
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
        (B.atom Q) =
      canonicalSouzaAtom G s' p (goodGridCellOfLevelCell G Q)) :
    (show ℂ from B.atom Q) =
      (((G.grid.μ Q.1).toReal ^ (s' - (p.toReal)⁻¹) : ℝ) : ℂ) := by
  obtain ⟨z, hz⟩ := G.grid.partition_nonempty k Q.1 Q.2
  have hcj := congrFun hatom z
  have hLHS : (souzaAtomFamily G s' p hs' hp hp_top).toFunction
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
      (B.atom Q) z = (show ℂ from B.atom Q) := by
    change Q.1.indicator (fun _ => (show ℂ from B.atom Q)) z = _
    exact Set.indicator_of_mem hz _
  have hRHS : canonicalSouzaAtom G s' p (goodGridCellOfLevelCell G Q) z =
      (((G.grid.μ Q.1).toReal ^ (s' - (p.toReal)⁻¹) : ℝ) : ℂ) := by
    have hzc : z ∈ (goodGridCellOfLevelCell G Q).cell := hz
    simp only [canonicalSouzaAtom, dif_pos hzc]
    rfl
  rw [hLHS, hRHS] at hcj
  exact hcj

/--
The ancestor coefficient sum of a positive representation is (the complex
cast of) a nonnegative real.
-/
private theorem ancestorCoeffSum_exists_nonneg_real
    (G : GoodGridSpace (α := α)) {s' : ℝ} {p' : ℝ≥0∞}
    {hs' : 0 < s'} {hp' : 1 ≤ p'} {hp'_top : p' ≠ ∞} [Fact (1 ≤ p')]
    {x : Lp ℂ p' G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s' p' hs' hp' hp'_top) x}
    (hR : SouzaPositiveRepresentation G s' p' hs' hp' hp'_top R)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    ∃ t : ℝ, 0 ≤ t ∧ ancestorCoeffSum G R Q = (t : ℂ) := by
  classical
  choose cR hcR0 hcoeff _hatom using fun (j : ℕ)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace j) => hR j J
  refine ⟨∑ j ∈ Finset.range (k + 1),
    ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      if Q.1 ⊆ J.1 then cR j J else 0, ?_, ?_⟩
  · refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun J _ => ?_
    by_cases h : Q.1 ⊆ J.1
    · rw [if_pos h]
      exact hcR0 j J
    · rw [if_neg h]
  · unfold ancestorCoeffSum
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    by_cases h : Q.1 ⊆ J.1
    · rw [if_pos h, if_pos h]
      exact hcoeff j J
    · rw [if_neg h, if_neg h, Complex.ofReal_zero]

/-- The `u₂` blocks of positive representations are positive. -/
private theorem multU2Block_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x xg : Lp ℂ p G.toWeakGridSpace.measure}
    {Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x}
    {Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg}
    (hRfpos : SouzaPositiveRepresentation G s p hs hp hp_top Rf)
    (hRgpos : SouzaPositiveRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg)
    (k : ℕ) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (multU2Block G s p hs h1p hp hp_top Rf Rg k) := by
  intro Q
  obtain ⟨c, hc0, hcoeff, hatom⟩ := hRfpos k Q
  obtain ⟨t, ht0, htsum⟩ := ancestorCoeffSum_exists_nonneg_real G hRgpos Q
  refine ⟨c * t, mul_nonneg hc0 ht0, ?_, hatom⟩
  show (Rf.block k).coeff Q * ancestorCoeffSum G Rg Q = ((c * t : ℝ) : ℂ)
  rw [hcoeff, htsum, Complex.ofReal_mul]

open Classical in
/-- The `u₁` blocks of positive representations are positive. -/
private theorem multU1Block_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x xg : Lp ℂ p G.toWeakGridSpace.measure}
    {Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x}
    {Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg}
    (hRfpos : SouzaPositiveRepresentation G s p hs hp hp_top Rf)
    (hRgpos : SouzaPositiveRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg)
    (j : ℕ) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (multU1Block G s p hs h1p hp hp_top Rf Rg j) := by
  intro J
  obtain ⟨e, he0, hecoeff, _⟩ := hRgpos j J
  choose cR hcR0 hcoeff hatomRf using fun (k : ℕ)
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) => hRfpos k Q
  refine ⟨e * ∑ k ∈ Finset.range j,
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        if J.1 ⊆ Q.1 then
          cR k Q * (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) *
            (G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s)
        else 0, ?_, ?_, ?_⟩
  · refine mul_nonneg he0 (Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun Q _ => ?_)
    by_cases h : J.1 ⊆ Q.1
    · rw [if_pos h]
      exact mul_nonneg
        (mul_nonneg (hcR0 k Q) (Real.rpow_nonneg ENNReal.toReal_nonneg _))
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    · rw [if_neg h]
  · show (Rg.block j).coeff J *
        (∑ k ∈ Finset.range j,
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            if J.1 ⊆ Q.1 then
              (Rf.block k).coeff Q *
                (show ℂ from (Rf.block k).atom Q) *
                (((G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
            else 0) = _
    rw [hecoeff, Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun Q _ => ?_
    by_cases h : J.1 ⊆ Q.1
    · rw [if_pos h, if_pos h, hcoeff k Q,
        souzaCanonical_atom_value G s p hs hp hp_top (hatomRf k Q),
        Complex.ofReal_mul, Complex.ofReal_mul]
    · rw [if_neg h, if_neg h, Complex.ofReal_zero]
  · show (souzaAtomFamily G s p hs hp hp_top).toFunction
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace j J)
        ((multU1Block G s p hs h1p hp hp_top Rf Rg j).atom J) =
      canonicalSouzaAtom G s p (goodGridCellOfLevelCell G J)
    simpa [fouCanonicalLocalAtom, goodGridCellOfLevelCell] using
      fouCanonicalLocalAtom_toFunction G s p hs hp hp_top
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace j J)

open Classical in
/--
**Proposition `boup`.B, positive form.**  The ancestor-tower coefficient sums
of a positive representation of an essentially bounded function are bounded
by the essential bound: along the tower of cells containing a point, the
partial sums of the (nonnegative) tower coefficients are nondecreasing and a
subsequence converges a.e. to the value of the represented function, which is
at most `M` in modulus.
-/
private theorem ancestorCoeffSum_norm_le_essBound_of_positive
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : α → ℂ} {M : ℝ}
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    {Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg}
    (hRgpos : SouzaPositiveRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg)
    (hgrep : (xg : α → ℂ) =ᵐ[G.toWeakGridSpace.measure] g)
    (hgM : ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M)
    (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    ‖ancestorCoeffSum G Rg Q‖ ≤ M := by
  classical
  choose cR hcR0 hcoeff hatomRg using fun (j : ℕ)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace j) => hRgpos j J
  have hcanon : SouzaCanonicalRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg :=
    fun j J => hatomRg j J
  -- A subsequence of the `L^p` partial sums converges a.e. to `xg`.
  have hmeas := tendstoInMeasure_of_tendsto_Lp
    (Rg.hasSum.tendsto_sum_nat :
      Filter.Tendsto (fun n => ∑ j ∈ Finset.range n,
        (Rg.block j).toLp (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top))
      Filter.atTop (𝓝 xg))
  rcases hmeas.exists_seq_tendsto_ae with ⟨φ, hφ, h_ae⟩
  -- The pointwise representatives of all partial sums, simultaneously.
  have hcoe_all : ∀ᵐ z ∂G.toWeakGridSpace.measure, ∀ n : ℕ,
      ((∑ j ∈ Finset.range n, (Rg.block j).toLp
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z =
        ∑ j ∈ Finset.range n, (Rg.block j).toFunLt
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) z := by
    have hsets : (⋂ n : ℕ, {z : α |
        ((∑ j ∈ Finset.range n, (Rg.block j).toLp
            (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) :
          Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z =
          ∑ j ∈ Finset.range n, (Rg.block j).toFunLt
            (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) z}) ∈
        ae G.toWeakGridSpace.measure :=
      countable_iInter_mem.mpr fun n =>
        coeFn_finset_range_sum_toLp
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) Rg.block n
    filter_upwards [hsets] with z hz n
    exact Set.mem_iInter.mp hz n
  -- The full-measure good set.
  have hgood : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      (Filter.Tendsto (fun i =>
          ((∑ j ∈ Finset.range (φ i), (Rg.block j).toLp
              (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) :
            Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z)
        Filter.atTop (𝓝 ((xg : α → ℂ) z))) ∧
      (∀ n : ℕ,
        ((∑ j ∈ Finset.range n, (Rg.block j).toLp
            (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) :
          Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z =
          ∑ j ∈ Finset.range n, (Rg.block j).toFunLt
            (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) z) ∧
      (xg : α → ℂ) z = g z ∧ ‖g z‖ ≤ M := by
    filter_upwards [h_ae, hcoe_all, hgrep, hgM] with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  -- Extract a point of `Q` in the good set.
  have hμQ_pos : 0 < G.grid.μ Q.1 := G.grid.positive_measure k Q.1 Q.2
  obtain ⟨z, hzQ, hzP⟩ :=
    exists_mem_of_ae_of_measure_ne_zero
      (μ := G.toWeakGridSpace.measure) (S := Q.1) hμQ_pos.ne' hgood
  obtain ⟨htendz, hcoez, hxgz, hgz⟩ := hzP
  -- The tower of cells containing `z`.
  have hex : ∀ m : ℕ,
      ∃ Qm : WeakGridSpace.LevelCell G.toWeakGridSpace m, z ∈ Qm.1 := by
    intro m
    have hzm : z ∈ ⋃ t ∈ G.grid.grid.partitions m, t := by
      rw [G.grid.grid.covering m]
      trivial
    rcases Set.mem_iUnion₂.mp hzm with ⟨Qs, hQs, hzQ'⟩
    exact ⟨⟨Qs, hQs⟩, hzQ'⟩
  choose Qz hQz using hex
  have hQzk : Qz k = Q :=
    Subtype.ext (DiracApproximation.cell_eq_of_mem_of_mem G (Qz k).2 Q.2
      (hQz k) hzQ)
  -- The real partial tower sums.
  set T : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, cR j (Qz j) with hT
  have hT_mono : Monotone T := by
    apply monotone_nat_of_le_succ
    intro n
    simp only [hT, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hcR0 n (Qz n))
  have hval : ∀ n : ℕ,
      ((∑ j ∈ Finset.range n, (Rg.block j).toLp
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z = ((T n : ℝ) : ℂ) := by
    intro n
    rw [hcoez n]
    have hterm : ∀ j ∈ Finset.range n,
        (Rg.block j).toFunLt
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) z =
          ((cR j (Qz j) : ℝ) : ℂ) := by
      intro j _
      rw [souza_toFunLt_eq_coeff_mul_atom G (p.toReal)⁻¹ p h1p hp hp_top
        (Rg.block j) (hQz j),
        souzaCanonical_atom_eq_one G p h1p hp hp_top Rg hcanon (Qz j),
        mul_one]
      exact hcoeff j (Qz j)
    rw [Finset.sum_congr rfl hterm, hT]
    exact (Complex.ofReal_sum _ _).symm
  -- The real limit along the subsequence.
  have htendT : Filter.Tendsto (fun i => T (φ i)) Filter.atTop
      (𝓝 (((xg : α → ℂ) z).re)) := by
    have h1 : Filter.Tendsto (fun i => ((T (φ i) : ℝ) : ℂ)) Filter.atTop
        (𝓝 ((xg : α → ℂ) z)) := by
      refine htendz.congr ?_
      intro i
      exact hval (φ i)
    have h2 := (Complex.continuous_re.tendsto _).comp h1
    simpa using h2
  -- Monotone comparison with the limit.
  have hTle : ∀ n, T n ≤ ((xg : α → ℂ) z).re := by
    intro n
    have hsub : T (φ n) ≤ ((xg : α → ℂ) z).re :=
      Monotone.ge_of_tendsto (hT_mono.comp hφ.monotone) htendT n
    exact le_trans (hT_mono (hφ.le_apply)) hsub
  have hreM : ((xg : α → ℂ) z).re ≤ M := by
    rw [hxgz]
    exact le_trans (Complex.re_le_norm (g z)) hgz
  -- Conclude through the tower collapse.
  have hanc : ancestorCoeffSum G Rg Q = ((T (k + 1) : ℝ) : ℂ) := by
    rw [← hQzk, ancestorCoeffSum_tower_eq G Rg Qz hQz]
    have hterm : ∀ j ∈ Finset.range (k + 1),
        (Rg.block j).coeff (Qz j) = ((cR j (Qz j) : ℝ) : ℂ) :=
      fun j _ => hcoeff j (Qz j)
    rw [Finset.sum_congr rfl hterm, hT]
    exact (Complex.ofReal_sum _ _).symm
  rw [hanc, Complex.norm_real, Real.norm_of_nonneg
    (Finset.sum_nonneg fun j _ => hcR0 j (Qz j))]
  exact le_trans (hTle (k + 1)) hreM

/--
**Remark `pos3`, representation form.**  The `u₁ + u₂` construction maps the
positive cones to the positive cone: if `g` is represented by a *positive*
finite-`(p,∞)`-cost representation `R_g` with `‖g‖ ≤ M` a.e., and `x` carries
a positive finite-`(p,q)`-cost representation `R_f`, then the pointwise
product `g·f` has a representative `y` carrying a *positive* representation
`R_y` with

`pqCost R_y ≤ (Cconv · pqCost_{(p,∞)} R_g + M) · pqCost_{(p,q)} R_f`.

The canonical-atom hypothesis and the ancestor-tower bound of the
non-positive version are *derived* from positivity
(`souzaPositiveRepresentation_canonical` and
`ancestorCoeffSum_norm_le_essBound_of_positive`), and positivity of the
`u₁`/`u₂` blocks is inherited from `R_f`, `R_g`
(`multU1Block_positive`/`multU2Block_positive`); the two pieces are summed by
`souzaPositiveRepresentationAdd`.
-/
theorem exists_mult_product_representation_pos
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cconv : ℝ,
      0 ≤ Cconv ∧
      ∀ (g : α → ℂ) (M : ℝ) (_hM : 0 ≤ M)
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
        SouzaPositiveRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := ∞) Rg →
        SouzaPositiveRepresentation G s p hs hp hp_top Rf →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rf →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsPointwiseProduct
            (G := G.toWeakGridSpace) (p := p) g
            (x : Lp ℂ p G.toWeakGridSpace.measure)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          ∃ Ry : WeakGridSpace.LpGridRepresentation
              (souzaAtomFamily G s p hs hp hp_top)
              (y : Lp ℂ p G.toWeakGridSpace.measure),
            SouzaPositiveRepresentation G s p hs hp hp_top Ry ∧
            WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Ry ∧
            WeakGridSpace.LpGridRepresentation.pqCost (q := q) Ry ≤
              (Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg
                  + M) *
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf := by
  obtain ⟨Cconv, hCconv0, hcore⟩ :=
    exists_mult_product_blocks G s p q hs hs_lt_inv h1p hp hp_top
  refine ⟨Cconv, hCconv0, ?_⟩
  intro g M hM xg Rg x Rf hgrep hgM hRgpos hRgfin hRfpos hRffin
  have hRgcanon : SouzaCanonicalRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg :=
    souzaPositiveRepresentation_canonical G (p.toReal)⁻¹ p h1p hp hp_top hRgpos
  have htower : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖ancestorCoeffSum G Rg Q‖ ≤ M := fun k Q =>
    ancestorCoeffSum_norm_le_essBound_of_positive G p h1p hp hp_top
      hRgpos hgrep hgM k Q
  obtain ⟨y1Lp, y2Lp, R1, R2, hR1block, hR2block, hR1fin, hR2fin,
    hR1cost, hR2cost, hprod⟩ :=
    hcore g M hM xg Rg x Rf hgrep hgM hRgcanon hRgfin htower hRffin
  -- The two pieces are positive.
  have hR1pos : SouzaPositiveRepresentation G s p hs hp hp_top R1 := by
    intro j
    rw [show R1.block j = multU1Block G s p hs h1p hp hp_top Rf Rg j from
      congrFun hR1block j]
    exact multU1Block_positive G s p hs h1p hp hp_top hRfpos hRgpos j
  have hR2pos : SouzaPositiveRepresentation G s p hs hp hp_top R2 := by
    intro k
    rw [show R2.block k = multU2Block G s p hs h1p hp hp_top Rf Rg k from
      congrFun hR2block k]
    exact multU2Block_positive G s p hs h1p hp hp_top hRfpos hRgpos k
  -- The positive sum of the two pieces.
  have hRaddfin := souzaPositiveRepresentationAdd_finitePQCost
    G s p q hs hp hp_top hR1pos hR2pos hR1fin hR2fin
  have hRaddpos := souzaPositiveRepresentationAdd_positive
    G s p hs hp hp_top hR1pos hR2pos
  have hRaddcost : WeakGridSpace.LpGridRepresentation.pqCost (q := q)
      (souzaPositiveRepresentationAdd G s p hs hp hp_top R1 R2 hR1pos hR2pos) ≤
      (Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg + M) *
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf := by
    refine (souzaPositiveRepresentationAdd_pqCost_le
      G s p q hs hp hp_top hR1pos hR2pos hR1fin hR2fin).trans ?_
    calc
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R1 +
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) R2
          ≤ Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf +
            M * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf :=
        add_le_add hR1cost hR2cost
      _ = (Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg
            + M) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf := by ring
  exact ⟨⟨y1Lp + y2Lp,
      ⟨souzaPositiveRepresentationAdd G s p hs hp hp_top R1 R2 hR1pos hR2pos,
        hRaddfin⟩⟩,
    hprod,
    souzaPositiveRepresentationAdd G s p hs hp hp_top R1 R2 hR1pos hR2pos,
    hRaddpos, hRaddfin, hRaddcost⟩

/--
**Remark `pos3` of the paper (positive Pointwise Multipliers II).**

Replacing `B^a_{p,b}` by the positive cones `B^{a+}_{p,b}` everywhere in
Proposition `mult`: for `0 < s < 1/p`, if `g` is represented by an element
`xg` of the positive cone of the `(1/p, p, ∞)` Souza space with finite
positive gauge, and `‖g‖ ≤ M` a.e., then for every element `x` of the
positive cone of `B^s_{p,q}` with finite positive gauge the product `g·f`
has a positive Besov representative `y` with

`|y|_{B^{s+}_{p,q}} ≤ (Cmult · |xg|_{B^{1/p,+}_{p,∞}} + M) · |x|_{B^{s+}_{p,q}}`,

where the positive gauges are the `ℝ≥0∞`-valued infima of the `(p,q)`-costs
over positive representations (`souzaPositiveNorm`).
-/
theorem souzaPointwiseMultipliersIIPositive
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
        souzaPositiveNorm G (p.toReal)⁻¹ p ∞ h1p hp hp_top xg ≠ ∞ →
        ∀ x : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          souzaPositiveNorm G s p q hs hp hp_top x ≠ ∞ →
          ∃ y : WeakGridSpace.BesovishSpace
              (souzaAtomFamily G s p hs hp hp_top) q,
            WeakGridSpace.RepresentsPointwiseProduct
              (G := G.toWeakGridSpace) (p := p) g
              (x : Lp ℂ p G.toWeakGridSpace.measure)
              (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
            SouzaPositiveElement G s p q hs hp hp_top y ∧
            souzaPositiveNorm G s p q hs hp hp_top y ≤
              (ENNReal.ofReal Cmult *
                  souzaPositiveNorm G (p.toReal)⁻¹ p ∞ h1p hp hp_top xg +
                ENNReal.ofReal M) *
                souzaPositiveNorm G s p q hs hp hp_top x := by
  classical
  obtain ⟨Cconv, hCconv0, hcore⟩ :=
    exists_mult_product_representation_pos G s p q hs hs_lt_inv h1p hp hp_top
  refine ⟨Cconv, hCconv0, ?_⟩
  intro g M xg hgrep hgM hNg_ne x hNf_ne
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
  set Ng : ℝ≥0∞ := souzaPositiveNorm G (p.toReal)⁻¹ p ∞ h1p hp hp_top xg
    with hNgdef
  set Nf : ℝ≥0∞ := souzaPositiveNorm G s p q hs hp hp_top x with hNfdef
  set oC : ℝ≥0∞ := ENNReal.ofReal Cconv with hoC
  set oM : ℝ≥0∞ := ENNReal.ofReal M with hoM
  -- One run of the construction fixes the product representative.
  obtain ⟨Rg₀, hRg₀pos, hRg₀fin, _⟩ :=
    exists_souzaPositiveRepresentation_pqCostENNReal_lt
      G (p.toReal)⁻¹ p ∞ h1p hp hp_top xg hNg_ne (ε := 1) one_pos
  obtain ⟨Rf₀, hRf₀pos, hRf₀fin, _⟩ :=
    exists_souzaPositiveRepresentation_pqCostENNReal_lt
      G s p q hs hp hp_top x hNf_ne (ε := 1) one_pos
  obtain ⟨y₀, hy₀prod, Ry₀, hRy₀pos, _, _⟩ :=
    hcore g M hM0 xg Rg₀ x Rf₀ hgrep hgM hRg₀pos hRg₀fin hRf₀pos hRf₀fin
  refine ⟨y₀, hy₀prod, ⟨Ry₀, hRy₀pos⟩, ?_⟩
  -- ε-optimization in the positive gauges.
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  set D : ℝ≥0∞ := oC * Nf + (oC * Ng + oM) + oC with hD
  have hoC_ne_top : oC ≠ ∞ := ENNReal.ofReal_ne_top
  have hoM_ne_top : oM ≠ ∞ := ENNReal.ofReal_ne_top
  have hD_ne_top : D ≠ ∞ := by
    rw [hD]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top hoC_ne_top hNf_ne,
          ENNReal.add_ne_top.mpr
            ⟨ENNReal.mul_ne_top hoC_ne_top hNg_ne, hoM_ne_top⟩⟩,
        hoC_ne_top⟩
  set δ : ℝ≥0∞ := min 1 ((ε : ℝ≥0∞) / D) with hδ
  have hδ_pos : 0 < δ := by
    rw [hδ]
    refine lt_min one_pos ?_
    exact ENNReal.div_pos (by exact_mod_cast hε.ne') hD_ne_top
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_ne_top : δ ≠ ∞ := (lt_of_le_of_lt hδ_le_one ENNReal.one_lt_top).ne
  have hδD : δ * D ≤ (ε : ℝ≥0∞) := by
    by_cases hD0 : D = 0
    · simp [hD0]
    · calc
        δ * D ≤ ((ε : ℝ≥0∞) / D) * D :=
          mul_le_mul_left (min_le_right _ _) D
        _ = (ε : ℝ≥0∞) := ENNReal.div_mul_cancel hD0 hD_ne_top
  -- δ-optimal positive representations.
  obtain ⟨Rg, hRgpos, hRgfin, hRglt⟩ :=
    exists_souzaPositiveRepresentation_pqCostENNReal_lt
      G (p.toReal)⁻¹ p ∞ h1p hp hp_top xg hNg_ne hδ_pos
  obtain ⟨Rf, hRfpos, hRffin, hRflt⟩ :=
    exists_souzaPositiveRepresentation_pqCostENNReal_lt
      G s p q hs hp hp_top x hNf_ne hδ_pos
  obtain ⟨y, hyprod, Ry, hRypos, hRyfin, hRycost⟩ :=
    hcore g M hM0 xg Rg x Rf hgrep hgM hRgpos hRgfin hRfpos hRffin
  have hyy₀ : y = y₀ := by
    apply Subtype.ext
    apply Lp.ext
    exact hyprod.trans hy₀prod.symm
  -- Real cost bounds for the δ-optimal representations.
  have hNgδ_ne_top : Ng + δ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hNg_ne, hδ_ne_top⟩
  have hNfδ_ne_top : Nf + δ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hNf_ne, hδ_ne_top⟩
  have hcg : WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg ≤
      (Ng + δ).toReal := by
    refine pqCost_le_of_pqCostENNReal_le Rg ?_ ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_toReal hNgδ_ne_top]
    exact hRglt.le
  have hcf : WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf ≤
      (Nf + δ).toReal := by
    refine pqCost_le_of_pqCostENNReal_le Rf ?_ ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_toReal hNfδ_ne_top]
    exact hRflt.le
  -- The gauge of the product is bounded by the constructed positive cost.
  have hgauge : souzaPositiveNorm G s p q hs hp hp_top y ≤
      ENNReal.ofReal
        ((Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg + M) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf) := by
    refine sInf_le ⟨Ry, hRypos, hRyfin, ?_⟩
    exact pqCostENNReal_le_of_finitePQCost_pqCost_le Ry hRyfin hRycost
  -- ENNReal massage of the right-hand side.
  have hg0 : 0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg :=
    WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rg
  have hf0 : 0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf :=
    WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rf
  have hofReal : ENNReal.ofReal
      ((Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg + M) *
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf) ≤
      (oC * (Ng + δ) + oM) * (Nf + δ) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' ?_ ?_
    · rw [ENNReal.ofReal_add (by positivity) hM0, ENNReal.ofReal_mul hCconv0]
      refine add_le_add (mul_le_mul' le_rfl ?_) le_rfl
      calc
        ENNReal.ofReal (WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg)
            ≤ ENNReal.ofReal ((Ng + δ).toReal) :=
          ENNReal.ofReal_le_ofReal hcg
        _ = Ng + δ := ENNReal.ofReal_toReal hNgδ_ne_top
    · calc
        ENNReal.ofReal (WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf)
            ≤ ENNReal.ofReal ((Nf + δ).toReal) :=
          ENNReal.ofReal_le_ofReal hcf
        _ = Nf + δ := ENNReal.ofReal_toReal hNfδ_ne_top
  -- Expand and absorb the δ-error.
  have hδδ : δ * δ ≤ δ := by
    calc
      δ * δ ≤ 1 * δ := mul_le_mul_left hδ_le_one δ
      _ = δ := one_mul δ
  have hexp : (oC * (Ng + δ) + oM) * (Nf + δ) ≤
      (oC * Ng + oM) * Nf + δ * D := by
    calc
      (oC * (Ng + δ) + oM) * (Nf + δ)
          = (oC * Ng + oM) * Nf +
            (oC * δ * Nf + ((oC * Ng + oM) * δ + oC * (δ * δ))) := by
        ring
      _ ≤ (oC * Ng + oM) * Nf +
            (oC * δ * Nf + ((oC * Ng + oM) * δ + oC * δ)) := by
        gcongr
      _ = (oC * Ng + oM) * Nf + δ * D := by
        rw [hD]
        ring
  calc
    souzaPositiveNorm G s p q hs hp hp_top y₀
        = souzaPositiveNorm G s p q hs hp hp_top y := by rw [hyy₀]
    _ ≤ ENNReal.ofReal
          ((Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg
              + M) *
            WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf) := hgauge
    _ ≤ (oC * (Ng + δ) + oM) * (Nf + δ) := hofReal
    _ ≤ (oC * Ng + oM) * Nf + δ * D := hexp
    _ ≤ (oC * Ng + oM) * Nf + ε := add_le_add le_rfl hδD

end

end GoodGridSpace
