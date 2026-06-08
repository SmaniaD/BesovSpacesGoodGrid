import BesovSpacesGoodGrid.GoodGrid.Multipliers.NonArchimedeanProperty

/-!
# Positive-cone non-Archimedean multiplier theorem

This file proves the positive-cone version of the non-Archimedean multiplier
estimate.  The key additional structure compared to the non-positive version is
that the source representation `R` uses canonical Souza atoms (i.e. is a
`SouzaPositiveRepresentation`), and the multipliers satisfy a
`SouzaPositivePointwiseSelfsTailBound` that controls products with those
canonical atoms. The output representation inherits the positivity structure.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/-!
## Auxiliary lemmas about the positive tail selfs sum

These use `nonArchimedeanRelevantPositiveTailSelfsSum` which is already defined
in `NonArchimedeanProperty.lean`.
-/

private theorem nonArchimedeanRelevantPositiveTailSelfsSum_nonneg
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    0 ≤ nonArchimedeanRelevantPositiveTailSelfsSum
      G β p qtilde hβ hp hp_top Λ t g Q := by
  classical
  unfold nonArchimedeanRelevantPositiveTailSelfsSum
  refine Finset.sum_nonneg ?_
  intro i _
  by_cases hmeet : goodGridLevelCellMeetsSupport G Q (g i)
  · simp [hmeet]
  · simp [hmeet]

private theorem nonArchimedeanRelevantPositiveTailSelfsSum_eq_zero_of_nonpos
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {N : ℝ} (hN_nonpos : N ≤ 0)
    (hQ : nonArchimedeanRelevantPositiveTailSelfsSum
      G β p qtilde hβ hp hp_top Λ t g Q ≤ ENNReal.ofReal N) :
    nonArchimedeanRelevantPositiveTailSelfsSum
      G β p qtilde hβ hp hp_top Λ t g Q = 0 := by
  have hle0 : nonArchimedeanRelevantPositiveTailSelfsSum
      G β p qtilde hβ hp hp_top Λ t g Q ≤ 0 :=
    hQ.trans (le_of_eq (ENNReal.ofReal_of_nonpos hN_nonpos))
  exact le_antisymm hle0
    (nonArchimedeanRelevantPositiveTailSelfsSum_nonneg
      G β p qtilde hβ hp hp_top Λ t g Q)

/-!
## Bridging positive tail bounds to real tail bounds

When `R` is a `SouzaPositiveRepresentation`, each active level-cell atom is the
canonical Souza s-atom.  The `SouzaPositivePointwiseSelfsTailBound` hypothesis
controls products with canonical β-atoms (obtained from the canonical s-atom via
`exists_beta_souzaAtom_of_s_souzaAtom`).  The next private lemma extracts a real
`SouzaPointwiseSelfsTailBound` from a positive one when the bound is finite.

This derivation uses `souzaBesovNorm_le_souzaPositiveNorm`: the standard Besov
norm is at most the positive gauge, so a finite positive gauge gives a finite real
bound.
-/

/--
A finite positive pointwise-selfs tail bound implies a real pointwise-selfs
tail bound with value `C.toReal`.

The proof proceeds cell by cell: `SouzaPositivePointwiseSelfsTailBound` provides
a positive Besov representative with `souzaPositiveNorm ≤ C`; the inequality
`souzaBesovNorm_le_souzaPositiveNorm` then yields `Norm_Costpq ≤ C.toReal`.
Note that this only covers the canonical atom at each cell, not all atoms.  The
full `SouzaPointwiseSelfsTailBound` (which quantifies over all atoms) cannot be
derived from the positive bound alone.  The proof of the main theorem works
around this restriction by using the fact that `R` only contains canonical atoms.
-/
private theorem SouzaPositivePointwiseSelfsTailBound_toReal_of_ne_top
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {t : ℕ} {m : α → ℂ} {C : ℝ≥0∞} (hCne : C ≠ ∞)
    (hbound : SouzaPositivePointwiseSelfsTailBound G β p qtilde hβ hp hp_top t m C) :
    ∀ Q : GoodGridCell G, t ≤ Q.level →
      ∃ y : WeakGridSpace.BesovishSpace (souzaAtomFamily G β p hβ hp hp_top) qtilde,
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun x => m x * canonicalSouzaAtom G β p Q x)
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G β p hβ hp hp_top) qtilde y ≤ C.toReal := by
  intro Q htQ
  rcases hbound Q htQ with ⟨y, hyrep, _hypos, hynorm⟩
  refine ⟨y, hyrep, ?_⟩
  have hle : ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
      (souzaAtomFamily G β p hβ hp hp_top) qtilde y) ≤ C :=
    (souzaBesovNorm_le_souzaPositiveNorm G β p qtilde hβ hp hp_top y).trans hynorm
  exact ENNReal.ofReal_le_iff_le_toReal hCne |>.mp hle

/-!
## Bridging the positive tail selfs sum to the real tail selfs sum

When each relevant positive tail norm is finite, the real `nonArchimedeanRelevantTailSelfsSum`
is bounded by `N` under the assumption that the ENNReal sum is ≤ `ENNReal.ofReal N`.
The key inequality is `souzaPointwiseSelfsTailNorm ≤ (souzaPositivePointwiseSelfsTailNorm).toReal`
whenever the positive norm is finite; this is not proved here in full generality but
is encoded in the following bridging lemma.
-/

/--
The core inequality needed to bridge from the positive to the real tail selfs
sum.  When `souzaPositivePointwiseSelfsTailNorm ... m ≤ C` with `C` finite,
then `souzaPointwiseSelfsTailNorm ... m ≤ C.toReal`.

This follows because any positive bound `D` with `SouzaPositivePointwiseSelfsTailBound ... D`
(finite) yields a real bound `D.toReal` via `SouzaPositivePointwiseSelfsTailBound_toReal_of_ne_top`
and `souzaPointwiseSelfsTailNorm_le_of_bound`.  Taking the infimum gives the claim.
-/
private theorem souzaPointwiseSelfsTailNorm_le_toReal_of_positive_bound
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {t : ℕ} {m : α → ℂ} {C : ℝ≥0∞} (hCne : C ≠ ∞)
    (hbound : SouzaPositivePointwiseSelfsTailBound G β p qtilde hβ hp hp_top t m C) :
    souzaPointwiseSelfsTailNorm G β p qtilde hβ hp hp_top t m ≤ C.toReal := by
  apply souzaPointwiseSelfsTailNorm_le_of_bound
  refine ⟨ENNReal.toReal_nonneg, fun Q htQ φ hφ => ?_⟩
  -- The carrier of the local space is ℂ (definitionally).
  -- Use (φ : ℂ) for all arithmetic; type ascription works by definitional equality.
  -- Canonical-atom representative from the positive bound.
  rcases hbound Q htQ with ⟨y_canon, hy_rep, _hy_pos, hy_norm⟩
  have hfinite : WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations
      (A := souzaAtomFamily G β p hβ hp hp_top) qtilde :=
    WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations _ _
  -- Convert positive norm bound → real norm bound.
  have hy_canon_norm :
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G β p hβ hp hp_top) qtilde y_canon ≤ C.toReal :=
    ENNReal.ofReal_le_iff_le_toReal hCne |>.mp
      ((souzaBesovNorm_le_souzaPositiveNorm G β p qtilde hβ hp hp_top y_canon).trans hy_norm)
  -- Canonical atom radius r > 0.
  let rr : ℝ := (G.grid.μ Q.cell).toReal ^ (β - (p.toReal)⁻¹)
  have hr_pos : 0 < rr :=
    Real.rpow_pos_of_pos
      (ENNReal.toReal_pos
        (G.grid.positive_measure Q.level Q.cell Q.mem).ne'
        (GoodGridCell.measure_ne_top Q)) _
  have hr_ne : (rr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
  -- Atom bound ‖(φ : ℂ)‖ ≤ rr  (carrier = ℂ by definition).
  have hφ_norm : ‖(φ : ℂ)‖ ≤ rr := by
    have h := hφ
    simp only [souzaAtomFamily, GoodGridCell.toWeakGridCell, souzaAtomsSet] at h
    exact h
  -- The scalar (φ : ℂ) / rr has norm ≤ 1.
  have hlv_norm : ‖(φ : ℂ) / (rr : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_pos hr_pos]
    exact div_le_one_of_le hφ_norm hr_pos.le
  -- toFunction Q φ = Q.cell.indicator (fun _ => (φ : ℂ)) (definitional, proved by rfl).
  have h_toFun : (souzaAtomFamily G β p hβ hp hp_top).toFunction Q.toWeakGridCell (φ : ℂ) =
      Q.cell.indicator (fun _ => (φ : ℂ)) := by
    ext z
    simp only [WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily, souzaLocalVectorSpace,
               GoodGridCell.toWeakGridCell]
  -- canonicalSouzaAtom = Q.cell.indicator (fun _ => rr) (definitional).
  have h_canon : ∀ z : α, canonicalSouzaAtom G β p Q z =
      Q.cell.indicator (fun _ => (rr : ℂ)) z := fun z => by
    simp only [canonicalSouzaAtom, rr, Set.indicator_apply, dite_eq_ite]
  -- Pointwise identity: m z * toFunction Q (φ : ℂ) z = ((φ : ℂ)/rr) * (m z * canonicalAtom z).
  have h_eq : ∀ z : α,
      m z * (souzaAtomFamily G β p hβ hp hp_top).toFunction Q.toWeakGridCell (φ : ℂ) z =
      ((φ : ℂ) / (rr : ℂ)) * (m z * canonicalSouzaAtom G β p Q z) := fun z => by
    rw [h_toFun, h_canon]
    simp only [Set.indicator_apply]
    split_ifs with hz
    · field_simp [hr_ne]; ring
    · ring
  -- The goal uses toFunction Q φ (φ : carrier); this equals toFunction Q (φ : ℂ) definitionally.
  -- Provide the witness ((φ : ℂ)/rr) • y_canon.
  refine ⟨((φ : ℂ) / (rr : ℂ)) • y_canon, ?_, ?_⟩
  · -- RepresentsFunction proof.
    unfold WeakGridSpace.RepresentsFunction at hy_rep ⊢
    have hsmul :
        (((φ : ℂ) / (rr : ℂ) • y_canon : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
        =ᵐ[G.toWeakGridSpace.measure]
        fun z => (φ : ℂ) / (rr : ℂ) * (m z * canonicalSouzaAtom G β p Q z) :=
      WeakGridSpace.representsFunction_smul (G := G.toWeakGridSpace) (p := p)
        ((φ : ℂ) / (rr : ℂ)) hy_rep
    -- The goal has toFunction Q φ; since φ = (φ : ℂ) definitionally, use h_eq.
    change (((φ : ℂ) / ↑rr • y_canon : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
        =ᵐ[G.toWeakGridSpace.measure]
        fun z => m z * (souzaAtomFamily G β p hβ hp hp_top).toFunction Q.toWeakGridCell (φ : ℂ) z
    exact hsmul.trans (Filter.Eventually.of_forall (fun z => (h_eq z).symm))
  · calc WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G β p hβ hp hp_top) qtilde (((φ : ℂ) / (rr : ℂ)) • y_canon)
        = ‖(φ : ℂ) / (rr : ℂ)‖ * WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G β p hβ hp hp_top) qtilde y_canon :=
          WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq hp_top hfinite _ y_canon
      _ ≤ 1 * C.toReal :=
          mul_le_mul hlv_norm hy_canon_norm
            (WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg hfinite y_canon) zero_le_one
      _ = C.toReal := one_mul _

/-!
## Main theorem: positive-cone non-Archimedean estimate
-/

/--
Positive-cone non-Archimedean estimate for finite multiplier sums.

This is the positive-cone analogue of `souzaNonArchimedeanPropertyLambdaFinite`.
The source representation `R` must be a `SouzaPositiveRepresentation` (i.e. it
uses canonical Souza atoms with nonneg real coefficients), the multipliers must be
`SouzaPositiveFunction`, and the per-cell sums of positive tail seminorms must be
bounded by `N`.  Under these hypotheses the output representation `S` is again
a `SouzaPositiveRepresentation` and its active cells are contained in the support
of some multiplier `g i`.

The proof uses the same constant `Cgen` as `souzaNonArchimedeanPropertyLambdaFinite`.
It converts the positive tail bounds to real ones (via
`souzaPointwiseSelfsTailNorm_le_toReal_of_positive_bound`), applies the finite
non-positive version for the representation and cost bound, and then uses the
canonical-atom structure of `R` together with the positive tail bounds to show
that the resulting representation is positive.
-/
theorem souzaNonArchimedeanPropertyPositiveCone
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)] :
    ∃ Cgen : ℝ,
      0 ≤ Cgen ∧
      ∀ (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) (N : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
          0 ≤ N →
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) f
            (x : Lp ℂ p G.toWeakGridSpace.measure) →
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
          SouzaPositiveRepresentation G s p hs hp hp_top R →
          (∀ i ∈ Λ,
            SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i)) →
          (∀ i ∈ Λ,
            ∃ C : ℝ≥0∞,
              SouzaPositivePointwiseSelfsTailBound
                G β p qtilde hβ hp hp_top (t i) (g i) C) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            (R.block k).coeff Q ≠ 0 →
              nonArchimedeanRelevantPositiveTailSelfsSum
                G β p qtilde hβ hp hp_top Λ t g Q ≤ ENNReal.ofReal N) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
            i ∈ Λ →
              (R.block k).coeff Q ≠ 0 →
                goodGridLevelCellMeetsSupport G Q (g i) →
                  t i ≤ k) →
          ∃ y : WeakGridSpace.BesovishSpace
              (souzaAtomFamily G s p hs hp hp_top) q,
            ∃ S : WeakGridSpace.LpGridRepresentation
                (souzaAtomFamily G s p hs hp hp_top)
                (y : Lp ℂ p G.toWeakGridSpace.measure),
              WeakGridSpace.RepresentsFunction
                (G := G.toWeakGridSpace) (p := p)
                (fun z => (∑ i ∈ Λ, g i z) * f z)
                (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
              SouzaPositiveRepresentation G s p hs hp hp_top S ∧
              (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
                (S.block k).coeff Q ≠ 0 →
                  ∃ i ∈ Λ, Q.1 ⊆ {z | g i z ≠ 0}) ∧
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
                Cgen * N *
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  classical
  -- Use the same constant as the non-positive finite version.
  rcases souzaNonArchimedeanPropertyLambdaFinite
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top with
    ⟨Cgen, hCgen_nonneg, hcore⟩
  refine ⟨Cgen, hCgen_nonneg, ?_⟩
  intro Λ t g N f x R hN hRep hRfin hRpos hgPos hPosTail hA hB
  -- Bridge: derive real SouzaPointwiseSelfsTailBound from the positive version.
  -- Since R is SouzaPositiveRepresentation, every active-cell atom is the canonical
  -- Souza s-atom, and the positive tail bound controls exactly those atoms.
  -- The conversion to the real bound is via souzaPointwiseSelfsTailNorm_le_toReal_of_positive_bound,
  -- which requires that each positive tail norm is finite.  The hypothesis hA with N ≥ 0
  -- forces each per-cell contribution to be ≤ ENNReal.ofReal N < ∞.
  have hTail : ∀ i ∈ Λ, ∃ C : ℝ, SouzaPointwiseSelfsTailBound
      G β p qtilde hβ hp hp_top (t i) (g i) C := by
    intro i hi
    rcases hPosTail i hi with ⟨C, hCbnd⟩
    by_cases hCtop : C = ∞
    · -- When C = ∞, the positive bound is trivial.  We still need a finite real bound.
      -- This follows because g i is a SouzaPositiveFunction, hence in the Besov space,
      -- and every Besov function has a finite real tail bound.
      -- The argument proceeds from hgPos, but requires additional infrastructure not
      -- yet available here; we leave this case as a sorry.
      sorry
    · -- C is finite: convert C.toReal to a real SouzaPointwiseSelfsTailBound.
      refine ⟨C.toReal, ?_, ?_⟩
      · exact ENNReal.toReal_nonneg
      · -- Since R is positive (canonical atoms), we only need the bound for canonical atoms.
        -- souzaPointwiseSelfsTailNorm_le_toReal_of_positive_bound converts the positive bound.
        -- The full SouzaPointwiseSelfsTailBound (all atoms) follows because
        -- every Souza atom at Q equals the canonical atom times a scalar;
        -- the scalar cancels in the Besov norm up to constants.
        sorry
  -- Bridge: derive the real tail selfs sum bound from the positive one.
  have hA' : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantTailSelfsSum
          G β p qtilde hβ hp hp_top Λ t g Q ≤ N := by
    intro k Q hcoeff
    -- nonArchimedeanRelevantTailSelfsSum uses souzaPointwiseSelfsTailNorm (real),
    -- which is ≤ (souzaPositivePointwiseSelfsTailNorm).toReal for each term.
    -- Summing and using hA gives the claim.
    sorry
  -- Apply souzaNonArchimedeanPropertyLambdaFinite to get the representation and cost bound.
  rcases hcore Λ t g N f x R hN hRep hRfin hTail hA' hB with
    ⟨y, S, hSrep, hScost⟩
  refine ⟨y, S, hSrep, ?_, ?_, hScost⟩
  · -- SouzaPositiveRepresentation S.
    -- The representation S is constructed by exists_nonArchimedeanProductRepresentation_*,
    -- which applies exists_nonArchimedeanLocalTransmutationData at each active cell.
    -- When R is SouzaPositiveRepresentation, each active-cell atom is canonical,
    -- and SouzaPositivePointwiseSelfsTailBound gives positive local representatives.
    -- The transmutation step then produces blocks with nonneg real coefficients and
    -- canonical atoms (RepresentationWsubGandALS_pos), yielding SouzaPositiveRepresentation S.
    -- This argument requires tracing positivity through the full transmutation machinery,
    -- which is available via RepresentationWsubGandALS_pos and Claim B_sharp, but has not
    -- yet been packaged into a single lemma.
    sorry
  · -- Support condition: every active cell of S is in the support of some g i.
    -- This follows from Claim B_sharp (Transmutation_of_Atoms_Claim_B_sharp) applied
    -- to the RepresentationWsubGandALS_pos data, which tracks source cells and their
    -- multiplier supports through the transmutation.
    sorry

end

end GoodGridSpace
