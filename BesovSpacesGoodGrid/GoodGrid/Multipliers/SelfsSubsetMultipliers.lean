import BesovSpacesGoodGrid.GoodGrid.Multipliers.NonArchimedeanProperty

/-!
# The tail `selfs` classes consist of pointwise multipliers (Corollary `23er`)

This file proves Corollary `23er` of the paper *Besov-ish spaces through
atomic decomposition*: for smoothness parameters `0 < s < β < 1/p` and any
integrability parameters `q, qtilde ∈ [1,∞]`, every function in the level-tail
`selfs` class `B^{β,t}_{p,qtilde,selfs}` is a pointwise multiplier of the
Souza Besov space `B^s_{p,q}`, and the inclusion is continuous: the multiplier
operator norm is controlled by a constant times the tail `selfs` seminorm.

The proof is a short derivation from the non-Archimedean property
(`souzaNonArchimedeanPropertyLambdaFinite`) applied to the one-element family
`{g}`, combined with a level-lowering step that converts a tail `selfs` bound
from an arbitrary cutoff level `t` to the cutoff level `0` demanded by the
support condition of the non-Archimedean theorem.

## Main results

* `souzaPointwiseSelfsTailBound_levelZero`: level lowering — a tail `selfs`
  bound from level `t` onward yields a full (level-`0`) `selfs` bound, with
  constant multiplied by the number of level-`t` cells.  An atom on a shallow
  cell is the finite disjoint sum of its level-`t` pieces, each of which is a
  scaled atom on a tail cell.
* `exists_souzaSelfsMultiplierConstant`: the quantitative Corollary `23er` —
  there is a constant `Cmult` such that every tail `selfs` bound `C` for `g`
  produces the multiplier operator bound `Cmult * C` for `g` on `B^s_{p,q}`.
* `souzaPointwiseMultiplier_of_souzaPointwiseSelfsTailClass`: the inclusion
  `B^{β,t}_{p,qtilde,selfs} ⊆ M(B^s_{p,q})`.
* `souzaPointwiseMultiplierNorm_le_const_mul_selfsTailNorm`: continuity of the
  inclusion at the level of (semi)norms.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/-- The zero representation has finite `(p,q)` cost (generic atom family). -/
private theorem zero_representation_finitePQCost
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' q' : ℝ≥0∞}
    [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    (A : WeakGridSpace.AtomFamily G' s' p' u') :
    WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q')
      (WeakGridSpace.LpGridRepresentation.zero A) := by
  have hp_pos : 0 < p'.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p')).ne' A.p_ne_top
  by_cases hqtop : q' = ∞
  · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_pos hqtop]
    refine ⟨0, ?_⟩
    rintro x ⟨j, rfl⟩
    have hzero : (0 : ℝ) ^ (p'.toReal)⁻¹ = 0 :=
      Real.zero_rpow (inv_ne_zero hp_pos.ne')
    simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower, hzero]
  · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hqtop]
    have hq_pos : 0 < q'.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q')).ne' hqtop
    have hpow_ne : q'.toReal / p'.toReal ≠ 0 :=
      div_ne_zero hq_pos.ne' hp_pos.ne'
    simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower,
      Real.zero_rpow hpow_ne]

/-- The zero representation has zero `(p,q)` cost (generic atom family). -/
private theorem zero_representation_pqCost_eq_zero
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' q' : ℝ≥0∞}
    [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    (A : WeakGridSpace.AtomFamily G' s' p' u') :
    WeakGridSpace.LpGridRepresentation.pqCost (q := q')
      (WeakGridSpace.LpGridRepresentation.zero A) = 0 := by
  have hp_pos : 0 < p'.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p')).ne' A.p_ne_top
  by_cases hqtop : q' = ∞
  · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos hqtop]
    have hzero : (0 : ℝ) ^ (p'.toReal)⁻¹ = 0 :=
      Real.zero_rpow (inv_ne_zero hp_pos.ne')
    simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower, hzero]
  · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hqtop]
    have hq_pos : 0 < q'.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q')).ne' hqtop
    have hpow_ne : q'.toReal / p'.toReal ≠ 0 :=
      div_ne_zero hq_pos.ne' hp_pos.ne'
    have hqinv_ne : (q'.toReal)⁻¹ ≠ 0 := inv_ne_zero hq_pos.ne'
    simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower,
      Real.zero_rpow hpow_ne, Real.zero_rpow hqinv_ne]

/-- The coefficient-cost gauge of the zero vector vanishes. -/
private theorem norm_Costpq_zero_le
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' q' : ℝ≥0∞}
    [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    (A : WeakGridSpace.AtomFamily G' s' p' u') :
    WeakGridSpace.BesovishSpace.Norm_Costpq A q'
      (0 : WeakGridSpace.BesovishSpace A q') ≤ 0 := by
  let R : WeakGridSpace.LpGridRepresentation A
      ((0 : WeakGridSpace.BesovishSpace A q') : Lp ℂ p' G'.measure) :=
    WeakGridSpace.LpGridRepresentation.zero A
  have h := WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost (A := A) (q := q')
    (g := (0 : WeakGridSpace.BesovishSpace A q')) R
    (zero_representation_finitePQCost A)
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq A q'
        (0 : WeakGridSpace.BesovishSpace A q')
        ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q') R := h
    _ = 0 := zero_representation_pqCost_eq_zero A

/-- Finite-sum triangle inequality for the coefficient-cost gauge. -/
private theorem norm_Costpq_finset_sum_le
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' q' : ℝ≥0∞}
    [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    (A : WeakGridSpace.AtomFamily G' s' p' u')
    {ι : Type*} (S : Finset ι) (v : ι → WeakGridSpace.BesovishSpace A q') :
    WeakGridSpace.BesovishSpace.Norm_Costpq A q' (∑ i ∈ S, v i) ≤
      ∑ i ∈ S, WeakGridSpace.BesovishSpace.Norm_Costpq A q' (v i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using norm_Costpq_zero_le (q' := q') A
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        WeakGridSpace.BesovishSpace.Norm_Costpq A q' (v a + ∑ i ∈ S, v i)
            ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A q' (v a) +
                WeakGridSpace.BesovishSpace.Norm_Costpq A q' (∑ i ∈ S, v i) :=
          WeakGridSpace.BesovishSpace.Norm_Costpq_add_le (A := A) (q := q')
            A.p_ne_top
            (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A q')
            (v a) (∑ i ∈ S, v i)
        _ ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A q' (v a) +
              ∑ i ∈ S, WeakGridSpace.BesovishSpace.Norm_Costpq A q' (v i) :=
          add_le_add le_rfl ih

/--
Core case of Corollary `23er`, with cutoff level `0`: a full `selfs` bound
turns `g` into a pointwise multiplier of `B^s_{p,q}` with operator bound
`Cmult * C`.

This is the non-Archimedean theorem applied to the singleton family `{g}`
with all level cutoffs equal to `0`, so both separation hypotheses hold
trivially, with `N = C`.
-/
private theorem exists_souzaSelfsZeroMultiplierConstant
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)] :
    ∃ Cmult : ℝ,
      0 ≤ Cmult ∧
      ∀ (g : α → ℂ) (C : ℝ),
        SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top 0 g C →
        SouzaPointwiseMultiplierBound G s p q hs hp hp_top g (Cmult * C) := by
  classical
  obtain ⟨Cgen, hCgen_nonneg, hCgen⟩ :=
    souzaNonArchimedeanPropertyLambdaFinite
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
  refine ⟨Cgen, hCgen_nonneg, ?_⟩
  intro g C hgC
  have hC_nonneg : 0 ≤ C := hgC.1
  have hCC_nonneg : 0 ≤ Cgen * C := mul_nonneg hCgen_nonneg hC_nonneg
  refine ⟨hCC_nonneg, ?_⟩
  intro x
  let A := souzaAtomFamily G s p hs hp hp_top
  let f : α → ℂ :=
    fun z => ((x : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z
  have hfRep :
      WeakGridSpace.RepresentsFunction (G := G.toWeakGridSpace) (p := p) f
        (x : Lp ℂ p G.toWeakGridSpace.measure) :=
    Filter.EventuallyEq.rfl
  -- One run of the non-Archimedean theorem for an arbitrary finite-cost
  -- representation `R` of `x`, with the singleton family `{g}`.
  have key :
      ∀ R : WeakGridSpace.LpGridRepresentation A
          (x : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
        ∃ y : WeakGridSpace.BesovishSpace A q,
          WeakGridSpace.RepresentsPointwiseProduct
            (G := G.toWeakGridSpace) (p := p) g
            (x : Lp ℂ p G.toWeakGridSpace.measure)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq A q y ≤
            Cgen * C * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
    intro R hRfin
    have hTail :
        ∀ i ∈ ({0} : Finset ℕ),
          ∃ C' : ℝ,
            SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top
              ((fun _ : ℕ => 0) i) ((fun _ : ℕ => g) i) C' :=
      fun i _ => ⟨C, hgC⟩
    have hA :
        ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (R.block k).coeff Q ≠ 0 →
            nonArchimedeanRelevantTailSelfsSum G β p qtilde hβ hp hp_top
              ({0} : Finset ℕ) (fun _ => 0) (fun _ => g) Q ≤ C := by
      intro k Q _
      have hnorm_le :
          souzaPointwiseSelfsTailNorm G β p qtilde hβ hp hp_top 0 g ≤ C :=
        souzaPointwiseSelfsTailNorm_le_of_bound G β p qtilde hβ hp hp_top hgC
      change
        (∑ i ∈ ({0} : Finset ℕ),
          if goodGridLevelCellMeetsSupport G Q ((fun _ : ℕ => g) i) then
            souzaPointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
              ((fun _ : ℕ => 0) i) ((fun _ : ℕ => g) i)
          else 0) ≤ C
      rw [Finset.sum_singleton]
      split_ifs
      · exact hnorm_le
      · exact hC_nonneg
    have hB :
        ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
          i ∈ ({0} : Finset ℕ) →
            (R.block k).coeff Q ≠ 0 →
              goodGridLevelCellMeetsSupport G Q ((fun _ : ℕ => g) i) →
                (fun _ : ℕ => 0) i ≤ k :=
      fun k _ i _ _ _ => Nat.zero_le k
    obtain ⟨y, S, hyRep, hSfin, hScost⟩ :=
      hCgen ({0} : Finset ℕ) (fun _ => 0) (fun _ => g) C f x R
        hC_nonneg hfRep hRfin hTail hA hB
    refine ⟨y, ?_, ?_⟩
    · refine hyRep.trans (Filter.Eventually.of_forall ?_)
      intro z
      simp [f]
    · calc
        WeakGridSpace.BesovishSpace.Norm_Costpq A q y
            ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) S :=
          WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
            (A := A) (q := q) (g := y) S hSfin
        _ ≤ Cgen * C * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
          hScost
  -- Fix the product representative once, then optimize the cost bound.
  obtain ⟨R₁, hR₁fin, _⟩ :=
    WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add (A := A) (q := q)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A q) x one_pos
  obtain ⟨y, hyProd, _⟩ := key R₁ hR₁fin
  refine ⟨y, hyProd, ?_⟩
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hden : (0 : ℝ) < Cgen * C + 1 := by linarith
  have hδ : 0 < ε / (Cgen * C + 1) := by positivity
  obtain ⟨R, hRfin, hRlt⟩ :=
    WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add (A := A) (q := q)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A q) x hδ
  obtain ⟨y', hy'Prod, hy'Norm⟩ := key R hRfin
  -- Both candidates represent the same a.e. product, so they coincide.
  have hyy' : y' = y := by
    apply Subtype.ext
    apply Lp.ext
    exact hy'Prod.trans hyProd.symm
  have hcost_le :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
        WeakGridSpace.BesovishSpace.Norm_Costpq A q x + ε / (Cgen * C + 1) :=
    hRlt.le
  have hmul :
      Cgen * C * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
        Cgen * C *
          (WeakGridSpace.BesovishSpace.Norm_Costpq A q x + ε / (Cgen * C + 1)) :=
    mul_le_mul_of_nonneg_left hcost_le hCC_nonneg
  have hfrac : Cgen * C * (ε / (Cgen * C + 1)) ≤ ε := by
    have hratio : Cgen * C / (Cgen * C + 1) ≤ (1 : ℝ) :=
      (div_le_one hden).2 (by linarith)
    have := mul_le_mul_of_nonneg_right hratio hε.le
    calc
      Cgen * C * (ε / (Cgen * C + 1))
          = (Cgen * C / (Cgen * C + 1)) * ε := by ring
      _ ≤ 1 * ε := this
      _ = ε := one_mul ε
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq A q y
        = WeakGridSpace.BesovishSpace.Norm_Costpq A q y' := by rw [hyy']
    _ ≤ Cgen * C * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
      hy'Norm
    _ ≤ Cgen * C *
          (WeakGridSpace.BesovishSpace.Norm_Costpq A q x + ε / (Cgen * C + 1)) :=
      hmul
    _ = Cgen * C * WeakGridSpace.BesovishSpace.Norm_Costpq A q x +
          Cgen * C * (ε / (Cgen * C + 1)) := by ring
    _ ≤ Cgen * C * WeakGridSpace.BesovishSpace.Norm_Costpq A q x + ε := by
      linarith

/--
Level lowering for tail `selfs` bounds.

A tail `selfs` bound for `g` from level `t` onward yields a full `selfs`
bound (cutoff level `0`), with the constant multiplied by the number of
level-`t` grid cells.  In the paper's notation this is one half of the
equivalence between `|·|_{B^{β,t}_{p,q,selfs}}` and `|·|_{B^β_{p,q,selfs}}`.

The proof decomposes a Souza atom on a cell `Q` of level below `t` as the
finite sum of its restrictions to the level-`t` cells contained in `Q`
(an exact pointwise identity, by nestedness and disjointness of the grid
partitions).  Each restriction is a scaled Souza atom on a tail cell with
scaling factor at most `1`, so the tail hypothesis applies to each piece.
-/
theorem souzaPointwiseSelfsTailBound_levelZero
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {t : ℕ} {g : α → ℂ} {C : ℝ}
    (hgC : SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top t g C) :
    SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top 0 g
      (((G.toWeakGridSpace.grid.partitions t).card : ℝ) * C) := by
  classical
  obtain ⟨hC0, hbound⟩ := hgC
  -- The level-`t` partition is nonempty, since it covers the whole space.
  have hpart_nonempty : (G.toWeakGridSpace.grid.partitions t).Nonempty := by
    have huniv_mem : Set.univ ∈ G.grid.grid.partitions 0 := by
      rw [G.grid.grid.first_partition_eq_univ]
      exact Finset.mem_singleton_self _
    obtain ⟨z, _⟩ := G.grid.partition_nonempty 0 Set.univ huniv_mem
    have hz : z ∈ ⋃ P ∈ G.grid.grid.partitions t, P := by
      rw [G.grid.grid.covering t]
      exact Set.mem_univ z
    rcases Set.mem_iUnion₂.mp hz with ⟨P, hP, _⟩
    exact ⟨P, hP⟩
  have hcard_one_le :
      (1 : ℝ) ≤ ((G.toWeakGridSpace.grid.partitions t).card : ℝ) := by
    have := Finset.card_pos.mpr hpart_nonempty
    exact_mod_cast this
  have hcard_nonneg :
      (0 : ℝ) ≤ ((G.toWeakGridSpace.grid.partitions t).card : ℝ) :=
    le_trans zero_le_one hcard_one_le
  refine ⟨mul_nonneg hcard_nonneg hC0, ?_⟩
  intro Q _ φ hφ
  by_cases hQt : t ≤ Q.level
  · -- Deep cells: use the tail bound directly.
    obtain ⟨y, hyRep, hyNorm⟩ := hbound Q hQt φ hφ
    exact ⟨y, hyRep,
      hyNorm.trans (le_mul_of_one_le_left hC0 hcard_one_le)⟩
  -- Shallow cells: decompose the atom into its level-`t` pieces.
  rw [not_le] at hQt
  let A := souzaAtomFamily G β p hβ hp hp_top
  let φ' : ℂ := φ
  let r : ℝ := β - (p.toReal)⁻¹
  have hr_neg : r < 0 := sub_neg.mpr hβ_lt_inv
  let μQ : ℝ := (G.grid.μ Q.cell).toReal
  have hμQ_pos : 0 < μQ :=
    ENNReal.toReal_pos Q.measure_pos.ne' Q.measure_ne_top
  have hφ'_le : ‖φ'‖ ≤ μQ ^ r := hφ
  -- The level-`t` cells contained in `Q.cell`.
  let F : Finset (Set α) :=
    (G.toWeakGridSpace.grid.partitions t).filter (fun P => P ⊆ Q.cell)
  have hF_mem : ∀ P ∈ F, P ∈ G.grid.grid.partitions t ∧ P ⊆ Q.cell := by
    intro P hP
    exact Finset.mem_filter.mp hP
  -- Per-piece data.
  let cellOf : {P // P ∈ F} → GoodGridCell G := fun P =>
    ⟨t, P.1, (hF_mem P.1 P.2).1⟩
  let μP : {P // P ∈ F} → ℝ := fun P => (G.grid.μ P.1).toReal
  have hμP_pos : ∀ P : {P // P ∈ F}, 0 < μP P := fun P =>
    ENNReal.toReal_pos (cellOf P).measure_pos.ne' (cellOf P).measure_ne_top
  have hμP_le : ∀ P : {P // P ∈ F}, μP P ≤ μQ := by
    intro P
    have hmono : G.grid.μ P.1 ≤ G.grid.μ Q.cell :=
      measure_mono (hF_mem P.1 P.2).2
    exact ENNReal.toReal_mono Q.measure_ne_top hmono
  let lamP : {P // P ∈ F} → ℝ := fun P => (μQ / μP P) ^ r
  let φP : {P // P ∈ F} → ℂ := fun P =>
    φ' * (((μP P / μQ) ^ r : ℝ) : ℂ)
  have hlamP_pos : ∀ P : {P // P ∈ F}, 0 < lamP P := fun P =>
    Real.rpow_pos_of_pos (div_pos hμQ_pos (hμP_pos P)) r
  have hlamP_le_one : ∀ P : {P // P ∈ F}, lamP P ≤ 1 := by
    intro P
    refine Real.rpow_le_one_of_one_le_of_nonpos ?_ hr_neg.le
    exact (one_le_div (hμP_pos P)).mpr (hμP_le P)
  -- The piece scaling factors multiply back to `1`.
  have hlam_phi : ∀ P : {P // P ∈ F},
      ((lamP P : ℝ) : ℂ) * φP P = φ' := by
    intro P
    have hbase :
        (μQ / μP P) ^ r * (μP P / μQ) ^ r = 1 := by
      rw [← Real.mul_rpow
        (div_nonneg hμQ_pos.le (hμP_pos P).le)
        (div_nonneg (hμP_pos P).le hμQ_pos.le)]
      rw [div_mul_div_comm]
      rw [mul_comm (μP P) μQ]
      rw [div_self (mul_pos hμQ_pos (hμP_pos P)).ne']
      exact Real.one_rpow r
    calc
      ((lamP P : ℝ) : ℂ) * (φ' * (((μP P / μQ) ^ r : ℝ) : ℂ))
          = φ' * ((((μQ / μP P) ^ r * (μP P / μQ) ^ r : ℝ)) : ℂ) := by
            push_cast
            ring
      _ = φ' := by rw [hbase]; simp
  -- Each piece is an admissible Souza atom on its level-`t` cell.
  have hφP_mem : ∀ P : {P // P ∈ F},
      φP P ∈ A.atoms (cellOf P).toWeakGridCell := by
    intro P
    have hfactor_nonneg : (0 : ℝ) ≤ (μP P / μQ) ^ r :=
      (Real.rpow_pos_of_pos (div_pos (hμP_pos P) hμQ_pos) r).le
    have hμQr_pos : 0 < μQ ^ r := Real.rpow_pos_of_pos hμQ_pos r
    change ‖φP P‖ ≤ (G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹)
    have hnorm_eq : ‖φP P‖ = ‖φ'‖ * (μP P / μQ) ^ r := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hfactor_nonneg]
    have hcollapse : μQ ^ r * (μP P / μQ) ^ r = μP P ^ r := by
      rw [← Real.mul_rpow hμQ_pos.le (div_nonneg (hμP_pos P).le hμQ_pos.le)]
      rw [mul_div_cancel₀ _ hμQ_pos.ne']
    calc
      ‖φP P‖ = ‖φ'‖ * (μP P / μQ) ^ r := hnorm_eq
      _ ≤ μQ ^ r * (μP P / μQ) ^ r :=
        mul_le_mul_of_nonneg_right hφ'_le hfactor_nonneg
      _ = μP P ^ r := hcollapse
  -- Apply the tail hypothesis on each level-`t` piece.
  have hpieces : ∀ P : {P // P ∈ F},
      ∃ y : WeakGridSpace.BesovishSpace A qtilde,
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => g z *
            A.toFunction (cellOf P).toWeakGridCell (φP P) z)
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq A qtilde y ≤ C := by
    intro P
    exact hbound (cellOf P) le_rfl (φP P) (hφP_mem P)
  choose yP hyP_rep hyP_norm using hpieces
  -- Assemble the candidate Besov-ish vector.
  refine ⟨∑ P ∈ F.attach, ((lamP P : ℝ) : ℂ) • yP P, ?_, ?_⟩
  · -- It represents `g * (the atom on Q)`.
    have hcoe :
        ((∑ P ∈ F.attach, ((lamP P : ℝ) : ℂ) • yP P :
            WeakGridSpace.BesovishSpace A qtilde) :
            Lp ℂ p G.toWeakGridSpace.measure) =
          ∑ P ∈ F.attach, ((lamP P : ℝ) : ℂ) •
            (yP P : Lp ℂ p G.toWeakGridSpace.measure) := by
      simp only [AddSubmonoidClass.coe_finsetSum]
      exact Finset.sum_congr rfl fun P _ => rfl
    have hsum_rep :
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ P ∈ F.attach, ((lamP P : ℝ) : ℂ) *
            (g z * A.toFunction (cellOf P).toWeakGridCell (φP P) z))
          (∑ P ∈ F.attach, ((lamP P : ℝ) : ℂ) •
            (yP P : Lp ℂ p G.toWeakGridSpace.measure)) := by
      refine WeakGridSpace.representsFunction_finset_sum F.attach _ _ ?_
      intro P _
      exact WeakGridSpace.representsFunction_smul _ (hyP_rep P)
    -- Pointwise, the represented sum collapses to `g * (atom on Q)`.
    have hfun_eq : ∀ z,
        (∑ P ∈ F.attach, ((lamP P : ℝ) : ℂ) *
          (g z * A.toFunction (cellOf P).toWeakGridCell (φP P) z)) =
          g z * A.toFunction Q.toWeakGridCell φ z := by
      intro z
      have hterm : ∀ P : {P // P ∈ F},
          ((lamP P : ℝ) : ℂ) *
            (g z * A.toFunction (cellOf P).toWeakGridCell (φP P) z) =
            g z * P.1.indicator (fun _ => φ') z := by
        intro P
        have htf :
            A.toFunction (cellOf P).toWeakGridCell (φP P) z =
              P.1.indicator (fun _ => φP P) z := rfl
        rw [htf]
        by_cases hz : z ∈ P.1
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
          calc
            ((lamP P : ℝ) : ℂ) * (g z * φP P)
                = g z * (((lamP P : ℝ) : ℂ) * φP P) := by ring
            _ = g z * φ' := by rw [hlam_phi P]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
          ring
      rw [Finset.sum_congr rfl (fun P _ => hterm P)]
      rw [← Finset.mul_sum]
      have htfQ :
          A.toFunction Q.toWeakGridCell φ z =
            Q.cell.indicator (fun _ => φ') z := rfl
      rw [htfQ]
      congr 1
      -- The level-`t` pieces partition `Q.cell` exactly.
      have hattach :
          (∑ P ∈ F.attach, P.1.indicator (fun _ => φ') z) =
            ∑ P ∈ F, P.indicator (fun _ => φ') z :=
        F.sum_attach (fun P => P.indicator (fun _ => φ') z)
      rw [hattach]
      by_cases hzQ : z ∈ Q.cell
      · -- Exactly one level-`t` cell contains `z`, and it lies inside `Q.cell`.
        have hzU : z ∈ ⋃ P ∈ G.grid.grid.partitions t, P := by
          rw [G.grid.grid.covering t]
          exact Set.mem_univ z
        rcases Set.mem_iUnion₂.mp hzU with ⟨P₀, hP₀_mem, hzP₀⟩
        have hP₀_sub : P₀ ⊆ Q.cell := by
          rcases G.grid.partition_subset_or_disjoint_of_le
              Q.level t hQt.le Q.cell Q.mem P₀ hP₀_mem with hsub | hdisj
          · exact hsub
          · exact absurd hzQ (Set.disjoint_left.mp hdisj hzP₀)
        have hP₀_F : P₀ ∈ F :=
          Finset.mem_filter.mpr ⟨hP₀_mem, hP₀_sub⟩
        rw [Set.indicator_of_mem hzQ]
        rw [Finset.sum_eq_single P₀]
        · rw [Set.indicator_of_mem hzP₀]
        · intro P hPF hPne
          have hP_mem : P ∈ G.grid.grid.partitions t := (hF_mem P hPF).1
          have hdisj : Disjoint P P₀ :=
            G.grid.grid.disjoint t P P₀ hP_mem hP₀_mem hPne
          have hzP : z ∉ P := fun hzP =>
            Set.disjoint_left.mp hdisj hzP hzP₀
          rw [Set.indicator_of_notMem hzP]
        · intro hP₀_not
          exact absurd hP₀_F hP₀_not
      · -- Outside `Q.cell` every piece vanishes.
        rw [Set.indicator_of_notMem hzQ]
        refine Finset.sum_eq_zero ?_
        intro P hPF
        have hzP : z ∉ P := fun hzP => hzQ ((hF_mem P hPF).2 hzP)
        rw [Set.indicator_of_notMem hzP]
    refine ?_
    rw [WeakGridSpace.RepresentsFunction, hcoe]
    exact hsum_rep.trans (Filter.Eventually.of_forall hfun_eq)
  · -- The cost bound: at most `card * C`.
    have htri :
        WeakGridSpace.BesovishSpace.Norm_Costpq A qtilde
            (∑ P ∈ F.attach, ((lamP P : ℝ) : ℂ) • yP P) ≤
          ∑ P ∈ F.attach,
            WeakGridSpace.BesovishSpace.Norm_Costpq A qtilde
              (((lamP P : ℝ) : ℂ) • yP P) :=
      norm_Costpq_finset_sum_le A F.attach _
    have hterm_le : ∀ P ∈ F.attach,
        WeakGridSpace.BesovishSpace.Norm_Costpq A qtilde
            (((lamP P : ℝ) : ℂ) • yP P) ≤ C := by
      intro P _
      have hsmul :
          WeakGridSpace.BesovishSpace.Norm_Costpq A qtilde
              (((lamP P : ℝ) : ℂ) • yP P) =
            ‖((lamP P : ℝ) : ℂ)‖ *
              WeakGridSpace.BesovishSpace.Norm_Costpq A qtilde (yP P) :=
        WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq (A := A) (q := qtilde)
          A.p_ne_top
          (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A qtilde)
          _ (yP P)
      have hnorm_lam : ‖((lamP P : ℝ) : ℂ)‖ = lamP P := by
        rw [Complex.norm_real, Real.norm_of_nonneg (hlamP_pos P).le]
      have hyP_nonneg :
          0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A qtilde (yP P) :=
        WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg (A := A) (q := qtilde)
          (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A qtilde)
          (yP P)
      calc
        WeakGridSpace.BesovishSpace.Norm_Costpq A qtilde
            (((lamP P : ℝ) : ℂ) • yP P)
            = lamP P *
                WeakGridSpace.BesovishSpace.Norm_Costpq A qtilde (yP P) := by
              rw [hsmul, hnorm_lam]
        _ ≤ 1 * C := by
              exact mul_le_mul (hlamP_le_one P) (hyP_norm P) hyP_nonneg
                zero_le_one
        _ = C := one_mul C
    have hcard_F :
        ((F.attach.card : ℝ)) ≤
          ((G.toWeakGridSpace.grid.partitions t).card : ℝ) := by
      rw [Finset.card_attach]
      exact_mod_cast Finset.card_filter_le _ _
    calc
      WeakGridSpace.BesovishSpace.Norm_Costpq A qtilde
          (∑ P ∈ F.attach, ((lamP P : ℝ) : ℂ) • yP P)
          ≤ ∑ P ∈ F.attach,
              WeakGridSpace.BesovishSpace.Norm_Costpq A qtilde
                (((lamP P : ℝ) : ℂ) • yP P) := htri
      _ ≤ ∑ _P ∈ F.attach, C := Finset.sum_le_sum hterm_le
      _ = (F.attach.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((G.toWeakGridSpace.grid.partitions t).card : ℝ) * C :=
        mul_le_mul_of_nonneg_right hcard_F hC0

/--
**Corollary `23er` of the paper, quantitative form.**

Let `0 < s < β < 1/p`, `q, qtilde ∈ [1,∞]` and fix a cutoff level `t`.  There
is a constant `Cmult` (depending only on the grid and the parameters) such
that every function `g` with tail `selfs` bound `C` — that is, every `g` with
`|g|_{B^{β,t}_{p,qtilde,selfs}} ≤ C` in the paper's notation — is a pointwise
multiplier of the Souza Besov space `B^s_{p,q}` with operator bound
`Cmult * C`.
-/
theorem exists_souzaSelfsMultiplierConstant
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p q qtilde : ℝ≥0∞) (t : ℕ)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)] :
    ∃ Cmult : ℝ,
      0 ≤ Cmult ∧
      ∀ (g : α → ℂ) (C : ℝ),
        SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top t g C →
        SouzaPointwiseMultiplierBound G s p q hs hp hp_top g (Cmult * C) := by
  obtain ⟨Czero, hCzero_nonneg, hCzero⟩ :=
    exists_souzaSelfsZeroMultiplierConstant
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
  refine ⟨Czero * ((G.toWeakGridSpace.grid.partitions t).card : ℝ),
    mul_nonneg hCzero_nonneg (Nat.cast_nonneg _), ?_⟩
  intro g C hgC
  have hzero :
      SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top 0 g
        (((G.toWeakGridSpace.grid.partitions t).card : ℝ) * C) :=
    souzaPointwiseSelfsTailBound_levelZero
      G β p qtilde hβ hβ_lt_inv hp hp_top hgC
  have hmult :=
    hCzero g (((G.toWeakGridSpace.grid.partitions t).card : ℝ) * C) hzero
  rw [mul_assoc]
  exact hmult

/--
**Corollary `23er` of the paper, inclusion form.**

For `0 < s < β < 1/p` and `q, qtilde ∈ [1,∞]`, every member of the tail
`selfs` class `B^{β,t}_{p,qtilde,selfs}` is a pointwise multiplier of the
Souza Besov space `B^s_{p,q}`.
-/
theorem souzaPointwiseMultiplier_of_souzaPointwiseSelfsTailClass
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p q qtilde : ℝ≥0∞) (t : ℕ)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    {g : α → ℂ}
    (hg : SouzaPointwiseSelfsTailClass G β p qtilde hβ hp hp_top t g) :
    SouzaPointwiseMultiplier G s p q hs hp hp_top g := by
  obtain ⟨Cmult, _, hCmult⟩ :=
    exists_souzaSelfsMultiplierConstant
      G s β p q qtilde t hs hβ hβs hβ_lt_inv hp hp_top
  obtain ⟨C, hC⟩ := hg
  exact ⟨Cmult * C, hCmult g C hC⟩

/--
**Corollary `23er` of the paper, continuity form.**

The inclusion `B^{β,t}_{p,qtilde,selfs} ⊆ M(B^s_{p,q})` is continuous: the
multiplier operator norm of `g` on `B^s_{p,q}` is at most a constant times the
tail `selfs` seminorm of `g`, with a constant independent of `g`.
-/
theorem souzaPointwiseMultiplierNorm_le_const_mul_selfsTailNorm
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p q qtilde : ℝ≥0∞) (t : ℕ)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)] :
    ∃ Cmult : ℝ,
      0 ≤ Cmult ∧
      ∀ g : α → ℂ,
        SouzaPointwiseSelfsTailClass G β p qtilde hβ hp hp_top t g →
        WeakGridSpace.pointwiseMultiplierNorm
            (A := souzaAtomFamily G s p hs hp hp_top) q g ≤
          Cmult * souzaPointwiseSelfsTailNorm G β p qtilde hβ hp hp_top t g := by
  obtain ⟨Cmult, hCmult_nonneg, hCmult⟩ :=
    exists_souzaSelfsMultiplierConstant
      G s β p q qtilde t hs hβ hβs hβ_lt_inv hp hp_top
  refine ⟨Cmult, hCmult_nonneg, ?_⟩
  intro g hg
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hden : (0 : ℝ) < Cmult + 1 := by linarith
  have hδ : 0 < ε / (Cmult + 1) := by positivity
  obtain ⟨C, hC_bound, hC_lt⟩ :=
    exists_souzaPointwiseSelfsTailBound_lt_norm_add
      G β p qtilde hβ hp hp_top hg hδ
  have hnorm_le :
      WeakGridSpace.pointwiseMultiplierNorm
          (A := souzaAtomFamily G s p hs hp hp_top) q g ≤ Cmult * C :=
    WeakGridSpace.pointwiseMultiplierNorm_le_of_bound (hCmult g C hC_bound)
  have hfrac : Cmult * (ε / (Cmult + 1)) ≤ ε := by
    have hratio : Cmult / (Cmult + 1) ≤ (1 : ℝ) :=
      (div_le_one hden).2 (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hratio hε.le
    calc
      Cmult * (ε / (Cmult + 1)) = (Cmult / (Cmult + 1)) * ε := by ring
      _ ≤ 1 * ε := hmul
      _ = ε := one_mul ε
  calc
    WeakGridSpace.pointwiseMultiplierNorm
        (A := souzaAtomFamily G s p hs hp hp_top) q g
        ≤ Cmult * C := hnorm_le
    _ ≤ Cmult *
          (souzaPointwiseSelfsTailNorm G β p qtilde hβ hp hp_top t g +
            ε / (Cmult + 1)) :=
      mul_le_mul_of_nonneg_left hC_lt.le hCmult_nonneg
    _ = Cmult * souzaPointwiseSelfsTailNorm G β p qtilde hβ hp hp_top t g +
          Cmult * (ε / (Cmult + 1)) := by ring
    _ ≤ Cmult * souzaPointwiseSelfsTailNorm G β p qtilde hβ hp hp_top t g +
          ε := by linarith

end

end GoodGridSpace
