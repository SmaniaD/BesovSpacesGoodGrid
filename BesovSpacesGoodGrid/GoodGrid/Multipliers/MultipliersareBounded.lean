import BesovSpacesGoodGrid.GoodGrid.BesovAtoms
import BesovSpacesGoodGrid.GoodGrid.Multipliers.Definition
import BesovSpacesGoodGrid.GoodGrid.Multipliers.Besovspq

/-!
# The `selfs` class is bounded

This file contains the first quantitative step in the proof that Souza
`selfs` multipliers are essentially bounded: a `selfs` bound controls the
ambient `L^p` norm of the product with every normalized Souza atom.
-/

open scoped ENNReal Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
The constant in the Souza Besov embedding into the ambient `L^p` space.

For a good grid the overlap constant is definitionally `1`, but we keep the
same expression as the abstract weak-grid embedding so this result can be
reused without unfolding that implementation detail.
-/
noncomputable def souzaBesovLpEmbeddingConstant
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞) : ℝ :=
  ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
    WeakGridSpace.LpGridRepresentation.cCoefficient p q
      (fun k =>
        (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
          G.toWeakGridSpace s p p k) ^ p.toReal)

/--
The local `L^p` embedding constant for the Souza Besov space on the grid
induced by a cell.
-/
noncomputable def inducedSouzaBesovLpEmbeddingConstant
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G)
    (s : ℝ) (p q : ℝ≥0∞) : ℝ :=
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  ((Wi.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
    WeakGridSpace.LpGridRepresentation.cCoefficient p q
      (fun k =>
        (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
          Wi s p p k) ^ p.toReal)

/--
The uniform geometric constant controlling all induced `L^p` embeddings on
good-grid cells.

The induced-grid constant itself carries a factor `μ(Q)^s`; this definition is
the part that does not depend on the cell.
-/
noncomputable def souzaBesovLpLocalEmbeddingConstant
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞) : ℝ :=
  WeakGridSpace.LpGridRepresentation.cCoefficient p q
    (besovAtomGeometricWeight G s p)

/--
The induced Souza embedding constant has the expected cell scale.
-/
theorem inducedSouzaBesovLpEmbeddingConstant_le_cellScale
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G)
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    inducedSouzaBesovLpEmbeddingConstant G Q s p q ≤
      (G.grid.μ Q.cell).toReal ^ s *
        souzaBesovLpLocalEmbeddingConstant G s p q := by
  classical
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  let Cind : ℝ :=
    WeakGridSpace.LpGridRepresentation.cCoefficient p q
      (fun k =>
        (WeakGridSpace.LpGridRepresentation.levelMeasureWeight Wi s p p k) ^ p.toReal)
  let Cgeom : ℝ :=
    WeakGridSpace.LpGridRepresentation.cCoefficient p q
      (besovAtomGeometricWeight G s p)
  let M : ℝ := (G.grid.μ Q.cell).toReal ^ s
  have hCemb_one :
      ((Wi.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) = 1 := by
    dsimp [Wi, WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid,
      GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid]
    norm_num
  have hCind_le : Cind ≤ M * Cgeom := by
    simpa [Wi, Cind, Cgeom, M] using
      induced_cCoefficient_le_geometric G Q s p q hs (inferInstance : Fact (1 ≤ p)) hp_top
  calc
    inducedSouzaBesovLpEmbeddingConstant G Q s p q
        = Cind := by
          dsimp [inducedSouzaBesovLpEmbeddingConstant, Cind]
          rw [hCemb_one]
          ring
    _ ≤ M * Cgeom := hCind_le
    _ = (G.grid.μ Q.cell).toReal ^ s *
        souzaBesovLpLocalEmbeddingConstant G s p q := by
          rfl

/--
The canonical Souza atom on a good-grid cell is an admissible `selfs` test.

The statement also records the concrete function represented by the chosen
`L^p` element, which is the bridge needed to turn the atom test into estimates
on cell indicators.
-/
theorem exists_canonicalSouzaAtomicUnit
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Q : GoodGridCell G) :
    ∃ x : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.AtomicUnit
        (A := souzaAtomFamily G s p hs hp hp_top) q x ∧
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (canonicalSouzaAtom G s p Q)
        (x : Lp ℂ p G.toWeakGridSpace.measure) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let c : ℂ := (((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)
  let xLp : Lp ℂ p G.toWeakGridSpace.measure :=
    MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
      (G.grid.grid.measurable Q.level Q.cell Q.mem)
      (GoodGridCell.measure_ne_top Q) c
  have hx_mem : xLp ∈ SouzaBesovSpace G s p q hs hp hp_top := by
    simpa [xLp, c] using
      indicatorConstLp_cell_mem_souzaBesov G s p q hs hp hp_top Q c
  let x : WeakGridSpace.BesovishSpace A q := ⟨xLp, by
    simpa [A, SouzaBesovSpace] using hx_mem⟩
  refine ⟨x, ?_, ?_⟩
  · refine ⟨Q.toWeakGridCell, c, ?_, ?_⟩
    · have hc_nonneg :
          0 ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) :=
        Real.rpow_nonneg ENNReal.toReal_nonneg _
      change ‖c‖ ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)
      simp [c, Complex.norm_real, Real.norm_of_nonneg hc_nonneg]
    · have hxcoe :
          ((xLp : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
            =ᵐ[G.toWeakGridSpace.measure] Q.cell.indicator (fun _ => c) :=
        MeasureTheory.indicatorConstLp_coeFn (μ := G.toWeakGridSpace.measure)
          (p := p) (hs := G.grid.grid.measurable Q.level Q.cell Q.mem)
          (hμs := GoodGridCell.measure_ne_top Q) (c := c)
      simpa [WeakGridSpace.RepresentsFunction, A, WeakGridSpace.AtomFamily.toFunction,
        souzaAtomFamily, souzaLocalVectorSpace, GoodGridCell.toWeakGridCell, x] using hxcoe
  · have hxcoe :
        ((xLp : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
          =ᵐ[G.toWeakGridSpace.measure] Q.cell.indicator (fun _ => c) :=
      MeasureTheory.indicatorConstLp_coeFn (μ := G.toWeakGridSpace.measure)
        (p := p) (hs := G.grid.grid.measurable Q.level Q.cell Q.mem)
        (hμs := GoodGridCell.measure_ne_top Q) (c := c)
    refine hxcoe.trans (Filter.Eventually.of_forall ?_)
    intro z
    by_cases hz : z ∈ Q.cell
    · simp [canonicalSouzaAtom, c, hz]
    · simp [canonicalSouzaAtom, c, hz]

/--
A `selfs` bound controls the `L^p` norm of the product with any normalized
Souza atom.

This is the formal version of the estimate obtained in the paper by testing
`g` on one atom and then applying the Besov-to-`L^p` embedding with `t = p`.
The remaining step toward the full `L^\infty` theorem is the martingale/Levy
argument turning the resulting uniform cell-average bounds into an essential
supremum bound.
-/
theorem souzaPointwiseSelfsBound_atomicUnit_product_eLpNorm_le
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m : α → ℂ} {C : ℝ}
    (hC : WeakGridSpace.PointwiseSelfsBound
      (A := souzaAtomFamily G s p hs hp hp_top) q m C)
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (hx : WeakGridSpace.AtomicUnit
      (A := souzaAtomFamily G s p hs hp hp_top) q x) :
    ∃ y : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := G.toWeakGridSpace) (p := p) m
        (x : Lp ℂ p G.toWeakGridSpace.measure)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      (eLpNorm ((y : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
        p G.toWeakGridSpace.measure).toReal ≤
        souzaBesovLpEmbeddingConstant G s p q * C := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  rcases hC.2 x hx with ⟨y, hprod, hy_cost⟩
  refine ⟨y, hprod, ?_⟩
  have hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / p.toReal := by
    linarith [hs.le]
  have ht_le_pu : p ≤ p * (∞ : ℝ≥0∞) := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * (∞ : ℝ≥0∞) := by
        exact mul_le_mul_right le_top p
  have hAfinite :
      WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations (A := A) q :=
    WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := A) q
  have hLp :
      (eLpNorm ((y : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
        p G.toWeakGridSpace.measure).toReal ≤
        souzaBesovLpEmbeddingConstant G s p q *
          WeakGridSpace.BesovishSpace.Norm_Costpq A q y := by
    simpa [souzaBesovLpEmbeddingConstant, A] using
      WeakGridSpace.BesovishSpace.lp_norm_le_const_mul_Norm_Costpq
        (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
        (A := A) (t := p)
        hp_top hp_top le_rfl ht_le_pu hs_nonneg
        (souza_assumptionG2 G s p q hs hp hp_top).1 hAfinite y
  have hconst_nonneg : 0 ≤ souzaBesovLpEmbeddingConstant G s p q := by
    dsimp [souzaBesovLpEmbeddingConstant]
    exact mul_nonneg
      (by positivity)
      (WeakGridSpace.LpGridRepresentation.cCoefficient_nonneg p q
        (fun k =>
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s p p k) ^ p.toReal)
        (fun k => Real.rpow_nonneg
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg
            G.toWeakGridSpace s p p k) _))
  calc
    (eLpNorm ((y : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
        p G.toWeakGridSpace.measure).toReal
        ≤ souzaBesovLpEmbeddingConstant G s p q *
            WeakGridSpace.BesovishSpace.Norm_Costpq A q y := hLp
    _ ≤ souzaBesovLpEmbeddingConstant G s p q * C :=
      mul_le_mul_of_nonneg_left hy_cost hconst_nonneg

/--
A `selfs` bound controls the concrete product with the canonical Souza atom on
each good-grid cell.
-/
theorem souzaPointwiseSelfsBound_canonicalAtom_product_eLpNorm_le
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m : α → ℂ} {C : ℝ}
    (hC : WeakGridSpace.PointwiseSelfsBound
      (A := souzaAtomFamily G s p hs hp hp_top) q m C)
    (Q : GoodGridCell G) :
    ∃ y : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => m z * canonicalSouzaAtom G s p Q z)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      (eLpNorm ((y : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
        p G.toWeakGridSpace.measure).toReal ≤
        souzaBesovLpEmbeddingConstant G s p q * C := by
  classical
  rcases exists_canonicalSouzaAtomicUnit G s p q hs hp hp_top Q with
    ⟨x, hx_unit, hx_rep⟩
  rcases souzaPointwiseSelfsBound_atomicUnit_product_eLpNorm_le
      G s p q hs hp hp_top hC x hx_unit with
    ⟨y, hprod, hy_bound⟩
  refine ⟨y, ?_, hy_bound⟩
  filter_upwards [hprod, hx_rep] with z hprod_z hx_z
  calc
    ((y : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z
        = m z * ((x : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) z := hprod_z
    _ = m z * canonicalSouzaAtom G s p Q z := by rw [hx_z]

/--
A cost bound in the Souza Besov space induced on a cell controls the local
`L^p` norm on that induced grid.
-/
theorem inducedSouzaBesov_eLpNorm_le
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G)
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (y : WeakGridSpace.BesovishSpace
      (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
        (souzaAtomFamily G s p hs hp hp_top)) q) :
    (eLpNorm
        ((y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure) :
          α → ℂ)
        p
        (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure).toReal ≤
      inducedSouzaBesovLpEmbeddingConstant G Q s p q *
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q y := by
  classical
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
    (souzaAtomFamily G s p hs hp hp_top)
  have hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / p.toReal := by
    linarith [hs.le]
  have ht_le_pu : p ≤ p * (∞ : ℝ≥0∞) := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * (∞ : ℝ≥0∞) := by
        exact mul_le_mul_right le_top p
  have hAfinite :
      WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations (A := Ai) q :=
    WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := Ai) q
  have hG2 :
      WeakGridSpace.AssumptionG2 Wi s p ∞ q :=
    induced_souza_assumptionG2 G s p q hs hp hp_top Q
  simpa [inducedSouzaBesovLpEmbeddingConstant, Wi, Ai] using
    WeakGridSpace.BesovishSpace.lp_norm_le_const_mul_Norm_Costpq
      (G := Wi) (s := s) (p := p) (u := ∞) (q := q)
      (A := Ai) (t := p)
      hp_top hp_top le_rfl ht_le_pu hs_nonneg hG2.1 hAfinite y

/--
Conditional local estimate for the product with a canonical Souza atom.

If restriction from the ambient Souza Besov space to the grid induced by `Q`
has operator bound `D`, then a `selfs` bound controls the induced `L^p` norm
of `m * a_Q` with the correct cell factor `μ(Q)^s`.
-/
theorem souzaPointwiseSelfsBound_restrictedCanonicalAtom_eLpNorm_le_of_restrictsToInduced
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G)
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m : α → ℂ} {C D : ℝ}
    (hC : WeakGridSpace.PointwiseSelfsBound
      (A := souzaAtomFamily G s p hs hp hp_top) q m C)
    (hD : 0 ≤ D)
    (hrestrict :
      ∀ x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q,
        ∃ y : WeakGridSpace.BesovishSpace
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q,
          WeakGridSpace.RepresentsPointwiseProduct
            (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell)
            (p := p) (Q.cell.indicator fun _ => (1 : ℂ))
            (x : Lp ℂ p G.toWeakGridSpace.measure)
            (y : Lp ℂ p
              (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
                (souzaAtomFamily G s p hs hp hp_top)) q y ≤
            D * WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q x) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsFunction
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell)
        (p := p)
        (fun z => Q.cell.indicator (fun _ => (1 : ℂ)) z *
          (m z * canonicalSouzaAtom G s p Q z))
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure) ∧
      (eLpNorm
          ((y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure) :
            α → ℂ)
          p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure).toReal ≤
        (G.grid.μ Q.cell).toReal ^ s *
          souzaBesovLpLocalEmbeddingConstant G s p q * D * C := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell A
  rcases exists_canonicalSouzaAtomicUnit G s p q hs hp hp_top Q with
    ⟨x, hx_unit, hx_rep⟩
  rcases hC.2 x hx_unit with ⟨z, hz_prod, hz_norm⟩
  rcases hrestrict z with ⟨y, hy_prod, hy_norm⟩
  refine ⟨y, ?_, ?_⟩
  · have hz_prod_i :
        ((z : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
          =ᵐ[Wi.measure]
            fun t => m t * ((x : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) t := by
      simpa [Wi, WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid,
        GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
        WeakGridSpace.WeakGridSpace.measure] using hz_prod
    have hx_rep_i :
        ((x : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
          =ᵐ[Wi.measure] canonicalSouzaAtom G s p Q := by
      simpa [Wi, WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid,
        GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
        WeakGridSpace.WeakGridSpace.measure] using hx_rep
    filter_upwards [hy_prod, hz_prod_i, hx_rep_i] with t hy_t hz_t hx_t
    calc
      ((y : Lp ℂ p Wi.measure) : α → ℂ) t
          = Q.cell.indicator (fun _ => (1 : ℂ)) t *
              ((z : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) t := hy_t
      _ = Q.cell.indicator (fun _ => (1 : ℂ)) t *
            (m t * ((x : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) t) := by rw [hz_t]
      _ = Q.cell.indicator (fun _ => (1 : ℂ)) t *
            (m t * canonicalSouzaAtom G s p Q t) := by rw [hx_t]
  · have hind_nonneg : 0 ≤ inducedSouzaBesovLpEmbeddingConstant G Q s p q := by
      dsimp [inducedSouzaBesovLpEmbeddingConstant]
      exact mul_nonneg
        (by positivity)
        (WeakGridSpace.LpGridRepresentation.cCoefficient_nonneg p q
          (fun k =>
            (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
              Wi s p p k) ^ p.toReal)
          (fun k => Real.rpow_nonneg
            (WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg
              Wi s p p k) _))
    have hAfinite :
        WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations (A := A) q :=
      WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := A) q
    have hz_norm_nonneg :
        0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A q z :=
      WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
        (A := A) (q := q) hAfinite z
    have hy_norm_le : WeakGridSpace.BesovishSpace.Norm_Costpq Ai q y ≤ D * C := by
      calc
        WeakGridSpace.BesovishSpace.Norm_Costpq Ai q y
            ≤ D * WeakGridSpace.BesovishSpace.Norm_Costpq A q z := by
              simpa [A, Ai] using hy_norm
        _ ≤ D * C := mul_le_mul_of_nonneg_left hz_norm hD
    have hDC_nonneg : 0 ≤ D * C := mul_nonneg hD hC.1
    have hscale :
        inducedSouzaBesovLpEmbeddingConstant G Q s p q ≤
          (G.grid.μ Q.cell).toReal ^ s *
            souzaBesovLpLocalEmbeddingConstant G s p q :=
      inducedSouzaBesovLpEmbeddingConstant_le_cellScale G Q s p q hs hp_top
    calc
      (eLpNorm
          ((y : Lp ℂ p Wi.measure) : α → ℂ)
          p Wi.measure).toReal
          ≤ inducedSouzaBesovLpEmbeddingConstant G Q s p q *
              WeakGridSpace.BesovishSpace.Norm_Costpq Ai q y := by
            simpa [Wi, Ai, A] using
              inducedSouzaBesov_eLpNorm_le G Q s p q hs hp hp_top y
      _ ≤ inducedSouzaBesovLpEmbeddingConstant G Q s p q * (D * C) :=
            mul_le_mul_of_nonneg_left hy_norm_le hind_nonneg
      _ ≤ ((G.grid.μ Q.cell).toReal ^ s *
            souzaBesovLpLocalEmbeddingConstant G s p q) * (D * C) :=
            mul_le_mul_of_nonneg_right hscale hDC_nonneg
      _ = (G.grid.μ Q.cell).toReal ^ s *
          souzaBesovLpLocalEmbeddingConstant G s p q * D * C := by
            ring

end

end GoodGridSpace
