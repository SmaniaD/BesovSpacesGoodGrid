import BesovSpacesGoodGrid.GoodGridBesovSpace
import BesovSpacesGoodGrid.WeakGridDirectAtoms
import BesovSpacesGoodGrid.WeakGridDirectBesovishSpaces

/-!
# Direct `L^p` Besov spaces on a good grid

This file contains the local-Banach-free variants of the good-grid Besov
constructions.  The atoms are ambient `L^p` vectors, either arbitrary
cell-supported size atoms or Souza atoms of the form `c • 1_Q`.
-/

namespace GoodGridSpace

open scoped ENNReal MeasureTheory

variable {α : Type*} [MeasurableSpace α]

noncomputable section

/--
The `L^p` class of the indicator of a good-grid cell.

This is the reusable anchor for the direct Souza atoms: a scalar `c` gives the
ambient `L^p` atom `c • directSouzaOneAtom G p Q`.
-/
noncomputable def directSouzaOneAtom (G : GoodGridSpace (α := α))
    (p : ℝ≥0∞) (Q : GoodGridCell G) :
    MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure := by
  have hQmeas : MeasurableSet Q.cell :=
    G.grid.grid.measurable Q.level Q.cell Q.mem
  have hQfinite : G.grid.μ Q.cell ≠ ∞ := by
    letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ Q.cell
  exact MeasureTheory.MemLp.toLp (Q.cell.indicator fun _ : α => (1 : ℂ))
    (by
      simpa [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
        WeakGridSpace.WeakGridSpace.measure] using
        (MeasureTheory.memLp_indicator_const (μ := G.grid.μ) (s := Q.cell)
          (p := p) hQmeas (1 : ℂ) (Or.inr hQfinite)))

/--
The direct `L^p` Souza atom predicate.

An atom on `Q` is an ambient `L^p` vector represented by a scalar multiple of
the cell indicator.  We keep both the classical coefficient bound and the
ambient `L^p` size bound as part of the predicate, so the definition interfaces
directly with `WeakGridSpace.LpAtomFamily`.
-/
def IsDirectSouzaAtom (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G) (f : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) :
    Prop :=
  ∃ c : ℂ,
    ‖c‖ ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) ∧
      f = c • directSouzaOneAtom G p Q ∧
        ‖f‖ ≤ (G.grid.μ Q.cell).toReal ^ s

/-- The direct cell-indicator atom is supported on its cell, modulo null sets. -/
theorem directSouzaOneAtom_supported (G : GoodGridSpace (α := α))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (Q : GoodGridCell G) :
    WeakGridSpace.LpSupportedOn G.toWeakGridSpace p Q.toWeakGridCell
      (directSouzaOneAtom G p Q) := by
  classical
  have hQmeas : MeasurableSet Q.cell :=
    G.grid.grid.measurable Q.level Q.cell Q.mem
  have hQfinite : G.grid.μ Q.cell ≠ ∞ := by
    letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ Q.cell
  let hmem :
      MeasureTheory.MemLp (Q.cell.indicator fun _ : α => (1 : ℂ))
        p G.toWeakGridSpace.measure := by
    simpa [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
      WeakGridSpace.WeakGridSpace.measure] using
      (MeasureTheory.memLp_indicator_const (μ := G.grid.μ) (s := Q.cell)
        (p := p) hQmeas (1 : ℂ) (Or.inr hQfinite))
  unfold WeakGridSpace.LpSupportedOn directSouzaOneAtom
  filter_upwards [MeasureTheory.ae_restrict_mem hQmeas.compl,
    MeasureTheory.ae_restrict_of_ae (MeasureTheory.MemLp.coeFn_toLp hmem)] with x hx hcoe
  have hxQ : x ∉ Q.cell := by
    simpa [GoodGridCell.toWeakGridCell] using hx
  rw [hcoe]
  simp [hxQ]

private theorem isDirectSouzaAtom_convex (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (Q : GoodGridCell G) :
    Convex ℝ {f : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure |
      IsDirectSouzaAtom G s p Q f} := by
  intro f hf g hg a b ha hb hab
  rcases hf with ⟨c, hc, rfl, hf_norm⟩
  rcases hg with ⟨d, hd, rfl, hg_norm⟩
  refine ⟨(a : ℂ) * c + (b : ℂ) * d, ?_, ?_, ?_⟩
  · calc
      ‖(a : ℂ) * c + (b : ℂ) * d‖ ≤ ‖(a : ℂ) * c‖ + ‖(b : ℂ) * d‖ :=
        norm_add_le ((a : ℂ) * c) ((b : ℂ) * d)
      _ = ‖a‖ * ‖c‖ + ‖b‖ * ‖d‖ := by
        simp
      _ ≤ ‖a‖ * ((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)) +
          ‖b‖ * ((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
      _ = (a + b) * ((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)) := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
            ring
      _ = (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) := by
            rw [hab, one_mul]
  · simp [add_smul, mul_smul]
    rfl
  · have ha_norm :
        ‖a • (c • directSouzaOneAtom G p Q)‖ =
          ‖a‖ * ‖c • directSouzaOneAtom G p Q‖ :=
      norm_smul a (c • directSouzaOneAtom G p Q)
    have hb_norm :
        ‖b • (d • directSouzaOneAtom G p Q)‖ =
          ‖b‖ * ‖d • directSouzaOneAtom G p Q‖ :=
      norm_smul b (d • directSouzaOneAtom G p Q)
    calc
      ‖a • (c • directSouzaOneAtom G p Q) + b • (d • directSouzaOneAtom G p Q)‖
          ≤ ‖a • (c • directSouzaOneAtom G p Q)‖ +
              ‖b • (d • directSouzaOneAtom G p Q)‖ :=
            norm_add_le _ _
      _ = ‖a‖ * ‖c • directSouzaOneAtom G p Q‖ +
          ‖b‖ * ‖d • directSouzaOneAtom G p Q‖ := by
            rw [ha_norm, hb_norm]
      _ ≤ ‖a‖ * ((G.grid.μ Q.cell).toReal ^ s) +
          ‖b‖ * ((G.grid.μ Q.cell).toReal ^ s) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hf_norm (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hg_norm (norm_nonneg _))
      _ = (a + b) * ((G.grid.μ Q.cell).toReal ^ s) := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
            ring
      _ = (G.grid.μ Q.cell).toReal ^ s := by
            rw [hab, one_mul]

/-- Direct Souza atoms are invariant under multiplication by a complex phase. -/
theorem isDirectSouzaAtom_phase_invariant (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (Q : GoodGridCell G)
    {f : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure} {σ : ℂ}
    (hf : IsDirectSouzaAtom G s p Q f) (hσ : ‖σ‖ = (1 : ℝ)) :
    IsDirectSouzaAtom G s p Q (σ • f) := by
  rcases hf with ⟨c, hc, rfl, hf_norm⟩
  refine ⟨σ * c, ?_, ?_, ?_⟩
  · calc
      ‖σ * c‖ = ‖σ‖ * ‖c‖ := norm_mul σ c
      _ = ‖c‖ := by rw [hσ, one_mul]
      _ ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) := hc
  · simp [mul_smul]
  · calc
      ‖σ • (c • directSouzaOneAtom G p Q)‖ = ‖σ‖ * ‖c • directSouzaOneAtom G p Q‖ :=
        norm_smul σ (c • directSouzaOneAtom G p Q)
      _ = ‖c • directSouzaOneAtom G p Q‖ := by rw [hσ, one_mul]
      _ ≤ (G.grid.μ Q.cell).toReal ^ s := hf_norm

/--
Souza atoms packaged as a direct `L^p` atom family.

This is the direct counterpart of `souzaAtomFamily`: atoms are subsets of the
ambient `L^p` space, with no local Banach space in the data.
-/
noncomputable def directSouzaAtomFamily (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) [Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    WeakGridSpace.LpAtomFamily G.toWeakGridSpace s p where
  s_pos := hs
  one_le_p := Fact.out
  p_ne_top := hp_top
  atoms := fun Q =>
    {f : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure |
      IsDirectSouzaAtom G s p ⟨Q.level, Q.cell, Q.mem⟩ f}
  atoms_nonempty := by
    intro Q
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_, ?_⟩
    · simpa using
        (Real.rpow_nonneg ENNReal.toReal_nonneg (s - (p.toReal)⁻¹) :
          0 ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹))
    · simp
    · calc
        ‖(0 : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure)‖ = 0 := norm_zero
        _ ≤ (G.grid.μ Q.cell).toReal ^ s := Real.rpow_nonneg ENNReal.toReal_nonneg _
  atoms_supported := by
    intro Q f hf
    rcases hf with ⟨c, _hc, rfl, _hbound⟩
    exact WeakGridSpace.lpSupportedOn_smul G.toWeakGridSpace p Q c
      (directSouzaOneAtom_supported G p ⟨Q.level, Q.cell, Q.mem⟩)
  atoms_convex := by
    intro Q
    exact isDirectSouzaAtom_convex G s p ⟨Q.level, Q.cell, Q.mem⟩
  atoms_phase_invariant := by
    intro Q f σ hf hσ
    exact isDirectSouzaAtom_phase_invariant G s p ⟨Q.level, Q.cell, Q.mem⟩ hf hσ
  atom_bound := by
    intro Q f hf
    rcases hf with ⟨_c, _hc, _hrep, hnorm⟩
    simpa [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
      WeakGridSpace.WeakGridSpace.measure] using hnorm

/--
The Besov-ish space built from the direct `L^p` Souza atom family.

This is the local-Banach-free counterpart of `SouzaBesovSpace`; its atoms are
ambient `L^p` vectors of the form `c • 1_Q`.
-/
noncomputable def DirectSouzaBesovSpace (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ q)] :
    Submodule ℂ (MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  exact WeakGridSpace.DirectLpBesovishSpace (directSouzaAtomFamily G s p hs hp_top) q

/-- Membership in the direct `L^p` Souza Besov-ish space. -/
def MemDirectSouzaBesov (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ q)]
    (g : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) : Prop :=
  g ∈ DirectSouzaBesovSpace G s p q hs hp hp_top

/--
The direct `L^p` size-atom Besov-ish space associated to a `GoodGridSpace`.

This is the new a.e./`L^p`-native model specialized to the weak grid induced
by `G`. Its atoms are all ambient `L^p` vectors supported on a cell and
bounded by `μ(Q)^s` in `L^p` norm; unlike `SouzaBesovSpace`, no pointwise
constant representative is part of the definition.
-/
noncomputable def DirectLpSizeBesovSpace (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ q)] :
    Submodule ℂ (MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  exact WeakGridSpace.LpSizeBesovishSpace G.toWeakGridSpace s p q hs hp_top

/-- Membership in the direct `L^p` size-atom Besov-ish space. -/
def MemDirectLpSizeBesov (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ q)]
    (g : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) : Prop :=
  g ∈ DirectLpSizeBesovSpace G s p q hs hp hp_top

end

end GoodGridSpace
