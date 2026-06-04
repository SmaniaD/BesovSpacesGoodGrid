import BesovSpacesGoodGrid.GoodGrid.BesovSpace
import BesovSpacesGoodGrid.WeakGrid.InducedGrid
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Mean oscillation norm on a good grid

This file records the mean-oscillation gauge from the manuscript.  The local
oscillation is defined as an infimum over constants of the `L^p` seminorm of
`f - c` restricted to a grid cell.  The global gauge is allowed to take the
value `∞`, since no summability is assumed for an arbitrary function.
-/

open scoped ENNReal BigOperators
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace MeanOscillation

/--
The canonical restriction map between `Lp` spaces when the target measure is
dominated by the source measure.

This is a small local tool for passing an atomic `HasSum` in the ambient
measure to the same `HasSum` after restricting the measure to a grid cell.
-/
noncomputable def lpRestrictMeasure
    (μ ν : Measure α) (hνμ : ν ≤ μ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℂ p μ →L[ℂ] Lp ℂ p ν := by
  refine LinearMap.mkContinuous
    { toFun := fun (f : Lp ℂ p μ) => MemLp.toLp f ((Lp.memLp f).mono_measure hνμ)
      map_add' := by
        intro (f : Lp ℂ p μ) (g : Lp ℂ p μ)
        let hf : MeasureTheory.MemLp f p ν := (Lp.memLp f).mono_measure hνμ
        let hg : MeasureTheory.MemLp g p ν := (Lp.memLp g).mono_measure hνμ
        let hfg : MeasureTheory.MemLp (f + g) p ν := (Lp.memLp (f + g)).mono_measure hνμ
        change hfg.toLp (f + g) = hf.toLp f + hg.toLp g
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _
          ((Lp.coeFn_add f g).filter_mono (ae_mono hνμ))
      map_smul' := by
        intro c (f : Lp ℂ p μ)
        let hf : MeasureTheory.MemLp f p ν := (Lp.memLp f).mono_measure hνμ
        let hcf : MeasureTheory.MemLp (c • f) p ν := (Lp.memLp (c • f)).mono_measure hνμ
        change hcf.toLp (c • f) = c • hf.toLp f
        rw [← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _
          ((Lp.coeFn_smul c f).filter_mono (ae_mono hνμ)) }
    1 ?_
  intro f
  calc
    ‖MemLp.toLp f ((Lp.memLp f).mono_measure hνμ)‖
        = (MeasureTheory.eLpNorm f p ν).toReal := by
          rw [Lp.norm_def]
          exact congrArg ENNReal.toReal <|
            MeasureTheory.eLpNorm_congr_ae
              (MemLp.coeFn_toLp ((Lp.memLp f).mono_measure hνμ))
    _ ≤ (MeasureTheory.eLpNorm f p μ).toReal := by
          exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
            (MeasureTheory.eLpNorm_mono_measure f hνμ)
    _ = 1 * ‖f‖ := by rw [Lp.norm_def, one_mul]

/-- The restriction map preserves the underlying representative a.e. for the restricted measure. -/
theorem lpRestrictMeasure_coeFn
    (μ ν : Measure α) (hνμ : ν ≤ μ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp ℂ p μ) :
    (lpRestrictMeasure μ ν hνμ p f : α → ℂ) =ᵐ[ν] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_measure hνμ)

/--
The local mean oscillation of `f` on a good-grid cell `Q`.

For finite `p`, this is the infimum over constants of
`(∫_Q ‖f - c‖^p)^(1/p)`.  For `p = ∞`, the same formula uses Mathlib's
`eLpNorm`, hence becomes the essential-supremum oscillation on `Q`.
-/
def osc (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (f : α → ℂ) (Q : GoodGridCell G) : ℝ≥0∞ :=
  sInf (Set.range fun c : ℂ =>
    MeasureTheory.eLpNorm (fun x => f x - c) p (G.grid.μ.restrict Q.cell))

/--
The local oscillation is bounded by the `L^p` distance to any fixed constant.

This is the formal version of choosing an arbitrary test constant in the
infimum defining `osc_p(f,Q)`.
-/
theorem osc_le_eLpNorm_sub_const (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (f : α → ℂ) (Q : GoodGridCell G) (c : ℂ) :
    osc G p f Q ≤
      MeasureTheory.eLpNorm (fun x => f x - c) p (G.grid.μ.restrict Q.cell) := by
  unfold osc
  exact sInf_le (Set.mem_range.mpr ⟨c, rfl⟩)

/--
If subtracting a chosen constant from `f` agrees with `g` on a cell, then the
oscillation of `f` on that cell is bounded by the local `L^p` norm of `g`.
-/
theorem osc_le_eLpNorm_of_sub_eq_on_cell (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (f g : α → ℂ) (Q : GoodGridCell G) (c : ℂ)
    (hfg : ∀ x ∈ Q.cell, f x - c = g x) :
    osc G p f Q ≤ MeasureTheory.eLpNorm g p (G.grid.μ.restrict Q.cell) := by
  calc
    osc G p f Q
        ≤ MeasureTheory.eLpNorm (fun x => f x - c) p (G.grid.μ.restrict Q.cell) :=
          osc_le_eLpNorm_sub_const G p f Q c
    _ = MeasureTheory.eLpNorm g p (G.grid.μ.restrict Q.cell) := by
      refine MeasureTheory.eLpNorm_congr_ae ?_
      filter_upwards [ae_restrict_mem (G.grid.grid.measurable Q.level Q.cell Q.mem)] with x hx
      exact hfg x hx

/-- The local oscillation only depends on the a.e. class on the cell. -/
theorem osc_congr_ae (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (f g : α → ℂ) (Q : GoodGridCell G)
    (hfg : f =ᵐ[G.grid.μ.restrict Q.cell] g) :
    osc G p f Q = osc G p g Q := by
  unfold osc
  congr 1
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    exact MeasureTheory.eLpNorm_congr_ae <| hfg.mono fun x hx => by simp [hx]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    exact MeasureTheory.eLpNorm_congr_ae <| hfg.symm.mono fun x hx => by simp [hx]

/--
If `f` is almost everywhere constant on a cell, then its oscillation on that
cell is zero.
-/
theorem osc_eq_zero_of_ae_eq_const (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (f : α → ℂ) (Q : GoodGridCell G) (c : ℂ)
    (hf : f =ᵐ[G.grid.μ.restrict Q.cell] fun _ => c) :
    osc G p f Q = 0 := by
  apply le_antisymm
  · calc
      osc G p f Q
          ≤ MeasureTheory.eLpNorm (fun x => f x - c) p (G.grid.μ.restrict Q.cell) :=
            osc_le_eLpNorm_sub_const G p f Q c
      _ = 0 := by
            have hzero :
                (fun x => f x - c) =ᵐ[G.grid.μ.restrict Q.cell] fun _ => 0 := by
              filter_upwards [hf] with x hx
              simp [hx]
            rw [MeasureTheory.eLpNorm_congr_ae hzero]
            simp
  · exact bot_le

/--
If `f` is pointwise constant on a cell, then its oscillation on that cell is
zero.
-/
theorem osc_eq_zero_of_eq_const_on_cell (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (f : α → ℂ) (Q : GoodGridCell G) (c : ℂ)
    (hf : ∀ x ∈ Q.cell, f x = c) :
    osc G p f Q = 0 := by
  refine osc_eq_zero_of_ae_eq_const G p f Q c ?_
  filter_upwards [ae_restrict_mem (G.grid.grid.measurable Q.level Q.cell Q.mem)] with x hx
  exact hf x hx

/--
The level-`k` contribution to the mean-oscillation gauge.

It is `∑_{Q ∈ P^k} μ(Q)^(-s p) osc_p(f,Q)^p`.
-/
def levelOscillationBlock (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (k : ℕ) : ℝ≥0∞ :=
  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    (G.grid.μ Q.1) ^ (-(s * p.toReal)) *
      (osc G p f ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G)) ^ p.toReal

/-- The level oscillation block only depends on the global a.e. class. -/
theorem levelOscillationBlock_congr_ae
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (f g : α → ℂ) (k : ℕ)
    (hfg : f =ᵐ[G.grid.μ] g) :
    levelOscillationBlock G s p f k = levelOscillationBlock G s p g k := by
  unfold levelOscillationBlock
  refine Finset.sum_congr rfl ?_
  intro Q _hQ
  rw [osc_congr_ae G p f g
    ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G)
    (ae_restrict_of_ae hfg)]


/--
The oscillation seminorm `osc^s_{p,q}`.

For `q = ∞` this is the supremum over levels.  Otherwise it is the usual
`ℓ^q(L^p)` aggregation of the level blocks.
-/
def oscillationSeminorm (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞) (f : α → ℂ) : ℝ≥0∞ :=
  if q = ∞ then
    sSup (Set.range fun k => (levelOscillationBlock G s p f k) ^ (1 / p.toReal))
  else
    (∑' k, (levelOscillationBlock G s p f k) ^ (q.toReal / p.toReal)) ^
      (1 / q.toReal)

/-- The oscillation seminorm only depends on the global a.e. class. -/
theorem oscillationSeminorm_congr_ae
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (f g : α → ℂ)
    (hfg : f =ᵐ[G.grid.μ] g) :
    oscillationSeminorm G s p q f = oscillationSeminorm G s p q g := by
  have hlevel : ∀ k, levelOscillationBlock G s p f k =
      levelOscillationBlock G s p g k :=
    fun k => levelOscillationBlock_congr_ae G s p f g k hfg
  by_cases hq : q = ∞
  · simp [oscillationSeminorm, hq, hlevel]
  · simp [oscillationSeminorm, hq, hlevel]

/--
The full mean-oscillation gauge `N_osc`.

The first term is `μ(I)^(-s) ‖f‖_p`, where `I = univ`; the second term is
`osc^s_{p,q}`.
-/
def meanOscillationNorm (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞) (f : α → ℂ) : ℝ≥0∞ :=
  (G.grid.μ Set.univ) ^ (-s) * MeasureTheory.eLpNorm f p G.grid.μ +
    oscillationSeminorm G s p q f

end MeanOscillation

end

end GoodGridSpace
