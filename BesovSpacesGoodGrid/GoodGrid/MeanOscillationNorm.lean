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
A Souza level block at a coarser level is pointwise constant on every finer
cell.

This is the local constancy used in the oscillation estimate: when `k ≤ k₀`,
each level-`k` Souza atom is either constant on the level-`k₀` cell `J`, or
vanishes there.
-/
theorem souzaLevelBlock_toFunLt_eq_on_finer_cell
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {k k₀ : ℕ} (hkk₀ : k ≤ k₀)
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    {x y : α} (hx : x ∈ J.1) (hy : y ∈ J.1) :
    B.toFunLt (souzaAtomFamily G s p hs hp hp_top) x =
      B.toFunLt (souzaAtomFamily G s p hs hp hp_top) y := by
  classical
  unfold WeakGridSpace.LevelBlock.toFunLt
  apply Finset.sum_congr rfl
  intro P _hP
  rcases G.grid.partition_subset_or_disjoint_of_le
      k k₀ hkk₀ P.1 P.2 J.1 J.2 with hsub | hdisj
  · have hxP : x ∈ P.1 := hsub hx
    have hyP : y ∈ P.1 := hsub hy
    dsimp [WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily, souzaLocalVectorSpace,
      WeakGridSpace.levelCellToWeakGridCell]
    rw [Set.indicator_of_mem hxP, Set.indicator_of_mem hyP]
  · have hxP : x ∉ P.1 := fun hxP => (Set.disjoint_left.mp hdisj hx hxP).elim
    have hyP : y ∉ P.1 := fun hyP => (Set.disjoint_left.mp hdisj hy hyP).elim
    dsimp [WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily, souzaLocalVectorSpace,
      WeakGridSpace.levelCellToWeakGridCell]
    rw [Set.indicator_of_notMem hxP, Set.indicator_of_notMem hyP]

/--
A finite sum of Souza level blocks with levels at most `k₀` is constant on each
level-`k₀` cell.
-/
theorem souzaFiniteBlockSum_toFunLt_eq_on_finer_cell
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {k₀ : ℕ} (S : Finset ℕ) (hS : ∀ k ∈ S, k ≤ k₀)
    (B : ∀ k, WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    {x y : α} (hx : x ∈ J.1) (hy : y ∈ J.1) :
    (∑ k ∈ S, (B k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x) =
      ∑ k ∈ S, (B k).toFunLt (souzaAtomFamily G s p hs hp hp_top) y := by
  refine Finset.sum_congr rfl ?_
  intro k hk
  exact souzaLevelBlock_toFunLt_eq_on_finer_cell
    (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
    (hkk₀ := hS k hk) (B := B k) (J := J) hx hy

/--
The finite low-frequency Souza part has zero oscillation on cells at the
endpoint level.
-/
theorem osc_eq_zero_souzaFiniteBlockSum_of_levels_le
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {k₀ : ℕ} (S : Finset ℕ) (hS : ∀ k ∈ S, k ≤ k₀)
    (B : ∀ k, WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀) :
    osc G p
        (fun x => ∑ k ∈ S, (B k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x)
        ({ level := k₀, cell := J.1, mem := J.2 } : GoodGridCell G) = 0 := by
  rcases G.grid.partition_nonempty k₀ J.1 J.2 with ⟨xJ, hxJ⟩
  refine osc_eq_zero_of_eq_const_on_cell G p _ _
    (∑ k ∈ S, (B k).toFunLt (souzaAtomFamily G s p hs hp hp_top) xJ) ?_
  intro x hx
  exact souzaFiniteBlockSum_toFunLt_eq_on_finer_cell
    (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
    (S := S) (hS := hS) (B := B) (J := J) hx hxJ

/--
The initial segment of a Souza representation up to level `k₀` has zero
oscillation on each level-`k₀` cell.

This is the representation-level version of the low-frequency constancy step
in the paper's oscillation estimate.
-/
theorem osc_eq_zero_souzaInitialSegment_of_levels_le
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    {k₀ : ℕ}
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀) :
    osc G p
        (fun x =>
          ∑ k ∈ Finset.range (k₀ + 1),
            (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x)
        ({ level := k₀, cell := J.1, mem := J.2 } : GoodGridCell G) = 0 := by
  refine osc_eq_zero_souzaFiniteBlockSum_of_levels_le
    (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
    (S := Finset.range (k₀ + 1)) (B := R.block) (J := J) ?_
  intro k hk
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)

/--
A finite Souza block sum in `Lp` is represented a.e. by the corresponding
finite sum of the pointwise block representatives.
-/
theorem souzaFiniteBlockSum_toLp_ae_eq_toFunLt_sum
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (S : Finset ℕ) :
    ((∑ k ∈ S, (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
      =ᵐ[G.grid.μ]
        fun x =>
          ∑ k ∈ S, (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simpa using
      (MeasureTheory.Lp.coeFn_zero ℂ p G.toWeakGridSpace.measure :
        ((0 : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
          =ᵐ[G.grid.μ] fun _ => (0 : ℂ))
  · intro k S hk hS
    let A := souzaAtomFamily G s p hs hp hp_top
    have hk_ae :
        ((R.block k).toLp A : α → ℂ)
          =ᵐ[G.grid.μ]
            (R.block k).toFunLt A :=
      WeakGridSpace.LevelBlock.coeFn_toLp A (R.block k)
    have hadd :
        (((R.block k).toLp A +
            ∑ i ∈ S, (R.block i).toLp A : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
          =ᵐ[G.grid.μ]
            fun x =>
              ((R.block k).toLp A : α → ℂ) x +
                ((∑ i ∈ S, (R.block i).toLp A :
                    Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) x :=
      MeasureTheory.Lp.coeFn_add
        ((R.block k).toLp A)
        (∑ i ∈ S, (R.block i).toLp A)
    filter_upwards [hadd, hk_ae, hS] with x hxadd hxk hxS
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    rw [hxadd, hxk, hxS]

/--
The finite initial Souza segment in `Lp` is represented a.e. by the pointwise
initial segment used in the oscillation estimates.
-/
theorem souzaInitialSegment_toLp_ae_eq_toFunLt_sum
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) :
    ((∑ k ∈ Finset.range (k₀ + 1),
        (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
      =ᵐ[G.grid.μ]
        fun x =>
          ∑ k ∈ Finset.range (k₀ + 1),
            (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x :=
  souzaFiniteBlockSum_toLp_ae_eq_toFunLt_sum
    (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
    (R := R) (S := Finset.range (k₀ + 1))

/--
The represented `Lp` function is a.e. the pointwise initial Souza segment plus
the corresponding `Lp` tail.

This is the formal version of splitting an atomic representation into low
frequencies and high frequencies.
-/
theorem souzaRepresentation_ae_eq_initialSegment_add_lpTail
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) :
    (g : α → ℂ)
      =ᵐ[G.grid.μ]
        fun x =>
          (∑ k ∈ Finset.range (k₀ + 1),
            (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x) +
            ((g -
              ∑ k ∈ Finset.range (k₀ + 1),
                (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
              Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) x := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let lowLp : Lp ℂ p G.toWeakGridSpace.measure :=
    ∑ k ∈ Finset.range (k₀ + 1), (R.block k).toLp A
  let tailLp : Lp ℂ p G.toWeakGridSpace.measure := g - lowLp
  have hlow :
      (lowLp : α → ℂ)
        =ᵐ[G.grid.μ]
          fun x => ∑ k ∈ Finset.range (k₀ + 1), (R.block k).toFunLt A x := by
    simpa [lowLp, A] using
      souzaInitialSegment_toLp_ae_eq_toFunLt_sum
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
        (R := R) k₀
  have hLp : lowLp + tailLp = g := by
    simp [tailLp, lowLp]
  have hg :
      (g : α → ℂ) =ᵐ[G.grid.μ] ((lowLp + tailLp : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) := by
    rw [hLp]
  have hadd :
      ((lowLp + tailLp : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
        =ᵐ[G.grid.μ] fun x => (lowLp : α → ℂ) x + (tailLp : α → ℂ) x :=
    MeasureTheory.Lp.coeFn_add lowLp tailLp
  have hreplace :
      (fun x => (lowLp : α → ℂ) x + (tailLp : α → ℂ) x)
        =ᵐ[G.grid.μ]
          fun x =>
            (∑ k ∈ Finset.range (k₀ + 1), (R.block k).toFunLt A x) +
              (tailLp : α → ℂ) x :=
    hlow.add Filter.EventuallyEq.rfl
  simpa [A, lowLp, tailLp] using hg.trans (hadd.trans hreplace)

/--
Adding a tail to a finite low-frequency Souza sum: on a level-`k₀` cell, the
oscillation is bounded by the local `L^p` norm of the tail.
-/
theorem osc_souzaFiniteBlockSum_add_tail_le_tail_eLpNorm
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {k₀ : ℕ} (S : Finset ℕ) (hS : ∀ k ∈ S, k ≤ k₀)
    (B : ∀ k, WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k)
    (tail : α → ℂ)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀) :
    osc G p
        (fun x =>
          (∑ k ∈ S, (B k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x) + tail x)
        ({ level := k₀, cell := J.1, mem := J.2 } : GoodGridCell G) ≤
      MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1) := by
  rcases G.grid.partition_nonempty k₀ J.1 J.2 with ⟨xJ, hxJ⟩
  let low : α → ℂ :=
    fun x => ∑ k ∈ S, (B k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x
  let c : ℂ := low xJ
  refine osc_le_eLpNorm_of_sub_eq_on_cell G p (fun x => low x + tail x) tail
    ({ level := k₀, cell := J.1, mem := J.2 } : GoodGridCell G) c ?_
  intro x hx
  have hlow : low x = c := by
    dsimp [c, low]
    exact souzaFiniteBlockSum_toFunLt_eq_on_finer_cell
      (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
      (S := S) (hS := hS) (B := B) (J := J) hx hxJ
  simp [hlow, c]

/--
Adding an arbitrary tail to the initial segment of a Souza representation: on
a level-`k₀` cell, the oscillation is bounded by the local `L^p` norm of that
tail.

This is the local reduction from oscillation to the high-frequency tail used
at the start of the proof of `(in4)`.
-/
theorem osc_souzaInitialSegment_add_tail_le_tail_eLpNorm
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    {k₀ : ℕ} (tail : α → ℂ)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀) :
    osc G p
        (fun x =>
          (∑ k ∈ Finset.range (k₀ + 1),
            (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x) + tail x)
        ({ level := k₀, cell := J.1, mem := J.2 } : GoodGridCell G) ≤
      MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1) := by
  refine osc_souzaFiniteBlockSum_add_tail_le_tail_eLpNorm
    (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
    (S := Finset.range (k₀ + 1)) (B := R.block) (tail := tail) (J := J) ?_
  intro k hk
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)

/--
If `f` agrees a.e. on a level-`k₀` cell with an initial Souza segment plus a
tail, then the oscillation of `f` on that cell is bounded by the local `L^p`
norm of the tail.

This is the a.e. version needed when the atomic series is known only as an
identity in `Lp`.
-/
theorem osc_le_tail_eLpNorm_of_ae_eq_souzaInitialSegment_add_tail
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    {k₀ : ℕ} (tail f : α → ℂ)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    (hf :
      f =ᵐ[G.grid.μ.restrict J.1]
        fun x =>
          (∑ k ∈ Finset.range (k₀ + 1),
            (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x) + tail x) :
    osc G p f ({ level := k₀, cell := J.1, mem := J.2 } : GoodGridCell G) ≤
      MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1) := by
  calc
    osc G p f ({ level := k₀, cell := J.1, mem := J.2 } : GoodGridCell G)
        =
          osc G p
            (fun x =>
              (∑ k ∈ Finset.range (k₀ + 1),
                (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x) + tail x)
            ({ level := k₀, cell := J.1, mem := J.2 } : GoodGridCell G) :=
        osc_congr_ae G p f _ ({ level := k₀, cell := J.1, mem := J.2 } : GoodGridCell G) hf
    _ ≤ MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1) :=
        osc_souzaInitialSegment_add_tail_le_tail_eLpNorm
          (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
          (R := R) (tail := tail) (J := J)

/--
On a parent cell, an ambient Souza level block agrees pointwise with its block
obtained by restricting to the induced grid on that parent.
-/
theorem souzaAmbientLevelBlockToInduced_toFunLt_eq_on_parent
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {k₀ i : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) (k₀ + i))
    {x : α} (hx : x ∈ Q.1) :
    B.toFunLt (souzaAtomFamily G s p hs hp hp_top) x =
      (WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace Q
          (souzaAtomFamily G s p hs hp hp_top) B).toFunLt
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q
          (souzaAtomFamily G s p hs hp hp_top)) x := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let F : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i) → ℂ := fun P =>
    B.coeff P * A.toFunction
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace (k₀ + i) P)
      (B.atom P) x
  have hcomp :
      (∑ P : {P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i) //
          ¬ (P : Set α) ⊆ Q.1},
          F P.1) = 0 := by
    apply Finset.sum_eq_zero
    intro P _hP
    have hxP_not : x ∉ (P.1 : Set α) := by
      intro hxP
      rcases G.grid.partition_subset_or_disjoint_of_le k₀ (k₀ + i)
          (Nat.le_add_right k₀ i) Q.1 Q.2 (P.1 : Set α) P.1.2 with hsub | hdisj
      · exact P.2 hsub
      · exact (Set.disjoint_left.mp hdisj hxP hx).elim
    have hzero :
        A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace (k₀ + i) P.1)
            (B.atom P.1) x = 0 := by
      simpa using A.local_support
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace (k₀ + i) P.1)
        (B.atom P.1) x hxP_not
    simp [F, hzero]
  have hsub :
      (∑ P : {P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i) //
          (P : Set α) ⊆ Q.1},
          F P.1) =
        (WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace Q A B).toFunLt
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q A) x := by
    rw [WeakGridSpace.LevelBlock.toFunLt]
    refine Fintype.sum_equiv
      (WeakGridSpace.inducedLevelCellEquivSubtype G.toWeakGridSpace Q).symm
      (fun P : {P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i) //
          (P : Set α) ⊆ Q.1} =>
        F P.1)
      (fun P : WeakGridSpace.LevelCell
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q) i =>
        (WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace Q A B).coeff P *
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q A).toFunction
            (WeakGridSpace.levelCellToWeakGridCell
              (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q) i P)
            ((WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace Q A B).atom P) x)
      ?_
    intro P
    rfl
  calc
    B.toFunLt A x = ∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i), F P := by
      simp [F, WeakGridSpace.LevelBlock.toFunLt]
    _ =
        (∑ P : {P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i) //
            (P : Set α) ⊆ Q.1},
          F P.1) +
          ∑ P : {P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i) //
              ¬ (P : Set α) ⊆ Q.1},
            F P.1 := by
      rw [Fintype.sum_subtype_add_sum_subtype
        (fun P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i) => P.1 ⊆ Q.1) F]
    _ =
        (WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace Q A B).toFunLt
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q A) x := by
      simp [hsub, hcomp]

/--
A single Souza level block, restricted to a parent cell, is controlled by the
geometric mesh decay of the induced grid on that parent.
-/
theorem eLpNorm_souzaAmbientLevelBlock_restrict_le_geometric_coeff
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {k₀ i : ℕ} (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) (k₀ + i)) :
    MeasureTheory.eLpNorm
        (B.toFunLt (souzaAtomFamily G s p hs hp hp_top))
        p (G.grid.μ.restrict J.1)
      ≤
        ENNReal.ofReal
          (((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
              (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
                ‖B.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Q : GoodGridCell G := { level := k₀, cell := J.1, mem := J.2 }
  let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
  let AI := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace J A
  let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
  have hmeas : MeasurableSet J.1 := G.grid.grid.measurable k₀ J.1 J.2
  have hcongr :
      B.toFunLt A =ᵐ[G.grid.μ.restrict J.1] BI.toFunLt AI := by
    filter_upwards [ae_restrict_mem hmeas] with x hx
    exact souzaAmbientLevelBlockToInduced_toFunLt_eq_on_parent
      (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
      (Q := J) (B := B) hx
  have hp_ne_zero : p ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le hp)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  have hp_le_pu : p ≤ p * ∞ := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * ∞ := mul_le_mul_right le_top p
  have hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / p.toReal := by
    linarith [hs.le]
  have hblock :
      MeasureTheory.eLpNorm (BI.toFunLt AI) p W.measure ≤
        ENNReal.ofReal
          (((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i *
              (∑ P : WeakGridSpace.LevelCell W i,
                ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) := by
    exact WeakGridSpace.LpGridRepresentation.eLpNorm_levelBlock_toFunLt_le_of_atom_bound
      (G := W) (A := AI) (t := p)
      hp_top hp_top le_rfl hp_le_pu hs_nonneg BI
  have hlocal_le_global :
      MeasureTheory.eLpNorm (BI.toFunLt AI) p (G.grid.μ.restrict J.1) ≤
        MeasureTheory.eLpNorm (BI.toFunLt AI) p W.measure := by
    simpa [W, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
      WeakGridSpace.WeakGridSpace.measure] using
      MeasureTheory.eLpNorm_mono_measure (BI.toFunLt AI) Measure.restrict_le_self
  have hweight :
      WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i
        ≤ (G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s := by
    simpa [W, Q] using
      _root_.GoodGridSpace.induced_levelMeasureWeight_le_geometric G Q s p hs i
  have hcoeff :
      (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal)
        ≤ ∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
            ‖B.coeff P‖ ^ p.toReal := by
    simpa [W, AI, BI, A] using
      WeakGridSpace.ambientLevelBlockToInduced_coeffPower_le G.toWeakGridSpace J A B
  have hroot :
      (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)
        ≤
          (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
            ‖B.coeff P‖ ^ p.toReal) ^ (1 / p.toReal) := by
    exact Real.rpow_le_rpow
      (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _)
      hcoeff (one_div_nonneg.mpr hp_pos.le)
  have hreal :
      ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i *
            (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^
              (1 / p.toReal)
        ≤
        ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
            (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
              ‖B.coeff P‖ ^ p.toReal) ^ (1 / p.toReal) := by
    have hC_nonneg : 0 ≤ (W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal) := by positivity
    have htarget_nonneg :
        0 ≤ (G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s := by
      exact mul_nonneg
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)
        (Real.rpow_nonneg (pow_nonneg
          (le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2) i) _)
    calc
      ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i *
            (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^
              (1 / p.toReal)
          =
        ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i *
            (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^
              (1 / p.toReal)) := by
            rw [mul_assoc]
      _ 
          ≤ ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
              (((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
                (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^
                  (1 / p.toReal)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hweight
                (Real.rpow_nonneg
                  (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _) _))
              hC_nonneg
      _ =
          ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
              (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^
                (1 / p.toReal) := by
            ring_nf
      _ ≤ ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
              ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
                (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
                  ‖B.coeff P‖ ^ p.toReal) ^ (1 / p.toReal) := by
            exact mul_le_mul_of_nonneg_left hroot
              (mul_nonneg hC_nonneg htarget_nonneg)
      _ =
          ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
              (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
                ‖B.coeff P‖ ^ p.toReal) ^ (1 / p.toReal) := by
            simp [W, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
              WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid]
  have htarget_nonneg :
      0 ≤ ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
            (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
              ‖B.coeff P‖ ^ p.toReal) ^ (1 / p.toReal) := by
    have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
      le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (mul_nonneg
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
          (Real.rpow_nonneg (pow_nonneg hlam_nonneg i) _)))
      (Real.rpow_nonneg
        (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _) _)
  calc
    MeasureTheory.eLpNorm (B.toFunLt A) p (G.grid.μ.restrict J.1)
        = MeasureTheory.eLpNorm (BI.toFunLt AI) p (G.grid.μ.restrict J.1) :=
          MeasureTheory.eLpNorm_congr_ae hcongr
    _ ≤ MeasureTheory.eLpNorm (BI.toFunLt AI) p W.measure := hlocal_le_global
    _ ≤ ENNReal.ofReal
          (((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i *
              (∑ P : WeakGridSpace.LevelCell W i,
                ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) := hblock
    _ ≤ ENNReal.ofReal
          (((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
              (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
                ‖B.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) :=
        ENNReal.ofReal_le_ofReal hreal

/--
Local version of
`eLpNorm_souzaAmbientLevelBlock_restrict_le_geometric_coeff`.

The coefficient power is kept on the grid induced by the parent cell `J`,
rather than immediately bounded by the full ambient level power.  This is the
form needed before summing over all parent cells.
-/
theorem eLpNorm_souzaAmbientLevelBlock_restrict_le_local_geometric_coeff
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {k₀ i : ℕ} (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) (k₀ + i)) :
    let A := souzaAtomFamily G s p hs hp hp_top
    let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
    let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
    MeasureTheory.eLpNorm
        (B.toFunLt A)
        p (G.grid.μ.restrict J.1)
      ≤
        ENNReal.ofReal
          (((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
              (∑ P : WeakGridSpace.LevelCell W i,
                ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) := by
  classical
  intro A W BI
  let AI := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace J A
  let Q : GoodGridCell G := { level := k₀, cell := J.1, mem := J.2 }
  have hmeas : MeasurableSet J.1 := G.grid.grid.measurable k₀ J.1 J.2
  have hcongr :
      B.toFunLt A =ᵐ[G.grid.μ.restrict J.1] BI.toFunLt AI := by
    filter_upwards [ae_restrict_mem hmeas] with x hx
    exact souzaAmbientLevelBlockToInduced_toFunLt_eq_on_parent
      (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
      (Q := J) (B := B) hx
  have hp_ne_zero : p ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le hp)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  have hp_le_pu : p ≤ p * ∞ := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * ∞ := mul_le_mul_right le_top p
  have hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / p.toReal := by
    linarith [hs.le]
  have hblock :
      MeasureTheory.eLpNorm (BI.toFunLt AI) p W.measure ≤
        ENNReal.ofReal
          (((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i *
              (∑ P : WeakGridSpace.LevelCell W i,
                ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) := by
    exact WeakGridSpace.LpGridRepresentation.eLpNorm_levelBlock_toFunLt_le_of_atom_bound
      (G := W) (A := AI) (t := p)
      hp_top hp_top le_rfl hp_le_pu hs_nonneg BI
  have hlocal_le_global :
      MeasureTheory.eLpNorm (BI.toFunLt AI) p (G.grid.μ.restrict J.1) ≤
        MeasureTheory.eLpNorm (BI.toFunLt AI) p W.measure := by
    simpa [W, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
      WeakGridSpace.WeakGridSpace.measure] using
      MeasureTheory.eLpNorm_mono_measure (BI.toFunLt AI) Measure.restrict_le_self
  have hweight :
      WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i
        ≤ (G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s := by
    simpa [W, Q] using
      _root_.GoodGridSpace.induced_levelMeasureWeight_le_geometric G Q s p hs i
  have hreal :
      ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i *
            (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^
              (1 / p.toReal)
        ≤
        ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
            (∑ P : WeakGridSpace.LevelCell W i,
              ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal) := by
    have hC_nonneg : 0 ≤ (W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal) := by positivity
    have hroot_nonneg :
        0 ≤ (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^
            (1 / p.toReal) :=
      Real.rpow_nonneg
        (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _) _
    calc
      ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i *
            (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^
              (1 / p.toReal)
          =
        ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i *
            (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^
              (1 / p.toReal)) := by
            rw [mul_assoc]
      _ ≤ ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
              (((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
                (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^
                  (1 / p.toReal)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hweight hroot_nonneg)
              hC_nonneg
      _ =
          ((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
              (∑ P : WeakGridSpace.LevelCell W i, ‖BI.coeff P‖ ^ p.toReal) ^
                (1 / p.toReal) := by
            ring_nf
      _ =
          ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
              (∑ P : WeakGridSpace.LevelCell W i,
                ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal) := by
            simp [W, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
              WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid]
  calc
    MeasureTheory.eLpNorm (B.toFunLt A) p (G.grid.μ.restrict J.1)
        = MeasureTheory.eLpNorm (BI.toFunLt AI) p (G.grid.μ.restrict J.1) :=
          MeasureTheory.eLpNorm_congr_ae hcongr
    _ ≤ MeasureTheory.eLpNorm (BI.toFunLt AI) p W.measure := hlocal_le_global
    _ ≤ ENNReal.ofReal
          (((W.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            WeakGridSpace.LpGridRepresentation.levelMeasureWeight W s p p i *
              (∑ P : WeakGridSpace.LevelCell W i,
                ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) := hblock
    _ ≤ ENNReal.ofReal
          (((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
            ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
              (∑ P : WeakGridSpace.LevelCell W i,
                ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) :=
        ENNReal.ofReal_le_ofReal hreal

/--
Real-valued form of
`eLpNorm_souzaAmbientLevelBlock_restrict_le_geometric_coeff`.
-/
theorem eLpNorm_souzaAmbientLevelBlock_restrict_toReal_le_geometric_coeff
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {k₀ i : ℕ} (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) (k₀ + i)) :
    (MeasureTheory.eLpNorm
        (B.toFunLt (souzaAtomFamily G s p hs hp hp_top))
        p (G.grid.μ.restrict J.1)).toReal
      ≤
        ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
            (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
              ‖B.coeff P‖ ^ p.toReal) ^ (1 / p.toReal) := by
  let A := souzaAtomFamily G s p hs hp hp_top
  have hp_le_pu : p ≤ p * ∞ := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * ∞ := mul_le_mul_right le_top p
  have hmem :
      MeasureTheory.MemLp (B.toFunLt A) p (G.grid.μ.restrict J.1) :=
    (WeakGridSpace.LevelBlock.toFunLt_memLp A hp_le_pu B).restrict J.1
  have htarget_nonneg :
      0 ≤ ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
            (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
              ‖B.coeff P‖ ^ p.toReal) ^ (1 / p.toReal) := by
    have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
      le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (mul_nonneg
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
          (Real.rpow_nonneg (pow_nonneg hlam_nonneg i) _)))
      (Real.rpow_nonneg
        (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _) _)
  have h :=
    eLpNorm_souzaAmbientLevelBlock_restrict_le_geometric_coeff
      (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
      (hp_top := hp_top) (J := J) (B := B)
  exact (ENNReal.le_ofReal_iff_toReal_le hmem.eLpNorm_ne_top htarget_nonneg).1 h

/--
Real-valued local form of
`eLpNorm_souzaAmbientLevelBlock_restrict_le_local_geometric_coeff`.
-/
theorem eLpNorm_souzaAmbientLevelBlock_restrict_toReal_le_local_geometric_coeff
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {k₀ i : ℕ} (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) (k₀ + i)) :
    let A := souzaAtomFamily G s p hs hp hp_top
    let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
    let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
    (MeasureTheory.eLpNorm
        (B.toFunLt A)
        p (G.grid.μ.restrict J.1)).toReal
      ≤
        ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
            (∑ P : WeakGridSpace.LevelCell W i,
              ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal) := by
  intro A W BI
  have hp_le_pu : p ≤ p * ∞ := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * ∞ := mul_le_mul_right le_top p
  have hmem :
      MeasureTheory.MemLp (B.toFunLt A) p (G.grid.μ.restrict J.1) :=
    (WeakGridSpace.LevelBlock.toFunLt_memLp A hp_le_pu B).restrict J.1
  have htarget_nonneg :
      0 ≤ ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
          ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
            (∑ P : WeakGridSpace.LevelCell W i,
              ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal) := by
    have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
      le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (mul_nonneg
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
          (Real.rpow_nonneg (pow_nonneg hlam_nonneg i) _)))
      (Real.rpow_nonneg
        (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _) _)
  have h :=
    eLpNorm_souzaAmbientLevelBlock_restrict_le_local_geometric_coeff
      (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
      (hp_top := hp_top) (J := J) (B := B)
  exact (ENNReal.le_ofReal_iff_toReal_le hmem.eLpNorm_ne_top htarget_nonneg).1
    (by simpa [A, W, BI] using h)

private theorem sum_subtype_le_sum_of_unique
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : ι → κ → Prop) [DecidableRel R] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i)
    (huniq : ∀ i j k, R i j → R i k → j = k) :
    (∑ j : κ, ∑ i : {i : ι // R i j}, f i.1) ≤ ∑ i : ι, f i := by
  classical
  let X := Sigma fun j : κ => {i : ι // R i j}
  let parentFine : X → ι := fun x => x.2.1
  have hparentFine_inj : Function.Injective parentFine := by
    intro x y hxy
    rcases x with ⟨j, i⟩
    rcases y with ⟨k, i'⟩
    dsimp [parentFine] at hxy
    have hRik : R i.1 k := by
      simpa [← hxy] using i'.2
    have hjk : j = k := huniq i.1 j k i.2 hRik
    subst k
    have hii' : i = i' := Subtype.ext hxy
    subst i'
    rfl
  have hsigma :
      (∑ x : X, f (parentFine x)) =
        ∑ j : κ, ∑ i : {i : ι // R i j}, f i.1 := by
    simpa [X, parentFine] using
      (Fintype.sum_sigma
        (f := fun x : Sigma (fun j : κ => {i : ι // R i j}) => f x.2.1))
  have himage :
      (∑ i ∈ ((Finset.univ : Finset X).image parentFine), f i) =
        ∑ x : X, f (parentFine x) := by
    simpa using
      (Finset.sum_image
        (s := (Finset.univ : Finset X)) (g := parentFine) (f := f)
        (by
          intro x _hx y _hy hxy
          exact hparentFine_inj hxy))
  have hsubset : (Finset.univ : Finset X).image parentFine ⊆ (Finset.univ : Finset ι) := by
    intro i _hi
    simp
  calc
    (∑ j : κ, ∑ i : {i : ι // R i j}, f i.1)
        = ∑ x : X, f (parentFine x) := hsigma.symm
    _ = ∑ i ∈ ((Finset.univ : Finset X).image parentFine), f i := himage.symm
    _ ≤ ∑ i ∈ (Finset.univ : Finset ι), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (by
            intro i _hi _him
            exact hf i)
    _ = ∑ i : ι, f i := by
        simp

private theorem fineCell_parent_unique
    (G : GoodGridSpace (α := α)) {k₀ i : ℕ}
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i))
    (J K : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    (hJ : P.1 ⊆ J.1) (hK : P.1 ⊆ K.1) :
    J = K := by
  by_cases hJK : J.1 = K.1
  · exact Subtype.ext hJK
  · have hdisj : Disjoint J.1 K.1 :=
      G.grid.grid.disjoint k₀ J.1 K.1 J.2 K.2 hJK
    rcases G.grid.partition_nonempty (k₀ + i) P.1 P.2 with ⟨x, hxP⟩
    exact False.elim ((Set.disjoint_left.mp hdisj) (hJ hxP) (hK hxP))

/--
Summing the coefficient power of ambient blocks restricted to all induced
grids at a fixed parent level gives at most the ambient coefficient power.

This is the formal bookkeeping step that each fine cell contributes to at
most one parent cell, because good-grid cells at the parent level are
disjoint.
-/
theorem sum_ambientLevelBlockToInduced_coeffPower_le
    (G : GoodGridSpace (α := α)) {s : ℝ} {p u : ℝ≥0∞}
    (A : WeakGridSpace.AtomFamily G.toWeakGridSpace s p u)
    {k₀ i : ℕ} (B : WeakGridSpace.LevelBlock A (k₀ + i)) :
    (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
      ∑ P : WeakGridSpace.LevelCell
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J) i,
        ‖(WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B).coeff P‖ ^
          p.toReal)
      ≤
        ∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
          ‖B.coeff P‖ ^ p.toReal := by
  classical
  let W0 := G.toWeakGridSpace
  let Parent := WeakGridSpace.LevelCell W0 k₀
  let Fine := WeakGridSpace.LevelCell W0 (k₀ + i)
  let R : Fine → Parent → Prop := fun P J => P.1 ⊆ J.1
  let F : Fine → ℝ := fun P => ‖B.coeff P‖ ^ p.toReal
  have hlocal :
      ∀ J : Parent,
        (∑ P : WeakGridSpace.LevelCell
            (WeakGridSpace.inducedWeakGridSpace W0 J) i,
          ‖(WeakGridSpace.ambientLevelBlockToInduced W0 J A B).coeff P‖ ^
            p.toReal)
          =
            ∑ P : {P : Fine // R P J},
              F P.1 := by
    intro J
    refine Fintype.sum_equiv
      (WeakGridSpace.inducedLevelCellEquivSubtype W0 J)
      (fun P : WeakGridSpace.LevelCell
          (WeakGridSpace.inducedWeakGridSpace W0 J) i =>
        ‖(WeakGridSpace.ambientLevelBlockToInduced W0 J A B).coeff P‖ ^
          p.toReal)
      (fun P : {P : Fine // R P J} =>
        F P.1) ?_
    intro P
    rfl
  change
    (∑ J : Parent,
      ∑ P : WeakGridSpace.LevelCell (WeakGridSpace.inducedWeakGridSpace W0 J) i,
        ‖(WeakGridSpace.ambientLevelBlockToInduced W0 J A B).coeff P‖ ^ p.toReal)
      ≤ ∑ P : Fine, F P
  calc
    (∑ J : Parent,
      ∑ P : WeakGridSpace.LevelCell (WeakGridSpace.inducedWeakGridSpace W0 J) i,
        ‖(WeakGridSpace.ambientLevelBlockToInduced W0 J A B).coeff P‖ ^ p.toReal)
        =
          ∑ J : Parent,
            ∑ P : {P : Fine // R P J},
              F P.1 := by
            refine Finset.sum_congr rfl ?_
            intro J _hJ
            exact hlocal J
    _ ≤ ∑ P : Fine, F P :=
        sum_subtype_le_sum_of_unique
          (R := R) (f := F)
          (fun P => Real.rpow_nonneg (norm_nonneg _) _)
          (by
            intro P J K hJ hK
            exact fineCell_parent_unique G P J K hJ hK)

/--
Finite local tail estimate for Souza blocks above a fixed parent cell.

This is the finite Minkowski step in the oscillation proof: on a level-`k₀`
cell `J`, a finite sum of deeper level blocks is bounded by the sum of the
geometric coefficient estimates for the individual blocks.
-/
theorem eLpNorm_souzaAmbientLevelBlock_finsetSum_restrict_le_geometric_coeff_sum
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {k₀ : ℕ} (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    (S : Finset ℕ)
    (B : (i : ℕ) →
      WeakGridSpace.LevelBlock
        (souzaAtomFamily G s p hs hp hp_top) (k₀ + i)) :
    MeasureTheory.eLpNorm
        (∑ i ∈ S, (B i).toFunLt (souzaAtomFamily G s p hs hp hp_top))
        p (G.grid.μ.restrict J.1)
      ≤
        ∑ i ∈ S,
          ENNReal.ofReal
            (((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
              ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
                (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
                  ‖(B i).coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  have hp_le_pu : p ≤ p * ∞ := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * ∞ := mul_le_mul_right le_top p
  have hmeas :
      ∀ i, i ∈ S →
        AEStronglyMeasurable ((B i).toFunLt A) (G.grid.μ.restrict J.1) := by
    intro i _hi
    exact ((WeakGridSpace.LevelBlock.toFunLt_memLp A hp_le_pu (B i)).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  calc
    MeasureTheory.eLpNorm
        (∑ i ∈ S, (B i).toFunLt A)
        p (G.grid.μ.restrict J.1)
        ≤ ∑ i ∈ S,
            MeasureTheory.eLpNorm ((B i).toFunLt A) p (G.grid.μ.restrict J.1) :=
          MeasureTheory.eLpNorm_sum_le hmeas hp
    _ ≤
        ∑ i ∈ S,
          ENNReal.ofReal
            (((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
              ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
                (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
                  ‖(B i).coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) := by
          refine Finset.sum_le_sum fun i _hi => ?_
          exact eLpNorm_souzaAmbientLevelBlock_restrict_le_geometric_coeff
            (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
            (hp_top := hp_top) (J := J) (B := B i)

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
The level block of oscillations for an initial segment plus an arbitrary tail
is bounded by the corresponding sum of local `L^p` norms of the tail.

This is the levelwise bookkeeping form of
`osc_souzaInitialSegment_add_tail_le_tail_eLpNorm`.
-/
theorem levelOscillationBlock_souzaInitialSegment_add_tail_le
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) (tail : α → ℂ) :
    levelOscillationBlock G s p
        (fun x =>
          (∑ k ∈ Finset.range (k₀ + 1),
            (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x) + tail x)
        k₀
      ≤
        ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          (G.grid.μ J.1) ^ (-(s * p.toReal)) *
            (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal := by
  classical
  unfold levelOscillationBlock
  refine Finset.sum_le_sum fun J _hJ => ?_
  gcongr
  exact osc_souzaInitialSegment_add_tail_le_tail_eLpNorm
    (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
    (R := R) (tail := tail) (J := J)

/--
Levelwise oscillation bound for a finite high-frequency tail.

This packages the local finite Minkowski estimate into the level oscillation
block: after the initial segment up to `k₀`, a finite tail of deeper blocks
controls the oscillation on level `k₀` with the expected geometric coefficient
sum on each parent cell.
-/
theorem levelOscillationBlock_souzaInitialSegment_add_finsetTail_le_geometric_coeff_sum
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) (S : Finset ℕ)
    (B : (i : ℕ) →
      WeakGridSpace.LevelBlock
        (souzaAtomFamily G s p hs hp hp_top) (k₀ + i)) :
    levelOscillationBlock G s p
        (fun x =>
          (∑ k ∈ Finset.range (k₀ + 1),
            (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x) +
              ∑ i ∈ S, (B i).toFunLt (souzaAtomFamily G s p hs hp hp_top) x)
        k₀
      ≤
        ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          (G.grid.μ J.1) ^ (-(s * p.toReal)) *
            (∑ i ∈ S,
              ENNReal.ofReal
                (((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
                  ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
                    (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
                      ‖(B i).coeff P‖ ^ p.toReal) ^ (1 / p.toReal))) ^ p.toReal := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let tail : α → ℂ := ∑ i ∈ S, (B i).toFunLt A
  have htail :
      levelOscillationBlock G s p
          (fun x =>
            (∑ k ∈ Finset.range (k₀ + 1), (R.block k).toFunLt A x) + tail x)
          k₀
        ≤
          ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
            (G.grid.μ J.1) ^ (-(s * p.toReal)) *
              (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal :=
    levelOscillationBlock_souzaInitialSegment_add_tail_le
      (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
      (R := R) (k₀ := k₀) (tail := tail)
  calc
    levelOscillationBlock G s p
        (fun x =>
          (∑ k ∈ Finset.range (k₀ + 1), (R.block k).toFunLt A x) +
            ∑ i ∈ S, (B i).toFunLt A x)
        k₀
        ≤
          ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
            (G.grid.μ J.1) ^ (-(s * p.toReal)) *
              (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal := by
            simpa [tail, A] using htail
    _ ≤
        ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          (G.grid.μ J.1) ^ (-(s * p.toReal)) *
            (∑ i ∈ S,
              ENNReal.ofReal
                (((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
                  ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ i) ^ s) *
                    (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k₀ + i),
          ‖(B i).coeff P‖ ^ p.toReal) ^ (1 / p.toReal))) ^ p.toReal := by
          refine Finset.sum_le_sum fun J _hJ => ?_
          gcongr
          simpa [tail, A] using
            eLpNorm_souzaAmbientLevelBlock_finsetSum_restrict_le_geometric_coeff_sum
              (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
              (hp_top := hp_top) (J := J) (S := S) (B := B)

/--
The local `L^p` norm of the infinite `Lp` tail is bounded by the sum of the
local `L^p` norms of its level blocks, provided these local norms are summable.

This is the analytic limiting step behind the passage from finite tails to the
actual representation tail.  The proof transports the ambient `HasSum` through
the restriction map `Lp μ → Lp (μ.restrict J)` and applies
`norm_tsum_le_tsum_norm` in the restricted `Lp` space.
-/
theorem eLpNorm_lpTail_restrict_toReal_le_tsum_block_restrict_toReal
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    (hSummable :
      Summable fun k =>
        (MeasureTheory.eLpNorm
          (((WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block k).toFunLt
            (souzaAtomFamily G s p hs hp hp_top))
          p (G.grid.μ.restrict J.1)).toReal) :
    (MeasureTheory.eLpNorm
      (((g -
        ∑ k ∈ Finset.range (k₀ + 1),
          (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ))
      p (G.grid.μ.restrict J.1)).toReal
      ≤
        ∑' k,
          (MeasureTheory.eLpNorm
            (((WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block k).toFunLt
              (souzaAtomFamily G s p hs hp hp_top))
            p (G.grid.μ.restrict J.1)).toReal := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let N := k₀ + 1
  let ν : Measure α := G.grid.μ.restrict J.1
  have hνμ : ν ≤ G.toWeakGridSpace.measure := by
    simpa [ν, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
      WeakGridSpace.WeakGridSpace.measure] using
      (Measure.restrict_le_self : G.grid.μ.restrict J.1 ≤ G.grid.μ)
  let L := lpRestrictMeasure G.toWeakGridSpace.measure ν hνμ p
  let T := WeakGridSpace.LpGridRepresentation.tail R N
  let tailLp : Lp ℂ p G.toWeakGridSpace.measure :=
    g - ∑ k ∈ Finset.range N, (R.block k).toLp A
  let F : ℕ → Lp ℂ p ν := fun k => L ((T.block k).toLp A)
  have hnorm_eq :
      ∀ k, ‖F k‖ =
        (MeasureTheory.eLpNorm ((T.block k).toFunLt A) p ν).toReal := by
    intro k
    have hcoe₁ :
        (F k : α → ℂ) =ᵐ[ν] ((T.block k).toLp A : α → ℂ) := by
      simpa [F, L] using
        lpRestrictMeasure_coeFn
          G.toWeakGridSpace.measure ν hνμ p ((T.block k).toLp A)
    have hcoe₂ :
        ((T.block k).toLp A : α → ℂ) =ᵐ[ν] (T.block k).toFunLt A :=
      (WeakGridSpace.LevelBlock.coeFn_toLp A (T.block k)).filter_mono (ae_mono hνμ)
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal (MeasureTheory.eLpNorm_congr_ae (hcoe₁.trans hcoe₂))
  have hSummableF : Summable fun k => ‖F k‖ :=
    hSummable.congr fun k => by
      simpa [A, N, T, ν] using (hnorm_eq k).symm
  have hHasSumF : HasSum F (L tailLp) := by
    simpa [F, L, T, tailLp, N, A] using T.hasSum.mapL L
  have hnorm_tail :
      ‖L tailLp‖ ≤ ∑' k, ‖F k‖ := by
    rw [← hHasSumF.tsum_eq]
    exact norm_tsum_le_tsum_norm hSummableF
  have htail_coe :
      (L tailLp : α → ℂ) =ᵐ[ν] (tailLp : α → ℂ) := by
    simpa [L] using lpRestrictMeasure_coeFn G.toWeakGridSpace.measure ν hνμ p tailLp
  calc
    (MeasureTheory.eLpNorm
      (((g -
        ∑ k ∈ Finset.range (k₀ + 1),
          (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ))
      p (G.grid.μ.restrict J.1)).toReal
        = ‖L tailLp‖ := by
          rw [Lp.norm_def]
          exact congrArg ENNReal.toReal
            (MeasureTheory.eLpNorm_congr_ae (by simpa [tailLp, N, A, ν] using htail_coe.symm))
    _ ≤ ∑' k, ‖F k‖ := hnorm_tail
    _ =
        ∑' k,
          (MeasureTheory.eLpNorm
            (((WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block k).toFunLt
              (souzaAtomFamily G s p hs hp hp_top))
            p (G.grid.μ.restrict J.1)).toReal := by
          refine tsum_congr fun k => ?_
          simpa [A, N, T, ν] using hnorm_eq k

/-- The geometric coefficient bound for the `i`-th level above a parent cell. -/
noncomputable def lpTailGeometricCoeffBound
    (G : GoodGridSpace (α := α))
    (s : ℝ)
    (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀) (i : ℕ) : ℝ :=
  ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
    ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ (i + 1)) ^ s) *
      (R.levelCoeffPower (k₀ + (i + 1))) ^ (1 / p.toReal)

/-- The local geometric coefficient bound for the `i`-th tail level over a parent cell. -/
noncomputable def lpTailLocalGeometricCoeffBound
    (G : GoodGridSpace (α := α))
    (s : ℝ)
    (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀) (i : ℕ) : ℝ :=
  let A := souzaAtomFamily G s p hs hp hp_top
  let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
  let B := R.block (k₀ + (i + 1))
  let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
  ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
    ((G.grid.μ J.1).toReal ^ s * (G.grid.lambda2 ^ (i + 1)) ^ s) *
      (∑ P : WeakGridSpace.LevelCell W (i + 1),
        ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)

/--
The local norm of a tail block is zero below the cutoff level.

This keeps later series arguments from unfolding the whole representation tail:
below the cutoff, the block is simply the zero block.
-/
theorem lpTail_localBlockNorm_eq_zero_of_lt
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    {k₀ k : ℕ} (hk : k < k₀ + 1)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀) :
    (MeasureTheory.eLpNorm
      (((WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block k).toFunLt
        (souzaAtomFamily G s p hs hp hp_top))
      p (G.grid.μ.restrict J.1)).toReal = 0 := by
  classical
  have hblock :
      (WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block k =
        WeakGridSpace.LevelBlock.zero (souzaAtomFamily G s p hs hp hp_top) k := by
    simp [hk]
  have hfun :
      ((WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block k).toFunLt
          (souzaAtomFamily G s p hs hp hp_top) =
        fun _ => (0 : ℂ) := by
    funext x
    rw [hblock]
    simp [WeakGridSpace.LevelBlock.toFunLt, WeakGridSpace.LevelBlock.zero]
  rw [hfun]
  simp

/--
The shifted local norm of a tail block is bounded by the geometric coefficient
attached to its level.
-/
theorem lpTail_localBlockNorm_shift_le_geometricCoeff
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀) (i : ℕ) :
    (MeasureTheory.eLpNorm
      (((WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block (k₀ + (i + 1))).toFunLt
        (souzaAtomFamily G s p hs hp hp_top))
      p (G.grid.μ.restrict J.1)).toReal
      ≤ lpTailGeometricCoeffBound G s p hs hp hp_top R k₀ J i := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  have hnot : ¬ k₀ + (i + 1) < k₀ + 1 := by omega
  have hblock :
      (WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block (k₀ + (i + 1)) =
        R.block (k₀ + (i + 1)) := by
    simp [hnot]
  calc
    (MeasureTheory.eLpNorm
      (((WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block (k₀ + (i + 1))).toFunLt
        A)
      p (G.grid.μ.restrict J.1)).toReal
        =
          (MeasureTheory.eLpNorm
            ((R.block (k₀ + (i + 1))).toFunLt A)
            p (G.grid.μ.restrict J.1)).toReal := by
            rw [hblock]
    _ ≤ lpTailGeometricCoeffBound G s p hs hp hp_top R k₀ J i := by
          simpa [lpTailGeometricCoeffBound, A] using
            eLpNorm_souzaAmbientLevelBlock_restrict_toReal_le_geometric_coeff
              (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
              (hp_top := hp_top) (k₀ := k₀) (i := i + 1) (J := J)
              (B := R.block (k₀ + (i + 1)))

/--
The shifted local norm of a tail block is bounded by the local geometric
coefficient attached to its descendants inside the parent cell.
-/
theorem lpTail_localBlockNorm_shift_le_localGeometricCoeff
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀) (i : ℕ) :
    (MeasureTheory.eLpNorm
      (((WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block (k₀ + (i + 1))).toFunLt
        (souzaAtomFamily G s p hs hp hp_top))
      p (G.grid.μ.restrict J.1)).toReal
      ≤ lpTailLocalGeometricCoeffBound G s p hs hp hp_top R k₀ J i := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  have hnot : ¬ k₀ + (i + 1) < k₀ + 1 := by omega
  have hblock :
      (WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block (k₀ + (i + 1)) =
        R.block (k₀ + (i + 1)) := by
    simp [hnot]
  calc
    (MeasureTheory.eLpNorm
      (((WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block (k₀ + (i + 1))).toFunLt
        A)
      p (G.grid.μ.restrict J.1)).toReal
        =
          (MeasureTheory.eLpNorm
            ((R.block (k₀ + (i + 1))).toFunLt A)
            p (G.grid.μ.restrict J.1)).toReal := by
            rw [hblock]
    _ ≤ lpTailLocalGeometricCoeffBound G s p hs hp hp_top R k₀ J i := by
          simpa [lpTailLocalGeometricCoeffBound, A] using
            eLpNorm_souzaAmbientLevelBlock_restrict_toReal_le_local_geometric_coeff
              (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
              (hp_top := hp_top) (k₀ := k₀) (i := i + 1) (J := J)
              (B := R.block (k₀ + (i + 1)))

/--
If a nonnegative series is zero before `N` and its shifted tail is bounded by
a summable series, then the whole series is summable and its total is bounded
by the shifted majorant.
-/
private theorem tsum_tail_le_tsum_shift_bound
    {a b : ℕ → ℝ} {N : ℕ}
    (ha_nonneg : ∀ k, 0 ≤ a k)
    (hprefix : ∀ k, k < N → a k = 0)
    (hshift : ∀ i, a (N + i) ≤ b i)
    (hb : Summable b) :
    Summable a ∧ ∑' k, a k ≤ ∑' i, b i := by
  have hshiftSummable : Summable fun i => a (N + i) :=
    Summable.of_nonneg_of_le (fun i => ha_nonneg (N + i)) hshift hb
  have hshiftSummable' : Summable fun i => a (i + N) := by
    simpa [Nat.add_comm] using hshiftSummable
  have ha : Summable a := (summable_nat_add_iff N).mp hshiftSummable'
  have hsum_zero : (∑ k ∈ Finset.range N, a k) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    exact hprefix k (Finset.mem_range.mp hk)
  have htail_eq :
      (∑' k, a k) = ∑' i, a (N + i) := by
    have h := ha.sum_add_tsum_nat_add N
    rw [hsum_zero, zero_add] at h
    calc
      (∑' k, a k) = ∑' i, a (i + N) := h.symm
      _ = ∑' i, a (N + i) := by
          refine tsum_congr fun i => ?_
          rw [Nat.add_comm]
  refine ⟨ha, ?_⟩
  calc
    (∑' k, a k) = ∑' i, a (N + i) := htail_eq
    _ ≤ ∑' i, b i := hshiftSummable.tsum_le_tsum hshift hb

/--
The local `L^p` norm of the `Lp` tail is bounded by the geometric coefficient
series attached to all levels above the parent cell.
-/
theorem eLpNorm_lpTail_restrict_toReal_le_tsum_geometricCoeff
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    (hSummableGeom :
      Summable fun i => lpTailGeometricCoeffBound G s p hs hp hp_top R k₀ J i) :
    (MeasureTheory.eLpNorm
      (((g -
        ∑ k ∈ Finset.range (k₀ + 1),
          (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ))
      p (G.grid.μ.restrict J.1)).toReal
      ≤
        ∑' i, lpTailGeometricCoeffBound G s p hs hp hp_top R k₀ J i := by
  classical
  let a : ℕ → ℝ := fun k =>
    (MeasureTheory.eLpNorm
      (((WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block k).toFunLt
        (souzaAtomFamily G s p hs hp hp_top))
      p (G.grid.μ.restrict J.1)).toReal
  let b : ℕ → ℝ := fun i =>
    lpTailGeometricCoeffBound G s p hs hp hp_top R k₀ J i
  have ha_nonneg : ∀ k, 0 ≤ a k := fun k => ENNReal.toReal_nonneg
  have hprefix : ∀ k, k < k₀ + 1 → a k = 0 := by
    intro k hk
    simpa [a] using
      lpTail_localBlockNorm_eq_zero_of_lt
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
        (hp_top := hp_top) (R := R) (k₀ := k₀) (k := k) hk J
  have hshift : ∀ i, a ((k₀ + 1) + i) ≤ b i := by
    intro i
    simpa [a, b, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      lpTail_localBlockNorm_shift_le_geometricCoeff
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
        (hp_top := hp_top) (R := R) (k₀ := k₀) (J := J) (i := i)
  have hseries :
      Summable a ∧ ∑' k, a k ≤ ∑' i, b i :=
    tsum_tail_le_tsum_shift_bound
      (N := k₀ + 1) ha_nonneg hprefix hshift (by simpa [b] using hSummableGeom)
  calc
    (MeasureTheory.eLpNorm
      (((g -
        ∑ k ∈ Finset.range (k₀ + 1),
          (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ))
      p (G.grid.μ.restrict J.1)).toReal
        ≤ ∑' k, a k := by
          simpa [a] using
            eLpNorm_lpTail_restrict_toReal_le_tsum_block_restrict_toReal
              (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
              (hp_top := hp_top) (R := R) (k₀ := k₀) (J := J) hseries.1
    _ ≤ ∑' i, b i := hseries.2
    _ = ∑' i, lpTailGeometricCoeffBound G s p hs hp hp_top R k₀ J i := rfl

/--
Local version of
`eLpNorm_lpTail_restrict_toReal_le_tsum_geometricCoeff`, with coefficient
powers restricted to descendants of the parent cell.
-/
theorem eLpNorm_lpTail_restrict_toReal_le_tsum_localGeometricCoeff
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀)
    (hSummableGeom :
      Summable fun i => lpTailLocalGeometricCoeffBound G s p hs hp hp_top R k₀ J i) :
    (MeasureTheory.eLpNorm
      (((g -
        ∑ k ∈ Finset.range (k₀ + 1),
          (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ))
      p (G.grid.μ.restrict J.1)).toReal
      ≤
        ∑' i, lpTailLocalGeometricCoeffBound G s p hs hp hp_top R k₀ J i := by
  classical
  let a : ℕ → ℝ := fun k =>
    (MeasureTheory.eLpNorm
      (((WeakGridSpace.LpGridRepresentation.tail R (k₀ + 1)).block k).toFunLt
        (souzaAtomFamily G s p hs hp hp_top))
      p (G.grid.μ.restrict J.1)).toReal
  let b : ℕ → ℝ := fun i =>
    lpTailLocalGeometricCoeffBound G s p hs hp hp_top R k₀ J i
  have ha_nonneg : ∀ k, 0 ≤ a k := fun k => ENNReal.toReal_nonneg
  have hprefix : ∀ k, k < k₀ + 1 → a k = 0 := by
    intro k hk
    simpa [a] using
      lpTail_localBlockNorm_eq_zero_of_lt
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
        (hp_top := hp_top) (R := R) (k₀ := k₀) (k := k) hk J
  have hshift : ∀ i, a ((k₀ + 1) + i) ≤ b i := by
    intro i
    simpa [a, b, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      lpTail_localBlockNorm_shift_le_localGeometricCoeff
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
        (hp_top := hp_top) (R := R) (k₀ := k₀) (J := J) (i := i)
  have hseries :
      Summable a ∧ ∑' k, a k ≤ ∑' i, b i :=
    tsum_tail_le_tsum_shift_bound
      (N := k₀ + 1) ha_nonneg hprefix hshift (by simpa [b] using hSummableGeom)
  calc
    (MeasureTheory.eLpNorm
      (((g -
        ∑ k ∈ Finset.range (k₀ + 1),
          (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ))
      p (G.grid.μ.restrict J.1)).toReal
        ≤ ∑' k, a k := by
          simpa [a] using
            eLpNorm_lpTail_restrict_toReal_le_tsum_block_restrict_toReal
              (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
              (hp_top := hp_top) (R := R) (k₀ := k₀) (J := J) hseries.1
    _ ≤ ∑' i, b i := hseries.2
    _ = ∑' i, lpTailLocalGeometricCoeffBound G s p hs hp hp_top R k₀ J i := rfl

/--
Levelwise a.e. version of the tail reduction.

If `f` agrees a.e. on every level-`k₀` cell with the initial Souza segment
plus `tail`, then `levelOscillationBlock` is controlled by the local `L^p`
tail contributions.
-/
theorem levelOscillationBlock_le_of_ae_eq_souzaInitialSegment_add_tail
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) (tail f : α → ℂ)
    (hf : ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
      f =ᵐ[G.grid.μ.restrict J.1]
        fun x =>
          (∑ k ∈ Finset.range (k₀ + 1),
            (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x) + tail x) :
    levelOscillationBlock G s p f k₀
      ≤
        ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          (G.grid.μ J.1) ^ (-(s * p.toReal)) *
            (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal := by
  classical
  unfold levelOscillationBlock
  refine Finset.sum_le_sum fun J _hJ => ?_
  gcongr
  exact osc_le_tail_eLpNorm_of_ae_eq_souzaInitialSegment_add_tail
    (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
    (R := R) (tail := tail) (f := f) (J := J) (hf J)

/--
For the `Lp` representative carried by a Souza representation, the level
oscillation block is controlled by the local `L^p` norms of the `Lp` tail after
level `k₀`.

This is the first levelwise tail estimate before replacing the local tail
norms by coefficient sums.
-/
theorem levelOscillationBlock_souzaRepresentation_coe_le_lpTail
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ : ℕ) :
    levelOscillationBlock G s p (g : α → ℂ) k₀
      ≤
        ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          (G.grid.μ J.1) ^ (-(s * p.toReal)) *
            (MeasureTheory.eLpNorm
              (((g -
                ∑ k ∈ Finset.range (k₀ + 1),
                  (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
                Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ))
              p (G.grid.μ.restrict J.1)) ^ p.toReal := by
  classical
  let tail : α → ℂ :=
    ((g -
      ∑ k ∈ Finset.range (k₀ + 1),
        (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
      Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
  refine levelOscillationBlock_le_of_ae_eq_souzaInitialSegment_add_tail
    (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
    (R := R) (k₀ := k₀) (tail := tail) (f := (g : α → ℂ)) ?_
  intro J
  simpa [tail] using
    ae_restrict_of_ae
      (souzaRepresentation_ae_eq_initialSegment_add_lpTail
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
        (R := R) k₀)

/--
Function-level version of
`levelOscillationBlock_souzaRepresentation_coe_le_lpTail`.

If a concrete function `f` represents the same a.e. class as the `Lp` value
`g`, then its level oscillation is controlled by the same `Lp` tail.
-/
theorem levelOscillationBlock_function_le_lpTail_of_ae_eq_souzaRepresentation
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (f : α → ℂ) (k₀ : ℕ)
    (hfg : f =ᵐ[G.grid.μ] (g : α → ℂ)) :
    levelOscillationBlock G s p f k₀
      ≤
        ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          (G.grid.μ J.1) ^ (-(s * p.toReal)) *
            (MeasureTheory.eLpNorm
              (((g -
                ∑ k ∈ Finset.range (k₀ + 1),
                  (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
                Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ))
              p (G.grid.μ.restrict J.1)) ^ p.toReal := by
  rw [levelOscillationBlock_congr_ae G s p f (g : α → ℂ) k₀ hfg]
  exact levelOscillationBlock_souzaRepresentation_coe_le_lpTail
    (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
    (R := R) k₀

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
