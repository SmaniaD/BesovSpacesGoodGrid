import BesovSpacesGoodGrid.GoodGrid.FiniteStandardNormimpliesBesov
import BesovSpacesGoodGrid.GoodGrid.MeanOscillationNorm

/-!
# Oscillation norm controlled by the standard representation norm

This file records the comparison corresponding to inequality `(in4)` in the
preprint.  The intended estimate says that the mean-oscillation gauge is
controlled by the standard atomic coefficient gauge.  The proof is organized in
the same two pieces as the manuscript:

* the `L^p` part of the oscillation norm is controlled by the atomic Besov
  gauge, via the existing `L^p` embedding estimate;
* the oscillation seminorm is controlled by the tail of an almost-minimizing
  standard atomic representation, followed by the geometric convolution
  estimate.

The final theorem packages these two estimates and also returns the `L^p`
membership supplied by the finite-standard-norm theorem.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace MeanOscillation

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
A finite `ENNReal` upper bound on the extended coefficient cost gives the same
real upper bound for `pqCost`.

This local helper mirrors the private conversion lemma used in the weak-grid
completeness machinery.
-/
theorem pqCost_le_of_pqCostENNReal_le
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {A : WeakGridSpace.AtomFamily G s p u} {g : Lp ℂ p G.measure} {C : ℝ}
    (R : WeakGridSpace.LpGridRepresentation A g)
    (hENNReal : WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R ≤
      ENNReal.ofReal C)
    (hC : 0 ≤ C) :
    WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤ C := by
  have hfin :
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R :=
    WeakGridSpace.LpGridRepresentation.finitePQCost_of_pqCostENNReal_le
      (G := G) (s := s) (p := p) (u := u) (q := q) (A := A) R
      (Fact.out : 1 ≤ q) hENNReal
  by_cases hq : q = ∞
  · simp only [WeakGridSpace.LpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [WeakGridSpace.LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hENNReal
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨k, rfl⟩
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp
      ((le_sSup (Set.mem_range.mpr ⟨k, rfl⟩)).trans hENNReal)
  · simp only [WeakGridSpace.LpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hfin
    simp only [WeakGridSpace.LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte] at hENNReal
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have h_nonneg : ∀ k, 0 ≤ R.levelCoeffPower k ^ (q.toReal / p.toReal) :=
      fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
    rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg hfin,
        ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg h_nonneg)
          (div_nonneg zero_le_one hq_pos.le)] at hENNReal
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp hENNReal

/-- The zero `LpGridRepresentation` has zero coefficient cost. -/
private theorem zero_lpgGridRepresentation_pqCost
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A : WeakGridSpace.AtomFamily G s p u) :
    let R : WeakGridSpace.LpGridRepresentation A (0 : Lp ℂ p G.measure) :=
      { block := fun k => WeakGridSpace.LevelBlock.zero A k
        hasSum := by simp }
    WeakGridSpace.LpGridRepresentation.pqCost (q := q) R = 0 := by
  classical
  intro R
  have hp_pos : 0 < p.toReal :=
    (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  have hp_inv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
  have hzero : ∀ k, R.levelCoeffPower k = 0 := by
    intro k
    unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
    simp [R, WeakGridSpace.LevelBlock.zero, Real.zero_rpow hp_pos.ne']
  by_cases hq : q = ∞
  · simp [WeakGridSpace.LpGridRepresentation.pqCost, hq, hzero,
      Real.zero_rpow hp_inv_pos.ne']
  · have hq_zero_ne : q ≠ 0 :=
      ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ q))
    have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq_zero_ne hq
    have hpow_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
    have hq_inv_pos : 0 < q.toReal⁻¹ := inv_pos.mpr hq_pos
    simp [WeakGridSpace.LpGridRepresentation.pqCost, hq, hzero,
      Real.zero_rpow hpow_pos.ne', Real.zero_rpow hq_inv_pos.ne']

/--
Souza-Besov elements admit almost-minimizing atomic representations.

This is the Lean version of the manuscript's sentence saying that, for every
`ε > 0`, one may choose a Besov representation whose coefficient cost is within
`ε` of the Besov gauge.  The statement is additive, which is the form supplied
by the abstract infimum lemma; the usual multiplicative `(1 + ε)` version
follows from this by a routine case split on whether the gauge vanishes.
-/
theorem exists_souzaBesovSpace_representation_cost_lt_norm_add
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (g : SouzaBesovSpace G s p q hs hp hp_top) {ε : ℝ} (hε : 0 < ε) :
    ∃ R :
        WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (g : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R <
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q g + ε := by
  simpa [SouzaBesovSpace] using
    (WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add
      (A := souzaAtomFamily G s p hs hp hp_top) (q := q)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations
        (A := souzaAtomFamily G s p hs hp hp_top) q)
      g hε)

/--
Multiplicative almost-minimizing form away from the zero-gauge case.

When the Besov gauge of `g` is positive, the additive approximation lemma gives
a representation with cost at most `(1 + ε)` times that gauge.  This is the
form used in the paper's displayed estimate.
-/
theorem exists_souzaBesovSpace_representation_cost_le_one_add_mul_norm
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (g : SouzaBesovSpace G s p q hs hp hp_top) {ε : ℝ} (hε : 0 < ε)
    (hg_pos :
      0 <
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs hp hp_top) q g) :
    ∃ R :
        WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (g : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
          (1 + ε) *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q g := by
  let N : ℝ :=
    WeakGridSpace.BesovishSpace.Norm_Costpq
      (souzaAtomFamily G s p hs hp hp_top) q g
  have hδ : 0 < ε * N := mul_pos hε (by simpa [N] using hg_pos)
  rcases exists_souzaBesovSpace_representation_cost_lt_norm_add
      (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
      (q := q) g hδ with
    ⟨R, hRfin, hRlt⟩
  refine ⟨R, hRfin, ?_⟩
  calc
    WeakGridSpace.LpGridRepresentation.pqCost (q := q) R
        ≤ N + ε * N := le_of_lt (by simpa [N] using hRlt)
    _ = (1 + ε) * N := by ring
    _ =
          (1 + ε) *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q g := by
        rfl

/--
Full multiplicative almost-minimizing representation.

This is the exact formal version of the preprint's displayed choice of
representation with cost bounded by `(1 + ε)` times the Besov gauge.
-/
theorem exists_souzaBesovSpace_representation_cost_le_one_add_mul_norm'
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (g : SouzaBesovSpace G s p q hs hp hp_top) {ε : ℝ} (hε : 0 < ε) :
    ∃ R :
        WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (g : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
          (1 + ε) *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q g := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let N : ℝ := WeakGridSpace.BesovishSpace.Norm_Costpq A q g
  rcases lt_or_eq_of_le
      (WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
        (A := A) (q := q)
        (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := A) q) g) with
    hN_pos | hN_zero
  · simpa [A, N] using
      exists_souzaBesovSpace_representation_cost_le_one_add_mul_norm
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
        (q := q) g hε hN_pos
  · have hCco :
        WeakGridSpace.LpGridRepresentation.cCoefficientFinite p q
          (fun k => (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s p p k) ^ p.toReal) :=
      (souza_assumptionG2 G s p q hs hp hp_top).1
    have hg_zero : g = 0 :=
      WeakGridSpace.BesovishSpace.eq_zero_of_Norm_Costpq_eq_zero
        (A := A) (q := q) hp_top hCco
        (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := A) q)
        (by simpa [A, N] using hN_zero.symm)
    subst g
    let R : WeakGridSpace.LpGridRepresentation A (0 : Lp ℂ p G.toWeakGridSpace.measure) :=
      { block := fun k => WeakGridSpace.LevelBlock.zero A k
        hasSum := by simp }
    refine ⟨R, ?_, ?_⟩
    · have hp_pos : 0 < p.toReal :=
        (ENNReal.toReal_pos_iff_ne_top p).2 hp_top
      have hp_inv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
      have hzero : ∀ k, R.levelCoeffPower k = 0 := by
        intro k
        unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
        simp [R, WeakGridSpace.LevelBlock.zero, Real.zero_rpow hp_pos.ne']
      by_cases hq : q = ∞
      · simp [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, hzero,
          Real.zero_rpow hp_inv_pos.ne']
      · have hq_zero_ne : q ≠ 0 :=
          ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ q))
        have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq_zero_ne hq
        have hpow_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
        simp [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, hzero,
          Real.zero_rpow hpow_pos.ne']
    · have hcost : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R = 0 := by
        simpa [R, A] using zero_lpgGridRepresentation_pqCost (A := A) (q := q)
      rw [hcost]
      exact mul_nonneg (by linarith)
        (WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
          (A := souzaAtomFamily G s p hs hp hp_top) (q := q)
          (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations
            (A := souzaAtomFamily G s p hs hp hp_top) q)
          (0 : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q))

/--
Finite standard representation norm supplies a Souza-Besov element.

This packages the canonical standard block sequence as an abstract
`LpGridRepresentation` with finite coefficient cost.  It is the bridge between
the concrete standard coefficient gauge `N_st(f)` and the abstract Besov
machinery used by the embedding theorems.
-/
theorem exists_souzaBesovSpace_of_standardRepresentationNorm_ne_top
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (hN :
      StandardAtomicRepresentation.standardRepresentationNorm
        G F s hs p hp_top q f hf ≠ ∞) :
    ∃ hfLp : MemLp f p G.grid.μ,
      ∃ g : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top),
        (g : Lp ℂ p G.toWeakGridSpace.measure) = hfLp.toLp f := by
  classical
  rcases
    StandardAtomicRepresentation.finite_standardRepresentationNorm_implies_memLp_and_hasSum
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q)
      f hf hN with
    ⟨hfLp, hstandard_sum⟩
  have hfin :
      WeakGridSpace.AbstractFinitePQCost
        (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) (q := q)
        (StandardAtomicRepresentation.canonicalStandardBlockSeq
          G F s hs p hp_top f hf) :=
    StandardAtomicRepresentation.abstractFinitePQCost_canonicalStandardBlockSeq_of_standardRepresentationNorm_ne_top
        (G := G) (F := F) (s := s) (hs := hs) (p := p)
        (hp_top := hp_top) (q := q) f hf hN
  let R :
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
        (hfLp.toLp f) :=
    { block :=
        StandardAtomicRepresentation.canonicalStandardBlockSeq
          G F s hs p hp_top f hf
      hasSum := hstandard_sum }
  have hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R := by
    simpa [R, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.AbstractFinitePQCost,
      WeakGridSpace.blockLvlCoeff_eq_levelCoeffPower] using hfin
  have hmem :
      hfLp.toLp f ∈ SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top) := by
    change
      WeakGridSpace.MemBesovishCoeffCost
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q (hfLp.toLp f)
    exact ⟨R, by simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost] using hRfin⟩
  exact ⟨hfLp, ⟨hfLp.toLp f, hmem⟩, rfl⟩

/--
The canonical standard representation has real coefficient cost bounded by
the standard coefficient gauge.

This is the cost-refined version of
`exists_souzaBesovSpace_of_standardRepresentationNorm_ne_top`: the Souza-Besov
element is represented by the actual canonical standard blocks, and the
abstract real cost of that representation is no larger than `N_st(f)`.
-/
theorem exists_souzaBesovSpace_representation_of_standardRepresentationNorm_ne_top
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (hN :
      StandardAtomicRepresentation.standardRepresentationNorm
        G F s hs p hp_top q f hf ≠ ∞) :
    ∃ hfLp : MemLp f p G.grid.μ,
      ∃ g : SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top),
        ∃ R :
          WeakGridSpace.LpGridRepresentation
            (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
            (g : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
            (g : Lp ℂ p G.toWeakGridSpace.measure) = hfLp.toLp f ∧
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
                (StandardAtomicRepresentation.standardRepresentationNorm
                  G F s hs p hp_top q f hf).toReal := by
  classical
  rcases
    StandardAtomicRepresentation.finite_standardRepresentationNorm_implies_memLp_and_hasSum
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q)
      f hf hN with
    ⟨hfLp, hstandard_sum⟩
  let R₀ :
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
        (hfLp.toLp f) :=
    { block :=
        StandardAtomicRepresentation.canonicalStandardBlockSeq
          G F s hs p hp_top f hf
      hasSum := hstandard_sum }
  have hRenn_eq :
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R₀ =
        StandardAtomicRepresentation.standardRepresentationNorm
          G F s hs p hp_top q f hf := by
    by_cases hq : q = ∞
    · simp [WeakGridSpace.LpGridRepresentation.pqCostENNReal,
        StandardAtomicRepresentation.standardRepresentationNorm, hq, R₀,
        WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        StandardAtomicRepresentation.standardBlockCoeffPower,
        StandardAtomicRepresentation.canonicalStandardBlockSeq]
    · simp [WeakGridSpace.LpGridRepresentation.pqCostENNReal,
        StandardAtomicRepresentation.standardRepresentationNorm, hq, R₀,
        WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        StandardAtomicRepresentation.standardBlockCoeffPower,
        StandardAtomicRepresentation.canonicalStandardBlockSeq]
  have hRenn_le :
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R₀ ≤
        ENNReal.ofReal
          (StandardAtomicRepresentation.standardRepresentationNorm
            G F s hs p hp_top q f hf).toReal := by
    rw [hRenn_eq, ENNReal.ofReal_toReal hN]
  have hRcost_le :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R₀ ≤
        (StandardAtomicRepresentation.standardRepresentationNorm
          G F s hs p hp_top q f hf).toReal :=
    pqCost_le_of_pqCostENNReal_le
      (R := R₀) hRenn_le ENNReal.toReal_nonneg
  have hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R₀ :=
    WeakGridSpace.LpGridRepresentation.finitePQCost_of_pqCostENNReal_le
      R₀ (Fact.out : 1 ≤ q) hRenn_le
  have hmem :
      hfLp.toLp f ∈ SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top) := by
    change
      WeakGridSpace.MemBesovishCoeffCost
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q (hfLp.toLp f)
    exact ⟨R₀, by simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost] using hRfin⟩
  refine ⟨hfLp, ⟨hfLp.toLp f, hmem⟩, ?_⟩
  let R :
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
        ((⟨hfLp.toLp f, hmem⟩ :
          SouzaBesovSpace G s p q hs Fact.out (ne_of_lt hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure) := R₀
  exact ⟨R, by simpa [R] using hRfin, rfl, by simpa [R] using hRcost_le⟩

/--
The `L^p` term in the mean-oscillation norm is bounded by the standard atomic
coefficient gauge.

This is the formal counterpart of the manuscript's use of Proposition `lp`:
after viewing the standard atomic expansion as a Souza-Besov representation,
the existing `L^p` embedding estimate bounds `‖f‖_p` by the representation
cost, and hence by the standard gauge.
-/
theorem exists_lpnorm_term_le_const_mul_standardRepresentationNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ),
        StandardAtomicRepresentation.standardRepresentationNorm
            G F s hs p hp_top q f hf ≠ ∞ →
          (G.grid.μ Set.univ) ^ (-s) * eLpNorm f p G.grid.μ ≤
            C *
              StandardAtomicRepresentation.standardRepresentationNorm
                G F s hs p hp_top q f hf := by
  classical
  let K : ℝ :=
    ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
      WeakGridSpace.LpGridRepresentation.cCoefficient p q
        (fun k =>
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s p p k) ^ p.toReal)
  let μI : ℝ := (G.grid.μ Set.univ).toReal
  refine ⟨ENNReal.ofReal (μI ^ (-s) * K), ENNReal.ofReal_ne_top, ?_⟩
  intro f hf hN
  rcases exists_souzaBesovSpace_representation_of_standardRepresentationNorm_ne_top
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top)
      (q := q) f hf hN with
    ⟨hfLp, g, R, hRfin, hg_eq, hRcost⟩
  have hCco :
      WeakGridSpace.LpGridRepresentation.cCoefficientFinite p q
        (fun k =>
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s p p k) ^ p.toReal) :=
    (souza_assumptionG2 G s p q hs Fact.out (ne_of_lt hp_top)).1
  have ht_le_pu : p ≤ p * ∞ := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * ∞ := mul_le_mul_right le_top p
  have hs_nonneg : 0 ≤ s - 1 / p.toReal + 1 / p.toReal := by
    linarith [hs.le]
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (by positivity)
      (WeakGridSpace.LpGridRepresentation.cCoefficient_nonneg p q
        (fun k =>
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s p p k) ^ p.toReal)
        (fun k => Real.rpow_nonneg
          (WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg
            G.toWeakGridSpace s p p k) _))
  have hg_ae :
      ((g : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =ᵐ[G.grid.μ] f := by
    rw [hg_eq]
    exact MemLp.coeFn_toLp hfLp
  have heLp_toReal :
      (eLpNorm ((g : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
          p G.grid.μ).toReal =
        (eLpNorm f p G.grid.μ).toReal :=
    congrArg ENNReal.toReal (MeasureTheory.eLpNorm_congr_ae hg_ae)
  have hNorm_le_cost :
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q g ≤
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
      (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
      (q := q) g R hRfin
  have hLp_real :
      (eLpNorm f p G.grid.μ).toReal ≤ K *
        (StandardAtomicRepresentation.standardRepresentationNorm
          G F s hs p hp_top q f hf).toReal := by
    calc
      (eLpNorm f p G.grid.μ).toReal
          =
            (eLpNorm ((g : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
              p G.grid.μ).toReal := heLp_toReal.symm
      _ ≤ K *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q g := by
          simpa [K, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid] using
            WeakGridSpace.BesovishSpace.lp_norm_le_const_mul_Norm_Costpq
              (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top))
              (q := q) (t := p)
              (hp_top := ne_of_lt hp_top) (ht_top := ne_of_lt hp_top)
              (hp_le_t := le_rfl) (ht_le_pu := ht_le_pu)
              (hs_nonneg := hs_nonneg) (hCco_fin := hCco)
              (hA :=
                WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations
                  (A := souzaAtomFamily G s p hs Fact.out (ne_of_lt hp_top)) q)
              g
      _ ≤ K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
          mul_le_mul_of_nonneg_left hNorm_le_cost hK_nonneg
      _ ≤ K *
            (StandardAtomicRepresentation.standardRepresentationNorm
              G F s hs p hp_top q f hf).toReal :=
          mul_le_mul_of_nonneg_left hRcost hK_nonneg
  have hμ_pos : 0 < G.grid.μ Set.univ :=
    G.grid.positive_measure 0 Set.univ
      (by simp [G.grid.grid.first_partition_eq_univ])
  letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ :=
    MeasureTheory.measure_ne_top G.grid.μ Set.univ
  have hμ_toReal_pos : 0 < μI := by
    simpa [μI] using ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
  have hμ_toReal_pos' : 0 < (G.grid.μ Set.univ).toReal := by
    simpa [μI] using hμ_toReal_pos
  have hμpow_nonneg : 0 ≤ μI ^ (-s) :=
    Real.rpow_nonneg hμ_toReal_pos.le _
  have hμpow_eq : ENNReal.ofReal (μI ^ (-s)) = (G.grid.μ Set.univ) ^ (-s) := by
    change ENNReal.ofReal ((G.grid.μ Set.univ).toReal ^ (-s)) =
      (G.grid.μ Set.univ) ^ (-s)
    rw [← ENNReal.ofReal_rpow_of_pos hμ_toReal_pos',
      ENNReal.ofReal_toReal hμ_ne_top]
  have heLp_eq :
      ENNReal.ofReal (eLpNorm f p G.grid.μ).toReal =
        eLpNorm f p G.grid.μ :=
    ENNReal.ofReal_toReal hfLp.eLpNorm_ne_top
  have hreal :
      μI ^ (-s) * (eLpNorm f p G.grid.μ).toReal ≤
        μI ^ (-s) * K *
          (StandardAtomicRepresentation.standardRepresentationNorm
            G F s hs p hp_top q f hf).toReal := by
    calc
      μI ^ (-s) * (eLpNorm f p G.grid.μ).toReal
          ≤ μI ^ (-s) *
              (K *
                (StandardAtomicRepresentation.standardRepresentationNorm
                  G F s hs p hp_top q f hf).toReal) :=
            mul_le_mul_of_nonneg_left hLp_real hμpow_nonneg
      _ =
          μI ^ (-s) * K *
            (StandardAtomicRepresentation.standardRepresentationNorm
              G F s hs p hp_top q f hf).toReal := by ring
  calc
    (G.grid.μ Set.univ) ^ (-s) * eLpNorm f p G.grid.μ
        =
          ENNReal.ofReal (μI ^ (-s) * (eLpNorm f p G.grid.μ).toReal) := by
        rw [← hμpow_eq, ← heLp_eq]
        rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
        exact (ENNReal.ofReal_mul hμpow_nonneg).symm
    _ ≤
          ENNReal.ofReal
            (μI ^ (-s) * K *
              (StandardAtomicRepresentation.standardRepresentationNorm
                G F s hs p hp_top q f hf).toReal) :=
        ENNReal.ofReal_le_ofReal hreal
    _ =
          ENNReal.ofReal (μI ^ (-s) * K) *
            StandardAtomicRepresentation.standardRepresentationNorm
              G F s hs p hp_top q f hf := by
        rw [← ENNReal.ofReal_toReal hN]
        rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
        rw [← ENNReal.ofReal_mul (mul_nonneg hμpow_nonneg hK_nonneg)]

private theorem levelCoeffPower_root_le_pqCost
    {G : WeakGridSpace.WeakGridSpace (α := α)}
    {s : ℝ} {p u q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {A : WeakGridSpace.AtomFamily G s p u}
    {g : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A g)
    (hp_top : p ≠ ∞)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (k : ℕ) :
    (R.levelCoeffPower k) ^ (1 / p.toReal) ≤
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  classical
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_top
  by_cases hqtop : q = ∞
  · have hbdd : BddAbove
        (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)) := by
      simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hRfin
    rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos hqtop]
    exact le_csSup hbdd ⟨k, rfl⟩
  · have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hqtop
    have hsum_nonneg :
        0 ≤ ∑' n, (R.levelCoeffPower n) ^ (q.toReal / p.toReal) :=
      tsum_nonneg fun n => Real.rpow_nonneg (R.levelCoeffPower_nonneg n) _
    have hterm_le :
        (R.levelCoeffPower k) ^ (q.toReal / p.toReal)
          ≤ ∑' n, (R.levelCoeffPower n) ^ (q.toReal / p.toReal) := by
      have hsum : Summable fun n => (R.levelCoeffPower n) ^ (q.toReal / p.toReal) := by
        simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hRfin
      simpa using
        sum_le_hasSum ({k} : Finset ℕ)
          (fun n _ => Real.rpow_nonneg (R.levelCoeffPower_nonneg n) _) hsum.hasSum
    have hpow_le :=
      Real.rpow_le_rpow (Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _)
        hterm_le (div_nonneg zero_le_one hq_pos.le)
    have hleft :
        ((R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) =
          (R.levelCoeffPower k) ^ (1 / p.toReal) := by
      have hdiv : q.toReal / p.toReal * (1 / q.toReal) = 1 / p.toReal := by
        field_simp [hq_pos.ne']
      calc
        ((R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)
            = (R.levelCoeffPower k) ^ ((q.toReal / p.toReal) * (1 / q.toReal)) := by
                rw [← Real.rpow_mul (R.levelCoeffPower_nonneg k)]
        _ = (R.levelCoeffPower k) ^ (1 / p.toReal) := by rw [hdiv]
    rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hqtop]
    rw [hleft] at hpow_le
    exact hpow_le

private theorem geometric_tail_kernel_summable
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s) :
    Summable fun i : ℕ => (G.grid.lambda2 ^ (i + 1)) ^ s := by
  have hlambda2_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  let ρ : ℝ := G.grid.lambda2 ^ s
  have hρ_nonneg : 0 ≤ ρ := by
    dsimp [ρ]
    exact (Real.rpow_pos_of_pos hlambda2_pos s).le
  have hρ_lt_one : ρ < 1 := by
    dsimp [ρ]
    exact Real.rpow_lt_one hlambda2_pos.le G.grid.hlambda2_lt_one hs
  have hgeom : Summable fun i : ℕ => ρ ^ (i + 1) := by
    simpa [pow_succ, mul_comm, Nat.add_comm] using
      (summable_geometric_of_lt_one hρ_nonneg hρ_lt_one).mul_left ρ
  refine hgeom.congr ?_
  intro i
  dsimp [ρ]
  simpa [Nat.add_comm] using
    Real.rpow_pow_comm hlambda2_pos.le s (i + 1)

private noncomputable def realSequenceLqGauge (q : ℝ≥0∞) (a : ℕ → ℝ) : ℝ :=
  if q = ∞ then
    sSup (Set.range a)
  else
    (∑' k, a k ^ q.toReal) ^ (1 / q.toReal)

private theorem levelCoeffRoot_realSequenceLqGauge_eq_pqCost
    {G : WeakGridSpace.WeakGridSpace (α := α)}
    {s : ℝ} {p u q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {A : WeakGridSpace.AtomFamily G s p u}
    {g : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A g)
    (hp_top : p ≠ ∞) :
    let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
    realSequenceLqGauge q a =
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  classical
  intro a
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_top
  by_cases hqtop : q = ∞
  · simp [realSequenceLqGauge, WeakGridSpace.LpGridRepresentation.pqCost,
      hqtop, a, one_div]
  · have hpow :
        ∀ k, a k ^ q.toReal =
          R.levelCoeffPower k ^ (q.toReal / p.toReal) := by
      intro k
      have hlevel_nonneg : 0 ≤ R.levelCoeffPower k :=
        R.levelCoeffPower_nonneg k
      have hdiv : (1 / p.toReal) * q.toReal = q.toReal / p.toReal := by
        ring
      calc
        a k ^ q.toReal
            = ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ q.toReal := rfl
        _ = R.levelCoeffPower k ^ ((1 / p.toReal) * q.toReal) := by
            rw [← Real.rpow_mul hlevel_nonneg]
        _ = R.levelCoeffPower k ^ (q.toReal / p.toReal) := by
            rw [hdiv]
    simp only [realSequenceLqGauge, hqtop, ↓reduceIte,
      WeakGridSpace.LpGridRepresentation.pqCost]
    congr 1
    exact tsum_congr hpow

private theorem future_convolution_lqGauge_le
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    {a b : ℕ → ℝ}
    (ha_nonneg : ∀ k, 0 ≤ a k)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hb_sum : Summable b)
    (ha_fin :
      if q = ∞ then
        BddAbove (Set.range a)
      else
        Summable fun k => a k ^ q.toReal) :
    realSequenceLqGauge q (fun k => ∑' i, b i * a (k + (i + 1))) ≤
      (∑' i, b i) * realSequenceLqGauge q a := by
  classical
  by_cases hqtop : q = ∞
  · subst q
    simp only [realSequenceLqGauge]
    have ha_bdd : BddAbove (Set.range a) := by
      simpa using ha_fin
    let A : ℝ := sSup (Set.range a)
    have hA_nonneg : 0 ≤ A := by
      exact (ha_nonneg 0).trans (le_csSup ha_bdd ⟨0, rfl⟩)
    have ha_le_A : ∀ k, a k ≤ A := by
      intro k
      exact le_csSup ha_bdd ⟨k, rfl⟩
    have hbA_sum : Summable fun i => b i * A := hb_sum.mul_right A
    have hconv_le : ∀ k, (∑' i, b i * a (k + (i + 1))) ≤ (∑' i, b i) * A := by
      intro k
      have hterm_le : (fun i => b i * a (k + (i + 1))) ≤ fun i => b i * A := by
        intro i
        exact mul_le_mul_of_nonneg_left (ha_le_A (k + (i + 1))) (hb_nonneg i)
      have hterm_sum : Summable fun i => b i * a (k + (i + 1)) :=
        Summable.of_nonneg_of_le
          (fun i => mul_nonneg (hb_nonneg i) (ha_nonneg _))
          hterm_le hbA_sum
      calc
        (∑' i, b i * a (k + (i + 1))) ≤ ∑' i, b i * A :=
          hterm_sum.tsum_le_tsum hterm_le hbA_sum
        _ = (∑' i, b i) * A := by
          simpa [mul_comm] using (hb_sum.hasSum.mul_right A).tsum_eq
    have hconv_bdd : BddAbove (Set.range fun k => ∑' i, b i * a (k + (i + 1))) :=
      ⟨(∑' i, b i) * A, by
        rintro x ⟨k, rfl⟩
        exact hconv_le k⟩
    refine csSup_le (Set.range_nonempty _) ?_
    rintro x ⟨k, rfl⟩
    simpa [A] using hconv_le k
  · have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hqtop
    have hq_one : 1 ≤ q.toReal := (ENNReal.dichotomy q).resolve_left hqtop
    have ha_q : Summable fun k => a k ^ q.toReal := by
      simpa [hqtop] using ha_fin
    let E : ℕ → Type := fun _ => ℝ
    let A : lp E q := ⟨a, memℓp_gen (by
      refine ha_q.congr ?_
      intro k
      rw [Real.norm_of_nonneg (ha_nonneg k)] )⟩
    have hA_norm :
        ‖A‖ = (∑' k, a k ^ q.toReal) ^ (1 / q.toReal) := by
      rw [lp.norm_eq_tsum_rpow hq_pos A]
      congr 1
      refine tsum_congr fun k => ?_
      simp [A, E, Real.norm_of_nonneg (ha_nonneg k)]
    let V : ℕ → lp E q := fun i =>
      ⟨fun k => b i * a (k + (i + 1)), memℓp_gen (by
        have hshift : Summable fun k => a (k + (i + 1)) ^ q.toReal := by
          have h := (summable_nat_add_iff (i + 1)).mpr ha_q
          simpa [Nat.add_assoc] using h
        have hscaled :
            Summable fun k => (b i) ^ q.toReal * a (k + (i + 1)) ^ q.toReal :=
          hshift.mul_left ((b i) ^ q.toReal)
        refine hscaled.congr ?_
        intro k
        have hterm_nonneg : 0 ≤ b i * a (k + (i + 1)) :=
          mul_nonneg (hb_nonneg i) (ha_nonneg _)
        rw [Real.norm_of_nonneg hterm_nonneg]
        exact (Real.mul_rpow (hb_nonneg i) (ha_nonneg _)).symm)⟩
    have hV_norm_le : ∀ i, ‖V i‖ ≤ b i * ‖A‖ := by
      intro i
      have hC_nonneg : 0 ≤ b i * ‖A‖ :=
        mul_nonneg (hb_nonneg i) (norm_nonneg _)
      refine lp.norm_le_of_tsum_le hq_pos hC_nonneg ?_
      have hshift_le :
          (∑' k, a (k + (i + 1)) ^ q.toReal) ≤ ∑' k, a k ^ q.toReal := by
        have hcomp :
            (∑' k, (fun n => a n ^ q.toReal) (k + (i + 1))) ≤
              ∑' k, a k ^ q.toReal :=
          tsum_comp_le_tsum_of_inj ha_q
            (fun k => Real.rpow_nonneg (ha_nonneg k) _)
            (by
              intro m n hmn
              exact Nat.add_right_cancel hmn)
        simpa [Function.comp_def, Nat.add_assoc] using hcomp
      have hsum_norm :
          (∑' k, ‖(V i : lp E q) k‖ ^ q.toReal)
            = (b i) ^ q.toReal * ∑' k, a (k + (i + 1)) ^ q.toReal := by
        have hshift : Summable fun k => a (k + (i + 1)) ^ q.toReal := by
          have h := (summable_nat_add_iff (i + 1)).mpr ha_q
          simpa [Nat.add_assoc] using h
        rw [← (hshift.hasSum.mul_left ((b i) ^ q.toReal)).tsum_eq]
        refine tsum_congr fun k => ?_
        have hterm_nonneg : 0 ≤ b i * a (k + (i + 1)) :=
          mul_nonneg (hb_nonneg i) (ha_nonneg _)
        simp [V, E, Real.norm_of_nonneg hterm_nonneg,
          Real.mul_rpow (hb_nonneg i) (ha_nonneg _)]
      have hA_pow :
          ∑' k, a k ^ q.toReal = ‖A‖ ^ q.toReal := by
        rw [hA_norm]
        have hsum_nonneg : 0 ≤ ∑' k, a k ^ q.toReal :=
          tsum_nonneg fun k => Real.rpow_nonneg (ha_nonneg k) _
        simpa [one_div] using
          (Real.rpow_inv_rpow hsum_nonneg hq_pos.ne').symm
      have hmul_le :
          (b i) ^ q.toReal * ∑' k, a (k + (i + 1)) ^ q.toReal
            ≤ (b i) ^ q.toReal * ‖A‖ ^ q.toReal := by
        rw [← hA_pow]
        exact mul_le_mul_of_nonneg_left hshift_le
          (Real.rpow_nonneg (hb_nonneg i) _)
      calc
        (∑' k, ‖(V i : lp E q) k‖ ^ q.toReal)
            = (b i) ^ q.toReal * ∑' k, a (k + (i + 1)) ^ q.toReal := hsum_norm
        _ ≤ (b i) ^ q.toReal * ‖A‖ ^ q.toReal := hmul_le
        _ = (b i * ‖A‖) ^ q.toReal := by
          exact (Real.mul_rpow (hb_nonneg i) (norm_nonneg _)).symm
    have hV_norm_sum : Summable fun i => ‖V i‖ :=
      Summable.of_nonneg_of_le
        (fun i => norm_nonneg _)
        hV_norm_le
        (hb_sum.mul_right ‖A‖)
    have hV_summable : Summable V := hV_norm_sum.of_norm
    let W : lp E q := ∑' i, V i
    have hW_norm :
        ‖W‖ ≤ (∑' i, b i) * ‖A‖ := by
      calc
        ‖W‖ ≤ ∑' i, ‖V i‖ := by
          simpa [W] using norm_tsum_le_tsum_norm hV_norm_sum
        _ ≤ ∑' i, b i * ‖A‖ :=
          hV_norm_sum.tsum_le_tsum hV_norm_le (hb_sum.mul_right ‖A‖)
        _ = (∑' i, b i) * ‖A‖ := by
          simpa [mul_comm] using (hb_sum.hasSum.mul_right ‖A‖).tsum_eq
    have hcoord : ∀ k, (W : (i : ℕ) → E i) k =
        ∑' i, b i * a (k + (i + 1)) := by
      intro k
      have hhas :
          HasSum (fun i => (V i : (j : ℕ) → E j) k) ((W : (j : ℕ) → E j) k) := by
        simpa [W] using
          (lp.evalCLM ℝ E q k).hasSum hV_summable.hasSum
      exact hhas.tsum_eq.symm
    have hconv_nonneg : ∀ k, 0 ≤ ∑' i, b i * a (k + (i + 1)) := by
      intro k
      exact tsum_nonneg fun i => mul_nonneg (hb_nonneg i) (ha_nonneg _)
    simp only [realSequenceLqGauge, if_neg hqtop]
    calc
      (∑' k, (∑' i, b i * a (k + (i + 1))) ^ q.toReal) ^ (1 / q.toReal)
          = ‖W‖ := by
            rw [lp.norm_eq_tsum_rpow hq_pos W]
            congr 1
            refine tsum_congr fun k => ?_
            rw [hcoord k]
            simp [Real.norm_of_nonneg (hconv_nonneg k)]
      _ ≤ (∑' i, b i) * ‖A‖ := hW_norm
      _ = (∑' i, b i) * (∑' k, a k ^ q.toReal) ^ (1 / q.toReal) := by
            rw [hA_norm]

private theorem future_convolution_summable_rpow
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    {a b : ℕ → ℝ}
    (hqtop : q ≠ ∞)
    (ha_nonneg : ∀ k, 0 ≤ a k)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hb_sum : Summable b)
    (ha_q : Summable fun k => a k ^ q.toReal) :
    Summable fun k => (∑' i, b i * a (k + (i + 1))) ^ q.toReal := by
  classical
  have hq_pos : 0 < q.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hqtop
  let E : ℕ → Type := fun _ => ℝ
  let A : lp E q := ⟨a, memℓp_gen (by
    refine ha_q.congr ?_
    intro k
    rw [Real.norm_of_nonneg (ha_nonneg k)])⟩
  have hA_norm :
      ‖A‖ = (∑' k, a k ^ q.toReal) ^ (1 / q.toReal) := by
    rw [lp.norm_eq_tsum_rpow hq_pos A]
    congr 1
    refine tsum_congr fun k => ?_
    simp [A, E, Real.norm_of_nonneg (ha_nonneg k)]
  let V : ℕ → lp E q := fun i =>
    ⟨fun k => b i * a (k + (i + 1)), memℓp_gen (by
      have hshift : Summable fun k => a (k + (i + 1)) ^ q.toReal := by
        have h := (summable_nat_add_iff (i + 1)).mpr ha_q
        simpa [Nat.add_assoc] using h
      have hscaled :
          Summable fun k => (b i) ^ q.toReal * a (k + (i + 1)) ^ q.toReal :=
        hshift.mul_left ((b i) ^ q.toReal)
      refine hscaled.congr ?_
      intro k
      have hterm_nonneg : 0 ≤ b i * a (k + (i + 1)) :=
        mul_nonneg (hb_nonneg i) (ha_nonneg _)
      rw [Real.norm_of_nonneg hterm_nonneg]
      exact (Real.mul_rpow (hb_nonneg i) (ha_nonneg _)).symm)⟩
  have hV_norm_le : ∀ i, ‖V i‖ ≤ b i * ‖A‖ := by
    intro i
    have hC_nonneg : 0 ≤ b i * ‖A‖ :=
      mul_nonneg (hb_nonneg i) (norm_nonneg _)
    refine lp.norm_le_of_tsum_le hq_pos hC_nonneg ?_
    have hshift_le :
        (∑' k, a (k + (i + 1)) ^ q.toReal) ≤ ∑' k, a k ^ q.toReal := by
      have hcomp :
          (∑' k, (fun n => a n ^ q.toReal) (k + (i + 1))) ≤
            ∑' k, a k ^ q.toReal :=
        tsum_comp_le_tsum_of_inj ha_q
          (fun k => Real.rpow_nonneg (ha_nonneg k) _)
          (by
            intro m n hmn
            exact Nat.add_right_cancel hmn)
      simpa [Function.comp_def, Nat.add_assoc] using hcomp
    have hsum_norm :
        (∑' k, ‖(V i : lp E q) k‖ ^ q.toReal)
          = (b i) ^ q.toReal * ∑' k, a (k + (i + 1)) ^ q.toReal := by
      have hshift : Summable fun k => a (k + (i + 1)) ^ q.toReal := by
        have h := (summable_nat_add_iff (i + 1)).mpr ha_q
        simpa [Nat.add_assoc] using h
      rw [← (hshift.hasSum.mul_left ((b i) ^ q.toReal)).tsum_eq]
      refine tsum_congr fun k => ?_
      have hterm_nonneg : 0 ≤ b i * a (k + (i + 1)) :=
        mul_nonneg (hb_nonneg i) (ha_nonneg _)
      simp [V, E, Real.norm_of_nonneg hterm_nonneg,
        Real.mul_rpow (hb_nonneg i) (ha_nonneg _)]
    have hA_pow :
        ∑' k, a k ^ q.toReal = ‖A‖ ^ q.toReal := by
      rw [hA_norm]
      have hsum_nonneg : 0 ≤ ∑' k, a k ^ q.toReal :=
        tsum_nonneg fun k => Real.rpow_nonneg (ha_nonneg k) _
      simpa [one_div] using
        (Real.rpow_inv_rpow hsum_nonneg hq_pos.ne').symm
    have hmul_le :
        (b i) ^ q.toReal * ∑' k, a (k + (i + 1)) ^ q.toReal
          ≤ (b i) ^ q.toReal * ‖A‖ ^ q.toReal := by
      rw [← hA_pow]
      exact mul_le_mul_of_nonneg_left hshift_le
        (Real.rpow_nonneg (hb_nonneg i) _)
    calc
      (∑' k, ‖(V i : lp E q) k‖ ^ q.toReal)
          = (b i) ^ q.toReal * ∑' k, a (k + (i + 1)) ^ q.toReal := hsum_norm
      _ ≤ (b i) ^ q.toReal * ‖A‖ ^ q.toReal := hmul_le
      _ = (b i * ‖A‖) ^ q.toReal := by
        exact (Real.mul_rpow (hb_nonneg i) (norm_nonneg _)).symm
  have hV_norm_sum : Summable fun i => ‖V i‖ :=
    Summable.of_nonneg_of_le
      (fun i => norm_nonneg _)
      hV_norm_le
      (hb_sum.mul_right ‖A‖)
  have hV_summable : Summable V := hV_norm_sum.of_norm
  let W : lp E q := ∑' i, V i
  have hcoord : ∀ k, (W : (i : ℕ) → E i) k =
      ∑' i, b i * a (k + (i + 1)) := by
    intro k
    have hhas :
        HasSum (fun i => (V i : (j : ℕ) → E j) k) ((W : (j : ℕ) → E j) k) := by
      simpa [W] using
        (lp.evalCLM ℝ E q k).hasSum hV_summable.hasSum
    exact hhas.tsum_eq.symm
  have hW_summable :
      Summable fun k => ‖(W : (i : ℕ) → E i) k‖ ^ q.toReal :=
    Memℓp.summable hq_pos (lp.memℓp W)
  refine hW_summable.congr ?_
  intro k
  rw [hcoord k]
  have hconv_nonneg : 0 ≤ ∑' i, b i * a (k + (i + 1)) :=
    tsum_nonneg fun i => mul_nonneg (hb_nonneg i) (ha_nonneg _)
  rw [Real.norm_of_nonneg hconv_nonneg]

private theorem localDescendantRoot_lpsum_le_levelCoeffRoot
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (k₀ i : ℕ) :
    (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
      (let A := souzaAtomFamily G s p hs hp hp_top
       let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
       let B := R.block (k₀ + (i + 1))
       let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
       (∑ P : WeakGridSpace.LevelCell W (i + 1),
          ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) ^ p.toReal) ^
      (1 / p.toReal)
      ≤
        (R.levelCoeffPower (k₀ + (i + 1))) ^ (1 / p.toReal) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le hp).ne' hp_top
  let localPower : WeakGridSpace.LevelCell G.toWeakGridSpace k₀ → ℝ := fun J =>
    let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
    let B := R.block (k₀ + (i + 1))
    let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
    ∑ P : WeakGridSpace.LevelCell W (i + 1), ‖BI.coeff P‖ ^ p.toReal
  have hlocal_nonneg :
      ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀, 0 ≤ localPower J := by
    intro J
    dsimp [localPower]
    exact Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _
  have hroot_pow :
      ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        (localPower J ^ (1 / p.toReal)) ^ p.toReal = localPower J := by
    intro J
    simpa [one_div] using Real.rpow_inv_rpow (hlocal_nonneg J) hp_pos.ne'
  have hleft_eq :
      (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        (localPower J ^ (1 / p.toReal)) ^ p.toReal) =
        ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀, localPower J := by
    refine Finset.sum_congr rfl ?_
    intro J _hJ
    exact hroot_pow J
  have hleft_eq_inv :
      (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        (localPower J ^ p.toReal⁻¹) ^ p.toReal) =
        ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀, localPower J := by
    simpa [one_div] using hleft_eq
  have hsum_le :
      (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀, localPower J)
        ≤ R.levelCoeffPower (k₀ + (i + 1)) := by
    simpa [localPower, A, WeakGridSpace.LpGridRepresentation.levelCoeffPower] using
      sum_ambientLevelBlockToInduced_coeffPower_le
        (G := G) (A := A) (k₀ := k₀) (i := i + 1)
        (B := R.block (k₀ + (i + 1)))
  have hleft_nonneg :
      0 ≤ ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        (localPower J ^ (1 / p.toReal)) ^ p.toReal := by
    exact Finset.sum_nonneg fun J _ =>
      Real.rpow_nonneg (Real.rpow_nonneg (hlocal_nonneg J) _) _
  have hpow_le :
      (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        (localPower J ^ (1 / p.toReal)) ^ p.toReal) ^ (1 / p.toReal)
        ≤ (R.levelCoeffPower (k₀ + (i + 1))) ^ (1 / p.toReal) := by
    exact Real.rpow_le_rpow hleft_nonneg
      (by
        rw [hleft_eq]
        exact hsum_le)
      (one_div_nonneg.mpr hp_pos.le)
  simpa [localPower, A] using hpow_le

private theorem weighted_lpTail_restrict_toReal_le_localSeries
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (k₀ : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀) :
    let K := ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal))
    let kernel : ℕ → ℝ := fun i => (G.grid.lambda2 ^ (i + 1)) ^ s
    let localRoot : ℕ → ℝ := fun i =>
      let A := souzaAtomFamily G s p hs hp hp_top
      let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
      let B := R.block (k₀ + (i + 1))
      let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
      (∑ P : WeakGridSpace.LevelCell W (i + 1),
        ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)
    (G.grid.μ J.1).toReal ^ (-s) *
      (MeasureTheory.eLpNorm
        (((g -
          ∑ k ∈ Finset.range (k₀ + 1),
            (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
          Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ))
        p (G.grid.μ.restrict J.1)).toReal
      ≤
        ∑' i, K * kernel i * localRoot i := by
  classical
  intro K kernel localRoot
  let A := souzaAtomFamily G s p hs hp hp_top
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hkernel_sum : Summable kernel := by
    simpa [kernel] using geometric_tail_kernel_summable G s hs
  have hkernel_nonneg : ∀ i, 0 ≤ kernel i := by
    intro i
    dsimp [kernel]
    have hlambda2_nonneg : 0 ≤ G.grid.lambda2 :=
      le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
    exact Real.rpow_nonneg (pow_nonneg hlambda2_nonneg _) _
  have hcost_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
    WeakGridSpace.LpGridRepresentation.pqCost_nonneg R
  have hlocalRoot_nonneg : ∀ i, 0 ≤ localRoot i := by
    intro i
    dsimp [localRoot]
    exact Real.rpow_nonneg
      (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have hlocalRoot_le_cost :
      ∀ i, localRoot i ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
    intro i
    have hroot_le_lpsum :
        localRoot i ≤
          (∑ J' : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
            (let A := souzaAtomFamily G s p hs hp hp_top
             let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J'
             let B := R.block (k₀ + (i + 1))
             let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J' A B
             (∑ P : WeakGridSpace.LevelCell W (i + 1),
                ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) ^ p.toReal) ^
            (1 / p.toReal) := by
      let term : WeakGridSpace.LevelCell G.toWeakGridSpace k₀ → ℝ := fun J' =>
        (let A := souzaAtomFamily G s p hs hp hp_top
         let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J'
         let B := R.block (k₀ + (i + 1))
         let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J' A B
         (∑ P : WeakGridSpace.LevelCell W (i + 1),
            ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) ^ p.toReal
      have hterm_nonneg :
          ∀ J' : WeakGridSpace.LevelCell G.toWeakGridSpace k₀, 0 ≤ term J' := by
        intro J'
        dsimp [term]
        exact Real.rpow_nonneg
          (Real.rpow_nonneg
            (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _) _) _
      have hsingle :
          term J ≤ ∑ J' : WeakGridSpace.LevelCell G.toWeakGridSpace k₀, term J' :=
        Finset.single_le_sum (by intro J' _hJ'; exact hterm_nonneg J') (Finset.mem_univ J)
      have htermJ :
          term J = localRoot i ^ p.toReal := by
        simp [term, localRoot]
      have hroot_pow :
          (localRoot i ^ p.toReal) ^ (1 / p.toReal) = localRoot i := by
        simpa [one_div] using
          Real.rpow_rpow_inv (hlocalRoot_nonneg i) hp_pos.ne'
      calc
        localRoot i = (localRoot i ^ p.toReal) ^ (1 / p.toReal) := hroot_pow.symm
        _ ≤ (∑ J' : WeakGridSpace.LevelCell G.toWeakGridSpace k₀, term J') ^
              (1 / p.toReal) := by
            exact Real.rpow_le_rpow
              (Real.rpow_nonneg (hlocalRoot_nonneg i) _)
              (by simpa [htermJ] using hsingle)
              (one_div_nonneg.mpr hp_pos.le)
        _ =
            (∑ J' : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
              (let A := souzaAtomFamily G s p hs hp hp_top
               let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J'
               let B := R.block (k₀ + (i + 1))
               let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J' A B
               (∑ P : WeakGridSpace.LevelCell W (i + 1),
                  ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) ^ p.toReal) ^
              (1 / p.toReal) := rfl
    exact hroot_le_lpsum.trans
      ((localDescendantRoot_lpsum_le_levelCoeffRoot
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
        (R := R) (k₀ := k₀) (i := i)).trans
        (levelCoeffPower_root_le_pqCost
          (R := R) hp_top hRfin (k₀ + (i + 1))))
  have hlocalSeries_sum : Summable fun i => K * kernel i * localRoot i := by
    have hbound :
        (fun i => K * kernel i * localRoot i)
          ≤ fun i =>
              (K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) * kernel i := by
      intro i
      calc
        K * kernel i * localRoot i = (K * kernel i) * localRoot i := by ring
        _ ≤ (K * kernel i) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
            exact mul_le_mul_of_nonneg_left (hlocalRoot_le_cost i)
              (mul_nonneg hK_nonneg (hkernel_nonneg i))
        _ = (K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) * kernel i := by
            ring
    exact Summable.of_nonneg_of_le
      (fun i => mul_nonneg (mul_nonneg hK_nonneg (hkernel_nonneg i))
        (hlocalRoot_nonneg i))
      hbound
      (hkernel_sum.mul_left
        (K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R))
  have hμ_pos_enn : 0 < G.grid.μ J.1 :=
    G.grid.positive_measure k₀ J.1 J.2
  letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hμ_ne_top : G.grid.μ J.1 ≠ ∞ :=
    MeasureTheory.measure_ne_top G.grid.μ J.1
  have hμ_pos : 0 < (G.grid.μ J.1).toReal :=
    ENNReal.toReal_pos hμ_pos_enn.ne' hμ_ne_top
  have hμs_nonneg : 0 ≤ (G.grid.μ J.1).toReal ^ s :=
    Real.rpow_nonneg hμ_pos.le _
  have hgeom_sum :
      Summable fun i =>
        lpTailLocalGeometricCoeffBound G s p hs hp hp_top R k₀ J i := by
    have hscaled := hlocalSeries_sum.mul_left ((G.grid.μ J.1).toReal ^ s)
    refine hscaled.congr ?_
    intro i
    simp [lpTailLocalGeometricCoeffBound, K, kernel, localRoot,
      mul_assoc, mul_left_comm, mul_comm]
  have htail :=
    eLpNorm_lpTail_restrict_toReal_le_tsum_localGeometricCoeff
      (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
      (hp_top := hp_top) (R := R) (k₀ := k₀) (J := J) hgeom_sum
  have hgeom_tsum_eq :
      (∑' i, lpTailLocalGeometricCoeffBound G s p hs hp hp_top R k₀ J i)
        =
          (G.grid.μ J.1).toReal ^ s * ∑' i, K * kernel i * localRoot i := by
    rw [← (hlocalSeries_sum.hasSum.mul_left ((G.grid.μ J.1).toReal ^ s)).tsum_eq]
    refine tsum_congr fun i => ?_
    simp [lpTailLocalGeometricCoeffBound, K, kernel, localRoot,
      mul_assoc, mul_left_comm, mul_comm]
  have hcancel :
      (G.grid.μ J.1).toReal ^ (-s) * (G.grid.μ J.1).toReal ^ s = 1 := by
    rw [← Real.rpow_add hμ_pos, neg_add_cancel, Real.rpow_zero]
  calc
    (G.grid.μ J.1).toReal ^ (-s) *
      (MeasureTheory.eLpNorm
        (((g -
          ∑ k ∈ Finset.range (k₀ + 1),
            (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
          Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ))
        p (G.grid.μ.restrict J.1)).toReal
        ≤
          (G.grid.μ J.1).toReal ^ (-s) *
            (∑' i,
              lpTailLocalGeometricCoeffBound G s p hs hp hp_top R k₀ J i) := by
          exact mul_le_mul_of_nonneg_left htail
            (Real.rpow_nonneg hμ_pos.le _)
    _ =
        (G.grid.μ J.1).toReal ^ (-s) *
          ((G.grid.μ J.1).toReal ^ s * ∑' i, K * kernel i * localRoot i) := by
          rw [hgeom_tsum_eq]
    _ = ∑' i, K * kernel i * localRoot i := by
          rw [← mul_assoc, hcancel, one_mul]

private theorem localSeries_lpsum_le_future_convolution
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (k₀ : ℕ) :
    let K := ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal))
    let kernel : ℕ → ℝ := fun i => (G.grid.lambda2 ^ (i + 1)) ^ s
    let globalRoot : ℕ → ℝ := fun i =>
      (R.levelCoeffPower (k₀ + (i + 1))) ^ (1 / p.toReal)
    let localSeries : WeakGridSpace.LevelCell G.toWeakGridSpace k₀ → ℝ := fun J =>
      ∑' i,
        K * kernel i *
          (let A := souzaAtomFamily G s p hs hp hp_top
           let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
           let B := R.block (k₀ + (i + 1))
           let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
           (∑ P : WeakGridSpace.LevelCell W (i + 1),
              ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal))
    (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
      (localSeries J) ^ p.toReal) ^ (1 / p.toReal)
      ≤ ∑' i, K * kernel i * globalRoot i := by
  classical
  intro K kernel globalRoot localSeries
  let Parent := WeakGridSpace.LevelCell G.toWeakGridSpace k₀
  let E : Parent → Type := fun _ => ℝ
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hkernel_sum : Summable kernel := by
    simpa [kernel] using geometric_tail_kernel_summable G s hs
  have hkernel_nonneg : ∀ i, 0 ≤ kernel i := by
    intro i
    dsimp [kernel]
    have hlambda2_nonneg : 0 ≤ G.grid.lambda2 :=
      le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
    exact Real.rpow_nonneg (pow_nonneg hlambda2_nonneg _) _
  have hglobalRoot_nonneg : ∀ i, 0 ≤ globalRoot i := by
    intro i
    dsimp [globalRoot]
    exact Real.rpow_nonneg (R.levelCoeffPower_nonneg _) _
  have hglobalRoot_le_cost :
      ∀ i, globalRoot i ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
    intro i
    simpa [globalRoot] using
      levelCoeffPower_root_le_pqCost
        (R := R) hp_top hRfin (k₀ + (i + 1))
  have hglobalWeighted_sum :
      Summable fun i => K * kernel i * globalRoot i := by
    have hbound :
        (fun i => K * kernel i * globalRoot i)
          ≤ fun i =>
              (K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) * kernel i := by
      intro i
      calc
        K * kernel i * globalRoot i = (K * kernel i) * globalRoot i := by ring
        _ ≤ (K * kernel i) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
            exact mul_le_mul_of_nonneg_left (hglobalRoot_le_cost i)
              (mul_nonneg hK_nonneg (hkernel_nonneg i))
        _ = (K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) * kernel i := by
            ring
    exact Summable.of_nonneg_of_le
      (fun i => mul_nonneg (mul_nonneg hK_nonneg (hkernel_nonneg i))
        (hglobalRoot_nonneg i))
      hbound
      (hkernel_sum.mul_left
        (K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R))
  let V : ℕ → lp E p := fun i =>
    ⟨fun J =>
      K * kernel i *
        (let A := souzaAtomFamily G s p hs hp hp_top
         let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
         let B := R.block (k₀ + (i + 1))
         let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
         (∑ P : WeakGridSpace.LevelCell W (i + 1),
            ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)),
      memℓp_gen (summable_of_hasFiniteSupport (by
        unfold Function.HasFiniteSupport
        exact (Set.toFinite (Set.univ : Set Parent)).subset (Set.subset_univ _)))⟩
  have hV_norm_le : ∀ i, ‖V i‖ ≤ K * kernel i * globalRoot i := by
    intro i
    have hC_nonneg : 0 ≤ K * kernel i * globalRoot i :=
      mul_nonneg (mul_nonneg hK_nonneg (hkernel_nonneg i)) (hglobalRoot_nonneg i)
    refine lp.norm_le_of_tsum_le hp_pos hC_nonneg ?_
    let localRoot : Parent → ℝ := fun J =>
      let A := souzaAtomFamily G s p hs hp hp_top
      let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
      let B := R.block (k₀ + (i + 1))
      let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
      (∑ P : WeakGridSpace.LevelCell W (i + 1),
        ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)
    have hlocalRoot_nonneg : ∀ J, 0 ≤ localRoot J := by
      intro J
      dsimp [localRoot]
      exact Real.rpow_nonneg
        (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _) _
    have hlpsum_le :
        (∑ J : Parent, localRoot J ^ p.toReal) ^ (1 / p.toReal)
          ≤ globalRoot i := by
      simpa [Parent, globalRoot, localRoot] using
        localDescendantRoot_lpsum_le_levelCoeffRoot
          (G := G) (s := s) (hs := hs) (p := p) (hp := hp) (hp_top := hp_top)
          (R := R) (k₀ := k₀) (i := i)
    have hsum_local_le :
        (∑ J : Parent, localRoot J ^ p.toReal) ≤ globalRoot i ^ p.toReal := by
      have hsum_nonneg : 0 ≤ ∑ J : Parent, localRoot J ^ p.toReal :=
        Finset.sum_nonneg fun J _ => Real.rpow_nonneg (hlocalRoot_nonneg J) _
      have hroot_nonneg :
          0 ≤ (∑ J : Parent, localRoot J ^ p.toReal) ^ (1 / p.toReal) :=
        Real.rpow_nonneg hsum_nonneg _
      have hpow := Real.rpow_le_rpow hroot_nonneg hlpsum_le hp_pos.le
      have hleft :
          ((∑ J : Parent, localRoot J ^ p.toReal) ^ (1 / p.toReal)) ^ p.toReal =
            ∑ J : Parent, localRoot J ^ p.toReal := by
        simpa [one_div] using Real.rpow_inv_rpow hsum_nonneg hp_pos.ne'
      have hleft_inv :
          ((∑ J : Parent, localRoot J ^ p.toReal) ^ p.toReal⁻¹) ^ p.toReal =
            ∑ J : Parent, localRoot J ^ p.toReal := by
        simpa [one_div] using hleft
      simpa [hleft_inv] using hpow
    have hsum_norm :
        (∑' J : Parent, ‖(V i : lp E p) J‖ ^ p.toReal)
          =
            (K * kernel i) ^ p.toReal *
              ∑ J : Parent, localRoot J ^ p.toReal := by
      rw [tsum_fintype]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro J _hJ
      have hfactor_nonneg : 0 ≤ K * kernel i :=
        mul_nonneg hK_nonneg (hkernel_nonneg i)
      have hterm_nonneg : 0 ≤ K * kernel i * localRoot J :=
        mul_nonneg hfactor_nonneg (hlocalRoot_nonneg J)
      change ‖K * kernel i * localRoot J‖ ^ p.toReal =
        (K * kernel i) ^ p.toReal * localRoot J ^ p.toReal
      rw [Real.norm_of_nonneg hterm_nonneg]
      rw [Real.mul_rpow hfactor_nonneg (hlocalRoot_nonneg J)]
    calc
      (∑' J : Parent, ‖(V i : lp E p) J‖ ^ p.toReal)
          = (K * kernel i) ^ p.toReal *
              ∑ J : Parent, localRoot J ^ p.toReal := hsum_norm
      _ ≤ (K * kernel i) ^ p.toReal * globalRoot i ^ p.toReal := by
          exact mul_le_mul_of_nonneg_left hsum_local_le
            (Real.rpow_nonneg (mul_nonneg hK_nonneg (hkernel_nonneg i)) _)
      _ = (K * kernel i * globalRoot i) ^ p.toReal := by
          rw [Real.mul_rpow (mul_nonneg hK_nonneg (hkernel_nonneg i))
            (hglobalRoot_nonneg i)]
  have hV_norm_sum : Summable fun i => ‖V i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hV_norm_le hglobalWeighted_sum
  have hV_sum : Summable V := hV_norm_sum.of_norm
  let W : lp E p := ∑' i, V i
  have hcoord : ∀ J : Parent, (W : (J : Parent) → E J) J = localSeries J := by
    intro J
    have hhas :
        HasSum (fun i => (V i : (J : Parent) → E J) J) ((W : (J : Parent) → E J) J) := by
      simpa [W] using
        (lp.evalCLM ℝ E p J).hasSum hV_sum.hasSum
    exact hhas.tsum_eq.symm
  have hlocalSeries_nonneg : ∀ J : Parent, 0 ≤ localSeries J := by
    intro J
    dsimp [localSeries]
    exact tsum_nonneg fun i => by
      dsimp [K, kernel]
      exact mul_nonneg (mul_nonneg hK_nonneg (hkernel_nonneg i))
        (Real.rpow_nonneg
          (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _) _)
  have hW_norm :
      ‖W‖ ≤ ∑' i, K * kernel i * globalRoot i := by
    calc
      ‖W‖ ≤ ∑' i, ‖V i‖ := by
        simpa [W] using norm_tsum_le_tsum_norm hV_norm_sum
      _ ≤ ∑' i, K * kernel i * globalRoot i :=
        hV_norm_sum.tsum_le_tsum hV_norm_le hglobalWeighted_sum
  calc
    (∑ J : Parent, (localSeries J) ^ p.toReal) ^ (1 / p.toReal)
        = ‖W‖ := by
          rw [lp.norm_eq_tsum_rpow hp_pos W]
          rw [tsum_fintype]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro J _hJ
          rw [hcoord J]
          simp [Real.norm_of_nonneg (hlocalSeries_nonneg J)]
    _ ≤ ∑' i, K * kernel i * globalRoot i := hW_norm

private theorem levelOscillationBlock_root_toReal_le_tailWeightedLpsum
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (f : α → ℂ) (k₀ : ℕ)
    (hfg : f =ᵐ[G.grid.μ] (g : α → ℂ)) :
    let tail : α → ℂ :=
      ((g -
        ∑ k ∈ Finset.range (k₀ + 1),
          (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
    let weightedTail : WeakGridSpace.LevelCell G.toWeakGridSpace k₀ → ℝ := fun J =>
      (G.grid.μ J.1).toReal ^ (-s) *
        (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)).toReal
    ((levelOscillationBlock G s p f k₀) ^ (1 / p.toReal)).toReal
      ≤
        (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          weightedTail J ^ p.toReal) ^ (1 / p.toReal) := by
  classical
  intro tail weightedTail
  let tailLp : Lp ℂ p G.toWeakGridSpace.measure :=
    g -
      ∑ k ∈ Finset.range (k₀ + 1),
        (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)
  have htail_def : tail = (tailLp : α → ℂ) := by
    rfl
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hp_inv_nonneg : 0 ≤ 1 / p.toReal :=
    one_div_nonneg.mpr hp_pos.le
  let tailBlock : ℝ≥0∞ :=
    ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
      (G.grid.μ J.1) ^ (-(s * p.toReal)) *
        (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal
  have hlevel :
      levelOscillationBlock G s p f k₀ ≤ tailBlock := by
    simpa [tailBlock, tail] using
      levelOscillationBlock_function_le_lpTail_of_ae_eq_souzaRepresentation
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
        (hp_top := hp_top) (R := R) (f := f) (k₀ := k₀) hfg
  letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have htail_mem :
      ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        MeasureTheory.MemLp tail p (G.grid.μ.restrict J.1) := by
    intro J
    rw [htail_def]
    exact (MeasureTheory.Lp.memLp tailLp).restrict J.1
  have hterm_ne_top :
      ∀ J ∈ (Finset.univ : Finset (WeakGridSpace.LevelCell G.toWeakGridSpace k₀)),
        (G.grid.μ J.1) ^ (-(s * p.toReal)) *
        (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal ≠ ∞ := by
    intro J _hJ
    have hμ_pos : 0 < G.grid.μ J.1 :=
      G.grid.positive_measure k₀ J.1 J.2
    have hμ_ne_top : G.grid.μ J.1 ≠ ∞ :=
      MeasureTheory.measure_ne_top G.grid.μ J.1
    have hμpow_ne_top :
        (G.grid.μ J.1) ^ (-(s * p.toReal)) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_ne_zero hμ_pos.ne' hμ_ne_top
    have htail_ne_top :
        MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1) ≠ ∞ :=
      (htail_mem J).eLpNorm_ne_top
    have htail_pow_ne_top :
        (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg htail_ne_top
    exact ENNReal.mul_ne_top hμpow_ne_top htail_pow_ne_top
  have htailBlock_ne_top : tailBlock ≠ ∞ := by
    simpa [tailBlock] using
      (ENNReal.sum_ne_top.mpr (by
        intro J hJ
        exact hterm_ne_top ⟨J, hJ⟩ (Finset.mem_univ _)))
  have htailBlock_root_ne_top : tailBlock ^ (1 / p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp_inv_nonneg htailBlock_ne_top
  have hroot_toReal_le :
      ((levelOscillationBlock G s p f k₀) ^ (1 / p.toReal)).toReal
        ≤ (tailBlock ^ (1 / p.toReal)).toReal :=
    ENNReal.toReal_mono htailBlock_root_ne_top
      (ENNReal.rpow_le_rpow hlevel hp_inv_nonneg)
  have htailBlock_toReal :
      tailBlock.toReal =
        ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          weightedTail J ^ p.toReal := by
    rw [show tailBlock =
      ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        (G.grid.μ J.1) ^ (-(s * p.toReal)) *
          (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal by rfl]
    rw [ENNReal.toReal_sum hterm_ne_top]
    refine Finset.sum_congr rfl ?_
    intro J _hJ
    have hμ_pos_enn : 0 < G.grid.μ J.1 :=
      G.grid.positive_measure k₀ J.1 J.2
    have hμ_ne_top : G.grid.μ J.1 ≠ ∞ :=
      MeasureTheory.measure_ne_top G.grid.μ J.1
    have hμ_toReal_pos : 0 < (G.grid.μ J.1).toReal :=
      ENNReal.toReal_pos hμ_pos_enn.ne' hμ_ne_top
    have htail_toReal_nonneg :
        0 ≤ (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)).toReal :=
      ENNReal.toReal_nonneg
    have hμneg_mul :
        (G.grid.μ J.1).toReal ^ (-(s * p.toReal))
          =
            ((G.grid.μ J.1).toReal ^ (-s)) ^ p.toReal := by
      calc
        (G.grid.μ J.1).toReal ^ (-(s * p.toReal))
            = (G.grid.μ J.1).toReal ^ ((-s) * p.toReal) := by ring_nf
        _ = ((G.grid.μ J.1).toReal ^ (-s)) ^ p.toReal :=
            Real.rpow_mul hμ_toReal_pos.le (-s) p.toReal
    have hweighted_pow :
        weightedTail J ^ p.toReal =
          (G.grid.μ J.1).toReal ^ (-(s * p.toReal)) *
            (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)).toReal ^
              p.toReal := by
      dsimp [weightedTail]
      rw [Real.mul_rpow (Real.rpow_nonneg hμ_toReal_pos.le _) htail_toReal_nonneg]
      rw [hμneg_mul]
    calc
      ((G.grid.μ J.1) ^ (-(s * p.toReal)) *
          (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal).toReal
          =
            ((G.grid.μ J.1) ^ (-(s * p.toReal))).toReal *
              ((MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal).toReal := by
            rw [ENNReal.toReal_mul]
      _ =
          (G.grid.μ J.1).toReal ^ (-(s * p.toReal)) *
            (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)).toReal ^
              p.toReal := by
            rw [← ENNReal.toReal_rpow]
            rw [← ENNReal.toReal_rpow]
      _ = weightedTail J ^ p.toReal := hweighted_pow.symm
  have htailBlock_root_toReal :
      (tailBlock ^ (1 / p.toReal)).toReal =
        (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          weightedTail J ^ p.toReal) ^ (1 / p.toReal) := by
    rw [← ENNReal.toReal_rpow]
    rw [htailBlock_toReal]
  exact hroot_toReal_le.trans_eq htailBlock_root_toReal

private theorem levelOscillationBlock_root_toReal_le_future_convolution
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (f : α → ℂ) (k₀ : ℕ)
    (hfg : f =ᵐ[G.grid.μ] (g : α → ℂ)) :
    let K := ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal))
    let kernel : ℕ → ℝ := fun i => (G.grid.lambda2 ^ (i + 1)) ^ s
    let globalRoot : ℕ → ℝ := fun i =>
      (R.levelCoeffPower (k₀ + (i + 1))) ^ (1 / p.toReal)
    ((levelOscillationBlock G s p f k₀) ^ (1 / p.toReal)).toReal
      ≤ ∑' i, K * kernel i * globalRoot i := by
  classical
  intro K kernel globalRoot
  let tail : α → ℂ :=
    ((g -
      ∑ k ∈ Finset.range (k₀ + 1),
        (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
      Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
  let weightedTail : WeakGridSpace.LevelCell G.toWeakGridSpace k₀ → ℝ := fun J =>
    (G.grid.μ J.1).toReal ^ (-s) *
      (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)).toReal
  let localSeries : WeakGridSpace.LevelCell G.toWeakGridSpace k₀ → ℝ := fun J =>
    ∑' i,
      K * kernel i *
        (let A := souzaAtomFamily G s p hs hp hp_top
         let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
         let B := R.block (k₀ + (i + 1))
         let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
         (∑ P : WeakGridSpace.LevelCell W (i + 1),
            ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal))
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hp_inv_nonneg : 0 ≤ 1 / p.toReal :=
    one_div_nonneg.mpr hp_pos.le
  have htail :
      ((levelOscillationBlock G s p f k₀) ^ (1 / p.toReal)).toReal
        ≤
          (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
            weightedTail J ^ p.toReal) ^ (1 / p.toReal) := by
    simpa [tail, weightedTail] using
      levelOscillationBlock_root_toReal_le_tailWeightedLpsum
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
        (hp_top := hp_top) (R := R) (f := f) (k₀ := k₀) hfg
  have hweighted_nonneg :
      ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        0 ≤ weightedTail J := by
    intro J
    dsimp [weightedTail]
    exact mul_nonneg
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      ENNReal.toReal_nonneg
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hkernel_nonneg : ∀ i, 0 ≤ kernel i := by
    intro i
    dsimp [kernel]
    have hlambda2_nonneg : 0 ≤ G.grid.lambda2 :=
      le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
    exact Real.rpow_nonneg (pow_nonneg hlambda2_nonneg _) _
  have hlocalRoot_nonneg :
      ∀ (J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀) i,
        0 ≤
          (let A := souzaAtomFamily G s p hs hp hp_top
           let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace J
           let B := R.block (k₀ + (i + 1))
           let BI := WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace J A B
           (∑ P : WeakGridSpace.LevelCell W (i + 1),
              ‖BI.coeff P‖ ^ p.toReal) ^ (1 / p.toReal)) := by
    intro J i
    exact Real.rpow_nonneg
      (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have hlocalSeries_nonneg :
      ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        0 ≤ localSeries J := by
    intro J
    dsimp [localSeries]
    exact tsum_nonneg fun i =>
      mul_nonneg (mul_nonneg hK_nonneg (hkernel_nonneg i))
        (hlocalRoot_nonneg J i)
  have hweighted_le_local :
      ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        weightedTail J ≤ localSeries J := by
    intro J
    simpa [tail, weightedTail, localSeries, K, kernel] using
      weighted_lpTail_restrict_toReal_le_localSeries
        (G := G) (s := s) (hs := hs) (p := p) (q := q)
        (hp := hp) (hp_top := hp_top) (R := R) hRfin
        (J := J) (k₀ := k₀)
  have hlpsum_le :
      (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        weightedTail J ^ p.toReal) ^ (1 / p.toReal)
        ≤
          (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
            localSeries J ^ p.toReal) ^ (1 / p.toReal) := by
    have hsum_nonneg :
        0 ≤ ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          weightedTail J ^ p.toReal :=
      Finset.sum_nonneg fun J _ =>
        Real.rpow_nonneg (hweighted_nonneg J) _
    have hsum_le :
        (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          weightedTail J ^ p.toReal)
          ≤
            ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
              localSeries J ^ p.toReal :=
      Finset.sum_le_sum fun J _ =>
        Real.rpow_le_rpow (hweighted_nonneg J) (hweighted_le_local J) hp_pos.le
    exact Real.rpow_le_rpow hsum_nonneg hsum_le hp_inv_nonneg
  have hlocal :
      (∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        localSeries J ^ p.toReal) ^ (1 / p.toReal)
        ≤ ∑' i, K * kernel i * globalRoot i := by
    simpa [localSeries, K, kernel, globalRoot] using
      localSeries_lpsum_le_future_convolution
        (G := G) (s := s) (hs := hs) (p := p) (q := q)
        (hp := hp) (hp_top := hp_top) (R := R) hRfin k₀
  exact htail.trans (hlpsum_le.trans hlocal)

private theorem levelOscillationBlock_root_ne_top_of_ae_eq_souzaRepresentation
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (f : α → ℂ) (k₀ : ℕ)
    (hfg : f =ᵐ[G.grid.μ] (g : α → ℂ)) :
    (levelOscillationBlock G s p f k₀) ^ (1 / p.toReal) ≠ ∞ := by
  classical
  let tail : α → ℂ :=
    ((g -
      ∑ k ∈ Finset.range (k₀ + 1),
        (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) :
      Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
  let tailBlock : ℝ≥0∞ :=
    ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
      (G.grid.μ J.1) ^ (-(s * p.toReal)) *
        (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hp_inv_nonneg : 0 ≤ 1 / p.toReal :=
    one_div_nonneg.mpr hp_pos.le
  have hlevel :
      levelOscillationBlock G s p f k₀ ≤ tailBlock := by
    simpa [tailBlock, tail] using
      levelOscillationBlock_function_le_lpTail_of_ae_eq_souzaRepresentation
        (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
        (hp_top := hp_top) (R := R) (f := f) (k₀ := k₀) hfg
  letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have htail_mem :
      ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
        MeasureTheory.MemLp tail p (G.grid.μ.restrict J.1) := by
    intro J
    dsimp [tail]
    exact (MeasureTheory.Lp.memLp
      (g -
        ∑ k ∈ Finset.range (k₀ + 1),
          (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top))).restrict J.1
  have hterm_ne_top :
      ∀ J ∈ (Finset.univ : Finset (WeakGridSpace.LevelCell G.toWeakGridSpace k₀)),
        (G.grid.μ J.1) ^ (-(s * p.toReal)) *
          (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal ≠ ∞ := by
    intro J _hJ
    have hμ_pos : 0 < G.grid.μ J.1 :=
      G.grid.positive_measure k₀ J.1 J.2
    have hμ_ne_top : G.grid.μ J.1 ≠ ∞ :=
      MeasureTheory.measure_ne_top G.grid.μ J.1
    have hμpow_ne_top :
        (G.grid.μ J.1) ^ (-(s * p.toReal)) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_ne_zero hμ_pos.ne' hμ_ne_top
    have htail_ne_top :
        MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1) ≠ ∞ :=
      (htail_mem J).eLpNorm_ne_top
    have htail_pow_ne_top :
        (MeasureTheory.eLpNorm tail p (G.grid.μ.restrict J.1)) ^ p.toReal ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg htail_ne_top
    exact ENNReal.mul_ne_top hμpow_ne_top htail_pow_ne_top
  have htailBlock_ne_top : tailBlock ≠ ∞ := by
    simpa [tailBlock] using
      (ENNReal.sum_ne_top.mpr (by
        intro J hJ
        exact hterm_ne_top ⟨J, hJ⟩ (Finset.mem_univ _)))
  have htailBlock_root_ne_top : tailBlock ^ (1 / p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp_inv_nonneg htailBlock_ne_top
  exact ne_top_of_le_ne_top htailBlock_root_ne_top
    (ENNReal.rpow_le_rpow hlevel hp_inv_nonneg)

private theorem levelOscillationBlock_root_le_ofReal_future_convolution
    (G : GoodGridSpace (α := α))
    (s : ℝ) (hs : 0 < s)
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (f : α → ℂ) (k₀ : ℕ)
    (hfg : f =ᵐ[G.grid.μ] (g : α → ℂ)) :
    let K := ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal))
    let kernel : ℕ → ℝ := fun i => (G.grid.lambda2 ^ (i + 1)) ^ s
    let globalRoot : ℕ → ℝ := fun i =>
      (R.levelCoeffPower (k₀ + (i + 1))) ^ (1 / p.toReal)
    (levelOscillationBlock G s p f k₀) ^ (1 / p.toReal)
      ≤ ENNReal.ofReal (∑' i, K * kernel i * globalRoot i) := by
  classical
  intro K kernel globalRoot
  have hne :
      (levelOscillationBlock G s p f k₀) ^ (1 / p.toReal) ≠ ∞ :=
    levelOscillationBlock_root_ne_top_of_ae_eq_souzaRepresentation
      (G := G) (s := s) (hs := hs) (p := p) (hp := hp)
      (hp_top := hp_top) (R := R) (f := f) (k₀ := k₀) hfg
  have hreal :
      ((levelOscillationBlock G s p f k₀) ^ (1 / p.toReal)).toReal
        ≤ ∑' i, K * kernel i * globalRoot i := by
    simpa [K, kernel, globalRoot] using
      levelOscillationBlock_root_toReal_le_future_convolution
        (G := G) (s := s) (hs := hs) (p := p) (q := q)
        (hp := hp) (hp_top := hp_top) (R := R) hRfin
        (f := f) (k₀ := k₀) hfg
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hkernel_nonneg : ∀ i, 0 ≤ kernel i := by
    intro i
    dsimp [kernel]
    have hlambda2_nonneg : 0 ≤ G.grid.lambda2 :=
      le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
    exact Real.rpow_nonneg (pow_nonneg hlambda2_nonneg _) _
  have hglobalRoot_nonneg : ∀ i, 0 ≤ globalRoot i := by
    intro i
    dsimp [globalRoot]
    exact Real.rpow_nonneg (R.levelCoeffPower_nonneg _) _
  have htarget_nonneg : 0 ≤ ∑' i, K * kernel i * globalRoot i :=
    tsum_nonneg fun i =>
      mul_nonneg (mul_nonneg hK_nonneg (hkernel_nonneg i))
        (hglobalRoot_nonneg i)
  exact (ENNReal.le_ofReal_iff_toReal_le hne htarget_nonneg).2 hreal

/--
The oscillation seminorm is bounded by the standard atomic coefficient gauge.

This is the discrete convolution estimate from the preprint.  Given an
almost-minimizing representation, the part of the atomic series above a cell
level `k₀` bounds the local oscillation on that cell.  Summing over cells and
then over levels gives convolution with the geometric kernel
`λ₂^{s n}`, whose sum is bounded by `(1 - λ₂^s)⁻¹`.
-/
theorem exists_oscillationSeminorm_le_const_mul_standardRepresentationNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ),
        StandardAtomicRepresentation.standardRepresentationNorm
            G F s hs p hp_top q f hf ≠ ∞ →
          oscillationSeminorm G s p q f ≤
            C *
              StandardAtomicRepresentation.standardRepresentationNorm
                G F s hs p hp_top q f hf := by
  classical
  let K : ℝ := ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal))
  let kernel : ℕ → ℝ := fun i => (G.grid.lambda2 ^ (i + 1)) ^ s
  let b : ℕ → ℝ := fun i => K * kernel i
  let CReal : ℝ := ∑' i, b i
  refine ⟨ENNReal.ofReal CReal, ENNReal.ofReal_ne_top, ?_⟩
  intro f hf hN
  let N : ℝ≥0∞ :=
    StandardAtomicRepresentation.standardRepresentationNorm
      G F s hs p hp_top q f hf
  change oscillationSeminorm G s p q f ≤ ENNReal.ofReal CReal * N
  have hN_ne_top : N ≠ ∞ := by
    simpa [N] using hN
  rcases exists_souzaBesovSpace_representation_of_standardRepresentationNorm_ne_top
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top)
      (q := q) f hf hN with
    ⟨hfLp, g, R, hRfin, hg_eq, hRcost⟩
  have hRcostN :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤ N.toReal := by
    simpa [N] using hRcost
  have hg_ae :
      ((g : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =ᵐ[G.grid.μ] f := by
    rw [hg_eq]
    exact MemLp.coeFn_toLp hfLp
  have hfg :
      f =ᵐ[G.grid.μ] ((g : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) :=
    hg_ae.symm
  let a : ℕ → ℝ := fun k => (R.levelCoeffPower k) ^ (1 / p.toReal)
  let conv : ℕ → ℝ := fun k => ∑' i, b i * a (k + (i + 1))
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hkernel_nonneg : ∀ i, 0 ≤ kernel i := by
    intro i
    dsimp [kernel]
    have hlambda2_nonneg : 0 ≤ G.grid.lambda2 :=
      le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
    exact Real.rpow_nonneg (pow_nonneg hlambda2_nonneg _) _
  have hb_nonneg : ∀ i, 0 ≤ b i := by
    intro i
    exact mul_nonneg hK_nonneg (hkernel_nonneg i)
  have hkernel_sum : Summable kernel := by
    simpa [kernel] using geometric_tail_kernel_summable G s hs
  have hb_sum : Summable b := by
    simpa [b] using hkernel_sum.mul_left K
  have hCReal_nonneg : 0 ≤ CReal := by
    dsimp [CReal]
    exact tsum_nonneg hb_nonneg
  have hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_ne_top
  have ha_nonneg : ∀ k, 0 ≤ a k := by
    intro k
    dsimp [a]
    exact Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
  have hconv_nonneg : ∀ k, 0 ≤ conv k := by
    intro k
    dsimp [conv]
    exact tsum_nonneg fun i => mul_nonneg (hb_nonneg i) (ha_nonneg _)
  have ha_fin :
      if q = ∞ then
        BddAbove (Set.range a)
      else
        Summable fun k => a k ^ q.toReal := by
    by_cases hqtop : q = ∞
    · simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop, a] using hRfin
    · have hpow :
          ∀ k, a k ^ q.toReal =
            R.levelCoeffPower k ^ (q.toReal / p.toReal) := by
        intro k
        have hlevel_nonneg : 0 ≤ R.levelCoeffPower k :=
          R.levelCoeffPower_nonneg k
        have hdiv : (1 / p.toReal) * q.toReal = q.toReal / p.toReal := by
          ring
        calc
          a k ^ q.toReal
              = ((R.levelCoeffPower k) ^ (1 / p.toReal)) ^ q.toReal := rfl
          _ = R.levelCoeffPower k ^ ((1 / p.toReal) * q.toReal) := by
              rw [← Real.rpow_mul hlevel_nonneg]
          _ = R.levelCoeffPower k ^ (q.toReal / p.toReal) := by
              rw [hdiv]
      have hsum_raw :
          Summable fun k => R.levelCoeffPower k ^ (q.toReal / p.toReal) := by
        simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hRfin
      simpa [hqtop] using hsum_raw.congr (fun k => (hpow k).symm)
  have haGauge_eq :
      realSequenceLqGauge q a =
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
    simpa [a] using
      levelCoeffRoot_realSequenceLqGauge_eq_pqCost
        (R := R) (hp_top := hp_ne_top) (q := q)
  have hconvGauge_le_cost :
      realSequenceLqGauge q conv ≤
        CReal * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
    have hconv :=
      future_convolution_lqGauge_le
        (q := q) (a := a) (b := b)
        ha_nonneg hb_nonneg hb_sum ha_fin
    calc
      realSequenceLqGauge q conv
          ≤ (∑' i, b i) * realSequenceLqGauge q a := by
            simpa [conv] using hconv
      _ = CReal * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
            rw [haGauge_eq]
  have hconvGauge_le_N :
      realSequenceLqGauge q conv ≤ CReal * N.toReal :=
    hconvGauge_le_cost.trans
      (mul_le_mul_of_nonneg_left hRcostN hCReal_nonneg)
  have htarget_eq :
      ENNReal.ofReal (CReal * N.toReal) = ENNReal.ofReal CReal * N := by
    rw [← ENNReal.ofReal_toReal hN_ne_top]
    rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    rw [← ENNReal.ofReal_mul hCReal_nonneg]
  have hroot_le_conv :
      ∀ k,
        (levelOscillationBlock G s p f k) ^ (1 / p.toReal)
          ≤ ENNReal.ofReal (conv k) := by
    intro k
    simpa [conv, b, a, K, kernel] using
      levelOscillationBlock_root_le_ofReal_future_convolution
        (G := G) (s := s) (hs := hs) (p := p) (q := q)
        (hp := Fact.out) (hp_top := hp_ne_top) (R := R) hRfin
        (f := f) (k₀ := k) hfg
  by_cases hqtop : q = ∞
  · have ha_le_cost :
        ∀ k, a k ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
      intro k
      simpa [a] using
        levelCoeffPower_root_le_pqCost
          (R := R) (hp_top := hp_ne_top) hRfin k
    have hcost_nonneg :
        0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
      WeakGridSpace.LpGridRepresentation.pqCost_nonneg R
    have hconv_le_N :
        ∀ k, conv k ≤ CReal * N.toReal := by
      intro k
      have hterm_le :
          (fun i => b i * a (k + (i + 1)))
            ≤ fun i => b i * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
        intro i
        exact mul_le_mul_of_nonneg_left (ha_le_cost _) (hb_nonneg i)
      have hterm_sum :
          Summable fun i => b i * a (k + (i + 1)) :=
        Summable.of_nonneg_of_le
          (fun i => mul_nonneg (hb_nonneg i) (ha_nonneg _))
          hterm_le
          (hb_sum.mul_right
            (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R))
      calc
        conv k
            ≤ ∑' i, b i * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
          hterm_sum.tsum_le_tsum hterm_le
            (hb_sum.mul_right
              (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R))
        _ = CReal * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
          simpa [CReal] using
            (hb_sum.hasSum.mul_right
              (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R)).tsum_eq
        _ ≤ CReal * N.toReal :=
          mul_le_mul_of_nonneg_left hRcostN hCReal_nonneg
    have hroot_le_target :
        ∀ k,
          (levelOscillationBlock G s p f k) ^ (1 / p.toReal)
            ≤ ENNReal.ofReal (CReal * N.toReal) := by
      intro k
      exact (hroot_le_conv k).trans
        (ENNReal.ofReal_le_ofReal (hconv_le_N k))
    have hosc_le_target :
        oscillationSeminorm G s p q f ≤ ENNReal.ofReal (CReal * N.toReal) := by
      rw [oscillationSeminorm, if_pos hqtop]
      refine sSup_le ?_
      rintro _ ⟨k, rfl⟩
      exact hroot_le_target k
    simpa [htarget_eq] using hosc_le_target
  · have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hqtop
    have hq_inv_nonneg : 0 ≤ 1 / q.toReal :=
      one_div_nonneg.mpr hq_pos.le
    have ha_q : Summable fun k => a k ^ q.toReal := by
      simpa [hqtop] using ha_fin
    have hconv_q_summable :
        Summable fun k => conv k ^ q.toReal := by
      simpa [conv] using
        future_convolution_summable_rpow
          (q := q) (a := a) (b := b) hqtop
          ha_nonneg hb_nonneg hb_sum ha_q
    have hlevel_pow_le :
        ∀ k,
          (levelOscillationBlock G s p f k) ^ (q.toReal / p.toReal)
            ≤ ENNReal.ofReal (conv k ^ q.toReal) := by
      intro k
      have hdiv : (1 / p.toReal) * q.toReal = q.toReal / p.toReal := by
        ring
      calc
        (levelOscillationBlock G s p f k) ^ (q.toReal / p.toReal)
            =
              ((levelOscillationBlock G s p f k) ^ (1 / p.toReal)) ^
                q.toReal := by
              rw [← ENNReal.rpow_mul, hdiv]
        _ ≤ (ENNReal.ofReal (conv k)) ^ q.toReal :=
              ENNReal.rpow_le_rpow (hroot_le_conv k) ENNReal.toReal_nonneg
        _ = ENNReal.ofReal (conv k ^ q.toReal) := by
              rw [← ENNReal.ofReal_rpow_of_nonneg (hconv_nonneg k)
                ENNReal.toReal_nonneg]
    have hosc_le_convGauge :
        oscillationSeminorm G s p q f ≤
          ENNReal.ofReal (realSequenceLqGauge q conv) := by
      rw [oscillationSeminorm, if_neg hqtop]
      have hsum_le :
          (∑' k, (levelOscillationBlock G s p f k) ^ (q.toReal / p.toReal))
            ≤ ∑' k, ENNReal.ofReal (conv k ^ q.toReal) :=
        ENNReal.tsum_le_tsum hlevel_pow_le
      have hconv_q_nonneg : ∀ k, 0 ≤ conv k ^ q.toReal := by
        intro k
        exact Real.rpow_nonneg (hconv_nonneg k) _
      have hconv_sum_nonneg : 0 ≤ ∑' k, conv k ^ q.toReal :=
        tsum_nonneg hconv_q_nonneg
      calc
        (∑' k, (levelOscillationBlock G s p f k) ^ (q.toReal / p.toReal)) ^
            (1 / q.toReal)
            ≤ (∑' k, ENNReal.ofReal (conv k ^ q.toReal)) ^
                (1 / q.toReal) :=
              ENNReal.rpow_le_rpow hsum_le hq_inv_nonneg
        _ =
            (ENNReal.ofReal (∑' k, conv k ^ q.toReal)) ^
              (1 / q.toReal) := by
              rw [ENNReal.ofReal_tsum_of_nonneg hconv_q_nonneg hconv_q_summable]
        _ = ENNReal.ofReal
              ((∑' k, conv k ^ q.toReal) ^ (1 / q.toReal)) := by
              rw [← ENNReal.ofReal_rpow_of_nonneg hconv_sum_nonneg
                hq_inv_nonneg]
        _ = ENNReal.ofReal (realSequenceLqGauge q conv) := by
              simp [realSequenceLqGauge, hqtop]
    have hosc_le_target :
        oscillationSeminorm G s p q f ≤ ENNReal.ofReal (CReal * N.toReal) :=
      hosc_le_convGauge.trans (ENNReal.ofReal_le_ofReal hconvGauge_le_N)
    simpa [htarget_eq] using hosc_le_target

/--
Finite standard representation norm forces membership in `L^p` and controls
the full mean-oscillation norm.

This is the packaged comparison
`N_osc(f) ≤ C N_st(f)`.  The proof is just bookkeeping once the two analytic
pieces above are available: the full mean-oscillation norm is the sum of the
`L^p` term and the oscillation seminorm.
-/
theorem exists_meanOscillationNorm_le_const_mul_standardRepresentationNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : Integrable f G.grid.μ),
        StandardAtomicRepresentation.standardRepresentationNorm
            G F s hs p hp_top q f hf ≠ ∞ →
          ∃ _hfLp : MemLp f p G.grid.μ,
            meanOscillationNorm G s p q f ≤
              C *
                StandardAtomicRepresentation.standardRepresentationNorm
                  G F s hs p hp_top q f hf := by
  classical
  rcases exists_lpnorm_term_le_const_mul_standardRepresentationNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q) with
    ⟨CLp, hCLp_fin, hLp_le⟩
  rcases exists_oscillationSeminorm_le_const_mul_standardRepresentationNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q) with
    ⟨Cosc, hCosc_fin, hosc_le⟩
  refine ⟨CLp + Cosc, ENNReal.add_ne_top.mpr ⟨hCLp_fin, hCosc_fin⟩, ?_⟩
  intro f hf hN
  rcases StandardAtomicRepresentation.finite_standardRepresentationNorm_implies_memLp_and_hasSum
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_top) (q := q)
      f hf hN with
    ⟨hfLp, _hstandard_sum⟩
  refine ⟨hfLp, ?_⟩
  calc
    meanOscillationNorm G s p q f
        =
          (G.grid.μ Set.univ) ^ (-s) * eLpNorm f p G.grid.μ +
            oscillationSeminorm G s p q f := rfl
    _ ≤
          CLp *
              StandardAtomicRepresentation.standardRepresentationNorm
                G F s hs p hp_top q f hf +
            Cosc *
              StandardAtomicRepresentation.standardRepresentationNorm
                G F s hs p hp_top q f hf :=
        add_le_add (hLp_le f hf hN) (hosc_le f hf hN)
    _ =
          (CLp + Cosc) *
            StandardAtomicRepresentation.standardRepresentationNorm
              G F s hs p hp_top q f hf := by
        rw [add_mul]

end MeanOscillation

end

end GoodGridSpace
