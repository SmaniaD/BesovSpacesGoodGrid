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
The level-`k` contribution to the mean-oscillation gauge.

It is `∑_{Q ∈ P^k} μ(Q)^(-s p) osc_p(f,Q)^p`.
-/
def levelOscillationBlock (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (k : ℕ) : ℝ≥0∞ :=
  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    (G.grid.μ Q.1) ^ (-(s * p.toReal)) *
      (osc G p f ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G)) ^ p.toReal

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
