import BesovSpacesGoodGrid.WeakGrid.Atoms
import BesovSpacesGoodGrid.WeakGrid.BesovishSpaces
import BesovSpacesGoodGrid.WeakGrid.Completeness
import BesovSpacesGoodGrid.GoodGrid.Definition
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.Complex.Basic

/-!
# Souza's atoms on a GoodGrid

This file defines:
1. `GoodGridCell`: cells of a `GoodGridSpace`
2. `GoodGridSpace.toWeakGrid`: the `WeakGrid` naturally induced by a `GoodGrid`
   (overlap constant = 1, since partitions are disjoint)
3. `IsSouzaAtom`: the predicate for `(s,p)`-Souza atoms
4. `canonicalSouzaAtom`: the canonical Souza atom on a cell
5. `souzaLocalVectorSpace`: the local vector space `ℂ` for Souza atoms
6. `souzaAtomFamily`: packages Souza atoms as an `AtomFamily`
7. `SouzaBesovSpace`: the Besov space induced by a `GoodGrid` and Souza atoms
-/

namespace GoodGridSpace

open scoped ENNReal MeasureTheory

variable {α : Type*} [MeasurableSpace α]

noncomputable section

-- ============================================================
-- §1. Grid cells and induced WeakGrid
-- ============================================================

/-- A cell in a `GoodGridSpace`: bundles its level, set, and membership proof. -/
structure GoodGridCell (G : GoodGridSpace (α := α)) where
  level : ℕ
  cell  : Set α
  mem   : cell ∈ G.grid.grid.partitions level

/-- Every `GoodGridCell` has strictly positive measure. -/
theorem GoodGridCell.measure_pos {G : GoodGridSpace (α := α)} (Q : GoodGridCell G) :
    0 < G.grid.μ Q.cell :=
  G.grid.positive_measure Q.level Q.cell Q.mem

/-- Every `GoodGridCell` has finite measure. -/
theorem GoodGridCell.measure_ne_top {G : GoodGridSpace (α := α)} (Q : GoodGridCell G) :
    G.grid.μ Q.cell ≠ ∞ :=
  by
    letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ Q.cell

/--
The overlap neighbourhood `Ω_Q^k` of `Q` in a disjoint partition is just `{Q}`.

At a given level the cells are pairwise disjoint, so no other cell can
intersect `Q`.
-/
private theorem overlapFinset_eq_singleton (G : GoodGridSpace (α := α))
    (k : ℕ) (Q : Set α) (hQ : Q ∈ G.grid.grid.partitions k) :
    WeakGridSpace.overlapFinset (G.grid.grid.partitions k) Q = {Q} := by
  ext R
  simp only [WeakGridSpace.overlapFinset, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro ⟨hR, hne⟩
    by_contra hRQ
    have hdisj := G.grid.grid.disjoint k R Q hR hQ hRQ
    obtain ⟨x, hxR, hxQ⟩ := hne
    exact absurd hxQ (Set.disjoint_left.mp hdisj hxR)
  · intro hRQ
    subst R
    exact ⟨hQ, by simpa using (G.grid.partition_nonempty k Q hQ)⟩

set_option linter.dupNamespace false in
/--
The `WeakGrid` induced by a `GoodGridSpace`.

Because the partitions are pairwise disjoint at each level, the same-level
overlap multiplicity is exactly 1, so `Cmult1 = 1`.
-/
def GoodGridSpace.toWeakGrid (G : GoodGridSpace (α := α)) :
    WeakGridSpace.WeakGrid (α := α) where
  μ                := G.grid.μ
  isFinite         := G.grid.isFinite
  partitions       := G.grid.grid.partitions
  measurable       := G.grid.grid.measurable
  positive_measure := G.grid.positive_measure
  exists_nonempty  := ⟨0, Set.univ, by
    rw [G.grid.grid.first_partition_eq_univ]; exact Finset.mem_singleton_self _⟩
  Cmult1           := 1
  overlap_card_le  := fun k Q hQ => by
    rw [overlapFinset_eq_singleton G k Q hQ]; simp

set_option linter.dupNamespace false in
/-- The `WeakGridSpace` induced by a `GoodGridSpace`. -/
def GoodGridSpace.toWeakGridSpace (G : GoodGridSpace (α := α)) :
    WeakGridSpace.WeakGridSpace (α := α) :=
  { grid := G.toWeakGrid }

/-- Every `GoodGridCell` gives a `WeakGridCell` in the induced `WeakGridSpace`. -/
def GoodGridCell.toWeakGridCell {G : GoodGridSpace (α := α)} (Q : GoodGridCell G) :
    WeakGridSpace.WeakGridCell G.toWeakGridSpace :=
  { level := Q.level, cell := Q.cell, mem := by exact Q.mem }

-- ============================================================
-- §2. Quantitative mesh estimate
-- ============================================================

/--
Every level-`n` good-grid cell has measure at most
`λ₂^n * μ(univ)`.

This is the formal induction behind the heuristic estimate
`|Q| ≤ λ₂^n |I|`: at each step a child has measure at most `λ₂` times
the measure of its parent.
-/
theorem cell_measure_le_lambda2_pow_mul_univ
    (G : GoodGridSpace (α := α)) :
    ∀ (n : ℕ) (Q : Set α), Q ∈ G.grid.grid.partitions n →
      G.grid.μ Q ≤ (ENNReal.ofReal G.grid.lambda2) ^ n * G.grid.μ Set.univ
  | 0, Q, hQ => by
      have hQ_univ : Q = Set.univ := by
        have hmem : Q ∈ ({Set.univ} : Finset (Set α)) := by
          simpa [G.grid.grid.first_partition_eq_univ] using hQ
        simpa using hmem
      subst hQ_univ
      simp
  | n + 1, Q, hQ => by
      obtain ⟨P, hP, hQP⟩ := G.grid.grid.nested n Q hQ
      have hstep :
          G.grid.μ Q ≤ ENNReal.ofReal G.grid.lambda2 * G.grid.μ P :=
        G.grid.ratio_upper n Q P hQ hP hQP
      have hind :
          G.grid.μ P ≤ (ENNReal.ofReal G.grid.lambda2) ^ n * G.grid.μ Set.univ :=
        cell_measure_le_lambda2_pow_mul_univ G n P hP
      calc
        G.grid.μ Q ≤ ENNReal.ofReal G.grid.lambda2 * G.grid.μ P := hstep
        _ ≤ ENNReal.ofReal G.grid.lambda2 *
              ((ENNReal.ofReal G.grid.lambda2) ^ n * G.grid.μ Set.univ) := by
            gcongr
        _ = (ENNReal.ofReal G.grid.lambda2) ^ (n + 1) * G.grid.μ Set.univ := by
            simp [pow_succ, mul_assoc, mul_comm]

-- ============================================================
-- §3. Souza's atoms: definition and canonical atom
-- ============================================================

/--
`a` is a `(s,p)`-Souza atom on cell `Q` if:
- `a` vanishes outside `Q`,
- `a` is constant on `Q`, and
- the constant `c` satisfies `‖c‖ ≤ μ(Q)^(s − 1/p)`.
-/
def IsSouzaAtom (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G) (a : α → ℂ) : Prop :=
  (∀ x ∉ Q.cell, a x = 0) ∧
  ∃ c : ℂ, (∀ x ∈ Q.cell, a x = c) ∧
            ‖c‖ ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)

/--
The canonical `(s,p)`-Souza atom on `Q`: takes the value `μ(Q)^(s−1/p)` on
`Q` and is zero outside.
-/
def canonicalSouzaAtom (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G) : α → ℂ := by
  classical
  exact fun x => if _ : x ∈ Q.cell then
    ((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) : ℝ) else 0

/-- The canonical Souza atom is indeed a Souza atom. -/
theorem canonicalSouzaAtom_isSouzaAtom (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G) :
    IsSouzaAtom G s p Q (canonicalSouzaAtom G s p Q) := by
  classical
  refine ⟨fun x hx => by simp [canonicalSouzaAtom, hx],
          ((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) : ℝ),
          fun x hx => by simp [canonicalSouzaAtom, hx], ?_⟩
  have hnonneg :
      0 ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  simp [Complex.norm_real, Real.norm_of_nonneg hnonneg]

-- ============================================================
-- §4. Local vector space for Souza atoms
-- ============================================================

/--
The local vector space at cell `Q` for Souza atoms is `ℂ`, with the
linear map `c ↦ (fun x => if x ∈ Q.cell then c else 0)`.
-/
def souzaLocalVectorSpace (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) :
    WeakGridSpace.LocalVectorSpace α := by
  classical
  exact
  { carrier := ℂ
    toFun :=
      { toFun    := fun c => Q.cell.indicator fun _ => c
        map_add' := by intro c d; ext x; by_cases hx : x ∈ Q.cell <;> simp [hx]
        map_smul' := by intro σ c; ext x; by_cases hx : x ∈ Q.cell <;> simp [hx] }
    injective_toFun := by
      intro c d hcd
      obtain ⟨x, hx⟩ := G.grid.partition_nonempty Q.level Q.cell Q.mem
      have := congr_fun hcd x
      simpa [hx] using this }

-- ============================================================
-- §5. Souza atom set and AtomFamily
-- ============================================================

/--
The set of Souza atoms at `Q`, viewed as elements `c : ℂ` of the local vector
space: those satisfying `‖c‖ ≤ μ(Q)^(s − 1/p)`.
-/
def souzaAtomsSet (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G) : Set ℂ :=
  { c : ℂ | ‖c‖ ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) }

/--
Souza atoms `(s,p)` form an `AtomFamily` on the `WeakGridSpace` induced by
the `GoodGrid`.  They are of type `(s, p, ∞)`, so `u = ∞` and `uConj = 1`.
-/
def souzaAtomFamily (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    WeakGridSpace.AtomFamily G.toWeakGridSpace s p ∞ where
  uConj             := 1
  s_pos             := hs
  one_le_p          := hp
  p_ne_top          := hp_top
  one_le_u          := le_top
  holder_conjugate  := by
    rw [ENNReal.holderConjugate_iff]
    simp
  localSpace        := fun Q =>
    souzaLocalVectorSpace G ⟨Q.level, Q.cell, Q.mem⟩
  atoms             := fun Q =>
    souzaAtomsSet G s p ⟨Q.level, Q.cell, Q.mem⟩
  atoms_nonempty    := fun Q =>
    ⟨0, by
      have hnonneg :
          0 ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) :=
        Real.rpow_nonneg ENNReal.toReal_nonneg _
      change ‖(0 : ℂ)‖ ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)
      simpa using hnonneg⟩
  local_memLp       := fun Q (c : ℂ) => by
    -- c · 1_Q ∈ L^(p · ∞) = L^∞, proved via boundedness
    classical
    have hp_ne_zero : p ≠ 0 :=
      ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le hp)
    have hp_top_mul : p * ∞ = ∞ := ENNReal.mul_top hp_ne_zero
    have hQmeas : MeasurableSet Q.cell :=
      G.grid.grid.measurable Q.level Q.cell Q.mem
    have hQfinite : G.grid.μ Q.cell ≠ ∞ :=
      by
        letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
        exact MeasureTheory.measure_ne_top G.grid.μ Q.cell
    simpa [souzaLocalVectorSpace, hp_top_mul, GoodGridSpace.toWeakGridSpace,
      GoodGridSpace.toWeakGrid] using
      (MeasureTheory.memLp_indicator_const (μ := G.grid.μ) (s := Q.cell)
        (p := ∞) hQmeas c (Or.inr hQfinite))
  local_support     := fun Q (c : ℂ) x hx => by
    classical
    change (Q.cell.indicator fun _ => c) x = 0
    simp [hx]
  atoms_convex      := fun Q => by
    -- souzaAtomsSet Q is a closed ball in ℂ, hence convex
    simpa [souzaAtomsSet, Metric.closedBall, dist_eq_norm] using
      (convex_closedBall (0 : ℂ) ((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)))
  atoms_phase_invariant := fun Q (c : ℂ) σ hc hσ => by
    simp only [souzaAtomsSet] at hc ⊢
    calc ‖σ • c‖ = ‖σ‖ * ‖c‖ := norm_smul σ c
      _ = 1 * ‖c‖             := by rw [hσ]
      _ = ‖c‖                 := one_mul _
      _ ≤ _                   := hc
  atom_bound        := fun Q (c : ℂ) hc => by
    -- eLpNorm (c · 1_Q) ∞ μ ≤ μ(Q)^(s − 1·p⁻¹)
    simp only [souzaAtomsSet] at hc
    classical
    have hp_ne_zero : p ≠ 0 :=
      ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le hp)
    have hp_top_mul : p * ∞ = ∞ := ENNReal.mul_top hp_ne_zero
    let r : ℝ := s - (p.toReal)⁻¹
    have hQpos : 0 < G.grid.μ Q.cell :=
      G.grid.positive_measure Q.level Q.cell Q.mem
    have hQfinite : G.grid.μ Q.cell ≠ ∞ :=
      by
        letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
        exact MeasureTheory.measure_ne_top G.grid.μ Q.cell
    have hQtoReal_pos : 0 < (G.grid.μ Q.cell).toReal :=
      ENNReal.toReal_pos hQpos.ne' hQfinite
    have hscale :
        ENNReal.ofReal ((G.grid.μ Q.cell).toReal ^ r) =
          (G.grid.μ Q.cell) ^ r := by
      rw [← ENNReal.ofReal_rpow_of_pos hQtoReal_pos, ENNReal.ofReal_toReal hQfinite]
    have hnorm_le :
        ‖c‖ₑ ≤ (G.grid.μ Q.cell) ^ r := by
      calc
        ‖c‖ₑ = ENNReal.ofReal ‖c‖ := by rw [ofReal_norm_eq_enorm]
        _ ≤ ENNReal.ofReal ((G.grid.μ Q.cell).toReal ^ r) :=
          ENNReal.ofReal_le_ofReal hc
        _ = (G.grid.μ Q.cell) ^ r := hscale
    change
      MeasureTheory.eLpNorm (Q.cell.indicator fun _ => c) (p * ∞)
          G.toWeakGridSpace.measure ≤
        WeakGridSpace.atomMeasureScale G.toWeakGridSpace s p 1 Q
    calc
      MeasureTheory.eLpNorm (Q.cell.indicator fun _ => c) (p * ∞) G.toWeakGridSpace.measure
          = MeasureTheory.eLpNorm (Q.cell.indicator fun _ => c) ∞ G.toWeakGridSpace.measure := by
            rw [hp_top_mul]
      _ ≤ ‖c‖ₑ := by
            simpa [MeasureTheory.eLpNorm_exponent_top] using
              (MeasureTheory.eLpNormEssSup_indicator_const_le
                (μ := G.toWeakGridSpace.measure) (s := Q.cell) (c := c))
      _ ≤ G.toWeakGridSpace.measure Q.cell ^ r := by
            simpa [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
              WeakGridSpace.WeakGridSpace.measure] using hnorm_le
      _ = WeakGridSpace.atomMeasureScale G.toWeakGridSpace s p 1 Q := by
            simp [WeakGridSpace.atomMeasureScale, WeakGridSpace.atomMeasureExponent, r,
              GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
              WeakGridSpace.WeakGridSpace.measure, ENNReal.toReal_one]

-- ============================================================
-- §6. Besov space induced by a GoodGrid and Souza atoms
-- ============================================================

/--
The Besov space associated to a `GoodGridSpace` and Souza atoms.

This is the general weak-grid Besov-ish space specialized to:
- the weak grid induced by `G`,
- the Souza atom family of type `(s,p,∞)`, and
- the coefficient summability exponent `q`.
-/
noncomputable def SouzaBesovSpace (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ q)] :
    Submodule ℂ (MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  exact WeakGridSpace.BesovishSpace (souzaAtomFamily G s p hs hp hp_top) q

/--
Membership in the Souza Besov space: an `L^p` function has an atomic
representation by Souza atoms with finite `(p,q)` coefficient cost.
-/
def MemSouzaBesov (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ q)]
    (g : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) : Prop :=
  g ∈ SouzaBesovSpace G s p q hs hp hp_top

-- ============================================================
-- §7. Grid generators and finite-level Besov elements
-- ============================================================

/--
The set of all measurable partition cells occurring at some level of the
good grid.

This is the concrete generating class used in the monotone-class density
argument below: first prove that the closed Souza Besov space contains
indicator functions of these cells, then use that the grid generates the
ambient sigma-algebra.
-/
def gridGeneratingSets (G : GoodGridSpace (α := α)) : Set (Set α) :=
  ⋃ n, (G.grid.grid.partitions n : Set (Set α))

/--
The grid-generating cells form a pi-system.

Nestedness of the good grid gives the key dichotomy: two cells from possibly
different levels are either disjoint or the finer one is contained in the
coarser one. Hence any nonempty intersection of two generators is again one
of the two cells.
-/
theorem isPiSystem_gridGeneratingSets (G : GoodGridSpace (α := α)) :
    IsPiSystem (gridGeneratingSets G) := by
  classical
  intro s hs t ht hst
  rcases Set.mem_iUnion.mp hs with ⟨n, hn⟩
  rcases Set.mem_iUnion.mp ht with ⟨m, hm⟩
  rcases le_total n m with hnm | hmn
  · rcases G.grid.partition_subset_or_disjoint_of_le n m hnm s hn t hm with hsub | hdisj
    · rw [Set.inter_eq_right.2 hsub]
      exact Set.mem_iUnion.mpr ⟨m, hm⟩
    · exfalso
      exact hst.ne_empty (Set.disjoint_iff_inter_eq_empty.mp hdisj.symm)
  · rcases G.grid.partition_subset_or_disjoint_of_le m n hmn t hm s hn with hsub | hdisj
    · rw [Set.inter_eq_left.2 hsub]
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    · exfalso
      exact hst.ne_empty (Set.disjoint_iff_inter_eq_empty.mp hdisj)

/--
The measurable space on `α` is generated by the good-grid cells.

This unwraps the `generates` field of the underlying nested partition
sequence, replacing the supremum over levels by the single set
`gridGeneratingSets G`.
-/
theorem grid_generates_eq_generateFrom_gridGeneratingSets (G : GoodGridSpace (α := α)) :
    ‹MeasurableSpace α› = MeasurableSpace.generateFrom (gridGeneratingSets G) := by
  calc
    ‹MeasurableSpace α› =
        ⨆ n, MeasurableSpace.generateFrom (G.grid.grid.partitions n) := by
      simpa using G.grid.grid.generates.symm
    _ = MeasurableSpace.generateFrom (gridGeneratingSets G) := by
      rw [MeasurableSpace.iSup_generateFrom]
      simp [gridGeneratingSets]

end
end GoodGridSpace

namespace WeakGridSpace

open scoped ENNReal MeasureTheory
open MeasureTheory

variable {α : Type*} [MeasurableSpace α]
variable {G : _root_.WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
variable [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/--
A single level block is already a finite-cost Besov-ish element.

The representation has exactly one nonzero level, namely `k`, and is zero at
all other levels. Therefore the `(p,q)` coefficient cost is finite: for
`q = ∞` the supremum is bounded by the single nonzero level, and for finite
`q` the coefficient sequence has finite support.
-/
theorem levelBlock_toLp_mem_besovish
    (A : AtomFamily G s p u) {k : ℕ} (B : LevelBlock A k) :
    B.toLp A ∈ BesovishSpace A q := by
  classical
  -- Build the representation concentrated at the single level `k`.
  let R : LpGridRepresentation A (B.toLp A) :=
    { block := fun n => if h : n = k then h.symm ▸ B else LevelBlock.zero A n
      hasSum := by
        have hterm :
            (fun n => ((if h : n = k then h.symm ▸ B else LevelBlock.zero A n) :
                LevelBlock A n).toLp A)
              = fun n => if n = k then B.toLp A else 0 := by
          funext n
          by_cases h : n = k
          · subst n
            simp
          · simp [h]
        simpa [hterm] using hasSum_ite_eq k (B.toLp A) }
  refine ⟨R, ?_⟩
  have hp_pos : 0 < p.toReal :=
    (ENNReal.toReal_pos_iff_ne_top p).2 A.p_ne_top
  have hzero_level : ∀ n, n ≠ k → R.levelCoeffPower n = 0 := by
    intro n hn
    unfold LpGridRepresentation.levelCoeffPower
    simp [R, hn, LevelBlock.zero, Real.zero_rpow hp_pos.ne']
  by_cases hq : q = ∞
  · -- In the `q = ∞` case, the cost is a bounded supremum.
    simp only [hq, ↓reduceIte]
    refine ⟨max 0 ((R.levelCoeffPower k) ^ (1 / p.toReal)), ?_⟩
    rintro x ⟨n, rfl⟩
    by_cases hn : n = k
    · subst n
      exact le_max_right _ _
    · have hinv_pos : 0 < 1 / p.toReal := div_pos one_pos hp_pos
      have hx : (R.levelCoeffPower n) ^ (1 / p.toReal) = 0 := by
        rw [hzero_level n hn, Real.zero_rpow hinv_pos.ne']
      change (R.levelCoeffPower n) ^ (1 / p.toReal) ≤
        max 0 ((R.levelCoeffPower k) ^ (1 / p.toReal))
      rw [hx]
      exact le_max_left _ _
  · -- In the finite-`q` case, summability follows from finite support.
    simp only [hq, ↓reduceIte]
    refine summable_of_hasFiniteSupport ?_
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton k).subset ?_
    intro n hn
    contrapose! hn
    have hq_pos : 0 < q.toReal := by
      linarith [(ENNReal.dichotomy q).resolve_left hq]
    have hpow_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
    rw [Function.mem_support]
    simp only [ne_eq, not_not]
    rw [hzero_level n (by simpa using hn), Real.zero_rpow hpow_pos.ne']

end WeakGridSpace

namespace GoodGridSpace

open scoped ENNReal MeasureTheory

variable {α : Type*} [MeasurableSpace α]

noncomputable section

/--
Constant multiples of good-grid cell indicators belong to the Souza Besov
space.

For a cell `Q`, the Souza atom with local coefficient
`μ(Q)^(s - 1 / p)` is the normalized indicator of `Q`. Choosing the block
coefficient `c / μ(Q)^(s - 1 / p)` makes the single active term equal to
`c · 1_Q`; all other cells in the same level have coefficient zero.
-/
theorem indicatorConstLp_cell_mem_souzaBesov
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Q : GoodGridCell G) (c : ℂ) :
    MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
        (G.grid.grid.measurable Q.level Q.cell Q.mem)
        (GoodGridCell.measure_ne_top Q) c
      ∈ SouzaBesovSpace G s p q hs hp hp_top := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Qw : WeakGridSpace.LevelCell G.toWeakGridSpace Q.level := ⟨Q.cell, Q.mem⟩
  let r : WeakGridSpace.LevelCell G.toWeakGridSpace Q.level → ℝ := fun P =>
    (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹)
  have hr_nonneg : ∀ P, 0 ≤ r P := by
    intro P
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hrQ_pos : 0 < r Qw := by
    have hQpos : 0 < G.grid.μ Q.cell := GoodGridCell.measure_pos Q
    have hQfinite : G.grid.μ Q.cell ≠ ∞ := GoodGridCell.measure_ne_top Q
    have hQtoReal_pos : 0 < (G.grid.μ Q.cell).toReal :=
      ENNReal.toReal_pos hQpos.ne' hQfinite
    exact Real.rpow_pos_of_pos hQtoReal_pos _
  -- The block is supported on the single cell `Qw`; every other coefficient is zero.
  let B : WeakGridSpace.LevelBlock A Q.level :=
    { coeff := fun P => if P = Qw then c / (r Qw : ℂ) else 0
      atom := fun P => ((r P : ℝ) : ℂ)
      atom_mem := by
        intro P
        change ‖(((r P : ℝ) : ℂ))‖ ≤ r P
        simp [Complex.norm_real, Real.norm_of_nonneg (hr_nonneg P)] }
  have hB_toLp :
      B.toLp A =
        MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
          (G.grid.grid.measurable Q.level Q.cell Q.mem)
          (GoodGridCell.measure_ne_top Q) c := by
    apply MeasureTheory.Lp.ext
    refine (WeakGridSpace.LevelBlock.coeFn_toLp A B).trans ?_
    have hpoint :
        B.toFunLt A =ᵐ[G.toWeakGridSpace.measure] Q.cell.indicator (fun _ => c) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hx : x ∈ Q.cell
      · -- On `Q`, the unique nonzero summand is the one indexed by `Qw`.
        have hsum :
          B.toFunLt A x =
            B.coeff Qw *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace Q.level Qw)
                (B.atom Qw) x := by
          unfold WeakGridSpace.LevelBlock.toFunLt
          exact Finset.sum_eq_single Qw
            (by
              intro P _ hP
              have hPQ : P ≠ Qw := hP
              simp [B, hPQ])
            (by intro hnot; exact False.elim (hnot (by simp [Qw])))
        rw [hsum]
        rw [Set.indicator_of_mem hx]
        simp only [A, B, Qw, WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily,
          souzaLocalVectorSpace]
        change c / (r Qw : ℂ) * (Q.cell.indicator (fun _ => (r Qw : ℂ)) x) = c
        rw [Set.indicator_of_mem hx]
        field_simp [show (r Qw : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt hrQ_pos)]
      · -- Off `Q`, the active cell indicator is zero, and all other coefficients vanish.
        have hsum :
          B.toFunLt A x = 0 := by
          unfold WeakGridSpace.LevelBlock.toFunLt
          refine Finset.sum_eq_zero ?_
          intro P hP
          by_cases hPQ : P = Qw
          · subst P
            simp only [A, B, Qw, WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily,
              souzaLocalVectorSpace]
            change c / (r Qw : ℂ) * (Q.cell.indicator (fun _ => (r Qw : ℂ)) x) = 0
            rw [Set.indicator_of_notMem hx]
            simp
          · simp [B, hPQ]
        rw [hsum]
        simp [hx]
    exact hpoint.trans
      (MeasureTheory.indicatorConstLp_coeFn (μ := G.toWeakGridSpace.measure)
        (p := p) (hs := G.grid.grid.measurable Q.level Q.cell Q.mem)
        (hμs := GoodGridCell.measure_ne_top Q) (c := c)).symm
  simpa [A, hB_toLp] using
    WeakGridSpace.levelBlock_toLp_mem_besovish (A := A) (q := q) B

-- ============================================================
-- §8. Strong compactness hypothesis A5 for Souza atoms
-- ============================================================

/--
For Souza atoms, `AssumptionA5` holds: `p` is finite and at least one by
hypothesis, and the atom set on each cell is the image in `L^p` of a closed
ball in `ℂ`.
-/
theorem souza_assumptionA5 (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] :
    WeakGridSpace.AssumptionA5 (souzaAtomFamily G s p hs hp hp_top) := by
  classical
  refine ⟨hp, hp_top, ?_⟩
  intro Q
  let A := souzaAtomFamily G s p hs hp hp_top
  let r : ℝ := (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)
  let toLpAtom : ℂ → MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure :=
    fun c => MeasureTheory.MemLp.toLp
      (A.toFunction Q c) (A.local_memLp_p Q c)
  have hcompact_ball : IsSeqCompact (Metric.closedBall (0 : ℂ) r) :=
    (isCompact_closedBall (0 : ℂ) r).isSeqCompact
  have hseq_cont : SeqContinuous toLpAtom := by
    have hQmeas : MeasurableSet Q.cell :=
      G.grid.grid.measurable Q.level Q.cell Q.mem
    have hQfinite : G.grid.μ Q.cell ≠ ∞ := by
      letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Q.cell
    have hone_mem :
        MeasureTheory.MemLp (Q.cell.indicator fun _ : α => (1 : ℂ))
          p G.toWeakGridSpace.measure := by
      simpa [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
        WeakGridSpace.WeakGridSpace.measure] using
        (MeasureTheory.memLp_indicator_const (μ := G.grid.μ) (s := Q.cell)
          (p := p) hQmeas (1 : ℂ) (Or.inr hQfinite))
    let oneAtom : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure :=
      MeasureTheory.MemLp.toLp (Q.cell.indicator fun _ : α => (1 : ℂ)) hone_mem
    have htoLpAtom_eq : toLpAtom = fun c : ℂ => c • oneAtom := by
      funext c
      have hlocal :
          A.toFunction Q c = c • (Q.cell.indicator fun _ : α => (1 : ℂ)) := by
        ext x
        change (Q.cell.indicator fun _ : α => c) x =
          (c • (Q.cell.indicator fun _ : α => (1 : ℂ))) x
        by_cases hx : x ∈ Q.cell <;>
          simp [hx]
      calc
        toLpAtom c
            = MeasureTheory.MemLp.toLp
                (c • (Q.cell.indicator fun _ : α => (1 : ℂ)))
                (hone_mem.const_smul c) := by
                exact MeasureTheory.MemLp.toLp_congr
                  (A.local_memLp_p Q c) (hone_mem.const_smul c)
                  (Filter.EventuallyEq.of_eq hlocal)
        _ = c • oneAtom := by
                rw [← hone_mem.toLp_const_smul c]
    rw [htoLpAtom_eq]
    exact (continuous_id.smul continuous_const).seqContinuous
  have himage_seq : IsSeqCompact (toLpAtom '' Metric.closedBall (0 : ℂ) r) :=
    hcompact_ball.image hseq_cont
  convert himage_seq using 1
  ext f
  constructor
  · intro hf
    rcases hf with ⟨c, hc, rfl⟩
    exact ⟨c, by
      simpa [Metric.mem_closedBall, dist_zero_right, A, r, souzaAtomFamily,
        souzaAtomsSet, WeakGridSpace.AtomFamily.IsAtom] using hc, rfl⟩
  · intro hf
    rcases hf with ⟨c, hc, rfl⟩
    exact ⟨c, by
      simpa [Metric.mem_closedBall, dist_zero_right, A, r, souzaAtomFamily,
        souzaAtomsSet, WeakGridSpace.AtomFamily.IsAtom] using hc, rfl⟩

private theorem levelMesh_le_geometric (G : GoodGridSpace (α := α)) (k : ℕ) :
    sSup (Set.range fun Q : WeakGridSpace.LevelCell G.toWeakGridSpace k =>
      (G.toWeakGridSpace.measure Q.1).toReal) ≤
      G.grid.lambda2 ^ k * (G.grid.μ Set.univ).toReal := by
  classical
  let S : Set ℝ := Set.range fun Q : WeakGridSpace.LevelCell G.toWeakGridSpace k =>
    (G.toWeakGridSpace.measure Q.1).toReal
  have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
    le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  change sSup S ≤ G.grid.lambda2 ^ k * (G.grid.μ Set.univ).toReal
  have hbound : ∀ x ∈ S, x ≤ G.grid.lambda2 ^ k * (G.grid.μ Set.univ).toReal := by
    intro x hx
    rcases hx with ⟨Q, rfl⟩
    have hQ := cell_measure_le_lambda2_pow_mul_univ G k Q.1 Q.2
    have huniv_ne_top : G.grid.μ Set.univ ≠ ∞ := by
      letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Set.univ
    have hbound_ne_top : ((ENNReal.ofReal G.grid.lambda2) ^ k * G.grid.μ Set.univ) ≠ ∞ := by
      exact ENNReal.mul_ne_top (by simp) huniv_ne_top
    have htoReal := ENNReal.toReal_mono hbound_ne_top hQ
    simpa [S, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
      WeakGridSpace.WeakGridSpace.measure, ENNReal.toReal_mul, huniv_ne_top, hlam_nonneg] using htoReal
  exact Real.sSup_le hbound (mul_nonneg (pow_nonneg hlam_nonneg k) ENNReal.toReal_nonneg)

private theorem souza_hmesh (G : GoodGridSpace (α := α)) :
    Filter.Tendsto
      (fun k => sSup (Set.range fun Q : WeakGridSpace.LevelCell G.toWeakGridSpace k =>
        (G.toWeakGridSpace.measure Q.1).toReal))
      Filter.atTop
      (nhds 0) := by
  let m : ℕ → ℝ := fun k =>
    sSup (Set.range fun Q : WeakGridSpace.LevelCell G.toWeakGridSpace k =>
      (G.toWeakGridSpace.measure Q.1).toReal)
  let ρ : ℝ := G.grid.lambda2
  let C : ℝ := (G.grid.μ Set.univ).toReal
  have hρ_nonneg : 0 ≤ ρ := le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hρ_lt_one : ρ < 1 := G.grid.hlambda2_lt_one
  have hgeom_sum : Summable (fun k : ℕ => C * ρ ^ k) := by
    simpa [ρ, C, mul_comm, mul_left_comm, mul_assoc] using
      (summable_geometric_of_lt_one hρ_nonneg hρ_lt_one).mul_left C
  have hgeom_tendsto : Filter.Tendsto (fun k : ℕ => C * ρ ^ k) Filter.atTop (nhds 0) := by
    simpa [ρ, C] using hgeom_sum.tendsto_atTop_zero
  have hlower : (fun _ : ℕ => (0 : ℝ)) ≤ fun k => m k := by
    intro k
    dsimp [m]
    refine Real.sSup_nonneg ?_
    intro x hx
    rcases hx with ⟨Q, rfl⟩
    exact ENNReal.toReal_nonneg
  have hupper : (fun k => m k) ≤ fun k => C * ρ ^ k := by
    intro k
    dsimp [m]
    simpa [ρ, C, mul_comm, mul_left_comm, mul_assoc] using levelMesh_le_geometric G k
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom_tendsto hlower hupper

private theorem souza_hCco
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    WeakGridSpace.LpGridRepresentation.cCoefficientFinite p q
      (fun k => (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
        G.toWeakGridSpace s p p k) ^ p.toReal) := by
  let w : ℕ → ℝ := fun k =>
    WeakGridSpace.LpGridRepresentation.levelMeasureWeight G.toWeakGridSpace s p p k
  let C : ℝ := ((G.grid.μ Set.univ).toReal) ^ s
  let ρ : ℝ := G.grid.lambda2 ^ s
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hmu_nonneg : 0 ≤ (G.grid.μ Set.univ).toReal := ENNReal.toReal_nonneg
  have hlam_nonneg : 0 ≤ G.grid.lambda2 := le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hρ_nonneg : 0 ≤ ρ := Real.rpow_nonneg hlam_nonneg _
  have hρ_lt_one : ρ < 1 := by
    simpa [ρ] using Real.rpow_lt_one hlam_nonneg G.grid.hlambda2_lt_one hs
  have hC_nonneg : 0 ≤ C := Real.rpow_nonneg hmu_nonneg _
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg G.toWeakGridSpace s p p k
  have hw_bound : ∀ k, w k ≤ C * ρ ^ k := by
    intro k
    have hmesh_nonneg :
        0 ≤ sSup (Set.range fun Q : WeakGridSpace.LevelCell G.toWeakGridSpace k =>
          (G.toWeakGridSpace.measure Q.1).toReal) := by
      refine Real.sSup_nonneg ?_
      intro x hx
      rcases hx with ⟨Q, rfl⟩
      exact ENNReal.toReal_nonneg
    calc
      w k
          = (sSup (Set.range fun Q : WeakGridSpace.LevelCell G.toWeakGridSpace k =>
              (G.toWeakGridSpace.measure Q.1).toReal)) ^ s := by
              simp [w, WeakGridSpace.LpGridRepresentation.levelMeasureWeight]
      _ ≤ (G.grid.lambda2 ^ k * (G.grid.μ Set.univ).toReal) ^ s := by
            exact Real.rpow_le_rpow hmesh_nonneg (levelMesh_le_geometric G k) hs.le
      _ = ((G.grid.μ Set.univ).toReal) ^ s * (G.grid.lambda2 ^ s) ^ k := by
            rw [Real.mul_rpow (pow_nonneg hlam_nonneg k) hmu_nonneg, mul_comm]
            have hpow : (G.grid.lambda2 ^ k : ℝ) ^ s = (G.grid.lambda2 ^ s) ^ k := by
              calc
                (G.grid.lambda2 ^ k : ℝ) ^ s = G.grid.lambda2 ^ ((k : ℝ) * s) := by
                    simpa [mul_comm] using (Real.rpow_natCast_mul hlam_nonneg k s).symm
                _ = G.grid.lambda2 ^ (s * k) := by ring_nf
                _ = (G.grid.lambda2 ^ s) ^ k := by
                    simpa [mul_comm] using (Real.rpow_mul_natCast hlam_nonneg s k)
            rw [hpow]
      _ = C * ρ ^ k := by simp [C, ρ]
  have hgeom_sum : Summable (fun k : ℕ => C * ρ ^ k) := by
    simpa [C, ρ, mul_comm, mul_left_comm, mul_assoc] using
      (summable_geometric_of_lt_one hρ_nonneg hρ_lt_one).mul_left C
  have hsum_w : Summable w :=
    Summable.of_nonneg_of_le hw_nonneg hw_bound hgeom_sum
  have hroot : ∀ k, ((w k) ^ p.toReal) ^ (1 / p.toReal) = w k := by
    intro k
    simpa [one_div] using Real.rpow_rpow_inv (hw_nonneg k) hp_pos.ne'
  by_cases hq1 : q = 1
  · have hbdd : BddAbove (Set.range fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
      refine ⟨∑' k, w k, ?_⟩
      intro x hx
      rcases hx with ⟨k, rfl⟩
      change ((w k) ^ p.toReal) ^ (1 / p.toReal) ≤ ∑' k, w k
      rw [hroot k]
      simpa using sum_le_hasSum ({k} : Finset ℕ) (fun n _ => hw_nonneg n) hsum_w.hasSum
    simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, w] using hbdd
  · by_cases hqtop : q = ∞
    · have hsum_root : Summable (fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
        refine Summable.of_nonneg_of_le
          (fun k => by rw [hroot k]; exact hw_nonneg k)
          (fun k => by rw [hroot k]; exact hw_bound k)
          hgeom_sum
      simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, w] using hsum_root
    · let q' : ℝ≥0∞ := q / (q - 1)
      have hq_toReal_le : (1 : ℝ) ≤ q.toReal := by
        have h := ENNReal.toReal_mono hqtop (Fact.out : 1 ≤ q)
        simpa using h
      have hq_toReal_ne_one : q.toReal ≠ 1 := by
        intro hreal
        apply hq1
        exact ((ENNReal.toReal_eq_toReal_iff' ENNReal.one_ne_top hqtop).mp (by simp [hreal])).symm
      have hq_toReal_one : 1 < q.toReal :=
        lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
      have hq_conj : q'.toReal.HolderConjugate q.toReal := by
        simpa [q'] using
          WeakGridSpace.LpGridRepresentation.holderConjugate_q_div_qsub1_toReal
            (q := q) hq_toReal_one hqtop
      have hq'_pos : 0 < q'.toReal := by
        rw [Real.holderConjugate_iff] at hq_conj
        exact zero_lt_one.trans hq_conj.1
      have hsum_qgeom : Summable (fun k : ℕ => C ^ q'.toReal * (ρ ^ q'.toReal) ^ k) := by
        have hρq_nonneg : 0 ≤ ρ ^ q'.toReal := Real.rpow_nonneg hρ_nonneg _
        have hρq_lt_one : ρ ^ q'.toReal < 1 := Real.rpow_lt_one hρ_nonneg hρ_lt_one hq'_pos
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (summable_geometric_of_lt_one hρq_nonneg hρq_lt_one).mul_left (C ^ q'.toReal)
      have hroot_pow : ∀ k,
          ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) = (w k) ^ q'.toReal := by
        intro k
        have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
          field_simp [hp_pos.ne']
        calc
          ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal)
              = ((w k) ^ p.toReal) ^ ((1 / p.toReal) * q'.toReal) := by rw [hdiv]
          _ = (((w k) ^ p.toReal) ^ (1 / p.toReal)) ^ q'.toReal := by
                rw [Real.rpow_mul (Real.rpow_nonneg (hw_nonneg k) _)]
          _ = (w k) ^ q'.toReal := by rw [hroot k]
      have hpow_geom : ∀ k, (ρ ^ k : ℝ) ^ q'.toReal = (ρ ^ q'.toReal) ^ k := by
        intro k
        calc
          (ρ ^ k : ℝ) ^ q'.toReal = ρ ^ ((k : ℝ) * q'.toReal) := by
              simpa [mul_comm] using (Real.rpow_natCast_mul hρ_nonneg k q'.toReal).symm
          _ = ρ ^ (q'.toReal * k) := by ring_nf
          _ = (ρ ^ q'.toReal) ^ k := by
              simpa [mul_comm] using (Real.rpow_mul_natCast hρ_nonneg q'.toReal k)
      have hle_q :
          (fun k => ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal)) ≤
            fun k => C ^ q'.toReal * (ρ ^ q'.toReal) ^ k := by
        intro k
        change ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) ≤ C ^ q'.toReal * (ρ ^ q'.toReal) ^ k
        rw [hroot_pow k]
        calc
          (w k) ^ q'.toReal ≤ (C * ρ ^ k) ^ q'.toReal := by
            exact Real.rpow_le_rpow (hw_nonneg k) (hw_bound k) hq'_pos.le
          _ = C ^ q'.toReal * (ρ ^ k : ℝ) ^ q'.toReal := by
                rw [Real.mul_rpow hC_nonneg (pow_nonneg hρ_nonneg k)]
          _ = C ^ q'.toReal * (ρ ^ q'.toReal) ^ k := by rw [hpow_geom k]
      have hnonneg_q : ∀ k, 0 ≤ ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) := by
        intro k
        exact Real.rpow_nonneg (Real.rpow_nonneg (hw_nonneg k) _) _
      simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, q', w] using
        Summable.of_nonneg_of_le hnonneg_q hle_q hsum_qgeom

-- ============================================================
-- §9. Completeness of Souza Besov spaces with the cost norm
-- ============================================================

/--
The Souza Besov space associated to a `GoodGrid`, endowed with the coefficient
cost norm `Norm_Costpq`, is complete, assuming the two concrete components of
the analytic grid hypothesis: coefficient summability and mesh decay.

The compactness hypothesis `A5` is supplied by `souza_assumptionA5`.
-/
theorem souzaBesovSpace_costNorm_completeSpace
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    @CompleteSpace
      (SouzaBesovSpace G s p q hs hp hp_top)
      (WeakGridSpace.BesovishSpace.costNormedAddCommGroup
        (A := souzaAtomFamily G s p hs hp hp_top) (q := q)
        hp_top (souza_hCco G s p q hs hp hp_top)).toMetricSpace.toPseudoMetricSpace.toUniformSpace := by
  let hCco : WeakGridSpace.LpGridRepresentation.cCoefficientFinite p q
      (fun k => (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
        G.toWeakGridSpace s p p k) ^ p.toReal) :=
    souza_hCco G s p q hs hp hp_top
  let hmesh : Filter.Tendsto
      (fun k => sSup (Set.range fun Q : WeakGridSpace.LevelCell G.toWeakGridSpace k =>
        (G.toWeakGridSpace.measure Q.1).toReal))
      Filter.atTop
      (nhds 0) :=
    souza_hmesh G
  let hG2 : WeakGridSpace.AssumptionG2 G.toWeakGridSpace s p ∞ q := ⟨hCco, hmesh⟩
  exact WeakGridSpace.besovishSpace_costNorm_completeSpace
    (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
    hp_top hs le_top
    (souzaAtomFamily G s p hs hp hp_top)
    hG2
    (souza_assumptionA5 G s p hs hp hp_top)

-- ============================================================
-- §10. Compactness of closed cost balls
-- ============================================================

/--
The closed `Norm_Costpq` ball in the Souza Besov space is sequentially compact
for the ambient strong `L^p` topology.

The set is viewed as a subset of `L^p`: an element belongs to the ball if it
lies in the Souza Besov space and its cost norm is at most `C`.
-/
theorem souza_closedCostBallInLp_isSeqCompact
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {C : ℝ} (hC : 0 ≤ C) :
    IsSeqCompact
      {f : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure |
        ∃ hf : f ∈ SouzaBesovSpace G s p q hs hp hp_top,
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q ⟨f, hf⟩ ≤ C} := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let hG2 : WeakGridSpace.AssumptionG2 G.toWeakGridSpace s p ∞ q :=
    ⟨souza_hCco G s p q hs hp hp_top, souza_hmesh G⟩
  intro x hx
  let gseq : ℕ → WeakGridSpace.BesovishSpace A q := fun n =>
    ⟨x n, Classical.choose (hx n)⟩
  have hgball : ∀ n,
      WeakGridSpace.BesovishSpace.Norm_Costpq A q (gseq n) ≤ C := by
    intro n
    exact Classical.choose_spec (hx n)
  rcases WeakGridSpace.closed_Norm_Costpq_ball_strongly_seqCompact
      (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
      hp_top hs le_top A hG2
      (souza_assumptionA5 G s p hs hp hp_top)
      hC gseq hgball with
      ⟨φ, hφ, gLim, hLim_ball, hLp_tendsto⟩
  refine ⟨(gLim : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure), ?_, φ, hφ, ?_⟩
  · refine ⟨?_, hLim_ball⟩
    exact gLim.2
  · simpa [gseq] using hLp_tendsto

/--
The closed `Norm_Costpq` ball in the Souza Besov space is compact in the ambient
`L^p` topology.
-/
theorem souza_closedCostBallInLp_isCompact
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {C : ℝ} (hC : 0 ≤ C) :
    IsCompact
      {f : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure |
        ∃ hf : f ∈ SouzaBesovSpace G s p q hs hp hp_top,
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q ⟨f, hf⟩ ≤ C} := by
  exact (souza_closedCostBallInLp_isSeqCompact G s p q hs hp hp_top hC).isCompact


/--
The closed `Norm_Costpq` ball is compact after viewing its elements in the
ambient strong `L^1` topology.

Since `SouzaBesovSpace G s p q` is a subspace of `L^p`, the statement is
formulated as the image of the `L^p` cost ball under the canonical continuous
finite-measure inclusion `L^p → L^1`. The proof is therefore just compactness
of continuous images, using `souza_closedCostBallInLp_isCompact`.
-/
theorem souza_closedCostBallInL1_isCompact
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {C : ℝ} (hC : 0 ≤ C) :
    IsCompact
      ((WeakGridSpace.LpGridRepresentation.lpInclusion
          (G := G.toWeakGridSpace) (p := 1) (t := p)
          ENNReal.one_ne_top hp_top hp) ''
        {f : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure |
          ∃ hf : f ∈ SouzaBesovSpace G s p q hs hp hp_top,
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q ⟨f, hf⟩ ≤ C}) := by
  exact (souza_closedCostBallInLp_isCompact G s p q hs hp hp_top hC).image
    (WeakGridSpace.LpGridRepresentation.lpInclusion
      (G := G.toWeakGridSpace) (p := 1) (t := p)
      ENNReal.one_ne_top hp_top hp).continuous

-- ============================================================
-- §11. Density in the ambient `L^p` space
-- ============================================================

/--
Indicator of a complement as the universe indicator minus the set indicator,
as an identity in `Lp ℂ p μ`.

This small helper is one of the closure properties needed in the monotone-class
argument for measurable indicators.
-/
lemma indicatorConstLp_complex_compl_eq_sub
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ] {p : ℝ≥0∞}
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℂ) :
    MeasureTheory.indicatorConstLp (μ := μ) p hs.compl (by finiteness) c
      = MeasureTheory.indicatorConstLp (μ := μ) p MeasurableSet.univ (by simp) c
          - MeasureTheory.indicatorConstLp (μ := μ) p hs hμs c := by
  rw [MeasureTheory.indicatorConstLp_univ (μ := μ) (p := p) (c := c)]
  ext1
  refine MeasureTheory.indicatorConstLp_coeFn.trans ?_
  have h_sub :=
    MeasureTheory.Lp.coeFn_sub
      (MeasureTheory.Lp.const p μ c)
      (MeasureTheory.indicatorConstLp (μ := μ) p hs hμs c)
  refine Filter.EventuallyEq.trans ?_ h_sub.symm
  filter_upwards [MeasureTheory.AEEqFun.coeFn_const (α := α) (μ := μ) (b := c),
    MeasureTheory.indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hs) (hμs := hμs)
      (c := c)] with x hxu hxs
  by_cases hmem : x ∈ s
  · simp [hxu, hxs, hmem]
  · simp [hxu, hxs, hmem]

/--
Every measurable indicator-constant `Lp` vector belongs to the closed Souza
Besov space.

Proof outline:
1. Let `C t` mean that every constant multiple of `1_t` belongs to the
   topological closure of the Souza Besov space.
2. The property holds for all grid cells by
   `indicatorConstLp_cell_mem_souzaBesov`.
3. The property is stable under complements and countable disjoint unions.
4. Since the grid cells form a pi-system generating the measurable space,
   `MeasurableSpace.induction_on_inter` gives `C t` for every measurable set.
-/
theorem indicatorConstLp_mem_souzaBesov_closure
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {t : Set α} (ht : MeasurableSet t) (hμt : G.toWeakGridSpace.measure t ≠ ∞)
    (c : ℂ) :
    MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p ht hμt c ∈
      (SouzaBesovSpace G s p q hs hp hp_top).topologicalClosure := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure G.toWeakGridSpace.measure := by
    dsimp [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
      WeakGridSpace.WeakGridSpace.measure]
    exact G.grid.isFinite
  let S : Submodule ℂ (MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) :=
    SouzaBesovSpace G s p q hs hp hp_top
  let M : Submodule ℂ (MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) :=
    S.topologicalClosure
  let C : ∀ u : Set α, MeasurableSet u → Prop :=
    fun u hu =>
      ∀ d : ℂ,
        MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p hu
          ((MeasureTheory.measure_lt_top G.toWeakGridSpace.measure u).ne) d ∈ M
  -- Empty set: the corresponding indicator is zero.
  have hempty : C ∅ MeasurableSet.empty := by
    intro d
    simp [M]
  -- Generators: grid-cell indicators are genuine Souza Besov elements.
  have hbasic :
      ∀ u (hu : u ∈ gridGeneratingSets G),
        C u ((grid_generates_eq_generateFrom_gridGeneratingSets G) ▸
          MeasurableSpace.GenerateMeasurable.basic u hu) := by
    intro u hu d
    rcases Set.mem_iUnion.mp hu with ⟨n, hn⟩
    have hum : MeasurableSet u := G.grid.grid.measurable n u hn
    have hcell :
        MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p hum
          ((MeasureTheory.measure_lt_top G.toWeakGridSpace.measure u).ne) d ∈ S := by
      simpa using
        indicatorConstLp_cell_mem_souzaBesov G s p q hs hp hp_top ⟨n, u, hn⟩ d
    exact S.le_topologicalClosure hcell
  -- Complements: use `1_{uᶜ} = 1_univ - 1_u`.
  have hcompl :
      ∀ u (hum : MeasurableSet u), C u hum → C uᶜ hum.compl := by
    intro u hum hu d
    have huniv : C Set.univ MeasurableSet.univ := by
      have hroot : Set.univ ∈ gridGeneratingSets G := by
        refine Set.mem_iUnion.mpr ⟨0, ?_⟩
        simp [G.grid.grid.first_partition_eq_univ]
      simpa using hbasic Set.univ hroot
    rw [indicatorConstLp_complex_compl_eq_sub hum
      ((MeasureTheory.measure_lt_top G.toWeakGridSpace.measure u).ne) d]
    exact M.sub_mem (huniv d) (hu d)
  -- Disjoint countable unions: approximate by finite partial unions in `Lp`.
  have hiUnion :
      ∀ (f : ℕ → Set α), Pairwise (fun i j => Disjoint (f i) (f j)) →
        ∀ hfm : ∀ i, MeasurableSet (f i),
        (∀ i, C (f i) (hfm i)) → C (⋃ i, f i) (MeasurableSet.iUnion hfm) := by
    intro f hfd hfm hf c
    let u : ℕ → Set α := fun n => ⋃ i ∈ Finset.range n, f i
    have hu_meas : ∀ n, MeasurableSet (u n) := by
      intro n
      exact Finset.measurableSet_biUnion (Finset.range n) (fun i _ => hfm i)
    -- Each finite partial union belongs to the closed subspace by finite additivity.
    have hu_mem : ∀ n, MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
        (hu_meas n) ((MeasureTheory.measure_lt_top G.toWeakGridSpace.measure (u n)).ne) c ∈ M := by
      intro n
      induction n with
      | zero =>
          simp [u, M]
      | succ n ihn =>
          have hdisj_union : Disjoint (u n) (f n) := by
            refine Set.disjoint_left.mpr ?_
            intro x hx_union hx_fn
            simp only [u, Finset.mem_range, Set.mem_iUnion, exists_prop] at hx_union
            rcases hx_union with ⟨i, hi_lt, hxi⟩
            have hi_ne : i ≠ n := by omega
            exact (Set.disjoint_left.mp (hfd hi_ne) hxi hx_fn).elim
          have hu_succ : u (n + 1) = u n ∪ f n := by
            ext x
            simp only [u, Finset.mem_range, Set.mem_iUnion, exists_prop, Set.mem_union]
            constructor
            · rintro ⟨i, hi_lt, hxi⟩
              by_cases hni : i = n
              · right
                simpa [hni] using hxi
              · left
                exact ⟨i, by omega, hxi⟩
            · rintro (⟨i, hi_lt, hxi⟩ | hxi)
              · exact ⟨i, by omega, hxi⟩
              · exact ⟨n, by omega, hxi⟩
          have h_union_eq :
              MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p (hu_meas (n + 1))
                ((MeasureTheory.measure_lt_top G.toWeakGridSpace.measure (u (n + 1))).ne) c
                = MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p (hu_meas n)
                    ((MeasureTheory.measure_lt_top G.toWeakGridSpace.measure (u n)).ne) c
                    + MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p (hfm n)
                        ((MeasureTheory.measure_lt_top G.toWeakGridSpace.measure (f n)).ne) c := by
            simpa [hu_succ] using
              (MeasureTheory.indicatorConstLp_disjoint_union
                (μ := G.toWeakGridSpace.measure) (p := p) (s := u n) (t := f n)
                (hu_meas n) (hfm n)
                ((MeasureTheory.measure_lt_top G.toWeakGridSpace.measure (u n)).ne)
                ((MeasureTheory.measure_lt_top G.toWeakGridSpace.measure (f n)).ne)
                hdisj_union c)
          rw [h_union_eq]
          exact M.add_mem ihn (hf n c)
    -- The symmetric difference between the partial union and the full union is the tail.
    have hu_subset : ∀ n, u n ⊆ ⋃ i, f i := by
      intro n x hx
      simp only [u, Finset.mem_range, Set.mem_iUnion, exists_prop] at hx
      rcases hx with ⟨i, -, hxi⟩
      exact Set.mem_iUnion.mpr ⟨i, hxi⟩
    have hsymmDiff : ∀ n, symmDiff (u n) (⋃ i, f i) = ⋃ i ≥ n, f i := by
      intro n
      ext x
      constructor
      · intro hx
        have hx' : x ∈ ⋃ i, f i ∧ x ∉ u n := by
          rcases Set.mem_symmDiff.mp hx with hxu | hxu
          · exfalso
            exact hxu.2 (hu_subset n hxu.1)
          · exact hxu
        rcases Set.mem_iUnion.mp hx'.1 with ⟨i, hxi⟩
        by_cases hi : i < n
        · exfalso
          have hxun : x ∈ u n := by
            exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨by simpa [Finset.mem_range] using hi, hxi⟩⟩
          exact hx'.2 hxun
        · exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Nat.le_of_not_gt hi, hxi⟩⟩
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hi_ge, hxi⟩
        refine Set.mem_symmDiff.mpr ?_
        right
        constructor
        · exact Set.mem_iUnion.2 ⟨i, hxi⟩
        · intro hx_union
          simp only [u, Finset.mem_range, Set.mem_iUnion, exists_prop] at hx_union
          rcases hx_union with ⟨j, hj_lt, hxj⟩
          have hij : j ≠ i := by omega
          exact (Set.disjoint_left.mp (hfd hij) hxj hxi).elim
    -- The measures of the disjoint tails tend to zero.
    have htail_tendsto :
        Filter.Tendsto (fun n => G.toWeakGridSpace.measure (symmDiff (u n) (⋃ i, f i)))
          Filter.atTop (nhds 0) := by
      have htail_eq :
          (fun n => G.toWeakGridSpace.measure (symmDiff (u n) (⋃ i, f i))) =
            fun n => G.toWeakGridSpace.measure (⋃ i ≥ n, f i) := by
        funext n
        rw [hsymmDiff n]
      rw [htail_eq]
      exact MeasureTheory.tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
        (fun i => (hfm i).nullMeasurableSet) hfd
    -- Convergence in measure of sets gives convergence of indicator-constants in `L^p`.
    have hlimit :
        Filter.Tendsto
          (fun n => MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
            (hu_meas n) ((MeasureTheory.measure_lt_top G.toWeakGridSpace.measure (u n)).ne) c)
          Filter.atTop
          (nhds (MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
            (MeasurableSet.iUnion hfm)
            ((MeasureTheory.measure_lt_top G.toWeakGridSpace.measure (⋃ i, f i)).ne) c)) := by
      exact MeasureTheory.tendsto_indicatorConstLp_set
        (μ := G.toWeakGridSpace.measure) (p := p) (s := ⋃ i, f i)
        (hs := MeasurableSet.iUnion hfm)
        (hμs := (MeasureTheory.measure_lt_top G.toWeakGridSpace.measure (⋃ i, f i)).ne)
        (ht := hu_meas)
        (hμt := fun n => (MeasureTheory.measure_lt_top G.toWeakGridSpace.measure (u n)).ne)
        hp_top htail_tendsto
    exact (Submodule.isClosed_topologicalClosure S).mem_of_tendsto
      hlimit (Filter.Eventually.of_forall hu_mem)
  have hC : C t ht := by
    refine MeasurableSpace.induction_on_inter
      (grid_generates_eq_generateFrom_gridGeneratingSets G)
      (isPiSystem_gridGeneratingSets G) hempty hbasic hcompl hiUnion t ht
  simpa [M] using hC c

/--
The Souza Besov space is dense in the ambient strong `L^p` topology.

The proof uses `MeasureTheory.Lp.induction`: it is enough to show that
indicator-constant vectors lie in the closure, that the closure is stable under
addition, and that it is closed. The previous theorem supplies the indicator
step.
-/
theorem souzaBesovSpace_dense
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    Dense (SouzaBesovSpace G s p q hs hp hp_top :
      Set (MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure)) := by
  classical
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  intro f _
  let S : Submodule ℂ (MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) :=
    SouzaBesovSpace G s p q hs hp hp_top
  let M : Submodule ℂ (MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) :=
    S.topologicalClosure
  refine MeasureTheory.Lp.induction (μ := G.toWeakGridSpace.measure) (p := p) hp_top
    (motive := fun g => g ∈ M) ?_ ?_ ?_ f
  · intro c t ht hμt
    exact indicatorConstLp_mem_souzaBesov_closure G s p q hs hp hp_top ht hμt.ne c
  · intro f g hf hg _ hfM hgM
    exact M.add_mem hfM hgM
  · exact Submodule.isClosed_topologicalClosure S

/--
The finite-measure inclusion `L^p → L^1` preserves indicator-constant vectors.

Both sides are represented by the same measurable function
`t.indicator (fun _ => c)`; only the ambient `Lp` exponent changes.
-/
lemma lpInclusion_indicatorConstLp_L1
    (G : GoodGridSpace (α := α))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {t : Set α} (ht : MeasurableSet t)
    (hμt : G.toWeakGridSpace.measure t ≠ ∞) (c : ℂ) :
    WeakGridSpace.LpGridRepresentation.lpInclusion
        (G := G.toWeakGridSpace) (p := 1) (t := p)
        ENNReal.one_ne_top hp_top hp
        (MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p ht hμt c)
      =
    MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) 1 ht hμt c := by
  haveI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  apply MeasureTheory.Lp.ext
  refine (WeakGridSpace.LpGridRepresentation.coeFn_lpInclusion
    (G := G.toWeakGridSpace) (p := 1) (t := p)
    ENNReal.one_ne_top hp_top hp
    (MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p ht hμt c)).trans ?_
  exact (MeasureTheory.indicatorConstLp_coeFn (μ := G.toWeakGridSpace.measure)
    (p := p) (hs := ht) (hμs := hμt) (c := c)).trans
      (MeasureTheory.indicatorConstLp_coeFn (μ := G.toWeakGridSpace.measure)
        (p := 1) (hs := ht) (hμs := hμt) (c := c)).symm

/--
The Souza Besov space built inside `L^p` is dense after viewing it in the
ambient strong `L^1` topology.

The dense subset of `L^1` is the image of `SouzaBesovSpace G s p q` under the
canonical inclusion `L^p → L^1`. The proof repeats the final `Lp.induction`
argument in `L^1`: indicator constants are in the closure because their
`L^p` representatives lie in the closed Souza Besov space and the inclusion is
continuous.
-/
theorem souzaBesovSpace_dense_inL1
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    Dense
      ((WeakGridSpace.LpGridRepresentation.lpInclusion
          (G := G.toWeakGridSpace) (p := 1) (t := p)
          ENNReal.one_ne_top hp_top hp) ''
        (SouzaBesovSpace G s p q hs hp hp_top :
          Set (MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure))) := by
  classical
  haveI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  let I :=
    WeakGridSpace.LpGridRepresentation.lpInclusion
      (G := G.toWeakGridSpace) (p := 1) (t := p)
      ENNReal.one_ne_top hp_top hp
  let S : Submodule ℂ (MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure) :=
    SouzaBesovSpace G s p q hs hp hp_top
  let T : Submodule ℂ (MeasureTheory.Lp ℂ 1 G.toWeakGridSpace.measure) :=
    S.map (I : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure →ₗ[ℂ]
      MeasureTheory.Lp ℂ 1 G.toWeakGridSpace.measure)
  have hT_dense : Dense (T : Set (MeasureTheory.Lp ℂ 1 G.toWeakGridSpace.measure)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    apply top_unique
    intro f _
    let M : Submodule ℂ (MeasureTheory.Lp ℂ 1 G.toWeakGridSpace.measure) :=
      T.topologicalClosure
    refine MeasureTheory.Lp.induction (μ := G.toWeakGridSpace.measure) (p := 1)
      ENNReal.one_ne_top (motive := fun g => g ∈ M) ?_ ?_ ?_ f
    · intro c t ht hμt
      have hind_p :
          MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p ht hμt.ne c ∈
            S.topologicalClosure := by
        exact indicatorConstLp_mem_souzaBesov_closure G s p q hs hp hp_top ht hμt.ne c
      have hI_mem :
          I (MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p ht hμt.ne c) ∈
            M := by
        change
          I (MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p ht hμt.ne c) ∈
            (S.map (I : MeasureTheory.Lp ℂ p G.toWeakGridSpace.measure →ₗ[ℂ]
              MeasureTheory.Lp ℂ 1 G.toWeakGridSpace.measure)).topologicalClosure
        exact (S.topologicalClosure_map I)
          (Submodule.mem_map.mpr
            ⟨MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p ht hμt.ne c,
              hind_p, rfl⟩)
      rwa [lpInclusion_indicatorConstLp_L1 G p hp hp_top ht hμt.ne c] at hI_mem
    · intro f g hf hg _ hfM hgM
      exact M.add_mem hfM hgM
    · exact Submodule.isClosed_topologicalClosure T
  simpa [I, S, T, Submodule.map_coe] using hT_dense

end

end GoodGridSpace
