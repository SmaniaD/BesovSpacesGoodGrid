import BesovSpacesGoodGrid.WeakGridAtomsDefinition
import BesovSpacesGoodGrid.WeakGridBesovishSpaces
import BesovSpacesGoodGrid.WeakGridCompletenessBesovishSpaces
import BesovSpacesGoodGrid.GoodGridDefinition
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
5. `souzaLocalBanachSpace`: the local Banach space `ℂ` for Souza atoms
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

/-- The `WeakGridSpace` induced by a `GoodGridSpace`. -/
def GoodGridSpace.toWeakGridSpace (G : GoodGridSpace (α := α)) :
    WeakGridSpace.WeakGridSpace (α := α) :=
  { grid := G.toWeakGrid }

/-- Every `GoodGridCell` gives a `WeakGridCell` in the induced `WeakGridSpace`. -/
def GoodGridCell.toWeakGridCell {G : GoodGridSpace (α := α)} (Q : GoodGridCell G) :
    WeakGridSpace.WeakGridCell G.toWeakGridSpace :=
  { level := Q.level, cell := Q.cell, mem := Q.mem }

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
              ((ENNReal.ofReal G.grid.lambda2) ^ n * G.grid.μ Set.univ) :=
            mul_le_mul_left' hind _
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
-- §4. Local Banach space for Souza atoms
-- ============================================================

/--
The local Banach space at cell `Q` for Souza atoms is `ℂ`, with the
linear map `c ↦ (fun x => if x ∈ Q.cell then c else 0)`.
-/
def souzaLocalBanachSpace (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) :
    WeakGridSpace.LocalBanachSpace α := by
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
The set of Souza atoms at `Q`, viewed as elements `c : ℂ` of the local
Banach space: those satisfying `‖c‖ ≤ μ(Q)^(s − 1/p)`.
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
    souzaLocalBanachSpace G ⟨Q.level, Q.cell, Q.mem⟩
  atoms             := fun Q =>
    souzaAtomsSet G s p ⟨Q.level, Q.cell, Q.mem⟩
  atoms_nonempty    := fun Q =>
    ⟨0, by
      have hnonneg :
          0 ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) :=
        Real.rpow_nonneg ENNReal.toReal_nonneg _
      change ‖(0 : ℂ)‖ ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)
      simpa using hnonneg⟩
  local_memLp       := fun Q c => by
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
    simpa [souzaLocalBanachSpace, hp_top_mul, GoodGridSpace.toWeakGridSpace,
      GoodGridSpace.toWeakGrid] using
      (MeasureTheory.memLp_indicator_const (μ := G.grid.μ) (s := Q.cell)
        (p := ∞) hQmeas c (Or.inr hQfinite))
  local_support     := fun Q c x hx => by
    classical
    change (Q.cell.indicator fun _ => c) x = 0
    simp [hx]
  atoms_convex      := fun Q => by
    -- souzaAtomsSet Q is a closed ball in ℂ, hence convex
    simpa [souzaAtomsSet, Metric.closedBall, dist_eq_norm] using
      (convex_closedBall (0 : ℂ) ((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)))
  atoms_phase_invariant := fun Q c σ hc hσ => by
    simp only [souzaAtomsSet] at hc ⊢
    calc ‖σ • c‖ = ‖σ‖ * ‖c‖ := norm_smul σ c
      _ = 1 * ‖c‖             := by rw [hσ]
      _ = ‖c‖                 := one_mul _
      _ ≤ _                   := hc
  atom_bound        := fun Q c hc => by
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
-- §7. Strong compactness hypothesis A5 for Souza atoms
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
-- §8. Completeness of Souza Besov spaces with the cost norm
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

end

end GoodGridSpace
