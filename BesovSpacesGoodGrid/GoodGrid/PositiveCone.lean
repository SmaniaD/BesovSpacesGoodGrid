import BesovSpacesGoodGrid.GoodGrid.BesovSpace
import BesovSpacesGoodGrid.WeakGrid.Multipliers

/-!
# Positive cone for Souza-Besov spaces

This file defines the positive cone associated with the Souza-atom Besov space.

A Besov element is positive when it has a Besov representation whose atoms are
the canonical Souza atoms and whose coefficients are nonnegative real numbers.
The positive gauge is the infimum of the usual coefficient costs over such
positive representations.
-/

open scoped ENNReal Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
Turn a weak-grid level cell of `G.toWeakGridSpace` back into the corresponding
good-grid cell.
-/
def goodGridCellOfLevelCell (G : GoodGridSpace (α := α)) {k : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : GoodGridCell G where
  level := k
  cell := Q.1
  mem := Q.2

/--
A level block is positive when every coefficient is a nonnegative real number
and every chosen atom is the canonical Souza atom on the same cell.
-/
def SouzaPositiveLevelBlock
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) : Prop :=
  ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    ∃ c : ℝ,
      0 ≤ c ∧
        B.coeff Q = (c : ℂ) ∧
        (souzaAtomFamily G s p hs hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q) =
          canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q)

/-- A Besov representation is positive when all of its level blocks are positive. -/
def SouzaPositiveRepresentation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) f) : Prop :=
  ∀ k, SouzaPositiveLevelBlock G s p hs hp hp_top (R.block k)

/--
The positive cone in the Souza-Besov space.  An element belongs to the cone
when it admits at least one positive Souza representation.
-/
def SouzaPositiveElement
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q) : Prop :=
  ∃ R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (f : Lp ℂ p G.toWeakGridSpace.measure),
    SouzaPositiveRepresentation G s p hs hp hp_top R

/--
Concrete function version of positivity: the function is represented almost
everywhere by a positive Besov element.
-/
def SouzaPositiveFunction
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (f : α → ℂ) : Prop :=
  ∃ g : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q,
    WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) f
        (g  : Lp ℂ p G.toWeakGridSpace.measure) ∧
      SouzaPositiveElement G s p q hs hp hp_top g

/--
Candidate upper bounds for the positive gauge.  Only finite-cost positive
representations are allowed in the infimum.
-/
def souzaPositiveCostUpperSet
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q) : Set ℝ≥0∞ :=
  { C | ∃ R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (f : Lp ℂ p G.toWeakGridSpace.measure),
      SouzaPositiveRepresentation G s p hs hp hp_top R ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
        WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R ≤ C }

/--
The positive Besov gauge: the infimum of the usual coefficient cost over all
positive Souza representations of the element.  It takes values in `ℝ≥0∞`,
so the ambient nonnegativity and possible infinite value are part of the type.
-/
noncomputable def souzaPositiveNorm
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q) : ℝ≥0∞ :=
  sInf (souzaPositiveCostUpperSet G s p q hs hp hp_top f)

/--
A quantitative positive bound for the level-tail Souza `selfs` tests.

This is the positive-cone analogue of `SouzaPointwiseSelfsTailBound`: for every
canonical Souza atom on a cell of level at least `t`, the product with `m` has
a positive Besov representative whose positive gauge is at most `C`.
-/
def SouzaPositivePointwiseSelfsTailBound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (t : ℕ) (m : α → ℂ) (C : ℝ≥0∞) : Prop :=
  ∀ Q : GoodGridCell G,
      t ≤ Q.level →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun x => m x * canonicalSouzaAtom G s p Q x)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          SouzaPositiveElement G s p q hs hp hp_top y ∧
          souzaPositiveNorm G s p q hs hp hp_top y ≤ C

/-- The set of all positive level-tail `selfs` bounds. -/
def souzaPositivePointwiseSelfsTailBoundSet
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (t : ℕ) (m : α → ℂ) : Set ℝ≥0∞ :=
  { C | SouzaPositivePointwiseSelfsTailBound G s p q hs hp hp_top t m C }

/--
The positive level-tail Souza `selfs` seminorm.

Mathematically this is the supremum of the positive Besov gauge of `m a_Q`
over canonical Souza atoms whose cells have level at least `t`.
-/
noncomputable def souzaPositivePointwiseSelfsTailNorm
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (t : ℕ) (m : α → ℂ) : ℝ≥0∞ :=
  sInf (souzaPositivePointwiseSelfsTailBoundSet G s p q hs hp hp_top t m)

private theorem souzaPositiveLevelBlock_smul_nonneg
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {k : ℕ} {a : ℝ} (ha : 0 ≤ a)
    {B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k}
    (hB : SouzaPositiveLevelBlock G s p hs hp hp_top B) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (WeakGridSpace.LevelBlock.smul
        (souzaAtomFamily G s p hs hp hp_top) (a : ℂ) B) := by
  intro Q
  rcases hB Q with ⟨c, hc, hcoeff, hatom⟩
  refine ⟨a * c, mul_nonneg ha hc, ?_, ?_⟩
  · simp [WeakGridSpace.LevelBlock.smul, hcoeff]
  · simpa [WeakGridSpace.LevelBlock.smul] using hatom

private noncomputable def souzaPositiveLevelBlockAdd
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {k : ℕ}
    (B C : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k where
  coeff := fun Q => B.coeff Q + C.coeff Q
  atom := B.atom
  atom_mem := B.atom_mem

private theorem souzaPositiveLevelBlockAdd_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {k : ℕ}
    {B C : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k}
    (hB : SouzaPositiveLevelBlock G s p hs hp hp_top B)
    (hC : SouzaPositiveLevelBlock G s p hs hp hp_top C) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (souzaPositiveLevelBlockAdd G s p hs hp hp_top B C) := by
  intro Q
  rcases hB Q with ⟨b, hb, hBcoeff, hBatom⟩
  rcases hC Q with ⟨c, hc, hCcoeff, _⟩
  refine ⟨b + c, add_nonneg hb hc, ?_, ?_⟩
  · simp [souzaPositiveLevelBlockAdd, hBcoeff, hCcoeff]
  · simpa [souzaPositiveLevelBlockAdd] using hBatom

private theorem souzaPositiveLevelBlockAdd_toLp
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {k : ℕ}
    {B C : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k}
    (hB : SouzaPositiveLevelBlock G s p hs hp hp_top B)
    (hC : SouzaPositiveLevelBlock G s p hs hp hp_top C) :
    (souzaPositiveLevelBlockAdd G s p hs hp hp_top B C).toLp
        (souzaAtomFamily G s p hs hp hp_top) =
      B.toLp (souzaAtomFamily G s p hs hp hp_top) +
        C.toLp (souzaAtomFamily G s p hs hp hp_top) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  unfold WeakGridSpace.LevelBlock.toLp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro Q _
  rcases hB Q with ⟨b, hb, hBcoeff, hBatom⟩
  rcases hC Q with ⟨c, hc, hCcoeff, hCatom⟩
  have hatomLp :
      MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q)) =
        MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (C.atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (C.atom Q)) := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      rw [hBatom, hCatom]
  unfold WeakGridSpace.LevelBlock.term
  simp [souzaPositiveLevelBlockAdd, A, hatomLp, add_smul]

private noncomputable def souzaPositiveRepresentationAdd
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x y : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (S : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) y)
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (hS : SouzaPositiveRepresentation G s p hs hp hp_top S) :
    WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (x + y) where
  block := fun k =>
    souzaPositiveLevelBlockAdd G s p hs hp hp_top (R.block k) (S.block k)
  hasSum := by
    simpa [souzaPositiveLevelBlockAdd_toLp G s p hs hp hp_top (hR _) (hS _)] using
      R.hasSum.add S.hasSum

private theorem souzaPositiveRepresentationAdd_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x y : Lp ℂ p G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x}
    {S : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) y}
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (hS : SouzaPositiveRepresentation G s p hs hp hp_top S) :
    SouzaPositiveRepresentation G s p hs hp hp_top
      (souzaPositiveRepresentationAdd G s p hs hp hp_top R S hR hS) := by
  intro k
  exact souzaPositiveLevelBlockAdd_positive G s p hs hp hp_top (hR k) (hS k)

private theorem pqCost_le_of_pqCostENNReal_le
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

private theorem pqCostENNReal_le_of_finitePQCost_pqCost_le
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {A : WeakGridSpace.AtomFamily G s p u} {g : Lp ℂ p G.measure} {C : ℝ}
    (R : WeakGridSpace.LpGridRepresentation A g)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (hcost : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤ C) :
    WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R ≤ ENNReal.ofReal C := by
  by_cases hq : q = ∞
  · simp only [WeakGridSpace.LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    simp only [WeakGridSpace.LpGridRepresentation.pqCost, hq, ↓reduceIte] at hcost
    simp only [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    apply sSup_le
    rintro x ⟨k, rfl⟩
    exact ENNReal.ofReal_le_ofReal ((le_csSup hRfin ⟨k, rfl⟩).trans hcost)
  · simp only [WeakGridSpace.LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    simp only [WeakGridSpace.LpGridRepresentation.pqCost, hq, ↓reduceIte] at hcost
    simp only [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have h_nonneg : ∀ k, 0 ≤ R.levelCoeffPower k ^ (q.toReal / p.toReal) :=
      fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
    rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg hRfin,
        ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg h_nonneg)
          (div_nonneg zero_le_one hq_pos.le)]
    exact ENNReal.ofReal_le_ofReal hcost

private theorem souzaPositiveRepresentationAdd_levelCoeffPower
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x y : Lp ℂ p G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x}
    {S : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) y}
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (hS : SouzaPositiveRepresentation G s p hs hp hp_top S) (k : ℕ) :
    (souzaPositiveRepresentationAdd G s p hs hp hp_top R S hR hS).levelCoeffPower k =
      (WeakGridSpace.LpGridRepresentation.add R S).levelCoeffPower k := by
  unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
  apply Finset.sum_congr rfl
  intro Q _
  rcases hR k Q with ⟨b, hb, hBcoeff, _⟩
  rcases hS k Q with ⟨c, hc, hCcoeff, _⟩
  simp [souzaPositiveRepresentationAdd, souzaPositiveLevelBlockAdd,
    WeakGridSpace.LpGridRepresentation.add, WeakGridSpace.LevelBlock.add, hBcoeff, hCcoeff,
    Complex.norm_real, Real.norm_of_nonneg hb, Real.norm_of_nonneg hc]

private theorem souzaPositiveRepresentationAdd_finitePQCost
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {x y : Lp ℂ p G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x}
    {S : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) y}
    (hRpos : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (hSpos : SouzaPositiveRepresentation G s p hs hp hp_top S)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (hSfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S) :
    WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
      (souzaPositiveRepresentationAdd G s p hs hp hp_top R S hRpos hSpos) := by
  have haddfin :
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
        (WeakGridSpace.LpGridRepresentation.add R S) :=
    WeakGridSpace.LpGridRepresentation.add_finitePQCost R S hp_top
      (Fact.out : 1 ≤ q) hRfin hSfin
  by_cases hq : q = ∞
  · simp only [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at haddfin ⊢
    convert haddfin using 2
    ext k
    rw [souzaPositiveRepresentationAdd_levelCoeffPower G s p hs hp hp_top hRpos hSpos k]
  · simp only [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at haddfin ⊢
    refine haddfin.congr ?_
    intro k
    rw [souzaPositiveRepresentationAdd_levelCoeffPower G s p hs hp hp_top hRpos hSpos k]

private theorem souzaPositiveRepresentationAdd_pqCost_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {x y : Lp ℂ p G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x}
    {S : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) y}
    (hRpos : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (hSpos : SouzaPositiveRepresentation G s p hs hp hp_top S)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (hSfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S) :
    WeakGridSpace.LpGridRepresentation.pqCost (q := q)
        (souzaPositiveRepresentationAdd G s p hs hp hp_top R S hRpos hSpos) ≤
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R +
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S := by
  have hadd :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q)
          (WeakGridSpace.LpGridRepresentation.add R S) ≤
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R +
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) S :=
    WeakGridSpace.LpGridRepresentation.pqCost_triangle R S hp_top
      (Fact.out : 1 ≤ q) hRfin hSfin
  convert hadd using 1
  · unfold WeakGridSpace.LpGridRepresentation.pqCost
    split_ifs <;> congr 1
    · ext C
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, congrArg (fun t => t ^ (1 / p.toReal))
          (souzaPositiveRepresentationAdd_levelCoeffPower
            G s p hs hp hp_top hRpos hSpos k).symm⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, congrArg (fun t => t ^ (1 / p.toReal))
          (souzaPositiveRepresentationAdd_levelCoeffPower
            G s p hs hp hp_top hRpos hSpos k)⟩
    · apply tsum_congr
      intro k
      rw [souzaPositiveRepresentationAdd_levelCoeffPower G s p hs hp hp_top hRpos hSpos k]

private theorem souzaPositiveCostUpperSet_add_mem
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {x y : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q}
    {C D : ℝ≥0∞}
    (hC : C ∈ souzaPositiveCostUpperSet G s p q hs hp hp_top x)
    (hD : D ∈ souzaPositiveCostUpperSet G s p q hs hp hp_top y) :
    C + D ∈ souzaPositiveCostUpperSet G s p q hs hp hp_top (x + y) := by
  rcases hC with ⟨R, hRpos, hRfin, hRcost⟩
  rcases hD with ⟨S, hSpos, hSfin, hScost⟩
  let T := souzaPositiveRepresentationAdd G s p hs hp hp_top R S hRpos hSpos
  have hTpos : SouzaPositiveRepresentation G s p hs hp hp_top T :=
    souzaPositiveRepresentationAdd_positive G s p hs hp hp_top hRpos hSpos
  have hTfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) T :=
    souzaPositiveRepresentationAdd_finitePQCost G s p q hs hp hp_top
      hRpos hSpos hRfin hSfin
  refine ⟨T, hTpos, hTfin, ?_⟩
  by_cases hCtop : C = ∞
  · simp [hCtop]
  by_cases hDtop : D = ∞
  · simp [hDtop]
  have hC_eq : ENNReal.ofReal C.toReal = C := ENNReal.ofReal_toReal hCtop
  have hD_eq : ENNReal.ofReal D.toReal = D := ENNReal.ofReal_toReal hDtop
  have hRcost_real :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤ C.toReal :=
    pqCost_le_of_pqCostENNReal_le
      (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
      (A := souzaAtomFamily G s p hs hp hp_top) R
      (by simpa [hC_eq] using hRcost)
      ENNReal.toReal_nonneg
  have hScost_real :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤ D.toReal :=
    pqCost_le_of_pqCostENNReal_le
      (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
      (A := souzaAtomFamily G s p hs hp hp_top) S
      (by simpa [hD_eq] using hScost)
      ENNReal.toReal_nonneg
  have hTcost_real :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) T ≤ C.toReal + D.toReal :=
    (souzaPositiveRepresentationAdd_pqCost_le G s p q hs hp hp_top
      hRpos hSpos hRfin hSfin).trans (add_le_add hRcost_real hScost_real)
  have hTcost_enn :
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) T ≤
        ENNReal.ofReal (C.toReal + D.toReal) :=
    pqCostENNReal_le_of_finitePQCost_pqCost_le
      (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
      (A := souzaAtomFamily G s p hs hp hp_top) T hTfin hTcost_real
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg, hC_eq, hD_eq] at hTcost_enn
  exact hTcost_enn

private noncomputable def souzaPositiveZeroLevelBlock
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ} :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k where
  coeff := fun _ => 0
  atom := fun Q =>
    (((G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)
  atom_mem := fun Q => by
    have hnonneg :
        0 ≤ (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    change ‖(((G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)‖ ≤
      (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹)
    simpa [Complex.norm_real, Real.norm_of_nonneg hnonneg]

private theorem souzaPositiveZeroLevelBlock_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ} :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (souzaPositiveZeroLevelBlock G s p hs hp hp_top (k := k)) := by
  intro Q
  refine ⟨0, le_rfl, rfl, ?_⟩
  funext x
  by_cases hx : x ∈ Q.1
  · dsimp [WeakGridSpace.AtomFamily.toFunction, souzaPositiveZeroLevelBlock,
      souzaAtomFamily, souzaLocalVectorSpace, canonicalSouzaAtom,
      goodGridCellOfLevelCell, WeakGridSpace.levelCellToWeakGridCell]
    simp [hx]
  · dsimp [WeakGridSpace.AtomFamily.toFunction, souzaPositiveZeroLevelBlock,
      souzaAtomFamily, souzaLocalVectorSpace, canonicalSouzaAtom,
      goodGridCellOfLevelCell, WeakGridSpace.levelCellToWeakGridCell]
    simp [hx]

private theorem souzaPositiveZeroLevelBlock_toLp
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] {k : ℕ} :
    (souzaPositiveZeroLevelBlock G s p hs hp hp_top (k := k)).toLp
        (souzaAtomFamily G s p hs hp hp_top) = 0 := by
  simp [WeakGridSpace.LevelBlock.toLp, WeakGridSpace.LevelBlock.term,
    souzaPositiveZeroLevelBlock]

private noncomputable def souzaPositiveZeroRepresentation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] :
    WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (0 : Lp ℂ p G.toWeakGridSpace.measure) where
  block := fun k => souzaPositiveZeroLevelBlock G s p hs hp hp_top (k := k)
  hasSum := by
    simpa [souzaPositiveZeroLevelBlock_toLp G s p hs hp hp_top] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : Lp ℂ p G.toWeakGridSpace.measure)) 0)

private theorem souzaPositiveZeroRepresentation_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] :
    SouzaPositiveRepresentation G s p hs hp hp_top
      (souzaPositiveZeroRepresentation G s p hs hp hp_top) := by
  intro k
  exact souzaPositiveZeroLevelBlock_positive G s p hs hp hp_top

private theorem souzaPositiveZeroRepresentation_levelCoeffPower
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] (k : ℕ) :
    (souzaPositiveZeroRepresentation G s p hs hp hp_top).levelCoeffPower k = 0 := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le hp).ne' hp_top
  simp [souzaPositiveZeroRepresentation, souzaPositiveZeroLevelBlock,
    WeakGridSpace.LpGridRepresentation.levelCoeffPower, Real.zero_rpow hp_pos.ne']

private theorem souzaPositiveZeroRepresentation_finitePQCost
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
      (souzaPositiveZeroRepresentation G s p hs hp hp_top) := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le hp).ne' hp_top
  by_cases hq : q = ∞
  · simp only [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, ↓reduceIte]
    refine ⟨0, ?_⟩
    rintro x ⟨k, rfl⟩
    have hinv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
    simp [souzaPositiveZeroRepresentation_levelCoeffPower G s p hs hp hp_top k,
      Real.zero_rpow hinv_pos.ne']
  · simp only [WeakGridSpace.LpGridRepresentation.FinitePQCost, hq, ↓reduceIte]
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have hpow_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
    simpa [souzaPositiveZeroRepresentation_levelCoeffPower G s p hs hp hp_top,
      Real.zero_rpow hpow_pos.ne'] using (summable_zero : Summable fun _ : ℕ => (0 : ℝ))

private theorem souzaPositiveZeroRepresentation_pqCostENNReal_zero
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q)
        (souzaPositiveZeroRepresentation G s p hs hp hp_top) = 0 := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le hp).ne' hp_top
  by_cases hq : q = ∞
  · simp only [WeakGridSpace.LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    apply le_antisymm
    · apply sSup_le
      rintro x ⟨k, rfl⟩
      have hinv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
      simp [souzaPositiveZeroRepresentation_levelCoeffPower G s p hs hp hp_top k,
        Real.zero_rpow hinv_pos.ne']
    · exact bot_le
  · simp only [WeakGridSpace.LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have hpow_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
    have hsum :
        (∑' k, ENNReal.ofReal
          (((souzaPositiveZeroRepresentation G s p hs hp hp_top).levelCoeffPower k) ^
            (q.toReal / p.toReal))) = 0 := by
      simp [souzaPositiveZeroRepresentation_levelCoeffPower G s p hs hp hp_top,
        Real.zero_rpow hpow_pos.ne']
    rw [hsum]
    exact ENNReal.zero_rpow_of_pos (one_div_pos.mpr hq_pos)

private theorem zero_mem_souzaPositiveCostUpperSet
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    (0 : ℝ≥0∞) ∈
      souzaPositiveCostUpperSet G s p q hs hp hp_top
        (0 : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q) := by
  refine ⟨souzaPositiveZeroRepresentation G s p hs hp hp_top,
    souzaPositiveZeroRepresentation_positive G s p hs hp hp_top,
    souzaPositiveZeroRepresentation_finitePQCost G s p q hs hp hp_top, ?_⟩
  simp [souzaPositiveZeroRepresentation_pqCostENNReal_zero G s p q hs hp hp_top]

private theorem souzaPositiveNorm_zero
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    souzaPositiveNorm G s p q hs hp hp_top
        (0 : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q) = 0 := by
  apply bot_unique
  unfold souzaPositiveNorm
  exact sInf_le (zero_mem_souzaPositiveCostUpperSet G s p q hs hp hp_top)

private theorem souzaPositiveCostUpperSet_smul_mem
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {a : ℝ} (ha : 0 ≤ a)
    {x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q}
    {C : ℝ≥0∞}
    (hC : C ∈ souzaPositiveCostUpperSet G s p q hs hp hp_top x) :
    ENNReal.ofReal a * C ∈
      souzaPositiveCostUpperSet G s p q hs hp hp_top ((a : ℂ) • x) := by
  rcases hC with ⟨R, hRpos, hRfin, hRcost⟩
  let T := WeakGridSpace.LpGridRepresentation.smul
    (A := souzaAtomFamily G s p hs hp hp_top) (a : ℂ) R
  have hTpos : SouzaPositiveRepresentation G s p hs hp hp_top T := by
    intro k
    exact souzaPositiveLevelBlock_smul_nonneg G s p hs hp hp_top ha (hRpos k)
  have hTfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) T :=
    WeakGridSpace.LpGridRepresentation.smul_finitePQCost
      (A := souzaAtomFamily G s p hs hp hp_top) (q := q) (a : ℂ) hRfin
  refine ⟨T, hTpos, hTfin, ?_⟩
  by_cases ha_zero : a = 0
  · subst ha_zero
    have hTcost_real :
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) T ≤ 0 := by
      dsimp [T]
      rw [WeakGridSpace.LpGridRepresentation.pqCost_smul
        (A := souzaAtomFamily G s p hs hp hp_top) (q := q)
        (0 : ℂ) R hp_top (Fact.out : 1 ≤ q) hRfin]
      simp [WeakGridSpace.LpGridRepresentation.pqCost_nonneg]
    have hTcost :
        WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) T ≤
          ENNReal.ofReal (0 : ℝ) :=
      pqCostENNReal_le_of_finitePQCost_pqCost_le
        (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
        (A := souzaAtomFamily G s p hs hp hp_top) T hTfin hTcost_real
    simpa using hTcost
  · have ha_pos : 0 < a := lt_of_le_of_ne' ha ha_zero
    by_cases hCtop : C = ∞
    · simp [hCtop, ENNReal.ofReal_ne_zero_iff.mpr ha_pos]
    have hC_eq : ENNReal.ofReal C.toReal = C := ENNReal.ofReal_toReal hCtop
    have hRcost_real :
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤ C.toReal :=
      pqCost_le_of_pqCostENNReal_le
        (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
        (A := souzaAtomFamily G s p hs hp hp_top) R
        (by simpa [hC_eq] using hRcost)
        ENNReal.toReal_nonneg
    have hTcost_real :
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) T ≤ a * C.toReal := by
      rw [WeakGridSpace.LpGridRepresentation.pqCost_smul
        (A := souzaAtomFamily G s p hs hp hp_top) (q := q)
        (a : ℂ) R hp_top (Fact.out : 1 ≤ q) hRfin]
      rw [Complex.norm_real, Real.norm_of_nonneg ha]
      exact mul_le_mul_of_nonneg_left hRcost_real ha
    have hTcost :
        WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) T ≤
          ENNReal.ofReal (a * C.toReal) :=
      pqCostENNReal_le_of_finitePQCost_pqCost_le
        (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
        (A := souzaAtomFamily G s p hs hp hp_top) T hTfin hTcost_real
    rw [ENNReal.ofReal_mul ha, hC_eq] at hTcost
    exact hTcost

private noncomputable def souzaCanonicalLocalAtom
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G) : ℂ :=
  ((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) : ℝ)

private theorem souzaCanonicalLocalAtom_nonneg
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G) :
    0 ≤ (souzaCanonicalLocalAtom G s p Q).re := by
  simp [souzaCanonicalLocalAtom, Real.rpow_nonneg ENNReal.toReal_nonneg]

private theorem souzaCanonicalLocalAtom_norm
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G) :
    ‖souzaCanonicalLocalAtom G s p Q‖ =
      (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) := by
  have hnonneg :
      0 ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  simp [souzaCanonicalLocalAtom, Complex.norm_real, Real.norm_of_nonneg hnonneg]

private theorem souzaCanonicalLocalAtom_pos
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : GoodGridCell G) :
    0 < (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) := by
  have hQpos : 0 < G.grid.μ Q.cell := GoodGridCell.measure_pos Q
  have hQfinite : G.grid.μ Q.cell ≠ ∞ := GoodGridCell.measure_ne_top Q
  exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hQpos.ne' hQfinite) _

private theorem souzaCanonicalLocalAtom_mem
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (Q : WeakGridSpace.WeakGridCell G.toWeakGridSpace) :
    souzaCanonicalLocalAtom G s p ⟨Q.level, Q.cell, Q.mem⟩ ∈
      (souzaAtomFamily G s p hs hp hp_top).atoms Q := by
  change ‖souzaCanonicalLocalAtom G s p ⟨Q.level, Q.cell, Q.mem⟩‖ ≤
    (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)
  rw [souzaCanonicalLocalAtom_norm]

private theorem souzaCanonicalLocalAtom_toFunction
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (Q : WeakGridSpace.WeakGridCell G.toWeakGridSpace) :
    (souzaAtomFamily G s p hs hp hp_top).toFunction Q
        (souzaCanonicalLocalAtom G s p ⟨Q.level, Q.cell, Q.mem⟩) =
      canonicalSouzaAtom G s p ⟨Q.level, Q.cell, Q.mem⟩ := by
  funext x
  by_cases hx : x ∈ Q.cell
  · change Q.cell.indicator
        (fun _ => souzaCanonicalLocalAtom G s p ⟨Q.level, Q.cell, Q.mem⟩) x =
      canonicalSouzaAtom G s p ⟨Q.level, Q.cell, Q.mem⟩ x
    simp [canonicalSouzaAtom, souzaCanonicalLocalAtom, hx]
  · change Q.cell.indicator
        (fun _ => souzaCanonicalLocalAtom G s p ⟨Q.level, Q.cell, Q.mem⟩) x =
      canonicalSouzaAtom G s p ⟨Q.level, Q.cell, Q.mem⟩ x
    simp [canonicalSouzaAtom, souzaCanonicalLocalAtom, hx]

/-- The positive elements form a cone under multiplication by nonnegative scalars. -/
theorem souzaPositiveElement_smul_nonneg
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {a : ℝ}
    (ha : 0 ≤ a)
    {x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q}
    (hx : SouzaPositiveElement G s p q hs hp hp_top x) :
    SouzaPositiveElement G s p q hs hp hp_top ((a : ℂ) • x) := by
  rcases hx with ⟨R, hR⟩
  refine ⟨WeakGridSpace.LpGridRepresentation.smul (A := souzaAtomFamily G s p hs hp hp_top)
      (a : ℂ) R, ?_⟩
  intro k
  exact souzaPositiveLevelBlock_smul_nonneg G s p hs hp hp_top ha (hR k)

/-- The positive elements are closed under addition. -/
theorem souzaPositiveElement_add
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {x y : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q}
    (hx : SouzaPositiveElement G s p q hs hp hp_top x)
    (hy : SouzaPositiveElement G s p q hs hp hp_top y) :
    SouzaPositiveElement G s p q hs hp hp_top (x + y) := by
  rcases hx with ⟨R, hR⟩
  rcases hy with ⟨S, hS⟩
  refine ⟨?_, ?_⟩
  · simpa using
      (souzaPositiveRepresentationAdd G s p hs hp hp_top R S hR hS)
  · exact souzaPositiveRepresentationAdd_positive G s p hs hp hp_top hR hS

/-- The positive gauge is homogeneous for nonnegative scalar multiplication. -/
theorem souzaPositiveNorm_smul_nonneg
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {a : ℝ} (ha : 0 ≤ a)
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q) :
    souzaPositiveNorm G s p q hs hp hp_top ((a : ℂ) • x) =
      ENNReal.ofReal a * souzaPositiveNorm G s p q hs hp hp_top x := by
  by_cases ha_zero : a = 0
  · subst ha_zero
    simp [souzaPositiveNorm_zero G s p q hs hp hp_top]
  have ha_pos : 0 < a := lt_of_le_of_ne' ha ha_zero
  let A : ℝ≥0∞ := ENNReal.ofReal a
  have hA_ne_zero : A ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr ha_pos
  have hA_ne_top : A ≠ ∞ := ENNReal.ofReal_ne_top
  apply le_antisymm
  · unfold souzaPositiveNorm
    let Ux := souzaPositiveCostUpperSet G s p q hs hp hp_top x
    let Uax := souzaPositiveCostUpperSet G s p q hs hp hp_top ((a : ℂ) • x)
    change sInf Uax ≤ A * sInf Ux
    by_cases hUx : Ux.Nonempty
    · rw [show sInf Ux = ⨅ C : Ux, C.1 by rw [sInf_eq_iInf, iInf_subtype],
        ENNReal.mul_iInf_of_ne hA_ne_zero hA_ne_top]
      exact le_iInf fun C =>
        sInf_le (by
          exact souzaPositiveCostUpperSet_smul_mem G s p q hs hp hp_top ha
            (by simpa [Ux] using C.2))
    · have hUx_top : sInf Ux = ∞ := by
        apply top_unique
        refine le_sInf ?_
        intro C hC
        exact False.elim (hUx ⟨C, hC⟩)
      rw [hUx_top, ENNReal.mul_top hA_ne_zero]
      exact le_top
  · unfold souzaPositiveNorm
    let Ux := souzaPositiveCostUpperSet G s p q hs hp hp_top x
    let Uax := souzaPositiveCostUpperSet G s p q hs hp hp_top ((a : ℂ) • x)
    change A * sInf Ux ≤ sInf Uax
    refine le_sInf ?_
    intro D hD
    have hinv_nonneg : 0 ≤ a⁻¹ := inv_nonneg.mpr ha
    have hback :
        ENNReal.ofReal a⁻¹ * D ∈
          souzaPositiveCostUpperSet G s p q hs hp hp_top
            (((a⁻¹ : ℝ) : ℂ) • ((a : ℂ) • x)) :=
      souzaPositiveCostUpperSet_smul_mem G s p q hs hp hp_top hinv_nonneg
        (by simpa [Uax] using hD)
    have hbackx : ENNReal.ofReal a⁻¹ * D ∈ Ux := by
      change ENNReal.ofReal a⁻¹ * D ∈
        souzaPositiveCostUpperSet G s p q hs hp hp_top x
      convert hback using 1
      congr 1
      symm
      rw [smul_smul]
      have hscalar : (((a⁻¹ : ℝ) : ℂ) * (a : ℂ)) = 1 := by
        exact_mod_cast inv_mul_cancel₀ ha_pos.ne'
      rw [hscalar, one_smul]
    have hnorm_le : sInf Ux ≤ ENNReal.ofReal a⁻¹ * D := sInf_le hbackx
    have hAinv : A * ENNReal.ofReal a⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul ha]
      simp [A, mul_inv_cancel₀ ha_pos.ne']
    calc
      A * sInf Ux ≤ A * (ENNReal.ofReal a⁻¹ * D) :=
        mul_le_mul_left' hnorm_le A
      _ = D := by
        rw [← mul_assoc, hAinv, one_mul]

/-- The positive gauge satisfies the triangle inequality on the cone. -/
theorem souzaPositiveNorm_add_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {x y : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q}
    (hx : SouzaPositiveElement G s p q hs hp hp_top x)
    (hy : SouzaPositiveElement G s p q hs hp hp_top y) :
    souzaPositiveNorm G s p q hs hp hp_top (x + y) ≤
      souzaPositiveNorm G s p q hs hp hp_top x +
        souzaPositiveNorm G s p q hs hp hp_top y := by
  let Ux := souzaPositiveCostUpperSet G s p q hs hp hp_top x
  let Uy := souzaPositiveCostUpperSet G s p q hs hp hp_top y
  let Uxy := souzaPositiveCostUpperSet G s p q hs hp hp_top (x + y)
  change sInf Uxy ≤ sInf Ux + sInf Uy
  by_cases hUx : Ux.Nonempty
  · by_cases hUy : Uy.Nonempty
    · rw [show sInf Ux = ⨅ C : Ux, C.1 by rw [sInf_eq_iInf, iInf_subtype],
        show sInf Uy = ⨅ D : Uy, D.1 by rw [sInf_eq_iInf, iInf_subtype]]
      exact ENNReal.le_iInf_add_iInf
        (f := fun C : Ux => C.1) (g := fun D : Uy => D.1)
        (fun C D =>
          sInf_le (by
            exact souzaPositiveCostUpperSet_add_mem G s p q hs hp hp_top
              (by simpa [Ux] using C.2) (by simpa [Uy] using D.2)))
    · have hUy_top : sInf Uy = ∞ := by
        apply top_unique
        refine le_sInf ?_
        intro D hD
        exact False.elim (hUy ⟨D, hD⟩)
      rw [hUy_top]
      simp
  · have hUx_top : sInf Ux = ∞ := by
      apply top_unique
      refine le_sInf ?_
      intro C hC
      exact False.elim (hUx ⟨C, hC⟩)
    rw [hUx_top]
    simp

/-- The usual Besov gauge is bounded by the positive gauge. -/
theorem souzaBesovNorm_le_souzaPositiveNorm
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q) :
    ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s p hs hp hp_top) q f) ≤
      souzaPositiveNorm G s p q hs hp hp_top f := by
  unfold souzaPositiveNorm
  refine le_sInf ?_
  intro C hC
  by_cases hCtop : C = ∞
  · simp [hCtop]
  rcases hC with ⟨R, _hRpos, hRfin, hRcost⟩
  have hC_eq : ENNReal.ofReal C.toReal = C := ENNReal.ofReal_toReal hCtop
  have hRcost_real :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤ C.toReal :=
    pqCost_le_of_pqCostENNReal_le
      (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
      (A := souzaAtomFamily G s p hs hp hp_top) R
      (by simpa [hC_eq] using hRcost)
      ENNReal.toReal_nonneg
  have hnorm_real :
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs hp hp_top) q f ≤ C.toReal :=
    (WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
      (A := souzaAtomFamily G s p hs hp hp_top) (q := q) (g := f) R hRfin).trans
      hRcost_real
  rw [← hC_eq]
  exact ENNReal.ofReal_le_ofReal hnorm_real

/--
A Souza-Besov element is real-valued when its `L^p` representative takes values
in the embedded real line almost everywhere.
-/
def SouzaBesovAEEqRealValued
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q) : Prop :=
  ∀ᵐ x ∂G.toWeakGridSpace.measure,
    ∃ r : ℝ, ((f : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) x = (r : ℂ)

/--
Real-valued Souza-Besov elements decompose as a difference of positive-cone
elements with no loss in the positive gauge.

If `f` is real-valued almost everywhere, then `f = u - v` in the Souza-Besov
space, where both `u` and `v` belong to the positive cone and each positive
gauge is bounded by the usual Besov gauge of `f`.
-/
theorem exists_souzaPositive_decomposition_of_aeRealValued
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (hf_real : SouzaBesovAEEqRealValued G s p q hs hp hp_top f) :
    ∃ u v : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      SouzaPositiveElement G s p q hs hp hp_top u ∧
        SouzaPositiveElement G s p q hs hp hp_top v ∧
        f = u - v ∧
        souzaPositiveNorm G s p q hs hp hp_top u ≤
          ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q f) ∧
        souzaPositiveNorm G s p q hs hp hp_top v ≤
          ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q f) := by
  sorry

/--
Complex-valued Souza-Besov elements decompose into real and imaginary
positive-cone differences with no loss in the positive gauge.

Every element of the complex Souza-Besov space can be written as
`(u - v) + i • (w - r)`, where all four pieces belong to the positive cone and
each positive gauge is bounded by the usual Besov gauge of `f`.
-/
theorem exists_souzaPositive_decomposition_of_aeComplexValued
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q) :
    ∃ u v w r : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      SouzaPositiveElement G s p q hs hp hp_top u ∧
        SouzaPositiveElement G s p q hs hp hp_top v ∧
        SouzaPositiveElement G s p q hs hp hp_top w ∧
        SouzaPositiveElement G s p q hs hp hp_top r ∧
        f = (u - v) + Complex.I • (w - r) ∧
        souzaPositiveNorm G s p q hs hp hp_top u ≤
          ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q f) ∧
        souzaPositiveNorm G s p q hs hp hp_top v ≤
          ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q f) ∧
        souzaPositiveNorm G s p q hs hp hp_top w ≤
          ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q f) ∧
        souzaPositiveNorm G s p q hs hp hp_top r ≤
          ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q f) := by
  sorry

/--
The positive cone `C_+(β)` in the ambient complex `L^β` space: these are the
classes which admit an almost everywhere nonnegative real representative.
-/
def LpNonnegativeCone
    (G : GoodGridSpace (α := α)) (β : ℝ≥0∞) :
    Set (Lp ℂ β G.toWeakGridSpace.measure) :=
  { f | ∀ᵐ x ∂G.toWeakGridSpace.measure,
      ∃ c : ℝ, 0 ≤ c ∧ (f : α → ℂ) x = (c : ℂ) }

/--
The Souza-Besov positive cone, viewed as a subset of the ambient `L^β` space.
-/
def SouzaPositiveConeInLbeta
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    Set (Lp ℂ p G.toWeakGridSpace.measure) :=
  { fp | ∃ f : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      SouzaPositiveElement G s p q hs hp hp_top f ∧
        (f : Lp ℂ p G.toWeakGridSpace.measure) = fp }

/--
The positive cone of the Souza-Besov space is strongly dense in the
nonnegative cone of the ambient `L^β` space.

For `1 ≤ β < ∞`, every nonnegative `L^β` function lies in the strong `L^β`
closure of the Souza-Besov positive cone.
-/
theorem souzaPositiveCone_dense_in_LpNonnegativeCone
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    LpNonnegativeCone G p ⊆
      closure (SouzaPositiveConeInLbeta G s p q hs hp hp_top) := by
  sorry

/-- Two sets agree up to a null set when their symmetric difference is null. -/
def aeEqSet (μ : Measure α) (S T : Set α) : Prop :=
  μ ((S \ T) ∪ (T \ S)) = 0

/-- A set is, modulo null sets, a countable union of good-grid cells. -/
def IsAECountableUnionOfGoodGridCells
    (G : GoodGridSpace (α := α)) (S : Set α) : Prop :=
  ∃ cells : ℕ → GoodGridCell G,
    aeEqSet G.grid.μ S (⋃ n, (cells n).cell)

/--
The support of a positive Souza-Besov function is, modulo a null set, a
countable union of cells of the good grid.
-/
theorem support_ae_countable_iUnion_goodGridCells_of_souzaPositiveFunction
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {f : α → ℂ}
    (hf : SouzaPositiveFunction G s p q hs hp hp_top f) :
    IsAECountableUnionOfGoodGridCells G {x | f x ≠ 0} := by
  sorry

end

end GoodGridSpace
