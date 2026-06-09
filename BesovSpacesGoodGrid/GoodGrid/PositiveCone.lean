import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.StandarRepresentationNormleqBesovNorm
import BesovSpacesGoodGrid.GoodGrid.BesovSpace
import BesovSpacesGoodGrid.WeakGrid.Multipliers
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Positive cone for Souza-Besov spaces

This file defines the positive cone associated with the Souza-atom Besov space.

A Besov element is positive when it has a Besov representation whose atoms are
the canonical Souza atoms and whose coefficients are nonnegative real numbers.
The positive gauge is the infimum of the usual coefficient costs over such
positive representations.
-/

open scoped ENNReal Topology symmDiff
open MeasureTheory Filter

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
A level block is *canonical* when every chosen atom is the canonical Souza atom
on its cell.  This is the atom half of `SouzaPositiveLevelBlock`, with **no**
constraint on the coefficients (they may be arbitrary complex numbers). -/
def SouzaCanonicalLevelBlock
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) : Prop :=
  ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    (souzaAtomFamily G s p hs hp hp_top).toFunction
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
        (B.atom Q) =
      canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q)

/-- A Besov representation is *canonical* when all of its level blocks use
canonical Souza atoms.  Coefficients are unconstrained. -/
def SouzaCanonicalRepresentation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) f) : Prop :=
  ∀ k, SouzaCanonicalLevelBlock G s p hs hp hp_top (R.block k)

/-- A positive level block is exactly a canonical level block with nonnegative
real coefficients. -/
theorem souzaPositiveLevelBlock_iff_canonical_and_nonneg
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    SouzaPositiveLevelBlock G s p hs hp hp_top B ↔
      (∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ∃ c : ℝ, 0 ≤ c ∧ B.coeff Q = (c : ℂ)) ∧
      SouzaCanonicalLevelBlock G s p hs hp hp_top B := by
  constructor
  · intro h
    refine ⟨fun Q => ?_, fun Q => ?_⟩
    · obtain ⟨c, hc0, hcoeff, _⟩ := h Q
      exact ⟨c, hc0, hcoeff⟩
    · obtain ⟨_, _, _, hcan⟩ := h Q
      exact hcan
  · rintro ⟨h1, h2⟩ Q
    obtain ⟨c, hc0, hcoeff⟩ := h1 Q
    exact ⟨c, hc0, hcoeff, h2 Q⟩

/-- A positive representation is exactly a canonical representation with
nonnegative real coefficients.  This is the bridge that lets us state the
positive-cone consequences with the weaker *canonical* hypothesis on the source
and recover full positivity only when the coefficients are also nonnegative. -/
theorem souzaPositiveRepresentation_iff_canonical_and_nonneg
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) f) :
    SouzaPositiveRepresentation G s p hs hp hp_top R ↔
      (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        ∃ c : ℝ, 0 ≤ c ∧ (R.block k).coeff Q = (c : ℂ)) ∧
      SouzaCanonicalRepresentation G s p hs hp hp_top R := by
  constructor
  · intro h
    refine ⟨fun k Q => ?_, fun k => ?_⟩
    · exact ((souzaPositiveLevelBlock_iff_canonical_and_nonneg
        G s p hs hp hp_top (R.block k)).mp (h k)).1 Q
    · exact ((souzaPositiveLevelBlock_iff_canonical_and_nonneg
        G s p hs hp hp_top (R.block k)).mp (h k)).2
  · rintro ⟨h1, h2⟩ k
    exact (souzaPositiveLevelBlock_iff_canonical_and_nonneg
      G s p hs hp hp_top (R.block k)).mpr ⟨h1 k, h2 k⟩

/-- A level block is *cone-positive* when every coefficient is a nonnegative real
number and every atom's function lies, almost everywhere, in the positive cone
(its value is a nonnegative real).  This is weaker than `SouzaPositiveLevelBlock`:
it does **not** require the atoms to be the canonical Souza atoms, only to be
nonnegative. -/
def SouzaConePositiveLevelBlock
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) : Prop :=
  ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    (∃ c : ℝ, 0 ≤ c ∧ B.coeff Q = (c : ℂ)) ∧
    (∀ᵐ x ∂ G.toWeakGridSpace.measure,
      ∃ d : ℝ, 0 ≤ d ∧
        (souzaAtomFamily G s p hs hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q) x = (d : ℂ))

/-- A Besov representation is *cone-positive* when all of its level blocks are
cone-positive: nonnegative real coefficients and atoms in the positive cone. -/
def SouzaConePositiveRepresentation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) f) : Prop :=
  ∀ k, SouzaConePositiveLevelBlock G s p hs hp hp_top (R.block k)

/-- A positive level block is in particular cone-positive: its canonical Souza
atom is, almost everywhere, a nonnegative real (it equals `μ(Q)^(s−1/p) ≥ 0` on
the cell and `0` off it). -/
theorem souzaPositiveLevelBlock_conePositive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    {B : WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k}
    (hB : SouzaPositiveLevelBlock G s p hs hp hp_top B) :
    SouzaConePositiveLevelBlock G s p hs hp hp_top B := by
  intro Q
  obtain ⟨c, hc0, hcoeff, hatom⟩ := hB Q
  refine ⟨⟨c, hc0, hcoeff⟩, ?_⟩
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [hatom]
  by_cases hx : x ∈ (goodGridCellOfLevelCell G Q).cell
  · exact ⟨(G.grid.μ (goodGridCellOfLevelCell G Q).cell).toReal ^ (s - (p.toReal)⁻¹),
      Real.rpow_nonneg ENNReal.toReal_nonneg _, by simp [canonicalSouzaAtom, hx]⟩
  · exact ⟨0, le_rfl, by simp [canonicalSouzaAtom, hx]⟩

/-- Every positive Souza representation is cone-positive. -/
theorem souzaPositiveRepresentation_conePositive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) f}
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R) :
    SouzaConePositiveRepresentation G s p hs hp hp_top R :=
  fun k => souzaPositiveLevelBlock_conePositive G s p hs hp hp_top (hR k)

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

/-- Scaling a positive Souza representation by a nonnegative real keeps it
positive (coefficients stay nonnegative reals; atoms are unchanged). -/
theorem souzaPositiveRepresentation_smul_nonneg
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {a : ℝ} (ha : 0 ≤ a)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g}
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R) :
    SouzaPositiveRepresentation G s p hs hp hp_top
      (WeakGridSpace.LpGridRepresentation.smul (a : ℂ) R) :=
  fun k => souzaPositiveLevelBlock_smul_nonneg G s p hs hp hp_top ha (hR k)

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
    simp [Complex.norm_real, Real.norm_of_nonneg hnonneg]

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
    simp [souzaPositiveZeroLevelBlock_toLp G s p hs hp hp_top]

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
    simp [souzaPositiveZeroRepresentation_levelCoeffPower G s p hs hp hp_top,
      Real.zero_rpow hpow_pos.ne']

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

/-- The zero Souza-Besov element belongs to the positive cone. -/
theorem souzaPositiveElement_zero
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    SouzaPositiveElement G s p q hs hp hp_top
      (0 : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q) := by
  exact ⟨souzaPositiveZeroRepresentation G s p hs hp hp_top,
    souzaPositiveZeroRepresentation_positive G s p hs hp hp_top⟩

/-- There is a cone-positive Souza representation of the zero `L^p` function with
zero `(p,q)` cost and identically vanishing coefficients.  This is the canonical
witness used for the degenerate `N = 0` case of the positive non-Archimedean
multiplier theorem. -/
theorem exists_souzaConePositiveZeroRepresentation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ S : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        (0 : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S = 0 ∧
      SouzaConePositiveRepresentation G s p hs hp hp_top S ∧
      (∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        (S.block k).coeff Q = 0) := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  refine ⟨souzaPositiveZeroRepresentation G s p hs hp hp_top,
    souzaPositiveZeroRepresentation_finitePQCost G s p q hs hp hp_top, ?_, ?_, ?_⟩
  · rw [WeakGridSpace.LpGridRepresentation.pqCost]
    by_cases hq : q = ∞
    · rw [if_pos hq]
      have hconst :
          (fun k => (souzaPositiveZeroRepresentation G s p hs hp hp_top).levelCoeffPower k ^
              (1 / p.toReal)) = fun _ : ℕ => (0 : ℝ) := by
        funext k
        rw [souzaPositiveZeroRepresentation_levelCoeffPower G s p hs hp hp_top k,
          Real.zero_rpow (one_div_ne_zero hp_pos.ne')]
      rw [hconst, Set.range_const, csSup_singleton]
    · rw [if_neg hq]
      have hq_pos : 0 < q.toReal :=
        ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
      have hpow_ne : q.toReal / p.toReal ≠ 0 := div_ne_zero hq_pos.ne' hp_pos.ne'
      have hsum :
          (∑' k, (souzaPositiveZeroRepresentation G s p hs hp hp_top).levelCoeffPower k ^
              (q.toReal / p.toReal)) = 0 := by
        simp [souzaPositiveZeroRepresentation_levelCoeffPower G s p hs hp hp_top,
          Real.zero_rpow hpow_ne]
      rw [hsum, Real.zero_rpow (one_div_ne_zero hq_pos.ne')]
  · exact souzaPositiveRepresentation_conePositive G s p hs hp hp_top
      (souzaPositiveZeroRepresentation_positive G s p hs hp hp_top)
  · intro k Q
    rfl

/-- The positive gauge of the zero Souza-Besov element is zero. -/
theorem souzaPositiveNorm_zero
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
      simp
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

private noncomputable def souzaLocalScalar
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (Q : WeakGridSpace.WeakGridCell G.toWeakGridSpace)
    (a : ((souzaAtomFamily G s p hs hp hp_top).localSpace Q).carrier) : ℂ := by
  change ℂ at a
  exact a

private theorem souzaAtomFamily_toFunction_eq_indicator
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (Q : WeakGridSpace.WeakGridCell G.toWeakGridSpace)
    (a : ((souzaAtomFamily G s p hs hp hp_top).localSpace Q).carrier) :
    (souzaAtomFamily G s p hs hp hp_top).toFunction Q a =
      Q.cell.indicator fun _ : α =>
        souzaLocalScalar G s p hs hp hp_top Q a := by
  funext x
  dsimp [WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily,
    souzaLocalVectorSpace, souzaLocalScalar]
  rfl

private noncomputable def souzaCanonicalizedLevelBlock
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k where
  coeff := fun Q =>
    B.coeff Q *
      souzaLocalScalar G s p hs hp hp_top
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) (B.atom Q) /
      souzaCanonicalLocalAtom G s p (goodGridCellOfLevelCell G Q)
  atom := fun Q =>
    souzaCanonicalLocalAtom G s p (goodGridCellOfLevelCell G Q)
  atom_mem := fun Q =>
    souzaCanonicalLocalAtom_mem G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)

private theorem souzaCanonicalizedLevelBlock_toLp
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    (souzaCanonicalizedLevelBlock G s p hs hp hp_top B).toLp
        (souzaAtomFamily G s p hs hp hp_top) =
      B.toLp (souzaAtomFamily G s p hs hp hp_top) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  unfold WeakGridSpace.LevelBlock.toLp
  refine Finset.sum_congr rfl ?_
  intro Q _
  let Qg := goodGridCellOfLevelCell G Q
  let aQ := souzaCanonicalLocalAtom G s p Qg
  have haQ_ne : aQ ≠ 0 := by
    have hpos := souzaCanonicalLocalAtom_pos G s p Qg
    simp [aQ, souzaCanonicalLocalAtom, hpos.ne']
  let bQ : ℂ :=
    souzaLocalScalar G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) (B.atom Q)
  have hfun :
      A.toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          (B.atom Q)
        = (bQ / aQ) •
          A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (souzaCanonicalLocalAtom G s p Qg) := by
    rw [souzaAtomFamily_toFunction_eq_indicator G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) (B.atom Q)]
    rw [souzaAtomFamily_toFunction_eq_indicator G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
      (souzaCanonicalLocalAtom G s p Qg)]
    funext x
    by_cases hx : x ∈ Q.1
    · simpa [WeakGridSpace.levelCellToWeakGridCell, Set.indicator_of_mem hx,
        Qg, aQ, bQ, souzaLocalScalar]
        using (div_mul_cancel₀ bQ haQ_ne).symm
    · simpa [WeakGridSpace.levelCellToWeakGridCell, Set.indicator_of_notMem hx,
        Qg, aQ, bQ, souzaLocalScalar]
  have htoLp :
      MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q)) =
        (bQ / aQ) •
          MemLp.toLp
            (A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (souzaCanonicalLocalAtom G s p Qg))
            (A.local_memLp_p
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (souzaCanonicalLocalAtom G s p Qg)) := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      rw [hfun]
  unfold WeakGridSpace.LevelBlock.term
  rw [htoLp]
  simp [souzaCanonicalizedLevelBlock, A, Qg, aQ, bQ, smul_smul,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

private theorem souzaCanonicalizedLevelBlock_positive_atom
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    (souzaAtomFamily G s p hs hp hp_top).toFunction
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
        ((souzaCanonicalizedLevelBlock G s p hs hp hp_top B).atom Q) =
      canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) := by
  simpa [souzaCanonicalizedLevelBlock, goodGridCellOfLevelCell] using
    souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)

private theorem souzaCanonicalizedLevelBlock_coeff_norm_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    ‖(souzaCanonicalizedLevelBlock G s p hs hp hp_top B).coeff Q‖ ≤
      ‖B.coeff Q‖ := by
  let Qg := goodGridCellOfLevelCell G Q
  let aQ := souzaCanonicalLocalAtom G s p Qg
  let bQ : ℂ :=
    souzaLocalScalar G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) (B.atom Q)
  have haQ_pos : 0 < ‖aQ‖ := by
    have hpos := souzaCanonicalLocalAtom_pos G s p Qg
    simpa [aQ, souzaCanonicalLocalAtom, Complex.norm_real,
      Real.norm_of_nonneg hpos.le] using hpos
  have hBatom_le : ‖bQ‖ ≤ ‖aQ‖ := by
    have hmem := B.atom_mem Q
    have hmem' :
        ‖bQ‖ ≤ (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) := by
      simpa [bQ, souzaLocalScalar, souzaAtomFamily, souzaAtomsSet,
        WeakGridSpace.levelCellToWeakGridCell] using hmem
    simpa [Qg, aQ, souzaCanonicalLocalAtom_norm] using hmem'
  calc
    ‖(souzaCanonicalizedLevelBlock G s p hs hp hp_top B).coeff Q‖
        = ‖B.coeff Q‖ * (‖bQ‖ / ‖aQ‖) := by
          simp [souzaCanonicalizedLevelBlock, Qg, aQ, bQ, norm_mul, norm_div,
            div_eq_mul_inv, mul_assoc]
    _ ≤ ‖B.coeff Q‖ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact div_le_one_of_le₀ hBatom_le (norm_nonneg _)
    _ = ‖B.coeff Q‖ := by rw [mul_one]

private theorem souzaCanonicalizedLevelBlock_levelCoeffPower_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(souzaCanonicalizedLevelBlock G s p hs hp hp_top B).coeff Q‖ ^ p.toReal) ≤
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖B.coeff Q‖ ^ p.toReal := by
  refine Finset.sum_le_sum ?_
  intro Q _
  exact Real.rpow_le_rpow (norm_nonneg _)
    (souzaCanonicalizedLevelBlock_coeff_norm_le G s p hs hp hp_top B Q)
    (ENNReal.toReal_nonneg)

/-- Canonicalizing a level block with nonnegative-real coefficients and
pointwise-positive atoms (on the cells where the coefficient does not vanish)
gives a positive level block. -/
private theorem souzaCanonicalizedLevelBlock_positive_of
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] {k : ℕ}
    (B : WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k)
    (hcoeff : ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ∃ r : NNReal, B.coeff Q = (r : ℂ))
    (hatom : ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      B.coeff Q ≠ 0 → ∀ x ∈ Q.1, ∃ a : NNReal, 0 < a ∧
        (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          (B.atom Q) x = (a : ℂ)) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (souzaCanonicalizedLevelBlock G s p hs hp hp_top B) := by
  classical
  intro Q
  have hatomeq := souzaCanonicalizedLevelBlock_positive_atom G s p hs hp hp_top B Q
  obtain ⟨r, hr⟩ := hcoeff Q
  by_cases hc0 : B.coeff Q = 0
  · exact ⟨0, le_rfl, by simp [souzaCanonicalizedLevelBlock, hc0], hatomeq⟩
  · have hQ_ne : G.toWeakGridSpace.grid.μ Q.1 ≠ 0 :=
      (G.toWeakGridSpace.grid.positive_measure k Q.1 Q.2).ne'
    obtain ⟨x₀, hx₀⟩ : Q.1.Nonempty :=
      MeasureTheory.nonempty_of_measure_ne_zero hQ_ne
    obtain ⟨a, ha_pos, ha_eq⟩ := hatom Q hc0 x₀ hx₀
    have hscalar :
        souzaLocalScalar G s p hs hp hp_top
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) (B.atom Q)
          = (a : ℂ) := by
      rw [souzaAtomFamily_toFunction_eq_indicator G s p hs hp hp_top
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) (B.atom Q),
        Set.indicator_of_mem
          (show x₀ ∈ (WeakGridSpace.levelCellToWeakGridCell
            G.toWeakGridSpace k Q).cell from hx₀)] at ha_eq
      exact ha_eq
    set μsp : ℝ := (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) with hμsp_def
    have hμsp_pos : 0 < μsp :=
      souzaCanonicalLocalAtom_pos G s p (goodGridCellOfLevelCell G Q)
    refine ⟨(r : ℝ) * (a : ℝ) / μsp, by positivity, ?_, hatomeq⟩
    show B.coeff Q *
        souzaLocalScalar G s p hs hp hp_top
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) (B.atom Q) /
        souzaCanonicalLocalAtom G s p (goodGridCellOfLevelCell G Q)
        = (((r : ℝ) * (a : ℝ) / μsp : ℝ) : ℂ)
    rw [hr, hscalar]
    have hcanon :
        souzaCanonicalLocalAtom G s p (goodGridCellOfLevelCell G Q) = ((μsp : ℝ) : ℂ) := by
      simp [souzaCanonicalLocalAtom, goodGridCellOfLevelCell, hμsp_def]
    rw [hcanon]
    push_cast
    field_simp

/-- From a representation with nonnegative-real coefficients and atoms that are
pointwise positive on the cells where the coefficient does not vanish, one
obtains a **positive** Souza representation of the same `L^p` element, with no
larger level coefficient powers and the same (or smaller) coefficient support. -/
theorem exists_souzaPositiveRepresentation_of_canonicalizable
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (hcoeff : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ∃ r : NNReal, (R.block k).coeff Q = (r : ℂ))
    (hatom : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 → ∀ x ∈ Q.1, ∃ a : NNReal, 0 < a ∧
        (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          ((R.block k).atom Q) x = (a : ℂ)) :
    ∃ R' : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top) g,
      SouzaPositiveRepresentation G s p hs hp hp_top R' ∧
      (∀ k, R'.levelCoeffPower k ≤ R.levelCoeffPower k) ∧
      (∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        (R'.block k).coeff Q ≠ 0 → (R.block k).coeff Q ≠ 0) := by
  classical
  refine ⟨{ block := fun k => souzaCanonicalizedLevelBlock G s p hs hp hp_top (R.block k)
            hasSum := ?_ }, ?_, ?_, ?_⟩
  · have hcongr : (fun k => (souzaCanonicalizedLevelBlock G s p hs hp hp_top
        (R.block k)).toLp (souzaAtomFamily G s p hs hp hp_top))
        = fun k => (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top) := by
      funext k
      exact souzaCanonicalizedLevelBlock_toLp G s p hs hp hp_top (R.block k)
    rw [hcongr]
    exact R.hasSum
  · intro k
    exact souzaCanonicalizedLevelBlock_positive_of G s p hs hp hp_top (R.block k)
      (hcoeff k) (fun Q hQ x hx => hatom k Q hQ x hx)
  · intro k
    simpa [WeakGridSpace.LpGridRepresentation.levelCoeffPower] using
      souzaCanonicalizedLevelBlock_levelCoeffPower_le G s p hs hp hp_top (R.block k)
  · intro k Q hne hR0
    exact hne (by simp [souzaCanonicalizedLevelBlock, hR0])

private noncomputable def realPositivePart (a : ℝ) : ℝ :=
  max a 0

private theorem realPositivePart_nonneg (a : ℝ) :
    0 ≤ realPositivePart a := by
  exact le_max_right a 0

private theorem realPositivePart_sub_neg (a : ℝ) :
    realPositivePart a - realPositivePart (-a) = a := by
  unfold realPositivePart
  by_cases ha : 0 ≤ a
  · have hnega : -a ≤ 0 := by linarith
    simp [max_eq_left ha, max_eq_right hnega]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    have hnega : 0 ≤ -a := by linarith
    simp [max_eq_right ha', max_eq_left hnega]

private noncomputable def complexRealPositiveCoeff (z : ℂ) : ℝ :=
  realPositivePart z.re

private noncomputable def complexRealNegativeCoeff (z : ℂ) : ℝ :=
  realPositivePart (-z.re)

private noncomputable def complexImagPositiveCoeff (z : ℂ) : ℝ :=
  realPositivePart z.im

private noncomputable def complexImagNegativeCoeff (z : ℂ) : ℝ :=
  realPositivePart (-z.im)

private theorem complexRealPositiveCoeff_nonneg (z : ℂ) :
    0 ≤ complexRealPositiveCoeff z :=
  realPositivePart_nonneg z.re

private theorem complexRealNegativeCoeff_nonneg (z : ℂ) :
    0 ≤ complexRealNegativeCoeff z :=
  realPositivePart_nonneg (-z.re)

private theorem complexImagPositiveCoeff_nonneg (z : ℂ) :
    0 ≤ complexImagPositiveCoeff z :=
  realPositivePart_nonneg z.im

private theorem complexImagNegativeCoeff_nonneg (z : ℂ) :
    0 ≤ complexImagNegativeCoeff z :=
  realPositivePart_nonneg (-z.im)

private theorem complex_coeff_decomposition (z : ℂ) :
    z =
      ((complexRealPositiveCoeff z - complexRealNegativeCoeff z : ℝ) : ℂ) +
        Complex.I *
          ((complexImagPositiveCoeff z - complexImagNegativeCoeff z : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [complexRealPositiveCoeff, complexRealNegativeCoeff,
      realPositivePart_sub_neg]
  · simp [complexImagPositiveCoeff, complexImagNegativeCoeff,
      realPositivePart_sub_neg]

private theorem realPositivePart_le_abs (a : ℝ) :
    realPositivePart a ≤ |a| := by
  unfold realPositivePart
  exact max_le (le_abs_self a) (abs_nonneg a)

private theorem realNegativePart_le_abs (a : ℝ) :
    realPositivePart (-a) ≤ |a| := by
  simpa [abs_neg] using realPositivePart_le_abs (-a)

private theorem complexRealPositiveCoeff_sub_negative_of_real
    {z : ℂ} (hz : ∃ r : ℝ, z = (r : ℂ)) :
    ((complexRealPositiveCoeff z - complexRealNegativeCoeff z : ℝ) : ℂ) = z := by
  rcases hz with ⟨r, rfl⟩
  simp [complexRealPositiveCoeff, complexRealNegativeCoeff, realPositivePart_sub_neg]

private theorem complexRealPositiveCoeff_norm_le_of_real
    {z : ℂ} (hz : ∃ r : ℝ, z = (r : ℂ)) :
    ‖((complexRealPositiveCoeff z : ℝ) : ℂ)‖ ≤ ‖z‖ := by
  rcases hz with ⟨r, rfl⟩
  simp [complexRealPositiveCoeff, Complex.norm_real,
    Real.norm_of_nonneg (realPositivePart_nonneg r), realPositivePart_le_abs]

private theorem complexRealNegativeCoeff_norm_le_of_real
    {z : ℂ} (hz : ∃ r : ℝ, z = (r : ℂ)) :
    ‖((complexRealNegativeCoeff z : ℝ) : ℂ)‖ ≤ ‖z‖ := by
  rcases hz with ⟨r, rfl⟩
  simp [complexRealNegativeCoeff, Complex.norm_real,
    Real.norm_of_nonneg (realPositivePart_nonneg (-r)), realNegativePart_le_abs]

private theorem abs_re_le_complex_norm (z : ℂ) :
    |z.re| ≤ ‖z‖ := by
  simpa [Complex.normSq, Complex.normSq_apply, Complex.normSq_eq_norm_sq] using
    Complex.abs_re_le_norm z

private theorem abs_im_le_complex_norm (z : ℂ) :
    |z.im| ≤ ‖z‖ := by
  simpa [Complex.normSq, Complex.normSq_apply, Complex.normSq_eq_norm_sq] using
    Complex.abs_im_le_norm z

private theorem complexRealPositiveCoeff_norm_le (z : ℂ) :
    ‖((complexRealPositiveCoeff z : ℝ) : ℂ)‖ ≤ ‖z‖ := by
  calc
    ‖((complexRealPositiveCoeff z : ℝ) : ℂ)‖ = realPositivePart z.re := by
      simp [complexRealPositiveCoeff, Complex.norm_real,
        Real.norm_of_nonneg (realPositivePart_nonneg z.re)]
    _ ≤ |z.re| := realPositivePart_le_abs z.re
    _ ≤ ‖z‖ := abs_re_le_complex_norm z

private theorem complexRealNegativeCoeff_norm_le (z : ℂ) :
    ‖((complexRealNegativeCoeff z : ℝ) : ℂ)‖ ≤ ‖z‖ := by
  calc
    ‖((complexRealNegativeCoeff z : ℝ) : ℂ)‖ = realPositivePart (-z.re) := by
      simp [complexRealNegativeCoeff, Complex.norm_real,
        Real.norm_of_nonneg (realPositivePart_nonneg (-z.re))]
    _ ≤ |z.re| := realNegativePart_le_abs z.re
    _ ≤ ‖z‖ := abs_re_le_complex_norm z

private theorem complexImagPositiveCoeff_norm_le (z : ℂ) :
    ‖((complexImagPositiveCoeff z : ℝ) : ℂ)‖ ≤ ‖z‖ := by
  calc
    ‖((complexImagPositiveCoeff z : ℝ) : ℂ)‖ = realPositivePart z.im := by
      simp [complexImagPositiveCoeff, Complex.norm_real,
        Real.norm_of_nonneg (realPositivePart_nonneg z.im)]
    _ ≤ |z.im| := realPositivePart_le_abs z.im
    _ ≤ ‖z‖ := abs_im_le_complex_norm z

private theorem complexImagNegativeCoeff_norm_le (z : ℂ) :
    ‖((complexImagNegativeCoeff z : ℝ) : ℂ)‖ ≤ ‖z‖ := by
  calc
    ‖((complexImagNegativeCoeff z : ℝ) : ℂ)‖ = realPositivePart (-z.im) := by
      simp [complexImagNegativeCoeff, Complex.norm_real,
        Real.norm_of_nonneg (realPositivePart_nonneg (-z.im))]
    _ ≤ |z.im| := realNegativePart_le_abs z.im
    _ ≤ ‖z‖ := abs_im_le_complex_norm z

private noncomputable def souzaPositivePartLevelBlock
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k where
  coeff := fun Q => ((complexRealPositiveCoeff (B.coeff Q) : ℝ) : ℂ)
  atom := fun Q =>
    souzaCanonicalLocalAtom G s p (goodGridCellOfLevelCell G Q)
  atom_mem := fun Q =>
    souzaCanonicalLocalAtom_mem G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)

private noncomputable def souzaNegativePartLevelBlock
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k where
  coeff := fun Q => ((complexRealNegativeCoeff (B.coeff Q) : ℝ) : ℂ)
  atom := fun Q =>
    souzaCanonicalLocalAtom G s p (goodGridCellOfLevelCell G Q)
  atom_mem := fun Q =>
    souzaCanonicalLocalAtom_mem G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)

private noncomputable def souzaImagPositivePartLevelBlock
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k where
  coeff := fun Q => ((complexImagPositiveCoeff (B.coeff Q) : ℝ) : ℂ)
  atom := fun Q =>
    souzaCanonicalLocalAtom G s p (goodGridCellOfLevelCell G Q)
  atom_mem := fun Q =>
    souzaCanonicalLocalAtom_mem G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)

private noncomputable def souzaImagNegativePartLevelBlock
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k where
  coeff := fun Q => ((complexImagNegativeCoeff (B.coeff Q) : ℝ) : ℂ)
  atom := fun Q =>
    souzaCanonicalLocalAtom G s p (goodGridCellOfLevelCell G Q)
  atom_mem := fun Q =>
    souzaCanonicalLocalAtom_mem G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)

private theorem souzaPositivePartLevelBlock_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (souzaPositivePartLevelBlock G s p hs hp hp_top B) := by
  intro Q
  refine ⟨complexRealPositiveCoeff (B.coeff Q),
    complexRealPositiveCoeff_nonneg (B.coeff Q), rfl, ?_⟩
  simpa [souzaPositivePartLevelBlock, goodGridCellOfLevelCell] using
    souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)

private theorem souzaNegativePartLevelBlock_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (souzaNegativePartLevelBlock G s p hs hp hp_top B) := by
  intro Q
  refine ⟨complexRealNegativeCoeff (B.coeff Q),
    complexRealNegativeCoeff_nonneg (B.coeff Q), rfl, ?_⟩
  simpa [souzaNegativePartLevelBlock, goodGridCellOfLevelCell] using
    souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)

private theorem souzaImagPositivePartLevelBlock_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (souzaImagPositivePartLevelBlock G s p hs hp hp_top B) := by
  intro Q
  refine ⟨complexImagPositiveCoeff (B.coeff Q),
    complexImagPositiveCoeff_nonneg (B.coeff Q), rfl, ?_⟩
  simpa [souzaImagPositivePartLevelBlock, goodGridCellOfLevelCell] using
    souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)

private theorem souzaImagNegativePartLevelBlock_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (souzaImagNegativePartLevelBlock G s p hs hp hp_top B) := by
  intro Q
  refine ⟨complexImagNegativeCoeff (B.coeff Q),
    complexImagNegativeCoeff_nonneg (B.coeff Q), rfl, ?_⟩
  simpa [souzaImagNegativePartLevelBlock, goodGridCellOfLevelCell] using
    souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)

private theorem souzaPositivePartLevelBlock_levelCoeffPower_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    (hreal : ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ∃ r : ℝ, B.coeff Q = (r : ℂ)) :
    WeakGridSpace.blockLvlCoeff
        (A := souzaAtomFamily G s p hs hp hp_top)
        (fun n => if h : n = k then h ▸
          souzaPositivePartLevelBlock G s p hs hp hp_top B else
          WeakGridSpace.LevelBlock.zero (souzaAtomFamily G s p hs hp hp_top) n) k ≤
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k, ‖B.coeff Q‖ ^ p.toReal := by
  simp only [WeakGridSpace.blockLvlCoeff, dif_pos rfl]
  refine Finset.sum_le_sum ?_
  intro Q _
  exact Real.rpow_le_rpow (norm_nonneg _)
    (complexRealPositiveCoeff_norm_le_of_real (hreal Q))
    ENNReal.toReal_nonneg

private theorem souzaNegativePartLevelBlock_levelCoeffPower_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    (hreal : ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ∃ r : ℝ, B.coeff Q = (r : ℂ)) :
    WeakGridSpace.blockLvlCoeff
        (A := souzaAtomFamily G s p hs hp hp_top)
        (fun n => if h : n = k then h ▸
          souzaNegativePartLevelBlock G s p hs hp hp_top B else
          WeakGridSpace.LevelBlock.zero (souzaAtomFamily G s p hs hp hp_top) n) k ≤
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k, ‖B.coeff Q‖ ^ p.toReal := by
  simp only [WeakGridSpace.blockLvlCoeff, dif_pos rfl]
  refine Finset.sum_le_sum ?_
  intro Q _
  exact Real.rpow_le_rpow (norm_nonneg _)
    (complexRealNegativeCoeff_norm_le_of_real (hreal Q))
    ENNReal.toReal_nonneg

private theorem souzaPositivePartLevelBlock_sub_negative_toLp
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    (hreal : ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ∃ r : ℝ, B.coeff Q = (r : ℂ))
    (hcanonical : ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          (B.atom Q) =
        canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q)) :
    (souzaPositivePartLevelBlock G s p hs hp hp_top B).toLp
        (souzaAtomFamily G s p hs hp hp_top) -
      (souzaNegativePartLevelBlock G s p hs hp hp_top B).toLp
        (souzaAtomFamily G s p hs hp hp_top) =
      B.toLp (souzaAtomFamily G s p hs hp hp_top) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  unfold WeakGridSpace.LevelBlock.toLp
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro Q _
  have hcanonical_pos :
      A.toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          ((souzaPositivePartLevelBlock G s p hs hp hp_top B).atom Q) =
        canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) := by
    simpa [A, souzaPositivePartLevelBlock, goodGridCellOfLevelCell] using
      souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
  have hcanonical_neg :
      A.toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          ((souzaNegativePartLevelBlock G s p hs hp hp_top B).atom Q) =
        canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) := by
    simpa [A, souzaNegativePartLevelBlock, goodGridCellOfLevelCell] using
      souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
  have hposLp :
      MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaPositivePartLevelBlock G s p hs hp hp_top B).atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaPositivePartLevelBlock G s p hs hp hp_top B).atom Q)) =
        MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q)) := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      rw [hcanonical_pos, hcanonical Q]
  have hnegLp :
      MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaNegativePartLevelBlock G s p hs hp hp_top B).atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaNegativePartLevelBlock G s p hs hp hp_top B).atom Q)) =
        MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q)) := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      rw [hcanonical_neg, hcanonical Q]
  have hcoeff :
      ((souzaPositivePartLevelBlock G s p hs hp hp_top B).coeff Q -
          (souzaNegativePartLevelBlock G s p hs hp hp_top B).coeff Q) =
        B.coeff Q := by
    simpa [souzaPositivePartLevelBlock, souzaNegativePartLevelBlock] using
      complexRealPositiveCoeff_sub_negative_of_real (hreal Q)
  unfold WeakGridSpace.LevelBlock.term
  rw [hposLp, hnegLp, ← sub_smul, hcoeff]

private theorem souzaComplexPartsLevelBlock_toLp
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    (hcanonical : ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          (B.atom Q) =
        canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q)) :
    B.toLp (souzaAtomFamily G s p hs hp hp_top) =
      ((souzaPositivePartLevelBlock G s p hs hp hp_top B).toLp
          (souzaAtomFamily G s p hs hp hp_top) -
        (souzaNegativePartLevelBlock G s p hs hp hp_top B).toLp
          (souzaAtomFamily G s p hs hp hp_top)) +
        Complex.I •
          ((souzaImagPositivePartLevelBlock G s p hs hp hp_top B).toLp
              (souzaAtomFamily G s p hs hp hp_top) -
            (souzaImagNegativePartLevelBlock G s p hs hp hp_top B).toLp
              (souzaAtomFamily G s p hs hp hp_top)) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  unfold WeakGridSpace.LevelBlock.toLp
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro Q _
  have hcanonical_re_pos :
      A.toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          ((souzaPositivePartLevelBlock G s p hs hp hp_top B).atom Q) =
        canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) := by
    simpa [A, souzaPositivePartLevelBlock, goodGridCellOfLevelCell] using
      souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
  have hcanonical_re_neg :
      A.toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          ((souzaNegativePartLevelBlock G s p hs hp hp_top B).atom Q) =
        canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) := by
    simpa [A, souzaNegativePartLevelBlock, goodGridCellOfLevelCell] using
      souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
  have hcanonical_im_pos :
      A.toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          ((souzaImagPositivePartLevelBlock G s p hs hp hp_top B).atom Q) =
        canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) := by
    simpa [A, souzaImagPositivePartLevelBlock, goodGridCellOfLevelCell] using
      souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
  have hcanonical_im_neg :
      A.toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          ((souzaImagNegativePartLevelBlock G s p hs hp hp_top B).atom Q) =
        canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) := by
    simpa [A, souzaImagNegativePartLevelBlock, goodGridCellOfLevelCell] using
      souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
  have hrePosLp :
      MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaPositivePartLevelBlock G s p hs hp hp_top B).atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaPositivePartLevelBlock G s p hs hp hp_top B).atom Q)) =
        MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q)) := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      rw [hcanonical_re_pos, hcanonical Q]
  have hreNegLp :
      MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaNegativePartLevelBlock G s p hs hp hp_top B).atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaNegativePartLevelBlock G s p hs hp hp_top B).atom Q)) =
        MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q)) := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      rw [hcanonical_re_neg, hcanonical Q]
  have himPosLp :
      MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaImagPositivePartLevelBlock G s p hs hp hp_top B).atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaImagPositivePartLevelBlock G s p hs hp hp_top B).atom Q)) =
        MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q)) := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      rw [hcanonical_im_pos, hcanonical Q]
  have himNegLp :
      MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaImagNegativePartLevelBlock G s p hs hp hp_top B).atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((souzaImagNegativePartLevelBlock G s p hs hp hp_top B).atom Q)) =
        MemLp.toLp
          (A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q))
          (A.local_memLp_p
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q)) := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      rw [hcanonical_im_neg, hcanonical Q]
  have hcoeff :
      B.coeff Q =
        ((souzaPositivePartLevelBlock G s p hs hp hp_top B).coeff Q -
          (souzaNegativePartLevelBlock G s p hs hp hp_top B).coeff Q) +
          Complex.I *
            ((souzaImagPositivePartLevelBlock G s p hs hp hp_top B).coeff Q -
              (souzaImagNegativePartLevelBlock G s p hs hp hp_top B).coeff Q) := by
    simpa [souzaPositivePartLevelBlock, souzaNegativePartLevelBlock,
      souzaImagPositivePartLevelBlock, souzaImagNegativePartLevelBlock] using
      complex_coeff_decomposition (B.coeff Q)
  unfold WeakGridSpace.LevelBlock.term
  rw [hrePosLp, hreNegLp, himPosLp, himNegLp, hcoeff]
  simpa [A, add_smul, sub_smul, mul_smul]

private theorem abstractFinitePQCost_of_blockLvlCoeff_le
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {A : WeakGridSpace.AtomFamily G s p u}
    {block block' : (k : ℕ) → WeakGridSpace.LevelBlock A k}
    (hle : ∀ k,
      WeakGridSpace.blockLvlCoeff (A := A) block' k ≤
        WeakGridSpace.blockLvlCoeff (A := A) block k)
    (hfin : WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) block) :
    WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) block' := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' A.p_ne_top
  by_cases hq : q = ∞
  · simp only [WeakGridSpace.AbstractFinitePQCost, hq, ↓reduceIte] at hfin ⊢
    refine ⟨Classical.choose hfin, ?_⟩
    rintro x ⟨k, rfl⟩
    exact (Real.rpow_le_rpow (WeakGridSpace.blockLvlCoeff_nonneg block' k)
      (hle k) (one_div_nonneg.mpr hp_pos.le)).trans (Classical.choose_spec hfin ⟨k, rfl⟩)
  · simp only [WeakGridSpace.AbstractFinitePQCost, hq, ↓reduceIte] at hfin ⊢
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    exact Summable.of_nonneg_of_le
      (fun k => Real.rpow_nonneg (WeakGridSpace.blockLvlCoeff_nonneg block' k) _)
      (fun k => Real.rpow_le_rpow
        (WeakGridSpace.blockLvlCoeff_nonneg block' k) (hle k)
        (div_nonneg hq_pos.le hp_pos.le))
      hfin

private theorem abstractPQCost_le_of_blockLvlCoeff_le
    {G : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {A : WeakGridSpace.AtomFamily G s p u}
    {block block' : (k : ℕ) → WeakGridSpace.LevelBlock A k}
    (hle : ∀ k,
      WeakGridSpace.blockLvlCoeff (A := A) block' k ≤
        WeakGridSpace.blockLvlCoeff (A := A) block k)
    (hfin : WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) block) :
    WeakGridSpace.abstractPQCost (A := A) (q := q) block' ≤
      WeakGridSpace.abstractPQCost (A := A) (q := q) block := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' A.p_ne_top
  by_cases hq : q = ∞
  · simp only [WeakGridSpace.AbstractFinitePQCost, hq, ↓reduceIte] at hfin
    simp only [WeakGridSpace.abstractPQCost, hq, ↓reduceIte]
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨k, rfl⟩
    exact (Real.rpow_le_rpow (WeakGridSpace.blockLvlCoeff_nonneg block' k)
      (hle k) (one_div_nonneg.mpr hp_pos.le)).trans (le_csSup hfin ⟨k, rfl⟩)
  · simp only [WeakGridSpace.AbstractFinitePQCost, hq, ↓reduceIte] at hfin
    simp only [WeakGridSpace.abstractPQCost, hq, ↓reduceIte]
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    apply Real.rpow_le_rpow
    · exact tsum_nonneg fun k =>
        Real.rpow_nonneg (WeakGridSpace.blockLvlCoeff_nonneg block' k) _
    · have hfin' :
          Summable fun k =>
            WeakGridSpace.blockLvlCoeff (A := A) block' k ^ (q.toReal / p.toReal) :=
        Summable.of_nonneg_of_le
          (fun k => Real.rpow_nonneg (WeakGridSpace.blockLvlCoeff_nonneg block' k) _)
          (fun k => Real.rpow_le_rpow
            (WeakGridSpace.blockLvlCoeff_nonneg block' k) (hle k)
            (div_nonneg hq_pos.le hp_pos.le))
          hfin
      exact hfin'.tsum_le_tsum
        (fun k => Real.rpow_le_rpow
          (WeakGridSpace.blockLvlCoeff_nonneg block' k) (hle k)
          (div_nonneg hq_pos.le hp_pos.le))
        hfin
    · exact one_div_nonneg.mpr hq_pos.le

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
            C.2)
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
      simp [mul_inv_cancel₀ ha_pos.ne']
    calc
      A * sInf Ux ≤ A * (ENNReal.ofReal a⁻¹ * D) :=
        by gcongr
      _ = D := by
        rw [← mul_assoc, hAinv, one_mul]

/-- The positive gauge satisfies the triangle inequality on the cone. -/
theorem souzaPositiveNorm_add_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {x y : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q}
    (_hx : SouzaPositiveElement G s p q hs hp hp_top x)
    (_hy : SouzaPositiveElement G s p q hs hp hp_top y) :
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
              C.2 D.2))
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
Real-valued Souza-Besov elements decompose uniformly as a difference of
positive-cone elements.

The intended proof uses the standard Souza representation of a real-valued
element: the coefficients are real, so we split them into positive and negative
parts.  The constant `C` absorbs the comparison between the standard
representation cost and the intrinsic Besov gauge.  The quantitative chain is:
standard representation cost is controlled by the Haar representation norm, the
Haar norm is controlled by a constant times the mean-oscillation norm, and the
mean-oscillation norm is controlled by the Besov gauge of `f`.
-/
theorem exists_souzaPositive_decomposition_of_aeRealValued
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ f : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          SouzaBesovAEEqRealValued G s p q hs hp hp_top f →
            ∃ u v : WeakGridSpace.BesovishSpace
                (souzaAtomFamily G s p hs hp hp_top) q,
              SouzaPositiveElement G s p q hs hp hp_top u ∧
                SouzaPositiveElement G s p q hs hp hp_top v ∧
                f = u - v ∧
                souzaPositiveNorm G s p q hs hp hp_top u ≤
                  ENNReal.ofReal C *
                    ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
                      (souzaAtomFamily G s p hs hp hp_top) q f) ∧
                souzaPositiveNorm G s p q hs hp hp_top v ≤
                  ENNReal.ofReal C *
                    ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
                      (souzaAtomFamily G s p hs hp hp_top) q f) := by
  classical
  letI : DecidableEq (Set α) := Classical.decEq (Set α)
  have hp_lt_top : p < ∞ := lt_top_iff_ne_top.mpr hp_top
  let H : UnbalancedHaarWavelet.HaarSystem (HaarRepresentation.GridOf G) :=
    Classical.choice (UnbalancedHaarWavelet.exists_haarSystem (HaarRepresentation.GridOf G))
  let F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G) :=
    { toHaarSystem := H
      alphaFunction := UnbalancedHaarWavelet.normalizedAlphaFunction
        (HaarRepresentation.GridOf G)
      alphaFunction_def := rfl }
  letI : DecidableEq F.Index := Classical.decEq F.Index
  rcases StandardAtomicRepresentation.exists_standardRepresentationNorm_le_const_mul_souzaBesovNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_lt_top)
      (q := q) with
    ⟨Cst, hCst_ne_top, hstandard_le⟩
  refine ⟨Cst.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro f hf_real
  let A := souzaAtomFamily G s p hs hp hp_top
  let fFun : α → ℂ := ((f : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
  haveI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hfMemLp : MemLp fFun p G.grid.μ := by
    simpa [fFun, GoodGridSpace.toWeakGridSpace] using
      (Lp.memLp (f : Lp ℂ p G.toWeakGridSpace.measure))
  have hfint : Integrable fFun G.grid.μ := hfMemLp.integrable (Fact.out : 1 ≤ p)
  have hf_real_grid : ∀ᵐ x ∂G.grid.μ, ∃ r : ℝ, fFun x = (r : ℂ) := by
    simpa [fFun, GoodGridSpace.toWeakGridSpace] using hf_real
  have hstd :
      StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint ≠ ∞ ∧
        StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint ≤
          Cst * ENNReal.ofReal
            (WeakGridSpace.BesovishSpace.Norm_Costpq A q f) := by
    simpa [A, fFun, GoodGridSpace.toWeakGridSpace] using
      hstandard_le f fFun hfint (Filter.EventuallyEq.rfl)
  rcases hstd with ⟨hstd_ne_top, hstd_le⟩
  rcases StandardAtomicRepresentation.finite_standardRepresentationNorm_implies_memBesov_and_standardRepresentation
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_lt_top)
      (q := q) fFun hfint hstd_ne_top with
    ⟨hfLp, gstd, Rstd, hgstdLp, hRstd_block, hRstd_fin, _hRstd_enn,
      hRstd_cost, _hgstd_cost⟩
  have hgstd_eq_f : gstd = f := by
    apply Subtype.ext
    have hto :
        hfLp.toLp fFun = (f : Lp ℂ p G.toWeakGridSpace.measure) := by
      change hfLp.toLp ((f : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =
        (f : Lp ℂ p G.toWeakGridSpace.measure)
      exact Lp.toLp_coeFn (f : Lp ℂ p G.toWeakGridSpace.measure) hfLp
    exact hgstdLp.trans hto
  have hRcoeff_real :
      ∀ k, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ∃ r : ℝ, (Rstd.block k).coeff Q = (r : ℂ) := by
    intro k Q
    have hblock :
        Rstd.block k =
          StandardAtomicRepresentation.canonicalStandardBlockSeq
            G F s hs p hp_lt_top fFun hfint k := congrFun hRstd_block k
    rw [hblock]
    exact StandardAtomicRepresentation.canonicalStandardLpGridBlock_coeff_realValued_of_aeRealValued
      G F s p hs hp hp_top fFun hfint hf_real_grid k Q
  have hRcanonical :
      ∀ k, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((Rstd.block k).atom Q) =
          canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) := by
    intro k Q
    have hblock :
        Rstd.block k =
          StandardAtomicRepresentation.canonicalStandardBlockSeq
            G F s hs p hp_lt_top fFun hfint k := congrFun hRstd_block k
    rw [hblock]
    cases k with
    | zero =>
        simpa [A, StandardAtomicRepresentation.canonicalStandardBlockSeq,
          StandardAtomicRepresentation.canonicalStandardLpGridBlock,
          StandardAtomicRepresentation.canonicalStandardFatherLevelBlock,
          souzaCanonicalLocalAtom, goodGridCellOfLevelCell] using
          souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace 0 Q)
    | succ k =>
        simpa [A, StandardAtomicRepresentation.canonicalStandardBlockSeq,
          StandardAtomicRepresentation.canonicalStandardLpGridBlock,
          StandardAtomicRepresentation.canonicalStandardPositiveLevelBlock,
          souzaCanonicalLocalAtom, goodGridCellOfLevelCell] using
          souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace (k + 1) Q)
  let Bpos : (k : ℕ) → WeakGridSpace.LevelBlock A k :=
    fun k => souzaPositivePartLevelBlock G s p hs hp hp_top (Rstd.block k)
  let Bneg : (k : ℕ) → WeakGridSpace.LevelBlock A k :=
    fun k => souzaNegativePartLevelBlock G s p hs hp hp_top (Rstd.block k)
  have hpos_level_le :
      ∀ k, WeakGridSpace.blockLvlCoeff (A := A) Bpos k ≤
        WeakGridSpace.blockLvlCoeff (A := A) Rstd.block k := by
    intro k
    simp only [WeakGridSpace.blockLvlCoeff, Bpos]
    refine Finset.sum_le_sum ?_
    intro Q _
    exact Real.rpow_le_rpow (norm_nonneg _)
      (complexRealPositiveCoeff_norm_le_of_real (hRcoeff_real k Q))
      ENNReal.toReal_nonneg
  have hneg_level_le :
      ∀ k, WeakGridSpace.blockLvlCoeff (A := A) Bneg k ≤
        WeakGridSpace.blockLvlCoeff (A := A) Rstd.block k := by
    intro k
    simp only [WeakGridSpace.blockLvlCoeff, Bneg]
    refine Finset.sum_le_sum ?_
    intro Q _
    exact Real.rpow_le_rpow (norm_nonneg _)
      (complexRealNegativeCoeff_norm_le_of_real (hRcoeff_real k Q))
      ENNReal.toReal_nonneg
  have hRstd_block_fin :
      WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) Rstd.block := by
    simpa [WeakGridSpace.AbstractFinitePQCost, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff, WeakGridSpace.LpGridRepresentation.levelCoeffPower] using
      hRstd_fin
  have hpos_fin : WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) Bpos :=
    abstractFinitePQCost_of_blockLvlCoeff_le hpos_level_le hRstd_block_fin
  have hneg_fin : WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) Bneg :=
    abstractFinitePQCost_of_blockLvlCoeff_le hneg_level_le hRstd_block_fin
  have hG2 : WeakGridSpace.AssumptionG2 G.toWeakGridSpace s p ∞ q :=
    souza_assumptionG2 G s p q hs hp hp_top
  haveI : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  rcases WeakGridSpace.formalBlockSeq_hasRepresentation
      (G := G.toWeakGridSpace) (A := A) (q := q)
      hG2 hp_top hs le_top Bpos hpos_fin with
    ⟨uLp, hupos_nonempty⟩
  rcases hupos_nonempty with ⟨Rpos_sub⟩
  rcases Rpos_sub with ⟨Rpos, hRpos_block⟩
  rcases WeakGridSpace.formalBlockSeq_hasRepresentation
      (G := G.toWeakGridSpace) (A := A) (q := q)
      hG2 hp_top hs le_top Bneg hneg_fin with
    ⟨vLp, hvneg_nonempty⟩
  rcases hvneg_nonempty with ⟨Rneg_sub⟩
  rcases Rneg_sub with ⟨Rneg, hRneg_block⟩
  have hRpos_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rpos := by
    simpa [WeakGridSpace.AbstractFinitePQCost, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff, WeakGridSpace.LpGridRepresentation.levelCoeffPower,
      hRpos_block] using hpos_fin
  have hRneg_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rneg := by
    simpa [WeakGridSpace.AbstractFinitePQCost, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff, WeakGridSpace.LpGridRepresentation.levelCoeffPower,
      hRneg_block] using hneg_fin
  let u : WeakGridSpace.BesovishSpace A q := ⟨uLp, ⟨Rpos, hRpos_fin⟩⟩
  let v : WeakGridSpace.BesovishSpace A q := ⟨vLp, ⟨Rneg, hRneg_fin⟩⟩
  have hRpos_positive : SouzaPositiveRepresentation G s p hs hp hp_top Rpos := by
    intro k
    rw [hRpos_block]
    exact souzaPositivePartLevelBlock_positive G s p hs hp hp_top (Rstd.block k)
  have hRneg_positive : SouzaPositiveRepresentation G s p hs hp hp_top Rneg := by
    intro k
    rw [hRneg_block]
    exact souzaNegativePartLevelBlock_positive G s p hs hp hp_top (Rstd.block k)
  have hsum_sub :
      HasSum (fun k => (Rstd.block k).toLp A)
        (uLp - vLp) := by
    refine (Rpos.hasSum.sub Rneg.hasSum).congr_fun ?_
    intro k
    rw [hRpos_block, hRneg_block]
    exact (souzaPositivePartLevelBlock_sub_negative_toLp
      G s p hs hp hp_top (Rstd.block k)
      (hRcoeff_real k) (hRcanonical k)).symm
  have huvLp_eq_gstd :
      uLp - vLp = (gstd : Lp ℂ p G.toWeakGridSpace.measure) :=
    HasSum.unique hsum_sub (by simpa [A] using Rstd.hasSum)
  have hdecomp : f = u - v := by
    apply Subtype.ext
    change (f : Lp ℂ p G.toWeakGridSpace.measure) = uLp - vLp
    exact (congrArg Subtype.val hgstd_eq_f).symm.trans huvLp_eq_gstd.symm
  have hRstd_cost_eq_block :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rstd =
        WeakGridSpace.abstractPQCost (A := A) (q := q) Rstd.block := by
    rfl
  have hRpos_cost_eq_block :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rpos =
        WeakGridSpace.abstractPQCost (A := A) (q := q) Bpos := by
    have hlevel : ∀ k,
        Rpos.levelCoeffPower k =
          WeakGridSpace.blockLvlCoeff (A := A) Bpos k := by
      intro k
      simp [WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        WeakGridSpace.blockLvlCoeff, hRpos_block]
    simp [WeakGridSpace.LpGridRepresentation.pqCost, WeakGridSpace.abstractPQCost, hlevel]
  have hRneg_cost_eq_block :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rneg =
        WeakGridSpace.abstractPQCost (A := A) (q := q) Bneg := by
    have hlevel : ∀ k,
        Rneg.levelCoeffPower k =
          WeakGridSpace.blockLvlCoeff (A := A) Bneg k := by
      intro k
      simp [WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        WeakGridSpace.blockLvlCoeff, hRneg_block]
    simp [WeakGridSpace.LpGridRepresentation.pqCost, WeakGridSpace.abstractPQCost, hlevel]
  have hRpos_cost :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rpos ≤
        (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal := by
    calc
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rpos
          = WeakGridSpace.abstractPQCost (A := A) (q := q) Bpos := hRpos_cost_eq_block
      _ ≤ WeakGridSpace.abstractPQCost (A := A) (q := q) Rstd.block :=
          abstractPQCost_le_of_blockLvlCoeff_le hpos_level_le hRstd_block_fin
      _ = WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rstd := hRstd_cost_eq_block.symm
      _ ≤ (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal := hRstd_cost
  have hRneg_cost :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rneg ≤
        (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal := by
    calc
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rneg
          = WeakGridSpace.abstractPQCost (A := A) (q := q) Bneg := hRneg_cost_eq_block
      _ ≤ WeakGridSpace.abstractPQCost (A := A) (q := q) Rstd.block :=
          abstractPQCost_le_of_blockLvlCoeff_le hneg_level_le hRstd_block_fin
      _ = WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rstd := hRstd_cost_eq_block.symm
      _ ≤ (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal := hRstd_cost
  have hRpos_enn :
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) Rpos ≤
        ENNReal.ofReal
          (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal :=
    pqCostENNReal_le_of_finitePQCost_pqCost_le Rpos hRpos_fin hRpos_cost
  have hRneg_enn :
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) Rneg ≤
        ENNReal.ofReal
          (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal :=
    pqCostENNReal_le_of_finitePQCost_pqCost_le Rneg hRneg_fin hRneg_cost
  have hu_norm_std :
      souzaPositiveNorm G s p q hs hp hp_top u ≤
        ENNReal.ofReal
          (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal := by
    unfold souzaPositiveNorm
    exact sInf_le ⟨Rpos, hRpos_positive, hRpos_fin, hRpos_enn⟩
  have hv_norm_std :
      souzaPositiveNorm G s p q hs hp hp_top v ≤
        ENNReal.ofReal
          (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal := by
    unfold souzaPositiveNorm
    exact sInf_le ⟨Rneg, hRneg_positive, hRneg_fin, hRneg_enn⟩
  have hstd_le_target :
      ENNReal.ofReal
          (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal ≤
        ENNReal.ofReal Cst.toReal *
          ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq A q f) := by
    calc
      ENNReal.ofReal
          (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal
          = StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint :=
            ENNReal.ofReal_toReal hstd_ne_top
      _ ≤ Cst * ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq A q f) :=
          hstd_le
      _ = ENNReal.ofReal Cst.toReal *
          ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq A q f) := by
          rw [ENNReal.ofReal_toReal hCst_ne_top]
  refine ⟨u, v, ⟨Rpos, hRpos_positive⟩, ⟨Rneg, hRneg_positive⟩, hdecomp, ?_, ?_⟩
  · exact hu_norm_std.trans hstd_le_target
  · exact hv_norm_std.trans hstd_le_target

/--
Complex-valued Souza-Besov elements decompose into real and imaginary
positive-cone differences with a uniform quantitative loss.

Every element of the complex Souza-Besov space can be written as
`(u - v) + i • (w - r)`, where all four pieces belong to the positive cone and
each positive gauge is bounded by a fixed constant times the usual Besov gauge
of `f`.  The intended proof applies the real-valued decomposition to the real
and imaginary parts, together with the boundedness of those coordinate
projections in the Souza-Besov gauge.
-/
theorem exists_souzaPositive_decomposition_of_aeComplexValued
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ f : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          ∃ u v w r : WeakGridSpace.BesovishSpace
              (souzaAtomFamily G s p hs hp hp_top) q,
            SouzaPositiveElement G s p q hs hp hp_top u ∧
              SouzaPositiveElement G s p q hs hp hp_top v ∧
              SouzaPositiveElement G s p q hs hp hp_top w ∧
              SouzaPositiveElement G s p q hs hp hp_top r ∧
              f = (u - v) + Complex.I • (w - r) ∧
              souzaPositiveNorm G s p q hs hp hp_top u ≤
                ENNReal.ofReal C *
                  ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
                    (souzaAtomFamily G s p hs hp hp_top) q f) ∧
              souzaPositiveNorm G s p q hs hp hp_top v ≤
                ENNReal.ofReal C *
                  ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
                    (souzaAtomFamily G s p hs hp hp_top) q f) ∧
              souzaPositiveNorm G s p q hs hp hp_top w ≤
                ENNReal.ofReal C *
                  ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
                    (souzaAtomFamily G s p hs hp hp_top) q f) ∧
              souzaPositiveNorm G s p q hs hp hp_top r ≤
                ENNReal.ofReal C *
                  ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
                    (souzaAtomFamily G s p hs hp hp_top) q f) := by
  classical
  letI : DecidableEq (Set α) := Classical.decEq (Set α)
  have hp_lt_top : p < ∞ := lt_top_iff_ne_top.mpr hp_top
  let H : UnbalancedHaarWavelet.HaarSystem (HaarRepresentation.GridOf G) :=
    Classical.choice (UnbalancedHaarWavelet.exists_haarSystem (HaarRepresentation.GridOf G))
  let F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G) :=
    { toHaarSystem := H
      alphaFunction := UnbalancedHaarWavelet.normalizedAlphaFunction
        (HaarRepresentation.GridOf G)
      alphaFunction_def := rfl }
  letI : DecidableEq F.Index := Classical.decEq F.Index
  rcases StandardAtomicRepresentation.exists_standardRepresentationNorm_le_const_mul_souzaBesovNorm
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_lt_top)
      (q := q) with
    ⟨Cst, hCst_ne_top, hstandard_le⟩
  refine ⟨Cst.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro f
  let A := souzaAtomFamily G s p hs hp hp_top
  let fFun : α → ℂ := ((f : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
  haveI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hfMemLp : MemLp fFun p G.grid.μ := by
    simpa [fFun, GoodGridSpace.toWeakGridSpace] using
      (Lp.memLp (f : Lp ℂ p G.toWeakGridSpace.measure))
  have hfint : Integrable fFun G.grid.μ := hfMemLp.integrable (Fact.out : 1 ≤ p)
  have hstd :
      StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint ≠ ∞ ∧
        StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint ≤
          Cst * ENNReal.ofReal
            (WeakGridSpace.BesovishSpace.Norm_Costpq A q f) := by
    simpa [A, fFun, GoodGridSpace.toWeakGridSpace] using
      hstandard_le f fFun hfint (Filter.EventuallyEq.rfl)
  rcases hstd with ⟨hstd_ne_top, hstd_le⟩
  rcases StandardAtomicRepresentation.finite_standardRepresentationNorm_implies_memBesov_and_standardRepresentation
      (G := G) (F := F) (s := s) (hs := hs) (p := p) (hp_top := hp_lt_top)
      (q := q) fFun hfint hstd_ne_top with
    ⟨hfLp, gstd, Rstd, hgstdLp, hRstd_block, hRstd_fin, _hRstd_enn,
      hRstd_cost, _hgstd_cost⟩
  have hgstd_eq_f : gstd = f := by
    apply Subtype.ext
    have hto :
        hfLp.toLp fFun = (f : Lp ℂ p G.toWeakGridSpace.measure) := by
      change hfLp.toLp ((f : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =
        (f : Lp ℂ p G.toWeakGridSpace.measure)
      exact Lp.toLp_coeFn (f : Lp ℂ p G.toWeakGridSpace.measure) hfLp
    exact hgstdLp.trans hto
  have hRcanonical :
      ∀ k, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        A.toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((Rstd.block k).atom Q) =
          canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) := by
    intro k Q
    have hblock :
        Rstd.block k =
          StandardAtomicRepresentation.canonicalStandardBlockSeq
            G F s hs p hp_lt_top fFun hfint k := congrFun hRstd_block k
    rw [hblock]
    cases k with
    | zero =>
        simpa [A, StandardAtomicRepresentation.canonicalStandardBlockSeq,
          StandardAtomicRepresentation.canonicalStandardLpGridBlock,
          StandardAtomicRepresentation.canonicalStandardFatherLevelBlock,
          souzaCanonicalLocalAtom, goodGridCellOfLevelCell] using
          souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace 0 Q)
    | succ k =>
        simpa [A, StandardAtomicRepresentation.canonicalStandardBlockSeq,
          StandardAtomicRepresentation.canonicalStandardLpGridBlock,
          StandardAtomicRepresentation.canonicalStandardPositiveLevelBlock,
          souzaCanonicalLocalAtom, goodGridCellOfLevelCell] using
          souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace (k + 1) Q)
  let BrePos : (k : ℕ) → WeakGridSpace.LevelBlock A k :=
    fun k => souzaPositivePartLevelBlock G s p hs hp hp_top (Rstd.block k)
  let BreNeg : (k : ℕ) → WeakGridSpace.LevelBlock A k :=
    fun k => souzaNegativePartLevelBlock G s p hs hp hp_top (Rstd.block k)
  let BimPos : (k : ℕ) → WeakGridSpace.LevelBlock A k :=
    fun k => souzaImagPositivePartLevelBlock G s p hs hp hp_top (Rstd.block k)
  let BimNeg : (k : ℕ) → WeakGridSpace.LevelBlock A k :=
    fun k => souzaImagNegativePartLevelBlock G s p hs hp hp_top (Rstd.block k)
  have hRePos_level_le :
      ∀ k, WeakGridSpace.blockLvlCoeff (A := A) BrePos k ≤
        WeakGridSpace.blockLvlCoeff (A := A) Rstd.block k := by
    intro k
    simp only [WeakGridSpace.blockLvlCoeff, BrePos]
    refine Finset.sum_le_sum ?_
    intro Q _
    exact Real.rpow_le_rpow (norm_nonneg _)
      (complexRealPositiveCoeff_norm_le ((Rstd.block k).coeff Q))
      ENNReal.toReal_nonneg
  have hReNeg_level_le :
      ∀ k, WeakGridSpace.blockLvlCoeff (A := A) BreNeg k ≤
        WeakGridSpace.blockLvlCoeff (A := A) Rstd.block k := by
    intro k
    simp only [WeakGridSpace.blockLvlCoeff, BreNeg]
    refine Finset.sum_le_sum ?_
    intro Q _
    exact Real.rpow_le_rpow (norm_nonneg _)
      (complexRealNegativeCoeff_norm_le ((Rstd.block k).coeff Q))
      ENNReal.toReal_nonneg
  have hImPos_level_le :
      ∀ k, WeakGridSpace.blockLvlCoeff (A := A) BimPos k ≤
        WeakGridSpace.blockLvlCoeff (A := A) Rstd.block k := by
    intro k
    simp only [WeakGridSpace.blockLvlCoeff, BimPos]
    refine Finset.sum_le_sum ?_
    intro Q _
    exact Real.rpow_le_rpow (norm_nonneg _)
      (complexImagPositiveCoeff_norm_le ((Rstd.block k).coeff Q))
      ENNReal.toReal_nonneg
  have hImNeg_level_le :
      ∀ k, WeakGridSpace.blockLvlCoeff (A := A) BimNeg k ≤
        WeakGridSpace.blockLvlCoeff (A := A) Rstd.block k := by
    intro k
    simp only [WeakGridSpace.blockLvlCoeff, BimNeg]
    refine Finset.sum_le_sum ?_
    intro Q _
    exact Real.rpow_le_rpow (norm_nonneg _)
      (complexImagNegativeCoeff_norm_le ((Rstd.block k).coeff Q))
      ENNReal.toReal_nonneg
  have hRstd_block_fin :
      WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) Rstd.block := by
    simpa [WeakGridSpace.AbstractFinitePQCost, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff, WeakGridSpace.LpGridRepresentation.levelCoeffPower] using
      hRstd_fin
  have hRePos_fin : WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) BrePos :=
    abstractFinitePQCost_of_blockLvlCoeff_le hRePos_level_le hRstd_block_fin
  have hReNeg_fin : WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) BreNeg :=
    abstractFinitePQCost_of_blockLvlCoeff_le hReNeg_level_le hRstd_block_fin
  have hImPos_fin : WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) BimPos :=
    abstractFinitePQCost_of_blockLvlCoeff_le hImPos_level_le hRstd_block_fin
  have hImNeg_fin : WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) BimNeg :=
    abstractFinitePQCost_of_blockLvlCoeff_le hImNeg_level_le hRstd_block_fin
  have hG2 : WeakGridSpace.AssumptionG2 G.toWeakGridSpace s p ∞ q :=
    souza_assumptionG2 G s p q hs hp hp_top
  haveI : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  rcases WeakGridSpace.formalBlockSeq_hasRepresentation
      (G := G.toWeakGridSpace) (A := A) (q := q)
      hG2 hp_top hs le_top BrePos hRePos_fin with
    ⟨uLp, hupos_nonempty⟩
  rcases hupos_nonempty with ⟨RrePos_sub⟩
  rcases RrePos_sub with ⟨RrePos, hRrePos_block⟩
  rcases WeakGridSpace.formalBlockSeq_hasRepresentation
      (G := G.toWeakGridSpace) (A := A) (q := q)
      hG2 hp_top hs le_top BreNeg hReNeg_fin with
    ⟨vLp, hvneg_nonempty⟩
  rcases hvneg_nonempty with ⟨RreNeg_sub⟩
  rcases RreNeg_sub with ⟨RreNeg, hRreNeg_block⟩
  rcases WeakGridSpace.formalBlockSeq_hasRepresentation
      (G := G.toWeakGridSpace) (A := A) (q := q)
      hG2 hp_top hs le_top BimPos hImPos_fin with
    ⟨wLp, hwpos_nonempty⟩
  rcases hwpos_nonempty with ⟨RimPos_sub⟩
  rcases RimPos_sub with ⟨RimPos, hRimPos_block⟩
  rcases WeakGridSpace.formalBlockSeq_hasRepresentation
      (G := G.toWeakGridSpace) (A := A) (q := q)
      hG2 hp_top hs le_top BimNeg hImNeg_fin with
    ⟨rLp, hrneg_nonempty⟩
  rcases hrneg_nonempty with ⟨RimNeg_sub⟩
  rcases RimNeg_sub with ⟨RimNeg, hRimNeg_block⟩
  have hRrePos_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) RrePos := by
    simpa [WeakGridSpace.AbstractFinitePQCost, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff, WeakGridSpace.LpGridRepresentation.levelCoeffPower,
      hRrePos_block] using hRePos_fin
  have hRreNeg_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) RreNeg := by
    simpa [WeakGridSpace.AbstractFinitePQCost, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff, WeakGridSpace.LpGridRepresentation.levelCoeffPower,
      hRreNeg_block] using hReNeg_fin
  have hRimPos_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) RimPos := by
    simpa [WeakGridSpace.AbstractFinitePQCost, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff, WeakGridSpace.LpGridRepresentation.levelCoeffPower,
      hRimPos_block] using hImPos_fin
  have hRimNeg_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) RimNeg := by
    simpa [WeakGridSpace.AbstractFinitePQCost, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.blockLvlCoeff, WeakGridSpace.LpGridRepresentation.levelCoeffPower,
      hRimNeg_block] using hImNeg_fin
  let u : WeakGridSpace.BesovishSpace A q := ⟨uLp, ⟨RrePos, hRrePos_fin⟩⟩
  let v : WeakGridSpace.BesovishSpace A q := ⟨vLp, ⟨RreNeg, hRreNeg_fin⟩⟩
  let w : WeakGridSpace.BesovishSpace A q := ⟨wLp, ⟨RimPos, hRimPos_fin⟩⟩
  let r : WeakGridSpace.BesovishSpace A q := ⟨rLp, ⟨RimNeg, hRimNeg_fin⟩⟩
  have hRrePos_positive : SouzaPositiveRepresentation G s p hs hp hp_top RrePos := by
    intro k
    rw [hRrePos_block]
    exact souzaPositivePartLevelBlock_positive G s p hs hp hp_top (Rstd.block k)
  have hRreNeg_positive : SouzaPositiveRepresentation G s p hs hp hp_top RreNeg := by
    intro k
    rw [hRreNeg_block]
    exact souzaNegativePartLevelBlock_positive G s p hs hp hp_top (Rstd.block k)
  have hRimPos_positive : SouzaPositiveRepresentation G s p hs hp hp_top RimPos := by
    intro k
    rw [hRimPos_block]
    exact souzaImagPositivePartLevelBlock_positive G s p hs hp hp_top (Rstd.block k)
  have hRimNeg_positive : SouzaPositiveRepresentation G s p hs hp hp_top RimNeg := by
    intro k
    rw [hRimNeg_block]
    exact souzaImagNegativePartLevelBlock_positive G s p hs hp hp_top (Rstd.block k)
  have hsum_complex :
      HasSum (fun k => (Rstd.block k).toLp A)
        ((uLp - vLp) + Complex.I • (wLp - rLp)) := by
    refine ((RrePos.hasSum.sub RreNeg.hasSum).add
      ((RimPos.hasSum.sub RimNeg.hasSum).const_smul Complex.I)).congr_fun ?_
    intro k
    rw [hRrePos_block, hRreNeg_block, hRimPos_block, hRimNeg_block]
    exact souzaComplexPartsLevelBlock_toLp
      G s p hs hp hp_top (Rstd.block k) (hRcanonical k)
  have hcomplexLp_eq_gstd :
      (uLp - vLp) + Complex.I • (wLp - rLp) =
        (gstd : Lp ℂ p G.toWeakGridSpace.measure) :=
    HasSum.unique hsum_complex (by simpa [A] using Rstd.hasSum)
  have hdecomp : f = (u - v) + Complex.I • (w - r) := by
    apply Subtype.ext
    change (f : Lp ℂ p G.toWeakGridSpace.measure) =
      (uLp - vLp) + Complex.I • (wLp - rLp)
    exact (congrArg Subtype.val hgstd_eq_f).symm.trans hcomplexLp_eq_gstd.symm
  have hRstd_cost_eq_block :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rstd =
        WeakGridSpace.abstractPQCost (A := A) (q := q) Rstd.block := by
    rfl
  have cost_eq_block
      {g : Lp ℂ p G.toWeakGridSpace.measure}
      {B : (k : ℕ) → WeakGridSpace.LevelBlock A k}
      (R : WeakGridSpace.LpGridRepresentation A g)
      (hRblock : R.block = B) :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R =
        WeakGridSpace.abstractPQCost (A := A) (q := q) B := by
    have hlevel : ∀ k,
        R.levelCoeffPower k =
          WeakGridSpace.blockLvlCoeff (A := A) B k := by
      intro k
      simp [WeakGridSpace.LpGridRepresentation.levelCoeffPower,
        WeakGridSpace.blockLvlCoeff, hRblock]
    simp [WeakGridSpace.LpGridRepresentation.pqCost, WeakGridSpace.abstractPQCost, hlevel]
  have hstd_target :
      ENNReal.ofReal
          (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal ≤
        ENNReal.ofReal Cst.toReal *
          ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq A q f) := by
    calc
      ENNReal.ofReal
          (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal
          = StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint :=
            ENNReal.ofReal_toReal hstd_ne_top
      _ ≤ Cst * ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq A q f) :=
          hstd_le
      _ = ENNReal.ofReal Cst.toReal *
          ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq A q f) := by
          rw [ENNReal.ofReal_toReal hCst_ne_top]
  have norm_bound
      {B : (k : ℕ) → WeakGridSpace.LevelBlock A k}
      {x : WeakGridSpace.BesovishSpace A q}
      (R : WeakGridSpace.LpGridRepresentation A
        (x : Lp ℂ p G.toWeakGridSpace.measure))
      (hRpos : SouzaPositiveRepresentation G s p hs hp hp_top R)
      (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
      (hRblock : R.block = B)
      (hle : ∀ k, WeakGridSpace.blockLvlCoeff (A := A) B k ≤
        WeakGridSpace.blockLvlCoeff (A := A) Rstd.block k)
      (_hBfin : WeakGridSpace.AbstractFinitePQCost (A := A) (q := q) B) :
      souzaPositiveNorm G s p q hs hp hp_top x ≤
        ENNReal.ofReal Cst.toReal *
          ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq A q f) := by
    have hRcost :
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
          (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal := by
      calc
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R
            = WeakGridSpace.abstractPQCost (A := A) (q := q) B :=
              cost_eq_block R hRblock
        _ ≤ WeakGridSpace.abstractPQCost (A := A) (q := q) Rstd.block :=
            abstractPQCost_le_of_blockLvlCoeff_le hle hRstd_block_fin
        _ = WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rstd :=
            hRstd_cost_eq_block.symm
        _ ≤ (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal :=
            hRstd_cost
    have hRenn :
        WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := q) R ≤
          ENNReal.ofReal
            (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal :=
      pqCostENNReal_le_of_finitePQCost_pqCost_le R hRfin hRcost
    have hnorm_std :
        souzaPositiveNorm G s p q hs hp hp_top x ≤
          ENNReal.ofReal
            (StandardAtomicRepresentation.standardRepresentationNorm G F s hs p hp_lt_top q fFun hfint).toReal := by
      unfold souzaPositiveNorm
      exact sInf_le ⟨R, hRpos, hRfin, hRenn⟩
    exact hnorm_std.trans hstd_target
  refine ⟨u, v, w, r,
    ⟨RrePos, hRrePos_positive⟩,
    ⟨RreNeg, hRreNeg_positive⟩,
    ⟨RimPos, hRimPos_positive⟩,
    ⟨RimNeg, hRimNeg_positive⟩,
    hdecomp, ?_, ?_, ?_, ?_⟩
  · exact norm_bound RrePos hRrePos_positive hRrePos_fin hRrePos_block
      hRePos_level_le hRePos_fin
  · exact norm_bound RreNeg hRreNeg_positive hRreNeg_fin hRreNeg_block
      hReNeg_level_le hReNeg_fin
  · exact norm_bound RimPos hRimPos_positive hRimPos_fin hRimPos_block
      hImPos_level_le hImPos_fin
  · exact norm_bound RimNeg hRimNeg_positive hRimNeg_fin hRimNeg_block
      hImNeg_level_le hImNeg_fin

/--
The positive cone `C_+(β)` in the ambient complex `L^β` space: these are the
classes which admit an almost everywhere nonnegative real representative.
-/
def LpNonnegativeCone
    (G : GoodGridSpace (α := α)) (β : ℝ≥0∞) :
    Set (Lp ℂ β G.toWeakGridSpace.measure) :=
  { f | ∀ᵐ x ∂G.toWeakGridSpace.measure,
      ∃ c : ℝ, 0 ≤ c ∧ (f : α → ℂ) x = (c : ℂ) }

/-- The zero `L^β` class lies in the nonnegative cone. -/
theorem zero_mem_LpNonnegativeCone
    (G : GoodGridSpace (α := α)) (β : ℝ≥0∞) :
    (0 : Lp ℂ β G.toWeakGridSpace.measure) ∈ LpNonnegativeCone G β := by
  filter_upwards [MeasureTheory.Lp.coeFn_zero ℂ β G.toWeakGridSpace.measure] with x hx
  exact ⟨0, le_rfl, by simpa using hx⟩

/--
The Souza-Besov positive cone, viewed as a subset of the ambient `L^β` space.
-/
def SouzaPositiveConeInLbeta
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)] :
    Set (Lp ℂ β G.toWeakGridSpace.measure) :=
  { fp | ∃ f : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s β hs hβ hβ_top) q,
      SouzaPositiveElement G s β q hs hβ hβ_top f ∧
        (f : Lp ℂ β G.toWeakGridSpace.measure) = fp }

/-- The zero `L^β` class lies in the ambient Souza-Besov positive cone. -/
theorem zero_mem_SouzaPositiveConeInLbeta
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)] :
    (0 : Lp ℂ β G.toWeakGridSpace.measure) ∈
      SouzaPositiveConeInLbeta G s β q hs hβ hβ_top := by
  exact ⟨0, souzaPositiveElement_zero G s β q hs hβ hβ_top, rfl⟩

private noncomputable def souzaIndicatorCellLevelBlock
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) (a : ℝ) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) Q.level where
  coeff := fun P =>
    if P = (⟨Q.cell, Q.mem⟩ :
        WeakGridSpace.LevelCell G.toWeakGridSpace Q.level) then
      (a : ℂ) / souzaCanonicalLocalAtom G s p Q
    else
      0
  atom := fun P => souzaCanonicalLocalAtom G s p (goodGridCellOfLevelCell G P)
  atom_mem := fun P =>
    souzaCanonicalLocalAtom_mem G s p hs hp hp_top
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace Q.level P)

private theorem souzaIndicatorCellLevelBlock_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) {a : ℝ} (ha : 0 ≤ a) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (souzaIndicatorCellLevelBlock G s p hs hp hp_top Q a) := by
  intro P
  by_cases hP : P = (⟨Q.cell, Q.mem⟩ :
      WeakGridSpace.LevelCell G.toWeakGridSpace Q.level)
  · subst P
    let r : ℝ := (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹)
    have hr_pos : 0 < r := by
      simpa [r] using souzaCanonicalLocalAtom_pos G s p Q
    refine ⟨a / r, div_nonneg ha hr_pos.le, ?_, ?_⟩
    · simp [souzaIndicatorCellLevelBlock, souzaCanonicalLocalAtom, r]
    · simpa [souzaIndicatorCellLevelBlock, goodGridCellOfLevelCell] using
        souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace Q.level
            (⟨Q.cell, Q.mem⟩ :
              WeakGridSpace.LevelCell G.toWeakGridSpace Q.level))
  · refine ⟨0, le_rfl, ?_, ?_⟩
    · simp [souzaIndicatorCellLevelBlock, hP]
    · simpa [souzaIndicatorCellLevelBlock, goodGridCellOfLevelCell] using
        souzaCanonicalLocalAtom_toFunction G s p hs hp hp_top
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace Q.level P)

private theorem souzaIndicatorCellLevelBlock_toLp
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] (Q : GoodGridCell G) (a : ℝ) :
    (souzaIndicatorCellLevelBlock G s p hs hp hp_top Q a).toLp
        (souzaAtomFamily G s p hs hp hp_top) =
      MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
        (G.grid.grid.measurable Q.level Q.cell Q.mem)
        (GoodGridCell.measure_ne_top Q) (a : ℂ) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Qw : WeakGridSpace.LevelCell G.toWeakGridSpace Q.level := ⟨Q.cell, Q.mem⟩
  let B := souzaIndicatorCellLevelBlock G s p hs hp hp_top Q a
  have hcanon_ne : souzaCanonicalLocalAtom G s p Q ≠ 0 := by
    have hpos := souzaCanonicalLocalAtom_pos G s p Q
    simp [souzaCanonicalLocalAtom, hpos.ne']
  apply MeasureTheory.Lp.ext
  refine (WeakGridSpace.LevelBlock.coeFn_toLp A B).trans ?_
  have hpoint :
      B.toFunLt A =ᵐ[G.toWeakGridSpace.measure] Q.cell.indicator (fun _ => (a : ℂ)) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx : x ∈ Q.cell
    · have hsum :
          B.toFunLt A x =
            B.coeff Qw *
              A.toFunction
                (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace Q.level Qw)
                (B.atom Qw) x := by
        unfold WeakGridSpace.LevelBlock.toFunLt
        exact Finset.sum_eq_single Qw
          (by
            intro P _ hP
            have hPQ : P ≠ Qw := hP
            have hPQ' :
                P ≠ (⟨Q.cell, Q.mem⟩ :
                  WeakGridSpace.LevelCell G.toWeakGridSpace Q.level) := by
              simpa [Qw] using hPQ
            simp [B, souzaIndicatorCellLevelBlock, hPQ'])
          (by intro hnot; exact False.elim (hnot (by simp [Qw])))
      rw [hsum]
      rw [Set.indicator_of_mem hx]
      dsimp [B, souzaIndicatorCellLevelBlock]
      rw [if_pos (by simp [Qw])]
      dsimp [A, WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily,
        souzaLocalVectorSpace, canonicalSouzaAtom, souzaCanonicalLocalAtom,
        goodGridCellOfLevelCell, WeakGridSpace.levelCellToWeakGridCell, Qw]
      rw [Set.indicator_of_mem hx]
      have hden :
          (((G.grid.μ Q.cell).toReal ^ (s - p.toReal⁻¹) : ℝ) : ℂ) ≠ 0 := by
        simpa [souzaCanonicalLocalAtom] using hcanon_ne
      exact div_mul_cancel₀ (a : ℂ) hden
    · have hsum : B.toFunLt A x = 0 := by
        unfold WeakGridSpace.LevelBlock.toFunLt
        refine Finset.sum_eq_zero ?_
        intro P hP
        by_cases hPQ : P = Qw
        · subst P
          dsimp [B, souzaIndicatorCellLevelBlock]
          rw [if_pos (by simp [Qw])]
          dsimp [A, WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily,
            souzaLocalVectorSpace, canonicalSouzaAtom, souzaCanonicalLocalAtom,
            goodGridCellOfLevelCell, WeakGridSpace.levelCellToWeakGridCell, Qw]
          simp [hx]
        · have hPQ' :
              P ≠ (⟨Q.cell, Q.mem⟩ :
                WeakGridSpace.LevelCell G.toWeakGridSpace Q.level) := by
            simpa [Qw] using hPQ
          simp [B, souzaIndicatorCellLevelBlock, hPQ']
      rw [hsum]
      simp [hx]
  exact hpoint.trans
    (MeasureTheory.indicatorConstLp_coeFn (μ := G.toWeakGridSpace.measure)
      (p := p) (hs := G.grid.grid.measurable Q.level Q.cell Q.mem)
      (hμs := GoodGridCell.measure_ne_top Q) (c := (a : ℂ))).symm

private theorem indicatorConstLp_cell_mem_SouzaPositiveConeInLbeta
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)]
    (Q : GoodGridCell G) {a : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
        (G.grid.grid.measurable Q.level Q.cell Q.mem)
        (GoodGridCell.measure_ne_top Q) (a : ℂ) ∈
      SouzaPositiveConeInLbeta G s β q hs hβ hβ_top := by
  let B := souzaIndicatorCellLevelBlock G s β hs hβ hβ_top Q a
  let f : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s β hs hβ hβ_top) q :=
    ⟨B.toLp (souzaAtomFamily G s β hs hβ hβ_top),
      WeakGridSpace.levelBlock_toLp_mem_besovish
        (A := souzaAtomFamily G s β hs hβ hβ_top) (q := q) B⟩
  refine ⟨f, ?_, ?_⟩
  · let A := souzaAtomFamily G s β hs hβ hβ_top
    let R : WeakGridSpace.LpGridRepresentation A (B.toLp A) := by
      classical
      refine
        { block := fun k =>
            if h : k = Q.level then
              cast (congrArg (WeakGridSpace.LevelBlock A) h.symm) B
            else
              souzaPositiveZeroLevelBlock G s β hs hβ hβ_top (k := k)
          hasSum := ?_ }
      have hterm :
          (fun k : ℕ =>
            ((if h : k = Q.level then
              cast (congrArg (WeakGridSpace.LevelBlock A) h.symm) B
            else
              souzaPositiveZeroLevelBlock G s β hs hβ hβ_top (k := k)) :
                WeakGridSpace.LevelBlock A k).toLp A)
              = fun k => if k = Q.level then B.toLp A else 0 := by
        funext k
        by_cases hk : k = Q.level
        · subst k
          simp [A]
        · simp [hk, A, souzaPositiveZeroLevelBlock_toLp G s β hs hβ hβ_top]
      simpa [hterm] using hasSum_ite_eq Q.level (B.toLp A)
    refine ⟨R, ?_⟩
    intro k
    by_cases hk : k = Q.level
    · subst k
      simpa [R, A, B] using
        souzaIndicatorCellLevelBlock_positive G s β hs hβ hβ_top Q ha
    · simpa [R, A, hk] using
        souzaPositiveZeroLevelBlock_positive G s β hs hβ hβ_top (k := k)
  · change B.toLp (souzaAtomFamily G s β hs hβ hβ_top) =
      MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
        (G.grid.grid.measurable Q.level Q.cell Q.mem)
        (GoodGridCell.measure_ne_top Q) (a : ℂ)
    exact souzaIndicatorCellLevelBlock_toLp G s β hs hβ hβ_top Q a

/-- The ambient Souza positive cone is closed under addition. -/
theorem SouzaPositiveConeInLbeta.add
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)]
    {x y : Lp ℂ β G.toWeakGridSpace.measure}
    (hx : x ∈ SouzaPositiveConeInLbeta G s β q hs hβ hβ_top)
    (hy : y ∈ SouzaPositiveConeInLbeta G s β q hs hβ hβ_top) :
    x + y ∈ SouzaPositiveConeInLbeta G s β q hs hβ hβ_top := by
  rcases hx with ⟨fx, hfx, rfl⟩
  rcases hy with ⟨fy, hfy, rfl⟩
  exact ⟨fx + fy, souzaPositiveElement_add G s β q hs hβ hβ_top hfx hfy, rfl⟩

/-- The ambient Souza positive cone is closed under nonnegative real scalars. -/
theorem SouzaPositiveConeInLbeta.smul_nonneg
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)]
    {a : ℝ} (ha : 0 ≤ a)
    {x : Lp ℂ β G.toWeakGridSpace.measure}
    (hx : x ∈ SouzaPositiveConeInLbeta G s β q hs hβ hβ_top) :
    (a : ℂ) • x ∈ SouzaPositiveConeInLbeta G s β q hs hβ hβ_top := by
  rcases hx with ⟨fx, hfx, rfl⟩
  exact ⟨(a : ℂ) • fx,
    souzaPositiveElement_smul_nonneg G s β q hs hβ hβ_top ha hfx, rfl⟩

private theorem closure_SouzaPositiveConeInLbeta_add
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)]
    {x y : Lp ℂ β G.toWeakGridSpace.measure}
    (hx : x ∈ closure (SouzaPositiveConeInLbeta G s β q hs hβ hβ_top))
    (hy : y ∈ closure (SouzaPositiveConeInLbeta G s β q hs hβ hβ_top)) :
    x + y ∈ closure (SouzaPositiveConeInLbeta G s β q hs hβ hβ_top) :=
  map_mem_closure₂ continuous_add hx hy fun _ hx' _ hy' =>
    SouzaPositiveConeInLbeta.add G s β q hs hβ hβ_top hx' hy'

private def gridGeneratingSemiringSets
    (G : GoodGridSpace (α := α)) : Set (Set α) :=
  insert ∅ (gridGeneratingSets G)

private theorem gridGeneratingSemiringSets_inter_mem
    (G : GoodGridSpace (α := α)) :
    ∀ u ∈ gridGeneratingSemiringSets G, ∀ v ∈ gridGeneratingSemiringSets G,
      u ∩ v ∈ gridGeneratingSemiringSets G := by
  intro u hu v hv
  rcases hu with rfl | hu
  · simp [gridGeneratingSemiringSets]
  rcases hv with rfl | hv
  · simp [gridGeneratingSemiringSets]
  by_cases huv : (u ∩ v).Nonempty
  · exact Or.inr ((isPiSystem_gridGeneratingSets G) u hu v hv huv)
  · left
    exact Set.not_nonempty_iff_eq_empty.mp huv

private theorem gridCell_diff_eq_sUnion_finset
    (G : GoodGridSpace (α := α))
    {n m : ℕ} {Q P : Set α}
    (hQ : Q ∈ G.grid.grid.partitions n)
    (hP : P ∈ G.grid.grid.partitions m) :
    ∃ I : Finset (Set α), ↑I ⊆ gridGeneratingSemiringSets G ∧
      Set.PairwiseDisjoint (I : Set (Set α)) id ∧ Q \ P = ⋃₀ I := by
  classical
  rcases le_total n m with hnm | hmn
  · rcases G.grid.partition_subset_or_disjoint_of_le n m hnm Q hQ P hP with hPQ | hdisj
    · let I : Finset (Set α) :=
        (G.grid.grid.partitions m).filter fun R => R ⊆ Q ∧ R ≠ P
      refine ⟨I, ?_, ?_, ?_⟩
      · intro R hR
        right
        exact Set.mem_iUnion.mpr ⟨m, (Finset.mem_filter.mp hR).1⟩
      · intro R hR S hS hRS
        exact G.grid.grid.disjoint m R S
          (Finset.mem_filter.mp hR).1 (Finset.mem_filter.mp hS).1 hRS
      · ext x
        constructor
        · rintro ⟨hxQ, hxP⟩
          have hxcover : x ∈ ⋃ R ∈ G.grid.grid.partitions m, R := by
            rw [G.grid.grid.covering m]
            trivial
          rcases Set.mem_iUnion.mp hxcover with ⟨R, hxR'⟩
          rcases Set.mem_iUnion.mp hxR' with ⟨hR, hxR⟩
          have hRQ : R ⊆ Q := by
            rcases G.grid.partition_subset_or_disjoint_of_le n m hnm Q hQ R hR with hsub | hdisjRQ
            · exact hsub
            · exact False.elim ((Set.disjoint_left.mp hdisjRQ) hxR hxQ)
          have hRP : R ≠ P := by
            intro h
            exact hxP (h ▸ hxR)
          have hRI : R ∈ I := by
            simp [I, hR, hRQ, hRP]
          exact Set.mem_sUnion_of_mem hxR hRI
        · intro hx
          rcases Set.mem_sUnion.mp hx with ⟨R, hRI, hxR⟩
          have hR : R ∈ G.grid.grid.partitions m := (Finset.mem_filter.mp hRI).1
          have hRQ : R ⊆ Q := (Finset.mem_filter.mp hRI).2.1
          have hRP : R ≠ P := (Finset.mem_filter.mp hRI).2.2
          refine ⟨hRQ hxR, ?_⟩
          intro hxP
          exact (Set.disjoint_left.mp
            (G.grid.grid.disjoint m R P hR hP hRP) hxR hxP).elim
    · refine ⟨{Q}, ?_, ?_, ?_⟩
      · intro R hR
        rw [Finset.mem_singleton.mp hR]
        right
        exact Set.mem_iUnion.mpr ⟨n, hQ⟩
      · simp
      · rw [hdisj.symm.sdiff_eq_left]
        simp
  · rcases G.grid.partition_subset_or_disjoint_of_le m n hmn P hP Q hQ with hQP | hdisj
    · refine ⟨∅, ?_, ?_, ?_⟩
      · simp
      · simp
      · rw [Set.diff_eq_empty.mpr hQP]
        simp
    · refine ⟨{Q}, ?_, ?_, ?_⟩
      · intro R hR
        rw [Finset.mem_singleton.mp hR]
        right
        exact Set.mem_iUnion.mpr ⟨n, hQ⟩
      · simp
      · rw [hdisj.sdiff_eq_left]
        simp

private theorem gridGeneratingSemiringSets_isSetSemiring
    (G : GoodGridSpace (α := α)) :
    MeasureTheory.IsSetSemiring (gridGeneratingSemiringSets G) where
  empty_mem := by simp [gridGeneratingSemiringSets]
  inter_mem := gridGeneratingSemiringSets_inter_mem G
  diff_eq_sUnion' := by
    intro u hu v hv
    rcases hu with rfl | hu
    · refine ⟨∅, ?_, ?_, ?_⟩ <;> simp
    rcases hv with rfl | hv
    · refine ⟨{u}, ?_, ?_, ?_⟩
      · intro R hR
        rw [Finset.mem_singleton.mp hR]
        exact Or.inr hu
      · simp
      · simp
    rcases Set.mem_iUnion.mp hu with ⟨n, hQ⟩
    rcases Set.mem_iUnion.mp hv with ⟨m, hP⟩
    exact gridCell_diff_eq_sUnion_finset G hQ hP

private theorem grid_generates_eq_generateFrom_gridGeneratingSemiringSets
    (G : GoodGridSpace (α := α)) :
    ‹MeasurableSpace α› =
      MeasurableSpace.generateFrom (gridGeneratingSemiringSets G) := by
  rw [gridGeneratingSemiringSets, MeasurableSpace.generateFrom_insert_empty]
  exact grid_generates_eq_generateFrom_gridGeneratingSets G

private theorem gridGeneratingSemiringSets_countable_cover
    (G : GoodGridSpace (α := α)) :
    ∃ D : Set (Set α), D.Countable ∧ D ⊆ gridGeneratingSemiringSets G ∧
      G.toWeakGridSpace.measure (⋃₀ D)ᶜ = 0 := by
  refine ⟨{Set.univ}, Set.countable_singleton Set.univ, ?_, ?_⟩
  · intro u hu
    rw [Set.mem_singleton_iff.mp hu]
    right
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    simp [G.grid.grid.first_partition_eq_univ]
  · simp

private theorem goodGridSpace_measure_ne_top
    (G : GoodGridSpace (α := α)) (u : Set α) :
    G.toWeakGridSpace.measure u ≠ ∞ := by
  haveI : MeasureTheory.IsFiniteMeasure G.toWeakGridSpace.measure := by
    dsimp [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
      WeakGridSpace.WeakGridSpace.measure]
    exact G.grid.isFinite
  exact (MeasureTheory.measure_lt_top G.toWeakGridSpace.measure u).ne

private theorem indicatorConstLp_congr_set
    {μ : Measure α} {p : ℝ≥0∞} {u v : Set α}
    (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hμu : μ u ≠ ∞) (hμv : μ v ≠ ∞) (c : ℂ)
    (huv : u = v) :
    MeasureTheory.indicatorConstLp (μ := μ) p hu hμu c =
      MeasureTheory.indicatorConstLp (μ := μ) p hv hμv c := by
  subst v
  congr

private theorem exists_gridSupClosure_symmDiff_lt
    (G : GoodGridSpace (α := α)) {u : Set α} (hu : MeasurableSet u)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ∈ supClosure (gridGeneratingSemiringSets G),
      G.toWeakGridSpace.measure (t ∆ u) < ε := by
  haveI : MeasureTheory.IsFiniteMeasure G.toWeakGridSpace.measure := by
    dsimp [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
      WeakGridSpace.WeakGridSpace.measure]
    exact G.grid.isFinite
  exact MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
    (μ := G.toWeakGridSpace.measure)
    (gridGeneratingSemiringSets_isSetSemiring G)
    (gridGeneratingSemiringSets_countable_cover G)
    (grid_generates_eq_generateFrom_gridGeneratingSemiringSets G)
    hu hε

private theorem gridFinset_sUnion_measurable
    (G : GoodGridSpace (α := α)) (I : Finset (Set α))
    (hIgrid : ∀ R ∈ I, R ∈ gridGeneratingSets G) :
    MeasurableSet (⋃₀ (I : Set (Set α))) := by
  rw [show ⋃₀ (I : Set (Set α)) = ⋃ R ∈ I, R by ext x; simp]
  exact Finset.measurableSet_biUnion I fun R hR => by
    rcases Set.mem_iUnion.mp (hIgrid R hR) with ⟨n, hn⟩
    exact G.grid.grid.measurable n R hn

private theorem indicatorConstLp_sUnion_finset_grid_mem_SouzaPositiveConeInLbeta
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)]
    (I : Finset (Set α))
    (hIgrid : ∀ R ∈ I, R ∈ gridGeneratingSets G)
    (hIdisj : Set.PairwiseDisjoint (I : Set (Set α)) id)
    {a : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
        (gridFinset_sUnion_measurable G I hIgrid)
        (goodGridSpace_measure_ne_top G (⋃₀ (I : Set (Set α))))
        (a : ℂ) ∈
      SouzaPositiveConeInLbeta G s β q hs hβ hβ_top := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure G.toWeakGridSpace.measure := by
    dsimp [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
      WeakGridSpace.WeakGridSpace.measure]
    exact G.grid.isFinite
  induction I using Finset.induction_on with
  | empty =>
      simpa using zero_mem_SouzaPositiveConeInLbeta G s β q hs hβ hβ_top
  | insert R I hRI ih =>
      have hRgrid : R ∈ gridGeneratingSets G :=
        hIgrid R (Finset.mem_insert_self R I)
      have hIgrid' : ∀ S ∈ I, S ∈ gridGeneratingSets G := by
        intro S hS
        exact hIgrid S (Finset.mem_insert_of_mem hS)
      have hIdisj' : Set.PairwiseDisjoint (I : Set (Set α)) id := by
        intro S hS T hT hST
        exact hIdisj (Finset.mem_insert_of_mem hS) (Finset.mem_insert_of_mem hT) hST
      have hRmeas : MeasurableSet R := by
        rcases Set.mem_iUnion.mp hRgrid with ⟨n, hn⟩
        exact G.grid.grid.measurable n R hn
      have hImeas :
          MeasurableSet (⋃₀ (I : Set (Set α))) :=
        gridFinset_sUnion_measurable G I hIgrid'
      have hdisjRI : Disjoint R (⋃₀ (I : Set (Set α))) := by
        refine Set.disjoint_left.mpr ?_
        intro x hxR hxU
        rcases Set.mem_sUnion.mp hxU with ⟨S, hS, hxS⟩
        have hRS : R ≠ S := by
          intro h
          exact hRI (h ▸ hS)
        have hRins : R ∈ ((insert R I : Finset (Set α)) : Set (Set α)) := by
          simp
        have hSins : S ∈ ((insert R I : Finset (Set α)) : Set (Set α)) := by
          simpa using (Finset.mem_insert_of_mem (show S ∈ I from hS))
        exact (Set.disjoint_left.mp
          (hIdisj hRins hSins hRS) hxR hxS).elim
      have hRmem :
          MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
              hRmeas (goodGridSpace_measure_ne_top G R)
              (a : ℂ) ∈
            SouzaPositiveConeInLbeta G s β q hs hβ hβ_top := by
        rcases Set.mem_iUnion.mp hRgrid with ⟨n, hn⟩
        simpa using
          indicatorConstLp_cell_mem_SouzaPositiveConeInLbeta
            G s β q hs hβ hβ_top ⟨n, R, hn⟩ ha
      have hImem :
          MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
              hImeas
              (goodGridSpace_measure_ne_top G (⋃₀ (I : Set (Set α))))
              (a : ℂ) ∈
            SouzaPositiveConeInLbeta G s β q hs hβ hβ_top := by
        simpa using ih hIgrid' hIdisj'
      have hUnion :
          ⋃₀ ((insert R I : Finset (Set α)) : Set (Set α)) =
            R ∪ ⋃₀ (I : Set (Set α)) := by
        simp
      have htarget_eq :
          MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
              (gridFinset_sUnion_measurable G (insert R I) hIgrid)
              (goodGridSpace_measure_ne_top G
                (⋃₀ ((insert R I : Finset (Set α)) : Set (Set α))))
              (a : ℂ) =
            MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
              (hRmeas.union hImeas)
              (goodGridSpace_measure_ne_top G (R ∪ ⋃₀ (I : Set (Set α))))
              (a : ℂ) :=
        indicatorConstLp_congr_set
          (gridFinset_sUnion_measurable G (insert R I) hIgrid)
          (hRmeas.union hImeas)
          (goodGridSpace_measure_ne_top G
            (⋃₀ ((insert R I : Finset (Set α)) : Set (Set α))))
          (goodGridSpace_measure_ne_top G (R ∪ ⋃₀ (I : Set (Set α))))
          (a : ℂ) hUnion
      rw [htarget_eq]
      rw [MeasureTheory.indicatorConstLp_disjoint_union
        (μ := G.toWeakGridSpace.measure) (p := β)
        hRmeas hImeas
        (goodGridSpace_measure_ne_top G R)
        (goodGridSpace_measure_ne_top G (⋃₀ (I : Set (Set α))))
        hdisjRI (a : ℂ)]
      exact SouzaPositiveConeInLbeta.add G s β q hs hβ hβ_top hRmem hImem

private theorem indicatorConstLp_supClosure_grid_mem_SouzaPositiveConeInLbeta
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)]
    {t : Set α} (ht : t ∈ supClosure (gridGeneratingSemiringSets G))
    (htm : MeasurableSet t) {a : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
        htm (goodGridSpace_measure_ne_top G t) (a : ℂ) ∈
      SouzaPositiveConeInLbeta G s β q hs hβ hβ_top := by
  classical
  let hSemiring := gridGeneratingSemiringSets_isSetSemiring G
  rcases (hSemiring.mem_supClosure_iff).mp ht with ⟨P, hPsubset⟩
  let I : Finset (Set α) := P.parts
  have hIgrid : ∀ R ∈ I, R ∈ gridGeneratingSets G := by
    intro R hR
    have hRsemiring : R ∈ gridGeneratingSemiringSets G := hPsubset hR
    rcases hRsemiring with hRempty | hRgrid
    · exfalso
      exact P.bot_notMem (by simpa [I, hRempty] using hR)
    · exact hRgrid
  have hIeq : ⋃₀ (I : Set (Set α)) = t := by
    exact (Finset.sup_id_set_eq_sUnion P.parts).symm.trans P.sup_parts
  have hImem :
      MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
          (gridFinset_sUnion_measurable G I hIgrid)
          (goodGridSpace_measure_ne_top G (⋃₀ (I : Set (Set α))))
          (a : ℂ) ∈
        SouzaPositiveConeInLbeta G s β q hs hβ hβ_top :=
    indicatorConstLp_sUnion_finset_grid_mem_SouzaPositiveConeInLbeta
      G s β q hs hβ hβ_top I hIgrid P.disjoint ha
  have hcongr :
      MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
          (gridFinset_sUnion_measurable G I hIgrid)
          (goodGridSpace_measure_ne_top G (⋃₀ (I : Set (Set α))))
          (a : ℂ) =
        MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
          htm (goodGridSpace_measure_ne_top G t) (a : ℂ) :=
    indicatorConstLp_congr_set
      (gridFinset_sUnion_measurable G I hIgrid) htm
      (goodGridSpace_measure_ne_top G (⋃₀ (I : Set (Set α))))
      (goodGridSpace_measure_ne_top G t) (a : ℂ) hIeq
  rwa [← hcongr]

private theorem indicatorConstLp_nonneg_mem_closure_SouzaPositiveConeInLbeta
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)]
    {u : Set α} (hu : MeasurableSet u) {a : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
        hu (goodGridSpace_measure_ne_top G u) (a : ℂ) ∈
      closure (SouzaPositiveConeInLbeta G s β q hs hβ hβ_top) := by
  classical
  let δ : ℕ → ℝ≥0∞ := fun n => (n : ℝ≥0∞)⁻¹
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    simp [δ]
  have happrox :
      ∀ n, ∃ t ∈ supClosure (gridGeneratingSemiringSets G),
        G.toWeakGridSpace.measure (t ∆ u) < δ n := by
    intro n
    exact exists_gridSupClosure_symmDiff_lt G hu (hδpos n)
  choose T hTsup hTdist using happrox
  have hTmeas : ∀ n, MeasurableSet (T n) := by
    intro n
    rw [grid_generates_eq_generateFrom_gridGeneratingSemiringSets G]
    exact measurableSet_generateFrom_of_mem_supClosure (hTsup n)
  have hδtend : Filter.Tendsto δ Filter.atTop (𝓝 0) := by
    simpa [δ] using ENNReal.tendsto_inv_nat_nhds_zero
  have hsymm_tend :
      Filter.Tendsto (fun n => G.toWeakGridSpace.measure (T n ∆ u))
        Filter.atTop (𝓝 0) := by
    refine ENNReal.tendsto_nhds_zero.2 ?_
    intro ε hε
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hδtend ε hε] with n hn
    exact (hTdist n).le.trans hn
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n =>
      MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) β
        (hTmeas n) (goodGridSpace_measure_ne_top G (T n)) (a : ℂ), ?_, ?_⟩
  · intro n
    exact indicatorConstLp_supClosure_grid_mem_SouzaPositiveConeInLbeta
      G s β q hs hβ hβ_top (hTsup n) (hTmeas n) ha
  · exact MeasureTheory.tendsto_indicatorConstLp_set
      (μ := G.toWeakGridSpace.measure) (p := β) (s := u)
      (hs := hu) (hμs := goodGridSpace_measure_ne_top G u)
      (t := T) (ht := hTmeas)
      (hμt := fun n => goodGridSpace_measure_ne_top G (T n))
      hβ_top hsymm_tend

private theorem ofReal_simpleFunc_toLp_nonneg_mem_closure_SouzaPositiveConeInLbeta
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)]
    (f : MeasureTheory.SimpleFunc α ℝ) (hf_nonneg : 0 ≤ f)
    (hf_memLp : MeasureTheory.MemLp (f : α → ℝ) β G.toWeakGridSpace.measure) :
    (Complex.ofRealCLM.compLpL β G.toWeakGridSpace.measure)
        ((f.toLp hf_memLp : MeasureTheory.Lp.simpleFunc ℝ β G.toWeakGridSpace.measure) :
          Lp ℝ β G.toWeakGridSpace.measure) ∈
      closure (SouzaPositiveConeInLbeta G s β q hs hβ hβ_top) := by
  classical
  let μ := G.toWeakGridSpace.measure
  let C := closure (SouzaPositiveConeInLbeta G s β q hs hβ hβ_top)
  let P : MeasureTheory.SimpleFunc α ℝ → Prop := fun f =>
    ∀ hf_memLp : MeasureTheory.MemLp (f : α → ℝ) β μ, 0 ≤ f →
      (Complex.ofRealCLM.compLpL β μ)
          ((f.toLp hf_memLp : MeasureTheory.Lp.simpleFunc ℝ β μ) :
            Lp ℝ β μ) ∈ C
  suffices hP : P f by
    exact hP hf_memLp hf_nonneg
  refine MeasureTheory.SimpleFunc.induction (motive := P)
    (fun a {u} hu => ?_) (fun {f g} hdisj hf_ih hg_ih => ?_) f
  · intro hf_memLp hf_nonneg
    by_cases hune : u.Nonempty
    · have ha : 0 ≤ a := by
        rcases hune with ⟨x, hx⟩
        simpa [MeasureTheory.SimpleFunc.coe_piecewise, hx] using hf_nonneg x
      have htarget :
          (Complex.ofRealCLM.compLpL β μ)
              (((MeasureTheory.SimpleFunc.piecewise u hu
                  (MeasureTheory.SimpleFunc.const α a)
                  (MeasureTheory.SimpleFunc.const α 0)).toLp hf_memLp :
                  MeasureTheory.Lp.simpleFunc ℝ β μ) :
                Lp ℝ β μ) =
            MeasureTheory.indicatorConstLp (μ := μ) β hu
              (goodGridSpace_measure_ne_top G u) (a : ℂ) := by
        rw [Lp.ext_iff]
        filter_upwards
          [ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM
            (((MeasureTheory.SimpleFunc.piecewise u hu
                (MeasureTheory.SimpleFunc.const α a)
                (MeasureTheory.SimpleFunc.const α 0)).toLp hf_memLp :
                MeasureTheory.Lp.simpleFunc ℝ β μ) :
              Lp ℝ β μ),
           MeasureTheory.MemLp.coeFn_toLp hf_memLp,
           MeasureTheory.indicatorConstLp_coeFn
              (μ := μ) (p := β) (hs := hu)
              (hμs := goodGridSpace_measure_ne_top G u) (c := (a : ℂ))] with x hmap htoLp hind
        rw [hmap, htoLp, hind]
        by_cases hx : x ∈ u <;> simp [MeasureTheory.SimpleFunc.coe_piecewise, hx]
      rw [htarget]
      exact indicatorConstLp_nonneg_mem_closure_SouzaPositiveConeInLbeta
        G s β q hs hβ hβ_top hu ha
    · have hu_empty : u = ∅ := Set.not_nonempty_iff_eq_empty.mp hune
      have htarget :
          (Complex.ofRealCLM.compLpL β μ)
              (((MeasureTheory.SimpleFunc.piecewise u hu
                  (MeasureTheory.SimpleFunc.const α a)
                  (MeasureTheory.SimpleFunc.const α 0)).toLp hf_memLp :
                  MeasureTheory.Lp.simpleFunc ℝ β μ) :
                Lp ℝ β μ) =
            (0 : Lp ℂ β μ) := by
        rw [Lp.ext_iff]
        filter_upwards
          [ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM
            (((MeasureTheory.SimpleFunc.piecewise u hu
                (MeasureTheory.SimpleFunc.const α a)
                (MeasureTheory.SimpleFunc.const α 0)).toLp hf_memLp :
                MeasureTheory.Lp.simpleFunc ℝ β μ) :
              Lp ℝ β μ),
           MeasureTheory.MemLp.coeFn_toLp hf_memLp,
           MeasureTheory.Lp.coeFn_zero ℂ β μ] with x hmap htoLp hzero
        rw [hmap, htoLp, hzero]
        simp [hu_empty]
      rw [htarget]
      exact subset_closure (zero_mem_SouzaPositiveConeInLbeta G s β q hs hβ hβ_top)
  · intro hfg_memLp hfg_nonneg
    have hmem :
        MeasureTheory.MemLp (f : α → ℝ) β μ ∧
          MeasureTheory.MemLp (g : α → ℝ) β μ :=
      (MeasureTheory.memLp_add_of_disjoint (p := β) (μ := μ)
        hdisj f.stronglyMeasurable g.stronglyMeasurable).1 hfg_memLp
    have hf_nonneg : 0 ≤ f := by
      intro x
      by_cases hfx : f x = 0
      · simp [hfx]
      · have hgx : g x = 0 := by
          by_contra hgx
          exact (Set.disjoint_left.mp hdisj hfx hgx)
        simpa [MeasureTheory.SimpleFunc.coe_add, hgx] using hfg_nonneg x
    have hg_nonneg : 0 ≤ g := by
      intro x
      by_cases hgx : g x = 0
      · simp [hgx]
      · have hfx : f x = 0 := by
          by_contra hfx
          exact (Set.disjoint_left.mp hdisj hfx hgx)
        simpa [MeasureTheory.SimpleFunc.coe_add, hfx] using hfg_nonneg x
    have htoLp_add :
        (((f + g).toLp hfg_memLp :
            MeasureTheory.Lp.simpleFunc ℝ β μ) :
          Lp ℝ β μ) =
          ((f.toLp hmem.1 : MeasureTheory.Lp.simpleFunc ℝ β μ) :
            Lp ℝ β μ) +
            ((g.toLp hmem.2 : MeasureTheory.Lp.simpleFunc ℝ β μ) :
              Lp ℝ β μ) := by
      rw [MeasureTheory.Lp.simpleFunc.toLp_eq_toLp,
        MeasureTheory.Lp.simpleFunc.toLp_eq_toLp,
        MeasureTheory.Lp.simpleFunc.toLp_eq_toLp]
      rw [← MeasureTheory.MemLp.toLp_add hmem.1 hmem.2]
      exact (MeasureTheory.MemLp.toLp_eq_toLp_iff hfg_memLp
        (hmem.1.add hmem.2)).2 (Filter.Eventually.of_forall fun _ => rfl)
    rw [htoLp_add, map_add]
    exact closure_SouzaPositiveConeInLbeta_add G s β q hs hβ hβ_top
      (hf_ih hmem.1 hf_nonneg) (hg_ih hmem.2 hg_nonneg)

private theorem ofReal_Lp_simpleFunc_nonneg_mem_closure_SouzaPositiveConeInLbeta
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)]
    (f : MeasureTheory.Lp.simpleFunc ℝ β G.toWeakGridSpace.measure)
    (hf_nonneg : 0 ≤ f) :
    (Complex.ofRealCLM.compLpL β G.toWeakGridSpace.measure)
        (f : Lp ℝ β G.toWeakGridSpace.measure) ∈
      closure (SouzaPositiveConeInLbeta G s β q hs hβ hβ_top) := by
  classical
  rcases MeasureTheory.Lp.simpleFunc.exists_simpleFunc_nonneg_ae_eq hf_nonneg with
    ⟨f', hf'_nonneg, hf_eq⟩
  have hf'_memLp : MeasureTheory.MemLp (f' : α → ℝ) β G.toWeakGridSpace.measure :=
    MeasureTheory.MemLp.ae_eq hf_eq
      (MeasureTheory.Lp.memLp (f : Lp ℝ β G.toWeakGridSpace.measure))
  have hreal_eq :
      ((f'.toLp hf'_memLp : MeasureTheory.Lp.simpleFunc ℝ β G.toWeakGridSpace.measure) :
        Lp ℝ β G.toWeakGridSpace.measure) =
        (f : Lp ℝ β G.toWeakGridSpace.measure) := by
    rw [Lp.ext_iff]
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hf'_memLp, hf_eq] with x htoLp hf
    rw [htoLp]
    exact hf.symm
  rw [← hreal_eq]
  exact ofReal_simpleFunc_toLp_nonneg_mem_closure_SouzaPositiveConeInLbeta
    G s β q hs hβ hβ_top f' hf'_nonneg hf'_memLp

/--
The positive cone of the Souza-Besov space is strongly dense in the
nonnegative cone of the ambient `L^β` space.

For `1 ≤ β < ∞`, every nonnegative `L^β` function lies in the strong `L^β`
closure of the Souza-Besov positive cone.
-/
theorem souzaPositiveCone_dense_in_LpNonnegativeCone
    (G : GoodGridSpace (α := α)) (s : ℝ) (β q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 1 ≤ β) (hβ_top : β ≠ ∞)
    [Fact (1 ≤ β)] [Fact (1 ≤ q)] :
    LpNonnegativeCone G β ⊆
      closure (SouzaPositiveConeInLbeta G s β q hs hβ hβ_top) := by
  intro f hf
  let μ := G.toWeakGridSpace.measure
  let fre : Lp ℝ β μ := (Complex.reCLM.compLpL β μ) f
  have hfre_nonneg : 0 ≤ fre := by
    rw [← MeasureTheory.Lp.coeFn_nonneg]
    filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.reCLM f, hf] with x hre hx
    rcases hx with ⟨c, hc, hfx⟩
    rw [hre, hfx]
    simpa using hc
  have hreconstruct :
      (Complex.ofRealCLM.compLpL β μ) fre = f := by
    rw [Lp.ext_iff]
    filter_upwards
      [ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM fre,
       ContinuousLinearMap.coeFn_compLpL Complex.reCLM f,
       hf] with x hof hre hx
    rcases hx with ⟨c, _hc, hfx⟩
    rw [hof, hre, hfx]
    simp
  have hdense :
      DenseRange
        (MeasureTheory.Lp.simpleFunc.coeSimpleFuncNonnegToLpNonneg
          β μ ℝ) :=
    MeasureTheory.Lp.simpleFunc.denseRange_coeSimpleFuncNonnegToLpNonneg
      β μ ℝ hβ_top
  have hfre_dense :
      (⟨fre, hfre_nonneg⟩ :
        { g : Lp ℝ β μ // 0 ≤ g }) ∈
        closure (Set.range
          (MeasureTheory.Lp.simpleFunc.coeSimpleFuncNonnegToLpNonneg
            β μ ℝ)) :=
    hdense ⟨fre, hfre_nonneg⟩
  rw [mem_closure_iff_seq_limit] at hfre_dense
  rcases hfre_dense with ⟨F, hF_range, hF_tend⟩
  have hF_mem_closure :
      ∀ n : ℕ,
        (Complex.ofRealCLM.compLpL β μ) (F n).1 ∈
          closure (SouzaPositiveConeInLbeta G s β q hs hβ hβ_top) := by
    intro n
    rcases hF_range n with ⟨Fsimple, hFsimple⟩
    have hval :
        (Fsimple.1 : Lp ℝ β μ) = (F n).1 := by
      simpa [MeasureTheory.Lp.simpleFunc.coeSimpleFuncNonnegToLpNonneg]
        using congrArg Subtype.val hFsimple
    rw [← hval]
    exact ofReal_Lp_simpleFunc_nonneg_mem_closure_SouzaPositiveConeInLbeta
      G s β q hs hβ hβ_top Fsimple.1 Fsimple.2
  have hF_tend_val :
      Filter.Tendsto (fun n : ℕ => (F n).1) Filter.atTop (𝓝 fre) :=
    (continuous_subtype_val.tendsto ⟨fre, hfre_nonneg⟩).comp hF_tend
  have hF_tend_complex :
      Filter.Tendsto
        (fun n : ℕ => (Complex.ofRealCLM.compLpL β μ) (F n).1)
        Filter.atTop (𝓝 ((Complex.ofRealCLM.compLpL β μ) fre)) :=
    ((Complex.ofRealCLM.compLpL β μ).continuous.tendsto fre).comp hF_tend_val
  exact isClosed_closure.mem_of_tendsto
    (by simpa [hreconstruct] using hF_tend_complex)
    (Filter.Eventually.of_forall hF_mem_closure)

/-- Two sets agree up to a null set when their symmetric difference is null. -/
def aeEqSet (μ : Measure α) (S T : Set α) : Prop :=
  μ ((S \ T) ∪ (T \ S)) = 0

/-- A set is, modulo null sets, a countable union of good-grid cells. -/
def IsAECountableUnionOfGoodGridCells
    (G : GoodGridSpace (α := α)) (S : Set α) : Prop :=
  ∃ cells : Set (GoodGridCell G),
    cells.Countable ∧ aeEqSet G.grid.μ S (⋃ Q ∈ cells, Q.cell)

/-- A set is, modulo null sets, a nonempty countable union of good-grid cells. -/
def IsAENonemptyCountableUnionOfGoodGridCells
    (G : GoodGridSpace (α := α)) (S : Set α) : Prop :=
  ∃ cells : Set (GoodGridCell G),
    cells.Nonempty ∧ cells.Countable ∧ aeEqSet G.grid.μ S (⋃ Q ∈ cells, Q.cell)

private def goodGridCellFromSigma
    (G : GoodGridSpace (α := α))
    (Q : Σ k : ℕ, WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    GoodGridCell G where
  level := Q.1
  cell := Q.2.1
  mem := Q.2.2

private theorem goodGridCellFromSigma_surjective
    (G : GoodGridSpace (α := α)) :
    Function.Surjective (goodGridCellFromSigma G) := by
  intro Q
  exact ⟨⟨Q.level, ⟨Q.cell, Q.mem⟩⟩, rfl⟩

private theorem countable_goodGridCell (G : GoodGridSpace (α := α)) :
    Countable (GoodGridCell G) := by
  classical
  exact (goodGridCellFromSigma_surjective G).countable

private def souzaPositiveRepresentationActiveCells
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g) :
    Set (GoodGridCell G) :=
  { Q | (R.block Q.level).coeff Q.toLevelCell ≠ 0 }

private theorem aeEqSet_of_ae_mem_iff
    {μ : Measure α} {S T : Set α}
    (h : ∀ᵐ x ∂μ, (x ∈ S ↔ x ∈ T)) :
    aeEqSet μ S T := by
  rw [aeEqSet]
  rw [Filter.Eventually, mem_ae_iff] at h
  refine measure_mono_null ?_ h
  intro x hx
  simp only [Set.mem_union, Set.mem_diff] at hx
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  intro hiff
  rcases hx with ⟨hxS, hxT⟩ | ⟨hxT, hxS⟩
  · exact hxT ((hiff.mp hxS))
  · exact hxS ((hiff.mpr hxT))

private theorem souzaPositiveLevelBlock_toFunLt_eq_real_nonneg
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    (hB : SouzaPositiveLevelBlock G s p hs hp hp_top B)
    (x : α) :
    ∃ a : ℝ, 0 ≤ a ∧
      B.toFunLt (souzaAtomFamily G s p hs hp hp_top) x = (a : ℂ) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  have hterm :
      ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ∃ a : ℝ, 0 ≤ a ∧
          B.coeff Q *
              A.toFunction
                (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x =
            (a : ℂ) := by
    intro Q
    rcases hB Q with ⟨c, hc, hcoeff, hatom⟩
    by_cases hx : x ∈ Q.1
    · let r : ℝ := (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹)
      have hr_nonneg : 0 ≤ r := by
        exact Real.rpow_nonneg ENNReal.toReal_nonneg _
      refine ⟨c * r, mul_nonneg hc hr_nonneg, ?_⟩
      rw [hcoeff, hatom]
      simp [canonicalSouzaAtom, r, goodGridCellOfLevelCell, hx]
    · refine ⟨0, le_rfl, ?_⟩
      rw [hcoeff, hatom]
      simp [canonicalSouzaAtom, goodGridCellOfLevelCell, hx]
  choose a ha_nonneg ha_eq using hterm
  refine ⟨∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k, a Q,
    Finset.sum_nonneg (fun Q _ => ha_nonneg Q), ?_⟩
  rw [show ((∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k, a Q : ℝ) : ℂ) =
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k, (a Q : ℂ) by
        exact Complex.ofReal_sum (Finset.univ) a]
  simp [WeakGridSpace.LevelBlock.toFunLt, A, ha_eq]

private theorem souzaPositiveLevelBlock_toFunLt_lower_of_coeff_ne_zero
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    (hB : SouzaPositiveLevelBlock G s p hs hp hp_top B)
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (hQcoeff : B.coeff Q ≠ 0)
    {x : α} (hxQ : x ∈ Q.1) :
    ∃ b a : ℝ, 0 < b ∧ b ≤ a ∧
      B.toFunLt (souzaAtomFamily G s p hs hp hp_top) x = (a : ℂ) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  choose c hc hcoeff hatom using hB
  let r : WeakGridSpace.LevelCell G.toWeakGridSpace k → ℝ :=
    fun S => (G.grid.μ S.1).toReal ^ (s - (p.toReal)⁻¹)
  let a : WeakGridSpace.LevelCell G.toWeakGridSpace k → ℝ :=
    fun S => if x ∈ S.1 then c S * r S else 0
  have hr_nonneg : ∀ S : WeakGridSpace.LevelCell G.toWeakGridSpace k, 0 ≤ r S := by
    intro S
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  have ha_nonneg : ∀ S : WeakGridSpace.LevelCell G.toWeakGridSpace k, 0 ≤ a S := by
    intro S
    by_cases hxS : x ∈ S.1
    · simp [a, hxS, mul_nonneg (hc S) (hr_nonneg S)]
    · simp [a, hxS]
  have hterm :
      ∀ S : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        B.coeff S *
            A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k S)
              (B.atom S) x =
          (a S : ℂ) := by
    intro S
    by_cases hxS : x ∈ S.1
    · rw [hcoeff S, hatom S]
      simp [a, r, canonicalSouzaAtom, goodGridCellOfLevelCell, hxS]
    · rw [hcoeff S, hatom S]
      simp [a, canonicalSouzaAtom, goodGridCellOfLevelCell, hxS]
  have hcQ_ne : c Q ≠ 0 := by
    intro hcQ_zero
    exact hQcoeff (by simp [hcoeff Q, hcQ_zero])
  have hcQ_pos : 0 < c Q :=
    lt_of_le_of_ne (hc Q) (Ne.symm hcQ_ne)
  have hrQ_pos : 0 < r Q := by
    simpa [r] using
      souzaCanonicalLocalAtom_pos G s p ⟨k, Q.1, Q.2⟩
  have haQ_pos : 0 < a Q := by
    simp [a, hxQ, mul_pos hcQ_pos hrQ_pos]
  refine ⟨a Q, ∑ S : WeakGridSpace.LevelCell G.toWeakGridSpace k, a S,
    haQ_pos, ?_, ?_⟩
  · exact Finset.single_le_sum (fun S _ => ha_nonneg S) (Finset.mem_univ Q)
  · rw [show ((∑ S : WeakGridSpace.LevelCell G.toWeakGridSpace k, a S : ℝ) : ℂ) =
        ∑ S : WeakGridSpace.LevelCell G.toWeakGridSpace k, (a S : ℂ) by
          exact Complex.ofReal_sum (Finset.univ) a]
    simp [WeakGridSpace.LevelBlock.toFunLt, A, hterm]

private theorem souzaPositiveRepresentation_block_toFunLt_eq_zero_of_notMem_activeCells
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    {k : ℕ} {x : α}
    (hx : x ∉ ⋃ Q ∈
        souzaPositiveRepresentationActiveCells G s p hs hp hp_top R, Q.cell) :
    (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x = 0 := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  unfold WeakGridSpace.LevelBlock.toFunLt
  refine Finset.sum_eq_zero ?_
  intro Q _hQ
  by_cases hxQ : x ∈ Q.1
  · have hcoeff_zero : (R.block k).coeff Q = 0 := by
      by_contra hcoeff_ne
      let Qg : GoodGridCell G := goodGridCellOfLevelCell G Q
      have hQg_active :
          Qg ∈ souzaPositiveRepresentationActiveCells G s p hs hp hp_top R := by
        simpa [souzaPositiveRepresentationActiveCells, Qg, goodGridCellOfLevelCell]
          using hcoeff_ne
      have hx_union :
          x ∈ ⋃ Q ∈
              souzaPositiveRepresentationActiveCells G s p hs hp hp_top R, Q.cell := by
        refine Set.mem_iUnion.mpr ⟨Qg, ?_⟩
        refine Set.mem_iUnion.mpr ⟨hQg_active, ?_⟩
        exact hxQ
      exact hx hx_union
    simp [hcoeff_zero]
  · rcases hR k Q with ⟨c, hc, hcoeff, hatom⟩
    rw [hcoeff, hatom]
    simp [canonicalSouzaAtom, goodGridCellOfLevelCell, hxQ]

private theorem souzaPositiveRepresentation_partial_toFun_eq_real_nonneg
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (N : ℕ) (x : α) :
    ∃ a : ℝ, 0 ≤ a ∧
      (∑ k ∈ Finset.range N,
        (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x) = (a : ℂ) := by
  classical
  have hterm :
      ∀ k : ℕ, ∃ a : ℝ, 0 ≤ a ∧
        (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x = (a : ℂ) := by
    intro k
    exact souzaPositiveLevelBlock_toFunLt_eq_real_nonneg
      G s p hs hp hp_top (R.block k) (hR k) x
  choose a ha_nonneg ha_eq using hterm
  refine ⟨∑ k ∈ Finset.range N, a k,
    Finset.sum_nonneg fun k _ => ha_nonneg k, ?_⟩
  rw [show ((∑ k ∈ Finset.range N, a k : ℝ) : ℂ) =
      ∑ k ∈ Finset.range N, (a k : ℂ) by
        norm_cast]
  simp [ha_eq]

private theorem souzaPositiveRepresentation_partial_toFun_lower_of_activeCell
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (Q : GoodGridCell G) {x : α}
    {b aQ : ℝ} (hb_le_aQ : b ≤ aQ)
    (hQ_eq :
      (R.block Q.level).toFunLt
          (souzaAtomFamily G s p hs hp hp_top) x = (aQ : ℂ))
    {N : ℕ} (hN : Q.level < N) :
    ∃ a : ℝ, b ≤ a ∧
      (∑ k ∈ Finset.range N,
        (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x) = (a : ℂ) := by
  classical
  have hterm :
      ∀ k : ℕ, ∃ a : ℝ, 0 ≤ a ∧
        (R.block k).toFunLt (souzaAtomFamily G s p hs hp hp_top) x = (a : ℂ) := by
    intro k
    exact souzaPositiveLevelBlock_toFunLt_eq_real_nonneg
      G s p hs hp hp_top (R.block k) (hR k) x
  choose a ha_nonneg ha_eq using hterm
  have haQ_eq : a Q.level = aQ := by
    apply Complex.ofReal_injective
    rw [← ha_eq Q.level, hQ_eq]
  refine ⟨∑ k ∈ Finset.range N, a k, ?_, ?_⟩
  · calc
      b ≤ a Q.level := by simpa [haQ_eq] using hb_le_aQ
      _ ≤ ∑ k ∈ Finset.range N, a k :=
        Finset.single_le_sum (fun k _ => ha_nonneg k) (by simpa using hN)
  · rw [show ((∑ k ∈ Finset.range N, a k : ℝ) : ℂ) =
        ∑ k ∈ Finset.range N, (a k : ℂ) by
          norm_cast]
    simp [ha_eq]

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
  classical
  rcases hf with ⟨g, hgf, hg_pos⟩
  rcases hg_pos with ⟨R, hR_pos⟩
  let A := souzaAtomFamily G s p hs hp hp_top
  let cells := souzaPositiveRepresentationActiveCells G s p hs hp hp_top R
  let μ := G.toWeakGridSpace.measure
  let partialSum : ℕ → Lp ℂ p μ :=
    fun N => ∑ k ∈ Finset.range N, (R.block k).toLp A
  have hpartial_tendsto :
      Tendsto partialSum atTop (𝓝 ((g : Lp ℂ p μ))) := by
    simpa [partialSum, μ, A] using R.hasSum.tendsto_sum_nat
  have hpartial_coe : ∀ N : ℕ,
      (partialSum N : α → ℂ) =ᵐ[μ]
        fun x => ∑ k ∈ Finset.range N, (R.block k).toFunLt A x := by
    intro N
    induction' N with N ih
    · simpa [partialSum] using (Lp.coeFn_zero ℂ p μ)
    · have hblock :
          (((R.block N).toLp A : Lp ℂ p μ) : α → ℂ) =ᵐ[μ]
            fun x => (R.block N).toFunLt A x := by
        simpa [μ, A] using
          WeakGridSpace.LevelBlock.coeFn_toLp A (R.block N)
      have hsum := ih.add hblock
      have hLp :
          partialSum (N + 1) =
            partialSum N + ((R.block N).toLp A : Lp ℂ p μ) := by
        simp [partialSum, Finset.sum_range_succ]
      rw [hLp]
      refine (Lp.coeFn_add _ _).trans ?_
      refine hsum.trans ?_
      filter_upwards with x
      simp [Finset.sum_range_succ, add_comm]
  have htendsto_measure :
      TendstoInMeasure μ (fun N => partialSum N) atTop (g : Lp ℂ p μ) :=
    tendstoInMeasure_of_tendsto_Lp hpartial_tendsto
  rcases htendsto_measure.exists_seq_tendsto_ae with
    ⟨φ, hφ_mono, hφ_tendsto_ae⟩
  have hcoe :
      ∀ᵐ x ∂μ, ∀ m : ℕ,
        partialSum (φ m) x =
          ∑ k ∈ Finset.range (φ m), (R.block k).toFunLt A x := by
    have hsets :
        (⋂ m : ℕ, {x : α |
          partialSum (φ m) x =
            ∑ k ∈ Finset.range (φ m), (R.block k).toFunLt A x}) ∈ ae μ := by
      exact countable_iInter_mem.mpr fun m => hpartial_coe (φ m)
    filter_upwards [hsets] with x hx m
    exact Set.mem_iInter.mp hx m
  have hsupport_ae :
      ∀ᵐ x ∂μ,
        (x ∈ {x | f x ≠ 0} ↔
          x ∈ ⋃ Q ∈ cells, Q.cell) := by
    filter_upwards [hgf, hφ_tendsto_ae, hcoe] with x hxgf hxlim hxcoe
    constructor
    · intro hfx
      by_contra hx_not
      have hsum_zero : ∀ m : ℕ,
          (∑ k ∈ Finset.range (φ m), (R.block k).toFunLt A x) = 0 := by
        intro m
        refine Finset.sum_eq_zero ?_
        intro k _hk
        simpa [A, cells] using
          souzaPositiveRepresentation_block_toFunLt_eq_zero_of_notMem_activeCells
            G s p q hs hp hp_top R hR_pos (k := k) (x := x) hx_not
      have hpartial_zero : ∀ m : ℕ, partialSum (φ m) x = 0 := by
        intro m
        rw [hxcoe m, hsum_zero m]
      have hgx_zero : (g : Lp ℂ p μ) x = 0 := by
        have hz_tendsto :
            Tendsto (fun m : ℕ => partialSum (φ m) x) atTop (𝓝 (0 : ℂ)) := by
          simpa [hpartial_zero] using tendsto_const_nhds
        exact tendsto_nhds_unique hxlim hz_tendsto
      exact hfx (by simpa [μ] using (hxgf ▸ hgx_zero))
    · intro hx_union
      rcases Set.mem_iUnion.mp hx_union with ⟨Q, hQ⟩
      rcases Set.mem_iUnion.mp hQ with ⟨hQactive, hxQ⟩
      rcases souzaPositiveLevelBlock_toFunLt_lower_of_coeff_ne_zero
          G s p hs hp hp_top (R.block Q.level) (hR_pos Q.level) Q.toLevelCell
          (by simpa [cells, souzaPositiveRepresentationActiveCells] using hQactive) hxQ with
        ⟨b, _aQ, hb_pos, _hb_le_aQ, _hQ_eq⟩
      have hφ_large : ∀ᶠ m in atTop, Q.level < φ m := by
        exact (hφ_mono.tendsto_atTop.eventually (eventually_gt_atTop Q.level))
      have hre_eventually :
          ∀ᶠ m in atTop, b ≤ (partialSum (φ m) x).re := by
        filter_upwards [hφ_large] with m hm
        rcases souzaPositiveRepresentation_partial_toFun_lower_of_activeCell
            G s p q hs hp hp_top R hR_pos Q _hb_le_aQ _hQ_eq hm with
          ⟨a, hb_le, hsum_eq⟩
        have hpartial_eq : partialSum (φ m) x = (a : ℂ) := by
          rw [hxcoe m, hsum_eq]
        rw [hpartial_eq]
        exact_mod_cast hb_le
      have hre_lim : b ≤ ((g : Lp ℂ p μ) x).re := by
        have hre_tendsto :
            Tendsto (fun m : ℕ => (partialSum (φ m) x).re) atTop
              (𝓝 (((g : Lp ℂ p μ) x).re)) :=
          (Complex.continuous_re.tendsto ((g : Lp ℂ p μ) x)).comp hxlim
        exact ge_of_tendsto hre_tendsto hre_eventually
      have hgx_ne : (g : Lp ℂ p μ) x ≠ 0 := by
        intro hgx_zero
        have hb_nonpos : b ≤ 0 := by simpa [hgx_zero] using hre_lim
        exact (not_le_of_gt hb_pos) hb_nonpos
      simpa [μ, hxgf] using hgx_ne
  refine ⟨cells, ?_, ?_⟩
  · haveI : Countable (GoodGridCell G) := countable_goodGridCell G
    exact Set.countable_univ.mono (Set.subset_univ cells)
  · exact aeEqSet_of_ae_mem_iff (by simpa [μ] using hsupport_ae)

/-- For a positive Souza representation `R` of `g`, if the coefficient at an
active cell `P` (level `j`) is nonzero, then `g` is, almost everywhere on `P.1`,
nonzero.  This is the "support witness" extracted from positivity: a nonzero
coefficient forces the represented function to be strictly positive a.e. on the
whole cell (no cancellation, since all atoms are canonical and coefficients are
nonnegative). -/
theorem souzaPositiveRepresentation_ae_ne_zero_on_active_cell
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    {j : ℕ} (P : WeakGridSpace.LevelCell G.toWeakGridSpace j)
    (hcoeff : (R.block j).coeff P ≠ 0) :
    ∀ᵐ x ∂ (G.toWeakGridSpace.measure.restrict P.1),
      (g : α → ℂ) x ≠ 0 := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let μ := G.toWeakGridSpace.measure
  let partialSum : ℕ → Lp ℂ p μ :=
    fun N => ∑ k ∈ Finset.range N, (R.block k).toLp A
  have hpartial_tendsto :
      Tendsto partialSum atTop (𝓝 ((g : Lp ℂ p μ))) := by
    simpa [partialSum, μ, A] using R.hasSum.tendsto_sum_nat
  have hpartial_coe : ∀ N : ℕ,
      (partialSum N : α → ℂ) =ᵐ[μ]
        fun x => ∑ k ∈ Finset.range N, (R.block k).toFunLt A x := by
    intro N
    induction' N with N ih
    · simpa [partialSum] using (Lp.coeFn_zero ℂ p μ)
    · have hblock :
          (((R.block N).toLp A : Lp ℂ p μ) : α → ℂ) =ᵐ[μ]
            fun x => (R.block N).toFunLt A x := by
        simpa [μ, A] using
          WeakGridSpace.LevelBlock.coeFn_toLp A (R.block N)
      have hsum := ih.add hblock
      have hLp :
          partialSum (N + 1) =
            partialSum N + ((R.block N).toLp A : Lp ℂ p μ) := by
        simp [partialSum, Finset.sum_range_succ]
      rw [hLp]
      refine (Lp.coeFn_add _ _).trans ?_
      refine hsum.trans ?_
      filter_upwards with x
      simp [Finset.sum_range_succ, add_comm]
  have htendsto_measure :
      TendstoInMeasure μ (fun N => partialSum N) atTop (g : Lp ℂ p μ) :=
    tendstoInMeasure_of_tendsto_Lp hpartial_tendsto
  rcases htendsto_measure.exists_seq_tendsto_ae with
    ⟨φ, hφ_mono, hφ_tendsto_ae⟩
  have hcoe :
      ∀ᵐ x ∂μ, ∀ m : ℕ,
        partialSum (φ m) x =
          ∑ k ∈ Finset.range (φ m), (R.block k).toFunLt A x := by
    have hsets :
        (⋂ m : ℕ, {x : α |
          partialSum (φ m) x =
            ∑ k ∈ Finset.range (φ m), (R.block k).toFunLt A x}) ∈ ae μ := by
      exact countable_iInter_mem.mpr fun m => hpartial_coe (φ m)
    filter_upwards [hsets] with x hx m
    exact Set.mem_iInter.mp hx m
  let Qg : GoodGridCell G := goodGridCellOfLevelCell G P
  have hP_meas : MeasurableSet P.1 :=
    G.toWeakGridSpace.grid.measurable j P.1 P.2
  filter_upwards [ae_restrict_of_ae hφ_tendsto_ae, ae_restrict_of_ae hcoe,
    ae_restrict_mem hP_meas] with x hxlim hxcoe hxP
  rcases souzaPositiveLevelBlock_toFunLt_lower_of_coeff_ne_zero
      G s p hs hp hp_top (R.block j) (hR j) P hcoeff hxP with
    ⟨b, aQ, hb_pos, hb_le_aQ, hQ_eq⟩
  have hφ_large : ∀ᶠ m in atTop, j < φ m :=
    hφ_mono.tendsto_atTop.eventually (eventually_gt_atTop j)
  have hre_eventually :
      ∀ᶠ m in atTop, b ≤ (partialSum (φ m) x).re := by
    filter_upwards [hφ_large] with m hm
    rcases souzaPositiveRepresentation_partial_toFun_lower_of_activeCell
        G s p q hs hp hp_top R hR Qg hb_le_aQ
        (by simpa [Qg, goodGridCellOfLevelCell] using hQ_eq)
        (by simpa [Qg, goodGridCellOfLevelCell] using hm) with
      ⟨a, hb_le, hsum_eq⟩
    have hpartial_eq : partialSum (φ m) x = (a : ℂ) := by
      rw [hxcoe m, hsum_eq]
    rw [hpartial_eq]
    exact_mod_cast hb_le
  have hre_lim : b ≤ ((g : Lp ℂ p μ) x).re := by
    have hre_tendsto :
        Tendsto (fun m : ℕ => (partialSum (φ m) x).re) atTop
          (𝓝 (((g : Lp ℂ p μ) x).re)) :=
      (Complex.continuous_re.tendsto ((g : Lp ℂ p μ) x)).comp hxlim
    exact ge_of_tendsto hre_tendsto hre_eventually
  intro hgx_zero
  have hb_nonpos : b ≤ 0 := by
    simpa [μ, hgx_zero] using hre_lim
  exact (not_le_of_gt hb_pos) hb_nonpos

/-- **Support of a positive representation, exact version (good grid).**
If `R` is a positive Souza representation of `g`, and `g` vanishes (a.e.) outside
a good-grid cell `Qc.cell`, then every coefficient at a cell `P` not contained in
`Qc.cell` is zero.  The exact containment (not merely a.e.) uses that the grid is
*good*: cells of comparable levels are either nested or disjoint
(`partition_subset_or_disjoint_of_le`), and finer cells have strictly smaller
measure (`cell_measure_le_lambda2_pow_mul_cell`, since `lambda2 < 1`). -/
theorem souzaPositiveRepresentation_coeff_eq_zero_of_not_subset_cell
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Qc : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top) g)
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (hsupp : ∀ᵐ x ∂ G.toWeakGridSpace.measure, x ∉ Qc.cell → (g : α → ℂ) x = 0)
    {n : ℕ} (P : WeakGridSpace.LevelCell G.toWeakGridSpace n)
    (hP : ¬ P.1 ⊆ Qc.cell) :
    (R.block n).coeff P = 0 := by
  classical
  have hμeq : G.toWeakGridSpace.measure = G.grid.μ := rfl
  by_contra hne
  have hPmeas : MeasurableSet P.1 := G.toWeakGridSpace.grid.measurable n P.1 P.2
  have hlin := souzaPositiveRepresentation_ae_ne_zero_on_active_cell
    G s p q hs hp hp_top R hR P hne
  have hlin' : ∀ᵐ x ∂ G.toWeakGridSpace.measure, x ∈ P.1 → (g : α → ℂ) x ≠ 0 :=
    (MeasureTheory.ae_restrict_iff' hPmeas).1 hlin
  have hae : ∀ᵐ x ∂ G.toWeakGridSpace.measure, x ∉ (P.1 \ Qc.cell) := by
    filter_upwards [hlin', hsupp] with x hx_lin hx_supp hmem
    exact hx_lin hmem.1 (hx_supp hmem.2)
  have hdiff_zero : G.toWeakGridSpace.measure (P.1 \ Qc.cell) = 0 := by
    simpa using MeasureTheory.ae_iff.mp hae
  have hP_pos : 0 < G.toWeakGridSpace.measure P.1 :=
    G.toWeakGridSpace.grid.positive_measure n P.1 P.2
  by_cases hle : Qc.level ≤ n
  · rcases G.grid.partition_subset_or_disjoint_of_le Qc.level n hle Qc.cell Qc.mem
      P.1 P.2 with hsub | hdisj
    · exact hP hsub
    · refine hP_pos.ne' ?_
      have hPeq : P.1 \ Qc.cell = P.1 := sdiff_eq_left.mpr hdisj
      rwa [hPeq] at hdiff_zero
  · push_neg at hle
    rcases G.grid.partition_subset_or_disjoint_of_le n Qc.level hle.le P.1 P.2
      Qc.cell Qc.mem with hsub | hdisj
    · exfalso
      have hQcmeas : MeasurableSet Qc.cell :=
        G.grid.grid.measurable Qc.level Qc.cell Qc.mem
      have hμcellpos : 0 < G.grid.μ Qc.cell := GoodGridCell.measure_pos Qc
      have hμcelltop : G.grid.μ Qc.cell ≠ ∞ := GoodGridCell.measure_ne_top Qc
      have hdiff_eq : G.grid.μ (P.1 \ Qc.cell) = G.grid.μ P.1 - G.grid.μ Qc.cell :=
        MeasureTheory.measure_diff hsub hQcmeas.nullMeasurableSet hμcelltop
      have hμP_le : G.grid.μ P.1 ≤ G.grid.μ Qc.cell := by
        have hz : G.grid.μ P.1 - G.grid.μ Qc.cell = 0 := by
          rw [← hdiff_eq]; exact hdiff_zero
        exact tsub_eq_zero_iff_le.mp hz
      have hk_pos : 0 < Qc.level - n := Nat.sub_pos_of_lt hle
      have hcellbd : G.grid.μ Qc.cell ≤
          (ENNReal.ofReal G.grid.lambda2) ^ (Qc.level - n) * G.grid.μ P.1 := by
        have h := cell_measure_le_lambda2_pow_mul_cell G ⟨n, P.1, P.2⟩ (Qc.level - n) Qc.cell
          (by rw [show n + (Qc.level - n) = Qc.level from Nat.add_sub_cancel' hle.le]
              exact Qc.mem)
          hsub
        simpa using h
      have hlam_lt1 : ENNReal.ofReal G.grid.lambda2 < 1 := by
        rw [ENNReal.ofReal_lt_one]; exact G.grid.hlambda2_lt_one
      have hc_lt1 : (ENNReal.ofReal G.grid.lambda2) ^ (Qc.level - n) < 1 :=
        pow_lt_one₀ zero_le hlam_lt1 hk_pos.ne'
      have hchain : G.grid.μ Qc.cell ≤
          (ENNReal.ofReal G.grid.lambda2) ^ (Qc.level - n) * G.grid.μ Qc.cell :=
        hcellbd.trans (mul_le_mul_left' hμP_le _)
      have hlt : (ENNReal.ofReal G.grid.lambda2) ^ (Qc.level - n) * G.grid.μ Qc.cell
          < G.grid.μ Qc.cell := by
        rw [mul_comm]
        calc G.grid.μ Qc.cell * (ENNReal.ofReal G.grid.lambda2) ^ (Qc.level - n)
            < G.grid.μ Qc.cell * 1 :=
              ENNReal.mul_lt_mul_right hμcellpos.ne' hμcelltop hc_lt1
          _ = G.grid.μ Qc.cell := mul_one _
      exact (lt_irrefl _) (lt_of_le_of_lt hchain hlt)
    · refine hP_pos.ne' ?_
      have hPeq : P.1 \ Qc.cell = P.1 := sdiff_eq_left.mpr hdisj.symm
      rwa [hPeq] at hdiff_zero

/--
If a positive Souza-Besov function has nonzero integral, then the countable
cell union representing its support can be chosen nonempty.
-/
theorem support_ae_nonempty_countable_iUnion_goodGridCells_of_souzaPositiveFunction
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {f : α → ℂ}
    (hf : SouzaPositiveFunction G s p q hs hp hp_top f)
    (hf_integral_ne_zero : (∫ x, f x ∂G.grid.μ) ≠ 0) :
    IsAENonemptyCountableUnionOfGoodGridCells G {x | f x ≠ 0} := by
  classical
  rcases support_ae_countable_iUnion_goodGridCells_of_souzaPositiveFunction
      G s p q hs hp hp_top hf with
    ⟨cells, hcells_count, hcells_ae⟩
  refine ⟨cells, ?_, hcells_count, hcells_ae⟩
  by_contra hcells_empty
  have hcells_eq_empty : cells = ∅ := by
    ext Q
    constructor
    · intro hQ
      exact False.elim (hcells_empty ⟨Q, hQ⟩)
    · intro hQ
      simp at hQ
  have hsupport_zero : G.grid.μ {x | f x ≠ 0} = 0 := by
    have hcells_ae' := hcells_ae
    rw [aeEqSet, hcells_eq_empty] at hcells_ae'
    simpa using hcells_ae'
  have hf_zero_ae : f =ᵐ[G.grid.μ] 0 := by
    exact (measure_eq_zero_iff_ae_notMem.mp hsupport_zero).mono fun x hx => by
      simpa using hx
  exact hf_integral_ne_zero (integral_eq_zero_of_ae hf_zero_ae)

end

end GoodGridSpace
