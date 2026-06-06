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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
