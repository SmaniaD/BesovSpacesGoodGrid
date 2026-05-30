import BesovSpacesGoodGrid.GoodGridBesovSpace
import BesovSpacesGoodGrid.GoodGridInducedGrid
import BesovSpacesGoodGrid.WeakGridTransmutation

/-!
# Besov atoms on a good grid

This file introduces the non-smooth, or Besov, atoms used to compare Souza's
atomic Besov space with larger atom classes.  A Besov atom on a cell `Q` is a
function supported on `Q` whose induced Besov norm of order `β` is controlled
by the scale factor `μ(Q)^(s - β)`.

The construction is deliberately phrased in terms of the existing induced-grid
and transmutation APIs.  The main comparison theorem below is the formal target
corresponding to the paper's proposition that any atom family squeezed between
Souza atoms and Besov atoms gives the same Besov space, with continuous norm
control in both directions.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/-- A `GoodGridCell` as a level cell of the weak grid induced by the good grid. -/
def GoodGridCell.toLevelCell {G : GoodGridSpace (α := α)} (Q : GoodGridCell G) :
    WeakGridSpace.LevelCell G.toWeakGridSpace Q.level :=
  ⟨Q.cell, Q.mem⟩

/--
The geometric constant used in the normalization of Besov atoms.

In the paper this is
`Cmult1^(1+1/p) * (∑ k, maior^(k β qtilde))^(1/qtilde)`.  For a good grid the
weak-grid overlap constant is already part of `G.toWeakGridSpace`; the
geometric ratio is `lambda2`, the upper child-to-parent measure ratio.
-/
noncomputable def besovAtomConstant
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞) : ℝ :=
  ((G.toWeakGridSpace.grid.Cmult1 : ℝ) ^ (1 + 1 / p.toReal)) *
    (if qtilde = ∞ then 1
     else (∑' k : ℕ, (G.grid.lambda2 ^ (k : ℕ)) ^ (β * qtilde.toReal)) ^
        (1 / qtilde.toReal))

/--
The induced Souza atom family of smoothness `β` on a parent cell `Q`.

This is the local model used to measure the Besov regularity of an atom
supported on `Q`.
-/
abbrev inducedSouzaAtomFamily
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) :
    WeakGridSpace.AtomFamily
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell) β p ∞ :=
  WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
    (souzaAtomFamily G β p hβ hp hp_top)

/--
An `(s, β, p, qtilde)` Besov atom representative supported on `Q`.

The predicate is stated for a concrete function on the ambient good-grid
measure.  It asks that the function has an `L^p` class admitting an induced
Besov representation of order `β` on the grid inside `Q`, with coefficient
gauge bounded by `C_ba⁻¹ μ(Q)^(s-β)`.
-/
def IsBesovAtom
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) (a : α → ℂ) : Prop :=
  ∃ ha : MemLp a p G.grid.μ,
  ∃ R : WeakGridSpace.LpGridRepresentation
      (inducedSouzaAtomFamily G β p hβ hp hp_top Q) ha.toLp,
    WeakGridSpace.LpGridRepresentation.FinitePQCost (q := qtilde) R ∧
      WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R
        ≤ (besovAtomConstant G β p qtilde)⁻¹ *
            (G.grid.μ Q.cell).toReal ^ (s - β)

/--
The family of Besov atoms as an `AtomFamily`.

This is the formal package corresponding to
`A^{bs}_{s,β,p,qtilde}`.  The local carrier is intentionally packaged as an
`AtomFamily` so it can be passed directly to the existing Besov-ish and
transmutation theorems.
-/
noncomputable def besovAtomFamily
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞) :
    WeakGridSpace.AtomFamily G.toWeakGridSpace s p 1 := by
  classical
  -- The carrier should be the ambient `L^p` functions supported on each cell,
  -- with atoms cut out by `IsBesovAtom`.  Proving the `AtomFamily` axioms is a
  -- local packaging task; the substantive estimate is recorded below.
  sorry

/--
Besov atoms are ordinary `(s,p,1)` atoms.

This is the formal version of the estimate
`|a|_p ≤ |Q|^s`, obtained from the induced `L^p` embedding and the defining
Besov-atom normalization.
-/
theorem besovAtom_is_sp_one_atom
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) :
    ∀ φ,
      (besovAtomFamily G s β p qtilde hs hβ hp hp_top).IsAtom Q.toWeakGridCell φ →
      eLpNorm
          ((besovAtomFamily G s β p qtilde hs hβ hp hp_top).toFunction
            Q.toWeakGridCell φ)
          p G.grid.μ ≤ (G.grid.μ Q.cell) ^ s := by
  sorry

/--
Hypothesis saying that an atom family lies between Souza atoms and Besov atoms,
up to fixed constants.

This is the Lean analogue of
`C56⁻¹ A_sz(Q) ⊆ A(Q) ⊆ C566 A_bs(Q)`.
-/
def SouzaBesovSandwich
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p u qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (A : WeakGridSpace.AtomFamily G.toWeakGridSpace s p u)
    (C56 C566 : ℝ) : Prop :=
  (∀ Q φ,
      (souzaAtomFamily G s p hs hp hp_top).IsAtom Q φ →
        ∃ ψ, A.IsAtom Q ψ ∧
          A.toFunction Q ψ =
            (C56⁻¹ : ℂ) •
              (souzaAtomFamily G s p hs hp hp_top).toFunction Q φ) ∧
  (∀ Q φ,
      A.IsAtom Q φ →
        ∃ ψ,
          (besovAtomFamily G s β p qtilde hs hβ hp hp_top).IsAtom Q ψ ∧
            A.toFunction Q φ =
              (C566 : ℂ) •
                (besovAtomFamily G s β p qtilde hs hβ hp hp_top).toFunction Q ψ)

/--
Besov-atom comparison theorem.

If a family `A` sits between Souza atoms and Besov atoms, then the three
Besov-ish spaces built from Souza atoms, `A`, and Besov atoms coincide as
subspaces of the ambient `L^p`.  The quantitative bounds are the two estimates
from the paper: the first follows from the lower inclusion, while the second
comes from transmuting each Besov atom into Souza atoms with geometric decay
`lambda2^(β-s)`.
-/
theorem souza_atoms_and_besov_atoms
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p u q qtilde : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ u)] [Fact (1 ≤ q)]
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β) (hp_top : p ≠ ∞)
    (A : WeakGridSpace.AtomFamily G.toWeakGridSpace s p u)
    (C56 C566 : ℝ) (hC56 : 0 ≤ C56) (hC566 : 0 ≤ C566)
    (hSandwich :
      SouzaBesovSandwich G s β p u qtilde hs hβ (inferInstance : Fact (1 ≤ p))
        hp_top A C56 C566) :
    (WeakGridSpace.BesovishSpace (souzaAtomFamily G s p hs inferInstance hp_top) q =
        WeakGridSpace.BesovishSpace A q) ∧
      (WeakGridSpace.BesovishSpace A q =
        WeakGridSpace.BesovishSpace
          (besovAtomFamily G s β p qtilde hs hβ inferInstance hp_top) q) ∧
      (∀ f : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs inferInstance hp_top) q,
        ∃ hfA : WeakGridSpace.MemBesovishCoeffCost A q
            (f : Lp ℂ p G.grid.μ),
          WeakGridSpace.BesovishSpace.Norm_Costpq A q
              (⟨(f : Lp ℂ p G.grid.μ), hfA⟩ :
                WeakGridSpace.BesovishSpace A q)
            ≤ C56 *
              WeakGridSpace.BesovishSpace.Norm_Costpq
                (souzaAtomFamily G s p hs inferInstance hp_top) q f) ∧
      (∀ f : WeakGridSpace.BesovishSpace A q,
        ∃ hfS : WeakGridSpace.MemBesovishCoeffCost
            (souzaAtomFamily G s p hs inferInstance hp_top) q
            (f : Lp ℂ p G.grid.μ),
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs inferInstance hp_top) q
              (⟨(f : Lp ℂ p G.grid.μ), hfS⟩ :
                WeakGridSpace.BesovishSpace
                  (souzaAtomFamily G s p hs inferInstance hp_top) q)
            ≤ (C566 / (1 - G.grid.lambda2 ^ (β - s))) *
              WeakGridSpace.BesovishSpace.Norm_Costpq A q f) := by
  -- The second embedding is exactly the transmutation argument: expand each
  -- Besov atom on the induced grid inside its support, rescale the resulting
  -- `β`-Souza atoms to `s`-Souza atoms, and sum the geometric tail.
  sorry

end

end GoodGridSpace
