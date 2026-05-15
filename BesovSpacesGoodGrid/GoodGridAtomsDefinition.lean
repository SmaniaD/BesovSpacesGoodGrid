import BesovSpacesGoodGrid.GoodGridDefinition
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Data.ENNReal.Holder
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Sequences

/-!
Atoms associated to a good grid.

This file formalizes the data from the paper's definition of a family of
atoms of type `(s,p,u)`. A cell is a member of one of the grid partitions.
For each cell `Q`, an atom family gives a local Banach space `localSpace Q`
with its own norm and a linear inclusion into complex-valued functions on `α`,
together with a convex, phase-invariant set `atoms Q` satisfying support and
`L^{p u}` size conditions.
-/

namespace GoodGridSpace

open scoped ENNReal Topology

universe u v

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
A cell of a good grid: a set appearing in one of the finite partitions.
-/
structure GoodGridCell (S : GoodGrid (α := α)) where
  level : ℕ
  cell : Set α
  mem : cell ∈ S.grid.partitions level

/-- Grid cells are measurable. -/
theorem measurable (S : GoodGrid (α := α)) (Q : GoodGridCell S) :
    MeasurableSet Q.cell :=
  S.grid.measurable Q.level Q.cell Q.mem

/--
The exponent appearing in the atom size estimate
`|Q| ^ (s - 1 / (u' p))`, where `u'` is represented by `uConj`.
-/
noncomputable def atomMeasureExponent (s : ℝ) (p uConj : ℝ≥0∞) : ℝ :=
  s - (uConj.toReal * p.toReal)⁻¹

/--
The measure scale in the atom bound.
-/
noncomputable def atomMeasureScale (S : GoodGrid (α := α)) (s : ℝ)
    (p uConj : ℝ≥0∞) (Q : GoodGridCell S) : ℝ≥0∞ :=
  (S.μ Q.cell) ^ atomMeasureExponent s p uConj

/--
A local Banach space of complex-valued functions on `α`.

The carrier has its own normed complex vector-space structure and its own
completeness proof. The map `toFun` is the inclusion/realization of local
elements as actual functions `α → ℂ`.
-/
structure GoodGridLocalBanachSpace (α : Type u) [MeasurableSpace α] where
  carrier : Type v
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace ℂ carrier]
  [completeSpace : CompleteSpace carrier]
  toFun : carrier →ₗ[ℂ] (α → ℂ)
  injective_toFun : Function.Injective toFun

attribute [instance] GoodGridLocalBanachSpace.normedAddCommGroup
attribute [instance] GoodGridLocalBanachSpace.normedSpace
attribute [instance] GoodGridLocalBanachSpace.completeSpace

namespace GoodGridLocalBanachSpace

variable (B : GoodGridLocalBanachSpace α)

/-- View an element of a local Banach space as a function on `α`. -/
def asFun (φ : B.carrier) : α → ℂ :=
  B.toFun φ

end GoodGridLocalBanachSpace

/--
A family of atoms of type `(s,p,u)` on a good grid.

The paper writes this as an indexed family
`(B(Q), A(Q))_{Q ∈ ⋃ₖ Pᵏ}`. Here `localSpace Q` is `B(Q)` and
`atoms Q` is `A(Q)`. Each `B(Q)` is a Banach space with its own norm. The
exponent `uConj` is the Hölder conjugate of `u`.
-/
structure AtomFamily
    (S : GoodGrid (α := α)) (s : ℝ) (p u : ℝ≥0∞) where
  /-- The Hölder conjugate exponent `u'`. -/
  uConj : ℝ≥0∞
  /-- The smoothness parameter is positive. -/
  s_pos : 0 < s
  /-- `p ∈ [1,∞)`. -/
  one_le_p : 1 ≤ p
  /-- `p < ∞`, expressed in `ℝ≥0∞` as `p ≠ ∞`. -/
  p_ne_top : p ≠ ∞
  /-- `u ∈ [1,∞]`. -/
  one_le_u : 1 ≤ u
  /-- `uConj` is the Hölder conjugate of `u`. -/
  holder_conjugate : ENNReal.HolderConjugate u uConj
  /-- The local Banach space `B(Q)`. -/
  localSpace : GoodGridCell S → GoodGridLocalBanachSpace.{u, v} α
  /-- The chosen atoms `A(Q)`, as elements of `B(Q)`. -/
  atoms : ∀ Q, Set ((localSpace Q).carrier)
  /-- Every cell has at least one atom. -/
  atoms_nonempty : ∀ Q, (atoms Q).Nonempty
  /-- `B(Q)` is contained in `L^{pu}`. -/
  local_memLp : ∀ Q φ, MeasureTheory.MemLp ((localSpace Q).toFun φ) (p * u) S.μ
  /-- Local functions are supported on `Q`. -/
  local_support : ∀ Q φ, ∀ x, x ∉ Q.cell → (localSpace Q).toFun φ x = 0
  /-- `A(Q)` is convex in the local Banach space. -/
  atoms_convex : ∀ Q, Convex ℝ (atoms Q)
  /-- `A(Q)` is invariant under multiplication by complex scalars of modulus one. -/
  atoms_phase_invariant :
    ∀ Q φ (σ : ℂ), φ ∈ atoms Q → ‖σ‖ = (1 : ℝ) → σ • φ ∈ atoms Q
  /-- The atom size estimate in `L^{pu}`. -/
  atom_bound :
    ∀ Q φ, φ ∈ atoms Q →
      MeasureTheory.eLpNorm ((localSpace Q).toFun φ) (p * u) S.μ ≤
        atomMeasureScale S s p uConj Q

namespace AtomFamily

variable {S : GoodGrid (α := α)} {s : ℝ} {p u : ℝ≥0∞}

/-- The actual function represented by a local element. -/
def toFunction (A : AtomFamily S s p u) (Q : GoodGridCell S)
    (φ : (A.localSpace Q).carrier) : α → ℂ :=
  (A.localSpace Q).toFun φ

/-- Predicate saying that `φ` is an atom of the family supported on `Q`. -/
def IsAtom (A : AtomFamily S s p u) (Q : GoodGridCell S)
    (φ : (A.localSpace Q).carrier) : Prop :=
  φ ∈ A.atoms Q

/-- For every cell there exists at least one atom. -/
theorem atoms_nonempty_on (A : AtomFamily S s p u) (Q : GoodGridCell S) :
    ∃ φ : (A.localSpace Q).carrier, A.IsAtom Q φ :=
  A.atoms_nonempty Q

/-- The type of atoms supported on a fixed grid cell. -/
def AtomsOn (A : AtomFamily S s p u) (Q : GoodGridCell S) : Type _ :=
  { φ : (A.localSpace Q).carrier // A.IsAtom Q φ }

/-- The set of all atoms in the family, viewed as functions on `α`. -/
def allAtoms (A : AtomFamily S s p u) : Set (α → ℂ) :=
  { f | ∃ (Q : GoodGridCell S) (φ : (A.localSpace Q).carrier),
      A.IsAtom Q φ ∧ A.toFunction Q φ = f }

theorem atom_memLp (A : AtomFamily S s p u)
    (Q : GoodGridCell S) (φ : (A.localSpace Q).carrier) :
    MeasureTheory.MemLp (A.toFunction Q φ) (p * u) S.μ :=
  A.local_memLp Q φ

/--
Every local function is also in `L^p`.

This uses that the measure of a grid is finite and that `u ≥ 1`, hence
`p ≤ p * u`.
-/
theorem local_memLp_p (A : AtomFamily S s p u)
    (Q : GoodGridCell S) (φ : (A.localSpace Q).carrier) :
    MeasureTheory.MemLp (A.toFunction Q φ) p S.μ := by
  letI := S.isFinite
  refine (A.local_memLp Q φ).mono_exponent ?_
  calc
    p = p * 1 := by rw [mul_one]
    _ ≤ p * u := by exact mul_le_mul_right A.one_le_u p

theorem atom_support (A : AtomFamily S s p u)
    (Q : GoodGridCell S) (φ : (A.localSpace Q).carrier) :
    ∀ x, x ∉ Q.cell → A.toFunction Q φ x = 0 :=
  A.local_support Q φ

theorem atom_norm_bound (A : AtomFamily S s p u)
    {Q : GoodGridCell S} {φ : (A.localSpace Q).carrier} (hφ : A.IsAtom Q φ) :
    MeasureTheory.eLpNorm (A.toFunction Q φ) (p * u) S.μ ≤
      atomMeasureScale S s p A.uConj Q :=
  A.atom_bound Q φ hφ

/--
Optional compactness hypothesis from the paper, modeled using the ambient
strong topology on functions.
-/
def StronglyCompactAtoms (A : AtomFamily S s p u) : Prop :=
  ∀ Q, IsCompact (A.atoms Q)

/--
Optional weak sequential compactness hypothesis. This predicate is stated for
the current ambient topology; later files can instantiate a weak topology if
the local spaces are packaged as `Lp` spaces.
-/
def WeaklySequentiallyCompactAtoms (A : AtomFamily S s p u) : Prop :=
  ∀ Q, IsSeqCompact (A.atoms Q)

/--
Optional finite-dimensional hypothesis: every local space is finite-dimensional
and `A(Q)` contains a relative neighborhood of `0` in `B(Q)`.
-/
def FiniteDimensionalAtoms (A : AtomFamily S s p u) : Prop :=
  (∀ Q, FiniteDimensional ℂ ((A.localSpace Q).carrier)) ∧
    ∀ Q, ∃ U : Set ((A.localSpace Q).carrier),
      U ∈ 𝓝 (0 : (A.localSpace Q).carrier) ∧ U ⊆ A.atoms Q

end AtomFamily

end

end GoodGridSpace
