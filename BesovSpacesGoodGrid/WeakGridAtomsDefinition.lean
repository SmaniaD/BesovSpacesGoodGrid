import BesovSpacesGoodGrid.WeakGridDefinition
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Data.ENNReal.Holder
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Sequences





namespace WeakGridSpace

open scoped ENNReal Topology

universe u v


variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
Uma célula de um Weak grid, agora usando WeakGridSpace como contexto.
-/
structure WeakGridCell (G : WeakGridSpace (α := α)) where
  level : ℕ
  cell : Set α
  mem : cell ∈ G.grid.partitions level

/-- Grid cells are measurable. -/


theorem measurable (G : WeakGridSpace (α := α)) (Q : WeakGridCell G) :
    MeasurableSet Q.cell :=
  G.grid.measurable Q.level Q.cell Q.mem

/--
The exponent appearing in the atom size estimate
`|Q| ^ (s - 1 / (u' p))`, where `u'` is represented by `uConj`.
-/


noncomputable def atomMeasureExponent (s : ℝ) (p uConj : ℝ≥0∞) : ℝ :=
  s - (uConj.toReal * p.toReal)⁻¹

/--
The measure scale in the atom bound.
-/


noncomputable def atomMeasureScale (G : WeakGridSpace (α := α)) (s : ℝ)
    (p uConj : ℝ≥0∞) (Q : WeakGridCell G) : ℝ≥0∞ :=
  (G.measure Q.cell) ^ atomMeasureExponent s p uConj

/--
A local vector space of complex-valued functions on `α`.

The carrier has its own complex vector-space structure. The map `toFun` is the
inclusion/realization of local elements as actual functions `α → ℂ`.
-/
structure LocalVectorSpace (α : Type u) [MeasurableSpace α] where
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  toFun : carrier →ₗ[ℂ] (α → ℂ)
  injective_toFun : Function.Injective toFun

attribute [instance] LocalVectorSpace.addCommGroup
attribute [instance] LocalVectorSpace.module



variable (B : LocalVectorSpace α)

/-- View an element of a local vector space as a function on `α`. -/
def asFun (φ : B.carrier) : α → ℂ :=
  B.toFun φ


/--
A family of atoms of type `(s,p,u)` on a Weak grid.

The paper writes this as an indexed family
`(B(Q), A(Q))_{Q ∈ ⋃ₖ Pᵏ}`. Here `localSpace Q` is `B(Q)` and
`atoms Q` is `A(Q)`. Each `B(Q)` is represented here as a complex vector
space of concrete functions. The exponent `uConj` is the Hölder conjugate of
`u`.
-/
structure AtomFamily
  (G : WeakGridSpace (α := α)) (s : ℝ) (p u : ℝ≥0∞) where
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
  /-- The local vector space `B(Q)`. -/
  localSpace : WeakGridCell G → LocalVectorSpace.{u, v} α
  /-- The chosen atoms `A(Q)`, as elements of `B(Q)`. -/
  atoms : ∀ Q, Set ((localSpace Q).carrier)
  /-- Every cell has at least one atom. -/
  atoms_nonempty : ∀ Q, (atoms Q).Nonempty
  /-- `B(Q)` is contained in `L^{pu}`. -/
  local_memLp : ∀ Q φ, MeasureTheory.MemLp ((localSpace Q).toFun φ) (p * u) G.measure
  /-- Local functions are supported on `Q`. -/
  local_support : ∀ Q φ, ∀ x, x ∉ Q.cell → (localSpace Q).toFun φ x = 0
  /-- `A(Q)` is convex in the local vector space. -/
  atoms_convex : ∀ Q, Convex ℝ (atoms Q)
  /-- `A(Q)` is invariant under multiplication by complex scalars of modulus one. -/
  atoms_phase_invariant :
    ∀ Q φ (σ : ℂ), φ ∈ atoms Q → ‖σ‖ = (1 : ℝ) → σ • φ ∈ atoms Q
  /-- The atom size estimate in `L^{pu}`. -/
  atom_bound :
    ∀ Q φ, φ ∈ atoms Q →
      MeasureTheory.eLpNorm ((localSpace Q).toFun φ) (p * u) G.measure ≤
        atomMeasureScale G s p uConj Q


variable {G : WeakGridSpace (α := α)} {s : ℝ} {p u : ℝ≥0∞}

namespace AtomFamily

/-- The actual function represented by a local element. -/
def toFunction (A : AtomFamily G s p u) (Q : WeakGridCell G)
    (φ : (A.localSpace Q).carrier) : α → ℂ :=
  (A.localSpace Q).toFun φ

/-- Predicate saying that `φ` is an atom of the family supported on `Q`. -/
def IsAtom (A : AtomFamily G s p u) (Q : WeakGridCell G)
    (φ : (A.localSpace Q).carrier) : Prop :=
  φ ∈ A.atoms Q

/-- For every cell there exists at least one atom. -/
theorem atoms_nonempty_on (A : AtomFamily G s p u) (Q : WeakGridCell G) :
    ∃ φ : (A.localSpace Q).carrier, A.IsAtom Q φ :=
  A.atoms_nonempty Q

/-- The type of atoms supported on a fixed grid cell. -/
def AtomsOn (A : AtomFamily G s p u) (Q : WeakGridCell G) : Type _ :=
  { φ : (A.localSpace Q).carrier // A.IsAtom Q φ }

/-- The set of all atoms in the family, viewed as functions on `α`. -/
def allAtoms (A : AtomFamily G s p u) : Set (α → ℂ) :=
  { f | ∃ (Q : WeakGridCell G) (φ : (A.localSpace Q).carrier),
      A.IsAtom Q φ ∧ A.toFunction Q φ = f }

theorem atom_memLp (A : AtomFamily G s p u)
    (Q : WeakGridCell G) (φ : (A.localSpace Q).carrier) :
    MeasureTheory.MemLp (A.toFunction Q φ) (p * u) G.measure :=
  A.local_memLp Q φ

/--
Every local function is also in `L^p`.

This uses that the measure of a grid is finite and that `u ≥ 1`, hence
`p ≤ p * u`.
-/
theorem local_memLp_p (A : AtomFamily G s p u)
    (Q : WeakGridCell G) (φ : (A.localSpace Q).carrier) :
    MeasureTheory.MemLp (A.toFunction Q φ) p G.measure := by
  have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
    dsimp [WeakGridSpace.measure]
    exact G.grid.isFinite
  letI := hfinite
  refine (A.local_memLp Q φ).mono_exponent ?_
  calc
    p = p * 1 := by rw [mul_one]
    _ ≤ p * u := by exact mul_le_mul_right A.one_le_u p

theorem atom_support (A : AtomFamily G s p u)
    (Q : WeakGridCell G) (φ : (A.localSpace Q).carrier) :
    ∀ x, x ∉ Q.cell → A.toFunction Q φ x = 0 :=
  A.local_support Q φ

theorem atom_norm_bound (A : AtomFamily G s p u)
    {Q : WeakGridCell G} {φ : (A.localSpace Q).carrier} (hφ : A.IsAtom Q φ) :
    MeasureTheory.eLpNorm (A.toFunction Q φ) (p * u) G.measure ≤
      atomMeasureScale G s p A.uConj Q :=
  A.atom_bound Q φ hφ

/--
Optional finite-dimensional hypothesis: every local space is finite-dimensional.
-/
def FiniteDimensionalAtoms (A : AtomFamily G s p u) : Prop :=
  ∀ Q, FiniteDimensional ℂ ((A.localSpace Q).carrier)


end AtomFamily

end

end WeakGridSpace
