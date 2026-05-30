import BesovSpacesGoodGrid.WeakGridDefinition
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
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
A local Banach space of complex-valued functions on `α`.

The carrier has its own normed complex vector-space structure and its own
completeness proof. The map `toFun` is the inclusion/realization of local
elements as actual functions `α → ℂ`.
-/
structure LocalBanachSpace (α : Type u) [MeasurableSpace α] where
  carrier : Type v
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace ℂ carrier]
  [completeSpace : CompleteSpace carrier]
  toFun : carrier →ₗ[ℂ] (α → ℂ)
  injective_toFun : Function.Injective toFun

attribute [instance] LocalBanachSpace.normedAddCommGroup
attribute [instance] LocalBanachSpace.normedSpace
attribute [instance] LocalBanachSpace.completeSpace



variable (B : LocalBanachSpace α)

/-- View an element of a local Banach space as a function on `α`. -/
def asFun (φ : B.carrier) : α → ℂ :=
  B.toFun φ


/--
A family of atoms of type `(s,p,u)` on a Weak grid.

The paper writes this as an indexed family
`(B(Q), A(Q))_{Q ∈ ⋃ₖ Pᵏ}`. Here `localSpace Q` is `B(Q)` and
`atoms Q` is `A(Q)`. Each `B(Q)` is a Banach space with its own norm. The
exponent `uConj` is the Hölder conjugate of `u`.
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
  /-- The local Banach space `B(Q)`. -/
  localSpace : WeakGridCell G → LocalBanachSpace.{u, v} α
  /-- The chosen atoms `A(Q)`, as elements of `B(Q)`. -/
  atoms : ∀ Q, Set ((localSpace Q).carrier)
  /-- Every cell has at least one atom. -/
  atoms_nonempty : ∀ Q, (atoms Q).Nonempty
  /-- `B(Q)` is contained in `L^{pu}`. -/
  local_memLp : ∀ Q φ, MeasureTheory.MemLp ((localSpace Q).toFun φ) (p * u) G.measure
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
Optional compactness hypothesis from the paper, modeled using the ambient
strong topology on functions.
-/
def StronglyCompactAtoms (A : AtomFamily G s p u) : Prop :=
  ∀ Q, IsCompact (A.atoms Q)

/--
Optional weak sequential compactness hypothesis. This predicate is stated for
the current ambient topology; later files can instantiate a weak topology if
the local spaces are packaged as `Lp` spaces.
-/
def WeaklySequentiallyCompactAtoms (A : AtomFamily G s p u) : Prop :=
  ∀ Q, IsSeqCompact (A.atoms Q)

/--
Optional finite-dimensional hypothesis: every local space is finite-dimensional
and `A(Q)` contains a relative neighborhood of `0` in `B(Q)`.
-/
def FiniteDimensionalAtoms (A : AtomFamily G s p u) : Prop :=
  (∀ Q, FiniteDimensional ℂ ((A.localSpace Q).carrier)) ∧
    ∀ Q, ∃ U : Set ((A.localSpace Q).carrier),
      U ∈ 𝓝 (0 : (A.localSpace Q).carrier) ∧ U ⊆ A.atoms Q


end AtomFamily

/--
An a.e. local Banach space over a weak grid.

Unlike `LocalBanachSpace`, this realizes local elements directly as vectors in
`L^p`.  This is the foundational API for atom families whose support and
linearity are meant modulo null sets rather than through chosen pointwise
representatives.
-/
structure AELocalBanachSpace
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞) where
  carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace ℂ carrier]
  [completeSpace : CompleteSpace carrier]
  toLp : carrier →ₗ[ℂ] MeasureTheory.Lp ℂ p G.measure
  injective_toLp : Function.Injective toLp

attribute [instance] AELocalBanachSpace.normedAddCommGroup
attribute [instance] AELocalBanachSpace.normedSpace
attribute [instance] AELocalBanachSpace.completeSpace

namespace AELocalBanachSpace

/--
Package a complete linear subspace of ambient `L^p` as an a.e. local Banach
space.

This is the reusable constructor for atom classes whose local spaces are
honest Banach subspaces of `L^p`, rather than pointwise spaces with a chosen
representative map. The realization map is just the subtype inclusion.
-/
noncomputable def ofLpSubmodule
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (E : Submodule ℂ (MeasureTheory.Lp ℂ p G.measure)) [CompleteSpace E] :
    AELocalBanachSpace G p where
  carrier := E
  toLp := E.subtype
  injective_toLp := by
    intro f g hfg
    exact Subtype.ext hfg

@[simp]
theorem ofLpSubmodule_toLp
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (E : Submodule ℂ (MeasureTheory.Lp ℂ p G.measure)) [CompleteSpace E]
    (f : E) :
    (ofLpSubmodule G p E).toLp f = (f : MeasureTheory.Lp ℂ p G.measure) :=
  rfl

end AELocalBanachSpace

/-- A local `L^p` vector is supported in `Q`, modulo null sets. -/
def AESupportedOn
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞)
    (Q : WeakGridCell G) (f : MeasureTheory.Lp ℂ p G.measure) : Prop :=
  (f : α → ℂ) =ᵐ[G.measure.restrict Q.cellᶜ] 0

/--
An atom family formulated directly in `L^p`.

This mirrors `AtomFamily`, but the realization map lands in `L^p`, support is
an a.e. statement, and the size estimate is expressed with the `Lp` norm.  It
is intended as the reusable replacement target for atom classes whose natural
objects are equivalence classes modulo null sets.
-/
structure AEAtomFamily
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) where
  /-- The smoothness parameter is positive. -/
  s_pos : 0 < s
  /-- `p ∈ [1,∞)`. -/
  one_le_p : 1 ≤ p
  /-- `p < ∞`, expressed in `ℝ≥0∞` as `p ≠ ∞`. -/
  p_ne_top : p ≠ ∞
  /-- The local Banach space `B(Q)`, realized in ambient `L^p`. -/
  localSpace : WeakGridCell G → AELocalBanachSpace G p
  /-- The chosen atoms `A(Q)`, as elements of `B(Q)`. -/
  atoms : ∀ Q, Set ((localSpace Q).carrier)
  /-- Every cell has at least one atom. -/
  atoms_nonempty : ∀ Q, (atoms Q).Nonempty
  /-- Local vectors are supported on `Q`, modulo null sets. -/
  local_support : ∀ Q φ, φ ∈ atoms Q →
    AESupportedOn G p Q ((localSpace Q).toLp φ)
  /-- `A(Q)` is convex in the local Banach space. -/
  atoms_convex : ∀ Q, Convex ℝ (atoms Q)
  /-- `A(Q)` is invariant under multiplication by complex scalars of modulus one. -/
  atoms_phase_invariant :
    ∀ Q φ (σ : ℂ), φ ∈ atoms Q → ‖σ‖ = (1 : ℝ) → σ • φ ∈ atoms Q
  /-- The atom size estimate in ambient `L^p`. -/
  atom_bound :
    ∀ Q φ, φ ∈ atoms Q →
      ‖(localSpace Q).toLp φ‖ ≤ (G.measure Q.cell).toReal ^ s

namespace AEAtomFamily

/-- The `L^p` vector represented by a local element. -/
def toLp {G : WeakGridSpace (α := α)} {s : ℝ} {p : ℝ≥0∞}
    (A : AEAtomFamily G s p) (Q : WeakGridCell G)
    (φ : (A.localSpace Q).carrier) : MeasureTheory.Lp ℂ p G.measure :=
  (A.localSpace Q).toLp φ

/-- Predicate saying that `φ` is an a.e. atom of the family supported on `Q`. -/
def IsAtom {G : WeakGridSpace (α := α)} {s : ℝ} {p : ℝ≥0∞}
    (A : AEAtomFamily G s p) (Q : WeakGridCell G)
    (φ : (A.localSpace Q).carrier) : Prop :=
  φ ∈ A.atoms Q

/-- For every cell there exists at least one a.e. atom. -/
theorem atoms_nonempty_on {G : WeakGridSpace (α := α)} {s : ℝ} {p : ℝ≥0∞}
    (A : AEAtomFamily G s p) (Q : WeakGridCell G) :
    ∃ φ : (A.localSpace Q).carrier, A.IsAtom Q φ :=
  A.atoms_nonempty Q

end AEAtomFamily

/-- The ambient `L^p` space as an a.e. local Banach space. -/
noncomputable def lpAELocalBanachSpace
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    AELocalBanachSpace G p where
  carrier := MeasureTheory.Lp ℂ p G.measure
  toLp := LinearMap.id
  injective_toLp := by
    intro x y h
    simpa using h

/-- The raw a.e. `(s,p,1)` atom condition in the `Lp` model. -/
def IsAESpAtom
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : WeakGridCell G) (f : MeasureTheory.Lp ℂ p G.measure) : Prop :=
  AESupportedOn G p Q f ∧ ‖f‖ ≤ (G.measure Q.cell).toReal ^ s

private theorem aeSupportedOn_zero
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞)
    (Q : WeakGridCell G) :
    AESupportedOn G p Q (0 : MeasureTheory.Lp ℂ p G.measure) := by
  exact MeasureTheory.ae_restrict_of_ae (MeasureTheory.Lp.coeFn_zero ℂ p G.measure)

private theorem aeSupportedOn_add
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)]
    (Q : WeakGridCell G)
    {f g : MeasureTheory.Lp ℂ p G.measure}
    (hf : AESupportedOn G p Q f) (hg : AESupportedOn G p Q g) :
    AESupportedOn G p Q (f + g) := by
  filter_upwards [MeasureTheory.ae_restrict_of_ae (MeasureTheory.Lp.coeFn_add f g), hf, hg] with
    x hfg hf0 hg0
  rw [hfg, Pi.add_apply, hf0, hg0]
  simp

private theorem aeSupportedOn_smul
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)]
    (Q : WeakGridCell G) (c : ℂ)
    {f : MeasureTheory.Lp ℂ p G.measure}
    (hf : AESupportedOn G p Q f) :
    AESupportedOn G p Q (c • f) := by
  filter_upwards [MeasureTheory.ae_restrict_of_ae (MeasureTheory.Lp.coeFn_smul c f), hf] with
    x hcf hf0
  simp [hcf, hf0]

/--
The ambient `L^p` subspace of functions supported on a cell `Q`, modulo null
sets.

This is the natural local space for atom theories built directly inside
ambient `L^p`: elements already carry their support condition as part of the
type, instead of repeating it in every atom predicate.
-/
def supportedLpSubmodule
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Q : WeakGridCell G) : Submodule ℂ (MeasureTheory.Lp ℂ p G.measure) where
  carrier := {f | AESupportedOn G p Q f}
  zero_mem' := aeSupportedOn_zero G p Q
  add_mem' := by
    intro f g hf hg
    exact aeSupportedOn_add G p Q hf hg
  smul_mem' := by
    intro c f hf
    exact aeSupportedOn_smul G p Q c hf

@[simp]
theorem mem_supportedLpSubmodule
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Q : WeakGridCell G) (f : MeasureTheory.Lp ℂ p G.measure) :
    f ∈ supportedLpSubmodule G p Q ↔ AESupportedOn G p Q f :=
  Iff.rfl

/--
The supported `L^p` subspace of a cell, packaged as an a.e. local Banach
space.

The explicit completeness assumption records the one analytic fact still
needed to use this subspace as a `LocalBanachSpace`. In applications it should
come from closedness of the support condition in ambient `L^p`.
-/
noncomputable def supportedLpAELocalBanachSpace
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Q : WeakGridCell G) [CompleteSpace (supportedLpSubmodule G p Q)] :
    AELocalBanachSpace G p :=
  AELocalBanachSpace.ofLpSubmodule G p (supportedLpSubmodule G p Q)

@[simp]
theorem supportedLpAELocalBanachSpace_toLp
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Q : WeakGridCell G) [CompleteSpace (supportedLpSubmodule G p Q)]
    (f : supportedLpSubmodule G p Q) :
    (supportedLpAELocalBanachSpace G p Q).toLp f =
      (f : MeasureTheory.Lp ℂ p G.measure) :=
  rfl

private theorem isAESpAtom_convex
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)]
    (Q : WeakGridCell G) :
    Convex ℝ {f : MeasureTheory.Lp ℂ p G.measure | IsAESpAtom G s p Q f} := by
  intro f hf g hg a b ha hb hab
  rcases hf with ⟨hf_supp, hf_norm⟩
  rcases hg with ⟨hg_supp, hg_norm⟩
  constructor
  · exact aeSupportedOn_add G p Q
      (aeSupportedOn_smul G p Q (a : ℂ) hf_supp)
      (aeSupportedOn_smul G p Q (b : ℂ) hg_supp)
  · calc
      ‖a • f + b • g‖ ≤ ‖(a : ℂ) • f‖ + ‖(b : ℂ) • g‖ :=
        norm_add_le ((a : ℂ) • f) ((b : ℂ) • g)
      _ = ‖(a : ℂ)‖ * ‖f‖ + ‖(b : ℂ)‖ * ‖g‖ := by
        rw [norm_smul, norm_smul]
      _ ≤ ‖(a : ℂ)‖ * ((G.measure Q.cell).toReal ^ s) +
          ‖(b : ℂ)‖ * ((G.measure Q.cell).toReal ^ s) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hf_norm (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hg_norm (norm_nonneg _))
      _ = (a + b) * ((G.measure Q.cell).toReal ^ s) := by
            rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
            have ha_abs : |a| = a := abs_of_nonneg ha
            have hb_abs : |b| = b := abs_of_nonneg hb
            rw [ha_abs, hb_abs]
            ring
      _ = (G.measure Q.cell).toReal ^ s := by rw [hab, one_mul]

/-- Raw a.e. `(s,p,1)` atoms are invariant under multiplication by a complex phase. -/
theorem isAESpAtom_phase_invariant
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)]
    (Q : WeakGridCell G) {f : MeasureTheory.Lp ℂ p G.measure} {σ : ℂ}
    (hf : IsAESpAtom G s p Q f) (hσ : ‖σ‖ = (1 : ℝ)) :
    IsAESpAtom G s p Q (σ • f) := by
  rcases hf with ⟨hf_supp, hf_norm⟩
  constructor
  · exact aeSupportedOn_smul G p Q σ hf_supp
  · calc
      ‖σ • f‖ = ‖σ‖ * ‖f‖ := norm_smul σ f
      _ = ‖f‖ := by rw [hσ, one_mul]
      _ ≤ (G.measure Q.cell).toReal ^ s := hf_norm

/--
The a.e. atom family of all supported `L^p` vectors with the usual
`μ(Q)^s` size bound.
-/
noncomputable def aeSpAtomFamily
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) [Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    AEAtomFamily G s p where
  s_pos := hs
  one_le_p := Fact.out
  p_ne_top := hp_top
  localSpace := fun _ => lpAELocalBanachSpace G p
  atoms := fun Q => {f : MeasureTheory.Lp ℂ p G.measure | IsAESpAtom G s p Q f}
  atoms_nonempty := by
    intro Q
    refine ⟨0, ?_⟩
    refine ⟨aeSupportedOn_zero G p Q, ?_⟩
    calc
      ‖(0 : MeasureTheory.Lp ℂ p G.measure)‖ = 0 := norm_zero
      _ ≤ (G.measure Q.cell).toReal ^ s := Real.rpow_nonneg ENNReal.toReal_nonneg s
  local_support := by
    intro Q φ hφ
    exact hφ.1
  atoms_convex := by
    intro Q
    exact isAESpAtom_convex G s p Q
  atoms_phase_invariant := by
    intro Q φ σ hφ hσ
    exact isAESpAtom_phase_invariant G s p Q hφ hσ
  atom_bound := by
    intro Q φ hφ
    exact hφ.2

end

end WeakGridSpace
