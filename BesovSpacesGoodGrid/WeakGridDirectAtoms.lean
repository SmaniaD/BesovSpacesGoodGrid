import BesovSpacesGoodGrid.WeakGridAtomsDefinition
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Direct `L^p` atom families on weak grids

This file contains the local-Banach-free atom API.  A direct atom family is a
family of subsets of the ambient `L^p` space, indexed by weak-grid cells, with
support and size estimates stated directly for `L^p` classes.
-/

namespace WeakGridSpace

open scoped ENNReal Topology

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
An ambient `L^p` vector is supported on the cell `Q`, modulo null sets.

This is the support condition for the direct `L^p` atom API below. It avoids
choosing pointwise representatives as part of the local data.
-/
def LpSupportedOn
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞)
    (Q : WeakGridCell G) (f : MeasureTheory.Lp ℂ p G.measure) : Prop :=
  (f : α → ℂ) =ᵐ[G.measure.restrict Q.cellᶜ] 0

/-- The zero `L^p` class is supported on every cell. -/
theorem lpSupportedOn_zero
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞)
    (Q : WeakGridCell G) :
    LpSupportedOn G p Q (0 : MeasureTheory.Lp ℂ p G.measure) := by
  exact MeasureTheory.ae_restrict_of_ae (MeasureTheory.Lp.coeFn_zero ℂ p G.measure)

/-- Cell support is stable under addition in ambient `L^p`. -/
theorem lpSupportedOn_add
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Q : WeakGridCell G)
    {f g : MeasureTheory.Lp ℂ p G.measure}
    (hf : LpSupportedOn G p Q f) (hg : LpSupportedOn G p Q g) :
    LpSupportedOn G p Q (f + g) := by
  filter_upwards [MeasureTheory.ae_restrict_of_ae (MeasureTheory.Lp.coeFn_add f g),
    hf, hg] with x hfg hf0 hg0
  rw [hfg, Pi.add_apply, hf0, hg0]
  simp

/-- Cell support is stable under scalar multiplication in ambient `L^p`. -/
theorem lpSupportedOn_smul
    (G : WeakGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Q : WeakGridCell G) (c : ℂ)
    {f : MeasureTheory.Lp ℂ p G.measure}
    (hf : LpSupportedOn G p Q f) :
    LpSupportedOn G p Q (c • f) := by
  filter_upwards [MeasureTheory.ae_restrict_of_ae (MeasureTheory.Lp.coeFn_smul c f),
    hf] with x hcf hf0
  simp [hcf, hf0]

/--
A direct atom family in ambient `L^p`.

This is the parallel API for atom classes whose atoms are literally subsets of
ambient `L^p`, indexed by grid cells. The support condition is a field of the
structure, so there is no separate local Banach space and no representative
map from local objects to functions.
-/
structure LpAtomFamily
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) where
  /-- The smoothness parameter is positive. -/
  s_pos : 0 < s
  /-- `p ∈ [1,∞)`. -/
  one_le_p : 1 ≤ p
  /-- `p < ∞`, expressed in `ℝ≥0∞` as `p ≠ ∞`. -/
  p_ne_top : p ≠ ∞
  /-- The chosen atoms on each cell, directly as ambient `L^p` classes. -/
  atoms : WeakGridCell G → Set (MeasureTheory.Lp ℂ p G.measure)
  /-- Every cell has at least one atom. -/
  atoms_nonempty : ∀ Q, (atoms Q).Nonempty
  /-- Atoms on `Q` are supported on `Q`, modulo null sets. -/
  atoms_supported : ∀ Q f, f ∈ atoms Q → LpSupportedOn G p Q f
  /-- `A(Q)` is convex as a subset of ambient `L^p`. -/
  atoms_convex : ∀ Q, Convex ℝ (atoms Q)
  /-- `A(Q)` is invariant under multiplication by complex scalars of modulus one. -/
  atoms_phase_invariant :
    ∀ Q f (σ : ℂ), f ∈ atoms Q → ‖σ‖ = (1 : ℝ) → σ • f ∈ atoms Q
  /-- The atom size estimate in ambient `L^p`. -/
  atom_bound :
    ∀ Q f, f ∈ atoms Q → ‖f‖ ≤ (G.measure Q.cell).toReal ^ s

variable {G : WeakGridSpace (α := α)} {s : ℝ} {p : ℝ≥0∞}

namespace LpAtomFamily

/-- Predicate saying that an ambient `L^p` vector is an atom supported on `Q`. -/
def IsAtom (A : LpAtomFamily G s p) (Q : WeakGridCell G)
    (f : MeasureTheory.Lp ℂ p G.measure) : Prop :=
  f ∈ A.atoms Q

/-- For every cell there exists at least one direct `L^p` atom. -/
theorem atoms_nonempty_on (A : LpAtomFamily G s p) (Q : WeakGridCell G) :
    ∃ f : MeasureTheory.Lp ℂ p G.measure, A.IsAtom Q f :=
  A.atoms_nonempty Q

/-- Direct `L^p` atoms are supported on their cell, modulo null sets. -/
theorem atom_supported (A : LpAtomFamily G s p)
    {Q : WeakGridCell G} {f : MeasureTheory.Lp ℂ p G.measure}
    (hf : A.IsAtom Q f) :
    LpSupportedOn G p Q f :=
  A.atoms_supported Q f hf

/-- Direct `L^p` atoms satisfy the family size bound. -/
theorem atom_norm_bound (A : LpAtomFamily G s p)
    {Q : WeakGridCell G} {f : MeasureTheory.Lp ℂ p G.measure}
    (hf : A.IsAtom Q f) :
    ‖f‖ ≤ (G.measure Q.cell).toReal ^ s :=
  A.atom_bound Q f hf

/-- The set of all atoms in a direct `L^p` atom family. -/
def allAtoms (A : LpAtomFamily G s p) : Set (MeasureTheory.Lp ℂ p G.measure) :=
  { f | ∃ Q : WeakGridCell G, A.IsAtom Q f }

end LpAtomFamily

/--
The raw direct `(s,p)` atom condition in ambient `L^p`.

Such an atom is supported on the cell `Q`, modulo null sets, and its ambient
`L^p` norm is bounded by `μ(Q)^s`.
-/
def IsLpSizeAtom
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (Q : WeakGridCell G) (f : MeasureTheory.Lp ℂ p G.measure) : Prop :=
  LpSupportedOn G p Q f ∧ ‖f‖ ≤ (G.measure Q.cell).toReal ^ s

private theorem isLpSizeAtom_convex
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)]
    (Q : WeakGridCell G) :
    Convex ℝ {f : MeasureTheory.Lp ℂ p G.measure | IsLpSizeAtom G s p Q f} := by
  intro f hf g hg a b ha hb hab
  rcases hf with ⟨hf_supp, hf_norm⟩
  rcases hg with ⟨hg_supp, hg_norm⟩
  constructor
  · have hsupp :
        LpSupportedOn G p Q ((a : ℂ) • f + (b : ℂ) • g) :=
      lpSupportedOn_add G p Q
        (lpSupportedOn_smul G p Q (a : ℂ) hf_supp)
        (lpSupportedOn_smul G p Q (b : ℂ) hg_supp)
    simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using hsupp
  · calc
      ‖a • f + b • g‖ ≤ ‖a • f‖ + ‖b • g‖ :=
        norm_add_le (a • f) (b • g)
      _ = ‖a‖ * ‖f‖ + ‖b‖ * ‖g‖ := by
        rw [norm_smul, norm_smul]
      _ ≤ ‖a‖ * ((G.measure Q.cell).toReal ^ s) +
          ‖b‖ * ((G.measure Q.cell).toReal ^ s) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hf_norm (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hg_norm (norm_nonneg _))
      _ = (a + b) * ((G.measure Q.cell).toReal ^ s) := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
            ring
      _ = (G.measure Q.cell).toReal ^ s := by rw [hab, one_mul]

/-- Raw direct `(s,p)` atoms are invariant under multiplication by a complex phase. -/
theorem isLpSizeAtom_phase_invariant
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)]
    (Q : WeakGridCell G) {f : MeasureTheory.Lp ℂ p G.measure} {σ : ℂ}
    (hf : IsLpSizeAtom G s p Q f) (hσ : ‖σ‖ = (1 : ℝ)) :
    IsLpSizeAtom G s p Q (σ • f) := by
  rcases hf with ⟨hf_supp, hf_norm⟩
  constructor
  · exact lpSupportedOn_smul G p Q σ hf_supp
  · calc
      ‖σ • f‖ = ‖σ‖ * ‖f‖ := norm_smul σ f
      _ = ‖f‖ := by rw [hσ, one_mul]
      _ ≤ (G.measure Q.cell).toReal ^ s := hf_norm

/--
The direct `L^p` atom family of all supported vectors with the standard
`μ(Q)^s` size bound.

This is the simplest concrete model for the new direct API: atoms are already
ambient `L^p` classes, and their support is imposed modulo null sets.
-/
noncomputable def lpSizeAtomFamily
    (G : WeakGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) [Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    LpAtomFamily G s p where
  s_pos := hs
  one_le_p := Fact.out
  p_ne_top := hp_top
  atoms := fun Q => {f : MeasureTheory.Lp ℂ p G.measure | IsLpSizeAtom G s p Q f}
  atoms_nonempty := by
    intro Q
    refine ⟨0, ?_⟩
    constructor
    · exact lpSupportedOn_zero G p Q
    · calc
        ‖(0 : MeasureTheory.Lp ℂ p G.measure)‖ = 0 := norm_zero
        _ ≤ (G.measure Q.cell).toReal ^ s := Real.rpow_nonneg ENNReal.toReal_nonneg s
  atoms_supported := by
    intro Q f hf
    exact hf.1
  atoms_convex := by
    intro Q
    exact isLpSizeAtom_convex G s p Q
  atoms_phase_invariant := by
    intro Q f σ hf hσ
    exact isLpSizeAtom_phase_invariant G s p Q hf hσ
  atom_bound := by
    intro Q f hf
    exact hf.2

end

end WeakGridSpace
