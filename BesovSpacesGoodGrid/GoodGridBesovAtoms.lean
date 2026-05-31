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

/-- The Besov-atom normalization constant is nonnegative. -/
theorem besovAtomConstant_nonneg
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞) :
    0 ≤ besovAtomConstant G β p qtilde := by
  unfold besovAtomConstant
  refine mul_nonneg (Real.rpow_nonneg (by positivity) _) ?_
  split_ifs
  · norm_num
  · exact Real.rpow_nonneg
      (tsum_nonneg fun k =>
        Real.rpow_nonneg
          (pow_nonneg (le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2) k) _)
      _

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
    (souzaAtomFamily G β p hβ hp.out hp_top)

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

/-- The local space of concrete `L^p` representatives supported on a cell. -/
def besovAtomLocalSubmodule
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞) (Q : GoodGridCell G) :
    Submodule ℂ (α → ℂ) where
  carrier := { a | MemLp a p G.grid.μ ∧ ∀ x, x ∉ Q.cell → a x = 0 }
  zero_mem' := by
    constructor
    · exact MemLp.zero
    · intro x hx
      rfl
  add_mem' := by
    intro a b ha hb
    constructor
    · exact ha.1.add hb.1
    · intro x hx
      simp [ha.2 x hx, hb.2 x hx]
  smul_mem' := by
    intro c a ha
    constructor
    · exact ha.1.const_smul c
    · intro x hx
      simp [ha.2 x hx]

/-- Local vector space used for Besov atoms on a fixed good-grid cell. -/
def besovAtomLocalVectorSpace
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞) (Q : GoodGridCell G) :
    WeakGridSpace.LocalVectorSpace α where
  carrier := besovAtomLocalSubmodule G p Q
  toFun :=
    { toFun := fun a => a
      map_add' := by
        intro a b
        rfl
      map_smul' := by
        intro c a
        rfl }
  injective_toFun := by
    intro a b hab
    ext x
    exact congrFun hab x

/-- The zero representative is a Besov atom. -/
theorem zero_isBesovAtom
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞) [Fact (1 ≤ qtilde)]
    (Q : GoodGridCell G) :
    IsBesovAtom G s β p qtilde hβ hp hp_top Q 0 := by
  let A := inducedSouzaAtomFamily G β p hβ hp hp_top Q
  let R : WeakGridSpace.LpGridRepresentation A (0 : Lp ℂ p G.grid.μ) :=
    { block := fun k => WeakGridSpace.LevelBlock.zero A k
      hasSum := by
        have hterms :
            (fun k => (WeakGridSpace.LevelBlock.zero A k).toLp A) =
              fun _ : ℕ => (0 : Lp ℂ p G.grid.μ) := by
          funext k
          exact WeakGridSpace.LevelBlock.zero_toLp A k
        rw [hterms]
        exact (hasSum_zero : HasSum (fun _ : ℕ => (0 : Lp ℂ p G.grid.μ)) 0) }
  refine ⟨MemLp.zero, R, ?_, ?_⟩
  · have hp_pos : 0 < p.toReal :=
      (ENNReal.toReal_pos_iff_ne_top p).2 hp_top
    have hzero : ∀ k, R.levelCoeffPower k = 0 := by
      intro k
      unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
      simp [R, WeakGridSpace.LevelBlock.zero, Real.zero_rpow hp_pos.ne']
    by_cases hq : qtilde = ∞
    · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_pos hq]
      refine ⟨0, ?_⟩
      rintro x ⟨k, rfl⟩
      have hinv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
      simpa [hzero k, Real.zero_rpow hinv_pos.ne']
    · have hq_pos : 0 < qtilde.toReal :=
        ENNReal.toReal_pos ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le
          (Fact.out : 1 ≤ qtilde)).ne' hq
      have hpow_pos : 0 < qtilde.toReal / p.toReal := div_pos hq_pos hp_pos
      rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hq]
      simpa [hzero, Real.zero_rpow hpow_pos.ne'] using
        (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  · have hp_pos : 0 < p.toReal :=
      (ENNReal.toReal_pos_iff_ne_top p).2 hp_top
    have hzero : ∀ k, R.levelCoeffPower k = 0 := by
      intro k
      unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
      simp [R, WeakGridSpace.LevelBlock.zero, Real.zero_rpow hp_pos.ne']
    have hcost_zero :
        WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) R = 0 := by
      by_cases hq : qtilde = ∞
      · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos hq]
        have hinv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
        have hfun :
            (fun k => R.levelCoeffPower k ^ (1 / p.toReal)) = fun _ : ℕ => 0 := by
          funext k
          simpa [hzero k] using Real.zero_rpow hinv_pos.ne'
        rw [hfun]
        simp
      · have hq_pos : 0 < qtilde.toReal :=
          ENNReal.toReal_pos ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le
            (Fact.out : 1 ≤ qtilde)).ne' hq
        have hpow_pos : 0 < qtilde.toReal / p.toReal := div_pos hq_pos hp_pos
        rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hq]
        have hinv_pos : 0 < qtilde.toReal⁻¹ := inv_pos.mpr hq_pos
        simp [hzero, Real.zero_rpow hpow_pos.ne', Real.zero_rpow hinv_pos.ne']
    calc
      R.pqCost = 0 := hcost_zero
      _ ≤ (besovAtomConstant G β p qtilde)⁻¹ * (G.grid.μ Q.cell).toReal ^ (s - β) :=
        mul_nonneg (inv_nonneg.mpr (besovAtomConstant_nonneg G β p qtilde))
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-- Besov atoms are convex as a set of concrete representatives. -/
theorem convex_isBesovAtom
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) :
    Convex ℝ { a : (besovAtomLocalVectorSpace G p Q).carrier |
      IsBesovAtom G s β p qtilde hβ hp hp_top Q
        ((besovAtomLocalVectorSpace G p Q).toFun a) } := by
  sorry

/-- Besov atoms are invariant under complex scalars of modulus one. -/
theorem isBesovAtom_smul_of_norm_eq_one
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) {a : α → ℂ} (σ : ℂ)
    (ha : IsBesovAtom G s β p qtilde hβ hp hp_top Q a)
    (hσ : ‖σ‖ = (1 : ℝ)) :
    IsBesovAtom G s β p qtilde hβ hp hp_top Q (σ • a) := by
  sorry

/-- The defining Besov normalization gives the ordinary atom size bound. -/
theorem isBesovAtom_eLpNorm_le
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    (Q : GoodGridCell G) {a : α → ℂ}
    (ha : IsBesovAtom G s β p qtilde hβ hp hp_top Q a) :
    eLpNorm a p G.grid.μ ≤ (G.grid.μ Q.cell) ^ s := by
  sorry

/--
The family of Besov atoms as an `AtomFamily`.

This is the formal package corresponding to
`A^{bs}_{s,β,p,qtilde}`.  The local carrier is intentionally packaged as an
`AtomFamily` so it can be passed directly to the existing Besov-ish and
transmutation theorems.
-/
noncomputable def besovAtomFamily
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞)
    [Fact (1 ≤ qtilde)] :
    WeakGridSpace.AtomFamily.{u, u} G.toWeakGridSpace s p 1 := by
  classical
  refine
    { uConj := ∞
      s_pos := hs
      one_le_p := hp.out
      p_ne_top := hp_top
      one_le_u := by simp
      holder_conjugate := by
        rw [ENNReal.holderConjugate_iff]
        simp
      localSpace := fun Q =>
        besovAtomLocalVectorSpace G p ⟨Q.level, Q.cell, Q.mem⟩
      atoms := fun Q =>
        { a | IsBesovAtom G s β p qtilde hβ hp hp_top ⟨Q.level, Q.cell, Q.mem⟩
            ((besovAtomLocalVectorSpace G p ⟨Q.level, Q.cell, Q.mem⟩).toFun a) }
      atoms_nonempty := ?_
      local_memLp := ?_
      local_support := ?_
      atoms_convex := ?_
      atoms_phase_invariant := ?_
      atom_bound := ?_ }
  · intro Q
    refine ⟨0, ?_⟩
    simpa [besovAtomLocalVectorSpace] using
      zero_isBesovAtom G s β p qtilde hβ hp hp_top ⟨Q.level, Q.cell, Q.mem⟩
  · intro Q a
    rw [mul_one]
    exact a.2.1
  · intro Q a x hx
    exact a.2.2 x hx
  · intro Q
    simpa using
      convex_isBesovAtom G s β p qtilde hβ hp hp_top ⟨Q.level, Q.cell, Q.mem⟩
  · intro Q a σ ha hσ
    exact isBesovAtom_smul_of_norm_eq_one G s β p qtilde hβ hp hp_top
      ⟨Q.level, Q.cell, Q.mem⟩ σ ha hσ
  · intro Q a ha
    rw [mul_one]
    calc
      eLpNorm
          ((besovAtomLocalVectorSpace G p ⟨Q.level, Q.cell, Q.mem⟩).toFun a)
          p G.toWeakGridSpace.measure
          ≤ (G.grid.μ Q.cell) ^ s := by
            exact isBesovAtom_eLpNorm_le G s β p qtilde hβ hp hp_top
              ⟨Q.level, Q.cell, Q.mem⟩ ha
      _ = WeakGridSpace.atomMeasureScale G.toWeakGridSpace s p ∞ Q := by
            simp [WeakGridSpace.atomMeasureScale, WeakGridSpace.atomMeasureExponent,
              GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
              WeakGridSpace.WeakGridSpace.measure]

/--
Besov atoms are ordinary `(s,p,1)` atoms.

This is the formal version of the estimate
`|a|_p ≤ |Q|^s`, obtained from the induced `L^p` embedding and the defining
Besov-atom normalization.
-/
theorem besovAtom_is_sp_one_atom
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hp : Fact (1 ≤ p)) (hp_top : p ≠ ∞) [Fact (1 ≤ qtilde)]
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
    [Fact (1 ≤ qtilde)]
    (A : WeakGridSpace.AtomFamily G.toWeakGridSpace s p u)
    (C56 C566 : ℝ) : Prop :=
  (∀ Q φ,
      (souzaAtomFamily G s p hs hp.out hp_top).IsAtom Q φ →
        ∃ ψ, A.IsAtom Q ψ ∧
          A.toFunction Q ψ =
            (C56⁻¹ : ℂ) •
              (souzaAtomFamily G s p hs hp.out hp_top).toFunction Q φ) ∧
  (∀ Q φ,
      A.IsAtom Q φ →
        ∃ ψ : ((besovAtomFamily G s β p qtilde hs hβ hp hp_top).localSpace Q).carrier,
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
    [Fact (1 ≤ p)] [Fact (1 ≤ u)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β) (hp_top : p ≠ ∞)
    (A : WeakGridSpace.AtomFamily G.toWeakGridSpace s p u)
    (C56 C566 : ℝ) (hC56 : 0 ≤ C56) (hC566 : 0 ≤ C566)
    (hSandwich :
      SouzaBesovSandwich G s β p u qtilde hs hβ (inferInstance : Fact (1 ≤ p))
        hp_top A C56 C566) :
    (WeakGridSpace.BesovishSpace (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q =
        WeakGridSpace.BesovishSpace A q) ∧
      (WeakGridSpace.BesovishSpace A q =
        WeakGridSpace.BesovishSpace
          (besovAtomFamily G s β p qtilde hs hβ inferInstance hp_top) q) ∧
      (∀ f : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q,
        ∃ hfA : WeakGridSpace.MemBesovishCoeffCost A q
            (f : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.BesovishSpace.Norm_Costpq A q
              (⟨(f : Lp ℂ p G.toWeakGridSpace.measure), hfA⟩ :
                WeakGridSpace.BesovishSpace A q)
            ≤ C56 *
              WeakGridSpace.BesovishSpace.Norm_Costpq
                (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q f) ∧
      (∀ f : WeakGridSpace.BesovishSpace A q,
        ∃ hfS : WeakGridSpace.MemBesovishCoeffCost
            (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q
            (f : Lp ℂ p G.toWeakGridSpace.measure),
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q
              (⟨(f : Lp ℂ p G.toWeakGridSpace.measure), hfS⟩ :
                WeakGridSpace.BesovishSpace
                  (souzaAtomFamily G s p hs (Fact.out : 1 ≤ p) hp_top) q)
            ≤ (C566 / (1 - G.grid.lambda2 ^ (β - s))) *
              WeakGridSpace.BesovishSpace.Norm_Costpq A q f) := by
  -- The second embedding is exactly the transmutation argument: expand each
  -- Besov atom on the induced grid inside its support, rescale the resulting
  -- `β`-Souza atoms to `s`-Souza atoms, and sum the geometric tail.
  sorry

end

end GoodGridSpace
