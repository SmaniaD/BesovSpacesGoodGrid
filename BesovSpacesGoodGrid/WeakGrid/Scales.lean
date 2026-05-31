import BesovSpacesGoodGrid.WeakGrid.BesovishSpaces

/-!
Scales of Besov-ish atom families.

This file packages the scale constructions used later for Besov-ish spaces.
Starting from an atom family with parameters `s`, `p`, and `u`, it records two
ways to rescale the atoms cell by cell.

The first construction changes only the smoothness parameter. The second one,
available when `u = ∞`, changes both the smoothness and the integrability
parameter.

After defining the scaled atom families, the file proves the basic inclusion
result for the one-parameter smoothness scale at the level of Besov-ish
spaces.
-/

variable {α : Type*} [MeasurableSpace α]

namespace WeakGridSpace

open scoped ENNReal Topology
open MeasureTheory

noncomputable section

variable {G : WeakGridSpace (α := α)} {s sTilde : ℝ} {p pTilde u : ℝ≥0∞}

namespace AtomFamily

/--
Scalar used to pass from smoothness `s` to smoothness `sTilde` on a cell `Q`.
-/
noncomputable def smoothnessScaleFactor
    (G : WeakGridSpace (α := α)) (s sTilde : ℝ)
    (Q : WeakGridCell G) : ℝ :=
  (G.measure Q.cell).toReal ^ (sTilde - s)

/--
Raw atom set for the one-parameter smoothness scale.

An element of this set is obtained by taking an original atom on `Q` and
multiplying it by the smoothness scale factor. The local vector spaces are not
changed here; this is only the underlying set of scaled atoms.
-/
noncomputable def smoothnessScaleAtoms
    (A : AtomFamily G s p u) (sTilde : ℝ)
    (Q : WeakGridCell G) : Set ((A.localSpace Q).carrier) :=
  { φ | ∃ a ∈ A.atoms Q,
      φ = smoothnessScaleFactor G s sTilde Q • a }

/-- Membership in the smoothness-scaled atom set is given by the defining witness. -/
theorem mem_smoothnessScaleAtoms
    (A : AtomFamily G s p u) (sTilde : ℝ)
    (Q : WeakGridCell G) (φ : (A.localSpace Q).carrier) :
    φ ∈ A.smoothnessScaleAtoms sTilde Q ↔
      ∃ a ∈ A.atoms Q,
        φ = smoothnessScaleFactor G s sTilde Q • a :=
  Iff.rfl

/--
Scalar used for the two-parameter scale when both smoothness and
integrability are changed.
-/
noncomputable def smoothnessIntegrabilityScaleFactor
    (G : WeakGridSpace (α := α)) (s sTilde : ℝ)
    (p pTilde : ℝ≥0∞) (Q : WeakGridCell G) : ℝ :=
  (G.measure Q.cell).toReal ^ (sTilde - s + 1 / p.toReal - 1 / pTilde.toReal)

/--
Raw atom set for the two-parameter scale when `u = ∞`.

An element of this set is obtained by multiplying an original atom on `Q` by
the combined smoothness and integrability factor. As above, this only changes
the set of atoms, not the ambient local spaces.
-/
noncomputable def smoothnessIntegrabilityScaleAtoms
    (A : AtomFamily G s p ∞) (sTilde : ℝ) (pTilde : ℝ≥0∞)
    (Q : WeakGridCell G) : Set ((A.localSpace Q).carrier) :=
  { φ | ∃ a ∈ A.atoms Q,
      φ = smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q • a }

/-- Membership in the two-parameter scaled atom set is given by the defining witness. -/
theorem mem_smoothnessIntegrabilityScaleAtoms
    (A : AtomFamily G s p ∞) (sTilde : ℝ) (pTilde : ℝ≥0∞)
    (Q : WeakGridCell G) (φ : (A.localSpace Q).carrier) :
    φ ∈ A.smoothnessIntegrabilityScaleAtoms sTilde pTilde Q ↔
      ∃ a ∈ A.atoms Q,
        φ = smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q • a :=
  Iff.rfl

/-- Every grid cell has strictly positive measure. -/
private theorem weakGridCell_measure_pos (G : WeakGridSpace (α := α))
    (Q : WeakGridCell G) : 0 < G.measure Q.cell := by
  simpa [WeakGridSpace.measure] using
    G.grid.positive_measure Q.level Q.cell Q.mem

/-- Every grid cell has finite measure. -/
private theorem weakGridCell_measure_ne_top (G : WeakGridSpace (α := α))
    (Q : WeakGridCell G) : G.measure Q.cell ≠ ∞ := by
  haveI : IsFiniteMeasure G.measure := by
    dsimp [WeakGridSpace.measure]
    exact G.grid.isFinite
  exact measure_ne_top G.measure Q.cell

/-- The complex norm of the one-parameter scale factor matches the expected cell weight. -/
private theorem enorm_smoothnessScaleFactor
    (G : WeakGridSpace (α := α)) (s sTilde : ℝ) (Q : WeakGridCell G) :
    ‖(smoothnessScaleFactor G s sTilde Q : ℂ)‖ₑ =
      (G.measure Q.cell) ^ (sTilde - s) := by
  have hQ_pos : 0 < G.measure Q.cell := weakGridCell_measure_pos G Q
  have hQ_ne_zero : G.measure Q.cell ≠ 0 := ne_of_gt hQ_pos
  have hQ_ne_top : G.measure Q.cell ≠ ∞ := weakGridCell_measure_ne_top G Q
  have hfactor_nonneg : 0 ≤ smoothnessScaleFactor G s sTilde Q := by
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfactor_nonneg]
  dsimp [smoothnessScaleFactor]
  calc
    ENNReal.ofReal ((G.measure Q.cell).toReal ^ (sTilde - s))
        = ENNReal.ofReal (((G.measure Q.cell) ^ (sTilde - s)).toReal) := by
            rw [ENNReal.toReal_rpow]
    _ = (G.measure Q.cell) ^ (sTilde - s) :=
            ENNReal.ofReal_toReal
              (ENNReal.rpow_ne_top_of_ne_zero hQ_ne_zero hQ_ne_top)

/-- The same norm computation for the two-parameter scale factor. -/
private theorem enorm_smoothnessIntegrabilityScaleFactor
    (G : WeakGridSpace (α := α)) (s sTilde : ℝ) (p pTilde : ℝ≥0∞)
    (Q : WeakGridCell G) :
    ‖(smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q : ℂ)‖ₑ =
      (G.measure Q.cell) ^ (sTilde - s + 1 / p.toReal - 1 / pTilde.toReal) := by
  have hQ_pos : 0 < G.measure Q.cell := weakGridCell_measure_pos G Q
  have hQ_ne_zero : G.measure Q.cell ≠ 0 := ne_of_gt hQ_pos
  have hQ_ne_top : G.measure Q.cell ≠ ∞ := weakGridCell_measure_ne_top G Q
  have hfactor_nonneg :
      0 ≤ smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q := by
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfactor_nonneg]
  dsimp [smoothnessIntegrabilityScaleFactor]
  calc
    ENNReal.ofReal
        ((G.measure Q.cell).toReal ^
          (sTilde - s + 1 / p.toReal - 1 / pTilde.toReal))
        =
        ENNReal.ofReal
          (((G.measure Q.cell) ^
            (sTilde - s + 1 / p.toReal - 1 / pTilde.toReal)).toReal) := by
            rw [ENNReal.toReal_rpow]
    _ = (G.measure Q.cell) ^
          (sTilde - s + 1 / p.toReal - 1 / pTilde.toReal) :=
            ENNReal.ofReal_toReal
              (ENNReal.rpow_ne_top_of_ne_zero hQ_ne_zero hQ_ne_top)

/-- In the `u = ∞` case, the Hölder conjugate is forced to be `1`. -/
private theorem holderConjugate_top_eq_one {uConj : ℝ≥0∞}
    (h : ENNReal.HolderConjugate ∞ uConj) : uConj = 1 := by
  simpa using (ENNReal.holderConjugate_iff.mp h)

/-- `toFunction` commutes with real scalar multiplication. -/
private theorem toFunction_real_smul
    (A : AtomFamily G s p u) (Q : WeakGridCell G)
    (r : ℝ) (a : (A.localSpace Q).carrier) :
    A.toFunction Q (r • a) = r • A.toFunction Q a := by
  funext x
  simp [AtomFamily.toFunction]

/-- The smoothness-scaled atom set is convex whenever the original atom set is. -/
private theorem convex_smoothnessScaleAtoms
    (A : AtomFamily G s p u) (sTilde : ℝ) (Q : WeakGridCell G) :
    Convex ℝ (A.smoothnessScaleAtoms sTilde Q) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨φ, hφ, rfl⟩
  rcases hy with ⟨ψ, hψ, rfl⟩
  refine ⟨a • φ + b • ψ, (A.atoms_convex Q) hφ hψ ha hb hab, ?_⟩
  calc
    a • (smoothnessScaleFactor G s sTilde Q • φ) +
        b • (smoothnessScaleFactor G s sTilde Q • ψ)
        = smoothnessScaleFactor G s sTilde Q • (a • φ) +
            smoothnessScaleFactor G s sTilde Q • (b • ψ) := by
              simp [smul_smul, mul_comm]
    _ = smoothnessScaleFactor G s sTilde Q • (a • φ + b • ψ) := by
          rw [smul_add]

/-- The two-parameter scaled atom set is convex whenever the original atom set is. -/
private theorem convex_smoothnessIntegrabilityScaleAtoms
    (A : AtomFamily G s p ∞) (sTilde : ℝ) (pTilde : ℝ≥0∞)
    (Q : WeakGridCell G) :
    Convex ℝ (A.smoothnessIntegrabilityScaleAtoms sTilde pTilde Q) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨φ, hφ, rfl⟩
  rcases hy with ⟨ψ, hψ, rfl⟩
  refine ⟨a • φ + b • ψ, (A.atoms_convex Q) hφ hψ ha hb hab, ?_⟩
  calc
    a • (smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q • φ) +
        b • (smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q • ψ)
        = smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q • (a • φ) +
            smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q • (b • ψ) := by
              simp [smul_smul, mul_comm]
    _ = smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q • (a • φ + b • ψ) := by
          rw [smul_add]

/--
Full atom family associated to the one-parameter smoothness scale.

This upgrades the raw scaled atom set to an `AtomFamily` by reusing the local
spaces and checking the required analytic properties.
-/
noncomputable def smoothnessScaleAtomFamily
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde) :
    AtomFamily G sTilde p u where
  uConj := A.uConj
  s_pos := hsTilde_pos
  one_le_p := A.one_le_p
  p_ne_top := A.p_ne_top
  one_le_u := A.one_le_u
  holder_conjugate := A.holder_conjugate
  localSpace := A.localSpace
  atoms := A.smoothnessScaleAtoms sTilde
  atoms_nonempty := by
    intro Q
    rcases A.atoms_nonempty Q with ⟨a, ha⟩
    exact ⟨smoothnessScaleFactor G s sTilde Q • a, a, ha, rfl⟩
  local_memLp := by
    intro Q φ
    exact A.local_memLp Q φ
  local_support := by
    intro Q φ x hx
    exact A.local_support Q φ x hx
  atoms_convex := convex_smoothnessScaleAtoms A sTilde
  atoms_phase_invariant := by
    intro Q φ σ hφ hσ
    rcases hφ with ⟨a, ha, rfl⟩
    refine ⟨σ • a, A.atoms_phase_invariant Q a σ ha hσ, ?_⟩
    rw [smul_comm]
  atom_bound := by
    intro Q φ hφ
    rcases hφ with ⟨a, ha, rfl⟩
    have hQ_pos : 0 < G.measure Q.cell := weakGridCell_measure_pos G Q
    have hQ_ne_zero : G.measure Q.cell ≠ 0 := ne_of_gt hQ_pos
    have hQ_ne_top : G.measure Q.cell ≠ ∞ := weakGridCell_measure_ne_top G Q
    have hfun :
        A.toFunction Q (smoothnessScaleFactor G s sTilde Q • a) =
          (smoothnessScaleFactor G s sTilde Q : ℂ) • A.toFunction Q a := by
      rw [toFunction_real_smul]
      funext x
      simp [Pi.smul_apply]
    have hscale_old :
        ‖(smoothnessScaleFactor G s sTilde Q : ℂ)‖ₑ *
            atomMeasureScale G s p A.uConj Q =
          atomMeasureScale G sTilde p A.uConj Q := by
      rw [enorm_smoothnessScaleFactor]
      simp only [atomMeasureScale]
      rw [← ENNReal.rpow_add _ _ hQ_ne_zero hQ_ne_top]
      congr 1
      unfold atomMeasureExponent
      ring
    calc
      MeasureTheory.eLpNorm
          (A.toFunction Q (smoothnessScaleFactor G s sTilde Q • a))
          (p * u) G.measure
          = MeasureTheory.eLpNorm
              ((smoothnessScaleFactor G s sTilde Q : ℂ) • A.toFunction Q a)
              (p * u) G.measure := by rw [hfun]
      _ = ‖(smoothnessScaleFactor G s sTilde Q : ℂ)‖ₑ *
            MeasureTheory.eLpNorm (A.toFunction Q a) (p * u) G.measure := by
              rw [MeasureTheory.eLpNorm_const_smul]
      _ ≤ ‖(smoothnessScaleFactor G s sTilde Q : ℂ)‖ₑ *
            atomMeasureScale G s p A.uConj Q :=
              mul_le_mul_of_nonneg_left (A.atom_norm_bound ha) bot_le
      _ = atomMeasureScale G sTilde p A.uConj Q := hscale_old

    /--
    Full atom family associated to the two-parameter scale when `u = ∞`.

    Compared with `smoothnessScaleAtomFamily`, this version also replaces `p` by
    `pTilde` and checks the corresponding analytic bounds.
    -/
noncomputable def smoothnessIntegrabilityScaleAtomFamily
    (A : AtomFamily G s p ∞) (sTilde : ℝ) (pTilde : ℝ≥0∞)
    (hsTilde_pos : 0 < sTilde)
    (hpTilde_one : 1 ≤ pTilde) (hpTilde_ne_top : pTilde ≠ ∞) :
    AtomFamily G sTilde pTilde ∞ where
  uConj := A.uConj
  s_pos := hsTilde_pos
  one_le_p := hpTilde_one
  p_ne_top := hpTilde_ne_top
  one_le_u := A.one_le_u
  holder_conjugate := A.holder_conjugate
  localSpace := A.localSpace
  atoms := A.smoothnessIntegrabilityScaleAtoms sTilde pTilde
  atoms_nonempty := by
    intro Q
    rcases A.atoms_nonempty Q with ⟨a, ha⟩
    exact ⟨smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q • a, a, ha, rfl⟩
  local_memLp := by
    intro Q φ
    have hp_ne_zero : p ≠ 0 := ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le A.one_le_p)
    have hpTilde_ne_zero : pTilde ≠ 0 := ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le hpTilde_one)
    simpa [ENNReal.mul_top hpTilde_ne_zero, ENNReal.mul_top hp_ne_zero] using A.local_memLp Q φ
  local_support := by
    intro Q φ x hx
    exact A.local_support Q φ x hx
  atoms_convex := convex_smoothnessIntegrabilityScaleAtoms A sTilde pTilde
  atoms_phase_invariant := by
    intro Q φ σ hφ hσ
    rcases hφ with ⟨a, ha, rfl⟩
    refine ⟨σ • a, A.atoms_phase_invariant Q a σ ha hσ, ?_⟩
    rw [smul_comm]
  atom_bound := by
    intro Q φ hφ
    rcases hφ with ⟨a, ha, rfl⟩
    have hQ_pos : 0 < G.measure Q.cell := weakGridCell_measure_pos G Q
    have hQ_ne_zero : G.measure Q.cell ≠ 0 := ne_of_gt hQ_pos
    have hQ_ne_top : G.measure Q.cell ≠ ∞ := weakGridCell_measure_ne_top G Q
    have hA_uConj : A.uConj = 1 := holderConjugate_top_eq_one A.holder_conjugate
    have hfun :
        A.toFunction Q (smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q • a) =
          (smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q : ℂ) • A.toFunction Q a := by
      rw [toFunction_real_smul]
      funext x
      simp [Pi.smul_apply]
    have hp_ne_zero : p ≠ 0 := ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le A.one_le_p)
    have hpTilde_ne_zero : pTilde ≠ 0 := ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le hpTilde_one)
    have hp_mul_top : p * ∞ = ∞ := ENNReal.mul_top hp_ne_zero
    have hpTilde_mul_top : pTilde * ∞ = ∞ := ENNReal.mul_top hpTilde_ne_zero
    have hscale_old :
        ‖(smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q : ℂ)‖ₑ *
            atomMeasureScale G s p A.uConj Q =
          atomMeasureScale G sTilde pTilde A.uConj Q := by
      rw [enorm_smoothnessIntegrabilityScaleFactor]
      simp only [atomMeasureScale]
      rw [← ENNReal.rpow_add _ _ hQ_ne_zero hQ_ne_top]
      congr 1
      unfold atomMeasureExponent
      simp [hA_uConj]
      ring
    calc
      MeasureTheory.eLpNorm
          (A.toFunction Q (smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q • a))
        (pTilde * ∞) G.measure
        = MeasureTheory.eLpNorm
            (A.toFunction Q (smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q • a))
            (p * ∞) G.measure := by rw [hpTilde_mul_top, hp_mul_top]
      _ = MeasureTheory.eLpNorm
            ((smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q : ℂ) • A.toFunction Q a)
            (p * ∞) G.measure := by rw [hfun]
      _ = ‖(smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q : ℂ)‖ₑ *
            MeasureTheory.eLpNorm (A.toFunction Q a) (p * ∞) G.measure := by
              rw [MeasureTheory.eLpNorm_const_smul]
      _ ≤ ‖(smoothnessIntegrabilityScaleFactor G s sTilde p pTilde Q : ℂ)‖ₑ *
            atomMeasureScale G s p A.uConj Q :=
            mul_le_mul_of_nonneg_left (A.atom_norm_bound ha) bot_le
      _ = atomMeasureScale G sTilde pTilde A.uConj Q := hscale_old

/--
The Besov-ish space associated to a chosen realization of the one-parameter
scaled atom family.

This is an abbreviation over the full scaled atom family, not only over the raw
set of scaled atoms.
-/
abbrev SmoothnessScaleBesovishSpace
    (Atilde : AtomFamily G sTilde p u) (q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ u)] [Fact (1 ≤ q)] :=
  BesovishSpace Atilde q

/--
The Besov-ish space associated to a chosen realization of the two-parameter
scaled atom family.
-/
abbrev SmoothnessIntegrabilityScaleBesovishSpace
    (Atilde : AtomFamily G sTilde pTilde ∞) (q : ℝ≥0∞)
    [Fact (1 ≤ pTilde)] [Fact (1 ≤ q)] :=
  BesovishSpace Atilde q

section SmoothnessScaleBesovishSpaces

variable {q qTilde : ℝ≥0∞}

/--
Levelwise weight attached to the change from `s` to `sTilde`.

This is the scalar that appears in the coefficient estimates after a
representation for the scaled atom family is converted back to a
representation for the original family.
-/
noncomputable def smoothnessScaleLevelWeight
    (G : WeakGridSpace (α := α)) (s sTilde : ℝ) (p : ℝ≥0∞) : ℕ → ℝ :=
  fun k => LpGridRepresentation.levelMeasureWeight G (sTilde - s) p p k

/--
Size of a levelwise weight sequence in the `q`-scale.

For finite `q`, this is the usual `l^q` size. For `q = ∞`, this is the
supremum of the sequence.
-/
noncomputable def scaleCoefficient
    (q : ℝ≥0∞) (w : ℕ → ℝ) : ℝ :=
  if q = ∞ then
    sSup (Set.range w)
  else
    (∑' k, w k ^ q.toReal) ^ (1 / q.toReal)

/--
Finiteness condition for `scaleCoefficient`.

For finite `q`, this asks summability of the `q`-powers. For `q = ∞`, it asks
that the sequence be bounded above.
-/
def scaleCoefficientFinite
    (q : ℝ≥0∞) (w : ℕ → ℝ) : Prop :=
  if q = ∞ then
    BddAbove (Set.range w)
  else
    Summable (fun k => w k ^ q.toReal)

/--
Recover an original atom from an atom in the scaled family.

This is the witness chosen from the definition of `smoothnessScaleAtoms`.
-/
private noncomputable def smoothnessScalePreimageAtom
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    {k : ℕ} (Q : LevelCell G k)
    (φ : (A.localSpace (levelCellToWeakGridCell G k Q)).carrier)
    (hφ : φ ∈ (A.smoothnessScaleAtomFamily sTilde hsTilde_pos).atoms
      (levelCellToWeakGridCell G k Q)) :
    (A.localSpace (levelCellToWeakGridCell G k Q)).carrier :=
  Classical.choose
    ((A.mem_smoothnessScaleAtoms sTilde (levelCellToWeakGridCell G k Q) φ).mp hφ)

/-- The chosen preimage atom really belongs to the original atom set. -/
private theorem smoothnessScalePreimageAtom_mem
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    {k : ℕ} (Q : LevelCell G k)
    (φ : (A.localSpace (levelCellToWeakGridCell G k Q)).carrier)
    (hφ : φ ∈ (A.smoothnessScaleAtomFamily sTilde hsTilde_pos).atoms
      (levelCellToWeakGridCell G k Q)) :
    smoothnessScalePreimageAtom A sTilde hsTilde_pos Q φ hφ ∈
      A.atoms (levelCellToWeakGridCell G k Q) := by
  exact (Classical.choose_spec
    ((A.mem_smoothnessScaleAtoms sTilde (levelCellToWeakGridCell G k Q) φ).mp hφ)).1

/--
An atom in the scaled family is the scale factor times its chosen preimage.
-/
private theorem smoothnessScalePreimageAtom_spec
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    {k : ℕ} (Q : LevelCell G k)
    (φ : (A.localSpace (levelCellToWeakGridCell G k Q)).carrier)
    (hφ : φ ∈ (A.smoothnessScaleAtomFamily sTilde hsTilde_pos).atoms
      (levelCellToWeakGridCell G k Q)) :
    φ = AtomFamily.smoothnessScaleFactor G s sTilde (levelCellToWeakGridCell G k Q) •
      smoothnessScalePreimageAtom A sTilde hsTilde_pos Q φ hφ := by
  exact (Classical.choose_spec
    ((A.mem_smoothnessScaleAtoms sTilde (levelCellToWeakGridCell G k Q) φ).mp hφ)).2

/--
Transform one block from the scaled family into a block for the original family.

The coefficients absorb the scale factor, while the atoms are replaced by the
chosen preimages.
-/
private noncomputable def smoothnessScaleToBaseBlock
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    {k : ℕ}
    (B : LevelBlock (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) k) : LevelBlock A k where
  coeff Q :=
    B.coeff Q *
      (AtomFamily.smoothnessScaleFactor G s sTilde (levelCellToWeakGridCell G k Q) : ℂ)
  atom Q := smoothnessScalePreimageAtom A sTilde hsTilde_pos Q (B.atom Q) (B.atom_mem Q)
  atom_mem Q := smoothnessScalePreimageAtom_mem A sTilde hsTilde_pos Q (B.atom Q) (B.atom_mem Q)

/--
The transformed block represents the same term as the original scaled block.
-/
private theorem smoothnessScaleToBaseBlock_term
  [Fact (1 ≤ p)]
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    {k : ℕ}
    (B : LevelBlock (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) k)
    (Q : LevelCell G k) :
    (smoothnessScaleToBaseBlock A sTilde hsTilde_pos B).term A Q =
      B.term (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) Q := by
  let Q' : WeakGridCell G := levelCellToWeakGridCell G k Q
  let a := smoothnessScalePreimageAtom A sTilde hsTilde_pos Q (B.atom Q) (B.atom_mem Q)
  have ha : B.atom Q = AtomFamily.smoothnessScaleFactor G s sTilde Q' • a := by
    simpa [Q', a] using
      smoothnessScalePreimageAtom_spec A sTilde hsTilde_pos Q (B.atom Q) (B.atom_mem Q)
  have hfun :
      A.toFunction Q' (B.atom Q) =
        (AtomFamily.smoothnessScaleFactor G s sTilde Q' : ℂ) • A.toFunction Q' a := by
    rw [ha, AtomFamily.toFunction_real_smul]
    funext x
    simp [Pi.smul_apply]
  have hfun' :
      (A.smoothnessScaleAtomFamily sTilde hsTilde_pos).toFunction Q' (B.atom Q) =
        (AtomFamily.smoothnessScaleFactor G s sTilde Q' : ℂ) • A.toFunction Q' a := by
    simpa [AtomFamily.smoothnessScaleAtomFamily, AtomFamily.toFunction] using hfun
  have hp_le_pu : p ≤ p * u := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * u := by
            gcongr
            exact A.one_le_u
  have hfinite : MeasureTheory.IsFiniteMeasure G.measure := by
    dsimp [WeakGridSpace.measure]
    exact G.grid.isFinite
  letI := hfinite
  have ha_memLp : MemLp (A.toFunction Q' a) p G.measure := by
    exact (A.local_memLp Q' a).mono_exponent hp_le_pu
  have htoLp_eq :
      MemLp.toLp
          (((AtomFamily.smoothnessScaleFactor G s sTilde Q' : ℂ) • A.toFunction Q' a))
          (ha_memLp.const_smul _)
        = MemLp.toLp
            ((A.smoothnessScaleAtomFamily sTilde hsTilde_pos).toFunction Q' (B.atom Q))
            ((LevelBlock.term._proof_3 (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) B Q)) := by
    simp [hfun']
  calc
    (smoothnessScaleToBaseBlock A sTilde hsTilde_pos B).term A Q
      = (B.coeff Q * (AtomFamily.smoothnessScaleFactor G s sTilde Q' : ℂ)) •
            MemLp.toLp (A.toFunction Q' a) ha_memLp := by
              rfl
    _ = B.coeff Q •
          MemLp.toLp
            (((AtomFamily.smoothnessScaleFactor G s sTilde Q' : ℂ) • A.toFunction Q' a))
            (ha_memLp.const_smul _) := by
          rw [MemLp.toLp_const_smul (f := A.toFunction Q' a)
            (hf := ha_memLp) (c := (AtomFamily.smoothnessScaleFactor G s sTilde Q' : ℂ))]
          exact (smul_smul (B.coeff Q)
            (AtomFamily.smoothnessScaleFactor G s sTilde Q' : ℂ)
            (MemLp.toLp (A.toFunction Q' a) ha_memLp)).symm
    _ = B.term (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) Q := by
          simpa [LevelBlock.term] using congrArg (fun z => B.coeff Q • z) htoLp_eq

/-- Summing the terms of the transformed block gives the same `Lp` element. -/
private theorem smoothnessScaleToBaseBlock_toLp
  [Fact (1 ≤ p)]
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    {k : ℕ}
    (B : LevelBlock (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) k) :
    (smoothnessScaleToBaseBlock A sTilde hsTilde_pos B).toLp A =
      B.toLp (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) := by
  unfold LevelBlock.toLp
  refine Finset.sum_congr rfl ?_
  intro Q _
  exact smoothnessScaleToBaseBlock_term A sTilde hsTilde_pos B Q

/--
Turn a representation in the scaled family into a representation in the
original family without changing the represented function.
-/
private noncomputable def smoothnessScaleToBaseRepresentation
  [Fact (1 ≤ p)]
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) g) :
    LpGridRepresentation A g where
  block k := smoothnessScaleToBaseBlock A sTilde hsTilde_pos (R.block k)
  hasSum := by
    refine HasSum.congr_fun R.hasSum ?_
    intro n
    exact smoothnessScaleToBaseBlock_toLp A sTilde hsTilde_pos (R.block n)

/-- The level weights are nonnegative. -/
private theorem smoothnessScaleLevelWeight_nonneg
    (G : WeakGridSpace (α := α)) (s sTilde : ℝ) (p : ℝ≥0∞) (k : ℕ) :
    0 ≤ smoothnessScaleLevelWeight G s sTilde p k := by
  exact LpGridRepresentation.levelMeasureWeight_nonneg G (sTilde - s) p p k

/--
Every level of a finite-cost representation is bounded by its total `pqCost`.
-/
private theorem levelCoeffRoot_le_pqCost
  [Fact (1 ≤ p)]
  [Fact (1 ≤ qTilde)]
    (A : AtomFamily G s p u)
    {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation A g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := qTilde) R)
    (k : ℕ) :
    (R.levelCoeffPower k) ^ (1 / p.toReal) ≤ LpGridRepresentation.pqCost (q := qTilde) R := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' A.p_ne_top
  by_cases hq : qTilde = ∞
  · simp only [LpGridRepresentation.pqCost, hq, ↓reduceIte]
    simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    exact le_csSup hRfin ⟨k, rfl⟩
  · have hq_pos : 0 < qTilde.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ qTilde)).ne' hq
    simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    simp only [LpGridRepresentation.pqCost, hq, ↓reduceIte]
    have hterm :
        R.levelCoeffPower k ^ (qTilde.toReal / p.toReal) ≤
          ∑' n, R.levelCoeffPower n ^ (qTilde.toReal / p.toReal) := by
      simpa using hRfin.sum_le_tsum ({k} : Finset ℕ)
        (fun n _ => Real.rpow_nonneg (R.levelCoeffPower_nonneg n) _)
    have hroot := Real.rpow_le_rpow
      (Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _) hterm
      (div_nonneg zero_le_one hq_pos.le)
    calc
      (R.levelCoeffPower k) ^ (1 / p.toReal)
          = (R.levelCoeffPower k ^ (qTilde.toReal / p.toReal)) ^ (1 / qTilde.toReal) := by
              rw [← Real.rpow_mul (R.levelCoeffPower_nonneg k)]
              congr 1
              field_simp [hp_pos.ne', hq_pos.ne']
      _ ≤ (∑' n, R.levelCoeffPower n ^ (qTilde.toReal / p.toReal)) ^ (1 / qTilde.toReal) := hroot

/--
Levelwise coefficient control after unscaling the representation.

The new level size is bounded by the old level size times the deterministic
weight attached to the change of smoothness.
-/
private theorem smoothnessScaleToBase_levelCoeffRoot_le
  [Fact (1 ≤ p)]
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    (hs_le : s ≤ sTilde)
    {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) g)
    (k : ℕ) :
    ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^
        (1 / p.toReal)
      ≤ smoothnessScaleLevelWeight G s sTilde p k * (R.levelCoeffPower k) ^ (1 / p.toReal) := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' A.p_ne_top
  have hexp_nonneg : 0 ≤ sTilde - s := sub_nonneg.mpr hs_le
  have hexp_nonneg' : 0 ≤ (sTilde - s) - 1 / p.toReal + 1 / p.toReal := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hexp_nonneg
  have hpower_le :
      (smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k ≤
        (smoothnessScaleLevelWeight G s sTilde p k) ^ p.toReal * R.levelCoeffPower k := by
    unfold LpGridRepresentation.levelCoeffPower smoothnessScaleToBaseRepresentation
    dsimp [smoothnessScaleToBaseBlock, smoothnessScaleLevelWeight]
    have hsum_le :
        ∑ Q : LevelCell G k,
        ‖(R.block k).coeff Q *
          (AtomFamily.smoothnessScaleFactor G s sTilde (levelCellToWeakGridCell G k Q) : ℂ)‖ ^ p.toReal
          ≤ ∑ Q : LevelCell G k,
              (smoothnessScaleLevelWeight G s sTilde p k) ^ p.toReal *
                ‖(R.block k).coeff Q‖ ^ p.toReal := by
      refine Finset.sum_le_sum fun Q _ => ?_
      have hfactor_nonneg :
          0 ≤ AtomFamily.smoothnessScaleFactor G s sTilde (levelCellToWeakGridCell G k Q) := by
        exact Real.rpow_nonneg ENNReal.toReal_nonneg _
      have hfactor_le :
          AtomFamily.smoothnessScaleFactor G s sTilde (levelCellToWeakGridCell G k Q) ≤
            LpGridRepresentation.levelMeasureWeight G (sTilde - s) p p k := by
        simpa [AtomFamily.smoothnessScaleFactor, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm] using
          LpGridRepresentation.levelCellMeasure_rpow_le_levelMeasureWeight
            G (sTilde - s) p p k hexp_nonneg' Q
      have hmul_le :
          AtomFamily.smoothnessScaleFactor G s sTilde (levelCellToWeakGridCell G k Q) *
              ‖(R.block k).coeff Q‖ ≤
            LpGridRepresentation.levelMeasureWeight G (sTilde - s) p p k * ‖(R.block k).coeff Q‖ := by
        exact mul_le_mul_of_nonneg_right hfactor_le (norm_nonneg _)
      calc
        ‖(R.block k).coeff Q *
          (AtomFamily.smoothnessScaleFactor G s sTilde (levelCellToWeakGridCell G k Q) : ℂ)‖ ^ p.toReal
            = (AtomFamily.smoothnessScaleFactor G s sTilde (levelCellToWeakGridCell G k Q) *
                ‖(R.block k).coeff Q‖) ^ p.toReal := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfactor_nonneg]
            ring_nf
        _ ≤ (LpGridRepresentation.levelMeasureWeight G (sTilde - s) p p k *
              ‖(R.block k).coeff Q‖) ^ p.toReal := by
              exact Real.rpow_le_rpow (mul_nonneg hfactor_nonneg (norm_nonneg _)) hmul_le hp_pos.le
        _ = (smoothnessScaleLevelWeight G s sTilde p k) ^ p.toReal * ‖(R.block k).coeff Q‖ ^ p.toReal := by
            simpa [smoothnessScaleLevelWeight] using
              (Real.mul_rpow
            (LpGridRepresentation.levelMeasureWeight_nonneg G (sTilde - s) p p k)
            (norm_nonneg ((R.block k).coeff Q)))
    calc
      ∑ Q : LevelCell G k,
        ‖(R.block k).coeff Q *
          (AtomFamily.smoothnessScaleFactor G s sTilde (levelCellToWeakGridCell G k Q) : ℂ)‖ ^ p.toReal
          ≤ ∑ Q : LevelCell G k,
              (smoothnessScaleLevelWeight G s sTilde p k) ^ p.toReal * ‖(R.block k).coeff Q‖ ^ p.toReal := hsum_le
      _ = (smoothnessScaleLevelWeight G s sTilde p k) ^ p.toReal * R.levelCoeffPower k := by
            rw [← Finset.mul_sum]
            simp [LpGridRepresentation.levelCoeffPower]
  have hroot := Real.rpow_le_rpow
    ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower_nonneg k)
    hpower_le (div_nonneg zero_le_one hp_pos.le)
  calc
    ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^
        (1 / p.toReal)
        ≤ (((smoothnessScaleLevelWeight G s sTilde p k) ^ p.toReal) * R.levelCoeffPower k) ^
            (1 / p.toReal) := hroot
    _ = ((smoothnessScaleLevelWeight G s sTilde p k) ^ p.toReal) ^ (1 / p.toReal) *
          (R.levelCoeffPower k) ^ (1 / p.toReal) := by
            rw [Real.mul_rpow]
            · exact Real.rpow_nonneg (smoothnessScaleLevelWeight_nonneg G s sTilde p k) _
            · exact R.levelCoeffPower_nonneg k
    _ = smoothnessScaleLevelWeight G s sTilde p k * (R.levelCoeffPower k) ^ (1 / p.toReal) := by
          simpa [one_div] using
            congrArg (fun x => x * (R.levelCoeffPower k) ^ (1 / p.toReal))
              (Real.rpow_rpow_inv (smoothnessScaleLevelWeight_nonneg G s sTilde p k) hp_pos.ne')

/--
Finiteness of the `pqCost` is preserved under the unscaling transformation.
-/
private theorem smoothnessScaleToBase_finitePQCost
  [Fact (1 ≤ p)]
  [Fact (1 ≤ q)] [Fact (1 ≤ qTilde)]
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    (hs_le : s ≤ sTilde)
    {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := qTilde) R)
    (hqfin : scaleCoefficientFinite q (smoothnessScaleLevelWeight G s sTilde p)) :
    LpGridRepresentation.FinitePQCost (q := q)
      (smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R) := by
  let C := LpGridRepresentation.pqCost (q := qTilde) R
  have hC_nonneg : 0 ≤ C := LpGridRepresentation.pqCost_nonneg R
  unfold LpGridRepresentation.FinitePQCost
  by_cases hq : q = ∞
  · simp only [hq, ↓reduceIte]
    simp only [scaleCoefficientFinite, hq, ↓reduceIte] at hqfin
    rcases hqfin with ⟨B, hB⟩
    refine ⟨B * C, ?_⟩
    rintro x ⟨k, rfl⟩
    calc
      ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^
          (1 / p.toReal)
          ≤ smoothnessScaleLevelWeight G s sTilde p k * C := by
              exact (smoothnessScaleToBase_levelCoeffRoot_le A sTilde hsTilde_pos hs_le R k).trans <|
                mul_le_mul_of_nonneg_left
                  (levelCoeffRoot_le_pqCost (A := A.smoothnessScaleAtomFamily sTilde hsTilde_pos)
                    R hRfin k)
                  (smoothnessScaleLevelWeight_nonneg G s sTilde p k)
      _ ≤ B * C := mul_le_mul_of_nonneg_right (hB ⟨k, rfl⟩) hC_nonneg
  · simp only [hq, ↓reduceIte]
    simp only [scaleCoefficientFinite, hq, ↓reduceIte] at hqfin
    refine Summable.of_nonneg_of_le
      (fun k => Real.rpow_nonneg
        ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower_nonneg k) _)
      ?_ (hqfin.mul_right (C ^ q.toReal))
    · intro k
      have hroot_le :
          ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^
              (1 / p.toReal)
            ≤ smoothnessScaleLevelWeight G s sTilde p k * C :=
        (smoothnessScaleToBase_levelCoeffRoot_le A sTilde hsTilde_pos hs_le R k).trans <|
          mul_le_mul_of_nonneg_left
            (levelCoeffRoot_le_pqCost (A := A.smoothnessScaleAtomFamily sTilde hsTilde_pos)
              R hRfin k)
            (smoothnessScaleLevelWeight_nonneg G s sTilde p k)
      calc
        ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^
            (q.toReal / p.toReal)
            = ((((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^
                (1 / p.toReal))) ^ q.toReal := by
                  rw [← Real.rpow_mul
                    ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower_nonneg k)]
                  congr 1
                  field_simp
        _ ≤ (smoothnessScaleLevelWeight G s sTilde p k * C) ^ q.toReal := by
              exact Real.rpow_le_rpow
                (Real.rpow_nonneg
                  ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower_nonneg k) _)
                hroot_le ENNReal.toReal_nonneg
        _ = (smoothnessScaleLevelWeight G s sTilde p k) ^ q.toReal * C ^ q.toReal := by
              rw [Real.mul_rpow (smoothnessScaleLevelWeight_nonneg G s sTilde p k) hC_nonneg]

/-- The scale coefficient is nonnegative whenever the weights are nonnegative. -/
private theorem scaleCoefficient_nonneg
    (q : ℝ≥0∞) (w : ℕ → ℝ) (hw_nonneg : ∀ k, 0 ≤ w k) :
    0 ≤ scaleCoefficient q w := by
  unfold scaleCoefficient
  by_cases hq : q = ∞
  · simp [hq]
    refine Real.sSup_nonneg ?_
    intro x hx
    rcases hx with ⟨k, rfl⟩
    exact hw_nonneg k
  · simp [hq]
    exact Real.rpow_nonneg (tsum_nonneg fun k => Real.rpow_nonneg (hw_nonneg k) _) _

/--
Quantitative `pqCost` estimate for the unscaled representation.

This is the main coefficient estimate behind the continuity of the inclusion.
-/
private theorem smoothnessScaleToBase_pqCost_le
  [Fact (1 ≤ p)]
  [Fact (1 ≤ q)] [Fact (1 ≤ qTilde)]
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    (hs_le : s ≤ sTilde)
    {g : Lp ℂ p G.measure}
    (R : LpGridRepresentation (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := qTilde) R)
    (hqfin : scaleCoefficientFinite q (smoothnessScaleLevelWeight G s sTilde p)) :
    LpGridRepresentation.pqCost (q := q)
      (smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R)
      ≤ scaleCoefficient q (smoothnessScaleLevelWeight G s sTilde p) *
          LpGridRepresentation.pqCost (q := qTilde) R := by
  let C := LpGridRepresentation.pqCost (q := qTilde) R
  have hC_nonneg : 0 ≤ C := LpGridRepresentation.pqCost_nonneg R
  have hqfin_full : scaleCoefficientFinite q (smoothnessScaleLevelWeight G s sTilde p) := hqfin
  by_cases hq : q = ∞
  · simp only [LpGridRepresentation.pqCost, ↓reduceIte, scaleCoefficient, hq]
    have hnewfin := smoothnessScaleToBase_finitePQCost A sTilde hsTilde_pos hs_le R hRfin hqfin
    simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hnewfin
    simp only [scaleCoefficientFinite, hq, ↓reduceIte] at hqfin
    refine csSup_le (Set.range_nonempty fun k =>
      ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^ (1 / p.toReal)) ?_
    rintro x ⟨k, rfl⟩
    calc
      ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^ (1 / p.toReal)
          ≤ smoothnessScaleLevelWeight G s sTilde p k * C := by
              exact (smoothnessScaleToBase_levelCoeffRoot_le A sTilde hsTilde_pos hs_le R k).trans <|
                mul_le_mul_of_nonneg_left
                  (levelCoeffRoot_le_pqCost (A := A.smoothnessScaleAtomFamily sTilde hsTilde_pos)
                    R hRfin k)
                  (smoothnessScaleLevelWeight_nonneg G s sTilde p k)
      _ ≤ sSup (Set.range (smoothnessScaleLevelWeight G s sTilde p)) * C := by
            exact mul_le_mul_of_nonneg_right
              (le_csSup hqfin ⟨k, rfl⟩) hC_nonneg
  · simp only [LpGridRepresentation.pqCost, ↓reduceIte, scaleCoefficient, hq]
    simp only [scaleCoefficientFinite, hq, ↓reduceIte] at hqfin
    have hnewfin := smoothnessScaleToBase_finitePQCost A sTilde hsTilde_pos hs_le R hRfin hqfin_full
    simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hnewfin
    have hsum_le :
        ∑' k,
          ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^
            (q.toReal / p.toReal)
          ≤ ∑' k, (smoothnessScaleLevelWeight G s sTilde p k) ^ q.toReal * C ^ q.toReal := by
      refine hnewfin.tsum_le_tsum ?_ (hqfin.mul_right (C ^ q.toReal))
      intro k
      have hroot_le :
          ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^
              (1 / p.toReal)
            ≤ smoothnessScaleLevelWeight G s sTilde p k * C :=
        (smoothnessScaleToBase_levelCoeffRoot_le A sTilde hsTilde_pos hs_le R k).trans <|
          mul_le_mul_of_nonneg_left
            (levelCoeffRoot_le_pqCost (A := A.smoothnessScaleAtomFamily sTilde hsTilde_pos)
              R hRfin k)
            (smoothnessScaleLevelWeight_nonneg G s sTilde p k)
      calc
        ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^
            (q.toReal / p.toReal)
            = ((((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^
                (1 / p.toReal))) ^ q.toReal := by
                  rw [← Real.rpow_mul
                    ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower_nonneg k)]
                  congr 1
                  field_simp
        _ ≤ (smoothnessScaleLevelWeight G s sTilde p k * C) ^ q.toReal := by
              exact Real.rpow_le_rpow
                (Real.rpow_nonneg
                  ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower_nonneg k) _)
                hroot_le ENNReal.toReal_nonneg
        _ = (smoothnessScaleLevelWeight G s sTilde p k) ^ q.toReal * C ^ q.toReal := by
              rw [Real.mul_rpow (smoothnessScaleLevelWeight_nonneg G s sTilde p k) hC_nonneg]
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have hroot := Real.rpow_le_rpow
      (tsum_nonneg fun k =>
        Real.rpow_nonneg
          ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower_nonneg k) _)
      hsum_le (div_nonneg zero_le_one hq_pos.le)
    calc
      (∑' k,
          ((smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R).levelCoeffPower k) ^
            (q.toReal / p.toReal)) ^ (1 / q.toReal)
          ≤ (∑' k, (smoothnessScaleLevelWeight G s sTilde p k) ^ q.toReal * C ^ q.toReal) ^
              (1 / q.toReal) := hroot
      _ = ((∑' k, (smoothnessScaleLevelWeight G s sTilde p k) ^ q.toReal) * C ^ q.toReal) ^
            (1 / q.toReal) := by rw [tsum_mul_right]
      _ = (∑' k, (smoothnessScaleLevelWeight G s sTilde p k) ^ q.toReal) ^ (1 / q.toReal) * C := by
            rw [Real.mul_rpow]
            · simpa [one_div] using
                congrArg
                  (fun x => (∑' k, (smoothnessScaleLevelWeight G s sTilde p k) ^ q.toReal) ^
                    (1 / q.toReal) * x)
                  (Real.rpow_rpow_inv hC_nonneg hq_pos.ne')
            · exact tsum_nonneg fun k =>
                Real.rpow_nonneg (smoothnessScaleLevelWeight_nonneg G s sTilde p k) _
            · exact Real.rpow_nonneg hC_nonneg _

/--
Set-theoretic inclusion from the scaled Besov-ish space into the original one.

The hypothesis `hqfin` is the only summability or boundedness assumption needed
on the deterministic scale weights.
-/
theorem smoothnessScaleBesovishSpace_subset
  [Fact (1 ≤ p)]
  [Fact (1 ≤ u)] [Fact (1 ≤ q)] [Fact (1 ≤ qTilde)]
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    (hs_le : s ≤ sTilde)
    (hqfin : scaleCoefficientFinite q (smoothnessScaleLevelWeight G s sTilde p))
    {g : Lp ℂ p G.measure}
    (hg : g ∈ SmoothnessScaleBesovishSpace
      (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) qTilde) :
    g ∈ BesovishSpace A q := by
  rcases hg with ⟨R, hRfin⟩
  exact ⟨smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R,
    smoothnessScaleToBase_finitePQCost A sTilde hsTilde_pos hs_le R hRfin hqfin⟩

/--
Linear inclusion from the smoothness-scaled Besov-ish space into the original
Besov-ish space.
-/
noncomputable def smoothnessScaleBesovishSpaceInclusion
  [Fact (1 ≤ p)]
    [Fact (1 ≤ u)] [Fact (1 ≤ q)] [Fact (1 ≤ qTilde)]
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    (hs_le : s ≤ sTilde)
    (hqfin : scaleCoefficientFinite q (smoothnessScaleLevelWeight G s sTilde p)) :
    SmoothnessScaleBesovishSpace (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) qTilde →ₗ[ℂ]
      BesovishSpace A q where
  toFun g := ⟨g.1, smoothnessScaleBesovishSpace_subset A sTilde hsTilde_pos hs_le hqfin g.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
Explicit continuity bound for the inclusion map in the `Norm_Costpq` gauge.

This turns the `pqCost` estimate on representations into a bound on the norm of
the induced element in the target Besov-ish space.
-/
theorem smoothnessScaleBesovishSpaceInclusion_Norm_Costpq_le
  [Fact (1 ≤ p)]
  [Fact (1 ≤ u)] [Fact (1 ≤ q)] [Fact (1 ≤ qTilde)]
    (A : AtomFamily G s p u) (sTilde : ℝ) (hsTilde_pos : 0 < sTilde)
    (hs_le : s ≤ sTilde)
    (hqfin : scaleCoefficientFinite q (smoothnessScaleLevelWeight G s sTilde p))
    (g : SmoothnessScaleBesovishSpace (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) qTilde) :
    BesovishSpace.Norm_Costpq A q
        (smoothnessScaleBesovishSpaceInclusion A sTilde hsTilde_pos hs_le hqfin g)
      ≤ scaleCoefficient q (smoothnessScaleLevelWeight G s sTilde p) *
          BesovishSpace.Norm_Costpq (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) qTilde g := by
  let C := scaleCoefficient q (smoothnessScaleLevelWeight G s sTilde p)
  have hC_nonneg : 0 ≤ C :=
    scaleCoefficient_nonneg q (smoothnessScaleLevelWeight G s sTilde p)
      (smoothnessScaleLevelWeight_nonneg G s sTilde p)
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hεC : 0 < ε / (C + 1) := by
    have : 0 < C + 1 := by linarith
    positivity
  rcases BesovishSpace.exists_cost_lt_Norm_Costpq_add
      (A := A.smoothnessScaleAtomFamily sTilde hsTilde_pos) (q := qTilde)
      (BesovishSpace.hasFiniteCostRepresentations
        (A := A.smoothnessScaleAtomFamily sTilde hsTilde_pos) qTilde)
      g hεC with ⟨R, hRfin, hRlt⟩
  have hnewfin :
      LpGridRepresentation.FinitePQCost (q := q)
        (smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R) :=
    smoothnessScaleToBase_finitePQCost A sTilde hsTilde_pos hs_le R hRfin hqfin
  have hNorm_le :
      BesovishSpace.Norm_Costpq A q
          (smoothnessScaleBesovishSpaceInclusion A sTilde hsTilde_pos hs_le hqfin g)
        ≤ LpGridRepresentation.pqCost (q := q)
            (smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R) := by
    exact BesovishSpace.Norm_Costpq_le_cost
      (g := smoothnessScaleBesovishSpaceInclusion A sTilde hsTilde_pos hs_le hqfin g)
      (smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R) hnewfin
  have hcost_le :
      LpGridRepresentation.pqCost (q := q)
          (smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R)
        ≤ C * LpGridRepresentation.pqCost (q := qTilde) R := by
    simpa [C] using
      smoothnessScaleToBase_pqCost_le A sTilde hsTilde_pos hs_le R hRfin hqfin
  have hRle :
      LpGridRepresentation.pqCost (q := qTilde) R
        ≤ BesovishSpace.Norm_Costpq (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) qTilde g +
            ε / (C + 1) := le_of_lt hRlt
  have hmul :
      C * LpGridRepresentation.pqCost (q := qTilde) R ≤
        C * (BesovishSpace.Norm_Costpq (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) qTilde g +
          ε / (C + 1)) :=
    mul_le_mul_of_nonneg_left hRle hC_nonneg
  have hsmall : C * (ε / (C + 1)) ≤ ε := by
    have hfrac : C / (C + 1) ≤ (1 : ℝ) := by
      have hden : 0 < C + 1 := by linarith
      exact (div_le_one hden).2 (by linarith)
    have hεnn : 0 ≤ ε := le_of_lt hε
    have hmul' : (C / (C + 1)) * ε ≤ (1 : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hfrac hεnn
    calc
      C * (ε / (C + 1)) = (C / (C + 1)) * ε := by ring
      _ ≤ (1 : ℝ) * ε := hmul'
      _ = ε := by ring
  calc
    BesovishSpace.Norm_Costpq A q
        (smoothnessScaleBesovishSpaceInclusion A sTilde hsTilde_pos hs_le hqfin g)
      ≤ LpGridRepresentation.pqCost (q := q)
          (smoothnessScaleToBaseRepresentation A sTilde hsTilde_pos R) := hNorm_le
    _ ≤ C * LpGridRepresentation.pqCost (q := qTilde) R := hcost_le
    _ ≤ C *
        (BesovishSpace.Norm_Costpq (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) qTilde g +
          ε / (C + 1)) := hmul
    _ = C * BesovishSpace.Norm_Costpq (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) qTilde g +
          C * (ε / (C + 1)) := by ring
    _ ≤ C * BesovishSpace.Norm_Costpq (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) qTilde g + ε := by
          have hsmall' := add_le_add_left hsmall
            (C * BesovishSpace.Norm_Costpq (A.smoothnessScaleAtomFamily sTilde hsTilde_pos) qTilde g)
          simpa [add_comm, add_left_comm, add_assoc] using hsmall'

end SmoothnessScaleBesovishSpaces

end AtomFamily

end

end WeakGridSpace
