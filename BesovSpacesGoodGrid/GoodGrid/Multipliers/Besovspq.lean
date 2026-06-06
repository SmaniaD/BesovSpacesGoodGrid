import BesovSpacesGoodGrid.GoodGrid.Multipliers.Definition
import BesovSpacesGoodGrid.WeakGrid.Transmutation

/-!
# Souza pointwise multipliers for general p and q

This file proves the general multiplier results for Souza Besov spaces on good
grids, including the cell-indicator theorem for every `q >= 1`, with the
endpoint `q = ∞` handled by a separate branch of the proof.
-/

open scoped ENNReal Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
Good-grid cells at comparable levels are nested or disjoint: if `W` is no
finer than `Q`, then either `Q` lies inside `W` or the two cells are disjoint.
-/
theorem GoodGridCell.subset_or_disjoint_of_le
    {G : GoodGridSpace (α := α)} (W Q : GoodGridCell G)
    (hlevel : W.level ≤ Q.level) :
    Q.cell ⊆ W.cell ∨ Disjoint Q.cell W.cell := by
  exact G.grid.partition_subset_or_disjoint_of_le W.level Q.level hlevel
    W.cell W.mem Q.cell Q.mem

/--
The root cell of the grid induced on a good-grid cell `W`.
-/
def GoodGridCell.inducedRootLevelCell
    {G : GoodGridSpace (α := α)} (W : GoodGridCell G) :
    WeakGridSpace.LevelCell
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell) 0 :=
  ⟨W.cell, by
    simpa [WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid] using
      (WeakGridSpace.mem_inducedPartitions_iff
        G.toWeakGridSpace W.toLevelCell (P := W.cell) (i := 0)).mpr
        ⟨by simpa using W.mem, subset_rfl⟩⟩

/--
A descendant good-grid cell `Q ⊆ W`, viewed as a level cell of the grid
induced on `W`.
-/
def GoodGridCell.toInducedLevelCellOfSubset
    {G : GoodGridSpace (α := α)} (W Q : GoodGridCell G)
    (hlevel : W.level ≤ Q.level) (hsub : Q.cell ⊆ W.cell) :
    WeakGridSpace.LevelCell
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
      (Q.level - W.level) := by
  let P : WeakGridSpace.LevelCell G.toWeakGridSpace
      (W.level + (Q.level - W.level)) :=
    ⟨Q.cell, by simpa [Nat.add_sub_of_le hlevel] using Q.mem⟩
  exact WeakGridSpace.ambientLevelCellToInduced G.toWeakGridSpace W.toLevelCell P hsub

/-- The induced level naturally attached to an ambient level after restricting to `W`. -/
def GoodGridCell.restrictionLevel
    {G : GoodGridSpace (α := α)} (W : GoodGridCell G) (i : ℕ) : ℕ :=
  i - W.level

/--
The level map `i ↦ i - W.level` is almost linear with slope `1`.

This is the level bookkeeping used for the one-block representations of
restricted Souza atoms.
-/
theorem GoodGridCell.restrictionLevel_bound
    {G : GoodGridSpace (α := α)} (W : GoodGridCell G) :
    ∀ i : ℕ,
      ((W.restrictionLevel i : ℕ) : NNReal) ≤
          (1 : ℝ) * (i : NNReal) + 0 ∧
        (1 : ℝ) * (i : NNReal) + (-(W.level : ℝ)) ≤
          ((W.restrictionLevel i : ℕ) : NNReal) := by
  intro i
  constructor
  · unfold GoodGridCell.restrictionLevel
    simpa using
      (show (((i - W.level : ℕ) : NNReal) : ℝ) ≤ (i : ℝ) by
        exact_mod_cast Nat.sub_le i W.level)
  · unfold GoodGridCell.restrictionLevel
    suffices (i : ℝ) + (-(W.level : ℝ)) ≤ (((i - W.level : ℕ) : NNReal) : ℝ) by
      simpa using this
    by_cases hWi : W.level ≤ i
    · have hcast : (((i - W.level : ℕ) : NNReal) : ℝ) = (i : ℝ) - W.level := by
        exact_mod_cast Nat.cast_sub hWi
      rw [hcast]
      exact le_rfl
    · have hiW : i < W.level := Nat.lt_of_not_ge hWi
      have hsub : i - W.level = 0 := Nat.sub_eq_zero_of_le hiW.le
      have hcast : (((i - W.level : ℕ) : NNReal) : ℝ) = 0 := by
        simp [hsub]
      have hle : (i : ℝ) - W.level ≤ 0 := by
        have hle_nat : i ≤ W.level := Nat.le_of_lt hiW
        have hle_real : (i : ℝ) ≤ W.level := by exact_mod_cast hle_nat
        linarith
      rw [hcast]
      linarith

/-- The level map `i ↦ i - W.level` is almost linear. -/
theorem GoodGridCell.restrictionLevel_almostLinear
    {G : GoodGridSpace (α := α)} (W : GoodGridCell G) :
    WeakGridSpace.AlmostLinearSequence W.restrictionLevel :=
  ⟨-(W.level : ℝ), 0, 1, by norm_num, W.restrictionLevel_bound⟩

/-- Real powers are antitone in the base when the exponent is non-positive. -/
private theorem rpow_le_rpow_of_nonpos_exponent
    {x y e : ℝ} (hx : 0 < x) (hxy : x ≤ y) (he : e ≤ 0) :
    y ^ e ≤ x ^ e := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hne_nonneg : 0 ≤ -e := by linarith
  have hpow : x ^ (-e) ≤ y ^ (-e) :=
    Real.rpow_le_rpow hx.le hxy hne_nonneg
  have hxpow : 0 < x ^ (-e) := Real.rpow_pos_of_pos hx _
  calc
    y ^ e = (y ^ (-e))⁻¹ := by
      simpa using Real.rpow_neg hy.le (-e)
    _ ≤ (x ^ (-e))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hxpow hpow
    _ = x ^ e := by
      simpa using (Real.rpow_neg hx.le (-e)).symm

/--
The normalized coefficient produced when restricting an ancestor atom to a
descendant cell has geometric decay.

If `W ⊆ Q` and `s < 1 / p`, then a Souza atom coefficient on `Q`, normalized
by the Souza scale of `W`, is bounded by
`lambda2^((level W - level Q) * (1 / p - s))`.  This is the local estimate
which replaces the older bookkeeping where ancestor restrictions were put on
the root induced cell with coefficient `1`.
-/
theorem souzaAncestorAtom_normalizedCoeff_le_geometric
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {W Q : GoodGridCell G}
    (hlevel : Q.level ≤ W.level)
    (hsub : W.cell ⊆ Q.cell)
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (c : ℂ)
    (hc : (souzaAtomFamily G s p hs hp hp_top).IsAtom Q.toWeakGridCell c) :
    ‖c / (((G.grid.μ W.cell).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)‖ ≤
      (G.grid.lambda2 ^ (W.level - Q.level) : ℝ) ^ ((p.toReal)⁻¹ - s) := by
  classical
  let β : ℝ := (p.toReal)⁻¹ - s
  let μW : ℝ := (G.grid.μ W.cell).toReal
  let μQ : ℝ := (G.grid.μ Q.cell).toReal
  let geom : ℝ := (G.grid.lambda2 ^ (W.level - Q.level) : ℝ) ^ β
  have hβ_pos : 0 < β := by
    dsimp [β]
    linarith
  have hW_pos_en : 0 < G.grid.μ W.cell :=
    G.grid.positive_measure W.level W.cell W.mem
  have hQ_pos_en : 0 < G.grid.μ Q.cell :=
    G.grid.positive_measure Q.level Q.cell Q.mem
  have hW_ne_top : G.grid.μ W.cell ≠ ∞ := by
    letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ W.cell
  have hQ_ne_top : G.grid.μ Q.cell ≠ ∞ := by
    letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ Q.cell
  have hμW_pos : 0 < μW :=
    ENNReal.toReal_pos hW_pos_en.ne' hW_ne_top
  have hμQ_pos : 0 < μQ :=
    ENNReal.toReal_pos hQ_pos_en.ne' hQ_ne_top
  have hμW_nonneg : 0 ≤ μW := hμW_pos.le
  have hμQ_nonneg : 0 ≤ μQ := hμQ_pos.le
  have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
    le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hgeom_nonneg : 0 ≤ geom := by
    dsimp [geom]
    exact Real.rpow_nonneg (pow_nonneg hlam_nonneg _) _
  have hW_level :
      W.level = Q.level + (W.level - Q.level) := by
    exact (Nat.add_sub_of_le hlevel).symm
  have hW_mem_shift :
      W.cell ∈ G.grid.grid.partitions (Q.level + (W.level - Q.level)) := by
    simpa [← hW_level] using W.mem
  have hmeasure_en :
      G.grid.μ W.cell ≤
        (ENNReal.ofReal G.grid.lambda2) ^ (W.level - Q.level) * G.grid.μ Q.cell :=
    cell_measure_le_lambda2_pow_mul_cell G Q (W.level - Q.level) W.cell
      hW_mem_shift hsub
  have hright_ne_top :
      (ENNReal.ofReal G.grid.lambda2) ^ (W.level - Q.level) * G.grid.μ Q.cell ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hQ_ne_top
  have hmeasure_real :
      μW ≤ G.grid.lambda2 ^ (W.level - Q.level) * μQ := by
    have htoReal := ENNReal.toReal_mono hright_ne_top hmeasure_en
    simpa [μW, μQ, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlam_nonneg] using htoReal
  have hmeasure_pow :
      μW ^ β ≤ (G.grid.lambda2 ^ (W.level - Q.level) * μQ) ^ β :=
    Real.rpow_le_rpow hμW_nonneg hmeasure_real hβ_pos.le
  have hsplit :
      (G.grid.lambda2 ^ (W.level - Q.level) * μQ) ^ β =
        geom * μQ ^ β := by
    rw [Real.mul_rpow (pow_nonneg hlam_nonneg _) hμQ_nonneg]
  have hμWβ_le : μW ^ β ≤ geom * μQ ^ β := by
    simpa [hsplit] using hmeasure_pow
  have hc_bound :
      ‖c‖ ≤ μQ ^ (s - (p.toReal)⁻¹) := by
    simpa [souzaAtomFamily, souzaAtomsSet, GoodGridCell.toWeakGridCell,
      WeakGridSpace.AtomFamily.IsAtom, μQ] using hc
  have hQ_neg :
      μQ ^ (s - (p.toReal)⁻¹) = (μQ ^ β)⁻¹ := by
    have h : s - (p.toReal)⁻¹ = -β := by
      dsimp [β]
      ring
    rw [h]
    simpa [one_div] using Real.rpow_neg hμQ_nonneg β
  have hW_neg :
      μW ^ (s - (p.toReal)⁻¹) = (μW ^ β)⁻¹ := by
    have h : s - (p.toReal)⁻¹ = -β := by
      dsimp [β]
      ring
    rw [h]
    simpa [one_div] using Real.rpow_neg hμW_nonneg β
  have hμQβ_pos : 0 < μQ ^ β := Real.rpow_pos_of_pos hμQ_pos β
  have hμWβ_pos : 0 < μW ^ β := Real.rpow_pos_of_pos hμW_pos β
  have hscale_bound :
      μQ ^ (s - (p.toReal)⁻¹) ≤
        μW ^ (s - (p.toReal)⁻¹) * geom := by
    rw [hQ_neg, hW_neg]
    have hdiv :
        (μQ ^ β)⁻¹ ≤ geom * (μW ^ β)⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ hμWβ_pos).2
      have hratio : μW ^ β / μQ ^ β ≤ geom := by
        rw [div_le_iff₀ hμQβ_pos]
        simpa [mul_comm] using hμWβ_le
      simpa [div_eq_mul_inv, mul_comm] using hratio
    simpa [mul_comm] using hdiv
  have hnorm_le :
      ‖c‖ ≤ μW ^ (s - (p.toReal)⁻¹) * geom :=
    hc_bound.trans hscale_bound
  have hμW_scale_pos : 0 < μW ^ (s - (p.toReal)⁻¹) :=
    Real.rpow_pos_of_pos hμW_pos _
  calc
    ‖c / (((G.grid.μ W.cell).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)‖
        = ‖c‖ / μW ^ (s - (p.toReal)⁻¹) := by
            rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hμW_scale_pos.le]
    _ ≤ geom := by
          rw [div_le_iff₀ hμW_scale_pos]
          simpa [mul_comm] using hnorm_le
    _ = (G.grid.lambda2 ^ (W.level - Q.level) : ℝ) ^ ((p.toReal)⁻¹ - s) := by
          rfl

/-- If `Q ⊆ W`, restricting a constant indicator on `Q` to `W` leaves it unchanged. -/
private theorem ambient_indicator_mul_cellIndicator_eq_self_of_subset
    {G : GoodGridSpace (α := α)} (W Q : GoodGridCell G)
    (c : ℂ) (hsub : Q.cell ⊆ W.cell) :
    (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
      Q.cell.indicator (fun _ => c) x) =
      Q.cell.indicator (fun _ => c) := by
  classical
  funext x
  by_cases hxQ : x ∈ Q.cell
  · have hxW : x ∈ W.cell := hsub hxQ
    simp [hxW, hxQ]
  · simp [hxQ]

/-- If two cells are disjoint, restricting a constant indicator gives zero. -/
private theorem ambient_indicator_mul_cellIndicator_eq_zero_of_disjoint
    {G : GoodGridSpace (α := α)} (W Q : GoodGridCell G)
    (c : ℂ) (hdisj : Disjoint Q.cell W.cell) :
    (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
      Q.cell.indicator (fun _ => c) x) = fun _ => 0 := by
  classical
  funext x
  by_cases hxW : x ∈ W.cell
  · have hxQ : x ∉ Q.cell := by
      intro hxQ
      exact (Set.disjoint_left.mp hdisj hxQ hxW).elim
    simp [hxW, hxQ]
  · simp [hxW]

/-- If `W ⊆ Q`, restricting a constant indicator on `Q` gives the indicator of `W`. -/
private theorem ambient_indicator_mul_cellIndicator_eq_indicator_of_superset
    {G : GoodGridSpace (α := α)} (W Q : GoodGridCell G)
    (c : ℂ) (hsub : W.cell ⊆ Q.cell) :
    (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
      Q.cell.indicator (fun _ => c) x) =
      W.cell.indicator (fun _ => c) := by
  classical
  funext x
  by_cases hxW : x ∈ W.cell
  · have hxQ : x ∈ Q.cell := hsub hxW
    simp [hxW, hxQ]
  · simp [hxW]

/--
Ambient one-atom restriction with the original level bookkeeping.

The restricted atom is represented in the original Souza grid, not directly in
the induced grid.  Descendant cells `Q ⊆ W` stay on their original level with
coefficient power `1`; ancestor cells `W ⊆ Q` are represented on the level of
`W`, with the normalized coefficient controlled by the strict gap
`s < 1 / p`.
-/
theorem restrict_souzaAtomFamily_toFunction_ambientSupportedOneBlockRepresentation
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) {i : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i)
    (c : ℂ)
    (hc : (souzaAtomFamily G s p hs hp hp_top).IsAtom
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) c) :
    ∃ y : Lp ℂ p G.toWeakGridSpace.measure,
    ∃ R : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top) y,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
          (souzaAtomFamily G s p hs hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) c x)
        y ∧
      (∀ n, n < W.level →
        (R.block n).toLp (souzaAtomFamily G s p hs hp hp_top) = 0) ∧
      (∀ n (P : WeakGridSpace.LevelCell G.toWeakGridSpace n),
        ¬ P.1 ⊆ W.cell → (R.block n).coeff P = 0) ∧
      (∀ n (P : WeakGridSpace.LevelCell G.toWeakGridSpace n),
        ¬ P.1 ⊆ Q.1 → (R.block n).coeff P = 0) ∧
      ∀ n : ℕ, R.levelCoeffPower n ≤
        if W.level ≤ i then
          if n = i then 1 else 0
        else
          if n = W.level then
            ((G.grid.lambda2 ^ (W.level - i) : ℝ) ^ ((p.toReal)⁻¹ - s)) ^ p.toReal
          else 0 := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Qg : GoodGridCell G := ⟨i, Q.1, Q.2⟩
  have hcQg : A.IsAtom Qg.toWeakGridCell c := by
    simpa [A, Qg, GoodGridCell.toWeakGridCell] using hc
  by_cases hWi : W.level ≤ i
  · rcases W.subset_or_disjoint_of_le Qg hWi with hsub | hdisj
    · have hAtom : A.IsAtom Qg.toWeakGridCell c := hcQg
      let B : WeakGridSpace.LevelBlock A i :=
        WeakGridSpace.LevelBlock.singleAtom A Q (1 : ℂ) c (by
          simpa [A, Qg, GoodGridCell.toWeakGridCell] using hAtom)
      let y : Lp ℂ p G.toWeakGridSpace.measure := B.toLp A
      let R : WeakGridSpace.LpGridRepresentation A y :=
        WeakGridSpace.LpGridRepresentation.singleBlockRepresentation (G := G.toWeakGridSpace)
          (A := A) B
      refine ⟨y, R, ?_, ?_, ?_, ?_, ?_⟩
      · have hB := WeakGridSpace.LevelBlock.singleAtom_ae_eq A Q (1 : ℂ) c
          (by simpa [A, Qg, GoodGridCell.toWeakGridCell] using hAtom)
        refine hB.trans (Filter.Eventually.of_forall ?_)
        intro x
        have hprod :=
          congrFun (ambient_indicator_mul_cellIndicator_eq_self_of_subset W Qg c hsub) x
        simpa [A, Qg, B, WeakGridSpace.AtomFamily.toFunction,
          GoodGridCell.toWeakGridCell, souzaAtomFamily, souzaLocalVectorSpace,
          WeakGridSpace.levelCellToWeakGridCell, one_mul] using hprod.symm
      · intro n hn
        have hni : n ≠ i := by
          intro hni
          subst n
          exact Nat.not_lt_of_ge hWi hn
        simpa [R, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation, hni, A] using
          (WeakGridSpace.LevelBlock.zero_toLp A n)
      · intro n P hnot
        by_cases hn : n = i
        · subst n
          by_cases hPQ : P = Q
          · subst P
            exfalso
            exact hnot hsub
          · simp [R, B, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation,
              WeakGridSpace.LevelBlock.singleAtom, hPQ]
        · simp [R, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation, hn,
            WeakGridSpace.LevelBlock.zero]
      · intro n P hnot
        by_cases hn : n = i
        · subst n
          by_cases hPQ : P = Q
          · subst P
            exact (hnot subset_rfl).elim
          · simp [R, B, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation,
              WeakGridSpace.LevelBlock.singleAtom, hPQ]
        · simp [R, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation, hn,
            WeakGridSpace.LevelBlock.zero]
      · intro n
        have hlevel :=
          WeakGridSpace.LevelBlock.singleAtom_singleBlock_levelCoeffPower
            A Q (1 : ℂ) c (by simpa [A, Qg, GoodGridCell.toWeakGridCell] using hAtom) n
        rw [hlevel]
        simp [hWi]
    · refine ⟨0, WeakGridSpace.LpGridRepresentation.zero A, ?_, ?_, ?_, ?_, ?_⟩
      · have hprod := ambient_indicator_mul_cellIndicator_eq_zero_of_disjoint W Qg c hdisj
        have htarget :
            (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) c x) =
              fun _ => 0 := by
          simpa [A, Qg, WeakGridSpace.AtomFamily.toFunction,
            GoodGridCell.toWeakGridCell, souzaAtomFamily, souzaLocalVectorSpace,
            WeakGridSpace.levelCellToWeakGridCell] using hprod
        rw [WeakGridSpace.RepresentsFunction, htarget]
        exact MeasureTheory.Lp.coeFn_zero ℂ p G.toWeakGridSpace.measure
      · intro n hn
        simpa [WeakGridSpace.LpGridRepresentation.zero, A] using
          (WeakGridSpace.LevelBlock.zero_toLp A n)
      · intro n P hnot
        simp [WeakGridSpace.LpGridRepresentation.zero, WeakGridSpace.LevelBlock.zero]
      · intro n P hnot
        simp [WeakGridSpace.LpGridRepresentation.zero, WeakGridSpace.LevelBlock.zero]
      · intro n
        rw [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower]
        by_cases hn : n = i <;> simp [hWi, hn]
  · have hiW : i < W.level := Nat.lt_of_not_ge hWi
    rcases Qg.subset_or_disjoint_of_le W hiW.le with hsub | hdisj
    · let rW : ℝ := (G.grid.μ W.cell).toReal ^ (s - (p.toReal)⁻¹)
      have hrW_pos : 0 < rW := by
        have hμW_pos : 0 < (G.grid.μ W.cell).toReal :=
          ENNReal.toReal_pos (GoodGridCell.measure_pos W).ne' (GoodGridCell.measure_ne_top W)
        exact Real.rpow_pos_of_pos hμW_pos _
      let φW : (A.localSpace W.toWeakGridCell).carrier := ((rW : ℝ) : ℂ)
      have hφW : A.IsAtom W.toWeakGridCell φW := by
        change ‖(((rW : ℝ) : ℂ))‖ ≤
          (G.grid.μ W.cell).toReal ^ (s - (p.toReal)⁻¹)
        rw [Complex.norm_real, Real.norm_of_nonneg hrW_pos.le]
      let B : WeakGridSpace.LevelBlock A W.level :=
        WeakGridSpace.LevelBlock.singleAtom A W.toLevelCell (c / (rW : ℂ)) φW hφW
      let y : Lp ℂ p G.toWeakGridSpace.measure := B.toLp A
      let R : WeakGridSpace.LpGridRepresentation A y :=
        WeakGridSpace.LpGridRepresentation.singleBlockRepresentation (G := G.toWeakGridSpace)
          (A := A) B
      refine ⟨y, R, ?_, ?_, ?_, ?_, ?_⟩
      · have hB := WeakGridSpace.LevelBlock.singleAtom_ae_eq A W.toLevelCell
          (c / (rW : ℂ)) φW hφW
        refine hB.trans (Filter.Eventually.of_forall ?_)
        intro x
        have hprod :=
          congrFun (ambient_indicator_mul_cellIndicator_eq_indicator_of_superset W Qg c hsub) x
        have hsource :
            A.toFunction
                (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) c x =
              Qg.cell.indicator (fun _ => c) x := by
          simp [A, Qg, WeakGridSpace.AtomFamily.toFunction,
            souzaAtomFamily, souzaLocalVectorSpace,
            WeakGridSpace.levelCellToWeakGridCell]
          rfl
        change c / (rW : ℂ) *
            A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace W.level W.toLevelCell)
              φW x =
            W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction
                (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) c x
        rw [hsource]
        rw [hprod]
        by_cases hxW : x ∈ W.cell
        · simp only [A, φW, WeakGridSpace.AtomFamily.toFunction,
            GoodGridCell.toWeakGridCell, souzaAtomFamily, souzaLocalVectorSpace,
            WeakGridSpace.levelCellToWeakGridCell]
          change c / (rW : ℂ) * (W.cell.indicator (fun _ => (rW : ℂ)) x) =
            W.cell.indicator (fun _ => c) x
          rw [Set.indicator_of_mem hxW, Set.indicator_of_mem hxW]
          field_simp [show (rW : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt hrW_pos)]
        · simp only [A, φW, WeakGridSpace.AtomFamily.toFunction,
            GoodGridCell.toWeakGridCell, souzaAtomFamily, souzaLocalVectorSpace,
            WeakGridSpace.levelCellToWeakGridCell]
          change c / (rW : ℂ) * (W.cell.indicator (fun _ => (rW : ℂ)) x) =
            W.cell.indicator (fun _ => c) x
          rw [Set.indicator_of_notMem hxW, Set.indicator_of_notMem hxW]
          simp
      · intro n hn
        have hnW : n ≠ W.level := by
          intro hnW
          subst n
          exact Nat.lt_irrefl _ hn
        simpa [R, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation, hnW, A] using
          (WeakGridSpace.LevelBlock.zero_toLp A n)
      · intro n P hnot
        by_cases hn : n = W.level
        · subst n
          by_cases hPW : P = W.toLevelCell
          · subst P
            exfalso
            exact hnot subset_rfl
          · simp [R, B, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation,
              WeakGridSpace.LevelBlock.singleAtom, hPW]
        · simp [R, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation, hn,
            WeakGridSpace.LevelBlock.zero]
      · intro n P hnot
        by_cases hn : n = W.level
        · subst n
          by_cases hPW : P = W.toLevelCell
          · subst P
            exact (hnot hsub).elim
          · simp [R, B, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation,
              WeakGridSpace.LevelBlock.singleAtom, hPW]
        · simp [R, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation, hn,
            WeakGridSpace.LevelBlock.zero]
      · intro n
        have hlevel :=
          WeakGridSpace.LevelBlock.singleAtom_singleBlock_levelCoeffPower
            A W.toLevelCell (c / (rW : ℂ)) φW hφW n
        rw [hlevel]
        by_cases hn : n = W.level
        · subst n
          have hcoeff :=
            souzaAncestorAtom_normalizedCoeff_le_geometric
              G s p hs hp hp_top hiW.le hsub hs_lt_inv c hcQg
          have hp_pos : 0 < p.toReal :=
            ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
          have hpow := Real.rpow_le_rpow (norm_nonneg _) hcoeff hp_pos.le
          simpa [hWi, rW] using hpow
        · have hp_pos : 0 < p.toReal :=
            ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
          simp [hWi, hn]
    · refine ⟨0, WeakGridSpace.LpGridRepresentation.zero A, ?_, ?_, ?_, ?_, ?_⟩
      · have hprod := ambient_indicator_mul_cellIndicator_eq_zero_of_disjoint W Qg c hdisj.symm
        have htarget :
            (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) c x) =
              fun _ => 0 := by
          simpa [A, Qg, WeakGridSpace.AtomFamily.toFunction,
            GoodGridCell.toWeakGridCell, souzaAtomFamily, souzaLocalVectorSpace,
            WeakGridSpace.levelCellToWeakGridCell] using hprod
        rw [WeakGridSpace.RepresentsFunction, htarget]
        exact MeasureTheory.Lp.coeFn_zero ℂ p G.toWeakGridSpace.measure
      · intro n hn
        simpa [WeakGridSpace.LpGridRepresentation.zero, A] using
          (WeakGridSpace.LevelBlock.zero_toLp A n)
      · intro n P hnot
        simp [WeakGridSpace.LpGridRepresentation.zero, WeakGridSpace.LevelBlock.zero]
      · intro n P hnot
        simp [WeakGridSpace.LpGridRepresentation.zero, WeakGridSpace.LevelBlock.zero]
      · intro n
        rw [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower]
        by_cases hn : n = W.level
        · subst n
          simp [hWi]
          exact Real.rpow_nonneg
            (Real.rpow_nonneg (pow_nonneg
              (le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2) _) _) _
        · simp [hWi, hn]

/--
If `W ⊆ Q` and `s ≤ 1 / p`, then every Souza atom constant on `Q` is also an
atom on the root cell of the grid induced on `W`.
-/
theorem souzaAtom_mem_inducedRoot_of_subset
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {W Q : GoodGridCell G}
    (hs_le_inv : s ≤ (p.toReal)⁻¹)
    (hsub : W.cell ⊆ Q.cell)
    (c : ℂ)
    (hc : (souzaAtomFamily G s p hs hp hp_top).IsAtom Q.toWeakGridCell c) :
    (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
      (souzaAtomFamily G s p hs hp hp_top)).IsAtom
        (WeakGridSpace.levelCellToWeakGridCell
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          0 W.inducedRootLevelCell)
        c := by
  classical
  have hc_bound :
      ‖c‖ ≤ (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) := by
    simpa [souzaAtomFamily, souzaAtomsSet, GoodGridCell.toWeakGridCell,
      WeakGridSpace.AtomFamily.IsAtom] using hc
  have hμ_le : G.grid.μ W.cell ≤ G.grid.μ Q.cell :=
    MeasureTheory.measure_mono hsub
  have hQ_ne_top : G.grid.μ Q.cell ≠ ∞ := by
    letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ Q.cell
  have hμ_toReal_le :
      (G.grid.μ W.cell).toReal ≤ (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_mono hQ_ne_top hμ_le
  have hW_pos_en : 0 < G.grid.μ W.cell :=
    G.grid.positive_measure W.level W.cell W.mem
  have hW_ne_top : G.grid.μ W.cell ≠ ∞ := by
    letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact MeasureTheory.measure_ne_top G.grid.μ W.cell
  have hW_pos : 0 < (G.grid.μ W.cell).toReal :=
    ENNReal.toReal_pos hW_pos_en.ne' hW_ne_top
  have hexp_nonpos : s - (p.toReal)⁻¹ ≤ 0 := by linarith
  have hpow :
      (G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) ≤
        (G.grid.μ W.cell).toReal ^ (s - (p.toReal)⁻¹) :=
    rpow_le_rpow_of_nonpos_exponent hW_pos hμ_toReal_le hexp_nonpos
  change ‖c‖ ≤ (G.grid.μ W.cell).toReal ^ (s - (p.toReal)⁻¹)
  exact hc_bound.trans hpow

/--
If `Q ⊆ W`, a Souza atom on `Q` is the same atom on the corresponding cell of
the grid induced on `W`.
-/
theorem souzaAtom_mem_inducedCell_of_subset
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (W Q : GoodGridCell G)
    (hlevel : W.level ≤ Q.level) (hsub : Q.cell ⊆ W.cell)
    (c : ℂ)
    (hc : (souzaAtomFamily G s p hs hp hp_top).IsAtom Q.toWeakGridCell c) :
    (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
      (souzaAtomFamily G s p hs hp hp_top)).IsAtom
        (WeakGridSpace.levelCellToWeakGridCell
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (Q.level - W.level)
          (W.toInducedLevelCellOfSubset Q hlevel hsub))
        c := by
  classical
  simpa [souzaAtomFamily, souzaAtomsSet, GoodGridCell.toWeakGridCell,
    GoodGridCell.toInducedLevelCellOfSubset,
    WeakGridSpace.inducedAtomFamily, WeakGridSpace.inducedWeakGridCellToAmbient,
    WeakGridSpace.ambientLevelCellToInduced,
    WeakGridSpace.AtomFamily.IsAtom] using hc

/--
If two cells are disjoint, restricting a canonical Souza atom on `Q` to `W`
gives the zero function.
-/
theorem indicator_mul_canonicalSouzaAtom_eq_zero_of_disjoint
    {G : GoodGridSpace (α := α)} (W Q : GoodGridCell G)
    (s : ℝ) (p : ℝ≥0∞)
    (hdisj : Disjoint Q.cell W.cell) :
    (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
      canonicalSouzaAtom G s p Q x) = fun _ => 0 := by
  classical
  funext x
  by_cases hxW : x ∈ W.cell
  · have hxQ : x ∉ Q.cell := by
      intro hxQ
      exact (Set.disjoint_left.mp hdisj hxQ hxW).elim
    simp [canonicalSouzaAtom, hxW, hxQ]
  · simp [canonicalSouzaAtom, hxW]

/--
If `Q ⊆ W`, restricting a canonical Souza atom on `Q` to `W` leaves it
unchanged.
-/
theorem indicator_mul_canonicalSouzaAtom_eq_self_of_subset
    {G : GoodGridSpace (α := α)} (W Q : GoodGridCell G)
    (s : ℝ) (p : ℝ≥0∞)
    (hsub : Q.cell ⊆ W.cell) :
    (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
      canonicalSouzaAtom G s p Q x) =
      canonicalSouzaAtom G s p Q := by
  classical
  funext x
  by_cases hxQ : x ∈ Q.cell
  · have hxW : x ∈ W.cell := hsub hxQ
    simp [canonicalSouzaAtom, hxW, hxQ]
  · simp [canonicalSouzaAtom, hxQ]

/--
If `W ⊆ Q`, restricting a canonical Souza atom on `Q` to `W` is a constant
multiple of the indicator of `W`.
-/
theorem indicator_mul_canonicalSouzaAtom_eq_indicator_of_superset
    {G : GoodGridSpace (α := α)} (W Q : GoodGridCell G)
    (s : ℝ) (p : ℝ≥0∞)
    (hsub : W.cell ⊆ Q.cell) :
    (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
      canonicalSouzaAtom G s p Q x) =
      W.cell.indicator
        (fun _ => (((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) := by
  classical
  funext x
  by_cases hxW : x ∈ W.cell
  · have hxQ : x ∈ Q.cell := hsub hxW
    simp [canonicalSouzaAtom, hxW, hxQ]
  · simp [canonicalSouzaAtom, hxW]

/--
If two cells are disjoint, restricting a constant indicator on `Q` to `W`
gives the zero function.
-/
theorem indicator_mul_cellIndicator_eq_zero_of_disjoint
    {G : GoodGridSpace (α := α)} (W Q : GoodGridCell G)
    (c : ℂ) (hdisj : Disjoint Q.cell W.cell) :
    (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
      Q.cell.indicator (fun _ => c) x) = fun _ => 0 := by
  classical
  funext x
  by_cases hxW : x ∈ W.cell
  · have hxQ : x ∉ Q.cell := by
      intro hxQ
      exact (Set.disjoint_left.mp hdisj hxQ hxW).elim
    simp [hxW, hxQ]
  · simp [hxW]

/--
If `Q ⊆ W`, restricting a constant indicator on `Q` to `W` leaves it
unchanged.
-/
theorem indicator_mul_cellIndicator_eq_self_of_subset
    {G : GoodGridSpace (α := α)} (W Q : GoodGridCell G)
    (c : ℂ) (hsub : Q.cell ⊆ W.cell) :
    (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
      Q.cell.indicator (fun _ => c) x) =
      Q.cell.indicator (fun _ => c) := by
  classical
  funext x
  by_cases hxQ : x ∈ Q.cell
  · have hxW : x ∈ W.cell := hsub hxQ
    simp [hxW, hxQ]
  · simp [hxQ]

/--
If `W ⊆ Q`, restricting a constant indicator on `Q` to `W` gives the same
constant indicator on `W`.
-/
theorem indicator_mul_cellIndicator_eq_indicator_of_superset
    {G : GoodGridSpace (α := α)} (W Q : GoodGridCell G)
    (c : ℂ) (hsub : W.cell ⊆ Q.cell) :
    (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
      Q.cell.indicator (fun _ => c) x) =
      W.cell.indicator (fun _ => c) := by
  classical
  funext x
  by_cases hxW : x ∈ W.cell
  · have hxQ : x ∈ Q.cell := hsub hxW
    simp [hxW, hxQ]
  · simp [hxW]

/--
Restricting a single Souza atom to `W` has an induced atomic representation
concentrated at the natural level `i - W.level`, with coefficient power at most
`1`.
-/
theorem restrict_souzaAtomFamily_toFunction_oneBlockRepresentation
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hs_le_inv : s ≤ (p.toReal)⁻¹)
    (W : GoodGridCell G) {i : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i)
    (c : ℂ)
    (hc : (souzaAtomFamily G s p hs hp hp_top).IsAtom
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) c) :
    ∃ y : Lp ℂ p
        (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure,
    ∃ R : WeakGridSpace.LpGridRepresentation
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) y,
      WeakGridSpace.RepresentsFunction
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
          (souzaAtomFamily G s p hs hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) c x)
        y ∧
      (∀ j : ℕ, ∀ S : WeakGridSpace.LevelCell
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell) j,
        (¬ S.1 ⊆ Q.1 → ((R.block j).coeff S = 0)) ∧
        (j < W.restrictionLevel i → ((R.block j).coeff S = 0))) ∧
      ∀ n : ℕ, R.levelCoeffPower n ≤
        if n = W.restrictionLevel i then 1 else 0 := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell A
  let Qg : GoodGridCell G := ⟨i, Q.1, Q.2⟩
  have hcQg : A.IsAtom Qg.toWeakGridCell c := by
    simpa [A, Qg, GoodGridCell.toWeakGridCell] using hc
  rcases le_total W.level i with hWi | hiW
  · rcases W.subset_or_disjoint_of_le Qg hWi with hsub | hdisj
    · let P := W.toInducedLevelCellOfSubset Qg hWi hsub
      have hAtom : Ai.IsAtom (WeakGridSpace.levelCellToWeakGridCell Wi (i - W.level) P) c := by
        simpa [A, Ai, Wi, Qg, P] using
          souzaAtom_mem_inducedCell_of_subset
            G s p hs hp hp_top W Qg hWi hsub c hcQg
      let B : WeakGridSpace.LevelBlock Ai (i - W.level) :=
        WeakGridSpace.LevelBlock.singleAtom Ai P (1 : ℂ) c hAtom
      let y : Lp ℂ p Wi.measure := B.toLp Ai
      let R : WeakGridSpace.LpGridRepresentation Ai y :=
        WeakGridSpace.LpGridRepresentation.singleBlockRepresentation (G := Wi) (A := Ai) B
      refine ⟨y, R, ?_, ?_, ?_⟩
      · have hB := WeakGridSpace.LevelBlock.singleAtom_ae_eq Ai P (1 : ℂ) c hAtom
        refine hB.trans (Filter.Eventually.of_forall ?_)
        intro x
        have hprod :=
          congrFun (indicator_mul_cellIndicator_eq_self_of_subset W Qg c hsub) x
        simpa [A, Ai, Wi, Qg, P, B, WeakGridSpace.AtomFamily.toFunction,
          WeakGridSpace.inducedAtomFamily, WeakGridSpace.inducedWeakGridCellToAmbient,
          GoodGridCell.toInducedLevelCellOfSubset, WeakGridSpace.ambientLevelCellToInduced,
          GoodGridCell.toWeakGridCell, souzaAtomFamily, souzaLocalVectorSpace,
          WeakGridSpace.levelCellToWeakGridCell, one_mul] using hprod.symm
      · intro j S
        constructor
        · intro hnot
          by_cases hj : j = i - W.level
          · subst j
            by_cases hSP : S = P
            · subst S
              exfalso
              apply hnot
              simp [P, Qg, GoodGridCell.toInducedLevelCellOfSubset,
                WeakGridSpace.ambientLevelCellToInduced]
            · simp [R, B, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation,
                WeakGridSpace.LevelBlock.singleAtom, hSP]
          · simp [R, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation,
              hj, WeakGridSpace.LevelBlock.zero]
        · intro hjlt
          have hj : j ≠ i - W.level := by
            intro hji
            subst j
            exact Nat.lt_irrefl _ hjlt
          simp [R, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation,
            hj, WeakGridSpace.LevelBlock.zero]
      · intro n
        have hlevel :=
          WeakGridSpace.LevelBlock.singleAtom_singleBlock_levelCoeffPower
            Ai P (1 : ℂ) c hAtom n
        rw [hlevel]
        have hone : ‖(1 : ℂ)‖ ^ p.toReal = (1 : ℝ) := by simp
        convert
          (show (if n = i - W.level then (1 : ℝ) else 0) ≤
              if n = i - W.level then (1 : ℝ) else 0 from le_rfl)
          using 1
        simp [Qg]
    · refine ⟨0, WeakGridSpace.LpGridRepresentation.zero Ai, ?_, ?_, ?_⟩
      · have hprod := indicator_mul_cellIndicator_eq_zero_of_disjoint W Qg c hdisj
        have htarget :
            (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) c x) =
              fun _ => 0 := by
          simpa [A, Qg, WeakGridSpace.AtomFamily.toFunction,
            GoodGridCell.toWeakGridCell, souzaAtomFamily, souzaLocalVectorSpace,
            WeakGridSpace.levelCellToWeakGridCell] using hprod
        rw [WeakGridSpace.RepresentsFunction, htarget]
        exact MeasureTheory.Lp.coeFn_zero ℂ p Wi.measure
      · intro j S
        constructor <;> intro _ <;> simp [WeakGridSpace.LpGridRepresentation.zero,
          WeakGridSpace.LevelBlock.zero]
      · intro n
        rw [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower]
        by_cases hn : n = W.restrictionLevel i <;> simp [hn]
  · rcases Qg.subset_or_disjoint_of_le W hiW with hsub | hdisj
    · let P := W.inducedRootLevelCell
      have hAtom : Ai.IsAtom (WeakGridSpace.levelCellToWeakGridCell Wi 0 P) c := by
        simpa [A, Ai, Wi, Qg, P] using
          souzaAtom_mem_inducedRoot_of_subset
            G s p hs hp hp_top hs_le_inv hsub c hcQg
      let B : WeakGridSpace.LevelBlock Ai 0 :=
        WeakGridSpace.LevelBlock.singleAtom Ai P (1 : ℂ) c hAtom
      let y : Lp ℂ p Wi.measure := B.toLp Ai
      let R : WeakGridSpace.LpGridRepresentation Ai y :=
        WeakGridSpace.LpGridRepresentation.singleBlockRepresentation (G := Wi) (A := Ai) B
      refine ⟨y, R, ?_, ?_, ?_⟩
      · have hB := WeakGridSpace.LevelBlock.singleAtom_ae_eq Ai P (1 : ℂ) c hAtom
        refine hB.trans (Filter.Eventually.of_forall ?_)
        intro x
        have hprod :=
          congrFun (indicator_mul_cellIndicator_eq_indicator_of_superset W Qg c hsub) x
        simpa [A, Ai, Wi, Qg, P, B, WeakGridSpace.AtomFamily.toFunction,
          WeakGridSpace.inducedAtomFamily, WeakGridSpace.inducedWeakGridCellToAmbient,
          GoodGridCell.inducedRootLevelCell, GoodGridCell.toWeakGridCell,
          souzaAtomFamily, souzaLocalVectorSpace,
          WeakGridSpace.levelCellToWeakGridCell, one_mul] using hprod.symm
      · intro j S
        constructor
        · intro hnot
          by_cases hj : j = 0
          · subst j
            by_cases hSP : S = P
            · subst S
              exfalso
              exact hnot hsub
            · simp [R, B, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation,
                WeakGridSpace.LevelBlock.singleAtom, hSP]
          · simp [R, WeakGridSpace.LpGridRepresentation.singleBlockRepresentation,
              hj, WeakGridSpace.LevelBlock.zero]
        · intro hjlt
          have hlev_zero : W.restrictionLevel i = 0 := Nat.sub_eq_zero_of_le hiW
          have hfalse : False := by
            rw [hlev_zero] at hjlt
            exact Nat.not_lt_zero _ hjlt
          exact False.elim hfalse
      · intro n
        have hlevel :=
          WeakGridSpace.LevelBlock.singleAtom_singleBlock_levelCoeffPower
            Ai P (1 : ℂ) c hAtom n
        rw [hlevel]
        have hlev_zero : W.restrictionLevel i = 0 := Nat.sub_eq_zero_of_le hiW
        have hone : ‖(1 : ℂ)‖ ^ p.toReal = (1 : ℝ) := by simp
        convert
          (show (if n = 0 then (1 : ℝ) else 0) ≤
              if n = 0 then (1 : ℝ) else 0 from le_rfl)
          using 1
        · simp
        · rw [hlev_zero]
    · refine ⟨0, WeakGridSpace.LpGridRepresentation.zero Ai, ?_, ?_, ?_⟩
      · have hprod := indicator_mul_cellIndicator_eq_zero_of_disjoint W Qg c hdisj.symm
        have htarget :
            (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q) c x) =
              fun _ => 0 := by
          simpa [A, Qg, WeakGridSpace.AtomFamily.toFunction,
            GoodGridCell.toWeakGridCell, souzaAtomFamily, souzaLocalVectorSpace,
            WeakGridSpace.levelCellToWeakGridCell] using hprod
        rw [WeakGridSpace.RepresentsFunction, htarget]
        exact MeasureTheory.Lp.coeFn_zero ℂ p Wi.measure
      · intro j S
        constructor <;> intro _ <;> simp [WeakGridSpace.LpGridRepresentation.zero,
          WeakGridSpace.LevelBlock.zero]
      · intro n
        rw [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower]
        by_cases hn : n = W.restrictionLevel i <;> simp [hn]

/--
If a representation has coefficient power supported at one level, then its
coefficient family has finite `(p,1)` cost.
-/
private theorem coeffFinitePQCost_of_levelCoeffPower_le_singleton
    {s : ℝ} {p u : ℝ≥0∞}
    (G : WeakGridSpace.WeakGridSpace (α := α))
    (A : WeakGridSpace.AtomFamily G s p u)
    (q : ℝ≥0∞)
    (hp_ne_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    [Fact (1 ≤ q)]
    {y : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A y)
    (k : ℕ)
    (hlevel : ∀ n : ℕ, R.levelCoeffPower n ≤ if n = k then 1 else 0) :
    WeakGridSpace.CoeffFinitePQCost
      (p := p) (q := q) G
      (fun j S => ((R.block j).coeff S)) := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  by_cases hq_top : q = ∞
  · rw [WeakGridSpace.CoeffFinitePQCost, if_pos hq_top]
    let f : ℕ → ℝ := fun n =>
      (WeakGridSpace.CoeffPLevel
        (p := p) G (fun j S => ((R.block j).coeff S)) n) ^ (1 / p.toReal)
    have hzero_inv : (0 : ℝ) ^ p.toReal⁻¹ = 0 :=
      Real.zero_rpow (inv_ne_zero hp_pos.ne')
    have hzero : ∀ n, n ≠ k → f n = 0 := by
      intro n hnk
      have hle0 : R.levelCoeffPower n ≤ 0 := by
        simpa [hnk] using hlevel n
      have hlevel_zero : R.levelCoeffPower n = 0 :=
        le_antisymm hle0 (R.levelCoeffPower_nonneg n)
      have hcoeff_zero :
          WeakGridSpace.CoeffPLevel
            (p := p) G (fun j S => ((R.block j).coeff S)) n = 0 := by
        simpa [WeakGridSpace.CoeffPLevel,
          WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hlevel_zero
      simp [f, hcoeff_zero, hzero_inv, one_div]
    have hfinite_range : (Set.range f).Finite := by
      refine ((Set.finite_singleton 0).union
        ((Set.finite_singleton k).image f)).subset ?_
      intro x hx
      rcases hx with ⟨n, rfl⟩
      by_cases hnk : n = k
      · exact Or.inr ⟨n, by simpa [hnk], rfl⟩
      · exact Or.inl (hzero n hnk)
    simpa [f] using hfinite_range.bddAbove
  · rw [WeakGridSpace.CoeffFinitePQCost, if_neg hq_top]
    have hq_ne_zero : q ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ q))
    have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq_ne_zero hq_top
    have hzero_qp : (0 : ℝ) ^ (q.toReal / p.toReal) = 0 :=
      Real.zero_rpow (div_ne_zero hq_pos.ne' hp_pos.ne')
    refine summable_of_hasFiniteSupport ?_
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton k).subset ?_
    intro n hn
    contrapose! hn
    rw [Function.mem_support]
    have hnk : n ≠ k := by
      simpa using hn
    have hle0 : R.levelCoeffPower n ≤ 0 := by
      simpa [hnk] using hlevel n
    have hlevel_zero : R.levelCoeffPower n = 0 :=
      le_antisymm hle0 (R.levelCoeffPower_nonneg n)
    have hcoeff_zero :
        WeakGridSpace.CoeffPLevel
          (p := p) G (fun j S => ((R.block j).coeff S)) n = 0 := by
      simpa [WeakGridSpace.CoeffPLevel,
        WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hlevel_zero
    simp [hcoeff_zero, hzero_qp]

/--
If the coefficient power is supported at one level, with any finite bound at
that level, then the coefficient family has finite `(p,q)` cost.
-/
private theorem coeffFinitePQCost_of_levelCoeffPower_le_singleton_const
    {s : ℝ} {p u : ℝ≥0∞}
    (G : WeakGridSpace.WeakGridSpace (α := α))
    (A : WeakGridSpace.AtomFamily G s p u)
    (q : ℝ≥0∞)
    (hp_ne_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    [Fact (1 ≤ q)]
    {y : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A y)
    (k : ℕ) (C : ℝ)
    (hlevel : ∀ n : ℕ, R.levelCoeffPower n ≤ if n = k then C else 0) :
    WeakGridSpace.CoeffFinitePQCost
      (p := p) (q := q) G
      (fun j S => ((R.block j).coeff S)) := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  by_cases hq_top : q = ∞
  · rw [WeakGridSpace.CoeffFinitePQCost, if_pos hq_top]
    let f : ℕ → ℝ := fun n =>
      (WeakGridSpace.CoeffPLevel
        (p := p) G (fun j S => ((R.block j).coeff S)) n) ^ (1 / p.toReal)
    have hzero_inv : (0 : ℝ) ^ p.toReal⁻¹ = 0 :=
      Real.zero_rpow (inv_ne_zero hp_pos.ne')
    have hzero : ∀ n, n ≠ k → f n = 0 := by
      intro n hnk
      have hle0 : R.levelCoeffPower n ≤ 0 := by
        simpa [hnk] using hlevel n
      have hlevel_zero : R.levelCoeffPower n = 0 :=
        le_antisymm hle0 (R.levelCoeffPower_nonneg n)
      have hcoeff_zero :
          WeakGridSpace.CoeffPLevel
            (p := p) G (fun j S => ((R.block j).coeff S)) n = 0 := by
        simpa [WeakGridSpace.CoeffPLevel,
          WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hlevel_zero
      simp [f, hcoeff_zero, hzero_inv, one_div]
    have hfinite_range : (Set.range f).Finite := by
      refine ((Set.finite_singleton 0).union
        ((Set.finite_singleton k).image f)).subset ?_
      intro x hx
      rcases hx with ⟨n, rfl⟩
      by_cases hnk : n = k
      · exact Or.inr ⟨n, by simpa [hnk], rfl⟩
      · exact Or.inl (hzero n hnk)
    simpa [f] using hfinite_range.bddAbove
  · rw [WeakGridSpace.CoeffFinitePQCost, if_neg hq_top]
    have hq_ne_zero : q ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ q))
    have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq_ne_zero hq_top
    have hzero_qp : (0 : ℝ) ^ (q.toReal / p.toReal) = 0 :=
      Real.zero_rpow (div_ne_zero hq_pos.ne' hp_pos.ne')
    refine summable_of_hasFiniteSupport ?_
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton k).subset ?_
    intro n hn
    contrapose! hn
    rw [Function.mem_support]
    have hnk : n ≠ k := by
      simpa using hn
    have hle0 : R.levelCoeffPower n ≤ 0 := by
      simpa [hnk] using hlevel n
    have hlevel_zero : R.levelCoeffPower n = 0 :=
      le_antisymm hle0 (R.levelCoeffPower_nonneg n)
    have hcoeff_zero :
        WeakGridSpace.CoeffPLevel
          (p := p) G (fun j S => ((R.block j).coeff S)) n = 0 := by
      simpa [WeakGridSpace.CoeffPLevel,
        WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hlevel_zero
    simp [hcoeff_zero, hzero_qp]

private theorem coeff_eq_zero_of_levelCoeffPower_le_zero
    {s : ℝ} {p u : ℝ≥0∞}
    {G : WeakGridSpace.WeakGridSpace (α := α)}
    {A : WeakGridSpace.AtomFamily G s p u}
    [Fact (1 ≤ p)]
    {y : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A y)
    {n : ℕ}
    (hlevel0 : R.levelCoeffPower n ≤ 0)
    (P : WeakGridSpace.LevelCell G n) :
    (R.block n).coeff P = 0 := by
  classical
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
      A.p_ne_top
  have hterm_le :
      ‖(R.block n).coeff P‖ ^ p.toReal ≤ R.levelCoeffPower n := by
    unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
    exact Finset.single_le_sum
      (fun Q _ => Real.rpow_nonneg (norm_nonneg ((R.block n).coeff Q)) _)
      (Finset.mem_univ P)
  have hterm_zero : ‖(R.block n).coeff P‖ ^ p.toReal = 0 :=
    le_antisymm (hterm_le.trans hlevel0)
      (Real.rpow_nonneg (norm_nonneg ((R.block n).coeff P)) _)
  have hnorm_zero : ‖(R.block n).coeff P‖ = 0 := by
    by_contra hne
    have hnorm_pos : 0 < ‖(R.block n).coeff P‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hpow_pos : 0 < ‖(R.block n).coeff P‖ ^ p.toReal :=
      Real.rpow_pos_of_pos hnorm_pos p.toReal
    linarith
  exact norm_eq_zero.mp hnorm_zero

/--
The one-level coefficient-power bound gives the geometric decay required in
`RepresentationWsubGandALS`, with constant `1`.
-/
private theorem levelCoeffPower_le_geometric_of_singleton_bound
    {s : ℝ} {p u : ℝ≥0∞}
    {G : WeakGridSpace.WeakGridSpace (α := α)}
    {A : WeakGridSpace.AtomFamily G s p u}
    [Fact (1 ≤ p)]
    {y : Lp ℂ p G.measure}
    (R : WeakGridSpace.LpGridRepresentation A y)
    (k : ℕ) (lam : ℝ) (hlam_pos : 0 < lam)
    (hlevel : ∀ n : ℕ, R.levelCoeffPower n ≤ if n = k then 1 else 0) :
    ∀ j : ℕ, k ≤ j → R.levelCoeffPower j ≤ 1 * lam ^ (j - k) := by
  intro j hkj
  by_cases hj : j = k
  · subst j
    simpa using hlevel k
  · have hle0 : R.levelCoeffPower j ≤ 0 := by
      simpa [hj] using hlevel j
    have hnonneg : 0 ≤ 1 * lam ^ (j - k) :=
      mul_nonneg zero_le_one (pow_nonneg hlam_pos.le _)
    exact hle0.trans hnonneg

/-- The uniform ambient decay ratio for restricting Souza atoms to a cell. -/
noncomputable def souzaAmbientRestrictionLambda
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) : ℝ :=
  (G.grid.lambda2 ^ ((p.toReal)⁻¹ - s)) ^ p.toReal

private theorem souzaAmbientRestrictionLambda_pos
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    0 < souzaAmbientRestrictionLambda G s p := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hlam_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  dsimp [souzaAmbientRestrictionLambda]
  exact Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hlam_pos _) _

private theorem souzaAmbientRestrictionLambda_lt_one
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hs_lt_inv : s < (p.toReal)⁻¹) :
    souzaAmbientRestrictionLambda G s p < 1 := by
  let δ : ℝ := (p.toReal)⁻¹ - s
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
    le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hρ_lt : G.grid.lambda2 ^ δ < 1 :=
    Real.rpow_lt_one hlam_nonneg G.grid.hlambda2_lt_one hδ_pos
  have hρ_pos : 0 < G.grid.lambda2 ^ δ := by
    exact Real.rpow_pos_of_pos
      (lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2) δ
  dsimp [souzaAmbientRestrictionLambda, δ]
  exact Real.rpow_lt_one hρ_pos.le hρ_lt hp_pos

private theorem souzaAncestor_geometric_coeffPower_eq_lambda_pow
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) (d : ℕ) :
    ((G.grid.lambda2 ^ d : ℝ) ^ ((p.toReal)⁻¹ - s)) ^ p.toReal =
      souzaAmbientRestrictionLambda G s p ^ d := by
  let δ : ℝ := (p.toReal)⁻¹ - s
  have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
    le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hleft :
      ((G.grid.lambda2 ^ d : ℝ) ^ ((p.toReal)⁻¹ - s)) ^ p.toReal =
        G.grid.lambda2 ^ ((δ * (d : ℝ)) * p.toReal) := by
    dsimp [δ]
    calc
      ((G.grid.lambda2 ^ d : ℝ) ^ ((p.toReal)⁻¹ - s)) ^ p.toReal
          = (G.grid.lambda2 ^ (((p.toReal)⁻¹ - s) * (d : ℝ))) ^ p.toReal := by
              congr 1
              simpa [mul_comm] using
                (Real.rpow_natCast_mul hlam_nonneg d ((p.toReal)⁻¹ - s)).symm
      _ = G.grid.lambda2 ^ ((((p.toReal)⁻¹ - s) * (d : ℝ)) * p.toReal) := by
              rw [← Real.rpow_mul hlam_nonneg]
  have hright :
      souzaAmbientRestrictionLambda G s p ^ d =
        G.grid.lambda2 ^ ((δ * p.toReal) * (d : ℝ)) := by
    dsimp [souzaAmbientRestrictionLambda, δ]
    calc
      ((G.grid.lambda2 ^ ((p.toReal)⁻¹ - s)) ^ p.toReal) ^ d
          = (G.grid.lambda2 ^ (((p.toReal)⁻¹ - s) * p.toReal)) ^ d := by
              congr 1
              rw [← Real.rpow_mul hlam_nonneg]
      _ = G.grid.lambda2 ^ ((((p.toReal)⁻¹ - s) * p.toReal) * (d : ℝ)) := by
              simpa [mul_comm] using
                (Real.rpow_mul_natCast hlam_nonneg
                  (((p.toReal)⁻¹ - s) * p.toReal) d).symm
  rw [hleft, hright]
  congr 1
  ring

private theorem levelCoeffPower_le_geometric_of_ambientRestriction_bound
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (W : GoodGridCell G) {i : ℕ}
    {A : WeakGridSpace.AtomFamily G.toWeakGridSpace s p ∞}
    [Fact (1 ≤ p)]
    {y : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation A y)
    (hlevel : ∀ n : ℕ, R.levelCoeffPower n ≤
      if W.level ≤ i then
        if n = i then 1 else 0
      else
        if n = W.level then
          ((G.grid.lambda2 ^ (W.level - i) : ℝ) ^ ((p.toReal)⁻¹ - s)) ^ p.toReal
        else 0) :
    ∀ j : ℕ, i ≤ j →
      R.levelCoeffPower j ≤
        1 * souzaAmbientRestrictionLambda G s p ^ (j - i) := by
  intro j hij
  by_cases hWi : W.level ≤ i
  · by_cases hji : j = i
    · subst j
      simpa [hWi] using hlevel i
    · have hle0 : R.levelCoeffPower j ≤ 0 := by
        simpa [hWi, hji] using hlevel j
      exact hle0.trans
        (mul_nonneg zero_le_one
          (pow_nonneg (le_of_lt (souzaAmbientRestrictionLambda_pos G s p
            (Fact.out : (1 : ℝ≥0∞) ≤ p)
            (by
              -- This branch only uses nonnegativity; `p ≠ ∞` is supplied by the atom family.
              exact A.p_ne_top))) _))
  · by_cases hjW : j = W.level
    · subst j
      have hgeom :=
        souzaAncestor_geometric_coeffPower_eq_lambda_pow G s p (W.level - i)
      simpa [hWi, hgeom] using hlevel W.level
    · have hle0 : R.levelCoeffPower j ≤ 0 := by
        simpa [hWi, hjW] using hlevel j
      exact hle0.trans
        (mul_nonneg zero_le_one
          (pow_nonneg (le_of_lt (souzaAmbientRestrictionLambda_pos G s p
            (Fact.out : (1 : ℝ≥0∞) ≤ p) A.p_ne_top)) _))

private theorem ambient_id_almostLinear_bound :
    ∀ i : ℕ,
      ((fun i : ℕ => i) i : NNReal) ≤ (1 : ℝ) * (i : NNReal) + 0 ∧
      (1 : ℝ) * (i : NNReal) + 0 ≤ ((fun i : ℕ => i) i : NNReal) := by
  intro i
  constructor <;> norm_num

private theorem ambient_id_almostLinearSequence :
    WeakGridSpace.AlmostLinearSequence (fun i : ℕ => i) :=
  ⟨0, 0, 1, by norm_num, ambient_id_almostLinear_bound⟩

/--
Ambient atom-data for restricting an atomic expansion to a good-grid cell.

This is the corrected transmutation package: source level `i` is sent to the
same ambient level `i`.  The local representatives are supported inside the
source cell, vanish before level `i`, and have the uniform geometric decay
coming from `s < 1 / p`.
-/
theorem restrict_souzaRepresentation_ambientTransmutationAtomData
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g) :
    ∃ h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
        Lp ℂ p G.toWeakGridSpace.measure,
    ∃ Rt : (i : ℕ) → (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i) →
        WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top) (h i Q),
      WeakGridSpace.RepresentationWsubGandALS
        (p := p) (q := q)
        G.toWeakGridSpace G.toWeakGridSpace
        (souzaAtomFamily G s p hs hp hp_top)
        (fun i : ℕ => i) ambient_id_almostLinearSequence
        (souzaAmbientRestrictionLambda G s p)
        (souzaAmbientRestrictionLambda_pos G s p hp hp_top)
        (souzaAmbientRestrictionLambda_lt_one G s p hp hp_top hs_lt_inv)
        1 (by norm_num) h Rt ∧
      (∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
            (souzaAtomFamily G s p hs hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
              ((R.block i).atom Q) x)
          (h i Q)) ∧
      (∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        ∀ n, n < W.level →
          ((Rt i Q).block n).toLp (souzaAtomFamily G s p hs hp hp_top) = 0) ∧
      (∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        ∀ n (P : WeakGridSpace.LevelCell G.toWeakGridSpace n), n < W.level →
          ((Rt i Q).block n).coeff P = 0) ∧
      (∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        ∀ n (P : WeakGridSpace.LevelCell G.toWeakGridSpace n),
          ¬ P.1 ⊆ W.cell → ((Rt i Q).block n).coeff P = 0) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let lam := souzaAmbientRestrictionLambda G s p
  let localData :
      (i : ℕ) → (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i) →
        ∃ y : Lp ℂ p G.toWeakGridSpace.measure,
        ∃ Rt : WeakGridSpace.LpGridRepresentation A y,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction
                (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
                ((R.block i).atom Q) x)
            y ∧
          (∀ n, n < W.level → (Rt.block n).toLp A = 0) ∧
          (∀ n (P : WeakGridSpace.LevelCell G.toWeakGridSpace n),
            ¬ P.1 ⊆ W.cell → (Rt.block n).coeff P = 0) ∧
          (∀ n (P : WeakGridSpace.LevelCell G.toWeakGridSpace n),
            ¬ P.1 ⊆ Q.1 → (Rt.block n).coeff P = 0) ∧
          ∀ n : ℕ, Rt.levelCoeffPower n ≤
            if W.level ≤ i then
              if n = i then 1 else 0
            else
              if n = W.level then
                ((G.grid.lambda2 ^ (W.level - i) : ℝ) ^
                  ((p.toReal)⁻¹ - s)) ^ p.toReal
              else 0 :=
    fun i Q =>
      restrict_souzaAtomFamily_toFunction_ambientSupportedOneBlockRepresentation
        G s p hs hp hp_top hs_lt_inv W Q ((R.block i).atom Q)
        (by simpa [A] using (R.block i).atom_mem Q)
  let h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
      Lp ℂ p G.toWeakGridSpace.measure :=
    fun i Q => Classical.choose (localData i Q)
  let Rt : (i : ℕ) → (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i) →
      WeakGridSpace.LpGridRepresentation A (h i Q) :=
    fun i Q => Classical.choose (Classical.choose_spec (localData i Q))
  have hspec :
      ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
            A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
              ((R.block i).atom Q) x)
          (h i Q) ∧
        (∀ n, n < W.level → ((Rt i Q).block n).toLp A = 0) ∧
        (∀ n (P : WeakGridSpace.LevelCell G.toWeakGridSpace n),
          ¬ P.1 ⊆ W.cell → ((Rt i Q).block n).coeff P = 0) ∧
        (∀ n (P : WeakGridSpace.LevelCell G.toWeakGridSpace n),
          ¬ P.1 ⊆ Q.1 → ((Rt i Q).block n).coeff P = 0) ∧
        ∀ n : ℕ, (Rt i Q).levelCoeffPower n ≤
          if W.level ≤ i then
            if n = i then 1 else 0
          else
            if n = W.level then
              ((G.grid.lambda2 ^ (W.level - i) : ℝ) ^
                ((p.toReal)⁻¹ - s)) ^ p.toReal
            else 0 := by
    intro i Q
    simpa [h, Rt, A] using
      (Classical.choose_spec (Classical.choose_spec (localData i Q)))
  refine ⟨h, Rt, ?_, ?_, ?_, ?_, ?_⟩
  · intro i Q
    refine ⟨?_, ?_, ?_⟩
    · by_cases hWi : W.level ≤ i
      · exact coeffFinitePQCost_of_levelCoeffPower_le_singleton_const
          G.toWeakGridSpace A q hp_top (Rt i Q) i 1
          (by intro n; simpa [hWi] using (hspec i Q).2.2.2.2 n)
      · exact coeffFinitePQCost_of_levelCoeffPower_le_singleton_const
          G.toWeakGridSpace A q hp_top (Rt i Q) W.level
          (((G.grid.lambda2 ^ (W.level - i) : ℝ) ^
            ((p.toReal)⁻¹ - s)) ^ p.toReal)
          (by intro n; simpa [hWi] using (hspec i Q).2.2.2.2 n)
    · intro j S
      constructor
      · exact (hspec i Q).2.2.2.1 j S
      · intro hji
        have hji' : j < i := by
          simpa using hji
        have hle0 : (Rt i Q).levelCoeffPower j ≤ 0 := by
          by_cases hWi : W.level ≤ i
          · have hji_ne : j ≠ i := by omega
            simpa [hWi, hji_ne] using (hspec i Q).2.2.2.2 j
          · have hiW : i < W.level := Nat.lt_of_not_ge hWi
            have hjW_ne : j ≠ W.level := by omega
            simpa [hWi, hjW_ne] using (hspec i Q).2.2.2.2 j
        exact coeff_eq_zero_of_levelCoeffPower_le_zero (Rt i Q) hle0 S
    · exact levelCoeffPower_le_geometric_of_ambientRestriction_bound
        G s p W (Rt i Q) (hspec i Q).2.2.2.2
  · intro i Q
    exact (hspec i Q).1
  · intro i Q
    exact (hspec i Q).2.1
  · intro i Q
    intro n P hnW
    have hle0 : (Rt i Q).levelCoeffPower n ≤ 0 := by
      by_cases hWi : W.level ≤ i
      · have hni : n ≠ i := by omega
        simpa [hWi, hni] using (hspec i Q).2.2.2.2 n
      · have hnW_ne : n ≠ W.level := by omega
        simpa [hWi, hnW_ne] using (hspec i Q).2.2.2.2 n
    exact coeff_eq_zero_of_levelCoeffPower_le_zero (Rt i Q) hle0 P
  · intro i Q
    exact (hspec i Q).2.2.1

private theorem transmutationCoeff_eq_zero_of_local_coeff_eq_zero
    {s : ℝ} {p u : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ u)]
    (G W : WeakGridSpace.WeakGridSpace (α := α))
    (AW : WeakGridSpace.AtomFamily W s p u)
    (h : (i : ℕ) → WeakGridSpace.LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : WeakGridSpace.LevelCell G i) →
      WeakGridSpace.LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → WeakGridSpace.LevelCell G i → ℂ)
    (N j : ℕ) (P : WeakGridSpace.LevelCell W j)
    (hzero : ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G i,
      ((R i Q).block j).coeff P = 0) :
    WeakGridSpace.TransmutationCoeff G W AW h R c N P = 0 := by
  classical
  dsimp [WeakGridSpace.TransmutationCoeff]
  apply Finset.sum_eq_zero
  intro i _hi
  apply Finset.sum_eq_zero
  intro Q _hQ
  simp [hzero i Q]

private theorem transmutationBlock_coeff_eq_zero_of_local_coeff_eq_zero
    {s : ℝ} {p u : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ u)]
    (G W : WeakGridSpace.WeakGridSpace (α := α))
    (AW : WeakGridSpace.AtomFamily W s p u)
    (h : (i : ℕ) → WeakGridSpace.LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : WeakGridSpace.LevelCell G i) →
      WeakGridSpace.LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → WeakGridSpace.LevelCell G i → ℂ)
    (N j : ℕ) (P : WeakGridSpace.LevelCell W j)
    (hzero : ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G i,
      ((R i Q).block j).coeff P = 0) :
    (WeakGridSpace.TransmutationBlock G W AW h R c N j).coeff P = 0 := by
  have hcoeff :=
    transmutationCoeff_eq_zero_of_local_coeff_eq_zero G W AW h R c N j P hzero
  simp [WeakGridSpace.TransmutationBlock, hcoeff]

private theorem transmutationBlockLimit_coeff_eq_zero_of_local_coeff_eq_zero
    {s : ℝ} {p u : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ u)]
    (G W : WeakGridSpace.WeakGridSpace (α := α))
    (AW : WeakGridSpace.AtomFamily W s p u)
    (h : (i : ℕ) → WeakGridSpace.LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : WeakGridSpace.LevelCell G i) →
      WeakGridSpace.LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → WeakGridSpace.LevelCell G i → ℂ)
    (A_als r_als : ℝ) (j : ℕ) (P : WeakGridSpace.LevelCell W j)
    (hzero : ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G i,
      ((R i Q).block j).coeff P = 0) :
    (WeakGridSpace.TransmutationBlockLimit G W AW h R c A_als r_als j).coeff P = 0 := by
  have hcoeff :
      WeakGridSpace.TransmutationCoeffLimit G W AW h R c A_als r_als P = 0 := by
    dsimp [WeakGridSpace.TransmutationCoeffLimit]
    exact transmutationCoeff_eq_zero_of_local_coeff_eq_zero
      G W AW h R c (WeakGridSpace.transmutationStabilizationIndex A_als r_als j)
      j P hzero
  simp [WeakGridSpace.TransmutationBlockLimit, hcoeff]

private theorem levelBlock_toLp_eq_zero_of_coeff_eq_zero
    {s : ℝ} {p u : ℝ≥0∞}
    {G : WeakGridSpace.WeakGridSpace (α := α)}
    (A : WeakGridSpace.AtomFamily G s p u) {j : ℕ}
    (B : WeakGridSpace.LevelBlock A j)
    (hcoeff : ∀ P : WeakGridSpace.LevelCell G j, B.coeff P = 0) :
    B.toLp A = 0 := by
  simp [WeakGridSpace.LevelBlock.toLp, WeakGridSpace.LevelBlock.term, hcoeff]

private theorem representsPointwiseProduct_finset_sum_ambient_aux
    {G : WeakGridSpace.WeakGridSpace (α := α)}
    {p : ℝ≥0∞} {ι : Type*}
    (m : α → ℂ) (S : Finset ι)
    (x y : ι → Lp ℂ p G.measure)
    (hxy : ∀ i ∈ S,
      WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p)
        m (x i) (y i)) :
    WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p)
      m (∑ i ∈ S, x i) (∑ i ∈ S, y i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using
        (WeakGridSpace.representsPointwiseProduct_zero
          (G := G) (p := p) m)
  | insert a S ha hS =>
      have ha_rep :
          WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p)
            m (x a) (y a) := hxy a (by simp [ha])
      have hS_rep :
          WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p)
            m (∑ i ∈ S, x i) (∑ i ∈ S, y i) := by
        refine hS ?_
        intro i hi
        exact hxy i (by simp [hi])
      simpa [Finset.sum_insert ha] using ha_rep.add hS_rep

/-- Ambient version of the finite-level restriction product identity. -/
private theorem restrict_souzaLevelBlock_representsPointwiseProduct_of_ambientAtomRepresentations
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (W : GoodGridCell G) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    (hAtom : WeakGridSpace.LevelCell G.toWeakGridSpace k →
      Lp ℂ p G.toWeakGridSpace.measure)
    (hyAtom :
      ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
            (souzaAtomFamily G s p hs hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (B.atom Q) x)
          (hAtom Q)) :
    WeakGridSpace.RepresentsPointwiseProduct
      (G := G.toWeakGridSpace)
      (p := p)
      (W.cell.indicator fun _ => (1 : ℂ))
      (B.toLp (souzaAtomFamily G s p hs hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure)
      ((G.toWeakGridSpace.grid.partitions k).attach.sum
        (fun Q => B.coeff Q • hAtom Q)) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Gi := G.toWeakGridSpace
  let S := (G.toWeakGridSpace.grid.partitions k).attach
  have hsum_rep :
      WeakGridSpace.RepresentsFunction
        (G := Gi) (p := p)
        (fun x => ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x))
        (S.sum (fun Q => B.coeff Q • hAtom Q)) := by
    refine WeakGridSpace.representsFunction_finset_sum
      (G := Gi) (p := p) S
      (fun Q x =>
        B.coeff Q *
          (W.cell.indicator (fun _ => (1 : ℂ)) x *
            A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (B.atom Q) x))
      (fun Q => B.coeff Q • hAtom Q) ?_
    intro Q _hQ
    exact WeakGridSpace.representsFunction_smul (G := Gi) (p := p)
      (B.coeff Q) (by simpa [A, Gi] using hyAtom Q)
  have hsum_point :
      (fun x => ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x))
        = fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
          B.toFunLt A x := by
    funext x
    calc
      ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x)
        = ∑ Q ∈ S,
            W.cell.indicator (fun _ => (1 : ℂ)) x *
              (B.coeff Q *
                A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                  (B.atom Q) x) := by
            refine Finset.sum_congr rfl ?_
            intro Q _hQ
            ring
      _ = W.cell.indicator (fun _ => (1 : ℂ)) x *
          (∑ Q ∈ S,
            B.coeff Q *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x) := by
            rw [Finset.mul_sum]
      _ = W.cell.indicator (fun _ => (1 : ℂ)) x *
          B.toFunLt A x := by
            simp [S, WeakGridSpace.LevelBlock.toFunLt]
  have hblock :
      (B.toLp A : α → ℂ) =ᵐ[Gi.measure] B.toFunLt A := by
    simpa [A, Gi, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid] using
      (WeakGridSpace.LevelBlock.coeFn_toLp A B)
  have hsum_to_fun :
      (fun x => ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x))
        =ᵐ[Gi.measure] fun x =>
          W.cell.indicator (fun _ => (1 : ℂ)) x * B.toFunLt A x := by
    exact Filter.Eventually.of_forall fun x => by
      rw [hsum_point]
  have hfun_to_lp :
      (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x * B.toFunLt A x)
        =ᵐ[Gi.measure] fun x =>
          W.cell.indicator (fun _ => (1 : ℂ)) x * (B.toLp A : α → ℂ) x :=
    hblock.mono fun x hx => by
      change W.cell.indicator (fun _ => (1 : ℂ)) x * B.toFunLt A x =
        W.cell.indicator (fun _ => (1 : ℂ)) x * (B.toLp A : α → ℂ) x
      rw [← hx]
  exact hsum_rep.trans (hsum_to_fun.trans hfun_to_lp)

/-- Ambient finite initial segments represent the pointwise restriction. -/
theorem restrict_souzaRepresentation_partialSum_representsPointwiseProduct_ambient
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (W : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
      Lp ℂ p G.toWeakGridSpace.measure)
    (hAtom :
      ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
            (souzaAtomFamily G s p hs hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
              ((R.block i).atom Q) x)
          (h i Q)) :
    ∀ N : ℕ,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := G.toWeakGridSpace)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        ((∑ i ∈ Finset.range N,
            (R.block i).toLp (souzaAtomFamily G s p hs hp hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure)
        (WeakGridSpace.PartialSumLevels
          G.toWeakGridSpace G.toWeakGridSpace
          h (fun i Q => (R.block i).coeff Q) N) := by
  classical
  intro N
  let A := souzaAtomFamily G s p hs hp hp_top
  let Gi := G.toWeakGridSpace
  have hlevel :
      ∀ i ∈ Finset.range N,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := Gi) (p := p)
          (W.cell.indicator fun _ => (1 : ℂ))
          ((R.block i).toLp A : Lp ℂ p G.toWeakGridSpace.measure)
          ((G.toWeakGridSpace.grid.partitions i).attach.sum
            (fun Q => (R.block i).coeff Q • h i Q)) := by
    intro i _hi
    exact restrict_souzaLevelBlock_representsPointwiseProduct_of_ambientAtomRepresentations
      G s p hs hp hp_top W (R.block i) (h i) (hAtom i)
  simpa [WeakGridSpace.PartialSumLevels, A, Gi] using
    representsPointwiseProduct_finset_sum_ambient_aux
      (G := Gi) (p := p)
      (W.cell.indicator fun _ => (1 : ℂ))
      (Finset.range N)
      (fun i => ((R.block i).toLp A : Lp ℂ p G.toWeakGridSpace.measure))
      (fun i => (G.toWeakGridSpace.grid.partitions i).attach.sum
        (fun Q => (R.block i).coeff Q • h i Q))
      hlevel

/--
For an ambient Souza representation, the restriction of each source atom to
`W` supplies the atom-data package required by the transmutation theorem.

This theorem packages the local one-atom restriction result into global
families `h` and `Rt`.  The finite-sum pointwise-product identity is proved
separately from these data.
-/
theorem restrict_souzaRepresentation_transmutationAtomData
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hs_le_inv : s ≤ (p.toReal)⁻¹)
    (W : GoodGridCell G)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g) :
    ∃ h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
        Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure,
    ∃ Rt : (i : ℕ) → (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i) →
        WeakGridSpace.LpGridRepresentation
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) (h i Q),
      WeakGridSpace.RepresentationWsubGandALS
        (p := p) (q := q)
        G.toWeakGridSpace
        (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top))
        W.restrictionLevel W.restrictionLevel_almostLinear
        lam hlam_pos hlam_lt 1 (by norm_num) h Rt ∧
      ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        WeakGridSpace.RepresentsFunction
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p)
          (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
            (souzaAtomFamily G s p hs hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
              ((R.block i).atom Q) x)
          (h i Q) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell A
  let localData :
      (i : ℕ) → (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i) →
        ∃ y : Lp ℂ p Wi.measure,
        ∃ Rt : WeakGridSpace.LpGridRepresentation Ai y,
          WeakGridSpace.RepresentsFunction
            (G := Wi) (p := p)
            (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction
                (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
                ((R.block i).atom Q) x)
            y ∧
          (∀ j : ℕ, ∀ S : WeakGridSpace.LevelCell Wi j,
            (¬ S.1 ⊆ Q.1 → ((Rt.block j).coeff S = 0)) ∧
            (j < W.restrictionLevel i → ((Rt.block j).coeff S = 0))) ∧
          ∀ n : ℕ, Rt.levelCoeffPower n ≤
            if n = W.restrictionLevel i then 1 else 0 :=
    fun i Q =>
      restrict_souzaAtomFamily_toFunction_oneBlockRepresentation
        G s p hs hp hp_top hs_le_inv W Q ((R.block i).atom Q)
        (by
          simpa [A] using (R.block i).atom_mem Q)
  let h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
      Lp ℂ p Wi.measure :=
    fun i Q => Classical.choose (localData i Q)
  let Rt : (i : ℕ) → (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i) →
      WeakGridSpace.LpGridRepresentation Ai (h i Q) :=
    fun i Q => Classical.choose (Classical.choose_spec (localData i Q))
  have hspec :
      ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        WeakGridSpace.RepresentsFunction
          (G := Wi) (p := p)
          (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
            A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
              ((R.block i).atom Q) x)
          (h i Q) ∧
        (∀ j : ℕ, ∀ S : WeakGridSpace.LevelCell Wi j,
          (¬ S.1 ⊆ Q.1 → (((Rt i Q).block j).coeff S = 0)) ∧
          (j < W.restrictionLevel i → (((Rt i Q).block j).coeff S = 0))) ∧
        ∀ n : ℕ, (Rt i Q).levelCoeffPower n ≤
          if n = W.restrictionLevel i then 1 else 0 := by
    intro i Q
    simpa [h, Rt] using
      (Classical.choose_spec (Classical.choose_spec (localData i Q)))
  refine ⟨h, Rt, ?_, ?_⟩
  · intro i Q
    refine ⟨?_, ?_, ?_⟩
    · exact coeffFinitePQCost_of_levelCoeffPower_le_singleton
        Wi Ai q hp_top (Rt i Q) (W.restrictionLevel i) (hspec i Q).2.2
    · exact (hspec i Q).2.1
    · exact levelCoeffPower_le_geometric_of_singleton_bound
        (Rt i Q) (W.restrictionLevel i) lam hlam_pos (hspec i Q).2.2
  · intro i Q
    exact (hspec i Q).1

/-- Finite sums preserve pointwise-product representations. -/
private theorem representsPointwiseProduct_finset_sum
    {G : WeakGridSpace.WeakGridSpace (α := α)}
    {p : ℝ≥0∞} {ι : Type*}
    (m : α → ℂ) (S : Finset ι)
    (x y : ι → Lp ℂ p G.measure)
    (hxy : ∀ i ∈ S,
      WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p)
        m (x i) (y i)) :
    WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p)
      m (∑ i ∈ S, x i) (∑ i ∈ S, y i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using
        (WeakGridSpace.representsPointwiseProduct_zero
          (G := G) (p := p) m)
  | insert a S ha hS =>
      have ha_rep :
          WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p)
            m (x a) (y a) := hxy a (by simp [ha])
      have hS_rep :
          WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p)
            m (∑ i ∈ S, x i) (∑ i ∈ S, y i) := by
        refine hS ?_
        intro i hi
        exact hxy i (by simp [hi])
      simpa [Finset.sum_insert ha] using ha_rep.add hS_rep

/--
If each atom of a Souza level block has a chosen restriction representative,
then the finite level block has the corresponding pointwise-product
representative.
-/
private theorem restrict_souzaLevelBlock_representsPointwiseProduct_of_atomRepresentations
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (W : GoodGridCell G) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    (hAtom : WeakGridSpace.LevelCell G.toWeakGridSpace k →
      Lp ℂ p
        (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure)
    (hyAtom :
      ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        WeakGridSpace.RepresentsFunction
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p)
          (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
            (souzaAtomFamily G s p hs hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (B.atom Q) x)
          (hAtom Q)) :
    WeakGridSpace.RepresentsPointwiseProduct
      (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
      (p := p)
      (W.cell.indicator fun _ => (1 : ℂ))
      (B.toLp (souzaAtomFamily G s p hs hp hp_top) :
        Lp ℂ p G.toWeakGridSpace.measure)
      ((G.toWeakGridSpace.grid.partitions k).attach.sum
        (fun Q => B.coeff Q • hAtom Q)) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let S := (G.toWeakGridSpace.grid.partitions k).attach
  have hsum_rep :
      WeakGridSpace.RepresentsFunction
        (G := Wi) (p := p)
        (fun x => ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x))
        (S.sum (fun Q => B.coeff Q • hAtom Q)) := by
    refine WeakGridSpace.representsFunction_finset_sum
      (G := Wi) (p := p) S
      (fun Q x =>
        B.coeff Q *
          (W.cell.indicator (fun _ => (1 : ℂ)) x *
            A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (B.atom Q) x))
      (fun Q => B.coeff Q • hAtom Q) ?_
    intro Q _hQ
    exact WeakGridSpace.representsFunction_smul (G := Wi) (p := p)
      (B.coeff Q) (by simpa [A, Wi] using hyAtom Q)
  have hsum_point :
      (fun x => ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x))
        = fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
          B.toFunLt A x := by
    funext x
    calc
      ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x)
        = ∑ Q ∈ S,
            W.cell.indicator (fun _ => (1 : ℂ)) x *
              (B.coeff Q *
                A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                  (B.atom Q) x) := by
            refine Finset.sum_congr rfl ?_
            intro Q _hQ
            ring
      _ = W.cell.indicator (fun _ => (1 : ℂ)) x *
          (∑ Q ∈ S,
            B.coeff Q *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x) := by
            rw [Finset.mul_sum]
      _ = W.cell.indicator (fun _ => (1 : ℂ)) x *
          B.toFunLt A x := by
            simp [S, WeakGridSpace.LevelBlock.toFunLt]
  have hblock :
      (B.toLp A : α → ℂ) =ᵐ[Wi.measure] B.toFunLt A := by
    simpa [A, Wi, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid] using
      (WeakGridSpace.LevelBlock.coeFn_toLp A B)
  have hsum_to_fun :
      (fun x => ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x))
        =ᵐ[Wi.measure] fun x =>
          W.cell.indicator (fun _ => (1 : ℂ)) x * B.toFunLt A x := by
    exact Filter.Eventually.of_forall fun x => by
      rw [hsum_point]
  have hfun_to_lp :
      (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x * B.toFunLt A x)
        =ᵐ[Wi.measure] fun x =>
          W.cell.indicator (fun _ => (1 : ℂ)) x * (B.toLp A : α → ℂ) x :=
    hblock.mono fun x hx => by
      change W.cell.indicator (fun _ => (1 : ℂ)) x * B.toFunLt A x =
        W.cell.indicator (fun _ => (1 : ℂ)) x * (B.toLp A : α → ℂ) x
      rw [← hx]
  exact hsum_rep.trans (hsum_to_fun.trans hfun_to_lp)

/--
The atom-data representatives constructed above represent the restriction of
each finite initial segment of the ambient representation.
-/
theorem restrict_souzaRepresentation_partialSum_representsPointwiseProduct
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (W : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
      Lp ℂ p
        (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure)
    (hAtom :
      ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        WeakGridSpace.RepresentsFunction
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p)
          (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
            (souzaAtomFamily G s p hs hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
              ((R.block i).atom Q) x)
          (h i Q)) :
    ∀ N : ℕ,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        ((∑ i ∈ Finset.range N,
            (R.block i).toLp (souzaAtomFamily G s p hs hp hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure)
        (WeakGridSpace.PartialSumLevels
          G.toWeakGridSpace
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          h (fun i Q => (R.block i).coeff Q) N) := by
  classical
  intro N
  let A := souzaAtomFamily G s p hs hp hp_top
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  have hlevel :
      ∀ i ∈ Finset.range N,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := Wi) (p := p)
          (W.cell.indicator fun _ => (1 : ℂ))
          ((R.block i).toLp A : Lp ℂ p G.toWeakGridSpace.measure)
          ((G.toWeakGridSpace.grid.partitions i).attach.sum
            (fun Q => (R.block i).coeff Q • h i Q)) := by
    intro i _hi
    exact restrict_souzaLevelBlock_representsPointwiseProduct_of_atomRepresentations
      G s p hs hp hp_top W (R.block i) (h i) (hAtom i)
  simpa [WeakGridSpace.PartialSumLevels, A, Wi] using
    representsPointwiseProduct_finset_sum
      (G := Wi) (p := p)
      (W.cell.indicator fun _ => (1 : ℂ))
      (Finset.range N)
      (fun i => ((R.block i).toLp A : Lp ℂ p G.toWeakGridSpace.measure))
      (fun i => (G.toWeakGridSpace.grid.partitions i).attach.sum
        (fun Q => (R.block i).coeff Q • h i Q))
      hlevel

/--
Complete atom-data input for the abstract transmutation bridge, with
`k i = i - W.level` and constant `C = 1`.
-/
theorem restrict_souzaRepresentation_transmutationData
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hs_le_inv : s ≤ (p.toReal)⁻¹)
    (W : GoodGridCell G)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g) :
    ∃ h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
        Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure,
    ∃ Rt : (i : ℕ) → (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i) →
        WeakGridSpace.LpGridRepresentation
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) (h i Q),
      WeakGridSpace.RepresentationWsubGandALS
        (p := p) (q := q)
        G.toWeakGridSpace
        (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top))
        W.restrictionLevel W.restrictionLevel_almostLinear
        lam hlam_pos hlam_lt 1 (by norm_num) h Rt ∧
      ∀ N : ℕ,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p)
          (W.cell.indicator fun _ => (1 : ℂ))
          ((∑ i ∈ Finset.range N,
              (R.block i).toLp (souzaAtomFamily G s p hs hp hp_top)) :
            Lp ℂ p G.toWeakGridSpace.measure)
          (WeakGridSpace.PartialSumLevels
            G.toWeakGridSpace
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
            h (fun i Q => (R.block i).coeff Q) N) := by
  classical
  rcases restrict_souzaRepresentation_transmutationAtomData
      G s p q hs hp hp_top hs_le_inv W lam hlam_pos hlam_lt R with
    ⟨h, Rt, hRt, hAtom⟩
  refine ⟨h, Rt, hRt, ?_⟩
  exact restrict_souzaRepresentation_partialSum_representsPointwiseProduct
    G s p hs hp hp_top W R h hAtom

/--
The explicit restriction constant produced by the transmutation argument for
the indicator of a good-grid cell.
-/
noncomputable def souzaRestrictionMultiplierConstant
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (W : GoodGridCell G) (lam : ℝ) : ℝ :=
  (G.toWeakGridSpace.grid.Cmult1 : ℝ) *
    WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
      (WeakGridSpace.transmutationKernelZ lam (-(W.level : ℝ)) 1)

/--
The compactness hypothesis `A5` for Souza atoms is inherited by the grid
induced on any good-grid cell.
-/
theorem induced_souza_assumptionA5
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (W : GoodGridCell G) :
    WeakGridSpace.AssumptionA5
      (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
        (souzaAtomFamily G s p hs hp hp_top)) := by
  exact WeakGridSpace.inducedAtomFamily_assumptionA5
    (G := G.toWeakGridSpace)
    (Q := W.toLevelCell)
    (A := souzaAtomFamily G s p hs hp hp_top)
    (souza_assumptionA5 G s p hs hp hp_top)

/--
The mesh of the weak grid induced on a good-grid cell tends to zero.
-/
theorem induced_souza_hmesh
    (G : GoodGridSpace (α := α)) (W : GoodGridCell G) :
    Filter.Tendsto
      (fun k => sSup (Set.range fun Q : WeakGridSpace.LevelCell
        (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell) k =>
          ((WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure Q.1).toReal))
      Filter.atTop
      (nhds 0) := by
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let m : ℕ → ℝ := fun k =>
    sSup (Set.range fun Q : WeakGridSpace.LevelCell Wi k =>
      (Wi.measure Q.1).toReal)
  let ρ : ℝ := G.grid.lambda2
  let C : ℝ := (G.grid.μ W.cell).toReal
  have hρ_nonneg : 0 ≤ ρ := le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hρ_lt_one : ρ < 1 := G.grid.hlambda2_lt_one
  have hgeom_sum : Summable (fun k : ℕ => C * ρ ^ k) := by
    simpa [ρ, C, mul_comm, mul_left_comm, mul_assoc] using
      (summable_geometric_of_lt_one hρ_nonneg hρ_lt_one).mul_left C
  have hgeom_tendsto : Filter.Tendsto (fun k : ℕ => C * ρ ^ k) Filter.atTop (nhds 0) := by
    simpa [ρ, C] using hgeom_sum.tendsto_atTop_zero
  have hlower : (fun _ : ℕ => (0 : ℝ)) ≤ fun k => m k := by
    intro k
    dsimp [m]
    refine Real.sSup_nonneg ?_
    intro x hx
    rcases hx with ⟨Q, rfl⟩
    exact ENNReal.toReal_nonneg
  have hupper : (fun k => m k) ≤ fun k => C * ρ ^ k := by
    intro k
    dsimp [m]
    simpa [ρ, C, Wi, mul_comm, mul_left_comm, mul_assoc] using
      induced_levelMesh_le_geometric G W k
  simpa [m, Wi] using
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hgeom_tendsto hlower hupper

/--
Coefficient summability for the Souza weights on the weak grid induced by a
good-grid cell.
-/
theorem induced_souza_hCco
    (G : GoodGridSpace (α := α)) (W : GoodGridCell G)
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    WeakGridSpace.LpGridRepresentation.cCoefficientFinite p q
      (fun k => (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
        (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        s p p k) ^ p.toReal) := by
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let w : ℕ → ℝ := fun k =>
    WeakGridSpace.LpGridRepresentation.levelMeasureWeight Wi s p p k
  let C : ℝ := ((G.grid.μ W.cell).toReal) ^ s
  let ρ : ℝ := G.grid.lambda2 ^ s
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hmu_nonneg : 0 ≤ (G.grid.μ W.cell).toReal := ENNReal.toReal_nonneg
  have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
    le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hρ_nonneg : 0 ≤ ρ := Real.rpow_nonneg hlam_nonneg _
  have hρ_lt_one : ρ < 1 := by
    simpa [ρ] using Real.rpow_lt_one hlam_nonneg G.grid.hlambda2_lt_one hs
  have hC_nonneg : 0 ≤ C := Real.rpow_nonneg hmu_nonneg _
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg Wi s p p k
  have hw_bound : ∀ k, w k ≤ C * ρ ^ k := by
    intro k
    calc
      w k
          ≤ (G.grid.μ W.cell).toReal ^ s * (G.grid.lambda2 ^ k) ^ s := by
              simpa [w, Wi] using induced_levelMeasureWeight_le_geometric G W s p hs k
      _ = ((G.grid.μ W.cell).toReal) ^ s * (G.grid.lambda2 ^ s) ^ k := by
            congr 1
            calc
              (G.grid.lambda2 ^ k : ℝ) ^ s =
                  G.grid.lambda2 ^ ((k : ℝ) * s) := by
                    simpa [mul_comm] using
                      (Real.rpow_natCast_mul hlam_nonneg k s).symm
              _ = G.grid.lambda2 ^ (s * k) := by ring_nf
              _ = (G.grid.lambda2 ^ s) ^ k := by
                    simpa [mul_comm] using
                      (Real.rpow_mul_natCast hlam_nonneg s k)
      _ = C * ρ ^ k := by simp [C, ρ]
  have hgeom_sum : Summable (fun k : ℕ => C * ρ ^ k) := by
    simpa [C, ρ, mul_comm, mul_left_comm, mul_assoc] using
      (summable_geometric_of_lt_one hρ_nonneg hρ_lt_one).mul_left C
  have hsum_w : Summable w :=
    Summable.of_nonneg_of_le hw_nonneg hw_bound hgeom_sum
  have hroot : ∀ k, ((w k) ^ p.toReal) ^ (1 / p.toReal) = w k := by
    intro k
    simpa [one_div] using Real.rpow_rpow_inv (hw_nonneg k) hp_pos.ne'
  by_cases hq1 : q = 1
  · have hbdd : BddAbove (Set.range fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
      refine ⟨∑' k, w k, ?_⟩
      intro x hx
      rcases hx with ⟨k, rfl⟩
      change ((w k) ^ p.toReal) ^ (1 / p.toReal) ≤ ∑' k, w k
      rw [hroot k]
      simpa using sum_le_hasSum ({k} : Finset ℕ) (fun n _ => hw_nonneg n) hsum_w.hasSum
    simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, w, Wi] using hbdd
  · by_cases hqtop : q = ∞
    · have hsum_root : Summable (fun k => ((w k) ^ p.toReal) ^ (1 / p.toReal)) := by
        refine Summable.of_nonneg_of_le
          (fun k => by rw [hroot k]; exact hw_nonneg k)
          (fun k => by rw [hroot k]; exact hw_bound k)
          hgeom_sum
      simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, w, Wi] using
        hsum_root
    · let q' : ℝ≥0∞ := q / (q - 1)
      have hq_toReal_le : (1 : ℝ) ≤ q.toReal := by
        have h := ENNReal.toReal_mono hqtop (Fact.out : 1 ≤ q)
        simpa using h
      have hq_toReal_ne_one : q.toReal ≠ 1 := by
        intro hreal
        apply hq1
        exact ((ENNReal.toReal_eq_toReal_iff' ENNReal.one_ne_top hqtop).mp
          (by simp [hreal])).symm
      have hq_toReal_one : 1 < q.toReal :=
        lt_of_le_of_ne hq_toReal_le (Ne.symm hq_toReal_ne_one)
      have hq_conj : q'.toReal.HolderConjugate q.toReal := by
        simpa [q'] using
          WeakGridSpace.LpGridRepresentation.holderConjugate_q_div_qsub1_toReal
            (q := q) hq_toReal_one hqtop
      have hq'_pos : 0 < q'.toReal := by
        rw [Real.holderConjugate_iff] at hq_conj
        exact zero_lt_one.trans hq_conj.1
      have hsum_qgeom : Summable (fun k : ℕ => C ^ q'.toReal * (ρ ^ q'.toReal) ^ k) := by
        have hρq_nonneg : 0 ≤ ρ ^ q'.toReal := Real.rpow_nonneg hρ_nonneg _
        have hρq_lt_one : ρ ^ q'.toReal < 1 :=
          Real.rpow_lt_one hρ_nonneg hρ_lt_one hq'_pos
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (summable_geometric_of_lt_one hρq_nonneg hρq_lt_one).mul_left (C ^ q'.toReal)
      have hroot_pow : ∀ k,
          ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) = (w k) ^ q'.toReal := by
        intro k
        have hdiv : q'.toReal / p.toReal = (1 / p.toReal) * q'.toReal := by
          field_simp [hp_pos.ne']
        calc
          ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal)
              = ((w k) ^ p.toReal) ^ ((1 / p.toReal) * q'.toReal) := by rw [hdiv]
          _ = (((w k) ^ p.toReal) ^ (1 / p.toReal)) ^ q'.toReal := by
                rw [Real.rpow_mul (Real.rpow_nonneg (hw_nonneg k) _)]
          _ = (w k) ^ q'.toReal := by rw [hroot k]
      have hpow_geom : ∀ k, (ρ ^ k : ℝ) ^ q'.toReal = (ρ ^ q'.toReal) ^ k := by
        intro k
        calc
          (ρ ^ k : ℝ) ^ q'.toReal = ρ ^ ((k : ℝ) * q'.toReal) := by
              simpa [mul_comm] using
                (Real.rpow_natCast_mul hρ_nonneg k q'.toReal).symm
          _ = ρ ^ (q'.toReal * k) := by ring_nf
          _ = (ρ ^ q'.toReal) ^ k := by
              simpa [mul_comm] using
                (Real.rpow_mul_natCast hρ_nonneg q'.toReal k)
      have hle_q :
          (fun k => ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal)) ≤
            fun k => C ^ q'.toReal * (ρ ^ q'.toReal) ^ k := by
        intro k
        change ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) ≤
          C ^ q'.toReal * (ρ ^ q'.toReal) ^ k
        rw [hroot_pow k]
        calc
          (w k) ^ q'.toReal ≤ (C * ρ ^ k) ^ q'.toReal := by
            exact Real.rpow_le_rpow (hw_nonneg k) (hw_bound k) hq'_pos.le
          _ = C ^ q'.toReal * (ρ ^ k : ℝ) ^ q'.toReal := by
                rw [Real.mul_rpow hC_nonneg (pow_nonneg hρ_nonneg k)]
          _ = C ^ q'.toReal * (ρ ^ q'.toReal) ^ k := by rw [hpow_geom k]
      have hnonneg_q : ∀ k, 0 ≤ ((w k) ^ p.toReal) ^ (q'.toReal / p.toReal) := by
        intro k
        exact Real.rpow_nonneg (Real.rpow_nonneg (hw_nonneg k) _) _
      simpa [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, hq1, hqtop, q', w, Wi] using
        Summable.of_nonneg_of_le hnonneg_q hle_q hsum_qgeom

/--
The concrete `G2` package for Souza atoms on the weak grid induced by a
good-grid cell.
-/
theorem induced_souza_assumptionG2
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G) :
    WeakGridSpace.AssumptionG2
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
      s p ∞ q :=
  ⟨induced_souza_hCco G W s p q hs hp hp_top, induced_souza_hmesh G W⟩

/--
Constant multiples of induced good-grid cell indicators belong to the induced
Souza Besov-ish space.
-/
theorem indicatorConstLp_inducedCell_mem_inducedSouzaBesov
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Q : GoodGridCell G)
    {i : ℕ}
    (P : WeakGridSpace.LevelCell
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell) i)
    (c : ℂ) :
    MeasureTheory.indicatorConstLp
        (μ := (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure)
        p
        ((WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).grid.measurable
          i P.1 P.2)
        (by
          letI : MeasureTheory.IsFiniteMeasure
              (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure :=
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).grid.isFinite
          exact MeasureTheory.measure_ne_top
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure P.1)
        c
      ∈ WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q := by
  classical
  let W := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  let A := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
    (souzaAtomFamily G s p hs hp hp_top)
  let Pg : WeakGridSpace.WeakGridCell W := WeakGridSpace.levelCellToWeakGridCell W i P
  let r : WeakGridSpace.LevelCell W i → ℝ := fun S =>
    (W.measure S.1).toReal ^ (s - (p.toReal)⁻¹)
  have hr_nonneg : ∀ S, 0 ≤ r S := by
    intro S
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hPfinite : W.measure P.1 ≠ ∞ := by
    letI : MeasureTheory.IsFiniteMeasure W.measure := W.grid.isFinite
    exact MeasureTheory.measure_ne_top W.measure P.1
  have hP_pos : 0 < W.measure P.1 :=
    W.grid.positive_measure i P.1 P.2
  have hrP_pos : 0 < r P := by
    have hPtoReal_pos : 0 < (W.measure P.1).toReal :=
      ENNReal.toReal_pos hP_pos.ne' hPfinite
    exact Real.rpow_pos_of_pos hPtoReal_pos _
  let B : WeakGridSpace.LevelBlock A i :=
    { coeff := fun S => if S = P then c / (r P : ℂ) else 0
      atom := fun S => ((r S : ℝ) : ℂ)
      atom_mem := by
        intro S
        change ‖(((r S : ℝ) : ℂ))‖ ≤
          (G.grid.μ S.1).toReal ^ (s - (p.toReal)⁻¹)
        have hmeasure :
            W.measure S.1 = G.grid.μ S.1 := rfl
        have hnorm : ‖(((r S : ℝ) : ℂ))‖ = r S := by
          simp [Complex.norm_real, Real.norm_of_nonneg (hr_nonneg S)]
        rw [hnorm]
        simp [r, W, hmeasure] }
  have hB_toLp :
      B.toLp A =
        MeasureTheory.indicatorConstLp
          (μ := W.measure) p
          (W.grid.measurable i P.1 P.2)
          hPfinite c := by
    apply MeasureTheory.Lp.ext
    refine (WeakGridSpace.LevelBlock.coeFn_toLp A B).trans ?_
    have hpoint :
        B.toFunLt A =ᵐ[W.measure] P.1.indicator (fun _ => c) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hx : x ∈ P.1
      · have hsum :
          B.toFunLt A x =
            B.coeff P *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell W i P)
                (B.atom P) x := by
          unfold WeakGridSpace.LevelBlock.toFunLt
          exact Finset.sum_eq_single P
            (by
              intro S _ hS
              have hSP : S ≠ P := hS
              simp [B, hSP])
            (by intro hnot; exact False.elim (hnot (by simp)))
        rw [hsum]
        rw [Set.indicator_of_mem hx]
        simp only [A, B, W, WeakGridSpace.AtomFamily.toFunction,
          WeakGridSpace.inducedAtomFamily, WeakGridSpace.inducedWeakGridCellToAmbient,
          WeakGridSpace.levelCellToWeakGridCell, souzaAtomFamily, souzaLocalVectorSpace]
        change c / (r P : ℂ) * (P.1.indicator (fun _ => (r P : ℂ)) x) = c
        rw [Set.indicator_of_mem hx]
        field_simp [show (r P : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt hrP_pos)]
      · have hsum :
          B.toFunLt A x = 0 := by
          unfold WeakGridSpace.LevelBlock.toFunLt
          refine Finset.sum_eq_zero ?_
          intro S _hS
          by_cases hSP : S = P
          · subst S
            simp only [A, B, WeakGridSpace.AtomFamily.toFunction,
              WeakGridSpace.inducedAtomFamily, WeakGridSpace.inducedWeakGridCellToAmbient,
              WeakGridSpace.levelCellToWeakGridCell, souzaAtomFamily, souzaLocalVectorSpace]
            change c / (r P : ℂ) * (P.1.indicator (fun _ => (r P : ℂ)) x) = 0
            rw [Set.indicator_of_notMem hx]
            simp
          · simp [B, hSP]
        rw [hsum]
        simp [hx]
    exact hpoint.trans
      (MeasureTheory.indicatorConstLp_coeFn (μ := W.measure)
        (p := p) (hs := W.grid.measurable i P.1 P.2)
        (hμs := hPfinite) (c := c)).symm
  simpa [A, W, hB_toLp] using
    WeakGridSpace.levelBlock_toLp_mem_besovish (A := A) (q := q) B

/--
Constant multiples of the root cell of an induced good grid belong to the
induced Souza Besov-ish space.
-/
theorem indicatorConstLp_inducedRoot_mem_inducedSouzaBesov
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G) (c : ℂ) :
    MeasureTheory.indicatorConstLp
        (μ := (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure)
        p
        ((WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).grid.measurable
          0 (W.inducedRootLevelCell).1 (W.inducedRootLevelCell).2)
        (by
          letI : MeasureTheory.IsFiniteMeasure
              (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure :=
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).grid.isFinite
          exact MeasureTheory.measure_ne_top
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure
            (W.inducedRootLevelCell).1)
        c
      ∈ WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q := by
  exact indicatorConstLp_inducedCell_mem_inducedSouzaBesov
    G s p q hs hp hp_top W W.inducedRootLevelCell c

/--
Constant multiples of a descendant cell `Q ⊆ W`, viewed inside the grid
induced on `W`, belong to the induced Souza Besov-ish space.
-/
theorem indicatorConstLp_descendant_mem_inducedSouzaBesov
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W Q : GoodGridCell G)
    (hlevel : W.level ≤ Q.level) (hsub : Q.cell ⊆ W.cell)
    (c : ℂ) :
    MeasureTheory.indicatorConstLp
        (μ := (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure)
        p
        ((WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).grid.measurable
          (Q.level - W.level)
          (W.toInducedLevelCellOfSubset Q hlevel hsub).1
          (W.toInducedLevelCellOfSubset Q hlevel hsub).2)
        (by
          letI : MeasureTheory.IsFiniteMeasure
              (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure :=
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).grid.isFinite
          exact MeasureTheory.measure_ne_top
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure
            (W.toInducedLevelCellOfSubset Q hlevel hsub).1)
        c
      ∈ WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q := by
  exact indicatorConstLp_inducedCell_mem_inducedSouzaBesov
    G s p q hs hp hp_top W (W.toInducedLevelCellOfSubset Q hlevel hsub) c

/--
The restriction of a canonical Souza atom to a good-grid cell is represented by
an element of the Souza Besov-ish space on the induced grid.

This formalizes the three local cases in the proof of the restriction lemma:
`Q ⊆ W`, `W ⊆ Q`, and `Q ∩ W = ∅`.
-/
theorem restrict_canonicalSouzaAtom_mem_inducedSouzaBesov
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W Q : GoodGridCell G) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsFunction
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
          canonicalSouzaAtom G s p Q x)
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) := by
  classical
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
    (souzaAtomFamily G s p hs hp hp_top)
  let cQ : ℂ := (((G.grid.μ Q.cell).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)
  rcases le_total W.level Q.level with hWQ | hQW
  · rcases W.subset_or_disjoint_of_le Q hWQ with hsub | hdisj
    · let P := W.toInducedLevelCellOfSubset Q hWQ hsub
      let yLp : Lp ℂ p Wi.measure :=
        MeasureTheory.indicatorConstLp
          (μ := Wi.measure) p
          (Wi.grid.measurable (Q.level - W.level) P.1 P.2)
          (by
            letI : MeasureTheory.IsFiniteMeasure Wi.measure := Wi.grid.isFinite
            exact MeasureTheory.measure_ne_top Wi.measure P.1)
          cQ
      have hy_mem : yLp ∈ WeakGridSpace.BesovishSpace Ai q := by
        simpa [Wi, Ai, P, cQ] using
          indicatorConstLp_descendant_mem_inducedSouzaBesov
            G s p q hs hp hp_top W Q hWQ hsub cQ
      refine ⟨⟨yLp, hy_mem⟩, ?_⟩
      have hycoe :
          ((yLp : Lp ℂ p Wi.measure) : α → ℂ) =ᵐ[Wi.measure]
            P.1.indicator (fun _ => cQ) :=
        MeasureTheory.indicatorConstLp_coeFn
          (μ := Wi.measure) (p := p)
          (hs := Wi.grid.measurable (Q.level - W.level) P.1 P.2)
          (hμs := by
            letI : MeasureTheory.IsFiniteMeasure Wi.measure := Wi.grid.isFinite
            exact MeasureTheory.measure_ne_top Wi.measure P.1)
          (c := cQ)
      refine hycoe.trans (Filter.Eventually.of_forall ?_)
      intro x
      have hprod :=
        congrFun (indicator_mul_canonicalSouzaAtom_eq_self_of_subset W Q s p hsub) x
      change P.1.indicator (fun _ => cQ) x =
        W.cell.indicator (fun _ => (1 : ℂ)) x * canonicalSouzaAtom G s p Q x
      rw [hprod]
      by_cases hxQ : x ∈ Q.cell
      · simp [P, GoodGridCell.toInducedLevelCellOfSubset,
          WeakGridSpace.ambientLevelCellToInduced, cQ, canonicalSouzaAtom, hxQ]
      · simp [P, GoodGridCell.toInducedLevelCellOfSubset,
          WeakGridSpace.ambientLevelCellToInduced, cQ, canonicalSouzaAtom, hxQ]
    · refine ⟨0, ?_⟩
      rw [indicator_mul_canonicalSouzaAtom_eq_zero_of_disjoint W Q s p hdisj]
      simpa [WeakGridSpace.RepresentsFunction] using
        (MeasureTheory.Lp.coeFn_zero ℂ p Wi.measure)
  · rcases Q.subset_or_disjoint_of_le W hQW with hsub | hdisj
    · let P := W.inducedRootLevelCell
      let yLp : Lp ℂ p Wi.measure :=
        MeasureTheory.indicatorConstLp
          (μ := Wi.measure) p
          (Wi.grid.measurable 0 P.1 P.2)
          (by
            letI : MeasureTheory.IsFiniteMeasure Wi.measure := Wi.grid.isFinite
            exact MeasureTheory.measure_ne_top Wi.measure P.1)
          cQ
      have hy_mem : yLp ∈ WeakGridSpace.BesovishSpace Ai q := by
        simpa [Wi, Ai, P, cQ] using
          indicatorConstLp_inducedRoot_mem_inducedSouzaBesov
            G s p q hs hp hp_top W cQ
      refine ⟨⟨yLp, hy_mem⟩, ?_⟩
      have hycoe :
          ((yLp : Lp ℂ p Wi.measure) : α → ℂ) =ᵐ[Wi.measure]
            P.1.indicator (fun _ => cQ) :=
        MeasureTheory.indicatorConstLp_coeFn
          (μ := Wi.measure) (p := p)
          (hs := Wi.grid.measurable 0 P.1 P.2)
          (hμs := by
            letI : MeasureTheory.IsFiniteMeasure Wi.measure := Wi.grid.isFinite
            exact MeasureTheory.measure_ne_top Wi.measure P.1)
          (c := cQ)
      refine hycoe.trans (Filter.Eventually.of_forall ?_)
      intro x
      have hprod :=
        congrFun (indicator_mul_canonicalSouzaAtom_eq_indicator_of_superset W Q s p hsub) x
      change P.1.indicator (fun _ => cQ) x =
        W.cell.indicator (fun _ => (1 : ℂ)) x * canonicalSouzaAtom G s p Q x
      rw [hprod]
      simp [P, GoodGridCell.inducedRootLevelCell, cQ]
    · refine ⟨0, ?_⟩
      rw [indicator_mul_canonicalSouzaAtom_eq_zero_of_disjoint W Q s p hdisj.symm]
      simpa [WeakGridSpace.RepresentsFunction] using
        (MeasureTheory.Lp.coeFn_zero ℂ p Wi.measure)

/--
Restricting an arbitrary Souza local atom coefficient on `Q` to a good-grid
cell `W` is represented by an element of the Souza Besov-ish space on the grid
induced on `W`.

The coefficient `c` is not required to satisfy the Souza atom bound here: it is
absorbed as the Besov coefficient of one induced Souza atom.
-/
theorem restrict_souzaAtomCoeff_mem_inducedSouzaBesov
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W Q : GoodGridCell G) (c : ℂ) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsFunction
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
          Q.cell.indicator (fun _ => c) x)
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) := by
  classical
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
    (souzaAtomFamily G s p hs hp hp_top)
  rcases le_total W.level Q.level with hWQ | hQW
  · rcases W.subset_or_disjoint_of_le Q hWQ with hsub | hdisj
    · let P := W.toInducedLevelCellOfSubset Q hWQ hsub
      let yLp : Lp ℂ p Wi.measure :=
        MeasureTheory.indicatorConstLp
          (μ := Wi.measure) p
          (Wi.grid.measurable (Q.level - W.level) P.1 P.2)
          (by
            letI : MeasureTheory.IsFiniteMeasure Wi.measure := Wi.grid.isFinite
            exact MeasureTheory.measure_ne_top Wi.measure P.1)
          c
      have hy_mem : yLp ∈ WeakGridSpace.BesovishSpace Ai q := by
        simpa [Wi, Ai, P] using
          indicatorConstLp_descendant_mem_inducedSouzaBesov
            G s p q hs hp hp_top W Q hWQ hsub c
      refine ⟨⟨yLp, hy_mem⟩, ?_⟩
      have hycoe :
          ((yLp : Lp ℂ p Wi.measure) : α → ℂ) =ᵐ[Wi.measure]
            P.1.indicator (fun _ => c) :=
        MeasureTheory.indicatorConstLp_coeFn
          (μ := Wi.measure) (p := p)
          (hs := Wi.grid.measurable (Q.level - W.level) P.1 P.2)
          (hμs := by
            letI : MeasureTheory.IsFiniteMeasure Wi.measure := Wi.grid.isFinite
            exact MeasureTheory.measure_ne_top Wi.measure P.1)
          (c := c)
      refine hycoe.trans (Filter.Eventually.of_forall ?_)
      intro x
      have hprod :=
        congrFun (indicator_mul_cellIndicator_eq_self_of_subset W Q c hsub) x
      change P.1.indicator (fun _ => c) x =
        W.cell.indicator (fun _ => (1 : ℂ)) x * Q.cell.indicator (fun _ => c) x
      rw [hprod]
      by_cases hxQ : x ∈ Q.cell
      · simp [P, GoodGridCell.toInducedLevelCellOfSubset,
          WeakGridSpace.ambientLevelCellToInduced, hxQ]
      · simp [P, GoodGridCell.toInducedLevelCellOfSubset,
          WeakGridSpace.ambientLevelCellToInduced, hxQ]
    · refine ⟨0, ?_⟩
      rw [indicator_mul_cellIndicator_eq_zero_of_disjoint W Q c hdisj]
      simpa [WeakGridSpace.RepresentsFunction] using
        (MeasureTheory.Lp.coeFn_zero ℂ p Wi.measure)
  · rcases Q.subset_or_disjoint_of_le W hQW with hsub | hdisj
    · let P := W.inducedRootLevelCell
      let yLp : Lp ℂ p Wi.measure :=
        MeasureTheory.indicatorConstLp
          (μ := Wi.measure) p
          (Wi.grid.measurable 0 P.1 P.2)
          (by
            letI : MeasureTheory.IsFiniteMeasure Wi.measure := Wi.grid.isFinite
            exact MeasureTheory.measure_ne_top Wi.measure P.1)
          c
      have hy_mem : yLp ∈ WeakGridSpace.BesovishSpace Ai q := by
        simpa [Wi, Ai, P] using
          indicatorConstLp_inducedRoot_mem_inducedSouzaBesov
            G s p q hs hp hp_top W c
      refine ⟨⟨yLp, hy_mem⟩, ?_⟩
      have hycoe :
          ((yLp : Lp ℂ p Wi.measure) : α → ℂ) =ᵐ[Wi.measure]
            P.1.indicator (fun _ => c) :=
        MeasureTheory.indicatorConstLp_coeFn
          (μ := Wi.measure) (p := p)
          (hs := Wi.grid.measurable 0 P.1 P.2)
          (hμs := by
            letI : MeasureTheory.IsFiniteMeasure Wi.measure := Wi.grid.isFinite
            exact MeasureTheory.measure_ne_top Wi.measure P.1)
          (c := c)
      refine hycoe.trans (Filter.Eventually.of_forall ?_)
      intro x
      have hprod :=
        congrFun (indicator_mul_cellIndicator_eq_indicator_of_superset W Q c hsub) x
      change P.1.indicator (fun _ => c) x =
        W.cell.indicator (fun _ => (1 : ℂ)) x * Q.cell.indicator (fun _ => c) x
      rw [hprod]
      simp [P, GoodGridCell.inducedRootLevelCell]
    · refine ⟨0, ?_⟩
      rw [indicator_mul_cellIndicator_eq_zero_of_disjoint W Q c hdisj.symm]
      simpa [WeakGridSpace.RepresentsFunction] using
        (MeasureTheory.Lp.coeFn_zero ℂ p Wi.measure)

/--
The same restriction result, phrased with the `AtomFamily.toFunction` of the
Souza atom family. This is the form used by level blocks.
-/
theorem restrict_souzaAtomFamily_toFunction_mem_inducedSouzaBesov
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W Q : GoodGridCell G) (c : ℂ) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsFunction
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
          (souzaAtomFamily G s p hs hp hp_top).toFunction Q.toWeakGridCell c x)
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) := by
  simpa [WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily, souzaLocalVectorSpace] using
    restrict_souzaAtomCoeff_mem_inducedSouzaBesov
      G s p q hs hp hp_top W Q c

/--
Restricting one Souza level block to a good-grid cell is represented in the
Souza Besov-ish space on the induced grid.
-/
theorem restrict_souzaLevelBlock_mem_inducedSouzaBesov
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G) {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        (B.toLp (souzaAtomFamily G s p hs hp hp_top) :
          Lp ℂ p G.toWeakGridSpace.measure)
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell A
  let S := (G.toWeakGridSpace.grid.partitions k).attach
  let goodCellOfLevel (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
      GoodGridCell G := ⟨k, Q.1, Q.2⟩
  let yAtom :
      (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) →
        WeakGridSpace.BesovishSpace Ai q := fun Q =>
    Classical.choose
      (restrict_souzaAtomFamily_toFunction_mem_inducedSouzaBesov
        G s p q hs hp hp_top W (goodCellOfLevel Q) (B.atom Q))
  have hyAtom :
      ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        WeakGridSpace.RepresentsFunction
          (G := Wi) (p := p)
          (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
            A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (B.atom Q) x)
          (yAtom Q : Lp ℂ p Wi.measure) := by
    intro Q
    simpa [A, Wi, Ai, goodCellOfLevel, GoodGridCell.toWeakGridCell] using
      (Classical.choose_spec
        (restrict_souzaAtomFamily_toFunction_mem_inducedSouzaBesov
          G s p q hs hp hp_top W (goodCellOfLevel Q) (B.atom Q)))
  let yLp : Lp ℂ p Wi.measure :=
    ∑ Q ∈ S, B.coeff Q • (yAtom Q : Lp ℂ p Wi.measure)
  have yLp_mem : yLp ∈ WeakGridSpace.BesovishSpace Ai q := by
    unfold yLp
    exact Submodule.sum_mem _ fun Q _hQ =>
      Submodule.smul_mem _ (B.coeff Q) (yAtom Q).property
  let y : WeakGridSpace.BesovishSpace Ai q := ⟨yLp, yLp_mem⟩
  refine ⟨y, ?_⟩
  have hsum_rep :
      WeakGridSpace.RepresentsFunction
        (G := Wi) (p := p)
        (fun x => ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x))
        (y : Lp ℂ p Wi.measure) := by
    unfold y yLp
    refine WeakGridSpace.representsFunction_finset_sum
      (G := Wi) (p := p) S
      (fun Q x =>
        B.coeff Q *
          (W.cell.indicator (fun _ => (1 : ℂ)) x *
            A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (B.atom Q) x))
      (fun Q => (B.coeff Q) • (yAtom Q : Lp ℂ p Wi.measure)) ?_
    intro Q _hQ
    exact WeakGridSpace.representsFunction_smul (G := Wi) (p := p)
      (B.coeff Q) (hyAtom Q)
  have hsum_point :
      (fun x => ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x))
        = fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
          B.toFunLt A x := by
    funext x
    calc
      ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x)
        = ∑ Q ∈ S,
            W.cell.indicator (fun _ => (1 : ℂ)) x *
              (B.coeff Q *
                A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                  (B.atom Q) x) := by
            refine Finset.sum_congr rfl ?_
            intro Q _hQ
            ring
      _ = W.cell.indicator (fun _ => (1 : ℂ)) x *
          (∑ Q ∈ S,
            B.coeff Q *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x) := by
            rw [Finset.mul_sum]
      _ = W.cell.indicator (fun _ => (1 : ℂ)) x *
          B.toFunLt A x := by
            simp [S, WeakGridSpace.LevelBlock.toFunLt]
  have hblock :
      (B.toLp A : α → ℂ) =ᵐ[Wi.measure] B.toFunLt A := by
    simpa [A, Wi, GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid] using
      (WeakGridSpace.LevelBlock.coeFn_toLp A B)
  have hsum_to_fun :
      (fun x => ∑ Q ∈ S,
          B.coeff Q *
            (W.cell.indicator (fun _ => (1 : ℂ)) x *
              A.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
                (B.atom Q) x))
        =ᵐ[Wi.measure] fun x =>
          W.cell.indicator (fun _ => (1 : ℂ)) x * B.toFunLt A x := by
    exact Filter.Eventually.of_forall fun x => by
      rw [hsum_point]
  have hfun_to_lp :
      (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x * B.toFunLt A x)
        =ᵐ[Wi.measure] fun x =>
          W.cell.indicator (fun _ => (1 : ℂ)) x * (B.toLp A : α → ℂ) x :=
    hblock.mono fun x hx => by
      change W.cell.indicator (fun _ => (1 : ℂ)) x * B.toFunLt A x =
        W.cell.indicator (fun _ => (1 : ℂ)) x * (B.toLp A : α → ℂ) x
      rw [← hx]
  exact hsum_rep.trans (hsum_to_fun.trans hfun_to_lp)

/--
Restricting a finite sum of Souza level blocks to a good-grid cell is
represented in the Souza Besov-ish space on the induced grid.
-/
theorem restrict_souzaFiniteLevelBlocks_mem_inducedSouzaBesov
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G) (T : Finset ℕ)
    (B : ∀ k : ℕ,
      WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        ((∑ k ∈ T, (B k).toLp (souzaAtomFamily G s p hs hp hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure)
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell A
  let yBlock : (k : ℕ) → WeakGridSpace.BesovishSpace Ai q := fun k =>
    Classical.choose
      (restrict_souzaLevelBlock_mem_inducedSouzaBesov
        G s p q hs hp hp_top W (B k))
  have hyBlock :
      ∀ k : ℕ,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := Wi) (p := p)
          (W.cell.indicator fun _ => (1 : ℂ))
          (((B k).toLp A : Lp ℂ p G.toWeakGridSpace.measure) :
            Lp ℂ p Wi.measure)
          (yBlock k : Lp ℂ p Wi.measure) := by
    intro k
    simpa [A, Wi, Ai] using
      (Classical.choose_spec
        (restrict_souzaLevelBlock_mem_inducedSouzaBesov
          G s p q hs hp hp_top W (B k)))
  let yLp : Lp ℂ p Wi.measure :=
    ∑ k ∈ T, (yBlock k : Lp ℂ p Wi.measure)
  have yLp_mem : yLp ∈ WeakGridSpace.BesovishSpace Ai q := by
    unfold yLp
    exact Submodule.sum_mem _ fun k _hk => (yBlock k).property
  let y : WeakGridSpace.BesovishSpace Ai q := ⟨yLp, yLp_mem⟩
  let xSum : Lp ℂ p Wi.measure :=
    ∑ k ∈ T, (((B k).toLp A : Lp ℂ p G.toWeakGridSpace.measure) :
      Lp ℂ p Wi.measure)
  refine ⟨y, ?_⟩
  have hy_sum :
      WeakGridSpace.RepresentsFunction
        (G := Wi) (p := p)
        (fun x => ∑ k ∈ T,
          W.cell.indicator (fun _ => (1 : ℂ)) x *
            ((B k).toLp A : α → ℂ) x)
        (y : Lp ℂ p Wi.measure) := by
    unfold y yLp
    refine WeakGridSpace.representsFunction_finset_sum
      (G := Wi) (p := p) T
      (fun k x => W.cell.indicator (fun _ => (1 : ℂ)) x *
        ((B k).toLp A : α → ℂ) x)
      (fun k => (yBlock k : Lp ℂ p Wi.measure)) ?_
    intro k _hk
    exact hyBlock k
  have hblocks_sum :
      WeakGridSpace.RepresentsFunction
        (G := Wi) (p := p)
        (fun x => ∑ k ∈ T, ((B k).toLp A : α → ℂ) x)
        xSum := by
    unfold xSum
    refine WeakGridSpace.representsFunction_finset_sum
      (G := Wi) (p := p) T
      (fun k x => ((B k).toLp A : α → ℂ) x)
      (fun k => (((B k).toLp A : Lp ℂ p G.toWeakGridSpace.measure) :
        Lp ℂ p Wi.measure)) ?_
    intro k _hk
    exact Filter.EventuallyEq.rfl
  have hsum_point :
      (fun x => ∑ k ∈ T,
          W.cell.indicator (fun _ => (1 : ℂ)) x *
            ((B k).toLp A : α → ℂ) x)
        = fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
          (∑ k ∈ T, ((B k).toLp A : α → ℂ) x) := by
    funext x
    rw [Finset.mul_sum]
  have hprod_sum :
      (fun x => W.cell.indicator (fun _ => (1 : ℂ)) x *
          (∑ k ∈ T, ((B k).toLp A : α → ℂ) x))
        =ᵐ[Wi.measure] fun x =>
          W.cell.indicator (fun _ => (1 : ℂ)) x * (xSum : α → ℂ) x :=
    hblocks_sum.mono fun x hx => by
      simpa using
        congrArg (fun z : ℂ => W.cell.indicator (fun _ => (1 : ℂ)) x * z) hx.symm
  have hsum_point_ae :
      (fun x => ∑ k ∈ T,
          W.cell.indicator (fun _ => (1 : ℂ)) x *
            ((B k).toLp A : α → ℂ) x)
        =ᵐ[Wi.measure] fun x =>
          W.cell.indicator (fun _ => (1 : ℂ)) x *
            (∑ k ∈ T, ((B k).toLp A : α → ℂ) x) :=
    Filter.Eventually.of_forall fun x => by
      rw [hsum_point]
  change ((y : Lp ℂ p Wi.measure) : α → ℂ) =ᵐ[Wi.measure] fun x =>
    W.cell.indicator (fun _ => (1 : ℂ)) x * (xSum : α → ℂ) x
  exact hy_sum.trans (hsum_point_ae.trans hprod_sum)

/--
Restricting the initial segment of a Souza atomic representation is represented
in the Souza Besov-ish space on the induced grid.
-/
theorem restrict_souzaInitialSegment_mem_inducedSouzaBesov
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (N : ℕ) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        ((∑ k ∈ Finset.range N,
            (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure)
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) := by
  exact restrict_souzaFiniteLevelBlocks_mem_inducedSouzaBesov
    G s p q hs hp hp_top W (Finset.range N) R.block

/--
Choose representatives for all restricted initial segments of a Souza
representation.
-/
theorem restrict_souzaInitialSegments_representatives
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g) :
    ∃ yseq : ℕ → WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      ∀ N,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p)
          (W.cell.indicator fun _ => (1 : ℂ))
          ((∑ k ∈ Finset.range N,
              (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) :
            Lp ℂ p G.toWeakGridSpace.measure)
          (yseq N : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) := by
  classical
  let yseq : ℕ → WeakGridSpace.BesovishSpace
      (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
        (souzaAtomFamily G s p hs hp hp_top)) q := fun N =>
    Classical.choose
      (restrict_souzaInitialSegment_mem_inducedSouzaBesov
        G s p q hs hp hp_top W R N)
  refine ⟨yseq, ?_⟩
  intro N
  exact Classical.choose_spec
    (restrict_souzaInitialSegment_mem_inducedSouzaBesov
      G s p q hs hp hp_top W R N)

/--
If the induced representatives of the restricted initial segments converge in
`L^p`, then their limit represents the restriction of the represented function.

This isolates the remaining analytic task in the restriction lemma: prove
convergence/Cauchy estimates for the induced representatives.
-/
theorem restrict_souzaRepresentation_of_tendsto_initialSegments
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (yseq : ℕ → WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q)
    (y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q)
    (hprod : ∀ N,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        ((∑ k ∈ Finset.range N,
            (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure)
        (yseq N : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure))
    (hy :
      Filter.Tendsto
        (fun N => (yseq N : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure))
        Filter.atTop
        (𝓝 (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure))) :
    WeakGridSpace.RepresentsPointwiseProduct
      (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
      (p := p)
      (W.cell.indicator fun _ => (1 : ℂ))
      (g : Lp ℂ p G.toWeakGridSpace.measure)
      (y : Lp ℂ p
        (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) := by
  classical
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let A := souzaAtomFamily G s p hs hp hp_top
  let partialSum : ℕ → Lp ℂ p Wi.measure := fun N =>
    ((∑ k ∈ Finset.range N, (R.block k).toLp A) :
      Lp ℂ p G.toWeakGridSpace.measure)
  have hx :
      Filter.Tendsto partialSum Filter.atTop (𝓝 (g : Lp ℂ p Wi.measure)) := by
    simpa [partialSum, A, Wi, WeakGridSpace.inducedWeakGridSpace,
      WeakGridSpace.inducedWeakGrid, WeakGridSpace.WeakGridSpace.measure] using
      R.hasSum.tendsto_sum_nat
  exact WeakGridSpace.RepresentsPointwiseProduct.of_tendsto_Lp
    (G := Wi) (p := p)
    (m := W.cell.indicator fun _ => (1 : ℂ))
    (xseq := partialSum)
    (yseq := fun N => (yseq N : Lp ℂ p Wi.measure))
    (x := (g : Lp ℂ p Wi.measure))
    (y := (y : Lp ℂ p Wi.measure))
    hx hy (by
      intro N
      simpa [partialSum, A, Wi] using hprod N)

/--
If the chosen restricted initial-segment representatives are Cauchy in the
induced Besov coefficient-cost gauge, then the full restricted function has an
induced Souza Besov-ish representative.

The hypotheses `hG2ind` and `hA5ind` are the induced-grid completeness
assumptions; proving them from the ambient good-grid Souza assumptions is the
remaining geometric compactness step.
-/
theorem restrict_souzaRepresentation_of_cauchy_initialSegments
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (yseq : ℕ → WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q)
    (hprod : ∀ N,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        ((∑ k ∈ Finset.range N,
            (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure)
        (yseq N : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure))
    (hG2ind : WeakGridSpace.AssumptionG2
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
      s p ∞ q)
    (hA5ind : WeakGridSpace.AssumptionA5
      (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
        (souzaAtomFamily G s p hs hp hp_top)))
    (hcauchy : ∀ η > 0, ∃ N₀, ∀ M ≥ N₀, ∀ N ≥ N₀,
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q
        (yseq N - yseq M) < η) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        (g : Lp ℂ p G.toWeakGridSpace.measure)
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
      ∀ η > 0, ∃ N₀, ∀ N ≥ N₀,
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q
          (y - yseq N) < η := by
  classical
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let Ai : WeakGridSpace.AtomFamily Wi s p ∞ :=
    WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
      (souzaAtomFamily G s p hs hp hp_top)
  haveI : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  rcases WeakGridSpace.besovishSpace_Norm_Costpq_cauchySeq_tendsto
      (G := Wi) (s := s) (p := p) (u := ∞) (q := q)
      hp_top hs le_top Ai (by simpa [Wi] using hG2ind)
      (by simpa [Wi, Ai] using hA5ind) (by simpa [Wi, Ai] using yseq)
      (by simpa [Wi, Ai] using hcauchy) with
    ⟨y, hycost⟩
  let zseq : ℕ → WeakGridSpace.BesovishSpace Ai q := fun N => y - yseq N
  have hz_cost : ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
      WeakGridSpace.BesovishSpace.Norm_Costpq Ai q (zseq N) < ε := by
    intro ε hε
    simpa [zseq, Ai] using hycost ε hε
  have hz_Lp :
      Filter.Tendsto
        (fun N => (zseq N : Lp ℂ p Wi.measure))
        Filter.atTop
        (𝓝 (0 : Lp ℂ p Wi.measure)) :=
    WeakGridSpace.BesovishSpace.tendsto_Lp_zero_of_tendsto_Norm_Costpq_zero
      (G := Wi) (s := s) (p := p) (u := ∞) (q := q)
      (A := Ai) hp_top hG2ind.1 zseq hz_cost
  have hy_Lp :
      Filter.Tendsto
        (fun N => (yseq N : Lp ℂ p Wi.measure))
        Filter.atTop
        (𝓝 (y : Lp ℂ p Wi.measure)) := by
    have h :=
      (tendsto_const_nhds (x := (y : Lp ℂ p Wi.measure))).sub hz_Lp
    simpa [zseq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  refine ⟨y, ?_, hycost⟩
  exact restrict_souzaRepresentation_of_tendsto_initialSegments
    G s p q hs hp hp_top W R yseq y hprod hy_Lp

/--
Bounded Cauchy products of restricted initial Souza segments converge to a
restricted Souza-Besov representative with the same cost bound.
-/
theorem restrict_souzaRepresentation_of_cauchy_initialSegments_bound
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (yseq : ℕ → WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q)
    (hprod : ∀ N,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        ((∑ k ∈ Finset.range N,
            (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure)
        (yseq N : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure))
    (hG2ind : WeakGridSpace.AssumptionG2
      (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
      s p ∞ q)
    (hA5ind : WeakGridSpace.AssumptionA5
      (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
        (souzaAtomFamily G s p hs hp hp_top)))
    {C : ℝ}
    (hbound : ∀ N,
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q (yseq N) ≤ C)
    (hcauchy : ∀ η > 0, ∃ N₀, ∀ M ≥ N₀, ∀ N ≥ N₀,
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q
        (yseq N - yseq M) < η) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        (g : Lp ℂ p G.toWeakGridSpace.measure)
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q y ≤ C := by
  classical
  rcases restrict_souzaRepresentation_of_cauchy_initialSegments
      G s p q hs hp hp_top W R yseq hprod hG2ind hA5ind hcauchy with
    ⟨y, hyprod, hycost⟩
  refine ⟨y, hyprod, ?_⟩
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let Ai : WeakGridSpace.AtomFamily Wi s p ∞ :=
    WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
      (souzaAtomFamily G s p hs hp hp_top)
  exact WeakGridSpace.BesovishSpace.Norm_Costpq_le_of_tendsto_Norm_Costpq
    (G := Wi) (s := s) (p := p) (u := ∞) (q := q) (A := Ai)
    hp_top
    (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := Ai) q)
    (by simpa [Wi, Ai] using hbound)
    (by simpa [Wi, Ai] using hycost)

/--
Souza-specialized version of
`restrict_souzaRepresentation_of_cauchy_initialSegments`: the induced `G2` and
`A5` assumptions are supplied automatically by the good-grid Souza structure.
-/
theorem restrict_souzaRepresentation_of_cauchy_initialSegments_souza
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (yseq : ℕ → WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q)
    (hprod : ∀ N,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        ((∑ k ∈ Finset.range N,
            (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure)
        (yseq N : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure))
    (hcauchy : ∀ η > 0, ∃ N₀, ∀ M ≥ N₀, ∀ N ≥ N₀,
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q
        (yseq N - yseq M) < η) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        (g : Lp ℂ p G.toWeakGridSpace.measure)
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
      ∀ η > 0, ∃ N₀, ∀ N ≥ N₀,
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q
          (y - yseq N) < η :=
  restrict_souzaRepresentation_of_cauchy_initialSegments
    G s p q hs hp hp_top W R yseq hprod
    (induced_souza_assumptionG2 G s p q hs hp hp_top W)
    (induced_souza_assumptionA5 G s p hs hp hp_top W)
    hcauchy

/--
Bounded Cauchy restricted initial Souza segments converge with the same bound;
the induced structural hypotheses are automatic.
-/
theorem restrict_souzaRepresentation_of_cauchy_initialSegments_bound_souza
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) g)
    (yseq : ℕ → WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q)
    (hprod : ∀ N,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        ((∑ k ∈ Finset.range N,
            (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) :
          Lp ℂ p G.toWeakGridSpace.measure)
        (yseq N : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure))
    {C : ℝ}
    (hbound : ∀ N,
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q (yseq N) ≤ C)
    (hcauchy : ∀ η > 0, ∃ N₀, ∀ M ≥ N₀, ∀ N ≥ N₀,
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q
        (yseq N - yseq M) < η) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsPointwiseProduct
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
        (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        (g : Lp ℂ p G.toWeakGridSpace.measure)
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q y ≤ C :=
  restrict_souzaRepresentation_of_cauchy_initialSegments_bound
    G s p q hs hp hp_top W R yseq hprod
    (induced_souza_assumptionG2 G s p q hs hp hp_top W)
    (induced_souza_assumptionA5 G s p hs hp hp_top W)
    hbound hcauchy

/--
Quantitative initial-segment restriction estimates give the induced-grid
restriction operator for one good-grid cell.

This is the intermediate form needed by the `selfs ⊂ L∞` argument: for every
ambient Besov element `x`, multiplication by `1_W` has a representative on the
grid induced by `W`, with a concrete cost bound.
-/
theorem souzaIndicatorRestrictsToInduced_of_initialSegmentRestrictionBound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G) {K : ℝ}
    (hK : 0 ≤ K)
    (hsegments :
      ∀ {g : Lp ℂ p G.toWeakGridSpace.measure},
      ∀ R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top) g,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
      ∃ yseq : ℕ → WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        (∀ N,
          WeakGridSpace.RepresentsPointwiseProduct
            (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
            (p := p)
            (W.cell.indicator fun _ => (1 : ℂ))
            ((∑ k ∈ Finset.range N,
                (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) :
              Lp ℂ p G.toWeakGridSpace.measure)
            (yseq N : Lp ℂ p
              (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure)) ∧
        (∀ N,
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q (yseq N) ≤
              K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) ∧
        (∀ η > 0, ∃ N₀, ∀ M ≥ N₀, ∀ N ≥ N₀,
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q
            (yseq N - yseq M) < η)) :
    ∀ x : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ y : WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p) (W.cell.indicator fun _ => (1 : ℂ))
          (x : Lp ℂ p G.toWeakGridSpace.measure)
          (y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q y ≤
          (2 * K + 1) * WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q x := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell A
  intro x
  let normx : ℝ := WeakGridSpace.BesovishSpace.Norm_Costpq A q x
  have hfiniteA :
      WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations (A := A) q :=
    WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A q
  have hnorm_nonneg : 0 ≤ normx :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
      (A := A) (q := q) hfiniteA x
  by_cases hnorm_zero : normx = 0
  · have hx_zero : x = 0 :=
      WeakGridSpace.BesovishSpace.eq_zero_of_Norm_Costpq_eq_zero
        (A := A) (q := q) hp_top
        (souza_assumptionG2 G s p q hs hp hp_top).1 hfiniteA
        (by simpa [A, normx] using hnorm_zero)
    refine ⟨0, ?_, ?_⟩
    · subst x
      simpa [WeakGridSpace.RepresentsPointwiseProduct] using
        WeakGridSpace.representsPointwiseProduct_zero
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p) (W.cell.indicator fun _ => (1 : ℂ))
    · have hzero :
          WeakGridSpace.BesovishSpace.Norm_Costpq Ai q
            (0 : WeakGridSpace.BesovishSpace Ai q) = 0 := by
        have hsmul := WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq
          (A := Ai) (q := q) hp_top
          (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := Ai) q)
          (0 : ℂ) (0 : WeakGridSpace.BesovishSpace Ai q)
        simp at hsmul
        exact hsmul
      change WeakGridSpace.BesovishSpace.Norm_Costpq Ai q
          (0 : WeakGridSpace.BesovishSpace Ai q) ≤ (2 * K + 1) * normx
      rw [hzero, hnorm_zero]
      simp
  · have hnorm_pos : 0 < normx := lt_of_le_of_ne' hnorm_nonneg hnorm_zero
    rcases WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add
        (A := A) (q := q) hfiniteA x hnorm_pos with
      ⟨R, hRfin, hRcost⟩
    rcases hsegments R hRfin with ⟨yseq, hprod, hbound, hcauchy⟩
    rcases restrict_souzaRepresentation_of_cauchy_initialSegments_bound
        G s p q hs hp hp_top W R yseq hprod
        (induced_souza_assumptionG2 G s p q hs hp hp_top W)
        (induced_souza_assumptionA5 G s p hs hp hp_top W) hbound hcauchy with
      ⟨y, hyprod, hybound⟩
    refine ⟨y, hyprod, ?_⟩
    calc
      WeakGridSpace.BesovishSpace.Norm_Costpq Ai q y
          ≤ K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
            simpa [A, Ai] using hybound
      _ ≤ K * (2 * normx) := by
            have hR_le : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
                2 * normx := by
              calc
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) R
                    ≤ normx + normx := le_of_lt (by simpa [A, normx] using hRcost)
                _ = 2 * normx := by ring
            exact mul_le_mul_of_nonneg_left hR_le hK
      _ = (2 * K) * normx := by ring
      _ ≤ (2 * K + 1) * normx := by
            exact mul_le_mul_of_nonneg_right (by linarith) hnorm_nonneg
      _ = (2 * K + 1) *
            WeakGridSpace.BesovishSpace.Norm_Costpq A q x := by
            rfl

/--
Quantitative initial-segment restriction estimates imply a pointwise multiplier
bound for the cell indicator.

This packages the final functional-analytic step of the restriction lemma:
once every finite-cost Souza representation has restricted initial segments
whose induced Besov costs are bounded by `K * pqCost(R)`, the usual
almost-minimizing representation argument gives a multiplier bound.  The
constant is stated as `2*K + 1` to keep the approximation step elementary.
-/
theorem souzaIndicatorPointwiseMultiplierBound_of_initialSegmentRestrictionBound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G) {K : ℝ}
    (hK : 0 ≤ K)
    (hsegments :
      ∀ {g : Lp ℂ p G.toWeakGridSpace.measure},
      ∀ R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top) g,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
      ∃ yseq : ℕ → WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        (∀ N,
          WeakGridSpace.RepresentsPointwiseProduct
            (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
            (p := p)
            (W.cell.indicator fun _ => (1 : ℂ))
            ((∑ k ∈ Finset.range N,
                (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) :
              Lp ℂ p G.toWeakGridSpace.measure)
            (yseq N : Lp ℂ p
              (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure)) ∧
        (∀ N,
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q (yseq N) ≤
              K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) ∧
        (∀ η > 0, ∃ N₀, ∀ M ≥ N₀, ∀ N ≥ N₀,
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q
            (yseq N - yseq M) < η)) :
    SouzaPointwiseMultiplierBound G s p q hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ)) (2 * K + 1) := by
  refine WeakGridSpace.indicatorPointwiseMultiplierBound_of_restrictsToInduced
    (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
    (A := souzaAtomFamily G s p hs hp hp_top)
    W.toLevelCell (by linarith) ?_
  exact souzaIndicatorRestrictsToInduced_of_initialSegmentRestrictionBound
    G s p q hs hp hp_top W hK hsegments

/--
Version of `souzaIndicatorPointwiseMultiplierBound_of_initialSegmentRestrictionBound`
as membership in the Souza pointwise multiplier class.
-/
theorem souzaIndicatorPointwiseMultiplier_of_initialSegmentRestrictionBound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G) {K : ℝ}
    (hK : 0 ≤ K)
    (hsegments :
      ∀ {g : Lp ℂ p G.toWeakGridSpace.measure},
      ∀ R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top) g,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
      ∃ yseq : ℕ → WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        (∀ N,
          WeakGridSpace.RepresentsPointwiseProduct
            (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
            (p := p)
            (W.cell.indicator fun _ => (1 : ℂ))
            ((∑ k ∈ Finset.range N,
                (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) :
              Lp ℂ p G.toWeakGridSpace.measure)
            (yseq N : Lp ℂ p
              (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure)) ∧
        (∀ N,
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q (yseq N) ≤
              K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) ∧
        (∀ η > 0, ∃ N₀, ∀ M ≥ N₀, ∀ N ≥ N₀,
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q
            (yseq N - yseq M) < η)) :
    SouzaPointwiseMultiplier G s p q hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ)) :=
  ⟨2 * K + 1,
    souzaIndicatorPointwiseMultiplierBound_of_initialSegmentRestrictionBound
      G s p q hs hp hp_top W hK hsegments⟩

/--
Direct restriction estimates give the induced-grid restriction operator for
one good-grid cell.

This is the endpoint-friendly version of
`souzaIndicatorRestrictsToInduced_of_initialSegmentRestrictionBound`.
-/
private theorem souzaIndicatorRestrictsToInduced_of_restrictionBound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G) {K : ℝ}
    (hK : 0 ≤ K)
    (hrestrict :
      ∀ {g : Lp ℂ p G.toWeakGridSpace.measure},
      ∀ R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top) g,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
      ∃ y : WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p)
          (W.cell.indicator fun _ => (1 : ℂ))
          (g : Lp ℂ p G.toWeakGridSpace.measure)
          (y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q y ≤
            K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) :
    ∀ x : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ y : WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p) (W.cell.indicator fun _ => (1 : ℂ))
          (x : Lp ℂ p G.toWeakGridSpace.measure)
          (y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q y ≤
          (2 * K + 1) * WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q x := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell A
  intro x
  let normx : ℝ := WeakGridSpace.BesovishSpace.Norm_Costpq A q x
  have hfiniteA :
      WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations (A := A) q :=
    WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A q
  have hnorm_nonneg : 0 ≤ normx :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
      (A := A) (q := q) hfiniteA x
  by_cases hnorm_zero : normx = 0
  · have hx_zero : x = 0 :=
      WeakGridSpace.BesovishSpace.eq_zero_of_Norm_Costpq_eq_zero
        (A := A) (q := q) hp_top
        (souza_assumptionG2 G s p q hs hp hp_top).1 hfiniteA
        (by simpa [A, normx] using hnorm_zero)
    refine ⟨0, ?_, ?_⟩
    · subst x
      simpa [WeakGridSpace.RepresentsPointwiseProduct] using
        WeakGridSpace.representsPointwiseProduct_zero
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p) (W.cell.indicator fun _ => (1 : ℂ))
    · have hzero :
          WeakGridSpace.BesovishSpace.Norm_Costpq Ai q
            (0 : WeakGridSpace.BesovishSpace Ai q) = 0 := by
        have hsmul := WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq
          (A := Ai) (q := q) hp_top
          (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := Ai) q)
          (0 : ℂ) (0 : WeakGridSpace.BesovishSpace Ai q)
        simp at hsmul
        exact hsmul
      change WeakGridSpace.BesovishSpace.Norm_Costpq Ai q
          (0 : WeakGridSpace.BesovishSpace Ai q) ≤ (2 * K + 1) * normx
      rw [hzero, hnorm_zero]
      simp
  · have hnorm_pos : 0 < normx := lt_of_le_of_ne' hnorm_nonneg hnorm_zero
    rcases WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add
        (A := A) (q := q) hfiniteA x hnorm_pos with
      ⟨R, hRfin, hRcost⟩
    rcases hrestrict R hRfin with ⟨y, hyprod, hybound⟩
    refine ⟨y, hyprod, ?_⟩
    calc
      WeakGridSpace.BesovishSpace.Norm_Costpq Ai q y
          ≤ K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
            simpa [A, Ai] using hybound
      _ ≤ K * (2 * normx) := by
            have hR_le : WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
                2 * normx := by
              calc
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) R
                    ≤ normx + normx := le_of_lt (by simpa [A, normx] using hRcost)
                _ = 2 * normx := by ring
            exact mul_le_mul_of_nonneg_left hR_le hK
      _ = (2 * K) * normx := by ring
      _ ≤ (2 * K + 1) * normx := by
            exact mul_le_mul_of_nonneg_right (by linarith) hnorm_nonneg
      _ = (2 * K + 1) *
            WeakGridSpace.BesovishSpace.Norm_Costpq A q x := by
            rfl

/--
Ambient supported restriction estimates give the induced-grid restriction
operator for a good-grid cell.

This is the formal version of the corrected bookkeeping: construct `1_W x`
first in the original Souza Besov space, using the original level index and
with coefficients zero before the level of `W` and outside `W`; then read that
same supported representation on the grid induced by `W`, without increasing
the coefficient cost.
-/
theorem souzaIndicatorRestrictsToInduced_of_ambientSupportedRestrictionBound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G) {K : ℝ}
    (hambient :
      ∀ x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q,
        ∃ y : Lp ℂ p G.toWeakGridSpace.measure,
        ∃ R : WeakGridSpace.LpGridRepresentation
            (souzaAtomFamily G s p hs hp hp_top) y,
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
          WeakGridSpace.RepresentsPointwiseProduct
            (G := G.toWeakGridSpace) (p := p)
            (W.cell.indicator fun _ => (1 : ℂ))
            (x : Lp ℂ p G.toWeakGridSpace.measure) y ∧
          (∀ n, n < W.level →
            (R.block n).toLp (souzaAtomFamily G s p hs hp hp_top) = 0) ∧
          (∀ n (P : WeakGridSpace.LevelCell G.toWeakGridSpace n),
            ¬ P.1 ⊆ W.cell → (R.block n).coeff P = 0) ∧
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ≤
            K * WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q x) :
    ∀ x : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ y : WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p) (W.cell.indicator fun _ => (1 : ℂ))
          (x : Lp ℂ p G.toWeakGridSpace.measure)
          (y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q y ≤
          K * WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q x := by
  exact WeakGridSpace.restrictsToInduced_of_ambientSupportedRepresentation
    (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
    (A := souzaAtomFamily G s p hs hp hp_top) W.toLevelCell hambient

/--
Direct restriction estimates imply a pointwise multiplier bound for the cell
indicator.

This variant is useful at the endpoint `q = ∞`: instead of requiring the
restricted initial segments to be Cauchy in the Besov coefficient gauge, it only
asks for a restricted representative of the full function with the desired
cost bound.
-/
private theorem souzaIndicatorPointwiseMultiplierBound_of_restrictionBound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G) {K : ℝ}
    (hK : 0 ≤ K)
    (hrestrict :
      ∀ {g : Lp ℂ p G.toWeakGridSpace.measure},
      ∀ R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top) g,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
      ∃ y : WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p)
          (W.cell.indicator fun _ => (1 : ℂ))
          (g : Lp ℂ p G.toWeakGridSpace.measure)
          (y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q y ≤
            K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) :
    SouzaPointwiseMultiplierBound G s p q hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ)) (2 * K + 1) := by
  refine WeakGridSpace.indicatorPointwiseMultiplierBound_of_restrictsToInduced
    (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
    (A := souzaAtomFamily G s p hs hp hp_top)
    W.toLevelCell (by linarith) ?_
  exact souzaIndicatorRestrictsToInduced_of_restrictionBound
    G s p q hs hp hp_top W hK hrestrict

/--
Direct-restriction version as membership in the Souza pointwise multiplier
class.
-/
private theorem souzaIndicatorPointwiseMultiplier_of_restrictionBound
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (W : GoodGridCell G) {K : ℝ}
    (hK : 0 ≤ K)
    (hrestrict :
      ∀ {g : Lp ℂ p G.toWeakGridSpace.measure},
      ∀ R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top) g,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
      ∃ y : WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p)
          (W.cell.indicator fun _ => (1 : ℂ))
          (g : Lp ℂ p G.toWeakGridSpace.measure)
          (y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q y ≤
            K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R) :
    SouzaPointwiseMultiplier G s p q hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ)) :=
  ⟨2 * K + 1,
    souzaIndicatorPointwiseMultiplierBound_of_restrictionBound
      G s p q hs hp hp_top W hK hrestrict⟩

private theorem cCoefficientInt_nonneg_of_nonneg
    (t q : ℝ≥0∞) (b : ℤ → ℝ)
    (hb_nonneg : ∀ k, 0 ≤ b k) :
    0 ≤ WeakGridSpace.LpGridRepresentation.cCoefficientInt t q b := by
  unfold WeakGridSpace.LpGridRepresentation.cCoefficientInt
  split_ifs with hq1 hqtop
  · refine Real.sSup_nonneg ?_
    intro x hx
    rcases hx with ⟨k, rfl⟩
    exact Real.rpow_nonneg (hb_nonneg k) _
  · exact tsum_nonneg fun k => Real.rpow_nonneg (hb_nonneg k) _
  · exact Real.rpow_nonneg
      (tsum_nonneg fun k => Real.rpow_nonneg (hb_nonneg k) _) _

private theorem transmutationKernelZ_nonneg
    (lam A r : ℝ) (hlam_pos : 0 < lam) :
    ∀ n : ℤ, 0 ≤ WeakGridSpace.transmutationKernelZ lam A r n := by
  intro n
  by_cases hn : A / r - 1 < (n : ℝ)
  · simp [WeakGridSpace.transmutationKernelZ, hn,
      Real.rpow_nonneg (le_of_lt hlam_pos)]
  · simp [WeakGridSpace.transmutationKernelZ, hn]

/-- Uniform constant for the ambient-grid restriction transmutation. -/
noncomputable def souzaAmbientRestrictionMultiplierConstant
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞) : ℝ :=
  (G.toWeakGridSpace.grid.Cmult1 : ℝ) *
    WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
      (WeakGridSpace.transmutationKernelZ
        (souzaAmbientRestrictionLambda G s p) 0 1)

private theorem souzaAmbientRestrictionMultiplierConstant_nonneg
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    0 ≤ souzaAmbientRestrictionMultiplierConstant G s p := by
  let lam := souzaAmbientRestrictionLambda G s p
  have hlam_pos : 0 < lam := souzaAmbientRestrictionLambda_pos G s p hp hp_top
  have hccoef_nonneg : 0 ≤
      WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
        (WeakGridSpace.transmutationKernelZ lam 0 1) :=
    cCoefficientInt_nonneg_of_nonneg p ∞ _
      (transmutationKernelZ_nonneg lam 0 1 hlam_pos)
  dsimp [souzaAmbientRestrictionMultiplierConstant, lam]
  exact mul_nonneg
    (by exact_mod_cast Nat.zero_le G.toWeakGridSpace.grid.Cmult1)
    hccoef_nonneg

/--
Representation-level endpoint restriction estimate obtained by transmuting on
the original grid.

This is the concrete replacement for an external `hrestrict` assumption at
`q = ∞`.
-/
theorem souzaIndicatorRestrictionBound_of_ambientRestrictionTransmutation_top
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) :
    ∀ {g : Lp ℂ p G.toWeakGridSpace.measure},
      ∀ R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top) g,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := ∞) R →
      ∃ y : WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) ∞,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p)
          (W.cell.indicator fun _ => (1 : ℂ))
          (g : Lp ℂ p G.toWeakGridSpace.measure)
          (y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) ∞ y ≤
            souzaAmbientRestrictionMultiplierConstant G s p *
              WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) R := by
  classical
  haveI : Fact ((1 : ℝ≥0∞) ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  let Gi := G.toWeakGridSpace
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let A := souzaAtomFamily G s p hs hp hp_top
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell A
  let lam := souzaAmbientRestrictionLambda G s p
  let K := souzaAmbientRestrictionMultiplierConstant G s p
  have hlam_pos : 0 < lam := souzaAmbientRestrictionLambda_pos G s p hp hp_top
  have hlam_lt : lam < 1 := souzaAmbientRestrictionLambda_lt_one G s p hp hp_top hs_lt_inv
  intro g R hRfin
  rcases restrict_souzaRepresentation_ambientTransmutationAtomData
      G s p ∞ hs hp hp_top hs_lt_inv W R with
    ⟨h, Rt, hRt, hAtom, _hbeforeLocalLp, hbeforeLocalCoeff, houtsideLocal⟩
  let c : (i : ℕ) → WeakGridSpace.LevelCell Gi i → ℂ :=
    fun i Q => (R.block i).coeff Q
  have hc : WeakGridSpace.CoeffFinitePQCost
      (p := p) (q := ∞) Gi c := by
    simpa [Gi, c, WeakGridSpace.CoeffFinitePQCost,
      WeakGridSpace.CoeffPLevel, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hRfin
  have hcost_eq :
      WeakGridSpace.CoeffPQCost (p := p) (q := ∞) Gi c =
        WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) R := by
    simp [Gi, c, WeakGridSpace.CoeffPQCost, WeakGridSpace.CoeffPLevel,
      WeakGridSpace.LpGridRepresentation.pqCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower]
  rcases WeakGridSpace.Transmutation_of_Atoms_Claim_A_top
      (G := Gi) (W := Gi) (AW := A)
      (p := p) (u := ∞)
      (fun i : ℕ => i) 0 0 1 (by norm_num)
      ambient_id_almostLinear_bound
      lam hlam_pos hlam_lt 1 (by norm_num) h Rt hRt c hc
      (souza_assumptionG2 G s p ∞ hs hp hp_top)
      hp_top hs with
    ⟨gLim, hsum, hmem, hfin, htend, hcost⟩
  let Rlim : WeakGridSpace.LpGridRepresentation A gLim :=
    { block := WeakGridSpace.TransmutationBlockLimit Gi Gi A h Rt c 0 1
      hasSum := hsum }
  have hbefore : ∀ n, n < W.level → (Rlim.block n).toLp A = 0 := by
    intro n hn
    exact levelBlock_toLp_eq_zero_of_coeff_eq_zero A (Rlim.block n) (by
      intro P
      exact transmutationBlockLimit_coeff_eq_zero_of_local_coeff_eq_zero
        Gi Gi A h Rt c 0 1 n P (fun i Q => hbeforeLocalCoeff i Q n P hn))
  have houtside : ∀ n (P : WeakGridSpace.LevelCell Gi n),
      ¬ P.1 ⊆ W.cell → (Rlim.block n).coeff P = 0 := by
    intro n P hP
    exact transmutationBlockLimit_coeff_eq_zero_of_local_coeff_eq_zero
      Gi Gi A h Rt c 0 1 n P (fun i Q => houtsideLocal i Q n P hP)
  let Ri : WeakGridSpace.LpGridRepresentation Ai gLim :=
    WeakGridSpace.ambientSupportedRepresentationToInduced Gi W.toLevelCell A
      Rlim hbefore houtside
  have hRi_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := ∞) Ri :=
    WeakGridSpace.ambientSupportedRepresentationToInduced_finitePQCost
      Gi W.toLevelCell A Rlim hbefore houtside hfin
  let y : WeakGridSpace.BesovishSpace Ai ∞ := ⟨gLim, ⟨Ri, hRi_fin⟩⟩
  have hprod_ambient :
      WeakGridSpace.RepresentsPointwiseProduct
        (G := Gi) (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        (g : Lp ℂ p Gi.measure)
        (gLim : Lp ℂ p Gi.measure) := by
    let partialSum : ℕ → Lp ℂ p Gi.measure := fun N =>
      ((∑ k ∈ Finset.range N, (R.block k).toLp A) :
        Lp ℂ p Gi.measure)
    have hx :
        Filter.Tendsto partialSum Filter.atTop
          (𝓝 (g : Lp ℂ p Gi.measure)) := by
      simpa [partialSum, A, Gi] using R.hasSum.tendsto_sum_nat
    exact WeakGridSpace.RepresentsPointwiseProduct.of_tendsto_Lp
      (G := Gi) (p := p)
      (m := W.cell.indicator fun _ => (1 : ℂ))
      (xseq := partialSum)
      (yseq := fun N => WeakGridSpace.PartialSumLevels Gi Gi h c N)
      (x := (g : Lp ℂ p Gi.measure))
      (y := (gLim : Lp ℂ p Gi.measure))
      hx htend (by
        intro N
        simpa [partialSum, A, Gi, c] using
          restrict_souzaRepresentation_partialSum_representsPointwiseProduct_ambient
            G s p hs hp hp_top W R h hAtom N)
  refine ⟨y, ?_, ?_⟩
  · simpa [Wi, Gi, Ai, y] using hprod_ambient
  · have hNorm_le_cost :
        WeakGridSpace.BesovishSpace.Norm_Costpq Ai ∞ y ≤
          WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Ri :=
      WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
        (A := Ai) (q := ∞) (g := y) Ri hRi_fin
    have hRi_cost :
        WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Ri ≤
          WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rlim :=
      WeakGridSpace.ambientSupportedRepresentationToInduced_pqCost_le
        Gi W.toLevelCell A Rlim hbefore houtside hfin
    calc
      WeakGridSpace.BesovishSpace.Norm_Costpq Ai ∞ y
          ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Ri := hNorm_le_cost
      _ ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rlim := hRi_cost
      _ ≤ K * WeakGridSpace.CoeffPQCost (p := p) (q := ∞) Gi c := by
            simpa [Rlim, Gi, A, K, lam, souzaAmbientRestrictionMultiplierConstant] using hcost
      _ = K * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) R := by
            rw [hcost_eq]

/--
Finite-`q` representation-level restriction estimate obtained by transmuting
on the original grid.

This is the finite counterpart of
`souzaIndicatorRestrictionBound_of_ambientRestrictionTransmutation_top`: the
same ambient transmutation theorem produces an `L^p` limit with finite
`q`-cost, and the support of the transmuted blocks lets us read the resulting
ambient representation as a representation on the grid induced by `W`.
-/
theorem souzaIndicatorRestrictionBound_of_ambientRestrictionTransmutation_finite
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hq_top : q ≠ ∞)
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) :
    ∀ {g : Lp ℂ p G.toWeakGridSpace.measure},
      ∀ R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top) g,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
      ∃ y : WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p)
          (W.cell.indicator fun _ => (1 : ℂ))
          (g : Lp ℂ p G.toWeakGridSpace.measure)
          (y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q y ≤
            souzaAmbientRestrictionMultiplierConstant G s p *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  classical
  let Gi := G.toWeakGridSpace
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let A := souzaAtomFamily G s p hs hp hp_top
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell A
  let lam := souzaAmbientRestrictionLambda G s p
  let K := souzaAmbientRestrictionMultiplierConstant G s p
  have hlam_pos : 0 < lam := souzaAmbientRestrictionLambda_pos G s p hp hp_top
  have hlam_lt : lam < 1 := souzaAmbientRestrictionLambda_lt_one G s p hp hp_top hs_lt_inv
  intro g R hRfin
  rcases restrict_souzaRepresentation_ambientTransmutationAtomData
      G s p q hs hp hp_top hs_lt_inv W R with
    ⟨h, Rt, hRt, hAtom, _hbeforeLocalLp, hbeforeLocalCoeff, houtsideLocal⟩
  let c : (i : ℕ) → WeakGridSpace.LevelCell Gi i → ℂ :=
    fun i Q => (R.block i).coeff Q
  have hc : WeakGridSpace.CoeffFinitePQCost
      (p := p) (q := q) Gi c := by
    simpa [Gi, c, WeakGridSpace.CoeffFinitePQCost,
      WeakGridSpace.CoeffPLevel, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hRfin
  have hcost_eq :
      WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi c =
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
    simp [Gi, c, WeakGridSpace.CoeffPQCost, WeakGridSpace.CoeffPLevel,
      WeakGridSpace.LpGridRepresentation.pqCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower]
  rcases WeakGridSpace.Transmutation_of_Atoms_Claim_A
      (G := Gi) (W := Gi) (AW := A)
      (p := p) (q := q) (u := ∞)
      (fun i : ℕ => i) 0 0 1 (by norm_num)
      ambient_id_almostLinear_bound
      lam hlam_pos hlam_lt 1 (by norm_num) h Rt hRt c hc hq_top
      (souza_assumptionG2 G s p q hs hp hp_top)
      hp_top hs with
    ⟨gLim, hsum, htail⟩
  have hfin :
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
        ({ block := WeakGridSpace.TransmutationBlockLimit Gi Gi A h Rt c 0 1
           hasSum := hsum } : WeakGridSpace.LpGridRepresentation A gLim) :=
    htail.2.1
  have htend :
      Filter.Tendsto (fun N => WeakGridSpace.PartialSumLevels Gi Gi h c N)
        Filter.atTop (𝓝 gLim) :=
    htail.2.2.1
  have hcost :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q)
          ({ block := WeakGridSpace.TransmutationBlockLimit Gi Gi A h Rt c 0 1
             hasSum := hsum } : WeakGridSpace.LpGridRepresentation A gLim) ≤
        (Gi.grid.Cmult1 : ℝ) *
        1 ^ (1 / p.toReal) *
        lam ^ (-(0 : ℝ) / p.toReal) *
        WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
          (WeakGridSpace.transmutationKernelZ lam 0 1) *
        (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal) *
        WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi c :=
    htail.2.2.2
  let Rlim : WeakGridSpace.LpGridRepresentation A gLim :=
    { block := WeakGridSpace.TransmutationBlockLimit Gi Gi A h Rt c 0 1
      hasSum := hsum }
  have hbefore : ∀ n, n < W.level → (Rlim.block n).toLp A = 0 := by
    intro n hn
    exact levelBlock_toLp_eq_zero_of_coeff_eq_zero A (Rlim.block n) (by
      intro P
      exact transmutationBlockLimit_coeff_eq_zero_of_local_coeff_eq_zero
        Gi Gi A h Rt c 0 1 n P (fun i Q => hbeforeLocalCoeff i Q n P hn))
  have houtside : ∀ n (P : WeakGridSpace.LevelCell Gi n),
      ¬ P.1 ⊆ W.cell → (Rlim.block n).coeff P = 0 := by
    intro n P hP
    exact transmutationBlockLimit_coeff_eq_zero_of_local_coeff_eq_zero
      Gi Gi A h Rt c 0 1 n P (fun i Q => houtsideLocal i Q n P hP)
  let Ri : WeakGridSpace.LpGridRepresentation Ai gLim :=
    WeakGridSpace.ambientSupportedRepresentationToInduced Gi W.toLevelCell A
      Rlim hbefore houtside
  have hRi_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Ri :=
    WeakGridSpace.ambientSupportedRepresentationToInduced_finitePQCost
      Gi W.toLevelCell A Rlim hbefore houtside hfin
  let y : WeakGridSpace.BesovishSpace Ai q := ⟨gLim, ⟨Ri, hRi_fin⟩⟩
  have hprod_ambient :
      WeakGridSpace.RepresentsPointwiseProduct
        (G := Gi) (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        (g : Lp ℂ p Gi.measure)
        (gLim : Lp ℂ p Gi.measure) := by
    let partialSum : ℕ → Lp ℂ p Gi.measure := fun N =>
      ((∑ k ∈ Finset.range N, (R.block k).toLp A) :
        Lp ℂ p Gi.measure)
    have hx :
        Filter.Tendsto partialSum Filter.atTop
          (𝓝 (g : Lp ℂ p Gi.measure)) := by
      simpa [partialSum, A, Gi] using R.hasSum.tendsto_sum_nat
    exact WeakGridSpace.RepresentsPointwiseProduct.of_tendsto_Lp
      (G := Gi) (p := p)
      (m := W.cell.indicator fun _ => (1 : ℂ))
      (xseq := partialSum)
      (yseq := fun N => WeakGridSpace.PartialSumLevels Gi Gi h c N)
      (x := (g : Lp ℂ p Gi.measure))
      (y := (gLim : Lp ℂ p Gi.measure))
      hx htend (by
        intro N
        simpa [partialSum, A, Gi, c] using
          restrict_souzaRepresentation_partialSum_representsPointwiseProduct_ambient
            G s p hs hp hp_top W R h hAtom N)
  refine ⟨y, ?_, ?_⟩
  · simpa [Wi, Gi, Ai, y] using hprod_ambient
  · have hNorm_le_cost :
        WeakGridSpace.BesovishSpace.Norm_Costpq Ai q y ≤
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Ri :=
      WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
        (A := Ai) (q := q) (g := y) Ri hRi_fin
    have hRi_cost :
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) Ri ≤
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rlim :=
      WeakGridSpace.ambientSupportedRepresentationToInduced_pqCost_le
        Gi W.toLevelCell A Rlim hbefore houtside hfin
    calc
      WeakGridSpace.BesovishSpace.Norm_Costpq Ai q y
          ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) Ri := hNorm_le_cost
      _ ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rlim := hRi_cost
      _ ≤ K * WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi c := by
            simpa [Rlim, Gi, A, K, lam, souzaAmbientRestrictionMultiplierConstant] using hcost
      _ = K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
            rw [hcost_eq]

/--
Endpoint induced restriction estimate with no external `hrestrict` hypothesis.
-/
theorem souzaIndicatorRestrictsToInduced_of_ambientRestrictionTransmutation_top
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) :
    ∀ x : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) ∞,
      ∃ y : WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) ∞,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p) (W.cell.indicator fun _ => (1 : ℂ))
          (x : Lp ℂ p G.toWeakGridSpace.measure)
          (y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) ∞ y ≤
          (2 * souzaAmbientRestrictionMultiplierConstant G s p + 1) *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) ∞ x := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  exact souzaIndicatorRestrictsToInduced_of_restrictionBound
    G s p ∞ hs hp hp_top W
    (souzaAmbientRestrictionMultiplierConstant_nonneg G s p hp hp_top)
    (souzaIndicatorRestrictionBound_of_ambientRestrictionTransmutation_top
      G s p hs hp hp_top hs_lt_inv W)

/--
Finite-`q` induced restriction estimate with no external `hrestrict`
hypothesis.
-/
theorem souzaIndicatorRestrictsToInduced_of_ambientRestrictionTransmutation_finite
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hq_top : q ≠ ∞)
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) :
    ∀ x : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ y : WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p) (W.cell.indicator fun _ => (1 : ℂ))
          (x : Lp ℂ p G.toWeakGridSpace.measure)
          (y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q y ≤
          (2 * souzaAmbientRestrictionMultiplierConstant G s p + 1) *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q x := by
  exact souzaIndicatorRestrictsToInduced_of_restrictionBound
    G s p q hs hp hp_top W
    (souzaAmbientRestrictionMultiplierConstant_nonneg G s p hp hp_top)
    (souzaIndicatorRestrictionBound_of_ambientRestrictionTransmutation_finite
      G s p q hs hp hp_top hq_top hs_lt_inv W)

/--
Induced restriction estimate obtained uniformly from ambient transmutation.

The proof splits only on whether `q = ∞`; both branches use the same ambient
grid transmutation and then read the supported limit representation on the
grid induced by `W`.
-/
theorem souzaIndicatorRestrictsToInduced_of_ambientRestrictionTransmutation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) :
    ∀ x : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ y : WeakGridSpace.BesovishSpace
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q,
        WeakGridSpace.RepresentsPointwiseProduct
          (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell)
          (p := p) (W.cell.indicator fun _ => (1 : ℂ))
          (x : Lp ℂ p G.toWeakGridSpace.measure)
          (y : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell).measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell
              (souzaAtomFamily G s p hs hp hp_top)) q y ≤
          (2 * souzaAmbientRestrictionMultiplierConstant G s p + 1) *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q x := by
  classical
  by_cases hq_top : q = ∞
  · subst q
    exact souzaIndicatorRestrictsToInduced_of_ambientRestrictionTransmutation_top
      G s p hs hp hp_top hs_lt_inv W
  · exact souzaIndicatorRestrictsToInduced_of_ambientRestrictionTransmutation_finite
      G s p q hs hp hp_top hq_top hs_lt_inv W

/--
Endpoint multiplier bound obtained from ambient transmutation, with constant
independent of the chosen cell.
-/
private theorem souzaIndicatorPointwiseMultiplierBound_of_ambientRestrictionTransmutation_top
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) :
    SouzaPointwiseMultiplierBound G s p ∞ hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ))
      (2 * souzaAmbientRestrictionMultiplierConstant G s p + 1) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  exact souzaIndicatorPointwiseMultiplierBound_of_restrictionBound
    G s p ∞ hs hp hp_top W
    (souzaAmbientRestrictionMultiplierConstant_nonneg G s p hp hp_top)
    (souzaIndicatorRestrictionBound_of_ambientRestrictionTransmutation_top
      G s p hs hp hp_top hs_lt_inv W)

/--
Finite-`q` multiplier bound obtained from ambient transmutation, with constant
independent of the chosen cell.
-/
private theorem souzaIndicatorPointwiseMultiplierBound_of_ambientRestrictionTransmutation_finite
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hq_top : q ≠ ∞)
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) :
    SouzaPointwiseMultiplierBound G s p q hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ))
      (2 * souzaAmbientRestrictionMultiplierConstant G s p + 1) := by
  exact souzaIndicatorPointwiseMultiplierBound_of_restrictionBound
    G s p q hs hp hp_top W
    (souzaAmbientRestrictionMultiplierConstant_nonneg G s p hp hp_top)
    (souzaIndicatorRestrictionBound_of_ambientRestrictionTransmutation_finite
      G s p q hs hp hp_top hq_top hs_lt_inv W)

/--
Uniform multiplier bound for good-grid cell indicators obtained from ambient
transmutation.

The bound is uniform in the cell `W`: the displayed constant depends only on
`G`, `s`, and `p`, not on the level or position of `W`.
-/
theorem souzaIndicatorPointwiseMultiplierBound_of_ambientRestrictionTransmutation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) :
    SouzaPointwiseMultiplierBound G s p q hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ))
      (2 * souzaAmbientRestrictionMultiplierConstant G s p + 1) := by
  classical
  by_cases hq_top : q = ∞
  · subst q
    exact souzaIndicatorPointwiseMultiplierBound_of_ambientRestrictionTransmutation_top
      G s p hs hp hp_top hs_lt_inv W
  · exact souzaIndicatorPointwiseMultiplierBound_of_ambientRestrictionTransmutation_finite
      G s p q hs hp hp_top hq_top hs_lt_inv W

/--
Endpoint ambient transmutation for good-grid cell indicators, with a constant
independent of the cell level.

This applies the abstract transmutation theorem on the original grid with
`k i = i`, then reads the resulting supported ambient representation on the
grid induced by `W`.
-/
theorem souzaIndicatorPointwiseMultiplier_of_ambientRestrictionTransmutation_top
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) :
    SouzaPointwiseMultiplier G s p ∞ hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ)) := by
  classical
  haveI : Fact ((1 : ℝ≥0∞) ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  let Gi := G.toWeakGridSpace
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let A := souzaAtomFamily G s p hs hp hp_top
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell A
  let lam := souzaAmbientRestrictionLambda G s p
  let K := souzaAmbientRestrictionMultiplierConstant G s p
  have hlam_pos : 0 < lam := souzaAmbientRestrictionLambda_pos G s p hp hp_top
  have hlam_lt : lam < 1 := souzaAmbientRestrictionLambda_lt_one G s p hp hp_top hs_lt_inv
  have hccoef_nonneg : 0 ≤
      WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
        (WeakGridSpace.transmutationKernelZ lam 0 1) :=
    cCoefficientInt_nonneg_of_nonneg p ∞ _
      (transmutationKernelZ_nonneg lam 0 1 hlam_pos)
  have hK : 0 ≤ K := by
    dsimp [K, souzaAmbientRestrictionMultiplierConstant, lam]
    exact mul_nonneg
      (by exact_mod_cast Nat.zero_le G.toWeakGridSpace.grid.Cmult1)
      hccoef_nonneg
  refine souzaIndicatorPointwiseMultiplier_of_restrictionBound
    G s p ∞ hs hp hp_top W hK ?_
  intro g R hRfin
  rcases restrict_souzaRepresentation_ambientTransmutationAtomData
      G s p ∞ hs hp hp_top hs_lt_inv W R with
    ⟨h, Rt, hRt, hAtom, _hbeforeLocalLp, hbeforeLocalCoeff, houtsideLocal⟩
  let c : (i : ℕ) → WeakGridSpace.LevelCell Gi i → ℂ :=
    fun i Q => (R.block i).coeff Q
  have hc : WeakGridSpace.CoeffFinitePQCost
      (p := p) (q := ∞) Gi c := by
    simpa [Gi, c, WeakGridSpace.CoeffFinitePQCost,
      WeakGridSpace.CoeffPLevel, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hRfin
  have hcost_eq :
      WeakGridSpace.CoeffPQCost (p := p) (q := ∞) Gi c =
        WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) R := by
    simp [Gi, c, WeakGridSpace.CoeffPQCost, WeakGridSpace.CoeffPLevel,
      WeakGridSpace.LpGridRepresentation.pqCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower]
  rcases WeakGridSpace.Transmutation_of_Atoms_Claim_A_top
      (G := Gi) (W := Gi) (AW := A)
      (p := p) (u := ∞)
      (fun i : ℕ => i) 0 0 1 (by norm_num)
      ambient_id_almostLinear_bound
      lam hlam_pos hlam_lt 1 (by norm_num) h Rt hRt c hc
      (souza_assumptionG2 G s p ∞ hs hp hp_top)
      hp_top hs with
    ⟨gLim, hsum, hmem, hfin, htend, hcost⟩
  let Rlim : WeakGridSpace.LpGridRepresentation A gLim :=
    { block := WeakGridSpace.TransmutationBlockLimit Gi Gi A h Rt c 0 1
      hasSum := hsum }
  have hbefore : ∀ n, n < W.level → (Rlim.block n).toLp A = 0 := by
    intro n hn
    exact levelBlock_toLp_eq_zero_of_coeff_eq_zero A (Rlim.block n) (by
      intro P
      exact transmutationBlockLimit_coeff_eq_zero_of_local_coeff_eq_zero
        Gi Gi A h Rt c 0 1 n P (fun i Q => hbeforeLocalCoeff i Q n P hn))
  have houtside : ∀ n (P : WeakGridSpace.LevelCell Gi n),
      ¬ P.1 ⊆ W.cell → (Rlim.block n).coeff P = 0 := by
    intro n P hP
    exact transmutationBlockLimit_coeff_eq_zero_of_local_coeff_eq_zero
      Gi Gi A h Rt c 0 1 n P (fun i Q => houtsideLocal i Q n P hP)
  let Ri : WeakGridSpace.LpGridRepresentation Ai gLim :=
    WeakGridSpace.ambientSupportedRepresentationToInduced Gi W.toLevelCell A
      Rlim hbefore houtside
  have hRi_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := ∞) Ri :=
    WeakGridSpace.ambientSupportedRepresentationToInduced_finitePQCost
      Gi W.toLevelCell A Rlim hbefore houtside hfin
  let y : WeakGridSpace.BesovishSpace Ai ∞ := ⟨gLim, ⟨Ri, hRi_fin⟩⟩
  have hprod_ambient :
      WeakGridSpace.RepresentsPointwiseProduct
        (G := Gi) (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        (g : Lp ℂ p Gi.measure)
        (gLim : Lp ℂ p Gi.measure) := by
    let partialSum : ℕ → Lp ℂ p Gi.measure := fun N =>
      ((∑ k ∈ Finset.range N, (R.block k).toLp A) :
        Lp ℂ p Gi.measure)
    have hx :
        Filter.Tendsto partialSum Filter.atTop
          (𝓝 (g : Lp ℂ p Gi.measure)) := by
      simpa [partialSum, A, Gi] using R.hasSum.tendsto_sum_nat
    exact WeakGridSpace.RepresentsPointwiseProduct.of_tendsto_Lp
      (G := Gi) (p := p)
      (m := W.cell.indicator fun _ => (1 : ℂ))
      (xseq := partialSum)
      (yseq := fun N => WeakGridSpace.PartialSumLevels Gi Gi h c N)
      (x := (g : Lp ℂ p Gi.measure))
      (y := (gLim : Lp ℂ p Gi.measure))
      hx htend (by
        intro N
        simpa [partialSum, A, Gi, c] using
          restrict_souzaRepresentation_partialSum_representsPointwiseProduct_ambient
            G s p hs hp hp_top W R h hAtom N)
  refine ⟨y, ?_, ?_⟩
  · simpa [Wi, Gi, Ai, y] using hprod_ambient
  · have hNorm_le_cost :
        WeakGridSpace.BesovishSpace.Norm_Costpq Ai ∞ y ≤
          WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Ri :=
      WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
        (A := Ai) (q := ∞) (g := y) Ri hRi_fin
    have hRi_cost :
        WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Ri ≤
          WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rlim :=
      WeakGridSpace.ambientSupportedRepresentationToInduced_pqCost_le
        Gi W.toLevelCell A Rlim hbefore houtside hfin
    calc
      WeakGridSpace.BesovishSpace.Norm_Costpq Ai ∞ y
          ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Ri := hNorm_le_cost
      _ ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rlim := hRi_cost
      _ ≤ K * WeakGridSpace.CoeffPQCost (p := p) (q := ∞) Gi c := by
            simpa [Rlim, Gi, A, K, lam, souzaAmbientRestrictionMultiplierConstant] using hcost
      _ = K * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) R := by
            rw [hcost_eq]

/--
Finite-`q` ambient transmutation for good-grid cell indicators, with a
constant independent of the cell level.
-/
theorem souzaIndicatorPointwiseMultiplier_of_ambientRestrictionTransmutation_finite
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hq_top : q ≠ ∞)
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) :
    SouzaPointwiseMultiplier G s p q hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ)) := by
  exact souzaIndicatorPointwiseMultiplier_of_restrictionBound
    G s p q hs hp hp_top W
    (souzaAmbientRestrictionMultiplierConstant_nonneg G s p hp hp_top)
    (souzaIndicatorRestrictionBound_of_ambientRestrictionTransmutation_finite
      G s p q hs hp hp_top hq_top hs_lt_inv W)

/--
Ambient transmutation theorem for good-grid cell indicators.

For every `q >= 1`, including `q = ∞`, the indicator of a good-grid cell is a
Souza pointwise multiplier under the strict condition `s < 1 / p`.
-/
theorem souzaIndicatorPointwiseMultiplier_of_ambientRestrictionTransmutation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (W : GoodGridCell G) :
    SouzaPointwiseMultiplier G s p q hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ)) := by
  classical
  by_cases hq_top : q = ∞
  · subst q
    exact souzaIndicatorPointwiseMultiplier_of_ambientRestrictionTransmutation_top
      G s p hs hp hp_top hs_lt_inv W
  · exact souzaIndicatorPointwiseMultiplier_of_ambientRestrictionTransmutation_finite
      G s p q hs hp hp_top hq_top hs_lt_inv W

private theorem CoeffPQCost_window_tail_tendsto_zero
    (G : WeakGridSpace.WeakGridSpace (α := α))
    (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (c : (i : ℕ) → WeakGridSpace.LevelCell G i → ℂ)
    (hp_top : p ≠ ∞) (hq_top : q ≠ ∞)
    (hc : WeakGridSpace.CoeffFinitePQCost (p := p) (q := q) G c) :
    ∀ ε > 0, ∃ N₀, ∀ M ≥ N₀, ∀ N ≥ M,
      WeakGridSpace.CoeffPQCost (p := p) (q := q) G
        (fun i Q => if M ≤ i ∧ i < N then c i Q else 0) < ε := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  have hq_ne_zero : q ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq_ne_zero hq_top
  let a : ℕ → ℝ := fun i =>
    (WeakGridSpace.CoeffPLevel (p := p) G c i) ^ (q.toReal / p.toReal)
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    exact Real.rpow_nonneg
      (Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have ha_sum : Summable a := by
    simpa [a, WeakGridSpace.CoeffFinitePQCost, hq_top] using hc
  intro ε hε
  have hεq_pos : 0 < ε ^ q.toReal := Real.rpow_pos_of_pos hε _
  rcases WeakGridSpace.summable_Ico_tail_tendsto_zero ha_nonneg ha_sum
      (ε ^ q.toReal) hεq_pos with
    ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro M hM N hMN
  have htail := hN₀ M hM N hMN
  have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.Ico M N, a i :=
    Finset.sum_nonneg fun i _ => ha_nonneg i
  have hroot_lt :
      (∑ i ∈ Finset.Ico M N, a i) ^ (1 / q.toReal) < ε := by
    have hpow_lt :
        (∑ i ∈ Finset.Ico M N, a i) ^ (1 / q.toReal) <
          (ε ^ q.toReal) ^ (1 / q.toReal) :=
      Real.rpow_lt_rpow hsum_nonneg htail (one_div_pos.mpr hq_pos)
    have hε_root : (ε ^ q.toReal) ^ (1 / q.toReal) = ε := by
      simpa [one_div] using Real.rpow_rpow_inv hε.le hq_pos.ne'
    rwa [hε_root] at hpow_lt
  simpa [a] using
    (by
      rw [WeakGridSpace.CoeffPQCost_window_eq_Ico
        (G := G) (p := p) (q := q) c M N hp_top hq_top]
      exact hroot_lt)

/--
Finite-`q` restriction transmutation theorem for good-grid cell indicators.

For every finite `q >= 1`, restricting Souza atoms to a good-grid cell and
transmuting the resulting one-block representatives proves that the indicator
of the cell is a pointwise multiplier.
-/
private theorem souzaIndicatorPointwiseMultiplier_of_restrictionTransmutation_finite
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hq_top : q ≠ ∞)
    (hs_le_inv : s ≤ (p.toReal)⁻¹)
    (W : GoodGridCell G)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1) :
    SouzaPointwiseMultiplier G s p q hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ)) := by
  classical
  let Gi := G.toWeakGridSpace
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let A := souzaAtomFamily G s p hs hp hp_top
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell A
  let K := souzaRestrictionMultiplierConstant G p W lam
  have hccoef_nonneg : 0 ≤
      WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
        (WeakGridSpace.transmutationKernelZ lam (-(W.level : ℝ)) 1) :=
    cCoefficientInt_nonneg_of_nonneg p ∞ _
      (transmutationKernelZ_nonneg lam (-(W.level : ℝ)) 1 hlam_pos)
  have hK : 0 ≤ K := by
    dsimp [K, souzaRestrictionMultiplierConstant]
    exact mul_nonneg
      (by exact_mod_cast Nat.zero_le G.toWeakGridSpace.grid.Cmult1)
      hccoef_nonneg
  refine souzaIndicatorPointwiseMultiplier_of_initialSegmentRestrictionBound
    G s p q hs hp hp_top W hK ?_
  intro g R hRfin
  rcases restrict_souzaRepresentation_transmutationData
      G s p q hs hp hp_top hs_le_inv W lam hlam_pos hlam_lt R with
    ⟨h, Rt, hRt, hprod⟩
  let c : (i : ℕ) → WeakGridSpace.LevelCell Gi i → ℂ :=
    fun i Q => (R.block i).coeff Q
  have hc : WeakGridSpace.CoeffFinitePQCost
      (p := p) (q := q) Gi c := by
    simpa [Gi, c, WeakGridSpace.CoeffFinitePQCost,
      WeakGridSpace.CoeffPLevel, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hRfin
  have hcost_eq :
      WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi c =
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
    simp [Gi, c, WeakGridSpace.CoeffPQCost, WeakGridSpace.CoeffPLevel,
      WeakGridSpace.LpGridRepresentation.pqCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower]
  have htrans :
      ∀ N,
        ∃ y : WeakGridSpace.BesovishSpace Ai q,
          (y : Lp ℂ p Wi.measure) =
            WeakGridSpace.PartialSumLevels Gi Wi h c N ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq Ai q y ≤
            K * WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi c := by
    intro N
    rcases WeakGridSpace.Transmutation_of_Atoms_initialSegment_besovish
        (G := Gi) (W := Wi) (AW := Ai)
        (p := p) (q := q) (u := ∞)
        W.restrictionLevel (-(W.level : ℝ)) 0 1 (by norm_num)
        W.restrictionLevel_bound
        lam hlam_pos hlam_lt 1 (by norm_num) h Rt hRt c hc N hq_top
        (induced_souza_assumptionG2 G s p q hs hp hp_top W)
        hp_top hs with
      ⟨y, hy_eq, hy_bound⟩
    refine ⟨y, hy_eq, ?_⟩
    simpa [Gi, Wi, Ai, A, K, c, souzaRestrictionMultiplierConstant] using hy_bound
  let yseq : ℕ → WeakGridSpace.BesovishSpace Ai q :=
    fun N => Classical.choose (htrans N)
  have hyseq :
      ∀ N,
        (yseq N : Lp ℂ p Wi.measure) =
          WeakGridSpace.PartialSumLevels Gi Wi h c N ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq Ai q (yseq N) ≤
          K * WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi c :=
    fun N => Classical.choose_spec (htrans N)
  have hwindow_bound :
      ∀ M N, M ≤ N →
        WeakGridSpace.BesovishSpace.Norm_Costpq Ai q (yseq N - yseq M) ≤
          K * WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi
            (fun i Q => if M ≤ i ∧ i < N then c i Q else 0) := by
    intro M N hMN
    let cwin : (i : ℕ) → WeakGridSpace.LevelCell Gi i → ℂ :=
      fun i Q => if M ≤ i ∧ i < N then c i Q else 0
    have hcwin : WeakGridSpace.CoeffFinitePQCost
        (p := p) (q := q) Gi cwin := by
      simpa [Gi, cwin] using
        WeakGridSpace.CoeffFinitePQCost_window
          (G := Gi) (p := p) (q := q) c M N hp_top
    rcases WeakGridSpace.Transmutation_of_Atoms_initialSegment_besovish
        (G := Gi) (W := Wi) (AW := Ai)
        (p := p) (q := q) (u := ∞)
        W.restrictionLevel (-(W.level : ℝ)) 0 1 (by norm_num)
        W.restrictionLevel_bound
        lam hlam_pos hlam_lt 1 (by norm_num) h Rt hRt cwin hcwin N hq_top
        (induced_souza_assumptionG2 G s p q hs hp hp_top W)
        hp_top hs with
      ⟨ywin, hywin_eq, hywin_bound⟩
    have hsub_eq : yseq N - yseq M = ywin := by
      apply Subtype.ext
      change ((yseq N : Lp ℂ p Wi.measure) - (yseq M : Lp ℂ p Wi.measure)) =
        (ywin : Lp ℂ p Wi.measure)
      rw [(hyseq N).1, (hyseq M).1, hywin_eq]
      exact (WeakGridSpace.PartialSumLevels_window_eq_sub
        (G := Gi) (W := Wi) h c hMN).symm
    rw [hsub_eq]
    simpa [Gi, Wi, Ai, A, K, cwin, souzaRestrictionMultiplierConstant] using hywin_bound
  refine ⟨yseq, ?_, ?_, ?_⟩
  · intro N
    have hprodN := hprod N
    simpa [Gi, Wi, A, Ai, c, (hyseq N).1] using hprodN
  · intro N
    calc
      WeakGridSpace.BesovishSpace.Norm_Costpq Ai q (yseq N)
          ≤ K * WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi c := (hyseq N).2
      _ = K * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
            rw [hcost_eq]
  · intro η hη
    have hden_pos : 0 < K + 1 := by linarith
    have hδ_pos : 0 < η / (K + 1) := by positivity
    rcases CoeffPQCost_window_tail_tendsto_zero
        Gi p q c hp_top hq_top hc (η / (K + 1)) hδ_pos with
      ⟨N₀, hN₀⟩
    refine ⟨N₀, ?_⟩
    intro M hM N hN
    by_cases hMN : M ≤ N
    · have htail := hN₀ M hM N hMN
      have hwin := hwindow_bound M N hMN
      calc
        WeakGridSpace.BesovishSpace.Norm_Costpq Ai q (yseq N - yseq M)
            ≤ K * WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi
                (fun i Q => if M ≤ i ∧ i < N then c i Q else 0) := hwin
        _ ≤ K * (η / (K + 1)) := by
              exact mul_le_mul_of_nonneg_left (le_of_lt htail) hK
        _ < η := by
              have hfrac : K / (K + 1) < (1 : ℝ) :=
                (div_lt_one hden_pos).2 (by linarith)
              have hmul : (K / (K + 1)) * η < (1 : ℝ) * η :=
                mul_lt_mul_of_pos_right hfrac hη
              calc
                K * (η / (K + 1)) = (K / (K + 1)) * η := by ring
                _ < η := by simpa using hmul
    · have hNM : N ≤ M := Nat.le_of_not_ge hMN
      have htail := hN₀ N hN M hNM
      have hwin := hwindow_bound N M hNM
      have hnorm_eq :
          WeakGridSpace.BesovishSpace.Norm_Costpq Ai q (yseq N - yseq M) =
            WeakGridSpace.BesovishSpace.Norm_Costpq Ai q (yseq M - yseq N) := by
        have hneg : yseq N - yseq M = (-1 : ℂ) • (yseq M - yseq N) := by
          calc
            yseq N - yseq M = -(yseq M - yseq N) := by simp
            _ = (-1 : ℂ) • (yseq M - yseq N) := by simp
        rw [hneg]
        rw [WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq
          (A := Ai) (q := q) hp_top
          (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := Ai) q)]
        simp
      calc
        WeakGridSpace.BesovishSpace.Norm_Costpq Ai q (yseq N - yseq M)
            = WeakGridSpace.BesovishSpace.Norm_Costpq Ai q (yseq M - yseq N) :=
              hnorm_eq
        _ ≤ K * WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi
                (fun i Q => if N ≤ i ∧ i < M then c i Q else 0) := hwin
        _ ≤ K * (η / (K + 1)) := by
              exact mul_le_mul_of_nonneg_left (le_of_lt htail) hK
        _ < η := by
              have hfrac : K / (K + 1) < (1 : ℝ) :=
                (div_lt_one hden_pos).2 (by linarith)
              have hmul : (K / (K + 1)) * η < (1 : ℝ) * η :=
                mul_lt_mul_of_pos_right hfrac hη
              calc
                K * (η / (K + 1)) = (K / (K + 1)) * η := by ring
                _ < η := by simpa using hmul

/--
Endpoint `q = ∞` restriction transmutation theorem for good-grid cell
indicators.

Unlike the finite-`q` theorem, this proof does not ask the restricted initial
segments to be Cauchy in the `q = ∞` Besov gauge.  It uses the endpoint
transmutation limit directly: the restricted partial sums converge strongly in
`L^p`, and the limiting representation has uniformly controlled `ℓ∞`
coefficient cost.
-/
private theorem souzaIndicatorPointwiseMultiplier_of_restrictionTransmutation_top
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hs_le_inv : s ≤ (p.toReal)⁻¹)
    (W : GoodGridCell G)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1) :
    SouzaPointwiseMultiplier G s p ∞ hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ)) := by
  classical
  haveI : Fact ((1 : ℝ≥0∞) ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  let Gi := G.toWeakGridSpace
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace W.toLevelCell
  let A := souzaAtomFamily G s p hs hp hp_top
  let Ai := WeakGridSpace.inducedAtomFamily G.toWeakGridSpace W.toLevelCell A
  let K := souzaRestrictionMultiplierConstant G p W lam
  have hccoef_nonneg : 0 ≤
      WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
        (WeakGridSpace.transmutationKernelZ lam (-(W.level : ℝ)) 1) :=
    cCoefficientInt_nonneg_of_nonneg p ∞ _
      (transmutationKernelZ_nonneg lam (-(W.level : ℝ)) 1 hlam_pos)
  have hK : 0 ≤ K := by
    dsimp [K, souzaRestrictionMultiplierConstant]
    exact mul_nonneg
      (by exact_mod_cast Nat.zero_le G.toWeakGridSpace.grid.Cmult1)
      hccoef_nonneg
  refine souzaIndicatorPointwiseMultiplier_of_restrictionBound
    G s p ∞ hs hp hp_top W hK ?_
  intro g R hRfin
  rcases restrict_souzaRepresentation_transmutationData
      G s p ∞ hs hp hp_top hs_le_inv W lam hlam_pos hlam_lt R with
    ⟨h, Rt, hRt, hprod⟩
  let c : (i : ℕ) → WeakGridSpace.LevelCell Gi i → ℂ :=
    fun i Q => (R.block i).coeff Q
  have hc : WeakGridSpace.CoeffFinitePQCost
      (p := p) (q := ∞) Gi c := by
    simpa [Gi, c, WeakGridSpace.CoeffFinitePQCost,
      WeakGridSpace.CoeffPLevel, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hRfin
  have hcost_eq :
      WeakGridSpace.CoeffPQCost (p := p) (q := ∞) Gi c =
        WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) R := by
    simp [Gi, c, WeakGridSpace.CoeffPQCost, WeakGridSpace.CoeffPLevel,
      WeakGridSpace.LpGridRepresentation.pqCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower]
  rcases WeakGridSpace.Transmutation_of_Atoms_Claim_A_top
      (G := Gi) (W := Wi) (AW := Ai)
      (p := p) (u := ∞)
      W.restrictionLevel (-(W.level : ℝ)) 0 1 (by norm_num)
      W.restrictionLevel_bound
      lam hlam_pos hlam_lt 1 (by norm_num) h Rt hRt c hc
      (induced_souza_assumptionG2 G s p ∞ hs hp hp_top W)
      hp_top hs with
    ⟨gLim, hsum, hmem, htail⟩
  rcases htail with ⟨hfin, htail'⟩
  rcases htail' with ⟨htendsto, hcost⟩
  let Rlim : WeakGridSpace.LpGridRepresentation Ai gLim :=
    { block := WeakGridSpace.TransmutationBlockLimit Gi Wi Ai h Rt c (-(W.level : ℝ)) 1
      hasSum := hsum }
  let y : WeakGridSpace.BesovishSpace Ai ∞ := ⟨gLim, hmem⟩
  have hprod_lim :
      WeakGridSpace.RepresentsPointwiseProduct
        (G := Wi) (p := p)
        (W.cell.indicator fun _ => (1 : ℂ))
        (g : Lp ℂ p Gi.measure)
        (y : Lp ℂ p Wi.measure) := by
    let partialSum : ℕ → Lp ℂ p Wi.measure := fun N =>
      ((∑ k ∈ Finset.range N, (R.block k).toLp A) :
        Lp ℂ p Gi.measure)
    have hx :
        Filter.Tendsto partialSum Filter.atTop
          (𝓝 (g : Lp ℂ p Wi.measure)) := by
      simpa [partialSum, A, Wi, Gi, WeakGridSpace.inducedWeakGridSpace,
        WeakGridSpace.inducedWeakGrid, WeakGridSpace.WeakGridSpace.measure] using
        R.hasSum.tendsto_sum_nat
    exact WeakGridSpace.RepresentsPointwiseProduct.of_tendsto_Lp
      (G := Wi) (p := p)
      (m := W.cell.indicator fun _ => (1 : ℂ))
      (xseq := partialSum)
      (yseq := fun N => WeakGridSpace.PartialSumLevels Gi Wi h c N)
      (x := (g : Lp ℂ p Wi.measure))
      (y := (gLim : Lp ℂ p Wi.measure))
      hx htendsto (by
        intro N
        simpa [partialSum, A, Gi, Wi, c] using hprod N)
  refine ⟨y, hprod_lim, ?_⟩
  have hNorm_le_cost :
      WeakGridSpace.BesovishSpace.Norm_Costpq Ai ∞ y ≤
        WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rlim :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
      (A := Ai) (q := ∞) (g := y) Rlim hfin
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq Ai ∞ y
        ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rlim := hNorm_le_cost
    _ ≤ K * WeakGridSpace.CoeffPQCost (p := p) (q := ∞) Gi c := by
          simpa [Rlim, Gi, Wi, Ai, A, K, c, souzaRestrictionMultiplierConstant] using hcost
    _ = K * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) R := by
          rw [hcost_eq]

/--
Restriction transmutation theorem for good-grid cell indicators.

For every `q >= 1`, including the endpoint `q = ∞`, restricting Souza atoms to
a good-grid cell and transmuting the resulting one-block representatives proves
that the indicator of the cell is a pointwise multiplier.
-/
theorem souzaIndicatorPointwiseMultiplier_of_restrictionTransmutation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hs_le_inv : s ≤ (p.toReal)⁻¹)
    (W : GoodGridCell G)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1) :
    SouzaPointwiseMultiplier G s p q hs hp hp_top
      (W.cell.indicator fun _ => (1 : ℂ)) := by
  classical
  by_cases hq_top : q = ∞
  · subst q
    exact souzaIndicatorPointwiseMultiplier_of_restrictionTransmutation_top
      G s p hs hp hp_top hs_le_inv W lam hlam_pos hlam_lt
  · exact souzaIndicatorPointwiseMultiplier_of_restrictionTransmutation_finite
      G s p q hs hp hp_top hq_top hs_le_inv W lam hlam_pos hlam_lt

/--
For Souza atoms, every pointwise multiplier belongs to the `selfs` class.
-/
theorem souzaPointwiseSelfsClass_of_souzaPointwiseMultiplier
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {m : α → ℂ}
    (hm : SouzaPointwiseMultiplier G s p q hs hp hp_top m) :
    SouzaPointwiseSelfsClass G s p q hs hp hp_top m := by
  exact WeakGridSpace.pointwiseSelfsClass_of_isPointwiseMultiplier
    (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
    (A := souzaAtomFamily G s p hs hp hp_top) (m := m) hm

end

end GoodGridSpace
