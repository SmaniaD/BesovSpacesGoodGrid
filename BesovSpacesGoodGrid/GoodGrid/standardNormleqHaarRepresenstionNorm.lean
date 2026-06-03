import BesovSpacesGoodGrid.GoodGrid.standardRepresentation

/-!
# The standard atomic norm is controlled by the Haar norm

This file records the one-sided comparison from the paper: after the Haar
blocks are regrouped into the standard Souza representation, the standard
coefficient gauge is bounded by a grid-dependent constant times the
`L²`-normalized Haar coefficient gauge.

The quantitative argument follows the manuscript estimate

`∑_P |k_P|^p ≤ C ∑_Q μ(Q)^(1 - s p - p/2) ∑_{S ∈ H_Q} |d_S|^p`.

The remaining work is deliberately split into reusable lemmas: a finite
incidence bound for the binary refinement, the coefficient estimate inside one
parent cell, the levelwise comparison, and the final `(p,q)` gauge comparison.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace StandardAtomicRepresentation

private theorem children_pairwiseDisjoint
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) :
    Set.PairwiseDisjoint
      (↑((HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell) : Set (Set α)) id := by
  intro A hA B hB hAB
  have hA_child :
      A ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell :=
    ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell A).1 hA
  have hB_child :
      B ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell :=
    ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell B).1 hB
  exact G.grid.grid.disjoint (Q.level + 1) A B hA_child.1 hB_child.1 hAB

private theorem children_iUnion_eq_cell
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) :
    (⋃ s ∈ (↑((HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell) : Set (Set α)), s) =
      Q.cell := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases (by simpa using hx) with ⟨s, hs, hxs⟩
    have hs_child :
        s ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell :=
      ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell s).1 hs
    exact hs_child.2 hxs
  · intro x hx
    have hx' :
        x ∈ ⋃ s ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell, s :=
      (HaarRepresentation.GridOf G).covering_by_children Q.level Q.cell Q.mem hx
    rcases (by simpa using hx') with ⟨s, hs, hxs⟩
    have hs_fin :
        s ∈ (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell :=
      ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell s).2 hs
    exact by
      simpa using (show x ∈ ⋃ s ∈
        (↑((HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell) : Set (Set α)), s from
          Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hs_fin, hxs⟩⟩)

private theorem children_measure_toReal_sum_eq
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) :
    (∑ s ∈ (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell,
        (G.grid.μ s).toReal) =
      (G.grid.μ Q.cell).toReal := by
  classical
  let C := (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell
  have hmeasure :
      G.grid.μ Q.cell = ∑ s ∈ C, G.grid.μ s := by
    rw [← children_iUnion_eq_cell G Q]
    exact (MeasureTheory.measure_biUnion_finset
      (μ := G.grid.μ)
      (children_pairwiseDisjoint G Q)
      (fun s hs => G.grid.grid.measurable (Q.level + 1) s
        (((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell s).1 hs).1)).symm
  have hfinite : ∀ s ∈ C, G.grid.μ s ≠ ∞ := by
    intro s hs
    exact MeasureTheory.measure_ne_top G.grid.μ s
  calc
    (∑ s ∈ C, (G.grid.μ s).toReal)
        = (∑ s ∈ C, G.grid.μ s).toReal := by
          rw [ENNReal.toReal_sum hfinite]
    _ = (G.grid.μ Q.cell).toReal := by
          rw [← hmeasure]

private theorem children_card_le_of_lt_inv_lambda1
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G)
    {N : ℕ} (hN : 1 / G.grid.lambda1 < (N : ℝ)) :
    ((HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell).card ≤ N := by
  classical
  let C := (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell
  have hQ_pos :
      0 < (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have hchild_lower :
      ∀ s ∈ C, G.grid.lambda1 * (G.grid.μ Q.cell).toReal ≤ (G.grid.μ s).toReal := by
    intro s hs
    have hs_child :
        s ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell :=
      ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell s).1 hs
    have hs_lower :
        ENNReal.ofReal G.grid.lambda1 * G.grid.μ Q.cell ≤ G.grid.μ s :=
      G.grid.ratio_lower Q.level s Q.cell hs_child.1 Q.mem hs_child.2
    have htoReal :=
      ENNReal.toReal_mono (MeasureTheory.measure_ne_top G.grid.μ s) hs_lower
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal G.grid.hlambda1_pos.le,
      GoodGridCell.measure_ne_top Q] using htoReal
  have hsum_lower :
      (C.card : ℝ) * (G.grid.lambda1 * (G.grid.μ Q.cell).toReal) ≤
        (G.grid.μ Q.cell).toReal := by
    calc
      (C.card : ℝ) * (G.grid.lambda1 * (G.grid.μ Q.cell).toReal)
          = ∑ s ∈ C, G.grid.lambda1 * (G.grid.μ Q.cell).toReal := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ s ∈ C, (G.grid.μ s).toReal := by
              exact Finset.sum_le_sum hchild_lower
      _ = (G.grid.μ Q.cell).toReal := children_measure_toReal_sum_eq G Q
  have hcard_mul_le_one :
      (C.card : ℝ) * G.grid.lambda1 ≤ 1 := by
    have h :=
      (mul_le_mul_iff_of_pos_right hQ_pos).1 ?_
    · simpa [mul_assoc, mul_comm, mul_left_comm] using h
    · simpa [mul_assoc, mul_comm, mul_left_comm] using hsum_lower
  have hcard_lt_N : (C.card : ℝ) < (N : ℝ) := by
    have hλ_pos := G.grid.hlambda1_pos
    have hcard_le_inv : (C.card : ℝ) ≤ 1 / G.grid.lambda1 := by
      exact (le_div_iff₀ hλ_pos).2 (by simpa [mul_comm] using hcard_mul_le_one)
    exact lt_of_le_of_lt hcard_le_inv hN
  exact Nat.le_of_lt_succ (by exact_mod_cast hcard_lt_N)

private theorem branch_incidence_sum_le_of_children_card_le
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G) {N : ℕ}
    (hN : ((HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell).card ≤ N) :
    (∑ b ∈ HaarRepresentation.indicesInCell G F Q,
      (branchCells (G := G) (F := F) (Q := Q) b).card) ≤
        (2 ^ N * 2 ^ N) * N := by
  classical
  let T := F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem
  let C := (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell
  have hT_childs : T.Childs = C := by
    ext s
    exact F.toHaarSystem.binaryRefinement.childs_are_children Q.level Q.cell Q.mem s |>.trans
      ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell s).symm
  have hbranch_card_le : ∀ p ∈ T.Branches, (p.1 ∪ p.2).card ≤ N := by
    intro p hp
    have hp_childs : p.1 ⊆ T.Childs ∧ p.2 ⊆ T.Childs :=
      T.TreeStructureChilds p hp
    have hsubset : p.1 ∪ p.2 ⊆ C := by
      rw [← hT_childs]
      exact Finset.union_subset hp_childs.1 hp_childs.2
    exact (Finset.card_le_card hsubset).trans hN
  have hbranches_card_le :
      T.Branches.card ≤ 2 ^ N * 2 ^ N := by
    have hsubset :
        T.Branches ⊆ T.Childs.powerset.product T.Childs.powerset := by
      intro p hp
      have hp_childs := T.TreeStructureChilds p hp
      simp [Finset.mem_product, Finset.mem_powerset, hp_childs.1, hp_childs.2]
    calc
      T.Branches.card ≤ (T.Childs.powerset.product T.Childs.powerset).card :=
        Finset.card_le_card hsubset
      _ = 2 ^ T.Childs.card * 2 ^ T.Childs.card := by
        simp [Finset.card_product, Finset.card_powerset]
      _ ≤ 2 ^ N * 2 ^ N := by
        have hchilds_card : T.Childs.card ≤ N := by
          simpa [hT_childs] using hN
        exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hchilds_card)
          (Nat.pow_le_pow_right (by norm_num) hchilds_card)
  calc
    (∑ b ∈ HaarRepresentation.indicesInCell G F Q,
      (branchCells (G := G) (F := F) (Q := Q) b).card)
        ≤ ∑ b ∈ HaarRepresentation.indicesInCell G F Q, N := by
          refine Finset.sum_le_sum ?_
          intro b hb
          exact hbranch_card_le b.1 b.2
    _ = (HaarRepresentation.indicesInCell G F Q).card * N := by
          rw [Finset.sum_const_nat]
          intro b hb
          rfl
    _ = T.Branches.card * N := by
          simp [HaarRepresentation.indicesInCell, T]
    _ ≤ (2 ^ N * 2 ^ N) * N := by
          exact Nat.mul_le_mul_right N hbranches_card_le

/--
Uniform bound for the finite incidence number in one parent cell.

This is the formal version of the manuscript estimate
`sup_Q ∑_{S ∈ H_Q} #(S₁ ∪ S₂) ≤ menor^{-2}`.  The bound is stated as an
existential natural number because it is purely combinatorial.
-/
theorem exists_branchIncidenceBound
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G)) :
    ∃ M : ℕ,
      ∀ Q : GoodGridCell G,
        (∑ b ∈ HaarRepresentation.indicesInCell G F Q,
          (branchCells (G := G) (F := F) (Q := Q) b).card) ≤ M := by
  classical
  rcases exists_nat_gt (1 / G.grid.lambda1) with ⟨N, hN⟩
  refine ⟨(2 ^ N * 2 ^ N) * N, ?_⟩
  intro Q
  exact branch_incidence_sum_le_of_children_card_le G F Q
    (children_card_le_of_lt_inv_lambda1 G Q hN)

/--
The standard child coefficient is bounded by the positive coefficient mass
`\tilde{k}_P`.

This is the local triangle-inequality step behind the standard representation:
the canonical Souza atom has exactly the Souza normalization on `P`, while
`tildeAtom_isSouzaAtom` bounds the averaged atom by the same size.
-/
theorem norm_standardChildCoeff_le_tildeCoeff
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1)) :
    ‖standardChildCoeff G F s p f hf Q P‖ ≤
      tildeCoeff G F (c₂ G) p s f hf Q P := by
  classical
  let Pcell := childToGoodGridCell (G := G) (Q := Q) P
  let x₀ := cellPoint G Pcell
  let r : ℝ := (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹)
  let T : ℝ := tildeCoeff G F (c₂ G) p s f hf Q P
  have hx₀ : x₀ ∈ Pcell.cell := by
    simpa [x₀, Pcell] using cellPoint_mem G Pcell
  have hm_pos : 0 < (G.grid.μ P.1).toReal := by
    have hm_pos_en : 0 < G.grid.μ P.1 :=
      G.grid.positive_measure (Q.level + 1) P.1 P.2
    letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
    have hm_ne_top : G.grid.μ P.1 ≠ ∞ :=
      MeasureTheory.measure_ne_top G.grid.μ P.1
    exact ENNReal.toReal_pos hm_pos_en.ne' hm_ne_top
  have hr_pos : 0 < r := by
    exact Real.rpow_pos_of_pos hm_pos _
  have hT_nonneg : 0 ≤ T := by
    simp [T, tildeCoeff]
    exact Finset.sum_nonneg fun b _ => by
      by_cases hbP : branchContainsCell G F Q P b
      · simp [hbP]
      · simp [hbP]
  have hcanon :
      canonicalSouzaAtom G s p Pcell x₀ = ((r : ℝ) : ℂ) := by
    unfold canonicalSouzaAtom
    rw [dif_pos hx₀]
    simp [Pcell, childToGoodGridCell, r]
  have heq :=
    standardChildCoeff_mul_canonicalSouzaAtom_eq_tildeCoeff_mul_tildeAtom
      G F p s f hf Q P x₀
  rw [hcanon] at heq
  have hnorm_eq :
      ‖standardChildCoeff G F s p f hf Q P‖ * r =
        T * ‖tildeAtom G F (c₂ G) p s f hf Q P x₀‖ := by
    have hnorm := congrArg norm heq
    rw [norm_mul, Complex.norm_of_nonneg hr_pos.le] at hnorm
    rw [norm_mul, Complex.norm_of_nonneg hT_nonneg] at hnorm
    simpa [T, mul_comm, mul_left_comm, mul_assoc] using hnorm
  have htilde :
      ‖tildeAtom G F (c₂ G) p s f hf Q P x₀‖ ≤ r := by
    simpa [x₀, Pcell, r] using tildeAtom_norm_bound G F p s f hf Q P
  have hmul :
      ‖standardChildCoeff G F s p f hf Q P‖ * r ≤ T * r := by
    rw [hnorm_eq]
    exact mul_le_mul_of_nonneg_left htilde hT_nonneg
  exact le_of_mul_le_mul_right hmul hr_pos

/--
Levelwise coefficient comparison between the standard Souza coefficients and
the `L²` Haar block at the same parent level.

This packages the estimate in the user-supplied proof sketch.  The constant is
finite and depends only on the good-grid geometry and the parameters `s,p`, not
on the function `f` or the level `k`.
-/
theorem exists_standardPositiveLevelCoeffRoot_le_const_mul_levelHaarBlockRoot
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_one : 1 < p) (hp_top : p < ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : MemLp f p G.grid.μ) (hfint : Integrable f G.grid.μ) (k : ℕ),
        ENNReal.ofReal
            (((standardLpGridRepresentation G F s hs p hp_one hp_top f hf).levelCoeffPower
                (k + 1)) ^ (1 / p.toReal)) ≤
          C * (HaarRepresentation.levelHaarBlock G F s p f hfint k) ^ (1 / p.toReal) := by
  classical
  sorry

/--
The level-zero coefficient root of the packaged standard representation is
controlled by the father term of the Haar norm.
-/
theorem exists_standardFatherLevelCoeffRoot_le_const_mul_fatherTerm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_one : 1 < p) (hp_top : p < ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : MemLp f p G.grid.μ) (hfint : Integrable f G.grid.μ),
        ENNReal.ofReal
            (((standardLpGridRepresentation G F s hs p hp_one hp_top f hf).levelCoeffPower 0) ^
              (1 / p.toReal)) ≤
          C * HaarRepresentation.fatherTerm G F s p f hfint := by
  classical
  sorry

/--
Pass from pointwise level estimates to the full `(p,q)` extended coefficient
gauge.

This is the `q = ∞`/`q < ∞` bookkeeping step.  It mirrors the helper
`qGauge_le_const_mul` used for the two Haar gauges, but is stated directly for
the shifted standard representation levels.
-/
theorem standardRepresentationNorm_le_of_level_bounds
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_one : 1 < p) (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (C0 Cpos : ℝ≥0∞) (hC0 : C0 ≠ ∞) (hCpos : Cpos ≠ ∞)
    (f : α → ℂ) (hf : MemLp f p G.grid.μ) (hfint : Integrable f G.grid.μ) :
    ENNReal.ofReal
        (((standardLpGridRepresentation G F s hs p hp_one hp_top f hf).levelCoeffPower 0) ^
          (1 / p.toReal)) ≤
        C0 * HaarRepresentation.fatherTerm G F s p f hfint →
    (∀ k,
      ENNReal.ofReal
        (((standardLpGridRepresentation G F s hs p hp_one hp_top f hf).levelCoeffPower (k + 1)) ^
          (1 / p.toReal)) ≤
        Cpos * (HaarRepresentation.levelHaarBlock G F s p f hfint k) ^ (1 / p.toReal)) →
      standardRepresentationNorm G F s hs p hp_one hp_top q f hf ≤
        (C0 + Cpos) * HaarRepresentation.haarL2RepresentationNorm G F s p q f hfint := by
  classical
  sorry

/--
Finite Haar `L²` representation norm controls the standard atomic norm.

For fixed good grid, full Haar system, and Besov parameters, there is a finite
constant `C` such that every `L^p` function whose Haar representation norm is
finite has finite standard representation norm, and the standard norm is at
most `C` times the Haar norm.
-/
theorem exists_standardRepresentationNorm_le_const_mul_haarL2RepresentationNorm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) (hp_one : 1 < p) (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hf : MemLp f p G.grid.μ) (hfint : Integrable f G.grid.μ),
        HaarRepresentation.haarL2RepresentationNorm G F s p q f hfint ≠ ∞ →
          standardRepresentationNorm G F s hs p hp_one hp_top q f hf ≠ ∞ ∧
            standardRepresentationNorm G F s hs p hp_one hp_top q f hf ≤
              C * HaarRepresentation.haarL2RepresentationNorm G F s p q f hfint := by
  classical
  letI : Fact (1 ≤ p) := ⟨le_of_lt hp_one⟩
  rcases exists_standardFatherLevelCoeffRoot_le_const_mul_fatherTerm
      G F s hs p hp_one hp_top with
    ⟨C0, hC0_fin, hfather⟩
  rcases exists_standardPositiveLevelCoeffRoot_le_const_mul_levelHaarBlockRoot
      G F s hs p hp_one hp_top with
    ⟨Cpos, hCpos_fin, hlevel⟩
  refine ⟨C0 + Cpos, ENNReal.Finiteness.add_ne_top hC0_fin hCpos_fin, ?_⟩
  intro f hf hfint
  intro hhaar_fin
  have hfather' :
        ENNReal.ofReal
          (((standardLpGridRepresentation G F s hs p hp_one hp_top f hf).levelCoeffPower 0) ^
            (1 / p.toReal)) ≤
        C0 * HaarRepresentation.fatherTerm G F s p f hfint := by
    simpa using hfather f hf hfint
  have hlevel' :
      ∀ k,
        ENNReal.ofReal
          (((standardLpGridRepresentation G F s hs p hp_one hp_top f hf).levelCoeffPower (k + 1)) ^
            (1 / p.toReal)) ≤
          Cpos * (HaarRepresentation.levelHaarBlock G F s p f hfint k) ^ (1 / p.toReal) := by
    simpa using hlevel f hf hfint
  have hnorm_le :
      standardRepresentationNorm G F s hs p hp_one hp_top q f hf ≤
        (C0 + Cpos) * HaarRepresentation.haarL2RepresentationNorm G F s p q f hfint :=
    standardRepresentationNorm_le_of_level_bounds G F s hs p hp_one hp_top q
      C0 Cpos hC0_fin hCpos_fin f hf hfint hfather' hlevel'
  have hstandard_fin :
      standardRepresentationNorm G F s hs p hp_one hp_top q f hf ≠ ∞ := by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.Finiteness.add_ne_top hC0_fin hCpos_fin) hhaar_fin)
      hnorm_le
  exact ⟨hstandard_fin, hnorm_le⟩

end StandardAtomicRepresentation

end

end GoodGridSpace
