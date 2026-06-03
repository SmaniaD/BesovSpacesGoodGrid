import BesovSpacesGoodGrid.GoodGrid.standardRepresentation

/-!
# The standard atomic norm is controlled by the Haar norm

This file records the one-sided comparison from the paper: after the Haar
blocks are regrouped into the standard Souza representation, the standard
coefficient gauge is bounded by a grid-dependent constant times the
`L²`-normalized Haar coefficient gauge.

The quantitative argument follows the manuscript estimate

`∑_P |k_P|^p ≤ C ∑_Q μ(Q)^(1 - s p - p/2) ∑_{S ∈ H_Q} |d_S|^p`.

The quantitative work is deliberately split into reusable lemmas: a finite
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
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  let C := (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell
  have hmeasure :
      G.grid.μ Q.cell = ∑ s ∈ C, G.grid.μ s := by
    rw [← children_iUnion_eq_cell G Q]
    simpa [C] using MeasureTheory.measure_biUnion_finset
      (μ := G.grid.μ)
      (children_pairwiseDisjoint G Q)
      (fun s hs => G.grid.grid.measurable (Q.level + 1) s
        (((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell s).1 hs).1)
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
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
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
    have hmul :
        ((C.card : ℝ) * G.grid.lambda1) * (G.grid.μ Q.cell).toReal ≤
          1 * (G.grid.μ Q.cell).toReal := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hsum_lower
    exact (mul_le_mul_iff_of_pos_right hQ_pos).1 hmul
  have hcard_lt_N : (C.card : ℝ) < (N : ℝ) := by
    have hlambda_pos := G.grid.hlambda1_pos
    have hcard_le_inv : (C.card : ℝ) ≤ 1 / G.grid.lambda1 := by
      exact (le_div_iff₀ hlambda_pos).2 (by simpa [mul_comm] using hcard_mul_le_one)
    exact lt_of_le_of_lt hcard_le_inv hN
  exact_mod_cast (le_of_lt hcard_lt_N)

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

private theorem childrenOfCell_card_le_of_lt_inv_lambda1
    (G : GoodGridSpace (α := α)) (Q : GoodGridCell G)
    {N : ℕ} (hN : 1 / G.grid.lambda1 < (N : ℝ)) :
    (childrenOfCell G Q).card ≤ N := by
  classical
  have hcard :
      (childrenOfCell G Q).card ≤
        ((HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell).card := by
    let C := (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell
    let φ : {P // P ∈ C} → WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1) :=
      fun P =>
        ⟨P.1, ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell P.1).1
          P.2 |>.1⟩
    calc
      (childrenOfCell G Q).card = (C.attach.image φ).card := by
        rfl
      _ ≤ C.attach.card := by
        exact Finset.card_image_le
      _ = C.card := by
        simp
  exact hcard.trans (children_card_le_of_lt_inv_lambda1 G Q hN)

private theorem indicesInCell_card_le_of_children_card_le
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G) {N : ℕ}
    (hN : ((HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell).card ≤ N) :
    (HaarRepresentation.indicesInCell G F Q).card ≤ 2 ^ N * 2 ^ N := by
  classical
  let T := F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem
  let C := (HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell
  have hT_childs : T.Childs = C := by
    ext s
    exact F.toHaarSystem.binaryRefinement.childs_are_children Q.level Q.cell Q.mem s |>.trans
      ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell s).symm
  have hsubset :
      T.Branches ⊆ T.Childs.powerset.product T.Childs.powerset := by
    intro p hp
    have hp_childs := T.TreeStructureChilds p hp
    simp [Finset.mem_product, Finset.mem_powerset, hp_childs.1, hp_childs.2]
  calc
    (HaarRepresentation.indicesInCell G F Q).card = T.Branches.card := by
      simp [HaarRepresentation.indicesInCell, T]
    _ ≤ (T.Childs.powerset.product T.Childs.powerset).card :=
      Finset.card_le_card hsubset
    _ = 2 ^ T.Childs.card * 2 ^ T.Childs.card := by
      simp [Finset.card_product, Finset.card_powerset]
    _ ≤ 2 ^ N * 2 ^ N := by
      have hchilds_card : T.Childs.card ≤ N := by
        simpa [hT_childs] using hN
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hchilds_card)
        (Nat.pow_le_pow_right (by norm_num) hchilds_card)

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

private theorem norm_branchCellCoeff_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖ =
      c₂ G * (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) *
        (G.grid.μ P.1).toReal ^ (1 / p.toReal - s) *
          ‖HaarRepresentation.Coeff G F f hf
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ := by
  have hQ_pos : 0 < (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have hP_pos : 0 < (G.grid.μ P.1).toReal := by
    have hP_pos_en : 0 < G.grid.μ P.1 :=
      G.grid.positive_measure (Q.level + 1) P.1 P.2
    letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact ENNReal.toReal_pos hP_pos_en.ne' (MeasureTheory.measure_ne_top G.grid.μ P.1)
  have hscale_nonneg :
      0 ≤ c₂ G * (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) *
        (G.grid.μ P.1).toReal ^ (1 / p.toReal - s) := by
    exact mul_nonneg
      (mul_nonneg (c₂_pos G).le (Real.rpow_pos_of_pos hQ_pos _).le)
      (Real.rpow_pos_of_pos hP_pos _).le
  have hQ_pow_nonneg : 0 ≤ (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) :=
    (Real.rpow_pos_of_pos hQ_pos _).le
  have hP_pow_nonneg : 0 ≤ (G.grid.μ P.1).toReal ^ (1 / p.toReal - s) :=
    (Real.rpow_pos_of_pos hP_pos _).le
  let scale : ℝ :=
    c₂ G * (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) *
      (G.grid.μ P.1).toReal ^ (1 / p.toReal - s)
  have hscale_eq :
      scale =
        c₂ G * (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) *
          (G.grid.μ P.1).toReal ^ (1 / p.toReal - s) := rfl
  have hscale_nonneg' : 0 ≤ scale := by
    simpa [scale] using hscale_nonneg
  calc
    ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖
        =
          ‖((scale : ℝ) : ℂ)‖ *
            ‖HaarRepresentation.Coeff G F f hf
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ := by
          simp [branchCellCoeff, scale, mul_assoc]
    _ =
        scale *
          ‖HaarRepresentation.Coeff G F f hf
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ := by
          simp [abs_of_nonneg hscale_nonneg']
    _ =
      c₂ G * (G.grid.μ Q.cell).toReal ^ (-(1 : ℝ) / 2) *
        (G.grid.μ P.1).toReal ^ (1 / p.toReal - s) *
          ‖HaarRepresentation.Coeff G F f hf
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ := by
          rw [hscale_eq]

private theorem rpow_le_max_mul_of_mul_le_le_mul
    {a b x q e : ℝ} (ha : 0 < a) (hx : 0 < x) (hq : 0 < q)
    (halower : a * q ≤ x) (hupper : x ≤ b * q) :
    x ^ e ≤ max (a ^ e) (b ^ e) * q ^ e := by
  have hratio_pos : 0 < x / q := div_pos hx hq
  have ha_le_ratio : a ≤ x / q :=
    (le_div_iff₀ hq).2 halower
  have hratio_le_b : x / q ≤ b :=
    (div_le_iff₀ hq).2 hupper
  have hx_eq : (x / q) * q = x := by
    field_simp [hq.ne']
  have hpow_eq : x ^ e = (x / q) ^ e * q ^ e := by
    calc
      x ^ e = ((x / q) * q) ^ e := by rw [hx_eq]
      _ = (x / q) ^ e * q ^ e := by
        rw [Real.mul_rpow hratio_pos.le hq.le]
  have hqpow_nonneg : 0 ≤ q ^ e := Real.rpow_nonneg hq.le e
  rw [hpow_eq]
  refine mul_le_mul_of_nonneg_right ?_ hqpow_nonneg
  by_cases he : 0 ≤ e
  · have hratio_pow_le : (x / q) ^ e ≤ b ^ e :=
      Real.rpow_le_rpow hratio_pos.le hratio_le_b he
    exact hratio_pow_le.trans (le_max_right (a ^ e) (b ^ e))
  · have he_nonpos : e ≤ 0 := le_of_not_ge he
    have hratio_pow_le : (x / q) ^ e ≤ a ^ e :=
      Real.rpow_le_rpow_of_nonpos ha ha_le_ratio he_nonpos
    exact hratio_pow_le.trans (le_max_left (a ^ e) (b ^ e))

private theorem child_measure_rpow_le_gridConst_mul_parent
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞) (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (hP : P ∈ childrenOfCell G Q) :
    (G.grid.μ P.1).toReal ^ (1 / p.toReal - s) ≤
      max (G.grid.lambda1 ^ (1 / p.toReal - s))
        (G.grid.lambda2 ^ (1 / p.toReal - s)) *
        (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s) := by
  letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hQ_pos : 0 < (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have hP_pos : 0 < (G.grid.μ P.1).toReal := by
    have hP_pos_en : 0 < G.grid.μ P.1 :=
      G.grid.positive_measure (Q.level + 1) P.1 P.2
    letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
    exact ENNReal.toReal_pos hP_pos_en.ne' (MeasureTheory.measure_ne_top G.grid.μ P.1)
  have hP_child :
      P.1 ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell :=
    ((HaarRepresentation.GridOf G).mem_childrenFinset_iff Q.level Q.cell P.1).1
      ((mem_childrenOfCell_iff G Q P).1 hP)
  have hlower_en :
      ENNReal.ofReal G.grid.lambda1 * G.grid.μ Q.cell ≤ G.grid.μ P.1 :=
    G.grid.ratio_lower Q.level P.1 Q.cell hP_child.1 Q.mem hP_child.2
  have hupper_en :
      G.grid.μ P.1 ≤ ENNReal.ofReal G.grid.lambda2 * G.grid.μ Q.cell :=
    G.grid.ratio_upper Q.level P.1 Q.cell hP_child.1 Q.mem hP_child.2
  have hlower :
      G.grid.lambda1 * (G.grid.μ Q.cell).toReal ≤ (G.grid.μ P.1).toReal := by
    have htoReal :=
      ENNReal.toReal_mono (MeasureTheory.measure_ne_top G.grid.μ P.1) hlower_en
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal G.grid.hlambda1_pos.le,
      GoodGridCell.measure_ne_top Q] using htoReal
  have hupper :
      (G.grid.μ P.1).toReal ≤
        G.grid.lambda2 * (G.grid.μ Q.cell).toReal := by
    have htoReal :=
      ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (GoodGridCell.measure_ne_top Q))
        hupper_en
    have hlambda2_nonneg : 0 ≤ G.grid.lambda2 :=
      G.grid.hlambda1_pos.le.trans G.grid.hlambda1_le_lambda2
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlambda2_nonneg,
      GoodGridCell.measure_ne_top Q] using htoReal
  exact rpow_le_max_mul_of_mul_le_le_mul G.grid.hlambda1_pos
    hP_pos hQ_pos hlower hupper

private theorem norm_branchCellCoeff_le_parentScale
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (hP : P ∈ childrenOfCell G Q)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖ ≤
      c₂ G *
        max (G.grid.lambda1 ^ (1 / p.toReal - s))
          (G.grid.lambda2 ^ (1 / p.toReal - s)) *
        (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s - 1 / 2) *
        ‖HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ := by
  let μQ := (G.grid.μ Q.cell).toReal
  let μP := (G.grid.μ P.1).toReal
  let K :=
    max (G.grid.lambda1 ^ (1 / p.toReal - s))
      (G.grid.lambda2 ^ (1 / p.toReal - s))
  let d :=
    ‖HaarRepresentation.Coeff G F f hf
      (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖
  have hQ_pos : 0 < μQ := by
    simpa [μQ] using
      ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have hQ_pow_nonneg : 0 ≤ μQ ^ (-(1 : ℝ) / 2) :=
    (Real.rpow_pos_of_pos hQ_pos _).le
  have hd_nonneg : 0 ≤ d := norm_nonneg _
  have hchild :
      μP ^ (1 / p.toReal - s) ≤ K * μQ ^ (1 / p.toReal - s) := by
    simpa [μP, μQ, K] using child_measure_rpow_le_gridConst_mul_parent G s p Q P hP
  have hmul :
      c₂ G * μQ ^ (-(1 : ℝ) / 2) * μP ^ (1 / p.toReal - s) * d ≤
        c₂ G * μQ ^ (-(1 : ℝ) / 2) *
          (K * μQ ^ (1 / p.toReal - s)) * d := by
    refine mul_le_mul_of_nonneg_right ?_ hd_nonneg
    refine mul_le_mul_of_nonneg_left hchild ?_
    exact mul_nonneg (c₂_pos G).le hQ_pow_nonneg
  have hpow :
      μQ ^ (-(1 : ℝ) / 2) * μQ ^ (1 / p.toReal - s) =
        μQ ^ (1 / p.toReal - s - 1 / 2) := by
    rw [← Real.rpow_add hQ_pos]
    ring_nf
  calc
    ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖
        = c₂ G * μQ ^ (-(1 : ℝ) / 2) *
            μP ^ (1 / p.toReal - s) * d := by
          simpa [μQ, μP, d] using norm_branchCellCoeff_eq G F s p f hf Q P b
    _ ≤ c₂ G * μQ ^ (-(1 : ℝ) / 2) *
          (K * μQ ^ (1 / p.toReal - s)) * d := hmul
    _ = c₂ G * K * μQ ^ (1 / p.toReal - s - 1 / 2) * d := by
          rw [← hpow]
          ring

private theorem norm_standardChildCoeff_rpow_le_branch_sum_rpow
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (hP : P ∈ childrenOfCell G Q) :
    ‖standardChildCoeff G F s p f hf Q P‖ ^ p.toReal ≤
      ((HaarRepresentation.indicesInCell G F Q).card : ℝ) ^ (p.toReal - 1) *
        ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
          (c₂ G *
              max (G.grid.lambda1 ^ (1 / p.toReal - s))
                (G.grid.lambda2 ^ (1 / p.toReal - s)) *
              (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s - 1 / 2) *
              ‖HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖) ^ p.toReal := by
  classical
  let S := HaarRepresentation.indicesInCell G F Q
  let scale : ℝ :=
    c₂ G *
      max (G.grid.lambda1 ^ (1 / p.toReal - s))
        (G.grid.lambda2 ^ (1 / p.toReal - s)) *
      (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s - 1 / 2)
  let d :
      {r : Finset (Set α) × Finset (Set α) //
        r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches} → ℝ :=
    fun b =>
      ‖HaarRepresentation.Coeff G F f hf
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖
  have hp_one_real : (1 : ℝ) ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp_top.ne (Fact.out : (1 : ℝ≥0∞) ≤ p)
    simpa using h
  have hp_nonneg : 0 ≤ p.toReal := le_trans (zero_le_one : (0 : ℝ) ≤ 1) hp_one_real
  have hQ_pos : 0 < (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have hlambda2_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  have hK_nonneg :
      0 ≤ max (G.grid.lambda1 ^ (1 / p.toReal - s))
        (G.grid.lambda2 ^ (1 / p.toReal - s)) := by
    exact (Real.rpow_pos_of_pos G.grid.hlambda1_pos _).le.trans
      (le_max_left _ _)
  have hscale_nonneg : 0 ≤ scale := by
    exact mul_nonneg (mul_nonneg (c₂_pos G).le hK_nonneg)
      (Real.rpow_pos_of_pos hQ_pos _).le
  have htilde_nonneg :
      0 ≤ tildeCoeff G F (c₂ G) p s f hf Q P := by
    simp [tildeCoeff]
    exact Finset.sum_nonneg fun b _ => by
      by_cases hbP : branchContainsCell G F Q P b
      · simp [hbP]
      · simp [hbP]
  have htilde_le :
      tildeCoeff G F (c₂ G) p s f hf Q P ≤
        ∑ b ∈ S, scale * d b := by
    calc
      tildeCoeff G F (c₂ G) p s f hf Q P
          = ∑ b ∈ S,
              if branchContainsCell G F Q P b then
                ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖
              else
                0 := by
            simp [S, tildeCoeff]
      _ ≤ ∑ b ∈ S,
              ‖branchCellCoeff G F (c₂ G) p s f hf Q P b‖ := by
            refine Finset.sum_le_sum ?_
            intro b hb
            by_cases hbP : branchContainsCell G F Q P b
            · simp [hbP]
            · simp [hbP]
      _ ≤ ∑ b ∈ S, scale * d b := by
            refine Finset.sum_le_sum ?_
            intro b hb
            simpa [scale, d] using norm_branchCellCoeff_le_parentScale G F s p f hf Q P hP b
  have hstd_le :
      ‖standardChildCoeff G F s p f hf Q P‖ ≤
        ∑ b ∈ S, scale * d b :=
    (norm_standardChildCoeff_le_tildeCoeff G F s p f hf Q P).trans htilde_le
  have hsum_nonneg : 0 ≤ ∑ b ∈ S, scale * d b :=
    Finset.sum_nonneg fun b _ => mul_nonneg hscale_nonneg (norm_nonneg _)
  have hleft :
      ‖standardChildCoeff G F s p f hf Q P‖ ^ p.toReal ≤
        (∑ b ∈ S, scale * d b) ^ p.toReal :=
    Real.rpow_le_rpow (norm_nonneg _) hstd_le hp_nonneg
  have hsum_rpow :
      (∑ b ∈ S, scale * d b) ^ p.toReal ≤
        (S.card : ℝ) ^ (p.toReal - 1) *
          ∑ b ∈ S, (scale * d b) ^ p.toReal :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S hp_one_real
      (fun b _ => mul_nonneg hscale_nonneg (norm_nonneg _))
  calc
    ‖standardChildCoeff G F s p f hf Q P‖ ^ p.toReal
        ≤ (∑ b ∈ S, scale * d b) ^ p.toReal := hleft
    _ ≤ (S.card : ℝ) ^ (p.toReal - 1) *
          ∑ b ∈ S, (scale * d b) ^ p.toReal := hsum_rpow
    _ =
      ((HaarRepresentation.indicesInCell G F Q).card : ℝ) ^ (p.toReal - 1) *
        ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
          (c₂ G *
              max (G.grid.lambda1 ^ (1 / p.toReal - s))
                (G.grid.lambda2 ^ (1 / p.toReal - s)) *
              (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s - 1 / 2) *
              ‖HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖) ^ p.toReal := by
        rfl

private theorem parentScale_coeff_rpow_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hp_pos : 0 < p.toReal)
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    (c₂ G *
        max (G.grid.lambda1 ^ (1 / p.toReal - s))
          (G.grid.lambda2 ^ (1 / p.toReal - s)) *
        (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s - 1 / 2) *
        ‖HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖) ^ p.toReal =
      (c₂ G *
        max (G.grid.lambda1 ^ (1 / p.toReal - s))
          (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal *
        (G.grid.μ Q.cell).toReal ^ (1 - s * p.toReal - p.toReal / 2) *
        ‖HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ ^ p.toReal := by
  let μQ := (G.grid.μ Q.cell).toReal
  let A :=
    c₂ G *
      max (G.grid.lambda1 ^ (1 / p.toReal - s))
        (G.grid.lambda2 ^ (1 / p.toReal - s))
  let d :=
    ‖HaarRepresentation.Coeff G F f hf
      (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖
  have hQ_pos : 0 < μQ := by
    simpa [μQ] using
      ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have hlambda2_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  have hK_nonneg :
      0 ≤ max (G.grid.lambda1 ^ (1 / p.toReal - s))
        (G.grid.lambda2 ^ (1 / p.toReal - s)) := by
    exact (Real.rpow_pos_of_pos G.grid.hlambda1_pos _).le.trans
      (le_max_left _ _)
  have hA_nonneg : 0 ≤ A := by
    exact mul_nonneg (c₂_pos G).le hK_nonneg
  have hμpow_nonneg : 0 ≤ μQ ^ (1 / p.toReal - s - 1 / 2) :=
    (Real.rpow_pos_of_pos hQ_pos _).le
  have hd_nonneg : 0 ≤ d := norm_nonneg _
  have hexp :
      (1 / p.toReal - s - 1 / 2) * p.toReal =
        1 - s * p.toReal - p.toReal / 2 := by
    field_simp [hp_pos.ne']
  calc
    (c₂ G *
        max (G.grid.lambda1 ^ (1 / p.toReal - s))
          (G.grid.lambda2 ^ (1 / p.toReal - s)) *
        (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s - 1 / 2) *
        ‖HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖) ^ p.toReal
        = (A * μQ ^ (1 / p.toReal - s - 1 / 2) * d) ^ p.toReal := by
          rfl
    _ = (A * μQ ^ (1 / p.toReal - s - 1 / 2)) ^ p.toReal * d ^ p.toReal := by
          rw [Real.mul_rpow (mul_nonneg hA_nonneg hμpow_nonneg) hd_nonneg]
    _ = A ^ p.toReal * (μQ ^ (1 / p.toReal - s - 1 / 2)) ^ p.toReal *
          d ^ p.toReal := by
          rw [Real.mul_rpow hA_nonneg hμpow_nonneg]
    _ = A ^ p.toReal * μQ ^ (1 - s * p.toReal - p.toReal / 2) *
          d ^ p.toReal := by
          rw [← Real.rpow_mul hQ_pos.le]
          rw [hexp]
    _ =
      (c₂ G *
        max (G.grid.lambda1 ^ (1 / p.toReal - s))
          (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal *
        (G.grid.μ Q.cell).toReal ^ (1 - s * p.toReal - p.toReal / 2) *
        ‖HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ ^ p.toReal := by
          rfl

private theorem norm_standardChildCoeff_rpow_le_uniform_branch_power
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    {N : ℕ}
    (hN : ((HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell).card ≤ N)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (Q.level + 1))
    (hP : P ∈ childrenOfCell G Q) :
    ‖standardChildCoeff G F s p f hf Q P‖ ^ p.toReal ≤
      ((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) *
        ((c₂ G *
            max (G.grid.lambda1 ^ (1 / p.toReal - s))
              (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal *
          (G.grid.μ Q.cell).toReal ^ (1 - s * p.toReal - p.toReal / 2) *
          ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
            ‖HaarRepresentation.Coeff G F f hf
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ ^ p.toReal) := by
  classical
  let S := HaarRepresentation.indicesInCell G F Q
  let B : ℕ := 2 ^ N * 2 ^ N
  let A :=
    c₂ G *
      max (G.grid.lambda1 ^ (1 / p.toReal - s))
        (G.grid.lambda2 ^ (1 / p.toReal - s))
  let μweight := (G.grid.μ Q.cell).toReal ^ (1 - s * p.toReal - p.toReal / 2)
  let d :
      {r : Finset (Set α) × Finset (Set α) //
        r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches} → ℝ :=
    fun b =>
      ‖HaarRepresentation.Coeff G F f hf
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top.ne
  have hp_one_real : (1 : ℝ) ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp_top.ne (Fact.out : (1 : ℝ≥0∞) ≤ p)
    simpa using h
  have hexp_nonneg : 0 ≤ p.toReal - 1 := sub_nonneg.2 hp_one_real
  have hcard_nat : S.card ≤ B := by
    simpa [S, B] using indicesInCell_card_le_of_children_card_le G F Q hN
  have hcard_real : (S.card : ℝ) ≤ (B : ℝ) := by exact_mod_cast hcard_nat
  have hcard_pow :
      (S.card : ℝ) ^ (p.toReal - 1) ≤ (B : ℝ) ^ (p.toReal - 1) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcard_real hexp_nonneg
  have hQ_pos : 0 < (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
  have hA_nonneg : 0 ≤ A := by
    have hK_nonneg :
        0 ≤ max (G.grid.lambda1 ^ (1 / p.toReal - s))
          (G.grid.lambda2 ^ (1 / p.toReal - s)) := by
      exact (Real.rpow_pos_of_pos G.grid.hlambda1_pos _).le.trans
        (le_max_left _ _)
    exact mul_nonneg (c₂_pos G).le hK_nonneg
  have hμweight_nonneg : 0 ≤ μweight :=
    Real.rpow_nonneg hQ_pos.le _
  have hsum_nonneg :
      0 ≤
        ∑ b ∈ S,
          (c₂ G *
              max (G.grid.lambda1 ^ (1 / p.toReal - s))
                (G.grid.lambda2 ^ (1 / p.toReal - s)) *
              (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s - 1 / 2) *
              ‖HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖) ^ p.toReal := by
    exact Finset.sum_nonneg fun b _ =>
      Real.rpow_nonneg
        (mul_nonneg
          (mul_nonneg hA_nonneg
            (Real.rpow_pos_of_pos hQ_pos _).le)
          (norm_nonneg _)) _
  have hsum_eq :
      (∑ b ∈ S,
          (c₂ G *
              max (G.grid.lambda1 ^ (1 / p.toReal - s))
                (G.grid.lambda2 ^ (1 / p.toReal - s)) *
              (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s - 1 / 2) *
              ‖HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖) ^ p.toReal) =
        A ^ p.toReal * μweight * ∑ b ∈ S, d b ^ p.toReal := by
    calc
      (∑ b ∈ S,
          (c₂ G *
              max (G.grid.lambda1 ^ (1 / p.toReal - s))
                (G.grid.lambda2 ^ (1 / p.toReal - s)) *
              (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s - 1 / 2) *
              ‖HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖) ^ p.toReal)
          =
        ∑ b ∈ S, A ^ p.toReal * μweight * d b ^ p.toReal := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          simpa [A, μweight, d] using parentScale_coeff_rpow_eq G F s p hp_pos f hf Q b
      _ = A ^ p.toReal * μweight * ∑ b ∈ S, d b ^ p.toReal := by
          simp [Finset.mul_sum, mul_assoc]
  have hpoint :=
    norm_standardChildCoeff_rpow_le_branch_sum_rpow G F s p hp_top f hf Q P hP
  calc
    ‖standardChildCoeff G F s p f hf Q P‖ ^ p.toReal
        ≤ (S.card : ℝ) ^ (p.toReal - 1) *
            ∑ b ∈ S,
              (c₂ G *
                  max (G.grid.lambda1 ^ (1 / p.toReal - s))
                    (G.grid.lambda2 ^ (1 / p.toReal - s)) *
                  (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s - 1 / 2) *
                  ‖HaarRepresentation.Coeff G F f hf
                    (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖) ^ p.toReal := by
          simpa [S] using hpoint
    _ ≤ (B : ℝ) ^ (p.toReal - 1) *
            ∑ b ∈ S,
              (c₂ G *
                  max (G.grid.lambda1 ^ (1 / p.toReal - s))
                    (G.grid.lambda2 ^ (1 / p.toReal - s)) *
                  (G.grid.μ Q.cell).toReal ^ (1 / p.toReal - s - 1 / 2) *
                  ‖HaarRepresentation.Coeff G F f hf
                    (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖) ^ p.toReal := by
          exact mul_le_mul_of_nonneg_right hcard_pow hsum_nonneg
    _ = (B : ℝ) ^ (p.toReal - 1) *
          (A ^ p.toReal * μweight * ∑ b ∈ S, d b ^ p.toReal) := by
          rw [hsum_eq]
    _ =
      ((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) *
        ((c₂ G *
            max (G.grid.lambda1 ^ (1 / p.toReal - s))
              (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal *
      (G.grid.μ Q.cell).toReal ^ (1 - s * p.toReal - p.toReal / 2) *
          ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
            ‖HaarRepresentation.Coeff G F f hf
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ ^ p.toReal) := by
          rfl

private theorem standardChildCoeff_children_real_sum_le
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    {N : ℕ} (hN : 1 / G.grid.lambda1 < (N : ℝ)) :
    (∑ P ∈ childrenOfCell G Q,
        ‖standardChildCoeff G F s p f hf Q P‖ ^ p.toReal) ≤
      (N : ℝ) *
        (((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) *
          ((c₂ G *
              max (G.grid.lambda1 ^ (1 / p.toReal - s))
                (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal *
            (G.grid.μ Q.cell).toReal ^ (1 - s * p.toReal - p.toReal / 2) *
            ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
              ‖HaarRepresentation.Coeff G F f hf
                (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ ^ p.toReal)) := by
  classical
  let R : ℝ :=
    ((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) *
      ((c₂ G *
          max (G.grid.lambda1 ^ (1 / p.toReal - s))
            (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal *
        (G.grid.μ Q.cell).toReal ^ (1 - s * p.toReal - p.toReal / 2) *
        ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
          ‖HaarRepresentation.Coeff G F f hf
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ ^ p.toReal)
  have hchildren_card_nat : (childrenOfCell G Q).card ≤ N :=
    childrenOfCell_card_le_of_lt_inv_lambda1 G Q hN
  have hchildren_card : ((childrenOfCell G Q).card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hchildren_card_nat
  have hchildfin_card :
      ((HaarRepresentation.GridOf G).childrenFinset Q.level Q.cell).card ≤ N :=
    children_card_le_of_lt_inv_lambda1 G Q hN
  have hR_nonneg : 0 ≤ R := by
    have hp_one_real : (1 : ℝ) ≤ p.toReal := by
      have h := ENNReal.toReal_mono hp_top.ne (Fact.out : (1 : ℝ≥0∞) ≤ p)
      simpa using h
    have hBpow_nonneg :
        0 ≤ ((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hK_nonneg :
        0 ≤ max (G.grid.lambda1 ^ (1 / p.toReal - s))
          (G.grid.lambda2 ^ (1 / p.toReal - s)) := by
      exact (Real.rpow_pos_of_pos G.grid.hlambda1_pos _).le.trans
        (le_max_left _ _)
    have hA_nonneg :
        0 ≤ (c₂ G *
          max (G.grid.lambda1 ^ (1 / p.toReal - s))
            (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal :=
      Real.rpow_nonneg (mul_nonneg (c₂_pos G).le hK_nonneg) _
    have hQ_pos : 0 < (G.grid.μ Q.cell).toReal :=
      ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne' (GoodGridCell.measure_ne_top Q)
    have hμ_nonneg :
        0 ≤ (G.grid.μ Q.cell).toReal ^ (1 - s * p.toReal - p.toReal / 2) :=
      Real.rpow_nonneg hQ_pos.le _
    have hsum_nonneg :
        0 ≤ ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
          ‖HaarRepresentation.Coeff G F f hf
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ ^ p.toReal :=
      Finset.sum_nonneg fun b _ => Real.rpow_nonneg (norm_nonneg _) _
    exact mul_nonneg hBpow_nonneg
      (mul_nonneg (mul_nonneg hA_nonneg hμ_nonneg) hsum_nonneg)
  calc
    (∑ P ∈ childrenOfCell G Q,
        ‖standardChildCoeff G F s p f hf Q P‖ ^ p.toReal)
        ≤ ∑ P ∈ childrenOfCell G Q, R := by
          refine Finset.sum_le_sum ?_
          intro P hP
          simpa [R] using
            norm_standardChildCoeff_rpow_le_uniform_branch_power G F s p hp_top
              f hf Q hchildfin_card P hP
    _ = ((childrenOfCell G Q).card : ℝ) * R := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * R := by
          exact mul_le_mul_of_nonneg_right hchildren_card hR_nonneg
    _ =
      (N : ℝ) *
        (((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) *
          ((c₂ G *
              max (G.grid.lambda1 ^ (1 / p.toReal - s))
                (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal *
            (G.grid.μ Q.cell).toReal ^ (1 - s * p.toReal - p.toReal / 2) *
            ∑ b ∈ HaarRepresentation.indicesInCell G F Q,
              ‖HaarRepresentation.Coeff G F f hf
              (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))‖ ^ p.toReal)) := by
          rfl

private theorem standardLevelCoeffPower_le_const_mul_levelHaarBlock_of_N
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    {N : ℕ} (hN : 1 / G.grid.lambda1 < (N : ℝ))
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) :
    standardLevelCoeffPower G F s p f hf k ≤
      ENNReal.ofReal
        ((N : ℝ) *
          (((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) *
            (c₂ G *
              max (G.grid.lambda1 ^ (1 / p.toReal - s))
                (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal)) *
        HaarRepresentation.levelHaarBlock G F s p f hf k := by
  classical
  let CReal : ℝ :=
    (N : ℝ) *
      (((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) *
        (c₂ G *
          max (G.grid.lambda1 ^ (1 / p.toReal - s))
            (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal)
  have hCReal_nonneg : 0 ≤ CReal := by
    have hBpow_nonneg :
        0 ≤ ((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hK_nonneg :
        0 ≤ max (G.grid.lambda1 ^ (1 / p.toReal - s))
          (G.grid.lambda2 ^ (1 / p.toReal - s)) := by
      exact (Real.rpow_pos_of_pos G.grid.hlambda1_pos _).le.trans
        (le_max_left _ _)
    have hA_nonneg :
        0 ≤ (c₂ G *
          max (G.grid.lambda1 ^ (1 / p.toReal - s))
            (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal :=
      Real.rpow_nonneg (mul_nonneg (c₂_pos G).le hK_nonneg) _
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hBpow_nonneg hA_nonneg)
  simp only [standardLevelCoeffPower, HaarRepresentation.levelHaarBlock]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro Q hQ
  let Qg : GoodGridCell G := { level := k, cell := Q.1, mem := Q.2 }
  let μweight : ℝ := (G.grid.μ Q.1).toReal ^ (1 - s * p.toReal - p.toReal / 2)
  let dsum : ℝ :=
    ∑ b ∈ HaarRepresentation.indicesInCell G F Qg,
      ‖HaarRepresentation.Coeff G F f hf
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Qg b))‖ ^ p.toReal
  have hμ_nonneg : 0 ≤ μweight := by
    have hQ_pos : 0 < (G.grid.μ Q.1).toReal := by
      simpa [Qg, μweight] using
        ENNReal.toReal_pos (GoodGridCell.measure_pos Qg).ne'
          (GoodGridCell.measure_ne_top Qg)
    exact Real.rpow_nonneg hQ_pos.le _
  have hdsum_nonneg : 0 ≤ dsum := by
    exact Finset.sum_nonneg fun b _ => Real.rpow_nonneg (norm_nonneg _) _
  have hleft_eq :
      (∑ P ∈ childrenOfCell G Qg,
        ENNReal.ofReal
          (‖standardChildCoeff G F s p f hf Qg P‖ ^ p.toReal)) =
        ENNReal.ofReal
          (∑ P ∈ childrenOfCell G Qg,
            ‖standardChildCoeff G F s p f hf Qg P‖ ^ p.toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro P hP
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hcellCoeff_eq :
      HaarRepresentation.cellCoeffPower G F p f hf Qg = ENNReal.ofReal dsum := by
    simp only [HaarRepresentation.cellCoeffPower, dsum]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    intro b hb
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hreal :
      (∑ P ∈ childrenOfCell G Qg,
          ‖standardChildCoeff G F s p f hf Qg P‖ ^ p.toReal) ≤
        CReal * (μweight * dsum) := by
    have h :=
      standardChildCoeff_children_real_sum_le G F s p hp_top f hf Qg hN
    simpa [CReal, μweight, dsum, Qg, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ P ∈ childrenOfCell G Qg,
        ENNReal.ofReal
          (‖standardChildCoeff G F s p f hf Qg P‖ ^ p.toReal))
        = ENNReal.ofReal
          (∑ P ∈ childrenOfCell G Qg,
            ‖standardChildCoeff G F s p f hf Qg P‖ ^ p.toReal) := hleft_eq
    _ ≤ ENNReal.ofReal (CReal * (μweight * dsum)) :=
          ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal CReal *
          (ENNReal.ofReal μweight * HaarRepresentation.cellCoeffPower G F p f hf Qg) := by
          rw [ENNReal.ofReal_mul hCReal_nonneg]
          rw [ENNReal.ofReal_mul hμ_nonneg]
          rw [hcellCoeff_eq]
    _ =
      ENNReal.ofReal
        ((N : ℝ) *
          (((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) *
            (c₂ G *
              max (G.grid.lambda1 ^ (1 / p.toReal - s))
                (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal)) *
        (ENNReal.ofReal ((G.grid.μ Q.1).toReal ^
            (1 - s * p.toReal - p.toReal / 2)) *
          HaarRepresentation.cellCoeffPower G F p f hf
            { level := k, cell := Q.1, mem := Q.2 }) := by
          rfl

private theorem exists_parent_of_level_succ
    (G : GoodGridSpace (α := α)) (k : ℕ)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1)) :
    ∃ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      P ∈ childrenOfCell G ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) := by
  rcases G.grid.grid.nested k P.1 P.2 with ⟨Q, hQ, hPQ⟩
  refine ⟨⟨Q, hQ⟩, ?_⟩
  rw [mem_childrenOfCell_iff]
  exact ((HaarRepresentation.GridOf G).mem_childrenFinset_iff k Q P.1).2 ⟨P.2, hPQ⟩

private theorem child_parent_unique
    (G : GoodGridSpace (α := α)) (k : ℕ)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1))
    (Q R : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (hQ : P ∈ childrenOfCell G
      ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G))
    (hR : P ∈ childrenOfCell G
      ({ level := k, cell := R.1, mem := R.2 } : GoodGridCell G)) :
    Q = R := by
  have hQ_child :
      P.1 ∈ (HaarRepresentation.GridOf G).children k Q.1 :=
    ((HaarRepresentation.GridOf G).mem_childrenFinset_iff k Q.1 P.1).1
      ((mem_childrenOfCell_iff G
        ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P).1 hQ)
  have hR_child :
      P.1 ∈ (HaarRepresentation.GridOf G).children k R.1 :=
    ((HaarRepresentation.GridOf G).mem_childrenFinset_iff k R.1 P.1).1
      ((mem_childrenOfCell_iff G
        ({ level := k, cell := R.1, mem := R.2 } : GoodGridCell G) P).1 hR)
  by_cases hQR : Q.1 = R.1
  · ext x
    rw [hQR]
  · have hdisj : Disjoint Q.1 R.1 :=
      G.grid.grid.disjoint k Q.1 R.1 Q.2 R.2 hQR
    rcases G.grid.partition_nonempty (k + 1) P.1 P.2 with ⟨x, hxP⟩
    exact False.elim ((Set.disjoint_left.mp hdisj) (hQ_child.2 hxP) (hR_child.2 hxP))

private theorem positiveCoeff_parent_sum_bound
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (k : ℕ) (P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1)) :
    ENNReal.ofReal
        (‖∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            if P ∈ childrenOfCell G
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
              standardChildCoeff G F s p f hf
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
            else 0‖ ^ p.toReal) ≤
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ENNReal.ofReal
          (‖if P ∈ childrenOfCell G
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
              standardChildCoeff G F s p f hf
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
            else 0‖ ^ p.toReal) := by
  classical
  rcases exists_parent_of_level_succ G k P with ⟨Q₀, hQ₀⟩
  have hsum :
      (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        if P ∈ childrenOfCell G
          ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
          standardChildCoeff G F s p f hf
            ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
        else 0) =
      standardChildCoeff G F s p f hf
        ({ level := k, cell := Q₀.1, mem := Q₀.2 } : GoodGridCell G) P := by
    rw [Finset.sum_eq_single Q₀]
    · simp [hQ₀]
    · intro Q _ hne
      have hnot :
          ¬ P ∈ childrenOfCell G
            ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) := by
        intro hQ
        exact hne ((child_parent_unique G k P Q₀ Q hQ₀ hQ).symm)
      simp [hnot]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ Q₀))
  calc
    ENNReal.ofReal
        (‖∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            if P ∈ childrenOfCell G
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
              standardChildCoeff G F s p f hf
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
            else 0‖ ^ p.toReal)
        =
      ENNReal.ofReal
        (‖standardChildCoeff G F s p f hf
          ({ level := k, cell := Q₀.1, mem := Q₀.2 } : GoodGridCell G) P‖ ^ p.toReal) := by
        rw [hsum]
    _ ≤
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ENNReal.ofReal
          (‖if P ∈ childrenOfCell G
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
              standardChildCoeff G F s p f hf
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
            else 0‖ ^ p.toReal) := by
        have hterm :
            ENNReal.ofReal
              (‖standardChildCoeff G F s p f hf
                ({ level := k, cell := Q₀.1, mem := Q₀.2 } : GoodGridCell G) P‖ ^
                  p.toReal) =
            ENNReal.ofReal
              (‖if P ∈ childrenOfCell G
                  ({ level := k, cell := Q₀.1, mem := Q₀.2 } : GoodGridCell G) then
                  standardChildCoeff G F s p f hf
                    ({ level := k, cell := Q₀.1, mem := Q₀.2 } : GoodGridCell G) P
                else 0‖ ^ p.toReal) := by
          simp [hQ₀]
        rw [hterm]
        let A : WeakGridSpace.LevelCell G.toWeakGridSpace k → ℝ≥0∞ := fun Q =>
          ENNReal.ofReal
            (‖if P ∈ childrenOfCell G
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
                standardChildCoeff G F s p f hf
                  ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
              else 0‖ ^ p.toReal)
        change A Q₀ ≤ ∑ Q, A Q
        exact Finset.single_le_sum (s := Finset.univ) (f := A)
          (fun Q _ => bot_le) (Finset.mem_univ Q₀)

private theorem sum_all_level_succ_if_child_eq_sum_children
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (hp_pos : 0 < p.toReal)
    (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
        ENNReal.ofReal
          (‖if P ∈ childrenOfCell G
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
              standardChildCoeff G F s p f hf
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
            else 0‖ ^ p.toReal)) =
      ∑ P ∈ childrenOfCell G
          ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G),
        ENNReal.ofReal
          (‖standardChildCoeff G F s p f hf
            ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P‖ ^ p.toReal) := by
  classical
  let Qg : GoodGridCell G := { level := k, cell := Q.1, mem := Q.2 }
  let A : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1) → ℝ≥0∞ := fun P =>
    ENNReal.ofReal
      (‖standardChildCoeff G F s p f hf Qg P‖ ^ p.toReal)
  calc
    (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
        ENNReal.ofReal
          (‖if P ∈ childrenOfCell G
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
              standardChildCoeff G F s p f hf
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
            else 0‖ ^ p.toReal))
        = ∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
            if P ∈ childrenOfCell G Qg then A P else 0 := by
          refine Finset.sum_congr rfl ?_
          intro P hP
          by_cases hchild : P ∈ childrenOfCell G Qg
          · simp [A, Qg, hchild]
          · simp [A, Qg, hchild, Real.zero_rpow hp_pos.ne']
    _ = ∑ P ∈ (Finset.univ.filter fun P =>
            P ∈ childrenOfCell G Qg), A P := by
          rw [Finset.sum_filter]
    _ = ∑ P ∈ childrenOfCell G Qg, A P := by
          refine Finset.sum_congr ?_ ?_
          · ext P
            simp
          · intro P hP
            rfl
    _ = ∑ P ∈ childrenOfCell G
          ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G),
        ENNReal.ofReal
          (‖standardChildCoeff G F s p f hf
            ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P‖ ^ p.toReal) := by
          rfl

private theorem abstract_positive_levelCoeffPower_le_standardLevelCoeffPower
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (f : α → ℂ) (hfint : Integrable f G.grid.μ) (k : ℕ) :
    ENNReal.ofReal (standardBlockCoeffPower G F s hs p hp_top f hfint (k + 1)) ≤
      standardLevelCoeffPower G F s p f hfint k := by
  classical
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
      hp_top.ne
  simp only [standardBlockCoeffPower, canonicalStandardLpGridBlock,
    canonicalStandardPositiveLevelBlock, standardLevelCoeffPower]
  change
    ENNReal.ofReal
        (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
          ‖∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            if P ∈ childrenOfCell G
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
              standardChildCoeff G F s p f hfint
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
            else 0‖ ^ p.toReal) ≤
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ∑ P ∈ childrenOfCell G
            ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G),
          ENNReal.ofReal
            (‖standardChildCoeff G F s p f hfint
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P‖ ^ p.toReal)
  rw [ENNReal.ofReal_sum_of_nonneg]
  · calc
      (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
        ENNReal.ofReal
          (‖∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            if P ∈ childrenOfCell G
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
              standardChildCoeff G F s p f hfint
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
            else 0‖ ^ p.toReal))
          ≤
        ∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            ENNReal.ofReal
              (‖if P ∈ childrenOfCell G
                  ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
                  standardChildCoeff G F s p f hfint
                    ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
                else 0‖ ^ p.toReal) := by
            exact Finset.sum_le_sum fun P _ =>
              positiveCoeff_parent_sum_bound G F s p f hfint k P
      _ =
        ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
          ∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1),
            ENNReal.ofReal
              (‖if P ∈ childrenOfCell G
                  ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) then
                  standardChildCoeff G F s p f hfint
                    ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P
                else 0‖ ^ p.toReal) := by
            exact Finset.sum_comm
      _ =
        ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
          ∑ P ∈ childrenOfCell G
              ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G),
            ENNReal.ofReal
              (‖standardChildCoeff G F s p f hfint
                ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G) P‖ ^ p.toReal) := by
            refine Finset.sum_congr rfl ?_
            intro Q hQ
            exact sum_all_level_succ_if_child_eq_sum_children G F s p f hfint hp_pos k Q
  · intro P hP
    exact Real.rpow_nonneg (norm_nonneg _) _

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
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hfint : Integrable f G.grid.μ) (k : ℕ),
        ENNReal.ofReal
            ((standardBlockCoeffPower G F s hs p hp_top f hfint (k + 1)) ^
              (1 / p.toReal)) ≤
          C * (HaarRepresentation.levelHaarBlock G F s p f hfint k) ^ (1 / p.toReal) := by
  classical
  rcases exists_nat_gt (1 / G.grid.lambda1) with ⟨N, hN⟩
  let CReal : ℝ :=
    (N : ℝ) *
      (((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) *
        (c₂ G *
          max (G.grid.lambda1 ^ (1 / p.toReal - s))
            (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal)
  let C : ℝ≥0∞ := ENNReal.ofReal (CReal ^ (1 / p.toReal))
  refine ⟨C, ENNReal.ofReal_ne_top, ?_⟩
  intro f hfint k
  have hpR_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
      hp_top.ne
  have hpInv_nonneg : 0 ≤ 1 / p.toReal := one_div_nonneg.2 hpR_pos.le
  have hCReal_nonneg : 0 ≤ CReal := by
    have hBpow_nonneg :
        0 ≤ ((2 ^ N * 2 ^ N : ℕ) : ℝ) ^ (p.toReal - 1) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hK_nonneg :
        0 ≤ max (G.grid.lambda1 ^ (1 / p.toReal - s))
          (G.grid.lambda2 ^ (1 / p.toReal - s)) := by
      exact (Real.rpow_pos_of_pos G.grid.hlambda1_pos _).le.trans
        (le_max_left _ _)
    have hA_nonneg :
        0 ≤ (c₂ G *
          max (G.grid.lambda1 ^ (1 / p.toReal - s))
            (G.grid.lambda2 ^ (1 / p.toReal - s))) ^ p.toReal :=
      Real.rpow_nonneg (mul_nonneg (c₂_pos G).le hK_nonneg) _
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hBpow_nonneg hA_nonneg)
  have hpower :
      ENNReal.ofReal (standardBlockCoeffPower G F s hs p hp_top f hfint (k + 1)) ≤
        ENNReal.ofReal CReal * HaarRepresentation.levelHaarBlock G F s p f hfint k := by
    calc
      ENNReal.ofReal (standardBlockCoeffPower G F s hs p hp_top f hfint (k + 1))
          ≤ standardLevelCoeffPower G F s p f hfint k := by
            exact abstract_positive_levelCoeffPower_le_standardLevelCoeffPower
              G F s hs p hp_top f hfint k
      _ ≤ ENNReal.ofReal CReal *
            HaarRepresentation.levelHaarBlock G F s p f hfint k := by
            simpa [CReal] using
              standardLevelCoeffPower_le_const_mul_levelHaarBlock_of_N
                G F s p hp_top hN f hfint k
  have hroot :
      (ENNReal.ofReal (standardBlockCoeffPower G F s hs p hp_top f hfint (k + 1))) ^
          (1 / p.toReal) ≤
        (ENNReal.ofReal CReal *
          HaarRepresentation.levelHaarBlock G F s p f hfint k) ^ (1 / p.toReal) :=
    ENNReal.rpow_le_rpow hpower hpInv_nonneg
  calc
    ENNReal.ofReal
        ((standardBlockCoeffPower G F s hs p hp_top f hfint (k + 1)) ^ (1 / p.toReal))
        =
          (ENNReal.ofReal (standardBlockCoeffPower G F s hs p hp_top f hfint (k + 1))) ^
            (1 / p.toReal) := by
          rw [ENNReal.ofReal_rpow_of_nonneg
            (standardBlockCoeffPower_nonneg G F s hs p hp_top f hfint (k + 1))
            hpInv_nonneg]
    _ ≤ (ENNReal.ofReal CReal *
          HaarRepresentation.levelHaarBlock G F s p f hfint k) ^ (1 / p.toReal) := hroot
    _ = C * (HaarRepresentation.levelHaarBlock G F s p f hfint k) ^ (1 / p.toReal) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hpInv_nonneg]
          have hC_eq : ENNReal.ofReal CReal ^ (1 / p.toReal) = C := by
            simpa [C] using
              ENNReal.ofReal_rpow_of_nonneg hCReal_nonneg hpInv_nonneg
          rw [hC_eq]

private theorem l2NormalizationFactor_alpha_for_standard
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G)) :
    HaarRepresentation.l2NormalizationFactor G F .alpha =
      Real.sqrt (G.grid.μ Set.univ).toReal := by
  let μI := (G.grid.μ Set.univ).toReal
  have hμI_pos : 0 < μI := by
    have hμ_pos : 0 < G.grid.μ Set.univ :=
      G.grid.positive_measure 0 Set.univ (by simp [G.grid.grid.first_partition_eq_univ])
    have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ := by
      letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Set.univ
    exact ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
  calc
    HaarRepresentation.l2NormalizationFactor G F .alpha
        = (Real.sqrt (1 / μI))⁻¹ := by
          simp [HaarRepresentation.l2NormalizationFactor, μI]
    _ = Real.sqrt μI := by
          have hsqrt_inv : Real.sqrt (1 / μI) = (Real.sqrt μI)⁻¹ := by
            rw [show 1 / μI = μI⁻¹ by ring, Real.sqrt_inv μI]
          rw [hsqrt_inv, inv_inv]

private theorem l2normalizedHaar_alpha_norm_eq
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (x : α) :
    ‖HaarRepresentation.L2normalizedHaar G F .alpha x‖ =
      (G.grid.μ Set.univ).toReal ^ (-(1 : ℝ) / 2) := by
  let μI := (G.grid.μ Set.univ).toReal
  have hμI_pos : 0 < μI := by
    have hμ_pos : 0 < G.grid.μ Set.univ :=
      G.grid.positive_measure 0 Set.univ (by simp [G.grid.grid.first_partition_eq_univ])
    have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ := by
      letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Set.univ
    exact ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
  have hnorm :
      ‖HaarRepresentation.L2normalizedHaar G F .alpha x‖ =
        Real.sqrt μI * (1 / μI) := by
    rw [HaarRepresentation.L2normalizedHaar,
      l2NormalizationFactor_alpha_for_standard G F]
    simp [UnbalancedHaarWavelet.FullHaarSystem.function, F.alphaFunction_def,
      UnbalancedHaarWavelet.normalizedAlphaFunction, μI,
      Real.sqrt_nonneg]
  calc
    ‖HaarRepresentation.L2normalizedHaar G F .alpha x‖
        = Real.sqrt μI * (1 / μI) := hnorm
    _ = μI ^ (-(1 : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow]
          rw [show 1 / μI = μI⁻¹ by ring]
          rw [show μI⁻¹ = μI ^ (-(1 : ℝ)) by
            have h := Real.rpow_neg hμI_pos.le (1 : ℝ)
            rw [Real.rpow_one] at h
            exact h.symm]
          rw [← Real.rpow_add hμI_pos]
          ring_nf

private theorem standardFatherLevelBlock_coeff_norm_eq_fatherWeight
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace 0) :
    ‖(canonicalStandardFatherLevelBlock G F s p hs hp hp_top f hf).coeff Q‖ =
      (G.grid.μ Set.univ).toReal ^ (1 / p.toReal - s - 1 / 2) *
        ‖HaarRepresentation.Coeff G F f hf .alpha‖ := by
  let μI := (G.grid.μ Set.univ).toReal
  have hQ_univ : Q.1 = Set.univ := by
    have hQ_mem : Q.1 ∈ G.grid.grid.partitions 0 := Q.2
    rw [G.grid.grid.first_partition_eq_univ] at hQ_mem
    exact Finset.mem_singleton.mp hQ_mem
  have hμI_pos : 0 < μI := by
    have hμ_pos : 0 < G.grid.μ Set.univ :=
      G.grid.positive_measure 0 Set.univ (by simp [G.grid.grid.first_partition_eq_univ])
    have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ := by
      letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Set.univ
    exact ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
  let r : ℝ := μI ^ (s - (p.toReal)⁻¹)
  let d : ℂ := HaarRepresentation.Coeff G F f hf .alpha
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hμI_pos _
  have hαnorm :
      ‖HaarRepresentation.L2normalizedHaar G F .alpha
          (cellPoint G { level := 0, cell := Q.1, mem := Q.2 })‖ =
        μI ^ (-(1 : ℝ) / 2) := by
    simpa [μI] using
      l2normalizedHaar_alpha_norm_eq G F
        (cellPoint G { level := 0, cell := Q.1, mem := Q.2 })
  have hpow :
      μI ^ (-(1 : ℝ) / 2) / r =
        μI ^ (1 / p.toReal - s - 1 / 2) := by
    calc
      μI ^ (-(1 : ℝ) / 2) / r =
          μI ^ (-(1 : ℝ) / 2) * μI ^ (-(s - (p.toReal)⁻¹)) := by
            rw [show r = μI ^ (s - (p.toReal)⁻¹) by rfl]
            rw [div_eq_mul_inv, Real.rpow_neg hμI_pos.le]
      _ = μI ^ (1 / p.toReal - s - 1 / 2) := by
            rw [← Real.rpow_add hμI_pos]
            ring_nf
  calc
    ‖(canonicalStandardFatherLevelBlock G F s p hs hp hp_top f hf).coeff Q‖
        =
      ‖d * HaarRepresentation.L2normalizedHaar G F .alpha
          (cellPoint G { level := 0, cell := Q.1, mem := Q.2 }) / (r : ℂ)‖ := by
        simp [canonicalStandardFatherLevelBlock, d, r, μI, hQ_univ]
    _ = ‖d‖ * (μI ^ (-(1 : ℝ) / 2) / r) := by
        rw [norm_div, norm_mul, hαnorm]
        rw [Complex.norm_of_nonneg hr_pos.le]
        ring
    _ =
      (G.grid.μ Set.univ).toReal ^ (1 / p.toReal - s - 1 / 2) *
        ‖HaarRepresentation.Coeff G F f hf .alpha‖ := by
        rw [hpow]
        simp [d, μI, mul_comm]

/--
The level-zero coefficient root of the abstract standard block sequence is
controlled by the father term of the Haar norm.
-/
theorem exists_standardFatherLevelCoeffRoot_le_const_mul_fatherTerm
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    [DecidableEq F.Index]
    (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hfint : Integrable f G.grid.μ),
        ENNReal.ofReal
            ((standardBlockCoeffPower G F s hs p hp_top f hfint 0) ^
              (1 / p.toReal)) ≤
          C * HaarRepresentation.fatherTerm G F s p f hfint := by
  classical
  refine ⟨1, by simp, ?_⟩
  intro f hfint
  let a : ℝ :=
    (G.grid.μ Set.univ).toReal ^ (1 / p.toReal - s - 1 / 2) *
      ‖HaarRepresentation.Coeff G F f hfint .alpha‖
  have hpR_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
      hp_top.ne
  have ha_nonneg : 0 ≤ a := by
    have hμ_pos : 0 < (G.grid.μ Set.univ).toReal := by
      have hμ_pos_en : 0 < G.grid.μ Set.univ :=
        G.grid.positive_measure 0 Set.univ (by simp [G.grid.grid.first_partition_eq_univ])
      have hμ_ne_top : G.grid.μ Set.univ ≠ ∞ := by
        letI : IsFiniteMeasure G.grid.μ := G.grid.isFinite
        exact MeasureTheory.measure_ne_top G.grid.μ Set.univ
      exact ENNReal.toReal_pos hμ_pos_en.ne' hμ_ne_top
    exact mul_nonneg (Real.rpow_pos_of_pos hμ_pos _).le (norm_nonneg _)
  have hlevel : standardBlockCoeffPower G F s hs p hp_top f hfint 0 = a ^ p.toReal := by
    let hp : 1 ≤ p := Fact.out
    let hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
    let Q₀ : WeakGridSpace.LevelCell G.toWeakGridSpace 0 :=
      ⟨Set.univ, by
        change Set.univ ∈ G.grid.grid.partitions 0
        simp [G.grid.grid.first_partition_eq_univ]⟩
    change standardBlockCoeffPower G F s hs p hp_top f hfint 0 =
      ((G.grid.μ Set.univ).toReal ^ (1 / p.toReal - s - 1 / 2) *
        ‖HaarRepresentation.Coeff G F f hfint .alpha‖) ^ p.toReal
    simp only [standardBlockCoeffPower, canonicalStandardLpGridBlock]
    change
      (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace 0,
        ‖(canonicalStandardFatherLevelBlock G F s p hs hp hp_ne_top f hfint).coeff Q‖ ^
          p.toReal) =
        ((G.grid.μ Set.univ).toReal ^ (1 / p.toReal - s - 1 / 2) *
          ‖HaarRepresentation.Coeff G F f hfint .alpha‖) ^ p.toReal
    rw [Finset.sum_eq_single Q₀]
    · rw [standardFatherLevelBlock_coeff_norm_eq_fatherWeight G F s p hs hp hp_ne_top
        f hfint Q₀]
    · intro Q _ hne
      have hQ_univ : Q.1 = Set.univ := by
        have hQ_mem : Q.1 ∈ G.grid.grid.partitions 0 := Q.2
        rw [G.grid.grid.first_partition_eq_univ] at hQ_mem
        exact Finset.mem_singleton.mp hQ_mem
      exact False.elim (hne (Subtype.ext hQ_univ))
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ Q₀))
  have hroot_real :
      (standardBlockCoeffPower G F s hs p hp_top f hfint 0) ^ (1 / p.toReal) = a := by
    rw [hlevel]
    rw [← Real.rpow_mul ha_nonneg]
    have hcancel : p.toReal * (1 / p.toReal) = 1 := by
      field_simp [hpR_pos.ne']
    rw [hcancel, Real.rpow_one]
  calc
    ENNReal.ofReal
        ((standardBlockCoeffPower G F s hs p hp_top f hfint 0) ^ (1 / p.toReal))
        = ENNReal.ofReal a := by rw [hroot_real]
    _ = HaarRepresentation.fatherTerm G F s p f hfint := by
        simp [HaarRepresentation.fatherTerm, a]
    _ ≤ 1 * HaarRepresentation.fatherTerm G F s p f hfint := by
        simp

private theorem ennreal_tsum_eq_zero_add_succ (u : ℕ → ℝ≥0∞) :
    (∑' k, u k) = u 0 + ∑' k, u (k + 1) := by
  simpa using (tsum_eq_zero_add' (f := u) ENNReal.summable)

private theorem ennreal_toReal_pos_of_one_le_lt_top (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp_top : p < ∞) :
    0 < p.toReal := by
  exact ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp_top.ne

private theorem qGauge_le_const_mul
    (C : ℝ≥0∞) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (u v : ℕ → ℝ≥0∞) (huv : ∀ k, u k ≤ C * v k) :
    (if q = ∞ then
        sSup (Set.range u)
      else
        (∑' k, (u k) ^ q.toReal) ^ (1 / q.toReal))
      ≤
    C *
      (if q = ∞ then
        sSup (Set.range v)
      else
        (∑' k, (v k) ^ q.toReal) ^ (1 / q.toReal)) := by
  by_cases hq_top : q = ∞
  · simp [hq_top]
    intro k
    exact (huv k).trans (mul_le_mul_right (le_iSup v k) C)
  · have hq_lt_top : q < ∞ := lt_top_iff_ne_top.2 hq_top
    have hqR_pos : 0 < q.toReal := ennreal_toReal_pos_of_one_le_lt_top q hq_lt_top
    simp [hq_top]
    have hpow :
        (∑' k, (u k) ^ q.toReal) ≤
          C ^ q.toReal * ∑' k, (v k) ^ q.toReal := by
      calc
        (∑' k, (u k) ^ q.toReal)
            ≤ ∑' k, (C * v k) ^ q.toReal := by
              exact ENNReal.tsum_le_tsum fun k =>
                ENNReal.rpow_le_rpow (huv k) hqR_pos.le
        _ = ∑' k, C ^ q.toReal * (v k) ^ q.toReal := by
              simp [ENNReal.mul_rpow_of_nonneg _ _ hqR_pos.le]
        _ = C ^ q.toReal * ∑' k, (v k) ^ q.toReal := by
              rw [ENNReal.tsum_mul_left]
    calc
      (∑' k, (u k) ^ q.toReal) ^ q.toReal⁻¹
          ≤ (C ^ q.toReal * ∑' k, (v k) ^ q.toReal) ^ q.toReal⁻¹ := by
            exact ENNReal.rpow_le_rpow hpow (inv_nonneg.2 hqR_pos.le)
      _ = C * (∑' k, (v k) ^ q.toReal) ^ q.toReal⁻¹ := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hqR_pos.le)]
            rw [← ENNReal.rpow_mul]
            have hcancel : q.toReal * q.toReal⁻¹ = 1 := by
              field_simp [hqR_pos.ne']
            rw [hcancel]
            simp

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
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (C0 Cpos : ℝ≥0∞) (_hC0 : C0 ≠ ∞) (_hCpos : Cpos ≠ ∞)
    (f : α → ℂ) (hfint : Integrable f G.grid.μ) :
    ENNReal.ofReal
        ((standardBlockCoeffPower G F s hs p hp_top f hfint 0) ^
          (1 / p.toReal)) ≤
        C0 * HaarRepresentation.fatherTerm G F s p f hfint →
    (∀ k,
      ENNReal.ofReal
        ((standardBlockCoeffPower G F s hs p hp_top f hfint (k + 1)) ^
          (1 / p.toReal)) ≤
        Cpos * (HaarRepresentation.levelHaarBlock G F s p f hfint k) ^ (1 / p.toReal)) →
      standardRepresentationNorm G F s hs p hp_top q f hfint ≤
        (C0 + Cpos) * HaarRepresentation.haarL2RepresentationNorm G F s p q f hfint := by
  classical
  intro hfather hlevels
  let L : ℕ → ℝ := fun k => standardBlockCoeffPower G F s hs p hp_top f hfint k
  let fatherStd : ℝ≥0∞ :=
    ENNReal.ofReal ((L 0) ^ (1 / p.toReal))
  let waveStd : ℝ≥0∞ :=
    if q = ∞ then
      sSup (Set.range fun k => ENNReal.ofReal ((L (k + 1)) ^
        (1 / p.toReal)))
    else
      (∑' k, (ENNReal.ofReal ((L (k + 1)) ^
        (1 / p.toReal))) ^ q.toReal) ^ (1 / q.toReal)
  let fatherH := HaarRepresentation.fatherTerm G F s p f hfint
  let waveH : ℝ≥0∞ :=
    if q = ∞ then
      sSup (Set.range fun k => (HaarRepresentation.levelHaarBlock G F s p f hfint k) ^
        (1 / p.toReal))
    else
      (∑' k, ((HaarRepresentation.levelHaarBlock G F s p f hfint k) ^
        (1 / p.toReal)) ^ q.toReal) ^ (1 / q.toReal)
  have hpR_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
      hp_top.ne
  have hpInv_nonneg : 0 ≤ 1 / p.toReal := one_div_nonneg.2 hpR_pos.le
  have hL_nonneg : ∀ k, 0 ≤ L k := by
    intro k
    exact standardBlockCoeffPower_nonneg G F s hs p hp_top f hfint k
  have hstd_le : standardRepresentationNorm G F s hs p hp_top q f hfint ≤
      fatherStd + waveStd := by
    by_cases hq : q = ∞
    · rw [standardRepresentationNorm]
      simp only [L, fatherStd, waveStd, hq, ↓reduceIte]
      refine sSup_le ?_
      rintro _ ⟨k, rfl⟩
      cases k with
      | zero =>
          simp
      | succ k =>
          have htail_le :
              sSup (Set.range fun k =>
                ENNReal.ofReal ((L (k + 1)) ^ (1 / p.toReal))) ≤
                fatherStd + sSup (Set.range fun k =>
                  ENNReal.ofReal ((L (k + 1)) ^ (1 / p.toReal))) := by
            simp
          exact (le_sSup (Set.mem_range_self k)).trans htail_le
    · have hq_lt_top : q < ∞ := lt_top_iff_ne_top.2 hq
      have hqR_pos : 0 < q.toReal := ennreal_toReal_pos_of_one_le_lt_top q hq_lt_top
      have hqR_one : 1 ≤ q.toReal := by
        simpa using ENNReal.toReal_mono hq (Fact.out : (1 : ℝ≥0∞) ≤ q)
      let root : ℕ → ℝ≥0∞ :=
        fun k => ENNReal.ofReal ((L k) ^ (1 / p.toReal))
      have hterm : ∀ k,
          ENNReal.ofReal ((L k) ^ (q.toReal / p.toReal)) =
            (root k) ^ q.toReal := by
        intro k
        change ENNReal.ofReal ((L k) ^ (q.toReal / p.toReal)) =
          (ENNReal.ofReal ((L k) ^ (1 / p.toReal))) ^ q.toReal
        rw [← ENNReal.ofReal_rpow_of_nonneg (hL_nonneg k)
          (div_nonneg hqR_pos.le hpR_pos.le)]
        rw [← ENNReal.ofReal_rpow_of_nonneg (hL_nonneg k) hpInv_nonneg]
        rw [← ENNReal.rpow_mul]
        congr 1
        field_simp [hpR_pos.ne']
      let tailSum : ℝ≥0∞ := ∑' k, (root (k + 1)) ^ q.toReal
      have hsplit :
          (∑' k, ENNReal.ofReal ((L k) ^
            (q.toReal / p.toReal))) =
            (root 0) ^ q.toReal + tailSum := by
        calc
          (∑' k, ENNReal.ofReal ((L k) ^
            (q.toReal / p.toReal))) =
              ∑' k, (root k) ^ q.toReal := by
                exact tsum_congr hterm
          _ = (root 0) ^ q.toReal + tailSum := by
                simpa [tailSum] using
                  ennreal_tsum_eq_zero_add_succ (fun k => (root k) ^ q.toReal)
      have hpow_add :
          (root 0) ^ q.toReal + tailSum ≤
            (root 0 + tailSum ^ (1 / q.toReal)) ^ q.toReal := by
        have h := ENNReal.add_rpow_le_rpow_add (root 0) (tailSum ^ (1 / q.toReal)) hqR_one
        simpa [one_div, ENNReal.rpow_inv_rpow hqR_pos.ne'] using h
      calc
        standardRepresentationNorm G F s hs p hp_top q f hfint
            = ((root 0) ^ q.toReal + tailSum) ^ (1 / q.toReal) := by
              simp [standardRepresentationNorm, L, hq, hsplit, root, tailSum]
        _ ≤ ((root 0 + tailSum ^ (1 / q.toReal)) ^ q.toReal) ^ (1 / q.toReal) := by
              exact ENNReal.rpow_le_rpow hpow_add (one_div_nonneg.2 hqR_pos.le)
        _ = root 0 + tailSum ^ (1 / q.toReal) := by
              rw [← ENNReal.rpow_mul]
              have hcancel : q.toReal * (1 / q.toReal) = 1 := by
                field_simp [hqR_pos.ne']
              rw [hcancel]
              simp
        _ = fatherStd + waveStd := by
              simp [fatherStd, waveStd, root, tailSum, hq]
  have hfather_le : fatherStd ≤ C0 * fatherH := by
    simpa [fatherStd, fatherH, L] using hfather
  have hwave_le : waveStd ≤ Cpos * waveH := by
    simpa [waveStd, waveH, L] using
      qGauge_le_const_mul Cpos q
        (fun k => ENNReal.ofReal ((L (k + 1)) ^ (1 / p.toReal)))
        (fun k => (HaarRepresentation.levelHaarBlock G F s p f hfint k) ^
          (1 / p.toReal))
        (by
          intro k
          simpa [L] using hlevels k)
  calc
    standardRepresentationNorm G F s hs p hp_top q f hfint
        ≤ fatherStd + waveStd := hstd_le
    _ ≤ C0 * fatherH + Cpos * waveH := add_le_add hfather_le hwave_le
    _ ≤ (C0 + Cpos) * (fatherH + waveH) := by
          calc
            C0 * fatherH + Cpos * waveH
                ≤ C0 * fatherH + Cpos * waveH + (C0 * waveH + Cpos * fatherH) := by
                  exact le_self_add
            _ = (C0 + Cpos) * (fatherH + waveH) := by
                  ring_nf
    _ = (C0 + Cpos) * HaarRepresentation.haarL2RepresentationNorm G F s p q f hfint := by
          by_cases hq : q = ∞
          · simp [HaarRepresentation.haarL2RepresentationNorm, fatherH, waveH, hq]
          · simp [HaarRepresentation.haarL2RepresentationNorm, fatherH, waveH, hq]
            congr 3
            apply tsum_congr
            intro k
            rw [← ENNReal.rpow_mul]
            congr 1
            ring

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
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p < ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (f : α → ℂ) (hfint : Integrable f G.grid.μ),
        HaarRepresentation.haarL2RepresentationNorm G F s p q f hfint ≠ ∞ →
          standardRepresentationNorm G F s hs p hp_top q f hfint ≠ ∞ ∧
            standardRepresentationNorm G F s hs p hp_top q f hfint ≤
              C * HaarRepresentation.haarL2RepresentationNorm G F s p q f hfint := by
  classical
  rcases exists_standardFatherLevelCoeffRoot_le_const_mul_fatherTerm
      G F s hs p hp_top with
    ⟨C0, hC0_fin, hfather⟩
  rcases exists_standardPositiveLevelCoeffRoot_le_const_mul_levelHaarBlockRoot
      G F s hs p hp_top with
    ⟨Cpos, hCpos_fin, hlevel⟩
  refine ⟨C0 + Cpos, ENNReal.Finiteness.add_ne_top hC0_fin hCpos_fin, ?_⟩
  intro f hfint hhaar_fin
  have hfather' :
        ENNReal.ofReal
          ((standardBlockCoeffPower G F s hs p hp_top f hfint 0) ^
            (1 / p.toReal)) ≤
        C0 * HaarRepresentation.fatherTerm G F s p f hfint := by
    simpa using hfather f hfint
  have hlevel' :
      ∀ k,
        ENNReal.ofReal
          ((standardBlockCoeffPower G F s hs p hp_top f hfint (k + 1)) ^
            (1 / p.toReal)) ≤
          Cpos * (HaarRepresentation.levelHaarBlock G F s p f hfint k) ^ (1 / p.toReal) := by
    simpa using hlevel f hfint
  have hnorm_le :
      standardRepresentationNorm G F s hs p hp_top q f hfint ≤
        (C0 + Cpos) * HaarRepresentation.haarL2RepresentationNorm G F s p q f hfint :=
    standardRepresentationNorm_le_of_level_bounds G F s hs p hp_top q
      C0 Cpos hC0_fin hCpos_fin f hfint hfather' hlevel'
  have hstandard_fin :
      standardRepresentationNorm G F s hs p hp_top q f hfint ≠ ∞ := by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.Finiteness.add_ne_top hC0_fin hCpos_fin) hhaar_fin)
      hnorm_le
  exact ⟨hstandard_fin, hnorm_le⟩

end StandardAtomicRepresentation

end

end GoodGridSpace
