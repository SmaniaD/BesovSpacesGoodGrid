import BesovSpacesGoodGrid.GoodGrid.Multipliers.Definition
import BesovSpacesGoodGrid.GoodGrid.BesovAtoms
import BesovSpacesGoodGrid.GoodGrid.Multipliers.Besovspq
import BesovSpacesGoodGrid.GoodGrid.Multipliers.MultipliersareBounded
import BesovSpacesGoodGrid.GoodGrid.PositiveCone
import BesovSpacesGoodGrid.WeakGrid.Scales

/-!
# Non-Archimedean estimate for multiplier sums

This file records the non-Archimedean estimate from the multiplier section in
a form adapted to the existing atomic representation API.  The proof is left as
a separate task: the statement packages the hypotheses about level-tail
`selfs` bounds, support separation, and compatible representation levels, and
asserts the existence of a controlled Souza Besov representation of the product
with a finite sum of multipliers.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
The support of `g` meets the level cell `Q`.
-/
def goodGridLevelCellMeetsSupport
    (G : GoodGridSpace (α := α)) {k : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) (g : α → ℂ) : Prop :=
  (Q.1 ∩ {x | g x ≠ 0}).Nonempty

/--
For one active representation cell `Q`, this is the sum of the level-tail
`selfs` seminorms of precisely those multipliers whose support meets `Q`.
-/
noncomputable def nonArchimedeanRelevantTailSelfsSum
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℝ := by
  classical
  exact
    ∑ i ∈ Λ,
      if goodGridLevelCellMeetsSupport G Q (g i) then
        souzaPointwiseSelfsTailNorm G β p qtilde hβ hp hp_top (t i) (g i)
      else
        0

/--
One term in the infinite relevant-tail series.

For an index `i ∈ Λ`, this is the tail `selfs` norm of `g i` if the support of
`g i` meets the source cell `Q`, and zero otherwise.  The definition is
`noncomputable` only to hide the classical decidability of the support-meeting
predicate.
-/
noncomputable def nonArchimedeanRelevantTailSelfsInfiniteTerm
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (Λ : Set ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (i : {i // i ∈ Λ}) : ℝ := by
  classical
  exact
    if goodGridLevelCellMeetsSupport G Q (g i.1) then
      souzaPointwiseSelfsTailNorm G β p qtilde hβ hp hp_top (t i.1) (g i.1)
    else
      0

/--
Infinite-index version of `nonArchimedeanRelevantTailSelfsSum`.

Here `Λ` is a set of indices, possibly infinite.  The value is written as a
`tsum` over the subtype of indices belonging to `Λ`; later estimates should
carry the appropriate `Summable` or `HasSum` hypothesis when convergence is
part of the mathematical content.
-/
noncomputable def nonArchimedeanRelevantTailSelfsInfiniteSum
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (Λ : Set ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℝ := by
  exact
    ∑' i : {i // i ∈ Λ},
      nonArchimedeanRelevantTailSelfsInfiniteTerm
        G β p qtilde hβ hp hp_top Λ t g Q i

private theorem souzaPointwiseSelfsTailNorm_nonneg_of_nonempty
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {t : ℕ} {m : α → ℂ}
    (hm : ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G s p q hs hp hp_top t m C) :
    0 ≤ souzaPointwiseSelfsTailNorm G s p q hs hp hp_top t m := by
  classical
  rcases hm with ⟨C, hC⟩
  refine le_csInf ?_ ?_
  · exact ⟨C, hC⟩
  · intro D hD
    exact hD.1

private theorem nonArchimedeanRelevantTailSelfsInfiniteTerm_nonneg
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {Λ : Set ℕ} {t : ℕ → ℕ} {g : ℕ → α → ℂ}
    (hTail : ∀ i ∈ Λ,
      ∃ C : ℝ,
        SouzaPointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (i : {i // i ∈ Λ}) :
    0 ≤ nonArchimedeanRelevantTailSelfsInfiniteTerm
        G β p qtilde hβ hp hp_top Λ t g Q i := by
  classical
  unfold nonArchimedeanRelevantTailSelfsInfiniteTerm
  by_cases hmeet : goodGridLevelCellMeetsSupport G Q (g i.1)
  · simp [hmeet,
      souzaPointwiseSelfsTailNorm_nonneg_of_nonempty
        G β p qtilde hβ hp hp_top (hTail i.1 i.2)]
  · simp [hmeet]

private theorem norm_le_relevantTailSelfsInfiniteTerm_of_mem_active
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {Λ : Set ℕ} {t : ℕ → ℕ} {g : ℕ → α → ℂ}
    (hTail : ∀ i ∈ Λ,
      ∃ C : ℝ,
        SouzaPointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C)
    {k : ℕ} {Q : WeakGridSpace.LevelCell G.toWeakGridSpace k}
    {i : {i // i ∈ Λ}} {z : α}
    (hzQ : z ∈ Q.1)
    (hg_bound :
      ‖g i.1 z‖ ≤
        souzaPointwiseSelfsTailNorm
          G β p qtilde hβ hp hp_top (t i.1) (g i.1)) :
    ‖g i.1 z‖ ≤
      nonArchimedeanRelevantTailSelfsInfiniteTerm
        G β p qtilde hβ hp hp_top Λ t g Q i := by
  classical
  by_cases hgz : g i.1 z = 0
  · have hnorm : ‖g i.1 z‖ = 0 := by simpa [hgz]
    rw [hnorm]
    exact nonArchimedeanRelevantTailSelfsInfiniteTerm_nonneg
      G β p qtilde hβ hp hp_top hTail Q i
  · have hmeet : goodGridLevelCellMeetsSupport G Q (g i.1) :=
      ⟨z, hzQ, hgz⟩
    simpa [nonArchimedeanRelevantTailSelfsInfiniteTerm, hmeet] using hg_bound

private theorem hasSum_of_nonneg_le_mul_hasSum
    {ι : Type*} {a b : ι → ℝ} {T K N : ℝ}
    (hK_nonneg : 0 ≤ K)
    (ha_nonneg : ∀ i, 0 ≤ a i)
    (hle : ∀ i, a i ≤ K * b i)
    (hb_sum : HasSum b T)
    (hT_le : T ≤ N) :
    HasSum a (∑' i, a i) ∧ (∑' i, a i) ≤ K * N := by
  classical
  have hKb_sum : Summable fun i => K * b i := hb_sum.summable.mul_left K
  have ha_sum : Summable a :=
    Summable.of_nonneg_of_le ha_nonneg hle hKb_sum
  refine ⟨ha_sum.hasSum, ?_⟩
  have htsum_le :
      (∑' i, a i) ≤ ∑' i, K * b i :=
    ha_sum.tsum_le_tsum hle hKb_sum
  have htsum_scaled : (∑' i, K * b i) = K * T :=
    (hb_sum.mul_left K).tsum_eq
  calc
    (∑' i, a i) ≤ ∑' i, K * b i := htsum_le
    _ = K * T := htsum_scaled
    _ ≤ K * N := mul_le_mul_of_nonneg_left hT_le hK_nonneg

private theorem nonArchimedeanRelevantTailSelfsSum_le_of_hasSum
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {Λ : Set ℕ} {Λfin : Finset ℕ} {t : ℕ → ℕ} {g : ℕ → α → ℂ}
    {N T : ℝ} {k : ℕ} {Q : WeakGridSpace.LevelCell G.toWeakGridSpace k}
    (hTail : ∀ i ∈ Λ,
      ∃ C : ℝ,
        SouzaPointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hΛfin : ∀ i ∈ Λfin, i ∈ Λ)
    (hTsum : HasSum
      (fun i : {i // i ∈ Λ} =>
        nonArchimedeanRelevantTailSelfsInfiniteTerm
          G β p qtilde hβ hp hp_top Λ t g Q i)
      T)
    (hTle : T ≤ N) :
    nonArchimedeanRelevantTailSelfsSum
      G β p qtilde hβ hp hp_top Λfin t g Q ≤ N := by
  classical
  let emb : {i // i ∈ Λfin} ↪ {i // i ∈ Λ} :=
    { toFun := fun i => ⟨i.1, hΛfin i.1 i.2⟩
      inj' := by
        intro a b h
        exact Subtype.ext (Subtype.mk.inj h) }
  let S : Finset {i // i ∈ Λ} := Λfin.attach.map emb
  have hsum_eq :
      nonArchimedeanRelevantTailSelfsSum
          G β p qtilde hβ hp hp_top Λfin t g Q =
        ∑ i ∈ S,
          nonArchimedeanRelevantTailSelfsInfiniteTerm
            G β p qtilde hβ hp hp_top Λ t g Q i := by
    let F : ℕ → ℝ := fun i =>
      if goodGridLevelCellMeetsSupport G Q (g i) then
        souzaPointwiseSelfsTailNorm G β p qtilde hβ hp hp_top (t i) (g i)
      else
        0
    change (∑ i ∈ Λfin, F i) = ∑ x ∈ S, F x.1
    change (∑ i ∈ Λfin, F i) = ∑ x ∈ Λfin.attach.map emb, F x.1
    simp only [Finset.sum_map]
    simp only [emb]
    change (∑ i ∈ Λfin, F i) = ∑ x ∈ Λfin.attach, F x.1
    exact (Λfin.sum_attach F).symm
  have hsum_le_T :
      (∑ i ∈ S,
          nonArchimedeanRelevantTailSelfsInfiniteTerm
            G β p qtilde hβ hp hp_top Λ t g Q i) ≤ T := by
    exact sum_le_hasSum S
      (fun i _hi =>
        nonArchimedeanRelevantTailSelfsInfiniteTerm_nonneg
          G β p qtilde hβ hp hp_top hTail Q i)
      hTsum
  calc
    nonArchimedeanRelevantTailSelfsSum
        G β p qtilde hβ hp hp_top Λfin t g Q
        = ∑ i ∈ S,
            nonArchimedeanRelevantTailSelfsInfiniteTerm
              G β p qtilde hβ hp hp_top Λ t g Q i := hsum_eq
    _ ≤ T := hsum_le_T
    _ ≤ N := hTle

private theorem norm_le_mul_relevantTailSelfsInfiniteTerm_of_mem_active
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {Λ : Set ℕ} {t : ℕ → ℕ} {g : ℕ → α → ℂ}
    (hTail : ∀ i ∈ Λ,
      ∃ C : ℝ,
        SouzaPointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C)
    {k : ℕ} {Q : WeakGridSpace.LevelCell G.toWeakGridSpace k}
    {z : α} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hzQ : z ∈ Q.1)
    (hg_bound : ∀ i : {i // i ∈ Λ},
      ‖g i.1 z‖ ≤ K *
        souzaPointwiseSelfsTailNorm
          G β p qtilde hβ hp hp_top (t i.1) (g i.1))
    (i : {i // i ∈ Λ}) :
    ‖g i.1 z‖ ≤
      K * nonArchimedeanRelevantTailSelfsInfiniteTerm
        G β p qtilde hβ hp hp_top Λ t g Q i := by
  classical
  by_cases hmeet : goodGridLevelCellMeetsSupport G Q (g i.1)
  · simpa [nonArchimedeanRelevantTailSelfsInfiniteTerm, hmeet] using hg_bound i
  · have hgz : g i.1 z = 0 := by
      by_contra hgz_ne
      exact hmeet ⟨z, hzQ, hgz_ne⟩
    have hnorm : ‖g i.1 z‖ = 0 := by simpa [hgz]
    rw [hnorm]
    exact mul_nonneg hK_nonneg
      (nonArchimedeanRelevantTailSelfsInfiniteTerm_nonneg
        G β p qtilde hβ hp hp_top hTail Q i)

private theorem hasSum_norm_of_mem_active
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {Λ : Set ℕ} {t : ℕ → ℕ} {g : ℕ → α → ℂ}
    (hTail : ∀ i ∈ Λ,
      ∃ C : ℝ,
        SouzaPointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C)
    {k : ℕ} {Q : WeakGridSpace.LevelCell G.toWeakGridSpace k}
    {z : α} {K N T : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hzQ : z ∈ Q.1)
    (hg_bound : ∀ i : {i // i ∈ Λ},
      ‖g i.1 z‖ ≤ K *
        souzaPointwiseSelfsTailNorm
          G β p qtilde hβ hp hp_top (t i.1) (g i.1))
    (hterm_sum : HasSum
      (fun i : {i // i ∈ Λ} =>
        nonArchimedeanRelevantTailSelfsInfiniteTerm
          G β p qtilde hβ hp hp_top Λ t g Q i) T)
    (hT_le : T ≤ N) :
    HasSum (fun i : {i // i ∈ Λ} => ‖g i.1 z‖)
        (∑' i : {i // i ∈ Λ}, ‖g i.1 z‖) ∧
      (∑' i : {i // i ∈ Λ}, ‖g i.1 z‖) ≤ K * N := by
  refine hasSum_of_nonneg_le_mul_hasSum hK_nonneg
    (fun i => norm_nonneg _) ?_ hterm_sum hT_le
  intro i
  exact norm_le_mul_relevantTailSelfsInfiniteTerm_of_mem_active
    G β p qtilde hβ hp hp_top hTail hK_nonneg hzQ hg_bound i

private theorem souzaLevelBlock_toFunLt_eq_zero_of_inactive_at
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {k : ℕ}
    (B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k)
    {z : α}
    (hz :
      ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        z ∈ Q.1 → B.coeff Q = 0) :
    B.toFunLt (souzaAtomFamily G s p hs hp hp_top) z = 0 := by
  classical
  unfold WeakGridSpace.LevelBlock.toFunLt
  refine Finset.sum_eq_zero ?_
  intro Q _hQ
  by_cases hzQ : z ∈ Q.1
  · simp [hz Q hzQ]
  · have hatom_zero :
        (souzaAtomFamily G s p hs hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q) z = 0 :=
      (souzaAtomFamily G s p hs hp hp_top).local_support
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
        (B.atom Q) z hzQ
    simp [hatom_zero]

theorem exists_active_cell_of_representsFunction_ne_zero_ae
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {f : α → ℂ}
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (x : Lp ℂ p G.toWeakGridSpace.measure)) :
    ∀ᵐ z ∂G.toWeakGridSpace.measure,
      f z ≠ 0 →
        ∃ k, ∃ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
          z ∈ Q.1 ∧ (R.block k).coeff Q ≠ 0 := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let μ := G.toWeakGridSpace.measure
  let partialSum : ℕ → Lp ℂ p μ :=
    fun N => ∑ k ∈ Finset.range N, (R.block k).toLp A
  have hpartial_tendsto :
      Filter.Tendsto partialSum Filter.atTop (𝓝 ((x : Lp ℂ p μ))) := by
    simpa [partialSum, μ, A] using R.hasSum.tendsto_sum_nat
  have hpartial_coe : ∀ N : ℕ,
      (partialSum N : α → ℂ) =ᵐ[μ]
        fun z => ∑ k ∈ Finset.range N, (R.block k).toFunLt A z := by
    intro N
    induction' N with N ih
    · simpa [partialSum] using (Lp.coeFn_zero ℂ p μ)
    · have hblock :
          (((R.block N).toLp A : Lp ℂ p μ) : α → ℂ) =ᵐ[μ]
            fun z => (R.block N).toFunLt A z := by
        simpa [μ, A] using
          WeakGridSpace.LevelBlock.coeFn_toLp A (R.block N)
      have hsum := ih.add hblock
      have hLp :
          partialSum (N + 1) =
            partialSum N + ((R.block N).toLp A : Lp ℂ p μ) := by
        simp [partialSum, Finset.sum_range_succ]
      rw [hLp]
      refine (Lp.coeFn_add _ _).trans ?_
      refine hsum.trans ?_
      filter_upwards with z
      simp [Finset.sum_range_succ, add_comm]
  have htendsto_measure :
      TendstoInMeasure μ (fun N => partialSum N) Filter.atTop
        (x : Lp ℂ p μ) :=
    tendstoInMeasure_of_tendsto_Lp hpartial_tendsto
  rcases htendsto_measure.exists_seq_tendsto_ae with
    ⟨φ, hφ_mono, hφ_tendsto_ae⟩
  have hcoe :
      ∀ᵐ z ∂μ, ∀ m : ℕ,
        partialSum (φ m) z =
          ∑ k ∈ Finset.range (φ m), (R.block k).toFunLt A z := by
    have hsets :
        (⋂ m : ℕ, {z : α |
          partialSum (φ m) z =
            ∑ k ∈ Finset.range (φ m), (R.block k).toFunLt A z}) ∈ ae μ := by
      exact countable_iInter_mem.mpr fun m => hpartial_coe (φ m)
    filter_upwards [hsets] with z hz m
    exact Set.mem_iInter.mp hz m
  filter_upwards [hRep, hφ_tendsto_ae, hcoe] with z hxf hxlim hxcoe hfz
  by_contra hactive
  have hno_active :
      ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        z ∈ Q.1 → (R.block k).coeff Q = 0 := by
    intro k Q hzQ
    by_contra hcoeff
    exact hactive ⟨k, Q, hzQ, hcoeff⟩
  have hsum_zero : ∀ m : ℕ,
      (∑ k ∈ Finset.range (φ m), (R.block k).toFunLt A z) = 0 := by
    intro m
    refine Finset.sum_eq_zero ?_
    intro k _hk
    exact souzaLevelBlock_toFunLt_eq_zero_of_inactive_at
      G s p hs hp hp_top (R.block k) (hno_active k)
  have hpartial_zero : ∀ m : ℕ, partialSum (φ m) z = 0 := by
    intro m
    rw [hxcoe m, hsum_zero m]
  have hxz_zero : ((x : Lp ℂ p μ) : α → ℂ) z = 0 := by
    have hz_tendsto :
        Filter.Tendsto (fun m : ℕ => partialSum (φ m) z) Filter.atTop
          (𝓝 (0 : ℂ)) := by
      simpa [hpartial_zero] using Filter.tendsto_const_nhds
    exact tendsto_nhds_unique hxlim hz_tendsto
  exact hfz (by simpa [μ] using (hxf ▸ hxz_zero))

private theorem memLp_and_norm_le_of_ae_norm_le_mul_representsFunction
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)]
    {C N : ℝ} {f h : α → ℂ}
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f x)
    (hh_meas : AEStronglyMeasurable h G.toWeakGridSpace.measure)
    (hnorm : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      ‖h z‖ ≤ C * N * ‖f z‖) :
    ∃ hmem : MemLp h p G.toWeakGridSpace.measure,
      ‖MemLp.toLp h hmem‖ ≤ C * N * ‖x‖ := by
  let μ := G.toWeakGridSpace.measure
  have hf_mem : MemLp f p μ :=
    MemLp.ae_eq hRep (Lp.memLp x)
  have hnorm' :
      ∀ᵐ z ∂μ, ‖h z‖ ≤ (C * N) * ‖f z‖ := by
    simpa [μ, mul_assoc] using hnorm
  have hmem : MemLp h p μ :=
    MemLp.of_le_mul (c := C * N) hf_mem (by
      simpa [μ] using hh_meas) hnorm'
  refine ⟨hmem, ?_⟩
  have hLp_bound :
      ∀ᵐ z ∂μ,
        ‖(MemLp.toLp h hmem : Lp ℂ p μ) z‖ ≤
          (C * N) * ‖(x : α → ℂ) z‖ := by
    filter_upwards [MemLp.coeFn_toLp hmem, hRep, hnorm'] with z hhz hxz hz
    rw [hhz, hxz]
    simpa [mul_assoc] using hz
  simpa [μ, mul_assoc] using
    (Lp.norm_le_mul_norm_of_ae_le_mul (μ := μ) (p := p)
      (f := MemLp.toLp h hmem) (g := x) hLp_bound)

/--
Positive-cone version of the relevant level-tail `selfs` sum.  It is the same
local overlap sum as `nonArchimedeanRelevantTailSelfsSum`, but with the
positive tail seminorm from the positive cone.
-/
noncomputable def nonArchimedeanRelevantPositiveTailSelfsSum
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℝ≥0∞ := by
  classical
  exact
    ∑ i ∈ Λ,
      if goodGridLevelCellMeetsSupport G Q (g i) then
        souzaPositivePointwiseSelfsTailNorm
          G β p qtilde hβ hp hp_top (t i) (g i)
      else
        0

/--
Apply a level-tail Souza `selfs` bound to the atom attached to a weak-grid
level cell.

The public tail-bound API quantifies over good-grid cells, while
representations are indexed by weak-grid level cells.  This lemma is just the
conversion between those two views of the same cell.
-/
private theorem SouzaPointwiseSelfsTailBound.apply_levelCell
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {t : ℕ} {m : α → ℂ} {C : ℝ}
    (hC : SouzaPointwiseSelfsTailBound G s p q hs hp hp_top t m C)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (htk : t ≤ k)
    (φ : ((souzaAtomFamily G s p hs hp hp_top).localSpace
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier)
    (hφ : φ ∈ (souzaAtomFamily G s p hs hp hp_top).atoms
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun x => m x *
          (souzaAtomFamily G s p hs hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s p hs hp hp_top) q y ≤ C := by
  simpa [goodGridCellOfLevelCell, WeakGridSpace.levelCellToWeakGridCell] using
    hC.2 (goodGridCellOfLevelCell G Q) htk φ hφ

/--
Approximate the tail `selfs` seminorm by a concrete bound and apply it to one
Souza atom sitting on a weak-grid level cell.

This is the local step used in the non-Archimedean proof: the hypotheses give
nonemptiness of the tail-bound set, while the final estimate needs a concrete
Besov representative for the product of the multiplier with the chosen atom.
-/
private theorem exists_souzaTailProduct_norm_le_norm_add
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {t : ℕ} {m : α → ℂ}
    (hNonempty : ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G s p q hs hp hp_top t m C)
    {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (htk : t ≤ k)
    (φ : ((souzaAtomFamily G s p hs hp hp_top).localSpace
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier)
    (hφ : φ ∈ (souzaAtomFamily G s p hs hp hp_top).atoms
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun x => m x *
          (souzaAtomFamily G s p hs hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s p hs hp hp_top) q y ≤
          souzaPointwiseSelfsTailNorm G s p q hs hp hp_top t m + ε := by
  rcases exists_souzaPointwiseSelfsTailBound_lt_norm_add
      G s p q hs hp hp_top hNonempty hε with
    ⟨C, hC, hC_lt⟩
  rcases SouzaPointwiseSelfsTailBound.apply_levelCell
      G s p q hs hp hp_top hC Q htk φ hφ with
    ⟨y, hy_rep, hy_norm⟩
  exact ⟨y, hy_rep, hy_norm.trans (le_of_lt hC_lt)⟩

/--
If a multiplier has no support inside a level cell, then its product with any
Souza atom supported on that cell is the zero function.
-/
private theorem mul_souzaAtom_eq_zero_of_not_meetsSupport
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {m : α → ℂ}
    (hdisj : ¬ goodGridLevelCellMeetsSupport G Q m)
    (φ : ((souzaAtomFamily G s p hs hp hp_top).localSpace
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier) :
    (fun x => m x *
      (souzaAtomFamily G s p hs hp hp_top).toFunction
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x) =
      fun _ => 0 := by
  classical
  funext x
  by_cases hxQ : x ∈ Q.1
  · have hm : m x = 0 := by
      by_contra hm_ne
      exact hdisj ⟨x, hxQ, hm_ne⟩
    simp [hm]
  · have hφ_zero :
      (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x = 0 :=
      (souzaAtomFamily G s p hs hp hp_top).local_support
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x hxQ
    simp [hφ_zero]

/-- The Souza coefficient-cost gauge of the zero Besov element is zero. -/
private theorem souzaNorm_Costpq_zero_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s p hs hp hp_top) q
        (0 : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q) ≤ 0 := by
  let A := souzaAtomFamily G s p hs hp hp_top
  have hzero :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq
      (A := A) (q := q) hp_top
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := A) q)
      (0 : ℂ) (0 : WeakGridSpace.BesovishSpace A q)
  simpa [A] using le_of_eq hzero

/-- An atom realized as `atomLp` represents its concrete atom function. -/
private theorem atomLp_representsFunction
    (G : WeakGridSpace.WeakGridSpace (α := α)) {s : ℝ} {p u : ℝ≥0∞}
    (A : WeakGridSpace.AtomFamily G s p u) [Fact (1 ≤ p)]
    (Q : WeakGridSpace.WeakGridCell G)
    (φ : (A.localSpace Q).carrier) :
    WeakGridSpace.RepresentsFunction (G := G) (p := p)
      (A.toFunction Q φ) (WeakGridSpace.atomLp A Q φ) := by
  simpa [WeakGridSpace.RepresentsFunction, WeakGridSpace.atomLp] using
    (MeasureTheory.MemLp.coeFn_toLp (A.local_memLp_p Q φ))

/-- Pointwise-product representatives are stable under finite sums. -/
private theorem representsPointwiseProduct_finset_sum
    (G : WeakGridSpace.WeakGridSpace (α := α)) {p : ℝ≥0∞}
    {ι : Type*} [Fact (1 ≤ p)]
    (S : Finset ι) (m : α → ℂ)
    (x y : ι → Lp ℂ p G.measure)
    (hxy : ∀ i ∈ S,
      WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p) m (x i) (y i)) :
    WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p) m
      (∑ i ∈ S, x i) (∑ i ∈ S, y i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using WeakGridSpace.representsPointwiseProduct_zero (G := G) (p := p) m
  | insert a S ha ih =>
      have hS : ∀ i ∈ S,
          WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p) m (x i) (y i) := by
        intro i hi
        exact hxy i (Finset.mem_insert_of_mem hi)
      have ha_prod :
          WeakGridSpace.RepresentsPointwiseProduct (G := G) (p := p) m (x a) (y a) :=
        hxy a (Finset.mem_insert_self a S)
      have hsum_prod := ih hS
      simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc] using
        ha_prod.add hsum_prod

/--
Finite sums of tail-controlled products with one fixed Souza atom have a Besov
representative whose coefficient-cost gauge is bounded by the sum of the
individual tail gauges, up to the chosen per-term error.
-/
private theorem exists_souzaTailProduct_finset_sum_norm_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (S : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    (hNonempty : ∀ i ∈ S, ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G s p q hs hp hp_top (t i) (g i) C)
    {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (hLevel : ∀ i ∈ S, t i ≤ k)
    (φ : ((souzaAtomFamily G s p hs hp hp_top).localSpace
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier)
    (hφ : φ ∈ (souzaAtomFamily G s p hs hp hp_top).atoms
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun x => ∑ i ∈ S, g i x *
          (souzaAtomFamily G s p hs hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s p hs hp hp_top) q y ≤
          ∑ i ∈ S,
            (souzaPointwiseSelfsTailNorm G s p q hs hp hp_top (t i) (g i) + ε) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_, ?_⟩
      · simpa [WeakGridSpace.RepresentsFunction] using
          (Lp.coeFn_zero ℂ p G.toWeakGridSpace.measure)
      · simpa using souzaNorm_Costpq_zero_le G s p q hs hp hp_top
  | insert a S ha ih =>
      have hNonemptyS : ∀ i ∈ S, ∃ C : ℝ,
          SouzaPointwiseSelfsTailBound G s p q hs hp hp_top (t i) (g i) C := by
        intro i hi
        exact hNonempty i (Finset.mem_insert_of_mem hi)
      have hLevelS : ∀ i ∈ S, t i ≤ k := by
        intro i hi
        exact hLevel i (Finset.mem_insert_of_mem hi)
      rcases ih hNonemptyS hLevelS with ⟨yS, hyS_rep, hyS_norm⟩
      have ha_mem : a ∈ insert a S := Finset.mem_insert_self a S
      rcases exists_souzaTailProduct_norm_le_norm_add
          G s p q hs hp hp_top (hNonempty a ha_mem) hε Q
          (hLevel a ha_mem) φ hφ with
        ⟨ya, hya_rep, hya_norm⟩
      refine ⟨yS + ya, ?_, ?_⟩
      · have hrep := hya_rep.add hyS_rep
        change (((yS + ya : WeakGridSpace.BesovishSpace A q) :
            Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =ᵐ[G.toWeakGridSpace.measure]
          fun x => ∑ i ∈ insert a S,
            g i x *
              (souzaAtomFamily G s p hs hp hp_top).toFunction
                (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x
        refine (Lp.coeFn_add
          (yS : Lp ℂ p G.toWeakGridSpace.measure)
          (ya : Lp ℂ p G.toWeakGridSpace.measure)).trans ?_
        filter_upwards [hrep] with x hx
        simpa [Finset.sum_insert, ha, Pi.add_apply, add_comm, add_left_comm, add_assoc] using hx
      · have htri :
          WeakGridSpace.BesovishSpace.Norm_Costpq A q (yS + ya) ≤
            WeakGridSpace.BesovishSpace.Norm_Costpq A q yS +
              WeakGridSpace.BesovishSpace.Norm_Costpq A q ya :=
          WeakGridSpace.BesovishSpace.Norm_Costpq_add_le
            (A := A) (q := q) hp_top
            (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (A := A) q)
            yS ya
        calc
          WeakGridSpace.BesovishSpace.Norm_Costpq A q (yS + ya)
              ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A q yS +
                  WeakGridSpace.BesovishSpace.Norm_Costpq A q ya := htri
          _ ≤
              (∑ i ∈ S,
                  (souzaPointwiseSelfsTailNorm G s p q hs hp hp_top (t i) (g i) + ε)) +
                (souzaPointwiseSelfsTailNorm G s p q hs hp hp_top (t a) (g a) + ε) :=
                add_le_add hyS_norm hya_norm
          _ =
              ∑ i ∈ insert a S,
                (souzaPointwiseSelfsTailNorm G s p q hs hp hp_top (t i) (g i) + ε) := by
                rw [Finset.sum_insert ha]
                ring

/--
Local finite-sum estimate for the indices whose supports meet the source cell.

Condition A controls the sum of the relevant tail seminorms by `N`; this lemma
turns that scalar control into a Besov representative for the corresponding
finite sum of products with one fixed Souza atom.
-/
private theorem exists_souzaRelevantTailProduct_norm_le_N_add
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) {N : ℝ}
    (hTail : ∀ i ∈ Λ, ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G s p q hs hp hp_top (t i) (g i) C)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    [DecidablePred fun i => goodGridLevelCellMeetsSupport G Q (g i)]
    (hA : nonArchimedeanRelevantTailSelfsSum
      G s p q hs hp hp_top Λ t g Q ≤ N)
    (hLevel : ∀ i, i ∈ Λ →
      goodGridLevelCellMeetsSupport G Q (g i) → t i ≤ k)
    {ε : ℝ} (hε : 0 < ε)
    (φ : ((souzaAtomFamily G s p hs hp hp_top).localSpace
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier)
    (hφ : φ ∈ (souzaAtomFamily G s p hs hp hp_top).atoms
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun x => ∑ i ∈ Λ.filter (fun i => goodGridLevelCellMeetsSupport G Q (g i)),
          g i x *
            (souzaAtomFamily G s p hs hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s p hs hp hp_top) q y ≤
          N + ((Λ.filter (fun i => goodGridLevelCellMeetsSupport G Q (g i))).card : ℝ) * ε := by
  classical
  let S : Finset ℕ := Λ.filter (fun i => goodGridLevelCellMeetsSupport G Q (g i))
  have hTailS : ∀ i ∈ S, ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G s p q hs hp hp_top (t i) (g i) C := by
    intro i hi
    exact hTail i ((Finset.mem_filter.mp hi).1)
  have hLevelS : ∀ i ∈ S, t i ≤ k := by
    intro i hi
    exact hLevel i ((Finset.mem_filter.mp hi).1) ((Finset.mem_filter.mp hi).2)
  rcases exists_souzaTailProduct_finset_sum_norm_le
      G s p q hs hp hp_top S t g hTailS hε Q hLevelS φ hφ with
    ⟨y, hy_rep, hy_norm⟩
  refine ⟨y, by simpa [S] using hy_rep, ?_⟩
  have hsum_tail_le :
      ∑ i ∈ S, souzaPointwiseSelfsTailNorm G s p q hs hp hp_top (t i) (g i) ≤ N := by
    have hsum_eq :
        ∑ i ∈ S, souzaPointwiseSelfsTailNorm G s p q hs hp hp_top (t i) (g i) =
          nonArchimedeanRelevantTailSelfsSum G s p q hs hp hp_top Λ t g Q := by
      dsimp [S, nonArchimedeanRelevantTailSelfsSum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hmeet : goodGridLevelCellMeetsSupport G Q (g i)
      · simp [hmeet]
      · simp [hmeet]
    exact hsum_eq.trans_le hA
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s p hs hp hp_top) q y
        ≤ ∑ i ∈ S,
            (souzaPointwiseSelfsTailNorm G s p q hs hp hp_top (t i) (g i) + ε) := hy_norm
    _ = (∑ i ∈ S,
          souzaPointwiseSelfsTailNorm G s p q hs hp hp_top (t i) (g i)) +
        (S.card : ℝ) * ε := by
          rw [Finset.sum_add_distrib]
          simp [mul_comm]
    _ ≤ N + (S.card : ℝ) * ε := by
          simpa [add_comm] using add_le_add_right hsum_tail_le ((S.card : ℝ) * ε)
    _ = N + ((Λ.filter (fun i => goodGridLevelCellMeetsSupport G Q (g i))).card : ℝ) * ε := by
          rfl

/--
Terms whose multiplier support does not meet the source cell do not contribute
to the product with an atom supported on that cell.
-/
private theorem sum_souzaAtom_products_eq_relevant_filter
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (Λ : Finset ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    [DecidablePred fun i => goodGridLevelCellMeetsSupport G Q (g i)]
    (φ : ((souzaAtomFamily G s p hs hp hp_top).localSpace
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier) :
    (fun x => ∑ i ∈ Λ,
      g i x *
        (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x) =
    (fun x => ∑ i ∈ Λ.filter (fun i => goodGridLevelCellMeetsSupport G Q (g i)),
      g i x *
        (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x) := by
  classical
  funext x
  let term : ℕ → ℂ := fun i =>
    g i x *
      (souzaAtomFamily G s p hs hp hp_top).toFunction
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x
  calc
    ∑ i ∈ Λ, term i
        = ∑ i ∈ Λ,
            if goodGridLevelCellMeetsSupport G Q (g i) then term i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hmeet : goodGridLevelCellMeetsSupport G Q (g i)
          · simp [hmeet]
          · have hzero_fun :=
              mul_souzaAtom_eq_zero_of_not_meetsSupport
                G s p hs hp hp_top Q hmeet φ
            have hzero : term i = 0 := by
              simpa [term] using congrFun hzero_fun x
            simp [hmeet, hzero]
    _ = ∑ i ∈ Λ.filter (fun i => goodGridLevelCellMeetsSupport G Q (g i)), term i := by
          rw [Finset.sum_filter]

/--
The local estimate for the full finite multiplier sum against one fixed Souza
atom. Non-relevant indices are discarded by support, and condition A controls
the remaining tail seminorms.
-/
private theorem exists_souzaTailProduct_full_sum_norm_le_N_add
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) {N : ℝ}
    (hTail : ∀ i ∈ Λ, ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G s p q hs hp hp_top (t i) (g i) C)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    [DecidablePred fun i => goodGridLevelCellMeetsSupport G Q (g i)]
    (hA : nonArchimedeanRelevantTailSelfsSum
      G s p q hs hp hp_top Λ t g Q ≤ N)
    (hLevel : ∀ i, i ∈ Λ →
      goodGridLevelCellMeetsSupport G Q (g i) → t i ≤ k)
    {ε : ℝ} (hε : 0 < ε)
    (φ : ((souzaAtomFamily G s p hs hp hp_top).localSpace
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier)
    (hφ : φ ∈ (souzaAtomFamily G s p hs hp hp_top).atoms
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun x => ∑ i ∈ Λ,
          g i x *
            (souzaAtomFamily G s p hs hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ x)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s p hs hp hp_top) q y ≤
          N + ((Λ.filter (fun i => goodGridLevelCellMeetsSupport G Q (g i))).card : ℝ) * ε := by
  classical
  rcases exists_souzaRelevantTailProduct_norm_le_N_add
      G s p q hs hp hp_top Λ t g hTail Q hA hLevel hε φ hφ with
    ⟨y, hy_rep, hy_norm⟩
  refine ⟨y, ?_, hy_norm⟩
  have hsum_eq :=
    sum_souzaAtom_products_eq_relevant_filter G s p hs hp hp_top Λ g Q φ
  simpa [hsum_eq] using hy_rep

/--
If a concrete representative of a Souza Besov element is supported in a
good-grid cell, then the induced restriction theorem represents the same
concrete function on the induced grid.
-/
private theorem supported_souzaBesov_restrictsToInduced
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hs_lt_inv : s < (p.toReal)⁻¹)
    (Q : GoodGridCell G) (F : α → ℂ)
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (hx : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) F
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hF_support : ∀ z, z ∉ Q.cell → F z = 0) :
    ∃ y : WeakGridSpace.BesovishSpace
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
          (souzaAtomFamily G s p hs hp hp_top)) q,
      WeakGridSpace.RepresentsFunction
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell)
        (p := p) F
        (y : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Q.toLevelCell
            (souzaAtomFamily G s p hs hp hp_top)) q y ≤
        (2 * souzaAmbientRestrictionMultiplierConstant G s p + 1) *
          WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s p hs hp hp_top) q x := by
  classical
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  rcases souzaCellIndicatorRestrictsToInduced
      G s p q hs hp hp_top hs_lt_inv Q x with
    ⟨y, hy_prod, hy_norm⟩
  refine ⟨y, ?_, hy_norm⟩
  have hxWi : ((x : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =ᵐ[Wi.measure] F := by
    simpa [Wi, WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid,
      GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid] using hx
  refine hy_prod.trans ?_
  filter_upwards [hxWi] with z hz
  by_cases hzQ : z ∈ Q.cell
  · rw [Set.indicator_of_mem hzQ, one_mul]
    exact hz
  · rw [Set.indicator_of_notMem hzQ, zero_mul, hF_support z hzQ]

/--
The product of a multiplier sum with a Souza atom supported on `Q` is still
supported on `Q`.
-/
private theorem sum_souzaAtom_products_supported
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (Λ : Finset ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (φ : ((souzaAtomFamily G s p hs hp hp_top).localSpace
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier) :
    ∀ z, z ∉ Q.1 →
      (∑ i ∈ Λ,
        g i z *
          (souzaAtomFamily G s p hs hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ z) = 0 := by
  classical
  intro z hzQ
  have hφ_zero :
      (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ z = 0 :=
    (souzaAtomFamily G s p hs hp hp_top).local_support
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ z hzQ
  simp [hφ_zero]

/--
Local β-Besov representative for the multiplier sum against one source Souza
atom, read on the grid induced by the source cell.

This combines the finite tail estimate with the induced restriction theorem.
It is the β-level input for the subsequent β-to-s conversion and transmutation
step.
-/
private theorem exists_souzaTailProduct_full_sum_induced_beta_norm_le_N_add
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) {N : ℝ}
    (hTail : ∀ i ∈ Λ, ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top (t i) (g i) C)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    [DecidablePred fun i => goodGridLevelCellMeetsSupport G Q (g i)]
    (hA : nonArchimedeanRelevantTailSelfsSum
      G β p qtilde hβ hp hp_top Λ t g Q ≤ N)
    (hLevel : ∀ i, i ∈ Λ →
      goodGridLevelCellMeetsSupport G Q (g i) → t i ≤ k)
    {ε : ℝ} (hε : 0 < ε)
    (φ : ((souzaAtomFamily G β p hβ hp hp_top).localSpace
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier)
    (hφ : φ ∈ (souzaAtomFamily G β p hβ hp hp_top).atoms
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)) :
    ∃ yβ : WeakGridSpace.BesovishSpace
        (inducedSouzaAtomFamily G β p hβ (inferInstance : Fact (1 ≤ p)) hp_top
          (goodGridCellOfLevelCell G Q)) qtilde,
      WeakGridSpace.RepresentsFunction
        (G := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace
          (goodGridCellOfLevelCell G Q).toLevelCell)
        (p := p)
        (fun z => ∑ i ∈ Λ,
          g i z *
            (souzaAtomFamily G β p hβ hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ z)
        (yβ : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace
            (goodGridCellOfLevelCell G Q).toLevelCell).measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (inducedSouzaAtomFamily G β p hβ (inferInstance : Fact (1 ≤ p)) hp_top
            (goodGridCellOfLevelCell G Q)) qtilde yβ ≤
        (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
          (N + ((Λ.filter (fun i => goodGridLevelCellMeetsSupport G Q (g i))).card : ℝ) *
            ε) := by
  classical
  let QG : GoodGridCell G := goodGridCellOfLevelCell G Q
  let F : α → ℂ := fun z => ∑ i ∈ Λ,
    g i z *
      (souzaAtomFamily G β p hβ hp hp_top).toFunction
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φ z
  rcases exists_souzaTailProduct_full_sum_norm_le_N_add
      G β p qtilde hβ hp hp_top Λ t g hTail Q hA hLevel hε φ hφ with
    ⟨yamb, hyamb_rep, hyamb_norm⟩
  have hF_support : ∀ z, z ∉ QG.cell → F z = 0 := by
    simpa [F, QG, goodGridCellOfLevelCell] using
      sum_souzaAtom_products_supported G β p hβ hp hp_top Λ g Q φ
  rcases supported_souzaBesov_restrictsToInduced
      G β p qtilde hβ hp hp_top hβ_lt_inv QG F yamb hyamb_rep hF_support with
    ⟨yβ, hyβ_rep, hyβ_norm⟩
  refine ⟨yβ, by simpa [F, QG, goodGridCellOfLevelCell] using hyβ_rep, ?_⟩
  have hK_nonneg : 0 ≤ 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1 := by
    have hK0 := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
    linarith
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq
        (inducedSouzaAtomFamily G β p hβ (inferInstance : Fact (1 ≤ p)) hp_top QG)
        qtilde yβ
        ≤ (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
            WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G β p hβ hp hp_top) qtilde yamb := hyβ_norm
    _ ≤ (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
          (N + ((Λ.filter (fun i => goodGridLevelCellMeetsSupport G Q (g i))).card : ℝ) *
            ε) := by
          exact mul_le_mul_of_nonneg_left hyamb_norm hK_nonneg

/--
Rescale a Souza atom of smoothness `s` on one cell into a Souza atom of
smoothness `β` on the same cell.

Pointwise, the original `s`-atom is `μ(Q)^(s-β)` times the rescaled `β`-atom.
This is the normalization cancellation used in the non-Archimedean estimate.
-/
private theorem exists_beta_souzaAtom_of_s_souzaAtom
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (φs : ((souzaAtomFamily G s p hs hp hp_top).localSpace
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier)
    (hφs : φs ∈ (souzaAtomFamily G s p hs hp hp_top).atoms
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)) :
    ∃ φβ : ((souzaAtomFamily G β p hβ hp hp_top).localSpace
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier,
      φβ ∈ (souzaAtomFamily G β p hβ hp hp_top).atoms
        (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) ∧
      (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φs =
        fun z => (((G.grid.μ Q.1).toReal ^ (s - β) : ℝ) : ℂ) *
          (souzaAtomFamily G β p hβ hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φβ z := by
  classical
  change ℂ at φs
  change φs ∈ souzaAtomsSet G s p (goodGridCellOfLevelCell G Q) at hφs
  change ∃ φβ : ℂ,
      φβ ∈ souzaAtomsSet G β p (goodGridCellOfLevelCell G Q) ∧
      (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φs =
        fun z => (((G.grid.μ Q.1).toReal ^ (s - β) : ℝ) : ℂ) *
          (souzaAtomFamily G β p hβ hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φβ z
  let μQ : ℝ := (G.grid.μ Q.1).toReal
  let φβ : ℂ := (((μQ ^ (β - s) : ℝ) : ℂ) * (φs : ℂ))
  refine ⟨φβ, ?_, ?_⟩
  · have hQ_pos : 0 < G.grid.μ Q.1 :=
      G.grid.positive_measure k Q.1 Q.2
    have hQ_finite : G.grid.μ Q.1 ≠ ∞ := by
      letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Q.1
    have hμ_pos : 0 < μQ := ENNReal.toReal_pos hQ_pos.ne' hQ_finite
    have hscale_nonneg : 0 ≤ μQ ^ (β - s) :=
      Real.rpow_nonneg hμ_pos.le _
    have hφs_bound :
        ‖(φs : ℂ)‖ ≤ μQ ^ (s - (p.toReal)⁻¹) := by
      simpa [μQ, souzaAtomsSet, goodGridCellOfLevelCell] using hφs
    change ‖φβ‖ ≤ μQ ^ (β - (p.toReal)⁻¹)
    calc
      ‖φβ‖ = μQ ^ (β - s) * ‖(φs : ℂ)‖ := by
        simp [φβ, Complex.norm_real, Real.norm_of_nonneg hscale_nonneg]
      _ ≤ μQ ^ (β - s) * μQ ^ (s - (p.toReal)⁻¹) := by
        exact mul_le_mul_of_nonneg_left hφs_bound hscale_nonneg
      _ = μQ ^ (β - (p.toReal)⁻¹) := by
        rw [← Real.rpow_add hμ_pos]
        ring_nf
  · funext z
    have hQ_pos : 0 < G.grid.μ Q.1 :=
      G.grid.positive_measure k Q.1 Q.2
    have hQ_finite : G.grid.μ Q.1 ≠ ∞ := by
      letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Q.1
    have hμ_pos : 0 < μQ := ENNReal.toReal_pos hQ_pos.ne' hQ_finite
    have hscale :
        (((μQ ^ (s - β) : ℝ) : ℂ) *
            (((μQ ^ (β - s) : ℝ) : ℂ) * (φs : ℂ))) = (φs : ℂ) := by
      have hscaleR : μQ ^ (s - β) * μQ ^ (β - s) = 1 := by
        calc
          μQ ^ (s - β) * μQ ^ (β - s)
              = μQ ^ ((s - β) + (β - s)) := by
                  rw [← Real.rpow_add hμ_pos]
          _ = μQ ^ (0 : ℝ) := by ring_nf
          _ = 1 := by rw [Real.rpow_zero]
      have hscaleC :
          (((μQ ^ (s - β) : ℝ) : ℂ) *
              ((μQ ^ (β - s) : ℝ) : ℂ)) = 1 := by
        exact_mod_cast hscaleR
      calc
        (((μQ ^ (s - β) : ℝ) : ℂ) *
            (((μQ ^ (β - s) : ℝ) : ℂ) * (φs : ℂ)))
            = ((((μQ ^ (s - β) : ℝ) : ℂ) *
                ((μQ ^ (β - s) : ℝ) : ℂ)) * (φs : ℂ)) := by ring
        _ = (φs : ℂ) := by rw [hscaleC]; ring
    change (Q.1.indicator (fun _ => φs)) z =
      (((G.grid.μ Q.1).toReal ^ (s - β) : ℝ) : ℂ) *
        (Q.1.indicator (fun _ => φβ)) z
    by_cases hzQ : z ∈ Q.1
    · rw [Set.indicator_of_mem hzQ, Set.indicator_of_mem hzQ]
      simpa [φβ, μQ] using hscale.symm
    · rw [Set.indicator_of_notMem hzQ, Set.indicator_of_notMem hzQ]
      simp

/-- Scaling a grid representation scales each level coefficient power by `‖c‖^p`. -/
private theorem lpGridRepresentation_smul_levelCoeffPower
    {W : WeakGridSpace.WeakGridSpace (α := α)} {s : ℝ} {p u : ℝ≥0∞}
    [Fact (1 ≤ p)] {A : WeakGridSpace.AtomFamily W s p u}
    {g : Lp ℂ p W.measure} (c : ℂ)
    (R : WeakGridSpace.LpGridRepresentation A g) (k : ℕ) :
    (WeakGridSpace.LpGridRepresentation.smul (A := A) c R).levelCoeffPower k =
      ‖c‖ ^ p.toReal * R.levelCoeffPower k := by
  unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
  unfold WeakGridSpace.LpGridRepresentation.smul WeakGridSpace.LevelBlock.smul
  calc
    (∑ Q : WeakGridSpace.LevelCell W k, ‖c * (R.block k).coeff Q‖ ^ p.toReal)
        = ∑ Q : WeakGridSpace.LevelCell W k,
            (‖c‖ * ‖(R.block k).coeff Q‖) ^ p.toReal := by
          refine Finset.sum_congr rfl ?_
          intro Q _hQ
          rw [norm_mul]
    _ = ∑ Q : WeakGridSpace.LevelCell W k,
          ‖c‖ ^ p.toReal * ‖(R.block k).coeff Q‖ ^ p.toReal := by
          refine Finset.sum_congr rfl ?_
          intro Q _hQ
          rw [Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
    _ = ‖c‖ ^ p.toReal *
          ∑ Q : WeakGridSpace.LevelCell W k, ‖(R.block k).coeff Q‖ ^ p.toReal := by
          rw [Finset.mul_sum]

/--
After converting a representation from smoothness `β` to smoothness `s`, each
target level is bounded by the deterministic smoothness weight times the
original representation cost.
-/
private theorem smoothnessScaleToBase_levelCoeffRoot_le_pqCost
    (W : _root_.WeakGridSpace.WeakGridSpace (α := α)) (s β : ℝ) (p q : ℝ≥0∞)
    {u : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A : _root_.WeakGridSpace.AtomFamily W s p u)
    (hβ : 0 < β) (hsβ : s ≤ β)
    {g : Lp ℂ p W.measure}
    (R : _root_.WeakGridSpace.LpGridRepresentation
      (A.smoothnessScaleAtomFamily β hβ) g)
    (hRfin : _root_.WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (k : ℕ) :
    ((_root_.WeakGridSpace.AtomFamily.smoothnessScaleToBaseRepresentation
        A β hβ R).levelCoeffPower k) ^ (1 / p.toReal) ≤
      _root_.WeakGridSpace.AtomFamily.smoothnessScaleLevelWeight W s β p k *
        _root_.WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  calc
    ((_root_.WeakGridSpace.AtomFamily.smoothnessScaleToBaseRepresentation
        A β hβ R).levelCoeffPower k) ^ (1 / p.toReal)
        ≤ _root_.WeakGridSpace.AtomFamily.smoothnessScaleLevelWeight W s β p k *
            (R.levelCoeffPower k) ^ (1 / p.toReal) :=
          _root_.WeakGridSpace.AtomFamily.smoothnessScaleToBase_levelCoeffRoot_le
            A β hβ hsβ R k
    _ ≤ _root_.WeakGridSpace.AtomFamily.smoothnessScaleLevelWeight W s β p k *
          _root_.WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
        exact mul_le_mul_of_nonneg_left
          (_root_.WeakGridSpace.AtomFamily.levelCoeffRoot_le_pqCost
            (A.smoothnessScaleAtomFamily β hβ) R hRfin k)
          (_root_.WeakGridSpace.AtomFamily.smoothnessScaleLevelWeight_nonneg W s β p k)

/--
Convert a β-Souza Besov element on the grid induced by `Q` into an ambient
Souza-s representation localized in `Q`.

The estimate is the coefficient-level form needed by transmutation: after the
ambient reindexing, no coefficients occur before `Q.level`, no coefficients
occur outside cells contained in `Q`, and the level powers decay geometrically
with ratio `(lambda2^(β-s))^p`.
-/
private theorem inducedSouzaBetaBesov_to_ambientSouzaS_geometric
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    (Q : GoodGridCell G)
    (yβ : WeakGridSpace.BesovishSpace
      (inducedSouzaAtomFamily G β p hβ (inferInstance : Fact (1 ≤ p)) hp_top Q) qtilde)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        (WeakGridSpace.inducedLpToAmbient G.toWeakGridSpace Q.toLevelCell
          (yβ : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell).measure)),
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
      (∀ j : ℕ, ∀ S : WeakGridSpace.LevelCell G.toWeakGridSpace j,
        (¬ S.1 ⊆ Q.cell → (R.block j).coeff S = 0) ∧
        (j < Q.level → (R.block j).coeff S = 0)) ∧
      ∀ j : ℕ, Q.level ≤ j →
        R.levelCoeffPower j ≤
          (((G.grid.μ Q.cell).toReal ^ (β - s) *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                (inducedSouzaAtomFamily G β p hβ
                  (inferInstance : Fact (1 ≤ p)) hp_top Q) qtilde yβ + ε)) ^
              p.toReal) *
            ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) ^ (j - Q.level) := by
  classical
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Q.toLevelCell
  let Aβi := inducedSouzaAtomFamily G β p hβ
    (inferInstance : Fact (1 ≤ p)) hp_top Q
  let AS := souzaAtomFamily G s p hs hp hp_top
  let ASi := inducedSouzaAtomFamily G s p hs
    (inferInstance : Fact (1 ≤ p)) hp_top Q
  let normβ : ℝ := WeakGridSpace.BesovishSpace.Norm_Costpq Aβi qtilde yβ
  let μQ : ℝ := (G.grid.μ Q.cell).toReal
  let scale : ℝ := μQ ^ (β - s) * (normβ + ε)
  let lamRoot : ℝ := G.grid.lambda2 ^ (β - s)
  let lam : ℝ := lamRoot ^ p.toReal
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hdelta_pos : 0 < β - s := sub_pos.mpr hβs
  have hlambda2_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  have hlambda2_nonneg : 0 ≤ G.grid.lambda2 := hlambda2_pos.le
  have hlamRoot_pos : 0 < lamRoot := Real.rpow_pos_of_pos hlambda2_pos (β - s)
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlamRoot_pos p.toReal
  have hlamRoot_lt_one : lamRoot < 1 :=
    Real.rpow_lt_one hlambda2_pos.le G.grid.hlambda2_lt_one hdelta_pos
  have hlam_lt : lam < 1 :=
    Real.rpow_lt_one hlamRoot_pos.le hlamRoot_lt_one hp_pos
  have hfiniteβ :
      WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations (A := Aβi) qtilde :=
    WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations Aβi qtilde
  have hnormβ_nonneg : 0 ≤ normβ :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
      (A := Aβi) (q := qtilde) hfiniteβ yβ
  have hnormβ_add_nonneg : 0 ≤ normβ + ε := by linarith
  have hμQ_nonneg : 0 ≤ μQ := ENNReal.toReal_nonneg
  have hscale_nonneg : 0 ≤ scale := by
    exact mul_nonneg (Real.rpow_nonneg hμQ_nonneg _) hnormβ_add_nonneg
  rcases WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add
      (A := Aβi) (q := qtilde) hfiniteβ yβ hε with
    ⟨Rβ, hRβfin, hRβcost_lt⟩
  let Rsi :=
    inducedSouzaBetaRepresentationToSouzaS G s β p hs hβ
      (inferInstance : Fact (1 ≤ p)) hp_top Q Rβ
  have hRsi_decay :
      ∀ n : ℕ, Rsi.levelCoeffPower n ≤ scale ^ p.toReal * lam ^ n := by
    intro n
    have hroot₀ :
        (Rsi.levelCoeffPower n) ^ (1 / p.toReal) ≤
          WeakGridSpace.LpGridRepresentation.levelMeasureWeight Wi (β - s) p p n *
            WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rβ := by
      simpa [Rsi, Wi, Aβi, inducedSouzaBetaRepresentationToSouzaS_levelCoeffPower] using
        besovToSouzaScaledCoeffPower_root_le
          G s β p qtilde hβ hβs hp_top Q Rβ hRβfin n
    have hweight :
        WeakGridSpace.LpGridRepresentation.levelMeasureWeight Wi (β - s) p p n
          ≤ μQ ^ (β - s) * lamRoot ^ n := by
      have h :=
        induced_levelMeasureWeight_le_geometric G Q (β - s) p hdelta_pos n
      have hgeom :
          (G.grid.lambda2 ^ n : ℝ) ^ (β - s) = lamRoot ^ n := by
        calc
          (G.grid.lambda2 ^ n : ℝ) ^ (β - s) =
              G.grid.lambda2 ^ ((n : ℝ) * (β - s)) := by
                simpa [mul_comm] using
                  (Real.rpow_natCast_mul hlambda2_nonneg n (β - s)).symm
          _ = G.grid.lambda2 ^ ((β - s) * n) := by ring_nf
          _ = lamRoot ^ n := by
                simpa [lamRoot, mul_comm] using
                  Real.rpow_mul_natCast hlambda2_nonneg (β - s) n
      simpa [Wi, μQ, hgeom] using h
    have hcost :
        WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rβ ≤ normβ + ε :=
      le_of_lt (by simpa [Aβi, normβ] using hRβcost_lt)
    have hcost_nonneg :
        0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rβ :=
      WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rβ
    have hweight_nonneg :
        0 ≤ WeakGridSpace.LpGridRepresentation.levelMeasureWeight Wi (β - s) p p n :=
      WeakGridSpace.LpGridRepresentation.levelMeasureWeight_nonneg Wi (β - s) p p n
    have hgeom_nonneg : 0 ≤ μQ ^ (β - s) * lamRoot ^ n :=
      mul_nonneg (Real.rpow_nonneg hμQ_nonneg _) (pow_nonneg hlamRoot_pos.le n)
    have hroot :
        (Rsi.levelCoeffPower n) ^ (1 / p.toReal) ≤ scale * lamRoot ^ n := by
      calc
        (Rsi.levelCoeffPower n) ^ (1 / p.toReal)
            ≤ WeakGridSpace.LpGridRepresentation.levelMeasureWeight Wi (β - s) p p n *
                WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rβ := hroot₀
        _ ≤ (μQ ^ (β - s) * lamRoot ^ n) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rβ := by
              exact mul_le_mul_of_nonneg_right hweight hcost_nonneg
        _ ≤ (μQ ^ (β - s) * lamRoot ^ n) * (normβ + ε) := by
              exact mul_le_mul_of_nonneg_left hcost hgeom_nonneg
        _ = scale * lamRoot ^ n := by
              ring
    have hleft :
        ((Rsi.levelCoeffPower n) ^ (1 / p.toReal)) ^ p.toReal =
          Rsi.levelCoeffPower n := by
      have hmul : (1 / p.toReal) * p.toReal = 1 := by
        field_simp [hp_pos.ne']
      calc
        ((Rsi.levelCoeffPower n) ^ (1 / p.toReal)) ^ p.toReal =
            (Rsi.levelCoeffPower n) ^ ((1 / p.toReal) * p.toReal) := by
            rw [← Real.rpow_mul (Rsi.levelCoeffPower_nonneg n)]
        _ = Rsi.levelCoeffPower n := by
            rw [hmul, Real.rpow_one]
    have hright_nonneg : 0 ≤ scale * lamRoot ^ n :=
      mul_nonneg hscale_nonneg (pow_nonneg hlamRoot_pos.le n)
    have hpow_geom :
        (lamRoot ^ n : ℝ) ^ p.toReal = lam ^ n := by
      calc
        (lamRoot ^ n : ℝ) ^ p.toReal =
            lamRoot ^ ((n : ℝ) * p.toReal) := by
              simpa [mul_comm] using
                (Real.rpow_natCast_mul hlamRoot_pos.le n p.toReal).symm
        _ = lamRoot ^ (p.toReal * n) := by ring_nf
        _ = lam ^ n := by
              simpa [lam, mul_comm] using
                Real.rpow_mul_natCast hlamRoot_pos.le p.toReal n
    have htarget :
        (scale * lamRoot ^ n) ^ p.toReal = scale ^ p.toReal * lam ^ n := by
      calc
        (scale * lamRoot ^ n) ^ p.toReal =
            scale ^ p.toReal * (lamRoot ^ n : ℝ) ^ p.toReal := by
              rw [Real.mul_rpow hscale_nonneg (pow_nonneg hlamRoot_pos.le n)]
        _ = scale ^ p.toReal * lam ^ n := by rw [hpow_geom]
    have hpow :=
      Real.rpow_le_rpow
        (Real.rpow_nonneg (Rsi.levelCoeffPower_nonneg n) _)
        hroot hp_pos.le
    rwa [hleft, htarget] at hpow
  have hC_nonneg : 0 ≤ scale ^ p.toReal :=
    Real.rpow_nonneg hscale_nonneg _
  have hRsi_fin :
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rsi :=
    finitePQCost_of_levelCoeffPower_geometric_decay
      Rsi (scale ^ p.toReal) lam hC_nonneg hlam_pos hlam_lt hRsi_decay
  let RA :=
    WeakGridSpace.inducedRepresentationToAmbient G.toWeakGridSpace Q.toLevelCell AS Rsi
  have hRA_fin :
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) RA :=
    WeakGridSpace.inducedRepresentationToAmbient_finitePQCost
      G.toWeakGridSpace Q.toLevelCell AS Rsi hRsi_fin
  refine ⟨RA, hRA_fin, ?_, ?_⟩
  · intro j S
    constructor
    · intro hS
      simpa [RA, AS] using
        WeakGridSpace.inducedRepresentationToAmbient_coeff_eq_zero_of_not_subset
          G.toWeakGridSpace Q.toLevelCell AS Rsi S hS
    · intro hj
      simpa [RA, AS] using
        WeakGridSpace.inducedRepresentationToAmbient_coeff_lt
          G.toWeakGridSpace Q.toLevelCell AS Rsi hj S
  · intro j hj
    let n : ℕ := j - Q.level
    have hj_eq : j = Q.level + n := by
      dsimp [n]
      omega
    calc
      RA.levelCoeffPower j = Rsi.levelCoeffPower n := by
        rw [hj_eq]
        simpa [RA, AS, n] using
          WeakGridSpace.inducedRepresentationToAmbient_levelCoeffPower_add
            G.toWeakGridSpace Q.toLevelCell AS Rsi
      _ ≤ scale ^ p.toReal * lam ^ n := hRsi_decay n
      _ =
          (((G.grid.μ Q.cell).toReal ^ (β - s) *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                (inducedSouzaAtomFamily G β p hβ
                  (inferInstance : Fact (1 ≤ p)) hp_top Q) qtilde yβ + ε)) ^
              p.toReal) *
            ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) ^ (j - Q.level) := by
          rw [show j - Q.level = n by rfl]

/-- **Rung B (positivity transfer).** Reading a *positive* ambient `β`-representation
that is supported on `Qc` (zero blocks before `Qc.level`, zero coefficients outside
`Qc.cell`) as a representation on the grid induced by `Qc` keeps the coefficients
nonnegative reals and the atoms pointwise positive on their cells.  The induced
blocks are literal reindexings of the ambient blocks, so positivity is inherited. -/
private theorem ambientSupportedRepresentationToInduced_souzaPositive
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    (Qc : GoodGridCell G)
    {g : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G β p hβ hp hp_top) g)
    (hR : SouzaPositiveRepresentation G β p hβ hp hp_top R)
    (hbefore : ∀ n, n < Qc.level →
      (R.block n).toLp (souzaAtomFamily G β p hβ hp hp_top) = 0)
    (houtside : ∀ n (P : WeakGridSpace.LevelCell G.toWeakGridSpace n),
      ¬ P.1 ⊆ Qc.cell → (R.block n).coeff P = 0) :
    (∀ (i : ℕ) (P : WeakGridSpace.LevelCell
        (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Qc.toLevelCell) i),
      ∃ r : NNReal,
        ((WeakGridSpace.ambientSupportedRepresentationToInduced G.toWeakGridSpace
          Qc.toLevelCell (souzaAtomFamily G β p hβ hp hp_top) R hbefore houtside).block i).coeff P
          = (r : ℂ)) ∧
    (∀ (i : ℕ) (P : WeakGridSpace.LevelCell
        (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Qc.toLevelCell) i)
        (x : α), x ∈ P.1 →
      ∃ a : NNReal, 0 < a ∧
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Qc.toLevelCell
            (souzaAtomFamily G β p hβ hp hp_top)).toFunction
          (WeakGridSpace.levelCellToWeakGridCell
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Qc.toLevelCell) i P)
          (((WeakGridSpace.ambientSupportedRepresentationToInduced G.toWeakGridSpace
            Qc.toLevelCell (souzaAtomFamily G β p hβ hp hp_top) R hbefore houtside).block i).atom P)
            x
          = (a : ℂ)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i P
    obtain ⟨c, hc, hcoeff, _⟩ :=
      hR (Qc.level + i)
        (WeakGridSpace.inducedLevelCellToAmbient G.toWeakGridSpace Qc.toLevelCell P)
    refine ⟨⟨c, hc⟩, ?_⟩
    show (WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace Qc.toLevelCell
        (souzaAtomFamily G β p hβ hp hp_top) (R.block (Qc.level + i))).coeff P = _
    rw [WeakGridSpace.ambientLevelBlockToInduced_coeff, hcoeff]
    norm_cast
  · intro i P x hx
    obtain ⟨c, hc, _, hatom⟩ :=
      hR (Qc.level + i)
        (WeakGridSpace.inducedLevelCellToAmbient G.toWeakGridSpace Qc.toLevelCell P)
    have hμpos : 0 < (G.grid.μ P.1).toReal := by
      have hp1 : 0 < G.grid.μ P.1 := by
        simpa [WeakGridSpace.inducedWeakGridSpace, WeakGridSpace.inducedWeakGrid,
          GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
          WeakGridSpace.WeakGridSpace.measure] using
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Qc.toLevelCell).grid.positive_measure
            i P.1 P.2
      have hpfin : G.grid.μ P.1 ≠ ∞ := by
        letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
        exact MeasureTheory.measure_ne_top G.grid.μ P.1
      exact ENNReal.toReal_pos hp1.ne' hpfin
    have haval_pos : 0 < (G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹) :=
      Real.rpow_pos_of_pos hμpos _
    refine ⟨⟨(G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹), haval_pos.le⟩, ?_, ?_⟩
    · rw [← NNReal.coe_lt_coe]; simpa using haval_pos
    · show (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace Qc.toLevelCell
          (souzaAtomFamily G β p hβ hp hp_top)).toFunction
          (WeakGridSpace.levelCellToWeakGridCell
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace Qc.toLevelCell) i P)
          ((WeakGridSpace.ambientLevelBlockToInduced G.toWeakGridSpace Qc.toLevelCell
            (souzaAtomFamily G β p hβ hp hp_top) (R.block (Qc.level + i))).atom P) x = _
      rw [WeakGridSpace.ambientLevelBlockToInduced_atom_toFunction, hatom]
      have hcan : canonicalSouzaAtom G β p (goodGridCellOfLevelCell G
            (WeakGridSpace.inducedLevelCellToAmbient G.toWeakGridSpace Qc.toLevelCell P)) x
          = (((G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹) : ℝ) : ℂ) := by
        simp [canonicalSouzaAtom, goodGridCellOfLevelCell,
          WeakGridSpace.inducedLevelCellToAmbient, hx]
      rw [hcan]
      norm_cast

/-- The canonical `(s,p)`-Souza atom equals `μ(Q)^(s-β)` times the canonical
`(β,p)`-Souza atom on the same cell. -/
private theorem canonicalSouzaAtom_eq_smul_beta
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (Qc : GoodGridCell G) (x : α) :
    canonicalSouzaAtom G s p Qc x =
      (((G.grid.μ Qc.cell).toReal ^ (s - β) : ℝ) : ℂ) *
        canonicalSouzaAtom G β p Qc x := by
  classical
  have hμ_pos : 0 < (G.grid.μ Qc.cell).toReal :=
    ENNReal.toReal_pos (GoodGridCell.measure_pos Qc).ne'
      (GoodGridCell.measure_ne_top Qc)
  by_cases hx : x ∈ Qc.cell
  · simp only [canonicalSouzaAtom, dif_pos hx]
    rw [← Complex.ofReal_mul, ← Real.rpow_add hμ_pos,
      show s - β + (β - (p.toReal)⁻¹) = s - (p.toReal)⁻¹ from by ring]
  · simp [canonicalSouzaAtom, hx]

/-- **Positive local product block for a single multiplier.**

If the multiplier `m` has a finite positive `selfs` tail seminorm at level
`t ≤ k`, then the product of `m` with the canonical `(s,p)`-Souza atom on a
cell `Q` of level `k` admits a **positive** ambient Souza-`s` representation
supported in `Q`, starting at level `k`, with levelwise coefficient roots
decaying geometrically with ratio `lambda2^(β-s)` and constant
`(tail seminorm) + εTail`.

This is the single-multiplier brick: the local data for the positive
non-Archimedean theorem is the finite sum of these bricks over the
multipliers. -/
private theorem exists_souzaPositiveTailProduct_single_s_atom_geometric
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    {t : ℕ} {m : α → ℂ}
    (hfin : souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top t m ≠ ∞)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (htk : t ≤ k)
    {εTail : ℝ} (hεTail : 0 < εTail) :
    ∃ hLp : Lp ℂ p G.toWeakGridSpace.measure,
    ∃ R : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top) hLp,
      WeakGridSpace.RepresentsFunction (G := G.toWeakGridSpace) (p := p)
        (fun z => m z * canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) z)
        hLp ∧
      SouzaPositiveRepresentation G s p hs hp hp_top R ∧
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
      (∀ j : ℕ, ∀ S : WeakGridSpace.LevelCell G.toWeakGridSpace j,
        (¬ S.1 ⊆ Q.1 → (R.block j).coeff S = 0) ∧
        (j < k → (R.block j).coeff S = 0)) ∧
      ∀ j : ℕ, k ≤ j →
        (R.levelCoeffPower j) ^ (1 / p.toReal) ≤
          ((souzaPositivePointwiseSelfsTailNorm G β p qtilde
              hβ hp hp_top t m).toReal + εTail) *
            (G.grid.lambda2 ^ (β - s)) ^ (j - k) := by
  classical
  let QG : GoodGridCell G := goodGridCellOfLevelCell G Q
  let Aβ := souzaAtomFamily G β p hβ hp hp_top
  let AS := souzaAtomFamily G s p hs hp hp_top
  let Wi := WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace QG.toLevelCell
  let normT : ℝ≥0∞ := souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top t m
  let D : ℝ := normT.toReal + εTail
  let μQ : ℝ := (G.grid.μ QG.cell).toReal
  let cscale : ℂ := ((μQ ^ (s - β) : ℝ) : ℂ)
  let lamRoot : ℝ := G.grid.lambda2 ^ (β - s)
  let lam : ℝ := lamRoot ^ p.toReal
  -- basic numeric facts
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hdelta_pos : 0 < β - s := sub_pos.mpr hβs
  have hlambda2_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  have hlambda2_nonneg : 0 ≤ G.grid.lambda2 := hlambda2_pos.le
  have hlamRoot_pos : 0 < lamRoot := Real.rpow_pos_of_pos hlambda2_pos (β - s)
  have hlamRoot_lt_one : lamRoot < 1 :=
    Real.rpow_lt_one hlambda2_pos.le G.grid.hlambda2_lt_one hdelta_pos
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlamRoot_pos p.toReal
  have hlam_lt : lam < 1 := Real.rpow_lt_one hlamRoot_pos.le hlamRoot_lt_one hp_pos
  have hμQ_pos : 0 < μQ :=
    ENNReal.toReal_pos (GoodGridCell.measure_pos QG).ne'
      (GoodGridCell.measure_ne_top QG)
  have hscale_nonneg : 0 ≤ μQ ^ (s - β) := Real.rpow_nonneg hμQ_pos.le _
  have hscaleβ_nonneg : 0 ≤ μQ ^ (β - s) := Real.rpow_nonneg hμQ_pos.le _
  have hD_nonneg : 0 ≤ D := add_nonneg ENNReal.toReal_nonneg hεTail.le
  have hnorm_c : ‖cscale‖ = μQ ^ (s - β) := by
    simp [cscale, Complex.norm_real, Real.norm_of_nonneg hscale_nonneg]
  have hmul_scale : μQ ^ (s - β) * μQ ^ (β - s) = 1 := by
    rw [← Real.rpow_add hμQ_pos,
      show s - β + (β - s) = (0 : ℝ) from by ring, Real.rpow_zero]
  have hε2 : (0 : ℝ≥0∞) < ENNReal.ofReal (εTail / 2) := by
    rw [ENNReal.ofReal_pos]
    linarith
  -- 1. extract a concrete positive tail bound below `normT + εTail/2`
  obtain ⟨C, hC, hClt⟩ :=
    exists_souzaPositivePointwiseSelfsTailBound_lt_norm_add
      G β p qtilde hβ hp hp_top t m hfin hε2
  -- 2. apply it to the cell `Q`
  obtain ⟨yβ, hyβ_rep, _hyβ_pos, hyβ_norm⟩ := hC QG htk
  have hyβnorm_lt :
      souzaPositiveNorm G β p qtilde hβ hp hp_top yβ
        < normT + ENNReal.ofReal (εTail / 2) :=
    lt_of_le_of_lt hyβ_norm hClt
  have hyβ_fin : souzaPositiveNorm G β p qtilde hβ hp hp_top yβ ≠ ∞ :=
    (hyβnorm_lt.trans_le le_top).ne
  -- 3. extract a positive representation with controlled cost
  obtain ⟨Rβ, hRβ_pos, hRβ_fin, hRβ_cost⟩ :=
    exists_souzaPositiveRepresentation_pqCostENNReal_lt
      G β p qtilde hβ hp hp_top yβ hyβ_fin hε2
  have hcostENN :
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := qtilde) Rβ
        ≤ ENNReal.ofReal D := by
    have hhalf :
        ENNReal.ofReal (εTail / 2) + ENNReal.ofReal (εTail / 2) =
          ENNReal.ofReal εTail := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      norm_num
    calc
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := qtilde) Rβ
          ≤ souzaPositiveNorm G β p qtilde hβ hp hp_top yβ +
              ENNReal.ofReal (εTail / 2) := hRβ_cost.le
      _ ≤ (normT + ENNReal.ofReal (εTail / 2)) + ENNReal.ofReal (εTail / 2) :=
            add_le_add hyβnorm_lt.le le_rfl
      _ = normT + ENNReal.ofReal εTail := by rw [add_assoc, hhalf]
      _ = ENNReal.ofReal D := by
            rw [← ENNReal.ofReal_toReal (show normT ≠ ∞ from hfin),
              ← ENNReal.ofReal_add ENNReal.toReal_nonneg hεTail.le]
  have hRβ_cost_real :
      WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rβ ≤ D :=
    pqCost_le_of_pqCostENNReal_le Rβ hcostENN hD_nonneg
  -- 4. the represented function vanishes outside `Q`
  have hsupp : ∀ᵐ x ∂ G.toWeakGridSpace.measure, x ∉ QG.cell →
      ((yβ : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) x = 0 := by
    filter_upwards [hyβ_rep] with x hx hxQ
    rw [hx]
    simp [canonicalSouzaAtom, hxQ]
  have houtside : ∀ n (P : WeakGridSpace.LevelCell G.toWeakGridSpace n),
      ¬ P.1 ⊆ QG.toLevelCell.1 → (Rβ.block n).coeff P = 0 := fun n P hP =>
    souzaPositiveRepresentation_coeff_eq_zero_of_not_subset_cell
      G β p qtilde hβ hp hp_top QG Rβ hRβ_pos hsupp P hP
  have hbefore : ∀ n, n < QG.level → (Rβ.block n).toLp Aβ = 0 := fun n hn =>
    souzaPositiveRepresentation_block_toLp_eq_zero_of_level_lt
      G β p qtilde hβ hp hp_top QG Rβ hRβ_pos hsupp hn
  -- 5. read the representation on the induced grid; positivity transfers
  let Rβi := WeakGridSpace.ambientSupportedRepresentationToInduced
    G.toWeakGridSpace QG.toLevelCell Aβ Rβ hbefore houtside
  obtain ⟨hRβi_coeff, hRβi_atom⟩ :=
    ambientSupportedRepresentationToInduced_souzaPositive
      G β p hβ hp hp_top QG Rβ hRβ_pos hbefore houtside
  have hRβi_fin :
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := qtilde) Rβi :=
    WeakGridSpace.ambientSupportedRepresentationToInduced_finitePQCost
      G.toWeakGridSpace QG.toLevelCell Aβ Rβ hbefore houtside hRβ_fin
  have hRβi_cost :
      WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rβi ≤ D :=
    (WeakGridSpace.ambientSupportedRepresentationToInduced_pqCost_le
      G.toWeakGridSpace QG.toLevelCell Aβ Rβ hbefore houtside hRβ_fin).trans
      hRβ_cost_real
  -- 6. convert the induced representation from smoothness β to smoothness s
  let Rsi := inducedSouzaBetaRepresentationToSouzaS G s β p hs hβ
    (inferInstance : Fact (1 ≤ p)) hp_top QG Rβi
  have hRsi_root : ∀ n : ℕ,
      (Rsi.levelCoeffPower n) ^ (1 / p.toReal) ≤ (μQ ^ (β - s) * D) * lamRoot ^ n := by
    intro n
    have hroot₀ :
        (Rsi.levelCoeffPower n) ^ (1 / p.toReal) ≤
          WeakGridSpace.LpGridRepresentation.levelMeasureWeight Wi (β - s) p p n *
            WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rβi := by
      simpa [Rsi, Wi, inducedSouzaBetaRepresentationToSouzaS_levelCoeffPower] using
        besovToSouzaScaledCoeffPower_root_le
          G s β p qtilde hβ hβs hp_top QG Rβi hRβi_fin n
    have hweight :
        WeakGridSpace.LpGridRepresentation.levelMeasureWeight Wi (β - s) p p n
          ≤ μQ ^ (β - s) * lamRoot ^ n := by
      have h := induced_levelMeasureWeight_le_geometric G QG (β - s) p hdelta_pos n
      have hgeom : (G.grid.lambda2 ^ n : ℝ) ^ (β - s) = lamRoot ^ n := by
        calc
          (G.grid.lambda2 ^ n : ℝ) ^ (β - s) =
              G.grid.lambda2 ^ ((n : ℝ) * (β - s)) := by
                simpa [mul_comm] using
                  (Real.rpow_natCast_mul hlambda2_nonneg n (β - s)).symm
          _ = G.grid.lambda2 ^ ((β - s) * n) := by ring_nf
          _ = lamRoot ^ n := by
                simpa [lamRoot, mul_comm] using
                  Real.rpow_mul_natCast hlambda2_nonneg (β - s) n
      simpa [Wi, μQ, hgeom] using h
    have hcost_nonneg :
        0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rβi :=
      WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rβi
    have hgeom_nonneg : 0 ≤ μQ ^ (β - s) * lamRoot ^ n :=
      mul_nonneg hscaleβ_nonneg (pow_nonneg hlamRoot_pos.le n)
    calc
      (Rsi.levelCoeffPower n) ^ (1 / p.toReal)
          ≤ WeakGridSpace.LpGridRepresentation.levelMeasureWeight Wi (β - s) p p n *
              WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rβi := hroot₀
      _ ≤ (μQ ^ (β - s) * lamRoot ^ n) *
            WeakGridSpace.LpGridRepresentation.pqCost (q := qtilde) Rβi :=
          mul_le_mul_of_nonneg_right hweight hcost_nonneg
      _ ≤ (μQ ^ (β - s) * lamRoot ^ n) * D :=
          mul_le_mul_of_nonneg_left hRβi_cost hgeom_nonneg
      _ = (μQ ^ (β - s) * D) * lamRoot ^ n := by ring
  have hRsi_coeff : ∀ (n : ℕ) (P : WeakGridSpace.LevelCell Wi n),
      ∃ r : NNReal, (Rsi.block n).coeff P = (r : ℂ) := by
    intro n P
    obtain ⟨r, hr⟩ := hRβi_coeff n P
    exact inducedSouzaBetaBlockToSouzaS_coeff_nnreal G s β p hs hβ
      (inferInstance : Fact (1 ≤ p)) hp_top QG (Rβi.block n) P hr
  have hRsi_atom : ∀ (n : ℕ) (P : WeakGridSpace.LevelCell Wi n) (x : α),
      x ∈ P.1 →
      ∃ a : NNReal, 0 < a ∧
        (WeakGridSpace.inducedAtomFamily G.toWeakGridSpace QG.toLevelCell AS).toFunction
          (WeakGridSpace.levelCellToWeakGridCell Wi n P) ((Rsi.block n).atom P) x
          = (a : ℂ) := by
    intro n P x hx
    obtain ⟨a, ha, hval⟩ := hRβi_atom n P x hx
    exact inducedSouzaBetaBlockToSouzaS_atom_toFunction_pos G s β p hs hβ
      (inferInstance : Fact (1 ≤ p)) hp_top QG (Rβi.block n) P x hx ha hval
  -- 7. reindex to the ambient grid and rescale by `μ(Q)^(s-β)`
  let RA := WeakGridSpace.inducedRepresentationToAmbient
    G.toWeakGridSpace QG.toLevelCell AS Rsi
  let hLp : Lp ℂ p G.toWeakGridSpace.measure :=
    cscale • (yβ : Lp ℂ p G.toWeakGridSpace.measure)
  let Rscaled : WeakGridSpace.LpGridRepresentation AS hLp :=
    WeakGridSpace.LpGridRepresentation.smul (A := AS) cscale RA
  -- the represented function
  have hrep : WeakGridSpace.RepresentsFunction (G := G.toWeakGridSpace) (p := p)
      (fun z => m z * canonicalSouzaAtom G s p QG z) hLp := by
    have hrep0 : WeakGridSpace.RepresentsFunction (G := G.toWeakGridSpace) (p := p)
        (fun z => cscale * (m z * canonicalSouzaAtom G β p QG z)) hLp := by
      simpa [hLp] using
        WeakGridSpace.representsFunction_smul (G := G.toWeakGridSpace) (p := p)
          cscale hyβ_rep
    refine hrep0.trans ?_
    filter_upwards with z
    rw [canonicalSouzaAtom_eq_smul_beta G s β p QG z]
    ring
  -- coefficients of the rescaled representation are nonnegative reals
  have hRscaled_coeff : ∀ (j : ℕ) (S : WeakGridSpace.LevelCell G.toWeakGridSpace j),
      ∃ r : NNReal, (Rscaled.block j).coeff S = (r : ℂ) := by
    intro j S
    obtain ⟨r, hr⟩ := WeakGridSpace.inducedRepresentationToAmbient_coeff_nnreal
      G.toWeakGridSpace QG.toLevelCell AS Rsi hRsi_coeff j S
    refine ⟨⟨μQ ^ (s - β), hscale_nonneg⟩ * r, ?_⟩
    show cscale * (RA.block j).coeff S = _
    rw [hr, ← Complex.ofReal_mul]
    norm_cast
  -- atoms are pointwise positive wherever the coefficient does not vanish
  have hRscaled_atom : ∀ (j : ℕ) (S : WeakGridSpace.LevelCell G.toWeakGridSpace j),
      (Rscaled.block j).coeff S ≠ 0 → ∀ x ∈ S.1, ∃ a : NNReal, 0 < a ∧
        AS.toFunction (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace j S)
          ((Rscaled.block j).atom S) x = (a : ℂ) := by
    intro j S hne x hx
    have hRA_ne : (RA.block j).coeff S ≠ 0 := by
      intro h0
      apply hne
      show cscale * (RA.block j).coeff S = 0
      rw [h0, mul_zero]
    have hjk : QG.level ≤ j := by
      by_contra hlt
      exact hRA_ne (WeakGridSpace.inducedRepresentationToAmbient_coeff_lt
        G.toWeakGridSpace QG.toLevelCell AS Rsi (Nat.lt_of_not_ge hlt) S)
    have hSsub : S.1 ⊆ QG.toLevelCell.1 := by
      by_contra hnot
      exact hRA_ne (WeakGridSpace.inducedRepresentationToAmbient_coeff_eq_zero_of_not_subset
        G.toWeakGridSpace QG.toLevelCell AS Rsi S hnot)
    have hatomRA := WeakGridSpace.inducedRepresentationToAmbient_atom_toFunction_pos
      G.toWeakGridSpace QG.toLevelCell AS Rsi hRsi_atom hjk S hSsub x hx
    simpa [Rscaled, WeakGridSpace.LpGridRepresentation.smul,
      WeakGridSpace.LevelBlock.smul] using hatomRA
  -- 8. canonicalize: replace the junk atoms outside `Q` by canonical atoms
  obtain ⟨Rfin, hRfin_pos, hRfin_lcp, hRfin_reflect⟩ :=
    exists_souzaPositiveRepresentation_of_canonicalizable
      G s p hs hp hp_top Rscaled hRscaled_coeff hRscaled_atom
  -- support of the final representation
  have hRfin_support : ∀ (j : ℕ) (S : WeakGridSpace.LevelCell G.toWeakGridSpace j),
      (¬ S.1 ⊆ Q.1 → (Rfin.block j).coeff S = 0) ∧
      (j < k → (Rfin.block j).coeff S = 0) := by
    intro j S
    constructor
    · intro hS
      by_contra hne
      apply hRfin_reflect j S hne
      show cscale * (RA.block j).coeff S = 0
      rw [WeakGridSpace.inducedRepresentationToAmbient_coeff_eq_zero_of_not_subset
        G.toWeakGridSpace QG.toLevelCell AS Rsi S hS, mul_zero]
    · intro hj
      by_contra hne
      apply hRfin_reflect j S hne
      show cscale * (RA.block j).coeff S = 0
      rw [WeakGridSpace.inducedRepresentationToAmbient_coeff_lt
        G.toWeakGridSpace QG.toLevelCell AS Rsi hj S, mul_zero]
  -- decay of the final representation, in root form
  have hRfin_root : ∀ j : ℕ, k ≤ j →
      (Rfin.levelCoeffPower j) ^ (1 / p.toReal) ≤ D * lamRoot ^ (j - k) := by
    intro j hj
    have hsmul : Rscaled.levelCoeffPower j =
        ‖cscale‖ ^ p.toReal * RA.levelCoeffPower j :=
      lpGridRepresentation_smul_levelCoeffPower (A := AS) cscale RA j
    have hRA_eq : RA.levelCoeffPower j = Rsi.levelCoeffPower (j - k) := by
      have hjeq : j = k + (j - k) := by omega
      conv_lhs => rw [hjeq]
      exact WeakGridSpace.inducedRepresentationToAmbient_levelCoeffPower_add
        G.toWeakGridSpace QG.toLevelCell AS Rsi
    calc
      (Rfin.levelCoeffPower j) ^ (1 / p.toReal)
          ≤ (Rscaled.levelCoeffPower j) ^ (1 / p.toReal) :=
            Real.rpow_le_rpow (Rfin.levelCoeffPower_nonneg j) (hRfin_lcp j)
              (one_div_nonneg.mpr hp_pos.le)
      _ = (‖cscale‖ ^ p.toReal * RA.levelCoeffPower j) ^ (1 / p.toReal) := by
            rw [hsmul]
      _ = ‖cscale‖ * (RA.levelCoeffPower j) ^ (1 / p.toReal) := by
            rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _)
              (RA.levelCoeffPower_nonneg j),
              ← Real.rpow_mul (norm_nonneg _), mul_one_div, div_self hp_pos.ne',
              Real.rpow_one]
      _ = ‖cscale‖ * (Rsi.levelCoeffPower (j - k)) ^ (1 / p.toReal) := by
            rw [hRA_eq]
      _ ≤ ‖cscale‖ * ((μQ ^ (β - s) * D) * lamRoot ^ (j - k)) :=
            mul_le_mul_of_nonneg_left (hRsi_root (j - k)) (norm_nonneg _)
      _ = D * lamRoot ^ (j - k) := by
            rw [hnorm_c,
              show μQ ^ (s - β) * (μQ ^ (β - s) * D * lamRoot ^ (j - k)) =
                (μQ ^ (s - β) * μQ ^ (β - s)) * (D * lamRoot ^ (j - k)) from by ring,
              hmul_scale, one_mul]
  -- decay in power form on the full level range, for the finite cost
  have hRfin_decay_all : ∀ j : ℕ,
      Rfin.levelCoeffPower j ≤ (D ^ p.toReal * (lam ^ k)⁻¹) * lam ^ j := by
    intro j
    by_cases hj : k ≤ j
    · have hroot := hRfin_root j hj
      have hleft : ((Rfin.levelCoeffPower j) ^ (1 / p.toReal)) ^ p.toReal =
          Rfin.levelCoeffPower j := by
        rw [← Real.rpow_mul (Rfin.levelCoeffPower_nonneg j), one_div,
          inv_mul_cancel₀ hp_pos.ne', Real.rpow_one]
      have hpow := Real.rpow_le_rpow
        (Real.rpow_nonneg (Rfin.levelCoeffPower_nonneg j) _) hroot hp_pos.le
      rw [hleft] at hpow
      have hgeom : (D * lamRoot ^ (j - k)) ^ p.toReal =
          D ^ p.toReal * lam ^ (j - k) := by
        rw [Real.mul_rpow hD_nonneg (pow_nonneg hlamRoot_pos.le _)]
        congr 1
        calc
          (lamRoot ^ (j - k) : ℝ) ^ p.toReal =
              lamRoot ^ (((j - k : ℕ) : ℝ) * p.toReal) := by
                simpa [mul_comm] using
                  (Real.rpow_natCast_mul hlamRoot_pos.le (j - k) p.toReal).symm
          _ = lamRoot ^ (p.toReal * ((j - k : ℕ) : ℝ)) := by ring_nf
          _ = lam ^ (j - k) := by
                simpa [lam, mul_comm] using
                  Real.rpow_mul_natCast hlamRoot_pos.le p.toReal (j - k)
      rw [hgeom] at hpow
      refine hpow.trans (le_of_eq ?_)
      rw [pow_sub₀ lam hlam_pos.ne' hj]
      ring
    · push_neg at hj
      have hRA0 : RA.levelCoeffPower j = 0 :=
        WeakGridSpace.inducedRepresentationToAmbient_levelCoeffPower_lt
          G.toWeakGridSpace QG.toLevelCell AS Rsi hj
      have hzero : Rfin.levelCoeffPower j ≤ 0 := by
        calc
          Rfin.levelCoeffPower j ≤ Rscaled.levelCoeffPower j := hRfin_lcp j
          _ = ‖cscale‖ ^ p.toReal * RA.levelCoeffPower j :=
              lpGridRepresentation_smul_levelCoeffPower (A := AS) cscale RA j
          _ = 0 := by rw [hRA0, mul_zero]
      exact hzero.trans
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hD_nonneg _)
            (inv_nonneg.mpr (pow_nonneg hlam_pos.le k)))
          (pow_nonneg hlam_pos.le j))
  have hCfin_nonneg : 0 ≤ D ^ p.toReal * (lam ^ k)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hD_nonneg _)
      (inv_nonneg.mpr (pow_nonneg hlam_pos.le k))
  have hRfin_finq : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rfin :=
    finitePQCost_of_levelCoeffPower_geometric_decay Rfin
      (D ^ p.toReal * (lam ^ k)⁻¹) lam hCfin_nonneg hlam_pos hlam_lt hRfin_decay_all
  exact ⟨hLp, Rfin, hrep, hRfin_pos, hRfin_finq, hRfin_support, hRfin_root⟩

/--
Local transmutation datum for a source Souza atom of smoothness `s`.

The proof first rescales the source atom to a Souza atom of smoothness `β`,
uses the β-tail bound and the β-to-s conversion, and then rescales the resulting
representation back by `μ(Q)^(s-β)`.  The two powers of `μ(Q)` cancel in the
level coefficient estimate.
-/
private theorem exists_souzaTailProduct_full_sum_s_atom_geometric
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) {N : ℝ}
    (hTail : ∀ i ∈ Λ, ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top (t i) (g i) C)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    [DecidablePred fun i => goodGridLevelCellMeetsSupport G Q (g i)]
    (hA : nonArchimedeanRelevantTailSelfsSum
      G β p qtilde hβ hp hp_top Λ t g Q ≤ N)
    (hLevel : ∀ i, i ∈ Λ →
      goodGridLevelCellMeetsSupport G Q (g i) → t i ≤ k)
    {εTail εGeom : ℝ} (hεTail : 0 < εTail) (hεGeom : 0 < εGeom)
    (φs : ((souzaAtomFamily G s p hs hp hp_top).localSpace
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)).carrier)
    (hφs : φs ∈ (souzaAtomFamily G s p hs hp hp_top).atoms
      (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)) :
    ∃ hLp : Lp ℂ p G.toWeakGridSpace.measure,
    ∃ R : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top) hLp,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => ∑ i ∈ Λ,
          g i z *
            (souzaAtomFamily G s p hs hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φs z)
        hLp ∧
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R ∧
      (∀ j : ℕ, ∀ S : WeakGridSpace.LevelCell G.toWeakGridSpace j,
        (¬ S.1 ⊆ Q.1 → (R.block j).coeff S = 0) ∧
        (j < k → (R.block j).coeff S = 0)) ∧
      ∀ j : ℕ, k ≤ j →
        R.levelCoeffPower j ≤
          ((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
              (N + ((Λ.filter (fun i =>
                goodGridLevelCellMeetsSupport G Q (g i))).card : ℝ) * εTail) +
            εGeom) ^ p.toReal *
            ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) ^ (j - k) := by
  classical
  let QG : GoodGridCell G := goodGridCellOfLevelCell G Q
  let μQ : ℝ := (G.grid.μ Q.1).toReal
  let cscale : ℂ := (((μQ ^ (s - β) : ℝ) : ℂ))
  let Ktail : ℝ := 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1
  let Btail : ℝ :=
    N + ((Λ.filter (fun i => goodGridLevelCellMeetsSupport G Q (g i))).card : ℝ) *
      εTail
  let lam : ℝ := (G.grid.lambda2 ^ (β - s)) ^ p.toReal
  rcases exists_beta_souzaAtom_of_s_souzaAtom
      G s β p hs hβ hp hp_top Q φs hφs with
    ⟨φβ, hφβ, hφs_eq⟩
  rcases exists_souzaTailProduct_full_sum_induced_beta_norm_le_N_add
      G β p qtilde hβ hβ_lt_inv hp hp_top Λ t g hTail Q hA hLevel
      hεTail φβ hφβ with
    ⟨yβ, hyβ_rep, hyβ_norm⟩
  rcases inducedSouzaBetaBesov_to_ambientSouzaS_geometric
      G s β p q qtilde hs hβ hβs hp hp_top QG yβ hεGeom with
    ⟨Rβs, hRβs_fin, hRβs_support, hRβs_decay⟩
  let hLp : Lp ℂ p G.toWeakGridSpace.measure :=
    cscale •
      (WeakGridSpace.inducedLpToAmbient G.toWeakGridSpace QG.toLevelCell
        (yβ : Lp ℂ p
          (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace QG.toLevelCell).measure))
  let R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) hLp :=
    WeakGridSpace.LpGridRepresentation.smul (A := souzaAtomFamily G s p hs hp hp_top)
      cscale Rβs
  have hR_fin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R :=
    WeakGridSpace.LpGridRepresentation.smul_finitePQCost
      (A := souzaAtomFamily G s p hs hp hp_top) (q := q) cscale hRβs_fin
  have hrepβ_ambient :
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => ∑ i ∈ Λ,
          g i z *
            (souzaAtomFamily G β p hβ hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φβ z)
        (WeakGridSpace.inducedLpToAmbient G.toWeakGridSpace QG.toLevelCell
          (yβ : Lp ℂ p
            (WeakGridSpace.inducedWeakGridSpace G.toWeakGridSpace QG.toLevelCell).measure)) := by
    simpa [WeakGridSpace.inducedLpToAmbient, QG, goodGridCellOfLevelCell] using hyβ_rep
  have hrep_scaled :
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => cscale * ∑ i ∈ Λ,
          g i z *
            (souzaAtomFamily G β p hβ hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φβ z)
        hLp := by
    simpa [hLp] using
      WeakGridSpace.representsFunction_smul
        (G := G.toWeakGridSpace) (p := p) cscale hrepβ_ambient
  have hR_rep :
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => ∑ i ∈ Λ,
          g i z *
            (souzaAtomFamily G s p hs hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q) φs z)
        hLp := by
    refine hrep_scaled.trans ?_
    filter_upwards with z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [hφs_eq]
    ring
  refine ⟨hLp, R, hR_rep, hR_fin, ?_, ?_⟩
  · intro j S
    constructor
    · intro hS
      have hzero := (hRβs_support j S).1 hS
      simp [R, WeakGridSpace.LpGridRepresentation.smul, WeakGridSpace.LevelBlock.smul,
        hzero]
    · intro hj
      have hzero := (hRβs_support j S).2 hj
      simp [R, WeakGridSpace.LpGridRepresentation.smul, WeakGridSpace.LevelBlock.smul,
        hzero]
  · intro j hj
    have hQ_pos : 0 < G.grid.μ Q.1 :=
      G.grid.positive_measure k Q.1 Q.2
    have hQ_finite : G.grid.μ Q.1 ≠ ∞ := by
      letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ Q.1
    have hμ_pos : 0 < μQ := ENNReal.toReal_pos hQ_pos.ne' hQ_finite
    have hμ_nonneg : 0 ≤ μQ := hμ_pos.le
    have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
    have hnormβ_nonneg :
        0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq
          (inducedSouzaAtomFamily G β p hβ (inferInstance : Fact (1 ≤ p)) hp_top QG)
          qtilde yβ :=
      WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
        (A := inducedSouzaAtomFamily G β p hβ
          (inferInstance : Fact (1 ≤ p)) hp_top QG)
        (q := qtilde)
        (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations
          (inducedSouzaAtomFamily G β p hβ
            (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde) yβ
    have hnorm_add_nonneg :
        0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq
            (inducedSouzaAtomFamily G β p hβ
              (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom := by
      linarith
    have hnorm_le :
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (inducedSouzaAtomFamily G β p hβ
              (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom
          ≤ Ktail * Btail + εGeom := by
      have hbase :
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (inducedSouzaAtomFamily G β p hβ
                (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ
            ≤ Ktail * Btail := by
        simpa [Ktail, Btail, QG] using hyβ_norm
      linarith
    have hpow_norm_le :
        (WeakGridSpace.BesovishSpace.Norm_Costpq
            (inducedSouzaAtomFamily G β p hβ
              (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom) ^ p.toReal
          ≤ (Ktail * Btail + εGeom) ^ p.toReal :=
      Real.rpow_le_rpow hnorm_add_nonneg hnorm_le hp_pos.le
    have hscale_nonneg : 0 ≤ μQ ^ (s - β) :=
      Real.rpow_nonneg hμ_nonneg _
    have hscaleβ_nonneg : 0 ≤ μQ ^ (β - s) :=
      Real.rpow_nonneg hμ_nonneg _
    have hcancel :
        ‖cscale‖ ^ p.toReal *
            (μQ ^ (β - s) *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                (inducedSouzaAtomFamily G β p hβ
                  (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom)) ^
              p.toReal =
          (WeakGridSpace.BesovishSpace.Norm_Costpq
              (inducedSouzaAtomFamily G β p hβ
                (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom) ^
            p.toReal := by
      have hnorm_c : ‖cscale‖ = μQ ^ (s - β) := by
        simp [cscale, Complex.norm_real, Real.norm_of_nonneg hscale_nonneg]
      have hmul_scale :
          μQ ^ (s - β) * μQ ^ (β - s) = 1 := by
        calc
          μQ ^ (s - β) * μQ ^ (β - s)
              = μQ ^ ((s - β) + (β - s)) := by
                  rw [← Real.rpow_add hμ_pos]
          _ = μQ ^ (0 : ℝ) := by ring_nf
          _ = 1 := by rw [Real.rpow_zero]
      calc
        ‖cscale‖ ^ p.toReal *
            (μQ ^ (β - s) *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                (inducedSouzaAtomFamily G β p hβ
                  (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom)) ^
              p.toReal
            =
          (μQ ^ (s - β)) ^ p.toReal *
            (μQ ^ (β - s) *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                (inducedSouzaAtomFamily G β p hβ
                  (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom)) ^
              p.toReal := by rw [hnorm_c]
        _ =
          (μQ ^ (s - β) *
            (μQ ^ (β - s) *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                (inducedSouzaAtomFamily G β p hβ
                  (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom))) ^
              p.toReal := by
          rw [Real.mul_rpow hscale_nonneg
            (mul_nonneg hscaleβ_nonneg hnorm_add_nonneg)]
        _ =
          (WeakGridSpace.BesovishSpace.Norm_Costpq
              (inducedSouzaAtomFamily G β p hβ
                (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom) ^
            p.toReal := by
          rw [← mul_assoc, hmul_scale, one_mul]
    have hR_level :
        R.levelCoeffPower j =
          ‖cscale‖ ^ p.toReal * Rβs.levelCoeffPower j := by
      simpa [R] using lpGridRepresentation_smul_levelCoeffPower
        (A := souzaAtomFamily G s p hs hp hp_top) cscale Rβs j
    have hlam_nonneg : 0 ≤ lam ^ (j - k) := by
      dsimp [lam]
      have hlambda2_pos : 0 < G.grid.lambda2 :=
        lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
      exact pow_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hlambda2_pos.le _) _) _
    calc
      R.levelCoeffPower j
          = ‖cscale‖ ^ p.toReal * Rβs.levelCoeffPower j := hR_level
      _ ≤ ‖cscale‖ ^ p.toReal *
            ((((G.grid.μ QG.cell).toReal ^ (β - s) *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                (inducedSouzaAtomFamily G β p hβ
                  (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom)) ^
              p.toReal) *
            ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) ^ (j - QG.level)) := by
          exact mul_le_mul_of_nonneg_left (hRβs_decay j (by simpa [QG] using hj))
            (Real.rpow_nonneg (norm_nonneg cscale) _)
      _ =
          (‖cscale‖ ^ p.toReal *
            (((G.grid.μ QG.cell).toReal ^ (β - s) *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                (inducedSouzaAtomFamily G β p hβ
                  (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom)) ^
              p.toReal)) *
            ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) ^ (j - QG.level) := by
          ring
      _ =
          (WeakGridSpace.BesovishSpace.Norm_Costpq
              (inducedSouzaAtomFamily G β p hβ
                (inferInstance : Fact (1 ≤ p)) hp_top QG) qtilde yβ + εGeom) ^
            p.toReal *
            ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) ^ (j - k) := by
          simpa [QG, goodGridCellOfLevelCell, μQ] using
            congrArg
              (fun x => x *
                ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) ^ (j - k))
              hcancel
      _ ≤ (Ktail * Btail + εGeom) ^ p.toReal *
            ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) ^ (j - k) := by
          exact mul_le_mul_of_nonneg_right hpow_norm_le hlam_nonneg
      _ =
          ((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
              (N + ((Λ.filter (fun i =>
                goodGridLevelCellMeetsSupport G Q (g i))).card : ℝ) * εTail) +
            εGeom) ^ p.toReal *
            ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) ^ (j - k) := by
          rfl

/--
Package the local atom estimates into the data required by
`RepresentationWsubGandALS`.

Inactive source cells, whose source coefficient is zero, are assigned the zero
representation. Active cells use the local Souza-atom estimate above.
-/
private theorem nonArchimedean_id_almostLinear_bound :
    ∀ i : ℕ,
      ((fun i : ℕ => i) i : NNReal) ≤ (1 : ℝ) * (i : NNReal) + 0 ∧
      (1 : ℝ) * (i : NNReal) + 0 ≤ ((fun i : ℕ => i) i : NNReal) := by
  intro i
  constructor <;> norm_num

private theorem exists_nonArchimedeanLocalTransmutationData
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) {N : ℝ}
    (hN : 0 ≤ N)
    (hTail : ∀ i ∈ Λ, ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top (t i) (g i) C)
    {RsrcTarget : Lp ℂ p G.toWeakGridSpace.measure}
    (Rsrc : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      RsrcTarget)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (Rsrc.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantTailSelfsSum
          G β p qtilde hβ hp hp_top Λ t g Q ≤ N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (Rsrc.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k)
    {εTail εGeom : ℝ} (hεTail : 0 < εTail) (hεGeom : 0 < εGeom) :
    ∃ h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
        Lp ℂ p G.toWeakGridSpace.measure,
    ∃ Rt : (i : ℕ) → (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i) →
        WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top) (h i Q),
      WeakGridSpace.RepresentationWsubGandALS
        (p := p) (q := q) G.toWeakGridSpace G.toWeakGridSpace
        (souzaAtomFamily G s p hs hp hp_top) (fun i : ℕ => i)
        ⟨0, 0, 1, by norm_num, nonArchimedean_id_almostLinear_bound⟩
        ((G.grid.lambda2 ^ (β - s)) ^ p.toReal)
        (by
          have hlambda2_pos : 0 < G.grid.lambda2 :=
            lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
          have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
            Real.rpow_pos_of_pos hlambda2_pos (β - s)
          exact Real.rpow_pos_of_pos hroot_pos p.toReal)
        (by
          have hp_pos : 0 < p.toReal :=
            ENNReal.toReal_pos
              (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
          have hdelta : 0 < β - s := sub_pos.mpr hβs
          have hlambda2_pos : 0 < G.grid.lambda2 :=
            lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
          have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
            Real.rpow_pos_of_pos hlambda2_pos (β - s)
          have hroot_lt : G.grid.lambda2 ^ (β - s) < 1 :=
            Real.rpow_lt_one hlambda2_pos.le G.grid.hlambda2_lt_one hdelta
          exact Real.rpow_lt_one hroot_pos.le hroot_lt hp_pos)
        (((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
            (N + (Λ.card : ℝ) * εTail) + εGeom) ^ p.toReal)
        (by
          have hK0 : 0 ≤ 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1 := by
            have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
            linarith
          have hBtail : 0 ≤ N + (Λ.card : ℝ) * εTail := by
            exact add_nonneg hN (mul_nonneg (by exact_mod_cast Nat.zero_le Λ.card) hεTail.le)
          have hbase :
              0 ≤ (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                  (N + (Λ.card : ℝ) * εTail) + εGeom := by
            exact add_nonneg (mul_nonneg hK0 hBtail) hεGeom.le
          exact Real.rpow_nonneg hbase _)
        h Rt ∧
      (∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        (Rsrc.block i).coeff Q ≠ 0 →
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => ∑ r ∈ Λ,
              g r z *
                (souzaAtomFamily G s p hs hp hp_top).toFunction
                  (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
                  ((Rsrc.block i).atom Q) z)
            (h i Q)) := by
  classical
  let AS := souzaAtomFamily G s p hs hp hp_top
  let lam : ℝ := (G.grid.lambda2 ^ (β - s)) ^ p.toReal
  let C : ℝ :=
    ((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
        (N + (Λ.card : ℝ) * εTail) + εGeom) ^ p.toReal
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hC_nonneg : 0 ≤ C := by
    have hK0 : 0 ≤ 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1 := by
      have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
      linarith
    have hBtail : 0 ≤ N + (Λ.card : ℝ) * εTail := by
      exact add_nonneg hN (mul_nonneg (by exact_mod_cast Nat.zero_le Λ.card) hεTail.le)
    have hbase :
        0 ≤ (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
            (N + (Λ.card : ℝ) * εTail) + εGeom := by
      exact add_nonneg (mul_nonneg hK0 hBtail) hεGeom.le
    exact Real.rpow_nonneg hbase _
  have existsLocal :
      ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        ∃ hLp : Lp ℂ p G.toWeakGridSpace.measure,
        ∃ Rloc : WeakGridSpace.LpGridRepresentation AS hLp,
          ((Rsrc.block i).coeff Q ≠ 0 →
            WeakGridSpace.RepresentsFunction
              (G := G.toWeakGridSpace) (p := p)
              (fun z => ∑ r ∈ Λ,
                g r z *
                  (souzaAtomFamily G s p hs hp hp_top).toFunction
                    (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
                    ((Rsrc.block i).atom Q) z)
              hLp) ∧
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rloc ∧
          (∀ j : ℕ, ∀ S : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            (¬ S.1 ⊆ Q.1 → (Rloc.block j).coeff S = 0) ∧
            (j < i → (Rloc.block j).coeff S = 0)) ∧
          ∀ j : ℕ, i ≤ j → Rloc.levelCoeffPower j ≤ C * lam ^ (j - i) := by
    intro i Q
    by_cases hcoeff : (Rsrc.block i).coeff Q = 0
    · refine ⟨0, WeakGridSpace.LpGridRepresentation.zero AS, ?_, ?_, ?_, ?_⟩
      · intro hne
        exact (hne hcoeff).elim
      · by_cases hqtop : q = ∞
        · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_pos hqtop]
          refine ⟨0, ?_⟩
          rintro x ⟨j, rfl⟩
          have hzero : (0 : ℝ) ^ (p.toReal)⁻¹ = 0 := by
            exact Real.zero_rpow (inv_ne_zero hp_pos.ne')
          simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower, hzero]
        · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hqtop]
          have hq_pos : 0 < q.toReal :=
            ENNReal.toReal_pos
              (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hqtop
          have hpow_ne : q.toReal / p.toReal ≠ 0 :=
            div_ne_zero hq_pos.ne' hp_pos.ne'
          simpa [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower,
            Real.zero_rpow hpow_ne] using (summable_zero : Summable fun _ : ℕ => (0 : ℝ))
      · intro j S
        constructor <;> intro _ <;>
          simp [WeakGridSpace.LpGridRepresentation.zero, WeakGridSpace.LevelBlock.zero]
      · intro j hj
        rw [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower]
        exact mul_nonneg hC_nonneg (pow_nonneg (by
          dsimp [lam]
          exact Real.rpow_nonneg (Real.rpow_nonneg (le_of_lt
            (lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2)) _) _) _)
    · rcases exists_souzaTailProduct_full_sum_s_atom_geometric
          G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
          Λ t g hTail Q (hA i Q hcoeff)
          (fun r hr hmeet => hB i Q r hr hcoeff hmeet)
          hεTail hεGeom ((Rsrc.block i).atom Q) ((Rsrc.block i).atom_mem Q) with
        ⟨hLp, Rloc, _hrep, hfin, hsupport, hdecay⟩
      refine ⟨hLp, Rloc, (fun _hne => _hrep), hfin, hsupport, ?_⟩
      intro j hj
      have hcard_le :
          (((Λ.filter (fun r => goodGridLevelCellMeetsSupport G Q (g r))).card : ℝ) ≤
            (Λ.card : ℝ)) := by
        exact_mod_cast
          (Finset.card_filter_le (s := Λ)
            (p := fun r => goodGridLevelCellMeetsSupport G Q (g r)))
      have htail_le :
          N + ((Λ.filter (fun r => goodGridLevelCellMeetsSupport G Q (g r))).card : ℝ) *
              εTail
            ≤ N + (Λ.card : ℝ) * εTail := by
        have hmul :=
          mul_le_mul_of_nonneg_right hcard_le hεTail.le
        linarith
      have hK_nonneg : 0 ≤ 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1 := by
        have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
        linarith
      have hlocal_base_nonneg :
          0 ≤ (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
              (N + ((Λ.filter (fun r =>
                goodGridLevelCellMeetsSupport G Q (g r))).card : ℝ) * εTail) +
            εGeom := by
        have htail_nonneg :
            0 ≤ N + ((Λ.filter (fun r =>
              goodGridLevelCellMeetsSupport G Q (g r))).card : ℝ) * εTail := by
          exact add_nonneg hN
            (mul_nonneg (by
              exact_mod_cast
                Nat.zero_le
                  ((Λ.filter (fun r => goodGridLevelCellMeetsSupport G Q (g r))).card))
              hεTail.le)
        exact add_nonneg (mul_nonneg hK_nonneg htail_nonneg) hεGeom.le
      have hlocal_base_le :
          (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
              (N + ((Λ.filter (fun r =>
                goodGridLevelCellMeetsSupport G Q (g r))).card : ℝ) * εTail) +
            εGeom
            ≤ (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                (N + (Λ.card : ℝ) * εTail) + εGeom := by
        have hmul := mul_le_mul_of_nonneg_left htail_le hK_nonneg
        linarith
      have hlocalC_le_C :
          ((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
              (N + ((Λ.filter (fun r =>
                goodGridLevelCellMeetsSupport G Q (g r))).card : ℝ) * εTail) +
            εGeom) ^ p.toReal ≤ C := by
        dsimp [C]
        exact Real.rpow_le_rpow hlocal_base_nonneg hlocal_base_le hp_pos.le
      have hlam_pow_nonneg : 0 ≤ lam ^ (j - i) := by
        exact pow_nonneg (by
          dsimp [lam]
          exact Real.rpow_nonneg (Real.rpow_nonneg (le_of_lt
            (lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2)) _) _) _
      exact le_trans (hdecay j hj)
        (mul_le_mul_of_nonneg_right hlocalC_le_C hlam_pow_nonneg)
  let h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
      Lp ℂ p G.toWeakGridSpace.measure :=
    fun i Q => Classical.choose (existsLocal i Q)
  let Rt : (i : ℕ) → (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i) →
      WeakGridSpace.LpGridRepresentation AS (h i Q) :=
    fun i Q => Classical.choose (Classical.choose_spec (existsLocal i Q))
  refine ⟨h, Rt, ?_, ?_⟩
  · intro i Q
    have hspec := Classical.choose_spec (Classical.choose_spec (existsLocal i Q))
    refine ⟨?_, hspec.2.2.1, hspec.2.2.2⟩
    simpa [WeakGridSpace.CoeffFinitePQCost,
      WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower, h, Rt] using hspec.2.1
  · intro i Q hcoeff
    have hspec := Classical.choose_spec (Classical.choose_spec (existsLocal i Q))
    exact hspec.1 hcoeff

/-- A block of a positive Souza representation satisfies the coefficient/atom
clause of `RepresentationWsubGandALS_pos`: the coefficient is a nonnegative
real and the (canonical) atom is strictly positive on its cell. -/
private theorem souzaPositiveRepresentation_block_pos_clause
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top) f}
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (j : ℕ) (S : WeakGridSpace.LevelCell G.toWeakGridSpace j) :
    ∃ r : NNReal, (R.block j).coeff S = (r : ℂ) ∧
      ∀ x, x ∈ S.1 →
        ∃ a : NNReal, 0 < a ∧
          (souzaAtomFamily G s p hs hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace j S)
            ((R.block j).atom S) x = (a : ℂ) := by
  obtain ⟨c, hc, hcoeff, hatom⟩ := hR j S
  refine ⟨⟨c, hc⟩, by rw [hcoeff]; norm_cast, ?_⟩
  intro x hx
  have hμ_pos : 0 < (G.grid.μ S.1).toReal := by
    have hfin : G.grid.μ S.1 ≠ ∞ := by
      letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
      exact MeasureTheory.measure_ne_top G.grid.μ S.1
    exact ENNReal.toReal_pos (G.grid.positive_measure j S.1 S.2).ne' hfin
  have hval_pos : 0 < (G.grid.μ S.1).toReal ^ (s - (p.toReal)⁻¹) :=
    Real.rpow_pos_of_pos hμ_pos _
  refine ⟨⟨(G.grid.μ S.1).toReal ^ (s - (p.toReal)⁻¹), hval_pos.le⟩, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa using hval_pos
  · have hcan : canonicalSouzaAtom G s p (goodGridCellOfLevelCell G S) x
        = (((G.grid.μ S.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ) := by
      simp [canonicalSouzaAtom, goodGridCellOfLevelCell, hx]
    rw [hatom, hcan]
    norm_cast

/-- **Positive local transmutation data.**

Positive-cone analogue of `exists_nonArchimedeanLocalTransmutationData`.  When the
source representation `Rsrc` is canonical and the multipliers `g i` are positive
Souza functions controlled by positive `selfs` tail bounds, the local product
representations of `(∑_{r∈Λ} g_r)·a_Q` can be chosen so that the assembled data
satisfies the **positive** transmutation hypothesis `RepresentationWsubGandALS_pos`
(nonnegative real coefficients and pointwise-positive atoms), with the same
geometric decay constant as in the non-positive version. -/
private theorem exists_nonArchimedeanLocalTransmutationData_pos
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) {N : ℝ}
    (hN : 0 ≤ N)
    (hgPos : ∀ i ∈ Λ, SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i))
    (hPosTail : ∀ i ∈ Λ, ∃ C : ℝ≥0∞,
      SouzaPositivePointwiseSelfsTailBound G β p qtilde hβ hp hp_top (t i) (g i) C)
    {RsrcTarget : Lp ℂ p G.toWeakGridSpace.measure}
    (Rsrc : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      RsrcTarget)
    (hRsrcCanon : SouzaCanonicalRepresentation G s p hs hp hp_top Rsrc)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (Rsrc.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantPositiveTailSelfsSum
          G β p qtilde hβ hp hp_top Λ t g Q ≤ ENNReal.ofReal N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (Rsrc.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k)
    {εTail εGeom : ℝ} (hεTail : 0 < εTail) (hεGeom : 0 < εGeom) :
    ∃ h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
        Lp ℂ p G.toWeakGridSpace.measure,
    ∃ Rt : (i : ℕ) → (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i) →
        WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top) (h i Q),
      WeakGridSpace.RepresentationWsubGandALS_pos
        (p := p) (q := q) G.toWeakGridSpace G.toWeakGridSpace
        (souzaAtomFamily G s p hs hp hp_top) (fun i : ℕ => i)
        ⟨0, 0, 1, by norm_num, nonArchimedean_id_almostLinear_bound⟩
        ((G.grid.lambda2 ^ (β - s)) ^ p.toReal)
        (by
          have hlambda2_pos : 0 < G.grid.lambda2 :=
            lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
          have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
            Real.rpow_pos_of_pos hlambda2_pos (β - s)
          exact Real.rpow_pos_of_pos hroot_pos p.toReal)
        (by
          have hp_pos : 0 < p.toReal :=
            ENNReal.toReal_pos
              (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
          have hdelta : 0 < β - s := sub_pos.mpr hβs
          have hlambda2_pos : 0 < G.grid.lambda2 :=
            lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
          have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
            Real.rpow_pos_of_pos hlambda2_pos (β - s)
          have hroot_lt : G.grid.lambda2 ^ (β - s) < 1 :=
            Real.rpow_lt_one hlambda2_pos.le G.grid.hlambda2_lt_one hdelta
          exact Real.rpow_lt_one hroot_pos.le hroot_lt hp_pos)
        (((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
            (N + (Λ.card : ℝ) * εTail) + εGeom) ^ p.toReal)
        (by
          have hK0 : 0 ≤ 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1 := by
            have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
            linarith
          have hBtail : 0 ≤ N + (Λ.card : ℝ) * εTail := by
            exact add_nonneg hN (mul_nonneg (by exact_mod_cast Nat.zero_le Λ.card) hεTail.le)
          have hbase :
              0 ≤ (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                  (N + (Λ.card : ℝ) * εTail) + εGeom := by
            exact add_nonneg (mul_nonneg hK0 hBtail) hεGeom.le
          exact Real.rpow_nonneg hbase _)
        h Rt ∧
      (∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        (Rsrc.block i).coeff Q ≠ 0 →
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => ∑ r ∈ Λ,
              g r z *
                (souzaAtomFamily G s p hs hp hp_top).toFunction
                  (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
                  ((Rsrc.block i).atom Q) z)
            (h i Q)) ∧
      -- Support witness (for consequence [ii]): a nonzero local block coefficient
      -- at a target cell `P` forces `P` into the support of some multiplier.
      (∀ (i : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i)
          (j : ℕ) (P : WeakGridSpace.LevelCell G.toWeakGridSpace j),
        ((Rt i Q).block j).coeff P ≠ 0 →
          ∃ r ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict P.1), g r z ≠ 0) := by
  classical
  let AS := souzaAtomFamily G s p hs hp hp_top
  let lamRoot : ℝ := G.grid.lambda2 ^ (β - s)
  let lam : ℝ := lamRoot ^ p.toReal
  let C : ℝ :=
    ((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
        (N + (Λ.card : ℝ) * εTail) + εGeom) ^ p.toReal
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hdelta_pos : 0 < β - s := sub_pos.mpr hβs
  have hlambda2_pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
  have hlamRoot_pos : 0 < lamRoot := Real.rpow_pos_of_pos hlambda2_pos _
  have hlamRoot_nonneg : 0 ≤ lamRoot := hlamRoot_pos.le
  have hlam_nonneg : 0 ≤ lam := (Real.rpow_pos_of_pos hlamRoot_pos _).le
  have hK0 : 0 ≤ souzaAmbientRestrictionMultiplierConstant G β p :=
    souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
  have hK_nonneg : 0 ≤ 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1 := by
    linarith
  have hBtail_nonneg : 0 ≤ N + (Λ.card : ℝ) * εTail :=
    add_nonneg hN (mul_nonneg (by exact_mod_cast Nat.zero_le Λ.card) hεTail.le)
  have hC_nonneg : 0 ≤ C :=
    Real.rpow_nonneg (add_nonneg (mul_nonneg hK_nonneg hBtail_nonneg) hεGeom.le) _
  have hbase_le : N + (Λ.card : ℝ) * εTail ≤
      (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
        (N + (Λ.card : ℝ) * εTail) + εGeom := by
    have hprod : 0 ≤ 2 * souzaAmbientRestrictionMultiplierConstant G β p *
        (N + (Λ.card : ℝ) * εTail) :=
      mul_nonneg (by linarith) hBtail_nonneg
    nlinarith
  have existsLocal :
      ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
        ∃ hLp : Lp ℂ p G.toWeakGridSpace.measure,
        ∃ Rloc : WeakGridSpace.LpGridRepresentation AS hLp,
          ((Rsrc.block i).coeff Q ≠ 0 →
            WeakGridSpace.RepresentsFunction
              (G := G.toWeakGridSpace) (p := p)
              (fun z => ∑ r ∈ Λ,
                g r z *
                  (souzaAtomFamily G s p hs hp hp_top).toFunction
                    (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
                    ((Rsrc.block i).atom Q) z)
              hLp) ∧
          SouzaPositiveRepresentation G s p hs hp hp_top Rloc ∧
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rloc ∧
          (∀ j : ℕ, ∀ S : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            (¬ S.1 ⊆ Q.1 → (Rloc.block j).coeff S = 0) ∧
            (j < i → (Rloc.block j).coeff S = 0)) ∧
          (∀ j : ℕ, i ≤ j → Rloc.levelCoeffPower j ≤ C * lam ^ (j - i)) ∧
          (∀ (j : ℕ) (P : WeakGridSpace.LevelCell G.toWeakGridSpace j),
            (Rloc.block j).coeff P ≠ 0 →
              ∃ r ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict P.1), g r z ≠ 0) := by
    intro i Q
    by_cases hcoeff : (Rsrc.block i).coeff Q = 0
    · -- Inactive source cell: the positive zero representation.
      refine ⟨0, souzaPositiveZeroRepresentation G s p hs hp hp_top, ?_,
        souzaPositiveZeroRepresentation_positive G s p hs hp hp_top,
        souzaPositiveZeroRepresentation_finitePQCost G s p q hs hp hp_top,
        ?_, ?_, ?_⟩
      · intro hne
        exact (hne hcoeff).elim
      · intro j S
        constructor <;> intro _ <;>
          exact souzaPositiveZeroRepresentation_coeff G s p hs hp hp_top j S
      · intro j hj
        rw [souzaPositiveZeroRepresentation_levelCoeffPower G s p hs hp hp_top j]
        exact mul_nonneg hC_nonneg (pow_nonneg hlam_nonneg _)
      · intro j P hne
        exact (hne (souzaPositiveZeroRepresentation_coeff G s p hs hp hp_top j P)).elim
    · -- Active source cell: sum the per-multiplier positive bricks.
      have hAQ := hA i Q hcoeff
      have hAQ' : (∑ r ∈ Λ, if goodGridLevelCellMeetsSupport G Q (g r) then
            souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top (t r) (g r)
          else 0) ≤ ENNReal.ofReal N := by
        simpa [nonArchimedeanRelevantPositiveTailSelfsSum] using hAQ
      have hfin_r : ∀ r ∈ Λ, goodGridLevelCellMeetsSupport G Q (g r) →
          souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top (t r) (g r)
            ≠ ∞ := by
        intro r hr hm
        have h := le_trans (Finset.single_le_sum
          (f := fun r' => if goodGridLevelCellMeetsSupport G Q (g r') then
            souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top (t r') (g r')
          else 0) (fun r' _ => zero_le) hr) hAQ'
        simp only [if_pos hm] at h
        exact (h.trans_lt ENNReal.ofReal_lt_top).ne
      let QG : GoodGridCell G := goodGridCellOfLevelCell G Q
      let D : ℕ → ℝ := fun r =>
        if r ∈ Λ ∧ goodGridLevelCellMeetsSupport G Q (g r) then
          (souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
            (t r) (g r)).toReal + εTail
        else 0
      have existsPer : ∀ r : ℕ,
          ∃ xr : Lp ℂ p G.toWeakGridSpace.measure,
          ∃ Rr : WeakGridSpace.LpGridRepresentation AS xr,
            (r ∈ Λ → WeakGridSpace.RepresentsFunction
              (G := G.toWeakGridSpace) (p := p)
              (fun z => g r z * canonicalSouzaAtom G s p QG z) xr) ∧
            SouzaPositiveRepresentation G s p hs hp hp_top Rr ∧
            WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rr ∧
            (∀ j : ℕ, ∀ S : WeakGridSpace.LevelCell G.toWeakGridSpace j,
              (¬ S.1 ⊆ Q.1 → (Rr.block j).coeff S = 0) ∧
              (j < i → (Rr.block j).coeff S = 0)) ∧
            (∀ j : ℕ, i ≤ j →
              (Rr.levelCoeffPower j) ^ (1 / p.toReal) ≤ D r * lamRoot ^ (j - i)) := by
        intro r
        by_cases hcase : r ∈ Λ ∧ goodGridLevelCellMeetsSupport G Q (g r)
        · obtain ⟨hrΛ, hmeets⟩ := hcase
          obtain ⟨xr, Rr, hrep, hpos, hfinq, hsupp, hdecay⟩ :=
            exists_souzaPositiveTailProduct_single_s_atom_geometric
              G s β p q qtilde hs hβ hβs hp hp_top
              (hfin_r r hrΛ hmeets) Q (hB i Q r hrΛ hcoeff hmeets) hεTail
          refine ⟨xr, Rr, fun _ => hrep, hpos, hfinq, hsupp, ?_⟩
          intro j hj
          rw [show D r = (souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
              (t r) (g r)).toReal + εTail from if_pos ⟨hrΛ, hmeets⟩]
          exact hdecay j hj
        · refine ⟨0, souzaPositiveZeroRepresentation G s p hs hp hp_top, ?_,
            souzaPositiveZeroRepresentation_positive G s p hs hp hp_top,
            souzaPositiveZeroRepresentation_finitePQCost G s p q hs hp hp_top,
            ?_, ?_⟩
          · intro hrΛ
            have hnm : ¬ goodGridLevelCellMeetsSupport G Q (g r) := fun hm =>
              hcase ⟨hrΛ, hm⟩
            have hzero : (fun z => g r z * canonicalSouzaAtom G s p QG z) =
                fun _ => (0 : ℂ) := by
              funext z
              by_cases hz : z ∈ Q.1
              · have hg0 : g r z = 0 := by
                  by_contra hgz
                  exact hnm ⟨z, hz, hgz⟩
                simp [hg0]
              · simp [canonicalSouzaAtom, QG, goodGridCellOfLevelCell, hz]
            rw [hzero]
            simpa [WeakGridSpace.RepresentsFunction] using
              (MeasureTheory.Lp.coeFn_zero ℂ p G.toWeakGridSpace.measure)
          · intro j S
            constructor <;> intro _ <;>
              exact souzaPositiveZeroRepresentation_coeff G s p hs hp hp_top j S
          · intro j hj
            rw [souzaPositiveZeroRepresentation_levelCoeffPower G s p hs hp hp_top j,
              Real.zero_rpow (one_div_pos.mpr hp_pos).ne',
              show D r = 0 from if_neg hcase, zero_mul]
      choose xs Rs hreps hposs hfinqs hsupps hdecays using existsPer
      obtain ⟨T, hTpos, hTfin, hTcoeff, hTroot⟩ :=
        exists_souzaPositiveRepresentation_finset_sum G s p q hs hp hp_top Λ xs Rs
          (fun r _ => hposs r) (fun r _ => hfinqs r)
      have hDsum : ∑ r ∈ Λ, D r ≤ N + (Λ.card : ℝ) * εTail := by
        have hD_le : ∀ r ∈ Λ, D r ≤
            (if goodGridLevelCellMeetsSupport G Q (g r) then
              souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
                (t r) (g r)
            else 0).toReal + εTail := by
          intro r hr
          by_cases hm : goodGridLevelCellMeetsSupport G Q (g r)
          · rw [show D r = _ + εTail from if_pos ⟨hr, hm⟩, if_pos hm]
          · rw [show D r = 0 from if_neg (fun hc => hm hc.2), if_neg hm]
            simpa using hεTail.le
        refine (Finset.sum_le_sum hD_le).trans ?_
        rw [Finset.sum_add_distrib]
        have hfinite : ∀ r ∈ Λ,
            (if goodGridLevelCellMeetsSupport G Q (g r) then
              souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
                (t r) (g r)
            else 0) ≠ ∞ := by
          intro r hr
          by_cases hm : goodGridLevelCellMeetsSupport G Q (g r)
          · rw [if_pos hm]
            exact hfin_r r hr hm
          · rw [if_neg hm]
            exact ENNReal.zero_ne_top
        have hsumT : ∑ r ∈ Λ,
            ((if goodGridLevelCellMeetsSupport G Q (g r) then
              souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
                (t r) (g r)
            else 0)).toReal ≤ N := by
          calc
            ∑ r ∈ Λ, ((if goodGridLevelCellMeetsSupport G Q (g r) then
                souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
                  (t r) (g r)
              else 0)).toReal
                = (∑ r ∈ Λ, if goodGridLevelCellMeetsSupport G Q (g r) then
                    souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
                      (t r) (g r)
                  else 0).toReal := (ENNReal.toReal_sum hfinite).symm
            _ ≤ (ENNReal.ofReal N).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hAQ'
            _ = N := ENNReal.toReal_ofReal hN
        have hcard : ∑ _r ∈ Λ, εTail = (Λ.card : ℝ) * εTail := by
          rw [Finset.sum_const, nsmul_eq_mul]
        linarith
      refine ⟨∑ r ∈ Λ, xs r, T, ?_, hTpos, hTfin, ?_, ?_, ?_⟩
      · -- the represented function
        intro _
        have hsum := WeakGridSpace.representsFunction_finset_sum
          (G := G.toWeakGridSpace) (p := p) Λ
          (fun r => fun z => g r z * canonicalSouzaAtom G s p QG z) xs
          (fun r hr => hreps r hr)
        refine hsum.trans ?_
        filter_upwards with z
        refine Finset.sum_congr rfl ?_
        intro r _
        rw [hRsrcCanon i Q]
      · -- support
        intro j S
        constructor
        · intro hS
          rw [hTcoeff j S]
          exact Finset.sum_eq_zero fun r _ => ((hsupps r) j S).1 hS
        · intro hj
          rw [hTcoeff j S]
          exact Finset.sum_eq_zero fun r _ => ((hsupps r) j S).2 hj
      · -- geometric decay
        intro j hj
        have hroot : (T.levelCoeffPower j) ^ (1 / p.toReal) ≤
            (N + (Λ.card : ℝ) * εTail) * lamRoot ^ (j - i) := by
          refine (hTroot j).trans ?_
          have hsum_le : ∑ r ∈ Λ, ((Rs r).levelCoeffPower j) ^ (1 / p.toReal)
              ≤ ∑ r ∈ Λ, D r * lamRoot ^ (j - i) :=
            Finset.sum_le_sum fun r _ => hdecays r j hj
          refine hsum_le.trans ?_
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right hDsum (pow_nonneg hlamRoot_nonneg _)
        have hleft : ((T.levelCoeffPower j) ^ (1 / p.toReal)) ^ p.toReal =
            T.levelCoeffPower j := by
          rw [← Real.rpow_mul (T.levelCoeffPower_nonneg j), one_div,
            inv_mul_cancel₀ hp_pos.ne', Real.rpow_one]
        have hgeom : ((N + (Λ.card : ℝ) * εTail) * lamRoot ^ (j - i)) ^ p.toReal
            = (N + (Λ.card : ℝ) * εTail) ^ p.toReal * lam ^ (j - i) := by
          rw [Real.mul_rpow hBtail_nonneg (pow_nonneg hlamRoot_nonneg _)]
          congr 1
          calc
            (lamRoot ^ (j - i) : ℝ) ^ p.toReal =
                lamRoot ^ (((j - i : ℕ) : ℝ) * p.toReal) := by
                  simpa [mul_comm] using
                    (Real.rpow_natCast_mul hlamRoot_nonneg (j - i) p.toReal).symm
            _ = lamRoot ^ (p.toReal * ((j - i : ℕ) : ℝ)) := by ring_nf
            _ = lam ^ (j - i) := by
                  simpa [lam, mul_comm] using
                    Real.rpow_mul_natCast hlamRoot_nonneg p.toReal (j - i)
        have hpow := Real.rpow_le_rpow
          (Real.rpow_nonneg (T.levelCoeffPower_nonneg j) _) hroot hp_pos.le
        rw [hleft, hgeom] at hpow
        refine hpow.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlam_nonneg _))
        exact Real.rpow_le_rpow hBtail_nonneg hbase_le hp_pos.le
      · -- support witness
        intro j P hne
        rw [hTcoeff j P] at hne
        obtain ⟨r, hrΛ, hr_ne⟩ : ∃ r ∈ Λ, ((Rs r).block j).coeff P ≠ 0 := by
          by_contra hall
          push_neg at hall
          exact hne (Finset.sum_eq_zero hall)
        refine ⟨r, hrΛ, ?_⟩
        have hae := souzaPositiveRepresentation_ae_ne_zero_on_active_cell
          G s p q hs hp hp_top (Rs r) (hposs r) P hr_ne
        filter_upwards [hae, MeasureTheory.ae_restrict_of_ae (hreps r hrΛ)]
          with z hz1 hz2 hgz
        exact hz1 (by rw [hz2, hgz, zero_mul])
  let h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
      Lp ℂ p G.toWeakGridSpace.measure :=
    fun i Q => Classical.choose (existsLocal i Q)
  let Rt : (i : ℕ) → (Q : WeakGridSpace.LevelCell G.toWeakGridSpace i) →
      WeakGridSpace.LpGridRepresentation AS (h i Q) :=
    fun i Q => Classical.choose (Classical.choose_spec (existsLocal i Q))
  refine ⟨h, Rt, ?_, ?_, ?_⟩
  · intro i Q
    have hspec := Classical.choose_spec (Classical.choose_spec (existsLocal i Q))
    obtain ⟨_, hpos, hfin, hsupp, hdecay, _⟩ := hspec
    refine ⟨?_, ?_, hdecay⟩
    · simpa [WeakGridSpace.CoeffFinitePQCost,
        WeakGridSpace.LpGridRepresentation.FinitePQCost,
        WeakGridSpace.LpGridRepresentation.levelCoeffPower, h, Rt] using hfin
    · intro j S
      obtain ⟨r, hr_coeff, hr_atom⟩ :=
        souzaPositiveRepresentation_block_pos_clause G s p hs hp hp_top hpos j S
      exact ⟨(hsupp j S).1, (hsupp j S).2, r, hr_coeff, hr_atom⟩
  · intro i Q hcoeff
    exact (Classical.choose_spec (Classical.choose_spec (existsLocal i Q))).1 hcoeff
  · intro i Q j P hne
    exact (Classical.choose_spec
      (Classical.choose_spec (existsLocal i Q))).2.2.2.2.2 j P hne

/--
The local product representatives produced for each source cell identify the
finite transmutation source sum with multiplication of the finite source
partial sum by the finite multiplier sum.
-/
private theorem nonArchimedean_partialSum_representsPointwiseProduct
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (Λ : Finset ℕ) (g : ℕ → α → ℂ)
    {RsrcTarget : Lp ℂ p G.toWeakGridSpace.measure}
    (Rsrc : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) RsrcTarget)
    (h : (i : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace i →
      Lp ℂ p G.toWeakGridSpace.measure)
    (hLocal : ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace i,
      (Rsrc.block i).coeff Q ≠ 0 →
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ r ∈ Λ,
            g r z *
              (souzaAtomFamily G s p hs hp hp_top).toFunction
                (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace i Q)
                ((Rsrc.block i).atom Q) z)
          (h i Q))
    (Ncut : ℕ) :
    WeakGridSpace.RepresentsPointwiseProduct
      (G := G.toWeakGridSpace) (p := p)
      (fun z => ∑ r ∈ Λ, g r z)
      (∑ i ∈ Finset.range Ncut,
        (Rsrc.block i).toLp (souzaAtomFamily G s p hs hp hp_top))
      (WeakGridSpace.PartialSumLevels G.toWeakGridSpace G.toWeakGridSpace h
        (fun i Q => (Rsrc.block i).coeff Q) Ncut) := by
  classical
  let Gi := G.toWeakGridSpace
  let AS := souzaAtomFamily G s p hs hp hp_top
  let m : α → ℂ := fun z => ∑ r ∈ Λ, g r z
  let c : (i : ℕ) → WeakGridSpace.LevelCell Gi i → ℂ :=
    fun i Q => (Rsrc.block i).coeff Q
  have hcell : ∀ i : ℕ, ∀ Q : WeakGridSpace.LevelCell Gi i,
      WeakGridSpace.RepresentsPointwiseProduct (G := Gi) (p := p) m
        (c i Q •
          WeakGridSpace.atomLp AS
            (WeakGridSpace.levelCellToWeakGridCell Gi i Q) ((Rsrc.block i).atom Q))
        (c i Q • h i Q) := by
    intro i Q
    by_cases hc : c i Q = 0
    · have hx :
          c i Q •
              WeakGridSpace.atomLp AS
                (WeakGridSpace.levelCellToWeakGridCell Gi i Q) ((Rsrc.block i).atom Q) =
            (0 : Lp ℂ p Gi.measure) := by
        simp [hc]
      have hy : c i Q • h i Q = (0 : Lp ℂ p Gi.measure) := by
        simp [hc]
      simpa [hx, hy] using
        WeakGridSpace.representsPointwiseProduct_zero (G := Gi) (p := p) m
    · have hatom :
          WeakGridSpace.RepresentsFunction (G := Gi) (p := p)
            (AS.toFunction (WeakGridSpace.levelCellToWeakGridCell Gi i Q)
              ((Rsrc.block i).atom Q))
            (WeakGridSpace.atomLp AS
              (WeakGridSpace.levelCellToWeakGridCell Gi i Q) ((Rsrc.block i).atom Q)) :=
        atomLp_representsFunction Gi AS
          (WeakGridSpace.levelCellToWeakGridCell Gi i Q) ((Rsrc.block i).atom Q)
      have hloc := hLocal i Q (by simpa [c] using hc)
      have hprod :
          WeakGridSpace.RepresentsPointwiseProduct (G := Gi) (p := p) m
            (WeakGridSpace.atomLp AS
              (WeakGridSpace.levelCellToWeakGridCell Gi i Q) ((Rsrc.block i).atom Q))
            (h i Q) := by
        filter_upwards [hloc, hatom] with z hhz haz
        calc
          ((h i Q : Lp ℂ p Gi.measure) : α → ℂ) z
              = ∑ r ∈ Λ,
                  g r z *
                    AS.toFunction (WeakGridSpace.levelCellToWeakGridCell Gi i Q)
                      ((Rsrc.block i).atom Q) z := hhz
          _ = (∑ r ∈ Λ, g r z) *
                AS.toFunction (WeakGridSpace.levelCellToWeakGridCell Gi i Q)
                  ((Rsrc.block i).atom Q) z := by
                rw [Finset.sum_mul]
          _ = m z *
                ((WeakGridSpace.atomLp AS
                  (WeakGridSpace.levelCellToWeakGridCell Gi i Q)
                  ((Rsrc.block i).atom Q) : Lp ℂ p Gi.measure) : α → ℂ) z := by
                rw [haz]
      exact hprod.smul (c i Q)
  have hlevel : ∀ i : ℕ,
      WeakGridSpace.RepresentsPointwiseProduct (G := Gi) (p := p) m
        ((Rsrc.block i).toLp AS)
        ((Gi.grid.partitions i).attach.sum fun Q => c i Q • h i Q) := by
    intro i
    simpa [WeakGridSpace.LevelBlock.toLp, WeakGridSpace.LevelBlock.term, AS, Gi, c] using
      representsPointwiseProduct_finset_sum Gi (Gi.grid.partitions i).attach m
        (fun Q => c i Q •
          WeakGridSpace.atomLp AS
            (WeakGridSpace.levelCellToWeakGridCell Gi i Q) ((Rsrc.block i).atom Q))
        (fun Q => c i Q • h i Q)
        (fun Q _hQ => hcell i Q)
  simpa [WeakGridSpace.PartialSumLevels, Gi, c] using
    representsPointwiseProduct_finset_sum Gi (Finset.range Ncut) m
      (fun i => (Rsrc.block i).toLp AS)
      (fun i => (Gi.grid.partitions i).attach.sum fun Q => c i Q • h i Q)
      (fun i _hi => hlevel i)

/--
Global non-Archimedean product representation with the explicit approximation
errors coming from the tail `sInf` and from choosing a near-optimal
β-to-s representation.

This is the fully assembled transmutation step before sending the two
approximation parameters to zero, or choosing them proportional to `N`.
-/
private theorem exists_nonArchimedeanProductRepresentation_with_errors
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) {N : ℝ}
    (hN : 0 ≤ N)
    (f : α → ℂ)
    {RsrcTarget : Lp ℂ p G.toWeakGridSpace.measure}
    (Rsrc : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      RsrcTarget)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rsrc)
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f RsrcTarget)
    (hTail : ∀ i ∈ Λ, ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (Rsrc.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantTailSelfsSum
          G β p qtilde hβ hp hp_top Λ t g Q ≤ N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (Rsrc.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k)
    {εTail εGeom : ℝ} (hεTail : 0 < εTail) (hεGeom : 0 < εGeom) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
    ∃ S : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        (y : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => (∑ i ∈ Λ, g i z) * f z)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
        (if q = ∞ then
          (G.toWeakGridSpace.grid.Cmult1 : ℝ) *
            ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                (N + (Λ.card : ℝ) * εTail) + εGeom) ^ p.toReal) ^
              (1 / p.toReal)) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ
                ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)
        else
          (G.toWeakGridSpace.grid.Cmult1 : ℝ) *
            ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                (N + (Λ.card : ℝ) * εTail) + εGeom) ^ p.toReal) ^
              (1 / p.toReal)) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ
                ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1) *
            (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
  classical
  let Gi := G.toWeakGridSpace
  let AS := souzaAtomFamily G s p hs hp hp_top
  let lam : ℝ := (G.grid.lambda2 ^ (β - s)) ^ p.toReal
  let C : ℝ :=
    ((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
        (N + (Λ.card : ℝ) * εTail) + εGeom) ^ p.toReal
  have hlam_pos : 0 < lam := by
    dsimp [lam]
    have hlambda2_pos : 0 < G.grid.lambda2 :=
      lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
    have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
      Real.rpow_pos_of_pos hlambda2_pos (β - s)
    exact Real.rpow_pos_of_pos hroot_pos p.toReal
  have hlam_lt : lam < 1 := by
    dsimp [lam]
    have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
    have hdelta : 0 < β - s := sub_pos.mpr hβs
    have hlambda2_pos : 0 < G.grid.lambda2 :=
      lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
    have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
      Real.rpow_pos_of_pos hlambda2_pos (β - s)
    have hroot_lt : G.grid.lambda2 ^ (β - s) < 1 :=
      Real.rpow_lt_one hlambda2_pos.le G.grid.hlambda2_lt_one hdelta
    exact Real.rpow_lt_one hroot_pos.le hroot_lt hp_pos
  have hC_nonneg : 0 ≤ C := by
    have hK0 : 0 ≤ 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1 := by
      have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
      linarith
    have hBtail : 0 ≤ N + (Λ.card : ℝ) * εTail := by
      exact add_nonneg hN (mul_nonneg (by exact_mod_cast Nat.zero_le Λ.card) hεTail.le)
    have hbase :
        0 ≤ (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
            (N + (Λ.card : ℝ) * εTail) + εGeom := by
      exact add_nonneg (mul_nonneg hK0 hBtail) hεGeom.le
    exact Real.rpow_nonneg hbase _
  rcases exists_nonArchimedeanLocalTransmutationData
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
      Λ t g hN hTail Rsrc hA hB hεTail hεGeom with
    ⟨h, Rt, hRt, hLocal⟩
  let c : (i : ℕ) → WeakGridSpace.LevelCell Gi i → ℂ :=
    fun i Q => (Rsrc.block i).coeff Q
  have hc : WeakGridSpace.CoeffFinitePQCost (p := p) (q := q) Gi c := by
    simpa [Gi, c, WeakGridSpace.CoeffFinitePQCost,
      WeakGridSpace.CoeffPLevel, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hRfin
  have hcost_eq :
      WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi c =
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
    simp [Gi, c, WeakGridSpace.CoeffPQCost, WeakGridSpace.CoeffPLevel,
      WeakGridSpace.LpGridRepresentation.pqCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower]
  have hsrc_tendsto :
      Filter.Tendsto
        (fun n => ∑ i ∈ Finset.range n, (Rsrc.block i).toLp AS)
        Filter.atTop (𝓝 RsrcTarget) := by
    simpa [AS] using Rsrc.hasSum.tendsto_sum_nat
  by_cases hqtop : q = ∞
  · subst q
    haveI : Fact ((1 : ℝ≥0∞) ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
    rcases WeakGridSpace.Transmutation_of_Atoms_Claim_A_top
        (G := Gi) (W := Gi) (AW := AS)
        (p := p) (u := ∞)
        (fun i : ℕ => i) 0 0 1 (by norm_num)
        nonArchimedean_id_almostLinear_bound
        lam hlam_pos hlam_lt C hC_nonneg h Rt hRt c hc
        (souza_assumptionG2 G s p ∞ hs hp hp_top)
        hp_top hs with
      ⟨gLim, hsum, hmem, hfin, htend, hcost⟩
    let S : WeakGridSpace.LpGridRepresentation AS gLim :=
      { block := WeakGridSpace.TransmutationBlockLimit Gi Gi AS h Rt c 0 1
        hasSum := hsum }
    let y : WeakGridSpace.BesovishSpace AS ∞ := ⟨gLim, ⟨S, hfin⟩⟩
    have hprod :
        WeakGridSpace.RepresentsPointwiseProduct
          (G := Gi) (p := p) (fun z => ∑ i ∈ Λ, g i z)
          RsrcTarget gLim := by
      exact WeakGridSpace.RepresentsPointwiseProduct.of_tendsto_Lp
        (G := Gi) (p := p)
        hsrc_tendsto htend
        (fun n =>
          nonArchimedean_partialSum_representsPointwiseProduct
            G s p hs hp hp_top Λ g Rsrc h hLocal n)
    have hrep :
        WeakGridSpace.RepresentsFunction
          (G := Gi) (p := p)
          (fun z => (∑ i ∈ Λ, g i z) * f z) gLim := by
      filter_upwards [hprod, hRep] with z hz hfz
      rw [hz, hfz]
    refine ⟨y, S, ?_, hfin, ?_⟩
    · simpa [y, Gi, AS] using hrep
    · calc
        WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) S
            ≤ (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                lam ^ (-(0 : ℝ) / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1) *
                WeakGridSpace.CoeffPQCost (p := p) (q := ∞) Gi c := by
              simpa [S] using hcost
        _ =
            (if (∞ : ℝ≥0∞) = ∞ then
              (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1)
            else
              (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1) *
                (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / (∞ : ℝ≥0∞).toReal)) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc := by
              simp [hcost_eq, C, lam, Gi]
  · rcases WeakGridSpace.Transmutation_of_Atoms_Claim_A
        (G := Gi) (W := Gi) (AW := AS)
        (p := p) (q := q) (u := ∞)
        (fun i : ℕ => i) 0 0 1 (by norm_num)
        nonArchimedean_id_almostLinear_bound
        lam hlam_pos hlam_lt C hC_nonneg h Rt hRt c hc hqtop
        (souza_assumptionG2 G s p q hs hp hp_top)
        hp_top hs with
      ⟨gLim, hsum, hmem, hfin, htend, hcost⟩
    let S : WeakGridSpace.LpGridRepresentation AS gLim :=
      { block := WeakGridSpace.TransmutationBlockLimit Gi Gi AS h Rt c 0 1
        hasSum := hsum }
    let y : WeakGridSpace.BesovishSpace AS q := ⟨gLim, ⟨S, hfin⟩⟩
    have hprod :
        WeakGridSpace.RepresentsPointwiseProduct
          (G := Gi) (p := p) (fun z => ∑ i ∈ Λ, g i z)
          RsrcTarget gLim := by
      exact WeakGridSpace.RepresentsPointwiseProduct.of_tendsto_Lp
        (G := Gi) (p := p)
        hsrc_tendsto htend
        (fun n =>
          nonArchimedean_partialSum_representsPointwiseProduct
            G s p hs hp hp_top Λ g Rsrc h hLocal n)
    have hrep :
        WeakGridSpace.RepresentsFunction
          (G := Gi) (p := p)
          (fun z => (∑ i ∈ Λ, g i z) * f z) gLim := by
      filter_upwards [hprod, hRep] with z hz hfz
      rw [hz, hfz]
    refine ⟨y, S, ?_, hfin, ?_⟩
    · simpa [y, Gi, AS] using hrep
    · calc
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S
            ≤ (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                lam ^ (-(0 : ℝ) / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1) *
                (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal) *
                WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi c := by
              simpa [S] using hcost
        _ =
            (if q = ∞ then
              (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1)
            else
              (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1) *
                (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
              simp [hqtop, hcost_eq, C, lam, Gi]

/-- Local copy of the nonnegativity of the integer coefficient kernel gauge. -/
private theorem cCoefficientInt_nonneg_local
    (t q : ℝ≥0∞) (b : ℤ → ℝ) (hb_nonneg : ∀ k, 0 ≤ b k) :
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

/--
Two Besov-ish vectors are equal when they represent the same concrete
function.  This is the quotient-space bookkeeping needed when we compare
near-optimal representations obtained with different approximation errors.
-/
private theorem souzaBesovish_eq_of_representsFunction
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {F : α → ℂ}
    {x y : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q}
    (hx : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) F
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hy : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) F
      (y : Lp ℂ p G.toWeakGridSpace.measure)) :
    x = y := by
  apply Subtype.ext
  apply Lp.ext
  exact hx.trans hy.symm

/-- The zero Souza representation has finite `(p,q)` cost. -/
private theorem souzaZeroRepresentation_finitePQCost
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
      (WeakGridSpace.LpGridRepresentation.zero
        (souzaAtomFamily G s p hs hp hp_top)) := by
  by_cases hqtop : q = ∞
  · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_pos hqtop]
    refine ⟨0, ?_⟩
    rintro x ⟨j, rfl⟩
    have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
    have hzero : (0 : ℝ) ^ (p.toReal)⁻¹ = 0 :=
      Real.zero_rpow (inv_ne_zero hp_pos.ne')
    simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower, hzero]
  · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hqtop]
    have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hqtop
    have hpow_ne : q.toReal / p.toReal ≠ 0 :=
      div_ne_zero hq_pos.ne' hp_pos.ne'
    simpa [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower,
      Real.zero_rpow hpow_ne] using (summable_zero : Summable fun _ : ℕ => (0 : ℝ))

/-- The zero Souza representation has zero `(p,q)` cost. -/
private theorem souzaZeroRepresentation_pqCost_eq_zero
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    WeakGridSpace.LpGridRepresentation.pqCost (q := q)
      (WeakGridSpace.LpGridRepresentation.zero
        (souzaAtomFamily G s p hs hp hp_top)) = 0 := by
  by_cases hqtop : q = ∞
  · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos hqtop]
    have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
    have hzero : (0 : ℝ) ^ (p.toReal)⁻¹ = 0 :=
      Real.zero_rpow (inv_ne_zero hp_pos.ne')
    simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower, hzero]
  · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hqtop]
    have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hqtop
    have hpow_ne : q.toReal / p.toReal ≠ 0 :=
      div_ne_zero hq_pos.ne' hp_pos.ne'
    have hqinv_ne : (q.toReal)⁻¹ ≠ 0 := inv_ne_zero hq_pos.ne'
    simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower,
      Real.zero_rpow hpow_ne, Real.zero_rpow hqinv_ne]

/--
Global non-Archimedean product representation for the nondegenerate case
`N > 0`, obtained from the error version by choosing the two approximation
parameters proportional to `N`.
-/
private theorem exists_nonArchimedeanProductRepresentation_of_pos
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) {N : ℝ}
    (hNpos : 0 < N)
    (f : α → ℂ)
    {RsrcTarget : Lp ℂ p G.toWeakGridSpace.measure}
    (Rsrc : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      RsrcTarget)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rsrc)
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f RsrcTarget)
    (hTail : ∀ i ∈ Λ, ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (Rsrc.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantTailSelfsSum
          G β p qtilde hβ hp hp_top Λ t g Q ≤ N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (Rsrc.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
    ∃ S : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        (y : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => (∑ i ∈ Λ, g i z) * f z)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
        ((G.toWeakGridSpace.grid.Cmult1 : ℝ) *
          (2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1) *
          WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
            (WeakGridSpace.transmutationKernelZ
              ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)) *
          N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
  classical
  let Gi := G.toWeakGridSpace
  let lam : ℝ := (G.grid.lambda2 ^ (β - s)) ^ p.toReal
  let Ktail : ℝ := 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1
  let epsTail : ℝ := N / ((Λ.card : ℝ) + 1)
  let epsGeom : ℝ := N
  have hden_pos : 0 < (Λ.card : ℝ) + 1 := by positivity
  have hεTail : 0 < epsTail := by
    exact div_pos hNpos hden_pos
  have hεGeom : 0 < epsGeom := hNpos
  rcases exists_nonArchimedeanProductRepresentation_with_errors
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
      Λ t g hNpos.le f Rsrc hRfin hRep hTail hA hB hεTail hεGeom with
    ⟨y, S, hSrep, hSfin, hScost⟩
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hKtail_nonneg : 0 ≤ Ktail := by
    have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
    dsimp [Ktail]
    linarith
  have hcard_eps_le :
      (Λ.card : ℝ) * epsTail ≤ N := by
    have hfrac_le_one : ((Λ.card : ℝ) / ((Λ.card : ℝ) + 1) : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hden_pos]
      linarith [show 0 ≤ (Λ.card : ℝ) by exact_mod_cast Nat.zero_le Λ.card]
    calc
      (Λ.card : ℝ) * epsTail
          = ((Λ.card : ℝ) / ((Λ.card : ℝ) + 1)) * N := by
              change (Λ.card : ℝ) * (N / ((Λ.card : ℝ) + 1)) =
                ((Λ.card : ℝ) / ((Λ.card : ℝ) + 1)) * N
              ring_nf
      _ ≤ 1 * N := mul_le_mul_of_nonneg_right hfrac_le_one hNpos.le
      _ = N := by ring
  have htail_le : N + (Λ.card : ℝ) * epsTail ≤ 2 * N := by
    linarith
  have hbase_nonneg :
      0 ≤ Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom := by
    exact add_nonneg
      (mul_nonneg hKtail_nonneg
        (add_nonneg hNpos.le
          (mul_nonneg (by exact_mod_cast Nat.zero_le Λ.card) hεTail.le)))
      hεGeom.le
  have hbase_le :
      Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom ≤
        (2 * Ktail + 1) * N := by
    have hmul := mul_le_mul_of_nonneg_left htail_le hKtail_nonneg
    calc
      Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom
          ≤ Ktail * (2 * N) + N := by
              exact add_le_add hmul le_rfl
      _ = (2 * Ktail + 1) * N := by ring
  have hroot_le :
      ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
          (1 / p.toReal) ≤
        (2 * Ktail + 1) * N := by
    have hroot_eq :
        ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
            (1 / p.toReal) =
          Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom := by
      have hmul : p.toReal * (1 / p.toReal) = 1 := by
        field_simp [hp_pos.ne']
      calc
        ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
            (1 / p.toReal)
            =
          (Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^
            (p.toReal * (1 / p.toReal)) := by
              rw [← Real.rpow_mul hbase_nonneg]
        _ = Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom := by
              rw [hmul, Real.rpow_one]
    rw [hroot_eq]
    exact hbase_le
  have hkernel_nonneg :
      ∀ n : ℤ, 0 ≤ WeakGridSpace.transmutationKernelZ lam 0 1 n := by
    intro n
    dsimp [WeakGridSpace.transmutationKernelZ]
    split_ifs
    · exact Real.rpow_nonneg (le_of_lt (by
        dsimp [lam]
        have hlambda2_pos : 0 < G.grid.lambda2 :=
          lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
        have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
          Real.rpow_pos_of_pos hlambda2_pos (β - s)
        exact Real.rpow_pos_of_pos hroot_pos p.toReal)) _
    · rfl
  have hcoef_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
        (WeakGridSpace.transmutationKernelZ lam 0 1) :=
    cCoefficientInt_nonneg_local p ∞ _ hkernel_nonneg
  have hfront_nonneg :
      0 ≤ (Gi.grid.Cmult1 : ℝ) *
        WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
          (WeakGridSpace.transmutationKernelZ lam 0 1) := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le Gi.grid.Cmult1) hcoef_nonneg
  have hpq_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc :=
    WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rsrc
  refine ⟨y, S, hSrep, hSfin, ?_⟩
  refine hScost.trans ?_
  by_cases hqtop : q = ∞
  · subst q
    have hfactor_le :
        (Gi.grid.Cmult1 : ℝ) *
            ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
              (1 / p.toReal) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1)
          ≤
        (Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N := by
      calc
        (Gi.grid.Cmult1 : ℝ) *
            ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
              (1 / p.toReal) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1)
            ≤
          (Gi.grid.Cmult1 : ℝ) * ((2 * Ktail + 1) * N) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hroot_le
                  (by exact_mod_cast Nat.zero_le Gi.grid.Cmult1))
                hcoef_nonneg
        _ =
          (Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N := by ring
    calc
      ((if (∞ : ℝ≥0∞) = ∞ then
          (Gi.grid.Cmult1 : ℝ) *
            ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
              (1 / p.toReal) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1)
        else
          (Gi.grid.Cmult1 : ℝ) *
              ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
                (1 / p.toReal) *
              WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                (WeakGridSpace.transmutationKernelZ lam 0 1) *
            (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / (∞ : ℝ≥0∞).toReal)) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc)
          ≤
        ((Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc := by
            simpa using mul_le_mul_of_nonneg_right hfactor_le hpq_nonneg
      _ =
        ((Gi.grid.Cmult1 : ℝ) *
          (2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1) *
          WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
            (WeakGridSpace.transmutationKernelZ
              ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)) *
          N * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc := by
            simp [Gi, Ktail, lam]
  · have hceil_one :
        (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal) = 1 := by
      norm_num
    have hfactor_le :
        (Gi.grid.Cmult1 : ℝ) *
              ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
                (1 / p.toReal) *
              WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                (WeakGridSpace.transmutationKernelZ lam 0 1) *
            (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)
          ≤
        (Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N := by
      calc
        (Gi.grid.Cmult1 : ℝ) *
              ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
                (1 / p.toReal) *
              WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                (WeakGridSpace.transmutationKernelZ lam 0 1) *
            (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)
            =
          (Gi.grid.Cmult1 : ℝ) *
              ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
                (1 / p.toReal) *
              WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                (WeakGridSpace.transmutationKernelZ lam 0 1) := by
              rw [hceil_one, mul_one]
        _ ≤
          (Gi.grid.Cmult1 : ℝ) * ((2 * Ktail + 1) * N) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hroot_le
                  (by exact_mod_cast Nat.zero_le Gi.grid.Cmult1))
                hcoef_nonneg
        _ =
          (Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N := by ring
    calc
      ((if q = ∞ then
          (Gi.grid.Cmult1 : ℝ) *
            ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
              (1 / p.toReal) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1)
        else
          (Gi.grid.Cmult1 : ℝ) *
              ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
                (1 / p.toReal) *
              WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                (WeakGridSpace.transmutationKernelZ lam 0 1) *
            (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc)
          ≤
        ((Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
            simpa [hqtop] using mul_le_mul_of_nonneg_right hfactor_le hpq_nonneg
      _ =
        ((Gi.grid.Cmult1 : ℝ) *
          (2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1) *
          WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
            (WeakGridSpace.transmutationKernelZ
              ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)) *
          N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
            simp [Gi, Ktail, lam]

/--
Degenerate non-Archimedean product representation for the case `N = 0`.

The proof uses the error version with arbitrarily small positive errors.  All
those representatives describe the same concrete product, so their Besov-ish
classes are equal.  Hence the `Norm_Costpq` of one fixed representative is
bounded by every positive number, and therefore vanishes; the embedding
criterion then identifies that representative with zero.
-/
private theorem exists_nonArchimedeanProductRepresentation_of_zero
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    (f : α → ℂ)
    {RsrcTarget : Lp ℂ p G.toWeakGridSpace.measure}
    (Rsrc : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      RsrcTarget)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rsrc)
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f RsrcTarget)
    (hTail : ∀ i ∈ Λ, ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (Rsrc.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantTailSelfsSum
          G β p qtilde hβ hp hp_top Λ t g Q ≤ 0)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (Rsrc.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
    ∃ S : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        (y : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => (∑ i ∈ Λ, g i z) * f z)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤ 0 := by
  classical
  let AS := souzaAtomFamily G s p hs hp hp_top
  let Gi := G.toWeakGridSpace
  let F : α → ℂ := fun z => (∑ i ∈ Λ, g i z) * f z
  rcases exists_nonArchimedeanProductRepresentation_with_errors
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
      Λ t g (le_refl (0 : ℝ)) f Rsrc hRfin hRep hTail hA hB
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) with
    ⟨y₀, S₀, hy₀_rep, _hS₀fin, _hS₀cost⟩
  have hfiniteA :
      WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations (A := AS) q :=
    WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations AS q
  let lam : ℝ := (G.grid.lambda2 ^ (β - s)) ^ p.toReal
  let Ktail : ℝ := 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hKtail_nonneg : 0 ≤ Ktail := by
    have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
    dsimp [Ktail]
    linarith
  have hkernel_nonneg :
      ∀ n : ℤ, 0 ≤ WeakGridSpace.transmutationKernelZ lam 0 1 n := by
    intro n
    dsimp [WeakGridSpace.transmutationKernelZ]
    split_ifs
    · exact Real.rpow_nonneg (le_of_lt (by
        dsimp [lam]
        have hlambda2_pos : 0 < G.grid.lambda2 :=
          lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
        have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
          Real.rpow_pos_of_pos hlambda2_pos (β - s)
        exact Real.rpow_pos_of_pos hroot_pos p.toReal)) _
    · rfl
  have hcoef_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
        (WeakGridSpace.transmutationKernelZ lam 0 1) :=
    cCoefficientInt_nonneg_local p ∞ _ hkernel_nonneg
  let D : ℝ :=
    (Gi.grid.Cmult1 : ℝ) *
      WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
        (WeakGridSpace.transmutationKernelZ lam 0 1) *
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc
  have hD_nonneg : 0 ≤ D := by
    exact mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le Gi.grid.Cmult1) hcoef_nonneg)
      (WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rsrc)
  have hnorm_le_zero :
      WeakGridSpace.BesovishSpace.Norm_Costpq AS q y₀ ≤ 0 := by
    refine le_iff_forall_pos_le_add.mpr ?_
    intro η hη
    let Aε : ℝ := Ktail * (Λ.card : ℝ) + 1
    have hAε_pos : 0 < Aε := by
      have hcard_nonneg : 0 ≤ (Λ.card : ℝ) := by exact_mod_cast Nat.zero_le Λ.card
      dsimp [Aε]
      nlinarith [mul_nonneg hKtail_nonneg hcard_nonneg]
    let ε : ℝ := (η / (D + 1)) / Aε
    have hε : 0 < ε := by
      exact div_pos (div_pos hη (by linarith)) hAε_pos
    rcases exists_nonArchimedeanProductRepresentation_with_errors
        G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
        Λ t g (le_refl (0 : ℝ)) f Rsrc hRfin hRep hTail hA hB
        hε hε with
      ⟨yε, Sε, hyε_rep, hSεfin, hSεcost⟩
    have hy_eq : y₀ = yε :=
      souzaBesovish_eq_of_representsFunction
        G s p q hs hp hp_top (F := F) hy₀_rep hyε_rep
    have hnorm_le_cost :
        WeakGridSpace.BesovishSpace.Norm_Costpq AS q y₀ ≤
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Sε := by
      rw [hy_eq]
      exact WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
        (A := AS) (q := q) yε Sε hSεfin
    let base : ℝ := Ktail * ((Λ.card : ℝ) * ε) + ε
    have hbase_nonneg : 0 ≤ base := by
      exact add_nonneg
        (mul_nonneg hKtail_nonneg
          (mul_nonneg (by exact_mod_cast Nat.zero_le Λ.card) hε.le))
        hε.le
    have hroot_eq : ((base ^ p.toReal) ^ (1 / p.toReal)) = base := by
      have hmul : p.toReal * (1 / p.toReal) = 1 := by
        field_simp [hp_pos.ne']
      calc
        (base ^ p.toReal) ^ (1 / p.toReal)
            = base ^ (p.toReal * (1 / p.toReal)) := by
                rw [← Real.rpow_mul hbase_nonneg]
        _ = base := by rw [hmul, Real.rpow_one]
    have hbase_le : base ≤ η / (D + 1) := by
      have hbase_eq : base = Aε * ε := by
        dsimp [base, Aε]
        ring
      rw [hbase_eq]
      calc
        Aε * ε = η / (D + 1) := by
          dsimp [ε]
          field_simp [hAε_pos.ne']
        _ ≤ η / (D + 1) := le_rfl
    have hDbase_le : D * base ≤ η := by
      calc
        D * base ≤ D * (η / (D + 1)) :=
          mul_le_mul_of_nonneg_left hbase_le hD_nonneg
        _ = (D / (D + 1)) * η := by ring
        _ ≤ 1 * η := by
          have hfrac : D / (D + 1) ≤ 1 := by
            rw [div_le_iff₀ (by linarith)]
            linarith
          exact mul_le_mul_of_nonneg_right hfrac hη.le
        _ = η := by ring
    have hSεcost_le : WeakGridSpace.LpGridRepresentation.pqCost (q := q) Sε ≤ η := by
      refine hSεcost.trans ?_
      by_cases hqtop : q = ∞
      · subst q
        have hroot_expr :
            ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
              (1 / p.toReal)) = base := by
          simpa [base, Ktail] using hroot_eq
        calc
          ((if (∞ : ℝ≥0∞) = ∞ then
              (Gi.grid.Cmult1 : ℝ) *
                ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                    ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
                  (1 / p.toReal)) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ
                    ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)
            else
              (Gi.grid.Cmult1 : ℝ) *
                ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                    ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
                  (1 / p.toReal)) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ
                    ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1) *
                (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / (∞ : ℝ≥0∞).toReal)) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc)
              =
            ((Gi.grid.Cmult1 : ℝ) * base *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1)) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc := by
                rw [hroot_expr]
                simp [lam, Gi]
          _ = D * base := by
                dsimp [D]
                ring
          _ ≤ η := hDbase_le
      ·
        have hroot_expr :
            ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
              (1 / p.toReal)) = base := by
          simpa [base, Ktail] using hroot_eq
        calc
          ((if q = ∞ then
              (Gi.grid.Cmult1 : ℝ) *
                ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                    ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
                  (1 / p.toReal)) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ
                    ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)
            else
              (Gi.grid.Cmult1 : ℝ) *
                ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                    ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
                  (1 / p.toReal)) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ
                    ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1) *
                (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc)
              =
            ((Gi.grid.Cmult1 : ℝ) * base *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1)) *
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
                rw [hroot_expr]
                simp [hqtop, lam, Gi]
          _ = D * base := by
                dsimp [D]
                ring
          _ ≤ η := hDbase_le
    calc
      WeakGridSpace.BesovishSpace.Norm_Costpq AS q y₀
          ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) Sε := hnorm_le_cost
      _ ≤ η := hSεcost_le
      _ = 0 + η := by ring
  have hnorm_zero :
      WeakGridSpace.BesovishSpace.Norm_Costpq AS q y₀ = 0 := by
    exact le_antisymm hnorm_le_zero
      (WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
        (A := AS) (q := q) hfiniteA y₀)
  have hy₀_zero : y₀ = 0 :=
    WeakGridSpace.BesovishSpace.eq_zero_of_Norm_Costpq_eq_zero
      (A := AS) (q := q) hp_top
      (souza_assumptionG2 G s p q hs hp hp_top).1 hfiniteA hnorm_zero
  let Szero : WeakGridSpace.LpGridRepresentation AS
      ((0 : WeakGridSpace.BesovishSpace AS q) : Lp ℂ p Gi.measure) :=
    WeakGridSpace.LpGridRepresentation.zero AS
  refine ⟨0, Szero, ?_, ?_, ?_⟩
  · simpa [F, AS, Gi, hy₀_zero] using hy₀_rep
  · simpa [Szero, AS] using
      souzaZeroRepresentation_finitePQCost G s p q hs hp hp_top
  · rw [souzaZeroRepresentation_pqCost_eq_zero G s p q hs hp hp_top]

/--
Non-Archimedean control for a finite sum of level-tail `selfs` multipliers.

Let `0 < s < β < 1 / p`.  There is a constant `Cgen` such that, whenever a finite family
`g i` has level-tail `selfs` control from levels `t i` onward, and a Souza
representation `R` of `f` satisfies the two separation hypotheses below, the
product `(∑ i in Λ, g i) * f` has a Souza representation whose coefficient
cost is bounded by `Cgen * N` times the coefficient cost of `R`, for
nonnegative `N`.

Hypothesis `hA` is the formal version of the paper's condition A: for each
active coefficient cell, the sum of the relevant tail `selfs` seminorms is at
most `N`.  Hypothesis `hB` is condition B: every relevant active cell lies at a
level where the corresponding multiplier is already in its allowed tail.
-/
theorem souzaNonArchimedeanPropertyLambdaFinite
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)] :
    ∃ Cgen : ℝ,
      0 ≤ Cgen ∧
      ∀ (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) (N : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
          0 ≤ N →
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) f
            (x : Lp ℂ p G.toWeakGridSpace.measure) →
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
          (∀ i ∈ Λ,
            ∃ C : ℝ,
              SouzaPointwiseSelfsTailBound
                G β p qtilde hβ hp hp_top (t i) (g i) C) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            (R.block k).coeff Q ≠ 0 →
              nonArchimedeanRelevantTailSelfsSum
                G β p qtilde hβ hp hp_top Λ t g Q ≤ N) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
            i ∈ Λ →
              (R.block k).coeff Q ≠ 0 →
                goodGridLevelCellMeetsSupport G Q (g i) →
                  t i ≤ k) →
          ∃ y : WeakGridSpace.BesovishSpace
              (souzaAtomFamily G s p hs hp hp_top) q,
            ∃ S : WeakGridSpace.LpGridRepresentation
                (souzaAtomFamily G s p hs hp hp_top)
                (y : Lp ℂ p G.toWeakGridSpace.measure),
              WeakGridSpace.RepresentsFunction
                (G := G.toWeakGridSpace) (p := p)
                (fun z => (∑ i ∈ Λ, g i z) * f z)
                (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
              WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
                Cgen * N *
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  classical
  let lam : ℝ := (G.grid.lambda2 ^ (β - s)) ^ p.toReal
  let Cgen : ℝ :=
    (G.toWeakGridSpace.grid.Cmult1 : ℝ) *
      (2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1) *
      WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
        (WeakGridSpace.transmutationKernelZ lam 0 1)
  refine ⟨Cgen, ?_, ?_⟩
  · have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
    have hmiddle : 0 ≤ 2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1 := by
      linarith
    have hkernel_nonneg :
        ∀ n : ℤ, 0 ≤ WeakGridSpace.transmutationKernelZ lam 0 1 n := by
      intro n
      dsimp [WeakGridSpace.transmutationKernelZ]
      split_ifs
      · exact Real.rpow_nonneg (le_of_lt (by
          dsimp [lam]
          have hlambda2_pos : 0 < G.grid.lambda2 :=
            lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
          have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
            Real.rpow_pos_of_pos hlambda2_pos (β - s)
          exact Real.rpow_pos_of_pos hroot_pos p.toReal)) _
      · rfl
    have hcoef_nonneg :
        0 ≤ WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
          (WeakGridSpace.transmutationKernelZ lam 0 1) :=
      cCoefficientInt_nonneg_local p ∞ _ hkernel_nonneg
    exact mul_nonneg
      (mul_nonneg
        (by exact_mod_cast Nat.zero_le G.toWeakGridSpace.grid.Cmult1)
        hmiddle)
      hcoef_nonneg
  · intro Λ t g N f x R hN hRep hRfin hTail hA hB
    by_cases hNzero : N = 0
    · subst N
      rcases exists_nonArchimedeanProductRepresentation_of_zero
          G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
          Λ t g f R hRfin hRep hTail hA hB with
        ⟨y, S, hSrep, hSfin, hScost⟩
      refine ⟨y, S, hSrep, hSfin, ?_⟩
      calc
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S
            ≤ 0 := hScost
        _ = Cgen * 0 * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
            ring
    · have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hNzero)
      rcases exists_nonArchimedeanProductRepresentation_of_pos
          G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
          Λ t g hNpos f R hRfin hRep hTail hA hB with
        ⟨y, S, hSrep, hSfin, hScost⟩
      refine ⟨y, S, hSrep, hSfin, ?_⟩
      simpa [Cgen, lam] using hScost

/-- The explicit coefficient-cost constant used by the finite representation step. -/
private noncomputable def nonArchimedeanRepresentationConstant
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞) : ℝ :=
  let lam : ℝ := (G.grid.lambda2 ^ (β - s)) ^ p.toReal
  (G.toWeakGridSpace.grid.Cmult1 : ℝ) *
    (2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1) *
    WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
      (WeakGridSpace.transmutationKernelZ lam 0 1)

private theorem nonArchimedeanRepresentationConstant_nonneg
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    0 ≤ nonArchimedeanRepresentationConstant G s β p := by
  let lam : ℝ := (G.grid.lambda2 ^ (β - s)) ^ p.toReal
  have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
  have hmiddle : 0 ≤ 2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1 := by
    linarith
  have hkernel_nonneg :
      ∀ n : ℤ, 0 ≤ WeakGridSpace.transmutationKernelZ lam 0 1 n := by
    intro n
    dsimp [WeakGridSpace.transmutationKernelZ]
    split_ifs
    · exact Real.rpow_nonneg (le_of_lt (by
        dsimp [lam]
        have hlambda2_pos : 0 < G.grid.lambda2 :=
          lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
        have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
          Real.rpow_pos_of_pos hlambda2_pos (β - s)
        exact Real.rpow_pos_of_pos hroot_pos p.toReal)) _
    · rfl
  have hcoef_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
        (WeakGridSpace.transmutationKernelZ lam 0 1) :=
    cCoefficientInt_nonneg_local p ∞ _ hkernel_nonneg
  exact mul_nonneg
    (mul_nonneg
      (by exact_mod_cast Nat.zero_le G.toWeakGridSpace.grid.Cmult1)
      hmiddle)
    hcoef_nonneg

private theorem exists_nonArchimedeanProductRepresentation_finset_with_cost_le
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    {Cgen N : ℝ} (hN : 0 ≤ N)
    (hCrep_le_Cgen : nonArchimedeanRepresentationConstant G s β p ≤ Cgen)
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    (f : α → ℂ)
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (hTail : ∀ i ∈ Λ, ∃ C : ℝ,
      SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantTailSelfsSum
          G β p qtilde hβ hp hp_top Λ t g Q ≤ N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
    ∃ S : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        (y : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => (∑ i ∈ Λ, g i z) * f z)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
        Cgen * N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  classical
  by_cases hNzero : N = 0
  · subst N
    rcases exists_nonArchimedeanProductRepresentation_of_zero
        G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
        Λ t g f R hRfin hRep hTail hA hB with
      ⟨y, S, hSrep, hSfin, hScost⟩
    refine ⟨y, S, hSrep, hSfin, ?_⟩
    calc
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤ 0 := hScost
      _ = Cgen * 0 * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by ring
  · have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hNzero)
    rcases exists_nonArchimedeanProductRepresentation_of_pos
        G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
        Λ t g hNpos f R hRfin hRep hTail hA hB with
      ⟨y, S, hSrep, hSfin, hScost⟩
    refine ⟨y, S, hSrep, hSfin, ?_⟩
    calc
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S
          ≤ nonArchimedeanRepresentationConstant G s β p *
              N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
            simpa [nonArchimedeanRepresentationConstant] using hScost
      _ ≤ Cgen * N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCrep_le_Cgen hN)
          (WeakGridSpace.LpGridRepresentation.pqCost_nonneg R)

/--
The initial finite part of a possibly infinite index set.

This is the index set used for the partial products
`(sum i <= n, g i) * f` in the infinite non-Archimedean statement.
-/
noncomputable def nonArchimedeanLambdaPartial (Λ : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter fun i => i ∈ Λ

/-- The strict initial segment `Λ ∩ {0, ..., n - 1}`. -/
noncomputable def nonArchimedeanLambdaInitial (Λ : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun i => i ∈ Λ

private theorem nonArchimedean_partialProducts_aestronglyMeasurable
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    {Λ : Set ℕ} {t : ℕ → ℕ} {g : ℕ → α → ℂ}
    {N : ℝ} {f : α → ℂ}
    {x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q}
    {R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (x : Lp ℂ p G.toWeakGridSpace.measure)}
    (hN : 0 ≤ N)
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (hTail : ∀ i ∈ Λ,
      ∃ C : ℝ,
        SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        ∃ T : ℝ,
          HasSum
            (fun i : {i // i ∈ Λ} =>
              nonArchimedeanRelevantTailSelfsInfiniteTerm
                G β p qtilde hβ hp hp_top Λ t g Q i)
            T ∧
          T ≤ N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun z => (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z)
        G.toWeakGridSpace.measure := by
  classical
  intro n
  let Λn : Finset ℕ := nonArchimedeanLambdaInitial Λ n
  rcases souzaNonArchimedeanPropertyLambdaFinite
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top with
    ⟨_Cfin, _hCfin_nonneg, hfinite⟩
  have hTail_fin : ∀ i ∈ Λn,
      ∃ C : ℝ,
        SouzaPointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C := by
    intro i hi
    exact hTail i ((Finset.mem_filter.mp hi).2)
  have hA_fin : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantTailSelfsSum
          G β p qtilde hβ hp hp_top Λn t g Q ≤ N := by
    intro k Q hQcoeff
    rcases hA k Q hQcoeff with ⟨T, hTsum, hTle⟩
    exact nonArchimedeanRelevantTailSelfsSum_le_of_hasSum
      G β p qtilde hβ hp hp_top hTail
      (fun i hi => (Finset.mem_filter.mp hi).2) hTsum hTle
  have hB_fin : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λn →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k := by
    intro k Q i hi hQcoeff hmeet
    exact hB k Q i ((Finset.mem_filter.mp hi).2) hQcoeff hmeet
  rcases hfinite Λn t g N f x R hN hRep hRfin hTail_fin hA_fin hB_fin with
    ⟨y, _Srep, hy_rep, _hSfin, _hy_cost⟩
  have hy_meas :
      AEStronglyMeasurable ((y : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ)
        G.toWeakGridSpace.measure :=
    (Lp.memLp (y : Lp ℂ p G.toWeakGridSpace.measure)).aestronglyMeasurable
  have hpartial_eq :
      ((y : Lp ℂ p G.toWeakGridSpace.measure) : α → ℂ) =ᵐ[G.toWeakGridSpace.measure]
        (fun z => (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z) := by
    simpa [Λn] using hy_rep
  exact hy_meas.congr hpartial_eq

theorem tendsto_nonArchimedean_partial_sums_of_hasSum
    {Λ : Set ℕ} (g : ℕ → α → ℂ) (f h : α → ℂ) {z : α}
    (hseries_z : HasSum
      (fun i : {i // i ∈ Λ} => g i.1 z * f z)
      (h z)) :
    Filter.Tendsto
      (fun n : ℕ => (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z)
      Filter.atTop (𝓝 (h z)) := by
  classical
  let fNat : ℕ → ℂ := fun i => if hi : i ∈ Λ then g i z * f z else 0
  have hzero_outside :
      ∀ i ∉ Set.range (fun j : {i // i ∈ Λ} => j.1), fNat i = 0 := by
    intro i hi
    by_cases hiΛ : i ∈ Λ
    · exact False.elim (hi ⟨⟨i, hiΛ⟩, rfl⟩)
    · simp [fNat, hiΛ]
  have hcomp :
      fNat ∘ (fun j : {i // i ∈ Λ} => j.1) =
        fun j : {i // i ∈ Λ} => g j.1 z * f z := by
    funext j
    simp [fNat, j.2]
  have hNat : HasSum fNat (h z) := by
    exact (Subtype.val_injective.hasSum_iff
      (f := fNat) (a := h z) hzero_outside).mp
      (by simpa [hcomp] using hseries_z)
  have htendsto := hNat.tendsto_sum_nat
  convert htendsto using 1
  ext n
  simp [nonArchimedeanLambdaInitial, fNat, Finset.sum_filter, Finset.sum_mul]

/--
Pointwise summability part of the infinite non-Archimedean statement.

Under the infinite version of conditions A and B, there is a uniform constant
`Cgen` such that, almost everywhere on the set where `f z ≠ 0`, the absolute
series `sum i in Λ, ‖g i z‖` is controlled by `Cgen * N`.  In particular the
complex series
`sum i in Λ, g i z * f z` has an almost everywhere pointwise sum.
-/
private theorem exists_nonArchimedeanInfinite_pointwise_hasSum
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)] :
    ∃ Cgen : ℝ,
      0 ≤ Cgen ∧
      1 ≤ Cgen ∧
      ∀ (Λ : Set ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) (N : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
          0 ≤ N →
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) f
            (x : Lp ℂ p G.toWeakGridSpace.measure) →
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
          (∀ i ∈ Λ,
            ∃ C : ℝ,
              SouzaPointwiseSelfsTailBound
                G β p qtilde hβ hp hp_top (t i) (g i) C) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            (R.block k).coeff Q ≠ 0 →
              ∃ T : ℝ,
                HasSum
                  (fun i : {i // i ∈ Λ} =>
                    nonArchimedeanRelevantTailSelfsInfiniteTerm
                      G β p qtilde hβ hp hp_top Λ t g Q i)
                  T ∧
                T ≤ N) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
            i ∈ Λ →
              (R.block k).coeff Q ≠ 0 →
                goodGridLevelCellMeetsSupport G Q (g i) →
                  t i ≤ k) →
          ∃ h : α → ℂ,
            ∃ absSum : α → ℝ,
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                f z ≠ 0 →
                  HasSum
                    (fun i : {i // i ∈ Λ} => ‖g i.1 z‖)
                    (absSum z) ∧
                  absSum z ≤ Cgen * N) ∧
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                HasSum
                  (fun i : {i // i ∈ Λ} => g i.1 z * f z)
                  (h z)) ∧
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                ‖h z‖ ≤ Cgen * N * ‖f z‖) ∧
              ∃ hmem : MemLp h p G.toWeakGridSpace.measure,
                ‖MemLp.toLp h hmem‖ ≤
                  Cgen * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖ := by
  classical
  let K : ℝ :=
    souzaBesovLpLocalEmbeddingConstant G β p qtilde *
      (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1)
  let Cgen : ℝ := max 1 K
  refine ⟨Cgen, ?_, ?_, ?_⟩
  · exact le_trans zero_le_one (le_max_left 1 K)
  · exact le_max_left 1 K
  · intro Λ t g N f x R hN hRep hRfin hTail hA hB
    let h : α → ℂ := fun z => ∑' i : {i // i ∈ Λ}, g i.1 z * f z
    let absSum : α → ℝ := fun z => ∑' i : {i // i ∈ Λ}, ‖g i.1 z‖
    have hK_nonneg : 0 ≤ K := by
      have hlocal := souzaBesovLpLocalEmbeddingConstant_nonneg G β p qtilde
      have hamb := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
      have hmiddle : 0 ≤ 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1 := by
        linarith
      exact mul_nonneg hlocal hmiddle
    have hK_le_Cgen : K ≤ Cgen := le_max_right 1 K
    have hbound_ae :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          ∀ i : {i // i ∈ Λ},
            ‖g i.1 z‖ ≤ K *
              souzaPointwiseSelfsTailNorm
                G β p qtilde hβ hp hp_top (t i.1) (g i.1) := by
      refine ae_all_iff.2 ?_
      intro i
      rcases hTail i.1 i.2 with ⟨C, hC⟩
      simpa [K] using
        souzaPointwiseSelfsTailNorm_norm_ae_le
          G β p qtilde hβ hp hp_top hβ_lt_inv
          (t := t i.1) (m := g i.1) ⟨C, hC⟩
    have hactive_ae :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          f z ≠ 0 →
            ∃ k, ∃ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              z ∈ Q.1 ∧ (R.block k).coeff Q ≠ 0 :=
      exists_active_cell_of_representsFunction_ne_zero_ae
        G s p q hs hp hp_top x R hRep
    have habs_ae :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          f z ≠ 0 →
            HasSum
              (fun i : {i // i ∈ Λ} => ‖g i.1 z‖)
              (absSum z) ∧
            absSum z ≤ Cgen * N := by
      filter_upwards [hbound_ae, hactive_ae] with z hbound_z hactive_z hfz
      rcases hactive_z hfz with ⟨k, Q, hzQ, hQcoeff⟩
      rcases hA k Q hQcoeff with ⟨T, hTsum, hTle⟩
      rcases hasSum_norm_of_mem_active
          G β p qtilde hβ hp hp_top hTail
          (Q := Q) (z := z) (K := K) (N := N) (T := T)
          hK_nonneg hzQ hbound_z hTsum hTle with
        ⟨hAbs, hAbs_le⟩
      refine ⟨by simpa [absSum] using hAbs, ?_⟩
      calc
        absSum z ≤ K * N := by simpa [absSum] using hAbs_le
        _ ≤ Cgen * N := mul_le_mul_of_nonneg_right hK_le_Cgen hN
    have hseries_ae :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          HasSum
            (fun i : {i // i ∈ Λ} => g i.1 z * f z)
            (h z) := by
      filter_upwards [habs_ae] with z habs_z
      by_cases hfz : f z = 0
      · simpa [h, hfz] using
          (hasSum_zero : HasSum (fun _ : {i // i ∈ Λ} => (0 : ℂ)) 0)
      · rcases habs_z hfz with ⟨hAbs, _hAbs_le⟩
        have hsummable_norm :
            Summable (fun i : {i // i ∈ Λ} => ‖g i.1 z‖) :=
          hAbs.summable
        have hsummable_g :
            Summable (fun i : {i // i ∈ Λ} => g i.1 z) :=
          hsummable_norm.of_norm
        exact (hsummable_g.mul_right (f z)).hasSum
    have hnorm_ae :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          ‖h z‖ ≤ Cgen * N * ‖f z‖ := by
      filter_upwards [habs_ae] with z habs_z
      by_cases hfz : f z = 0
      · have hzsum : h z = 0 := by simp [h, hfz]
        simp [hzsum, hfz]
      · rcases habs_z hfz with ⟨hAbs, hAbs_le⟩
        have hsummable_norm :
            Summable (fun i : {i // i ∈ Λ} => ‖g i.1 z‖) :=
          hAbs.summable
        have hsummable_prod_norm :
            Summable (fun i : {i // i ∈ Λ} => ‖g i.1 z * f z‖) := by
          simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using
            hsummable_norm.mul_right ‖f z‖
        have hnorm_le :
            ‖h z‖ ≤ ∑' i : {i // i ∈ Λ}, ‖g i.1 z * f z‖ := by
          simpa [h] using norm_tsum_le_tsum_norm hsummable_prod_norm
        have htsum_prod :
            (∑' i : {i // i ∈ Λ}, ‖g i.1 z * f z‖) =
              absSum z * ‖f z‖ := by
          simpa [absSum, norm_mul, mul_comm, mul_left_comm, mul_assoc] using
            (hsummable_norm.tsum_mul_right ‖f z‖)
        calc
          ‖h z‖ ≤ ∑' i : {i // i ∈ Λ}, ‖g i.1 z * f z‖ := hnorm_le
          _ = absSum z * ‖f z‖ := htsum_prod
          _ ≤ (Cgen * N) * ‖f z‖ :=
            mul_le_mul_of_nonneg_right hAbs_le (norm_nonneg _)
          _ = Cgen * N * ‖f z‖ := by ring
    have hpartial_meas :
        ∀ n : ℕ,
          AEStronglyMeasurable
            (fun z => (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z)
            G.toWeakGridSpace.measure :=
      nonArchimedean_partialProducts_aestronglyMeasurable
        G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
        hN hRep hRfin hTail hA hB
    have hpartial_tendsto :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          Filter.Tendsto
            (fun n : ℕ =>
              (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z)
            Filter.atTop (𝓝 (h z)) := by
      filter_upwards [hseries_ae] with z hseries_z
      exact tendsto_nonArchimedean_partial_sums_of_hasSum g f h hseries_z
    have hh_meas : AEStronglyMeasurable h G.toWeakGridSpace.measure :=
      aestronglyMeasurable_of_tendsto_ae Filter.atTop hpartial_meas hpartial_tendsto
    rcases memLp_and_norm_le_of_ae_norm_le_mul_representsFunction
        G p hRep hh_meas hnorm_ae with
      ⟨hmem, hmem_norm⟩
    exact ⟨h, absSum, habs_ae, hseries_ae, hnorm_ae, hmem, hmem_norm⟩



theorem mem_of_mem_nonArchimedeanLambdaInitial
    {Λ : Set ℕ} {n i : ℕ}
    (hi : i ∈ nonArchimedeanLambdaInitial Λ n) :
    i ∈ Λ := by
  classical
  have hi' : i ∈ Finset.range n ∧ i ∈ Λ := by
    simpa [nonArchimedeanLambdaInitial] using hi
  exact hi'.2

private theorem exists_nonArchimedean_finite_representation_initial
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    {Cgen N : ℝ} (hN : 0 ≤ N)
    (hCrep_le_Cgen : nonArchimedeanRepresentationConstant G s β p ≤ Cgen)
    (Λ : Set ℕ) (n : ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    (f : α → ℂ)
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (hTail : ∀ i ∈ Λ,
      ∃ C : ℝ,
        SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        ∃ T : ℝ,
          HasSum
            (fun i : {i // i ∈ Λ} =>
              nonArchimedeanRelevantTailSelfsInfiniteTerm
                G β p qtilde hβ hp hp_top Λ t g Q i)
            T ∧
          T ≤ N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z)
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          Cgen * N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  classical
  have hA_fin : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantTailSelfsSum
          G β p qtilde hβ hp hp_top (nonArchimedeanLambdaInitial Λ n) t g Q ≤ N := by
    intro k Q hQcoeff
    rcases hA k Q hQcoeff with ⟨T, hTsum, hTle⟩
    exact nonArchimedeanRelevantTailSelfsSum_le_of_hasSum
      G β p qtilde hβ hp hp_top hTail
      (fun i hi => mem_of_mem_nonArchimedeanLambdaInitial hi) hTsum hTle
  have hTail_fin : ∀ i, i ∈ nonArchimedeanLambdaInitial Λ n →
      ∃ C : ℝ,
        SouzaPointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C := by
    intro i hi
    exact hTail i (mem_of_mem_nonArchimedeanLambdaInitial hi)
  have hB_fin : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ nonArchimedeanLambdaInitial Λ n →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k := by
    intro k Q i hi hQcoeff hmeet
    exact hB k Q i (mem_of_mem_nonArchimedeanLambdaInitial hi) hQcoeff hmeet
  exact exists_nonArchimedeanProductRepresentation_finset_with_cost_le
    G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
    hN hCrep_le_Cgen (nonArchimedeanLambdaInitial Λ n) t g f x R hRep hRfin
    hTail_fin hA_fin hB_fin


theorem ae_eq_partialFun_on_composed_subseq
    {μ : Measure α} {p : ℝ≥0∞}
    {partialFun : ℕ → α → ℂ}
    {yseq : ℕ → Lp ℂ p μ}
    (hyseq_rep : ∀ n, yseq n =ᵐ[μ] partialFun n)
    (φ ψ : ℕ → ℕ) :
    ∀ᵐ z ∂μ, ∀ n : ℕ,
      yseq (φ (ψ n)) z = partialFun (φ (ψ n)) z := by
  have hsets :
      (⋂ n : ℕ, {z : α |
        yseq (φ (ψ n)) z = partialFun (φ (ψ n)) z}) ∈ ae μ := by
    exact countable_iInter_mem.mpr fun n => hyseq_rep (φ (ψ n))
  filter_upwards [hsets] with z hz n
  exact Set.mem_iInter.mp hz n

theorem representsFunction_of_tendsto_subseq
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    {h : α → ℂ} {yLimLp : Lp ℂ p G.toWeakGridSpace.measure}
    {partialFun : ℕ → α → ℂ}
    (φ ψ : ℕ → ℕ)
    (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hpartial_tendsto : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      Filter.Tendsto (fun n : ℕ => partialFun n z) Filter.atTop (𝓝 (h z)))
    (hy_subseq_tendsto : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      Filter.Tendsto (fun n : ℕ => partialFun (φ (ψ n)) z)
        Filter.atTop (𝓝 (yLimLp z))) :
    WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) h yLimLp := by
  let μ := G.toWeakGridSpace.measure
  let A : Set α :=
    {z : α | Filter.Tendsto (fun n : ℕ => partialFun n z) Filter.atTop (𝓝 (h z))}
  let B : Set α :=
    {z : α | Filter.Tendsto
      (fun n : ℕ => partialFun (φ (ψ n)) z) Filter.atTop (𝓝 (yLimLp z))}
  let D : Set α := A ∩ B
  have hA : A ∈ ae μ := by
    simpa [A, μ] using hpartial_tendsto
  have hB : B ∈ ae μ := by
    simpa [B, μ] using hy_subseq_tendsto
  have hD : D ∈ ae μ := by
    exact Filter.Eventually.and hA hB
  filter_upwards [hD] with z hz
  rcases hz with ⟨hzA, hzB⟩
  have hsub :
      Filter.Tendsto (fun n : ℕ => partialFun (φ (ψ n)) z)
        Filter.atTop (𝓝 (h z)) :=
    hzA.comp ((hφ.comp hψ).tendsto_atTop)
  exact tendsto_nhds_unique hzB hsub

theorem exists_subseq_tendsto_ae_of_tendsto_Lp
    {μ : Measure α} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : ℕ → Lp ℂ p μ} {uLim : Lp ℂ p μ}
    (hu_tendsto : Filter.Tendsto u Filter.atTop (𝓝 uLim)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ z ∂μ, Filter.Tendsto (fun n : ℕ => u (ψ n) z)
        Filter.atTop (𝓝 (uLim z)) := by
  have hu_measure :
      TendstoInMeasure μ
        (fun n z => u n z)
        Filter.atTop
        (fun z => uLim z) := by
    simpa only using
      (tendstoInMeasure_of_tendsto_Lp
        (μ := μ) (p := p) (f := u) (g := uLim)
        (l := Filter.atTop) hu_tendsto)

  simpa only using
    (TendstoInMeasure.exists_seq_tendsto_ae
      (μ := μ)
      (f := fun n z => u n z)
      (g := fun z => uLim z)
      hu_measure)



theorem exists_limit_representation_of_finite_sequence
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {Cbound : ℝ} (hCbound_nonneg : 0 ≤ Cbound)
    {h : α → ℂ} {partialFun : ℕ → α → ℂ}
    (yseq : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (Sseq : ∀ n, WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (yseq n : Lp ℂ p G.toWeakGridSpace.measure))
    (hyseq_rep : ∀ n,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (partialFun n)
        (yseq n : Lp ℂ p G.toWeakGridSpace.measure))
    (hSseq_fin : ∀ n,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (Sseq n))
    (hSseq_cost : ∀ n,
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) (Sseq n) ≤ Cbound)
    (hpartial_tendsto : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      Filter.Tendsto (fun n : ℕ => partialFun n z) Filter.atTop (𝓝 (h z))) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) h
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤ Cbound := by
  classical

  let A := souzaAtomFamily G s p hs hp hp_top
  let μ := G.toWeakGridSpace.measure
  let yseqLp : ℕ → Lp ℂ p μ := fun n => (yseq n : Lp ℂ p μ)

  rcases WeakGridSpace.exists_strongly_convergent_subseq_of_uniform_pqCost
      (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
      hp_top hs le_top A
      (souza_assumptionG2 G s p q hs hp hp_top)
      (souza_assumptionA5 G s p hs hp hp_top)
      Sseq hCbound_nonneg hSseq_fin hSseq_cost with
    ⟨φ, hφ, yLimLp, S, hmemLim, hSfin, hScost, hy_tendsto, _hcoeff_lim, _hatom_lim⟩

  have hy_tendsto_lp :
      Filter.Tendsto
        (fun n : ℕ => yseqLp (φ n))
        Filter.atTop
        (𝓝 yLimLp) := by
    change Filter.Tendsto
      (fun n : ℕ => (yseq (φ n) : Lp ℂ p G.toWeakGridSpace.measure))
      Filter.atTop
      (𝓝 yLimLp)
    exact hy_tendsto

  rcases exists_subseq_tendsto_ae_of_tendsto_Lp
      (μ := μ)
      (u := fun n : ℕ => yseqLp (φ n))
      (uLim := yLimLp)
      hy_tendsto_lp with
    ⟨ψ, hψ, hy_ae⟩

  have hyseq_rep_lp : ∀ n, yseqLp n =ᵐ[μ] partialFun n := by
    intro n
    change WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) (partialFun n)
      (yseq n : Lp ℂ p G.toWeakGridSpace.measure)
    exact hyseq_rep n

  have hcoe :
      ∀ᵐ z ∂μ, ∀ n : ℕ,
        yseqLp (φ (ψ n)) z = partialFun (φ (ψ n)) z :=
    ae_eq_partialFun_on_composed_subseq hyseq_rep_lp φ ψ

  have hy_subseq_tendsto :
      ∀ᵐ z ∂μ,
        Filter.Tendsto
          (fun n : ℕ => partialFun (φ (ψ n)) z)
          Filter.atTop
          (𝓝 (yLimLp z)) := by
    filter_upwards [hy_ae, hcoe] with z hyz hcoez
    exact hyz.congr' <|
      Filter.Eventually.of_forall fun n : ℕ => hcoez n

  have hy_subseq_tendsto_G :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        Filter.Tendsto
          (fun n : ℕ => partialFun (φ (ψ n)) z)
          Filter.atTop
          (𝓝 (yLimLp z)) := by
    change ∀ᵐ z ∂μ,
        Filter.Tendsto
          (fun n : ℕ => partialFun (φ (ψ n)) z)
          Filter.atTop
          (𝓝 (yLimLp z))
    exact hy_subseq_tendsto

  have hLimRep :
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) h yLimLp :=
    representsFunction_of_tendsto_subseq
      G p φ ψ hφ hψ hpartial_tendsto hy_subseq_tendsto_G

  refine ⟨⟨yLimLp, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact hmemLim

  · change WeakGridSpace.LpGridRepresentation A yLimLp
    exact S

  · change WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) h yLimLp
    exact hLimRep

  · change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S
    exact hSfin

  · change WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤ Cbound
    exact hScost

/--
Limit passage for uniformly bounded finite representations, preserving an
abstract coefficient-support property.

The support predicate `SupportProp k Q` can be any proposition attached to a
level cell.  It is inherited by the limit representation because coefficient
convergence implies that a nonzero limit coefficient is nonzero along some
finite approximant.
-/
theorem exists_limit_representation_of_finite_sequence_with_support
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {Cbound : ℝ} (hCbound_nonneg : 0 ≤ Cbound)
    {h : α → ℂ} {partialFun : ℕ → α → ℂ}
    (SupportProp : ∀ k, WeakGridSpace.LevelCell G.toWeakGridSpace k → Prop)
    (yseq : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (Sseq : ∀ n, WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (yseq n : Lp ℂ p G.toWeakGridSpace.measure))
    (hyseq_rep : ∀ n,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (partialFun n)
        (yseq n : Lp ℂ p G.toWeakGridSpace.measure))
    (hSseq_fin : ∀ n,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (Sseq n))
    (hSseq_cost : ∀ n,
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) (Sseq n) ≤ Cbound)
    (hSseq_supp : ∀ n k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ((Sseq n).block k).coeff Q ≠ 0 → SupportProp k Q)
    (hpartial_tendsto : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      Filter.Tendsto (fun n : ℕ => partialFun n z) Filter.atTop (𝓝 (h z))) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) h
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤ Cbound ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 → SupportProp k Q) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let μ := G.toWeakGridSpace.measure
  let yseqLp : ℕ → Lp ℂ p μ := fun n => (yseq n : Lp ℂ p μ)
  rcases WeakGridSpace.exists_strongly_convergent_subseq_of_uniform_pqCost
      (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
      hp_top hs le_top A
      (souza_assumptionG2 G s p q hs hp hp_top)
      (souza_assumptionA5 G s p hs hp hp_top)
      Sseq hCbound_nonneg hSseq_fin hSseq_cost with
    ⟨φ, hφ, yLimLp, S, hmemLim, hSfin, hScost, hy_tendsto, hcoeff_lim, _hatom_lim⟩
  have hy_tendsto_lp :
      Filter.Tendsto
        (fun n : ℕ => yseqLp (φ n))
        Filter.atTop
        (𝓝 yLimLp) := by
    change Filter.Tendsto
      (fun n : ℕ => (yseq (φ n) : Lp ℂ p G.toWeakGridSpace.measure))
      Filter.atTop
      (𝓝 yLimLp)
    exact hy_tendsto
  rcases exists_subseq_tendsto_ae_of_tendsto_Lp
      (μ := μ)
      (u := fun n : ℕ => yseqLp (φ n))
      (uLim := yLimLp)
      hy_tendsto_lp with
    ⟨ψ, hψ, hy_ae⟩
  have hyseq_rep_lp : ∀ n, yseqLp n =ᵐ[μ] partialFun n := by
    intro n
    change WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) (partialFun n)
      (yseq n : Lp ℂ p G.toWeakGridSpace.measure)
    exact hyseq_rep n
  have hcoe :
      ∀ᵐ z ∂μ, ∀ n : ℕ,
        yseqLp (φ (ψ n)) z = partialFun (φ (ψ n)) z :=
    ae_eq_partialFun_on_composed_subseq hyseq_rep_lp φ ψ
  have hy_subseq_tendsto :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        Filter.Tendsto
          (fun n : ℕ => partialFun (φ (ψ n)) z)
          Filter.atTop
          (𝓝 (yLimLp z)) := by
    filter_upwards [hy_ae, hcoe] with z hyz hcoez
    exact hyz.congr' <|
      Filter.Eventually.of_forall fun n : ℕ => hcoez n
  have hLimRep :
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) h yLimLp :=
    representsFunction_of_tendsto_subseq
      G p φ ψ hφ hψ hpartial_tendsto hy_subseq_tendsto
  have hsupp_lim : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (S.block k).coeff Q ≠ 0 → SupportProp k Q := by
    intro k Q hne
    have hex : ∃ n, ((Sseq (φ n)).block k).coeff Q ≠ 0 := by
      by_contra hall
      push_neg at hall
      have hzero :
          Filter.Tendsto (fun n => ((Sseq (φ n)).block k).coeff Q)
            Filter.atTop (𝓝 (0 : ℂ)) := by
        simpa [hall] using
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop (𝓝 (0 : ℂ)))
      exact hne (tendsto_nhds_unique (hcoeff_lim k Q) hzero)
    obtain ⟨n, hn⟩ := hex
    exact hSseq_supp (φ n) k Q hn
  exact ⟨⟨yLimLp, hmemLim⟩, S, hLimRep, hSfin, hScost, hsupp_lim⟩


private theorem exists_nonArchimedeanInfinite_besov_representation
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    {Cgen N : ℝ} (hN : 0 ≤ N)
    (hCgen_nonneg : 0 ≤ Cgen)
    (hCrep_le_Cgen : nonArchimedeanRepresentationConstant G s β p ≤ Cgen)
    (Λ : Set ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    (f h : α → ℂ)
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (hTail : ∀ i ∈ Λ,
      ∃ C : ℝ,
        SouzaPointwiseSelfsTailBound G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        ∃ T : ℝ,
          HasSum
            (fun i : {i // i ∈ Λ} =>
              nonArchimedeanRelevantTailSelfsInfiniteTerm
                G β p qtilde hβ hp hp_top Λ t g Q i)
            T ∧
          T ≤ N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k)
    (hseries : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      HasSum
        (fun i : {i // i ∈ Λ} => g i.1 z * f z)
        (h z)) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) h
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          Cgen * N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let μ := G.toWeakGridSpace.measure
  let partialFun : ℕ → α → ℂ := fun n z =>
    (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z
  have hfiniteRep : ∀ n,
      ∃ y : WeakGridSpace.BesovishSpace A q,
      ∃ S : WeakGridSpace.LpGridRepresentation A
          (y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) (partialFun n)
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          Cgen * N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
    intro n
    simpa [partialFun] using
      exists_nonArchimedean_finite_representation_initial
        G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
        hN hCrep_le_Cgen Λ n t g f x R hRep hRfin hTail hA hB
  let yseq : ℕ → WeakGridSpace.BesovishSpace A q := fun n => Classical.choose (hfiniteRep n)
  let Sseq : ∀ n, WeakGridSpace.LpGridRepresentation A
      (yseq n : Lp ℂ p G.toWeakGridSpace.measure) := fun n =>
    Classical.choose (Classical.choose_spec (hfiniteRep n))
  have hyseq_rep : ∀ n,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (partialFun n)
        (yseq n : Lp ℂ p G.toWeakGridSpace.measure) := by
    intro n
    exact (Classical.choose_spec (Classical.choose_spec (hfiniteRep n))).1
  have hSseq_fin : ∀ n,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (Sseq n) := by
    intro n
    exact (Classical.choose_spec (Classical.choose_spec (hfiniteRep n))).2.1
  have hSseq_cost : ∀ n,
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) (Sseq n) ≤
        Cgen * N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
    intro n
    exact (Classical.choose_spec (Classical.choose_spec (hfiniteRep n))).2.2
  have hCbound_nonneg :
      0 ≤ Cgen * N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
    exact mul_nonneg (mul_nonneg hCgen_nonneg hN)
      (WeakGridSpace.LpGridRepresentation.pqCost_nonneg R)
  have hpartial_tendsto :
      ∀ᵐ z ∂μ,
        Filter.Tendsto (fun n : ℕ => partialFun n z) Filter.atTop (𝓝 (h z)) := by
    filter_upwards [hseries] with z hseries_z
    exact tendsto_nonArchimedean_partial_sums_of_hasSum g f h hseries_z
  exact exists_limit_representation_of_finite_sequence
    G s p q hs hp hp_top hCbound_nonneg
    yseq Sseq hyseq_rep hSseq_fin hSseq_cost hpartial_tendsto

/--
Infinite-index non-Archimedean control.

For almost every point `z` with `f z ≠ 0`, the absolute series
`sum i in Λ, ‖g i z‖` is controlled by `Cgen * N`.  Hence the complex series
`sum i in Λ, g i z * f z` is pointwise well-defined almost everywhere; call its
sum `h z`.  The conclusion says that this limit function `h` is represented by
a Souza-Besov element and has a representation whose coefficient cost satisfies
the same type of bound as in the finite theorem.
-/
theorem souzaNonArchimedeanProperty
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)] :
    ∃ Cgen : ℝ,
      0 ≤ Cgen ∧
      1 ≤ Cgen ∧
      ∀ (Λ : Set ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) (N : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
          0 ≤ N →
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) f
            (x : Lp ℂ p G.toWeakGridSpace.measure) →
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
          (∀ i ∈ Λ,
            ∃ C : ℝ,
              SouzaPointwiseSelfsTailBound
                G β p qtilde hβ hp hp_top (t i) (g i) C) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            (R.block k).coeff Q ≠ 0 →
              ∃ T : ℝ,
                HasSum
                  (fun i : {i // i ∈ Λ} =>
                    nonArchimedeanRelevantTailSelfsInfiniteTerm
                      G β p qtilde hβ hp hp_top Λ t g Q i)
                  T ∧
                T ≤ N) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
            i ∈ Λ →
              (R.block k).coeff Q ≠ 0 →
                goodGridLevelCellMeetsSupport G Q (g i) →
                  t i ≤ k) →
          ∃ h : α → ℂ,
            ∃ absSum : α → ℝ,
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                f z ≠ 0 →
                  HasSum
                    (fun i : {i // i ∈ Λ} => ‖g i.1 z‖)
                    (absSum z) ∧
                  absSum z ≤ Cgen * N) ∧
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                HasSum
                  (fun i : {i // i ∈ Λ} => g i.1 z * f z)
                  (h z)) ∧
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                ‖h z‖ ≤ Cgen * N * ‖f z‖) ∧
              (∃ hmem : MemLp h p G.toWeakGridSpace.measure,
                ‖MemLp.toLp h hmem‖ ≤
                  Cgen * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖) ∧
              ∃ y : WeakGridSpace.BesovishSpace
                  (souzaAtomFamily G s p hs hp hp_top) q,
                ∃ S : WeakGridSpace.LpGridRepresentation
                    (souzaAtomFamily G s p hs hp hp_top)
                    (y : Lp ℂ p G.toWeakGridSpace.measure),
                  WeakGridSpace.RepresentsFunction
                    (G := G.toWeakGridSpace) (p := p) h
                    (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
                  WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
                    Cgen * N *
                      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := by
  classical
  rcases exists_nonArchimedeanInfinite_pointwise_hasSum
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top with
    ⟨Cpoint, hCpoint_nonneg, hCpoint_one_le, hpointwise⟩
  let Crep : ℝ := nonArchimedeanRepresentationConstant G s β p
  have hCrep_nonneg : 0 ≤ Crep :=
    nonArchimedeanRepresentationConstant_nonneg G s β p hp hp_top
  let Cgen : ℝ := max Cpoint Crep
  have hCpoint_le_Cgen : Cpoint ≤ Cgen := le_max_left _ _
  have hCrep_le_Cgen : Crep ≤ Cgen := le_max_right _ _
  have hCgen_nonneg : 0 ≤ Cgen := le_trans hCpoint_nonneg hCpoint_le_Cgen
  have hCgen_one_le : 1 ≤ Cgen := le_trans hCpoint_one_le hCpoint_le_Cgen
  refine ⟨Cgen, hCgen_nonneg, hCgen_one_le, ?_⟩
  intro Λ t g N f x R hN hRep hRfin hTail hA hB
  rcases hpointwise Λ t g N f x R hN hRep hRfin hTail hA hB with
    ⟨h, absSum, habs, hseries, hnorm, hmem⟩
  have habs' :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        f z ≠ 0 →
          HasSum
            (fun i : {i // i ∈ Λ} => ‖g i.1 z‖)
            (absSum z) ∧
          absSum z ≤ Cgen * N := by
    filter_upwards [habs] with z hz hfz
    rcases hz hfz with ⟨hsum, hle⟩
    exact ⟨hsum, hle.trans (mul_le_mul_of_nonneg_right hCpoint_le_Cgen hN)⟩
  have hnorm' :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        ‖h z‖ ≤ Cgen * N * ‖f z‖ := by
    filter_upwards [hnorm] with z hz
    calc
      ‖h z‖ ≤ Cpoint * N * ‖f z‖ := hz
      _ ≤ Cgen * N * ‖f z‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCpoint_le_Cgen hN) (norm_nonneg _)
  rcases hmem with ⟨hmemLp, hmemNorm⟩
  have hmem' :
      ∃ hmem : MemLp h p G.toWeakGridSpace.measure,
        ‖MemLp.toLp h hmem‖ ≤
          Cgen * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖ := by
    refine ⟨hmemLp, ?_⟩
    calc
      ‖MemLp.toLp h hmemLp‖ ≤
          Cpoint * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖ := hmemNorm
      _ ≤ Cgen * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCpoint_le_Cgen hN) (norm_nonneg _)
  refine ⟨h, absSum, habs', hseries, hnorm', hmem', ?_⟩
  exact exists_nonArchimedeanInfinite_besov_representation
    G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
    hN hCgen_nonneg hCrep_le_Cgen Λ t g f h x R
    hRep hRfin hTail hA hB hseries




/-!
## Infinite positive multiplier families: pointwise machinery

The infinite positive theorem mirrors the non-positive infinite theorem with
the real tail seminorms replaced by the positive tail seminorms (valued in
`ℝ≥0∞`).  The pointwise `L∞` control comes from the canonical-atom tail chain
in `MultipliersareBounded`, which only tests the multiplier against canonical
atoms and is therefore available from the positive tail bounds.
-/

/-- A finite positive tail bound restricts to a canonical-atom real tail bound
with constant `C.toReal`. -/
theorem SouzaPositivePointwiseSelfsTailBound.toCanonical
    {G : GoodGridSpace (α := α)} {s : ℝ} {p q : ℝ≥0∞}
    {hs : 0 < s} {hp : 1 ≤ p} {hp_top : p ≠ ∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {t : ℕ} {m : α → ℂ} {C : ℝ≥0∞} (hCne : C ≠ ∞)
    (hbound : SouzaPositivePointwiseSelfsTailBound G s p q hs hp hp_top t m C) :
    SouzaPointwiseCanonicalSelfsTailBound G s p q hs hp hp_top t m C.toReal := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  intro Q htQ
  rcases hbound Q htQ with ⟨y, hyrep, _hypos, hynorm⟩
  refine ⟨y, hyrep, ?_⟩
  have hle : ENNReal.ofReal (WeakGridSpace.BesovishSpace.Norm_Costpq
      (souzaAtomFamily G s p hs hp hp_top) q y) ≤ C :=
    (souzaBesovNorm_le_souzaPositiveNorm G s p q hs hp hp_top y).trans hynorm
  exact (ENNReal.ofReal_le_iff_le_toReal hCne).mp hle

/-- Tail `L∞` control by the positive tail seminorm: if the positive tail
seminorm of `m` at cutoff `t` is finite, then `‖m‖` is a.e. bounded by the
structural constant times its `toReal`.  Same constant as in the real case. -/
theorem souzaPositivePointwiseSelfsTailNorm_norm_ae_le
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hs_lt_inv : s < (p.toReal)⁻¹)
    {t : ℕ} {m : α → ℂ}
    (hfin : souzaPositivePointwiseSelfsTailNorm G s p q hs hp hp_top t m ≠ ∞) :
    ∀ᵐ x ∂G.grid.μ,
      ‖m x‖ ≤
        souzaBesovLpLocalEmbeddingConstant G s p q *
          (2 * souzaAmbientRestrictionMultiplierConstant G s p + 1) *
            (souzaPositivePointwiseSelfsTailNorm
              G s p q hs hp hp_top t m).toReal := by
  classical
  let K : ℝ :=
    souzaBesovLpLocalEmbeddingConstant G s p q *
      (2 * souzaAmbientRestrictionMultiplierConstant G s p + 1)
  let Ntail : ℝ :=
    (souzaPositivePointwiseSelfsTailNorm G s p q hs hp hp_top t m).toReal
  have hK_nonneg : 0 ≤ K := by
    have hlocal := souzaBesovLpLocalEmbeddingConstant_nonneg G s p q
    have hamb := souzaAmbientRestrictionMultiplierConstant_nonneg G s p hp hp_top
    exact mul_nonneg hlocal (by linarith)
  have hseq_bound :
      ∀ᵐ x ∂G.grid.μ,
        ∀ n : ℕ, ‖m x‖ ≤ K * (Ntail + (1 : ℝ) / (n + 1)) := by
    refine ae_all_iff.2 ?_
    intro n
    have hε : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hεE : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / (n + 1)) := by
      rw [ENNReal.ofReal_pos]
      exact hε
    obtain ⟨C, hC, hClt⟩ :=
      exists_souzaPositivePointwiseSelfsTailBound_lt_norm_add
        G s p q hs hp hp_top t m hfin hεE
    have hCne : C ≠ ∞ := by
      refine (hClt.trans ?_).ne
      exact ENNReal.add_lt_top.mpr ⟨hfin.lt_top, ENNReal.ofReal_lt_top⟩
    have hCtoReal_le : C.toReal ≤ Ntail + 1 / (n + 1) := by
      have hC_le : C ≤ ENNReal.ofReal (Ntail + 1 / (n + 1)) := by
        calc
          C ≤ souzaPositivePointwiseSelfsTailNorm G s p q hs hp hp_top t m +
              ENNReal.ofReal (1 / (n + 1)) := hClt.le
          _ = ENNReal.ofReal (Ntail + 1 / (n + 1)) := by
              rw [← ENNReal.ofReal_toReal hfin,
                ← ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le]
      calc
        C.toReal ≤ (ENNReal.ofReal (Ntail + 1 / (n + 1))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hC_le
        _ = Ntail + 1 / (n + 1) :=
          ENNReal.toReal_ofReal
            (add_nonneg ENNReal.toReal_nonneg hε.le)
    filter_upwards [souzaPointwiseSelfsTailBound_norm_ae_le
      G s p q hs hp hp_top hs_lt_inv (hC.toCanonical hCne)] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_left hCtoReal_le hK_nonneg)
  filter_upwards [hseq_bound] with x hx
  have htend :
      Filter.Tendsto (fun n : ℕ => K * (Ntail + (1 : ℝ) / (n + 1)))
        Filter.atTop (𝓝 (K * Ntail)) := by
    have hzero :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [mul_add] using (tendsto_const_nhds.mul (tendsto_const_nhds.add hzero))
  have hev :
      ∀ᶠ n : ℕ in Filter.atTop,
        ‖m x‖ ≤ K * (Ntail + (1 : ℝ) / ((n : ℝ) + 1)) :=
    Filter.Eventually.of_forall fun n => hx n
  simpa [K, Ntail] using ge_of_tendsto htend hev

/-- Positive analogue of `nonArchimedeanRelevantTailSelfsInfiniteTerm`: the
positive tail seminorm of `g i` if the support of `g i` meets `Q`, else `0`.
The value lives in `ℝ≥0∞`, so no summability witness is needed to state the
infinite condition A. -/
noncomputable def nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    (Λ : Set ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (i : {i // i ∈ Λ}) : ℝ≥0∞ := by
  classical
  exact
    if goodGridLevelCellMeetsSupport G Q (g i.1) then
      souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top (t i.1) (g i.1)
    else
      0

/-- Each term of the positive infinite tail sum is finite whenever the whole
sum is dominated by a finite bound. -/
private theorem nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm_ne_top
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {Λ : Set ℕ} {t : ℕ → ℕ} {g : ℕ → α → ℂ} {N : ℝ}
    {k : ℕ} {Q : WeakGridSpace.LevelCell G.toWeakGridSpace k}
    (hA : (∑' i : {i // i ∈ Λ},
      nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
        G β p qtilde hβ hp hp_top Λ t g Q i) ≤ ENNReal.ofReal N)
    (i : {i // i ∈ Λ}) :
    nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
      G β p qtilde hβ hp hp_top Λ t g Q i ≠ ∞ := by
  have hle := (ENNReal.le_tsum i).trans hA
  exact (hle.trans_lt ENNReal.ofReal_lt_top).ne

/-- In particular the positive tail seminorm of any multiplier whose support
meets the cell is finite. -/
private theorem positiveTailNorm_ne_top_of_meets_of_tsum_le
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {Λ : Set ℕ} {t : ℕ → ℕ} {g : ℕ → α → ℂ} {N : ℝ}
    {k : ℕ} {Q : WeakGridSpace.LevelCell G.toWeakGridSpace k}
    (hA : (∑' i : {i // i ∈ Λ},
      nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
        G β p qtilde hβ hp hp_top Λ t g Q i) ≤ ENNReal.ofReal N)
    {i : {i // i ∈ Λ}}
    (hmeet : goodGridLevelCellMeetsSupport G Q (g i.1)) :
    souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
      (t i.1) (g i.1) ≠ ∞ := by
  have hterm := nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm_ne_top
    G β p qtilde hβ hp hp_top hA i
  simp only [nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm,
    if_pos hmeet] at hterm
  exact hterm

/-- Restriction of the positive infinite condition A to a finite subfamily:
the finite relevant positive tail sum over any finite subset of `Λ` is
dominated by the infinite sum. -/
private theorem nonArchimedeanRelevantPositiveTailSelfsSum_le_tsum
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {Λ : Set ℕ} {Λfin : Finset ℕ} {t : ℕ → ℕ} {g : ℕ → α → ℂ}
    {k : ℕ} {Q : WeakGridSpace.LevelCell G.toWeakGridSpace k}
    (hΛfin : ∀ i ∈ Λfin, i ∈ Λ) :
    nonArchimedeanRelevantPositiveTailSelfsSum
        G β p qtilde hβ hp hp_top Λfin t g Q ≤
      ∑' i : {i // i ∈ Λ},
        nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
          G β p qtilde hβ hp hp_top Λ t g Q i := by
  classical
  let F : ℕ → ℝ≥0∞ := fun i =>
    if goodGridLevelCellMeetsSupport G Q (g i) then
      souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top (t i) (g i)
    else
      0
  have htsum_eq :
      (∑' i : {i // i ∈ Λ},
        nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
          G β p qtilde hβ hp hp_top Λ t g Q i) =
        ∑' i : ℕ, Λ.indicator F i := by
    rw [← tsum_subtype Λ F]
    rfl
  have hfin_eq :
      nonArchimedeanRelevantPositiveTailSelfsSum
          G β p qtilde hβ hp hp_top Λfin t g Q =
        ∑ i ∈ Λfin, Λ.indicator F i := by
    show (∑ i ∈ Λfin, F i) = ∑ i ∈ Λfin, Λ.indicator F i
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Set.indicator_of_mem (hΛfin i hi)]
  rw [hfin_eq, htsum_eq]
  exact ENNReal.sum_le_tsum Λfin

/-- Pointwise absolute summability on an active cell, positive version: if
`z` lies in an active cell `Q`, the multipliers obey the tail `L∞` bound, and
the positive infinite condition A holds at `Q`, then the absolute series
`∑ ‖g i z‖` converges with sum at most `K * N`. -/
private theorem hasSum_norm_of_mem_active_pos
    (G : GoodGridSpace (α := α)) (β : ℝ) (p qtilde : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ qtilde)]
    {Λ : Set ℕ} {t : ℕ → ℕ} {g : ℕ → α → ℂ}
    {k : ℕ} {Q : WeakGridSpace.LevelCell G.toWeakGridSpace k}
    {z : α} {K N : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hN : 0 ≤ N)
    (hzQ : z ∈ Q.1)
    (hg_bound : ∀ i : {i // i ∈ Λ},
      souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
          (t i.1) (g i.1) ≠ ∞ →
        ‖g i.1 z‖ ≤ K *
          (souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
            (t i.1) (g i.1)).toReal)
    (hA : (∑' i : {i // i ∈ Λ},
      nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
        G β p qtilde hβ hp hp_top Λ t g Q i) ≤ ENNReal.ofReal N) :
    HasSum (fun i : {i // i ∈ Λ} => ‖g i.1 z‖)
        (∑' i : {i // i ∈ Λ}, ‖g i.1 z‖) ∧
      (∑' i : {i // i ∈ Λ}, ‖g i.1 z‖) ≤ K * N := by
  classical
  set Term : {i // i ∈ Λ} → ℝ≥0∞ := fun i =>
    nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
      G β p qtilde hβ hp hp_top Λ t g Q i with hTerm
  have hterm_ne_top : ∀ i, Term i ≠ ∞ := fun i =>
    nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm_ne_top
      G β p qtilde hβ hp hp_top hA i
  have htsum_ne_top : (∑' i, Term i) ≠ ∞ :=
    (hA.trans_lt ENNReal.ofReal_lt_top).ne
  have hsummable_toReal : Summable (fun i => (Term i).toReal) :=
    ENNReal.summable_toReal htsum_ne_top
  have htoReal_le : (∑' i, (Term i).toReal) ≤ N := by
    calc
      (∑' i, (Term i).toReal) = (∑' i, Term i).toReal :=
        (ENNReal.tsum_toReal_eq hterm_ne_top).symm
      _ ≤ (ENNReal.ofReal N).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hA
      _ = N := ENNReal.toReal_ofReal hN
  refine hasSum_of_nonneg_le_mul_hasSum hK_nonneg
    (fun i => norm_nonneg _) ?_ hsummable_toReal.hasSum htoReal_le
  intro i
  by_cases hmeet : goodGridLevelCellMeetsSupport G Q (g i.1)
  · have hfin_i : souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
        (t i.1) (g i.1) ≠ ∞ :=
      positiveTailNorm_ne_top_of_meets_of_tsum_le
        G β p qtilde hβ hp hp_top hA hmeet
    have hTerm_eq : (Term i).toReal =
        (souzaPositivePointwiseSelfsTailNorm G β p qtilde hβ hp hp_top
          (t i.1) (g i.1)).toReal := by
      rw [hTerm]
      simp [nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm, hmeet]
    rw [hTerm_eq]
    exact hg_bound i hfin_i
  · have hgz : g i.1 z = 0 := by
      by_contra hgz_ne
      exact hmeet ⟨z, hzQ, hgz_ne⟩
    have hTerm_eq : (Term i).toReal = 0 := by
      rw [hTerm]
      simp [nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm, hmeet]
    rw [hTerm_eq, hgz]
    simp

/-- **Positive non-Archimedean product representation with explicit errors.**

Positive-cone analogue of `exists_nonArchimedeanProductRepresentation_with_errors`.
The `represents` and `cost` parts mirror the non-positive assembly (using the
positive local data and the plain `RepresentationWsubGandALS` extracted from it);
the support consequence `[ii]` is read off `Transmutation_of_Atoms_Claim_B` and the
positivity consequence `[i]` off `Transmutation_of_Atoms_Claim_B_sharp`. -/
private theorem exists_nonArchimedeanProductRepresentation_pos_with_errors
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) {N : ℝ}
    (hN : 0 ≤ N)
    (f : α → ℂ)
    {RsrcTarget : Lp ℂ p G.toWeakGridSpace.measure}
    (Rsrc : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      RsrcTarget)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rsrc)
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f RsrcTarget)
    (hRcanon : SouzaCanonicalRepresentation G s p hs hp hp_top Rsrc)
    (hgPos : ∀ i ∈ Λ,
      SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i))
    (hPosTail : ∀ i ∈ Λ,
      ∃ C : ℝ≥0∞,
        SouzaPositivePointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (Rsrc.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantPositiveTailSelfsSum
          G β p qtilde hβ hp hp_top Λ t g Q ≤ ENNReal.ofReal N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (Rsrc.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k)
    {εTail εGeom : ℝ} (hεTail : 0 < εTail) (hεGeom : 0 < εGeom) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
    ∃ S : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        (y : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => (∑ i ∈ Λ, g i z) * f z)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
        (if q = ∞ then
          (G.toWeakGridSpace.grid.Cmult1 : ℝ) *
            ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                (N + (Λ.card : ℝ) * εTail) + εGeom) ^ p.toReal) ^
              (1 / p.toReal)) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ
                ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)
        else
          (G.toWeakGridSpace.grid.Cmult1 : ℝ) *
            ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                (N + (Λ.card : ℝ) * εTail) + εGeom) ^ p.toReal) ^
              (1 / p.toReal)) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ
                ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1) *
            (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc ∧
      (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        (S.block k).coeff Q ≠ 0 →
          ∃ i ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1), g i z ≠ 0) ∧
      (SouzaPositiveRepresentation G s p hs hp hp_top Rsrc →
        SouzaConePositiveRepresentation G s p hs hp hp_top S) := by
  classical
  let Gi := G.toWeakGridSpace
  let AS := souzaAtomFamily G s p hs hp hp_top
  let lam : ℝ := (G.grid.lambda2 ^ (β - s)) ^ p.toReal
  let C : ℝ :=
    ((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
        (N + (Λ.card : ℝ) * εTail) + εGeom) ^ p.toReal
  have hlam_pos : 0 < lam := by
    dsimp [lam]
    have hlambda2_pos : 0 < G.grid.lambda2 :=
      lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
    have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
      Real.rpow_pos_of_pos hlambda2_pos (β - s)
    exact Real.rpow_pos_of_pos hroot_pos p.toReal
  have hlam_lt : lam < 1 := by
    dsimp [lam]
    have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
    have hdelta : 0 < β - s := sub_pos.mpr hβs
    have hlambda2_pos : 0 < G.grid.lambda2 :=
      lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
    have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
      Real.rpow_pos_of_pos hlambda2_pos (β - s)
    have hroot_lt : G.grid.lambda2 ^ (β - s) < 1 :=
      Real.rpow_lt_one hlambda2_pos.le G.grid.hlambda2_lt_one hdelta
    exact Real.rpow_lt_one hroot_pos.le hroot_lt hp_pos
  have hC_nonneg : 0 ≤ C := by
    have hK0 : 0 ≤ 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1 := by
      have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
      linarith
    have hBtail : 0 ≤ N + (Λ.card : ℝ) * εTail := by
      exact add_nonneg hN (mul_nonneg (by exact_mod_cast Nat.zero_le Λ.card) hεTail.le)
    have hbase :
        0 ≤ (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
            (N + (Λ.card : ℝ) * εTail) + εGeom := by
      exact add_nonneg (mul_nonneg hK0 hBtail) hεGeom.le
    exact Real.rpow_nonneg hbase _
  rcases exists_nonArchimedeanLocalTransmutationData_pos
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
      Λ t g hN hgPos hPosTail Rsrc hRcanon hA hB hεTail hεGeom with
    ⟨h, Rt, hRt_pos, hLocal, hSupp⟩
  have hRt :
      WeakGridSpace.RepresentationWsubGandALS (p := p) (q := q) Gi Gi AS
        (fun i : ℕ => i)
        ⟨0, 0, 1, by norm_num, nonArchimedean_id_almostLinear_bound⟩
        lam hlam_pos hlam_lt C hC_nonneg h Rt := by
    intro i Q
    rcases hRt_pos i Q with ⟨hfin, hloc, hdecay⟩
    refine ⟨hfin, ?_, hdecay⟩
    intro j S
    exact ⟨(hloc j S).1, (hloc j S).2.1⟩
  let c : (i : ℕ) → WeakGridSpace.LevelCell Gi i → ℂ :=
    fun i Q => (Rsrc.block i).coeff Q
  have hc : WeakGridSpace.CoeffFinitePQCost (p := p) (q := q) Gi c := by
    simpa [Gi, c, WeakGridSpace.CoeffFinitePQCost,
      WeakGridSpace.CoeffPLevel, WeakGridSpace.LpGridRepresentation.FinitePQCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower] using hRfin
  have hcost_eq :
      WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi c =
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
    simp [Gi, c, WeakGridSpace.CoeffPQCost, WeakGridSpace.CoeffPLevel,
      WeakGridSpace.LpGridRepresentation.pqCost,
      WeakGridSpace.LpGridRepresentation.levelCoeffPower]
  have hsrc_tendsto :
      Filter.Tendsto
        (fun n => ∑ i ∈ Finset.range n, (Rsrc.block i).toLp AS)
        Filter.atTop (𝓝 RsrcTarget) := by
    simpa [AS] using Rsrc.hasSum.tendsto_sum_nat
  by_cases hqtop : q = ∞
  · subst q
    haveI : Fact ((1 : ℝ≥0∞) ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
    rcases WeakGridSpace.Transmutation_of_Atoms_Claim_A_top
        (G := Gi) (W := Gi) (AW := AS)
        (p := p) (u := ∞)
        (fun i : ℕ => i) 0 0 1 (by norm_num)
        nonArchimedean_id_almostLinear_bound
        lam hlam_pos hlam_lt C hC_nonneg h Rt hRt c hc
        (souza_assumptionG2 G s p ∞ hs hp hp_top)
        hp_top hs with
      ⟨gLim, hsum, hmem, hfin, htend, hcost⟩
    let S : WeakGridSpace.LpGridRepresentation AS gLim :=
      { block := WeakGridSpace.TransmutationBlockLimit Gi Gi AS h Rt c 0 1
        hasSum := hsum }
    let y : WeakGridSpace.BesovishSpace AS ∞ := ⟨gLim, ⟨S, hfin⟩⟩
    have hprod :
        WeakGridSpace.RepresentsPointwiseProduct
          (G := Gi) (p := p) (fun z => ∑ i ∈ Λ, g i z)
          RsrcTarget gLim := by
      exact WeakGridSpace.RepresentsPointwiseProduct.of_tendsto_Lp
        (G := Gi) (p := p)
        hsrc_tendsto htend
        (fun n =>
          nonArchimedean_partialSum_representsPointwiseProduct
            G s p hs hp hp_top Λ g Rsrc h hLocal n)
    have hrep :
        WeakGridSpace.RepresentsFunction
          (G := Gi) (p := p)
          (fun z => (∑ i ∈ Λ, g i z) * f z) gLim := by
      filter_upwards [hprod, hRep] with z hz hfz
      rw [hz, hfz]
    refine ⟨y, S, ?_, hfin, ?_, ?_, ?_⟩
    · simpa [y, Gi, AS] using hrep
    · calc
        WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) S
            ≤ (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                lam ^ (-(0 : ℝ) / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1) *
                WeakGridSpace.CoeffPQCost (p := p) (q := ∞) Gi c := by
              simpa [S] using hcost
        _ =
            (if (∞ : ℝ≥0∞) = ∞ then
              (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1)
            else
              (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1) *
                (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / (∞ : ℝ≥0∞).toReal)) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc := by
              simp [hcost_eq, C, lam, Gi]
    · intro k P hP_coeff
      have hm_real :
          WeakGridSpace.TransmutationCoeffLimit Gi Gi AS h Rt c 0 1 P ≠ 0 := by
        intro h0
        apply hP_coeff
        show (WeakGridSpace.TransmutationCoeffLimit Gi Gi AS h Rt c 0 1 P : ℂ) = 0
        exact_mod_cast h0
      rcases WeakGridSpace.transmutationCoeff_support_witness
          Gi Gi AS (fun i : ℕ => i) 0 0 1 (by norm_num)
          nonArchimedean_id_almostLinear_bound
          lam hlam_pos hlam_lt C hC_nonneg h Rt hRt_pos c
          (WeakGridSpace.transmutationStabilizationIndex 0 1 k) P hm_real with
        ⟨i₀, hi₀, Q', hQ', hPQ', hcQ', r, hr_pos, hr_coeff⟩
      exact hSupp i₀ Q' k P (by rw [hr_coeff]; exact_mod_cast hr_pos.ne')
    · intro hRpos k P
      refine ⟨⟨WeakGridSpace.TransmutationCoeffLimit Gi Gi AS h Rt c 0 1 P, ?_, rfl⟩, ?_⟩
      · unfold WeakGridSpace.TransmutationCoeffLimit WeakGridSpace.TransmutationCoeff
        exact Finset.sum_nonneg
          (fun i _ => Finset.sum_nonneg (fun Q _ => norm_nonneg _))
      · have hc_nonneg :
            ∀ i (Q : WeakGridSpace.LevelCell Gi i), ∃ r : NNReal, c i Q = (r : ℂ) := by
          intro i Q
          rcases hRpos i Q with ⟨d, hd_nonneg, hd_coeff, _⟩
          exact ⟨⟨d, hd_nonneg⟩, by
            show (Rsrc.block i).coeff Q = ((⟨d, hd_nonneg⟩ : NNReal) : ℂ)
            rw [hd_coeff]⟩
        refine Filter.Eventually.of_forall (fun x => ?_)
        by_cases hxP : x ∈ P.1
        · exact WeakGridSpace.TransmutationAtomLocalLimit_toFunction_nonneg
            Gi Gi AS (fun i : ℕ => i) 0 0 1 (by norm_num)
            nonArchimedean_id_almostLinear_bound
            lam hlam_pos hlam_lt C hC_nonneg h Rt hRt_pos c hc_nonneg P hxP
        · refine ⟨0, le_refl 0, ?_⟩
          have hsupp := AS.local_support
            (WeakGridSpace.levelCellToWeakGridCell Gi k P)
            (WeakGridSpace.TransmutationAtomLocalLimit Gi Gi AS h Rt c 0 1 P) x hxP
          rw [Complex.ofReal_zero]
          exact hsupp
  · rcases WeakGridSpace.Transmutation_of_Atoms_Claim_A
        (G := Gi) (W := Gi) (AW := AS)
        (p := p) (q := q) (u := ∞)
        (fun i : ℕ => i) 0 0 1 (by norm_num)
        nonArchimedean_id_almostLinear_bound
        lam hlam_pos hlam_lt C hC_nonneg h Rt hRt c hc hqtop
        (souza_assumptionG2 G s p q hs hp hp_top)
        hp_top hs with
      ⟨gLim, hsum, hmem, hfin, htend, hcost⟩
    let S : WeakGridSpace.LpGridRepresentation AS gLim :=
      { block := WeakGridSpace.TransmutationBlockLimit Gi Gi AS h Rt c 0 1
        hasSum := hsum }
    let y : WeakGridSpace.BesovishSpace AS q := ⟨gLim, ⟨S, hfin⟩⟩
    have hprod :
        WeakGridSpace.RepresentsPointwiseProduct
          (G := Gi) (p := p) (fun z => ∑ i ∈ Λ, g i z)
          RsrcTarget gLim := by
      exact WeakGridSpace.RepresentsPointwiseProduct.of_tendsto_Lp
        (G := Gi) (p := p)
        hsrc_tendsto htend
        (fun n =>
          nonArchimedean_partialSum_representsPointwiseProduct
            G s p hs hp hp_top Λ g Rsrc h hLocal n)
    have hrep :
        WeakGridSpace.RepresentsFunction
          (G := Gi) (p := p)
          (fun z => (∑ i ∈ Λ, g i z) * f z) gLim := by
      filter_upwards [hprod, hRep] with z hz hfz
      rw [hz, hfz]
    refine ⟨y, S, ?_, hfin, ?_, ?_, ?_⟩
    · simpa [y, Gi, AS] using hrep
    · calc
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S
            ≤ (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                lam ^ (-(0 : ℝ) / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1) *
                (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal) *
                WeakGridSpace.CoeffPQCost (p := p) (q := q) Gi c := by
              simpa [S] using hcost
        _ =
            (if q = ∞ then
              (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1)
            else
              (Gi.grid.Cmult1 : ℝ) *
                C ^ (1 / p.toReal) *
                WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                  (WeakGridSpace.transmutationKernelZ lam 0 1) *
                (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
              simp [hqtop, hcost_eq, C, lam, Gi]
    · intro k P hP_coeff
      have hm_real :
          WeakGridSpace.TransmutationCoeffLimit Gi Gi AS h Rt c 0 1 P ≠ 0 := by
        intro h0
        apply hP_coeff
        show (WeakGridSpace.TransmutationCoeffLimit Gi Gi AS h Rt c 0 1 P : ℂ) = 0
        exact_mod_cast h0
      rcases WeakGridSpace.transmutationCoeff_support_witness
          Gi Gi AS (fun i : ℕ => i) 0 0 1 (by norm_num)
          nonArchimedean_id_almostLinear_bound
          lam hlam_pos hlam_lt C hC_nonneg h Rt hRt_pos c
          (WeakGridSpace.transmutationStabilizationIndex 0 1 k) P hm_real with
        ⟨i₀, hi₀, Q', hQ', hPQ', hcQ', r, hr_pos, hr_coeff⟩
      exact hSupp i₀ Q' k P (by rw [hr_coeff]; exact_mod_cast hr_pos.ne')
    · intro hRpos k P
      refine ⟨⟨WeakGridSpace.TransmutationCoeffLimit Gi Gi AS h Rt c 0 1 P, ?_, rfl⟩, ?_⟩
      · unfold WeakGridSpace.TransmutationCoeffLimit WeakGridSpace.TransmutationCoeff
        exact Finset.sum_nonneg
          (fun i _ => Finset.sum_nonneg (fun Q _ => norm_nonneg _))
      · have hc_nonneg :
            ∀ i (Q : WeakGridSpace.LevelCell Gi i), ∃ r : NNReal, c i Q = (r : ℂ) := by
          intro i Q
          rcases hRpos i Q with ⟨d, hd_nonneg, hd_coeff, _⟩
          exact ⟨⟨d, hd_nonneg⟩, by
            show (Rsrc.block i).coeff Q = ((⟨d, hd_nonneg⟩ : NNReal) : ℂ)
            rw [hd_coeff]⟩
        refine Filter.Eventually.of_forall (fun x => ?_)
        by_cases hxP : x ∈ P.1
        · exact WeakGridSpace.TransmutationAtomLocalLimit_toFunction_nonneg
            Gi Gi AS (fun i : ℕ => i) 0 0 1 (by norm_num)
            nonArchimedean_id_almostLinear_bound
            lam hlam_pos hlam_lt C hC_nonneg h Rt hRt_pos c hc_nonneg P hxP
        · refine ⟨0, le_refl 0, ?_⟩
          have hsupp := AS.local_support
            (WeakGridSpace.levelCellToWeakGridCell Gi k P)
            (WeakGridSpace.TransmutationAtomLocalLimit Gi Gi AS h Rt c 0 1 P) x hxP
          rw [Complex.ofReal_zero]
          exact hsupp

/-- **Positive non-Archimedean product representation (clean constant).**

Single assembly lemma behind the positive-cone theorem: given a canonical source
representation `Rsrc` and positive multipliers, it produces one output
representation `S` of `(∑ᵢ gᵢ)·f` with the cost bound (clean constant, no error
parameters), the support consequence `[ii]`, and the conditional positivity
consequence `[i]`.  Internally it builds positive local transmutation data and
reads everything off `Claim A` / `Claim B` / `Claim B_sharp`; the error
parameters of the underlying construction are sent to zero proportionally to
`N`. -/
theorem exists_nonArchimedeanProductRepresentation_positive
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) (N : ℝ)
    (f : α → ℂ)
    {RsrcTarget : Lp ℂ p G.toWeakGridSpace.measure}
    (Rsrc : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      RsrcTarget)
    (hN : 0 ≤ N)
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f RsrcTarget)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rsrc)
    (hRcanon : SouzaCanonicalRepresentation G s p hs hp hp_top Rsrc)
    (hgPos : ∀ i ∈ Λ,
      SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i))
    (hPosTail : ∀ i ∈ Λ,
      ∃ C : ℝ≥0∞,
        SouzaPositivePointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (Rsrc.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantPositiveTailSelfsSum
          G β p qtilde hβ hp hp_top Λ t g Q ≤ ENNReal.ofReal N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (Rsrc.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
    ∃ S : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        (y : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => (∑ i ∈ Λ, g i z) * f z)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
        ((G.toWeakGridSpace.grid.Cmult1 : ℝ) *
          (2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1) *
          WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
            (WeakGridSpace.transmutationKernelZ
              ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)) *
          N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc ∧
      (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        (S.block k).coeff Q ≠ 0 →
          ∃ i ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1), g i z ≠ 0) ∧
      (SouzaPositiveRepresentation G s p hs hp hp_top Rsrc →
        SouzaConePositiveRepresentation G s p hs hp hp_top S) := by
  classical
  by_cases hNzero : N = 0
  · subst N
    -- Degenerate case `N = 0`.  The cost target `Cgen · 0 · pqCost = 0` forces a
    -- zero-coefficient representation, so the product `(∑ g)·f` must itself vanish.
    -- We read that off the positive error construction with arbitrarily small
    -- errors (its cost tends to `0`), conclude the product is represented by the
    -- zero Besov class, and hand back the canonical cone-positive zero
    -- representation, whose support / positivity consequences are immediate.
    let AS := souzaAtomFamily G s p hs hp hp_top
    let Gi := G.toWeakGridSpace
    let F : α → ℂ := fun z => (∑ i ∈ Λ, g i z) * f z
    rcases exists_nonArchimedeanProductRepresentation_pos_with_errors
        G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
        Λ t g (le_refl (0 : ℝ)) f Rsrc hRfin hRep hRcanon hgPos hPosTail hA hB
        (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) with
      ⟨y₀, S₀, hy₀_rep, _hS₀fin, _hS₀cost, _, _⟩
    have hfiniteA :
        WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations (A := AS) q :=
      WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations AS q
    let lam : ℝ := (G.grid.lambda2 ^ (β - s)) ^ p.toReal
    let Ktail : ℝ := 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1
    have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
    have hKtail_nonneg : 0 ≤ Ktail := by
      have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
      dsimp [Ktail]
      linarith
    have hkernel_nonneg :
        ∀ n : ℤ, 0 ≤ WeakGridSpace.transmutationKernelZ lam 0 1 n := by
      intro n
      dsimp [WeakGridSpace.transmutationKernelZ]
      split_ifs
      · exact Real.rpow_nonneg (le_of_lt (by
          dsimp [lam]
          have hlambda2_pos : 0 < G.grid.lambda2 :=
            lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
          have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
            Real.rpow_pos_of_pos hlambda2_pos (β - s)
          exact Real.rpow_pos_of_pos hroot_pos p.toReal)) _
      · rfl
    have hcoef_nonneg :
        0 ≤ WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
          (WeakGridSpace.transmutationKernelZ lam 0 1) :=
      cCoefficientInt_nonneg_local p ∞ _ hkernel_nonneg
    let D : ℝ :=
      (Gi.grid.Cmult1 : ℝ) *
        WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
          (WeakGridSpace.transmutationKernelZ lam 0 1) *
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc
    have hD_nonneg : 0 ≤ D := by
      exact mul_nonneg
        (mul_nonneg (by exact_mod_cast Nat.zero_le Gi.grid.Cmult1) hcoef_nonneg)
        (WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rsrc)
    have hnorm_le_zero :
        WeakGridSpace.BesovishSpace.Norm_Costpq AS q y₀ ≤ 0 := by
      refine le_iff_forall_pos_le_add.mpr ?_
      intro η hη
      let Aε : ℝ := Ktail * (Λ.card : ℝ) + 1
      have hAε_pos : 0 < Aε := by
        have hcard_nonneg : 0 ≤ (Λ.card : ℝ) := by exact_mod_cast Nat.zero_le Λ.card
        dsimp [Aε]
        nlinarith [mul_nonneg hKtail_nonneg hcard_nonneg]
      let ε : ℝ := (η / (D + 1)) / Aε
      have hε : 0 < ε := by
        exact div_pos (div_pos hη (by linarith)) hAε_pos
      rcases exists_nonArchimedeanProductRepresentation_pos_with_errors
          G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
          Λ t g (le_refl (0 : ℝ)) f Rsrc hRfin hRep hRcanon hgPos hPosTail hA hB
          hε hε with
        ⟨yε, Sε, hyε_rep, hSεfin, hSεcost, _, _⟩
      have hy_eq : y₀ = yε :=
        souzaBesovish_eq_of_representsFunction
          G s p q hs hp hp_top (F := F) hy₀_rep hyε_rep
      have hnorm_le_cost :
          WeakGridSpace.BesovishSpace.Norm_Costpq AS q y₀ ≤
            WeakGridSpace.LpGridRepresentation.pqCost (q := q) Sε := by
        rw [hy_eq]
        exact WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
          (A := AS) (q := q) yε Sε hSεfin
      let base : ℝ := Ktail * ((Λ.card : ℝ) * ε) + ε
      have hbase_nonneg : 0 ≤ base := by
        exact add_nonneg
          (mul_nonneg hKtail_nonneg
            (mul_nonneg (by exact_mod_cast Nat.zero_le Λ.card) hε.le))
          hε.le
      have hroot_eq : ((base ^ p.toReal) ^ (1 / p.toReal)) = base := by
        have hmul : p.toReal * (1 / p.toReal) = 1 := by
          field_simp [hp_pos.ne']
        calc
          (base ^ p.toReal) ^ (1 / p.toReal)
              = base ^ (p.toReal * (1 / p.toReal)) := by
                  rw [← Real.rpow_mul hbase_nonneg]
          _ = base := by rw [hmul, Real.rpow_one]
      have hbase_le : base ≤ η / (D + 1) := by
        have hbase_eq : base = Aε * ε := by
          dsimp [base, Aε]
          ring
        rw [hbase_eq]
        calc
          Aε * ε = η / (D + 1) := by
            dsimp [ε]
            field_simp [hAε_pos.ne']
          _ ≤ η / (D + 1) := le_rfl
      have hDbase_le : D * base ≤ η := by
        calc
          D * base ≤ D * (η / (D + 1)) :=
            mul_le_mul_of_nonneg_left hbase_le hD_nonneg
          _ = (D / (D + 1)) * η := by ring
          _ ≤ 1 * η := by
            have hfrac : D / (D + 1) ≤ 1 := by
              rw [div_le_iff₀ (by linarith)]
              linarith
            exact mul_le_mul_of_nonneg_right hfrac hη.le
          _ = η := by ring
      have hSεcost_le :
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Sε ≤ η := by
        refine hSεcost.trans ?_
        by_cases hqtop : q = ∞
        · subst q
          have hroot_expr :
              ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                  ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
                (1 / p.toReal)) = base := by
            simpa [base, Ktail] using hroot_eq
          calc
            ((if (∞ : ℝ≥0∞) = ∞ then
                (Gi.grid.Cmult1 : ℝ) *
                  ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                      ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
                    (1 / p.toReal)) *
                  WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                    (WeakGridSpace.transmutationKernelZ
                      ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)
              else
                (Gi.grid.Cmult1 : ℝ) *
                  ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                      ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
                    (1 / p.toReal)) *
                  WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                    (WeakGridSpace.transmutationKernelZ
                      ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1) *
                  (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / (∞ : ℝ≥0∞).toReal)) *
                WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc)
                =
              ((Gi.grid.Cmult1 : ℝ) * base *
                  WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                    (WeakGridSpace.transmutationKernelZ lam 0 1)) *
                WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc := by
                  rw [hroot_expr]
                  simp [lam, Gi]
            _ = D * base := by
                  dsimp [D]
                  ring
            _ ≤ η := hDbase_le
        ·
          have hroot_expr :
              ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                  ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
                (1 / p.toReal)) = base := by
            simpa [base, Ktail] using hroot_eq
          calc
            ((if q = ∞ then
                (Gi.grid.Cmult1 : ℝ) *
                  ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                      ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
                    (1 / p.toReal)) *
                  WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                    (WeakGridSpace.transmutationKernelZ
                      ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)
              else
                (Gi.grid.Cmult1 : ℝ) *
                  ((((2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) *
                      ((0 : ℝ) + (Λ.card : ℝ) * ε) + ε) ^ p.toReal) ^
                    (1 / p.toReal)) *
                  WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                    (WeakGridSpace.transmutationKernelZ
                      ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1) *
                  (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)) *
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc)
                =
              ((Gi.grid.Cmult1 : ℝ) * base *
                  WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                    (WeakGridSpace.transmutationKernelZ lam 0 1)) *
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
                  rw [hroot_expr]
                  simp [hqtop, lam, Gi]
            _ = D * base := by
                  dsimp [D]
                  ring
            _ ≤ η := hDbase_le
      calc
        WeakGridSpace.BesovishSpace.Norm_Costpq AS q y₀
            ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) Sε := hnorm_le_cost
        _ ≤ η := hSεcost_le
        _ = 0 + η := by ring
    have hnorm_zero :
        WeakGridSpace.BesovishSpace.Norm_Costpq AS q y₀ = 0 := by
      exact le_antisymm hnorm_le_zero
        (WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
          (A := AS) (q := q) hfiniteA y₀)
    have hy₀_zero : y₀ = 0 :=
      WeakGridSpace.BesovishSpace.eq_zero_of_Norm_Costpq_eq_zero
        (A := AS) (q := q) hp_top
        (souza_assumptionG2 G s p q hs hp hp_top).1 hfiniteA hnorm_zero
    obtain ⟨Szero, hSzero_fin, hSzero_cost, hSzero_pos, hSzero_coeff⟩ :=
      exists_souzaConePositiveZeroRepresentation G s p q hs hp hp_top
    refine ⟨0, Szero, ?_, hSzero_fin, ?_, ?_, ?_⟩
    · simpa [F, AS, Gi, hy₀_zero] using hy₀_rep
    · rw [hSzero_cost]
      simp
    · intro k Q hcoeff
      exact absurd (hSzero_coeff k Q) hcoeff
    · intro _
      exact hSzero_pos
  have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hNzero)
  let Gi := G.toWeakGridSpace
  let lam : ℝ := (G.grid.lambda2 ^ (β - s)) ^ p.toReal
  let Ktail : ℝ := 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1
  let epsTail : ℝ := N / ((Λ.card : ℝ) + 1)
  let epsGeom : ℝ := N
  have hden_pos : 0 < (Λ.card : ℝ) + 1 := by positivity
  have hεTail : 0 < epsTail := div_pos hNpos hden_pos
  have hεGeom : 0 < epsGeom := hNpos
  rcases exists_nonArchimedeanProductRepresentation_pos_with_errors
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
      Λ t g hN f Rsrc hRfin hRep hRcanon hgPos hPosTail hA hB hεTail hεGeom with
    ⟨y, S, hSrep, _hSfin, hScost, hSupp, hPos⟩
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hKtail_nonneg : 0 ≤ Ktail := by
    have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
    dsimp [Ktail]
    linarith
  have hcard_eps_le :
      (Λ.card : ℝ) * epsTail ≤ N := by
    have hfrac_le_one : ((Λ.card : ℝ) / ((Λ.card : ℝ) + 1) : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hden_pos]
      linarith [show 0 ≤ (Λ.card : ℝ) by exact_mod_cast Nat.zero_le Λ.card]
    calc
      (Λ.card : ℝ) * epsTail
          = ((Λ.card : ℝ) / ((Λ.card : ℝ) + 1)) * N := by
              change (Λ.card : ℝ) * (N / ((Λ.card : ℝ) + 1)) =
                ((Λ.card : ℝ) / ((Λ.card : ℝ) + 1)) * N
              ring_nf
      _ ≤ 1 * N := mul_le_mul_of_nonneg_right hfrac_le_one hNpos.le
      _ = N := by ring
  have htail_le : N + (Λ.card : ℝ) * epsTail ≤ 2 * N := by
    linarith
  have hbase_nonneg :
      0 ≤ Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom := by
    exact add_nonneg
      (mul_nonneg hKtail_nonneg
        (add_nonneg hNpos.le
          (mul_nonneg (by exact_mod_cast Nat.zero_le Λ.card) hεTail.le)))
      hεGeom.le
  have hbase_le :
      Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom ≤
        (2 * Ktail + 1) * N := by
    have hmul := mul_le_mul_of_nonneg_left htail_le hKtail_nonneg
    calc
      Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom
          ≤ Ktail * (2 * N) + N := by
              exact add_le_add hmul le_rfl
      _ = (2 * Ktail + 1) * N := by ring
  have hroot_le :
      ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
          (1 / p.toReal) ≤
        (2 * Ktail + 1) * N := by
    have hroot_eq :
        ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
            (1 / p.toReal) =
          Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom := by
      have hmul : p.toReal * (1 / p.toReal) = 1 := by
        field_simp [hp_pos.ne']
      calc
        ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
            (1 / p.toReal)
            =
          (Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^
            (p.toReal * (1 / p.toReal)) := by
              rw [← Real.rpow_mul hbase_nonneg]
        _ = Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom := by
              rw [hmul, Real.rpow_one]
    rw [hroot_eq]
    exact hbase_le
  have hkernel_nonneg :
      ∀ n : ℤ, 0 ≤ WeakGridSpace.transmutationKernelZ lam 0 1 n := by
    intro n
    dsimp [WeakGridSpace.transmutationKernelZ]
    split_ifs
    · exact Real.rpow_nonneg (le_of_lt (by
        dsimp [lam]
        have hlambda2_pos : 0 < G.grid.lambda2 :=
          lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
        have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
          Real.rpow_pos_of_pos hlambda2_pos (β - s)
        exact Real.rpow_pos_of_pos hroot_pos p.toReal)) _
    · rfl
  have hcoef_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
        (WeakGridSpace.transmutationKernelZ lam 0 1) :=
    cCoefficientInt_nonneg_local p ∞ _ hkernel_nonneg
  have hpq_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc :=
    WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rsrc
  refine ⟨y, S, hSrep, _hSfin, ?_, hSupp, hPos⟩
  refine hScost.trans ?_
  by_cases hqtop : q = ∞
  · subst q
    have hfactor_le :
        (Gi.grid.Cmult1 : ℝ) *
            ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
              (1 / p.toReal) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1)
          ≤
        (Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N := by
      calc
        (Gi.grid.Cmult1 : ℝ) *
            ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
              (1 / p.toReal) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1)
            ≤
          (Gi.grid.Cmult1 : ℝ) * ((2 * Ktail + 1) * N) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hroot_le
                  (by exact_mod_cast Nat.zero_le Gi.grid.Cmult1))
                hcoef_nonneg
        _ =
          (Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N := by ring
    calc
      ((if (∞ : ℝ≥0∞) = ∞ then
          (Gi.grid.Cmult1 : ℝ) *
            ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
              (1 / p.toReal) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1)
        else
          (Gi.grid.Cmult1 : ℝ) *
              ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
                (1 / p.toReal) *
              WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                (WeakGridSpace.transmutationKernelZ lam 0 1) *
            (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / (∞ : ℝ≥0∞).toReal)) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc)
          ≤
        ((Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc := by
            simpa using mul_le_mul_of_nonneg_right hfactor_le hpq_nonneg
      _ =
        ((Gi.grid.Cmult1 : ℝ) *
          (2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1) *
          WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
            (WeakGridSpace.transmutationKernelZ
              ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)) *
          N * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rsrc := by
            simp [Gi, Ktail, lam]
  · have hceil_one :
        (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal) = 1 := by
      norm_num
    have hfactor_le :
        (Gi.grid.Cmult1 : ℝ) *
              ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
                (1 / p.toReal) *
              WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                (WeakGridSpace.transmutationKernelZ lam 0 1) *
            (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)
          ≤
        (Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N := by
      calc
        (Gi.grid.Cmult1 : ℝ) *
              ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
                (1 / p.toReal) *
              WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                (WeakGridSpace.transmutationKernelZ lam 0 1) *
            (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)
            =
          (Gi.grid.Cmult1 : ℝ) *
              ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
                (1 / p.toReal) *
              WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                (WeakGridSpace.transmutationKernelZ lam 0 1) := by
              rw [hceil_one, mul_one]
        _ ≤
          (Gi.grid.Cmult1 : ℝ) * ((2 * Ktail + 1) * N) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hroot_le
                  (by exact_mod_cast Nat.zero_le Gi.grid.Cmult1))
                hcoef_nonneg
        _ =
          (Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N := by ring
    calc
      ((if q = ∞ then
          (Gi.grid.Cmult1 : ℝ) *
            ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
              (1 / p.toReal) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1)
        else
          (Gi.grid.Cmult1 : ℝ) *
              ((Ktail * (N + (Λ.card : ℝ) * epsTail) + epsGeom) ^ p.toReal) ^
                (1 / p.toReal) *
              WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
                (WeakGridSpace.transmutationKernelZ lam 0 1) *
            (Nat.ceil (1 : ℝ) : ℝ) ^ (1 / q.toReal)) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc)
          ≤
        ((Gi.grid.Cmult1 : ℝ) * (2 * Ktail + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ lam 0 1) * N) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
            simpa [hqtop] using mul_le_mul_of_nonneg_right hfactor_le hpq_nonneg
      _ =
        ((Gi.grid.Cmult1 : ℝ) *
          (2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1) *
          WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
            (WeakGridSpace.transmutationKernelZ
              ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)) *
          N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rsrc := by
            simp [hqtop, Gi, Ktail, lam]

/-- **Positive-cone non-Archimedean estimate (assembly core).**

Public entry point that performs the full positive-cone assembly using the
private positive machinery of this file.  It builds the positive local
transmutation data (`exists_nonArchimedeanLocalTransmutationData_pos`) and reads
cost / support / positivity off the transmutation `Claim A` / `Claim B` /
`Claim B_sharp`.  The user-facing wrapper `souzaNonArchimedeanPropertyPositiveCone`
(in the standalone file) just forwards to this lemma.

See that wrapper's docstring for the precise statement and the reason the
support consequence `[ii]` is unconditional while the positivity consequence
`[i]` needs `c_Q ≥ 0`. -/
theorem souzaNonArchimedeanPropertyPositiveCone_core
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)] :
    ∃ Cgen : ℝ,
      0 ≤ Cgen ∧
      ∀ (Λ : Finset ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) (N : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
          0 ≤ N →
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) f
            (x : Lp ℂ p G.toWeakGridSpace.measure) →
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
          SouzaCanonicalRepresentation G s p hs hp hp_top R →
          (∀ i ∈ Λ,
            SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i)) →
          (∀ i ∈ Λ,
            ∃ C : ℝ≥0∞,
              SouzaPositivePointwiseSelfsTailBound
                G β p qtilde hβ hp hp_top (t i) (g i) C) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            (R.block k).coeff Q ≠ 0 →
              nonArchimedeanRelevantPositiveTailSelfsSum
                G β p qtilde hβ hp hp_top Λ t g Q ≤ ENNReal.ofReal N) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
            i ∈ Λ →
              (R.block k).coeff Q ≠ 0 →
                goodGridLevelCellMeetsSupport G Q (g i) →
                  t i ≤ k) →
          ∃ y : WeakGridSpace.BesovishSpace
              (souzaAtomFamily G s p hs hp hp_top) q,
            ∃ S : WeakGridSpace.LpGridRepresentation
                (souzaAtomFamily G s p hs hp hp_top)
                (y : Lp ℂ p G.toWeakGridSpace.measure),
              WeakGridSpace.RepresentsFunction
                (G := G.toWeakGridSpace) (p := p)
                (fun z => (∑ i ∈ Λ, g i z) * f z)
                (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
              WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
                Cgen * N *
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
              (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
                (S.block k).coeff Q ≠ 0 →
                  ∃ i ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1), g i z ≠ 0) ∧
              (SouzaPositiveRepresentation G s p hs hp hp_top R →
                SouzaConePositiveRepresentation G s p hs hp hp_top S) := by
  classical
  refine ⟨(G.toWeakGridSpace.grid.Cmult1 : ℝ) *
            (2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1) *
            WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
              (WeakGridSpace.transmutationKernelZ
                ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1), ?_, ?_⟩
  · have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
    have hmiddle :
        0 ≤ 2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1 := by
      linarith
    have hkernel_nonneg :
        ∀ n : ℤ, 0 ≤ WeakGridSpace.transmutationKernelZ
          ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1 n := by
      intro n
      dsimp [WeakGridSpace.transmutationKernelZ]
      split_ifs
      · exact Real.rpow_nonneg (le_of_lt (by
          have hlambda2_pos : 0 < G.grid.lambda2 :=
            lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
          have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
            Real.rpow_pos_of_pos hlambda2_pos (β - s)
          exact Real.rpow_pos_of_pos hroot_pos p.toReal)) _
      · rfl
    have hcoef_nonneg :
        0 ≤ WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
          (WeakGridSpace.transmutationKernelZ
            ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1) :=
      cCoefficientInt_nonneg_local p ∞ _ hkernel_nonneg
    exact mul_nonneg
      (mul_nonneg
        (by exact_mod_cast Nat.zero_le G.toWeakGridSpace.grid.Cmult1)
        hmiddle)
      hcoef_nonneg
  · intro Λ t g N f x R hN hRep hRfin hRcanon hgPos hPosTail hA hB
    exact exists_nonArchimedeanProductRepresentation_positive
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
      Λ t g N f R hN hRep hRfin hRcanon hgPos hPosTail hA hB

/-!
## Infinite positive multiplier families: assembly

The infinite positive theorem is assembled exactly like the non-positive one:
finite truncations along the initial segments of `Λ` via the finite positive
theorem, compactness of uniformly bounded representations (now with
coefficient and atom convergence), and identification of the limit.  The
support witness passes to the limit through the coefficient convergence; cone
positivity passes through the closedness of the positive cone.
-/

/-- The explicit constant of the finite positive theorem
`exists_nonArchimedeanProductRepresentation_positive`. -/
noncomputable def nonArchimedeanPositiveRepresentationConstant
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞) : ℝ :=
  (G.toWeakGridSpace.grid.Cmult1 : ℝ) *
    (2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1) *
    WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
      (WeakGridSpace.transmutationKernelZ
        ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1)

private theorem nonArchimedeanPositiveRepresentationConstant_nonneg
    (G : GoodGridSpace (α := α)) (s β : ℝ) (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    0 ≤ nonArchimedeanPositiveRepresentationConstant G s β p := by
  have hK := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
  have hmiddle :
      0 ≤ 2 * (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1) + 1 := by
    linarith
  have hkernel_nonneg :
      ∀ n : ℤ, 0 ≤ WeakGridSpace.transmutationKernelZ
        ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1 n := by
    intro n
    dsimp [WeakGridSpace.transmutationKernelZ]
    split_ifs
    · exact Real.rpow_nonneg (le_of_lt (by
        have hlambda2_pos : 0 < G.grid.lambda2 :=
          lt_of_lt_of_le G.grid.hlambda1_pos G.grid.hlambda1_le_lambda2
        have hroot_pos : 0 < G.grid.lambda2 ^ (β - s) :=
          Real.rpow_pos_of_pos hlambda2_pos (β - s)
        exact Real.rpow_pos_of_pos hroot_pos p.toReal)) _
    · rfl
  have hcoef_nonneg :
      0 ≤ WeakGridSpace.LpGridRepresentation.cCoefficientInt p ∞
        (WeakGridSpace.transmutationKernelZ
          ((G.grid.lambda2 ^ (β - s)) ^ p.toReal) 0 1) :=
    cCoefficientInt_nonneg_local p ∞ _ hkernel_nonneg
  exact mul_nonneg
    (mul_nonneg
      (by exact_mod_cast Nat.zero_le G.toWeakGridSpace.grid.Cmult1)
      hmiddle)
    hcoef_nonneg

/-- Finite truncations of the infinite positive data along the initial
segments of `Λ`, with the uniform cost bound, the support witness, and the
conditional cone positivity. -/
private theorem exists_nonArchimedean_finite_representation_initial_pos
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    {N : ℝ} (hN : 0 ≤ N)
    (Λ : Set ℕ) (n : ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    (f : α → ℂ)
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (hRcanon : SouzaCanonicalRepresentation G s p hs hp hp_top R)
    (hgPos : ∀ i ∈ Λ,
      SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i))
    (hPosTail : ∀ i ∈ Λ,
      ∃ C : ℝ≥0∞,
        SouzaPositivePointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        (∑' i : {i // i ∈ Λ},
          nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
            G β p qtilde hβ hp hp_top Λ t g Q i) ≤ ENNReal.ofReal N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z)
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          nonArchimedeanPositiveRepresentationConstant G s β p * N *
            WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 →
            ∃ i ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1), g i z ≠ 0) ∧
        (SouzaPositiveRepresentation G s p hs hp hp_top R →
          SouzaConePositiveRepresentation G s p hs hp hp_top S) := by
  classical
  let Λn : Finset ℕ := nonArchimedeanLambdaInitial Λ n
  have hgPos_fin : ∀ i ∈ Λn,
      SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i) := fun i hi =>
    hgPos i (mem_of_mem_nonArchimedeanLambdaInitial hi)
  have hPosTail_fin : ∀ i ∈ Λn,
      ∃ C : ℝ≥0∞,
        SouzaPositivePointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C := fun i hi =>
    hPosTail i (mem_of_mem_nonArchimedeanLambdaInitial hi)
  have hA_fin : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantPositiveTailSelfsSum
          G β p qtilde hβ hp hp_top Λn t g Q ≤ ENNReal.ofReal N := by
    intro k Q hQcoeff
    exact (nonArchimedeanRelevantPositiveTailSelfsSum_le_tsum
      G β p qtilde hβ hp hp_top
      (fun i hi => mem_of_mem_nonArchimedeanLambdaInitial hi)).trans
      (hA k Q hQcoeff)
  have hB_fin : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λn →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k := fun k Q i hi hQcoeff hmeet =>
    hB k Q i (mem_of_mem_nonArchimedeanLambdaInitial hi) hQcoeff hmeet
  obtain ⟨y, S, hy_rep, hS_fin, hS_cost, hS_supp, hS_pos⟩ :=
    exists_nonArchimedeanProductRepresentation_positive
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
      Λn t g N f R hN hRep hRfin hRcanon hgPos_fin hPosTail_fin hA_fin hB_fin
  refine ⟨y, S, hy_rep, hS_fin, hS_cost, ?_, hS_pos⟩
  intro k Q hne
  obtain ⟨i, hiΛn, hwit⟩ := hS_supp k Q hne
  exact ⟨i, mem_of_mem_nonArchimedeanLambdaInitial hiΛn, hwit⟩

/-- The nonnegative real ray `{c : ℝ≥0} ⊆ ℂ` is closed: it is the intersection
of the zero set of `im` and the nonnegativity set of `re`. -/
private theorem complex_nonnegReal_isClosed :
    IsClosed {z : ℂ | ∃ c : ℝ, 0 ≤ c ∧ z = (c : ℂ)} := by
  have hset : {z : ℂ | ∃ c : ℝ, 0 ≤ c ∧ z = (c : ℂ)} =
      {z : ℂ | z.im = 0} ∩ {z : ℂ | 0 ≤ z.re} := by
    ext z
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by simp, by simpa using hc⟩
    · rintro ⟨him, hre⟩
      refine ⟨z.re, hre, ?_⟩
      have him' : z.im = 0 := him
      apply Complex.ext <;> simp [him']
  rw [hset]
  exact (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

/-- **Limit of finite positive representations.**

Mirrors `exists_limit_representation_of_finite_sequence`, additionally
transporting the support witness and (conditionally) cone positivity to the
limit.  The support witness passes through the coefficient convergence of the
compactness extraction; cone positivity passes through the closedness of the
nonnegative real ray (coefficients) and almost-everywhere convergence of a
subsequence of the atom functions (atoms). -/
private theorem exists_limit_representation_of_finite_sequence_pos
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {Cbound : ℝ} (hCbound_nonneg : 0 ≤ Cbound)
    {h : α → ℂ} {partialFun : ℕ → α → ℂ}
    {Λ : Set ℕ} {g : ℕ → α → ℂ} {P : Prop}
    (yseq : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (Sseq : ∀ n, WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (yseq n : Lp ℂ p G.toWeakGridSpace.measure))
    (hyseq_rep : ∀ n,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (partialFun n)
        (yseq n : Lp ℂ p G.toWeakGridSpace.measure))
    (hSseq_fin : ∀ n,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (Sseq n))
    (hSseq_cost : ∀ n,
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) (Sseq n) ≤ Cbound)
    (hpartial_tendsto : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      Filter.Tendsto (fun n : ℕ => partialFun n z) Filter.atTop (𝓝 (h z)))
    (hSseq_supp : ∀ n k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ((Sseq n).block k).coeff Q ≠ 0 →
        ∃ i ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1), g i z ≠ 0)
    (hSseq_pos : P → ∀ n,
      SouzaConePositiveRepresentation G s p hs hp hp_top (Sseq n)) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) h
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤ Cbound ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 →
            ∃ i ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1), g i z ≠ 0) ∧
        (P → SouzaConePositiveRepresentation G s p hs hp hp_top S) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let μ := G.toWeakGridSpace.measure
  let yseqLp : ℕ → Lp ℂ p μ := fun n => (yseq n : Lp ℂ p μ)
  rcases WeakGridSpace.exists_strongly_convergent_subseq_of_uniform_pqCost
      (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
      hp_top hs le_top A
      (souza_assumptionG2 G s p q hs hp hp_top)
      (souza_assumptionA5 G s p hs hp hp_top)
      Sseq hCbound_nonneg hSseq_fin hSseq_cost with
    ⟨φ, hφ, yLimLp, S, hmemLim, hSfin, hScost, hy_tendsto, hcoeff_lim, hatom_lim⟩
  have hy_tendsto_lp :
      Filter.Tendsto
        (fun n : ℕ => yseqLp (φ n))
        Filter.atTop
        (𝓝 yLimLp) := by
    change Filter.Tendsto
      (fun n : ℕ => (yseq (φ n) : Lp ℂ p G.toWeakGridSpace.measure))
      Filter.atTop
      (𝓝 yLimLp)
    exact hy_tendsto
  rcases exists_subseq_tendsto_ae_of_tendsto_Lp
      (μ := μ)
      (u := fun n : ℕ => yseqLp (φ n))
      (uLim := yLimLp)
      hy_tendsto_lp with
    ⟨ψ, hψ, hy_ae⟩
  have hyseq_rep_lp : ∀ n, yseqLp n =ᵐ[μ] partialFun n := by
    intro n
    change WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) (partialFun n)
      (yseq n : Lp ℂ p G.toWeakGridSpace.measure)
    exact hyseq_rep n
  have hcoe :
      ∀ᵐ z ∂μ, ∀ n : ℕ,
        yseqLp (φ (ψ n)) z = partialFun (φ (ψ n)) z :=
    ae_eq_partialFun_on_composed_subseq hyseq_rep_lp φ ψ
  have hy_subseq_tendsto :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        Filter.Tendsto
          (fun n : ℕ => partialFun (φ (ψ n)) z)
          Filter.atTop
          (𝓝 (yLimLp z)) := by
    filter_upwards [hy_ae, hcoe] with z hyz hcoez
    exact hyz.congr' <|
      Filter.Eventually.of_forall fun n : ℕ => hcoez n
  have hLimRep :
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) h yLimLp :=
    representsFunction_of_tendsto_subseq
      G p φ ψ hφ hψ hpartial_tendsto hy_subseq_tendsto
  -- support witness at the limit, via coefficient convergence
  have hsupp_lim : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (S.block k).coeff Q ≠ 0 →
        ∃ i ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1), g i z ≠ 0 := by
    intro k Q hne
    have hex : ∃ n, ((Sseq (φ n)).block k).coeff Q ≠ 0 := by
      by_contra hall
      push_neg at hall
      have hzero :
          Filter.Tendsto (fun n => ((Sseq (φ n)).block k).coeff Q)
            Filter.atTop (𝓝 (0 : ℂ)) := by
        simpa [hall] using
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop (𝓝 (0 : ℂ)))
      exact hne (tendsto_nhds_unique (hcoeff_lim k Q) hzero)
    obtain ⟨n, hn⟩ := hex
    exact hSseq_supp (φ n) k Q hn
  -- cone positivity at the limit
  have hpos_lim : P → SouzaConePositiveRepresentation G s p hs hp hp_top S := by
    intro hP k Q
    have hpos_n : ∀ n,
        SouzaConePositiveLevelBlock G s p hs hp hp_top ((Sseq (φ n)).block k) :=
      fun n => hSseq_pos hP (φ n) k
    constructor
    · -- nonnegative real coefficient: closed-set limit
      exact complex_nonnegReal_isClosed.mem_of_tendsto (hcoeff_lim k Q)
        (Filter.Eventually.of_forall fun n => (hpos_n n Q).1)
    · -- atom in the positive cone: a.e. limit along a subsequence
      obtain ⟨ψa, _hψa, hae_atom⟩ :=
        exists_subseq_tendsto_ae_of_tendsto_Lp
          (μ := μ)
          (u := fun n => WeakGridSpace.atomLp A
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (((Sseq (φ n)).block k).atom Q))
          (uLim := WeakGridSpace.atomLp A
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((S.block k).atom Q))
          (hatom_lim k Q)
      have hcoe_n : ∀ᵐ x ∂μ, ∀ n : ℕ,
          ((WeakGridSpace.atomLp A
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (((Sseq (φ (ψa n))).block k).atom Q)) : α → ℂ) x =
            A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (((Sseq (φ (ψa n))).block k).atom Q) x := by
        refine ae_all_iff.2 ?_
        intro n
        exact atomLp_representsFunction G.toWeakGridSpace A
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          (((Sseq (φ (ψa n))).block k).atom Q)
      have hcoe_lim :
          ((WeakGridSpace.atomLp A
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((S.block k).atom Q)) : α → ℂ) =ᵐ[μ]
            A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              ((S.block k).atom Q) :=
        atomLp_representsFunction G.toWeakGridSpace A
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          ((S.block k).atom Q)
      have hcone_n : ∀ᵐ x ∂μ, ∀ n : ℕ,
          ∃ d : ℝ, 0 ≤ d ∧
            A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (((Sseq (φ (ψa n))).block k).atom Q) x = (d : ℂ) := by
        refine ae_all_iff.2 ?_
        intro n
        exact (hpos_n (ψa n) Q).2
      filter_upwards [hae_atom, hcoe_n, hcoe_lim, hcone_n]
        with x hx_lim hx_coe hx_coelim hx_cone
      have htends :
          Filter.Tendsto
            (fun n => A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (((Sseq (φ (ψa n))).block k).atom Q) x)
            Filter.atTop
            (𝓝 (A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              ((S.block k).atom Q) x)) := by
        rw [← hx_coelim]
        exact hx_lim.congr fun n => hx_coe n
      exact complex_nonnegReal_isClosed.mem_of_tendsto htends
        (Filter.Eventually.of_forall fun n => hx_cone n)
  exact ⟨⟨yLimLp, hmemLim⟩, S, hLimRep, hSfin, hScost, hsupp_lim, hpos_lim⟩

/--
Limit of finite positive representations with an abstract coefficient-support
predicate.

This is the reusable positive analogue of
`exists_limit_representation_of_finite_sequence_with_support`: coefficient
support passes to the limit by coefficient convergence, and cone positivity
passes to the limit by closedness of the nonnegative real ray and a.e.
convergence of atom representatives.
-/
theorem exists_limit_representation_of_finite_sequence_pos_with_support
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {Cbound : ℝ} (hCbound_nonneg : 0 ≤ Cbound)
    {h : α → ℂ} {partialFun : ℕ → α → ℂ}
    (SupportProp : ∀ k, WeakGridSpace.LevelCell G.toWeakGridSpace k → Prop)
    (yseq : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (Sseq : ∀ n, WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (yseq n : Lp ℂ p G.toWeakGridSpace.measure))
    (hyseq_rep : ∀ n,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (partialFun n)
        (yseq n : Lp ℂ p G.toWeakGridSpace.measure))
    (hSseq_fin : ∀ n,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (Sseq n))
    (hSseq_cost : ∀ n,
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) (Sseq n) ≤ Cbound)
    (hpartial_tendsto : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      Filter.Tendsto (fun n : ℕ => partialFun n z) Filter.atTop (𝓝 (h z)))
    (hSseq_supp : ∀ n k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ((Sseq n).block k).coeff Q ≠ 0 → SupportProp k Q)
    (hSseq_pos : ∀ n,
      SouzaConePositiveRepresentation G s p hs hp hp_top (Sseq n)) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) h
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤ Cbound ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 → SupportProp k Q) ∧
        SouzaConePositiveRepresentation G s p hs hp hp_top S := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let μ := G.toWeakGridSpace.measure
  let yseqLp : ℕ → Lp ℂ p μ := fun n => (yseq n : Lp ℂ p μ)
  rcases WeakGridSpace.exists_strongly_convergent_subseq_of_uniform_pqCost
      (G := G.toWeakGridSpace) (s := s) (p := p) (u := ∞) (q := q)
      hp_top hs le_top A
      (souza_assumptionG2 G s p q hs hp hp_top)
      (souza_assumptionA5 G s p hs hp hp_top)
      Sseq hCbound_nonneg hSseq_fin hSseq_cost with
    ⟨φ, hφ, yLimLp, S, hmemLim, hSfin, hScost, hy_tendsto, hcoeff_lim, hatom_lim⟩
  have hy_tendsto_lp :
      Filter.Tendsto
        (fun n : ℕ => yseqLp (φ n))
        Filter.atTop
        (𝓝 yLimLp) := by
    change Filter.Tendsto
      (fun n : ℕ => (yseq (φ n) : Lp ℂ p G.toWeakGridSpace.measure))
      Filter.atTop
      (𝓝 yLimLp)
    exact hy_tendsto
  rcases exists_subseq_tendsto_ae_of_tendsto_Lp
      (μ := μ)
      (u := fun n : ℕ => yseqLp (φ n))
      (uLim := yLimLp)
      hy_tendsto_lp with
    ⟨ψ, hψ, hy_ae⟩
  have hyseq_rep_lp : ∀ n, yseqLp n =ᵐ[μ] partialFun n := by
    intro n
    change WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) (partialFun n)
      (yseq n : Lp ℂ p G.toWeakGridSpace.measure)
    exact hyseq_rep n
  have hcoe :
      ∀ᵐ z ∂μ, ∀ n : ℕ,
        yseqLp (φ (ψ n)) z = partialFun (φ (ψ n)) z :=
    ae_eq_partialFun_on_composed_subseq hyseq_rep_lp φ ψ
  have hy_subseq_tendsto :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        Filter.Tendsto
          (fun n : ℕ => partialFun (φ (ψ n)) z)
          Filter.atTop
          (𝓝 (yLimLp z)) := by
    filter_upwards [hy_ae, hcoe] with z hyz hcoez
    exact hyz.congr' <|
      Filter.Eventually.of_forall fun n : ℕ => hcoez n
  have hLimRep :
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) h yLimLp :=
    representsFunction_of_tendsto_subseq
      G p φ ψ hφ hψ hpartial_tendsto hy_subseq_tendsto
  have hsupp_lim : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (S.block k).coeff Q ≠ 0 → SupportProp k Q := by
    intro k Q hne
    have hex : ∃ n, ((Sseq (φ n)).block k).coeff Q ≠ 0 := by
      by_contra hall
      push_neg at hall
      have hzero :
          Filter.Tendsto (fun n => ((Sseq (φ n)).block k).coeff Q)
            Filter.atTop (𝓝 (0 : ℂ)) := by
        simpa [hall] using
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop (𝓝 (0 : ℂ)))
      exact hne (tendsto_nhds_unique (hcoeff_lim k Q) hzero)
    obtain ⟨n, hn⟩ := hex
    exact hSseq_supp (φ n) k Q hn
  have hpos_lim : SouzaConePositiveRepresentation G s p hs hp hp_top S := by
    intro k Q
    have hpos_n : ∀ n,
        SouzaConePositiveLevelBlock G s p hs hp hp_top ((Sseq (φ n)).block k) :=
      fun n => hSseq_pos (φ n) k
    constructor
    · exact complex_nonnegReal_isClosed.mem_of_tendsto (hcoeff_lim k Q)
        (Filter.Eventually.of_forall fun n => (hpos_n n Q).1)
    · obtain ⟨ψa, _hψa, hae_atom⟩ :=
        exists_subseq_tendsto_ae_of_tendsto_Lp
          (μ := μ)
          (u := fun n => WeakGridSpace.atomLp A
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (((Sseq (φ n)).block k).atom Q))
          (uLim := WeakGridSpace.atomLp A
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((S.block k).atom Q))
          (hatom_lim k Q)
      have hcoe_n : ∀ᵐ x ∂μ, ∀ n : ℕ,
          ((WeakGridSpace.atomLp A
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (((Sseq (φ (ψa n))).block k).atom Q)) : α → ℂ) x =
            A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (((Sseq (φ (ψa n))).block k).atom Q) x := by
        refine ae_all_iff.2 ?_
        intro n
        exact atomLp_representsFunction G.toWeakGridSpace A
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          (((Sseq (φ (ψa n))).block k).atom Q)
      have hcoe_lim :
          ((WeakGridSpace.atomLp A
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            ((S.block k).atom Q)) : α → ℂ) =ᵐ[μ]
            A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              ((S.block k).atom Q) :=
        atomLp_representsFunction G.toWeakGridSpace A
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          ((S.block k).atom Q)
      have hcone_n : ∀ᵐ x ∂μ, ∀ n : ℕ,
          ∃ d : ℝ, 0 ≤ d ∧
            A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (((Sseq (φ (ψa n))).block k).atom Q) x = (d : ℂ) := by
        refine ae_all_iff.2 ?_
        intro n
        exact (hpos_n (ψa n) Q).2
      filter_upwards [hae_atom, hcoe_n, hcoe_lim, hcone_n]
        with x hx_lim hx_coe hx_coelim hx_cone
      have htends :
          Filter.Tendsto
            (fun n => A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              (((Sseq (φ (ψa n))).block k).atom Q) x)
            Filter.atTop
            (𝓝 (A.toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
              ((S.block k).atom Q) x)) := by
        rw [← hx_coelim]
        exact hx_lim.congr fun n => hx_coe n
      exact complex_nonnegReal_isClosed.mem_of_tendsto htends
        (Filter.Eventually.of_forall fun n => hx_cone n)
  exact ⟨⟨yLimLp, hmemLim⟩, S, hLimRep, hSfin, hScost, hsupp_lim, hpos_lim⟩

private theorem nonArchimedean_partialProducts_aestronglyMeasurable_pos
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    {Λ : Set ℕ} {t : ℕ → ℕ} {g : ℕ → α → ℂ}
    {N : ℝ} {f : α → ℂ}
    {x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q}
    {R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (x : Lp ℂ p G.toWeakGridSpace.measure)}
    (hN : 0 ≤ N)
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (hRcanon : SouzaCanonicalRepresentation G s p hs hp hp_top R)
    (hgPos : ∀ i ∈ Λ,
      SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i))
    (hPosTail : ∀ i ∈ Λ,
      ∃ C : ℝ≥0∞,
        SouzaPositivePointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        (∑' i : {i // i ∈ Λ},
          nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
            G β p qtilde hβ hp hp_top Λ t g Q i) ≤ ENNReal.ofReal N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun z => (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z)
        G.toWeakGridSpace.measure := by
  classical
  intro n
  obtain ⟨y, _S, hy_rep, _, _, _, _⟩ :=
    exists_nonArchimedean_finite_representation_initial_pos
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
      hN Λ n t g f x R hRep hRfin hRcanon hgPos hPosTail hA hB
  exact ((MeasureTheory.Lp.memLp
    (y : Lp ℂ p G.toWeakGridSpace.measure)).aestronglyMeasurable).congr hy_rep

/-- Pointwise summability part of the infinite **positive** non-Archimedean
statement.  Mirrors `exists_nonArchimedeanInfinite_pointwise_hasSum`, with the
real tail seminorms replaced by the positive tail seminorms; the `L∞` input is
`souzaPositivePointwiseSelfsTailNorm_norm_ae_le`, available because the tail
`L∞` chain only tests against canonical atoms. -/
private theorem exists_nonArchimedeanInfinite_pointwise_hasSum_pos
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)] :
    ∃ Cgen : ℝ,
      0 ≤ Cgen ∧
      1 ≤ Cgen ∧
      ∀ (Λ : Set ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) (N : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
          0 ≤ N →
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) f
            (x : Lp ℂ p G.toWeakGridSpace.measure) →
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
          SouzaCanonicalRepresentation G s p hs hp hp_top R →
          (∀ i ∈ Λ,
            SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i)) →
          (∀ i ∈ Λ,
            ∃ C : ℝ≥0∞,
              SouzaPositivePointwiseSelfsTailBound
                G β p qtilde hβ hp hp_top (t i) (g i) C) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            (R.block k).coeff Q ≠ 0 →
              (∑' i : {i // i ∈ Λ},
                nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
                  G β p qtilde hβ hp hp_top Λ t g Q i) ≤ ENNReal.ofReal N) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
            i ∈ Λ →
              (R.block k).coeff Q ≠ 0 →
                goodGridLevelCellMeetsSupport G Q (g i) →
                  t i ≤ k) →
          ∃ h : α → ℂ,
            ∃ absSum : α → ℝ,
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                f z ≠ 0 →
                  HasSum
                    (fun i : {i // i ∈ Λ} => ‖g i.1 z‖)
                    (absSum z) ∧
                  absSum z ≤ Cgen * N) ∧
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                HasSum
                  (fun i : {i // i ∈ Λ} => g i.1 z * f z)
                  (h z)) ∧
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                ‖h z‖ ≤ Cgen * N * ‖f z‖) ∧
              ∃ hmem : MemLp h p G.toWeakGridSpace.measure,
                ‖MemLp.toLp h hmem‖ ≤
                  Cgen * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖ := by
  classical
  let K : ℝ :=
    souzaBesovLpLocalEmbeddingConstant G β p qtilde *
      (2 * souzaAmbientRestrictionMultiplierConstant G β p + 1)
  let Cgen : ℝ := max 1 K
  refine ⟨Cgen, ?_, ?_, ?_⟩
  · exact le_trans zero_le_one (le_max_left 1 K)
  · exact le_max_left 1 K
  · intro Λ t g N f x R hN hRep hRfin hRcanon hgPos hPosTail hA hB
    let h : α → ℂ := fun z => ∑' i : {i // i ∈ Λ}, g i.1 z * f z
    let absSum : α → ℝ := fun z => ∑' i : {i // i ∈ Λ}, ‖g i.1 z‖
    have hK_nonneg : 0 ≤ K := by
      have hlocal := souzaBesovLpLocalEmbeddingConstant_nonneg G β p qtilde
      have hamb := souzaAmbientRestrictionMultiplierConstant_nonneg G β p hp hp_top
      have hmiddle : 0 ≤ 2 * souzaAmbientRestrictionMultiplierConstant G β p + 1 := by
        linarith
      exact mul_nonneg hlocal hmiddle
    have hK_le_Cgen : K ≤ Cgen := le_max_right 1 K
    have hbound_ae :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          ∀ i : {i // i ∈ Λ},
            souzaPositivePointwiseSelfsTailNorm
                G β p qtilde hβ hp hp_top (t i.1) (g i.1) ≠ ∞ →
              ‖g i.1 z‖ ≤ K *
                (souzaPositivePointwiseSelfsTailNorm
                  G β p qtilde hβ hp hp_top (t i.1) (g i.1)).toReal := by
      refine ae_all_iff.2 ?_
      intro i
      by_cases hfin_i : souzaPositivePointwiseSelfsTailNorm
          G β p qtilde hβ hp hp_top (t i.1) (g i.1) ≠ ∞
      · filter_upwards [souzaPositivePointwiseSelfsTailNorm_norm_ae_le
          G β p qtilde hβ hp hp_top hβ_lt_inv hfin_i] with z hz _hfin
        simpa [K] using hz
      · exact Filter.Eventually.of_forall fun z hfin' => absurd hfin' hfin_i
    have hactive_ae :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          f z ≠ 0 →
            ∃ k, ∃ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              z ∈ Q.1 ∧ (R.block k).coeff Q ≠ 0 :=
      exists_active_cell_of_representsFunction_ne_zero_ae
        G s p q hs hp hp_top x R hRep
    have habs_ae :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          f z ≠ 0 →
            HasSum
              (fun i : {i // i ∈ Λ} => ‖g i.1 z‖)
              (absSum z) ∧
            absSum z ≤ Cgen * N := by
      filter_upwards [hbound_ae, hactive_ae] with z hbound_z hactive_z hfz
      rcases hactive_z hfz with ⟨k, Q, hzQ, hQcoeff⟩
      rcases hasSum_norm_of_mem_active_pos
          G β p qtilde hβ hp hp_top
          (Q := Q) (z := z) (K := K) (N := N)
          hK_nonneg hN hzQ hbound_z (hA k Q hQcoeff) with
        ⟨hAbs, hAbs_le⟩
      refine ⟨by simpa [absSum] using hAbs, ?_⟩
      calc
        absSum z ≤ K * N := by simpa [absSum] using hAbs_le
        _ ≤ Cgen * N := mul_le_mul_of_nonneg_right hK_le_Cgen hN
    have hseries_ae :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          HasSum
            (fun i : {i // i ∈ Λ} => g i.1 z * f z)
            (h z) := by
      filter_upwards [habs_ae] with z habs_z
      by_cases hfz : f z = 0
      · simpa [h, hfz] using
          (hasSum_zero : HasSum (fun _ : {i // i ∈ Λ} => (0 : ℂ)) 0)
      · rcases habs_z hfz with ⟨hAbs, _hAbs_le⟩
        have hsummable_norm :
            Summable (fun i : {i // i ∈ Λ} => ‖g i.1 z‖) :=
          hAbs.summable
        have hsummable_g :
            Summable (fun i : {i // i ∈ Λ} => g i.1 z) :=
          hsummable_norm.of_norm
        exact (hsummable_g.mul_right (f z)).hasSum
    have hnorm_ae :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          ‖h z‖ ≤ Cgen * N * ‖f z‖ := by
      filter_upwards [habs_ae] with z habs_z
      by_cases hfz : f z = 0
      · have hzsum : h z = 0 := by simp [h, hfz]
        simp [hzsum, hfz]
      · rcases habs_z hfz with ⟨hAbs, hAbs_le⟩
        have hsummable_norm :
            Summable (fun i : {i // i ∈ Λ} => ‖g i.1 z‖) :=
          hAbs.summable
        have hsummable_prod_norm :
            Summable (fun i : {i // i ∈ Λ} => ‖g i.1 z * f z‖) := by
          simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using
            hsummable_norm.mul_right ‖f z‖
        have hnorm_le :
            ‖h z‖ ≤ ∑' i : {i // i ∈ Λ}, ‖g i.1 z * f z‖ := by
          simpa [h] using norm_tsum_le_tsum_norm hsummable_prod_norm
        have htsum_prod :
            (∑' i : {i // i ∈ Λ}, ‖g i.1 z * f z‖) =
              absSum z * ‖f z‖ := by
          simpa [absSum, norm_mul, mul_comm, mul_left_comm, mul_assoc] using
            (hsummable_norm.tsum_mul_right ‖f z‖)
        calc
          ‖h z‖ ≤ ∑' i : {i // i ∈ Λ}, ‖g i.1 z * f z‖ := hnorm_le
          _ = absSum z * ‖f z‖ := htsum_prod
          _ ≤ (Cgen * N) * ‖f z‖ :=
            mul_le_mul_of_nonneg_right hAbs_le (norm_nonneg _)
          _ = Cgen * N * ‖f z‖ := by ring
    have hpartial_meas :
        ∀ n : ℕ,
          AEStronglyMeasurable
            (fun z => (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z)
            G.toWeakGridSpace.measure :=
      nonArchimedean_partialProducts_aestronglyMeasurable_pos
        G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
        hN hRep hRfin hRcanon hgPos hPosTail hA hB
    have hpartial_tendsto :
        ∀ᵐ z ∂G.toWeakGridSpace.measure,
          Filter.Tendsto
            (fun n : ℕ =>
              (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z)
            Filter.atTop (𝓝 (h z)) := by
      filter_upwards [hseries_ae] with z hseries_z
      exact tendsto_nonArchimedean_partial_sums_of_hasSum g f h hseries_z
    have hh_meas : AEStronglyMeasurable h G.toWeakGridSpace.measure :=
      aestronglyMeasurable_of_tendsto_ae Filter.atTop hpartial_meas hpartial_tendsto
    rcases memLp_and_norm_le_of_ae_norm_le_mul_representsFunction
        G p hRep hh_meas hnorm_ae with
      ⟨hmem, hmem_norm⟩
    exact ⟨h, absSum, habs_ae, hseries_ae, hnorm_ae, hmem, hmem_norm⟩

/-- Besov-representation part of the infinite positive statement: finite
positive truncations with uniform cost, compactness, and identification of the
limit, carrying the support witness and conditional cone positivity. -/
private theorem exists_nonArchimedeanInfinite_besov_representation_pos
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)]
    {Cgen N : ℝ} (hN : 0 ≤ N)
    (hCgen_nonneg : 0 ≤ Cgen)
    (hCrep_le_Cgen :
      nonArchimedeanPositiveRepresentationConstant G s β p ≤ Cgen)
    (Λ : Set ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ)
    (f h : α → ℂ)
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (hRcanon : SouzaCanonicalRepresentation G s p hs hp hp_top R)
    (hgPos : ∀ i ∈ Λ,
      SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i))
    (hPosTail : ∀ i ∈ Λ,
      ∃ C : ℝ≥0∞,
        SouzaPositivePointwiseSelfsTailBound
          G β p qtilde hβ hp hp_top (t i) (g i) C)
    (hA : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        (∑' i : {i // i ∈ Λ},
          nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
            G β p qtilde hβ hp hp_top Λ t g Q i) ≤ ENNReal.ofReal N)
    (hB : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q (g i) →
            t i ≤ k)
    (hseries : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      HasSum
        (fun i : {i // i ∈ Λ} => g i.1 z * f z)
        (h z)) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) h
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          Cgen * N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 →
            ∃ i ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1), g i z ≠ 0) ∧
        (SouzaPositiveRepresentation G s p hs hp hp_top R →
          SouzaConePositiveRepresentation G s p hs hp hp_top S) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let μ := G.toWeakGridSpace.measure
  let partialFun : ℕ → α → ℂ := fun n z =>
    (∑ i ∈ nonArchimedeanLambdaInitial Λ n, g i z) * f z
  have hpq_nonneg : 0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
    WeakGridSpace.LpGridRepresentation.pqCost_nonneg R
  have hfiniteRep : ∀ n,
      ∃ y : WeakGridSpace.BesovishSpace A q,
      ∃ S : WeakGridSpace.LpGridRepresentation A
          (y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) (partialFun n)
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          Cgen * N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 →
            ∃ i ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1), g i z ≠ 0) ∧
        (SouzaPositiveRepresentation G s p hs hp hp_top R →
          SouzaConePositiveRepresentation G s p hs hp hp_top S) := by
    intro n
    obtain ⟨y, S, hy_rep, hS_fin, hS_cost, hS_supp, hS_pos⟩ :=
      exists_nonArchimedean_finite_representation_initial_pos
        G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
        hN Λ n t g f x R hRep hRfin hRcanon hgPos hPosTail hA hB
    refine ⟨y, S, by simpa [partialFun] using hy_rep, hS_fin, ?_, hS_supp, hS_pos⟩
    refine hS_cost.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCrep_le_Cgen hN) hpq_nonneg
  let yseq : ℕ → WeakGridSpace.BesovishSpace A q := fun n =>
    Classical.choose (hfiniteRep n)
  let Sseq : ∀ n, WeakGridSpace.LpGridRepresentation A
      (yseq n : Lp ℂ p G.toWeakGridSpace.measure) := fun n =>
    Classical.choose (Classical.choose_spec (hfiniteRep n))
  have hyseq_rep : ∀ n,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (partialFun n)
        (yseq n : Lp ℂ p G.toWeakGridSpace.measure) := fun n =>
    (Classical.choose_spec (Classical.choose_spec (hfiniteRep n))).1
  have hSseq_fin : ∀ n,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (Sseq n) := fun n =>
    (Classical.choose_spec (Classical.choose_spec (hfiniteRep n))).2.1
  have hSseq_cost : ∀ n,
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) (Sseq n) ≤
        Cgen * N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R := fun n =>
    (Classical.choose_spec (Classical.choose_spec (hfiniteRep n))).2.2.1
  have hSseq_supp : ∀ n k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ((Sseq n).block k).coeff Q ≠ 0 →
        ∃ i ∈ Λ, ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1), g i z ≠ 0 :=
    fun n =>
    (Classical.choose_spec (Classical.choose_spec (hfiniteRep n))).2.2.2.1
  have hSseq_pos : SouzaPositiveRepresentation G s p hs hp hp_top R → ∀ n,
      SouzaConePositiveRepresentation G s p hs hp hp_top (Sseq n) :=
    fun hRpos n =>
    (Classical.choose_spec (Classical.choose_spec (hfiniteRep n))).2.2.2.2 hRpos
  have hCbound_nonneg :
      0 ≤ Cgen * N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
    mul_nonneg (mul_nonneg hCgen_nonneg hN) hpq_nonneg
  have hpartial_tendsto :
      ∀ᵐ z ∂μ,
        Filter.Tendsto (fun n : ℕ => partialFun n z) Filter.atTop (𝓝 (h z)) := by
    filter_upwards [hseries] with z hseries_z
    exact tendsto_nonArchimedean_partial_sums_of_hasSum g f h hseries_z
  exact exists_limit_representation_of_finite_sequence_pos
    G s p q hs hp hp_top hCbound_nonneg
    yseq Sseq hyseq_rep hSseq_fin hSseq_cost hpartial_tendsto hSseq_supp hSseq_pos

/-- **Infinite positive non-Archimedean theorem (core form).**

Infinite-index analogue of `souzaNonArchimedeanPropertyPositiveCone_core`: the
multiplier family is indexed by an arbitrary set `Λ ⊆ ℕ`, the positive
condition A is stated as an `ℝ≥0∞`-valued `tsum` bound (no summability
witness needed), and the conclusions are those of the non-positive infinite
theorem **plus** the support witness `[ii]` and the conditional cone
positivity `[i]` of the limit representation. -/
theorem souzaNonArchimedeanPropertyPositiveConeInfinite_core
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q qtilde : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ qtilde)] :
    ∃ Cgen : ℝ,
      0 ≤ Cgen ∧
      1 ≤ Cgen ∧
      ∀ (Λ : Set ℕ) (t : ℕ → ℕ) (g : ℕ → α → ℂ) (N : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
          0 ≤ N →
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) f
            (x : Lp ℂ p G.toWeakGridSpace.measure) →
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
          SouzaCanonicalRepresentation G s p hs hp hp_top R →
          (∀ i ∈ Λ,
            SouzaPositiveFunction G β p qtilde hβ hp hp_top (g i)) →
          (∀ i ∈ Λ,
            ∃ C : ℝ≥0∞,
              SouzaPositivePointwiseSelfsTailBound
                G β p qtilde hβ hp hp_top (t i) (g i) C) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            (R.block k).coeff Q ≠ 0 →
              (∑' i : {i // i ∈ Λ},
                nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
                  G β p qtilde hβ hp hp_top Λ t g Q i) ≤ ENNReal.ofReal N) →
          (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
            i ∈ Λ →
              (R.block k).coeff Q ≠ 0 →
                goodGridLevelCellMeetsSupport G Q (g i) →
                  t i ≤ k) →
          ∃ h : α → ℂ,
            ∃ absSum : α → ℝ,
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                f z ≠ 0 →
                  HasSum
                    (fun i : {i // i ∈ Λ} => ‖g i.1 z‖)
                    (absSum z) ∧
                  absSum z ≤ Cgen * N) ∧
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                HasSum
                  (fun i : {i // i ∈ Λ} => g i.1 z * f z)
                  (h z)) ∧
              (∀ᵐ z ∂G.toWeakGridSpace.measure,
                ‖h z‖ ≤ Cgen * N * ‖f z‖) ∧
              (∃ hmem : MemLp h p G.toWeakGridSpace.measure,
                ‖MemLp.toLp h hmem‖ ≤
                  Cgen * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖) ∧
              ∃ y : WeakGridSpace.BesovishSpace
                  (souzaAtomFamily G s p hs hp hp_top) q,
                ∃ S : WeakGridSpace.LpGridRepresentation
                    (souzaAtomFamily G s p hs hp hp_top)
                    (y : Lp ℂ p G.toWeakGridSpace.measure),
                  WeakGridSpace.RepresentsFunction
                    (G := G.toWeakGridSpace) (p := p) h
                    (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
                  WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
                    Cgen * N *
                      WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
                  (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
                    (S.block k).coeff Q ≠ 0 →
                      ∃ i ∈ Λ,
                        ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1),
                          g i z ≠ 0) ∧
                  (SouzaPositiveRepresentation G s p hs hp hp_top R →
                    SouzaConePositiveRepresentation G s p hs hp hp_top S) := by
  classical
  rcases exists_nonArchimedeanInfinite_pointwise_hasSum_pos
      G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top with
    ⟨Cpoint, hCpoint_nonneg, hCpoint_one_le, hpointwise⟩
  let Crep : ℝ := nonArchimedeanPositiveRepresentationConstant G s β p
  have hCrep_nonneg : 0 ≤ Crep :=
    nonArchimedeanPositiveRepresentationConstant_nonneg G s β p hp hp_top
  let Cgen : ℝ := max Cpoint Crep
  have hCpoint_le_Cgen : Cpoint ≤ Cgen := le_max_left _ _
  have hCrep_le_Cgen : Crep ≤ Cgen := le_max_right _ _
  have hCgen_nonneg : 0 ≤ Cgen := le_trans hCpoint_nonneg hCpoint_le_Cgen
  have hCgen_one_le : 1 ≤ Cgen := le_trans hCpoint_one_le hCpoint_le_Cgen
  refine ⟨Cgen, hCgen_nonneg, hCgen_one_le, ?_⟩
  intro Λ t g N f x R hN hRep hRfin hRcanon hgPos hPosTail hA hB
  rcases hpointwise Λ t g N f x R hN hRep hRfin hRcanon hgPos hPosTail hA hB with
    ⟨h, absSum, habs, hseries, hnorm, hmem⟩
  have habs' :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        f z ≠ 0 →
          HasSum
            (fun i : {i // i ∈ Λ} => ‖g i.1 z‖)
            (absSum z) ∧
          absSum z ≤ Cgen * N := by
    filter_upwards [habs] with z hz hfz
    rcases hz hfz with ⟨hsum, hle⟩
    exact ⟨hsum, hle.trans (mul_le_mul_of_nonneg_right hCpoint_le_Cgen hN)⟩
  have hnorm' :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        ‖h z‖ ≤ Cgen * N * ‖f z‖ := by
    filter_upwards [hnorm] with z hz
    calc
      ‖h z‖ ≤ Cpoint * N * ‖f z‖ := hz
      _ ≤ Cgen * N * ‖f z‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCpoint_le_Cgen hN) (norm_nonneg _)
  rcases hmem with ⟨hmemLp, hmemNorm⟩
  have hmem' :
      ∃ hmem : MemLp h p G.toWeakGridSpace.measure,
        ‖MemLp.toLp h hmem‖ ≤
          Cgen * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖ := by
    refine ⟨hmemLp, ?_⟩
    calc
      ‖MemLp.toLp h hmemLp‖ ≤
          Cpoint * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖ := hmemNorm
      _ ≤ Cgen * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCpoint_le_Cgen hN) (norm_nonneg _)
  refine ⟨h, absSum, habs', hseries, hnorm', hmem', ?_⟩
  exact exists_nonArchimedeanInfinite_besov_representation_pos
    G s β p q qtilde hs hβ hβs hβ_lt_inv hp hp_top
    hN hCgen_nonneg hCrep_le_Cgen Λ t g f h x R
    hRep hRfin hRcanon hgPos hPosTail hA hB hseries

end

end GoodGridSpace
