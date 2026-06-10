import BesovSpacesGoodGrid.GoodGrid.Multipliers.NonArchimedeanPropertyPositiveStandalone

/-!
# Strongly regular domains and Pointwise Multipliers I

This file formalizes the subsection *Strongly regular domains* (`srd`) of the
paper *Besov-ish spaces through atomic decomposition*:

* the definition of an `(a, K, k₁)`-**strongly regular domain** `Ω`: inside
  every grid cell `Q` of level at least `k₁`, the intersection `Q ∩ Ω` is an
  exactly disjoint countable union of grid cells, with the level-by-level
  cost control `∑_{P ∈ ℱ^k} μ(P)^a ≤ K · μ(Q)^a`;
* Proposition `pos2`: if `Ω` is a `(1 − βp, K, k₁)`-strongly regular domain
  then the indicator of `Ω` satisfies the **positive** tail `selfs` bound
  `|1_Ω|_{B^{β+,k₁}_{p,∞,selfs}} ≤ K^{1/p}` — each product `1_Ω · a_Q` is
  exhibited as a positive Souza representation read off directly from the
  decomposition families;
* Proposition `pm1` (**Pointwise Multipliers I**): the non-Archimedean
  estimate for finite sums `∑ Θᵢ · 1_{Ωᵢ}` of weighted indicators of strongly
  regular domains, with the cost bound `Cgen2 · N`, the (a.e.) support
  localization of the output cells, and preservation of positivity.

## Main results

* `StronglyRegularDomain` (and the witness structure
  `StronglyRegularDecomposition`): the definition.
* `souzaPositiveSelfsTailBound_of_stronglyRegularDomain`: Proposition `pos2`.
* `souzaPositiveFunction_of_stronglyRegularDomain`: the indicator of a
  strongly regular domain lies in the positive Souza-Besov cone `B^{β+}_{p,∞}`.
* `souzaPointwiseMultipliersI`: Proposition `pm1`.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
The decomposition data witnessing strong regularity of `Ω` inside one grid
cell `Q`.

`family k` is the finite family `ℱ^k(Q ∩ Ω)` of level-`k` grid cells from the
paper's definition: the chosen cells are genuine level-`k` cells
(`family_subset`), together they tile `Q ∩ Ω` exactly (`cover`), distinct
chosen cells never overlap — even across different levels —
(`pairwise_disjoint`), and at every level the `a`-th powers of the cell
measures are controlled by the `a`-th power of the measure of the ambient
cell `Q` (`cost`).
-/
structure StronglyRegularDecomposition
    (G : GoodGridSpace (α := α)) (Ω : Set α) (a K : ℝ)
    (Q : GoodGridCell G) where
  /-- The family `ℱ^k(Q ∩ Ω)` of level-`k` cells used to tile `Q ∩ Ω`. -/
  family : ℕ → Finset (Set α)
  /-- Every chosen set is a genuine level-`k` grid cell. -/
  family_subset : ∀ k, family k ⊆ G.toWeakGridSpace.grid.partitions k
  /-- The chosen cells tile `Q ∩ Ω` exactly. -/
  cover : Q.cell ∩ Ω = ⋃ k, ⋃ P ∈ family k, (P : Set α)
  /-- Distinct chosen cells are disjoint, also across levels. -/
  pairwise_disjoint : ∀ k k' (P W : Set α), P ∈ family k → W ∈ family k' →
    P ≠ W → Disjoint P W
  /-- Level-by-level measure cost control with exponent `a`. -/
  cost : ∀ k, ∑ P ∈ family k, (G.grid.μ P).toReal ^ a ≤
    K * (G.grid.μ Q.cell).toReal ^ a

/--
A measurable set `Ω` is an `(a, K, k₁)`-**strongly regular domain** for the
good grid `G` when every grid cell `Q` of level at least `k₁` admits a
strongly regular decomposition of `Q ∩ Ω` with exponent `a` and cost
constant `K`.
-/
def StronglyRegularDomain
    (G : GoodGridSpace (α := α)) (Ω : Set α) (a K : ℝ) (k₁ : ℕ) : Prop :=
  MeasurableSet Ω ∧
    ∀ Q : GoodGridCell G, k₁ ≤ Q.level →
      Nonempty (StronglyRegularDecomposition G Ω a K Q)

/-- The level-`k₁` partition of a good grid is nonempty. -/
private theorem partitions_nonempty
    (G : GoodGridSpace (α := α)) (k₁ : ℕ) :
    (G.grid.grid.partitions k₁).Nonempty := by
  have huniv_mem : Set.univ ∈ G.grid.grid.partitions 0 := by
    rw [G.grid.grid.first_partition_eq_univ]
    exact Finset.mem_singleton_self _
  obtain ⟨z, _⟩ := G.grid.partition_nonempty 0 Set.univ huniv_mem
  have hz : z ∈ ⋃ P ∈ G.grid.grid.partitions k₁, P := by
    rw [G.grid.grid.covering k₁]
    exact Set.mem_univ z
  rcases Set.mem_iUnion₂.mp hz with ⟨P, hP, _⟩
  exact ⟨P, hP⟩

/-- The cost constant of a strongly regular domain is automatically
nonnegative. -/
theorem StronglyRegularDomain.nonneg_K
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a K : ℝ} {k₁ : ℕ}
    (hΩ : StronglyRegularDomain G Ω a K k₁) : 0 ≤ K := by
  obtain ⟨P, hP⟩ := partitions_nonempty G k₁
  obtain ⟨D⟩ := hΩ.2 ⟨k₁, P, hP⟩ le_rfl
  have hcost := D.cost 0
  have hsum_nonneg :
      0 ≤ ∑ W ∈ D.family 0, (G.grid.μ W).toReal ^ a :=
    Finset.sum_nonneg fun W _ => Real.rpow_nonneg ENNReal.toReal_nonneg a
  have hμpos :
      0 < (G.grid.μ (⟨k₁, P, hP⟩ : GoodGridCell G).cell).toReal ^ a :=
    Real.rpow_pos_of_pos
      (ENNReal.toReal_pos (GoodGridCell.measure_pos _).ne'
        (GoodGridCell.measure_ne_top _)) a
  nlinarith [le_trans hsum_nonneg hcost]

/-- A set can be a grid cell at only one level: cells at strictly deeper
levels are strictly smaller in measure, so they can never coincide with a
shallower cell. -/
private theorem grid_level_eq_of_mem_mem
    (G : GoodGridSpace (α := α)) {k k' : ℕ} {P : Set α}
    (hP : P ∈ G.grid.grid.partitions k)
    (hP' : P ∈ G.grid.grid.partitions k') :
    k = k' := by
  by_contra hne
  rcases Nat.lt_or_ge k k' with h | h
  · exact goodGridCell_not_subset_of_level_lt G ⟨k', P, hP'⟩ ⟨P, hP⟩ h
      subset_rfl
  · have h' : k' < k := lt_of_le_of_ne h fun e => hne e.symm
    exact goodGridCell_not_subset_of_level_lt G ⟨k, P, hP⟩ ⟨P, hP'⟩ h'
      subset_rfl

/-- A finite sum of `indicatorConstLp`'s of pairwise disjoint sets is the
`indicatorConstLp` of their union. -/
private theorem sum_indicatorConstLp_disjoint
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {ι : Type*} (E : ι → Set α)
    (hmeas : ∀ i, MeasurableSet (E i))
    (hfin : ∀ i, G.toWeakGridSpace.measure (E i) ≠ ∞)
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (S : Finset ι) (v : ℂ)
    (hUm : MeasurableSet (⋃ i ∈ S, E i))
    (hUf : G.toWeakGridSpace.measure (⋃ i ∈ S, E i) ≠ ∞) :
    (∑ i ∈ S, MeasureTheory.indicatorConstLp
        (μ := G.toWeakGridSpace.measure) p (hmeas i) (hfin i) v) =
      MeasureTheory.indicatorConstLp
        (μ := G.toWeakGridSpace.measure) p hUm hUf v := by
  classical
  apply Lp.ext
  have hsum :
      WeakGridSpace.RepresentsFunction (G := G.toWeakGridSpace) (p := p)
        (fun z => ∑ i ∈ S, (E i).indicator (fun _ => v) z)
        (∑ i ∈ S, MeasureTheory.indicatorConstLp
          (μ := G.toWeakGridSpace.measure) p (hmeas i) (hfin i) v) :=
    WeakGridSpace.representsFunction_finset_sum S _ _
      (fun i _ => MeasureTheory.indicatorConstLp_coeFn)
  have hpt : ∀ z,
      (∑ i ∈ S, (E i).indicator (fun _ => v) z) =
        (⋃ i ∈ S, E i).indicator (fun _ => v) z := by
    intro z
    by_cases hz : z ∈ ⋃ i ∈ S, E i
    · rcases Set.mem_iUnion₂.mp hz with ⟨i₀, hi₀S, hzi₀⟩
      rw [Set.indicator_of_mem hz]
      rw [Finset.sum_eq_single i₀]
      · rw [Set.indicator_of_mem hzi₀]
      · intro j hjS hji
        have hzj : z ∉ E j := fun hzj =>
          Set.disjoint_left.mp (hdisj j i₀ hji) hzj hzi₀
        rw [Set.indicator_of_notMem hzj]
      · intro hi₀
        exact absurd hi₀S hi₀
    · rw [Set.indicator_of_notMem hz]
      refine Finset.sum_eq_zero fun i hiS => ?_
      have hzi : z ∉ E i := fun hzi =>
        hz (Set.mem_iUnion₂.mpr ⟨i, hiS, hzi⟩)
      rw [Set.indicator_of_notMem hzi]
  have hpt' :
      (fun z => ∑ i ∈ S, (E i).indicator (fun _ => v) z)
        =ᵐ[G.toWeakGridSpace.measure]
        (⋃ i ∈ S, E i).indicator (fun _ => v) :=
    Filter.Eventually.of_forall hpt
  exact hsum.trans
    (hpt'.trans MeasureTheory.indicatorConstLp_coeFn.symm)

/-- Proof-irrelevant set congruence for `indicatorConstLp`. -/
private theorem indicatorConstLp_congr_sets
    {μ' : Measure α} {p' : ℝ≥0∞} {u w : Set α}
    (hu : MeasurableSet u) (hμu : μ' u ≠ ∞)
    (hw : MeasurableSet w) (hμw : μ' w ≠ ∞)
    (c : ℂ) (huw : u = w) :
    MeasureTheory.indicatorConstLp (μ := μ') p' hu hμu c =
      MeasureTheory.indicatorConstLp (μ := μ') p' hw hμw c := by
  subst huw
  rfl

/--
`L^p` convergence of disjoint indicator pieces: the indicators of countably
many pairwise disjoint measurable sets of finite total measure sum, in `L^p`,
to the indicator of their union.

This is the convergence backbone of Proposition `pos2`: the level families of
a strongly regular decomposition tile `Q ∩ Ω`, and the corresponding atomic
blocks converge in `L^p` because the measure of the un-tiled remainder
shrinks to zero.
-/
private theorem hasSum_indicatorConstLp_iUnion
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (E : ℕ → Set α)
    (hmeas : ∀ k, MeasurableSet (E k))
    (hfin : ∀ k, G.toWeakGridSpace.measure (E k) ≠ ∞)
    (hdisj : ∀ k k', k ≠ k' → Disjoint (E k) (E k'))
    (v : ℂ)
    (hUm : MeasurableSet (⋃ k, E k))
    (hUf : G.toWeakGridSpace.measure (⋃ k, E k) ≠ ∞) :
    HasSum
      (fun k => MeasureTheory.indicatorConstLp
        (μ := G.toWeakGridSpace.measure) p (hmeas k) (hfin k) v)
      (MeasureTheory.indicatorConstLp
        (μ := G.toWeakGridSpace.measure) p hUm hUf v) := by
  classical
  have hp_ne_zero : p ≠ 0 :=
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hpt_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  -- Countable additivity, in real form.
  have htsum :
      (∑' k, G.toWeakGridSpace.measure (E k)) =
        G.toWeakGridSpace.measure (⋃ k, E k) :=
    (measure_iUnion (fun i j hij => hdisj i j hij) hmeas).symm
  have hμsum :
      HasSum (fun k => (G.toWeakGridSpace.measure (E k)).toReal)
        ((G.toWeakGridSpace.measure (⋃ k, E k)).toReal) := by
    have hne : (∑' k, G.toWeakGridSpace.measure (E k)) ≠ ∞ := by
      rw [htsum]; exact hUf
    have hsummable :
        Summable (fun k => (G.toWeakGridSpace.measure (E k)).toReal) :=
      ENNReal.summable_toReal hne
    have hval :
        (∑' k, (G.toWeakGridSpace.measure (E k)).toReal) =
          (G.toWeakGridSpace.measure (⋃ k, E k)).toReal := by
      rw [← htsum]
      exact (ENNReal.tsum_toReal_eq fun k => hfin k).symm
    simpa [hval] using hsummable.hasSum
  -- Distance from a partial sum to the limit, computed exactly.
  have hUs_m : ∀ s : Finset ℕ, MeasurableSet (⋃ k ∈ s, E k) := fun s =>
    s.measurableSet_biUnion (fun k _ => hmeas k)
  have hUs_sub : ∀ s : Finset ℕ, (⋃ k ∈ s, E k) ⊆ ⋃ k, E k := fun s =>
    Set.iUnion₂_subset fun k _ => Set.subset_iUnion E k
  have hUs_f : ∀ s : Finset ℕ,
      G.toWeakGridSpace.measure (⋃ k ∈ s, E k) ≠ ∞ := fun s =>
    ne_top_of_le_ne_top hUf (measure_mono (hUs_sub s))
  have hrest_m : ∀ s : Finset ℕ,
      MeasurableSet ((⋃ k, E k) \ ⋃ k ∈ s, E k) := fun s =>
    hUm.diff (hUs_m s)
  have hrest_f : ∀ s : Finset ℕ,
      G.toWeakGridSpace.measure ((⋃ k, E k) \ ⋃ k ∈ s, E k) ≠ ∞ := fun s =>
    ne_top_of_le_ne_top hUf (measure_mono Set.diff_subset)
  have hdist : ∀ s : Finset ℕ,
      dist
        (∑ k ∈ s, MeasureTheory.indicatorConstLp
          (μ := G.toWeakGridSpace.measure) p (hmeas k) (hfin k) v)
        (MeasureTheory.indicatorConstLp
          (μ := G.toWeakGridSpace.measure) p hUm hUf v) =
        ‖v‖ * (G.toWeakGridSpace.measure
          ((⋃ k, E k) \ ⋃ k ∈ s, E k)).toReal ^ (1 / p.toReal) := by
    intro s
    have hpartial :
        (∑ k ∈ s, MeasureTheory.indicatorConstLp
          (μ := G.toWeakGridSpace.measure) p (hmeas k) (hfin k) v) =
          MeasureTheory.indicatorConstLp
            (μ := G.toWeakGridSpace.measure) p (hUs_m s) (hUs_f s) v :=
      sum_indicatorConstLp_disjoint G p E hmeas hfin hdisj s v _ _
    have hsplit :
        MeasureTheory.indicatorConstLp
            (μ := G.toWeakGridSpace.measure) p hUm hUf v =
          MeasureTheory.indicatorConstLp
            (μ := G.toWeakGridSpace.measure) p (hUs_m s) (hUs_f s) v +
          MeasureTheory.indicatorConstLp
            (μ := G.toWeakGridSpace.measure) p (hrest_m s) (hrest_f s) v := by
      have hu :
          (⋃ k ∈ s, E k) ∪ ((⋃ k, E k) \ ⋃ k ∈ s, E k) = ⋃ k, E k :=
        Set.union_diff_cancel (hUs_sub s)
      have hd :
          Disjoint (⋃ k ∈ s, E k) ((⋃ k, E k) \ ⋃ k ∈ s, E k) :=
        Set.disjoint_sdiff_right
      calc
        MeasureTheory.indicatorConstLp
            (μ := G.toWeakGridSpace.measure) p hUm hUf v
            = MeasureTheory.indicatorConstLp
                (μ := G.toWeakGridSpace.measure) p
                ((hUs_m s).union (hrest_m s))
                (by rw [hu]; exact hUf) v :=
          indicatorConstLp_congr_sets hUm hUf _ _ v hu.symm
        _ = _ :=
          MeasureTheory.indicatorConstLp_disjoint_union
            (hUs_m s) (hrest_m s) (hUs_f s) (hrest_f s) hd v
    rw [dist_eq_norm, hpartial, hsplit]
    have hcancel :
        MeasureTheory.indicatorConstLp
            (μ := G.toWeakGridSpace.measure) p (hUs_m s) (hUs_f s) v -
          (MeasureTheory.indicatorConstLp
              (μ := G.toWeakGridSpace.measure) p (hUs_m s) (hUs_f s) v +
            MeasureTheory.indicatorConstLp
              (μ := G.toWeakGridSpace.measure) p (hrest_m s) (hrest_f s) v) =
          -(MeasureTheory.indicatorConstLp
              (μ := G.toWeakGridSpace.measure) p (hrest_m s) (hrest_f s) v) := by
      abel
    rw [hcancel, norm_neg,
      MeasureTheory.norm_indicatorConstLp hp_ne_zero hp_top]
    rfl
  -- The remainder measure tends to zero along the partial sums.
  have hμrest :
      Filter.Tendsto
        (fun s : Finset ℕ =>
          (G.toWeakGridSpace.measure ((⋃ k, E k) \ ⋃ k ∈ s, E k)).toReal)
        Filter.atTop (𝓝 0) := by
    have hμrest_eq : ∀ s : Finset ℕ,
        (G.toWeakGridSpace.measure ((⋃ k, E k) \ ⋃ k ∈ s, E k)).toReal =
          (G.toWeakGridSpace.measure (⋃ k, E k)).toReal -
            ∑ k ∈ s, (G.toWeakGridSpace.measure (E k)).toReal := by
      intro s
      have hdiff :
          G.toWeakGridSpace.measure ((⋃ k, E k) \ ⋃ k ∈ s, E k) =
            G.toWeakGridSpace.measure (⋃ k, E k) -
              G.toWeakGridSpace.measure (⋃ k ∈ s, E k) :=
        measure_diff (hUs_sub s) (hUs_m s).nullMeasurableSet (hUs_f s)
      have hbiUnion :
          G.toWeakGridSpace.measure (⋃ k ∈ s, E k) =
            ∑ k ∈ s, G.toWeakGridSpace.measure (E k) :=
        measure_biUnion_finset
          (fun i _ j _ hij => hdisj i j hij) (fun k _ => hmeas k)
      rw [hdiff, ENNReal.toReal_sub_of_le (measure_mono (hUs_sub s)) hUf,
        hbiUnion, ENNReal.toReal_sum (fun k _ => hfin k)]
    have hconst_sub :
        Filter.Tendsto
          (fun s : Finset ℕ =>
            (G.toWeakGridSpace.measure (⋃ k, E k)).toReal -
              ∑ k ∈ s, (G.toWeakGridSpace.measure (E k)).toReal)
          Filter.atTop
          (𝓝 ((G.toWeakGridSpace.measure (⋃ k, E k)).toReal -
            (G.toWeakGridSpace.measure (⋃ k, E k)).toReal)) :=
      Filter.Tendsto.sub tendsto_const_nhds hμsum
    rw [sub_self] at hconst_sub
    exact hconst_sub.congr fun s => (hμrest_eq s).symm
  -- Conclude: the distances tend to zero.
  rw [HasSum]
  rw [tendsto_iff_dist_tendsto_zero]
  have hpow :
      Filter.Tendsto
        (fun s : Finset ℕ =>
          (G.toWeakGridSpace.measure
            ((⋃ k, E k) \ ⋃ k ∈ s, E k)).toReal ^ (1 / p.toReal))
        Filter.atTop (𝓝 0) := by
    have h := hμrest.rpow_const
      (p := 1 / p.toReal) (Or.inr (by positivity))
    have h0 : (0 : ℝ) ^ (1 / p.toReal) = 0 :=
      Real.zero_rpow (by positivity)
    rw [h0] at h
    exact h
  have hfinal :
      Filter.Tendsto
        (fun s : Finset ℕ =>
          ‖v‖ * (G.toWeakGridSpace.measure
            ((⋃ k, E k) \ ⋃ k ∈ s, E k)).toReal ^ (1 / p.toReal))
        Filter.atTop (𝓝 0) := by
    simpa using hpow.const_mul ‖v‖
  exact hfinal.congr fun s => (hdist s).symm

/--
The level-`k` block of the representation built for Proposition `pos2`: on
the cells of the decomposition family it carries the coefficient
`Θ · μ(Q)^{β−1/p} / μ(P)^{β−1/p}` together with the canonical Souza atom, and
it vanishes elsewhere.
-/
private noncomputable def decompositionLevelBlock
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {Ω : Set α} {a K : ℝ} (Θ : ℝ) (Q : GoodGridCell G)
    (D : StronglyRegularDecomposition G Ω a K Q) (k : ℕ) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G β p hβ hp hp_top) k := by
  classical
  exact
  { coeff := fun P =>
      if P.1 ∈ D.family k then
        (((Θ * (G.grid.μ Q.cell).toReal ^ (β - (p.toReal)⁻¹)) /
            (G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹) : ℝ) : ℂ)
      else 0
    atom := fun P =>
      (((G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹) : ℝ) : ℂ)
    atom_mem := fun P => by
      change ‖(((G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹) : ℝ) : ℂ)‖ ≤
        (G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹)
      rw [Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)] }

/-- The blocks of the `pos2` construction are positive: real nonnegative
coefficients on canonical Souza atoms. -/
private theorem decompositionLevelBlock_positive
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {Ω : Set α} {a K : ℝ} {Θ : ℝ} (hΘ : 0 ≤ Θ) (Q : GoodGridCell G)
    (D : StronglyRegularDecomposition G Ω a K Q) (k : ℕ) :
    SouzaPositiveLevelBlock G β p hβ hp hp_top
      (decompositionLevelBlock G β p hβ hp hp_top Θ Q D k) := by
  classical
  intro P
  have hatom :
      (souzaAtomFamily G β p hβ hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k P)
          ((decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).atom P) =
        canonicalSouzaAtom G β p (goodGridCellOfLevelCell G P) := by
    funext z
    show P.1.indicator
        (fun _ => (((G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹) : ℝ) : ℂ)) z =
      canonicalSouzaAtom G β p (goodGridCellOfLevelCell G P) z
    by_cases hz : z ∈ P.1
    · rw [Set.indicator_of_mem hz]
      simp [canonicalSouzaAtom, goodGridCellOfLevelCell, hz]
    · rw [Set.indicator_of_notMem hz]
      simp [canonicalSouzaAtom, goodGridCellOfLevelCell, hz]
  by_cases hP : P.1 ∈ D.family k
  · refine ⟨(Θ * (G.grid.μ Q.cell).toReal ^ (β - (p.toReal)⁻¹)) /
        (G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹),
      div_nonneg
        (mul_nonneg hΘ (Real.rpow_nonneg ENNReal.toReal_nonneg _))
        (Real.rpow_nonneg ENNReal.toReal_nonneg _), ?_, hatom⟩
    show (if P.1 ∈ D.family k then _ else (0 : ℂ)) = _
    rw [if_pos hP]
  · refine ⟨0, le_rfl, ?_, hatom⟩
    show (if P.1 ∈ D.family k then _ else (0 : ℂ)) = ((0 : ℝ) : ℂ)
    rw [if_neg hP]
    simp

/-- The `pos2` block at level `k` realizes, in `L^p`, the indicator of the
union of the level-`k` tiles with the constant value `Θ · μ(Q)^{β−1/p}`. -/
private theorem decompositionLevelBlock_toLp
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {Ω : Set α} {a K : ℝ} (Θ : ℝ) (Q : GoodGridCell G)
    (D : StronglyRegularDecomposition G Ω a K Q) (k : ℕ)
    (hEm : MeasurableSet (⋃ P ∈ D.family k, (P : Set α)))
    (hEf : G.toWeakGridSpace.measure (⋃ P ∈ D.family k, (P : Set α)) ≠ ∞) :
    (decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).toLp
        (souzaAtomFamily G β p hβ hp hp_top) =
      MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
        hEm hEf
        (((Θ * (G.grid.μ Q.cell).toReal ^ (β - (p.toReal)⁻¹) : ℝ)) : ℂ) := by
  classical
  apply Lp.ext
  have hpt : ∀ z,
      (decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).toFunLt
          (souzaAtomFamily G β p hβ hp hp_top) z =
        (⋃ P ∈ D.family k, (P : Set α)).indicator
          (fun _ =>
            (((Θ * (G.grid.μ Q.cell).toReal ^ (β - (p.toReal)⁻¹) : ℝ)) : ℂ))
          z := by
    intro z
    unfold WeakGridSpace.LevelBlock.toFunLt
    set v : ℝ := Θ * (G.grid.μ Q.cell).toReal ^ (β - (p.toReal)⁻¹) with hv
    have hterm : ∀ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        (decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).coeff P *
          (souzaAtomFamily G β p hβ hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k P)
            ((decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).atom P) z =
          if P.1 ∈ D.family k then P.1.indicator (fun _ => ((v : ℝ) : ℂ)) z
          else 0 := by
      intro P
      have htf :
          (souzaAtomFamily G β p hβ hp hp_top).toFunction
              (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k P)
              ((decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).atom P) z =
            P.1.indicator
              (fun _ => (((G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹) : ℝ) : ℂ)) z :=
        rfl
      have hcoeff :
          (decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).coeff P =
            if P.1 ∈ D.family k then
              ((v / (G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹) : ℝ) : ℂ)
            else 0 := rfl
      rw [htf, hcoeff]
      by_cases hP : P.1 ∈ D.family k
      · rw [if_pos hP, if_pos hP]
        by_cases hz : z ∈ P.1
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
          have haP_pos :
              0 < (G.grid.μ P.1).toReal ^ (β - (p.toReal)⁻¹) :=
            Real.rpow_pos_of_pos
              (ENNReal.toReal_pos
                (G.grid.positive_measure k P.1
                  (D.family_subset k hP)).ne'
                (by
                  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
                  exact MeasureTheory.measure_ne_top G.grid.μ P.1)) _
          rw [← Complex.ofReal_mul, div_mul_cancel₀ _ haP_pos.ne']
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
      · rw [if_neg hP, if_neg hP, zero_mul]
    rw [Finset.sum_congr rfl fun P _ => hterm P]
    by_cases hz : z ∈ ⋃ P ∈ D.family k, (P : Set α)
    · rcases Set.mem_iUnion₂.mp hz with ⟨P₀, hP₀F, hzP₀⟩
      have hP₀mem : P₀ ∈ G.toWeakGridSpace.grid.partitions k :=
        D.family_subset k hP₀F
      rw [Set.indicator_of_mem hz]
      rw [Finset.sum_eq_single
        (⟨P₀, hP₀mem⟩ : WeakGridSpace.LevelCell G.toWeakGridSpace k)]
      · rw [if_pos hP₀F, Set.indicator_of_mem hzP₀]
      · intro P _ hPne
        by_cases hPF : P.1 ∈ D.family k
        · rw [if_pos hPF]
          have hPne' : P.1 ≠ P₀ := fun he =>
            hPne (Subtype.ext he)
          have hzP : z ∉ P.1 := fun hzP =>
            Set.disjoint_left.mp
              (D.pairwise_disjoint k k P.1 P₀ hPF hP₀F hPne') hzP hzP₀
          rw [Set.indicator_of_notMem hzP]
        · rw [if_neg hPF]
      · intro hmem
        exact absurd (Finset.mem_attach _ _) hmem
    · rw [Set.indicator_of_notMem hz]
      refine Finset.sum_eq_zero fun P _ => ?_
      by_cases hPF : P.1 ∈ D.family k
      · rw [if_pos hPF]
        have hzP : z ∉ P.1 := fun hzP =>
          hz (Set.mem_iUnion₂.mpr ⟨P.1, hPF, hzP⟩)
        rw [Set.indicator_of_notMem hzP]
      · rw [if_neg hPF]
  have hpt' :
      (decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).toFunLt
          (souzaAtomFamily G β p hβ hp hp_top)
        =ᵐ[G.toWeakGridSpace.measure]
        (⋃ P ∈ D.family k, (P : Set α)).indicator
          (fun _ =>
            (((Θ * (G.grid.μ Q.cell).toReal ^ (β - (p.toReal)⁻¹) : ℝ)) : ℂ)) :=
    Filter.Eventually.of_forall hpt
  exact (WeakGridSpace.LevelBlock.coeFn_toLp _ _).trans
    (hpt'.trans MeasureTheory.indicatorConstLp_coeFn.symm)

/-- Level-by-level coefficient cost of the `pos2` blocks: at every level the
`p`-th power sum of the coefficients is at most `Θ^p · K`. -/
private theorem decompositionLevelBlock_coeff_sum_le
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {Ω : Set α} {K : ℝ} {Θ : ℝ} (hΘ : 0 ≤ Θ)
    (Q : GoodGridCell G)
    (D : StronglyRegularDecomposition G Ω (1 - β * p.toReal) K Q) (k : ℕ) :
    (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).coeff P‖ ^
          p.toReal) ≤
      Θ ^ p.toReal * K := by
  classical
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hμQ_pos : 0 < (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_pos (GoodGridCell.measure_pos Q).ne'
      (GoodGridCell.measure_ne_top Q)
  set r : ℝ := β - (p.toReal)⁻¹ with hr
  set μQ : ℝ := (G.grid.μ Q.cell).toReal with hμQ
  set F : Set α → ℝ := fun X =>
    if X ∈ D.family k then
      ((Θ * μQ ^ r) / (G.grid.μ X).toReal ^ r) ^ p.toReal
    else 0 with hF
  have hsummand : ∀ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ‖(decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).coeff P‖ ^
          p.toReal = F P.1 := by
    intro P
    by_cases hP : P.1 ∈ D.family k
    · have hcoeff :
          (decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).coeff P =
            (((Θ * μQ ^ r) / (G.grid.μ P.1).toReal ^ r : ℝ) : ℂ) := by
        show (if P.1 ∈ D.family k then _ else (0 : ℂ)) = _
        rw [if_pos hP]
      have hquot_nonneg :
          0 ≤ (Θ * μQ ^ r) / (G.grid.μ P.1).toReal ^ r :=
        div_nonneg
          (mul_nonneg hΘ (Real.rpow_nonneg ENNReal.toReal_nonneg _))
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      rw [hcoeff, Complex.norm_real, Real.norm_of_nonneg hquot_nonneg, hF]
      simp only [if_pos hP]
    · have hcoeff :
          (decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).coeff P =
            0 := by
        show (if P.1 ∈ D.family k then _ else (0 : ℂ)) = 0
        rw [if_neg hP]
      rw [hcoeff, hF]
      simp [hP, Real.zero_rpow hpt_pos.ne']
  rw [Finset.sum_congr rfl fun P _ => hsummand P]
  have hcoe :
      (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k, F P.1) =
        ∑ X ∈ G.toWeakGridSpace.grid.partitions k, F X :=
    Finset.sum_coe_sort (G.toWeakGridSpace.grid.partitions k) F
  rw [hcoe]
  have hfilter :
      (∑ X ∈ G.toWeakGridSpace.grid.partitions k, F X) =
        ∑ X ∈ D.family k,
          ((Θ * μQ ^ r) / (G.grid.μ X).toReal ^ r) ^ p.toReal := by
    rw [hF]
    rw [Finset.sum_ite_mem]
    congr 1
    exact Finset.inter_eq_right.mpr (D.family_subset k)
  rw [hfilter]
  have hterm : ∀ X ∈ D.family k,
      ((Θ * μQ ^ r) / (G.grid.μ X).toReal ^ r) ^ p.toReal =
        Θ ^ p.toReal * μQ ^ (β * p.toReal - 1) *
          (G.grid.μ X).toReal ^ (1 - β * p.toReal) := by
    intro X hX
    have hμX_pos : 0 < (G.grid.μ X).toReal :=
      ENNReal.toReal_pos
        (G.grid.positive_measure k X (D.family_subset k hX)).ne'
        (MeasureTheory.measure_ne_top G.grid.μ X)
    have hrpt : r * p.toReal = β * p.toReal - 1 := by
      rw [hr]
      field_simp
    rw [Real.div_rpow
      (mul_nonneg hΘ (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    rw [Real.mul_rpow hΘ (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    rw [← Real.rpow_mul hμQ_pos.le, ← Real.rpow_mul hμX_pos.le, hrpt]
    rw [div_eq_mul_inv, ← Real.rpow_neg hμX_pos.le]
    have hexp : -(β * p.toReal - 1) = 1 - β * p.toReal := by ring
    rw [hexp]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hfactor_nonneg : 0 ≤ Θ ^ p.toReal * μQ ^ (β * p.toReal - 1) :=
    mul_nonneg (Real.rpow_nonneg hΘ _) (Real.rpow_nonneg hμQ_pos.le _)
  calc
    Θ ^ p.toReal * μQ ^ (β * p.toReal - 1) *
        (∑ X ∈ D.family k, (G.grid.μ X).toReal ^ (1 - β * p.toReal))
        ≤ Θ ^ p.toReal * μQ ^ (β * p.toReal - 1) *
            (K * μQ ^ (1 - β * p.toReal)) :=
      mul_le_mul_of_nonneg_left (D.cost k) hfactor_nonneg
    _ = Θ ^ p.toReal * K *
          (μQ ^ (β * p.toReal - 1) * μQ ^ (1 - β * p.toReal)) := by ring
    _ = Θ ^ p.toReal * K := by
      have hzero : (β * p.toReal - 1) + (1 - β * p.toReal) = 0 := by ring
      rw [← Real.rpow_add hμQ_pos, hzero, Real.rpow_zero, mul_one]

/--
Core construction for Proposition `pos2`, with a nonnegative scalar weight
`Θ` built in.

Given a strongly regular decomposition of `Q ∩ Ω` with exponent `1 − βp`, the
product `Θ · 1_Ω · a_Q` (where `a_Q` is the canonical `(β,p)`-Souza atom on
`Q`) has a positive Souza representation whose coefficients at level `k` are
`Θ · (μ(P)/μ(Q))^{1/p−β}` on the cells `P ∈ ℱ^k`, and whose positive
`(p,∞)`-gauge is at most `Θ · K^{1/p}`.
-/
private theorem exists_souzaPositiveElement_indicator_mul_atom
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {Ω : Set α} {K : ℝ} (hK : 0 ≤ K)
    {Θ : ℝ} (hΘ : 0 ≤ Θ)
    (Q : GoodGridCell G)
    (D : StronglyRegularDecomposition G Ω (1 - β * p.toReal) K Q) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G β p hβ hp hp_top) ∞,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => (Θ : ℂ) * Ω.indicator (fun _ => (1 : ℂ)) z *
          canonicalSouzaAtom G β p Q z)
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      SouzaPositiveElement G β p ∞ hβ hp hp_top y ∧
      souzaPositiveNorm G β p ∞ hβ hp hp_top y ≤
        ENNReal.ofReal (Θ * K ^ (p.toReal)⁻¹) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.toWeakGridSpace.measure :=
    G.grid.isFinite
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  set r : ℝ := β - (p.toReal)⁻¹ with hr
  set v : ℝ := Θ * (G.grid.μ Q.cell).toReal ^ r with hv
  set A := souzaAtomFamily G β p hβ hp hp_top with hA
  -- The level tiles and their basic measure theory.
  set Ek : ℕ → Set α := fun k => ⋃ P ∈ D.family k, (P : Set α) with hEkdef
  have hEk_meas : ∀ k, MeasurableSet (Ek k) := fun k =>
    (D.family k).measurableSet_biUnion fun P hP =>
      G.grid.grid.measurable k P (D.family_subset k hP)
  have hEk_fin : ∀ k, G.toWeakGridSpace.measure (Ek k) ≠ ∞ := fun k =>
    MeasureTheory.measure_ne_top _ _
  have hEk_disj : ∀ k k', k ≠ k' → Disjoint (Ek k) (Ek k') := by
    intro k k' hkk'
    refine Set.disjoint_left.mpr ?_
    intro z hz hz'
    rcases Set.mem_iUnion₂.mp hz with ⟨P, hP, hzP⟩
    rcases Set.mem_iUnion₂.mp hz' with ⟨W, hW, hzW⟩
    by_cases hPW : P = W
    · subst hPW
      exact hkk'
        (grid_level_eq_of_mem_mem G
          (D.family_subset k hP) (D.family_subset k' hW))
    · exact Set.disjoint_left.mp
        (D.pairwise_disjoint k k' P W hP hW hPW) hzP hzW
  have hUm : MeasurableSet (⋃ k, Ek k) := MeasurableSet.iUnion hEk_meas
  have hUf : G.toWeakGridSpace.measure (⋃ k, Ek k) ≠ ∞ :=
    MeasureTheory.measure_ne_top _ _
  -- The candidate `L^p` element and its atomic representation.
  set yLp : Lp ℂ p G.toWeakGridSpace.measure :=
    MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
      hUm hUf ((v : ℝ) : ℂ) with hyLp
  have hBtoLp : ∀ k,
      (decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).toLp A =
        MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
          (hEk_meas k) (hEk_fin k) ((v : ℝ) : ℂ) := fun k =>
    decompositionLevelBlock_toLp G β p hβ hp hp_top Θ Q D k
      (hEk_meas k) (hEk_fin k)
  have hhasSum :
      HasSum
        (fun k =>
          (decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).toLp A)
        yLp := by
    have h := hasSum_indicatorConstLp_iUnion G p hp_top Ek
      hEk_meas hEk_fin hEk_disj ((v : ℝ) : ℂ) hUm hUf
    have heq :
        (fun k =>
          (decompositionLevelBlock G β p hβ hp hp_top Θ Q D k).toLp A) =
          fun k =>
            MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure)
              p (hEk_meas k) (hEk_fin k) ((v : ℝ) : ℂ) :=
      funext hBtoLp
    rw [heq]
    exact h
  set R : WeakGridSpace.LpGridRepresentation A yLp :=
    { block := fun k => decompositionLevelBlock G β p hβ hp hp_top Θ Q D k
      hasSum := hhasSum } with hRdef
  have hRpos : SouzaPositiveRepresentation G β p hβ hp hp_top R := fun k =>
    decompositionLevelBlock_positive G β p hβ hp hp_top hΘ Q D k
  have hlcp : ∀ k, R.levelCoeffPower k ≤ Θ ^ p.toReal * K := fun k =>
    decompositionLevelBlock_coeff_sum_le G β p hβ hp hp_top hΘ Q D k
  have hbound_real : ∀ k,
      (R.levelCoeffPower k) ^ (1 / p.toReal) ≤ Θ * K ^ (p.toReal)⁻¹ := by
    intro k
    have h1 :
        (R.levelCoeffPower k) ^ (1 / p.toReal) ≤
          (Θ ^ p.toReal * K) ^ (1 / p.toReal) :=
      Real.rpow_le_rpow
        (WeakGridSpace.LpGridRepresentation.levelCoeffPower_nonneg R k)
        (hlcp k) (by positivity)
    refine h1.trans_eq ?_
    rw [Real.mul_rpow (Real.rpow_nonneg hΘ _) hK,
      ← Real.rpow_mul hΘ, mul_one_div, div_self hpt_pos.ne',
      Real.rpow_one, one_div]
  have hcostENN :
      WeakGridSpace.LpGridRepresentation.pqCostENNReal (q := ∞) R ≤
        ENNReal.ofReal (Θ * K ^ (p.toReal)⁻¹) := by
    rw [WeakGridSpace.LpGridRepresentation.pqCostENNReal, if_pos rfl]
    refine sSup_le ?_
    rintro x ⟨k, rfl⟩
    exact ENNReal.ofReal_le_ofReal (hbound_real k)
  have hRfin :
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := ∞) R :=
    WeakGridSpace.LpGridRepresentation.finitePQCost_of_pqCostENNReal_le
      R le_top hcostENN
  have hymem : yLp ∈ WeakGridSpace.BesovishSpace A ∞ := ⟨R, hRfin⟩
  refine ⟨⟨yLp, hymem⟩, ?_, ⟨R, hRpos⟩, ?_⟩
  · -- It represents `Θ · 1_Ω · a_Q`.
    show (yLp : α → ℂ) =ᵐ[G.toWeakGridSpace.measure] _
    refine MeasureTheory.indicatorConstLp_coeFn.trans
      (Filter.Eventually.of_forall ?_)
    intro z
    show (⋃ k, Ek k).indicator (fun _ => ((v : ℝ) : ℂ)) z =
      (Θ : ℂ) * Ω.indicator (fun _ => (1 : ℂ)) z *
        canonicalSouzaAtom G β p Q z
    have hcover : (⋃ k, Ek k) = Q.cell ∩ Ω := D.cover.symm
    rw [hcover]
    by_cases hz : z ∈ Q.cell ∩ Ω
    · rw [Set.indicator_of_mem hz]
      obtain ⟨hzQ, hzΩ⟩ := hz
      rw [Set.indicator_of_mem hzΩ]
      have hatom :
          canonicalSouzaAtom G β p Q z =
            (((G.grid.μ Q.cell).toReal ^ r : ℝ) : ℂ) := by
        simp [canonicalSouzaAtom, hzQ, hr]
      rw [hatom, hv]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hz]
      by_cases hzQ : z ∈ Q.cell
      · have hzΩ : z ∉ Ω := fun hzΩ => hz ⟨hzQ, hzΩ⟩
        rw [Set.indicator_of_notMem hzΩ]
        ring
      · have hatom : canonicalSouzaAtom G β p Q z = 0 := by
          simp [canonicalSouzaAtom, hzQ]
        rw [hatom]
        ring
  · -- The positive gauge is controlled by the cost of `R`.
    exact sInf_le ⟨R, hRpos, hRfin, hcostENN⟩

/--
**Proposition `pos2` of the paper.**

If `Ω` is a `(1 − βp, K, k₁)`-strongly regular domain, then the indicator of
`Ω` satisfies the positive level-tail `selfs` bound
`|1_Ω|_{B^{β+,k₁}_{p,∞,selfs}} ≤ K^{1/p}`: for every grid cell `Q` of level
at least `k₁`, the product of `1_Ω` with the canonical `(β,p)`-Souza atom on
`Q` admits a positive Souza representation with positive `(p,∞)`-gauge at
most `K^{1/p}`.
-/
theorem souzaPositiveSelfsTailBound_of_stronglyRegularDomain
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {Ω : Set α} {K : ℝ} {k₁ : ℕ}
    (hΩ : StronglyRegularDomain G Ω (1 - β * p.toReal) K k₁) :
    SouzaPositivePointwiseSelfsTailBound G β p ∞ hβ hp hp_top k₁
      (Ω.indicator fun _ => (1 : ℂ))
      (ENNReal.ofReal (K ^ (p.toReal)⁻¹)) := by
  intro Q hQ
  obtain ⟨D⟩ := hΩ.2 Q hQ
  obtain ⟨y, hyrep, hypos, hynorm⟩ :=
    exists_souzaPositiveElement_indicator_mul_atom G β p hβ hp hp_top
      hΩ.nonneg_K (zero_le_one) Q D
  refine ⟨y, ?_, hypos, ?_⟩
  · refine hyrep.trans (Filter.Eventually.of_forall fun z => ?_)
    show ((1 : ℝ) : ℂ) * Ω.indicator (fun _ => (1 : ℂ)) z *
        canonicalSouzaAtom G β p Q z =
      Ω.indicator (fun _ => (1 : ℂ)) z * canonicalSouzaAtom G β p Q z
    push_cast
    ring
  · simpa using hynorm

/--
Weighted version of Proposition `pos2`: a nonnegative multiple `Θ · 1_Ω` of
the indicator of a `(1 − βp, K, k₁)`-strongly regular domain satisfies the
positive tail `selfs` bound with constant `Θ · K^{1/p}`.
-/
theorem souzaPositiveSelfsTailBound_smul_of_stronglyRegularDomain
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {Ω : Set α} {K : ℝ} {k₁ : ℕ}
    (hΩ : StronglyRegularDomain G Ω (1 - β * p.toReal) K k₁)
    {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    SouzaPositivePointwiseSelfsTailBound G β p ∞ hβ hp hp_top k₁
      (fun z => (Θ : ℂ) * Ω.indicator (fun _ => (1 : ℂ)) z)
      (ENNReal.ofReal (Θ * K ^ (p.toReal)⁻¹)) := by
  intro Q hQ
  obtain ⟨D⟩ := hΩ.2 Q hQ
  obtain ⟨y, hyrep, hypos, hynorm⟩ :=
    exists_souzaPositiveElement_indicator_mul_atom G β p hβ hp hp_top
      hΩ.nonneg_K hΘ Q D
  exact ⟨y, hyrep, hypos, hynorm⟩

/--
The indicator of a strongly regular domain, with any nonnegative weight,
lies in the positive Souza-Besov cone `B^{β+}_{p,∞}`.

The level-`k₁` cells tile the whole space, so `Θ · 1_Ω` is the finite sum of
the products `Θ · 1_{Q ∩ Ω}` over `Q ∈ 𝒫^{k₁}`, and each summand is a scaled
copy of the positive element produced for Proposition `pos2`.
-/
theorem souzaPositiveFunction_of_stronglyRegularDomain
    (G : GoodGridSpace (α := α)) (β : ℝ) (p : ℝ≥0∞)
    (hβ : 0 < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {Ω : Set α} {K : ℝ} {k₁ : ℕ}
    (hΩ : StronglyRegularDomain G Ω (1 - β * p.toReal) K k₁)
    {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    SouzaPositiveFunction G β p ∞ hβ hp hp_top
      (fun z => (Θ : ℂ) * Ω.indicator (fun _ => (1 : ℂ)) z) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.toWeakGridSpace.measure :=
    G.grid.isFinite
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  set A := souzaAtomFamily G β p hβ hp hp_top with hA
  -- One positive piece per level-`k₁` cell, with the weight rescaled so that
  -- the piece represents `Θ · 1_{X ∩ Ω}`.
  have hpiece : ∀ X : {X // X ∈ G.toWeakGridSpace.grid.partitions k₁},
      ∃ y : WeakGridSpace.BesovishSpace A ∞,
        WeakGridSpace.RepresentsFunction (G := G.toWeakGridSpace) (p := p)
          (fun z =>
            ((Θ * (G.grid.μ X.1).toReal ^ ((p.toReal)⁻¹ - β) : ℝ) : ℂ) *
              Ω.indicator (fun _ => (1 : ℂ)) z *
              canonicalSouzaAtom G β p ⟨k₁, X.1, X.2⟩ z)
          (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        SouzaPositiveElement G β p ∞ hβ hp hp_top y ∧
        souzaPositiveNorm G β p ∞ hβ hp hp_top y ≤
          ENNReal.ofReal
            ((Θ * (G.grid.μ X.1).toReal ^ ((p.toReal)⁻¹ - β)) *
              K ^ (p.toReal)⁻¹) := by
    intro X
    obtain ⟨D⟩ := hΩ.2 ⟨k₁, X.1, X.2⟩ le_rfl
    exact exists_souzaPositiveElement_indicator_mul_atom G β p hβ hp hp_top
      hΩ.nonneg_K
      (mul_nonneg hΘ (Real.rpow_nonneg ENNReal.toReal_nonneg _)) _ D
  choose y hyrep _hypos hynorm using hpiece
  -- Extract positive finite-cost representations of the pieces.
  have hrep : ∀ X : {X // X ∈ G.toWeakGridSpace.grid.partitions k₁},
      ∃ R : WeakGridSpace.LpGridRepresentation A
          (y X : Lp ℂ p G.toWeakGridSpace.measure),
        SouzaPositiveRepresentation G β p hβ hp hp_top R ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := ∞) R := by
    intro X
    have hfin : souzaPositiveNorm G β p ∞ hβ hp hp_top (y X) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hynorm X)
    obtain ⟨R, hRpos, hRfin, _⟩ :=
      exists_souzaPositiveRepresentation_pqCostENNReal_lt G β p ∞
        hβ hp hp_top (y X) hfin (ε := 1) zero_lt_one
    exact ⟨R, hRpos, hRfin⟩
  choose R hRpos hRfin using hrep
  -- Sum the pieces into one positive representation.
  obtain ⟨T, hTpos, _hTfin, _, _⟩ :=
    exists_souzaPositiveRepresentation_finset_sum G β p ∞ hβ hp hp_top
      (Finset.univ :
        Finset {X // X ∈ G.toWeakGridSpace.grid.partitions k₁})
      (fun X => (y X : Lp ℂ p G.toWeakGridSpace.measure)) R
      (fun X _ => hRpos X) (fun X _ => hRfin X)
  have hmem :
      (∑ X : {X // X ∈ G.toWeakGridSpace.grid.partitions k₁},
        (y X : Lp ℂ p G.toWeakGridSpace.measure)) ∈
        WeakGridSpace.BesovishSpace A ∞ :=
    Submodule.sum_mem _ fun X _ => (y X).2
  refine ⟨⟨_, hmem⟩, ?_, ⟨T, hTpos⟩⟩
  -- The sum represents `Θ · 1_Ω`, because the level-`k₁` cells tile `α`.
  unfold WeakGridSpace.RepresentsFunction
  have hsum :=
    WeakGridSpace.representsFunction_finset_sum
      (G := G.toWeakGridSpace) (p := p)
      (Finset.univ :
        Finset {X // X ∈ G.toWeakGridSpace.grid.partitions k₁})
      (fun X z =>
        ((Θ * (G.grid.μ X.1).toReal ^ ((p.toReal)⁻¹ - β) : ℝ) : ℂ) *
          Ω.indicator (fun _ => (1 : ℂ)) z *
          canonicalSouzaAtom G β p ⟨k₁, X.1, X.2⟩ z)
      (fun X => (y X : Lp ℂ p G.toWeakGridSpace.measure))
      (fun X _ => hyrep X)
  refine hsum.trans (Filter.Eventually.of_forall ?_)
  intro z
  show (∑ X : {X // X ∈ G.toWeakGridSpace.grid.partitions k₁},
      ((Θ * (G.grid.μ X.1).toReal ^ ((p.toReal)⁻¹ - β) : ℝ) : ℂ) *
        Ω.indicator (fun _ => (1 : ℂ)) z *
        canonicalSouzaAtom G β p ⟨k₁, X.1, X.2⟩ z) =
    (Θ : ℂ) * Ω.indicator (fun _ => (1 : ℂ)) z
  by_cases hzΩ : z ∈ Ω
  · rw [Set.indicator_of_mem hzΩ, mul_one]
    -- `z` lies in exactly one level-`k₁` cell.
    have hz : z ∈ ⋃ P ∈ G.grid.grid.partitions k₁, P := by
      rw [G.grid.grid.covering k₁]
      exact Set.mem_univ z
    rcases Set.mem_iUnion₂.mp hz with ⟨P₀, hP₀, hzP₀⟩
    have hμP₀_pos : 0 < (G.grid.μ P₀).toReal :=
      ENNReal.toReal_pos
        (G.grid.positive_measure k₁ P₀ hP₀).ne'
        (MeasureTheory.measure_ne_top G.grid.μ P₀)
    rw [Finset.sum_eq_single
      (⟨P₀, hP₀⟩ : {X // X ∈ G.toWeakGridSpace.grid.partitions k₁})]
    · have hatom :
          canonicalSouzaAtom G β p ⟨k₁, P₀, hP₀⟩ z =
            (((G.grid.μ P₀).toReal ^ (β - (p.toReal)⁻¹) : ℝ) : ℂ) := by
        simp [canonicalSouzaAtom, hzP₀]
      rw [hatom]
      have hwu :
          (G.grid.μ P₀).toReal ^ ((p.toReal)⁻¹ - β) *
            (G.grid.μ P₀).toReal ^ (β - (p.toReal)⁻¹) = 1 := by
        rw [← Real.rpow_add hμP₀_pos]
        have hzero : ((p.toReal)⁻¹ - β) + (β - (p.toReal)⁻¹) = 0 := by ring
        rw [hzero, Real.rpow_zero]
      calc
        ((Θ * (G.grid.μ P₀).toReal ^ ((p.toReal)⁻¹ - β) : ℝ) : ℂ) * 1 *
            (((G.grid.μ P₀).toReal ^ (β - (p.toReal)⁻¹) : ℝ) : ℂ)
            = ((Θ * ((G.grid.μ P₀).toReal ^ ((p.toReal)⁻¹ - β) *
                (G.grid.μ P₀).toReal ^ (β - (p.toReal)⁻¹)) : ℝ) : ℂ) := by
          push_cast
          ring
        _ = (Θ : ℂ) := by
          rw [hwu, mul_one]
    · intro X _ hXne
      have hXne' : X.1 ≠ P₀ := fun he => hXne (Subtype.ext he)
      have hzX : z ∉ X.1 := fun hzX =>
        Set.disjoint_left.mp
          (G.grid.grid.disjoint k₁ X.1 P₀ X.2 hP₀ hXne') hzX hzP₀
      have hatom : canonicalSouzaAtom G β p ⟨k₁, X.1, X.2⟩ z = 0 := by
        simp [canonicalSouzaAtom, hzX]
      rw [hatom, mul_zero]
    · intro hmem'
      exact absurd (Finset.mem_univ _) hmem'
  · rw [Set.indicator_of_notMem hzΩ, mul_zero]
    refine Finset.sum_eq_zero fun X _ => ?_
    rw [mul_zero, zero_mul]

/--
The weighted overlap cost of a family of strongly regular domains at one
cell: the sum of `Θ i · (K i)^{1/p}` over the indices in `Λ` whose domain
meets the cell.  This is the quantity bounded by `N` in condition A of
Proposition `pm1`.
-/
noncomputable def stronglyRegularOverlapCost
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (Λ : Finset ℕ) (Ω : ℕ → Set α) (K Θ : ℕ → ℝ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℝ := by
  classical
  exact ∑ i ∈ Λ,
    if (Q.1 ∩ Ω i).Nonempty then Θ i * (K i) ^ (p.toReal)⁻¹ else 0

/--
**Proposition `pm1` of the paper (Pointwise Multipliers I).**

There is a constant `Cgen2` with the following property.  Let `Ω i`, for `i`
in a finite set `Λ`, be `(1 − βp, K i, t i)`-strongly regular domains and let
`Θ i > 0` be weights.  Let `f` be represented by a finite-cost canonical
Souza representation `R` of `x` in `B^s_{p,q}` whose active cells satisfy

* **A.** on every active cell `Q`, the total weighted cost
  `∑_{i : Q ∩ Ω i ≠ ∅} Θ i · (K i)^{1/p}` is at most `N`;
* **B.** every active cell meeting `Ω i` has level at least `t i`.

Then the product `(∑ i, Θ i · 1_{Ω i}) · f` has a Souza representation `S`
with finite cost, `pqCost S ≤ Cgen2 · N · pqCost R`, and moreover

* **[i]** every active cell of `S` is, up to measure zero, contained in some
  `Ω i` with `i ∈ Λ`;
* **[ii]** if `R` is a positive representation then `S` is cone-positive (in
  particular, nonnegative coefficients are preserved).
-/
theorem souzaPointwiseMultipliersI
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cgen2 : ℝ,
      0 ≤ Cgen2 ∧
      ∀ (Λ : Finset ℕ) (t : ℕ → ℕ) (Ω : ℕ → Set α) (K Θ : ℕ → ℝ) (N : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
        0 ≤ N →
        (∀ i ∈ Λ,
          StronglyRegularDomain G (Ω i) (1 - β * p.toReal) (K i) (t i)) →
        (∀ i ∈ Λ, 0 < Θ i) →
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) f
          (x : Lp ℂ p G.toWeakGridSpace.measure) →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
        SouzaCanonicalRepresentation G s p hs hp hp_top R →
        -- Condition A: weighted cost of the domains meeting an active cell.
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (R.block k).coeff Q ≠ 0 →
            stronglyRegularOverlapCost G p Λ Ω K Θ Q ≤ N) →
        -- Condition B: active cells meeting `Ω i` are deep enough.
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
          i ∈ Λ →
            (R.block k).coeff Q ≠ 0 →
              (Q.1 ∩ Ω i).Nonempty →
                t i ≤ k) →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          ∃ S : WeakGridSpace.LpGridRepresentation
              (souzaAtomFamily G s p hs hp hp_top)
              (y : Lp ℂ p G.toWeakGridSpace.measure),
            WeakGridSpace.RepresentsFunction
              (G := G.toWeakGridSpace) (p := p)
              (fun z => (∑ i ∈ Λ,
                (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) * f z)
              (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
            WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
            WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
              Cgen2 * N *
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
            -- [i] support: active cells of `S` lie a.e. in some `Ω i`.
            (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
              (S.block k).coeff Q ≠ 0 →
                ∃ i ∈ Λ,
                  ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1),
                    z ∈ Ω i) ∧
            -- [ii] positivity is preserved.
            (SouzaPositiveRepresentation G s p hs hp hp_top R →
              SouzaConePositiveRepresentation G s p hs hp hp_top S) := by
  classical
  obtain ⟨Cgen, hCgen0, hCgen⟩ :=
    souzaNonArchimedeanPropertyPositiveCone G s β p q ∞
      hs hβ hβs hβ_lt_inv hp hp_top
  refine ⟨Cgen, hCgen0, ?_⟩
  intro Λ t Ω K Θ N f x R hN hSRD hΘpos hRep hRfin hRcanon hA hB
  -- The support of each weighted indicator is exactly its domain.
  have hsupp : ∀ i ∈ Λ,
      {z | (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z ≠ 0} = Ω i := by
    intro i hi
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hne
      by_contra hzΩ
      exact hne (by rw [Set.indicator_of_notMem hzΩ, mul_zero])
    · intro hzΩ
      rw [Set.indicator_of_mem hzΩ, mul_one]
      exact Complex.ofReal_ne_zero.mpr (hΘpos i hi).ne'
  have hgpos : ∀ i ∈ Λ,
      SouzaPositiveFunction G β p ∞ hβ hp hp_top
        (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) :=
    fun i hi =>
      souzaPositiveFunction_of_stronglyRegularDomain G β p hβ hp hp_top
        (hSRD i hi) (hΘpos i hi).le
  have htail : ∀ i ∈ Λ,
      ∃ C : ℝ≥0∞,
        SouzaPositivePointwiseSelfsTailBound G β p ∞ hβ hp hp_top (t i)
          (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) C :=
    fun i hi =>
      ⟨ENNReal.ofReal (Θ i * (K i) ^ (p.toReal)⁻¹),
        souzaPositiveSelfsTailBound_smul_of_stronglyRegularDomain
          G β p hβ hp hp_top (hSRD i hi) (hΘpos i hi).le⟩
  -- Condition A in the positive tail-seminorm form.
  have hA' : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        nonArchimedeanRelevantPositiveTailSelfsSum G β p ∞ hβ hp hp_top Λ t
          (fun i z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) Q ≤
          ENNReal.ofReal N := by
    intro k Q hQ
    have hAQ' : (∑ i ∈ Λ,
        if (Q.1 ∩ Ω i).Nonempty then Θ i * (K i) ^ (p.toReal)⁻¹ else 0) ≤
        N := hA k Q hQ
    have hterm : ∀ i ∈ Λ,
        (if goodGridLevelCellMeetsSupport G Q
            (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) then
          souzaPositivePointwiseSelfsTailNorm G β p ∞ hβ hp hp_top (t i)
            (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z)
        else 0) ≤
          ENNReal.ofReal
            (if (Q.1 ∩ Ω i).Nonempty then
              Θ i * (K i) ^ (p.toReal)⁻¹
            else 0) := by
      intro i hi
      have hmeet : goodGridLevelCellMeetsSupport G Q
          (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) ↔
          (Q.1 ∩ Ω i).Nonempty := by
        unfold goodGridLevelCellMeetsSupport
        rw [hsupp i hi]
      by_cases hc : (Q.1 ∩ Ω i).Nonempty
      · rw [if_pos (hmeet.mpr hc), if_pos hc]
        exact sInf_le
          (souzaPositiveSelfsTailBound_smul_of_stronglyRegularDomain
            G β p hβ hp hp_top (hSRD i hi) (hΘpos i hi).le)
      · rw [if_neg (fun h => hc (hmeet.mp h)), if_neg hc]
        simp
    change (∑ i ∈ Λ,
        if goodGridLevelCellMeetsSupport G Q
            (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) then
          souzaPositivePointwiseSelfsTailNorm G β p ∞ hβ hp hp_top (t i)
            (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z)
        else 0) ≤ ENNReal.ofReal N
    calc
      (∑ i ∈ Λ,
          if goodGridLevelCellMeetsSupport G Q
              (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) then
            souzaPositivePointwiseSelfsTailNorm G β p ∞ hβ hp hp_top (t i)
              (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z)
          else 0)
          ≤ ∑ i ∈ Λ,
              ENNReal.ofReal
                (if (Q.1 ∩ Ω i).Nonempty then
                  Θ i * (K i) ^ (p.toReal)⁻¹
                else 0) :=
        Finset.sum_le_sum hterm
      _ = ENNReal.ofReal
            (∑ i ∈ Λ,
              if (Q.1 ∩ Ω i).Nonempty then
                Θ i * (K i) ^ (p.toReal)⁻¹
              else 0) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        intro i hi
        by_cases hc : (Q.1 ∩ Ω i).Nonempty
        · rw [if_pos hc]
          exact mul_nonneg (hΘpos i hi).le
            (Real.rpow_nonneg (hSRD i hi).nonneg_K _)
        · rw [if_neg hc]
      _ ≤ ENNReal.ofReal N := ENNReal.ofReal_le_ofReal hAQ'
  -- Condition B in the support form.
  have hB' : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q
            (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) →
            t i ≤ k := by
    intro k Q i hi hQ hmeet
    apply hB k Q i hi hQ
    unfold goodGridLevelCellMeetsSupport at hmeet
    rwa [hsupp i hi] at hmeet
  obtain ⟨y, S, hSrep, hSfin, hScost, hSupp, hSpos⟩ :=
    hCgen Λ t
      (fun i z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z)
      N f x R hN hRep hRfin hRcanon hgpos htail hA' hB'
  refine ⟨y, S, hSrep, hSfin, hScost, ?_, hSpos⟩
  -- Translate the support conclusion into membership in the domains.
  intro k Q hQ
  obtain ⟨i, hi, hae⟩ := hSupp k Q hQ
  refine ⟨i, hi, ?_⟩
  refine hae.mono fun z hz => ?_
  by_contra hzΩ
  exact hz (by rw [Set.indicator_of_notMem hzΩ, mul_zero])

/--
Infinite-index analogue of `stronglyRegularOverlapCost`: the `ℝ≥0∞`-valued
series of the weighted costs `Θ i · (K i)^{1/p}` over the indices in
`Λ ⊆ ℕ` whose domain meets the cell.  No summability witness is needed.
-/
noncomputable def stronglyRegularOverlapCostInfinite
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (Λ : Set ℕ) (Ω : ℕ → Set α) (K Θ : ℕ → ℝ)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℝ≥0∞ := by
  classical
  exact ∑' i : {i // i ∈ Λ},
    if (Q.1 ∩ Ω i.1).Nonempty then
      ENNReal.ofReal (Θ i.1 * (K i.1) ^ (p.toReal)⁻¹)
    else 0

/--
**Proposition `pm1` of the paper, infinite-index version.**

The family of strongly regular domains may now be indexed by an arbitrary
`Λ ⊆ ℕ`; condition A becomes the `ℝ≥0∞`-valued series bound
`stronglyRegularOverlapCostInfinite ≤ N` on active cells.  The conclusions
are those of the infinite positive non-Archimedean theorem for the weighted
indicator family `g i = Θ i · 1_{Ω i}`: almost everywhere on the support of
`f` the series `∑ Θ i · 1_{Ω i}(z)` converges absolutely with bound
`Cgen2 · N`, the pointwise products sum to a limit function `h ∈ L^p`, and
`h` has a Souza representation `S` with finite cost,
`pqCost S ≤ Cgen2 · N · pqCost R`, every active cell of `S` contained a.e. in
some `Ω i`, and cone-positivity of `S` whenever `R` is positive.
-/
theorem souzaPointwiseMultipliersIInfinite
    (G : GoodGridSpace (α := α))
    (s β : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hβ : 0 < β) (hβs : s < β)
    (hβ_lt_inv : β < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cgen2 : ℝ,
      0 ≤ Cgen2 ∧
      ∀ (Λ : Set ℕ) (t : ℕ → ℕ) (Ω : ℕ → Set α) (K Θ : ℕ → ℝ) (N : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
        0 ≤ N →
        (∀ i ∈ Λ,
          StronglyRegularDomain G (Ω i) (1 - β * p.toReal) (K i) (t i)) →
        (∀ i ∈ Λ, 0 < Θ i) →
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) f
          (x : Lp ℂ p G.toWeakGridSpace.measure) →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
        SouzaCanonicalRepresentation G s p hs hp hp_top R →
        -- Condition A: weighted overlap series of the domains, on active cells.
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (R.block k).coeff Q ≠ 0 →
            stronglyRegularOverlapCostInfinite G p Λ Ω K Θ Q ≤
              ENNReal.ofReal N) →
        -- Condition B: active cells meeting `Ω i` are deep enough.
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
          i ∈ Λ →
            (R.block k).coeff Q ≠ 0 →
              (Q.1 ∩ Ω i).Nonempty →
                t i ≤ k) →
        ∃ h : α → ℂ,
          ∃ absSum : α → ℝ,
            (∀ᵐ z ∂G.toWeakGridSpace.measure,
              f z ≠ 0 →
                HasSum
                  (fun i : {i // i ∈ Λ} =>
                    ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖)
                  (absSum z) ∧
                absSum z ≤ Cgen2 * N) ∧
            (∀ᵐ z ∂G.toWeakGridSpace.measure,
              HasSum
                (fun i : {i // i ∈ Λ} =>
                  (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
                (h z)) ∧
            (∀ᵐ z ∂G.toWeakGridSpace.measure,
              ‖h z‖ ≤ Cgen2 * N * ‖f z‖) ∧
            (∃ hmem : MemLp h p G.toWeakGridSpace.measure,
              ‖MemLp.toLp h hmem‖ ≤
                Cgen2 * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖) ∧
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
                  Cgen2 * N *
                    WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
                -- [i] support: active cells of `S` lie a.e. in some `Ω i`.
                (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
                  (S.block k).coeff Q ≠ 0 →
                    ∃ i ∈ Λ,
                      ∀ᵐ z ∂(G.toWeakGridSpace.measure.restrict Q.1),
                        z ∈ Ω i) ∧
                -- [ii] positivity is preserved.
                (SouzaPositiveRepresentation G s p hs hp hp_top R →
                  SouzaConePositiveRepresentation G s p hs hp hp_top S) := by
  classical
  obtain ⟨Cgen, hCgen0, _hCgen1, hCgen⟩ :=
    souzaNonArchimedeanPropertyPositiveConeInfinite G s β p q ∞
      hs hβ hβs hβ_lt_inv hp hp_top
  refine ⟨Cgen, hCgen0, ?_⟩
  intro Λ t Ω K Θ N f x R hN hSRD hΘpos hRep hRfin hRcanon hA hB
  -- The support of each weighted indicator is exactly its domain.
  have hsupp : ∀ i ∈ Λ,
      {z | (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z ≠ 0} = Ω i := by
    intro i hi
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hne
      by_contra hzΩ
      exact hne (by rw [Set.indicator_of_notMem hzΩ, mul_zero])
    · intro hzΩ
      rw [Set.indicator_of_mem hzΩ, mul_one]
      exact Complex.ofReal_ne_zero.mpr (hΘpos i hi).ne'
  have hgpos : ∀ i ∈ Λ,
      SouzaPositiveFunction G β p ∞ hβ hp hp_top
        (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) :=
    fun i hi =>
      souzaPositiveFunction_of_stronglyRegularDomain G β p hβ hp hp_top
        (hSRD i hi) (hΘpos i hi).le
  have htail : ∀ i ∈ Λ,
      ∃ C : ℝ≥0∞,
        SouzaPositivePointwiseSelfsTailBound G β p ∞ hβ hp hp_top (t i)
          (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) C :=
    fun i hi =>
      ⟨ENNReal.ofReal (Θ i * (K i) ^ (p.toReal)⁻¹),
        souzaPositiveSelfsTailBound_smul_of_stronglyRegularDomain
          G β p hβ hp hp_top (hSRD i hi) (hΘpos i hi).le⟩
  -- Condition A in the positive tail-seminorm series form.
  have hA' : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      (R.block k).coeff Q ≠ 0 →
        (∑' i : {i // i ∈ Λ},
          nonArchimedeanRelevantPositiveTailSelfsInfiniteTerm
            G β p ∞ hβ hp hp_top Λ t
            (fun i z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z)
            Q i) ≤ ENNReal.ofReal N := by
    intro k Q hQ
    have hAQ' : (∑' i : {i // i ∈ Λ},
        if (Q.1 ∩ Ω i.1).Nonempty then
          ENNReal.ofReal (Θ i.1 * (K i.1) ^ (p.toReal)⁻¹)
        else 0) ≤ ENNReal.ofReal N := hA k Q hQ
    refine le_trans (ENNReal.tsum_le_tsum fun i => ?_) hAQ'
    have hmeet : goodGridLevelCellMeetsSupport G Q
        (fun z => (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z) ↔
        (Q.1 ∩ Ω i.1).Nonempty := by
      unfold goodGridLevelCellMeetsSupport
      rw [hsupp i.1 i.2]
    change (if goodGridLevelCellMeetsSupport G Q
        (fun z => (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z) then
        souzaPositivePointwiseSelfsTailNorm G β p ∞ hβ hp hp_top (t i.1)
          (fun z => (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z)
      else 0) ≤ _
    by_cases hc : (Q.1 ∩ Ω i.1).Nonempty
    · rw [if_pos (hmeet.mpr hc), if_pos hc]
      exact sInf_le
        (souzaPositiveSelfsTailBound_smul_of_stronglyRegularDomain
          G β p hβ hp hp_top (hSRD i.1 i.2) (hΘpos i.1 i.2).le)
    · rw [if_neg (fun h => hc (hmeet.mp h)), if_neg hc]
  -- Condition B in the support form.
  have hB' : ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) i,
      i ∈ Λ →
        (R.block k).coeff Q ≠ 0 →
          goodGridLevelCellMeetsSupport G Q
            (fun z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z) →
            t i ≤ k := by
    intro k Q i hi hQ hmeet
    apply hB k Q i hi hQ
    unfold goodGridLevelCellMeetsSupport at hmeet
    rwa [hsupp i hi] at hmeet
  obtain ⟨h, absSum, habs, hHasSum, hbound, hmem, y, S, hSrep, hSfin, hScost,
      hSupp, hSpos⟩ :=
    hCgen Λ t
      (fun i z => (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z)
      N f x R hN hRep hRfin hRcanon hgpos htail hA' hB'
  refine ⟨h, absSum, habs, hHasSum, hbound, hmem, y, S, hSrep, hSfin, hScost,
    ?_, hSpos⟩
  -- Translate the support conclusion into membership in the domains.
  intro k Q hQ
  obtain ⟨i, hi, hae⟩ := hSupp k Q hQ
  refine ⟨i, hi, ?_⟩
  refine hae.mono fun z hz => ?_
  by_contra hzΩ
  exact hz (by rw [Set.indicator_of_notMem hzΩ, mul_zero])

end

end GoodGridSpace
