import BesovSpacesGoodGrid.GoodGrid.QuasiAlgebra
import BesovSpacesGoodGrid.GoodGrid.Multipliers.StronglyRegularDomains

/-!
# Regular domains

This file starts the formalization of the subsection *Regular domains* (`cf`)
of the paper *Besov-ish spaces through atomic decomposition*.

The main definitions are deliberately separated from the multiplier estimates:

* `firstContainedLevel` is the paper's `k₀(Ω)`, with the convention that it is
  `0` if `Ω` contains no grid cell;
* `RegularFamily` is the countable, pairwise-disjoint family version of
  regularity, indexed by a subset of `ℕ`;
* `RegularDomain` is the one-set version.

The final statements record the two results from the subsection: a strongly
regular domain is regular after lowering the smoothness exponent, and a
regular family gives localized Souza representations for the restrictions
`g · 1_{Ωᵣ}` plus the indicator/multiplier bounds.  The remaining open proof is
the localized restriction estimate, which reuses the long `u₁ + u₂` product
construction from `QuasiAlgebra` together with new localization bookkeeping.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/-- A level `k` contains a grid cell lying inside `Ω`. -/
def ContainsGridCellAtLevel (G : GoodGridSpace (α := α)) (Ω : Set α)
    (k : ℕ) : Prop :=
  ∃ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k, Q.1 ⊆ Ω

/-- The set `Ω` contains at least one grid cell, at some level. -/
def ContainsGridCell (G : GoodGridSpace (α := α)) (Ω : Set α) : Prop :=
  ∃ k : ℕ, ContainsGridCellAtLevel G Ω k

/--
The first level at which `Ω` contains a grid cell.

This is the paper's `k₀(Ω)`.  If no such level exists we return `0`; all
regularity structures below include a witness that the relevant sets really
contain a grid cell, so the fallback convention is never used in the main API.
-/
noncomputable def firstContainedLevel
    (G : GoodGridSpace (α := α)) (Ω : Set α) : ℕ := by
  classical
  exact if h : ContainsGridCell G Ω then Nat.find h else 0

/-- `firstContainedLevel` satisfies the defining containment property whenever
`Ω` contains a grid cell. -/
theorem firstContainedLevel_spec
    (G : GoodGridSpace (α := α)) {Ω : Set α}
    (hΩ : ContainsGridCell G Ω) :
    ContainsGridCellAtLevel G Ω (firstContainedLevel G Ω) := by
  classical
  unfold firstContainedLevel
  rw [dif_pos hΩ]
  exact Nat.find_spec hΩ

/-- No earlier level contains a grid cell before `firstContainedLevel`. -/
theorem not_containsGridCellAtLevel_lt_firstContainedLevel
    (G : GoodGridSpace (α := α)) {Ω : Set α}
    (hΩ : ContainsGridCell G Ω) {k : ℕ}
    (hk : k < firstContainedLevel G Ω) :
    ¬ ContainsGridCellAtLevel G Ω k := by
  classical
  unfold firstContainedLevel at hk
  rw [dif_pos hΩ] at hk
  exact Nat.find_min hΩ hk

/-- The union of a countable family selected by `Λ`. -/
def regularFamilyUnion (Λ : Set ℕ) (Ω : ℕ → Set α) : Set α :=
  ⋃ i ∈ Λ, Ω i

/--
A countable pairwise-disjoint family of measurable sets is
`(a, C, c)`-regular when it admits level families of grid cells which tile each
member and whose level costs satisfy the geometric estimate from equation
`(dom)` of the paper.

The indexing set is a subset `Λ : Set ℕ`, matching the conventions already
used for infinite multiplier families in the project.
-/
structure RegularFamily
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (a C c : ℝ) where
  /-- Active domains are measurable. -/
  measurable : ∀ i ∈ Λ, MeasurableSet (Ω i)
  /-- Active domains contain a grid cell, so `k₀(Ωᵢ)` is meaningful. -/
  contains_cell : ∀ i ∈ Λ, ContainsGridCell G (Ω i)
  /-- The whole union contains a grid cell, so `k₀(⋃ᵢ Ωᵢ)` is meaningful. -/
  union_contains_cell : ContainsGridCell G (regularFamilyUnion Λ Ω)
  /-- The regularity constant is nonnegative. -/
  C_nonneg : 0 ≤ C
  /-- The geometric ratio is nonnegative. -/
  c_nonneg : 0 ≤ c
  /-- The geometric ratio is strictly smaller than one. -/
  c_lt_one : c < 1
  /-- The active domains are pairwise disjoint. -/
  pairwise_disjoint :
    ∀ i ∈ Λ, ∀ j ∈ Λ, i ≠ j → Disjoint (Ω i) (Ω j)
  /-- The family `ℱᵏ(Ωᵢ)` of level-`k` cells. -/
  family : ℕ → ℕ → Finset (Set α)
  /-- Every selected set is a genuine level-`k` grid cell. -/
  family_subset :
    ∀ i ∈ Λ, ∀ k, family i k ⊆ G.toWeakGridSpace.grid.partitions k
  /-- No cells are selected below the first contained level of `Ωᵢ`. -/
  family_empty_before :
    ∀ i ∈ Λ, ∀ k, k < firstContainedLevel G (Ω i) → family i k = ∅
  /-- Inactive indices carry the empty decomposition. -/
  family_empty_of_not_mem :
    ∀ i ∉ Λ, ∀ k, family i k = ∅
  /-- The selected cells tile each active domain. -/
  cover :
    ∀ i ∈ Λ, Ω i = ⋃ k, ⋃ Q ∈ family i k, (Q : Set α)
  /-- Distinct selected cells in a fixed active domain are disjoint, even
  across different levels. -/
  pairwise_disjoint_cells :
    ∀ i ∈ Λ, ∀ k l (P Q : Set α),
      P ∈ family i k → Q ∈ family i l → P ≠ Q → Disjoint P Q
  /-- The level cost estimate `(dom)`. -/
  cost :
    ∀ k,
      (∑' i : ℕ,
          Set.indicator Λ
            (fun i => ∑ Q ∈ family i k, (G.grid.μ Q).toReal ^ a) i) ≤
        C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
          (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a

/--
A single measurable set is an `(a, C, c)`-regular domain when it is tiled by
level families of grid cells with the same geometric level-cost estimate.
-/
structure RegularDomain
    (G : GoodGridSpace (α := α)) (Ω : Set α) (a C c : ℝ) where
  /-- The domain is measurable. -/
  measurable : MeasurableSet Ω
  /-- The domain contains a grid cell, so `k₀(Ω)` is meaningful. -/
  contains_cell : ContainsGridCell G Ω
  /-- The regularity constant is nonnegative. -/
  C_nonneg : 0 ≤ C
  /-- The geometric ratio is nonnegative. -/
  c_nonneg : 0 ≤ c
  /-- The geometric ratio is strictly smaller than one. -/
  c_lt_one : c < 1
  /-- The family `ℱᵏ(Ω)` of level-`k` cells. -/
  family : ℕ → Finset (Set α)
  /-- Every selected set is a genuine level-`k` grid cell. -/
  family_subset : ∀ k, family k ⊆ G.toWeakGridSpace.grid.partitions k
  /-- No cells are selected below the first contained level of `Ω`. -/
  family_empty_before :
    ∀ k, k < firstContainedLevel G Ω → family k = ∅
  /-- The selected cells tile `Ω`. -/
  cover : Ω = ⋃ k, ⋃ Q ∈ family k, (Q : Set α)
  /-- Distinct selected cells are disjoint, even across different levels. -/
  pairwise_disjoint_cells :
    ∀ k l (P Q : Set α),
      P ∈ family k → Q ∈ family l → P ≠ Q → Disjoint P Q
  /-- The one-domain version of the level cost estimate `(dom)`. -/
  cost :
    ∀ k,
      (∑ Q ∈ family k, (G.grid.μ Q).toReal ^ a) ≤
        C * c ^ (k - firstContainedLevel G Ω) * (G.grid.μ Ω).toReal ^ a

/-- A cell selected by a regular family is contained in its domain. -/
theorem RegularFamily.cell_subset_domain
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    {i k : ℕ} {Q : Set α} (hi : i ∈ Λ) (hQ : Q ∈ hΩ.family i k) :
    Q ⊆ Ω i := by
  intro z hz
  rw [hΩ.cover i hi]
  exact Set.mem_iUnion.mpr
    ⟨k, Set.mem_iUnion.mpr
      ⟨Q, Set.mem_iUnion.mpr ⟨hQ, hz⟩⟩⟩

/-- A cell selected by a regular family is contained in the family union. -/
theorem RegularFamily.cell_subset_union
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    {i k : ℕ} {Q : Set α} (hi : i ∈ Λ) (hQ : Q ∈ hΩ.family i k) :
    Q ⊆ regularFamilyUnion Λ Ω :=
  (hΩ.cell_subset_domain hi hQ).trans
    (Set.subset_iUnion₂_of_subset i hi subset_rfl)

/-- Cells selected for two different active domains are disjoint. -/
theorem RegularFamily.selected_cells_disjoint_of_ne_index
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    {i j k l : ℕ} {P Q : Set α}
    (hi : i ∈ Λ) (hj : j ∈ Λ) (hij : i ≠ j)
    (hP : P ∈ hΩ.family i k) (hQ : Q ∈ hΩ.family j l) :
    Disjoint P Q :=
  (hΩ.pairwise_disjoint i hi j hj hij).mono
    (hΩ.cell_subset_domain hi hP) (hΩ.cell_subset_domain hj hQ)

/--
Distinct cells selected by a regular family are disjoint, whether they come
from the same active domain or from different active domains.
-/
theorem RegularFamily.selected_cells_disjoint
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    {i j k l : ℕ} {P Q : Set α}
    (hi : i ∈ Λ) (hj : j ∈ Λ)
    (hP : P ∈ hΩ.family i k) (hQ : Q ∈ hΩ.family j l)
    (hPQ : P ≠ Q) :
    Disjoint P Q := by
  by_cases hij : i = j
  · subst hij
    exact hΩ.pairwise_disjoint_cells i hi k l P Q hP hQ hPQ
  · exact hΩ.selected_cells_disjoint_of_ne_index hi hj hij hP hQ

/--
For each fixed level, only finitely many active indices can contribute a
nonzero regular-family cost.

This is the formal reason the displayed `(dom)` series is summable: a nonzero
level contribution chooses at least one level-`k` grid cell, and the disjoint
active domains prevent two different indices from choosing the same cell.
-/
theorem RegularFamily.cost_summable
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c) (k : ℕ) :
    Summable
      (fun i : ℕ =>
        Set.indicator Λ
          (fun i => ∑ Q ∈ hΩ.family i k, (G.grid.μ Q).toReal ^ a) i) := by
  classical
  let activeCost : ℕ → ℝ := fun i =>
    Set.indicator Λ
      (fun i => ∑ Q ∈ hΩ.family i k, (G.grid.μ Q).toReal ^ a) i
  have hsupport_finite : (Function.support activeCost).Finite := by
    let selectedExists :
        ∀ i : Function.support activeCost,
          ∃ Q : Set α, Q ∈ hΩ.family (i : ℕ) k := fun i => by
      have hi : (i : ℕ) ∈ Λ := by
        by_contra hi
        exact i.2 (by simp [activeCost, Set.indicator_of_notMem hi])
      have hsum_ne :
          (∑ Q ∈ hΩ.family (i : ℕ) k, (G.grid.μ Q).toReal ^ a) ≠ 0 := by
        intro hsum
        exact i.2 (by simp [activeCost, Set.indicator_of_mem hi, hsum])
      have hex :
          ∃ Q ∈ hΩ.family (i : ℕ) k, (G.grid.μ Q).toReal ^ a ≠ 0 := by
        by_contra hnone
        apply hsum_ne
        refine Finset.sum_eq_zero ?_
        intro Q hQ
        by_contra hQne
        exact hnone ⟨Q, hQ, hQne⟩
      exact ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩
    let chosen :
        Function.support activeCost →
          WeakGridSpace.LevelCell G.toWeakGridSpace k := fun i => by
      have hi : (i : ℕ) ∈ Λ := by
        by_contra hi
        exact i.2 (by simp [activeCost, Set.indicator_of_notMem hi])
      let Q : Set α := Classical.choose (selectedExists i)
      have hQ : Q ∈ hΩ.family (i : ℕ) k :=
        by simpa [Q] using Classical.choose_spec (selectedExists i)
      exact ⟨Q, hΩ.family_subset (i : ℕ) hi k hQ⟩
    have hchosen_mem :
        ∀ i : Function.support activeCost,
          (chosen i).1 ∈ hΩ.family (i : ℕ) k := by
      intro i
      dsimp [chosen]
      exact by simpa using Classical.choose_spec (selectedExists i)
    have hchosen_inj : Function.Injective chosen := by
      intro i j hij
      by_cases hijidx : (i : ℕ) = (j : ℕ)
      · exact Subtype.ext hijidx
      exfalso
      have hii : (i : ℕ) ∈ Λ := by
        by_contra hi
        exact i.2 (by simp [activeCost, Set.indicator_of_notMem hi])
      have hjj : (j : ℕ) ∈ Λ := by
        by_contra hj
        exact j.2 (by simp [activeCost, Set.indicator_of_notMem hj])
      have hdisj :
          Disjoint (chosen i).1 (chosen j).1 :=
        hΩ.selected_cells_disjoint_of_ne_index hii hjj hijidx
          (hchosen_mem i) (hchosen_mem j)
      have hsame : (chosen i).1 = (chosen j).1 :=
        congrArg Subtype.val hij
      rw [hsame] at hdisj
      have hpos : 0 < G.grid.μ (chosen j).1 :=
        G.grid.positive_measure k (chosen j).1 (chosen j).2
      have hzero : G.grid.μ (chosen j).1 = 0 := by
        have hsub_empty : (chosen j).1 ⊆ (∅ : Set α) := by
          intro z hz
          exact Set.disjoint_left.mp hdisj hz hz
        exact measure_mono_null hsub_empty measure_empty
      rw [hzero] at hpos
      exact (lt_irrefl (0 : ℝ≥0∞)) hpos
    haveI : Finite (Function.support activeCost) :=
      Finite.of_injective chosen hchosen_inj
    exact Set.toFinite (Function.support activeCost)
  change Summable activeCost
  exact summable_of_hasFiniteSupport hsupport_finite

/-- The union of a regular family is measurable. -/
theorem RegularFamily.measurable_union
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c) :
    MeasurableSet (regularFamilyUnion Λ Ω) := by
  classical
  have hunion :
      regularFamilyUnion Λ Ω =
        ⋃ i : ℕ, if hi : i ∈ Λ then Ω i else ∅ := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_iUnion₂.mp hz with ⟨i, hi, hzi⟩
      exact Set.mem_iUnion.mpr ⟨i, by simp [hi, hzi]⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
      by_cases hi : i ∈ Λ
      · exact Set.mem_iUnion₂.mpr ⟨i, hi, by simpa [hi] using hzi⟩
      · simp [hi] at hzi
  rw [hunion]
  exact MeasurableSet.iUnion fun i => by
    by_cases hi : i ∈ Λ
    · simpa [hi] using hΩ.measurable i hi
    · simp [hi]

/--
No active decomposition cell can occur before the first level at which the
whole family union contains a grid cell.
-/
theorem RegularFamily.not_mem_family_of_lt_firstContainedLevel_union
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    {i k : ℕ} {Q : Set α} (hi : i ∈ Λ)
    (hk : k < firstContainedLevel G (regularFamilyUnion Λ Ω)) :
    Q ∉ hΩ.family i k := by
  intro hQ
  have hQmem : Q ∈ G.toWeakGridSpace.grid.partitions k :=
    hΩ.family_subset i hi k hQ
  have hcontains :
      ContainsGridCellAtLevel G (regularFamilyUnion Λ Ω) k :=
    ⟨⟨Q, hQmem⟩, hΩ.cell_subset_union hi hQ⟩
  exact not_containsGridCellAtLevel_lt_firstContainedLevel
    G hΩ.union_contains_cell hk hcontains

/--
The level-`k` cell family naturally associated with the union of a regular
family: keep exactly those level-`k` grid cells selected by at least one
active member of the family.
-/
noncomputable def RegularFamily.unionFamily
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c) (k : ℕ) :
    Finset (Set α) := by
  classical
  exact (G.toWeakGridSpace.grid.partitions k).filter
    (fun Q => ∃ i ∈ Λ, Q ∈ hΩ.family i k)

/-- Membership in the union-level family. -/
theorem RegularFamily.mem_unionFamily_iff
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    {k : ℕ} {Q : Set α} :
    Q ∈ hΩ.unionFamily k ↔
      Q ∈ G.toWeakGridSpace.grid.partitions k ∧
        ∃ i ∈ Λ, Q ∈ hΩ.family i k := by
  classical
  simp [RegularFamily.unionFamily]

/-- Every cell in the union-level family is a genuine level-`k` grid cell. -/
theorem RegularFamily.unionFamily_subset
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c) (k : ℕ) :
    hΩ.unionFamily k ⊆ G.toWeakGridSpace.grid.partitions k := by
  intro Q hQ
  exact (hΩ.mem_unionFamily_iff.mp hQ).1

/-- The union-level family tiles the union of the regular family. -/
theorem RegularFamily.unionFamily_cover
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c) :
    regularFamilyUnion Λ Ω =
      ⋃ k, ⋃ Q ∈ hΩ.unionFamily k, (Q : Set α) := by
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion₂.mp hz with ⟨i, hi, hzi⟩
    rw [hΩ.cover i hi] at hzi
    rcases Set.mem_iUnion.mp hzi with ⟨k, hzi⟩
    rcases Set.mem_iUnion.mp hzi with ⟨Q, hzi⟩
    rcases Set.mem_iUnion.mp hzi with ⟨hQ, hzQ⟩
    have hQgrid : Q ∈ G.toWeakGridSpace.grid.partitions k :=
      hΩ.family_subset i hi k hQ
    have hQunion : Q ∈ hΩ.unionFamily k :=
      hΩ.mem_unionFamily_iff.mpr ⟨hQgrid, ⟨i, hi, hQ⟩⟩
    exact Set.mem_iUnion.mpr
      ⟨k, Set.mem_iUnion.mpr
        ⟨Q, Set.mem_iUnion.mpr ⟨hQunion, hzQ⟩⟩⟩
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨k, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨Q, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hQ, hzQ⟩
    rcases (hΩ.mem_unionFamily_iff.mp hQ).2 with ⟨i, hi, hQi⟩
    exact hΩ.cell_subset_union hi hQi hzQ

/-- Distinct cells in the union-level family are disjoint. -/
theorem RegularFamily.unionFamily_pairwise_disjoint
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    {k l : ℕ} {P Q : Set α}
    (hP : P ∈ hΩ.unionFamily k) (hQ : Q ∈ hΩ.unionFamily l)
    (hPQ : P ≠ Q) :
    Disjoint P Q := by
  rcases (hΩ.mem_unionFamily_iff.mp hP).2 with ⟨i, hi, hPi⟩
  rcases (hΩ.mem_unionFamily_iff.mp hQ).2 with ⟨j, hj, hQj⟩
  exact hΩ.selected_cells_disjoint hi hj hPi hQj hPQ

/--
The union-level family has no cells before the first level at which the union
contains a grid cell.
-/
theorem RegularFamily.unionFamily_empty_before
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    {k : ℕ} (hk : k < firstContainedLevel G (regularFamilyUnion Λ Ω)) :
    hΩ.unionFamily k = ∅ := by
  classical
  ext Q
  constructor
  · intro hQ
    rcases (hΩ.mem_unionFamily_iff.mp hQ).2 with ⟨i, hi, hQi⟩
    exact (hΩ.not_mem_family_of_lt_firstContainedLevel_union hi hk hQi).elim
  · intro hQ
    simp at hQ

/-- A cell selected by a regular domain is contained in the domain. -/
theorem RegularDomain.cell_subset_domain
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a C c : ℝ}
    (hΩ : RegularDomain G Ω a C c) {k : ℕ} {Q : Set α}
    (hQ : Q ∈ hΩ.family k) :
    Q ⊆ Ω := by
  intro z hz
  rw [hΩ.cover]
  exact Set.mem_iUnion.mpr
    ⟨k, Set.mem_iUnion.mpr
      ⟨Q, Set.mem_iUnion.mpr ⟨hQ, hz⟩⟩⟩

/--
Every regular domain is a regular family with one active index.

This is often the most convenient bridge between the one-domain and
family-valued formulations: the active set is `{0}`, all inactive indices have
the empty cell family, and the cost estimate is exactly the original
one-domain estimate.
-/
noncomputable def RegularDomain.toRegularFamily_singleton
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a C c : ℝ}
    (hΩ : RegularDomain G Ω a C c) :
    RegularFamily G ({0} : Set ℕ) (fun _ : ℕ => Ω) a C c := by
  classical
  let F : ℕ → ℕ → Finset (Set α) :=
    fun i k => if i = 0 then hΩ.family k else ∅
  have hunion : regularFamilyUnion ({0} : Set ℕ) (fun _ : ℕ => Ω) = Ω := by
    ext z
    simp [regularFamilyUnion]
  refine
    { measurable := ?_
      contains_cell := ?_
      union_contains_cell := ?_
      C_nonneg := hΩ.C_nonneg
      c_nonneg := hΩ.c_nonneg
      c_lt_one := hΩ.c_lt_one
      pairwise_disjoint := ?_
      family := F
      family_subset := ?_
      family_empty_before := ?_
      family_empty_of_not_mem := ?_
      cover := ?_
      pairwise_disjoint_cells := ?_
      cost := ?_ }
  · intro i hi
    exact hΩ.measurable
  · intro i hi
    exact hΩ.contains_cell
  · simpa [hunion] using hΩ.contains_cell
  · intro i hi j hj hij
    have hi0 : i = 0 := by simpa using hi
    have hj0 : j = 0 := by simpa using hj
    exact (hij (hi0.trans hj0.symm)).elim
  · intro i hi k Q hQ
    have hi0 : i = 0 := by simpa using hi
    have hQ' : Q ∈ hΩ.family k := by
      simpa [F, hi0] using hQ
    exact hΩ.family_subset k hQ'
  · intro i hi k hk
    have hi0 : i = 0 := by simpa using hi
    simpa [F, hi0] using hΩ.family_empty_before k hk
  · intro i hi k
    have hi0 : i ≠ 0 := by
      intro h
      exact hi (by simp [h])
    simp [F, hi0]
  · intro i hi
    have hi0 : i = 0 := by simpa using hi
    simpa [F, hi0] using hΩ.cover
  · intro i hi k l P Q hP hQ hPQ
    have hi0 : i = 0 := by simpa using hi
    have hP' : P ∈ hΩ.family k := by
      simpa [F, hi0] using hP
    have hQ' : Q ∈ hΩ.family l := by
      simpa [F, hi0] using hQ
    exact hΩ.pairwise_disjoint_cells k l P Q hP' hQ' hPQ
  · intro k
    have hterm :
        (fun i : ℕ =>
            Set.indicator ({0} : Set ℕ)
              (fun i =>
                ∑ Q ∈ F i k, (G.grid.μ Q).toReal ^ a) i)
          =
        Function.update (fun _ : ℕ => (0 : ℝ)) 0
          (∑ Q ∈ hΩ.family k, (G.grid.μ Q).toReal ^ a) := by
      funext i
      by_cases hi0 : i = 0
      · subst hi0
        simp [F]
      · simp [F, hi0]
    have htsum :
        (∑' i : ℕ,
            Set.indicator ({0} : Set ℕ)
              (fun i =>
                ∑ Q ∈ F i k, (G.grid.μ Q).toReal ^ a) i) =
          ∑ Q ∈ hΩ.family k, (G.grid.μ Q).toReal ^ a := by
      calc
        (∑' i : ℕ,
            Set.indicator ({0} : Set ℕ)
              (fun i =>
                ∑ Q ∈ F i k, (G.grid.μ Q).toReal ^ a) i)
            = ∑' i : ℕ,
                Function.update (fun _ : ℕ => (0 : ℝ)) 0
                  (∑ Q ∈ hΩ.family k, (G.grid.μ Q).toReal ^ a) i := by
              rw [hterm]
        _ = ∑ Q ∈ hΩ.family k, (G.grid.μ Q).toReal ^ a := by
          rw [tsum_eq_single 0]
          · simp
          · intro b hb
            simp [Function.update, hb]
    simpa [F, hunion, htsum] using hΩ.cost k

/--
The union of a regular family is a regular domain.

This is the observation following the representation estimate in the paper.
The proof filters each finite partition level by the cells selected by at
least one active member of the family; the pairwise disjointness of the
domains prevents double counting.
-/
theorem RegularFamily.regularDomain_union
    {G : GoodGridSpace (α := α)} {Λ : Set ℕ} {Ω : ℕ → Set α}
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c) :
    Nonempty (RegularDomain G (regularFamilyUnion Λ Ω) a C c) := by
  refine ⟨
    { measurable := hΩ.measurable_union
      contains_cell := hΩ.union_contains_cell
      C_nonneg := hΩ.C_nonneg
      c_nonneg := hΩ.c_nonneg
      c_lt_one := hΩ.c_lt_one
      family := hΩ.unionFamily
      family_subset := hΩ.unionFamily_subset
      family_empty_before := fun k hk => hΩ.unionFamily_empty_before hk
      cover := hΩ.unionFamily_cover
      pairwise_disjoint_cells := ?_
      cost := ?_ }⟩
  · intro k l P Q hP hQ hPQ
    exact hΩ.unionFamily_pairwise_disjoint hP hQ hPQ
  · intro k
    classical
    let w : Set α → ℝ := fun Q => (G.grid.μ Q).toReal ^ a
    let F : Finset (Set α) := hΩ.unionFamily k
    let owner : Set α → ℕ := fun Q =>
      if hQ : Q ∈ F then
        Classical.choose (hΩ.mem_unionFamily_iff.mp hQ).2
      else 0
    let S : Finset ℕ := F.image owner
    let activeCost : ℕ → ℝ := fun i =>
      Set.indicator Λ (fun i => ∑ Q ∈ hΩ.family i k, w Q) i
    have hw_nonneg : ∀ Q, 0 ≤ w Q := fun Q =>
      Real.rpow_nonneg ENNReal.toReal_nonneg a
    have howner_mem : ∀ ⦃Q : Set α⦄, Q ∈ F → owner Q ∈ Λ := by
      intro Q hQ
      change
        (if hQ' : Q ∈ F then
          Classical.choose (hΩ.mem_unionFamily_iff.mp hQ').2
        else 0) ∈ Λ
      rw [dif_pos hQ]
      exact (Classical.choose_spec (hΩ.mem_unionFamily_iff.mp hQ).2).1
    have howner_cell :
        ∀ ⦃Q : Set α⦄, Q ∈ F → Q ∈ hΩ.family (owner Q) k := by
      intro Q hQ
      change
        Q ∈ hΩ.family
          (if hQ' : Q ∈ F then
            Classical.choose (hΩ.mem_unionFamily_iff.mp hQ').2
          else 0) k
      rw [dif_pos hQ]
      exact (Classical.choose_spec (hΩ.mem_unionFamily_iff.mp hQ).2).2
    have hS_subset : ∀ ⦃i : ℕ⦄, i ∈ S → i ∈ Λ := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨Q, hQF, rfl⟩
      exact howner_mem hQF
    have hactive_nonneg : ∀ i, 0 ≤ activeCost i := by
      intro i
      by_cases hi : i ∈ Λ
      · simp only [activeCost, Set.indicator_of_mem hi]
        exact Finset.sum_nonneg fun Q _ => hw_nonneg Q
      · simp only [activeCost, Set.indicator_of_notMem hi]
        exact le_rfl
    have hfiber_subset :
        ∀ i : ℕ, (F.filter fun Q => owner Q = i) ⊆ hΩ.family i k := by
      intro i Q hQ
      rcases Finset.mem_filter.mp hQ with ⟨hQF, hQi⟩
      simpa only [hQi] using howner_cell hQF
    have hfiber_le :
        ∀ i : ℕ,
          (∑ Q ∈ F.filter fun Q => owner Q = i, w Q) ≤
            ∑ Q ∈ hΩ.family i k, w Q := by
      intro i
      exact Finset.sum_le_sum_of_subset_of_nonneg (hfiber_subset i)
        (fun Q _ _ => hw_nonneg Q)
    have hfinite_le_active :
        (∑ i ∈ S, ∑ Q ∈ F.filter fun Q => owner Q = i, w Q) ≤
          ∑ i ∈ S, activeCost i := by
      refine Finset.sum_le_sum ?_
      intro i hiS
      exact (hfiber_le i).trans_eq (by
        simp only [activeCost, Set.indicator_of_mem (hS_subset hiS)])
    have hdecomp :
        (∑ i ∈ S, ∑ Q ∈ F.filter fun Q => owner Q = i, w Q) =
          ∑ Q ∈ F, w Q := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := F) (t := S) (g := owner)
        (fun Q hQ => Finset.mem_image.mpr ⟨Q, hQ, rfl⟩) w
    calc
      (∑ Q ∈ hΩ.unionFamily k, (G.grid.μ Q).toReal ^ a)
          = ∑ Q ∈ F, w Q := rfl
      _ = ∑ i ∈ S, ∑ Q ∈ F.filter fun Q => owner Q = i, w Q :=
        hdecomp.symm
      _ ≤ ∑ i ∈ S, activeCost i := hfinite_le_active
      _ ≤ ∑' i : ℕ, activeCost i :=
        (hΩ.cost_summable k).sum_le_tsum S
          (fun i _ => hactive_nonneg i)
      _ ≤ C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
          (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a := by
        simpa only [activeCost, w] using hΩ.cost k

/-- A cell selected in a strong decomposition lies inside the decomposed
intersection `Q ∩ Ω`. -/
theorem StronglyRegularDecomposition.cell_subset_inter
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a K : ℝ}
    {Q : GoodGridCell G} (D : StronglyRegularDecomposition G Ω a K Q)
    {k : ℕ} {P : Set α} (hP : P ∈ D.family k) :
    P ⊆ Q.cell ∩ Ω := by
  intro z hz
  rw [D.cover]
  exact Set.mem_iUnion.mpr
    ⟨k, Set.mem_iUnion.mpr
      ⟨P, Set.mem_iUnion.mpr ⟨hP, hz⟩⟩⟩

/-- A cell selected in a strong decomposition lies inside the ambient
strong-regularity cell. -/
theorem StronglyRegularDecomposition.cell_subset_cell
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a K : ℝ}
    {Q : GoodGridCell G} (D : StronglyRegularDecomposition G Ω a K Q)
    {k : ℕ} {P : Set α} (hP : P ∈ D.family k) :
    P ⊆ Q.cell :=
  (D.cell_subset_inter hP).trans Set.inter_subset_left

/-- A cell selected in a strong decomposition lies inside the domain. -/
theorem StronglyRegularDecomposition.cell_subset_domain
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a K : ℝ}
    {Q : GoodGridCell G} (D : StronglyRegularDecomposition G Ω a K Q)
    {k : ℕ} {P : Set α} (hP : P ∈ D.family k) :
    P ⊆ Ω :=
  (D.cell_subset_inter hP).trans Set.inter_subset_right

/--
Choose the strong decomposition of `Q ∩ Ω` used by a strongly regular domain.

This is a thin choice wrapper used to assemble the regular-domain
decomposition from the finite level `k₀(Ω)` partition.
-/
private noncomputable def stronglyRegularRootDecomposition
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a K : ℝ}
    (hΩ : StronglyRegularDomain G Ω a K 0) {k₀ : ℕ}
    (Q : Set α) (hQ : Q ∈ G.toWeakGridSpace.grid.partitions k₀) :
    StronglyRegularDecomposition G Ω a K ⟨k₀, Q, hQ⟩ :=
  Classical.choice (hΩ.2 ⟨k₀, Q, hQ⟩ (Nat.zero_le k₀))

/--
Candidate level family for proving that a strongly regular domain is regular:
at each level `k`, combine the strong decompositions of `Q ∩ Ω` over all
cells `Q` in the partition at `k₀(Ω)`.
-/
private noncomputable def stronglyRegularCandidateFamily
    (G : GoodGridSpace (α := α)) (Ω : Set α) (a K : ℝ)
    (hΩ : StronglyRegularDomain G Ω a K 0) (k : ℕ) :
    Finset (Set α) := by
  classical
  let k₀ := firstContainedLevel G Ω
  exact (G.toWeakGridSpace.grid.partitions k₀).biUnion fun Q =>
    if hQ : Q ∈ G.toWeakGridSpace.grid.partitions k₀ then
      (stronglyRegularRootDecomposition hΩ Q hQ).family k
    else ∅

/-- Every selected candidate cell is a level-`k` grid cell. -/
private theorem stronglyRegularCandidateFamily_subset
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a K : ℝ}
    {hΩ : StronglyRegularDomain G Ω a K 0} (k : ℕ) :
    stronglyRegularCandidateFamily G Ω a K hΩ k ⊆
      G.toWeakGridSpace.grid.partitions k := by
  classical
  intro P hP
  simp only [stronglyRegularCandidateFamily] at hP
  rcases Finset.mem_biUnion.mp hP with ⟨Q, hQ, hPQ⟩
  have hPQ' :
      P ∈ (stronglyRegularRootDecomposition hΩ Q hQ).family k := by
    simpa [hQ] using hPQ
  exact (stronglyRegularRootDecomposition hΩ Q hQ).family_subset k hPQ'

/-- Every selected candidate cell lies inside the target domain. -/
private theorem stronglyRegularCandidateFamily_cell_subset_domain
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a K : ℝ}
    {hΩ : StronglyRegularDomain G Ω a K 0} {k : ℕ} {P : Set α}
    (hP : P ∈ stronglyRegularCandidateFamily G Ω a K hΩ k) :
    P ⊆ Ω := by
  classical
  simp only [stronglyRegularCandidateFamily] at hP
  rcases Finset.mem_biUnion.mp hP with ⟨Q, hQ, hPQ⟩
  have hPQ' :
      P ∈ (stronglyRegularRootDecomposition hΩ Q hQ).family k := by
    simpa [hQ] using hPQ
  exact (stronglyRegularRootDecomposition hΩ Q hQ).cell_subset_domain hPQ'

/--
The candidate family has no cells before `k₀(Ω)`: otherwise such a cell would
itself witness an earlier contained grid cell.
-/
private theorem stronglyRegularCandidateFamily_empty_before
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a K : ℝ}
    {hΩcell : ContainsGridCell G Ω}
    {hΩ : StronglyRegularDomain G Ω a K 0} {k : ℕ}
    (hk : k < firstContainedLevel G Ω) :
    stronglyRegularCandidateFamily G Ω a K hΩ k = ∅ := by
  classical
  ext P
  constructor
  · intro hP
    have hPgrid : P ∈ G.toWeakGridSpace.grid.partitions k :=
      stronglyRegularCandidateFamily_subset (G := G) (Ω := Ω) (a := a)
        (K := K) (hΩ := hΩ) k hP
    have hcontains : ContainsGridCellAtLevel G Ω k :=
      ⟨⟨P, hPgrid⟩,
        stronglyRegularCandidateFamily_cell_subset_domain
          (G := G) (Ω := Ω) (a := a) (K := K)
          (hΩ := hΩ) hP⟩
    exact (not_containsGridCellAtLevel_lt_firstContainedLevel
      G hΩcell hk hcontains).elim
  · intro hP
    simp at hP

/-- The candidate family obtained from strong decompositions tiles the domain. -/
private theorem stronglyRegularCandidateFamily_cover
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a K : ℝ}
    {hΩ : StronglyRegularDomain G Ω a K 0} :
    Ω = ⋃ k, ⋃ P ∈ stronglyRegularCandidateFamily G Ω a K hΩ k, (P : Set α) := by
  classical
  ext z
  constructor
  · intro hzΩ
    let k₀ := firstContainedLevel G Ω
    have hzcover : z ∈ ⋃ Q ∈ G.toWeakGridSpace.grid.partitions k₀, Q := by
      change z ∈ ⋃ Q ∈ G.grid.grid.partitions k₀, Q
      rw [G.grid.grid.covering k₀]
      exact Set.mem_univ z
    rcases Set.mem_iUnion₂.mp hzcover with ⟨Q, hQ, hzQ⟩
    let D := stronglyRegularRootDecomposition hΩ Q hQ
    have hz_inter : z ∈ Q ∩ Ω := ⟨hzQ, hzΩ⟩
    rw [D.cover] at hz_inter
    rcases Set.mem_iUnion.mp hz_inter with ⟨k, hz_inter⟩
    rcases Set.mem_iUnion.mp hz_inter with ⟨P, hz_inter⟩
    rcases Set.mem_iUnion.mp hz_inter with ⟨hP, hzP⟩
    have hP_candidate :
        P ∈ stronglyRegularCandidateFamily G Ω a K hΩ k := by
      simp only [stronglyRegularCandidateFamily]
      refine Finset.mem_biUnion.mpr ⟨Q, hQ, ?_⟩
      change P ∈
        (if hQ' : Q ∈ G.toWeakGridSpace.grid.partitions
            (firstContainedLevel G Ω) then
          (stronglyRegularRootDecomposition hΩ Q hQ').family k
        else ∅)
      rw [dif_pos hQ]
      exact hP
    exact Set.mem_iUnion.mpr
      ⟨k, Set.mem_iUnion.mpr
        ⟨P, Set.mem_iUnion.mpr ⟨hP_candidate, hzP⟩⟩⟩
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨k, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨P, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hP, hzP⟩
    exact stronglyRegularCandidateFamily_cell_subset_domain
      (G := G) (Ω := Ω) (a := a) (K := K) (hΩ := hΩ) hP hzP

/-- Distinct selected cells in the candidate family are disjoint. -/
private theorem stronglyRegularCandidateFamily_pairwise_disjoint
    {G : GoodGridSpace (α := α)} {Ω : Set α} {a K : ℝ}
    {hΩ : StronglyRegularDomain G Ω a K 0}
    {k l : ℕ} {P R : Set α}
    (hP : P ∈ stronglyRegularCandidateFamily G Ω a K hΩ k)
    (hR : R ∈ stronglyRegularCandidateFamily G Ω a K hΩ l)
    (hPR : P ≠ R) :
    Disjoint P R := by
  classical
  let k₀ := firstContainedLevel G Ω
  simp only [stronglyRegularCandidateFamily] at hP hR
  rcases Finset.mem_biUnion.mp hP with ⟨Q, hQ, hPQ⟩
  rcases Finset.mem_biUnion.mp hR with ⟨W, hW, hRW⟩
  have hPQ' :
      P ∈ (stronglyRegularRootDecomposition hΩ Q hQ).family k := by
    simpa [hQ] using hPQ
  have hRW' :
      R ∈ (stronglyRegularRootDecomposition hΩ W hW).family l := by
    simpa [hW] using hRW
  by_cases hQW : Q = W
  · subst hQW
    have hW_eq_hQ : hW = hQ := Subsingleton.elim _ _
    have hRW'' :
        R ∈ (stronglyRegularRootDecomposition hΩ Q hQ).family l := by
      simpa [hW_eq_hQ] using hRW'
    exact (stronglyRegularRootDecomposition hΩ Q hQ).pairwise_disjoint
      k l P R hPQ' hRW'' hPR
  · have hroot_disjoint : Disjoint Q W :=
      G.grid.grid.disjoint k₀ Q W (by simpa using hQ) (by simpa using hW) hQW
    exact hroot_disjoint.mono
      ((stronglyRegularRootDecomposition hΩ Q hQ).cell_subset_cell hPQ')
      ((stronglyRegularRootDecomposition hΩ W hW).cell_subset_cell hRW')

/-- Lower companion of `cell_measure_le_lambda2_pow_mul_univ`: every level-`n`
cell has measure at least `λ₁^n` times the measure of the whole space. -/
private theorem cell_measure_ge_lambda1_pow_mul_univ
    (G : GoodGridSpace (α := α)) :
    ∀ (n : ℕ) (Q : Set α), Q ∈ G.grid.grid.partitions n →
      (ENNReal.ofReal G.grid.lambda1) ^ n * G.grid.μ Set.univ ≤ G.grid.μ Q
  | 0, Q, hQ => by
      have hQ_univ : Q = Set.univ := by
        have hmem : Q ∈ ({Set.univ} : Finset (Set α)) := by
          simpa [G.grid.grid.first_partition_eq_univ] using hQ
        simpa using hmem
      subst hQ_univ
      simp
  | n + 1, Q, hQ => by
      obtain ⟨P, hP, hQP⟩ := G.grid.grid.nested n Q hQ
      have hstep :
          ENNReal.ofReal G.grid.lambda1 * G.grid.μ P ≤ G.grid.μ Q :=
        G.grid.ratio_lower n Q P hQ hP hQP
      have hind :
          (ENNReal.ofReal G.grid.lambda1) ^ n * G.grid.μ Set.univ ≤ G.grid.μ P :=
        cell_measure_ge_lambda1_pow_mul_univ G n P hP
      calc
        (ENNReal.ofReal G.grid.lambda1) ^ (n + 1) * G.grid.μ Set.univ
            = ENNReal.ofReal G.grid.lambda1 *
                ((ENNReal.ofReal G.grid.lambda1) ^ n * G.grid.μ Set.univ) := by
              rw [pow_succ]; ring
        _ ≤ ENNReal.ofReal G.grid.lambda1 * G.grid.μ P := by gcongr
        _ ≤ G.grid.μ Q := hstep

/-- The cells of the level-`n` partition cover the whole space, so their
measures sum to the total measure. -/
private theorem partition_measure_sum
    (G : GoodGridSpace (α := α)) (n : ℕ) :
    ∑ Q ∈ G.grid.grid.partitions n, G.grid.μ Q = G.grid.μ Set.univ := by
  classical
  have hdisj :
      (↑(G.grid.grid.partitions n) : Set (Set α)).PairwiseDisjoint
        (id : Set α → Set α) := by
    intro P hP W hW hPW
    simpa using
      G.grid.grid.disjoint n P W (by simpa using hP) (by simpa using hW) hPW
  have hmeas :
      ∀ P ∈ G.grid.grid.partitions n, MeasurableSet ((id : Set α → Set α) P) :=
    fun P hP => G.grid.grid.measurable n P hP
  have hbu :=
    MeasureTheory.measure_biUnion_finset (μ := G.grid.μ) hdisj hmeas
  simp only [id_eq] at hbu
  rw [← hbu, G.grid.grid.covering n]

/--
Quantitative core of `regularDomain_of_stronglyRegularDomain`: the candidate
family obtained from the strong decompositions of `Q ∩ Ω` over the level
`k₀(Ω)` partition converts the strong `1 - βp` cost into the regular `1 - sp`
level cost, with geometric ratio `λ₂^{(β-s)p}` and constant `K · λ₁^{-k₀(Ω)}`.
-/
private theorem stronglyRegularCandidateFamily_cost
    {G : GoodGridSpace (α := α)} {Ω : Set α} {s β K : ℝ} {p : ℝ≥0∞}
    (hsβ : s < β) (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hΩcell : ContainsGridCell G Ω)
    (hΩ : StronglyRegularDomain G Ω (1 - β * p.toReal) K 0) (k : ℕ) :
    (∑ Q ∈ stronglyRegularCandidateFamily G Ω (1 - β * p.toReal) K hΩ k,
        (G.grid.μ Q).toReal ^ (1 - s * p.toReal)) ≤
      K * (G.grid.lambda1 ^ firstContainedLevel G Ω)⁻¹ *
        (G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω) *
        (G.grid.μ Ω).toReal ^ (1 - s * p.toReal) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  letI : MeasureTheory.IsFiniteMeasure G.toWeakGridSpace.measure := G.grid.isFinite
  -- Real exponent bookkeeping.
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hsp_lt_one : s * p.toReal < 1 := by
    have h := mul_lt_mul_of_pos_right hs_lt_inv hpr
    rwa [inv_mul_cancel₀ hpr.ne'] at h
  have ha_pos : 0 < 1 - s * p.toReal := by linarith
  have hsp_pos : 0 < s * p.toReal := mul_pos hs hpr
  have hθ_pos : 0 < (β - s) * p.toReal := mul_pos (by linarith) hpr
  have hθ_nonneg : 0 ≤ (β - s) * p.toReal := hθ_pos.le
  have hlam1pos : 0 < G.grid.lambda1 := G.grid.hlambda1_pos
  have hlam2pos : 0 < G.grid.lambda2 :=
    lt_of_lt_of_le hlam1pos G.grid.hlambda1_le_lambda2
  have hK : 0 ≤ K := hΩ.nonneg_K
  have hμ0pos : 0 < (G.grid.μ Set.univ).toReal := by
    have huniv : Set.univ ∈ G.grid.grid.partitions 0 := by
      rw [G.grid.grid.first_partition_eq_univ]; exact Finset.mem_singleton_self _
    exact ENNReal.toReal_pos (G.grid.positive_measure 0 Set.univ huniv).ne'
      (measure_ne_top G.grid.μ _)
  -- The lower bound `λ₁^{k₀} μ(I) ≤ μ(Ω)`, via a level-`k₀` cell inside `Ω`.
  obtain ⟨W, hWsub⟩ := firstContainedLevel_spec G hΩcell
  have hWlowR :
      G.grid.lambda1 ^ (firstContainedLevel G Ω) * (G.grid.μ Set.univ).toReal
        ≤ (G.grid.μ Ω).toReal := by
    have hraw :
        (ENNReal.ofReal G.grid.lambda1) ^ (firstContainedLevel G Ω) * G.grid.μ Set.univ
          ≤ G.grid.μ Ω :=
      le_trans
        (cell_measure_ge_lambda1_pow_mul_univ G (firstContainedLevel G Ω) W.1 W.2)
        (measure_mono hWsub)
    have h := (ENNReal.toReal_le_toReal
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          (measure_ne_top G.grid.μ _)) (measure_ne_top G.grid.μ Ω)).mpr hraw
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hlam1pos.le] using h
  -- The level-`k₀` root cells convert their cost into a `μ(Ω)^{a}` bound.
  have hroot :
      (∑ Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω),
          (G.grid.μ Q).toReal ^ (1 - s * p.toReal))
        ≤ (G.grid.lambda1 ^ firstContainedLevel G Ω)⁻¹
            * (G.grid.μ Ω).toReal ^ (1 - s * p.toReal) := by
    set L := G.grid.lambda1 ^ (firstContainedLevel G Ω) with hLdef
    set μ₀ := (G.grid.μ Set.univ).toReal with hμ₀def
    have hL : 0 < L := by rw [hLdef]; exact pow_pos hlam1pos _
    have hsumμ :
        (∑ Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω), (G.grid.μ Q).toReal)
          = μ₀ := by
      rw [← ENNReal.toReal_sum (fun Q _ => measure_ne_top G.grid.μ Q),
          partition_measure_sum G (firstContainedLevel G Ω)]
    have hμ0_le : μ₀ ≤ L⁻¹ * (G.grid.μ Ω).toReal := by
      rw [← inv_mul_cancel_left₀ hL.ne' μ₀]
      exact mul_le_mul_of_nonneg_left hWlowR (inv_nonneg.mpr hL.le)
    have hμpow : μ₀ ^ (1 - s * p.toReal - 1) * μ₀ = μ₀ ^ (1 - s * p.toReal) := by
      have h := Real.rpow_add hμ0pos (1 - s * p.toReal - 1) 1
      rw [Real.rpow_one] at h
      rw [← h]; congr 1; ring
    have hconst :
        L ^ (1 - s * p.toReal - 1) * (L⁻¹) ^ (1 - s * p.toReal) = L⁻¹ := by
      rw [Real.inv_rpow hL.le,
          show (1 - s * p.toReal - 1) = (1 - s * p.toReal) + (-1) from by ring,
          Real.rpow_add hL, Real.rpow_neg_one, mul_right_comm,
          mul_inv_cancel₀ (Real.rpow_pos_of_pos hL (1 - s * p.toReal)).ne', one_mul]
    have hterm : ∀ Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω),
        (G.grid.μ Q).toReal ^ (1 - s * p.toReal)
          ≤ (L * μ₀) ^ (1 - s * p.toReal - 1) * (G.grid.μ Q).toReal := by
      intro Q hQ
      have hQpos : 0 < (G.grid.μ Q).toReal :=
        ENNReal.toReal_pos (G.grid.positive_measure _ Q hQ).ne'
          (measure_ne_top G.grid.μ Q)
      have hQlow : L * μ₀ ≤ (G.grid.μ Q).toReal := by
        have hraw := cell_measure_ge_lambda1_pow_mul_univ G (firstContainedLevel G Ω) Q hQ
        have h := (ENNReal.toReal_le_toReal
            (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
              (measure_ne_top G.grid.μ _)) (measure_ne_top G.grid.μ Q)).mpr hraw
        simpa [ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal hlam1pos.le, hLdef, hμ₀def] using h
      have hmpos : 0 < L * μ₀ := mul_pos hL hμ0pos
      have hsplit : (G.grid.μ Q).toReal ^ (1 - s * p.toReal)
          = (G.grid.μ Q).toReal ^ (1 - s * p.toReal - 1) * (G.grid.μ Q).toReal := by
        have h := Real.rpow_add hQpos (1 - s * p.toReal - 1) 1
        rw [Real.rpow_one] at h
        rw [← h]; congr 1; ring
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hmpos hQlow (by linarith)) hQpos.le
    calc
      (∑ Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω),
          (G.grid.μ Q).toReal ^ (1 - s * p.toReal))
          ≤ ∑ Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω),
              (L * μ₀) ^ (1 - s * p.toReal - 1) * (G.grid.μ Q).toReal :=
            Finset.sum_le_sum hterm
      _ = (L * μ₀) ^ (1 - s * p.toReal - 1) *
            ∑ Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω), (G.grid.μ Q).toReal := by
            rw [← Finset.mul_sum]
      _ = (L * μ₀) ^ (1 - s * p.toReal - 1) * μ₀ := by rw [hsumμ]
      _ = L ^ (1 - s * p.toReal - 1) * μ₀ ^ (1 - s * p.toReal) := by
            rw [Real.mul_rpow hL.le hμ0pos.le, mul_assoc, hμpow]
      _ ≤ L ^ (1 - s * p.toReal - 1) *
            (L⁻¹ * (G.grid.μ Ω).toReal) ^ (1 - s * p.toReal) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hL.le _)
            exact Real.rpow_le_rpow hμ0pos.le hμ0_le ha_pos.le
      _ = L⁻¹ * (G.grid.μ Ω).toReal ^ (1 - s * p.toReal) := by
            rw [Real.mul_rpow (inv_nonneg.mpr hL.le) ENNReal.toReal_nonneg,
                ← mul_assoc, hconst]
  -- `λ₂^{(k-k₀)(β-s)p}` written as a power of the geometric ratio.
  have hcpow :
      (G.grid.lambda2 ^ (k - firstContainedLevel G Ω)) ^ ((β - s) * p.toReal)
        = (G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω) := by
    rw [← Real.rpow_natCast G.grid.lambda2 (k - firstContainedLevel G Ω),
        ← Real.rpow_natCast (G.grid.lambda2 ^ ((β - s) * p.toReal))
            (k - firstContainedLevel G Ω),
        ← Real.rpow_mul hlam2pos.le, ← Real.rpow_mul hlam2pos.le,
        mul_comm (↑(k - firstContainedLevel G Ω) : ℝ) ((β - s) * p.toReal)]
  -- The candidate family is the disjoint union of the root decompositions.
  have hbiU :
      stronglyRegularCandidateFamily G Ω (1 - β * p.toReal) K hΩ k
        = (G.grid.grid.partitions (firstContainedLevel G Ω)).biUnion
            (fun Q => if hQ : Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω)
              then (stronglyRegularRootDecomposition hΩ Q hQ).family k else ∅) := rfl
  have hdisj :
      (↑(G.grid.grid.partitions (firstContainedLevel G Ω)) : Set (Set α)).PairwiseDisjoint
        (fun Q => if hQ : Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω)
          then (stronglyRegularRootDecomposition hΩ Q hQ).family k else ∅) := by
    intro Q hQmem W hWmem hQW
    simp only [Finset.mem_coe] at hQmem hWmem
    rw [Function.onFun, dif_pos hQmem, dif_pos hWmem, Finset.disjoint_left]
    intro P hPQ hPW
    have hPsubQ : P ⊆ Q :=
      (stronglyRegularRootDecomposition hΩ Q hQmem).cell_subset_cell hPQ
    have hPsubW : P ⊆ W :=
      (stronglyRegularRootDecomposition hΩ W hWmem).cell_subset_cell hPW
    have hPk : P ∈ G.grid.grid.partitions k :=
      (stronglyRegularRootDecomposition hΩ Q hQmem).family_subset k hPQ
    obtain ⟨x, hx⟩ := G.grid.partition_nonempty k P hPk
    exact Set.disjoint_left.mp
      (G.grid.grid.disjoint (firstContainedLevel G Ω) Q W hQmem hWmem hQW)
      (hPsubQ hx) (hPsubW hx)
  by_cases hk : k < firstContainedLevel G Ω
  · -- Below `k₀(Ω)` the candidate family is empty.
    rw [stronglyRegularCandidateFamily_empty_before
        (G := G) (Ω := Ω) (a := 1 - β * p.toReal) (K := K)
        (hΩcell := hΩcell) (hΩ := hΩ) hk, Finset.sum_empty]
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg hK (inv_nonneg.mpr (pow_nonneg hlam1pos.le _))
      · exact pow_nonneg (Real.rpow_nonneg hlam2pos.le _) _
    · exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  · push_neg at hk
    -- Per root cell `Q`: convert the strong cost into the regular cost.
    have hinner : ∀ Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω),
        (∑ P ∈ (if hQ : Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω)
                  then (stronglyRegularRootDecomposition hΩ Q hQ).family k else ∅),
            (G.grid.μ P).toReal ^ (1 - s * p.toReal))
          ≤ K * (G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω)
              * (G.grid.μ Q).toReal ^ (1 - s * p.toReal) := by
      intro Q hQ
      rw [dif_pos hQ]
      set D := stronglyRegularRootDecomposition hΩ Q hQ with hDdef
      have hQpos : 0 < (G.grid.μ Q).toReal :=
        ENNReal.toReal_pos (G.grid.positive_measure _ Q hQ).ne'
          (measure_ne_top G.grid.μ Q)
      have hbound : ∀ P ∈ D.family k,
          (G.grid.μ P).toReal ^ (1 - s * p.toReal)
            ≤ (G.grid.μ P).toReal ^ (1 - β * p.toReal)
                * ((G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω)
                    * (G.grid.μ Q).toReal ^ ((β - s) * p.toReal)) := by
        intro P hP
        have hPk : P ∈ G.grid.grid.partitions k := D.family_subset k hP
        have hPpos : 0 < (G.grid.μ P).toReal :=
          ENNReal.toReal_pos (G.grid.positive_measure _ P hPk).ne'
            (measure_ne_top G.grid.μ P)
        have hPsub : P ⊆ Q := D.cell_subset_cell hP
        have hPlvl : P ∈ G.grid.grid.partitions
            (firstContainedLevel G Ω + (k - firstContainedLevel G Ω)) := by
          rwa [Nat.add_sub_cancel' hk]
        have hμP_le : (G.grid.μ P).toReal
            ≤ G.grid.lambda2 ^ (k - firstContainedLevel G Ω) * (G.grid.μ Q).toReal := by
          have hraw := cell_measure_le_lambda2_pow_mul_cell G
            ⟨firstContainedLevel G Ω, Q, hQ⟩ (k - firstContainedLevel G Ω) P hPlvl hPsub
          have h := (ENNReal.toReal_le_toReal (measure_ne_top G.grid.μ P)
              (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
                (measure_ne_top G.grid.μ _))).mpr hraw
          simpa [ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal hlam2pos.le] using h
        have hsplitP : (G.grid.μ P).toReal ^ (1 - s * p.toReal)
            = (G.grid.μ P).toReal ^ (1 - β * p.toReal)
                * (G.grid.μ P).toReal ^ ((β - s) * p.toReal) := by
          rw [← Real.rpow_add hPpos]; congr 1; ring
        rw [hsplitP]
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hPpos.le _)
        calc (G.grid.μ P).toReal ^ ((β - s) * p.toReal)
            ≤ (G.grid.lambda2 ^ (k - firstContainedLevel G Ω) * (G.grid.μ Q).toReal)
                ^ ((β - s) * p.toReal) :=
              Real.rpow_le_rpow hPpos.le hμP_le hθ_nonneg
          _ = (G.grid.lambda2 ^ (k - firstContainedLevel G Ω)) ^ ((β - s) * p.toReal)
                * (G.grid.μ Q).toReal ^ ((β - s) * p.toReal) :=
              Real.mul_rpow (pow_nonneg hlam2pos.le _) ENNReal.toReal_nonneg
          _ = (G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω)
                * (G.grid.μ Q).toReal ^ ((β - s) * p.toReal) := by rw [hcpow]
      calc
        (∑ P ∈ D.family k, (G.grid.μ P).toReal ^ (1 - s * p.toReal))
            ≤ ∑ P ∈ D.family k, (G.grid.μ P).toReal ^ (1 - β * p.toReal)
                * ((G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω)
                    * (G.grid.μ Q).toReal ^ ((β - s) * p.toReal)) :=
              Finset.sum_le_sum hbound
        _ = (∑ P ∈ D.family k, (G.grid.μ P).toReal ^ (1 - β * p.toReal))
                * ((G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω)
                    * (G.grid.μ Q).toReal ^ ((β - s) * p.toReal)) := by
              rw [← Finset.sum_mul]
        _ ≤ (K * (G.grid.μ Q).toReal ^ (1 - β * p.toReal))
                * ((G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω)
                    * (G.grid.μ Q).toReal ^ ((β - s) * p.toReal)) := by
              apply mul_le_mul_of_nonneg_right (D.cost k)
              exact mul_nonneg (pow_nonneg (Real.rpow_nonneg hlam2pos.le _) _)
                (Real.rpow_nonneg ENNReal.toReal_nonneg _)
        _ = K * (G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω)
                * (G.grid.μ Q).toReal ^ (1 - s * p.toReal) := by
              rw [show (1 - s * p.toReal) = (1 - β * p.toReal) + (β - s) * p.toReal from by ring,
                  Real.rpow_add hQpos]
              ring
    calc
      (∑ Q ∈ stronglyRegularCandidateFamily G Ω (1 - β * p.toReal) K hΩ k,
          (G.grid.μ Q).toReal ^ (1 - s * p.toReal))
          = ∑ Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω),
              (∑ P ∈ (if hQ : Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω)
                    then (stronglyRegularRootDecomposition hΩ Q hQ).family k else ∅),
                (G.grid.μ P).toReal ^ (1 - s * p.toReal)) := by
            rw [hbiU, Finset.sum_biUnion hdisj]
      _ ≤ ∑ Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω),
            K * (G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω)
              * (G.grid.μ Q).toReal ^ (1 - s * p.toReal) :=
            Finset.sum_le_sum hinner
      _ = K * (G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω)
            * ∑ Q ∈ G.grid.grid.partitions (firstContainedLevel G Ω),
                (G.grid.μ Q).toReal ^ (1 - s * p.toReal) := by
            rw [← Finset.mul_sum]
      _ ≤ K * (G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω)
            * ((G.grid.lambda1 ^ firstContainedLevel G Ω)⁻¹
                * (G.grid.μ Ω).toReal ^ (1 - s * p.toReal)) := by
            apply mul_le_mul_of_nonneg_left hroot
            exact mul_nonneg hK (pow_nonneg (Real.rpow_nonneg hlam2pos.le _) _)
      _ = K * (G.grid.lambda1 ^ firstContainedLevel G Ω)⁻¹
            * (G.grid.lambda2 ^ ((β - s) * p.toReal)) ^ (k - firstContainedLevel G Ω)
            * (G.grid.μ Ω).toReal ^ (1 - s * p.toReal) := by ring

/--
Quantitative version of the proposition after the definition of regular
domains.

If `β > s`, every `(1 - βp, K, 0)`-strongly regular domain which contains a
grid cell is regular with exponent `1 - sp` and geometric ratio
`λ₂ ^ ((β - s) p)`, for some constant depending on the domain and the grid.
Here `λ₂` is the upper child-to-parent measure ratio of the good grid.
-/
theorem regularDomain_of_stronglyRegularDomain
    (G : GoodGridSpace (α := α)) (Ω : Set α) (s β K : ℝ) (p : ℝ≥0∞)
    (hsβ : s < β) (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hΩcell : ContainsGridCell G Ω)
    (hΩ : StronglyRegularDomain G Ω (1 - β * p.toReal) K 0) :
    ∃ C' : ℝ,
      0 ≤ C' ∧
      Nonempty (RegularDomain G Ω (1 - s * p.toReal) C'
        (G.grid.lambda2 ^ ((β - s) * p.toReal))) := by
  classical
  let aStrong : ℝ := 1 - β * p.toReal
  let F : ℕ → Finset (Set α) :=
    stronglyRegularCandidateFamily G Ω aStrong K hΩ
  let C' : ℝ := K * (G.grid.lambda1 ^ firstContainedLevel G Ω)⁻¹
  have hC' : 0 ≤ C' :=
    mul_nonneg hΩ.nonneg_K (inv_nonneg.mpr (pow_nonneg G.grid.hlambda1_pos.le _))
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hθ_pos : 0 < (β - s) * p.toReal := mul_pos (by linarith) hpr
  have hlambda2_nonneg : 0 ≤ G.grid.lambda2 :=
    G.grid.hlambda1_pos.le.trans G.grid.hlambda1_le_lambda2
  have hratio_nonneg : 0 ≤ G.grid.lambda2 ^ ((β - s) * p.toReal) :=
    Real.rpow_nonneg hlambda2_nonneg _
  have hratio_lt_one : G.grid.lambda2 ^ ((β - s) * p.toReal) < 1 :=
    Real.rpow_lt_one hlambda2_nonneg G.grid.hlambda2_lt_one hθ_pos
  refine ⟨C', hC', ?_⟩
  refine ⟨
    { measurable := hΩ.1
      contains_cell := hΩcell
      C_nonneg := hC'
      c_nonneg := hratio_nonneg
      c_lt_one := hratio_lt_one
      family := F
      family_subset := ?_
      family_empty_before := ?_
      cover := ?_
      pairwise_disjoint_cells := ?_
      cost := ?_ }⟩
  · intro k
    exact stronglyRegularCandidateFamily_subset
      (G := G) (Ω := Ω) (a := aStrong) (K := K)
      (hΩ := hΩ) k
  · intro k hk
    exact stronglyRegularCandidateFamily_empty_before
      (G := G) (Ω := Ω) (a := aStrong) (K := K)
      (hΩcell := hΩcell) (hΩ := hΩ) hk
  · change Ω =
      ⋃ k, ⋃ Q ∈ stronglyRegularCandidateFamily G Ω aStrong K hΩ k, (Q : Set α)
    exact stronglyRegularCandidateFamily_cover
      (G := G) (Ω := Ω) (a := aStrong) (K := K) (hΩ := hΩ)
  · intro k l P Q hP hQ hPQ
    exact stronglyRegularCandidateFamily_pairwise_disjoint
      (G := G) (Ω := Ω) (a := aStrong) (K := K)
      (hΩ := hΩ) hP hQ hPQ
  · intro k
    exact stronglyRegularCandidateFamily_cost hsβ hs hs_lt_inv hp hp_top hΩcell hΩ k

section RestrictionCost

variable (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
variable {hs : 0 < s} {hp : 1 ≤ p} {hp_top : p ≠ ∞}
variable [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/--
The level-`j` aggregated coefficient power appearing in estimate `(hiip1)`:
sum over all active `r` and all level-`j` cells of the `p`-power of the
localized restriction coefficients.
-/
noncomputable def regularFamilyRestrictionLevelCoeffPower
    (Λ : Set ℕ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) →
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        ((y i : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q) :
          Lp ℂ p G.toWeakGridSpace.measure))
    (j : ℕ) : ℝ :=
  ∑' i : ℕ,
    Set.indicator Λ
      (fun i =>
        ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
          ‖((R i).block j).coeff Q‖ ^ p.toReal) i

/--
The mixed `(p,q)` coefficient gauge from `(hiip1)`.  For `q = ∞` it is the
supremum of the level roots; otherwise it is the usual `ℓ^q` norm of those
roots.
-/
noncomputable def regularFamilyRestrictionCost
    (Λ : Set ℕ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) →
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        ((y i : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q) :
          Lp ℂ p G.toWeakGridSpace.measure)) : ℝ :=
  if q = ∞ then
    sSup (Set.range fun j : ℕ =>
      (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^ (1 / p.toReal))
  else
    (∑' j : ℕ,
      (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
        (q.toReal / p.toReal)) ^ (1 / q.toReal)

private theorem regularFamilyRestrictionLevelCoeffPower_nonneg
    (Λ : Set ℕ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) →
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        ((y i : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q) :
          Lp ℂ p G.toWeakGridSpace.measure))
    (j : ℕ) :
    0 ≤ regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j := by
  unfold regularFamilyRestrictionLevelCoeffPower
  exact tsum_nonneg fun i => by
    by_cases hi : i ∈ Λ
    · rw [Set.indicator_of_mem hi]
      exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
    · rw [Set.indicator_of_notMem hi]

end RestrictionCost

section RegularFamilyIndicatorBlocks

variable (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
variable (s C c : ℝ) (p q : ℝ≥0∞)
variable {hs : 0 < s} {hp : 1 ≤ p} {hp_top : p ≠ ∞}
variable [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/--
The canonical level block for the indicator of one member of a regular family.

On selected cells `Q ∈ ℱᵏ(Ωᵢ)` the coefficient is `|Q|^{1/p-s}` and the atom is
the canonical Souza atom `|Q|^{s-1/p} 1_Q`, so the product is exactly `1_Q`.
Outside the selected family the coefficient is zero.
-/
noncomputable def regularFamilyIndicatorBlock
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (i k : ℕ) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k where
  coeff := fun P =>
    if P.1 ∈ hΩ.family i k then
      (((G.grid.μ P.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ) else 0
  atom := fun P => (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)
  atom_mem := fun P => by
    change ‖((((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ)) : ℂ)‖
      ≤ (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹)
    simp [Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]

/-- A nonzero indicator coefficient is attached to a selected regular-family
cell. -/
theorem regularFamilyIndicatorBlock_coeff_ne_zero_mem
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (hcoeff : (regularFamilyIndicatorBlock (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff Q ≠ 0) :
    Q.1 ∈ hΩ.family i k := by
  classical
  by_contra hQ
  exact hcoeff (by simp [regularFamilyIndicatorBlock, hQ])

/-- The canonical indicator block of a regular-family member is positive:
its coefficients are nonnegative real numbers and its atoms are the canonical
Souza atoms. -/
theorem regularFamilyIndicatorBlock_positive
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (i k : ℕ) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (regularFamilyIndicatorBlock
        (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k) := by
  classical
  intro Q
  have hatom :
      (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          ((regularFamilyIndicatorBlock
            (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).atom Q) =
        canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) := by
    funext x
    change
      (Q.1.indicator
        (fun _ =>
          (((G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x) =
        canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) x
    by_cases hx : x ∈ Q.1
    · simp [canonicalSouzaAtom, goodGridCellOfLevelCell,
        hx]
    · simp [canonicalSouzaAtom, goodGridCellOfLevelCell,
        hx]
  by_cases hQ : Q.1 ∈ hΩ.family i k
  · refine ⟨(G.grid.μ Q.1).toReal ^ ((p.toReal)⁻¹ - s), ?_, ?_, ?_⟩
    · exact Real.rpow_nonneg ENNReal.toReal_nonneg _
    · simp [regularFamilyIndicatorBlock, hQ]
    · exact hatom
  · refine ⟨0, le_rfl, ?_, ?_⟩
    · simp [regularFamilyIndicatorBlock, hQ]
    · exact hatom

/-- A nonzero active indicator coefficient lives on a cell contained in the
corresponding regular-family domain. -/
theorem regularFamilyIndicatorBlock_coeff_ne_zero_subset_domain
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i k : ℕ} (hi : i ∈ Λ)
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (hcoeff : (regularFamilyIndicatorBlock (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff Q ≠ 0) :
    Q.1 ⊆ Ω i :=
  hΩ.cell_subset_domain hi
      (regularFamilyIndicatorBlock_coeff_ne_zero_mem
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ Q hcoeff)

/-- The level coefficient power of the indicator block is exactly the regular
family level cost for that member. -/
theorem regularFamilyIndicatorBlock_levelCoeffPower
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i k : ℕ} (hi : i ∈ Λ) :
    (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(regularFamilyIndicatorBlock (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff P‖ ^ p.toReal)
      = ∑ Q ∈ hΩ.family i k, (G.grid.μ Q).toReal ^ (1 - p.toReal * s) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hexp : ((p.toReal)⁻¹ - s) * p.toReal = 1 - p.toReal * s := by
    rw [sub_mul, inv_mul_cancel₀ hpr.ne']; ring
  have hterm : ∀ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ‖(regularFamilyIndicatorBlock (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff P‖ ^ p.toReal
        = if P.1 ∈ hΩ.family i k then
            (G.grid.μ P.1).toReal ^ (1 - p.toReal * s) else 0 := by
    intro P
    by_cases hP : P.1 ∈ hΩ.family i k
    · simp only [regularFamilyIndicatorBlock, hP, if_true]
      rw [Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _),
        ← Real.rpow_mul ENNReal.toReal_nonneg, hexp]
    · simp only [regularFamilyIndicatorBlock, hP, if_false, norm_zero,
        Real.zero_rpow hpr.ne']
  rw [Finset.sum_congr rfl (fun P _ => hterm P),
    Finset.sum_coe_sort (G.toWeakGridSpace.grid.partitions k)
      (fun Q => if Q ∈ hΩ.family i k then
        (G.grid.μ Q).toReal ^ (1 - p.toReal * s) else 0),
    ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr (hΩ.family_subset i hi k)]

/-- The indicator block represents the finite union of the selected cells at
that level. -/
theorem regularFamilyIndicatorBlock_represents_levelTile
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i k : ℕ} (hi : i ∈ Λ) :
    WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p)
      ((⋃ Q ∈ hΩ.family i k, (Q : Set α)).indicator fun _ => (1 : ℂ))
      ((regularFamilyIndicatorBlock
        (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).toLp
          (souzaAtomFamily G s p hs hp hp_top)) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  letI : MeasureTheory.IsFiniteMeasure G.toWeakGridSpace.measure := G.grid.isFinite
  let A := souzaAtomFamily G s p hs hp hp_top
  let B := regularFamilyIndicatorBlock
    (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k
  refine (WeakGridSpace.LevelBlock.coeFn_toLp A B).trans ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  unfold WeakGridSpace.LevelBlock.toFunLt
  by_cases hx : x ∈ ⋃ Q ∈ hΩ.family i k, (Q : Set α)
  · rcases Set.mem_iUnion₂.mp hx with ⟨Q₀, hQ₀, hxQ₀⟩
    rw [Set.indicator_of_mem hx,
      Finset.sum_eq_single ⟨Q₀, hΩ.family_subset i hi k hQ₀⟩]
    · have hQ₀pos : 0 < (G.grid.μ Q₀).toReal :=
        ENNReal.toReal_pos
          (G.grid.positive_measure _ Q₀ (hΩ.family_subset i hi k hQ₀)).ne'
          (measure_ne_top _ _)
      simp only [B, regularFamilyIndicatorBlock, A, WeakGridSpace.AtomFamily.toFunction,
        souzaAtomFamily, souzaLocalVectorSpace, hQ₀, if_true]
      change (((G.grid.μ Q₀).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
        * (Q₀.indicator
            (fun _ => (((G.grid.μ Q₀).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x) = 1
      rw [Set.indicator_of_mem hxQ₀, ← Complex.ofReal_mul,
        ← Real.rpow_add hQ₀pos,
        show ((p.toReal)⁻¹ - s) + (s - (p.toReal)⁻¹) = 0 from by ring,
        Real.rpow_zero, Complex.ofReal_one]
    · intro P _ hPne
      by_cases hPfam : P.1 ∈ hΩ.family i k
      · have hxP : x ∉ P.1 := by
          intro hxP
          exact Set.disjoint_left.mp
            (hΩ.pairwise_disjoint_cells i hi k k P.1 Q₀ hPfam hQ₀
              (fun h => hPne (Subtype.ext h))) hxP hxQ₀
        simp only [B, regularFamilyIndicatorBlock, A, WeakGridSpace.AtomFamily.toFunction,
          souzaAtomFamily, souzaLocalVectorSpace, hPfam, if_true]
        change (((G.grid.μ P.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
          * ((P.1).indicator
              (fun _ => (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x) = 0
        rw [Set.indicator_of_notMem hxP, mul_zero]
      · simp only [B, regularFamilyIndicatorBlock, hPfam, if_false, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_attach _ _) hnot
  · rw [Set.indicator_of_notMem hx]
    refine Finset.sum_eq_zero ?_
    intro P _
    by_cases hPfam : P.1 ∈ hΩ.family i k
    · have hxP : x ∉ P.1 := fun hxP =>
        hx (Set.mem_iUnion₂.mpr ⟨P.1, hPfam, hxP⟩)
      simp only [B, regularFamilyIndicatorBlock, A, WeakGridSpace.AtomFamily.toFunction,
        souzaAtomFamily, souzaLocalVectorSpace, hPfam, if_true]
      change (((G.grid.μ P.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
        * ((P.1).indicator
            (fun _ => (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x) = 0
      rw [Set.indicator_of_notMem hxP, mul_zero]
    · simp only [B, regularFamilyIndicatorBlock, hPfam, if_false, zero_mul]

/-- The regular-family hypothesis controls the aggregate level coefficient
power of the indicator blocks. -/
theorem regularFamilyIndicatorBlock_aggregate_levelCoeffPower_le
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (k : ℕ) :
    (∑' i : ℕ,
      Set.indicator Λ
        (fun i =>
          ∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            ‖(regularFamilyIndicatorBlock
              (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff P‖ ^
              p.toReal) i) ≤
      C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
        (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s) := by
  classical
  have hterm : ∀ i,
      Set.indicator Λ
        (fun i =>
          ∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            ‖(regularFamilyIndicatorBlock
              (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff P‖ ^
              p.toReal) i =
      Set.indicator Λ
        (fun i => ∑ Q ∈ hΩ.family i k, (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) i := by
    intro i
    by_cases hi : i ∈ Λ
    · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
      exact regularFamilyIndicatorBlock_levelCoeffPower
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) hΩ hi
    · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi]
  rw [tsum_congr hterm]
  exact hΩ.cost k

/-- The canonical indicator block for one active member is bounded by the
aggregate regular-family level cost. -/
theorem regularFamilyIndicatorBlock_levelCoeffPower_le_familyCost
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i k : ℕ} (hi : i ∈ Λ) :
    (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff P‖ ^
          p.toReal) ≤
      C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
        (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s) := by
  classical
  have hcost_summable :
      Summable (fun i : ℕ =>
        Set.indicator Λ
          (fun i => ∑ Q ∈ hΩ.family i k,
            (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) i) :=
    hΩ.cost_summable k
  have hnonneg : ∀ n ∉ ({i} : Finset ℕ),
      0 ≤ Set.indicator Λ
        (fun i => ∑ Q ∈ hΩ.family i k,
          (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) n := by
    intro n _
    by_cases hn : n ∈ Λ
    · rw [Set.indicator_of_mem hn]
      exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg ENNReal.toReal_nonneg _
    · rw [Set.indicator_of_notMem hn]
  have hsingle :
      Set.indicator Λ
          (fun i => ∑ Q ∈ hΩ.family i k,
            (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) i
        ≤
      ∑' n : ℕ,
        Set.indicator Λ
          (fun i => ∑ Q ∈ hΩ.family i k,
            (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) n := by
    simpa using hcost_summable.sum_le_tsum ({i} : Finset ℕ) hnonneg
  calc
    (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff P‖ ^
          p.toReal)
        =
      ∑ Q ∈ hΩ.family i k, (G.grid.μ Q).toReal ^ (1 - p.toReal * s) :=
      regularFamilyIndicatorBlock_levelCoeffPower
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) hΩ hi
    _ =
      Set.indicator Λ
          (fun i => ∑ Q ∈ hΩ.family i k,
            (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) i := by
      rw [Set.indicator_of_mem hi]
    _ ≤
      ∑' n : ℕ,
        Set.indicator Λ
          (fun i => ∑ Q ∈ hΩ.family i k,
            (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) n := hsingle
    _ ≤
      C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
        (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s) := hΩ.cost k

/-- If the regular-family indicator representation is used as the first input
of the `u₁` block, every nonzero output coefficient is supported inside the
corresponding active domain. -/
theorem regularFamilyIndicator_quasiU1Block_coeff_ne_zero_subset_domain
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i k : ℕ} (hi : i ∈ Λ)
    {xind xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xind)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock : ∀ m,
      Rind.block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (hcoeff :
      (quasiU1Block G s p hs hp hp_top Rind Rg k).coeff Q ≠ 0) :
    Q.1 ⊆ Ω i := by
  have hleft :
      (Rind.block k).coeff Q ≠ 0 :=
    quasiU1Block_coeff_ne_zero_left
      G s p hs hp hp_top Rind Rg Q hcoeff
  have hleft' :
      (regularFamilyIndicatorBlock
        (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff Q ≠ 0 := by
    simpa only [hblock k] using hleft
  exact regularFamilyIndicatorBlock_coeff_ne_zero_subset_domain
    (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
    (p := p) hΩ hi Q hleft'

/-- If the regular-family indicator representation is used as the first input
of the `u₂` block, every nonzero output coefficient is supported inside the
corresponding active domain. -/
theorem regularFamilyIndicator_quasiU2Block_coeff_ne_zero_subset_domain
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i j : ℕ} (hi : i ∈ Λ)
    {xind xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xind)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock : ∀ m,
      Rind.block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace j)
    (hcoeff :
      (quasiU2Block G s p hs hp hp_top Rind Rg j).coeff J ≠ 0) :
    J.1 ⊆ Ω i := by
  have hstrict :
      strictWeightedAncestorCoeffSum G Rind J ≠ 0 :=
    quasiU2Block_coeff_ne_zero_right
      G s p hs hp hp_top Rind Rg J hcoeff
  rcases strictWeightedAncestorCoeffSum_ne_zero_exists G Rind J hstrict with
    ⟨k, _hk, Q, hJQ, hQcoeff⟩
  have hQcoeff' :
      (regularFamilyIndicatorBlock
        (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff Q ≠ 0 := by
    simpa only [hblock k] using hQcoeff
  exact hJQ.trans
    (regularFamilyIndicatorBlock_coeff_ne_zero_subset_domain
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ hi Q hQcoeff')

/--
The strict ancestor tower of the canonical indicator representation is bounded
by one.

For a fixed cell `J`, at most one selected ancestor from the regular
decomposition can contribute: two different selected ancestors containing `J`
would violate pairwise disjointness of the selected cells.  The nonzero
contribution is exactly one because the coefficient
`|Q|^{1/p-s}` cancels the Souza atom value `|Q|^{s-1/p}` on `Q`.
-/
theorem regularFamilyIndicator_strictWeightedAncestorCoeffSum_norm_le_one
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i j : ℕ} (hi : i ∈ Λ)
    {xind : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xind)
    (hblock : ∀ m,
      Rind.block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace j) :
    ‖strictWeightedAncestorCoeffSum G Rind J‖ ≤ 1 := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  obtain ⟨z, hzJ⟩ := G.grid.partition_nonempty j J.1 J.2
  by_cases hex :
      ∃ k ∈ Finset.range j,
        ∃ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
          J.1 ⊆ Q.1 ∧
            Q.1 ∈ hΩ.family i k
  · rcases hex with ⟨k₀, hk₀, Q₀, hJQ₀, hQ₀fam⟩
    have hlevel_ne :
        ∀ k ∈ Finset.range j,
          ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            J.1 ⊆ Q.1 → Q.1 ∈ hΩ.family i k →
              k ≠ k₀ → False := by
      intro k _hk Q hJQ hQfam hne
      by_cases hQeq : Q.1 = Q₀.1
      · have hQmem : Q.1 ∈ G.grid.grid.partitions k := Q.2
        have hQ₀mem : Q.1 ∈ G.grid.grid.partitions k₀ := by simpa [hQeq] using Q₀.2
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact goodGridCell_not_subset_of_level_lt G ⟨k₀, Q.1, hQ₀mem⟩ ⟨Q.1, hQmem⟩ hlt subset_rfl
        · exact goodGridCell_not_subset_of_level_lt G ⟨k, Q.1, hQmem⟩ ⟨Q.1, hQ₀mem⟩ hgt subset_rfl
      · have hdisj := hΩ.pairwise_disjoint_cells i hi k k₀ Q.1 Q₀.1 hQfam hQ₀fam hQeq
        exact Set.disjoint_left.mp hdisj (hJQ hzJ) (hJQ₀ hzJ)
    have hunique_same_level :
        ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          J.1 ⊆ Q.1 → Q.1 ∈ hΩ.family i k₀ → Q = Q₀ := by
      intro Q hJQ hQfam
      have hQeq : Q.1 = Q₀.1 := by
        by_contra hneq
        have hdisj := hΩ.pairwise_disjoint_cells i hi k₀ k₀ Q.1 Q₀.1 hQfam hQ₀fam hneq
        exact Set.disjoint_left.mp hdisj (hJQ hzJ) (hJQ₀ hzJ)
      exact Subtype.ext hQeq
    have hinner_zero :
        ∀ k ∈ Finset.range j, k ≠ k₀ →
          (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            if J.1 ⊆ Q.1 then
              (Rind.block k).coeff Q * (show ℂ from (Rind.block k).atom Q)
            else 0) = 0 := by
      intro k hk hk_ne
      refine Finset.sum_eq_zero ?_
      intro Q _
      by_cases hJQ : J.1 ⊆ Q.1
      · by_cases hQfam : Q.1 ∈ hΩ.family i k
        · exact (hlevel_ne k hk Q hJQ hQfam hk_ne).elim
        · have hcoeff : (Rind.block k).coeff Q = 0 := by
            rw [hblock k]
            simp [regularFamilyIndicatorBlock, hQfam]
          simp [hJQ, hcoeff]
      · simp [hJQ]
    have hinner_k₀ :
        (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k₀,
          if J.1 ⊆ Q.1 then
            (Rind.block k₀).coeff Q * (show ℂ from (Rind.block k₀).atom Q)
          else 0) = 1 := by
      rw [Finset.sum_eq_single Q₀]
      · have hQ₀pos : 0 < (G.grid.μ Q₀.1).toReal :=
          ENNReal.toReal_pos
            (G.grid.positive_measure _ Q₀.1 Q₀.2).ne' (measure_ne_top _ _)
        rw [if_pos hJQ₀, hblock k₀]
        simp only [regularFamilyIndicatorBlock, hQ₀fam, if_true]
        change (((G.grid.μ Q₀.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ) *
            (((G.grid.μ Q₀.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ) = 1
        rw [← Complex.ofReal_mul, ← Real.rpow_add hQ₀pos,
          show ((p.toReal)⁻¹ - s) + (s - (p.toReal)⁻¹) = 0 from by ring,
          Real.rpow_zero, Complex.ofReal_one]
      · intro Q _ hQ_ne
        by_cases hJQ : J.1 ⊆ Q.1
        · by_cases hQfam : Q.1 ∈ hΩ.family i k₀
          · have hQeq := hunique_same_level Q hJQ hQfam
            exact (hQ_ne hQeq).elim
          · have hcoeff : (Rind.block k₀).coeff Q = 0 := by
              rw [hblock k₀]
              simp [regularFamilyIndicatorBlock, hQfam]
            simp [hJQ, hcoeff]
        · simp [hJQ]
      · intro hnot
        exact absurd (Finset.mem_univ Q₀) hnot
    have hsum :
        strictWeightedAncestorCoeffSum G Rind J = 1 := by
      unfold strictWeightedAncestorCoeffSum
      rw [Finset.sum_eq_single k₀]
      · exact hinner_k₀
      · intro k hk hk_ne
        exact hinner_zero k hk hk_ne
      · intro hnot
        exact absurd hk₀ hnot
    rw [hsum, norm_one]
  · have hsum :
        strictWeightedAncestorCoeffSum G Rind J = 0 := by
      unfold strictWeightedAncestorCoeffSum
      refine Finset.sum_eq_zero ?_
      intro k hk
      refine Finset.sum_eq_zero ?_
      intro Q _
      by_cases hJQ : J.1 ⊆ Q.1
      · have hQfam : Q.1 ∉ hΩ.family i k := by
          intro hQfam
          exact hex ⟨k, hk, Q, hJQ, hQfam⟩
        have hcoeff : (Rind.block k).coeff Q = 0 := by
          rw [hblock k]
          simp [regularFamilyIndicatorBlock, hQfam]
        simp [hJQ, hcoeff]
      · simp [hJQ]
    rw [hsum, norm_zero]
    norm_num

/-- Aggregate level estimate for the `u₁` blocks over a regular family. -/
theorem regularFamilyIndicator_quasiU1Block_aggregate_levelCoeffPower_le
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {xind : ℕ → Lp ℂ p G.toWeakGridSpace.measure}
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (xind i))
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock : ∀ i m,
      (Rind i).block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    {M : ℝ} (hM0 : 0 ≤ M)
    (htower_g : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G Rg Q‖ ≤ M)
    (k : ℕ) :
    (∑' i : ℕ,
      Set.indicator Λ
        (fun i =>
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            ‖(quasiU1Block G s p hs hp hp_top (Rind i) Rg k).coeff Q‖ ^
              p.toReal) i) ≤
      M ^ p.toReal *
        (C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
          (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s)) := by
  classical
  let indicatorCost : ℕ → ℝ := fun i =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ‖(regularFamilyIndicatorBlock
        (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff Q‖ ^
        p.toReal
  let u1Cost : ℕ → ℝ := fun i =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ‖(quasiU1Block G s p hs hp hp_top (Rind i) Rg k).coeff Q‖ ^ p.toReal
  have hMpow0 : 0 ≤ M ^ p.toReal := Real.rpow_nonneg hM0 _
  have hterm :
      ∀ i,
        Set.indicator Λ u1Cost i ≤
          Set.indicator Λ (fun i => M ^ p.toReal * indicatorCost i) i := by
    intro i
    by_cases hi : i ∈ Λ
    · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
      have hlevel :
          (Rind i).levelCoeffPower k = indicatorCost i := by
        simp [indicatorCost, WeakGridSpace.LpGridRepresentation.levelCoeffPower, hblock i k]
      calc
        u1Cost i
            ≤ M ^ p.toReal * (Rind i).levelCoeffPower k :=
          quasiU1Block_levelCoeffPower_le G s p hs hp hp_top (Rind i) Rg hM0 htower_g k
        _ = M ^ p.toReal * indicatorCost i := by rw [hlevel]
    · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi]
  have hright_summable :
      Summable (fun i : ℕ =>
        Set.indicator Λ (fun i => M ^ p.toReal * indicatorCost i) i) := by
    have hcost_summable :
        Summable (fun i : ℕ =>
          Set.indicator Λ
            (fun i => ∑ Q ∈ hΩ.family i k,
              (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) i) :=
      hΩ.cost_summable k
    have hcongr :
        (fun i : ℕ =>
          Set.indicator Λ (fun i => M ^ p.toReal * indicatorCost i) i)
          =
        fun i : ℕ => M ^ p.toReal *
          Set.indicator Λ
            (fun i => ∑ Q ∈ hΩ.family i k,
              (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) i := by
      funext i
      by_cases hi : i ∈ Λ
      · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
        dsimp [indicatorCost]
        change M ^ p.toReal *
            (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              ‖(regularFamilyIndicatorBlock
                (hs := hs) (hp := hp) (hp_top := hp_top)
                G Λ Ω s C c p hΩ i k).coeff P‖ ^ p.toReal)
            =
          M ^ p.toReal *
            ∑ Q ∈ hΩ.family i k,
              (G.grid.μ Q).toReal ^ (1 - p.toReal * s)
        rw [regularFamilyIndicatorBlock_levelCoeffPower
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) hΩ hi]
      · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi, mul_zero]
    rw [hcongr]
    exact hcost_summable.mul_left _
  have hleft_summable :
      Summable (fun i : ℕ => Set.indicator Λ u1Cost i) := by
    refine Summable.of_nonneg_of_le ?_ hterm hright_summable
    intro i
    by_cases hi : i ∈ Λ
    · rw [Set.indicator_of_mem hi]
      exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
    · rw [Set.indicator_of_notMem hi]
  have htsum_le :
      (∑' i : ℕ, Set.indicator Λ u1Cost i) ≤
        ∑' i : ℕ, Set.indicator Λ (fun i => M ^ p.toReal * indicatorCost i) i :=
    hleft_summable.tsum_le_tsum hterm hright_summable
  have hright_eq :
      (∑' i : ℕ, Set.indicator Λ (fun i => M ^ p.toReal * indicatorCost i) i)
        =
      M ^ p.toReal *
        (∑' i : ℕ,
          Set.indicator Λ
            (fun i => ∑ Q ∈ hΩ.family i k,
              (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) i) := by
    have hcongr :
        (fun i : ℕ =>
          Set.indicator Λ (fun i => M ^ p.toReal * indicatorCost i) i)
          =
        fun i : ℕ => M ^ p.toReal *
          Set.indicator Λ
            (fun i => ∑ Q ∈ hΩ.family i k,
              (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) i := by
      funext i
      by_cases hi : i ∈ Λ
      · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
        dsimp [indicatorCost]
        change M ^ p.toReal *
            (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              ‖(regularFamilyIndicatorBlock
                (hs := hs) (hp := hp) (hp_top := hp_top)
                G Λ Ω s C c p hΩ i k).coeff P‖ ^ p.toReal)
            =
          M ^ p.toReal *
            ∑ Q ∈ hΩ.family i k,
              (G.grid.μ Q).toReal ^ (1 - p.toReal * s)
        rw [regularFamilyIndicatorBlock_levelCoeffPower
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) hΩ hi]
      · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi, mul_zero]
    rw [hcongr, tsum_mul_left]
  calc
    (∑' i : ℕ, Set.indicator Λ u1Cost i)
        ≤ ∑' i : ℕ, Set.indicator Λ (fun i => M ^ p.toReal * indicatorCost i) i :=
      htsum_le
    _ = M ^ p.toReal *
        (∑' i : ℕ,
          Set.indicator Λ
            (fun i => ∑ Q ∈ hΩ.family i k,
              (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) i) := hright_eq
    _ ≤ M ^ p.toReal *
        (C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
          (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s)) := by
      exact mul_le_mul_of_nonneg_left (hΩ.cost k) hMpow0

/-- The aggregate level sequence of the `u₁` blocks is summable over the
active regular-family indices. -/
theorem regularFamilyIndicator_quasiU1Block_aggregate_summable
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {xind : ℕ → Lp ℂ p G.toWeakGridSpace.measure}
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (xind i))
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock : ∀ i m,
      (Rind i).block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    {M : ℝ} (hM0 : 0 ≤ M)
    (htower_g : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G Rg Q‖ ≤ M)
    (k : ℕ) :
    Summable (fun i : ℕ =>
      Set.indicator Λ
        (fun i =>
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            ‖(quasiU1Block G s p hs hp hp_top (Rind i) Rg k).coeff Q‖ ^
              p.toReal) i) := by
  classical
  let indicatorCost : ℕ → ℝ := fun i =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ‖(regularFamilyIndicatorBlock
        (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff Q‖ ^
        p.toReal
  let u1Cost : ℕ → ℝ := fun i =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ‖(quasiU1Block G s p hs hp hp_top (Rind i) Rg k).coeff Q‖ ^ p.toReal
  have hMpow0 : 0 ≤ M ^ p.toReal := Real.rpow_nonneg hM0 _
  have hterm :
      ∀ i,
        Set.indicator Λ u1Cost i ≤
          Set.indicator Λ (fun i => M ^ p.toReal * indicatorCost i) i := by
    intro i
    by_cases hi : i ∈ Λ
    · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
      have hlevel :
          (Rind i).levelCoeffPower k = indicatorCost i := by
        simp [indicatorCost, WeakGridSpace.LpGridRepresentation.levelCoeffPower, hblock i k]
      calc
        u1Cost i
            ≤ M ^ p.toReal * (Rind i).levelCoeffPower k :=
          quasiU1Block_levelCoeffPower_le G s p hs hp hp_top (Rind i) Rg hM0 htower_g k
        _ = M ^ p.toReal * indicatorCost i := by rw [hlevel]
    · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi]
  have hright_summable :
      Summable (fun i : ℕ =>
        Set.indicator Λ (fun i => M ^ p.toReal * indicatorCost i) i) := by
    have hcost_summable :
        Summable (fun i : ℕ =>
          Set.indicator Λ
            (fun i => ∑ Q ∈ hΩ.family i k,
              (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) i) :=
      hΩ.cost_summable k
    have hcongr :
        (fun i : ℕ =>
          Set.indicator Λ (fun i => M ^ p.toReal * indicatorCost i) i)
          =
        fun i : ℕ => M ^ p.toReal *
          Set.indicator Λ
            (fun i => ∑ Q ∈ hΩ.family i k,
              (G.grid.μ Q).toReal ^ (1 - p.toReal * s)) i := by
      funext i
      by_cases hi : i ∈ Λ
      · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
        dsimp [indicatorCost]
        change M ^ p.toReal *
            (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              ‖(regularFamilyIndicatorBlock
                (hs := hs) (hp := hp) (hp_top := hp_top)
                G Λ Ω s C c p hΩ i k).coeff P‖ ^ p.toReal)
            =
          M ^ p.toReal *
            ∑ Q ∈ hΩ.family i k,
              (G.grid.μ Q).toReal ^ (1 - p.toReal * s)
        rw [regularFamilyIndicatorBlock_levelCoeffPower
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) hΩ hi]
      · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi, mul_zero]
    rw [hcongr]
    exact hcost_summable.mul_left _
  refine Summable.of_nonneg_of_le ?_ hterm hright_summable
  intro i
  by_cases hi : i ∈ Λ
  · rw [Set.indicator_of_mem hi]
    exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
  · rw [Set.indicator_of_notMem hi]

/-- For a fixed level cell, at most one active regular-family indicator can
contribute a nonzero `u₂` coefficient. -/
theorem regularFamilyIndicator_quasiU2Block_unique_active_index
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i l j : ℕ} (hi : i ∈ Λ) (hl : l ∈ Λ)
    {xind_i xind_l xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind_i : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xind_i)
    (Rind_l : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xind_l)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock_i : ∀ m,
      Rind_i.block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    (hblock_l : ∀ m,
      Rind_l.block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ l m)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace j)
    (hcoeff_i :
      (quasiU2Block G s p hs hp hp_top Rind_i Rg j).coeff J ≠ 0)
    (hcoeff_l :
      (quasiU2Block G s p hs hp hp_top Rind_l Rg j).coeff J ≠ 0) :
    i = l := by
  classical
  by_contra hil
  obtain ⟨z, hzJ⟩ := G.grid.partition_nonempty j J.1 J.2
  have hJi : J.1 ⊆ Ω i :=
    regularFamilyIndicator_quasiU2Block_coeff_ne_zero_subset_domain
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ hi Rind_i Rg hblock_i J hcoeff_i
  have hJl : J.1 ⊆ Ω l :=
    regularFamilyIndicator_quasiU2Block_coeff_ne_zero_subset_domain
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ hl Rind_l Rg hblock_l J hcoeff_l
  have hdisj := hΩ.pairwise_disjoint i hi l hl hil
  exact Set.disjoint_left.mp hdisj (hJi hzJ) (hJl hzJ)

/-- Pointwise coefficient bound for `u₂` with a regular-family indicator as
the first input. -/
theorem regularFamilyIndicator_quasiU2Block_coeff_norm_rpow_le
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i j : ℕ} (hi : i ∈ Λ)
    {xind xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xind)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock : ∀ m,
      Rind.block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    (J : WeakGridSpace.LevelCell G.toWeakGridSpace j) :
    ‖(quasiU2Block G s p hs hp hp_top Rind Rg j).coeff J‖ ^ p.toReal ≤
      ‖(Rg.block j).coeff J‖ ^ p.toReal := by
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hcoeff :
      (quasiU2Block G s p hs hp hp_top Rind Rg j).coeff J =
        (Rg.block j).coeff J * strictWeightedAncestorCoeffSum G Rind J := rfl
  have hnorm :
      ‖(quasiU2Block G s p hs hp hp_top Rind Rg j).coeff J‖ =
        ‖(Rg.block j).coeff J‖ * ‖strictWeightedAncestorCoeffSum G Rind J‖ := by
    rw [hcoeff, norm_mul]
  have htower :
      ‖strictWeightedAncestorCoeffSum G Rind J‖ ≤ 1 :=
    regularFamilyIndicator_strictWeightedAncestorCoeffSum_norm_le_one
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ hi Rind hblock J
  have hmul :
      ‖(Rg.block j).coeff J‖ * ‖strictWeightedAncestorCoeffSum G Rind J‖ ≤
        ‖(Rg.block j).coeff J‖ * 1 :=
    mul_le_mul_of_nonneg_left htower (norm_nonneg _)
  calc
    ‖(quasiU2Block G s p hs hp hp_top Rind Rg j).coeff J‖ ^ p.toReal
        ≤ (‖(Rg.block j).coeff J‖ * 1) ^ p.toReal := by
      rw [hnorm]
      exact Real.rpow_le_rpow
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hmul hpr.le
    _ = ‖(Rg.block j).coeff J‖ ^ p.toReal := by rw [mul_one]

private theorem tsum_le_of_nonneg_unique_nonzero_bound
    {f : ℕ → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B)
    (huniq : ∀ i l, f i ≠ 0 → f l ≠ 0 → i = l)
    (hbound : ∀ i, f i ≤ B) :
    Summable f ∧ (∑' i : ℕ, f i) ≤ B := by
  classical
  by_cases hex : ∃ i, f i ≠ 0
  · rcases hex with ⟨i₀, hi₀⟩
    have hzero : ∀ i ≠ i₀, f i = 0 := by
      intro i hi
      by_contra hfi
      exact hi (huniq i i₀ hfi hi₀)
    have hsum : Summable f := by
      refine summable_of_hasFiniteSupport ?_
      refine Set.Finite.subset (Set.finite_singleton i₀) ?_
      intro i hi
      simp only [Function.mem_support] at hi
      exact (Classical.not_imp.mp (fun h => hi (hzero i h))).1
    refine ⟨hsum, ?_⟩
    rw [tsum_eq_single i₀]
    · exact hbound i₀
    · intro b hb
      exact hzero b hb
  · have hzero : ∀ i, f i = 0 := by
      intro i
      by_contra hfi
      exact hex ⟨i, hfi⟩
    have hsum : Summable f := by
      refine summable_of_hasFiniteSupport ?_
      refine Set.Finite.subset (Set.finite_empty) ?_
      intro i hi
      simp only [Function.mem_support] at hi
      exact (hi (hzero i)).elim
    refine ⟨hsum, ?_⟩
    rw [tsum_congr hzero]
    simp [hB0]

/-- Aggregate level estimate for the `u₂` blocks over a regular family. -/
theorem regularFamilyIndicator_quasiU2Block_aggregate_levelCoeffPower_le
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {xind : ℕ → Lp ℂ p G.toWeakGridSpace.measure}
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (xind i))
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock : ∀ i m,
      (Rind i).block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    (j : ℕ) :
    (∑' i : ℕ,
      Set.indicator Λ
        (fun i =>
          ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff J‖ ^
              p.toReal) i) ≤
      Rg.levelCoeffPower j := by
  classical
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  let cellCost :
      WeakGridSpace.LevelCell G.toWeakGridSpace j → ℕ → ℝ := fun J i =>
    Set.indicator Λ
      (fun i =>
        ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff J‖ ^
          p.toReal) i
  have htotal :
      (fun i : ℕ =>
        Set.indicator Λ
          (fun i =>
            ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
              ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff J‖ ^
                p.toReal) i)
        =
      fun i : ℕ => ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j, cellCost J i := by
    funext i
    by_cases hi : i ∈ Λ
    · rw [Set.indicator_of_mem hi]
      simp only [cellCost, Set.indicator_of_mem hi]
    · rw [Set.indicator_of_notMem hi]
      refine (Finset.sum_eq_zero ?_).symm
      intro J _
      simp [cellCost, Set.indicator_of_notMem hi]
  have hcell :
      ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
        Summable (cellCost J) ∧
          (∑' i : ℕ, cellCost J i) ≤ ‖(Rg.block j).coeff J‖ ^ p.toReal := by
    intro J
    refine tsum_le_of_nonneg_unique_nonzero_bound
      (B := ‖(Rg.block j).coeff J‖ ^ p.toReal)
      (Real.rpow_nonneg (norm_nonneg _) _) ?_ ?_
    · intro i l hi_nonzero hl_nonzero
      have hiΛ : i ∈ Λ := by
        by_contra hiΛ
        exact hi_nonzero (by simp [cellCost, Set.indicator_of_notMem hiΛ])
      have hlΛ : l ∈ Λ := by
        by_contra hlΛ
        exact hl_nonzero (by simp [cellCost, Set.indicator_of_notMem hlΛ])
      have hci :
          (quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff J ≠ 0 := by
        intro hzero
        exact hi_nonzero (by
          simp [cellCost, Set.indicator_of_mem hiΛ, hzero, Real.zero_rpow hpr.ne'])
      have hcl :
          (quasiU2Block G s p hs hp hp_top (Rind l) Rg j).coeff J ≠ 0 := by
        intro hzero
        exact hl_nonzero (by
          simp [cellCost, Set.indicator_of_mem hlΛ, hzero, Real.zero_rpow hpr.ne'])
      exact regularFamilyIndicator_quasiU2Block_unique_active_index
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) hΩ hiΛ hlΛ (Rind i) (Rind l) Rg
        (hblock i) (hblock l) J hci hcl
    · intro i
      by_cases hiΛ : i ∈ Λ
      · simp only [cellCost, Set.indicator_of_mem hiΛ]
        exact regularFamilyIndicator_quasiU2Block_coeff_norm_rpow_le
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) hΩ hiΛ (Rind i) Rg (hblock i) J
      · simp only [cellCost, Set.indicator_of_notMem hiΛ]
        exact Real.rpow_nonneg (norm_nonneg _) _
  calc
    (∑' i : ℕ,
      Set.indicator Λ
        (fun i =>
          ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff J‖ ^
              p.toReal) i)
        = ∑' i : ℕ, ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j, cellCost J i := by
          rw [htotal]
    _ = ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
          ∑' i : ℕ, cellCost J i := by
          rw [Summable.tsum_finsetSum]
          intro J _
          exact (hcell J).1
    _ ≤ ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
          ‖(Rg.block j).coeff J‖ ^ p.toReal :=
          Finset.sum_le_sum fun J _ => (hcell J).2
    _ = Rg.levelCoeffPower j := rfl

/-- The aggregate level sequence of the `u₂` blocks is summable over the
active regular-family indices. -/
theorem regularFamilyIndicator_quasiU2Block_aggregate_summable
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {xind : ℕ → Lp ℂ p G.toWeakGridSpace.measure}
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (xind i))
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock : ∀ i m,
      (Rind i).block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    (j : ℕ) :
    Summable (fun i : ℕ =>
      Set.indicator Λ
        (fun i =>
          ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff J‖ ^
              p.toReal) i) := by
  classical
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  let cellCost :
      WeakGridSpace.LevelCell G.toWeakGridSpace j → ℕ → ℝ := fun J i =>
    Set.indicator Λ
      (fun i =>
        ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff J‖ ^
          p.toReal) i
  have htotal :
      (fun i : ℕ =>
        Set.indicator Λ
          (fun i =>
            ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
              ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff J‖ ^
                p.toReal) i)
        =
      fun i : ℕ => ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j, cellCost J i := by
    funext i
    by_cases hi : i ∈ Λ
    · rw [Set.indicator_of_mem hi]
      simp only [cellCost, Set.indicator_of_mem hi]
    · rw [Set.indicator_of_notMem hi]
      refine (Finset.sum_eq_zero ?_).symm
      intro J _
      simp [cellCost, Set.indicator_of_notMem hi]
  have hcell :
      ∀ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
        Summable (cellCost J) := by
    intro J
    exact (tsum_le_of_nonneg_unique_nonzero_bound
      (B := ‖(Rg.block j).coeff J‖ ^ p.toReal)
      (Real.rpow_nonneg (norm_nonneg _) _)
      (by
        intro i l hi_nonzero hl_nonzero
        have hiΛ : i ∈ Λ := by
          by_contra hiΛ
          exact hi_nonzero (by simp [cellCost, Set.indicator_of_notMem hiΛ])
        have hlΛ : l ∈ Λ := by
          by_contra hlΛ
          exact hl_nonzero (by simp [cellCost, Set.indicator_of_notMem hlΛ])
        have hci :
            (quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff J ≠ 0 := by
          intro hzero
          exact hi_nonzero (by
            simp [cellCost, Set.indicator_of_mem hiΛ, hzero, Real.zero_rpow hpr.ne'])
        have hcl :
            (quasiU2Block G s p hs hp hp_top (Rind l) Rg j).coeff J ≠ 0 := by
          intro hzero
          exact hl_nonzero (by
            simp [cellCost, Set.indicator_of_mem hlΛ, hzero, Real.zero_rpow hpr.ne'])
        exact regularFamilyIndicator_quasiU2Block_unique_active_index
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) hΩ hiΛ hlΛ (Rind i) (Rind l) Rg
          (hblock i) (hblock l) J hci hcl)
      (by
        intro i
        by_cases hiΛ : i ∈ Λ
        · simp only [cellCost, Set.indicator_of_mem hiΛ]
          exact regularFamilyIndicator_quasiU2Block_coeff_norm_rpow_le
            (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
            (p := p) hΩ hiΛ (Rind i) Rg (hblock i) J
        · simp only [cellCost, Set.indicator_of_notMem hiΛ]
          exact Real.rpow_nonneg (norm_nonneg _) _)).1
  rw [htotal]
  refine Finset.induction_on
    (Finset.univ : Finset (WeakGridSpace.LevelCell G.toWeakGridSpace j)) ?_ ?_
  · simp
  · intro J S hJS hS
    simpa [Finset.sum_insert, hJS] using (hcell J).add hS

/-- Real version of the two-term convexity estimate for powers. -/
private theorem real_add_rpow_le_two_sub_one_mul
    {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 1 ≤ r) :
    (a + b) ^ r ≤ (2 : ℝ) ^ (r - 1) * (a ^ r + b ^ r) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a b hr

/--
The aggregate level sequence of the product blocks `u₁ + u₂` is summable over
the active indices of a regular family.

This is the summability part used inside
`regularFamilyIndicator_quasiProductBlock_aggregate_levelCoeffPower_le`,
exposed separately for finite-subfamily truncation arguments.
-/
theorem regularFamilyIndicator_quasiProductBlock_aggregate_summable
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {xind : ℕ → Lp ℂ p G.toWeakGridSpace.measure}
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (xind i))
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock : ∀ i m,
      (Rind i).block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    {M : ℝ} (hM0 : 0 ≤ M)
    (htower_g : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G Rg Q‖ ≤ M)
    (j : ℕ) :
    Summable fun i : ℕ =>
      Set.indicator Λ
        (fun i =>
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            ‖(WeakGridSpace.LevelBlock.add
              (souzaAtomFamily G s p hs hp hp_top)
              (quasiU1Block G s p hs hp hp_top (Rind i) Rg j)
              (quasiU2Block G s p hs hp hp_top (Rind i) Rg j)).coeff Q‖ ^
              p.toReal) i := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let K : ℝ := (2 : ℝ) ^ (p.toReal - 1)
  let u1Cost : ℕ → ℝ := fun i =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      ‖(quasiU1Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^ p.toReal
  let u2Cost : ℕ → ℝ := fun i =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^ p.toReal
  let addCost : ℕ → ℝ := fun i =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      ‖(WeakGridSpace.LevelBlock.add A
        (quasiU1Block G s p hs hp hp_top (Rind i) Rg j)
        (quasiU2Block G s p hs hp hp_top (Rind i) Rg j)).coeff Q‖ ^
        p.toReal
  have hp_real : 1 ≤ p.toReal := (ENNReal.dichotomy p).resolve_left hp_top
  have hK0 : 0 ≤ K := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hterm :
      ∀ i,
        Set.indicator Λ addCost i ≤
          K * (Set.indicator Λ u1Cost i + Set.indicator Λ u2Cost i) := by
    intro i
    by_cases hi : i ∈ Λ
    · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi, Set.indicator_of_mem hi]
      dsimp [addCost, u1Cost, u2Cost, K, A]
      calc
        (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            ‖(WeakGridSpace.LevelBlock.add
              (souzaAtomFamily G s p hs hp hp_top)
              (quasiU1Block G s p hs hp hp_top (Rind i) Rg j)
              (quasiU2Block G s p hs hp hp_top (Rind i) Rg j)).coeff Q‖ ^
              p.toReal)
            ≤
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            (2 : ℝ) ^ (p.toReal - 1) *
              (‖(quasiU1Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^
                  p.toReal +
                ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^
                  p.toReal) := by
            refine Finset.sum_le_sum ?_
            intro Q _
            let U1 := quasiU1Block G s p hs hp hp_top (Rind i) Rg j
            let U2 := quasiU2Block G s p hs hp hp_top (Rind i) Rg j
            have hnn : 0 ≤ ‖U1.coeff Q‖ + ‖U2.coeff Q‖ :=
              add_nonneg (norm_nonneg _) (norm_nonneg _)
            have hnorm :
                ‖(WeakGridSpace.LevelBlock.add
                  (souzaAtomFamily G s p hs hp hp_top) U1 U2).coeff Q‖ =
                  ‖U1.coeff Q‖ + ‖U2.coeff Q‖ := by
              change ‖(((‖U1.coeff Q‖ + ‖U2.coeff Q‖ : ℝ) : ℂ))‖ =
                ‖U1.coeff Q‖ + ‖U2.coeff Q‖
              rw [Complex.norm_real, Real.norm_of_nonneg hnn]
            rw [hnorm]
            exact real_add_rpow_le_two_sub_one_mul
              (norm_nonneg _) (norm_nonneg _) hp_real
        _ = (2 : ℝ) ^ (p.toReal - 1) *
            ((∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
                ‖(quasiU1Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^
                  p.toReal) +
              ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
                ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^
                  p.toReal) := by
            rw [← Finset.mul_sum]
            simp only [Finset.sum_add_distrib, mul_add]
    · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi,
        Set.indicator_of_notMem hi]
      exact mul_nonneg hK0 (by simp)
  have hu1sum :
      Summable (fun i : ℕ => Set.indicator Λ u1Cost i) :=
    regularFamilyIndicator_quasiU1Block_aggregate_summable
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ Rind Rg hblock hM0 htower_g j
  have hu2sum :
      Summable (fun i : ℕ => Set.indicator Λ u2Cost i) :=
    regularFamilyIndicator_quasiU2Block_aggregate_summable
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ Rind Rg hblock j
  have hright_summable :
      Summable (fun i : ℕ =>
        K * (Set.indicator Λ u1Cost i + Set.indicator Λ u2Cost i)) :=
    (hu1sum.add hu2sum).mul_left K
  refine Summable.of_nonneg_of_le ?_ hterm hright_summable
  intro i
  by_cases hi : i ∈ Λ
  · rw [Set.indicator_of_mem hi]
    exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
  · rw [Set.indicator_of_notMem hi]

/-- Aggregate level estimate for the product blocks `u₁ + u₂` over a regular
family. -/
theorem regularFamilyIndicator_quasiProductBlock_aggregate_levelCoeffPower_le
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {xind : ℕ → Lp ℂ p G.toWeakGridSpace.measure}
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (xind i))
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock : ∀ i m,
      (Rind i).block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    {M : ℝ} (hM0 : 0 ≤ M)
    (htower_g : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G Rg Q‖ ≤ M)
    (j : ℕ) :
    (∑' i : ℕ,
      Set.indicator Λ
        (fun i =>
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            ‖(WeakGridSpace.LevelBlock.add
              (souzaAtomFamily G s p hs hp hp_top)
              (quasiU1Block G s p hs hp hp_top (Rind i) Rg j)
              (quasiU2Block G s p hs hp hp_top (Rind i) Rg j)).coeff Q‖ ^
              p.toReal) i) ≤
      (2 : ℝ) ^ (p.toReal - 1) *
        (M ^ p.toReal *
          (C * c ^ (j - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
            (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s)) +
          Rg.levelCoeffPower j) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let K : ℝ := (2 : ℝ) ^ (p.toReal - 1)
  let u1Cost : ℕ → ℝ := fun i =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      ‖(quasiU1Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^ p.toReal
  let u2Cost : ℕ → ℝ := fun i =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^ p.toReal
  let addCost : ℕ → ℝ := fun i =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      ‖(WeakGridSpace.LevelBlock.add A
        (quasiU1Block G s p hs hp hp_top (Rind i) Rg j)
        (quasiU2Block G s p hs hp hp_top (Rind i) Rg j)).coeff Q‖ ^
        p.toReal
  have hp_real : 1 ≤ p.toReal := (ENNReal.dichotomy p).resolve_left hp_top
  have hK0 : 0 ≤ K := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hterm :
      ∀ i,
        Set.indicator Λ addCost i ≤
          K * (Set.indicator Λ u1Cost i + Set.indicator Λ u2Cost i) := by
    intro i
    by_cases hi : i ∈ Λ
    · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi, Set.indicator_of_mem hi]
      dsimp [addCost, u1Cost, u2Cost, K, A]
      calc
        (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            ‖(WeakGridSpace.LevelBlock.add
              (souzaAtomFamily G s p hs hp hp_top)
              (quasiU1Block G s p hs hp hp_top (Rind i) Rg j)
              (quasiU2Block G s p hs hp hp_top (Rind i) Rg j)).coeff Q‖ ^
              p.toReal)
            ≤
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
            (2 : ℝ) ^ (p.toReal - 1) *
              (‖(quasiU1Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^
                  p.toReal +
                ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^
                  p.toReal) := by
            refine Finset.sum_le_sum ?_
            intro Q _
            let U1 := quasiU1Block G s p hs hp hp_top (Rind i) Rg j
            let U2 := quasiU2Block G s p hs hp hp_top (Rind i) Rg j
            have hnn : 0 ≤ ‖U1.coeff Q‖ + ‖U2.coeff Q‖ :=
              add_nonneg (norm_nonneg _) (norm_nonneg _)
            have hnorm :
                ‖(WeakGridSpace.LevelBlock.add
                  (souzaAtomFamily G s p hs hp hp_top) U1 U2).coeff Q‖ =
                  ‖U1.coeff Q‖ + ‖U2.coeff Q‖ := by
              change ‖(((‖U1.coeff Q‖ + ‖U2.coeff Q‖ : ℝ) : ℂ))‖ =
                ‖U1.coeff Q‖ + ‖U2.coeff Q‖
              rw [Complex.norm_real, Real.norm_of_nonneg hnn]
            rw [hnorm]
            exact real_add_rpow_le_two_sub_one_mul
              (norm_nonneg _) (norm_nonneg _) hp_real
        _ = (2 : ℝ) ^ (p.toReal - 1) *
            ((∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
                ‖(quasiU1Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^
                  p.toReal) +
              ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
                ‖(quasiU2Block G s p hs hp hp_top (Rind i) Rg j).coeff Q‖ ^
                  p.toReal) := by
            rw [← Finset.mul_sum]
            simp only [Finset.sum_add_distrib, mul_add]
    · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi,
        Set.indicator_of_notMem hi]
      exact mul_nonneg hK0 (by simp)
  have hu1sum :
      Summable (fun i : ℕ => Set.indicator Λ u1Cost i) :=
    regularFamilyIndicator_quasiU1Block_aggregate_summable
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ Rind Rg hblock hM0 htower_g j
  have hu2sum :
      Summable (fun i : ℕ => Set.indicator Λ u2Cost i) :=
    regularFamilyIndicator_quasiU2Block_aggregate_summable
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ Rind Rg hblock j
  have hright_summable :
      Summable (fun i : ℕ =>
        K * (Set.indicator Λ u1Cost i + Set.indicator Λ u2Cost i)) :=
    (hu1sum.add hu2sum).mul_left K
  have hleft_summable :
      Summable (fun i : ℕ => Set.indicator Λ addCost i) := by
    refine Summable.of_nonneg_of_le ?_ hterm hright_summable
    intro i
    by_cases hi : i ∈ Λ
    · rw [Set.indicator_of_mem hi]
      exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
    · rw [Set.indicator_of_notMem hi]
  have htsum_le :
      (∑' i : ℕ, Set.indicator Λ addCost i) ≤
        ∑' i : ℕ, K * (Set.indicator Λ u1Cost i + Set.indicator Λ u2Cost i) :=
    hleft_summable.tsum_le_tsum hterm hright_summable
  have hright_eq :
      (∑' i : ℕ, K * (Set.indicator Λ u1Cost i + Set.indicator Λ u2Cost i))
        =
      K * ((∑' i : ℕ, Set.indicator Λ u1Cost i) +
        ∑' i : ℕ, Set.indicator Λ u2Cost i) := by
    rw [tsum_mul_left, Summable.tsum_add hu1sum hu2sum]
  have hu1_le :
      (∑' i : ℕ, Set.indicator Λ u1Cost i) ≤
        M ^ p.toReal *
          (C * c ^ (j - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
            (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s)) :=
    regularFamilyIndicator_quasiU1Block_aggregate_levelCoeffPower_le
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ Rind Rg hblock hM0 htower_g j
  have hu2_le :
      (∑' i : ℕ, Set.indicator Λ u2Cost i) ≤ Rg.levelCoeffPower j :=
    regularFamilyIndicator_quasiU2Block_aggregate_levelCoeffPower_le
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ Rind Rg hblock j
  calc
    (∑' i : ℕ, Set.indicator Λ addCost i)
        ≤ ∑' i : ℕ, K * (Set.indicator Λ u1Cost i + Set.indicator Λ u2Cost i) :=
      htsum_le
    _ = K * ((∑' i : ℕ, Set.indicator Λ u1Cost i) +
        ∑' i : ℕ, Set.indicator Λ u2Cost i) := hright_eq
    _ ≤ K *
        (M ^ p.toReal *
          (C * c ^ (j - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
            (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s)) +
          Rg.levelCoeffPower j) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hu1_le hu2_le) hK0

/--
Finite-subfamily version of the product-block aggregate level estimate.

If `Γ` is a finite set of active indices, the level-`j` product-block cost over
`Γ` is bounded by the same global regular-family level estimate.  This is the
finite truncation form used in non-Archimedean sums.
-/
theorem regularFamilyIndicator_quasiProductBlock_finset_levelCoeffPower_le
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {xind : ℕ → Lp ℂ p G.toWeakGridSpace.measure}
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (xind i))
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock : ∀ i m,
      (Rind i).block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    {M : ℝ} (hM0 : 0 ≤ M)
    (htower_g : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G Rg Q‖ ≤ M)
    (Γ : Finset ℕ) (hΓΛ : ∀ i ∈ Γ, i ∈ Λ)
    (j : ℕ) :
    (∑ i ∈ Γ,
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
        ‖(WeakGridSpace.LevelBlock.add
          (souzaAtomFamily G s p hs hp hp_top)
          (quasiU1Block G s p hs hp hp_top (Rind i) Rg j)
          (quasiU2Block G s p hs hp hp_top (Rind i) Rg j)).coeff Q‖ ^
          p.toReal) ≤
      (2 : ℝ) ^ (p.toReal - 1) *
        (M ^ p.toReal *
          (C * c ^ (j - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
            (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s)) +
          Rg.levelCoeffPower j) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let addCost : ℕ → ℝ := fun i =>
    ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      ‖(WeakGridSpace.LevelBlock.add A
        (quasiU1Block G s p hs hp hp_top (Rind i) Rg j)
        (quasiU2Block G s p hs hp hp_top (Rind i) Rg j)).coeff Q‖ ^
        p.toReal
  have hadd_summable :
      Summable fun i : ℕ => Set.indicator Λ addCost i :=
    regularFamilyIndicator_quasiProductBlock_aggregate_summable
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ Rind Rg hblock hM0 htower_g j
  have hnonneg :
      ∀ i, 0 ≤ Set.indicator Λ addCost i := by
    intro i
    by_cases hi : i ∈ Λ
    · rw [Set.indicator_of_mem hi]
      exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
    · rw [Set.indicator_of_notMem hi]
  have hsum_eq :
      (∑ i ∈ Γ, addCost i) =
        ∑ i ∈ Γ, Set.indicator Λ addCost i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Set.indicator_of_mem (hΓΛ i hi)]
  calc
    (∑ i ∈ Γ, addCost i)
        = ∑ i ∈ Γ, Set.indicator Λ addCost i := hsum_eq
    _ ≤ ∑' i : ℕ, Set.indicator Λ addCost i :=
        hadd_summable.sum_le_tsum Γ (fun i _ => hnonneg i)
    _ ≤ (2 : ℝ) ^ (p.toReal - 1) *
        (M ^ p.toReal *
          (C * c ^ (j - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
            (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s)) +
          Rg.levelCoeffPower j) := by
        simpa [addCost, A] using
          regularFamilyIndicator_quasiProductBlock_aggregate_levelCoeffPower_le
            (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
            (p := p) hΩ Rind Rg hblock hM0 htower_g j

theorem regularFamilyRestriction_bound_nonneg
    (G : GoodGridSpace (α := α)) {f : α → ℂ} {M : ℝ}
    (hM : ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ M) :
    0 ≤ M := by
  have hμpos : 0 < G.grid.μ Set.univ := by
    refine G.grid.positive_measure 0 Set.univ ?_
    rw [G.grid.grid.first_partition_eq_univ]
    exact Finset.mem_singleton_self _
  have hμne : G.toWeakGridSpace.measure ≠ 0 := by
    intro h0
    rw [show G.toWeakGridSpace.measure = G.grid.μ from rfl] at h0
    rw [h0] at hμpos
    simp at hμpos
  haveI : Filter.NeBot (ae G.toWeakGridSpace.measure) :=
    ae_neBot.mpr hμne
  obtain ⟨z, hz⟩ := hM.exists
  exact le_trans (norm_nonneg (f z)) hz

private theorem regularFamily_productBlock_coeff_ne_zero_subset_domain
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i j : ℕ} (hi : i ∈ Λ)
    {xind xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xind)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hblock : ∀ m,
      Rind.block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace j)
    (hcoeff :
      (WeakGridSpace.LevelBlock.add (souzaAtomFamily G s p hs hp hp_top)
        (quasiU1Block G s p hs hp hp_top Rind Rg j)
        (quasiU2Block G s p hs hp hp_top Rind Rg j)).coeff Q ≠ 0) :
    Q.1 ⊆ Ω i := by
  rcases WeakGridSpace.LevelBlock.add_coeff_ne_zero
      (souzaAtomFamily G s p hs hp hp_top)
      (quasiU1Block G s p hs hp hp_top Rind Rg j)
      (quasiU2Block G s p hs hp hp_top Rind Rg j) Q hcoeff with h1 | h2
  · exact regularFamilyIndicator_quasiU1Block_coeff_ne_zero_subset_domain
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ hi Rind Rg hblock Q h1
  · exact regularFamilyIndicator_quasiU2Block_coeff_ne_zero_subset_domain
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ hi Rind Rg hblock Q h2

noncomputable def regularFamilyGeomLevel
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p : ℝ≥0∞) (j : ℕ) : ℝ :=
  C * c ^ (j - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
    (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s)

noncomputable def regularFamilyGeomRootCost
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞) : ℝ :=
  if q = ∞ then
    sSup (Set.range fun j : ℕ =>
      (regularFamilyGeomLevel G Λ Ω s C c p j) ^ (1 / p.toReal))
  else
    (∑' j : ℕ,
      (regularFamilyGeomLevel G Λ Ω s C c p j) ^ (q.toReal / p.toReal)) ^
        (1 / q.toReal)

theorem regularFamilyGeomLevel_nonneg
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c) (j : ℕ) :
    0 ≤ regularFamilyGeomLevel G Λ Ω s C c p j := by
  exact mul_nonneg
    (mul_nonneg hΩ.C_nonneg (pow_nonneg hΩ.c_nonneg _))
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)

theorem regularFamilyGeomRootCost_nonneg
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c) :
    0 ≤ regularFamilyGeomRootCost G Λ Ω s C c p q := by
  by_cases hq : q = ∞
  · rw [regularFamilyGeomRootCost, if_pos hq]
    exact Real.sSup_nonneg' ⟨_,
      ⟨0, rfl⟩,
      Real.rpow_nonneg (regularFamilyGeomLevel_nonneg
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) hΩ 0) _⟩
  · rw [regularFamilyGeomRootCost, if_neg hq]
    exact Real.rpow_nonneg
      (tsum_nonneg fun j =>
        Real.rpow_nonneg (regularFamilyGeomLevel_nonneg
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) hΩ j) _) _

theorem regularFamilyGeomLevel_rpow_summable
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (hp_top : p ≠ ∞)
    (hq_top : q ≠ ∞) :
    Summable fun j : ℕ =>
      (regularFamilyGeomLevel G Λ Ω s C c p j) ^ (q.toReal / p.toReal) := by
  classical
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hqr : 0 < q.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq_top
  have hqp_pos : 0 < q.toReal / p.toReal := div_pos hqr hpr
  let k₀ := firstContainedLevel G (regularFamilyUnion Λ Ω)
  let a : ℝ := 1 - p.toReal * s
  let d : ℝ := c ^ (q.toReal / p.toReal)
  let B : ℝ :=
    (C * (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a) ^
      (q.toReal / p.toReal)
  have hd0 : 0 ≤ d := Real.rpow_nonneg hΩ.c_nonneg _
  have hd1 : d < 1 := Real.rpow_lt_one hΩ.c_nonneg hΩ.c_lt_one hqp_pos
  have hBgeom : Summable (fun m : ℕ => B * d ^ m) :=
    (summable_geometric_of_lt_one hd0 hd1).mul_left B
  rw [← summable_nat_add_iff k₀]
  refine Summable.of_nonneg_of_le
    (fun m => Real.rpow_nonneg
      (regularFamilyGeomLevel_nonneg
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) hΩ (m + k₀)) _) ?_ hBgeom
  intro m
  have hCμ0 :
      0 ≤ C * (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a :=
    mul_nonneg hΩ.C_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hbase0 :
      0 ≤ C * c ^ m *
        (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a :=
    mul_nonneg (mul_nonneg hΩ.C_nonneg (pow_nonneg hΩ.c_nonneg _))
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  calc
    (regularFamilyGeomLevel G Λ Ω s C c p (m + k₀)) ^
        (q.toReal / p.toReal)
        =
      (C * c ^ m *
        (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a) ^
          (q.toReal / p.toReal) := by
        simp [regularFamilyGeomLevel, k₀, a, Nat.add_sub_cancel]
    _ = B * d ^ m := by
      rw [show C * c ^ m *
            (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a =
            (C * (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a) * c ^ m by ring]
      rw [Real.mul_rpow hCμ0 (pow_nonneg hΩ.c_nonneg _)]
      rw [← Real.rpow_natCast c m,
        ← Real.rpow_natCast (c ^ (q.toReal / p.toReal)) m,
        ← Real.rpow_mul hΩ.c_nonneg, ← Real.rpow_mul hΩ.c_nonneg]
      simp only [B, d, a]
      congr 1
      ring_nf
    _ ≤ B * d ^ m := le_rfl

theorem regularFamilyGeomLevel_root_le_rootCost
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (hp_top : p ≠ ∞) (j : ℕ) :
    (regularFamilyGeomLevel G Λ Ω s C c p j) ^ (1 / p.toReal) ≤
      regularFamilyGeomRootCost G Λ Ω s C c p q := by
  classical
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  by_cases hq : q = ∞
  · rw [regularFamilyGeomRootCost, if_pos hq]
    let D : ℝ :=
      C * (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ (1 - p.toReal * s)
    have hD0 : 0 ≤ D :=
      mul_nonneg hΩ.C_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    have hbdd : BddAbove (Set.range fun j : ℕ =>
        (regularFamilyGeomLevel G Λ Ω s C c p j) ^ (1 / p.toReal)) := by
      refine ⟨D ^ (1 / p.toReal), ?_⟩
      rintro x ⟨k, rfl⟩
      have hc_pow_le :
          c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) ≤ 1 :=
        pow_le_one₀ hΩ.c_nonneg hΩ.c_lt_one.le
      have hlevelD : regularFamilyGeomLevel G Λ Ω s C c p k ≤ D := by
        have hμa0 :
            0 ≤ (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^
              (1 - p.toReal * s) :=
          Real.rpow_nonneg ENNReal.toReal_nonneg _
        have hc_mul_le :
            C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) ≤
              C * 1 :=
          mul_le_mul_of_nonneg_left hc_pow_le hΩ.C_nonneg
        calc
          regularFamilyGeomLevel G Λ Ω s C c p k
              ≤ C * 1 *
                  (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^
                    (1 - p.toReal * s) := by
                exact mul_le_mul_of_nonneg_right hc_mul_le hμa0
          _ = D := by ring
      exact Real.rpow_le_rpow
        (regularFamilyGeomLevel_nonneg
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) hΩ k) hlevelD (one_div_nonneg.mpr hpr.le)
    exact le_csSup hbdd ⟨j, rfl⟩
  · have hqr : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    rw [regularFamilyGeomRootCost, if_neg hq]
    have hsum : Summable fun n : ℕ =>
        (regularFamilyGeomLevel G Λ Ω s C c p n) ^ (q.toReal / p.toReal) :=
      regularFamilyGeomLevel_rpow_summable
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) (q := q) hΩ hp_top hq
    have hterm_le :
        (regularFamilyGeomLevel G Λ Ω s C c p j) ^ (q.toReal / p.toReal) ≤
          ∑' n : ℕ,
            (regularFamilyGeomLevel G Λ Ω s C c p n) ^ (q.toReal / p.toReal) := by
      simpa using
        sum_le_hasSum ({j} : Finset ℕ)
          (fun n _ => Real.rpow_nonneg
            (regularFamilyGeomLevel_nonneg
              (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
              (p := p) hΩ n) _) hsum.hasSum
    have hpow_le :=
      Real.rpow_le_rpow
        (Real.rpow_nonneg
          (regularFamilyGeomLevel_nonneg
            (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
            (p := p) hΩ j) _) hterm_le (one_div_nonneg.mpr hqr.le)
    have hleft :
        ((regularFamilyGeomLevel G Λ Ω s C c p j) ^
            (q.toReal / p.toReal)) ^ (1 / q.toReal) =
          (regularFamilyGeomLevel G Λ Ω s C c p j) ^ (1 / p.toReal) := by
      have hdiv : q.toReal / p.toReal * (1 / q.toReal) = 1 / p.toReal := by
        field_simp [hqr.ne']
      rw [← Real.rpow_mul
        (regularFamilyGeomLevel_nonneg
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) hΩ j), hdiv]
    rwa [hleft] at hpow_le

private theorem regularFamilyIndicatorBlock_inactive_coeff
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i k : ℕ} (hi : i ∉ Λ)
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    (regularFamilyIndicatorBlock
      (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff Q = 0 := by
  have hQ : Q.1 ∉ hΩ.family i k := by
    rw [hΩ.family_empty_of_not_mem i hi k]
    simp
  simp [regularFamilyIndicatorBlock, hQ]

private theorem regularFamilyIndicatorBlock_inactive_toLp
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i k : ℕ} (hi : i ∉ Λ) :
    (regularFamilyIndicatorBlock
      (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).toLp
        (souzaAtomFamily G s p hs hp hp_top) = 0 := by
  classical
  unfold WeakGridSpace.LevelBlock.toLp WeakGridSpace.LevelBlock.term
  refine Finset.sum_eq_zero ?_
  intro Q _
  rw [regularFamilyIndicatorBlock_inactive_coeff
    (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
    (p := p) hΩ hi Q]
  simp

noncomputable def regularFamilyInactiveIndicatorRepresentation
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (i : ℕ) (hi : i ∉ Λ) :
    WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (0 : Lp ℂ p G.toWeakGridSpace.measure) :=
  { block := fun k =>
      regularFamilyIndicatorBlock
        (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k
    hasSum := by
      have hterms :
          (fun k =>
            (regularFamilyIndicatorBlock
              (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).toLp
                (souzaAtomFamily G s p hs hp hp_top)) =
            fun _ : ℕ => (0 : Lp ℂ p G.toWeakGridSpace.measure) := by
        funext k
        exact regularFamilyIndicatorBlock_inactive_toLp
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) hΩ hi
      rw [hterms]
      exact (hasSum_zero : HasSum (fun _ : ℕ => (0 : Lp ℂ p G.toWeakGridSpace.measure)) 0) }

private theorem regularFamilyInactiveIndicatorRepresentation_finite
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (hp_top : p ≠ ∞) {i : ℕ} (hi : i ∉ Λ) :
    WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
      (regularFamilyInactiveIndicatorRepresentation
        (hs := hs) (hp := hp) (hp_top := hp_top)
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) hΩ i hi) := by
  classical
  let R := regularFamilyInactiveIndicatorRepresentation
    (hs := hs) (hp := hp) (hp_top := hp_top)
    (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
    (p := p) hΩ i hi
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos
    (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hzero : ∀ k, R.levelCoeffPower k = 0 := by
    intro k
    unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
    simp [R, regularFamilyInactiveIndicatorRepresentation,
      regularFamilyIndicatorBlock_inactive_coeff
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) hΩ hi, Real.zero_rpow hp_pos.ne']
  by_cases hq : q = ∞
  · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_pos hq]
    refine ⟨0, ?_⟩
    rintro x ⟨k, rfl⟩
    have hinv_pos : 0 < 1 / p.toReal := one_div_pos.mpr hp_pos
    change R.levelCoeffPower k ^ (1 / p.toReal) ≤ 0
    rw [hzero k, Real.zero_rpow hinv_pos.ne']
  · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hq]
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    have hpow_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
    change Summable (fun k : ℕ => R.levelCoeffPower k ^ (q.toReal / p.toReal))
    have hfun :
        (fun k : ℕ => R.levelCoeffPower k ^ (q.toReal / p.toReal)) =
          fun _ : ℕ => (0 : ℝ) := by
      funext k
      rw [hzero k, Real.zero_rpow hpow_pos.ne']
    rw [hfun]
    exact summable_zero

private theorem regular_rpow_one_div_rpow {x : ℝ} (hx : 0 ≤ x) {e : ℝ} (he : e ≠ 0) :
    (x ^ (1 / e)) ^ e = x := by
  rw [← Real.rpow_mul hx, one_div, inv_mul_cancel₀ he, Real.rpow_one]

private theorem regular_rpow_rpow_one_div {x : ℝ} (hx : 0 ≤ x) {e : ℝ} (he : e ≠ 0) :
    (x ^ e) ^ (1 / e) = x := by
  rw [← Real.rpow_mul hx, mul_one_div, div_self he, Real.rpow_one]

theorem regularFamilyRestrictionCost_le_of_level_bound
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (hp_top : p ≠ ∞)
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hRgfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rg)
    {M : ℝ} (hM0 : 0 ≤ M)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) →
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        ((y i : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q) :
          Lp ℂ p G.toWeakGridSpace.measure))
    (hlevel : ∀ j,
      regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j ≤
        (2 : ℝ) ^ (p.toReal - 1) *
          (M ^ p.toReal * regularFamilyGeomLevel G Λ Ω s C c p j +
            Rg.levelCoeffPower j)) :
    regularFamilyRestrictionCost G s p q Λ y R ≤
      ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
        (M * regularFamilyGeomRootCost G Λ Ω s C c p q +
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg) := by
  classical
  let K : ℝ := (2 : ℝ) ^ (p.toReal - 1)
  let Kroot : ℝ := K ^ (1 / p.toReal)
  let Droot : ℕ → ℝ := fun j =>
    (regularFamilyGeomLevel G Λ Ω s C c p j) ^ (1 / p.toReal)
  let Groot : ℝ := regularFamilyGeomRootCost G Λ Ω s C c p q
  let Broot : ℕ → ℝ := fun j => (Rg.levelCoeffPower j) ^ (1 / p.toReal)
  let Rcost : ℝ := WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hp_real : 1 ≤ p.toReal := (ENNReal.dichotomy p).resolve_left hp_top
  have hK0 : 0 ≤ K := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hKroot0 : 0 ≤ Kroot := Real.rpow_nonneg hK0 _
  have hKroot_pow : Kroot ^ p.toReal = K :=
    regular_rpow_one_div_rpow hK0 hp_pos.ne'
  have hD0 : ∀ j, 0 ≤ Droot j := fun j =>
    Real.rpow_nonneg
      (regularFamilyGeomLevel_nonneg
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) hΩ j) _
  have hB0 : ∀ j, 0 ≤ Broot j := fun j =>
    Real.rpow_nonneg (Rg.levelCoeffPower_nonneg j) _
  have hG0 : 0 ≤ Groot := regularFamilyGeomRootCost_nonneg
    (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
    (p := p) (q := q) hΩ
  have hRcost0 : 0 ≤ Rcost := WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rg
  have hDroot_le : ∀ j, Droot j ≤ Groot := fun j =>
    regularFamilyGeomLevel_root_le_rootCost
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) (q := q) hΩ hp_top j
  have hBroot_le : ∀ j, Broot j ≤ Rcost := fun j =>
    WeakGridSpace.AtomFamily.levelCoeffRoot_le_pqCost
      (souzaAtomFamily G s p hs hp hp_top) Rg hRgfin j
  have hroot_level : ∀ j,
      (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^ (1 / p.toReal) ≤
        Kroot * (M * Droot j + Broot j) := by
    intro j
    let L := regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j
    have hL0 : 0 ≤ L := by
      dsimp [L, regularFamilyRestrictionLevelCoeffPower]
      exact tsum_nonneg fun i => by
        by_cases hi : i ∈ Λ
        · rw [Set.indicator_of_mem hi]
          exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
        · rw [Set.indicator_of_notMem hi]
    have ha0 : 0 ≤ M * Droot j := mul_nonneg hM0 (hD0 j)
    have hb0 : 0 ≤ Broot j := hB0 j
    have hsum_pow :
        M ^ p.toReal * regularFamilyGeomLevel G Λ Ω s C c p j +
            Rg.levelCoeffPower j ≤
          (M * Droot j + Broot j) ^ p.toReal := by
      have hMD :
          (M * Droot j) ^ p.toReal =
            M ^ p.toReal * regularFamilyGeomLevel G Λ Ω s C c p j := by
        rw [Real.mul_rpow hM0 (hD0 j)]
        simp only [Droot]
        rw [regular_rpow_one_div_rpow
          (regularFamilyGeomLevel_nonneg
            (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
            (p := p) hΩ j) hp_pos.ne']
      have hB :
          (Broot j) ^ p.toReal = Rg.levelCoeffPower j := by
        simp only [Broot]
        rw [regular_rpow_one_div_rpow (Rg.levelCoeffPower_nonneg j) hp_pos.ne']
      calc
        M ^ p.toReal * regularFamilyGeomLevel G Λ Ω s C c p j +
            Rg.levelCoeffPower j
            = (M * Droot j) ^ p.toReal + (Broot j) ^ p.toReal := by
                rw [hMD, hB]
        _ ≤ (M * Droot j + Broot j) ^ p.toReal :=
          Real.add_rpow_le_rpow_add ha0 hb0 hp_real
    have hpow_bound :
        L ≤ (Kroot * (M * Droot j + Broot j)) ^ p.toReal := by
      have hright0 : 0 ≤ M * Droot j + Broot j := add_nonneg ha0 hb0
      calc
        L ≤ K * (M ^ p.toReal * regularFamilyGeomLevel G Λ Ω s C c p j +
              Rg.levelCoeffPower j) := hlevel j
        _ ≤ K * (M * Droot j + Broot j) ^ p.toReal :=
          mul_le_mul_of_nonneg_left hsum_pow hK0
        _ = (Kroot * (M * Droot j + Broot j)) ^ p.toReal := by
          rw [Real.mul_rpow hKroot0 hright0, hKroot_pow]
    calc
      L ^ (1 / p.toReal)
          ≤ ((Kroot * (M * Droot j + Broot j)) ^ p.toReal) ^ (1 / p.toReal) :=
        Real.rpow_le_rpow hL0 hpow_bound (one_div_nonneg.mpr hp_pos.le)
      _ = Kroot * (M * Droot j + Broot j) := by
        exact regular_rpow_rpow_one_div
          (mul_nonneg hKroot0 (add_nonneg ha0 hb0)) hp_pos.ne'
  by_cases hq : q = ∞
  · rw [regularFamilyRestrictionCost, if_pos hq]
    have hbdd : BddAbove (Set.range fun j : ℕ =>
        (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^ (1 / p.toReal)) := by
      refine ⟨Kroot * (M * Groot + Rcost), ?_⟩
      rintro x ⟨j, rfl⟩
      exact le_trans (hroot_level j)
        (mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul_of_nonneg_left (hDroot_le j) hM0)
            (hBroot_le j)) hKroot0)
    exact csSup_le (Set.range_nonempty _) (by
      rintro x ⟨j, rfl⟩
      exact le_trans (hroot_level j)
        (mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul_of_nonneg_left (hDroot_le j) hM0)
            (hBroot_le j)) hKroot0))
  · have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    have hq_real : 1 ≤ q.toReal := by
      have h := ENNReal.toReal_mono hq (Fact.out : (1 : ℝ≥0∞) ≤ q)
      simpa using h
    rw [regularFamilyRestrictionCost, if_neg hq]
    have hDsum : Summable fun j : ℕ => (M * Droot j) ^ q.toReal := by
      have hgeom : Summable fun j : ℕ =>
          (regularFamilyGeomLevel G Λ Ω s C c p j) ^ (q.toReal / p.toReal) :=
        regularFamilyGeomLevel_rpow_summable
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) (q := q) hΩ hp_top hq
      have hfun :
          (fun j : ℕ => (M * Droot j) ^ q.toReal) =
            fun j : ℕ =>
              M ^ q.toReal *
                (regularFamilyGeomLevel G Λ Ω s C c p j) ^
                  (q.toReal / p.toReal) := by
        funext j
        rw [Real.mul_rpow hM0 (hD0 j)]
        simp only [Droot]
        rw [← Real.rpow_mul
          (regularFamilyGeomLevel_nonneg
            (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
            (p := p) hΩ j)]
        congr 1
        ring_nf
      rw [hfun]
      exact hgeom.mul_left _
    have hBsum : Summable fun j : ℕ => (Broot j) ^ q.toReal := by
      have hfin := hRgfin
      rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hq] at hfin
      have hfun :
          (fun j : ℕ => (Broot j) ^ q.toReal) =
            fun j : ℕ => (Rg.levelCoeffPower j) ^ (q.toReal / p.toReal) := by
        funext j
        simp only [Broot]
        rw [← Real.rpow_mul (Rg.levelCoeffPower_nonneg j)]
        congr 1
        ring
      rw [hfun]
      exact hfin
    have hsum_add : Summable fun j : ℕ => (M * Droot j + Broot j) ^ q.toReal :=
      Real.summable_Lp_add_of_nonneg hq_real
        (fun j => mul_nonneg hM0 (hD0 j)) hB0 hDsum hBsum
    have hLsum : Summable fun j : ℕ =>
        (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
          (q.toReal / p.toReal) := by
      refine Summable.of_nonneg_of_le
        (f := fun j : ℕ => (Kroot * (M * Droot j + Broot j)) ^ q.toReal)
        (g := fun j : ℕ =>
          (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
            (q.toReal / p.toReal))
        (fun j => Real.rpow_nonneg
          (regularFamilyRestrictionLevelCoeffPower_nonneg
            (G := G) (s := s) (p := p) (q := q)
            (hs := hs) (hp := hp) (hp_top := hp_top) Λ y R j) _) ?_ ?_
      · intro j
        have hL0 : 0 ≤ regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j :=
          regularFamilyRestrictionLevelCoeffPower_nonneg
            (G := G) (s := s) (p := p) (q := q)
            (hs := hs) (hp := hp) (hp_top := hp_top) Λ y R j
        have hleft :
            (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
                (q.toReal / p.toReal) =
              ((regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
                (1 / p.toReal)) ^ q.toReal := by
          rw [← Real.rpow_mul hL0]
          congr 1
          ring
        change
          (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
              (q.toReal / p.toReal) ≤
            (Kroot * (M * Droot j + Broot j)) ^ q.toReal
        rw [hleft]
        exact Real.rpow_le_rpow
          (Real.rpow_nonneg hL0 _) (hroot_level j) hq_pos.le
      · have hscaled : Summable fun j : ℕ =>
            (Kroot * (M * Droot j + Broot j)) ^ q.toReal := by
          have hfun :
              (fun j : ℕ => (Kroot * (M * Droot j + Broot j)) ^ q.toReal) =
                fun j : ℕ => Kroot ^ q.toReal *
                  (M * Droot j + Broot j) ^ q.toReal := by
            funext j
            rw [Real.mul_rpow hKroot0 (add_nonneg (mul_nonneg hM0 (hD0 j)) (hB0 j))]
          rw [hfun]
          exact hsum_add.mul_left _
        exact hscaled
    have htsum_le :
        (∑' j : ℕ,
          (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
            (q.toReal / p.toReal)) ≤
          ∑' j : ℕ, (Kroot * (M * Droot j + Broot j)) ^ q.toReal := by
      refine hLsum.tsum_le_tsum ?_ ?_
      · intro j
        have hL0 : 0 ≤ regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j :=
          regularFamilyRestrictionLevelCoeffPower_nonneg
            (G := G) (s := s) (p := p) (q := q)
            (hs := hs) (hp := hp) (hp_top := hp_top) Λ y R j
        have hleft :
            (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
                (q.toReal / p.toReal) =
              ((regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
                (1 / p.toReal)) ^ q.toReal := by
          rw [← Real.rpow_mul hL0]
          congr 1
          ring
        change
          (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
              (q.toReal / p.toReal) ≤
            (Kroot * (M * Droot j + Broot j)) ^ q.toReal
        rw [hleft]
        exact Real.rpow_le_rpow
          (Real.rpow_nonneg hL0 _) (hroot_level j) hq_pos.le
      · have hfun :
            (fun j : ℕ => (Kroot * (M * Droot j + Broot j)) ^ q.toReal) =
              fun j : ℕ => Kroot ^ q.toReal *
                (M * Droot j + Broot j) ^ q.toReal := by
          funext j
          rw [Real.mul_rpow hKroot0 (add_nonneg (mul_nonneg hM0 (hD0 j)) (hB0 j))]
        rw [hfun]
        exact hsum_add.mul_left _
    have hscaled_root :
        (∑' j : ℕ, (Kroot * (M * Droot j + Broot j)) ^ q.toReal) ^
            (1 / q.toReal) =
          Kroot * (∑' j : ℕ, (M * Droot j + Broot j) ^ q.toReal) ^
            (1 / q.toReal) := by
      have hfun :
          (fun j : ℕ => (Kroot * (M * Droot j + Broot j)) ^ q.toReal) =
            fun j : ℕ => Kroot ^ q.toReal *
              (M * Droot j + Broot j) ^ q.toReal := by
        funext j
        rw [Real.mul_rpow hKroot0 (add_nonneg (mul_nonneg hM0 (hD0 j)) (hB0 j))]
      rw [hfun, tsum_mul_left, Real.mul_rpow
        (Real.rpow_nonneg hKroot0 _)
        (tsum_nonneg fun j =>
          Real.rpow_nonneg (add_nonneg (mul_nonneg hM0 (hD0 j)) (hB0 j)) _),
        regular_rpow_rpow_one_div hKroot0 hq_pos.ne']
    have hadd_root :
        (∑' j : ℕ, (M * Droot j + Broot j) ^ q.toReal) ^ (1 / q.toReal) ≤
          M * Groot + Rcost := by
      have hLp := Real.Lp_add_le_tsum_of_nonneg' hq_real
        (fun j => mul_nonneg hM0 (hD0 j)) hB0 hDsum hBsum
      refine le_trans hLp ?_
      have hDroot_cost :
          (∑' j : ℕ, (M * Droot j) ^ q.toReal) ^ (1 / q.toReal) =
            M * Groot := by
        have hfun :
            (fun j : ℕ => (M * Droot j) ^ q.toReal) =
              fun j : ℕ => M ^ q.toReal * Droot j ^ q.toReal := by
          funext j
          rw [Real.mul_rpow hM0 (hD0 j)]
        have hDfun :
            (fun j : ℕ => Droot j ^ q.toReal) =
              fun j : ℕ =>
                (regularFamilyGeomLevel G Λ Ω s C c p j) ^
                  (q.toReal / p.toReal) := by
          funext j
          simp only [Droot]
          rw [← Real.rpow_mul
            (regularFamilyGeomLevel_nonneg
              (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
              (p := p) hΩ j)]
          congr 1
          ring
        rw [hfun, tsum_mul_left, hDfun]
        dsimp [Groot, regularFamilyGeomRootCost]
        rw [if_neg hq]
        rw [Real.mul_rpow (Real.rpow_nonneg hM0 _)
          (tsum_nonneg fun j =>
            Real.rpow_nonneg
              (regularFamilyGeomLevel_nonneg
                (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
                (p := p) hΩ j) _),
          regular_rpow_rpow_one_div hM0 hq_pos.ne']
      have hBroot_cost :
          (∑' j : ℕ, Broot j ^ q.toReal) ^ (1 / q.toReal) = Rcost := by
        have hBfun :
            (fun j : ℕ => Broot j ^ q.toReal) =
              fun j : ℕ => (Rg.levelCoeffPower j) ^ (q.toReal / p.toReal) := by
          funext j
          simp only [Broot]
          rw [← Real.rpow_mul (Rg.levelCoeffPower_nonneg j)]
          congr 1
          ring
        rw [hBfun]
        dsimp [Rcost]
        rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hq]
      linarith
    calc
      (∑' j : ℕ,
        (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
          (q.toReal / p.toReal)) ^ (1 / q.toReal)
          ≤ (∑' j : ℕ, (Kroot * (M * Droot j + Broot j)) ^ q.toReal) ^
              (1 / q.toReal) :=
        Real.rpow_le_rpow
          (tsum_nonneg fun j => Real.rpow_nonneg
            (regularFamilyRestrictionLevelCoeffPower_nonneg
              (G := G) (s := s) (p := p) (q := q)
              (hs := hs) (hp := hp) (hp_top := hp_top) Λ y R j) _)
          htsum_le (one_div_nonneg.mpr hq_pos.le)
      _ = Kroot * (∑' j : ℕ, (M * Droot j + Broot j) ^ q.toReal) ^
            (1 / q.toReal) := hscaled_root
      _ ≤ Kroot * (M * Groot + Rcost) :=
        mul_le_mul_of_nonneg_left hadd_root hKroot0

end RegularFamilyIndicatorBlocks

/-- A finite sum of `indicatorConstLp`'s of pairwise disjoint sets is the
`indicatorConstLp` of their union (local copy for this file). -/
private theorem sum_indicatorConstLp_disjoint_aux
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
      rw [Set.indicator_of_mem hz, Finset.sum_eq_single i₀]
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

/-- For nested measurable sets `A ⊆ B` of finite measure, the indicator of `B`
splits as the indicator of `A` plus the indicator of `B \ A`. -/
private theorem indicatorConstLp_add_diff
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    (hAfin : G.toWeakGridSpace.measure A ≠ ∞)
    (hBfin : G.toWeakGridSpace.measure B ≠ ∞) (v : ℂ) :
    MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p hB hBfin v
      = MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p hA hAfin v
        + MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p (hB.diff hA)
            (ne_top_of_le_ne_top hBfin (measure_mono Set.diff_subset)) v := by
  classical
  apply Lp.ext
  have hBc := MeasureTheory.indicatorConstLp_coeFn (μ := G.toWeakGridSpace.measure)
    (p := p) (hs := hB) (hμs := hBfin) (c := v)
  have hAc := MeasureTheory.indicatorConstLp_coeFn (μ := G.toWeakGridSpace.measure)
    (p := p) (hs := hA) (hμs := hAfin) (c := v)
  have hDc := MeasureTheory.indicatorConstLp_coeFn (μ := G.toWeakGridSpace.measure)
    (p := p) (hs := hB.diff hA)
    (hμs := ne_top_of_le_ne_top hBfin (measure_mono Set.diff_subset)) (c := v)
  have hadd := Lp.coeFn_add
    (MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p hA hAfin v)
    (MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p (hB.diff hA)
      (ne_top_of_le_ne_top hBfin (measure_mono Set.diff_subset)) v)
  filter_upwards [hBc, hAc, hDc, hadd] with z hz hzA hzD hzadd
  rw [hz, hzadd, Pi.add_apply, hzA, hzD]
  by_cases hzB : z ∈ B
  · by_cases hzAmem : z ∈ A
    · rw [Set.indicator_of_mem hzB, Set.indicator_of_mem hzAmem,
          Set.indicator_of_notMem (fun h => h.2 hzAmem), add_zero]
    · rw [Set.indicator_of_mem hzB, Set.indicator_of_notMem hzAmem,
          Set.indicator_of_mem (Set.mem_diff_of_mem hzB hzAmem), zero_add]
  · rw [Set.indicator_of_notMem hzB, Set.indicator_of_notMem (fun h => hzB (hAB h)),
        Set.indicator_of_notMem (fun h => hzB h.1), add_zero]

open Filter in
/-- The indicators of a disjoint countable family of finite-measure cells sum
(in `L^p`) to the indicator of their union, when that union has finite
measure. -/
private theorem hasSum_indicatorConstLp_iUnion
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (E : ℕ → Set α) (Ω : Set α)
    (hEmeas : ∀ k, MeasurableSet (E k))
    (hEfin : ∀ k, G.toWeakGridSpace.measure (E k) ≠ ∞)
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (hΩmeas : MeasurableSet Ω) (hΩfin : G.toWeakGridSpace.measure Ω ≠ ∞)
    (hcover : Ω = ⋃ k, E k) (v : ℂ) :
    HasSum (fun k => MeasureTheory.indicatorConstLp
        (μ := G.toWeakGridSpace.measure) p (hEmeas k) (hEfin k) v)
      (MeasureTheory.indicatorConstLp
        (μ := G.toWeakGridSpace.measure) p hΩmeas hΩfin v) := by
  classical
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hsubΩ : ∀ k, E k ⊆ Ω := fun k => by rw [hcover]; exact Set.subset_iUnion E k
  have hbUmono : ∀ {t₁ t₂ : Finset ℕ}, t₁ ⊆ t₂ →
      (⋃ k ∈ t₁, E k) ⊆ ⋃ k ∈ t₂, E k := by
    intro t₁ t₂ ht z hz
    rcases Set.mem_iUnion₂.mp hz with ⟨k, hk, hzk⟩
    exact Set.mem_iUnion₂.mpr ⟨k, ht hk, hzk⟩
  set D : ℕ → Set α := fun N => Ω \ ⋃ k ∈ Finset.range N, E k with hDdef
  have hDmeas : ∀ N, MeasurableSet (D N) := fun N =>
    hΩmeas.diff (MeasurableSet.biUnion (Finset.range N).countable_toSet fun k _ => hEmeas k)
  have hDanti : Antitone D := by
    intro M N hMN z hz
    simp only [hDdef, Set.mem_diff] at hz ⊢
    refine ⟨hz.1, fun h => hz.2 (hbUmono (fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hMN)) h)⟩
  have hDfin : ∀ N, G.toWeakGridSpace.measure (D N) ≠ ∞ := fun N =>
    ne_top_of_le_ne_top hΩfin (measure_mono Set.diff_subset)
  have hDinter : ⋂ N, D N = ∅ := by
    ext z
    simp only [hDdef, Set.mem_iInter, Set.mem_diff, Set.mem_empty_iff_false, iff_false]
    intro hz
    obtain ⟨hzΩ, _⟩ := hz 0
    rw [hcover] at hzΩ
    obtain ⟨k₀, hzk₀⟩ := Set.mem_iUnion.mp hzΩ
    exact (hz (k₀ + 1)).2
      (Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_self k₀)) hzk₀)
  have htend0 :
      Tendsto (fun N => G.toWeakGridSpace.measure (D N)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := G.toWeakGridSpace.measure)
      (fun N => (hDmeas N).nullMeasurableSet) hDanti ⟨0, hDfin 0⟩
    rwa [hDinter, measure_empty] at h
  have hcontR : ContinuousAt (fun x : ℝ => x ^ (1 / p.toReal)) 0 :=
    Real.continuousAt_rpow_const 0 (1 / p.toReal) (Or.inr (by positivity))
  have htendR :
      Tendsto (fun N => ‖v‖ * (G.toWeakGridSpace.measure (D N)).toReal ^ (1 / p.toReal))
        atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => (G.toWeakGridSpace.measure (D N)).toReal) atTop (𝓝 0) := by
      simpa using (ENNReal.tendsto_toReal (by simp)).comp htend0
    have h2 : Tendsto (fun N => (G.toWeakGridSpace.measure (D N)).toReal ^ (1 / p.toReal))
        atTop (𝓝 0) := by
      have key := hcontR.tendsto.comp h1
      simp only [Real.zero_rpow (show (1 / p.toReal) ≠ 0 by positivity)] at key
      exact key
    simpa using h2.const_mul ‖v‖
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := (Metric.tendsto_nhds.1 htendR ε hε).exists
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (by positivity :
      0 ≤ ‖v‖ * (G.toWeakGridSpace.measure (D N)).toReal ^ (1 / p.toReal))] at hN
  filter_upwards [Filter.eventually_ge_atTop (Finset.range N)] with s hs
  have hUm : MeasurableSet (⋃ k ∈ s, E k) :=
    MeasurableSet.biUnion s.countable_toSet fun k _ => hEmeas k
  have hUsubΩ : (⋃ k ∈ s, E k) ⊆ Ω := by
    intro z hz
    rcases Set.mem_iUnion₂.mp hz with ⟨k, _, hzk⟩
    exact hsubΩ k hzk
  have hUf : G.toWeakGridSpace.measure (⋃ k ∈ s, E k) ≠ ∞ :=
    ne_top_of_le_ne_top hΩfin (measure_mono hUsubΩ)
  have hsub : Ω \ ⋃ k ∈ s, E k ⊆ D N := by
    intro z hz
    simp only [hDdef, Set.mem_diff] at hz ⊢
    exact ⟨hz.1, fun h => hz.2 (hbUmono hs h)⟩
  rw [sum_indicatorConstLp_disjoint_aux G p E hEmeas hEfin hdisj s v hUm hUf,
    dist_eq_norm, indicatorConstLp_add_diff G p hUm hΩmeas hUsubΩ hUf hΩfin v,
    show MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p hUm hUf v -
        (MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p hUm hUf v +
          MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p (hΩmeas.diff hUm)
            (ne_top_of_le_ne_top hΩfin (measure_mono Set.diff_subset)) v)
      = -(MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p (hΩmeas.diff hUm)
            (ne_top_of_le_ne_top hΩfin (measure_mono Set.diff_subset)) v) from by abel,
    norm_neg, MeasureTheory.norm_indicatorConstLp hp0 hp_top]
  refine lt_of_le_of_lt ?_ hN
  gcongr
  exact ENNReal.toReal_mono (hDfin N) (measure_mono hsub)

/-- A nonnegative real series that vanishes below `k₀` and is dominated past
`k₀` by a geometric tail `B · d^{k-k₀}` (with `0 ≤ d < 1`) has total mass at
most `B / (1 - d)`. -/
private theorem geometric_tail_tsum_le
    {f : ℕ → ℝ} {B d : ℝ} (k₀ : ℕ)
    (hfnn : ∀ k, 0 ≤ f k)
    (hf0 : ∀ k, k < k₀ → f k = 0)
    (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hfb : ∀ k, k₀ ≤ k → f k ≤ B * d ^ (k - k₀)) :
    ∑' k, f k ≤ B / (1 - d) := by
  have hgsum : Summable (fun m : ℕ => B * d ^ m) :=
    (summable_geometric_of_lt_one hd0 hd1).mul_left B
  have hshift_le : ∀ m, f (m + k₀) ≤ B * d ^ m := by
    intro m
    simpa [Nat.add_sub_cancel] using hfb (m + k₀) (Nat.le_add_left k₀ m)
  have hshift_sum : Summable (fun m => f (m + k₀)) :=
    Summable.of_nonneg_of_le (fun m => hfnn _) hshift_le hgsum
  have hsum : Summable f := (summable_nat_add_iff k₀).1 hshift_sum
  rw [← hsum.sum_add_tsum_nat_add k₀,
    Finset.sum_eq_zero (fun i hi => hf0 i (Finset.mem_range.mp hi)), zero_add]
  calc ∑' m, f (m + k₀)
      ≤ ∑' m, B * d ^ m := Summable.tsum_le_tsum hshift_le hshift_sum hgsum
    _ = B * ∑' m, d ^ m := tsum_mul_left
    _ = B * (1 - d)⁻¹ := by rw [tsum_geometric_of_lt_one hd0 hd1]
    _ = B / (1 - d) := (div_eq_mul_inv B (1 - d)).symm

/--
The indicator estimate `(estG)` for a regular domain.

The constant is written in the finite-`q` form from the paper.  The case
`q = ∞` has the usual supremum interpretation and should be added as a
separate wrapper when needed.
-/
theorem regularDomain_indicator_besov_norm_bound
    (G : GoodGridSpace (α := α)) (Ω : Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) (hq_top : q ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularDomain G Ω (1 - p.toReal * s) C c) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (Ω.indicator fun _ => (1 : ℂ))
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs hp hp_top) q y ≤
        C ^ (1 / p.toReal) /
            (1 - c ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) *
          (G.grid.μ Ω).toReal ^ (1 / p.toReal - s) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  letI : MeasureTheory.IsFiniteMeasure G.toWeakGridSpace.measure := G.grid.isFinite
  set A := souzaAtomFamily G s p hs hp hp_top with hAdef
  set a : ℝ := 1 - p.toReal * s with hadef
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hqr : 0 < q.toReal :=
    ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one (Fact.out (p := (1 : ℝ≥0∞) ≤ q))).ne' hq_top
  have hqp_pos : 0 < q.toReal / p.toReal := div_pos hqr hpr
  have hc : 0 ≤ c := hΩ.c_nonneg
  have hgeom : c ^ (q.toReal / p.toReal) < 1 :=
    Real.rpow_lt_one hc hΩ.c_lt_one hqp_pos
  have hΩfin : G.toWeakGridSpace.measure Ω ≠ ∞ := measure_ne_top _ _
  have hΩpos : 0 < (G.grid.μ Ω).toReal := by
    obtain ⟨W, hWsub⟩ := firstContainedLevel_spec G hΩ.contains_cell
    exact ENNReal.toReal_pos
      (lt_of_lt_of_le (G.grid.positive_measure _ W.1 W.2) (measure_mono hWsub)).ne' hΩfin
  have hμa_pos : 0 < (G.grid.μ Ω).toReal ^ a := Real.rpow_pos_of_pos hΩpos a
  -- The cost constant is nonnegative.
  have hC : 0 ≤ C := by
    have hcost := hΩ.cost (firstContainedLevel G Ω)
    rw [Nat.sub_self, pow_zero, mul_one] at hcost
    have h0 : 0 ≤ C * (G.grid.μ Ω).toReal ^ a :=
      le_trans (Finset.sum_nonneg fun Q _ => Real.rpow_nonneg ENNReal.toReal_nonneg _) hcost
    by_contra hCneg
    push_neg at hCneg
    exact absurd h0 (not_le.mpr (mul_neg_of_neg_of_pos hCneg hμa_pos))
  -- The level cells tiling `Ω`.
  set E : ℕ → Set α := fun k => ⋃ Q ∈ hΩ.family k, (Q : Set α) with hEdef
  have hEmeas : ∀ k, MeasurableSet (E k) := fun k =>
    MeasurableSet.biUnion (hΩ.family k).countable_toSet
      (fun Q hQ => G.grid.grid.measurable k Q (hΩ.family_subset k hQ))
  have hEsubΩ : ∀ k, E k ⊆ Ω := by
    intro k
    rw [hΩ.cover]
    exact Set.subset_iUnion (fun k => ⋃ Q ∈ hΩ.family k, (Q : Set α)) k
  have hEfin : ∀ k, G.toWeakGridSpace.measure (E k) ≠ ∞ := fun k =>
    ne_top_of_le_ne_top hΩfin (measure_mono (hEsubΩ k))
  have hEdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    rcases Set.mem_iUnion₂.mp hzi with ⟨P, hP, hzP⟩
    rcases Set.mem_iUnion₂.mp hzj with ⟨Q, hQ, hzQ⟩
    by_cases hPQ : P = Q
    · subst hPQ
      have hPi : P ∈ G.grid.grid.partitions i := hΩ.family_subset i hP
      have hPj : P ∈ G.grid.grid.partitions j := hΩ.family_subset j hQ
      rcases lt_or_gt_of_ne hij with h | h
      · exact goodGridCell_not_subset_of_level_lt G ⟨j, P, hPj⟩ ⟨P, hPi⟩ h subset_rfl
      · exact goodGridCell_not_subset_of_level_lt G ⟨i, P, hPi⟩ ⟨P, hPj⟩ h subset_rfl
    · exact Set.disjoint_left.mp
        (hΩ.pairwise_disjoint_cells i j P Q hP hQ hPQ) hzP hzQ
  have hcover' : Ω = ⋃ k, E k := hΩ.cover
  -- The atomic block family realizing `1_Ω = ∑_k ∑_{Q ∈ F^k} 1_Q`.
  let block : (k : ℕ) → WeakGridSpace.LevelBlock A k := fun k =>
    { coeff := fun P =>
        if P.1 ∈ hΩ.family k then
          (((G.grid.μ P.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ) else 0
      atom := fun P => (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)
      atom_mem := fun P => by
        change ‖((((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ)) : ℂ)‖
          ≤ (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹)
        simp [Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)] }
  -- Each block evaluates to the indicator of the level-`k` tile.
  have htoLp : ∀ k, (block k).toLp A = MeasureTheory.indicatorConstLp
      (μ := G.toWeakGridSpace.measure) p (hEmeas k) (hEfin k) 1 := by
    intro k
    apply MeasureTheory.Lp.ext
    refine (WeakGridSpace.LevelBlock.coeFn_toLp A (block k)).trans ?_
    have hpoint : (block k).toFunLt A =ᵐ[G.toWeakGridSpace.measure]
        (E k).indicator (fun _ => (1 : ℂ)) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      unfold WeakGridSpace.LevelBlock.toFunLt
      by_cases hx : x ∈ E k
      · rcases Set.mem_iUnion₂.mp hx with ⟨Q₀, hQ₀, hxQ₀⟩
        rw [Set.indicator_of_mem hx,
          Finset.sum_eq_single ⟨Q₀, hΩ.family_subset k hQ₀⟩]
        · have hQ₀pos : 0 < (G.grid.μ Q₀).toReal :=
            ENNReal.toReal_pos
              (G.grid.positive_measure _ Q₀ (hΩ.family_subset k hQ₀)).ne' (measure_ne_top _ _)
          simp only [block, A, WeakGridSpace.AtomFamily.toFunction,
            souzaAtomFamily, souzaLocalVectorSpace, hQ₀, if_true]
          change (((G.grid.μ Q₀).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
            * (Q₀.indicator (fun _ => (((G.grid.μ Q₀).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x) = 1
          rw [Set.indicator_of_mem hxQ₀, ← Complex.ofReal_mul,
            ← Real.rpow_add hQ₀pos,
            show ((p.toReal)⁻¹ - s) + (s - (p.toReal)⁻¹) = 0 from by ring,
            Real.rpow_zero, Complex.ofReal_one]
        · intro P _ hPne
          by_cases hPfam : P.1 ∈ hΩ.family k
          · have hxP : x ∉ P.1 := by
              intro hxP
              exact Set.disjoint_left.mp
                (hΩ.pairwise_disjoint_cells k k P.1 Q₀ hPfam hQ₀
                  (fun h => hPne (Subtype.ext h))) hxP hxQ₀
            simp only [block, A, WeakGridSpace.AtomFamily.toFunction,
              souzaAtomFamily, souzaLocalVectorSpace, hPfam, if_true]
            change (((G.grid.μ P.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
              * ((P.1).indicator (fun _ => (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x) = 0
            rw [Set.indicator_of_notMem hxP, mul_zero]
          · simp only [block, hPfam, if_false, zero_mul]
        · intro hnot
          exact absurd (Finset.mem_attach _ _) hnot
      · rw [Set.indicator_of_notMem hx]
        refine Finset.sum_eq_zero ?_
        intro P _
        by_cases hPfam : P.1 ∈ hΩ.family k
        · have hxP : x ∉ P.1 := fun hxP =>
            hx (Set.mem_iUnion₂.mpr ⟨P.1, hPfam, hxP⟩)
          simp only [block, A, WeakGridSpace.AtomFamily.toFunction,
            souzaAtomFamily, souzaLocalVectorSpace, hPfam, if_true]
          change (((G.grid.μ P.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
            * ((P.1).indicator (fun _ => (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)) x) = 0
          rw [Set.indicator_of_notMem hxP, mul_zero]
        · simp only [block, hPfam, if_false, zero_mul]
    exact hpoint.trans
      (MeasureTheory.indicatorConstLp_coeFn (μ := G.toWeakGridSpace.measure)
        (p := p) (hs := hEmeas k) (hμs := hEfin k) (c := (1 : ℂ))).symm
  -- Assemble the representation of `1_Ω`.
  set g₀ := MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
    hΩ.measurable hΩfin (1 : ℂ) with hg₀
  have hHasSum : HasSum (fun k => (block k).toLp A) g₀ := by
    have hfun : (fun k => (block k).toLp A)
        = fun k => MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
            (hEmeas k) (hEfin k) 1 := funext htoLp
    rw [hfun]
    exact hasSum_indicatorConstLp_iUnion G p hp_top E Ω hEmeas hEfin hEdisj
      hΩ.measurable hΩfin hcover' 1
  let R : WeakGridSpace.LpGridRepresentation A g₀ := { block := block, hasSum := hHasSum }
  -- The level coefficient power equals the regular-domain level cost.
  have hlcp : ∀ k, R.levelCoeffPower k = ∑ Q ∈ hΩ.family k, (G.grid.μ Q).toReal ^ a := by
    intro k
    have hexp : ((p.toReal)⁻¹ - s) * p.toReal = a := by
      rw [hadef, sub_mul, inv_mul_cancel₀ hpr.ne']; ring
    have hterm : ∀ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(block k).coeff P‖ ^ p.toReal
          = if P.1 ∈ hΩ.family k then (G.grid.μ P.1).toReal ^ a else 0 := by
      intro P
      by_cases hP : P.1 ∈ hΩ.family k
      · simp only [block, hP, if_true]
        rw [Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _),
          ← Real.rpow_mul ENNReal.toReal_nonneg, hexp]
      · simp only [block, hP, if_false, norm_zero, Real.zero_rpow hpr.ne']
    simp only [WeakGridSpace.LpGridRepresentation.levelCoeffPower, R]
    rw [Finset.sum_congr rfl (fun P _ => hterm P),
      Finset.sum_coe_sort (G.toWeakGridSpace.grid.partitions k)
        (fun Q => if Q ∈ hΩ.family k then (G.grid.μ Q).toReal ^ a else 0),
      ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (hΩ.family_subset k)]
  -- Geometric control of the coefficient cost.
  set d : ℝ := c ^ (q.toReal / p.toReal) with hddef
  have hd0 : 0 ≤ d := Real.rpow_nonneg hc _
  set B : ℝ := C ^ (q.toReal / p.toReal) * (G.grid.μ Ω).toReal ^ (a * (q.toReal / p.toReal))
    with hBdef
  have hf0 : ∀ k, k < firstContainedLevel G Ω →
      (R.levelCoeffPower k) ^ (q.toReal / p.toReal) = 0 := by
    intro k hk
    rw [hlcp, hΩ.family_empty_before k hk, Finset.sum_empty, Real.zero_rpow hqp_pos.ne']
  have hfb : ∀ k, firstContainedLevel G Ω ≤ k →
      (R.levelCoeffPower k) ^ (q.toReal / p.toReal) ≤ B * d ^ (k - firstContainedLevel G Ω) := by
    intro k _
    have hle : R.levelCoeffPower k ≤ C * c ^ (k - firstContainedLevel G Ω) * (G.grid.μ Ω).toReal ^ a := by
      rw [hlcp]; exact hΩ.cost k
    have hlcp_nonneg : 0 ≤ R.levelCoeffPower k := by
      rw [hlcp]; exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg ENNReal.toReal_nonneg _
    calc (R.levelCoeffPower k) ^ (q.toReal / p.toReal)
        ≤ (C * c ^ (k - firstContainedLevel G Ω) * (G.grid.μ Ω).toReal ^ a)
            ^ (q.toReal / p.toReal) :=
          Real.rpow_le_rpow hlcp_nonneg hle hqp_pos.le
      _ = B * d ^ (k - firstContainedLevel G Ω) := by
          rw [Real.mul_rpow (mul_nonneg hC (pow_nonneg hc _)) (Real.rpow_nonneg ENNReal.toReal_nonneg _),
            Real.mul_rpow hC (pow_nonneg hc _), hBdef, hddef,
            ← Real.rpow_natCast c (k - firstContainedLevel G Ω),
            ← Real.rpow_natCast (c ^ (q.toReal / p.toReal)) (k - firstContainedLevel G Ω),
            ← Real.rpow_mul hc, ← Real.rpow_mul hc,
            ← Real.rpow_mul ENNReal.toReal_nonneg,
            mul_comm (↑(k - firstContainedLevel G Ω) : ℝ) (q.toReal / p.toReal)]
          ring
  have hfnn : ∀ k, 0 ≤ (R.levelCoeffPower k) ^ (q.toReal / p.toReal) := fun k =>
    Real.rpow_nonneg (by
      rw [hlcp]; exact Finset.sum_nonneg fun Q _ => Real.rpow_nonneg ENNReal.toReal_nonneg _) _
  -- Summability of the coefficient cost series.
  have hgsum : Summable (fun m : ℕ => B * d ^ m) :=
    (summable_geometric_of_lt_one hd0 hgeom).mul_left B
  have hfsum : Summable (fun k => (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) := by
    rw [← summable_nat_add_iff (firstContainedLevel G Ω)]
    refine Summable.of_nonneg_of_le (fun m => hfnn _) (fun m => ?_) hgsum
    simpa [Nat.add_sub_cancel] using hfb (m + firstContainedLevel G Ω) (Nat.le_add_left _ _)
  have hFin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R := by
    rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hq_top]
    exact hfsum
  -- The Besov-ish element.
  refine ⟨⟨g₀, ⟨R, by rw [if_neg hq_top]; exact hfsum⟩⟩, ?_, ?_⟩
  · -- Represents `1_Ω`.
    exact MeasureTheory.indicatorConstLp_coeFn (μ := G.toWeakGridSpace.measure)
      (hs := hΩ.measurable) (hμs := hΩfin) (c := (1 : ℂ))
  · -- Cost bound.
    refine le_trans (WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
      (A := A) (q := q) ⟨g₀, ⟨R, by rw [if_neg hq_top]; exact hfsum⟩⟩ R hFin) ?_
    rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hq_top]
    have htsum_le : (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ≤ B / (1 - d) :=
      geometric_tail_tsum_le (firstContainedLevel G Ω) hfnn hf0 hd0 hgeom hfb
    have h1md : 0 < 1 - d := by linarith
    have e1 : q.toReal / p.toReal * (1 / q.toReal) = 1 / p.toReal := by
      field_simp
    have e2 : a * (q.toReal / p.toReal) * (1 / q.toReal) = 1 / p.toReal - s := by
      rw [hadef]; field_simp
    calc (∑' k, (R.levelCoeffPower k) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)
        ≤ (B / (1 - d)) ^ (1 / q.toReal) :=
          Real.rpow_le_rpow (tsum_nonneg hfnn) htsum_le (by positivity)
      _ = C ^ (1 / p.toReal) /
            (1 - d) ^ (1 / q.toReal) *
          (G.grid.μ Ω).toReal ^ (1 / p.toReal - s) := by
          rw [hBdef, Real.div_rpow (by positivity) (le_of_lt h1md),
            Real.mul_rpow (Real.rpow_nonneg hC _) (Real.rpow_nonneg ENNReal.toReal_nonneg _),
            ← Real.rpow_mul hC, ← Real.rpow_mul ENNReal.toReal_nonneg, e1, e2]
          ring

/--
The bounded multiplier operator `g ↦ g · 1_Ω` on
`B^s_{p,q} ∩ L∞` for a regular domain.

This packages estimate `(G)` in the same concrete-representative style as
`souzaPointwiseMultipliersIII`: the output represents the pointwise product
with the characteristic function, and its Besov gauge is bounded by a constant
times the bounded Besov norm of the input.
-/
theorem regularDomain_indicator_multiplier_on_bounded_souzaBesov
    (G : GoodGridSpace (α := α)) (Ω : Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) (hq_top : q ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularDomain G Ω (1 - p.toReal * s) C c) :
    ∃ Cop : ℝ,
      0 ≤ Cop ∧
      ∀ (g : α → ℂ) (M : ℝ)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => g z * Ω.indicator (fun _ => (1 : ℂ)) z)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q y ≤
            Cop *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                  (souzaAtomFamily G s p hs hp hp_top) q xg + M) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  set A := souzaAtomFamily G s p hs hp hp_top with hAdef
  have hA := WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A q
  -- The indicator `1_Ω` as a Besov element with the estimate `(estG)`.
  obtain ⟨yΩ, hyΩrepr, hyΩcost⟩ :=
    regularDomain_indicator_besov_norm_bound G Ω s C c p q hs hs_lt_inv hp hp_top hq_top hΩ
  set E : ℝ := C ^ (1 / p.toReal) /
      (1 - c ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) *
        (G.grid.μ Ω).toReal ^ (1 / p.toReal - s) with hEdef
  have hcyΩ : 0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A q yΩ :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg hA yΩ
  have hE : 0 ≤ E := le_trans hcyΩ hyΩcost
  -- The quasi-algebra product bound.
  obtain ⟨Cqa, hCqa, hIII⟩ := souzaPointwiseMultipliersIII G s p q hs hs_lt_inv hp hp_top
  refine ⟨Cqa * (E + 1), mul_nonneg hCqa (by linarith), ?_⟩
  intro g M xg hgrepr hgbdd
  -- `M ≥ 0`, since `‖g‖ ≤ M` holds a.e. on a space of positive measure.
  have hΩ0 : 0 < G.toWeakGridSpace.measure Ω := by
    obtain ⟨W, hWsub⟩ := firstContainedLevel_spec G hΩ.contains_cell
    exact lt_of_lt_of_le (G.grid.positive_measure _ W.1 W.2) (measure_mono hWsub)
  have hμne : G.toWeakGridSpace.measure ≠ 0 := by
    intro h
    rw [h] at hΩ0
    simp at hΩ0
  haveI : (MeasureTheory.ae G.toWeakGridSpace.measure).NeBot :=
    MeasureTheory.ae_neBot.2 hμne
  have hM : 0 ≤ M := by
    obtain ⟨z, hz⟩ :=
      (hgbdd.and (Filter.Eventually.of_forall fun z => norm_nonneg (g z))).exists
    exact le_trans hz.2 hz.1
  -- `1_Ω` is bounded by `1`.
  have hΩbdd : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      ‖Ω.indicator (fun _ => (1 : ℂ)) z‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ Ω <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  -- Apply the quasi-algebra product to `g` and `1_Ω`.
  obtain ⟨y, hyrepr, hycost, _⟩ :=
    hIII g (Ω.indicator fun _ => (1 : ℂ)) M 1 xg yΩ hgrepr hyΩrepr hgbdd hΩbdd
  refine ⟨y, hyrepr, ?_⟩
  have hcxg : 0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A q xg :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg hA xg
  calc WeakGridSpace.BesovishSpace.Norm_Costpq A q y
      ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A q y + M * 1 := by
        rw [mul_one]; linarith
    _ ≤ Cqa * ((WeakGridSpace.BesovishSpace.Norm_Costpq A q xg + M) *
          (WeakGridSpace.BesovishSpace.Norm_Costpq A q yΩ + 1)) := hycost
    _ ≤ Cqa * ((WeakGridSpace.BesovishSpace.Norm_Costpq A q xg + M) * (E + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hCqa
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith
    _ = Cqa * (E + 1) * (WeakGridSpace.BesovishSpace.Norm_Costpq A q xg + M) := by ring

/-- Canonical Souza representation of the indicator of one active member of a
regular family. -/
theorem regularFamilyIndicator_besov_representation
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i : ℕ} (hi : i ∈ Λ) :
    ∃ yind : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
    ∃ Rind : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        (yind : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        ((Ω i).indicator fun _ => (1 : ℂ))
        (yind : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rind ∧
      ∀ k, Rind.block k =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  letI : MeasureTheory.IsFiniteMeasure G.toWeakGridSpace.measure := G.grid.isFinite
  let A := souzaAtomFamily G s p hs hp hp_top
  let a : ℝ := 1 - p.toReal * s
  let E : ℕ → Set α := fun k => ⋃ Q ∈ hΩ.family i k, (Q : Set α)
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have ha_pos : 0 < a := by
    dsimp [a]
    have hmul : p.toReal * s < 1 := by
      have hpinv_mul : p.toReal⁻¹ * p.toReal = 1 := by
        field_simp [hpr.ne']
      calc
        p.toReal * s < p.toReal * p.toReal⁻¹ := by
          exact mul_lt_mul_of_pos_left hs_lt_inv hpr
        _ = 1 := by rw [mul_comm, hpinv_mul]
    linarith
  have hEmeas : ∀ k, MeasurableSet (E k) := fun k =>
    MeasurableSet.biUnion (hΩ.family i k).countable_toSet
      (fun Q hQ => G.grid.grid.measurable k Q (hΩ.family_subset i hi k hQ))
  have hEsubΩ : ∀ k, E k ⊆ Ω i := by
    intro k z hz
    rcases Set.mem_iUnion₂.mp hz with ⟨Q, hQ, hzQ⟩
    exact hΩ.cell_subset_domain hi hQ hzQ
  have hEfin : ∀ k, G.toWeakGridSpace.measure (E k) ≠ ∞ := fun k =>
    ne_top_of_le_ne_top (measure_ne_top _ _) (measure_mono (hEsubΩ k))
  have hEdisj : ∀ k l, k ≠ l → Disjoint (E k) (E l) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro z hzk hzl
    rcases Set.mem_iUnion₂.mp hzk with ⟨P, hP, hzP⟩
    rcases Set.mem_iUnion₂.mp hzl with ⟨Q, hQ, hzQ⟩
    by_cases hPQ : P = Q
    · subst hPQ
      have hPk : P ∈ G.grid.grid.partitions k := hΩ.family_subset i hi k hP
      have hPl : P ∈ G.grid.grid.partitions l := hΩ.family_subset i hi l hQ
      rcases lt_or_gt_of_ne hkl with hlt | hgt
      · exact goodGridCell_not_subset_of_level_lt G ⟨l, P, hPl⟩ ⟨P, hPk⟩ hlt subset_rfl
      · exact goodGridCell_not_subset_of_level_lt G ⟨k, P, hPk⟩ ⟨P, hPl⟩ hgt subset_rfl
    · exact Set.disjoint_left.mp
        (hΩ.pairwise_disjoint_cells i hi k l P Q hP hQ hPQ) hzP hzQ
  let block : (k : ℕ) → WeakGridSpace.LevelBlock A k := fun k =>
    regularFamilyIndicatorBlock
      (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k
  have htoLp : ∀ k, (block k).toLp A =
      MeasureTheory.indicatorConstLp
        (μ := G.toWeakGridSpace.measure) p (hEmeas k) (hEfin k) 1 := by
    intro k
    apply Lp.ext
    exact (regularFamilyIndicatorBlock_represents_levelTile
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ hi).trans
        (MeasureTheory.indicatorConstLp_coeFn
          (μ := G.toWeakGridSpace.measure) (p := p)
          (hs := hEmeas k) (hμs := hEfin k) (c := (1 : ℂ))).symm
  set g₀ := MeasureTheory.indicatorConstLp (μ := G.toWeakGridSpace.measure) p
    (hΩ.measurable i hi) (measure_ne_top _ _) (1 : ℂ) with hg₀
  have hHasSum0 : HasSum
      (fun k => MeasureTheory.indicatorConstLp
        (μ := G.toWeakGridSpace.measure) p (hEmeas k) (hEfin k) (1 : ℂ)) g₀ := by
    simpa [g₀, E] using
      hasSum_indicatorConstLp_iUnion G p hp_top E (Ω i) hEmeas hEfin hEdisj
        (hΩ.measurable i hi) (measure_ne_top _ _) (hΩ.cover i hi) (1 : ℂ)
  have hHasSum : HasSum (fun k => (block k).toLp A) g₀ :=
    hHasSum0.congr_fun fun k => htoLp k
  let R : WeakGridSpace.LpGridRepresentation A g₀ := { block := block, hasSum := hHasSum }
  have hlevel_le : ∀ k,
      R.levelCoeffPower k ≤
        C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
          (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a := by
    intro k
    change
      (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k).coeff P‖ ^
          p.toReal) ≤
        C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
          (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a
    dsimp [a]
    exact regularFamilyIndicatorBlock_levelCoeffPower_le_familyCost
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ hi
  have hFin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R := by
    by_cases hq : q = ∞
    · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_pos hq]
      let D : ℝ := C * (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a
      have hD0 : 0 ≤ D := mul_nonneg hΩ.C_nonneg
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      refine ⟨D ^ (1 / p.toReal), ?_⟩
      rintro x ⟨k, rfl⟩
      have hc_pow_le : c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) ≤ 1 :=
        pow_le_one₀ hΩ.c_nonneg hΩ.c_lt_one.le
      have hlevelD : R.levelCoeffPower k ≤ D := by
        have hμa0 : 0 ≤ (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a :=
          Real.rpow_nonneg ENNReal.toReal_nonneg _
        have hc_mul_le : C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) ≤
            C * 1 :=
          mul_le_mul_of_nonneg_left hc_pow_le hΩ.C_nonneg
        calc
          R.levelCoeffPower k
              ≤ C * c ^ (k - firstContainedLevel G (regularFamilyUnion Λ Ω)) *
                  (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a := hlevel_le k
          _ ≤ C * 1 * (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a := by
            exact mul_le_mul_of_nonneg_right hc_mul_le hμa0
          _ = D := by ring
      exact Real.rpow_le_rpow (R.levelCoeffPower_nonneg k) hlevelD
        (one_div_nonneg.mpr hpr.le)
    · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hq]
      have hqr : 0 < q.toReal :=
        ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
      have hqp_pos : 0 < q.toReal / p.toReal := div_pos hqr hpr
      let d : ℝ := c ^ (q.toReal / p.toReal)
      have hd0 : 0 ≤ d := Real.rpow_nonneg hΩ.c_nonneg _
      have hd1 : d < 1 := Real.rpow_lt_one hΩ.c_nonneg hΩ.c_lt_one hqp_pos
      let B : ℝ := (C * (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a) ^
        (q.toReal / p.toReal)
      have hBgeom : Summable (fun m : ℕ => B * d ^ m) :=
        (summable_geometric_of_lt_one hd0 hd1).mul_left B
      rw [← summable_nat_add_iff (firstContainedLevel G (regularFamilyUnion Λ Ω))]
      refine Summable.of_nonneg_of_le
        (fun m => Real.rpow_nonneg (R.levelCoeffPower_nonneg _) _) ?_ hBgeom
      intro m
      have hbase0 :
          0 ≤ C * c ^ m *
            (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a :=
        mul_nonneg (mul_nonneg hΩ.C_nonneg (pow_nonneg hΩ.c_nonneg _))
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      have hlevel :
          R.levelCoeffPower (m + firstContainedLevel G (regularFamilyUnion Λ Ω)) ≤
            C * c ^ m *
              (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a := by
        simpa [Nat.add_sub_cancel] using
          hlevel_le (m + firstContainedLevel G (regularFamilyUnion Λ Ω))
      calc
        (R.levelCoeffPower (m + firstContainedLevel G (regularFamilyUnion Λ Ω))) ^
            (q.toReal / p.toReal)
            ≤ (C * c ^ m *
                (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a) ^
                (q.toReal / p.toReal) :=
          Real.rpow_le_rpow (R.levelCoeffPower_nonneg _) hlevel hqp_pos.le
        _ = B * d ^ m := by
          have hCμ0 :
              0 ≤ C * (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a :=
            mul_nonneg hΩ.C_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
          rw [show C * c ^ m *
                (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a =
                (C * (G.grid.μ (regularFamilyUnion Λ Ω)).toReal ^ a) * c ^ m by ring]
          rw [Real.mul_rpow hCμ0 (pow_nonneg hΩ.c_nonneg _)]
          rw [← Real.rpow_natCast c m,
            ← Real.rpow_natCast (c ^ (q.toReal / p.toReal)) m,
            ← Real.rpow_mul hΩ.c_nonneg, ← Real.rpow_mul hΩ.c_nonneg]
          congr 1
          ring_nf
  let yind : WeakGridSpace.BesovishSpace A q := ⟨g₀, ⟨R, hFin⟩⟩
  refine ⟨yind, R, ?_, hFin, ?_⟩
  · exact MeasureTheory.indicatorConstLp_coeFn
      (μ := G.toWeakGridSpace.measure) (p := p)
      (hs := hΩ.measurable i hi) (hμs := measure_ne_top _ _) (c := (1 : ℂ))
  · intro k
    rfl

/-- Positive canonical Souza representation of the indicator of one active
member of a regular family. -/
theorem regularFamilyIndicator_besov_positive_representation
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {i : ℕ} (hi : i ∈ Λ) :
    ∃ yind : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
    ∃ Rind : WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        (yind : Lp ℂ p G.toWeakGridSpace.measure),
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        ((Ω i).indicator fun _ => (1 : ℂ))
        (yind : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rind ∧
      SouzaPositiveRepresentation G s p hs hp hp_top Rind ∧
      ∀ k, Rind.block k =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k := by
  obtain ⟨yind, Rind, hrep, hfin, hblock⟩ :=
    regularFamilyIndicator_besov_representation
      G Λ Ω s C c p q hs hs_lt_inv hp hp_top hΩ hi
  refine ⟨yind, Rind, hrep, hfin, ?_, hblock⟩
  intro k
  rw [hblock k]
  exact regularFamilyIndicatorBlock_positive
    (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
    (p := p) hΩ i k

/--
Endpoint version of `regularDomain_indicator_besov_norm_bound`.

For `q = ∞`, the geometric series in `(estG)` is replaced by a supremum, so
the regular-domain indicator has the simpler bound
`C ^ (1 / p) * μ(Ω) ^ (1 / p - s)`.
-/
theorem regularDomain_indicator_besov_norm_bound_top
    (G : GoodGridSpace (α := α)) (Ω : Set α)
    (s C c : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hΩ : RegularDomain G Ω (1 - p.toReal * s) C c) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) ∞,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (Ω.indicator fun _ => (1 : ℂ))
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs hp hp_top) ∞ y ≤
        C ^ (1 / p.toReal) *
          (G.grid.μ Ω).toReal ^ (1 / p.toReal - s) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  letI : MeasureTheory.IsFiniteMeasure G.toWeakGridSpace.measure := G.grid.isFinite
  let A := souzaAtomFamily G s p hs hp hp_top
  let hFam : RegularFamily G ({0} : Set ℕ) (fun _ : ℕ => Ω)
      (1 - p.toReal * s) C c :=
    hΩ.toRegularFamily_singleton
  have h0mem : (0 : ℕ) ∈ ({0} : Set ℕ) := by simp
  obtain ⟨y, R, hyrepr, hRfin, hblock⟩ :=
    regularFamilyIndicator_besov_representation
      G ({0} : Set ℕ) (fun _ : ℕ => Ω) s C c p ∞
      hs hs_lt_inv hp hp_top hFam h0mem
  refine ⟨y, hyrepr, ?_⟩
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hroot_nonneg : 0 ≤ 1 / p.toReal := one_div_nonneg.mpr hpr.le
  have hlevel_le :
      ∀ k, R.levelCoeffPower k ≤
        C * c ^ (k - firstContainedLevel G Ω) *
          (G.grid.μ Ω).toReal ^ (1 - p.toReal * s) := by
    intro k
    change
      (∑ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(R.block k).coeff P‖ ^ p.toReal) ≤
        C * c ^ (k - firstContainedLevel G Ω) *
          (G.grid.μ Ω).toReal ^ (1 - p.toReal * s)
    rw [hblock k]
    have hraw :=
      regularFamilyIndicatorBlock_levelCoeffPower_le_familyCost
        (G := G) (Λ := ({0} : Set ℕ)) (Ω := fun _ : ℕ => Ω)
        (s := s) (C := C) (c := c) (p := p)
        (hs := hs) (hp := hp) (hp_top := hp_top) hFam h0mem
        (k := k)
    simpa [regularFamilyUnion] using hraw
  have hlevel_root_le :
      ∀ k, (R.levelCoeffPower k) ^ (1 / p.toReal) ≤
        C ^ (1 / p.toReal) *
          (G.grid.μ Ω).toReal ^ (1 / p.toReal - s) := by
    intro k
    have hc_pow_le : c ^ (k - firstContainedLevel G Ω) ≤ 1 :=
      pow_le_one₀ hΩ.c_nonneg hΩ.c_lt_one.le
    have hμa0 : 0 ≤ (G.grid.μ Ω).toReal ^ (1 - p.toReal * s) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hlevelD :
        R.levelCoeffPower k ≤ C * (G.grid.μ Ω).toReal ^ (1 - p.toReal * s) := by
      calc
        R.levelCoeffPower k
            ≤ C * c ^ (k - firstContainedLevel G Ω) *
                (G.grid.μ Ω).toReal ^ (1 - p.toReal * s) := hlevel_le k
        _ ≤ C * 1 * (G.grid.μ Ω).toReal ^ (1 - p.toReal * s) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hc_pow_le hΩ.C_nonneg) hμa0
        _ = C * (G.grid.μ Ω).toReal ^ (1 - p.toReal * s) := by ring
    calc
      (R.levelCoeffPower k) ^ (1 / p.toReal)
          ≤ (C * (G.grid.μ Ω).toReal ^ (1 - p.toReal * s)) ^
              (1 / p.toReal) :=
        Real.rpow_le_rpow (R.levelCoeffPower_nonneg k) hlevelD hroot_nonneg
      _ = C ^ (1 / p.toReal) *
            (G.grid.μ Ω).toReal ^ (1 / p.toReal - s) := by
        rw [Real.mul_rpow hΩ.C_nonneg
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
        rw [← Real.rpow_mul ENNReal.toReal_nonneg]
        congr 1
        field_simp [hpr.ne']
  refine le_trans (WeakGridSpace.BesovishSpace.Norm_Costpq_le_cost
    (A := A) (q := ∞) y R hRfin) ?_
  rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos rfl]
  exact csSup_le (Set.range_nonempty _) (by
    rintro x ⟨k, rfl⟩
    exact hlevel_root_le k)

/-- The regular-domain indicator bound, with the endpoint `q = ∞` folded in. -/
noncomputable def regularDomainIndicatorCost
    (G : GoodGridSpace (α := α)) (Ω : Set α)
    (s C c : ℝ) (p q : ℝ≥0∞) : ℝ :=
  if q = ∞ then
    C ^ (1 / p.toReal) *
      (G.grid.μ Ω).toReal ^ (1 / p.toReal - s)
  else
    C ^ (1 / p.toReal) /
        (1 - c ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) *
      (G.grid.μ Ω).toReal ^ (1 / p.toReal - s)

/-- The regular-domain indicator gauge is nonnegative for genuine regular
domains. -/
theorem regularDomainIndicatorCost_nonneg
    (G : GoodGridSpace (α := α)) (Ω : Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ q)]
    (hΩ : RegularDomain G Ω (1 - p.toReal * s) C c) :
    0 ≤ regularDomainIndicatorCost G Ω s C c p q := by
  classical
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hCpow : 0 ≤ C ^ (1 / p.toReal) :=
    Real.rpow_nonneg hΩ.C_nonneg _
  have hμpow : 0 ≤ (G.grid.μ Ω).toReal ^ (1 / p.toReal - s) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  by_cases hq : q = ∞
  · simp only [regularDomainIndicatorCost, hq, if_true]
    exact mul_nonneg hCpow hμpow
  · have hqr : 0 < q.toReal :=
      ENNReal.toReal_pos
        (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    have hqp_pos : 0 < q.toReal / p.toReal := div_pos hqr hpr
    have hgeom : c ^ (q.toReal / p.toReal) < 1 :=
      Real.rpow_lt_one hΩ.c_nonneg hΩ.c_lt_one hqp_pos
    have hden_nonneg :
        0 ≤ (1 - c ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) :=
      (Real.rpow_pos_of_pos (sub_pos.mpr hgeom) _).le
    simp only [regularDomainIndicatorCost, hq, if_false]
    exact mul_nonneg (div_nonneg hCpow hden_nonneg) hμpow

/--
All-`q` wrapper for the regular-domain indicator estimate `(estG)`.

For finite `q` this is `regularDomain_indicator_besov_norm_bound`; at
`q = ∞` it is `regularDomain_indicator_besov_norm_bound_top`.
-/
theorem regularDomain_indicator_besov_norm_bound_all
    (G : GoodGridSpace (α := α)) (Ω : Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularDomain G Ω (1 - p.toReal * s) C c) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (Ω.indicator fun _ => (1 : ℂ))
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs hp hp_top) q y ≤
        regularDomainIndicatorCost G Ω s C c p q := by
  classical
  by_cases hq : q = ∞
  · subst q
    simpa [regularDomainIndicatorCost] using
      regularDomain_indicator_besov_norm_bound_top
        G Ω s C c p hs hs_lt_inv hp hp_top hΩ
  · simpa [regularDomainIndicatorCost, hq] using
      regularDomain_indicator_besov_norm_bound
        G Ω s C c p q hs hs_lt_inv hp hp_top hq hΩ

/--
Endpoint bounded multiplier estimate for the regular-domain indicator.

This is the `q = ∞` companion to
`regularDomain_indicator_multiplier_on_bounded_souzaBesov`.
-/
theorem regularDomain_indicator_multiplier_on_bounded_souzaBesov_top
    (G : GoodGridSpace (α := α)) (Ω : Set α)
    (s C c : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hΩ : RegularDomain G Ω (1 - p.toReal * s) C c) :
    ∃ Cop : ℝ,
      0 ≤ Cop ∧
      ∀ (g : α → ℂ) (M : ℝ)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) ∞),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) ∞,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => g z * Ω.indicator (fun _ => (1 : ℂ)) z)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) ∞ y ≤
            Cop *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                  (souzaAtomFamily G s p hs hp hp_top) ∞ xg + M) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  set A := souzaAtomFamily G s p hs hp hp_top
  have hA := WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A ∞
  obtain ⟨yΩ, hyΩrepr, hyΩcost⟩ :=
    regularDomain_indicator_besov_norm_bound_top
      G Ω s C c p hs hs_lt_inv hp hp_top hΩ
  set E : ℝ := C ^ (1 / p.toReal) *
    (G.grid.μ Ω).toReal ^ (1 / p.toReal - s) with hEdef
  have hcyΩ : 0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A ∞ yΩ :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg hA yΩ
  have hE : 0 ≤ E := le_trans hcyΩ hyΩcost
  obtain ⟨Cqa, hCqa, hIII⟩ :=
    souzaPointwiseMultipliersIII G s p ∞ hs hs_lt_inv hp hp_top
  refine ⟨Cqa * (E + 1), mul_nonneg hCqa (by linarith), ?_⟩
  intro g M xg hgrepr hgbdd
  have hΩ0 : 0 < G.toWeakGridSpace.measure Ω := by
    obtain ⟨W, hWsub⟩ := firstContainedLevel_spec G hΩ.contains_cell
    exact lt_of_lt_of_le (G.grid.positive_measure _ W.1 W.2) (measure_mono hWsub)
  have hμne : G.toWeakGridSpace.measure ≠ 0 := by
    intro h
    rw [h] at hΩ0
    simp at hΩ0
  haveI : (MeasureTheory.ae G.toWeakGridSpace.measure).NeBot :=
    MeasureTheory.ae_neBot.2 hμne
  have hM : 0 ≤ M := by
    obtain ⟨z, hz⟩ :=
      (hgbdd.and (Filter.Eventually.of_forall fun z => norm_nonneg (g z))).exists
    exact le_trans hz.2 hz.1
  have hΩbdd : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      ‖Ω.indicator (fun _ => (1 : ℂ)) z‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ Ω <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  obtain ⟨y, hyrepr, hycost, _⟩ :=
    hIII g (Ω.indicator fun _ => (1 : ℂ)) M 1 xg yΩ
      hgrepr hyΩrepr hgbdd hΩbdd
  refine ⟨y, hyrepr, ?_⟩
  have hcxg : 0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A ∞ xg :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg hA xg
  calc WeakGridSpace.BesovishSpace.Norm_Costpq A ∞ y
      ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A ∞ y + M * 1 := by
        rw [mul_one]; linarith
    _ ≤ Cqa * ((WeakGridSpace.BesovishSpace.Norm_Costpq A ∞ xg + M) *
          (WeakGridSpace.BesovishSpace.Norm_Costpq A ∞ yΩ + 1)) := hycost
    _ ≤ Cqa * ((WeakGridSpace.BesovishSpace.Norm_Costpq A ∞ xg + M) * (E + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hCqa
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith
    _ = Cqa * (E + 1) * (WeakGridSpace.BesovishSpace.Norm_Costpq A ∞ xg + M) := by ring

/--
All-`q` wrapper for the bounded multiplier estimate
`g ↦ g · 1_Ω` on `B^s_{p,q} ∩ L∞`.
-/
theorem regularDomain_indicator_multiplier_on_bounded_souzaBesov_all
    (G : GoodGridSpace (α := α)) (Ω : Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularDomain G Ω (1 - p.toReal * s) C c) :
    ∃ Cop : ℝ,
      0 ≤ Cop ∧
      ∀ (g : α → ℂ) (M : ℝ)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => g z * Ω.indicator (fun _ => (1 : ℂ)) z)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q y ≤
            Cop *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                  (souzaAtomFamily G s p hs hp hp_top) q xg + M) := by
  classical
  by_cases hq : q = ∞
  · subst q
    simpa using
      regularDomain_indicator_multiplier_on_bounded_souzaBesov_top
        G Ω s C c p hs hs_lt_inv hp hp_top hΩ
  · exact
      regularDomain_indicator_multiplier_on_bounded_souzaBesov
        G Ω s C c p q hs hs_lt_inv hp hp_top hq hΩ

/-- All-`q` indicator estimate for the union of a regular family. -/
theorem regularFamilyUnion_indicator_besov_norm_bound_all
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c) :
    ∃ y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        ((regularFamilyUnion Λ Ω).indicator fun _ => (1 : ℂ))
        (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s p hs hp hp_top) q y ≤
        regularDomainIndicatorCost G (regularFamilyUnion Λ Ω) s C c p q := by
  rcases hΩ.regularDomain_union with ⟨hUnion⟩
  exact regularDomain_indicator_besov_norm_bound_all
    G (regularFamilyUnion Λ Ω) s C c p q hs hs_lt_inv hp hp_top hUnion

/--
All-`q` bounded multiplier estimate for the indicator of the union of a
regular family.
-/
theorem regularFamilyUnion_indicator_multiplier_on_bounded_souzaBesov_all
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c) :
    ∃ Cop : ℝ,
      0 ≤ Cop ∧
      ∀ (g : α → ℂ) (M : ℝ)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => g z *
              (regularFamilyUnion Λ Ω).indicator (fun _ => (1 : ℂ)) z)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q y ≤
            Cop *
              (WeakGridSpace.BesovishSpace.Norm_Costpq
                  (souzaAtomFamily G s p hs hp hp_top) q xg + M) := by
  rcases hΩ.regularDomain_union with ⟨hUnion⟩
  exact regularDomain_indicator_multiplier_on_bounded_souzaBesov_all
    G (regularFamilyUnion Λ Ω) s C c p q hs hs_lt_inv hp hp_top hUnion

/--
The representation estimate `(pdd)`/`(hiip1)` for a regular family.

Each restriction `g · 1_{Ωᵣ}` receives a Souza representation whose nonzero
level-`j` coefficients live on cells contained in `Ωᵣ`, and the mixed
coefficient cost over the whole family is controlled by the bounded Besov
gauge of `g`.  The input function is assumed bounded, matching the paper's
hypothesis `g ∈ B^s_{p,q} ∩ L∞`; the formal bound below uses
`|g|_{B^s_{p,q}} + |g|∞`.
-/
theorem regularFamily_restriction_representations
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c) :
    ∃ Crel : ℝ,
      0 ≤ Crel ∧
      ∀ (g : α → ℂ)
        (M : ℝ)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        ∃ y : ℕ → WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          ∃ R : (i : ℕ) →
              WeakGridSpace.LpGridRepresentation
                (souzaAtomFamily G s p hs hp hp_top)
                ((y i : WeakGridSpace.BesovishSpace
                    (souzaAtomFamily G s p hs hp hp_top) q) :
                  Lp ℂ p G.toWeakGridSpace.measure),
            (∀ i ∈ Λ,
              WeakGridSpace.RepresentsFunction
                (G := G.toWeakGridSpace) (p := p)
                (fun z => g z * (Ω i).indicator (fun _ => (1 : ℂ)) z)
                (y i : Lp ℂ p G.toWeakGridSpace.measure)) ∧
            (∀ i ∈ Λ,
              WeakGridSpace.LpGridRepresentation.FinitePQCost
                (q := q) (R i)) ∧
            (∀ i ∈ Λ, ∀ j
              (Q : WeakGridSpace.LevelCell G.toWeakGridSpace j),
                ((R i).block j).coeff Q ≠ 0 → Q.1 ⊆ Ω i) ∧
            regularFamilyRestrictionCost G s p q Λ y R ≤
              Crel *
                (WeakGridSpace.BesovishSpace.Norm_Costpq
                    (souzaAtomFamily G s p hs hp hp_top) q xg + M) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  obtain ⟨Cfou, hCfou0, hCfou⟩ :=
    exists_weighted_fouRepresentation G s p q hs hp hp_top
  let Krel : ℝ :=
    ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
      (regularFamilyGeomRootCost G Λ Ω s C c p q + Cfou)
  refine ⟨Krel, ?_, ?_⟩
  · exact mul_nonneg
      (Real.rpow_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) _)
      (add_nonneg
        (regularFamilyGeomRootCost_nonneg
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) (q := q) hΩ)
        hCfou0)
  intro g M xg hgrepr hgbdd
  have hM0 : 0 ≤ M := regularFamilyRestriction_bound_nonneg G hgbdd
  obtain ⟨Rg, hRgfin, hRgcost, htower_g, _hstrict_g⟩ :=
    hCfou g M xg hgrepr hgbdd
  let zeroBesov : WeakGridSpace.BesovishSpace A q :=
    ⟨0, WeakGridSpace.memBesovishCoeffCost_zero (A := A) (q := q)⟩
  let indExists := fun i (hi : i ∈ Λ) =>
    regularFamilyIndicator_besov_representation
      G Λ Ω s C c p q hs hs_lt_inv hp hp_top hΩ hi
  let activeIndY := fun i (hi : i ∈ Λ) =>
    Classical.choose (indExists i hi)
  let activeIndR := fun i (hi : i ∈ Λ) =>
    Classical.choose (Classical.choose_spec (indExists i hi))
  let indPkg :
      (i : ℕ) →
        Σ yind : WeakGridSpace.BesovishSpace A q,
          WeakGridSpace.LpGridRepresentation A
            (yind : Lp ℂ p G.toWeakGridSpace.measure) := fun i =>
    if hi : i ∈ Λ then
      ⟨activeIndY i hi, activeIndR i hi⟩
    else
      ⟨zeroBesov,
        regularFamilyInactiveIndicatorRepresentation
          (hs := hs) (hp := hp) (hp_top := hp_top)
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) hΩ i hi⟩
  let yind : ℕ → WeakGridSpace.BesovishSpace A q := fun i => (indPkg i).1
  let Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation A
      (yind i : Lp ℂ p G.toWeakGridSpace.measure) := fun i => (indPkg i).2
  have hind_active :
      ∀ i (hi : i ∈ Λ),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          ((Ω i).indicator fun _ => (1 : ℂ))
          (yind i : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (Rind i) ∧
        ∀ k, (Rind i).block k =
          regularFamilyIndicatorBlock
            (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k := by
    intro i hi
    have hspec := Classical.choose_spec (Classical.choose_spec (indExists i hi))
    dsimp [yind, Rind, indPkg]
    rw [dif_pos hi]
    simpa [indExists, activeIndY, activeIndR] using hspec
  have hblock_all : ∀ i k,
      (Rind i).block k =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k := by
    intro i k
    by_cases hi : i ∈ Λ
    · exact (hind_active i hi).2.2 k
    · dsimp [Rind, yind, indPkg]
      rw [dif_neg hi]
      rfl
  let prodStrict :
      ∀ i, i ∈ Λ →
        ∀ (j : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace j),
          ‖strictWeightedAncestorCoeffSum G (Rind i) J‖ ≤ 1 := fun i hi j J =>
    regularFamilyIndicator_strictWeightedAncestorCoeffSum_norm_le_one
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ hi (Rind i) (fun m => hblock_all i m) J
  let prodExists := fun i (hi : i ∈ Λ) =>
    exists_quasi_product_of_tower_representations
      G s p q hs hp hp_top
      ((Ω i).indicator fun _ => (1 : ℂ)) g 1 M
      (by norm_num : (0 : ℝ) ≤ 1) hM0
      (yind i) xg (Rind i) Rg
      (hind_active i hi).1 hgrepr
      (hind_active i hi).2.1 hRgfin
      htower_g (prodStrict i hi)
  let activeProdY := fun i (hi : i ∈ Λ) =>
    Classical.choose (prodExists i hi)
  let activeProdR := fun i (hi : i ∈ Λ) =>
    Classical.choose (Classical.choose_spec (prodExists i hi))
  let prodPkg :
      (i : ℕ) →
        Σ yprod : WeakGridSpace.BesovishSpace A q,
          WeakGridSpace.LpGridRepresentation A
            (yprod : Lp ℂ p G.toWeakGridSpace.measure) := fun i =>
    if hi : i ∈ Λ then
      ⟨activeProdY i hi, activeProdR i hi⟩
    else
      ⟨xg, Rg⟩
  let y : ℕ → WeakGridSpace.BesovishSpace A q := fun i => (prodPkg i).1
  let R : (i : ℕ) → WeakGridSpace.LpGridRepresentation A
      (y i : Lp ℂ p G.toWeakGridSpace.measure) := fun i => (prodPkg i).2
  have hprod_active :
      ∀ i (hi : i ∈ Λ),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ((Ω i).indicator (fun _ => (1 : ℂ)) z) * g z)
          (y i : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i) ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R i) ≤
          M * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (Rind i) +
            1 * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg ∧
        (∀ k, (R i).block k =
          WeakGridSpace.LevelBlock.add A
            (quasiU1Block G s p hs hp hp_top (Rind i) Rg k)
            (quasiU2Block G s p hs hp hp_top (Rind i) Rg k)) := by
    intro i hi
    have hspec := Classical.choose_spec (Classical.choose_spec (prodExists i hi))
    dsimp [y, R, prodPkg]
    rw [dif_pos hi]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [prodExists, activeProdY, activeProdR] using hspec.1
    · simpa [prodExists, activeProdY, activeProdR] using hspec.2.1
    · simpa [prodExists, activeProdY, activeProdR, one_mul] using hspec.2.2.1
    · simpa [prodExists, activeProdY, activeProdR, A] using hspec.2.2.2.1
  refine ⟨y, R, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hrep := (hprod_active i hi).1
    filter_upwards [hrep] with z hz
    rw [hz]
    ring
  · intro i hi
    exact (hprod_active i hi).2.1
  · intro i hi j Q hcoeff
    have hblock := (hprod_active i hi).2.2.2 j
    rw [hblock] at hcoeff
    exact regularFamily_productBlock_coeff_ne_zero_subset_domain
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hΩ hi (Rind i) Rg (fun m => hblock_all i m) Q hcoeff
  · have hlevel : ∀ j,
        regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j ≤
          (2 : ℝ) ^ (p.toReal - 1) *
            (M ^ p.toReal * regularFamilyGeomLevel G Λ Ω s C c p j +
              Rg.levelCoeffPower j) := by
      intro j
      have hcongr :
          regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j =
            ∑' i : ℕ,
              Set.indicator Λ
                (fun i =>
                  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
                    ‖(WeakGridSpace.LevelBlock.add A
                      (quasiU1Block G s p hs hp hp_top (Rind i) Rg j)
                      (quasiU2Block G s p hs hp hp_top (Rind i) Rg j)).coeff Q‖ ^
                      p.toReal) i := by
        unfold regularFamilyRestrictionLevelCoeffPower
        apply tsum_congr
        intro i
        by_cases hi : i ∈ Λ
        · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
          apply Finset.sum_congr rfl
          intro Q _
          rw [(hprod_active i hi).2.2.2 j]
        · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi]
      rw [hcongr]
      exact regularFamilyIndicator_quasiProductBlock_aggregate_levelCoeffPower_le
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) hΩ Rind Rg hblock_all hM0 htower_g j
    calc
      regularFamilyRestrictionCost G s p q Λ y R
          ≤ ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
              (M * regularFamilyGeomRootCost G Λ Ω s C c p q +
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg) :=
        regularFamilyRestrictionCost_le_of_level_bound
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) (q := q) hΩ hp_top Rg hRgfin hM0 y R hlevel
      _ ≤ Krel *
            (WeakGridSpace.BesovishSpace.Norm_Costpq A q xg + M) := by
        have hNx0 : 0 ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A q xg :=
          WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg
            (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A q) xg
        have hG0 : 0 ≤ regularFamilyGeomRootCost G Λ Ω s C c p q :=
          regularFamilyGeomRootCost_nonneg
            (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
            (p := p) (q := q) hΩ
        have hKroot0 :
            0 ≤ ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) :=
          Real.rpow_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) _
        have hinner :
            M * regularFamilyGeomRootCost G Λ Ω s C c p q +
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg ≤
            (regularFamilyGeomRootCost G Λ Ω s C c p q + Cfou) *
              (WeakGridSpace.BesovishSpace.Norm_Costpq A q xg + M) := by
          calc
            M * regularFamilyGeomRootCost G Λ Ω s C c p q +
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg
                ≤ M * regularFamilyGeomRootCost G Λ Ω s C c p q +
                    Cfou * WeakGridSpace.BesovishSpace.Norm_Costpq A q xg :=
              add_le_add_right hRgcost _
            _ ≤ (regularFamilyGeomRootCost G Λ Ω s C c p q + Cfou) *
                  (WeakGridSpace.BesovishSpace.Norm_Costpq A q xg + M) := by
              nlinarith [hM0, hG0, hCfou0, hNx0]
        dsimp [Krel]
        calc
          ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
              (M * regularFamilyGeomRootCost G Λ Ω s C c p q +
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg)
              ≤ ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
                ((regularFamilyGeomRootCost G Λ Ω s C c p q + Cfou) *
                  (WeakGridSpace.BesovishSpace.Norm_Costpq A q xg + M)) :=
            mul_le_mul_of_nonneg_left hinner hKroot0
          _ = ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
                (regularFamilyGeomRootCost G Λ Ω s C c p q + Cfou) *
              (WeakGridSpace.BesovishSpace.Norm_Costpq A q xg + M) := by
            ring

end

end GoodGridSpace
