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
`g · 1_{Ωᵣ}` plus the indicator/multiplier bounds.  Their proofs are left as
focused `sorry`s because they reuse the long `u₁ + u₂` product construction
from `QuasiAlgebra` together with new localization bookkeeping.
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
  /-- The level-cost series over the active countable family is summable. -/
  cost_summable :
    ∀ k,
      Summable
        (fun i : ℕ =>
          Set.indicator Λ
            (fun i => ∑ Q ∈ family i k, (G.grid.μ Q).toReal ^ a) i)
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
      pairwise_disjoint := ?_
      family := F
      family_subset := ?_
      family_empty_before := ?_
      family_empty_of_not_mem := ?_
      cover := ?_
      pairwise_disjoint_cells := ?_
      cost_summable := ?_
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
    rw [hterm]
    refine summable_of_hasFiniteSupport ?_
    have hsubset :
        Function.support
            (Function.update (fun _ : ℕ => (0 : ℝ)) 0
              (∑ Q ∈ hΩ.family k, (G.grid.μ Q).toReal ^ a)) ⊆
          ({0} : Set ℕ) := by
      intro i hi
      by_cases hi0 : i = 0
      · simp [hi0]
      · simp [Function.support, Function.update, hi0] at hi
    exact Set.Finite.subset (Set.finite_singleton 0) hsubset
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
    (hsβ : s < β) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
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
  refine ⟨max 0 K, le_max_left 0 K, ?_⟩
  refine ⟨
    { measurable := hΩ.1
      contains_cell := hΩcell
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
    -- Remaining quantitative core of the LaTeX proof: convert the strong
    -- `1 - βp` cost on each `Q ∩ Ω` into a `1 - sp` cost for the combined
    -- level family, using the `λ₂` measure decay between levels and then
    -- absorb the finite `k₀(Ω)`-level comparison constants into `C'`.
    sorry

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

end RestrictionCost

/--
The representation estimate `(pdd)`/`(hiip1)` for a regular family.

Each restriction `g · 1_{Ωᵣ}` receives a Souza representation whose nonzero
level-`j` coefficients live on cells contained in `Ωᵣ`, and the mixed
coefficient cost over the whole family is controlled by the Besov cost of
`g`.
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
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
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
                WeakGridSpace.BesovishSpace.Norm_Costpq
                  (souzaAtomFamily G s p hs hp hp_top) q xg := by
  sorry

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
    (hΩ : RegularDomain G Ω (1 - p.toReal * s) C c)
    (hgeom : c ^ (q.toReal / p.toReal) < 1) :
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
  sorry

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
  sorry

end

end GoodGridSpace
