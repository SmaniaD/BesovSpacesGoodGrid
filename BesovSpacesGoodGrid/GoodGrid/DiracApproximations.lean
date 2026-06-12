import BesovSpacesGoodGrid.GoodGrid.AlternativeRepresentationsAndNorms.standardRepresentation
import BesovSpacesGoodGrid.GoodGrid.PositiveCone

/-!
# Dirac approximations

This file implements the manuscript section *Dirac's approximations*.

For a point `x₀` and a level `k₀`, the manuscript enumerates the finite family
`𝒮_{x₀}^{k₀}` of Haar branches living above `x₀` at levels `k < k₀` and builds a
telescoping sum `∑ ψ_i = 1_{Q_{k₀}} / |Q_{k₀}|`, where `Q_{k₀}` is the cell of
`𝒫^{k₀}` containing `x₀` (equation `(part)`).  Integrating against `f` term by
term and comparing with the pointwise evaluation of the partial Haar sums
`f_{k₀}` yields

`f_{k₀}(x₀) = ∫ f · 1_{Q_{k₀}} / |Q_{k₀}| dm`,

from which Proposition *Dirac's Approximations* (`boup`) follows.

## Implementation notes

The enumerated family `𝒮_{x₀}^{k₀}` and the telescoping identity `(part)` are
already available in the dependency `UnbalancedHaarWavelet` in filtered-sum
form: `Normalized_indicator_in_Haar_Wavelets_span` states exactly

`1_Q/|Q| = 1_I/|I| + sumDown_normed_indicator`,

where `sumDown_normed_indicator` is the double sum over levels `k < k₀` and
branches whose support contains `Q` — the same family `𝒮_{x₀}^{k₀}`, indexed by
filters instead of an enumeration.  We therefore work with the filtered form
throughout and never need the explicit enumeration `S^1, …, S^N`.

## Plan

1. `diracKernel`: the normalized indicator `1_Q/|Q|`, and the transported
   identity `(part)` (`diracKernel_eq_alpha_add_sumDown`).
2. `partialHaarSum`: the partial sums `f_{k₀}` of the Haar series (equation
   `(k0)`), and `partialStandardSum`, the corresponding partial sums
   `∑_{k ≤ k₀} ∑_P k_P a_P` of the standard atomic representation; they agree
   pointwise (`partialHaarSum_eq_partialStandardSum`), by the block identities
   from `standardRepresentation`.
3. The term-by-term comparison (equation `(igual)`): for a branch whose
   support contains `x₀`, the chain coefficient of the unnormalized wavelet
   times its integral against `f` equals `d_S φ_S(x₀)`
   (`integral_chainTerm_eq_coeff_mul_normalizedFunction`).
4. The main evaluation theorem (`partialHaarSum_eq_integral_diracKernel`):
   `f_{k₀}(x₀) = ∫ f · 1_{Q_{k₀}}/|Q_{k₀}| dm` for `x₀ ∈ Q_{k₀} ∈ 𝒫^{k₀}`.
5. Proposition `boup`:
   * A. `|f_{k₀}(x₀)| ≤ esssup |f 1_{Q_{k₀}}|`
     for the representation `(sumf)` (`claimA_standard`) and for nonnegative
     representations (`claimA_positive`);
   * B. the ancestor-sum form
     `∑_{J ⊇ Q} k_J ã_J(x₀) = ∫ f · 1_Q/|Q| dm` (`claimB`): immediate from
     steps 2 and 4, with the per-level collapse to the unique ancestor pair
     given by `standardLevelSum_eq_ancestor_term`.
-/

open scoped ENNReal BigOperators
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace DiracApproximation

/-!
## Step 1: the Dirac kernel `1_Q/|Q|` and the telescoping identity `(part)`
-/

/--
The Dirac kernel attached to a good-grid cell: the normalized indicator
`1_Q / |Q|`.  This is the manuscript's approximate identity at scale
`Q.level`.
-/
def diracKernel (G : GoodGridSpace (α := α)) (Q : GoodGridCell G) : α → ℝ :=
  fun x => Set.indicator Q.cell (fun _ => 1 / (G.grid.μ Q.cell).toReal) x

/-- Every point lies in some cell of the partition at any prescribed level. -/
theorem exists_goodGridCell_mem (G : GoodGridSpace (α := α)) (x₀ : α) (k₀ : ℕ) :
    ∃ Q : GoodGridCell G, Q.level = k₀ ∧ x₀ ∈ Q.cell := by
  have hx : x₀ ∈ ⋃ s ∈ G.grid.grid.partitions k₀, s := by
    rw [G.grid.grid.covering k₀]
    exact Set.mem_univ x₀
  rcases Set.mem_iUnion₂.1 hx with ⟨s, hs, hxs⟩
  exact ⟨⟨k₀, s, hs⟩, rfl, hxs⟩

/-- Two cells of the same level sharing a point coincide. -/
theorem cell_eq_of_mem_of_mem (G : GoodGridSpace (α := α)) {k : ℕ} {s t : Set α}
    (hs : s ∈ G.grid.grid.partitions k) (ht : t ∈ G.grid.grid.partitions k)
    {x : α} (hxs : x ∈ s) (hxt : x ∈ t) : s = t := by
  by_contra hne
  exact Set.disjoint_left.1 (G.grid.grid.disjoint k s t hs ht hne) hxs hxt

/--
The manuscript identity `(part)` in unnormalized-wavelet form:

`1_Q/|Q| = 1_I/|I| + ∑_{k < Q.level} ∑_{c ∈ 𝒫^k, Q ⊆ c} ∑_{S ∈ ℋ(c), Q ⊆ supp S} c_S ψ_S`.

This is a direct transport of
`UnbalancedHaarWavelet.Normalized_indicator_in_Haar_Wavelets_span`.
-/
theorem diracKernel_eq_alpha_add_sumDown (G : GoodGridSpace (α := α))
    [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G) :
    diracKernel G Q =
      fun x =>
        UnbalancedHaarWavelet.normalizedAlphaFunction (HaarRepresentation.GridOf G) x +
          UnbalancedHaarWavelet.sumDown_normed_indicator (HaarRepresentation.GridOf G)
            F.toHaarSystem Q.cell Q.level Q.mem x :=
  UnbalancedHaarWavelet.Normalized_indicator_in_Haar_Wavelets_span
    (HaarRepresentation.GridOf G) F.toHaarSystem Q.cell Q.level Q.mem

/-!
## Step 2: partial sums of the Haar series and of the standard representation
-/

/--
The partial Haar sum `f_{k₀}` from equation `(k0)`:

`f_{k₀} = d_I φ_I + ∑_{k < k₀} ∑_{Q ∈ 𝒫^k} ∑_{S ∈ ℋ(Q)} d_S φ_S`.
-/
def partialHaarSum (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k₀ : ℕ) (x : α) : ℂ :=
  HaarRepresentation.Coeff G F f hf .alpha *
      HaarRepresentation.normalizedFunction G F .alpha x +
    ∑ k ∈ Finset.range k₀, ∑ Q ∈ (G.grid.grid.partitions k).attach,
      StandardAtomicRepresentation.haarCellBlockFunction G F f hf ⟨k, Q.1, Q.2⟩ x

/--
The partial sum `∑_{k ≤ k₀} ∑_{P ∈ 𝒫^k} k_P a_P` of the standard atomic
representation, with the same father term as the Haar partial sum and the
tilde blocks from `standardRepresentation` at the wavelet levels.
-/
def partialStandardSum (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k₀ : ℕ) (x : α) : ℂ :=
  HaarRepresentation.Coeff G F f hf .alpha *
      HaarRepresentation.normalizedFunction G F .alpha x +
    ∑ k ∈ Finset.range k₀, ∑ Q ∈ (G.grid.grid.partitions k).attach,
      StandardAtomicRepresentation.standardCellBlockFunction G F p s f hf ⟨k, Q.1, Q.2⟩ x

/--
The two partial sums agree pointwise: this is the manuscript's remark that
`f_{k₀} = ∑_{k ≤ k₀} ∑_{P ∈ 𝒫^k} k_P a_P`, and it follows block by block from
`haarBlock_eq_sum_tildeCoeff_tildeAtom_pointwise`.
-/
theorem partialHaarSum_eq_partialStandardSum (G : GoodGridSpace (α := α))
    [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (k₀ : ℕ) (x : α) :
    partialHaarSum G F f hf k₀ x = partialStandardSum G F p s f hf k₀ x := by
  unfold partialHaarSum partialStandardSum
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun Q _ => ?_
  exact StandardAtomicRepresentation.haarBlock_eq_sum_tildeCoeff_tildeAtom_pointwise
    G F p s f hf ⟨k, Q.1, Q.2⟩ x

/-!
## Step 3: term-by-term comparison (equation `(igual)`)

For a branch `S` of the tree over a cell `c` whose support contains the point
`x₀`, the chain coefficient of the *unnormalized* wavelet `ψ_S` appearing in
`sumDownSubTree_normed_indicator`, multiplied by `∫ f ψ_S`, equals
`d_S φ_S(x₀)`.  This is the manuscript computation `(igual)`: both sides equal
`± d_S √(|S_{3-a}| / |S_a|) / √(|S₁| + |S₂|)`.
-/

/-- The cells carried by a branch of the tree over `Q` are children of `Q`;
in particular the branch support is contained in `Q`. -/
theorem branchSupport_branchCells_subset (G : GoodGridSpace (α := α))
    [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    UnbalancedHaarWavelet.branchSupport
        (StandardAtomicRepresentation.branchCells (G := G) (F := F) (Q := Q) b) ⊆
      Q.cell := by
  classical
  intro y hy
  rcases Set.mem_iUnion₂.1 hy with ⟨s, hs, hys⟩
  have hs' : s ∈ b.1.1 ∪ b.1.2 := by
    simpa [StandardAtomicRepresentation.branchCells] using hs
  have hchilds :=
    (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).TreeStructureChilds b.1 b.2
  have hs_child : s ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell := by
    rcases Finset.mem_union.1 hs' with h1 | h2
    · exact (F.toHaarSystem.binaryRefinement.childs_are_children
        Q.level Q.cell Q.mem s).1 (hchilds.1 h1)
    · exact (F.toHaarSystem.binaryRefinement.childs_are_children
        Q.level Q.cell Q.mem s).1 (hchilds.2 h2)
  exact hs_child.2 hys

/-- The Haar cell block vanishes at points outside the cell. -/
theorem haarCellBlockFunction_eq_zero_of_not_mem (G : GoodGridSpace (α := α))
    [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (f : α → ℂ) (hf : Integrable f G.grid.μ) (Q : GoodGridCell G)
    {x : α} (hx : x ∉ Q.cell) :
    StandardAtomicRepresentation.haarCellBlockFunction G F f hf Q x = 0 := by
  classical
  unfold StandardAtomicRepresentation.haarCellBlockFunction
  refine Finset.sum_eq_zero fun b _ => ?_
  have hzero :
      HaarRepresentation.normalizedFunction G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x = 0 := by
    refine StandardAtomicRepresentation.normalizedFunction_eq_zero_of_not_mem_branchCells
      G F Q b ?_
    exact fun hmem => hx (branchSupport_branchCells_subset G F Q b hmem)
  rw [hzero, mul_zero]

/-- The product of an integrable function with a complexified Haar wavelet is
integrable, since the wavelet is a combination of two scaled indicators. -/
theorem integrable_mul_haarWavelet (G : GoodGridSpace (α := α))
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    Integrable (fun x => f x *
      ((UnbalancedHaarWavelet.haarWavelet G.grid.μ A B x : ℝ) : ℂ)) G.grid.μ := by
  have hrw : (fun x => f x *
      ((UnbalancedHaarWavelet.haarWavelet G.grid.μ A B x : ℝ) : ℂ)) =
      fun x => ((1 / (G.grid.μ A).toReal : ℝ) : ℂ) * Set.indicator A f x -
        ((1 / (G.grid.μ B).toReal : ℝ) : ℂ) * Set.indicator B f x := by
    funext x
    by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
      simp [UnbalancedHaarWavelet.haarWavelet, Set.indicator_apply, hxA, hxB] <;>
      push_cast <;> ring
  rw [hrw]
  exact ((hf.indicator hA).const_mul _).sub ((hf.indicator hB).const_mul _)

/-- Every cell carried by a branch of the tree over `Q` is a child of `Q`. -/
theorem mem_children_of_mem_combinatorialSupport (G : GoodGridSpace (α := α))
    [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    {r : Finset (Set α) × Finset (Set α)}
    (hr : r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches)
    {t : Set α} (ht : t ∈ Combinatorial_Support r) :
    t ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell := by
  classical
  have hchilds :=
    (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).TreeStructureChilds r hr
  rcases Finset.mem_union.1 (by simpa [Combinatorial_Support] using ht) with h1 | h2
  · exact (F.toHaarSystem.binaryRefinement.childs_are_children
      Q.level Q.cell Q.mem t).1 (hchilds.1 h1)
  · exact (F.toHaarSystem.binaryRefinement.childs_are_children
      Q.level Q.cell Q.mem t).1 (hchilds.2 h2)

/--
Laminarity: if one point of the child cell `P` lies in the support of a branch
of the tree over `Q`, then the whole cell `P` is contained in that support.
-/
theorem child_subset_branchSupport_of_mem_point (G : GoodGridSpace (α := α))
    [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (Q : GoodGridCell G)
    {r : Finset (Set α) × Finset (Set α)}
    (hr : r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches)
    {P : Set α} (hP : P ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell)
    {x₀ : α} (hx₀ : x₀ ∈ P)
    (hx₀' : x₀ ∈ UnbalancedHaarWavelet.branchSupport (Combinatorial_Support r)) :
    P ⊆ UnbalancedHaarWavelet.branchSupport (Combinatorial_Support r) := by
  classical
  rcases Set.mem_iUnion₂.1 hx₀' with ⟨s, hs, hxs⟩
  have hs' : s ∈ Combinatorial_Support r := by simpa using hs
  have hs_child := mem_children_of_mem_combinatorialSupport G F Q hr hs'
  have hsP : s = P :=
    cell_eq_of_mem_of_mem G hs_child.1 hP.1 hxs hx₀
  rw [← hsP]
  exact UnbalancedHaarWavelet.subset_branchSupport_of_mem hs'

/--
Equation `(igual)`, term by term: for a branch `S` of the tree over `Q` whose
support contains the child cell `P ∋ x₀`, the chain coefficient of the
unnormalized wavelet `ψ_S`, multiplied by `∫ f ψ_S`, equals `d_S φ_S(x₀)`.

Both sides equal `± d_S √(|S_{3-a}| / |S_a|) / √(|S₁| + |S₂|)`: this is the
manuscript computation `(igual)`.
-/
theorem chainCoeff_mul_integral_eq_coeff_mul_normalizedFunction
    [∀ (s t : Set α), Decidable (s ⊆ t)]
    (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches})
    {P : Set α}
    (hP : P ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell)
    (hbP : P ∈ Combinatorial_Support b.1)
    {x₀ : α} (hx₀ : x₀ ∈ P) :
    (((if P ⊆ UnbalancedHaarWavelet.branchSupport b.1.1 then
        (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal /
          (G.grid.μ (UnbalancedHaarWavelet.branchSupport
            (Combinatorial_Support b.1))).toReal
      else
        -((G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal /
          (G.grid.μ (UnbalancedHaarWavelet.branchSupport
            (Combinatorial_Support b.1))).toReal)) : ℝ) : ℂ) *
      ∫ x, f x * ((UnbalancedHaarWavelet.haarWavelet G.grid.μ
          (UnbalancedHaarWavelet.branchSupport b.1.1)
          (UnbalancedHaarWavelet.branchSupport b.1.2) x : ℝ) : ℂ) ∂G.grid.μ =
    HaarRepresentation.Coeff G F f hf
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
      HaarRepresentation.normalizedFunction G F
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x₀ := by
  classical
  have hμA : 0 < (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal :=
    StandardAtomicRepresentation.branchSupport_toReal_pos_left G F Q b
  have hμB : 0 < (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal :=
    StandardAtomicRepresentation.branchSupport_toReal_pos_right G F Q b
  have hdisj :
      Disjoint (UnbalancedHaarWavelet.branchSupport b.1.1)
        (UnbalancedHaarWavelet.branchSupport b.1.2) :=
    F.toHaarSystem.branchSupport_components_disjoint (HaarRepresentation.GridOf G) b
  have hμsum :
      (G.grid.μ (UnbalancedHaarWavelet.branchSupport
        (Combinatorial_Support b.1))).toReal =
      (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal +
        (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal := by
    simpa [Combinatorial_Support] using
      UnbalancedHaarWavelet.branchSupport_union_measure_toReal_eq_add
        (G := HaarRepresentation.GridOf G) (H := F.toHaarSystem)
        (hcell := Q.mem) b.2
  -- identification of the abstract Haar function with the concrete wavelet
  have hfun : ∀ x,
      UnbalancedHaarWavelet.FullHaarSystem.function (HaarRepresentation.GridOf G) F
        (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x =
      UnbalancedHaarWavelet.haarWavelet G.grid.μ
        (UnbalancedHaarWavelet.branchSupport b.1.1)
        (UnbalancedHaarWavelet.branchSupport b.1.2) x := by
    intro x
    simp only [UnbalancedHaarWavelet.FullHaarSystem.function,
      UnbalancedHaarWavelet.HaarSystem.wavelet,
      HaarRepresentation.indexOfCellBranch,
      F.toHaarSystem.haarWavelets_def]
  -- the coefficient against the normalized wavelet factors through `∫ f ψ`
  have hCoeff :
      HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) =
        ((HaarRepresentation.l2NormalizationFactor G F
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) : ℝ) : ℂ) *
          ∫ x, f x * ((UnbalancedHaarWavelet.haarWavelet G.grid.μ
              (UnbalancedHaarWavelet.branchSupport b.1.1)
              (UnbalancedHaarWavelet.branchSupport b.1.2) x : ℝ) : ℂ) ∂G.grid.μ := by
    rw [← MeasureTheory.integral_const_mul]
    unfold HaarRepresentation.Coeff HaarRepresentation.L2normalizedHaar
    congr 1
    funext x
    rw [hfun x]
    ring
  -- the squared normalization factor
  have hN :
      F.indexL2NormSq (HaarRepresentation.GridOf G)
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) =
        1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal +
          1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal := by
    simp [UnbalancedHaarWavelet.FullHaarSystem.indexL2NormSq,
      UnbalancedHaarWavelet.haarWaveletL2NormSq, HaarRepresentation.indexOfCellBranch]
  have hN_pos :
      0 < 1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal +
        1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal :=
    add_pos (one_div_pos.2 hμA) (one_div_pos.2 hμB)
  have hl_sq :
      HaarRepresentation.l2NormalizationFactor G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
        HaarRepresentation.l2NormalizationFactor G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) =
      (1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal +
        1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal)⁻¹ := by
    unfold HaarRepresentation.l2NormalizationFactor
    rw [← mul_inv, Real.mul_self_sqrt (by rw [hN]; exact hN_pos.le), hN]
  have hABne :
      (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal +
        (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal ≠ 0 :=
    (add_pos hμA hμB).ne'
  rcases Finset.mem_union.1 (by simpa [Combinatorial_Support] using hbP) with h1 | h2
  · -- `P` lies on the left side of the branch
    have hPA : P ⊆ UnbalancedHaarWavelet.branchSupport b.1.1 :=
      UnbalancedHaarWavelet.subset_branchSupport_of_mem h1
    have hval :=
      StandardAtomicRepresentation.normalizedFunction_eq_left_of_mem
        G F Q ⟨P, hP.1⟩ b h1 hx₀
    rw [if_pos hPA, hCoeff, hval, hμsum]
    have hreal :
        (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal /
          ((G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal +
            (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal) =
        (HaarRepresentation.l2NormalizationFactor G F
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
          HaarRepresentation.l2NormalizationFactor G F
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))) *
          (1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal) := by
      rw [hl_sq]
      field_simp
      ring
    rw [hreal]
    push_cast
    ring
  · -- `P` lies on the right side of the branch
    have hxB : x₀ ∈ UnbalancedHaarWavelet.branchSupport b.1.2 :=
      UnbalancedHaarWavelet.subset_branchSupport_of_mem h2 hx₀
    have hPA : ¬ P ⊆ UnbalancedHaarWavelet.branchSupport b.1.1 :=
      fun hPA => Set.disjoint_left.1 hdisj (hPA hx₀) hxB
    have hval :=
      StandardAtomicRepresentation.normalizedFunction_eq_right_of_mem
        G F Q ⟨P, hP.1⟩ b h2 hx₀
    rw [if_neg hPA, hCoeff, hval, hμsum]
    have hreal :
        (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal /
          ((G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal +
            (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal) =
        (HaarRepresentation.l2NormalizationFactor G F
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
          HaarRepresentation.l2NormalizationFactor G F
            (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b))) *
          (1 / (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal) := by
      rw [hl_sq]
      field_simp
      ring
    rw [hreal]
    push_cast
    ring

/--
Equation `(igual)`, summed: integrating `f` against the one-cell telescoping sum
`sumDownSubTree_normed_indicator` recovers the Haar cell block at any point
`x₀` of the child cell `P`.
-/
theorem integral_mul_sumDownSubTree_eq_haarCellBlock (G : GoodGridSpace (α := α))
    [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G) {P : Set α}
    (hP : P ∈ (HaarRepresentation.GridOf G).children Q.level Q.cell)
    {x₀ : α} (hx₀ : x₀ ∈ P) :
    (∫ x, f x *
        ((UnbalancedHaarWavelet.sumDownSubTree_normed_indicator
          (HaarRepresentation.GridOf G) F.toHaarSystem Q.mem P x : ℝ) : ℂ)
        ∂G.grid.μ) =
      StandardAtomicRepresentation.haarCellBlockFunction G F f hf Q x₀ := by
  classical
  -- pointwise expansion of the integrand as a finite sum
  have hpoint : ∀ x : α,
      f x * ((UnbalancedHaarWavelet.sumDownSubTree_normed_indicator
          (HaarRepresentation.GridOf G) F.toHaarSystem Q.mem P x : ℝ) : ℂ) =
      ∑ B ∈ ((F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches).filter
          (fun B => P ⊆ UnbalancedHaarWavelet.branchSupport (Combinatorial_Support B)),
        ((if P ⊆ UnbalancedHaarWavelet.branchSupport B.1 then
            (G.grid.μ (UnbalancedHaarWavelet.branchSupport B.2)).toReal /
              (G.grid.μ (UnbalancedHaarWavelet.branchSupport
                (Combinatorial_Support B))).toReal
          else
            -((G.grid.μ (UnbalancedHaarWavelet.branchSupport B.1)).toReal /
              (G.grid.μ (UnbalancedHaarWavelet.branchSupport
                (Combinatorial_Support B))).toReal) : ℝ) : ℂ) *
          (f x * ((UnbalancedHaarWavelet.haarWavelet G.grid.μ
            (UnbalancedHaarWavelet.branchSupport B.1)
            (UnbalancedHaarWavelet.branchSupport B.2) x : ℝ) : ℂ)) := by
    intro x
    simp only [UnbalancedHaarWavelet.sumDownSubTree_normed_indicator]
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [Complex.ofReal_mul]
    ring
  rw [show (fun x => f x *
      ((UnbalancedHaarWavelet.sumDownSubTree_normed_indicator
        (HaarRepresentation.GridOf G) F.toHaarSystem Q.mem P x : ℝ) : ℂ)) =
      _ from funext hpoint]
  rw [MeasureTheory.integral_finsetSum _ (fun B hB => by
    have hBmem :
        B ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches :=
      (Finset.mem_filter.1 hB).1
    exact (integrable_mul_haarWavelet G
      (StandardAtomicRepresentation.measurableSet_branchSupport_left G F Q ⟨B, hBmem⟩)
      (StandardAtomicRepresentation.measurableSet_branchSupport_right G F Q ⟨B, hBmem⟩)
      f hf).const_mul _)]
  simp_rw [MeasureTheory.integral_const_mul]
  rw [Finset.sum_filter]
  rw [← Finset.sum_attach
    ((F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches)
    (fun B =>
      if P ⊆ UnbalancedHaarWavelet.branchSupport (Combinatorial_Support B) then
        ((if P ⊆ UnbalancedHaarWavelet.branchSupport B.1 then
            (G.grid.μ (UnbalancedHaarWavelet.branchSupport B.2)).toReal /
              (G.grid.μ (UnbalancedHaarWavelet.branchSupport
                (Combinatorial_Support B))).toReal
          else
            -((G.grid.μ (UnbalancedHaarWavelet.branchSupport B.1)).toReal /
              (G.grid.μ (UnbalancedHaarWavelet.branchSupport
                (Combinatorial_Support B))).toReal) : ℝ) : ℂ) *
          ∫ x, f x * ((UnbalancedHaarWavelet.haarWavelet G.grid.μ
            (UnbalancedHaarWavelet.branchSupport B.1)
            (UnbalancedHaarWavelet.branchSupport B.2) x : ℝ) : ℂ) ∂G.grid.μ
      else 0)]
  have hterm : ∀ b ∈
      ((F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches).attach,
      (if P ⊆ UnbalancedHaarWavelet.branchSupport (Combinatorial_Support b.1) then
        ((if P ⊆ UnbalancedHaarWavelet.branchSupport b.1.1 then
            (G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.2)).toReal /
              (G.grid.μ (UnbalancedHaarWavelet.branchSupport
                (Combinatorial_Support b.1))).toReal
          else
            -((G.grid.μ (UnbalancedHaarWavelet.branchSupport b.1.1)).toReal /
              (G.grid.μ (UnbalancedHaarWavelet.branchSupport
                (Combinatorial_Support b.1))).toReal) : ℝ) : ℂ) *
          ∫ x, f x * ((UnbalancedHaarWavelet.haarWavelet G.grid.μ
            (UnbalancedHaarWavelet.branchSupport b.1.1)
            (UnbalancedHaarWavelet.branchSupport b.1.2) x : ℝ) : ℂ) ∂G.grid.μ
      else 0) =
      HaarRepresentation.Coeff G F f hf
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) *
        HaarRepresentation.normalizedFunction G F
          (.wavelet (HaarRepresentation.indexOfCellBranch G F Q b)) x₀ := by
    intro b _
    by_cases hPb : P ⊆ UnbalancedHaarWavelet.branchSupport (Combinatorial_Support b.1)
    · rw [if_pos hPb]
      have hmem : P ∈ Combinatorial_Support b.1 :=
        (UnbalancedHaarWavelet.child_subset_branchSupport_iff_mem
          (HaarRepresentation.GridOf G) hP
          (fun t ht => mem_children_of_mem_combinatorialSupport G F Q b.2 ht)).1 hPb
      exact chainCoeff_mul_integral_eq_coeff_mul_normalizedFunction
        G F f hf Q b hP hmem hx₀
    · rw [if_neg hPb]
      have hx₀' : x₀ ∉ UnbalancedHaarWavelet.branchSupport
          (StandardAtomicRepresentation.branchCells (G := G) (F := F) (Q := Q) b) := by
        intro hmem
        refine hPb (child_subset_branchSupport_of_mem_point G F Q b.2 hP hx₀ ?_)
        simpa [StandardAtomicRepresentation.branchCells, Combinatorial_Support]
          using hmem
      rw [StandardAtomicRepresentation.normalizedFunction_eq_zero_of_not_mem_branchCells
        G F Q b hx₀', mul_zero]
  rw [Finset.sum_congr rfl hterm]
  rfl

/-!
## Step 4: the evaluation theorem
-/

/-- The product of an integrable function with a complexified Dirac kernel is
integrable. -/
theorem integrable_mul_diracKernel (G : GoodGridSpace (α := α))
    (Q : GoodGridCell G) (f : α → ℂ) (hf : Integrable f G.grid.μ) :
    Integrable (fun x => f x * ((diracKernel G Q x : ℝ) : ℂ)) G.grid.μ := by
  have hQm : MeasurableSet Q.cell := G.grid.grid.measurable Q.level Q.cell Q.mem
  have hrw : (fun x => f x * ((diracKernel G Q x : ℝ) : ℂ)) =
      fun x => ((1 / (G.grid.μ Q.cell).toReal : ℝ) : ℂ) * Set.indicator Q.cell f x := by
    funext x
    by_cases hx : x ∈ Q.cell <;>
      simp [diracKernel, Set.indicator_apply, hx, mul_comm]
  rw [hrw]
  exact (hf.indicator hQm).const_mul _

/--
**Dirac approximation, evaluation form.**  For `f` integrable, `x₀ ∈ Q.cell`
with `Q ∈ 𝒫^{k₀}`:

`f_{k₀}(x₀) = ∫ f · 1_{Q}/|Q| dm`.

The proof is by induction on `Q.level`, using the one-step telescoping
identity `normalized_indicator_child_eq_cell_add_sum_chain_2`, the term-by-term
identity of Step 3, and the vanishing of the off-cell blocks
(`haarCellBlockFunction_eq_zero_of_not_mem`).
-/
theorem partialHaarSum_eq_integral_mul_diracKernel (G : GoodGridSpace (α := α))
    [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G) {x₀ : α} (hx₀ : x₀ ∈ Q.cell) :
    partialHaarSum G F f hf Q.level x₀ =
      ∫ x, f x * ((diracKernel G Q x : ℝ) : ℂ) ∂G.grid.μ := by
  classical
  suffices H : ∀ (k : ℕ) (Q : GoodGridCell G), Q.level = k → ∀ {x₀ : α}, x₀ ∈ Q.cell →
      partialHaarSum G F f hf k x₀ =
        ∫ x, f x * ((diracKernel G Q x : ℝ) : ℂ) ∂G.grid.μ by
    exact H Q.level Q rfl hx₀
  intro k
  induction k with
  | zero =>
    intro Q hQ x₀ hx₀
    -- at level zero the cell is the whole space and only the father term remains
    have hcell : Q.cell = Set.univ := by
      have hmem : Q.cell ∈ G.grid.grid.partitions 0 := hQ ▸ Q.mem
      rw [G.grid.grid.first_partition_eq_univ] at hmem
      simpa using hmem
    have hμU : 0 < (G.grid.μ Set.univ).toReal := by
      rw [← hcell]
      exact ENNReal.toReal_pos Q.measure_pos.ne' Q.measure_ne_top
    -- the father function is the constant `1/μ(univ)`
    have halpha : ∀ x,
        UnbalancedHaarWavelet.FullHaarSystem.function (HaarRepresentation.GridOf G) F
          .alpha x = 1 / (G.grid.μ Set.univ).toReal := by
      intro x
      rw [show UnbalancedHaarWavelet.FullHaarSystem.function (HaarRepresentation.GridOf G)
          F .alpha = F.alphaFunction from rfl, F.alphaFunction_def]
      simp [UnbalancedHaarWavelet.normalizedAlphaFunction]
    have hl : HaarRepresentation.l2NormalizationFactor G F .alpha =
        Real.sqrt (G.grid.μ Set.univ).toReal := by
      unfold HaarRepresentation.l2NormalizationFactor
      rw [show F.indexL2NormSq (HaarRepresentation.GridOf G) .alpha =
        1 / (G.grid.μ Set.univ).toReal from rfl]
      rw [one_div, Real.sqrt_inv, inv_inv]
    have hCoeff : HaarRepresentation.Coeff G F f hf .alpha =
        (∫ x, f x ∂G.grid.μ) *
          ((Real.sqrt (G.grid.μ Set.univ).toReal *
            (1 / (G.grid.μ Set.univ).toReal) : ℝ) : ℂ) := by
      rw [← MeasureTheory.integral_mul_const]
      unfold HaarRepresentation.Coeff HaarRepresentation.L2normalizedHaar
      congr 1
      funext x
      rw [halpha x, hl]
      push_cast
      ring
    have hnf : HaarRepresentation.normalizedFunction G F .alpha x₀ =
        ((Real.sqrt (G.grid.μ Set.univ).toReal *
          (1 / (G.grid.μ Set.univ).toReal) : ℝ) : ℂ) := by
      unfold HaarRepresentation.normalizedFunction
      rw [halpha x₀, hl]
      push_cast
      ring
    have hdk : (fun x => f x * ((diracKernel G Q x : ℝ) : ℂ)) =
        fun x => f x * ((1 / (G.grid.μ Set.univ).toReal : ℝ) : ℂ) := by
      funext x
      simp [diracKernel, hcell]
    simp only [partialHaarSum, Finset.range_zero, Finset.sum_empty, add_zero]
    rw [hCoeff, hnf, hdk, MeasureTheory.integral_mul_const]
    have hc : (Real.sqrt (G.grid.μ Set.univ).toReal *
        (1 / (G.grid.μ Set.univ).toReal)) *
        (Real.sqrt (G.grid.μ Set.univ).toReal *
          (1 / (G.grid.μ Set.univ).toReal)) = 1 / (G.grid.μ Set.univ).toReal := by
      have hss := Real.mul_self_sqrt hμU.le
      field_simp
      linear_combination hss
    calc (∫ x, f x ∂G.grid.μ) *
          ((Real.sqrt (G.grid.μ Set.univ).toReal *
            (1 / (G.grid.μ Set.univ).toReal) : ℝ) : ℂ) *
          ((Real.sqrt (G.grid.μ Set.univ).toReal *
            (1 / (G.grid.μ Set.univ).toReal) : ℝ) : ℂ)
        = (∫ x, f x ∂G.grid.μ) *
            (((Real.sqrt (G.grid.μ Set.univ).toReal *
              (1 / (G.grid.μ Set.univ).toReal)) *
              (Real.sqrt (G.grid.μ Set.univ).toReal *
                (1 / (G.grid.μ Set.univ).toReal)) : ℝ) : ℂ) := by
          push_cast
          ring
      _ = (∫ x, f x ∂G.grid.μ) * ((1 / (G.grid.μ Set.univ).toReal : ℝ) : ℂ) := by
          rw [hc]
  | succ k ih =>
    intro Q hQ x₀ hx₀
    -- the parent cell at level `k`
    obtain ⟨t, ht, hsub⟩ := G.grid.grid.nested k Q.cell (hQ ▸ Q.mem)
    set Qp : GoodGridCell G := ⟨k, t, ht⟩ with hQp
    have hx₀t : x₀ ∈ Qp.cell := hsub hx₀
    have hchild : Q.cell ∈ (HaarRepresentation.GridOf G).children Qp.level Qp.cell :=
      ⟨hQ ▸ Q.mem, hsub⟩
    -- the new level contributes only the block of the parent cell
    have hsum_level : ∑ c ∈ (G.grid.grid.partitions k).attach,
        StandardAtomicRepresentation.haarCellBlockFunction G F f hf ⟨k, c.1, c.2⟩ x₀ =
        StandardAtomicRepresentation.haarCellBlockFunction G F f hf Qp x₀ := by
      refine Finset.sum_eq_single_of_mem
        (⟨t, ht⟩ : {s : Set α // s ∈ G.grid.grid.partitions k})
        (Finset.mem_attach _ _) ?_
      intro c _ hc
      refine haarCellBlockFunction_eq_zero_of_not_mem G F f hf ⟨k, c.1, c.2⟩ ?_
      intro hx₀c
      exact hc (Subtype.ext (cell_eq_of_mem_of_mem G c.2 ht hx₀c hx₀t))
    have hstep : partialHaarSum G F f hf (k + 1) x₀ =
        partialHaarSum G F f hf k x₀ +
          StandardAtomicRepresentation.haarCellBlockFunction G F f hf Qp x₀ := by
      unfold partialHaarSum
      rw [Finset.sum_range_succ, hsum_level]
      ring
    -- the telescoping identity, integrated against `f`
    have hchain := UnbalancedHaarWavelet.normalized_indicator_child_eq_cell_add_sum_chain_2
      (G := HaarRepresentation.GridOf G) (H := F.toHaarSystem)
      (hcell := Qp.mem) hchild
    have hsplit : ∫ x, f x *
        ((UnbalancedHaarWavelet.sumDownSubTree_normed_indicator
          (HaarRepresentation.GridOf G) F.toHaarSystem Qp.mem Q.cell x : ℝ) : ℂ)
        ∂G.grid.μ =
        (∫ x, f x * ((diracKernel G Q x : ℝ) : ℂ) ∂G.grid.μ) -
          ∫ x, f x * ((diracKernel G Qp x : ℝ) : ℂ) ∂G.grid.μ := by
      rw [← MeasureTheory.integral_sub (integrable_mul_diracKernel G Q f hf)
        (integrable_mul_diracKernel G Qp f hf)]
      congr 1
      funext x
      have hsd : UnbalancedHaarWavelet.sumDownSubTree_normed_indicator
          (HaarRepresentation.GridOf G) F.toHaarSystem Qp.mem Q.cell x =
          diracKernel G Q x - diracKernel G Qp x := by
        have hx := congrFun hchain x
        simpa [diracKernel] using hx.symm
      rw [hsd]
      push_cast
      ring
    rw [hstep, ih Qp rfl hx₀t,
      ← integral_mul_sumDownSubTree_eq_haarCellBlock G F f hf Qp hchild hx₀, hsplit]
    ring

/-!
## Step 5: Proposition (Dirac's Approximations)
-/

/--
**Proposition `boup`, part A** (for the representation `(sumf)`):

`|f_{k₀}(x₀)| ≤ esssup |f 1_Q|` whenever `x₀ ∈ Q.cell`.

This follows from the evaluation theorem, since the average of `f` over `Q`
is bounded by the essential supremum of `f` on `Q`.
-/
theorem claimA_standard (G : GoodGridSpace (α := α))
    [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G) {x₀ : α} (hx₀ : x₀ ∈ Q.cell) :
    ENNReal.ofReal ‖partialHaarSum G F f hf Q.level x₀‖ ≤
      eLpNorm (Set.indicator Q.cell f) ∞ G.grid.μ := by
  classical
  have hQm : MeasurableSet Q.cell := G.grid.grid.measurable Q.level Q.cell Q.mem
  have hpos : 0 < (G.grid.μ Q.cell).toReal :=
    ENNReal.toReal_pos Q.measure_pos.ne' Q.measure_ne_top
  -- the average of `f` over `Q` as a constant multiple of `∫ 1_Q f`
  have hrw : (fun x => f x * ((diracKernel G Q x : ℝ) : ℂ)) =
      fun x => ((1 / (G.grid.μ Q.cell).toReal : ℝ) : ℂ) * Set.indicator Q.cell f x := by
    funext x
    by_cases hx : x ∈ Q.cell <;>
      simp [diracKernel, Set.indicator_apply, hx, mul_comm]
  have hc : ‖((1 / (G.grid.μ Q.cell).toReal : ℝ) : ℂ)‖ₑ = (G.grid.μ Q.cell)⁻¹ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), one_div,
      ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_toReal Q.measure_ne_top]
  rw [partialHaarSum_eq_integral_mul_diracKernel G F f hf Q hx₀, hrw,
    MeasureTheory.integral_const_mul, ofReal_norm, enorm_mul, hc]
  calc (G.grid.μ Q.cell)⁻¹ * ‖∫ x, Set.indicator Q.cell f x ∂G.grid.μ‖ₑ
      ≤ (G.grid.μ Q.cell)⁻¹ * ∫⁻ x, ‖Set.indicator Q.cell f x‖ₑ ∂G.grid.μ :=
        mul_le_mul_left' (MeasureTheory.enorm_integral_le_lintegral_enorm _) _
    _ = (G.grid.μ Q.cell)⁻¹ * eLpNorm f 1 (G.grid.μ.restrict Q.cell) := by
        rw [← MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
          MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hQm]
    _ ≤ (G.grid.μ Q.cell)⁻¹ * (eLpNorm f ∞ (G.grid.μ.restrict Q.cell) *
          ((G.grid.μ.restrict Q.cell) Set.univ) ^
            (1 / (1 : ℝ≥0∞).toReal - 1 / (∞ : ℝ≥0∞).toReal)) :=
        mul_le_mul_left'
          (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ le_top
            (hf.1.restrict)) _
    _ = (G.grid.μ Q.cell)⁻¹ * (eLpNorm f ∞ (G.grid.μ.restrict Q.cell) *
          G.grid.μ Q.cell) := by
        rw [MeasureTheory.Measure.restrict_apply_univ]
        norm_num
    _ = eLpNorm f ∞ (G.grid.μ.restrict Q.cell) *
          ((G.grid.μ Q.cell)⁻¹ * G.grid.μ Q.cell) := by
        ring
    _ = eLpNorm f ∞ (G.grid.μ.restrict Q.cell) := by
        rw [ENNReal.inv_mul_cancel Q.measure_pos.ne' Q.measure_ne_top, mul_one]
    _ = eLpNorm (Set.indicator Q.cell f) ∞ G.grid.μ :=
        (MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hQm).symm

/-!
## Step 6: Proposition `boup` part A for nonnegative representations

For a *positive* Souza representation `f = ∑_k ∑_P k_P a_P` — nonnegative real
coefficients and canonical Souza atoms, as in `SouzaPositiveRepresentation` —
the manuscript's part A is "obvious": at (almost) any point `x₀ ∈ Q` the
ancestor sum `∑_{J ⊇ Q} k_J |J|^{s-1/p}` is a partial sum of a series of
nonnegative terms whose limit is `f(x₀)`, so it is bounded by `esssup |f 1_Q|`.

The pointwise control is extracted from the `L^p` convergence of the
representation through an a.e.-convergent subsequence; monotonicity of the
partial sums then upgrades subsequential convergence to the bound for every
partial sum.
-/

/-- Every cell has an ancestor at each coarser level. -/
theorem exists_ancestor (G : GoodGridSpace (α := α)) (Q : GoodGridCell G)
    {k : ℕ} (hk : k ≤ Q.level) :
    ∃ J, J ∈ G.grid.grid.partitions k ∧ Q.cell ⊆ J := by
  have hmem : Q.cell ∈ G.grid.grid.partitions (k + (Q.level - k)) := by
    rw [Nat.add_sub_cancel' hk]
    exact Q.mem
  obtain ⟨t, ht, hsub⟩ := G.grid.grid.nested_iterate k (Q.level - k) Q.cell hmem
  exact ⟨t, ht, hsub⟩

/--
The `k`-th term of the ancestor-coefficient sum of a representation: the
modulus-free coefficient `Re k_J` of the ancestor `J ∈ 𝒫^k` of `Q`, weighted by
`|J|^{s-1/p}`.  When `k > Q.level` no ancestor needs to exist and the term
defaults to `0`.
-/
noncomputable def ancestorTerm (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top) f)
    (Q : GoodGridCell G) (k : ℕ) : ℝ := by
  classical
  exact if h : ∃ J, J ∈ G.grid.grid.partitions k ∧ Q.cell ⊆ J then
    ((R.block k).coeff ⟨h.choose, h.choose_spec.1⟩).re *
      (G.grid.μ h.choose).toReal ^ (s - (p.toReal)⁻¹)
  else 0

/--
The real-valued level block of a positive representation: at each point this is
`k_P |P|^{s-1/p}` for the unique level-`k` cell `P` containing the point.
-/
noncomputable def positiveBlockFun (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top) f)
    (k : ℕ) (x : α) : ℝ :=
  ∑ P ∈ (G.toWeakGridSpace.grid.partitions k).attach,
    ((R.block k).coeff P).re *
      Set.indicator P.1 (fun _ => (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹)) x

/-- For a positive representation, all real coefficients are nonnegative. -/
theorem coeff_re_nonneg (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top) f}
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (k : ℕ) (P : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    0 ≤ ((R.block k).coeff P).re := by
  obtain ⟨c, hc0, hcoeff, -⟩ := hR k P
  rw [hcoeff]
  simpa using hc0

/-- The real level blocks of a positive representation are nonnegative. -/
theorem positiveBlockFun_nonneg (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top) f}
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (k : ℕ) (x : α) :
    0 ≤ positiveBlockFun G s p hs hp hp_top R k x := by
  refine Finset.sum_nonneg fun P _ => mul_nonneg
    (coeff_re_nonneg G s p hs hp hp_top hR k P) ?_
  exact Set.indicator_nonneg (fun y _ => Real.rpow_nonneg ENNReal.toReal_nonneg _) x

/-- Value of the real level block at a point of a given level-`k` cell. -/
theorem positiveBlockFun_apply_of_mem (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top) f)
    {k : ℕ} (J : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {x : α} (hx : x ∈ J.1) :
    positiveBlockFun G s p hs hp hp_top R k x =
      ((R.block k).coeff J).re *
        (G.grid.μ J.1).toReal ^ (s - (p.toReal)⁻¹) := by
  classical
  unfold positiveBlockFun
  rw [Finset.sum_eq_single_of_mem J (Finset.mem_attach _ _) ?_]
  · rw [Set.indicator_of_mem hx]
  · intro P _ hPJ
    have hxP : x ∉ P.1 := by
      intro hxP
      exact hPJ (Subtype.ext (cell_eq_of_mem_of_mem G P.2 J.2 hxP hx))
    rw [Set.indicator_of_notMem hxP, mul_zero]

/--
For `k ≤ Q.level` the ancestor term equals the value of the real level block at
any point of `Q`: the chosen ancestor is exactly the level-`k` cell containing
that point.
-/
theorem ancestorTerm_eq_positiveBlockFun (G : GoodGridSpace (α := α)) (s : ℝ)
    (p : ℝ≥0∞) (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top) f)
    (Q : GoodGridCell G) {k : ℕ} (hk : k ≤ Q.level)
    {x : α} (hx : x ∈ Q.cell) :
    ancestorTerm G s p hs hp hp_top R Q k =
      positiveBlockFun G s p hs hp hp_top R k x := by
  classical
  have hex : ∃ J, J ∈ G.grid.grid.partitions k ∧ Q.cell ⊆ J :=
    exists_ancestor G Q hk
  have hxJ : x ∈ hex.choose := hex.choose_spec.2 hx
  rw [ancestorTerm, dif_pos hex,
    positiveBlockFun_apply_of_mem G s p hs hp hp_top R
      ⟨hex.choose, hex.choose_spec.1⟩ hxJ]

/-- Coercions of finite sums in `Lp` agree almost everywhere with the pointwise
sums of the coercions. -/
private theorem lp_coeFn_finset_sum {ι : Type*}
    {μ : MeasureTheory.Measure α} {q : ℝ≥0∞}
    (t : Finset ι) (g : ι → Lp ℂ q μ) :
    ⇑(∑ i ∈ t, g i) =ᵐ[μ] fun x => ∑ i ∈ t, g i x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [MeasureTheory.Lp.coeFn_zero (E := ℂ) (p := q) (μ := μ)] with x hx
      simpa using hx
  | insert i t hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [MeasureTheory.Lp.coeFn_add (g i) (∑ j ∈ t, g j), ih] with x hx hx2
      rw [hx, Pi.add_apply, hx2, Finset.sum_insert hi]

/--
The `L^p` level block of a positive representation agrees almost everywhere
with the (complexified) real level block.
-/
theorem positiveBlock_coeFn (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    {R : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top) f}
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R) (k : ℕ) :
    ⇑((R.block k).toLp (souzaAtomFamily G s p hs hp hp_top))
      =ᵐ[G.toWeakGridSpace.measure]
      fun x => ((positiveBlockFun G s p hs hp hp_top R k x : ℝ) : ℂ) := by
  classical
  -- a.e. identification of each one-cell term
  have hterm : ∀ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ⇑((R.block k).term (souzaAtomFamily G s p hs hp hp_top) P)
        =ᵐ[G.toWeakGridSpace.measure]
        fun x => ((((R.block k).coeff P).re *
          Set.indicator P.1
            (fun _ => (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹)) x : ℝ) : ℂ) := by
    intro P
    obtain ⟨c, hc0, hcoeff, hatom⟩ := hR k P
    filter_upwards [MeasureTheory.Lp.coeFn_smul ((R.block k).coeff P)
        (MemLp.toLp _ ((souzaAtomFamily G s p hs hp hp_top).local_memLp_p
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k P)
          ((R.block k).atom P))),
      MeasureTheory.MemLp.coeFn_toLp
        ((souzaAtomFamily G s p hs hp hp_top).local_memLp_p
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k P)
          ((R.block k).atom P))] with x hx1 hx2
    rw [WeakGridSpace.LevelBlock.term, hx1, Pi.smul_apply, hx2, hatom, hcoeff]
    by_cases hxP : x ∈ P.1
    · rw [Set.indicator_of_mem hxP]
      have hatomval : canonicalSouzaAtom G s p (goodGridCellOfLevelCell G P) x =
          (((G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ) := by
        simp [canonicalSouzaAtom, goodGridCellOfLevelCell, hxP]
      rw [hatomval, smul_eq_mul, Complex.ofReal_re]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hxP]
      have hatomval : canonicalSouzaAtom G s p (goodGridCellOfLevelCell G P) x = 0 := by
        simp [canonicalSouzaAtom, goodGridCellOfLevelCell, hxP]
      rw [hatomval]
      simp
  -- sum the one-cell identifications over the level
  have hsum := lp_coeFn_finset_sum
    ((G.toWeakGridSpace.grid.partitions k).attach)
    (fun P => (R.block k).term (souzaAtomFamily G s p hs hp hp_top) P)
  have hterms : ∀ᵐ x ∂G.toWeakGridSpace.measure,
      ∀ P : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ((R.block k).term (souzaAtomFamily G s p hs hp hp_top) P) x =
          ((((R.block k).coeff P).re *
            Set.indicator P.1
              (fun _ => (G.grid.μ P.1).toReal ^ (s - (p.toReal)⁻¹)) x : ℝ) : ℂ) :=
    MeasureTheory.ae_all_iff.2 hterm
  filter_upwards [hsum, hterms] with x hx hx2
  rw [WeakGridSpace.LevelBlock.toLp, hx,
    Finset.sum_congr rfl fun P _ => hx2 P]
  rw [positiveBlockFun]
  push_cast
  ring

/-- An `L^p`-convergent series admits a subsequence of partial sums converging
almost everywhere. -/
private theorem exists_ae_tendsto_partialSums {μ : MeasureTheory.Measure α}
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    (g : ℕ → Lp ℂ q μ) (f : Lp ℂ q μ)
    (htends : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, g k)
      Filter.atTop (nhds f)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Filter.Tendsto (fun i => ⇑(∑ k ∈ Finset.range (ns i), g k) x)
        Filter.atTop (nhds (⇑f x)) := by
  set S : ℕ → Lp ℂ q μ := fun n => ∑ k ∈ Finset.range n, g k with hS_def
  have hnorm : Filter.Tendsto (fun n => ‖S n - f‖) Filter.atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp htends
  have heLp : Filter.Tendsto (fun n => eLpNorm (⇑(S n) - ⇑f) q μ)
      Filter.atTop (nhds 0) := by
    have hrw : ∀ n, eLpNorm (⇑(S n) - ⇑f) q μ = ENNReal.ofReal ‖S n - f‖ := by
      intro n
      have h1 : eLpNorm (⇑(S n) - ⇑f) q μ = eLpNorm (⇑(S n - f)) q μ :=
        MeasureTheory.eLpNorm_congr_ae (MeasureTheory.Lp.coeFn_sub (S n) f).symm
      rw [h1, MeasureTheory.Lp.norm_def,
        ENNReal.ofReal_toReal (MeasureTheory.Lp.eLpNorm_ne_top _)]
    simp only [hrw]
    simpa using ENNReal.tendsto_ofReal hnorm
  have hmeas : MeasureTheory.TendstoInMeasure μ (fun n => ⇑(S n))
      Filter.atTop ⇑f :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hq0 hqt
      (fun n => MeasureTheory.Lp.aestronglyMeasurable (S n))
      (MeasureTheory.Lp.aestronglyMeasurable f) heLp
  obtain ⟨ns, hns_mono, hae⟩ := hmeas.exists_seq_tendsto_ae
  exact ⟨ns, hns_mono, hae⟩

/-- Almost-everywhere facts hold at some point of every good-grid cell. -/
theorem exists_mem_cell_of_ae (G : GoodGridSpace (α := α)) (Q : GoodGridCell G)
    {P : α → Prop} (hP : ∀ᵐ x ∂G.toWeakGridSpace.measure, P x) :
    ∃ x ∈ Q.cell, P x := by
  by_contra h
  push_neg at h
  have hsub : Q.cell ⊆ {x | ¬ P x} := fun x hx => h x hx
  rw [MeasureTheory.ae_iff] at hP
  have hle : G.grid.μ Q.cell ≤ G.grid.μ {x | ¬ P x} :=
    MeasureTheory.measure_mono hsub
  rw [show G.grid.μ {x | ¬ P x} = G.toWeakGridSpace.measure {x | ¬ P x} from rfl,
    hP] at hle
  exact absurd (lt_of_lt_of_le Q.measure_pos hle) (by simp)

/--
**Proposition `boup`, part A, nonnegative case.**  For a positive Souza
representation `f = ∑_k ∑_P k_P a_P` (nonnegative coefficients, canonical
atoms) and every cell `Q`:

`∑_{J ⊇ Q} k_J |J|^{s-1/p} ≤ esssup |f 1_Q|`.
-/
theorem claimA_positive (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞) [Fact (1 ≤ p)]
    {f : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top) f)
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    (Q : GoodGridCell G) :
    ENNReal.ofReal (∑ k ∈ Finset.range (Q.level + 1),
        ancestorTerm G s p hs hp hp_top R Q k) ≤
      eLpNorm (Set.indicator Q.cell (⇑f)) ∞ G.toWeakGridSpace.measure := by
  classical
  -- a.e.-convergent subsequence of the partial sums of the representation
  obtain ⟨ns, hns_mono, hae⟩ :=
    exists_ae_tendsto_partialSums (μ := G.toWeakGridSpace.measure)
      (lt_of_lt_of_le zero_lt_one hp).ne' hp_top
      (fun k => (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) f
      R.hasSum.tendsto_sum_nat
  -- a.e. identification of partial sums with the real partial sums
  have hblocks : ∀ᵐ x ∂G.toWeakGridSpace.measure, ∀ k,
      ⇑((R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) x =
        ((positiveBlockFun G s p hs hp hp_top R k x : ℝ) : ℂ) :=
    MeasureTheory.ae_all_iff.2 fun k => positiveBlock_coeFn G s p hs hp hp_top hR k
  have hpartials : ∀ᵐ x ∂G.toWeakGridSpace.measure, ∀ n,
      ⇑(∑ k ∈ Finset.range n,
          (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) x =
        ∑ k ∈ Finset.range n,
          ⇑((R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) x :=
    MeasureTheory.ae_all_iff.2 fun n =>
      lp_coeFn_finset_sum (Finset.range n)
        (fun k => (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top))
  -- the essential-sup bound holds a.e.
  have hess : ∀ᵐ x ∂G.toWeakGridSpace.measure,
      ‖Set.indicator Q.cell (⇑f) x‖ₑ ≤
        eLpNormEssSup (Set.indicator Q.cell (⇑f)) G.toWeakGridSpace.measure :=
    MeasureTheory.ae_le_eLpNormEssSup
  -- pick a witness point in `Q`
  obtain ⟨x₀, hx₀Q, hx₀⟩ :=
    exists_mem_cell_of_ae G Q (hae.and (hblocks.and (hpartials.and hess)))
  obtain ⟨hx₀_lim, hx₀_blocks, hx₀_partials, hx₀_ess⟩ := hx₀
  -- the real partial sums at the witness point
  have hSu : ∀ n, ⇑(∑ k ∈ Finset.range n,
      (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) x₀ =
      ((∑ k ∈ Finset.range n,
        positiveBlockFun G s p hs hp hp_top R k x₀ : ℝ) : ℂ) := by
    intro n
    rw [hx₀_partials n]
    push_cast
    exact Finset.sum_congr rfl fun k _ => hx₀_blocks k
  have hu_mono : Monotone (fun n => ∑ k ∈ Finset.range n,
      positiveBlockFun G s p hs hp hp_top R k x₀) := by
    intro m n hmn
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun k _ _ => positiveBlockFun_nonneg G s p hs hp hp_top hR k x₀)
    intro j hj
    exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj) hmn)
  -- monotone real partial sums with a convergent subsequence are bounded by
  -- the limit of the subsequence
  have hu_le : ∀ n, (∑ k ∈ Finset.range n,
      positiveBlockFun G s p hs hp hp_top R k x₀) ≤ (⇑f x₀).re := by
    have hre_lim : Filter.Tendsto (fun i => ∑ k ∈ Finset.range (ns i),
        positiveBlockFun G s p hs hp hp_top R k x₀) Filter.atTop
        (nhds ((⇑f x₀).re)) := by
      have h1 : Filter.Tendsto (fun i =>
          (⇑(∑ k ∈ Finset.range (ns i),
            (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) x₀).re)
          Filter.atTop (nhds ((⇑f x₀).re)) :=
        (Complex.continuous_re.tendsto _).comp hx₀_lim
      have h2 : (fun i =>
          (⇑(∑ k ∈ Finset.range (ns i),
            (R.block k).toLp (souzaAtomFamily G s p hs hp hp_top)) x₀).re) =
          fun i => ∑ k ∈ Finset.range (ns i),
            positiveBlockFun G s p hs hp hp_top R k x₀ := by
        funext i
        rw [hSu (ns i)]
        simp
      rwa [h2] at h1
    intro n
    have h1 : (∑ k ∈ Finset.range n,
        positiveBlockFun G s p hs hp hp_top R k x₀) ≤
        ∑ k ∈ Finset.range (ns n),
          positiveBlockFun G s p hs hp hp_top R k x₀ :=
      hu_mono hns_mono.le_apply
    have h2 : (∑ k ∈ Finset.range (ns n),
        positiveBlockFun G s p hs hp hp_top R k x₀) ≤ (⇑f x₀).re :=
      Monotone.ge_of_tendsto (hu_mono.comp hns_mono.monotone) hre_lim n
    exact h1.trans h2
  -- the ancestor sum is the real partial sum at level `Q.level + 1`
  have hanc : ∑ k ∈ Finset.range (Q.level + 1),
      ancestorTerm G s p hs hp hp_top R Q k =
      ∑ k ∈ Finset.range (Q.level + 1),
        positiveBlockFun G s p hs hp hp_top R k x₀ := by
    refine Finset.sum_congr rfl fun k hk => ?_
    exact ancestorTerm_eq_positiveBlockFun G s p hs hp hp_top R Q
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hx₀Q
  -- conclude
  rw [hanc]
  calc ENNReal.ofReal (∑ k ∈ Finset.range (Q.level + 1),
        positiveBlockFun G s p hs hp hp_top R k x₀)
      ≤ ENNReal.ofReal ((⇑f x₀).re) :=
        ENNReal.ofReal_le_ofReal (hu_le (Q.level + 1))
    _ ≤ ENNReal.ofReal ‖⇑f x₀‖ :=
        ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)
    _ = ‖Set.indicator Q.cell (⇑f) x₀‖ₑ := by
        rw [ofReal_norm, Set.indicator_of_mem hx₀Q]
    _ ≤ eLpNormEssSup (Set.indicator Q.cell (⇑f)) G.toWeakGridSpace.measure :=
        hx₀_ess
    _ = eLpNorm (Set.indicator Q.cell (⇑f)) ∞ G.toWeakGridSpace.measure :=
        MeasureTheory.eLpNorm_exponent_top.symm

/-!
## Step 7: Proposition `boup` part B

For the standard representation `(sumf)`, part B is immediate from what is
already proved: the standard partial sum agrees pointwise with the Haar
partial sum (`partialHaarSum_eq_partialStandardSum`), and the Haar partial sum
at scale `Q.level` is the conditional expectation on `𝒫^{Q.level}`
(`partialHaarSum_eq_integral_mul_diracKernel`).

The reduction of the partial standard sum to the manuscript's ancestor sum
`∑_{J ⊇ Q} k_J ã_J(x₀)` is the content of
`standardLevelSum_eq_ancestor_term`: at each level only the unique ancestor
cell of `Q` contributes, because the tilde atoms vanish off their cells.
-/

/--
**Proposition `boup`, part B.**  For the standard representation `(sumf)`, the
partial sum up to scale `Q.level`, evaluated at any point `x₀ ∈ Q`, is the
average of `f` over `Q`:

`∑_{J ⊇ Q} k_J ã_J(x₀) = ∫ f · 1_Q/|Q| dm`.

The proof combines `partialHaarSum_eq_partialStandardSum` with the evaluation
theorem `partialHaarSum_eq_integral_mul_diracKernel`.
-/
theorem claimB (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    (Q : GoodGridCell G) {x₀ : α} (hx₀ : x₀ ∈ Q.cell) :
    partialStandardSum G F p s f hf Q.level x₀ =
      ∫ x, f x * ((diracKernel G Q x : ℝ) : ℂ) ∂G.grid.μ := by
  rw [← partialHaarSum_eq_partialStandardSum G F p s f hf Q.level x₀]
  exact partialHaarSum_eq_integral_mul_diracKernel G F f hf Q hx₀

/--
At each level `k`, the standard blocks evaluated at a point `x₀` collapse to
the single ancestor term: the contribution of the unique pair `(c, P)` with
`c ∈ 𝒫^k`, `P ∈ 𝒫^{k+1}`, `x₀ ∈ P ⊆ c`.  All other terms vanish because the
tilde atoms are supported on their cells.

Together with `claimB`, this identifies the partial standard sum with the
manuscript's ancestor sum `∑_{J ⊇ Q} k_J ã_J(x₀)`.
-/
theorem standardLevelSum_eq_ancestor_term (G : GoodGridSpace (α := α))
    [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := HaarRepresentation.GridOf G))
    (p : ℝ≥0∞) (s : ℝ) (f : α → ℂ) (hf : Integrable f G.grid.μ)
    {k : ℕ} {c : Set α} (hc : c ∈ G.grid.grid.partitions k)
    (P : WeakGridSpace.LevelCell G.toWeakGridSpace (k + 1)) (hPc : P.1 ⊆ c)
    {x₀ : α} (hx₀ : x₀ ∈ P.1) :
    ∑ c' ∈ (G.grid.grid.partitions k).attach,
      StandardAtomicRepresentation.standardCellBlockFunction G F p s f hf
        ⟨k, c'.1, c'.2⟩ x₀ =
      ((StandardAtomicRepresentation.tildeCoeff G F
          (StandardAtomicRepresentation.c₂ G) p s f hf ⟨k, c, hc⟩ P : ℝ) : ℂ) *
        StandardAtomicRepresentation.tildeAtom G F
          (StandardAtomicRepresentation.c₂ G) p s f hf ⟨k, c, hc⟩ P x₀ := by
  classical
  have hx₀c : x₀ ∈ c := hPc hx₀
  -- only the ancestor cell `c` contributes at level `k`
  rw [Finset.sum_eq_single_of_mem
    (⟨c, hc⟩ : {t : Set α // t ∈ G.grid.grid.partitions k})
    (Finset.mem_attach _ _) ?_]
  · -- within the block of `c`, only the child `P ∋ x₀` contributes
    have hPmem : P ∈ StandardAtomicRepresentation.childrenOfCell G ⟨k, c, hc⟩ :=
      (StandardAtomicRepresentation.mem_childrenOfCell_iff G ⟨k, c, hc⟩ P).2
        (((HaarRepresentation.GridOf G).mem_childrenFinset_iff k c P.1).2 ⟨P.2, hPc⟩)
    rw [StandardAtomicRepresentation.standardCellBlockFunction,
      Finset.sum_eq_single_of_mem P hPmem ?_]
    intro P' _ hP'P
    have hx₀P' : x₀ ∉ P'.1 := by
      intro hx₀P'
      exact hP'P (Subtype.ext (cell_eq_of_mem_of_mem G P'.2 P.2 hx₀P' hx₀))
    rw [StandardAtomicRepresentation.tildeAtom_eq_zero_of_not_mem G F
      (StandardAtomicRepresentation.c₂ G) p s f hf ⟨k, c, hc⟩ P' hx₀P', mul_zero]
  · -- blocks of the other level-`k` cells vanish at `x₀`
    intro c' _ hc'c
    rw [StandardAtomicRepresentation.standardCellBlockFunction]
    refine Finset.sum_eq_zero fun P' hP' => ?_
    have hP'sub : P'.1 ⊆ c'.1 :=
      (((HaarRepresentation.GridOf G).mem_childrenFinset_iff k c'.1 P'.1).1
        ((StandardAtomicRepresentation.mem_childrenOfCell_iff G ⟨k, c'.1, c'.2⟩ P').1
          hP')).2
    have hx₀P' : x₀ ∉ P'.1 := by
      intro hx₀P'
      exact hc'c (Subtype.ext (cell_eq_of_mem_of_mem G c'.2 hc (hP'sub hx₀P') hx₀c))
    rw [StandardAtomicRepresentation.tildeAtom_eq_zero_of_not_mem G F
      (StandardAtomicRepresentation.c₂ G) p s f hf ⟨k, c'.1, c'.2⟩ P' hx₀P', mul_zero]

end DiracApproximation

end

end GoodGridSpace
