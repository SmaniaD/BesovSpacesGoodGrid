import BesovSpacesGoodGrid.GoodGrid.RegularDomains
import BesovSpacesGoodGrid.GoodGrid.Multipliers.NonArchimedeanProperty

/-!
# Non-Archimedean regular-domain multiplier statements

This file records the regular-domain analogue of the non-Archimedean
multiplier estimates proved for strongly regular domains.

The statements are intentionally split into two styles.

* The non-uniform version allows each `Ω i` to have its own regularity
  constants `C i`, `c i`.  The local overlap hypothesis therefore weights each
  domain by the bounded-Besov indicator gauge
  `1 + regularDomainIndicatorCost`.
* The uniform version assumes one `RegularFamily`; the local overlap only
  counts the active weights, while the family regularity is part of the
  structural constant.

In both styles the support/localization conclusion is part of the general
statement.  Positivity is only an extra conclusion of the positive variants.
The statements are formulated on the bounded Besov gauge: the input comes with
an a.e. bound `‖f‖ ≤ M`, and the output estimate controls
`pqCost S + ‖h‖∞`.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
The non-uniform local overlap cost for regular domains.

For a source cell `Q`, this sums the absolute active weights of all domains
met by `Q`, multiplied by the individual bounded-Besov indicator gauge of that
domain.  The extra `1` records the `L∞` part of the quasialgebra estimate for
the indicator.
-/
noncomputable def regularDomainOverlapCostInfinite
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (C c Θ : ℕ → ℝ) (p q : ℝ≥0∞)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℝ≥0∞ := by
  classical
  exact ∑' i : {i // i ∈ Λ},
    if (Q.1 ∩ Ω i.1).Nonempty then
      ENNReal.ofReal
        (|Θ i.1| *
          (1 + regularDomainIndicatorCost G (Ω i.1) s (C i.1) (c i.1) p q))
    else 0

/--
A single active regular-domain summand is bounded by the non-uniform overlap
cost of the cell.

This is the local extraction used in the intended levelwise proof: once an
active source cell `Q` meets `Ω i`, the global hypothesis on
`regularDomainOverlapCostInfinite` controls the weighted indicator gauge of
that one domain.
-/
theorem regularDomainOverlapCostInfinite_term_le
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (C c Θ : ℕ → ℝ) (p q : ℝ≥0∞)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {i : ℕ} (hi : i ∈ Λ) (hmeet : (Q.1 ∩ Ω i).Nonempty) :
    ENNReal.ofReal
        (|Θ i| * (1 + regularDomainIndicatorCost G (Ω i) s (C i) (c i) p q)) ≤
      regularDomainOverlapCostInfinite G Λ Ω s C c Θ p q Q := by
  classical
  change
    ENNReal.ofReal
        (|Θ i| * (1 + regularDomainIndicatorCost G (Ω i) s (C i) (c i) p q)) ≤
      ∑' j : {j // j ∈ Λ},
        if (Q.1 ∩ Ω j.1).Nonempty then
          ENNReal.ofReal
            (|Θ j.1| *
              (1 + regularDomainIndicatorCost G (Ω j.1) s (C j.1) (c j.1) p q))
        else 0
  simpa only [hmeet, if_true] using
    ENNReal.le_tsum
      (f := fun j : {j // j ∈ Λ} =>
        if (Q.1 ∩ Ω j.1).Nonempty then
          ENNReal.ofReal
            (|Θ j.1| *
              (1 + regularDomainIndicatorCost G (Ω j.1) s (C j.1) (c j.1) p q))
        else 0)
      ⟨i, hi⟩

/-- Every grid level cell is nonempty, because it has positive grid measure. -/
theorem levelCell_nonempty
    (G : GoodGridSpace (α := α)) {k : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    Q.1.Nonempty := by
  by_contra hQempty
  have hQeq : Q.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hQempty
  have hpos : 0 < G.grid.μ Q.1 :=
    G.grid.positive_measure k Q.1 Q.2
  rw [hQeq] at hpos
  simp at hpos

/--
If a level cell is contained in an active domain, then the corresponding
non-uniform overlap summand is controlled by the cell overlap cost.
-/
theorem regularDomainOverlapCostInfinite_term_le_of_subset
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (C c Θ : ℕ → ℝ) (p q : ℝ≥0∞)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {i : ℕ} (hi : i ∈ Λ) (hsubset : Q.1 ⊆ Ω i) :
    ENNReal.ofReal
        (|Θ i| * (1 + regularDomainIndicatorCost G (Ω i) s (C i) (c i) p q)) ≤
      regularDomainOverlapCostInfinite G Λ Ω s C c Θ p q Q := by
  obtain ⟨z, hzQ⟩ := levelCell_nonempty G Q
  exact regularDomainOverlapCostInfinite_term_le
    G Λ Ω s C c Θ p q Q hi ⟨z, hzQ, hsubset hzQ⟩

/--
Real-valued extraction from the non-uniform overlap hypothesis for a cell
contained in an active domain.
-/
theorem regularDomain_weightedIndicatorCost_le_of_overlap_subset
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (C c Θ : ℕ → ℝ) (p q : ℝ≥0∞) {N : ℝ} (hN0 : 0 ≤ N)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {i : ℕ} (hi : i ∈ Λ) (hsubset : Q.1 ⊆ Ω i)
    (hoverlap : regularDomainOverlapCostInfinite G Λ Ω s C c Θ p q Q ≤
      ENNReal.ofReal N) :
    |Θ i| * (1 + regularDomainIndicatorCost G (Ω i) s (C i) (c i) p q) ≤ N := by
  have hterm :
      ENNReal.ofReal
          (|Θ i| *
            (1 + regularDomainIndicatorCost G (Ω i) s (C i) (c i) p q)) ≤
        ENNReal.ofReal N :=
    (regularDomainOverlapCostInfinite_term_le_of_subset
      G Λ Ω s C c Θ p q Q hi hsubset).trans hoverlap
  exact (ENNReal.ofReal_le_ofReal_iff hN0).mp hterm

/--
Real-valued extraction from the non-uniform overlap hypothesis for a cell that
meets an active regular domain.  The overlap controls
`|Θ i| * (1 + indicatorCost Ωᵢ)`; since the indicator cost is nonnegative, it
also controls `|Θ i|` itself.
-/
theorem regularDomain_weight_abs_le_of_overlap_meet
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (C c Θ : ℕ → ℝ) (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ q)] {N : ℝ} (hN0 : 0 ≤ N) {k : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {i : ℕ} (hi : i ∈ Λ)
    (hΩi : RegularDomain G (Ω i) (1 - p.toReal * s) (C i) (c i))
    (hmeet : (Q.1 ∩ Ω i).Nonempty)
    (hoverlap : regularDomainOverlapCostInfinite G Λ Ω s C c Θ p q Q ≤
      ENNReal.ofReal N) :
    |Θ i| ≤ N := by
  have hweighted :
      |Θ i| *
          (1 + regularDomainIndicatorCost G (Ω i) s (C i) (c i) p q) ≤ N := by
    have hterm :
        ENNReal.ofReal
            (|Θ i| *
              (1 + regularDomainIndicatorCost G (Ω i) s (C i) (c i) p q)) ≤
          ENNReal.ofReal N :=
      (regularDomainOverlapCostInfinite_term_le
        G Λ Ω s C c Θ p q Q hi hmeet).trans hoverlap
    exact (ENNReal.ofReal_le_ofReal_iff hN0).mp hterm
  have hcost0 :
      0 ≤ regularDomainIndicatorCost G (Ω i) s (C i) (c i) p q :=
    regularDomainIndicatorCost_nonneg
      G (Ω i) s (C i) (c i) p q hp hp_top hΩi
  have hfactor : 1 ≤ 1 + regularDomainIndicatorCost G (Ω i) s (C i) (c i) p q := by
    linarith
  calc
    |Θ i| = |Θ i| * 1 := by ring
    _ ≤ |Θ i| *
        (1 + regularDomainIndicatorCost G (Ω i) s (C i) (c i) p q) :=
      mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)
    _ ≤ N := hweighted

/-- Comparison test for real nonnegative series, keeping the canonical `tsum`
as the sum of the smaller series. -/
theorem hasSum_tsum_of_nonneg_le_hasSum
    {ι : Type*} {a b : ι → ℝ} {T N : ℝ}
    (ha_nonneg : ∀ i, 0 ≤ a i)
    (hle : ∀ i, a i ≤ b i)
    (hb_sum : HasSum b T)
    (hT_le : T ≤ N) :
    HasSum a (∑' i, a i) ∧ (∑' i, a i) ≤ N := by
  classical
  have ha_sum : Summable a :=
    Summable.of_nonneg_of_le ha_nonneg hle hb_sum.summable
  refine ⟨ha_sum.hasSum, ?_⟩
  calc
    (∑' i, a i) ≤ ∑' i, b i :=
      ha_sum.tsum_le_tsum hle hb_sum.summable
    _ = T := hb_sum.tsum_eq
    _ ≤ N := hT_le

/--
At a point in an active source cell, the non-uniform overlap hypothesis bounds
the absolute weighted-indicator series.  Unlike the uniform regular-family
lemma, this does not use disjointness of the domains; summability comes from
the `ℝ≥0∞` overlap sum itself.
-/
theorem regularDomain_weightedIndicator_norm_tsum_le_of_active_cell
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (C c Θ : ℕ → ℝ) (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ q)] {N : ℝ} (hN0 : 0 ≤ N)
    (hΩ : ∀ i ∈ Λ, RegularDomain G (Ω i) (1 - p.toReal * s) (C i) (c i))
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {z : α} (hzQ : z ∈ Q.1)
    (hoverlap : regularDomainOverlapCostInfinite G Λ Ω s C c Θ p q Q ≤
      ENNReal.ofReal N) :
    HasSum
      (fun i : {i // i ∈ Λ} =>
        ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖)
      (∑' i : {i // i ∈ Λ},
        ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖) ∧
    (∑' i : {i // i ∈ Λ},
        ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖) ≤ N := by
  classical
  let Term : {i // i ∈ Λ} → ℝ≥0∞ := fun i =>
    if (Q.1 ∩ Ω i.1).Nonempty then
      ENNReal.ofReal
        (|Θ i.1| *
          (1 + regularDomainIndicatorCost G (Ω i.1) s (C i.1) (c i.1) p q))
    else 0
  have hterm_ne_top : ∀ i, Term i ≠ ∞ := by
    intro i
    dsimp [Term]
    split_ifs
    · exact ENNReal.ofReal_ne_top
    · simp
  have htsum_ne_top : (∑' i, Term i) ≠ ∞ := by
    have hTerm_le :
        (∑' i : {i // i ∈ Λ}, Term i) ≤ ENNReal.ofReal N := by
      simpa [Term, regularDomainOverlapCostInfinite] using hoverlap
    exact (hTerm_le.trans_lt ENNReal.ofReal_lt_top).ne
  have hTerm_sum : Summable fun i => (Term i).toReal :=
    ENNReal.summable_toReal htsum_ne_top
  have htoReal_le : (∑' i, (Term i).toReal) ≤ N := by
    have hTerm_le :
        (∑' i : {i // i ∈ Λ}, Term i) ≤ ENNReal.ofReal N := by
      simpa [Term, regularDomainOverlapCostInfinite] using hoverlap
    calc
      (∑' i : {i // i ∈ Λ}, (Term i).toReal)
          = (∑' i : {i // i ∈ Λ}, Term i).toReal :=
        (ENNReal.tsum_toReal_eq hterm_ne_top).symm
      _ ≤ (ENNReal.ofReal N).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hTerm_le
      _ = N := ENNReal.toReal_ofReal hN0
  refine hasSum_tsum_of_nonneg_le_hasSum
    (fun i => norm_nonneg _) ?_ hTerm_sum.hasSum htoReal_le
  intro i
  by_cases hzi : z ∈ Ω i.1
  · have hmeet : (Q.1 ∩ Ω i.1).Nonempty := ⟨z, hzQ, hzi⟩
    have hcost0 :
        0 ≤ regularDomainIndicatorCost G (Ω i.1) s (C i.1) (c i.1) p q :=
      regularDomainIndicatorCost_nonneg
        G (Ω i.1) s (C i.1) (c i.1) p q hp hp_top (hΩ i.1 i.2)
    have hfactor : 1 ≤
        1 + regularDomainIndicatorCost G (Ω i.1) s (C i.1) (c i.1) p q := by
      linarith
    have hprod0 :
        0 ≤ |Θ i.1| *
          (1 + regularDomainIndicatorCost G (Ω i.1) s (C i.1) (c i.1) p q) :=
      mul_nonneg (abs_nonneg _) (by linarith)
    have hTerm_toReal :
        (Term i).toReal =
          |Θ i.1| *
            (1 + regularDomainIndicatorCost G (Ω i.1) s (C i.1) (c i.1) p q) := by
      dsimp [Term]
      rw [if_pos hmeet]
      exact ENNReal.toReal_ofReal hprod0
    calc
      ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖
          = |Θ i.1| := by
            simp [Set.indicator_of_mem hzi, Complex.norm_real]
      _ = |Θ i.1| * 1 := by ring
      _ ≤ |Θ i.1| *
          (1 + regularDomainIndicatorCost G (Ω i.1) s (C i.1) (c i.1) p q) :=
        mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)
      _ = (Term i).toReal := hTerm_toReal.symm
  · have hnorm_zero :
        ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖ = 0 := by
      simp [Set.indicator_of_notMem hzi]
    rw [hnorm_zero]
    exact ENNReal.toReal_nonneg

/--
Product version of the non-uniform pointwise estimate: once the absolute
indicator series is controlled, multiplying every term by the fixed value
`f z` gives the expected `N * ‖f z‖` bound.
-/
theorem regularDomain_weightedIndicator_product_tsum_norm_le_of_active_cell
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (C c Θ : ℕ → ℝ) (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ q)] {N : ℝ} (hN0 : 0 ≤ N)
    (hΩ : ∀ i ∈ Λ, RegularDomain G (Ω i) (1 - p.toReal * s) (C i) (c i))
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {z : α} (hzQ : z ∈ Q.1)
    (hoverlap : regularDomainOverlapCostInfinite G Λ Ω s C c Θ p q Q ≤
      ENNReal.ofReal N)
    (f : α → ℂ) :
    ‖(∑' i : {i // i ∈ Λ},
        (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
      ≤ N * ‖f z‖ := by
  classical
  obtain ⟨hAbs, hAbs_le⟩ :=
    regularDomain_weightedIndicator_norm_tsum_le_of_active_cell
      G Λ Ω s C c Θ p q hp hp_top hN0 hΩ Q hzQ hoverlap
  have hsummable_prod_norm :
      Summable fun i : {i // i ∈ Λ} =>
        ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z‖ := by
    simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using
      hAbs.summable.mul_right ‖f z‖
  have hnorm_le :
      ‖(∑' i : {i // i ∈ Λ},
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
        ≤ ∑' i : {i // i ∈ Λ},
          ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z‖ :=
    norm_tsum_le_tsum_norm hsummable_prod_norm
  have htsum_prod :
      (∑' i : {i // i ∈ Λ},
          ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z‖) =
        (∑' i : {i // i ∈ Λ},
          ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖) *
          ‖f z‖ := by
    simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using
      hAbs.summable.tsum_mul_right ‖f z‖
  calc
    ‖(∑' i : {i // i ∈ Λ},
        (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
        ≤ ∑' i : {i // i ∈ Λ},
          ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z‖ :=
      hnorm_le
    _ = (∑' i : {i // i ∈ Λ},
          ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖) *
          ‖f z‖ := htsum_prod
    _ ≤ N * ‖f z‖ :=
      mul_le_mul_of_nonneg_right hAbs_le (norm_nonneg _)

/--
Almost everywhere non-uniform pointwise summability and `L∞` control for the
canonical weighted-domain-indicator product series.
-/
theorem regularDomain_weightedIndicator_product_tsum_bounds_ae
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (C c Θ : ℕ → ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {N M : ℝ} (hN0 : 0 ≤ N)
    (hΩ : ∀ i ∈ Λ, RegularDomain G (Ω i) (1 - p.toReal * s) (C i) (c i))
    (f : α → ℂ)
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hfbdd : ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ M)
    (hoverlap :
      ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        (R.block k).coeff Q ≠ 0 →
          regularDomainOverlapCostInfinite G Λ Ω s C c Θ p q Q ≤
            ENNReal.ofReal N) :
    ∀ᵐ z ∂G.toWeakGridSpace.measure,
      (f z ≠ 0 →
        HasSum
          (fun i : {i // i ∈ Λ} =>
            ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖)
          (∑' i : {i // i ∈ Λ},
            ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖) ∧
        (∑' i : {i // i ∈ Λ},
            ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖) ≤ N) ∧
      HasSum
        (fun i : {i // i ∈ Λ} =>
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
        (∑' i : {i // i ∈ Λ},
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z) ∧
      ‖(∑' i : {i // i ∈ Λ},
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
        ≤ N * ‖f z‖ ∧
      ‖(∑' i : {i // i ∈ Λ},
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
        ≤ N * M := by
  classical
  have hactive_ae :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        f z ≠ 0 →
          ∃ k, ∃ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            z ∈ Q.1 ∧ (R.block k).coeff Q ≠ 0 :=
    exists_active_cell_of_representsFunction_ne_zero_ae
      G s p q hs hp hp_top x R hRep
  filter_upwards [hactive_ae, hfbdd] with z hactive_z hfbdd_z
  by_cases hfz : f z = 0
  · have hprod_zero :
        (fun i : {i // i ∈ Λ} =>
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z) =
          fun _ => 0 := by
        funext i
        simp [hfz]
    have hsum_zero :
        (∑' i : {i // i ∈ Λ},
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z) = 0 := by
      rw [hprod_zero]
      simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hfz_ne
      exact (hfz_ne hfz).elim
    · rw [hprod_zero]
      exact summable_zero.hasSum
    · rw [hsum_zero, hfz]
      simp
    · rw [hsum_zero]
      simpa using mul_nonneg hN0 (regularFamilyRestriction_bound_nonneg G hfbdd)
  · rcases hactive_z hfz with ⟨k, Q, hzQ, hQcoeff⟩
    obtain ⟨hAbs, hAbs_le⟩ :=
      regularDomain_weightedIndicator_norm_tsum_le_of_active_cell
        G Λ Ω s C c Θ p q hp hp_top hN0 hΩ Q hzQ (hoverlap k Q hQcoeff)
    have hsummable_prod_norm :
        Summable fun i : {i // i ∈ Λ} =>
          ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z‖ := by
      simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using
        hAbs.summable.mul_right ‖f z‖
    have hsum :
        HasSum
          (fun i : {i // i ∈ Λ} =>
            (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
          (∑' i : {i // i ∈ Λ},
            (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z) :=
      hsummable_prod_norm.of_norm.hasSum
    have hnorm :
        ‖(∑' i : {i // i ∈ Λ},
            (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
          ≤ N * ‖f z‖ :=
      regularDomain_weightedIndicator_product_tsum_norm_le_of_active_cell
        G Λ Ω s C c Θ p q hp hp_top hN0 hΩ Q hzQ (hoverlap k Q hQcoeff) f
    refine ⟨?_, hsum, hnorm, ?_⟩
    · intro _hfz
      exact ⟨hAbs, hAbs_le⟩
    · exact hnorm.trans (mul_le_mul_of_nonneg_left hfbdd_z hN0)

/--
The uniform local overlap cost for a regular family.

The regularity constants are not included in the summand: they belong to the
single structural constant of the theorem.
-/
noncomputable def regularFamilyOverlapCostInfinite
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (Θ : ℕ → ℝ) {k : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℝ≥0∞ := by
  classical
  exact ∑' i : {i // i ∈ Λ},
    if (Q.1 ∩ Ω i.1).Nonempty then
      ENNReal.ofReal |Θ i.1|
    else 0

/--
A single active weight is bounded by the uniform regular-family overlap cost
of the cell.
-/
theorem regularFamilyOverlapCostInfinite_term_le
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (Θ : ℕ → ℝ) {k : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {i : ℕ} (hi : i ∈ Λ) (hmeet : (Q.1 ∩ Ω i).Nonempty) :
    ENNReal.ofReal |Θ i| ≤ regularFamilyOverlapCostInfinite G Λ Ω Θ Q := by
  classical
  change
    ENNReal.ofReal |Θ i| ≤
      ∑' j : {j // j ∈ Λ},
        if (Q.1 ∩ Ω j.1).Nonempty then
          ENNReal.ofReal |Θ j.1|
        else 0
  simpa only [hmeet, if_true] using
    ENNReal.le_tsum
      (f := fun j : {j // j ∈ Λ} =>
        if (Q.1 ∩ Ω j.1).Nonempty then
          ENNReal.ofReal |Θ j.1|
        else 0)
      ⟨i, hi⟩

/--
If a level cell is contained in an active member of a regular family, then the
corresponding uniform weight is controlled by the cell overlap cost.
-/
theorem regularFamilyOverlapCostInfinite_term_le_of_subset
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (Θ : ℕ → ℝ) {k : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {i : ℕ} (hi : i ∈ Λ) (hsubset : Q.1 ⊆ Ω i) :
    ENNReal.ofReal |Θ i| ≤ regularFamilyOverlapCostInfinite G Λ Ω Θ Q := by
  obtain ⟨z, hzQ⟩ := levelCell_nonempty G Q
  exact regularFamilyOverlapCostInfinite_term_le
    G Λ Ω Θ Q hi ⟨z, hzQ, hsubset hzQ⟩

/--
Real-valued extraction from the uniform overlap hypothesis for a cell contained
in an active family member.
-/
theorem regularFamily_weight_abs_le_of_overlap_subset
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (Θ : ℕ → ℝ) {N : ℝ} (hN0 : 0 ≤ N) {k : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {i : ℕ} (hi : i ∈ Λ) (hsubset : Q.1 ⊆ Ω i)
    (hoverlap : regularFamilyOverlapCostInfinite G Λ Ω Θ Q ≤ ENNReal.ofReal N) :
    |Θ i| ≤ N := by
  have hterm : ENNReal.ofReal |Θ i| ≤ ENNReal.ofReal N :=
    (regularFamilyOverlapCostInfinite_term_le_of_subset
      G Λ Ω Θ Q hi hsubset).trans hoverlap
  exact (ENNReal.ofReal_le_ofReal_iff hN0).mp hterm

/--
Real-valued extraction from the uniform overlap hypothesis for a cell that
meets an active family member.
-/
theorem regularFamily_weight_abs_le_of_overlap_meet
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (Θ : ℕ → ℝ) {N : ℝ} (hN0 : 0 ≤ N) {k : ℕ}
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {i : ℕ} (hi : i ∈ Λ) (hmeet : (Q.1 ∩ Ω i).Nonempty)
    (hoverlap : regularFamilyOverlapCostInfinite G Λ Ω Θ Q ≤ ENNReal.ofReal N) :
    |Θ i| ≤ N := by
  have hterm : ENNReal.ofReal |Θ i| ≤ ENNReal.ofReal N :=
    (regularFamilyOverlapCostInfinite_term_le
      G Λ Ω Θ Q hi hmeet).trans hoverlap
  exact (ENNReal.ofReal_le_ofReal_iff hN0).mp hterm

/--
An entire level cell cannot be contained in two different active members of a
regular family, because active members are pairwise disjoint and level cells
are nonempty.
-/
theorem regularFamily_unique_index_of_levelCell_subset
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    {k i j : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    (hi : i ∈ Λ) (hj : j ∈ Λ)
    (hQi : Q.1 ⊆ Ω i) (hQj : Q.1 ⊆ Ω j) :
    i = j := by
  by_contra hij
  obtain ⟨z, hzQ⟩ := levelCell_nonempty G Q
  have hdisj : Disjoint (Ω i) (Ω j) :=
    hΩ.pairwise_disjoint i hi j hj hij
  exact Set.disjoint_left.mp hdisj (hQi hzQ) (hQj hzQ)

/--
An a.e. bound on a represented function gives the `L∞` witness and norm bound
used in the bounded Besov gauge.

The main theorems state the output estimate with a genuine `L∞` norm.  This
small bridge turns the pointwise estimate `‖h‖ ≤ B` into the formal term
`‖MemLp.toLp h hmemInf‖ ≤ B`.
-/
theorem linftyMemLp_and_norm_le_of_representsFunction_bound
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    {B : ℝ} (hB0 : 0 ≤ B) {h : α → ℂ}
    {y : Lp ℂ p G.toWeakGridSpace.measure}
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) h y)
    (hbound : ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖h z‖ ≤ B) :
    ∃ hmemInf : MemLp h (∞ : ℝ≥0∞) G.toWeakGridSpace.measure,
      ‖MemLp.toLp h hmemInf‖ ≤ B := by
  let μ := G.toWeakGridSpace.measure
  have hmeas : AEStronglyMeasurable h μ := by
    exact (Lp.memLp y).aestronglyMeasurable.congr hRep
  have hmemInf : MemLp h (∞ : ℝ≥0∞) μ :=
    memLp_top_of_bound hmeas B (by simpa [μ] using hbound)
  refine ⟨hmemInf, ?_⟩
  have htop :
      eLpNorm h (∞ : ℝ≥0∞) μ ≤ ENNReal.ofReal B := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (by simpa [μ] using hbound)
  have hcoe :
      eLpNorm ((MemLp.toLp h hmemInf : Lp ℂ (∞ : ℝ≥0∞) μ) : α → ℂ)
          (∞ : ℝ≥0∞) μ =
        eLpNorm h (∞ : ℝ≥0∞) μ :=
    eLpNorm_congr_ae (MemLp.coeFn_toLp hmemInf)
  rw [Lp.norm_def]
  rw [hcoe]
  exact (ENNReal.le_ofReal_iff_toReal_le hmemInf.eLpNorm_ne_top hB0).1 htop

/-- The zero representation has finite `(p,q)` cost. -/
private theorem zero_representation_finitePQCost
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' q' : ℝ≥0∞}
    [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    (A : WeakGridSpace.AtomFamily G' s' p' u') :
    WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q')
      (WeakGridSpace.LpGridRepresentation.zero A) := by
  have hp_pos : 0 < p'.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p')).ne' A.p_ne_top
  by_cases hqtop : q' = ∞
  · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_pos hqtop]
    refine ⟨0, ?_⟩
    rintro x ⟨j, rfl⟩
    have hzero : (0 : ℝ) ^ (p'.toReal)⁻¹ = 0 :=
      Real.zero_rpow (inv_ne_zero hp_pos.ne')
    simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower, hzero]
  · rw [WeakGridSpace.LpGridRepresentation.FinitePQCost, if_neg hqtop]
    have hq_pos : 0 < q'.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q')).ne' hqtop
    have hpow_ne : q'.toReal / p'.toReal ≠ 0 :=
      div_ne_zero hq_pos.ne' hp_pos.ne'
    simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower,
      Real.zero_rpow hpow_ne]

/-- The zero representation has zero `(p,q)` cost. -/
private theorem zero_representation_pqCost_eq_zero
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' q' : ℝ≥0∞}
    [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    (A : WeakGridSpace.AtomFamily G' s' p' u') :
    WeakGridSpace.LpGridRepresentation.pqCost (q := q')
      (WeakGridSpace.LpGridRepresentation.zero A) = 0 := by
  have hp_pos : 0 < p'.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p')).ne' A.p_ne_top
  by_cases hqtop : q' = ∞
  · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos hqtop]
    have hzero : (0 : ℝ) ^ (p'.toReal)⁻¹ = 0 :=
      Real.zero_rpow (inv_ne_zero hp_pos.ne')
    simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower, hzero]
  · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hqtop]
    have hq_pos : 0 < q'.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q')).ne' hqtop
    have hpow_ne : q'.toReal / p'.toReal ≠ 0 :=
      div_ne_zero hq_pos.ne' hp_pos.ne'
    have hqinv_ne : (q'.toReal)⁻¹ ≠ 0 := inv_ne_zero hq_pos.ne'
    simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower,
      Real.zero_rpow hpow_ne, Real.zero_rpow hqinv_ne]

/-- A nonzero coefficient in a scaled level block comes from the original block. -/
theorem levelBlock_smul_coeff_ne_zero
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' : ℝ≥0∞}
    [Fact (1 ≤ p')]
    (A : WeakGridSpace.AtomFamily G' s' p' u') {k : ℕ}
    (c : ℂ) (B : WeakGridSpace.LevelBlock A k)
    (Q : WeakGridSpace.LevelCell G' k)
    (hcoeff : (WeakGridSpace.LevelBlock.smul A c B).coeff Q ≠ 0) :
    B.coeff Q ≠ 0 := by
  intro hzero
  exact hcoeff (by simp [WeakGridSpace.LevelBlock.smul, hzero])

/--
A nonzero coefficient in a scaled grid representation comes from the original
representation.
-/
theorem lpGridRepresentation_smul_coeff_ne_zero
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' : ℝ≥0∞}
    [Fact (1 ≤ p')]
    {A : WeakGridSpace.AtomFamily G' s' p' u'} {g : Lp ℂ p' G'.measure}
    (c : ℂ) (R : WeakGridSpace.LpGridRepresentation A g)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G' k)
    (hcoeff : ((WeakGridSpace.LpGridRepresentation.smul c R).block k).coeff Q ≠ 0) :
    (R.block k).coeff Q ≠ 0 := by
  exact levelBlock_smul_coeff_ne_zero A c (R.block k) Q hcoeff

/--
In a positive Souza level block, the raw local scalar chosen as the atom is a
nonnegative real number.  The positive-block definition states this at the
level of the canonical atom function; evaluating on a point of the cell
recovers the underlying local scalar.
-/
theorem souzaPositiveLevelBlock_atom_nonneg_real
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {k : ℕ}
    {B : WeakGridSpace.LevelBlock
      (souzaAtomFamily G s p hs hp hp_top) k}
    (hB : SouzaPositiveLevelBlock G s p hs hp hp_top B)
    (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    ∃ a : ℝ, 0 ≤ a ∧ (show ℂ from B.atom Q) = (a : ℂ) := by
  obtain ⟨_c, _hc0, _hcoeff, hatom⟩ := hB Q
  let a : ℝ := (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹)
  refine ⟨a, Real.rpow_nonneg ENNReal.toReal_nonneg _, ?_⟩
  obtain ⟨z, hzQ⟩ := levelCell_nonempty G Q
  have hleft :
      (souzaAtomFamily G s p hs hp hp_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
          (B.atom Q) z = (show ℂ from B.atom Q) := by
    change
      (Q.1.indicator (fun _ => (show ℂ from B.atom Q)) z) =
        (show ℂ from B.atom Q)
    rw [Set.indicator_of_mem hzQ]
  have hright :
      canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) z = (a : ℂ) := by
    simp [canonicalSouzaAtom, goodGridCellOfLevelCell, a, hzQ]
  calc
    (show ℂ from B.atom Q)
        = (souzaAtomFamily G s p hs hp hp_top).toFunction
            (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace k Q)
            (B.atom Q) z := hleft.symm
    _ = canonicalSouzaAtom G s p (goodGridCellOfLevelCell G Q) z :=
      congrFun hatom z
    _ = (a : ℂ) := hright

/--
The weighted ancestor tower of a positive Souza representation is itself a
nonnegative real scalar.
-/
theorem weightedAncestorCoeffSum_nonneg_real_of_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) :
    ∃ a : ℝ, 0 ≤ a ∧ weightedAncestorCoeffSum G R Q = (a : ℂ) := by
  classical
  let coeffReal : (j : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace j → ℝ :=
    fun j J => Classical.choose
      (((souzaPositiveRepresentation_iff_canonical_and_nonneg
        G s p hs hp hp_top R).mp hR).1 j J)
  let atomReal : (j : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace j → ℝ :=
    fun j J => Classical.choose
      (souzaPositiveLevelBlock_atom_nonneg_real
        G s p hs hp hp_top (hR j) J)
  let termReal : (j : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace j → ℝ :=
    fun j J => if Q.1 ⊆ J.1 then coeffReal j J * atomReal j J else 0
  refine ⟨∑ j ∈ Finset.range (k + 1),
      ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j, termReal j J, ?_, ?_⟩
  · refine Finset.sum_nonneg ?_
    intro j _hj
    refine Finset.sum_nonneg ?_
    intro J _hJ
    dsimp [termReal]
    split_ifs
    · exact mul_nonneg
        (Classical.choose_spec
          (((souzaPositiveRepresentation_iff_canonical_and_nonneg
            G s p hs hp hp_top R).mp hR).1 j J)).1
        (Classical.choose_spec
          (souzaPositiveLevelBlock_atom_nonneg_real
            G s p hs hp hp_top (hR j) J)).1
    · exact le_rfl
  · unfold weightedAncestorCoeffSum
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl ?_
    intro J hJ
    by_cases hsub : Q.1 ⊆ J.1
    · have hcoeff :
          (R.block j).coeff J = (coeffReal j J : ℂ) :=
        (Classical.choose_spec
          (((souzaPositiveRepresentation_iff_canonical_and_nonneg
            G s p hs hp hp_top R).mp hR).1 j J)).2
      have hatom :
          (show ℂ from (R.block j).atom J) = (atomReal j J : ℂ) :=
        (Classical.choose_spec
          (souzaPositiveLevelBlock_atom_nonneg_real
            G s p hs hp hp_top (hR j) J)).2
      simp [termReal, hsub, hcoeff, hatom, Complex.ofReal_mul]
    · simp [termReal, hsub]

/--
The strict weighted ancestor tower of a positive Souza representation is a
nonnegative real scalar.
-/
theorem strictWeightedAncestorCoeffSum_nonneg_real_of_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x : Lp ℂ p G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (hR : SouzaPositiveRepresentation G s p hs hp hp_top R)
    {j : ℕ} (J : WeakGridSpace.LevelCell G.toWeakGridSpace j) :
    ∃ a : ℝ, 0 ≤ a ∧ strictWeightedAncestorCoeffSum G R J = (a : ℂ) := by
  classical
  let coeffReal : (k : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace k → ℝ :=
    fun k Q => Classical.choose
      (((souzaPositiveRepresentation_iff_canonical_and_nonneg
        G s p hs hp hp_top R).mp hR).1 k Q)
  let atomReal : (k : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace k → ℝ :=
    fun k Q => Classical.choose
      (souzaPositiveLevelBlock_atom_nonneg_real
        G s p hs hp hp_top (hR k) Q)
  let termReal : (k : ℕ) → WeakGridSpace.LevelCell G.toWeakGridSpace k → ℝ :=
    fun k Q => if J.1 ⊆ Q.1 then coeffReal k Q * atomReal k Q else 0
  refine ⟨∑ k ∈ Finset.range j,
      ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k, termReal k Q, ?_, ?_⟩
  · refine Finset.sum_nonneg ?_
    intro k _hk
    refine Finset.sum_nonneg ?_
    intro Q _hQ
    dsimp [termReal]
    split_ifs
    · exact mul_nonneg
        (Classical.choose_spec
          (((souzaPositiveRepresentation_iff_canonical_and_nonneg
            G s p hs hp hp_top R).mp hR).1 k Q)).1
        (Classical.choose_spec
          (souzaPositiveLevelBlock_atom_nonneg_real
            G s p hs hp hp_top (hR k) Q)).1
    · exact le_rfl
  · unfold strictWeightedAncestorCoeffSum
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl ?_
    intro Q hQ
    by_cases hsub : J.1 ⊆ Q.1
    · have hcoeff :
          (R.block k).coeff Q = (coeffReal k Q : ℂ) :=
        (Classical.choose_spec
          (((souzaPositiveRepresentation_iff_canonical_and_nonneg
            G s p hs hp hp_top R).mp hR).1 k Q)).2
      have hatom :
          (show ℂ from (R.block k).atom Q) = (atomReal k Q : ℂ) :=
        (Classical.choose_spec
          (souzaPositiveLevelBlock_atom_nonneg_real
            G s p hs hp hp_top (hR k) Q)).2
      simp [termReal, hsub, hcoeff, hatom, Complex.ofReal_mul]
    · simp [termReal, hsub]

/--
The `u₁` product block is cone-positive when both input representations are
positive.  Its atom is inherited from the first representation, while its
coefficient is the product of a nonnegative coefficient and the nonnegative
ancestor tower of the second representation.
-/
theorem quasiU1Block_conePositive_of_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {xf xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xf)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hRf : SouzaPositiveRepresentation G s p hs hp hp_top Rf)
    (hRg : SouzaPositiveRepresentation G s p hs hp hp_top Rg)
    (k : ℕ) :
    SouzaConePositiveLevelBlock G s p hs hp hp_top
      (quasiU1Block G s p hs hp hp_top Rf Rg k) := by
  intro Q
  constructor
  · obtain ⟨c, hc0, hcoeff⟩ :=
      ((souzaPositiveRepresentation_iff_canonical_and_nonneg
        G s p hs hp hp_top Rf).mp hRf).1 k Q
    obtain ⟨a, ha0, htower⟩ :=
      weightedAncestorCoeffSum_nonneg_real_of_positive
        G s p hs hp hp_top Rg hRg Q
    refine ⟨c * a, mul_nonneg hc0 ha0, ?_⟩
    simp [quasiU1Block, hcoeff, htower, Complex.ofReal_mul]
  · simpa [quasiU1Block] using
      (souzaPositiveRepresentation_conePositive
        G s p hs hp hp_top hRf k Q).2

/--
The `u₁` product block is in fact Souza-positive when both input
representations are positive: the coefficient is nonnegative real, and the
atom is the canonical atom inherited from the first representation.
-/
theorem quasiU1Block_positive_of_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {xf xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xf)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hRf : SouzaPositiveRepresentation G s p hs hp hp_top Rf)
    (hRg : SouzaPositiveRepresentation G s p hs hp hp_top Rg)
    (k : ℕ) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (quasiU1Block G s p hs hp hp_top Rf Rg k) := by
  intro Q
  obtain ⟨c, hc0, hcoeff, hatom⟩ := hRf k Q
  obtain ⟨a, ha0, htower⟩ :=
    weightedAncestorCoeffSum_nonneg_real_of_positive
      G s p hs hp hp_top Rg hRg Q
  refine ⟨c * a, mul_nonneg hc0 ha0, ?_, ?_⟩
  · simp [quasiU1Block, hcoeff, htower, Complex.ofReal_mul]
  · simpa [quasiU1Block] using hatom

/--
The `u₂` product block is cone-positive when both input representations are
positive.  Its atom is inherited from the second representation, while its
coefficient is the product of a nonnegative coefficient and the nonnegative
strict ancestor tower of the first representation.
-/
theorem quasiU2Block_conePositive_of_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {xf xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xf)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hRf : SouzaPositiveRepresentation G s p hs hp hp_top Rf)
    (hRg : SouzaPositiveRepresentation G s p hs hp hp_top Rg)
    (j : ℕ) :
    SouzaConePositiveLevelBlock G s p hs hp hp_top
      (quasiU2Block G s p hs hp hp_top Rf Rg j) := by
  intro J
  constructor
  · obtain ⟨c, hc0, hcoeff⟩ :=
      ((souzaPositiveRepresentation_iff_canonical_and_nonneg
        G s p hs hp hp_top Rg).mp hRg).1 j J
    obtain ⟨a, ha0, htower⟩ :=
      strictWeightedAncestorCoeffSum_nonneg_real_of_positive
        G s p hs hp hp_top Rf hRf J
    refine ⟨c * a, mul_nonneg hc0 ha0, ?_⟩
    simp [quasiU2Block, hcoeff, htower, Complex.ofReal_mul]
  · simpa [quasiU2Block] using
      (souzaPositiveRepresentation_conePositive
        G s p hs hp hp_top hRg j J).2

/--
The `u₂` product block is Souza-positive when both input representations are
positive: the coefficient is nonnegative real, and the atom is the canonical
atom inherited from the second representation.
-/
theorem quasiU2Block_positive_of_positive
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {xf xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xf)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hRf : SouzaPositiveRepresentation G s p hs hp hp_top Rf)
    (hRg : SouzaPositiveRepresentation G s p hs hp hp_top Rg)
    (j : ℕ) :
    SouzaPositiveLevelBlock G s p hs hp hp_top
      (quasiU2Block G s p hs hp hp_top Rf Rg j) := by
  intro J
  obtain ⟨c, hc0, hcoeff, hatom⟩ := hRg j J
  obtain ⟨a, ha0, htower⟩ :=
    strictWeightedAncestorCoeffSum_nonneg_real_of_positive
      G s p hs hp hp_top Rf hRf J
  refine ⟨c * a, mul_nonneg hc0 ha0, ?_, ?_⟩
  · simp [quasiU2Block, hcoeff, htower, Complex.ofReal_mul]
  · simpa [quasiU2Block] using hatom

/-- Scaling a representation scales each level coefficient power by `‖c‖^p`. -/
theorem lpGridRepresentation_smul_levelCoeffPower
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' : ℝ≥0∞}
    [Fact (1 ≤ p')]
    {A : WeakGridSpace.AtomFamily G' s' p' u'} {g : Lp ℂ p' G'.measure}
    (c : ℂ) (R : WeakGridSpace.LpGridRepresentation A g) (k : ℕ) :
    (WeakGridSpace.LpGridRepresentation.smul c R).levelCoeffPower k =
      ‖c‖ ^ p'.toReal * R.levelCoeffPower k := by
  unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
  unfold WeakGridSpace.LpGridRepresentation.smul WeakGridSpace.LevelBlock.smul
  calc
    (∑ Q : WeakGridSpace.LevelCell G' k, ‖c * (R.block k).coeff Q‖ ^ p'.toReal)
        = ∑ Q : WeakGridSpace.LevelCell G' k,
            (‖c‖ * ‖(R.block k).coeff Q‖) ^ p'.toReal := by
          refine Finset.sum_congr rfl ?_
          intro Q _hQ
          rw [norm_mul]
    _ = ∑ Q : WeakGridSpace.LevelCell G' k,
          ‖c‖ ^ p'.toReal * ‖(R.block k).coeff Q‖ ^ p'.toReal := by
          refine Finset.sum_congr rfl ?_
          intro Q _hQ
          rw [Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
    _ = ‖c‖ ^ p'.toReal *
          ∑ Q : WeakGridSpace.LevelCell G' k,
            ‖(R.block k).coeff Q‖ ^ p'.toReal := by
          rw [Finset.mul_sum]

/--
For two representations with disjoint coefficient support at a fixed level,
the repackaged sum has level coefficient power equal to the sum of the two
level coefficient powers.
-/
theorem lpGridRepresentation_add_levelCoeffPower_eq_of_disjoint_support
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' : ℝ≥0∞}
    [Fact (1 ≤ p')]
    {A : WeakGridSpace.AtomFamily G' s' p' u'}
    {g h : Lp ℂ p' G'.measure}
    (R : WeakGridSpace.LpGridRepresentation A g)
    (S : WeakGridSpace.LpGridRepresentation A h) (k : ℕ)
    (hdisj : ∀ Q : WeakGridSpace.LevelCell G' k,
      (R.block k).coeff Q ≠ 0 → (S.block k).coeff Q = 0) :
    (WeakGridSpace.LpGridRepresentation.add R S).levelCoeffPower k =
      R.levelCoeffPower k + S.levelCoeffPower k := by
  have hp_pos : 0 < p'.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p')).ne' A.p_ne_top
  have hzero_pow : (0 : ℝ) ^ p'.toReal = 0 :=
    Real.zero_rpow hp_pos.ne'
  unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro Q _hQ
  by_cases hRzero : (R.block k).coeff Q = 0
  · simp [WeakGridSpace.LpGridRepresentation.add, WeakGridSpace.LevelBlock.add,
      hRzero, hzero_pow, Complex.norm_real]
  · have hSzero : (S.block k).coeff Q = 0 := hdisj Q hRzero
    simp [WeakGridSpace.LpGridRepresentation.add, WeakGridSpace.LevelBlock.add,
      hSzero, hzero_pow, Complex.norm_real]

/-- A nonzero level coefficient power contains a nonzero coefficient. -/
theorem lpGridRepresentation_levelCoeffPower_ne_zero_exists_coeff
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' : ℝ≥0∞}
    [Fact (1 ≤ p')]
    {A : WeakGridSpace.AtomFamily G' s' p' u'} {g : Lp ℂ p' G'.measure}
    (R : WeakGridSpace.LpGridRepresentation A g) {k : ℕ}
    (hlevel : R.levelCoeffPower k ≠ 0) :
    ∃ Q : WeakGridSpace.LevelCell G' k, (R.block k).coeff Q ≠ 0 := by
  have hp_pos : 0 < p'.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p')).ne' A.p_ne_top
  by_contra hnone
  apply hlevel
  unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
  refine Finset.sum_eq_zero ?_
  intro Q _hQ
  have hcoeff : (R.block k).coeff Q = 0 := by
    by_contra hne
    exact hnone ⟨Q, hne⟩
  simp [hcoeff, Real.zero_rpow hp_pos.ne']

/--
Finite weighted sums of concrete represented functions have finite-cost
representations, with the expected triangle-inequality cost bound.

This is the purely algebraic assembly step.  The later non-Archimedean
estimate has to improve this crude finite-sum bound by using local overlap
information level by level.
-/
theorem exists_finset_weighted_sum_representation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Γ : Finset ℕ) (Θ : ℕ → ℝ) (f : ℕ → α → ℂ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (f i)
        (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hFin : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i)) :
    ∃ Y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (Y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          (Y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          ∑ i ∈ Γ, |Θ i| *
            WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R i) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  induction Γ using Finset.induction_on with
  | empty =>
      let Y : WeakGridSpace.BesovishSpace A q :=
        ⟨0, WeakGridSpace.memBesovishCoeffCost_zero (A := A) (q := q)⟩
      let S : WeakGridSpace.LpGridRepresentation A
          (Y : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.LpGridRepresentation A
          (0 : Lp ℂ p G.toWeakGridSpace.measure)
        exact WeakGridSpace.LpGridRepresentation.zero A
      refine ⟨Y, S, ?_, ?_, ?_⟩
      · change WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) (fun _ => (0 : ℂ))
          (0 : Lp ℂ p G.toWeakGridSpace.measure)
        simpa [WeakGridSpace.RepresentsFunction] using
          (Lp.coeFn_zero ℂ p G.toWeakGridSpace.measure)
      · change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
          (WeakGridSpace.LpGridRepresentation.zero A)
        exact zero_representation_finitePQCost A
      · change WeakGridSpace.LpGridRepresentation.pqCost (q := q)
            (WeakGridSpace.LpGridRepresentation.zero A) ≤ 0
        rw [zero_representation_pqCost_eq_zero A]
  | insert a Γ ha ih =>
      have hRep_rest : ∀ i ∈ Γ,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) (f i)
            (y i : Lp ℂ p G.toWeakGridSpace.measure) := by
        intro i hi
        exact hRep i (Finset.mem_insert_of_mem hi)
      have hFin_rest : ∀ i ∈ Γ,
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i) := by
        intro i hi
        exact hFin i (Finset.mem_insert_of_mem hi)
      rcases ih hRep_rest hFin_rest with ⟨Yrest, Srest, hRepS, hFinS, hCostS⟩
      let Yscaled : WeakGridSpace.BesovishSpace A q := (Θ a : ℂ) • y a
      let Rscaled : WeakGridSpace.LpGridRepresentation A
          (Yscaled : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.LpGridRepresentation A
          ((Θ a : ℂ) • (y a : Lp ℂ p G.toWeakGridSpace.measure))
        exact WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)
      let Ysum : WeakGridSpace.BesovishSpace A q := Yscaled + Yrest
      let Ssum : WeakGridSpace.LpGridRepresentation A
          (Ysum : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.LpGridRepresentation A
          ((Yscaled : Lp ℂ p G.toWeakGridSpace.measure) +
            (Yrest : Lp ℂ p G.toWeakGridSpace.measure))
        exact WeakGridSpace.LpGridRepresentation.add Rscaled Srest
      have hRepScaled :
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => (Θ a : ℂ) * f a z)
            (Yscaled : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => (Θ a : ℂ) * f a z)
          ((Θ a : ℂ) • (y a : Lp ℂ p G.toWeakGridSpace.measure))
        exact WeakGridSpace.representsFunction_smul (G := G.toWeakGridSpace)
          (p := p) (Θ a : ℂ) (hRep a (Finset.mem_insert_self a Γ))
      have hRepSum :
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => (Θ a : ℂ) * f a z +
              ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
            (Ysum : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => (Θ a : ℂ) * f a z +
            ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          ((Yscaled : Lp ℂ p G.toWeakGridSpace.measure) +
            (Yrest : Lp ℂ p G.toWeakGridSpace.measure))
        exact (Lp.coeFn_add
          (Yscaled : Lp ℂ p G.toWeakGridSpace.measure)
          (Yrest : Lp ℂ p G.toWeakGridSpace.measure)).trans
          (hRepScaled.add hRepS)
      have hFinScaled :
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rscaled := by
        change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
          (WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a))
        exact WeakGridSpace.LpGridRepresentation.smul_finitePQCost
          (A := A) (q := q) (Θ a : ℂ)
          (hFin a (Finset.mem_insert_self a Γ))
      have hFinSum :
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Ssum := by
        change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
          (WeakGridSpace.LpGridRepresentation.add Rscaled Srest)
        exact WeakGridSpace.LpGridRepresentation.add_finitePQCost
          Rscaled Srest hp_top Fact.out hFinScaled hFinS
      have hCostScaled :
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rscaled =
            |Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a) := by
        change WeakGridSpace.LpGridRepresentation.pqCost (q := q)
            (WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)) =
          |Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a)
        rw [WeakGridSpace.LpGridRepresentation.pqCost_smul
          (A := A) (q := q) (Θ a : ℂ) (R a) hp_top Fact.out
          (hFin a (Finset.mem_insert_self a Γ))]
        simp
      have hCostSum :
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Ssum ≤
            |Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a) +
              ∑ i ∈ Γ, |Θ i| *
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R i) := by
        change WeakGridSpace.LpGridRepresentation.pqCost (q := q)
            (WeakGridSpace.LpGridRepresentation.add Rscaled Srest) ≤ _
        calc
          WeakGridSpace.LpGridRepresentation.pqCost (q := q)
              (WeakGridSpace.LpGridRepresentation.add Rscaled Srest)
              ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rscaled +
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) Srest :=
            WeakGridSpace.LpGridRepresentation.pqCost_triangle
              Rscaled Srest hp_top Fact.out hFinScaled hFinS
          _ = |Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a) +
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) Srest := by
            rw [hCostScaled]
          _ ≤ |Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a) +
              ∑ i ∈ Γ, |Θ i| *
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R i) :=
            by
              have h := add_le_add_left hCostS
                (|Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a))
              simpa [add_comm, add_left_comm, add_assoc] using h
      refine ⟨Ysum, Ssum, ?_, hFinSum, ?_⟩
      · simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc]
          using hRepSum
      · simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc]
          using hCostSum

/--
Finite weighted sums also preserve coefficient support in the expected weak
sense: every nonzero coefficient of the assembled representation comes from
one of the active summands.

This is the algebraic support-transfer companion to
`exists_finset_weighted_sum_representation`.  The sharp non-Archimedean
regular-domain estimate still has to use the regular-domain product blocks,
but this lemma isolates the finite-sum bookkeeping.
-/
theorem exists_finset_weighted_sum_representation_support
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Γ : Finset ℕ) (Θ : ℕ → ℝ) (f : ℕ → α → ℂ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (P : (i : ℕ) → (k : ℕ) →
      WeakGridSpace.LevelCell G.toWeakGridSpace k → Prop)
    (hRep : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (f i)
        (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hFin : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i))
    (hSupp : ∀ i ∈ Γ, ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ((R i).block k).coeff Q ≠ 0 → P i k Q) :
    ∃ Y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (Y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          (Y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          ∑ i ∈ Γ, |Θ i| *
            WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R i) ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 → ∃ i ∈ Γ, P i k Q) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  induction Γ using Finset.induction_on with
  | empty =>
      let Y : WeakGridSpace.BesovishSpace A q :=
        ⟨0, WeakGridSpace.memBesovishCoeffCost_zero (A := A) (q := q)⟩
      let S : WeakGridSpace.LpGridRepresentation A
          (Y : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.LpGridRepresentation A
          (0 : Lp ℂ p G.toWeakGridSpace.measure)
        exact WeakGridSpace.LpGridRepresentation.zero A
      refine ⟨Y, S, ?_, ?_, ?_, ?_⟩
      · change WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) (fun _ => (0 : ℂ))
          (0 : Lp ℂ p G.toWeakGridSpace.measure)
        simpa [WeakGridSpace.RepresentsFunction] using
          (Lp.coeFn_zero ℂ p G.toWeakGridSpace.measure)
      · change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
          (WeakGridSpace.LpGridRepresentation.zero A)
        exact zero_representation_finitePQCost A
      · change WeakGridSpace.LpGridRepresentation.pqCost (q := q)
            (WeakGridSpace.LpGridRepresentation.zero A) ≤ 0
        rw [zero_representation_pqCost_eq_zero A]
      · intro k Q hcoeff
        exact False.elim (hcoeff (by simp [S, WeakGridSpace.LpGridRepresentation.zero,
          WeakGridSpace.LevelBlock.zero]))
  | insert a Γ ha ih =>
      have hRep_rest : ∀ i ∈ Γ,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) (f i)
            (y i : Lp ℂ p G.toWeakGridSpace.measure) := by
        intro i hi
        exact hRep i (Finset.mem_insert_of_mem hi)
      have hFin_rest : ∀ i ∈ Γ,
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i) := by
        intro i hi
        exact hFin i (Finset.mem_insert_of_mem hi)
      have hSupp_rest : ∀ i ∈ Γ,
          ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            ((R i).block k).coeff Q ≠ 0 → P i k Q := by
        intro i hi k Q hcoeff
        exact hSupp i (Finset.mem_insert_of_mem hi) k Q hcoeff
      rcases ih hRep_rest hFin_rest hSupp_rest with
        ⟨Yrest, Srest, hRepS, hFinS, hCostS, hSuppS⟩
      let Yscaled : WeakGridSpace.BesovishSpace A q := (Θ a : ℂ) • y a
      let Rscaled : WeakGridSpace.LpGridRepresentation A
          (Yscaled : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.LpGridRepresentation A
          ((Θ a : ℂ) • (y a : Lp ℂ p G.toWeakGridSpace.measure))
        exact WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)
      let Ysum : WeakGridSpace.BesovishSpace A q := Yscaled + Yrest
      let Ssum : WeakGridSpace.LpGridRepresentation A
          (Ysum : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.LpGridRepresentation A
          ((Yscaled : Lp ℂ p G.toWeakGridSpace.measure) +
            (Yrest : Lp ℂ p G.toWeakGridSpace.measure))
        exact WeakGridSpace.LpGridRepresentation.add Rscaled Srest
      have hRepScaled :
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => (Θ a : ℂ) * f a z)
            (Yscaled : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => (Θ a : ℂ) * f a z)
          ((Θ a : ℂ) • (y a : Lp ℂ p G.toWeakGridSpace.measure))
        exact WeakGridSpace.representsFunction_smul (G := G.toWeakGridSpace)
          (p := p) (Θ a : ℂ) (hRep a (Finset.mem_insert_self a Γ))
      have hRepSum :
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => (Θ a : ℂ) * f a z +
              ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
            (Ysum : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => (Θ a : ℂ) * f a z +
            ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          ((Yscaled : Lp ℂ p G.toWeakGridSpace.measure) +
            (Yrest : Lp ℂ p G.toWeakGridSpace.measure))
        exact (Lp.coeFn_add
          (Yscaled : Lp ℂ p G.toWeakGridSpace.measure)
          (Yrest : Lp ℂ p G.toWeakGridSpace.measure)).trans
          (hRepScaled.add hRepS)
      have hFinScaled :
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rscaled := by
        change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
          (WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a))
        exact WeakGridSpace.LpGridRepresentation.smul_finitePQCost
          (A := A) (q := q) (Θ a : ℂ)
          (hFin a (Finset.mem_insert_self a Γ))
      have hFinSum :
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Ssum := by
        change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
          (WeakGridSpace.LpGridRepresentation.add Rscaled Srest)
        exact WeakGridSpace.LpGridRepresentation.add_finitePQCost
          Rscaled Srest hp_top Fact.out hFinScaled hFinS
      have hCostScaled :
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rscaled =
            |Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a) := by
        change WeakGridSpace.LpGridRepresentation.pqCost (q := q)
            (WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)) =
          |Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a)
        rw [WeakGridSpace.LpGridRepresentation.pqCost_smul
          (A := A) (q := q) (Θ a : ℂ) (R a) hp_top Fact.out
          (hFin a (Finset.mem_insert_self a Γ))]
        simp
      have hCostSum :
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Ssum ≤
            |Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a) +
              ∑ i ∈ Γ, |Θ i| *
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R i) := by
        change WeakGridSpace.LpGridRepresentation.pqCost (q := q)
            (WeakGridSpace.LpGridRepresentation.add Rscaled Srest) ≤ _
        calc
          WeakGridSpace.LpGridRepresentation.pqCost (q := q)
              (WeakGridSpace.LpGridRepresentation.add Rscaled Srest)
              ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rscaled +
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) Srest :=
            WeakGridSpace.LpGridRepresentation.pqCost_triangle
              Rscaled Srest hp_top Fact.out hFinScaled hFinS
          _ = |Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a) +
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) Srest := by
            rw [hCostScaled]
          _ ≤ |Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a) +
              ∑ i ∈ Γ, |Θ i| *
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R i) :=
            by
              have h := add_le_add_left hCostS
                (|Θ a| * WeakGridSpace.LpGridRepresentation.pqCost (q := q) (R a))
              simpa [add_comm, add_left_comm, add_assoc] using h
      have hSuppSum :
          ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            (Ssum.block k).coeff Q ≠ 0 → ∃ i ∈ insert a Γ, P i k Q := by
        intro k Q hcoeff
        have hsource :
            (Rscaled.block k).coeff Q ≠ 0 ∨ (Srest.block k).coeff Q ≠ 0 := by
          exact WeakGridSpace.LpGridRepresentation.add_coeff_ne_zero
            Rscaled Srest Q hcoeff
        rcases hsource with hscaled | hrest
        · have hscaled' :
              ((WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)).block k).coeff Q
                ≠ 0 := by
            change
              ((WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)).block k).coeff Q
                ≠ 0
            exact hscaled
          have horig :
              ((R a).block k).coeff Q ≠ 0 :=
            lpGridRepresentation_smul_coeff_ne_zero
              (G' := G.toWeakGridSpace) (s' := s) (p' := p)
              (u' := ∞) (A := A)
              (g := (y a : Lp ℂ p G.toWeakGridSpace.measure))
              (Θ a : ℂ) (R a) Q hscaled'
          refine ⟨a, Finset.mem_insert_self a Γ, ?_⟩
          exact hSupp a (Finset.mem_insert_self a Γ) k Q horig
        · rcases hSuppS k Q hrest with ⟨i, hi, hPi⟩
          exact ⟨i, Finset.mem_insert_of_mem hi, hPi⟩
      refine ⟨Ysum, Ssum, ?_, hFinSum, ?_, ?_⟩
      · simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc]
          using hRepSum
      · simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc]
          using hCostSum
      · simpa using hSuppSum

/--
Finite weighted sums with disjoint coefficient supports have exact level
coefficient power: at every level, the output power is the sum of the scaled
input powers.

The support-source conclusion says that every nonzero output coefficient
actually comes from a nonzero coefficient of one active input representation.
-/
theorem exists_finset_weighted_sum_representation_disjoint_levelCoeffPower
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Γ : Finset ℕ) (Θ : ℕ → ℝ) (f : ℕ → α → ℂ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (f i)
        (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hFin : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i))
    (hDisj : ∀ i ∈ Γ, ∀ l ∈ Γ, i ≠ l →
      ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        ((R i).block k).coeff Q ≠ 0 → ((R l).block k).coeff Q = 0) :
    ∃ Y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (Y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          (Y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        (∀ k,
          S.levelCoeffPower k =
            ∑ i ∈ Γ, ‖(Θ i : ℂ)‖ ^ p.toReal *
              (R i).levelCoeffPower k) ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 →
            ∃ i ∈ Γ, ((R i).block k).coeff Q ≠ 0) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  induction Γ using Finset.induction_on with
  | empty =>
      let Y : WeakGridSpace.BesovishSpace A q :=
        ⟨0, WeakGridSpace.memBesovishCoeffCost_zero (A := A) (q := q)⟩
      let S : WeakGridSpace.LpGridRepresentation A
          (Y : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.LpGridRepresentation A
          (0 : Lp ℂ p G.toWeakGridSpace.measure)
        exact WeakGridSpace.LpGridRepresentation.zero A
      refine ⟨Y, S, ?_, ?_, ?_, ?_⟩
      · change WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) (fun _ => (0 : ℂ))
          (0 : Lp ℂ p G.toWeakGridSpace.measure)
        simpa [WeakGridSpace.RepresentsFunction] using
          (Lp.coeFn_zero ℂ p G.toWeakGridSpace.measure)
      · change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
          (WeakGridSpace.LpGridRepresentation.zero A)
        exact zero_representation_finitePQCost A
      · intro k
        change (WeakGridSpace.LpGridRepresentation.zero A).levelCoeffPower k = 0
        simp [WeakGridSpace.LpGridRepresentation.zero_levelCoeffPower]
      · intro k Q hcoeff
        exact False.elim (hcoeff (by simp [S, WeakGridSpace.LpGridRepresentation.zero,
          WeakGridSpace.LevelBlock.zero]))
  | insert a Γ ha ih =>
      have hRep_rest : ∀ i ∈ Γ,
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p) (f i)
            (y i : Lp ℂ p G.toWeakGridSpace.measure) := by
        intro i hi
        exact hRep i (Finset.mem_insert_of_mem hi)
      have hFin_rest : ∀ i ∈ Γ,
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i) := by
        intro i hi
        exact hFin i (Finset.mem_insert_of_mem hi)
      have hDisj_rest : ∀ i ∈ Γ, ∀ l ∈ Γ, i ≠ l →
          ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            ((R i).block k).coeff Q ≠ 0 → ((R l).block k).coeff Q = 0 := by
        intro i hi l hl hil k Q hcoeff
        exact hDisj i (Finset.mem_insert_of_mem hi) l
          (Finset.mem_insert_of_mem hl) hil k Q hcoeff
      rcases ih hRep_rest hFin_rest hDisj_rest with
        ⟨Yrest, Srest, hRepS, hFinS, hLevelS, hSuppS⟩
      let Yscaled : WeakGridSpace.BesovishSpace A q := (Θ a : ℂ) • y a
      let Rscaled : WeakGridSpace.LpGridRepresentation A
          (Yscaled : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.LpGridRepresentation A
          ((Θ a : ℂ) • (y a : Lp ℂ p G.toWeakGridSpace.measure))
        exact WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)
      let Ysum : WeakGridSpace.BesovishSpace A q := Yscaled + Yrest
      let Ssum : WeakGridSpace.LpGridRepresentation A
          (Ysum : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.LpGridRepresentation A
          ((Yscaled : Lp ℂ p G.toWeakGridSpace.measure) +
            (Yrest : Lp ℂ p G.toWeakGridSpace.measure))
        exact WeakGridSpace.LpGridRepresentation.add Rscaled Srest
      have hRepScaled :
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => (Θ a : ℂ) * f a z)
            (Yscaled : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => (Θ a : ℂ) * f a z)
          ((Θ a : ℂ) • (y a : Lp ℂ p G.toWeakGridSpace.measure))
        exact WeakGridSpace.representsFunction_smul (G := G.toWeakGridSpace)
          (p := p) (Θ a : ℂ) (hRep a (Finset.mem_insert_self a Γ))
      have hRepSum :
          WeakGridSpace.RepresentsFunction
            (G := G.toWeakGridSpace) (p := p)
            (fun z => (Θ a : ℂ) * f a z +
              ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
            (Ysum : Lp ℂ p G.toWeakGridSpace.measure) := by
        change WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => (Θ a : ℂ) * f a z +
            ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          ((Yscaled : Lp ℂ p G.toWeakGridSpace.measure) +
            (Yrest : Lp ℂ p G.toWeakGridSpace.measure))
        exact (Lp.coeFn_add
          (Yscaled : Lp ℂ p G.toWeakGridSpace.measure)
          (Yrest : Lp ℂ p G.toWeakGridSpace.measure)).trans
          (hRepScaled.add hRepS)
      have hFinScaled :
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rscaled := by
        change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
          (WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a))
        exact WeakGridSpace.LpGridRepresentation.smul_finitePQCost
          (A := A) (q := q) (Θ a : ℂ)
          (hFin a (Finset.mem_insert_self a Γ))
      have hFinSum :
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Ssum := by
        change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
          (WeakGridSpace.LpGridRepresentation.add Rscaled Srest)
        exact WeakGridSpace.LpGridRepresentation.add_finitePQCost
          Rscaled Srest hp_top Fact.out hFinScaled hFinS
      have hLevelSum : ∀ k,
          Ssum.levelCoeffPower k =
            ∑ i ∈ insert a Γ, ‖(Θ i : ℂ)‖ ^ p.toReal *
              (R i).levelCoeffPower k := by
        intro k
        have hdisj_scaled_rest :
            ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              (Rscaled.block k).coeff Q ≠ 0 → (Srest.block k).coeff Q = 0 := by
          intro Q hscaled
          have hscaled' :
              ((WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)).block k).coeff Q
                ≠ 0 := by
            change
              ((WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)).block k).coeff Q
                ≠ 0
            exact hscaled
          have ha_coeff : ((R a).block k).coeff Q ≠ 0 :=
            lpGridRepresentation_smul_coeff_ne_zero
              (G' := G.toWeakGridSpace) (s' := s) (p' := p) (u' := ∞)
              (A := A) (g := (y a : Lp ℂ p G.toWeakGridSpace.measure))
              (Θ a : ℂ) (R a) Q hscaled'
          by_contra hSrest_ne
          rcases hSuppS k Q hSrest_ne with ⟨i, hi, hi_coeff⟩
          have hai : a ≠ i := by
            intro hai
            subst hai
            exact ha hi
          have hi_zero : ((R i).block k).coeff Q = 0 :=
            hDisj a (Finset.mem_insert_self a Γ) i
              (Finset.mem_insert_of_mem hi) hai k Q ha_coeff
          exact hi_coeff hi_zero
        have hadd_level :
            Ssum.levelCoeffPower k =
              Rscaled.levelCoeffPower k + Srest.levelCoeffPower k := by
          change
            (WeakGridSpace.LpGridRepresentation.add Rscaled Srest).levelCoeffPower k =
              Rscaled.levelCoeffPower k + Srest.levelCoeffPower k
          exact lpGridRepresentation_add_levelCoeffPower_eq_of_disjoint_support
            Rscaled Srest k hdisj_scaled_rest
        have hscaled_level :
            Rscaled.levelCoeffPower k =
              ‖(Θ a : ℂ)‖ ^ p.toReal * (R a).levelCoeffPower k := by
          change
            (WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)).levelCoeffPower k =
              ‖(Θ a : ℂ)‖ ^ p.toReal * (R a).levelCoeffPower k
          exact lpGridRepresentation_smul_levelCoeffPower
            (G' := G.toWeakGridSpace) (s' := s) (p' := p) (u' := ∞)
            (A := A) (g := (y a : Lp ℂ p G.toWeakGridSpace.measure))
            (Θ a : ℂ) (R a) k
        calc
          Ssum.levelCoeffPower k
              = Rscaled.levelCoeffPower k + Srest.levelCoeffPower k := hadd_level
          _ = ‖(Θ a : ℂ)‖ ^ p.toReal * (R a).levelCoeffPower k +
                ∑ i ∈ Γ, ‖(Θ i : ℂ)‖ ^ p.toReal *
                  (R i).levelCoeffPower k := by
              rw [hscaled_level, hLevelS k]
          _ = ∑ i ∈ insert a Γ, ‖(Θ i : ℂ)‖ ^ p.toReal *
                (R i).levelCoeffPower k := by
              rw [Finset.sum_insert ha]
      have hSuppSum :
          ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            (Ssum.block k).coeff Q ≠ 0 →
              ∃ i ∈ insert a Γ, ((R i).block k).coeff Q ≠ 0 := by
        intro k Q hcoeff
        have hsource :
            (Rscaled.block k).coeff Q ≠ 0 ∨ (Srest.block k).coeff Q ≠ 0 :=
          WeakGridSpace.LpGridRepresentation.add_coeff_ne_zero
            Rscaled Srest Q hcoeff
        rcases hsource with hscaled | hrest
        · have hscaled' :
              ((WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)).block k).coeff Q
                ≠ 0 := by
            change
              ((WeakGridSpace.LpGridRepresentation.smul (Θ a : ℂ) (R a)).block k).coeff Q
                ≠ 0
            exact hscaled
          have horig : ((R a).block k).coeff Q ≠ 0 :=
            lpGridRepresentation_smul_coeff_ne_zero
              (G' := G.toWeakGridSpace) (s' := s) (p' := p) (u' := ∞)
              (A := A) (g := (y a : Lp ℂ p G.toWeakGridSpace.measure))
              (Θ a : ℂ) (R a) Q hscaled'
          exact ⟨a, Finset.mem_insert_self a Γ, horig⟩
        · rcases hSuppS k Q hrest with ⟨i, hi, hRi⟩
          exact ⟨i, Finset.mem_insert_of_mem hi, hRi⟩
      refine ⟨Ysum, Ssum, ?_, hFinSum, ?_, ?_⟩
      · simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc]
          using hRepSum
      · exact hLevelSum
      · exact hSuppSum

/--
Finite weighted sums localized in pairwise disjoint members of a regular
family have exact level coefficient power.  This packages the abstract
disjoint-support lemma with the geometric disjointness of regular families.
-/
theorem exists_finset_weighted_sum_regularFamily_levelCoeffPower
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (p q : ℝ≥0∞) {a C c : ℝ}
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω a C c)
    (Γ : Finset ℕ) (hΓΛ : ∀ i ∈ Γ, i ∈ Λ)
    (Θ : ℕ → ℝ) (f : ℕ → α → ℂ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (f i)
        (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hFin : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i))
    (hSuppDomain : ∀ i ∈ Γ, ∀ k
      (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        ((R i).block k).coeff Q ≠ 0 → Q.1 ⊆ Ω i) :
    ∃ Y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (Y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          (Y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        (∀ k,
          S.levelCoeffPower k =
            ∑ i ∈ Γ, ‖(Θ i : ℂ)‖ ^ p.toReal *
              (R i).levelCoeffPower k) ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 → ∃ i ∈ Γ, Q.1 ⊆ Ω i) := by
  classical
  have hDisj : ∀ i ∈ Γ, ∀ l ∈ Γ, i ≠ l →
      ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        ((R i).block k).coeff Q ≠ 0 → ((R l).block k).coeff Q = 0 := by
    intro i hi l hl hil k Q hiQ
    by_contra hlQ
    have hQi : Q.1 ⊆ Ω i := hSuppDomain i hi k Q hiQ
    have hQl : Q.1 ⊆ Ω l := hSuppDomain l hl k Q hlQ
    have heq : i = l :=
      regularFamily_unique_index_of_levelCell_subset
        G Λ Ω hΩ Q (hΓΛ i hi) (hΓΛ l hl) hQi hQl
    exact hil heq
  obtain ⟨Y, S, hRepS, hFinS, hLevelS, hSuppS⟩ :=
    exists_finset_weighted_sum_representation_disjoint_levelCoeffPower
      G s p q hs hp hp_top Γ Θ f y R hRep hFin hDisj
  refine ⟨Y, S, hRepS, hFinS, hLevelS, ?_⟩
  intro k Q hcoeff
  rcases hSuppS k Q hcoeff with ⟨i, hi, hiQ⟩
  exact ⟨i, hi, hSuppDomain i hi k Q hiQ⟩

/--
Finite weighted level powers are bounded by `N ^ p` times the unweighted level
power whenever every active weight has norm at most `N`.
-/
theorem finset_weighted_levelCoeffPower_le_of_weight_bound
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {Γ : Finset ℕ} {Θ : ℕ → ℝ} {N : ℝ}
    (a : ℕ → ℝ) (ha0 : ∀ i ∈ Γ, 0 ≤ a i)
    (hΘ : ∀ i ∈ Γ, ‖(Θ i : ℂ)‖ ≤ N) :
    (∑ i ∈ Γ, ‖(Θ i : ℂ)‖ ^ p.toReal * a i) ≤
      N ^ p.toReal * ∑ i ∈ Γ, a i := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hweight_nonneg : 0 ≤ ‖(Θ i : ℂ)‖ := norm_nonneg _
  have hpow_le : ‖(Θ i : ℂ)‖ ^ p.toReal ≤ N ^ p.toReal :=
    Real.rpow_le_rpow hweight_nonneg (hΘ i hi) hp_pos.le
  exact mul_le_mul_of_nonneg_right hpow_le (ha0 i hi)

/--
Finite weighted level powers only need a weight bound on the nonzero support of
the level data.

This is the form used by the non-Archimedean localization argument: a domain
whose product representation has no coefficient at a fixed level contributes
nothing at that level, so its weight does not need to be controlled there.
-/
theorem finset_weighted_levelCoeffPower_le_of_weight_bound_on_support
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {Γ : Finset ℕ} {Θ : ℕ → ℝ} {N : ℝ}
    (a : ℕ → ℝ) (ha0 : ∀ i ∈ Γ, 0 ≤ a i)
    (hΘ : ∀ i ∈ Γ, a i ≠ 0 → ‖(Θ i : ℂ)‖ ≤ N) :
    (∑ i ∈ Γ, ‖(Θ i : ℂ)‖ ^ p.toReal * a i) ≤
      N ^ p.toReal * ∑ i ∈ Γ, a i := by
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases hai : a i = 0
  · simp [hai]
  · have hweight_nonneg : 0 ≤ ‖(Θ i : ℂ)‖ := norm_nonneg _
    have hpow_le : ‖(Θ i : ℂ)‖ ^ p.toReal ≤ N ^ p.toReal :=
      Real.rpow_le_rpow hweight_nonneg (hΘ i hi hai) hp_pos.le
    exact mul_le_mul_of_nonneg_right hpow_le (ha0 i hi)

/-- Raising to `1/e` and then to `e` returns a nonnegative real. -/
theorem rpow_one_div_rpow_eq_self {x e : ℝ} (hx : 0 ≤ x) (he : e ≠ 0) :
    (x ^ (1 / e)) ^ e = x := by
  rw [← Real.rpow_mul hx]
  field_simp [he]
  rw [Real.rpow_one]

/-- Raising to `e` and then to `1/e` returns a nonnegative real. -/
theorem rpow_rpow_one_div_eq_self {x e : ℝ} (hx : 0 ≤ x) (he : e ≠ 0) :
    (x ^ e) ^ (1 / e) = x := by
  rw [← Real.rpow_mul hx]
  field_simp [he]
  rw [Real.rpow_one]

/--
If every level coefficient power of `S` is bounded by `N ^ p` times the
corresponding level power of `R`, then the `(p,q)` coefficient cost of `S` is
bounded by `N` times that of `R`.
-/
theorem pqCost_le_mul_of_levelCoeffPower_le
    {G' : WeakGridSpace.WeakGridSpace (α := α)} {s' : ℝ} {p' u' q' : ℝ≥0∞}
    [Fact (1 ≤ p')] [Fact (1 ≤ q')]
    {A : WeakGridSpace.AtomFamily G' s' p' u'}
    {g h : Lp ℂ p' G'.measure}
    (R : WeakGridSpace.LpGridRepresentation A g)
    (S : WeakGridSpace.LpGridRepresentation A h)
    {N : ℝ} (hN0 : 0 ≤ N)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q') R)
    (hSfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q') S)
    (hlevel : ∀ k, S.levelCoeffPower k ≤ N ^ p'.toReal * R.levelCoeffPower k) :
    WeakGridSpace.LpGridRepresentation.pqCost (q := q') S ≤
      N * WeakGridSpace.LpGridRepresentation.pqCost (q := q') R := by
  classical
  have hp_pos : 0 < p'.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p')).ne' A.p_ne_top
  have hp_ne : p'.toReal ≠ 0 := hp_pos.ne'
  have hNpow0 : 0 ≤ N ^ p'.toReal := Real.rpow_nonneg hN0 _
  have hroot_level : ∀ k,
      (S.levelCoeffPower k) ^ (1 / p'.toReal) ≤
        N * (R.levelCoeffPower k) ^ (1 / p'.toReal) := by
    intro k
    have hS0 : 0 ≤ S.levelCoeffPower k := S.levelCoeffPower_nonneg k
    have hR0 : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
    calc
      (S.levelCoeffPower k) ^ (1 / p'.toReal)
          ≤ (N ^ p'.toReal * R.levelCoeffPower k) ^ (1 / p'.toReal) :=
        Real.rpow_le_rpow hS0 (hlevel k) (one_div_nonneg.mpr hp_pos.le)
      _ = N * (R.levelCoeffPower k) ^ (1 / p'.toReal) := by
        rw [Real.mul_rpow hNpow0 hR0,
          rpow_rpow_one_div_eq_self hN0 hp_ne]
  by_cases hqtop : q' = ∞
  · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos hqtop]
    rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos hqtop]
    have hbddS : BddAbove
        (Set.range fun k => (S.levelCoeffPower k) ^ (1 / p'.toReal)) := by
      simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hSfin
    have hcostR_bdd : BddAbove
        (Set.range fun k => (R.levelCoeffPower k) ^ (1 / p'.toReal)) := by
      simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hRfin
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨k, rfl⟩
    exact (hroot_level k).trans
      (mul_le_mul_of_nonneg_left
        (le_csSup hcostR_bdd ⟨k, rfl⟩) hN0)
  · have hq_pos : 0 < q'.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q')).ne' hqtop
    have hq_ne : q'.toReal ≠ 0 := hq_pos.ne'
    rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hqtop]
    rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hqtop]
    have hSsum : Summable fun k => (S.levelCoeffPower k) ^ (q'.toReal / p'.toReal) := by
      simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hSfin
    have hRsum : Summable fun k => (R.levelCoeffPower k) ^ (q'.toReal / p'.toReal) := by
      simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hRfin
    have hterm_le : ∀ k,
        (S.levelCoeffPower k) ^ (q'.toReal / p'.toReal) ≤
          N ^ q'.toReal * (R.levelCoeffPower k) ^ (q'.toReal / p'.toReal) := by
      intro k
      have hS0 : 0 ≤ S.levelCoeffPower k := S.levelCoeffPower_nonneg k
      have hR0 : 0 ≤ R.levelCoeffPower k := R.levelCoeffPower_nonneg k
      have hleft :
          (S.levelCoeffPower k) ^ (q'.toReal / p'.toReal) =
            ((S.levelCoeffPower k) ^ (1 / p'.toReal)) ^ q'.toReal := by
        rw [← Real.rpow_mul hS0]
        congr 1
        field_simp [hp_ne]
      have hright :
          N ^ q'.toReal * (R.levelCoeffPower k) ^ (q'.toReal / p'.toReal) =
            (N * (R.levelCoeffPower k) ^ (1 / p'.toReal)) ^ q'.toReal := by
        rw [Real.mul_rpow hN0 (Real.rpow_nonneg hR0 _)]
        congr 1
        rw [← Real.rpow_mul hR0]
        congr 1
        field_simp [hp_ne]
      rw [hleft, hright]
      exact Real.rpow_le_rpow
        (Real.rpow_nonneg hS0 _) (hroot_level k) hq_pos.le
    have htsum_le :
        (∑' k, (S.levelCoeffPower k) ^ (q'.toReal / p'.toReal)) ≤
          ∑' k, N ^ q'.toReal *
            (R.levelCoeffPower k) ^ (q'.toReal / p'.toReal) := by
      exact hSsum.tsum_le_tsum hterm_le (hRsum.mul_left _)
    have hsum_scaled :
        (∑' k, N ^ q'.toReal *
            (R.levelCoeffPower k) ^ (q'.toReal / p'.toReal)) =
          N ^ q'.toReal *
            ∑' k, (R.levelCoeffPower k) ^ (q'.toReal / p'.toReal) := by
      rw [tsum_mul_left]
    calc
      (∑' k, (S.levelCoeffPower k) ^ (q'.toReal / p'.toReal)) ^
          (1 / q'.toReal)
          ≤ (∑' k, N ^ q'.toReal *
            (R.levelCoeffPower k) ^ (q'.toReal / p'.toReal)) ^
              (1 / q'.toReal) :=
        Real.rpow_le_rpow
          (tsum_nonneg fun k => Real.rpow_nonneg (S.levelCoeffPower_nonneg k) _)
          htsum_le (one_div_nonneg.mpr hq_pos.le)
      _ = (N ^ q'.toReal *
            ∑' k, (R.levelCoeffPower k) ^ (q'.toReal / p'.toReal)) ^
              (1 / q'.toReal) := by
        rw [hsum_scaled]
      _ = N *
            (∑' k, (R.levelCoeffPower k) ^ (q'.toReal / p'.toReal)) ^
              (1 / q'.toReal) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hN0 _)
          (tsum_nonneg fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _),
          rpow_rpow_one_div_eq_self hN0 hq_ne]

/-- Local public copy of the nonnegativity of the mixed regular-family level power. -/
theorem regularFamilyRestrictionLevelCoeffPower_nonneg_local
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ)
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
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

/-- The `tsum` of a function cut down to a finite set is its finite sum. -/
theorem tsum_finset_indicator_eq_sum (Γ : Finset ℕ) (a : ℕ → ℝ) :
    (∑' i : ℕ, Set.indicator ((Γ : Set ℕ)) a i) = ∑ i ∈ Γ, a i := by
  classical
  have hsum : HasSum (fun i : ℕ => Set.indicator ((Γ : Set ℕ)) a i)
      (∑ i ∈ Γ, Set.indicator ((Γ : Set ℕ)) a i) :=
    hasSum_sum_of_ne_finset_zero (s := Γ) (f := fun i : ℕ =>
      Set.indicator ((Γ : Set ℕ)) a i) (by
        intro i hi
        change Set.indicator ((Γ : Set ℕ)) a i = 0
        rw [Set.indicator_of_notMem]
        simpa using hi)
  rw [hsum.tsum_eq]
  exact Finset.sum_congr rfl fun i hi => by
    rw [Set.indicator_of_mem]
    simpa using hi

/--
For a finite index set, the mixed regular-family level power is the
corresponding finite sum of level powers.
-/
theorem regularFamilyRestrictionLevelCoeffPower_finset
    (G : GoodGridSpace (α := α)) (Γ : Finset ℕ)
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) →
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        ((y i : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q) :
          Lp ℂ p G.toWeakGridSpace.measure))
    (j : ℕ) :
    regularFamilyRestrictionLevelCoeffPower G s p q (Γ : Set ℕ) y R j =
      ∑ i ∈ Γ, (R i).levelCoeffPower j := by
  unfold regularFamilyRestrictionLevelCoeffPower
  rw [tsum_finset_indicator_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rfl

/--
For a finite regular subfamily, the unweighted localized sum has `pqCost`
exactly equal to the mixed regular-family restriction cost for that finite
index set.
-/
theorem exists_finset_unweighted_sum_regularFamily_pqCost_eq_restrictionCost
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (p q : ℝ≥0∞) {a C c : ℝ}
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω a C c)
    (Γ : Finset ℕ) (hΓΛ : ∀ i ∈ Γ, i ∈ Λ)
    (f : ℕ → α → ℂ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (f i)
        (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hFin : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i))
    (hSuppDomain : ∀ i ∈ Γ, ∀ k
      (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        ((R i).block k).coeff Q ≠ 0 → Q.1 ⊆ Ω i) :
    ∃ Y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (Y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ i ∈ Γ, f i z)
          (Y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        (∀ k,
          S.levelCoeffPower k =
            regularFamilyRestrictionLevelCoeffPower G s p q (Γ : Set ℕ) y R k) ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S =
          regularFamilyRestrictionCost G s p q (Γ : Set ℕ) y R := by
  classical
  let oneWeight : ℕ → ℝ := fun _ => 1
  obtain ⟨Y, S, hRepS, hFinS, hLevelS, _hSuppS⟩ :=
    exists_finset_weighted_sum_regularFamily_levelCoeffPower
      G Λ Ω s p q hs hp hp_top hΩ Γ hΓΛ oneWeight f y R
      (by
        intro i hi
        simpa using hRep i hi)
      hFin hSuppDomain
  have hLevel : ∀ k,
      S.levelCoeffPower k =
        regularFamilyRestrictionLevelCoeffPower G s p q (Γ : Set ℕ) y R k := by
    intro k
    calc
      S.levelCoeffPower k
          = ∑ i ∈ Γ, ‖((1 : ℝ) : ℂ)‖ ^ p.toReal *
              (R i).levelCoeffPower k := by
              simpa [oneWeight] using hLevelS k
      _ = ∑ i ∈ Γ, (R i).levelCoeffPower k := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp
      _ = regularFamilyRestrictionLevelCoeffPower G s p q (Γ : Set ℕ) y R k := by
              rw [regularFamilyRestrictionLevelCoeffPower_finset]
  have hCost :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S =
        regularFamilyRestrictionCost G s p q (Γ : Set ℕ) y R := by
    by_cases hqtop : q = ∞
    · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos hqtop]
      rw [regularFamilyRestrictionCost, if_pos hqtop]
      congr 1
      ext x
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, congrArg (fun t => t ^ (1 / p.toReal)) (hLevel k).symm⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, congrArg (fun t => t ^ (1 / p.toReal)) (hLevel k)⟩
    · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hqtop]
      rw [regularFamilyRestrictionCost, if_neg hqtop]
      congr 1
      apply tsum_congr
      intro k
      rw [hLevel k]
  refine ⟨Y, S, ?_, hFinS, hLevel, hCost⟩
  simpa [oneWeight] using hRepS

/--
Finite weighted regular-family sums satisfy the non-Archimedean `pqCost`
bound whenever the active weights are bounded by `N` on the finite subfamily.

This is the finite algebraic estimate: the weighted representation is compared
level by level with the unweighted mixed representation, whose cost is exactly
the finite regular-family restriction cost.
-/
theorem exists_finset_weighted_sum_regularFamily_pqCost_le
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (p q : ℝ≥0∞) {a C c : ℝ}
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω a C c)
    (Γ : Finset ℕ) (hΓΛ : ∀ i ∈ Γ, i ∈ Λ)
    (Θ : ℕ → ℝ) {N : ℝ} (hN0 : 0 ≤ N)
    (f : ℕ → α → ℂ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hWeight : ∀ i ∈ Γ, |Θ i| ≤ N)
    (hRep : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (f i)
        (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hFin : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i))
    (hSuppDomain : ∀ i ∈ Γ, ∀ k
      (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        ((R i).block k).coeff Q ≠ 0 → Q.1 ⊆ Ω i) :
    ∃ Y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (Y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          (Y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          N * regularFamilyRestrictionCost G s p q (Γ : Set ℕ) y R ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 → ∃ i ∈ Γ, Q.1 ⊆ Ω i) := by
  classical
  obtain ⟨Yw, Sw, hRepSw, hFinSw, hLevelSw, hSuppSw⟩ :=
    exists_finset_weighted_sum_regularFamily_levelCoeffPower
      G Λ Ω s p q hs hp hp_top hΩ Γ hΓΛ Θ f y R hRep hFin hSuppDomain
  obtain ⟨Yu, Su, _hRepSu, hFinSu, hLevelSu, hCostSu⟩ :=
    exists_finset_unweighted_sum_regularFamily_pqCost_eq_restrictionCost
      G Λ Ω s p q hs hp hp_top hΩ Γ hΓΛ f y R hRep hFin hSuppDomain
  have hLevelBound : ∀ k,
      Sw.levelCoeffPower k ≤ N ^ p.toReal * Su.levelCoeffPower k := by
    intro k
    calc
      Sw.levelCoeffPower k
          = ∑ i ∈ Γ, ‖(Θ i : ℂ)‖ ^ p.toReal *
              (R i).levelCoeffPower k := hLevelSw k
      _ ≤ N ^ p.toReal * ∑ i ∈ Γ, (R i).levelCoeffPower k := by
          exact finset_weighted_levelCoeffPower_le_of_weight_bound
            hp hp_top (fun i => (R i).levelCoeffPower k)
            (fun i _hi => (R i).levelCoeffPower_nonneg k)
            (fun i hi => by
              simpa [Complex.norm_real] using hWeight i hi)
      _ = N ^ p.toReal * Su.levelCoeffPower k := by
          rw [hLevelSu k]
          rw [regularFamilyRestrictionLevelCoeffPower_finset]
  have hCost :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Sw ≤
        N * regularFamilyRestrictionCost G s p q (Γ : Set ℕ) y R := by
    calc
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Sw
          ≤ N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Su :=
        pqCost_le_mul_of_levelCoeffPower_le
          Su Sw hN0 hFinSu hFinSw hLevelBound
      _ = N * regularFamilyRestrictionCost G s p q (Γ : Set ℕ) y R := by
          rw [hCostSu]
  exact ⟨Yw, Sw, hRepSw, hFinSw, hCost, hSuppSw⟩

/--
Finite weighted regular-family sums with a levelwise support weight bound.

This variant is tailored to the non-Archimedean proof.  At a fixed level `k`
we only ask for `|Θ i| ≤ N` when the `i`-th representation has nonzero
`levelCoeffPower k`; indices with zero level power do not affect the estimate.
-/
theorem exists_finset_weighted_sum_regularFamily_pqCost_le_of_level_weight_bound
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (p q : ℝ≥0∞) {a C c : ℝ}
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω a C c)
    (Γ : Finset ℕ) (hΓΛ : ∀ i ∈ Γ, i ∈ Λ)
    (Θ : ℕ → ℝ) {N : ℝ} (hN0 : 0 ≤ N)
    (f : ℕ → α → ℂ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hWeightLevel : ∀ i ∈ Γ, ∀ k,
      (R i).levelCoeffPower k ≠ 0 → |Θ i| ≤ N)
    (hRep : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (f i)
        (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hFin : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i))
    (hSuppDomain : ∀ i ∈ Γ, ∀ k
      (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        ((R i).block k).coeff Q ≠ 0 → Q.1 ⊆ Ω i) :
    ∃ Y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (Y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          (Y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          N * regularFamilyRestrictionCost G s p q (Γ : Set ℕ) y R ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 → ∃ i ∈ Γ, Q.1 ⊆ Ω i) := by
  classical
  obtain ⟨Yw, Sw, hRepSw, hFinSw, hLevelSw, hSuppSw⟩ :=
    exists_finset_weighted_sum_regularFamily_levelCoeffPower
      G Λ Ω s p q hs hp hp_top hΩ Γ hΓΛ Θ f y R hRep hFin hSuppDomain
  obtain ⟨Yu, Su, _hRepSu, hFinSu, hLevelSu, hCostSu⟩ :=
    exists_finset_unweighted_sum_regularFamily_pqCost_eq_restrictionCost
      G Λ Ω s p q hs hp hp_top hΩ Γ hΓΛ f y R hRep hFin hSuppDomain
  have hLevelBound : ∀ k,
      Sw.levelCoeffPower k ≤ N ^ p.toReal * Su.levelCoeffPower k := by
    intro k
    calc
      Sw.levelCoeffPower k
          = ∑ i ∈ Γ, ‖(Θ i : ℂ)‖ ^ p.toReal *
              (R i).levelCoeffPower k := hLevelSw k
      _ ≤ N ^ p.toReal * ∑ i ∈ Γ, (R i).levelCoeffPower k := by
          exact finset_weighted_levelCoeffPower_le_of_weight_bound_on_support
            hp hp_top (fun i => (R i).levelCoeffPower k)
            (fun i _hi => (R i).levelCoeffPower_nonneg k)
            (fun i hi hlevel_ne => by
              simpa [Complex.norm_real] using hWeightLevel i hi k hlevel_ne)
      _ = N ^ p.toReal * Su.levelCoeffPower k := by
          rw [hLevelSu k]
          rw [regularFamilyRestrictionLevelCoeffPower_finset]
  have hCost :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Sw ≤
        N * regularFamilyRestrictionCost G s p q (Γ : Set ℕ) y R := by
    calc
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Sw
          ≤ N * WeakGridSpace.LpGridRepresentation.pqCost (q := q) Su :=
        pqCost_le_mul_of_levelCoeffPower_le
          Su Sw hN0 hFinSu hFinSw hLevelBound
      _ = N * regularFamilyRestrictionCost G s p q (Γ : Set ℕ) y R := by
          rw [hCostSu]
  exact ⟨Yw, Sw, hRepSw, hFinSw, hCost, hSuppSw⟩

/-- Finite mixed `(p,q)` cost for a regular-family collection of representations. -/
def RegularFamilyRestrictionFiniteCost
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ)
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) →
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        ((y i : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q) :
          Lp ℂ p G.toWeakGridSpace.measure)) : Prop :=
  if q = ∞ then
    BddAbove (Set.range fun j : ℕ =>
      (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^ (1 / p.toReal))
  else
    Summable fun j : ℕ =>
      (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
        (q.toReal / p.toReal)

/--
Compare a single representation against a mixed regular-family coefficient
gauge.  If its level powers are bounded by `N ^ p` times the mixed level
powers, then its `pqCost` is bounded by `N` times the mixed restriction cost.
-/
theorem pqCost_le_mul_regularFamilyRestrictionCost_of_levelCoeffPower_le
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ)
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {hLp : Lp ℂ p G.toWeakGridSpace.measure}
    (S : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) hLp)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) →
      WeakGridSpace.LpGridRepresentation
        (souzaAtomFamily G s p hs hp hp_top)
        ((y i : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q) :
          Lp ℂ p G.toWeakGridSpace.measure))
    {N : ℝ} (hN0 : 0 ≤ N)
    (hSfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S)
    (hMixedFin : RegularFamilyRestrictionFiniteCost G Λ s p q hs hp hp_top y R)
    (hlevel : ∀ j,
      S.levelCoeffPower j ≤
        N ^ p.toReal * regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) :
    WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
      N * regularFamilyRestrictionCost G s p q Λ y R := by
  classical
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp_top
  have hp_ne : p.toReal ≠ 0 := hp_pos.ne'
  have hNpow0 : 0 ≤ N ^ p.toReal := Real.rpow_nonneg hN0 _
  have hroot_level : ∀ j,
      (S.levelCoeffPower j) ^ (1 / p.toReal) ≤
        N * (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
          (1 / p.toReal) := by
    intro j
    have hS0 : 0 ≤ S.levelCoeffPower j := S.levelCoeffPower_nonneg j
    have hL0 : 0 ≤ regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j :=
      regularFamilyRestrictionLevelCoeffPower_nonneg_local
        G Λ s p q hs hp hp_top y R j
    calc
      (S.levelCoeffPower j) ^ (1 / p.toReal)
          ≤ (N ^ p.toReal *
              regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
              (1 / p.toReal) :=
        Real.rpow_le_rpow hS0 (hlevel j) (one_div_nonneg.mpr hp_pos.le)
      _ = N *
            (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
              (1 / p.toReal) := by
        rw [Real.mul_rpow hNpow0 hL0,
          rpow_rpow_one_div_eq_self hN0 hp_ne]
  by_cases hqtop : q = ∞
  · rw [WeakGridSpace.LpGridRepresentation.pqCost, if_pos hqtop]
    rw [regularFamilyRestrictionCost, if_pos hqtop]
    have hbddS : BddAbove
        (Set.range fun j => (S.levelCoeffPower j) ^ (1 / p.toReal)) := by
      simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hSfin
    have hbddMixed : BddAbove
        (Set.range fun j : ℕ =>
          (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
            (1 / p.toReal)) := by
      simpa [RegularFamilyRestrictionFiniteCost, hqtop] using hMixedFin
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    exact (hroot_level j).trans
      (mul_le_mul_of_nonneg_left
        (le_csSup hbddMixed ⟨j, rfl⟩) hN0)
  · have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hqtop
    have hq_ne : q.toReal ≠ 0 := hq_pos.ne'
    rw [WeakGridSpace.LpGridRepresentation.pqCost, if_neg hqtop]
    rw [regularFamilyRestrictionCost, if_neg hqtop]
    have hSsum : Summable fun j => (S.levelCoeffPower j) ^ (q.toReal / p.toReal) := by
      simpa [WeakGridSpace.LpGridRepresentation.FinitePQCost, hqtop] using hSfin
    have hMixedSum : Summable fun j : ℕ =>
        (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
          (q.toReal / p.toReal) := by
      simpa [RegularFamilyRestrictionFiniteCost, hqtop] using hMixedFin
    have hterm_le : ∀ j,
        (S.levelCoeffPower j) ^ (q.toReal / p.toReal) ≤
          N ^ q.toReal *
            (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
              (q.toReal / p.toReal) := by
      intro j
      have hS0 : 0 ≤ S.levelCoeffPower j := S.levelCoeffPower_nonneg j
      have hL0 : 0 ≤ regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j :=
        regularFamilyRestrictionLevelCoeffPower_nonneg_local
          G Λ s p q hs hp hp_top y R j
      have hleft :
          (S.levelCoeffPower j) ^ (q.toReal / p.toReal) =
            ((S.levelCoeffPower j) ^ (1 / p.toReal)) ^ q.toReal := by
        rw [← Real.rpow_mul hS0]
        congr 1
        field_simp [hp_ne]
      have hright :
          N ^ q.toReal *
              (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
                (q.toReal / p.toReal) =
            (N *
              (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
                (1 / p.toReal)) ^ q.toReal := by
        rw [Real.mul_rpow hN0 (Real.rpow_nonneg hL0 _)]
        congr 1
        rw [← Real.rpow_mul hL0]
        congr 1
        field_simp [hp_ne]
      rw [hleft, hright]
      exact Real.rpow_le_rpow
        (Real.rpow_nonneg hS0 _) (hroot_level j) hq_pos.le
    have htsum_le :
        (∑' j, (S.levelCoeffPower j) ^ (q.toReal / p.toReal)) ≤
          ∑' j, N ^ q.toReal *
            (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
              (q.toReal / p.toReal) := by
      exact hSsum.tsum_le_tsum hterm_le (hMixedSum.mul_left _)
    have hsum_scaled :
        (∑' j, N ^ q.toReal *
            (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
              (q.toReal / p.toReal)) =
          N ^ q.toReal *
            ∑' j, (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
              (q.toReal / p.toReal) := by
      rw [tsum_mul_left]
    calc
      (∑' j, (S.levelCoeffPower j) ^ (q.toReal / p.toReal)) ^
          (1 / q.toReal)
          ≤ (∑' j, N ^ q.toReal *
            (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
              (q.toReal / p.toReal)) ^ (1 / q.toReal) :=
        Real.rpow_le_rpow
          (tsum_nonneg fun j => Real.rpow_nonneg (S.levelCoeffPower_nonneg j) _)
          htsum_le (one_div_nonneg.mpr hq_pos.le)
      _ = (N ^ q.toReal *
            ∑' j, (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
              (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
        rw [hsum_scaled]
      _ = N *
            (∑' j, (regularFamilyRestrictionLevelCoeffPower G s p q Λ y R j) ^
              (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hN0 _)
          (tsum_nonneg fun j =>
            Real.rpow_nonneg
              (regularFamilyRestrictionLevelCoeffPower_nonneg_local
                G Λ s p q hs hp hp_top y R j) _),
          rpow_rpow_one_div_eq_self hN0 hq_ne]

/--
Positive finite weighted sums preserve positivity and coefficient support.

The weights are real and nonnegative.  The representation is assembled with the
positive finite-sum construction from `PositiveCone`, so the result is a
positive Souza representation.  The support conclusion again says that a
nonzero output coefficient must come from one active input coefficient.
-/
theorem exists_finset_weighted_sum_positive_representation_support
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Γ : Finset ℕ) (Θ : ℕ → ℝ) (f : ℕ → α → ℂ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (P : (i : ℕ) → (k : ℕ) →
      WeakGridSpace.LevelCell G.toWeakGridSpace k → Prop)
    (hΘ : ∀ i ∈ Γ, 0 ≤ Θ i)
    (hRep : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (f i)
        (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hPos : ∀ i ∈ Γ, SouzaPositiveRepresentation G s p hs hp hp_top (R i))
    (hFin : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i))
    (hSupp : ∀ i ∈ Γ, ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ((R i).block k).coeff Q ≠ 0 → P i k Q) :
    ∃ Y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (Y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          (Y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        SouzaPositiveRepresentation G s p hs hp hp_top S ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 → ∃ i ∈ Γ, P i k Q) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let xLp : ℕ → Lp ℂ p G.toWeakGridSpace.measure :=
    fun i => (Θ i : ℂ) • (y i : Lp ℂ p G.toWeakGridSpace.measure)
  let Rscaled : (i : ℕ) → WeakGridSpace.LpGridRepresentation A (xLp i) :=
    fun i => by
      change WeakGridSpace.LpGridRepresentation A
        ((Θ i : ℂ) • (y i : Lp ℂ p G.toWeakGridSpace.measure))
      exact WeakGridSpace.LpGridRepresentation.smul (Θ i : ℂ) (R i)
  have hPosScaled : ∀ i ∈ Γ,
      SouzaPositiveRepresentation G s p hs hp hp_top (Rscaled i) := by
    intro i hi
    change SouzaPositiveRepresentation G s p hs hp hp_top
      (WeakGridSpace.LpGridRepresentation.smul (Θ i : ℂ) (R i))
    exact souzaPositiveRepresentation_smul_nonneg G s p hs hp hp_top
      (hΘ i hi) (hPos i hi)
  have hFinScaled : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (Rscaled i) := by
    intro i hi
    change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q)
      (WeakGridSpace.LpGridRepresentation.smul (Θ i : ℂ) (R i))
    exact WeakGridSpace.LpGridRepresentation.smul_finitePQCost
      (A := A) (q := q) (Θ i : ℂ) (hFin i hi)
  obtain ⟨T, hTpos, hTfin, hTcoeff, _hTroot⟩ :=
    exists_souzaPositiveRepresentation_finset_sum
      G s p q hs hp hp_top Γ xLp Rscaled hPosScaled hFinScaled
  have hYmem :
      (∑ i ∈ Γ, xLp i) ∈
        WeakGridSpace.BesovishSpace A q := by
    refine Submodule.sum_mem (WeakGridSpace.BesovishSpace A q) ?_
    intro i hi
    refine Submodule.smul_mem (WeakGridSpace.BesovishSpace A q)
      (Θ i : ℂ) ?_
    exact (y i).2
  let Y : WeakGridSpace.BesovishSpace A q :=
    ⟨∑ i ∈ Γ, xLp i, hYmem⟩
  let S : WeakGridSpace.LpGridRepresentation A
      (Y : Lp ℂ p G.toWeakGridSpace.measure) := by
    change WeakGridSpace.LpGridRepresentation A (∑ i ∈ Γ, xLp i)
    exact T
  have hRepScaled : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => (Θ i : ℂ) * f i z) (xLp i) := by
    intro i hi
    change WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p)
      (fun z => (Θ i : ℂ) * f i z)
      ((Θ i : ℂ) • (y i : Lp ℂ p G.toWeakGridSpace.measure))
    exact WeakGridSpace.representsFunction_smul (G := G.toWeakGridSpace)
      (p := p) (Θ i : ℂ) (hRep i hi)
  have hRepSum :
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
        (∑ i ∈ Γ, xLp i) :=
    WeakGridSpace.representsFunction_finset_sum
      (G := G.toWeakGridSpace) (p := p) Γ
      (fun i z => (Θ i : ℂ) * f i z) xLp hRepScaled
  have hSuppS :
      ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        (S.block k).coeff Q ≠ 0 → ∃ i ∈ Γ, P i k Q := by
    intro k Q hcoeff
    have hsum_ne : (∑ i ∈ Γ, ((Rscaled i).block k).coeff Q) ≠ 0 := by
      rw [← hTcoeff k Q]
      change (S.block k).coeff Q ≠ 0
      exact hcoeff
    have hexists :
        ∃ i ∈ Γ, ((Rscaled i).block k).coeff Q ≠ 0 := by
      by_contra hnone
      have hzero_each : ∀ i ∈ Γ, ((Rscaled i).block k).coeff Q = 0 := by
        intro i hi
        by_contra hne
        exact hnone ⟨i, hi, hne⟩
      have hsum_zero : (∑ i ∈ Γ, ((Rscaled i).block k).coeff Q) = 0 := by
        exact Finset.sum_eq_zero fun i hi => hzero_each i hi
      exact hsum_ne hsum_zero
    rcases hexists with ⟨i, hi, hscaled⟩
    have hscaled' :
        ((WeakGridSpace.LpGridRepresentation.smul (Θ i : ℂ) (R i)).block k).coeff Q
          ≠ 0 := by
      change
        ((WeakGridSpace.LpGridRepresentation.smul (Θ i : ℂ) (R i)).block k).coeff Q
          ≠ 0
      exact hscaled
    have horig : ((R i).block k).coeff Q ≠ 0 :=
      lpGridRepresentation_smul_coeff_ne_zero
        (G' := G.toWeakGridSpace) (s' := s) (p' := p) (u' := ∞)
        (A := A) (g := (y i : Lp ℂ p G.toWeakGridSpace.measure))
        (Θ i : ℂ) (R i) Q hscaled'
    exact ⟨i, hi, hSupp i hi k Q horig⟩
  refine ⟨Y, S, ?_, ?_, ?_, ?_⟩
  · change WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p)
      (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
      (∑ i ∈ Γ, xLp i)
    exact hRepSum
  · change SouzaPositiveRepresentation G s p hs hp hp_top T
    exact hTpos
  · change WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) T
    exact hTfin
  · exact hSuppS

/--
The regular-family product block for one member has no nonzero coefficients
outside that member.

`RegularDomains.lean` uses this fact internally in the restriction theorem.
The non-Archimedean statements need the same support transfer publicly, so we
record the local version here from the public `u₁` and `u₂` support lemmas.
-/
theorem regularFamily_productBlock_coeff_ne_zero_subset_domain_local
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
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

/--
For a nonzero coefficient of the regular-family product block, the uniform
overlap hypothesis controls the active weight attached to that block.
-/
theorem regularFamily_weight_abs_le_of_productBlock_overlap
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {Θ : ℕ → ℝ} {N : ℝ} (hN0 : 0 ≤ N)
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
        (quasiU2Block G s p hs hp hp_top Rind Rg j)).coeff Q ≠ 0)
    (hoverlap : regularFamilyOverlapCostInfinite G Λ Ω Θ Q ≤ ENNReal.ofReal N) :
    |Θ i| ≤ N := by
  have hsubset : Q.1 ⊆ Ω i :=
    regularFamily_productBlock_coeff_ne_zero_subset_domain_local
      G Λ Ω s C c p hs hp hp_top hΩ hi Rind Rg hblock Q hcoeff
  exact regularFamily_weight_abs_le_of_overlap_subset
    G Λ Ω Θ hN0 Q hi hsubset hoverlap

/--
A nonzero coefficient of the product block for `Ω_i` sees a nonzero source
cell of the second representation that meets `Ω_i`.

For the `u₁` part this source cell is an ancestor from the weighted ancestor
tower of `Rg`; for the `u₂` part it is the output cell itself.
-/
theorem regularFamily_productBlock_coeff_ne_zero_exists_source_meeting_domain
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
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
    ∃ l : ℕ, ∃ P : WeakGridSpace.LevelCell G.toWeakGridSpace l,
      (Rg.block l).coeff P ≠ 0 ∧ (P.1 ∩ Ω i).Nonempty := by
  rcases WeakGridSpace.LevelBlock.add_coeff_ne_zero
      (souzaAtomFamily G s p hs hp hp_top)
      (quasiU1Block G s p hs hp hp_top Rind Rg j)
      (quasiU2Block G s p hs hp hp_top Rind Rg j) Q hcoeff with h1 | h2
  · have hright :
        weightedAncestorCoeffSum G Rg Q ≠ 0 :=
      quasiU1Block_coeff_ne_zero_right
        G s p hs hp hp_top Rind Rg Q h1
    rcases weightedAncestorCoeffSum_ne_zero_exists G Rg Q hright with
      ⟨l, _hl, P, hQP, hPcoeff⟩
    have hQsubset : Q.1 ⊆ Ω i :=
      regularFamilyIndicator_quasiU1Block_coeff_ne_zero_subset_domain
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) hΩ hi Rind Rg hblock Q h1
    obtain ⟨z, hzQ⟩ := levelCell_nonempty G Q
    exact ⟨l, P, hPcoeff, ⟨z, hQP hzQ, hQsubset hzQ⟩⟩
  · have hsource : (Rg.block j).coeff Q ≠ 0 :=
      quasiU2Block_coeff_ne_zero_left
        G s p hs hp hp_top Rind Rg Q h2
    have hQsubset : Q.1 ⊆ Ω i :=
      regularFamilyIndicator_quasiU2Block_coeff_ne_zero_subset_domain
        (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
        (p := p) hΩ hi Rind Rg hblock Q h2
    obtain ⟨z, hzQ⟩ := levelCell_nonempty G Q
    exact ⟨j, Q, hsource, ⟨z, hzQ, hQsubset hzQ⟩⟩

/--
Apply the main source-cell overlap hypothesis to a nonzero coefficient of a
regular-family product block.
-/
theorem regularFamily_weight_abs_le_of_productBlock_source_overlap
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {Θ : ℕ → ℝ} {N : ℝ} (hN0 : 0 ≤ N)
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
        (quasiU2Block G s p hs hp hp_top Rind Rg j)).coeff Q ≠ 0)
    (hoverlap :
      ∀ l (P : WeakGridSpace.LevelCell G.toWeakGridSpace l),
        (Rg.block l).coeff P ≠ 0 →
          regularFamilyOverlapCostInfinite G Λ Ω Θ P ≤ ENNReal.ofReal N) :
    |Θ i| ≤ N := by
  rcases regularFamily_productBlock_coeff_ne_zero_exists_source_meeting_domain
      G Λ Ω s C c p hs hp hp_top hΩ hi Rind Rg hblock Q hcoeff with
    ⟨l, P, hPcoeff, hPmeet⟩
  have hterm : ENNReal.ofReal |Θ i| ≤ ENNReal.ofReal N :=
    (regularFamilyOverlapCostInfinite_term_le
      G Λ Ω Θ P hi hPmeet).trans (hoverlap l P hPcoeff)
  exact (ENNReal.ofReal_le_ofReal_iff hN0).mp hterm

/--
Levelwise version of the source-overlap weight control for product
representations.

If the `i`-th product representation has nonzero coefficient power at level
`k`, then some product coefficient at that level is nonzero.  The preceding
source-overlap lemma then finds an active source coefficient of `Rg`, so the
main overlap hypothesis bounds the weight `Θ i`.
-/
theorem regularFamily_weight_abs_le_of_productLevel_source_overlap
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {Θ : ℕ → ℝ} {N : ℝ} (hN0 : 0 ≤ N)
    {i k : ℕ} (hi : i ∈ Λ)
    {xind xg xprod : Lp ℂ p G.toWeakGridSpace.measure}
    (Rind : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xind)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (Rprod : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xprod)
    (hblock : ∀ m,
      Rind.block m =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i m)
    (hprodBlock : ∀ m,
      Rprod.block m =
        WeakGridSpace.LevelBlock.add (souzaAtomFamily G s p hs hp hp_top)
          (quasiU1Block G s p hs hp hp_top Rind Rg m)
          (quasiU2Block G s p hs hp hp_top Rind Rg m))
    (hlevel : Rprod.levelCoeffPower k ≠ 0)
    (hoverlap :
      ∀ l (P : WeakGridSpace.LevelCell G.toWeakGridSpace l),
        (Rg.block l).coeff P ≠ 0 →
          regularFamilyOverlapCostInfinite G Λ Ω Θ P ≤ ENNReal.ofReal N) :
    |Θ i| ≤ N := by
  rcases lpGridRepresentation_levelCoeffPower_ne_zero_exists_coeff
      (G' := G.toWeakGridSpace) (s' := s) (p' := p) (u' := ∞)
      (A := souzaAtomFamily G s p hs hp hp_top) Rprod hlevel with
    ⟨Q, hQcoeff⟩
  have hprodCoeff :
      (WeakGridSpace.LevelBlock.add (souzaAtomFamily G s p hs hp hp_top)
        (quasiU1Block G s p hs hp hp_top Rind Rg k)
        (quasiU2Block G s p hs hp hp_top Rind Rg k)).coeff Q ≠ 0 := by
    rw [← hprodBlock k]
    exact hQcoeff
  exact regularFamily_weight_abs_le_of_productBlock_source_overlap
    G Λ Ω s C c p hs hp hp_top hΩ hN0 hi Rind Rg hblock Q hprodCoeff hoverlap

/--
Finite weighted sums of regular-family product representations satisfy the
non-Archimedean cost estimate under the source-cell overlap hypothesis.

This is the finite core of the uniform theorem.  The product representations
are supplied as input, with their blocks identified as the usual
`quasiU1 + quasiU2` product blocks.  The overlap hypothesis is imposed only on
nonzero source coefficients of `Rg`; the previous lemma converts it into the
levelwise weight bound needed by the finite weighted-sum estimate.
-/
theorem exists_finset_weighted_sum_regularFamily_product_pqCost_le_of_source_overlap
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (Γ : Finset ℕ) (hΓΛ : ∀ i ∈ Γ, i ∈ Λ)
    (Θ : ℕ → ℝ) {N : ℝ} (hN0 : 0 ≤ N)
    (f : ℕ → α → ℂ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (xind : ℕ → Lp ℂ p G.toWeakGridSpace.measure)
    (Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (xind i))
    (hRep : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (f i)
        (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hFin : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i))
    (hIndBlock : ∀ i ∈ Γ, ∀ k,
      (Rind i).block k =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k)
    (hProdBlock : ∀ i ∈ Γ, ∀ k,
      (R i).block k =
        WeakGridSpace.LevelBlock.add (souzaAtomFamily G s p hs hp hp_top)
          (quasiU1Block G s p hs hp hp_top (Rind i) Rg k)
          (quasiU2Block G s p hs hp hp_top (Rind i) Rg k))
    (hoverlap :
      ∀ l (P : WeakGridSpace.LevelCell G.toWeakGridSpace l),
        (Rg.block l).coeff P ≠ 0 →
          regularFamilyOverlapCostInfinite G Λ Ω Θ P ≤ ENNReal.ofReal N) :
    ∃ Y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (Y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          (Y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          N * regularFamilyRestrictionCost G s p q (Γ : Set ℕ) y R ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 → ∃ i ∈ Γ, Q.1 ⊆ Ω i) := by
  classical
  have hSuppDomain : ∀ i ∈ Γ, ∀ k
      (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        ((R i).block k).coeff Q ≠ 0 → Q.1 ⊆ Ω i := by
    intro i hi k Q hcoeff
    have hprodCoeff :
        (WeakGridSpace.LevelBlock.add (souzaAtomFamily G s p hs hp hp_top)
          (quasiU1Block G s p hs hp hp_top (Rind i) Rg k)
          (quasiU2Block G s p hs hp hp_top (Rind i) Rg k)).coeff Q ≠ 0 := by
      rw [← hProdBlock i hi k]
      exact hcoeff
    exact regularFamily_productBlock_coeff_ne_zero_subset_domain_local
      G Λ Ω s C c p hs hp hp_top hΩ (hΓΛ i hi)
      (Rind i) Rg (hIndBlock i hi) Q hprodCoeff
  have hWeightLevel : ∀ i ∈ Γ, ∀ k,
      (R i).levelCoeffPower k ≠ 0 → |Θ i| ≤ N := by
    intro i hi k hlevel
    exact regularFamily_weight_abs_le_of_productLevel_source_overlap
      G Λ Ω s C c p hs hp hp_top hΩ hN0 (hΓΛ i hi)
      (Rind i) Rg (R i) (hIndBlock i hi) (hProdBlock i hi) hlevel hoverlap
  exact exists_finset_weighted_sum_regularFamily_pqCost_le_of_level_weight_bound
    G Λ Ω s p q hs hp hp_top hΩ Γ hΓΛ Θ hN0 f y R
    hWeightLevel hRep hFin hSuppDomain

/--
Regular-family restriction representations built from a prescribed source
representation with explicit tower bounds.

This is the reusable bridge between the main non-Archimedean hypotheses and
the finite weighted product estimate.  Unlike
`regularFamily_restriction_representations`, the source representation is not
chosen by the theorem: it is the concrete representation `Rg` supplied by the
caller.  The conclusion also records the exact `u₁ + u₂` block identity for
each active product representation.
-/
theorem regularFamily_product_restriction_representations_from_tower
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c) :
    ∃ Crel : ℝ,
      0 ≤ Crel ∧
      ∀ (g : α → ℂ) (M : ℝ)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (Rg : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (xg : Lp ℂ p G.toWeakGridSpace.measure)),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rg →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          ‖weightedAncestorCoeffSum G Rg Q‖ ≤ M) →
        ∃ yind : ℕ → WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          ∃ Rind : (i : ℕ) →
              WeakGridSpace.LpGridRepresentation
                (souzaAtomFamily G s p hs hp hp_top)
                (yind i : Lp ℂ p G.toWeakGridSpace.measure),
            ∃ y : ℕ → WeakGridSpace.BesovishSpace
                (souzaAtomFamily G s p hs hp hp_top) q,
              ∃ R : (i : ℕ) →
                  WeakGridSpace.LpGridRepresentation
                    (souzaAtomFamily G s p hs hp hp_top)
                    (y i : Lp ℂ p G.toWeakGridSpace.measure),
                (∀ i ∈ Λ,
                  WeakGridSpace.RepresentsFunction
                    (G := G.toWeakGridSpace) (p := p)
                    ((Ω i).indicator fun _ => (1 : ℂ))
                    (yind i : Lp ℂ p G.toWeakGridSpace.measure)) ∧
                (∀ i ∈ Λ,
                  WeakGridSpace.LpGridRepresentation.FinitePQCost
                    (q := q) (Rind i)) ∧
                (∀ i k,
                  (Rind i).block k =
                    regularFamilyIndicatorBlock
                      (hs := hs) (hp := hp) (hp_top := hp_top)
                      G Λ Ω s C c p hΩ i k) ∧
                (∀ i ∈ Λ,
                  WeakGridSpace.RepresentsFunction
                    (G := G.toWeakGridSpace) (p := p)
                    (fun z => ((Ω i).indicator (fun _ => (1 : ℂ)) z) * g z)
                    (y i : Lp ℂ p G.toWeakGridSpace.measure)) ∧
                (∀ i ∈ Λ,
                  WeakGridSpace.LpGridRepresentation.FinitePQCost
                    (q := q) (R i)) ∧
                (∀ i ∈ Λ, ∀ k,
                  (R i).block k =
                    WeakGridSpace.LevelBlock.add
                      (souzaAtomFamily G s p hs hp hp_top)
                      (quasiU1Block G s p hs hp hp_top (Rind i) Rg k)
                      (quasiU2Block G s p hs hp hp_top (Rind i) Rg k)) ∧
                (∀ i ∈ Λ, ∀ j
                  (Q : WeakGridSpace.LevelCell G.toWeakGridSpace j),
                    ((R i).block j).coeff Q ≠ 0 → Q.1 ⊆ Ω i) ∧
                regularFamilyRestrictionCost G s p q Λ y R ≤
                  Crel *
                    (WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg + M) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Crel : ℝ :=
    ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
      (regularFamilyGeomRootCost G Λ Ω s C c p q + 1)
  refine ⟨Crel, ?_, ?_⟩
  · exact mul_nonneg
      (Real.rpow_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) _)
      (add_nonneg
        (regularFamilyGeomRootCost_nonneg
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) (q := q) hΩ)
        zero_le_one)
  intro g M xg Rg hgrepr hgbdd hRgfin htower_g
  have hM0 : 0 ≤ M := regularFamilyRestriction_bound_nonneg G hgbdd
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
  refine ⟨yind, Rind, y, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (hind_active i hi).1
  · intro i hi
    exact (hind_active i hi).2.1
  · exact hblock_all
  · intro i hi
    exact (hprod_active i hi).1
  · intro i hi
    exact (hprod_active i hi).2.1
  · intro i hi k
    exact (hprod_active i hi).2.2.2 k
  · intro i hi j Q hcoeff
    have hprodCoeff :
        (WeakGridSpace.LevelBlock.add A
          (quasiU1Block G s p hs hp hp_top (Rind i) Rg j)
          (quasiU2Block G s p hs hp hp_top (Rind i) Rg j)).coeff Q ≠ 0 := by
      rw [← (hprod_active i hi).2.2.2 j]
      exact hcoeff
    exact regularFamily_productBlock_coeff_ne_zero_subset_domain_local
      (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
      (p := p) hs hp hp_top hΩ hi (Rind i) Rg
      (fun m => hblock_all i m) Q hprodCoeff
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
      simpa [regularFamilyGeomLevel] using
        regularFamilyIndicator_quasiProductBlock_aggregate_levelCoeffPower_le
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
      _ ≤ Crel *
            (WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg + M) := by
        have hG0 : 0 ≤ regularFamilyGeomRootCost G Λ Ω s C c p q :=
          regularFamilyGeomRootCost_nonneg
            (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
            (p := p) (q := q) hΩ
        have hR0 : 0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg :=
          WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rg
        have hK0 :
            0 ≤ ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) :=
          Real.rpow_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) _
        have hinner :
            M * regularFamilyGeomRootCost G Λ Ω s C c p q +
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg ≤
            (regularFamilyGeomRootCost G Λ Ω s C c p q + 1) *
              (WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg + M) := by
          nlinarith [hM0, hG0, hR0]
        dsimp [Crel]
        calc
          ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
              (M * regularFamilyGeomRootCost G Λ Ω s C c p q +
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg)
              ≤ ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
                ((regularFamilyGeomRootCost G Λ Ω s C c p q + 1) *
                  (WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg + M)) :=
            mul_le_mul_of_nonneg_left hinner hK0
          _ = ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
                (regularFamilyGeomRootCost G Λ Ω s C c p q + 1) *
              (WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg + M) := by
            ring

/--
Finite product restrictions satisfy the same level bound as the full regular
family.

This turns the explicit finite product-block estimate from `RegularDomains`
into the formal `regularFamilyRestrictionLevelCoeffPower` language used by the
non-Archimedean finite weighted-sum machinery.
-/
theorem regularFamily_product_restriction_finset_levelCoeffPower_le
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (xind : ℕ → Lp ℂ p G.toWeakGridSpace.measure)
    (Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (xind i))
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hIndBlock : ∀ i k,
      (Rind i).block k =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k)
    (Γ : Finset ℕ) (hΓΛ : ∀ i ∈ Γ, i ∈ Λ)
    (hProdBlock : ∀ i ∈ Γ, ∀ k,
      (R i).block k =
        WeakGridSpace.LevelBlock.add (souzaAtomFamily G s p hs hp hp_top)
          (quasiU1Block G s p hs hp hp_top (Rind i) Rg k)
          (quasiU2Block G s p hs hp hp_top (Rind i) Rg k))
    {M : ℝ} (hM0 : 0 ≤ M)
    (htower_g : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G Rg Q‖ ≤ M)
    (j : ℕ) :
    regularFamilyRestrictionLevelCoeffPower G s p q (Γ : Set ℕ) y R j ≤
      (2 : ℝ) ^ (p.toReal - 1) *
        (M ^ p.toReal * regularFamilyGeomLevel G Λ Ω s C c p j +
          Rg.levelCoeffPower j) := by
  classical
  calc
    regularFamilyRestrictionLevelCoeffPower G s p q (Γ : Set ℕ) y R j
        = ∑ i ∈ Γ, (R i).levelCoeffPower j := by
          rw [regularFamilyRestrictionLevelCoeffPower_finset]
    _ = ∑ i ∈ Γ,
        ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace j,
          ‖(WeakGridSpace.LevelBlock.add
            (souzaAtomFamily G s p hs hp hp_top)
            (quasiU1Block G s p hs hp hp_top (Rind i) Rg j)
            (quasiU2Block G s p hs hp hp_top (Rind i) Rg j)).coeff Q‖ ^
            p.toReal := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          unfold WeakGridSpace.LpGridRepresentation.levelCoeffPower
          refine Finset.sum_congr rfl ?_
          intro Q _
          rw [hProdBlock i hi j]
    _ ≤ (2 : ℝ) ^ (p.toReal - 1) *
        (M ^ p.toReal * regularFamilyGeomLevel G Λ Ω s C c p j +
          Rg.levelCoeffPower j) := by
          simpa [regularFamilyGeomLevel] using
          regularFamilyIndicator_quasiProductBlock_finset_levelCoeffPower_le
              (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
              (p := p) hΩ Rind Rg hIndBlock hM0 htower_g Γ hΓΛ j

/--
A subfamily restriction cost is controlled by the global regular-family
geometry whenever its level powers satisfy the global level estimate.

The index set used in the restriction cost, `Λcost`, is deliberately separate
from the regular family `Λ`.  This is the form needed for finite truncations:
the finite sum only sees the indices in `Γ`, but the geometric decay still
comes from the ambient regular family.
-/
theorem regularFamilyRestrictionCost_le_of_global_level_bound
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (Λcost : Set ℕ) (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
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
      regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j ≤
        (2 : ℝ) ^ (p.toReal - 1) *
          (M ^ p.toReal * regularFamilyGeomLevel G Λ Ω s C c p j +
            Rg.levelCoeffPower j)) :
    regularFamilyRestrictionCost G s p q Λcost y R ≤
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
    ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
      hp_top
  have hp_real : 1 ≤ p.toReal := (ENNReal.dichotomy p).resolve_left hp_top
  have hK0 : 0 ≤ K := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hKroot0 : 0 ≤ Kroot := Real.rpow_nonneg hK0 _
  have hKroot_pow : Kroot ^ p.toReal = K :=
    rpow_one_div_rpow_eq_self hK0 hp_pos.ne'
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
      (regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
          (1 / p.toReal) ≤
        Kroot * (M * Droot j + Broot j) := by
    intro j
    let L := regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j
    have hL0 : 0 ≤ L :=
      regularFamilyRestrictionLevelCoeffPower_nonneg_local
        (G := G) (Λ := Λcost) (s := s) (p := p) (q := q)
        hs hp hp_top y R j
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
        rw [rpow_one_div_rpow_eq_self
          (regularFamilyGeomLevel_nonneg
            (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
            (p := p) hΩ j) hp_pos.ne']
      have hB :
          (Broot j) ^ p.toReal = Rg.levelCoeffPower j := by
        simp only [Broot]
        rw [rpow_one_div_rpow_eq_self (Rg.levelCoeffPower_nonneg j) hp_pos.ne']
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
          ≤ ((Kroot * (M * Droot j + Broot j)) ^ p.toReal) ^
              (1 / p.toReal) :=
        Real.rpow_le_rpow hL0 hpow_bound (one_div_nonneg.mpr hp_pos.le)
      _ = Kroot * (M * Droot j + Broot j) := by
        exact rpow_rpow_one_div_eq_self
          (mul_nonneg hKroot0 (add_nonneg ha0 hb0)) hp_pos.ne'
  by_cases hq : q = ∞
  · rw [regularFamilyRestrictionCost, if_pos hq]
    have hbdd : BddAbove (Set.range fun j : ℕ =>
        (regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
          (1 / p.toReal)) := by
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
        (regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
          (q.toReal / p.toReal) := by
      refine Summable.of_nonneg_of_le
        (f := fun j : ℕ => (Kroot * (M * Droot j + Broot j)) ^ q.toReal)
        (g := fun j : ℕ =>
          (regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
            (q.toReal / p.toReal))
        (fun j => Real.rpow_nonneg
          (regularFamilyRestrictionLevelCoeffPower_nonneg_local
            (G := G) (Λ := Λcost) (s := s) (p := p) (q := q)
            hs hp hp_top y R j) _) ?_ ?_
      · intro j
        have hL0 : 0 ≤ regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j :=
          regularFamilyRestrictionLevelCoeffPower_nonneg_local
            (G := G) (Λ := Λcost) (s := s) (p := p) (q := q)
            hs hp hp_top y R j
        have hleft :
            (regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
                (q.toReal / p.toReal) =
              ((regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
                (1 / p.toReal)) ^ q.toReal := by
          rw [← Real.rpow_mul hL0]
          congr 1
          ring
        change
          (regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
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
          (regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
            (q.toReal / p.toReal)) ≤
          ∑' j : ℕ, (Kroot * (M * Droot j + Broot j)) ^ q.toReal := by
      refine hLsum.tsum_le_tsum ?_ ?_
      · intro j
        have hL0 : 0 ≤ regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j :=
          regularFamilyRestrictionLevelCoeffPower_nonneg_local
            (G := G) (Λ := Λcost) (s := s) (p := p) (q := q)
            hs hp hp_top y R j
        have hleft :
            (regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
                (q.toReal / p.toReal) =
              ((regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
                (1 / p.toReal)) ^ q.toReal := by
          rw [← Real.rpow_mul hL0]
          congr 1
          ring
        change
          (regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
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
        rpow_rpow_one_div_eq_self hKroot0 hq_pos.ne']
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
          rpow_rpow_one_div_eq_self hM0 hq_pos.ne']
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
        (regularFamilyRestrictionLevelCoeffPower G s p q Λcost y R j) ^
          (q.toReal / p.toReal)) ^ (1 / q.toReal)
          ≤ (∑' j : ℕ, (Kroot * (M * Droot j + Broot j)) ^ q.toReal) ^
              (1 / q.toReal) :=
        Real.rpow_le_rpow
          (tsum_nonneg fun j => Real.rpow_nonneg
            (regularFamilyRestrictionLevelCoeffPower_nonneg_local
              (G := G) (Λ := Λcost) (s := s) (p := p) (q := q)
              hs hp hp_top y R j) _)
          htsum_le (one_div_nonneg.mpr hq_pos.le)
      _ = Kroot * (∑' j : ℕ, (M * Droot j + Broot j) ^ q.toReal) ^
            (1 / q.toReal) := hscaled_root
      _ ≤ Kroot * (M * Groot + Rcost) :=
        mul_le_mul_of_nonneg_left hadd_root hKroot0

/--
Finite weighted sums of the regular-family product restrictions satisfy the
global geometric non-Archimedean estimate.

This combines the source-cell overlap estimate, the finite product-block level
bound, and the global restriction-cost comparison.  It is the finite partial
sum estimate that the infinite regular-family theorem should take to the
limit.
-/
theorem exists_finset_weighted_sum_regularFamily_product_pqCost_le_global
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (Γ : Finset ℕ) (hΓΛ : ∀ i ∈ Γ, i ∈ Λ)
    (Θ : ℕ → ℝ) {N M : ℝ} (hN0 : 0 ≤ N) (hM0 : 0 ≤ M)
    (f : ℕ → α → ℂ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hRgfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rg)
    (xind : ℕ → Lp ℂ p G.toWeakGridSpace.measure)
    (Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (xind i))
    (hRep : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (f i)
        (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hFin : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i))
    (hIndBlock : ∀ i k,
      (Rind i).block k =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k)
    (hProdBlock : ∀ i ∈ Γ, ∀ k,
      (R i).block k =
        WeakGridSpace.LevelBlock.add (souzaAtomFamily G s p hs hp hp_top)
          (quasiU1Block G s p hs hp hp_top (Rind i) Rg k)
          (quasiU2Block G s p hs hp hp_top (Rind i) Rg k))
    (htower_g : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G Rg Q‖ ≤ M)
    (hoverlap :
      ∀ l (P : WeakGridSpace.LevelCell G.toWeakGridSpace l),
        (Rg.block l).coeff P ≠ 0 →
          regularFamilyOverlapCostInfinite G Λ Ω Θ P ≤ ENNReal.ofReal N) :
    ∃ Y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (Y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          (Y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          N *
            (((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
              (M * regularFamilyGeomRootCost G Λ Ω s C c p q +
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg)) ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 → ∃ i ∈ Γ, Q.1 ⊆ Ω i) := by
  classical
  obtain ⟨Y, S, hRepS, hFinS, hCostS, hSuppS⟩ :=
    exists_finset_weighted_sum_regularFamily_product_pqCost_le_of_source_overlap
      G Λ Ω s C c p q hs hp hp_top hΩ Γ hΓΛ Θ hN0 f y R Rg xind Rind
      hRep hFin (fun i _hi k => hIndBlock i k) hProdBlock hoverlap
  have hlevel : ∀ j,
      regularFamilyRestrictionLevelCoeffPower G s p q (Γ : Set ℕ) y R j ≤
        (2 : ℝ) ^ (p.toReal - 1) *
          (M ^ p.toReal * regularFamilyGeomLevel G Λ Ω s C c p j +
            Rg.levelCoeffPower j) := by
    intro j
    exact regularFamily_product_restriction_finset_levelCoeffPower_le
      G Λ Ω s C c p q hs hp hp_top hΩ Rg xind Rind y R hIndBlock
      Γ hΓΛ hProdBlock hM0 htower_g j
  have hRestr :
      regularFamilyRestrictionCost G s p q (Γ : Set ℕ) y R ≤
        ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
          (M * regularFamilyGeomRootCost G Λ Ω s C c p q +
            WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg) :=
    regularFamilyRestrictionCost_le_of_global_level_bound
      G Λ Ω (Γ : Set ℕ) s C c p q hs hp hp_top hΩ Rg hRgfin hM0 y R hlevel
  refine ⟨Y, S, hRepS, hFinS, ?_, hSuppS⟩
  exact hCostS.trans (mul_le_mul_of_nonneg_left hRestr hN0)

/--
Finite weighted regular-family product sums with the bounded-Besov gauge
constant in the same shape as the final multiplier statement.
-/
theorem exists_finset_weighted_sum_regularFamily_product_pqCost_le_global_bounded
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (Γ : Finset ℕ) (hΓΛ : ∀ i ∈ Γ, i ∈ Λ)
    (Θ : ℕ → ℝ) {N M : ℝ} (hN0 : 0 ≤ N) (hM0 : 0 ≤ M)
    (f : ℕ → α → ℂ)
    (y : ℕ → WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (y i : Lp ℂ p G.toWeakGridSpace.measure))
    {xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) xg)
    (hRgfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rg)
    (xind : ℕ → Lp ℂ p G.toWeakGridSpace.measure)
    (Rind : (i : ℕ) → WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) (xind i))
    (hRep : ∀ i ∈ Γ,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p) (f i)
        (y i : Lp ℂ p G.toWeakGridSpace.measure))
    (hFin : ∀ i ∈ Γ,
      WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) (R i))
    (hIndBlock : ∀ i k,
      (Rind i).block k =
        regularFamilyIndicatorBlock
          (hs := hs) (hp := hp) (hp_top := hp_top) G Λ Ω s C c p hΩ i k)
    (hProdBlock : ∀ i ∈ Γ, ∀ k,
      (R i).block k =
        WeakGridSpace.LevelBlock.add (souzaAtomFamily G s p hs hp hp_top)
          (quasiU1Block G s p hs hp hp_top (Rind i) Rg k)
          (quasiU2Block G s p hs hp hp_top (Rind i) Rg k))
    (htower_g : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G Rg Q‖ ≤ M)
    (hoverlap :
      ∀ l (P : WeakGridSpace.LevelCell G.toWeakGridSpace l),
        (Rg.block l).coeff P ≠ 0 →
          regularFamilyOverlapCostInfinite G Λ Ω Θ P ≤ ENNReal.ofReal N) :
    ∃ Y : WeakGridSpace.BesovishSpace
        (souzaAtomFamily G s p hs hp hp_top) q,
      ∃ S : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (Y : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p)
          (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * f i z)
          (Y : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
          (((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
              (regularFamilyGeomRootCost G Λ Ω s C c p q + 1)) *
            N *
            (WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg + M) ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 → ∃ i ∈ Γ, Q.1 ⊆ Ω i) := by
  classical
  obtain ⟨Y, S, hRepS, hFinS, hCostS, hSuppS⟩ :=
    exists_finset_weighted_sum_regularFamily_product_pqCost_le_global
      G Λ Ω s C c p q hs hp hp_top hΩ Γ hΓΛ Θ hN0 hM0 f y R Rg hRgfin
      xind Rind hRep hFin hIndBlock hProdBlock htower_g hoverlap
  let Kroot : ℝ := ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal)
  let Groot : ℝ := regularFamilyGeomRootCost G Λ Ω s C c p q
  let Rcost : ℝ := WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rg
  have hK0 : 0 ≤ Kroot :=
    Real.rpow_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) _
  have hG0 : 0 ≤ Groot := regularFamilyGeomRootCost_nonneg
    (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
    (p := p) (q := q) hΩ
  have hR0 : 0 ≤ Rcost := WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rg
  have hinner : M * Groot + Rcost ≤ (Groot + 1) * (Rcost + M) := by
    nlinarith [hM0, hG0, hR0]
  refine ⟨Y, S, hRepS, hFinS, ?_, hSuppS⟩
  calc
    WeakGridSpace.LpGridRepresentation.pqCost (q := q) S
        ≤ N * (Kroot * (M * Groot + Rcost)) := hCostS
    _ = Kroot * N * (M * Groot + Rcost) := by ring
    _ ≤ Kroot * N * ((Groot + 1) * (Rcost + M)) :=
      mul_le_mul_of_nonneg_left hinner (mul_nonneg hK0 hN0)
    _ = (Kroot * (Groot + 1)) * N * (Rcost + M) := by ring

/--
Partial sums over the initial finite truncations of an active index set
converge to the corresponding subtype-indexed `HasSum`.
-/
theorem tendsto_initial_subtype_sums_of_hasSum
    {Λ : Set ℕ} (a : ℕ → ℂ) {L : ℂ}
    (hseries : HasSum (fun i : {i // i ∈ Λ} => a i.1) L) :
    Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ nonArchimedeanLambdaInitial Λ n, a i)
      Filter.atTop (𝓝 L) := by
  classical
  let aNat : ℕ → ℂ := fun i => if hi : i ∈ Λ then a i else 0
  have hzero_outside :
      ∀ i ∉ Set.range (fun j : {i // i ∈ Λ} => j.1), aNat i = 0 := by
    intro i hi
    by_cases hiΛ : i ∈ Λ
    · exact False.elim (hi ⟨⟨i, hiΛ⟩, rfl⟩)
    · simp [aNat, hiΛ]
  have hcomp :
      aNat ∘ (fun j : {i // i ∈ Λ} => j.1) =
        fun j : {i // i ∈ Λ} => a j.1 := by
    funext j
    simp [aNat, j.2]
  have hNat : HasSum aNat L :=
    (Subtype.val_injective.hasSum_iff
      (f := aNat) (a := L) hzero_outside).mp
      (by simpa [hcomp] using hseries)
  have htendsto := hNat.tendsto_sum_nat
  convert htendsto using 1
  ext n
  simp [nonArchimedeanLambdaInitial, aNat, Finset.sum_filter]

/--
For a regular family, the pointwise weighted indicator series has finite
support.  At a fixed point, at most one active domain can contribute.
-/
theorem regularFamily_weightedIndicator_summable_pointwise
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    (Θ : ℕ → ℝ) (f : α → ℂ) (z : α) :
    Summable fun i : {i // i ∈ Λ} =>
      (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z := by
  classical
  let term : {i // i ∈ Λ} → ℂ := fun i =>
    (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z
  have hsupport_finite : (Function.support term).Finite := by
    by_cases hmem : ∃ i : {i // i ∈ Λ}, z ∈ Ω i.1
    · rcases hmem with ⟨i₀, hi₀z⟩
      refine Set.Finite.subset (Set.finite_singleton i₀) ?_
      intro i hi
      have hzi : z ∈ Ω i.1 := by
        by_contra hzin
        have hterm_zero : term i = 0 := by
          simp [term, Set.indicator_of_notMem hzin]
        exact hi hterm_zero
      have hval : i.1 = i₀.1 := by
        by_contra hne
        have hdisj : Disjoint (Ω i.1) (Ω i₀.1) :=
          hΩ.pairwise_disjoint i.1 i.2 i₀.1 i₀.2 hne
        exact Set.disjoint_left.mp hdisj hzi hi₀z
      exact Set.mem_singleton_iff.mpr (Subtype.ext hval)
    · refine Set.Finite.subset Set.finite_empty ?_
      intro i hi
      exfalso
      have hzi : z ∈ Ω i.1 := by
        by_contra hzin
        have hterm_zero : term i = 0 := by
          simp [term, Set.indicator_of_notMem hzin]
        exact hi hterm_zero
      exact hmem ⟨i, hzi⟩
  change Summable term
  exact summable_of_hasFiniteSupport hsupport_finite

/-- The canonical pointwise sum of the weighted indicator series. -/
theorem regularFamily_weightedIndicator_hasSum_tsum_pointwise
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    (Θ : ℕ → ℝ) (f : α → ℂ) (z : α) :
    HasSum
      (fun i : {i // i ∈ Λ} =>
        (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
      (∑' i : {i // i ∈ Λ},
        (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z) := by
  exact (regularFamily_weightedIndicator_summable_pointwise
    G Λ Ω hΩ Θ f z).hasSum

/--
At a point where the represented input has an active source cell, the overlap
hypothesis bounds the absolute weighted-indicator sum by `N`.
-/
theorem regularFamily_weightedIndicator_norm_tsum_le_of_active_cell
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    (Θ : ℕ → ℝ) {N : ℝ} (hN0 : 0 ≤ N)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {z : α} (hzQ : z ∈ Q.1)
    (hoverlap : regularFamilyOverlapCostInfinite G Λ Ω Θ Q ≤ ENNReal.ofReal N) :
    HasSum
      (fun i : {i // i ∈ Λ} =>
        ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖)
      (∑' i : {i // i ∈ Λ},
        ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖) ∧
    (∑' i : {i // i ∈ Λ},
        ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖) ≤ N := by
  classical
  let b : {i // i ∈ Λ} → ℝ := fun i =>
    ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖
  have hsummable :
      Summable b := by
    let term : {i // i ∈ Λ} → ℂ := fun i =>
      (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z
    have hsupport_finite : (Function.support term).Finite := by
      by_cases hmem : ∃ i : {i // i ∈ Λ}, z ∈ Ω i.1
      · rcases hmem with ⟨i₀, hi₀z⟩
        refine Set.Finite.subset (Set.finite_singleton i₀) ?_
        intro i hi
        have hzi : z ∈ Ω i.1 := by
          by_contra hzin
          have hterm_zero : term i = 0 := by
            simp [term, Set.indicator_of_notMem hzin]
          exact hi hterm_zero
        have hval : i.1 = i₀.1 := by
          by_contra hne
          have hdisj : Disjoint (Ω i.1) (Ω i₀.1) :=
            hΩ.pairwise_disjoint i.1 i.2 i₀.1 i₀.2 hne
          exact Set.disjoint_left.mp hdisj hzi hi₀z
        exact Set.mem_singleton_iff.mpr (Subtype.ext hval)
      · refine Set.Finite.subset Set.finite_empty ?_
        intro i hi
        exfalso
        have hzi : z ∈ Ω i.1 := by
          by_contra hzin
          have hterm_zero : term i = 0 := by
            simp [term, Set.indicator_of_notMem hzin]
          exact hi hterm_zero
        exact hmem ⟨i, hzi⟩
    have hnorm_support :
        Function.support b ⊆ Function.support term := by
      intro i hi hterm_zero
      apply hi
      change ‖term i‖ = 0
      rw [hterm_zero]
      simp
    exact summable_of_hasFiniteSupport (hsupport_finite.subset hnorm_support)
  have hterm_le : ∀ i, b i ≤ N := by
    intro i
    by_cases hzi : z ∈ Ω i.1
    · have hmeet : (Q.1 ∩ Ω i.1).Nonempty := ⟨z, hzQ, hzi⟩
      have htheta :
          |Θ i.1| ≤ N :=
        regularFamily_weight_abs_le_of_overlap_meet
          G Λ Ω Θ hN0 Q i.2 hmeet hoverlap
      calc
        b i = |Θ i.1| := by
          simp [b, Set.indicator_of_mem hzi, Complex.norm_real]
        _ ≤ N := htheta
    · have hbzero : b i = 0 := by
        simp [b, Set.indicator_of_notMem hzi]
      rw [hbzero]
      exact hN0
  have hsum_le : (∑' i : {i // i ∈ Λ}, b i) ≤ N := by
    by_cases hmem : ∃ i : {i // i ∈ Λ}, b i ≠ 0
    · rcases hmem with ⟨i₀, hi₀⟩
      have hzero : ∀ i ≠ i₀, b i = 0 := by
        intro i hi
        by_contra hbi
        have hzi : z ∈ Ω i.1 := by
          by_contra hzin
          have hbzero : b i = 0 := by
            simp [b, Set.indicator_of_notMem hzin]
          exact hbi hbzero
        have hzi₀ : z ∈ Ω i₀.1 := by
          by_contra hzin
          have hbzero : b i₀ = 0 := by
            simp [b, Set.indicator_of_notMem hzin]
          exact hi₀ hbzero
        have hval : i.1 = i₀.1 := by
          by_contra hne
          have hdisj : Disjoint (Ω i.1) (Ω i₀.1) :=
            hΩ.pairwise_disjoint i.1 i.2 i₀.1 i₀.2 hne
          exact Set.disjoint_left.mp hdisj hzi hzi₀
        exact hi (Subtype.ext hval)
      rw [tsum_eq_single i₀]
      · exact hterm_le i₀
      · intro i hi
        exact hzero i hi
    · have hzero : ∀ i, b i = 0 := by
        intro i
        by_contra hbi
        exact hmem ⟨i, hbi⟩
      have htsum_zero : (∑' i : {i // i ∈ Λ}, b i) = 0 := by
        calc
          (∑' i : {i // i ∈ Λ}, b i)
              = ∑' i : {i // i ∈ Λ}, (0 : ℝ) := by
                exact tsum_congr fun i => hzero i
          _ = 0 := by simp
      rw [htsum_zero]
      exact hN0
  exact ⟨hsummable.hasSum, by simpa [b] using hsum_le⟩

/--
The canonical product series is pointwise bounded by `N * ‖f z‖` whenever the
source representation has an active cell containing `z`.
-/
theorem regularFamily_weightedIndicator_product_tsum_norm_le_of_active_cell
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    {a C c : ℝ} (hΩ : RegularFamily G Λ Ω a C c)
    (Θ : ℕ → ℝ) {N : ℝ} (hN0 : 0 ≤ N)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k)
    {z : α} (hzQ : z ∈ Q.1)
    (hoverlap : regularFamilyOverlapCostInfinite G Λ Ω Θ Q ≤ ENNReal.ofReal N)
    (f : α → ℂ) :
    ‖(∑' i : {i // i ∈ Λ},
        (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
      ≤ N * ‖f z‖ := by
  classical
  obtain ⟨hAbs, hAbs_le⟩ :=
    regularFamily_weightedIndicator_norm_tsum_le_of_active_cell
      G Λ Ω hΩ Θ hN0 Q hzQ hoverlap
  have hsummable_prod_norm :
      Summable fun i : {i // i ∈ Λ} =>
        ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z‖ := by
    simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using
      hAbs.summable.mul_right ‖f z‖
  have hnorm_le :
      ‖(∑' i : {i // i ∈ Λ},
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
        ≤ ∑' i : {i // i ∈ Λ},
          ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z‖ :=
    norm_tsum_le_tsum_norm hsummable_prod_norm
  have htsum_prod :
      (∑' i : {i // i ∈ Λ},
          ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z‖) =
        (∑' i : {i // i ∈ Λ},
          ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖) *
          ‖f z‖ := by
    simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using
      hAbs.summable.tsum_mul_right ‖f z‖
  calc
    ‖(∑' i : {i // i ∈ Λ},
        (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
        ≤ ∑' i : {i // i ∈ Λ},
          ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z‖ :=
      hnorm_le
    _ = (∑' i : {i // i ∈ Λ},
          ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖) *
          ‖f z‖ := htsum_prod
    _ ≤ N * ‖f z‖ :=
      mul_le_mul_of_nonneg_right hAbs_le (norm_nonneg _)

/--
Almost everywhere, the canonical pointwise regular-family sum has the expected
`HasSum` and the non-Archimedean pointwise bounds.
-/
theorem regularFamily_weightedIndicator_product_tsum_bounds_ae
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (Θ : ℕ → ℝ) {N M : ℝ} (hN0 : 0 ≤ N)
    (f : α → ℂ)
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hfbdd : ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ M)
    (hoverlap :
      ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        (R.block k).coeff Q ≠ 0 →
          regularFamilyOverlapCostInfinite G Λ Ω Θ Q ≤ ENNReal.ofReal N) :
    ∀ᵐ z ∂G.toWeakGridSpace.measure,
      HasSum
        (fun i : {i // i ∈ Λ} =>
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
        (∑' i : {i // i ∈ Λ},
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z) ∧
      ‖(∑' i : {i // i ∈ Λ},
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
        ≤ N * ‖f z‖ ∧
      ‖(∑' i : {i // i ∈ Λ},
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
        ≤ N * M := by
  classical
  have hactive_ae :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        f z ≠ 0 →
          ∃ k, ∃ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            z ∈ Q.1 ∧ (R.block k).coeff Q ≠ 0 :=
    exists_active_cell_of_representsFunction_ne_zero_ae
      G s p q hs hp hp_top x R hRep
  filter_upwards [hactive_ae, hfbdd] with z hactive_z hfbdd_z
  have hsum :
      HasSum
        (fun i : {i // i ∈ Λ} =>
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
        (∑' i : {i // i ∈ Λ},
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z) :=
    regularFamily_weightedIndicator_hasSum_tsum_pointwise
      G Λ Ω hΩ Θ f z
  have hnorm :
      ‖(∑' i : {i // i ∈ Λ},
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)‖
        ≤ N * ‖f z‖ := by
    by_cases hfz : f z = 0
    · simp [hfz]
    · rcases hactive_z hfz with ⟨k, Q, hzQ, hQcoeff⟩
      exact regularFamily_weightedIndicator_product_tsum_norm_le_of_active_cell
        G Λ Ω hΩ Θ hN0 Q hzQ (hoverlap k Q hQcoeff) f
  refine ⟨hsum, hnorm, ?_⟩
  exact hnorm.trans (mul_le_mul_of_nonneg_left hfbdd_z hN0)

/--
Infinite uniform regular-family Besov representation from a prescribed
pointwise `HasSum`.

This is the limit step after the finite regular-family non-Archimedean
estimate.  It builds products `1_{Ω_i} f`, applies the finite estimate to the
initial truncations of `Λ`, and passes to a uniformly bounded representation
limit while preserving the domain-localized coefficient support.
-/
theorem exists_regularFamily_nonArchimedean_infinite_besov_representation
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c)
    (Θ : ℕ → ℝ) {N M : ℝ} (hN0 : 0 ≤ N)
    (f h : α → ℂ)
    (x : WeakGridSpace.BesovishSpace
      (souzaAtomFamily G s p hs hp hp_top) q)
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top)
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hRep : WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := p) f
      (x : Lp ℂ p G.toWeakGridSpace.measure))
    (hfbdd : ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ M)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R)
    (htower_g : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖weightedAncestorCoeffSum G R Q‖ ≤ M)
    (hoverlap :
      ∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
        (R.block k).coeff Q ≠ 0 →
          regularFamilyOverlapCostInfinite G Λ Ω Θ Q ≤ ENNReal.ofReal N)
    (hseries : ∀ᵐ z ∂G.toWeakGridSpace.measure,
      HasSum
        (fun i : {i // i ∈ Λ} =>
          (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
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
          (((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
              (regularFamilyGeomRootCost G Λ Ω s C c p q + 1)) *
            N *
            (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R + M) ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (S.block k).coeff Q ≠ 0 → ∃ i ∈ Λ, Q.1 ⊆ Ω i) := by
  classical
  let A := souzaAtomFamily G s p hs hp hp_top
  let Cna : ℝ :=
    ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
      (regularFamilyGeomRootCost G Λ Ω s C c p q + 1)
  have hM0 : 0 ≤ M := regularFamilyRestriction_bound_nonneg G hfbdd
  rcases regularFamily_product_restriction_representations_from_tower
      G Λ Ω s C c p q hs hs_lt_inv hp hp_top hΩ with
    ⟨_Crel, _hCrel0, hproducts⟩
  rcases hproducts f M x R hRep hfbdd hRfin htower_g with
    ⟨yind, Rind, yprod, Rprod, _hindRep, _hindFin, hIndBlock,
      hprodRep, hprodFin, hProdBlock, _hProdSupp, _hRestrCost⟩
  let productFun : ℕ → α → ℂ := fun i z =>
    ((Ω i).indicator (fun _ => (1 : ℂ)) z) * f z
  let partialFun : ℕ → α → ℂ := fun n z =>
    ∑ i ∈ nonArchimedeanLambdaInitial Λ n, (Θ i : ℂ) * productFun i z
  let Cbound : ℝ :=
    Cna * N * (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R + M)
  have hCna0 : 0 ≤ Cna := by
    exact mul_nonneg
      (Real.rpow_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) _)
      (add_nonneg
        (regularFamilyGeomRootCost_nonneg
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) (q := q) hΩ)
        zero_le_one)
  have hCbound0 : 0 ≤ Cbound := by
    exact mul_nonneg (mul_nonneg hCna0 hN0)
      (add_nonneg (WeakGridSpace.LpGridRepresentation.pqCost_nonneg R) hM0)
  have hfiniteRep : ∀ n,
      ∃ yn : WeakGridSpace.BesovishSpace A q,
      ∃ Sn : WeakGridSpace.LpGridRepresentation A
          (yn : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) (partialFun n)
          (yn : Lp ℂ p G.toWeakGridSpace.measure) ∧
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Sn ∧
        WeakGridSpace.LpGridRepresentation.pqCost (q := q) Sn ≤ Cbound ∧
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (Sn.block k).coeff Q ≠ 0 → ∃ i ∈ Λ, Q.1 ⊆ Ω i) := by
    intro n
    let Γ : Finset ℕ := nonArchimedeanLambdaInitial Λ n
    have hΓΛ : ∀ i ∈ Γ, i ∈ Λ := fun i hi =>
      mem_of_mem_nonArchimedeanLambdaInitial hi
    obtain ⟨Y, S, hRepS, hFinS, hCostS, hSuppS⟩ :=
      exists_finset_weighted_sum_regularFamily_product_pqCost_le_global_bounded
        G Λ Ω s C c p q hs hp hp_top hΩ Γ hΓΛ Θ hN0 hM0
        productFun yprod Rprod R hRfin
        (fun i => (yind i : Lp ℂ p G.toWeakGridSpace.measure)) Rind
        (fun i hi => hprodRep i (hΓΛ i hi))
        (fun i hi => hprodFin i (hΓΛ i hi))
        hIndBlock
        (fun i hi k => hProdBlock i (hΓΛ i hi) k)
        htower_g hoverlap
    refine ⟨Y, S, ?_, hFinS, ?_, ?_⟩
    · change WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := p)
        (fun z => ∑ i ∈ Γ, (Θ i : ℂ) * productFun i z)
        (Y : Lp ℂ p G.toWeakGridSpace.measure)
      exact hRepS
    · change WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤ Cbound
      exact hCostS
    · intro k Q hcoeff
      obtain ⟨i, hiΓ, hQi⟩ := hSuppS k Q hcoeff
      exact ⟨i, hΓΛ i hiΓ, hQi⟩
  let yseq : ℕ → WeakGridSpace.BesovishSpace A q := fun n =>
    Classical.choose (hfiniteRep n)
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
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) (Sseq n) ≤ Cbound := by
    intro n
    exact (Classical.choose_spec (Classical.choose_spec (hfiniteRep n))).2.2.1
  have hSseq_supp : ∀ n k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ((Sseq n).block k).coeff Q ≠ 0 → ∃ i ∈ Λ, Q.1 ⊆ Ω i := by
    intro n k Q hcoeff
    exact (Classical.choose_spec (Classical.choose_spec (hfiniteRep n))).2.2.2 k Q hcoeff
  have hpartial_tendsto :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        Filter.Tendsto (fun n : ℕ => partialFun n z) Filter.atTop (𝓝 (h z)) := by
    filter_upwards [hseries] with z hseries_z
    have htendsto :=
      tendsto_initial_subtype_sums_of_hasSum
        (Λ := Λ)
        (a := fun i : ℕ =>
          (Θ i : ℂ) * (Ω i).indicator (fun _ => (1 : ℂ)) z * f z)
        hseries_z
    change Filter.Tendsto
      (fun n : ℕ =>
        ∑ i ∈ nonArchimedeanLambdaInitial Λ n,
          (Θ i : ℂ) * productFun i z)
      Filter.atTop (𝓝 (h z))
    simpa [productFun, mul_assoc] using htendsto
  simpa [A, Cbound, Cna] using
    exists_limit_representation_of_finite_sequence_with_support
      G s p q hs hp hp_top hCbound0
      (SupportProp := fun k Q => ∃ i ∈ Λ, Q.1 ⊆ Ω i)
      yseq Sseq hyseq_rep hSseq_fin hSseq_cost hSseq_supp hpartial_tendsto

/--
Non-Archimedean estimate for a non-uniform family of regular domains.

The domains may have different regularity constants.  The overlap hypothesis
therefore uses `regularDomainOverlapCostInfinite`, i.e. for every active source
cell `Q` it controls the weighted sum of the bounded-Besov indicator gauges of
the domains meeting `Q`.  The localization conclusion does not require
positivity: every nonzero output coefficient is supported in one of the active
domains.
-/
theorem regularDomains_nonArchimedean_indicator_multipliers
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cna : ℝ,
      0 ≤ Cna ∧
      ∀ (Λ : Set ℕ) (Ω : ℕ → Set α) (C c Θ : ℕ → ℝ) (N M : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
        0 ≤ N →
        (∀ i ∈ Λ, RegularDomain G (Ω i) (1 - p.toReal * s) (C i) (c i)) →
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) f
          (x : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ M) →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
        SouzaCanonicalRepresentation G s p hs hp hp_top R →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          ‖weightedAncestorCoeffSum G R Q‖ ≤ M) →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          ‖strictWeightedAncestorCoeffSum G R Q‖ ≤ M) →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (R.block k).coeff Q ≠ 0 →
            regularDomainOverlapCostInfinite G Λ Ω s C c Θ p q Q ≤
              ENNReal.ofReal N) →
        ∃ h : α → ℂ,
          ∃ absSum : α → ℝ,
            (∀ᵐ z ∂G.toWeakGridSpace.measure,
              f z ≠ 0 →
                HasSum
                  (fun i : {i // i ∈ Λ} =>
                    ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖)
                  (absSum z) ∧
                absSum z ≤ Cna * N) ∧
            (∀ᵐ z ∂G.toWeakGridSpace.measure,
              HasSum
                (fun i : {i // i ∈ Λ} =>
                  (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
                (h z)) ∧
            (∀ᵐ z ∂G.toWeakGridSpace.measure,
              ‖h z‖ ≤ Cna * N * ‖f z‖) ∧
            (∀ᵐ z ∂G.toWeakGridSpace.measure,
              ‖h z‖ ≤ Cna * N * M) ∧
            (∃ hmem : MemLp h p G.toWeakGridSpace.measure,
              ‖MemLp.toLp h hmem‖ ≤
                Cna * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖) ∧
            ∃ hmemInf : MemLp h (∞ : ℝ≥0∞) G.toWeakGridSpace.measure,
              ∃ y : WeakGridSpace.BesovishSpace
                  (souzaAtomFamily G s p hs hp hp_top) q,
                ∃ S : WeakGridSpace.LpGridRepresentation
                    (souzaAtomFamily G s p hs hp hp_top)
                    (y : Lp ℂ p G.toWeakGridSpace.measure),
                  WeakGridSpace.RepresentsFunction
                    (G := G.toWeakGridSpace) (p := p) h
                    (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
                  WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) S +
                      ‖MemLp.toLp h hmemInf‖ ≤
                    Cna * N *
                      (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R + M) ∧
                  (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
                    (S.block k).coeff Q ≠ 0 →
                      ∃ i ∈ Λ, Q.1 ⊆ Ω i) := by
  sorry

/--
Positive non-uniform variant.

The support conclusion is inherited from the general theorem.  The extra
assumptions `0 ≤ Θ i` and positivity of the source representation add the
positive-cone conclusion for the output representation.
-/
theorem regularDomains_nonArchimedean_indicator_multipliers_positive
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cna : ℝ,
      0 ≤ Cna ∧
      ∀ (Λ : Set ℕ) (Ω : ℕ → Set α) (C c Θ : ℕ → ℝ) (N M : ℝ)
        (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
        0 ≤ N →
        (∀ i ∈ Λ, RegularDomain G (Ω i) (1 - p.toReal * s) (C i) (c i)) →
        (∀ i ∈ Λ, 0 ≤ Θ i) →
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) f
          (x : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ M) →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
        SouzaCanonicalRepresentation G s p hs hp hp_top R →
        SouzaPositiveRepresentation G s p hs hp hp_top R →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          ‖weightedAncestorCoeffSum G R Q‖ ≤ M) →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          ‖strictWeightedAncestorCoeffSum G R Q‖ ≤ M) →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (R.block k).coeff Q ≠ 0 →
            regularDomainOverlapCostInfinite G Λ Ω s C c Θ p q Q ≤
              ENNReal.ofReal N) →
        ∃ h : α → ℂ,
          ∃ absSum : α → ℝ,
            (∀ᵐ z ∂G.toWeakGridSpace.measure,
              f z ≠ 0 →
                HasSum
                  (fun i : {i // i ∈ Λ} =>
                    ‖(Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z‖)
                  (absSum z) ∧
                absSum z ≤ Cna * N) ∧
            (∀ᵐ z ∂G.toWeakGridSpace.measure,
              HasSum
                (fun i : {i // i ∈ Λ} =>
                  (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
                (h z)) ∧
            (∀ᵐ z ∂G.toWeakGridSpace.measure,
              ‖h z‖ ≤ Cna * N * M) ∧
            ∃ hmemInf : MemLp h (∞ : ℝ≥0∞) G.toWeakGridSpace.measure,
              ∃ y : WeakGridSpace.BesovishSpace
                  (souzaAtomFamily G s p hs hp hp_top) q,
                ∃ S : WeakGridSpace.LpGridRepresentation
                    (souzaAtomFamily G s p hs hp hp_top)
                    (y : Lp ℂ p G.toWeakGridSpace.measure),
                  WeakGridSpace.RepresentsFunction
                    (G := G.toWeakGridSpace) (p := p) h
                    (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
                  WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) S +
                      ‖MemLp.toLp h hmemInf‖ ≤
                    Cna * N *
                      (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R + M) ∧
                  (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
                    (S.block k).coeff Q ≠ 0 →
                      ∃ i ∈ Λ, Q.1 ⊆ Ω i) ∧
                  SouzaConePositiveRepresentation G s p hs hp hp_top S := by
  sorry

/--
Uniform regular-family version.

The structural constant may depend on the regular family parameters.  The
overlap hypothesis only counts the active weights seen by each source cell.
-/
theorem regularFamily_nonArchimedean_indicator_multipliers
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c) :
    ∃ Cna : ℝ,
      0 ≤ Cna ∧
      ∀ (Θ : ℕ → ℝ) (N M : ℝ) (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
        0 ≤ N →
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) f
          (x : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ M) →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
        SouzaCanonicalRepresentation G s p hs hp hp_top R →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          ‖weightedAncestorCoeffSum G R Q‖ ≤ M) →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          ‖strictWeightedAncestorCoeffSum G R Q‖ ≤ M) →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (R.block k).coeff Q ≠ 0 →
            regularFamilyOverlapCostInfinite G Λ Ω Θ Q ≤ ENNReal.ofReal N) →
        ∃ h : α → ℂ,
          ∃ hmemInf : MemLp h (∞ : ℝ≥0∞) G.toWeakGridSpace.measure,
            ∃ y : WeakGridSpace.BesovishSpace
                (souzaAtomFamily G s p hs hp hp_top) q,
              ∃ S : WeakGridSpace.LpGridRepresentation
                  (souzaAtomFamily G s p hs hp hp_top)
                  (y : Lp ℂ p G.toWeakGridSpace.measure),
                WeakGridSpace.RepresentsFunction
                  (G := G.toWeakGridSpace) (p := p) h
                  (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
                (∀ᵐ z ∂G.toWeakGridSpace.measure,
                  HasSum
                    (fun i : {i // i ∈ Λ} =>
                      (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
                    (h z)) ∧
                (∀ᵐ z ∂G.toWeakGridSpace.measure,
                  ‖h z‖ ≤ Cna * N * M) ∧
                WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) S +
                    ‖MemLp.toLp h hmemInf‖ ≤
                  Cna * N *
                    (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R + M) ∧
                (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
                  (S.block k).coeff Q ≠ 0 →
                    ∃ i ∈ Λ, Q.1 ⊆ Ω i) := by
  classical
  let Cbase : ℝ :=
    ((2 : ℝ) ^ (p.toReal - 1)) ^ (1 / p.toReal) *
      (regularFamilyGeomRootCost G Λ Ω s C c p q + 1)
  let Cna : ℝ := Cbase + 1
  have hCbase0 : 0 ≤ Cbase := by
    exact mul_nonneg
      (Real.rpow_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) _)
      (add_nonneg
        (regularFamilyGeomRootCost_nonneg
          (G := G) (Λ := Λ) (Ω := Ω) (s := s) (C := C) (c := c)
          (p := p) (q := q) hΩ)
        zero_le_one)
  refine ⟨Cna, add_nonneg hCbase0 zero_le_one, ?_⟩
  intro Θ N M f x R hN0 hRep hfbdd hRfin _hcanon htower_g _hstrict hoverlap
  let h : α → ℂ := fun z =>
    ∑' i : {i // i ∈ Λ},
      (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z
  have hM0 : 0 ≤ M := regularFamilyRestriction_bound_nonneg G hfbdd
  have hRcost0 : 0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) R :=
    WeakGridSpace.LpGridRepresentation.pqCost_nonneg R
  have hbounds :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        HasSum
          (fun i : {i // i ∈ Λ} =>
            (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
          (h z) ∧
        ‖h z‖ ≤ N * ‖f z‖ ∧
        ‖h z‖ ≤ N * M := by
    simpa [h] using
      regularFamily_weightedIndicator_product_tsum_bounds_ae
        G Λ Ω s C c p q hs hp hp_top hΩ Θ hN0 f x R hRep hfbdd hoverlap
  have hseries :
      ∀ᵐ z ∂G.toWeakGridSpace.measure,
        HasSum
          (fun i : {i // i ∈ Λ} =>
            (Θ i.1 : ℂ) * (Ω i.1).indicator (fun _ => (1 : ℂ)) z * f z)
          (h z) := by
    filter_upwards [hbounds] with z hz
    exact hz.1
  have hnormNM :
      ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖h z‖ ≤ N * M := by
    filter_upwards [hbounds] with z hz
    exact hz.2.2
  have hnormC :
      ∀ᵐ z ∂G.toWeakGridSpace.measure, ‖h z‖ ≤ Cna * N * M := by
    filter_upwards [hnormNM] with z hz
    have hNM0 : 0 ≤ N * M := mul_nonneg hN0 hM0
    calc
      ‖h z‖ ≤ N * M := hz
      _ ≤ Cna * (N * M) := by
        exact le_mul_of_one_le_left hNM0 (by dsimp [Cna]; nlinarith [hCbase0])
      _ = Cna * N * M := by ring
  obtain ⟨y, S, hRepS, hFinS, hCostS, hSuppS⟩ :=
    exists_regularFamily_nonArchimedean_infinite_besov_representation
      G Λ Ω s C c p q hs hs_lt_inv hp hp_top hΩ Θ hN0
      f h x R hRep hfbdd hRfin htower_g hoverlap hseries
  have hNM0 : 0 ≤ N * M := mul_nonneg hN0 hM0
  obtain ⟨hmemInf, hInfNorm⟩ :=
    linftyMemLp_and_norm_le_of_representsFunction_bound
      G p hNM0 hRepS hnormNM
  refine ⟨h, hmemInf, y, S, hRepS, hseries, hnormC, hFinS, ?_, hSuppS⟩
  have hA0 :
      0 ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := q) R + M :=
    add_nonneg hRcost0 hM0
  have hcost_final :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) S +
          ‖MemLp.toLp h hmemInf‖ ≤
        Cna * N *
          (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R + M) := by
    dsimp [Cna, Cbase] at hCostS ⊢
    nlinarith [hCostS, hInfNorm, hCbase0, hN0, hM0, hRcost0, hA0]
  exact hcost_final

/-- Positive uniform regular-family variant. -/
theorem regularFamily_nonArchimedean_indicator_multipliers_positive
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s C c : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hΩ : RegularFamily G Λ Ω (1 - p.toReal * s) C c) :
    ∃ Cna : ℝ,
      0 ≤ Cna ∧
      ∀ (Θ : ℕ → ℝ) (N M : ℝ) (f : α → ℂ)
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (R : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
        0 ≤ N →
        (∀ i ∈ Λ, 0 ≤ Θ i) →
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) f
          (x : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖f z‖ ≤ M) →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
        SouzaCanonicalRepresentation G s p hs hp hp_top R →
        SouzaPositiveRepresentation G s p hs hp hp_top R →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          ‖weightedAncestorCoeffSum G R Q‖ ≤ M) →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          ‖strictWeightedAncestorCoeffSum G R Q‖ ≤ M) →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (R.block k).coeff Q ≠ 0 →
            regularFamilyOverlapCostInfinite G Λ Ω Θ Q ≤ ENNReal.ofReal N) →
        ∃ h : α → ℂ,
          ∃ hmemInf : MemLp h (∞ : ℝ≥0∞) G.toWeakGridSpace.measure,
            ∃ y : WeakGridSpace.BesovishSpace
                (souzaAtomFamily G s p hs hp hp_top) q,
              ∃ S : WeakGridSpace.LpGridRepresentation
                  (souzaAtomFamily G s p hs hp hp_top)
                  (y : Lp ℂ p G.toWeakGridSpace.measure),
                WeakGridSpace.RepresentsFunction
                  (G := G.toWeakGridSpace) (p := p) h
                  (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
                (∀ᵐ z ∂G.toWeakGridSpace.measure,
                  ‖h z‖ ≤ Cna * N * M) ∧
                WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
                WeakGridSpace.LpGridRepresentation.pqCost (q := q) S +
                    ‖MemLp.toLp h hmemInf‖ ≤
                  Cna * N *
                    (WeakGridSpace.LpGridRepresentation.pqCost (q := q) R + M) ∧
                (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
                  (S.block k).coeff Q ≠ 0 →
                    ∃ i ∈ Λ, Q.1 ⊆ Ω i) ∧
                SouzaConePositiveRepresentation G s p hs hp hp_top S := by
  sorry

end

end GoodGridSpace
