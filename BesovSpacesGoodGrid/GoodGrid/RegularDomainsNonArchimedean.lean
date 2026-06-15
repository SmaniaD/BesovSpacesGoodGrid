import BesovSpacesGoodGrid.GoodGrid.RegularDomains

/-!
# Non-Archimedean regular-domain multiplier statements

This file records the regular-domain analogue of the non-Archimedean
multiplier estimates proved for strongly regular domains.

The statements are intentionally split into two styles.

* The non-uniform version allows each `Ω i` to have its own regularity
  constants `C i`, `c i`.  The local overlap hypothesis therefore weights each
  domain by `regularDomainIndicatorCost`.
* The uniform version assumes one `RegularFamily`; the local overlap only
  counts the active weights, while the family regularity is part of the
  structural constant.

In both styles the support/localization conclusion is part of the general
statement.  Positivity is only an extra conclusion of the positive variants.
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
met by `Q`, multiplied by the individual regular-domain indicator cost of
that domain.
-/
noncomputable def regularDomainOverlapCostInfinite
    (G : GoodGridSpace (α := α)) (Λ : Set ℕ) (Ω : ℕ → Set α)
    (s : ℝ) (C c Θ : ℕ → ℝ) (p q : ℝ≥0∞)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℝ≥0∞ := by
  classical
  exact ∑' i : {i // i ∈ Λ},
    if (Q.1 ∩ Ω i.1).Nonempty then
      ENNReal.ofReal
        (|Θ i.1| * regularDomainIndicatorCost G (Ω i.1) s (C i.1) (c i.1) p q)
    else 0

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
Non-Archimedean estimate for a non-uniform family of regular domains.

The domains may have different regularity constants.  The overlap hypothesis
therefore uses `regularDomainOverlapCostInfinite`.  The localization conclusion
does not require positivity: every nonzero output coefficient is supported in
one of the active domains.
-/
theorem regularDomains_nonArchimedean_indicator_multipliers
    (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cna : ℝ,
      0 ≤ Cna ∧
      ∀ (Λ : Set ℕ) (Ω : ℕ → Set α) (C c Θ : ℕ → ℝ) (N : ℝ)
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
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
        SouzaCanonicalRepresentation G s p hs hp hp_top R →
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
            (∃ hmem : MemLp h p G.toWeakGridSpace.measure,
              ‖MemLp.toLp h hmem‖ ≤
                Cna * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖) ∧
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
                  Cna * N *
                    WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
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
      ∀ (Λ : Set ℕ) (Ω : ℕ → Set α) (C c Θ : ℕ → ℝ) (N : ℝ)
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
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
        SouzaCanonicalRepresentation G s p hs hp hp_top R →
        SouzaPositiveRepresentation G s p hs hp hp_top R →
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
                  Cna * N *
                    WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
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
      ∀ (Θ : ℕ → ℝ) (N : ℝ) (f : α → ℂ)
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
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (R.block k).coeff Q ≠ 0 →
            regularFamilyOverlapCostInfinite G Λ Ω Θ Q ≤ ENNReal.ofReal N) →
        ∃ h : α → ℂ,
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
              WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) S ∧
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) S ≤
                Cna * N *
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
              (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
                (S.block k).coeff Q ≠ 0 →
                  ∃ i ∈ Λ, Q.1 ⊆ Ω i) := by
  sorry

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
      ∀ (Θ : ℕ → ℝ) (N : ℝ) (f : α → ℂ)
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
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) R →
        SouzaCanonicalRepresentation G s p hs hp hp_top R →
        SouzaPositiveRepresentation G s p hs hp hp_top R →
        (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          (R.block k).coeff Q ≠ 0 →
            regularFamilyOverlapCostInfinite G Λ Ω Θ Q ≤ ENNReal.ofReal N) →
        ∃ h : α → ℂ,
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
                Cna * N *
                  WeakGridSpace.LpGridRepresentation.pqCost (q := q) R ∧
              (∀ k (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
                (S.block k).coeff Q ≠ 0 →
                  ∃ i ∈ Λ, Q.1 ⊆ Ω i) ∧
              SouzaConePositiveRepresentation G s p hs hp hp_top S := by
  sorry

end

end GoodGridSpace
