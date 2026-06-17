import BesovSpacesGoodGrid.GoodGrid.RegularDomains

/-!
# Alternative description of `B^s_{1,1}`

This file formalizes the setup of the manuscript section
*A remarkable description of `B^s_{1,1}`*.

For `0 < s < 1`, and for a chosen family `𝓦hat` of regular domains satisfying
`𝓟 ⊆ 𝓦hat ⊆ 𝓦`, we introduce the concrete representation space whose atoms are
the normalized indicators

`1_Ω / μ(Ω)^(1 - s)`.

The final proposition is stated in the representative-function form needed by
the current library: the domain representation is a concrete function, while
the Souza Besov space is modeled as a subtype of `L^1`.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/-- The exponent `1 / (1 - s)` used by the alternative description. -/
noncomputable def domainEndpointExponent (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - s)⁻¹)

/-- The set of all grid cells, viewed only as measurable subsets. -/
def gridCellSet (G : GoodGridSpace (α := α)) : Set (Set α) :=
  { Ω | ∃ k : ℕ, Ω ∈ G.toWeakGridSpace.grid.partitions k }

/-- The regular domains appearing in the endpoint description. -/
def regularDomainClass
    (G : GoodGridSpace (α := α)) (s C c : ℝ) : Set (Set α) :=
  { Ω | Nonempty (RegularDomain G Ω (1 - s) C c) }

/--
The formal version of `𝓟 ⊆ 𝓦hat ⊆ 𝓦`, where `𝓦` is the family of
`(1 - s, C, c)`-regular domains.
-/
structure AdmissibleDomainClass
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α)) : Prop where
  /-- Every grid cell is allowed as an atom domain. -/
  grid_subset : gridCellSet G ⊆ 𝓦hat
  /-- Every allowed set is a regular domain with the fixed constants. -/
  regular_subset : 𝓦hat ⊆ regularDomainClass G s C c

/--
The normalized indicator `1_Ω / μ(Ω)^(1 - s)`, written as
`μ(Ω)^(s - 1) 1_Ω`.
-/
def normalizedDomainIndicator
    (G : GoodGridSpace (α := α)) (s : ℝ) (Ω : Set α) : α → ℂ :=
  fun z => Ω.indicator
    (fun _ => (((G.grid.μ Ω).toReal ^ (s - 1) : ℝ) : ℂ)) z

/--
A concrete representation

`f = ∑ i, c_i * 1_{Ω_i} / μ(Ω_i)^(1 - s)`

with `Ω_i ∈ 𝓦hat` and `∑ ‖c_i‖ < ∞`.
-/
structure DomainAtomicRepresentation
    (G : GoodGridSpace (α := α)) (s : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)] (f : α → ℂ) where
  /-- The domains `Ω_i` in the representation. -/
  domain : ℕ → Set α
  /-- Each domain belongs to the chosen family `𝓦hat`. -/
  domain_mem : ∀ i, domain i ∈ 𝓦hat
  /-- The scalar coefficients `c_i`. -/
  coeff : ℕ → ℂ
  /-- The concrete function belongs to the endpoint `L^{1/(1-s)}` space. -/
  memLp : MemLp f (domainEndpointExponent s) G.grid.μ
  /-- Each term belongs to the same endpoint `L^p` space. -/
  term_memLp :
    ∀ i, MemLp
      (fun z => coeff i * normalizedDomainIndicator G s (domain i) z)
      (domainEndpointExponent s) G.grid.μ
  /-- The series of normalized indicators represents `f` in endpoint `L^p`. -/
  hasSum :
    HasSum
      (fun i =>
        MemLp.toLp
          (fun z => coeff i * normalizedDomainIndicator G s (domain i) z)
          (term_memLp i))
      (MemLp.toLp f memLp)
  /-- The coefficient sequence is absolutely summable. -/
  coeff_summable : Summable fun i => ‖coeff i‖

namespace DomainAtomicRepresentation

variable {G : GoodGridSpace (α := α)} {s : ℝ} {𝓦hat : Set (Set α)}
variable [Fact (1 ≤ domainEndpointExponent s)] {f : α → ℂ}

/-- The cost of a domain representation is the `ℓ¹` norm of its coefficients. -/
noncomputable def coeffCost
    (R : DomainAtomicRepresentation G s 𝓦hat f) : ℝ :=
  ∑' i, ‖R.coeff i‖

/-- Representation costs are nonnegative. -/
theorem coeffCost_nonneg
    (R : DomainAtomicRepresentation G s 𝓦hat f) :
    0 ≤ R.coeffCost := by
  simpa [coeffCost] using tsum_nonneg fun i => norm_nonneg (R.coeff i)

end DomainAtomicRepresentation

/-- Membership in the alternative `B^{1-s}` space. -/
def DomainBesovSpace
    (G : GoodGridSpace (α := α)) (s : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)] (f : α → ℂ) : Prop :=
  Nonempty (DomainAtomicRepresentation G s 𝓦hat f)

/-- Candidate upper bounds for the alternative representation gauge. -/
def domainBesovGaugeUpperSet
    (G : GoodGridSpace (α := α)) (s : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)] (f : α → ℂ) : Set ℝ :=
  { r | ∃ R : DomainAtomicRepresentation G s 𝓦hat f,
      R.coeffCost ≤ r }

/--
The alternative `B^{1-s}` gauge: the infimum of `∑ ‖c_i‖` over all normalized
regular-domain representations.
-/
noncomputable def domainBesovGauge
    (G : GoodGridSpace (α := α)) (s : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)] (f : α → ℂ) : ℝ :=
  sInf (domainBesovGaugeUpperSet G s 𝓦hat f)

theorem domainBesovGaugeUpperSet_bddBelow
    (G : GoodGridSpace (α := α)) (s : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)] (f : α → ℂ) :
    BddBelow (domainBesovGaugeUpperSet G s 𝓦hat f) := by
  refine ⟨0, ?_⟩
  intro r hr
  rcases hr with ⟨R, hR⟩
  exact le_trans R.coeffCost_nonneg hR

/-- The gauge is bounded by the cost of any concrete representation. -/
theorem domainBesovGauge_le_coeffCost
    (G : GoodGridSpace (α := α)) (s : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)] {f : α → ℂ}
    (R : DomainAtomicRepresentation G s 𝓦hat f) :
    domainBesovGauge G s 𝓦hat f ≤ R.coeffCost := by
  unfold domainBesovGauge
  exact csInf_le
    (domainBesovGaugeUpperSet_bddBelow G s 𝓦hat f)
    ⟨R, le_rfl⟩

/-- The upper-bound set for the alternative gauge is nonempty when `f` has a
domain representation. -/
theorem domainBesovGaugeUpperSet_nonempty
    (G : GoodGridSpace (α := α)) (s : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)] {f : α → ℂ}
    (hf : DomainBesovSpace G s 𝓦hat f) :
    (domainBesovGaugeUpperSet G s 𝓦hat f).Nonempty := by
  rcases hf with ⟨R⟩
  exact ⟨R.coeffCost, ⟨R, le_rfl⟩⟩

/-- Choose a domain representation whose coefficient cost is within `ε` of the
alternative gauge. -/
theorem exists_domainAtomicRepresentation_coeffCost_lt_gauge_add
    (G : GoodGridSpace (α := α)) (s : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)] {f : α → ℂ}
    (hf : DomainBesovSpace G s 𝓦hat f) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : DomainAtomicRepresentation G s 𝓦hat f,
      R.coeffCost < domainBesovGauge G s 𝓦hat f + ε := by
  have hlt :
      sInf (domainBesovGaugeUpperSet G s 𝓦hat f) <
        sInf (domainBesovGaugeUpperSet G s 𝓦hat f) + ε :=
    lt_add_of_pos_right _ hε
  rcases exists_lt_of_csInf_lt
      (domainBesovGaugeUpperSet_nonempty G s 𝓦hat hf) hlt with
    ⟨r, hr, hrlt⟩
  rcases hr with ⟨R, hR⟩
  exact ⟨R, lt_of_le_of_lt hR (by simpa [domainBesovGauge] using hrlt)⟩

/-- The Souza `B^s_{1,1}` space associated to the good grid. -/
abbrev SouzaBesov11
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s) :=
  WeakGridSpace.BesovishSpace
    (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
    (1 : ℝ≥0∞)

/--
The regular-domain indicator estimate `(estG)` specialized to `p = q = 1`.
-/
theorem regularDomain_indicator_souzaBesov11_bound
    (G : GoodGridSpace (α := α)) (Ω : Set α) (s C c : ℝ)
    (hs : 0 < s) (hs_lt_one : s < 1)
    (hΩ : RegularDomain G Ω (1 - s) C c) :
    ∃ y : SouzaBesov11 G s hs,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (Ω.indicator fun _ => (1 : ℂ))
        (y : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
          (1 : ℝ≥0∞) y ≤
        regularDomainIndicatorCost G Ω s C c
          (1 : ℝ≥0∞) (1 : ℝ≥0∞) := by
  have hs_lt_inv : s < ((1 : ℝ≥0∞).toReal)⁻¹ := by
    simpa using hs_lt_one
  have hΩ' : RegularDomain G Ω
      (1 - (1 : ℝ≥0∞).toReal * s) C c := by
    simpa using hΩ
  simpa [SouzaBesov11] using
    regularDomain_indicator_besov_norm_bound_all
      G Ω s C c (1 : ℝ≥0∞) (1 : ℝ≥0∞)
      hs hs_lt_inv le_rfl ENNReal.one_ne_top hΩ'

/--
The normalized indicator of a regular domain belongs to Souza `B^s_{1,1}`.

This is the reusable term-level estimate behind the inclusion
`B^{1-s} ⊆ B^s_{1,1}`.
-/
theorem regularDomain_normalizedIndicator_souzaBesov11_bound
    (G : GoodGridSpace (α := α)) (Ω : Set α) (s C c : ℝ)
    (hs : 0 < s) (hs_lt_one : s < 1)
    (hΩ : RegularDomain G Ω (1 - s) C c) :
    ∃ y : SouzaBesov11 G s hs,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (normalizedDomainIndicator G s Ω)
        (y : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
          (1 : ℝ≥0∞) y ≤
        (G.grid.μ Ω).toReal ^ (s - 1) *
          regularDomainIndicatorCost G Ω s C c
            (1 : ℝ≥0∞) (1 : ℝ≥0∞) := by
  classical
  let A := souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top
  let scale : ℂ := (((G.grid.μ Ω).toReal ^ (s - 1) : ℝ) : ℂ)
  obtain ⟨y, hyrep, hycost⟩ :=
    regularDomain_indicator_souzaBesov11_bound G Ω s C c hs hs_lt_one hΩ
  refine ⟨scale • y, ?_, ?_⟩
  · have hrep :=
      WeakGridSpace.representsFunction_smul
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        scale hyrep
    have hfun :
        (fun z => scale * Ω.indicator (fun _ => (1 : ℂ)) z) =
          normalizedDomainIndicator G s Ω := by
      funext z
      by_cases hz : z ∈ Ω
      · simp [normalizedDomainIndicator, scale, Set.indicator_of_mem hz]
      · simp [normalizedDomainIndicator, scale, Set.indicator_of_notMem hz]
    simpa [hfun] using hrep
  · have hA :
        WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations
          (A := A) (1 : ℝ≥0∞) :=
      WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A (1 : ℝ≥0∞)
    have hnorm :
        WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) (scale • y) =
          ‖scale‖ * WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) y := by
      exact WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq
        (A := A) (q := (1 : ℝ≥0∞)) ENNReal.one_ne_top hA scale y
    have hscale_norm : ‖scale‖ = (G.grid.μ Ω).toReal ^ (s - 1) := by
      simp [scale, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    rw [hnorm, hscale_norm]
    exact mul_le_mul_of_nonneg_left hycost
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/--
For `p = q = 1`, the regular-domain indicator estimate is uniform after the
normalization `1_Ω / μ(Ω)^(1 - s)`.
-/
theorem regularDomain_normalizedIndicatorCost_eq
    (G : GoodGridSpace (α := α)) (Ω : Set α) (s C c : ℝ)
    (hΩ : RegularDomain G Ω (1 - s) C c) :
    (G.grid.μ Ω).toReal ^ (s - 1) *
        regularDomainIndicatorCost G Ω s C c
          (1 : ℝ≥0∞) (1 : ℝ≥0∞) =
      C / (1 - c) := by
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hΩfin : G.grid.μ Ω ≠ ∞ := measure_ne_top _ _
  have hμpos : 0 < (G.grid.μ Ω).toReal := by
    obtain ⟨W, hWsub⟩ := firstContainedLevel_spec G hΩ.contains_cell
    exact ENNReal.toReal_pos
      (lt_of_lt_of_le (G.grid.positive_measure _ W.1 W.2) (measure_mono hWsub)).ne'
      hΩfin
  have hcost :
      regularDomainIndicatorCost G Ω s C c
          (1 : ℝ≥0∞) (1 : ℝ≥0∞) =
        C / (1 - c) * (G.grid.μ Ω).toReal ^ (1 - s) := by
    simp only [regularDomainIndicatorCost, ENNReal.one_ne_top, if_false,
      ENNReal.toReal_one, one_div_one, Real.rpow_one]
  rw [hcost]
  calc
    (G.grid.μ Ω).toReal ^ (s - 1) *
        (C / (1 - c) * (G.grid.μ Ω).toReal ^ (1 - s))
        = C / (1 - c) *
            ((G.grid.μ Ω).toReal ^ (s - 1) *
              (G.grid.μ Ω).toReal ^ (1 - s)) := by ring
    _ = C / (1 - c) * (G.grid.μ Ω).toReal ^ (0 : ℝ) := by
      rw [← Real.rpow_add hμpos]
      congr 1
      ring_nf
    _ = C / (1 - c) := by rw [Real.rpow_zero, mul_one]

/--
Choose Souza representatives for all terms in a domain atomic representation,
with the endpoint constant `C / (1 - c)` already factored out.
-/
theorem domainAtomicRepresentation_terms_souzaBesov11_uniform_bound
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s) (hs_lt_one : s < 1)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat)
    {f : α → ℂ} (R : DomainAtomicRepresentation G s 𝓦hat f) :
    ∃ y : ℕ → SouzaBesov11 G s hs,
      (∀ i, WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
        (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure)) ∧
      (∀ i,
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
            (1 : ℝ≥0∞) (y i) ≤
          C / (1 - c) * ‖R.coeff i‖) := by
  classical
  let A := souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top
  have hdom : ∀ i, RegularDomain G (R.domain i) (1 - s) C c := by
    intro i
    exact Classical.choice (h𝓦.regular_subset (R.domain_mem i))
  have hterm :
      ∀ i, ∃ y : SouzaBesov11 G s hs,
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
          (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
          (y : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) y ≤
          C / (1 - c) * ‖R.coeff i‖ := by
    intro i
    obtain ⟨y, hyrep, hycost⟩ :=
      regularDomain_normalizedIndicator_souzaBesov11_bound
        G (R.domain i) s C c hs hs_lt_one (hdom i)
    refine ⟨R.coeff i • y, ?_, ?_⟩
    · exact WeakGridSpace.representsFunction_smul
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (R.coeff i) hyrep
    · have hA :
          WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations
            (A := A) (1 : ℝ≥0∞) :=
        WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A (1 : ℝ≥0∞)
      have hsmul :
          WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) (R.coeff i • y) =
            ‖R.coeff i‖ * WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) y := by
        exact WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq
          (A := A) (q := (1 : ℝ≥0∞)) ENNReal.one_ne_top hA (R.coeff i) y
      rw [hsmul]
      have hcost_eq :
          (G.grid.μ (R.domain i)).toReal ^ (s - 1) *
              regularDomainIndicatorCost G (R.domain i) s C c
                (1 : ℝ≥0∞) (1 : ℝ≥0∞) =
            C / (1 - c) :=
        regularDomain_normalizedIndicatorCost_eq G (R.domain i) s C c (hdom i)
      calc
        ‖R.coeff i‖ * WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) y
            ≤ ‖R.coeff i‖ *
                ((G.grid.μ (R.domain i)).toReal ^ (s - 1) *
                  regularDomainIndicatorCost G (R.domain i) s C c
                    (1 : ℝ≥0∞) (1 : ℝ≥0∞)) :=
              mul_le_mul_of_nonneg_left hycost (norm_nonneg (R.coeff i))
        _ = ‖R.coeff i‖ * (C / (1 - c)) := by rw [hcost_eq]
        _ = C / (1 - c) * ‖R.coeff i‖ := by ring
  let y : ℕ → SouzaBesov11 G s hs := fun i => Classical.choose (hterm i)
  refine ⟨y, ?_, ?_⟩
  · intro i
    exact (Classical.choose_spec (hterm i)).1
  · intro i
    exact (Classical.choose_spec (hterm i)).2

/--
The coherent Souza representatives of a domain atomic representation satisfy
the expected cost estimate for every finite partial sum.
-/
theorem domainAtomicRepresentation_terms_souzaBesov11_finset_bound
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s) (hs_lt_one : s < 1)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat)
    {f : α → ℂ} (R : DomainAtomicRepresentation G s 𝓦hat f) :
    ∃ y : ℕ → SouzaBesov11 G s hs,
      (∀ i, WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
        (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure)) ∧
      (∀ i,
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
            (1 : ℝ≥0∞) (y i) ≤
          C / (1 - c) * ‖R.coeff i‖) ∧
      (∀ F : Finset ℕ,
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
            (1 : ℝ≥0∞) (∑ i ∈ F, y i) ≤
          |C / (1 - c)| * ∑ i ∈ F, ‖R.coeff i‖) := by
  classical
  obtain ⟨y, hyrep, hycost⟩ :=
    domainAtomicRepresentation_terms_souzaBesov11_uniform_bound
      G s C c 𝓦hat hs hs_lt_one h𝓦 R
  let A := souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top
  have hycost_abs :
      ∀ i, WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) (y i) ≤
        |C / (1 - c)| * ‖R.coeff i‖ := by
    intro i
    exact (hycost i).trans
      (mul_le_mul_of_nonneg_right (le_abs_self (C / (1 - c))) (norm_nonneg (R.coeff i)))
  refine ⟨y, hyrep, hycost, ?_⟩
  intro F
  have hA :
      WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations
        (A := A) (1 : ℝ≥0∞) :=
    WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A (1 : ℝ≥0∞)
  refine Finset.induction_on F ?base ?step
  · simp only [Finset.sum_empty]
    have hzero_eq :
        WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞)
            (0 : SouzaBesov11 G s hs) = 0 := by
      have hsmul :=
        WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq
          (A := A) (q := (1 : ℝ≥0∞)) ENNReal.one_ne_top hA
          (0 : ℂ) (0 : SouzaBesov11 G s hs)
      simpa only [zero_smul, norm_zero, zero_mul] using hsmul
    rw [hzero_eq]
    rw [mul_zero]
  · intro a S ha hS
    simp only [Finset.sum_insert ha]
    calc
      WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞)
          (y a + ∑ i ∈ S, y i)
          ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) (y a) +
              WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞)
                (∑ i ∈ S, y i) :=
        WeakGridSpace.BesovishSpace.Norm_Costpq_add_le
          (A := A) (q := (1 : ℝ≥0∞)) ENNReal.one_ne_top hA
          (y a) (∑ i ∈ S, y i)
      _ ≤ |C / (1 - c)| * ‖R.coeff a‖ +
            |C / (1 - c)| * ∑ i ∈ S, ‖R.coeff i‖ :=
        add_le_add (hycost_abs a) hS
      _ = |C / (1 - c)| * (‖R.coeff a‖ + ∑ i ∈ S, ‖R.coeff i‖) := by ring

/--
The finite tails of the coherent Souza representatives have arbitrarily small
cost.  This is the Cauchy estimate needed for the infinite sum.
-/
theorem domainAtomicRepresentation_terms_souzaBesov11_tail_cost_tendsto_zero
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s) (hs_lt_one : s < 1)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat)
    {f : α → ℂ} (R : DomainAtomicRepresentation G s 𝓦hat f) :
    ∃ y : ℕ → SouzaBesov11 G s hs,
      (∀ i, WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
        (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure)) ∧
      (∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ M ≥ N,
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
            (1 : ℝ≥0∞) (∑ i ∈ Finset.Ico N M, y i) < ε) := by
  classical
  obtain ⟨y, hyrep, _hycost, hfin⟩ :=
    domainAtomicRepresentation_terms_souzaBesov11_finset_bound
      G s C c 𝓦hat hs hs_lt_one h𝓦 R
  refine ⟨y, hyrep, ?_⟩
  let K : ℝ := |C / (1 - c)|
  have hmajor_nonneg : ∀ i, 0 ≤ K * ‖R.coeff i‖ := by
    intro i
    exact mul_nonneg (abs_nonneg _) (norm_nonneg (R.coeff i))
  have hmajor_sum : Summable fun i => K * ‖R.coeff i‖ :=
    R.coeff_summable.mul_left K
  have htail :=
    WeakGridSpace.summable_Ico_tail_tendsto_zero
      (a := fun i => K * ‖R.coeff i‖) hmajor_nonneg hmajor_sum
  intro ε hε
  rcases htail ε hε with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro N hN M hNM
  have hcost := hfin (Finset.Ico N M)
  have hfactor :
      K * (∑ i ∈ Finset.Ico N M, ‖R.coeff i‖) =
        ∑ i ∈ Finset.Ico N M, K * ‖R.coeff i‖ := by
    rw [Finset.mul_sum]
  exact lt_of_le_of_lt (hcost.trans_eq hfactor) (hN₀ N hN M hNM)

/--
The coherent Souza representatives have the same `L^1` sum as the original
domain atomic representation, after the natural finite-measure inclusion from
`L^{1/(1-s)}` to `L^1`.
-/
theorem domainAtomicRepresentation_terms_souzaBesov11_Lp_hasSum
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s) (hs_lt_one : s < 1)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat)
    {f : α → ℂ} (R : DomainAtomicRepresentation G s 𝓦hat f) :
    ∃ y : ℕ → SouzaBesov11 G s hs,
      (∀ i, WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
        (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure)) ∧
      HasSum
        (fun i => (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure))
        (WeakGridSpace.LpGridRepresentation.lpInclusion
          (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
          (t := domainEndpointExponent s)
          ENNReal.one_ne_top ENNReal.ofReal_ne_top Fact.out
          (MemLp.toLp f R.memLp)) := by
  classical
  obtain ⟨y, hyrep, _hycost⟩ :=
    domainAtomicRepresentation_terms_souzaBesov11_uniform_bound
      G s C c 𝓦hat hs hs_lt_one h𝓦 R
  refine ⟨y, hyrep, ?_⟩
  let I : Lp ℂ (domainEndpointExponent s) G.toWeakGridSpace.measure →L[ℂ]
      Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure :=
    WeakGridSpace.LpGridRepresentation.lpInclusion
      (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
      (t := domainEndpointExponent s)
      ENNReal.one_ne_top ENNReal.ofReal_ne_top Fact.out
  have hmap :
      HasSum
        (fun i => I
          (MemLp.toLp
            (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
            (R.term_memLp i)))
        (I (MemLp.toLp f R.memLp)) := by
    exact R.hasSum.mapL I
  refine HasSum.congr_fun hmap ?_
  intro i
  apply Lp.ext
  have hleft :
      ((I
          (MemLp.toLp
            (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
            (R.term_memLp i)) :
        Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) : α → ℂ) =ᵐ[G.toWeakGridSpace.measure]
        (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z) := by
    exact
      (WeakGridSpace.LpGridRepresentation.coeFn_lpInclusion
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (t := domainEndpointExponent s)
        ENNReal.one_ne_top ENNReal.ofReal_ne_top Fact.out
        (MemLp.toLp
          (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
          (R.term_memLp i))).trans
        (MemLp.coeFn_toLp (R.term_memLp i))
  exact (hyrep i).trans hleft.symm

/--
If a chosen family of Souza elements represents the concrete terms of a domain
atomic representation, then its sum in ambient `L¹` is the image of the original
`L^{1/(1-s)}` sum under the finite-measure inclusion.
-/
theorem domainAtomicRepresentation_terms_souzaBesov11_Lp_hasSum_of_rep
    (G : GoodGridSpace (α := α)) (s : ℝ) {𝓦hat : Set (Set α)}
    [Fact (1 ≤ domainEndpointExponent s)]
    {f : α → ℂ} (R : DomainAtomicRepresentation G s 𝓦hat f)
    (hs : 0 < s)
    (y : ℕ → SouzaBesov11 G s hs)
    (hyrep : ∀ i, WeakGridSpace.RepresentsFunction
      (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
      (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
      (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure)) :
    HasSum
      (fun i => (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure))
      (WeakGridSpace.LpGridRepresentation.lpInclusion
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (t := domainEndpointExponent s)
        ENNReal.one_ne_top ENNReal.ofReal_ne_top Fact.out
        (MemLp.toLp f R.memLp)) := by
  classical
  let I : Lp ℂ (domainEndpointExponent s) G.toWeakGridSpace.measure →L[ℂ]
      Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure :=
    WeakGridSpace.LpGridRepresentation.lpInclusion
      (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
      (t := domainEndpointExponent s)
      ENNReal.one_ne_top ENNReal.ofReal_ne_top Fact.out
  have hmap :
      HasSum
        (fun i => I
          (MemLp.toLp
            (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
            (R.term_memLp i)))
        (I (MemLp.toLp f R.memLp)) := by
    exact R.hasSum.mapL I
  refine HasSum.congr_fun hmap ?_
  intro i
  apply Lp.ext
  have hleft :
      ((I
          (MemLp.toLp
            (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
            (R.term_memLp i)) :
        Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) : α → ℂ) =ᵐ[G.toWeakGridSpace.measure]
        (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z) := by
    exact
      (WeakGridSpace.LpGridRepresentation.coeFn_lpInclusion
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (t := domainEndpointExponent s)
        ENNReal.one_ne_top ENNReal.ofReal_ne_top Fact.out
        (MemLp.toLp
          (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
          (R.term_memLp i))).trans
        (MemLp.coeFn_toLp (R.term_memLp i))
  exact (hyrep i).trans hleft.symm

/--
The initial Souza partial sums associated to a domain representation are Cauchy
for the coefficient-cost gauge.
-/
theorem domainAtomicRepresentation_initialSegments_souzaBesov11_cost_cauchy
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s) (hs_lt_one : s < 1)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat)
    {f : α → ℂ} (R : DomainAtomicRepresentation G s 𝓦hat f) :
    ∃ y : ℕ → SouzaBesov11 G s hs,
      (∀ i, WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
        (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure)) ∧
      (∀ η > 0, ∃ N₀, ∀ m ≥ N₀, ∀ n ≥ N₀,
        WeakGridSpace.BesovishSpace.Norm_Costpq
            (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
            (1 : ℝ≥0∞)
            ((∑ i ∈ Finset.range n, y i) - (∑ i ∈ Finset.range m, y i)) < η) := by
  classical
  obtain ⟨y, hyrep, htail⟩ :=
    domainAtomicRepresentation_terms_souzaBesov11_tail_cost_tendsto_zero
      G s C c 𝓦hat hs hs_lt_one h𝓦 R
  refine ⟨y, hyrep, ?_⟩
  let A := souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top
  have hA :
      WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations
        (A := A) (1 : ℝ≥0∞) :=
    WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A (1 : ℝ≥0∞)
  intro η hη
  rcases htail η hη with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro m hm n hn
  by_cases hmn : m ≤ n
  · have hdiff :
        (∑ i ∈ Finset.range n, y i) - (∑ i ∈ Finset.range m, y i) =
          ∑ i ∈ Finset.Ico m n, y i := by
      rw [Finset.sum_Ico_eq_sub (f := fun i => y i) hmn]
    rw [hdiff]
    exact hN₀ m hm n hmn
  · have hnm : n ≤ m := Nat.le_of_not_ge hmn
    have hdiff :
        (∑ i ∈ Finset.range n, y i) - (∑ i ∈ Finset.range m, y i) =
          -∑ i ∈ Finset.Ico n m, y i := by
      rw [Finset.sum_Ico_eq_sub (f := fun i => y i) hnm]
      abel
    rw [hdiff]
    have hneg :
        WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞)
            (-∑ i ∈ Finset.Ico n m, y i) =
          WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞)
            (∑ i ∈ Finset.Ico n m, y i) := by
      have hsmul :=
        WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq
          (A := A) (q := (1 : ℝ≥0∞)) ENNReal.one_ne_top hA
          (-1 : ℂ) (∑ i ∈ Finset.Ico n m, y i)
      simpa only [neg_smul, one_smul, norm_neg, norm_one, one_mul] using hsmul
    rw [hneg]
    exact hN₀ n hn m hnm

/--
Finite partial sums of a domain representation already give Souza
`B^s_{1,1}` elements.

This is the finite truncation step used before passing to an infinite
`ℓ¹`-limit.
-/
theorem finset_domainAtomicRepresentation_souzaBesov11_bound
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s) (hs_lt_one : s < 1)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat)
    {f : α → ℂ} (R : DomainAtomicRepresentation G s 𝓦hat f)
    (F : Finset ℕ) :
    ∃ x : SouzaBesov11 G s hs,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (fun z => ∑ i ∈ F,
          R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
        (x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
          (1 : ℝ≥0∞) x ≤
        ∑ i ∈ F,
          ‖R.coeff i‖ *
            ((G.grid.μ (R.domain i)).toReal ^ (s - 1) *
              regularDomainIndicatorCost G (R.domain i) s C c
                (1 : ℝ≥0∞) (1 : ℝ≥0∞)) := by
  classical
  let A := souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top
  let B : ℕ → ℝ := fun i =>
    (G.grid.μ (R.domain i)).toReal ^ (s - 1) *
      regularDomainIndicatorCost G (R.domain i) s C c
        (1 : ℝ≥0∞) (1 : ℝ≥0∞)
  have hdom : ∀ i, Nonempty (RegularDomain G (R.domain i) (1 - s) C c) := by
    intro i
    exact h𝓦.regular_subset (R.domain_mem i)
  let Ωreg : ∀ i, RegularDomain G (R.domain i) (1 - s) C c := fun i =>
    Classical.choice (hdom i)
  have hnormB : ∀ i, 0 ≤ B i := by
    intro i
    have hΩi : RegularDomain G (R.domain i)
        (1 - (1 : ℝ≥0∞).toReal * s) C c := by
      simpa using Ωreg i
    exact mul_nonneg
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      (regularDomainIndicatorCost_nonneg
        G (R.domain i) s C c (1 : ℝ≥0∞) (1 : ℝ≥0∞)
        le_rfl ENNReal.one_ne_top hΩi)
  have hterm :
      ∀ i, ∃ y : SouzaBesov11 G s hs,
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
          (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
          (y : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) ∧
        WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) y ≤
          ‖R.coeff i‖ * B i := by
    intro i
    obtain ⟨y, hyrep, hycost⟩ :=
      regularDomain_normalizedIndicator_souzaBesov11_bound
        G (R.domain i) s C c hs hs_lt_one (Ωreg i)
    refine ⟨R.coeff i • y, ?_, ?_⟩
    · exact WeakGridSpace.representsFunction_smul
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (R.coeff i) hyrep
    · have hA :
          WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations
            (A := A) (1 : ℝ≥0∞) :=
        WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A (1 : ℝ≥0∞)
      have hsmul :
          WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) (R.coeff i • y) =
            ‖R.coeff i‖ * WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) y := by
        exact WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq
          (A := A) (q := (1 : ℝ≥0∞)) ENNReal.one_ne_top hA (R.coeff i) y
      rw [hsmul]
      exact mul_le_mul_of_nonneg_left hycost (norm_nonneg (R.coeff i))
  let y : ℕ → SouzaBesov11 G s hs := fun i => Classical.choose (hterm i)
  have hyrep :
      ∀ i, WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (fun z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
        (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) := by
    intro i
    exact (Classical.choose_spec (hterm i)).1
  have hycost :
      ∀ i, WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) (y i) ≤
        ‖R.coeff i‖ * B i := by
    intro i
    exact (Classical.choose_spec (hterm i)).2
  refine ⟨∑ i ∈ F, y i, ?_, ?_⟩
  · have hsumRep :
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
          (fun z => ∑ i ∈ F,
            R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
          (∑ i ∈ F,
            (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure)) :=
      WeakGridSpace.representsFunction_finset_sum
      (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
      F (fun i z => R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
      (fun i => (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure))
      (fun i _ => hyrep i)
    have hcoeSum :
        ((∑ i ∈ F, y i : SouzaBesov11 G s hs) :
          Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) =
          ∑ i ∈ F,
            (y i : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) := by
      simp only [AddSubmonoidClass.coe_finsetSum]
    rw [hcoeSum]
    exact hsumRep
  · have hA :
        WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations
          (A := A) (1 : ℝ≥0∞) :=
      WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A (1 : ℝ≥0∞)
    refine Finset.induction_on F ?base ?step
    · simp only [Finset.sum_empty]
      have hzero_eq :
          WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞)
              (0 : SouzaBesov11 G s hs) = 0 := by
        have hsmul :=
          WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq
            (A := A) (q := (1 : ℝ≥0∞)) ENNReal.one_ne_top hA
            (0 : ℂ) (0 : SouzaBesov11 G s hs)
        simpa only [zero_smul, norm_zero, zero_mul] using hsmul
      exact le_of_eq hzero_eq
    · intro a S ha hS
      simp only [Finset.sum_insert ha]
      calc
        WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞)
            (y a + ∑ i ∈ S, y i)
            ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) (y a) +
                WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞)
                  (∑ i ∈ S, y i) :=
          WeakGridSpace.BesovishSpace.Norm_Costpq_add_le
            (A := A) (q := (1 : ℝ≥0∞)) ENNReal.one_ne_top hA
            (y a) (∑ i ∈ S, y i)
        _ ≤ ‖R.coeff a‖ * B a + ∑ i ∈ S, ‖R.coeff i‖ * B i :=
          add_le_add (hycost a) hS

/--
Finite partial sums satisfy the expected uniform estimate from the manuscript:
the regular-domain constants have been absorbed into `C / (1 - c)`.
-/
theorem finset_domainAtomicRepresentation_souzaBesov11_uniform_bound
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s) (hs_lt_one : s < 1)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat)
    {f : α → ℂ} (R : DomainAtomicRepresentation G s 𝓦hat f)
    (F : Finset ℕ) :
    ∃ x : SouzaBesov11 G s hs,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (fun z => ∑ i ∈ F,
          R.coeff i * normalizedDomainIndicator G s (R.domain i) z)
        (x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
          (1 : ℝ≥0∞) x ≤
        C / (1 - c) * ∑ i ∈ F, ‖R.coeff i‖ := by
  classical
  obtain ⟨x, hxrep, hxcost⟩ :=
    finset_domainAtomicRepresentation_souzaBesov11_bound
      G s C c 𝓦hat hs hs_lt_one h𝓦 R F
  refine ⟨x, hxrep, ?_⟩
  have hΩ : ∀ i, RegularDomain G (R.domain i) (1 - s) C c := by
    intro i
    exact Classical.choice (h𝓦.regular_subset (R.domain_mem i))
  have hsum_eq :
      (∑ i ∈ F,
          ‖R.coeff i‖ *
            ((G.grid.μ (R.domain i)).toReal ^ (s - 1) *
              regularDomainIndicatorCost G (R.domain i) s C c
                (1 : ℝ≥0∞) (1 : ℝ≥0∞))) =
        ∑ i ∈ F, ‖R.coeff i‖ * (C / (1 - c)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [regularDomain_normalizedIndicatorCost_eq G (R.domain i) s C c (hΩ i)]
  have hfactor :
      (∑ i ∈ F, ‖R.coeff i‖ * (C / (1 - c))) =
        C / (1 - c) * ∑ i ∈ F, ‖R.coeff i‖ := by
    rw [← Finset.sum_mul]
    ring
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
        (1 : ℝ≥0∞) x
        ≤ ∑ i ∈ F,
            ‖R.coeff i‖ *
              ((G.grid.μ (R.domain i)).toReal ^ (s - 1) *
                regularDomainIndicatorCost G (R.domain i) s C c
                  (1 : ℝ≥0∞) (1 : ℝ≥0∞)) := hxcost
    _ = ∑ i ∈ F, ‖R.coeff i‖ * (C / (1 - c)) := hsum_eq
    _ = C / (1 - c) * ∑ i ∈ F, ‖R.coeff i‖ := hfactor

/--
A single normalized regular-domain representation determines a Souza
`B^s_{1,1}` element.  This is the infinite-series version of the finite
truncation estimate above.
-/
theorem domainAtomicRepresentation_to_souzaBesov11
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s) (hs_lt_one : s < 1)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat)
    {f : α → ℂ} (R : DomainAtomicRepresentation G s 𝓦hat f) :
    ∃ x : SouzaBesov11 G s hs,
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        f (x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) ∧
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
          (1 : ℝ≥0∞) x ≤
        |C / (1 - c)| * R.coeffCost := by
  classical
  let A := souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top
  obtain ⟨y, hyrep, _hycost, hfin⟩ :=
    domainAtomicRepresentation_terms_souzaBesov11_finset_bound
      G s C c 𝓦hat hs hs_lt_one h𝓦 R
  let gseq : ℕ → SouzaBesov11 G s hs := fun N => ∑ i ∈ Finset.range N, y i
  have hcauchy : ∀ η > 0, ∃ N₀, ∀ m ≥ N₀, ∀ n ≥ N₀,
      WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞)
        (gseq n - gseq m) < η := by
    let K : ℝ := |C / (1 - c)|
    have hmajor_nonneg : ∀ i, 0 ≤ K * ‖R.coeff i‖ := by
      intro i
      exact mul_nonneg (abs_nonneg _) (norm_nonneg (R.coeff i))
    have hmajor_sum : Summable fun i => K * ‖R.coeff i‖ :=
      R.coeff_summable.mul_left K
    have htail :=
      WeakGridSpace.summable_Ico_tail_tendsto_zero
        (a := fun i => K * ‖R.coeff i‖) hmajor_nonneg hmajor_sum
    intro η hη
    rcases htail η hη with ⟨N₀, hN₀⟩
    refine ⟨N₀, ?_⟩
    intro m hm n hn
    by_cases hmn : m ≤ n
    · have hdiff : gseq n - gseq m = ∑ i ∈ Finset.Ico m n, y i := by
        dsimp [gseq]
        rw [Finset.sum_Ico_eq_sub (f := fun i => y i) hmn]
      rw [hdiff]
      have hfactor :
          K * (∑ i ∈ Finset.Ico m n, ‖R.coeff i‖) =
            ∑ i ∈ Finset.Ico m n, K * ‖R.coeff i‖ := by
        rw [Finset.mul_sum]
      exact lt_of_le_of_lt ((hfin (Finset.Ico m n)).trans_eq hfactor)
        (hN₀ m hm n hmn)
    · have hnm : n ≤ m := Nat.le_of_not_ge hmn
      have hdiff : gseq n - gseq m = -∑ i ∈ Finset.Ico n m, y i := by
        dsimp [gseq]
        rw [Finset.sum_Ico_eq_sub (f := fun i => y i) hnm]
        abel
      rw [hdiff]
      have hA :
          WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations
            (A := A) (1 : ℝ≥0∞) :=
        WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A (1 : ℝ≥0∞)
      have hneg :
          WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞)
              (-∑ i ∈ Finset.Ico n m, y i) =
            WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞)
              (∑ i ∈ Finset.Ico n m, y i) := by
        have hsmul :=
          WeakGridSpace.BesovishSpace.Norm_Costpq_smul_eq
            (A := A) (q := (1 : ℝ≥0∞)) ENNReal.one_ne_top hA
            (-1 : ℂ) (∑ i ∈ Finset.Ico n m, y i)
        simpa only [neg_smul, one_smul, norm_neg, norm_one, one_mul] using hsmul
      rw [hneg]
      have hfactor :
          K * (∑ i ∈ Finset.Ico n m, ‖R.coeff i‖) =
            ∑ i ∈ Finset.Ico n m, K * ‖R.coeff i‖ := by
        rw [Finset.mul_sum]
      exact lt_of_le_of_lt ((hfin (Finset.Ico n m)).trans_eq hfactor)
        (hN₀ n hn m hnm)
  letI : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  obtain ⟨x, hx_cost⟩ :=
    WeakGridSpace.besovishSpace_Norm_Costpq_cauchySeq_tendsto
      (G := G.toWeakGridSpace) (s := s) (p := (1 : ℝ≥0∞))
      (u := ∞) (q := (1 : ℝ≥0∞))
      ENNReal.one_ne_top hs le_top A
      (souza_assumptionG2 G s (1 : ℝ≥0∞) (1 : ℝ≥0∞)
        hs le_rfl ENNReal.one_ne_top)
      (souza_assumptionA5 G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
      gseq hcauchy
  have hLp_sum :=
    domainAtomicRepresentation_terms_souzaBesov11_Lp_hasSum_of_rep
      G s R hs y hyrep
  let I : Lp ℂ (domainEndpointExponent s) G.toWeakGridSpace.measure →L[ℂ]
      Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure :=
    WeakGridSpace.LpGridRepresentation.lpInclusion
      (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
      (t := domainEndpointExponent s)
      ENNReal.one_ne_top ENNReal.ofReal_ne_top Fact.out
  let zseq : ℕ → SouzaBesov11 G s hs := fun N => x - gseq N
  have hz_Lp :
      Filter.Tendsto
        (fun N => ((zseq N : SouzaBesov11 G s hs) :
          Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure))
        Filter.atTop
        (𝓝 (0 : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure)) :=
    WeakGridSpace.BesovishSpace.tendsto_Lp_zero_of_tendsto_Norm_Costpq_zero
      (G := G.toWeakGridSpace) (s := s) (p := (1 : ℝ≥0∞))
      (u := ∞) (q := (1 : ℝ≥0∞)) (A := A)
      ENNReal.one_ne_top
      (souza_assumptionG2 G s (1 : ℝ≥0∞) (1 : ℝ≥0∞)
        hs le_rfl ENNReal.one_ne_top).1
      zseq
      (by
        intro ε hε
        simpa [zseq] using hx_cost ε hε)
  have hx_Lp :
      Filter.Tendsto
        (fun N => (gseq N : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure))
        Filter.atTop
        (𝓝 (x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure)) := by
    have h :=
      (tendsto_const_nhds
        (x := (x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure))).sub hz_Lp
    simpa [zseq] using h
  have hpartial_sum :
      Filter.Tendsto
        (fun N => (gseq N : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure))
        Filter.atTop
        (𝓝 (I (MemLp.toLp f R.memLp))) := by
    simpa [gseq, I] using hLp_sum.tendsto_sum_nat
  have hx_eq :
      (x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) =
        I (MemLp.toLp f R.memLp) :=
    tendsto_nhds_unique hx_Lp hpartial_sum
  have hxrep :
      WeakGridSpace.RepresentsFunction
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        f (x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) := by
    change ((x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) : α → ℂ)
      =ᵐ[G.toWeakGridSpace.measure] f
    rw [hx_eq]
    exact
      (WeakGridSpace.LpGridRepresentation.coeFn_lpInclusion
        (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
        (t := domainEndpointExponent s)
        ENNReal.one_ne_top ENNReal.ofReal_ne_top Fact.out
        (MemLp.toLp f R.memLp)).trans
        (MemLp.coeFn_toLp R.memLp)
  have hbound : ∀ N,
      WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) (gseq N) ≤
        |C / (1 - c)| * R.coeffCost := by
    intro N
    have hsum_le :
        (∑ i ∈ Finset.range N, ‖R.coeff i‖) ≤ R.coeffCost := by
      simpa [DomainAtomicRepresentation.coeffCost] using
        R.coeff_summable.sum_le_tsum (Finset.range N)
          (fun i _ => norm_nonneg (R.coeff i))
    exact (hfin (Finset.range N)).trans
      (mul_le_mul_of_nonneg_left hsum_le (abs_nonneg _))
  have hxcost :
      WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) x ≤
        |C / (1 - c)| * R.coeffCost :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_le_of_tendsto_Norm_Costpq
      (A := A) (q := (1 : ℝ≥0∞))
      ENNReal.one_ne_top
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A (1 : ℝ≥0∞))
      hbound hx_cost
  exact ⟨x, hxrep, hxcost⟩

/--
Every function with a normalized regular-domain representation belongs to the
Souza `B^s_{1,1}` space, with the expected norm control.

This is the formal version of the first half of Proposition `rema`, using
`(estG)` term by term.
-/
theorem domainBesovSpace_to_souzaBesov11
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s) (hs_lt_one : s < 1)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat) :
    ∃ C₀ : ℝ,
      0 ≤ C₀ ∧
      ∀ f : α → ℂ,
        DomainBesovSpace G s 𝓦hat f →
          ∃ x : SouzaBesov11 G s hs,
            WeakGridSpace.RepresentsFunction
              (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
              f (x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) ∧
            WeakGridSpace.BesovishSpace.Norm_Costpq
                (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
                (1 : ℝ≥0∞) x ≤
              C₀ * domainBesovGauge G s 𝓦hat f := by
  classical
  let C₀ : ℝ := |C / (1 - c)|
  refine ⟨C₀, abs_nonneg _, ?_⟩
  intro f hf
  rcases hf with ⟨R₀⟩
  obtain ⟨x₀, hx₀rep, _hx₀cost⟩ :=
    domainAtomicRepresentation_to_souzaBesov11
      G s C c 𝓦hat hs hs_lt_one h𝓦 R₀
  refine ⟨x₀, hx₀rep, ?_⟩
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hden : 0 < C₀ + 1 := by
    dsimp [C₀]
    linarith [abs_nonneg (C / (1 - c))]
  have hδ : 0 < ε / (C₀ + 1) := by positivity
  obtain ⟨Rε, hRε⟩ :=
    exists_domainAtomicRepresentation_coeffCost_lt_gauge_add
      G s 𝓦hat (show DomainBesovSpace G s 𝓦hat f from ⟨R₀⟩) hδ
  obtain ⟨xε, hxεrep, hxεcost⟩ :=
    domainAtomicRepresentation_to_souzaBesov11
      G s C c 𝓦hat hs hs_lt_one h𝓦 Rε
  have hxε_eq_x₀ : xε = x₀ := by
    apply Subtype.ext
    apply Lp.ext
    exact hxεrep.trans hx₀rep.symm
  have hx₀cost :
      WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
          (1 : ℝ≥0∞) x₀ ≤
        C₀ * Rε.coeffCost := by
    simpa [C₀, hxε_eq_x₀] using hxεcost
  have hRε_le :
      Rε.coeffCost ≤ domainBesovGauge G s 𝓦hat f + ε / (C₀ + 1) :=
    le_of_lt hRε
  have hmul :
      C₀ * Rε.coeffCost ≤
        C₀ * (domainBesovGauge G s 𝓦hat f + ε / (C₀ + 1)) :=
    mul_le_mul_of_nonneg_left hRε_le (by dsimp [C₀]; exact abs_nonneg _)
  have hsmall : C₀ * (ε / (C₀ + 1)) ≤ ε := by
    have hfrac : C₀ / (C₀ + 1) ≤ (1 : ℝ) :=
      (div_le_one hden).2 (by linarith)
    have hεnn : 0 ≤ ε := le_of_lt hε
    calc
      C₀ * (ε / (C₀ + 1)) = (C₀ / (C₀ + 1)) * ε := by ring
      _ ≤ (1 : ℝ) * ε := mul_le_mul_of_nonneg_right hfrac hεnn
      _ = ε := by ring
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq
        (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
        (1 : ℝ≥0∞) x₀
        ≤ C₀ * Rε.coeffCost := hx₀cost
    _ ≤ C₀ * (domainBesovGauge G s 𝓦hat f + ε / (C₀ + 1)) := hmul
    _ = C₀ * domainBesovGauge G s 𝓦hat f + C₀ * (ε / (C₀ + 1)) := by ring
    _ ≤ C₀ * domainBesovGauge G s 𝓦hat f + ε :=
      add_le_add_right hsmall _

section DecodeReindex

variable {β E : Type*} [AddCommGroup E] [TopologicalSpace E]

private def decode₂WithZero [Encodable β] (f : β → E) : ℕ → E :=
  fun n => (Encodable.decode₂ β n).elim 0 f

/--
Summing an encodable family by `decode₂`, with zero terms outside the image of
`encode`, gives the same unconditional sum.  This is a local adapter from the
natural-number indexing used in the domain representation to the more natural
level/cell sigma index used by Souza representations.
-/
private theorem hasSum_decode₂_iff [Encodable β] {f : β → E} {a : E} :
    HasSum
      (fun n : ℕ =>
        match Encodable.decode₂ β n with
        | some b => f b
        | none => 0)
      a ↔
    HasSum f a := by
  classical
  let e : β ≃ Set.range (Encodable.encode : β → ℕ) :=
    Equiv.ofInjective (Encodable.encode : β → ℕ) Encodable.encode_injective
  let F : ℕ → E :=
    fun n =>
      match Encodable.decode₂ β n with
      | some b => f b
      | none => 0
  have hF_indicator :
      F = (Set.range (Encodable.encode : β → ℕ)).indicator F := by
    funext n
    by_cases hn : n ∈ Set.range (Encodable.encode : β → ℕ)
    · rw [Set.indicator_of_mem hn]
    · have hdecode : Encodable.decode₂ β n = none := by
        exact Option.eq_none_iff_forall_not_mem.mpr fun b hb =>
          hn ⟨b, Encodable.mem_decode₂.1 hb⟩
      rw [Set.indicator_of_notMem hn]
      simp [F, hdecode]
  have hsub :
      HasSum (F ∘ (↑) : Set.range (Encodable.encode : β → ℕ) → E) a ↔
        HasSum F a := by
    have hsub0 :
        HasSum (F ∘ (↑) : Set.range (Encodable.encode : β → ℕ) → E) a ↔
          HasSum ((Set.range (Encodable.encode : β → ℕ)).indicator F) a :=
      hasSum_subtype_iff_indicator
      (s := Set.range (Encodable.encode : β → ℕ)) (f := F) (a := a)
    rwa [← hF_indicator] at hsub0
  have hrange :
      HasSum (F ∘ (↑) : Set.range (Encodable.encode : β → ℕ) → E) a ↔
        HasSum f a := by
    have hcomp : ((F ∘ (↑)) ∘ (e : β → Set.range (Encodable.encode : β → ℕ))) = f := by
      funext b
      simp [F, e, Encodable.decode₂_encode]
    rw [← e.hasSum_iff]
    rw [hcomp]
  exact hsub.symm.trans hrange

private theorem summable_decode₂_iff [Encodable β] {f : β → E} :
    Summable
      (fun n : ℕ =>
        match Encodable.decode₂ β n with
        | some b => f b
        | none => 0)
      ↔
    Summable f := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    exact ⟨a, (hasSum_decode₂_iff.mp ha)⟩
  · intro h
    rcases h with ⟨a, ha⟩
    exact ⟨a, (hasSum_decode₂_iff.mpr ha)⟩

private theorem hasSum_decode₂WithZero_iff [Encodable β] {f : β → E} {a : E} :
    HasSum (decode₂WithZero f) a ↔ HasSum f a := by
  constructor
  · intro h
    apply (hasSum_decode₂_iff (β := β) (E := E) (f := f) (a := a)).mp
    refine h.congr_fun ?_
    intro n
    unfold decode₂WithZero
    cases Encodable.decode₂ β n <;> rfl
  · intro h
    refine ((hasSum_decode₂_iff (β := β) (E := E) (f := f) (a := a)).mpr h).congr_fun ?_
    intro n
    unfold decode₂WithZero
    cases Encodable.decode₂ β n <;> rfl

private theorem summable_decode₂WithZero_iff [Encodable β] {f : β → E} :
    Summable (decode₂WithZero f) ↔ Summable f := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    exact ⟨a, (hasSum_decode₂WithZero_iff.mp ha)⟩
  · intro h
    rcases h with ⟨a, ha⟩
    exact ⟨a, (hasSum_decode₂WithZero_iff.mpr ha)⟩

end DecodeReindex

section DecodeTsum

variable {β : Type*}

private theorem tsum_decode₂WithZero_eq [Encodable β] {f : β → ℝ} (hf : Summable f) :
    (∑' n : ℕ, decode₂WithZero f n) = ∑' b : β, f b := by
  exact (hasSum_decode₂WithZero_iff.mpr hf.hasSum).tsum_eq.trans hf.hasSum.tsum_eq.symm

private theorem tsum_decode₂_eq [Encodable β] {f : β → ℝ} (hf : Summable f) :
    (∑' n : ℕ,
      match Encodable.decode₂ β n with
      | some b => f b
      | none => 0) =
    ∑' b : β, f b := by
  exact (hasSum_decode₂_iff.mpr hf.hasSum).tsum_eq.trans hf.hasSum.tsum_eq.symm

end DecodeTsum

/-- The natural flat index for a Souza representation: a level and a cell. -/
private abbrev SouzaCellIndex (G : GoodGridSpace (α := α)) :=
  Σ k : ℕ, WeakGridSpace.LevelCell G.toWeakGridSpace k

/--
The coefficient obtained by rewriting a Souza cell term
`s_Q a_Q 1_Q` as a multiple of the normalized domain indicator
`μ(Q)^(s-1) 1_Q`.
-/
private noncomputable def souzaDomainFlattenedCoeff
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s)
    {g : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top) g)
    (iQ : SouzaCellIndex G) : ℂ :=
  let scale : ℝ := (G.grid.μ iQ.2.1).toReal ^ (s - 1)
  let a : ℂ := (R.block iQ.1).atom iQ.2
  (R.block iQ.1).coeff iQ.2 * a / (scale : ℂ)

/-- The flattened domain coefficient is controlled by the original Souza coefficient. -/
private theorem souzaDomainFlattenedCoeff_norm_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s)
    {g : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top) g)
    (iQ : SouzaCellIndex G) :
    ‖souzaDomainFlattenedCoeff G s hs R iQ‖ ≤
      ‖(R.block iQ.1).coeff iQ.2‖ := by
  let scale : ℝ := (G.grid.μ iQ.2.1).toReal ^ (s - 1)
  let a : ℂ := (R.block iQ.1).atom iQ.2
  let coeff : ℂ := (R.block iQ.1).coeff iQ.2
  have hscale_pos : 0 < scale := by
    let Qgood : GoodGridCell G :=
      ⟨iQ.1, iQ.2.1, by
        simp [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid]⟩
    have hμ : 0 < (G.grid.μ iQ.2.1).toReal :=
      ENNReal.toReal_pos (ne_of_gt (GoodGridCell.measure_pos Qgood))
        (GoodGridCell.measure_ne_top Qgood)
    exact Real.rpow_pos_of_pos hμ _
  have ha : ‖a‖ ≤ scale := by
    dsimp [a, scale]
    simpa only [WeakGridSpace.AtomFamily.IsAtom, souzaAtomFamily, souzaAtomsSet,
      GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid, ENNReal.toReal_one, inv_one]
      using (R.block iQ.1).atom_mem iQ.2
  have hmain : ‖coeff * a / (scale : ℂ)‖ ≤ ‖coeff‖ := by
    rw [norm_div, norm_mul]
    have hnorm_scale : ‖(scale : ℂ)‖ = scale := by
      simpa only [abs_of_pos hscale_pos] using (RCLike.norm_ofReal (K := ℂ) scale)
    rw [hnorm_scale]
    have hmul : ‖coeff‖ * ‖a‖ ≤ ‖coeff‖ * scale :=
      mul_le_mul_of_nonneg_left ha (norm_nonneg coeff)
    calc
      ‖coeff‖ * ‖a‖ / scale ≤ ‖coeff‖ * scale / scale :=
        div_le_div_of_nonneg_right hmul hscale_pos.le
      _ = ‖coeff‖ := by field_simp [hscale_pos.ne']
  simpa [souzaDomainFlattenedCoeff, scale, a, coeff] using hmain

/--
The flattened domain coefficients form an `ℓ¹` family, with no larger cost
than the original Souza `(1,1)` representation.
-/
private theorem souzaDomainFlattenedCoeff_summable_norm_and_tsum_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s)
    {g : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top) g)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost
      (q := (1 : ℝ≥0∞)) R) :
    Summable (fun iQ : SouzaCellIndex G => ‖souzaDomainFlattenedCoeff G s hs R iQ‖) ∧
      (∑' iQ : SouzaCellIndex G, ‖souzaDomainFlattenedCoeff G s hs R iQ‖) ≤
        WeakGridSpace.LpGridRepresentation.pqCost (q := (1 : ℝ≥0∞)) R := by
  classical
  let c : SouzaCellIndex G → ℝ :=
    fun iQ => ‖souzaDomainFlattenedCoeff G s hs R iQ‖
  let b : SouzaCellIndex G → ℝ :=
    fun iQ => ‖(R.block iQ.1).coeff iQ.2‖
  have hc_nonneg : ∀ iQ, 0 ≤ c iQ := fun iQ => norm_nonneg _
  have hb_nonneg : ∀ iQ, 0 ≤ b iQ := fun iQ => norm_nonneg _
  have hcb : ∀ iQ, c iQ ≤ b iQ := by
    intro iQ
    exact souzaDomainFlattenedCoeff_norm_le G s hs R iQ
  have hb_sum : Summable b := by
    refine (summable_sigma_of_nonneg (f := b) hb_nonneg).2 ?_
    constructor
    · intro k
      exact (hasSum_fintype (fun Q : WeakGridSpace.LevelCell G.toWeakGridSpace k =>
        ‖(R.block k).coeff Q‖)).summable
    · simpa [b] using
        (WeakGridSpace.LpGridRepresentation.finitePQCost_one_one_iff R).1 hRfin
  have hc_sum : Summable c :=
    Summable.of_nonneg_of_le hc_nonneg hcb hb_sum
  refine ⟨by simpa [c] using hc_sum, ?_⟩
  have htsum_le : (∑' iQ : SouzaCellIndex G, c iQ) ≤ ∑' iQ : SouzaCellIndex G, b iQ :=
    hc_sum.tsum_le_tsum hcb hb_sum
  have hb_tsum :
      (∑' iQ : SouzaCellIndex G, b iQ) =
        WeakGridSpace.LpGridRepresentation.pqCost (q := (1 : ℝ≥0∞)) R := by
    calc
      (∑' iQ : SouzaCellIndex G, b iQ)
          = ∑' k : ℕ, ∑' Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              ‖(R.block k).coeff Q‖ := by
            rw [hb_sum.tsum_sigma]
      _ = ∑' k : ℕ, ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              ‖(R.block k).coeff Q‖ := by
            apply tsum_congr
            intro k
            rw [tsum_fintype]
      _ = WeakGridSpace.LpGridRepresentation.pqCost (q := (1 : ℝ≥0∞)) R := by
            exact (WeakGridSpace.LpGridRepresentation.pqCost_one_one_eq_tsum_levelCoeffPower R).symm
  exact htsum_le.trans_eq hb_tsum

private theorem domainEndpointExponent_toReal
    (s : ℝ) [Fact (1 ≤ domainEndpointExponent s)] :
    (domainEndpointExponent s).toReal = (1 - s)⁻¹ := by
  have hle : (1 : ℝ) ≤ (1 - s)⁻¹ := by
    simpa [domainEndpointExponent] using
      (ENNReal.one_le_ofReal.mp (Fact.out : (1 : ℝ≥0∞) ≤ domainEndpointExponent s))
  exact ENNReal.toReal_ofReal (hle.trans' zero_le_one)

private theorem domainEndpoint_critical_exponent_zero
    (s : ℝ) [Fact (1 ≤ domainEndpointExponent s)] :
    s - 1 / (1 : ℝ≥0∞).toReal + 1 / (domainEndpointExponent s).toReal = 0 := by
  rw [domainEndpointExponent_toReal s]
  norm_num

private theorem domainEndpoint_cCoefficientFinite_one
    (G : GoodGridSpace (α := α)) (s : ℝ)
    [Fact (1 ≤ domainEndpointExponent s)] :
    WeakGridSpace.LpGridRepresentation.cCoefficientFinite
      (domainEndpointExponent s) (1 : ℝ≥0∞)
      (fun k => (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
        G.toWeakGridSpace s (1 : ℝ≥0∞) (domainEndpointExponent s) k) ^
          (domainEndpointExponent s).toReal) := by
  classical
  have ht_pos : 0 < (domainEndpointExponent s).toReal := by
    rw [domainEndpointExponent_toReal s]
    exact zero_lt_one.trans_le
      (by
        simpa [domainEndpointExponent] using
          (ENNReal.one_le_ofReal.mp
            (Fact.out : (1 : ℝ≥0∞) ≤ domainEndpointExponent s)))
  have hroot :
      ∀ k : ℕ,
        ((WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s (1 : ℝ≥0∞) (domainEndpointExponent s) k) ^
              (domainEndpointExponent s).toReal) ^
            (1 / (domainEndpointExponent s).toReal) =
          1 := by
    intro k
    have hweight :
        WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s (1 : ℝ≥0∞) (domainEndpointExponent s) k =
          1 := by
      unfold WeakGridSpace.LpGridRepresentation.levelMeasureWeight
      rw [domainEndpoint_critical_exponent_zero s, Real.rpow_zero]
    rw [hweight]
    norm_num
  simp only [WeakGridSpace.LpGridRepresentation.cCoefficientFinite, ↓reduceIte]
  change BddAbove (Set.range fun k : ℕ =>
    ((WeakGridSpace.LpGridRepresentation.levelMeasureWeight
      G.toWeakGridSpace s (1 : ℝ≥0∞) (domainEndpointExponent s) k) ^
        (domainEndpointExponent s).toReal) ^
      (1 / (domainEndpointExponent s).toReal))
  refine ⟨1, ?_⟩
  rintro x ⟨k, rfl⟩
  change
    ((WeakGridSpace.LpGridRepresentation.levelMeasureWeight
      G.toWeakGridSpace s (1 : ℝ≥0∞) (domainEndpointExponent s) k) ^
        (domainEndpointExponent s).toReal) ^
      (1 / (domainEndpointExponent s).toReal) ≤ 1
  rw [hroot k]

private theorem souzaDomainFlattenedCoeff_normalizedDomainIndicator_eq
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s)
    {g : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top) g)
    (iQ : SouzaCellIndex G) :
    (fun z => souzaDomainFlattenedCoeff G s hs R iQ *
        normalizedDomainIndicator G s iQ.2.1 z)
      =
    (fun z => (R.block iQ.1).coeff iQ.2 *
        (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top).toFunction
          (WeakGridSpace.levelCellToWeakGridCell G.toWeakGridSpace iQ.1 iQ.2)
          ((R.block iQ.1).atom iQ.2) z) := by
  funext z
  let scale : ℝ := (G.grid.μ iQ.2.1).toReal ^ (s - 1)
  let a : ℂ := (R.block iQ.1).atom iQ.2
  let coeff : ℂ := (R.block iQ.1).coeff iQ.2
  have hscale_pos : 0 < scale := by
    let Qgood : GoodGridCell G :=
      ⟨iQ.1, iQ.2.1, by
        simp [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid]⟩
    have hμ : 0 < (G.grid.μ iQ.2.1).toReal :=
      ENNReal.toReal_pos (ne_of_gt (GoodGridCell.measure_pos Qgood))
        (GoodGridCell.measure_ne_top Qgood)
    exact Real.rpow_pos_of_pos hμ _
  by_cases hz : z ∈ iQ.2.1
  · dsimp [souzaDomainFlattenedCoeff, normalizedDomainIndicator,
      WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily, souzaLocalVectorSpace,
      WeakGridSpace.levelCellToWeakGridCell, GoodGridSpace.toWeakGridSpace,
      GoodGridSpace.toWeakGrid, scale, a, coeff]
    rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    change coeff * a / (scale : ℂ) * (scale : ℂ) = coeff * a
    field_simp [hscale_pos.ne']
  · dsimp [souzaDomainFlattenedCoeff, normalizedDomainIndicator,
      WeakGridSpace.AtomFamily.toFunction, souzaAtomFamily, souzaLocalVectorSpace,
      WeakGridSpace.levelCellToWeakGridCell, GoodGridSpace.toWeakGridSpace,
      GoodGridSpace.toWeakGrid, scale, a, coeff]
    rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    simp only [mul_zero]

private theorem souzaDomainFlattenedCoeff_domainTerm_memLp
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s)
    [Fact (1 ≤ domainEndpointExponent s)]
    {g : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top) g)
    (iQ : SouzaCellIndex G) :
    MemLp (fun z => souzaDomainFlattenedCoeff G s hs R iQ *
        normalizedDomainIndicator G s iQ.2.1 z)
      (domainEndpointExponent s) G.grid.μ := by
  let scale : ℂ := (((G.grid.μ iQ.2.1).toReal ^ (s - 1) : ℝ) : ℂ)
  let coeff : ℂ := souzaDomainFlattenedCoeff G s hs R iQ
  have hterm :
      (fun z => souzaDomainFlattenedCoeff G s hs R iQ *
          normalizedDomainIndicator G s iQ.2.1 z)
        =
      iQ.2.1.indicator (fun _ => coeff * scale) := by
    funext z
    by_cases hz : z ∈ iQ.2.1
    · simp [normalizedDomainIndicator, coeff, scale, Set.indicator_of_mem hz]
    · simp [normalizedDomainIndicator, coeff, scale, Set.indicator_of_notMem hz]
  let Qgood : GoodGridCell G :=
    ⟨iQ.1, iQ.2.1, by
      simp [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid]⟩
  rw [hterm]
  exact MeasureTheory.memLp_indicator_const
    (μ := G.grid.μ) (s := iQ.2.1)
    (p := domainEndpointExponent s)
    (G.grid.grid.measurable Qgood.level Qgood.cell Qgood.mem)
    (coeff * scale) (Or.inr (GoodGridCell.measure_ne_top Qgood))

private theorem souzaDomainFlattenedCoeff_domainTerm_norm_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s)
    [Fact (1 ≤ domainEndpointExponent s)]
    {g : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top) g)
    (iQ : SouzaCellIndex G) :
    ‖MemLp.toLp
      (fun z => souzaDomainFlattenedCoeff G s hs R iQ *
        normalizedDomainIndicator G s iQ.2.1 z)
      (souzaDomainFlattenedCoeff_domainTerm_memLp G s hs R iQ)‖ ≤
      ‖souzaDomainFlattenedCoeff G s hs R iQ‖ := by
  let t : ℝ≥0∞ := domainEndpointExponent s
  let μQ : ℝ := (G.grid.μ iQ.2.1).toReal
  let scale : ℂ := ((μQ ^ (s - 1) : ℝ) : ℂ)
  let coeff : ℂ := souzaDomainFlattenedCoeff G s hs R iQ
  let Qgood : GoodGridCell G :=
    ⟨iQ.1, iQ.2.1, by
      simp [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid]⟩
  have hμ_pos : 0 < μQ := by
    dsimp [μQ]
    exact ENNReal.toReal_pos (ne_of_gt (GoodGridCell.measure_pos Qgood))
      (GoodGridCell.measure_ne_top Qgood)
  have ht_ne_zero : t ≠ 0 := by
    exact ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ t))
  have hterm :
      (fun z => souzaDomainFlattenedCoeff G s hs R iQ *
          normalizedDomainIndicator G s iQ.2.1 z)
        =
      iQ.2.1.indicator (fun _ => coeff * scale) := by
    funext z
    by_cases hz : z ∈ iQ.2.1
    · simp [normalizedDomainIndicator, coeff, scale, μQ, Set.indicator_of_mem hz]
    · simp [normalizedDomainIndicator, coeff, scale, μQ, Set.indicator_of_notMem hz]
  have htoLp :
      MemLp.toLp
        (fun z => souzaDomainFlattenedCoeff G s hs R iQ *
          normalizedDomainIndicator G s iQ.2.1 z)
        (souzaDomainFlattenedCoeff_domainTerm_memLp G s hs R iQ)
        =
      MeasureTheory.indicatorConstLp
        (μ := G.grid.μ) (p := t)
        (G.grid.grid.measurable Qgood.level Qgood.cell Qgood.mem)
        (GoodGridCell.measure_ne_top Qgood)
        (coeff * scale) := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp
      (souzaDomainFlattenedCoeff_domainTerm_memLp G s hs R iQ)).trans <|
      (Filter.EventuallyEq.of_eq hterm).trans
      (MeasureTheory.indicatorConstLp_coeFn
        (μ := G.grid.μ) (p := t)
        (hs := G.grid.grid.measurable Qgood.level Qgood.cell Qgood.mem)
        (hμs := GoodGridCell.measure_ne_top Qgood)
        (c := coeff * scale)).symm
  rw [htoLp]
  have hnorm :=
    MeasureTheory.norm_indicatorConstLp
      (μ := G.grid.μ) (p := t)
      (hs := G.grid.grid.measurable Qgood.level Qgood.cell Qgood.mem)
      (hμs := GoodGridCell.measure_ne_top Qgood)
      (c := coeff * scale)
      ht_ne_zero ENNReal.ofReal_ne_top
  rw [hnorm]
  have ht_real : t.toReal = (1 - s)⁻¹ := by
    dsimp [t]
    exact domainEndpointExponent_toReal s
  have hpow_cancel : μQ ^ (s - 1) * μQ ^ (1 / t.toReal) = 1 := by
    rw [ht_real]
    have hden_pos : 0 < 1 - s := by
      have hle : (1 : ℝ) ≤ (1 - s)⁻¹ := by
        simpa [domainEndpointExponent] using
          (ENNReal.one_le_ofReal.mp (Fact.out : (1 : ℝ≥0∞) ≤ domainEndpointExponent s))
      by_contra hnonpos
      have hnonpos' : 1 - s ≤ 0 := le_of_not_gt hnonpos
      have hinv_nonpos : (1 - s)⁻¹ ≤ 0 := inv_nonpos.mpr hnonpos'
      linarith
    have hinv_inv : 1 / (1 - s)⁻¹ = 1 - s := by
      field_simp [hden_pos.ne']
    rw [hinv_inv, ← Real.rpow_add hμ_pos]
    ring_nf
    exact Real.rpow_zero μQ
  have hscale_norm : ‖scale‖ = μQ ^ (s - 1) := by
    dsimp [scale]
    simp [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hμ_pos.le _)]
  have hμreal : G.grid.μ.real iQ.2.1 = μQ := by
    simp [μQ, measureReal_def]
  rw [norm_mul, hscale_norm, hμreal]
  calc
    ‖coeff‖ * μQ ^ (s - 1) * μQ ^ (1 / t.toReal)
        = ‖coeff‖ * (μQ ^ (s - 1) * μQ ^ (1 / t.toReal)) := by ring
    _ = ‖coeff‖ := by rw [hpow_cancel, mul_one]
    _ ≤ ‖souzaDomainFlattenedCoeff G s hs R iQ‖ := by rfl

private noncomputable def souzaDomainTermLp
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s)
    [Fact (1 ≤ domainEndpointExponent s)]
    {g : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top) g)
    (iQ : SouzaCellIndex G) :
    Lp ℂ (domainEndpointExponent s) G.grid.μ :=
  MemLp.toLp
    (fun z => souzaDomainFlattenedCoeff G s hs R iQ *
      normalizedDomainIndicator G s iQ.2.1 z)
    (souzaDomainFlattenedCoeff_domainTerm_memLp G s hs R iQ)

private theorem souzaDomainTermLp_summable
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s)
    [Fact (1 ≤ domainEndpointExponent s)]
    {g : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top) g)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost
      (q := (1 : ℝ≥0∞)) R) :
    Summable (fun iQ : SouzaCellIndex G => souzaDomainTermLp G s hs R iQ) := by
  have hcoeff_sum :
      Summable (fun iQ : SouzaCellIndex G =>
        ‖souzaDomainFlattenedCoeff G s hs R iQ‖) :=
    (souzaDomainFlattenedCoeff_summable_norm_and_tsum_le G s hs R hRfin).1
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le
    (fun iQ => norm_nonneg (souzaDomainTermLp G s hs R iQ)) ?_ hcoeff_sum
  intro iQ
  exact souzaDomainFlattenedCoeff_domainTerm_norm_le G s hs R iQ

private theorem souzaDomainTermLp_eq_termLt
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s)
    [Fact (1 ≤ domainEndpointExponent s)]
    {g : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top) g)
    (ht_le_pu : domainEndpointExponent s ≤ (1 : ℝ≥0∞) * ∞)
    (iQ : SouzaCellIndex G) :
    souzaDomainTermLp G s hs R iQ =
      WeakGridSpace.LevelBlock.termLt
        (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
        ht_le_pu (R.block iQ.1) iQ.2 := by
  apply Lp.ext
  refine (MemLp.coeFn_toLp
    (souzaDomainFlattenedCoeff_domainTerm_memLp G s hs R iQ)).trans ?_
  refine (Filter.EventuallyEq.of_eq
    (souzaDomainFlattenedCoeff_normalizedDomainIndicator_eq G s hs R iQ)).trans ?_
  exact (WeakGridSpace.LevelBlock.coeFn_termLt
    (G := G.toWeakGridSpace) (s := s) (p := (1 : ℝ≥0∞)) (u := ∞)
    (A := souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
    ht_le_pu (R.block iQ.1) iQ.2).symm

private theorem souzaDomainTermLp_hasSum
    (G : GoodGridSpace (α := α)) (s : ℝ) (hs : 0 < s)
    [Fact (1 ≤ domainEndpointExponent s)]
    {g : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top) g)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost
      (q := (1 : ℝ≥0∞)) R) :
    ∃ h : Lp ℂ (domainEndpointExponent s) G.grid.μ,
      HasSum (fun iQ : SouzaCellIndex G => souzaDomainTermLp G s hs R iQ) h ∧
      h =ᵐ[G.grid.μ] (g : α → ℂ) := by
  classical
  let t : ℝ≥0∞ := domainEndpointExponent s
  let A := souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top
  have ht_le_pu : t ≤ (1 : ℝ≥0∞) * ∞ := by
    simp [t]
  have hδ_nonneg :
      0 ≤ s - 1 / (1 : ℝ≥0∞).toReal + 1 / t.toReal := by
    rw [show t = domainEndpointExponent s from rfl]
    rw [domainEndpoint_critical_exponent_zero s]
  obtain ⟨h, hlevel, hae⟩ :=
    WeakGridSpace.LpGridRepresentation.exists_Lt_representative_hasSum_of_lp_embedding
      (G := G.toWeakGridSpace) (s := s) (p := (1 : ℝ≥0∞)) (u := ∞)
      (q := (1 : ℝ≥0∞)) (A := A) (t := t)
      ENNReal.one_ne_top ENNReal.ofReal_ne_top le_rfl Fact.out ht_le_pu
      hδ_nonneg R hRfin
      (by
        change WeakGridSpace.LpGridRepresentation.cCoefficientFinite
          (domainEndpointExponent s) (1 : ℝ≥0∞)
          (fun k => (WeakGridSpace.LpGridRepresentation.levelMeasureWeight
            G.toWeakGridSpace s (1 : ℝ≥0∞) (domainEndpointExponent s) k) ^
              (domainEndpointExponent s).toReal)
        exact domainEndpoint_cCoefficientFinite_one G s)
  have hinner :
      ∀ k : ℕ,
        HasSum
          (fun Q : WeakGridSpace.LevelCell G.toWeakGridSpace k =>
            souzaDomainTermLp G s hs R ⟨k, Q⟩)
          ((R.block k).toLt (t := t) A ht_le_pu) := by
    intro k
    have hsum :
        HasSum
          (fun Q : WeakGridSpace.LevelCell G.toWeakGridSpace k =>
            souzaDomainTermLp G s hs R ⟨k, Q⟩)
          (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            souzaDomainTermLp G s hs R ⟨k, Q⟩) :=
      hasSum_fintype _
    convert hsum using 1
    rw [WeakGridSpace.LevelBlock.toLt]
    simp only [t, A]
    exact Finset.sum_congr rfl fun Q _ =>
      (souzaDomainTermLp_eq_termLt G s hs R ht_le_pu ⟨k, Q⟩).symm
  have hflat_summable :
      Summable (fun iQ : SouzaCellIndex G => souzaDomainTermLp G s hs R iQ) :=
    souzaDomainTermLp_summable G s hs R hRfin
  refine ⟨h, ?_, hae⟩
  exact hlevel.sigma_of_hasSum hinner hflat_summable

private theorem domainAtomicRepresentation_of_souzaRepresentation
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat)
    {g : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top) g)
    (hRfin : WeakGridSpace.LpGridRepresentation.FinitePQCost
      (q := (1 : ℝ≥0∞)) R) :
    ∃ DR : DomainAtomicRepresentation G s 𝓦hat (g : α → ℂ),
      DR.coeffCost ≤ WeakGridSpace.LpGridRepresentation.pqCost
        (q := (1 : ℝ≥0∞)) R := by
  classical
  letI : ∀ k : ℕ, Encodable (WeakGridSpace.LevelCell G.toWeakGridSpace k) :=
    fun _ => Fintype.toEncodable _
  letI : Encodable (SouzaCellIndex G) := inferInstance
  obtain ⟨h, hflat, hae⟩ := souzaDomainTermLp_hasSum G s hs R hRfin
  let domainNat : ℕ → Set α := fun n =>
    match Encodable.decode₂ (SouzaCellIndex G) n with
    | some iQ => iQ.2.1
    | none => Set.univ
  let coeffNat : ℕ → ℂ :=
    decode₂WithZero (fun iQ : SouzaCellIndex G =>
      souzaDomainFlattenedCoeff G s hs R iQ)
  have huniv_mem : Set.univ ∈ 𝓦hat := by
    exact h𝓦.grid_subset (show Set.univ ∈ gridCellSet G from ⟨0, by
      simp [GoodGridSpace.toWeakGridSpace, GoodGridSpace.toWeakGrid,
        G.grid.grid.first_partition_eq_univ]⟩)
  have hdomain_mem : ∀ n, domainNat n ∈ 𝓦hat := by
    intro n
    dsimp [domainNat]
    cases hdec : Encodable.decode₂ (SouzaCellIndex G) n with
    | none => exact huniv_mem
    | some iQ =>
        exact h𝓦.grid_subset (show iQ.2.1 ∈ gridCellSet G from ⟨iQ.1, iQ.2.2⟩)
  let hmemLp : MemLp (g : α → ℂ) (domainEndpointExponent s) G.grid.μ :=
    MeasureTheory.MemLp.ae_eq hae (Lp.memLp h)
  have hterm_memLp : ∀ n, MemLp
      (fun z => coeffNat n * normalizedDomainIndicator G s (domainNat n) z)
      (domainEndpointExponent s) G.grid.μ := by
    intro n
    dsimp [coeffNat, domainNat]
    cases hdec : Encodable.decode₂ (SouzaCellIndex G) n with
    | some iQ =>
        simpa [decode₂WithZero, hdec] using
          souzaDomainFlattenedCoeff_domainTerm_memLp G s hs R iQ
    | none =>
        simp [decode₂WithZero, hdec]
  have htarget :
      MemLp.toLp (g : α → ℂ) hmemLp = h := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hmemLp).trans hae.symm
  let decodedTermNat : ℕ → Lp ℂ (domainEndpointExponent s) G.grid.μ :=
    decode₂WithZero (fun iQ : SouzaCellIndex G => souzaDomainTermLp G s hs R iQ)
  have hnat :
      HasSum decodedTermNat h := by
    dsimp [decodedTermNat]
    exact (hasSum_decode₂WithZero_iff
      (β := SouzaCellIndex G)
      (E := Lp ℂ (domainEndpointExponent s) G.grid.μ)
      (f := fun iQ : SouzaCellIndex G => souzaDomainTermLp G s hs R iQ)
      (a := h)).mpr hflat
  have hrep_hasSum :
      HasSum
        (fun n =>
          MemLp.toLp
            (fun z => coeffNat n * normalizedDomainIndicator G s (domainNat n) z)
            (hterm_memLp n))
        (MemLp.toLp (g : α → ℂ) hmemLp) := by
    rw [htarget]
    refine hnat.congr_fun ?_
    intro n
    cases hdec : Encodable.decode₂ (SouzaCellIndex G) n with
    | some iQ =>
        simp only [decodedTermNat, decode₂WithZero, hdec, Option.elim_some]
        apply Lp.ext
        refine (MemLp.coeFn_toLp (hterm_memLp n)).trans ?_
        have hfun :
            (fun z => coeffNat n * normalizedDomainIndicator G s (domainNat n) z)
              =
            (fun z => souzaDomainFlattenedCoeff G s hs R iQ *
              normalizedDomainIndicator G s iQ.2.1 z) := by
          have hcoeff_decode :
              coeffNat n = souzaDomainFlattenedCoeff G s hs R iQ := by
            dsimp [coeffNat, decode₂WithZero]
            rw [hdec]
            simp
          have hdomain_decode : domainNat n = iQ.2.1 := by
            dsimp [domainNat]
            rw [hdec]
          funext z
          rw [hcoeff_decode, hdomain_decode]
        exact (Filter.EventuallyEq.of_eq hfun).trans
          (MemLp.coeFn_toLp
            (souzaDomainFlattenedCoeff_domainTerm_memLp G s hs R iQ)).symm
    | none =>
        simp only [decodedTermNat, decode₂WithZero, hdec, Option.elim_none]
        apply Lp.ext
        refine (MemLp.coeFn_toLp (hterm_memLp n)).trans ?_
        have hfun :
            (fun z => coeffNat n * normalizedDomainIndicator G s (domainNat n) z)
              =
            (0 : α → ℂ) := by
          have hcoeff_decode : coeffNat n = 0 := by
            dsimp [coeffNat, decode₂WithZero]
            rw [hdec]
            simp
          have hdomain_decode : domainNat n = Set.univ := by
            dsimp [domainNat]
            rw [hdec]
          funext z
          rw [hcoeff_decode, hdomain_decode]
          simp
        exact (Filter.EventuallyEq.of_eq hfun).trans
          (Lp.coeFn_zero ℂ (domainEndpointExponent s) G.grid.μ).symm
  have hcoeff_summable :
      Summable fun n => ‖coeffNat n‖ := by
    let fraw : SouzaCellIndex G → ℝ :=
      fun iQ => ‖souzaDomainFlattenedCoeff G s hs R iQ‖
    have hraw :
        Summable (decode₂WithZero fraw) := by
      exact (summable_decode₂WithZero_iff
        (β := SouzaCellIndex G)
        (E := ℝ)
        (f := fraw)).mpr
        (souzaDomainFlattenedCoeff_summable_norm_and_tsum_le G s hs R hRfin).1
    refine hraw.congr ?_
    intro n
    dsimp [fraw, coeffNat, decode₂WithZero]
    cases Encodable.decode₂ (SouzaCellIndex G) n <;> simp
  let DR : DomainAtomicRepresentation G s 𝓦hat (g : α → ℂ) :=
    { domain := domainNat
      domain_mem := hdomain_mem
      coeff := coeffNat
      memLp := hmemLp
      term_memLp := hterm_memLp
      hasSum := hrep_hasSum
      coeff_summable := hcoeff_summable }
  refine ⟨DR, ?_⟩
  have hcoeff_tsum :
      DR.coeffCost =
        ∑' iQ : SouzaCellIndex G, ‖souzaDomainFlattenedCoeff G s hs R iQ‖ := by
    let fraw : SouzaCellIndex G → ℝ :=
      fun iQ => ‖souzaDomainFlattenedCoeff G s hs R iQ‖
    calc
      DR.coeffCost
          = ∑' n : ℕ, decode₂WithZero fraw n := by
            dsimp [DR, DomainAtomicRepresentation.coeffCost, coeffNat]
            apply tsum_congr
            intro n
            dsimp [decode₂WithZero]
            cases Encodable.decode₂ (SouzaCellIndex G) n <;> simp [fraw]
      _ = ∑' iQ : SouzaCellIndex G, fraw iQ := by
            exact tsum_decode₂WithZero_eq
              (f := fraw)
              (by
                dsimp [fraw]
                exact
                  (souzaDomainFlattenedCoeff_summable_norm_and_tsum_le G s hs R hRfin).1)
      _ = ∑' iQ : SouzaCellIndex G, ‖souzaDomainFlattenedCoeff G s hs R iQ‖ := by
            rfl
  rw [hcoeff_tsum]
  exact (souzaDomainFlattenedCoeff_summable_norm_and_tsum_le G s hs R hRfin).2

/--
Every Souza `B^s_{1,1}` element admits a normalized-domain representation with
domains in `𝓦hat`.

This is the second half of Proposition `rema`: a Souza representation already
uses grid cells, and `𝓟 ⊆ 𝓦hat`.
-/
theorem souzaBesov11_to_domainBesovSpace
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat) :
    ∀ x : SouzaBesov11 G s hs,
      DomainBesovSpace G s 𝓦hat
        ((x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) : α → ℂ) ∧
      domainBesovGauge G s 𝓦hat
        ((x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) : α → ℂ) ≤
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
          (1 : ℝ≥0∞) x := by
  classical
  intro x
  let A := souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top
  have hA :
      WeakGridSpace.BesovishSpace.HasFiniteCostRepresentations
        (A := A) (1 : ℝ≥0∞) :=
    WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations A (1 : ℝ≥0∞)
  rcases hA x with ⟨R₀, hR₀fin⟩
  obtain ⟨DR₀, _hDR₀cost⟩ :=
    domainAtomicRepresentation_of_souzaRepresentation
      G s C c 𝓦hat hs h𝓦 R₀ hR₀fin
  refine ⟨⟨DR₀⟩, ?_⟩
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  rcases WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add
      (A := A) (q := (1 : ℝ≥0∞)) hA x hε with
    ⟨Rε, hRεfin, hRεlt⟩
  obtain ⟨DRε, hDRεcost⟩ :=
    domainAtomicRepresentation_of_souzaRepresentation
      G s C c 𝓦hat hs h𝓦 Rε hRεfin
  calc
    domainBesovGauge G s 𝓦hat
        ((x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) : α → ℂ)
        ≤ DRε.coeffCost :=
          domainBesovGauge_le_coeffCost G s 𝓦hat DRε
    _ ≤ WeakGridSpace.LpGridRepresentation.pqCost (q := (1 : ℝ≥0∞)) Rε :=
          hDRεcost
    _ ≤ WeakGridSpace.BesovishSpace.Norm_Costpq A (1 : ℝ≥0∞) x + ε :=
          le_of_lt hRεlt

/--
Proposition `rema`: the alternative regular-domain space and Souza
`B^s_{1,1}` have the same concrete representatives, and their gauges are
equivalent.
-/
theorem domainBesovSpace_equiv_souzaBesov11
    (G : GoodGridSpace (α := α)) (s C c : ℝ) (𝓦hat : Set (Set α))
    [Fact (1 ≤ domainEndpointExponent s)]
    (hs : 0 < s) (hs_lt_one : s < 1)
    (h𝓦 : AdmissibleDomainClass G s C c 𝓦hat) :
    (∃ C₀ : ℝ,
      0 ≤ C₀ ∧
      ∀ f : α → ℂ,
        DomainBesovSpace G s 𝓦hat f →
          ∃ x : SouzaBesov11 G s hs,
            WeakGridSpace.RepresentsFunction
              (G := G.toWeakGridSpace) (p := (1 : ℝ≥0∞))
              f (x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) ∧
            WeakGridSpace.BesovishSpace.Norm_Costpq
                (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
                (1 : ℝ≥0∞) x ≤
              C₀ * domainBesovGauge G s 𝓦hat f) ∧
    (∀ x : SouzaBesov11 G s hs,
      DomainBesovSpace G s 𝓦hat
        ((x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) : α → ℂ) ∧
      domainBesovGauge G s 𝓦hat
        ((x : Lp ℂ (1 : ℝ≥0∞) G.toWeakGridSpace.measure) : α → ℂ) ≤
        WeakGridSpace.BesovishSpace.Norm_Costpq
          (souzaAtomFamily G s (1 : ℝ≥0∞) hs le_rfl ENNReal.one_ne_top)
          (1 : ℝ≥0∞) x) := by
  exact ⟨domainBesovSpace_to_souzaBesov11 G s C c 𝓦hat hs hs_lt_one h𝓦,
    souzaBesov11_to_domainBesovSpace G s C c 𝓦hat hs h𝓦⟩

end

end GoodGridSpace
