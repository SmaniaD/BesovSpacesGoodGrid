import BesovSpacesGoodGrid.GoodGrid.Multipliers.NonArchimedeanProperty

/-!
# Pointwise Multipliers II: `B^{1/p}_{p,∞} ∩ L^∞` consists of multipliers

This file formalizes Proposition `mult` (Pointwise Multipliers II) of the
paper *Besov-ish spaces through atomic decomposition*: every function `g` in
`B^{1/p}_{p,∞} ∩ L^∞` is a pointwise multiplier of the Souza Besov space
`B^s_{p,q}` for `0 < s < 1/p`, with operator bound of the shape
`C · |g|_{B^{1/p}_{p,∞}} + |g|_∞`.

The paper's proof splits the product `g·f` into two atomic pieces: for
near-optimal representations `f = ∑ c_Q a_Q` and `g = ∑ e_J b_J` (the latter
given by Corollary `fou`, with canonical `(1/p, p)`-atoms `b_J = 1_J`),

* `u₁` collects the terms with `J ⊊ Q`, whose level coefficient norms form a
  convolution with the geometric kernel `λ₂^{(j-k)(1/p-s)}` — this yields the
  factor `|g|_{B^{1/p}_{p,∞}} / (1 - λ₂^{1/p-s})`;
* `u₂` collects the terms with `Q ⊆ J`, whose coefficients are
  `c_Q · (∑_{J ⊇ Q} e_J)`; by Proposition `boup`.B the tower sums
  `∑_{J ⊇ Q} e_J` are bounded by `|g|_∞`, giving the factor `|g|_∞`;

and the identity `g·f = u₁ + u₂` is obtained from truncations converging in
`L¹` together with the compactness/limit machinery of Corollary `compa1`.

## Main result

* `souzaPointwiseMultipliersII`: the quantitative multiplier bound.

## Current state of the proof

The outer proof (the ε-optimization over near-optimal representations of `f`
and the uniqueness of the product representative in `L^p`) is complete.  Two
inner sublemmas are still `sorry`, with their mathematical content clearly
delimited:

* `exists_fouRepresentation` — the input from Corollary `fou` and
  Proposition `boup`.B: a canonical-atom representation of `g` with
  `(p,∞)`-cost controlled by `|g|_{B^{1/p}_{p,∞}}` and all ancestor-tower
  coefficient sums bounded by `|g|_∞`.  This should be derived from the
  standard-representation machinery in `AlternativeRepresentationsAndNorms`
  (Theorem 15.1 / Corollary `fou`), plus the not-yet-formalized
  Proposition 17.1 (`boup`).
* `exists_mult_product_representation` — the `u₁ + u₂` construction: the
  convolution estimate for `u₁`, the `L^∞` estimate for `u₂`, and the `L¹`
  truncation argument identifying `g·f = u₁ + u₂` via
  `representation_limit_strong_existence` (Corollary `compa1`).
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

/--
The ancestor-tower coefficient sum of a representation at a cell `Q`: the sum
of the coefficients of all cells `J` of level at most `Q.level` containing
`Q`.  For the canonical-atom representation of `g` produced by Corollary
`fou`, this is the quantity `∑_{J ⊇ Q} e_J` controlled by `|g|_∞` in the
paper (Proposition `boup`.B); since the cells containing `Q` at each level
are unique, the inner sums have a single nonzero term.
-/
def ancestorCoeffSum
    (G : GoodGridSpace (α := α)) {s' : ℝ} {p' : ℝ≥0∞}
    {hs' : 0 < s'} {hp' : 1 ≤ p'} {hp'_top : p' ≠ ∞}
    [Fact (1 ≤ p')]
    {x : Lp ℂ p' G.toWeakGridSpace.measure}
    (R : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s' p' hs' hp' hp'_top) x)
    {k : ℕ} (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k) : ℂ := by
  classical
  exact ∑ j ∈ Finset.range (k + 1),
    ∑ J : WeakGridSpace.LevelCell G.toWeakGridSpace j,
      if Q.1 ⊆ J.1 then (R.block j).coeff J else 0

/--
**Input from Corollary `fou` and Proposition `boup`.B** (still `sorry`).

Every `g ∈ B^{1/p}_{p,∞} ∩ L^∞` admits a canonical-atom Souza representation
`R_g` whose `(p,∞)`-coefficient cost is controlled by a universal constant
times `|g|_{B^{1/p}_{p,∞}}`, and whose ancestor-tower coefficient sums are
all bounded by the essential bound `M` of `g`.

Mathematical content: take the standard representation of `g` (Theorem 15.1
and Corollary `fou`, already formalized in pieces in
`AlternativeRepresentationsAndNorms`); its tower sums are conditional
averages of `g` over cells, hence bounded by `|g|_∞` — this last step is
Proposition 17.1 (`boup`).B, not yet formalized.
-/
theorem exists_fouRepresentation
    (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] :
    ∃ Cfou : ℝ,
      0 ≤ Cfou ∧
      ∀ (g : α → ℂ) (M : ℝ)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        ∃ Rg : WeakGridSpace.LpGridRepresentation
            (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top)
            (xg : Lp ℂ p G.toWeakGridSpace.measure),
          SouzaCanonicalRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg ∧
          WeakGridSpace.LpGridRepresentation.FinitePQCost (q := ∞) Rg ∧
          WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg ≤
            Cfou * WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞ xg ∧
          ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
            ‖ancestorCoeffSum G Rg Q‖ ≤ M := by
  sorry

/--
The level-`k` block of the piece `u₂` of the paper's proof: it reuses the
atoms of the representation of `f`, and multiplies each coefficient `c_Q` by
the ancestor-tower sum `∑_{J ⊇ Q} e_J` of the representation of `g`.

This realizes the paper's identity `a_Q · b_J = a_Q` for `Q ⊆ J`: collecting
all such terms attaches to the cell `Q` the coefficient
`c_Q · ∑_{J ⊇ Q} e_J`, with the original atom of `f` unchanged.
-/
private noncomputable def multU2Block
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg)
    (k : ℕ) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) k where
  coeff := fun Q => (Rf.block k).coeff Q * ancestorCoeffSum G Rg Q
  atom := (Rf.block k).atom
  atom_mem := (Rf.block k).atom_mem

/--
Levelwise cost of the `u₂` blocks: when all ancestor-tower sums of `Rg` are
bounded by `M`, the `p`-th power coefficient sum of `multU2Block` at each
level is at most `M^p` times that of `Rf`.

This is the paper's estimate
`(∑_Q |c_Q · ∑_{J ⊇ Q} e_J|^p)^{1/p} ≤ |g|_∞ · (∑_Q |c_Q|^p)^{1/p}`.
-/
private theorem multU2Block_levelCoeffPower_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg)
    {M : ℝ} (hM0 : 0 ≤ M)
    (htower : ∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
      ‖ancestorCoeffSum G Rg Q‖ ≤ M)
    (k : ℕ) :
    (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(multU2Block G s p hs h1p hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal) ≤
      M ^ p.toReal * Rf.levelCoeffPower k := by
  have hpt_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp_top
  have hterm : ∀ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
      ‖(multU2Block G s p hs h1p hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal ≤
        M ^ p.toReal * ‖(Rf.block k).coeff Q‖ ^ p.toReal := by
    intro Q
    have hnorm :
        ‖(multU2Block G s p hs h1p hp hp_top Rf Rg k).coeff Q‖ =
          ‖(Rf.block k).coeff Q‖ * ‖ancestorCoeffSum G Rg Q‖ :=
      norm_mul _ _
    have hle :
        ‖(Rf.block k).coeff Q‖ * ‖ancestorCoeffSum G Rg Q‖ ≤
          ‖(Rf.block k).coeff Q‖ * M :=
      mul_le_mul_of_nonneg_left (htower k Q) (norm_nonneg _)
    calc
      ‖(multU2Block G s p hs h1p hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal
          ≤ (‖(Rf.block k).coeff Q‖ * M) ^ p.toReal := by
        rw [hnorm]
        exact Real.rpow_le_rpow
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hle hpt_pos.le
      _ = M ^ p.toReal * ‖(Rf.block k).coeff Q‖ ^ p.toReal := by
        rw [Real.mul_rpow (norm_nonneg _) hM0, mul_comm]
  calc
    (∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
        ‖(multU2Block G s p hs h1p hp hp_top Rf Rg k).coeff Q‖ ^ p.toReal)
        ≤ ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            M ^ p.toReal * ‖(Rf.block k).coeff Q‖ ^ p.toReal :=
      Finset.sum_le_sum fun Q _ => hterm Q
    _ = M ^ p.toReal *
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            ‖(Rf.block k).coeff Q‖ ^ p.toReal := by
      rw [Finset.mul_sum]
    _ = M ^ p.toReal * Rf.levelCoeffPower k := rfl

/--
The level-`j` block of the piece `u₁` of the paper's proof: on each cell `J`
it carries the coefficient `e_J · ∑_{Q ⊋ J} c_Q v_Q μ(J)^{1/p−s}` over the
canonical `(s,p)`-Souza atom on `J`, where `v_Q` is the value of the atom of
`Rf` at `Q`.  This realizes the paper's identity
`a_Q · b_J = (value of a_Q) · μ(J)^{1/p−s} · (canonical a_J)` for `J ⊊ Q`:
the strict ancestors `Q ⊋ J` are exactly the cells of levels `k < j`
containing `J`.
-/
private noncomputable def multU1Block
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg)
    (j : ℕ) :
    WeakGridSpace.LevelBlock (souzaAtomFamily G s p hs hp hp_top) j := by
  classical
  exact
  { coeff := fun J =>
      (Rg.block j).coeff J *
        ∑ k ∈ Finset.range j,
          ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
            if J.1 ⊆ Q.1 then
              (Rf.block k).coeff Q *
                (show ℂ from (Rf.block k).atom Q) *
                (((G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
            else 0
    atom := fun J =>
      (((G.grid.μ J.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)
    atom_mem := fun J => by
      change ‖(((G.grid.μ J.1).toReal ^ (s - (p.toReal)⁻¹) : ℝ) : ℂ)‖ ≤
        (G.grid.μ J.1).toReal ^ (s - (p.toReal)⁻¹)
      rw [Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)] }

open Classical in
/--
Pointwise coefficient bound for the `u₁` blocks: the transmutation factor of
each strict ancestor at level `k < j` is at most `λ₂^{(j−k)(1/p−s)}`, so

`‖coeff(u₁)_J‖ ≤ ‖e_J‖ · ∑_{k<j} λ₂^{(j−k)(1/p−s)} ·
  (∑_{Q ∈ P^k, Q ⊇ J} ‖c_Q‖)`.

The inner sum over `Q` has at most one nonzero term (the level-`k` ancestor
of `J`).  This is the per-cell input to the paper's convolution estimate.
-/
private theorem multU1Block_coeff_norm_le
    (G : GoodGridSpace (α := α)) (s : ℝ) (p : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)]
    {x xg : Lp ℂ p G.toWeakGridSpace.measure}
    (Rf : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G s p hs hp hp_top) x)
    (Rg : WeakGridSpace.LpGridRepresentation
      (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) xg)
    (j : ℕ) (J : WeakGridSpace.LevelCell G.toWeakGridSpace j) :
    ‖(multU1Block G s p hs h1p hp hp_top Rf Rg j).coeff J‖ ≤
      ‖(Rg.block j).coeff J‖ *
        ∑ k ∈ Finset.range j,
          (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) *
            ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              (if J.1 ⊆ Q.1 then ‖(Rf.block k).coeff Q‖ else 0) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.grid.μ := G.grid.isFinite
  have hθ : 0 < (p.toReal)⁻¹ - s := sub_pos.mpr hs_lt_inv
  have hlam_nonneg : 0 ≤ G.grid.lambda2 :=
    le_trans G.grid.hlambda1_pos.le G.grid.hlambda1_le_lambda2
  have hcoeff :
      (multU1Block G s p hs h1p hp hp_top Rf Rg j).coeff J =
        (Rg.block j).coeff J *
          ∑ k ∈ Finset.range j,
            ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
              if J.1 ⊆ Q.1 then
                (Rf.block k).coeff Q *
                  (show ℂ from (Rf.block k).atom Q) *
                  (((G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)
              else 0 := rfl
  rw [hcoeff, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun k hk => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun Q _ => ?_
  by_cases hJQ : J.1 ⊆ Q.1
  · rw [if_pos hJQ, if_pos hJQ]
    -- The measure-ratio estimate for the level-`k` ancestor.
    have hkj : k ≤ j := (Finset.mem_range.mp hk).le
    have hJmem : J.1 ∈ G.grid.grid.partitions (k + (j - k)) := by
      rw [Nat.add_sub_cancel' hkj]
      exact J.2
    have hμJ_le :
        G.grid.μ J.1 ≤
          (ENNReal.ofReal G.grid.lambda2) ^ (j - k) * G.grid.μ Q.1 :=
      cell_measure_le_lambda2_pow_mul_cell G ⟨k, Q.1, Q.2⟩ (j - k) J.1
        hJmem hJQ
    have hμQ_pos : 0 < (G.grid.μ Q.1).toReal :=
      ENNReal.toReal_pos
        (G.grid.positive_measure k Q.1 Q.2).ne'
        (MeasureTheory.measure_ne_top G.grid.μ Q.1)
    have hμJ_real :
        (G.grid.μ J.1).toReal ≤
          G.grid.lambda2 ^ (j - k) * (G.grid.μ Q.1).toReal := by
      have hRHS_ne :
          (ENNReal.ofReal G.grid.lambda2) ^ (j - k) * G.grid.μ Q.1 ≠ ∞ :=
        ENNReal.mul_ne_top
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          (MeasureTheory.measure_ne_top G.grid.μ Q.1)
      have := ENNReal.toReal_mono hRHS_ne hμJ_le
      rwa [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hlam_nonneg] at this
    -- The atom value is controlled by the Souza normalization.
    have hatom_le :
        ‖(show ℂ from (Rf.block k).atom Q)‖ ≤
          (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) :=
      (Rf.block k).atom_mem Q
    -- The transmutation factor estimate.
    have hfactor :
        ‖(show ℂ from (Rf.block k).atom Q)‖ *
            (G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) ≤
          (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) := by
      have hμJθ :
          (G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) ≤
            (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) *
              (G.grid.μ Q.1).toReal ^ ((p.toReal)⁻¹ - s) := by
        rw [← Real.mul_rpow (pow_nonneg hlam_nonneg _) hμQ_pos.le]
        exact Real.rpow_le_rpow ENNReal.toReal_nonneg hμJ_real hθ.le
      calc
        ‖(show ℂ from (Rf.block k).atom Q)‖ *
            (G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s)
            ≤ (G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) *
                ((G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) *
                  (G.grid.μ Q.1).toReal ^ ((p.toReal)⁻¹ - s)) :=
          mul_le_mul hatom_le hμJθ
            (Real.rpow_nonneg ENNReal.toReal_nonneg _)
            (Real.rpow_nonneg ENNReal.toReal_nonneg _)
        _ = (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) *
              ((G.grid.μ Q.1).toReal ^ (s - (p.toReal)⁻¹) *
                (G.grid.μ Q.1).toReal ^ ((p.toReal)⁻¹ - s)) := by ring
        _ = (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) := by
          rw [← Real.rpow_add hμQ_pos]
          have hzero : (s - (p.toReal)⁻¹) + ((p.toReal)⁻¹ - s) = 0 := by
            ring
          rw [hzero, Real.rpow_zero, mul_one]
    -- Assemble the per-term bound.
    have hμJθ_nonneg :
        (0 : ℝ) ≤ (G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    calc
      ‖(Rf.block k).coeff Q * (show ℂ from (Rf.block k).atom Q) *
          (((G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s) : ℝ) : ℂ)‖
          = ‖(Rf.block k).coeff Q‖ *
              (‖(show ℂ from (Rf.block k).atom Q)‖ *
                (G.grid.μ J.1).toReal ^ ((p.toReal)⁻¹ - s)) := by
        rw [norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hμJθ_nonneg, mul_assoc]
      _ ≤ ‖(Rf.block k).coeff Q‖ *
            (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) :=
        mul_le_mul_of_nonneg_left hfactor (norm_nonneg _)
      _ = (G.grid.lambda2 ^ (j - k)) ^ ((p.toReal)⁻¹ - s) *
            ‖(Rf.block k).coeff Q‖ := by ring
  · rw [if_neg hJQ, if_neg hJQ]
    simp

/--
**The `u₁ + u₂` construction** (still `sorry`).

Given a finite-cost representation `R_f` of `x` and a canonical-atom
representation `R_g` of `g` with bounded ancestor-tower sums, the product
`g·f` has a Besov representative `y` with

`‖y‖ ≤ (Cconv · pqCost_{(p,∞)} R_g + M) · pqCost_{(p,q)} R_f`,

where `Cconv = Cconv(G, s, p)` reflects the geometric series
`∑_n λ₂^{n(1/p−s)} = (1 − λ₂^{1/p−s})⁻¹`.

Mathematical content (the body of the paper's proof): split
`a_Q · b_J = a_Q` for `Q ⊆ J` and `a_Q · b_J = (|J|/|Q|)^{1/p−s} a_J` for
`J ⊊ Q`; assemble `u₁` (convolution estimate over levels, Young's
inequality) and `u₂` (tower-sum estimate); identify `g·f = u₁ + u₂` through
`L¹`-convergent truncations and `representation_limit_strong_existence`.
-/
theorem exists_mult_product_representation
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cconv : ℝ,
      0 ≤ Cconv ∧
      ∀ (g : α → ℂ) (M : ℝ) (hM : 0 ≤ M)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞)
        (Rg : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top)
          (xg : Lp ℂ p G.toWeakGridSpace.measure))
        (x : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G s p hs hp hp_top) q)
        (Rf : WeakGridSpace.LpGridRepresentation
          (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure)),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        SouzaCanonicalRepresentation G (p.toReal)⁻¹ p h1p hp hp_top Rg →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := ∞) Rg →
        (∀ (k : ℕ) (Q : WeakGridSpace.LevelCell G.toWeakGridSpace k),
          ‖ancestorCoeffSum G Rg Q‖ ≤ M) →
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rf →
        ∃ y : WeakGridSpace.BesovishSpace
            (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsPointwiseProduct
            (G := G.toWeakGridSpace) (p := p) g
            (x : Lp ℂ p G.toWeakGridSpace.measure)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G s p hs hp hp_top) q y ≤
            (Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg
                + M) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf := by
  sorry

/--
**Proposition `mult` of the paper (Pointwise Multipliers II).**

Let `0 < s < 1/p`.  There is a constant `Cmult` such that every function
`g ∈ B^{1/p}_{p,∞} ∩ L^∞` — formally: `g` is represented by a Besov-ish
element `xg` of the `(1/p, p, ∞)` Souza space and `‖g‖ ≤ M` almost
everywhere — is a pointwise multiplier of `B^s_{p,q}` with operator bound

`|G|_{B^s_{p,q}} ≤ Cmult · |g|_{B^{1/p}_{p,∞}} + M`,

the formal counterpart of the paper's bound
`Ce·Cno·|g|_{B^{1/p}_{p,∞}}/(1 − λ₂^{1/p−s}) + |g|_∞`.
-/
theorem souzaPointwiseMultipliersII
    (G : GoodGridSpace (α := α)) (s : ℝ) (p q : ℝ≥0∞)
    (hs : 0 < s) (hs_lt_inv : s < (p.toReal)⁻¹)
    (h1p : 0 < (p.toReal)⁻¹) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    ∃ Cmult : ℝ,
      0 ≤ Cmult ∧
      ∀ (g : α → ℂ) (M : ℝ)
        (xg : WeakGridSpace.BesovishSpace
          (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞),
        WeakGridSpace.RepresentsFunction
          (G := G.toWeakGridSpace) (p := p) g
          (xg : Lp ℂ p G.toWeakGridSpace.measure) →
        (∀ᵐ z ∂G.toWeakGridSpace.measure, ‖g z‖ ≤ M) →
        SouzaPointwiseMultiplierBound G s p q hs hp hp_top g
          (Cmult * WeakGridSpace.BesovishSpace.Norm_Costpq
              (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞ xg
            + M) := by
  classical
  obtain ⟨Cfou, hCfou0, hCfou⟩ :=
    exists_fouRepresentation G p h1p hp hp_top
  obtain ⟨Cconv, hCconv0, hCconv⟩ :=
    exists_mult_product_representation G s p q hs hs_lt_inv h1p hp hp_top
  refine ⟨Cconv * Cfou, mul_nonneg hCconv0 hCfou0, ?_⟩
  intro g M xg hgrep hgM
  set Ng : ℝ := WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞ xg with hNg
  -- The essential bound is nonnegative, since the measure is nonzero.
  have hM0 : 0 ≤ M := by
    have hμpos : 0 < G.grid.μ Set.univ := by
      refine G.grid.positive_measure 0 Set.univ ?_
      rw [G.grid.grid.first_partition_eq_univ]
      exact Finset.mem_singleton_self _
    have hμne : G.toWeakGridSpace.measure ≠ 0 := by
      intro h0
      rw [show G.toWeakGridSpace.measure = G.grid.μ from rfl] at h0
      rw [h0] at hμpos
      simp at hμpos
    haveI : (Filter.NeBot (MeasureTheory.ae G.toWeakGridSpace.measure)) :=
      MeasureTheory.ae_neBot.mpr hμne
    obtain ⟨z, hz⟩ := hgM.exists
    exact le_trans (norm_nonneg (g z)) hz
  have hNg0 : 0 ≤ Ng :=
    WeakGridSpace.BesovishSpace.Norm_Costpq_nonneg (A := souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) (q := ∞)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (souzaAtomFamily G (p.toReal)⁻¹ p h1p hp hp_top) ∞) xg
  -- The `fou` representation of `g`.
  obtain ⟨Rg, hRgcanon, hRgfin, hRgcost, hRgtower⟩ := hCfou g M xg hgrep hgM
  have hCbound :
      Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg + M ≤
        Cconv * Cfou * Ng + M := by
    have := mul_le_mul_of_nonneg_left hRgcost hCconv0
    calc
      Cconv * WeakGridSpace.LpGridRepresentation.pqCost (q := ∞) Rg + M
          ≤ Cconv * (Cfou * Ng) + M := by linarith
      _ = Cconv * Cfou * Ng + M := by ring
  have hK0 : 0 ≤ Cconv * Cfou * Ng + M := by positivity
  refine ⟨hK0, ?_⟩
  intro x
  -- One run of the product construction for an arbitrary finite-cost
  -- representation of `x`.
  have key :
      ∀ Rf : WeakGridSpace.LpGridRepresentation (souzaAtomFamily G s p hs hp hp_top)
          (x : Lp ℂ p G.toWeakGridSpace.measure),
        WeakGridSpace.LpGridRepresentation.FinitePQCost (q := q) Rf →
        ∃ y : WeakGridSpace.BesovishSpace (souzaAtomFamily G s p hs hp hp_top) q,
          WeakGridSpace.RepresentsPointwiseProduct
            (G := G.toWeakGridSpace) (p := p) g
            (x : Lp ℂ p G.toWeakGridSpace.measure)
            (y : Lp ℂ p G.toWeakGridSpace.measure) ∧
          WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q y ≤
            (Cconv * Cfou * Ng + M) *
              WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf := by
    intro Rf hRffin
    obtain ⟨y, hyprod, hynorm⟩ :=
      hCconv g M hM0 xg Rg x Rf hgrep hgM hRgcanon hRgfin hRgtower hRffin
    refine ⟨y, hyprod, hynorm.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hCbound
      (WeakGridSpace.LpGridRepresentation.pqCost_nonneg Rf)
  -- Fix the product representative once, then optimize the cost bound.
  obtain ⟨R₁, hR₁fin, _⟩ :=
    WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add (A := souzaAtomFamily G s p hs hp hp_top)
      (q := q)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (souzaAtomFamily G s p hs hp hp_top) q) x
      one_pos
  obtain ⟨y, hyProd, _⟩ := key R₁ hR₁fin
  refine ⟨y, hyProd, ?_⟩
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hden : (0 : ℝ) < Cconv * Cfou * Ng + M + 1 := by linarith
  have hδ : 0 < ε / (Cconv * Cfou * Ng + M + 1) := by positivity
  obtain ⟨Rf, hRffin, hRflt⟩ :=
    WeakGridSpace.BesovishSpace.exists_cost_lt_Norm_Costpq_add (A := souzaAtomFamily G s p hs hp hp_top)
      (q := q)
      (WeakGridSpace.BesovishSpace.hasFiniteCostRepresentations (souzaAtomFamily G s p hs hp hp_top) q) x hδ
  obtain ⟨y', hy'Prod, hy'Norm⟩ := key Rf hRffin
  have hyy' : y' = y := by
    apply Subtype.ext
    apply Lp.ext
    exact hy'Prod.trans hyProd.symm
  have hcost_le :
      WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf ≤
        WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q x +
          ε / (Cconv * Cfou * Ng + M + 1) :=
    hRflt.le
  have hmul :
      (Cconv * Cfou * Ng + M) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf ≤
        (Cconv * Cfou * Ng + M) *
          (WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q x +
            ε / (Cconv * Cfou * Ng + M + 1)) :=
    mul_le_mul_of_nonneg_left hcost_le hK0
  have hfrac :
      (Cconv * Cfou * Ng + M) *
          (ε / (Cconv * Cfou * Ng + M + 1)) ≤ ε := by
    have hratio :
        (Cconv * Cfou * Ng + M) / (Cconv * Cfou * Ng + M + 1) ≤ (1 : ℝ) :=
      (div_le_one hden).2 (by linarith)
    have hmul' := mul_le_mul_of_nonneg_right hratio hε.le
    calc
      (Cconv * Cfou * Ng + M) * (ε / (Cconv * Cfou * Ng + M + 1))
          = ((Cconv * Cfou * Ng + M) / (Cconv * Cfou * Ng + M + 1)) * ε := by
        ring
      _ ≤ 1 * ε := hmul'
      _ = ε := one_mul ε
  calc
    WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q y
        = WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q y' := by rw [hyy']
    _ ≤ (Cconv * Cfou * Ng + M) *
          WeakGridSpace.LpGridRepresentation.pqCost (q := q) Rf := hy'Norm
    _ ≤ (Cconv * Cfou * Ng + M) *
          (WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q x +
            ε / (Cconv * Cfou * Ng + M + 1)) := hmul
    _ = (Cconv * Cfou * Ng + M) *
          WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q x +
          (Cconv * Cfou * Ng + M) *
            (ε / (Cconv * Cfou * Ng + M + 1)) := by ring
    _ ≤ (Cconv * Cfou * Ng + M) *
          WeakGridSpace.BesovishSpace.Norm_Costpq (souzaAtomFamily G s p hs hp hp_top) q x + ε := by
      linarith

end

end GoodGridSpace
