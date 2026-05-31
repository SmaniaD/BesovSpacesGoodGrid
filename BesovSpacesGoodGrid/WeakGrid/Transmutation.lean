import BesovSpacesGoodGrid.WeakGrid.Atoms
import BesovSpacesGoodGrid.WeakGrid.BesovishSpaces
import BesovSpacesGoodGrid.WeakGrid.Completeness
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order





variable {α : Type*} [MeasurableSpace α]

namespace WeakGridSpace

open scoped ENNReal BigOperators Topology
open MeasureTheory Filter

attribute [local instance] Classical.propDecidable



noncomputable section

variable {G : WeakGridSpace (α := α)} {s : ℝ} {p u q : ℝ≥0∞}
variable [Fact (1 ≤ p)] [Fact (1 ≤ u)] [Fact (1 ≤ q)]

/-- The measure-theoretic, or essential, support of a function.

This is the smallest measurable support expressed as an intersection: a point
belongs to `measureSupport μ f` if it belongs to every measurable set outside
which `f` vanishes almost everywhere.  Unlike `Function.support`, this ignores
changes on null sets. -/
def measureSupport {β : Type*} [Zero β] (μ : Measure α) (f : α → β) : Set α :=
  ⋂₀ {S : Set α | MeasurableSet S ∧ ∀ᵐ x ∂ μ.restrict Sᶜ, f x = 0}



/-- Source coefficient `p`-power for the source grid `GIn`. -/
noncomputable def CoeffPLevel
    (G : WeakGridSpace (α := α))
    (c : (i : ℕ) → LevelCell G i → ℂ) (i : ℕ) : ℝ :=
  ∑ Q : LevelCell G i, ‖c i Q‖ ^ p.toReal

/-- Source coefficient `(p,q)` cost for the source grid `GIn`. -/
noncomputable def  CoeffPQCost
    (G : WeakGridSpace (α := α))
    (c : (i : ℕ) → LevelCell G i → ℂ) : ℝ :=
  if q = ∞ then
    sSup (Set.range fun i =>
      (CoeffPLevel  (p := p) G c i) ^ (1 / p.toReal))
  else
    (∑' i, (CoeffPLevel  (p := p) G c i) ^
      (q.toReal / p.toReal)) ^ (1 / q.toReal)

/--
Finiteness of the source coefficient `(p,q)` cost, matching
`(∑ᵢ (∑_{Q∈𝓖ⁱ}|c_Q|^p)^{q/p})^{1/q} < ∞`.
-/
def CoeffFinitePQCost
    (G : WeakGridSpace (α := α))
    (c : (i : ℕ) → LevelCell G i → ℂ) : Prop :=
  if q = ∞ then
    BddAbove (Set.range fun i =>
      (CoeffPLevel  (p := p) G c i) ^ (1 / p.toReal))
  else
    Summable fun i =>
      (CoeffPLevel  (p := p) G c i) ^ (q.toReal / p.toReal)

/-- A level selector `k : ℕ → ℕ` is almost linear if it stays between two affine
functions with the same positive slope.

Concretely, there are real constants `A`, `B`, and `r > 0` such that, for every
source level `i`, the chosen output level `k i` lies between `r * i + A` and
`r * i + B`.  In the paper this is the device that keeps the representation
levels `k i` comparable to the source index `i` up to a bounded error.

This condition is used in two places throughout the file:
1. to show that only finitely many source levels can contribute to a fixed
  output level;
2. to replace sums indexed by `k i` with convolution estimates on arithmetic
  progressions. -/
def AlmostLinearSequence (k : ℕ → ℕ) : Prop :=
  ∃ (A B : ℝ) (r : ℝ), r > 0 ∧ ∀ i : ℕ,
    (k i : NNReal) ≤ r * (i : NNReal) + B ∧
    r * (i : NNReal) + A ≤ (k i : NNReal)

/-- For an almost linear sequence, only finitely many indices can land below a
fixed output level.

This is the finiteness statement behind all later truncations: once `k i ≤ j`,
the lower affine bound in `AlmostLinearSequence` forces `i` to lie below an
explicit constant depending on `j`.  As a result, every sum over
`{ i | k i ≤ j }` is automatically finite. -/
private lemma almostLinearSequence_finite_le_level
    {k : ℕ → ℕ} (hk : AlmostLinearSequence k) (j : ℕ) :
    {i : ℕ | k i ≤ j}.Finite := by
  classical
  obtain ⟨A, B, r, hr, hk_bound⟩ := hk
  let M : ℕ := Nat.ceil (((j : ℝ) - A) / r) + 1
  refine (Set.finite_lt_nat M).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  have hlower : r * (i : ℝ) + A ≤ (k i : ℝ) := by
    simpa using (hk_bound i).2
  have hkj : (k i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hi
  have hri_le : r * (i : ℝ) ≤ (j : ℝ) - A := by
    calc
      r * (i : ℝ) ≤ (k i : ℝ) - A := by linarith
      _ ≤ (j : ℝ) - A := by linarith
  have hi_div : (i : ℝ) ≤ ((j : ℝ) - A) / r := by
    rw [le_div_iff₀ hr]
    simpa [mul_comm] using hri_le
  have hi_ceil : i ≤ Nat.ceil (((j : ℝ) - A) / r) := by
    exact_mod_cast (hi_div.trans (Nat.le_ceil (((j : ℝ) - A) / r)))
  omega

/-- For a fixed output level `j`, this is the first source index after which the
almost-linear lower bound forces `k i > j`.

It is the threshold used in Claim III to show that the transmutation data at
level `j` become eventually constant in `N`. -/
noncomputable def transmutationStabilizationIndex (A r : ℝ) (j : ℕ) : ℕ :=
  Nat.ceil (((j : ℝ) - A) / r) + 1

/-- Once the source index is beyond `transmutationStabilizationIndex A r j`, the
almost-linear lower bound implies `j < k i`. -/
private lemma transmutation_lt_level_of_ge_stabilization
    {k : ℕ → ℕ} {A B r : ℝ} (hr : 0 < r)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r * (i : NNReal) + B ∧
      r * (i : NNReal) + A ≤ (k i : NNReal))
    {j i : ℕ}
    (hi : transmutationStabilizationIndex A r j ≤ i) :
    j < k i := by
  have hceil_lt : Nat.ceil (((j : ℝ) - A) / r) < i := by
    have hsucc : Nat.ceil (((j : ℝ) - A) / r) + 1 ≤ i := hi
    omega
  have hdiv_lt : (((j : ℝ) - A) / r) < i := by
    exact lt_of_le_of_lt (Nat.le_ceil (((j : ℝ) - A) / r)) (by exact_mod_cast hceil_lt)
  have hri : (j : ℝ) - A < r * (i : ℝ) := by
    rw [div_lt_iff₀ hr] at hdiv_lt
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv_lt
  have hlower : r * (i : ℝ) + A ≤ (k i : ℝ) := by
    simpa using (hk_bound i).2
  have hj_lt : (j : ℝ) < (k i : ℝ) := by
    linarith
  exact_mod_cast hj_lt

/-- The finite partial source expansion, grouped by source level.

`PartialSumLevels G W h c N` is the sum of the first `N` source levels of the
representation `∑ c i Q • h i Q`, viewed in the target `L^p` space over `W`.
It is the object that Claim I and Claim II decompose into transmutation blocks.

The definition is intentionally finite: all bookkeeping identities in the file
are proved first for this truncated sum, and only later are infinite limits
handled through summability results. -/
def PartialSumLevels
    (G W : WeakGridSpace (α := α))
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) : Lp ℂ p W.measure :=
  ∑ i ∈ Finset.range N, (G.grid.partitions i).attach.sum (fun Q => c i Q • h i Q)




/-- Structural hypothesis saying that each source atom admits a representation on
the target grid with the localization and decay required for transmutation.

For every source cell `Q` at level `i`, the representation `R i Q` must satisfy
three properties:
1. its coefficient family on the target grid has finite `(p,q)` cost;
2. coefficients vanish outside cells contained in `Q`, and also vanish below the
  cutoff level `k i`;
3. above level `k i`, the block cost decays geometrically like `C * lam^(j-k i)`.

This package is the exact input used in Claim II.  The almost-linear sequence
`k` controls where the decay starts, while `lam` and `C` control its size. -/
def RepresentationWsubGandALS
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (_hk : AlmostLinearSequence k)
    (lam : ℝ) (_hlam_pos : 0 < lam) (_hlam_lt : lam < 1)
    (C : ℝ) (_hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    : Prop :=
  ∀ i : ℕ, ∀ Q : LevelCell G i,
      CoeffFinitePQCost (p := p) (q := q) W (fun j S => ((R i Q).block j).coeff S) ∧
      (∀ j : ℕ, ∀ S : LevelCell W j,
        (¬ S.1 ⊆ Q.1 → ((R i Q).block j).coeff S = 0) ∧
        (j < k i → ((R i Q).block j).coeff S = 0)) ∧
      ∀ j : ℕ, k i ≤ j → ((R i Q).levelCoeffPower j) ≤ C * lam ^ (j - k i)


def RepresentationWsubGandALS_pos
  (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (_hk : AlmostLinearSequence k)
    (lam : ℝ) (_hlam_pos : 0 < lam) (_hlam_lt : lam < 1)
    (C : ℝ) (_hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    : Prop :=
  ∀ i : ℕ, ∀ Q : LevelCell G i,
      CoeffFinitePQCost (p := p) (q := q) W (fun j S => ((R i Q).block j).coeff S) ∧
      (∀ j : ℕ, ∀ S : LevelCell W j,
        (¬ S.1 ⊆ Q.1 → ((R i Q).block j).coeff S = 0) ∧
        (j < k i → ((R i Q).block j).coeff S = 0) ∧
        ∃ r : NNReal, ((R i Q).block j).coeff S = (r : ℂ) ∧
        ∀ x, x ∈ S.1 →
          ∃ a : NNReal, 0 < a ∧
            AW.toFunction (levelCellToWeakGridCell W j S) (((R i Q).block j).atom S) x =
              (a : ℂ)) ∧
      ∀ j : ℕ, k i ≤ j → ((R i Q).levelCoeffPower j) ≤ C * lam ^ (j - k i)

/-- Transmutation coefficient for `P ∈ W^j`:
    `m_{P,N} = ∑_{i<N} ∑_{Q ∈ G^i, P ⊆ Q} |c_Q · s_{P,Q}|`
    where `s_{P,Q} = ((R i Q).block j).coeff P`. -/
noncomputable def TransmutationCoeff
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) {j : ℕ} (P : LevelCell W j) : ℝ :=
  ∑ i ∈ Finset.range N,
    ∑ Q ∈ (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1),
      ‖c i Q * ((R i Q).block j).coeff P‖

omit [Fact (1 ≤ u)] [Fact (1 ≤ q)] in
/-- For a fixed target cell `P ∈ W^j`, the transmutation coefficients `m_{P,N}`
stop changing once `N` passes the stabilization threshold determined by the
almost-linear lower bound for `k`. -/
private lemma TransmutationCoeff_stabilizes
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    {j : ℕ} (P : LevelCell W j) :
    ∀ N : ℕ,
      TransmutationCoeff G W AW h R c
          (transmutationStabilizationIndex A_als r_als j + N) P =
        TransmutationCoeff G W AW h R c
          (transmutationStabilizationIndex A_als r_als j) P := by
  intro N
  induction' N with N ih
  · rfl
  · let M := transmutationStabilizationIndex A_als r_als j
    have hk_large : j < k (M + N) := by
      apply transmutation_lt_level_of_ge_stabilization (B := B_als) hr_als hk_bound
      dsimp [M]
      omega
    have hinner_zero :
        ∑ Q ∈ (G.grid.partitions (M + N)).attach.filter (fun Q => P.1 ⊆ Q.1),
          ‖c (M + N) Q * ((R (M + N) Q).block j).coeff P‖ = 0 := by
      apply Finset.sum_eq_zero
      intro Q hQ
      have hcoeff_zero : ((R (M + N) Q).block j).coeff P = 0 :=
        ((hR (M + N) Q).2.1 j P).2 hk_large
      simp [hcoeff_zero]
    calc
      TransmutationCoeff G W AW h R c (transmutationStabilizationIndex A_als r_als j + (N + 1)) P
          = TransmutationCoeff G W AW h R c (M + N) P +
              ∑ Q ∈ (G.grid.partitions (M + N)).attach.filter (fun Q => P.1 ⊆ Q.1),
                ‖c (M + N) Q * ((R (M + N) Q).block j).coeff P‖ := by
            dsimp [TransmutationCoeff]
            have hMN : transmutationStabilizationIndex A_als r_als j + (N + 1) = (M + N) + 1 := by
              simp [M, add_assoc, add_left_comm, add_comm]
            rw [hMN, Finset.sum_range_succ]
      _ = TransmutationCoeff G W AW h R c M P + 0 := by rw [ih, hinner_zero]
      _ = TransmutationCoeff G W AW h R c (transmutationStabilizationIndex A_als r_als j) P := by
            simp [M]

/-- The stable value of the transmutation coefficients at a fixed target cell.
This is the formal `m_{P,∞}` used in Claim III. -/
noncomputable def TransmutationCoeffLimit
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (A_als r_als : ℝ)
    {j : ℕ} (P : LevelCell W j) : ℝ :=
  TransmutationCoeff G W AW h R c (transmutationStabilizationIndex A_als r_als j) P

/-- Beyond the stabilization threshold, the coefficients equal their stable
limit value `m_{P,∞}`. -/
lemma TransmutationCoeff_eq_limit_of_ge
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    {j : ℕ} (P : LevelCell W j)
    {N : ℕ}
    (hN : transmutationStabilizationIndex A_als r_als j ≤ N) :
    TransmutationCoeff G W AW h R c N P =
      TransmutationCoeffLimit G W AW h R c A_als r_als P := by
  let M := transmutationStabilizationIndex A_als r_als j
  have hNM : N = M + (N - M) := by
    dsimp [M]
    omega
  rw [hNM, TransmutationCoeffLimit]
  exact TransmutationCoeff_stabilizes G W AW k A_als B_als r_als hr_als hk_bound
    lam hlam_pos hlam_lt C hC h R hR c P (N - M)

/-- The coefficient sequence `N ↦ m_{P,N}` converges because it is eventually
constant. -/
private lemma TransmutationCoeff_tendsto_limit
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    {j : ℕ} (P : LevelCell W j) :
    Tendsto (fun N => TransmutationCoeff G W AW h R c N P) atTop
      (𝓝 (TransmutationCoeffLimit G W AW h R c A_als r_als P)) := by
  let M := transmutationStabilizationIndex A_als r_als j
  have heq :
      (fun N => TransmutationCoeff G W AW h R c N P) =ᶠ[atTop]
        (fun _ => TransmutationCoeffLimit G W AW h R c A_als r_als P) := by
    refine eventually_atTop.2 ⟨M, ?_⟩
    intro N hN
    exact TransmutationCoeff_eq_limit_of_ge G W AW k A_als B_als r_als hr_als hk_bound
      lam hlam_pos hlam_lt C hC h R hR c P hN
  exact tendsto_const_nhds.congr' heq.symm

/-- Transmutation atom `d_{P,N}` for `P ∈ W^j`: the normalised convex combination
    of the atoms `b_{P,Q}` weighted by `c_Q · s_{P,Q}`.
    When `m_{P,N} = 0` it is defined to be `0`.
    Otherwise `d_{P,N} = (1/m_{P,N}) · ∑_{i<N} ∑_{Q∈G^i,P⊆Q} c_Q·s_{P,Q}·b_{P,Q}`. -/
noncomputable def TransmutationAtom
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) {j : ℕ} (P : LevelCell W j) : Lp ℂ p W.measure :=
  let m := TransmutationCoeff G W AW h R c N P
  let num := ∑ i ∈ Finset.range N,
    ∑ Q ∈ (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1),
      c i Q • ((R i Q).block j).term AW P
  if m = 0 then 0 else (m : ℂ)⁻¹ • num







/-- The transmutation atom `d_{P,N}` as an element of the local vector space
    `AW.localSpace (levelCellToWeakGridCell W j P)`.
    It is the normalised complex combination
    `(1/m) · ∑_{i<N} ∑_{Q∈Gⁱ,P⊆Q} c_Q · s_{P,Q} · b_{P,Q}`
    computed *inside* the local space, where `b_{P,Q}` is the atom stored in
    `(R i Q).block j` and `s_{P,Q} = ((R i Q).block j).coeff P`.
    When `m = 0` it is defined to be `0`. -/
noncomputable def TransmutationAtomLocal
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) {j : ℕ} (P : LevelCell W j) :
    (AW.localSpace (levelCellToWeakGridCell W j P)).carrier :=
  let m := TransmutationCoeff G W AW h R c N P
  -- Flat (sigma) index set: pairs (level i, cell Q) with i < N and P ⊆ Q
  let FS : Finset (Σ i : ℕ, LevelCell G i) :=
    (Finset.range N).sigma
      (fun i => (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1))
  let num :=
    ∑ iQ ∈ FS,
      (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
        ((R iQ.1 iQ.2).block j).atom P
  if m = 0 then 0 else (m : ℂ)⁻¹ • num

/-- For a fixed target cell `P ∈ W^j`, the normalized local atoms `d_{P,N}`
also stabilize once no new source levels can contribute to level `j`. -/
private lemma TransmutationAtomLocal_stabilizes
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    {j : ℕ} (P : LevelCell W j) :
    ∀ N : ℕ,
      TransmutationAtomLocal G W AW h R c
          (transmutationStabilizationIndex A_als r_als j + N) P =
        TransmutationAtomLocal G W AW h R c
          (transmutationStabilizationIndex A_als r_als j) P := by
  intro N
  induction' N with N ih
  · rfl
  · let M := transmutationStabilizationIndex A_als r_als j
    have hk_large : j < k (M + N) := by
      apply transmutation_lt_level_of_ge_stabilization (B := B_als) hr_als hk_bound
      dsimp [M]
      omega
    have hcoeff_step :
        TransmutationCoeff G W AW h R c ((M + N) + 1) P =
          TransmutationCoeff G W AW h R c (M + N) P := by
      calc
        TransmutationCoeff G W AW h R c ((M + N) + 1) P
            = TransmutationCoeff G W AW h R c M P := by
              simpa [M, add_assoc, add_left_comm, add_comm] using
                TransmutationCoeff_stabilizes G W AW k A_als B_als r_als hr_als hk_bound
                  lam hlam_pos hlam_lt C hC h R hR c P (N + 1)
        _ = TransmutationCoeff G W AW h R c (M + N) P := by
              simpa [M] using
                (TransmutationCoeff_stabilizes G W AW k A_als B_als r_als hr_als hk_bound
                  lam hlam_pos hlam_lt C hC h R hR c P N).symm
    have htail_zero :
        ∑ Q ∈ (G.grid.partitions (M + N)).attach.filter (fun Q => P.1 ⊆ Q.1),
          (c (M + N) Q * ((R (M + N) Q).block j).coeff P) •
            ((R (M + N) Q).block j).atom P = 0 := by
      apply Finset.sum_eq_zero
      intro Q hQ
      have hcoeff_zero : ((R (M + N) Q).block j).coeff P = 0 :=
        ((hR (M + N) Q).2.1 j P).2 hk_large
      simp [hcoeff_zero]
    have hnum_step :
        (∑ iQ ∈ ((Finset.range ((M + N) + 1)).sigma
            (fun i => (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1))),
          (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
            ((R iQ.1 iQ.2).block j).atom P) =
        (∑ iQ ∈ ((Finset.range (M + N)).sigma
            (fun i => (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1))),
          (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
            ((R iQ.1 iQ.2).block j).atom P) := by
      rw [Finset.sum_sigma, Finset.sum_sigma, Finset.sum_range_succ, htail_zero, add_zero]
    calc
      TransmutationAtomLocal G W AW h R c (transmutationStabilizationIndex A_als r_als j + (N + 1)) P
          = TransmutationAtomLocal G W AW h R c (M + N) P := by
            have hMN : transmutationStabilizationIndex A_als r_als j + (N + 1) = (M + N) + 1 := by
              simp [M, add_assoc, add_left_comm, add_comm]
            dsimp [TransmutationAtomLocal]
            rw [hMN, hcoeff_step, hnum_step]
          _ = TransmutationAtomLocal G W AW h R c (transmutationStabilizationIndex A_als r_als j) P := by
            simpa [M] using ih

/-- The stable local atom attached to a target cell. This is the formal
`d_{P,∞}` used in Claim III before applying `atomLp`. -/
noncomputable def TransmutationAtomLocalLimit
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (A_als r_als : ℝ)
    {j : ℕ} (P : LevelCell W j) :
    (AW.localSpace (levelCellToWeakGridCell W j P)).carrier :=
  TransmutationAtomLocal G W AW h R c (transmutationStabilizationIndex A_als r_als j) P

/-- Beyond the stabilization threshold, the local atoms equal their stable
limit value `d_{P,∞}`. -/
private lemma TransmutationAtomLocal_eq_limit_of_ge
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    {j : ℕ} (P : LevelCell W j)
    {N : ℕ}
    (hN : transmutationStabilizationIndex A_als r_als j ≤ N) :
    TransmutationAtomLocal G W AW h R c N P =
      TransmutationAtomLocalLimit G W AW h R c A_als r_als P := by
  let M := transmutationStabilizationIndex A_als r_als j
  have hNM : N = M + (N - M) := by
    dsimp [M]
    omega
  rw [hNM, TransmutationAtomLocalLimit]
  exact TransmutationAtomLocal_stabilizes G W AW k A_als B_als r_als hr_als hk_bound
    lam hlam_pos hlam_lt C hC h R hR c P (N - M)

/-- The stable `L^p` atom attached to a target cell. This is the paper's
`d_{P,∞}` as an actual element of `L^p`. -/
noncomputable def TransmutationAtomLimit
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (A_als r_als : ℝ)
    {j : ℕ} (P : LevelCell W j) : Lp ℂ p W.measure :=
  atomLp AW (levelCellToWeakGridCell W j P)
    (TransmutationAtomLocalLimit G W AW h R c A_als r_als P)

/-- The `L^p` atoms in the transmutation representation converge because they
are eventually constant cellwise. -/
private lemma TransmutationAtom_tendsto_limit
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    {j : ℕ} (P : LevelCell W j) :
    Tendsto
      (fun N => atomLp AW (levelCellToWeakGridCell W j P)
        (TransmutationAtomLocal G W AW h R c N P))
      atTop
      (𝓝 (TransmutationAtomLimit G W AW h R c A_als r_als P)) := by
  let M := transmutationStabilizationIndex A_als r_als j
  have heq :
      (fun N => atomLp AW (levelCellToWeakGridCell W j P)
        (TransmutationAtomLocal G W AW h R c N P)) =ᶠ[atTop]
        (fun _ => TransmutationAtomLimit G W AW h R c A_als r_als P) := by
    refine eventually_atTop.2 ⟨M, ?_⟩
    intro N hN
    simp [TransmutationAtomLimit,
      TransmutationAtomLocal_eq_limit_of_ge G W AW k A_als B_als r_als hr_als hk_bound
        lam hlam_pos hlam_lt C hC h R hR c P hN]
  exact tendsto_const_nhds.congr' heq.symm

/-- `TransmutationAtomLocal G W AW h R c N P` is an atom of `AW` on cell `P`.
    **Proof**: when `m = 0` the element is `0`, which is an atom
    (`atom_zero_mem`).  When `m ≠ 0` the element equals
    `∑ (c_Q · s_{P,Q} / m) · b_{P,Q}`,
    a weighted sum of AW-atoms with coefficient-norms summing to `1`;
    convexity of `AW.atoms P` (together with phase-invariance used inside
    `atom_finsum_mem`) shows the sum is still an atom. -/
private theorem TransmutationAtomLocal_isAtom
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) {j : ℕ} (P : LevelCell W j) :
    AW.IsAtom (levelCellToWeakGridCell W j P)
      (TransmutationAtomLocal G W AW h R c N P) := by
  set Pg := levelCellToWeakGridCell W j P
  set m  := TransmutationCoeff G W AW h R c N P
  -- Local alias for the flat index set (same expression as in TransmutationAtomLocal)
  let FS : Finset (Σ i : ℕ, LevelCell G i) :=
    (Finset.range N).sigma
      (fun i => (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1))
  show TransmutationAtomLocal G W AW h R c N P ∈ AW.atoms Pg
  -- Rewrite using the explicit form of TransmutationAtomLocal (holds by rfl)
  have hdef : TransmutationAtomLocal G W AW h R c N P =
      if m = 0 then 0
      else (m : ℂ)⁻¹ • ∑ iQ ∈ FS,
        (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
          ((R iQ.1 iQ.2).block j).atom P := rfl
  rw [hdef]
  by_cases hm : m = 0
  · -- m = 0: the atom is 0, which is in A.atoms Pg
    rw [if_pos hm]; exact atom_zero_mem AW Pg
  · -- m ≠ 0
    rw [if_neg hm]
    have hm_nonneg : 0 ≤ m :=
      Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun _Q _ => norm_nonneg _
    have hm_pos : 0 < m := lt_of_le_of_ne hm_nonneg (Ne.symm hm)
    -- Distribute m⁻¹ into the sum, then apply atom_finsum_mem
    rw [show (m : ℂ)⁻¹ • ∑ iQ ∈ FS,
          (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
            ((R iQ.1 iQ.2).block j).atom P =
        ∑ iQ ∈ FS,
          ((m : ℂ)⁻¹ * (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P)) •
            ((R iQ.1 iQ.2).block j).atom P from by
      rw [Finset.smul_sum]; congr 1; ext iQ; rw [smul_smul]]
    let lamFS : (Σ i : ℕ, LevelCell G i) → ℂ :=
      fun iQ => (m : ℂ)⁻¹ * (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P)
    let aFS : (Σ i : ℕ, LevelCell G i) → (AW.localSpace Pg).carrier :=
      fun iQ => ((R iQ.1 iQ.2).block j).atom P
    have haFS : ∀ iQ ∈ FS, aFS iQ ∈ AW.atoms Pg := by
      intro iQ hiQ
      rcases iQ with ⟨i, Q⟩
      exact (R i Q).block j |>.atom_mem P
    -- Flatten the sigma sum back to the nested form to recover `m`.
    have h_flat : ∑ iQ ∈ FS, ‖c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P‖ = m := by
      show ∑ iQ ∈ (Finset.range N).sigma
          (fun i => (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1)),
          ‖c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P‖ = m
      rw [Finset.sum_sigma]
      rfl
    have hm_norm : ‖(m : ℂ)‖ = m :=
      (RCLike.norm_ofReal (K := ℂ) m).trans (abs_of_pos hm_pos)
    have hlamFS : ∑ iQ ∈ FS, ‖lamFS iQ‖ ≤ 1 := by
      have hbound : ∑ iQ ∈ FS, ‖lamFS iQ‖ = 1 := by
        have h_expand : ∀ iQ ∈ FS,
            ‖lamFS iQ‖ = m⁻¹ * ‖c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P‖ :=
          fun iQ _ => by
            dsimp [lamFS]
            rw [norm_mul, norm_inv, hm_norm]
        rw [Finset.sum_congr rfl h_expand, ← Finset.mul_sum, h_flat,
          inv_mul_cancel₀ hm_pos.ne']
      exact hbound.le
    have hrw : ∀ iQ ∈ FS, lamFS iQ • aFS iQ =
        (‖lamFS iQ‖ : ℝ) • phaseAtom AW Pg (lamFS iQ) (aFS iQ) := by
      intro iQ hiQ
      exact (norm_smul_phaseAtom AW Pg (lamFS iQ) (aFS iQ)).symm
    rw [Finset.sum_congr rfl hrw]
    set r : ℝ := ∑ iQ ∈ FS, ‖lamFS iQ‖
    by_cases hr : r = 0
    · have hall : ∀ iQ ∈ FS, ‖lamFS iQ‖ = 0 := fun iQ hiQ =>
        le_antisymm (hr ▸ Finset.single_le_sum (fun jQ _ => norm_nonneg _) hiQ) (norm_nonneg _)
      have h0 : ∑ iQ ∈ FS, (‖lamFS iQ‖ : ℝ) • phaseAtom AW Pg (lamFS iQ) (aFS iQ) = 0 :=
        Finset.sum_eq_zero (fun iQ hiQ => by simp [hall iQ hiQ])
      rw [h0]
      exact atom_zero_mem AW Pg
    · have hr_pos : 0 < r :=
        lt_of_le_of_ne (Finset.sum_nonneg fun iQ _ => norm_nonneg _) (Ne.symm hr)
      have h_conv :
          ∑ iQ ∈ FS, (‖lamFS iQ‖ / r) • phaseAtom AW Pg (lamFS iQ) (aFS iQ) ∈ AW.atoms Pg := by
        exact (AW.atoms_convex Pg).sum_mem
          (fun iQ _ => div_nonneg (norm_nonneg _) hr_pos.le)
          (by rw [← Finset.sum_div]; exact div_self hr_pos.ne')
          (fun iQ hiQ => phaseAtom_mem AW Pg (lamFS iQ) (haFS iQ hiQ))
      have h_factor :
          ∑ iQ ∈ FS, (‖lamFS iQ‖ : ℝ) • phaseAtom AW Pg (lamFS iQ) (aFS iQ) =
            (r : ℝ) • ∑ iQ ∈ FS, (‖lamFS iQ‖ / r) • phaseAtom AW Pg (lamFS iQ) (aFS iQ) := by
        conv_rhs => rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun iQ _ => ?_
        rw [smul_smul, mul_div_cancel₀ _ (ne_of_gt hr_pos)]
      rw [h_factor, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      exact atom_smul_mem_of_norm_le_one AW Pg
        (by rw [RCLike.norm_ofReal, abs_of_pos hr_pos]; exact hlamFS) h_conv

/-- **Claim I**: `∑_j ∑_{P∈W^j} m_{P,N} · d_{P,N} = ∑_{i<N} ∑_{Q∈G^i} c_Q · h_Q` in Lp.
    Proof: exchange summation order using `h_Q = ∑_j ∑_{P⊆Q} s_{P,Q}·b_{P,Q}` (from `hR`)
    and the identity `m_{P,N} · d_{P,N} = ∑_{i<N} ∑_{Q∈G^i,P⊆Q} c_Q·s_{P,Q}·b_{P,Q}`. -/
private theorem ClaimI
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (hk : AlmostLinearSequence k)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k hk lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := q) G c)
    (N : ℕ) :
    ∑' j : ℕ, ∑ P ∈ (W.grid.partitions j).attach,
        (↑(TransmutationCoeff G W AW h R c N P) : ℂ) •
          TransmutationAtom G W AW h R c N P =
    PartialSumLevels G W h c N := by
  -- Step 1: m_{P,N} · d_{P,N} = ∑_{i<N} ∑_{Q∈G^i} c_Q · term_{j,P,Q}
  have mD_eq : ∀ (j : ℕ) (P : LevelCell W j),
      (↑(TransmutationCoeff G W AW h R c N P) : ℂ) • TransmutationAtom G W AW h R c N P =
      ∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach,
        c i Q • ((R i Q).block j).term AW P := by
    intro j P
    -- P ⊄ Q → coeff = 0 → term = 0  (localization from hR)
    have hterm : ∀ i ∈ Finset.range N, ∀ Q ∈ (G.grid.partitions i).attach,
        ¬ P.1 ⊆ Q.1 → c i Q • ((R i Q).block j).term AW P = 0 := by
      intro i _ Q _ hPQ
      simp [LevelBlock.term, ((hR i Q).2.1 j P).1 hPQ]
    -- Removing the filter doesn't change the term sum (non-subset terms vanish)
    have hfilt_term : ∀ i ∈ Finset.range N,
        ∑ Q ∈ (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1),
            c i Q • ((R i Q).block j).term AW P =
        ∑ Q ∈ (G.grid.partitions i).attach,
            c i Q • ((R i Q).block j).term AW P := by
      intro i hi
      apply Finset.sum_filter_of_ne
      intro Q hQ hne
      by_contra h
      exact hne (hterm i hi Q hQ h)
    -- Removing the filter doesn't change the norm sum (non-subset coeff = 0)
    have hfilt_norm : ∀ i ∈ Finset.range N,
        ∑ Q ∈ (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1),
            ‖c i Q * ((R i Q).block j).coeff P‖ =
        ∑ Q ∈ (G.grid.partitions i).attach,
            ‖c i Q * ((R i Q).block j).coeff P‖ := by
      intro i hi
      apply Finset.sum_filter_of_ne
      intro Q hQ hne
      by_contra h
      simp [((hR i Q).2.1 j P).1 h] at hne
    -- Rewrite TransmutationCoeff and TransmutationAtom
    simp only [TransmutationAtom, TransmutationCoeff]
    set m := ∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach,
        ‖c i Q * ((R i Q).block j).coeff P‖
    rw [show (∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach.filter
            (fun Q => P.1 ⊆ Q.1), ‖c i Q * ((R i Q).block j).coeff P‖) = m from
      Finset.sum_congr rfl hfilt_norm]
    by_cases hm : m = 0
    · -- m = 0: all ‖c_Q s_{P,Q}‖ = 0, so all terms are 0
      simp only [hm, ↓reduceIte, smul_zero]
      symm
      apply Finset.sum_eq_zero; intro i hi
      apply Finset.sum_eq_zero; intro Q hQ
      have hle : ‖c i Q * ((R i Q).block j).coeff P‖ ≤ m :=
        calc ‖c i Q * ((R i Q).block j).coeff P‖
            ≤ ∑ Q' ∈ (G.grid.partitions i).attach,
                ‖c i Q' * ((R i Q').block j).coeff P‖ :=
              Finset.single_le_sum
                (f := fun Q' => ‖c i Q' * ((R i Q').block j).coeff P‖)
                (fun Q' _ => norm_nonneg _) hQ
          _ ≤ m :=
              Finset.single_le_sum
                (f := fun i' => ∑ Q' ∈ (G.grid.partitions i').attach,
                  ‖c i' Q' * ((R i' Q').block j).coeff P‖)
                (fun i' _ => Finset.sum_nonneg (fun Q' _ => norm_nonneg _)) hi
      have hzero : c i Q * ((R i Q).block j).coeff P = 0 :=
        norm_eq_zero.mp (le_antisymm (hm ▸ hle) (norm_nonneg _))
      simp only [LevelBlock.term, smul_smul, hzero, zero_smul]
    · -- m ≠ 0: (↑m) · (↑m)⁻¹ · num = num
      simp only [hm, ↓reduceIte]
      have hm_C : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      rw [smul_smul, mul_inv_cancel₀ hm_C, one_smul]
      exact Finset.sum_congr rfl hfilt_term
  -- Step 2: rewrite LHS using mD_eq, then exchange sums
  simp only [PartialSumLevels]
  -- Rewrite each summand via mD_eq
  have lhs_rw : ∀ j : ℕ,
      ∑ P ∈ (W.grid.partitions j).attach,
          (↑(TransmutationCoeff G W AW h R c N P) : ℂ) • TransmutationAtom G W AW h R c N P =
      ∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach,
          c i Q • ((R i Q).block j).toLp AW := by
    intro j
    simp_rw [Finset.sum_congr rfl (fun P _ => mD_eq j P)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro Q _
    rw [← Finset.smul_sum]
    simp only [LevelBlock.toLp]
  simp_rw [lhs_rw]
  -- Step 3: ∑' j, ∑_{i,Q} c_Q · (block j).toLp = ∑_{i,Q} c_Q · h i Q  -- using HasSum for each (i,Q) and linearity over the finite sum
  have hasSum_iQ : HasSum
      (fun j => ∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach,
          c i Q • ((R i Q).block j).toLp AW)
      (∑ i ∈ Finset.range N, ∑ Q ∈ (G.grid.partitions i).attach,
          c i Q • h i Q) := by
    apply hasSum_sum; intro i _
    apply hasSum_sum; intro Q _
    exact ((R i Q).hasSum.const_smul (c i Q))
  rw [hasSum_iQ.tsum_eq]

/-- Endpoint `q = ∞` version of **Claim I**.  This is the same bookkeeping
identity as `ClaimI`, with all coefficient-cost hypotheses specialized to the
supremum endpoint. -/
private theorem ClaimI_top
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (hk : AlmostLinearSequence k)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := ∞) G W AW k hk
      lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := ∞) G c)
    (N : ℕ) :
    ∑' j : ℕ, ∑ P ∈ (W.grid.partitions j).attach,
        (↑(TransmutationCoeff G W AW h R c N P) : ℂ) •
          TransmutationAtom G W AW h R c N P =
    PartialSumLevels G W h c N := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  exact ClaimI (p := p) (u := u) (q := ∞) G W AW k hk
    lam hlam_pos hlam_lt C hC h R hR c hc N


/-- The level-`k` block of the transmutation atomic decomposition with respect to
    the target atom family `AW` on `W`.  For each cell `P ∈ W^k`:
    - coefficient: `m_{P,N} := TransmutationCoeff G W AW h R c N P ∈ ℝ≥0` (cast to ℂ),
    - atom: `d_{P,N} := TransmutationAtomLocal G W AW h R c N P`,
    which is a genuine `AW`-atom by `TransmutationAtomLocal_isAtom`. -/
noncomputable def TransmutationBlock
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) (k : ℕ) : LevelBlock AW k where
  coeff P := (TransmutationCoeff G W AW h R c N P : ℂ)
  atom P  := TransmutationAtomLocal G W AW h R c N P
  atom_mem P := TransmutationAtomLocal_isAtom G W AW h R c N P

/-- The local normalized transmutation block has the same `L^p` value as the
external formula using `TransmutationAtom`.

This is the bookkeeping identity
`∑_P m_{P,N} d_{P,N}` at a fixed level. -/
private lemma transmutationBlock_toLp_eq
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N j : ℕ) :
    (TransmutationBlock G W AW h R c N j).toLp AW =
      ∑ P ∈ (W.grid.partitions j).attach,
        (TransmutationCoeff G W AW h R c N P : ℂ) •
          TransmutationAtom G W AW h R c N P := by
  unfold LevelBlock.toLp
  apply Finset.sum_congr rfl
  intro P hP
  set m := TransmutationCoeff G W AW h R c N P with hm_def
  set Pg := levelCellToWeakGridCell W j P
  set FS : Finset (Σ i : ℕ, LevelCell G i) :=
    (Finset.range N).sigma
      (fun i => (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1))
  subst Pg
  have hnum_sigma :
      (∑ iQ ∈ FS, c iQ.1 iQ.2 • ((R iQ.1 iQ.2).block j).term AW P) =
        ∑ i ∈ Finset.range N,
          ∑ Q ∈ (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1),
            c i Q • ((R i Q).block j).term AW P := by
    rw [Finset.sum_sigma]
  by_cases hm : m = 0
  · have hcoeffR : TransmutationCoeff G W AW h R c N P = 0 := by
      rw [← hm_def, hm]
    simp [LevelBlock.term, TransmutationBlock, hcoeffR]
    rw [hm]
    exact (zero_smul ℂ (TransmutationAtom G W AW h R c N P)).symm
  · have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    simp only [LevelBlock.term, TransmutationBlock]
    rw [show TransmutationCoeff G W AW h R c N P = m by rw [hm_def]]
    simp only [TransmutationAtom, TransmutationAtomLocal, ← hm_def, hm, ↓reduceIte]
    rw [smul_smul, mul_inv_cancel₀ hmC, one_smul]
    rw [← hnum_sigma]
    apply Lp.ext
    have hsum_ae :
        ⇑(∑ iQ ∈ FS, c iQ.1 iQ.2 • ((R iQ.1 iQ.2).block j).term AW P)
          =ᵐ[W.measure]
        fun x => ∑ iQ ∈ FS,
          (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) *
            AW.toFunction (levelCellToWeakGridCell W j P)
              (((R iQ.1 iQ.2).block j).atom P) x := by
      induction FS using Finset.induction_on with
      | empty =>
          exact (Lp.coeFn_zero ℂ p W.measure).trans
            (Filter.Eventually.of_forall (fun x => by simp))
      | insert iQ S hiQ ih =>
          simp only [Finset.sum_insert hiQ]
          refine (Lp.coeFn_add _ _).trans ?_
          have hhead :
              ⇑(c iQ.1 iQ.2 • ((R iQ.1 iQ.2).block j).term AW P)
                =ᵐ[W.measure]
              fun x => (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) *
                AW.toFunction (levelCellToWeakGridCell W j P)
                  (((R iQ.1 iQ.2).block j).atom P) x :=
            ((Lp.coeFn_smul _ _).trans
              ((LevelBlock.coeFn_term AW ((R iQ.1 iQ.2).block j) P).fun_const_smul _)).trans
              (Filter.Eventually.of_forall (fun x => by
                simp only [smul_eq_mul]
                ring))
          exact (hhead.add ih).trans
            (Filter.Eventually.of_forall (fun x => by
              simp only [Pi.add_apply]))
    filter_upwards
      [Lp.coeFn_smul (m : ℂ)
        (MemLp.toLp
          (AW.toFunction (levelCellToWeakGridCell W j P)
            ((m : ℂ)⁻¹ •
              ∑ iQ ∈ FS,
                (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
                  ((R iQ.1 iQ.2).block j).atom P))
          (AW.local_memLp_p (levelCellToWeakGridCell W j P) _)),
       MemLp.coeFn_toLp
          (AW.local_memLp_p (levelCellToWeakGridCell W j P)
            ((m : ℂ)⁻¹ •
              ∑ iQ ∈ FS,
                (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) •
                  ((R iQ.1 iQ.2).block j).atom P)),
       hsum_ae] with x hsmul htoLp hsum
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul ⊢
    rw [hsmul, htoLp, hsum]
    simp only [AtomFamily.toFunction, map_smul, map_sum, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hmC, one_mul]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- If a fixed target cell `P` is contained in cells `Q` of one source level,
then those `Q`s form an overlap family. Hence their number is bounded by
`G.grid.Cmult1`.

This is the geometric multiplicity used in Claim II at the step
`(∑_{Q:P⊆Q} a_Q)^p ≤ Cmult1^p ∑_{Q:P⊆Q} a_Q^p`. -/
private lemma containing_cells_card_le_Cmult1
    (G W : WeakGridSpace (α := α)) (i j : ℕ) (P : LevelCell W j) :
    ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1).card
      ≤ G.grid.Cmult1 := by
  classical
  let S := (G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1
  by_cases hS : S.Nonempty
  · rcases hS with ⟨Q₀, hQ₀S⟩
    have hPne : P.1.Nonempty := by
      by_contra hne
      have hEmpty : P.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hpos : 0 < W.measure P.1 := by
        simpa [WeakGridSpace.measure] using W.grid.positive_measure j P.1 P.2
      rw [hEmpty, measure_empty] at hpos
      exact (lt_irrefl (0 : ℝ≥0∞)) hpos
    have hQ₀mem : Q₀.1 ∈ G.grid.partitions i := Q₀.2
    have hQ₀contains : P.1 ⊆ Q₀.1 := by
      simpa [S] using (Finset.mem_filter.mp hQ₀S).2
    have hmap :
        Set.MapsTo (fun Q : LevelCell G i => Q.1) (S : Set (LevelCell G i))
          (overlapFinset (G.grid.partitions i) Q₀.1 : Set (Set α)) := by
      intro Q hQS
      have hQcontains : P.1 ⊆ Q.1 := by
        simpa [S] using (Finset.mem_filter.mp hQS).2
      rcases hPne with ⟨x, hxP⟩
      simp [overlapFinset, Q.2]
      exact ⟨x, hQcontains hxP, hQ₀contains hxP⟩
    have hinj :
        Set.InjOn (fun Q : LevelCell G i => Q.1) (S : Set (LevelCell G i)) := by
      intro Q hQS R hRS hQR
      cases Q
      cases R
      simp at hQR
      simp [hQR]
    simpa [S] using
      (Finset.card_le_card_of_injOn (fun Q : LevelCell G i => Q.1) hmap hinj).trans
        (G.grid.overlap_card_le i Q₀.1 hQ₀mem)
  · have hEmpty : S = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hS
    have hcard :
        ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1).card = 0 := by
      simpa [S] using congrArg Finset.card hEmpty
    omega

/-- Power-sum estimate for the cells of one source level that contain a fixed
target cell.

This is the formal version of the Claim II step
`(∑_{Q:P⊆Q} a_Q)^p ≤ Cmult1^p ∑_{Q:P⊆Q} a_Q^p`. -/
private lemma containing_cells_sum_rpow_le_Cmult1
    (G W : WeakGridSpace (α := α)) (i j : ℕ) (P : LevelCell W j)
    (a : LevelCell G i → ℝ)
    (hp_ne_top : p ≠ ∞)
    (ha_nonneg : ∀ Q ∈
      ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
        0 ≤ a Q) :
    (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
        a Q) ^ p.toReal ≤
      (G.grid.Cmult1 : ℝ) ^ p.toReal *
        ∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          a Q ^ p.toReal := by
  classical
  let S := (G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1
  have hp_one : (1 : ℝ) ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp_ne_top (Fact.out : (1 : ℝ≥0∞) ≤ p)
    simpa using h
  have hp_nonneg : 0 ≤ p.toReal := le_trans (zero_le_one : (0 : ℝ) ≤ 1) hp_one
  have hpow_sum :
      (∑ Q ∈ S, a Q) ^ p.toReal ≤
        (S.card : ℝ) ^ (p.toReal - 1) *
          ∑ Q ∈ S, a Q ^ p.toReal :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S hp_one
      (by simpa [S] using ha_nonneg)
  have hcardC_nat : S.card ≤ G.grid.Cmult1 := by
    simpa [S] using containing_cells_card_le_Cmult1 G W i j P
  have hcardC : (S.card : ℝ) ≤ (G.grid.Cmult1 : ℝ) := by exact_mod_cast hcardC_nat
  have hCnonneg : 0 ≤ (G.grid.Cmult1 : ℝ) := by exact_mod_cast Nat.zero_le G.grid.Cmult1
  by_cases hSempty : S.card = 0
  · have hS : S = ∅ := Finset.card_eq_zero.mp hSempty
    change (∑ Q ∈ S, a Q) ^ p.toReal ≤
      (G.grid.Cmult1 : ℝ) ^ p.toReal * ∑ Q ∈ S, a Q ^ p.toReal
    rw [hS]
    simp [Real.zero_rpow (lt_of_lt_of_le zero_lt_one hp_one).ne']
  · have hSpos_nat : 1 ≤ S.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hSempty)
    have hSpos : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hSpos_nat
    have hcard_pow_le_C :
        (S.card : ℝ) ^ (p.toReal - 1) ≤ (G.grid.Cmult1 : ℝ) ^ p.toReal := by
      calc
        (S.card : ℝ) ^ (p.toReal - 1)
            ≤ (S.card : ℝ) ^ p.toReal :=
              Real.rpow_le_rpow_of_exponent_le hSpos (by linarith)
        _ ≤ (G.grid.Cmult1 : ℝ) ^ p.toReal :=
              Real.rpow_le_rpow (by positivity) hcardC hp_nonneg
    exact hpow_sum.trans
      (mul_le_mul_of_nonneg_right hcard_pow_le_C
        (Finset.sum_nonneg fun Q hQ => Real.rpow_nonneg (ha_nonneg Q (by simpa [S] using hQ)) _))

/-- Fixed-source-level estimate after applying the multiplicity bound to each
target cell and exchanging the finite sums. -/
private  lemma transmutation_fixed_i_power_bound
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (i j : ℕ) (hp_ne_top : p ≠ ∞) :
    (∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal) ≤
      (G.grid.Cmult1 : ℝ) ^ p.toReal *
        ∑ Q : LevelCell G i,
          ‖c i Q‖ ^ p.toReal * (R i Q).levelCoeffPower j := by
  classical
  have hCnonneg : 0 ≤ (G.grid.Cmult1 : ℝ) := by exact_mod_cast Nat.zero_le G.grid.Cmult1
  have hpoint : ∀ P : LevelCell W j,
      (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
        ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal ≤
      (G.grid.Cmult1 : ℝ) ^ p.toReal *
        ∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖ ^ p.toReal := by
    intro P
    exact containing_cells_sum_rpow_le_Cmult1 (p := p) G W i j P
      (fun Q => ‖c i Q * ((R i Q).block j).coeff P‖) hp_ne_top
      (fun Q hQ => norm_nonneg _)
  calc
    (∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal)
        ≤ ∑ P : LevelCell W j,
            (G.grid.Cmult1 : ℝ) ^ p.toReal *
              ∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
                ‖c i Q * ((R i Q).block j).coeff P‖ ^ p.toReal := by
          exact Finset.sum_le_sum fun P _ => hpoint P
    _ = (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ∑ P : LevelCell W j,
            ∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
              ‖c i Q * ((R i Q).block j).coeff P‖ ^ p.toReal := by
          rw [Finset.mul_sum]
    _ = (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ∑ Q : LevelCell G i,
            ∑ P : LevelCell W j,
              if P.1 ⊆ Q.1 then
                ‖c i Q * ((R i Q).block j).coeff P‖ ^ p.toReal else 0 := by
          congr 1
          rw [Finset.sum_comm]
          simp [Finset.sum_filter]
    _ ≤ (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ∑ Q : LevelCell G i,
            ∑ P : LevelCell W j,
              ‖c i Q * ((R i Q).block j).coeff P‖ ^ p.toReal := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun Q _ =>
              Finset.sum_le_sum fun P _ => by
              by_cases hPQ : P.1 ⊆ Q.1
              · simp [hPQ]
              · simp [hPQ, Real.rpow_nonneg
                  (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _])
            (Real.rpow_nonneg hCnonneg _)
    _ = (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ∑ Q : LevelCell G i,
            ‖c i Q‖ ^ p.toReal * (R i Q).levelCoeffPower j := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro Q hQ
          rw [LpGridRepresentation.levelCoeffPower, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro P hP
          rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

/-- Root form of the single-source-level estimate used in Claim II.

This lemma combines the geometric overlap bound from
`transmutation_fixed_i_power_bound` with the decay information supplied by the
representation hypothesis `hR`.  For a fixed source level `i` and output level
`j ≥ k i`, it shows that the contribution of level `i` to the target level `j`
is controlled by three factors:
1. the overlap multiplicity `G.grid.Cmult1`;
2. the decay term `lam^((j-k i)/p)` coming from the representation;
3. the source coefficient size at level `i`, measured by `CoeffPLevel`.

This is the local estimate that later gets summed in `i` by Minkowski and then
reorganized into the convolution bound. -/
private lemma transmutation_fixed_i_root_bound
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (hk : AlmostLinearSequence k)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k hk lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (i j : ℕ) (hp_ne_top : p ≠ ∞) (hki : k i ≤ j) :
    (∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal) ^ (1 / p.toReal) ≤
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) := by
  classical
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos
      (fun h0 => absurd (h0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)) (by norm_num))
      hp_ne_top
  have hp_inv_nonneg : 0 ≤ 1 / p.toReal := by positivity
  have hCmult_nonneg : 0 ≤ (G.grid.Cmult1 : ℝ) := by exact_mod_cast Nat.zero_le G.grid.Cmult1
  have hlam_nonneg : 0 ≤ lam ^ ((↑(j - k i) : ℝ) / p.toReal) :=
    Real.rpow_nonneg hlam_pos.le _
  have hcoeff_nonneg : 0 ≤ CoeffPLevel (p := p) G c i :=
    Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
  have hfixed := transmutation_fixed_i_power_bound
    (p := p) G W AW h R c i j hp_ne_top
  have hdecay_sum :
      ∑ Q : LevelCell G i,
          ‖c i Q‖ ^ p.toReal * (R i Q).levelCoeffPower j
        ≤
      (C * lam ^ (j - k i)) * CoeffPLevel (p := p) G c i := by
    calc
      ∑ Q : LevelCell G i,
          ‖c i Q‖ ^ p.toReal * (R i Q).levelCoeffPower j
          ≤ ∑ Q : LevelCell G i,
              ‖c i Q‖ ^ p.toReal * (C * lam ^ (j - k i)) := by
            exact Finset.sum_le_sum fun Q _ =>
              mul_le_mul_of_nonneg_left ((hR i Q).2.2 j hki)
                (Real.rpow_nonneg (norm_nonneg _) _)
      _ = (C * lam ^ (j - k i)) * CoeffPLevel (p := p) G c i := by
            simp only [CoeffPLevel]
            rw [← Finset.sum_mul]
            ring_nf
  have hpower :
      ∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal
        ≤
      ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal)) ^ p.toReal := by
    have h1 :
        ∑ P : LevelCell W j,
          (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
            ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal
          ≤
        (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ((C * lam ^ (j - k i)) * CoeffPLevel (p := p) G c i) := by
      exact hfixed.trans
        (mul_le_mul_of_nonneg_left hdecay_sum
          (Real.rpow_nonneg hCmult_nonneg _))
    have hfactor_nonneg : 0 ≤ C * lam ^ (j - k i) :=
      mul_nonneg hC (pow_nonneg hlam_pos.le _)
    have htarget_eq :
        ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
            (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal)) ^ p.toReal =
        (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ((C * lam ^ (j - k i)) * CoeffPLevel (p := p) G c i) := by
      calc
        ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
            (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal)) ^ p.toReal
            =
          (G.grid.Cmult1 : ℝ) ^ p.toReal *
            (C ^ (1 / p.toReal)) ^ p.toReal *
            (lam ^ ((↑(j - k i) : ℝ) / p.toReal)) ^ p.toReal *
            ((CoeffPLevel (p := p) G c i) ^ (1 / p.toReal)) ^ p.toReal := by
              rw [Real.mul_rpow
                    (mul_nonneg (mul_nonneg hCmult_nonneg (Real.rpow_nonneg hC _))
                      hlam_nonneg)
                    (Real.rpow_nonneg hcoeff_nonneg _),
                  Real.mul_rpow
                    (mul_nonneg hCmult_nonneg (Real.rpow_nonneg hC _))
                    hlam_nonneg,
                  Real.mul_rpow hCmult_nonneg (Real.rpow_nonneg hC _)]
        _ = (G.grid.Cmult1 : ℝ) ^ p.toReal *
            C *
            lam ^ (j - k i) *
            CoeffPLevel (p := p) G c i := by
              rw [← Real.rpow_mul hC, ← Real.rpow_mul hlam_pos.le,
                ← Real.rpow_mul hcoeff_nonneg]
              field_simp [hp_pos.ne']
              simp
        _ = (G.grid.Cmult1 : ℝ) ^ p.toReal *
          ((C * lam ^ (j - k i)) * CoeffPLevel (p := p) G c i) := by ring
    simpa [← htarget_eq] using h1
  have hleft_nonneg :
      0 ≤ ∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal :=
    Finset.sum_nonneg fun P _ => Real.rpow_nonneg
      (Finset.sum_nonneg fun Q _ => norm_nonneg _) _
  have htarget_nonneg :
      0 ≤ (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hCmult_nonneg (Real.rpow_nonneg hC _))
        hlam_nonneg)
      (Real.rpow_nonneg hcoeff_nonneg _)
  have hroot := Real.rpow_le_rpow hleft_nonneg hpower hp_inv_nonneg
  calc
    (∑ P : LevelCell W j,
        (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
          ‖c i Q * ((R i Q).block j).coeff P‖) ^ p.toReal) ^ (1 / p.toReal)
        ≤
      (((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal)) ^ p.toReal) ^
        (1 / p.toReal) := hroot
    _ = (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) := by
          rw [← Real.rpow_mul htarget_nonneg]
          field_simp [hp_pos.ne']
          rw [Real.rpow_one]

/-- Finite Minkowski inequality for a nonnegative family.

The statement is the discrete finite version of the estimate
"the `ℓ^p` norm of a sum is bounded by the sum of the `ℓ^p` norms".
It is used repeatedly when the transmutation coefficients are written as finite
sums over source levels and one wants to separate the contribution of each
level before passing to infinite sums. -/
private lemma finset_Lp_sum_le_sum_Lp
    {ι κ : Type*} (S : Finset ι) (T : Finset κ) (a : ι → κ → ℝ)
    (hp_ne_top : p ≠ ∞)
    (ha_nonneg : ∀ i ∈ S, ∀ k ∈ T, 0 ≤ a i k) :
    (∑ k ∈ T, (∑ i ∈ S, a i k) ^ p.toReal) ^ (1 / p.toReal) ≤
      ∑ i ∈ S, (∑ k ∈ T, (a i k) ^ p.toReal) ^ (1 / p.toReal) := by
  classical
  have hp_one : (1 : ℝ) ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp_ne_top (Fact.out : (1 : ℝ≥0∞) ≤ p)
    simpa using h
  have hp_pos : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hp_one
  revert ha_nonneg
  refine Finset.induction_on S ?base ?step
  · intro ha_nonneg
    simp only [Finset.sum_empty]
    rw [Real.zero_rpow hp_pos.ne']
    simp only [Finset.sum_const_zero]
    rw [Real.zero_rpow (one_div_pos.mpr hp_pos).ne']
  · intro i S hi ih ha_nonneg
    have hi_nonneg : ∀ k ∈ T, 0 ≤ a i k := by
      intro k hk
      exact ha_nonneg i (Finset.mem_insert_self i S) k hk
    have hS_nonneg : ∀ i' ∈ S, ∀ k ∈ T, 0 ≤ a i' k := by
      intro i' hi' k hk
      exact ha_nonneg i' (Finset.mem_insert_of_mem hi') k hk
    have hsumS_nonneg : ∀ k ∈ T, 0 ≤ ∑ i' ∈ S, a i' k := by
      intro k hk
      exact Finset.sum_nonneg fun i' hi' => hS_nonneg i' hi' k hk
    calc
      (∑ k ∈ T, (∑ i' ∈ insert i S, a i' k) ^ p.toReal) ^ (1 / p.toReal)
          =
        (∑ k ∈ T, (a i k + ∑ i' ∈ S, a i' k) ^ p.toReal) ^ (1 / p.toReal) := by
          congr 2
          ext k
          rw [Finset.sum_insert hi]
      _ ≤
        (∑ k ∈ T, (a i k) ^ p.toReal) ^ (1 / p.toReal) +
          (∑ k ∈ T, (∑ i' ∈ S, a i' k) ^ p.toReal) ^ (1 / p.toReal) := by
          exact Real.Lp_add_le_of_nonneg
            (s := T) (p := p.toReal)
            (f := fun k => a i k)
            (g := fun k => ∑ i' ∈ S, a i' k)
            hp_one hi_nonneg hsumS_nonneg
      _ ≤
        (∑ k ∈ T, (a i k) ^ p.toReal) ^ (1 / p.toReal) +
          ∑ i' ∈ S, (∑ k ∈ T, (a i' k) ^ p.toReal) ^ (1 / p.toReal) := by
          exact add_le_add_right (ih hS_nonneg)
            ((∑ k ∈ T, (a i k) ^ p.toReal) ^ (1 / p.toReal))
      _ =
        ∑ i' ∈ insert i S, (∑ k ∈ T, (a i' k) ^ p.toReal) ^ (1 / p.toReal) := by
          rw [Finset.sum_insert hi]

/-- A positive-step arithmetic progression never repeats values. -/
lemma arithProg_injective {a b : ℕ} (ha : 0 < a) :
    Function.Injective (fun n : ℕ => b + a * n) := by
  intro n m hnm
  have hmul : a * n = a * m := by
    exact Nat.add_left_cancel hnm
  exact Nat.mul_left_cancel ha hmul

/-- Restricting a summable sequence to one arithmetic progression preserves
summability.

This is the basic reindexing fact needed when source levels are split into
residue classes modulo `alpha = ceil r`. -/
private lemma summable_arithProg_comp {f : ℕ → ℝ} (hf : Summable f) {a b : ℕ} (ha : 0 < a) :
    Summable (fun n => f (b + a * n)) := by
  exact hf.comp_injective (arithProg_injective ha)

/-- For a nonnegative summable sequence, the sum over one arithmetic progression
is bounded by the full sum.

This is the monotonicity input used after decomposing indices into residue
classes: each class captures only part of the original sequence, so its total
mass cannot exceed the whole mass. -/
private  lemma tsum_arithProg_le {f : ℕ → ℝ} (hf : Summable f) (hf_nonneg : ∀ n, 0 ≤ f n)
    {a b : ℕ} (ha : 0 < a) :
    (∑' n, f (b + a * n)) ≤ ∑' n, f n := by
  let phi : ℕ → ℕ := fun n => b + a * n
  have hphi_inj : Function.Injective phi := arithProg_injective ha
  let e : ℕ ≃ Set.range phi := Equiv.ofInjective phi hphi_inj
  have h_range : (∑' n, f (phi n)) = ∑' x : Set.range phi, f x.1 := by
    simpa [phi, e] using e.tsum_eq (fun x : Set.range phi => f x.1)
  have hind_summable : Summable (Set.indicator (Set.range phi) f) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hf
    · intro n
      by_cases hn : n ∈ Set.range phi
      · simp [Set.indicator, hn, hf_nonneg]
      · simp [Set.indicator, hn]
    · intro n
      by_cases hn : n ∈ Set.range phi
      · simp [Set.indicator, hn]
      · simp [Set.indicator, hn, hf_nonneg]
  calc
    (∑' n, f (b + a * n)) = ∑' x : Set.range phi, f x.1 := by simpa [phi] using h_range
    _ = ∑' n, Set.indicator (Set.range phi) f n := by
      simpa using (tsum_subtype (Set.range phi) f)
    _ ≤ ∑' n, f n := hind_summable.tsum_le_tsum (fun n => by
      by_cases hn : n ∈ Set.range phi
      · simp [Set.indicator, hn]
      · simp [Set.indicator, hn, hf_nonneg]) hf

/-- Injectively reindexing a nonnegative summable family can only decrease its
total sum.

This abstract form is used several times to compare a sum over a subset or over
a reindexed copy with the original ambient sum. -/
private lemma tsum_comp_le_tsum_of_injective
    {ι κ : Type*} [Encodable ι] [Encodable κ]
    {f : κ → ℝ} (hf : Summable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    {phi : ι → κ} (hphi : Function.Injective phi) :
    (∑' i, f (phi i)) ≤ ∑' x, f x := by
  let e : ι ≃ Set.range phi := Equiv.ofInjective phi hphi
  have h_range : (∑' i, f (phi i)) = ∑' x : Set.range phi, f x.1 := by
    simpa [e] using e.tsum_eq (fun x : Set.range phi => f x.1)
  have hind_summable : Summable (Set.indicator (Set.range phi) f) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hf
    · intro x
      by_cases hx : x ∈ Set.range phi
      · simp [Set.indicator, hx, hf_nonneg]
      · simp [Set.indicator, hx]
    · intro x
      by_cases hx : x ∈ Set.range phi
      · simp [Set.indicator, hx]
      · simp [Set.indicator, hx, hf_nonneg]
  calc
    (∑' i, f (phi i)) = ∑' x : Set.range phi, f x.1 := by simpa using h_range
    _ = ∑' x, Set.indicator (Set.range phi) f x := by
      simpa using (tsum_subtype (Set.range phi) f)
    _ ≤ ∑' x, f x := hind_summable.tsum_le_tsum (fun x => by
      by_cases hx : x ∈ Set.range phi
      · simp [Set.indicator, hx]
      · simp [Set.indicator, hx, hf_nonneg]) hf

/-- Uniform bound for the `ℓ^q` norm of a finite family.

If every term in a finite family is between `0` and `C`, then its `ℓ^q` norm is
at most `card^(1/q) * C`.  In this file the lemma is used to pay for the finite
number of residue classes appearing in the almost-linear decomposition, which is
why the factor `(Nat.ceil r)^(1/q)` appears in the final estimates. -/
private lemma finset_Lq_le_card_rpow_mul_bound {ι : Type*} (S : Finset ι) (a : ι → ℝ) (C : ℝ)
    (ha_nonneg : ∀ i ∈ S, 0 ≤ a i) (ha_le : ∀ i ∈ S, a i ≤ C)
    (hC_nonneg : 0 ≤ C) (hq_ne_top : q ≠ ∞) :
    (∑ i ∈ S, a i ^ q.toReal) ^ (1 / q.toReal) ≤ (S.card : ℝ) ^ (1 / q.toReal) * C := by
  have hq_pos : 0 < q.toReal :=
    ENNReal.toReal_pos
      (fun h0 => absurd (h0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ q)) (by norm_num))
      hq_ne_top
  have hsum_le : ∑ i ∈ S, a i ^ q.toReal ≤ ∑ i ∈ S, C ^ q.toReal := by
    exact Finset.sum_le_sum fun i hi =>
      Real.rpow_le_rpow (ha_nonneg i hi) (ha_le i hi) hq_pos.le
  have hpow_le :
      (∑ i ∈ S, a i ^ q.toReal) ^ (1 / q.toReal) ≤
        (∑ i ∈ S, C ^ q.toReal) ^ (1 / q.toReal) :=
    Real.rpow_le_rpow
      (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha_nonneg i hi) _)
      hsum_le
      (div_nonneg zero_le_one hq_pos.le)
  have hsumC : ∑ i ∈ S, C ^ q.toReal = (S.card : ℝ) * C ^ q.toReal := by
    rw [Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ i ∈ S, a i ^ q.toReal) ^ (1 / q.toReal)
        ≤ ((S.card : ℝ) * C ^ q.toReal) ^ (1 / q.toReal) := by simpa [hsumC] using hpow_le
    _ = (S.card : ℝ) ^ (1 / q.toReal) * C := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hC_nonneg _)]
      rw [← Real.rpow_mul hC_nonneg]
      field_simp [hq_pos.ne']
      rw [Real.rpow_one]

/-- The level-by-level transmutation estimate in Claim II.

For a fixed target level `j`, this lemma bounds the `p`-cost of the
transmutation coefficients at level `j` by a weighted sum over source levels.
It is the place where all local ingredients are assembled:
1. Minkowski separates the finite sum over source levels `i < N`;
2. the geometric overlap bound controls how many source cells may contain a
  given target cell;
3. localization forces only cells with `P ⊆ Q` to appear;
4. the representation hypothesis contributes the decay factor beginning at
  level `k i`.

The output is already in the form needed for the later convolution argument:
each source level contributes a term weighted by
`lam^((j-k i)/p) * CoeffPLevel(G,c,i)^(1/p)`. -/
private lemma transmutation_level_bound
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (hk : AlmostLinearSequence k)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k hk lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N j : ℕ) (hp_ne_top : p ≠ ∞) :
    (CoeffPLevel (p := p) W
        (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j) ^ (1 / p.toReal) ≤
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        (∑' i, if k i ≤ j then
          lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
            (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0) := by
  classical
  let S : Finset ℕ := Finset.range N
  let T : Finset (LevelCell W j) := Finset.univ
  let a : ℕ → LevelCell W j → ℝ := fun i P =>
    if k i ≤ j then
      ∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
        ‖c i Q * ((R i Q).block j).coeff P‖
    else 0
  have ha_nonneg : ∀ i ∈ S, ∀ P ∈ T, 0 ≤ a i P := by
    intro i hi P hP
    dsimp [a]
    split_ifs
    · exact Finset.sum_nonneg fun Q hQ => norm_nonneg _
    · exact le_rfl
  have hm_eq : ∀ P : LevelCell W j,
      TransmutationCoeff G W AW h R c N P = ∑ i ∈ S, a i P := by
    intro P
    dsimp [S, a, TransmutationCoeff]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hki : k i ≤ j
    · simp [hki]
    · have hjlt : j < k i := Nat.lt_of_not_ge hki
      have hinner_zero :
          (∑ Q ∈ ((G.grid.partitions i).attach.filter fun Q : LevelCell G i => P.1 ⊆ Q.1),
            ‖c i Q * ((R i Q).block j).coeff P‖) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro Q hQ
        have hcoeff_zero := ((hR i Q).2.1 j P).2 hjlt
        simp [hcoeff_zero]
      simpa [hki, norm_mul] using hinner_zero
  have hleft_eq :
      CoeffPLevel (p := p) W
          (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j =
        ∑ P : LevelCell W j, (∑ i ∈ S, a i P) ^ p.toReal := by
    unfold CoeffPLevel
    refine Finset.sum_congr rfl ?_
    intro P hP
    change ‖((TransmutationCoeff G W AW h R c N P : ℝ) : ℂ)‖ ^ p.toReal =
      (∑ i ∈ S, a i P) ^ p.toReal
    rw [hm_eq P]
    have hsum_nonneg : 0 ≤ ∑ i ∈ S, a i P :=
      Finset.sum_nonneg fun i hi => ha_nonneg i hi P (by simp [T])
    rw [Complex.norm_of_nonneg hsum_nonneg]
  have hMinkowski :
      (∑ P : LevelCell W j, (∑ i ∈ S, a i P) ^ p.toReal) ^ (1 / p.toReal) ≤
        ∑ i ∈ S, (∑ P : LevelCell W j, (a i P) ^ p.toReal) ^ (1 / p.toReal) := by
    simpa [T] using
      finset_Lp_sum_le_sum_Lp (p := p) S T a hp_ne_top ha_nonneg
  have hterm_bound : ∀ i ∈ S,
      (∑ P : LevelCell W j, (a i P) ^ p.toReal) ^ (1 / p.toReal) ≤
        (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          (if k i ≤ j then
            lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
              (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0) := by
    intro i hi
    by_cases hki : k i ≤ j
    · have hfixed := transmutation_fixed_i_root_bound
        (p := p) G W AW k hk lam hlam_pos hlam_lt C hC h R hR c i j hp_ne_top hki
      simpa [a, hki, mul_assoc] using hfixed
    · have hzero_sum :
          (∑ P : LevelCell W j, (a i P) ^ p.toReal) = 0 := by
        have hp_pos : 0 < p.toReal :=
          ENNReal.toReal_pos
            (fun h0 => absurd (h0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)) (by norm_num))
            hp_ne_top
        refine Finset.sum_eq_zero ?_
        intro P hP
        simp [a, hki, Real.zero_rpow hp_pos.ne']
      have hp_pos : 0 < p.toReal :=
        ENNReal.toReal_pos
          (fun h0 => absurd (h0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)) (by norm_num))
          hp_ne_top
      rw [hzero_sum, Real.zero_rpow (one_div_pos.mpr hp_pos).ne']
      simp [hki]
  have hfinite_le :
      ∑ i ∈ S, (∑ P : LevelCell W j, (a i P) ^ p.toReal) ^ (1 / p.toReal) ≤
        ∑ i ∈ S,
          (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
            (if k i ≤ j then
              lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
                (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0) :=
    Finset.sum_le_sum fun i hi => hterm_bound i hi
  have hfinite_tsum :
      ∑ i ∈ S,
          (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
            (if k i ≤ j then
              lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
                (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0)
        ≤
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        (∑' i, if k i ≤ j then
          lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
            (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0) := by
    let K : ℝ := (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal)
    let g : ℕ → ℝ := fun i =>
      if k i ≤ j then
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0
    have hg_nonneg : ∀ i, 0 ≤ g i := by
      intro i
      dsimp [g]
      split_ifs
      · exact mul_nonneg (Real.rpow_nonneg hlam_pos.le _)
          (Real.rpow_nonneg
            (Finset.sum_nonneg fun Q hQ => Real.rpow_nonneg (norm_nonneg _) _) _)
      · exact le_rfl
    have hg_support : Function.support g ⊆ {i : ℕ | k i ≤ j} := by
      intro i hi
      by_contra hki
      have hki' : ¬ k i ≤ j := by simpa using hki
      have : g i = 0 := by simp [g, hki']
      exact hi this
    have hg_finite : (Function.support g).Finite :=
      (almostLinearSequence_finite_le_level hk j).subset hg_support
    have hgsum : Summable g := summable_of_hasFiniteSupport hg_finite
    have hsum_le : ∑ i ∈ S, g i ≤ ∑' i, g i :=
      hgsum.sum_le_tsum S (fun i hi => hg_nonneg i)
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hC _)
    calc
      ∑ i ∈ S,
          (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
            (if k i ≤ j then
              lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
                (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0)
          = K * ∑ i ∈ S, g i := by
            simp [K, g, Finset.mul_sum]
      _ ≤ K * (∑' i, g i) := mul_le_mul_of_nonneg_left hsum_le hK_nonneg
      _ =
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        (∑' i, if k i ≤ j then
          lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
            (CoeffPLevel (p := p) G c i) ^ (1 / p.toReal) else 0) := by
            simp [K, g]
  rw [hleft_eq]
  exact hMinkowski.trans (hfinite_le.trans hfinite_tsum)

namespace LpGridRepresentation

/-- Integer-indexed version of the paper's coefficient-cost function.

This is used for the convolution trick exactly as it appears in the paper,
where the kernel is naturally indexed by `ℤ` and may have a finite negative
tail. -/
noncomputable def cCoefficientInt (t q : ℝ≥0∞) (b : ℤ → ℝ) : ℝ :=
  if q = 1 then
    sSup (Set.range fun k => b k ^ (1 / t.toReal))
  else if q = ∞ then
    ∑' k : ℤ, b k ^ (1 / t.toReal)
  else
    let q' := q / (q - 1)
    (∑' k : ℤ, b k ^ (q'.toReal / t.toReal)) ^ (1 / q'.toReal)

/-- Nonnegativity of the integer-indexed coefficient-cost function. -/
private theorem cCoefficientInt_nonneg (t q : ℝ≥0∞) (b : ℤ → ℝ)
    (hb_nonneg : ∀ k, 0 ≤ b k) :
    0 ≤ cCoefficientInt t q b := by
  unfold cCoefficientInt
  split_ifs with hq1 hqtop
  · refine Real.sSup_nonneg ?_
    intro x hx
    rcases hx with ⟨k, rfl⟩
    exact Real.rpow_nonneg (hb_nonneg k) _
  · exact tsum_nonneg fun k => Real.rpow_nonneg (hb_nonneg k) _
  · exact Real.rpow_nonneg (tsum_nonneg fun k => Real.rpow_nonneg (hb_nonneg k) _) _

end LpGridRepresentation

/-- The truncated integer kernel from the paper:
`b_n = λ^(r n)` when `n > A / r - 1`, and `0` otherwise. -/
noncomputable def transmutationKernelZ (lam A r : ℝ) : ℤ → ℝ :=
  fun n => if A / r - 1 < (n : ℝ) then lam ^ (r * (n : ℝ)) else 0

/-- The truncated integer kernel has summable `1/p`-root.

The positive side is geometric.  The negative side is finite because the
paper's cutoff `n > A / r - 1` excludes all sufficiently negative integers. -/
private lemma transmutationKernelZ_root_summable
    (lam A r : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1) (hr : 0 < r)
    (hp_pos : 0 < p.toReal) :
    Summable fun n : ℤ => (transmutationKernelZ lam A r n) ^ (1 / p.toReal) := by
  classical
  let bZ : ℤ → ℝ := transmutationKernelZ lam A r
  let rho : ℝ := lam ^ (r / p.toReal)
  have hrho_nonneg : 0 ≤ rho := by
    dsimp [rho]
    exact Real.rpow_nonneg hlam_pos.le _
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    refine Real.rpow_lt_one hlam_pos.le hlam_lt ?_
    positivity
  have hpos_le : (fun n : ℕ => (bZ n) ^ (1 / p.toReal)) ≤ fun n : ℕ => rho ^ n := by
    intro n
    dsimp [bZ, transmutationKernelZ, rho]
    by_cases hn : A / r - 1 < (n : ℝ)
    · simp [hn]
      rw [← Real.rpow_mul hlam_pos.le]
      have hexp : r * (n : ℝ) * p.toReal⁻¹ = (r / p.toReal) * n := by
        ring
      rw [hexp, Real.rpow_mul hlam_pos.le, Real.rpow_natCast]
    · simp [hn]
      rw [Real.zero_rpow (inv_pos.mpr hp_pos).ne']
      exact pow_nonneg hrho_nonneg n
  have hpos_sum : Summable fun n : ℕ => (bZ n) ^ (1 / p.toReal) := by
    exact Summable.of_nonneg_of_le
      (fun n => by
        dsimp [bZ, transmutationKernelZ]
        split_ifs
        · exact Real.rpow_nonneg (Real.rpow_nonneg hlam_pos.le _) _
        · exact Real.rpow_nonneg le_rfl _)
      hpos_le
      (summable_geometric_of_lt_one hrho_nonneg hrho_lt_one)
  let M : ℕ := Nat.ceil (max (0 : ℝ) (-A / r))
  have hneg_support : Function.support (fun n : ℕ => (bZ (-(n + 1 : ℤ))) ^ (1 / p.toReal)) ⊆
      {n : ℕ | n < M} := by
    intro n hn
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq] at hn ⊢
    by_contra hM
    have hMle : M ≤ n := Nat.le_of_not_gt hM
    have hMle_real : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hMle
    have hceil_ge : max (0 : ℝ) (-A / r) ≤ (M : ℝ) := by
      dsimp [M]
      exact Nat.le_ceil _
    have hneg_le : -A / r ≤ (n : ℝ) := by
      exact (le_max_right (0 : ℝ) (-A / r)).trans (hceil_ge.trans hMle_real)
    have hcut_not : ¬ A / r - 1 < (-(n + 1 : ℤ) : ℝ) := by
      have hcast : (-(n + 1 : ℤ) : ℝ) = -((n : ℝ) + 1) := by norm_num
      intro hlt
      rw [hcast] at hlt
      have hneg_le' : -(A / r) ≤ (n : ℝ) := by
        rwa [neg_div] at hneg_le
      have hlt' : (n : ℝ) < -(A / r) := by linarith
      exact (not_lt_of_ge hneg_le') hlt'
    have hzero : (bZ (-(n + 1 : ℤ))) ^ (1 / p.toReal) = 0 := by
      dsimp [bZ, transmutationKernelZ]
      rw [if_neg]
      exact Real.zero_rpow (one_div_pos.mpr hp_pos).ne'
      intro hlt
      have hcast : ((-(↑n + 1) : ℤ) : ℝ) = -((n : ℝ) + 1) := by norm_num
      rw [hcast] at hlt
      have hneg_le' : -(A / r) ≤ (n : ℝ) := by
        rwa [neg_div] at hneg_le
      have hlt' : (n : ℝ) < -(A / r) := by linarith
      exact (not_lt_of_ge hneg_le') hlt'
    exact hn hzero
  have hneg_sum : Summable fun n : ℕ => (bZ (-(n + 1 : ℤ))) ^ (1 / p.toReal) :=
    summable_of_hasFiniteSupport ((Set.finite_lt_nat M).subset hneg_support)
  exact Summable.of_nat_of_neg_add_one hpos_sum hneg_sum

/-- Extend a sequence on `ℕ` to a sequence on `ℤ` by declaring all negative
indices to be zero.

This is a bookkeeping device used to rewrite the source sequence as a genuine
integer-indexed sequence before applying the convolution argument on `ℤ`.  The
extension does not change the positive part and adds no extra mass on the
negative side. -/
noncomputable def extendNatToInt (f : ℕ → ℝ) : ℤ → ℝ :=
  fun z => if hz : 0 ≤ z then f z.toNat else 0

/-- On nonnegative integers, `extendNatToInt` agrees with the original sequence. -/
private lemma extendNatToInt_ofNat (f : ℕ → ℝ) (n : ℕ) :
    extendNatToInt f n = f n := by
  simp [extendNatToInt]

/-- On strictly negative integers, `extendNatToInt` is zero. -/
private lemma extendNatToInt_negSucc (f : ℕ → ℝ) (n : ℕ) :
    extendNatToInt f (-(n + 1 : ℤ)) = 0 := by
  dsimp [extendNatToInt]
  rw [if_neg]
  omega

/-- Nonnegativity is preserved by the extension from `ℕ` to `ℤ`. -/
private lemma extendNatToInt_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    ∀ z : ℤ, 0 ≤ extendNatToInt f z := by
  intro z
  dsimp [extendNatToInt]
  split_ifs with hz
  · exact hf z.toNat
  · exact le_rfl

/-- A summable sequence on `ℕ` remains summable after zero-extension to `ℤ`. -/
private lemma summable_extendNatToInt {f : ℕ → ℝ} (hf : Summable f) :
    Summable (extendNatToInt f) := by
  have hpos : Summable fun n : ℕ => extendNatToInt f n := by
    simpa [extendNatToInt_ofNat] using hf
  have hneg : Summable fun n : ℕ => extendNatToInt f (-(n + 1 : ℤ)) := by
    have hzero : (fun n : ℕ => extendNatToInt f (-(n + 1 : ℤ))) = fun _ => 0 := by
      funext n
      exact extendNatToInt_negSucc f n
    rw [hzero]
    simp
  exact Summable.of_nat_of_neg_add_one hpos hneg

/-- The total sum of the zero-extension to `ℤ` is the same as the original sum
on `ℕ`. -/
private lemma tsum_extendNatToInt {f : ℕ → ℝ} (hf : Summable f) :
    (∑' z : ℤ, extendNatToInt f z) = ∑' n : ℕ, f n := by
  have hpos : Summable fun n : ℕ => extendNatToInt f n := by
    simpa [extendNatToInt_ofNat] using hf
  have hneg : Summable fun n : ℕ => extendNatToInt f (-(n + 1 : ℤ)) := by
    have hzero : (fun n : ℕ => extendNatToInt f (-(n + 1 : ℤ))) = fun _ => 0 := by
      funext n
      exact extendNatToInt_negSucc f n
    rw [hzero]
    simp
  have hpos_tsum :
      (∑' n : ℕ, extendNatToInt f n) = ∑' n : ℕ, f n :=
    tsum_congr fun n => extendNatToInt_ofNat f n
  have hneg_tsum :
      (∑' n : ℕ, extendNatToInt f (-(n + 1 : ℤ))) = 0 := by
    have hzero : (fun n : ℕ => extendNatToInt f (-(n + 1 : ℤ))) = fun _ => 0 := by
      funext n
      exact extendNatToInt_negSucc f n
    rw [hzero]
    simp
  calc
    (∑' z : ℤ, extendNatToInt f z)
        = (∑' n : ℕ, extendNatToInt f n) +
            ∑' n : ℕ, extendNatToInt f (-(n + 1 : ℤ)) :=
          tsum_of_nat_of_neg_add_one hpos hneg
    _ = (∑' n : ℕ, f n) + 0 := by rw [hpos_tsum, hneg_tsum]
    _ = ∑' n : ℕ, f n := by ring

/-- Quotient index in the residue-class decomposition of an output level.

For a given slope `r > 0`, `outputClassJ r k` is the coarse block index of the
paper's decomposition of `k` into something like `r * j + ell`. -/
noncomputable def outputClassJ (r : ℝ) (k : ℕ) : ℕ :=
  Nat.floor ((k : ℝ) / r)

/-- Residue-class index in the decomposition of an output level.

Together with `outputClassJ`, this records the bounded remainder when `k` is
written relative to the slope `r`.  The remainder always lives in one of the
finitely many classes indexed by `0, ..., ceil r - 1`. -/
noncomputable def outputClassEll (r : ℝ) (k : ℕ) : ℕ :=
  Nat.floor ((k : ℝ) - r * (outputClassJ r k : ℝ))

/-- Lower bound saying that `outputClassJ r k` does not overshoot `k / r`. -/
private lemma outputClassJ_lower (r : ℝ) (hr : 0 < r) (k : ℕ) :
    r * (outputClassJ r k : ℝ) ≤ (k : ℝ) := by
  have hdiv_nonneg : 0 ≤ (k : ℝ) / r := div_nonneg (Nat.cast_nonneg k) hr.le
  have hj_le : (outputClassJ r k : ℝ) ≤ (k : ℝ) / r := by
    simpa [outputClassJ] using Nat.floor_le hdiv_nonneg
  have hmul := mul_le_mul_of_nonneg_left hj_le hr.le
  calc
    r * (outputClassJ r k : ℝ) ≤ r * ((k : ℝ) / r) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    _ = (k : ℝ) := by
      field_simp [hr.ne']

/-- Upper bound saying that `outputClassJ r k` is the largest integer below `k / r`. -/
private lemma outputClassJ_upper (r : ℝ) (hr : 0 < r) (k : ℕ) :
    (k : ℝ) < r * (((outputClassJ r k) + 1 : ℕ) : ℝ) := by
  have hj_lt : (k : ℝ) / r < (outputClassJ r k : ℝ) + 1 := by
    simpa [outputClassJ] using Nat.lt_floor_add_one ((k : ℝ) / r)
  have hmul := mul_lt_mul_of_pos_left hj_lt hr
  calc
    (k : ℝ) = r * ((k : ℝ) / r) := by
      field_simp [hr.ne']
    _ < r * ((outputClassJ r k : ℝ) + 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    _ = r * (((outputClassJ r k) + 1 : ℕ) : ℝ) := by
      norm_num

/-- The paper's class decomposition: every output level `k` is hit by the
candidate `kout ell j = ceil (r*j + ell)` for its canonical class `ell` and
block index `j`, and the class is one of the `ceil r` classes. -/
private lemma outputClass_spec (r : ℝ) (hr : 0 < r) (k : ℕ) :
    outputClassEll r k < Nat.ceil r ∧
      Nat.ceil (r * (outputClassJ r k : ℝ) + (outputClassEll r k : ℝ)) = k ∧
      (k : ℝ) < r * (((outputClassJ r k) + 1 : ℕ) : ℝ) := by
  let j : ℕ := outputClassJ r k
  let ell : ℕ := outputClassEll r k
  let x : ℝ := (k : ℝ) - r * (j : ℝ)
  have hj_lower : r * (j : ℝ) ≤ (k : ℝ) := by
    simpa [j] using outputClassJ_lower r hr k
  have hj_upper : (k : ℝ) < r * (((j + 1 : ℕ) : ℝ)) := by
    simpa [j] using outputClassJ_upper r hr k
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    linarith
  have hx_lt_r : x < r := by
    dsimp [x]
    have hstep : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by norm_num
    rw [hstep] at hj_upper
    linarith
  have hell_le_x : (ell : ℝ) ≤ x := by
    dsimp [ell, outputClassEll, x, j]
    exact Nat.floor_le hx_nonneg
  have hx_lt_ell_add_one : x < (ell : ℝ) + 1 := by
    dsimp [ell, outputClassEll, x, j]
    exact Nat.lt_floor_add_one x
  have hell_lt_alpha : ell < Nat.ceil r := by
    have hell_lt_r : (ell : ℝ) < r := lt_of_le_of_lt hell_le_x hx_lt_r
    have hr_le_alpha : r ≤ (Nat.ceil r : ℝ) := Nat.le_ceil r
    exact_mod_cast lt_of_lt_of_le hell_lt_r hr_le_alpha
  have ha_le_k : r * (j : ℝ) + (ell : ℝ) ≤ (k : ℝ) := by
    dsimp [x] at hell_le_x
    linarith
  have hk_lt_a_add_one : (k : ℝ) < r * (j : ℝ) + (ell : ℝ) + 1 := by
    dsimp [x] at hx_lt_ell_add_one
    linarith
  have hceil_eq : Nat.ceil (r * (j : ℝ) + (ell : ℝ)) = k := by
    apply le_antisymm
    · exact (Nat.ceil_le).2 ha_le_k
    · have hceil_ge : r * (j : ℝ) + (ell : ℝ) ≤
          (Nat.ceil (r * (j : ℝ) + (ell : ℝ)) : ℝ) :=
        Nat.le_ceil _
      have hk_lt_ceil_add_one : (k : ℝ) <
          (Nat.ceil (r * (j : ℝ) + (ell : ℝ)) : ℝ) + 1 := by
        linarith
      exact Nat.lt_succ_iff.mp (by exact_mod_cast hk_lt_ceil_add_one)
  exact ⟨by simpa [ell] using hell_lt_alpha,
    by simpa [j, ell] using hceil_eq,
    by simpa [j] using hj_upper⟩

/-- The convolution estimate produced by the almost-linear structure.

This is the technical heart of Claim II.  Starting from a sequence of source
sizes `vL`, it studies the target-side quantity obtained by summing over all
source levels `i` with `k i ≤ j`, weighted by the geometric factor coming from
the representation decay.

The proof follows the paper's strategy closely:
1. split the indices `i` into finitely many residue classes modulo `ceil r`;
2. on each class, rewrite the sum as a genuine convolution on `ℤ`;
3. bound that convolution by the truncated kernel coming from the almost-linear
  lower and upper bounds on `k`;
4. recombine the finitely many classes and pay the factor `ceil r`.

The conclusion has two parts: summability of the target sequence, and the final
norm estimate with the explicit convolution constant
`LpGridRepresentation.cCoefficientInt p ∞ (transmutationKernelZ lam A_als r_als)`. -/
private lemma transmutation_convolution_bound
    (k : ℕ → ℕ)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
  (A_als B_als r_als : ℝ ) (hr_als : 0 < r_als)
    (hk_upper : ∀ i : ℕ, (k i : NNReal) ≤ r_als * (i : NNReal) + B_als)
  (hk_lower : ∀ i : ℕ, r_als * (i : NNReal) + A_als ≤ k i)
    (vL : ℕ → ℝ)
    (hvL_nn : ∀ i, 0 ≤ vL i)
    (hsource : Summable fun i => vL i ^ (q.toReal / p.toReal))
  (hp_ne_top : p ≠ ∞)
    (hq_ne_top : q ≠ ∞) :
    Summable (fun j =>
      (∑' i, if k i ≤ j then
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (vL i) ^ (1 / p.toReal) else 0) ^ q.toReal) ∧
    (∑' j, (∑' i, if k i ≤ j then
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (vL i) ^ (1 / p.toReal) else 0) ^ q.toReal) ^ (1 / q.toReal) ≤
      lam ^ (-(B_als : ℝ) / p.toReal) *
      LpGridRepresentation.cCoefficientInt p ∞
        (transmutationKernelZ lam A_als r_als) *
      (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
      (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
  let alpha : ℕ := Nat.ceil (r_als : ℝ)
  let bZ : ℤ → ℝ := transmutationKernelZ lam A_als r_als
  let convL : ℕ → ℝ := fun j =>
    ∑' i, if k i ≤ j then
      lam ^ ((↑(j - k i) : ℝ) / p.toReal) * (vL i) ^ (1 / p.toReal) else 0
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos
      (fun h0 => absurd (h0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)) (by norm_num))
      hp_ne_top
  have hq_pos : 0 < q.toReal :=
    ENNReal.toReal_pos
      (fun h0 => absurd (h0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ q)) (by norm_num))
      hq_ne_top
  have halpha_pos : 0 < alpha := by
    have hr_pos_real : 0 < (r_als : ℝ) := by exact_mod_cast hr_als
    exact Nat.ceil_pos.mpr hr_pos_real
  have hbZ_nonneg : ∀ n, 0 ≤ bZ n := by
    intro n
    dsimp [bZ, transmutationKernelZ]
    split_ifs
    · exact Real.rpow_nonneg hlam_pos.le _
    · exact le_rfl
  have hconvL_nn : ∀ j, 0 ≤ convL j := by
    intro j
    exact tsum_nonneg fun i => by
      split_ifs with hij
      · exact mul_nonneg (Real.rpow_nonneg hlam_pos.le _) (Real.rpow_nonneg (hvL_nn i) _)
      · exact le_rfl
  have hsource_nn : ∀ i, 0 ≤ vL i ^ (q.toReal / p.toReal) := by
    intro i
    exact Real.rpow_nonneg (hvL_nn i) _
  have hccoeff_nonneg : 0 ≤ LpGridRepresentation.cCoefficientInt p ∞ bZ :=
    LpGridRepresentation.cCoefficientInt_nonneg p ∞ bZ hbZ_nonneg
  have hccoeff_eq :
      LpGridRepresentation.cCoefficientInt p ∞ bZ =
        ∑' n : ℤ, bZ n ^ (1 / p.toReal) := by
    simp [LpGridRepresentation.cCoefficientInt, bZ]
  let srcPow : Fin alpha → ℕ → ℝ :=
    fun m n => vL (m.1 + alpha * n) ^ (q.toReal / p.toReal)
  have hsrcPow_summable : ∀ m : Fin alpha, Summable (srcPow m) := by
    intro m
    simpa [srcPow] using
      summable_arithProg_comp hsource (a := alpha) (b := m.1) halpha_pos
  have hsrcPow_le : ∀ m : Fin alpha, (∑' n, srcPow m n) ≤ ∑' i, vL i ^ (q.toReal / p.toReal) := by
    intro m
    simpa [srcPow] using
      tsum_arithProg_le hsource hsource_nn (a := alpha) (b := m.1) halpha_pos
  have hsrcRoot_le : ∀ m : Fin alpha,
      (∑' n, srcPow m n) ^ (1 / q.toReal) ≤
        (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
    intro m
    exact Real.rpow_le_rpow
      (tsum_nonneg fun n => by simpa [srcPow] using hsource_nn (m.1 + alpha * n))
      (hsrcPow_le m)
      (div_nonneg zero_le_one hq_pos.le)
  let Csrc : ℝ := (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)
  have hCsrc_nonneg : 0 ≤ Csrc := by
    dsimp [Csrc]
    exact Real.rpow_nonneg (tsum_nonneg hsource_nn) _
  have hsrcFamily_le :
      (∑ m : Fin alpha, ((∑' n, srcPow m n) ^ (1 / q.toReal)) ^ q.toReal) ^ (1 / q.toReal) ≤
        (alpha : ℝ) ^ (1 / q.toReal) * Csrc := by
    simpa [Csrc] using
      finset_Lq_le_card_rpow_mul_bound (q := q) (S := (Finset.univ : Finset (Fin alpha)))
        (a := fun m => (∑' n, srcPow m n) ^ (1 / q.toReal))
        ((∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal))
        (fun m hm => Real.rpow_nonneg (tsum_nonneg fun n => by
          simpa [srcPow] using hsource_nn (m.1 + alpha * n)) _)
        (fun m hm => hsrcRoot_le m)
        hCsrc_nonneg
        hq_ne_top
  let kout : Fin alpha → ℕ → ℕ :=
    fun ell j => Nat.ceil ((r_als : ℝ) * (j : ℝ) + (ell.1 : ℝ))
  let koutExists : Fin alpha → ℕ → Prop :=
    fun ell j => ((kout ell j : ℕ) : ℝ) < (r_als : ℝ) * ((j + 1 : ℕ) : ℝ)
  have hkout_lower : ∀ ell : Fin alpha, ∀ j : ℕ,
      (r_als : ℝ) * (j : ℝ) + (ell.1 : ℝ) ≤ (kout ell j : ℕ) := by
    intro ell j
    exact Nat.le_ceil _
  have hkout_lt_add_one : ∀ ell : Fin alpha, ∀ j : ℕ,
      ((kout ell j : ℕ) : ℝ) < (r_als : ℝ) * (j : ℝ) + (ell.1 : ℝ) + 1 := by
    intro ell j
    apply Nat.ceil_lt_add_one
    positivity
  have hkout_eq_when_exists : ∀ ell : Fin alpha, ∀ j : ℕ,
      koutExists ell j →
        (r_als : ℝ) * (j : ℝ) + (ell.1 : ℝ) ≤ (kout ell j : ℕ) ∧
        ((kout ell j : ℕ) : ℝ) < (r_als : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    intro ell j hEx
    exact ⟨hkout_lower ell j, hEx⟩
  let kclass : ℕ → Sigma fun _ell : Fin alpha => ℕ := fun j =>
    ⟨⟨outputClassEll r_als j, by
        have hspec := (outputClass_spec r_als hr_als j).1
        simpa [alpha] using hspec⟩, outputClassJ r_als j⟩
  have hkclass_kout : ∀ j : ℕ, kout (kclass j).1 (kclass j).2 = j := by
    intro j
    have hspec := (outputClass_spec r_als hr_als j).2.1
    simpa [kclass, kout] using hspec
  have hkclass_exists : ∀ j : ℕ, koutExists (kclass j).1 (kclass j).2 := by
    intro j
    have hspec := (outputClass_spec r_als hr_als j).2.2
    dsimp [koutExists]
    rw [hkclass_kout j]
    simpa [kclass] using hspec
  have hkclass_injective : Function.Injective kclass := by
    intro j₁ j₂ hEq
    calc
      j₁ = kout (kclass j₁).1 (kclass j₁).2 := (hkclass_kout j₁).symm
      _ = kout (kclass j₂).1 (kclass j₂).2 := by rw [hEq]
      _ = j₂ := hkclass_kout j₂
  let classConv : Fin alpha → ℕ → ℝ := fun ell j =>
    if koutExists ell j then convL (kout ell j) else 0
  have hclassConv_nonneg : ∀ ell : Fin alpha, ∀ j : ℕ, 0 ≤ classConv ell j := by
    intro ell j
    dsimp [classConv]
    split_ifs
    · exact hconvL_nn _
    · exact le_rfl
  have hclassConv_kclass : ∀ j : ℕ,
      classConv (kclass j).1 (kclass j).2 = convL j := by
    intro j
    dsimp [classConv]
    rw [if_pos (hkclass_exists j), hkclass_kout j]
  have hkclass_of_exists : ∀ ell : Fin alpha, ∀ j : ℕ,
      koutExists ell j → kclass (kout ell j) = ⟨ell, j⟩ := by
    intro ell j hEx
    have hJ_eq : outputClassJ r_als (kout ell j) = j := by
      have hdiv_nonneg : 0 ≤ ((kout ell j : ℕ) : ℝ) / r_als :=
        div_nonneg (Nat.cast_nonneg _) hr_als.le
      refine (Nat.floor_eq_iff hdiv_nonneg).2 ⟨?_, ?_⟩
      · rw [le_div_iff₀ hr_als]
        have hlow := hkout_lower ell j
        have hell_nonneg : 0 ≤ (ell.1 : ℝ) := by positivity
        linarith
      · rw [div_lt_iff₀ hr_als]
        have hExReal : ((kout ell j : ℕ) : ℝ) < r_als * ((j : ℝ) + 1) := by
          simpa [koutExists] using hEx
        linarith
    have hEll_eq : outputClassEll r_als (kout ell j) = ell.1 := by
      have hlow := hkout_lower ell j
      have hhi := hkout_lt_add_one ell j
      have hx_nonneg :
          0 ≤ ((kout ell j : ℕ) : ℝ) - r_als * (j : ℝ) := by
        have hell_nonneg : 0 ≤ (ell.1 : ℝ) := by positivity
        linarith
      have hfloor : Nat.floor (((kout ell j : ℕ) : ℝ) - r_als * (j : ℝ)) = ell.1 := by
        refine (Nat.floor_eq_iff hx_nonneg).2 ⟨?_, ?_⟩
        · linarith
        · linarith
      simpa [outputClassEll, hJ_eq] using hfloor
    apply Sigma.ext
    · exact Fin.ext hEll_eq
    · simp [kclass, hJ_eq]
  let existingClass : Type := {x : Sigma fun _ell : Fin alpha => ℕ // koutExists x.1 x.2}
  let kclassExisting : ℕ → existingClass := fun j => ⟨kclass j, hkclass_exists j⟩
  have hkclassExisting_bijective : Function.Bijective kclassExisting := by
    constructor
    · intro j₁ j₂ hEq
      exact hkclass_injective (congrArg Subtype.val hEq)
    · intro x
      rcases x with ⟨x, hx⟩
      rcases x with ⟨ell, j⟩
      refine ⟨kout ell j, ?_⟩
      apply Subtype.ext
      exact hkclass_of_exists ell j hx
  have hclassConv_existing : ∀ x : existingClass,
      classConv x.1.1 x.1.2 = convL (kout x.1.1 x.1.2) := by
    intro x
    dsimp [classConv]
    exact if_pos x.2
  let kclassEquiv : ℕ ≃ existingClass :=
    Equiv.ofBijective kclassExisting hkclassExisting_bijective
  have htsum_existing :
      (∑' j : ℕ, convL j ^ q.toReal) =
        ∑' x : existingClass, classConv x.1.1 x.1.2 ^ q.toReal := by
    rw [← kclassEquiv.tsum_eq (fun x : existingClass =>
      classConv x.1.1 x.1.2 ^ q.toReal)]
    apply tsum_congr
    intro j
    simp [kclassEquiv, kclassExisting, hclassConv_kclass]
  have htsum_le_classSigma :
      Summable (fun x : (Sigma fun _ell : Fin alpha => ℕ) =>
        classConv x.1 x.2 ^ q.toReal) →
      (∑' j : ℕ, convL j ^ q.toReal) ≤
        ∑' x : (Sigma fun _ell : Fin alpha => ℕ), classConv x.1 x.2 ^ q.toReal := by
    intro hsClass
    rw [htsum_existing]
    exact tsum_comp_le_tsum_of_injective
      (ι := existingClass) (κ := Sigma fun _ell : Fin alpha => ℕ)
      (f := fun x => classConv x.1 x.2 ^ q.toReal)
      hsClass
      (fun x => Real.rpow_nonneg (hclassConv_nonneg x.1 x.2) _)
      (phi := Subtype.val)
      Subtype.val_injective
  have hclassYoung :
      Summable (fun x : (Sigma fun _ell : Fin alpha => ℕ) =>
        classConv x.1 x.2 ^ q.toReal) ∧
      (∑' x : (Sigma fun _ell : Fin alpha => ℕ), classConv x.1 x.2 ^ q.toReal) ^
          (1 / q.toReal) ≤
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞ bZ *
        (alpha : ℝ) ^ (1 / q.toReal) *
        Csrc := by
    let srcRoot : ℕ → ℝ := fun i => vL i ^ (1 / p.toReal)
    let srcZ : ℤ → ℝ := extendNatToInt srcRoot
    let convZ : ℤ → ℝ := fun j =>
      ∑' n : ℤ, bZ n ^ (1 / p.toReal) * srcZ (j - n)
    have hbRoot_summable : Summable fun n : ℤ => bZ n ^ (1 / p.toReal) := by
      simpa [bZ] using
        transmutationKernelZ_root_summable (p := p)
          lam A_als r_als hlam_pos hlam_lt hr_als hp_pos
    have hbRoot_nonneg : ∀ n : ℤ, 0 ≤ bZ n ^ (1 / p.toReal) := by
      intro n
      exact Real.rpow_nonneg (hbZ_nonneg n) _
    have hsrcRoot_nonneg : ∀ i : ℕ, 0 ≤ srcRoot i := by
      intro i
      exact Real.rpow_nonneg (hvL_nn i) _
    have hsrcZ_nonneg : ∀ z : ℤ, 0 ≤ srcZ z := by
      simpa [srcZ] using extendNatToInt_nonneg hsrcRoot_nonneg
    have hsrcRoot_q_summable : Summable fun i : ℕ => srcRoot i ^ q.toReal := by
      have hpow_eq :
          (fun i : ℕ => srcRoot i ^ q.toReal) =
            fun i : ℕ => vL i ^ (q.toReal / p.toReal) := by
        funext i
        dsimp [srcRoot]
        rw [← Real.rpow_mul (hvL_nn i)]
        ring_nf
      simpa [hpow_eq] using hsource
    have hsrcZ_q_summable : Summable fun z : ℤ => srcZ z ^ q.toReal := by
      have hpow_eq :
          (fun z : ℤ => srcZ z ^ q.toReal) =
            extendNatToInt (fun i : ℕ => srcRoot i ^ q.toReal) := by
        funext z
        by_cases hz : 0 ≤ z
        · simp [srcZ, extendNatToInt, hz]
        · simp [srcZ, extendNatToInt, hz, Real.zero_rpow hq_pos.ne']
      simpa [hpow_eq] using summable_extendNatToInt hsrcRoot_q_summable
    have hsrcZ_q_tsum :
        (∑' z : ℤ, srcZ z ^ q.toReal) =
          ∑' i : ℕ, vL i ^ (q.toReal / p.toReal) := by
      calc
        (∑' z : ℤ, srcZ z ^ q.toReal)
            = ∑' i : ℕ, srcRoot i ^ q.toReal := by
              have hpow_eq :
                  (fun z : ℤ => srcZ z ^ q.toReal) =
                    extendNatToInt (fun i : ℕ => srcRoot i ^ q.toReal) := by
                funext z
                by_cases hz : 0 ≤ z
                · simp [srcZ, extendNatToInt, hz]
                · simp [srcZ, extendNatToInt, hz, Real.zero_rpow hq_pos.ne']
              simpa [hpow_eq] using tsum_extendNatToInt hsrcRoot_q_summable
        _ = ∑' i : ℕ, vL i ^ (q.toReal / p.toReal) := by
              apply tsum_congr
              intro i
              dsimp [srcRoot]
              rw [← Real.rpow_mul (hvL_nn i)]
              ring_nf
    have hconvZ_nonneg : ∀ j : ℤ, 0 ≤ convZ j := by
      intro j
      dsimp [convZ]
      exact tsum_nonneg fun n => mul_nonneg (hbRoot_nonneg n) (hsrcZ_nonneg (j - n))
    let scale : ℝ := lam ^ (-(B_als : ℝ) / p.toReal)
    have hscale_nonneg : 0 ≤ scale := by
      dsimp [scale]
      exact Real.rpow_nonneg hlam_pos.le _
    have hclass_le_convZ : ∀ ell : Fin alpha, ∀ j : ℕ,
        classConv ell j ≤ scale * convZ j := by
      intro ell j
      dsimp [classConv]
      by_cases hEx : koutExists ell j
      · rw [if_pos hEx]
        let f : ℕ → ℝ := fun i =>
          if k i ≤ kout ell j then
            lam ^ ((↑(kout ell j - k i) : ℝ) / p.toReal) * srcRoot i
          else 0
        let sec : ℤ → ℝ := fun n =>
          bZ n ^ (1 / p.toReal) * srcZ ((j : ℤ) - n)
        have hf_nonneg : ∀ i, 0 ≤ f i := by
          intro i
          dsimp [f]
          split_ifs with hik
          · exact mul_nonneg (Real.rpow_nonneg hlam_pos.le _) (hsrcRoot_nonneg i)
          · exact le_rfl
        have hf_support : Function.support f ⊆ {i : ℕ | k i ≤ kout ell j} := by
          intro i hi
          by_contra hik
          have hik' : ¬ k i ≤ kout ell j := by simpa using hik
          have : f i = 0 := by simp [f, hik']
          exact hi this
        have hf_sum : Summable f :=
          summable_of_hasFiniteSupport
            ((almostLinearSequence_finite_le_level
              ⟨A_als, B_als, r_als, hr_als, fun i => ⟨hk_upper i, hk_lower i⟩⟩
              (kout ell j)).subset hf_support)
        have hconv_eq : convL (kout ell j) = ∑' i, f i := by
          simp [convL, f, srcRoot]
        rw [hconv_eq]
        have hsec_nonneg : ∀ n : ℤ, 0 ≤ sec n := by
          intro n
          dsimp [sec]
          exact mul_nonneg (hbRoot_nonneg n) (hsrcZ_nonneg ((j : ℤ) - n))
        let M : ℕ := Nat.ceil (max (0 : ℝ) (-A_als / r_als))
        have hsec_support : Function.support sec ⊆ Set.Icc (-(M : ℤ)) j := by
          intro n hn
          simp only [Function.mem_support, ne_eq] at hn
          constructor
          · by_contra hnlow
            have hsucc : n + 1 ≤ -(M : ℤ) := by omega
            have hsucc_real : (n : ℝ) + 1 ≤ -((M : ℝ)) := by exact_mod_cast hsucc
            have hceil_ge : max (0 : ℝ) (-A_als / r_als) ≤ (M : ℝ) := by
              dsimp [M]
              exact Nat.le_ceil _
            have hneg_bound : -((M : ℝ)) ≤ A_als / r_als := by
              have hA_bound : -A_als / r_als ≤ (M : ℝ) :=
                (le_max_right (0 : ℝ) (-A_als / r_als)).trans hceil_ge
              convert neg_le_neg hA_bound using 1 <;> ring
            have hcut_not : ¬ A_als / r_als - 1 < (n : ℝ) := by
              have hle : (n : ℝ) + 1 ≤ A_als / r_als := hsucc_real.trans hneg_bound
              linarith
            have hb_zero : bZ n = 0 := by
              dsimp [bZ, transmutationKernelZ]
              simp [hcut_not]
            have hb_root_zero : bZ n ^ (1 / p.toReal) = 0 := by
              rw [hb_zero, Real.zero_rpow (one_div_pos.mpr hp_pos).ne']
            have hsec_zero : sec n = 0 := by
              rw [show sec n = bZ n ^ (1 / p.toReal) * srcZ ((j : ℤ) - n) by rfl, hb_root_zero]
              ring
            exact hn hsec_zero
          · by_contra hnj
            have hneg : ¬ 0 ≤ (j : ℤ) - n := by omega
            have hsrc_zero : srcZ ((j : ℤ) - n) = 0 := by
              dsimp [srcZ, extendNatToInt]
              rw [if_neg hneg]
            have hsec_zero : sec n = 0 := by
              rw [show sec n = bZ n ^ (1 / p.toReal) * srcZ ((j : ℤ) - n) by rfl, hsrc_zero]
              ring
            exact hn hsec_zero
        have hsec_sum : Summable sec :=
          summable_of_hasFiniteSupport ((Set.finite_Icc (-(M : ℤ)) j).subset hsec_support)
        have hphi_inj : Function.Injective (fun i : ℕ => (j : ℤ) - i) := by
          intro a b hab
          have : (a : ℤ) = b := by linarith
          exact_mod_cast this
        have hterm_le : ∀ i : ℕ, f i ≤ scale * sec ((j : ℤ) - i) := by
          intro i
          by_cases hik : k i ≤ kout ell j
          · have hk_upper_real : (k i : ℝ) ≤ r_als * (i : ℝ) + B_als := by
              exact_mod_cast hk_upper i
            have hk_le_real : (k i : ℝ) ≤ (kout ell j : ℝ) := by
              exact_mod_cast hik
            have hkout_ge_j : r_als * (j : ℝ) ≤ (kout ell j : ℝ) := by
              have hell_nonneg : 0 ≤ (ell.1 : ℝ) := by positivity
              linarith [hkout_lower ell j]
            have hlag_cut_real : A_als / r_als - 1 < (j : ℝ) - (i : ℝ) := by
              have hk_lower_real : r_als * (i : ℝ) + A_als ≤ (k i : ℝ) := by
                exact_mod_cast hk_lower i
              have hkout_lt : (kout ell j : ℝ) < r_als * ((j + 1 : ℕ) : ℝ) := by
                simpa [koutExists] using hEx
              have hklt : (k i : ℝ) < r_als * ((j + 1 : ℕ) : ℝ) :=
                lt_of_le_of_lt hk_le_real hkout_lt
              have hlt : A_als < r_als * (((j : ℝ) + 1) - (i : ℝ)) := by
                have hmid : r_als * (i : ℝ) + A_als < r_als * ((j + 1 : ℕ) : ℝ) :=
                  lt_of_le_of_lt hk_lower_real hklt
                have hrew :
                    r_als * (((j : ℝ) + 1) - (i : ℝ)) =
                      r_als * ((j + 1 : ℕ) : ℝ) - r_als * (i : ℝ) := by
                  calc
                    r_als * (((j : ℝ) + 1) - (i : ℝ))
                        = r_als * ((j : ℝ) + 1) - r_als * (i : ℝ) := by ring
                    _ = r_als * ((j + 1 : ℕ) : ℝ) - r_als * (i : ℝ) := by
                      norm_num [Nat.cast_add]
                rw [hrew]
                linarith
              have hdiv : A_als / r_als < ((j : ℝ) + 1) - (i : ℝ) := by
                rw [div_lt_iff₀ hr_als]
                simpa [mul_comm, mul_left_comm, mul_assoc] using hlt
              linarith
            have hlag_cut : A_als / r_als - 1 < ((((j : ℤ) - i : ℤ) : ℝ)) := by
              have hcast : ((((j : ℤ) - i : ℤ) : ℝ)) = (j : ℝ) - (i : ℝ) := by
                norm_num
              simpa [hcast] using hlag_cut_real
            have hb_eq :
                bZ ((j : ℤ) - i) = lam ^ (r_als * ((((j : ℤ) - i : ℤ) : ℝ))) := by
              dsimp [bZ, transmutationKernelZ]
              rw [if_pos hlag_cut]
            have hb_root_eq :
                bZ ((j : ℤ) - i) ^ (1 / p.toReal) =
                  lam ^ ((r_als * ((((j : ℤ) - i : ℤ) : ℝ))) / p.toReal) := by
              rw [hb_eq, ← Real.rpow_mul hlam_pos.le]
              congr 1
              ring
            have hlag_exp :
                (r_als * ((((j : ℤ) - i : ℤ) : ℝ)) - B_als) / p.toReal ≤
                  ((↑(kout ell j - k i) : ℝ) / p.toReal) := by
              rw [Nat.cast_sub hik]
              have hcast : ((((j : ℤ) - i : ℤ) : ℝ)) = (j : ℝ) - (i : ℝ) := by
                norm_num
              rw [hcast]
              field_simp [hp_pos.ne']
              linarith
            have hlam_le :
                lam ^ ((↑(kout ell j - k i) : ℝ) / p.toReal) ≤
                  scale * bZ ((j : ℤ) - i) ^ (1 / p.toReal) := by
              calc
                lam ^ ((↑(kout ell j - k i) : ℝ) / p.toReal)
                    ≤ lam ^ ((r_als * ((((j : ℤ) - i : ℤ) : ℝ)) - B_als) / p.toReal) := by
                      exact Real.rpow_le_rpow_of_exponent_ge hlam_pos hlam_lt.le hlag_exp
                _ = scale * bZ ((j : ℤ) - i) ^ (1 / p.toReal) := by
                    rw [hb_root_eq]
                    have hexp :
                        ((r_als * ((((j : ℤ) - i : ℤ) : ℝ)) - B_als) / p.toReal) =
                          -(B_als : ℝ) / p.toReal +
                            (r_als * ((((j : ℤ) - i : ℤ) : ℝ))) / p.toReal := by
                      field_simp [hp_pos.ne']
                      ring
                    rw [hexp, ← Real.rpow_add hlam_pos]
            have hsrc_eq : srcZ ((j : ℤ) - ((j : ℤ) - i)) = srcRoot i := by
              have hsub : (j : ℤ) - ((j : ℤ) - i) = i := by ring
              rw [hsub]
              simpa [srcZ] using extendNatToInt_ofNat srcRoot i
            calc
              f i = lam ^ ((↑(kout ell j - k i) : ℝ) / p.toReal) * srcRoot i := by
                simp [f, hik]
              _ ≤ (scale * bZ ((j : ℤ) - i) ^ (1 / p.toReal)) * srcRoot i := by
                exact mul_le_mul_of_nonneg_right hlam_le (hsrcRoot_nonneg i)
              _ = scale * sec ((j : ℤ) - i) := by
                rw [show sec ((j : ℤ) - i) =
                    bZ ((j : ℤ) - i) ^ (1 / p.toReal) * srcZ ((j : ℤ) - ((j : ℤ) - i)) by rfl,
                  hsrc_eq]
                ring
          · have hnonneg : 0 ≤ scale * sec ((j : ℤ) - i) := by
              exact mul_nonneg hscale_nonneg (hsec_nonneg ((j : ℤ) - i))
            simpa [f, hik] using hnonneg
        have hsum_comp : Summable fun i : ℕ => scale * sec ((j : ℤ) - i) :=
          (hsec_sum.mul_left scale).comp_injective hphi_inj
        have hsum_le : (∑' i : ℕ, f i) ≤ ∑' i : ℕ, scale * sec ((j : ℤ) - i) :=
          hf_sum.tsum_le_tsum hterm_le hsum_comp
        have hsum_reindex :
            (∑' i : ℕ, scale * sec ((j : ℤ) - i)) ≤ ∑' n : ℤ, scale * sec n := by
          exact tsum_comp_le_tsum_of_injective
            ((hsec_sum.mul_left scale))
            (fun n => mul_nonneg hscale_nonneg (hsec_nonneg n))
            hphi_inj
        have htsum_scale : (∑' n : ℤ, scale * sec n) = scale * convZ j := by
          calc
            (∑' n : ℤ, scale * sec n) = scale * ∑' n : ℤ, sec n := by
              simpa [sec, mul_assoc] using (hsec_sum.hasSum.mul_left scale).tsum_eq
            _ = scale * convZ j := by rfl
        exact (hsum_le.trans hsum_reindex).trans_eq htsum_scale
      · have hnonneg : 0 ≤ scale * convZ j := mul_nonneg hscale_nonneg (hconvZ_nonneg j)
        simpa [hEx] using hnonneg
    have hYoungZ :
        Summable (fun j : ℤ => convZ j ^ q.toReal) ∧
        (∑' j : ℤ, convZ j ^ q.toReal) ^ (1 / q.toReal) ≤
          LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc := by
      have hq_one : (1 : ℝ) ≤ q.toReal := by
        have h := ENNReal.toReal_mono hq_ne_top (Fact.out : (1 : ℝ≥0∞) ≤ q)
        simpa using h
      let a : ℤ → ℝ := fun n => bZ n ^ (1 / p.toReal)
      let e : ℕ ≃ ℤ := Equiv.intEquivNat.symm
      let part : ℕ → ℤ → ℝ :=
        fun N j => ∑ m ∈ Finset.range N, a (e m) * srcZ (j - e m)
      have ha_nonneg : ∀ n : ℤ, 0 ≤ a n := by
        intro n
        exact hbRoot_nonneg n
      have ha_sum_nat : Summable (fun m : ℕ => a (e m)) :=
        hbRoot_summable.comp_injective e.injective
      have ha_tsum_eq :
          (∑' m : ℕ, a (e m)) = LpGridRepresentation.cCoefficientInt p ∞ bZ := by
        calc
          (∑' m : ℕ, a (e m)) = ∑' n : ℤ, a n := by
            simpa [e] using (e.tsum_eq a)
          _ = LpGridRepresentation.cCoefficientInt p ∞ bZ := by
            simpa [a] using hccoeff_eq.symm
      have hsrcZ_le_Csrc : ∀ z : ℤ, srcZ z ≤ Csrc := by
        intro z
        have hsingle : srcZ z ^ q.toReal ≤ ∑' j : ℤ, srcZ j ^ q.toReal := by
          have hle := hsrcZ_q_summable.sum_le_tsum ({z} : Finset ℤ)
            (fun j hj => Real.rpow_nonneg (hsrcZ_nonneg j) _)
          simpa using hle
        have hroot := Real.rpow_le_rpow
          (Real.rpow_nonneg (hsrcZ_nonneg z) _)
          hsingle
          (div_nonneg zero_le_one hq_pos.le)
        calc
          srcZ z = (srcZ z ^ q.toReal) ^ (1 / q.toReal) := by
            rw [← Real.rpow_mul (hsrcZ_nonneg z)]
            field_simp [hq_pos.ne']
            rw [Real.rpow_one]
          _ ≤ (∑' j : ℤ, srcZ j ^ q.toReal) ^ (1 / q.toReal) := hroot
          _ = Csrc := by simp [Csrc, hsrcZ_q_tsum]
      have hterm_q_summable : ∀ z : ℤ,
          Summable (fun j : ℤ => (a z * srcZ (j - z)) ^ q.toReal) := by
        intro z
        have hshift : Summable (fun j : ℤ => srcZ (j - z) ^ q.toReal) := by
          simpa using hsrcZ_q_summable.comp_injective (Equiv.subRight z).injective
        have hmul : Summable (fun j : ℤ => a z ^ q.toReal * (srcZ (j - z) ^ q.toReal)) :=
          hshift.mul_left (a z ^ q.toReal)
        convert hmul using 1
        ext j
        rw [Real.mul_rpow (ha_nonneg z) (hsrcZ_nonneg (j - z))]
      have hterm_norm : ∀ z : ℤ,
          (∑' j : ℤ, (a z * srcZ (j - z)) ^ q.toReal) ^ (1 / q.toReal) ≤ a z * Csrc := by
        intro z
        have hshift_tsum :
            (∑' j : ℤ, srcZ (j - z) ^ q.toReal) = ∑' j : ℤ, srcZ j ^ q.toReal := by
          simpa using (Equiv.subRight z).tsum_eq (fun j : ℤ => srcZ j ^ q.toReal)
        have htsum_eq :
            (∑' j : ℤ, (a z * srcZ (j - z)) ^ q.toReal) =
              a z ^ q.toReal * ∑' j : ℤ, srcZ j ^ q.toReal := by
          calc
            (∑' j : ℤ, (a z * srcZ (j - z)) ^ q.toReal)
                = ∑' j : ℤ, a z ^ q.toReal * (srcZ (j - z) ^ q.toReal) := by
                    apply tsum_congr
                    intro j
                    rw [Real.mul_rpow (ha_nonneg z) (hsrcZ_nonneg (j - z))]
            _ = a z ^ q.toReal * ∑' j : ℤ, srcZ (j - z) ^ q.toReal := by
                  simpa [mul_assoc] using ((hsrcZ_q_summable.comp_injective (Equiv.subRight z).injective).hasSum.mul_left (a z ^ q.toReal)).tsum_eq
            _ = a z ^ q.toReal * ∑' j : ℤ, srcZ j ^ q.toReal := by rw [hshift_tsum]
        calc
          (∑' j : ℤ, (a z * srcZ (j - z)) ^ q.toReal) ^ (1 / q.toReal)
              = (a z ^ q.toReal * ∑' j : ℤ, srcZ j ^ q.toReal) ^ (1 / q.toReal) := by
                  rw [htsum_eq]
          _ = (a z ^ q.toReal) ^ (1 / q.toReal) * (∑' j : ℤ, srcZ j ^ q.toReal) ^ (1 / q.toReal) := by
                rw [Real.mul_rpow (Real.rpow_nonneg (ha_nonneg z) _) (tsum_nonneg fun j => Real.rpow_nonneg (hsrcZ_nonneg j) _)]
              _ ≤ a z * Csrc := by
                apply le_of_eq
                rw [← Real.rpow_mul (ha_nonneg z)]
                field_simp [hq_pos.ne']
                rw [Real.rpow_one]
                simp [Csrc, hsrcZ_q_tsum]
      have hpart_nonneg : ∀ N : ℕ, ∀ j : ℤ, 0 ≤ part N j := by
        intro N j
        exact Finset.sum_nonneg fun m hm => mul_nonneg (ha_nonneg _) (hsrcZ_nonneg _)
      have hpart_bound : ∀ N : ℕ,
          Summable (fun j : ℤ => part N j ^ q.toReal) ∧
          (∑' j : ℤ, part N j ^ q.toReal) ^ (1 / q.toReal) ≤
            (∑ m ∈ Finset.range N, a (e m)) * Csrc := by
        intro N
        induction' N with N ih
        · constructor
          · simp [part, Real.zero_rpow hq_pos.ne']
          · have hzero : (∑' j : ℤ, part 0 j ^ q.toReal) = 0 := by
                simp [part, Real.zero_rpow hq_pos.ne']
            rw [hzero]
            rw [Real.zero_rpow (one_div_ne_zero hq_pos.ne')]
            simp
        · rcases ih with ⟨ih_sum, ih_bound⟩
          have hterm_nonneg : ∀ j : ℤ, 0 ≤ a (e N) * srcZ (j - e N) := by
            intro j
            exact mul_nonneg (ha_nonneg _) (hsrcZ_nonneg _)
          have hsum_succ : Summable (fun j : ℤ => part (N + 1) j ^ q.toReal) := by
            simpa [part, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using
              Real.summable_Lp_add_of_nonneg
                hq_one
                (fun j => hpart_nonneg N j)
                hterm_nonneg
                ih_sum
                (hterm_q_summable (e N))
          have hbound_succ :
              (∑' j : ℤ, part (N + 1) j ^ q.toReal) ^ (1 / q.toReal) ≤
                (∑ m ∈ Finset.range (N + 1), a (e m)) * Csrc := by
            have hLp := Real.Lp_add_le_tsum_of_nonneg'
              (ι := ℤ)
              (p := q.toReal)
              hq_one
              (f := fun j : ℤ => part N j)
              (g := fun j : ℤ => a (e N) * srcZ (j - e N))
              (fun j => hpart_nonneg N j)
              hterm_nonneg
              ih_sum
              (hterm_q_summable (e N))
            have hrhs :
                (∑' j : ℤ, part N j ^ q.toReal) ^ (1 / q.toReal) +
                    (∑' j : ℤ, (a (e N) * srcZ (j - e N)) ^ q.toReal) ^ (1 / q.toReal)
                  ≤ (∑ m ∈ Finset.range (N + 1), a (e m)) * Csrc := by
              calc
                (∑' j : ℤ, part N j ^ q.toReal) ^ (1 / q.toReal) +
                    (∑' j : ℤ, (a (e N) * srcZ (j - e N)) ^ q.toReal) ^ (1 / q.toReal)
                    ≤ (∑ m ∈ Finset.range N, a (e m)) * Csrc + a (e N) * Csrc :=
                      add_le_add ih_bound (hterm_norm (e N))
                _ = (∑ m ∈ Finset.range (N + 1), a (e m)) * Csrc := by
                    rw [Finset.sum_range_succ]
                    ring
            exact (by
              simpa [part, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using
                hLp.trans hrhs)
          exact ⟨hsum_succ, hbound_succ⟩
      have hpart_tendsto : ∀ j : ℤ, Tendsto (fun N : ℕ => part N j) atTop (𝓝 (convZ j)) := by
        intro j
        let termj : ℕ → ℝ := fun m => a (e m) * srcZ (j - e m)
        have htermj_sum : Summable termj := by
          refine Summable.of_nonneg_of_le
            (fun m => mul_nonneg (ha_nonneg _) (hsrcZ_nonneg _))
            (fun m => ?_)
            (ha_sum_nat.mul_right Csrc)
          exact mul_le_mul_of_nonneg_left (hsrcZ_le_Csrc _) (ha_nonneg _)
        have htermj_tsum : (∑' m : ℕ, termj m) = convZ j := by
          calc
            (∑' m : ℕ, termj m) = ∑' n : ℤ, a n * srcZ (j - n) := by
              simpa [termj, e] using (e.tsum_eq (fun n : ℤ => a n * srcZ (j - n)))
            _ = convZ j := by rfl
        have hsumj := htermj_sum.hasSum
        rw [htermj_tsum] at hsumj
        simpa [part, termj] using hsumj.tendsto_sum_nat
      have hfinite_bound : ∀ T : Finset ℤ,
          ∑ j ∈ T, convZ j ^ q.toReal ≤
            ((LpGridRepresentation.cCoefficientInt p ∞ bZ) * Csrc) ^ q.toReal := by
        intro T
        let u : ℕ → ℝ := fun N => ∑ j ∈ T, part N j ^ q.toReal
        have hu_tendsto : Tendsto u atTop (𝓝 (∑ j ∈ T, convZ j ^ q.toReal)) := by
          refine tendsto_finsetSum T ?_
          intro j hj
          exact (Real.continuousAt_rpow_const (x := convZ j) (q := q.toReal) (Or.inr hq_pos.le)).tendsto.comp (hpart_tendsto j)
        have hu_bound : ∀ N : ℕ,
            u N ≤ ((LpGridRepresentation.cCoefficientInt p ∞ bZ) * Csrc) ^ q.toReal := by
          intro N
          rcases hpart_bound N with ⟨hsumN, hboundN⟩
          have hsum_le : u N ≤ ∑' j : ℤ, part N j ^ q.toReal :=
            hsumN.sum_le_tsum T (fun j hj => Real.rpow_nonneg (hpart_nonneg N j) _)
          have hnorm_le :
              (∑' j : ℤ, part N j ^ q.toReal) ^ (1 / q.toReal) ≤
                (LpGridRepresentation.cCoefficientInt p ∞ bZ) * Csrc := by
            calc
              (∑' j : ℤ, part N j ^ q.toReal) ^ (1 / q.toReal)
                  ≤ (∑ m ∈ Finset.range N, a (e m)) * Csrc := hboundN
              _ ≤ (∑' m : ℕ, a (e m)) * Csrc := by
                    exact mul_le_mul_of_nonneg_right
                      (ha_sum_nat.sum_le_tsum (Finset.range N) (fun m hm => ha_nonneg _))
                      hCsrc_nonneg
              _ = (LpGridRepresentation.cCoefficientInt p ∞ bZ) * Csrc := by rw [ha_tsum_eq]
          have hpow_le :
              ∑' j : ℤ, part N j ^ q.toReal ≤
                ((LpGridRepresentation.cCoefficientInt p ∞ bZ) * Csrc) ^ q.toReal := by
            have hpow' :
                ((∑' j : ℤ, part N j ^ q.toReal) ^ (1 / q.toReal)) ^ q.toReal ≤
                  ((LpGridRepresentation.cCoefficientInt p ∞ bZ) * Csrc) ^ q.toReal :=
              Real.rpow_le_rpow
                (Real.rpow_nonneg (tsum_nonneg fun j => Real.rpow_nonneg (hpart_nonneg N j) _) _)
                hnorm_le
                hq_pos.le
            calc
              ∑' j : ℤ, part N j ^ q.toReal
                  = ((∑' j : ℤ, part N j ^ q.toReal) ^ (1 / q.toReal)) ^ q.toReal := by
                      symm
                      rw [← Real.rpow_mul (tsum_nonneg fun j => Real.rpow_nonneg (hpart_nonneg N j) _)]
                      field_simp [hq_pos.ne']
                      rw [Real.rpow_one]
              _ ≤ ((LpGridRepresentation.cCoefficientInt p ∞ bZ) * Csrc) ^ q.toReal := hpow'
          exact hsum_le.trans hpow_le
        exact le_of_tendsto' hu_tendsto hu_bound
      have hconvZ_q_summable : Summable (fun j : ℤ => convZ j ^ q.toReal) :=
        summable_of_sum_le
          (fun j => Real.rpow_nonneg (hconvZ_nonneg j) _)
          hfinite_bound
      have htsum_le :
          ∑' j : ℤ, convZ j ^ q.toReal ≤
            ((LpGridRepresentation.cCoefficientInt p ∞ bZ) * Csrc) ^ q.toReal :=
        Real.tsum_le_of_sum_le
          (fun j => Real.rpow_nonneg (hconvZ_nonneg j) _)
          hfinite_bound
      refine ⟨hconvZ_q_summable, ?_⟩
      have hroot := Real.rpow_le_rpow
        (tsum_nonneg fun j => Real.rpow_nonneg (hconvZ_nonneg j) _)
        htsum_le
        (div_nonneg zero_le_one hq_pos.le)
      calc
        (∑' j : ℤ, convZ j ^ q.toReal) ^ (1 / q.toReal)
            ≤ (((LpGridRepresentation.cCoefficientInt p ∞ bZ) * Csrc) ^ q.toReal) ^ (1 / q.toReal) := hroot
        _ = LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc := by
              rw [← Real.rpow_mul (mul_nonneg hccoeff_nonneg hCsrc_nonneg)]
              field_simp [hq_pos.ne']
              rw [Real.rpow_one]
    have hconvZ_nat_summable : Summable fun j : ℕ => convZ j ^ q.toReal := by
      exact hYoungZ.1.comp_injective (by
        intro a b h
        exact_mod_cast h)
    have hscaled_convZ_nat_summable :
        Summable fun j : ℕ => (scale * convZ j) ^ q.toReal := by
      have hmul : Summable fun j : ℕ => scale ^ q.toReal * convZ j ^ q.toReal :=
        hconvZ_nat_summable.mul_left (scale ^ q.toReal)
      convert hmul using 1
      ext j
      rw [Real.mul_rpow hscale_nonneg (hconvZ_nonneg j)]
    have hclass_summable : ∀ ell : Fin alpha,
        Summable fun j : ℕ => classConv ell j ^ q.toReal := by
      intro ell
      refine Summable.of_nonneg_of_le
        (fun j => Real.rpow_nonneg (hclassConv_nonneg ell j) _)
        ?_
        hscaled_convZ_nat_summable
      intro j
      exact Real.rpow_le_rpow
        (hclassConv_nonneg ell j)
        (hclass_le_convZ ell j)
        hq_pos.le
    have hsigma_summable :
        Summable (fun x : (Sigma fun _ell : Fin alpha => ℕ) =>
          classConv x.1 x.2 ^ q.toReal) := by
      refine (summable_sigma_of_nonneg
        (f := fun x : (Sigma fun _ell : Fin alpha => ℕ) =>
          classConv x.1 x.2 ^ q.toReal)
        (fun x => Real.rpow_nonneg (hclassConv_nonneg x.1 x.2) _)).2 ?_
      constructor
      · exact hclass_summable
      · exact summable_of_hasFiniteSupport
          (Set.finite_univ.subset (by intro x hx; simp))
    refine ⟨hsigma_summable, ?_⟩
    have hconvZ_nat_le :
        (∑' j : ℕ, convZ j ^ q.toReal) ^ (1 / q.toReal) ≤
          (∑' j : ℤ, convZ j ^ q.toReal) ^ (1 / q.toReal) := by
      have hsum_le :
          (∑' j : ℕ, convZ j ^ q.toReal) ≤ ∑' j : ℤ, convZ j ^ q.toReal := by
        exact tsum_comp_le_tsum_of_injective
          hYoungZ.1
          (fun z => Real.rpow_nonneg (hconvZ_nonneg z) _)
          (phi := fun j : ℕ => (j : ℤ))
          (by
            intro a b h
            exact Int.ofNat.inj h)
      exact Real.rpow_le_rpow
        (tsum_nonneg fun j => Real.rpow_nonneg (hconvZ_nonneg j) _)
        hsum_le
        (div_nonneg zero_le_one hq_pos.le)
    have hscaled_convZ_norm_le :
        (∑' j : ℕ, (scale * convZ j) ^ q.toReal) ^ (1 / q.toReal) ≤
          scale * (LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc) := by
      have hscaled_tsum :
          (∑' j : ℕ, (scale * convZ j) ^ q.toReal) =
            scale ^ q.toReal * ∑' j : ℕ, convZ j ^ q.toReal := by
        calc
          (∑' j : ℕ, (scale * convZ j) ^ q.toReal)
              = ∑' j : ℕ, scale ^ q.toReal * convZ j ^ q.toReal := by
                  apply tsum_congr
                  intro j
                  rw [Real.mul_rpow hscale_nonneg (hconvZ_nonneg j)]
          _ = scale ^ q.toReal * ∑' j : ℕ, convZ j ^ q.toReal := by
                simpa [mul_assoc] using
                  (hconvZ_nat_summable.hasSum.mul_left (scale ^ q.toReal)).tsum_eq
      calc
        (∑' j : ℕ, (scale * convZ j) ^ q.toReal) ^ (1 / q.toReal)
            = (scale ^ q.toReal * ∑' j : ℕ, convZ j ^ q.toReal) ^ (1 / q.toReal) := by
                rw [hscaled_tsum]
        _ = scale * (∑' j : ℕ, convZ j ^ q.toReal) ^ (1 / q.toReal) := by
              have hmul_rpow :
                  (scale ^ q.toReal * ∑' j : ℕ, convZ j ^ q.toReal) ^ (1 / q.toReal) =
                    (scale ^ q.toReal) ^ (1 / q.toReal) *
                      (∑' j : ℕ, convZ j ^ q.toReal) ^ (1 / q.toReal) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  (Real.mul_rpow (Real.rpow_nonneg hscale_nonneg _)
                    (tsum_nonneg fun j => Real.rpow_nonneg (hconvZ_nonneg j) _)
                    (x := scale ^ q.toReal)
                    (y := ∑' j : ℕ, convZ j ^ q.toReal)
                    (z := 1 / q.toReal))
              rw [hmul_rpow]
              rw [← Real.rpow_mul hscale_nonneg]
              field_simp [hq_pos.ne']
              rw [Real.rpow_one, mul_comm]
        _ ≤ scale * (∑' j : ℤ, convZ j ^ q.toReal) ^ (1 / q.toReal) := by
              exact mul_le_mul_of_nonneg_left hconvZ_nat_le hscale_nonneg
        _ ≤ scale * (LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc) := by
              exact mul_le_mul_of_nonneg_left hYoungZ.2 hscale_nonneg
    have hclass_norm_le : ∀ ell : Fin alpha,
        (∑' j : ℕ, classConv ell j ^ q.toReal) ^ (1 / q.toReal) ≤
          scale * (LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc) := by
      intro ell
      have hsum_le :
          (∑' j : ℕ, classConv ell j ^ q.toReal) ≤
            ∑' j : ℕ, (scale * convZ j) ^ q.toReal := by
        exact (hclass_summable ell).tsum_le_tsum
          (fun j =>
            Real.rpow_le_rpow
              (hclassConv_nonneg ell j)
              (hclass_le_convZ ell j)
              hq_pos.le)
          hscaled_convZ_nat_summable
      have hroot_le :
          (∑' j : ℕ, classConv ell j ^ q.toReal) ^ (1 / q.toReal) ≤
            (∑' j : ℕ, (scale * convZ j) ^ q.toReal) ^ (1 / q.toReal) := by
        exact Real.rpow_le_rpow
          (tsum_nonneg fun j => Real.rpow_nonneg (hclassConv_nonneg ell j) _)
          hsum_le
          (div_nonneg zero_le_one hq_pos.le)
      exact hroot_le.trans hscaled_convZ_norm_le
    have hclass_bound_nonneg :
        0 ≤ scale * (LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc) := by
      exact mul_nonneg hscale_nonneg (mul_nonneg hccoeff_nonneg hCsrc_nonneg)
    have hsigma_eq :
        (∑' x : (Sigma fun _ell : Fin alpha => ℕ), classConv x.1 x.2 ^ q.toReal) =
          ∑ ell : Fin alpha, (((∑' j : ℕ, classConv ell j ^ q.toReal) ^ (1 / q.toReal)) ^ q.toReal) := by
      rw [hsigma_summable.tsum_sigma, tsum_fintype]
      refine Finset.sum_congr rfl ?_
      intro ell hEll
      symm
      rw [← Real.rpow_mul
        (tsum_nonneg fun j => Real.rpow_nonneg (hclassConv_nonneg ell j) _)]
      field_simp [hq_pos.ne']
      rw [Real.rpow_one]
    calc
      (∑' x : (Sigma fun _ell : Fin alpha => ℕ), classConv x.1 x.2 ^ q.toReal) ^
          (1 / q.toReal)
          = (∑ ell : Fin alpha,
              (((∑' j : ℕ, classConv ell j ^ q.toReal) ^ (1 / q.toReal)) ^ q.toReal)) ^
              (1 / q.toReal) := by
                rw [hsigma_eq]
      _ ≤ (alpha : ℝ) ^ (1 / q.toReal) *
            (scale * (LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc)) := by
            simpa using
              finset_Lq_le_card_rpow_mul_bound (q := q)
                (S := (Finset.univ : Finset (Fin alpha)))
                (a := fun ell => (∑' j : ℕ, classConv ell j ^ q.toReal) ^ (1 / q.toReal))
                (scale * (LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc))
                (fun ell hEll =>
                  Real.rpow_nonneg
                    (tsum_nonneg fun j => Real.rpow_nonneg (hclassConv_nonneg ell j) _) _)
                (fun ell hEll => hclass_norm_le ell)
                hclass_bound_nonneg
                hq_ne_top
      _ = scale * LpGridRepresentation.cCoefficientInt p ∞ bZ *
            (alpha : ℝ) ^ (1 / q.toReal) * Csrc := by
            ring
  have hconv_summable : Summable (fun j : ℕ => convL j ^ q.toReal) := by
    have hsComp :
        Summable (fun j : ℕ =>
          (fun x : (Sigma fun _ell : Fin alpha => ℕ) =>
            classConv x.1 x.2 ^ q.toReal) (kclass j)) :=
      hclassYoung.1.comp_injective hkclass_injective
    simpa [hclassConv_kclass] using hsComp
  have hsum_root_le :
      (∑' j : ℕ, convL j ^ q.toReal) ^ (1 / q.toReal) ≤
        (∑' x : (Sigma fun _ell : Fin alpha => ℕ),
          classConv x.1 x.2 ^ q.toReal) ^ (1 / q.toReal) := by
    exact Real.rpow_le_rpow
      (tsum_nonneg fun j => Real.rpow_nonneg (hconvL_nn j) _)
      (htsum_le_classSigma hclassYoung.1)
      (div_nonneg zero_le_one hq_pos.le)
  constructor
  · exact hconv_summable
  · simpa [Csrc, bZ, alpha, convL, one_div] using hsum_root_le.trans hclassYoung.2

/-- Endpoint `q = ∞` version of the convolution estimate used in Claim II.

The source sequence is controlled in `ℓ∞`, while the integer kernel is used in
`ℓ¹`; hence the target convolution is uniformly bounded. -/
lemma transmutation_convolution_bound_top
    (k : ℕ → ℕ)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (A_als B_als r_als : ℝ) (hr_als : 0 < r_als)
    (hk_upper : ∀ i : ℕ, (k i : NNReal) ≤ r_als * (i : NNReal) + B_als)
    (hk_lower : ∀ i : ℕ, r_als * (i : NNReal) + A_als ≤ k i)
    (vL : ℕ → ℝ)
    (hvL_nn : ∀ i, 0 ≤ vL i)
    (hsource : BddAbove (Set.range fun i => vL i ^ (1 / p.toReal)))
    (hp_ne_top : p ≠ ∞) :
    BddAbove (Set.range fun j =>
      ∑' i, if k i ≤ j then
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (vL i) ^ (1 / p.toReal) else 0) ∧
    sSup (Set.range fun j =>
      ∑' i, if k i ≤ j then
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) *
          (vL i) ^ (1 / p.toReal) else 0) ≤
      lam ^ (-(B_als : ℝ) / p.toReal) *
      LpGridRepresentation.cCoefficientInt p ∞
        (transmutationKernelZ lam A_als r_als) *
      sSup (Set.range fun i => vL i ^ (1 / p.toReal)) := by
  classical
  let alpha : ℕ := Nat.ceil (r_als : ℝ)
  let bZ : ℤ → ℝ := transmutationKernelZ lam A_als r_als
  let convL : ℕ → ℝ := fun j =>
    ∑' i, if k i ≤ j then
      lam ^ ((↑(j - k i) : ℝ) / p.toReal) * (vL i) ^ (1 / p.toReal) else 0
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos
      (fun h0 => absurd (h0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)) (by norm_num))
      hp_ne_top
  have halpha_pos : 0 < alpha := by
    have hr_pos_real : 0 < (r_als : ℝ) := by exact_mod_cast hr_als
    exact Nat.ceil_pos.mpr hr_pos_real
  have hbZ_nonneg : ∀ n, 0 ≤ bZ n := by
    intro n
    dsimp [bZ, transmutationKernelZ]
    split_ifs
    · exact Real.rpow_nonneg hlam_pos.le _
    · exact le_rfl
  have hconvL_nn : ∀ j, 0 ≤ convL j := by
    intro j
    exact tsum_nonneg fun i => by
      split_ifs with hij
      · exact mul_nonneg (Real.rpow_nonneg hlam_pos.le _) (Real.rpow_nonneg (hvL_nn i) _)
      · exact le_rfl
  have hccoeff_nonneg : 0 ≤ LpGridRepresentation.cCoefficientInt p ∞ bZ :=
    LpGridRepresentation.cCoefficientInt_nonneg p ∞ bZ hbZ_nonneg
  have hccoeff_eq :
      LpGridRepresentation.cCoefficientInt p ∞ bZ =
        ∑' n : ℤ, bZ n ^ (1 / p.toReal) := by
    simp [LpGridRepresentation.cCoefficientInt, bZ]
  let srcRoot : ℕ → ℝ := fun i => vL i ^ (1 / p.toReal)
  let Csrc : ℝ := sSup (Set.range srcRoot)
  have hCsrc_nonneg : 0 ≤ Csrc := by
    exact Real.sSup_nonneg' ⟨_, ⟨0, rfl⟩, Real.rpow_nonneg (hvL_nn 0) _⟩
  have hsrcRoot_le_Csrc : ∀ i, srcRoot i ≤ Csrc := by
    intro i
    exact le_csSup (by simpa [srcRoot] using hsource) ⟨i, rfl⟩
  let srcZ : ℤ → ℝ := extendNatToInt srcRoot
  let convZ : ℤ → ℝ := fun j =>
    ∑' n : ℤ, bZ n ^ (1 / p.toReal) * srcZ (j - n)
  have hbRoot_summable : Summable fun n : ℤ => bZ n ^ (1 / p.toReal) := by
    simpa [bZ] using
      transmutationKernelZ_root_summable (p := p)
        lam A_als r_als hlam_pos hlam_lt hr_als hp_pos
  have hbRoot_nonneg : ∀ n : ℤ, 0 ≤ bZ n ^ (1 / p.toReal) := by
    intro n
    exact Real.rpow_nonneg (hbZ_nonneg n) _
  have hsrcRoot_nonneg : ∀ i : ℕ, 0 ≤ srcRoot i := by
    intro i
    exact Real.rpow_nonneg (hvL_nn i) _
  have hsrcZ_nonneg : ∀ z : ℤ, 0 ≤ srcZ z := by
    simpa [srcZ] using extendNatToInt_nonneg hsrcRoot_nonneg
  have hsrcZ_le_Csrc : ∀ z : ℤ, srcZ z ≤ Csrc := by
    intro z
    by_cases hz : 0 ≤ z
    · dsimp [srcZ, extendNatToInt]
      rw [if_pos hz]
      exact hsrcRoot_le_Csrc z.toNat
    · dsimp [srcZ, extendNatToInt]
      rw [if_neg hz]
      exact hCsrc_nonneg
  have hconvZ_nonneg : ∀ j : ℤ, 0 ≤ convZ j := by
    intro j
    dsimp [convZ]
    exact tsum_nonneg fun n => mul_nonneg (hbRoot_nonneg n) (hsrcZ_nonneg (j - n))
  have hconvZ_le : ∀ j : ℤ,
      convZ j ≤ LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc := by
    intro j
    let a : ℤ → ℝ := fun n => bZ n ^ (1 / p.toReal)
    let term : ℤ → ℝ := fun n => a n * srcZ (j - n)
    have ha_nonneg : ∀ n, 0 ≤ a n := by
      intro n
      exact hbRoot_nonneg n
    have hterm_nonneg : ∀ n, 0 ≤ term n := by
      intro n
      exact mul_nonneg (ha_nonneg n) (hsrcZ_nonneg (j - n))
    have hterm_le : ∀ n, term n ≤ a n * Csrc := by
      intro n
      exact mul_le_mul_of_nonneg_left (hsrcZ_le_Csrc (j - n)) (ha_nonneg n)
    have hterm_sum : Summable term := by
      refine Summable.of_nonneg_of_le hterm_nonneg hterm_le ?_
      exact (by simpa [a, term, mul_comm, mul_left_comm, mul_assoc] using
        (hbRoot_summable.mul_right Csrc))
    have hscaled_sum : Summable (fun n : ℤ => a n * Csrc) := by
      simpa [a] using hbRoot_summable.mul_right Csrc
    have hscaled_tsum :
        (∑' n : ℤ, a n * Csrc) =
          LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc := by
      have ha_summable : Summable a := by
        simpa [a] using hbRoot_summable
      calc
        (∑' n : ℤ, a n * Csrc) = (∑' n : ℤ, a n) * Csrc := by
          simpa using (ha_summable.hasSum.mul_right Csrc).tsum_eq
        _ = LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc := by
          rw [hccoeff_eq]
    calc
      convZ j = ∑' n : ℤ, term n := by rfl
      _ ≤ ∑' n : ℤ, a n * Csrc := hterm_sum.tsum_le_tsum hterm_le hscaled_sum
      _ = LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc := hscaled_tsum
  let scale : ℝ := lam ^ (-(B_als : ℝ) / p.toReal)
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    exact Real.rpow_nonneg hlam_pos.le _
  let kout : Fin alpha → ℕ → ℕ :=
    fun ell j => Nat.ceil ((r_als : ℝ) * (j : ℝ) + (ell.1 : ℝ))
  let koutExists : Fin alpha → ℕ → Prop :=
    fun ell j => ((kout ell j : ℕ) : ℝ) < (r_als : ℝ) * ((j + 1 : ℕ) : ℝ)
  have hkout_lower : ∀ ell : Fin alpha, ∀ j : ℕ,
      (r_als : ℝ) * (j : ℝ) + (ell.1 : ℝ) ≤ (kout ell j : ℕ) := by
    intro ell j
    exact Nat.le_ceil _
  have hkout_lt_add_one : ∀ ell : Fin alpha, ∀ j : ℕ,
      ((kout ell j : ℕ) : ℝ) < (r_als : ℝ) * (j : ℝ) + (ell.1 : ℝ) + 1 := by
    intro ell j
    apply Nat.ceil_lt_add_one
    positivity
  let kclass : ℕ → Sigma fun _ell : Fin alpha => ℕ := fun j =>
    ⟨⟨outputClassEll r_als j, by
        have hspec := (outputClass_spec r_als hr_als j).1
        simpa [alpha] using hspec⟩, outputClassJ r_als j⟩
  have hkclass_kout : ∀ j : ℕ, kout (kclass j).1 (kclass j).2 = j := by
    intro j
    have hspec := (outputClass_spec r_als hr_als j).2.1
    simpa [kclass, kout] using hspec
  have hkclass_exists : ∀ j : ℕ, koutExists (kclass j).1 (kclass j).2 := by
    intro j
    have hspec := (outputClass_spec r_als hr_als j).2.2
    dsimp [koutExists]
    rw [hkclass_kout j]
    simpa [kclass] using hspec
  let classConv : Fin alpha → ℕ → ℝ := fun ell j =>
    if koutExists ell j then convL (kout ell j) else 0
  have hclassConv_kclass : ∀ j : ℕ,
      classConv (kclass j).1 (kclass j).2 = convL j := by
    intro j
    dsimp [classConv]
    rw [if_pos (hkclass_exists j), hkclass_kout j]
  have hclass_le_convZ : ∀ ell : Fin alpha, ∀ j : ℕ,
      classConv ell j ≤ scale * convZ j := by
    intro ell j
    dsimp [classConv]
    by_cases hEx : koutExists ell j
    · rw [if_pos hEx]
      let f : ℕ → ℝ := fun i =>
        if k i ≤ kout ell j then
          lam ^ ((↑(kout ell j - k i) : ℝ) / p.toReal) * srcRoot i
        else 0
      let sec : ℤ → ℝ := fun n =>
        bZ n ^ (1 / p.toReal) * srcZ ((j : ℤ) - n)
      have hf_nonneg : ∀ i, 0 ≤ f i := by
        intro i
        dsimp [f]
        split_ifs with hik
        · exact mul_nonneg (Real.rpow_nonneg hlam_pos.le _) (hsrcRoot_nonneg i)
        · exact le_rfl
      have hf_support : Function.support f ⊆ {i : ℕ | k i ≤ kout ell j} := by
        intro i hi
        by_contra hik
        have hik' : ¬ k i ≤ kout ell j := by simpa using hik
        have : f i = 0 := by simp [f, hik']
        exact hi this
      have hf_sum : Summable f :=
        summable_of_hasFiniteSupport
          ((almostLinearSequence_finite_le_level
            ⟨A_als, B_als, r_als, hr_als, fun i => ⟨hk_upper i, hk_lower i⟩⟩
            (kout ell j)).subset hf_support)
      have hconv_eq : convL (kout ell j) = ∑' i, f i := by
        simp [convL, f, srcRoot]
      rw [hconv_eq]
      have hsec_nonneg : ∀ n : ℤ, 0 ≤ sec n := by
        intro n
        dsimp [sec]
        exact mul_nonneg (hbRoot_nonneg n) (hsrcZ_nonneg ((j : ℤ) - n))
      let M : ℕ := Nat.ceil (max (0 : ℝ) (-A_als / r_als))
      have hsec_support : Function.support sec ⊆ Set.Icc (-(M : ℤ)) j := by
        intro n hn
        simp only [Function.mem_support, ne_eq] at hn
        constructor
        · by_contra hnlow
          have hsucc : n + 1 ≤ -(M : ℤ) := by omega
          have hsucc_real : (n : ℝ) + 1 ≤ -((M : ℝ)) := by exact_mod_cast hsucc
          have hceil_ge : max (0 : ℝ) (-A_als / r_als) ≤ (M : ℝ) := by
            dsimp [M]
            exact Nat.le_ceil _
          have hneg_bound : -((M : ℝ)) ≤ A_als / r_als := by
            have hA_bound : -A_als / r_als ≤ (M : ℝ) :=
              (le_max_right (0 : ℝ) (-A_als / r_als)).trans hceil_ge
            convert neg_le_neg hA_bound using 1 <;> ring
          have hcut_not : ¬ A_als / r_als - 1 < (n : ℝ) := by
            have hle : (n : ℝ) + 1 ≤ A_als / r_als := hsucc_real.trans hneg_bound
            linarith
          have hb_zero : bZ n = 0 := by
            dsimp [bZ, transmutationKernelZ]
            simp [hcut_not]
          have hb_root_zero : bZ n ^ (1 / p.toReal) = 0 := by
            rw [hb_zero, Real.zero_rpow (one_div_pos.mpr hp_pos).ne']
          have hsec_zero : sec n = 0 := by
            rw [show sec n = bZ n ^ (1 / p.toReal) * srcZ ((j : ℤ) - n) by rfl,
              hb_root_zero]
            ring
          exact hn hsec_zero
        · by_contra hnj
          have hneg : ¬ 0 ≤ (j : ℤ) - n := by omega
          have hsrc_zero : srcZ ((j : ℤ) - n) = 0 := by
            dsimp [srcZ, extendNatToInt]
            rw [if_neg hneg]
          have hsec_zero : sec n = 0 := by
            rw [show sec n = bZ n ^ (1 / p.toReal) * srcZ ((j : ℤ) - n) by rfl,
              hsrc_zero]
            ring
          exact hn hsec_zero
      have hsec_sum : Summable sec :=
        summable_of_hasFiniteSupport ((Set.finite_Icc (-(M : ℤ)) j).subset hsec_support)
      have hphi_inj : Function.Injective (fun i : ℕ => (j : ℤ) - i) := by
        intro a b hab
        have : (a : ℤ) = b := by linarith
        exact_mod_cast this
      have hterm_le : ∀ i : ℕ, f i ≤ scale * sec ((j : ℤ) - i) := by
        intro i
        by_cases hik : k i ≤ kout ell j
        · have hk_upper_real : (k i : ℝ) ≤ r_als * (i : ℝ) + B_als := by
            exact_mod_cast hk_upper i
          have hk_le_real : (k i : ℝ) ≤ (kout ell j : ℝ) := by
            exact_mod_cast hik
          have hkout_ge_j : r_als * (j : ℝ) ≤ (kout ell j : ℝ) := by
            have hell_nonneg : 0 ≤ (ell.1 : ℝ) := by positivity
            linarith [hkout_lower ell j]
          have hlag_cut_real : A_als / r_als - 1 < (j : ℝ) - (i : ℝ) := by
            have hk_lower_real : r_als * (i : ℝ) + A_als ≤ (k i : ℝ) := by
              exact_mod_cast hk_lower i
            have hkout_lt : (kout ell j : ℝ) < r_als * ((j + 1 : ℕ) : ℝ) := by
              simpa [koutExists] using hEx
            have hklt : (k i : ℝ) < r_als * ((j + 1 : ℕ) : ℝ) :=
              lt_of_le_of_lt hk_le_real hkout_lt
            have hlt : A_als < r_als * (((j : ℝ) + 1) - (i : ℝ)) := by
              have hmid : r_als * (i : ℝ) + A_als < r_als * ((j + 1 : ℕ) : ℝ) :=
                lt_of_le_of_lt hk_lower_real hklt
              have hrew :
                  r_als * (((j : ℝ) + 1) - (i : ℝ)) =
                    r_als * ((j + 1 : ℕ) : ℝ) - r_als * (i : ℝ) := by
                calc
                  r_als * (((j : ℝ) + 1) - (i : ℝ))
                      = r_als * ((j : ℝ) + 1) - r_als * (i : ℝ) := by ring
                  _ = r_als * ((j + 1 : ℕ) : ℝ) - r_als * (i : ℝ) := by
                    norm_num [Nat.cast_add]
              rw [hrew]
              linarith
            have hdiv : A_als / r_als < ((j : ℝ) + 1) - (i : ℝ) := by
              rw [div_lt_iff₀ hr_als]
              simpa [mul_comm, mul_left_comm, mul_assoc] using hlt
            linarith
          have hlag_cut : A_als / r_als - 1 < ((((j : ℤ) - i : ℤ) : ℝ)) := by
            have hcast : ((((j : ℤ) - i : ℤ) : ℝ)) = (j : ℝ) - (i : ℝ) := by
              norm_num
            simpa [hcast] using hlag_cut_real
          have hb_eq :
              bZ ((j : ℤ) - i) = lam ^ (r_als * ((((j : ℤ) - i : ℤ) : ℝ))) := by
            dsimp [bZ, transmutationKernelZ]
            rw [if_pos hlag_cut]
          have hb_root_eq :
              bZ ((j : ℤ) - i) ^ (1 / p.toReal) =
                lam ^ ((r_als * ((((j : ℤ) - i : ℤ) : ℝ))) / p.toReal) := by
            rw [hb_eq, ← Real.rpow_mul hlam_pos.le]
            congr 1
            ring
          have hlag_exp :
              (r_als * ((((j : ℤ) - i : ℤ) : ℝ)) - B_als) / p.toReal ≤
                ((↑(kout ell j - k i) : ℝ) / p.toReal) := by
            rw [Nat.cast_sub hik]
            have hcast : ((((j : ℤ) - i : ℤ) : ℝ)) = (j : ℝ) - (i : ℝ) := by
              norm_num
            rw [hcast]
            field_simp [hp_pos.ne']
            linarith
          have hlam_le :
              lam ^ ((↑(kout ell j - k i) : ℝ) / p.toReal) ≤
                scale * bZ ((j : ℤ) - i) ^ (1 / p.toReal) := by
            calc
              lam ^ ((↑(kout ell j - k i) : ℝ) / p.toReal)
                  ≤ lam ^ ((r_als * ((((j : ℤ) - i : ℤ) : ℝ)) - B_als) / p.toReal) := by
                    exact Real.rpow_le_rpow_of_exponent_ge hlam_pos hlam_lt.le hlag_exp
              _ = scale * bZ ((j : ℤ) - i) ^ (1 / p.toReal) := by
                  rw [hb_root_eq]
                  have hexp :
                      ((r_als * ((((j : ℤ) - i : ℤ) : ℝ)) - B_als) / p.toReal) =
                        -(B_als : ℝ) / p.toReal +
                          (r_als * ((((j : ℤ) - i : ℤ) : ℝ)) / p.toReal) := by
                    field_simp [hp_pos.ne']
                    ring
                  rw [hexp, ← Real.rpow_add hlam_pos]
          have hsrc_eq : srcZ ((j : ℤ) - ((j : ℤ) - i)) = srcRoot i := by
            have hsub : (j : ℤ) - ((j : ℤ) - i) = i := by ring
            rw [hsub]
            simpa [srcZ] using extendNatToInt_ofNat srcRoot i
          calc
            f i = lam ^ ((↑(kout ell j - k i) : ℝ) / p.toReal) * srcRoot i := by
              simp [f, hik]
            _ ≤ (scale * bZ ((j : ℤ) - i) ^ (1 / p.toReal)) * srcRoot i := by
              exact mul_le_mul_of_nonneg_right hlam_le (hsrcRoot_nonneg i)
            _ = scale * sec ((j : ℤ) - i) := by
              rw [show sec ((j : ℤ) - i) =
                  bZ ((j : ℤ) - i) ^ (1 / p.toReal) *
                    srcZ ((j : ℤ) - ((j : ℤ) - i)) by rfl,
                hsrc_eq]
              ring
        · have hnonneg : 0 ≤ scale * sec ((j : ℤ) - i) := by
            exact mul_nonneg hscale_nonneg (hsec_nonneg ((j : ℤ) - i))
          simpa [f, hik] using hnonneg
      have hsum_comp : Summable fun i : ℕ => scale * sec ((j : ℤ) - i) :=
        (hsec_sum.mul_left scale).comp_injective hphi_inj
      have hsum_le : (∑' i : ℕ, f i) ≤ ∑' i : ℕ, scale * sec ((j : ℤ) - i) :=
        hf_sum.tsum_le_tsum hterm_le hsum_comp
      have hsum_reindex :
          (∑' i : ℕ, scale * sec ((j : ℤ) - i)) ≤ ∑' n : ℤ, scale * sec n := by
        exact tsum_comp_le_tsum_of_injective
          ((hsec_sum.mul_left scale))
          (fun n => mul_nonneg hscale_nonneg (hsec_nonneg n))
          hphi_inj
      have htsum_scale : (∑' n : ℤ, scale * sec n) = scale * convZ j := by
        calc
          (∑' n : ℤ, scale * sec n) = scale * ∑' n : ℤ, sec n := by
            simpa [sec, mul_assoc] using (hsec_sum.hasSum.mul_left scale).tsum_eq
          _ = scale * convZ j := by rfl
      exact (hsum_le.trans hsum_reindex).trans_eq htsum_scale
    · have hnonneg : 0 ≤ scale * convZ j := mul_nonneg hscale_nonneg (hconvZ_nonneg j)
      simpa [hEx] using hnonneg
  have hconv_bound : ∀ j : ℕ,
      convL j ≤
        scale * (LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc) := by
    intro j
    have hclass := hclass_le_convZ (kclass j).1 (kclass j).2
    rw [hclassConv_kclass j] at hclass
    exact hclass.trans
      (mul_le_mul_of_nonneg_left (hconvZ_le (kclass j).2) hscale_nonneg)
  have hbdd : BddAbove (Set.range convL) := by
    refine ⟨scale * (LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc), ?_⟩
    rintro x ⟨j, rfl⟩
    exact hconv_bound j
  constructor
  · simpa [convL] using hbdd
  · have hsup_le :
        sSup (Set.range convL) ≤
          scale * (LpGridRepresentation.cCoefficientInt p ∞ bZ * Csrc) := by
      apply csSup_le (Set.range_nonempty _)
      rintro x ⟨j, rfl⟩
      exact hconv_bound j
    simpa [scale, Csrc, srcRoot, bZ, convL, mul_assoc] using hsup_le

/-- The transmutation blocks have finite abstract `(p,q)` cost.

This lemma is the bridge from the coefficient estimates of Claim II to the
abstract summability machinery for block sequences.  It says that the level
blocks produced by transmutation are controlled by a summable majorant, hence
form an admissible block family in the target Besov-type space.

Conceptually, the proof has only two inputs:
1. `transmutation_level_bound`, which controls one target level in terms of the
  convolution sequence;
2. `transmutation_convolution_bound`, which proves that this convolution
  sequence has finite `(p,q)` cost. -/
private lemma transmutationBlock_abstractFinitePQCost
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ) (hk : AlmostLinearSequence k)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k hk lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := q) G c)
    (N : ℕ) (hp_ne_top : p ≠ ∞) (hq_ne_top : q ≠ ∞) :
    AbstractFinitePQCost (q := q) (TransmutationBlock G W AW h R c N) := by
  have hq_pos : (0 : ℝ) < q.toReal :=
    ENNReal.toReal_pos (fun h0 => absurd (h0 ▸ (Fact.out : 1 ≤ q)) (by norm_num)) hq_ne_top
  obtain ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ := hk
  let uL : ℕ → ℝ :=
    fun j => CoeffPLevel (p := p) W
      (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j
  let vL : ℕ → ℝ := fun i => CoeffPLevel (p := p) G c i
  let convL : ℕ → ℝ :=
    fun j => ∑' i, if k i ≤ j then
      lam ^ ((↑(j - k i) : ℝ) / p.toReal) * (vL i) ^ (1 / p.toReal) else 0
  have huL_nn : ∀ j, 0 ≤ uL j := fun j =>
    Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _
  have hvL_nn : ∀ i, 0 ≤ vL i := fun i =>
    Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
  have hconvL_nn : ∀ j, 0 ≤ convL j := fun j =>
    tsum_nonneg fun i => by
      split_ifs
      · exact mul_nonneg (Real.rpow_nonneg hlam_pos.le _) (Real.rpow_nonneg (hvL_nn i) _)
      · exact le_rfl
  have hvL_sum : Summable fun i => vL i ^ (q.toReal / p.toReal) := by
    simpa [CoeffFinitePQCost, hq_ne_top, vL] using hc
  have hk0 : AlmostLinearSequence k := ⟨_, B_als, r_als, hr_als, hk_bound⟩
  have hLevelBound : ∀ j, uL j ^ (1 / p.toReal) ≤
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j := by
    intro j
    simpa [uL, vL, convL] using
      transmutation_level_bound
        G W AW k hk0 lam hlam_pos hlam_lt C hC h R hR c N j hp_ne_top
  have hk_upper : ∀ i : ℕ, (k i : NNReal) ≤ r_als * (i : NNReal) + B_als :=
    fun i => (hk_bound i).1
  have hk_lower : ∀ i : ℕ, r_als * (i : NNReal) + A_als ≤ k i := by
    intro i
    exact_mod_cast (hk_bound i).2
  have hConv :
      Summable (fun j => convL j ^ q.toReal) ∧
      (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) ≤
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
        (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
    simpa [convL] using
      transmutation_convolution_bound
        (p := p) (q := q) k lam hlam_pos hlam_lt A_als B_als r_als hr_als
        hk_upper hk_lower vL hvL_nn hvL_sum hp_ne_top hq_ne_top
  have hterm_le : ∀ j,
      uL j ^ (q.toReal / p.toReal) ≤
      (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
      convL j ^ q.toReal := by
    intro j
    have h1 : uL j ^ (q.toReal / p.toReal) ≤
        ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j) ^ q.toReal := by
      have hmono := Real.rpow_le_rpow
        (Real.rpow_nonneg (huL_nn j) (1 / p.toReal))
        (hLevelBound j) hq_pos.le
      rwa [← Real.rpow_mul (huL_nn j),
           show 1 / p.toReal * q.toReal = q.toReal / p.toReal from by ring] at hmono
    have h2 : ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j) ^ q.toReal =
        (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
        convL j ^ q.toReal := by
      rw [Real.mul_rpow
            (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hC (1 / p.toReal)))
            (hconvL_nn j),
          Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hC (1 / p.toReal)),
          ← Real.rpow_mul hC,
          show 1 / p.toReal * q.toReal = q.toReal / p.toReal from by ring]
    exact h1.trans h2.le
  have huL_sum : Summable (fun j => uL j ^ (q.toReal / p.toReal)) :=
    Summable.of_nonneg_of_le
      (fun j => Real.rpow_nonneg (huL_nn j) _)
      hterm_le
      (hConv.1.mul_left _)
  simp only [AbstractFinitePQCost, hq_ne_top, ↓reduceIte]
  simpa [uL, blockLvlCoeff, CoeffPLevel, TransmutationBlock] using huL_sum

/-- **Claim II**: For every `N : ℕ`, the transmutation level blocks
    `TransmutationBlock G W AW h R c N k` form a `Bˢ_{p,q}(AW)`-representation of
    `PartialSumLevels G W h c N`, and the `(p,q)` coefficient cost satisfies

        pqCost(m_{P,N}) ≤ Cmult1 * C^(1/p) * lam^(-B/p) * Cco2(p,b) * Cm1^(1/q)
                          * pqCost(c_Q)

    where `Cmult1 = G.grid.Cmult1` (multiplicity of G), `C` and `lam` are the
    decay constants from `hR`, `B` and `r` are the ALS upper-offset and slope from `hk`,
    `Cco2(p,b) = LpGridRepresentation.cCoefficientInt p ∞
      (transmutationKernelZ lam A r)`
    is the convolution trick constant (Prop 4.2, Case A) with the paper's
    truncated integer kernel `b_n = lam ^ (r * n)` when `n > A / r - 1`,
    and `Cm1 = Nat.ceil r` accounts for the `⌈r⌉` residue classes.

    This theorem is the final transmutation statement for a fixed truncation
    level `N`.

    Part 1 is the exact reconstruction statement: the target block sequence
    obtained from the transmutation coefficients and atoms sums back to the
    truncated source expansion `PartialSumLevels`.

    Part 2 is the quantitative statement: the target coefficient cost is bounded
    by the source coefficient cost times three kinds of constants:
    1. geometric constants of the grids, such as the overlap multiplicity;
    2. decay constants `C` and `lam` coming from the representation `R`;
    3. the convolution constants coming from the explicit almost-linear witness
       data `A_als`, `B_als`, `r_als`.

    The theorem is stated with those witness parameters already explicit in the
    hypotheses, so the meaning of the final bound is transparent at the point of
    use: once one has chosen concrete almost-linear bounds for `k`, the same
    data appear directly in the output estimate. -/
private theorem ClaimII
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := q) G c)
    (N : ℕ)
    (hq_ne_top : q ≠ ∞)
    -- Hypotheses needed for Part 1 (formalBlockSeq_summable)
    (hG2_W : AssumptionG2 W s p u q)
    (hp_ne_top : p ≠ ∞)
    (hs_pos : 0 < s) :
    /- Part 1: the transmutation level blocks sum to `PartialSumLevels` in Lp. -/
    HasSum (fun j => (TransmutationBlock G W AW h R c N j).toLp AW)
           (PartialSumLevels G W h c N) ∧
    /- Part 2: with those explicit ALS hypotheses, the `(p,q)`-cost satisfies: -/
    CoeffPQCost (p := p) (q := q) W (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) ≤
      (G.grid.Cmult1 : ℝ) *
      C ^ (1 / p.toReal) *
      lam ^ (-(B_als : ℝ) / p.toReal) *
      LpGridRepresentation.cCoefficientInt p ∞
        (transmutationKernelZ lam A_als r_als) *
      (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
      CoeffPQCost (p := p) (q := q) G c := by
  have hq_pos : (0 : ℝ) < q.toReal :=
    ENNReal.toReal_pos (fun h => absurd (h ▸ (Fact.out : 1 ≤ q)) (by norm_num)) hq_ne_top
  have hp_pos : (0 : ℝ) < p.toReal :=
    ENNReal.toReal_pos (fun h => absurd (h ▸ AW.one_le_p) (by norm_num)) AW.p_ne_top
  have hk0 : AlmostLinearSequence k := ⟨A_als, B_als, r_als, hr_als, hk_bound⟩
  constructor
  · -- Part 1: HasSum
    -- Strategy: (a) AbstractFinitePQCost (TransmutationBlock) from coefficient bound + hc;
    --           (b) formalBlockSeq_summable gives Summable;
    --           (c) identify the sum as PartialSumLevels via ClaimI.
    --
    -- (a) Finite abstract pq-cost
    -- blockLvlCoeff (TransmutationBlock j) k = CoeffPLevel W (TransmutationCoeff) k,
    -- so AbstractFinitePQCost = CoeffFinitePQCost W (TransmutationCoeff),
    -- which follows from Part 2's bound (CoeffPQCost W ≤ K · CoeffPQCost G c) + hc.
    have hfin : AbstractFinitePQCost (q := q) (TransmutationBlock G W AW h R c N) := by
      exact transmutationBlock_abstractFinitePQCost
        G W AW k hk0 lam hlam_pos hlam_lt C hC h R hR c hc N hp_ne_top hq_ne_top
    -- (b) Summable via formalBlockSeq_summable (no atom convergence needed!)
    have hsum : Summable (fun j => (TransmutationBlock G W AW h R c N j).toLp AW) :=
      formalBlockSeq_summable (G := W) (A := AW) hG2_W hp_ne_top hs_pos Fact.out
        (TransmutationBlock G W AW h R c N) hfin
    -- (c) Identity: (TransmutationBlock j).toLp AW = ∑_P m_P · TransmutationAtom P
    -- follows from atomLp being linear and the definitions of TransmutationAtomLocal/Atom.
    have hblock_eq : ∀ j, (TransmutationBlock G W AW h R c N j).toLp AW =
        ∑ P ∈ (W.grid.partitions j).attach,
          (TransmutationCoeff G W AW h R c N P : ℂ) •
            TransmutationAtom G W AW h R c N P := by
      intro j
      exact transmutationBlock_toLp_eq G W AW h R c N j
    -- (d) The tsum equals PartialSumLevels by ClaimI
    have htsum_eq : ∑' j, (TransmutationBlock G W AW h R c N j).toLp AW =
        PartialSumLevels G W h c N := by
      simp_rw [hblock_eq]
      exact ClaimI G W AW k hk0 lam hlam_pos hlam_lt C hC h R hR c hc N
    -- Conclude: HasSum from Summable + sum identity
    rw [← htsum_eq]
    exact hsum.hasSum
  · -- Part 2: Coefficient bound (paper Prop 8.1)
    -- Since q ≠ ∞, unpack CoeffPQCost on both sides as (∑' ...)^{1/q}
    have hLHS_eq :
        CoeffPQCost (p := p) (q := q) W
          (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) =
        (∑' j, CoeffPLevel (p := p) W
            (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j ^
          (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
      simp [CoeffPQCost, hq_ne_top]
    have hRHS_eq :
        CoeffPQCost (p := p) (q := q) G c =
        (∑' i, CoeffPLevel (p := p) G c i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
      simp [CoeffPQCost, hq_ne_top]
    rw [hLHS_eq, hRHS_eq]
    -- Working abbreviations
    set uL : ℕ → ℝ :=
      fun j => CoeffPLevel (p := p) W
        (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j
    set vL : ℕ → ℝ := fun i => CoeffPLevel (p := p) G c i
    -- Convolution sequence:  convL_j = ∑_i [k_i ≤ j] · lam^{(j - k_i)/p} · vL_i^{1/p}
    -- (the per-level bound from Minkowski applied term-by-term; includes 1/p powers)
    set convL : ℕ → ℝ :=
      fun j => ∑' i, if k i ≤ j then
        lam ^ ((↑(j - k i) : ℝ) / p.toReal) * (vL i) ^ (1 / p.toReal) else 0
    -- Basic nonnegativity
    have huL_nn : ∀ j, 0 ≤ uL j := fun j =>
      Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _
    have hvL_nn : ∀ i, 0 ≤ vL i := fun i =>
      Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
    have hconvL_nn : ∀ j, 0 ≤ convL j := fun j =>
      tsum_nonneg fun i => by
        split_ifs with hi
        · exact mul_nonneg (Real.rpow_nonneg hlam_pos.le _) (Real.rpow_nonneg (hvL_nn i) _)
        · exact le_refl 0
    -- STEP A: Level-by-level bound (Minkowski + decay + multiplicity)
    -- For each j: u_j^{1/p} ≤ Cmult1 · C^{1/p} · convL_j
    -- where convL_j = ∑_i [k_i ≤ j] lam^{(j-k_i)/p} · vL_i^{1/p}
    -- Proof sketch:
    --   m_{P,N} = ∑_{i<N} ∑_{Q∈G^i, P⊆Q} |c_Q · s_{P,Q}|
    --   Minkowski: (∑_P m_P^p)^{1/p} ≤ ∑_{i: k_i≤j} (∑_P (∑_{Q:P⊆Q} |c_Q s_{P,Q}|)^p)^{1/p}
    --   Each term ≤ Cmult1 · (C · lam^{j-k_i})^{1/p} · vL_i^{1/p}
    --   (using multiplicity bound + decay bound from hR)
    have hLevelBound : ∀ j, uL j ^ (1 / p.toReal) ≤
        (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j := by
      intro j
      simpa [uL, vL, convL] using
        transmutation_level_bound
          G W AW k hk0 lam hlam_pos hlam_lt C hC h R hR c N j hp_ne_top
    -- STEP D: Convolution + ALS bound (paper Prop 4.2, Case A)
    -- Uses k i ≤ r · i + B (ALS upper bound):
    --   lam^{j - k i} ≤ lam^{j - r·i - B} = lam^{-B} · lam^{j - r·i}
    -- Decomposes i into ⌈r⌉ residue classes mod ⌈r⌉,
    -- applies Young's ℓ^{q/p} convolution with b_n = lam^{r·n}
    -- (the C_co2(p,q,b) constant of Prop 4.2).
    have hvL_sum : Summable fun i => vL i ^ (q.toReal / p.toReal) := by
      simpa [CoeffFinitePQCost, hq_ne_top, vL] using hc
    have hk_upper : ∀ i : ℕ, (k i : NNReal) ≤ r_als * (i : NNReal) + B_als :=
      fun i => (hk_bound i).1
    have hk_lower : ∀ i : ℕ, r_als * (i : NNReal) + A_als ≤ k i := by
      intro i
      exact_mod_cast (hk_bound i).2
    have hConv :
        Summable (fun j => convL j ^ q.toReal) ∧
        (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) ≤
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
        (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
      simpa [convL] using
        transmutation_convolution_bound
          (p := p) (q := q) k lam hlam_pos hlam_lt A_als B_als r_als hr_als
          hk_upper hk_lower vL hvL_nn hvL_sum hp_ne_top hq_ne_top
    have hConvBound :
        (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) ≤
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
        (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) :=
      hConv.2
    -- STEP B+C: From hLevelBound, bound ∑' j, u_j^{q/p}
    -- u_j^{1/p} ≤ Cm1 · C^{1/p} · convL_j  ⟹  u_j^{q/p} = (u_j^{1/p})^q ≤ (Cm1 · C^{1/p} · convL_j)^q
    --                                            = Cm1^q · C^{q/p} · convL_j^q
    -- Summing: ∑' j, u_j^{q/p} ≤ Cm1^q · C^{q/p} · ∑' j, convL_j^q
    have hterm_le : ∀ j,
        uL j ^ (q.toReal / p.toReal) ≤
        (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
        convL j ^ q.toReal := by
      intro j
      -- uL j^{q/p} = (uL j^{1/p})^q ≤ (Cmult1 * C^{1/p} * convL j)^q  [rpow monotone]
      have h1 : uL j ^ (q.toReal / p.toReal) ≤
          ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j) ^ q.toReal := by
        have hmono := Real.rpow_le_rpow
          (Real.rpow_nonneg (huL_nn j) (1 / p.toReal))
          (hLevelBound j) hq_pos.le
        rwa [← Real.rpow_mul (huL_nn j),
             show 1 / p.toReal * q.toReal = q.toReal / p.toReal from by ring] at hmono
      -- (Cmult1 * C^{1/p} * convL j)^q = Cmult1^q * C^{q/p} * convL j^q
      have h2 : ((G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j) ^ q.toReal =
          (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
          convL j ^ q.toReal := by
        rw [Real.mul_rpow
              (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hC (1 / p.toReal)))
              (hconvL_nn j),
            Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hC (1 / p.toReal)),
            ← Real.rpow_mul hC,
            show 1 / p.toReal * q.toReal = q.toReal / p.toReal from by ring]
      exact h1.trans h2.le
    -- Sum the term-by-term bound
    have hStepBC :
        ∑' j, uL j ^ (q.toReal / p.toReal) ≤
        (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
        ∑' j, convL j ^ q.toReal := by
      -- Summability of convL^q follows from hConvBound (finite upper bound)
      have hconv_sum : Summable (fun j => convL j ^ q.toReal) := by
        exact hConv.1
      -- The RHS term (pointwise scaled by the constant factor) is summable
      have hKsumm : Summable (fun j =>
            (G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
            convL j ^ q.toReal) :=
        hconv_sum.mul_left _
      -- uL^{q/p} is summable because it is dominated term-by-term by hKsumm
      have huL_sum : Summable (fun j => uL j ^ (q.toReal / p.toReal)) :=
        Summable.of_nonneg_of_le
          (fun j => Real.rpow_nonneg (huL_nn j) _)
          hterm_le
          hKsumm
      rw [← tsum_mul_left]
      exact huL_sum.tsum_le_tsum hterm_le hKsumm
    -- STEP E: Extract the 1/q root:
    -- (Cm1^q · C^{q/p} · X)^{1/q} = Cm1 · C^{1/p} · X^{1/q}
    have hX_nn : (0 : ℝ) ≤ ∑' j, convL j ^ q.toReal :=
      tsum_nonneg fun j => Real.rpow_nonneg (hconvL_nn j) _
    have hStepE :
        (∑' j, uL j ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) ≤
        (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) := by
      have hstep1 :
          (∑' j, uL j ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) ≤
          ((G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
           ∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) :=
        Real.rpow_le_rpow
          (tsum_nonneg fun j => Real.rpow_nonneg (huL_nn j) _)
          hStepBC
          (div_nonneg zero_le_one hq_pos.le)
      -- Algebra: (Cm1^q · C^{q/p} · X)^{1/q} = Cm1 · C^{1/p} · X^{1/q}
      have hstep2 :
          ((G.grid.Cmult1 : ℝ) ^ q.toReal * C ^ (q.toReal / p.toReal) *
           ∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) =
          (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) := by
        rw [Real.mul_rpow
              (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hC _))
              hX_nn,
            Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hC _)]
        -- (Cm1^q)^{1/q} = Cm1
        congr 2
        · rw [← Real.rpow_mul (Nat.cast_nonneg _)]
          rw [mul_one_div_cancel hq_pos.ne', Real.rpow_one]
        -- (C^{q/p})^{1/q} = C^{1/p}
        · rw [← Real.rpow_mul hC]
          congr 1; field_simp [hp_pos.ne', hq_pos.ne']
      exact hstep1.trans hstep2.le
    -- Final combination
    calc (∑' j, uL j ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)
        ≤ (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          (∑' j, convL j ^ q.toReal) ^ (1 / q.toReal) :=
          hStepE
      _ ≤ (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
          (lam ^ (-(B_als : ℝ) / p.toReal) *
           LpGridRepresentation.cCoefficientInt p ∞
             (transmutationKernelZ lam A_als r_als) *
           (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
           (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal)) :=
          mul_le_mul_of_nonneg_left hConvBound
            (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hC _))
      _ = (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * lam ^ (-(B_als : ℝ) / p.toReal) *
          LpGridRepresentation.cCoefficientInt p ∞
            (transmutationKernelZ lam A_als r_als) *
          (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
          (∑' i, vL i ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by ring

/-- Endpoint `q = ∞` version of **Claim II**, not stated explicitly in the text.

For every `N`, the transmutation blocks form a representation of the truncated
source expansion, and their `ℓ∞` coefficient cost is controlled by the source
`ℓ∞` coefficient cost and the same integer-kernel constant as in the finite
`q` case. -/
private theorem ClaimII_top
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := ∞) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := ∞) G c)
    (N : ℕ)
    (hG2_W : AssumptionG2 W s p u ∞)
    (hp_ne_top : p ≠ ∞)
    (hs_pos : 0 < s) :
    HasSum (fun j => (TransmutationBlock G W AW h R c N j).toLp AW)
           (PartialSumLevels G W h c N) ∧
    CoeffPQCost (p := p) (q := ∞) W
      (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) ≤
      (G.grid.Cmult1 : ℝ) *
      C ^ (1 / p.toReal) *
      lam ^ (-(B_als : ℝ) / p.toReal) *
      LpGridRepresentation.cCoefficientInt p ∞
        (transmutationKernelZ lam A_als r_als) *
      CoeffPQCost (p := p) (q := ∞) G c := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  have hk0 : AlmostLinearSequence k := ⟨A_als, B_als, r_als, hr_als, hk_bound⟩
  let uL : ℕ → ℝ :=
    fun j => CoeffPLevel (p := p) W
      (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j
  let vL : ℕ → ℝ := fun i => CoeffPLevel (p := p) G c i
  let convL : ℕ → ℝ :=
    fun j => ∑' i, if k i ≤ j then
      lam ^ ((↑(j - k i) : ℝ) / p.toReal) * (vL i) ^ (1 / p.toReal) else 0
  have huL_nn : ∀ j, 0 ≤ uL j := fun j =>
    Finset.sum_nonneg fun P _ => Real.rpow_nonneg (norm_nonneg _) _
  have hvL_nn : ∀ i, 0 ≤ vL i := fun i =>
    Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
  have hsource_bdd : BddAbove (Set.range fun i => vL i ^ (1 / p.toReal)) := by
    simpa [CoeffFinitePQCost, vL] using hc
  have hLevelBound : ∀ j, uL j ^ (1 / p.toReal) ≤
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j := by
    intro j
    simpa [uL, vL, convL] using
      transmutation_level_bound
        (p := p) (q := ∞)
        G W AW k hk0 lam hlam_pos hlam_lt C hC h R hR c N j hp_ne_top
  have hk_upper : ∀ i : ℕ, (k i : NNReal) ≤ r_als * (i : NNReal) + B_als :=
    fun i => (hk_bound i).1
  have hk_lower : ∀ i : ℕ, r_als * (i : NNReal) + A_als ≤ k i := by
    intro i
    exact_mod_cast (hk_bound i).2
  have hConv :
      BddAbove (Set.range convL) ∧
      sSup (Set.range convL) ≤
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        sSup (Set.range fun i => vL i ^ (1 / p.toReal)) := by
    simpa [convL] using
      transmutation_convolution_bound_top
        (p := p) k lam hlam_pos hlam_lt A_als B_als r_als hr_als
        hk_upper hk_lower vL hvL_nn hsource_bdd hp_ne_top
  have hconv_point : ∀ j,
      convL j ≤
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        sSup (Set.range fun i => vL i ^ (1 / p.toReal)) := by
    intro j
    exact (le_csSup hConv.1 ⟨j, rfl⟩).trans hConv.2
  let K0 : ℝ := (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal)
  have hK0_nonneg : 0 ≤ K0 := by
    dsimp [K0]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hC _)
  have hroot_bound : ∀ j,
      uL j ^ (1 / p.toReal) ≤
        (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        sSup (Set.range fun i => vL i ^ (1 / p.toReal)) := by
    intro j
    calc
      uL j ^ (1 / p.toReal) ≤ K0 * convL j := by
        simpa [K0, mul_assoc] using hLevelBound j
      _ ≤ K0 *
          (lam ^ (-(B_als : ℝ) / p.toReal) *
            LpGridRepresentation.cCoefficientInt p ∞
              (transmutationKernelZ lam A_als r_als) *
            sSup (Set.range fun i => vL i ^ (1 / p.toReal))) := by
        exact mul_le_mul_of_nonneg_left (hconv_point j) hK0_nonneg
      _ =
        (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        sSup (Set.range fun i => vL i ^ (1 / p.toReal)) := by
        simp [K0, mul_assoc]
  have hroot_bdd : BddAbove (Set.range fun j => uL j ^ (1 / p.toReal)) := by
    refine ⟨(G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        sSup (Set.range fun i => vL i ^ (1 / p.toReal)), ?_⟩
    rintro x ⟨j, rfl⟩
    exact hroot_bound j
  have hfin : AbstractFinitePQCost (q := ∞) (TransmutationBlock G W AW h R c N) := by
    simpa [AbstractFinitePQCost, uL, blockLvlCoeff, CoeffPLevel, TransmutationBlock] using hroot_bdd
  constructor
  · have hsum : Summable (fun j => (TransmutationBlock G W AW h R c N j).toLp AW) :=
      formalBlockSeq_summable (G := W) (A := AW) hG2_W hp_ne_top hs_pos Fact.out
        (TransmutationBlock G W AW h R c N) hfin
    have hblock_eq : ∀ j, (TransmutationBlock G W AW h R c N j).toLp AW =
        ∑ P ∈ (W.grid.partitions j).attach,
          (TransmutationCoeff G W AW h R c N P : ℂ) •
            TransmutationAtom G W AW h R c N P := by
      intro j
      exact transmutationBlock_toLp_eq G W AW h R c N j
    have htsum_eq : ∑' j, (TransmutationBlock G W AW h R c N j).toLp AW =
        PartialSumLevels G W h c N := by
      simp_rw [hblock_eq]
      exact ClaimI_top G W AW k hk0 lam hlam_pos hlam_lt C hC h R hR c hc N
    rw [← htsum_eq]
    exact hsum.hasSum
  · have hLHS_eq :
        CoeffPQCost (p := p) (q := ∞) W
          (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) =
        sSup (Set.range fun j => uL j ^ (1 / p.toReal)) := by
      simp [CoeffPQCost, uL]
    have hRHS_eq :
        CoeffPQCost (p := p) (q := ∞) G c =
        sSup (Set.range fun i => vL i ^ (1 / p.toReal)) := by
      simp [CoeffPQCost, vL]
    rw [hLHS_eq, hRHS_eq]
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    exact hroot_bound j

/-- Endpoint `q = ∞` finite-cost statement for the transmutation blocks. -/
lemma transmutationBlock_abstractFinitePQCost_top
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := ∞) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := ∞) G c)
    (N : ℕ)
    (hp_ne_top : p ≠ ∞) :
    AbstractFinitePQCost (q := ∞) (TransmutationBlock G W AW h R c N) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  have hk0 : AlmostLinearSequence k := ⟨A_als, B_als, r_als, hr_als, hk_bound⟩
  let uL : ℕ → ℝ :=
    fun j => CoeffPLevel (p := p) W
      (fun _ P => (TransmutationCoeff G W AW h R c N P : ℂ)) j
  let vL : ℕ → ℝ := fun i => CoeffPLevel (p := p) G c i
  let convL : ℕ → ℝ :=
    fun j => ∑' i, if k i ≤ j then
      lam ^ ((↑(j - k i) : ℝ) / p.toReal) * (vL i) ^ (1 / p.toReal) else 0
  have hvL_nn : ∀ i, 0 ≤ vL i := fun i =>
    Finset.sum_nonneg fun Q _ => Real.rpow_nonneg (norm_nonneg _) _
  have hsource_bdd : BddAbove (Set.range fun i => vL i ^ (1 / p.toReal)) := by
    simpa [CoeffFinitePQCost, vL] using hc
  have hLevelBound : ∀ j, uL j ^ (1 / p.toReal) ≤
      (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) * convL j := by
    intro j
    simpa [uL, vL, convL] using
      transmutation_level_bound
        (p := p) (q := ∞)
        G W AW k hk0 lam hlam_pos hlam_lt C hC h R hR c N j hp_ne_top
  have hk_upper : ∀ i : ℕ, (k i : NNReal) ≤ r_als * (i : NNReal) + B_als :=
    fun i => (hk_bound i).1
  have hk_lower : ∀ i : ℕ, r_als * (i : NNReal) + A_als ≤ k i := by
    intro i
    exact_mod_cast (hk_bound i).2
  have hConv :
      BddAbove (Set.range convL) ∧
      sSup (Set.range convL) ≤
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        sSup (Set.range fun i => vL i ^ (1 / p.toReal)) := by
    simpa [convL] using
      transmutation_convolution_bound_top
        (p := p) k lam hlam_pos hlam_lt A_als B_als r_als hr_als
        hk_upper hk_lower vL hvL_nn hsource_bdd hp_ne_top
  have hconv_point : ∀ j,
      convL j ≤
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        sSup (Set.range fun i => vL i ^ (1 / p.toReal)) := by
    intro j
    exact (le_csSup hConv.1 ⟨j, rfl⟩).trans hConv.2
  let K0 : ℝ := (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal)
  have hK0_nonneg : 0 ≤ K0 := by
    dsimp [K0]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hC _)
  have hroot_bound : ∀ j,
      uL j ^ (1 / p.toReal) ≤
        (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        sSup (Set.range fun i => vL i ^ (1 / p.toReal)) := by
    intro j
    calc
      uL j ^ (1 / p.toReal) ≤ K0 * convL j := by
        simpa [K0, mul_assoc] using hLevelBound j
      _ ≤ K0 *
          (lam ^ (-(B_als : ℝ) / p.toReal) *
            LpGridRepresentation.cCoefficientInt p ∞
              (transmutationKernelZ lam A_als r_als) *
            sSup (Set.range fun i => vL i ^ (1 / p.toReal))) := by
        exact mul_le_mul_of_nonneg_left (hconv_point j) hK0_nonneg
      _ =
        (G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        sSup (Set.range fun i => vL i ^ (1 / p.toReal)) := by
        simp [K0, mul_assoc]
  have hroot_bdd : BddAbove (Set.range fun j => uL j ^ (1 / p.toReal)) := by
    refine ⟨(G.grid.Cmult1 : ℝ) * C ^ (1 / p.toReal) *
        lam ^ (-(B_als : ℝ) / p.toReal) *
        LpGridRepresentation.cCoefficientInt p ∞
          (transmutationKernelZ lam A_als r_als) *
        sSup (Set.range fun i => vL i ^ (1 / p.toReal)), ?_⟩
    rintro x ⟨j, rfl⟩
    exact hroot_bound j
  simpa [AbstractFinitePQCost, uL, blockLvlCoeff, CoeffPLevel, TransmutationBlock] using hroot_bdd

/-- The `N = ∞` block of the transmuted representation.  At level `j`, its
coefficients are the stable values `m_{P,∞}` and its atoms are the stable local
atoms `d_{P,∞}`. -/
noncomputable def TransmutationBlockLimit
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (A_als r_als : ℝ)
    (j : ℕ) : LevelBlock AW j where
  coeff P := (TransmutationCoeffLimit G W AW h R c A_als r_als P : ℂ)
  atom P := TransmutationAtomLocalLimit G W AW h R c A_als r_als P
  atom_mem P := by
    simpa [TransmutationAtomLocalLimit] using
      TransmutationAtomLocal_isAtom G W AW h R c
        (transmutationStabilizationIndex A_als r_als j) P

/-- Real `pqCost` bounds for a finite-cost representation imply the same bound
for the extended `ENNReal` coefficient cost.  This is the public local version
of the conversion used by the completeness machinery. -/
private lemma pqCostENNReal_le_of_finitePQCost_pqCost_le
  (W : WeakGridSpace (α := α))
  {A : AtomFamily W s p u} {g : Lp ℂ p W.measure} {C : ℝ}
    (R : LpGridRepresentation A g)
    (hRfin : LpGridRepresentation.FinitePQCost (q := q) R)
    (hcost : LpGridRepresentation.pqCost (q := q) R ≤ C) :
    LpGridRepresentation.pqCostENNReal (q := q) R ≤ ENNReal.ofReal C := by
  by_cases hq : q = ∞
  · simp only [LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    simp only [LpGridRepresentation.pqCost, hq, ↓reduceIte] at hcost
    simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    apply sSup_le
    rintro x ⟨k, rfl⟩
    exact ENNReal.ofReal_le_ofReal ((le_csSup hRfin ⟨k, rfl⟩).trans hcost)
  · simp only [LpGridRepresentation.pqCostENNReal, hq, ↓reduceIte]
    simp only [LpGridRepresentation.pqCost, hq, ↓reduceIte] at hcost
    simp only [LpGridRepresentation.FinitePQCost, hq, ↓reduceIte] at hRfin
    have hq_pos : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
    have h_nonneg : ∀ k, 0 ≤ R.levelCoeffPower k ^ (q.toReal / p.toReal) :=
      fun k => Real.rpow_nonneg (R.levelCoeffPower_nonneg k) _
    rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg hRfin,
        ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg h_nonneg)
          (div_nonneg zero_le_one hq_pos.le)]
    exact ENNReal.ofReal_le_ofReal hcost

/-- **Claim III**: the finite transmutation representations converge strongly in
`L^p` to the representation obtained from the stable coefficients `m_{P,∞}` and
stable atoms `d_{P,∞}`.

Formally, the limit block sequence is `TransmutationBlockLimit`; the theorem
states that its block sum converges in `L^p`, defines a Besov-ish element, and
that the truncated source sums `PartialSumLevels ... N` converge strongly to the
same limit. -/

theorem Transmutation_of_Atoms_Claim_A
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := q) G c)
    (hq_ne_top : q ≠ ∞)
    (hG2_W : AssumptionG2 W s p u q)
    (hp_ne_top : p ≠ ∞)
    (hs_pos : 0 < s) :
    ∃ gLim : Lp ℂ p W.measure,
      HasSum (fun j => (TransmutationBlockLimit G W AW h R c A_als r_als j).toLp AW) gLim ∧
      MemBesovishCoeffCost AW q gLim ∧
      Tendsto (fun N => PartialSumLevels G W h c N) atTop (𝓝 gLim) := by
  let K : ℝ :=
    (G.grid.Cmult1 : ℝ) *
    C ^ (1 / p.toReal) *
    lam ^ (-(B_als : ℝ) / p.toReal) *
    LpGridRepresentation.cCoefficientInt p ∞ (transmutationKernelZ lam A_als r_als) *
    (Nat.ceil (r_als : ℝ) : ℝ) ^ (1 / q.toReal) *
    CoeffPQCost (p := p) (q := q) G c
  have hCoeffP_nonneg : ∀ i : ℕ, 0 ≤ CoeffPLevel (p := p) G c i := by
    intro i
    exact Finset.sum_nonneg fun Q hQ => Real.rpow_nonneg (norm_nonneg _) _
  have hCoeffPQ_nonneg : 0 ≤ CoeffPQCost (p := p) (q := q) G c := by
    simp [CoeffPQCost, hq_ne_top]
    exact Real.rpow_nonneg (tsum_nonneg fun i => Real.rpow_nonneg (hCoeffP_nonneg i) _) _
  have hkernel_nonneg : ∀ n : ℤ, 0 ≤ transmutationKernelZ lam A_als r_als n := by
    intro n
    by_cases hn : A_als / r_als - 1 < (n : ℝ)
    · simp [transmutationKernelZ, hn, Real.rpow_nonneg (le_of_lt hlam_pos)]
    · simp [transmutationKernelZ, hn]
  have hccoef_nonneg : 0 ≤
      LpGridRepresentation.cCoefficientInt p ∞ (transmutationKernelZ lam A_als r_als) :=
    LpGridRepresentation.cCoefficientInt_nonneg p ∞ _ hkernel_nonneg
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    repeat' apply mul_nonneg
    · exact by exact_mod_cast Nat.zero_le G.grid.Cmult1
    · exact Real.rpow_nonneg hC _
    · exact Real.rpow_nonneg (le_of_lt hlam_pos) _
    · exact hccoef_nonneg
    · exact Real.rpow_nonneg (show 0 ≤ (Nat.ceil r_als : ℝ) by exact_mod_cast Nat.zero_le (Nat.ceil r_als)) _
    · exact hCoeffPQ_nonneg
  let gseq : ℕ → Lp ℂ p W.measure := fun N => PartialSumLevels G W h c N
  let Rseq : ∀ N, LpGridRepresentation AW (gseq N) := fun N =>
    { block := TransmutationBlock G W AW h R c N
      hasSum := (ClaimII G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt
        C hC h R hR c hc N hq_ne_top hG2_W hp_ne_top hs_pos).1 }
  let Rlim : (j : ℕ) → LevelBlock AW j :=
    fun j => TransmutationBlockLimit G W AW h R c A_als r_als j
  have huniform : ∀ N,
      LpGridRepresentation.pqCostENNReal (q := q) (Rseq N) ≤ ENNReal.ofReal K := by
    intro N
    have hfin : LpGridRepresentation.FinitePQCost (q := q) (Rseq N) := by
      simpa [LpGridRepresentation.FinitePQCost, AbstractFinitePQCost,
        blockLvlCoeff_eq_levelCoeffPower] using
        (transmutationBlock_abstractFinitePQCost
          (p := p) (q := q) G W AW k ⟨A_als, B_als, r_als, hr_als, hk_bound⟩
          lam hlam_pos hlam_lt C hC h R hR c hc N hp_ne_top hq_ne_top)
    have hcost : LpGridRepresentation.pqCost (q := q) (Rseq N) ≤ K := by
      simpa [K, Rseq, LpGridRepresentation.pqCost, CoeffPQCost, TransmutationBlock] using
        (ClaimII G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt
          C hC h R hR c hc N hq_ne_top hG2_W hp_ne_top hs_pos).2
    exact pqCostENNReal_le_of_finitePQCost_pqCost_le (q := q) W (Rseq N) hfin hcost
  have hcoeff_tendsto : ∀ (j : ℕ) (P : LevelCell W j),
      Tendsto (fun N => ((Rseq N).block j).coeff P) atTop
        (𝓝 ((Rlim j).coeff P)) := by
    intro j P
    exact (Complex.continuous_ofReal.tendsto (TransmutationCoeffLimit G W AW h R c A_als r_als P)).comp
      (TransmutationCoeff_tendsto_limit G W AW k A_als B_als r_als hr_als hk_bound
        lam hlam_pos hlam_lt C hC h R hR c P)
  have hatom_tendsto : ∀ (j : ℕ) (P : LevelCell W j),
      Tendsto
        (fun N => atomLp AW (levelCellToWeakGridCell W j P) (((Rseq N).block j).atom P))
        atTop
        (𝓝 (atomLp AW (levelCellToWeakGridCell W j P) ((Rlim j).atom P))) := by
    intro j P
    simpa [Rseq, Rlim, TransmutationBlockLimit, TransmutationAtomLimit] using
      TransmutationAtom_tendsto_limit G W AW k A_als B_als r_als hr_als hk_bound
        lam hlam_pos hlam_lt C hC h R hR c P
  rcases representation_limit_strong_existence (G := W) (p := p) (u := u) (q := q)
      hp_ne_top hs_pos Fact.out AW hG2_W Rseq hK_nonneg huniform Rlim
      hcoeff_tendsto hatom_tendsto with
    ⟨gLim, hRlim, hmem, hfin, hcost, hg_tendsto⟩
  exact ⟨gLim, hRlim, hmem, hg_tendsto⟩

/-- Endpoint `q = ∞` version of **Claim III**. -/
theorem Transmutation_of_Atoms_Claim_A_top
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS (p := p) (q := ∞) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := ∞) G c)
    (hG2_W : AssumptionG2 W s p u ∞)
    (hp_ne_top : p ≠ ∞)
    (hs_pos : 0 < s) :
    ∃ gLim : Lp ℂ p W.measure,
      HasSum (fun j => (TransmutationBlockLimit G W AW h R c A_als r_als j).toLp AW) gLim ∧
      MemBesovishCoeffCost AW ∞ gLim ∧
      Tendsto (fun N => PartialSumLevels G W h c N) atTop (𝓝 gLim) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  let K : ℝ :=
    (G.grid.Cmult1 : ℝ) *
    C ^ (1 / p.toReal) *
    lam ^ (-(B_als : ℝ) / p.toReal) *
    LpGridRepresentation.cCoefficientInt p ∞ (transmutationKernelZ lam A_als r_als) *
    CoeffPQCost (p := p) (q := ∞) G c
  have hCoeffP_nonneg : ∀ i : ℕ, 0 ≤ CoeffPLevel (p := p) G c i := by
    intro i
    exact Finset.sum_nonneg fun Q hQ => Real.rpow_nonneg (norm_nonneg _) _
  have hCoeffPQ_nonneg : 0 ≤ CoeffPQCost (p := p) (q := ∞) G c := by
    simp [CoeffPQCost]
    exact Real.sSup_nonneg' ⟨_, ⟨0, rfl⟩, Real.rpow_nonneg (hCoeffP_nonneg 0) _⟩
  have hkernel_nonneg : ∀ n : ℤ, 0 ≤ transmutationKernelZ lam A_als r_als n := by
    intro n
    by_cases hn : A_als / r_als - 1 < (n : ℝ)
    · simp [transmutationKernelZ, hn, Real.rpow_nonneg (le_of_lt hlam_pos)]
    · simp [transmutationKernelZ, hn]
  have hccoef_nonneg : 0 ≤
      LpGridRepresentation.cCoefficientInt p ∞ (transmutationKernelZ lam A_als r_als) :=
    LpGridRepresentation.cCoefficientInt_nonneg p ∞ _ hkernel_nonneg
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    repeat' apply mul_nonneg
    · exact by exact_mod_cast Nat.zero_le G.grid.Cmult1
    · exact Real.rpow_nonneg hC _
    · exact Real.rpow_nonneg (le_of_lt hlam_pos) _
    · exact hccoef_nonneg
    · exact hCoeffPQ_nonneg
  let gseq : ℕ → Lp ℂ p W.measure := fun N => PartialSumLevels G W h c N
  let Rseq : ∀ N, LpGridRepresentation AW (gseq N) := fun N =>
    { block := TransmutationBlock G W AW h R c N
      hasSum := (ClaimII_top G W AW k A_als B_als r_als hr_als hk_bound
        lam hlam_pos hlam_lt C hC h R hR c hc N hG2_W hp_ne_top hs_pos).1 }
  let Rlim : (j : ℕ) → LevelBlock AW j :=
    fun j => TransmutationBlockLimit G W AW h R c A_als r_als j
  have huniform : ∀ N,
      LpGridRepresentation.pqCostENNReal (q := ∞) (Rseq N) ≤ ENNReal.ofReal K := by
    intro N
    have hfin : LpGridRepresentation.FinitePQCost (q := ∞) (Rseq N) := by
      simpa [LpGridRepresentation.FinitePQCost, AbstractFinitePQCost,
        blockLvlCoeff_eq_levelCoeffPower] using
        (transmutationBlock_abstractFinitePQCost_top
          (p := p) G W AW k A_als B_als r_als hr_als hk_bound
          lam hlam_pos hlam_lt C hC h R hR c hc N hp_ne_top)
    have hcost : LpGridRepresentation.pqCost (q := ∞) (Rseq N) ≤ K := by
      simpa [K, Rseq, LpGridRepresentation.pqCost, CoeffPQCost, TransmutationBlock] using
        (ClaimII_top G W AW k A_als B_als r_als hr_als hk_bound
          lam hlam_pos hlam_lt C hC h R hR c hc N hG2_W hp_ne_top hs_pos).2
    exact pqCostENNReal_le_of_finitePQCost_pqCost_le (q := ∞) W (Rseq N) hfin hcost
  have hcoeff_tendsto : ∀ (j : ℕ) (P : LevelCell W j),
      Tendsto (fun N => ((Rseq N).block j).coeff P) atTop
        (𝓝 ((Rlim j).coeff P)) := by
    intro j P
    exact (Complex.continuous_ofReal.tendsto (TransmutationCoeffLimit G W AW h R c A_als r_als P)).comp
      (TransmutationCoeff_tendsto_limit G W AW k A_als B_als r_als hr_als hk_bound
        lam hlam_pos hlam_lt C hC h R hR c P)
  have hatom_tendsto : ∀ (j : ℕ) (P : LevelCell W j),
      Tendsto
        (fun N => atomLp AW (levelCellToWeakGridCell W j P) (((Rseq N).block j).atom P))
        atTop
        (𝓝 (atomLp AW (levelCellToWeakGridCell W j P) ((Rlim j).atom P))) := by
    intro j P
    simpa [Rseq, Rlim, TransmutationBlockLimit, TransmutationAtomLimit] using
      TransmutationAtom_tendsto_limit G W AW k A_als B_als r_als hr_als hk_bound
        lam hlam_pos hlam_lt C hC h R hR c P
  rcases representation_limit_strong_existence (G := W) (p := p) (u := u) (q := ∞)
      hp_ne_top hs_pos Fact.out AW hG2_W Rseq hK_nonneg huniform Rlim
      hcoeff_tendsto hatom_tendsto with
    ⟨gLim, hRlim, hmem, hfin, hcost, hg_tendsto⟩
  exact ⟨gLim, hRlim, hmem, hg_tendsto⟩


/-- The coefficient `m_P` from Claim B, for a fixed target cell `P`.

The finite set `source` represents the source cells `Q` that are available in
the finite sum coming from formula `(from)` in the paper. -/
noncomputable def claimBMass {σ τ : Type*}
    (source : Finset σ) (c : σ → ℝ) (s : τ → σ → ℝ) (P : τ) : ℝ :=
  ∑ Q ∈ source, |c Q * s P Q|

/-- The function `d_P` from Claim B, written pointwise from formula `(from)`.

When `m_P = 0` the paper defines `d_P` to be zero; otherwise it is the
normalised sum of the atoms `b_{P,Q}`. -/
noncomputable def claimBAtom {σ τ β : Type*}
    (source : Finset σ) (c : σ → ℝ) (s : τ → σ → ℝ)
    (b : τ → σ → β → ℝ) (P : τ) : β → ℝ :=
  let m := claimBMass source c s P
  fun x => if m = 0 then 0 else m⁻¹ * ∑ Q ∈ source, c Q * s P Q * b P Q x

/-- **Claim B, support witness.**

If the Claim B mass `m_P` is nonzero and the scalar coefficients `s_{P,Q}`
are nonnegative, then some source cell really contributes to `P`: its source
coefficient is nonzero and its transmutation coefficient is positive.  The
last hypothesis is the paper's support input, namely that every positive
contribution forces `P` to lie in the support of the corresponding `h_Q`.

The positivity of the normalised atom `d_P` is part of the surrounding paper
argument, but the finite witness itself only needs `m_P ≠ 0`. -/
theorem claimB_support_witness {σ τ β : Type*}
    (source : Finset σ) (c : σ → ℝ) (s : τ → σ → ℝ)
    (b : τ → σ → β → ℝ) (Pcell : τ → Set β) (h : σ → β → ℝ) (P : τ)
    (hs_nonneg : ∀ Q ∈ source, 0 ≤ s P Q)
    (_hb_pos : ∀ Q ∈ source, ∀ x ∈ Pcell P, 0 < b P Q x)
    (_hd_nonzero : ∀ x ∈ Pcell P, claimBAtom source c s b P x ≠ 0)
    (hsupport : ∀ Q ∈ source, 0 < s P Q → Pcell P ⊆ Function.support (h Q))
    (hm : claimBMass source c s P ≠ 0) :
    ∃ Q ∈ source, c Q ≠ 0 ∧ 0 < s P Q ∧ Pcell P ⊆ Function.support (h Q) := by
  by_contra hnone
  apply hm
  simp only [claimBMass]
  refine Finset.sum_eq_zero ?_
  intro Q hQ
  have hnot : ¬ (c Q ≠ 0 ∧ 0 < s P Q ∧ Pcell P ⊆ Function.support (h Q)) := by
    intro hcontrib
    exact hnone ⟨Q, hQ, hcontrib⟩
  have hc_or_hs : c Q = 0 ∨ s P Q = 0 := by
    by_cases hc : c Q = 0
    · exact Or.inl hc
    · right
      have hnot_pos : ¬ 0 < s P Q := by
        intro hs_pos
        exact hnot ⟨hc, hs_pos, hsupport Q hQ hs_pos⟩
      exact le_antisymm (not_lt.mp hnot_pos) (hs_nonneg Q hQ)
  rcases hc_or_hs with hc | hs
  · simp [hc]
  · simp [hs]

omit [Fact (1 ≤ u)] [Fact (1 ≤ q)] in
/-- **Claim B, witness form with the transmutation hypotheses.**

Under the positive representation hypothesis used by
`Transmutation_of_Atoms_Claim_B`, a nonzero mass `m_P` at a finite stage comes
from a genuine source cell.  More explicitly, some source coefficient is
nonzero and the corresponding representation coefficient is a positive real
number.  Since the finite mass only sums over cells containing `P`, the witness
also satisfies `P ⊆ Q`.

This is the project-level form of the paper's assertion that a nonzero `m_P`
forces a nontrivial positive contribution from some `Q`. -/
theorem transmutationCoeff_support_witness
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS_pos (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (N : ℕ) {j : ℕ} (P : LevelCell W j)
    (hm : TransmutationCoeff G W AW h R c N P ≠ 0) :
    ∃ i ∈ Finset.range N, ∃ Q ∈ (G.grid.partitions i).attach,
      P.1 ⊆ Q.1 ∧ c i Q ≠ 0 ∧
        ∃ r : NNReal, 0 < r ∧ ((R i Q).block j).coeff P = (r : ℂ) := by
  by_contra hnone
  apply hm
  simp only [TransmutationCoeff]
  refine Finset.sum_eq_zero ?_
  intro i hi
  refine Finset.sum_eq_zero ?_
  intro Q hQ
  simp only [Finset.mem_filter] at hQ
  rcases hQ with ⟨hQ_mem, hP_sub_Q⟩
  have hnot :
      ¬ (c i Q ≠ 0 ∧ ∃ r : NNReal, 0 < r ∧
        ((R i Q).block j).coeff P = (r : ℂ)) := by
    intro hw
    rcases hw with ⟨hc, r, hr_pos, hr_coeff⟩
    exact hnone ⟨i, hi, Q, hQ_mem, hP_sub_Q, hc, r, hr_pos, hr_coeff⟩
  have hcoeff_nonneg := ((hR i Q).2.1 j P).2.2
  rcases hcoeff_nonneg with ⟨r, hr_coeff, _hatom_pos⟩
  by_cases hc : c i Q = 0
  · simp [hc]
  · have hr_zero : r = 0 := by
      by_contra hr_ne
      have hr_pos : 0 < r := lt_of_le_of_ne bot_le (Ne.symm hr_ne)
      exact hnot ⟨hc, r, hr_pos, hr_coeff⟩
    simp [hr_coeff, hr_zero]

omit [Fact (1 ≤ u)] [Fact (1 ≤ q)] in
/-- Under the positive representation hypothesis, every single pointwise block
term is a nonnegative real number. -/
private lemma positiveRepresentation_term_eq_nnreal
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS_pos (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    {i n : ℕ} (Q : LevelCell G i) (S : LevelCell W n) (x : α) :
    ∃ a : NNReal,
      ((R i Q).block n).coeff S *
        AW.toFunction (levelCellToWeakGridCell W n S) (((R i Q).block n).atom S) x =
          (a : ℂ) := by
  rcases ((hR i Q).2.1 n S).2.2 with ⟨r, hr_coeff, hatom_pos⟩
  by_cases hxS : x ∈ S.1
  · rcases hatom_pos x hxS with ⟨a, _ha_pos, ha_atom⟩
    refine ⟨r * a, ?_⟩
    simp [hr_coeff, ha_atom]
  · refine ⟨0, ?_⟩
    have hatom_zero :
        AW.toFunction (levelCellToWeakGridCell W n S) (((R i Q).block n).atom S) x = 0 := by
      simpa [levelCellToWeakGridCell] using
        AW.local_support (levelCellToWeakGridCell W n S) (((R i Q).block n).atom S) x hxS
    simp [hatom_zero]

omit [Fact (1 ≤ u)] [Fact (1 ≤ q)] in
/-- The distinguished positive coefficient gives a strictly positive pointwise
term on its target cell. -/
private lemma positiveRepresentation_distinguished_term_pos
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS_pos (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    {i j : ℕ} {Q : LevelCell G i} {P : LevelCell W j}
    (hcoeff_pos : ∃ r : NNReal, 0 < r ∧ ((R i Q).block j).coeff P = (r : ℂ))
    {x : α} (hxP : x ∈ P.1) :
    ∃ a : NNReal, 0 < a ∧
      ((R i Q).block j).coeff P *
        AW.toFunction (levelCellToWeakGridCell W j P) (((R i Q).block j).atom P) x =
          (a : ℂ) := by
  rcases hcoeff_pos with ⟨r, hr_pos, hr_coeff⟩
  rcases ((hR i Q).2.1 j P).2.2 with ⟨r', hr'_coeff, hatom_pos⟩
  rcases hatom_pos x hxP with ⟨a, ha_pos, ha_atom⟩
  have hr_eq : r' = r := by
    have hcast : (r' : ℂ) = (r : ℂ) := hr'_coeff.symm.trans hr_coeff
    exact_mod_cast hcast
  subst r'
  refine ⟨r * a, mul_pos hr_pos ha_pos, ?_⟩
  simp [hr_coeff, ha_atom]

omit [Fact (1 ≤ u)] [Fact (1 ≤ q)] in
/-- Under the positive representation hypothesis, every pointwise level-block
sum is a nonnegative real number. -/
private lemma positiveRepresentation_block_toFunLt_eq_nnreal
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS_pos (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    {i n : ℕ} (Q : LevelCell G i) (x : α) :
    ∃ a : NNReal, ((R i Q).block n).toFunLt AW x = (a : ℂ) := by
  classical
  have hterm :
      ∀ S : LevelCell W n, ∃ a : NNReal,
        ((R i Q).block n).coeff S *
          AW.toFunction (levelCellToWeakGridCell W n S) (((R i Q).block n).atom S) x =
            (a : ℂ) := by
    intro S
    exact positiveRepresentation_term_eq_nnreal
      G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt C hC h R hR Q S x
  choose a ha using hterm
  refine ⟨∑ S : LevelCell W n, a S, ?_⟩
  simp [LevelBlock.toFunLt, ha]

omit [Fact (1 ≤ u)] [Fact (1 ≤ q)] in
/-- On the target cell of a strictly positive coefficient, the corresponding
level-block value is a nonnegative real bounded below by a positive real. -/
private lemma positiveRepresentation_distinguished_block_lower
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS_pos (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    {i j : ℕ} {Q : LevelCell G i} {P : LevelCell W j}
    (hcoeff_pos : ∃ r : NNReal, 0 < r ∧ ((R i Q).block j).coeff P = (r : ℂ))
    {x : α} (hxP : x ∈ P.1) :
    ∃ a b : NNReal, 0 < b ∧ b ≤ a ∧ ((R i Q).block j).toFunLt AW x = (a : ℂ) := by
  classical
  rcases positiveRepresentation_distinguished_term_pos
      G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt C hC h R hR
      hcoeff_pos hxP with
    ⟨b, hb_pos, hb_term⟩
  have hterm :
      ∀ S : LevelCell W j, ∃ a : NNReal,
        ((R i Q).block j).coeff S *
          AW.toFunction (levelCellToWeakGridCell W j S) (((R i Q).block j).atom S) x =
            (a : ℂ) := by
    intro S
    exact positiveRepresentation_term_eq_nnreal
      G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt C hC h R hR Q S x
  choose a ha using hterm
  have haP : a P = b := by
    have hcast : (a P : ℂ) = (b : ℂ) := (ha P).symm.trans hb_term
    exact_mod_cast hcast
  refine ⟨∑ S : LevelCell W j, a S, b, hb_pos, ?_, ?_⟩
  · rw [← haP]
    exact Finset.single_le_sum (fun S _ => bot_le) (Finset.mem_univ P)
  · simp [LevelBlock.toFunLt, ha]

omit [Fact (1 ≤ u)] [Fact (1 ≤ q)] in
/-- Once the finite partial block sum contains the distinguished level, its
pointwise value on the target cell is bounded below by one fixed positive real. -/
private lemma positiveRepresentation_partial_toFun_lower
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS_pos (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    {i j : ℕ} {Q : LevelCell G i} {P : LevelCell W j}
    (hcoeff_pos : ∃ r : NNReal, 0 < r ∧ ((R i Q).block j).coeff P = (r : ℂ))
    {x : α} (hxP : x ∈ P.1) :
    ∃ b : NNReal, 0 < b ∧ ∀ N, j < N →
      ∃ a : NNReal, b ≤ a ∧
        (∑ n ∈ Finset.range N, ((R i Q).block n).toFunLt AW x) = (a : ℂ) := by
  classical
  have hblock :
      ∀ n : ℕ, ∃ a : NNReal, ((R i Q).block n).toFunLt AW x = (a : ℂ) := by
    intro n
    exact positiveRepresentation_block_toFunLt_eq_nnreal
      G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt C hC h R hR Q x
  choose a ha using hblock
  rcases positiveRepresentation_distinguished_block_lower
      G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt C hC h R hR
      hcoeff_pos hxP with
    ⟨aj, b, hb_pos, hb_le_aj, haj⟩
  have haj_eq : a j = aj := by
    have hcast : (a j : ℂ) = (aj : ℂ) := (ha j).symm.trans haj
    exact_mod_cast hcast
  refine ⟨b, hb_pos, ?_⟩
  intro N hN
  refine ⟨∑ n ∈ Finset.range N, a n, ?_, ?_⟩
  · have hj_mem : j ∈ Finset.range N := Finset.mem_range.mpr hN
    exact hb_le_aj.trans (by
      rw [← haj_eq]
      exact Finset.single_le_sum (fun n _ => bot_le) hj_mem)
  · simp [ha]

/-- A positive block representation gives a positive representative a.e. on any
target cell whose coefficient is strictly positive.

This is the analytic bridge needed by Claim B: the positive representation
hypothesis is stated at the level of block atoms, while Claim B wants positivity
for the represented `Lp` function. -/
private lemma positiveRepresentation_source_ae_pos_of_pos_coeff
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS_pos (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    {i j : ℕ} {Q : LevelCell G i} {P : LevelCell W j}
    (hcoeff_pos : ∃ r : NNReal, 0 < r ∧ ((R i Q).block j).coeff P = (r : ℂ)) :
    ∀ᵐ x ∂ W.measure.restrict P.1,
      ∃ r : NNReal, 0 < r ∧ h i Q x = (r : ℂ) := by
  classical
  let partialSum : ℕ → Lp ℂ p W.measure :=
    fun N => ∑ n ∈ Finset.range N, ((R i Q).block n).toLp AW
  have hpartial_tendsto : Tendsto partialSum atTop (𝓝 (h i Q)) := by
    simpa [partialSum] using (R i Q).hasSum.tendsto_sum_nat
  have hpartial_coe : ∀ N : ℕ,
      (partialSum N : α → ℂ) =ᵐ[W.measure]
        fun x => ∑ n ∈ Finset.range N, ((R i Q).block n).toFunLt AW x := by
    intro N
    induction' N with N ih
    · simpa [partialSum] using (Lp.coeFn_zero ℂ p W.measure)
    · have hblock :
          (((R i Q).block N).toLp AW : α → ℂ) =ᵐ[W.measure]
            fun x => ((R i Q).block N).toFunLt AW x :=
        LevelBlock.coeFn_toLp AW ((R i Q).block N)
      have hsum := ih.add hblock
      have hLp :
          partialSum (N + 1) =
            partialSum N + ((R i Q).block N).toLp AW := by
        simp [partialSum, Finset.sum_range_succ]
      rw [hLp]
      refine (Lp.coeFn_add _ _).trans ?_
      refine hsum.trans ?_
      filter_upwards with x
      simp [Finset.sum_range_succ, add_comm]
  have htendsto_measure :
      TendstoInMeasure W.measure (fun N => partialSum N) atTop (h i Q) :=
    tendstoInMeasure_of_tendsto_Lp hpartial_tendsto
  rcases htendsto_measure.exists_seq_tendsto_ae with ⟨φ, hφ_mono, hφ_tendsto_ae⟩
  have hφ_tendsto_restrict :
      ∀ᵐ x ∂ W.measure.restrict P.1,
        Tendsto (fun m => partialSum (φ m) x) atTop (𝓝 (h i Q x)) :=
    ae_restrict_of_ae hφ_tendsto_ae
  have hcoe_restrict :
      ∀ᵐ x ∂ W.measure.restrict P.1, ∀ m : ℕ,
        partialSum (φ m) x =
          ∑ n ∈ Finset.range (φ m), ((R i Q).block n).toFunLt AW x := by
    have hsets :
        (⋂ m : ℕ, {x : α |
          partialSum (φ m) x =
            ∑ n ∈ Finset.range (φ m), ((R i Q).block n).toFunLt AW x}) ∈
          ae (W.measure.restrict P.1) := by
      exact countable_iInter_mem.mpr fun m => ae_restrict_of_ae (hpartial_coe (φ m))
    filter_upwards [hsets] with x hx m
    exact Set.mem_iInter.mp hx m
  have hP_meas : MeasurableSet P.1 := W.grid.measurable j P.1 P.2
  filter_upwards [ae_restrict_mem hP_meas, hφ_tendsto_restrict, hcoe_restrict] with
    x hxP hxlim hxcoe
  rcases positiveRepresentation_partial_toFun_lower
      G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt C hC h R hR
      hcoeff_pos hxP with
    ⟨b, hb_pos, hb_lower⟩
  have hφ_large : ∀ᶠ m in atTop, j < φ m := by
    exact (hφ_mono.tendsto_atTop.eventually (eventually_gt_atTop j))
  have hre_eventually :
      ∀ᶠ m in atTop, (b : ℝ) ≤ (partialSum (φ m) x).re := by
    filter_upwards [hφ_large] with m hm
    rcases hb_lower (φ m) hm with ⟨a, hba, hsum_eq⟩
    have hpartial_eq : partialSum (φ m) x = (a : ℂ) := by
      rw [hxcoe m, hsum_eq]
    rw [hpartial_eq]
    exact_mod_cast hba
  have him_eventually :
      (fun m => (partialSum (φ m) x).im) =ᶠ[atTop] fun _ => (0 : ℝ) := by
    filter_upwards [hφ_large] with m hm
    rcases hb_lower (φ m) hm with ⟨a, _hba, hsum_eq⟩
    have hpartial_eq : partialSum (φ m) x = (a : ℂ) := by
      rw [hxcoe m, hsum_eq]
    simp [hpartial_eq]
  have hre_lim : (b : ℝ) ≤ (h i Q x).re := by
    have hre_tendsto :
        Tendsto (fun m => (partialSum (φ m) x).re) atTop (𝓝 ((h i Q x).re)) :=
      (Complex.continuous_re.tendsto (h i Q x)).comp hxlim
    exact ge_of_tendsto hre_tendsto hre_eventually
  have him_lim : (h i Q x).im = 0 := by
    have him_tendsto_zero :
        Tendsto (fun m => (partialSum (φ m) x).im) atTop (𝓝 (0 : ℝ)) :=
      him_eventually.tendsto
    have him_tendsto :
        Tendsto (fun m => (partialSum (φ m) x).im) atTop (𝓝 ((h i Q x).im)) :=
      (Complex.continuous_im.tendsto (h i Q x)).comp hxlim
    exact tendsto_nhds_unique him_tendsto him_tendsto_zero
  have hb_nonneg : (0 : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hb_pos.le
  have hb_real_pos : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb_pos
  refine ⟨⟨(h i Q x).re, ?_⟩, ?_, ?_⟩
  · exact le_trans hb_nonneg hre_lim
  · exact lt_of_lt_of_le hb_real_pos hre_lim
  · apply Complex.ext
    · rfl
    · simp [him_lim]

/-- **Claim B** from the transmutation proposition.

Besides the limiting transmutation statement, this formulation records the
support witness used in the positive case: whenever the limiting mass attached
to a target cell `P` is nonzero and the limiting atom `d_P` is nonzero on `P`,
some source cell `Q` containing `P` contributes with nonzero source coefficient
and positive real representation coefficient. -/
theorem Transmutation_of_Atoms_Claim_B (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS_pos (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc : CoeffFinitePQCost (p := p) (q := q) G c)
    (hG2_W : AssumptionG2 W s p u q)
    (hp_ne_top : p ≠ ∞)
    (hs_pos : 0 < s) :
    (∃ gLim : Lp ℂ p W.measure,
      HasSum (fun j => (TransmutationBlockLimit G W AW h R c A_als r_als j).toLp AW) gLim ∧
      MemBesovishCoeffCost AW q gLim ∧
      Tendsto (fun N => PartialSumLevels G W h c N) atTop (𝓝 gLim)) ∧
    (∀ j : ℕ, ∀ P : LevelCell W j,
      TransmutationCoeffLimit G W AW h R c A_als r_als P ≠ 0 →
      (∃ x, x ∈ P.1 →
        AW.toFunction (levelCellToWeakGridCell W j P)
          (TransmutationAtomLocalLimit G W AW h R c A_als r_als P) x ≠ 0) →
        ∃ i ∈ Finset.range (transmutationStabilizationIndex A_als r_als j),
          ∃ Q ∈ (G.grid.partitions i).attach,
          P.1 ⊆ Q.1 ∧ c i Q ≠ 0 ∧
            ∃ r : NNReal, 0 < r ∧ ((R i Q).block j).coeff P = (r : ℂ) ∧
              ∀ᵐ x ∂ W.measure.restrict P.1,
                ∃ r : NNReal, 0 < r ∧ h i Q x = (r : ℂ)) := by
  have hR_plain : RepresentationWsubGandALS (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R := by
    intro i Q
    rcases hR i Q with ⟨hfin, hloc, hdecay⟩
    refine ⟨hfin, ?_, hdecay⟩
    intro j S
    exact ⟨(hloc j S).1, (hloc j S).2.1⟩
  constructor
  · by_cases hq_top : q = ∞
    · subst q
      exact Transmutation_of_Atoms_Claim_A_top G W AW k A_als B_als r_als hr_als hk_bound
        lam hlam_pos hlam_lt C hC h R hR_plain c hc hG2_W hp_ne_top hs_pos
    · exact Transmutation_of_Atoms_Claim_A G W AW k A_als B_als r_als hr_als hk_bound
        lam hlam_pos hlam_lt C hC h R hR_plain c hc hq_top hG2_W hp_ne_top hs_pos
  · intro j P hm _hd_nonzero
    rcases transmutationCoeff_support_witness G W AW k A_als B_als r_als hr_als hk_bound
      lam hlam_pos hlam_lt C hC h R hR c
      (transmutationStabilizationIndex A_als r_als j) P
      (by simpa [TransmutationCoeffLimit] using hm) with
      ⟨i, hi, Q, hQ, hPQ, hcQ, r, hr_pos, hr_coeff⟩
    refine ⟨i, hi, Q, hQ, hPQ, hcQ, r, hr_pos, hr_coeff, ?_⟩
    exact positiveRepresentation_source_ae_pos_of_pos_coeff
      G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt C hC h R hR
      ⟨r, hr_pos, hr_coeff⟩

omit [Fact (1 ≤ u)] [Fact (1 ≤ q)] in
/-- Under nonnegative source coefficients, a nonzero limiting mass gives a
pointwise nonzero limiting atom on the target cell. -/
private lemma TransmutationAtomLocalLimit_ne_zero_of_coeff_ne_zero
    (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS_pos (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc_nonneg : ∀ i : ℕ, ∀ Q : LevelCell G i, ∃ r : NNReal, c i Q = (r : ℂ))
    {j : ℕ} (P : LevelCell W j)
    (hm : TransmutationCoeffLimit G W AW h R c A_als r_als P ≠ 0)
    {x : α} (hxP : x ∈ P.1) :
    AW.toFunction (levelCellToWeakGridCell W j P)
      (TransmutationAtomLocalLimit G W AW h R c A_als r_als P) x ≠ 0 := by
  classical
  let N := transmutationStabilizationIndex A_als r_als j
  let m := TransmutationCoeff G W AW h R c N P
  let Pg := levelCellToWeakGridCell W j P
  let FS : Finset (Σ i : ℕ, LevelCell G i) :=
    (Finset.range N).sigma
      (fun i => (G.grid.partitions i).attach.filter (fun Q => P.1 ⊆ Q.1))
  have hmN : m ≠ 0 := by
    simpa [m, N, TransmutationCoeffLimit] using hm
  rcases transmutationCoeff_support_witness
      G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt C hC h R hR c
      N P (by simpa [N, TransmutationCoeffLimit] using hm) with
    ⟨i₀, hi₀, Q₀, hQ₀, hP_sub_Q₀, hcQ₀_ne, r₀, hr₀_pos, hr₀_coeff⟩
  let iQ₀ : Σ i : ℕ, LevelCell G i := ⟨i₀, Q₀⟩
  have hiQ₀_mem : iQ₀ ∈ FS := by
    simp [FS, iQ₀, hi₀, hQ₀, hP_sub_Q₀]
  have hterm :
      ∀ iQ : Σ i : ℕ, LevelCell G i, ∃ a : NNReal,
        (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) *
          AW.toFunction Pg (((R iQ.1 iQ.2).block j).atom P) x = (a : ℂ) := by
    intro iQ
    rcases hc_nonneg iQ.1 iQ.2 with ⟨rc, hrc_eq⟩
    rcases ((hR iQ.1 iQ.2).2.1 j P).2.2 with ⟨rs, hrs_eq, hatom_pos⟩
    rcases hatom_pos x hxP with ⟨a, _ha_pos, ha_eq⟩
    refine ⟨rc * rs * a, ?_⟩
    simp [Pg, hrc_eq, hrs_eq, ha_eq, mul_assoc]
  choose a ha using hterm
  have hdist :
      ∃ b : NNReal, 0 < b ∧
        (c i₀ Q₀ * ((R i₀ Q₀).block j).coeff P) *
          AW.toFunction Pg (((R i₀ Q₀).block j).atom P) x = (b : ℂ) := by
    rcases hc_nonneg i₀ Q₀ with ⟨rc, hrc_eq⟩
    have hrc_pos : 0 < rc := by
      have hrc_ne : rc ≠ 0 := by
        intro hrc_zero
        apply hcQ₀_ne
        simp [hrc_eq, hrc_zero]
      exact lt_of_le_of_ne bot_le (Ne.symm hrc_ne)
    rcases ((hR i₀ Q₀).2.1 j P).2.2 with ⟨rs, hrs_eq, hatom_pos⟩
    have hrs_eq_r₀ : rs = r₀ := by
      have hcast : (rs : ℂ) = (r₀ : ℂ) := hrs_eq.symm.trans hr₀_coeff
      exact_mod_cast hcast
    rcases hatom_pos x hxP with ⟨b, hb_pos, hb_eq⟩
    refine ⟨rc * r₀ * b, mul_pos (mul_pos hrc_pos hr₀_pos) hb_pos, ?_⟩
    subst rs
    simp [Pg, hrc_eq, hr₀_coeff, hb_eq, mul_assoc]
  rcases hdist with ⟨b, hb_pos, hb_eq⟩
  have ha_iQ₀_pos : 0 < a iQ₀ := by
    have hcast : (a iQ₀ : ℂ) = (b : ℂ) := by
      simpa [iQ₀] using (ha iQ₀).symm.trans hb_eq
    have hab : a iQ₀ = b := by
      exact_mod_cast hcast
    simpa [hab] using hb_pos
  have hsum_pos : 0 < ∑ iQ ∈ FS, a iQ :=
    Finset.sum_pos' (fun iQ _ => bot_le) ⟨iQ₀, hiQ₀_mem, ha_iQ₀_pos⟩
  have hsum_eq :
      (∑ iQ ∈ FS,
        (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) *
          AW.toFunction Pg (((R iQ.1 iQ.2).block j).atom P) x) =
        ((∑ iQ ∈ FS, a iQ : NNReal) : ℂ) := by
    simp [ha]
  have hfun :
      AW.toFunction Pg (TransmutationAtomLocalLimit G W AW h R c A_als r_als P) x =
        (m : ℂ)⁻¹ *
          ∑ iQ ∈ FS,
            (c iQ.1 iQ.2 * ((R iQ.1 iQ.2).block j).coeff P) *
              AW.toFunction Pg (((R iQ.1 iQ.2).block j).atom P) x := by
    simp [TransmutationAtomLocalLimit, TransmutationAtomLocal, N, m, Pg, FS, hmN,
      AtomFamily.toFunction, map_smul, map_sum, Finset.sum_apply, smul_eq_mul]
  rw [hfun, hsum_eq]
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hmN)) (by exact_mod_cast hsum_pos.ne')

/-- A sharper Claim B under nonnegative source coefficients.

The extra source-coefficient hypothesis says every `c i Q` is a nonnegative
real number, embedded in `ℂ`.  For the source cell selected by Claim B, the
nonzero condition then upgrades to strict positivity. -/
theorem Transmutation_of_Atoms_Claim_B_sharp (G W : WeakGridSpace (α := α))
    (AW : AtomFamily W s p u)
    (k : ℕ → ℕ)
    (A_als B_als r_als : ℝ)
    (hr_als : 0 < r_als)
    (hk_bound : ∀ i : ℕ,
      (k i : NNReal) ≤ r_als * (i : NNReal) + B_als ∧
      r_als * (i : NNReal) + A_als ≤ (k i : NNReal))
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (i : ℕ) → LevelCell G i → Lp ℂ p W.measure)
    (R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AW (h i Q))
    (hR : RepresentationWsubGandALS_pos (p := p) (q := q) G W AW k
      ⟨A_als, B_als, r_als, hr_als, hk_bound⟩ lam hlam_pos hlam_lt C hC h R)
    (c : (i : ℕ) → LevelCell G i → ℂ)
    (hc_nonneg : ∀ i : ℕ, ∀ Q : LevelCell G i, ∃ r : NNReal, c i Q = (r : ℂ))
    (hc : CoeffFinitePQCost (p := p) (q := q) G c)
    (hG2_W : AssumptionG2 W s p u q)
    (hp_ne_top : p ≠ ∞)
    (hs_pos : 0 < s) :
    (∃ gLim : Lp ℂ p W.measure,
      HasSum (fun j => (TransmutationBlockLimit G W AW h R c A_als r_als j).toLp AW) gLim ∧
      MemBesovishCoeffCost AW q gLim ∧
      Tendsto (fun N => PartialSumLevels G W h c N) atTop (𝓝 gLim)) ∧
    (∀ j : ℕ, ∀ P : LevelCell W j,
      TransmutationCoeffLimit G W AW h R c A_als r_als P ≠ 0 →
      (∀ᵐ x ∂ W.measure.restrict P.1,
        AW.toFunction (levelCellToWeakGridCell W j P)
          (TransmutationAtomLocalLimit G W AW h R c A_als r_als P) x ≠ 0) ∧
        ∃ i ∈ Finset.range (transmutationStabilizationIndex A_als r_als j),
          ∃ Q ∈ (G.grid.partitions i).attach,
          P.1 ⊆ Q.1 ∧
            (∃ rc : NNReal, 0 < rc ∧ c i Q = (rc : ℂ)) ∧
            ∃ r : NNReal, 0 < r ∧ ((R i Q).block j).coeff P = (r : ℂ) ∧
              ∀ᵐ x ∂ W.measure.restrict P.1,
                ∃ r : NNReal, 0 < r ∧ h i Q x = (r : ℂ)) := by
  rcases Transmutation_of_Atoms_Claim_B G W AW k A_als B_als r_als hr_als hk_bound
      lam hlam_pos hlam_lt C hC h R hR c hc hG2_W hp_ne_top hs_pos with
    ⟨hlimit, hwitness⟩
  refine ⟨hlimit, ?_⟩
  intro j P hm
  have hP_meas : MeasurableSet P.1 := W.grid.measurable j P.1 P.2
  have hatom_ae :
      ∀ᵐ x ∂ W.measure.restrict P.1,
        AW.toFunction (levelCellToWeakGridCell W j P)
          (TransmutationAtomLocalLimit G W AW h R c A_als r_als P) x ≠ 0 := by
    filter_upwards [ae_restrict_mem hP_meas] with x hxP
    exact TransmutationAtomLocalLimit_ne_zero_of_coeff_ne_zero
      G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt C hC h R hR
      c hc_nonneg P hm hxP
  rcases transmutationCoeff_support_witness G W AW k A_als B_als r_als hr_als hk_bound
      lam hlam_pos hlam_lt C hC h R hR c
      (transmutationStabilizationIndex A_als r_als j) P
      (by simpa [TransmutationCoeffLimit] using hm) with
    ⟨i, hi, Q, hQ, hPQ, hcQ_ne, r, hr_pos, hr_coeff⟩
  rcases hc_nonneg i Q with ⟨rc, hrc_eq⟩
  have hrc_pos : 0 < rc := by
    have hrc_ne : rc ≠ 0 := by
      intro hrc_zero
      apply hcQ_ne
      simp [hrc_eq, hrc_zero]
    exact lt_of_le_of_ne bot_le (Ne.symm hrc_ne)
  refine ⟨hatom_ae, i, hi, Q, hQ, hPQ, ⟨rc, hrc_pos, hrc_eq⟩, r, hr_pos, hr_coeff, ?_⟩
  exact positiveRepresentation_source_ae_pos_of_pos_coeff
    G W AW k A_als B_als r_als hr_als hk_bound lam hlam_pos hlam_lt C hC h R hR
    ⟨r, hr_pos, hr_coeff⟩

private lemma id_almostLinear_bound :
    ∀ i : ℕ,
      ((fun i : ℕ => i) i : NNReal) ≤ (1 : ℝ) * (i : NNReal) + 0 ∧
      (1 : ℝ) * (i : NNReal) + 0 ≤ ((fun i : ℕ => i) i : NNReal) := by
  intro i
  constructor <;> norm_num

private lemma id_almostLinearSequence : AlmostLinearSequence (fun i : ℕ => i) :=
  ⟨0, 0, 1, by norm_num, id_almostLinear_bound⟩

/--
The explicit constant in Claim C for the identity level map.

This is the Lean version of the paper's Claim C constant after simplifying the
special case used here.  The almost-linear sequence is `k i = i`, so the general
Claim A factors `lambda^(-B/p)` and `m1^(1/q)` are both equal to one.
-/
noncomputable def transmutationClaimCEmbeddingConstant
    (G : WeakGridSpace (α := α)) (p _q : ℝ≥0∞) (lam C : ℝ) : ℝ :=
  (G.grid.Cmult1 : ℝ) *
    C ^ (1 / p.toReal) *
    LpGridRepresentation.cCoefficientInt p ∞ (transmutationKernelZ lam 0 1)

/-- Claim C: if every `AG1` atom admits a uniformly controlled `AG2`
representation centered at the same level, then any `AG1` atomic expansion
transmutes into an `AG2` expansion.

The constants `lam` and `C` are outside the universal quantifier over atoms, so
they are uniform: they do not depend on the particular atom being represented. -/
theorem Transmutation_of_Atoms_Claim_C_explicit
    (G : WeakGridSpace (α := α))
    (u1 u2 : ℝ≥0∞)
    [Fact (1 ≤ u2)]
    (AG1 : AtomFamily G s p u1)
    (AG2 : AtomFamily G s p u2)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hAG1_to_AG2 : ∀ i : ℕ, ∀ Q : LevelCell G i,
      ∀ g : Lp ℂ p G.measure,
        (∃ φ : (AG1.localSpace (levelCellToWeakGridCell G i Q)).carrier,
          AG1.IsAtom (levelCellToWeakGridCell G i Q) φ ∧
            g = atomLp AG1 (levelCellToWeakGridCell G i Q) φ) →
          ∃ Rg : LpGridRepresentation AG2 g,
            CoeffFinitePQCost (p := p) (q := q) G
              (fun j S => (Rg.block j).coeff S) ∧
            (∀ j : ℕ, ∀ S : LevelCell G j,
              (¬ S.1 ⊆ Q.1 → (Rg.block j).coeff S = 0) ∧
              (j < i → (Rg.block j).coeff S = 0)) ∧
            ∀ j : ℕ, i ≤ j → Rg.levelCoeffPower j ≤ C * lam ^ (j - i)) :
    0 ≤ transmutationClaimCEmbeddingConstant G p q lam C ∧
      ∀ (h : (i : ℕ) → LevelCell G i → Lp ℂ p G.measure),
      (∀ i : ℕ, ∀ Q : LevelCell G i,
        ∃ φ : (AG1.localSpace (levelCellToWeakGridCell G i Q)).carrier,
          AG1.IsAtom (levelCellToWeakGridCell G i Q) φ ∧
            h i Q = atomLp AG1 (levelCellToWeakGridCell G i Q) φ) →
      ∀ (c : (i : ℕ) → LevelCell G i → ℂ),
      CoeffFinitePQCost (p := p) (q := q) G c →
      AssumptionG2 G s p u2 q →
      p ≠ ∞ →
      0 < s →
      ∃ R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AG2 (h i Q),
        RepresentationWsubGandALS (p := p) (q := q) G G AG2 (fun i : ℕ => i)
          id_almostLinearSequence lam hlam_pos hlam_lt C hC h R ∧
        ∃ gLim : Lp ℂ p G.measure,
          Tendsto (fun N => PartialSumLevels G G h c N) atTop (𝓝 gLim) ∧
          ∃ hsum_AG2 :
            HasSum (fun j => (TransmutationBlockLimit G G AG2 h R c 0 1 j).toLp AG2) gLim,
            let RlimAG2 : LpGridRepresentation AG2 gLim :=
              { block := TransmutationBlockLimit G G AG2 h R c 0 1
                hasSum := hsum_AG2 }
            LpGridRepresentation.FinitePQCost (q := q) RlimAG2 ∧
            MemBesovishCoeffCost AG2 q gLim ∧
              LpGridRepresentation.pqCost (q := q) RlimAG2 ≤
                transmutationClaimCEmbeddingConstant G p q lam C *
                  CoeffPQCost (p := p) (q := q) G c := by
  classical
  let C_cont_embedding : ℝ := transmutationClaimCEmbeddingConstant G p q lam C
  have hkernel_nonneg : ∀ n : ℤ, 0 ≤ transmutationKernelZ lam 0 1 n := by
    intro n
    dsimp [transmutationKernelZ]
    split_ifs
    · exact Real.rpow_nonneg (le_of_lt hlam_pos) _
    · rfl
  have hccoef_nonneg : 0 ≤
      LpGridRepresentation.cCoefficientInt p ∞ (transmutationKernelZ lam 0 1) :=
    LpGridRepresentation.cCoefficientInt_nonneg p ∞ _ hkernel_nonneg
  have hCcont_nonneg : 0 ≤ C_cont_embedding := by
    dsimp [C_cont_embedding, transmutationClaimCEmbeddingConstant]
    repeat' apply mul_nonneg
    · exact by exact_mod_cast Nat.zero_le G.grid.Cmult1
    · exact Real.rpow_nonneg hC _
    · exact hccoef_nonneg
  refine ⟨by simpa [C_cont_embedding] using hCcont_nonneg, ?_⟩
  intro h h_atom c hc hG2_G hp_ne_top hs_pos
  have hrepr : ∀ i : ℕ, ∀ Q : LevelCell G i,
      ∃ Rg : LpGridRepresentation AG2 (h i Q),
        CoeffFinitePQCost (p := p) (q := q) G
          (fun j S => (Rg.block j).coeff S) ∧
        (∀ j : ℕ, ∀ S : LevelCell G j,
          (¬ S.1 ⊆ Q.1 → (Rg.block j).coeff S = 0) ∧
          (j < i → (Rg.block j).coeff S = 0)) ∧
        ∀ j : ℕ, i ≤ j → Rg.levelCoeffPower j ≤ C * lam ^ (j - i) := by
    intro i Q
    exact hAG1_to_AG2 i Q (h i Q) (h_atom i Q)
  choose R0 hR0 using hrepr
  let R : (i : ℕ) → (Q : LevelCell G i) → LpGridRepresentation AG2 (h i Q) :=
    fun i Q => R0 i Q
  have hR : RepresentationWsubGandALS (p := p) (q := q) G G AG2 (fun i : ℕ => i)
      id_almostLinearSequence lam hlam_pos hlam_lt C hC h R := by
    intro i Q
    simpa [R] using hR0 i Q
  refine ⟨R, hR, ?_⟩
  let K : ℝ := C_cont_embedding * CoeffPQCost (p := p) (q := q) G c
  have hCoeffP_nonneg : ∀ i : ℕ, 0 ≤ CoeffPLevel (p := p) G c i := by
    intro i
    exact Finset.sum_nonneg fun Q hQ => Real.rpow_nonneg (norm_nonneg _) _
  have hCoeffPQ_nonneg : 0 ≤ CoeffPQCost (p := p) (q := q) G c := by
    by_cases hq_top : q = ∞
    · have hbdd : BddAbove
          (Set.range fun i => CoeffPLevel (p := p) G c i ^ (1 / p.toReal)) := by
        simpa [CoeffFinitePQCost, hq_top] using hc
      have hzero_le :
          0 ≤ CoeffPLevel (p := p) G c 0 ^ (1 / p.toReal) :=
        Real.rpow_nonneg (hCoeffP_nonneg 0) _
      simpa [CoeffPQCost, hq_top] using
        hzero_le.trans
          (le_csSup hbdd ⟨0, rfl⟩)
    · simp [CoeffPQCost, hq_top]
      exact Real.rpow_nonneg (tsum_nonneg fun i => Real.rpow_nonneg (hCoeffP_nonneg i) _) _
  have hK_nonneg : 0 ≤ K := mul_nonneg hCcont_nonneg hCoeffPQ_nonneg
  let gseq : ℕ → Lp ℂ p G.measure := fun N => PartialSumLevels G G h c N
  let Rseq : ∀ N, LpGridRepresentation AG2 (gseq N) := fun N =>
    { block := TransmutationBlock G G AG2 h R c N
      hasSum := by
        by_cases hq_top : q = ∞
        · subst q
          exact (ClaimII_top G G AG2 (fun i : ℕ => i) 0 0 1 (by norm_num)
            id_almostLinear_bound lam hlam_pos hlam_lt C hC h R hR c hc N
            hG2_G hp_ne_top hs_pos).1
        · exact (ClaimII G G AG2 (fun i : ℕ => i) 0 0 1 (by norm_num)
            id_almostLinear_bound lam hlam_pos hlam_lt C hC h R hR c hc N
            hq_top hG2_G hp_ne_top hs_pos).1 }
  let Rlim : (j : ℕ) → LevelBlock AG2 j :=
    fun j => TransmutationBlockLimit G G AG2 h R c 0 1 j
  have huniform : ∀ N,
      LpGridRepresentation.pqCostENNReal (q := q) (Rseq N) ≤ ENNReal.ofReal K := by
    intro N
    have hfin : LpGridRepresentation.FinitePQCost (q := q) (Rseq N) := by
      by_cases hq_top : q = ∞
      · subst q
        simpa [Rseq, LpGridRepresentation.FinitePQCost, AbstractFinitePQCost,
          blockLvlCoeff_eq_levelCoeffPower] using
          (transmutationBlock_abstractFinitePQCost_top
            (p := p) G G AG2 (fun i : ℕ => i) 0 0 1 (by norm_num)
            id_almostLinear_bound lam hlam_pos hlam_lt C hC h R hR c hc N hp_ne_top)
      · simpa [Rseq, LpGridRepresentation.FinitePQCost, AbstractFinitePQCost,
          blockLvlCoeff_eq_levelCoeffPower] using
          (transmutationBlock_abstractFinitePQCost
            (p := p) (q := q) G G AG2 (fun i : ℕ => i) id_almostLinearSequence
            lam hlam_pos hlam_lt C hC h R hR c hc N hp_ne_top hq_top)
    have hcost : LpGridRepresentation.pqCost (q := q) (Rseq N) ≤ K := by
      by_cases hq_top : q = ∞
      · subst q
        simpa [K, C_cont_embedding, transmutationClaimCEmbeddingConstant, Rseq,
          LpGridRepresentation.pqCost, CoeffPQCost, TransmutationBlock] using
          (ClaimII_top G G AG2 (fun i : ℕ => i) 0 0 1 (by norm_num)
            id_almostLinear_bound lam hlam_pos hlam_lt C hC h R hR c hc N
            hG2_G hp_ne_top hs_pos).2
      · simpa [K, C_cont_embedding, transmutationClaimCEmbeddingConstant, Rseq,
          LpGridRepresentation.pqCost, CoeffPQCost, TransmutationBlock] using
          (ClaimII G G AG2 (fun i : ℕ => i) 0 0 1 (by norm_num)
            id_almostLinear_bound lam hlam_pos hlam_lt C hC h R hR c hc N
            hq_top hG2_G hp_ne_top hs_pos).2
    exact pqCostENNReal_le_of_finitePQCost_pqCost_le (q := q) G (Rseq N) hfin hcost
  have hcoeff_tendsto : ∀ (j : ℕ) (P : LevelCell G j),
      Tendsto (fun N => ((Rseq N).block j).coeff P) atTop
        (𝓝 ((Rlim j).coeff P)) := by
    intro j P
    exact (Complex.continuous_ofReal.tendsto
      (TransmutationCoeffLimit G G AG2 h R c 0 1 P)).comp
        (TransmutationCoeff_tendsto_limit G G AG2 (fun i : ℕ => i) 0 0 1
          (by norm_num) id_almostLinear_bound lam hlam_pos hlam_lt C hC h R hR c P)
  have hatom_tendsto : ∀ (j : ℕ) (P : LevelCell G j),
      Tendsto
        (fun N => atomLp AG2 (levelCellToWeakGridCell G j P) (((Rseq N).block j).atom P))
        atTop
        (𝓝 (atomLp AG2 (levelCellToWeakGridCell G j P) ((Rlim j).atom P))) := by
    intro j P
    simpa [Rseq, Rlim, TransmutationBlockLimit, TransmutationAtomLimit] using
      TransmutationAtom_tendsto_limit G G AG2 (fun i : ℕ => i) 0 0 1
        (by norm_num) id_almostLinear_bound lam hlam_pos hlam_lt C hC h R hR c P
  rcases representation_limit_strong_existence (G := G) (p := p) (u := u2) (q := q)
      hp_ne_top hs_pos Fact.out AG2 hG2_G Rseq hK_nonneg huniform Rlim
      hcoeff_tendsto hatom_tendsto with
    ⟨gLim, hRlim, hmem, _hfin, hcost, hg_tendsto⟩
  refine ⟨gLim, hg_tendsto, hRlim, ?_⟩
  exact ⟨_hfin, hmem, by simpa [K] using hcost⟩

/-- Continuous embedding induced by Claim C.

If every `AG1` atom admits a uniformly controlled representation by `AG2`
atoms, then every element represented with finite `(p,q)` cost in `AG1` is also
represented with finite `(p,q)` cost in `AG2`.  Moreover the `AG2` cost gauge is
bounded by a uniform constant times the `AG1` cost gauge. -/
theorem Transmutation_of_Atoms_continuous_embedding_explicit
    (G : WeakGridSpace (α := α))
    (u1 u2 : ℝ≥0∞)
    [Fact (1 ≤ u2)]
    (AG1 : AtomFamily G s p u1)
    (AG2 : AtomFamily G s p u2)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hAG1_to_AG2 : ∀ i : ℕ, ∀ Q : LevelCell G i,
      ∀ g : Lp ℂ p G.measure,
        (∃ φ : (AG1.localSpace (levelCellToWeakGridCell G i Q)).carrier,
          AG1.IsAtom (levelCellToWeakGridCell G i Q) φ ∧
            g = atomLp AG1 (levelCellToWeakGridCell G i Q) φ) →
          ∃ Rg : LpGridRepresentation AG2 g,
            CoeffFinitePQCost (p := p) (q := q) G
              (fun j S => (Rg.block j).coeff S) ∧
            (∀ j : ℕ, ∀ S : LevelCell G j,
              (¬ S.1 ⊆ Q.1 → (Rg.block j).coeff S = 0) ∧
              (j < i → (Rg.block j).coeff S = 0)) ∧
            ∀ j : ℕ, i ≤ j → Rg.levelCoeffPower j ≤ C * lam ^ (j - i))
    (hG2_G : AssumptionG2 G s p u2 q)
    (hp_ne_top : p ≠ ∞)
    (hs_pos : 0 < s) :
    0 ≤ transmutationClaimCEmbeddingConstant G p q lam C ∧
      ∀ g : BesovishSpace AG1 q,
        ∃ hg2 : MemBesovishCoeffCost AG2 q (g : Lp ℂ p G.measure),
          BesovishSpace.Norm_Costpq AG2 q
              (⟨(g : Lp ℂ p G.measure), hg2⟩ : BesovishSpace AG2 q) ≤
            transmutationClaimCEmbeddingConstant G p q lam C *
              BesovishSpace.Norm_Costpq AG1 q g := by
  classical
  rcases Transmutation_of_Atoms_Claim_C_explicit G u1 u2 AG1 AG2
      lam hlam_pos hlam_lt C hC hAG1_to_AG2 with
    ⟨hCcont_nonneg_explicit, hclaim⟩
  let C_cont_embedding : ℝ := transmutationClaimCEmbeddingConstant G p q lam C
  have hCcont_nonneg : 0 ≤ C_cont_embedding := by
    simpa [C_cont_embedding] using hCcont_nonneg_explicit
  refine ⟨hCcont_nonneg_explicit, ?_⟩
  have hAG1_finite : BesovishSpace.HasFiniteCostRepresentations (A := AG1) q :=
    BesovishSpace.hasFiniteCostRepresentations (A := AG1) (q := q)
  have transmute_rep :
      ∀ {gLp : Lp ℂ p G.measure} (Rg : LpGridRepresentation AG1 gLp),
        LpGridRepresentation.FinitePQCost (q := q) Rg →
        ∃ hg2 : MemBesovishCoeffCost AG2 q gLp,
          BesovishSpace.Norm_Costpq AG2 q
              (⟨gLp, hg2⟩ : BesovishSpace AG2 q) ≤
            C_cont_embedding * LpGridRepresentation.pqCost (q := q) Rg := by
    intro gLp Rg hRgfin
    let h : (i : ℕ) → LevelCell G i → Lp ℂ p G.measure :=
      fun i Q => atomLp AG1 (levelCellToWeakGridCell G i Q) ((Rg.block i).atom Q)
    let c : (i : ℕ) → LevelCell G i → ℂ :=
      fun i Q => (Rg.block i).coeff Q
    have h_atom : ∀ i : ℕ, ∀ Q : LevelCell G i,
        ∃ φ : (AG1.localSpace (levelCellToWeakGridCell G i Q)).carrier,
          AG1.IsAtom (levelCellToWeakGridCell G i Q) φ ∧
            h i Q = atomLp AG1 (levelCellToWeakGridCell G i Q) φ := by
      intro i Q
      exact ⟨(Rg.block i).atom Q, (Rg.block i).atom_mem Q, rfl⟩
    have hc : CoeffFinitePQCost (p := p) (q := q) G c := by
      simpa [CoeffFinitePQCost, LpGridRepresentation.FinitePQCost, c,
        CoeffPLevel, LpGridRepresentation.levelCoeffPower] using hRgfin
    rcases hclaim h h_atom c hc hG2_G hp_ne_top hs_pos with
      ⟨R, _hR, gLim, hgLim_tendsto, hsum_AG2, hRlim_fin, hmem, hcost⟩
    have hpartial_eq : ∀ N,
        PartialSumLevels G G h c N =
          ∑ i ∈ Finset.range N, (Rg.block i).toLp AG1 := by
      intro N
      simp [PartialSumLevels, h, c, LevelBlock.toLp, LevelBlock.term, atomLp]
    have hpartial_tendsto_g :
        Tendsto (fun N => PartialSumLevels G G h c N) atTop (𝓝 gLp) := by
      simpa [hpartial_eq] using Rg.hasSum.tendsto_sum_nat
    have hgLim_eq : gLim = gLp :=
      tendsto_nhds_unique hgLim_tendsto hpartial_tendsto_g
    subst gLim
    let RlimAG2 : LpGridRepresentation AG2 gLp :=
      { block := TransmutationBlockLimit G G AG2 h R c 0 1
        hasSum := hsum_AG2 }
    have hnorm_le :
        BesovishSpace.Norm_Costpq AG2 q
            (⟨gLp, hmem⟩ : BesovishSpace AG2 q) ≤
          LpGridRepresentation.pqCost (q := q) RlimAG2 :=
      BesovishSpace.Norm_Costpq_le_cost (A := AG2) (q := q)
        (g := (⟨gLp, hmem⟩ : BesovishSpace AG2 q)) RlimAG2 hRlim_fin
    have hcoeff_cost_eq :
        CoeffPQCost (p := p) (q := q) G c =
          LpGridRepresentation.pqCost (q := q) Rg := by
      simp [CoeffPQCost, LpGridRepresentation.pqCost, c,
        CoeffPLevel, LpGridRepresentation.levelCoeffPower]
    refine ⟨hmem, ?_⟩
    calc
      BesovishSpace.Norm_Costpq AG2 q
          (⟨gLp, hmem⟩ : BesovishSpace AG2 q)
          ≤ LpGridRepresentation.pqCost (q := q) RlimAG2 := hnorm_le
      _ ≤ C_cont_embedding * CoeffPQCost (p := p) (q := q) G c := hcost
      _ = C_cont_embedding * LpGridRepresentation.pqCost (q := q) Rg := by
        rw [hcoeff_cost_eq]
  intro g
  rcases g.property with ⟨Rg0, hRg0fin⟩
  rcases transmute_rep Rg0 hRg0fin with ⟨hg2, _hbound0⟩
  refine ⟨hg2, ?_⟩
  refine le_iff_forall_pos_le_add.mpr ?_
  intro ε hε
  have hden_pos : 0 < C_cont_embedding + 1 := by
    linarith
  have hδ_pos : 0 < ε / (C_cont_embedding + 1) := by
    positivity
  rcases BesovishSpace.exists_cost_lt_Norm_Costpq_add (A := AG1) (q := q)
      hAG1_finite g hδ_pos with
    ⟨Rg, hRgfin, hRglt⟩
  rcases transmute_rep Rg hRgfin with ⟨hg2ε, hnormε⟩
  have hcost_to_norm :
      C_cont_embedding * LpGridRepresentation.pqCost (q := q) Rg ≤
        C_cont_embedding *
          (BesovishSpace.Norm_Costpq AG1 q g + ε / (C_cont_embedding + 1)) :=
    mul_le_mul_of_nonneg_left (le_of_lt hRglt) hCcont_nonneg
  have hsmall : C_cont_embedding * (ε / (C_cont_embedding + 1)) ≤ ε := by
    have hfrac : C_cont_embedding / (C_cont_embedding + 1) ≤ (1 : ℝ) :=
      (div_le_one hden_pos).2 (by linarith)
    have hε_nonneg : 0 ≤ ε := le_of_lt hε
    have hmul : (C_cont_embedding / (C_cont_embedding + 1)) * ε ≤ (1 : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hfrac hε_nonneg
    calc
      C_cont_embedding * (ε / (C_cont_embedding + 1)) =
          (C_cont_embedding / (C_cont_embedding + 1)) * ε := by ring
      _ ≤ (1 : ℝ) * ε := hmul
      _ = ε := by ring
  have hboundε :
      BesovishSpace.Norm_Costpq AG2 q
          (⟨(g : Lp ℂ p G.measure), hg2ε⟩ : BesovishSpace AG2 q) ≤
        C_cont_embedding * BesovishSpace.Norm_Costpq AG1 q g + ε := by
    calc
      BesovishSpace.Norm_Costpq AG2 q
          (⟨(g : Lp ℂ p G.measure), hg2ε⟩ : BesovishSpace AG2 q)
          ≤ C_cont_embedding * LpGridRepresentation.pqCost (q := q) Rg := hnormε
      _ ≤ C_cont_embedding *
          (BesovishSpace.Norm_Costpq AG1 q g + ε / (C_cont_embedding + 1)) :=
            hcost_to_norm
      _ = C_cont_embedding * BesovishSpace.Norm_Costpq AG1 q g +
          C_cont_embedding * (ε / (C_cont_embedding + 1)) := by ring
      _ ≤ C_cont_embedding * BesovishSpace.Norm_Costpq AG1 q g + ε := by
        exact add_le_add_right hsmall _
  have hsame :
      (⟨(g : Lp ℂ p G.measure), hg2ε⟩ : BesovishSpace AG2 q) =
        ⟨(g : Lp ℂ p G.measure), hg2⟩ :=
    Subtype.ext rfl
  simpa [hsame] using hboundε

end -- closes noncomputable section

end WeakGridSpace
