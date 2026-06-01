import BesovSpacesGoodGrid.GoodGrid.BesovSpace
import UnbalancedHaarWavelet.HaarWaveletsCoeffs
import UnbalancedHaarWavelet.HaarWavelets_def_Martingale

/-!
# Haar representation norm on a good grid

This file records the concrete Haar-coefficient gauge used in the paper's
Haar representation section.  The underlying Haar wavelets are the concrete
non-normalized wavelets from `UnbalancedHaarWavelet`; this file exposes the
paper's normalized functions `φ_i = ψ_i / ‖ψ_i‖₂`, so the coefficient
`d_i^f = ∫ f φ_i dμ` is the usual orthonormal Haar coefficient.
-/

open scoped ENNReal BigOperators
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace HaarRepresentation

abbrev GridOf (G : GoodGridSpace (α := α)) : UnbalancedHaarWavelet.Grid (α := α) :=
  G.grid.toGrid

/--
The support used for full Haar indices.

The father function is supported on the whole space.  A wavelet index uses its
ordinary branch support from `UnbalancedHaarWavelet`.
-/
def support (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G)) :
    F.Index → Set α
  | .alpha => Set.univ
  | .wavelet i => i.branchSupport (GridOf G) F.toHaarSystem

/--
The scalar that turns the concrete Haar function into an `L²`-normalized one.

The dependency's wavelet is denoted here by `ψ_i`; this is `1 / ‖ψ_i‖₂`, using
the square norm supplied by `UnbalancedHaarWavelet`.
-/
def l2NormalizationFactor (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G)) (i : F.Index) : ℝ :=
  (Real.sqrt (F.indexL2NormSq (GridOf G) i))⁻¹

/--
The `L²`-normalized full Haar function `φ_i`.

The function `F.function` is the concrete non-normalized Haar function from
`UnbalancedHaarWavelet` (with the dependency's father-function convention).
This definition rescales it by `1 / ‖ψ_i‖₂`.
-/
def normalizedFunction (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (i : F.Index) (x : α) : ℂ :=
  ((l2NormalizationFactor G F i : ℝ) : ℂ) *
    (UnbalancedHaarWavelet.FullHaarSystem.function (GridOf G) F i x : ℂ)

/--
The Haar coefficient against the normalized Haar function, with the
integrability hypothesis explicit in the API.

This is the manuscript's convention `d_i^f = ∫ f φ_i dm`, as a complex integral.
Since `φ_i` has `L²` norm `1`, no extra division by `‖ψ_i‖₂²` appears.
-/
def Coeff (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (f : α → ℂ) (_hf : Integrable f G.grid.μ) (i : F.Index) : ℂ :=
  ∫ x, f x * normalizedFunction G F i x ∂G.grid.μ

/--
Wavelet indices whose parent cell is `Q`.

This is the formal version of the finite family `H_Q` in the paper.
-/
def indicesInCell (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (Q : GoodGridCell G) :
    Finset {b : Finset (Set α) × Finset (Set α) //
      b ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches} :=
  (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches.attach

/-- Turn a branch of the binary refinement tree over `Q` into a global Haar index. -/
def indexOfCellBranch (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (Q : GoodGridCell G)
    (b : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (F.toHaarSystem.binaryRefinement.tree Q.level Q.cell Q.mem).Branches}) :
    F.toHaarSystem.Index where
  level := Q.level
  cell := Q.cell
  hcell := Q.mem
  branch := b

/--
The `p`-power contribution of Haar coefficients over one cell `Q`.

This is the inner finite sum `∑_{S ∈ H_Q} |d_S^f|^p`, written using the
normalized Haar coefficient convention fixed above.
-/
def cellCoeffPower (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) (Q : GoodGridCell G) :
    ℝ≥0∞ :=
  ∑ b ∈ indicesInCell G F Q,
    ENNReal.ofReal (‖Coeff G F f hf (.wavelet (indexOfCellBranch G F Q b))‖ ^ p.toReal)

/--
The level-`k` Haar block appearing in `N_haar`.

It is
`∑_{Q ∈ P^k} μ(Q)^(1 - s p - p/2) ∑_{S ∈ H_Q} |d_S^f|^p`.
-/
def levelHaarBlock (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) (k : ℕ) :
    ℝ≥0∞ :=
  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    ENNReal.ofReal ((G.grid.μ Q.1).toReal ^ (1 - s * p.toReal - p.toReal / 2)) *
      cellCoeffPower G F p f hf
        { level := k
          cell := Q.1
          mem := Q.2 }

/--
The father-function term in `N_haar`.

This is `μ(I)^(1/p - s - 1/2) |d_I^f|`, with `I = univ`.
-/
def fatherTerm (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((G.grid.μ Set.univ).toReal ^ (1 / p.toReal - s - 1 / 2) *
      ‖Coeff G F f hf .alpha‖)

/--
The Haar representation gauge from the paper, using `L²`-normalized Haar
functions.
-/
def haarL2RepresentationNorm (G : GoodGridSpace (α := α)) [DecidableEq (Set α)]
    (F : UnbalancedHaarWavelet.FullHaarSystem (G := GridOf G))
    (s : ℝ) (p q : ℝ≥0∞) (f : α → ℂ) (hf : Integrable f G.grid.μ) : ℝ≥0∞ :=
  fatherTerm G F s p f hf +
    if q = ∞ then
      sSup (Set.range fun k => (levelHaarBlock G F s p f hf k) ^ (1 / p.toReal))
    else
      (∑' k, (levelHaarBlock G F s p f hf k) ^ (q.toReal / p.toReal)) ^
        (1 / q.toReal)

end HaarRepresentation

end

end GoodGridSpace
