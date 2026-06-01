import BesovSpacesGoodGrid.GoodGrid.BesovSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Mean oscillation norm on a good grid

This file records the mean-oscillation gauge from the manuscript.  The local
oscillation is defined as an infimum over constants of the `L^p` seminorm of
`f - c` restricted to a grid cell.  The global gauge is allowed to take the
value `∞`, since no summability is assumed for an arbitrary function.
-/

open scoped ENNReal BigOperators
open MeasureTheory

namespace GoodGridSpace

universe u

variable {α : Type u} [MeasurableSpace α]

noncomputable section

namespace MeanOscillation

/--
The local mean oscillation of `f` on a good-grid cell `Q`.

For finite `p`, this is the infimum over constants of
`(∫_Q ‖f - c‖^p)^(1/p)`.  For `p = ∞`, the same formula uses Mathlib's
`eLpNorm`, hence becomes the essential-supremum oscillation on `Q`.
-/
def osc (G : GoodGridSpace (α := α)) (p : ℝ≥0∞)
    (f : α → ℂ) (Q : GoodGridCell G) : ℝ≥0∞ :=
  sInf (Set.range fun c : ℂ =>
    MeasureTheory.eLpNorm (fun x => f x - c) p (G.grid.μ.restrict Q.cell))

/--
The level-`k` contribution to the mean-oscillation gauge.

It is `∑_{Q ∈ P^k} μ(Q)^(-s p) osc_p(f,Q)^p`.
-/
def levelOscillationBlock (G : GoodGridSpace (α := α))
    (s : ℝ) (p : ℝ≥0∞) (f : α → ℂ) (k : ℕ) : ℝ≥0∞ :=
  ∑ Q : WeakGridSpace.LevelCell G.toWeakGridSpace k,
    (G.grid.μ Q.1) ^ (-(s * p.toReal)) *
      (osc G p f ({ level := k, cell := Q.1, mem := Q.2 } : GoodGridCell G)) ^ p.toReal

/--
The oscillation seminorm `osc^s_{p,q}`.

For `q = ∞` this is the supremum over levels.  Otherwise it is the usual
`ℓ^q(L^p)` aggregation of the level blocks.
-/
def oscillationSeminorm (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞) (f : α → ℂ) : ℝ≥0∞ :=
  if q = ∞ then
    sSup (Set.range fun k => (levelOscillationBlock G s p f k) ^ (1 / p.toReal))
  else
    (∑' k, (levelOscillationBlock G s p f k) ^ (q.toReal / p.toReal)) ^
      (1 / q.toReal)

/--
The full mean-oscillation gauge `N_osc`.

The first term is `μ(I)^(-s) ‖f‖_p`, where `I = univ`; the second term is
`osc^s_{p,q}`.
-/
def meanOscillationNorm (G : GoodGridSpace (α := α))
    (s : ℝ) (p q : ℝ≥0∞) (f : α → ℂ) : ℝ≥0∞ :=
  (G.grid.μ Set.univ) ^ (-s) * MeasureTheory.eLpNorm f p G.grid.μ +
    oscillationSeminorm G s p q f

end MeanOscillation

end

end GoodGridSpace
