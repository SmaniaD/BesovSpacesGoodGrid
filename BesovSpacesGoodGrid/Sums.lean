import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Basic

/-!
# Block-indexed sums

This file provides a small reusable notation layer for sums indexed by a
sequence of finite families.  It packages a global index as a level together
with a cell at that level, and defines notation for the corresponding iterated
infinite sum.
-/

open scoped BigOperators

universe u v

/--
`BlockIndex F` is the type of all global indices associated with a family

`F : ℕ → Finset (Set α)`.

An element `P : BlockIndex F` consists of:

* `P.level : ℕ`;
* `P.val : Set α`;
* `P.mem : P.val ∈ F P.level`.

Thus `P` represents a pair `(k, P)` with `P ∈ F k`.
-/
structure BlockIndex {α : Type u} (F : ℕ → Finset (Set α)) where
  level : ℕ
  val : Set α
  mem : val ∈ F level

namespace BlockIndex

variable {α : Type u}
variable {F : ℕ → Finset (Set α)}

/-- The level of a global block index. -/
def k (P : BlockIndex F) : ℕ :=
  P.level

/-- The underlying set associated with a global block index. -/
def set (P : BlockIndex F) : Set α :=
  P.val

end BlockIndex


/--
The infinite block sum associated with a family of finite sets

`F : ℕ → Finset (Set α)`.

If `c : BlockIndex F → E`, then

`blockTsum F c`

means

`∑' k : ℕ, ∑ P in (F k).attach, c ⟨k, P.1, P.2⟩`.

Mathematically, this represents

`∑ₖ ∑_{P ∈ F k} c_P`.
-/
noncomputable def blockTsum
    {α : Type u}
    {E : Type v}
    [AddCommMonoid E]
    [TopologicalSpace E]
    (F : ℕ → Finset (Set α))
    (c : BlockIndex F → E) : E :=
  ∑' k : ℕ, (F k).attach.sum fun P => c ⟨k, P.1, P.2⟩


/--
Notation for the global block sum.

`∑ᵇ P ∈ᵇ F, c P`

means

`blockTsum F (fun P => c P)`.
-/
syntax "∑ᵇ " ident " ∈ᵇ " term ", " term : term

macro_rules
  | `(∑ᵇ $P:ident ∈ᵇ $F, $body) =>
      `(blockTsum $F (fun $P => $body))


/--
`ChildIndex F P` is the type of strict descendants of `P`.

An element `Q : ChildIndex F P` consists of:

* `Q.level : ℕ`;
* `Q.val : Set α`;
* `Q.mem : Q.val ∈ F Q.level`;
* `Q.level_gt : P.level < Q.level`;
* `Q.subset : Q.val ⊆ P.val`.

Thus `Q` represents a block strictly below `P`.
This is the formal meaning of `Q ∈ P⁺`.
-/
structure ChildIndex
    {α : Type u}
    (F : ℕ → Finset (Set α))
    (P : BlockIndex F) where
  level : ℕ
  val : Set α
  mem : val ∈ F level
  level_gt : P.level < level
  subset : val ⊆ P.val

namespace ChildIndex

variable {α : Type u}
variable {F : ℕ → Finset (Set α)}
variable {P : BlockIndex F}

/--
Forget that a child index is a child, keeping only the underlying
global block index.
-/
def toBlockIndex (Q : ChildIndex F P) : BlockIndex F :=
  ⟨Q.level, Q.val, Q.mem⟩

end ChildIndex


/--
`ParentIndex F P` is the type of strict ancestors of `P`.

An element `Q : ParentIndex F P` consists of:

* `Q.level : ℕ`;
* `Q.val : Set α`;
* `Q.mem : Q.val ∈ F Q.level`;
* `Q.level_lt : Q.level < P.level`;
* `Q.contains : P.val ⊆ Q.val`.

Thus `Q` represents a block strictly above `P`.
This is the formal meaning of `Q ∈ P⁻`.
-/
structure ParentIndex
    {α : Type u}
    (F : ℕ → Finset (Set α))
    (P : BlockIndex F) where
  level : ℕ
  val : Set α
  mem : val ∈ F level
  level_lt : level < P.level
  contains : P.val ⊆ val

namespace ParentIndex

variable {α : Type u}
variable {F : ℕ → Finset (Set α)}
variable {P : BlockIndex F}

/--
Forget that a parent index is a parent, keeping only the underlying
global block index.
-/
def toBlockIndex (Q : ParentIndex F P) : BlockIndex F :=
  ⟨Q.level, Q.val, Q.mem⟩

end ParentIndex


/--
The infinite sum over the strict descendants of `P`.

`childTsum F P d`

means

`∑' Q : ChildIndex F P, d Q`.

The type `ChildIndex F P` encodes the conditions

`P.level < Q.level` and `Q.val ⊆ P.val`.
-/
noncomputable def childTsum
    {α : Type u}
    {E : Type v}
    [AddCommMonoid E]
    [TopologicalSpace E]
    (F : ℕ → Finset (Set α))
    (P : BlockIndex F)
    (d : ChildIndex F P → E) : E :=
  ∑' Q : ChildIndex F P, d Q


/--
The infinite sum over the strict ancestors of `P`.

`parentTsum F P d`

means

`∑' Q : ParentIndex F P, d Q`.

The type `ParentIndex F P` encodes the conditions

`Q.level < P.level` and `P.val ⊆ Q.val`.
-/
noncomputable def parentTsum
    {α : Type u}
    {E : Type v}
    [AddCommMonoid E]
    [TopologicalSpace E]
    (F : ℕ → Finset (Set α))
    (P : BlockIndex F)
    (d : ParentIndex F P → E) : E :=
  ∑' Q : ParentIndex F P, d Q


/--
Notation for summing over descendants.

`∑⁺ Q ∈ᵇ F below P, d Q`

means

`∑' Q : ChildIndex F P, d Q`.
-/
syntax "∑⁺ " ident " ∈ᵇ " term " below " term ", " term : term

macro_rules
  | `(∑⁺ $Q:ident ∈ᵇ $F below $P, $body) =>
      `(childTsum $F $P (fun $Q => $body))


/--
Notation for summing over ancestors.

`∑⁻ Q ∈ᵇ F above P, d Q`

means

`∑' Q : ParentIndex F P, d Q`.
-/
syntax "∑⁻ " ident " ∈ᵇ " term " above " term ", " term : term

macro_rules
  | `(∑⁻ $Q:ident ∈ᵇ $F above $P, $body) =>
      `(parentTsum $F $P (fun $Q => $body))


/-
Tensor-style notation.

The expression

`∑⊗ᵇ[F] c P ⊗ d Q ⊗ e R`

expands to

`∑ᵇ P ∈ᵇ F,
 ∑ᵇ Q ∈ᵇ F,
 ∑ᵇ R ∈ᵇ F,
 (c P * d Q) * e R`.

The expression

`∑⊗ᵇ[F] c P ⊗ d P⁺`

expands to

`∑ᵇ P ∈ᵇ F,
 ∑⁺ Q ∈ᵇ F below P,
 c P * d Q`.

The expression

`∑⊗ᵇ[F] c P ⊗ d P⁻`

expands to

`∑ᵇ P ∈ᵇ F,
 ∑⁻ Q ∈ᵇ F above P,
 c P * d Q`.

The symbol `⊗` is only notation here. It expands to multiplication `*`.
-/

declare_syntax_cat blockTensorFactors

syntax ident ident : blockTensorFactors
syntax ident ident "⁺" : blockTensorFactors
syntax ident ident "⁻" : blockTensorFactors

syntax ident ident " ⊗ " blockTensorFactors : blockTensorFactors
syntax ident ident "⁺" " ⊗ " blockTensorFactors : blockTensorFactors
syntax ident ident "⁻" " ⊗ " blockTensorFactors : blockTensorFactors

syntax "∑⊗ᵇ[" term "] " blockTensorFactors : term

syntax "blockTensorSum%(" term ", " blockTensorFactors ")" : term
syntax "blockTensorTail%(" term ", " term ", " blockTensorFactors ")" : term

macro_rules
  | `(∑⊗ᵇ[$F] $xs:blockTensorFactors) =>
      `(blockTensorSum%($F, $xs))

  /- First factor: it must be an ordinary block index. -/
  | `(blockTensorSum%($F:term, $c:ident $P:ident)) =>
      `(∑ᵇ $P ∈ᵇ $F, $c $P)

  | `(blockTensorSum%($F:term, $c:ident $P:ident ⊗ $rest:blockTensorFactors)) =>
      `(∑ᵇ $P ∈ᵇ $F,
        blockTensorTail%($F, ($c $P), $rest))

  /- Ordinary next factor. -/
  | `(blockTensorTail%($F:term, $acc:term, $d:ident $Q:ident)) =>
      `(∑ᵇ $Q ∈ᵇ $F,
        $acc * ($d $Q))

  | `(blockTensorTail%($F:term, $acc:term, $d:ident $Q:ident ⊗ $rest:blockTensorFactors)) =>
      `(∑ᵇ $Q ∈ᵇ $F,
        blockTensorTail%($F, ($acc * ($d $Q)), $rest))

  /- Descendant factor: `d P⁺`. -/
  | `(blockTensorTail%($F:term, $acc:term, $d:ident $P:ident⁺)) =>
      `(∑⁺ Qchild ∈ᵇ $F below $P,
        $acc * ($d (ChildIndex.toBlockIndex Qchild)))

  | `(blockTensorTail%($F:term, $acc:term, $d:ident $P:ident⁺ ⊗ $rest:blockTensorFactors)) =>
      `(∑⁺ Qchild ∈ᵇ $F below $P,
        blockTensorTail%($F, ($acc * ($d (ChildIndex.toBlockIndex Qchild))), $rest))

  /- Ancestor factor: `d P⁻`. -/
  | `(blockTensorTail%($F:term, $acc:term, $d:ident $P:ident⁻)) =>
      `(∑⁻ Qparent ∈ᵇ $F above $P,
        $acc * ($d (ParentIndex.toBlockIndex Qparent)))

  | `(blockTensorTail%($F:term, $acc:term, $d:ident $P:ident⁻ ⊗ $rest:blockTensorFactors)) =>
      `(∑⁻ Qparent ∈ᵇ $F above $P,
        blockTensorTail%($F, ($acc * ($d (ParentIndex.toBlockIndex Qparent))), $rest))


section Examples

variable
    {α : Type u}
    {E : Type v}
    [AddCommMonoid E]
    [TopologicalSpace E]
    [Mul E]

/--
Basic global block-sum notation.
-/
example
    (F : ℕ → Finset (Set α))
    (c : BlockIndex F → E) :
    (∑ᵇ P ∈ᵇ F, c P)
      =
    blockTsum F c := by
  rfl

/--
Expanded form of the global block sum.
-/
example
    (F : ℕ → Finset (Set α))
    (c : BlockIndex F → E) :
    (∑ᵇ P ∈ᵇ F, c P)
      =
    (∑' k : ℕ, (F k).attach.sum fun P => c ⟨k, P.1, P.2⟩) := by
  rfl

/--
Explicit descendant sum.
-/
example
    (F : ℕ → Finset (Set α))
    (P : BlockIndex F)
    (d : BlockIndex F → E) :
    (∑⁺ Q ∈ᵇ F below P, d (ChildIndex.toBlockIndex Q))
      =
    (∑' Q : ChildIndex F P, d (ChildIndex.toBlockIndex Q)) := by
  rfl

/--
Explicit ancestor sum.
-/
example
    (F : ℕ → Finset (Set α))
    (P : BlockIndex F)
    (d : BlockIndex F → E) :
    (∑⁻ Q ∈ᵇ F above P, d (ParentIndex.toBlockIndex Q))
      =
    (∑' Q : ParentIndex F P, d (ParentIndex.toBlockIndex Q)) := by
  rfl

/--
Two independent block indices.
-/
example
    (F : ℕ → Finset (Set α))
    (c d : BlockIndex F → E) :
    (∑⊗ᵇ[F] c P ⊗ d Q)
      =
    (∑ᵇ P ∈ᵇ F,
      ∑ᵇ Q ∈ᵇ F,
      c P * d Q) := by
  rfl

/--
Three independent block indices.
-/
example
    (F : ℕ → Finset (Set α))
    (c d e : BlockIndex F → E) :
    (∑⊗ᵇ[F] c P ⊗ d Q ⊗ e R)
      =
    (∑ᵇ P ∈ᵇ F,
      ∑ᵇ Q ∈ᵇ F,
      ∑ᵇ R ∈ᵇ F,
      (c P * d Q) * e R) := by
  rfl

/--
A descendant factor: `d P⁺`.

This means that the second index ranges over descendants of `P`.
-/
example
    (F : ℕ → Finset (Set α))
    (c d : BlockIndex F → E) :
    (∑⊗ᵇ[F] c P ⊗ d P⁺)
      =
    (∑ᵇ P ∈ᵇ F,
      ∑⁺ Q ∈ᵇ F below P,
      c P * d (ChildIndex.toBlockIndex Q)) := by
  rfl

/--
An ancestor factor: `d P⁻`.

This means that the second index ranges over ancestors of `P`.
-/
example
    (F : ℕ → Finset (Set α))
    (c d : BlockIndex F → E) :
    (∑⊗ᵇ[F] c P ⊗ d P⁻)
      =
    (∑ᵇ P ∈ᵇ F,
      ∑⁻ Q ∈ᵇ F above P,
      c P * d (ParentIndex.toBlockIndex Q)) := by
  rfl

/--
A mixed expression: one descendant factor and one ancestor factor.
-/
example
    (F : ℕ → Finset (Set α))
    (c d e : BlockIndex F → E) :
    (∑⊗ᵇ[F] c P ⊗ d P⁺ ⊗ e P⁻)
      =
    (∑ᵇ P ∈ᵇ F,
      ∑⁺ Qchild ∈ᵇ F below P,
      ∑⁻ Qparent ∈ᵇ F above P,
      (c P * d (ChildIndex.toBlockIndex Qchild)) *
        e (ParentIndex.toBlockIndex Qparent)) := by
  rfl

/--
A dependent variation: after binding `Q`, one can use `Q⁺`.
-/
example
    (F : ℕ → Finset (Set α))
    (c d e : BlockIndex F → E) :
    (∑⊗ᵇ[F] c P ⊗ d Q ⊗ e Q⁺)
      =
    (∑ᵇ P ∈ᵇ F,
      ∑ᵇ Q ∈ᵇ F,
      ∑⁺ Qchild ∈ᵇ F below Q,
      (c P * d Q) * e (ChildIndex.toBlockIndex Qchild)) := by
  rfl

end Examples
