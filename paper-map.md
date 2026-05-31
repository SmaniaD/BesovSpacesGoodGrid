# Paper Map

This file maps the published paper

Daniel Smania, *Besov-ish spaces through atomic decomposition*,
Analysis & PDE 15 (2022), no. 1

to the current Lean formalization in this repository.  The numbering below follows
the final published version of the article, not the older preprint numbering.

Status labels:

- `proved`: there is a Lean theorem or definition covering the item.
- `partial`: the main infrastructure exists, but the published statement is not yet
  formalized as a matching theorem.
- `not started`: no substantial Lean formalization is currently present here.
- `external`: the topic is expected to come from another library or repository.
- `documentation`: mathematical motivation or notation rather than a formal target.

## Published Table of Contents

| Paper section | Title | Current Lean status |
|---|---|---|
| 1 | Introduction | documentation |
| 2 | Notation | partial |
| Part I | Divide and rule | partial |
| 3 | Measure spaces and grids | partial |
| 4 | A bag of tricks | partial |
| 5 | Atoms | proved |
| 6 | Besov-ish spaces | partial |
| 7 | Scales of spaces | partial |
| 8 | Transmutation of atoms | proved for the needed form |
| 9 | Good grids | proved |
| 10 | Induced spaces | partial |
| 11 | Examples of classes of atoms | partial |
| Part II | Spaces defined by Souza's atoms | partial |
| 12 | Besov spaces in a measure space with a good grid | partial |
| 13 | Positive cone | not started |
| 14 | Unbalanced Haar wavelets | external / not started here |
| 15 | Alternative characterizations, I: Messing with norms | not started |
| 16 | Alternative characterizations, II: Messing with atoms | partial; Proposition 16.1 is proved |
| 17 | Dirac's approximations | not started |
| Part III | Applications | not started |
| 18 | Pointwise multipliers acting on \(B^s_{p,q}\) | not started |
| 19 | \(B^s_{p,q} \cap L^\infty\) is a quasialgebra | not started |
| 20 | A remarkable description of \(B^s_{1,1}\) | not started |
| 21 | Left compositions | not started |

## Main Formalization Anchors

| Paper item | Mathematical content | Lean item | File | Status |
|---|---|---|---|---|
| Section 3 | Weak grids and overlap control | `WeakGridSpace.WeakGrid`, `WeakGridSpace.WeakGridSpace` | `BesovSpacesGoodGrid/WeakGrid/Definition.lean` | partial |
| Section 5 | Classes of \((s,p,u)\)-atoms and assumptions A1-A7 | `WeakGridSpace.LocalVectorSpace`, `WeakGridSpace.AtomFamily` | `BesovSpacesGoodGrid/WeakGrid/Atoms.lean` | proved |
| Section 6 | Besov-ish spaces defined by atomic decompositions | `WeakGridSpace.BesovishSpace`, `WeakGridSpace.LpGridRepresentation`, `WeakGridSpace.Norm_Costpq` | `BesovSpacesGoodGrid/WeakGrid/BesovishSpaces.lean` | partial |
| Proposition 6.1 | Embedding of Besov-ish spaces in \(L^p\) | Besov-ish embedding and cost-norm API | `BesovSpacesGoodGrid/WeakGrid/BesovishSpaces.lean` | partial |
| Propositions 6.3-6.7 | Limit representation, completeness, compactness mechanisms | `representation_limit`, `representation_limit_strong`, `representation_limit_strong_existence`, `representation_limit_weak_existence`, `besovishSpace_costNorm_completeSpace` | `BesovSpacesGoodGrid/WeakGrid/Completeness.lean` | partial |
| Proposition 7.1 | Scale inclusions for different smoothness parameters | `smoothnessScaleBesovishSpace_subset`, `smoothnessScaleBesovishSpaceInclusion_Norm_Costpq_le` | `BesovSpacesGoodGrid/WeakGrid/Scales.lean` | partial |
| Proposition 8.1 | Transmutation of atoms | `Transmutation_of_Atoms_Claim_A`, `Transmutation_of_Atoms_Claim_B`, `Transmutation_of_Atoms_Claim_C_explicit`, `Transmutation_of_Atoms_continuous_embedding_explicit` | `BesovSpacesGoodGrid/WeakGrid/Transmutation.lean` | proved for the current use |
| Section 9 | Good grids and their constants | `GoodGridSpace.GoodGrid`, `GoodGridSpace.GoodGridSpace` | `BesovSpacesGoodGrid/GoodGrid/Definition.lean` | proved |
| Section 10 | Induced grids and induced atomic decompositions | `inducedWeakGrid`, `inducedWeakGridSpace`, `inducedRepresentationToAmbient` | `BesovSpacesGoodGrid/WeakGrid/InducedGrid.lean` | partial |
| Section 11A | Souza atoms | `GoodGridSpace.IsSouzaAtom`, `GoodGridSpace.souzaAtomFamily` | `BesovSpacesGoodGrid/GoodGrid/BesovSpace.lean` | proved |
| Sections 11B-11C | Holder atoms and bounded variation atoms | none | none | not started |
| Section 12 | Souza Besov spaces on a good grid | `GoodGridSpace.SouzaBesovSpace` | `BesovSpacesGoodGrid/GoodGrid/BesovSpace.lean` | partial |
| Section 12 | Compactness and density for Souza Besov spaces | `souzaBesovSpace_costNorm_completeSpace`, `souza_closedCostBallInLp_isCompact`, `souza_closedCostBallInL1_isCompact`, `souzaBesovSpace_dense`, `souzaBesovSpace_dense_inL1` | `BesovSpacesGoodGrid/GoodGrid/BesovSpace.lean` | proved |
| Proposition 16.1 | Souza atoms and Besov atoms define the same Besov space under the sandwich hypotheses | `atoms_between_souza_atoms_and_besov_atoms` | `BesovSpacesGoodGrid/GoodGrid/BesovAtoms.lean` | proved |
| Claim inside Proposition 16.1 | A Besov atom has a Souza-atom representation with geometric decay | `besovAtom_to_souza_representation_decay`, `besovAtom_to_induced_souzaS_representation_decay_claimC` | `BesovSpacesGoodGrid/GoodGrid/BesovAtoms.lean` | proved |
| Propositions 16.2-16.3 | Holder atoms and bounded variation atoms as examples in Proposition 16.1 | none | none | not started |
| Sections 18-21 | Multiplier, quasialgebra, \(B^s_{1,1}\), and composition applications | none | none | not started |

## Proposition 16.1: Current Completed Bridge

The most important completed theorem is the formal version of Proposition 16.1,
which compares Souza atoms, an intermediate atom family, and Besov atoms.

In paper notation, the proposition assumes a good grid \(\mathcal P\), a class
\(\mathcal A\) of \((s,p,u)\)-atoms, \(s < \beta\), and constants \(C_1,C_2 > 0\)
such that, for every \(Q \in \mathcal P\),

\[
\frac{1}{C_1}\mathcal A^{sz}_{s,p}(Q)
  \subset \mathcal A(Q)
  \subset C_2\mathcal A^{bs}_{s,\beta,p,\tilde q}(Q).
\]

The formal theorem is

```lean
GoodGridSpace.atoms_between_souza_atoms_and_besov_atoms
```

and it proves the continuous comparison of the corresponding Besov-ish spaces,
using the explicit Claim C transmutation theorem.

The internal geometric-decay claim from the proof is formalized as

```lean
GoodGridSpace.besovAtom_to_souza_representation_decay
GoodGridSpace.besovAtom_to_induced_souzaS_representation_decay_claimC
```

The paper's decay estimate has the form

\[
\left(\sum_{\substack{P \in \mathcal P^k\\P\subset J}} |m_P|^p\right)^{1/p}
  \leq C \lambda^{(k-j)(\beta-s)}.
\]

In Lean this estimate is packaged in the representation format required by
`Transmutation_of_Atoms_Claim_C_explicit`.

## Next Formalization Targets

The natural next target is Section 15 or the remaining examples in Section 16.

Section 16 is probably the most direct continuation:

1. Formalize the paper's Holder atom family from Section 11B.
2. Prove Proposition 16.2 by applying
   `atoms_between_souza_atoms_and_besov_atoms`.
3. Formalize the bounded variation atom family from Section 11C.
4. Prove Proposition 16.3 by the same sandwich strategy.

Section 15 is more structural:

1. Formalize the alternative norm appearing in Theorem 15.1.
2. Prove the comparison between the original Souza Besov cost norm and the
   alternative norm.
3. Derive Corollary 15.2.

The application sections, especially Sections 18 and 19, should probably wait
until Sections 15 and 16 are more complete, because they use the alternative
characterizations and atom comparisons heavily.
