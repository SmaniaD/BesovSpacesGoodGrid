# Status do repositório

Branch atual: `Atomliner`

Última verificação: `lake build` passa com sucesso.

## Objetivo principal

Formalizar a comparação entre o espaço de Besov construído com átomos de Souza
e o espaço construído com átomos de Besov em uma boa grade.  O alvo principal
atual é completar `GoodGridBesovAtoms.lean`, especialmente o teorema
`souza_atoms_and_besov_atoms`.

Em termos matemáticos, queremos provar que uma família de átomos situada entre
os átomos de Souza e os átomos de Besov gera o mesmo espaço de Besov, com as
cotas normativas esperadas.

## Estado atual

- `LocalBanachSpace` foi renomeado para `LocalVectorSpace`.
- `LocalVectorSpace` agora exige apenas estrutura de espaço vetorial complexo:
  `AddCommGroup` e `Module ℂ`.
- `besovAtomFamily` já está definido como uma `AtomFamily`.
- O carrier local dos átomos de Besov é o subespaço de funções concretas
  `a : α → ℂ` que são `MemLp a p μ` e são suportadas na célula.
- `IsBesovAtom` é um predicado sobre representantes concretos, usando a classe
  `Lp` via uma prova existencial de `MemLp`.
- `zero_isBesovAtom` está provado.
- Foi adicionada a hipótese natural `[Fact (1 ≤ qtilde)]` onde `besovAtomFamily`
  é usado, para evitar o caso degenerado `qtilde = 0` no custo dos coeficientes.

## O que falta fazer

Em `BesovSpacesGoodGrid/GoodGridBesovAtoms.lean`, ainda faltam os seguintes
sublemas/teoremas:

- `convex_isBesovAtom`: provar que os átomos de Besov formam um conjunto convexo.
- `isBesovAtom_smul_of_norm_eq_one`: provar invariância por escalares complexos
  de módulo um.
- `isBesovAtom_eLpNorm_le`: provar que a normalização de Besov implica a cota
  ordinária de átomo `(s,p,1)`.
- `besovAtom_is_sp_one_atom`: conectar a cota anterior ao campo `atom_bound` da
  família empacotada.
- `souza_atoms_and_besov_atoms`: completar a comparação principal entre os
  espaços.

## Próximos passos sugeridos

1. Provar lemas gerais em `WeakGridBesovishSpaces.lean` para transportar
   `LpGridRepresentation` por soma convexa e por escalares de módulo um.
2. Usar esses lemas para fechar `convex_isBesovAtom` e
   `isBesovAtom_smul_of_norm_eq_one`.
3. Provar a estimativa analítica `isBesovAtom_eLpNorm_le` a partir da
   representação induzida e da constante `besovAtomConstant`.
4. Substituir `besovAtom_is_sp_one_atom` por uma prova curta usando
   `isBesovAtom_eLpNorm_le`.
5. Atacar `souza_atoms_and_besov_atoms` via o argumento de transmutação já
   existente em `WeakGridTransmutation.lean`.

## Observações

- O build passa apesar dos `sorry`s restantes.
- Não há mudanças pendentes fora do escopo dos arquivos de átomos/estrutura local.
- O ponto técnico mais delicado continua sendo a relação entre representantes
  concretos `α → ℂ` e classes em `Lp`.
