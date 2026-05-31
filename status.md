# Status do repositório

Branch atual: `Atomliner`

Última verificação: `lake build` passa com sucesso.

## Objetivo principal

Formalizar a comparação entre o espaço de Besov construído com átomos de Souza
e o espaço construído com átomos de Besov em uma boa grade.  O alvo principal
atual é completar `GoodGrid/BesovAtoms.lean`, especialmente o teorema
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
- `convex_isBesovAtom` está provado usando adição de representações e a
  desigualdade triangular do custo `pq`.
- `isBesovAtom_smul_of_norm_eq_one` está provado usando escala de
  representações e invariância do custo por escalares de norma um.
- `besovAtom_is_sp_one_atom` agora é uma consequência curta de
  `isBesovAtom_eLpNorm_le`.
- `isBesovAtom_eLpNorm_le` está provado: a prova aplica o embedding no grid
  induzido, controla o coeficiente induzido pela constante geométrica com o
  expoente conjugado `qtilde'`, e converte a cota real de volta para `ℝ≥0∞`.
- `besovAtom_to_souza_representation_decay` está provado: para um átomo de
  Besov em `Q`, a representação induzida de Souza-`β` tem coeficientes
  rescalados `c_P μ(P)^(β-s)` com decaimento geométrico
  `lambda2^(k(β-s))`, exatamente a conta usada no Claim de transmutação.
- Também foram adicionados os blocos auxiliares que convertem um bloco ou uma
  representação Souza-`β` em Souza-`s` sem alterar o elemento de `Lp`.
- O Claim C de transmutação agora tem uma interface explícita para a constante:
  `transmutationClaimCEmbeddingConstant`,
  `Transmutation_of_Atoms_Claim_C_explicit`, e
  `Transmutation_of_Atoms_continuous_embedding_explicit`. Os wrappers
  existenciais antigos de `Transmutation_of_Atoms_Claim_C` e
  `Transmutation_of_Atoms_continuous_embedding` foram removidos. A
  constante de Claim C já está simplificada no caso identidade: os fatores
  `lambda^0` e `ceil(1)^(1/q)` foram removidos da definição pública.
- A constante `besovAtomConstant` foi corrigida para usar o expoente conjugado
  `qtilde'` na parte geométrica, enquanto `qtilde` continua sendo o expoente do
  custo dos coeficientes.
- Foi adicionada a hipótese natural `[Fact (1 ≤ qtilde)]` onde `besovAtomFamily`
  é usado, para evitar o caso degenerado `qtilde = 0` no custo dos coeficientes.

## O que falta fazer

Em `BesovSpacesGoodGrid/GoodGrid/BesovAtoms.lean`, ainda faltam os seguintes
sublemas/teoremas:

- `souza_atoms_and_besov_atoms`: completar a comparação principal entre os
  espaços.

## Próximos passos sugeridos

1. Atacar `souza_atoms_and_besov_atoms` via o argumento de transmutação já
   existente em `WeakGrid/Transmutation.lean`.

## Observações

- O build passa apesar dos `sorry`s restantes.
- Não há mudanças pendentes fora do escopo dos arquivos de átomos/estrutura local.
- O ponto técnico mais delicado restante é empacotar a comparação principal dos
  espaços usando os resultados de transmutação já disponíveis.
