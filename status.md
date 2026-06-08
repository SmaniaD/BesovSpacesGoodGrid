# Status atual

Este arquivo resume o estado recente dos arquivos centrais em
`BesovSpacesGoodGrid/GoodGrid`.

## Resultado recente: tail `selfs` implica `L∞` uniformemente em `t`

Arquivos principais:

- `BesovSpacesGoodGrid/GoodGrid/Multipliers/Definition.lean`
- `BesovSpacesGoodGrid/GoodGrid/Multipliers/MultipliersareBounded.lean`

O que foi provado recentemente:

- Foi adicionado o alias qualitativo
  `SouzaPointwiseSelfsTailClass`.
- Foi provada uma versao eventual do passo de martingal:
  `ae_le_of_eventually_goodGridLevelAverage_le`.
  Ela permite usar cotas de medias de nivel apenas para `n >= t`.
- Foram provadas as estimativas locais tail, com a mesma constante da teoria
  global:
  - produto do multiplicador com o atomo Souza canonico;
  - `MemLp` local de `Q.cell.indicator m`;
  - cota local de `eLpNorm` em expoente `p`;
  - cota local de `eLpNorm` em expoente `1`;
  - cota da integral de `‖m‖` em uma celula tail.
- Foi provado:

  ```lean
  souzaPointwiseSelfsTailBound_norm_ae_le
  ```

  isto e,
  \[
    \|m(x)\|
    \le
    C(G,s,p,q)\, C_{\mathrm{tail}}
    \quad\text{para quase todo }x.
  \]

- Foi provado tambem o enunciado com a seminorma tail exata:

  ```lean
  souzaPointwiseSelfsTailNorm_norm_ae_le
  ```

  isto e,
  \[
    \|m(x)\|
    \le
    C(G,s,p,q)\,
    |m|_{\mathcal B^{s,t}_{p,q,\mathrm{selfs}}}
    \quad\text{para quase todo }x,
  \]
  com constante independente de `t`.
- Tambem foi adicionada a forma qualitativa:

  ```lean
  souzaPointwiseSelfsTailClass_norm_ae_bounded
  ```

## PositiveCone.lean

Arquivo principal:

- `BesovSpacesGoodGrid/GoodGrid/PositiveCone.lean`

Estado atual:

- O arquivo nao tem mais `sorry`.
- O arquivo compila com:

  ```bash
  lake env lean BesovSpacesGoodGrid/GoodGrid/PositiveCone.lean
  ```

- A checagem ainda emite alguns warnings de linter, todos estilisticos:
  `try simp instead of simpa` e alguns argumentos de `simp` nao usados.

Teoremas principais agora presentes sem `sorry`:

- `exists_souzaPositive_decomposition_of_aeRealValued`
- `exists_souzaPositive_decomposition_of_aeComplexValued`
- `souzaPositiveCone_dense_in_LpNonnegativeCone`
- `support_ae_countable_iUnion_goodGridCells_of_souzaPositiveFunction`

Matematicamente, a parte de decomposicao positiva real/complexa foi fechada:
funcoes real-valued admitem decomposicao em diferenca de funcoes positivas,
e funcoes complexas admitem a decomposicao pelas partes real e imaginaria.

## NonArchimedeanProperty.lean

Arquivo principal:

- `BesovSpacesGoodGrid/GoodGrid/Multipliers/NonArchimedeanProperty.lean`

Estado atual:

- O arquivo compila com:

  ```bash
  lake env lean BesovSpacesGoodGrid/GoodGrid/Multipliers/NonArchimedeanProperty.lean
  ```

- Ha dois `sorry`s, em:

  ```lean
  souzaNonArchimedeanPropertyLambdaInfinite
  souzaNonArchimedeanPropertyPositiveCone
  ```

- A versao finita principal nao positiva ja esta provada:

  ```lean
  souzaNonArchimedeanPropertyLambdaFinite
  ```

O que ela diz, em termos matematicos:

se
\[
  0 < s < \beta < 1/p,
\]
uma familia finita \(g_i\) tem controle tail `selfs`, e uma representacao Souza
de \(f\) satisfaz as hipoteses de separacao A e B, entao
\[
  \Big(\sum_{i\in\Lambda} g_i\Big)f
\]
tem uma representacao Souza cujo custo e controlado por
\[
  C_{\mathrm{gen}}\,N\,\operatorname{cost}(R).
\]

- A versao infinita ja esta enunciada em forma pontual/Besov:

  ```lean
  souzaNonArchimedeanPropertyLambdaInfinite
  ```

  Ela usa a lemma auxiliar
  `exists_nonArchimedeanInfinite_pointwise_hasSum`, que isola a parte pontual.
  Essa lemma auxiliar agora esta provada sem `sorry`.  A conclusao diz que
  existe uma funcao concreta `h` tal que, para quase todo ponto `z` com
  `f z ≠ 0`, a serie absoluta
  \[
    \sum_{i\in\Lambda} |g_i(z)|
  \]
  tem soma `absSum z` e satisfaz `absSum z <= Cgen * N`.  Alem disso, para
  quase todo `z`, a serie complexa
  \[
    \sum_{i\in\Lambda} g_i(z) f(z)
  \]
  tem soma `h z`.

  A mesma lemma pontual agora tambem prova:

  ```lean
  ∃ hmem : MemLp h p G.toWeakGridSpace.measure,
    ‖MemLp.toLp h hmem‖ ≤
      Cgen * N * ‖(x : Lp ℂ p G.toWeakGridSpace.measure)‖
  ```

  A prova de `h ∈ Lp` foi fechada mostrando primeiro que `h` e
  `AEStronglyMeasurable`, como limite quase sempre dos produtos parciais
  finitos.  Cada produto parcial e mensuravel porque a versao finita
  `souzaNonArchimedeanPropertyLambdaFinite` fornece um representante em `Lp`.
  A condicao A infinita com `HasSum` e nao-negatividade dos termos relevantes
  fornece a condicao A finita para cada truncacao.

  Finalmente, a versao publica infinita ainda afirma que `h` e representada por
  um elemento Souza-Besov com uma representacao `S` de custo finito e
  `pqCost S <= Cgen * N * pqCost R`.

- A versao infinita atual nao inclui mais uma hipotese separada de cauda
  uniforme.  Toda a informacao global esta concentrada na condicao A infinita,
  agora formalizada com uma soma testemunhada:
  `HasSum (fun i : {i // i ∈ Λ} =>
    nonArchimedeanRelevantTailSelfsInfiniteTerm ... Q i) T` e `T <= N` em
  cada celula ativa da representacao fixa `R`.
- A constante da versao infinita e escolhida com `0 <= Cgen` e `1 <= Cgen`,
  para poder absorver simultaneamente a constante da parte pontual e a
  constante da parte Besov.

## O que falta provar

Os `sorry`s localizados nos arquivos centrais checados sao:

```lean
souzaNonArchimedeanPropertyLambdaInfinite
souzaNonArchimedeanPropertyPositiveCone
```

O que falta matematicamente para a versao infinita:

- A parte pontual da versao infinita ja esta provada:
  soma absoluta quase sempre, soma complexa quase sempre, cota pontual
  `‖h z‖ <= Cgen * N * ‖f z‖`, pertencimento a `Lp`, e cota
  `‖h‖_Lp <= Cgen * N * ‖x‖_Lp`.
- Usar completude/fechamento adequado para obter o limite no espaco Besov/Lp.
- Construir uma representacao Souza `S` de `h` com custo finito e passar a
  cota `pqCost S <= Cgen * N * pqCost R`.

O que ainda falta matematicamente para essa versao positiva:

- Usar a versao positiva do tail bound:
  `SouzaPositivePointwiseSelfsTailBound`.
- Produzir uma representacao do produto que preserve positividade dos atomos e
  coeficientes.
- Controlar o suporte da nova representacao, mostrando que cada celula ativa de
  saida fica dentro do suporte de algum \(g_i\).
- Converter a soma positiva em `ℝ≥0∞` para uma cota real compatível com o custo
  `pqCost`.
- Reutilizar, tanto quanto possivel, a infraestrutura ja provada para
  `souzaNonArchimedeanProperty`, especialmente os casos `N = 0` e `N > 0`.

## Checks recentes

Passaram:

```bash
lake env lean BesovSpacesGoodGrid/GoodGrid/Multipliers/Definition.lean
lake env lean BesovSpacesGoodGrid/GoodGrid/Multipliers/MultipliersareBounded.lean
lake env lean BesovSpacesGoodGrid/GoodGrid/Multipliers.lean
lake env lean BesovSpacesGoodGrid/GoodGrid/PositiveCone.lean
lake env lean BesovSpacesGoodGrid/GoodGrid/Multipliers/NonArchimedeanProperty.lean
```

Busca por `sorry` nos arquivos centrais checados:

```bash
rg -n "\bsorry\b" \
  BesovSpacesGoodGrid/GoodGrid/PositiveCone.lean \
  BesovSpacesGoodGrid/GoodGrid/Multipliers/NonArchimedeanProperty.lean \
  BesovSpacesGoodGrid/GoodGrid/Multipliers/MultipliersareBounded.lean \
  BesovSpacesGoodGrid/GoodGrid/Multipliers/Definition.lean
```

Resultado: apenas os `sorry`s de
`souzaNonArchimedeanPropertyLambdaInfinite` e
`souzaNonArchimedeanPropertyPositiveCone`.
