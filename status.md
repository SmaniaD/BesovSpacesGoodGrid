# Status do PositiveCone

Arquivo principal: `BesovSpacesGoodGrid/GoodGrid/PositiveCone.lean`.

## Estado atual

- O arquivo ja contem os enunciados pedidos para:
  - decomposicao real `exists_souzaPositive_decomposition_of_aeRealValued`;
  - decomposicao complexa `exists_souzaPositive_decomposition_of_aeComplexValued`;
  - densidade do cone positivo de Souza-Besov em `C_+(beta)` na topologia forte de `L^beta`;
  - resultado sobre suporte como uniao enumeravel de celulas da good grid.
- Permanecem quatro `sorry`s nesse arquivo:
  - `exists_souzaPositive_decomposition_of_aeRealValued`;
  - `exists_souzaPositive_decomposition_of_aeComplexValued`;
  - `souzaPositiveCone_dense_in_LpNonnegativeCone`;
  - `support_ae_countable_iUnion_goodGridCells_of_souzaPositiveFunction`.
- Nenhum novo `sorry` foi adicionado nesta etapa.
- O ultimo `lake env lean BesovSpacesGoodGrid/GoodGrid/PositiveCone.lean` completo ainda falhava na canonicalizacao de um bloco de nivel. Depois disso foi adicionado o lema auxiliar
  `souzaAtomFamily_toFunction_eq_indicator`, mas o check seguinte foi interrompido antes de terminar. Portanto o estado atual ainda precisa ser verificado.

## O que ja foi encaminhado

- Foi introduzida a ideia correta para a prova real:
  primeiro substituir cada atomo local por um atomo Souza canonico positivo, absorvendo o escalar original no coeficiente.
- Foram adicionadas pecas auxiliares para isso:
  - `souzaLocalScalar`, para ver um elemento do `carrier` local como um escalar complexo;
  - `souzaAtomFamily_toFunction_eq_indicator`, para reduzir `toFunction` a uma indicadora constante;
  - `souzaCanonicalizedLevelBlock`, que troca os atomos de um bloco pelos atomos canonicos;
  - lemas pretendidos para preservar o valor em `L^p` e controlar os coeficientes.
- Tambem ja existem funcoes auxiliares para separar coeficientes:
  - partes positiva/negativa reais;
  - partes positiva/negativa das coordenadas real e imaginaria complexas;
  - decomposicao pontual de coeficiente complexo.

## Proximo passo imediato

1. Rodar:

   ```bash
   lake env lean BesovSpacesGoodGrid/GoodGrid/PositiveCone.lean
   ```

2. Fechar primeiro os erros locais em:
   - `souzaAtomFamily_toFunction_eq_indicator`, se houver problema de reducao;
   - `souzaCanonicalizedLevelBlock_toLp`, especialmente a igualdade
     `original atom = (bQ / aQ) • canonical atom`;
   - `souzaCanonicalizedLevelBlock_coeff_norm_le`, especialmente a cota
     `norm (new coeff) <= norm (old coeff)`.

3. Quando esses lemas compilarem, levantar de bloco para representacao:
   - definir `souzaCanonicalizedRepresentation`;
   - provar que ela representa o mesmo elemento;
   - provar que o custo nao aumenta;
   - provar que todos os atomos da representacao sao canonicos positivos.

## O que falta para fechar os teoremas principais

### Decomposicao real

- Escolher uma representacao Souza/standard quase otima de `f`.
- Usar a hipotese real-valued para obter coeficientes reais na representacao standard, ou provar esse fato para a representacao canonica.
- Separar os coeficientes em partes positiva e negativa.
- Construir duas representacoes positivas `u` e `v`.
- Provar `f = u - v`.
- Provar a cota quantitativa com uma constante `C`, usando a cadeia indicada:
  custo standard `<=` norma Haar `<= C *` norma de oscilacao `<=` gauge Besov de `f`.

### Decomposicao complexa

- Repetir a separacao nas coordenadas real e imaginaria.
- Construir `u`, `v`, `w`, `r` positivos.
- Provar `f = (u - v) + Complex.I • (w - r)`.
- Controlar as quatro normas positivas pela mesma constante, ou por uma constante uniforme maior.

### Densidade em `L^beta`

- Aproximar uma funcao nao negativa de `L^beta` por funcoes simples nao negativas.
- Aproximar/realizar essas funcoes simples por combinacoes finitas de atomos Souza canonicos positivos em celulas da good grid.
- Provar convergencia forte em `L^beta`.
- Concluir que todo elemento de `LpNonnegativeCone G beta` esta no fechamento de `SouzaPositiveConeInLbeta`.

### Suporte como uniao enumeravel de celulas

- A partir de uma representacao positiva, observar que cada bloco de nivel usa finitamente muitas celulas.
- A uniao sobre todos os niveis e enumeravel.
- Provar que, fora dessa uniao, todos os atomos somam zero quase sempre.
- Concluir a igualdade de suporte modulo conjunto nulo.

## Observacao de estilo

A direcao mais limpa continua sendo a sugerida: canonicalizar a representacao primeiro, depois separar apenas os coeficientes. Isso evita tentar provar positividade diretamente para atomos arbitrarios e deixa as cotas de custo reduzidas a desigualdades simples sobre coeficientes.
