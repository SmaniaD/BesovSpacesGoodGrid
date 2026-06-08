# AGENTS.md

## Project Directives
- Prefer minimal, focused changes.
- Follow existing project patterns before adding new abstractions or dependencies.
- Avoid unrelated refactors and generated-file churn.
- Treat user changes in the working tree as intentional unless explicitly told otherwise.
- Make the code as reusable for other projects as possible. It should be readable and easy to reuse.
- Follow Mathlib Style Guidelines: https://leanprover-community.github.io/contribute/style.html
- Do not add axioms or admits. Add `sorry` only when appropriate to divide the task into subproblems, and after the run report which sorries you added.

## Moral Directives
- Be honest. Do not use hacks or bugs to prove something in Lean that is not mathematically honest.
- Do not add additional assumptions to the main theorems and definitions without asking for permission.
- You may fix typos, but mention them in the final response.

## Commands
- Build: `lake build`
- Check a file: `lake env lean <path>`
- Diagnose slow Lean files or declarations with localized profiling: add `set_option profiler true` near the problematic declaration and then run `lake env lean <path>`.

## Style
- Keep Lean proofs readable and local when possible.
- Prefer clear names and small lemmas over dense proof terms when that improves maintainability.
- Add docstrings to main definitions and theorems, explaining the content in a professional, polite but colloquial way. Avoid too much mathematical notation.
- Put a main comment at the top of each substantial file summarizing its main results.
- Suggest factoring a file into smaller topic-focused files when that would improve readability or compilation speed.
- Substantial files should expose a small number of public definitions or theorems. Most supporting results should be private or internal when possible.
- When creating a new file or repository, ask about its main goal and use that goal when deciding whether results should be public or private.
- The comments for public results must be superb, self-contained, and clear.
- When asked to explain the mathematics of the results, use MathJax when possible to render your answer.
- Use `f`, `g`, `h` for functions. Do not use `x`, `y`, and `z` for functions.

## Lean Performance / Heartbeat Directives
- In Lean proofs, avoid broad `simp`, `simpa`, `aesop`, `omega`, `linarith`, or other expensive automation in goals involving heavy dependent types, coercions, `Lp`, `Measure`, `ENNReal`, `ae`/`a.e.`, filters, grids, representations, or project-specific structures.
- Prefer `change ...` followed by `exact ...` when two goals are definitionally equal. Do not use `simpa` merely to bridge definitional equalities involving local abbreviations such as `let μ := ...`, `let A := ...`, or coercions from structured objects.
- Prefer `simp only [...]` or `simpa only [...]` over `simp [...]` or `simpa [...]`. Keep the simplification set explicit and small.
- When using `simpa`, first try to make all major implicit arguments explicit, especially `(μ := ...)`, `(p := ...)`, `(q := ...)`, `(G := ...)`, `(f := ...)`, `(g := ...)`, `(u := ...)`, `(uLim := ...)`, and filter arguments.
- Avoid writing goals where Lean must infer coercions from structured objects to functions. For `Lp`, `BesovishSpace`, grid representations, and similar objects, introduce explicitly typed local abbreviations such as:
  ```lean
  let μ := G.toWeakGridSpace.measure
  let A := souzaAtomFamily G s p hs hp hp_top
  let fLp : ℕ → Lp ℂ p μ := fun n => ...
  ```
  Then state intermediate facts using these abbreviations.
- For convergence in measure, almost-everywhere convergence, or pointwise convergence of `Lp` representatives, write the coerced functions explicitly:
  ```lean
  fun n z => u n z
  fun z => uLim z
  ```
  rather than relying on Lean to infer coercions from `u : ℕ → Lp ℂ p μ` or `uLim : Lp ℂ p μ`.
- Avoid type ascriptions such as:
  ```lean
  have h : TendstoInMeasure μ u l v := ...
  ```
  when `u` and `v` are structured objects with coercions. Instead, state the function-level form explicitly:
  ```lean
  have h :
      TendstoInMeasure μ
        (fun n z => u n z)
        l
        (fun z => v z) := by
    ...
  ```
- When constructing existential witnesses, provide the witnesses explicitly before proving dependent fields. Prefer:
  ```lean
  refine ⟨witness₁, witness₂, ?_, ?_⟩
  ```
  over leaving witnesses as metavariables that later have to be inferred from dependent hypotheses.
- In final proof steps, avoid `simpa using h` if the goal contains dependent coercions or project-specific structures. Prefer:
  ```lean
  change ExpectedType
  exact h
  ```
- If a proof times out or consumes many heartbeats, do not increase `maxHeartbeats` as the first response. First try:
  1. making implicit arguments explicit;
  2. replacing broad `simpa` with `change`/`exact`;
  3. replacing `simp` with `simp only`;
  4. introducing typed local abbreviations;
  5. splitting the proof into small private lemmas.
- Use `set_option profiler true` or localized `set_option maxHeartbeats ... in` only for diagnosis. Do not leave large heartbeat increases in committed code unless explicitly justified in the final report.
- After modifying a Lean proof, check the affected file with:
  ```bash
  lake env lean <path>
  ```
  and report any remaining slow declarations, added `sorry`s, or heartbeat-related workarounds.
