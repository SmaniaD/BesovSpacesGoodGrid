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

## Style
- Keep Lean proofs readable and local when possible.
- Prefer clear names and small lemmas over dense proof terms when that improves maintainability.
- Add docstrings to main definitions and theorems, explaining the content in a professional, polite but colloquial way. Avoid too much mathematical notation.
- Put a main comment at the top of each substantial file summarizing its main results.
- Suggest factoring a file into smaller topic-focused files when that would improve readability or compilation speed.
- Substantial files should expose a small number of public definitions or theorems. Most supporting results should be private or internal when possible.
- When creating a new file or repository, ask about its main goal and use that goal when deciding whether results should be public or private.
- The comments for public results must be superb, self-contained, and clear.
-When asked to explain the mathematics of the results, use MathJax when possible to render your answer
-Use f, g, h for functions. Do not use x and y and z for functions.
