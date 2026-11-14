# AGENTS.md

Shared guidance for coding agents working in this repository. This file combines the writing conventions from the former `AGENTS.md` with the consultation and proof-workflow guidance from `CLAUDE.md`.

## Contribution workflow

Follow [CONTRIBUTING.md](CONTRIBUTING.md) for contribution scope, mathematical restructuring, faithful Lean translation, reuse of existing results, and scientific and engineering review. Follow the user's agreed scope for each task.

## Markdown math

For Markdown containing mathematical notation, follow the [gh-markdown-math skill](.agents/skills/gh-markdown-math/SKILL.md) for rendering rules and the validation workflow. The repository-specific conventions and example skeleton below supplement that skill.

Additional notation and layout conventions:

- Use LaTeX commands for mathematical symbols: `\to`, `\neq`, `\geq`, `\leq`, `\in`, `\cdot`, `\top` for transpose, and `\blacksquare` for Q.E.D. Do not substitute plain ASCII such as `!=`, `>=`, `^T`, `sum`, or `alpha`.
- For multi-line derivations, use `\begin{aligned} ... \end{aligned}` in a display block with `&=` alignment. Follow the skill's rules for source-line layout and row separators.
- Group short related equations with `\qquad` on one display line instead of stacking many tiny blocks.

## Structure

- `#` for the theorem title, `##` for top-level sections (`Statement`, `Proof`, `Consequence`, etc.).
- Sub-theorems inside a proof use `###` with a period-separated title like `### Theorem 2. Antipode identities`. Never put an em dash in a heading.
- Inline mini-proofs use **bold run-in headers**: `**Proof.**`, `**Reason.**`, `**Claim.**`.
- Use blockquotes (`>`) for informal restatements or remarks that sit alongside the formal statement.
- Use ordered lists (`1.`, `2.`, ...) for enumerated cases and unordered lists (`-`) for bullet points.

## Prose

- No em dashes anywhere (user global rule). Use `,`, `;`, `:`, or `.` instead. No exceptions for headings, captions, or run-in labels.
- Italicize short emphases with `*...*`; bold with `**...**` for labels and run-in headers.
- Keep paragraphs short. Blank line between paragraphs, between display math and prose, and between list items that contain display math.

## Code and identifiers

- Use backticks only for: file names, directory paths, Lean identifiers, shell commands, and literal code snippets.
- Do **not** use backticks for mathematical variables or expressions. Those go in `$...$`.

## Example skeleton

```markdown
# Theorem Title

## Statement

Let $f : \lbrace 0,1\rbrace^n \to \lbrace 0,1\rbrace$. Suppose ...

$$ \text{main equation} $$

> **Equivalently.** Informal restatement.

## Proof

Prose lead-in.

### Theorem 1. Short name

**Claim.** Something.

**Proof.** Expand:

$$ \begin{aligned} X &= Y + Z \cr &= W. \end{aligned} $$

### Conclusion

Wrap up. $\blacksquare$

## Consequence

$$ H^{\ast}(f) \geq 2. $$
```

Apply this style to every file under `theorems/` and to
`artifacts/intro-materials/writeup.md`.

## Repository validation setup

The Markdown skill describes the checker and render audits. Keep these repository-specific setup notes here:

- **Local pre-commit hook:** optionally enable it with `git config core.hooksPath artifacts/hooks`. It lints the staged Markdown snapshot, so it does not check unstaged changes or files that have not been added.
- **CI:** the source branch uses `.gitlab-ci.yml` for static and KaTeX validation. That configuration has not been copied onto `clean`; do not assume a merge gate exists here. Once CI is restored, verify its configuration and project merge settings before relying on it.
- **Maintenance:** keep `artifacts/scripts/check_md_math.py` and the canonical rule catalogue in `.claude/skills/gh-markdown-math/SKILL.md` aligned when a new renderer issue is verified.

## Second opinions and consultation

Use a focused second opinion when it can resolve a concrete uncertainty:

- A bug remains after one or two unsuccessful attempts.
- Two non-obvious approaches need comparison.
- A difficult proof or implementation would benefit from an independent review.
- The user explicitly requests a cross-check.

Routine edits, formatting, and work whose correctness is already clear do not need a consultation. Treat suggested theorem names, library signatures, tactics, and constructions as candidates to check against the source and the actual proof goals.

## Proof development and long-running work

Use this loop for nontrivial Lean work:

1. Refine the natural-language argument and its dependencies.
2. Consult on a specific unresolved obstacle when useful.
3. Write or reuse the Lean proof, preserving the mathematical argument.
4. Build and check the affected code in the coordinating session.
5. Use the exact error and goal state to guide the next correction.
6. Confirm the resulting theorem matches the intended statement, and inspect proof completeness and validation results.

A successful build is necessary evidence; also check statement faithfulness and proof placeholders. Once the Lean package is present, `bash artifacts/scripts/validate.sh` provides the repository's build, placeholder, and axiom checks. It expects a `formalization` package and tracked Lean sources. Do not claim Lean validation while those prerequisites are absent.

When a build or check runs for a long time, use the environment's background or resumable-session support and keep track of its completion. A useful, independent uncertainty may be explored concurrently with a bounded consultation. Run that consultation in the background too and keep it read-only. For CLI consultations that take their prompt as an argument, redirect stdin from `/dev/null`. Do not manufacture questions to fill waiting time or let a consultation delay responding to a completed build.
