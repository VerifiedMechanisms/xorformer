# How many attention heads does it take to compute a Boolean function?

We study the expressivity of single-layer, attention-only transformers: how does the number of parallel attention heads limit the Boolean functions they can compute?

Two-bit XOR is a motivating test case: how many heads are needed to distinguish its two positive inputs from its two negative inputs?

## Problem statement

For a positive integer $n$ and a Boolean function

$$ f : \lbrace 0,1\rbrace^n \to \lbrace 0,1\rbrace, $$

determine the smallest number of attention heads needed to compute it exactly on every input.

We call this minimum the function's [head complexity](definitions/05_head_complexity.md), denoted $H^{\ast}(f)$. We seek structural explanations for it: lower bounds that establish what attention cannot compute, and constructions that show how to compute a function with few heads.

The [problem statement](problem_statement.md) defines the research goal and core questions, including exact complexity for natural function families and connections to classical Boolean complexity measures.

## Model

The baseline uses token-plus-position embeddings, one softmax self-attention layer, and a thresholded linear readout from a final query token. The query attends to every input position and itself, and its output includes the residual connection. There is no MLP or layer normalization.

Each realization may choose any positive finite model and head dimensions; only the number of heads is minimized. The [definitions](definitions/README.md) specify the architecture, scores, classification convention, and complexity measures.

## Mathematical account

The mathematical account develops representations of attention scores, constructions for computing Boolean functions, and lower bounds on head complexity.

The [theorem index](theorems.md) organizes results by chapter and records their dependencies. Each theorem includes a statement and proof, with links to the definitions and earlier results it uses.

Start with the definitions, then read [Chapter 1: Foundations and normal form](theorems/01_foundations_and_normal_form/README.md).

## Further reading and contributing

- [Introductory writeup](artifacts/intro-materials/writeup.md): the two-bit XOR example and its geometric interpretation.
- [Contributing](CONTRIBUTING.md): how to structure results, formalize proofs, and submit contributions.
- [Agent guidance](AGENTS.md): writing conventions and proof-development workflow.
