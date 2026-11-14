# How many attention heads does it take to compute a Boolean function?

We study the expressivity of single-layer, attention-only transformers: how does the number of parallel attention heads limit the Boolean functions they can compute?

The motivating example is two-bit XOR. A single head can compute AND and OR with a linear readout, but XOR requires two heads. This suggests using the minimum number of heads as a complexity measure for Boolean functions.

## Problem statement

Given a Boolean function

$$ f : \lbrace 0,1\rbrace^n \to \lbrace 0,1\rbrace, $$

determine the smallest number of attention heads needed to compute it exactly on every input.

We call this minimum the function's **head complexity**, denoted $H^{\ast}(f)$. We seek structural explanations for it: lower bounds that establish what attention cannot compute, and constructions that show how to compute a function with few heads.

The [problem statement](problem_statement.md) defines the research goal and core questions, including exact complexity for natural function families and connections to classical Boolean complexity measures.

## Model

The baseline uses shared token-plus-position embeddings, one softmax self-attention layer, and a thresholded linear readout from a final query token. The query attends to every input position and itself, and its output includes the residual connection. There is no MLP or layer normalization.

Model and head dimensions are unrestricted; the quantity being minimized is the number of heads. The [model specification](model.md) gives the complete equations, computability definition, masking convention, and architectural assumptions.

## Further reading and contributing

- [Introductory writeup](artifacts/intro-materials/writeup.md): the two-bit XOR example and its geometric interpretation.
- [Contributing](CONTRIBUTING.md): how to structure results, formalize proofs, and submit contributions.
- [Agent guidance](AGENTS.md): writing conventions and proof-development workflow.
