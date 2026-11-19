# Problem Statement: Head Complexity of Boolean Functions in One-Layer Attention

## Goal

For a positive integer $n$, we want to characterize the minimum number of attention heads required to compute a Boolean function

$$f : \lbrace 0,1 \rbrace^n \to \lbrace 0,1 \rbrace$$

in a **single-layer attention-only transformer** with a **linear readout** from a designated query token.

[Two-bit XOR](https://www.lesswrong.com/posts/T66BKwSufh5SfiPHm/how-many-attention-heads-do-you-need-to-do-xor-3) is a motivating test case for understanding how head count limits the functions this architecture can compute.

## Model

The [model definition](definitions/01_model.md) fixes the architecture. Its query residual produces a [score](definitions/02_score.md) $\Phi$, which determines the output using the [classification convention](definitions/03_classification.md).

[Computability](definitions/04_computability.md) requires agreement with the target function on every Boolean input. Model and head dimensions are arbitrary positive finite integers and may vary between realizations; head count is the resource being measured.

## Main Quantity

Our central problem is to understand the [head complexity](definitions/05_head_complexity.md) $H^{\ast}(f)$ as a function of $f$. Its definition permits zero heads and uses infinity when no realization exists.

## Core Questions

1. **Exact characterization.** Can $H^{\ast}(f)$ be expressed, exactly or approximately, in terms of a known invariant of $f$?
2. **Lower bounds.** What techniques prove that a function requires at least $H$ heads?
3. **Upper bounds.** Can we constructively realize broad classes of Boolean functions with few heads?
4. **Comparison to classical complexity measures.** How does $H^{\ast}(f)$ relate to:
   - threshold degree,
   - rational degree,
   - threshold density / sparsity,
   - circuit depth / threshold-circuit complexity,
   - Fourier or spectral complexity measures?
5. **Natural families.** What is $H^{\ast}(f)$ for standard functions such as:
   - $\mathrm{AND}$, $\mathrm{OR}$,
   - parity / $\mathrm{XOR}$,
   - majority,
   - exact-count / symmetric functions,
   - address / indexing functions,
   - intersections of threshold functions?

## Desired Outcome

We would like to identify either:

- an invariant $I(f)$ such that $H^{\ast}(f)$ is controlled by $I(f)$ (ideally $H^{\ast}(f) \asymp I(f)$ on broad classes), or
- explicit function families for which the head complexity exhibits qualitatively new behavior compared to classical measures.

The [theorem index](theorems.md) records the results currently developed in the mathematical account.
