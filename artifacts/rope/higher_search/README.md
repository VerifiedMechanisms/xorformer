# Asymmetric Perturbations Of Three Pure Rotary Heads

This directory contains 50 exact pairs of pure and vanilla three-head upper certificates on eight bits. Every function is non-globally-complement-invariant. Thirty-eight samples perturb vertices where the original score was zero. None supplies a separation.

## Algebraic Starting Point

For three centered denominator forms $B_0,B_1,B_2$, take cyclic numerator differences. The cleared score is a signed multiple of the Vandermonde product

$$ (B_0-B_1)(B_1-B_2)(B_2-B_0). $$

The generator chooses positive mass vectors and a fixed invertible signed circulation matrix so that the numerator vectors also satisfy the pure-atom relation. Its atom weights, values, query numerators, and readout constant are rational. Perturbations are bounded using the exact smallest nonzero baseline margin. They preserve every nonzero baseline label while resolving the zero vertices asymmetrically.

The Vandermonde baseline itself cannot separate these models. Add the same affine form to all three denominator directions so that all their slopes become positive, then apply a common positive scaling to keep each denominator positive on the cube. Differences retain their signs. Cyclic numerator differences then give an admissible vanilla three-head realization of the same baseline signs.

For the perturbed targets, `compile_vandermonde_perturb.py` uses those oriented denominators and solves a linear program for numerators. It rounds each successful proposal to integers and verifies the resulting signs exactly. It succeeded on all 50 retained samples. This is a finite collection of certificates, not a universal theorem about perturbations.

## Exact Verification

`exact_vandermonde_perturb.jsonl` stores the full rational pure parameters, all truth tables, and integer vanilla denominators and numerators. Bit $i$ of the input index is coordinate $i$; bit $m$ of each hexadecimal truth table is the function value at input index $m$.

```bash
python3 artifacts/rope/higher_search/verify_vandermonde_perturb.py \
  artifacts/rope/higher_search/exact_vandermonde_perturb.jsonl
```

The independent verifier uses only Python's standard library. It checks all 12,800 inputs, strict positivity of every attention weight, strict common orientation of each vanilla denominator, positivity of every denominator on the whole cube, and agreement of both scores with every stored truth-table bit. The scalar-to-architecture bridges are those of Theorem 14 and the original affine-fraction normal form.

`search_vandermonde_perturb.py` and `compile_vandermonde_perturb.py` need NumPy and SciPy. Run substantial campaigns through `heavy`. Numerical fitting failures have no lower-bound interpretation. The search script deliberately records unresolved attempts as unresolved.
