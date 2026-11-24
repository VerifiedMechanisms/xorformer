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


## Exact Parity Extensions

The three `exact_parity_extensions*.jsonl` files contain another 180 exact pairs: 80 functions on six bits, 40 on eight bits, and 60 balanced functions on eight bits. Every function restricts to three-bit parity when its extra coordinates are zero. Thus threshold degree and both head counts are exactly three. The certificates check 30,720 cube inputs in total.

Start with positive denominators $1+t_hL$, where $L=z_0+z_1+z_2$ and the three positive rational numbers $t_h$ are distinct. Partial fractions of

$$ \frac{L^3-4L}{\prod_{h=0}^{2}(1+t_hL)} $$

give a constant plus three reciprocal atoms. Its sign on the three-bit cube is parity. Adding independent integer denominator slopes on the extra coordinates, with compensating constants, preserves that parity face. All weights remain strictly positive. In the balanced family each denominator slope vector sums to zero, so their span contains no strictly oriented vector. This score-level obstruction did not prevent vanilla Boolean realizations: all 60 balanced samples have exact matching three-head certificates.

```bash
python3 artifacts/rope/higher_search/verify_small.py \
  artifacts/rope/higher_search/exact_parity_extensions_n6.jsonl \
  artifacts/rope/higher_search/exact_parity_extensions_n8.jsonl \
  artifacts/rope/higher_search/exact_parity_extensions_balanced_n8.jsonl
```

The independent verifier uses only the standard library. It checks positive pure atom weights, every full-cube pure sign, strict orientation and positivity of the vanilla denominators, every integer cleared vanilla sign, and the parity restriction. The architecture bridges are unchanged from Theorems 10 and 14. `search_small_exact.py` generates candidates; `certify_small.py` proposes rational vanilla certificates by fixed-denominator linear programming and passes them through the independent verifier. Floating fitting losses are not lower bounds.
