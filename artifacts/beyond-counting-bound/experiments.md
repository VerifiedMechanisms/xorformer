# Exact Checks of Candidate Representations

## Purpose and limitations

These experiments attempt to refute proposed hard examples by producing admissible representations. They cannot establish infeasibility or a lower bound. A numerical failure is always recorded as `UNKNOWN`.

The small sweep tried 180 fits on seven through ten input bits. It found 21 representations that passed exact arithmetic verification. The retained certificates use the fewest heads found for each tested target. This is not a claim of minimality.

A subsequent larger sweep was interrupted after 38 completed fits and three certificates. An audit of earlier runs found that random labels and products of halfspaces had already been investigated numerically in commit `0064c21` of `VerifiedMechanisms/autoresearch-runs`. More optimizer runs on those families would not supply the missing lower-bound mechanism.

## Certificate semantics

Each JSON certificate supplies integer arrays $w_{hi}\gt0$ and $a_{hi}$, orientations $o_h\in\lbrace0,1\rbrace$, an integer scale $K=2^q$, and a bias $\sigma\in\lbrace-1,1\rbrace$. Its score is

$$ S(x)=\sigma+\sum_h\frac{\sum_i a_{hi}x_i}{K+\sum_i w_{hi}\bigl((1-o_h)x_i+o_h(1-x_i)\bigr)}. $$

Every denominator is positive on the cube. Its variable coefficients are all strictly positive when $o_h=0$ and all strictly negative when $o_h=1$. Thus it satisfies the manuscript's admissibility condition. Numerators are affine, so the manuscript's realization theorem applies.

The independent verifier uses no floating-point arithmetic and imports no optimizer code. For each summand with numerator $a$ and positive denominator $d$, it computes the exact quotient and remainder

$$ Qa=kd+r,\qquad 0\leq r\lt d,\qquad Q=2^{128}. $$

This bounds the scaled summand between $k$ and $k+1$, with equality when the remainder is zero. Summing the integer bounds proves every required strict sign on all $2^n$ cube inputs. The output is retained in `experiments/exact-verification.jsonl`.

## A concrete failed obstruction

The certificate `experiments/n8-h4-random_code_subset-r0.json` gives four heads for a function whose positive support is a seven-element subset of a binary code with minimum distance at least three.

The code has parity-check columns equal to the distinct nonzero four-bit representations of the integers one through eight. No vector of Hamming weight one or two is in its kernel: a single column is nonzero, and two distinct columns do not sum to zero over the two-element field. Every subset of the code therefore retains minimum distance at least three.

The positive vertices in this certificate are isolated from one another even at distance two. Consequently, the proposed lower bound asserting one head per such isolated positive vertex is false. This example says nothing about the asymptotic target for arbitrary Boolean functions.

## Reproduction

Run the independent verifier with:

```sh
python3 artifacts/beyond-counting-bound/verify_representation.py artifacts/beyond-counting-bound/experiments/n*-r*.json
```

The search script includes an analytic-gradient check. Sustained optimizer searches must be run through the shared machine's `heavy` wrapper. Bounds imposed for numerical stability constrain only the search, never the mathematical model or a lower-bound claim.

## Projected hinge-loss search

The later `search_projected_hinge.py` solves a convex squared-hinge readout problem inside each denominator update. Its gradient check had maximum absolute error below $4\cdot10^{-12}$. Across 28 completed trials it produced six exact certificates, all independently checked by `verify_representation.py`. The remaining 22 results are `UNKNOWN`.

The smallest new certificates for the three fixed random targets use eight heads on eight bits, eighteen heads on nine bits, and twenty-four heads on ten bits. These are upper bounds for those particular targets, not worst-case bounds or minimality claims. The exact certificates, verification output, and trial records are retained under `experiments/` with `projected-hinge` in their names. Total recorded optimizer time was about five minutes; the two-hour command limit was only a maximum and was not counted as elapsed work.
