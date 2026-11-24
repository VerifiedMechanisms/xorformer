# Finite original-model experiments

## Scope

These experiments test possible mechanisms and produce a few finite witnesses. They do not establish a worst-case asymptotic bound. Failure of a numerical optimizer, or a solver timeout, is not an impossibility certificate. All substantial searches ran through `heavy`; mathematical work continued while they ran.

## Random targets

`probe_random_targets.py` optimizes squared hinge loss with strictly positive denominator slopes parameterized by softplus, using both denominator orientations. A separate linear program tests whether the resulting denominator dictionary supports the target with new affine numerators.

For six inputs and three heads, two of eight sampled targets acquired feasible linear-program witnesses. `random-n6-h3-exact-witnesses.json` records rationalized coefficients, strictly positive replacements for underflowed slopes, and exact verification at all 64 vertices. The raw optimization file is `random-n6-h3.json`. Its `best_error` concerns the optimizer before the separate linear program; `post_lp_error` identifies the successful linear-program fits.

For eight inputs, the searches with four and eight heads found no strict fits in eight sampled targets and twenty restarts per target. `probe_whitened_targets.py` additionally eliminates the linear coefficient block using a QR basis and an inner optimization; four targets with eight restarts and four heads again produced no strict fit. These results diagnose optimization difficulty only. The raw files retain the seeds, labels, restart outcomes, and coefficients where available.

## Exact mixed-orientation witness

`probe_exact_small_heads.py` asks Z3 for a two-head representation of the four-bit conjunction of two exclusive-or functions. The all-positive orientation timed out after 300 seconds. The mixed orientation returned a rational witness, saved in `exact-n4-h2-xor-and.json`.

Let $x_0,x_1,x_2,x_3$ be the input bits. The denominators and numerators are

$$ B_1=1+sum_{i=0}^3(1-x_i),qquad A_1=-x_0/2-7x_2/8. $$

$$ B_2=1+x_0+x_1+x_2+2x_3,qquad A_2=-1+63x_0/64+x_1/2+45x_2/32+3x_3/4. $$

The score $A_1/B_1+A_2/B_2$ is positive exactly when $x_0\neq x_1$ and $x_2\neq x_3$. Both denominators are positive on the entire cube, and all slopes of each have its required strict common sign. Root independently evaluated all sixteen values with rational arithmetic. This is an exact finite witness, not a general construction or a Lean theorem.

## Other finite certificates

The permutation-rounding, two-head star, and radial-jet experiments have separate notes that state precisely which conclusions have exact certificates. In particular, the radial-jet saturation proof combines a modular nonzero minor with an independent characteristic-zero rank bound. A difference between two modular ranks alone would not justify that conclusion.
