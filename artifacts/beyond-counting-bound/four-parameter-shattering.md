# Nine Reciprocal Tests on Four Positive Parameters

## Exact finite theorem

There are nine fixed tests

$$ F_q(\theta)=\sum_{i=1}^4\frac{r_{qi}}{\theta_i+p_{qi}}-c_q,\qquad p_{qi}\gt0, $$

whose strict signs realize all 512 binary patterns with $\theta_i\gt0$. The residues are signed. This disproves a proposed upper bound of twice the number of parameters for this separable-query relaxation. It does not refute any asymptotic bound for the attention-head architecture, whose full Boolean query table has additional constraints.

The [exact reciprocal certificate](separable-mobius/n4-m9-step-exact.json) contains every coefficient and witness. Its construction starts with a finite threshold-vote system. The search returned a satisfying assignment; the proof uses the retained witnesses and independent exact verification, not trust in the search algorithm.

## Finite threshold-vote system

Index the queries by $q=0,\ldots,8$. Their weight vectors and twice-thresholds are as follows.

| Query | Weight vector | Twice the threshold |
|---|---|---|
| 0 | $(-4,1,-3,3)$ | 1 |
| 1 | $(-3,2,-1,4)$ | 3 |
| 2 | $(-4,3,-2,2)$ | 1 |
| 3 | $(2,-1,3,-2)$ | 1 |
| 4 | $(1,-3,4,-4)$ | 1 |
| 5 | $(1,-3,3,-4)$ | 1 |
| 6 | $(-2,4,-1,3)$ | 1 |
| 7 | $(1,-3,4,2)$ | 5 |
| 8 | $(2,-1,2,-1)$ | 5 |

The four coordinate orders of the queries are

$$ \begin{aligned} &(0,1,2,3,4,5,6,7,8),\cr &(6,2,7,4,3,0,5,1,8),\cr &(2,6,3,1,4,5,7,8,0),\cr &(7,5,1,8,4,3,6,2,0).\end{aligned} $$

Let $t_{qi}\in\lbrace1,\ldots,9\rbrace$ be the rank of query $q$ in coordinate order $i$. For a cut vector $z\in\lbrace0,\ldots,9\rbrace^4$, put

$$ v_{qi}(z)=\mathbf1[t_{qi}\gt z_i],\qquad G_q(z)=\sum_iw_{qi}v_{qi}(z)-c_q. $$

The retained finite certificate specifies one cut vector for each of the 512 output patterns. Direct enumeration of all 10,000 cut vectors independently obtains all 512 patterns. Every gate value is a nonzero half-integer, so its absolute value is at least $1/2$.

## Rational lift and strict error bound

Set $R=257$, and define the fixed poles, residues, and positive parameter witness by

$$ p_{qi}=R^{2t_{qi}},\qquad r_{qi}=w_{qi}p_{qi},\qquad \theta_i(z)=R^{2z_i+1}. $$

If $t_{qi}\leq z_i$, then $\theta_i/p_{qi}\geq R$, and the fraction $p_{qi}/(\theta_i+p_{qi})$ lies between zero and $1/(R+1)$. If $t_{qi}\gt z_i$, then $\theta_i/p_{qi}\leq1/R$, and that fraction lies between $R/(R+1)$ and one. In both cases,

$$ \left|\frac{p_{qi}}{\theta_i+p_{qi}}-v_{qi}(z)\right|\leq\frac1{R+1}. $$

Every weight has absolute value at most four. Thus

$$ |F_q(\theta(z))-G_q(z)|\leq\frac{16}{258}\lt\frac14. $$

Every signed ideal margin is at least $1/2$. Each lifted reciprocal margin therefore exceeds $1/4$, proving all 512 patterns with strictly positive parameters and denominators. $\blacksquare$

## Verification boundary

`lift_four_axis_step_witness.py` verifies each coordinate chain, all finite gate inequalities, the displayed error bounds, and every final reciprocal sign using exact fractions. `generate_four_parameter_lean.py` generates a separate kernel-checked certificate for the final reciprocal inequalities. It stores the small cut indices, derives the positive powers algebraically, and checks 32 batches of 16 witnesses to keep the kernel computation within the memory limit.

The final declaration is `HeadComplexity.MobiusFourParameterShattering.nine_tests_shattered` in `MobiusFourParameterShattering.lean`. It compiled successfully, and its axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`. Its input-label surjectivity is proved using the finite base-two digit equivalence; no exhaustive search over all functions is trusted.

The three-axis, seven-query step search returned an UNSAT diagnostic. That diagnostic is retained with its exact finite-model scope; no Lean-checked impossibility theorem or general reciprocal upper bound is asserted from it. The four-axis, ten-query search is a further experiment. None of these finite results proves the selected worst-case head-complexity target.
