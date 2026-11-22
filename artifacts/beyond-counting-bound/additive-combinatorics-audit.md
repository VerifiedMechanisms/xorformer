# Additive Concentration and Restriction Audits

## Inverse Littlewood-Offord hypotheses

[Nguyen and Vu, Theorems 2.5 and 2.8](https://people.math.osu.edu/nguyen.1261/cikk/optimalILO-final.pdf) describe additive structure when a signed sum has polynomially large point concentration, or when normalized real vectors have polynomially large small-ball concentration at a specified radius. These hypotheses are substantive. Positivity of the denominator coefficients does not imply either hypothesis at a radius relevant to exact signs.

For an explicit admissible denominator, set

$$ B(x)=1+\sum_{i=0}^{n-1}2^i x_i. $$

All coefficients are strictly positive. Binary expansion proves that its values on the cube are precisely the distinct integers from one through $2^n$. Thus, under the uniform cube distribution,

$$ \sup_t\Pr[B(x)=t]=2^{-n}. $$

The corresponding signed sum has the same point concentration, since replacing $x_i$ by $(1+\eta_i)/2$ is a bijection on input assignments. After any common positive normalization of the coefficients, the values remain distinct. At every radius less than half their minimum separation, the small-ball probability is also $2^{-n}$.

For every fixed $C$, this is less than $n^{-C}$ for sufficiently large $n$. Consequently, invoking an inverse theorem uniformly over all admissible denominators is invalid. A dichotomy might still treat concentrated and dispersed coefficients separately, but no bound sufficient for the target has been proved for the dispersed case. The inverse theorem alone is not a compression theorem for the model.

## Restriction of signs versus restriction of real outputs

[Kane and Williams, Lemma 3.1](https://cseweb.ucsd.edu/~dakane/depth2LTF.pdf) bound the probability that a restricted linear threshold gate still depends on more than one input. Their Corollary 2.1 gives the random-function counting scale $\Omega(2^n/n^2)$ for depth-two threshold circuits. Those gates emit Boolean values. The hidden attention heads here emit real ratios before the final sum is thresholded.

This distinction can be tested exactly. Fix any subset $F$ of coordinates and any assignment to $F$ in the preceding denominator. On the remaining coordinates $R$, write

$$ B_R(x)=c+\sum_{i\in R}2^i x_i,\qquad c=1+\sum_{i\in F}2^i a_i\geq1. $$

The admissible ratio $g_R(x)=1/B_R(x)$ remains nonconstant in every free coordinate. Holding the other free coordinates fixed and denoting their contribution plus $c$ by $d\gt0$, its change on coordinate $j$ is

$$ \frac{1}{d+2^j}-\frac{1}{d}=-\frac{2^j}{d(d+2^j)}\neq0. $$

Its Boolean sign is constant, but its real output is not. Replacing it by that constant sign inside a sum is invalid: subtracting a threshold between two of its distinct values changes the final labels. The threshold-gate restriction lemma therefore does not imply elimination of attention heads. This example is an obstruction to that transfer, not a lower bound for head complexity. A new argument controlling the summed real outputs would be required.

## A recent polynomial representation result

[Rajagopalan and Saurabh, Theorem 3 and Corollary 5](https://arxiv.org/html/2611.11966v1), posted in November 2026, bound the nondeterministic and rational degrees of almost all Boolean functions by $n/2+O(\sqrt{n\log n})$. Their nondeterministic predicate is $p(x)\neq0$ exactly on the true inputs. Their Theorem 6 also disproves a proposed general hypercube Nullstellensatz extension using three quadratic polynomials.

These statements concern different representations. A strict attention score is nonzero on both label classes. A low-degree polynomial representing a zero set does not by itself supply an affine-denominator decomposition, and degree does not count its affine-ratio summands. Conversely, a degree lower bound of order $n$ cannot imply the requested head lower bound at exponential scale. No head-count conclusion is inferred from this source.

## Audit conclusion

The new literature checks do not discharge the selected target. The concentration hypothesis, preservation of real outputs under restrictions, and conversion from polynomial degree to unrestricted head count are separate missing arguments. None is treated as routine or as an established lemma. The architecture and the freedom to choose target-dependent denominators remain unchanged.
