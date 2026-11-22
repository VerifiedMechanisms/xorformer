# Parameter-Line Degree Obstruction

## Statement

For every positive integer $H$, there are $H$ admissible one-bit heads whose denominator parameters depend affinely on a positive scalar $t$, and a fixed output bias, such that any polynomial in $t$ agreeing with the output signs for all $t\gt 0$ has degree at least $H$.

This is an obstruction to a proposed counting argument. It is not a lower bound on $W(n)$.

## Construction

For $0\leq h\lt H$, use the denominator

$$ B_h(t,x)=H+h+tx. $$

For every $t\gt 0$, its constant term and slope are strictly positive. A constant numerator $b_h$ is admissible. At the input $x=1$, the score is

$$ S(t)=c+\sum_{h=0}^{H-1}\frac{b_h}{t+H+h}. $$

The following rational function has this form by partial fractions:

$$ G_H(t)=(-1)^{H+1}\frac{\prod_{j=1}^H(t-j-1/2)}{\prod_{h=0}^{H-1}(t+H+h)}. $$

Concretely, take

$$ c=(-1)^{H+1},\qquad b_h=(-1)^{H+1}\frac{\prod_{j=1}^H(-H-h-j-1/2)}{\prod_{\ell\neq h}(\ell-h)}. $$

The poles are distinct, and matching their residues and the value at infinity proves $S=G_H$. At $t=k+1$, for $0\leq k\leq H$, the numerator has $H-k$ negative factors and the denominator is positive. Thus $G_H(k+1)$ is positive exactly when $k$ is odd. Every strictly sign-matching polynomial has at least one root in each of the $H$ intervening intervals, so its degree is at least $H$.

The Lean proof also covers the manuscript's non-strict convention for false labels. It uses exact reciprocal interpolation to obtain scores equal to $1$ or $-1$, followed by the already formalized ordered sign-change theorem.

## Consequence for polynomial predicates

Suppose a polynomial in the original numerator and denominator coefficients agrees with the output sign on every admissible parameter choice. Restricting it to the affine parameter ray above gives a polynomial of degree no greater than its total degree. Therefore its total degree must be at least $H$. Choosing a different sign-equivalent polynomial in the same parameters cannot avoid this obstruction.

This conclusion does not exclude a different parametrization, several predicates, a bound specific to simultaneous cube evaluations, or an argument that does not use polynomial degree.

## Literature audit

[Anthony and Bartlett, Theorem 8.11 and its proof, pages 122 to 123](https://openeclass.panteion.gr/modules/document/file.php/PMS152/LEARNING/Anthony%20Martin%2C%20Bartlett%20Peter%20L.%20%282009%29%20--%20Neural%20Network%20Learning_%20Theoretical%20Foundations.pdf) state a VC bound depending logarithmically on input fan-in and discrete input magnitude. The proof transforms sigmoid weights exponentially and claims that the final polynomial degree is at most $3ND+2$, independently of the number of hidden units.

The claimed degree step fails already for $N=D=1$. Set all input weights to zero and the transformed bias of hidden unit $h$ to $t+H+h-1$. Its output is $1/(t+H+h)$. These transformed biases are positive for $t\gt 0$. With the fixed output coefficients above, the final score is $G_H(t)$. Taking $H=6$ forces degree at least six, exceeding $3ND+2=5$.

This refutes that proof step, not the VC bound itself. No replacement proof establishing the needed fan-in bound was found. [Bartlett and Williamson's original discrete-input result](https://doi.org/10.1162/neco.1996.8.3.625) gives an upper bound of order $W\log(WD)$, which retains the logarithm of the total parameter count. It does not supply the requested unbounded improvement.

## Formal audit

The declarations in `formalization/HeadComplexity/Atoms/ParameterLineOscillation.lean` are:

- `HeadComplexity.ParameterLineOscillation.exists_alternating_parameter_line`.
- `HeadComplexity.ParameterLineOscillation.exists_parameter_line_forcing_degree`.
- `HeadComplexity.ParameterLineOscillation.admissible_heads_force_parameter_degree`.

The last declaration quantifies over actual `FracAtom 1` heads and all positive parameter values. The proof uses only the standard Lean foundational axioms. It does not assume a bound or a conjecture about head complexity.
