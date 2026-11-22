# Positive Denominators Do Not Bound Dual Oscillation

## Statement

This is a counterexample to a possible proof shortcut, not a head-complexity lower bound.

For every integer $M\geq1$, there are explicit real coefficients $\lambda_0,\ldots,\lambda_{M-1}$ such that

$$ \sum_{j=0}^{M-1}\frac{\lambda_j}{t+j}=\frac{\prod_{r=1}^{M-1}(t-r)}{\prod_{j=0}^{M-1}(t+j)},\qquad t\gt0. $$

Consequently, this linear functional of positive reciprocal evaluations has exactly $M-1$ distinct positive zeros. When $M\geq2$, all zeros are simple, so its sign changes at every one of them.

## Proof

Set $Q(t)=\prod_{r=1}^{M-1}(t-r)$ and $D(t)=\prod_{j=0}^{M-1}(t+j)$. Define

$$ \lambda_j=\frac{Q(-j)}{\prod_{0\leq k\leq M-1, k\neq j}(k-j)}=(-1)^{M-1-j}\frac{(j+M-1)!}{(j!)^2(M-1-j)!}. $$

The polynomial

$$ R(t)=Q(t)-\sum_{j=0}^{M-1}\lambda_j\prod_{k\neq j}(t+k) $$

has degree at most $M-1$. At each of the $M$ distinct points $-j$, every summand except the one indexed by $j$ vanishes, and the definition of $\lambda_j$ gives $R(-j)=0$. Thus $R=0$. Division by the strictly positive value $D(t)$ proves the identity for $t\gt0$.

The numerator has precisely the distinct positive roots $1,\ldots,M-1$. The denominator is strictly positive there. This proves the zero and sign-change assertions. $\blacksquare$

## Application to the manuscript's atoms

Take $M=2^n$ and index Boolean inputs by the binary statistic

$$ T(x)=\sum_{i=0}^{n-1}2^i x_i. $$

For each $t\gt0$, the function $x\mapsto1/(t+T(x))$ is one admissible affine-ratio atom: its constant denominator coefficient and every variable coefficient are strictly positive. The fixed linear functional

$$ L(v)=\sum_{x\in\lbrace0,1\rbrace^n}\lambda_{T(x)}v(x) $$

therefore has $2^n-1$ distinct positive zeros along this single-head parameter curve.

For example, when $n=2$,

$$ -\frac1t+\frac{12}{t+1}-\frac{30}{t+2}+\frac{20}{t+3}=\frac{(t-1)(t-2)(t-3)}{t(t+1)(t+2)(t+3)}. $$

When $M\geq2$, the coefficients in the functional have both signs. The result rules out a uniform oscillation bound polynomial in $n$ for arbitrary linear functionals on the positive reciprocal chamber. It does not rule out a more specific invariant that controls the signs or geometry of its dual coefficients.

## Formal audit

`formalization/HeadComplexity/Atoms/ReciprocalOscillation.lean` proves the stronger version with arbitrary prescribed roots and arbitrary distinct nonnegative shifts:

- `HeadComplexity.exists_reciprocal_prescribed_roots_identity`.
- `HeadComplexity.exists_reciprocal_prescribed_positive_zeros`.

The explicit factorial formula and the binary-cube specialization are proved above on paper; those two specializations are not separately formalized in this file.

Both declarations were checked with `lake build HeadComplexity.Atoms.ReciprocalOscillation`. The audit file `AuditReciprocalOscillation.lean` reports only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` for each declaration.
