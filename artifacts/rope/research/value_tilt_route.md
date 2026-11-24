# Value Tilt and Classifier Approximation Route Audit

## A strict classifier as a difference of two products

For one pure atom, write its positive denominator as $D(x)=\gamma+\sum_i a_i(1-x_i)+b_i x_i$, its token values as $v_0,v_1$, and its query value as $v_q=\eta/\gamma$. Introduce the tilted partition function

$$ D(t,x)=\gamma e^{tv_q}+\sum_i a_i e^{tv_0}(1-x_i)+b_i e^{tv_1}x_i. $$

It is positive for every real $t$, and direct differentiation gives

$$ \left.\frac{\partial}{\partial t}\log D(t,x)\right|_{t=0}=p(x). $$

For a strict score $S(x)=c+\sum_{h=1}^H p_h(x)$, define

$$ G(t,x)=e^{ct}\prod_{h=1}^H D_h(t,x). $$

Then $\partial_tG(0,x)=G(0,x)S(x)$, with $G(0,x)\gt0$. For each cube point, the difference quotient $(G(t,x)-G(0,x))/t$ converges to a nonzero value with the desired sign. Since there are finitely many inputs, one sufficiently small positive finite $t$ gives the correct signs simultaneously. Thus every strict pure classifier is also the sign of a difference of two products of positive affine forms. This derivative argument is handwritten.

The representation retains useful structure, but it does not by itself supply $H$ vanilla fractions. A telescoping expansion of the product difference has mixed products of the old and new factors. Dividing by one product does not turn all its terms into affine-over-affine fractions.

## Uniform denominator slopes can require leaving the sign-preserving interval

The slope at coordinate $i$ of one tilted denominator is $b_i e^{tv_1}-a_i e^{tv_0}$. If $v_1\neq v_0$, sufficiently extreme values of $t$ make these slopes uniform. The strict-margin argument only controls a neighborhood of zero. There need not be an overlap with an orientation interval.

Convexity of $\log G(t,x)$ does not repair this. A positive derivative at zero gives the expected positive change for positive $t$, but an initially negative derivative may later cross zero and produce the opposite comparison. Query-only value tilts change denominator constants without changing the mixed slope signs at all.

### A classifier-level counterexample to this tilt construction

Take one pure atom on two bits with

$$ \gamma=1,\qquad \eta=0,\qquad a=(100,1),\qquad b=(1,200),\qquad v_0=0,\qquad v_1=1. $$

Put

$$ A(x)=1+100(1-x_1)+(1-x_2),\qquad B(x)=x_1+200x_2. $$

The score $B/(A+B)-1/2$ computes exactly the second input bit. In particular, it is negative at $(1,0)$ and positive at $(0,1)$. This classifier has a one-head vanilla representation by the ordinary linear-threshold theorem.

Use a positive tilt parameter $r$ so the new denominator is $A+r^2B$. The product-difference comparison aligned with the derivative at $r=1$ is

$$ \frac{A+r^2B-r(A+B)}{r-1}=rB-A\qquad(r\neq1). $$

Its denominator slopes are $r^2-100$ and $200r^2-1$. If both are positive, then $r\gt10$, and the comparison at $(1,0)$ is $r-2\gt0$, an incorrect positive label. If both slopes are negative, then $200r^2\lt1$, and the comparison at $(0,1)$ is $200r-101\lt0$, an incorrect negative label. Both slopes cannot vanish simultaneously.

The derivative classifier evaluated at the tilted endpoint also fails: it compares $r^2B-A$ with zero, and the same two inputs give the wrong label in the corresponding orientation intervals.

The original classifier, the difference-quotient identity, and both orientation failures are Lean-checked in `Atoms/RoPETiltObstruction.lean`. The failure concerns this particular family of approximating classifiers. It leaves the one-head equivalence intact and illustrates why an alternative representation is necessary.

## Continued fractions and one-dimensional order

For the reciprocal subclass, pivoting an arrowhead matrix produces continued-fraction expressions. With several independent affine denominator directions, their later pivots are rational functions, so the expression does not retain one affine denominator per head. A common affine statistic is different: its partial fractions are governed by a single univariate polynomial, and Theorem 17 proves head preservation there.

The same limitation affects order-based arguments. Cauchy partial fractions and divided differences can exploit one ordered scalar statistic. General rotary denominators need not order the cube points consistently, and their relative order can change from one denominator to another. No multivariate replacement preserving the original head count was established.

The difference-of-products representation is a rigorous alternative sign certificate. Turning it into $H$ admissible affine fractions, while retaining the finite strict signs, remains open in this route.

## A simpler algebraic product difference

The exponential tilt is unnecessary for the sign certificate itself. Consider any finite family of positive affine denominators $D_h$ and affine numerators $N_h$, with a strict score $S(x)=\sum_hN_h(x)/D_h(x)$. Define

$$ G(t,x)=\prod_h(D_h(x)+tN_h(x)). $$

Differentiating the finite product at zero gives

$$ \partial_tG(0,x)=\left(\prod_hD_h(x)\right)S(x). $$

The difference quotient has a continuous extension at zero. The cube is finite, the original derivative is nonzero at every cube point, and every original factor is positive. Consequently, for every prescribed upper bound $a\gt0$, there is one finite $t\in(0,a)$ such that every perturbed factor stays positive and

$$ \mathrm{sgn}\left(\prod_h(D_h(x)+tN_h(x))-\prod_hD_h(x)\right)=\mathrm{sgn}S(x) $$

for every cube point. The product difference is also nonzero everywhere. This statement applies to arbitrary positive affine fractions, so it is stronger than a statement restricted to pure atoms.

A free score constant can be absorbed into the first numerator when $H\geq1$. Before absorption, a sufficiently small downward shift removes zero scores without changing the strict-positive classifier convention. Thus every positive affine-fraction classifier with at least one head has a strict sign representation by the difference of two products of $H$ positive affine factors. For $H=0$, the classifier is constant and can be treated separately.

The full finite-parameter statement and the free-constant wrapper are Lean-checked in `Results/ProductDifferenceSign.lean`, as `exists_positive_product_difference` and `CubeAffine.classifier_as_product_difference`. This formalization proves an alternate sign representation. It supplies no denominator orientation or vanilla head-count conclusion.
