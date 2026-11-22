# Two Positive Parameters and Three Sign Tests

## Statement

Consider fixed predicates of the form

$$ F_q(x,y)=\frac{r_q}{x+p_q}+\frac{s_q}{y+t_q}-c_q,\qquad x,y,p_q,t_q\gt0. $$

The largest number of such predicates whose strict signs can be independently prescribed by varying the two positive parameters is exactly three. This finite result concerns a relaxation used to audit a possible counting argument. It is not an asymptotic result for attention heads.

## Explicit lower bound

Take

$$ F_1(x,y)=\frac1{x+1}-\frac1{y+1},\qquad F_2(x,y)=-\frac8{x+1}+\frac{15}{y+2}-1,\qquad F_3(x,y)=\frac13-\frac1{x+1}. $$

The unused second residue in the third predicate is zero; its second pole can be any positive number. Direct rational evaluation gives the following eight strict sign vectors. The table lists the actual values, so it also certifies that no tie is used.

| Parameters | First value | Second value | Third value |
| --- | --- | --- | --- |
| $(1/2,2/5)$ | $-1/21$ | $-1/12$ | $-1/3$ |
| $(1/2,1)$ | $1/6$ | $-4/3$ | $-1/3$ |
| $(1/2,1/4)$ | $-2/15$ | $1/3$ | $-1/3$ |
| $(3/2,31/20)$ | $2/255$ | $9/355$ | $-1/15$ |
| $(4,39/10)$ | $-1/245$ | $-17/295$ | $2/15$ |
| $(4,5)$ | $1/30$ | $-16/35$ | $2/15$ |
| $(4,1)$ | $-3/10$ | $12/5$ | $2/15$ |
| $(5/2,51/20)$ | $2/497$ | $1/91$ | $1/21$ |

## Upper bound

Multiplication by the positive denominator preserves each strict sign and gives

$$ (x+p_q)(y+t_q)F_q(x,y)=-c_qxy+(s_q-c_qt_q)x+(r_q-c_qp_q)y+r_qt_q+s_qp_q-c_qp_qt_q. $$

Thus every cleared test is an affine form in the three coordinates $x,y,xy$. Four affine forms on three-dimensional real space cannot realize all sixteen strict sign vectors. Here is a direct proof that also covers dependent or degenerate forms.

Write the four forms as $L_q(z)=a_q\cdot z+d_q$. There are real coefficients $\lambda_q$, not all zero, with $\sum_q\lambda_q a_q=0$. Consequently

$$ \sum_q\lambda_q L_q(z)=\sum_q\lambda_qd_q=:D $$

is constant. If $D\geq0$, prescribe the sign of each form with nonzero coefficient to be opposite to the sign of that coefficient. Their weighted sum would be strictly negative, a contradiction. If $D\lt0$, prescribe matching signs instead; their weighted sum would be strictly positive. Assign arbitrary signs where the coefficient is zero. In both cases a strict sign vector is absent. Restricting to the surface $z=(x,y,xy)$ with positive coordinates cannot restore that vector. Any collection with more than four predicates contains a four-predicate subcollection. This proves the upper bound. $\blacksquare$

## Audit scope and blocked inference

`HeadComplexity.MobiusParameterShattering.three_tests_shattered`, in `formalization/HeadComplexity/Atoms/MobiusParameterShattering.lean`, checks the explicit lower bound over the real numbers. The upper bound is the written linear-algebra proof above. The finite search files in `separable-mobius/` motivated the example; their unsuccessful searches do not prove upper bounds.

The example disproves a bound equating the number of independently realizable sign tests with the number of positive scalar parameters. It does not disprove a uniform constant-factor bound. Such a bound for arbitrary sums of positive affine ratios, if strong enough to improve the manuscript's counting theorem, remains unproved here. No transfer from this two-parameter relaxation to the full attention model is claimed.

## Three-parameter adversarial extension

The two-parameter result does not extend to the proposed bound of $2H-1$ tests for $H$ positive scalar parameters. Six fixed tests of the form

$$ F_q(\theta)=\sum_{h=1}^3\frac{r_{qh}}{\theta_h+p_{qh}}-c_q,\qquad \theta_h,p_{qh}\gt0 $$

realize all 64 strict sign vectors. The following coefficients are exact terminating decimals.

| Test | Pole triple | Residue triple | Threshold |
| --- | --- | --- | --- |
| 1 | $(233.368,0.0935806,9.25278)$ | $(242.688,-0.0925863,-0.01746)$ | $0.119577$ |
| 2 | $(1.68722,1045.81,7.6483)$ | $(-0.185895,620.953,-0.716991)$ | $0.446687$ |
| 3 | $(0.136276,1.4277,0.000000416615)$ | $(-17.1545,-0.0805527,-0.0144831)$ | $-74.5988$ |
| 4 | $(4.50014,0.000729847,72.179)$ | $(1.2498,0.000886264,-163.429)$ | $-1.58714$ |
| 5 | $(0.0128411,41.5317,38.6291)$ | $(0.00738387,-56.6961,72.7201)$ | $0.518105$ |
| 6 | $(980.608,0.306928,194.556)$ | $(-755.264,0.0977403,-161.808)$ | $-1.26616$ |

All 64 positive parameter triples are listed in [the exact certificate](separable-mobius/n3-m6-exact.json). The key for each triple is the integer whose six binary digits give the signs, with the first test in the least significant position. Exact rational evaluation verifies every sign, with every absolute test value exceeding $10^{-6}$.

For an independent kernel check, `formalization/HeadComplexity/Atoms/MobiusThreeParameterShattering.lean` multiplies every pole, residue, and parameter coordinate by $K=10^{12}$ and every threshold by the same scale before dividing it back in the test. If the integer data are $P,R,X,C$, positivity of $K$ and the three denominators reduces every assertion to the sign of the integer

$$ K\bigl(R_1D_2D_3+R_2D_1D_3+R_3D_1D_2\bigr)-CD_1D_2D_3,\qquad D_h=X_h+P_h. $$

The declarations `cleared_signs` and `labels_surjective` check all 384 integer inequalities and all 64 binary labelings. `test_cleared` proves the rational identity, and `six_tests_shattered` proves the real-valued existence statement. Its axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

This example concerns the same relaxation, whose pole and residue data vary freely between tests. No construction of these six tests as the complete Boolean evaluation table of the manuscript's heads is asserted. It rules out the specific $2H-1$ relaxation bound. It does not rule out a larger uniform constant, and it proves no asymptotic head lower bound.
