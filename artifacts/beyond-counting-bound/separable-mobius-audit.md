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
