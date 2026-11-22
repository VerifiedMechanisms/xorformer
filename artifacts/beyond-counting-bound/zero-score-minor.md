# Denominator Directions at a Zero Score

## Statement

There is an admissible two-head score on four input bits, equal to zero on nine specified vertices, whose evaluation Jacobian on those vertices has rank at least nine. In particular, the proposed bound $nH$ on the Jacobian rank at a common zero is false, even with strictly positive denominator slopes.

This is an obstruction to a proposed proof mechanism. It is not a lower bound for the worst-case head complexity.

## Exact construction

Use the normalized score

$$ S(x)=1+\frac{u_1\cdot x}{1+b_1\cdot x}+\frac{u_2\cdot x}{1+b_2\cdot x}, $$

with

$$ b_1=(1,1,1,1)/7,\qquad b_2=(10,10,9,9)/71, $$

$$ u_1=(-568,-568,-71,-71)/7,\qquad u_2=(5670,5670,630,630)/71. $$

All denominator slopes are strictly positive. Put $L_1=1-x_1-x_2$, $L_2=1-x_3-x_4$, and $D=7+x_1+x_2+x_3+x_4$. Direct calculation gives

$$ S(x)=497\left(\frac{L_1}{D}-\frac{L_1}{D+L_2/10}\right)=\frac{497L_1L_2}{10D(D+L_2/10)}. $$

The second denominator is positive throughout the cube. Thus $S=0$ whenever $L_1L_2=0$.

Encode a vertex by $v=\sum_{i=1}^4 2^{i-1}x_i$. Take the sample vertices, in this order,

$$ 1,2,4,5,6,7,8,9,13. $$

Each has zero score. Order the sixteen parameters as the four coordinates of $u_1$, then $u_2$, then $b_1$, then $b_2$. With zero-based column indices, retain columns $0,1,2,3,4,5,6,8,10$. The derivative entries are

$$ \frac{\partial S(x)}{\partial u_{hi}}=\frac{x_i}{1+b_h\cdot x},\qquad \frac{\partial S(x)}{\partial b_{hi}}=-\frac{x_i(u_h\cdot x)}{(1+b_h\cdot x)^2}. $$

Exact rational elimination gives the determinant of this nine by nine minor:

$$ \det J_{\mathrm{minor}}=\frac{10401023166874151}{15516104491008000000}\neq0. $$

The reproducible verifier `verify_zero_score_minor.py` checks the score identity at all sixteen vertices, all nine zero evaluations, positivity, and the displayed determinant using integer and rational arithmetic. It does not rely on a floating-point rank estimate.

## Consequence and limitation

Fix the other seven parameters. The inverse function theorem gives an open neighborhood of zero in the nine selected score coordinates. Every strict sign assignment on these nine vertices is therefore realized by parameters sufficiently close to the displayed point. Denominator admissibility persists because the slopes are strictly positive.

The fixed-denominator feature span has dimension at most $nH=8$, whereas this local family shatters nine vertices. A sign-counting proof cannot simply replace the full family near a zero score by its fixed-denominator span. No asymptotic conclusion follows from this finite example.

The auxiliary numerical search `search_zero_fibers.py` was also checked against centered finite differences. Its unsuccessful searches are recorded as `UNKNOWN`; they do not establish nonexistence of other regular zero fibers.
