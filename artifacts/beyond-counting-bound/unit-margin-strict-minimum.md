# A Full-Rank Strict Local Minimum with Full-Cube Unit Margins

## Statement

There is an admissible three-head score on eighteen Boolean variables, with origin value one, that has unit signed margin at all 262,144 cube vertices and is a strict local minimum of the squared normalized numerator norm under those constraints. Its 108 nonorigin active constraints have independent gradients in the 108 numerator and denominator parameters. All denominator slopes are strictly negative, and every denominator is strictly positive on the cube.

This disproves the assertion that every interior local minimum with full-cube unit margins must have a deficient active Jacobian. It does not establish a property of global minima, a counting theorem for minima, or an asymptotic lower bound for the manuscript's worst-case head complexity. The main research target remains unproved.

## Explicit data and exact checks

The file [data.json](unit-minimum-certificate/data.json) specifies integers defining a rational center $c\in\mathbb{Q}^{108}$, a rational matrix $R$, a rational vector $\lambda^0$, 108 distinct nonzero cube vertices $v_r$, and labels $y_r\in\lbrace-1,1\rbrace$. Every entry of $c$, $R$, and $\lambda^0$ has the common denominator $D=10^{70}$. The data hash is `46c83825266d3e7971d89882a42ef3e04747d10858f07ce860cbafd85c682fc5`.

The first 54 coordinates of $z$ are numerator coefficients $u_{ih}$; the remaining coordinates are denominator slopes $b_{ih}$. Within either group, the head index varies fastest. Define

$$ A_h(x;z)=\sum_{i=1}^{18}u_{ih}x_i,\qquad B_h(x;z)=1+\sum_{i=1}^{18}b_{ih}x_i,\qquad T(x;z)=\sum_{h=1}^{3}\frac{A_h(x;z)}{B_h(x;z)}. $$

Set

$$ \gamma=\frac{2373357636515531}{125000000000000000000},\qquad F_r(z)=T(v_r;z)+\gamma\mathbf{1}_{\lbrace y_r=-1\rbrace}. $$

Let $J(z)=DF(z)$. Matrix norms below are the induced infinity norm, and vector norms are infinity norms. The exact verifier [verify_unit_minimum_contraction.py](verify_unit_minimum_contraction.py) establishes the following bounds using only integer and rational arithmetic:

$$ \begin{aligned} |u_{ih}(c)|&\lt\tfrac12,& b_{ih}(c)&\lt-\tfrac1{1000},& B_h(\mathbf{1};c)&\gt\tfrac1{100},\cr \lVert R\rVert_\infty&\lt10^5,& \lVert I-RJ(c)\rVert_\infty&\lt10^{-50},& \lVert F(c)\rVert_\infty&\lt10^{-60},\cr \min_r\lambda_r^0&\gt\tfrac3{1000},& \lVert\lambda^0\rVert_\infty&\lt10^6,& \lVert J(c)^\top Y\lambda^0-\nabla\phi(c)\rVert_\infty&\lt10^{-50}. \end{aligned} $$

Here $Y=\mathrm{diag}(y_r)$ and $\phi(z)=\frac12\sum_{i,h}u_{ih}^2$. Among the selected labels, 63 are positive and 45 are negative.

At every unselected nonzero vertex, the same verifier establishes the exact disjunction

$$ T(x;c)\geq10^{-8}\quad\text{or}\quad T(x;c)\leq-\gamma-10^{-8}. $$

There are 123,768 vertices in the first alternative and 138,267 in the second. Including the 108 selected vertices and the origin accounts for the entire cube. Define the remaining labels by this disjunction, and label the origin positive.

The verifier does not treat rounded floating values as exact roots or inequalities. It rounds every exact center-Jacobian entry to denominator $D$, checks the rounding error by cross-multiplication, multiplies integer matrices, and includes the rounding error in the displayed bounds. It checks the full-cube disjunction after multiplying by the three positive integer denominators. [audit.json](unit-minimum-certificate/audit.json) records the resulting exact bounds and source hashes. High-precision numerical refinement is used only to produce the candidate data.

## A certified nearby root

Put $m=108$, $r=10^{-40}$, and $\beta=10^{-3}$. On the closed infinity ball $C=\lbrace z:\lVert z-c\rVert_\infty\leq r\rbrace$, all slopes remain negative, every numerator coefficient has magnitude less than one, and

$$ B_h(x;z)\geq B_h(\mathbf{1};c)-18r\gt\beta. $$

The derivatives of a head are

$$ \frac{\partial T(x;z)}{\partial u_{ih}}=\frac{x_i}{B_h(x;z)},\qquad \frac{\partial T(x;z)}{\partial b_{ih}}=-\frac{x_iA_h(x;z)}{B_h(x;z)^2}. $$

Each entry of $J$ is Lipschitz on $C$, with respect to the infinity norm, with constant at most

$$ \frac{18}{\beta^2}+\frac{2\cdot18^2}{\beta^3}\lt10^{12}=:L. $$

For numerator columns, only the first summand is needed. For denominator columns, the first summand bounds changes in the numerator coefficients and the second bounds changes in the denominator coefficients. The factor 18 in the numerator magnitude follows from $|u_{ih}|\lt1$ and Boolean coordinates. The segment between any two points of $C$ stays in $C$, so these derivative bounds imply the stated Lipschitz bounds.

Define $G(z)=z-RF(z)$. On $C$,

$$ \lVert DG(z)\rVert_\infty\leq\lVert I-RJ(c)\rVert_\infty+\lVert R\rVert_\infty mLr\lt10^{-50}+10^5\cdot108\cdot10^{12}\cdot10^{-40}=:q\lt\tfrac12. $$

Also $\lVert G(c)-c\rVert_\infty\lt10^{-55}\lt r/2$. Therefore $G$ maps $C$ into itself and is a contraction. The contraction mapping theorem gives a unique fixed point $z^\ast\in C$. Since $\lVert I-RJ(c)\rVert_\infty\lt1$, the square matrices $R$ and $J(c)$ are invertible. Thus $G(z^\ast)=z^\ast$ implies $F(z^\ast)=0$.

The same norm estimate at $z^\ast$ proves that $J(z^\ast)$ is invertible and

$$ \lVert J(z^\ast)^{-1}\rVert_\infty\leq\frac{10^5}{1-q},\qquad \lVert J(z^\ast)^{-\top}\rVert_\infty\leq\frac{m10^5}{1-q}. $$

The factor $m$ in the transpose estimate follows by bounding each column sum by $m$ times the maximum absolute row sum.

## All cube margins persist

Every cube score is Lipschitz on $C$ with constant at most

$$ \frac{18\cdot3}{\beta}+\frac{18^2\cdot3}{\beta^2}\lt10^{10}=:K. $$

Consequently the change of any unselected score between $c$ and $z^\ast$ is at most $Kr=10^{-30}\lt10^{-8}/2$. The unselected positive scores remain positive and the unselected negative scores remain below $-\gamma$. The selected scores are exactly zero or $-\gamma$, according to their labels. The origin score is identically zero for $T$.

Hence the normalized score

$$ S(x)=1+\frac2\gamma T(x;z^\ast) $$

has signed margin at least one on every vertex. Its origin value is one. Exactly the selected 108 nonorigin vertices have unit margin. The coherent negative slopes and the strict positivity of every denominator ensure admissibility in the manuscript's exact model. Scaling the numerator coefficients by $2/\gamma$ is an invertible change of parameters and preserves the active Jacobian rank.

## Positive multipliers and strict local minimality

Define the exact multiplier vector by

$$ J(z^\ast)^\top Y\lambda^\ast=\nabla\phi(z^\ast). $$

The center residual, Jacobian Lipschitz estimate, and inverse-transpose estimate give

$$ \lVert\lambda^\ast-\lambda^0\rVert_\infty\leq\frac{m10^5}{1-q}\left(r+10^{-50}+mLr10^6\right)\lt\frac1{1000}. $$

The verifier checks the last numerical inequality exactly. Thus every multiplier satisfies $\lambda_r^\ast\gt1/500$.

For completeness, positivity and invertibility imply strict local minimality without a second-order assumption. Let $g(z)=YF(z)$ be the vector of active constraint slacks. Its derivative at $z^\ast$ is invertible, so the inverse function theorem supplies local coordinates $s=g(z)$ centered at zero. In these coordinates the objective $\psi(s)=\phi(g^{-1}(s))$ satisfies

$$ \nabla\psi(0)=\lambda^\ast. $$

Choose a sufficiently small open ball about zero on which every partial derivative of $\psi$ remains positive and on which the inverse coordinate map exists. If a distinct nearby point is feasible, its slack vector is a nonzero vector $s\geq0$. The segment $ts$, for $0\leq t\leq1$, lies in this ball, and

$$ \psi(s)-\psi(0)=\int_0^1\nabla\psi(ts)\cdot s dt\gt0. $$

Thus $z^\ast$ is a strict local minimum under the active inequalities. All other cube inequalities are strictly satisfied nearby, and the origin inequality is constant, so it is also a strict local minimum under the entire cube system.

The normalized numerator vector in $S$ is $(2/\gamma)u$. Its squared norm is the positive constant $(2/\gamma)^2$ times the squared norm of $u$. Consequently the same strict local minimum statement holds for the normalized score's numerator norm. This completes the written proof.

## Audit scope and remaining question

The analytic proof above uses explicit rational inequalities, the contraction mapping theorem, and the inverse function theorem. The exact verifier checks the numerical certificate without floating-point assertions. The Lean declarations `HeadComplexity.UnitMinimumCenter.unselected_score_gap` and `active_residual` check the center's entire cube gap and all selected residual bounds. `den_positive` checks denominator positivity. These declarations depend only on standard foundational axioms. The contraction and local-minimum deductions are written proofs, not claimed as Lean declarations.

This construction rules out a universal local-minimum rank-defect shortcut. It does not show that the constructed point is a global minimum, and it does not bound the number of local or global minima. A proposed argument using those stronger properties remains blocked until it supplies a new proof mechanism. The manuscript's architecture, unrestricted parameters, and definitions of head complexity and worst-case complexity are unchanged.
