# Convex Perspective Form and Its Counting Obstruction

## Exact score transformation

Fix a head orientation. Write $\phi_{h0}(x)=1$ and, for $i\geq1$, write $\phi_{hi}(x)=x_i$ in the positive orientation or $\phi_{hi}(x)=1-x_i$ in the negative orientation. A denominator with strictly signed slopes then has the form

$$ B_h(x)=\sum_{i=0}^n b_{hi}\phi_{hi}(x),\qquad b_{hi}\gt0. $$

An arbitrary affine numerator has the form $A_h(x)=\sum_i a_{hi}\phi_{hi}(x)$. Choose $q_h$ so large that $a_{hi}+q_hb_{hi}\gt0$ for every $i$, and put $s_{hi}=\sqrt{a_{hi}+q_hb_{hi}}$. For a score $S(x)=c+\sum_h A_h(x)/B_h(x)$, set $T=\sum_hq_h-c$. Then the following is an exact identity on every input:

$$ S(x)=\sum_{h=1}^H\sum_{i=0}^n\frac{s_{hi}^2\phi_{hi}(x)}{\sum_{j=0}^n b_{hj}\phi_{hj}(x)}-T. $$

The choices of $q_h$ can also make $T$ positive when $H\geq1$. Conversely, every score of the displayed form has affine numerators and admissible strictly oriented denominators, so it is an exact-model score. This is a change of parameters for each fixed orientation pattern, not a restriction to bounded or rational coefficients.

The constant-denominator case is covered for classification by strictification and continuity. First subtract a sufficiently small positive bias from a finite-cube classifier so that both label classes have strict margins. Replace every constant denominator $b_0$ by $b_0+\varepsilon\sum_i x_i$, leaving the affine numerator unchanged. All finitely many scores converge to their original values as $\varepsilon\downarrow0$, so one sufficiently small positive $\varepsilon$ preserves all signs. Each perturbed ratio is an admissible positive-orientation head. The case $H=0$ consists of constant scores and requires no transformation.

## Convexity and a linear matrix inequality

For $b,d\gt0$ and $0\leq t\leq1$, direct algebra gives

$$ t\frac{a^2}{b}+(1-t)\frac{c^2}{d}-\frac{(ta+(1-t)c)^2}{tb+(1-t)d}=\frac{t(1-t)(ad-cb)^2}{bd(tb+(1-t)d)}\geq0. $$

Thus, for each fixed input, the transformed score is jointly convex in the numerator parameters $s$, denominator parameters $b$, and threshold $T$. Nonnegative weights $\phi_{hi}(x)$ preserve the inequality, and each denominator is affine in $b$. This is the quadratic-over-linear perspective construction described in [Boyd and Vandenberghe's convex optimization slides, section 3](https://web.stanford.edu/~boyd/cvxbook/bv_cvxslides.pdf).

There is also an explicit matrix form. Let $v_x$ have entries $s_{hi}\sqrt{\phi_{hi}(x)}$, and let $D_x$ be diagonal, with entry $B_h(x)$ repeated for each $i$. Since $D_x$ is positive definite,

$$ \begin{pmatrix}T&v_x^{\top}\cr v_x&D_x\end{pmatrix}\succeq0\quad\Longleftrightarrow\quad T\geq v_x^{\top}D_x^{-1}v_x\quad\Longleftrightarrow\quad S(x)\leq0. $$

For completeness, the equivalence follows by completing the square in its quadratic form:

$$ Tz^2+2zv_x^{\top}y+y^{\top}D_xy=(y+zD_x^{-1}v_x)^{\top}D_x(y+zD_x^{-1}v_x)+z^2(T-v_x^{\top}D_x^{-1}v_x). $$

All matrix entries are linear in the transformed parameters. Therefore a false-label constraint is an intersection of the positive denominator domain with a spectrahedral cone. A true-label constraint is its complement in that domain. Convexity of false-label constraints does not make a mixed-label feasibility problem convex.

## Arbitrary membership patterns in three dimensions

The following exact construction rules out a counting theorem that uses only convexity, positive scaling, and a common strict interior point.

For integers $r,q\geq0$, define

$$ p_r=(r,r^2,1),\qquad \ell_q(u,v,w)=v-2qu+(q^2-1/2)w. $$

Then

$$ \ell_q(p_r)=(r-q)^2-1/2, $$

which is negative when $r=q$ and positive otherwise. For any finite set $E$ of nonnegative integers, put

$$ K_E=\lbrace (u,v,w):w\geq0, \ell_q(u,v,w)\geq0\text{ for every }q\in E\rbrace. $$

This is a closed convex polyhedral cone, and

$$ p_r\in K_E\quad\Longleftrightarrow\quad r\notin E. $$

The point $(0,1,1)$ satisfies every defining inequality strictly, since $\ell_q(0,1,1)=q^2+1/2\gt0$. For each finite $E$, continuity and finiteness therefore give a neighborhood contained in $K_E$.

To realize an arbitrary finite incidence matrix $L_{jr}\in\lbrace0,1\rbrace$, choose $E_j=\lbrace r:L_{jr}=0\rbrace$. The point $p_r$ belongs to $K_{E_j}$ exactly when $L_{jr}=1$. In particular, taking the columns to be all $2^m$ binary strings gives $m$ cones with all $2^m$ membership patterns, in dimension three, with a common strict interior point. These polyhedral cones are also spectrahedral: put all defining linear forms on the diagonal of a matrix.

This counterexample does not have the shared arrow-matrix structure of the head constraints. It proves only that convexity and general spectrahedral representability do not supply the desired bound. A bound for that specific shared structure, strong enough at $H=\Theta(2^n/n^2)$, remains unproved. The approach is blocked at that theorem-strength gap.

## Formal audit

`formalization/HeadComplexity/Atoms/ConvexPerspective.lean` proves the exact perspective identity, its weighted convexity inequality, the square-coefficient shift identity, and the arbitrary finite incidence construction. Its `arbitrary_incidence` declaration proves convexity, closure under nonnegative scaling, and every required membership equivalence. `common_strict_point` proves strict slack for all defining inequalities at the common point. The conversion of full attention scores, the neighborhood argument, and the matrix equivalence are written proofs above. No declaration in this file asserts the main asymptotic lower bound.
