# Full-Cube Active Margins with Positive Multipliers

## Statement and scope

Use the sixteen-bit, three-head score and the 96 selected vertices specified in `integer-zero-fiber-16.json`. Let $\theta=(u,b)\in\mathbb R^{96}$ contain all numerator and denominator slopes, with score constant fixed at one, and let

$$ F_i(\theta)=1+\sum_{h=1}^3\frac{u_h\cdot x_i}{1+b_h\cdot x_i},\qquad g(\theta)=\sum_{h,j}u_{hj}^2. $$

There is an explicit Boolean label table $Y:\lbrace0,1\rbrace^{16}\to\lbrace-1,1\rbrace$, with 54,004 positive entries, and a number $\epsilon_0\gt0$ such that, for every $0\lt\epsilon\lt\epsilon_0$, there is a parameter point $\theta_\epsilon$ satisfying all of the following. Write $y_i=Y(x_i)$ on the 96 selected vertices; these labels have 44 positive and 52 negative entries.

- Every denominator slope is strictly positive.
- Every selected signed score equals $\epsilon$.
- Every other cube vertex has signed score strictly greater than $\epsilon$.
- The selected evaluation Jacobian is invertible.
- The point is a strict local minimum of $g$ subject to all 65,536 signed margin inequalities, and also subject to just the 96 selected ones.
- The 96 active constraints have strictly positive stationarity multipliers; all other constraints are inactive.

This theorem gives one full-cube Boolean function and no asymptotic count of minima or sign patterns. The normalization fixes the score constant at one; it does not optimize over that constant. The complete label table is specified by the construction below and retained in hexadecimal form in `fullcube-active-minimum-checks.json`.

## Exact dual certificate

Let $\theta_0$ be the rational zero-score point from [the regular-zero construction](regular-coordinate-zeros.md), and put $J=DF(\theta_0)$. That construction proves $F(\theta_0)=0$ and $\det J\neq0$. The new independent verifier `verify_zero_fiber_dual.py` computes the unique rational vector

$$ v=J^{-\top}\nabla g(\theta_0) $$

and proves that all 96 coordinates are nonzero. Its complete rational entries and their signs are retained in `zero-fiber-dual-checks.json`. Define $y_i=\mathrm{sign}(v_i)$. Thus the label vector is explicitly determined by rational arithmetic on the supplied integer data.

For clarity, the exact linear system used in this computation is as follows. At selected row $r$, write $D_{hr}=1+b_h\cdot x_r$ and $U_{hr}=3u_h\cdot x_r$, both integers. Define

$$ d_r=3\prod_{h=1}^3D_{hr}^2,\qquad M=\mathrm{diag}(d_r)J,\qquad a=3\nabla g(\theta_0). $$

The matrix $M$ and vector $a$ have integer entries. Fraction-free elimination solves $M^\top w=a$ and checks the resulting rational solution by direct multiplication. The desired dual vector is

$$ v_r=d_rw_r/3. $$

A second check rebuilds the original rational score derivatives and verifies $J^\top v=\nabla g(\theta_0)$ directly, without using the row-cleared system. Two further independent computations solve the cleared system modulo 101 and 65521. Both determinants and all 96 solution coordinates are nonzero. Primality of the two moduli is checked by trial division. The exact rational check proves the claimed signs, rather than inferring signs from modular residues.

The integer certificate is also kernel checked in `CoordinateZeroDualData.lean`. Its rational interpretation is proved by `HeadComplexity.CoordinateZeroFiber.normDual_equation`, `normDual_ne_zero`, and `normDualLabel_mul_pos` in `CoordinateZeroDual.lean`. These declarations check the exact dual equation and strict positivity after multiplying by the specified labels. The analytic conclusion below is a written proof, not a Lean theorem.

## Proof of the analytic conclusion

Define $G(\theta)=\mathrm{diag}(y)F(\theta)$. Its derivative at $\theta_0$ is invertible. The inverse function theorem therefore gives a continuously differentiable inverse $\psi$ on a neighborhood of zero, with $G(\psi(z))=z$ and $\psi(0)=\theta_0$. Shrink this neighborhood so that every denominator slope remains strictly positive and every evaluation Jacobian remains invertible.

Put $\widetilde g=g\circ\psi$. The chain rule and the definition of $y$ give

$$ \nabla\widetilde g(0)=\mathrm{diag}(y)J^{-\top}\nabla g(\theta_0)=(|v_1|,\ldots,|v_{96}|). $$

Every component is strictly positive. By continuity and finiteness, choose an open box $(-\eta,\eta)^{96}$ on which every partial derivative of $\widetilde g$ is positive. Set $\epsilon_0=\eta/2$ and $\theta_\epsilon=\psi(\epsilon\mathbf1)$.

Consider any distinct feasible point in the inverse image of this box. Its image $z$ satisfies $z_i\geq\epsilon$ for all $i$, with at least one strict inequality. The segment from $\epsilon\mathbf1$ to $z$ lies in the box. Along that segment,

$$ \frac{d}{dt}\widetilde g\bigl(\epsilon\mathbf1+t(z-\epsilon\mathbf1)\bigr)=\sum_i\frac{\partial\widetilde g}{\partial z_i}\bigl(\epsilon\mathbf1+t(z-\epsilon\mathbf1)\bigr)(z_i-\epsilon)\gt0. $$

Integration proves $g(\psi(z))\gt g(\theta_\epsilon)$. This proves the strict local minimum. Finally, let $\lambda=\nabla\widetilde g(\epsilon\mathbf1)$. Every $\lambda_i$ is positive, and the chain rule gives the exact stationarity equation

$$ \nabla g(\theta_\epsilon)=DF(\theta_\epsilon)^\top\mathrm{diag}(y)\lambda. $$

All 96 selected constraints are active because $G(\theta_\epsilon)=\epsilon\mathbf1$. This proves the selected-constraint assertions.

## Compatibility with every remaining cube vertex

The independent verifier `verify_fullcube_active_minimum.py` enumerates the whole cube with exact integers, updating the three affine numerators and denominators along a Gray code. At the base point there are exactly 106 zero scores. The smallest absolute value among the other 65,430 scores is exactly $1/31671$.

Let $Z$ be this 106-point zero set. Solve the exact rational system

$$ J\Delta=y. $$

The file `fullcube-active-minimum-checks.json` retains every coordinate of $\Delta$. At the ten vertices in $Z$ outside the selected set, the verifier checks

$$ |DS_x(\theta_0)\Delta|\gt14. $$

These ten vertices are $51619,51699,58635,59558,60434,60517,60948,61811,64336,64452$. Define $Y$ at them as the sign of the displayed derivative. Define $Y$ at each nonzero base-score vertex as the sign of that score, and use the already specified labels on the selected vertices. This defines $Y$ everywhere. The integer enumeration, rational tangent system, and all ten inequalities are checked explicitly, independently of the earlier numerical search.

Differentiating the inverse identity gives $\theta'_0=\Delta$. Therefore, at each of the ten extra zero vertices,

$$ Y(x)S_x(\theta_\epsilon)=\epsilon|DS_x(\theta_0)\Delta|+o(\epsilon)\gt\epsilon $$

for all sufficiently small positive $\epsilon$. At every nonzero base-score vertex, continuity and the positive minimum $1/31671$ imply $Y(x)S_x(\theta_\epsilon)\gt\epsilon$ after a further uniform shrinkage of $\epsilon_0$. There are only finitely many vertices, so one positive $\epsilon_0$ works for all of them.

Thus every full-cube constraint is satisfied and exactly the selected 96 are active. The strict local minimum already proved on the larger selected-constraint feasible set remains a strict local minimum on the full-cube feasible set. The same multipliers, extended by zero on inactive constraints, give its stationarity equation. This completes the proof. $\blacksquare$

The full-cube enumeration and rational tangent checks use independent exact Python arithmetic. The Lean declarations certify the zero-fiber data and norm dual, but do not claim to formalize the complete cube enumeration, analytic continuation, or local-minimum theorem.

For each fixed $\epsilon$, dividing the entire score by $\epsilon$ gives selected margins equal to one and all other margins greater than one. This changes the fixed constant to $1/\epsilon$ and scales the numerator-norm objective by $1/\epsilon^2$. It preserves the local-minimum statement on that fixed-constant slice. It does not prove a unit-margin statement on the slice whose constant is fixed at one.

## Consequence for the attempted counting mechanism

This example disproves an assertion that positive denominator slopes, binary equal-magnitude active scores, and strictly positive inequality multipliers force rank loss or rule out interior constrained minima. A maximum principle for individual score functionals does not apply to the feasible corner formed by 96 independent inequalities.

It supplies a local minimum for one full-cube label table. A bound on the total number of relevant minima sufficient to improve the worst-case head lower bound is still missing. No exponent strictly between one and two, and no unbounded factor over the manuscript's lower bound, follows from this result.
