# The Amplitude Polytope and Its Interior Maximum Principle

## Statement and scope

Fix $n\geq2$. Consider all affine-ratio tables $F(x)=(a_0+\sum_i a_ix_i)/(1+\sum_i b_ix_i)$ on the Boolean cube, with every $b_i\gt0$ and $\|F\|_\infty\leq1$. No nonconstant table in this family is a strict local maximum of any real linear functional of the table entries, where local maximality is measured in the table image.

The same conclusion holds with strictly negative coherent slopes after complementing all input coordinates. If the exact model's constant-denominator case is included, the only possible strict local maxima are the two constant tables and signed single-coordinate literals. These exceptions are necessary: a Boolean table of either type is uniquely maximized over all amplitude-one tables by its own correlation functional.

There is a stronger statement for a generic functional: if its coefficients at all singleton and two-coordinate vertices are nonzero, no nonconstant positive-slope table is even a nonstrict local maximum. The condition need not hold for a functional supported on active classification constraints.

This is a statement about a bounded one-head family. It does not count feasible classification chambers or prove a lower bound on the number of heads. The obstruction to that transfer is exhibited at the end.

## The exact numerator polytope

For fixed $b_i\geq0$, the allowed numerator coefficients form the polytope

$$ P_b=\left\lbrace(a_0,a):\sum_i(a_i-b_i)_+\leq1-a_0,\quad\sum_i(-a_i-b_i)_+\leq1+a_0\right\rbrace. $$

Here $t_+=\max(t,0)$. Indeed $A(x)\leq D(x)$ for every Boolean $x$ is equivalent to $a_0+\sum_i(a_i-b_i)_+\leq1$. Apply the same argument to $-A$ for the other inequality.

There is an explicit Minkowski-sum description:

$$ P_b=\bigl(\lbrace0\rbrace\times\prod_i[-b_i,b_i]\bigr)+\mathrm{conv}\left(\lbrace\pm(1,0)\rbrace\cup\lbrace\pm(1,-2e_i):1\leq i\leq n\rbrace\right). $$

**Proof.** Put $p_i=(a_i-b_i) _+$, $m_i=(-a_i-b_i) _+$, and $d_i=\min(b_i,\max(-b_i,a_i))$. Then $a_i=d_i+p_i-m_i$ and $|d_i|\leq b_i$. The point $(a_0,p-m)$ is the convex combination with weights

$$ \theta_{+,0}=\frac{1+a_0-\sum_i m_i}{2},\qquad\theta_{-,0}=\frac{1-a_0-\sum_i p_i}{2},\qquad\theta_{+,i}=\frac{m_i}{2},\qquad\theta_{-,i}=\frac{p_i}{2}. $$

They are nonnegative by the two budgets and sum to one. Their first coordinate is $a_0$, and their coordinate $i$ is $p_i-m_i$. This proves one inclusion. Conversely each listed generator satisfies the budgets after addition of any point of the box, and the budgets define a convex set. This proves equality. $\blacksquare$

Every vertex of this finite Minkowski sum is a sum of vertices of the two summands. This follows directly by expanding both points as convex combinations of their vertices: an extreme point of the resulting convex hull must be among the finitely many vertex sums. Consequently every vertex numerator has the form

$$ A_{s,i,\tau}(b,x)=\sum_j s_jb_jx_j+\tau\ell_i(x),\qquad s_j\in\lbrace-1,1\rbrace,\quad\tau\in\lbrace-1,1\rbrace, $$

where $\ell_0(x)=1$ and $\ell_i(x)=1-2x_i$ for $1\leq i\leq n$. Some of these vertex sums need not be extreme; the inclusion is all that is needed. Every displayed numerator is feasible for every $b\geq0$, since its absolute value is at most $1+\sum_jb_jx_j$.

## Harmonicity of every vertex branch

Fix $s,i,\tau$, and let $F(b,x)=A_{s,i,\tau}(b,x)/D(b,x)$. Put $B=\mathrm{diag}(b)+bb^\top$ and

$$ \mathcal L=\sum_{j,k}B_{jk}\partial_{b_jb_k}+2\sum_jb_j\partial_{b_j}. $$

Then $\mathcal LF(b,x)=0$ for every Boolean vertex. In particular every fixed linear functional $h(b)=\sum_x\mu_xF(b,x)$ satisfies $\mathcal Lh=0$.

**Proof.** Fix $x$, and abbreviate $N=A_{s,i,\tau}(b,x)$, $r=\sum_jb_jx_j$, and $C=\sum_js_jb_jx_j$. The constant term $\tau\ell_i(x)$ does not vary with $b$. Differentiation gives

$$ \partial_jF=\frac{s_jx_j}{D}-\frac{Nx_j}{D^2},\qquad\partial_{jk}F=-\frac{(s_j+s_k)x_jx_k}{D^2}+\frac{2Nx_jx_k}{D^3}. $$

Using $x_j^2=x_j$, one has $x_j(Bx)_j=b_jx_jD$ and $x^\top Bx=rD$. Thus the second-order part equals $-2C/D+2Nr/D^2$, while the first-order part equals $2C/D-2Nr/D^2$. Their sum is zero. Finally

$$ z^\top Bz=\sum_jb_jz_j^2+(b\cdot z)^2\gt0\qquad(z\neq0), $$

so $\mathcal L$ is elliptic on the positive orthant. $\blacksquare$

This calculation retains the dependence of the extreme numerator on the denominator coefficients. Holding those numerator coefficients fixed would be a different parameter path.

## An analytic local maximum principle

We give the needed local principle directly. Let a real analytic function $h$ satisfy a second-order linear equation whose coefficients are analytic, whose second-order coefficient matrix is positive definite, and whose zeroth-order coefficient is zero. If $h$ has a local maximum at an interior point, it is constant in a neighborhood of that point.

**Proof.** Subtract the value of $h$ at the point and translate the point to zero. If the Taylor series is not identically zero, let $P$ be its first nonzero homogeneous part, of degree $k$. Local maximality implies $k\geq2$ and $P(z)\leq0$ for every real $z$. The terms of degree $k-2$ in the differential equation give

$$ \sum_{j,l}B_{jl}(0)\partial_{jl}P=0. $$

An invertible linear change of variables converts this equation to $\Delta Q=0$ for a nonzero homogeneous polynomial $Q$ of degree $k$, still nonpositive everywhere. The divergence theorem and homogeneity give

$$ 0=\int_{\mathrm{ball}}\Delta Q=k\int_{\mathrm{sphere}}Q. $$

A continuous nonpositive nonzero homogeneous polynomial has strictly negative integral on the unit sphere, a contradiction. Therefore all nonconstant Taylor coefficients vanish. Real analyticity gives the asserted local constancy. $\blacksquare$

This is the analytic special case of the classical strong maximum principle. No uniform ellipticity at the boundary of the positive orthant is used.

## Proof of the table-image statement

Suppose a table $F_0$ with positive slopes is a strict local maximum of a linear functional on the bounded table family. Fix one coefficient representation $(a^0,b^0)$ of it. If $a^0$ is not a vertex of $P_{b^0}$, a nontrivial segment in this polytope passes through $a^0$ in its relative interior. Fixed-denominator evaluation is injective on affine numerators, and the functional is linear along the segment. It cannot have a strict local maximum at its interior point. Hence $a^0$ is a vertex.

Choose a vertex branch $A_{s,i,\tau}$ representing $a^0$. For every nearby positive $b$, its table remains feasible. The resulting height $h(b)$ has a local maximum at $b^0$. The harmonicity and analytic maximum principle prove that $h$ is constant in a neighborhood. Strictness in the table image would therefore force the entire table $F(b,\cdot)$ to be constant as a function of $b$ on that neighborhood.

The only vertex branches with this property, for $n\geq2$, are the constant tables. To verify this, fix a vertex $x$. Constancy of the rational function of $b$ means that its constant and each linear coefficient agree after multiplying by $D$. Thus, whenever $x_j=1$,

$$ F_0(x)=s_j=\tau\ell_i(x). $$

For $i=0$, apply this at every singleton to obtain $s_j=\tau$, and then $F\equiv\tau$. For $i\neq0$, the singleton $e_i$ forces $s_i=-\tau$. Choose $j\neq i$; its singleton forces $s_j=\tau$. At $e_i+e_j$, the two coefficient equations force $s_i=s_j$, a contradiction. This proves the positive-slope statement.

Complementing all input coordinates and rescaling by the positive constant term converts strictly negative coherent slopes to strictly positive slopes and preserves the table norm and strict local maximality. Finally, at constant denominator the coefficient polytope is exactly the second summand of the displayed Minkowski sum. A nonvertex again cannot give a strict local maximum, so only constants and signed literals remain. $\blacksquare$

## The stronger generic-functional statement

Every bounded table admits an entire feasible harmonic parameter family through it, without an extreme-point hypothesis. Use the clipping decomposition above, set $c_i=d_i/b_i\in[-1,1]$, and put $k(x)=a_0+\sum_i(p_i-m_i)x_i$. The convex-combination proof gives $|k(x)|\leq1$ on the cube. For every new positive slope vector $b'$, the table

$$ F(b',x)=\frac{k(x)+\sum_i c_i b_i'x_i}{1+\sum_i b_i'x_i} $$

is therefore bounded by one. It agrees with the original table at $b'=b$, and the same harmonic calculation applies with $s_i$ replaced by $c_i$ and the constant numerator term replaced by $k(x)$.

Suppose a functional $\mu$ has a local maximum at the original table. The height on this feasible family has a local maximum, so it is constant on a neighborhood. Being rational, it is then a constant rational function. For any nonzero vertex $x$, the linear denominator $1+b'\cdot x$ is distinct and nonproportional to every other vertex denominator. Clear denominators in the constant identity, then restrict to the hyperplane $1+b'\cdot x=0$. If $\mu_x\neq0$, the numerator $k(x)+\sum_i c_i b_i'x_i$ vanishes on that hyperplane and is a scalar multiple of its denominator. One may justify the restriction by excluding the finite union of intersections with other denominator hyperplanes; the remaining subset is dense in the chosen hyperplane. Since the numerator is linear, vanishing there proves the stated divisibility.

Apply this to all singleton and pair vertices. The singletons give $k(e_i)=c_i$. The pairs give

$$ c_i=c_j=k(e_i+e_j)\qquad(i\neq j). $$

Thus all $c_i$ equal one constant $c$. Since $k$ is affine, $k(e_i+e_j)=k(e_i)+k(e_j)-k(0)$ implies $k(0)=c$, and then all its nonconstant coefficients vanish. Therefore $k\equiv c$ and the entire feasible family, including the original table, is the constant table $c$. This proves the stronger assertion. $\blacksquare$

## The classification transfer is still blocked

The theorem concerns an unconstrained linear functional on one bounded atom family. A minimum of a norm subject to every signed classification inequality is a different problem. Its second-order necessary condition applies only to directions that preserve the active constraints to first order. It does not assert that each individual atom is an unconstrained local maximum of its multiplier functional.

Even harmonicity of every score coordinate does not permit pushing a feasible point to the boundary of parameter space while preserving all signs. An explicit counterexample consists of the four harmonic polynomials

$$ 1+(u^2-v^2),\qquad1-(u^2-v^2),\qquad1+2uv,\qquad1-2uv. $$

All four are positive at the origin. Their common positive region is bounded, because positivity implies $|u^2-v^2|\lt1$ and $|2uv|\lt1$, and

$$ (u^2+v^2)^2=(u^2-v^2)^2+(2uv)^2\lt2. $$

This example is an obstruction to an inference from harmonicity alone; it is not asserted to be an attention-head parameterization. A theorem controlling the simultaneous signed inequalities for the actual head family is still needed. Neither the maximum principle nor the numerator-polytope decomposition supplies it, and the selected asymptotic target remains unproved.

The generic-functional strengthening does not fix this issue. Classification multipliers can vanish at every singleton and pair vertex, and a constrained minimum still need not maximize the multiplier functional on an individual unconstrained atom. Also, any proposed deformation replacing each head by one coordinate priority list while retaining all labels is already ruled out by the [proved parity separation](parity-priority-separation.md). These transfer steps are not being assumed.

## Verification scope

`AmplitudePolytope.lean` checks the clipping decomposition, the explicit nonnegative convex weights and their coefficient identities, the amplitude inequality for vertex branches, the product-rule cancellation for choice probabilities, positivity of the elliptic metric, and the bounded harmonic chamber. The polytope vertex argument, analytic maximum principle, and full table-image theorem are the written proofs above. They are not asserted to be complete Lean declarations.
