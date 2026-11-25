# Two-extremum head duplication and the remaining joint gap

## Statement and status

This note extends the smooth duplication test in `unrestricted_capacity_full_cube_norm.md` to a tie between the two interval-budget branches. It uses the actual full-cube head suprema. The first-order and second-order optimization hypotheses below are explicit. The linear algebra that closes the Hessian identity is kernel checked; existence of a global optimum with the stated regularity is not asserted.

Let the score be $S=b+\sum_h A_h/B_h$, with positive affine denominators and admissible strict coherent slope orientation. Suppose each nonconstant head has a unique maximum $u_h$ at $p_h$ and a unique minimum $l_h$ at $q_h$. The optimally redistributed amplitude is

$$ K=\max\left(b+\sum_h u_h,-b-\sum_h l_h\right). $$

Use unit signed constraints $f(x)S(x)\geq1$. Let $\lambda_x\geq0$ be their multipliers, put $\mu_x=\lambda_xf(x)$, and let $\tau\in[0,1]$ be the multiplier on the upper interval branch. Write $z_x=(1,x)$ and suppress the head index.

The first-order equations for this head are

$$ \sum_x\mu_x\frac{z_x}{B(x)}=\tau\frac{z_p}{B(p)}-(1-\tau)\frac{z_q}{B(q)},\qquad \sum_x\mu_x\frac{A(x)z_x}{B(x)^2}=\tau u\frac{z_p}{B(p)}-(1-\tau)l\frac{z_q}{B(q)}. $$

Define the residual signed Hessian

$$ M=\sum_x\mu_x\frac{z_xz_x^\top}{B(x)^2}-\tau\frac{z_pz_p^\top}{B(p)^2}+(1-\tau)\frac{z_qz_q^\top}{B(q)^2}. $$

The equations imply $Ma=Mb=0$, where $a,b$ are the affine coefficient vectors of $A,B$.

## Duplication with both endpoint values fixed

Replace the head by two half-weight heads

$$ \frac12\frac{A+\varepsilon C}{B+\varepsilon D}+\frac12\frac{A-\varepsilon C}{B-\varepsilon D}. $$

For any affine $D$, impose $C(p)=uD(p)$ and $C(q)=lD(q)$. Both endpoint values then remain exactly fixed. Unique extrema and strict coherent admissibility persist for sufficiently small $\varepsilon$. Hence both interval budgets remain unchanged, including when they are tied. The first score derivative vanishes on every cube row.

Add $tE$ to $C$, where $E(p)=E(q)=0$ and $t$ is any real number. A valid second-order necessary condition at a duplicated local minimum forces

$$ \sum_x\mu_x\frac{E(x)D(x)}{B(x)^2}=0 $$

for every such $E$ and every affine $D$: otherwise the coefficient of $t$ changes sign. Since the endpoint terms vanish, this is $E^\top MD=0$.

The determinant of the endpoint values of $A,B$ is

$$ A(p)B(q)-A(q)B(p)=(u-l)B(p)B(q)\neq0. $$

Every affine form is therefore an endpoint-zero form plus a linear combination of $A,B$. The first-order identities and the duplication identities together give $M=0$.

`TwoExtremumDuplication.ratio_endpoint_annihilator` formalizes precisely this final implication for an arbitrary vector subspace of real functions. `two_endpoint_annihilator` supplies the explicit Cramer decomposition, and `endpoint_det_ne_zero` supplies the displayed determinant. The analytic KKT and second-order bridge remains a written argument under its stated regularity hypotheses.

## What the identity does and does not imply

The matrix identity has positive-semidefinite sides:

$$ \sum_{f(x)=1}\lambda_x\frac{z_xz_x^\top}{B(x)^2}+(1-\tau)\frac{z_qz_q^\top}{B(q)^2}=\sum_{f(x)=-1}\lambda_x\frac{z_xz_x^\top}{B(x)^2}+\tau\frac{z_pz_p^\top}{B(p)^2}. $$

Consequently the span of the positive active rows lies in the span of the negative active rows together with $z_p$. If all active rows span the full affine coordinate space, at least $n$ negative active rows are needed. This is a lower bound on minority support, not a compression theorem giving small minority support.

For several heads, the same signed measure satisfies one such identity per head, with head-dependent denominators and extrema. At widths near $N/n^{3/2}$ the total number of quadratic reciprocal features is larger than $N$. It is tempting to conclude that the denominators must belong to a low-dimensional class. No rank theorem justifying that inference is proved: each identity has different endpoint corrections, and arbitrary signed cancellation remains present.

The existing cross-moment computation gives a separate obstruction. If $g_h=u_h-A_h/B_h$ and the upper branch is active, the diagonal moments vanish while

$$ \sum_{h,k}\sum_x\mu_xg_h(x)g_k(x)=1-K^2. $$

Thus $K\gt1$ forces a negative cross moment. A new norm-controlled joint replacement would need to turn that cross moment into a feasible score direction with controlled head overhead and amplitude. A value approximation whose individual head norms diverge does not supply this step. A local improvement after doubling width also does not bound the number of further doublings or prove a prescribed relative margin.

## Precise remaining lemma

One possible sufficient route is a quantitative replacement theorem: whenever a width $H$ representation has relative margin below the target, there is a joint replacement using at most $CH$ admissible heads that increases the margin by a controlled amount, and the iteration can be implemented without accumulating head support beyond $CH$. The duplication calculation supplies neither the quantitative gain nor the support-recycling statement. It also does not cover extrema ties within a head, denominator boundary strata, or failure of the optimization regularity hypotheses. The unrestricted lower-bound target remains open.
