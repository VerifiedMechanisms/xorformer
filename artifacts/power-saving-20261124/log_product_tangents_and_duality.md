# Log product tangents and the fixed-denominator alternative

## Scope

Every original affine-ratio score is a tangent derivative of a product of positive affine forms. This observation preserves the original model, but the useful dual potential has signed weights and need not be convex or concave, even after removing the denominator scaling freedom. The exact reformulation and a two-bit Hessian calculation are recorded here. They do not establish an improved unrestricted head lower bound.

## Original scores are log product tangents

Let $H\geq1$, and let

$$ S(x)=c+\sum_{h=1}^H\frac{A_h(x)}{B_h(x)} $$

be an admissible original score on the Boolean cube. Absorb the bias into the first numerator by replacing $A_1$ by $A_1+cB_1$. This preserves its original admissibility: for a nonconstant denominator the numerator is arbitrary, and for a constant denominator the added term is constant and does not change the numerator slopes.

Write the resulting numerators as $D_h$, and define

$$ B_h(t,x)=B_h(x)+tD_h(x),\qquad Q_t(x)=\prod_{h=1}^H B_h(t,x). $$

There is an interval about $t=0$ on which every factor is positive on the entire continuous cube. Indeed, positivity on its finitely many vertices persists for small $t$, and an affine function attains its minimum on the cube at a vertex. For nonconstant denominators, their strict common slope signs persist for small $t$ as well. For a constant denominator, the slopes of the perturbed form are $t$ times the coherent numerator slopes; every nonzero sufficiently small $t$ therefore still has an allowed coherent orientation. A constant numerator leaves the denominator constant.

Consequently, for every cube input,

$$ \left.\frac{d}{dt}\log Q_t(x)\right|_{t=0}=\sum_{h=1}^H\frac{D_h(x)}{B_h(x)}=S(x). $$

For each sufficiently small fixed $t$, the function $x\mapsto\log Q_t(x)$ is concave on the continuous cube, since it is a sum of logarithms of positive affine functions. This does not imply concavity of its tangent derivative in $t$.

The forward construction is all that is asserted. At a constant denominator, an arbitrary path of coherent nonconstant forms can have a first derivative with some zero slopes and some nonzero slopes. Such a derivative need not satisfy the original constant-denominator numerator restriction, so an unrestricted converse about all paths would require care.

## The exact fixed-denominator dual

Let $X$ be a finite subset of $\mathbb R^n$, let $v_x=(1,x)$, and fix positive affine denominators $B_h(x)=b_h\cdot v_x$ with $H\geq1$. In this section allow all affine numerators for these fixed denominators. This agrees with the original model when every denominator is nonconstant. Allowing arbitrary numerators at constant denominators is an enlargement, so dual certificates obtained below still prove nonrepresentability there.

For a strict label table $F:X\to\lbrace-1,1\rbrace$, the following are equivalent:

1. There are affine numerators and a bias giving a score with $F(x)S(x)\gt0$ for every $x\in X$.

2. There is no nonzero vector $\lambda\in\mathbb R^X$ with $\lambda_x\geq0$ and

$$ \sum_{x\in X}\lambda_xF(x)\frac{v_x}{B_h(x)}=0\qquad\text{for every }h. $$

**Proof.** Apply the finite-dimensional strict Gordan alternative to the matrix with rows $F(x)(v_x/B_h(x))_h$. The numerator coefficients are its unrestricted linear variables. The bias is already included in this linear span, since $B_1/B_1=1$.

Equivalently, any vector satisfying the displayed equalities also satisfies

$$ \sum_x\lambda_xF(x)=b_h\cdot\sum_x\lambda_xF(x)\frac{v_x}{B_h(x)}=0, $$

so a separately added bias column introduces no missing dual condition. $\blacksquare$

Define the signed log potential on the open cone where all $b\cdot v_x$ are positive:

$$ \Phi_\lambda(b)=\sum_{x\in X}\lambda_xF(x)\log(b\cdot v_x). $$

Its gradient and Hessian are

$$ \nabla\Phi_\lambda(b)=\sum_x\lambda_xF(x)\frac{v_x}{b\cdot v_x},\qquad \nabla^2\Phi_\lambda(b)=-\sum_x\lambda_xF(x)\frac{v_xv_x^{\top}}{(b\cdot v_x)^2}. $$

Thus a fixed-denominator label table fails to be represented exactly when there is one nonzero nonnegative $\lambda$ for which all $b_h$ are critical points of the same signed log potential. To exclude a label from the original class of width $H$, one must produce such a common certificate for all heads in each permitted denominator configuration. The certificate may depend on that configuration. This dual reformulation does not by itself provide the needed uniform exclusion.

## Positivity does not make the dual potential convex

Take the two-bit cube, put $\lambda_x=1$ at every vertex, and take the parity labels

$$ F(0,0)=F(1,1)=1,\qquad F(1,0)=F(0,1)=-1. $$

Normalize the denominator constant to one and use strictly positive slopes $u,v$. The resulting potential is

$$ \Phi(u,v)=-\log(1+u)-\log(1+v)+\log(1+u+v). $$

At the strictly coherent point $u=v=1/2$, its Hessian is

$$ \nabla^2\Phi(1/2,1/2)=\frac1{36}\begin{pmatrix}7&-9\cr-9&7\end{pmatrix}. $$

The eigenvalue in direction $(1,1)$ is $-1/18$, and the eigenvalue in direction $(1,-1)$ is $4/9$. Hence the Hessian is indefinite within the normalized positive-slope parameter domain. This is not an artifact of the radial scaling direction or of a denominator approaching zero.

The calculation shows precisely where the direct log-concavity argument fails: the dual potential weights the logs by $\lambda_xF(x)$, and those coefficients have both signs. It does not rule out a different theorem controlling its simultaneous critical-point configurations or counting actual Boolean labels.

## Interior critical-point saddles in every dimension

The loss of convexity persists at points satisfying the dual equations. Let $n\geq2$, take the $n$-bit cube, let $F(x)=(-1)^{|x|}$, and put $B(x)=1+|x|$. Fix the positive weights $\lambda_x=1+|x|$ independently of the variable denominator coefficients. At $b=(1,\ldots,1)$,

$$ \nabla\Phi_\lambda(b)=\sum_xF(x)v_x=0, $$

since parity sums to zero against every affine function on this cube. Thus these weights give an actual fixed-denominator dual certificate.

Keep the constant coefficient normalized to one. To compute the Hessian in the $n$ slope coordinates, use $1/(1+k)=\int_0^1t^kdt$. Expanding the independent Boolean coordinates gives the diagonal and distinct-coordinate entries:

$$ \begin{aligned} d&=-\sum_x\frac{F(x)x_i}{1+|x|}=\int_0^1t(1-t)^{n-1}dt=\frac1{n(n+1)},\cr o&=-\sum_x\frac{F(x)x_ix_j}{1+|x|}=-\int_0^1t^2(1-t)^{n-2}dt=-\frac2{(n-1)n(n+1)}\quad(i\neq j).\end{aligned} $$

The displayed integrals follow directly by one and two integrations by parts, respectively. The Hessian is $(d-o)I+oJ$, where $J$ is the all-ones matrix. Its eigenvalues are therefore

$$ d+(n-1)o=-\frac1{n(n+1)}\quad\text{on the all-ones direction},\qquad d-o=\frac1{n(n-1)}\quad\text{on its perpendicular space}. $$

Every dimension $n\geq2$ thus has a dual critical-point saddle strictly inside the normalized positive-slope domain. For $n=3$ this is $(2I-J)/12$, with eigenvalues $-1/12$ and $1/6$. This excludes a direct argument that every relevant critical point is a convex minimum or a concave maximum.

## Strictly positive dual weights can fail at polynomial width

The nonnegative weights in Gordan's alternative cannot in general be strengthened to weights positive at every vertex, even for prescribed configurations with only polynomially many heads.

**Proposition.** Let $n\geq1$, fix a vertex $v$, and write $r=|v|$. There are $L=(r+1)(n-r+1)$ strictly positive coherent denominators such that their affine-numerator span contains the exact table $\mathbf 1_{\lbrace v\rbrace}$. In particular $L\leq(n+2)^2/4$.

**Proof.** Choose a positive irrational $\varepsilon$ and put

$$ B(x)=1+\varepsilon|x|,\qquad C(x)=\sum_{i:v_i=0}x_i+\sum_{i:v_i=1}(1-x_i),\qquad q(x)=\frac{C(x)}{B(x)}. $$

If $a$ counts ones outside the support of $v$ and $b$ counts zeros inside it, then $0\leq a\leq n-r$, $0\leq b\leq r$, and

$$ q(x)=\frac{a+b}{1+\varepsilon(r+a-b)}. $$

These $L$ values are distinct. Equality between two values forces equality of the rational constant and irrational coefficients after cross multiplication. Thus their numerators $a+b$ are equal. Unless both are zero, their values $r+a-b$ are also equal, forcing the same pair $(a,b)$. The zero numerator occurs only at $v$.

Choose $L$ distinct parameters $\beta_h\in(0,\varepsilon)$, and let $D_h=B+\beta_hC$. Every slope of $D_h$ is either $\varepsilon+\beta_h$ or $\varepsilon-\beta_h$, so all are strictly positive. The denominators are positive on the cube because $B\gt0$ and $C\geq0$.

Let $\mathcal Q$ be the set of the $L$ values of $q$, and define

$$ P(z)=\prod_{q\in\mathcal Q\setminus\lbrace0\rbrace}\left(1-\frac zq\right),\qquad Q(z)=\prod_{h=1}^L(1+\beta_hz). $$

The rational function $P/Q$ is one at zero and zero at every other value in $\mathcal Q$. Since its numerator degree is at most $L-1$ and its denominator has distinct linear factors, elementary partial fractions supply real $w_h$ such that

$$ \frac{P(z)}{Q(z)}=\sum_{h=1}^L\frac{w_h}{1+\beta_hz}. $$

Substituting $z=q(x)$ gives the exact original-model table identity

$$ \mathbf 1_{\lbrace v\rbrace}(x)=\sum_{h=1}^L\frac{w_hB(x)}{D_h(x)}. $$

The numerators are affine and the denominators nonconstant with strictly positive slopes. The bound on $L$ follows from $(r+1)+(n-r+1)=n+2$. $\blacksquare$

For this prescribed denominator configuration, any vector in the dual equations is orthogonal to the displayed indicator table. Therefore $\lambda_vF(v)=0$, hence $\lambda_v=0$, for every target $F$. Strict positivity of every dual weight is impossible.

This failure is nonvacuous whenever $(n+1)L\lt2^n$, in particular for all sufficiently large $n$. The numerator space then has dimension below $2^n$, so choose a nonzero vector $w$ orthogonal to it. Take $F(x)$ to be the sign of $w_x$ wherever $w_x\neq0$, and choose either sign at its zero coordinates. Then $\lambda_x=|w_x|$ is a nonzero nonnegative dual certificate. Every such certificate still vanishes at $v$, so none can be strictly positive everywhere.

This does not contradict Gordan's nonnegative alternative and does not imply a head lower bound: the conclusion concerns an exact score table in a fixed numerator space, not the complexity of its sign labels.

## Verification boundary

The derivative identities, strict Gordan reformulation, and Hessian calculation are written proofs. The Hessians and their eigenvalues follow from the exact finite sums and elementary integrals shown explicitly. No Lean verification is claimed. No change to the original target statement or its admissible representations is made.
