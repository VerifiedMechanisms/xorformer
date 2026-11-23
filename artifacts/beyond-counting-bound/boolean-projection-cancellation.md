# Boolean Projection Identities and High Contact

## Scope

This note gives an exact classification of constant-residue reciprocal identities along an integer denominator deformation, and an independent construction of high contact with full affine span. Both mechanisms allow signed cancellation and positive denominator slopes. Neither is an unrestricted head-count lower bound. The classification has no bound on the number of switching terms needed, and it concerns an identity throughout a deformation rather than an arbitrary representation at one parameter value.

## A vanishing ideal for Boolean lines

Fix $n\geq1$. In $\mathbb R[u_1,\ldots,u_n]$, let

$$ I=\left\langle u_i u_j(u_i-u_j):1\leq i\lt j\leq n\right\rangle,\qquad V=\bigcup_{x\in\lbrace0,1\rbrace^n}\lbrace tx:t\in\mathbb R\rbrace. $$

**Theorem 1.** The ideal of all real polynomials vanishing on $V$ is exactly $I$. The degree $k$ homogeneous component of the quotient has dimension one for $k=0$, and for $k\geq1$ has dimension

$$ \sum_{s=1}^{\min(k,n)}\binom ns. $$

**Proof.** Each generator vanishes on every line in $V$: if both selected coordinates are nonzero, they are equal. For the converse, a degree $k$ monomial with nonempty support $S$ is congruent modulo $I$ to

$$ M_{S,k}=u_{\max S}^{k-|S|+1}\prod_{i\in S\setminus\lbrace\max S\rbrace}u_i. $$

Indeed, whenever $i\lt j=\max S$ and the exponent at $i$ is at least two, the relation $u_i^2u_j=u_iu_j^2$ transfers one exponent from $i$ to $j$. Both coordinates belong to the support, so every such step is multiplication of a generator by a monomial. The number of exponents away from the chosen coordinate strictly decreases. This terminates with the displayed monomial.

Let $Q$ vanish on $V$, and write it as a sum of homogeneous parts. For a fixed Boolean $x$, the polynomial $Q(tx)$ vanishes for every real $t$. Each of its coefficients is therefore zero. Thus every homogeneous part vanishes on $V$ separately. The degree-zero part is zero. Reduce a positive-degree part by the preceding transfers to

$$ R_k=\sum_{\substack{\varnothing\neq S\subseteq[n]\cr |S|\leq k}}c_{S,k}M_{S,k}. $$

It still vanishes on $V$. At the indicator vector of a nonempty set $T$ with $|T|\leq k$, its value is $\sum_{\varnothing\neq S\subseteq T}c_{S,k}$. Induction on $|T|$ shows that every coefficient is zero. Hence the original homogeneous part belongs to $I$, proving the ideal equality. The same triangular evaluation argument proves linear independence of the displayed residue classes; the transfer argument proves spanning. This gives the dimension formula. $\blacksquare$

## Exact reciprocal identities

Let $(c_v)$ be a finitely supported family of real numbers indexed by $v\in\mathbb N^n$, and form

$$ P(z)=\sum_v c_v z_1^{v_1}\cdots z_n^{v_n}. $$

Fix any strictly positive affine function $D(x)=1+b\cdot x$ with every $b_i\gt0$. For each Boolean input define

$$ R_x(\varepsilon)=\sum_v\frac{c_v}{D(x)+\varepsilon v\cdot x}. $$

**Theorem 2.** The following three statements are equivalent:

1. For every Boolean $x$, the rational function $R_x$ vanishes identically.

2. For every Boolean $x$ and every integer $m\geq0$, one has $\sum_{v:v\cdot x=m}c_v=0$.

3. The polynomial $P$ belongs to the ideal

$$ J=\left\langle(z_i-1)(z_j-1)(z_i-z_j):1\leq i\lt j\leq n\right\rangle. $$

**Proof.** Group the summands of $R_x$ by their projection $m=v\cdot x$. The terms with $m\gt0$ have distinct simple poles at $-D(x)/m$. If the rational function is zero, the residue at each pole gives a zero coefficient sum for that group. The remaining constant term gives the group with $m=0$. Conversely, zero coefficient sums make the rational function zero term by term. This proves the equivalence of the first two statements.

The second statement says precisely that $P(t^{x_1},\ldots,t^{x_n})$ is the zero polynomial in $t$. On putting $u=z-1$, this becomes vanishing of $Q(u)=P(1+u)$ at every point $u=(t-1)x$. Theorem 1 applies. Translation takes its generators to the displayed generators of $J$, proving the final equivalence. $\blacksquare$

It is enough in the first statement to assume vanishing on any nonempty open interval of nonnegative $\varepsilon$: a rational function zero on such an interval is identically zero. Throughout this interval every denominator has strictly positive constant and slopes. The reciprocal terms are therefore admissible affine-ratio heads. Absorbing each constant numerator into the free bias gives the manuscript's reduced normal form as well.

Expanding a generator gives the six-point switch

$$ (z_i-1)(z_j-1)(z_i-z_j)=z_i^2z_j-z_iz_j^2-z_i^2+z_j^2+z_i-z_j. $$

Since ideal membership uses polynomial coefficients, Theorem 2 says that every such finitely supported identity is a finite real linear combination of translates of these six-point switches. This is an exact generation theorem. It does not assert that the translated switches stay within the original support or that their number is controlled by the number of original heads.

## A cancellation invisible on the cube

For two coordinates write

$$ R=\frac1{D+\varepsilon(2x+y)}-\frac1{D+\varepsilon(x+2y)}-\frac1{D+2\varepsilon x}+\frac1{D+2\varepsilon y}+\frac1{D+\varepsilon x}-\frac1{D+\varepsilon y}. $$

The six-point switch proves $R=0$ at every Boolean pair, for every positive $D$ and every nonnegative $\varepsilon$. It need not be zero as a rational function of unrestricted inputs. Its zeroth, first, and second velocity moments vanish formally, while its third moment is

$$ (2x+y)^3-(x+2y)^3-(2x)^3+(2y)^3+x^3-y^3=6xy(x-y). $$

This is nonzero as a polynomial and zero on the Boolean cube. Thus even a family that cancels for an entire interval of denominator deformations need not give a formal rational identity in the input variables. All six velocity vectors are distinct.

## Full affine span permits arbitrarily high contact

**Theorem 3.** For integers $n,k\geq1$, there are $H=nk+2$ distinct vectors in $\mathbb R^n$ with full affine span, nonzero real residues, and positive coherent affine denominators, such that their reciprocal sum has zero Taylor coefficients through order $k$ at a common-denominator collision. Its coefficient of order $k+1$ is nonzero at a Boolean input.

**Proof.** Set $m=nk+1$ and use the moment-curve vectors and finite-difference weights

$$ v_h=(h,h^2,\ldots,h^n),\qquad c_h=(-1)^{m-h}\binom mh,\qquad 0\leq h\leq m. $$

For every integer $r\lt m$ the weighted power sum $\sum_h c_hh^r$ is zero; for every $r\geq m$ it is strictly positive. To prove both assertions, expand the elementary identity

$$ \sum_{h=0}^m(-1)^{m-h}\binom mh e^{ht}=(e^t-1)^m. $$

The right side has no terms below degree $m$. Every coefficient in degree at least $m$ is positive: it is a sum over compositions of that degree into $m$ positive parts, each contributing the reciprocal of a product of positive factorials. Comparing Taylor coefficients proves the assertions.

Fix $D(x)=1+\sum_i x_i$ and consider $R_x(\varepsilon)=\sum_h c_h/(D(x)+\varepsilon v_h\cdot x)$. Its Taylor coefficient in degree $j$ is

$$ \frac{(-1)^j}{D(x)^{j+1}}\sum_{h=0}^m c_h(v_h\cdot x)^j. $$

For $j\leq k$, the summand is a polynomial in $h$ of degree at most $nj\leq nk\lt m$, so the coefficient vanishes, even for arbitrary real $x$ for which $D(x)\neq0$. At the Boolean input $e_n$, the coefficient for $j=k+1$ is a nonzero scalar times $\sum_h c_hh^{n(k+1)}$, which is positive by the power-sum assertion. The vectors $v_0,\ldots,v_n$ are affinely independent: the matrix with rows $(1,h,\ldots,h^n)$ has nonzero Vandermonde determinant. All vectors are nonnegative and distinct, and every residue is nonzero. Finally $D(x)+\varepsilon v_h\cdot x$ has constant one and strictly positive slopes for $\varepsilon\geq0$. This proves every claim. $\blacksquare$

## Literature and the remaining gap

[Hajdu and Tijdeman's algebraic discrete tomography chapter, Theorem 1](https://pub.math.leidenuniv.nl/~tijdemanr/DiscTom.pdf), describes zero line-sum configurations using translated switching atoms. Its generating-polynomial method informs Theorems 1 and 2 above. The projections here collect sums on hyperplanes normal to Boolean vectors, so the chapter's line-sum theorem is not being imported unchanged in higher dimension. The displayed ideal and its normal-form proof are supplied directly.

Theorems 1 and 2 identify actual Boolean cancellation relations rather than replacing them by formal input identities. However, ideal generation alone gives no economical decomposition in the number of heads. Theorem 3 also prevents a repair that bounds contact order merely by the affine dimension of the velocity configuration. Neither argument controls arbitrary affine numerators, several collision scales, or the signs at one fixed target-dependent parameter value. Those are substantive missing steps. No estimate of the number of unrestricted classification chambers follows from these theorems, and neither requested asymptotic lower bound has been proved.

## Verification scope

The three general theorems above have written proofs. The companion Lean file checks the six-term Boolean identity, its first three formal moments, and the first nonzero formal moment. The general vanishing-ideal and moment-curve theorems are not claimed as Lean declarations. A separate exact-arithmetic program verifies the normal-form reductions and finite moment examples; those finite checks are computational evidence, not a substitute for the general proofs.
