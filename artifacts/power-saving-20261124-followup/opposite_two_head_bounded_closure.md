# Opposite two-head bounded-amplitude closure excludes mixed points

## Statement and scope

Let $v$ be a Boolean vertex with at least two one-coordinates and at least two zero-coordinates. Its scalar point indicator is not a uniform limit of scores consisting of one positive-orientation head, one negative-orientation head, and a bias, when the two individual full-cube head norms remain bounded.

The bias then also remains bounded, because the scores converge uniformly. The theorem permits arbitrary affine numerators, all boundary rates of positive denominators, and arbitrary signed cancellation between the two heads and the bias. It is a written compactness proof, not a kernel-checked declaration.

This is an obstruction for the specified opposite-orientation pair. It does not rule out constant-factor overhead or even two heads with the same orientation: the point $1100$ has the bounded-amplitude two-positive-head approximation in `unrestricted_capacity_mixed_point.md`. No impossibility is asserted when the two individual norms are allowed to diverge.

## Three elementary limit facts

### Fact 1. Compact denominator normalization

For a sequence of positive-orientation affine ratios $A_\nu/B_\nu$ with bounded full-cube norms, normalize $B_\nu(\mathbf1)=1$. After taking a subsequence, all denominator and numerator coefficients converge. Write the limits as $B,A$ and the pointwise ratio limit as $u$. Then $B$ is nonnegative, nonzero, and increasing in every coordinate; moreover

$$ A(x)=u(x)B(x) $$

at every cube vertex, including the zero set of $B$. Bounded ratio norms give bounded numerator values, hence bounded affine coefficients. The analogous normalization for a negative-orientation head is at $\mathbf0$.

If $B(v)=0$, its positive coefficients can occur only in zero-coordinates of $v$. Thus for a nonempty set $J$ of those coordinates,

$$ B(x)=\sum_{j\in J}b_jx_j,\qquad b_j\gt0. $$

The affine $A$ vanishes on the entire face $x_J=0$, so $A(x)=\sum_{j\in J}a_jx_j$. The negative-orientation statement uses $1-x_i$ on one-coordinates of $v$.

All these assertions also apply after restricting to a coordinate face or subtracting a constant from the ratio. We work in the enlarged coherent affine-ratio class, so such operations preserve the hypotheses needed for this proof.

### Fact 2. An endpoint cannot be the sole changed value

A uniform limit $u$ of positive-orientation heads cannot equal a constant $a$ at every vertex of an $r$-cube except its all-one vertex, with a different value there, if $r\geq2$. Normalize its denominators at the all-one vertex. After subtracting $a$, the limiting affine numerator would equal a nonzero point indicator, since the limiting denominator is one at that vertex. This is impossible: the alternating cube sum annihilates affine functions in dimension at least two, but not a nonzero point indicator.

The negative-orientation counterpart concerns the all-zero vertex. No common bound on the approximating parameters is needed, only convergence of the ratio values.

### Fact 3. Vanishing on a half cube leaves a reciprocal profile

Suppose a bounded positive-head sequence converges to $h$, and $h$ vanishes identically on the half cube $x_k=0$. Write the denominator and numerator there as $B_\nu(z)$ and $A_\nu(z)$, with coordinate slopes $b_{\nu,k}\gt0$ and $a_{\nu,k}$. The exact identity

$$ \phi_\nu(z,1)=\frac{B_\nu(z)}{B_\nu(z)+b_{\nu,k}}\phi_\nu(z,0)+\frac{a_{\nu,k}}{B_\nu(z)+b_{\nu,k}} $$

shows that $h(z,1)$ is a limit of constant-numerator positive reciprocal heads. The first term tends uniformly to zero because its prefactor lies in $[0,1]$.

After a further subsequence, the constant numerators have a common sign. Consequently $h(z,1)$ is either nonnegative and decreasing in every remaining coordinate, or nonpositive and increasing in every remaining coordinate. The complementary negative-orientation assertion applies when the zero half cube is $x_k=1$.

## Limiting polynomial identity

Suppose, for contradiction, that the two heads converge to $u,w$, the biases converge to $b$, and

$$ b+u+w=\mathbf1_v. $$

Use Fact 1 to obtain nonzero limiting denominators $B,C$ and affine numerators $A,D$, with $B$ increasing and $C$ decreasing. Then on the entire cube,

$$ bBC+AC+DB=\mathbf1_vBC. $$

The left side has Boolean polynomial degree at most two. Since the cube dimension is at least four, its alternating sum vanishes, forcing $B(v)C(v)=0$. The displayed polynomial therefore vanishes at every vertex. There are two cases, up to exchanging orientations by a global complementation.

## Both limiting denominators vanish at the target

Let $J$ be the positive support of $B$, contained in the zero-coordinates of $v$, and $K$ the negative support of $C$, contained in the one-coordinates. Fact 1 gives

$$ B=\sum_{j\in J}b_jx_j,\qquad A=\sum_{j\in J}a_jx_j,\qquad C=\sum_{k\in K}c_k(1-x_k),\qquad D=\sum_{k\in K}d_k(1-x_k). $$

The coefficient of each $x_jx_k$ in the zero polynomial gives

$$ b+\frac{a_j}{b_j}+\frac{d_k}{c_k}=0. $$

Hence $A=aB$ and $D=dC$ for constants $a,d$ satisfying $b+a+d=0$. Let $F$ be $x_J=0$ and $G$ be $x_K=1$. Then $u=a$ outside $F$ and $w=d$ outside $G$.

If $|K|\geq2$, fix every coordinate outside $K$. On the resulting $K$-cube, $u$ equals $a$ away from the all-one vertex: outside $F$ this is already known, while inside $F$ it follows from $w=d$ and the target's support. Fact 2 forces $u=a$ at the remaining vertex too. Thus $u=a$ everywhere. The equation for the score now makes $w-d$ a point indicator, contradicting the negative endpoint statement on the target's at least two zero-coordinates. The case $|J|\geq2$ is symmetric.

It remains that $J=\lbrace j\rbrace$ and $K=\lbrace k\rbrace$. On $F$, the function $u-a$ vanishes when $x_k=0$. On $G$, the function $w-d$ vanishes when $x_j=1$. Fact 3 therefore makes their restrictions to $F\cap G$ signed reciprocal limits of opposite orientations. Their sum is the point indicator of the remaining coordinates, whose target still has at least one one and one zero.

Such a sum is impossible. If its two terms have opposite signs, their monotonicities agree, so the sum is either increasing or decreasing in every coordinate. A mixed-point indicator has neither property. If both terms are nonpositive, their sum cannot equal one at the target. If both are nonnegative, the decreasing term vanishes at the all-zero vertex and hence everywhere above it, while the increasing term vanishes at the all-one vertex and hence everywhere below it. Both terms must therefore vanish at the target. This proves the contradiction in the first case.

## Only one limiting denominator vanishes at the target

Assume $B(v)=0$ and $C(v)\gt0$. Write $B=\sum_{j\in J}b_jx_j$ and $A=\sum_{j\in J}a_jx_j$ as above, and set $E=D+bC$. The zero identity becomes

$$ AC+EB=0. $$

If $C$ has no nonzero coefficient outside $J$, the coefficients involving one outside variable show that $E$ also depends only on $J$. On $F$, both $C$ and $E$ are constant, with $C\gt0$. Thus $u$ differs from a constant only at the target on $F$, contradicting Fact 2 on the target's at least two one-coordinates.

Suppose instead that $C$ has a nonzero coefficient outside $J$. The mixed coefficients in $AC+EB=0$ imply that all $a_j/b_j$ have a common value $a$, so $A=aB$. The affine function $T=E+aC$ vanishes wherever at least one coordinate of $J$ equals one.

If $|J|\geq2$, this forces $T=0$ identically. Indeed its vanishing on two coordinate-one faces kills all slopes and the constant coefficient. On the subcube obtained by varying only the target's one-coordinates, $C$ remains positive, because it is decreasing and positive at its all-one vertex $v$. There $u-a$ would be the all-one point indicator, again contradicting Fact 2.

The only remaining possibility is $J=\lbrace j\rbrace$, in which case

$$ T=\lambda(1-x_j). $$

If $\lambda=0$, the preceding all-one-subcube argument still applies. Assume $\lambda\neq0$. On $F$, the boundedness relation forces $C\gt0$ everywhere: at a zero of $C$, the limiting $D$ and hence $T$ would also vanish, contrary to $T=\lambda$. Let $h=u-a$ on $F$. The exact restricted equation is

$$ h+\frac\lambda C=\mathbf1_{v|F}. $$

The face $F$ has dimension at least three. Normalize the restricted positive-head sequence converging to $h$ once more, obtaining affine limits $A',B'$ as in Fact 1. Clearing the last equation gives

$$ A'C+\lambda B'=\mathbf1_{v|F}B'C. $$

Its alternating sum forces $B'(v)=0$, since $C(v)\gt0$ and the left side has degree at most two. Let the nonempty positive support of $B'$ be $J'$, contained in the remaining zero-coordinates. Fact 1 makes $A'$ supported on $J'$ too.

If $C$ has any nonzero coefficient outside $J'$, the mixed coefficients of the now-zero polynomial $A'C+\lambda B'$ force every coefficient of $A'$ to vanish. Then $\lambda B'=0$, impossible. Hence $C$ depends only on $J'$. On the face $x_{J'}=0$, it is a positive constant. The restricted $h$ again differs from a constant only at the target, and varying its at least two one-coordinates contradicts Fact 2.

This exhausts both denominator cases and proves the theorem.

## Consequence for the remaining compiler question

For every fixed amplitude bound, opposite two-head approximations stay a positive uniform distance from a mixed-point gate with at least two literals of each sign. The proof is qualitative and gives no explicit distance as a function of that bound.

The theorem isolates why the four-bit numerical experiments favor two same-orientation poles rather than an opposite pair. It does not count unrestricted truth tables, forbid a repair with new heads, or rule out polynomial or constant-factor head overhead. In particular, the already proved scalar-cylinder compiler supplies the needed same-orientation repair for $1100$.

## Sharp six-bit bounded-closure consequence

For the six-bit point $111000$, bounded-amplitude uniform approximation requires at least three heads, allowing every denominator orientation. Two equal-orientation heads are excluded by the inherited monotone-pole localization theorem, since each orientation has three opposing literals. An opposite pair is excluded by the theorem above. Constant-denominator heads may be assigned either weak orientation for this enlarged-class argument. The scalar mixed-cylinder compiler provides a three-head approximation with amplitude bounded independently of tolerance. Thus three is the exact minimum in bounded-amplitude approximation closure for this scalar gate.

This rules out a two-output-head bounded-amplitude value compiler for the product of two opposite anchored-face gates. It does not rule out a universal constant overhead greater than one, and it does not concern the head complexity of the gate's truth table.

## Independent audit and checked ingredients

Two other agents independently audited the complete written argument, including the Boolean quadratic coefficient comparisons, the singleton-face reciprocal limit, the second denominator normalization, and the endpoint restrictions. Both audits passed. The full compactness and case-classification theorem remains a written proof.

The companion module `formalization/HeadComplexity/Research/ReciprocalHalfFaceGeometry.lean` kernel checks three quantitative ingredients in namespace `HeadComplexity.ReciprocalHalfFaceGeometry`: `halfFace_reciprocal_error_le`, `middle_abs_le_endpoints`, and `not_isolated_middle_spike`. The first bounds the error in the half-face reciprocal identity by the vanishing-half error. The second proves that the absolute middle value of opposite signed reciprocal profiles is at most the sum of the absolute endpoint values, and the third excludes an isolated middle spike. These declarations do not package the full compactness theorem or assert an unrestricted head-count lower bound.

The module build completed successfully with 3137 jobs. Each of the three exported theorems has exactly `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms; see `reciprocal-half-face-build.txt` and `reciprocal-half-face-axioms.txt`.
