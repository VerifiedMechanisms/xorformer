# An Exact Mean-Value Identity and a Parity Amplitude Obstruction

## Statement

Let $n\geq1$, and let $F=A/D$ on the Boolean cube, where $A,D$ are affine and $D$ is positive there. Then

$$ \left|\sum_{x\in\lbrace0,1\rbrace^n}(-1)^{|x|}F(x)\right|\leq2\max_x|F(x)|. $$

In particular, this applies to every exact attention atom in the manuscript, with either denominator orientation. The constant two is sharp as a supremum, even among admissible atoms with strictly positive denominator slopes.

For any number of heads, consider $S=c+\sum_h\phi_h$ and amplitude bounds $M_h\geq\max_x|\phi_h(x)|$. If the score represents parity with signed margin at least $\mu$, then

$$ 2^n\mu\leq2\sum_hM_h. $$

Consequently, if $M=|c|+\sum_hM_h\gt0$ and the signed margin is at least $\gamma M$, then

$$ \gamma\leq2^{1-n}. $$

This is an amplitude obstruction at every head count. It is not an asymptotic lower bound on the number of heads. Parity still has the manuscript's exact head complexity $n$.

## Reciprocal moments

Complement any coordinates whose denominator slopes are negative, and divide the numerator and denominator by the resulting positive constant term. These operations preserve the maximum table amplitude and the absolute alternating sum. It suffices to treat

$$ F(T)=\frac{a_0+\sum_{i\in T}a_i}{1+\sum_{i\in T}w_i},\qquad w_i\geq0,\qquad T\subseteq[n]. $$

For any set of coordinates $U$, define

$$ K_U=\sum_{T\subseteq U}\frac{(-1)^{|T|}}{1+\sum_{i\in T}w_i}=\int_0^1\prod_{i\in U}(1-t^{w_i}) dt. $$

The integral identity follows by expanding the finite product and integrating each power. When a weight is zero, its factor is zero, including at the endpoint under the convention $0^0=1$; the integral identity is unchanged.

The factors lie in $[0,1]$, so

$$ 0\leq K_U\leq1,\qquad K_U\leq K_{U\setminus\lbrace i\rbrace}. $$

Put $K=K_{[n]}$ and $d_i=K_{[n]\setminus\lbrace i\rbrace}-K$. Splitting the subset sums according to whether they contain $i$ gives

$$ L(F):=\sum_{T\subseteq[n]}(-1)^{|T|}F(T)=a_0K-\sum_i a_id_i. $$

Apply the same identity with numerator equal to denominator. The alternating sum of the constant function is zero because $n\geq1$, yielding

$$ \sum_iw_id_i=K,\qquad0\leq d_i\leq1-K. $$

Also $K\lt1$. Indeed, $K=1$ would force every $d_i=0$, contradicting the balance identity.

## The exact cube point

Define

$$ z_i=\frac{d_i}{1-K}. $$

Each $z_i$ belongs to $[0,1]$, and the balance identity gives

$$ 1+\sum_iw_iz_i=\frac1{1-K}. $$

Therefore, with the same affine ratio evaluated on the continuous cube,

$$ F(z)=(1-K)a_0+\sum_i a_id_i,\qquad L(F)=F(0)-F(z). $$

The point $z$ depends only on the denominator, not on the numerator. It can lie on the boundary, as it does in dimension one.

Let $B=\max_x|F(x)|$ over Boolean vertices. The affine functions $BD+A$ and $BD-A$ are nonnegative at every vertex, hence throughout the cube by convexity. Since $D$ stays positive there, $|F(z)|\leq B$. The identity proves $|L(F)|\leq2B$.

For coherent nonpositive slopes, simultaneous complementation suffices. The written argument permits arbitrary positive affine denominators by complementing only the coordinates with negative slopes. The formal atom theorem uses the manuscript's exact coherent class, without enlarging its definition.

## A finite inequality proof used in Lean

The kernel proof also establishes the stronger normalized assertion $|L(F)-a_0|\leq1$ directly from the vertex bounds $|A(T)|\leq D(T)$.

For the upper bound, set $q_i=\max(-a_i-w_i,0)$. Evaluating $A+D\geq0$ at the vertex containing exactly those coordinates with $a_i+w_i\lt0$ gives $\sum_iq_i\leq a_0+1$. Since $-a_i\leq w_i+q_i$,

$$ \begin{aligned} L(F)&\leq(a_0+1)K+\sum_iq_id_i\cr &\leq(a_0+1)K+(1-K)\sum_iq_i\cr &\leq a_0+1.\end{aligned} $$

Apply the same argument to $-A$ for the lower bound. This proof uses only the exact moment identities and their positivity bounds. The separate explicit cube-point identity is also formalized.

## Sharpness in the actual architecture

For $t\gt0$, put

$$ F_t(x)=1-\frac2{1+t\sum_i x_i}. $$

Its maximum absolute cube value is one. It is negative one at the origin and converges to one at every other vertex. Thus $L(F_t)\to-2$. An explicit error bound is

$$ |L(F_t)+2|\leq\frac{2(2^n-1)}{1+t}. $$

This is a literal `FracAtom`, with parameters

$$ \gamma=\frac12,\qquad\rho_i=\frac1{2n},\qquad\alpha=1+2nt,\qquad m_i=1,\qquad\delta=0,\qquad\eta=-\frac32. $$

Substitution gives denominator $1+t\sum_i x_i$ and numerator $-1+t\sum_i x_i$. Every required positive parameter is strictly positive. Sharpness is a written limiting argument with independent exact atom evaluations; it is not asserted as a separate Lean limit theorem.

## The obstruction for sums of heads

Write $\chi(x)=(-1)^{|x|}$. If $\chi(x)S(x)\geq\mu$ at all vertices, then

$$ 2^n\mu\leq\sum_x\chi(x)S(x)=\sum_h\sum_x\chi(x)\phi_h(x)\leq2\sum_hM_h. $$

The constant term vanishes in the alternating sum. Taking $\mu=\gamma M$ and using $\sum_hM_h\leq M$ proves the relative margin bound.

For every fixed $0\lt\beta\lt1$, the quantity $\exp(-n^\beta)$ eventually exceeds $2^{1-n}$. Hence no representation of parity, with any finite number of admissible heads, can achieve that relative amplitude margin for all sufficiently large dimensions. A universal repair to the margin required by the proposed intermediate-exponent covering argument is therefore false, even with unrestricted head overhead.

The [bounded-head covering theorem](luce-covering.md) remains valid for its explicitly restricted class. Its conditional universal-count deductions do not imply the original target; beyond the parity obstruction they are vacuous as claims of universality. This resolves the margin-transfer question for that approach and does not resolve the unrestricted worst-case head complexity.

## Formal audit

`formalization/HeadComplexity/Atoms/HeadParityAmplitude.lean` proves the integral representation, positivity and deletion bounds, the balance identity, the explicit cube point, and the alternating-sum estimate. Principal declarations are `moment_integral`, `moment_balance`, `meanPoint_bounds`, `alternatingRatio_mean_value`, and `positive_affine_ratio_bound`, all in the namespace `HeadComplexity.HeadParityAmplitude`.

`formalization/HeadComplexity/Atoms/HeadParityAmplitudeAtoms.lean` derives the affine coefficients of the actual atom, checks simultaneous complementation, and proves `atom_parity_amplitude_bound`, `parity_margin_sum_bound`, and `parity_relative_margin_bound`. The last theorem permits every natural head count and arbitrary real atom parameters satisfying the original positivity conditions.

The cube is enumerated by finite subsets of its coordinate indices; `subsetBits` is their Boolean indicator. The resulting parity character is exactly negative one to the subset cardinality. No discretization of model parameters, fixed denominator dictionary, or restriction on target dependence is used.
