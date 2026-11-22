# Homogeneous Geometric Products Admit Every Boolean Tangent

## Statement

Let $n\geq1$, put $N=2^n$, and identify Boolean inputs with subsets of $V=\lbrace1,\ldots,n\rbrace$. There are $N$ fixed homogeneous linear forms $L_T$ in $n+1$ variables, indexed by $T\subseteq V$, all with strictly positive coefficients, and positive real weights $w_T$ summing to one, with the following property.

For every $f:2^V\to[-1,1]$ there are real numbers $d_T(f)$ summing to zero such that

$$ Q_{\epsilon,f}(z)=e^{\epsilon f(\varnothing)}\prod_{T\subseteq V}L_T(z)^{w_T+\epsilon d_T(f)} $$

has positive exponents throughout $|\epsilon|\leq1/(128N^3)$ and satisfies

$$ Q_{\epsilon,f}(1,\mathbf1_S)=(1+|S|)e^{\epsilon f(S)}\qquad(S\subseteq V). $$

Every $Q_{\epsilon,f}$ is positive, real analytic, and homogeneous of degree one on the positive orthant. For every $\alpha\gt0$, every mixed derivative of $Q_{\epsilon,f}^{-\alpha}$ has the strict sign prescribed by complete monotonicity. The baseline $Q_{0,f}$ does not depend on $f$ and agrees with the single linear form $z_0+\sum_i z_i$ at every Boolean evaluation point.

The factors, weights, and perturbations are given explicitly below by one invertible finite matrix. The weights need not be integers. These geometric products are generally not polynomials, and this theorem gives no attention-head representation or asymptotic head lower bound.

## Coverage coordinates

Index a square matrix $C$ by nonempty subsets of $V$ and set

$$ C_{S,T}=\mathbf1_{\lbrace S\cap T\neq\varnothing\rbrace}. $$

For any table $g$ with $g(\varnothing)=0$, its unique coverage coefficients are

$$ c_T=-\sum_{U\subseteq T}(-1)^{|T|-|U|}g(V\setminus U),\qquad g(S)=\sum_{T\neq\varnothing}c_TC_{S,T}. $$

Indeed, if $h(U)=g(V)-g(V\setminus U)$, the second identity is equivalent to $h(U)=\sum_{T\subseteq U}c_T$, with $c_\varnothing=0$. Subset Möbius inversion proves both statements. Each row of $C^{-1}$ has at most $2^{|T|}$ entries of absolute value one, so its induced maximum-row-sum norm satisfies

$$ \|C^{-1}\|_\infty\leq N. $$

Take $g(S)=\log(1+|S|)$. Its coefficients depend only on $t=|T|$ and have the positive integral representation

$$ c_T=\int_0^1\frac{v^{n-t}(1-v)^t}{-\log v}dv. $$

To verify the formula, start from $\log(1+k)=\int_0^1(1-v^k)/(-\log v)dv$, substitute it into the finite inversion formula, and expand $(1-v)^t$. The starting identity follows by integrating $v^s$ first in $v\in(0,1)$ and then in $s\in[0,k]$. All integrands in that identity are nonnegative, so the order exchange is valid.

On $[1/4,1/2]$, the integrand is at least $4^{-n}/2$, because $v^{n-t}\geq4^{-(n-t)}$, $(1-v)^t\geq2^{-t}$, and $-\log v\leq\log4\lt2$. Therefore

$$ c_T\geq\mu:=\frac1{8N^2},\qquad \sum_{T\neq\varnothing}c_T=\log(n+1)\leq n,\qquad \|c\|_\infty\leq n. $$

## Explicit positive affine factors

Set

$$ a=128n(n+1)N^4,\qquad M=e^a,\qquad \delta=\frac1{128nN^3},\qquad L_T(z)=z_0+M\sum_{i\in T}z_i+\delta\sum_{i\notin T}z_i. $$

In particular, $L_\varnothing(z)=z_0+\delta\sum_i z_i$. For nonempty $S,T$, define

$$ v_0(S)=\log(1+\delta|S|),\qquad B_{S,T}=\frac{\log L_T(1,\mathbf1_S)-v_0(S)}a. $$

If $S\cap T=\varnothing$, then $B_{S,T}=C_{S,T}=0$. Otherwise put $k=|S\cap T|\geq1$ and $\ell=|S\setminus T|$. The exact entry formula is

$$ a(B_{S,T}-1)=\log\left(k+e^{-a}(1+\delta\ell)\right)-\log(1+\delta|S|). $$

Both logarithms are nonnegative. Their arguments are at most $n+1$ and $1+\delta n$, respectively, since $a\gt1$, $e\gt2$, and $\delta n\lt1$. Thus

$$ |B_{S,T}-C_{S,T}|\leq\frac{n+1}a,\qquad \rho:=\|C^{-1}(B-C)\|_\infty\leq\frac{N^2(n+1)}a=\frac1{128nN^2}\lt\frac12. $$

The Neumann series proves that $B$ is invertible and

$$ \|B^{-1}\|_\infty\leq\frac{N}{1-\rho}\leq2N. $$

Define $z=B^{-1}(g-v_0)$. From $Cc=g$,

$$ z-c=(I+C^{-1}(B-C))^{-1}\left(-C^{-1}v_0-C^{-1}(B-C)c\right). $$

Here $\|v_0\|_\infty\leq n\delta$, $Nn\delta=\mu/16$, and $\rho n\leq\mu/16$. Consequently

$$ \|z-c\|_\infty\leq\frac{\mu/8}{1-\rho}\leq\frac\mu4,\qquad z_T\geq\frac{3\mu}4,\qquad z_T\leq n+\frac\mu4. $$

Set $w_T=z_T/a$ for $T\neq\varnothing$, and set $w_\varnothing=1-\sum_{T\neq\varnothing}w_T$. Then all weights are positive. In fact

$$ \sum_{T\neq\varnothing}w_T\leq\frac{N(n+1)}a=\frac1{128nN^3}\lt\frac12. $$

The equation $Bz=g-v_0$ proves $\sum_Tw_T\log L_T(1,\mathbf1_S)=g(S)$. At $S=\varnothing$ every factor is one, so the same identity holds there.

## Every tangent with a uniform interval

For the specified $f$, let $r(S)=f(S)-f(\varnothing)$ on nonempty subsets and let $h=B^{-1}r$. Then $\|r\| _\infty\leq2$ and $\|h\| _\infty\leq4N$. Define

$$ d_T(f)=h_T/a\quad(T\neq\varnothing),\qquad d_\varnothing(f)=-\sum_{T\neq\varnothing}d_T(f). $$

If $|\epsilon|\leq1/(128N^3)=\mu/(16N)$, then $|\epsilon h_T|\leq\mu/4$. Hence $z_T+\epsilon h_T\geq\mu/2$ for every nonempty $T$, while

$$ \sum_{T\neq\varnothing}(w_T+\epsilon d_T(f))\leq\frac{N(n+\mu/2)}a\lt\frac12. $$

The empty-set exponent is therefore also positive, and the exponents still sum to one. Taking logarithms in the definition of $Q_{\epsilon,f}$ and using $Bh=r$ proves the stated Boolean evaluation formula exactly.

## Every negative power is completely monotone

Let $L(z)=\sum_{i=0}^n\ell_i z_i$ with every $\ell_i\gt0$, and let $\beta\gt0$. For a nonnegative integer multi-index $\gamma$ of total order $k$, direct differentiation gives

$$ (-1)^k\partial^\gamma L(z)^{-\beta}=(\beta)_k\left(\prod_i\ell_i^{\gamma_i}\right)L(z)^{-\beta-k}\gt0, $$

where $(\beta) _0=1$ and $(\beta) _k=\beta(\beta+1)\cdots(\beta+k-1)$ for $k\geq1$. Apply this with $\beta=\alpha(w_T+\epsilon d_T(f))$. The multivariate product rule expresses every signed derivative of the finite product $Q _{\epsilon,f}^{-\alpha}$ as a sum of positive terms, multiplied by the positive constant $e^{-\alpha\epsilon f(\varnothing)}$. This proves strict complete monotonicity. Homogeneity follows from the sum of exponents being one. $\blacksquare$

## Polynomiality is the missing restriction

For $n\geq2$, take $f(\varnothing)=f(\lbrace1\rbrace)=f(\lbrace2\rbrace)=-1$ and $f(\lbrace1,2\rbrace)=1$. For every nonzero permitted $\epsilon$, the four values violate the affine identity by

$$ Q_{\epsilon,f}(1,e_1+e_2)+Q_{\epsilon,f}(1,0)-Q_{\epsilon,f}(1,e_1)-Q_{\epsilon,f}(1,e_2)=3(e^\epsilon-e^{-\epsilon})\neq0. $$

A homogeneous degree-one polynomial is linear. Therefore this $Q_{\epsilon,f}$ is not a polynomial. The construction cannot be substituted for the manuscript's denominator product, which has integer degree and finitely many linear factors counted with integer multiplicity.

[Scott and Sokal, Lemma 2.4 and Section 2](https://people.maths.ox.ac.uk/scott/Papers/compmono.pdf) develop the relation between logarithmic derivatives and completely monotone powers. [Wei, Corollary 7.5 in version 2](https://arxiv.org/html/2609.31592v2) studies accumulation of admissible exponents at zero for homogeneous hyperbolic polynomials. That factorization criterion is a statement about polynomials. The theorem above is proved independently and shows explicitly why a relaxation to homogeneous analytic functions with completely monotone negative powers loses the needed restriction. No unproved result from that preprint is used here.

The asymptotic sign count for integer products and their admissible tangent scores remains a theorem-strength gap. This construction blocks the stated analytic relaxation, not the selected head-complexity conjecture.

## Verification scope

`CoverageCoordinates.coverage_kernel` and `CoverageCoordinates.complemented_coverage_kernel` check the alternating subset identities in Lean. `CoverageCoordinates.scale_identities` checks three scale calculations. The analytic matrix perturbation, complete monotonicity, and full construction above are written proofs, not Lean declarations.

The independent exact verifier checks both coverage inverse products through dimension eight, rational bounds for all coefficient sizes through dimension twenty, and all numerical budgets through dimension eight. These finite checks audit the formulas; the displayed argument proves the theorem in every dimension.
