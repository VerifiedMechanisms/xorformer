# Product Tangents and a Submodularity Obstruction

## Exact tangent identity

Let $X=\lbrace0,1\rbrace^n$. Suppose every affine function $B_h$ is positive on $X$, and let $A_h$ be arbitrary affine functions. Put

$$ S(x)=\sigma+\sum_{h=1}^H\frac{A_h(x)}{B_h(x)},\qquad D_t(x)=e^{\sigma t}\prod_{h=1}^H\bigl(B_h(x)+tA_h(x)\bigr). $$

For sufficiently small $|t|$, every factor is positive on the finite set $X$, and direct differentiation gives

$$ \left.\frac{d}{dt}\log D_t(x)\right|_{t=0}=S(x),\qquad D'_0(x)=\sigma\prod_hB_h(x)+\sum_h A_h(x)\prod_{g\neq h}B_g(x). $$

If a denominator has strictly coherent slopes, that coherence also persists for sufficiently small $|t|$. This identifies the cleared numerator as a tangent vector to a coordinatewise product of affine evaluation tables. The general tangent-space formula for Hadamard products appears in [Bocci, Carlini, and Kileel, Lemma 2.12](https://web.ma.utexas.edu/users/jkileel/HadamardPublished.pdf).

This identity is a reduction. It does not bound the number of orthants met by the resulting tangent vectors. No sufficient sign-counting theorem for this product variety has been established here.

## A precise failure of the submodular relaxation

Identify a cube vertex with a subset of $\lbrace1,\ldots,n\rbrace$. For $n\geq2$, define

$$ q(S)=\log(1+|S|),\qquad \delta_n=\log\left(\frac{n^2}{n^2-1}\right)\gt0. $$

**Claim.** For every function $f:2^{\lbrace1,\ldots,n\rbrace}\to\lbrace-1,1\rbrace$ and every real $t$ with $|t|\lt\delta_n/4$, the function $q_t=q+tf$ is submodular and is strictly submodular on every incomparable pair. Consequently, the positive log-submodular table

$$ D_t(S)=(1+|S|)e^{tf(S)} $$

has arbitrary prescribed logarithmic tangent $f$ at the single affine-factor table $D_0(S)=1+|S|$.

**Proof.** For incomparable $S,T$, let $a=1+|S\cap T|$, $p=|S\setminus T|$, and $r=|T\setminus S|$. Then $p,r\geq1$ and $a+p+r\leq n+1$. Therefore $a\leq n-1$ and $a(a+p+r)\leq n^2-1$. It follows that

$$ q(S)+q(T)-q(S\cup T)-q(S\cap T)=\log\left(1+\frac{pr}{a(a+p+r)}\right)\geq\delta_n. $$

The corresponding four-term expression in $f$ has absolute value at most four. Hence the four-term expression in $q_t$ is at least $\delta_n-4|t|\gt0$. For comparable $S,T$, it is identically zero for every set function. This proves the submodularity assertion. Taking the logarithmic derivative of the displayed formula for $D_t$ gives $f$. $\blacksquare$

The claim does not assert that $D_t$ factors into a bounded number of admissible affine functions when $t\neq0$. It proves that retaining positivity and log-submodularity while dropping the factorization constraint loses every restriction on tangent signs, even at a baseline having only one factor. Thus submodularity alone cannot supply the missing lower-bound invariant.
