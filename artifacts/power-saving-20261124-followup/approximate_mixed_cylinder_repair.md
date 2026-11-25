# The dense cylinder obstruction admits economical approximate repair

## Statement and status

The preceding exact mixed-cylinder obstruction does not persist automatically under uniform-distribution error. In fact, its own constructed family has a low-cost approximate cylinder score with quantitative original-head margin.

Let $g$ be any sign table on $d$ address bits with an exact negative-face affine expansion using $J$ blocks and total full-cube affine norm at most $3^d$. Put $n=d+m$ and $f(a,z)=g(a)(-1)^{|z|}$. For sufficiently large $m$, there is a table $\widehat f$ agreeing with $f$ on at least $63/64$ of the full cube and admitting an affine mixed-cylinder score of weighted cost

$$ K\leq J(r+1)\sum_{j=0}^r\binom mj,\qquad r\leq8\sqrt m. $$

The score compiles into $K$ original admissible heads with full-cube relative margin at least

$$ \gamma\geq\frac1{2\cdot3^d(4m+1)^r\widetilde C_r+1},\qquad \widetilde C_r=(r+1)(2r+2)^{2r+1}. $$

For the dense family in `mixed_cylinder_dense_obstruction.md`, $m=O(\log n)$ and its exhibited original width is $H=(m+1)J$. Therefore

$$ K\leq H\exp(O(\sqrt{\log n}\log\log n))=Hn^{o(1)},\qquad \gamma\geq\exp(-O(n)). $$

This is a written proof. The final quantitative compilation is exactly the scope of the kernel-checked `HeadComplexity.LinearCylinderMargin.hasRelativeMargin_of_cylinder_affine_sum`. It is a positive result for the displayed family, not a repair theorem for every original-width truth table.

## A polynomial with the right signs on typical Hamming weights

Assume $m\geq64$. Set

$$ a=\left\lceil\frac m2-4\sqrt m\right\rceil,\qquad b=\left\lfloor\frac m2+4\sqrt m\right\rfloor,\qquad r=b-a. $$

Both endpoints lie in $[0,m]$, and $r\leq8\sqrt m$. Define

$$ P(t)=(-1)^b\prod_{j=a}^{b-1}(2t-2j-1). $$

For every integer $t$, each factor is a nonzero odd integer. Hence $|P(t)|\geq1$ everywhere on the integer Hamming levels. For $a\leq t\leq b$, exactly $b-t$ factors are negative, so $\mathrm{sgn}P(t)=(-1)^t$.

Under a uniform Boolean input, $T=|z|$ has mean $m/2$ and variance $m/4$. Chebyshev's inequality gives

$$ \Pr\left(\left|T-\frac m2\right|\gt4\sqrt m\right)\leq\frac1{64}. $$

Thus $\widehat f(a,z)=\mathrm{sgn}(g(a)P(|z|))$ agrees with $f$ on at least $63/64$ of all pairs, independently of the address table. The full score $g(a)P(|z|)$ has signed gap at least one at every vertex with respect to $\widehat f$, including every disagreement vertex. This last fact is necessary for applying the full-cube relative-margin compiler.

## Coefficient mass and cylinder cost

Substitute $t=\sum_i z_i$ and reduce with $z_i^2=z_i$. The resulting multilinear expansion has degree at most $r$, so it uses at most $D=\sum_{j=0}^r\binom mj$ monomials. Before reduction, every affine factor has coefficient mass at most $4m+1$. Multiplication multiplies the mass upper bounds, and collecting equal Boolean monomials cannot increase the coefficient mass. Hence

$$ P(|z|)=\sum_{T\subseteq[m],\ |T|\leq r}c_T\prod_{i\in T}z_i,\qquad \sum_T|c_T|\leq(4m+1)^r. $$

Multiply this expansion by each negative-face affine address block. The result is a mixed cylinder with negative literals only on address coordinates and at most $r$ positive payload literals, times the original affine address numerator scaled by $c_T$. Each such block therefore has linear head budget at most $r+1$ and amplitude multiplier at most $\widetilde C_r$.

Summing the full-cube affine norms gives at most $3^d(4m+1)^r$. The quantitative compiler applies to the complete unit-gap score and permits all signed cancellation. It proves the stated head and margin bounds. For $m=O(\log n)$,

$$ \log D\leq O(\sqrt m\log(m+1)),\qquad r\log(4m+1)+\log\widetilde C_r=o(n), $$

which gives the asymptotic bounds. For bounded $m$, use the exact finite parity expansion instead; the asymptotic statement concerns $m\to\infty$.

## Consequence for the search

The exact mixed-cylinder lower bound and this approximate construction concern the same truth tables. They are consistent because face alternating sums are sensitive to wrong-label score magnitudes. The exact obstruction rules out polylogarithmic overhead for preserving every label through this comparison class, while a subpolynomial overhead suffices for constant-error approximation of this family with moderate margin.

A general approximate cylinder repair from an arbitrary original $H$-head representation remains open. The construction uses the known address-times-parity form and an exact controlled-mass address expansion. No such form, or economical replacement with the same useful properties, has been obtained for unrestricted scores with arbitrary target-dependent denominators and signed cancellation.
