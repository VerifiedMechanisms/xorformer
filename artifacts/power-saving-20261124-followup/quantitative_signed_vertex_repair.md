# Quantitative signed-statistic vertex repair

## Scope and provenance

Every individual Boolean vertex indicator has an admissible approximation using $n+1$ heads whose total full-cube amplitude is explicitly bounded. This is a written proof. It is a quantitative specialization of the signed-statistic polynomial bank in commit `c7469597` on `origin/ar/027ac8030b43`, file `Results/JointFamilySignedJets.lean`. That branch checks the limiting construction and full-cube admissibility, but does not state the amplitude estimate below. No declaration from that branch is imported here.

This does not prove a width-sensitive repair for an arbitrary score. The number of exceptional vertices and the size of the score being corrected must still be controlled. The calculation includes all outside errors, divergent residues, and the norm of each individual head.

## A bounded indicator bank

Let $n\geq1$, let $v\in\lbrace0,1\rbrace^n$, and fix $0\lt\varepsilon\leq1$. Define

$$ V(x)=d_H(x,v),\qquad U(x)=(n+1)\sum_i x_i,\qquad p_h(x)=U(x)+hV(x)\quad(0\leq h\leq n). $$

The slope of $p_h$ in coordinate $i$ is $n+1+h(1-2v_i)$, which lies between $1$ and $2n+1$. Its constant coefficient is $h|v|$. On the full cube,

$$ 0\leq p_h(x)\leq P_0:=3n^2. $$

Let $\lambda_{rh}$ be the coefficient of $z^r$ in the Lagrange basis polynomial of node $h$ among $0,\ldots,n$. Then

$$ \sum_{h=0}^n\lambda_{rh}(U+hV)^\ell=0\quad(\ell\lt r),\qquad \sum_{h=0}^n\lambda_{rh}(U+hV)^r=V^r. $$

Write

$$ P(z)=\prod_{k=1}^n\left(1-\frac z k\right)=\sum_{r=0}^n c_rz^r,\qquad A=(n+1)^3 2^n. $$

The polynomial $P(V(x))$ is exactly the indicator of $v$. The coefficient bounds needed below are

$$ \sum_r|c_r|=n+1,\qquad \sum_{r,h}|\lambda_{rh}|\leq(n+1)^2 2^n,\qquad \sum_{r,h}|c_r\lambda_{rh}|\leq A. $$

For the middle inequality, the sum of absolute coefficients of the numerator of the Lagrange polynomial at $h$ is at most $\prod_{k\neq h}(1+k)$. Its denominator has absolute value $h!(n-h)!$. Thus its coefficient norm is at most $(n+1)\binom nh/(h+1)\leq(n+1)2^n$. Summing over $h$ gives the stated loose bound.

Choose

$$ T=\frac{4AP_0^{n+1}}{\varepsilon},\qquad a_h=\sum_{r=0}^n c_rT^{r+1}\lambda_{rh},\qquad \phi_h(x)=\frac{a_h}{T-p_h(x)}. $$

Every denominator is strictly positive throughout the full cube and has strictly negative coordinate slopes. In particular each $\phi_h$ is a genuine original head by `FracAtom.ofNegativeAffineRatio`; arbitrary signs of $a_h$ are allowed. Here $T\geq2P_0$ and $T\geq1$.

The finite geometric identity, followed by cancellation of the lower moments, gives

$$ T^{r+1}\sum_h\frac{\lambda_{rh}}{T-p_h}=\sum_h\lambda_{rh}p_h^r\frac{T}{T-p_h}. $$

Subtract the top moment $V^r$. The absolute difference is at most $2P_0^{r+1}\sum_h|\lambda_{rh}|/T$. Therefore the bank score $F_v=\sum_h\phi_h$ satisfies

$$ \sup_x|F_v(x)-\mathbf1_{x=v}|\leq\frac{2AP_0^{n+1}}T=\frac\varepsilon2\leq\varepsilon. $$

Moreover the sum of the full-cube norms of the individual heads obeys

$$ \sum_h\|\phi_h\|_\infty\leq\frac2T\sum_h|a_h|\leq2AT^n. $$

This last estimate explicitly charges cancellation inside the bank. It is not a bound only on the total score. Since

$$ \log(2AT^n)=O\left(n^2\log(n+1)+n\log(1/\varepsilon)\right), $$

the construction has a quantitative, singly exponential-in-polynomial amplitude bound at inverse-exponential error tolerances.

## Repairing finitely many bounded errors

Suppose a genuine original score $S$ has amplitude at most $B$, and let $E$ be a set of $m\geq1$ vertices. Suppose coefficients $d_v$, with $|d_v|\leq R$ and $R\geq1$, have been chosen so that

$$ f(x)\left(S(x)+\sum_{v\in E}d_v\mathbf1_{x=v}\right)\geq1\qquad\text{for every }x. $$

Use the preceding bank at tolerance $\varepsilon=1/(4mR)$ for every $v$. Scaling a numerator by $d_v$ preserves admissibility. The resulting score uses $H+(n+1)m$ heads, has signed gap at least $3/4$, and has relative margin at least

$$ \frac{3}{4(B+2mRA T^n)},\qquad T=16mRA P_0^{n+1}. $$

The accumulated error on every vertex is at most $mR\varepsilon=1/4$. Its amplitude is at most $B+2mRA T^n$. These are full-cube estimates, including vertices outside $E$.

If $\log(B+R)\leq\mathrm{poly}(n)$ and $m\leq2^n$, the repaired margin is at least $\exp(-\mathrm{poly}(n))$. A bound $m\leq H/\sqrt n$ would give $O(\sqrt n H)$ overhead, which fits the stronger-margin tradeoff already formalized in `SublinearOverheadRepairTradeoff.lean`.

## The remaining first lemma

The required access statement is still absent. One needs a score of controlled amplitude, with at least a unit gap except on at most $H/\sqrt n$ vertices, and bounded corrections on those vertices, for every width $H$ truth table at the critical widths. Rescaling an arbitrary original score can make its already-correct gap one only at the cost of an uncontrolled amplitude and uncontrolled correction coefficients. A linear programming active-row certificate can have order $nH$ rows, which exceeds this budget by a factor of order $n^{3/2}$.

The approximation variant of the margin count permits a constant fraction of incorrect labels, but it still needs a quantitative margin on the remaining rows. The shared bank does not establish that premise. Thus this checkpoint isolates a useful repair primitive and the exact sparsity-and-amplitude inequality still needed; it yields no new unrestricted lower bound by itself.
