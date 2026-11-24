# Two interior heads defeat denominator-preserving approximate repair

## Written finite statement

Let $n\geq2$ and $0\lt\varepsilon\lt1/2$. Put

$$ B(x)=1+\sum_{i=1}^n x_i,\qquad A(x)=1-2x_1,\qquad D(x)=1-2x_2,\qquad f(x)=A(x)D(x). $$

The two original admissible heads

$$ \phi_1(x)=\frac{A(x)}{B(x)},\qquad \phi_2(x)=\frac{-A(x)}{B(x)+\varepsilon D(x)} $$

strictly represent $f$, because their sum is $\varepsilon A D/[B(B+\varepsilon D)]$. Every denominator coefficient is strictly positive, including the second-coordinate slope $1-2\varepsilon$ of the perturbed denominator. The denominators are bounded between $1/2$ and $n+2$ throughout the cube. Thus no denominator approaches zero and no face concentration is involved.

Now allow any finite number of copies of these two denominators, arbitrary new affine numerators, and arbitrary bias. If the resulting strict score $S$ has a truth table agreeing with $f$ on more than three quarters of the cube, then its full-cube relative margin is at most $\varepsilon$.

**Proof.** Replace every term $L/(B+\varepsilon D)$ by $L/B$ and keep every other term. The resulting score is $Q=R/B$ for an affine $R$, because the bias can be absorbed into $R$. The exact difference identity gives

$$ \left|\frac{L(x)}{B(x)+\varepsilon D(x)}-\frac{L(x)}{B(x)}\right|=\frac{\varepsilon|D(x)|}{B(x)}\left|\frac{L(x)}{B(x)+\varepsilon D(x)}\right|\leq\varepsilon\left\|\frac{L}{B+\varepsilon D}\right\|_\infty. $$

Hence $\|S-Q\|_\infty\leq\varepsilon$ times the full amplitude of $S$. If the relative margin of $S$ exceeded $\varepsilon$, then $Q$ would be strict and have the same complete truth table.

Fix all coordinates except the first two. The four values of an affine $R$ satisfy

$$ R_{00}+R_{11}=R_{01}+R_{10}. $$

They cannot have simultaneously the XOR-product signs $+,-,-,+$: the left side would be strictly positive and the right side strictly negative. At least one vertex in each disjoint four-point fiber is therefore misclassified by $\mathrm{sign}(R)$, giving at least $2^n/4$ errors. This contradicts the assumed agreement. $\blacksquare$

The conclusion includes agreement on $15/16$ of the cube and permits arbitrary signed cancellation in every refitted comparison. It rules out a repair based only on independently reweighting existing groups, even if that procedure is strengthened to arbitrary numerator refitting and arbitrary repetition of the old denominators.

## What survives

Changing the second denominator to $B+D/4$ gives the same two-head truth table with relative margin at least

$$ \frac1{12(n+1)^2}. $$

Indeed its signed gap is at least $1/[4(n+1)(n+5/4)]$, while the two individual norms sum to at most $1+4/3=7/3$; these bounds imply the displayed looser constant. Every coefficient of the new denominator is still positive. Thus the target has a good representation at the same width.

This is a written counterexample to a fixed-dictionary group-rescaling argument. It is not an obstruction to unrestricted repair, nor an example of a truth table for which every comparable-width representation has small margin. The fully kernel-checked `TwoFactorMarginRepair.hasRelativeMargin_of_two_LTFs` supplies a more general new-direction repair theorem, with a different explicit bound.
