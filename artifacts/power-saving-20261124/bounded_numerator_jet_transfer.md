# Bounded Numerator Jets Admit Polynomial Sign Counting

## Status and new mechanism

This auxiliary theorem extends fixed-radial transfer to polynomial numerator paths of bounded order. Numerators may move and may cancel to arbitrarily high total order. A finite list of low-order moment tests, followed by one exponential score with polynomial numerators, determines every eventual sign. This does not prove that arbitrary original-model representations have such a description with bounded jet order.

The proof below is written mathematics. No Lean formalization is claimed. It avoids the false assertion that arbitrary affine-numerator recalibration within the same exponential directions suffices: the new exponential numerators have degree up to $r+1$ in the input.

## Transfer theorem on a finite set

Let $X$ be finite. Fix functions $B,C_h,A_{hj}:X\to\mathbb R$, with $B(x)\gt0$, for $1\leq h\leq H$ and $0\leq j\leq r$. Define

$$ R_t(x)=\sum_{h=1}^H\frac{\sum_{j=0}^r t^jA_{hj}(x)}{B(x)+tC_h(x)}. $$

For every integer $k\geq0$, put

$$ F_k(x)=\sum_{h=1}^H\sum_{j=0}^{\min(r,k)}A_{hj}(x)B(x)^j(-C_h(x))^{k-j}. $$

Define the fixed polynomial numerator functions and exponential score

$$ P_h(x)=\sum_{j=0}^r A_{hj}(x)B(x)^j(-C_h(x))^{r-j},\qquad E_t(x)=\sum_{h=1}^H P_h(x)e^{-tC_h(x)}. $$

There is $t_0\gt0$ such that all denominators are positive for $0\lt t\lt t_0$, and every eventual coordinate sign is determined as follows. If some $F_k(x)$ with $0\leq k\lt r$ is nonzero, use the sign of the first such $F_k(x)$. If all those low-order tests vanish, use the sign of $E_t(x)$ at any sufficiently small positive $t$. The latter sign stabilizes, including the possibility that it is identically zero.

**Proof.** At each fixed input, the convergent reciprocal expansion is

$$ R_t(x)=\sum_{k\geq0}\frac{F_k(x)}{B(x)^{k+1}}t^k. $$

The exponential expansion is

$$ E_t(x)=\sum_{\ell\geq0}\frac{F_{r+\ell}(x)}{\ell!}t^\ell. $$

The second identity follows directly by expanding each exponential and collecting terms:

$$ \sum_{h=1}^H P_h(x)(-C_h(x))^\ell=\sum_{h=1}^H\sum_{j=0}^r A_{hj}(x)B(x)^j(-C_h(x))^{r+\ell-j}=F_{r+\ell}(x). $$

If a low-order coefficient is first nonzero, positivity of $B$ proves the asserted sign. Otherwise the remaining rational and exponential coefficients differ only by positive factors. Their first nonzero coefficients therefore have the same sign. If every remaining coefficient vanishes, both germs vanish identically. Analyticity supplies eventual signs, and the finite set $X$ permits one common positive smallness threshold. $\blacksquare$

The case $r=0$ is the fixed radial moment theorem. A polynomial bias can be included by adding a term with $C_0=0$ and numerator $B\sum_j c_jt^j$.

## Affine data yield polynomial predicates of low degree

Now let $X=\lbrace0,1\rbrace^n$, with $N=2^n$, and assume $B$, every $C_h$, and every $A_{hj}$ is affine. The data are fixed independently of $t$. Write $C_h(x)=c_{h0}+\sum_i c_{hi}x_i$ and introduce independent positive variables $z_{h0},z_{h1},\ldots,z_{hn}$. At an actual scale they take the values $z_{hi}=e^{-tc_{hi}}$.

The high-order sign predicate is the polynomial

$$ E(x)=\sum_{h=1}^H z_{h0}\left(\sum_{j=0}^r A_{hj}(x)B(x)^j(-C_h(x))^{r-j}\right)\prod_{i=1}^n z_{hi}^{x_i}. $$

For fixed input, each $F_k$ with $k\lt r$ has parameter degree at most $k+1\leq r$. The displayed $E$ has parameter degree at most $n+r+2$. The parameter counts are $(r+1)H(n+1)$ for all affine numerator coefficients, $H(n+1)$ for the affine shifts, $n+1$ for the base, and $H(n+1)$ for the product variables. Thus

$$ p=(n+1)\bigl((r+3)H+1\bigr),\qquad D=n+r+2,\qquad M=(r+1)N. $$

There are $M$ polynomial predicates, namely the $r$ low-order tests and the exponential predicate at each input. The eventual label is a deterministic function of their three-valued signs: take the first nonzero low-order sign, or the exponential sign if all low-order tests vanish. Exact zeros can be assigned to the false class.

Allowing the product variables to vary independently enlarges the family. The general sign-pattern estimate in [Alon, Tools from Higher Algebra, Proposition 5.5](https://web.math.princeton.edu/~nalon/PDFS/tools1.pdf) therefore gives, when $2M\geq p$,

$$ \left|\lbrace\text{eventual Boolean labels of these order }r\text{ numerator paths}\rbrace\right|\leq\left(\frac{8eDM}{p}\right)^p. $$

This counts actual labels, including arbitrary coordinate-dependent cancellation orders. It does not count only real-table dimension, roots, or low-order tangent vectors. The use of three-valued polynomial signs is essential because the rule branches on exact vanishing of the low-order coefficients.

For every fixed nonnegative integer $r$, and widths $H=\Theta(N/n^x)$ with $1\lt x\lt2$, the logarithm of this count is

$$ O_r\bigl(nH\log(N/H)\bigr)=O_r(nH\log n)=o(N). $$

Consequently the worst-case number of heads within this bounded-jet radial class is $\Omega_r(N/(n\log n))$. More generally, if $r\leq n^\alpha$ for fixed $0\leq\alpha\lt1$, the same estimate yields an obstruction at the scale $N/(n^{1+\alpha}\log n)$, with suitable absolute constants depending on $\alpha$. This remains a restricted-class statement.

## Relation to the fixed-direction counterexample

The bounded analytic counterexample in `fixed_direction_joint_compilation_separation.md` has numerator degree two, so this theorem applies with $r=2$. It is not a contradiction. That counterexample rules out affine exponential numerators in the same two directions. The present transform uses numerators $P_h$ of input degree up to three, together with the two low-order tests. It preserves the eventual signs through a larger, but still polynomially parameterized, class.

## Precise unresolved step

No argument bounds the required numerator-jet order uniformly in the input dimension for arbitrary sign representations, and no argument reduces arbitrary denominator paths to fixed radial paths with a controlled cost. If $r$ is comparable to $n$, the parameter count in the displayed estimate can lose the desired power saving. A valid unrestricted extension must control that complexity or replace it by a different invariant. Merely invoking finite-dimensionality or the usual least-polynomial-space construction does not do so after Boolean polynomial identities are imposed.
