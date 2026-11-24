# A Divisibility Test for Permutation Moment Cancellation

## Statement and boundary

This note tests the near-coincident endpoint of the permutation family supplied by the asker. It proves a nonvanishing criterion for its leading moment polynomials using an integer congruence. It does not bound the signs of the family at arbitrary finite scale, and it does not improve the unrestricted worst-case head lower bound.

Let $H\geq2$, let $n\geq2$, and let $\pi_1,\ldots,\pi_n$ be permutations of $[H]$. For real levels $\alpha_1,\ldots,\alpha_H$, write $\bar\alpha=H^{-1}\sum_r\alpha_r$ and $a_r=\alpha_r-\bar\alpha$. If $S\subseteq[n]$ has cardinality $k$, define, for $2\leq j\leq k$,

$$ P_{S,j}(\alpha)=\sum_{h=1}^H\sum_{\substack{V\subseteq S\cr |V|=j}}\prod_{i\in V}a_{\pi_i(h)}. $$

The permutations are fixed when this expression is regarded as a polynomial in the levels.

**Theorem 1.** If $H$ does not divide $(j-1)\binom{k}{j}$, then $P_{S,j}$ is a nonzero polynomial. More strongly, its value at every standard coordinate vector $e_r\in\mathbb R^H$ is nonzero, with

$$ |P_{S,j}(e_r)|\geq H^{1-j}. $$

Consequently, if a prime power $p^r$ divides $H$ and

$$ r\gt\lfloor\log_p n\rfloor+\lfloor\log_p(n-1)\rfloor, $$

then this conclusion holds simultaneously for every permutation tuple, every $S$, and every $2\leq j\leq|S|$. In particular, it holds whenever $H$ is a power of two and $H\gt n(n-1)$.

This last range includes rounded dyadic widths of order $2^n/n^x$ for every fixed $x\gt0$ and all sufficiently large $n$. This is a statement about nonzero polynomials and their endpoint signs. It is not a statement about all head representations at those widths.

## The integer congruence

Fix a level index $r$ and set $\alpha=e_r$. For each row $h$, let

$$ m_h=|\lbrace i\in S:\pi_i(h)=r\rbrace|. $$

Each column contains the level $r$ once, so $\sum_hm_h=k$. At this choice of levels, each centered entry is either $1-1/H$ or $-1/H$. Hence $P_{S,j}(e_r)$ is the coefficient of $z^j$ in

$$ \sum_{h=1}^H(1+z(1-1/H))^{m_h}(1-z/H)^{k-m_h}. $$

For a fixed row, expand the first factor by treating its entries as $-1/H$ plus an exceptional increment of one. Put $M_\ell=\sum_h\binom{m_h}{\ell}$, so that $M_0=H$ and $M_1=k$. Coefficient extraction gives

$$ P_{S,j}(e_r)=\sum_{\ell=0}^j M_\ell\binom{k-\ell}{j-\ell}(-1/H)^{j-\ell}. $$

Combining the first two terms and multiplying by $H^{j-1}$ gives the exact integer identity

$$ H^{j-1}P_{S,j}(e_r)=(-1)^j(1-j)\binom{k}{j}+\sum_{\ell=2}^j(-1)^{j-\ell}H^{\ell-1}M_\ell\binom{k-\ell}{j-\ell}. $$

In particular,

$$ H^{j-1}P_{S,j}(e_r)\equiv(-1)^j(1-j)\binom{k}{j}\pmod H. $$

If the stated divisibility fails, the integer on the left cannot be zero. Its absolute value is at least one, proving both assertions of Theorem 1. No assumption about distinct rows or distinct numerical levels is needed. $\blacksquare$

## The prime-power range

For completeness, the needed valuation bound follows directly from the factorial formula. Counting the multiples of each power of a prime $p$ gives

$$ v_p(k!)=\sum_{a\geq1}\lfloor k/p^a\rfloor. $$

Subtract the analogous formulas for $j!$ and $(k-j)!$. Every summand in the difference is zero or one, and only $a\leq\lfloor\log_p k\rfloor$ can contribute. Therefore

$$ v_p\binom{k}{j}\leq\lfloor\log_p k\rfloor,\qquad v_p(j-1)\leq\lfloor\log_p(j-1)\rfloor. $$

For $2\leq j\leq k\leq n$, their sum is at most the bound in the statement. Thus $p^r$ cannot divide $(j-1)\binom{k}{j}$, so neither can $H$. This proves the simultaneous criterion. If $H=2^r\gt n(n-1)$, then $r\gt\log_2 n+\log_2(n-1)$, which is sufficient.

The factorial valuation formula and its relation to Kummer's carry theorem are also stated in [the primary research article, Theorems 2.3 and 2.4](https://math.colgate.edu/~integers/v120/v120.pdf). The elementary argument above supplies all number theory used here.

## Distinct levels can be chosen explicitly

Under the simultaneous criterion, nonvanishing holds outside a finite union of proper algebraic zero sets in the level space. In particular, generic distinct real levels work simultaneously for all permutation tuples. There is also a direct finite choice.

Choose a rational number

$$ 0\lt\eta\lt\frac1{2n4^nH^n},\qquad \alpha_r=\mathbf1_{\lbrace r=1\rbrace}+\eta\frac rH. $$

These levels are distinct. They are within $\eta$ in maximum norm of $e_1$. Centering changes each entry by at most $2\eta$. Since the centered entries at $e_1$ have absolute value at most one, and $\eta\leq1/2$, telescoping a product of $j$ entries bounds its change by $j2^j\eta$. There are $H\binom{k}{j}$ such products. Uniformly over all choices,

$$ |P_{S,j}(\alpha)-P_{S,j}(e_1)|\leq Hn4^n\eta\lt\tfrac12H^{1-n}. $$

Theorem 1 gives $|P_{S,j}(e_1)|\geq H^{1-j}\geq H^{1-n}$. Every displayed polynomial therefore stays nonzero, and keeps its sign, at these explicit distinct levels.

## Consequence for the near-coincident family

Fix positive $c$, fixed levels $\alpha$, and put $\beta_r=1+\epsilon\alpha_r$. For sufficiently small positive $\epsilon$, all levels are positive. Define the actual admissible reciprocal-head score

$$ T_\pi(S)=\sum_{h=1}^H\frac1{c+\sum_{i\in S}\beta_{\pi_i(h)}},\qquad \mu_k=H\mathbb E\frac1{c+\beta_{U_1}+\cdots+\beta_{U_k}}, $$

where the indices $U_i$ are independent and uniform on $[H]$. Every denominator has positive constant coefficient and strictly positive variable slopes.

Subtract from $T_\pi$ its Hoeffding components of orders zero through $d$, where $1\leq d\lt n$, and put $j=d+1$. The order-one component already sums to zero. The resulting table is identically zero when $|S|\lt j$. For $|S|\geq j$, its expansion starts with

$$ \frac{(-1)^j j!\epsilon^j}{(c+|S|)^{j+1}}P_{S,j}(\alpha)+O(\epsilon^{j+1}). $$

To verify the coefficient, expand the reciprocal at $c+k$. Every polynomial term of degree less than $j$ in the selected level variables has Hoeffding order less than $j$ and is removed. At degree $j$, only products involving $j$ distinct coordinates survive; centering replaces each selected level by $a_r$, and there are $j!$ orderings of those coordinates. This gives the displayed expression. The finite input and permutation sets make the remainder uniform for fixed levels.

If the levels satisfy the simultaneous nonvanishing conclusion above, sufficiently small positive $\epsilon$ gives exactly the signs of $(-1)^jP_{S,j}(\alpha)$ on every set of size at least $j$, for every permutation tuple at once. The cutoff on $\epsilon$ is allowed to depend on the fixed levels, $H$, $n$, and $c$.

The counterterms are realizable in the unchanged model. For a fixed $V\subseteq[n]$ of size $q$ and arbitrary real numbers $a_0,\ldots,a_n$, the table $\mathbf1_{\lbrace V\subseteq S\rbrace}a_{|S|}$ has an exact representation by at most $(q+1)(n+1)$ reciprocal heads. Choose $C\gt n$ and distinct positive $\gamma_\ell$. The numbers $t+Cz$, with $0\leq t\leq n$ and $0\leq z\leq q$, are distinct. The square Cauchy matrix $1/(\gamma_\ell+t+Cz)$ is invertible: a vanishing linear combination at all its $M$ nodes would have a numerator of degree at most $M-1$ with $M$ distinct roots; evaluation at the distinct poles then makes every coefficient zero. Thus its columns interpolate values $a_t$ when $z=q$ and zero otherwise. Substitute $t=|S|$ and $z=|S\cap V|$. All denominator slopes are either one or $1+C$, and all constants are positive. Summing this construction over orders through $d$ uses at most

$$ (n+1)\sum_{q=0}^d(q+1)\binom nq $$

additional heads. This upper estimate includes the unnecessary first-order terms. No sign-preserving conversion of arbitrary head representations is asserted.

## Counting the endpoint signs

Replace the entries $a_{\pi_i(h)}$ by independent real parameters $u_{hi}$. At any Boolean input, the expression

$$ Q_j(x)=(-1)^j\sum_{h=1}^H\sum_{\substack{V\subseteq[n]\cr |V|=j}}\prod_{i\in V}(u_{hi}x_i) $$

has parameter degree $j$. A sufficiently small positive bias fixes the zero outputs with $|x|\lt j$ and preserves all other signs. Thus the endpoint tables above belong to the strict sign family of $Q_j(x)+b$, in $p=nH+1$ real parameters. When $N=2^n\geq p$, Warren's bound gives

$$ \log_2(\text{number of endpoint tables})\leq p\log_2\left(\frac{4ejN}{p}\right). $$

For $H$ between fixed positive multiples of $N/n^x$, with fixed $1\lt x\lt2$, and $j\leq n$, this is $O(nH\log n)$. The constants may depend on the fixed width comparison constants and $x$. This count concerns distinct signs, not parameter components.

Without higher-order subtraction, $j=2$ and $Q_2$ is simply a homogeneous quadratic polynomial in the input bits. Its coefficients are the pairwise column inner products. The resulting strict endpoint tables, with a small bias added at weights zero and one, have count at most

$$ \sum_{r=0}^{D}\binom Nr\leq(eN/D)^D,\qquad D=1+\binom n2, $$

and hence logarithm $O(n^3)$, independently of $H$. This follows from the VC bound for a linear space of $D$ features and Sauer's inequality.

## Why the unrestricted target remains open

The congruence proves nonvanishing at a specified level vector and on a generic fixed-level set. It does not prove nonvanishing at every real level vector. The asker's exact moment-matching examples have exceptional levels with arbitrarily deep cancellation. Those examples are consistent with this theorem.

The small-scale limit also keeps the levels fixed while sending $\epsilon$ to zero. Rewriting arbitrary finite levels as $1+\epsilon\alpha_r$ and allowing $\alpha_r$ to diverge with $\epsilon$ does not put them in this limit. There is no uniform cutoff independent of the levels in the proof. An arbitrary strict finite-scale head representation has not been converted to one of the endpoint tables counted above.

Consequently neither generic nonvanishing, the endpoint sign count, nor the prime-power head range proves any improvement over the unrestricted exponent two. The full finite-scale sign count and the fixed-exponent lower-bound goal remain unresolved.

## Verification

The congruence, valuation argument, explicit perturbation, endpoint expansion, and actual-head counterterm construction are complete written proofs. They are not new Lean declarations. The companion exact-arithmetic verifier checks the coefficient identity for integer occupancy partitions and checks the stated divisibility range on finite inputs. Its computations supplement, rather than replace, the proofs. No definition or admissibility condition in `HeadComplexity` is changed.
