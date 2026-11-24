# Adaptive product compilation can require a logarithmic width increase

## Statement and scope

For arbitrarily large head counts $H$, there is a Boolean input dimension $n$ and a strict Boolean target with an admissible original representation using at most $H$ heads, for which every representation by $K$ affine-times-product atoms and a free bias satisfies $K=\Omega(H\log H)$.

The replacement atoms may be chosen jointly, depend on the complete target, and use arbitrary real one-bit factors. Consequently no universal compiler with $K\leq CH$ exists for any absolute constant $C$.

The construction can be made with $n=\Theta(H\log H)$, and then forces $K=\Omega(H\log n)$. It does not establish this obstruction when $H$ is exponential in $n$, and does not rule out a compiler with $K=O(H\log n)$ or another subpolynomial overhead in $n$. Such a compiler could still imply the requested worst-case head lower bound. This note proves a new compiler obstruction, not the requested lower bound itself.

## Explicit parameters

For every integer $s\geq1$, put

$$ q=2^s,\qquad H=2q^2,\qquad L=q^2,\qquad m=\frac{q(q+1)}2,\qquad M=ms,\qquad J=2^{M-1}. $$

There is an original $H$-head strict sign target on $n=M+L(m+1)=\Theta(H^2)$ bits whose restriction to $M$ selected row inputs and $J$ selected column inputs has sign rank $M$. Therefore every affine-times-product representation with a free bias satisfies

$$ 2K+1\geq M,\qquad \frac KH\geq\frac{(1+1/q)s}{8}-\frac1{4q^2}. $$

Since $\log_2H=2s+1$, the required width ratio grows as a positive constant times $\log H$. A further counting argument below reduces the input dimension to $n=2M=\Theta(H\log H)$, while retaining the lower bound $K=\Omega(H\log H)=\Omega(H\log n)$.

## Fixed reciprocal queries with many independently chosen signs

The following construction is the Hall-selector theorem checked in the prior branch `origin/ar/7485202da367`, in `artifacts/beyond-counting-bound/reciprocal-matching-shattering.md`. Its general finite-field matching and selector inequalities are also formalized there in `ReciprocalMatchingShattering.lean` and `ReciprocalLevelSelector.lean`. For completeness, the written argument needed here is reproduced below.

Let $I=\mathbb F_q^2$, of cardinality $L=q^2$. Take $q/2$ copies of each of the $q+1$ directions of affine lines. There are $m=q(q+1)/2$ such direction copies, indexed by $g=0,\ldots,m-1$. For each copy, choose a linear map $c_g:I\to\mathbb F_q$ with that direction as its fibers. Fix a bijection between the field and $s$-bit strings.

### Lemma 1. Independent colors have distinct representatives

For every choice of colors $a_g\in\mathbb F_q$, there are distinct $i_g\in I$ with $c_g(i_g)=a_g$.

**Proof.** Each requested color class is an affine line, and each line can occur at most $q/2$ times among the chosen direction copies. Suppose a set $T\subset I$ with $|T|\lt m$ contains $t$ distinct affine lines. It cannot contain $q+1$ lines, because any such collection has union size at least

$$ (q+1)q-\binom{q+1}{2}=m. $$

Thus $t\leq q$, and pairwise intersections have size at most one, giving

$$ |T|\geq tq-\binom t2\geq\frac{t(q+1)}2\geq\frac{tq}{2}. $$

At most $tq/2\leq|T|$ requested classes are contained in $T$. This excludes every Hall obstruction of size below $m$; larger sets already have at least as many elements as there are requested classes. Hall's theorem gives the representatives. $\blacksquare$

Let $w_{gbi}\in\lbrace-1,1\rbrace$ be bit $b$ of the encoded color $c_g(i)$, in signed form. There are $M=ms$ query indices $(g,b)$. Put $R=4L+1$, and use two positive parameters $\theta_{i,+},\theta_{i,-}$ per point $i\in I$. Define the fixed queries

$$ F_{gb}(\theta)=\sum_{i\in I}w_{gbi}\left(\frac{R^{2g+2}}{\theta_{i,+}+R^{2g+2}}-\frac{R^{2g}}{\theta_{i,-}+R^{2g}}\right). $$

These have the form $F_j(\theta)=\sum_{h=1}^H a_{jh}/(p_{jh}+\theta_h)$ with integer poles $p_{jh}\geq1$ and integer residues $a_{jh}$.

### Lemma 2. All query sign vectors have positive rational witnesses

Every assignment of signs to the $M$ queries has a positive integer parameter witness with every signed query value greater than $1/2$.

**Proof.** Interpret the $s$ desired signs at each group $g$ as its desired color. Choose distinct representatives from Lemma 1. Assign level $a_i=g$ to $i=i_g$, and assign level $m$ to every unused point. Set both parameters of point $i$ to $R^{2a_i+1}$.

For nonnegative integers $a$ and group indices $g$, put

$$ D_g(a)=\frac{R^{2g+2}}{R^{2a+1}+R^{2g+2}}-\frac{R^{2g}}{R^{2a+1}+R^{2g}}. $$

Direct division and monotonicity give

$$ D_g(g)=1-\frac2{R+1},\qquad 0\leq D_g(a)\leq\frac1{R+1}\quad(a\neq g). $$

For the latter bound, if $a\geq g+1$, the first fraction is at most $1/(R+1)$; if $a\leq g-1$, the second fraction is at least $R/(R+1)$ and the first is at most one. Exactly one selected point has level $g$, with the desired bit. Thus every signed query value is at least

$$ 1-\frac{L+1}{R+1}=1-\frac{L+1}{4L+2}\gt\frac12. $$

All parameters are positive integers. $\blacksquare$

## A general coherent embedding of selected columns

Let $T$ be any finite collection of desired sign columns. For each $\sigma\in T$, choose the positive integer witness $\theta^\sigma$ from Lemma 2. Use $M$ row bits $x_j$ and one column bit $y_\sigma$ for every selected column. For head $h$, define

$$ A_h(x,y)=\sum_{j=1}^M a_{jh}x_j,\qquad B_h(x,y)=1+\sum_{j=1}^M(p_{jh}-1/2)x_j+\sum_{\sigma\in T}(\theta_h^\sigma-1/2)y_\sigma. $$

The constant is one and all slopes are strictly positive. Thus the denominators are admissible and positive on the entire cube. The arbitrary affine numerators are permitted because every denominator is nonconstant. At the selected input $(e_j,e_\sigma)$ the score is exactly $F_j(\theta^\sigma)$.

All selected signed margins exceed $1/2$. Add the free bias $c=\sqrt2/8$. Every unperturbed full-cube score is rational, so the perturbed score is nonzero at every vertex. Also $0\lt c\lt1/4$, so all selected signs remain unchanged. This produces a strict original $H$-head target on $M+|T|$ bits with every prescribed selected sign column.

## Polynomial-dimension encoding of all antipodal columns

Take one sign vector from each antipodal pair in $\lbrace-1,1\rbrace^M$. Instead of one input bit per witness, use level bits $y_{i,a}$ for $i\in I$ and $a=0,\ldots,m$. For every selected sign column, its witness from Lemma 2 gives levels $a_i$, and its column input has $y_{i,a_i}=1$ and all other level bits zero. Exactly $L$ level bits are one.

Put $\varepsilon=1/(4L)$. For head $h=(i,\pm)$, retain the same numerator $A_h$ and define

$$ B_h(x,y)=1+\sum_{j=1}^M(p_{jh}-1/2)x_j+\varepsilon\sum_{k\in I}\sum_{a=0}^m y_{k,a}+\sum_{a=0}^m(R^{2a+1}-3/4)y_{i,a}. $$

Every slope is strictly positive, including level bits belonging to other points, and the constant is one. At the selected row and level assignment the denominator equals

$$ 1+(p_{jh}-1/2)+L\varepsilon+(R^{2a_i+1}-3/4)=p_{jh}+\theta_h. $$

The selected column vertices are distinct: equal level assignments would give equal query values, which cannot have two distinct strict sign columns. Thus all $J=2^{M-1}$ antipodal classes occur on distinct vertices using only $L(m+1)$ column bits. The same irrational bias makes the full-cube score strict. The total dimension is $n=M+L(m+1)=\Theta(H^2)$.

## Rank forces the compiler overhead

### Lemma 3. An antipodal-complete sign table has full row sign rank

If a strict sign table with $M$ rows contains at least one representative of every antipodal sign pair, every real matrix with that sign table has rank at least $M$.

**Proof.** Otherwise choose a nonzero vector $a$ in its left kernel. Extend the signs of the nonzero entries of $a$ to a complete sign vector $\tau$. Some column has signs $\tau$ or $-\tau$. Its scalar product with $a$ has all nonzero terms positive, or all nonzero terms negative. At least one is nonzero, contradicting membership in the left kernel. $\blacksquare$

Now let a product atom on the full cube be an affine form times arbitrary one-bit factors. Across the row-column partition, write its product factor as $U(x)V(y)$ and its affine form as $L_x(x)+L_y(y)$. Write $z_\sigma$ for the selected column vertex, which can be a one-hot vertex or the level encoding. At the selected inputs its matrix is

$$ \big(L_x(e_j)U(e_j)\big)V(z_\sigma)+U(e_j)\big(L_y(z_\sigma)V(z_\sigma)\big), $$

a sum of two rank-one matrices. A free bias contributes at most rank one. Therefore $K$ affine-times-product atoms plus a bias have selected matrix rank at most $2K+1$. Lemma 3 gives $2K+1\geq M$ and the stated ratio after substitution. $\blacksquare$

With pure product atoms and a free bias, the stronger inequality is $K+1\geq M$.

## A dimension linear in the number of shattered queries

One can reduce the dimension further if a fixed positive fraction of the full row sign rank is enough.

### Lemma 4. Some square sign tables have linear sign rank

For every integer $M\geq100$, there is an $M$ by $M$ strict sign table with sign rank greater than $M/100$.

**Proof.** Put $r=\lfloor M/100\rfloor$. Every matrix of rank at most $r$ factors as $UV$, with $U$ of size $M$ by $r$ and $V$ of size $r$ by $M$. Its $M^2$ entries are degree-two polynomials in $p=2Mr\leq M^2$ real variables. Warren's strict-sign bound gives at most

$$ \left(\frac{4eM}{r}\right)^{2Mr} $$

strict sign tables of rank at most $r$. The function $r\log(4eM/r)$ is increasing for $0\lt r\leq M/100$. Therefore the logarithm base two of this bound is at most

$$ \frac{2M^2}{100}\log_2(400e)\lt\frac{22M^2}{100}\lt M^2. $$

Here $e\lt3$ gives $400e\lt2^{11}$. Fewer than the $2^{M^2}$ strict sign tables have sign rank at most $r$. An omitted table has integer sign rank at least $r+1\gt M/100$. $\blacksquare$

For $s\geq3$, the selector construction has $M\geq100$. Choose a table from Lemma 4 and use its $M$ columns in the general coherent embedding. This gives an original $H$-head strict target on

$$ n=2M=q(q+1)s=\Theta(H\log H) $$

bits. The same bound of $2K+1$ on matrix rank now implies

$$ 2K+1\gt M/100,\qquad \frac KH\gt\frac{(1+1/q)s}{800}-\frac1{4q^2}. $$

For $s\geq3$, one has $2s\leq\log_2n\leq4s$, so this is $K=\Omega(H\log n)$. The sign table in Lemma 4 is obtained by a finite counting argument; this dimension reduction is an existence theorem, not an efficiently generated explicit matrix.

## What this does not prove

The strongest dimension reduction has $H=\Theta(n/\log n)$, which is far below the exponential widths relevant to the desired worst-case lower bound. The theorem excludes a constant-overhead joint adaptive product compiler uniformly in all dimensions and widths. It does not exclude a compiler with $K=O(H\log n)$, whose logarithmic overhead matches this obstruction up to constants and could still imply an exponent saving for the original model.

The desired unrestricted worst-case lower bound remains open.

## Verification boundary

The Hall-selector ingredient is a previously kernel-checked theorem, with declarations `HeadComplexity.ReciprocalMatchingShattering.unbounded_tests_per_positive_parameter` and the more explicit constructions in that module. The exact bipartite head embedding was also checked in the prior module `HeadComplexity.Results.BipartiteReciprocalShattering`, whose declaration namespace is `HeadComplexity.BipartiteReciprocalShattering`.

The general antipodal matrix argument and product-score rank bound are newly formalized in `formalization/HeadComplexity/Research/AntipodalProductRank.lean`. The declarations are `HeadComplexity.AntipodalProductRank.rank_eq_card_of_antipodal`, `HeadComplexity.AntipodalProductRank.signRank_eq_card_of_antipodal`, `HeadComplexity.AntipodalProductRank.productScoreMatrix_rank_le`, and `HeadComplexity.AntipodalProductRank.product_width_of_antipodal`. Independent fresh builds passed, and `antipodal-product-independent-lean-audit.txt` records only the standard foundational axioms for these four declarations.

The identification of Boolean product atoms with the matrix model, the polynomial-dimension level encoding, the square-matrix counting argument, and the full original-model compiler obstruction remain written proofs. Thus the asymptotic obstruction is not claimed as one end-to-end Lean theorem. The independent rational six-row example in `adaptive_two_product_separation.md` is a separate small finite instance; it is not used to infer the general asymptotic result.
