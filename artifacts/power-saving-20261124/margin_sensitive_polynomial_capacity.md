# Polynomial sign capacity after conditioning each denominator

## Status and scope

This note gives a new unconditional relation between width, relative head-amplitude margin, and the number of Boolean targets. It does not give a lower bound for unrestricted head complexity. Arbitrarily small margins remain permitted in the original model.

The argument differs from a metric cover of normalized heads. A reciprocal is replaced by a polynomial whose degree is proportional to the logarithm of the reciprocal margin. Polynomial sign counting then pays the logarithm of that degree. Consequently the entropy penalty is proportional to the double logarithm of the reciprocal margin.

The original proofs below are written mathematical proofs. The follow-up run has now formalized the finite theorem and both requested scale estimates. The declarations and exact hypotheses are recorded in the audit section below. The polynomial sign bound used in the written proof is Warren's strict-sign estimate, in the form of Proposition 5.4 in [Alon, Tools from Higher Algebra](https://web.math.princeton.edu/~nalon/PDFS/tools1.pdf). Its Lean implementation is also kernel checked.

## Definitions

Let $n\geq1$, $H\geq1$, and $N=2^n$. Consider an admissible original-model score

$$ S(x)=c+\sum_{h=1}^H\phi_h(x),\qquad \phi_h(x)=\frac{A_h(x)}{B_h(x)},\qquad x\in\lbrace0,1\rbrace^n. $$

Every denominator is affine, strictly positive on the whole cube, and has slopes all strictly positive, all strictly negative, or all zero. Numerators obey the original coherent-sign restriction when the denominator is constant. Define

$$ M=|c|+\sum_{h=1}^H\max_x|\phi_h(x)|. $$

For a strict Boolean target $F:\lbrace0,1\rbrace^n\to\lbrace-1,+1\rbrace$ represented by $S$, put

$$ \gamma(S,F)=\frac{\min_x F(x)S(x)}{M}. $$

The denominator $M$ is positive for every strict representation. Moreover $0\lt\gamma(S,F)\leq1$. Let $T(n,H,\gamma)$ be the number of targets having a representation with at most $H$ heads and $\gamma(S,F)\geq\gamma$, where $0\lt\gamma\leq1$. Zero heads can pad a representation to exactly $H$ heads, using any admissible denominator and the zero numerator. This leaves $M$ unchanged.

## Theorem 1. A quantitative margin-sensitive sign count

Put

$$ p=1+3(n+1)H,\qquad d=\left\lceil(n+1)\log\frac{2}{\gamma}\right\rceil,\qquad D=2d+2. $$

Here $\log$ is the natural logarithm. If $p\leq N$, then

$$ T(n,H,\gamma)\leq\bigl(2(n+1)!\bigr)^H\left(\frac{4eDN}{p}\right)^p. $$

The theorem allows arbitrary coefficient magnitudes, target-dependent denominators, and cancellation. The displayed margin condition is its only additional hypothesis.

### Proof. Step 1. Normalize the orientation

For each head separately, replace its input coordinates by either $y_i=x_i$ or $y_i=1-x_i$, according to the common sign of its denominator slopes. This is a choice of one of two orientations, not a shared change of the target's input coordinates. The numerator remains affine in $y$. The denominator becomes

$$ B(y)=b_0+\sum_{i=1}^n b_i y_i,\qquad b_0\gt0,\qquad b_i\geq0. $$

For a nonconstant admissible denominator, every $b_i\gt0$. For a constant denominator, every $b_i=0$. Positivity of $b_0$ follows by evaluating the original denominator at its minimizing cube vertex. We retain zero coefficients only to include the constant case.

### Proof. Step 2. Partition by the largest present coefficient

Choose a permutation ordering the $n+1$ numbers $b_0,b_1,\ldots,b_n$ nonincreasingly, with any fixed tie convention. There are at most $(n+1)!$ possible orders. At input $y$, index $0$ is always present, and index $i\geq1$ is present exactly when $y_i=1$. Let $j(y)$ be the first present index in the chosen order. Set $q(y)=b_{j(y)}$.

Since the positive coefficient $b_0$ is always present, $q(y)\gt0$. Every summand present in $B(y)$ is at most $q(y)$, and one equals it. Thus

$$ 1\leq\frac{B(y)}{q(y)}\leq n+1. $$

Once the orientation and coefficient order are fixed, the index $j(y)$ depends only on the Boolean input. This is the point that permits one polynomial evaluation predicate for each cube vertex.

### Proof. Step 3. Approximate a reciprocal by an elementary polynomial

For $u\in[1,n+1]$, define

$$ P_d(u)=\frac{1}{n+1}\sum_{k=0}^{d}\left(1-\frac{u}{n+1}\right)^k. $$

The finite geometric sum gives the exact identity

$$ \frac1u-P_d(u)=\frac1u\left(1-\frac{u}{n+1}\right)^{d+1}. $$

The last factor is nonnegative and at most $\exp(-(d+1)/(n+1))\leq\gamma/2$. Consequently

$$ \left|\frac{A(y)}{B(y)}-\frac{A(y)}{q(y)}P_d\left(\frac{B(y)}{q(y)}\right)\right|\leq\frac{\gamma}{2}\left|\frac{A(y)}{B(y)}\right|. $$

This is a relative error for each head at each point. It does not require a bound on its affine coefficients or on the condition number of its denominator over the whole cube.

### Proof. Step 4. Enlarge to a polynomial parameter family

Introduce $n+1$ new real parameters $z_0,\ldots,z_n$ for each head. At the actual representation set $z_j=1/b_j$ when $b_j\gt0$; values of $z_j$ corresponding to $b_j=0$ are arbitrary because such indices never equal $j(y)$. Treating all $z_j$ as independent parameters enlarges the class.

For a fixed list of head orientations and coefficient orders, use the score

$$ G(x)=c+\sum_{h=1}^H A_h(y_h)z_{h,j_h(y_h)}P_d\bigl(B_h(y_h)z_{h,j_h(y_h)}\bigr). $$

At each fixed cube input, this is a polynomial in $p=1+3(n+1)H$ real parameters: the bias, the affine numerator coefficients, the affine denominator coefficients, and the new reciprocal-coefficient parameters. Its total degree is at most $2d+2=D$. Indeed $B_hz_{h,j}$ has degree two, and the outside factor $A_hz_{h,j}$ also has degree two.

At the actual parameter values,

$$ |S(x)-G(x)|\leq\frac{\gamma}{2}\sum_h\max_y|\phi_h(y)|\leq\frac{\gamma M}{2}. $$

If $F(x)S(x)\geq\gamma M$ at every vertex, then $F(x)G(x)\geq\gamma M/2\gt0$. Thus $G$ has exactly the same strict sign table as $S$.

There are at most $\bigl(2(n+1)!\bigr)^H$ lists of orientations and orders. For each such list, Warren's bound gives at most $(4eDN/p)^p$ strict sign tables when $p\leq N$. Their union proves the theorem. $\blacksquare$

## Corollary 2. Doubly exponential margins are necessary at the disputed width scale

Fix a real number $\beta$ with $0\lt\beta\lt1$. There are an absolute constant $c\gt0$ and an integer $n_0(\beta)$ such that, for every integer $n\geq n_0(\beta)$ and every integer

$$ 1\leq H\leq\frac{c2^n}{n^{1+\beta}}, $$

at most $2^{N/2}$ targets admit an $H$-head representation whose relative amplitude margin is at least

$$ \gamma_n=\exp\bigl(-\exp(n^\beta)\bigr). $$

For example, $c=1/100$ works after increasing $n_0(\beta)$.

Equivalently, a uniformly random Boolean target has probability at most $2^{-N/2}$ of admitting such a representation. Outside this exceptional set, either the target has no representation of the specified width, or every representation of that width has margin smaller than $\gamma_n$.

**Proof.** Let $H_n=\lfloor cN/n^{1+\beta}\rfloor$. The sign family is nested in the width by zero-head padding, so it suffices to use $H_n$. For sufficiently large $n$, $H_n\geq1$ and

$$ \frac{p}{N}=(3c+o(1))n^{-\beta}. $$

For $\gamma=\gamma_n$, the chosen polynomial degree satisfies

$$ \log_2 D=\frac{n^\beta}{\log2}+O(\log n). $$

The logarithm of the orientation and order factor is at most

$$ H_n\bigl(1+(n+1)\log_2(n+1)\bigr)=O\left(\frac{cN\log n}{n^\beta}\right)=o(N). $$

Also $\log_2(N/p)=O_\beta(\log n)$. Therefore Theorem 1 gives

$$ \log_2 T(n,H_n,\gamma_n)\leq\left(\frac{3c}{\log2}+o(1)\right)N. $$

For $c=1/100$, the limiting coefficient is less than $1/2$. Increasing $n_0(\beta)$ makes the bound at most $N/2$. $\blacksquare$

## Consequence and the exact remaining gap

If one could prove that every target represented with $H$ heads also has a representation with at most $C H$ heads and relative margin at least $\exp(-\exp(n^\beta))$, for some fixed $\beta\lt1$ and absolute $C$, Corollary 2 would give the requested exponent improvement with $x=1+\beta\lt2$. A repair to margin $\exp(-n^C)$ would give a stronger count at the $N/(n\log n)$ scale.

No such sparse margin repair is proved here. Generic semialgebraic witness estimates are much weaker at exponentially large width. Unlimited-head constructions with good margin do not imply a width-preserving repair. Exact pencil families can separately be counted by their small nonlinear parameter block, but an arbitrary denominator configuration need not belong to few pencils.

The earlier typical-target amplitude theorem, which forces margins at most $4n/\sqrt N$ independently of width, does not contradict this approach. Such a singly exponential margin still gives polynomial approximation degree and logarithmic degree cost. The present obstruction is specifically the potentially doubly exponential deterioration of the best margin at small width.


## Follow-up kernel audit and logarithmic scale

The finite formula is now `HeadComplexity.OriginalMarginCapacity.card_highMarginFunctions_le` in `formalization/HeadComplexity/Research/OriginalMarginCapacity.lean`. It uses genuine original `FracAtom` heads and the full-cube relative margin defined in `RelativeMarginQuantifiers.lean`. The coefficient-order chart includes both orientations and all $(n+1)!$ coefficient orders. Its only analytic approximation hypothesis is discharged by the displayed ceiling degree. The parameter hypothesis remains $1+3(n+1)H\leq N$.

The declarations `HeadComplexity.MarginCapacityEstimates.card_highMargin_sqrt_scale` and `HeadComplexity.MarginCapacityEstimates.card_highMargin_logarithmic_scale` establish the following finite bounds for every $n\geq32$:

$$ H\leq\frac{N}{100n\sqrt n},\quad\gamma=\exp(-\exp(\sqrt n))\quad\Longrightarrow\quad T(n,H,\gamma)\leq2^{N/2}. $$

$$ H\leq\frac{N\log n}{100n^2},\quad\gamma=\exp(-\exp(n/\log n))\quad\Longrightarrow\quad T(n,H,\gamma)\leq2^{N/2}. $$

The logarithmic statement is obtained directly from the finite formula, with $t=n/\log n$. It is not an application of the fixed-power corollary with an exponent depending on $n$. In both cases the proof bounds the natural-log entropy by $7N/25$, checks the parameter budget, and uses $7/25\lt(\log2)/2$.

The overhead versions charge a comparison width $K=\lceil CH\rceil+B$. For $C\geq1$, they replace $1/100$ by $1/(100C)$ and require $500(B+1)n^2\leq N$. This condition holds for every sufficiently large $n$ for each fixed additive overhead $B$. Thus neither rounding nor a constant multiplicative overhead is omitted.

All these declarations have transitive axioms exactly among `propext`, `Classical.choice`, and `Quot.sound`. Build and axiom logs are in `artifacts/power-saving-20261124-followup/`; see [the finite audit](../power-saving-20261124-followup/finite_count_audit.md) for the declaration inventory and constants.

The unrestricted conclusion is still absent. The exact exceptional set is `allRepresentationsLowMargin n H K gamma`, meaning original width $H$ truth tables for which every strict width $K$ representation has margin below $\gamma$. `mem_allRepresentationsLowMargin_iff` proves that universal quantifier explicitly. A low-margin chosen representation, rescaling, or a strict weak-limit argument cannot replace a count of this set or a truth-table-preserving repair.
