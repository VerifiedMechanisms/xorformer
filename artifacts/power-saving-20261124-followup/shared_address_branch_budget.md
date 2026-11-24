# The branch budget in a shared address family

## Exact scope

This note counts an actual Boolean observation fiber in a restricted positive reciprocal family. It gives no observation-fiber theorem for unrestricted original heads. In particular, its common known address form, fixed numerators, and fixed bias are assumptions.

Let $H\geq1$ and $k\geq1$. Split the input into $d$ address bits $z$ and $k$ selector bits $y$, with $d+k=n$. Fix a strictly positive affine address form $a(z)$ with distinct values on all $2^d$ address inputs. For example, $a(z)=1+\sum_{j=0}^{d-1}2^jz_j$ works. For positive selector parameters, set

$$ S_b(z,y)=\sum_{h=1}^{H}\frac{1}{a(z)+\sum_{i=1}^{k}b_{hi}y_i},\qquad b_{hi}\gt0. $$

All heads are original admissible heads: every denominator constant and slope is strictly positive, and the numerator is the constant one. Observe the score at every address input with exactly one selector active. Assume $2^d\geq2H-1$ and that the $H$ parameters in every selector column are distinct.

**Theorem.** Given these observations, there are at most $(H!)^{k-1}$ full real score tables of the displayed form. This upper bound is attained for suitable observations. The theorem counts real tables; it does not assert that these tables have distinct strict Boolean signs.

## Rational interpolation identifies each column

For selector $i$, define the monic polynomial and rational function

$$ Q_i(t)=\prod_{h=1}^{H}(t+b_{hi}),\qquad R_i(t)=\frac{Q_i'(t)}{Q_i(t)}=\sum_{h=1}^{H}\frac{1}{t+b_{hi}}. $$

The observations give $R_i$ at the distinct positive arguments $a(z)$. If two parameter columns have the same observations, then

$$ Q_i'(t)\widetilde Q_i(t)-\widetilde Q_i'(t)Q_i(t) $$

vanishes at at least $2H-1$ distinct points. Its degree is at most $2H-2$, because the two leading terms of degree $2H-1$ cancel. Thus it is the zero polynomial. The rational functions $R_i$ are identical, so their poles and multiplicities agree. Equivalently, the derivative of $Q_i/\widetilde Q_i$ is zero, and monicity then gives $Q_i=\widetilde Q_i$.

Hence the observations determine the unordered parameter multiset in every selector column. Simultaneous permutation of all head indices does not change the score. Fixing the first column's order leaves at most $H!$ choices for each of the other $k-1$ columns, proving the upper bound.

## Every relative matching can yield a different full table

Take $b_{h1}=h$ for $1\leq h\leq H$, and take the known multiset in every other selector column to be

$$ \lbrace(H+1),2(H+1),\ldots,H(H+1)\rbrace. $$

Every assignment of these multisets to the first-column head labels has the same single-selector observations. For two different assignments, choose a column $i$ in which they differ and activate selectors $1$ and $i$ together. The resulting pole multiset is

$$ \lbrace h+(H+1)\pi_i(h):1\leq h\leq H\rbrace. $$

Every such sum uniquely identifies its pair of indices, so different permutations produce different pole multisets. The preceding interpolation argument shows that their values cannot agree at all the $2^d\geq2H-1$ address points. Therefore all $(H!)^{k-1}$ relative matchings give different full real score tables.

The constructed scores are positive everywhere. They all have the constant-positive truth table. No lower bound on the number of Boolean truth tables follows from this attainment statement.

## The near-critical entropy budget

The address condition requires at least $\log_2(2H-1)$ address bits. Therefore

$$ \log\left((H!)^{k-1}\right)\leq kH\log H,\qquad k\leq n-\log_2(2H-1). $$

For any fixed $a\gt0$ and $c\gt0$, if $H\geq c2^n/n^a$ and the displayed address condition is feasible, then $k\leq a\log_2 n+O_c(1)$. Since $H\leq2^n$,

$$ \log\left((H!)^{k-1}\right)=O_{a,c}(nH\log n). $$

Thus these independent matching branches respect the entropy budget that would suffice at the requested widths. This is why simply amplifying the small-width selector counterexamples does not refute that budget.

## The first missing unrestricted lemma

An arbitrary original denominator need not share one known address form across heads. Its affine numerator need not be constant. The complete real score table on an address face need not identify its decomposition, and even generic identifiability would not control the degree of the reconstruction formulas as those real face values vary.

A useful unrestricted extension would supply charts in which an address face contributes only $O(nH)$ linear variables, while its remaining $n-d$ directions contribute only $O((n-d)H)$ nonlinear variables and predicates of polynomial degree in $n$. The partially linear sign count could then exploit the small number of remaining directions. No such chart has been established here. Replacing real face values by their sign labels would be a further unsupported step.

The interpolation and factorial bounds above are written proofs. No Lean declaration or finite computational certificate is claimed.
