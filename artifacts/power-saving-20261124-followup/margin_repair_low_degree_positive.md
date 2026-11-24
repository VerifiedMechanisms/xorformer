# A quantitative repair for low threshold degree

## Statement and status

Let $n,d\geq0$, and let $f:\lbrace0,1\rbrace^n\to\lbrace-1,+1\rbrace$ have strict polynomial threshold degree at most $d$. Put

$$ D=\sum_{j=0}^d\binom nj. $$

There is a representation of the entire truth table by $D$ genuine original heads, zero bias, and full-cube relative margin at least

$$ \gamma_D=\frac{1}{2DD!+1}. $$

The integer separator step is kernel checked in `formalization/HeadComplexity/Research/LowDegreeMarginRepair.lean`, as `HeadComplexity.LowDegreeMarginRepair.exists_integer_monomial_separator`. The compiler is kernel checked separately in `MonomialMarginCompiler.lean`, as `HeadComplexity.MonomialMarginCompiler.hasRelativeMargin_of_thresholdDegree`. Its original-model corollary is `HeadComplexity.MonomialMarginCompiler.hasRelativeMargin_of_computable`. The declaration `HeadComplexity.MonomialMarginCompiler.not_mem_allRepresentationsLowMargin_of_thresholdDegree` excludes these tables from the universally quantified bad-margin class whenever the comparison width and requested margin fit the displayed budget. These statements permit arbitrary real coefficients in the starting threshold polynomial. The original-model corollary applies to every table representable with $H$ heads, using $d=H$ and the inherited denominator-clearing threshold-degree theorem. The width is $D$, not a constant multiple of $H$ in general.

The asymptotic estimates and the cluster-composition obstruction below are written proofs. They are intermediate progress and do not imply a lower bound beyond the inherited unrestricted one.

## Integer coefficients with a finite bound

Use one feature $x^S=\prod_{i\in S}x_i$ for every subset $S\subseteq\lbrace1,\ldots,n\rbrace$ with $|S|\leq d$. These $D$ features are linearly independent as real functions on the entire cube. Their independence is already formalized as `HeadComplexity.linearIndependent_lowDegreeMonomials`.

Multiplying the row at $x$ by $f(x)$ preserves row span. The signed feature matrix has integer entries in $\lbrace-1,0,1\rbrace$, and its rows span $\mathbb R^D$. A strict threshold polynomial supplies a real separator. Since the cube is finite, rescale that separator so every signed value is at least one.

The active-row argument `HeadComplexity.IntegerSeparatorMarginRepair.exists_bounded_integer_separator` then gives integers $a_S$ such that

$$ f(x)\sum_{|S|\leq d}a_Sx^S\geq1\quad\text{for every }x,\qquad |a_S|\leq D!. $$

The argument selects $D$ independent tight rows of the feasible polyhedron and applies Cramer's rule. The coefficient bound is the Leibniz determinant bound for a matrix whose entries have absolute value at most one. No coefficient-height assumption is imposed on the starting real separator.

## Compiling the monomials into genuine heads

The inherited theorem `HeadComplexity.exists_fracAtom_approx_signedMonomial` gives, for each $S$ and each $\varepsilon\gt0$, a genuine head $\phi_S$ with uniform full-cube error

$$ \left|\phi_S(x)-a_Sx^S\right|\lt\varepsilon. $$

Take $\varepsilon=1/(2D)$. Summing the errors gives an error at most $1/2$, so the resulting score has every signed value at least $1/2$. Since $x^S$ takes values in $\lbrace0,1\rbrace$, each head satisfies

$$ \|\phi_S\|_\infty\leq D!+\frac{1}{2D},\qquad \sum_S\|\phi_S\|_\infty\leq DD!+\frac12. $$

Dividing these two estimates gives $\gamma_D$. All norms are on the whole Boolean cube. The empty monomial is included, so the stated implementation may use zero bias and exactly $D$ heads. The approximation theorem's constructed heads have strictly coherent denominator slopes and are admissible in the original model.

## Explicit small-width ranges

Let either $t(n)=\sqrt n$ or $t(n)=n/\log n$. Both satisfy $t(n)/\log(n+1)\to\infty$. Suppose a table has an original representation with integer width

$$ H\leq\frac{t(n)}{4\log(n+1)}. $$

The inherited denominator-clearing theorem gives threshold degree at most $H$. For all sufficiently large $n$, the resulting dimension obeys

$$ D=\sum_{j=0}^H\binom nj\leq\sum_{j=0}^Hn^j\leq(n+1)^{H+1}\leq\exp\bigl(t(n)/2\bigr). $$

The last inequality uses $t(n)\geq4\log(n+1)$. Also $D!\leq D^D$, and $2DD!+1\leq3D^{D+1}$ for $D\geq1$. Consequently

$$ \log\frac1{\gamma_D}\leq\log3+(D+1)\log D\leq\log3+\frac{t(n)}2\left(\exp\bigl(t(n)/2\bigr)+1\right)\leq\exp\bigl(t(n)\bigr) $$

for all sufficiently large $n$. The final inequality follows after dividing by $\exp(t(n))$, because $t(n)\exp(-t(n)/2)\to0$.

Thus every table of original width $H\leq\sqrt n/[4\log(n+1)]$ has a genuine repair with margin at least $\exp(-\exp(\sqrt n))$ and width at most $\exp(\sqrt n/2)$. Likewise, every table of original width $H\leq n/[4\log n\log(n+1)]$ has margin at least $\exp(-\exp(n/\log n))$ at width at most $\exp(n/[2\log n])$.

These replacement widths are $\exp(o(n))$. They are negligible compared with either critical width $c2^n/n^{3/2}$ or $c2^n\log n/n^2$, for each fixed $c\gt0$. This proves that an isolated small-width table is repairable within an additive subexponential budget. It does not prove that all small clusters inside a much larger signed sum can be replaced this way.

## Why independent cluster repairs do not compose

The compiler preserves a cluster's sign table. It does not preserve its numerical contribution to a score containing other clusters. Denominator clearing has the same limitation: it multiplies a cluster by an input-dependent positive factor.

A one-variable example already shows the failure. Let the original admissible head be $\phi(x)=1/(1+x)$ and let the bias be $b=-3/4$. The score $b+\phi(x)$ is positive at $x=0$ and negative at $x=1$. For any $0\lt\varepsilon\lt1/3$, the replacement head

$$ \widetilde\phi(x)=\frac1{1+\varepsilon x} $$

has exactly the same positive sign table as $\phi$, is an original admissible head, and has full-cube norm one. But $b+\widetilde\phi(x)$ is positive at both inputs. Thus even a bounded, genuine, same-width repair of a cluster's own truth table need not preserve the truth table of the full signed score.

To use the small-width theorem inside an exponential-width representation, a new gluing lemma must preserve each cluster's contribution to all relevant comparison levels, or must solve all clusters' inequalities jointly. Bounds on the individual clusters' sign margins alone do not supply that lemma. This is the first failing implication of the proposed independent-cluster repair route.
