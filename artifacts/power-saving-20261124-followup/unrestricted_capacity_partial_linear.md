# Active row certificates and low dimensional denominator families

## Status

The active row certificate and Cramer sign reconstruction below are kernel checked in `formalization/HeadComplexity/Research/PartialLinearCertificate.lean`. The finite partially linear polynomial count is kernel checked as `HeadComplexity.PartialLinearCapacity.card_patterns_le` in `formalization/HeadComplexity/Research/PartialLinearCapacity.lean`. Its application to denominator families is a written proof. They do not yet give a smaller unrestricted bound for `HeadComplexity.worstCaseHeadComplexity`.

The count handles arbitrary real coefficients, arbitrary signed cancellation, and arbitrarily small margin. The outstanding obstruction is the number of independent denominator parameters.

## A finite partially linear count

Let $P_i(b)\in\mathbb R^L$, for $1\leq i\leq m$, be vector valued polynomials in $q$ real parameters. Assume every coordinate has total degree at most $D$, where $D\geq 0$. Consider the strict sign patterns of the scores $P_i(b)\cdot a$, where both $b\in\mathbb R^q$ and $a\in\mathbb R^L$ vary freely.

Suppose $L\geq 1$ and $q+1\leq m$. The number of strict sign patterns is at most

$$ 2^L {m+2L\choose L}\left(\frac{4e(2DL+1)m}{q+1}\right)^{q+1}. $$

This follows from the audited Warren theorem after eliminating the linear coefficients by a finite set of active sample constraints. There is no bound on the size of $a$ or $b$.

### Lemma 1. A compact active row certificate

Let $A$ be a real matrix with $L$ columns, let $r$ be a vector, and suppose the polyhedron $K=\lbrace a:Aa\geq r\rbrace$ is nonempty and compact. Then some $a\in K$ has $L$ linearly independent active rows.

**Proof.** Choose an extreme point $a$ of $K$. If the active rows do not span the dual space, there is a nonzero $v$ annihilated by every active row. All inactive constraints have strictly positive slack. Since there are finitely many constraints, sufficiently small $\varepsilon\gt 0$ makes both $a+\varepsilon v$ and $a-\varepsilon v$ feasible. Their midpoint is $a$, contradicting extremality. Select a basis among the active rows. $\blacksquare$

The Lean declarations are `extreme_active_kernel_eq_zero`, `exists_active_injective`, `exists_nonsingular_rows`, and `exists_active_basis`, all in namespace `HeadComplexity.PartialLinearCertificate`.

### Lemma 2. Actual sample and box rows suffice

Fix a strict pattern $\sigma\in\lbrace-1,+1\rbrace^m$ realized at $(b,a)$. Scale $a$ so that $\sigma_iP_i(b)\cdot a\geq 1$ for every $i$. Choose a finite $T\geq\max_j|a_j|$. Intersect these inequalities with $-T\leq a_j\leq T$.

This is a nonempty compact polyhedron. Lemma 1 supplies an unordered set $I$ of $L$ independent active rows among the $m$ sample rows and $2L$ box rows. Record the labels only on selected sample rows. There are at most

$$ {m+2L\choose L}2^L $$

such discrete certificates. The value of $T$ remains an additional free real parameter, rather than being discretized or charged as side information.

For selected sample rows, multiply the active equation by $\sigma_i$ to write it as $P_i(b)\cdot a=\sigma_i$. The selected box rows have constant coefficients and right side $-T$. Thus, after fixing $I$ and its sample labels, the square system is $M(b)a=r(T)$, with a nonsingular matrix whose entries have degree at most $D$. Each right side is constant or linear in $T$.

The Lean declaration `exists_bounded_active_basis` proves the compact certificate after adjoining the box rows. The declarations `boundedRows` and `boundedRhs` explicitly define these rows. The declaration `det_ne_zero_of_same_range` proves that an arbitrary fixed ordering of the selected row set may be used. Ordered row tuples and their factorial overcount are unnecessary.

### Lemma 3. Polynomial reconstruction

Let $\Delta(b)=\det M(b)$ and let $C(b,T)$ be the vector of Cramer numerators. Each coordinate of $C$ has degree at most $(L-1)D+1$, since exactly one determinant column is replaced by $r(T)$. Therefore

$$ Q_i(b,T)=\Delta(b)P_i(b)\cdot C(b,T) $$

has degree at most $2LD+1$. At the certified point,

$$ Q_i(b,T)=\Delta(b)^2 P_i(b)\cdot a. $$

The determinant is nonzero, so $Q_i$ has the same strict sign as the original score. The Lean declarations `cramer_eq_det_smul` and `sign_cramer` prove this identity and strict sign equivalence over the reals. The declarations `det_totalDegree_le`, `cramer_totalDegree_le`, and `certificateScore_totalDegree_le` in namespace `HeadComplexity.PartialLinearCapacity` prove the polynomial degree calculation. The declaration `exists_certificate_pattern` proves the complete chart cover, including arbitrary coefficient scaling, selected labels, and the extra box variable.

There are $q+1$ free real parameters. Applying Warren with degree $2LD+1$ gives the count for each fixed certificate. Sum over the discrete certificates from Lemma 2. $\blacksquare$

## Application to original denominators of small affine dimension

Normalize the original admissible denominators at the zero input, so each is $B_h(x)=1+b_h\cdot x$. This normalization preserves positivity on the entire Boolean cube, and does not constrain the original numerators or signed output coefficients.

Suppose the slope vectors lie in an affine subspace of dimension at most $d$. Allow the subspace itself to vary. Write

$$ b_h=b_0+\sum_{j=1}^d t_{hj}c_j. $$

There are $q=n(d+1)+dH$ nonlinear parameters. Every $B_h(x)$ is a polynomial of degree at most two in these parameters. After the exact numerator normalization from `NormalizedCounting.lean`, use $L=nH+1$ unrestricted linear numerator and bias coefficients. Clearing the positive denominators gives feature polynomials of degree at most $D=2H$.

The preceding theorem gives the explicit bound

$$ 2^{nH+1}{N+2nH+2\choose nH+1}\left(\frac{4e(4H(nH+1)+1)N}{n(d+1)+dH+1}\right)^{n(d+1)+dH+1},\qquad N=2^n. $$

It is valid whenever $n(d+1)+dH+1\leq N$. An overparameterization by $b_0,c_j,t_{hj}$ causes no difficulty: every permitted original representation lies in the counted family. Allowing all signs of these parameters enlarges the family and therefore also causes no difficulty for the upper count. Positivity is used only to transfer signs when clearing the original denominators.

For $1\leq d\leq n$ and $n\leq H\leq N/(2n)$, taking logarithms and using the standard binomial estimate gives

$$ \log_2|\mathcal F_d(n,H)|=O\left(nH\log\frac{eN}{nH}+ndH+n^2d\right). $$

The constants are absolute. The logarithm of the Warren base is $O(n)$ because $H\leq N$ and $d\geq1$. The discrete certificate term is $O(nH\log(eN/(nH)))$.

Consequently, for sufficiently small fixed constants $c$ and $c'$, the count is less than $2^{N/2}$ at either of the following scales, for all sufficiently large $n$:

- $H\leq cN/n^{3/2}$ and $d\leq c'\sqrt n$.

- $H\leq cN\log n/n^2$ and $d\leq c'n/\log n$.

These are unconditional counts for the specified denominator subclasses, with no margin hypothesis. They do not assert that every truth table represented at width $H$ belongs to either subclass.

## The remaining inequality

For the unrestricted model one must allow $d=n$. The last estimate then contains $n^2H$. At width $H=cN/n^{3/2}$ this is $cN\sqrt n$, and at width $H=cN\log n/n^2$ it is $cN\log n$. Neither is below $N$ for any fixed positive $c$ once $n$ is large.

Thus this route needs either a theorem replacing the nonlinear parameter cost $O(ndH)$ by $o(n^2H)$ for all original denominator families, or a separate count showing that truth tables requiring full dimensional denominator families are sufficiently rare. A low dimensional representation for one chosen score is insufficient. The quantified statement must concern every truth table at the original width, allowing a new representation when needed.

## Scope of the row restriction

The certificate uses actual sample rows and fixed coordinate box rows. It does not require a bound on the number of parameter solutions to arbitrary linear observations of the entire feature table. One positive reciprocal head can have exponentially many parameter preimages under carefully chosen arbitrary linear observations, as investigated separately by the finite margin audit. That phenomenon does not contradict the certificate: many parameter preimages may realize the same truth table, and arbitrary dual observations are not the active constraints used here.
