# Unbounded Reciprocal Tests per Parameter

## Statement and scope

For every integer $s\geq1$, put $q=2^s$ and $P=2q^2$. There are

$$ M=\frac{q(q+1)}2s $$

fixed tests of the form

$$ F_j(\theta)=\sum_{i=1}^{P}\frac{r_{ji}}{\theta_i+p_{ji}},\qquad p_{ji}\gt0, $$

such that every assignment of signs to all tests occurs at strictly positive parameters. The residues are signed. All witnesses can have signed margins greater than $1/2$. Consequently the ratio $M/P=(1+1/q)s/4$ is unbounded.

This theorem concerns freely specified query coefficients. It disproves every uniform linear VC bound in the number of parameters for that relaxation. It is not a lower bound on the manuscript's worst-case head complexity. The independent query coefficients here do not satisfy the affine Boolean-table constraints with a small number of input bits.

## Independent choices by affine lines

Let $I=\mathbb F_q^2$, so $|I|=L=q^2$. Let $K$ consist of $q/2$ copies of each of the $q+1$ directions of affine lines. Thus $|K|=m=q(q+1)/2$. For $k\in K$, let $c_k:I\to\mathbb F_q$ be its direction's linear form. Fix a bijection from the field to the $s$-bit strings.

For every collection of desired colors $a_k$, there are distinct representatives $i_k\in I$ with $c_k(i_k)=a_k$. Here is the complete Hall argument. If a set $T\subset I$ has size less than $m$, and contains $t$ distinct affine lines, then $t\leq q$: any $q+1$ lines have union size at least $(q+1)q-\binom{q+1}2=m$. For $t\leq q$, the same two-term inclusion-exclusion estimate gives

$$ |T|\geq tq-\binom t2\geq\frac{t(q+1)}2\geq\frac{tq}2. $$

Each line occurs in $q/2$ copies of its direction. Hence at most $tq/2\leq|T|$ color classes from distinct members of $K$ can be contained in $T$. This rules out every Hall obstruction and proves the assertion.

Index the members of $K$ by $g=0,\ldots,m-1$. For each query $(g,b)$ and label $i\in I$, define $w_{gbi}$ to be $1$ or $-1$ according to bit $b$ of the encoded color $c_g(i)$.

## A reciprocal pair selects one level

Set $R=4L+1$. For $g\geq0$ and $a\geq0$, define

$$ D_g(a)=\frac{R^{2g+2}}{R^{2a+1}+R^{2g+2}}-\frac{R^{2g}}{R^{2a+1}+R^{2g}}. $$

The following bounds are uniform in all the indices:

$$ D_g(g)=1-\frac2{R+1},\qquad 0\leq D_g(a)\leq\frac1{R+1}\quad(a\neq g). $$

**Proof.** The displayed equality follows by dividing the two fractions by $R^{2g+1}$. Positivity follows because $p/(t+p)$ increases with $p$ for positive $t,p$. If $a\geq g+1$, then $R^{2a+1}/R^{2g+2}\geq R$, so the first fraction is at most $1/(R+1)$; subtracting the nonnegative second fraction preserves the bound. If $a\leq g-1$, then $R^{2a+1}/R^{2g}\leq1/R$. Thus the second fraction is at least $R/(R+1)$, while the first is at most one. This proves the remaining bound. $\blacksquare$

## The fixed queries and their witnesses

Use two positive parameters $\theta_{i,+},\theta_{i,-}$ for every $i\in I$. The fixed test for $(g,b)$ is

$$ F_{gb}(\theta)=\sum_{i\in I}w_{gbi}\left(\frac{R^{2g+2}}{\theta_{i,+}+R^{2g+2}}-\frac{R^{2g}}{\theta_{i,-}+R^{2g}}\right). $$

Each summand in the expansion is one of the required reciprocal terms, with positive pole. Given desired signs, interpret the $s$ signs for each $g$ as its desired color. Take the distinct Hall representatives $i_g$. Assign level $a_i=g$ if $i=i_g$ and assign level $m$ to every unused label. Set

$$ \theta_{i,+}=\theta_{i,-}=R^{2a_i+1}. $$

For query $(g,b)$, exactly one representative has level $g$. Its weight is the prescribed sign $\varepsilon_{gb}$. Every other label has a different level. Therefore

$$ \begin{aligned} \varepsilon_{gb}F_{gb}(\theta)&\geq D_g(g)-\sum_{i\neq i_g}D_g(a_i)\cr&\geq1-\frac{L+1}{R+1}\cr&=1-\frac{L+1}{4L+2}\gt\frac12.\end{aligned} $$

This proves all sign assignments with a uniform strict margin. The two parameters in each pair are equal only at the chosen witnesses; the query family itself imposes no equality restriction. $\blacksquare$

## Strictly positive residues also suffice

The same conclusion holds with strictly positive poles and residues, using $4q^2$ positive parameters instead of $2q^2$. Every test is then strictly decreasing in every coordinate and strictly convex. The number of tests divided by the parameter count is $(1+1/q)s/8$, still unbounded.

To prove this, use the identity, valid for $t,p\gt0$,

$$ \frac{p}{t+p}+\frac{p^{-1}}{t^{-1}+p^{-1}}=1. $$

Every term in the preceding construction has residue equal to its pole or its negative. Replace each old parameter $t_i$ by two independent positive parameters $z_{i,+},z_{i,-}$, with witnesses $z_{i,+}=t_i$ and $z_{i,-}=t_i^{-1}$. For a positive term retain $p/(z_{i,+}+p)$. For a negative term use $p^{-1}/(z_{i,-}+p^{-1})-1$. In either case add a term with pole one and residue $\delta=1/(8L+1)$ on the unused coordinate. All resulting residues and poles are strictly positive.

Each query has exactly $L$ negative original terms. The new test therefore has threshold $L$. Its value at every constructed witness is the old test plus a positive error bounded by

$$ 2L\delta=\frac{2L}{8L+1}\lt\frac14. $$

Thus all its prescribed signed margins exceed $1/4$. Its partial derivatives are $-r_i/(z_i+p_i)^2\lt0$, and its Hessian is diagonal with entries $2r_i/(z_i+p_i)^3\gt0$. These facts prove the monotonicity and strict convexity claims. The general positive-residue transformation and the resulting unbounded ratio are also kernel checked in Lean.

## Architecture boundary

The free queries can be embedded on singleton inputs of a Boolean cube with $M$ input coordinates. For term $i$, use denominator $\theta_i+\sum_j p_{ji}x_j$ and numerator $\sum_j r_{ji}x_j$. Every denominator has strictly positive constant and slopes. At singleton $e_j$ the score is exactly $F_j(\theta)$. This shows the obstruction is present in actual admissible heads when the input dimension is allowed to grow with the number of queries. It does not realize these query tables on a cube with only logarithmically many input coordinates, or shatter the full cube.

The prescribed poles depend geometrically on the group index. A small affine Boolean denominator cannot simply be substituted for that table. In particular, every positive affine subset sum is within a factor equal to the number of summands of its largest selected summand. This limits its widely separated multiplicative scales. No argument here controls representations with arbitrary cancellation at closely spaced scales. Treating that remaining control as automatic would leave a theorem-strength gap.

## Audit status

`ReciprocalLevelSelector.lean` proves the uniform selector inequalities. `ReciprocalMatchingShattering.lean` combines them with the existing finite-field Hall theorem, transports the result to finite index types, and proves `HeadComplexity.ReciprocalMatchingShattering.unbounded_tests_per_positive_parameter`. This general signed-residue theorem passes Lean with only the standard foundational axioms. `PositiveReciprocalCompletion.lean` proves the general inversion identity and its error bound. `PositiveReciprocalShattering.lean` proves the transformation and `HeadComplexity.PositiveReciprocalShattering.unbounded_positive_tests_per_parameter`, again using only the standard foundational axioms. The calculus interpretation is a written consequence of the strictly positive residues.

The independent exact verifier checks all eight assignments in the smallest field and 36 further color assignments over the four- and eight-element fields. It checks 1,454 selector inequalities and 1,624 signed-residue test values and another 1,624 independently expanded positive-residue test values. These finite checks supplement the general proof; they do not replace its Hall argument. The selected asymptotic head lower bound remains unproved.
