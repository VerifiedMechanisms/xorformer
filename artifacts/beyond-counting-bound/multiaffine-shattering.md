# Multiaffinity Alone Does Not Remove the Logarithmic Loss

## Scope

This is an obstruction to a proposed counting argument, not a lower bound for attention heads. It proves that polynomial tests which are affine in each parameter separately can shatter a number of tests of order the parameter count times its logarithm. Consequently, the separate affinity of the cleared head equations does not by itself justify a linear VC bound.

The construction uses unrestricted polynomial coefficients. No claim is made that these particular tests are evaluations of the manuscript's head model.

## Statement

Let $p\geq2$, $m=\lfloor p/2\rfloor$, and let $q=2^b$ be a positive integer satisfying $q\leq p/(8\log p)$, where the logarithm is natural. There are $mb$ polynomials $P_{i,j}$ in $p$ real variables, each of degree at most one in each variable, such that every assignment of signs to these polynomials is attained at a permutation of $(1,\ldots,p)$.

Every attained value can be chosen to equal its prescribed sign exactly. In particular, for all sufficiently large $p$, the number of shattered tests is at least

$$ \left\lfloor\frac p2\right\rfloor\left\lfloor\log_2\left(\frac{p}{8\log p}\right)\right\rfloor=\Omega(p\log p). $$

## Proof

### Lemma 1. Independent color choices admit distinct representatives

There are maps $c_i:[p]\to[q]$, for $1\leq i\leq m$, such that for every choice $a_1,\ldots,a_m\in[q]$, the sets $c_i^{-1}(a_i)$ have pairwise distinct representatives.

**Proof.** Choose all values $c_i(r)$ independently and uniformly from $[q]$. A failure of the required property has, by Hall's marriage theorem, a witness consisting of a set $T\subseteq[p]$ of size $t\lt m$, a set $I\subseteq[m]$ of size $t+1$, and colors $a_i$ for $i\in I$, with

$$ c_i^{-1}(a_i)\subseteq T\qquad(i\in I). $$

Indeed, if a collection of chosen color classes has union of size $t$ smaller than the number of its classes, retain any $t+1$ of those classes. For a fixed witness, its probability is

$$ (1-1/q)^{(p-t)(t+1)}\leq\exp\left(-\frac{(p-t)(t+1)}q\right)\leq p^{-4(t+1)}. $$

The last inequality follows from $p-t\geq p/2$ and $p/q\geq8\log p$. Summing over the choices gives a failure probability at most

$$ \begin{aligned} \sum_{t=0}^{m-1}\binom pt\binom m{t+1}q^{t+1}p^{-4(t+1)}&\leq\sum_{t=0}^{m-1}p^{-t-2}\cr&\leq\frac1{p(p-1)}\lt1.\end{aligned} $$

Here we used $q\leq p$ and the elementary bounds on the binomial coefficients. Thus a suitable collection of maps exists. One finite construction is to enumerate all collections lexicographically and retain the first satisfying the stated Hall conditions. $\blacksquare$

### Lemma 2. Reading one permutation entry with multiaffine polynomials

Fix $i\in[p]$. Every function $v:[p]\to\mathbb R$ has a multiaffine polynomial $P$ in the variables other than $z_i$ such that

$$ P(z_1,\ldots,z_p)=v(z_i) $$

whenever $(z_1,\ldots,z_p)$ is a permutation of $(1,\ldots,p)$.

**Proof.** Use the explicit polynomial

$$ P(z)=\sum_{r=1}^p v(r)\frac{\prod_{j\neq i}(r-z_j)}{\prod_{s\neq r}(r-s)}. $$

All denominators are fixed nonzero integers. Each summand is affine in each variable separately and does not depend on $z_i$. If $z_i=r$, the numerator and denominator in the corresponding summand are equal. If $z_i\neq r$, some other position $j\neq i$ contains $r$, so that summand's numerator is zero. Thus precisely the summand with $r=z_i$ remains, giving $P(z)=v(z_i)$. $\blacksquare$

### Completion of the construction

Identify the $q=2^b$ colors with all sign vectors of length $b$. Apply Lemma 2 to each of the $b$ bits of each color map $c_i$ from Lemma 1. This gives $mb$ fixed multiaffine polynomials $P_{i,j}$.

Given any signs for these polynomials, interpret the $b$ signs at each $i$ as a desired color $a_i$. Lemma 1 supplies distinct values $r_i\in c_i^{-1}(a_i)$. Set $z_i=r_i$ for $i\leq m$, and fill the remaining positions with the unused elements of $[p]$. The result is a permutation, and Lemma 2 gives exactly the prescribed signs. $\blacksquare$

## An explicit finite-field construction

The probabilistic step can also be replaced by a finite-field construction, with a smaller absolute constant. Let $q=2^s\geq4$, put $p=q^3$, and identify the $p$ labels with the points of $\mathbb F_q^3$. There are $D=q^2+q+1$ directions of nonzero linear forms, up to nonzero scalar multiplication. For each direction choose the representative whose first nonzero coordinate is one, and use its $q$ fibers as a color partition.

Repeat every such partition $r=q/2-1$ times. This gives

$$ m=rD=\frac{q^3-q^2-q-2}{2}\lt\frac p2 $$

color maps. These maps have the distinct-representative property of Lemma 1.

**Proof.** Every color class is an affine plane with $q^2$ points. Two distinct affine planes intersect in at most $q$ points. A set $T$ with at most $p/2$ points cannot contain $q+1$ distinct affine planes, since the first two terms of inclusion-exclusion would give

$$ |T|\geq(q+1)q^2-\binom{q+1}{2}q=\frac{q^3+q^2}{2}\gt\frac p2. $$

Now fix $T$ of size $t\lt m$. If $t\lt q^2$, it contains no color class. Otherwise it contains at most $q$ distinct planes. Since each plane occurs in exactly $r$ of the repeated partitions, at most $rq\lt q^2\leq t$ of the color maps can have any color class contained in $T$. A Hall obstruction would require $t+1$ such maps, so none exists. $\blacksquare$

Apply Lemma 2 after fixing any bijection between $\mathbb F_q^3$ and $[p]$. This explicitly constructs $ms$ shattered multiaffine tests in $p$ parameters, with

$$ ms=\left(\frac16-o(1)\right)p\log_2p. $$

The tests are given by the finite product interpolation formula in Lemma 2, without a search for color maps. For example, $q=8$ gives $p=512$, $D=73$, $r=3$, and $m=219$, hence $657$ independent sign tests in $512$ parameters. All labels are attained at positive integer permutations, so restricting the parameter domain to the positive orthant does not repair the proposed generic linear bound.

## Formalization and finite checks

`formalization/HeadComplexity/Results/MultiaffinePermutation.lean` proves the product interpolation identity, the degree bound in every variable, Hall selection from the stated small-set condition, and positive-parameter shattering conditional on that condition. The main declarations are `decoder_eval_permutation`, `decoder_degreeOf_le_one`, `exists_color_representatives`, and `exists_positive_multiaffine_shattering`, all in the namespace `HeadComplexity.MultiaffinePermutation`. The axiom audit in `multiaffine-axioms.txt` reports only `propext`, `Classical.choice`, and `Quot.sound`.

The probabilistic estimate, finite-field verification of the Hall condition for general field size, and asymptotic statements above are written proofs, not Lean declarations. The independent exact script `verify_finite_field_matchings.py` checks the field arithmetic, plane sizes and intersections, integer Hall estimates, and selected matchings for field sizes four and eight. Those finite examples supplement the general proof; checking selected matchings alone would not establish the Hall condition.

## Tensor interpretation and literature check

A multiaffine polynomial is a linear functional of the rank-one tensor

$$ (1,z_1)\otimes\cdots\otimes(1,z_p). $$

Thus the construction also proves an $\Omega(p\log p)$ VC lower bound for linear classification by rank-one tensors of order $p$ and mode size two, when the input tensors are arbitrary. It concerns classification on tensor inputs, not tensor completion or classification restricted to rank-one input tensors.

[Khavari and Rabusseau's 2021 paper](https://proceedings.neurips.cc/paper/2021/file/5a9d8bf5b7a4b35f3110dde8673bdda2-Paper.pdf) gives a general tensor-network counting bound and, for rank-one tensors, a linear lower bound and an upper bound with a logarithmic order factor. The argument above is self-contained; no novelty claim relative to later tensor-network work is made.

## Audit against the intended application

For the head model, the cleared test at a cube point is

$$ P_x=\sigma\prod_h B_h(x)+\sum_h A_h(x)\prod_{g\neq h}B_g(x). $$

This expression is affine separately in the parameter block of each head, and hence in every scalar parameter. The theorem shows that this fact alone cannot remove a logarithmic factor from a general sign-counting bound. It does not rule out a bound exploiting the special coefficient structure, positivity of the denominators, or the Boolean evaluation points. No such stronger bound is established here.
