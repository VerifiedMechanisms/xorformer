# Weighted capacity of moderately sized local algebra clusters

## Status and scope

This is a written counting proof. Its weighted sign-count input is kernel checked as `HeadComplexity.weightedStrictPolynomialSignPatterns_card_le`. The uniform-length polynomial specialization, its filtered recurrence, positive clearing, and exact product-of-weights finite count are now kernel checked in `FilteredAlgebraCapacity.lean`, notably `HeadComplexity.FilteredAlgebraCapacity.card_represented_le` and `mem_represented_of_score`. Its parameter `q` counts nonidentity basis vectors, so its cluster length is `q + 1`. The inclusion of abstract filtered algebras, the nonuniform-length formula, the weight-product simplification, and the asymptotic estimates below remain written proofs. The margin-repair agent independently audited the complete parameter count, telescoping identity, and both asymptotic estimates, without finding a gap. It allows arbitrary real structure constants, affine coefficients, and signed cancellation. Every base denominator is positive on the full Boolean cube. No access theorem from unrestricted xorformers is asserted.

The point of the estimate is that a cubic number of structure coordinates is affordable *per moderately sized cluster*. It need not be affordable for one cluster whose length is the entire width. This differs from the inherited [global border-basis obstruction](../power-saving-20261124/staircase_charts_and_shape_degree.md), where a length $H$ algebra could introduce quadratically or cubically many coordinates in $H$.

## Local algebra coordinates

Let $A$ be a finite-dimensional, commutative, associative, unital local real algebra, with residue field $\mathbb R$, dimension $q\geq1$, and maximal ideal $\mathfrak m$. Its powers give a filtration

$$ A\supset\mathfrak m\supset\mathfrak m^2\supset\cdots\supset\mathfrak m^q=0. $$

Choose a basis $e_0=1,e_1,\ldots,e_{q-1}$ adapted to this filtration. For $i\geq1$, assign an order $k_i\in\lbrace1,\ldots,q-1\rbrace$, so the basis elements with order at least $a$ span $\mathfrak m^a$. Multiplication has the form

$$ e_i e_j=\sum_{\ell:k_\ell\geq k_i+k_j}c_{ij\ell}e_\ell\qquad(i,j\geq1). $$

There are at most $(q-1)^3$ displayed structure slots. No associativity, commutativity, smoothability, or rank equations will be used in the upper count. We count the larger family obtained by letting every permitted slot vary independently. In this larger family, define every power by a fixed left-associated recurrence. Products still vanish at the stated order because each multiplication increases filtration order. The finite geometric expression defines the comparison score even when the freely chosen multiplication is not associative.

For context, ordinary border-basis charts are genuine affine charts of the Hilbert scheme, and their generic coordinates include one coefficient for each border-to-basis reduction. The principal component admits explicit shape charts at radical points. Those qualitative parameterizations do not provide the weighted capacity estimate used here; see Kreuzer and Robbiano, [The Geometry of Border Bases](https://arxiv.org/pdf/1004.1044), Definition 2.1 and Sections 3 and 4. Our argument instead retains the redundant local structure coefficients and charges their complete cost.

## Finite score class

Put $N=2^n$ and $d=n+1$. Fix cluster dimensions $q_1,\ldots,q_G\geq1$ and filtration-order lists as above. Define

$$ K=\sum_gq_g,\qquad Q=\max_gq_g,\qquad s=\sum_g(q_g-1)^3,\qquad p=1+2dK+s. $$

At cluster $g$, choose arbitrary real affine forms $B_{g,0},B_{g,1},\ldots,B_{g,q_g-1}$ and $L_{g,0},\ldots,L_{g,q_g-1}$. Require only $B_{g,0}(x)\gt0$ on the full Boolean cube. Put

$$ U_g(x)=\sum_{i=1}^{q_g-1}B_{g,i}(x)e_i,\qquad B_g(x)=B_{g,0}(x)1+U_g(x). $$

Since $U_g^{q_g}=0$, its inverse is the finite expression

$$ B_g(x)^{-1}=\sum_{m=0}^{q_g-1}\frac{(-1)^mU_g(x)^m}{B_{g,0}(x)^{m+1}}. $$

Let $R_{g,i}(x)$ be its coordinate at $e_i$. Count the strict truth tables of

$$ S(x)=c+\sum_g\sum_{i=0}^{q_g-1}L_{g,i}(x)R_{g,i}(x). $$

This includes scores obtained by applying any fixed linear functional $\lambda_g$ to $A_g(x)B_g(x)^{-1}$, where $A_g$ is an arbitrary affine $A_g$-valued function: set $L_{g,i}(x)=\lambda_g(A_g(x)e_i)$. Freely choosing the affine $L_{g,i}$ only enlarges the class.

If $p\leq N$, the number of strict truth tables in this class is at most

$$ \left(\frac{12eN}{p}\right)^p Q^{2dK}K^{dG+s}. $$

The formula charges every structure slot, including slots whose coefficient is forced to zero by the filtration. Thus its parameter count is explicit and does not depend on a dimension calculation for an algebraic parameter space.

## Proof of the weighted estimate

Assign rational weights as follows. Every coefficient in one affine form receives the same weight:

$$ w(B_{g,0})=\frac1K,\qquad w(B_{g,i})=\frac{k_i}{q_g}+\frac1K,\qquad w(L_{g,i})=1-\frac{k_i}{q_g}\quad(i\geq1),\qquad w(L_{g,0})=w(c)=1. $$

A permitted structure slot receives

$$ w(c_{ij\ell})=\frac{k_\ell-k_i-k_j}{q_g}+\frac1K. $$

An unused slot receives weight $1/K$. Every weight is strictly positive and at most two.

### Telescoping through multiplication

For $m\geq1$, a monomial in the $e_\ell$ coordinate of $U_g^m$ contains $m$ affine input coefficients and $m-1$ structure coefficients. Its order differences telescope, giving the exact weight

$$ \frac{k_\ell}{q_g}+\frac{2m-1}{K}. $$

This follows directly by induction on $m$. Multiplying a coordinate at $e_j$ by an input coefficient at $e_i$ and a structure coefficient $c_{ij\ell}$ replaces $k_j/q_g$ by $k_\ell/q_g$ and adds two units of $1/K$. A nonzero term has $m\leq k_\ell\leq q_g-1$.

Multiply the score by the everywhere-positive quantity

$$ D(x)=\prod_gB_{g,0}(x)^{q_g}. $$

A nonconstant inverse term, after multiplication by its affine $L_{g,\ell}$ and by the clearing powers, has weight

$$ \begin{aligned} 1-\frac{k_\ell}{q_g}+\frac{k_\ell}{q_g}+\frac{2m-1}{K}+\frac{q_g-m-1}{K}+\frac{K-q_g}{K}&=2+\frac{m-2}{K}\cr &\leq3. \end{aligned} $$

The constant inverse coordinate has weight $2-1/K$, and the bias term has weight two. Every Boolean evaluation polynomial of the cleared score therefore has weighted degree at most three. The recurrence expansion is a polynomial in all the counted parameters; no inverse structure coefficients occur.

### Product of weights

All nonbase affine weights are at least $1/Q$, and every structure weight is at least $1/K$. The zero-index numerator weights equal one. Consequently

$$ \prod_{a=1}^p w_a\geq Q^{-2dK}K^{-(dG+s)}. $$

Multiply all rational weights and the degree bound by a common positive integer. The integer-weight theorem has the same degree-to-weight ratio, and gives

$$ T\leq\left(\frac{12eN}{p}\right)^p\frac1{\prod_aw_a}\leq\left(\frac{12eN}{p}\right)^pQ^{2dK}K^{dG+s}. $$

Positive clearing preserves every strict label. The count is valid without imposing the polynomial identities satisfied by an actual local algebra, because omitting those identities enlarges the parameter set. $\blacksquare$

## Two useful asymptotic regimes

Allow ordered lists of cluster lengths in an interval $q\leq q_g\leq2q$, all filtration-order lists, and total size at most $K_{\max}$. The empty list supplies constant scores. There are at most $2^{K_{\max}}(2q)^{K_{\max}}$ choices of compositions and order lists. This adds at most $K_{\max}\log(4q)$ to the logarithmic count.

For every sufficiently large $n$, the union has at most $2^{N/2}$ truth tables in either of these regimes:

1. $q=\lceil n^{1/3}\rceil$ and $K_{\max}\leq N/(1000n^{5/3})$.

2. $q=\lceil\log n\rceil$ and $K_{\max}\leq N\log n/(1000n^2)$.

**Estimate.** Write $c=1/1000$. In both regimes, $Q\leq2q$, $G\leq K/q$, $s\leq4q^2K$, and eventually $p\leq5nK\leq N$. The logarithm of the finite bound is

$$ p\log(12eN/p)+2dK\log Q+(dG+s)\log K. $$

The first two terms and the composition/order-list term are $o(N)$ in both regimes. Indeed, $p/N=O(n^{-2/3})$ in the first regime and $O(\log n/n)$ in the second, while $\log Q=O(\log n)$.

For the first regime, eventually $n^{1/3}\leq q\leq2n^{1/3}$, $d\leq2n$, and $\log K\leq n\log2$. Hence the remaining terms satisfy

$$ dG\log K\leq2cN\log2,\qquad s\log K\leq16cN\log2. $$

Their sum is $18cN\log2$, which is strictly below $N\log2/2$ with room for all $o(N)$ terms.

For the second regime, eventually $\log n\leq q\leq2\log n$. The corresponding bounds are

$$ dG\log K\leq2cN\log2,\qquad s\log K\leq16cN\log2\frac{(\log n)^3}{n}=o(N). $$

Again the total is strictly below $N\log2/2$ for every sufficiently large $n$. The empty score class adds only two tables and is absorbed by the same strict eventual gap. $\blacksquare$

## The remaining access lemma

This count includes general local real algebras of moderate length, not only monomial quotients or one-parameter jets. It does not require an efficient border-basis parameterization.

To obtain an unrestricted theorem, one still needs a truth-table preserving decomposition into clusters in the indicated interval, with total length at most the stated budget, or an upper count for the tables excluded from such a decomposition. The relevant excluded class must contain every original-width table for which *every* comparable-width representation fails the good-margin condition.

An arbitrary large local algebra cannot simply be divided into small algebras: higher powers in its reciprocal may connect many filtration levels, and the global score need not be the sum of reciprocals of the proposed pieces. Likewise, replacing a local algebra by a monomial initial algebra can alter strict labels. Neither operation is justified by this finite count.
