# Positive block-convex families can retain the full permutation entropy

## Statement and scope

Convex feasible fibers in every complete parameter block, even inside the positive orthant, do not by themselves remove the generic $nH\log H$ cost from a sign count. The construction below is an abstract multiaffine polynomial family. It is not a construction of original xorformer evaluations on the Boolean cube, and it gives no counterexample to the desired unrestricted capacity bound.

For each power of two $H=2^k$ and each integer $n\geq1$, there are $P=nH$ positive real parameters, arranged into $H$ blocks of dimension $n$, and $M=Pk$ polynomial evaluation predicates such that:

- Every predicate has degree at most $H-1$ and is affine in every entire parameter block separately.

- Every strict sign cell has a convex fiber when all but one complete parameter block are fixed.

- The predicates realize at least $(H!)^n$ distinct strict sign tables, already on a finite collection of positive integer parameter points.

In particular, the entropy is $\Theta(nH\log H)$. A hypothetical bound of the form $C^P(M/P)^P$, with absolute $C$, is false for this class: its logarithm is only $O(P\log\log H)$.

The theorem and its asymptotic consequences are written proofs. `verify_block_convex_permutation_entropy.py` supplies a separate exact finite certificate for $H=4,8$. No Lean verification of this abstract construction is claimed.

## Why block convexity is present in the original model

Fix the orientation of each nonconstant original denominator, and fix every head except one. Write the contribution of the other heads and the bias as $R(x)$. The remaining score is

$$ R(x)+\frac{A(x)}{B(x)},\qquad B(x)\gt0. $$

For a fixed target $F(x)\in\lbrace-1,+1\rbrace$, its strict sign constraint is equivalent to

$$ F(x)\bigl(A(x)+R(x)B(x)\bigr)\gt0. $$

This is an affine inequality in the full coefficient block of $A$ and $B$. The coherent positive-slope cone is convex; the coherent negative-slope cone with positivity on the whole cube is also convex. Thus, within each fixed nonconstant orientation stratum, the feasible fiber of a target is convex in every complete head block. The numerator coefficients are jointly convex when all denominators are fixed as well.

The abstract theorem below satisfies these same fiber properties. Consequently a proof using just these properties would be insufficient. It must use more of the reciprocal evaluation form or the Boolean sample rows.

## A multiaffine way to read a permutation

Start with one coordinate group of $H$ positive parameters $z_1,\ldots,z_H$. Let $E_s$ denote the elementary symmetric polynomial of degree $s$ evaluated on the fixed roots $1,\ldots,H$, with $E_0=1$.

For $0\leq r\leq H-1$, define the univariate polynomial

$$ R_r(t)=\sum_{s=0}^r(-t)^sE_{r-s}. $$

If $(z_1,\ldots,z_H)$ is a permutation of $(1,\ldots,H)$, then division of the elementary-symmetric generating function by $1+z_i u$ gives

$$ e_r(z_1,\ldots,\widehat z_i,\ldots,z_H)=R_r(z_i). $$

Here the hat means that the indicated variable is omitted. Equivalently, this identity follows inductively from $E_r=e_r(z_{\neq i})+z_i e_{r-1}(z_{\neq i})$.

The polynomial $R_r$ has degree exactly $r$ and leading coefficient $(-1)^r$. Thus $R_0,\ldots,R_{H-1}$ form a basis of the univariate polynomials of degree at most $H-1$.

For every bit position $b\in\lbrace0,\ldots,k-1\rbrace$, interpolate a polynomial $q_b$ of degree at most $H-1$ with

$$ q_b(j)=\begin{cases}+1&\text{if bit }b\text{ of }j-1\text{ is }1,\cr -1&\text{if that bit is }0,\end{cases}\qquad 1\leq j\leq H. $$

The interpolation nodes are distinct integers, so the coefficients can be chosen rational. Express $q_b=\sum_{r=0}^{H-1}c_{b,r}R_r$, and define

$$ F_{i,b}(z)=\sum_{r=0}^{H-1}c_{b,r}e_r(z_1,\ldots,\widehat z_i,\ldots,z_H). $$

Each $F_{i,b}$ is multiaffine and has degree at most $H-1$. At every permutation point it equals $q_b(z_i)\in\lbrace-1,+1\rbrace$. Therefore the $Hk$ signs recover every root assigned to every position, and hence recover the permutation itself. The $H!$ permutation points induce $H!$ different strict sign tables.

All parameter coordinates are positive integers. By continuity, each of these sign tables also occurs on an open neighborhood contained in the positive orthant. The result is not an artifact of parameters lying on a boundary or of zero evaluation predicates.

## Independent coordinate groups and full-block convexity

Now use variables $z_{h,j}$ with $1\leq h\leq H$ and $1\leq j\leq n$. The full block at index $h$ is $(z_{h,1},\ldots,z_{h,n})$. For each $j$, use an independent copy of the preceding construction, with predicates $F_{i,j,b}$ depending only on $z_{1,j},\ldots,z_{H,j}$.

Every predicate is affine in each full block: it uses at most the one variable $z_{h,j}$ from that block, and with degree at most one. Fixing every other block, each prescribed strict sign is an affine open halfspace in the remaining block. Intersecting these halfspaces with the positive orthant gives a convex fiber, possibly empty.

The independent coordinate groups realize $(H!)^n$ sign tables on $M=nHk$ predicates. Since

$$ \log_2(H!)=H\log_2H-O(H), $$

their total entropy is $P\log_2H-O(P)$. This is the same order as the problematic multihomogeneous degree contribution, even though every full-block fiber is convex and every parameter lies in the positive orthant.

## Almost all of the entropy persists with fewer predicates

Keep only $r\leq k$ selected bits per position, and set $q=2^r$. Each $r$-bit word belongs to exactly $H/q$ of the roots. The possible words across the $H$ positions are precisely the balanced words with this multiplicity. Thus one coordinate group has

$$ \frac{H!}{((H/q)!)^q} $$

distinct restricted sign tables. The balanced multinomial coefficient is maximal among all multinomial coefficients with $q$ categories and total $H$: moving one unit from a count at least two larger than another strictly increases the coefficient. There are at most $(H+1)^q$ possible count vectors, and the sum of their multinomial coefficients is $q^H$. It follows that

$$ \frac{H!}{((H/q)!)^q}\geq\frac{q^H}{(H+1)^q}. $$

For $n$ coordinate groups, the number of distinct strict tables on $M'=Pr=nHr$ predicates is therefore at least

$$ 2^{M'-n2^r\log_2(H+1)}. $$

This supplies a direct comparison at the disputed parameter scales. Let $N=2^n$, choose a power of two $H$ within a fixed factor of either $cN/n^{3/2}$ or $cN\log n/n^2$, and set $r=\lfloor N/(nH)\rfloor$. For every fixed $c\gt0$ and all sufficiently large $n$, one has $1\leq r\leq\log_2H$, $r=o(n)$, and $nH=o(N)$. Moreover,

$$ M'=N-O(nH)=N-o(N),\qquad n2^r\log_2(H+1)=o(N). $$

The abstract family consequently realizes at least $2^{N-o(N)}$ distinct strict sign tables on $M'\leq N$ predicates. If desired, duplicate predicates to obtain exactly $N$ rows without reducing the number of tables. In particular, positive parameters and full-block convexity alone cannot give the required $2^{N/2}$ upper count at either critical scale.

## Exact failed implication

The false generic implication is that positivity of the denominator-parameter domain and convex feasible fibers in every full head block force a sign count with only $O(nH\log(N/(nH)))$ entropy. The construction gives full-block convex positive families with $\Theta(nH\log H)$ entropy, and with $N-o(N)$ entropy at the two critical scales.

The missing special ingredient must constrain which multiaffine interactions can arise from the original predicates $\mathrm{sign}(b+\sum_h A_h(x)/B_h(x))$ as $x$ ranges over the Boolean cube. The elementary-symmetric bit predicates here have not been represented by those original evaluations. They must not be used as an unrestricted lower-margin counterexample or as evidence that the original $O(N/n^2)$ conjecture is true.

## Finite certificate

The companion script solves the elementary-symmetric interpolation systems over exact rational arithmetic, clears denominators to integer coefficients, and verifies every root value for $H=4,8$. For $H=4$ it additionally evaluates every one of the $24$ permutation points directly and checks that all $24$ strict tables are distinct. For $H=8$ the certificate checks all root values but does not enumerate all $40320$ permutation points; that count uses the written injectivity proof.

These computations are reproducible finite evidence for the formulas. The proof for arbitrary $H$ above is independent of the computation.
