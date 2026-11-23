# Parity separates attention heads from priority sums

## Statement

For a Boolean vector $x$, write $\chi(x)=(-1)^{\sum_i x_i}$. A literal conjunction is the indicator of a subcube, including the constant conjunction. Suppose a real score is a sum of $m$ real multiples of literal conjunctions and has the strict sign $\chi$ at every vertex. Then

$$ 3^n \leq m 2^n. $$

This lower bound is classical: Basu, Bhatnagar, Gopalan, and Lipton prove it as Theorem 6.5 of [Polynomials that Sign Represent Parity and Descartes' Rule of Signs](https://arxiv.org/pdf/math/0702773). The proof below counts faces directly.

Consequently, if an arbitrary affine score plus a sum of $H$ real-valued coordinate priority lists strictly sign-represents parity, then

$$ 3^n \leq (nH+n+1)2^n. $$

Here a priority list tests literals in order, returns an arbitrary real output at the first successful test, and otherwise returns an arbitrary real default. Both orientations and arbitrary mixed literals are allowed. Repeated tests do not improve this bound: after a coordinate has been tested, its value is known on the continuing branch, so subsequent tests on that coordinate are either redundant or terminate that branch. Pruning them leaves at most $n$ tests.

In the manuscript's attention model, parity has head complexity exactly $n$. Thus a conversion from arbitrary attention representations to such priority sums cannot have a number of lists bounded by any fixed polynomial in the input dimension and the original number of heads, even with a free affine term. This is a compiler obstruction, not the requested worst-case lower bound for attention.

## Face-counting proof

A face specifies each coordinate as fixed to zero, fixed to one, or free. There are $3^n$ faces, including the vertices. For each face $F$, define

$$ A_F(P)=\sum_{x\in F}\chi(x)P(x). $$

Every summand is strictly positive when $P$ sign-represents parity. Hence $A_F(P)\gt 0$ for every face, including zero-dimensional faces.

Consider one conjunction $C$. If a free coordinate of $F$ is absent from $C$, pair each vertex with the vertex obtained by flipping that coordinate. Their contributions cancel. If a fixed coordinate of $F$ contradicts a literal of $C$, every contribution is zero. Conversely, if neither obstruction occurs, precisely one vertex of $F$ satisfies $C$, so $A_F(C)$ is either $1$ or $-1$.

For each coordinate absent from $C$, a contributing face must fix it to zero or to one. For each coordinate present in $C$, a contributing face must either fix it to the required value or leave it free. Thus each conjunction has a nonzero alternating sum on exactly $2^n$ faces, independently of its width.

For $P=\sum_{j=1}^m c_j C_j$, every face must have $A_F(C_j)\neq 0$ for at least one $j$, since otherwise $A_F(P)=0$. Counting these covering incidences proves $3^n\leq m2^n$. The argument permits arbitrary real coefficients, repeated conjunctions, cancellations, and arbitrarily small positive margins. $\blacksquare$

## Priority-list expansion

Let a pruned list contain $r\leq n$ literal tests $\ell_1,\ldots,\ell_r$, with corresponding outputs $a_1,\ldots,a_r$ and default $a_{r+1}$. Each $\ell_j(x)$ is zero or one. Its value is exactly

$$ L(x)=a_1+\sum_{k=1}^r(a_{k+1}-a_k)\prod_{j=1}^k(1-\ell_j(x)). $$

If the first successful test has index $t$, the prefix products are one for $k\lt t$ and zero for $k\geq t$. The expression telescopes to $a_t$. If no test succeeds, all products are one and it telescopes to $a_{r+1}$. The empty list is simply its default.

Every nonzero prefix product is a literal conjunction. Constants from all lists and the affine score combine into one constant conjunction. The affine part contributes at most $n$ singleton conjunctions. Thus the entire score has at most $nH+n+1$ conjunction terms, which proves the stated inequality.

The manuscript's convention permits nonpositive scores on one label. This does not evade the obstruction. On a finite cube, subtract a sufficiently small positive constant from any score that is positive on its positive label and nonpositive on the other label. This makes both signs strict while preserving every label and changes only the already allowed affine constant. Reversing all coefficients handles either parity orientation.

## Audit and scope

`formalization/HeadComplexity/Results/SubcubeConjunctionCover.lean` formalizes the complete face-counting argument. The main declaration is `HeadComplexity.SubcubeConjunctionCover.parity_conjunction_count`. It constructs a surjection from a conjunction index paired with a Boolean code onto all faces. Each code specifies one of the two allowed face states in every coordinate.

The priority-list expansion and pruning argument are proved above. They are not claimed as Lean declarations. The existing exact attention result is `HeadComplexity.HStar_parity`. The source theorem about conjunctions is credited to the literature; no novelty is claimed for its lower bound.

This closes the proposed polynomial-size priority-list compilation mechanism. It does not constrain a head directly: a rational head can have nonzero alternating sums on every face. No inequality stronger than the manuscript's worst-case lower bound follows from this result.
