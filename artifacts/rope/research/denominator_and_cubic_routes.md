# Denominator and Cubic Route Audits

These notes record routes investigated after the unconditional two-head proof. They do not prove or refute universal head preservation. The proved comparison results are stated in Theorems 16, 17, and 21; the pure architectural bridge is Theorem 18.

## A common projective input shift can fail

In centered coordinates, a common projective substitution translates every normalized denominator direction by the same vector. This does not always orient even two pure denominators.

Take denominator directions $(r,0)$ and $(-r,0)$ with $1/2\leq r\lt1$. After a common shift $(a,b)$, their directions are $(a+r,b)$ and $(a-r,b)$. If both have strict uniform slope signs, their shared second coordinate forces the same orientation. For positive orientation, $a\gt r$ and $b\gt0$, contradicting positivity of the first denominator at $(-1,-1)$ because $1-(a+r)-b\lt0$. For negative orientation, $a\lt-r$ and $b\lt0$, contradicting positivity of the second denominator at $(1,1)$ because $1+(a-r)+b\lt0$.

The actual admissibility obstruction, including possible zero-slope cases, is Lean-checked in `Atoms/RoPEProjectiveObstruction.lean`. That file supplies genuine nondegenerate pure atoms with directions $(3/4,0)$ and $(-3/4,0)$. This rules out a particular common-shift construction. It is not a Boolean separation, and Theorem 16 still replaces those two heads by two vanilla heads using a different construction.

## The three-head even polynomial

For a centered score $T+\sum_{i=1}^3u_i/(1+b_i)$, clearing denominators gives $P=Q+O$, where the even part is

$$ Q=T+q,\qquad q=T(b_1b_2+b_1b_3+b_2b_3)+u_1(b_2+b_3)+u_2(b_1+b_3)+u_3(b_1+b_2), $$

and the odd part is

$$ O=T(b_1+b_2+b_3)+u_1+u_2+u_3+Tb_1b_2b_3+u_1b_2b_3+u_2b_1b_3+u_3b_1b_2. $$

Strictly equal signs of $P(x)$ and $P(-x)$ are equivalent to $|O(x)|\lt|Q(x)|$. All these identities and the domination equivalence are Lean-checked in `Atoms/RoPEThreeEven.lean`.

### The pencil identity changes at three heads

Consider $b_1+t u_1$ as a direction in the first numerator-denominator pencil. Under the translation

$$ (b_1,b_2,b_3)\mapsto(b_1-t,b_2+t,b_3+t),\qquad (u_1,u_2,u_3)\mapsto(u_1-(1-Tt),u_2+(1-Tt),u_3+(1-Tt)), $$

the quadratic $q$ changes by

$$ 2(b_1+t u_1)+(Tt^2-2t). $$

The last term vanishes exactly when $t=0$ or $Tt=2$. The corresponding two-head translation changes its quadratic only by $2(b_1+t u_1)$, for every $t$. This algebraic distinction explains why the null-pencil step from the two-head argument does not transfer automatically. It is not a three-head lower bound.

One can sometimes combine the three pure pencil directions to obtain a positive null direction for the dual quadratic. That only reorients an *even-part representation*. It does not control the new odd part. Scaling denominator directions toward zero generally makes the linear odd term grow unless an additional cancellation is proved. Thus positive null directions alone do not establish a three-head Boolean comparison.

The rigorous conclusion from the even polynomial is the four-head bound of Theorem 21. It follows directly from writing $q$ as three products and applying a finite difference compiler. No matrix-rank assumption is needed.

## Cubic representations modulo Boolean identities

For three heads, the cleared polynomial has the form

$$ P=N_1D_2D_3+N_2D_1D_3+N_3D_1D_2. $$

Changing a representation while keeping its polynomial exactly fixed is a restricted algebraic problem. Boolean equality allows additional freedom: in centered coordinates one may add any expression of the form

$$ \sum_i L_i(z)(z_i^2-1), $$

with affine $L_i$, without changing values on the cube. Therefore uniqueness of a continuous cubic factorization does not by itself exclude a different three-head Boolean representation.

The mixed cubic coefficients using three distinct coordinates are unchanged by these additions. Restricting those coefficients to three disjoint variable blocks produces trilinear tensors without repeated-coordinate terms. This offers a possible route to recovering denominator information, but it has not supplied a sign invariant. Even exact recovery from the partially specified cubic tensor would only concern equality of cleared polynomials, unless an additional argument controlled all alternative sign representations.

An elementary calculation shows why the first mixed-block test is insufficient. If the three denominator restrictions form bases on each of three blocks, the corresponding trilinear coefficient map from the three numerator restrictions has rank 23 in a 27-dimensional tensor space. Its four linear constraints include three diagonal entries. For a rank-one target with coefficient vectors $(0,a,b)$, $(c,0,d)$, and $(e,f,0)$, the remaining constraint is $ade+bcf=0$. Mixed signs in all three vectors are compatible with that equation. Thus this test alone does not rule out positive denominator directions. The calculation was an exploratory symbolic linear-algebra check, not a Lean theorem or a Boolean separation.

## The reciprocal subclass and singular limits

Pure atoms include query-only reciprocal terms, by setting both token values to zero. The unresolved three-head case therefore already includes

$$ S=c+\frac{a_1}{D_1}+\frac{a_2}{D_2}+\frac{a_3}{D_3},\qquad D_i\gt0. $$

Its cleared numerator is $cD_1D_2D_3+a_1D_2D_3+a_2D_1D_3+a_3D_1D_2$. When $c\neq0$ and the three denominator directions are independent, its highest homogeneous term is the product of three independent linear forms.

A simple common-denominator limiting construction has a restriction. For three fractions with denominators $F+\varepsilon B_i$ and numerators whose leading order is $\varepsilon^{-2}A_i$, cancellation of the first two orders requires $\sum_iA_i=0$ and, in the simplest constant-base case, $\sum_iA_iB_i=0$. The usual nondegenerate linear syzygy then gives a cubic proportional to

$$ (B_1-B_2)(B_1-B_3)(B_2-B_3). $$

Those three factors span at most two directions. This rules out that specific limiting ansatz for a generic product of three independent directions. General parameter paths, denominator clusters, and Boolean reductions have not been classified. No conclusion about all three-head vanilla classifiers follows.

## Why a continuous-domain obstruction does not finish the Boolean problem

A possible separation strategy is to replicate variables in blocks, making pure scores depend on block averages, and obtain dense grids in a fixed-dimensional box. Several unresolved steps remain.

- Vanilla parameters need not be equal within a block. Restricting to a prefix grid yields arbitrary cumulative coefficient functions, rather than affine functions of the block average.

- Averaging a cleared polynomial over within-block permutations preserves its signs, but can destroy the three-head algebraic form.

- Positive affine denominators can be normalized to have slope absolute sum below one. If every slope becomes small, product expectations nearly preserve affine-product structure. Heavy coordinates obstruct this simplification. Opposing denominators approaching $1+z_i$ and $1-z_i$ show that fixing a heavy coordinate can make one conditional denominator vanish in the limit.

- Numerator cancellation can make the ordinary aggregate polynomial much smaller than repeated-coordinate corrections. Normalizing after Boolean reduction can therefore leave a different limiting object from normalizing before reduction.

One possible replacement would prove that every bounded-degree sign representation of a dense block-average classifier becomes approximately block-symmetric before averaging. Irreducibility of a continuous limiting boundary might then force proportionality. Neither the required compactness statement nor its treatment of unbounded parameters has been proved here.

These gaps are substantive. The continuous cubic discussion supplies possible future routes, not a finite Boolean counterexample and not the requested universal equality.
