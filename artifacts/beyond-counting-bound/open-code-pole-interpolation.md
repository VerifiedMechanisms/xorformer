# Open Codes and Positive Reciprocal Jet Interpolation

## Statement and scope

The following auxiliary interpolation theorem is proved here. It does not assert a lower bound for attention-head complexity.

**Theorem.** Let $n\geq2$, let $N=2^n$, and let $m$ be the largest power of two at most $n/2$. There exist $q=N/m^2$ affine forms $B_1,\ldots,B_q$ with strictly positive rational constant terms and strictly positive rational slopes such that

$$ \mathrm{span}_{\mathbb R}\left\lbrace x\mapsto\frac{x_S}{B_h(x)^3}:1\leq h\leq q, S\subseteq\lbrace1,\ldots,n\rbrace, |S|\leq2\right\rbrace=\mathbb R^{\lbrace0,1\rbrace^n},\qquad x_S=\prod_{i\in S}x_i. $$

In particular, $q\lt16N/n^2$. When $n=2^{r+1}$, the construction has $q=4N/n^2$ exactly. The proof gives a finite rational algorithm for choosing the forms. No bound on the running time of that algorithm is claimed.

The positive forms can vary in every coefficient. This theorem does not settle the different question about a common binary slope vector and varying intercepts in `reciprocal-jet-ranks.md`.

## An open-neighborhood partition

Put $m=2^r$ and index a block's coordinates by the additive group $G=\mathbb F_2^r$, including its zero element. For a word $x\in\mathbb F_2^G$, define its syndrome and a code by

$$ s(x)=\sum_{g\in G}x_g g,\qquad C=\lbrace x:s(x)=0\rbrace. $$

Let $e_g$ be the word with its only nonzero coordinate at $g$. The map

$$ x\longmapsto\bigl(x+e_{s(x)},s(x)\bigr) $$

is a bijection from $\mathbb F_2^G$ to $C\times G$. Indeed, its first component has syndrome $s(x)+s(x)=0$, and its inverse is $(c,g)\mapsto c+e_g$, whose syndrome is $g$. Consequently every word has exactly one codeword at Hamming distance one, and $|C|m=2^m$.

This is a perfect total dominating code, with open rather than closed neighborhoods. Total domination of hypercubes is treated in [Azarija, Henning, and Klavžar, “(Total) Domination in Prisms”](https://arxiv.org/abs/1606.08143). The explicit bijection above is the only coding fact needed in this proof.

Use two disjoint blocks of $m$ coordinates. Let the remaining $\ell=n-2m$ coordinates be unrestricted in the centers. Thus the center set is

$$ V=C\times C\times\lbrace0,1\rbrace^{\ell},\qquad |V|=\frac{2^n}{m^2}=q. $$

For every input $y$ there is a unique center $v(y)\in V$ and a unique pair of coordinates $i(y),j(y)$, one in each block, such that

$$ y=v(y)\mathbin{\oplus}e_{i(y)}\mathbin{\oplus}e_{j(y)}. $$

Each center therefore has a tile of $m^2$ inputs, and the tiles partition the entire cube. Unused coordinates agree with the center. The cardinality claim follows from the block bijection, without a covering estimate or a compatibility assumption.

## A quantitative pole witness

For each center $v$ and coordinate $k$, let $z_{vk}(x)=x_k$ if $v_k=0$ and let $z_{vk}(x)=1-x_k$ if $v_k=1$. Define

$$ d_v(x)=\sum_{k=1}^n z_{vk}(x),\qquad E_y(x)=z_{v(y),i(y)}(x)z_{v(y),j(y)}(x),\qquad a_y(x)=2-d_{v(y)}(x). $$

The function $E_y$ is a squarefree polynomial of degree at most two. At every cube vertex its value is zero or one. At $x=y$ one has $a_y(y)=0$ and $E_y(y)=1$. If $x\neq y$ and $a_y(x)=0$, then $E_y(x)=0$: otherwise $x$ differs from $v(y)$ in both selected coordinates and, since its distance is two, in no other coordinate, forcing $x=y$.

Set $\varepsilon=1/(4N)$ and form the square matrix

$$ K_{x,y}=\frac{\varepsilon^3 E_y(x)}{\bigl(\varepsilon+a_y(x)\bigr)^3}. $$

Every denominator is nonzero because $a_y(x)$ is an integer and $0\lt\varepsilon\lt1$. Each diagonal entry is one. An off-diagonal entry vanishes if $a_y(x)=0$. Otherwise $|a_y(x)|\geq1$ and $\varepsilon\leq1/2$, so

$$ |K_{x,y}|\leq8\varepsilon^3,\qquad \sum_{y\neq x}|K_{x,y}|\leq8(N-1)\varepsilon^3\lt\frac{1}{8N^2}\lt1. $$

Thus $K$ is strictly diagonally dominant and nonsingular. One direct proof is to assume $Ku=0$ for a nonzero vector, choose $x$ with maximal $|u_x|$, and obtain

$$ |u_x|=\left|\sum_{y\neq x}K_{x,y}u_y\right|\leq\left(\sum_{y\neq x}|K_{x,y}|\right)|u_x|\lt|u_x|, $$

a contradiction. This is an explicit rational witness. No limiting determinant or unproved genericity assertion is being used.

## Transfer to strictly positive coefficients

The preceding witness has mixed denominator slopes. It is used only to certify that a polynomial is nonzero. Define affine forms depending on one real parameter by

$$ D(x)=1+\sum_{k=1}^n x_k,\qquad B_v(t,x)=(1-t)D(x)+t\bigl(\varepsilon+2-d_v(x)\bigr). $$

Writing $|v|$ for the Hamming weight of the center gives the coefficients explicitly:

$$ B_v(t,x)=1+t(\varepsilon+1-|v|)+\sum_{k=1}^n\bigl(1-2t(1-v_k)\bigr)x_k. $$

If $0\lt t\lt1/(n+3)$, each slope is either one or $1-2t\gt0$. The constant term is positive because $|v|\leq n$ and

$$ 1+t(\varepsilon+1-|v|)\geq1-tn+t(\varepsilon+1)\gt1-\frac{n}{n+3}\gt0. $$

Consider the rational matrix $M_{x,y}(t)=E_y(x)/B _{v(y)}(t,x)^3$. For each row, clear all center denominators by $R _x(t)=\prod _{v\in V}B _v(t,x)^3$. The resulting polynomial matrix is

$$ A(t)_{x,y}=E_y(x)\prod_{v\in V\setminus\lbrace v(y)\rbrace}B_v(t,x)^3,\qquad P(t)=\det A(t). $$

Every entry has degree at most $3(q-1)$, so $P$ has degree at most $D_0=3N(q-1)$. At $t=1$, every cleared denominator is nonzero and $M(1)=\varepsilon^{-3}K$. Hence $P(1)\neq0$, and $P$ is a nonzero rational polynomial.

There are $D_0+1$ distinct rational grid points

$$ t_j=\frac{j}{(D_0+2)(n+3)},\qquad 1\leq j\leq D_0+1. $$

Each lies strictly between zero and $1/(n+3)$. A nonzero polynomial of degree at most $D_0$ has at most $D_0$ distinct roots. Choose the first grid point with $P(t_j)\neq0$. This finite selection is well defined. At this point, every $B_v$ has strictly positive rational coefficients, every $R_x$ is positive, and $M(t_j)$ is nonsingular.

Each column of $M(t_j)$ is a linear combination of the stated degree-at-most-two numerator columns belonging to its center. These columns therefore span all $N$ functions on the cube. Finally, maximality of $m$ gives $m\leq n/2\lt2m$, hence $q=N/m^2\lt16N/n^2$. For $n=2^{r+1}$ one has $m=n/2$ and $q=4N/n^2$. This proves the theorem. $\blacksquare$

## Relation to jets and to actual heads

For a positive affine form $B=b_0+\sum_i b_i x_i$, the value, first derivatives, and second derivatives of $B\mapsto1/B(x)$ have entries proportional to $1/B$, $x_i/B^2$, and $x_i x_j/B^3$, when the constant coefficient is included among the differentiable parameters by setting $x_0=1$. Therefore the theorem is a full-span statement for second-order reciprocal jets at $q$ positive parameter points.

It does not identify an arbitrary second-order jet with a head. An actual head has an affine numerator over one affine denominator. A linear combination of all second derivatives has a general quadratic numerator over a cubed denominator. Its quadratically many coefficients are independent interpolation variables here, whereas they are not independent parameters of one actual head. Approximating derivatives by finite differences also costs heads and does not remove that distinction.

The counting or realization argument that would connect this interpolation theorem to the selected lower-bound target is absent. This route remains blocked at that gap. In particular, this theorem proves neither an upper bound of order $2^n/n^2$ for $W(n)$ nor a refutation of such an upper bound.

## Formal audit boundary

`formalization/HeadComplexity/Atoms/OpenCodePartition.lean` proves the syndrome identities, the unique open-code encoding, and the exact block and product cardinalities. `FiniteFlipIsolation.lean` proves the Boolean isolation and two-literal product identities. `PoleIsolation.lean` proves the integer separation estimate and quantitative nonsingularity, including the explicit perturbation. `PolynomialPositiveGrid.lean` proves finite grid root avoidance, positivity of the homotopy coefficients, and the determinant degree estimate. `PositiveRationalTransfer.lean` proves the polynomial clearing identity and transfers nonsingularity into the positive interval.

`formalization/HeadComplexity/Results/PositivePairCover.lean` assembles the positive affine matrix theorem from a selected two-flip cover. `OpenCodeJetInterpolation.lean` instantiates that cover with the explicit codes. Its declarations `HeadComplexity.OpenCodeJetInterpolation.exists_positive_full_rank` and `HeadComplexity.OpenCodeJetInterpolation.exists_positive_interpolation` give the end-to-end real interpolation theorem for $n=2^{r+1}$. The declaration `center_budget` proves $q n^2=4\cdot2^n$ exactly, and `selectedNumerator_product` identifies every selected numerator as a product of two literals.

The extension by unused coordinates and the rational-coefficient refinement are the written proofs above. The finite root-avoidance argument is formalized over the reals; rationality follows in the written proof from the displayed rational grid and coefficient formulas. The exact attention-head model and the definition of $W(n)$ have not been changed.

The independent script `verify_open_code_poles.py` checks the complete finite isolation conditions and a nonzero determinant modulo 65521 for every dimension from two through eight. The selected positive grid index is one in all seven cases. At dimension eight the matrix has size 256, there are 16 centers, and its determinant modulo 65521 is 63420. All rational denominators used in these modular checks are invertible modulo the prime. The records are in `open-code-pole-checks.json`; they check instances of the construction and are not used to infer its general validity.
