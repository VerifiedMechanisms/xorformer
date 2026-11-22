# Code-Supported Functions Do Not Witness the Requested Refutation

## Statement

Let $A$ be a binary matrix of rank $r$ with $r$ rows and $n$ columns, let $s\in\mathbb F_2^r$, and put $C=\lbrace x\in\lbrace0,1\rbrace^n:Ax=s\rbrace$. Let $\ell_j$ be the weight of row $j$ of $A$. If a Boolean function $f$ vanishes outside $C$, then the manuscript's exact model satisfies

$$ H^{\ast}(f)\leq W(n-r)+\sum_{j=1}^r\ell_j\leq W(n-r)+nr. $$

Consequently, for Hamming lengths $n=2^r-1$, every Boolean function supported on a coset of the binary Hamming code satisfies

$$ H^{\ast}(f)\leq(1+o(1))\frac{2^n}{n^2}. $$

This upper bound applies to arbitrary subsets of the code, including random subsets. It rules out that candidate class for proving that $n^2W(n)/2^n$ is unbounded. It does not establish a universal upper bound for arbitrary Boolean functions.

## Exact parity penalties

First fix an integer $\ell\geq1$ and any table $v:\lbrace0,1,\ldots,\ell\rbrace\to\mathbb R$. Define

$$ D(t)=\prod_{a=1}^{\ell}(t+a),\qquad P(t)=\sum_{q=0}^{\ell}v(q)D(q)\prod_{\substack{0\leq a\leq\ell\cr a\neq q}}\frac{t-a}{q-a}. $$

Then $\deg P\leq\ell$ and $P(q)/D(q)=v(q)$ for every integer $0\leq q\leq\ell$. Polynomial division and partial fractions give the explicit identity

$$ \frac{P(t)}{D(t)}=c+\sum_{a=1}^{\ell}\frac{\lambda_a}{t+a},\qquad \lambda_a=\frac{P(-a)}{\prod_{\substack{1\leq b\leq\ell\cr b\neq a}}(b-a)}, $$

where $c$ is the coefficient of $t^{\ell}$ in $P$. To verify the identity, subtract the right side and clear $D$: the leading coefficients agree, and evaluation at the $\ell$ distinct numbers $-1,\ldots,-\ell$ gives zero. The resulting polynomial of degree at most $\ell-1$ is therefore zero.

For row $j$ of $A$, let $t_j(x)$ be the ordinary integer sum of the selected bits. Set $v_j(q)=0$ when $q\bmod2=s_j$, and $v_j(q)=1$ otherwise. The preceding formula represents the exact violation indicator $v_j(t_j(x))$ by a constant and $\ell_j$ affine-ratio terms. Their denominators have positive constant coefficients and nonnegative slopes. Zero slopes will be handled after the final strict score is constructed.

Thus

$$ V(x)=\sum_{j=1}^r v_j(t_j(x)) $$

has a representation with at most $\sum_j\ell_j$ such terms, satisfies $V(x)=0$ on $C$, and satisfies $V(x)\geq1$ outside $C$.

## Information coordinates and the final score

Choose $r$ pivot columns of $A$ forming an invertible matrix $A_P$, and let $I$ be the other $n-r$ coordinate positions. For every assignment $y$ to $I$, there is exactly one codeword in $C$ with that assignment, because its pivot coordinates are

$$ x_P=A_P^{-1}(s-A_Iy)\quad\text{over }\mathbb F_2. $$

Define $g(y)$ to be $f$ on that unique completion. Choose a strict rational score $G(y)$ for $g$ using at most $W(n-r)$ heads. Such strictification is part of the manuscript's normal-form argument. Extend it to all $n$ input coordinates by ignoring the pivot bits.

Let $M=1+\max_y|G(y)|$ and define

$$ S(x)=G(x_I)-MV(x). $$

On $C$ this is $G(x_I)$, so it has the required strict sign. Outside $C$ it satisfies

$$ S(x)\leq |G(x_I)|-M\lt0. $$

Thus $S$ strictly represents $f$ and uses no more than $W(n-r)+\sum_j\ell_j$ rational terms, before removing the zero denominator slopes.

## Admissibility in the exact architecture

The denominators in the lifted score for $G$ are positive on the full cube and have either nonnegative slopes or nonpositive slopes. A positive-oriented denominator can be perturbed by adding $\varepsilon\sum_i x_i$; a negative-oriented one can be perturbed by subtracting this quantity. A constant denominator is perturbed in the positive direction. For sufficiently small $\varepsilon\gt0$, every denominator remains positive at every cube vertex, and all its slopes have one common strict sign.

Apply the same positive perturbation to the parity-penalty denominators. Keep all numerators and the overall bias fixed. Because the cube and the number of heads are finite, the perturbed scores converge uniformly to $S$ as $\varepsilon\to0$. The strict score $S$ has a positive minimum absolute value on the cube. Therefore sufficiently small perturbations preserve every sign. The manuscript's normal form now realizes all the perturbed terms by the original attention architecture, without increasing the head count. This proves the theorem. $\blacksquare$

## Hamming-code consequence

For $n=2^r-1$, take the columns of $A$ to be all nonzero vectors of $\mathbb F_2^r$. The matrix has rank $r$ and each row has weight $2^{r-1}=(n+1)/2$. These are the standard parity checks in [Hamming's original construction](https://doi.org/10.1002/j.1538-7305.1950.tb00463.x). The dimension and row weights also follow directly from this displayed matrix description.

Writing $m=n-r$, the manuscript's universal upper bound gives

$$ \begin{aligned} H^{\ast}(f)&\leq W(m)+\frac{r(n+1)}2\cr &\leq(1+o(1))\frac{2^{n-r}}{n-r}+\frac{r(n+1)}2\cr &=(1+o(1))\frac{2^n}{n^2}. \end{aligned} $$

Here $2^r=n+1$, $r=\log_2(n+1)$, and the polynomial penalty cost is negligible compared with $2^n/n^2$. This implication is unconditional within the manuscript's model and uses its proved universal upper bound in the smaller input dimension. It does not impose restrictions on the real parameters or embedding dimensions.

The construction is a written proof and has not been formalized in Lean. Its role in this research is to reject a proposed hard family, not to mark the original objective complete.
