# Coordinate monotonicity does not remove abstract block entropy

## Statement and scope

The abstract family in [block_convex_permutation_entropy.md](block_convex_permutation_entropy.md) can also have globally coordinatewise nondecreasing rational scores on the positive parameter orthant, while retaining its full permutation entropy. Each score can be strictly positive and uniformly bounded between one half and three halves, with threshold one.

For $H=2^k$ with $k\geq1$ and $n\geq1$, there are $P=nH$ positive real parameters in $H$ complete blocks of dimension $n$, and $M=Pk$ rational scores such that:

- Each score is nondecreasing in every parameter throughout the positive orthant.

- Each score lies strictly between $1/2$ and $3/2$ throughout that orthant.

- After positive denominator clearing, each threshold predicate is multiaffine and is affine in each complete parameter block separately. Its degree is at most $H$.

- Every strict sign cell has convex fibers in each complete parameter block.

- The scores realize at least $(H!)^n$ different strict threshold tables, at explicit positive rational parameter points.

These are written abstract statements, not original xorformer constructions or Lean declarations. In particular, positivity, parameter monotonicity, bounded values, and complete-block convexity alone do not imply the desired entropy reduction. The special reciprocal-sum form and the common Boolean evaluation rows remain essential.

## Monotonization on a compact box

Retain the previous predicates $F_{i,j,b}$, which use only coordinate group $z_{1,j},\ldots,z_{H,j}$ and read bit $b$ of the root assigned to position $i$ at each permutation of $1,\ldots,H$. Write $T=H+1$ and $C=H(H+1)/2$. All witness coordinates lie in the interior of $[0,T]$.

Each first partial derivative of every $F_{i,j,b}$ is bounded on $[0,T]^P$. Choose a common constant $A\gt0$ large enough that

$$ A+\frac{\partial F_{i,j,b}}{\partial z_{h,j}}(z)\geq1 $$

for all rows, all $h$, and all points of the box. Set

$$ \widetilde F_{i,j,b}(z)=F_{i,j,b}(z)+A\left(\sum_{h=1}^H z_{h,j}-C\right). $$

This remains affine in every entire head block. Its partial derivatives in group $j$ are at least one, and its derivatives in all other groups are zero. At every permutation witness the added term vanishes, so all previously encoded signs are exactly unchanged.

The derivative bound can be made explicit and rational. In the previous notation $F_{i,j,b}=\sum_{r=0}^{H-1}c_{b,r}e_r(z_{\neq i,j})$, it suffices to choose

$$ A=1+\max_b\sum_{r=1}^{H-1}|c_{b,r}|\binom{H-2}{r-1}T^{r-1}. $$

For $h\neq i$, differentiating $e_r$ removes that variable and leaves $e_{r-1}$ in $H-2$ variables; for $h=i$ the original derivative is zero. Each elementary symmetric summand is nonnegative on the box, and its size is bounded by the corresponding binomial coefficient times the power of $T$. Thus the displayed formula proves the claimed derivative inequality directly.

## Global positive-orthant scores

For every parameter put

$$ z_{h,j}=\frac{Tt_{h,j}}{1+t_{h,j}},\qquad t_{h,j}\gt0. $$

This maps the positive orthant coordinatewise into the interior of the box and is strictly increasing in each coordinate. Define

$$ R_{i,j,b}(t)=\widetilde F_{i,j,b}(z(t)). $$

The chain rule gives nonnegative partial derivatives everywhere on the positive orthant, strictly positive for coordinates in the row's own group. All witness roots remain available: a root value $z_{h,j}=s\in\lbrace1,\ldots,H\rbrace$ is realized by the positive rational value $t_{h,j}=s/(T-s)$. Consequently all permutation tables survive on interior positive parameter points, with strict values exactly $+1$ or $-1$ for $R$.

To impose bounded positive score values as well, choose a finite $L$ bounding the absolute values of all $\widetilde F$ on the box and put

$$ \lambda=\frac1{2(L+1)},\qquad G_{i,j,b}(t)=1+\lambda R_{i,j,b}(t). $$

One may take

$$ L=\max_b\sum_{r=0}^{H-1}|c_{b,r}|\binom{H-1}{r}T^r+AC. $$

Indeed, the sum of the group coordinates ranges from zero to $HT=2C$. Hence $|\sum_hz_{h,j}-C|\leq C$. This $L$ is nonnegative and rational, and it follows that $1/2\lt G\lt3/2$ everywhere. The score remains coordinatewise nondecreasing, while its threshold-one labels at permutation witnesses are precisely the old labels.

## Denominator clearing and full-block fibers

For a row in group $j$, clear only its own positive denominator

$$ D_j(t)=\prod_{h=1}^H(1+t_{h,j}). $$

Then $D_j(G_{i,j,b}-1)$ is a multiaffine polynomial of degree at most $H$. To see this, any monomial $\prod_{h\in I}z_{h,j}$ of the original multiaffine predicate becomes, after clearing,

$$ T^{|I|}\prod_{h\in I}t_{h,j}\prod_{h\notin I}(1+t_{h,j}). $$

Every factor uses at most one variable from each complete block. Fixing all blocks except block $h$, a strict threshold condition is therefore an affine open halfspace in that complete block. Intersecting all such halfspaces with the positive orthant gives a convex fiber. The rational score and the cleared polynomial have identical strict signs because $D_j\gt0$.

Two distinctions are necessary. Clearing a row by a product over all $nH$ parameters would introduce products of different coordinates within one block and would not preserve the asserted full-block affinity. Also, monotonicity belongs to the rational score $G$, not necessarily to its cleared numerator: multiplication by a positive variable factor preserves signs but need not preserve derivative signs.

## Entropy and the precise failed implication

Every sign table in the previous permutation construction is retained. Thus the full family has at least $(H!)^n$ tables, with logarithmic cardinality of order $nH\log H$. Keeping only $r\leq k$ bits per position retains at least

$$ 2^{nHr-n2^r\log_2(H+1)} $$

tables on $nHr$ rows. As established in the preceding note, at either critical width $H\asymp2^n/n^{3/2}$ or $H\asymp2^n\log n/n^2$, taking $r=\lfloor2^n/(nH)\rfloor$ gives $2^{2^n-o(2^n)}$ tables on at most $2^n$ rows. Duplicating rows reaches exactly $2^n$ without decreasing the count or changing any property above.

The failed generic claim is that these abstract hypotheses force a count with only $O(P\log(M/P))$ entropy, or force a half-table bound at either target scale. The construction does not preserve the genuine original evaluation formula $b+\sum_h A_h(x)/B_h(x)$ across a common Boolean cube. It therefore neither refutes an original-model repair theorem nor establishes the original conjecture. It identifies a necessary extra ingredient for any argument based on the positive normal form: parameter monotonicity and block convexity must be supplemented by a property of the actual shared Boolean rows or the reciprocal-sum structure.
