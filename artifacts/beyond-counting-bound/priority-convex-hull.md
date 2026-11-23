# The Exact Convex Hull of Bounded Heads

## Statement

Let $n\geq1$, and let $\mathcal A_n$ be the tables of all admissible affine-ratio heads on the Boolean cube with maximum absolute value at most one. Include the constant-denominator case. A positive coordinate priority function chooses an ordering of the $n$ coordinates, returns a prescribed sign at the first coordinate whose input is one, and returns a prescribed default sign if all inputs are zero. A negative coordinate priority function applies such a rule to the complemented input. Let $\mathcal D_n$ be the finite set of both kinds of sign tables.

**Theorem 1.** Every bounded head is exactly a convex combination of elements of $\mathcal D_n$, and

$$ \overline{\mathrm{conv}(\mathcal A_n)}=\mathrm{conv}(\mathcal D_n),\qquad |\mathcal D_n|\leq2^{n+2}n!. $$

This is a statement about the closed convex hull, not equality of the original head family with that polytope. In fact, for every $n$, a single strictly positive admissible head can require $2^n+1$ priority tables in any convex decomposition. Thus the theorem does not provide a head-count-preserving compiler. Both assertions are proved below.

## A finite elimination identity

First use positive denominator slopes. Write $D=1+\sum_i b_ix_i$, with $b_i\geq0$. The [numerator-polytope decomposition](amplitude-polytope-maximum.md) writes any bounded affine ratio as

$$ F(x)=\frac{k(x)+\sum_i b_ic_ix_i}{1+\sum_i b_ix_i},\qquad |c_i|\leq1,\qquad |k(x)|\leq1, $$

where $k$ is affine. More explicitly, take $p_i=(a_i-b_i) _+$, $m_i=(-a_i-b_i) _+$, and $d_i=\min(b_i,\max(-b_i,a_i))$. Set $c_i=d_i/b_i$ when $b_i\gt0$ and zero otherwise, and $k(x)=a_0+\sum_i(p_i-m_i)x_i$. The two amplitude budgets show that $k$ is a convex combination of constants and signed coordinate literals. The displayed identity holds also when a slope is zero, since then $d_i=0$.

For any subset $S$ of coordinates, define

$$ F_S(x)=\frac{k(x)+\sum_{i\in S}b_ic_ix_i}{1+\sum_{i\in S}b_ix_i},\qquad W_S=1+\sum_{i\in S}b_i. $$

Let $G_{j,c}(g)$ return $c$ when $x_j=1$ and $g(x)$ otherwise. The following is an exact identity of whole tables:

$$ F_S=\frac1{W_S}k+\sum_{j\in S}\frac{b_j}{W_S}G_{j,c_j}(F_{S\setminus\lbrace j\rbrace}). $$

**Proof.** Fix an input. If $x_j=0$, removing $j$ changes neither the numerator nor denominator, so the gated term equals $F_S(x)$. If $x_j=1$, it equals $c_j$. The numerator of the right side, before division by $W_S$, is therefore

$$ k(x)+\sum_{j\in S:x_j=1}b_jc_j+\sum_{j\in S:x_j=0}b_jF_S(x)=W_SF_S(x). $$

The last equality is just the defining fraction for $F_S$. All combination weights are nonnegative and sum to one. $\blacksquare$

This gives a finite recursive construction. It is the same sampling rule as choosing the next item with probability proportional to its weight, with an always-available item of weight one whose output is $k$. The familiar ranking distribution is the [Plackett-Luce model](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/plackett.pdf). No probabilistic representation theorem is needed here: the elimination identity proves the construction algebraically.

## Proof of the convex-hull equality

Let $P_+$ be the convex hull of positive coordinate priority functions. It contains constants and signed literals, and hence every affine $k$ with amplitude at most one. It is closed under $G_{j,c}$ for every $c\in[-1,1]$.

To check closure first for $c=\pm1$ on a priority function, move coordinate $j$ to the beginning of its order, overwrite its output by $c$, and remove its old occurrence. If $x_j=0$, deleting the old occurrence changes no output; if $x_j=1$, the new first entry supplies $c$. Thus the result is another priority function. For a convex combination of priority functions the same conclusion follows because the gate, with its constant output fixed, is affine in its table argument. Finally

$$ G_{j,c}(g)=\frac{1+c}{2}G_{j,1}(g)+\frac{1-c}{2}G_{j,-1}(g). $$

The elimination identity and induction on $|S|$ now show that every $F_S$ belongs to $P_+$, starting with $F_\varnothing=k$. This proves the asserted inclusion for nonnegative slopes, without a limiting argument or a bound on denominator conditioning.

Conversely, fix a full priority order $\pi$, coordinate outputs $c_i\in\lbrace-1,1\rbrace$, and default $c_0$. For $t\gt1$ set

$$ b_{\pi(r)}=t^{n-r+1},\qquad A_t(x)=c_0+\sum_i c_ib_ix_i,\qquad F_t(x)=\frac{A_t(x)}{1+\sum_i b_ix_i}. $$

Every slope is strictly positive and $|F_t|\leq1$. At a nonzero input let $r$ be the position of its first active coordinate. The leading term has weight $t^{n-r+1}$; each lower weight and the constant term are at most one $t$-th of that weight. Hence the error from the priority output is at most $2n/t$. At the zero input it is exactly zero. Thus the entire table converges uniformly to the prescribed priority function. All such functions lie in the closure of the bounded head family.

Complementing every input coordinate converts any strictly negative coherent denominator into a positive one after division by its positive value at the all-one input. It preserves the amplitude and carries positive priority functions to negative ones. Constant denominators were already included. This proves both inclusions in the closed-convex-hull equality. There are at most $n!$ orders, $2^{n+1}$ output assignments, and two orientations, proving the count. $\blacksquare$

## The exact dual norm

For any real cube table $\mu$, the theorem gives

$$ \sup_{F\in\mathcal A_n}|\langle\mu,F\rangle|=\max_{d\in\mathcal D_n}|\langle\mu,d\rangle|. $$

There is a concrete formula for the positive orientation. For an order $\pi$, let $C_r$ be the cell where all earlier coordinates are zero and coordinate $\pi(r)$ is one. Maximizing the output signs independently gives

$$ \max_{d\in\mathcal D_n^+}\langle\mu,d\rangle=\max_\pi\left(|\mu(0)|+\sum_{r=1}^n\left|\sum_{x\in C_r}\mu(x)\right|\right). $$

The other orientation is obtained by complementing the input of $\mu$. In particular, for parity all cell sums vanish except the last cell; the default contributes one more unit. The supremum of the absolute parity correlation is exactly two. This recovers the previously proved amplitude bound and establishes sharpness of its one-head constant as a supremum.

For independent uniform random signs $f$, a direct finite union bound gives, with probability at least $1-\delta$,

$$ \sup_{F\in\mathcal A_n}\frac{|\langle f,F\rangle|}{2^n}\leq\sqrt{\frac{2\log(2^{n+3}n!/\delta)}{2^n}}. $$

Indeed, for each fixed sign table $d$, the exponential moment of $\langle f,d\rangle$ is $\cosh(t)^{2^n}\leq\exp(2^nt^2/2)$. Chernoff's argument bounds the two tails by $2\exp(-2^nr^2/2)$; use the displayed dictionary cardinality. By linearity this event controls the relative amplitude margin of every finite signed sum of heads, with arbitrary target-dependent denominators. It still does not bound their number.

## A single head can require the maximum convex support

Put $N=2^n$ and identify a cube vertex with its binary integer $s\in\lbrace0,\ldots,N-1\rbrace$. Consider the one-head curve

$$ F_t(x)=\frac{1}{(1+t)(1+t\sum_{i=0}^{n-1}2^ix_i)},\qquad t\gt0. $$

Its numerator is the positive constant $1/(1+t)$ and its denominator has strictly positive slopes. Its amplitude is less than one.

**Theorem 2.** Some positive integer $t$ gives a table $F_t$ that is not a convex combination of $N$ or fewer members of $\mathcal D_n$. It is a convex combination of $N+1$ members.

**Proof.** First the curve is not contained in any affine hyperplane of the $N$-dimensional table space. Suppose

$$ a+\sum_{s=0}^{N-1}\frac{a_s}{(1+t)(1+st)}=0 $$

identically for positive $t$. Multiply by $1+t$. The coefficient of the growing term as $t$ tends to infinity forces $a=0$, and then the limit forces $a_0=0$. The remaining simple fractions have distinct poles at $-1/s$ for $1\leq s\leq N-1$. Their residues force all remaining coefficients to be zero.

It follows from Theorem 1 that the priority dictionary has full affine span. Choose an affine basis for the span of any set of at most $N$ dictionary elements, and extend that basis to $N$ affinely independent dictionary elements. The hyperplane they span contains the original set, including when the original set was dependent. There are at most $\binom{M}{N}$ such hyperplanes, where $M=|\mathcal D_n|$. By the preceding argument none contains the entire curve. Multiplying a hyperplane equation along the curve by

$$ (1+t)\prod_{s=1}^{N-1}(1+st) $$

gives a nonzero polynomial of degree at most $N$. Each hyperplane therefore excludes at most $N$ positive integers. At least one of the first $N\binom{M}{N}+1$ positive integers avoids all the hyperplanes. Its table cannot lie in the affine span, and hence cannot lie in the convex hull, of any $N$ dictionary elements.

Theorem 1 places this table in the convex hull of the dictionary. For completeness, any convex representation in $\mathbb R^N$ with more than $N+1$ positive coefficients can be shortened: the augmented vectors $(1,d)$ are linearly dependent, so perturb the coefficients along a nonzero dependence until one first reaches zero. The weights still sum to one and represent the same table. Repeating terminates with at most $N+1$ entries. The lower bound just proved makes this number exactly $N+1$. $\blacksquare$

For $n=2$, the integer $t=1$ already works, giving the four table entries $1/2,1/4,1/6,1/8$. The combined dictionary has 14 distinct sign tables. Its 97 distinct hyperplanes spanned by four affinely independent dictionary points all have nonzero value at this table; the exact finite replay records the primitive integer normals and their evaluations. Thus even this one head needs five priority tables in a convex representation. Its Boolean labels are all positive, so this is expressly a statement about exact real tables, not a Boolean lower bound.

## What remains missing

The convex-hull equality is global and covers unrestricted signed numerators and both coherent denominator orientations. However, taking a convex hull discards the number of original heads. Theorem 2 quantifies this loss: one bounded head can already require the maximum possible convex support in the priority dictionary. Conversely, a short convex representation in that dictionary need not consist of admissible finite-parameter heads, since some dictionary tables are only boundary limits.

No argument here bounds the number of sign patterns in sums of a specified number of heads. Controlling that set before convexification remains a substantive gap. Neither the original unbounded lower-bound target nor the stronger matching-order target follows from this theorem.

## Verification scope

The general convex-hull equality, the dual formula, the finite union bound, and the arbitrary-dimension maximum-support construction have complete written proofs above. The companion exact-arithmetic program implements the recursive convex decomposition, checks every output against the finite dictionary, and verifies the two-bit hyperplane certificate. The Lean companion proves the finite elimination induction and closure of the convex hull of partial priority lists under bounded gates. Its theorem `HeadComplexity.PriorityConvexHull.ratio_mem_priorityHull` proves the normalized choice-table inclusion, assuming the bounded affine fallback already belongs to that hull. The scalar elimination, binary interpolation, and quantitative dominance estimates are also checked. The clipping bridge, complementary orientation, finite dictionary count, limiting equality, and maximum-support theorem retain their complete written proofs; they are not claimed as fully formalized Lean declarations.
