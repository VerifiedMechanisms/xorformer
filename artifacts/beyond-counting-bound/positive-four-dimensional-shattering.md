# Positive Reciprocal Shattering in Four Real Dimensions

## Statement and scope

For every integer $r\geq3$, set $H=2^{r-1}$ and $M=(r-1)2^{r-2}$. There exist $M$ distinct points $X_j\in\mathbb Q_{\gt0}^4$ such that every labeling of these points is represented, with signed margin greater than $1/4$, by

$$ S(X)=-\frac12+\sum_{h=1}^H\frac1{1+w_h\cdot X},\qquad w_h\in\mathbb Q_{\gt0}^4. $$

Thus the number of shattered points per head, and per real parameter in the unrestricted four-coordinate family, is unbounded. All numerators and all denominator coefficients are positive. The input dimension is fixed. This rules out a linear parameter-count bound based only on those properties.

These are real input points with many coordinate scales. They are not vertices of a four-dimensional Boolean cube. The theorem does not improve the manuscript's lower bound or change its architecture.

## A binary switching construction

The rectangle family below is the planar construction in [Mustafa, Theorem 10.12](https://lipn.univ-paris13.fr/~mustafa/Books/SCGSS/book-samplingincombinatorics.pdf). The lifted geometric method also appears in [Csikos, Kupavskii, and Mustafa, Proposition 5](https://www.jmlr.org/papers/volume20/18-719/18-719.pdf). Here is a direct verification of the needed incidence property.

For a binary prefix $a$ of length $i$, let $I(a)$ be its dyadic open interval in $(0,2^r)$, of length $2^{r-i}$. Use rectangles

$$ I(a0)\times I(b0),\qquad 1\leq i\leq r-1,\quad |a|=i-1,\quad |b|=r-i-1. $$

Assign an arbitrary bit $\sigma_i(a,b)$ to each rectangle, zero for selected rectangles. For each word $A$ of length $r-1$, compute $B$ from left to right by

$$ B_j=A_{r-j}\mathbin\oplus\sigma_{r-j}(A_1\cdots A_{r-j-1},B_1\cdots B_{j-1}),\qquad 1\leq j\leq r-1. $$

Take the $H$ points $(2\mathrm{val}(A)+1,2\mathrm{val}(B)+1)$. Fixing a level and prefixes $(a0,b0)$ gives a consistent equation exactly when its bit is zero. In that case the remaining letters of $A$ are uniquely recovered in increasing index order, using the known prefix of $B$. The recursion then recovers all of $B$. Hence every selected rectangle contains exactly one point and every unselected rectangle contains none. There are $2^{r-2}$ rectangles per level, giving the stated $M$.

All rectangle endpoints are even integers, whereas point coordinates are odd. Membership therefore has a coordinate gap of at least one, on either side of every boundary.

## A positive reciprocal compiler

Put $R=16H$. For the rectangle with endpoints $(a,b)\times(c,d)$, use the fixed positive rational query

$$ X=(R^a,R^{-b},R^c,R^{-d}). $$

For each point $(s,t)$ of its labeling's witness set, use one head with

$$ w=(R^{-s},R^s,R^{-t},R^t). $$

The scalar appearing in its denominator, apart from the constant one, is

$$ w\cdot X=R^{a-s}+R^{s-b}+R^{c-t}+R^{t-d}. $$

If the point is inside the rectangle, all four exponents are at most minus one. Consequently

$$ 0\lt w\cdot X\leq\frac4R\leq\frac14,\qquad \frac1{1+w\cdot X}\geq\frac45. $$

If the point is outside, at least one exponent is at least one. Positivity of all four terms gives

$$ w\cdot X\geq R=16H,\qquad 0\lt\frac1{1+w\cdot X}\lt\frac1{16H}. $$

A selected query has at least one inside head and every head is positive. Its score is at least $4/5-1/2=3/10\gt1/4$. An unselected query has only outside heads, so its score is less than $H/(16H)-1/2=-7/16\lt-1/4$. This proves the statement, including uniform strict margins and rational parameters. Distinct rectangles give distinct endpoint quadruples and therefore distinct queries. $\blacksquare$

The reciprocal compiler is independent of the switching construction: any finite box incidence family with the displayed coordinate gaps admits the same conversion. No cancellation is used.

## Audit and the Boolean boundary

`PositiveReciprocalBoxGap.lean` proves the inside and outside estimates and the general finite-sum margin theorem `HeadComplexity.PositiveReciprocalBoxGap.separated_box_sum`. The switching construction, its geometric encoding, and the full asymptotic consequence above are written proofs, not claimed as Lean declarations. The accompanying independent exact verifier checks the recursive incidence construction and every score it tests, using rational arithmetic.

For the rectangular construction, the score depends on a point through four geometric coordinates. The [separated-scale theorem](positive-subset-scales.md) limits the number of such scales available from one admissible affine Boolean denominator to at most $n+1$ when consecutive ratios exceed $n+1$. It therefore prevents the literal replacement of these geometric tables by small Boolean affine tables. It does not control arbitrary signed sums of admissible heads.

A possible sharper Boolean sign count must exploit that input constraint or another property absent here. The gap between such a count and this real-input counterexample remains unresolved. This auxiliary theorem is not completion of the selected worst-case head-complexity target.
