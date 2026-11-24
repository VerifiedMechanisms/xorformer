# A Finite Local Obstruction to Four Vanilla Heads

## Statement

Read Boolean outputs as signs. Use seventeen sign coordinates $(t,x,y)$, where $t\in\lbrace-1,1\rbrace$ and $x,y\in\lbrace-1,1\rbrace^8$. Interleave the sixteen nonspecial coordinates as $x_0,y_0,x_1,y_1,\ldots,x_7,y_7$. Let $z_0$ be their all-negative corner. Let $z_i$ denote a single-coordinate flip of $z_0$, and let $z_{ij}$ denote a two-coordinate flip.

Prescribe a label $b(z)$ on the following $101$ points:

- $b(z_0)=-1$.
- $b(z_i)=1$ for all sixteen coordinates.
- $b(z_{x_i,y_j})=-1$ whenever $i\neq j$.
- $b(z_{y_i,y_j})=-1$ whenever $i\neq j$.

Extend these prescriptions by $b(-z)=b(z)$. Suppose a Boolean function $f$ has the labels $f(t,z)=t b(z)$ at both selector values and all these points. No labels elsewhere are prescribed. There are $404$ distinct prescribed inputs.

Then, in the unchanged original xorformer model,

$$ H_V(f)\geq5. $$

This is an obstruction against every vanilla-admissible representation with four heads, including arbitrary real parameters, unrestricted finite width, all denominator orientations, and constant denominators. It is not a pure rotary upper bound or a counterexample by itself.

## Proof

### Lemma 1. A selector projection retains four oriented factors

By the exact affine-fraction normal form, a four-head score is a sum of four admissible affine fractions and a constant. Write its positive denominators and arbitrary numerators as

$$ D_h=d_h+e_ht+B_h(z),\qquad N_h=n_h+a_ht+U_h(z), $$

where $B_h,U_h$ are homogeneous linear forms on the sixteen nonspecial coordinates. The slopes of each $B_h$ are all strictly positive, all strictly negative, or all zero. Clear the four positive denominators to obtain

$$ P(t,z)=c\prod_{h=0}^{3}D_h(t,z)+\sum_{h=0}^{3}N_h(t,z)\prod_{j\neq h}D_j(t,z). $$

Define

$$ Q(z)=\frac{P(1,z)-P(-1,z)+P(1,-z)-P(-1,-z)}4. $$

This selector-odd, globally even projection is quadratic. Its nonconstant monomials come from cubic terms of $P$. Every such monomial has at least one denominator direction as a factor. Consequently

$$ Q(z)=q+\sum_{h=0}^{3}A_h(z)B_h(z) $$

for homogeneous linear forms $A_h$. This identity holds for arbitrary affine data, without assuming that $f$ has any global symmetry. An exact coefficient formula and the complete quartic expansion are checked in `FourHeadSelectorQuadratic.extracted_eq`.

If a denominator direction has negative slopes, replace both $A_h$ and $B_h$ by their negatives. Hence every $B_h$ has strictly positive slopes or is zero.

At any prescribed point with $b(z)=1$, the first and third terms defining $Q$ are strictly positive, while the second and fourth terms are nonpositive. Thus $Q(z)\gt0$. The reverse labels give $Q(z)\lt0$. This remains valid when the original score is zero at a false label.

### Lemma 2. The local quadratic labels force an invertible cross matrix

Let $C$ be the eight-by-eight matrix of mixed coefficients between $x$ and $y$ in $Q$. A cross face away from a matched pair has negative labels at its diagonal corners and positive labels at its off-diagonal corners. Its four-point difference gives

$$ C_{ij}\lt0\qquad(i\neq j). $$

Write $p_0=Q(z_0)$, $p_j=Q(z_{y_j})$, and $p_{jk}=Q(z_{y_j,y_k})$. Direct expansion of an even quadratic gives

$$ 4\sum_iC_{ij}=5p_j-5p_0+\sum_{k\neq j}(p_k-p_{jk}). $$

Every term has the required strict sign, so each column sum of $C$ is positive. Thus $M=C^\top$ has nonpositive off-diagonal entries and positive row sums. The maximum principle used in [Theorem 17](017_pure_rope_twelve_bit_obstruction.md) proves that $M$ is invertible and that the solution to $Mu=w$ is strictly positive whenever $w$ is strictly positive.

### Lemma 3. Four positive factors cannot supply eight cross directions

Let $A,V,D,W$ be the eight-by-four matrices of the coefficients of the left and right factors on the two coordinate blocks. Lemma 1 gives

$$ C=AW^\top+VD^\top, $$

where each column of $V$ and $W$ is strictly positive or zero. Since $C$ is invertible, both square concatenations $(A\ V)$ and $(W\ D)$ are invertible. In particular no column of $V$ or $W$ is zero. The factorization implies

$$ V^\top M^{-1}W=0. $$

Every entry of the left side is strictly positive: each column of $W$ is strictly positive, $M^{-1}$ maps it to a strictly positive vector, and each column of $V$ is strictly positive. This contradiction excludes four heads. Padding with zero heads excludes every smaller budget. $\blacksquare$

## Formalization and scope

- [PositiveHalfRankCross.lean](../../formalization/HeadComplexity/Polynomial/PositiveHalfRankCross.lean): `PositiveHalfRankCross.obstruction` proves Lemma 3 for arbitrary even matrix size, including zero directions.
- [FourHeadSelectorQuadratic.lean](../../formalization/HeadComplexity/Polynomial/FourHeadSelectorQuadratic.lean): `cleared_eq`, `extracted_eq`, and `firstFactor_linear` prove the exact algebraic projection.
- [FourHeadLocalQuadratic.lean](../../formalization/HeadComplexity/Polynomial/FourHeadLocalQuadratic.lean): `LocalPattern` and `quadratic_obstruction` define and analyze the first finite pattern.
- [FourHeadLocalPattern.lean](../../formalization/HeadComplexity/Results/FourHeadLocalPattern.lean): `not_computable_four`, `HStar_ge_five`, and `SharedHStar_ge_five` state the lower bound for the existing scalar and shared-embedding models.

The scalar-to-architecture step uses the repository's existing exact affine-fraction equivalence, so this lower bound applies to all original-model architectures of the stated head count.

## A variant using only cross coefficients

The first pattern also forces every off-diagonal coefficient within the $y$ block to be negative. A stronger Gram-matrix obstruction rules out the intended pure four-head construction for that pattern. The following variant removes this condition while retaining the all-vanilla lower bound.

Keep the corner, singleton, and off-matching cross-pair prescriptions. Replace the within the $y$ block pair prescriptions by these middle-layer witnesses. For each $j$, choose a background $v_j$ on the other seven $y$ coordinates:

- For $j=0$, set coordinates $1,2,3$ positive and $4,5,6,7$ negative.
- For $j\neq0$, set coordinate $0$ and the two smallest elements of $\lbrace1,\ldots,7\rbrace\setminus\lbrace j\rbrace$ positive; set the other background coordinates negative.

Let $z(j,s,a)$ have every $x$ coordinate negative, $y_j=a$, and $y_k=s v_{jk}$ for $k\neq j$. Prescribe

$$ b(z(j,s,a))=-a\qquad(s,a\in\lbrace-1,1\rbrace). $$

Extend by global complementation and both selector values as before. The $32$ listed middle witnesses comprise $18$ distinct points, with consistent labels. The complete pattern contains $364$ distinct seventeen-bit inputs.

For every even quadratic $Q$, the new exact identity is

$$ Q(z(j,1,1))-Q(z(j,1,-1))+Q(z(j,-1,1))-Q(z(j,-1,-1))=-4\sum_iC_{ij}. $$

The prescribed labels make the left side negative, so every cross-column sum is positive. The rest of the proof is unchanged. Thus this second pattern also implies $H_V(f)\geq5$, without requiring signs on the within-block coefficients.

The pattern is consistent. Set $w_0=11/10$ and $w_j=1$ for $j\neq0$, and let $J$ be the all-ones matrix. The quadratic

$$ Q_0(x,y)=\frac{48}{5}-\frac3{20}\left[\left(\sum_i x_i\right)^2+\left(\sum_i y_i\right)^2\right]+x^\top\left(\mathrm{diag}(w+8)-J\right)y $$

has every required local label. Moreover, for any real $\delta$, the perturbation $\delta(y_4-y_5)(y_6-y_7)$ vanishes at every prescribed point. A sufficiently positive $\delta$ therefore makes a within the $y$ block coefficient positive while retaining the entire pattern. This verifies that the second pattern does not impose the within-block sign condition used by the preceding Gram obstruction.

[FourHeadCrossOnlyPattern.lean](../../formalization/HeadComplexity/Results/FourHeadCrossOnlyPattern.lean) defines `middleInput` and `CrossOnlyPattern`, checks `middle_difference`, and proves `crossOnly_not_computable_four`, `crossOnly_HStar_ge_five`, and `crossOnly_SharedHStar_ge_five`. The independent [local-pattern verifier](../../artifacts/rope/prior_obstructions/verify_four_head_local_patterns.py) checks the point counts, the quadratic completion, and the vanishing perturbation exactly.

A pure four-head score meeting the second pattern would establish a strict separation, regardless of its labels at the remaining inputs. Constructing and certifying such a score remains a separate task.
