# Sparse directions forced by small Boolean collision identities

## Two positive denominator heads

Let $n\geq4$ and let

$$ B(x)=1+\sum_{i=1}^n b_i x_i,\qquad D(x)=1+\sum_{i=1}^n d_i x_i,\qquad b_i,d_i\gt0. $$

Suppose nonzero zero-constant affine forms $A(x)=\sum_i a_i x_i$ and $C(x)=\sum_i c_i x_i$ satisfy

$$ \frac{A(x)}{B(x)}+\frac{C(x)}{D(x)}=0\qquad(x\in\lbrace0,1\rbrace^n). $$

Then at least one of the following holds.

1. $B=D$.

2. There are a nonempty coordinate set $I$ of size at most two and a positive scalar $r\neq1$ such that

$$ D=rB+(r-1)\left(\sum_{i\in I}x_i-1\right). $$

3. The denominators agree outside a nonempty coordinate set $I$ of size at most two. If $I$ has two elements, the two nonzero differences $d_i-b_i$ sum to zero.

Each displayed alternative admits a nonzero affine-feature dependency. Thus this is an exact classification of two-head dependence in this positive, normalized chart.

### Proof by coefficients and rank

Evaluating the cleared identity at a singleton gives

$$ c_i=-r_i a_i,\qquad r_i=\frac{1+d_i}{1+b_i}. $$

The coefficient of every squarefree quadratic monomial vanishes, so for distinct $i,j$,

$$ a_i(d_j-r_i b_j)+a_j(d_i-r_j b_i)=0. $$

First suppose some $a_j=0$. Then also $c_j=0$. Put $I=\lbrace i:a_i\neq0\rbrace$. Since $b_j\gt0$, the equation with $i\in I$ and $j\notin I$ gives $r_i=d_j/b_j$. Therefore all active $r_i$ equal a common positive $r$, all inactive coordinates satisfy $d_j=rb_j$, and all active coordinates satisfy $d_i=rb_i+r-1$. Consequently $C=-rA$ and

$$ AD+CB=(r-1)A\left(\sum_{i\in I}x_i-1\right). $$

If $r=1$, the denominators agree. Otherwise evaluation at each active pair gives $a_i+a_j=0$. Three active coordinates would force every one of their coefficients to be zero. Thus $|I|\leq2$, giving alternative 2.

Now suppose every $a_i\neq0$. The homogeneous quadratic coefficient matrix of $AD+CB$ is

$$ Q=\frac{ad^\top+da^\top+cb^\top+bc^\top}{2}. $$

The gradient of $AD+CB$ vanishes at the cube center because every quadratic vanishing on the cube is a linear combination of $x_i^2-x_i$. Hence the four vectors in the displayed factorization satisfy

$$ D(\tfrac12\mathbf1)a+A(\tfrac12\mathbf1)d+B(\tfrac12\mathbf1)c+C(\tfrac12\mathbf1)b=0. $$

Since $D(\tfrac12\mathbf1)\gt0$, their span has dimension at most three. Thus $Q$ has rank at most three. Its off-diagonal entries vanish, and

$$ Q_{ii}=\frac{a_i(d_i-b_i)}{1+b_i}. $$

Since $n\geq4$, at least one coordinate has $b_j=d_j$. If all do, alternative 1 holds. Otherwise the off-diagonal equations with an agreeing coordinate and a differing coordinate show that there is one nonzero $k$ such that

$$ a_j=kb_j\quad(b_j=d_j),\qquad a_i=k(1+b_i)\quad(b_i\neq d_i). $$

Let $I=\lbrace i:b_i\neq d_i\rbrace$ and $s=\sum_{i\in I}x_i$. Then

$$ A=k(B-1+s),\qquad C=-k(D-1+s),\qquad AD+CB=k(s-1)(D-B). $$

Each differing pair therefore satisfies $(d_i-b_i)+(d_j-b_j)=0$. Three differing coordinates would force their differences to vanish. Thus $|I|\leq2$, with the stated sum condition when $|I|=2$.

For the converse in alternative 2, take $A=x_i$ for a singleton or $A=x_i-x_j$ for a pair, and take $C=-rA$. In alternative 3, take $A=B-1+s$ and $C=-(D-1+s)$. The displayed products vanish on the Boolean cube in both cases. All denominator slopes remain strictly positive by the hypotheses, so every constructed affine-ratio head is admissible. $\blacksquare$

## The dimension threshold is sharp

In three coordinates, take

$$ B=1+x_0+x_1+3x_2,\qquad D=1+3x_0+4x_1+7x_2,\qquad A=x_0-4x_1-x_2,\qquad C=-2x_0+10x_1+2x_2. $$

Direct expansion gives

$$ AD+CB=(x_0^2-x_0)-6(x_1^2-x_1)-(x_2^2-x_2). $$

All three numerator coefficients are nonzero, all three denominator slopes differ, and the quadratic matrix has rank three. The denominators do not satisfy any of the classified alternatives. Thus the rank-three bound and the dimension threshold four are both sharp.

## Opposite orientations cannot cancel in pairs

Suppose instead that $b_i\gt0\gt d_i$, with $1+d_i\gt0$, and $n\geq3$. In the singleton equations above, every $r_i$ is positive. In the pair equations, both coefficients $d_j-r_i b_j$ and $d_i-r_j b_i$ are negative. A zero numerator coefficient forces all the others to be zero. If none is zero, each pair must have opposite signs, which is impossible on three coordinates.

Therefore two heads with opposite coherent denominator orientations have normalized affine-feature spaces intersecting only at zero. Before removing constant terms, their intersection consists only of constant functions. This statement allows arbitrary signed numerator coefficients; it uses the original coherent denominator orientation.

## A general multilinear core

Let $v_1,\ldots,v_n$ span a vector space $E$. Suppose deleting any at most $d-1$ columns still leaves a spanning family. If a $d$-linear form $T$ vanishes on every tuple of distinct columns, then $T=0$. Symmetry is unnecessary.

**Proof.** Induct on $d$. For $d=1$, use spanning. For larger $d$, fix one column $v_i$ in the first slot. The remaining columns are robust after deletion of at most $d-2$ further columns, so induction makes the resulting $(d-1)$-linear form zero. Finally the original columns span the first slot. $\blacksquare$

For a real polynomial $P$ of degree at most $d$, suppose $P$ vanishes on all subset sums $\sum_i x_i v_i$ with Boolean $x$. Taking finite differences along $d$ distinct columns shows that its top homogeneous polarization vanishes on all distinct column tuples. The multilinear lemma kills that top part, and induction on degree kills $P$.

Consequently, if a nonzero polynomial of degree at most $d$ vanishes on those subset sums, deleting at most $d-1$ columns must destroy spanning. Equivalently there is a nonzero linear functional on $E$ supported on at most $d-1$ of the columns.

## Application and exact limitation

A cleared identity among $H$ affine-ratio heads is a polynomial of degree at most $H$ in the linear span of their numerator and denominator slopes. If that polynomial is not identically zero before Boolean reduction, the preceding argument forces a nonzero linear combination of those slopes supported on at most $H-1$ input coordinates.

This is useful information for small collision clusters. For two heads, the rank argument above gives the stronger complete classification. It does not supply the requested unrestricted count: at the critical widths, $H$ is exponentially larger than $n$, so the support conclusion is automatic. A route through this lemma still needs to decompose an arbitrary badly conditioned large configuration into small collision clusters, or prove a substantially sharper degree-versus-support statement for the special cleared numerator family. Neither step is proved here.

## Verification boundary

The complete same-orientation two-head classification and the finite-difference passage to polynomial injectivity are written proofs. The committed Lean module `HeadComplexity/Research/RobustCubeProjection.lean` checks the multilinear core and its contrapositive. The module `HeadComplexity/Research/PairCollisionRank.lean` checks the rank-three obstruction, its direct full-cube consequence, and opposite-orientation pair independence. It does not yet formalize the full same-orientation classification or polynomial injectivity statement. No original model definition is changed and no stronger unrestricted lower bound is claimed.
