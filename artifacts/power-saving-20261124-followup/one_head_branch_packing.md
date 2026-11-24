# Feasible one-head branches with a balanced constant denominator

## Statement

Fix an ordered affine basis $I$ of $d=n+1$ Boolean vertices and prescribed unit values $g\in\lbrace-1,+1\rbrace^d$. Let $Z$ be its affine evaluation matrix, with rows $z_x=(1,x_1,\ldots,x_n)$, and put $T=Z^{-1}\mathrm{diag}(g)Z$.

Consider all positive coefficient vectors $b\in\mathbb R^d$ for which $a=Tb$ satisfies the full-cube inequalities $|z_xa|\geq z_xb$. Every ratio $z_xa/(z_xb)$ is then an admissible original one-head score, has the fixed unit observations on $I$, and strictly represents its sign table.

Fix $0\lt\kappa\leq1$. Among those representations satisfying

$$ b_0\geq\kappa\sum_{i=0}^{d-1}b_i, $$

the number of different truth-table extensions is at most

$$ \left(\frac{4d^{3/2}}{\kappa}\right)^d. $$

In particular, a constant coefficient at least a fixed inverse power of $n$ times the coefficient sum gives at most $n^{O(n)}$ extensions per actual signed basis. This is a written proof, not a Lean declaration. The hypothesis on the constant coefficient is essential to the argument below and has not been removed.

## Arithmetic volume distortion of the basis map

Let $s_1\geq\cdots\geq s_d\gt0$ be the singular values of $Z$. Since $Z$ has integer entries and is nonsingular, $|\det Z|\geq1$. Since all entries are zero or one, every $s_i\leq\|Z\|_F\leq d$.

Write $\sigma_1\geq\cdots\geq\sigma_d\gt0$ for the singular values of $T$. Exterior powers and submultiplicativity give, for every $0\leq k\leq d$,

$$ \prod_{i=1}^k\sigma_i=\|\bigwedge^kT\|\leq\|\bigwedge^kZ^{-1}\|\|\bigwedge^kZ\|=\frac{\left(\prod_{i=1}^ks_i\right)\left(\prod_{i=1}^{d-k}s_i\right)}{|\det Z|}\leq d^d. $$

The middle diagonal sign matrix is orthogonal and contributes operator norm one. Choosing $k$ to be the number of singular values greater than one yields

$$ \prod_{i=1}^d\max(1,\sigma_i)\leq d^d. $$

This product estimate retains the total distortion of the ellipsoid. Replacing every singular value by the largest one would lose a further factor of $d$ in the logarithmic exponent.

## Packing different label tables

Scale $b$ so that $\sum_i b_i=1$. This does not change the score or its labels. Then $\|b\|_2\leq1$, $b_0\geq\kappa$, and $a\in E=T(B_2^d)$.

Choose one witness $a$ for each different represented table. If two witnesses $a,a'$ have opposite labels at $x$, their full-cube unit inequalities imply

$$ |z_x(a-a')|\geq z_xb+z_xb'\geq2\kappa. $$

Since $\|z_x\|_2\leq\sqrt d$, the witnesses are pairwise separated by at least $2\kappa/\sqrt d$ in Euclidean distance. Let $r=\kappa/\sqrt d\leq1$. The interiors of the radius $r$ balls about the witnesses are disjoint, and their union is contained in $E+rB_2^d$.

In singular-vector coordinates,

$$ E+rB_2^d\subseteq2\mathrm{diag}(\sigma_1+r,\ldots,\sigma_d+r)B_2^d. $$

Indeed, after coordinatewise division by $\sigma_i+r$, the sum of a point in $E$ and a point in $rB_2^d$ has norm at most two by the triangle inequality. Comparing Euclidean volumes now gives

$$ \begin{aligned} \lvert\mathcal F\rvert&\leq2^d\prod_{i=1}^d\left(1+\frac{\sigma_i}{r}\right)\cr &\leq2^d\left(1+\frac1r\right)^d\prod_{i=1}^d\max(1,\sigma_i)\cr &\leq\left(\frac4r\right)^dd^d=\left(\frac{4d^{3/2}}{\kappa}\right)^d. \end{aligned} $$

The label family is finite, so selecting one witness per label and applying finite volume additivity causes no compactness or choice-of-limit issue. $\blacksquare$

## Exact obstruction to a simpler order-chart argument

The two open branches in `generic_one_head_basis_nonuniqueness.md` cannot be merged by fixing the order of the individual terminal ratios $a_i/b_i$. The same basis has the following two fully feasible integer witnesses:

$$ \begin{aligned} b&=(34,67,48,72,39,95,60,43),\cr a&=(-2420,4983,-3550,5406,-2423,-1641,778,-3137),\cr b'&=(23,39,4,21,37,27,96,30),\cr a'&=(-1285,2867,-2128,3173,-1483,-993,384,-1778). \end{aligned} $$

Both terminal-ratio lists have the same strict increasing coordinate order

$$ (2,7,0,4,5,6,1,3). $$

Their full truth tables nevertheless differ at vertex $17$. `check_one_head_ratio_order.py` checks every cube inequality and all strict rational comparisons exactly. This is a finite exact computation, not a separate Lean proof. It rules out one branch per terminal-ratio order, while leaving a bound on the number of branches within an order open.

## First remaining obstruction

The original model allows $b_0/\sum_i b_i$ to be arbitrarily small. The packing separation above then tends to zero, and the displayed count provides no uniform $n^{O(n)}$ estimate. A naive boundary recursion is also insufficient: labels unresolved at one scale can lie on a denominator-zero face, and the leading numerator can have both signs there. In the exact seven-variable example, taking $b=e_1$ gives $a=(-6,13,-10,14,-6,-4,2,-8)$; the resulting boundary data satisfy $|A(x)|\geq B(x)$ everywhere, but $A$ has both signs on the face $x_1=0$ where $B=0$.

That boundary vector is not an admissible original head, because some denominator coefficients vanish. It is a limit obstruction to the proposed one-sign boundary lemma. Any recursive count must track the remaining affine sign problem on this face and prove that its entropy can be charged without repeatedly paying the full dimension.

The current argument therefore controls only a denominator-balanced subfamily. It does not bound all universally low-margin truth tables, does not provide a constant-overhead repair, and does not improve the unrestricted lower bound.

## A kernel-checked edge restriction

For a coefficient-positive denominator $B=b_0+\sum_i b_ix_i$, write $A=a_0+\sum_i a_ix_i$. Suppose $|A(x)|\geq B(x)$ everywhere and $x_i=0$ at a unit contact $|A(x)|=B(x)$. Changing just this bit to one gives

$$ B(x)+b_i\leq|A(x)+a_i|\leq|A(x)|+|a_i|=B(x)+|a_i|, $$

so $b_i\leq|a_i|$. An affine spanning set of unit contacts has a point with $x_i=0$ for every coordinate; otherwise the nonzero affine form $x_i-1$ vanishes on the entire set. Thus every feasible actual affine-basis certificate satisfies $b_i\leq|a_i|$ for all variable coordinates.

This implication is kernel checked as `HeadComplexity.UnitGapBasisGeometry.abs_slope_ge_of_affine_spanning_contacts` in [UnitGapBasisGeometry.lean](../../formalization/HeadComplexity/Research/UnitGapBasisGeometry.lean). The intermediate zero-contact lemma needs no positivity hypothesis. The module builds, and its four theorem declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. This necessary condition does not constrain $b_0/\sum_i b_i$ and does not prove uniqueness or a branch count.

## A weaker possible repair of the packing argument

The already refuted constant-denominator deformation would require every branch to contain $b=e_0$. A weaker sufficient statement would be that every nonempty fully feasible branch contains some positive $b$ with

$$ b_0\geq n^{-C}\sum_i b_i $$

for an absolute constant $C$. Such a representative would permit the earlier packing bound without requiring a common representative or retaining an initially ill-conditioned one. No proof is known.

The reproducible floating search `search_fixed_basis_balance.py` tested 89,384 random eight-variable candidate bases and 88,984 sampled feasible branches over 300 seconds. The smallest computed maximum of $b_0/\sum_i b_i$ was $1/4$. For a separate fixed basis supplied by the root agent, `analyze_fixed_basis_boundary.py` numerically enumerated four positive branches, with computed maxima $1/4$, $1/3$, $1/2$, and $1$. Its exact matrix is reconstructed from the Boolean basis before running the floating LP solver. These are finite exploratory computations, not exact feasibility or exhaustion certificates, and do not support an asymptotic upper bound.

Another formulation makes the boundary issue explicit. Associate to each feasible $b$ the open box

$$ Q_b=Tb+\mathrm{diag}(b)(-1,1)^d. $$

Boxes belonging to different truth tables are disjoint: an intersection would imply $|(Tb-Tb')_i|\lt b_i+b'_i$ in every coordinate, contradicting the unit gaps at any Boolean row where the labels differ. Each box has opposite corners $(T-I)b$ and $(T+I)b$, lying in the two complementary eigenspaces of $T$. This formulation alone does not bound how many very thin boxes can approach the boundary. A successful argument must use the actual Boolean observation hyperplanes or prove the balanced-representative statement above.
