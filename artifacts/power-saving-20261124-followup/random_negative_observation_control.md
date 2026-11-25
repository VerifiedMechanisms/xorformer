# Random Negative Observations Control Nonnegative Heads

## Statement and scope

There is a uniform, parameter-independent observation bound for nonnegative original heads outside a small exceptional subset of the cube. It does not require the observed vertex to maximize the head. The deterministic bound is kernel checked in `Research/SelectedNegativeControl.lean`; the random exceptional-set estimate below is a written finite proof.

This bound concerns values of nonnegative heads. It does not bound a strict sign gap, produce a narrow repair, or count unrestricted truth tables. The positive-partition obstruction at the end explains why that distinction is necessary.

## Any selected downward neighbors

Let $g=A/B$ on the Boolean cube, where $A$ is affine and nonnegative everywhere, and $B$ is affine with strictly positive values and nonnegative variable coefficients. Fix a vertex $v$. Let $T$ be any set of $k\geq2$ coordinates at which $v_i=1$, and write $v-i$ for changing coordinate $i$ to zero. Then

$$ (k-1)g(v)\leq\sum_{i\in T}g(v-i). $$

**Proof.** Write $A=A(v)$, $B=B(v)$, and let $a_i,b_i$ be the affine variable coefficients. Every denominator $B-b_i$ is positive and at most $B$. The numerator at the vertex obtained by deleting all coordinates in $T$ is

$$ A_T=A-\sum_{i\in T}a_i\geq0. $$

Consequently

$$ \sum_{i\in T}\frac{A-a_i}{B-b_i}\geq\frac{\sum_{i\in T}(A-a_i)}B=(k-1)\frac AB+\frac{A_T}B\geq(k-1)g(v). $$

Every numerator $A-a_i$ is nonnegative because it is an actual cube value. No sign condition on the numerator coefficients, no comparison among denominator coefficient sizes, and no maximizing condition on $v$ is used. The coordinates outside the selected face remain fixed. The exact finite subset inequality is `SelectedNegativeControl.affine_corner_subset_ratio_le`.

For a denominator with nonpositive variable coefficients, the same statement holds with any selected upward neighbors at coordinates where $v_i=0$. The two-neighbor forms on actual Boolean vertices are `affine_two_down_ratio_le` and `affine_two_up_ratio_le`.

An equivalent proof expands a nonnegative affine numerator as its minimum plus a nonnegative combination of coordinate literals. Each nonzero literal at $v$ survives at least $k-1$ selected downward neighbors, while the denominator only decreases. This expansion is an explanation of the inequality, not an assumption restricting the numerator.

## Four observations independent of every head

Let $Z$ be any set of observed vertices. Call $v$ good if it has two distinct downward neighbors in $Z$ and two distinct upward neighbors in $Z$. Select such neighbors $d_1,d_2,u_1,u_2$ once for each good vertex. Every nonnegative original head satisfies

$$ g(v)\leq g(d_1)+g(d_2)+g(u_1)+g(u_2). $$

For an original head, all denominator slopes have the sign of its single scalar $\alpha-1$. If this sign is nonnegative, use the two downward neighbors and add the nonnegative values at the upward neighbors. If it is negative, use the upward pair and add the downward values. The case $\alpha=1$ is included. Since the denominator is strictly positive, head nonnegativity implies numerator nonnegativity at every cube point.

`SelectedNegativeControl.original_four_neighbors_le` proves this statement directly for `FracAtom`. Its observations depend on $Z$ and $v$, not on the head, the target-dependent denominator, or any real coefficient. There is no union bound over parameter values.

For any number of nonnegative original heads, set $G=\sum_hg_h$. The same observation choices give

$$ G(v)\leq G(d_1)+G(d_2)+G(u_1)+G(u_2). $$

In particular, if $G(z)\leq L$ for all $z\in Z$, then $G(v)\leq4L$ at every good vertex. These are `sum_four_neighbors_le` and `total_le_four_of_observations`. Arbitrary differences of nonnegative heads are not substituted into this inequality.

## A random half leaves exponentially fewer exceptional vertices

First include each Boolean vertex in $Z$ independently with probability $1/2$. At a vertex of weight $r$, its $r$ downward neighbors are distinct, so the probability that fewer than two belong to $Z$ is exactly

$$ (1+r)2^{-r}. $$

The analogous upward probability is $(1+n-r)2^{-(n-r)}$. The two events can overlap, so their sum is an upper bound. If $E(Z)$ is the set of vertices that are not good, linearity of expectation and the binomial theorem give

$$ \mathbb E|E(Z)|\leq2\sum_{r=0}^n\binom nr(1+r)2^{-r}=2\left(1+\frac n3\right)\left(\frac32\right)^n. $$

For example, with probability at least $1/2$,

$$ |E(Z)|\leq4\left(1+\frac n3\right)\left(\frac32\right)^n. $$

No independence between exceptional-vertex events is needed. Only independence of the distinct neighbors of one fixed vertex is used in the probability calculation.

The conclusion also holds for an exactly balanced random half, with a slightly larger constant. Suppose $n\geq1$ and $Z$ is uniform among subsets of size $2^{n-1}$. Any specified $s$ distinct vertices all miss $Z$ with probability at most $2^{-s}$, by sampling without replacement. For $r\geq1$, the event of exactly one observed downward neighbor is contained in the union, over its possible location, of the events that the other $r-1$ neighbors all miss $Z$. Hence the probability of fewer than two observed downward neighbors is at most $(1+2r)2^{-r}$. The same bound also covers $r=0$. Therefore

$$ \mathbb E|E(Z)|\leq2\left(1+\frac{2n}3\right)\left(\frac32\right)^n $$

for the exactly balanced model. At either critical width in this run, even a polynomial multiple of this exceptional-set size is negligible relative to the width, because $(3/2)^n/2^n=(3/4)^n$ decays exponentially.

## The gap remains after centering

Every original head can be shifted by its full-cube minimum to become nonnegative, with the shift absorbed into the score bias. Thus the deterministic observation theorem does apply to a centered nonnegative decomposition. However, the resulting bias can cancel the positive total almost exactly. Controlling the positive total on observed vertices does not control its distance from the threshold.

The precise obstruction is in [unrestricted_capacity_positive_partition_gap.md](unrestricted_capacity_positive_partition_gap.md): any original strict score of width $H$ can be embedded, with $H+2$ admissible nonnegative heads having minimum zero, into a bounded-mass positive total arbitrarily close to the constant one, while its difference from one retains the complete original truth table. Thus a proposed inference from bounded observed mass or bounded total mass to a uniform strict-label gap is false. A quotient or removal theorem for these positive near-partitions, with controlled width and retained labels, would still be needed.

## Verification

`SelectedNegativeControl.lean` contains the deterministic subset inequality, both Boolean edge directions, the complete original-head bridge, and the summed observation bound. The accompanying build and transitive axiom outputs distinguish those kernel-checked declarations from the written probability computation. No original definition was modified.
