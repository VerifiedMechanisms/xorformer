# Mixed affine-cylinder sign compilation fails at critical widths

## Scope and strengthened statement

An affine-cylinder block is an arbitrary real affine function multiplied by a coordinate-cylinder indicator. The literals may have arbitrary mixed signs. Let $\mathcal C_n(f)$ be the least number of such blocks whose sum, together with a free bias, strictly represents the Boolean table $f$. All coefficients and all signed cancellation are allowed.

For parity on $n$ bits,

$$ \mathcal C_n(\mathrm{PARITY}_n)+1\geq\frac{2}{n+2}\left(\frac32\right)^n. $$

The proof previously written for coherent anchored faces extends to every mixed cylinder. This extension matters: neither arbitrary choices of literals nor the new linear mixed-cylinder compiler avoids the obstruction.

There is also a critical-width family. Fix $p\gt1$ and $c\gt0$. For every sufficiently large $n$, there is a table $f_n$ with an original admissible-head representation of width at most $c2^n/n^p$ and relative margin at least $\exp(-C_p n)$, but

$$ \frac{\mathcal C_n(f_n)}{2^n/n^p}\geq c_p\frac{n^{\alpha(p-1)}}{(\log n)^{1+3\beta}},\qquad \alpha=\log_2(3/2),\quad\beta=\log_2(4/3)=1-\alpha. $$

In particular, at the aimed width $2^n/n^{3/2}$, the required number of mixed affine-cylinder blocks exceeds the original width by $n^{0.29248\ldots}$ up to logarithmic factors. No $O(H(\log n)^A)$ compiler into these scores, for any fixed $A$, can hold even when restricted to the critical widths. The weighted cylinder budget $\sum_j(\min(|P_j|,|Q_j|)+1)$ is at least the number of blocks, so the same impossibility holds for that budget.

The full exponential and dense-width bounds are written proofs. The polynomial-degree ingredient is kernel checked in `formalization/HeadComplexity/Research/MixedCylinderDegree.lean`: `thresholdDegLE_of_cylinder_score` permits arbitrary mixed literals and signed cancellation, and `exists_large_cylinder_of_parity_score` forces a block with at least $n-1$ literals in every strict parity score. All eight public declarations have only `[propext, Classical.choice, Quot.sound]`; the build and axiom logs are `mixed-cylinder-degree-build.txt` and `mixed-cylinder-degree-axioms.txt`. The full all-face count is not asserted to be formalized. The inherited `HeadComplexity.HStar_parity` proves that parity has original head complexity exactly $n$. The gating and quantitative original-head compilation used below are kernel checked. No unrestricted margin-repair impossibility is asserted: the displayed examples already have substantially better original-head margin than either benchmark test.

For historical context, the exponential conjunction-sparsity obstruction is established in Theorem 6.3 of [Basu, Bhatnagar, Gopalan, and Lipton, *Polynomials that Sign Represent Parity and Descartes Rule of Signs*](https://sites.cc.gatech.edu/people/home/parik/RESEARCH/sparse.pdf). The self-contained face proof here permits affine factors and is then amplified at the original-model benchmark widths. The critical-width extension, constants, source margin, and all-representation quantifiers were independently audited by the finite-margin agent.

## Every mixed cylinder covers few parity faces

Write a block as

$$ B(x)=A(x)\prod_{i\in P}x_i\prod_{i\in Q}(1-x_i),\qquad P\cap Q=\varnothing,\qquad S=P\cup Q. $$

There are $3^n$ coordinate faces, since each coordinate is free, fixed to zero, or fixed to one. For a face $F$ with free-coordinate set $T$, take the alternating sum $\Delta_F B$ over its free coordinates.

If a fixed coordinate in $P$ is zero, or a fixed coordinate in $Q$ is one, the block vanishes on the face. Otherwise, every free coordinate in $S$ is forced to its designated literal value wherever the block is nonzero. Summing over these coordinates leaves an affine function of the free coordinates outside $S$. Its alternating sum is zero if at least two such coordinates remain.

Thus a necessary condition for $\Delta_F B\neq0$ is compatibility of every fixed literal and $|T\setminus S|\leq1$. Put $s=|S|$. Each coordinate of $S$ has exactly two allowed face states, free or fixed correctly, regardless of the literal's sign. Outside $S$, either no coordinate is free or exactly one is free. Consequently the block contributes on at most

$$ 2^s\left(2^{n-s}+(n-s)2^{n-s-1}\right)=2^n\left(1+\frac{n-s}{2}\right)\leq(n+2)2^{n-1} $$

faces. When $s=n$, the second summand is zero. The formula can equivalently be interpreted using real powers, so this boundary case causes no negative-exponent counting issue.

For every strict parity score, every face alternating sum is nonzero: after multiplication by a face-dependent common sign, every summand is strictly positive. Hence at least one block or the bias contributes to each face. A bias is an empty-cylinder affine block. Double counting gives

$$ 3^n\leq(\mathcal C_n(\mathrm{PARITY}_n)+1)(n+2)2^{n-1}. $$

This is a sign-only argument. It does not require exact equality with the parity score, bounded coefficients, compatible coefficient signs, or disjoint cylinders.

## A hard address table

Let $d\geq8$ and $M=2^d$. There exists a table $g$ on the address cube with

$$ \mathcal C_d(g)\gt\frac{M}{100d}. $$

Indeed, for $K=\lfloor M/(100d)\rfloor$ there are at most $3^{dK}$ ordered choices of mixed cylinders. For any choice, affine coefficients and bias form a linear space with at most $L=1+(d+1)K\leq M/50$ parameters. The degree-one case of `HeadComplexity.strictPolynomialSignPatterns_card_le` bounds its strict sign tables by $(4eM/L)^L$. Since $\log3\lt2$,

$$ Kd\log3+L\log(4eM/L)\leq\frac M{50}+\frac M{50}\log(200e)\lt\frac M5\lt M\log2. $$

The table $g$ and its negation have equal mixed-cylinder complexity, by negating every affine coefficient and the bias.

Independently, every address table has an exact score equal to its signs formed from at most $J\leq4M\log d/d$ negative-face affine blocks, with total full-cube affine norm at most $3^d$. Expand in negative squarefree monomials, whose coefficient mass is at most $3^d$, and group the monomials using the inherited upward radius-one star cover. The exact star grouping and its norm estimate are detailed in `anchored_affine_dense_width_obstruction.md`; nothing in that construction presupposes a small mixed-cylinder complexity for $g$.

## Amplification and original admissibility

Split $n=d+m$ variables and set $f(a,z)=g(a)(-1)^{|z|}$. Positive-pole Cauchy interpolation gives

$$ q_m(t)=\sum_{j=0}^m\frac{r_j}{t+j+1},\qquad q_m(k)=(-1)^k\quad(0\leq k\leq m),\qquad \sum_j|r_j|\leq C_m=(m+1)^2(2m+1)^{2m+1}. $$

Multiply the exact address star expansion by $q_m(|z|)$. Each resulting summand has an affine numerator, a positive affine denominator with nonnegative slopes, and a negative address-face gate. The kernel-checked `CoherentFaceGating.exists_atom_negativeFace_ratio` approximates it with one original head by using the denominator

$$ j+1+\sum_\ell z_\ell+R\sum_{i\in S}a_i+\delta\left(\sum_i a_i+\sum_\ell z_\ell\right),\qquad R,\delta\gt0. $$

All slopes are strictly positive and the denominator is positive everywhere. The gate does not increase the ungated full-cube norm. Applying `UniformMarginCompiler.hasRelativeMargin_of_uniformlyOneAtomApproximable` to the entire unit signed score, jointly across all terms, gives

$$ H\leq\frac{4(m+1)2^d\log d}{d},\qquad \gamma\geq\frac1{2\cdot3^dC_m+1}. $$

Now consider any mixed affine-cylinder score representing $f$. For every face of the parity block, its alternating sum is a strict address score for $g$ or $-g$. A global mixed affine-cylinder block becomes either zero or a mixed affine-cylinder block on the address variables. Hence at least $\mathcal C_d(g)$ global blocks must contribute on each of the $3^m$ parity faces. Each block contributes on at most $(m+2)2^{m-1}$ such faces, by the preceding mixed-literal calculation. Therefore every representation satisfies

$$ \mathcal C_n(f)\geq\frac{2\mathcal C_d(g)}{m+2}\left(\frac32\right)^m\gt\frac{2^d}{50d(m+2)}\left(\frac32\right)^m. $$

This lower bound quantifies over all mixed affine-cylinder representations. It does not require that their cylinders retain the original address decomposition.

Choose

$$ m=\left\lceil(p-1)\log_2n+3\log_2\log n\right\rceil,\qquad d=n-m. $$

Then $H=O_p(2^n/(n^p\log n))$, so it is eventually below every prescribed $c2^n/n^p$, while the claimed lower ratio follows directly. The full-cube margin is at least $\exp(-O_p(n))$. Zero-head padding reaches any larger desired budget without changing that margin. For the logarithmic fallback, the same construction with $p=2$ gives

$$ \frac{\mathcal C_n(f)}{2^n\log n/n^2}\geq c_2\frac{n^\alpha}{(\log n)^{2+3\beta}}\longrightarrow\infty. $$

## Exact point of failure

The failed sign-only access inequality is $\mathcal C_n(f)\leq CH(\log n)^A+\exp(o(n))$ for a fixed $A$, even when the premise is restricted to $H\asymp2^n/n^{3/2}$ or the fallback width. The additive subexponential term is negligible compared with those widths. Thus introducing mixed literals does not repair the sparse anchored-face route.

The quantitative mixed-cylinder compiler remains valid. The missing step is the existence of a sufficiently cheap cylinder score, and the family above disproves that step at every polylogarithmic overhead. The aimed-width exponent $0.29248\ldots$ does not rule out all polynomial overheads, such as the parent's separate conditional $\sqrt n$-overhead repair interface. Nor does it restrict arbitrary original-head repairs, low-margin truth-table counts, score-dependent multipliers, or methods that use small off-cylinder tails to determine signs through cancellation.

This is an exact full-table compiler obstruction. A small number of wrong labels can invalidate an alternating-sum sign when coefficients have arbitrary magnitude. No robustness to $N/16$ errors, or to a merely positive agreement edge, follows from this proof; approximate cylinder access remains open.
