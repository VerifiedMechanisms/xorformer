# A General Finite Difference Simulation Bound

## Statement

Suppose a Boolean classifier has a scalar score with $H$ affine ratios whose denominators are positive on the Boolean cube. Then it has a vanilla realization with at most $2^H-1$ heads, in the unchanged model of [model.md](../../model.md).

In particular, for the scalar pure and retained rotary classes,

$$ H_V(f)\leq 2^{H_P(f)}-1,\qquad H_V(f)\leq 2^{H_A(f)}-1. $$

These bounds include $H=0$ and $n=0$. For $H=1$ the bound is one. For $H=2$ it recovers the three-head general retained upper bound from Theorem 14. The stronger two-head pure theorem requires the special pure numerator relation.

The bound is independent of the input length. It does not prove head preservation for general pure rotary families.

## Proof

For $H=0$, the classifier is constant and needs zero vanilla heads. Assume $H\geq1$, and write the original score as

$$ S(x)=c+\sum_{h=1}^H\frac{N_h(x)}{D_h(x)},\qquad D_h(x)\gt0. $$

Decrease $c$ by a sufficiently small positive amount so that every score is nonzero and all Boolean labels are unchanged. Absorb the resulting constant into the first numerator: set $L_1=N_1+cD_1$ and $L_h=N_h$ for $h\neq1$. Every $L_h$ is affine. Clearing denominators gives the strict sign polynomial

$$ P(x)=\sum_{h=1}^H L_h(x)\prod_{j\neq h}D_j(x),\qquad S(x)=\frac{P(x)}{\prod_{h=1}^H D_h(x)}. $$

For a subset $I\subseteq\lbrace1,\ldots,H\rbrace$, write $L_I=\sum_{h\in I}L_h$ and $D_I=\sum_{h\in I}D_h$. Put $B(x)=1+\sum_i x_i$. For $\varepsilon\gt0$, define

$$ F_\varepsilon(x)=\sum_{\varnothing\neq I\subseteq\lbrace1,\ldots,H\rbrace}(-1)^{H-|I|}\frac{L_I(x)}{B(x)+\varepsilon D_I(x)}. $$

There are $2^H-1$ nonempty subsets. Each numerator is affine. Each denominator is positive on the cube, since $B$ and every nonempty $D_I$ are positive there. For sufficiently small positive $\varepsilon$, every denominator slope is strictly positive: its slope at coordinate $i$ is $1+\varepsilon\sum_{h\in I}C_{h,i}$, where $C_{h,i}$ is the slope of $D_h$. Finitely many subsets and coordinates are involved. Thus every displayed ratio is vanilla-admissible for one common positive interval of $\varepsilon$ values.

### Lemma 1. Alternating moments

For real numbers $L_h,D_h$, the alternating sums satisfy

$$ \sum_{I\subseteq\lbrace1,\ldots,H\rbrace}(-1)^{H-|I|}L_I D_I^k=0\quad\text{for }0\leq k\lt H-1, $$

$$ \sum_{I\subseteq\lbrace1,\ldots,H\rbrace}(-1)^{H-|I|}L_I D_I^{H-1}=(H-1)!\sum_{h=1}^H L_h\prod_{j\neq h}D_j. $$

**Proof.** Expand $L_I D_I^k$ as a sum indexed by ordered tuples $(h_0,\ldots,h_k)$ in $I$, with summand $L_{h_0}\prod_{r=1}^kD_{h_r}$. For a fixed tuple, let $J$ be the set of its indices. Its total alternating coefficient is

$$ \sum_{I\supseteq J}(-1)^{H-|I|}=\begin{cases}1&\text{if }J=\lbrace1,\ldots,H\rbrace,\cr0&\text{otherwise.}\end{cases} $$

The zero case follows by pairing each subset with the subset obtained by toggling any index outside $J$. If $k\lt H-1$, the tuple has fewer than $H$ entries and cannot contain every index. If $k=H-1$, it contains every index exactly when it is a permutation. Fixing $h_0=h$ leaves $(H-1)!$ orders of the remaining indices. Summing these contributions gives the second formula. For $H=1$, the second formula reads $L_1=L_1$ and there are no vanishing-moment conditions. $\blacksquare$

### Lemma 2. The scaled scores converge with an explicit finite error bound

At each cube point, define

$$ R_\varepsilon(x)=\frac{F_\varepsilon(x)}{(-\varepsilon)^{H-1}(H-1)!}. $$

The common scalar multiplier is finite and nonzero for every selected $\varepsilon\gt0$. It can be applied to every numerator without changing the head count. If it is negative, that sign is included in the numerators.

For $B\gt0$ and $B+\varepsilon D\gt0$, the finite geometric expansion is the exact identity

$$ \frac1{B+\varepsilon D}=\sum_{k=0}^{H-1}\frac{(-\varepsilon)^kD^k}{B^{k+1}}+\frac{(-\varepsilon)^H D^H}{B^H(B+\varepsilon D)}. $$

Applying Lemma 1 to this identity gives

$$ R_\varepsilon(x)=\frac{P(x)}{B(x)^H}-\frac{\varepsilon}{(H-1)!}\sum_{\varnothing\neq I\subseteq\lbrace1,\ldots,H\rbrace}(-1)^{H-|I|}\frac{L_I(x)D_I(x)^H}{B(x)^H(B(x)+\varepsilon D_I(x))}. $$

Since every nonempty $D_I(x)$ is positive and $\varepsilon\gt0$, the denominator $B(x)+\varepsilon D_I(x)$ is at least $B(x)$. Therefore

$$ \left|R_\varepsilon(x)-\frac{P(x)}{B(x)^H}\right|\leq\frac{\varepsilon}{(H-1)!}\sum_{\varnothing\neq I\subseteq\lbrace1,\ldots,H\rbrace}\frac{|L_I(x)|D_I(x)^H}{B(x)^{H+1}}. $$

The right side is a fixed finite nonnegative number times $\varepsilon$ at each input. The cube is finite, and every $P(x)/B(x)^H$ is nonzero. A sufficiently small positive $\varepsilon$ therefore makes the displayed error smaller than $|P(x)|/B(x)^H$ simultaneously at every input. Choose it also in the interval ensuring positive denominator slopes. Then $R_\varepsilon$, $P$, and the original strict score have the same sign at every input.

Every head has finite real parameters at this selected $\varepsilon$. The vanilla affine-fraction normal form realizes $R_\varepsilon$ with $2^H-1$ heads. The argument also works when $n=0$, where the cube has one point and denominator-slope conditions are vacuous. This proves the bound. $\blacksquare$

## Zero-constant reciprocal improvement

If the score is a sum of $H+1$ constant-numerator reciprocals with no free constant, multiplying by the last positive denominator gives

$$ D_{H+1}(x)\sum_{h=1}^{H+1}\frac{a_h}{D_h(x)}=a_{H+1}+\sum_{h=1}^H\frac{a_hD_{H+1}(x)}{D_h(x)}. $$

The right side has $H$ arbitrary positive affine ratios. Consequently the original classifier requires at most $2^H-1$ vanilla heads. In particular, three zero-constant reciprocal heads require at most three vanilla heads. The coefficient signs are unrestricted, and zero scores on negative inputs are allowed.

This reduction is Lean-checked in `Results/ReciprocalUpperBound.lean` as `vanilla_of_zero_constant_reciprocals` and `vanilla_three_of_zero_constant_reciprocals`. It does not settle three reciprocal heads with a nonzero free constant: multiplication by the last denominator then adds an affine term whose incorporation into the remaining affine-ratio numerators is not established.

## Architectural and formalization scope

The scalar result applies to every architectural rotary family whose scores have the stated positive affine-ratio form. The pure architectural-to-scalar direction, including the self-query token and arbitrary rotary frequency tables, is addressed separately in Theorem 18. No fixed-width or bounded-precision claim is made here.

The full scalar bound is Lean-checked in `Results/FiniteDifferenceUpperBound.lean`. The main declarations are `FiniteDifference.computable_of_positive_denominators`, `pureRoPEFamily_vanilla_exponential_bound`, and `retainedRoPEFamily_vanilla_exponential_bound`. They include zero heads and zero input bits, preserve the existing strict-positive threshold convention, and conclude computability in the unchanged shared-embedding vanilla architecture.

The algebraic identities are formalized in `Foundation/AlternatingMoments.lean`: `AlternatingMoments.power_below`, `AlternatingMoments.power_top`, `AlternatingMoments.mixed_below`, `AlternatingMoments.mixed_top`, and `AlternatingMoments.reciprocal_sum_expansion`. Lean obtains the mixed moments by differentiating the ordinary power identities over the polynomial ring. The construction then applies `exists_pos_lt_sign_preserving` to the explicit continuous remainder and selects one finite positive parameter. The checked declarations use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry` or new axioms.

The proof uses no pure-specific numerator constraint. It cannot establish the requested equality by itself, because its subset expansion generally has more than $H$ terms.
