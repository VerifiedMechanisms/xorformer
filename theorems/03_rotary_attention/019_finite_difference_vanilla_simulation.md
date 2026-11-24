# A General Finite Difference Simulation Bound

## Statement

Suppose a Boolean classifier has a scalar score with $H$ affine ratios whose denominators are positive on the Boolean cube. Then it has a vanilla realization with at most $2^H-1$ heads, in the unchanged model of [model.md](../../model.md).

In particular, for the scalar pure and retained rotary classes,

$$ H_V(f)\leq 2^{H_P(f)}-1,\qquad H_V(f)\leq 2^{H_A(f)}-1. $$

These bounds include $H=0$ and $n=0$. For $H=1$ the bound is one. For $H=2$ it recovers the three-head general retained upper bound from Theorem 14. The stronger two-head pure theorem requires the special pure numerator relation.

The bound is independent of the input length. It does not prove head preservation for general pure rotary families.

The special pure numerator improves the bound to $2^H-2$ for $H\geq2$. In fact, only one of the $H$ heads needs to be pure; all other affine numerators and positive denominators may be arbitrary. The proof below also gives the bounds $2^{H-1}$ for $H\geq1$ reciprocal heads with a free constant and $2^{H-1}-1$ for reciprocal heads with zero free constant.

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

## One pure head removes one subset term

Suppose $H\geq2$ and one head is pure. The finite perturbation from Theorem 16 makes its input-token values distinct and all total scores nonzero. Its endpoint lemma supplies $N_1=tD_1+\sigma F$, where $\sigma\in\lbrace-1,1\rbrace$, the affine form $F$ is positive on the cube, and its slopes are all strictly positive or all strictly negative.

Subtract $tD_1$ from the first numerator and absorb $c+t$ into a second numerator. The cleared polynomial $P$ is unchanged, and the first resulting numerator is $L_1=\sigma F$. Use $F$ as the common base in the subset construction. For parameter $\varepsilon\gt0$, perturb only this numerator to

$$ L_1^{(\varepsilon)}=\sigma(F+\varepsilon D_1). $$

The new cleared polynomial is $P+\sigma\varepsilon\prod_hD_h$, so the scaled finite-difference score still tends to $P/F^H$. The exact geometric remainder remains continuous at zero because all denominators equal $F$ there. Every perturbed denominator $F+\varepsilon D_I$ is positive and retains the strict slope orientation of $F$ for sufficiently small $\varepsilon$.

The empty subset still has zero numerator. The singleton subset $I=\lbrace1\rbrace$ now has a constant ratio:

$$ \frac{L_1^{(\varepsilon)}}{F+\varepsilon D_1}=\sigma. $$

Its scaled coefficient can be put into the free readout constant. Deleting these two subsets leaves exactly $2^H-2$ heads. A finite strict sign margin chooses one finite parameter and completes the Boolean simulation. This gives six vanilla heads for an arbitrary three-head pure classifier, and recovers two heads when $H=2$.

The proof is Lean-checked in `Results/PureFiniteDifference.lean`. The main declarations are `CubeAffine.computable_of_strict_tangent_uniform_numerator`, `vanilla_of_positive_fractions_with_uniform_endpoint`, `vanilla_of_pure_add_positive_fractions`, and `pureRoPEComputable_vanilla_improved_exponential_bound`. The mixed theorem allows all heads except the distinguished pure head to be arbitrary positive affine ratios. It includes $n=0$; the zero-head and one-head pure cases are separately covered by Theorem 16.

## Zero-constant reciprocal improvement

If the score is a sum of $H+1$ constant-numerator reciprocals with no free constant, multiplying by the last positive denominator gives

$$ D_{H+1}(x)\sum_{h=1}^{H+1}\frac{a_h}{D_h(x)}=a_{H+1}+\sum_{h=1}^H\frac{a_hD_{H+1}(x)}{D_h(x)}. $$

The right side has $H$ arbitrary positive affine ratios. Consequently the original classifier requires at most $2^H-1$ vanilla heads. In particular, three zero-constant reciprocal heads require at most three vanilla heads. The coefficient signs are unrestricted, and zero scores on negative inputs are allowed.

This reduction is Lean-checked in `Results/ReciprocalUpperBound.lean` as `vanilla_of_zero_constant_reciprocals` and `vanilla_three_of_zero_constant_reciprocals`. It does not settle three reciprocal heads with a nonzero free constant: multiplication by the last denominator then adds an affine term whose incorporation into the remaining affine-ratio numerators is not established.

## Reciprocal improvement with a free constant

A sum of $m+1$ constant-numerator reciprocals, with an arbitrary free constant, requires at most $2^m$ vanilla heads. Thus three reciprocal heads with a free constant require at most four vanilla heads. This bound does not assert a three-head simulation.

For $m \gt 0$, write $R=D_{m+1}$ and $L=a_{m+1}+cR$. Clearing denominators gives a polynomial with the same sign as the reciprocal score:

$$ P=L\prod_{j=1}^mD_j+R\sum_{h=1}^ma_h\prod_{j\neq h}D_j. $$

For each subset $I\subseteq\lbrace1,\ldots,m\rbrace$, put $D_I=\sum_{h\in I}D_h$ and $a_I=\sum_{h\in I}a_h$. Set $B_t(x)=1+t\sum_i x_i$. The following sum uses one affine numerator and one denominator for every subset, including the empty subset:

$$ T_t=\sum_{I\subseteq\lbrace1,\ldots,m\rbrace}\frac{(-1)^{|I|}}{B_t+t^2D_I}\left(\frac{L}{t^{2m}m!}-\frac{Ra_I}{t^{2m-2}(m-1)!}\right). $$

The alternating power identity and its mixed version show that $T_t(x)\to P(x)$ as $t\to0$. The constant weights first survive at order $m$ and produce $L\prod_jD_j/B_t^{m+1}$; the weights $a_I$ first survive at order $m-1$ and produce $R\sum_ha_h\prod_{j\neq h}D_j/B_t^m$. Both exact rational remainders tend to zero. These are two expansions of the same $2^m$ denominator family, so their affine numerators can be added without adding heads.

Every denominator is positive for $t\gt0$, and its slope in coordinate $i$ is $t+t^2\sum_{h\in I}C_{hi}$, which is strictly positive for sufficiently small $t$. A finite strict sign margin therefore selects one finite $t\gt0$ that realizes the desired Boolean labels. For an original score that vanishes at some negative inputs, first decrease the free constant slightly. The case $m=0$ is an affine threshold after clearing its single positive denominator, and needs one head. Zero input bits are included.

The exact reciprocal expansion is formalized as `AlternatingMoments.reciprocal_power_expansion` in `Foundation/AlternatingReciprocals.lean`. The shared-denominator construction is `FiniteDifference.computable_of_strict_reciprocalCleared`; the resulting bounds are `vanilla_of_reciprocals` and `vanilla_four_of_three_reciprocals` in `Results/ReciprocalFiniteDifference.lean`.

## Architectural and formalization scope

The scalar result applies to every architectural rotary family whose scores have the stated positive affine-ratio form. The pure architectural-to-scalar direction, including the self-query token and arbitrary rotary frequency tables, is addressed separately in Theorem 18. No fixed-width or bounded-precision claim is made here.

The full scalar bound is Lean-checked in `Results/FiniteDifferenceUpperBound.lean`. The main declarations are `FiniteDifference.computable_of_positive_denominators`, `pureRoPEFamily_vanilla_exponential_bound`, and `retainedRoPEFamily_vanilla_exponential_bound`. They include zero heads and zero input bits, preserve the existing strict-positive threshold convention, and conclude computability in the unchanged shared-embedding vanilla architecture.

The algebraic identities are formalized in `Foundation/AlternatingMoments.lean`: `AlternatingMoments.power_below`, `AlternatingMoments.power_top`, `AlternatingMoments.mixed_below`, `AlternatingMoments.mixed_top`, and `AlternatingMoments.reciprocal_sum_expansion`. Lean obtains the mixed moments by differentiating the ordinary power identities over the polynomial ring. The construction then applies `exists_pos_lt_sign_preserving` to the explicit continuous remainder and selects one finite positive parameter. The checked declarations use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry` or new axioms.

The generic bound uses no pure-specific numerator constraint; the one-subset deletion uses the positive pure endpoint explicitly. Neither construction establishes the requested equality at arbitrary head counts, because its subset expansion generally has more than $H$ terms.
