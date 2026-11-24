# Anchored affine compilation fails at the benchmark widths

## Statement and scope

An anchored affine block is an affine function times an all-positive or all-negative coordinate-face indicator. Write $\mathcal A_n(f)$ for the least number of such blocks whose sum, with a free bias and arbitrary real coefficients, strictly sign-represents $f$ on the full Boolean cube. Repeated anchors and arbitrary signed cancellation are allowed.

For every fixed $p\gt1$ and $c\gt0$, there are, for every sufficiently large $n$, Boolean tables $f_n$ with original head complexity at most $c2^n/n^p$, but

$$ \frac{\mathcal A_n(f_n)}{2^n/n^p}\longrightarrow\infty. $$

The same conclusion holds with the width budget $c2^n\log n/n^2$. The constructed tables have original-model relative margin at least $\exp(-C_p n)$ at the stated width, for a constant $C_p$. Thus this is a counterexample to a particular compiler, not an obstruction to unrestricted margin repair. It rules out a constant-overhead compiler into anchored affine blocks even when restricted to the exponentially large widths relevant to the benchmark.

The full dense-width theorem is a written proof. The norm-preserving original-model gating ingredient is kernel-checked as `HeadComplexity.CoherentFaceGating.exists_atom_negativeFace_ratio` in `formalization/HeadComplexity/Research/CoherentFaceGating.lean`. Existing formal counting, star-cover, and uniform-margin-compiler declarations are identified where used. No original model definition is changed.

## An address table that is hard for anchored affine blocks

Let $d\geq8$ and $M=2^d$. There is a table $g:\lbrace0,1\rbrace^d\to\lbrace-1,+1\rbrace$ such that

$$ \mathcal A_d(g)\gt\frac{M}{100d}. $$

To see this, put $K=\lfloor M/(100d)\rfloor$. There are at most $(2M)^K$ ordered choices of anchors and orientations for $K$ blocks. For each choice the score depends linearly on at most $L=1+(d+1)K$ real coefficients, including its bias. The degree-one case of the kernel-checked theorem `HeadComplexity.strictPolynomialSignPatterns_card_le` gives at most $(4eM/L)^L$ strict sign patterns for this choice.

For $d\geq8$, $L\leq M/50$. The function $t\log(4eM/t)$ is increasing for $0\lt t\leq M$, so the logarithm of the total count is bounded by

$$ K\log(2M)+L\log(4eM/L)\leq\frac{M}{50}+\frac{M}{50}\log(200e)\lt\frac M5\lt M\log2. $$

For the displayed loose constants, use $\log2\lt1$, $200\lt2^8$, and $\log2\gt1/2$. Therefore fewer than $2^M$ tables have anchored complexity at most $K$. An integer complexity greater than $K$ is greater than $M/(100d)$. Negating a score shows that $g$ and $-g$ have the same anchored complexity.

## A short exact anchored score for every address table

The same $g$ has a real score equal to $g$ at every address, written as a sum of $J$ negative-face affine blocks, with

$$ J\leq\frac{4M\log d}{d},\qquad g(a)=\sum_{s=1}^J A_s(a)\prod_{i\in S_s}(1-a_i),\qquad \sum_{s=1}^J\|A_s\|_\infty\leq3^d. $$

Here the affine norms are on the entire address cube, before multiplication by their face indicators. For completeness, expand $g$ in the negative-monomial basis using $y_i=1-a_i$. Its Möbius coefficient at $T$ is an alternating sum of $2^{|T|}$ signs, so its absolute value is at most $2^{|T|}$. The total coefficient mass is at most $\sum_T2^{|T|}=3^d$.

Cover all subsets by upward radius-one monomial stars: a center $S$ covers $S$ and every $S\cup\lbrace i\rbrace$. Assign each monomial to one covering center. The terms assigned to a center factor as its monomial times one affine function, and the sum of the affine sup norms is at most the original coefficient mass. The all-subset cover includes the empty monomial, so no separate bias is needed in this factorization.

The inherited theorem `exists_universal_starCover_bernoulli` supplies such a cover. Its specialization in `bernoulliStarBudget_logarithmic_le` gives

$$ J\leq\frac{2M(\log(d/2)+1)}d\leq\frac{4M\log d}d. $$

The grouping is the algebraic construction used in `SquarefreePolynomial.computableWithHeadsN_of_starCover`. Only its exact factorization is needed here; its approximate heads are not multiplied together.

## Parity interpolation and a genuine gate

For $m\geq1$, there is a rational function

$$ q_m(t)=\sum_{j=0}^m\frac{r_j}{t+j+1},\qquad q_m(k)=(-1)^k\quad(0\leq k\leq m), $$

whose residues satisfy

$$ \sum_{j=0}^m|r_j|\leq C_m:=(m+1)^2(2m+1)^{2m+1}. $$

Let $Q(t)=\prod_{j=0}^m(t+j+1)$. Interpolate the polynomial $P$ of degree at most $m$ with $P(k)=(-1)^kQ(k)$, and take the partial fractions of $P/Q$. At every pole $-j-1$, each Lagrange numerator factor has magnitude at most $2m+1$, while its nonzero integer denominator has magnitude at least one. Also $Q(k)\leq(2m+1)^{m+1}$ and $|Q'(-j-1)|=j!(m-j)!\geq1$. These inequalities give $|r_j|\leq(m+1)(2m+1)^{2m+1}$, proving the stated bound.

Define the $n=d+m$ bit table

$$ f(a,z)=g(a)(-1)^{|z|}. $$

Its exact real score $g(a)q_m(|z|)$ is a sum of $(m+1)J$ terms of the form

$$ \left(\prod_{i\in S}(1-a_i)\right)\frac{r_jA_s(a)}{j+1+\sum_{\ell=1}^m z_\ell}. $$

Each such term is uniformly approximable by one admissible original head. Use numerator $r_jA_s(a)$ and denominator

$$ j+1+\sum_\ell z_\ell+R\sum_{i\in S}a_i+\delta\left(\sum_i a_i+\sum_\ell z_\ell\right),\qquad R,\delta\gt0. $$

Every slope is strictly positive and the denominator is positive on the full cube. Let $R\to\infty$ and $\delta\to0$. The target face retains its original ratio, and the complement is suppressed. The new denominator is at least the original denominator pointwise, so the new head's full-cube norm is at most $|r_j|\|A_s\|_\infty$. This construction is exactly the scope of `CoherentFaceGating.exists_atom_negativeFace_ratio`, allowing the zero address slopes of the original ratio.

The exact limiting sum equals $f\in\lbrace-1,+1\rbrace$. Consequently the existing kernel-checked theorem `UniformMarginCompiler.hasRelativeMargin_of_uniformlyOneAtomApproximable` gives an original-model representation with

$$ H\leq(m+1)J\leq\frac{4(m+1)2^d\log d}{d},\qquad \gamma\geq\frac1{2\cdot3^d C_m+1}. $$

This margin uses the bias plus the sum of full-cube head norms. No parameter rescaling is used to improve it. For $m=O(\log n)$ the right side is at least $\exp(-O(n))$.

## Amplifying the anchored lower bound

Consider any strict anchored affine representation $P(a,z)$ of $f$. For every face $F$ of the $m$-dimensional $z$ cube, take its alternating sum over the free $z$ coordinates. At a fixed address $a$, all summands have the same strict sign after one common sign depending on $F$. Thus the resulting address score strictly represents either $g$ or $-g$.

The alternating sum of a global anchored affine block is either zero or an anchored affine block on the address variables. The original bias remains a permitted free bias. Therefore at least $\mathcal A_d(g)$ global blocks must contribute to each of the $3^m$ faces.

A block whose anchor uses $s$ of the $z$ coordinates can contribute only when every fixed anchored coordinate matches its required value and at most one free coordinate lies outside that anchor. As in `anchored_affine_parity_support_obstruction.md`, it contributes on at most

$$ 2^m\left(1+\frac{m-s}{2}\right)\leq(m+2)2^{m-1} $$

faces. Double-counting contributing block-face pairs yields

$$ \mathcal A_n(f)\geq\frac{2\mathcal A_d(g)}{m+2}\left(\frac32\right)^m\gt\frac{2^d}{50d(m+2)}\left(\frac32\right)^m. $$

This argument allows every possible anchored representation of $f$, not just ones retaining the original addresses or the constructed star cover. Its quantifier is over all anchored affine scores. It is not a statement about all original-model representations.

## Choice of block dimensions at the benchmark

Fix $p\gt1$. Put $N=2^n$ and, for sufficiently large $n$, choose

$$ m=\left\lceil(p-1)\log_2n+3\log_2\log n\right\rceil,\qquad d=n-m. $$

Then $m=O_p(\log n)$, $d\sim n$, and $2^m$ lies between $n^{p-1}(\log n)^3$ and twice that number. The original width therefore satisfies

$$ H=O_p\left(\frac{N}{n^p\log n}\right). $$

In particular $H\leq\lfloor cN/n^p\rfloor$ for every fixed $c\gt0$ and all sufficiently large $n$. Padding by zero genuine heads preserves the margin.

Let $\beta=\log_2(4/3)$ and $\alpha=1-\beta=\log_2(3/2)\gt0$. The anchored lower bound gives

$$ \mathcal A_n(f)\geq c_p\frac{N}{n^{1+\beta(p-1)}(\log n)^{1+3\beta}},\qquad \frac{\mathcal A_n(f)}{N/n^p}\geq c_p\frac{n^{\alpha(p-1)}}{(\log n)^{1+3\beta}}\longrightarrow\infty. $$

At $p=3/2$, this gives a polynomial overhead obstruction with power $\tfrac12\log_2(3/2)\approx0.29248$, up to logarithmic factors. At $p=2$, the same construction also fits the larger fallback width $cN\log n/n^2$, and

$$ \frac{\mathcal A_n(f)}{N\log n/n^2}\geq c_2\frac{n^\alpha}{(\log n)^{2+3\beta}}\longrightarrow\infty. $$

Both benchmark margins are much smaller than the constructed margin $\exp(-O_p(n))$. These examples therefore belong to the high-margin class, and do not establish the existence of any universally low-margin truth table.

## Consequence for the research route

The positive anchored decomposition has bounded mass, and the new gate has no norm loss. Nevertheless, a constant-head-overhead repair cannot always pass through an exact sparse anchored affine score, even at the target widths. The first failed inequality for that route is

$$ \mathcal A_n(f)\leq C H+\exp(o(n)) $$

under the hypothesis that $f$ has an original $H$-head representation at either benchmark scale. The constructed family violates it by a polynomial factor.

A repair directly into general original heads remains open. So do arguments that approximate affine face blocks but allow their small off-face tails to determine labels through cancellation. Neither is covered by this anchored-score lower bound.
