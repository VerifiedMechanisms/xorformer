# Exact address scores do not determine a head decomposition

## Status

The finite residual-parameter count, the exponential one-head fiber, and the constant-face embedding below are written proofs. `Research/SameFaceScoreFiber.lean` checks the general same-face identity and an explicit pair of genuine original heads with different extension labels. The module build completed with 3226 jobs; all three theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`. The finite-margin agent independently audited all three written arguments, including both coherent orientations and the finite error allocation. None of these results proves the desired unrestricted lower bound or disproves a density-specific extension bound.

## Frozen head data leave few residual parameters

Split the $n$ coordinates into $d$ address coordinates $z$ and $k=n-d$ remaining coordinates $y$. Fix every head's complete affine numerator and denominator on the face $y=0$, including their real coefficients. Permit arbitrary affine extensions in $y$, arbitrary real numerator coefficients, arbitrary coherent denominator orientations subject to full-cube positivity, and a free bias.

There are $p=1+2kH$ remaining real parameters. At a fixed cube input, clearing the positive product of the $H$ denominators gives a polynomial of degree at most $H+1$ in those parameters. Consequently, when $1\leq p\leq N=2^n$, the existing strict polynomial sign theorem gives

$$ T\leq\left(\frac{4e(H+1)N}{p}\right)^p. $$

If $H\geq1$, $k\geq1$, and $H\leq N$, then the logarithm of this expression is $O(nkH)$. Taking $d$ about $\log_2(nH)$ at either critical width leaves $k=O(\log n)$, so the residual directions already cost only $O(nH\log n)$ entropy. The high polynomial degree in the residual variables is harmless at that scale.

The hypothesis fixes the individual head data. It does not merely fix the score values or their signs on the address face.

## A large one-head fiber of an exactly constant face

Let $m\geq1$, let $n=2m+1$, and write the input as $(x,t,y)$ with $x,t\in\lbrace0,1\rbrace^m$ and $y\in\lbrace0,1\rbrace$. For every weight vector $w\in\lbrace1,\ldots,2^m\rbrace^m$, put

$$ B_w(x,t)=1+\sum_{j=1}^m w_jx_j+\sum_{i=1}^m2^{i-1}t_i,\qquad S_w(x,t,y)=\frac{B_w(x,t)-(2^m+1/2)y}{B_w(x,t)+y}. $$

All denominator slopes and the constant term are strictly positive. The numerator is affine with arbitrary real coefficients, so `FracAtom.ofPositiveAffineRatio` makes this one genuine original head. The denominator is positive on the entire cube. On the whole address face $y=0$, the score is exactly one, independently of $w$.

On $y=1$ the numerator is a half-integer, hence never zero. Set $x$ to the $j$-th unit vector, and let $r=\sum_i2^{i-1}t_i$ range over every integer from zero to $2^m-1$. Then

$$ S_w(e_j,t,1)\gt0\quad\Longleftrightarrow\quad r+w_j\geq2^m. $$

If $w_j\lt w'_j$, choose $r=2^m-w'_j$. This lies in the permitted range, gives a positive label for $w'$ and a negative label for $w$, and therefore distinguishes their full truth tables. Thus exactly the same real address score table belongs to at least

$$ (2^m)^m=2^{m^2} $$

different strict one-head truth tables. There is no head-permutation ambiguity when $H=1$.

This does not refute the desired density-specific estimate. The example has one head and an address face of dimension $2m$, much larger than the proposed $\log_2(nH)$ address scale. In the independently audited shared-address matching construction at $H\asymp N/\mathrm{poly}(n)$, identifying $H$ components consumes about $\log_2H$ coordinates, leaving only $O(\log n)$ selector coordinates. Its $(H!)^{O(\log n)}$ branch multiplicity respects an $\exp(O(nH\log n))$ budget. Neither construction proves that all original-model fibers satisfy that budget.

## A constant face can hide any original truth table

Let $S(z)=b+\sum_{h=1}^H A_h(z)/B_h(z)$ be any strict original score on the $n$-cube. There is a score on the $(n+1)$-cube with at most $2H+1$ genuine heads which is exactly one on $y=0$ and has the same signs as $S$ on $y=1$.

First replace any constant-denominator head by a strictly positive-slope denominator arbitrarily close to it, keeping the affine numerator. For a constant denominator $c$, use $c+\eta\sum_i z_i$ with $\eta\gt0$, keeping the affine numerator. Its norm does not increase, and its error tends uniformly to zero. This handles the original $\alpha=1$ case without assuming that a constant-denominator head can ignore arbitrary coordinates. This preserves the complete truth table after a sufficiently small perturbation, because the original cube is finite and its score is strict. Every denominator may therefore be assumed to have either strictly positive or strictly negative slopes.

For a positive-slope denominator, use the pair

$$ P_{h,\epsilon,T}(z,y)=\frac{A_h(z)}{B_h(z)+\epsilon y}-\frac{A_h(z)}{B_h(z)+Ty}. $$

For a negative-slope denominator, use

$$ P_{h,\epsilon,T}(z,y)=\frac{A_h(z)}{B_h(z)+T(1-y)}-\frac{A_h(z)}{B_h(z)+T-\epsilon y}. $$

Here $0\lt\epsilon\lt T$. Every old and new denominator slope has the required common sign, and all denominators are positive on the full cube. Every numerator is still affine. Each pair is identically zero on $y=0$. On $y=1$, the positive pair converges uniformly to $A_h/B_h$ as $\epsilon\to0$ and $T\to\infty$; the negative pair converges uniformly as $T\to\infty$ with fixed positive $\epsilon$. All individual norms are at most the norm of the corresponding original head, since each denominator is at least $B_h$ pointwise.

Add bias one and the single genuine positive-slope head

$$ C_\eta(z,y)=\frac{(b-1)y}{1+\eta y+\eta\sum_i z_i},\qquad\eta\gt0. $$

It vanishes exactly on $y=0$ and approaches $b-1$ uniformly on $y=1$. Hence $1+C_\eta+\sum_hP_{h,\epsilon,T}$ has the claimed exact face values and, for finite sufficiently small and large parameter choices, all the required extension signs. Write $D=|b|+\sum_h\|A_h/B_h\|_\infty$ for the original amplitude. The initial constant-denominator approximation also does not increase any head norm, so the final amplitude satisfies

$$ D_{\mathrm{embedded}}\leq1+|b-1|+2\sum_h\|A_h/B_h\|_\infty\leq2D+2. $$

Thus the construction does not require unbounded individual amplitudes. It still retains the source-dependent tiny gap on the opposite face.

For an explicit finite error allocation, let $g=\min_z|S(z)|\gt0$. Approximate each constant-denominator head within $g/(4(H+1))$, approximate each resulting head by its pair on $y=1$ within $g/(4(H+1))$, and choose the bias helper error below $g/4$. The final score differs from the original one on $y=1$ by less than $3g/4$. Every limiting argument therefore selects actual finite parameters and strictly admissible heads; no degenerate head is used in the output.

Thus even the singular fiber of the fixed exact face score one contains, at constant head overhead, copies of every unrestricted original class in one fewer input dimension. This is not a proof that its critical-width entropy is large. It shows that bounding that fiber cannot be justified merely by generic finite-to-one identifiability or by discarding constant-score decompositions.

## The precise unresolved counting step

The already kernel-checked interface `HeadComplexity.CoherentDenominatorCharts.worstCase_gt_of_sqrt_chart_entropy` asks for an upper bound $\exp((nH+1)\sqrt n)$ on every globally feasible active chart. The logarithmic counterpart asks for $\exp((nH+1)n/\log n)$. These charts retain the full-cube unit-gap inequalities, coefficient box, nonsingular active basis, and union over coherent denominator orientations.

A stronger density-specific target would bound those chart extensions by $\exp(O(nH\log n))$. One possible proof would reconstruct the individual address-head data through that many relevant branches and then apply the residual bound above. No such reconstruction theorem is known here. A bound only on exact observation fibers would still require control of how extension labels change as their continuously varying observation values change. The generic Cramer or elimination degree restores a term of order $nH\log H$, which is of order $n^2H$ at critical width. Dividing by $H!$ removes only $O(H\log H)$ and does not remove that extra factor of $n$.

## Restriction transfers every healthy repair back

`HeadComplexity.RelativeMarginRestriction.relativeMargin_restrict_ge` and `hasRelativeMargin_restrict`, in `Research/RelativeMarginRestriction.lean`, kernel-check that restriction to any coordinate face cannot decrease the relative margin of a strict score. The full-cube norm of each restricted head can only decrease, while every retained signed score is unchanged. The module built with 3285 jobs, and all seven theorem audits use only the standard three axioms.

The existing exact `FracAtom.restrict` construction retains $\alpha$, $\delta$, and the positive weights of every free coordinate. Fixed coordinates contribute their positive attention weights to $\gamma$ and their numerator contributions to $\eta$. Thus the restricted atom is genuine even when $\alpha=1$; no new positive-slope approximation is required for restriction.

Consequently, a comparison-width healthy-margin repair for every constant-face embedding above would restrict to a comparison-width healthy-margin repair for every original source table. The singular constant-face class cannot simply be omitted from the access theorem. This implication does not claim that such a repair is impossible.

The declarations `not_hasRelativeMargin_of_restriction` and `allRepresentationsLowMargin_of_restriction` make the universal quantifier explicit: absence of every width $K$ comparison representation of margin $\gamma$ survives any original-model extension. Combining this with the written embedding gives an injection of the corresponding low-margin truth-table classes at source widths $H$ and $2H+1$, with $K$ and $\gamma$ held fixed. No chosen ill-conditioned witness is used.

There is an important entropy limit to this observation. The embedding fixes all labels on an entire half-cube, so its class in dimension $n+1$ has the trivial upper count $2^{2^n}$. It does not by itself obstruct a global half-entropy budget in that larger dimension. What fails is the inference that exact face scores freeze the individual head parameters or that generic finite-to-one reconstruction covers every fiber. A sharper density-specific bound on the exceptional fibers remains a possible route.
