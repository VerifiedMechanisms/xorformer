# Unrestricted capacity after exact score normalization

## Scope

This note audits unrestricted counting independently of the margin argument. The model remains the original affine-ratio normal form, with target-dependent denominators, arbitrary real numerator coefficients, and arbitrary signed cancellation. Every original denominator is strictly positive on the complete Boolean cube.

The exact normalization below sharpens the finite constants in the usual Warren count. It does not improve the asymptotic exponent two. The later interpolation-branch calculation explains precisely why an inherited factorial example does not settle the missing Boolean sign count.

The normalized counting bridge and a finite consequence have now been formalized in `formalization/HeadComplexity/Research/NormalizedCounting.lean`. In this run the imported theorem `HeadComplexity.warrenStrictSignPatternBound` also discharges the inherited sign-counting premise. The interpolation-branch analysis and proposed replacement lemma below remain written mathematics. A transitive axiom report containing only foundational axioms, by itself, must never be mistaken for discharging a theorem hypothesis.

## Exact normalization at one cube vertex

Let $n\geq1$, $H\geq1$, $X=\lbrace0,1\rbrace^n$, and $N=2^n$. Consider any strict score

$$ S(x)=c+\sum_{h=1}^H\frac{A_h(x)}{B_h(x)},\qquad B_h(x)\gt0\quad(x\in X). $$

Write $A_h(x)=\alpha_h+u_h\cdot x$ and $B_h(x)=\beta_h+v_h\cdot x$. Since the zero vertex belongs to $X$, every $\beta_h\gt0$. Direct division gives

$$ \frac{A_h(x)}{B_h(x)}=\frac{\alpha_h}{\beta_h}+\frac{a_h\cdot x}{1+b_h\cdot x},\qquad b_h=\frac{v_h}{\beta_h},\qquad a_h=\frac{u_h}{\beta_h}-\frac{\alpha_hv_h}{\beta_h^2}. $$

Consequently the new constant term is exactly $S(0)$. It is nonzero because the score is strict on the complete cube. Divide the complete score by $|S(0)|$, which is positive, and absorb this factor into the $a_h$. The resulting sign-equivalent score has the form

$$ G_s(x)=s+\sum_{h=1}^H\frac{a_h\cdot x}{1+b_h\cdot x},\qquad s\in\lbrace-1,1\rbrace. $$

The denominators remain positive on the whole cube. Their coherent orientation is unchanged by positive scaling. The numerator transformation only subtracts a constant multiple of its denominator and rescales positively. At a constant denominator this leaves the numerator slopes unchanged up to positive scaling, so their original coherent-sign restriction is preserved. Thus this is an admissible transformation of the displayed heads, with no width overhead.

An original representation using the weak false-label convention can first be made strict by decreasing its free bias slightly. Finiteness of the cube guarantees a decrease smaller than every positive score. All false scores become strictly negative. No head changes in this strictification.

The two choices of $s$ are the only discrete choices required in this normalization. The $2nH$ real parameters are the coordinates of all $a_h,b_h$. For a capacity upper bound, forgetting their admissibility restrictions only enlarges the parameter family.

## Finite unrestricted count

For a fixed $s$, clear the positive denominator product. The resulting polynomial at a cube input is

$$ P_{s,x}(a,b)=s\prod_{h=1}^H(1+b_h\cdot x)+\sum_{h=1}^H(a_h\cdot x)\prod_{g\neq h}(1+b_g\cdot x). $$

It has total parameter degree at most $H$, including the first term because $s$ is fixed. There are $p=2nH$ continuous parameters. Warren's strict-sign estimate therefore gives the following finite result whenever $2nH\leq N$:

$$ |\mathcal F_{n,H}|\leq2\left(\frac{4eHN}{2nH}\right)^{2nH}=2\left(\frac{2eN}{n}\right)^{2nH}. $$

Here $\mathcal F_{n,H}$ contains every original-model truth table representable with at most $H$ heads. Zero-head padding makes the width exactly $H$ without changing the score. The estimate is a mathematical consequence of the standard [strict-sign theorem in Alon's survey, Proposition 5.4](https://web.math.princeton.edu/~nalon/PDFS/tools1.pdf). No margin, coefficient height, fixed dictionary, or noncancellation assumption is introduced.

Taking base-two logarithms yields

$$ \log_2|\mathcal F_{n,H}|\leq1+2nH\bigl(n-\log_2n+\log_2(2e)\bigr). $$

Therefore every positive integer $H$ satisfying $2nH\leq N$ and

$$ 1+2nH\bigl(n-\log_2n+\log_2(2e)\bigr)\lt N $$

is strictly smaller than the original worst-case head complexity $W(n)$. In particular this written argument gives

$$ W(n)\geq\left(\frac12-o(1)\right)\frac{2^n}{n^2}. $$

The new unconditional Lean declaration `HeadComplexity.NormalizedCounting.worstCase_real_lower` proves the concrete consequence, for every integer $n\geq8$,

$$ W(n)\geq\frac{2^n-1}{2n^2}. $$

The exact normalized count is `HeadComplexity.NormalizedCounting.card_le`, and the original-model bridge is `HeadComplexity.NormalizedCounting.mem_strictPatterns_of_computable`. The integer division form is `HeadComplexity.NormalizedCounting.worstCase_gt_div_all_large`.

This is only a constant improvement over a coarse finite count. The logarithmic and fixed-power targets remain open.

## The precise degree barrier survives

The width cancels from the base of the displayed count because $D=H$ and $p=2nH$. At $H=cN/n^{3/2}$ its logarithm divided by $N$ is asymptotic to $2c\sqrt n$. At $H=cN\log n/n^2$, using the natural logarithm in the width, the quotient is asymptotic to $2c\log n$. Both diverge for each fixed $c\gt0$.

Thus improving the normalization, eliminating redundant constants, and quotienting positive denominator scales cannot prove either target through this ordinary total-degree estimate. The first failing inequality would be an assertion that either divergent quotient stays below one.

## What the inherited positive matching construction actually costs

The exact construction in `origin/ar/7485202da367`, `artifacts/beyond-counting-bound/pole-matching-fibers.md`, uses $d=\lceil\log_2(2H)\rceil$ address coordinates and $k=n-d$ selector coordinates. It provides $(H!)^{k-1}$ regular positive interpolation branches, modulo a global head permutation, whenever its stated hypotheses hold.

The address budget implies

$$ k\leq\log_2(N/H)-1. $$

Since $\log_2(H!)\leq H\log_2H$, its certified branch count $B$ satisfies

$$ \log_2B\leq H\log_2H\bigl(\log_2(N/H)-2\bigr). $$

For $H=\lfloor cN/n^x\rfloor$ with fixed $c\gt0$ and $1\lt x\lt2$, this is $O_{c,x}(nH\log n)=o(N)$. More explicitly, eventually $H\geq cN/(2n^x)$, so $\log_2(N/H)\leq x\log_2n+\log_2(2/c)$ and $\log_2H\leq n$ whenever $H\leq N$.

This is an upper estimate on the number of branches supplied by that particular construction, not an upper bound on all positive interpolation fibers. It shows that the inherited example does not certify $\exp(\Theta(nH\log H))$ branches at the critical widths. Moreover every displayed score there is nonnegative, and positive whenever at least one selector bit is on. The many branches therefore share one Boolean sign table. Distinct real score tables and distinct interpolation branches must not be counted as distinct Boolean targets.

## A possible replacement lemma

A sufficient unrestricted statement would be an absolute-constant bound of the form

$$ \log_2|\mathcal F_{n,H}|\leq CnH\log_2\left(2+\frac{N}{nH}\right)+CH\log_2(H+1)\log_2\left(2+\frac NH\right). $$

At the widths relevant here this would be $O(nH\log n)$ and would yield an even stronger lower bound of order $N/(n\log n)$ after choosing a sufficiently small width constant. The inherited positive matching construction is compatible with this estimate. Ordinary Warren, multihomogeneous degree counting, and parameter dimension alone do not establish it.

One route to such a statement would bound the actual real sign-region topology of the positive-denominator evaluation map, using the Boolean input geometry. A bound on its complex degree, or a count of arbitrary interpolation branches without accounting for their signs, would require an additional argument. No such replacement lemma is proved in this note.
