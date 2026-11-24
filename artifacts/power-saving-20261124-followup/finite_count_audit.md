# Finite margin capacity audit with head overhead

## Status

The finite theorem in [the inherited note](../power-saving-20261124/margin_sensitive_polynomial_capacity.md) is valid. Both requested high-margin counting estimates follow from that theorem, with explicit constants and a common sufficient threshold. Neither estimate bounds the number of all unrestricted representable truth tables.

The arguments below are written proofs. The table of Lean ingredients identifies what the kernel checks already establish. In particular, neither Warren's theorem nor the whole finite margin count is currently a kernel-checked theorem.

All logarithms in this note are natural. Write $N=2^n$. The margin denominator is exactly

$$ M=|b|+\sum_{h=1}^H\|\phi_h\|_\infty,\qquad \|\phi_h\|_\infty=\max_{x\in\lbrace0,1\rbrace^n}|\phi_h(x)|. $$

Thus the norm is taken on the entire Boolean cube, separately for each head, before summing. Cancellation in the score does not reduce this denominator.

## Audit of the model and finite theorem

An original atom has positive parameters $\gamma,\alpha,\rho_i$ and unrestricted real parameters $\eta,\delta,m_i$. On the Boolean cube its denominator and numerator are the affine functions

$$ B(x)=\gamma+\sum_i\rho_i+(\alpha-1)\sum_i\rho_i x_i,\qquad A(x)=\eta+\sum_i\rho_i m_i+\sum_i\rho_i\bigl((\alpha-1)m_i+\alpha\delta\bigr)x_i. $$

Every denominator slope therefore has the sign of $\alpha-1$. Every denominator value is positive. If $\alpha=1$, the numerator slopes are $\delta\rho_i$, so they too have a common strict sign or are all zero. The inherited proof may enlarge this numerator class when counting, which can only increase its upper count. Nothing forces different heads to use the same denominator, orientation, coefficient order, or parameter values.

Reflecting every coordinate for a negative-slope head, separately inside that head, gives

$$ B(y)=b_0+\sum_{i=1}^n b_i y_i,\qquad b_0\gt0,\qquad b_i\geq0. $$

The reflected constant is the original denominator at its minimizing vertex. It is positive without a coefficient-size bound. Selecting the largest present coefficient gives $q(x)\gt0$ and

$$ 1\leq B(x)/q(x)\leq n+1. $$

The constant coefficient is always present. Zero slope coefficients in the constant-denominator case therefore cannot be selected. A fixed coefficient order and fixed orientation determine the selected index at every input, including all ties under a fixed tie convention. There are at most $2(n+1)!$ charts per head.

For $d=\lceil(n+1)\log(2/\gamma)\rceil$, the geometric polynomial has pointwise error at most $(\gamma/2)|\phi_h(x)|$. This is relative error against the actual head value, so arbitrary signed numerator coefficients and cancellation remain allowed. Summing errors gives at most $\gamma M/2$. Every score with relative margin at least $\gamma$ retains its entire strict sign table after the replacement.

For each head, the affine numerator, affine denominator, and formal reciprocals of its coefficients contribute $3(n+1)$ real parameters. The latter reciprocals are treated as independent parameters only to enlarge the counted family. The one output bias gives

$$ p=1+3(n+1)H,\qquad D=2d+2. $$

For every fixed input, the replacement score is a polynomial in those parameters of total degree at most $D$. The choices of selected indices are fixed before this polynomial is defined. No rational function remains in these parameter polynomials.

[Alon's Proposition 5.4](https://web.math.princeton.edu/~nalon/PDFS/tools1.pdf), checked directly at printed pages 14–15, states Warren's strict-sign estimate with the constant and range used here: $N$ real polynomials of degree at most $D$ in $p$ real variables have at most $(4eDN/p)^p$ strict sign patterns when $N\geq p$. The approximation already makes all scores strict, so the version that counts zero coordinates is unnecessary. The resulting finite estimate is

$$ T(n,H,\gamma)\leq\bigl(2(n+1)!\bigr)^H\left(\frac{4eDN}{p}\right)^p,\qquad p\leq N. $$

Here $T$ counts truth tables admitting at least one admissible representation of width at most $H$ with the specified margin. Zero atoms pad smaller widths without changing $M$ or the score.

The original Lean classifier uses a strict inequality only for the true class. On a finite cube, its bias can be shifted so that false inputs also have strictly negative score, with no additional heads. This strictification gives some positive margin, but gives no uniform quantitative lower margin. Consequently it cannot be used to drop the margin hypothesis from $T$.

## A direct finite estimate covering both scales

### Theorem 1. Constant and additive head overhead

Let $n\geq32$, let $C\geq1$ be real, let $B\geq0$ be an integer, and suppose

$$ \log(n+1)\leq t\leq n,\qquad \frac{(B+1)n^2}{2^n}\leq\frac1{500}. $$

Define the original width budget, the enlarged width budget, and the test margin by

$$ H=\left\lfloor\frac{N}{100C nt}\right\rfloor,\qquad K=\lceil CH\rceil+B,\qquad \gamma=\exp(-\exp(t)). $$

Then at most $2^{N/2}$ Boolean truth tables admit a representation of width at most $K$ and relative margin at least $\gamma$. More precisely,

$$ \log T(n,K,\gamma)\leq\frac{1011}{4000}N\lt\frac{\log2}{2}N. $$

**Proof.** If $K=0$, only the two constant sign tables occur, and the conclusion is immediate. Suppose $K\geq1$. The ceilings and additive overhead give

$$ \frac KN\leq\frac1{100nt}+\frac{B+1}{N}\leq\frac3{250nt}. $$

The last inequality uses $t\leq n$ and the displayed overhead assumption. The parameter count therefore satisfies

$$ \frac{pt}{N}=\frac tN+3(n+1)\frac{Kt}{N}\leq\frac1{500n}+\frac9{250}\left(1+\frac1n\right)\leq\frac1{25}. $$

Thus $p/N\leq1/(25t)\leq1$, verifying Warren's dimensional hypothesis. Since $\log(2/\gamma)=\log2+e^t$, the degree satisfies

$$ D\leq2(n+1)(\log2+e^t)+4\leq6(n+1)e^t. $$

The last inequality follows from $n\geq1$, $t\geq0$, and $\log2\leq1$. The function $u\mapsto u\log(4eDN/u)$ is increasing for $0\lt u\leq N$, because its derivative is $\log(4eDN/u)-1\gt0$. Applying the finite theorem and replacing $p$ by $N/(25t)$ gives

$$ \frac{\log T}{N}\leq\frac3{250nt}\bigl(\log2+(n+1)\log(n+1)\bigr)+\frac1{25t}\bigl(t+\log(600e(n+1)t)\bigr). $$

For $n\geq32$ and $t\leq n$, we have $600e\leq(n+1)^3$ and consequently

$$ \log(600e(n+1)t)\leq5\log(n+1). $$

Using $\log(n+1)\leq t$, $\log2\leq\log(n+1)$, and $n\geq32$ now gives

$$ \frac{\log T}{N}\leq\frac1{25}+\frac15+\frac3{250}\left(1+\frac2n\right)\leq\frac{1011}{4000}. $$

Finally $\log2\geq2/3$, for example by the integral form of the midpoint inequality for the convex function $1/x$ on $[1,2]$, so the claimed strict comparison follows. $\blacksquare$

The condition on $B$ holds eventually for every fixed additive overhead. If $B=0$, it holds for every $n\geq32$: the sequence $n^2/2^n$ decreases for $n\geq3$, and its value at $32$ is less than $1/500$.

### Corollary 2. The aimed power scale

Take $t=\sqrt n$ and $c=1/(100C)$. Theorem 1 applies to

$$ H=\left\lfloor\frac{cN}{n^{3/2}}\right\rfloor,\qquad K=\lceil CH\rceil+B,\qquad \gamma=\exp(-\exp(\sqrt n)). $$

The inequality $\log(n+1)\leq\sqrt n$ holds for all real $n\geq1$: the difference has nonnegative derivative and is positive at $1$. Also $\sqrt n\leq n$. Hence the high-margin count is at most $2^{N/2}$ for every sufficiently large $n$, and for every $n\geq32$ when $B=0$.

### Corollary 3. The logarithmic fallback scale

Take $t=n/\log n$ and $c=1/(100C)$. Theorem 1 applies directly to

$$ H=\left\lfloor\frac{cN\log n}{n^2}\right\rfloor,\qquad K=\lceil CH\rceil+B,\qquad \gamma=\exp\left(-\exp\left(\frac n{\log n}\right)\right). $$

For $n\geq32$, we have $\log n\geq1$ and

$$ \log(n+1)\leq\sqrt n\leq\frac n{\log n}\leq n. $$

Thus the high-margin count is at most $2^{N/2}$ under exactly the same overhead condition. This is a substitution into the finite formula, not an application of the inherited fixed-exponent corollary with an exponent depending on $n$.

For comparison, at either scale the sharp leading term from the inherited finite formula is

$$ \limsup_{n\to\infty}\frac{\log_2 T(n,\lceil CH\rceil+B,\gamma)}{N}\leq\frac{3Cc}{\log2}. $$

Indeed $p/N=(3Cc+o(1))/t$, $\log D=t+O(\log n)$, the chart contribution divided by $N$ is $O(Cc\log n/t)$, and $\log(N/p)=O(\log n)$. Both choices of $t$ satisfy $\log n/t\to0$, while all fixed additive overhead terms vanish exponentially. Any fixed $c\lt(\log2)/(6C)$ therefore works eventually. The explicit constant above is chosen to make the finite bookkeeping simple.

## Existing kernel-checked ingredients

The following declarations are present in the required starting revision. The listed files are relative to `formalization/HeadComplexity/`.

| Ingredient | Declaration | File | Scope |
| --- | --- | --- | --- |
| Original head readout to exact atom | `head_readout_eq_eval`, `fracComputable_of_computable` | `Atoms/HeadToFracAtom.lean` | Exact original-model reduction, no width loss |
| Atom to original heads | `computable_of_fracComputable` | `Atoms/FracAtomHead.lean` | Keeps every atom admissible |
| Affine numerator and denominator | `FracAtom.eval_eq_numPoly_div_denPoly`, `FracAtom.denPoly_pos`, degree lemmas | `Atoms/AtomPolynomials.lean` | Pointwise identity and positive denominator |
| Same-width strictification | `exists_strict_fracCertificate` | `Atoms/ClearedNormalForm.lean` | Some strict margin, no uniform margin bound |
| Zero-atom padding | `FracAtom.zero_eval`, `FracAtom.sum_pad_eval` | `Atoms/FracComputableMonotone.lean` | Exact same score at larger width |
| Maximum-coefficient sum bound | `selected_max_sum_bounds` | `Research/ConditionedReciprocalApproximation.lean` | Assumes a nonnegative finite family and selected maximum |
| Exact geometric error | `exact_error` | `Research/ConditionedReciprocalApproximation.lean` | Scalar algebra with nonzero denominator factors |
| Relative error estimate | `geometric_relative_error`, `exponential_relative_error` | `Research/ConditionedReciprocalApproximation.lean` | Assumes positive selected coefficient and two-sided conditioning |
| Sign preservation | `sign_preserved_of_relative_error`, `conditioned_score_preserves_sign` | `Research/ConditionedReciprocalApproximation.lean` | Explicit positive margin, full-amplitude bounds, and degree hypothesis |
| Unrestricted clearing and parameter degree | `countingClearedPoly_totalDegree_le`, `card_headComputableFunctions_le_strictPatterns` | `Results/CountingLowerBound.lean` | Unconditional reduction, with degree depending on width |
| Existing counting lower bound interface | `worstCaseHeadComplexity_gt_div_of_warren` | `Results/CountingLowerBound.lean` | Requires `WarrenStrictSignPatternBound` as an explicit hypothesis |

The selected maximum theorem does not by itself construct coefficient-order charts from an original atom. The approximation declarations do not define the full-cube supremum, quantify over all representations, count charts, prove Warren, or derive either asymptotic lower bound. Their hypotheses are precisely where the written proof supplies these objects and inequalities.

The existing lower bound declaration is kernel checked as an implication with the stated Warren premise. That premise is a proposition argument, not a new Lean axiom, so a clean transitive axiom list does not mean that Warren or an unconditional exponential lower bound has been formalized.

## Quantifiers still needed for an unrestricted conclusion

Let $\mathcal R_H$ be the truth tables representable by at most $H$ original heads. Let $\mathcal G_{K,\gamma}$ be those admitting some admissible representation of width at most $K$ and margin at least $\gamma$. Define

$$ \mathcal B_{H,K,\gamma}=\lbrace F\in\mathcal R_H:\ \text{every admissible representation of }F\text{ of width at most }K\text{ has margin less than }\gamma\rbrace. $$

Here representations in the universal quantifier may use completely new denominators and arbitrary real coefficients. When $K\geq H$, the two disjoint sets satisfy

$$ \mathcal R_H=(\mathcal R_H\cap\mathcal G_{K,\gamma})\mathbin{\dot\cup}\mathcal B_{H,K,\gamma},\qquad |\mathcal R_H|\leq T(n,K,\gamma)+|\mathcal B_{H,K,\gamma}|. $$

The high-margin count controls only the first term. A same-truth-table repair with constant head overhead would make the second set empty. A separate bound strictly below $2^N-2^{N/2}$ would also suffice. No such repair or bound is established here. An arbitrarily ill-conditioned individual representation, a small-margin family with one label table, or a count that fixes the denominators does not estimate this second term.

## Render verification

The static checker and KaTeX validation passed for all 111 source math spans. A direct call to GitHub's Markdown API rendered exactly 111 math spans, with no residual delimiters or double-escaped payloads. The one control-space note corresponds to the intentional space following the colon in the definition of the bad set. The `gh` and `glab` executables are unavailable in this checkout; GitHub was audited through its API with repository-scoped credentials, and the GitLab render audit was not run.
