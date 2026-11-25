# Final Primary Literature and Unrestricted Bound Audit

## Status

Audit completed during the final hour of the run, 2026-11-25 UTC. No audited source supplies the missing unrestricted logarithmic or fixed-power improvement. This is a report about the sources below, not a claim that no such theorem exists elsewhere.

The original definition of `HeadComplexity.worstCaseHeadComplexity` remains unchanged. Denominators may depend on the target, all real coefficients and signed cancellation remain allowed, and the full-cube relative-margin hypotheses have not been removed.

## Independent audit of the public lower bounds

The proof in `formalization/HeadComplexity/Research/BootstrapWeightedCounting.lean` gives, for every $n\geq256$,

$$ W(n)\geq\frac{2^n-1}{n(n+7)}\geq\left(1-\frac8n\right)\frac{2^n}{n^2}. $$

The exact declaration `BootstrapWeightedCounting.worstCase_real_leading_constant` and the public epsilon corollary `HeadComplexity.bootstrap_weighted_counting_worst_case_one_sub_epsilon` use the original unrestricted definition. This improves the leading constant at the existing quadratic scale. It is not a positive power saving or a logarithmic factor improvement.

The audit checked the weighted count at $H=1$, the separate argument when the Warren parameter range fails, positivity of logarithmic denominators, and the conversion from the logarithmic certificate to the explicit bound. In particular, the simplified count uses numerator weight $H$, so it has no division by $H-1$ at width one. The sharper weight $H-1$ estimate is only used with $H\geq2$.

`QuadraticScaleTypicalComplexity.card_le_exp_at_quadratic_budget` states that, for $n\geq8$, $H\gt0$, $u\leq1$, and $n^2H\leq u2^n$,

$$ \lvert F_H\rvert\leq\exp\left(\left(u+\frac{10}{n}\right)2^n\log2\right). $$

Here $F_H$ is the unrestricted representable truth-table class. Writing $U=n^2H/2^n$, the exact certificate has logarithm

$$ \log2+U2^n\log2+\frac{2^n}{n}U\bigl(\log(16e^2)-\log U\bigr). $$

The inequalities $\log(16e^2)\leq5$ and $-U\log U\leq1-U$ bound the last factor by $5$. The final slack uses $n\leq2^n$ and $5+\log2\leq10\log2$. The epsilon corollary assumes $\varepsilon n\geq20$. This audit found no missing hypothesis. The build and transitive axiom evidence are recorded in the run handoff, rather than inferred from this written audit.

## General real polynomial predicate bounds

[Goldberg and Jerrum, Theorem 2.2](https://www.cs.ox.ac.uk/people/paul.goldberg/papers/goldbergjerrum.pdf) bounds VC dimension by $2k\log_2(8eds)$ for a class described by a Boolean formula using $s$ polynomial predicates, $k$ real parameters, and total degree at most $d$. Clearing the positive denominators of an original score gives $k=O(nH)$, $d=O(H)$, and one strict sign predicate on the admissible parameter region. The resulting bound retains $O(nH\log H)$ complexity. Restricting parameters to admissible heads is legitimate, but the theorem supplies no special saving for observations on the full Boolean cube.

## Boolean threshold networks

[Kane and Williams, Theorem 2.3 and Corollary 2.1](https://cseweb.ucsd.edu/~dakane/depth2LTF.pdf) count top threshold gates applied to a fixed collection of Boolean-valued bottom functions. Combined with the count of bottom threshold gates, their counting lower bound for almost all Boolean functions is $\Omega(2^n/n^2)$. The fixed bottom outputs in that theorem are Boolean. Original rational heads output arbitrary real numbers, and their magnitudes affect signed cancellation, so replacing each head by its sign does not justify an application to the present model.

[Baldi and Vershynin, Theorem 3.1 and Corollary 8.4](https://arxiv.org/pdf/1901.00434) study networks of Boolean threshold gates. For architecture $(n,m,1)$ they obtain capacity of order $n^2m$ in their specified growth range. The shallow lower bound in Corollary 8.4 assumes $n\geq1.1\lceil\log_2m\rceil$. This condition eventually fails at $m=2^n/\mathrm{poly}(n)$. Thus even that Boolean-network lower capacity estimate cannot be extrapolated to the density relevant here. Its upper bound does not remove the quadratic-scale counting obstruction.

## Rational classifiers with a different decision rule

[Pardo and Sebastián, Corollary 5.13](https://arxiv.org/html/2504.11345v1) concerns an algebraically closed field and classifiers $\chi_{D(h)}$, where $D(h)$ is the set on which the numerator and denominator of a rational function are both nonzero. This is a zero versus nonzero decision rule, not a real positive versus negative decision rule. A strictly representing original score has nonzero numerator and denominator at every Boolean vertex, so its associated classifier of this kind is constant on the cube. The corollary therefore does not distinguish its truth table and cannot replace the strict-sign counting theorem used here.

## Algebraic geometry and recovery of rational networks

[Grosdos, Robeva, and Zubkov, Sections 3.2 and 4.3](https://arxiv.org/html/2509.11088v1) study reciprocal activation and represent a shallow network by its full formal numerator and denominator polynomials. Their recovery algorithm factors the denominator and then recovers the output coefficients. This input contains substantially more information than values or signs on the Boolean cube. Their relation with a projected Chow variety requires eliminating unobserved coefficients, with growing equation complexity explicitly discussed in Section 4.3. Neither the reconstruction statement nor the dimension calculations bound the number of Boolean sign extensions from a small observation set. Arbitrary affine head numerators also require an additional model comparison. No such bridge is inferred here.

## Exact rational degree

[Iyer et al., On the Rational Degree of Boolean Functions and Applications](https://arxiv.org/abs/2310.08004) define rational degree using exact equality to the Boolean function on the cube. They prove that almost every Boolean function has rational degree at least $n/2-O(\sqrt n)$. A strictly representing score in the present problem need only have the correct signs, not equal the labels. Moreover, clearing an original score of width $H$ already has degree $H$, so even a comparable sign-degree obstruction of order $n$ would not yield an exponential head lower bound. The exact rational-degree theorem is not an unrestricted capacity improvement for this model.

## Remaining theorem needed

A useful genuinely Boolean improvement would control the original representable class at dense widths with $nH\leq2^n$ by an entropy estimate such as

$$ \log_2\lvert F_H\rvert\leq CnH\left(1+\log\frac{2^n}{nH}+\log n\right), $$

or prove an admissible, truth-table preserving compiler with a sufficiently favorable width and margin tradeoff. The displayed entropy bound is a target, not a proved theorem. The sources audited above do not supply it. The finite margin estimates and the universal-low-margin quantifiers in the handoff still require an unrestricted access argument.
