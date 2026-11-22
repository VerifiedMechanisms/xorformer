# Beyond the Counting Bound

## Target and proof standard

Prove that the sequence $n^2W(n)/2^n$ is unbounded for the unchanged model in the attached `version-5.tex`.

$$ \forall C\gt0\qquad \forall n_0\qquad \exists n\geq n_0\qquad \exists f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace,\qquad H^{\ast}(f)\gt C\frac{2^n}{n^2}. $$

The desired conclusion is not an assumption in any argument. Denominators may depend on the target. Neither fixed-denominator dimension bounds nor exact real-table dimension bounds establish this Boolean sign-representation statement.

The source and start time are recorded in `run.json`. The attachment is outside this repository and is not modified.

## Initial audit

The manuscript's normalized score has a discrete sign and $2nH$ real parameters:

$$ S(x)=\sigma+\sum_{h=1}^H\frac{u_h\cdot x}{1+b_h\cdot x},\qquad \sigma\in\lbrace-1,1\rbrace. $$

Clearing denominators at each of the $2^n-1$ nonzero inputs gives parameter polynomials of degree $H$. The monomial $\sigma\prod_h b_{h,1}$ at $x=e_1$ proves that replacing this degree by the input dimension is invalid.

Warren's bound yields the exponent $1+2nHL_n$, where $L_n=\log_2(2e(2^n-1)/n)$. This proves the stated lower bound of order $2^n/n^2$ but no unbounded improvement factor.

The repository file `formalization/HeadComplexity/Results/CountingLowerBound.lean` makes the analytic theorem an explicit hypothesis named `WarrenStrictSignPatternBound`. Its finite reductions are formalized; Warren's theorem itself is not proved there. This distinction must remain visible in any new formalization.

## Approaches awaiting investigation

- Sharper sign counting for sums of fractions on the admissible positive-denominator domain.
- Positive reciprocal varieties, variation arguments, and constraints not captured by total parameter degree.
- Combinatorial or number-theoretic constructions forcing lower bounds uniformly over all denominator choices.
- Earlier research branches, audited for complete mechanisms and exact counterexamples to tempting shortcuts.

No theorem establishing the target has been proved at this checkpoint.

## First adversarial audit

**Counting refinements.** The two-block multidegree estimate recorded in the earlier `autoresearch-runs` commit `cc640ff`, theorem 217, has the form below, with an absolute constant $C$:

$$ \mathcal N(n,H)\leq\left(\frac{C4^n}{(n+1)^2H}\right)^{(n+1)H}. $$

Its source is the sign-condition estimate in [Basu and Rizzie, Theorems 12 and 13](https://arxiv.org/html/1507.03958). At $H=c2^n/n^2$, the logarithm of the displayed right side is $(c+o(1))2^n$. Thus the refinement still only excludes a bounded range of constants $c$. It cannot establish the selected target by itself. Status: blocked at the required unbounded improvement factor.

**Sparse algebraic counting.** [Rojas and Vidyasagar, Theorems 3 and 4](https://arxiv.org/html/math/0112208v3) replace total-degree bounds with normalized Newton volume and give an explicit block-degree entropy correction. A small degree in each head block does not alone eliminate the dependence on the number of blocks. No bound sufficient for this target has been obtained.

The direct [Newton-volume calculation](newton-volume-obstruction.md) shows that the common normalized parameter polytope has volume at least $(H/4)^{nH}$. This rules out a small-volume explanation for removing the logarithm. A method using more information than this volume would be a materially different approach.

**A misleading rational-network theorem.** [Pardo and Sebastian, Corollary 5.13](https://arxiv.org/html/2504.11345v1) concerns classifiers defined by the nonvanishing locus of rational functions over an algebraically closed field. Nonvanishing and positive-versus-negative classification are different predicates. Applying that theorem directly to the manuscript's real signs is invalid.

**Threshold-network capacity.** [Baldi and Vershynin, Theorem 3.1 and Section 10.3](https://arxiv.org/html/1901.00434) analyze threshold activations and impose a restriction on the growth of layer widths in their capacity lower bound. Their theorem neither applies to affine-ratio heads nor supplies a lower bound at the exponentially wide regime in question. A transfer of architectures would itself require a new proof.

**Margins and exact interpolation.** The manuscript's conditioning argument uses a positive normalized margin and a denominator contraction parameter bounded away from one. Neither is uniform over the allowed model. The regular-zero construction proves exact real-table interpolation with on the order of $2^n/n$ heads. Dimension counting for exact interpolation cannot exclude Boolean sign universality with fewer heads.

**Positive-domain oscillation.** The explicit construction in [reciprocal-oscillation.md](reciprocal-oscillation.md) gives $2^n-1$ positive zeros for a fixed linear functional along a one-head positive-denominator curve. Positivity alone therefore does not give the proposed low-oscillation shortcut. The generic identity and exact-zero statement have been proved in Lean.

**Existing complete counting formalizations.** The `xorformer-runs` commits `0fc32da` and `6f5c7d4` contain an unconditional strict Warren argument, with generic margins and constrained minima as major dependencies. The local manuscript-counting file remains conditional on its explicit Warren interface. Neither version yields the unbounded factor required here, so importing that development would not resolve the research objective.

## Second adversarial audit

**Real stability does not survive the needed quotient.** The earlier `xorformer-runs` commit `6195355` gives the following exact example. The admissible affine denominator $D=1/10+x+y+5z$ is real stable, whereas the Boolean reduction of its square is

$$ R=1/100+(6/5)(x+y)+26z+2xy+10xz+10yz. $$

It vanishes at $x=y=-13/10+i/10$ and $z=7/50+i/8$, all in the open upper half-plane. Direct symbolic rational arithmetic independently checked this zero and the Rayleigh value $-27/50$ at $(x,y,z)=(0,0,7/50)$. Thus stability of the unreduced denominator product does not provide the proposed invariant after Boolean reduction.

**Reciprocal-variety geometry.** [Kummer and Vinzant](https://arxiv.org/html/1610.04584) prove determinantal and hyperbolicity results for reciprocal linear spaces. [Rincon, Vinzant, and Yu, Proposition 3.10](https://arxiv.org/html/1907.08545) show that hyperbolicity passes to tangent spaces at real smooth points. Neither statement proves that sums of the manuscript's affine-ratio atoms retain a common hyperbolicity constraint. The required assertion for arbitrary signed numerators and target-dependent denominators is unproved. Status: blocked at a substantive geometric theorem, not a routine compatibility check.

**Finite candidate checks.** [experiments.md](experiments.md) specifies the exact admissible certificates and their independent integer verifier. In particular, a seven-point code support on eight bits has a four-head certificate, refuting the proposed isolated-support counting argument. Numerical failures were not used as evidence of infeasibility.

**Other reductions rejected as incomplete.** Fixed-denominator span dimension, full real-table interpolation dimension, the exact dual-certificate alternative, low-degree antipodal projections, and a proposed compression to sparse polynomial signs do not supply a lower bound for every allowed representation at the required scale. No general sparse-sign compression theorem has been proved here. Rephrasing the target through such an unproved assertion does not constitute a new proof mechanism.

The original target, architecture, denominator freedom, and worst-case definition have not been changed. No Lean declaration or paper proof establishing the selected asymptotic refutation exists in this work so far.

## Resumed audit: positive interpolation fibers

The first turn ended before the requested twelve hours. Research resumed on November 22 following the asker's correction. The target remains unproved and the duration requirement remains outstanding.

A new test concerned a possible way to remove the degree factor in sign counting: uniqueness, up to head permutations, of positive-denominator interpolation from as many cube evaluations as there are effective parameters. That proposed uniqueness statement is false. The computer-assisted theorem in [positive-fiber-obstruction.md](positive-fiber-obstruction.md) gives two regular, distinct two-head representations agreeing on 21 vertices of the five-bit cube. Their scores differ by more than $1/10$ at two other vertices. The inverse function theorem makes the ambiguity persist on an open set of interpolation data. Two independent exact rational verifiers check the contraction and separation certificates. A weaker quantitative bound on positive branches is not ruled out, but has not been proved.

[Zhang, Zhang, Loh, and Liang](https://arxiv.org/html/2201.13132v2) establish generic identifiability for particular two-component ranking mixtures. Those models have coupled probability numerators and substantially more structured observations; their theorem does not establish uniqueness for the manuscript's arbitrary affine numerators. The counterexample above directly tests the latter model.

[Grosdos, Robeva, and Zubkov](https://arxiv.org/html/2509.11088v1) study rational-function identities and coefficient varieties for reciprocal-activation networks. Their ambient space is a space of polynomial fractions, rather than Boolean sign tables. Their dimension and defining-equation results do not imply the selected lower bound.

[Zhang and Kileel](https://arxiv.org/html/2311.05116v3), Theorem 2.6, bound metric entropy using intrinsic dimension, section-component counts, and a logarithmic ambient-dimension term. Their rational-network application controls continuous outputs and Lipschitz losses. The resulting ambient-size logarithm and the absence of a uniform margin prevent a direct improvement of the unrestricted Boolean counting bound.
