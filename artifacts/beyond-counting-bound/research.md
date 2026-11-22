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
