# Monomial Star Covers and Universal Head Bounds

## Statement

Keep the single-layer attention-only model and $H^{\ast}$ unchanged. Write $d=\deg_{\pm}(f)$ and $W(n)=\max_f H^{\ast}(f)$.

For every $n\gt0$ and every Boolean function on $n$ inputs,

$$ H^{\ast}(f)\leq \frac{11\cdot2^n}{n}, \qquad W(n)\leq\frac{11\cdot2^n}{n}. $$

This strengthens the pre-existing universal bound $2^n-1$ from core theorem 9. The unconditional integer result takes the minimum with every intermediate endpoint, so it also preserves dimension zero and all smaller earlier universal budgets.

For every $n\gt0$ and every certificate of threshold degree at most $D$,

$$ H^{\ast}(f)\leq G(n,D), \qquad G(n,D)=\sum_{r=0}^{D-1}\binom{n-1}{r}. $$

The empty sum is zero. Core theorem 6 consequently strengthens to the unconditional sandwich

$$ d\leq H^{\ast}(f)\leq G(n,d). $$

In particular, quadratic threshold functions need at most $n$ heads and cubic threshold functions need at most $1+\binom n2$ heads. The result for $D=2$ improves the old degree-sensitive support budget $1+\binom n2$ to $n$; on eight inputs the budgets are $29$ and $8$.

These are uniform bounds. Specialized existing theorems can give smaller values for particular functions or dimensions.

## Proof

### Theorem 1. One head for an affine block on a positive face

For a coordinate set $S$, let $x_S=\prod_{i\in S}x_i$. One genuine fractional attention atom uniformly approximates

$$ x_S\left(c+\sum_i a_i x_i\right) $$

to any positive tolerance. Its numerator is the whole affine expression. Its denominator is

$$ 1+\sum_{i\in S}R(1-x_i)+\sum_{i\notin S}\delta(1-x_i). $$

Choose $R$ large and $\delta$ small. On the positive face, the denominator tends to one. Outside it, at least one $R$ term suppresses the numerator uniformly. All denominator slopes are strictly negative, so the existing negative-affine-ratio realization gives a genuine `FracAtom`. Finite strict margins allow one such atom per block to replace a strict sign polynomial without changing its labels. The existing fractional-normal-form bridge then realizes these atoms in the actual attention model.

The Lean declarations are `exists_fracAtom_approx_monomial_mul_affineValue` and `SquarefreePolynomial.computableWithHeadsN_of_starCover`.

### Theorem 2. Degree-sensitive stars

A center $S$ covers the monomials with supports $S$ and $S\cup\lbrace i\rbrace$. Assigning all covered terms to their center makes one affine block times $x_S$.

Take every center of size $D-1,D-3,\ldots$. Every nonconstant monomial of degree at most $D$ is either a center or becomes one after deleting one coordinate. Thus the number of heads is at most

$$ \sum_{\substack{0\leq r\lt D\cr r\equiv D-1\pmod 2}}\binom nr = \sum_{r=0}^{D-1}\binom{n-1}{r}. $$

The identity follows from Pascal's rule in steps of two. A constant coefficient is a free classifier bias. All polynomial coefficients assigned to one star are combined before approximation.

The Lean declarations are `HStar_le_starDegreeBound_of_ThresholdDegLE`, `starDegreeBound_eq_sum_pred_choose`, and `thresholdDeg_le_HStar_le_starDegreeBound`.

At ambient degree the alternating family has $2^{n-1}$ centers. This already strictly improves the original universal numerical budget in every dimension at least two.

### Theorem 3. Finite alteration and the logarithmic intermediate bound

Select each possible center independently with probability $p\in[0,1]$. A monomial with support $T$ has exactly $\lvert T\rvert+1$ possible covering centers. Add one center for each uncovered monomial. Finite weighted averaging gives a cover of size at most

$$ 2^n p+\sum_{T\subseteq[n]}(1-p)^{\lvert T\rvert+1}=2^n p+(1-p)(2-p)^n. $$

All weights are finite products of $p$ and $1-p$, whose sum is exactly one. The proof also covers the two endpoint probabilities. No probabilistic estimate is assumed.

Using $(1-p/2)^n\leq\exp(-np/2)$ and the admissible rate $p=2\log(n/2)/n$, for $n\geq2$ one obtains

$$ H^{\ast}(f)\leq L(n), \qquad L(n)=\frac{2\cdot2^n(\log(n/2)+1)}{n}. $$

The Lean declarations are `HStar_real_le_bernoulliStarBudget` and `HStar_real_le_logarithmicStarBudget`. This intermediate result also proves $W(n)/2^n\to0$, formalized as `tendsto_worstCaseHeadComplexity_div_two_pow`.

### Theorem 4. Discounted repairs remove the logarithm

Let $K(n)$ be the minimum size of a full upward star cover. A partial cover on one block consists of selected centers $S$ and uncovered monomials $T$. If $C$ covers the other block, the combined centers are

$$ (S\mathbin{\oplus}Q_m)\cup(T\mathbin{\oplus}C). $$

A selected first-block center can pair with every second-block monomial. An uncovered first-block monomial can instead pair with a center from $C$. Thus the repair cost is discounted by $\lvert C\rvert/2^m$.

This is a radius-one adaptation of the semidirect covering construction of [Cooper, Ellis, and Kahng, Section 2.1](https://arxiv.org/abs/math/0309081). The construction, its size bound, and the resulting attention compilation are proved in Lean here, rather than assumed from that paper.

Finite weighted alteration and the semidirect construction give the exact recurrence

$$ K(a+b)\leq2^{a+b}p+K(b)(1-p)(2-p)^a. $$

Take $a=\lfloor n/2\rfloor$, $b=n-a$, and $p=7/(2a)$. For $n\geq74$, one has $a\geq37$ and $b\geq a$. The exponential series through degree six proves

$$ \exp(-7/4)\leq7/40. $$

Assuming the inductive bound on the smaller block, the recurrence gives

$$ K(n)\leq2^n\left(\frac{7}{2a}+\frac{11}{a}\cdot\frac7{40}\right)=2^n\frac{217}{40a}\leq\frac{11\cdot2^n}{n}. $$

The last inequality uses $n\leq2a+1$ and $a\geq37$. For $2\leq n\lt74$, the already proved logarithmic cover bound is at most $11\cdot2^n/n$, because $\log(n/2)\leq\log64=6\log2\leq9/2$. Dimension one is immediate. Strong induction closes the proof.

The main Lean declarations are `monomialStarCoverNumber_block_recurrence`, `monomialStarCoverNumber_real_le_eleven`, and `HStar_real_le_eleven_mul_two_pow_div`.

## Certified strict improvement

The [certification report](../../artifacts/theorem-subsumption/star-strengthenings.md) gives eight comparisons using the pinned theorem-subsumption tool. Each check proves both directions of requirement alignment, proves the forward context-free guarantee implication, and refutes the reverse guarantee implication with an explicit Lean proof. Every normalized head count has a checked bridge to the unchanged `HStar`.

The final integer theorem `HStar_le_universalElevenStarBound` preserves the original universal bound, the half-cube bound, and the full rounded logarithmic bound. The new real endpoint is strictly smaller than $L(n)$ for every $n\geq256$. The natural-budget comparison also has an exact strict witness at $n=256$.

## Open directions

The argument gives an upper bound, not an exact worst-case head complexity. The existing counting lower bound still carries its explicit Warren-estimate premise. A matching unconditional lower bound and a universal fixed-denominator span at the dimension-count threshold remain open in this development. The constant $11$ is not claimed optimal.
