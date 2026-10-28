# Certified Atomic-Margin Strengthenings

## Prior Result and Strengthenings

The starting point is the refined theorem 195 bound in [`AtomicMarginRefinement.lean`](../../formalization/HeadComplexity/Results/AtomicMarginRefinement.lean), with sample constant two and real coefficient three. Let $N=2^n$, $r=\Lambda/\gamma$, and $\kappa=\kappa_{\mathrm{atom}}(f)$. Every result below uses the same attention model and genuine fractional atoms as that result.

### Theorem 1. Exact entropy and integer bounds

Under exactly the original atomic-margin certificate hypotheses,

$$ H^{\ast}(f)\leq \left\lfloor 2n\log 2 r^2\right\rfloor+1, \qquad H^{\ast}(f)\leq (2n\log 2+1)r^2. $$

For nonconstant functions the literal infimum satisfies

$$ H^{\ast}(f)\leq (2n\log 2+1)\kappa^2. $$

The integer endpoint is strictly smaller than the refined endpoint $\lceil2(n+1)r^2\rceil$ for every genuine nonconstant certificate. The homogeneous real endpoint is strictly smaller than $3(n+1)r^2$ for every genuine certificate. The unconditional integer theorem takes the minimum with the previous endpoint, preserving constant-function certificates with very small ratios.

The declarations are `AtomicMarginCertificate.HStar_le_min_entropy_refined`, `AtomicMarginCertificate.HStar_real_le_atomicCondition_entropy`, and `HStar_real_le_atomicConditionNumber_entropy` in [AtomicMarginEntropy.lean](../../formalization/HeadComplexity/Results/AtomicMarginEntropy.lean).

**Proof.** The refined sampling rule only needs

$$ N\exp\left(-\frac{m}{2r^2}\right)\lt1. $$

Retain $\log N=n\log 2$ exactly and choose the first integer strictly larger than $2r^2\log N$. The full strict-margin compiler then applies. For nonconstant functions $r\geq1$, so the one rounding unit is at most $r^2$. The square-root lower-bound argument passes the homogeneous inequality to the infimum without requiring attainment. $\blacksquare$

### Theorem 2. Local signed-margin budgets

For a fixed original certificate define its actual margins

$$ s_x=y_x(c+\Lambda u_x)\geq\gamma. $$

It is sufficient for a positive integer $m$ that

$$ B_{\mathrm{profile}}(m)=\sum_x\exp\left(-\frac{m s_x^2}{2\Lambda^2}\right)\lt1. $$

Then $H^{\ast}(f)\leq m$. This condition contains every instance of the uniform sufficient condition, since

$$ B_{\mathrm{profile}}(m)\leq N\exp\left(-\frac{m\gamma^2}{2\Lambda^2}\right). $$

The declarations are `AtomicMarginCertificate.computableWithHeadsN_of_profile_budget` and `AtomicMarginCertificate.HStar_le_of_profile_budget` in [AtomicMarginProfile.lean](../../formalization/HeadComplexity/Results/AtomicMarginProfile.lean).

**Proof.** Apply the independent-sampling tail estimate separately with error allowance $s_x/\Lambda$. Sum these individual tail estimates before testing whether the budget is below one. The empirical signed score is strictly positive at every input. The actual selected atoms, with their sample coefficients absorbed into readouts, give the original attention model. $\blacksquare$

### Theorem 3. Canonical output ranges

At each input define the smallest enclosing interval of atom outputs by

$$ l_x=\min_j a_j(x), \qquad h_x=\max_j a_j(x), \qquad c_x=\frac{l_x+h_x}{2}, \qquad R_x=\frac{h_x-l_x}{2}. $$

The normalized outputs ensure $0\leq R_x\leq1$. A sufficient condition is now

$$ B_{\mathrm{range}}(m)=\sum_{x:R_x\gt0}\exp\left(-\frac{m s_x^2}{2\Lambda^2 R_x^2}\right)\lt1. $$

Again $H^{\ast}(f)\leq m$, and the new budget is at most the profile budget and therefore at most the uniform budget. Zero-width inputs consume no budget: their outputs are identical under every sampled atom. The canonical half-width is proved minimal among all enclosing intervals, including intervals with arbitrary input-dependent centers.

The main declarations are `AtomicMarginCertificate.HStar_le_of_tightRange_budget`, `tightOutputRange_radius_minimal`, and `tightRangeBudget_le_uniformBudget` in [AtomicMarginRange.lean](../../formalization/HeadComplexity/Results/AtomicMarginRange.lean).

**Proof.** Apply the profile sampler to centered outputs divided by their positive radii. Centers cancel exactly from the difference between the mean and the sample. Restrict the probabilistic argument to positive-width coordinates; every remaining coordinate has exactly zero sampling loss. The centers are analytical auxiliaries. They add no operations or parameters to the attention model. $\blacksquare$

### Theorem 4. A one-head neighborhood and stronger invariant lower bounds

For every nonconstant function, hence $n\geq1$,

$$ \kappa\lt\frac{N}{N-1}\quad\Longrightarrow\quad H^{\ast}(f)\leq1. $$

Equivalently,

$$ H^{\ast}(f)\geq2\quad\Longrightarrow\quad \kappa\geq\frac{N}{N-1}\gt1. $$

If the labels are balanced, $\sum_x y_x=0$, and $n\geq2$, the stronger bound is

$$ H^{\ast}(f)\geq2\quad\Longrightarrow\quad \kappa\geq\frac{N}{N-2}. $$

In particular, the actual invariant of two-bit XOR satisfies $\kappa_{\mathrm{atom}}(\mathrm{PARITY}_2)\geq2$, improving the pre-existing endpoint one.

The declarations are `HStar_le_one_of_atomicConditionNumber_lt_gap`, `one_add_gap_le_atomicConditionNumber_of_two_le_HStar`, and `balanced_atomicConditionNumber_lower_bound` in [AtomicConditionGap.lean](../../formalization/HeadComplexity/Results/AtomicConditionGap.lean). `atomicOneHeadGap` uses $1/\max\lbrace1,N-1\rbrace$ to define the otherwise irrelevant zero-dimensional case. The explicit XOR lower bound is `xor2_atomicConditionNumber_ge_two` in [AtomicConditionGapSubsumption.lean](../../formalization/HeadComplexity/AtomicConditionGapSubsumption.lean).

**Proof.** Write the total label deficit of an individual atom as

$$ D_j=\sum_x(1-y_x a_j(x))\geq0. $$

If $D_j\lt2$, every true input has strictly larger atom output than every false input. Otherwise a reversed true/false pair alone contributes at least two to the deficit. Choose a threshold between the two output classes. That single existing atom computes the function.

Nonconstancy and normalization imply $|c|\leq\Lambda-\gamma$. Therefore

$$ \mathbb E D_j\leq2N\left(1-\frac{\gamma}{\Lambda}\right). $$

A ratio $r\lt N/(N-1)$ makes this expectation strictly less than two, so some atom has deficit below two. For balanced labels the bias terms cancel and the sharper estimate is

$$ \mathbb E D_j\leq N\left(1-\frac{\gamma}{\Lambda}\right). $$

If the function needs two heads, every atom has deficit at least two. The latter estimate gives $r\geq N/(N-2)$. Taking lower bounds over all finite certificates proves both invariant bounds. For the open one-head criterion, an infimum below the cutoff has a realized certificate below the cutoff. No minimizing certificate is assumed. $\blacksquare$

## Strictness and Theorem-Subsumption Certificates

All comparisons use the project's pinned `theorem-subsumption` revision `112d2d977cb3c1daa452a9ed6db6561fd025f128`. Elaboration asserts every status and the classification `source strictly subsumes target under this alignment`. The comparisons run in logical mode; contextual adapters are not attempted or counted as improvements.

| Comparison module | Improvement | Requirements, old to new / new to old | Guarantees, new to old / old to new |
| --- | --- | --- | --- |
| [AtomicEntropySubsumption.lean](../../formalization/HeadComplexity/AtomicEntropySubsumption.lean) | Real bound | `PROVED` / `PROVED` | `PROVED` / `REFUTED` |
| Same module | Integer bound | `PROVED` / `PROVED` | `PROVED` / `REFUTED` |
| [AtomicProfileSubsumption.lean](../../formalization/HeadComplexity/AtomicProfileSubsumption.lean) | Profile applicability | `PROVED` / `REFUTED` | `PROVED` / `PROVED` |
| [AtomicRangeSubsumption.lean](../../formalization/HeadComplexity/AtomicRangeSubsumption.lean) | Canonical range applicability | `PROVED` / `REFUTED` | `PROVED` / `PROVED` |
| [AtomicConditionGapSubsumption.lean](../../formalization/HeadComplexity/AtomicConditionGapSubsumption.lean) | Joint invariant lower bounds | `PROVED` / `PROVED` | `PROVED` / `REFUTED` |

The entropy comparisons reuse the existing sampling contract, with its checked bridge from actual certificates. The profile and range comparisons expose the two budgets and their proved domination. Their sampling-rule fields are supplied by the new compiler proofs. Separate target bridges call the refined uniform compiler directly. The condition-gap comparison exposes a scalar together with the exact requirement that it equals `atomicConditionNumber`; both sides require precisely the same equality and nonconstancy assumption.

Context-free reverse refutations may use scalar tuples that do not satisfy those requirements. For example, the gap comparison does not claim that two-bit parity has condition number one. The following additional proofs establish actual strict improvement, beyond abstract contract comparisons:

- `certificate_real_endpoints_strict` applies to every genuine certificate. `certificate_natural_endpoints_strict` applies to every genuine nonconstant certificate.
- `tightOrCertificate` is a genuine nonconstant two-bit OR certificate with scale five, margin one, and normalized atom output $(2x_0+4x_1-1)/5$. Its actual signed margins are $1,1,3,5$, so the certified global margin is attained.
- At fifty samples its profile budget is $2e^{-1}+e^{-9}+e^{-25}\lt1$, while the old uniform budget is $4e^{-1}\gt1$. These inequalities are proved with rational bounds on the exponential, not floating point experiments.
- The same certificate has zero output widths, so its canonical range budget is zero already at one sample, while the old uniform budget still fails. This is an improvement of the sampling certificate; OR's one-head complexity was already known.
- `actual_gap_endpoints_strict` and `parity_atomicCondition_gap` prove strict lower endpoints on actual functions needing at least two heads. The balanced argument gives the explicit actual XOR bound two.

## Definitions and Existing Statements

`HStar`, the attention model, `FracAtom`, the original certificate structures, `atomicConditionNumber`, and all existing public theorem signatures are preserved. `AtomicSampling.lean` generalizes its implementation to coordinatewise thresholds and enclosing output intervals; its uniform theorems remain wrappers with unchanged types. New definitions record entropy sample counts, local margins, budgets, output extrema, canonical ranges, and the one-head gap. The new results are exported alongside the existing results in `Results/All.lean`.

## Reproduction

Use the pinned Lean 4.31.0, Mathlib v4.31.0, and theorem-subsumption dependency. From the repository root:

```sh
bash artifacts/scripts/validate_atomic_strengthenings.sh
bash artifacts/scripts/validate.sh
npm install --no-save --package-lock=false katex
python3 artifacts/scripts/check_md_math.py --katex artifacts/theorem-subsumption/atomic-strengthenings.md formalization/README.md theorems/02_complexity_measure_upper_bounds/195_atomic_margin_sparsification.md
```

The focused validator rebuilds all five comparisons, checks their asserted statuses, scans the new proof sources for placeholders, and audits every theorem, including generated certificates and private lemmas. The full validator checks all imported results. Both permit only `propext`, `Classical.choice`, and `Quot.sound`.

## Attempts and Remaining Questions

A ceiling at the exact logarithmic threshold can leave the failure budget equal to one when the threshold is integral. The proved bound uses a floor followed by a successor. Keeping the selected atom's old readout bias initially gave a much smaller one-head neighborhood. Allowing its own threshold and using total deficit below two sharpened that result to $N/(N-1)$. Cancellation of the bias then sharpened the balanced case further.

Uniform margins lose the contribution of over-separated inputs, and positive-radius formulas alone mishandle deterministic output coordinates. The profile and zero-width range arguments address those losses separately.

These results leave the optimal constants, sharp condition-number gaps, and exact atomic condition number of XOR unresolved. The present bounds do not establish a new head-complexity separation family or a general characterization of `HStar`. Higher-head analogues of the deficit obstruction, bounds using the probability support rather than every indexed atom, and further improvements beyond interval-based concentration are natural next targets.
