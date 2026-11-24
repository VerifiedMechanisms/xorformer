# RoPE and Head Complexity

## Statement and status

Write $H_V(f)$ for the vanilla head complexity in [model.md](../../model.md). Write $H_P(f)$ for the variant that replaces additive positional embeddings by rotary query/key encoding, and $H_A(f)$ for the variant that retains additive positional embeddings and also applies rotary query/key encoding. Values are never rotated.

With unrestricted finite dimensions and real parameters, the following comparisons hold for every Boolean function:

$$ \deg_{\pm}(f)\leq H_A(f)\leq H_P(f)\leq H_V(f). $$

Both rotary complexities are independent of whether the frequencies are fixed to the standard base 10,000 schedule or can be chosen freely. This independence holds for exact real-valued scores at every head count, not just for classifiers.

| Positional embeddings | Rotary frequencies | Comparison established here |
| --- | --- | --- |
| Replaced by RoPE | Fixed standard | $H_P(f)\leq H_V(f)$ |
| Replaced by RoPE | Freely chosen | Same exact scores and complexity as fixed standard |
| Retained alongside RoPE | Fixed standard | $H_A(f)\leq H_P(f)\leq H_V(f)$ |
| Retained alongside RoPE | Freely chosen | Same exact scores and complexity as fixed standard |

**Equality cases.** All inequalities are equalities whenever $H_V(f)=\deg_{\pm}(f)$. In particular this covers every symmetric Boolean function, including parity and exact-count predicates, and every linear threshold function. Constants need zero heads.

[Theorem 16](016_pure_rope_two_head_equality.md) proves equality whenever pure RoPE uses at most two heads, with no symmetry hypothesis. It strengthens the complement-invariant case from [Theorem 15](015_pure_rope_two_heads_complement_invariant.md).

**Strict retained comparison.** The seven-bit function in [Theorem 15's corollary](015_pure_rope_two_heads_complement_invariant.md) satisfies $H_A(f)=2\lt3=H_P(f)=H_V(f)$. Thus retaining positional embeddings alongside RoPE can strictly reduce head count.

**Strict pure comparison.** [Theorem 22](022_explicit_pure_rope_separation.md) supplies an explicit finite Boolean function with $H_P(f)=3$ and $4\leq H_V(f)\leq7$. Its lower bound combines a quantitative coefficient obstruction with a finite replication and sign-rigidity argument. The full separation proof is handwritten, with exact rational certificates; its supporting pure upper construction is Lean-checked. The separate score example below does not itself establish this Boolean separation.

## Model conventions

Positions are $1,\ldots,n,q$, with $q=n+1$ the fixed query token. For an even head dimension $d=2m$, let $R_j$ be block diagonal, with block $r$ the planar rotation by $j\omega_r$. The logit at input position $i$ is

$$ \ell_i=\left(R_q W_Q u_q\right)^\top R_i W_K u_i=q_0^\top R_{i-q}W_Ku_i, \qquad q_0=W_Qu_q. $$

The query token attends to itself as well. Its self-logit is $q_0^\top W_Ku_q$. The residual and threshold contribute an arbitrary scalar constant. Input embeddings are $u_i=e_{x_i}$ in the pure variant, and $u_i=e_{x_i}+p_i$ in the retained variant.

The fixed schedule is

$$ \omega_r=10000^{-2r/d}, \qquad r=0,\ldots,m-1. $$

In the free convention these frequencies are additional real parameters, shared across heads. Widths may depend on the input length and function. There is no norm, precision, or conditioning restriction. The results do not assert comparable behavior at a fixed width or bounded parameter size.

## Proof

### Theorem 1. Standard rotary features interpolate arbitrary finite logits

For every $n\geq1$, choose an even $d=2m\geq n$. The real matrix with rows indexed by $i=1,\ldots,n$ and columns

$$ \cos((i-q)\omega_r), \qquad \sin((i-q)\omega_r), \qquad r=0,\ldots,m-1, $$

has row rank $n$.

**Proof.** Suppose real coefficients $t_i$ annihilate every column. For each frequency both the cosine and sine equations vanish, so

$$ \sum_{i=1}^{n}t_i z_r^{i-q}=0, \qquad z_r=e^{\mathrm{i}\omega_r}. $$

After multiplication by $z_r^{q-1}$, the real polynomial

$$ P(z)=\sum_{i=1}^{n}t_i z^{i-1} $$

vanishes at each $z_r$ and its complex conjugate. These $2m$ points are distinct: the frequencies are distinct and lie in $(0,1]$, and positive and negative angles in this range cannot coincide modulo $2\pi$. Since $\deg P\leq n-1\lt2m$, the polynomial is zero. Thus every $t_i=0$. $\blacksquare$

Take $q_0$ to have block $(1,0)$ at every frequency. Then the map

$$ k\longmapsto\left(q_0^\top R_{i-q}k\right)_{i=1}^{n} $$

is surjective. Two independently chosen key vectors therefore prescribe arbitrary logits for bit zero and bit one at every position. A separate query-token key prescribes the self-logit, because $q_0\neq0$.

The same fixed frequencies and query vector work for every head; the keys vary by head. Thus frequency sharing imposes no extra constraint. For $n=0$ there are no interpolation constraints, and $d=2$ suffices.

### Theorem 2. Exact scalar normal forms

For positive parameters $a_i,b_i,\gamma$ and arbitrary real $v_0,v_1,\eta$, define a pure atom by

$$ P(x)=\frac{\eta+\sum_i\bigl(a_i v_0(1-x_i)+b_i v_1x_i\bigr)}{\gamma+\sum_i\bigl(a_i(1-x_i)+b_i x_i\bigr)}. $$

For positive parameters $a_i,b_i,\gamma$ and arbitrary real $m_i,\delta,\eta$, define a retained atom by

$$ A(x)=\frac{\eta+\sum_i\bigl(a_i m_i(1-x_i)+b_i(m_i+\delta)x_i\bigr)}{\gamma+\sum_i\bigl(a_i(1-x_i)+b_i x_i\bigr)}. $$

The exact scores of the pure and retained rotary models with $H$ heads are, respectively, constants plus sums of $H$ pure atoms and constants plus sums of $H$ retained atoms. These descriptions hold with either frequency convention.

**Necessity.** Set $a_i=\exp(\ell_i(0))$, $b_i=\exp(\ell_i(1))$, and $\gamma=\exp(\ell_q)$. Compose the linear value and output maps with the final readout. Without additive embeddings the two input-token values are $v_0,v_1$. With additive embeddings they are $m_i,m_i+\delta$, where the shared difference is the readout of $e_1-e_0$. The query contributes an arbitrary numerator constant $\eta$. These facts give the displayed formulas for every rotary frequency choice.

**Pure sufficiency.** Use three independent embedding vectors for the tokens $0,1,=$ and one extra output direction. Apply Theorem 1 to choose the two token keys with logits $\log a_i$ and $\log b_i$. Choose the query key to give $\log\gamma$, and choose its query projection to be $q_0$. Independent linear value maps send the three embeddings to scalar values $v_0,v_1,\eta/\gamma$. Output projections write into the extra direction, which is also the readout direction. The query residual is orthogonal to it. The embeddings are shared across heads; all projections can be chosen independently for each head.

**Retained sufficiency.** Take $e_0=0$, and use independent basis vectors for $e_1$, $e_=$, the $n$ input positional embeddings, and an output direction. Set $p_q=0$. Theorem 1 supplies a key difference giving the prescribed logit differences $\log b_i-\log a_i$. Each independent positional key then sets the baseline $\log a_i$ at its own position. Each positional value sets $m_i$, and the token-value difference sets $\delta$. The query key and value set $\gamma$ and $\eta$ as before. All heads use these same embedding basis vectors.

These constructions use the fixed schedule. Any free-frequency model has one of the displayed normal forms and can consequently be replaced by a fixed-frequency model with exactly the same score and head count. The converse holds because the standard frequencies are an allowed free choice. $\blacksquare$

Every pure atom is a retained atom: take $m_i=v_0$ and $\delta=v_1-v_0$. Hence $H_A(f)\leq H_P(f)$.

### Theorem 3. Every vanilla atom is exactly one pure rotary atom

By [the vanilla normal form](../01_foundations_and_normal_form/010_linear_fractional_normal_form.md), it suffices to simulate every admissible affine ratio

$$ r(x)=\frac{b+\sum_i A_i x_i}{d+\sum_i C_i x_i}. $$

**Positive denominator slopes.** Assume $C_i\gt0$ for every $i$ and $d\gt0$. Choose $t$ such that $w_i=A_i+tC_i\gt0$ for every $i$. For example, take

$$ t=1+\sum_i\left|\frac{A_i}{C_i}\right|. $$

Choose $Q\gt0$ large enough that $\sum_iw_i/Q\lt d$, and set

$$ a_i=\frac{w_i}{Q}, \qquad b_i=a_i+C_i, \qquad v_0=-(t+Q), \qquad v_1=-t, $$

$$ \gamma=d-\sum_i a_i, \qquad \eta=b-\sum_i a_i v_0. $$

All attention weights are strictly positive. The pure atom has denominator $d+\sum_iC_ix_i$, numerator constant $b$, and numerator slopes

$$ b_i v_1-a_i v_0=Qa_i-tC_i=A_i. $$

It therefore equals $r$ on every input, with no limiting argument and no approximation.

**Negative denominator slopes.** Substitute $y_i=1-x_i$. The transformed ratio has positive slopes $-C_i$ and denominator constant $d+\sum_iC_i\gt0$. Apply the positive construction, then swap $a_i$ with $b_i$ at every position and swap $v_0$ with $v_1$. This implements the simultaneous complementation exactly. It does not assume invariance under complementing only some inputs.

**Constant denominator.** Admissibility says that all $A_i$ are positive, all negative, or all zero. In the positive case choose $Q\gt0$ with $\sum_i A_i/Q\lt d$, take $a_i=b_i=A_i/Q$, $v_0=0$, $v_1=Q$, $\gamma=d-\sum_i a_i$, and $\eta=b$. In the negative case use $a_i=b_i=-A_i/Q$ and $v_1=-Q$. When every slope vanishes, use any strictly positive equal weights with sum below $d$ and take $v_0=v_1=0$. The empty-input case is included.

Thus every vanilla score with $H$ heads is exactly a pure rotary score with $H$ heads. Applying Theorem 2 and then thresholding proves $H_P(f)\leq H_V(f)$ for both rotary frequency conventions. $\blacksquare$

### Theorem 4. Retained RoPE equals unrestricted positive affine-ratio complexity

Let $L_+(f)$ be the least number of ratios in a score

$$ S(x)=c+\sum_{h=1}^{H}\frac{N_h(x)}{D_h(x)}, \qquad D_h(x)\gt0 \text{ on the Boolean cube}, $$

where all numerators and denominators are affine and no sign restriction is placed on the denominator slopes. Then

$$ H_A(f)=L_+(f). $$

**Proof.** Every retained atom is such a ratio, which gives $L_+(f)\leq H_A(f)$.

For the converse, first make the classifier strict by decreasing $c$ slightly. On a finite cube this preserves all positive labels and makes every negative label have a strictly negative score; if there are no positive labels, any sufficiently small decrease works. Small perturbations of denominator slopes preserve denominator positivity and all strict score signs. We may therefore assume every slope $C_i$ of every denominator is nonzero.

Fix one perturbed ratio $(b+\sum_i A_ix_i)/(d+\sum_i C_ix_i)$. Positivity on the cube is equivalent to

$$ d\gt\sum_i\max(-C_i,0). $$

For sufficiently small $\varepsilon\gt0$, take

$$ a_i=\max(-C_i,0)+\varepsilon, \qquad b_i=a_i+C_i, \qquad \gamma=d-\sum_i a_i\gt0, $$

$$ \delta=0, \qquad m_i=\frac{A_i}{C_i}, \qquad \eta=b-\sum_i a_i m_i. $$

The retained atom has exactly the prescribed numerator and denominator. Apply this to all heads. Although the perturbation may change the real-valued score, it preserves the Boolean classifier exactly and uses the same head count. For $n=0$ every function is constant and both complexities are zero. $\blacksquare$

In particular $H_A$ is invariant under complementing any subset of input bits, because $L_+$ is. Such an invariance of $H_V$ is not assumed or proved here.

### Theorem 5. Threshold-degree lower bound and equality cases

Every rotary head in Theorem 2 has an affine numerator and a denominator positive on the cube. For a score with $H$ heads, clear the denominators:

$$ \left(\prod_{h=1}^{H}D_h(x)\right)S(x)=c\prod_{h=1}^{H}D_h(x)+\sum_{h=1}^{H}N_h(x)\prod_{g\neq h}D_g(x). $$

This polynomial has degree at most $H$ and the same classifier as $S$, since the multiplier is positive. Hence threshold degree lower-bounds both rotary complexities. Combined with Theorem 3, this proves the claimed chain.

Whenever vanilla attains the threshold-degree lower bound, the entire chain is squeezed to equality. [The symmetric sign-change theorem](../01_foundations_and_normal_form/012_symmetric_sign_changes.md) gives

$$ H_A(f)=H_P(f)=H_V(f)=\deg_{\pm}(f)=\text{number of changes between adjacent Hamming weights} $$

for symmetric $f$. The [one-head characterization](../01_foundations_and_normal_form/011_one_head_characterization.md) gives the same conclusion for linear threshold functions. $\blacksquare$

The ten-bit rank obstruction in [Theorem 13](../02_separations_and_counterexamples/013_strict_threshold_degree_separation.md) also applies to all rotary variants: its exclusion of two heads uses only the sum-of-two-affine-products form after clearing denominators. It therefore does not furnish a separation between vanilla and RoPE.

### Theorem 6. Two rotary heads require at most three vanilla heads

For either rotary variant,

$$ H_A(f)\leq2\quad\Longrightarrow\quad H_V(f)\leq3. $$

In particular, if a two-head retained rotary model strictly improves on vanilla, the exact counts must be two versus three. Theorem 16 rules out strict improvement with two pure rotary heads.

**Proof.** A two-head retained score can first be made strict by adjusting its constant. Clearing its positive denominators gives a strict sign representation

$$ P(x)=L_1(x)R_1(x)+L_2(x)R_2(x) $$

with affine factors. Set $B(x)=1+\sum_i x_i$. For sufficiently small $\varepsilon\gt0$, each of $B$, $B+\varepsilon R_1$, and $B+\varepsilon R_2$ is positive on the cube and has all denominator slopes strictly positive. Consider the three-head vanilla score

$$ S_\varepsilon(x)=\frac{L_1(x)+L_2(x)}{\varepsilon B(x)}-\frac{L_1(x)}{\varepsilon(B(x)+\varepsilon R_1(x))}-\frac{L_2(x)}{\varepsilon(B(x)+\varepsilon R_2(x))}. $$

All three ratios are admissible by the vanilla normal form. Direct cancellation gives

$$ S_\varepsilon(x)=\frac{L_1(x)R_1(x)}{B(x)(B(x)+\varepsilon R_1(x))}+\frac{L_2(x)R_2(x)}{B(x)(B(x)+\varepsilon R_2(x))}. $$

As $\varepsilon\to0$, this converges to $P(x)/B(x)^2$, whose sign is strict at every cube point. Finiteness of the cube ensures a single sufficiently small positive $\varepsilon$ preserves all signs simultaneously. This gives three vanilla heads. Zero- and one-head cases are already covered by the constant and linear-threshold characterizations. $\blacksquare$

This argument is an upper bound, not a construction of a function that actually needs the third vanilla head.

## A strict score separation that does not settle head complexity

On three bits consider

$$ g(x)=\frac{1}{5+x_1+x_2-x_3}. $$

This is one pure atom: take $a=(1,1,2)$, $b=(2,2,1)$, $\gamma=1$, $\eta=1$, and $v_0=v_1=0$.

However, no one-head vanilla score, even with an arbitrary added constant, equals $g$ on the full cube. To see this, absorb any added constant into the numerator and suppose $N/E=1/D$, where $D=5+x_1+x_2-x_3$ and $E$ is an admissible vanilla denominator. Write $N=b+A_1x_1+A_2x_2+A_3x_3$. Equality implies $ND=E$ on the cube. The three quadratic coefficients in the unique multilinear expansion are zero, giving

$$ A_1+A_2=0, \qquad A_3-A_1=0, \qquad A_3-A_2=0. $$

Thus every $A_i=0$, so $E=bD$. Positivity gives $b\gt0$, and the slopes of $E$ have mixed signs, contradicting vanilla admissibility.

Nevertheless every threshold of $g$ is a linear threshold function: multiply the threshold inequality by the positive $D$. Consequently these classifiers all have vanilla head complexity at most one. The example proves that exact score simulation in the reverse direction is impossible, while leaving the Boolean head-count equality question open.

## Formalization and remaining work

The new Lean scalar model is `PureRoPEAtom` in [Atoms/RoPE.lean](../../formalization/HeadComplexity/Atoms/RoPE.lean). Its positive-denominator expansion is `PureRoPEAtom.denominator_pos`, and `PureRoPEAtom.eval_eq` identifies the scalar function with its affine ratio.

`AffineFraction.exists_pure_positive` gives the constructive simulation for positive denominator slopes. `AffineFraction.exists_pure` covers every vanilla-admissible ratio, including negative and zero slopes. `pureRoPEComputable_of_vanilla` lifts it to every head count of the existing shared-embedding vanilla model.

[Results/RoPEComparison.lean](../../formalization/HeadComplexity/Results/RoPEComparison.lean) defines the minimum scalar counts `PureRoPEHStar` and `RetainedRoPEHStar`. The complete scalar inequality chain is proved by `thresholdDeg_le_retainedRoPEHStar`, `retainedRoPEHStar_le_pure`, and `pureRoPEHStar_le_vanilla`. `ropeHStar_eq_vanilla_of_degree_tight` proves equality whenever vanilla attains threshold degree, and `ropeHStar_symmetric` gives the exact symmetric result. The one-head equivalences are `pureRoPEComputable_one_iff_isLTF` and `retainedRoPEComputable_one_iff_isLTF`.

[Examples/RoPE.lean](../../formalization/HeadComplexity/Examples/RoPE.lean) defines `RoPEExamples.mixedReciprocal`. `RoPEExamples.mixedReciprocal_no_vanilla_one_head_score` checks the exact-score obstruction against the existing shared-embedding vanilla architecture, including a free threshold constant.

The literal rotation matrices, the Vandermonde interpolation argument, the bridge from scalar atoms to literal rotary attention, Theorem 4's unrestricted-denominator equivalence, and Theorem 6's three-head upper bound are handwritten proofs here, not Lean-checked statements. No existing vanilla definition or theorem is changed.

Theorem 15 settles strictness for the retained class but excludes its seven-bit example as a pure separation. Theorem 16 rules out every two-head pure separation. The explicit replicated construction in Theorem 22 achieves a strict pure separation with three pure heads and at least four vanilla heads. Its exact vanilla count within the range four through seven, a substantially smaller example, and a complete Lean formalization of the quantitative lower bound remain open. Nonuniform denominator coefficients, the strict score example, and failed numerical fitting do not by themselves prove any Boolean separation.
