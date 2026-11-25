# Exact Pure RoPE Architectural Bridge

## Statement

The pure scalar atoms in [Theorem 14](014_rope_head_complexity.md) are exactly the affine scores of the literal pure rotary architecture, at every input length and head count. This includes separate model and head dimensions, explicit output projections, shared token embeddings, a fixed query token attending to itself, and unrotated token-only values. The existing vanilla definitions are unchanged.

For every $n,H\geq0$, every family of pure atoms $P_1,\ldots,P_H$, and every real constant $c$, a standard-frequency rotary model realizes exactly

$$ S(x)=c+\sum_{h=1}^{H}P_h(x). $$

The construction uses common model and head width $2(n+2)$ and the standard frequencies

$$ \omega_r=10000^{-r/(n+2)}, \qquad r=0,\ldots,n+1. $$

Conversely, every pure rotary model, with arbitrary positive model dimension and positive even head dimension, has such a scalar representation with the same number of heads. Its frequencies may be standard or freely chosen. Consequently the two frequency conventions have identical exact affine scores and Boolean head budgets when finite width is unrestricted.

> This bridge proves an equivalence between literal pure RoPE and its scalar normal form. It does not prove that pure RoPE and vanilla have the same Boolean head complexity.

## Proof

### Theorem 1. Exact extraction from the rectangular architecture

Let the model dimension be $d_m$ and the head dimension be $2m$. For a head, write $e_0,e_1,e_=$ for the shared token embeddings and let $R_j$ be its common rotary schedule. The fixed query position is $q=n+1$. Its token-specific logit is

$$ \ell_j(t)=\langle R_jW_Ke_t,R_qW_Qe_=\rangle. $$

This includes the self-logit $\ell_q(=)$. Set

$$ a_i=\exp(\ell_i(0)), \qquad b_i=\exp(\ell_i(1)), \qquad \gamma=\exp(\ell_q(=)). $$

Composing the readout with the output and value projections gives

$$ v_t=\langle w,W_OW_Ve_t\rangle, \qquad \eta=\gamma v_=. $$

Linearity of the output projection and readout gives the exact head contribution

$$ P(x)=\frac{\eta+\sum_i\bigl(a_i v_0(1-x_i)+b_i v_1x_i\bigr)}{\gamma+\sum_i\bigl(a_i(1-x_i)+b_i x_i\bigr)}. $$

The residual and threshold contribute $c=\langle w,e_=\rangle-\tau$. All attention weights are strictly positive. This argument uses no interpolation property and does not change the given head dimension or frequency schedule. $\blacksquare$

### Theorem 2. Standard frequencies interpolate finite logits

Let $m\gt n$ and suppose the complex numbers $z_r=\exp(\mathrm{i}\omega_r)$ are distinct. The square complex Vandermonde matrix is invertible. For any real target values at the $n+1$ positions, extend them arbitrarily to values $y_j$ for $j=0,\ldots,m-1$. There exist complex coefficients $a_r$ with

$$ \sum_{r=0}^{m-1}a_r z_r^j=y_j, \qquad j=0,\ldots,m-1. $$

Identify each real rotary block with a complex coordinate. Put the unrotated query block equal to $\exp(-\mathrm{i}q\omega_r)$ and the key block equal to $a_r/z_r$. Rotation makes every query block equal to $1$. At position $j+1$, the real query-key inner product is

$$ \mathop{\mathrm{Re}}\sum_r z_r^{j+1}\frac{a_r}{z_r}=\mathop{\mathrm{Re}}\sum_r a_rz_r^j=y_j. $$

Thus one common query vector permits arbitrary logits at all input positions and at the self position. The query vector and frequency schedule can be shared by every head.

For the standard schedule, the angles $10000^{-r/m}$ are distinct and lie in $(0,1]$. Complex exponentiation is injective on these imaginary angles because they lie in $(-\pi,\pi]$. Hence the required nodes are distinct. Taking $m=n+2$ also leaves at least three independent token embedding coordinates. This proof uses a larger finite width than the sharper real-rank proof in Theorem 14. $\blacksquare$

### Theorem 3. Exact realization with shared embeddings

Use the first three standard basis vectors as the shared embeddings of the tokens $0,1,=$. By Theorem 2, choose separate key vectors for each token and each head giving the input logits $\log a_i$ and $\log b_i$, and the query self-logit $\log\gamma$.

Linear maps can prescribe these key images independently because the three token embeddings are independent. They likewise send the query embedding to the common query vector and the token embeddings to scalar values $v_0,v_1,\eta/\gamma$ along one common readout direction. Take each output projection to be the identity. The threshold absorbs the fixed residual and realizes the desired constant $c$.

This construction preserves every real affine score, hence also the convention that the Boolean label is true exactly when the score is strictly positive. It uses no limit and no approximation. $\blacksquare$

## Boundary cases

When $n=0$, the input domain has one element. The construction above uses $m=2$ and still interpolates the self-logit. Every Boolean function on this domain is constant.

When $H=0$, the sum of head outputs is empty. The only score is the fixed residual readout minus the threshold, so precisely the constant Boolean functions are computable. The Lean equivalences quantify over all natural numbers without excluding either boundary case.

## Broader frequency choices

The extraction proof also works when every head chooses a separate frequency list. It applies to arbitrary finite head width and arbitrary linear position maps, so an odd width with an additional unrotated coordinate is covered as well. The self-logit still applies the same position map to the query and its own key.

Every such score has an exact realization using the common fixed-standard schedule above. In particular, allowing separate freely chosen frequencies for different heads gives the same Boolean class at every head count as shared freely chosen frequencies or the fixed-standard schedule. This is an additional extraction theorem, not a change to the original architecture definitions.

## Lean declarations and verification

The core implementation adds four modules and changes no pre-existing model definitions.

| Module | Main declarations |
| --- | --- |
| `HeadComplexity/Model/PureRoPE.lean` | `PureRotaryFamily.head_readout_eq_atom`, `PureRotaryFamily.residual_score_eq`, `blockRotation`, `standardRotaryFrequency` |
| `HeadComplexity/Model/PureRoPERealization.lean` | `exists_pureRotaryFamily_score_of_interpolates`, `pureRotaryComputableAt_iff_scalar_of_interpolates` |
| `HeadComplexity/Model/RotaryInterpolation.lean` | `standardRotarySchedule_interpolates`, `exists_standardPureRotaryFamily_score`, `standardPureRotaryComputable_iff_scalar`, `freePureRotaryComputable_iff_scalar` |
| `HeadComplexity/Model/RectangularPureRoPE.lean` | `RectangularPureRotaryFamily.exists_standard_score`, `rectangularStandardPureRotaryComputable_iff_scalar`, `rectangularFreePureRotaryComputable_iff_scalar`, `rectangularStandardPureRotaryComputable_iff_free` |

All four core modules build. The repository axiom checker audits 105 theorem declarations across them and reports only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry` or project-defined axiom is used.

The extension `HeadComplexity/Model/PureRoPEHeadSchedules.lean` proves `RectangularPureRotaryFamily.exists_standard_score_of_headSchedules`, `rectangularHeadwiseFreePureRotaryComputable_iff_scalar`, and `rectangularHeadwiseFreePureRotaryComputable_iff_standard`. The module `HeadComplexity/Results/RoPEBoundaryCases.lean` proves the zero-head constant-function characterizations and `empty_input_head_minima`, which makes all four zero minima at empty input explicit. Each additional module builds, and each of its six theorem declarations has the same standard-axiom-only audit.
