# Two Pure Rotary Heads Always Equal Vanilla

## Statement

Use the unchanged original xorformer model and the pure rotary variant from [Theorem 14](014_rope_head_complexity.md). For every finite Boolean function $f$,

$$ H_P(f)\leq2\quad\Longrightarrow\quad H_P(f)=H_V(f). $$

There is no complement-invariance hypothesis. In particular, a strict pure-RoPE Boolean head-count separation must have at least three pure heads and at least four vanilla heads. This rules out the entire proposed two-versus-three search, including asymmetric functions of threshold degree two.

The result strengthens [Theorem 15](015_pure_rope_two_heads_complement_invariant.md). It does not establish equality at higher head counts, and it does not concern retained positional embeddings.

## Proof

### Lemma 1. A pure numerator-denominator pencil contains an admissible denominator

Consider one pure atom with affine numerator and denominator

$$ N(x)=\eta+\sum_i\left(a_i v_0(1-x_i)+b_i v_1x_i\right),\qquad D(x)=\gamma+\sum_i\left(a_i(1-x_i)+b_ix_i\right), $$

where $a_i,b_i,\gamma\gt0$. Suppose $v_0\neq v_1$. Then some affine form $B=rN+sD$, with $r\in\lbrace-1,1\rbrace$, is positive on the entire Boolean cube and has all slopes strictly positive or all slopes strictly negative.

**Proof.** First suppose $v_0\lt v_1$. If $\eta\gt v_0\gamma$, choose

$$ B=N-v_0D=\eta-v_0\gamma+(v_1-v_0)\sum_i b_ix_i. $$

The constant and all slopes are strictly positive. Otherwise choose

$$ B=v_1D-N=v_1\gamma-\eta+(v_1-v_0)\sum_i a_i(1-x_i). $$

Here $v_1\gamma-\eta\gt0$, every summand is nonnegative on the cube, and every slope is strictly negative. If $v_1\lt v_0$, negate $N$, both token values, and $\eta$, and apply the previous case. The resulting form still lies in the original numerator-denominator pencil with coefficient $r\in\lbrace-1,1\rbrace$ on $N$. $\blacksquare$

### Lemma 2. One oriented factor compiles a quadratic into two vanilla heads

Suppose

$$ P=A B+C D, $$

where all four forms are affine, $B,D\gt0$ on the Boolean cube, and every slope of $B$ is strictly positive or every slope is strictly negative. Then the sign of $P$ has a two-head vanilla realization.

**Proof.** Write $B_i,D_i$ for the slopes, and set

$$ e=1+\sum_i\left|\frac{D_i}{B_i}\right|,\qquad E=eB+D. $$

The scalar $e$ is positive, so $E$ is positive on the cube. For every coordinate $e\gt|D_i/B_i|$, so $E_i=eB_i+D_i$ has the same strict sign as $B_i$. Both $B$ and $E$ are therefore vanilla-admissible denominators with arbitrary affine numerators. The exact identity

$$ \frac{C}{B}+\frac{A-eC}{E}=\frac{AB+CD}{BE} $$

proves the claim because $BE\gt0$. For zero inputs the slope conditions are vacuous and every numerator is constant, so the same construction is admissible. $\blacksquare$

### Lemma 3. A nondegenerate pure two-head score has a two-head vanilla classifier

Let the pure score be

$$ S=t+\frac{N_1}{D_1}+\frac{N_2}{D_2}, $$

and suppose the first head has distinct token values. Its cleared polynomial is

$$ P=N_1D_2+D_1(N_2+tD_2). $$

By Lemma 1 there is $B=rN_1+sD_1$ with $r^2=1$, positive on the cube and strictly oriented. Consequently

$$ P=(rD_2)B+D_1\left(N_2+(t-rs)D_2\right). $$

Apply Lemma 2 with $A=rD_2$, $C=N_2+(t-rs)D_2$, and $D=D_1$. The new score has exactly the sign of $P$, hence exactly the sign of $S$. This is a change of rational score with a positive multiplier, not an assertion that the two real-valued scores are equal. $\blacksquare$

### Lemma 4. Coincident token values can be removed without changing labels

If the first head already has distinct token values, no modification is needed. Otherwise let $S$ denote the original score, with label one precisely when $S\gt0$. Choose $\varepsilon\gt0$ smaller than every positive value of $S$ on the finite cube. If there are no positive values, any positive $\varepsilon$ works.

Decrease the score constant by $\varepsilon$, and increase the first head's bit-one token value by $\varepsilon/2$. For every input, the latter change increases the head output by

$$ \frac{\varepsilon}{2}\frac{\sum_i b_ix_i}{\gamma+\sum_i\left(a_i(1-x_i)+b_ix_i\right)}, $$

which lies between zero and $\varepsilon/2$. Thus originally positive scores remain positive, and originally nonpositive scores become strictly negative. The first head's token values are now distinct. All attention weights, the query constant, the second head, and the input length remain valid finite parameters. Lemma 3 applies. $\blacksquare$

### Conclusion

Every pure two-head classifier is a vanilla two-head classifier. The reverse inclusion follows from Theorem 14's exact simulation of each vanilla atom by one pure atom. The zero- and one-head levels agree by the constant and linear-threshold characterizations. Hence the minimum head counts agree whenever the pure count is at most two. $\blacksquare$

## Formalization and architectural scope

The complete scalar-to-vanilla result is Lean-checked, without `sorry` or new axioms, in [Results/PureRoPETwoHeads.lean](../../formalization/HeadComplexity/Results/PureRoPETwoHeads.lean):

- `RoPETwoHead.pure_oriented_pencil` proves Lemma 1.
- `RoPETwoHead.compile_products` proves Lemma 2 with the explicit coefficient $e$ above.
- `RoPETwoHead.compile_pure_two` proves the exact sign compilation for nondegenerate heads.
- `RoPETwoHead.raiseOneValue_bounds` and `RoPETwoHead.nondegenerate_pure_two` prove the finite perturbation argument.
- `vanillaComputable_two_of_pureRoPE` concludes computation in the existing literal vanilla shared-embedding architecture.
- `pureRoPEComputable_two_iff_vanilla` gives equality of the two-head Boolean classes.
- `pureRoPEHStar_eq_vanilla_of_le_two` proves equality of minimum counts at these levels.
- `pureRoPE_separation_requires_three_heads` proves the obstruction to a two-versus-three separation.

No existing model definition or statement is changed. The new Lean theorem uses the previously defined `PureRoPEAtom` scalar model and the original `computableWithSharedHeadsN` vanilla architecture.

For literal pure RoPE, necessity of the scalar form follows by exponentiating the two logits at every input position and the query self-logit. Token-only values give the shared pair $v_0,v_1$, and the fixed query token contributes $\eta$. Thus every architectural pure two-head model enters the Lean theorem's hypotheses. The conclusion is already an architectural vanilla realization through `computableWithSharedHeadsN_iff_affineFractionComputable`.

The reverse inclusion, and therefore equality for either fixed standard frequencies or freely chosen frequencies, uses Theorem 14's scalar-to-RoPE construction: finite rotary interpolation prescribes the bit-zero and bit-one logits independently, shared independent token embeddings support those key vectors and token-only values, and a separate output direction realizes the scalar readout. That literal rotary interpolation and matrix bridge remains handwritten in Theorem 14. This note adds no restriction on width or real parameters.
