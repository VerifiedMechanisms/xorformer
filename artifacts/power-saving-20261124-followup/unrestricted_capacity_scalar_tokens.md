# Scalar token decoding and the Boolean addressing gap

## Exact lower bound

Suppose one real token can encode every word of $r$ bits. Bit $i$ is read by the strict sign of a real polynomial $P_i$ of degree at most $D$. The token assigned to each word may be an arbitrary real number, and its ordering need not agree with binary ordering.

$$ 2^r-1\leq\sum_{i=1}^r\deg P_i\leq rD. $$

**Proof.** Choose one token for every word. Different words require different tokens, so sort the $2^r$ tokens. Every adjacent pair has a bit with opposite signs. The intermediate value theorem gives a root of that bit polynomial in the open gap. These $2^r-1$ roots of $\prod_iP_i$ are distinct. Every bit polynomial is nonzero, because all selected evaluations are strict. The root bound for a nonzero polynomial proves the inequality. $\blacksquare$

The kernel-checked declaration `HeadComplexity.ScalarTokenDecoder.all_words_degree_bound` proves this statement. The more precise `all_words_le_sum_degrees` retains the sum of the individual natural degrees. The proof explicitly sorts the chosen real tokens; it assumes no ordering of the words.

## Positive reciprocal poles

Suppose the bit decoders have the form

$$ R_i(t)=c_i+\sum_{h=1}^H\frac{A_{ih}(t)}{B_h(t)}, $$

where every numerator and denominator is affine in the scalar token. Assume only that all $B_h(t)$ are positive at every selected token. Clearing the common denominator gives

$$ P_i(t)=c_i\prod_{h=1}^HB_h(t)+\sum_{h=1}^HA_{ih}(t)\prod_{g\neq h}B_g(t),\qquad\deg P_i\leq H. $$

The sign is unchanged, so

$$ 2^r-1\leq rH. $$

`HeadComplexity.ScalarTokenDecoder.reciprocal_decoder_bound` proves this consequence, including denominator clearing and the degree estimate. Arbitrary real coefficients, affine numerators, signed residues, and signed cancellation are permitted. Positivity is needed only at the selected tokens. Thus this obstruction applies to every genuine original-model scalar decoder satisfying the displayed form, and also to a larger class.

This is a theorem about reading words from one scalar token. It is not a lower bound for unrestricted xorformer head complexity.

## The bound is essentially sharp

The scalar degree barrier does not rule out the usual parameter-bit extraction scale. Balanced Gray codes order all $2^r$ words so that each coordinate changes at most $2^r/r+2$ times. Existence for every positive $r$ is Theorem 1 of [Bhat and Savage, Balanced Gray Codes, 1996](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/EJC/Volume_3/PDFFiles/v3i1r25.pdf).

Here is the resulting decoder construction. Place the ordered words at tokens $t_j=j$, for $j=1,\ldots,2^r$. For each bit $i$, put one simple root at $j+1/2$ exactly when that bit changes between words $j$ and $j+1$. Choose the overall sign of $P_i$ to match the first word. This polynomial has the prescribed signs at every token, and degree at most $D=\lceil 2^r/r+2\rceil$.

Choose the same denominator for every bit:

$$ Q(t)=\prod_{h=1}^D(t+h). $$

It is strictly positive on all selected tokens. Since $\deg P_i\leq D$ and $Q$ has distinct real roots, polynomial division and partial fractions give real constants $c_i,a_{ih}$ such that

$$ \frac{P_i(t)}{Q(t)}=c_i+\sum_{h=1}^D\frac{a_{ih}}{t+h}. $$

Thus $O(2^r/r)$ shared positive reciprocal poles suffice for scalar bit reading. The residues may have either sign, as permitted in the unrestricted model. The Gray-code theorem and this decoder construction are written mathematics, not Lean declarations in this run. No numerical experiment is used in the argument.

## What this says at the critical width

Write $N=2^n$ and $H\asymp N/n^2$. Reading exactly $n$ bits from one scalar token using only $H$ poles is impossible, because the necessary inequality would be $N-1\leq nH\asymp N/n$.

That statement must not be replaced by an assertion about $r\approx n$ without tracking the additive difference. The usual capacity construction stores $r=\lfloor\log_2H\rfloor=n-2\log_2n+O(1)$ bits per parameter. At this value, the degree lower bound requires only $\Omega(H/\log H)$ poles, and the Gray-code construction achieves that order. There is no contradiction with an available budget of $H$ shared poles.

The first missing lemma in a proposed original-model upper construction is therefore a Boolean token-address compiler. It would have to expose enough independently stored scalar tokens and select their bit decoders on the full $n$-dimensional Boolean cube, while every denominator remains admissible. A naive allocation of $\log_2H$ address bits and two groups of $\log_2n$ selector bits does not supply such a compiler: an affine denominator in $k$ binary selector coordinates has only $k+1$ independent affine coefficients. Binary information content alone does not let it select $n$ unrelated stored weights. One-hot selectors spend physical input coordinates, and overlapping-address constructions require a separate proof.

There is a sharper obstruction if binary selector bits enter only the numerators. For a fixed token, every denominator is then constant as a function of the selectors, and the entire score is affine in those selectors. With two selectors, its four values satisfy

$$ S(0,0)+S(1,1)=S(0,1)+S(1,0). $$

It cannot have negative signs at $(0,0),(1,1)$ and positive signs at $(0,1),(1,0)$. Thus this architecture cannot even read the four-bit XOR word, for any number of shared poles. The declarations `binarySelector_rectangle` and `binarySelector_cannot_xor` prove this for arbitrary real numerators, residues, and denominator values. Allowing selector dependence in the denominators escapes the argument and returns to the original unresolved model.

Conversely, a lower bound beyond $N/n^2$ cannot simply cite positivity to exclude scalar bit extraction. The construction above has positive poles and arbitrary signed cancellation, and already reaches the sharp scalar order. A successful unrestricted capacity argument must also exploit the way all Boolean queries share the same affine denominator coefficients.

## Verification boundary

The file is `formalization/HeadComplexity/Research/ScalarTokenDecoder.lean`. The audited declarations are `ordered_words_le_sum_degrees`, `all_words_le_sum_degrees`, `all_words_degree_bound`, `cleared_natDegree_le`, `eval_cleared`, `reciprocal_decoder_bound`, `binarySelector_rectangle`, and `binarySelector_cannot_xor`, all in `HeadComplexity.ScalarTokenDecoder`.

These declarations leave `HeadComplexity.worstCaseHeadComplexity` and every model definition unchanged. They provide a precise obstruction and a precise limitation of that obstruction. Neither requested unrestricted lower bound follows.
