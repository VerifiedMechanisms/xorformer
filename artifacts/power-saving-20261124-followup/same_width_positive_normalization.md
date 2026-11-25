# A same-width positive normal form

## Exact original-model statement

Suppose an original width $H$ representation of $f$ has relative margin at least $\gamma$, with the full-cube amplitude requested in the benchmark. Then either $f$ or its global output complement has a representation with the same $H$ genuine heads satisfying all of the following:

- Every head is nonnegative on the entire Boolean cube and attains zero somewhere.

- The bias is exactly $-1$.

- The amplitude, including that bias, is at most three.

- The complete truth table is strict, and its relative margin is at least $\gamma/3$.

The exact declaration is `HeadComplexity.SameWidthPositiveNormalization.hasNormalizedMargin_or_complement` in `formalization/HeadComplexity/Research/SameWidthPositiveNormalization.lean`. The predicate `HasNormalizedMargin` records every displayed condition. `normalized_or_complement_of_computable` starts directly from the original `computableWithHeadsN` definition and obtains the same form with no positive quantitative margin premise.

There is no increase in width, including at width zero. This is a global output complement, not an independent input-coordinate complement. Every head remains admissible and retains its original denominator orientation. All coefficients remain arbitrary real numbers.

## Proof

First center each head at the midpoint of its full-cube range and transfer the constants into the bias. This preserves the score exactly and does not increase amplitude. Write the centered head ranges as $[-s_h,s_h]$ and the new bias as $c$. If $c\gt0$, negate every head and the bias and complement all labels. The resulting score has bias $c\leq0$ and retains at least the original margin.

Put

$$ R=\sum_hs_h,\qquad A=R-c. $$

This $A$ is exactly the centered score's amplitude. Strict representation gives $A\gt0$. Set

$$ \psi_h(x)=\frac{\phi_h(x)+s_h}{A}. $$

Each new head is genuine, nonnegative, and has minimum zero. The exact score identity is

$$ -1+\sum_h\psi_h(x)=\frac{c+\sum_h\phi_h(x)}{A}. $$

Its full-cube amplitude satisfies

$$ 1+\sum_h\|\psi_h\|_\infty=1+\frac{2R}{A}\leq3. $$

The signed minimum score has been divided by $A$, so it is at least the previous relative margin. Dividing by the new amplitude loses at most another factor three. This proves the theorem, with all complete-table signs preserved. $\blacksquare$

The centering and global-negation helper is `SignedCenteredCertificate.exists_signed_centered_certificate`. The new normalization step is `SameWidthPositiveNormalization.normalize_of_centered_nonpositive`.

## Consequence and limitation

Up to a factor two for output complementation, counting original width $H$ truth tables is equivalent to counting the truth tables of this bounded positive normal form. A quantitative repair theorem may therefore restrict attention to nonnegative minimum-zero heads, bias $-1$, and amplitude at most three, with only a fixed factor loss in its input margin. This gives an exact normalization of the original problem; it does not itself prove a better count or a new positive lower margin.

Arbitrary signed cancellation in the original score is retained through the centering, the new threshold at one, and the freely chosen heads. The sum of the normalized nonnegative heads can still approach the constant one with arbitrarily small signed slack. The separate `NonnegativePartitionEmbedding` theorem shows that every original width $H$ table also has arbitrarily close bounded near-partition representatives at width $H+2$. That inclusion does not rule out a sharp count of the whole normalized class, but it prevents treating proximity to a positive partition as an automatic exclusion of source truth tables.

The remaining access problem is quantitative separation from one, or a bound on all labels realized by narrow near-partition degenerations. The normalization does not supply either conclusion.

## Verification

The module builds successfully in 3289 jobs. The three new theorem declarations have only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom reports. The helper module is separately checked. The proofs include the full-cube norms, arbitrary source bias, all original coefficients, and the global output complement explicitly.
