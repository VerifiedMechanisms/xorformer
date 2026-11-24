# Three Affine Zero Faces Need At Most Four Vanilla Heads

## Statement

Let $d_0,d_1,d_2$ be affine real functions that are nonnegative on the Boolean cube. Define $f(x)$ to be true exactly when at least one $d_i(x)$ is zero. Then the unchanged original shared xorformer computes $f$ with four heads.

In particular, this applies to a union of three conjunctions with arbitrary positive and negative literals. The conjunctions may overlap. This is an upper bound, not a separation or a lower bound of four.

## Proof

Write $d_h(x)=d_{h,0}+\sum_i d_{h,i}x_i$ and choose

$$ B(x)=1+\sum_i(1+|d_{0,i}|+|d_{1,i}|)x_i. $$

The four denominators $B$, $B+d_0$, $B+d_1$, and $B+d_0+d_1$ are positive on the cube, and every coefficient of every denominator is strictly positive. They are therefore vanilla-admissible denominators in the affine-fraction normal form.

The reciprocal difference has the exact identity

$$ F(x)=\frac{1}{B}-\frac{1}{B+d_0}-\frac{1}{B+d_1}+\frac{1}{B+d_0+d_1}=\frac{d_0d_1(2B+d_0+d_1)}{B(B+d_0)(B+d_1)(B+d_0+d_1)}. $$

Consequently, $G=d_2F$ is nonnegative. It vanishes exactly on the union of the three zero sets and is strictly positive elsewhere. The cube is finite, so choose $\delta\gt0$ smaller than every positive value of $G$. If there are no positive values, any positive $\delta$ works.

The four-head score is

$$ S(x)=\delta-\frac{d_2}{B}+\frac{d_2}{B+d_0}+\frac{d_2}{B+d_1}-\frac{d_2}{B+d_0+d_1}=\delta-G(x). $$

This score is strictly positive exactly when $f$ is true. All four numerators are affine. The affine-fraction realization theorem supplies the original shared attention architecture, with unrestricted finite width and real parameters. No model definition is changed. $\blacksquare$

## Pure Rotary Comparison

For a union of three literal conjunctions, let $d_h$ count the mismatched literals of conjunction $h$. These counts are nonnegative integers. Three pure atoms give

$$ S_P(x)=-5+\sum_{h=0}^{2}\frac{1}{1/10+d_h(x)}. $$

At a true input the score is at least $5$; at a false input it is at most $-25/11$. Exact integer atom parameters and the scalar-to-rotary architecture bridge are recorded in the [search certificates](../../artifacts/rope/counterexample_search/README.md) and [Theorem 14](014_rope_head_complexity.md).

Thus this family has pure head complexity at most three and vanilla head complexity at most four. Exact vanilla three-head certificates are already available for the balanced examples on 12, 18, and 24 bits. Their threshold degree is three. No member with vanilla complexity four is established here.

## Lean Verification

The file [ThreeFaceFourHeads.lean](../../formalization/HeadComplexity/Results/ThreeFaceFourHeads.lean) proves:

- `HeadComplexity.ThreeFaceFourHeads.reciprocal_difference`.
- `HeadComplexity.ThreeFaceFourHeads.reciprocal_difference_pos_iff`.
- `HeadComplexity.ThreeFaceFourHeads.computable_four`.

The last theorem concludes `computableWithSharedHeadsN n 4 f`, so its conclusion includes the original architecture through the existing normal-form equivalence. The proof handles constant functions and degenerate affine zero sets. It uses no `sorry` and no new axioms.
