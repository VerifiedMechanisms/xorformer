# Four Vanilla Heads for Complement-Invariant Three-Head Rotary Classifiers

## Statement

Let $f : \lbrace 0,1\rbrace^n \to \lbrace 0,1\rbrace$ satisfy $f(\neg x)=f(x)$ for every input. If three affine fractions with positive denominators compute $f$, then four vanilla heads compute $f$ in the unchanged xorformer model.

Consequently, for either scalar rotary variant,

$$ H_P(f)\leq 3\quad\Longrightarrow\quad H_V(f)\leq 4,\qquad H_A(f)\leq 3\quad\Longrightarrow\quad H_V(f)\leq 4. $$

This is a four-head upper bound. It does not prove that three pure rotary heads can always be replaced by three vanilla heads. The two-head equality in [Theorem 16](016_pure_rope_two_heads.md) remains stronger at that head count and requires no complement invariance.

The proof and its scalar pure and retained corollaries are Lean-checked, with no `sorry` or new axioms. The fixed-frequency and freely chosen frequency pure architectural bridges are supplied separately by [Theorem 18](018_pure_rope_architectural_bridge.md).

## A quadratic product compiler

### Lemma 1. One extra head for a sum of affine products

Suppose affine forms $A_1,\ldots,A_m,B_1,\ldots,B_m$ and a real constant $c$ give a score

$$ Q(x)=c+\sum_{j=1}^m A_j(x)B_j(x) $$

that is nonzero at every cube point. Its Boolean signs can be computed by $m+1$ vanilla heads.

**Proof.** For $t\gt0$, define affine denominators

$$ F_t(x)=1+t\sum_i x_i,\qquad G_{j,t}(x)=F_t(x)+t^2B_j(x). $$

At $t=0$, every denominator equals one. The slope of $G_{j,t}$ at coordinate $i$ is $t(1+tB_{j,i})$, where $B_{j,i}$ is the corresponding slope of $B_j$. Finiteness therefore gives one positive interval of $t$ values on which all denominators are positive at all cube points and all denominator slopes are strictly positive.

Use the $m+1$ fractions in

$$ R_t(x)=c+\frac{\sum_j A_j(x)}{t^2F_t(x)}-\sum_{j=1}^m\frac{A_j(x)}{t^2G_{j,t}(x)}. $$

Each numerator is affine, and each denominator is vanilla-admissible. Direct cancellation gives

$$ R_t(x)=c+\sum_{j=1}^m\frac{A_j(x)B_j(x)}{F_t(x)G_{j,t}(x)}. $$

The right side extends continuously to $t=0$, where it equals $Q(x)$. Since the cube is finite and all values of $Q$ are nonzero, one sufficiently small positive $t$ preserves every sign simultaneously. Select such a finite $t$ inside the denominator interval. All resulting parameters are finite real numbers. $\blacksquare$

The conclusion also covers $m=0$ and $n=0$. A zero numerator can supply the unused head when $m=0$.

## Three-head antipodal averaging

First decrease the score's constant by a sufficiently small positive amount, preserving every Boolean label and making every score nonzero. Absorb that constant into the first numerator. Write the resulting strict score as

$$ S(x)=\frac{N_1(x)}{D_1(x)}+\frac{N_2(x)}{D_2(x)}+\frac{N_3(x)}{D_3(x)},\qquad D_j(x)\gt0. $$

Clearing denominators preserves strict signs and gives

$$ P=N_1D_2D_3+N_2D_1D_3+N_3D_1D_2. $$

Write each affine form as its constant at the center of the cube plus an odd affine form:

$$ N_j=\nu_j+u_j,\qquad D_j=d_j+b_j,\qquad u_j(\neg x)=-u_j(x),\qquad b_j(\neg x)=-b_j(x). $$

Because $f$ is complement-invariant, $P(x)$ and $P(\neg x)$ have the same strict sign. Their average $Q(x)=(P(x)+P(\neg x))/2$ has that sign as well. Expanding its even part gives

$$ Q=T+b_1A_1+b_2A_2+b_3A_3,\qquad T=\nu_1d_2d_3+\nu_2d_1d_3+\nu_3d_1d_2, $$

$$ \begin{aligned} A_1&=\nu_3b_2+\nu_2b_3+d_3u_2+d_2u_3,\cr A_2&=\nu_1b_3+d_3u_1+d_1u_3,\cr A_3&=d_2u_1+d_1u_2. \end{aligned} $$

Every $A_j$ and $b_j$ is affine. Lemma 1 with $m=3$ therefore computes the same classifier with four vanilla heads. If the starting classifier uses fewer than three heads, add zero-valued heads first. $\blacksquare$

## Formalization and remaining gap

The generic compiler is `CubeAffine.computable_of_strict_product_sum` in `formalization/HeadComplexity/Results/QuadraticProductUpperBound.lean`.

The averaging identity and comparison are in `formalization/HeadComplexity/Results/RoPEThreeComplement.lean`. Its main declarations are `CubeAffine.three_product_even_part`, `vanilla_four_of_three_positive_fractions_complement`, `vanilla_four_of_retainedRoPE_three_complement`, and `vanilla_four_of_pureRoPE_three_complement`.

This proof does not use the pure numerator constraint. Its finite difference construction uses one shared base denominator and three perturbed denominators. Reducing those four heads to three requires a further argument, as does eliminating complement invariance at three heads. Neither step follows from the even-part identity alone.
