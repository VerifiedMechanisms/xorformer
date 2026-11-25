# Positive anchored-face decomposition with controlled full-cube mass

## Statement and status

This is an unconditional structural theorem for every individual original-model head. The positive reciprocal expansion, endpoint identities, and full-cube norm estimate are now kernel checked in `PositiveReciprocalExpansion.lean`. The application to every genuine original head, including both coherent orientations and the genuine block approximation interface, is checked in `OriginalAnchoredExpansion.original_head_expansion`. The earlier companion module records the elementary coefficient mass estimates. This is not a margin repair theorem.

Let $B(x)=c+\sum_{i=1}^n w_i x_i$ with $c\gt 0$ and $w_i\gt 0$, let $A$ be an arbitrary real affine function, and set $M=\max_{x\in\lbrace 0,1\rbrace^n}|A(x)/B(x)|$. There are positive coefficients $\kappa_S$, indexed by all $S\subseteq[n]$, for which

$$ \frac{A(x)}{B(x)}=\sum_{S\subseteq[n]}\kappa_S A(x)\prod_{i\in S}(1-x_i). $$

Every summand is uniformly approximable by one admissible original-model head. The sum of the full-cube norms of the summands satisfies

$$ \sum_{S\subseteq[n]}\left\|\kappa_S A(x)\prod_{i\in S}(1-x_i)\right\|_\infty\leq M\left(1+\sum_{i=1}^n\frac{w_i}{c+w_i}\right)\leq(n+1)M. $$

All signs of $A$ and all cancellations between different original heads remain allowed. A head with all negative denominator slopes satisfies the same theorem after simultaneously complementing every coordinate. A constant denominator gives an affine function and needs only the empty-face block.

## Positive reciprocal coefficients

Write $C=c+\sum_iw_i$ and $y_i=1-x_i$. Define the coefficients in increasing order of $|S|$ by

$$ \kappa_\varnothing=\frac1C,\qquad \kappa_S=\frac{\sum_{i\in S}w_i\kappa_{S\setminus\lbrace i\rbrace}}{C-\sum_{i\in S}w_i}\quad(S\neq\varnothing). $$

Every denominator is at least $c\gt0$. Thus induction proves $\kappa_S\gt0$ for all $S$. Work in the Boolean polynomial algebra, where $y_i^2=y_i$. The coefficient of $y_S=\prod_{i\in S}y_i$ in

$$ \left(C-\sum_iw_i y_i\right)\sum_{S\subseteq[n]}\kappa_S y_S $$

equals $C\kappa_\varnothing=1$ for $S=\varnothing$, and otherwise equals

$$ \left(C-\sum_{i\in S}w_i\right)\kappa_S-\sum_{i\in S}w_i\kappa_{S\setminus\lbrace i\rbrace}=0. $$

The recurrence therefore proves the reciprocal identity on the entire Boolean cube. No convergence argument, denominator discretization, or restriction on real coefficients is used.

For comparison, the same positive coefficients have the integral formula

$$ \kappa_S=\int_0^\infty\exp\left(-\left(c+\sum_{i\notin S}w_i\right)t\right)\prod_{i\in S}(1-\exp(-w_i t))dt. $$

The integral is not needed for the algebraic proof. Its integrand is between zero and $\exp(-ct)$, and expansion of the finite product gives the same reciprocal identity.

## Full-cube mass bound

Evaluating the reciprocal identity at the all-zero input and at the singleton input $e_i$ gives

$$ \sum_S\kappa_S=\frac1c,\qquad \sum_{S:i\notin S}\kappa_S=\frac1{c+w_i}. $$

On the face $x_S=0$, the denominator is at most $c+\sum_{i\notin S}w_i$. Therefore the full-cube norm of the $S$ block is at most $M\kappa_S(c+\sum_{i\notin S}w_i)$. Summing and reversing finite sums yields

$$ \begin{aligned} \sum_S\kappa_S\left(c+\sum_{i\notin S}w_i\right)&=c\sum_S\kappa_S+\sum_iw_i\sum_{S:i\notin S}\kappa_S\cr &=1+\sum_i\frac{w_i}{c+w_i}\cr &\leq n+1. \end{aligned} $$

This estimate uses norms on the whole cube. In particular it does not replace the denominator by its value at one selected input.

An alternative decomposition into bounded scalar features separates $A(x)=a+\sum_i u_i x_i$. The features are the negative monomials $\prod_{j\in S}(1-x_j)$ and the mixed literals $x_i\prod_{j\in S}(1-x_j)$ with $i\notin S$. Their total absolute coefficient mass is

$$ \frac{|a|}{c}+\sum_i\frac{|u_i|}{c+w_i}\leq(2n+1)M. $$

Indeed $|a|\leq Mc$ and $|a+u_i|\leq M(c+w_i)$, so $|u_i|\leq M(2c+w_i)\leq2M(c+w_i)$. This weaker bound gives a fixed finite dictionary independent of the original head parameters.

## Admissibility of every approximating head

A whole affine function times a positive face indicator is uniformly one-head approximable by the existing declaration `uniformlyOneAtomApproximable_monomial_mul_affineValue` in `Atoms/AffineMonomialApproximation.lean`. Applying the exact original-model symmetry `FracAtom.flip` gives the corresponding negative-face block used above.

For a direct construction on a negative face, choose $\epsilon,\delta\gt0$ and use denominator

$$ D_{\epsilon,\delta}(x)=\epsilon+\sum_{j\in S}x_j+\delta\sum_{j\notin S}x_j $$

with numerator $\epsilon A(x)$. Every denominator slope is strictly positive. First take $\epsilon\to0$ and then $\delta/\epsilon\to0$. On $x_S=0$ the ratio converges uniformly to $A(x)$, and off that face it converges uniformly to zero. The cube is finite, so these statements give uniform approximation simultaneously at every input. Empty $S$ is also allowed. Arbitrary signs in $A$ are permitted by `FracAtom.ofPositiveAffineRatio`.

The same construction with numerator $\epsilon x_i$ proves admissibility for the mixed literal feature. It would be incorrect to assume that an arbitrary mixed face indicator is itself one-head approximable; only one opposing literal, or more generally one affine numerator, is used here.

## Consequence for a whole score and the precise remaining inequality

Apply the theorem independently to each head of a score $S=b+\sum_h\phi_h$. Group all blocks with the same anchored face and orientation. Their affine numerators add, so at most $2^{n+1}$ affine face blocks remain. The triangle inequality gives total block amplitude at most

$$ |b|+(n+1)\sum_h\|\phi_h\|_\infty\leq(n+1)\left(|b|+\sum_h\|\phi_h\|_\infty\right). $$

This preserves the real score exactly at the level of limiting blocks. Approximating the finitely many blocks sufficiently accurately then preserves every truth-table label with genuine heads. The width bound is exponential and does not give the desired constant overhead at $H\asymp2^n/\mathrm{poly}(n)$.

Suppose the original normalized margin is $\gamma\gt0$. Normalize the bounded scalar features by their total coefficient mass and sample them independently. The existing finite atomic sampling theorem gives simultaneous one-sided error less than half the original signed margin once

$$ K\gt \frac{8(2n+1)^2}{\gamma^2}\log(2^{n+1})=O\left(\frac{n^3}{\gamma^2}\right). $$

The factor $8$ follows by requiring error $\gamma/[2(2n+1)]$ in the normalized average and applying the bound $2^n\exp(-K\epsilon^2/2)\lt1$. This is a sufficient bound, not a lower bound on the number of samples.

The first missing lemma is a classification-specific support compression theorem: from an original $H$-head signed combination, choose at most $CH+\exp(o(n))$ genuine affine face blocks, or genuinely new heads, whose signed sum has the same labels and relative margin at least the target scale. The positive decomposition proves a polynomial mass budget, but does not prove this support bound. Reoptimizing coefficients in the full finite dictionary gives only a generic factorial-size integer separator in dimension $2^n$, whose margin scale is far smaller than $\exp(-\exp(\sqrt n))$ or $\exp(-\exp(n/\log n))$.

Thus this route currently isolates support compression as a separate requirement. It does not justify sampling without a dependence on margin, and it does not convert a badly conditioned representation into a truth table that lacks every good comparable-width representation.

## Kernel-checked ingredients

The file `formalization/HeadComplexity/Research/AnchoredAtomicDecomposition.lean` checks the following declarations in namespace `HeadComplexity.AnchoredAtomicDecomposition`.

- `uniformlyOneAtomApproximable_negativeFace_affine` supplies a genuine original-model head for every required approximation tolerance and every affine block.

- `scalar_coefficient_mass_le` proves the scalar-feature bound from the zero-input and singleton-input norm inequalities.

- `face_coefficient_mass_eq` and `face_coefficient_mass_le` prove the stronger block mass identity and bound from the displayed endpoint identities. They do not assert the existence or positivity of the reciprocal coefficients. Those are proved in writing above.

The module builds successfully. All five theorem declarations, including the affine complementation identity, have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. The later `PositiveReciprocalExpansion` module closes the previously missing coefficient existence and positivity ingredient. Its `reciprocal_with_endpoint_identities` and `ratio_with_full_cube_mass` prove the exact nonnegative expansion and the complete full-cube norm bound. The subsequent `OriginalAnchoredExpansion.original_head_expansion` checks the assembly for an arbitrary genuine original head, including simultaneous complementation and approximation of every block by one genuine head. Its `norm_eval_eq_atomSup` identifies the norm exactly with the requested full-cube atom supremum. See `positive_reciprocal_expansion_kernel.md` for the declarations and verification scope. The sum over a whole score and the proposed support-compression application remain the written arguments above.
