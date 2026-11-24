# Scalar mixed-cylinder compilation and localization tests

## Proved scalar compiler

A cylinder fixes $r$ coordinates to one and $s$ coordinates to zero. Its scalar indicator is uniformly approximable on the entire Boolean cube by

$$ \max(1,\min(r,s)) $$

original admissible fractional heads, with a free bias. The approximation concerns scalar values, so it also preserves any strictly represented truth table after summing finitely many such blocks and choosing the error sufficiently small. It does not provide a relative-margin bound.

This statement is kernel checked as `HeadComplexity.ScalarCylinderCompiler.uniformlyAtomsApproximable_cylinder_min` in `formalization/HeadComplexity/Research/ScalarCylinderCompiler.lean`.

**Proof.** Suppose $r\gt 0$, and let $t$ count the positive literals. Interpolate any scalar profile $F(0),\ldots,F(r)$ in the reciprocal basis with positive distinct shifts:

$$ F(t)=c+\sum_{j=1}^{r}\frac{b_j}{t+q_j},\qquad q_j\gt 0. $$

Absorb $c$ into the first numerator, obtaining $r$ affine numerators. Gate all these ratios to the negative face by adding a large positive denominator slope on each negative literal. Small positive perturbations of the remaining slopes keep every head admissible. This preserves the interpolated profile on the face and sends every term to zero outside it. Complementing every input exchanges $r$ and $s$. If one side is empty, the inherited one-head anchored-face approximation applies.

The absorption is specific to a scalar profile. Multiplication by an additional arbitrary affine score would make the modified first numerator quadratic. The previously checked affine-cylinder budget remains $\min(r,s)+1$.

## A counterexample to the first localization conjecture

The proposed scalar lower bound $\min(r,s)+1$ is false, including in approximation closure. For the point $1100$, put $t=x_1+x_2$ and $z=x_3+x_4$. On $t\in\lbrace0,1,2\rbrace$,

$$ \mathbf 1_{t=2}=\frac{6t(t-1)}{(t+1)(t+2)}=\frac{6t+18}{t+1}-\frac{36}{t+2}. $$

Consequently, as $R\to\infty$ and $\eta\to0^+$,

$$ \frac{6t+18}{1+t+Rz+\eta\sum_i x_i}-\frac{36}{2+t+Rz+\eta\sum_i x_i}\to\mathbf 1_{x=1100} $$

uniformly on the full cube. Each denominator has a positive intercept and strictly positive slopes, hence admits a genuine original-model fractional head. Numerator signs and cancellation are unrestricted. This explicit construction, rather than the floating-point search, establishes the counterexample.

## A proved obstruction when all orientations agree

The quantitative error bound below is a written proof. Its arbitrary-precision consequence, including coordinate-face restrictions, is kernel checked in `formalization/HeadComplexity/Research/MonotonePoleLocalization.lean`. The declarations `dimension_le_of_positive_atom_approximation` and `dimension_le_of_negative_atom_approximation` give the endpoint statements; `face_dimension_le_of_positive_atom_approximation` and its negative counterpart give the mixed-point restrictions. The proof uses closedness of the finite-dimensional Boolean polynomial space, so it imposes no bounds on the approximating coefficients.

**Claim.** Let $q\lt r$. A sum of $q$ positive-orientation heads and a bias cannot approximate the all-one point indicator on an $r$-cube with uniform error smaller than $2^{-r}$. The analogous statement holds for negative-orientation heads at the all-zero point.

**Proof.** Write the score as $S=P/D$, where $D$ is the product of its $q$ positive affine denominators and $P$ has degree at most $q$. Normalize each denominator to have value one at the all-one vertex $v$. Monotonicity gives $0\lt D(x)\leq1$ throughout the cube and $D(v)=1$. If $|S(x)-\mathbf1_{x=v}|\leq\epsilon$, then $|P(x)-\mathbf1_{x=v}|\leq\epsilon$. The alternating cube sum annihilates every polynomial of degree smaller than $r$, while its value on the point indicator has absolute value one. The triangle inequality gives $1\leq2^r\epsilon$.

Restricting a larger cube to the positive literals shows that arbitrary-precision approximation of a mixed point by heads all having positive orientation requires at least $r$ heads. Negative orientation analogously requires at least $s$ heads. The conclusion allows arbitrary coefficients and cancellation within that orientation class.

For a point with three positive and three negative literals, this rules out every two-head approximating family whose orientations agree. It leaves one positive and one negative head unresolved.

## The remaining mixed-orientation test

The exploratory scripts `probe_mixed_point_closure.py` and `probe_mixed_point_norming.py` optimize real parameters with SciPy. Their output is finite floating-point evidence only. Singular value cutoffs, finite parameter ranges, local optimization, and solver tolerances preclude a universal conclusion.

For the six-bit point $111000$, two heads of the same orientation produced a smallest observed uniform error near $1/8$. Opposite orientations did not produce a vanishing error. On the four-bit point $1100$, the opposite-orientation norming experiment suggested

$$ |S(1100)|\leq7\max_{x\neq1100}|S(x)|. $$

The largest observed ratio approached seven as the positive head concentrated on $x_3=x_4=0$ and the negative head on $x_1=x_2=1$. The corresponding limiting model is a sum of affine scores on two opposing faces plus a constant. Its $3+3+1$ bound explains this candidate value. No proof that these limits exhaust the original two-head class has been obtained.

The first failing lemma is a uniform norming bound for the full opposite-orientation pair, allowing coefficient blowup and all boundary rates. Degree clearing alone cannot establish it. A general quotient with the product of two opposing face denominators can approximate their intersection point; the original two-head model has the additional numerator restriction

$$ P\in B_1\mathrm{Aff}+B_2\mathrm{Aff}, $$

which any valid proof must use. The already checked strict-interior opposite-orientation independence theorem does not control degenerating zero slopes, boundary poles, or divergent coefficients.

Even a proof of this two-head obstruction would be a structural checkpoint. It would not count all unrestricted truth tables at width comparable to $N/n^{3/2}$.

## Verification

The scalar compiler build completed successfully with 2553 jobs. Its five exported declarations have transitive axioms `propext`, `Classical.choice`, and `Quot.sound`. Exact logs are `scalar-cylinder-build.txt` and `scalar-cylinder-axioms.txt`.

The monotone localization build completed successfully with 2541 jobs. Its seven exported declarations have transitive axioms `propext`, `Classical.choice`, and `Quot.sound`; see `monotone-pole-build.txt` and `monotone-pole-axioms.txt`. The intermediate `dimension_le_of_maximal_denominator_approximation` assumes only that the product of denominators is maximal at the target vertex.
