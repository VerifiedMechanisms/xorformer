# Shared threshold chambers for one-head feasible bases

## Status

The scalar and full-cube equivalences below, and the exact six-bit counterexample, are kernel checked in `HeadComplexity/Research/OneHeadSharedChamber.lean`. They do not prove a capacity improvement or a truth table with small optimal margin. They isolate a stronger condition that a feasible-basis counting argument must exploit.

## Shared-chamber equivalence

Let $A$ and $B$ be affine forms on the Boolean cube, with $B(x) \gt 0$ everywhere. Put

$$ U=(A+B)/2,\qquad V=(B-A)/2. $$

For prescribed labels $f(x)\in\lbrace -1,+1\rbrace$, the full unit-gap condition is equivalent to two simultaneous weak threshold inequalities:

$$ f(x)A(x)\geq B(x)\quad\Longleftrightarrow\quad f(x)U(x)\geq0\qquad\text{and}\qquad f(x)(-V(x))\geq0. $$

Without prescribed labels, the equivalent condition is $U(x)V(x)\leq0$. The assumption $B=U+V\gt0$ is essential to the converse. At a positive unit contact, $U=B$ and $V=0$. At a negative unit contact, $U=0$ and $V=B$.

Now fix $n+1$ affinely independent Boolean contact points $v_j$, with signs $\sigma_j$. Let $\lambda_j$ be their affine barycentric coordinates. The unique interpolating numerator satisfies

$$ U(x)=\sum_{\sigma_j=+1}\lambda_j(x)B(v_j),\qquad V(x)=\sum_{\sigma_j=-1}\lambda_j(x)B(v_j). $$

Thus a feasible extension requires that these two complementary-contact affine forms lie in the closures of the same threshold chamber after changing the sign of $V$. In the original positive-orientation model, their sum $B$ must additionally have strictly positive constant and coordinate coefficients. Arbitrary real-value interpolation fibers omit both the global shared-chamber condition and this coefficient constraint.

The Lean declarations `unit_gap_iff_shared_chamber`, `unit_gap_iff_product_nonpos`, `full_gap_iff_shared_chamber`, `positive_contact`, and `negative_contact` check the algebraic and full-cube statements. The barycentric specialization is written reasoning using affine interpolation.

## The complete coefficient-ratio order does not determine the extension

Use six bits, written most significant bit first, and contact vertices

$$ (7,8,13,17,19,32,43),\qquad (\sigma_j)=(+1,+1,+1,+1,-1,+1,-1). $$

These are the affinely independent contacts already certified in `OneHeadFeasibleBasisNonuniqueness.lean`. List an affine form's constant coefficient first. Two coefficient pairs are

$$ b^{(0)}=(20,22,26,4,3,28,24),\qquad a^{(0)}=(216,-174,-366,-192,-193,-168,220), $$

$$ b^{(1)}=(1,14,29,9,5,20,9),\qquad a^{(1)}=(119,-104,-219,-109,-125,-98,139). $$

All denominator coefficients are strictly positive. Both pairs satisfy all seven prescribed contacts exactly, and $|A^{(k)}(x)|\geq B^{(k)}(x)$ at all 64 vertices. Nevertheless, their signs differ at vertex 4: at $x=(0,0,0,1,0,0)$ the values are $23$ and $-6$, respectively.

For both pairs the seven ratios $a_i/b_i$, including the intercept, are strictly increasing in the identical index order

$$ (4,3,2,1,5,6,0). $$

The Lean declarations `RatioOrderCounterexample.same_strict_ratio_order`, `common_basis_contacts`, `full_cube_unit_gap`, and `different_labels` certify these assertions. `atom` and `atom_eval` realize the ratios as genuine original `FracAtom` heads using `ofPositiveAffineRatio`.

This rules out an injective branch code consisting only of the contact basis, contact signs, and coefficient-ratio permutation. It does not rule out an $n^{O(n)}$ count with additional information, and it says nothing adverse about the best unrestricted margin of either truth table.

## Remaining counting problem

For each fixed Boolean contact simplex and its contact signs, count the threshold chambers admitting the two complementary zero-contact witnesses above, whose difference has a positive coherent coefficient vector. A bound of $n^{O(n)}$ would be useful in a larger feasible-chart argument. A lower bound of $2^{\Omega(n^2)}$ for one fixed simplex would rule out that particular bound. Neither is proved here.

A boundary construction must preserve the unit gap on every cube vertex. Merely letting the denominator vanish on an anchored face and inducing arbitrary affine values there is insufficient: the outside-face contact equations can force numerator and denominator coordinate increments to coincide, which removes the purported branch freedom.
