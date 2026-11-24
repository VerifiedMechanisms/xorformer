# Positive pole orders do not fix multivariate minor signs

## The attempted simplification

For one head, positive denominator clearing reduces the entire sign class to affine threshold functions. In a scalar Cauchy system, determinants have Vandermonde factorizations whose signs are fixed by the pole order. A possible unrestricted capacity shortcut would extend such an order rule to the positive multivariate denominator family.

The following exact two-head calculation shows that coordinate orders and coordinatewise ratio orders do not suffice. It concerns oriented-matroid minors, not the number of truth tables. In the example dimension the whole generic linear span is fixed, so the minor variation itself creates no new capacity.

## A compact determinant formula

For $x\in\lbrace0,1\rbrace^3$, put

$$ B_1(x)=1+u_0x_0+u_1x_1+u_2x_2,\qquad B_2(x)=1+v_0x_0+v_1x_1+v_2x_2. $$

Use the seven nonzero cube vertices in lexicographic order, and the cleared feature columns

$$ B_1B_2, x_0B_2, x_1B_2, x_2B_2, x_0B_1, x_1B_1, x_2B_1. $$

Define

$$ \delta_{ij}=u_j(1+v_i)-v_j(1+u_i). $$

Direct expansion of the resulting matrix $M$ gives

$$ \det M=\delta_{01}\delta_{12}\delta_{20}+\delta_{10}\delta_{21}\delta_{02}. $$

The apparent degree-six terms cancel. The determinant has total degree five and fifty monomials. The script `positive_minor_factor_check.py` constructs the seven-by-seven matrix over the exact polynomial ring over the rationals and checks the displayed identity by symbolic expansion.

## Fixed orders, opposite signs, and a singular point

Every row of this table satisfies all four sets of strict inequalities

$$ 0\lt u_0\lt u_1\lt u_2,\qquad 0\lt v_0\lt v_1\lt v_2,\qquad u_i\lt v_i,\qquad \frac{u_0}{v_0}\lt\frac{u_1}{v_1}\lt\frac{u_2}{v_2}. $$

| First slope vector | Second slope vector | Cleared determinant |
| --- | --- | --- |
| $(4,9,36)$ | $(10,13,46)$ | $151360$ |
| $(3,5,7)$ | $(21,33,40)$ | $-10476$ |
| $(12,38,39)$ | $(13,41,42)$ | $0$ |

All slopes are strictly positive, so every affine denominator is genuinely admissible. The rational-feature matrix is obtained by dividing each row by $B_1(x)B_2(x)\gt0$, which preserves the determinant sign.

The singular pair has a simple exact explanation:

$$ \frac{13(x_0-x_1)}{14B_1(x)}-\frac{x_0-x_1}{B_2(x)}=0\qquad\text{for every Boolean }x. $$

After clearing denominators, its numerator is

$$ \frac{(x_0-x_1)(x_0+x_1-1)}{14}=\frac{x_0^2-x_0-x_1^2+x_1}{14}, $$

which vanishes on the cube. When $x_0\neq x_1$, the denominators are proportional; when $x_0=x_1$, the numerator vanishes. Thus the relation comes from different restrictions to Boolean faces, even though the global poles are distinct and strictly ordered.

## Why this is not a capacity counterexample

Every displayed cleared feature is a Boolean polynomial of degree at most two. That polynomial space has dimension seven. Whenever the determinant is nonzero, these seven features span the whole space. Consequently the set of strict truth tables available after arbitrary numerator coefficients is the same full class of quadratic threshold tables at both nonsingular parameter points.

The calculation rules out a simple positive order rule for individual multivariate minors. It does not rule out a bound after quotienting by the entire numerator span, a density-sensitive count of sign classes, or a constant-overhead repair. Generic branch counts and changing determinant signs remain insufficient substitutes for truth-table counts.

## Verification boundary

The determinant identity and numerical entries were checked with exact rational polynomial arithmetic by the committed script. The Boolean-ideal relation and the dimension argument are written proofs. No new Lean declaration is claimed for this calculation, and no model definition was changed.
