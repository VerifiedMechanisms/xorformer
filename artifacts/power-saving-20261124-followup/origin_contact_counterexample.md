# An origin contact does not preserve the constant-denominator branch

## Kernel-checked counterexample

Work on six bits, with vertex numbers written most significant bit first. The seven affinely independent contact vertices and prescribed unit values are

$$ (0,18,20,29,44,46,57),\qquad (+1,+1,-1,+1,+1,-1,-1). $$

Write an affine form's constant coefficient first. Set

$$ b=(1,3,1,1,1,1,1),\qquad a=(1,-31,15,55,-19,-13,-47). $$

Every coefficient of $B$ is strictly positive. The ratio $A/B$ is an admissible original head, takes exactly the prescribed unit values at all seven contacts, and has $|A(x)|\geq B(x)$ on the entire cube.

The unique affine numerator interpolating these same contact values over the constant denominator $1$ is

$$ a^{\mathrm{const}}=(1,-6,2,10,-4,-2,-8). $$

It too satisfies a full-cube unit gap, since its 64 values are nonzero odd integers. But at vertex 11, namely $x=(0,0,1,0,1,1)$, the original numerator equals $-4$ and its denominator equals $4$, while the constant-denominator numerator equals $1$. Thus the two truth tables differ.

This disproves the proposed lemma that including the denominator's minimizing vertex among a full unit-contact basis permits replacement by a constant denominator while preserving the basis and the whole truth table. It does not obstruct changing the contact basis, and neither truth table has been shown to have small optimal unrestricted margin.

All statements above are checked in `HeadComplexity/Research/OriginContactBranchCounterexample.lean`, namespace `HeadComplexity.OriginContactBranchCounterexample`. The principal declarations are `basis_contains_origin`, `basis_affine_injective`, `constant_interpolant_unique`, `both_full_cube_unit_gaps`, `different_labels`, and `atom_eval`.

## Exact balance calculation for this branch

The following calculation is written and checked by rational finite computation, not formalized in Lean. Allow the denominator coefficient vector $b$ to vary while retaining the same contact basis and contact values. The resulting unique numerator satisfies

$$ A(11)=b_0-2b_1+2b_2-b_3-b_5+b_6,\qquad B(11)=b_0+b_3+b_5+b_6. $$

The original branch has negative label at vertex 11. Its unit-gap constraint gives

$$ b_0\leq b_1-b_2-b_6\leq b_1,\qquad \frac{b_0}{\sum_{i=0}^{6}b_i}\leq\frac12. $$

The nonnegative boundary coefficient vector $(1,1,0,0,0,0,0)$ satisfies all 64 unit-gap inequalities for this same truth table. Convex combinations with the strictly positive vector above remain feasible, have strictly positive denominator coefficients, and approach intercept fraction $1/2$. Thus $1/2$ is the exact supremum. This example only prevents denominator mass fraction $1$ in the fixed chart; it does not refute an inverse-polynomial balance bound.

## Discovery and verification

`search_origin_contact_basis.py` sampled dense origin-containing Boolean bases and positive integer denominator vectors. The stored discovery used 7,730 sampled bases, with 4,530 nonsingular bases and 15,263 feasible denominator samples. Once a discrepancy was found, Sympy verified every contact and every full-cube inequality using exact rational arithmetic. The coefficient reduction and balance LP data are in `origin-contact-basis-n6.json`. The Lean certificate is independent of the floating search and uses the reduced integer vectors displayed above.
