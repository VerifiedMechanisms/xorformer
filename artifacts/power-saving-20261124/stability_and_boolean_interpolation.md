# Stable denominator products and Boolean interpolation

## Status

This note tests a possible use of real stability for the unrestricted head model. The denominator product is real stable, and the original score is a tangent derivative of its logarithm. However, Boolean multilinear interpolation does not preserve real stability, even for a product of two strictly positive coherent affine denominators. Logarithmic concavity and submodularity alone do not constrain the signs of arbitrary tangents.

These are elementary written observations and an exact counterexample. They do not prove an improved head lower bound. The stability counterexample, cube agreement, and original product stability are Lean verified as recorded below; the general tangent and cone discussion is a written proof.

## The exact tangent interpretation

A real polynomial is real stable if it is nonzero whenever every input coordinate has strictly positive imaginary part. If an affine real form has all slopes strictly positive, its imaginary part is strictly positive on this domain. If all slopes are strictly negative, its imaginary part is strictly negative. A positive constant is nonzero there as well. Thus every admissible denominator $B_h$ is real stable, and so is

$$ Q(x)=\prod_{h=1}^H B_h(x). $$

Every such denominator is positive on the entire real cube $[0,1]^n$, since the extrema of an affine form occur at vertices. For nonconstant denominators with strict coherent slopes, arbitrary affine numerators $A_h$ give an admissible perturbation $B_h+\varepsilon A_h$ for every sufficiently small real $\varepsilon$. Finiteness of the heads and coordinates makes one neighborhood work for all heads. The logarithmic derivative is exactly

$$ \left.\frac{\partial}{\partial\varepsilon}\log\prod_h\big(B_h(x)+\varepsilon A_h(x)\big)\right|_{\varepsilon=0}=\sum_h\frac{A_h(x)}{B_h(x)}. $$

Constant-denominator heads retain the separate original numerator restriction. They can simply be left outside this tangent description, or treated as limits of strictly coherent denominators. No constraint on their contribution is silently imposed here.

Writing $b_h$ for the slope vector, the real Hessian on the cube satisfies

$$ \nabla^2\log Q(x)=-\sum_h\frac{b_hb_h^{\top}}{B_h(x)^2}. $$

It is negative semidefinite. Its off-diagonal entries are nonpositive, because slopes within each nonconstant head have one sign. Thus $\log Q$ is concave and submodular on the real cube. These are genuine properties of the base denominator product, including mixtures of positive and negative denominator orientations.

## Boolean interpolation destroys real stability

Take three variables and the admissible denominators

$$ B_1=3+x_1+27x_2+8x_3,\qquad B_2=2+15x_1+15x_2+x_3. $$

Every constant and slope is strictly positive. Reducing $B_1B_2$ by the Boolean identities $x_i^2=x_i$ gives its unique multilinear cube interpolation

$$ F=6+62x_1+504x_2+27x_3+420x_1x_2+121x_1x_3+147x_2x_3. $$

At $x_3=-1$ this becomes

$$ F(x_1,x_2,-1)=-21-59x_1+357x_2+420x_1x_2. $$

For a real bilinear polynomial $a+bx+cy+dxy$, the root in $x$ when $y=i$ has imaginary part

$$ \mathrm{Im}\left(-\frac{a+ci}{b+di}\right)=\frac{ad-bc}{b^2+d^2}. $$

Here $bc-ad=-12243$, so this root has strictly positive imaginary part. The denominator $b+di$ is nonzero. Now replace $x_3=-1$ by $x_3=-1+i\varepsilon$. The corresponding root in $x_1$, with $x_2=i$ fixed, depends continuously on $\varepsilon$ near zero. For sufficiently small positive $\varepsilon$, it still has positive imaginary part. This gives a zero of $F$ with all three coordinates in the upper half-plane. Therefore $F$ is not real stable.

This is also an explicit violation of the necessary Rayleigh inequality for multiaffine stable polynomials. That general criterion appears in [Wagner, Multivariate stable polynomials, Section 3](https://www.math.uwaterloo.ca/~dgwagner/ceb_wagner.pdf), but the direct root calculation above proves the needed failure without relying on the criterion.

The stability-preserving operation that discards every nonsquarefree monomial is different from Boolean interpolation, which identifies every positive power of a coordinate with that coordinate. The former operation cannot be substituted for the latter when preserving cube evaluations or labels.

The file `formalization/HeadComplexity/Research/BooleanInterpolationStability.lean` verifies three statements in namespace `HeadComplexity.BooleanInterpolationStability`: `denominator_product_upperStable`, `interpolation_agrees_on_boolean_cube`, and `multilinear_not_upperStable`. Its exact complex zero uses

$$ x_1=\frac{-1518114267+116143413i}{1808988641},\qquad x_2=i,\qquad x_3=-1+\frac{i}{100}. $$

The file compiles, and each displayed theorem's axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. This is a finite exact algebraic certificate of the counterexample, not formal verification of an unrestricted lower bound.

## Why the cone properties alone do not give a sign bound

Fix a smooth function $g$ on the real cube whose Hessian is uniformly negative definite and whose mixed second derivatives are all uniformly strictly negative. Such a function can itself be a logarithm of an admissible denominator product with $n$ heads: take $B_h(x)=1+x_h+\sum_i x_i$ for $1\leq h\leq n$. Their slope vectors are independent and strictly positive, so the displayed Hessian formula gives both strict properties uniformly on the compact cube.

For any smooth $T$, both $g+\varepsilon T$ and $g-\varepsilon T$ retain these properties for sufficiently small positive $\varepsilon$, by compactness and continuity. Every real table on the Boolean cube has a multilinear polynomial extension $T$.

Thus the cone of concave submodular functions has tangent directions with arbitrary prescribed cube signs at its interior points. This is a statement about that function cone, not a proof that a fixed small number of affine denominators realizes every tangent. The low-head parameterization is the substantive information a successful argument would have to use.

The remaining possibility is a quantitative geometric bound on tangent sign tables of the specific finite product parameterization. Real stability, concavity, and submodularity by themselves do not supply such a bound, and the direct multilinear-stability reduction is false.
