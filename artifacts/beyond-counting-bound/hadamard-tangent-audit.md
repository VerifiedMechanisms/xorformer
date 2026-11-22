# Hadamard Products and Logarithmic Tangents

## Exact identity

Let $X=\lbrace0,1\rbrace^n$, and let $L\subseteq\mathbb R^X$ be the vector space of affine evaluation tables. For positive affine denominator tables $B_1,\ldots,B_H$ and affine tables $A_1,\ldots,A_H$, define

$$ Q_t(x)=\prod_{h=1}^H\bigl(B_h(x)+tA_h(x)\bigr). $$

For all sufficiently small real $t$, every factor is positive at every point of the finite cube. The product rule gives

$$ \left.\frac{d}{dt}\log Q_t(x)\right|_{t=0}=\sum_{h=1}^H\frac{A_h(x)}{B_h(x)}. $$

If $H\geq1$, a constant score term $c$ is absorbed by replacing $A_1$ with $A_1+cB_1$. Thus an admissible score is a logarithmic tangent vector to the coordinatewise product map from $L^H$. No restriction on target-dependent denominators has been introduced.

This identity does not identify the collection of signs of these tangent vectors with the signs of points in a fixed linear space. The base point, and hence the tangent space, varies with the representation.

## The published degree formula

[Bocci, Carlini, and Kileel, Theorem 6.8 and Remark 6.9](https://iris.polito.it/retrieve/handle/11583/2646826/119104/HadamardARXIV.pdf), compute the degree of the $H$-fold Hadamard power of a generic projective $n$-plane in a sufficiently large ambient projective space. In the equal-factor case their formula is

$$ \frac{(nH)!}{(n!)^H H!}. $$

Their stated sufficient ambient-dimension hypothesis is at least $\binom{n+H}{H}-1$. The Boolean evaluation space instead has ambient dimension $2^n-1$, and its affine-evaluation plane is a specified nongeneric plane. At $H$ of order $2^n/n^\alpha$, with fixed $1\lt\alpha\lt2$, the sufficient dimension hypothesis fails by an exponential factor in $n^2$. The formula therefore cannot be asserted for this manuscript model.

Even as a hypothetical bound, this factorial expression has logarithm

$$ (n-1)H\log H+O(nH), $$

uniformly in the regime under discussion, by Stirling's formula. Since $\log H$ is of order $n$, this remains of order $n^2H$. Quotienting only by the common permutation of the heads does not supply an unbounded counting gain.

## Status

The logarithmic-tangent identity is exact. A theorem bounding the Boolean sign patterns of all these moving tangent spaces strongly enough to establish the requested lower bound is absent. Generic Hadamard-product degrees, tangent-space dimension, and factor identifiability do not fill that gap. This approach is blocked until a new invariant controls the real signs for the particular Boolean evaluation plane.
