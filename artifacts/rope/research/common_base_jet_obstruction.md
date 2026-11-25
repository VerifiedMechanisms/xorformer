# A Five-Head Obstruction for Regular Common-Base Jets

This note studies one possible improvement of the six-head vanilla upper bound for the separated pure three-head family. It proves an exact polynomial moment obstruction. It does not prove a five-head Boolean lower bound, and it does not determine whether the source family has vanilla minimum four, five, or six.

## The moment statement

Let $H\geq 1$. Let $A_i,B_i$ be real homogeneous linear forms in $r$ variables, for $i=0,\ldots,H-1$, satisfying

$$ \sum_i A_i=0,\qquad \sum_i A_iB_i=0. $$

Set $C=\sum_iA_iB_i^2$. If $r\gt H-1$, then $C$ is invariant under translation by a nonzero vector. In particular, it cannot equal a cubic having no nonzero translation direction.

**Proof.** Replace every $B_i$ by $B_i-B_0$. Both the quadratic cancellation and $C$ are unchanged because of the two displayed identities. The term indexed by zero disappears. Write the remaining $H-1$ pairs as $A'_i,B'_i$.

The linear map $v\mapsto(A'_i(v)+B'_i(v))_i$ has a nonzero kernel vector when $r\gt H-1$. At that vector,

$$ 0=\sum_iA'_i(v)B'_i(v)=-\sum_iA'_i(v)^2. $$

Thus every $A'_i(v)$ and $B'_i(v)$ vanishes. Every summand, and hence $C$, is invariant under translation by $v$. $\blacksquare$

## The source section has five essential coordinates

The source cubic in its six independent affine coordinates is

$$ W=N_0D_1D_2+N_1D_0D_2+N_2D_0D_1. $$

On the hyperplane $F=N_0+cD_0=0$, its restriction is

$$ W|_{F=0}=D_0\bigl(N_1D_2+N_2D_1-cD_1D_2\bigr). $$

This has no nonzero translation direction for any real $c$. Indeed, if its directional derivative vanishes identically, evaluation at five coordinate-pair points successively forces the direction components of $D_0,D_2,D_1,N_1,N_2$ to vanish. Equivalently, one may obtain the directional derivative by the exact polarization identity

$$ 2\partial_vW(x)=W(x+v)-W(x-v)-2W(v). $$

The moment theorem therefore excludes such a representation with at most five pairs. The common-base finite-difference construction using six heads is not reducible to five merely by finding a more economical set of these second-order moments.

## What this says about the proposed approximation route

Consider denominators with a common limit $F$, with first perturbations $F+tB_i$, and numerator expansions whose largest pole is $t^{-2}A_i$. If the divergent terms cancel, then, modulo $F$, their first two moment identities are exactly the displayed cancellations. The finite second-order term has cubic part $\sum_iA_iB_i^2$ modulo $F$. Terms involving the next numerator coefficients or second denominator perturbations retain a factor of $F$ after clearing $F^3$ and disappear on this hyperplane.

Consequently this regular second-order construction, with common base chosen from the positive endpoint pencil $F=N_0+cD_0$, cannot give the source cubic with five heads. The case $c=1$ gives a positive uniformly increasing base in the explicit physical family, so this addresses the natural endpoint-based attempt to improve its six-head simulation.

This argument concerns an exact leading-polynomial ansatz. It leaves open higher-order numerator poles, more singular parameter paths, several distinct limiting denominators, and alternative finite Boolean sign representations. None of those possibilities is excluded by the moment theorem.

## Lean verification

`HeadComplexity/Polynomial/CommonBaseJetObstruction.lean` proves:

- `exists_common_kernel_of_quadratic_zero`;
- `exists_cubic_translation_direction`;
- `endpoint_polarization` and `endpoint_no_translation_direction`;
- `no_endpoint_moments_of_small_head_count` and `no_five_head_endpoint_moments`.

The Lean statements formalize the exact moment identities and the source-section obstruction. The interpretation of asymptotic numerator and denominator expansions in the preceding section is a mathematical explanation, not a separate Lean limit theorem.
