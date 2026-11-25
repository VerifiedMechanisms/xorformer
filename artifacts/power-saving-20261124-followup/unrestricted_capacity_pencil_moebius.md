# A Boolean obstruction to the multihead Möbius tangent

## Exact statement

The one-head Möbius deformation from `unrestricted_capacity_full_parameter_contacts.md` does not extend to a universal two-head parameter flow. This fails even when both denominators depend on the same single affine statistic, if the numerators are unrestricted affine forms.

On six Boolean variables, put

$$ T=\sum_{i=0}^5x_i,\qquad L_1=x_0-x_1,\qquad L_2=x_2-x_3,\qquad B_1=1+T,\qquad B_2=1+2T. $$

Consider the genuine original-model score

$$ S=1+\frac{L_1}{B_1}+\frac{L_2}{B_2}. $$

Both denominator constants and every denominator slope are strictly positive. Each ratio is realized by `FracAtom.ofPositiveAffineRatio`. Moreover $S\geq1/6$ on the full cube: a nonzero first numerator has denominator at least two, and a nonzero second numerator has denominator at least three.

Allow arbitrary affine numerator variations $A_1,A_2$, arbitrary affine denominator variations $D_1,D_2$, and an arbitrary bias variation $c$. This includes a larger space than the full normalized parameter tangent. Every resulting quotient-rule tangent has the form

$$ V=c+\frac{A_1}{B_1}+\frac{A_2}{B_2}-\frac{L_1D_1}{B_1^2}-\frac{L_2D_2}{B_2^2}. $$

**Theorem.** No such $V$ agrees with $1-S^2$ at every Boolean vertex. In particular, no differentiable parameter path through these ordered two heads realizes the Möbius family $S\mapsto(S+t)/(1+tS)$, even only on the Boolean cube.

## Twelve actual rows

For $k=0,1,2$, choose the last two coordinates as $(0,0),(1,0),(1,1)$ respectively. In the first pair choose exactly one bit equal to one, and do the same in the second pair. Write $\varepsilon=L_1\in\lbrace-1,1\rbrace$ and $\eta=L_2\in\lbrace-1,1\rbrace$. On these four rows,

$$ T=2+k,\qquad B_1=3+k,\qquad B_2=5+2k. $$

Let $C_k(F)$ be the unnormalized signed sum of these four values with weights $\varepsilon\eta$. Any affine function has zero such sum. If $d_{1,i}$ denotes the coefficient of $x_i$ in $D_1$, and similarly for $D_2$, direct expansion gives

$$ C_k(V)=-\frac{2(d_{1,2}-d_{1,3})}{(3+k)^2}-\frac{2(d_{2,0}-d_{2,1})}{(5+2k)^2}. $$

The integer weights

$$ (\lambda_0,\lambda_1,\lambda_2)=(-15975,81536,-83025) $$

satisfy the exact identities

$$ \sum_{k=0}^2\frac{\lambda_k}{(3+k)^2}=0,\qquad \sum_{k=0}^2\frac{\lambda_k}{(5+2k)^2}=0,\qquad \sum_{k=0}^2\frac{\lambda_k}{(3+k)(5+2k)}=2. $$

Consequently the twelve-row functional $\Lambda(F)=\sum_k\lambda_kC_k(F)$ annihilates every $V$. On the other hand,

$$ C_k(1-S^2)=-\frac8{(3+k)(5+2k)},\qquad \Lambda(1-S^2)=-16. $$

This proves the theorem without invoking an identity outside the Boolean cube. $\blacksquare$

## Formalization and scope

`HeadComplexity/Research/PencilMoebiusTangentObstruction.lean` checks the literal admissible atoms, full-cube strict positivity, the twelve-row annihilator for arbitrary real affine variations, its value on the Möbius direction, and the nonmembership conclusion. The principal declarations are `HeadComplexity.PencilMoebiusTangentObstruction.annihilator_tangent`, `annihilator_moebius`, and `no_moebius_tangent`. The quotient-rule interpretation for differentiable parameter paths is the written calculus deduction; the finite linear-space nonmembership is kernel checked.

This rules out a specific universal parameter-flow construction. It does not obstruct a different path preserving the same unit constraints, a different representation of the score, or a truth-table-preserving repair. The score has a constant positive truth table, which is easy. It also does not contradict the scalar rational-function Möbius argument: the arbitrary numerators here are not functions of the shared statistic $T$.
