# Independent audit of generic radial initial degree

## Scope and verdict

I independently read `generic_radial_initial_degree.md` on 2026-11-24. The elementary proofs of its low-degree limit theorem, Hamming-star rank witness, and weak-sign compactness corollary are correct as stated. They concern fixed radial directions, or a uniformly conditioned compact family of directions if the corresponding uniform estimates are imposed. They give no reduction of unrestricted finite-scale head representations to that regime.

## Matrix estimate

The Boolean coefficient of a set $S$ of size $s$ in $x_i/(1+tC_h)$ first appears at order $s-1$. At that order it is

$$ \mathbf 1_{i\in S}(-1)^{s-1}(s-1)!\prod_{j\in S\setminus\lbrace i\rbrace}c_{hj}. $$

Boolean reduction cannot increase degree. To achieve all $s$ distinct variables at order $s-1$, every variable other than the outside factor $x_i$ must occur exactly once. Constant terms in $C_h$ therefore do not affect the coefficient. The row factorization and the derivative-interpolation matrix are correct.

An invertible block from rows of degrees at most $K$ solves the coefficient vector of an arbitrary score from its low-degree table coefficients. A high row of degree $s\gt K$ then contains powers of the scale at least $t^{s-K}$. Boundedness of the inverse block gives the asserted $O(t)$ bound relative to the table supremum norm. This step does not assume bounded numerator coefficients. The constant generator is handled separately by evaluating the score at the zero vertex.

## Generic-rank witness

Distinct nonzero binary syndrome labels give a coloring in which two equal-color vertices have distance at least three. Choosing centers in the lower Hamming ball of radius $K-1$ gives disjoint closed stars entirely in the ball of radius $K$. Evaluation of multilinear polynomials of degree at most $K$ on that ball is an isomorphism, by its triangular subset matrix.

A prescribed value on one star leaf isolates one selected derivative functional. This proves independence of all $nH$ derivative columns. The selected maximal minor is a nonzero polynomial, and a small positive perturbation of zero coordinates keeps it nonzero. Thus the generic rank condition genuinely occurs with strictly positive denominator slopes.

## Weak signs and the external probability statement

Normalizing representing tables to supremum norm one before passing to a subsequence gives a nonzero limiting table. It retains weak target signs, even where the limit vanishes. This correctly addresses the higher-order decision of zero coordinates; the argument does not replace eventual strict signs by strict signs of one leading coefficient.

I separately opened [Anthony's primary paper](https://arxiv.org/pdf/2610.15057), version 2, and checked its Theorem 1 and Section 6. The theorem gives concentration of strict threshold degree in the central one or two integers. Section 6 transfers the same concentration bound to weak threshold degree through the parity duality

$$ \mathrm{td}_{\mathrm w}(F)+\mathrm{td}(F\chi)=n. $$

Thus the weak-degree statement used in Corollary 4 has the cited source support. This is a check of that external theorem's statement and its application, not an independent reproof of the paper.

## Verification distinction

This audit is a written mathematical audit. The generic derivative-rank theorem has not been Lean checked here. The separately kernel-checked radial moment and moving-numerator transfer theorems concern different, explicitly stated auxiliary assertions.
