# Two rational heads require many deterministic priority pieces

## The proposed compiler and its first failing lemma

A finite collection of denominator boundary charts would give a strong count if every narrow score could be replaced, with constant head overhead, by deterministic priority pieces with affine terminal values. The following example rules out that particular compiler, even though it has a polynomial relative margin already.

A priority piece tests distinct coordinates in a fixed order. A successful test returns a prescribed real constant. If every test fails, the piece returns an arbitrary affine function of the remaining coordinates. We allow either literal in every test, a larger class than the uniform orientations available to individual head boundary charts.

**Restriction lemma.** A sum of $K$ priority pieces, plus a bias, has a restriction fixing at most $K$ coordinates on which its score is affine.

**Proof.** If any piece still has an unresolved test, choose its first unresolved coordinate and fix it so the test succeeds. All earlier tests of that piece have already failed, so this makes the piece constant. Every other piece remains a priority piece, an affine function, or a constant after restriction. At least one unresolved piece disappears at each step. After at most $K$ steps all pieces are affine or constant. Coordinates already fixed are skipped, so no contradictory assignment is introduced. $\blacksquare$

## A two-head family

Let $r$ be odd, $n=2r$, and split the variables into two blocks. Write $u,v$ for their Hamming weights and put

$$ U=2u-r,\qquad V=2v-r,\qquad M=r+1,\qquad R=r(r+2),\qquad K=R+1. $$

Define the strictly positive-slope affine forms

$$ L_1=MU+V,\qquad L_2=U+MV. $$

Since $U,V$ are nonzero odd integers in $[-r,r]$, the signs of $L_1,L_2$ are respectively the signs of $U,V$. Moreover $1\leq|L_i|\leq R$. The two-head score is

$$ S=L_1-\frac{K L_1}{K+L_2}=\frac{L_1L_2}{K+L_2}. $$

Here $K+L_2$ has constant coefficient one and strictly positive slopes. The first term is an admissible constant-denominator head because all its numerator slopes are positive. The second term is an admissible positive-affine-denominator head with an arbitrary affine numerator. This checks the original model's special restriction on constant denominators; arbitrary affine numerators over a constant denominator are not being assumed.

The score is positive exactly when the two block majorities agree. Both heads are bounded on the full cube by $R$ and $KR$, respectively, and the signed score is at least $1/(2R+1)$. Its relative margin therefore satisfies

$$ \gamma\geq\frac{1}{R(R+2)(2R+1)}. $$

Thus this is a well-conditioned family, not a counterexample to the desired margin repair.

## Lower bound for the proposed compiled class

Fix at most $(r-1)/2$ coordinates, anywhere in the two blocks. Each block majority can still take both signs: the unfixed coordinates can be set all zero or all one to obtain the two outcomes. Choose these two assignments in each block. On the resulting rectangle the agreement labels alternate.

An affine score on the remaining coordinates has equal sums on the two diagonals of that rectangle. Strict representation of alternating agreement labels would make one diagonal sum positive and the other negative, a contradiction. The original positive-true, weak-negative-false convention also gives a contradiction: the positive diagonal sum is strictly positive and the other is nonpositive.

Consequently every restriction fixing at most $(r-1)/2$ coordinates remains non-linearly-separable. The restriction lemma implies that any sum of deterministic priority pieces with affine terminal values representing this table needs at least $(r+1)/2$ pieces. This is a linear-in-dimension overhead for a family already represented by two genuine heads.

## Verification boundary and consequence

`formalization/HeadComplexity/Research/TwoHeadAffineProduct.lean` kernel-checks the general positive-affine constant-denominator constructor, the exact two-head product identity, and the original-model `fracComputable` consequence. The declarations are `HeadComplexity.TwoHeadAffineProduct.positiveAffineAtom_eval`, `productAtoms_score`, and `product_fracComputable`.

The majority-block family, its explicit relative margin, and the restriction argument for priority pieces are written proofs. They are not claimed as Lean declarations. `verify_priority_vertex_family.py` separately checks the score identity, signs, and margin bound exactly for several odd block sizes, by their Hamming-weight classes.

This rules out replacing each head by constantly many deterministic priority pieces while preserving an arbitrary sum's truth table. It does not rule out grouped boundary charts with several active coefficients, a compiler with additive polynomial width, or the requested critical-width margin repair.
