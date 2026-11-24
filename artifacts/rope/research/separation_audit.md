# Audit of the Replicated Three-Head Separation

The complete mathematical argument is [Theorem 22](../../../theorems/03_rotary_attention/022_pure_rope_three_head_separation.md). Three independent reviews checked the full argument after the construction was found. This note records the main points where an apparently similar argument could fail and why this proof avoids those failures. The full theorem is not claimed as a Lean declaration.

## The source is genuinely pure

For each replica group, the source uses positive masses and the same two input-token values. With the integer-scaled forms in the theorem, the coefficient sums are $\sum u_h=42$ and $\sum d_h=0$. Therefore the parameters $\gamma=116$ and $\eta=-42$ give exactly $N_h=u_h(q)$ and $D_h=200+d_h(q)$. The denominators lie between $194$ and $206$ on the entire continuous cube. The query value is $-42/116$, which is permitted by the original model.

The construction does not use position-dependent values. The literal pure rotary bridge realizes its positive attention masses for both the fixed standard frequency schedule and freely chosen frequencies, at finite width. The original vanilla normal form supplies all necessary restrictions on a hypothetical vanilla representation.

## Boolean signs, not exact scores

A hypothetical vanilla representation need only match the labels at the finite Boolean inputs. Its score can be completely different from the source score. A finite downward threshold shift makes all its scores strict while preserving every label, including negative labels that originally had zero score. Clearing positive denominators produces a cubic with the same strict signs.

The proof takes a different hypothetical representation for every replication count. It does not assume that the parameters, widths, numerators, or denominator directions vary continuously with that count.

## Averaging preserves only the coefficients actually used

Boolean multilinearization and averaging need not preserve a cubic's full factorization. The proof does not require that. It retains only cubic monomials with one group from each of three disjoint blocks. Such monomials use three distinct replica variables, so Boolean reductions cannot affect their coefficients. Averaging and summing their coefficients gives products of the aggregated slopes exactly.

Repeated-group monomials can acquire lower-degree correction terms. Those terms are included in the averaged polynomial used for sign convergence, and cannot contribute to the selected cross-block cubic tensor.

## The normalization survives cancellations

Only the averaged polynomial coefficient vector is normalized. No head parameter is normalized or assumed bounded. Even arbitrarily large numerator coefficients and arbitrarily severe cancellations leave the selected tensor's rank condition intact, because multiplying a tensor by a nonzero scalar preserves that condition.

The maximum coefficient norm is one after normalization. A convergent subsequence therefore has a nonzero polynomial limit of degree at most three. This avoids the invalid inference that a nonzero score must have a nonzero limit under some independently chosen denominator normalization.

## Sign agreement forces divisibility here

The grids become dense. At every point where the source polynomial is nonzero, moving grid points eventually have its same sign. Coefficient convergence gives weak sign agreement of the limiting polynomial. On the smooth zero hypersurface near the origin, both source signs occur arbitrarily nearby, so the limiting polynomial vanishes.

The source polynomial is irreducible for a specific reason: in six independent affine coordinates it is linear and primitive in the third numerator coordinate. Solving for that coordinate on the real zero patch and clearing denominators gives an identically zero polynomial in the remaining seventeen coordinates. Gauss's lemma then yields divisibility. Both polynomials have degree at most three, so the nonzero limit is a positive scalar multiple of the source.

A generic claim that identical finite signs imply identical polynomials would be false. The dense-grid limit, smooth sign-changing patch, irreducibility, and degree bound are all essential here.

## Degenerate denominators do not escape the obstruction

A vanilla denominator has either all strictly positive slopes, all strictly negative slopes, or all zero slopes. If any is nonconstant, its aggregate in every six-group block is nonzero and has a uniform strict sign. It can be sign-normalized to a vector in the compact probability simplex.

The common kernel of the three aggregated denominator forms has dimension at least three even when the forms are dependent. The proof chooses an orthonormal triple inside this kernel. Thus it never assumes a nonsingular denominator matrix. A nonzero limiting cubic tensor guarantees that some denominator is nonconstant along the eventual subsequence.

## The final contradiction is closed under limits

The relevant four-by-four determinants of the source contraction are fourth powers of its denominator coordinates. Hence a source contraction has rank at most three exactly on the three-dimensional denominator kernel. Rank at most three is expressed by vanishing minors, so it passes to limits.

The limiting orthonormal triple lies in that kernel and spans it. The limiting normalized nonnegative denominator vector is orthogonal to this triple. The source kernel contains the all-ones vector, forcing the normalized vector's coordinate sum to be zero. Its coordinate sum is also one. This is the contradiction.

The argument establishes eventual separation, hence a finite Boolean counterexample exists. It does not supply an effective bound for the first replication count, and it does not infer any lower bound from numerical search failures.
