# Pure Rotary Proof Track: Audited Routes

## Scope

This note records proof attempts in the run starting from `bdca97f`. The original target was the reverse implication from pure rotary computability with $H$ heads to unchanged vanilla computability with $H$ heads, for every input length and every Boolean function. The investigation instead produced the rigorous mathematical separation in [Theorem 22](../../theorems/03_rotary_attention/022_pure_rope_three_head_separation.md). Its full lower bound and architectural transfer are now Lean-checked. The score threshold is strictly positive, the query is fixed and attends to itself, and pure values are unrotated and token-only.

The literal standard-frequency and free-frequency architectural bridges are proved in [Theorem 18](../../theorems/03_rotary_attention/018_pure_rope_architectural_bridge.md). Thus the scalar Boolean comparisons transfer to the stated architectures without an unproved interpolation assumption.

## 1. Endpoint reorientation succeeds for two heads

For a nondegenerate pure atom $N/D$, one of the two token endpoints gives

$$ N=tD+\sigma F,\qquad \sigma\in\lbrace-1,1\rbrace, $$

where $F$ is positive on the cube and has strictly positive slopes or strictly negative slopes. The explicit endpoint numerators are

$$ F_0=N-v_0D=(\eta-v_0\gamma)+(v_1-v_0)\sum_i b_i x_i,\qquad F_1=v_1D-N=(v_1\gamma-\eta)+(v_1-v_0)\sum_i a_i(1-x_i). $$

The query-value position relative to the token values determines which of $F_0,-F_0,F_1,-F_1$ is suitable. The full finite case split is `PureRoPEAtom.exists_uniform_endpoint` in `Results/RoPETwoHeads.lean`.

For a second arbitrary positive affine ratio $Q/E$, clearing the two denominators gives

$$ DE\left(c+\frac ND+\frac QE\right)=DM+\sigma FE,\qquad M=Q+(c+t)E. $$

The general two-product compiler takes $P=UZ+FV$ and sets $G=F+\varepsilon Z$. For a sufficiently small nonzero finite $\varepsilon$, both $F$ and $G$ remain admissible. Its score satisfies

$$ \frac{U/\varepsilon}{F}+\frac{V-U/\varepsilon}{G}=\frac{UZ+FV}{FG}. $$

This preserves the entire cleared polynomial and hence its signs. It need not preserve the original real score. No complement-invariance assumption appears. `vanilla_two_of_pure_add_positive_fraction` is stronger than the pure-pure two-head theorem.

Equal input-token values are handled by first decreasing the free threshold constant enough to obtain nonzero scores at every cube point, then perturbing one token value by less than the resulting finite sign margin. The attention mass multiplying that value is between zero and one. `Atoms/RoPEStrictness.lean` proves this uniformly, including arbitrary background scores and arbitrary head counts.

## 2. Pairwise replacement does not give an induction

The positive multiplier introduced by the two-head construction depends on the input. It cannot be discarded when a third score is added. Even the simpler opposite shear identity shows the problem:

$$ \frac a{1+ta}+\frac b{1-tb}=\frac{a+b}{(1+ta)(1-tb)}. $$

At $a=b=1$ and $t=1/2$, the pair changes from $2$ to $8/3$. Adding the unchanged background $-5/2$ changes the total sign from negative to positive. This is checked by `RoPEShearObstruction.pair_replacement_changes_total_sign`.

For a direct first-head substitution in an $H$-head cleared polynomial, the remaining numerator after extracting the positive endpoint is generally degree $H-1$. The two-product compiler needs that factor to be affine. For $H=2$ it is affine automatically; for larger $H$ this is an actual missing construction, not a bookkeeping issue.

## 3. Independent output shears lose the cancellation

Apply $a\mapsto a/(1+ta)$, $b\mapsto b/(1+ub)$, and $c\mapsto c/(1+vc)$. The cleared numerator is

$$ a+b+c+(t+u)ab+(t+v)ac+(u+v)bc+(tu+tv+uv)abc. $$

Preserving the original additive numerator identically forces all three pairwise sums to vanish, hence $t=u=v=0$. The analogous pairwise condition at every head count at least three also forces every shear to vanish. These are `independent_three_shears_trivial` and `pairwise_shear_cancellation_trivial` in `Atoms/RoPEShearObstruction.lean`.

These statements rule out a universal coefficient-preserving substitution. They do not rule out alternative sign representatives on a finite Boolean cube.

## 4. A common projective input shift cannot always orient denominators

In centered coordinates, a common projective substitution translates normalized denominator directions by one vector. Two directions $(r,0)$ and $(-r,0)$ become $(a+r,b)$ and $(a-r,b)$. For $r\geq1/2$, positivity on the cube and uniform slope signs cannot hold for both translated denominators. Opposite orientations require contradictory signs for $b$; equal orientations violate positivity at a corner.

`Atoms/RoPEProjectiveObstruction.lean` proves `no_common_oriented_shift` and `shifted_pair_not_admissible`, and supplies genuine nondegenerate pure atoms with directions $(3/4,0)$ and $(-3/4,0)$. This failure already occurs in a regime where Boolean two-head equivalence is proved, so it is only a limitation of the proposed transformation.

## 5. Univariate and collinear families do preserve every head count

A polynomial of degree at most $H$ in an arbitrary affine statistic has an $H$-head vanilla sign realization. The statistic may have mixed or zero coefficients. A small projective perturbation preserves finite strict signs, and proper partial fractions provide uniformly oriented denominators.

More generally, arbitrary affine numerators with positive denominators whose slope vectors are collinear admit the same head count. Clearing denominators gives a sum of affine functions times univariate polynomials of degree below $H$. One common family of partial-fraction poles realizes all terms simultaneously with $H$ heads.

The full statements are `AffineStatistic.computable_of_polynomial`, `AffineStatistic.computable_of_affine_polynomial_sum`, and `AffineStatistic.computable_of_collinear_denominators`. They are proved in `Results/AffineStatisticUpperBound.lean` and `Results/CollinearDenominatorUpperBound.lean`, with pure and retained specializations. The unrestricted problem allows independent denominator directions, so this reduction does not apply automatically.

The stronger `AffineStatistic.computable_of_denominator_plane` handles denominators in the span of two affine forms, provided that span contains a positive form $B$ with strictly uniform slopes. Set $y=T/B$ and use proper partial fractions with denominators $T+a_hB$. Large positive poles make every denominator positive with the orientation of $B$. This construction preserves the signs exactly and needs no limiting argument. It is formalized in `Results/DenominatorPlaneUpperBound.lean`.

## 6. Finite differences give a general bound, with extra heads

For arbitrary positive affine denominators, inclusion-exclusion over nonempty subsets yields $2^H-1$ admissible vanilla ratios. The alternating moments vanish through order $H-2$, and the first surviving coefficient is $(H-1)!$ times the original cleared numerator. An exact geometric-series remainder and a finite strict margin justify a finite parameter choice.

The complete proof, including $H=0$ and $n=0$, is in [Theorem 19](../../theorems/03_rotary_attention/019_finite_difference_vanilla_simulation.md) and `FiniteDifference.computable_of_positive_denominators`. No special pure constraint is needed for that bound. The pure endpoint permits deleting one additional subset term after a small numerator perturbation, improving the bound to $2^H-2$ for $H\geq2$. This is `pureRoPEComputable_vanilla_improved_exponential_bound` in `Results/PureFiniteDifference.lean`. Three pure heads therefore need at most six vanilla heads. Reciprocal numerators permit the further bounds described in Theorem 19.

## 7. Three-head complement averaging leaves an odd-part problem

Write a centered three-head cleared cubic as $P=Q+O$, with $Q$ even and $O$ odd. If the classifier is complement-invariant and the scores are strict, then

$$ |O(z)|\lt|Q(z)| $$

at every cube point, and the even quadratic $Q$ has the correct signs. Its quadratic part can be grouped into three products of linear forms. This gives a useful lower-degree representative, but does not by itself give three admissible heads.

`Atoms/RoPEThreeEven.lean` checks the antipodal expansion, the strict domination equivalence, and the relevant pencil identities. The two-head inverse-pencil self-pairing is identically zero. The corresponding three-head expression is $Tt^2-2t$, which is generally nonzero.

Finding a positive isotropic direction for the even quadratic alone is insufficient: a new three-head representation may introduce an odd part that violates the strict domination inequality. Scaling denominator directions to zero can make an uncancelled linear odd term diverge. No three-head equivalence follows from this argument as it stands.

A four-head bound does follow and is fully formalized in `Results/RoPEThreeComplement.lean`. The generic compiler `CubeAffine.computable_of_strict_product_sum` realizes a strict score $c+\sum_{j=1}^m A_jB_j$ using $m+1$ vanilla heads. Applied to the three-product even quadratic, it gives `vanilla_four_of_pureRoPE_three_complement`, and also the stronger retained-atom version. [Theorem 21](../../theorems/03_rotary_attention/021_three_heads_complement_invariant.md) gives the full argument.

## 8. Uniform real-score approximation is too strong

The pure atom with score

$$ g(x)=\frac1{5+x_0+x_1-x_2} $$

cannot be uniformly approximated by one vanilla score with error less than $1/100000$, even with a free readout constant and unrestricted finite width. `Examples/RoPEApproximation.lean` proves this quantitative gap by clearing denominators at seven vertices and using the uniform slope-sign constraint. The main architectural declaration is `mixedReciprocal_no_close_vanilla_one_head_score`.

Every Boolean threshold of this same score is still a linear threshold function and therefore needs at most one vanilla head. Thus a proof by arbitrarily accurate headwise score approximation would demand a false statement, while one-head Boolean equivalence holds. The later three-head separation uses a different argument.

## 9. Exponential token-value tilting does not preserve score order

Tilting attention weights by the exponential of their token values eventually orients the input denominator slopes when the token values differ. Each individual tilted mean is monotone in the tilt parameter, because its derivative is a variance. This does not preserve the ordering of different inputs.

A one-bit example has input weights $a=b=1$, query weight $10$, and values $0,1,2$ for zero, one, and query. Its scores are $20/11$ and $21/11$. Multiplying each weight by $10$ raised to its value changes the scores to $2000/1001$ and $201/101$, in the opposite order. Consequently a global threshold adjustment alone cannot preserve this particular ordering throughout the tilt. This is not a Boolean lower bound, and it does not exclude changing the readout orientation or the whole representation.

## 10. Distinct-group cubic tensors turn the grid route into a separation

Generic exact polynomial rigidity alone cannot separate finite Boolean sign classes: another cubic can share the labels, and Boolean vanishing polynomials change the representation. Initial grid arguments also failed because averaging need not preserve a full numerator-denominator product structure, and unbounded numerator cancellations invalidate parameter-normalized limits.

The successful refinement retains only cubic coefficients using one group from each of three disjoint blocks. These coefficients preserve the product structure exactly under replica averaging. Normalize the averaged polynomial itself, use dense-grid signs and irreducibility to identify its nonzero limit, then apply a closed tensor-rank obstruction. No bound on numerator parameters is required.

For the source cubic $u_1d_2d_3+u_2d_1d_3+u_3d_1d_2$, the contraction matrix has rank at most three exactly on the denominator kernel. Its three decisive four-by-four minors are $d_i^4$. Any vanilla tensor has a three-dimensional subspace of such low-rank contractions, together with an orthogonal same-signed denominator vector. Compactness forces the limiting vector into a zero-sum denominator row space, contradicting its simplex normalization.

[Theorem 22](../../theorems/03_rotary_attention/022_pure_rope_three_head_separation.md) gives the full mathematical proof and explicit genuine pure masses. It proves pure minimum three and vanilla minimum between four and six for all sufficiently large members of an explicit family on $18m$ bits. The first such $m$ remains unknown. Its full compactness and divisibility lower bound is proved in `Results/PureThreeSeparation.lean`, including the exact vanilla-to-averaged-polynomial bridge. [The independent audit](research/separation_audit.md) records the checks of sign equivalence, averaging, degeneracies, and architectural scope.

The route was also made quantitative. [An explicit tensor gap](research/quantitative_tensor_gap.md), together with rational graph interpolation and an integer-minor conditioning bound, gives the sufficient replication threshold $m\geq10^{40000}$ in [the effective-bound note](research/effective_replication_threshold.md). These numerical constants have independent mathematical audits. The Lean proof establishes the existential threshold and a positive tensor gap without specifying these constants.

## 11. Exact certificates support finite examples only

`search/search_many_head.py` explores three-head pure classifiers and different vanilla denominator choices, including initializations from the proved endpoint forms. Successful fits are rationalized and checked on the entire cube using Python integer arithmetic. The independent verifier checks positivity, uniform nonzero denominator slope signs, and every cleared sign in both models.

Numerical optimization failures remain unresolved instances. They are not lower bounds, and some failures disappear with different initializations. A finite list of successful certificates does not prove universal equality. The new collection contains 353 integer-verified three-head fits. An exact positive dual witness excludes the three fixed endpoint denominators for one sample, with arbitrary affine numerators, but does not exclude other denominator choices. [The search report](search/three_head_search.md) states these scopes and reproduction commands.


## 12. Matrix and exact cubic transformations have limited scope

The arrowhead matrix representation converts a fraction sum into a Schur-complement sign. Positive leaf denominators permit completing squares, but generic elimination creates rational rather than affine pivots. The checked coordinate-separated congruence restriction forces a monomial leaf transformation and preserves denominator directions. `Atoms/RoPEArrowhead.lean` and [the matrix note](research/matrix_route.md) give the exact scope.

The cubic-pencil route attempts to place two new denominators in a pencil through a chosen oriented form. `Atoms/CubicPencilObstruction.lean` supplies a cubic for which this exact polynomial representation is impossible. This only excludes that prescribed exact representation; Theorem 22 is needed to obtain a Boolean lower bound against arbitrary representations.

## 13. Product differences and value tilts

Every strict finite sum of positive-denominator fractions has a sign-equivalent difference of two positive affine products at a sufficiently small finite perturbation. `exists_positive_product_difference` and `CubeAffine.classifier_as_product_difference` in `Results/ProductDifferenceSign.lean` prove this using the derivative of the product and a common strict margin. This gives an alternative sign representation without yet giving oriented denominators.

Increasing the perturbation until all factor slopes become uniform need not preserve the labels. `Atoms/RoPETiltObstruction.lean` proves an explicit two-bit failure of that proposed continuation. The target in that example still has a one-head vanilla classifier. [The value-tilt note](research/value_tilt_route.md) separates these statements carefully.

## 14. Boolean zero families and tangent representations

A nontrivial vanilla score can vanish identically on the Boolean cube while its cleared polynomial is a nonzero multiple of a Boolean vanishing relation. Perturbing such a family yields additional same-head sign constructions. `CubeAffine.computable_of_zero_family_tangent` in `Results/BooleanTangentUpperBound.lean` proves the generic finite-margin compiler.

A three-head family with denominators $F$, $F+a x_1$, and $F+a(1-x_1)$ and numerators $-1$, $1-x_1$, and $x_1$ is identically zero on Boolean inputs. Its cleared polynomial is $a(2F+a)(x_1^2-x_1)$. Jacobian exploration suggested useful subclasses, but did not prove general three-head coverage. No Jacobian rank or suggested subclass is used as an unproved universal premise.

## 15. General contraction ranks separate every larger head budget

The cubic rank obstruction extends to every $H\geq3$. For $W_H=\sum_iN_i\prod_{j\neq i}D_j$, a nonzero denominator direction forces contraction flattening rank at least $2H-2$. The kernel proof uses the pair equations $d_ke_l+d_le_k=0$ twice, first on the denominator projection and then on its numerator fiber. Each has dimension at most one. A zero denominator direction has rank at most $H$.

This uniform rank characterization gives the paired denominator kernel, whose dimension is $H$ and which contains the all-ones vector. The compact frame and simplex-normal contradiction now works in every dimension. The polynomial source is irreducible and has a regular real zero patch, so sign rigidity and Boolean replica averaging supply the same limit argument. [Theorem 23](../../theorems/03_rotary_attention/023_pure_rope_separation_every_head_count.md) gives the complete independently audited mathematical proof. It separates every head budget above two. Its complete arbitrary-head formalization is in `Results/PureGeneralSeparation.lean`, with no remaining obstruction premise. `Results/RoPEUniversalBudgets.lean` classifies the universal head-preserving implication exactly: it holds if and only if the budget is at most two.

## 16. Small replications have exact alternative representations

For the three-head family, the first replication is a linear threshold function and has head minimum one. The second replication has threshold degree and head minimum three in all models. A sharper covariance estimate proves the third replication has minimum one again; the exact minima are therefore not monotone in the replication count. The quadratic lower bound uses positive inputs whose sum is zero and whose complements are negative. Averaging the two strict inequalities cancels the even terms of a hypothetical quadratic, leaving an impossible separating linear form.

The second-replication vanilla upper bound replaces each denominator $D_i$ by $D_i+L$, where $L$ is the common linear statistic. The new slopes are strictly positive. At $L=0$ the score is unchanged; away from zero, an explicit error estimate preserves its sign. Both statements are Lean-checked. Failed numerical fits at this replication were therefore limitations of the optimization, not impossibility evidence. [The small-replication note](research/small_replication_exact_complexity.md) records the exact constructions.

## 17. Exact finite-factor and regular jet obstructions

The [finite-factor residue argument](research/exact_finite_factor_obstruction.md) excludes every exact oriented affine-fraction representation of the three-head source boundary on the entire continuous cube. Every oriented hyperplane section retains an irreducible factor of degree at least two. Reducing a proposed polynomial identity modulo each denominator forces all those factors into a multiplier of insufficient degree. This does not exclude finite Boolean representations, nor their degenerate limits: denominator collisions and replica averaging prevent transferring that exact identity obstruction directly.

A different [common-base jet argument](research/subset_and_jet_limits.md) excludes five-head regular second-order cubic moment constructions for a selected source section. `CommonBaseJetObstruction.no_five_head_endpoint_moments` is Lean-checked. It is restricted to that moment scheme and does not prove a six-head Boolean lower bound.
