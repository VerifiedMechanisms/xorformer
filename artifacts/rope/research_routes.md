# Pure Rotary Proof Track: Audited Routes

## Scope

This note records proof attempts in the run starting from `bdca97f`. The target is the reverse implication from pure rotary computability with $H$ heads to unchanged vanilla computability with $H$ heads, for every input length and every Boolean function. Universal equality is not claimed here. The score threshold is strictly positive, the query is fixed and attends to itself, and pure values are unrotated and token-only.

The literal standard-frequency and free-frequency architectural bridges are proved in [Theorem 18](../../theorems/03_rotary_attention/018_pure_rope_architectural_bridge.md). Thus the remaining issue is the Boolean sign class of the scalar atoms, rather than an unproved interpolation assumption.

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

## 6. Finite differences give a general bound, with extra heads

For arbitrary positive affine denominators, inclusion-exclusion over nonempty subsets yields $2^H-1$ admissible vanilla ratios. The alternating moments vanish through order $H-2$, and the first surviving coefficient is $(H-1)!$ times the original cleared numerator. An exact geometric-series remainder and a finite strict margin justify a finite parameter choice.

The complete proof, including $H=0$ and $n=0$, is in [Theorem 19](../../theorems/03_rotary_attention/019_finite_difference_vanilla_simulation.md) and `FiniteDifference.computable_of_positive_denominators`. No special pure constraint is needed. Compressing this subset expansion to $H$ terms has not been established.

## 7. Three-head complement averaging leaves an odd-part problem

Write a centered three-head cleared cubic as $P=Q+O$, with $Q$ even and $O$ odd. If the classifier is complement-invariant and the scores are strict, then

$$ |O(z)|\lt|Q(z)| $$

at every cube point, and the even quadratic $Q$ has the correct signs. Its quadratic part can be grouped into three products of linear forms. This gives a useful lower-degree representative, but does not by itself give three admissible heads.

`Atoms/RoPEThreeEven.lean` checks the antipodal expansion, the strict domination equivalence, and the relevant pencil identities. The two-head inverse-pencil self-pairing is identically zero. The corresponding three-head expression is $Tt^2-2t$, which is generally nonzero.

Finding a positive isotropic direction for the even quadratic alone is insufficient: a new three-head representation may introduce an odd part that violates the strict domination inequality. Scaling denominator directions to zero can make an uncancelled linear odd term diverge. No three-head equivalence follows from this argument as it stands.

## 8. Uniform real-score approximation is too strong

The pure atom with score

$$ g(x)=\frac1{5+x_0+x_1-x_2} $$

cannot be uniformly approximated by one vanilla score with error less than $1/100000$, even with a free readout constant and unrestricted finite width. `Examples/RoPEApproximation.lean` proves this quantitative gap by clearing denominators at seven vertices and using the uniform slope-sign constraint. The main architectural declaration is `mixedReciprocal_no_close_vanilla_one_head_score`.

Every Boolean threshold of this same score is still a linear threshold function and therefore needs at most one vanilla head. Thus a proof by arbitrarily accurate headwise score approximation would demand a false statement, while the requested Boolean implication remains possible.

## 9. Exponential token-value tilting does not preserve score order

Tilting attention weights by the exponential of their token values eventually orients the input denominator slopes when the token values differ. Each individual tilted mean is monotone in the tilt parameter, because its derivative is a variance. This does not preserve the ordering of different inputs.

A one-bit example has input weights $a=b=1$, query weight $10$, and values $0,1,2$ for zero, one, and query. Its scores are $20/11$ and $21/11$. Multiplying each weight by $10$ raised to its value changes the scores to $2000/1001$ and $201/101$, in the opposite order. Consequently a global threshold adjustment alone cannot preserve this particular ordering throughout the tilt. This is not a Boolean lower bound, and it does not exclude changing the readout orientation or the whole representation.

## 10. Generic cubic rigidity does not directly transfer to Boolean signs

The three-head polynomial $u_1d_2d_3+d_1u_2d_3+d_1d_2u_3$ suggests studying whether its denominator factors are identifiable from its singular locus. Even an exact polynomial rigidity theorem would not establish a Boolean separation: another cubic can have the same finite signs, and adding multiples of $x_i^2-x_i$ changes the polynomial without changing its cube values.

A proposed dense-grid argument replicates input coordinates and takes a limit. Several gaps remain. A vanilla model can assign different coefficients to different copies; averaging the cleared polynomial preserves signs but need not preserve its product structure. Heavy denominator coordinates obstruct a direct concentration argument. Finally, cancellations between heads can shrink the cleared polynomial faster than the multilinearization error, invalidating a normalized limit argument. No rigidity or grid argument is used here as a proved head-count lower bound.

The related cubic-completion route seeks a different product representation after adding Boolean vanishing polynomials. No general oriented completion with the original head count has been established.

## 11. Exact certificates support finite examples only

`search/search_many_head.py` explores three-head pure classifiers and different vanilla denominator choices, including initializations from the proved endpoint forms. Successful fits are rationalized and checked on the entire cube using Python integer arithmetic. The independent verifier checks positivity, uniform nonzero denominator slope signs, and every cleared sign in both models.

Numerical optimization failures remain unresolved instances. They are not lower bounds, and some failures disappear with different initializations. A finite list of successful certificates does not prove the universal equality.
