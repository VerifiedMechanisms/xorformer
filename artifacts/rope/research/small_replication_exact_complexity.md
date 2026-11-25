# Small Replication Counts: Exact Minima and Degree Certificates

The source family from [Theorem 22](../../../theorems/03_rotary_attention/022_pure_rope_three_head_separation.md) does not separate the architectures at its first eight replication counts. The first three minima are one, three, and one in both models. In particular, the minimum need not increase with the replication count. The arguments below also explain why numerical fitting failures at small replication counts cannot establish separation.

| Replication count | Common minimum head count | Threshold degree |
| --- | --- | --- |
| 1 | 1 | 1 |
| 2 | 3 | 3 |
| 3 | 1 | 1 |
| 4 | 3 | 3 |
| 5 | Either 2 or 3, unresolved | 2 |
| 6 | 3 | 3 |
| 7 | 3 | 3 |
| 8 | 3 | 3 |

The finite vanilla upper certificates for replications four through eight and the quadratic upper certificate for replication five are exhaustive integer computations. The lower bounds, pure rotary realizations, and complete results at replications one through three are Lean-checked.

## The first replication is a weighted majority

Write $A_i$ and $B_i$ for the sums of the first and last coordinate of type $i$ across the three blocks, respectively. Put

$$ T=\sum_i(A_i+B_i),\qquad L=4\sum_iA_i+3\sum_iB_i,\qquad N_i=2(T+A_i),\qquad D_i=200+A_i-B_i. $$

Then $\sum_iN_i=2L$, $|A_i|\leq3$, and $194\leq D_i\leq206$. Since $3T=L-\sum_iA_i$, the numerator absolute sum satisfies

$$ \sum_i|N_i|\leq6|T|+18\leq2|L|+36. $$

Consequently the source score $S=\sum_iN_i/D_i$ obeys

$$ \left|S-\frac L{100}\right|\leq\frac{6(2|L|+36)}{200\cdot194}. $$

Whenever $|L|\geq1$, the right side is strictly smaller than $|L|/100$, so $S$ and $L$ have the same strict sign. At replication one, all eighteen centered coordinates are signs and the sum of the linear weights is $63$. Thus $L$ is an odd integer and never vanishes. The classifier is exactly the weighted majority with weight four on each first-half coordinate and weight three on each second-half coordinate. Both corner labels occur, so its minimum head count is one.

These claims are Lean-checked in [`PureSourceLinearApproximation.lean`](../../../formalization/HeadComplexity/Results/PureSourceLinearApproximation.lean), including `score_linear_error`, `classifier_one_isLTF`, and `classifier_one_head_minima`.

## A quadratic obstruction at replication two

At replication two, each $A_i$ and $B_i$ can independently take any integer value from $-3$ to $3$. Consider the following three count vectors, with the semicolon separating the $A$ and $B$ triples:

$$ v_1=(-2,1,1;-2,0,2),\qquad v_2=(1,-2,1;2,-2,0),\qquad v_3=(1,1,-2;0,2,-2). $$

They sum to zero. All have $L=0$, and the cleared source polynomial takes value four on each of them and value negative four on each negative vector. Thus the source labels are positive at $v_i$ and negative at $-v_i$.

For any polynomial $Q$ of degree at most two, the difference $Q(v)-Q(-v)$ is linear in $v$. Therefore

$$ \sum_{i=1}^{3}\bigl(Q(v_i)-Q(-v_i)\bigr)=0. $$

This contradicts a quadratic sign representation of the six-count classifier, since every summand would be strictly positive.

The same obstruction applies to a polynomial in the original 36 Boolean variables, without assuming it depends only on the six counts. For each count vector, take all six cyclic shifts of a fixed Boolean realization within each of the six coordinate types, using the same shift in every type. This gives eighteen positive Boolean inputs. Each coordinate is true in exactly nine of these inputs, because the three count vectors sum to zero. Their complements are all negative. The constant and quadratic even parts cancel between each input and its complement, and the linear parts cancel because the eighteen inputs are balanced in every coordinate. Hence the sums of every degree-at-most-two polynomial over the positive inputs and their complements agree, which is incompatible with the required signs.

The generic balanced-complement moment identity is implemented in [`QuadraticMomentCertificate.lean`](../../../formalization/HeadComplexity/Polynomial/QuadraticMomentCertificate.lean). The eighteen explicit inputs and their exact source scores are implemented in [`PureSecondReplicationDegree.lean`](../../../formalization/HeadComplexity/Results/PureSecondReplicationDegree.lean). The source scores at the positive inputs are $1/1999950$; their complementary scores are $-1/1999950$. This proves threshold degree three and pure minimum three.

## An exact vanilla representation with three heads

Replace each denominator by

$$ E_i=D_i+L=200+A_i-B_i+L. $$

Its coefficient in every centered input coordinate is strictly positive, because the weights four and three of $L$ dominate the added coefficient $1$, $-1$, or $0$. It remains positive throughout the continuous cube. The affine-fraction normal form therefore realizes each $N_i/E_i$ as one vanilla head.

If $L=0$, the new score equals the source score exactly. Otherwise, at replication two, $L$ is a nonzero integer. Write $B=200+L$. Since $|L|\leq63$, one has $B\geq137$ and

$$ \left|\sum_i\frac{N_i}{B+A_i-B_i}-\frac{2L}{B}\right|\leq\frac{6(2|L|+36)}{B(B-6)}\lt\frac{2|L|}{B}. $$

The last inequality follows from $|L|\geq1$ and $|L|(B-12)\geq125\gt108$. Thus the new score and the source score both have the sign of $L$ away from the zero hyperplane, and agree exactly on it. This gives three vanilla heads. Together with the quadratic lower bound, all pure, standard-frequency rotary, free-frequency rotary, and vanilla minima equal three on this 36-bit classifier.

The upper construction is Lean-checked in [`PureSourceTwoReplicasUpper.lean`](../../../formalization/HeadComplexity/Results/PureSourceTwoReplicasUpper.lean). It is an exact classifier proof; no optimizer output is used as a certificate.

## Exact upper certificates through replication eight

A smaller shift of the opposite sign extends the three-head upper certificate. Use

$$ E_i=D_i-\frac{13}{50}L. $$

Every denominator slope is strictly negative. In the first half of each block, its coefficients are $-1/25$ at coordinate $i$ and $-26/25$ at the other coordinates. In the second half, they are $-89/50$ at coordinate $i$ and $-39/50$ elsewhere. The denominator is at least $200-63(13/50)=9181/50\gt0$ on the entire continuous cube. Each affine numerator over this denominator therefore has a one-head vanilla realization.

The remaining sign comparison was checked exhaustively with integer arithmetic for every replication count from one through eight. For a fixed $m$, the classifier depends only on six independent counts, each ranging from zero to $3m$. Thus the check covers exactly $(3m+1)^6$ patterns and every Boolean input. All eight comparisons have zero disagreements, including the $244140625$ patterns at replication eight.

The concrete integer numerator and denominator rows, all pattern counts, and the exact verifier are recorded in [`replicated_family_m1_to_m8_common_shift.exact.json`](../search/replicated_family_m1_to_m8_common_shift.exact.json) and [`search_common_shift.py`](../search/search_common_shift.py). The verifier bounds every integer intermediate below the signed 64-bit limit before using integer arrays. These finite upper certificates are exhaustive arithmetic computations, not additional Lean theorems.

The replication-two classifier is a restriction of every even-replication classifier, obtained by copying each original coordinate equally many times. Threshold degree cannot increase under a coordinate-identification restriction. Therefore every positive even replication has threshold degree and pure minimum exactly three. This lower bound is Lean-checked in [`PureReplicationDivisibility.lean`](../../../formalization/HeadComplexity/Results/PureReplicationDivisibility.lean). Together with the exhaustive upper certificates, all four head minima equal three at replications four, six, and eight as well.

An independent verification directly evaluated the recorded affine rows, multiplied their three positive denominators, and compared the resulting strict signs to the source on all $427292180$ patterns across the eight replication counts. This check does not use the common-shift expansion. Reproduce it with:

```bash
heavy python3 artifacts/rope/search/search_common_shift.py --verify-affine artifacts/rope/search/replicated_family_m1_to_m8_common_shift.exact.json
```

## Every admissible common shift fails at replication nine

The common-shift construction itself eventually fails. This is a limitation of the proposed denominators, not a lower bound for arbitrary three-head vanilla representations.

For the general shift $E_i=D_i+tL$, uniform strict denominator slopes and positivity throughout the cube require exactly

$$ -\frac{200}{63}\lt t\lt-\frac14\qquad\text{or}\qquad\frac13\lt t\lt\frac{200}{63}. $$

At replication nine, consider the two realizable six-count aggregate vectors

$$ (A;B)=\frac19(-27,-17,27;11,7,5),\qquad (A';B')=\frac19(-27,7,21;19,-27,7). $$

Both have $L=1/9$. After clearing their positive shifted denominators and removing the common positive scaling, the respective score numerators are

$$ P_+(t)=-40+3544t+2t^2,\qquad P_-(t)=392+3656t+2t^2. $$

The first source label is false because $P_+(0)\lt0$, but $P_+(t)\gt0$ throughout the positive admissible interval. The second source label is true because $P_-(0)\gt0$, but $P_-(t)\lt0$ throughout the negative admissible interval. Hence every admissible common shift disagrees with the source on one of these two Boolean inputs.

This obstruction, including realizability by actual 162-bit inputs and both exact score identities, is Lean-checked in [`PureCommonShiftObstruction.lean`](../../../formalization/HeadComplexity/Results/PureCommonShiftObstruction.lean), theorem `common_shift_nine_disagrees`. It excludes only this one-parameter construction. It does not assert that replication nine separates the architectures or is the first separating replication count.

## The third replication is again a weighted majority

A sharper covariance estimate proves that the source has the sign of $L$ whenever $|L|\geq1/3$. Define

$$ B=\frac{2L}{3}\sum_i\frac1{D_i}. $$

The exact identity is

$$ S-B=\frac23\sum_{i\lt j}(A_i-A_j)\left(\frac1{D_i}-\frac1{D_j}\right). $$

Three real numbers in $[-3,3]$ have total pairwise distance at most twelve. Also $|D_i-D_j|\leq12$, so each reciprocal difference is at most $12/194^2$. Therefore

$$ |S-B|\leq\frac{96}{194^2},\qquad |B|\geq\frac{2|L|}{206}. $$

If $|L|\geq1/3$, then $|B|\geq1/309\gt96/194^2$. The scores $S$, $B$, and $L$ thus have the same strict sign. At replication three, the weighted count $K$ of true bits, with weights four and three, satisfies

$$ L=\frac{2K-189}{3},\qquad |L|\geq\frac13. $$

The classifier is exactly the nonconstant threshold $K\geq95$. All four model minima equal one. The continuous estimate and the exact Boolean consequence are fully Lean-checked in [`PureThirdReplicationLinear.lean`](../../../formalization/HeadComplexity/Results/PureThirdReplicationLinear.lean), with declarations `score_covariance_bound`, `score_pos_iff_linear_of_third_margin`, `classifier_three_isLTF`, and `classifier_three_head_minima`.

## Replication five has threshold degree two

The fifth replication is nonlinear, but it admits an exact quadratic sign representation. Write the aggregate coordinates as $A_i=a_i/5$ and $B_i=b_i/5$, where each integer coordinate ranges over $\lbrace-15,-13,\ldots,15\rbrace$. Define

$$ L_0=4\sum_i a_i+3\sum_i b_i,\qquad z_i=a_i-b_i,\qquad N_{0,i}=2\left(\sum_j(a_j+b_j)+a_i\right). $$

An explicit quadratic is

$$ Q(a,b)=2016L_0+2L_0\sum_i z_i-\sum_iN_{0,i}z_i. $$

Every one of the $16777216$ aggregate patterns has the same strict sign for this quadratic and the source score. Neither vanishes, and the minimum absolute value of $Q$ on this grid is eight. The exhaustive signed-integer computation, with an explicit overflow bound, is recorded in [`check_fifth_quadratic.py`](../search/check_fifth_quadratic.py) and [`fifth_replication_quadratic.exact.json`](../search/fifth_replication_quadratic.exact.json). Since the aggregate coordinates are affine functions of the Boolean coordinates, this gives threshold degree at most two on the original 90-bit cube.

For the lower bound, consider cyclic permutations of the following positive and negative aggregate patterns:

$$ (a;b)=(-15,1,3;5,5,5),\qquad (a';b')=(-15,-11,15;13,15,-13). $$

The three positive scores are $49292/30441495$ and the three negative scores are $-1292/30413637$. Both triples have the same total first-half aggregate, negative eleven, and the same total second-half aggregate, fifteen. They admit three positive and three negative Boolean realizations whose first moments agree at every individual coordinate. To see this directly, the first-half counts are cyclic permutations of $(0,8,9)$ and $(0,2,15)$ across fifteen positions. Choose the size-eight and size-nine sets to cover all positions and overlap in two; take the size-two negative set to be this overlap and the size-fifteen negative set to be all positions. The positive second-half sets each have size ten, with disjoint size-five complements, while the negative second-half sets have sizes fourteen, fifteen, and one, the size-one set complementing the size-fourteen set. Every second-half coordinate then appears twice in both triples.

An affine score has equal sums over the two triples. It cannot be strictly positive at all three positive inputs and nonpositive at all three negative inputs. This exact first-moment obstruction is Lean-checked in [`PureFifthReplicationNonlinear.lean`](../../../formalization/HeadComplexity/Results/PureFifthReplicationNonlinear.lean), including `classifier_five_not_isLTF`, `classifier_five_threshold_degree_lower`, and `classifier_five_head_minima_lower`.

Consequently the fifth replication has threshold degree exactly two, with the upper bound certified by exhaustive integer arithmetic and the lower bound certified in Lean. All four architectures have the same minimum, which lies in $\lbrace2,3\rbrace$: if the pure minimum is two, the two-head equivalence gives vanilla minimum two; otherwise the pure lower bound and vanilla upper certificate force both minima to equal three. The quadratic certificate alone does not give a two-head representation, and this common minimum at replication five remains unresolved here.

## Replication seven has threshold degree three

At replication seven, the obstruction to quadratics returns. Take the six simultaneous permutations of each of the following aggregate patterns:

$$ (a;b)=(-21,9,19;9,1,-19),\qquad (a';b')=(-21,9,19;13,-15,-7). $$

The actual aggregates are $A_i=a_i/7$ and $B_i=b_i/7$. Every permutation of the first pattern has source score $3637/346730560\gt0$, whereas every permutation of the second has score $-203/346729048\lt0$.

The two permutation orbits have matching constant, first, and second moments. In both cases,

$$ \sum_i a_i=7,\qquad\sum_i b_i=-9,\qquad\sum_i a_i^2=883,\qquad\sum_i b_i^2=443,\qquad\sum_i a_i b_i=-541. $$

These five identities determine every first and second moment after simultaneous permutation averaging. Thus the sum of any quadratic polynomial over the positive orbit equals its sum over the negative orbit. Strict positivity on the first and nonpositivity on the second would contradict this equality.

This rules out quadratics in the original 126 Boolean variables as well. Independently average any proposed Boolean quadratic over all permutations inside each of the six types, each containing 21 coordinates. A diagonal Boolean monomial becomes the type count divided by 21; a product of distinct coordinates of the same type becomes $k(k-1)/(21\cdot20)$; a product from two different types becomes the product of their counts divided by $21^2$. Hence the averaged polynomial is quadratic in the six counts, preserves the source signs, and contradicts the orbit moment identity above.

The exact two orbits, moment comparisons, and rational scores are recorded in [`check_seventh_quadratic_obstruction.py`](../search/check_seventh_quadratic_obstruction.py) and [`seventh_replication_quadratic_obstruction.exact.json`](../search/seventh_replication_quadratic_obstruction.exact.json). The complete Boolean lower bound, including the six-type reindexing and independent permutation averaging, is Lean-checked in [`PureSeventhReplicationDegree.lean`](../../../formalization/HeadComplexity/Results/PureSeventhReplicationDegree.lean), with declarations `classifier_seven_not_thresholdDegLE_two`, `classifier_seven_pure_head_minimum`, and `classifier_seven_threshold_degree`. Together with the exhaustive vanilla three-head upper certificate, this proves threshold degree three and all four minimum head counts equal to three at replication seven. The vanilla upper certificate remains an exhaustive integer computation, while all lower bounds and the pure upper realization are formalized.

Copying coordinates extends the lower bound to every positive multiple of seven. Consequently each such replication has threshold degree three, pure minimum three for both standard and free rotary frequencies, and vanilla minimum at least three. These infinite-family consequences are Lean-checked as `classifier_seven_multiple_threshold_degree`, `classifier_seven_multiple_pure_head_minimum`, and `classifier_seven_multiple_head_minima`. This assertion concerns divisibility of replication counts; it does not assert monotonicity between consecutive counts or a vanilla three-head upper bound for arbitrary multiples of seven.
