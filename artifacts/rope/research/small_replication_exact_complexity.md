# Exact Head Counts at the First Two Replication Counts

The source family from [Theorem 22](../../../theorems/03_rotary_attention/022_pure_rope_three_head_separation.md) does not separate the architectures at its first two replication counts. The first classifier has minimum one in both models. The second has minimum three in both models. The arguments below also explain why numerical fitting failures at small replication counts cannot establish separation.

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
