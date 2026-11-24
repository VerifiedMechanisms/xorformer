# Shared permutation dictionaries on exponential patches

## Status

This note investigates a possible universal upper construction. It does not prove an upper bound at the counting scale and does not prove the requested lower bound. It records a new patch compiler, a precise candidate family that avoids an explicit object-address input, and finite computations that reject several particular dictionaries. The finite computations do not reject all dictionaries.

The patch compiler is a written elementary proof. The negative finite certificate is an exact rational computation. Neither has been formalized in Lean.

## 1. A candidate without explicit object addresses

Fix positive numbers $p_0,w_1,\ldots,w_k,\lambda_1,\ldots,\lambda_H$ and vectors $b_1,\ldots,b_H\in\mathbb R^k$. Put

$$ p(v)=p_0+\sum_{j=1}^k w_jv_j,\qquad v\in\lbrace 0,1\rbrace^k. $$

For a permutation $\pi$ of $[H]$, consider the scores

$$ S_{\pi,\alpha,L}(v)=L(v)+\sum_{h=1}^H\frac{\alpha_h+b_h\cdot v}{p(v)+\lambda_{\pi(h)}}, $$

where $\alpha\in\mathbb R^H$ and the affine form $L$ are free. The vectors $b_h$, the statistic $p$, and the pole list are shared by every branch. Let the resulting label class be $\mathcal D$.

There are $H!$ discrete branches. This family does not allocate $\lceil\log_2H\rceil$ input coordinates to identify an object. Thus the previously established addressed-permutation counting obstruction does not directly apply. On the other hand, factorially many branches alone do not imply that $\mathcal D$ contains every Boolean labeling.

For fixed poles, define the linear table space

$$ V=\mathrm{span}\left(1,v_1,\ldots,v_k,\frac1{p(v)+\lambda_1},\ldots,\frac1{p(v)+\lambda_H}\right). $$

Every branch consists of a translate $g_\pi+V$, with

$$ g_\pi(v)=\sum_{h=1}^H\frac{b_h\cdot v}{p(v)+\lambda_{\pi(h)}}. $$

Consequently the actual universality question is whether these translates meet every open coordinate orthant. Their affine spans, covariances, and number of permutations are insufficient to establish that fact.

## 2. Independent row programming with shared slopes

Let $r\geq1$. On $r+k$ Boolean coordinates write $(z,v)$ and consider the patch

$$ P=\lbrace(e_i,v):1\leq i\leq r,\quad v\in\lbrace0,1\rbrace^k\rbrace. $$

**Proposition.** Choose independently for every row $i$ a branch permutation $\pi_i$, constants $\alpha_{ih}$, and an affine form $L_i(v)$. If the resulting row scores are strict, their combined label table on $P$ is represented by at most $H+k+1$ original-model heads, all with strictly positive denominator slopes.

**Proof.** Choose $d$ with $0\lt d\lt\min_h(p_0+\lambda_h)$. Define

$$ B_h(z,v)=d+\sum_{i=1}^r(p_0+\lambda_{\pi_i(h)}-d)z_i+\sum_{j=1}^k w_jv_j,\qquad A_h(z,v)=\sum_{i=1}^r\alpha_{ih}z_i+b_h\cdot v. $$

Every denominator coefficient, including its constant, is strictly positive. At $(e_i,v)$ the quotient is exactly the corresponding term of row $i$. The numerator is arbitrary affine, as permitted when the denominator is nonconstant.

It remains to approximate the table $L_i(v)$ with $k+1$ heads. Write $L_i(v)=\ell_{i0}+\sum_j\ell_{ij}v_j$. Choose $C_j\gt1+\max_i|\ell_{ij}|$, put $q_{ij}=C_j+\ell_{ij}\gt1$, and choose $0\lt d_j\lt\min_iq_{ij}^{-1}$. For $\varepsilon\gt0$ define

$$ D_{j,\varepsilon}(z,v)=d_j+\sum_{i=1}^r(q_{ij}^{-1}-d_j)z_i+\varepsilon\sum_{a=1}^k v_a. $$

At $(e_i,v)$ the head $v_j/D_{j,\varepsilon}$ tends to $q_{ij}v_j$ as $\varepsilon\to0^+$. Every slope is strictly positive for positive $\varepsilon$. A final head has numerator

$$ A_0(z,v)=\sum_i\ell_{i0}z_i-\sum_jC_jv_j $$

and denominator $1+\varepsilon(\sum_i z_i+\sum_jv_j)$. It tends to the displayed affine numerator. The sum of these $k+1$ heads therefore tends to $L_i(v)$ at every patch point. Since the patch is finite and the desired combined scores are strict, a sufficiently small positive $\varepsilon$ preserves every label. All denominators are positive on the whole ambient cube, not merely on $P$. $\blacksquare$

This proposition has no restriction on the number of rows. Thus a fixed dictionary that realizes every labeling on $k$ bits would independently program arbitrarily many one-hot rows with only $k+1$ additional heads. The needed dictionary universality has not been proved.

## 3. Why global localization is still missing

The displayed patch uses upper stars and positive denominator slopes. The descending support-localization compiler from the prior upper-bound work naturally programs lower stars with that orientation. Replacing $z$ by $1-z$ changes the row slopes to negative while leaving the data slopes positive, which violates the original coherent-slope condition.

One can instead try to transplant all row denominators directly to a lower star. For prescribed positive additive row values, this can require a large common shift in the denominator, as quantified in `universal_upper_construction_audit.md`. The new shifted Cauchy dictionary need not have the same label capacity. Taking a fixed radial limit is also insufficient: the checked fixed-radial transfer bounds that class separately, while the uniform moving-numerator extension is false.

Therefore even dictionary universality on upper-star patches would not by itself complete a full-cube upper construction. A sign-preserving localization compiler with controlled overhead would still be needed.

## 4. Finite exploration

The script `probe_shared_pencil_dictionary.py` uses $p(v)=1+\sum_j2^{j-1}v_j$, poles $\lambda_h=h$, and integer numerator slopes. It checks whether each target is strictly separable in any branch. The linear-program objective maximizes a common margin capped at one; numerator coefficients are unbounded. In particular the test does not incorrectly insist on unit margin while keeping a fixed offset unscaled.

The exploratory results are floating point and establish no universal theorem:

| Data bits | Heads | Free affine correction | Targets per dictionary | Dictionaries | Missed targets |
| --- | --- | --- | --- | --- | --- |
| 3 | 3 | no | all 256 | 10 | 78 to 93 |
| 4 | 4 | no | 1000 sampled | 3 | 874 to 887 |
| 3 | 3 | yes | all 256 | 5 | 0, 1, 1, 0, 1 |
| 4 | 4 | yes | 1000 sampled | 3 | 48, 45, 62 |
| 4 | 5 | yes | 3000 sampled | 1 | 23 |

The last two rows use centered integer dictionaries, meaning $\sum_h b_h=0$. Small successful cases do not extrapolate to an asymptotic construction. Failures of one dictionary do not imply failures of all dictionaries or of continuously varying pole values.

## 5. Exact certificate for one failed dictionary

The script `audit_shared_dictionary_failure.py` checks one target from the four-bit, four-head experiment. For every one of the 24 permutations it reconstructs rational nonnegative weights $t_v$ satisfying

$$ \sum_vt_v=1,\qquad \sum_vt_v y_vF(v)=0,\qquad \sum_vt_vy_vg_\pi(v)\leq0, $$

where $F(v)$ is the vector of the free constant, affine, and Cauchy features. All entries are rational because the input coordinates, poles, and numerator dictionary are rational. The script verifies these identities and inequalities with exact rational arithmetic after using a floating linear program only to propose a support.

If a branch had a strict representation, then $y_v(F(v)\cdot a+g_\pi(v))\gt0$ for every $v$. Multiplying by $t_v$ and summing would give a strictly positive number because the weights are nonnegative and sum to one. The first moment identity removes the free features, leaving the nonpositive last expression, a contradiction.

The rational witnesses are saved in `shared-pencil-exact-failure.json`. This is a finite exact certificate for the stated dictionary and target. It is not a proof about other dictionaries, larger dimensions, the unrestricted head class, or the desired lower exponent.

## 6. Convex relaxation is universally feasible in the failed example

The same exact audit proves two additional facts for this four-bit, four-head dictionary: the sum of its 24 offset vectors is zero, and the matrix containing all free feature columns together with all offset columns has rank 16 over the rationals. The output records a nonzero rational determinant of a selected square submatrix.

Let $Q=\mathbb R^{16}/V$ and project the offsets to $Q$. They span $Q$ and their equally weighted mean is zero. Therefore zero is an interior point of their convex hull in $Q$. Indeed, a supporting nonzero linear functional at zero would be nonnegative on every projected offset; their zero mean would then make it vanish on all of them, contradicting their spanning property.

For any target $y\in\lbrace-1,1\rbrace^{16}$, choose a sufficiently small $\eta\gt0$ that the class of $\eta y$ lies in this convex hull. Then some convex combination $g$ of branch offsets satisfies $\eta y-g\in V$. Thus the convexified family represents every strict Boolean target.

Convex combinations of permutation matrices are doubly stochastic, so this is also a universally feasible doubly stochastic relaxation. Section 5 nevertheless certifies a target missed by every permutation branch. The gap occurs in the actual positive Cauchy family with free affine corrections, rather than in an unrelated abstract polytope.

This finite counterexample rules out transferring relaxed feasibility to a single permutation without a further hypothesis. It does not rule out a rounding theorem that uses additional heads, a special dictionary, or quantitative hypotheses not present here.

## 7. Remaining question

The unaddressed permutation dictionary is a precise new possible escape from the earlier addressed-branch obstruction. No universal dictionary at $H=O(2^k/k)$, or at any smaller asymptotically relevant width, was constructed. No general obstruction at that scale was proved. Even such a dictionary would still need the global localization bridge explained above.
