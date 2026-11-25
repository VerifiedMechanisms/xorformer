# Pure RoPE Separates Every Head Budget Above Two

## Statement and formalization status

In the unchanged xorformer model, the universal reverse implication holds exactly at head budgets at most two:

$$ \left[\forall n\ \forall f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace,\quad f\text{ is pure-RoPE computable with }H\text{ heads}\Longrightarrow f\text{ is vanilla computable with }H\text{ heads}\right]\quad\Longleftrightarrow\quad H\leq2. $$

More precisely, for every integer $H\geq3$, an explicit family $f_{H,m}$ on $2H^2m$ bits satisfies, for all sufficiently large positive integers $m$,

$$ H^{\ast}_{\mathrm{pure\ RoPE}}(f_{H,m})=H,\qquad H+1\leq H^{\ast}_{\mathrm{vanilla}}(f_{H,m})\leq2^H-2. $$

Both standard fixed rotary frequencies and freely chosen frequencies have the displayed pure minimum. The model uses a fixed query attending to every input and itself, unrestricted finite dimensions and real parameters, Q/K-only rotations, and unrotated token-only values. Classification uses the existing strictly positive score threshold. Retained positional embeddings are not involved.

The entire arbitrary-head result is Lean-checked, including the actual Boolean classifiers, exact pure minimum, vanilla lower and upper bounds, and scalar-to-rotary architectural bridge. The final theorem has no remaining algebraic or analytic premise. Its dependencies use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms, with no `sorry` or additional axioms. The specialized three-head proof remains available in [Theorem 22](022_pure_rope_three_head_separation.md).

## The explicit family

Fix $H\geq3$. There are $H$ blocks, each containing $2H$ coordinate groups. Each group contains $m$ bits. Write their centered means as

$$ q_{bj}=\frac1m\sum_{r=1}^m(2x_{bjr}-1),\qquad 1\leq b\leq H,\quad1\leq j\leq2H. $$

For $1\leq i\leq H$, define

$$ d_i(q)=\sum_{b=1}^H(q_{bi}-q_{b,H+i}),\qquad N_i(q)=2\sum_{b=1}^H\left(\sum_{j=1}^{2H}q_{bj}+q_{bi}\right),\qquad D_i(q)=C_H+d_i(q), $$

where

$$ B_H=4H^2+2H,\qquad C_H=20H^2+20. $$

Let $f_{H,m}$ be the strictly positive threshold of $S_H(q)=\sum_iN_i(q)/D_i(q)$. On the continuous cube, $|d_i(q)|\leq2H$ and $|N_i(q)|\leq B_H$, so every denominator is positive.

These are genuine pure atoms. Let $d_{ij}$ and $u_{ij}$ be the coefficients of a group coordinate in $d_i$ and $N_i$, respectively. They do not depend on the block. Explicitly, $d_{ij}$ is $1$ at $j=i$, $-1$ at $j=H+i$, and zero elsewhere; $u_{ij}$ is $4$ at $j=i$ and $2$ elsewhere. For each individual bit in this group choose

$$ a_{bjr}=\frac{2(u_{ij}-d_{ij})}{m},\qquad b_{bjr}=\frac{2u_{ij}}m,\qquad\gamma=C_H-2B_H,\qquad\eta=-B_H,\qquad v_0=0,\quad v_1=1. $$

All input masses are strictly positive, and $\gamma=12H^2-4H+20\gt0$. The resulting atom has numerator $N_i(q)$ and denominator $D_i(q)$ exactly. Thus $H$ pure heads compute $f_{H,m}$. The established architectural bridge realizes these same scores with common standard rotary frequencies, and hence also with free frequencies.

At $H=3$, this is exactly the family of Theorem 22, including its denominator constant $C_3=200$.

## A general contraction-rank lemma

Use independent variables $D_1,\ldots,D_H,N_1,\ldots,N_H$, and set

$$ W_H(D,N)=\sum_{i=1}^H N_i p_i(D),\qquad p_i(D)=\prod_{j\neq i}D_j,\qquad p_{ik}(D)=\prod_{j\notin\lbrace i,k\rbrace}D_j. $$

Let $T_H$ be its symmetric $H$-linear polarization, with any fixed nonzero normalization. Contract its first argument against $v=(d,a)$. Flatten the remaining tensor into a matrix whose rows are the second argument and whose columns are the remaining $H-2$ arguments.

**Claim.** If $d=0$, this flattening has rank at most $H$. If $d\neq0$, its rank is at least $2H-2$, which is strictly greater than $H$.

**Proof.** Up to a nonzero constant, diagonal evaluation of the contracted tensor is the directional derivative

$$ Q_v(D,N)=\partial_vW_H=\sum_i a_i p_i(D)+\sum_iN_i q_i(D),\qquad q_i(D)=\sum_{k\neq i}d_kp_{ik}(D). $$

When $d=0$, this polynomial and its polarization use only the $H$ denominator coordinates. The rank is therefore at most $H$.

Suppose $d\neq0$. A vector $w=(e,b)$ in the flattening kernel satisfies $\partial_wQ_v=0$: evaluate all remaining arguments at the same vector. The nonzero scalar relating the two expressions is a factorial. Comparing the coefficients of the independent numerator variables gives $\partial_e q_i=0$ for every $i$.

For distinct $k,l$ different from $i$, the coefficient of the monomial with denominator indices $i,k,l$ omitted is

$$ d_ke_l+d_le_k. $$

For fixed $i$, distinct unordered pairs $\lbrace k,l\rbrace$ give distinct monomials. Since $H\geq3$, each pair $k\neq l$ has some excluded index $i$. Hence

$$ d_ke_l+d_le_k=0\qquad(k\neq l). $$

Choose $s$ with $d_s\neq0$. These equations determine every $e_j$, for $j\neq s$, from the single coordinate $e_s$. Thus the projection of the flattening kernel onto its denominator-direction coordinates has dimension at most one.

In the kernel of that projection, $e=0$. The remaining derivative identity is $\sum_i b_iq_i=0$. Comparing its distinct monomials $p_{ik}$ gives

$$ b_id_k+b_kd_i=0\qquad(i\neq k). $$

Again every $b_j$ is determined by $b_s$. This fiber has dimension at most one. Rank-nullity for the projection restricted to the flattening kernel now bounds that kernel's dimension by two. Its domain has dimension $2H$, so the flattening rank is at least $2H-2\gt H$. $\blacksquare$

The lemma is unchanged if $T_H$ is multiplied by a nonzero scalar or each block undergoes the same invertible linear change of coordinates.

## The physical source coordinates

Within one block, the map from physical coordinates $x_1,\ldots,x_{2H}$ to denominator and numerator directions is

$$ d_i=x_i-x_{H+i},\qquad u_i=2\left(\sum_{j=1}^{2H}x_j+x_i\right). $$

It is invertible. Indeed, with $s=\sum_jx_j$,

$$ s=\frac{\sum_i u_i-\sum_i d_i}{2H+1},\qquad x_i=u_i/2-s,\qquad x_{H+i}=u_i/2-s-d_i. $$

The common kernel $K$ of the physical denominator rows is the $H$-dimensional paired subspace. In particular, it contains the all-ones vector. The source mixed tensor is nonzero: it is the polarization of the nonzero polynomial $W_H$, transported by an invertible map in every block. By the contraction-rank lemma, for this tensor the vectors whose contractions have flattening rank at most $H$ are exactly $K$.

## The closed obstruction for vanilla tensors

Consider the degree $H$ mixed tensor of a cleared $H$-head vanilla score, retaining one coordinate from each of the $H$ blocks. Denominator rows in a block either have uniformly strict sign or are zero. Numerator rows are arbitrary; an arbitrary score constant can be absorbed into one numerator before clearing denominators.

The common kernel of the $H$ denominator rows in the first $2H$-dimensional block has dimension at least $H$. Choose an orthonormal $H$-frame in it. Contracting along any member of this frame kills every term in which the first block supplies a denominator. In the surviving terms, the covectors in the second block belong to the span of its $H$ denominator rows. Thus each contraction flattening has rank at most $H$.

Suppose a sequence of these vanilla tensors converges to a nonzero scalar multiple of the source tensor. The source tensor is nonzero. Eventually each approximating tensor is nonzero, so at least one denominator is nonconstant. Its first-block row is uniformly strict in sign. Normalize that row, changing its sign if necessary, to a nonnegative vector with coordinate sum one.

Pass to a subsequence on which both the orthonormal frame and this simplex vector converge. Their parameter spaces are compact. Rank at most $H$ is closed, since it is the vanishing of all $(H+1)$ by $(H+1)$ minors. Every limit frame vector therefore belongs to $K$ by the contraction-rank lemma. The $H$ orthonormal limit vectors span $K$.

The limit simplex vector is perpendicular to this entire frame, hence to $K$. But $\mathbf1\in K$, while its inner product with $\mathbf1$ is its coordinate sum, equal to one. This contradiction proves that no such sequence of vanilla tensors exists.

This argument does not bound or normalize individual head parameters. It permits arbitrary cancellations and arbitrary changes of representation.

## Irreducibility and sign rigidity

The source cleared polynomial is

$$ P_H(q)=W_H\bigl(C_H+d(q),N(q)\bigr). $$

The polynomial $W_H$ is irreducible. Over the rational-function field in the denominator variables it is a nonzero linear polynomial in the numerator variables, hence irreducible. Its coefficients $p_i(D)$ have greatest common divisor one, since each denominator variable is absent from one coefficient. Gauss's lemma proves irreducibility over the real polynomial ring.

The invertible block-coordinate map, followed by the use of the block sums as the first $2H$ coordinates and the other blocks as unused coordinates, identifies $P_H$ with $W_H$ after an invertible affine substitution. Its degree is exactly $H$, and it remains irreducible in the larger polynomial ring.

Near $q=0$, all denominators equal $C_H\gt0$ and all numerators vanish. In these affine coordinates the zero set has the rational graph

$$ N_1=-\frac{\sum_{i=2}^H N_ip_i(D)}{p_1(D)}. $$

There is an open patch of this graph inside the physical cube, with $p_1(D)\neq0$. The polynomial changes sign across the patch.

Consequently, any nonzero polynomial $Q$ of degree at most $H$ with weakly matching signs throughout the cube must be a positive scalar multiple of $P_H$. Continuity first forces $Q$ to vanish on the graph patch, by approaching it from both sign regions. Substitution of the rational graph into $Q$, followed by clearing powers of $p_1$, gives a polynomial that vanishes on an open set and is therefore identically zero. Division over the rational-function field and Gauss's lemma give $P_H\mid Q$. The degree bound forces a scalar multiple, and weak sign agreement forces the nonzero scalar to be positive.

The same argument shows that no nonzero polynomial of degree at most $H-1$ can have these weak signs.

## From finite Boolean grids to the contradiction

Suppose infinitely many replication counts had $H$-head vanilla classifiers for $f_{H,m}$. Select a sequence tending to infinity. At each replication count, decrease the free score constant by a sufficiently small amount so that all scores are strictly positive on true inputs and strictly negative on false inputs. The Boolean domain is finite, so this strictification preserves its classifier.

Clear the positive denominators. Average the resulting degree at most $H$ polynomial over permutations of the bits within each of the $2H^2$ replica groups. Every orbit has a constant source label, so strict signs are preserved. Sampling without replacement expresses this average as a polynomial of degree at most $H$ in the group means, once $m\geq H$.

Normalize the entire averaged polynomial coefficient vector to have maximum absolute coefficient one. The fixed finite-dimensional coefficient space is compact, so a subsequence converges to a nonzero polynomial $Q$. For every point in the continuous cube, choose group-count grid points converging to it. Convergence of coefficients and evaluation gives weak sign agreement between $Q$ and $P_H$ wherever $P_H$ is nonzero. The preceding sign-rigidity argument yields $Q=\lambda P_H$ with $\lambda\gt0$.

The mixed degree $H$ tensor retaining one coordinate from every block preserves the actual vanilla factor structure under this averaging. Indeed, a degree at most $H$ monomial contributing to such a coefficient uses each of those $H$ groups exactly once. Its conditional mean is the product of the corresponding group means, so the coefficient is obtained by summing each original linear-form slope over its replica group. The degree bound excludes repeated-group contributions to this coefficient. Uniform strict denominator signs survive these sums.

Therefore the mixed tensors of the normalized averaged polynomials are actual vanilla tensors of the kind in the closed obstruction. Their limit is the mixed tensor of $\lambda P_H$, which is a nonzero scalar multiple of the physical source tensor. This is impossible. Hence all sufficiently large replication counts require more than $H$ vanilla heads.

For the exact pure minimum, repeat the coefficient-normalization and dense-grid sign argument assuming infinitely many degree at most $H-1$ polynomial sign representations. Averaging preserves that smaller degree, producing a nonzero limit of degree at most $H-1$ weakly agreeing with $P_H$. Sign rigidity contradicts the degree bound. Thus the family eventually has threshold degree $H$.

Pure heads are lower-bounded by threshold degree and the explicit construction uses $H$ pure heads, so their minimum is exactly $H$. The already proved pure-specific finite-difference bound supplies the vanilla upper bound $2^H-2$. This proves the displayed separation. $\blacksquare$

## A uniform coefficient gap

The closed obstruction also gives a quantitative conclusion with an existential radius. Fix a nonzero real scalar $t$. There is a number $\varepsilon\gt0$ such that every sum of $H$ affine numerators times the complementary products of $H$ oriented affine denominator forms differs from $tP_H$ by at least $\varepsilon$ in some squarefree coefficient of total degree $H$.

This statement imposes no bound on the factor parameters and does not require the denominator constants to be positive. If no such radius existed, choose an oriented factor sum whose error in every selected coefficient is less than $1/(k+1)$ for each positive integer $k$. These coefficients would converge to those of $tP_H$, contradicting the proved obstruction. The radius is not an effective replication threshold.

## Consequences and Lean declarations

The two-head theorem proves the universal reverse implication for $H\leq2$, including zero heads. The construction above disproves it for every $H\geq3$. Adding unused bits preserves all four minimum head counts exactly, so for every fixed $H\geq3$ there is such a separation at every sufficiently large input length.

The mathematical proof is uniform in $H$, but its threshold in $m$ is existential. The explicit sufficient threshold in Theorem 22 applies to $H=3$. The precise vanilla minimum between $H+1$ and $2^H-2$ and the first separating replication count remain undetermined.

Zero heads and zero input length are included in the universal theorem. With zero heads, only constant Boolean functions are computable. At input length zero, every Boolean function is constant and all four minimum head counts are zero. No complement-invariance assumption is used at two heads.

The principal declarations are:

- `PureGeneralReplicatedGrid.eventually_complexity_separation_general` in [PureGeneralSeparation.lean](../../formalization/HeadComplexity/Results/PureGeneralSeparation.lean) proves the full eventual family bounds and both rotary minimum identities for every $H\geq3$.

- `universal_pure_to_vanilla_iff_head_le_two` in [RoPEUniversalBudgets.lean](../../formalization/HeadComplexity/Results/RoPEUniversalBudgets.lean) classifies every head budget. The same file proves the standard fixed-frequency, shared free-frequency, and headwise free-frequency versions.

- `pureRoPE_separation_every_budget_every_large_input_length` in [PureGeneralSeparationAllLargeInputs.lean](../../formalization/HeadComplexity/Results/PureGeneralSeparationAllLargeInputs.lean) proves the separation at every sufficiently large input length for each fixed $H\geq3$.

- `PureGeneralReplicatedGrid.exists_oriented_top_coefficient_gap` in [PureGeneralCoefficientGap.lean](../../formalization/HeadComplexity/Results/PureGeneralCoefficientGap.lean) proves the uniform coefficient gap.

The central algebraic declarations are `RoPEGeneralDerivative.secondMap_rank_le_iff`, `RoPEGeneralPolarization.contractDiagonal_source`, and `RoPEGeneralPhysicalRank.contractMap_scaled_reindexedPhysical_rank_le_iff`. They connect the actual source polynomial, its mixed coefficients, and the physical paired-coordinate rank locus. `BlockCoefficientLimit.tendsto_contractDiagonal_coeff` transports the coefficients preserved by Boolean replica averaging to moving contraction directions. `RoPEGeneralFrames.no_conditionally_oriented_polynomial_rank_limit` supplies the compactness contradiction, including zero denominator matrices. `PureGeneralReplicatedGrid.oriented_factor_limit_excluded` discharges that obstruction for the actual family.

The vanilla architectural definitions and the strictly positive threshold convention are unchanged. The result separates Boolean computability classes; it does not infer such a separation from failure of exact real-score simulation.
