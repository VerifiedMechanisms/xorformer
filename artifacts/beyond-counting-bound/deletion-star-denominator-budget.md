# Denominator Budgets on Deletion Stars

## Scope

The existing [bipartite shattering construction](bipartite-reciprocal-shattering.md) uses two-hot inputs. The [critical-width construction](critical-width-capacity-lower.md) uses lower deletion stars, where increasing denominator coefficients outside a center suppresses a new head on previously programmed cells. Combining these two mechanisms would require a new embedding. This note identifies an exact obstruction to copying the reciprocal query denominators into the latter cells.

These statements concern individual denominator tables. They do not constrain every signed sum that has the same signs, do not exclude a different local construction, and do not prove a worst-case head lower bound. Both denominator orientations remain allowed in the original model.

## Exact extension criterion

Let $I$ and $J$ be disjoint coordinate sets of cardinalities $R,M\geq2$, and put $U=I\cup J$. The sample points are

$$ z_{ij}=\mathbf1_U-e_i-e_j\qquad(i\in I, j\in J). $$

Fix real numbers $\theta_i,p_j$ such that $\theta_i+p_j\gt0$ for every pair. Put $\theta_{\max}=\max_i\theta_i$ and $p_{\max}=\max_j p_j$.

**Theorem 1.** There is an affine denominator $B(z)=c+\sum_{v\in U}b_vz_v$ with $c\gt0$ and every $b_v\gt0$, satisfying $B(z_{ij})=\theta_i+p_j$ for all pairs, if and only if

$$ (R-1)\theta_{\max}+(M-1)p_{\max}\lt\sum_i\theta_i+\sum_jp_j. $$

The same criterion applies if additional coordinates are fixed to one in every sample point, and strictly positive slopes are required on them as well. Arbitrary additional coordinates fixed to zero cause no change either.

**Proof.** Write $D=B(\mathbf1_U)$. The table condition is

$$ D-b_i-b_j=\theta_i+p_j. $$

Comparing two rows and then two columns gives constants $\alpha,\beta$ with $\alpha+\beta=D$, $b_i=\alpha-\theta_i$, and $b_j=\beta-p_j$. Thus positive slopes require $\alpha\gt\theta_{\max}$ and $\beta\gt p_{\max}$. The constant coefficient is

$$ c=D-\sum_i b_i-\sum_jb_j=\sum_i\theta_i+\sum_jp_j-(R-1)\alpha-(M-1)\beta. $$

Because $R-1$ and $M-1$ are positive, $c\gt0$ implies the claimed strict inequality.

Conversely, let $g$ be the positive gap in that inequality. Choose positive $\eta,\xi$ such that $(R-1)\eta+(M-1)\xi\lt g$, and set $\alpha=\theta_{\max}+\eta$, $\beta=p_{\max}+\xi$. Define the slopes and $c$ by the displayed formulas. Every slope and $c$ is strictly positive, and direct substitution gives all the required sample values. In particular the denominator is positive on the entire cube.

For extra coordinates fixed to one, assign them positive slopes with total less than $c$ and subtract that total from the constant coefficient. This preserves every sample value and positivity. Conversely, absorb those positive slopes into the constant before applying the necessity argument. Extra coordinates fixed to zero may be assigned arbitrary positive slopes; restricting them to zero proves necessity. $\blacksquare$

The criterion is unchanged by the additive gauge $\theta_i\mapsto\theta_i+t$, $p_j\mapsto p_j-t$: both sides change by $(R-M)t$. Thus choosing a different decomposition of the same additive table cannot repair a failed inequality.

## A concrete failed embedding

Take $R=M=3$, $\theta=(1,100,1)$, and $p=(1,1,1)$. The table is positive and has rows with constant values $2,101,2$. It occurs on two-hot inputs for the literal positive denominator

$$ B(x,y)=1+\sum_{i=1}^3(\theta_i-1/2)x_i+\sum_{j=1}^3(p_j-1/2)y_j. $$

Every displayed slope and the constant are strictly positive. On $(e_i,e_j)$ its value is $\theta_i+p_j$.

On lower deletion stars, however, the two sides of Theorem 1 are $202$ and $105$. Consequently no positive-slope denominator has this same table there. Complementing all six inputs does give a valid negative-slope denominator, but it does not give the positive slopes needed by the stated downset suppression construction. This distinction does not prohibit using negative heads in a different construction.

## Small denominators have a small vertex cover

Let $B(z)=c+\sum_vb_vz_v$ have positive constant and slopes, let a center $U$ contain disjoint nonempty sets $I,J$, and put $D=B(\mathbf1_U)$. For $0\lt\tau\lt1$, form a bipartite graph on $I,J$ with edge $ij$ exactly when

$$ B(\mathbf1_U-e_i-e_j)\leq\tau D. $$

**Theorem 2.** Every matching in this graph has size strictly less than $1/(1-\tau)$. Hence its edges can be covered by fewer than $1/(1-\tau)$ row and column vertices. When $\tau\leq1/2$, all its edges share one common vertex, unless it has no edges.

**Proof.** Every edge satisfies $b_i+b_j\geq(1-\tau)D$. For a matching of size $k$, the involved coordinates are distinct. Positivity of the constant and of the other coefficients gives

$$ k(1-\tau)D\leq\sum_{ij\text{ in the matching}}(b_i+b_j)\leq\sum_{v\in U}b_v\lt D. $$

This proves the matching bound. The vertex-cover conclusion follows from the bipartite matching theorem. Here is the needed argument. Choose a maximum matching, start alternating paths from its unmatched left vertices, and let $Z$ be the reachable vertices. The set of left vertices outside $Z$ together with right vertices inside $Z$ meets every edge. Otherwise an uncovered edge would lead from a reachable left vertex to an unreachable right vertex; whether or not it is matched, the alternating-path rules contradict this. There is no reachable unmatched right vertex, since such a path would augment the matching. Every matched edge has either both endpoints reachable or neither reachable. Thus the displayed cover contains exactly one endpoint of every matched edge, and no unmatched vertex. Its cardinality equals the matching size.

If $\tau\leq1/2$, the matching size is less than two, so the cover has size at most one. $\blacksquare$

## Consequence for the attempted dense shattering construction

The reciprocal-query embedding permits independently chosen positive row parameters and query poles. Theorem 1 shows that those tables cannot be copied unchanged into lower deletion cells. Theorem 2 quantifies the restriction responsible for this: one head can have denominators less than half its center value only on one row or one column of such a cell.

Neither theorem counts signs after unrestricted cancellation among several heads. In particular, a bounded denominator range on most entries is not a sign-preserving Taylor approximation theorem. The existing deep-cancellation examples still apply to proposed arguments based only on approximation error. The attempted combination is blocked at the missing embedding; the full critical-width sign count and the fixed-exponent lower bound remain unproved.

## Verification

The proofs above are written proofs. `verify_deletion_star_budget.py` independently checks the reconstruction formulas, the gauge invariance, and the small-denominator matching conclusion on finite exact rational examples. These checks are not Lean declarations and do not replace the quantified arguments.
