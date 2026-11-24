# Full-dimensional minimal Boolean projection circuits

## Statement

For every integer $n\geq1$, there is a signed measure on $2n+2$ distinct points in $\mathbb R^{n+1}$ with these properties:

1. Its pushforward under every anchored Boolean projection $w\mapsto w_0+\sum_iw_ix_i$ is zero.
2. Every signed measure on the same support having this property is a scalar multiple of it. In particular, no proper subset supports such a nonzero measure.
3. The support has affine span dimension $n+1$.
4. A common translation makes every intercept and slope strictly positive. The resulting reciprocal identity uses original admissible heads with arbitrary signed constant numerators.

Thus minimal universal projection circuits need not have dimension $O(\log H)$ when their support has size $H$. This does not establish a hard truth table. The measure represents the zero score and can be removed without changing any other score.

## Construction and identity

Let $e_0,e_1,\ldots,e_n$ be the coordinate vectors, and write $q_i=e_1+\cdots+e_i$, with $q_0=0$. Define

$$ P_0=0,\qquad P_n=q_n,\qquad U_i=e_0+q_{i-1},\qquad V_i=e_0+q_{i-1}-e_i\quad(1\leq i\leq n). $$

Assign coefficients $-1,+1,-1,+1$ respectively to $P_0,P_n,U_i,V_i$. For a Boolean input $x$, let $p_i=\sum_{j\leq i}x_j$. For every scalar function $F$ and every real $B$,

$$ F(B+p_n)-F(B)+\sum_{i=1}^n\bigl(F(B+1+p_{i-1}-x_i)-F(B+1+p_{i-1})\bigr)=0. $$

**Proof.** If $x_i=0$, the corresponding summand is zero. If $x_i=1$, it equals $F(B+p_{i-1})-F(B+p_i)$. These terms telescope, including the steps at which $p_i=p_{i-1}$. This proves the identity for every scalar kernel, not only polynomial moments or reciprocals.

The points are distinct. The two endpoint points have zeroth coordinate zero, and all other points have zeroth coordinate one. The $U_i$ are different prefixes. Each $V_i$ has a unique negative coordinate, namely coordinate $i$, so they are mutually distinct and different from every $U_j$.

## Minimality and full affine span

Give arbitrary coefficients $a,b,u_i,v_i$ to $P_0,P_n,U_i,V_i$, and suppose all anchored Boolean pushforwards vanish. The zero query, evaluated at projection value zero, gives $a+b=0$. At the singleton query $x=e_k$, the level-zero and level-one coefficient equations are

$$ a+v_k=0,\qquad b+u_k+\sum_{i\lt k}(u_i+v_i)=0. $$

The first gives $v_k=-a$ for every $k$. Inducting on $k$ in the second gives $u_k=a$, and the zero query gives $b=-a$. These coefficients are exactly a scalar multiple of the displayed relation. If any one coefficient vanishes, all vanish. This proves minimality.

The affine span is full because

$$ U_i-V_i=e_i,\qquad U_1-P_0=e_0. $$

These differences span all $n+1$ coordinate directions. Minimality here concerns universal projection identities, equivalently identities for every scalar test function. A relation among the reciprocal values at one fixed choice of base denominator can have additional accidental dependencies. No uniform minimality assertion for that narrower evaluation matrix is made.

## Original-model admissibility

Use the common base

$$ B(x)=2+2\sum_i x_i. $$

The endpoint denominators are $B$ and $B+\sum_i x_i$. The other denominators are $B+1+p_{i-1}$ and $B+1+p_{i-1}-x_i$. Every intercept is two or three and every slope is one, two, or three. They are positive on the entire cube and have strictly positive coherent slopes, so `FracAtom.ofPositiveAffineRatio` realizes their constant signed numerators as genuine original heads. Taking $F(t)=1/t$ in the identity proves exact cancellation.

The denominators are distinct, uniformly bounded away from zero, and separated in coefficient space. Therefore this dependence does not require colliding poles or a denominator boundary. The construction nonetheless has a short description. It uses one common affine base and an ordered coordinate chain. Its full affine span does not imply a large configuration parameter count.

## Quotient-aware interpretation

The identity is the sum of $n$ translated four-point anchored ghosts. Before cancellation, adjacent ghosts share an intermediate point with opposite coefficients. Restoring those $n-1$ auxiliary points decomposes the minimal $2n+2$-point circuit into $n$ elementary pieces. The number of point occurrences is $4n$, less than twice the original support size.

Consequently this example is compatible with a constant-support-overhead compiler that is allowed to introduce auxiliary directions and remove exact ghosts. It only rules out a classification based on the affine span of minimal circuits on their original support. The unresolved question is whether every relevant projection relation admits an equally economical normal form, with quantitative control through nearby perturbations and moving affine numerators. No general sparse lift or label-preserving access theorem follows from this chain.

## Verification boundary

The Lean file `formalization/HeadComplexity/Research/BooleanProjectionChainCircuit.lean` checks `scalar_function_identity`, `all_projection_moments`, and `reciprocal_identity` for every $n$. It also checks `constant_residue_identity_unique`, deriving the one-dimensional relation space from universal scalar-kernel identities, with arbitrary real coefficients. Its intermediate zero and singleton probe formulas are checked directly.

Distinctness, affine span, the positive-affine realization application, and the elementary-ghost decomposition are written proofs above. `verify_projection_chain.py` independently checks exact rational matrices for $1\leq n\leq8$; `projection-chain-exact.json` distinguishes projection rank from the rank of one selected reciprocal evaluation matrix. Those finite computations are not used for the arbitrary-dimension proof.

The target build passed with 3226 jobs. All five audited exported declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. The saved build and axiom outputs are `projection-chain-build.txt` and `projection-chain-axioms.txt`; the GitHub render audit recognized all 51 math spans.
