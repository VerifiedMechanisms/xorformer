# Minimal Boolean moment circuits can retain full affine dimension

## Statement

Let $n\geq2$ and $D\geq n$. There is a signed cloud of

$$ H=D+2n+1 $$

points in $\mathbb R^{n+1}$ with the following properties. Queries are the anchored Boolean vectors $\bar x=(1,x)$.

1. All Boolean projection moments of degrees at most $D$ vanish.

2. The displayed dependence is a circuit: its coefficients are all nonzero, and every dependence among those moment columns is a scalar multiple of it.

3. There is no nonzero exact Boolean projection ghost supported on these points. Equivalently, the columns obtained from all projection moments of all orders are linearly independent.

4. The points have affine span $\mathbb R^{n+1}$. They can all be translated into the strictly positive orthant.

5. The signed cloud has exactly the same scalar-kernel observations as a cloud on one affine line with $D+3$ atoms.

For example, let $D$ grow much faster than $n$. Then $H/D$ tends to $1$, while the affine dimension remains $n+1$. Thus neither minimality of the finite-moment circuit nor removal of all exact ghosts on its current support gives an ordinary-Veronese bound of the form $\dim\mathrm{aff}(S)=O(H/D)$. The global transport in property 5 repairs this particular example economically.

## Construction

Use coordinate vectors $e_0,e_1,\ldots,e_n$. Define the chain points

$$ P_0=0,\qquad P_n=\sum_{i=1}^n e_i,\qquad U_i=e_0+\sum_{j=1}^i e_j,\qquad V_i=U_i-e_{i+1}\quad(0\leq i\lt n). $$

The exact chain ghost has coefficients $-1$ at $P_0$, $+1$ at $P_n$, $-1$ at every $U_i$, and $+1$ at every $V_i$. It obeys the all-kernel identity

$$ F(\bar x\cdot P_n)-F(0)+\sum_{i=0}^{n-1}\bigl(F(\bar x\cdot V_i)-F(\bar x\cdot U_i)\bigr)=0. $$

This follows by telescoping, since $x_{i+1}$ is either zero or one. Every exact ghost on this chain support is a scalar multiple of this identity; the zero and singleton Boolean queries already prove that fact. These statements are kernel checked in `BooleanProjectionChainCircuit.lean`.

Remove $P_0$ and $U_0=e_0$. Let $G'$ be the remaining $2n$ points, with their original signed coefficients $g_w$. Then

$$ \sum_{w\in G'}g_wF(\bar x\cdot w)=F(0)+F(1). $$

Set $q=D+1$ and choose $M\geq2$. Append the $q$ intercept-axis points $jMe_0$, for $1\leq j\leq q$. For the nodes $M,2M,\ldots,qM$, let

$$ L_j(t)=\prod_{\substack{1\leq k\leq q\cr k\neq j}}\frac{t-kM}{(j-k)M},\qquad c_j=-L_j(0)-L_j(1). $$

The two evaluations $L_j(0)$ and $L_j(1)$ have the same nonzero sign, since both arguments lie strictly below every interpolation node. Consequently every $c_j$ is nonzero.

Lagrange interpolation gives, for every polynomial $p$ of degree at most $D$,

$$ p(0)+p(1)+\sum_{j=1}^q c_jp(jM)=0. $$

Combining the two identities proves the required moment relation on the $2n+q$ points. It also proves the exact all-kernel equivalence to the line cloud with nodes $0,1,M,\ldots,qM$ and coefficients $1,1,c_1,\ldots,c_q$.

## Minimality of the finite-moment dependence

Suppose arbitrary coefficients $a_w$ on $G'$ and $d_j$ on the line atoms annihilate every Boolean projection moment through degree $D$. The contribution of the line atoms is independent of the Boolean query. Subtracting the moment equations at $x$ and at the zero query therefore gives

$$ \sum_{w\in G'}a_w(\bar x\cdot w)^k=\sum_{w\in G'}a_w(\bar 0\cdot w)^k\qquad(0\leq k\leq D). $$

All the chain projection values belong to $\lbrace0,1,\ldots,n\rbrace$. Since $D\geq n$, Vandermonde interpolation upgrades this to equality for every scalar kernel $F$.

At the zero query, only $P_n$ projects to zero; all other points of $G'$ project to one. Write $b=a_{P_n}$ and let $t$ be the sum of the other coefficients. Thus the chain part has projection measure $b\delta_0+t\delta_1$ at every Boolean query.

Adjoin coefficients $-b$ at $P_0$ and $-t$ at $U_0$. This is an exact ghost on the original chain support. Its uniqueness forces $t=b$ and $a_w=bg_w$ for every point of $G'$. The remaining moment equations become

$$ b(0^k+1^k)+\sum_{j=1}^q d_j(jM)^k=0\qquad(0\leq k\lt q). $$

The square Vandermonde matrix on the $q$ distinct line nodes is invertible. Hence $d_j=bc_j$ for every $j$. This proves one-dimensionality of the kernel, and all the displayed coefficients are nonzero. Therefore every proper subset is independent.

## Absence of supported exact ghosts

Suppose arbitrary coefficients on the constructed support give zero against every scalar function of every Boolean projection. At the zero Boolean query, each line atom has its own projection value $jM$, distinct from the chain projection values zero and one. Testing the indicator of that value forces its coefficient to vanish.

What remains is an exact ghost supported on $G'$. Extend it by zero at the two removed chain points. Uniqueness of the original chain relation forces every coefficient to vanish. Thus there is no exact ghost on the current support, despite the high-order finite-moment circuit.

## Affine dimension and positivity

The differences $U_i-V_i=e_{i+1}$, for $1\leq i\lt n$, supply $e_2,\ldots,e_n$. The difference $U_1-V_0=2e_1$ supplies $e_1$. Finally, $U_1-P_n=e_0-\sum_{i=2}^n e_i$ supplies $e_0$. All are differences of points in $G'$, so its affine span is full.

Translate every point by $2(e_0+\cdots+e_n)$. Every coordinate is then strictly positive. Translation preserves moment vanishing through degree $D$ by the binomial formula, preserves the exact ghost and all-kernel equivalence statements by translating each scalar test function, and preserves affine dimension and circuit minimality.

## Implication for the unrestricted problem

This example refutes a support-local access lemma, not the desired lower bound. In particular, the assertion that a minimal finite-moment circuit with no supported exact ghost must have affine dimension $O(H/D)$ is false for Boolean projection moments. Applying an ordinary Veronese circuit theorem after merely deleting supported exact ghosts is therefore invalid.

The example remains compatible with a global signed transport theorem that adds new atoms and removes projection ghosts. Here the transport is explicit and uses only two new points before deleting the full-dimensional chain. The resulting one-line cloud is precisely the economical structure that a useful access theorem would need to recover.

The statement concerns constant-residue projection clouds. It does not establish a compiler for general curved denominator paths or moving affine numerators, and it makes no margin claim for truth tables.

## Verification status

`SplicedProjectionCircuit.lean` kernel checks `chain_remainder_identity`, `two_point_polynomial_identity`, and `spliced_polynomial_identity`. These prove the all-kernel chain replacement and the interpolation moment relation. The all-size minimality, absence-of-supported-ghost, and affine-dimension arguments above are written proofs, using the already kernel-checked chain uniqueness theorem.

`verify_spliced_moment_circuit.py` supplies exact finite checks for nine examples with $2\leq n\leq5$ and $3\leq D\leq50$. It verifies every moment relation with rational arithmetic and verifies rank $H-1$ for the moment matrix, rank $H$ for the full fiber-incidence matrix, and affine rank $n+1$ modulo the prime $1000000007$. The rational identities provide the matching upper bound for the moment rank. These computations are evidence for the stated formulas and are not substitutes for the written proof.
