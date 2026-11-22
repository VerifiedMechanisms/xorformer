# Positive Cauchy Fibers and Local Sign Constructions

## Scope and exact finite result

There are six fixed tests

$$ F_q(\theta)=\sum_{i=1}^3\frac{r_{qi}}{\theta_i+p_{qi}}-c_q,\qquad p_{qi},r_{qi}\gt0, $$

whose strict signs realize all 64 binary patterns as $\theta$ ranges over the positive orthant. The exact coefficients and 64 witnesses are in [the rational certificate](separable-mobius/n3-m6-positive-fiber-exact.json). Every test is strictly decreasing in each parameter and strictly convex: its Hessian is diagonal with entries $2r_{qi}/(\theta_i+p_{qi})^3\gt0$.

This concerns a separable reciprocal relaxation. Its query coefficients vary freely between tests. It does not identify these tests with Boolean evaluations of the manuscript's architecture, and it gives no asymptotic lower bound for that architecture.

The construction uses six regular permutation branches, exact linear feasibility, and an explicitly bounded rational perturbation. The retained linear certificate is [here](separable-mobius/n3-m6-positive-fiber-linear.json). Solver failure in the larger seven-test and nine-test searches is not used as evidence of an upper bound.

## Symmetric fibers and offset rank

Fix distinct positive numbers $t_1,\ldots,t_h$ and a positive number $p$. For a permutation $\pi$ of $\lbrace1,\ldots,h\rbrace$, set $\theta_i=t_{\pi(i)}$. The symmetric test

$$ \sum_{i=1}^h\frac1{\theta_i+p}-\sum_{j=1}^h\frac1{t_j+p} $$

vanishes at every such permutation. Its derivative after writing $\theta_i=t_{\pi(i)}+\varepsilon v_{\pi(i)}$ is independent of the branch:

$$ -\sum_{j=1}^h\frac{v_j}{(t_j+p)^2}. $$

Perturb the residues to $1+\varepsilon\alpha_i$, the poles to $p+\varepsilon\beta_i$, and the threshold by $\varepsilon\gamma$. The branch-dependent first-order offset is

$$ e_\pi=\sum_i\left(\frac{\alpha_i}{t_{\pi(i)}+p}-\frac{\beta_i}{(t_{\pi(i)}+p)^2}\right)-\gamma. $$

For $h\geq3$, these offsets form a vector space of dimension $2h-1$ inside the space of functions on the $h!$ permutations.

**Proof.** Put $a_j=(t_j+p)^{-1}$ and $b_j=-a_j^2$. Suppose $\sum_i(\alpha_i a_{\pi(i)}+\beta_i b_{\pi(i)})-\gamma=0$ for every permutation. Swapping the distinct values $j,k$ between positions $r,s$ and subtracting gives

$$ (a_j-a_k)\left((\alpha_r-\alpha_s)-(\beta_r-\beta_s)(a_j+a_k)\right)=0. $$

The $a_j$ are distinct. For each fixed $r,s$, choose two pairs $j,k$ with different sums $a_j+a_k$, which is possible because $h\geq3$. Subtraction forces $\beta_r=\beta_s$, and then $\alpha_r=\alpha_s$. Thus all $\alpha_i$ equal one constant, all $\beta_i$ equal another, and $\gamma$ is determined by those two constants. Conversely, every such choice is a relation. The linear map from $2h+1$ coefficients therefore has a two-dimensional kernel and rank $2h-1$. $\blacksquare$

For $h=3$, every offset satisfies $\sum_\pi\mathrm{sgn}(\pi)e_\pi=0$: fixing a coordinate value leaves two permutations of opposite parity. The alternating relation has a five-dimensional kernel, which equals the offset image by the rank calculation. Thus this single relation is the complete compatibility condition, not an assumed genericity property.

## The retained linear system

For the six-test construction, take $h=3$, $t=(1,2,3)$, and $p_q=q$ for $1\leq q\leq6$. Define

$$ G_{qj}=-\frac1{(t_j+p_q)^2},\qquad C=G(G_{1:3})^{-1}. $$

Here $G_{1:3}$ denotes the first three rows. Its determinant is exactly $-4679/1866240000$, as verified by rational arithmetic. The first three rows of $C$ are the identity matrix.

For every sign vector $y\in\lbrace-1,1\rbrace^6$, the retained linear certificate specifies a branch $\pi_y$ and a rational vector $w_y\in\mathbb Q^3$. It also specifies six rational offset vectors $e_\pi\in\mathbb Q^3$ satisfying the alternating relation coordinatewise. The independently checked inequalities are

$$ y_q w_{yq}\geq1\quad(1\leq q\leq3),\qquad y_q\left(C_qw_y+e_{\pi_y,q-3}\right)\geq1\quad(4\leq q\leq6). $$

For the first three queries use zero perturbation offsets. For each later query, solve the displayed offset equation for rational $\alpha,\beta,\gamma$. The rank theorem proves compatibility, and the verifier checks each resulting equality exactly. Transform $w_y$ back by $(G_{1:3})^{-1}$ and assign its entries to the coordinates prescribed by $\pi_y$. This gives a rational direction $v_y$ in the original parameter coordinates. Every signed first-order test value is at least one.

## Explicit perturbation and error bound

For a fixed query, witness, and coordinate write $d=t_{\pi(i)}+p_q$, $a=\alpha_{qi}$, and $w=\beta_{qi}+v_{yi}$. Direct algebra gives

$$ \frac{1+\varepsilon a}{d+\varepsilon w}-\frac1d-\varepsilon\left(\frac ad-\frac w{d^2}\right)=\frac{\varepsilon^2w(w-ad)}{d^2(d+\varepsilon w)}. $$

If $\varepsilon|w|\leq d/2$, the absolute remainder is at most $2\varepsilon^2|w|(|w|+|a|d)/d^3$. Let $R$ be the maximum, over all retained query-witness pairs, of the sum of these coefficient bounds over the three coordinates. It is an explicitly computed nonnegative rational number.

Choose $\varepsilon$ to be the minimum of one, $1/(2(1+R))$, and all the following positive rational numbers:

$$ \frac1{2(1+|\alpha_{qi}|)},\qquad \frac{p_q}{2(1+|\beta_{qi}|)},\qquad \frac{t_{\pi_y(i)}}{2(1+|v_{yi}|)}. $$

The resulting residues, poles, and witness coordinates are strictly positive. The last two bounds imply $\varepsilon|\beta_{qi}+v_{yi}|\leq(t_{\pi_y(i)}+p_q)/2$. Thus every total remainder is at most $\varepsilon^2R\lt\varepsilon/2$. Since the signed linear term is at least $\varepsilon$, every final signed test value exceeds $\varepsilon/2$.

All constants, the chosen scale, and the final witness coordinates are recorded as exact fractions. `lift_permutation_fiber_witness.py` checks the offset identities and all linear inequalities, computes this scale, and independently evaluates all 384 final reciprocal signs. This proves the finite result without inferring a positive margin from floating-point calculations. $\blacksquare$

## Formal verification boundary

`generate_positive_fiber_lean.py` clears the denominators of the retained certificate with one common integer scale and generates `PositiveMobiusFiberShattering.lean`. Its finite inequalities and real-valued sign transfer are separate from the linear solver. The final declaration is `HeadComplexity.PositiveMobiusFiberShattering.six_positive_tests_shattered`; `residues_positive` records the additional strict positivity of all residues.

The general offset-rank calculation and perturbation mechanism above are written proofs. The finite Lean certificate verifies its resulting six-test example directly. Neither level of verification asserts the requested unboundedness of $n^2W(n)/2^n$.
