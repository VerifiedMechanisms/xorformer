# A global parity margin certificate and the atomic sparsity gap

## Status

The parity theorem in this note is kernel checked against genuine original heads and the full-cube relative margin. It quantifies over every representation at every width. The convex atomic dual and the universal monomial comparison are written proofs.

This result does not disprove the requested margin repair. The upper bound $2^{1-n}$ is much larger than either tested margin $\exp(-\exp(\sqrt n))$ or $\exp(-\exp(n/\log n))$ for all sufficiently large $n$. It supplies a genuine all-representation certificate and identifies exactly what a convex atomic relaxation forgets.

## An upper bound for every parity representation

Let $n\geq1$, let $X=\lbrace0,1\rbrace^n$, and write

$$ \chi(x)=\prod_{i=1}^n(1-2x_i),\qquad N=2^n. $$

For every admissible original head $\phi$, with arbitrary real numerator coefficients and either coherent denominator orientation,

$$ \left|\sum_{x\in X}\chi(x)\phi(x)\right|\leq2\|\phi\|_\infty. $$

Consequently, for every width $H$, every real bias $b$, and every collection of genuine heads strictly representing parity,

$$ \frac{\min_x\chi(x)\left(b+\sum_{h=1}^H\phi_h(x)\right)}{|b|+\sum_{h=1}^H\|\phi_h\|_\infty}\leq\frac2N. $$

Every norm here is on the full Boolean cube. Head count, coefficient magnitudes, target-dependent denominators, and signed cancellation are unrestricted.

### Lemma 1. The reciprocal functional

First let $B(x)=\beta+\sum_iw_ix_i$, with $\beta\gt0$ and $w_i\geq0$, including zero slopes. Define

$$ L(U)=\sum_x\frac{\chi(x)U(x)}{B(x)},\qquad C=L(1),\qquad E_i=L(x_i). $$

The Laplace identity and the Boolean product expansion give

$$ C=\int_0^\infty e^{-\beta t}\prod_i(1-e^{-w_it}) dt,\qquad E_i=-\int_0^\infty e^{-\beta t-w_it}\prod_{j\neq i}(1-e^{-w_jt}) dt. $$

Therefore $0\leq C\leq1/\beta$, $E_i\leq0$, and

$$ C-E_i=\int_0^\infty e^{-\beta t}\prod_{j\neq i}(1-e^{-w_jt}) dt\leq\frac1\beta. $$

All integrals are absolutely convergent, since each is a finite sum of decaying exponentials. These identities and inequalities are included in the Lean proof.

### Lemma 2. A nonnegative affine numerator

If $U(x)=a+\sum_iu_ix_i\geq0$ on the cube, then

$$ \sum_i(-u_i)_+\leq a. $$

Evaluate $U$ at the vertex containing exactly the negative-slope coordinates. Put $R=1/\beta-C\geq0$. Since $E_i\leq0$ and $-E_i\leq R$, one has

$$ u_iE_i\leq(-u_i)_+R. $$

It follows that

$$ L(U)=aC+\sum_iu_iE_i\leq aC+R\sum_i(-u_i)_+\leq\frac a\beta. $$

### Lemma 3. A bounded original head

Let $\phi=A/B$, where $A$ is affine, and put $M=\|\phi\|_\infty$. The affine function $U=MB+A$ is nonnegative on the full cube. Its constant coefficient is $M\beta+A(0)\leq2M\beta$. Also

$$ L(B)=\sum_x\chi(x)=0, $$

including when $n=1$. Thus Lemma 2 gives $L(A)=L(U)\leq2M$. Apply the same argument to $-A$ to obtain $|L(A)|\leq2M$.

An original head with negative denominator slopes becomes a head with nonnegative slopes after simultaneous input complementation. This preserves its full-cube norm and changes parity by the constant sign $(-1)^n$, so the absolute correlation bound is unchanged. Constant denominators are already covered by the zero-slope case.

Finally, sum the head bounds. The bias has zero parity correlation. A uniform signed score gap $m$ gives $Nm\leq\sum_x\chi(x)S(x)\leq2\sum_h\|\phi_h\|_\infty$, which proves the relative-margin bound.

## Exact Lean declarations

All declarations are in `formalization/HeadComplexity/Research/GlobalParityMargin.lean`, namespace `HeadComplexity.GlobalParityMargin`.

- `original_head_parity_abs_le` proves the universal head correlation bound.

- `score_parity_abs_le` proves the amplitude bound for arbitrary original scores.

- `relativeMargin_parity_le` proves the relative-margin theorem for every width.

- `signedLabel_parityFunction` identifies the Boolean target with the parity sign used in the proof.

The file additionally checks the Laplace formulas, all reciprocal-functional inequalities, the affine numerator argument, and the orientation bridge. `AuditGlobalParityMargin.lean` prints the transitive axioms of every theorem in the new module. The build and audit logs are `global-parity-margin-build.txt` and `global-parity-margin-axioms.txt`.

A subsequent cross-branch audit found an independent stronger edge-based alternation recurrence in commit `c2fa3081` on `origin/ar/027ac8030b43`, file `Results/JointFamilyParityWeakLearner.lean`. Its `jointFamily_faceAlternation_abs_le_of_edges` also implies the head sup-norm bound by bounding every edge difference by twice the norm. The proof here uses Laplace integrals and additionally supplies the original-head orientation and full relative-margin wrappers. No declaration from that branch is imported.

## The intrinsic atomic dual

This section is a written finite-dimensional convex argument. Let $\mathcal A$ contain the two constant functions $\pm1$ and every nonzero original head divided by its full-cube norm. The set is symmetric, since output negation preserves admissibility. Its closure lies in the compact cube $[-1,1]^N$. Put $C=\mathrm{conv}(\overline{\mathcal A})$.

For a Boolean sign table $f$, define the unrestricted atomic margin

$$ \Gamma_\infty(f)=\max_{v\in C}\min_x f(x)v(x). $$

Finite-dimensional minimax gives the exact dual

$$ \Gamma_\infty(f)=\min_{\lambda_x\geq0, \sum_x\lambda_x=1}\max_{a\in\overline{\mathcal A}}\sum_x\lambda_xf(x)a(x). $$

The primal equals the supremum of the requested relative margin over all finite widths. A normalized original score lies in $C$. Conversely, finite convex combinations of limit atoms can be approximated by genuine normalized heads; any strict positive gap survives sufficiently close approximation. Carathéodory controls support by $N+1$, but does not control it by the width of a separate sign representation.

For parity, the uniform dual measure gives $\Gamma_\infty(\chi)\leq2/N$ by the kernel-checked theorem above. This is a global certificate, independent of any one denominator dictionary or representation.

## Why the unconstrained atomic dual cannot settle the benchmark

Every sign table has a multilinear expansion

$$ f(x)=\sum_{S\subseteq[n]}c_S\prod_{i\in S}x_i,\qquad |c_S|\leq2^{|S|},\qquad \sum_S|c_S|\leq3^n. $$

The coefficient formula is Boolean Möbius inversion. The final inequality is $\sum_S2^{|S|}=3^n$. Every squarefree monomial is uniformly approximable by one admissible original head; this is the scope of the inherited `Atoms/UniformApproximation.lean` theorem. Therefore

$$ \Gamma_\infty(f)\geq3^{-n} $$

for every table. More concretely, applying the already kernel-checked uniform-margin compiler to these written coefficient bounds gives width $N$ and margin at least $1/(2\cdot3^n+1)$. The specialized coefficient calculation is written here, not a new Lean declaration.

Both requested test margins are eventually much smaller than $3^{-n}$. Thus no dual certificate for the width-unconstrained convex atomic problem can establish that a table fails either test margin. Such a certificate must retain the comparison-width constraint.

The first missing inequality is a sparse-separator statement: if a table has a width $H$ sign representation, must a separator with moderately bounded atomic norm exist using at most $CH$ genuine heads, or enough fewer than $nH$ heads to fit a positive-power counting budget? Convex minimax and Carathéodory alone give no such implication. Replacing $CH$ by $N+1$ loses the entire desired gain at the critical widths. This is a global sparsity gap, not a conditioning defect of one chosen representation.
