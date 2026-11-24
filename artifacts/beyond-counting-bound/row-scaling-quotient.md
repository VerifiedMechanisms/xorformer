# Variation After Row Scaling

## Statements and scope

The [symmetric normalization](symmetric-row-balancing.md) gives a positive row scaling with uniform leverage for generic fixed-denominator head spaces. This note proves three further statements.

1. Infinitesimal rebalancing is an orthogonal projection in the tangent space of a Grassmannian. It removes a nonnegative, explicitly computable part of the squared variation.

2. If every denominator lies in one fixed affine pencil, the strict sign patterns of the head space are independent of the locations of the distinct denominators in that pencil.

3. This cancellation of denominator freedom does not extend to arbitrary lists. At a specified positive three-head point on four bits, all twelve denominator directions remain independent after quotienting by every infinitesimal row scaling. The same holds on an open set, including points to which symmetric normalization applies.

The first statement has twenty-four general Lean-checked matrix declarations, together with a complete written differentiation argument. The second is a complete interpolation proof. The third has a written rational-lifting proof and nine Lean-checked finite-field identities. None is an asymptotic head lower bound.

## An orthogonal formula for rebalancing

Let $P$ be the orthogonal projection onto an $r$-dimensional subspace of $\mathbb R^N$. A derivative $X$ of such projections satisfies

$$ X=X^\top,\qquad PX+XP=X,\qquad PXP=0. $$

For $t\in\mathbb R^N$, let $D_t=\mathrm{diag}(t)$. Row multiplication by $\mathrm{diag}(e^{\varepsilon t/2})$ induces the tangent vector

$$ R_P(t)=\frac12(D_tP+PD_t)-PD_tP. $$

**Proof.** If $A$ is a full-column-rank matrix spanning the subspace, its projection is $A(A^\top A)^{-1}A^\top$. Differentiate this expression at $A'=D_tA/2$. The two outer derivatives give $(D_tP+PD_t)/2$; differentiating the inverse Gram matrix gives $-PD_tP$. $\blacksquare$

Define the symmetric matrix

$$ L_{ij}=\delta_{ij}P_{ii}-P_{ij}^2. $$

It is a weighted graph Laplacian. Indeed, $P^2=P$ implies $P_{ii}=\sum_jP_{ij}^2$, and consequently

$$ t^\top Lt=\frac12\sum_{i,j}P_{ij}^2(t_i-t_j)^2\geq0,\qquad \mathrm{diag}(R_P(t))=Lt. $$

Use the Frobenius inner product on matrices. Cyclicity of trace, $PXP=0$, and $PX+XP=X$ give the exact identities

$$ \langle X,R_P(t)\rangle_F=\frac12\sum_i t_iX_{ii},\qquad \lVert R_P(t)\rVert_F^2=\frac12t^\top Lt. $$

Write $d=\mathrm{diag}(X)$. There is always a solution of $Lt=-d$. Indeed, if $La=0$, the energy identity gives $R_P(a)=0$, so the pairing identity gives $a^\top d=0$. Thus $d$ is orthogonal to the kernel of the symmetric matrix $L$ and belongs to its range. This argument includes disconnected projection graphs and singular Laplacians.

For any such solution put $Y=X+R_P(t)$. Then

$$ \mathrm{diag}(Y)=0,\qquad \langle Y,R_P(a)\rangle_F=0\text{ for every }a,\qquad \lVert Y\rVert_F^2=\lVert X\rVert_F^2-\frac12t^\top Lt. $$

Therefore $Y$ is the orthogonal projection of $X$ away from row-scaling directions and is the unique tangent matrix of least Frobenius norm in its row-scaling equivalence class. Uniqueness concerns $Y$; adding an element of $\ker L$ to $t$ does not change $R_P(t)$.

### Why this is the derivative of symmetric normalization

On a neighborhood with fixed row matroid, the basis set $\mathcal B$ is fixed. In the notation of the normalization proof, the Hessian of the determinant objective is the covariance matrix of the random basis indicator under its strictly positive basis distribution. Its kernel is the orthogonal complement of the span of $\mathbf1_B-c$. Consequently the Hessian is positive definite on that span. The implicit function theorem gives a smooth local minimizing row scale in this gauge.

At a balanced point, hold its current row scale fixed while differentiating the underlying head matrix, obtaining $X$. Differentiating the additional balancing scale contributes $R_P(t)$. Since the diagonal of the final projection is fixed, its derivative is exactly the matrix $Y$ above.

The preexisting row scale depends on the denominators. The contraction formula does not bound $X$ uniformly in the original coefficient coordinates and does not supply an entropy bound.

### Equivalent information identity

Let $\pi_B$ be the squared-minor basis probabilities of the currently scaled matrix. For a smooth path within a fixed row-matroid stratum, let $\xi_B$ be the derivative of the logarithm of its unnormalized squared minor, with the row scale initially held fixed. Center $\xi$ by its mean. Differentiating the balanced probabilities gives

$$ g_B=\xi_B-\mathbb E_\pi\xi+\langle\mathbf1_B-c,t\rangle,\qquad \mathbb E_\pi[(\mathbf1_B-c)g_B]=0. $$

Thus $g$ is the orthogonal residual after projecting the centered score onto the linear span of centered basis indicators. Pythagoras gives

$$ \mathbb E_\pi g_B^2=\mathrm{Var}_\pi(\xi_B)-t^\top Lt. $$

For completeness, the basis-indicator covariance equals $L$. Differentiate the log determinant twice with respect to row log weights. The first derivative is $P_{ii}$ and its derivative in direction $t$ is $(Lt)_i$, which proves the covariance formula.

The squared-minor Fisher information is twice the squared Frobenius norm of the projection derivative. One proof uses an orthonormal frame $Q$ and its unit exterior product. At a point rotate coordinates so that $Q$ is the first $r$ coordinate vectors. The derivative outside their span is a matrix $B$, the exterior-product derivative has squared norm $\lVert B\rVert_F^2$, and the projection derivative has squared norm $2\lVert B\rVert_F^2$. Differentiating the probabilities, which are squares of the exterior-product coordinates, gives Fisher information $4\lVert B\rVert_F^2$. Coordinates identically zero on the stratum have zero derivative and contribute zero. This recovers the same contraction identity.

## Exact elimination of pole locations in a pencil

Let $E,F$ be independent affine forms, and let

$$ D_h=\alpha_hE+\beta_hF\qquad(1\leq h\leq H) $$

be pairwise nonproportional forms, each strictly positive on the cube. Put $Q=\prod_hD_h$. The fixed-denominator head space is

$$ U_D=Q^{-1}K,\qquad K=L\cdot\mathrm{span}\lbrace E^{H-1-j}F^j:0\leq j\leq H-1\rbrace. $$

**Proof.** The binary forms $G_h(E,F)=\prod_{g\neq h}D_g$ are linearly independent. Evaluate a proposed relation at $(E,F)=(-\beta_h,\alpha_h)$. Every term except $G_h$ vanishes, while $G_h$ is nonzero because no other denominator is proportional to $D_h$. There are $H$ forms, which is the dimension of the binary forms of degree $H-1$, so they form a basis. Multiplying a head sum by $Q$ gives $\sum_hA_hG_h$ with arbitrary affine $A_h$. Its span is exactly $K$. Evaluation on the finite cube preserves this equality of spans, even if some polynomial directions coincide there. $\blacksquare$

Since $Q$ is positive on every cube input, the strict signs available in $U_D$ are exactly those available in $K$. Thus they depend on the pencil and the number of distinct denominators, but not on the locations of these denominators within that pencil.

For two heads, every independent denominator pair belongs to a unique pencil. The space of pencils in the $(n+1)$-dimensional affine-form space has dimension $2(n-1)$. Accordingly the denominator-space variation modulo row scaling has dimension at most $2(n-1)$, rather than $2n$. This does not assert an analogous reduction for arbitrary larger lists.

## Twelve directions survive for three heads

Use four bits, indexed from zero, with the positive slope vectors

$$ b_1=(19,3,1,20),\qquad b_2=(1,19,2,5),\qquad b_3=(16,15,3,8),\qquad D_h(x)=1+b_h\cdot x. $$

Index the sixteen cube points by their binary integers. Let $A$ be the $16\times13$ rational matrix with columns $1$ and $x_i/D_h(x)$, ordered by head and then bit. Let $B=\lbrace0,\ldots,12\rbrace$ and $E=\lbrace13,14,15\rbrace$. Its square submatrix $A_B$ is nonsingular. Define the rational $3\times16$ matrix $T$ by

$$ T_E=I_3,\qquad T_B=-A_EA_B^{-1}. $$

Then $TA=0$ and $\ker T=\mathrm{im}(A)$. If $\dot A$ is a variation of the evaluation matrix, $T\dot A$ represents its subspace tangent: it vanishes exactly when every derivative column belongs to the original column space.

For a row-scaling parameter $x$, the corresponding matrix is $T e_x e_x^\top A$. Their sum over all sixteen rows is zero, so their span has dimension at most fifteen. For a denominator parameter $b_{h,j}$, its matrix is $T\partial_{b_{h,j}}A$, where the only nonzero derivative columns are

$$ \partial_{b_{h,j}}\left(\frac{x_i}{D_h(x)}\right)=-\frac{x_ix_j}{D_h(x)^2}. $$

Form a $39\times27$ matrix $C$ by flattening, in row-major order, the fifteen row-scaling matrices for rows zero through fourteen, followed by the twelve denominator-derivative matrices. The first twenty-seven rows of $C$ form a nonsingular square matrix. Therefore the fifteen row-scaling directions and the twelve denominator directions are jointly independent. Since all sixteen row-scaling directions sum to zero, this accounts for every row-scaling direction. The denominator quotient rank is exactly twelve.

### Exact certificate and rational lift

The certificate works modulo $101$. Every displayed positive denominator is less than $101$. The file `RowScalingQuotient.lean` checks the literal evaluation formulas and an inverse of the thirteen-row evaluation minor. Hence $A_B$ is nonsingular over the rationals, its inverse has denominators not divisible by $101$, and reduction of $T$ is defined.

A separate checked table gives the inverses of all denominators, so the derivative formula uses certified reciprocal values. The file also checks that its stored normal matrix annihilates the evaluation matrix and is the identity on the last three columns. Since the first thirteen evaluation rows are independent, these identities uniquely specify the reduction of $T$. It then checks that the stored twenty-seven-row matrix is exactly the matrix of the row-scaling and derivative formulas above, and checks a left inverse of the square selected matrix by the identity `selectedInverse * selected = 1`. Its determinant is therefore nonzero modulo $101$, and the rational determinant is nonzero as well.

All these nonvanishing conditions persist on an open neighborhood of the displayed real parameters. This neighborhood meets the open dense stratum from the symmetric-normalization theorem. A fixed positive row scaling is a diffeomorphism of the Grassmannian preserving its row-scaling orbits. Quotient tangent rank is therefore unchanged by balancing. Consequently there are uniformly balanced positive three-head spaces whose denominator variation still has all twelve independent directions.

This is a finite example, not an asymptotic claim. It excludes a proposed blanket collapse of denominator degrees of freedom under row normalization. Counting the full normalized family remains open.

## Verification and literature scope

`certify_row_scaling_quotient.py` constructs the actual rational matrices before reducing them modulo the prime. Nine declarations in `HeadComplexity.RowScalingQuotient` check positivity, evaluations, inverse identities, the annihilator, and the literal selected-matrix formula. The rational lifting, tangent-space interpretation, information identity, and general pencil theorem are written proofs, not end-to-end Lean theorems.

`RowScalingGeometry.lean` separately proves twenty-four general matrix declarations over an arbitrary finite index type. In particular, `exists_rebalancing` proves solvability without an invertibility assumption, `rebalanced_energy` proves the exact norm decrease, `rebalanced_orthogonal` and `rebalanced_minimal` prove least norm, and `rebalanced_unique` proves uniqueness of the resulting tangent matrix. Their printed axiom dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`. Differentiating the projection formula, smooth local dependence of the balancing scale, and the probability interpretation remain written analytic arguments.

`verify_row_scaling_geometry.py` independently checks the differential identities by exact rational arithmetic on twelve variations of a six-row Vandermonde space. It evaluates all squared-minor probabilities, the graph Laplacian, the balancing correction, and both information identities. It also checks that two different positive three-denominator lists in the displayed two-dimensional span have the same thirteen-dimensional cleared space on four bits. These are finite replays of the written proofs.

`experiments/quotient-tangent-ranks.json` records nineteen further finite-field computations through six bits. Their role is exploratory. The rigorous finite example above uses its own rational construction and kernel-checked certificate.

The recent [Li, Reichman, Williams, and Wu report, Theorems 1.4, 1.5, and 6.5](https://eccc.weizmann.ac.il/report/2026/311/download/), does not supply the remaining uniform bound. Its stronger random-restriction results assume bounded weights and noticeable separation. Its unrestricted depth-two selection bound retains a logarithm, and its weight normalization comes from a general semialgebraic rational-point estimate. Neither changes the gap for arbitrary signed affine-ratio sums on the full cube. No transfer between these architectures is assumed here.
