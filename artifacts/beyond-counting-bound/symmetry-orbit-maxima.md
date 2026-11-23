# Six Strict Maxima from a Permutation Orbit

## Statement and scope

On the six-bit cube, the normalized family of admissible full affine heads has a linear functional with at least six distinct nondegenerate strict local maxima. Its coefficients can all be chosen strictly positive, and all six normalized tables can also be chosen strictly positive.

The construction uses an exact stationary point of a squared-distance objective, a positive definite full parameter Hessian, and invariance under all permutations of three input coordinates. It strengthens the earlier two-point example. It gives no growing asymptotic count and no lower bound for the worst-case head complexity. The selected unboundedness target remains open.

## Exact data

For $x\in\lbrace0,1\rbrace^6$, put $Y_x=(1,x_0,\ldots,x_5)$ and

$$ a=(-140,-294,-921,-15,1629,327,87),\qquad b=(15,69,1,288,15,363),\qquad D_x=4+b^\top x,\qquad T_x=\frac{a^\top Y_x}{D_x}. $$

The denominator constant is fixed at four in the following parameter chart. Dividing both numerator and denominator by four gives the manuscript's usual normalized positive denominator.

The rational functional coefficients are specified by the 32-entry list `orbit_mu` in [the exact certificate](symmetry-orbit-maxima-certificate.json). If $v=\sum_{i=0}^5 2^i x_i$, define

$$ j(x)=x_0+x_1+x_2+4(x_3+2x_4+4x_5),\qquad \mu_x=\mathrm{orbit\_mu}_{j(x)}. $$

This formula makes the functional invariant under the symmetric group on the first three coordinates. Every entry of the certificate is an explicit rational number. No decimal tolerance or numerical assertion is part of its verification.

Let $J$ be the 64 by 13 Jacobian of the table map in its seven numerator and six denominator parameters. Let $E(a,b)=\sum_x(T_x-\mu_x)^2$. Its derivatives are

$$ J_{x,a_i}=\frac{Y_{xi}}{D_x},\qquad J_{x,b_j}=-\frac{T_xx_j}{D_x},\qquad \frac12\nabla E=J^\top(T-\mu). $$

Writing $M=\nabla^2E/2$, its three blocks are

$$ M_{a_i,a_j}=\sum_x\frac{Y_{xi}Y_{xj}}{D_x^2},\qquad M_{a_i,b_j}=\sum_x\frac{(\mu_x-2T_x)Y_{xi}x_j}{D_x^2},\qquad M_{b_i,b_j}=\sum_x\frac{(3T_x^2-2\mu_xT_x)x_ix_j}{D_x^2}. $$

The certificate gives explicit rational matrices $L,K$ and positive rational numbers $p_1,\ldots,p_{13}$. Direct exact arithmetic verifies

$$ J^\top(T-\mu)=0,\qquad M=L\mathrm{diag}(p)L^\top,\qquad KL=I,\qquad p_i\gt0. $$

Consequently $M$ is positive definite. The stationary point is a nondegenerate strict local minimum of $E$ in the entire 13-dimensional head parameter chart, including every affine numerator coefficient.

## Local image regularity

The head parameters are locally recoverable from table entries. Write $s_0=T(0)$ and $s_i=T(e_i)$. The origin and singleton entries give

$$ a_0=4s_0,\qquad a_i=(4+b_i)s_i-a_0. $$

For each pair $i,j$, the pair entry $s_{ij}=T(e_i+e_j)$ therefore satisfies

$$ (s_{ij}-s_i)b_i+(s_{ij}-s_j)b_j=4(s_i+s_j-s_0-s_{ij}). $$

Use the six pairs listed in `reconstruction_pairs` in the certificate. Their coefficient matrix has determinant

$$ \frac{690194282359739897079}{9648514031409376640}\neq0. $$

It follows that these entries recover $b$ by an invertible linear system in a neighborhood of the displayed table; the preceding singleton formulas then recover $a$. This is a smooth local inverse. The head-table image is thus a smooth embedded 13-dimensional manifold near this point.

## From squared distance to a normalized maximum

The head-table family is locally closed under positive scalar multiplication: scale its numerator and leave its denominator fixed. Differentiating in this radial direction at the stationary point gives

$$ \langle\mu,T\rangle=\|T\|^2\gt0. $$

In local coordinates consisting of a positive radial coordinate $r$ and a unit table $U$, the squared distance is

$$ E(r,U)=r^2-2r\langle\mu,U\rangle+\|\mu\|^2. $$

Its positive radial minimizer is $r=\langle\mu,U\rangle$, throughout a sufficiently small neighborhood of the displayed point. Substitution gives the reduced objective

$$ E_{\mathrm{red}}(U)=\|\mu\|^2-\langle\mu,U\rangle^2. $$

The full Hessian of $E$ is positive definite, so its Schur complement after eliminating the radial coordinate is positive definite. The height $h(U)=\langle\mu,U\rangle$ is positive here. Stationarity of $E_{\mathrm{red}}$ gives $\nabla h=0$, and its Hessian is $-2h\nabla^2h$. Hence $\nabla^2h$ is negative definite. This proves a nondegenerate strict local maximum on the normalized image, whose dimension is twelve.

## The six-point orbit

Permute the first three numerator coefficients and the first three denominator coefficients together. The corresponding coordinate permutation preserves the cube sum norm, the positive denominator domain, and $\mu$. It therefore carries the strict local minimum of $E$ to another strict local minimum, with the same positive definiteness by coordinate congruence. The normalized-height argument applies at each point.

The six orbit tables are pairwise distinct. This is checked exactly in the certificate and in Lean; equal norms then imply that their normalized tables are also distinct. Before the positive translation below, these six tables have three distinct strict Boolean sign patterns, each itself a one-head function. This finite count does not have an asymptotic implication.

## Positive functional and positive tables

Positivity can be imposed without changing the squared-distance problem. For any constant $C$, let $D_x=4+b^\top x$ and define

$$ a'_0=a_0+4C,\qquad a'_i=a_i+Cb_i,\qquad b'=b,\qquad \mu'_x=\mu_x+C. $$

Then $T'_{a',b'}(x)=T _{a,b}(x)+C$, so

$$ \sum_x(T'_{a',b'}(x)-\mu'_x)^2=\sum_x(T_{a,b}(x)-\mu_x)^2. $$

The parameter transformation is a smooth bijection with a smooth inverse, obtained by replacing $C$ by $-C$. At a stationary point its Hessian transformation is a congruence, so positive definiteness persists. The exact certificate checks $\mu_x+100\gt0$ and $T_x+100\gt0$ for every input. Take $C=100$. The group invariance, the distinct tables, and the norm equality along their orbit persist. Applying the normalized-height argument to the translated squared-distance problem proves the positive version of the theorem. $\blacksquare$

## Audit and limitations

`verify_symmetry_orbit_maxima.py` independently constructs the derivatives from the rational table, verifies the full Hessian factorization and inverse, and checks all six input permutations. `SymmetryOrbitMaxima.lean` is the separately generated finite certificate. The calculus and local inverse argument above are written proofs, not claimed as Lean calculus declarations.

The search also produced a putative 24-point orbit near a nearly constant table. Its raw parameter gradient was small, but exact stationarity correction destroyed the positive Hessian. That candidate was rejected. Subsequent search diagnostics impose stationarity in an orthonormal tangent basis before checking curvature. No theorem is inferred from the remaining unsuccessful searches.

This example does not refute an upper bound of the form $\exp(O(n\log n))$ for maxima, does not give exponentially many classification minima, and does not establish any denominator exponent between one and two for $W(n)$.
