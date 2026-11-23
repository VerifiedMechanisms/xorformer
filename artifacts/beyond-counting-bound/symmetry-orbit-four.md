# Twenty-Four Strict Maxima of One Positive Head Functional

## Statement

On the seven-bit cube, one strictly positive linear functional has at least 24 distinct nondegenerate strict local maxima on the image of normalized, full affine one-head tables with strictly positive denominator slopes. The tables can all be chosen strictly positive. This extends the [six-point certificate](symmetry-orbit-maxima.md); it is not an asymptotic maximum count or a head-complexity lower bound.

## Exact data

Use coordinates numbered zero through six, and set

$$ D(x)=1+11x_0+7x_1+375x_2+33x_3+6x_4+5240x_5+266x_6, $$

$$ A(x)=15-15x_0-12x_1-837x_2-48x_3-66x_4+14862x_5-2642x_6,\qquad T(x)=A(x)/D(x). $$

The file `symmetry-orbit-four-certificate.json` specifies a rational functional $\mu$, invariant under every permutation of the first four coordinates. Its 40 orbit values are indexed by

$$ x_0+x_1+x_2+x_3+5(x_4+2x_5+4x_6). $$

All values in the certificate are exact rational numbers. A small floating-point gradient is not used to certify stationarity. Independent rational verification recomputes all 128 table entries, all 15 gradient coordinates, the full Hessian, its positive diagonal factorization, and the inverse of the triangular factor.

## Stationarity and second variation

For arbitrary nearby affine numerator coefficients $a$ and denominator slopes $b$, with denominator constant fixed to one, put $Y(x)=(1,x)$ and

$$ T_{a,b}(x)=\frac{a\cdot Y(x)}{1+b\cdot x},\qquad E(a,b)=\sum_x\bigl(T_{a,b}(x)-\mu_x\bigr)^2. $$

The Jacobian columns are $Y_i/D$ and $-Tx_j/D$. The certificate checks

$$ J^\top(T-\mu)=0. $$

Half the Hessian of $E$ has blocks

$$ M_{aa,ij}=\sum_x\frac{Y_iY_j}{D^2},\qquad M_{ab,ij}=\sum_x\frac{(\mu-2T)Y_ix_j}{D^2},\qquad M_{bb,ij}=\sum_x\frac{(3T^2-2\mu T)x_ix_j}{D^2}. $$

These formulas follow by differentiating each square in $E$. The saved rational matrices satisfy $M=L\mathrm{diag}(p)L^\top$, $L^{-1}L=I$, and $p_i\gt0$ for all 15 indices. Thus $M$ is positive definite over the reals. The denominator coefficients stay strictly positive in a neighborhood, so the score map and loss are smooth there. Stationarity and the positive definite Hessian prove a nondegenerate strict local minimum of the full loss, including every numerator and denominator direction.

## The table image has local coordinates

The origin and singleton values, together with the denominator slopes, determine every numerator coefficient. If $s_0=T(0)$, $s_i=T(e_i)$, and $s_{ij}=T(e_i+e_j)$, then

$$ (s_{ij}-s_i)b_i+(s_{ij}-s_j)b_j=s_i+s_j-s_0-s_{ij}. $$

Use the seven pairs $(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2)$. Their coefficient matrix has exact determinant

$$ -\frac{40258767308949}{694701086727678160}\neq0. $$

Consequently these table entries recover $b$ smoothly near the displayed table, then recover $a_i=(1+b_i)s_i-s_0$ and $a_0=s_0$. This is a local inverse of the score map, so its image is a smooth embedded 15-dimensional manifold near $T$. There is no unexamined parameter redundancy in the preceding Hessian argument.

## Passing to the unit sphere

The numerator scaling direction belongs to the model. Stationarity in that direction gives the checked identity

$$ \mu\cdot T=\|T\|^2\gt0. $$

Write nearby nonzero image tables as $rU$, where $r\gt0$ and $\|U\|=1$. Radial scaling is a smooth local product coordinate because its derivative has nonzero component in the radial direction. Put $h(U)=\mu\cdot U$. The loss becomes

$$ E(r,U)=r^2-2rh(U)+\|\mu\|^2. $$

At the displayed stationary point, $r=h(U)\gt0$. Eliminating the radial coordinate gives the reduced loss $\|\mu\|^2-h(U)^2$. Its Hessian is the positive definite Schur complement of the full loss Hessian. Since the first derivative of $h$ vanishes there, this reduced Hessian is $-2h(U)\nabla^2h(U)$. Therefore $h$ has negative definite Hessian on the 14-dimensional normalized image: the point is a nondegenerate strict local maximum.

## Symmetry, distinctness, and positivity

All 24 permutations of the first four cube coordinates preserve $\mu$, the Euclidean table norm, and the admissible table family. They therefore carry the proved maximum to maxima with the same nondegeneracy. Exact table comparison verifies that all 24 resulting tables are different, and exact norm comparison verifies that their norms agree. Normalization consequently preserves distinctness.

Finally replace $\mu$ by $\mu+100$ and every table by $T+100$. On coefficient space the replacement is the invertible affine map

$$ a_0'=a_0+100,\qquad a_i'=a_i+100b_i. $$

It leaves the residual $T-\mu$, and hence the loss, unchanged after this change of coordinates. It commutes with coordinate permutations. Every entry of every translated table and of the translated functional is strictly positive, as checked exactly. The local loss minima, local image inverses, and radial argument therefore apply again to this translated family. The 24 translated tables have equal norms and remain distinct, giving the claimed positive example. $\blacksquare$

The untranslated table has a zero entry; the four different positive supports recorded during the search are not asserted to be four strict Boolean classifiers. After translation all 24 tables have the same positive labels. Thus the example supplies no multiplicity of hard Boolean functions.

## Verification scope

`verify_symmetry_orbit_four.py` is an independent rational replay. `SymmetryOrbitFour.lean` checks 13 finite declarations, including stationarity, all orbit tables, the rational Hessian factorization, real positive definiteness, the reconstruction determinant, and positive translation. The smooth local-maximum deduction is the written proof above. No full asymptotic claim is inferred from this finite certificate.
