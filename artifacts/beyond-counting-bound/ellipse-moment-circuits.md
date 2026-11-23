# Elliptic Moment Circuits That Resist Collinear Replacement

## Statement

Write $E$ for the ellipse $x^2+xy+y^2=1$, and let $V_k$ be the restrictions to $E$ of the polynomials spanned by

$$ 1,\quad x^j,\quad y^j,\quad (x+y)^j\qquad(1\leq j\leq k). $$

**Theorem 1.** For every $k\geq0$,

$$ \dim V_k=1+2k-\lfloor k/3\rfloor. $$

For every $k\geq3$, there are

$$ H=2k+2-\lfloor k/3\rfloor $$

distinct positive rational velocity vectors in two dimensions, and nonzero integer residues, such that their Boolean moments through degree $k$ form a circuit and their reciprocal sum has exact contact order $k+1$. The velocity projections in the three nonzero Boolean directions are all distinct, and the residues can all be distinct. Consequently the reciprocal families have no persistent linear identity. Their projection data have no finite constant-residue representation supported on an affine line.

All equivalences in the last sentence concern the entire deformation family with the same fixed positive base denominator, not the sign table at a fixed parameter. No asymptotic Boolean lower bound is asserted.

## Harmonic dimension calculation

Parametrize the ellipse by

$$ x=\frac2{\sqrt3}\cos\theta,\qquad y=\frac2{\sqrt3}\cos(\theta-2\pi/3),\qquad x+y=\frac2{\sqrt3}\cos(\theta-\pi/3). $$

The identity $x^2+xy+y^2=1$ follows by expansion. The Chebyshev recurrence $T_0(t)=1$, $T_1(t)=t$, and $T_{j+1}(t)=2tT_j(t)-T_{j-1}(t)$ gives $T_j(\cos\theta)=\cos(j\theta)$. Its leading coefficient is nonzero, so polynomials of degree at most $k$ in any one of the three linear forms span the corresponding harmonics through frequency $k$.

At frequency $j$, the three available functions are

$$ \cos(j\theta),\qquad \cos(j\theta-j\pi/3),\qquad \cos(j\theta-2j\pi/3). $$

If $3$ divides $j$, these span the single function $\cos(j\theta)$. Otherwise the first two span both the sine and cosine of frequency $j$, since $\sin(j\pi/3)\neq0$. Different frequencies are linearly independent, as follows for example by integrating products over one period. The constant contributes one dimension. Adding the frequency contributions proves the formula.

## Rational circuits and exact contact

Put $d=\dim V_k$. Choose a basis of $V_k$ consisting of polynomial restrictions. Its evaluations at $d$ suitable points are independent: otherwise all evaluation functionals would lie in a proper subspace of the dual, and a nonzero basis combination would vanish everywhere. Therefore each specified $d$-point evaluation determinant, as a function of $d$ independently varying points, is not identically zero.

Take $H=d+1$ varying points on the ellipse. Outside the zero sets of these finitely many determinants, every $d$ columns are independent. Their unique relation is given by the signed $d$ by $d$ cofactors and has all coefficients nonzero. Since $V_{k+1}$ has larger dimension, also avoid the zero set of an evaluation determinant for $d+1$ independent functions chosen from $V_{k+1}$. Then this relation does not annihilate $V_{k+1}$.

One can also require pairwise distinct cofactor coefficients. For any two indices $i,j$, choose a third index $\ell$. Temporarily set the points at $i$ and $\ell$ equal, and choose the other points so that deleting column $i$ leaves a basis. The cofactor at $i$ is nonzero, while the cofactor at $j$ is zero because its minor retains the repeated columns. Hence the difference of these two cofactor functions is not identically zero. Avoid its zero set for every pair.

Finally avoid equal projections of two points in each of the three directions. Each forbidden equality is again a proper algebraic condition. A rational parametrization of the ellipse is

$$ x(t)=\frac{t^2-1}{1+t+t^2},\qquad y(t)=-\frac{t(t+2)}{1+t+t^2}. $$

It covers the ellipse except one point. All the determinant and projection conditions become nonzero rational functions of the parameters. Their finite product is not identically zero. Its nonvanishing set contains an open set, and hence a rational parameter tuple. Thus all points and cofactor residues can be rational. Clear the common residue denominator to make the residues integers.

Translate every velocity by $(2,2)$. The ellipse has both coordinates between $-2/\sqrt3$ and $2/\sqrt3$, so every translated coordinate is positive. Translation preserves the moment kernels through each degree by the binomial theorem, and preserves distinctness of each projection.

With $D(z)=1+z_1+z_2$, expand the score at the denominator collision:

$$ \sum_v\frac{c_v}{D(z)+\varepsilon v\cdot z}=\sum_{j\geq0}\frac{(-\varepsilon)^j}{D(z)^{j+1}}\sum_v c_v(v\cdot z)^j. $$

The moments through $k$ vanish at every Boolean input, and some degree $k+1$ moment does not. This proves exact contact order $k+1$. All denominator slopes are $1+\varepsilon v_i\gt0$ for nonnegative $\varepsilon$.

At the input $z=(1,0)$ the projections are distinct and positive. Thus the reciprocal terms have distinct simple poles in the deformation parameter. Nonzero residues prevent cancellation of any pole. This proves both absence of persistent linear identities and minimality of the number $H$ among representations of this entire rational family using heads with denominators affine in the deformation parameter, numerators independent of it, and a bias independent of it: fewer heads could supply fewer than $H$ poles at that one input.

## Why no collinear constant-residue replacement exists

Suppose a finite constant-residue velocity family on a line has exactly the same projection data. Combine repeated velocities and remove zero coefficients. The line cannot have constant first coordinate, since the target has $H$ distinct nonzero first-coordinate projection masses. Therefore projection onto the first coordinate is injective on that line, and the proposed family has exactly $H$ effective points with the same first coordinates and residues as the original family.

The same argument applies to the second coordinate. Since all residues are distinct, they identify the matching between the two coordinate projection lists uniquely. The proposed family must therefore consist of exactly the original points. This is impossible: a line meets the nondegenerate ellipse in at most two points, whereas $H\geq7$.

Equality of persistent reciprocal families with the same base implies equality of these projection data by residues at their distinct poles. This completes the proof of Theorem 1. $\blacksquare$

## A seven-point exact certificate

Take the parameters $t=4,5,\ldots,10$ in the rational parametrization and translate by $(2,2)$. The following positive velocities and integer residues give the case $k=3$:

| First coordinate | Second coordinate | Residue |
| --- | --- | --- |
| $19/7$ | $6/7$ | $9030651$ |
| $86/31$ | $27/31$ | $-139451671$ |
| $121/43$ | $38/43$ | $773603110$ |
| $54/19$ | $17/19$ | $-2053378830$ |
| $209/73$ | $66/73$ | $2822318335$ |
| $262/91$ | $83/91$ | $-1938507571$ |
| $107/37$ | $34/37$ | $526385976$ |

The degree-at-most-three moment matrix has rank six, with the displayed full-support null vector. Adding fourth moments raises its rank to seven. The three fourth moments, in directions $(1,0),(0,1),(1,1)$, are respectively

$$ \frac{90613464360}{1405678729},\qquad \frac{15464511960}{1405678729},\qquad -\frac{106077976320}{1405678729}. $$

Exact rational inverses of selected moment submatrices certify the ranks. All residues and all projections in each direction are pairwise distinct. The degree-three relation is therefore a circuit, has no persistent identity, and cannot be moved to a line without changing its persistent projection data.

## Scope of the obstruction

The [formal-power circuit bound of Li and Liu](https://arxiv.org/html/2606.24349v1) would require at least $2k+2$ terms for formal affine degree $k$ moment circuits spanning two dimensions. The construction has $\lfloor k/3\rfloor$ fewer terms. Thus even minimization of persistent support and exclusion of collinear representatives do not justify that exact formal-to-Boolean transfer. The mechanism is a missing harmonic at each frequency divisible by three, rather than a removable persistent subidentity.

This does not disprove every weaker contact estimate, and it supplies no count of unrestricted classification chambers. The comparisons concern constant residues and one common linear denominator deformation. They do not establish a lower bound for arbitrary affine numerators at a fixed target-dependent parameter point. In particular, this two-bit construction is not presented as a difficult Boolean function.

## Verification scope

The dimension formula and arbitrary-degree existence theorem have complete written proofs. The seven-point certificate is checked with exact rational arithmetic and finite Lean declarations for its moments, inverse matrices, coordinate positivity, and distinctness. The general harmonic argument and existence proof are not claimed as Lean declarations.
