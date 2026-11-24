# Exact classification of two-head Boolean zero relations

## Scope and status

This note classifies all linear dependencies between two affine-numerator head spaces on a Boolean cube with at least four coordinates. It gives a precise example of how rank defects away from collisions can be charged to a small parameter family. It does not classify dependencies among arbitrarily many heads, prove a margin repair theorem, or improve the unrestricted worst-case head lower bound.

The proof is an elementary written argument using the rank of a quadratic form. The companion script checks representative cases by exact rational arithmetic. The auxiliary Lean modules `AffineBooleanZeroDivisors.lean` and `TwoHeadBooleanDegeneracy.lean` verify the coefficientwise zero-divisor classification, the rank-four diagonal restriction, the factorization at a zero diagonal entry, and the positive rescaling with at most two remaining denominator slopes when there are at least five coordinates. The dimension-four extension, uniqueness, and full intersection-dimension statement below remain written proofs. No original worst-case lower-bound theorem is formalized here.

## Statement

Let $n\geq4$. Let $B,C$ be affine forms, strictly positive on $X=\lbrace0,1\rbrace^n$, with every spatial slope nonzero. Their slopes need not have a coherent sign for the theorem. Assume that $B$ and $C$ are not proportional. Define the affine-numerator table spaces

$$ U_B=\lbrace(A(x)/B(x))_{x\in X}: A\text{ is affine}\rbrace,\qquad U_C=\lbrace(D(x)/C(x))_{x\in X}:D\text{ is affine}\rbrace. $$

Both spaces contain the constant table. Introduce the finite list of affine forms

$$ \mathcal G_n=\lbrace x_i, x_i-1:1\leq i\leq n\rbrace\cup\lbrace x_i-x_j, x_i+x_j-1:1\leq i\lt j\leq n\rbrace. $$

For each form $G_0$ on this list, define its complementary form $F_0$ by pairing $x_i$ with $x_i-1$ and pairing $x_i-x_j$ with $x_i+x_j-1$. Each paired product vanishes on the whole Boolean cube.

**Theorem.** Exactly one of the following cases holds.

1. There are no real numbers $\lambda\gt0$ and $\alpha\neq0$ and no $G_0\in\mathcal G_n$ such that $C-\lambda B=\alpha G_0$. Then $U_B\cap U_C$ consists exactly of the constant tables and $\dim(U_B+U_C)=2n+1$.

2. Such $\lambda,\alpha,G_0$ exist. The direction of $G_0$ and the scalar $\lambda$ are unique. If $F_0$ is its complementary form, then

$$ U_B\cap U_C=\mathrm{span}\lbrace1,F_0/B\rbrace,\qquad \dim(U_B+U_C)=2n. $$

More explicitly, every affine pair $A,D$ satisfying $A/B+D/C=0$ on $X$ has the form

$$ A=\kappa B+\mu F_0,\qquad D=-\kappa C-\lambda\mu F_0 $$

for real $\kappa,\mu$. In the first case only the solutions with $\mu=0$ occur.

In the original coherent-slope model, nonproportional denominators of opposite slope orientations are always in the first case. Indeed, the second case would make their slopes proportional with a positive factor on at least one unaffected coordinate.

## Proof

### Lemma 1. Affine Boolean zero divisors

Suppose nonzero affine forms $F,G$ satisfy $F(x)G(x)=0$ at every Boolean vertex. Then, up to separate nonzero scalar factors and exchanging $F,G$, they are either $x_i,x_i-1$ or $x_i-x_j,x_i+x_j-1$ for distinct coordinates $i,j$.

**Proof.** A nonconstant affine form with a nonzero slope in coordinate $i$ has at most one zero in each pair of vertices differing only in coordinate $i$. Hence it vanishes at at most half the vertices. A nonzero constant has no zeros. Since the zero sets of $F,G$ cover the cube, both zero sets have exactly half the vertices and they are disjoint.

If an affine form with exactly half the vertices as zeros had at least three nonzero slopes, choose one of them, $a_i$. For every assignment to the other coordinates, exactly one of the two values obtained by varying $x_i$ must be zero. Thus the affine form in the remaining coordinates takes values only in $\lbrace0,-a_i\rbrace$. Two remaining nonzero slopes already produce at least three distinct values on their two-dimensional face: the four values are $t,t+a_j,t+a_k,t+a_j+a_k$, and cannot all belong to a two-element set when $a_j,a_k$ are both nonzero. This is a contradiction.

Thus each form has at most two nonzero slopes. With one slope, its half-cube zero set is a coordinate face and the complementary half-cube is the opposite face. With two slopes, the two zero vertices in that coordinate square must be a diagonal pair; the two forms are proportional to $x_i-x_j$ and $x_i+x_j-1$. This proves the lemma. $\blacksquare$

### Lemma 2. A quadratic rank restriction

Write the coefficient vectors of the spatial parts of $A,D,B,C$ as $a,d,b,c$, respectively. If $AC+DB$ vanishes on the cube, then there are real numbers $k_i$ such that

$$ P=AC+DB=\sum_{i=1}^n k_i(x_i^2-x_i). $$

The symmetric matrix of the spatial quadratic part is

$$ Q=\frac12(ac^{\top}+ca^{\top}+db^{\top}+bd^{\top})=\mathrm{diag}(k_1,\ldots,k_n). $$

Consequently at most four of the $k_i$ are nonzero. Under the positivity hypotheses and $n\geq4$, at least one $k_j$ is zero.

**Proof.** The multilinear reduction of a quadratic polynomial that vanishes on every Boolean vertex is zero: successively evaluating at the zero vector, singletons, and pairs forces its constant, linear, and mixed quadratic coefficients to vanish. Thus the only possible terms in the unreduced polynomial have the displayed form. Each of the four outer products has rank at most one, so $Q$ has rank at most four. A diagonal matrix has rank equal to its number of nonzero diagonal entries.

Only the case $n=4$ with all four $k_i$ nonzero needs an additional argument. Homogenize using a coordinate $x_0$. The matrix $\widehat Q$ of $P=\sum_i k_i(x_i^2-x_0x_i)$ has spatial diagonal $k_i$, first row entries $\widehat Q_{0i}=-k_i/2$, and $\widehat Q_{00}=0$. It has rank at most four because $P=AC+DB$, and rank at least four because its spatial diagonal is invertible. Its determinant is

$$ \det\widehat Q=-\frac14\left(\sum_i k_i\right)\prod_i k_i. $$

Hence $\sum_i k_i=0$, and $r=(1,1/2,1/2,1/2,1/2)^{\top}$ is in its kernel. Let $T$ have as columns the homogeneous coefficient vectors of $A,C,D,B$. Then $\widehat Q=TJT^{\top}$, where $J$ consists of two invertible two-by-two off-diagonal blocks with entries $1/2$. Since $\widehat Q$ has rank four, $T$ has rank four and is injective. Thus $\widehat Qr=0$ forces $T^{\top}r=0$. In particular $B(1/2,1/2,1/2,1/2)=0$, contradicting positivity at the cube vertices and affinity. This excludes the remaining case. $\blacksquare$

### Lemma 3. A nonzero relation factors through a Boolean zero divisor

Suppose $P=AC+DB$ vanishes on $X$ and is not the zero polynomial. Then there are real numbers $\lambda,\kappa$ such that

$$ P=(A-\kappa B)(C-\lambda B). $$

Both factors are nonzero affine forms.

**Proof.** Let $T=\lbrace i:k_i\neq0\rbrace$ in Lemma 2. This set is nonempty and has at most four elements. Lemma 2 gives an index $j\notin T$. Every coefficient involving $x_j$ in the polynomial $P=\sum_i k_i(x_i^2-x_i)$ is zero.

Put $\kappa=a_j/b_j$ and $\lambda=c_j/b_j$. These are defined because $b_j\neq0$. The zero coefficient of $x_j^2$ says $a_jc_j+d_jb_j=0$, so $d_j=-\kappa c_j$. Therefore the affine forms

$$ U=A-\kappa B,\qquad V=D+\kappa C $$

both have zero $x_j$ slope, and $P=UC+VB$. Regard this as a polynomial in $x_j$ with coefficients in the other variables. Its coefficient of $x_j$ is the affine form $c_jU+b_jV$, which must be zero. Hence $V=-\lambda U$, and

$$ P=U(C-\lambda B)=(A-\kappa B)(C-\lambda B). $$

The polynomial $P$ is nonzero, so both factors are nonzero. $\blacksquare$

### Completion of the theorem

If $P$ is the zero polynomial, then $AC=-DB$. Two nonproportional nonconstant affine forms are relatively prime in the real polynomial ring. Thus $B$ divides $A$, forcing $A=\kappa B$ because both are affine. It follows that $D=-\kappa C$.

If $P$ is nonzero, Lemma 3 and Lemma 1 show that $C-\lambda B$ is proportional to some $G_0\in\mathcal G_n$, and $A-\kappa B$ is proportional to the complementary $F_0$. At any Boolean vertex where $G_0$ vanishes, positivity of $B,C$ gives $\lambda=C(x)/B(x)\gt0$. Substituting in $D+\lambda A=-\kappa(C-\lambda B)$ gives the displayed formula for $D$.

Conversely, that formula for $A,D$ clears to $\mu F_0(C-\lambda B)=\mu\alpha F_0G_0$, which vanishes on the cube. Thus all the listed pairs are genuine zero relations.

To prove uniqueness, suppose two different values $\lambda_1,\lambda_2$ were possible. Subtracting the two identities expresses $(\lambda_1-\lambda_2)B$ as a linear combination of two forms in $\mathcal G_n$. Their spatial supports together use at most four coordinates. For $n\geq5$, a coordinate outside that union contradicts the nonzero slopes of $B$. For $n=4$, the only remaining possibility is that the two supports are disjoint pairs covering all coordinates. The two forms then have a common Boolean zero, obtained by choosing a zero on each pair independently. The displayed expression would force $B$ to vanish there, again a contradiction. Thus $\lambda_1=\lambda_2$. Their difference directions are then equal. The complementary factor is unique up to scale by Lemma 1.

Each head space has dimension $n+1$, because division by a positive table is injective on affine forms. In the exceptional case, $F_0/B$ is not constant: otherwise $F_0$ would be proportional to $B$, although $F_0$ has zero vertices and $B$ is strictly positive. The intersection consequently has dimension two. In the other case it has dimension one. The dimension formula for a sum of two subspaces proves the claimed ranks. $\blacksquare$

## Parameter count and limitation

Normalize the constant coefficients of $B,C$ to one. This is permitted because both forms are positive at the zero vertex. The full pair of denominators has $2n$ slope parameters. For each fixed $G_0\in\mathcal G_n$, the exceptional family $C=\lambda B+\alpha G_0$ has at most $n+1$ parameters: the $n$ slopes of $B$ and the scalar $\alpha$, while the constant-coefficient equality determines $\lambda$. There are $n(n+1)$ listed forms. Thus the noncollision two-head rank-defect locus lies in a finite union of families of codimension at least $n-1$.

This is a genuine codimension saving for two heads. It does not establish an analogous saving for large collective dependencies. For example, distinct denominators in a common pencil can have a zero relation involving many heads even when no pair has an extra dependency. Nor does avoiding the exact defect locus give a quantitative lower singular-value bound without controlling distance to that locus. The needed uniform argument at exponentially large widths remains open.


## Sharpness of the dimension threshold

The theorem fails for three coordinates, even with strictly positive denominator coefficients. Set

$$ B=1+x_1+x_2+3x_3,\qquad C=4+x_1+2x_2+3x_3,\qquad A=-14-18x_1-13x_2-18x_3,\qquad D=56+24x_1+25x_2. $$

Direct expansion gives

$$ AC+DB=6(x_1^2-x_1)-(x_2^2-x_2)-54(x_3^2-x_3). $$

Thus $A/B+D/C$ vanishes on all eight vertices, although the cleared polynomial is nonzero. No $C-\lambda B$ is proportional to one of the canonical forms. To check this, its slopes are $(1-\lambda,2-\lambda,3-3\lambda)$. For at most two slopes to be nonzero, $\lambda$ must be $1$ or $2$. At $\lambda=1$ the form is $3+x_2$, which has no Boolean zero. At $\lambda=2$ it is $2-x_1-3x_3$, which likewise has no Boolean zero. The constant and all slopes of both denominators are strictly positive, so this is an original-model example. The dimension threshold $n\geq4$ is therefore sharp.
