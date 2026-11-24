# Ordinary moment dependence and a low-dimensional base locus

## Statement and scope

Let $\Gamma$ be a finite set of $H$ distinct points of complex projective $n$-space, where $n\geq1$. Say that $\Gamma$ has the property $\mathrm{CB}(D)$ if every homogeneous polynomial of degree $D$ vanishing on all but one point of $\Gamma$ vanishes on that last point as well. Let $s\geq1$ and suppose $D\geq n(s-1)$.

Let $V_s$ be the reduced common zero locus of all homogeneous degree $s$ forms vanishing on $\Gamma$. Then:

1. Every point of $\Gamma$ lies on a positive-dimensional irreducible component of $V_s$.

2. Every irreducible component of $V_s$ has dimension $r$ satisfying

$$ \binom{s+r}{r}\leq H. $$

In particular, choosing $s$ of order $D/n$ and $D$ of order $\exp(\sqrt n)$ gives component dimension $O(\sqrt n)$ when $H\leq2^n$.

These are written mathematical results, not Lean declarations. Their hypotheses concern ordinary polynomial moments at parameter points. Vanishing only after evaluating on the Boolean cube does not imply these hypotheses. The results do not give the requested unrestricted capacity bound: the parameter cost of the varying base loci and the passage from Boolean observations to ordinary moments remain separate gaps.

## A separator for an isolated common zero

### Lemma 1. Local separator with a global degree bound

Let $f_1,\ldots,f_n\in\mathbb C[x_1,\ldots,x_n]$ have degrees at most positive integers $d_1,\ldots,d_n$. Suppose that $p$ is an isolated point of their common zero locus. There is a polynomial $g$ of degree at most $\sum_i(d_i-1)$ such that $g(p)=1$ and $g(q)=0$ at every other common zero $q$. Other components of the common zero locus may have positive dimension, and the local scheme at $p$ may be nonreduced.

**Proof.** Introduce independent variables $y_1,\ldots,y_n$. Telescoping one coordinate at a time gives divided-difference polynomials $a_{ij}(x,y)$ such that

$$ f_i(x)-f_i(y)=\sum_{j=1}^n a_{ij}(x,y)(x_j-y_j),\qquad \deg a_{ij}\leq d_i-1. $$

Put $\Delta(x,y)=\det(a_{ij}(x,y))$. Its total degree, including both sets of variables, is at most $\sum_i(d_i-1)$. Let

$$ A_p=\mathbb C[y_1,\ldots,y_n] _{\mathfrak m_p}/(f_1(y),\ldots,f_n(y)) $$

be the finite local algebra at $p$. It is a zero-dimensional local complete intersection. At $x=p$, the displayed divided-difference identity expresses the regular sequence $f_i(y)$ as a matrix times the parameters $y_j-p_j$. The distinguished-socle theorem says that $\Delta(p,y)$ is nonzero in $A_p$.

For precision, the result used here is [Kass and Wickelgren, Definition 1 and Lemma 4](https://arxiv.org/html/1608.05669#S1), which states the nonvanishing for an isolated zero, without requiring a globally finite zero locus. It applies to any matrix giving the displayed expression. Thus multiplicity at $p$ is permitted.

Choose a complex linear functional $\lambda:A_p\to\mathbb C$ with $\lambda(\Delta(p,y))=1$, and apply it coefficientwise in $y$ to define

$$ g(x)=\lambda(\Delta(x,y)). $$

This does not increase degree in $x$, and $g(p)=1$. If $q\neq p$ is any common zero, the adjugate identity in $A_p$ gives

$$ (q_j-y_j)\Delta(q,y)=0\qquad(1\leq j\leq n). $$

Some $q_j-p_j$ is nonzero. The corresponding $q_j-y_j$ has nonzero residue in the local algebra and is therefore a unit. Hence $\Delta(q,y)=0$ in $A_p$, and $g(q)=0$. This proves the lemma. $\blacksquare$

### Example 2. A double point and a line

The equations $f_1(x,y)=x^2(x-1)$ and $f_2(x,y)=y(x-1)$ have the double isolated point $(0,0)$ and the entire line $x=1$ as common zeros. In the local algebra at the origin, with variables $(a,b)$, one has $a^2=b=0$. A divided-difference determinant reduces to

$$ \Delta((x,y),(a,b))=x(1-x)+(x-1)^2a\quad\text{in }A_{(0,0)}[x,y]. $$

Taking the coefficient of $a$ gives the separator $g(x,y)=(x-1)^2$. Direct evaluation of the determinant at both variable pairs equal to the origin would give zero. The local functional is what handles the nonreduced point.

## Excluding isolated points from the base locus

Suppose $p\in\Gamma$ is isolated in $V_s$. Choose an affine chart containing every point of $\Gamma$. The dehomogenized degree $s$ forms vanishing on $\Gamma$ generate an ideal that is primary to the maximal ideal at $p$ after localization.

There exist $n$ complex linear combinations $f_1,\ldots,f_n$ of these forms whose common zero locus still isolates $p$. One may choose them successively by prime avoidance in the regular local ring at $p$: at each stage, the original ideal is not contained in any positive-dimensional minimal prime of the preceding equations. Avoiding finitely many proper linear subspaces lowers local dimension by one. Each chosen polynomial has degree at most $s$.

Lemma 1 supplies a polynomial of degree at most $n(s-1)$ which is one at $p$ and zero at every other point of $\Gamma$. Homogenizing in the chosen affine coordinate, and multiplying by that coordinate if necessary, produces a degree $D$ form separating $p$ from $\Gamma\setminus\lbrace p\rbrace$. This contradicts $\mathrm{CB}(D)$.

A point not lying on any positive-dimensional irreducible component of a projective algebraic set is an isolated point of that set. Consequently every point of $\Gamma$ lies on a positive-dimensional component of $V_s$.

## Bounding component dimension

Write $I(\Gamma)_s$ for the space of degree $s$ forms vanishing on $\Gamma$. The defining property of $V_s$ and the inclusion $\Gamma\subseteq V_s$ give the equality

$$ I(V_s)_s=I(\Gamma)_s. $$

The homogeneous Hilbert function therefore satisfies

$$ \mathrm{HF}_{V_s}(s)=\mathrm{HF}_{\Gamma}(s)\leq H. $$

Let $Y$ be an irreducible component of dimension $r$. Its homogeneous coordinate ring admits a linear homogeneous Noether normalization in $r+1$ variables. The degree $s$ monomials in those linear forms are independent, so

$$ \binom{s+r}{r}\leq\mathrm{HF}_Y(s)\leq\mathrm{HF}_{V_s}(s)\leq H. $$

This proves the claimed bound. For the stated asymptotic consequence, use $r\leq n$ and

$$ \binom{s+r}{r}=\prod_{j=1}^r\frac{s+j}{j}\geq\left(\frac{s}{n}\right)^r. $$

If $D=\lfloor\exp(\sqrt n)\rfloor$ and $s=\lfloor D/n\rfloor+1$, then $D\geq n(s-1)$, and for all sufficiently large $n$,

$$ \log(s/n)\geq\tfrac12\sqrt n,\qquad r\leq\frac{\log H}{\log(s/n)}\leq2(\log2)\sqrt n. $$

The constants are intentionally coarse. No relation between this auxiliary ordinary-moment order $D$ and an arbitrary original-model representation has been proved.

## The exact ordinary-moment hypothesis

Suppose that distinct affine parameter points $b_h\in\mathbb R^n$ admit nonzero real coefficients $c_h$, one for every point, satisfying

$$ \sum_{h=1}^H c_h P(b_h)=0\qquad\text{for every polynomial }P\text{ of degree at most }D. $$

Then their projective closures in a common affine chart satisfy $\mathrm{CB}(D)$. Indeed a separating polynomial would reduce the displayed sum to one nonzero coefficient times a nonzero value. The identity extends to complex polynomials by linearity.

The requirement that every coefficient is nonzero is essential. Zero coefficients must be discarded before defining the essential support. More general derivative functionals require a scheme version, which is not proved here. In particular, arbitrary affine numerators and Boolean projection ghosts cannot silently be replaced by this reduced-point hypothesis.

## Source audit and remaining parameter problem

The proof above uses a local socle generator, not an inference from the regularity of the isolated part. [Chardin and Philippon's regularity theorem](https://webusers.imj-prg.fr/~marc.chardin/publications/textes/11.RI.pdf) bounds the regularity of an isolated zero-dimensional part of an intersection. That fact alone does not provide a separator also vanishing on its positive-dimensional components. Their [erratum](https://webusers.imj-prg.fr/~marc.chardin/publications/textes/11.Err.pdf) corrects the definition of relative regularity and preserves their subsequent theorems; the local-socle argument above avoids that issue.

Known Cayley–Bacharach structure theorems do not presently supply the needed quantitative alternative. [Levinson and Ullery](https://arxiv.org/html/2102.08525) conjecture a plane-configuration statement in general dimension, with several low-dimensional cases proved. [Le and Linh](https://arxiv.org/html/2511.22113) extend the dimension-four case. [Banerjee](https://arxiv.org/html/2403.07272) obtains curve containment when the Cayley–Bacharach order is sufficiently large relative to the desired curve degree. The sufficient order in the latter argument is polynomial in that curve degree; at $H\asymp\exp(n)$ and $D\asymp\exp(\sqrt n)$, the natural degree budget $H/D$ is much too large to satisfy that condition. None of these results is used in the proof above.

The remaining counting problem is substantive. A low-dimensional variety can have a large family of defining equations. A candidate incidence bound would control the family of ordered configurations whose degree $s$ base locus has no isolated configuration points by roughly

$$ O\left(rH+H+\frac{n^2H}{s}\right) $$

parameters, together with a suitably small algebraic degree or an explicit polynomial atlas. This expression is a target, not a proved bound. Unions of long lines suggest the $rH$ position term and a cost of order $nH/s$ for varying their supports. Hypersurfaces of degree at most $s$ in a small linear space suggest why a moduli cost comparable to the degree $s$ Hilbert function could be plausible. Neither example justifies the bound for arbitrary reducible or singular base loci.

Even such an incidence dimension theorem would need an effective sign-pattern count on the resulting parameter locus. Replacing ambient parameter dimension by intrinsic dimension without charging algebraic degree would repeat the already-audited intrinsic-counting gap. The ordinary-moment lifting problem, the incidence-family bound, and its effective capacity estimate are three separate remaining steps.
