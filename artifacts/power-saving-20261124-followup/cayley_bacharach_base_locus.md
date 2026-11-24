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

The requirement that every coefficient is nonzero is essential. Zero coefficients must be discarded before defining the essential support. The scheme version below permits derivative functionals under an ordinary-moment hypothesis. Boolean projection ghosts still cannot silently be replaced by this hypothesis.

## Extension to finite local schemes

Let $Z\subset\mathbb A^n_{\mathbb C}$ be a zero-dimensional scheme of length $L$, with coordinate algebra $B=\prod_p B_p$ decomposed into its local factors. Let $\Lambda:B\to\mathbb C$ be a linear functional whose restriction to every factor $B_p$ is nonzero. Assume

$$ \Lambda(P)=0\qquad\text{for every polynomial }P\text{ of degree at most }D. $$

Let $V_s(Z)$ be the reduced base locus of all polynomials of degree at most $s$ vanishing scheme-theoretically on $Z$, or equivalently use their degree $s$ homogenizations in a chart containing $Z$. If $D\geq n(s-1)$, every support point of $Z$ lies on a positive-dimensional component of $V_s(Z)$. Every component dimension $r$ satisfies $\binom{s+r}{r}\leq L$.

**Proof.** Suppose $p$ is isolated in this base locus and choose $n$ equations of degree at most $s$ from $I(Z)$ isolating it, as before. Write $A$ for their finite local complete-intersection algebra at $p$, and $\Delta(x,y)$ for their divided-difference determinant. The natural map $A\to B_p$ is surjective.

We first verify the required full local duality using the same distinguished-socle fact as Lemma 1. In $A\otimes_{\mathbb C}A$, the adjugate identity gives $(x_j-y_j)\Delta=0$. Thus

$$ \Theta:A^\vee\to A,\qquad \Theta(\lambda)=(\mathrm{id}\otimes\lambda)(\Delta) $$

is an $A$-linear map, where $(a\lambda)(b)=\lambda(ab)$. The socle of $A^\vee$ is one-dimensional and consists of scalar multiples of residue evaluation $\pi:A\to\mathbb C$: annihilation by the maximal ideal means exactly that the functional vanishes on that ideal. The image $\Theta(\pi)=\Delta(x,p)$ is the nonzero distinguished socle element.

Every nonzero submodule of a finite module over an Artinian local ring meets its socle. To see this, multiply a nonzero element by the largest power of the maximal ideal that acts nontrivially. Therefore $\ker\Theta$ is zero. Its source and target have the same finite dimension, so $\Theta$ is an isomorphism.

After applying $A\to B_p$ in the first factor, the coefficient functionals of $\Delta(x,y)$ consequently span all of $B_p$. At every other local factor $B_q$, the determinant vanishes in $B_q\otimes A$. Indeed the adjugate identity still holds, and some $x_j-y_j$ has nonzero constant residue $q_j-p_j$ and hence is a unit in this tensor product of finite local complex algebras.

Choose $b\in B_p$ with $\Lambda|_{B_p}(b)\neq0$, and choose $\lambda\in A^\vee$ so that $g(x)=\lambda(\Delta(x,y))$ maps to $b$ in $B_p$. It maps to zero in all other factors, and has degree at most $n(s-1)$. Thus $\Lambda(g)\neq0$, contradicting the assumed moment annihilation.

Finally, scheme-theoretic containment of $Z$ in the degree $s$ equations implies the inequality

$$ \mathrm{HF}_{V_s(Z)}(s)\leq\mathrm{HF}_Z(s)\leq L. $$

The Noether-normalization argument gives the component bound. $\blacksquare$

A directional first-order functional $P\mapsto cP(b)+v\cdot\nabla P(b)$ factors through the length-two algebra obtained from $P(b+t v)$ modulo $t^2$, provided $v\neq0$; if $v=0$, its essential algebra has length one. A collection of such functionals at distinct supports can therefore have total scheme length at most twice the number of heads. This observation supplies the scheme input only when the asserted ordinary polynomial moments vanish. It does not establish that vanishing from original Boolean score cancellation.

## Source audit and remaining parameter problem

The proof above uses a local socle generator, not an inference from the regularity of the isolated part. [Chardin and Philippon's regularity theorem](https://webusers.imj-prg.fr/~marc.chardin/publications/textes/11.RI.pdf) bounds the regularity of an isolated zero-dimensional part of an intersection. That fact alone does not provide a separator also vanishing on its positive-dimensional components. Their [erratum](https://webusers.imj-prg.fr/~marc.chardin/publications/textes/11.Err.pdf) corrects the definition of relative regularity and preserves their subsequent theorems; the local-socle argument above avoids that issue.

Known Cayley–Bacharach structure theorems do not presently supply the needed quantitative alternative. [Levinson and Ullery](https://arxiv.org/html/2102.08525) conjecture a plane-configuration statement in general dimension, with several low-dimensional cases proved. [Le and Linh](https://arxiv.org/html/2511.22113) extend the dimension-four case. [Banerjee](https://arxiv.org/html/2403.07272) obtains curve containment when the Cayley–Bacharach order is sufficiently large relative to the desired curve degree. The sufficient order in the latter argument is polynomial in that curve degree; at $H\asymp\exp(n)$ and $D\asymp\exp(\sqrt n)$, the natural degree budget $H/D$ is much too large to satisfy that condition. None of these results is used in the proof above.

A low-dimensional variety can have a large family of defining equations. For reduced Cayley–Bacharach configurations, the next argument controls this family by a small determining subset. The separate weighted incidence argument now supplies an effective sign-pattern estimate, as recorded at the end of this note.

## A small determining subset

Write $h(t)=\mathrm{HF}_{\Gamma}(t)$, set $h(-1)=0$, and write $a_t=h(t)-h(t-1)$. Define

$$ m=\left\lfloor\frac{D+2}{s+1}\right\rfloor,\qquad 0\leq s\leq D+1. $$

Then

$$ m h(s)\leq H. $$

The source input is [Angelini, Chiantini, and Vannieuwenhoven, Theorem 4.9](https://ems.press/content/serial-article-files/39940?nt=1), which states for a finite reduced complex set satisfying $\mathrm{CB}(i)$ that

$$ \sum_{t=0}^j a_t\leq\sum_{t=i+1-j}^{i+1}a_t\qquad(0\leq j\leq i+1). $$

Their result extends the Geramita–Kreuzer–Robbiano inequality to any Cayley–Bacharach order, rather than only the final nonsurjective evaluation degree. No general-position hypothesis is present. Cayley–Bacharach is monotone in the order: a lower-degree separator could be multiplied by a linear form nonzero at the point being separated.

**Proof of the displayed bound.** For each complete block of $s+1$ successive indices in $\lbrace0,\ldots,D+1\rbrace$, its $a_t$ sum is at least $h(s)$. The initial block has that sum by definition. A later block ends at an index $k\leq D+1$. Apply the source inequality with $i=k-1$ and $j=s$, using $\mathrm{CB}(k-1)$. Sum over the $m$ disjoint complete blocks and use $\sum_{t\geq0}a_t=H$. $\blacksquare$

The arithmetic summation of these explicit window premises is kernel-checked in `Research/CayleyBacharachWindowMass.lean`: `window_mass_mul_floor_le`, `window_mass_le_div_floor`, and `window_mass_le_twice_ratio`. The geometric Hilbert-function inequality used to obtain those premises remains a written source-based argument.

In particular, if $s+1\leq(D+2)/2$, then

$$ h(s)\leq\frac{2(s+1)H}{D+2}. $$

Choose $M=h(s)$ points of $\Gamma$ whose degree $s$ evaluation functionals form a basis of the span of all evaluation functionals on $\Gamma$. The resulting subset $\Gamma_0$ satisfies

$$ |\Gamma_0|=M\leq H/m,\qquad I(\Gamma_0)_s=I(\Gamma)_s,\qquad V_s(\Gamma_0)=V_s(\Gamma). $$

Thus $M$ points determine the entire degree $s$ base locus. This is an existence statement, with finitely many choices of the determining indices, and does not assert a low-degree rational reconstruction chart.

## Dimension of the reduced configuration family

Let $\mathcal C_{n,H,D}$ be the constructible family of ordered configurations of $H$ distinct points of $\mathbb P^n_{\mathbb C}$ satisfying $\mathrm{CB}(D)$. Let

$$ r_\ast=\max\lbrace r\leq n:\binom{s+r}{r}\leq H\rbrace,\qquad M_\ast=\left\lfloor H/m\right\rfloor. $$

Then the preceding argument proves the dimension bound

$$ \dim\mathcal C_{n,H,D}\leq nM_\ast+r_\ast(H-M_\ast). $$

**Proof.** Cayley–Bacharach and all evaluation-rank requirements are constructible conditions, expressed by ranks of finite evaluation matrices. Partition the configuration family by $M=h(s)$ and by a choice of $M$ determining point indices. Projection onto those points has image dimension at most $nM$. For a fixed determining tuple, each remaining point belongs to its degree $s$ base locus, every component of which has dimension at most $r_\ast$ by the Hilbert-function bound above. The fiber has dimension at most $r_\ast(H-M)$. The fiber dimension theorem gives $nM+r_\ast(H-M)$ on each piece. This expression is nondecreasing in $M$, and $M\leq M_\ast$. A finite union has the maximum of its pieces' dimensions. $\blacksquare$

For $D=\lfloor\exp(\sqrt n)\rfloor$, take $s=\lfloor D/n^2\rfloor$. For sufficiently large $n$, $s+1\leq2D/n^2$, so $M_\ast\leq4H/n^2$. Also $\log(s/n)\geq\sqrt n/2$, giving $r_\ast\leq2(\log2)\sqrt n$ when $H\leq2^n$. Consequently

$$ \dim\mathcal C_{n,H,D}\leq\left(2(\log2)\sqrt n+\frac4n\right)H. $$

This dimension theorem concerns reduced ordinary-moment supports. The preceding finite-scheme separator theorem does not by itself extend the determining-point argument to nonreduced algebras.

## A bounded-degree curve cover at linear length

In affine dimension three, suppose a finite reduced set $\Gamma$ satisfies $\mathrm{CB}(D)$ and has $H\leq CD$ points, where $C\geq1$. Put $s=\lceil4C\rceil+2$, and assume $D\geq3(s+1)$. Then $\Gamma$ lies on an algebraic curve of total degree at most $s^2$, independently of $D$.

**Proof.** The window estimate gives

$$ h_\Gamma(s)\leq\frac{2(s+1)H}{D+2}\leq2C(s+1)\lt\binom{s+2}{2}. $$

Hence the degree $s$ base locus $V_s(\Gamma)$ has no component of dimension at least two. Its zero-dimensional components contain no point of $\Gamma$, by the local separator theorem and $D\geq3(s-1)$. Therefore every point of $\Gamma$ belongs to a one-dimensional component of $V_s(\Gamma)$.

Choose two sufficiently general linear combinations of the degree at most $s$ equations defining this base locus. They have no common hypersurface component in affine three-space: first choose a nonzero combination, and then avoid its finitely many irreducible factors, none of which divides every defining equation. Their intersection contains all curve components of $V_s(\Gamma)$. Affine Bézout bounds the sum of degrees of these curve components by $s^2$. Equivalently, homogenize the two chosen polynomials to their actual degrees; neither acquires the hyperplane at infinity as a component, and a common projective hypersurface would restrict to a common affine one. Projective Bézout therefore gives the same bound. Taking the union of the relevant curve components proves the assertion. $\blacksquare$

For a real set, one may take all complex curve components of the real base locus, which form a conjugation-invariant union. The resulting curve is defined over the reals and the degree bound still holds. This corollary uses the Hilbert-window and separator arguments above, not a separate curve-cover conjecture or a large-order curve theorem.

## Effective capacity and the remaining access problem

The determining tuple uses only $nM$ parameters, but its incidence equations also incur a degree cost. Choose an invertible $M$ by $M$ minor of its degree $s$ evaluation matrix. Membership of one additional point in the evaluation span is expressed by augmented minors. These equations have degree at most $sM$ in the determining-point variables and at most $s$ in the new point.

Giving weight one to the determining variables and weight $M$ to all other point variables bounds their weighted degree by $2sM$. The written theorem in `weighted_incidence_capacity.md` charges the incidence codimension at this lower degree and the remaining dimension at the score degree. Its application, including all affine numerator coefficients through the kernel-checked active-coefficient certificate, is worked out in `cayley_bacharach_head_capacity.md`. It proves the stated half-entropy counts at both requested widths for this pole-restricted class. The first-order annihilation argument there reduces first-order local moment functionals to reduced Cayley–Bacharach support with a factor two in the annihilation order.

An ordinary-moment lift or another access theorem for arbitrary original representations remains unresolved. Except for the explicitly identified arithmetic window declarations, the geometric results in this note are written proofs, not kernel-checked Lean declarations.
