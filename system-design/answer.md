# Answer: head complexity is positive linear-fractional threshold rank

Write

$$
  \chi_f(x)=2f(x)-1\in\lbrace-1,1\rbrace.
$$

All statements below concern nonconstant $f$.  A constant function needs no
head if $H=0$ is allowed, and one vacuous head if the convention requires
$H\ge1$.

An affine form

$$
  D(x)=d_0+\sum_{i=1}^n d_i x_i
$$

will be called **attention-positive** if it is positive on the Boolean cube
and either all $d_i\gt 0$ or all $d_i\lt 0$.  (Constant denominators occur as a
limit and do not change any strict Boolean classification.)  Define the
positive linear-fractional threshold rank

$$
 \rho_{\mathrm{LF}}(f)=\min\left\lbrace H:
 \chi_f(x)\sum_{h=1}^H\frac{N_h(x)}{D_h(x)}\gt 0
 \text{ for every }x\in\lbrace 0,1\rbrace^n\right\rbrace,                 \tag{1}
$$

where every $N_h$ is affine and every $D_h$ is
attention-positive.

The exact answer to the question in the README is

$$
                         \boxed{H^\ast(f)=\rho_{\mathrm{LF}}(f).}             \tag{2}
$$

The equivalence is constructive in both directions.  In particular, every
feasible representation in (1) is realized with scalar heads,
$d_{\rm head}=1$, a shared $d_{\rm model}=n+2$ embedding, and no
bit-dependent value increment.

This is also an attention-free characterization: after multiplying (1) by
the positive product of the denominators, it is the least $H$ for which
$f$ has a polynomial threshold representation of the special shared-factor
form

$$
 P(x)=\sum_{h=1}^H N_h(x)\prod_{k\ne h}D_k(x).             \tag{3}
$$

Thus the complexity measured by heads is not threshold degree alone.  It is
the width of a sum of positive linear-fractional functions, or equivalently
the shared-linear-factor width of the polynomial threshold form (3).

The characterization has substantive consequences:

$$
 \mathrm{tdeg}(f)\le H^\ast(f)
 \le \mathrm{spr}_{0/1}(f),                          \tag{4}
$$

where $\mathrm{spr}_{0/1}(f)$ is the minimum number of nonconstant
monomials in a strict multilinear polynomial threshold representation in the
$0/1$ monomial basis.  A sharper endpoint sparsity
$\mathrm{espr}(f)$, defined in Section 3, satisfies
$H^\ast(f)\le\mathrm{espr}(f)\le\mathrm{spr} _{0/1}(f)$.
Both sides of (4) can nevertheless be exponentially loose:
parity separates the upper bound, while the counting theorem separates the
lower bound.  For every nonconstant symmetric Boolean function,

$$
 H^\ast(f)=\lvert\lbrace k\in\lbrace 0,\ldots,n-1\rbrace :f(k)\ne f(k+1)\rbrace\rvert.         \tag{5}
$$

An exact rational covector certificate also proves
$H^\ast(f)=\mathrm{tdeg}(f)$ for every nonconstant Boolean function on
at most four bits.

Intersections and unions of coherent affine thresholds need at most the sum
of their numbers of attainable levels minus one.  For arbitrary mixed-sign
thresholds, finite-level polynomial interpolation gives the support-sensitive
bound (15d.1), so these natural threshold-gate compositions are covered
without treating inadmissible affine forms as attention denominators.

For the addressing function $\mathrm{IDX}_r(a,y)=y_a$, threshold
degree is exactly $r+1$, and a data-dependent Cauchy perturbation gives
$r+1\le H^\ast(\mathrm{IDX}_r)\le2^r-1$ for every $r\ge2$.  The first
three values are exactly 2, 3, and 4, respectively.

On the other hand, some threshold-degree-two functions on $n$ bits require
$\Omega(n/\log n)$ heads, and unrestricted functions can require
$\Omega(2^n/n^2)$ heads.  Hence no degree measure bounded by $n$ can
give a general upper bound on head complexity that is polynomial in $n$.
More generally, for every fixed $d\ge2$, exact threshold-degree $d$
functions can require $\Omega_d(n^{d-1}/\log n)$ heads.
The worst-case scale is localized to

$$
 \left(\frac12-o(1)\right)\frac{2^n}{n^2}
 \le \max_f H^\ast(f)
 \lt \frac32\frac{2^n}{n}\qquad(n\ge8).
$$

The exact characterization (2) and all constructive upper bounds below are
proved directly.  The explicit Hadamard lower-bound corollary invokes the
standard spectral sign-rank bound, and the enumerative lower bounds invoke
Warren's standard polynomial sign-pattern theorem; their uses and parameters
are stated where applied.

The remainder proves these statements.

## 1. Scalar normal form of a head

Fix a head and compose its output projection with the final readout.  The
result is a scalar value functional.  The query token is input-independent,
so the query vector is fixed.  Consequently, at input position $i$, the
logit and scalar value have the forms

$$
 \ell_i(x)=\kappa_i+\beta x_i,
 \qquad
 v_i(x)=c_i+\delta x_i,                                   \tag{6}
$$

where $\beta$ and $\delta$ are independent of $i$.  The query token
itself contributes a constant logit and a constant value.

Put $a_i=e^{\kappa_i}\gt 0$, $t=e^\beta\gt 0$, and let $q\gt 0$ be the
exponential of the query-token logit.  The scalar output of the head is

$$
 \frac{q c_{=}+\sum_i a_i t^{x_i}(c_i+\delta x_i)}
      {q+\sum_i a_i t^{x_i}}.                              \tag{7}
$$

Because $x_i\in\lbrace 0,1\rbrace$, both numerator and denominator in (7) are
affine functions of $x$; explicitly,

$$
 D(x)=q+\sum_i a_i+(t-1)\sum_i a_ix_i,
$$

$$
 N(x)=q c_{=}+\sum_i a_ic_i+
       \sum_i a_i\bigl(t(c_i+\delta)-c_i\bigr)x_i.
$$

The coefficient of $x_i$ in the denominator is $(t-1)a_i$.  Thus all
nonconstant denominator coefficients are strictly
positive when $t\gt 1$, strictly negative when $t\lt 1$, and zero when $t=1$.
The denominator is positive everywhere.

Every computed nonconstant Boolean classifier may be assumed to have a strict
margin.  Indeed, after a model has been fixed, raise the final threshold by an
amount smaller than the least positive-example margin.  Positive examples
remain positive, and examples formerly at or below the threshold become
strictly negative.  A head with $t=1$ can then be perturbed to $t\ne1$,
while its affine numerator is held fixed, and the finitely many scores change
by less than this margin.  Therefore every $H$-head classifier has a
representation of the form (1).  The constant residual and readout threshold
cause no extra term: for $H\ge1$, a constant $c$ is absorbed by replacing
$N_1$ with $N_1+cD_1$.

The converse is not merely formal; all the fractions in (1) can be realized
simultaneously with shared embeddings and scalar heads.  Consider

$$
 D(x)=d_0+\sum_i d_i x_i,
 \qquad N(x)=a+\sum_i b_i x_i.                             \tag{8}
$$

If all $d_i\gt 0$, choose $t\gt 1$ so large that

$$
 \sum_i\frac{d_i}{t-1}\lt d_0.
$$

If all $d_i\lt 0$, positivity at $1^n$ says
$d_0\gt\sum_i|d_i|$; choose $t\in(0,1)$ sufficiently close to zero that

$$
 \sum_i\frac{|d_i|}{1-t}\lt d_0.
$$

In either case set

$$
 \lambda_i=\frac{d_i}{t-1}\gt 0,
 \qquad q=d_0-\sum_i\lambda_i\gt 0.                           \tag{9}
$$

Then

$$
 q+\sum_i\lambda_i t^{x_i}=D(x).                          \tag{10}
$$

Set the bit-dependent part of the value to zero, choose

$$
 c_i=\frac{b_i}{d_i},
 \qquad
 c_{=}=\frac{a-\sum_i\lambda_i c_i}{q}.                   \tag{11}
$$

The numerator of (7) is now exactly $N(x)$.

To realize all heads at once, take a model space with basis

$$
 b,s_1,\ldots,s_n,q_0
$$

and use shared embeddings

$$
 e_0=0,\quad e_1=b,\quad p_i=s_i,\quad e_{=}=q_0,\quad p_{=}=0.
$$

For head $h$, use head dimension one.  Let its query map send $q_0$ to
one; let its key map send $s_i,b,q_0$ respectively to
$\log\lambda_{hi},\log t_h,\log q_h$; and let its value map send
$s_i,b,q_0$ respectively to $c_{hi},0,c_{h=}$.  Send the scalar head
output back along $q_0$, use the dual coordinate as the readout, and set the
readout threshold to one.  The residual contributes exactly that one, so the
resulting affine score is the sum in (1).  This constructs (1) exactly, using
$d_{\rm head}=1$ and $d_{\rm model}=n+2$.

This proves (2).  It also shows that unbounded model and head dimensions do
not add expressivity in the stated architecture.  More strongly, the
construction used $d_{\rm head}=1$ and set the bit-dependent value increment
$\delta$ to zero in every head.  Thus arbitrary value-vector width and
bit-sensitive values are unnecessary for exact expressivity here; the input
dependence can be carried entirely by scalar attention weights.

The characterization is algorithmic, not only terminological.  Fix $H$
and an orientation $\sigma_h\in\lbrace-1,1\rbrace$ for each denominator.  Feasibility
is the finite existential system

$$
 \sigma_hd_{hi}\gt 0,\qquad D_h(x)\gt 0,\qquad
 \chi_f(x)\sum_{h=1}^H N_h(x)\prod_{k\ne h}D_k(x)\gt 0       \tag{11a}
$$

for all $h,i$ and all cube vertices $x$.  These are strict polynomial
inequalities in the $2H(n+1)$ affine coefficients.  Enumerating the
$2^H$ orientations and applying real quantifier elimination decides whether
$H^\ast(f)\le H$.  The finite universal upper bound in Section 4 supplies a
stopping value, so (11a) computes $H^\ast(f)$ exactly from the truth table.
Equivalently, candidate-width membership lies in the existential theory of
the reals; the finite orientation disjunction may be enumerated or encoded.
This procedure is not claimed efficient; it records that no hidden choice of
embedding dimension or transcendental softmax parameter remains.
Moreover, every feasible set in (11a) is open and defined over the rationals,
so density of rational points gives a rational linear-fractional certificate
whenever a real one exists.  The corresponding transformer uses logarithms
of positive rationals in its key parameters, as in the explicit converse.

The normal form also makes the basic invariances transparent.  Output
negation replaces every $N_h$ by $-N_h$; coordinate permutations merely
permute coefficients; and the global bit complement $x\mapsto1-x$ flips
all coefficients of each denominator together while preserving positivity.
Thus these operations preserve $H^\ast$.  Fixing input coordinates preserves
denominator coherence on the remaining coordinates, so restrictions cannot
increase $H^\ast$.

Adding dummy coordinates preserves it exactly.  If $f(x)=g(x_S)$, fixing
the unused coordinates gives $H^\ast(g)\le H^\ast(f)$.  Conversely, extend each
denominator in a strict representation of $g$ by coefficients
$+\varepsilon$ on the unused coordinates when its orientation is positive,
and by $-\varepsilon$ when it is negative.  For sufficiently small
$\varepsilon\gt 0$, positivity and the finite classification margin persist,
while numerators can remain independent of the dummy bits.  Hence

$$
                              H^\ast(f)=H^\ast(g).              \tag{11b}
$$

## 2. Immediate algebraic consequences

For one head,

$$
 \mathrm{sign}\frac{N(x)}{D(x)}=\mathrm{sign}N(x)
$$

because $D\gt 0$.  Conversely, the construction above realizes every affine
threshold.  Therefore

$$
 H^\ast(f)=1
 \quad\Longleftrightarrow\quad
 f\text{ is a nonconstant linear threshold function}.     \tag{12}
$$

For $H$ heads, multiply (1) by
$Q=\prod_hD_h\gt 0$.  Equation (3) results, and its degree is at most $H$.
Replacing powers $x_i^r$ by $x_i$ multilinearizes it on the cube without
increasing degree.  Hence

$$
                         \mathrm{tdeg}(f)\le H^\ast(f). \tag{13}
$$

More precisely, (3) says that an $H$-head function has a degree $H$
polynomial threshold representation consisting of $H$ product gates, each
with $H$ affine factors, and with all but one factor shared between adjacent
terms.  This shared-factor constraint is the information lost by threshold
degree.

In fact, the top end of threshold degree is maximally coarse.  Let
$\pi(x)=(-1)^{|x|}$.  The evaluation vectors of all multilinear polynomials
of degree at most $n-1$ form the $(2^n-1)$-dimensional hyperplane

$$
 \left\lbrace s:\sum_x\pi(x)s(x)=0\right\rbrace.                    \tag{13a}
$$

The inclusion follows because the full alternating sum of every monomial of
degree below $n$ is zero, and equality follows by dimension.  This
hyperplane meets every open orthant except the two with sign vectors
$\pm\pi$: for any other sign vector $y$, the numbers $\pi(x)y(x)$ have
both signs, so positive magnitudes can be chosen to make their weighted sum
zero.  Therefore parity and its complement are the only functions with
threshold degree $n$; every other function has threshold degree at most
$n-1$.  Section 7 will show that many of those functions nevertheless need
exponentially many heads.

This also pins down the comparison with two other classical notions.  If
$\mathrm{spr}_{0/1}(f)$ denotes strict threshold sparsity in the
$0/1$-monomial basis, then the polynomial in (3), after
multilinearization, uses only monomials of degree at most $H$.  Consequently

$$
 \mathrm{spr}_{0/1}(f)
 \le \sum_{j=1}^{\min\lbrace H^\ast(f),n\rbrace}\binom nj.              \tag{13b}
$$

For rational degree there are two conventions.  A positive-denominator
rational sign representation $P/Q$, with $Q\gt 0$ on the cube, has exactly
the sign of $P$; its minimum numerator degree is therefore just threshold
degree.  Under the convention that both $P,Q$ have degree at most $d$
and $Q$ is merely nonzero, the sign is that of $PQ$, so

$$
 \tfrac12\mathrm{tdeg}(f)
 \le \mathrm{rdeg}_{\ne0}(f)
 \le \mathrm{tdeg}(f)
 \le H^\ast(f).                                             \tag{13c}
$$

Thus ordinary rational sign degree still forgets the factor-sharing and
coherent-positivity constraints.  Approximate rational degree is a different
notion: an exact classifier supplies no parameter-independent approximation
margin, so there is no automatic constant-error comparison.  Circuit-wise,
(3) is a depth-three arithmetic threshold expression: a top sum of $H$
products of affine forms, with the $H$ denominator factors shared and
positive.  Dropping either sharing or positivity enlarges the algebraic
circuit search space and is valid for lower bounds, but not for converses;
no equality with either relaxation is being asserted.

Walsh--Fourier sparsity is incomparable with head complexity.  The parity
sign function is a single Walsh character, yet has $H^\ast=n$.  In the other
direction, for $n\ge2$ the AND sign function is

$$
 2\prod_{i=1}^n x_i-1,
$$

whose expansion after $x_i=(1-z_i)/2$ has every one of the $2^n$ Walsh
characters nonzero (including the constant), yet AND has one head.  Thus
Fourier support size is incomparable with head complexity.  Fourier degree
also cannot replace it: AND has Fourier degree $n$ and one head, while the
counting theorem in Section 7 gives exponentially large head complexity even
though every Boolean function has Fourier degree at most $n$.

## 3. Sparse polynomial thresholds give head upper bounds

For a nonempty set $S\subseteq[n]$ and $\varepsilon\gt 0$, define

$$
 B_{S,\varepsilon}(x)=
 \frac{\varepsilon}
 {\varepsilon+\sum_{i\in S}(1-x_i)
   +\varepsilon^2\sum_{i\notin S}(1-x_i)}.                 \tag{14}
$$

The denominator has strictly negative nonconstant coefficients and remains
positive on the cube, so (14) is one admissible head.  Uniformly on the finite
cube,

$$
 B_{S,\varepsilon}(x)\longrightarrow x_S:=\prod_{i\in S}x_i
 \quad\text{as }\varepsilon\downarrow0.                   \tag{15}
$$

Indeed, if $x_S=0$, the denominator is at least one and the quotient is at
most $\varepsilon$.  If $x_S=1$, the quotient is
$1/(1+\varepsilon r)$, where $0\le r\le n-|S|$.

Let

$$
 p(x)=c_\varnothing+\sum_{S\in\mathcal S}c_Sx_S
$$

be a strict polynomial threshold representation of $f$.  The score

$$
 c_\varnothing+\sum_{S\in\mathcal S}c_SB_{S,\varepsilon}(x)
$$

converges uniformly to $p$.  Since the cube is finite and $p$ has a
strict margin, a sufficiently small $\varepsilon$ gives exactly the same
Boolean function.  The constant can be absorbed into one affine numerator.
This proves the upper bound in (4).

The subscript in $\mathrm{spr}_{0/1}$ matters: sparsity is measured
in the positive $0/1$ monomial basis $x_S$, not in the parity-character
basis after changing to $\lbrace-1,1\rbrace$ variables.

A basis-symmetric refinement is sometimes sharper.  Let
$\mathrm{espr}(f)$ be the minimum number of nonconstant endpoint
monomials in a strict threshold score when every term may independently be
either

$$
                       x_S=\prod_{i\in S}x_i
 \quad\text{or}\quad
                       \bar x_S=\prod_{i\in S}(1-x_i).
$$

The negative-oriented bump (14) realizes $x_S$, and its positive-oriented
dual realizes $\bar x_S$.  The same uniform-margin proof therefore gives

$$
 H^\ast(f)\le\mathrm{espr}(f)
 \le\min\lbrace\mathrm{spr}_{x}(f),\mathrm{spr}_{1-x}(f)\rbrace.
$$

Here $\mathrm{spr}_{x}=\mathrm{spr} _{0/1}$, and
$\mathrm{spr} _{1-x}$ is the analogous sparsity after using
$(1-x)_S$ as the monomial basis.
Allowing the two endpoint bases term by term is important; it is exactly what
produces the minority-polarity formula bound below.

The sparsity upper bound can be exponentially loose.  Let
$\pi(x)=(-1)^{|x|}$, and suppose a strict multilinear polynomial $p$ has
sign $\pi$.  Write

$$
 p(1_T)=(-1)^{|T|}r_T,\qquad r_T\gt 0.
$$

Möbius inversion says that the coefficient of $x_S$ is

$$
c_S=\sum_{T\subseteq S}(-1)^{|S|-|T|}p(1_T)
 =(-1)^{|S|}\sum_{T\subseteq S}r_T\ne0.                 \tag{15a}
$$

Thus every monomial occurs in every strict parity threshold polynomial.  The
polynomial $\prod_i(1-2x_i)$ supplies the matching upper bound, and

$$
 \mathrm{spr}_{0/1}(\mathrm{PARITY}_n)=2^n-1,
 \qquad H^\ast(\mathrm{PARITY}_n)=n.                         \tag{15b}
$$

The head value follows from the symmetric theorem in Section 5.  Hence head
complexity can be exponentially smaller than this threshold-sparsity measure,
even though it is always at least threshold degree.

As a useful corollary, a monotone DNF with $M$ terms has at most $M$ heads:
use one endpoint bump (14) for each satisfied conjunction and threshold their
sum at $1/2$.  For sufficiently small $\varepsilon$, an unsatisfied term
contributes at most $\varepsilon$, while a satisfied term contributes at
least $1/(1+n\varepsilon)$, which proves the separation explicitly.
Dually, a monotone CNF with $M$ clauses has at most $M$ heads by
using the analogous bumps

$$
 \frac{\varepsilon}
 {\varepsilon+\sum_{i\in S}x_i+
   \varepsilon^2\sum_{i\notin S}x_i}
$$

for violated clauses.

The same sparsity argument gives a controlled bound for nonmonotone formulas.
If the $j$-th term of a DNF contains $p_j$ positive and $q_j$ negated
literals, its indicator

$$
 \prod_{i\in P_j}x_i\prod_{i\in Q_j}(1-x_i)
$$

expands into at most $2^{q_j}$ positive-basis monomials.  There is a dual
expansion as well.  Put $u_i=1-x_i$; then

$$
 \prod_{i\in P_j}(1-u_i)\prod_{i\in Q_j}u_i
 =\sum_{T\subseteq P_j}(-1)^{|T|}u_{T\cup Q_j}.
$$

Every nonconstant $u_S=\prod_{i\in S}(1-x_i)$ is the limit of the
positive-oriented endpoint bump

$$
 \frac{\varepsilon}
 {\varepsilon+\sum_{i\in S}x_i+
   \varepsilon^2\sum_{i\notin S}x_i}.
$$

Thus one may use the cheaper of the two coherent endpoint bases.  Since the
DNF is the threshold of the sum of its term indicators,

$$
 H^\ast(\mathrm{DNF})\le\sum_j2^{\min\lbrace p_j,q_j\rbrace}.          \tag{15c}
$$

Applying the same statement to violated-clause indicators gives the analogous
CNF bound.  The remaining exponential dependence is on the minority literal
polarity within a term, rather than on a convention for which polarity is
called negated.  Arbitrary individual coordinate complementation still does
not preserve coherent denominator orientation.

### Intersections and unions of coherent thresholds

There is also a direct composition theorem for coherent threshold gates
(monotone or antimonotone).  Let

$$
 g_j(x)=\mathbf1[L_j(x)\gt 0],\qquad 1\le j\le M,
$$

where the nonzero coefficients of each affine $L_j$ all have the same sign,
and let $r_j$ be the number of distinct values assumed by $L_j$ on the
cube.  Then both the intersection and the union of these gates satisfy

$$
 H^\ast\left(\bigwedge_{j=1}^M g_j\right),\quad
 H^\ast\left(\bigvee_{j=1}^M g_j\right)
 \le\sum_{j=1}^M(r_j-1).                                 \tag{15d}
$$

Indeed, choose $r_j-1$ distinct shifts $t_{jh}$ large enough that every
$L_j+t_{jh}$ is positive on the cube.  On the $r_j$ distinct scalar
levels of $L_j$, the functions

$$
 1,\quad\frac1{L_j+t_{j1}},\ldots,
 \frac1{L_j+t_{j,r_j-1}}
$$

form a Cauchy basis by the root-counting argument of Section 4.  They
therefore interpolate the zero-one step $g_j$ exactly.  Each nonconstant
term is an attention head because its denominator is positive and coherent.
Zero coefficients in $L_j$ are handled by an arbitrarily small same-sign
perturbation of the denominators; the intersection and union scores below
have margin $1/2$, so the finite classifier is unchanged.

Finally, threshold
$\sum_jg_j-M+1/2$ for the intersection and
$\sum_jg_j-1/2$ for the union, absorbing the constant into one numerator.
For example, an intersection or union of $M$ unit-weight cardinality gates
has at most $Mn$ heads, since each has at most $n+1$ levels.  Mixed-sign
threshold weights fall outside this theorem for a structural reason: their
shifted affine forms are not admissible attention denominators.

There is nevertheless a general polynomial fallback for arbitrary threshold
weights.  Retain $g_j=\mathbf1[L_j\gt 0]$, let $S_j$ be the variable support
of $L_j$, and let $r_j$ again be its number of distinct cube values.  Put

$$
 \mathcal M=\bigcup_{j=1}^M
 \left\lbrace S:\varnothing\ne S\subseteq S_j,\ |S|\le r_j-1\right\rbrace.
$$

Then, without any sign-coherence assumption,

$$
 H^\ast\left(\bigwedge_jg_j\right),\quad
 H^\ast\left(\bigvee_jg_j\right)
 \le |\mathcal M|
 \le\min\left\lbrace 2^n-1,
   \sum_j\sum_{s=1}^{\min\lbrace|S_j|,r_j-1\rbrace}\binom{|S_j|}{s}\right\rbrace.       \tag{15d.1}
$$

Indeed, univariate Lagrange interpolation on the $r_j$ attainable levels
gives a polynomial $q_j$ of degree at most $r_j-1$ with
$q_j(L_j(x))=g_j(x)$ exactly.  After Boolean multilinearization,
$q_j(L_j(x))$ uses only monomials indexed by the displayed subsets of
$S_j$.  The scores
$\sum_jq_j(L_j)-M+1/2$ and
$\sum_jq_j(L_j)-1/2$ compute the intersection and union with margin
$1/2$.  The endpoint-sparsity construction then gives (15d.1).  This bound
can be much weaker than (15d) for coherent dense gates, but it applies to
mixed-sign gates and can be small when their supports or level counts are
small.  In particular, an intersection or union of (M) arbitrary
(s)-variable threshold gates needs at most (M(2^s-1)) heads (and often
fewer because their monomial supports overlap).

There is one general composition rule that does not require normalizing score
magnitudes.  If $f,g$ are functions on the same $n$-cube with head
complexities $H,K$, then

$$
 H^\ast(f\mathbin{\mathsf{XOR}}g)
 \le \sum_{j=1}^{\min\lbrace H+K,n\rbrace}\binom nj.                \tag{15e}
$$

Indeed, clear the positive denominators in strict scores for $f$ and $g$,
obtaining multilinear sign polynomials $P_f,P_g$ of degrees at most $H,K$.
The polynomial $-P_fP_g$, multilinearized on the cube, has the XOR sign.
It has degree at most $\min\lbrace H+K,n\rbrace$, so it contains no more nonconstant
monomials than the displayed sum.  The endpoint-bump theorem proves (15e).
The same statement holds for XNOR after removing the minus sign.  In contrast,
adding two arbitrary strict scores need not compute AND or OR: a large score
of one sign can overwhelm a small score of the other.  Thus no unproved linear
head-count composition rule is being used here.

## 4. A universal upper bound

Let $m=2^n$ and encode every vertex injectively by

$$
 z(x)=\sum_{i=1}^n2^{i-1}x_i\in\lbrace 0,\ldots,m-1\rbrace.
$$

Choose distinct positive numbers $t_1,\ldots,t_{m-1}$.  The $m$
functions on these nodes

$$
 1,\quad \frac1{z+t_1},\quad\ldots,\quad\frac1{z+t_{m-1}}                 \tag{16}
$$

are linearly independent.  To see this, suppose a linear combination
vanishes at all $m$ nodes and multiply it by
$Q(z)=\prod_h(z+t_h)$.  The result is a polynomial of degree at most
$m-1$ with $m$ distinct roots, hence is identically zero.  Evaluating it
at $-t_h$ kills every term except the $h$-th residue, so all coefficients
vanish.

Thus (16) interpolates any prescribed $m$ real labels.  Each nonconstant
term is an admissible head with constant numerator and positive coherent
denominator.  The constant term is absorbed into the first numerator.  Hence

$$
                           H^\ast(f)\le2^n-1.                 \tag{17}
$$

This is an exact interpolation construction, rather than a limiting one.

### A sharper universal upper bound from hypercube neighborhoods

Let $Q_n$ be the graph of the Boolean cube, let
$\Gamma(v)=\lbrace x:d_H(x,v)=1\rbrace$ be the open neighborhood of $v$, and let
$\gamma_o(Q_n)$ be the fewest open neighborhoods that cover all vertices.
Then

$$
                         H^\ast(f)\le\gamma_o(Q_n).           \tag{17a}
$$

To prove this, first temporarily allow arbitrary nonvanishing affine
denominators.  For a center $v$, the affine form

$$
 L_v(x)=d_H(x,v)-1
$$

vanishes on exactly the $n$ vertices in $\Gamma(v)$.  For small
$\varepsilon\gt 0$, consider the denominator $L_v+\varepsilon$.  For every
affine numerator $N$,

$$
 \frac{\varepsilon N(x)}{L_v(x)+\varepsilon}
 \longrightarrow
 \begin{cases}
  N(x),&x\in\Gamma(v),\cr
  0,&x\notin\Gamma(v).
 \end{cases}                                               \tag{17b}
$$

The $n$ neighbors of $v$ are affinely independent, so restrictions of
affine numerators to $\Gamma(v)$ give every vector in
$\mathbb R^{\Gamma(v)}$.  If the chosen neighborhoods cover the cube, the
limiting numerator spaces therefore contain every coordinate vector of
$\mathbb R^{2^n}$.  A suitable $2^n\times2^n$ evaluation minor tends to a
nonzero diagonal determinant, and hence is nonzero for sufficiently small
$\varepsilon$.  Fix such an $\varepsilon$ and the corresponding affine
numerator columns.

It remains to restore the attention sign restriction.  That evaluation minor
is a rational function of the affine-denominator coefficients.  Since it is
nonzero at the construction above, its cleared numerator is a nonzero
polynomial.  A nonzero real polynomial cannot vanish on the entire open cone

$$
 d_0\gt 0,\qquad d_1\gt 0,\ldots,d_n\gt 0.
$$

Thus the same minor is nonzero for some strictly positive coherent
denominators.  With those denominators fixed, affine numerators interpolate
every real function on the cube.  The normal-form converse then proves
(17a).  In fact, the exceptional positive denominators lie in the zero set of
a nonzero polynomial, so independent continuously distributed positive
coefficients succeed with probability one.

The transfer can also be made a finite construction.  Choose the mixed-sign
witness and its affine numerator columns rationally.  If $m=2^n$ and the
cover has $H$ centers, multiply each row of the selected evaluation minor
by $\prod_hD_h(x)$.  Its determinant becomes a nonzero polynomial in the
$H(n+1)$ denominator coefficients, of total degree at most $mH$.  A
nonzero polynomial of total degree at most $mH$ cannot vanish on every point
of the grid

$$
                  \lbrace 1,2,\ldots,mH+1\rbrace^{H(n+1)}.
$$

Hence exhaustive finite search finds positive integer denominator
coefficients with the required full-rank minor.  This is inefficient but
fully constructive; the almost-sure statement above is only the shorter way
to choose them.

There is an elementary probabilistic cover bound.  Select every cube vertex
as a center independently with probability $p=\ln(n)/n$.  A fixed vertex
has $n$ possible neighboring centers, so its probability of remaining
uncovered is at most

$$
 (1-p)^n\le e^{-pn}=\frac1n.
$$

After the random choice, add one neighboring center for every uncovered
vertex.  The expected final number of centers is at most

$$
 2^n p+\frac{2^n}{n}
 =\frac{2^n(\ln n+1)}{n}.
$$

Consequently a cover of at most the ceiling of this quantity exists.  Along
with the Cauchy construction,

$$
 H^\ast(f)\le
 \min\left\lbrace 2^n-1,
 \left\lceil\frac{2^n(\ln n+1)}n\right\rceil\right\rbrace
 =O\left(\frac{2^n\log n}{n}\right).                   \tag{17c}
$$

A binary linear-code construction removes the logarithmic factor for every
$n$.  Put $r=\lfloor\log_2 n\rfloor$, and form an $r\times n$
parity-check matrix $B$ whose first $2^r$ columns list every syndrome in
$\mathbb F_2^r$, including zero; repeat arbitrary columns if necessary.
The matrix has rank $r$, so its kernel $C$ has size $2^{n-r}$.

For every vertex $x$, its syndrome $s=Bx$ occurs as a column, say the
$i$-th.  Hence $B(x\oplus e_i)=s+s=0$, and $x$ has a neighbor in
$C$.  This also works when $s=0$: flipping the coordinate whose column is
zero gives a distinct neighboring codeword.  Thus the open neighborhoods
centered at the single kernel $C$ cover the entire cube.  Consequently

$$
 H^\ast(f)\le\gamma_o(Q_n)\le2^{n-\lfloor\log_2n\rfloor}
 \lt\frac{2^{n+1}}n.                                       \tag{17d}
$$

At powers of two this construction has exactly $2^n/n$ centers, meeting
the elementary covering lower bound because every open neighborhood contains
$n$ vertices.

The syndrome construction has a useful nonlinear refinement.  Let the
columns of a full-rank $r\times n$ parity-check matrix form a set
$A\subseteq\mathbb F_2^r$, and let $T\subseteq\mathbb F_2^r$ satisfy

$$
                              T+A=\mathbb F_2^r.
$$

Then the union of the syndrome fibers indexed by $T$ is an open dominating
set: if $Bx=s=t+a$, flipping a coordinate whose column is $a$ moves $x$
to syndrome $t$.  Its size is $|T|2^{n-r}$, and therefore

$$
                  H^\ast(f)\le\gamma_o(Q_n)\le |T|2^{n-r}. \tag{17d'}
$$

This can improve the power-of-two rounding constant.  In
$\mathbb F_2^6$, the following are two exact additive covers:

$$
\begin{split}
 A_{12}={}&\lbrace 17,18,20,23,26,31,34,39,56,58,61,63\rbrace,\cr
 T_7={}&\lbrace 0,6,10,20,22,48,49\rbrace,\cr
 A_{14}={}&\lbrace 6,11,20,25,33,34,35,43,46,47,52,53,62,63\rbrace,\cr
 T_6={}&\lbrace 0,4,7,8,43,57\rbrace.
\end{split}
$$

Integers are read as six-bit vectors.  Direct XOR gives
$T_7+A_{12}=T_6+A_{14}=\mathbb F_2^6$, and both column sets span the
space.  There is also a seven-bit cover

$$
\begin{split}
 A_{13}={}&\lbrace 0,3,4,14,20,52,66,89,95,96,110,115,126\rbrace,\cr
 T_{12}={}&\lbrace 0,1,13,40,69,78,83,97,104,112,120,125\rbrace,
\end{split}
$$

with $T_{12}+A_{13}=\mathbb F_2^7$ and $A_{13}$ spanning.  Cartesian-
product lifting here is completely explicit: from any cover
$T+A=\mathbb F_2^r$, set

$$
 A^{(s)}=A\times\mathbb F_2^s,
 \qquad T^{(s)}=T\times\lbrace 0^s\rbrace.
$$

Then
$T^{(s)}+A^{(s)}=(T+A)\times\mathbb F_2^s=\mathbb F_2^{r+s}$,
$|A^{(s)}|=|A|2^s$, and $|T^{(s)}|=|T|$.  The lifted columns still
span: $A$ spans the first factor, and, after fixing any $a\in A$, the
differences of $(a,u)$ over $u\in\mathbb F_2^s$ span the second.
Repeating any existing column then increases the matrix length without
changing the sumset or its rank.

Apply this with $s=k-3$.  The $12/7$ cover is available once
$n\ge122^{k-3}=32^{k-1}$, has syndrome dimension $6+s=k+3$, and
gives $72^{n-k-3}$ centers.  The $13/12$ cover is available once
$n\ge132^{k-3}$, has syndrome dimension $7+s=k+4$, and gives
$122^{n-k-4}$ centers.  Before the first threshold use the
single-kernel construction.  Thus, for
$k=\lfloor\log_2n\rfloor\ge3$,

$$
\gamma_o(Q_n)\le
\begin{cases}
 2^{n-k},
   &2^k\le n\lt 3\cdot2^{k-1},\cr
 72^{n-k-3},
   &3\cdot2^{k-1}\le n\lt 13\cdot2^{k-3},\cr
 122^{n-k-4},
   &13\cdot2^{k-3}\le n\lt 2^{k+1}.
\end{cases}                                             \tag{17d''}
$$

The first regime is (17d); the next two use the $12/7$ and $13/12$
covers.  Relative to $2^n/n$, the three bounds are respectively less than
$3/2$, $91/64$, and $3/2$.  At the two refinement points
$n=12\cdot2^s$ and $n=13\cdot2^s$, the constants are $21/16$ and
$39/32$, respectively.
Consequently

$$
                    H^\ast(f)\le\gamma_o(Q_n)
                    \lt\frac32\frac{2^n}{n}
                    \qquad(n\ge8).                       \tag{17d'''}
$$

Since each open neighborhood has exactly $n$ vertices, a union bound gives
$\gamma_o(Q_n)\ge\lceil2^n/n\rceil$.  Therefore the explicit piecewise
covers in (17d'') have size strictly less than
$(3/2)\gamma_o(Q_n)$ for every $n\ge8$: they are a strict
$3/2$-approximation to the optimal open-neighborhood cover.  This lower
bound concerns the cover mechanism; it is not asserted as a lower bound on
$H^\ast(f)$.

The 14 columns in the six-target base cover are best possible for that
six-bit mechanism.  Translate $T$ so that $0\in T$.  Its five other
distinct vectors have rank between three and five (a two-dimensional binary
space has only three nonzero vectors).  At rank five they are a basis.  At
rank four their one-dimensional relation kernel is classified by its support,
whose size is three, four, or five.  At rank three, a five-element subset of
the seven nonzero vectors is determined by its two-element complement, and
$\mathrm{GL}(3,2)$ is transitive on pairs of distinct nonzero vectors.
Thus, up to an invertible linear change of
coordinates there is one rank-five type, three rank-four types (according to
whether the unique circuit has size three, four, or five), and one rank-three
type.  Representatives, with binary vectors encoded by integers, are

$$
\begin{array}{c|c}
\mathrm{rank}&T\cr \hline
5&\lbrace 0,1,2,4,8,16\rbrace\cr
4&\lbrace 0,1,2,4,8,3\rbrace,\ \lbrace 0,1,2,4,8,7\rbrace,
   \lbrace 0,1,2,4,8,15\rbrace\cr
3&\lbrace 0,1,2,3,4,5\rbrace.
\end{array}
$$

For each representative, `selftests/run` enumerates every subset $B$ of
the indicated span of the relevant size and computes $|T+B|$ exactly.
The resulting translate maxima are:

- six translates of the rank-five type cover at most 30 of 32 points;
- three translates of the rank-four types cover at most 14, 14, and 13 of
  16 points;
- the rank-three type needs two translates to cover its eight-point span.

Accounting for the cosets of each span in $\mathbb F_2^6$ gives lower
bounds $14,16,16$ on the number of columns, respectively.  Thus
$|A|\ge14$ whenever $|T|=6$ and $A+T=\mathbb F_2^6$, with equality in
the displayed $A_{14},T_6$ certificate.  This is a scoped finite
optimality statement, not a claim that the global constant $3/2$ is
optimal among all neighborhood covers.

For fixed-denominator numerical interpolation, this order is optimal.  Define
$I_n$ to be the least $H$ for which some fixed admissible denominators
$D_1,\ldots,D_H$ satisfy

$$
 \mathrm{span}\left\lbrace\frac{N}{D_h}:
 N\text{ affine},\ 1\le h\le H\right\rbrace
 =\mathbb R^{\lbrace 0,1\rbrace^n}.
$$

For each fixed $D_h$, the numerator space has dimension $n+1$ and
contains the same constant function $D_h/D_h=1$.  Hence the sum of $H$
such spaces has dimension at most $1+nH$.  The cover construction and this
dimension bound give

$$
 \left\lceil\frac{2^n-1}{n}\right\rceil
 \le I_n
 \le2^{n-\lfloor\log_2n\rfloor}
 \lt\frac{2^{n+1}}n.                                       \tag{17e}
$$

For $n\ge8$, the multi-coset refinement (17d''') sharpens the final upper
bound in (17e) to $I_n\lt(3/2)2^n/n$.
Thus the fixed-denominator universal interpolation width is
$I_n=\Theta(2^n/n)$.  Moreover, if $n\ge2$ is a power of two, both endpoints
in (17e) equal $2^n/n$, and hence

$$
                         I_n=\frac{2^n}{n}
 \qquad(n\ge2\text{ a power of two}).                    \tag{17f}
$$

There is also a structural proof of the $n=3$ case.  In $Q_3$, the neighborhoods of
$000,001,010$ cover all vertices except $111$.  The localization limit
therefore spans the other seven coordinate vectors; together with the common
constant vector it also spans the eighth.  Positive-cone transfer and the
dimension lower bound give $I_3=3$.

Exact rational row-reduction certificates in `selftests/run` additionally
attain the dimension lower bound at $n=5,6$.  Full-rank reductions modulo
the prime $10^9+7$ do the same at $n=7,9,10,11,12$: all denominators
are positive integers and nonzero modulo the prime, so a nonzero modular
minor implies a nonzero rational minor.  The larger three reductions are
reproduced in `selftests/interpolation_modular_large`.  The cases $n=2,4,8$
follow from (17f), and $n=1$ is immediate.  Therefore

$$
 I_n=\left\lceil\frac{2^n-1}{n}\right\rceil
 \qquad(1\le n\le12).                                   \tag{17g}
$$

The blocked generic interpolation question in the approach registry concerns
the sharp lower endpoint in general, not these finite cases or the asymptotic
order.

## 5. Exact head complexity of every symmetric function

Suppose $f(x)$ depends only on $k=|x|$, and let

$$
 A(f)=\lvert\lbrace k\in\lbrace 0,\ldots,n-1\rbrace : f(k)\ne f(k+1)\rbrace\rvert.          \tag{18}
$$

First, any degree $d$ polynomial threshold representation can be averaged
over all coordinate permutations.  At a fixed Hamming weight all summands
have the same strict sign, so averaging preserves the represented function.
A symmetric multilinear polynomial of degree $d$ has the form

$$
 \sum_{r=0}^d a_r e_r(x),
$$

and at weight $k$, $e_r(x)=\binom{k}{r}$.  It therefore becomes a
univariate polynomial $q(k)$ of degree at most $d$.  Every adjacent label
change forces a distinct real root in the corresponding interval
$(k,k+1)$.  Thus $d\ge A(f)$.  By (13),

$$
 H^\ast(f)\ge A(f).                                           \tag{19}
$$

For the converse, put one root $r_k\in(k,k+1)$ in every interval where the
label changes.  A signed product of these $A(f)$ linear factors is a
univariate polynomial $p(k)$ whose sign is exactly $\chi_f(k)$.  Choose
distinct $t_1,\ldots,t_A\gt 0$ and set

$$
 Q(k)=\prod_{h=1}^A(k+t_h).
$$

Since $\deg p=\deg Q=A$, partial fractions give

$$
 \frac{p(k)}{Q(k)}=c+\sum_{h=1}^A\frac{c_h}{k+t_h}.         \tag{20}
$$

Every denominator in (20) is
$t_h+x_1+\cdots+x_n$, hence is attention-positive.  Absorb $c$ into one
numerator and apply (2).  This proves (5).

Consequently:

- $\mathrm{AND}$, $\mathrm{OR}$, majority, and every nonconstant
  one-cut Hamming-weight threshold have one head;
- parity has exactly $n$ heads;
- $\mathrm{EXACT}_t$ has two heads for $0\lt t\lt n$, and one head at
  $t=0,n$;
- any symmetric function that is one on a union of Hamming-weight intervals
  has exactly the number of boundary crossings of those intervals.

For $n=2$, this recovers the complete classification: fourteen functions
are affine threshold functions and hence use at most one head (the two
constants use zero under the $H=0$ convention), while XOR and XNOR use two.

### Functions of a coherent affine statistic

The upper-bound mechanism does not require full symmetry.  Let

$$
 L(x)=\ell_0+\sum_iw_ix_i
$$

have all $w_i\gt 0$ or all $w_i\lt 0$, let its distinct values on the cube be
$\lambda_1\lt\cdots\lt\lambda_s$, and suppose $f(x)=\phi(L(x))$.  If

$$
 A_L(f)=\lvert\lbrace j:\phi(\lambda_j)\ne\phi(\lambda_{j+1})\rbrace\rvert,
$$

then

$$
                              H^\ast(f)\le A_L(f).           \tag{20s}
$$

Put one root in each open interval between consecutive attainable levels
where the label changes, and let $p(L)$ be the signed product of those
linear factors.  Choose $A_L(f)$ distinct shifts $t_h$ so large that
$L+t_h\gt 0$ on the cube.  The partial-fraction expansion of
$p(L)/\prod_h(L+t_h)$ has one constant and $A_L(f)$ reciprocal terms.
Every denominator is attention-positive with the orientation of the $w_i$'s,
so the normal-form theorem proves (20s).  Unlike the symmetric case, no
matching lower bound is asserted: an unrelated nonsymmetric threshold
polynomial need not be a polynomial in $L$.

As a concrete broad corollary, partition the variables into blocks of sizes
$n_1,\ldots,n_b$, and suppose $f$ is invariant under permutations within
each block.  Mixed-radix weights encode the block Hamming weights injectively
by one all-positive affine statistic.  Therefore

$$
 H^\ast(f)\le \prod_{j=1}^b(n_j+1)-1.                       \tag{20t}
$$

The sharper bound (20s) counts only the label changes in the mixed-radix
ordering.  For fixed $b$, (20t) is polynomial in the block sizes even though
the function may depend on every input bit.

### Addressing / indexing

Let $\mathrm{IDX}_r$ have address bits
$a=(a_1,\ldots,a_r)$, data bits $(y_b) _{b\in\lbrace 0,1\rbrace^r}$, and output
$y_a$.  This natural nonsymmetric family satisfies

$$
 r+1\le H^\ast(\mathrm{IDX}_r)\le2^r.                 \tag{20a}
$$

The lower bound already follows from threshold degree, and that degree can
be determined exactly.  Introduce a new Boolean variable $z$ and identify
each data bit by

$$
 y_b=z\oplus |b|\pmod2.
$$

This is an affine substitution: $y_b=z$ for even $|b|$ and
$y_b=1-z$ for odd $|b|$.  Under it, $\mathrm{IDX}_r$ becomes
parity (or its complement, depending on the sign convention) on
$a_1,\ldots,a_r,z$.  Substitution and Boolean multilinearization do not
increase polynomial degree, so parity's degree lower bound gives
$\mathrm{tdeg}(\mathrm{IDX}_r)\ge r+1$.  The exact selector
polynomial

$$
 2\sum_{b\in\lbrace 0,1\rbrace^r}y_b
   \prod_{i:b_i=1}a_i\prod_{i:b_i=0}(1-a_i)-1            \tag{20b}
$$

has degree $r+1$ and sign $2y_a-1$, proving equality.

For the head upper bound, put $m=2^r$ and encode the address by the distinct
number $z(a)=\sum_i2^{i-1}a_i$.  Choose $m$ distinct positive poles
$t_1,\ldots,t_m$.  The square Cauchy matrix

$$
 \left(\frac1{z(a)+t_h}\right)_{a,h}
$$

is nonsingular by the same root-counting proof as (16).  Hence, for every
data coordinate $b$, there are coefficients $\beta_{hb}$ such that

$$
 \sum_{h=1}^m\frac{\beta_{hb}}{z(a)+t_h}=\mathbf1[a=b].  \tag{20c}
$$

Summing (20c) against $y_b$ gives exactly $y_a$.  Subtract $1/2$ by
replacing the first affine numerator with
$\sum_b\beta_{1b}y_b-\tfrac12(z(a)+t_1)$.  The displayed denominators have
zero coefficients on the data bits; adding
$\varepsilon\sum_b y_b$ to every denominator makes all coefficients
strictly positive.  On the finite cube the resulting score converges
uniformly to $y_a-1/2$, so sufficiently small $\varepsilon\gt 0$ preserves
the classifier.  This proves the upper bound in (20a) with valid attention
denominators.

This $2^r$-term construction is optimal if the denominators are required to
be data-independent (the unperturbed closure used above).  In that case the
score at address $a$ is

$$
 b(a)+\sum_b C_{ab}y_b,\qquad
 C_{ab}=\sum_{h=1}^H\frac{\beta_{hb}}{D_h(a)},
$$

so $\mathrm{rank}C\le H$.  Correct classification for every data
vector forces
$C_{aa}\gt\sum_{b\ne a}|C_{ab}|$: compare the largest score with $y_a=0$
to the smallest score with $y_a=1$.  Thus $C$ is strictly diagonally
dominant and nonsingular, giving $H\ge2^r$.  Improvements over (20a) must
therefore exploit genuine data dependence in the denominators.

Such dependence always saves one head once $r\ge2$.  More precisely,

$$
 r+1\le H^\ast(\mathrm{IDX}_r)\le2^r-1
 \qquad(r\ge2).                                         \tag{20c.1}
$$

Here is an explicit proof of the improved upper bound.  Put $m=2^r$,
$H=m-1$, and use poles $h=1,\ldots,H$.  On the address nodes
$z=0,\ldots,m-1$, let

$$
 R_{zh}=\frac1{z+h},\qquad
 Q(z)=\prod_{h=1}^{m-1}(z+h),\qquad
 V(z)=\prod_{j=0}^{m-1}(z-j),
$$

and set $c_z=Q(z)/V'(z)$.  Since $Q(z)/(z+h)$ has degree $m-2$, the
Lagrange leading-coefficient identity gives $c^TR=0$.  The columns of
$R$ are independent by the Cauchy root-counting argument used in (16), so
$\mathrm{col}R=c^\perp$.  Also, $m$ is even and $Q(z)\gt 0$ on
these nodes, so
$\mathrm{sign}c_z=(-1)^{m-1-z}=(-1)^{z+1}$.

Let $q=m/2$, and define a vector $B$ supported at two even nodes by

$$
 B_0=c_q,\qquad B_q=-c_0,
 \qquad B_z=0\quad(z\ne0,q).
$$

Then $c^TB=0$, so there is a unique rational $\beta$ with $R\beta=B$.
The signs of its entries are explicit.  If

$$
 \sum_{h=1}^{m-1}\frac{\beta_h}{z+h}=\frac{P(z)}{Q(z)},
$$

then $P$ has the $m-2$ roots other than $0,q$, and therefore

$$
 P(z)=K\prod_{j\ne0,q}(z-j),\qquad K\lt 0.
$$

Indeed, $c_q\lt 0$, so $P(0)=B_0Q(0)=c_qQ(0)\lt 0$, while the displayed
product at zero is positive because it has $m-2$ negative factors.

At $-h$, $P(-h)\lt 0$, whereas
$\mathrm{sign}Q'(-h)=(-1)^{h-1}$.  Taking residues gives

$$
                         \mathrm{sign}\beta_h=(-1)^h.             \tag{20c.2}
$$

Let $a_1=z\bmod2$ be the low address bit and put
$U_h(a)=\beta_ha_1$.  Because $B$ is supported on even nodes,

$$
                 \sum_h\frac{U_h(a)}{z(a)+h}=a_1B_{z(a)}=0.             \tag{20c.3}
$$

Define the address vectors

$$
 g_h(a)=-\frac{U_h(a)}{(z(a)+h)^2},qquad
 \gamma_h=c^Tg_h.
$$

Here $c_z$ is positive at every odd $z$, so

$$
 \gamma_h=-\beta_h\sum_{z\ \mathrm{odd}}\frac{c_z}{(z+h)^2}.
$$

By (20c.2), the rational vector $\gamma$ has both positive and negative
entries.  Consequently, for each data coordinate $b$, one can choose
strictly positive rational $q_{hb}$ such that
$\sum_h\gamma_hq_{hb}=c_b$: start all $q_{hb}$ at one and increase one
coordinate having the required sign.  It follows that

$$
 c^T\left(e_b-\sum_hq_{hb}g_h\right)=0.
$$

The parenthesized vector lies in $c^\perp=\mathrm{col}R$, so choose
rational $v_{hb}$ with

$$
 e_b=\sum_h\left(\frac{v_{hb}}{z+h}+q_{hb}g_h\right).    \tag{20c.4}
$$

Now use the $H=m-1$ heads

$$
 D_h=z(a)+h+\varepsilon\sum_bq_{hb}y_b,
 \qquad
 N_h=\varepsilon^{-1}U_h(a)+\sum_bv_{hb}y_b.             \tag{20c.5}
$$

Their denominators have strictly positive coefficients.  Expanding at
$\varepsilon=0$, the order $1/\varepsilon$ term vanishes by (20c.3),
and (20c.4) makes the finite term exactly $y_a$.  The remaining error is
uniformly $O(\varepsilon)$ on the finite cube.  Subtract $1/2$ in one
numerator and take a sufficiently small positive rational $\varepsilon$.
This proves (20c.1) with an actual strict attention representation.

The first two address sizes can be made exact:

$$
 H^\ast(\mathrm{IDX}_1)=2,
 \qquad H^\ast(\mathrm{IDX}_2)=3.                     \tag{20d}
$$

The first identity follows immediately from (20a).  For the second, use
little-endian address order $b_1+2b_2$, so the six variables are
$(a_1,a_2,y_{00},y_{10},y_{01},y_{11})$.  The following rows give
$(d_0;d_1,\ldots,d_6)$ for $D_h$ and
$(n_0;n_1,\ldots,n_6)$ for $N_h$:

$$
\begin{array}{c|r|r}
h&D_h&N_h\cr \hline
1&(2;1,1,2,1,2,1)&(173;203,-203,-15,-203,-169,203)\cr
2&(1;2,1,2,1,1,1)&(-203;13,161,-18,30,184,-114)\cr
3&(1;1,2,1,2,2,1)&(26;-203,1,45,170,-18,-33)
\end{array}
$$

All denominator coefficients and constants are positive.  Direct exact
substitution on the 64 vertices gives

$$
 (2\mathrm{IDX}_2(x)-1)
 \sum_{h=1}^3\frac{N_h(x)}{D_h(x)}\ge\frac8{15}\gt 0.
$$

Thus three heads suffice, while the threshold-degree lower bound in (20a)
rules out two.  The certificate is independently evaluated with rational
arithmetic in `selftests/run`.

The next address size is also exact:

$$
                 H^\ast(\mathrm{IDX}_3)=4.            \tag{20d'}
$$

In the variable order
$(a_1,a_2,a_3,y_0,\ldots,y_7)$, the following integer rows give
$(d_0;d_1,\ldots,d_{11})$ and
$(n_0;n_1,\ldots,n_{11})$:

$$
\begin{array}{c|r|r}
h&D_h&N_h\cr \hline
1&(1000;22026466,1,22026466,1,1,4764,1,1,1,1,1)
 &(-42568;-10314,-171161,-36369,124386,-13248,1052,-12245,-5783,7390,-22003,-22036)\cr
2&(22029032;-22026466,-1,-563,-1,-485,-1,-76,-415,-1,-22,-1)
 &(-16622;-2559,-204994,-65214,-1610,29882,655,2624,-677,12207,625,-6785)\cr
3&(22034149;-1959,-3563,-22026466,-1,-121,-1,-1,-1,-1,-1,-1034)
 &(-14668;234978,-36046,-10799,5177,-13621,-5057,-1519,74534,12665,-4377,-17400)\cr
4&(22030391;-1,-22026466,-1,-1,-144,-1,-1571,-1066,-1,-1,-138)
 &(83654;72237,91371,-132731,-5346,9544,5519,-28717,-61088,-5598,58660,13018)
\end{array}
$$

The executable `selftests/address_three_bit_four_heads` contains four fixed
integer numerator-denominator pairs and checks all 2,048 inputs using exact
`Fraction` arithmetic.  One denominator has all positive nonconstant
coefficients and three have all negative nonconstant coefficients; all four
are at least 1,000 on the cube.  The exact minimum signed margin is

$$
 \frac{145955662462817}{271312146681030}\gt 0.537.            \tag{20d''}
$$

Thus four heads suffice with a rational attention certificate.  The
threshold-degree lower bound $r+1=4$ proves optimality, giving (20d').

There is also a complete three-bit classification.  Fix

$$
 D_1=1+x_1+x_2+x_3,
 \qquad D_2=1+2x_1+3x_2+4x_3.
$$

The seven score vectors obtained by evaluating

$$
 1,\quad \frac{x_1}{D_1},\frac{x_2}{D_1},\frac{x_3}{D_1},
 \quad \frac{x_1}{D_2},\frac{x_2}{D_2},\frac{x_3}{D_2}
$$

on the eight cube vertices have rank seven; for example, the minor obtained
by omitting the $000$ row is $1/14515200$.  These vectors span the full
two-denominator numerator space: for each $h$, the omitted vector $1/D_h$
is a linear combination of $1$ and the $x_i/D_h$, using
$1=D_h/D_h$.  Their common orthogonal vector is

$$
 c_x=(-1)^{|x|}D_1(x)D_2(x).
$$

Orthogonality follows directly because the alternating cube sum of every
polynomial of degree below three is zero.  A codimension-one subspace
$c^\perp$ meets every open orthant except the two whose signs are
$\pm\mathrm{sign}(c)$.  Those two excluded sign patterns are parity
and its complement.

For completeness, the count of one-head patterns can be certified without a
table.  The eight central hyperplanes in affine-parameter space have normals
$(1,x_1,x_2,x_3)$, one for each cube vertex.  Their normal-span lattice has,
by rank, Möbius sums

$$
 1,-8,28,-44,23;
$$

at rank three there are twelve flats of Möbius value $-3$ and eight of
value $-1$, while the other ranks have respectively
$1,8,28,1$ flats.  Thus the characteristic polynomial is
$t^4-8t^3+28t^2-44t+23$, whose value at $-1$ is 104.  The elementary
hyperplane-region recurrence therefore gives 104 strict affine sign
patterns.  Hence, among the 256 three-bit functions, those 104 use at most
one head, parity and its complement use three, and the remaining 150 use
exactly two.

There is also a complete, computer-assisted four-bit classification:

$$
 H^\ast(f)=\mathrm{tdeg}(f)
 \quad\text{for every nonconstant }f:\lbrace 0,1\rbrace^4\to\lbrace 0,1\rbrace. \tag{20e}
$$

The finite certificate uses exact oriented-matroid arithmetic.  For a
rational evaluation subspace $V\subseteq\mathbb R^{16}$, write a basis of
$V^\perp$ as a matrix with row $c_x$ at vertex $x$.  By the strict
theorem of alternatives, $V$ misses the open orthant $y$ exactly when
there is a nonzero $w$ such that

$$
                         y_x\langle c_x,w\rangle\ge0
 \quad\text{for every }x.                                \tag{20f}
$$

The compatibility cone in (20f) is pointed because the $c_x$'s span the
normal space.  If nonempty, it therefore has an extreme ray cut out by
$c-1$ independent row hyperplanes, where $c=\mathrm{codim}V$.
Enumerating those row intersections and all sign choices at zero coordinates
lists the missed orthants exactly.

`selftests/four_bit_exhaustive` carries out that enumeration with rational
arithmetic.  It proves that the degree-at-most-two polynomial evaluation
space meets 57,574 orthants and that the intersection of the missed sets of
twelve explicit admissible two-head spaces is empty on those orthants.  It
also proves that six explicit admissible three-head spaces collectively meet
all 65,534 nonparity orthants.  The denominator lists are part of the
certificate; one exceptional mixed-orientation pair is additionally checked
by direct affine numerators with exact margin $7/377$.

The same verifier computes the affine arrangement characteristic polynomial
directly from the matroid subset formula:

$$
 t^5-16t^4+120t^3-460t^2+820t-465.
$$

It has 1,882 regions.  Thus, when $H=0$ is allowed for constants, the exact
small-input distributions are

| input bits | 0 heads | 1 head | 2 heads | 3 heads | 4 heads |
|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 2 | 0 | 0 | 0 |
| 2 | 2 | 12 | 2 | 0 | 0 |
| 3 | 2 | 102 | 150 | 2 | 0 |
| 4 | 2 | 1,880 | 55,692 | 7,960 | 2 |

Now (13a) says that the other two orthants are parity and its complement,
which have four heads by the symmetric theorem.  Equation (13) supplies the
matching lower bound at degrees two and three, while (12) handles degree one.
This proves (20e) without a floating-point feasibility decision.  Together
with (11b), it also proves $H^\ast(f)=\mathrm{tdeg}(f)$ for every
nonconstant four-junta, regardless of the ambient input dimension.

## 6. A lower bound from communication sign rank

Partition the variables into $u$ and $v$, and let $M_f$ be the sign
matrix $M_f(u,v)=\chi_f(u,v)$.  The evaluation matrix of any affine form is

$$
 L(u,v)=A(u)+B(v),
$$

so it has ordinary matrix rank at most two.  Entrywise products multiply rank
bounds, since the outer-product decompositions of two matrices give all
pairwise outer products after taking their entrywise product.  Each summand
in (3) is a product of $H$ affine forms and hence has
matrix rank at most $2^H$.  Summing the $H$ terms gives a real matrix of
rank at most $H2^H$ with sign pattern $M_f$.  Therefore

$$
 \mathrm{signrank}(M_f)\le H^\ast(f)2^{H^\ast(f)}
 \le2^{2H^\ast(f)},                                          \tag{21}
$$

and in particular, if $L=\log_2\mathrm{signrank}(M_f)\ge1$,

$$
 H^\ast(f)\ge L-\log_2 L.                                    \tag{22}
$$

Indeed, any smaller $H\lt L-\log_2L$ also has
$\log_2H\lt\log_2L$, contradicting
$H+\log_2H\ge L$.  The simpler $H^\ast(f)\ge L/2$ remains valid but loses a
logarithmic additive term rather than just a constant.

This lower bound is genuinely different from threshold degree.  For an
explicit separation, let $R=2^r$, index coordinates by
$a,b\in\lbrace 0,1\rbrace^r$, and let

$$
 A_{ab}=(-1)^{a\cdot b}
$$

be the $R\times R$ Walsh-Hadamard sign matrix.  On $2R$ input bits
$u=(u_a)$, $v=(v_b)$, define

$$
 F_r(u,v)=1
 \quad\Longleftrightarrow\quad
 \sum_{a,b}A_{ab}u_av_b-\frac12\gt 0.                        \tag{23}
$$

Equation (23) is a strict degree-two polynomial threshold representation.
On the restriction $u=e_a,v=e_b$, its sign matrix is exactly $A$.  The
standard spectral sign-rank bound for a Walsh-Hadamard matrix gives
$\mathrm{signrank}(A)\ge\sqrt R$.  Sign rank cannot increase when
passing to a submatrix, so (21)--(22) yield

$$
 H^\ast(F_r)\ge
 \min\lbrace h\in\mathbb N:h2^h\ge2^{r/2}\rbrace
 \ge \frac r2-\log_2\frac r2                            \tag{24}
$$

for $r\ge2$, with integer rounding understood.

For sufficiently large $r$, this lower bound exceeds one.  Equation (12)
then rules out threshold degree one, while (23) supplies degree two; hence
$F_r$ has exact threshold degree two.  Thus threshold degree two does not
imply bounded head complexity even for an explicit family.

The rank argument is not inherently bipartite.  Partition the variables into
$k\ge2$ blocks and let $\mathrm{signrank}_k(T_f)$ be the least CP
tensor rank of a real $k$-tensor with the sign pattern of the corresponding
truth-table tensor.  An affine form is a sum of $k$ tensors, each depending
on just one block, so its CP rank is at most $k$.  Entrywise products
multiply CP-rank bounds and sums add them.  Applying this to (3) gives

$$
 \mathrm{signrank}_k(T_f)\le H^\ast(f)k^{H^\ast(f)}.      \tag{24a}
$$

Consequently, with
$L_k=\log_k\mathrm{signrank}_k(T_f)\ge1$,

$$
                         H^\ast(f)\ge L_k-\log_kL_k.         \tag{24b}
$$

This supplies multipartition lower bounds that can be stronger than any one
matrix flattening; (21)--(22) are exactly the $k=2$ case.

There is a much larger (nonexplicit) separation already inside the same
bilinear family.  For every sign matrix
$A\in\lbrace-1,1\rbrace^{m\times m}$, define on $2m$ bits

$$
 F_A(u,v)=1
 \quad\Longleftrightarrow\quad
 \sum_{i,j=1}^m A_{ij}u_iv_j-\frac12\gt 0.                  \tag{25}
$$

These are $2^{m^2}$ distinct strict degree-two threshold functions, because
their restrictions to $(u,v)=(e_i,e_j)$ recover the sign matrices $A$.
On just these $L=m^2$ restricted inputs, the cleared scores of an
$H$-head model are degree $H$ polynomials in

$$
 K=2H(2m+1)\le6Hm
$$

normal-form parameters.  If $L\ge K$, the polynomial sign-pattern bound
(Warren's theorem, stated in the next section) gives at most

$$
 \left(\frac{4eHL}{K}\right)^K
 \le (em)^{6Hm}                                           \tag{26}
$$

patterns.  For
$H\le m/(12\log_2(em))$, this is at most $2^{m^2/2}$, fewer than the
$2^{m^2}$ choices of $A$.  Consequently, for all sufficiently large
$m$, some degree-two function on $2m$ bits satisfies

$$
 H^\ast(F_A)\gt\left\lfloor\frac{m}{12\log_2(em)}\right\rfloor.
                                                                    \tag{27}
$$

For large $m$ this lower bound exceeds one, so (12) shows that the selected
function is not a linear threshold function; its threshold degree is
therefore exactly two.  In particular, the gap between threshold degree and
head complexity is
$\Omega(n/\log n)$ on $n$-bit functions of threshold degree two.  The
same count shows that a uniformly random sign matrix $A$ has this property
with probability tending to one (after reducing the constant if necessary).

The existential choice can be made canonical and computable, though not
efficient.  Order the $m\times m$ sign matrices lexicographically and take
the first $A$ for which $H^\ast(F_A)$ exceeds the displayed bound.  Existence
is (26), while the quantifier-elimination procedure (11a) decides each
candidate exactly.  Thus (27) yields a uniform recursive family of explicit
truth tables, not only a choice requiring an oracle or a random draw.

The separation is not peculiar to degree two.  Fix $d\ge2$, take $d$
blocks of $m$ Boolean variables, and for every sign tensor
$A\in\lbrace-1,1\rbrace^{[m]^d}$ define

$$
 F_A(u^{(1)},\ldots,u^{(d)})=1
 \quad\Longleftrightarrow\quad
 \sum_{i_1,\ldots,i_d}A_{i_1\cdots i_d}
       \prod_{j=1}^d u^{(j)}_{i_j}-\frac12\gt 0.             \tag{27a}
$$

This is a strict degree $d$ threshold representation.  On the product of
the $d$ one-hot restrictions, it recovers all $2^{m^d}$ sign tensors.
There are $L=m^d$ restricted inputs and
$K=2H(dm+1)=O_d(Hm)$ normal-form parameters.  Warren's bound gives only

$$
 2^{O_d(Hm\log m)}
$$

head-model sign patterns there.  It follows that, for every fixed $d$, some
function on $N=dm$ bits with threshold degree at most $d$ requires

$$
                         H^\ast(F_A)=\Omega_d
                         \left(\frac{N^{d-1}}{\log N}\right).           \tag{27b}
$$

The tensor can be chosen to have threshold degree exactly $d$.  Indeed, on
the one-hot grid, restrictions of all degree-at-most $(d-1)$ polynomials lie
in a linear space of dimension at most

$$
 R=\sum_{s=0}^{d-1}\binom ds m^s\le2^d m^{d-1}.
$$

An $R$-dimensional score space meets at most
$2\sum_{j=0}^{R-1}\binom{m^d-1}{j} =2^{O_d(m^{d-1}\log m)}$
open orthants.  This is a negligible fraction of
the $2^{m^d}$ sign tensors, as is the low-head class at the width used in
(27b).  Choose $A$ outside the union of those two classes.  Its displayed
polynomial gives threshold degree at most $d$, while the orthant count rules
out degree $d-1$.  Thus fixed threshold degree $d$ permits head complexity
$\Omega_d(N^{d-1}/\log N)$ for every fixed $d\ge2$.

## 7. Exponential worst-case head complexity

The preceding explicit separation is logarithmic.  A semialgebraic counting
argument shows that the worst case is exponential.

For $H\ge1$, absorb the overall constant score into one affine numerator.
Also scale each numerator-denominator pair by the positive number
$D_h(0)^{-1}$, so that every denominator constant is one.  This does not
change any fraction.  The normalized form uses at most

$$
 K=H(2n+1)
$$

real coefficients: $n+1$ for each $N_h$ and $n$ remaining coefficients
for each $D_h$.
For each of the $M=2^n$ input vertices, the cleared expression (3) is a
polynomial of degree at most $H$ in these $K$ parameters.  Ignoring all
positivity and coherent-sign restrictions can only enlarge the family.
Models with fewer than $H$ heads are included by padding with zero
numerators, so it suffices to count this one parameter family.

The polynomial sign-pattern bound (Warren's theorem) says that $M$ real
polynomials of degree at most $H$ in $K$ variables, with $M\ge K$, have
at most

$$
 \left(\frac{4eHM}{K}\right)^K
 =\left(\frac{4eM}{2n+1}\right)^{H(2n+1)}                 \tag{28}
$$

strict sign patterns.  For $n\ge4$, the base-two logarithm of (28) is at
most

$$
 H(2n+1)\left(n+\log_2\frac{4e}{2n+1}\right)
 =(2+o(1))Hn^2.                                           \tag{29}
$$

For example, when $n\ge5$, $4e\lt 2n+1$, so the exponent is at most
$(2+1/n)Hn^2$.  Fix any $\varepsilon\gt 0$ and take
$H\le(1/2-\varepsilon)M/n^2$.  For sufficiently large $n$, $K\lt M$ and
the exponent in (29) is at most
$(1-2\varepsilon+o(1))M\lt M$.  Since there are $2^M$ Boolean functions,

$$
 \max_{f:\lbrace 0,1\rbrace^n\to\lbrace 0,1\rbrace}H^\ast(f)
 \ge\left(\frac12-o(1)\right)\frac{2^n}{n^2}.             \tag{30}
$$

Indeed, (29) shows more: the fraction of functions computable at this width
is at most $2^{-(2\varepsilon-o(1))M}$, so a uniformly random Boolean
function obeys the same lower bound with overwhelming probability.  It is
nonparity with the same probability, so by (13a) the hard function can
simultaneously be chosen to have threshold degree at most $n-1$.

For each fixed rational $\varepsilon\gt 0$, lexicographically enumerating truth
tables and applying (11a) selects a canonical computable function above the
$(1/2-\varepsilon)2^n/n^2$ width for every sufficiently large $n$.  The
asymptotic lower bound is therefore effective in this quantified sense even
though the counting proof does not give a short closed formula for the truth
table.

Together, (17d''') and (30) give

$$
 \left(\frac12-o(1)\right)\frac{2^n}{n^2}
 \le \max_f H^\ast(f)
 \lt\frac32\frac{2^n}{n}
 \qquad(n\ge8).                                          \tag{31}
$$

Every Boolean function has threshold degree at most $n$, but (30) gives
functions with exponentially larger head complexity.  This proves that the
shared-factor width in (3), rather than polynomial or rational degree by
itself, is the essential extra resource.

## 8. Geometric formulation

There is a standard algebraic-geometric reading of the shared-factor form.
Homogenize affine forms using a new variable $x_0$, and put
$Q=\prod_{h=1}^H D_h$.  Then

$$
 \left.\frac{d}{d\varepsilon}
   \prod_{h=1}^H(D_h+\varepsilon N_h)
 \right|_{\varepsilon=0}
 =\sum_{h=1}^H N_h\prod_{k\ne h}D_k=P.                  \tag{31a}
$$

Thus (3) is precisely an element of the image of the tangent map to the Chow
variety of completely reducible degree $H$ forms, at the base point
$Q$.  (Using the parametric tangent image avoids any ambiguity at singular
points with repeated factors.)  Attention selects a particular real
semialgebraic locus of base points: after dehomogenization every factor is
positive on the cube and has coherent nonconstant coefficients.  Equivalently,
$H^\ast(f)$ is the least degree at which the Boolean sign orthant of $f$
contains the evaluation of such a positive Chow-tangent vector.

Let

$$
 \mathcal V_n=
 \left\lbrace\left(\frac{N(x)}{D(x)}\right)_{x\in\lbrace 0,1\rbrace^n}:
 N\text{ affine},\ D\text{ attention-positive}\right\rbrace
 \subset\mathbb R^{2^n}.
$$

If $\mathcal O_f$ is the open orthant with sign vector $\chi_f$, then

$$
 H^\ast(f)=\min\lbrace H:(\mathcal V_n+\cdots+\mathcal V_n)
                    \cap\mathcal O_f\ne\varnothing\rbrace.     \tag{32}
$$

So, geometrically, head complexity is an **orthant secant rank** of the
linear-fractional evaluation family.  Algebraically it is the positive
shared-factor threshold width (3).  Equations (4), (5), (22), and (31) locate
this invariant relative to classical Boolean complexity measures and show
why none of the degree notions alone captures it.  Parity makes it
exponentially smaller than $0/1$-threshold sparsity, while random functions
make it exponentially larger than threshold degree.
