# Approach Registry

This registry groups the proof search by mathematical mechanism.  A route is
marked **blocked** when its next step is as strong as the original problem; it
is reopened only when a new mechanism appears.

No public search or external solution source was used in any route below.

## A. Scalar linear-fractional normal form — complete

At the query token, the query vector is input-independent.  After composing a
head with the output projection and final readout, its scalar contribution has
the form

$$
  \frac{a_h+\sum_i b_{hi}x_i}
       {c_h+\sum_i d_{hi}x_i},
$$

where the denominator is positive on the cube and its nonconstant
coefficients are either all positive or all negative.  The converse is proved
with shared token/positional embeddings, not merely asserted.

Concrete result: an exact, dimension-free normal-form theorem for $H^\ast(f)$.
For each fixed $H$, the theorem gives a finite existential-real feasibility
system over affine numerator and denominator coefficients; together with the
universal upper bound, this is an exact truth-table decision procedure for
$H^\ast(f)$, and candidate-width membership lies in the existential theory of
the reals.  All inequalities are strict, so any real certificate can be
perturbed to a rational one.
The same perturbation proves exact dummy-variable invariance: the complexity
of a junta equals that of its core function.

## B. Algebraic denominator clearing / threshold degree — complete

Multiplying a sum of $H$ linear-fractional terms by the product of their
positive denominators gives a polynomial threshold representation of degree
at most $H$.

Concrete result: $\mathrm{tdeg}(f)\le H^\ast(f)$, with both
Boolean-cube multilinearization and zero-margin issues audited.

This route alone cannot characterize $H^\ast$: every Boolean function has
threshold degree at most $n$, while a separate parameter-counting route is
proved to give functions with exponentially many required heads.
More sharply, the degree $(n-1)$ evaluation space is the hyperplane
orthogonal to parity, so parity and its complement are the only functions of
threshold degree $n$; all other orthants already meet that hyperplane.

## C. Symmetry, alternation, and partial fractions — complete

For a symmetric function, symmetrizing a threshold polynomial reduces it to a
univariate polynomial in Hamming weight.  Its minimum degree is the number of
adjacent sign changes.  Conversely, a degree $a$ sign polynomial divided by
$\prod_{h=1}^a(k+t_h)$ has a partial-fraction expansion using $a$ heads.

Concrete result:

$$
 H^\ast(f)=\lvert\lbrace k:f(k)\ne f(k+1)\rbrace\rvert
$$

for every nonconstant symmetric Boolean function.

Cross-pollination with the Cauchy route gives a broader one-sided theorem.
If $f$ depends only on an affine statistic whose nonconstant coefficients
are strictly coherent, then its head complexity is at most the number of
label changes across the ordered attainable statistic levels.  Mixed-radix
encoding consequently gives
$H^\ast(f)\le\prod_j(n_j+1)-1$ for functions symmetric within blocks of sizes
$n_j$.  No matching lower bound is inferred without a transitive
symmetrization argument.

## D. Cauchy interpolation / universal construction — complete

Encode each vertex by the distinct scalar
$z(x)=\sum_i2^{i-1}x_i$.  The functions
$1,1/(z+t_1),\ldots,1/(z+t_{2^n-1})$ form a basis on the $2^n$ nodes by a
Cauchy-polynomial argument.

Concrete result: the universal bound $H^\ast(f)\le 2^n-1$, with actual
attention parameters available from the normal-form converse.

The same finite-level interpolation gives a composition theorem without
pretending that thresholded one-head outputs can simply be fed to another
gate.  If $g_j=\mathbf1[L_j\gt 0]$ and each affine $L_j$ has coherent
nonconstant coefficients and $r_j$ distinct cube values, then intersections
and unions of the $g_j$'s need at most $\sum_j(r_j-1)$ heads.  In
particular, $M$ unit-weight cardinality gates need at most $Mn$ heads.

## E. Semialgebraic geometry / orthant secant rank — complete

The evaluation vector of one head lies on a rational semialgebraic family in
$\mathbb R^{2^n}$.  An $H$-head classifier asks whether an $H$-fold
Minkowski sum of this family meets the open orthant prescribed by $f$.
After homogenization, the cleared polynomial is also the differential of
$\prod_h(D_h+\varepsilon N_h)$ at zero: it lies in the parametric tangent
space to the Chow variety of products of $H$ linear forms, based on the
attention-positive real locus.  This identifies shared-factor width with a
positive Chow-tangent threshold invariant rather than merely renaming the
architecture.

Concrete result: polynomial sign-pattern counting after denominator clearing
proves the existence of functions with
$H^\ast(f)=\Omega(2^n/n^2)$.  This is independent of threshold-degree lower
bounds and demonstrates genuinely width-like behavior.
Normalizing each positive denominator by $D_h(0)$ removes one redundant
parameter per head.  The resulting sign-pattern exponent is
$(2+o(1))Hn^2$, giving the sharpened bound

$$
 \max_f H^\ast(f)\ge
 \left(\frac12-o(1)\right)\frac{2^n}{n^2}.
$$

For every fixed $\varepsilon\gt 0$, the fraction computable below
$(1/2-\varepsilon)2^n/n^2$ is exponentially small in $2^n$.

There is a concrete ceiling on the black-box semialgebraic version of this
proof mechanism.  It sees $K=\Theta(Hn)$ parameters, polynomial degree
$H$, and $M=2^n$ tests.  The generic sign-pattern exponent is

$$
 K\log\left(\frac{HM}{K}\right)
 =\Theta(Hn^2),
$$

because $H$ cancels inside the logarithm.  Comparing with the $2^M$ truth
tables therefore stops at $H=\Theta(2^n/n^2)$, exactly the proved order.
Closing the remaining factor $n$ requires exploiting the shared-product
structure beyond a theorem that sees only parameter count and total degree;
it cannot come from tightening constants in the same Warren calculation.

Cross-pollination with bilinear PTFs gives a stronger degree separation:
among the $2^{m^2}$ functions
$\mathrm{sign}(\sum A_{ij}u_iv_j-1/2)$, all of threshold degree at
most two, sign-pattern counting on the one-hot restriction proves that some
require $\Omega(m/\log m)$ heads.
The same one-hot argument tensorizes: for every fixed $d\ge2$, some exact
threshold-degree $d$ functions on $N$ bits require
$\Omega_d(N^{d-1}/\log N)$ heads.  A separate orthant count for the
degree $(d-1)$ one-hot evaluation space makes the degree exact.
The exact feasibility procedure from route A also makes the existential
families effective: lexicographically enumerate coefficient sign tensors (or
truth tables) and select the first candidate that fails the desired width.
This is a canonical recursive construction, albeit not an efficient or
closed-form one.

## F. Finite differences and Fourier structure — blocked

Study mixed differences of $N/D$, possible sign-regularity of reciprocal
affine functions, and Fourier constraints on sums of heads.

Mixed-difference formulas for $N/D$ were derived, but the arbitrary affine
numerator destroys the complete-monotonicity enjoyed by $1/D$.  Along a
maximal chain $x^{(0)},\ldots,x^{(n)}$, numerator increments can prescribe
arbitrary one-head values exactly: set
$N(x^{(k)})=y_kD(x^{(k)})$ and recover the affine coefficients from
successive differences.  The surviving constraints collapse to degree after
denominator clearing.

Two exact counterexamples already rule out Fourier sparsity itself: parity is
a single Walsh character but needs $n$ heads, while the AND sign function
has all $2^n$ Walsh coefficients nonzero and needs one head.

Blocked gap: a Fourier or finite-difference invariant that survives arbitrary
affine numerators and is additive over heads.  Reopen only if such an invariant
is proposed.

## G. Fixed-denominator linear algebra / computational checks — mixed

For fixed positive denominators, fitting head numerators is a linear problem.
Exact rational-rank checks for the family
$(a+\sum b_i x_i)/(z+t_h)$ show nontrivial dependencies; for small $n$,
the first full interpolation widths observed were
$1,2,3,4,7,12$ for $n=1,\ldots,6$ with the tested dyadic encoding and
integer poles.

These computations are sanity checks only.  No rank pattern is promoted to a
theorem without an exact proof.

One small case did survive exact audit.  For $n=3$, the fixed denominators
$D_1=1+x_1+x_2+x_3$ and $D_2=1+2x_1+3x_2+4x_3$ give a seven-dimensional
score space (an explicit minor is $1/14515200$).  Its normal vector is
$(-1)^{|x|}D_1(x)D_2(x)$, so the only missed orthants are parity and its
complement.  This proves the full three-bit classification
$104$ threshold functions / $150$ exact two-head functions / $2$
exact three-head functions.

The four-bit probe was subsequently replaced by an exact computer-assisted
proof.  A rational normal-space covector enumeration shows that twelve
explicit admissible two-head spaces cover all 57,574 degree-at-most-two
orthants, and six explicit three-head spaces cover all 65,534 nonparity
orthants.  The verifier uses only `Fraction` arithmetic and the extreme rays
of pointed compatibility cones; no floating tolerance remains.  Together
with the degree lower bound, this proves
$H^\ast(f)=\mathrm{tdeg}(f)$ for every nonconstant four-bit function.
The full denominator certificate is in `selftests/four_bit_exhaustive`.
The same exact script evaluates the affine-arrangement characteristic
polynomial and obtains the head-count distribution
$2,1880,55692,7960,2$ at widths $0,1,2,3,4$.

A stronger experiment fixes independent generic coherent denominators and
uses all affine numerators.  Exact rational ranks for $n\le6$ reach the full
$2^n$-dimensional function space at
$H=\lceil(2^n-1)/n\rceil$.  Every head contributes at most $n$ new
numeric dimensions because $D_h/D_h=1$.

These finite certificates are theorems.  Rational reductions handle
$n\le6$, the coding proof handles $n=8$, and explicit full-rank reductions
modulo $10^9+7$ at $n=7,9,10,11,12$ imply nonzero rational minors because
all integer denominators remain nonzero modulo the prime.  The larger cases
are reproduced by `selftests/interpolation_modular_large`.  Together with the
dimension lower bound they prove
$I_n=\lceil(2^n-1)/n\rceil$ for every $1\le n\le12$.
The uniform extrapolation is not promoted from this finite sequence.

Status of this improved universal upper bound: **blocked**.  Proving that the
generic quotient subspaces $\mathrm{Aff}/D_h$ are nondefective is a
theorem-strength secant/interpolation lemma.  Numerical rank is not accepted
as proof.  The audited theorem instead gets the correct $\Theta(2^n/n)$
numeric-interpolation order from route J, without claiming the sharp generic
dimension-count constant.

A later, genuinely different one-parameter degeneration was also tested.
Put $z(x)=\sum_i2^{i-1}x_i$ and coalesce denominators of the form
$1+t_hz(x)$ at $t_h=0$.  Its limiting block-Krylov space is

$$
 \mathrm{span}\lbrace x_i z^k:1\le i\le n,\ 0\le k\lt H\rbrace.
$$

This would have supplied a confluent-Vandermonde proof if it reached the
dimension count.  It does not: at $n=6,H=11$, exact rational elimination
gives rank $62$, not $63=2^6-1$.  The counterexample is reproduced in
`selftests/run`.  Thus the binary subset-sum osculating route is **blocked**;
independent denominator directions, as in the successful finite
certificates, are essential at least for this degeneration.

The route was reopened once using a genuinely new mechanism and then blocked
again.  Expanding $x_i/(1+t_h\cdot x)$ at small $t_h$ turns the leading
matrix into generic gradient evaluation for multiaffine polynomials.  A
matroid partition shows that the raw dimension count has no subset-density
obstruction, but completion requires the nondefectivity theorem

$$
 q\mapsto(\nabla q(t_1),\ldots,\nabla q(t_H))
\quad\text{has rank }\min(2^n-1,nH)
$$

at generic points.  Coordinate degenerations reduce to hypercube-neighborhood
coverings and do not prove this for all $n$.  This missing lemma is exactly
the claimed improvement, so it is not treated as routine and the route is
blocked.

A second reopening used the constant vector common to all quotient spaces.
Neighborhood localization need only cover all but one cube vertex, since the
last coordinate vector is the all-ones vector minus the others.  This proves
the sharp result $I_3=3$: the centers $000,001,010$ cover seven of the
eight vertices.  It does not solve the general problem.  Already in $Q_5$,
seven centers (the dimension-count width) cover at most 29 vertices.  To see
this exactly, split centers by parity.  The largest opposite-parity boundary
of $k=0,1,2,3,\ge4$ same-parity centers has size respectively
$0,5,10,13,16$; maximizing the two boundary sizes over a total of seven
centers gives 29.  Thus at least three coordinates remain uncovered, and the
common constant repairs only one.  With no further multiscale mechanism, this
reopening is blocked rather than promoted to generic nondefectivity.

## H. Communication/sign-rank and restriction reductions — complete

Partition variables and view a score table under restrictions.  Test whether
the linear-fractional structure gives matrix-rank, sign-rank, or variation
diminishing bounds not already implied by threshold degree.

Concrete result: after positive denominator clearing, each affine
factor has matrix rank at most two across any bipartition.  Hadamard products
multiply rank, so an $H$-head sign matrix has sign rank at most
$H2^H$, and hence

$$
 H^\ast(f)\ge L-\log_2L,
 \qquad L=\log_2\mathrm{signrank}(M_f).
$$

This route is not a restatement of threshold degree.  A bilinear polynomial
built from an explicit Hadamard sign matrix has threshold degree at most two,
while its one-hot restriction supplies a growing sign-rank lower bound.
For a $k$-block partition, the same proof with CP tensor rank gives
$\mathrm{signrank}_k(T_f)\le Hk^H$ and hence
$H\ge L_k-\log_kL_k$ when $L_k\ge1$, providing a genuinely multiparty version rather than
only matrix flattenings.

## I. Sparse polynomial thresholds / reciprocal endpoint bumps — complete

For every nonempty $S\subseteq[n]$, the admissible one-head function

$$
 b_{S,\delta}(x)=
 \frac{\delta}{\delta+\sum_{i\in S}(1-x_i)
       +\delta^2\sum_{i\notin S}(1-x_i)}
$$

converges uniformly on the Boolean cube to the monomial $x_S$ as
$\delta\downarrow0$.  Consequently, a strict polynomial threshold
representation with $M$ nonconstant monomials gives an $M$-head model.
The positive-oriented dual bump converges to
$\prod_{i\in S}(1-x_i)$.  Allowing either endpoint monomial independently
in a threshold score defines endpoint sparsity $\mathrm{espr}$, and
the same proof gives $H^\ast(f)\le\mathrm{espr}(f)$.

Concrete result:

$$
  \mathrm{tdeg}(f)\le H^\ast(f)
  \le \mathrm{spr}_{0/1}(f),
$$

where sparsity is in the positive $0/1$-monomial basis and the constant
monomial is not counted.  This route also gives a second, structurally
different proof of the universal $2^n-1$ upper bound.

The upper bound is not an equivalence: Möbius inversion shows that every
strict parity threshold polynomial has all $2^n$ coefficients nonzero, so
$\mathrm{spr}_{0/1}(\mathrm{PARITY}_n)=2^n-1$, whereas route C gives
$H^\ast(\mathrm{PARITY}_n)=n$.
Expanding a mixed term in either the $x$-monomial basis or the
$(1-x)$-monomial basis yields the sharper nonmonotone DNF bound
$H^\ast\le\sum_j2^{\min\lbrace p_j,q_j\rbrace}$, where $p_j,q_j$ count its two literal
polarities, and the analogous bound for CNF violation terms.

Cross-pollination with finite-level interpolation also handles intersections
and unions of completely arbitrary, mixed-sign affine thresholds.  Interpolate
each gate's zero-one output by a univariate polynomial on its attainable affine
levels, sum those exact gate indicators with margin $1/2$, and apply endpoint
sparsity.  If gate $j$ has support $S_j$ and $r_j$ levels, the resulting
head count is at most the size of
$\bigcup_j\lbrace S:\varnothing\ne S\subseteq S_j,|S|\le r_j-1\rbrace$.
This is a general polynomial fallback; route D's reciprocal construction is
sharper when the thresholds themselves have coherent slopes.

## J. Hypercube-neighborhood localization — complete

For a cube vertex $v$, the affine form
$L_v(x)=d_H(x,v)-1$ vanishes exactly on its $n$ neighbors.  The scaled
quotient $\varepsilon N/(L_v+\varepsilon)$ therefore limits to the
restriction of an affine numerator on that neighborhood and to zero
elsewhere.  Since the neighbors are affinely independent, one denominator
localizes an arbitrary $n$-vector there.

An open-neighborhood cover consequently gives full numeric interpolation.
The first construction has mixed denominator signs, but a nonzero evaluation
minor is a rational function of denominator coefficients; its cleared
numerator cannot vanish throughout the open all-positive coefficient cone.
This transfers full rank to attention-admissible denominators.
After clearing row denominators, the minor polynomial has total degree at
most $2^nH$; therefore it is already nonzero somewhere on the finite
positive grid $\lbrace 1,\ldots,2^nH+1\rbrace^{H(n+1)}$.  Thus the transfer has a
finite integer search version and is not merely a generic-existence claim.

Selecting each center with probability $\ln(n)/n$ and adding one center for
each uncovered vertex proves

$$
 H^\ast(f)\le\gamma_o(Q_n)
 \le\left\lceil\frac{2^n(\ln n+1)}n\right\rceil.
$$

The probabilistic alteration above already supplies
$O(2^n\log n/n)$ without the blocked generic-nondefectivity lemma in route
G.  A coding construction is stronger.  Take
$r=\lfloor\log_2 n\rfloor$, put every $r$-bit syndrome (including zero)
among the columns of a parity-check matrix, and repeat columns to reach length
$n$.  For every vertex, flipping a coordinate labeled by its syndrome
moves it into the kernel.  The zero column also gives every codeword a
distinct codeword neighbor, so this single kernel is an open-neighborhood
cover.  This proves the deterministic universal bound

$$
 H^\ast(f)\le2^{n-\lfloor\log_2n\rfloor}\lt\frac{2^{n+1}}n,
$$

and the audited worst-case upper $O(2^n/n)$.

A genuinely new multi-coset mechanism improves the rounding constant
uniformly after finite base cases are lifted.  If parity-check columns
$A\subseteq\mathbb F_2^r$ and target syndromes
$T\subseteq\mathbb F_2^r$ obey $T+A=\mathbb F_2^r$, the union of the
$|T|$ syndrome fibers is an open-neighborhood cover of size
$|T|2^{n-r}$.  Two exact six-bit covers are

$$
 \begin{aligned}
 A_{12}&=\lbrace 17,18,20,23,26,31,34,39,56,58,61,63\rbrace,&
 T_7&=\lbrace 0,6,10,20,22,48,49\rbrace,\cr
 A_{14}&=\lbrace 6,11,20,25,33,34,35,43,46,47,52,53,62,63\rbrace,&
 T_6&=\lbrace 0,4,7,8,43,57\rbrace.
 \end{aligned}
$$

They obey $T_7+A_{12}=T_6+A_{14}=\mathbb F_2^6$ and both column sets
span.  A further seven-bit certificate is

$$
 A_{13}=\lbrace 0,3,4,14,20,52,66,89,95,96,110,115,126\rbrace,\quad
 T_{12}=\lbrace 0,1,13,40,69,78,83,97,104,112,120,125\rbrace.
$$

It obeys $T_{12}+A_{13}=\mathbb F_2^7$, and $A_{13}$ spans.
Cartesian lifting and column repetition use the $12/7$ cover on
$[1.5\cdot2^k,1.625\cdot2^k)$ and the $13/12$ cover above
$1.625\cdot2^k$; the single kernel handles the lower half.  The resulting
uniform theorem is

$$
 H^\ast(f)\lt\frac32\frac{2^n}{n}\qquad(n\ge8).
$$

The elementary cover lower bound $\gamma_o(Q_n)\ge\lceil2^n/n\rceil$
shows that the constructed open dominating sets are within a strict factor
$3/2$ of optimal.  This is a cover optimality comparison, not a head lower
bound.
All base covers and their Cartesian lifts are verified by finite XOR
coverage, not inferred from solver silence or a random-search extrapolation.
The 14-column count for six target syndromes is also optimal inside
$\mathbb F_2^6$.  After translating $T$ to contain zero, its five
remaining vectors have only five linear-dependence types up to
$\mathrm{GL}(6,2)$.  Exhaustive translate unions on their spans show lower
bounds $14,16,16$ for ranks five, four, and three.  This closes the concrete
13-by-6 refinement without claiming that the global $3/2$ constant is
optimal over unrelated cover constructions.

Together with the shared-constant dimension lower bound, the same construction
determines the fixed-denominator interpolation width exactly as
$I_n=2^n/n$ whenever $n\ge2$ is a power of two.
`selftests/run` also records full-rank finite-field certificates for explicit
positive integer denominators at
$(n,H)=(7,19),(8,32),(9,57)$, independently checking the positive-cone
transfer's concrete implication.  All three attain the dimension lower bound;
the separate large verifier continues the sharp certificates through $n=12$.

## K. Variable-identification minors / addressing — complete

For the address function $\mathrm{IDX}_r(a,y)=y_a$, identify every
data bit $y_b$ with either one new bit $z$ or its complement according to
the parity of $b$.  The resulting function is parity on $r+1$ variables,
so restriction by affine identification proves threshold degree, and hence
head complexity, at least $r+1$.  The usual exact selector polynomial gives
the matching threshold-degree upper bound.

A square Cauchy mechanism first gives a $2^r$-head upper bound: reciprocal
affine functions form a basis on the address cube, and each affine numerator
can carry independent coefficients for all data bits.  A small coherent
perturbation restores strict denominator coefficients without crossing the
fixed margin.

Concrete result:

$$
 \mathrm{tdeg}(\mathrm{IDX}_r)=r+1,
 \qquad r+1\le H^\ast(\mathrm{IDX}_r)\le2^r-1
 \quad(r\ge2).
$$

The improvement by one is uniform and genuinely uses data-dependent
denominators.  For the rectangular Cauchy matrix with poles
$1,\ldots,2^r-1$, take its left-null vector $c$ and a Cauchy combination
$B$ supported at the two even address nodes $0,2^{r-1}$.  Its residues
$\beta_h$ alternate in sign.  Therefore the exactly cancelling
address-affine numerators $U_h=\beta_ha_1$ have first-order quotient
coordinates of both signs.  Positive data coefficients can match every
coordinate $c_b$; the remainder lies in the Cauchy column space.  A
rational $\varepsilon$-perturbation then converges uniformly to the selector
score $y_a$.  This supplies a proof for every $r\ge2$, rather than an
extrapolation from computed ranks.

The first cases sharpen to
$H^\ast(\mathrm{IDX}_1)=2$,
$H^\ast(\mathrm{IDX}_2)=3$, and, by the exact certificate below,
$H^\ast(\mathrm{IDX}_3)=4$.  No extrapolation of exact equality with
threshold degree is made for $r\ge4$.

For $r=3$, a direct four-head search was rationalized into an exact integer
certificate.  One denominator has positive orientation and three have
negative orientation; every denominator stays strictly positive.  Exact
substitution on all 2,048 inputs gives signed margin greater than $537/1000$,
so the threshold-degree lower bound is attained:

$$
                    H^\ast(\mathrm{IDX}_3)=4.
$$

The executable `selftests/address_three_bit_four_heads` contains the fixed
integer rows and verifies the exact margin.  The preceding five-head
higher-codimension perturbation was useful as a bridge, but is superseded by
this smaller certificate.

The direct certificate does not reveal a sparse identity that can simply be
continued to larger $r$.  Exact Möbius inversion of its cleared degree-four
polynomial gives support counts
$1,11,55,165,330$: every one of the 562 monomials of degree at most four is
present.  Thus the tempting claim
$H^\ast(\mathrm{IDX}_r)=r+1$ for all $r$ is **blocked** beyond $r=3$
until a new structural construction or lower-bound mechanism appears; the
finite equality itself is fully proved.

The Cauchy upper bound is provably optimal inside the data-independent-
denominator closure: the address-by-data coefficient matrix has rank at most
$H$, while correctness for every data vector makes it strictly diagonally
dominant and hence rank $2^r$.  A possible improvement must use data
coefficients in the denominators.

An earlier, stronger attempt at width $H=2^r-1$ asked for surjectivity of
the entire first-order map from all cancellation relations.  Exact
calculations show full rank for $r=2,3,4,5$, but a uniform proof of that
stronger statement is
still blocked.  It is no longer needed for the theorem: the explicit
two-point relation above supplies one pair of opposite quotient signs, which
is exactly the weaker mechanism the selector construction requires.

At $r=3,H=4$, the same first-order cone mechanism is provably blocked.  The
normal space and the set of quotient generators both have dimension four.
If the four generators span, their positive cone is pointed; if they do not,
they miss some normal direction.  But the eight normal rows have a strictly
positive dependence (use any positive Cauchy column as the weights), so no
pointed cone contains all of them.  This rules out only this singular
first-order construction, not an arbitrary four-head model; it is not used as
a lower bound in the answer.  The exact mixed-orientation four-head
certificate above demonstrates concretely why that mechanism-specific
obstruction could not be promoted to impossibility.

## L. Algebraic composition / higher tangent order — mixed

Cleared scores multiply safely for XOR and XNOR because only their signs
matter.  If $H^\ast(f)=H$ and $H^\ast(g)=K$, their product has degree at most
$H+K$.  Multiplication followed by the endpoint-bump construction proves
the concrete bound

$$
 H^\ast(f\mathbin{\mathsf{XOR}}g)
 \le\sum_{j=1}^{\min\lbrace H+K,n\rbrace}\binom nj.
$$

The tempting stronger rule $H^\ast(f\mathsf{op}g)\le H+K$ is **blocked**
for general Boolean operations.  Algebraically, the product of the two Chow
tangent scores is a mixed second derivative of the product base form, whereas
an $H+K$-head representation is only a first tangent vector.  For AND and
OR there is an even more elementary obstruction to the naive proof: adding
strict scores does not combine their signs because their positive and
negative magnitudes are uncontrolled.  Reopen this route only with a genuine
score-normalization construction or an identity returning the mixed tangent
to the admissible first-tangent locus.

## M. Directed edge boundaries / exterior minors — blocked as subsumed

Along an edge in coordinate $i$, one head obeys the exact identity

$$
 \Delta_i(N/D)
 =\frac{b_iD^0-d_iN^0}{D^0D^1}.
$$

The numerator is affine in the other variables; its coefficients are the
$2\times2$ exterior minors $b_id_j-d_ib_j$ of the numerator and
denominator coefficient rows.  For $H$ heads, clearing the positive edge
denominators produces a sum of one affine factor times $H-1$ products
$D_k^0D_k^1$.

Clearing gives the exact rank estimate
$\mathrm{psr}(B_{f,i})\le2H4^{H-1}$ for the partial sign matrix of
directed bichromatic edges.  However, adversarial comparison kills it as a
new lower bound.  If $S=[S^0\ S^1]$ is a rank $r$ sign-rank witness for
the original truth table under the partition that groups $x_i$ with the
second side, then $S^1-S^0$ has rank at most $2r$ and has the required
sign on every bichromatic edge.  Hence

$$
 \mathrm{psr}(B_{f,i})
 \le2\mathrm{signrank}(M_f),
$$

and route H already yields a stronger head lower bound.

The edge identity remains a concrete structural calculation and is tested
exactly, but rank alone has been exhausted.  This route is blocked unless a
new mechanism exploits the shared Plücker relations rather than discarding
them into ordinary rank; the dominated inequality is intentionally absent
from the answer's theorem statements.

## Audit ledger

- **Normal-form necessity:** proved by composing $W_O,W_V$ with the readout
  and using the input-independent query; the bit-induced key/value changes are
  position-independent.
- **Normal-form sufficiency:** proved with a shared $(n+2)$-dimensional
  embedding and scalar heads.  The exact parameter identities are checked in
  `selftests/run` for both denominator orientations.
- **Zero-logit-shift heads:** handled by first making the finite classifier
  margin strict and then perturbing the denominator while holding its affine
  numerator fixed.  No constant-denominator expressivity is lost.
- **Threshold-degree lower bound:** complete; it uses only positivity of the
  denominator product and Boolean multilinearization.
- **Sparse upper bound:** complete in the $0/1$ monomial basis; each endpoint
  bump has all denominator coefficients strictly negative.  The basis
  convention is explicit in `answer.md`.
- **Mixed-sign threshold compositions:** complete via exact Lagrange
  interpolation on each gate's finite set of affine levels, Boolean
  multilinearization, and the sparse upper bound.  This route never treats a
  mixed-sign affine score as an admissible attention denominator.
- **Symmetric theorem:** complete; lower bound is permutation averaging plus
  root counting, upper bound is a literal partial-fraction construction.
- **Sign-rank theorem:** complete modulo the standard spectral sign-rank bound
  for the explicit Walsh-Hadamard corollary.  The general inequality follows
  directly from ranks of Hadamard products.
- **Counting theorems:** complete modulo Warren's standard polynomial
  sign-pattern bound.  Positivity restrictions are discarded only in the
  enlarging direction, every denominator constant is normalized using
  $D_h(0)\gt 0$, and smaller head counts are included by zero-numerator padding.
- **Sharp generic interpolation at
  $\lceil(2^n-1)/n\rceil$:** blocked and absent from the answer's theorem
  statements.  Route J proves the asymptotic $\Theta(2^n/n)$ interpolation
  width by a different construction.
- **Neighborhood localization:** complete; the only limiting step proves a
  nonzero finite minor for sufficiently small $\varepsilon$, and the
  polynomial-open-cone argument restores strict attention admissibility.
- **Multi-coset neighborhood covers:** complete; the two six-bit and one
  seven-bit column sets span, their XOR sumsets cover all 64 or 128 syndromes,
  Cartesian lifting preserves coverage, and repeated columns extend the
  certified intervals.  The five-type translate enumeration proves
  optimality of 14 columns only for six target syndromes in the six-bit base
  group; no global cover optimality is claimed.
- **Addressing theorem:** complete; the parity identification proves the
  degree lower bound.  Alternating residues of an explicit two-point Cauchy
  relation prove the $2^r-1$ upper bound for every $r\ge2$, and positivity
  of every perturbed denominator coefficient is built into the construction.
  The fast exact verifier reconstructs the positive first-order solve and
  evaluates the resulting finite $\varepsilon$ classifier on every input
  through three address bits, rather than checking only the residue signs.
  The optimal four-head, three-address-bit instance is also exhaustively
  checked with rational arithmetic.
- **Four-bit exhaustive theorem:** complete; the missed-orthant criterion is
  a strict theorem of alternatives, all extreme-ray covectors are enumerated
  over the rationals, and both finite denominator covers are checked by
  `selftests/four_bit_exhaustive`.
