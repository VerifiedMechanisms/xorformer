# A finite-order filtered lift on a fixed positive grid

## Status and scope

This is a written unconditional finite-dimensional theorem about signed direction clouds. It is not a theorem that repairs the relative margin of an arbitrary original-model score. In particular, adding the exact zero-score correction below need not increase the margin. The theorem permits arbitrary real direction coordinates and arbitrary signed real residues.

The correction preserves every scalar function of every Boolean projection, not only finitely many moments. Its additional directions belong to a fixed positive integer grid. Its width cost is negligible compared with the critical exponential widths when the order is at most a suitable positive constant times the input dimension.

The proof is elementary polynomial interpolation. The accompanying rational computation checks one instance. The finite-moment-to-arbitrary-kernel implication is kernel checked in `FilteredMomentLift.lean`; the simplex interpolation construction and its asymptotic consequence remain written proofs.

## The finite theorem

Let $d,r,H$ be nonnegative integers, and let $V$ be any subset of $\lbrace0,1\rbrace^d$. Fix a vector $v\in\mathbb Z_{\gt0}^d$, arbitrary vectors $w_1,\ldots,w_H\in\mathbb R^d$, and arbitrary real residues $c_1,\ldots,c_H$. Suppose

$$ \sum_{h=1}^H c_h(w_h\cdot x)^j=0\qquad\text{for every }x\in V\text{ and }0\leq j\leq r. $$

Write

$$ \Lambda_{d,r}=\lbrace\beta\in\mathbb Z_{\geq0}^d:|\beta|\leq r\rbrace,\qquad D=|\Lambda_{d,r}|=\binom{d+r}{r}. $$

There are real residues $a_\beta$, indexed by this fixed set, with both following properties.

1. The auxiliary cloud is an exact Boolean-projection ghost. For every $x\in V$ and every function $F:\mathbb R\to\mathbb R$,

$$ \sum_{\beta\in\Lambda_{d,r}}a_\beta F((v+\beta)\cdot x)=0. $$

2. Subtracting this ghost removes every ordinary multivariate moment through order $r$. For every polynomial $p$ of total degree at most $r$,

$$ \sum_{h=1}^H c_hp(w_h)-\sum_{\beta\in\Lambda_{d,r}}a_\beta p(v+\beta)=0. $$

Thus the original cloud and a cloud with at most $H+D$ terms have exactly the same Boolean projections, while the replacement has ordinary order of vanishing at least $r+1$. All auxiliary coordinates are strictly positive integers.

## Proof by simplex-grid interpolation

For a real variable $u$ and an integer $k\geq0$, use the polynomial

$$ \binom uk=\frac{u(u-1)\cdots(u-k+1)}{k!},\qquad\binom u0=1. $$

For $\beta\in\Lambda_{d,r}$ define the polynomial

$$ L_\beta(t)=\left(\prod_{i=1}^d\binom{t_i}{\beta_i}\right)\binom{r-\sum_i t_i}{r-|\beta|}. $$

Its total degree is at most $r$. For every $\gamma\in\Lambda_{d,r}$ one has $L_\beta(\gamma)=1$ if $\gamma=\beta$, and zero otherwise. Indeed, if some $\gamma_i\lt\beta_i$, the corresponding factor vanishes. Otherwise $\gamma\geq\beta$ coordinatewise; if they differ, then $r-|\gamma|\lt r-|\beta|$, so the final factor vanishes.

There are exactly $D$ monomials of total degree at most $r$, and the $D$ displayed polynomials are linearly independent because their evaluations on the grid form the identity matrix. They are therefore a basis of that polynomial space. Consequently every polynomial $p$ of degree at most $r$ satisfies

$$ p(w)=\sum_{\beta\in\Lambda_{d,r}}p(v+\beta)L_\beta(w-v). $$

Set

$$ a_\beta=\sum_{h=1}^H c_hL_\beta(w_h-v). $$

Multiplying the interpolation identity by $c_h$ and summing gives property 2.

To prove property 1, fix $x\in V$. Since $x$ is Boolean and $|\beta|\leq r$, every auxiliary projection belongs to the set

$$ \lbrace v\cdot x,v\cdot x+1,\ldots,v\cdot x+r\rbrace. $$

Property 2, applied to $p(w)=(w\cdot x)^j$, and the assumed moment identities give zero auxiliary projection moments for $j=0,\ldots,r$. The Vandermonde matrix on the $r+1$ displayed distinct real numbers is invertible. Hence the total auxiliary residue at each projection value is zero. Summing an arbitrary function $F$ against these grouped residues proves property 1. This includes projections whose support is smaller than $r+1$. $\blacksquare$

## Positive affine denominators and the original model

For affine shifts $D_h(x)=w_{h0}+\sum_{i=1}^n w_{hi}x_i$, apply the theorem in dimension $d=n+1$ to the Boolean query set

$$ V=\lbrace(1,x):x\in\lbrace0,1\rbrace^n\rbrace. $$

Use $v=(1,\ldots,1)$. The auxiliary shifts have strictly positive intercept and slopes, all bounded by $r+1$. For any fixed base value $B(x)$ and scale $\varepsilon$ at which the denominators are nonzero, property 1 gives the exact identity

$$ \sum_{\beta\in\Lambda_{n+1,r}}\frac{a_\beta}{B(x)+\varepsilon(v+\beta)\cdot(1,x)}=0. $$

If $B$ is a positive constant, every auxiliary denominator is strictly positive and has strictly positive slopes for $\varepsilon\gt0$. Each term, with numerator $a_\beta$ or $-a_\beta$, is therefore a genuine original-model atom by the positive affine-ratio constructor.

More generally, if $B$ is positive on the full cube and has strictly positive slopes, the same conclusion holds. If its slopes are all strictly negative, then for all sufficiently small positive $\varepsilon$ they remain strictly negative, and positivity on the finite cube also persists. The negative affine-ratio constructor then applies. Constant numerators meet the original restriction whenever a denominator is constant. Thus no inadmissible auxiliary head is needed.

The equality is exact on the entire Boolean cube, so arbitrary signed cancellation with other parts of the score is preserved. The theorem does not bound the relative margin after adding these heads. The next section extends the construction to fixed affine numerators without imposing separate cancellation on their coefficients.

## Extension to affine numerators

Suppose each original numerator is an arbitrary fixed affine function $A_h(x)$, and the combined projection moments satisfy

$$ \sum_h A_h(x)(w_h\cdot(1,x))^j=0\qquad(0\leq j\leq r). $$

Use the same simplex interpolation basis in dimension $d=n+1$, and define the auxiliary affine functions

$$ A_\beta(x)=\sum_h L_\beta(w_h-v)A_h(x). $$

For every direction polynomial $p$ of degree at most $r$, interpolation gives, pointwise in $x$,

$$ \sum_h A_h(x)p(w_h)=\sum_\beta A_\beta(x)p(v+\beta). $$

In particular, the combined auxiliary projection moments vanish through degree $r$. Their projection values still occupy at most $r+1$ distinct integers. Apply the same Vandermonde argument, now with the real residues $A_\beta(x)$ at the fixed input $x$. For every scalar kernel $F$ one obtains

$$ \sum_\beta A_\beta(x)F((v+\beta)\cdot(1,x))=0. $$

Consequently the auxiliary affine-numerator heads sum exactly to zero for the reciprocal kernel as well. Subtracting them preserves the whole score and removes every ordinary numerator-weighted direction moment through degree $r$. Every numerator remains affine, and the positive or negative affine-ratio constructor still makes each new head admissible.

This argument does not require the projection moments to vanish separately for each original numerator coefficient. Cancellation of the combined values at every Boolean input is sufficient. The correction numerators are linear combinations of the original numerators with coefficients independent of the input.

Without the projection-vanishing hypothesis, the same interpolation formulas still give an exact decomposition into the positive-grid score and a remainder whose ordinary numerator-weighted moments through order $r$ vanish. In that version the grid score need not be zero, so discarding it would not preserve labels.

## Width at critical exponential scales

Put $d=n+1$ and $r=\lfloor d/4\rfloor$. For $r\gt0$, the elementary binomial estimate gives

$$ D=\binom{d+r}{r}\leq\left(\frac{e(d+r)}r\right)^r\leq(5e)^{d/4}\lt15^{d/4}. $$

The middle inequality follows because $s\log(e(d+s)/s)$ is increasing for $s\gt0$, so it can be evaluated at $s=d/4$. The last inequality uses $e\lt3$.

Since $15^{1/4}\lt2$, for every fixed exponent $p\gt0$,

$$ D=o(2^n/n^p). $$

In particular, this correction has vanishing relative width cost at both $H=\Theta(2^n/n^{3/2})$ and $H=\Theta(2^n\log n/n^2)$. This is an additive-width statement only. It does not prove a margin repair at either scale.

## Coefficient size for bounded directions

The interpolation coefficients are explicit polynomials of degree at most $r$ in the original direction coordinates. A crude bound suffices to show that the positive grid does not conceal an arbitrary coefficient precision requirement when the original cloud is bounded.

Suppose $|w_{hi}-v_i|\leq R$ for every coordinate. For $r\geq1$, put $M=2r+dR+1$. Every factor in the falling-factorial numerator of $L_\beta(w_h-v)$ has absolute value at most $M$. Therefore

$$ |L_\beta(w_h-v)|\leq\frac{M^r}{(r-|\beta|)!\prod_i\beta_i!}. $$

The multinomial identity, with the additional coordinate $r-|\beta|$, gives

$$ \sum_\beta|a_\beta|\leq\left(\sum_h|c_h|\right)\frac{((d+1)M)^r}{r!}. $$

For $r=O(n)$, $d=n+1$, and $R$ polynomially bounded in $n$, the multiplicative coefficient mass is at most $\exp(O(n\log n))$. This estimate controls only the correction mass. It supplies no lower bound on the signed score of the original representation.

## What this resolves and what it does not

The exact ghost ideal permits a controlled positive-grid normal form through a linear in $n$ ordinary order. The seven-point plateau in `margin_repair_boolean_collision_moments.md` is one concrete input to this construction.

The required unrestricted lower bound still needs a mechanism beyond this theorem. Taking $r$ comparable to $\exp(\sqrt n)$ makes the grid much too large. Moreover, ordinary moment vanishing through a linear in $n$ order by itself does not bound the entropy of all higher collision jets. Fixed straight collisions were already covered by the inherited `RadialMomentTransfer.uniform_radial_sign_transfer`; the remaining challenge concerns arbitrary curved paths, multiple base denominators, affine numerator jets, or a different global capacity argument.

## Verification

`HeadComplexity.FilteredMomentLift.sum_kernel_eq_zero_of_finite_moments` proves that vanishing moments through order $r$, on any prescribed $r+1$ distinct projection values, annihilate every scalar function. `sum_kernel_eq_zero_of_integer_projection` specializes this to values in a translated integer interval. The hypotheses allow arbitrary real residues, multiplicities, and an entirely arbitrary scalar kernel.

The module build completed successfully with 3139 jobs. The transitive axiom audit for both declarations reports only `propext`, `Classical.choice`, and `Quot.sound`. The build and audit logs are `filtered_moment_lift_build.txt` and `filtered_moment_lift_axioms.txt`.

The script `filtered_lift_certificate.py` computes the simplex basis and correction for the seven-point order-three plateau. Its exact rational checks verify the cardinal interpolation matrix, all ordinary moments through degree three, and the zero grouped auxiliary residues at every Boolean query. The ten-point grid has only six nonzero correction residues in this instance. Its output is `filtered_lift_certificate.json`.
