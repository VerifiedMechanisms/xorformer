# Distinct Permutation Levels with Deep Cancellation

## Statement and scope

The near-coincident permutation family can have deep cancellation even when its levels are all distinct and positive. Its uncentered permutation sum can have a power-of-two head count; subtracting the symmetric mean costs three more heads. An analytic deformation of an independent product grid gives a linear, rather than exponential, head cost for the desired vanishing order.

**Theorem 1.** Let $q\geq4$ be a power of two, put $H=q^2$ and $L=q(q+1)/2$, and choose $2\leq m\leq L-1$. There exist $H$ distinct positive real numbers $\alpha_h$ and a permutation $\pi$ of $[H]$ such that

$$ \sum_{h=1}^H(\alpha_h+\alpha_{\pi(h)})^s=\frac1H\sum_{h,l=1}^H(\alpha_h+\alpha_l)^s\qquad(0\leq s\leq m), $$

but this equality fails at $s=m+1$. For every $c\gt0$, the mean-centered actual two-input head family with levels $\beta_h=1+\epsilon\alpha_h$ therefore has a zero of exactly order $m+1$ at $\epsilon=0$ at input $(1,1)$.

For any prescribed $m\geq2$, choosing the least allowable power of two gives $H\lt8(m+1)$. For $q\gt4$, this follows by applying minimality to $q/2$, giving $q^2/8+q/4\lt m+1$; the case $q=4$ follows from $m\geq2$. Equivalently, for every dyadic square $H=q^2$ with $q\geq4$, taking $m=L-1$ gives order $(H+\sqrt H)/2$. Thus no bound of order $\log H$, or of any fixed power $H^a$ with $a\lt1$, can universally truncate this Taylor expansion when input dimension is fixed at two.

There is only one potentially nonzero Boolean output after centering in this construction. It does not give a large sign family, a counterexample to the proposed full-cube count, or a lower bound on worst-case head complexity. It specifically tests the exceptional-level issue left by the [moment divisibility theorem](permutation-moment-divisibility.md).

## An independent grid as an exact base point

Index the levels by ordered pairs $(i,j)\in[q]^2$ and let $\pi(i,j)=(j,i)$. Define polynomials in $q^2$ real variables by

$$ F_s(\alpha)=\sum_{i,j=1}^q(\alpha_{ij}+\alpha_{ji})^s-\frac1{q^2}\sum_{i,j,k,l=1}^q(\alpha_{ij}+\alpha_{kl})^s. $$

The polynomials $F_0$ and $F_1$ vanish identically. Fix $u_i=3^i$, and put $\alpha^0_{ij}=u_i$. The $L$ sums $u_i+u_j$ for $i\leq j$ are pairwise distinct, as their base-three expansions show. At this point, the paired sum in the first term enumerates $u_i+u_j$ once for each pair. In the second term every $u_i+u_k$ occurs $q^2$ times before division by $q^2$. Consequently

$$ F_s(\alpha^0)=0\qquad(s\geq0). $$

The base levels repeat. The purpose of the deformation below is to break all repetitions while preserving precisely the first $m$ moment identities.

## The Jacobian has the needed independent directions

For $s\geq2$, direct differentiation at the base point gives

$$ (DF_s) _{ij}=2s\left((u_i+u_j)^{s-1}-\frac1q\sum_{l=1}^q(u_i+u_l)^{s-1}\right). $$

This formula also holds when $i=j$: differentiating $(2\alpha_{ii})^s$ gives the same factor of two.

**Lemma 2.** The covectors $DF_2,\ldots,DF_{m+1}$ are linearly independent whenever $m\lt L$.

**Proof.** For a proposed relation with coefficients $c_s$, set

$$ R(z)=\sum_{s=2}^{m+1}2s c_s z^{s-1}. $$

The zero-gradient equations say that $R(u_i+u_j)$ equals its mean across row $i$, for every $j$. Denote that mean by $r_i$. Symmetry in $i,j$ forces $r_i=r_j$ for all pairs. Thus $R$ takes one constant value at all $L$ distinct unordered pair sums. Since its degree is at most $m\lt L$, it is constant as a polynomial. Its constant coefficient is zero, so all the coefficients $c_s$ vanish. $\blacksquare$

Let $V$ be the common kernel of $DF_2,\ldots,DF_m$. Lemma 2 says that $DF_{m+1}$ is not identically zero on $V$.

**Lemma 3.** For any row $i$ and distinct columns $j,l$, the functional $v\mapsto v_{ij}-v_{il}$ is not identically zero on $V$ if $q\geq3$.

**Proof.** Every matrix $G$ in the span of the gradient covectors has the form $G_{ab}=S_{ab}-r_a$ with $S$ symmetric. Its antisymmetric part therefore has zero circulation on every three-cycle:

$$ (G_{ab}-G_{ba})+(G_{bc}-G_{cb})+(G_{ca}-G_{ac})=0. $$

The coordinate functional in the statement has matrix $E_{ij}-E_{il}$. If $i,j,l$ are distinct, its circulation on $(i,j,l)$ equals two. If one of $j,l$ equals $i$, choose a third index different from the other two; the corresponding circulation equals one or minus one. It therefore lies outside the span of the gradients. The annihilator of $V$ is exactly that span, proving the claim. $\blacksquare$

Choose $v\in V$ with

$$ DF_{m+1}(v)\neq0,\qquad v_{ij}\neq v_{il}\quad(i\in[q],\ j\neq l). $$

Such a vector exists because each forbidden equality defines a proper linear subspace of $V$, by the two lemmas, and a finite union of proper linear subspaces does not cover a vector space over the reals. One elementary proof of the last fact is to choose nonzero linear equations for the subspaces: their product is a nonzero polynomial and cannot vanish everywhere on a real vector space.

If the $u_i$ are rational, this step can be made by finite rational arithmetic. Compute a rational basis $v_1,\ldots,v_d$ for $V$ and test vectors $\sum_{a=1}^d t^{a-1}v_a$ at positive integers $t$. Each forbidden equation is a nonzero polynomial of degree at most $d-1$ in $t$, so a finite search succeeds with a proved bound on the number of excluded choices.

## An exact moment-preserving deformation

Apply the real analytic implicit function theorem to the map

$$ \Phi=(F_2,\ldots,F_m):\mathbb R^{q^2}\to\mathbb R^{m-1} $$

at $\alpha^0$. Its derivative has rank $m-1$, by Lemma 2. Thus $\Phi^{-1}(0)$ is a real analytic submanifold near $\alpha^0$, with tangent space $V$. A local analytic parametrization supplies a curve $\alpha(t)$ in that submanifold satisfying

$$ \alpha(0)=\alpha^0,\qquad\alpha'(0)=v,\qquad F_s(\alpha(t))=0\quad(2\leq s\leq m). $$

The next moment satisfies

$$ F_{m+1}(\alpha(t))=tDF_{m+1}(v)+O(t^2), $$

so it is nonzero for all sufficiently small nonzero $t$. Within a fixed row,

$$ \alpha_{ij}(t)-\alpha_{il}(t)=t(v_{ij}-v_{il})+O(t^2), $$

which is also nonzero for sufficiently small nonzero $t$. Between different rows the base values $u_i$ are already distinct; continuity keeps them distinct. Continuity also keeps every level positive. There are finitely many conditions, so one common sufficiently small positive $t$ satisfies them all. Fixing that value proves the moment assertion of Theorem 1.

This is an existence proof for exact real levels. It does not assert that an approximate numerical solution satisfies the moment equations, or that the resulting levels are rational. The model permits unrestricted real coefficients.

## Exact transfer to the admissible heads

For the levels just obtained, set $\beta_{ij}=1+\epsilon\alpha_{ij}$. They remain distinct and positive for every positive $\epsilon$. With $d=c+2$, define

$$ R(\epsilon)=\sum_{i,j}\frac1{d+\epsilon(\alpha_{ij}+\alpha_{ji})}-\frac1{q^2}\sum_{i,j,k,l}\frac1{d+\epsilon(\alpha_{ij}+\alpha_{kl})}. $$

This is the difference between the permutation sum and its independent-column mean at input $(1,1)$. Analytic expansion at zero yields

$$ R(\epsilon)=\sum_{s\geq0}\frac{(-1)^sF_s(\alpha)}{d^{s+1}}\epsilon^s. $$

The first nonzero coefficient is at order $m+1$, proving the claimed exact vanishing order. All the denominators in this expression are positive for positive $\epsilon$.

On the full two-bit cube the uncentered score is the sum of the $H$ heads

$$ (x_1,x_2)\longmapsto\frac1{c+\beta_{ij}x_1+\beta_{ji}x_2}. $$

Their slopes are strictly positive. At weights zero and one the permutation sum equals its independent-column mean exactly. The symmetric mean table on weights zero, one, and two can be subtracted with three actual reciprocal heads: choose three distinct positive $\gamma_l$ and interpolate the three mean values with $\sum_l a_l/(\gamma_l+x_1+x_2)$ using the nonsingular three-by-three Cauchy matrix. The usual polynomial-root proof of Cauchy nonsingularity is given in the [moment divisibility note](permutation-moment-divisibility.md).

Thus the full centered family has an exact $H+3$ head realization in the unchanged model. The permutation sum itself has $H$ heads, with $H$ a power of two. The distinction between these two counts matters. Tiny additional readout bias can remove the three zero outputs if strict labels are wanted, but the Taylor claim is about the mean-centered score before that bias.

## Consequences and limitations

There is a matching linear upper bound on the possible order in this two-column family.

**Theorem 4.** For any $H\geq2$ distinct real levels and any permutation, the mean-centered score is not identically zero, and its first nonzero Taylor order is at most $2H$. If the permutation is an involution with $f$ fixed points, the order is at most $H+f$.

**Proof.** Let $t_1,\ldots,t_R$ be the distinct paired sums $\alpha_h+\alpha_{\pi(h)}$, where $R\leq H$, and set $Q(t)=\prod_{r=1}^R(t-t_r)$. The uniform paired-sum measure gives expectation zero to $Q^2$. The independent-sum measure gives it strictly positive expectation: after ordering the distinct levels, the sums

$$ 2\alpha_1\lt\alpha_1+\alpha_2\lt\cdots\lt\alpha_1+\alpha_H\lt\alpha_2+\alpha_H\lt\cdots\lt2\alpha_H $$

give $2H-1\gt H\geq R$ distinct support points, all with positive mass. At least one is not a root of $Q$. Agreement of all moments through degree $2R$ would force the expectations of $Q^2$ to agree, a contradiction. Hence one of the moment differences through $2R$ is nonzero. The Taylor expansion transfers the same bound to the vanishing order. For an involution there are at most $(H+f)/2$ distinct paired sums, proving the refinement. $\blacksquare$

The construction and this upper bound determine the maximal order up to absolute constants along the dyadic-square widths: it is of order $H$. Repeated numerical levels are not essential. Prime-power head counts and generic nonvanishing do not control exceptional real levels. In particular, a uniform sublinear bound on the first nonzero Taylor order is false even with distinct positive slopes.

The centered table still has only one potentially nonzero Boolean value. High vanishing order is not sign entropy, and parameter degeneracy is not shattering. The construction supplies no unrestricted head lower bound and does not refute the proposed critical-width sign count. The original fixed-exponent target remains unproved.

## Verification boundary

The gradient formula, independence arguments, analytic deformation, positive-quadrature upper bound, and exact-model transfer form a complete written proof using the standard real analytic implicit function theorem. No Lean theorem for that deformation is claimed. The companion exact-arithmetic script multiplies the rational Jacobian by $q$ and verifies full row rank modulo a prime checked by trial division. These ranks also certify full row rank over the rationals. Augmented ranks check all the relevant tangent-space exclusions on the finite instances. No numerical moment solver or approximate-root certificate is used. A slower rational-elimination run was interrupted without a result; the modular certificates are the completed checks.
