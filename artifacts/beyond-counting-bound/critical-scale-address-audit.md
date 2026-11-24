# Address Budgets at Exponential Head Counts

## Target and scope

The current target is an unconditional eventual bound in the unchanged model: there exist fixed $\varepsilon\gt0$, $c\gt0$, and $n_0$ such that

$$ W(n)\geq c\frac{2^n}{n^{2-\varepsilon}}\qquad(n\geq n_0). $$

This note does not prove that statement. It audits a proposed obstruction to a stronger full-cube sign count, including the integer rounding. Component multiplicity, real-valued tables, and strict Boolean labelings are kept distinct.

The source is [the signed-residue construction on branch ar/0f08fe6fb98a](https://github.com/VerifiedMechanisms/xorformer/blob/ad4b30e10e5a5d6d0f1e025f2af6bddce8019931/artifacts/head-compression/continuation-lower-bound.tex), read at the pinned commit. The [denominator-information audit](https://github.com/VerifiedMechanisms/xorformer/blob/ad4b30e10e5a5d6d0f1e025f2af6bddce8019931/artifacts/head-compression/exponent-precision.tex) and [unconditional baseline audit](https://github.com/VerifiedMechanisms/xorformer/blob/2672bc2f68e854622722d26b91a86e42e1ccab31/artifacts/head-compression/reverse-alternative-counting-audit.tex) were also read directly. The finite denominator-library hypothesis in the former does not restrict the real parameters in this run.

## Exact rounding and multiplicity bounds

Fix real $x\gt0$ and $c\gt0$. For an integer $n\geq4$, set

$$ L=x\log_2 n-\log_2 c,\qquad S=\lceil L\rceil,\qquad r=n-S,\qquad H=2^r. $$

Assume $2\leq S\leq\lfloor n/2\rfloor$. These conditions hold for every sufficiently large $n$, for each fixed pair $x,c$. Then

$$ \frac{c2^n}{2n^x}\lt H\leq\frac{c2^n}{n^x},\qquad H\geq2^{n/2},\qquad S=\log_2(2^n/H). $$

**Proof.** The ceiling inequalities give $L\leq S\lt L+1$. Exponentiating $n-L-1\lt n-S\leq n-L$ gives the first pair. The second follows from $S\leq n/2$, and the last is an identity. The eventual range follows from $L\to\infty$ and $L/n\to0$. $\blacksquare$

Let $C=(H!)^S$ be the signed-residue component count and $Q=(H!)^{S-1}$ its number of orbits under simultaneous head relabeling. The following finite inequalities hold in the stated range:

$$ \frac1{16}Hn\log_2(2^n/H)\leq\log_2 Q\leq\log_2 C\leq Hn\log_2(2^n/H). $$

**Proof.** Since $H=2^r\geq4$, the largest $H/2$ factors in $H!$ are at least $H/2$. Consequently

$$ \frac H2(r-1)\leq\log_2(H!)\leq Hr. $$

Use $r\geq n/2$, hence $r-1\geq n/4$, and $S-1\geq S/2$. These give the lower bound. The upper bound uses $r\leq n$. Substitute the exact identity for $S$. $\blacksquare$

In particular, for fixed $x,c$,

$$ \log_2 Q=\Theta(Hn\log n),\qquad \log_2 C=\Theta(Hn\log n). $$

For $1\lt x\lt2$, these quantities are $\Theta(2^n\log n/n^{x-1})=o(2^n)$. Also $H\leq2^n/(10n)$ eventually, because $n^{x-1}\geq10c$ eventually. Thus the construction genuinely reaches the proposed exponential-head range after rounding, while its multiplicity remains on the proposed entropy scale.

## What the source construction establishes

There are $2HS$ free parameters. On the $HS$ inputs $(u,e_j)$ the zero equations split into independent Cauchy interpolation systems. All denominator slopes are strictly negative, and every denominator exceeds $3/4$ throughout the full cube. Arbitrary signed residues are allowed. The source proves regularity and exactly $C$ connected components, each of dimension $HS$.

The diagonal action of the head-permutation group is free on the tuples of strict pole orders. Fixing the first order leaves $Q$ orbits. Hence quotienting by one simultaneous permutation does not eliminate the factorial growth.

However, the logarithm per free parameter is of order $n$, whereas the logarithm per unrestricted-model parameter is only of order $\log n$ at this scale. Indeed the free-parameter count is $2HS$, and the unrestricted normalized count is $2nH$. Confusing these two dimensions would incorrectly turn the component construction into an obstruction to the critical-scale proposal.

For an additional symmetric query at scalar argument $d$, the interpolation identity is

$$ -1+\sum_h\frac{c_h}{d-b_h}=-\frac{\prod_i(d-d_i)}{\prod_h(d-b_h)}. $$

For $d\gt\max_h b_h$, its sign away from the prescribed roots depends only on the fixed interpolation nodes. Permuting the poles does not change it. This statement concerns symmetric extra queries; it does not assert that every multi-selector query has the same sign.

## Comparison with this run's matching construction

In [the pole-matching construction](pole-matching-fibers.md), the address length is $d=\lceil\log_2(2H)\rceil=r+1$ and the remaining selector count is $k=n-d=S-1$. Thus the displayed inequivalent matching count is $(H!)^{S-2}$. If $S\geq4$, the same factorial estimates give

$$ \frac1{16}HnS\leq\log_2\bigl((H!)^{S-2}\bigr)\leq HnS. $$

Here the whole constructed family of matchings has one Boolean sign pattern: the score is zero when every selector is zero and positive otherwise. The distinctness theorem concerns real-valued tables. It supplies no distinct-label count.

## A count for the restricted signed-residue family

There is also a direct sign-count audit that does not count components. Keep the common binary address form fixed as in the source, but allow all $2HS$ residue and selector-pole parameters to vary in their full admissible domain. Write $N=2^n$ and suppose $2HS\leq N$. Clearing denominators at all $N$ inputs gives polynomials of degree at most $H$ in those $2HS$ parameters. Warren's theorem therefore bounds the number of strict full-cube labelings in this restricted family by

$$ \log_2|\mathcal F^{\mathrm{address}}_{n,H}|\leq2HS\log_2(2eN/S). $$

For $n\geq4$ and $S\geq2$, the right side is at most $3nHS$. At the fixed-exponent scale with $x\gt1$, the condition $2HS\leq N$ holds eventually since $2HS/N\leq2cS/n^x\to0$.

This is a rigorous restricted-family upper count, not a new bound on the full admissible class. In particular, it does not account for independently varying the address slopes in every head. The missing argument is precisely a count for that unrestricted adaptive family, not the factorial component estimate above.

## Status of the proposed full-cube estimate

The proposed estimate is still unproved:

$$ \log_2|\mathcal F_{n,H}|\leq CnH\bigl(1+\log_2(2^n/H)\bigr),\qquad 2^{n/2}\leq H\leq2^n/(10n). $$

Neither component construction refutes it. Neither proves it. An attempted extension from the fixed address family would have to control the independent denominator slopes without imposing denominator sharing, bounded precision, or a relative margin. No such extension is established here. This is a theorem-strength gap, not a lemma that can be assumed in a proof of the target.

The imported Warren modules have been rebuilt locally. Their explicit eventual baseline is still $W(n)\geq2^n/(70n^2)$ for $n\geq16$. The rounding and restricted-family calculations in this note are complete written arguments; they are not new Lean declarations or an exponent improvement.
