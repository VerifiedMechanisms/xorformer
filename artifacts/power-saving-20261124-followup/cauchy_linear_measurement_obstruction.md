# Positive reciprocal heads can have many linear-measurement branches

## Scope

This is an obstruction to replacing Boolean point-evaluation constraints by arbitrary linear measurements of the full score table in a branch-counting argument. It is not an obstruction to a bound that uses the actual Boolean labels or coordinate evaluations. Every head below is admissible in the original model, and every displayed score table is strictly positive.

The theorem and regularity argument are written proofs. The small example is independently checked with exact rational arithmetic by [the verifier](verify_cauchy_measurements.py). No new Lean declaration is claimed in this note.

## A reciprocal curve with prescribed positive intersections

Let $m\geq2$ and let $r_1,\ldots,r_{m-1}$ be distinct positive real numbers. Put

$$ P(s)=\prod_{j=1}^{m-1}(s-r_j),\qquad Q(s)=\prod_{t=1}^{m}(s+t),\qquad c_t=\frac{P(-t)}{\prod_{u\neq t}(u-t)}. $$

The elementary partial-fraction identity gives

$$ F(s):=\sum_{t=1}^{m}\frac{c_t}{s+t}=\frac{P(s)}{Q(s)}. $$

For completeness, multiplying by $Q$ gives two polynomials of degree at most $m-1$. At each of the $m$ distinct points $-1,\ldots,-m$, only one summand on the left survives, and the chosen residue makes its value equal to $P$. Polynomial interpolation proves the identity. This is the same algebraic mechanism as the repository's kernel-checked `real_partial_fraction`; the instantiation here remains written.

The curve $s\mapsto((s+t)^{-1})_{t=1}^{m}$ lies entirely in the positive orthant when $s\gt0$. Nevertheless the single linear hyperplane with normal $(c_t)$ intersects it at all the prescribed positive points. These are simple intersections, because

$$ F'(r_j)=\frac{P'(r_j)}{Q(r_j)}\neq0. $$

Positivity therefore does not turn arbitrary linear sections of a reciprocal feature family into sections of degree polynomial in the number of input bits.

## A full Boolean-cube branch construction

Choose positive integers $d,k$ and set $n=d+k$ and $m=2^d$. Write the Boolean input as $(y,z)$ and define

$$ t(y)=1+\sum_{a=1}^{d}2^{a-1}y_a,\qquad \phi_b(y,z)=\frac1{t(y)+\sum_{i=1}^{k}b_i z_i},\qquad b_i\gt0. $$

The address statistic takes every value $1,\ldots,m$ exactly once. Let $y(t)$ be the corresponding address. For each selector $i$, define one fixed linear measurement of an arbitrary full-cube real table $v$ by

$$ L_i(v)=\sum_{t=1}^{m}c_t v(y(t),e_i). $$

The coefficient vector is fixed before choosing $b$. The measurements of the head are

$$ L_i(\phi_b)=F(b_i). $$

Consequently the map from the $k$ positive parameters $b_i$ to the $k$ measurements has exactly

$$ (m-1)^k $$

positive preimages of the zero measurement vector. Each parameter is independently one of the prescribed roots. The Jacobian is diagonal with nonzero entries $F'(b_i)$, so all these preimages are regular and isolated. The full-cube tables themselves are distinct: at $(0,e_i)$ their values are $(1+b_i)^{-1}$, which determine every parameter.

Every denominator has strictly positive constant and slope coefficients. For a literal original-model realization, write the slopes as $w_1,\ldots,w_n$, let $A=\sum_jw_j\gt0$, and take

$$ \alpha=1+2A,\qquad \rho_j=\frac{w_j}{2A},\qquad \gamma=\frac12,\qquad \eta=1,\qquad \delta=0,\qquad m_j=0. $$

Then $\gamma+\sum_j\rho_j=1$, $(\alpha-1)\rho_j=w_j$, and the numerator is constantly one. Thus these are genuine single heads. Alternatively, admissibility follows directly from `FracAtom.ofPositiveAffineRatio_eval`.

Taking $k=d$ gives $n=2d$ and

$$ \log_2\bigl((2^d-1)^d\bigr)\geq d(d-1)=\frac{n^2}{4}-\frac n2. $$

This rules out any uniform upper bound of the form $\exp(O(n\log n))$ on the number of positive regular branches of arbitrary linear measurement maps even for one head.

## Why this does not count Boolean targets

Every coordinate of every displayed table is positive. All branches represent the same constant-true Boolean function, which already has a width-zero representation. None of the measurement equations is an individual score equation. In fact no individual score coordinate vanishes anywhere in the parameter family.

Thus the construction does not refute a small bound for positive fibers of a selected *coordinate-evaluation* map. It does not refute a sample-compression theorem whose support constraints are actual labelled inputs, and it does not estimate the universally low-margin class. A proof that introduces arbitrary dual hyperplanes must account for these extra branches instead of identifying their number with truth-table capacity.

The Boolean address cost is also explicit: making one independent parameter have $m-1$ roots uses $d=\log_2m$ address coordinates; only $k=n-d$ selectors remain. Applying independent copies to many heads would require a proved way of isolating those heads in the coordinate constraints. The present construction provides no such isolation.

## Exact four-bit instance

Take $d=k=2$, roots $1,2,3$, and residues

$$ (c_1,c_2,c_3,c_4)=(-4,30,-60,35). $$

Then

$$ -\frac4{s+1}+\frac{30}{s+2}-\frac{60}{s+3}+\frac{35}{s+4}=\frac{(s-1)(s-2)(s-3)}{(s+1)(s+2)(s+3)(s+4)}. $$

The two measurements have nine distinct regular positive preimages. The scalar derivatives at the three roots are respectively $1/60,-1/360,1/420$. The verifier checks the polynomial identity, both measurements, the nine nonzero Jacobian determinants, the full sixteen-entry tables, and the literal original atom formula using only rational arithmetic.
