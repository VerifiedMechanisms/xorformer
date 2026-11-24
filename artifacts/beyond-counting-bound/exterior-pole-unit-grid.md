# Two-Level Interpolation on an Arithmetic Grid

## Statement and scope

This note tests a proposed source of many sign extensions from regular unit-valued interpolation data. The obstruction below allows arbitrary residues, arbitrary bias, affine numerators, and poles on both sides of the sample interval. It concerns a single common affine address. It does not apply when different heads have independently chosen address slopes, or when an affine numerator in the address bits is not affine in the scalar address.

**Theorem 1.** Let $H\geq1$, $a\in\mathbb R$, and $d\gt0$. Suppose a nonconstant real function $F$ is a bias plus a sum of at most $H$ affine-over-affine functions of $t$, with all denominators strictly positive throughout $[a,a+(2H-1)d]$. If

$$ F(a+jd)\in\lbrace-1,1\rbrace\qquad(0\leq j\lt2H), $$

then $H\leq2$. If $H=2$, the reduced function has two distinct finite poles, one on each side of the sample interval, and a constant polynomial part.

In particular, with poles restricted to one side and constant polynomial part, the same interpolation condition forces $H=1$. Constant functions with value one or minus one are explicitly excluded.

This is a complete written theorem for the stated family. It does not improve the unrestricted worst-case head lower bound.

## A derivative zero bound

Combine coincident poles and divide each affine numerator by its denominator. The reduced expression has the form

$$ F(t)=ut+v+\sum_{i=1}^k\frac{r_i}{t-p_i}, $$

where the $p_i$ are distinct, lie outside the sample interval, and every $r_i$ is nonzero. Set $K=k$ if $u=0$, and $K=k+1$ otherwise. Nonconstancy gives $K\geq1$. Moreover, $K\leq H$: a nonzero linear polynomial part requires at least one original constant-denominator summand, whereas the finite poles require at least $k$ nonconstant-denominator summands.

**Lemma 2.** The function $F$ has at most $K$ zeros, and $F'$ has at most $K-1$ zeros, counted with multiplicity, in the sample interval.

**Proof.** Clearing the $k$ finite poles gives a nonzero numerator of degree at most $K$, proving the first assertion.

For the derivative, the functions $(t-p_i)^{-2}$ form an extended complete Chebyshev system on any interval containing no pole. Indeed, put $y_i=(t-p_i)^{-1}$. The Wronskian of any first $s$ such functions is

$$ \left(\prod_{i=1}^s y_i^2\right)\left(\prod_{j=0}^{s-1}(-1)^j(j+1)!\right)\prod_{1\leq i\lt j\leq s}(y_j-y_i), $$

which never vanishes. If the constant function one is prepended, expansion along its column gives the same Vandermonde argument, now with powers starting at $y_i^3$, so all initial Wronskians again remain nonzero.

For completeness, the zero-count implication follows by induction on the number of functions. Divide a linear combination by its nonvanishing first basis function and differentiate. The initial Wronskians of the resulting derivative basis are the corresponding original Wronskians divided by a power of the first function. The derivative basis therefore satisfies the same hypothesis with one fewer function. Rolle's theorem, with multiplicities, completes the induction. This applies to $F'$ using $k$ functions when $u=0$ and $k+1$ functions when $u\neq0$. $\blacksquare$

## The values must occur in paired runs

Write $M=2H$ and let $r$ count sign changes between consecutive prescribed unit values. Each change forces a zero of $F$. Each equality of consecutive values forces a zero of $F'$ between those two nodes. Lemma 2 gives

$$ r\leq K,\qquad M-1-r\leq K-1,\qquad 2H=M\leq2K\leq2H. $$

Thus $K=H$ and $r=H$. There are exactly $H+1$ constant-sign runs.

Choose a zero of $F$ between each pair of consecutive runs. Each of the $H-1$ interior runs lies between two such zeros and forces at least one derivative zero in that interval. If it has $L$ nodes, it also forces at least $L-1$ derivative zeros there by Rolle's theorem. An end run with $L$ nodes forces at least $L-1$ additional derivative zeros beyond the first or last chosen zero. These intervals are disjoint. The derivative budget is only $H-1$.

Consequently the end runs have length one, and each interior run has length at most two. Since the total length is $2H$, every interior run has length exactly two. Up to changing all signs, the sequence is

$$ -,+,+,-,-,+,+,-,\ldots. $$

Both signs occur exactly $H$ times. After an affine change of the variable, assume the grid is $0,1,\ldots,2H-1$. Let $Q_+$ and $Q_-$ be the monic polynomials whose roots are, respectively, the plus and minus nodes. Each has degree $H$.

## A root ratio is monotone on both exterior intervals

Define $R(t)=Q_+(t)/Q_-(t)$. It is positive on each exterior interval. Let $\varepsilon_j$ denote the prescribed sign at node $j$, choosing the first sign negative. Then

$$ E(z):=\sum_{j=0}^{2H-1}\varepsilon_j z^j=-(1-z)\sum_{i=0}^{H-1}(-z^2)^i=-\frac{(1-z)(1-(-z^2)^H)}{1+z^2}\lt0\qquad(0\lt z\lt1). $$

For $t\lt0$, integration of $z^{-t+j-1}$ gives

$$ \frac{R'(t)}{R(t)}=\sum_j\frac{\varepsilon_j}{t-j}=-\int_0^1z^{-t-1}E(z) dz\gt0. $$

The integral is finite for every such $t$. Reversing the node order multiplies the sign sequence by $(-1)^H$. The same calculation after reflection about the grid center proves that $R'$ is nonzero with constant sign on $(2H-1,\infty)$ as well. Changing all prescribed signs replaces $R$ by its reciprocal and preserves strict monotonicity.

It follows that every horizontal level of $R$ has at most one preimage on each exterior interval.

## Counting the finite poles

Let $D(t)=\prod_i(t-p_i)$ and write $F=P/D$ in reduced form.

If $u=0$, then $k=K=H$, and the two polynomials $P-D$ and $P+D$ each have $H$ prescribed roots. They therefore satisfy

$$ P-D=(v-1)Q_+,\qquad P+D=(v+1)Q_-,\qquad D=\frac{(v+1)Q_--(v-1)Q_+}{2}. $$

Neither $v-1$ nor $v+1$ is zero: otherwise the corresponding polynomial would have degree below $H$ and $H$ roots, forcing $F$ to be constant. Every finite pole consequently satisfies

$$ R(p_i)=\frac{v+1}{v-1}. $$

Strict exterior monotonicity gives at most two distinct finite poles in total, and at most one on either side. Thus $H=k\leq2$, with the asserted side condition when $H=2$.

If $u\neq0$, then $k=H-1$ and $P$ has degree $H$. Both $P-D$ and $P+D$ have leading coefficient $u$, so

$$ P-D=uQ_+,\qquad P+D=uQ_-,\qquad D=\frac u2(Q_--Q_+). $$

All finite poles now satisfy $R(p_i)=1$. Hence $k\leq2$ and $H\leq3$. The two remaining cases are explicit. For $H=2$, the paired-run nodes give

$$ Q_-=t(t-3),\qquad Q_+=(t-1)(t-2),\qquad Q_--Q_+=-2. $$

This contradicts $\deg D=1$. For $H=3$ they give

$$ Q_-=t(t-3)(t-4),\qquad Q_+=(t-1)(t-2)(t-5),\qquad Q_--Q_+=t^2-5t+10. $$

The last quadratic has discriminant minus fifteen, contradicting two real finite poles. A global sign change only negates these differences. The linear-part case therefore has $H=1$. This completes Theorem 1. $\blacksquare$

## The two orientations matter

The exception at two heads occurs in the exact admissible model on two bits. Put $t=x+2y$ and

$$ F(t)=5-\frac{24}{5(t+1)}-\frac{24}{5(4-t)}. $$

Its values at $t=0,1,2,3$ are $-1,1,1,-1$. The denominator $1+x+2y$ has strictly positive slopes, while $4-x-2y$ has strictly negative slopes. Both are positive on the whole two-bit cube. Thus an argument based only on left-hand poles would miss an actual admissible representation.

The theorem rules out a full arithmetic-address unit-data block at twice the effective head count once that count exceeds two. It does not cover arbitrary affine numerators in binary address coordinates, independently varying address slopes, or selected active sets without the stated scalar grid. Those omissions prevent a transfer to the unrestricted target. No such transfer is asserted.

## Verification

The proof is written, not Lean-formalized. `verify_exterior_pole_unit_grid.py` checks the paired-run generating-polynomial identity, the two exceptional polynomial differences, and the two-head admissible example using exact arithmetic. No numerical search outcome is used in the proof.
