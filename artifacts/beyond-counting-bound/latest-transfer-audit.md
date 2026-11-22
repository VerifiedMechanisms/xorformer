# Auditing Three Further Literature Transfers

## Integer polynomial parity does not preserve real signs

[Kalai, Kumar, and Volk, Definition 1.8 and Theorem 1.9](https://arxiv.org/html/2611.21201v1) study the correlation of the integer-polynomial phase $\exp(i\pi P(x))=(-1)^{P(x)}$ with the number-theoretic Möbius function. Their three stated structural hypotheses involve depth-three top fan-in, first-partial dimension, or multiplication-gate count that is $o(n)$.

The manuscript instead classifies using $\mathrm{sign}(P(x))$ after clearing positive denominators. These two predicates are not interchangeable. For every integer polynomial $P$ that is nonzero on the cube,

$$ \mathrm{sign}(2P(x))=\mathrm{sign}(P(x)),\qquad (-1)^{2P(x)}=1. $$

Even the positive affine polynomial $P(x)=1+x_1$ has constant real sign and a nonconstant parity phase. Conversely, $P(x)=1-2x_1$ has a nonconstant real sign and constant parity phase. These are exact identities, not precision issues. A transfer would need a proved sign-to-phase compiler with a sufficient complexity bound. None is available here, and the critical head count is exponential rather than $o(n)$.

## Tensor-network counts need a new representation

[Khavari and Rabusseau, Theorem 2](https://proceedings.neurips.cc/paper_files/paper/2021/file/5a9d8bf5b7a4b35f3110dde8673bdda2-Paper.pdf) bound the VC dimension of their tensor-network models by $2P\log(12v)$, where $P$ is the number of independent core entries and $v$ is the number of core tensors. The proof applies Warren's theorem to polynomials of degree $v$ in those independent entries.

A Boolean tensor has $n$ modes, but that observation does not provide a representation of head scores using $n$ cores and $O(nH)$ independent entries. In particular, even one admissible head can have exponentially large exact matrix flattening rank.

**Exact example.** On $2m$ bits, put

$$ a(x)=\sum_{i=0}^{m-1}2^i x_i,\qquad b(y)=\sum_{i=0}^{m-1}2^i y_i,\qquad T(x,y)=\frac1{1+a(x)+b(y)}. $$

All denominator slopes are strictly positive, so this is an admissible one-head score. As $x,y$ range over their cubes, $a,b$ range bijectively over $0,\ldots,2^m-1$. With $q=2^m$, the flattening is the Hilbert matrix $C_{ij}=1/(1+i+j)$, $0\leq i,j\lt q$. It has rank $q$.

**Proof.** If $c\in\mathbb R^q$ is nonzero, the polynomial $p(t)=\sum_{i=0}^{q-1}c_it^i$ is nonzero. Hence

$$ c^\top Cc=\int_0^1p(t)^2dt\gt0. $$

The equality follows by integrating each monomial. For strictness, a nonzero polynomial cannot vanish on the whole open interval. At one point its square is positive, and continuity gives a positive integral on a smaller interval. Thus $C$ is positive definite and nonsingular. $\blacksquare$

Every sum of $r$ rank-one tensors flattens into a sum of $r$ rank-one matrices. Therefore an exact CP decomposition of this one-head table requires at least $2^m$ terms. Similarly, a tensor-train representation in the displayed variable order needs a middle bond of dimension at least $2^m$: cutting that bond writes the flattening as a product of two matrices with inner dimension equal to the bond size.

This is an exact-value obstruction, not a sign obstruction. The displayed head has constant positive sign. An entirely different sign-preserving compiler is not ruled out; establishing one with the required parameter and factor budgets remains a theorem-strength gap.

## A join of concept classes is not a sum of scores

[Blondal, Hatami, Hatami, Lalov, and Tretiak, Theorem 1.12](https://arxiv.org/html/2606.18236v1) prove subadditivity of list replicability for joins of concept classes on disjoint domains. Their operation concatenates independently chosen labels on those domains.

Attention heads are real-valued scores on the same domain, added before the final sign. Their individual signs do not determine the sign of their sum. For example, the pairs of constant admissible scores $(2,-1)$ and $(1,-2)$ have identical component sign tables and opposite sum sign tables. These constants can each be written as $rB/B$ with the same strictly positive affine $B$.

Consequently the cited join theorem does not identify an additive invariant of the head model. A quantitative theorem handling sums of real scores with unrestricted cancellation would be additional mathematics, not an instance of the published disjoint-domain composition rule.

## Status

All three proposed transfers are blocked at the stated representation or composition steps. Neither the selected unboundedness statement nor an intermediate-exponent lower bound follows. No definition of the attention architecture or of $W(n)$ has changed. The elementary counterexamples above are written proofs; this note claims no new Lean declaration.
