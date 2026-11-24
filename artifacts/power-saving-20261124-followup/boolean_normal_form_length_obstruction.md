# Boolean normal form can increase local length exponentially

## Statement and scope

For every positive integer $n$, there is a homogeneous polynomial $P_n$ in $n+1$ variables whose full derivative space has dimension $n+1$, but whose canonical homogeneous Boolean normal form has derivative-space dimension at least $2^n$. For even $n$, that normal form also has homogeneous border Waring rank at least $\binom{n}{n/2}$.

This is a written theorem, proved below. It rules out preserving local moment length by taking the canonical Boolean quotient representative. It does not rule out an existential small lift modulo Boolean ghosts: the original $P_n$ is already such a lift. It also gives no obstruction to sign-preserving repair or to the original unrestricted width lower bound.

The [ghost-ideal audit](unrestricted_capacity_ghost_ideal.md) identifies the relevant homogeneous relations. This note isolates a different issue: the complexity of choosing their canonical normal form.

## Canonical reduction

Let $z_0,z_1,\ldots,z_n$ be independent real variables and put

$$ I_n=\langle z_i^2-z_0z_i:1\leq i\leq n\rangle,\qquad P_n=(z_1+\cdots+z_n)^n. $$

Reduction replaces every positive exponent of $z_i$ by one and transfers the removed degree to $z_0$. Thus every homogeneous class of degree $n$ has a unique representative that is squarefree in $z_1,\ldots,z_n$. The uniqueness follows by setting $z_0=1$ and evaluating at all Boolean points: squarefree Boolean monomials are linearly independent as functions on the cube.

For $S\subseteq[n]$, let $c_S$ be the number of maps from $[n]$ onto $S$. The convention $c_{\varnothing}=0$ applies because $n\gt0$. Expansion of the power, followed by reduction, gives

$$ R_n=\sum_{S\subseteq[n]}c_S z_0^{n-|S|}\prod_{i\in S}z_i,\qquad P_n-R_n\in I_n. $$

Equivalently, $c_S=|S|!\left\lbrace {n\atop |S|}\right\rbrace$, where the braces denote a Stirling number of the second kind. The sole term without a factor of $z_0$ is the one indexed by $S=[n]$, and its coefficient is $n!$. Consequently

$$ R_n(0,z_1,\ldots,z_n)=n!z_1\cdots z_n. $$

For every Boolean vector $x$, the original and reduced polynomials have exactly the same value:

$$ R_n(1,x)=P_n(1,x)=(x_1+\cdots+x_n)^n. $$

## Derivative-space length

For a polynomial $F$, write $\mathrm{Diff}(F)$ for the real span of $F$ and all of its partial derivatives of all orders. This is the length of its local inverse-system algebra.

Every derivative of $P_n$ is a scalar multiple of $(z_1+\cdots+z_n)^j$ for some $0\leq j\leq n$. All these powers occur and have different degrees. Hence

$$ \dim\mathrm{Diff}(P_n)=n+1. $$

For each subset $S\subseteq[n]$, differentiate $R_n$ once in each variable indexed by $S$ and then set $z_0=0$. Specialization commutes with these derivatives, so

$$ \left.\left(\prod_{i\in S}\partial_{z_i}\right)R_n\right|_{z_0=0}=n!\prod_{i\notin S}z_i. $$

The $2^n$ monomials on the right are distinct. Their linear independence implies the linear independence of the corresponding derivatives before specialization. Therefore

$$ \dim\mathrm{Diff}(R_n)\geq2^n. $$

This already disproves any universal constant-factor, or polynomial-factor, preservation of derivative-space length under canonical Boolean reduction.

## Middle catalecticant

Suppose $n=2m$. Index a square submatrix of the middle catalecticant of $R_n$ by the $m$-element subsets $S,T\subseteq[n]$. A row differentiates once in every variable of $S$, a column differentiates once in every variable of $T$, and neither uses $z_0$.

Every term containing $z_0$ contributes zero. The remaining term is $n!z_1\cdots z_n$, so the matrix entry is

$$ C_{S,T}=\begin{cases}n!&T=[n]\setminus S,\cr0&\text{otherwise}.\end{cases} $$

Complementation permutes the $m$-element subsets. Thus this submatrix is $n!$ times a permutation matrix and has rank $\binom{n}{m}$. A homogeneous power has middle catalecticant rank at most one, and matrix rank at most a fixed integer is a closed condition. It follows that

$$ \underline{\mathrm{wr}}(R_n)\geq\binom{n}{n/2}. $$

The ratio between this lower bound and the source length $n+1$ grows exponentially. This is distinct from the quadratic factorial-homogenization obstruction in the [earlier note](factorial_homogenization_rank_obstruction.md).

## Why this does not settle access

The low-length polynomial $P_n$ remains an available representative of the same Boolean observations. The obstruction concerns the particular squarefree normal form, not the minimum length among all representatives modulo $I_n$.

Even strict positivity does not remove the canonical blowup. Adding $\varepsilon z_0^n$, with $\varepsilon\gt0$, makes every Boolean value positive. The source derivative space then has dimension at most $2n+1$, while the specialization at $z_0=0$ and the middle catalecticant submatrix are unchanged. The resulting truth table has a constant classifier.

The first missing access statement is consequently existential: given a limit of narrow original scores, does there exist some bounded moment-functional lift, after subtracting full-cube observation ghosts, of length comparable to the original width? Choosing the canonical quotient representative is not a proof of that statement.

There is also a separate general compactness pitfall. [Huang, Michałek, and Ventura](https://arxiv.org/html/1912.13174) exhibit homogeneous forms whose smoothable and cactus ranks exceed their border ranks: the span of a flat limit can be smaller than the limit of spans. Their displayed families have an upper bound below twice the border rank, so those examples disprove equality of lengths but do not disprove a constant-factor bound. The source is over the complex numbers and concerns Veronese observations; it is not a counterexample in the original admissible real-head model.

## Verification status

The general proofs above are written arguments and are not claimed as Lean declarations. The accompanying exact-integer checker verifies the surjection coefficients, Boolean evaluation identity, and complement-matrix pattern for even dimensions two through ten. Those computations corroborate the formulas and are not substitutes for the general proof. No original model definition or axiom was changed.
