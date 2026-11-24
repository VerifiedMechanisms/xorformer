# Small Head Counts Can Require Large Polynomial Sign Support

## Statement and scope

For a Boolean sign function $f:\lbrace-1,1\rbrace^n\to\lbrace-1,1\rbrace$, let $\mathrm{dns}(f)$ be the smallest number of Walsh characters with nonzero coefficients in a real polynomial whose strict sign is $f$.

For every $k\geq1$ and $r\geq0$, let $f_{k,r}$ be the product of $k$ majority functions on disjoint blocks of $2r+1$ bits. The input dimension is $n=k(2r+1)$. In the unchanged manuscript architecture,

$$ H^{\ast}(f_{k,r})\leq2^{k-1},\qquad \mathrm{dns}(f_{k,r})\geq\left(\frac{4^r}{\binom{2r}{r}}\right)^k\geq(r+1)^{k/2}. $$

The notation $H^{\ast}$ here applies to the Boolean predicate that the displayed sign function is positive, after the coordinate substitution $z_i=1-2x_i$.

In particular, four heads compute a family on $n=3(2r+1)$ bits whose threshold density is at least $(r+1)^{3/2}$. More generally, there are no fixed constants $C,a,b\gt0$ such that every admissible $H$-head Boolean function satisfies $\mathrm{dns}(f)\leq Cn^aH^b$.

The reciprocal constructions can have every denominator value in $[1,1+\varepsilon]$, for any prescribed $\varepsilon\gt0$. Thus this obstruction persists with arbitrarily well-conditioned denominators. Its small margins are permitted by the original model.

This is a counterexample to a proposed conversion from heads to sparse polynomial signs. It is an upper bound for particular functions together with a lower bound in a different representation model. It proves neither of the requested worst-case head lower bounds.

## A finite-difference construction for products

Let $L_1,\ldots,L_k$ be affine real functions on the Boolean cube. Write $L_j(x)=c_j+\sum_i a_{ji}x_i$. Put $J=\lbrace2,\ldots,k\rbrace$ and choose

$$ D(x)=1+\sum_{j\in J}|c_j|+\sum_i\left(1+\sum_{j\in J}|a_{ji}|\right)x_i,\qquad D_T=D+\sum_{j\in T}L_j\quad(T\subseteq J). $$

Every constant coefficient and every slope of every $D_T$ is strictly positive. The positive affine-ratio realization theorem therefore makes each summand in

$$ S(x)=L_1(x)\sum_{T\subseteq J}\frac{(-1)^{|T|}}{D_T(x)} $$

an admissible head. There are exactly $2^{k-1}$ summands.

### Lemma 1. Reciprocal finite differences

For real increments $u_1,\ldots,u_m$, suppose $d+\sum_{i\in T}u_i\gt0$ for every subset $T$. Then

$$ \sum_{T\subseteq[m]}\frac{(-1)^{|T|}}{d+\sum_{i\in T}u_i}=\left(\prod_{i=1}^m u_i\right)\sum_{\pi\in\mathfrak S_m}\prod_{j=0}^m\frac1{d+\sum_{\ell=1}^j u_{\pi(\ell)}}. $$

The empty product and the single permutation of the empty set give the formula for $m=0$.

**Proof.** Induct on $m$. Adding the last increment $u$ replaces the previous finite difference at $d$ by its value at $d$ minus its value at $d+u$. For each path in the induction hypothesis, apply the product telescoping identity

$$ \prod_{j=0}^{m-1}\frac1{t_j}-\prod_{j=0}^{m-1}\frac1{t_j+u}=u\sum_{q=0}^{m-1}\left(\prod_{j=0}^{q}\frac1{t_j}\right)\left(\prod_{j=q}^{m-1}\frac1{t_j+u}\right). $$

To verify this identity, telescope the products by changing their factors one at a time and use $1/t-1/(t+u)=u/(t(t+u))$. With $t_j=d+\sum_{\ell=1}^j u_{\pi(\ell)}$, the term indexed by $q$ inserts the new increment immediately after the first $q$ old increments. Every permutation of all $m$ increments occurs exactly once. All denominators are nonzero by hypothesis, so every algebraic step is valid, even for negative or zero increments. $\blacksquare$

Every term in the final permutation sum is positive. Consequently the finite difference has precisely the sign of $\prod_i u_i$, including equality to zero. Applying the lemma pointwise proves that $S$ has the sign of $\prod_{j=1}^kL_j$.

### Four-head special case

For three factors the identity is especially explicit:

$$ \frac A D-\frac A{D+u}-\frac A{D+v}+\frac A{D+u+v}=\frac{Auv(2D+u+v)}{D(D+u)(D+v)(D+u+v)}. $$

The four denominator values are positive, and $2D+u+v=D+(D+u+v)\gt0$. Thus the signs agree with $Auv$. The identity, sign equivalence, and assembly into the original four-head model are Lean checked in `AffineTripleFourHeads.lean`.

### Denominators arbitrarily close to one

With the same positive affine forms $D_T$, choose a positive $M$ at least their maximum value over all subsets and cube vertices. Replace each denominator by $1+\delta D_T$, where $\delta=\varepsilon/M$. Its constant coefficient and all slopes remain positive, and its values belong to $[1,1+\varepsilon]$. The new common base is $1+\delta D$ and its increments are $\delta L_j$. Lemma 1 gives the same strict labels, because the additional factor $\delta^{k-1}$ is positive. No bound on the resulting margin is asserted.

## The spectral support lower bound

Write $\chi_T(z)=\prod_{i\in T}z_i$ and $\widehat f(T)=\mathbb E[f(z)\chi_T(z)]$, using uniform probability on the cube.

### Lemma 2. Support must carry unit Fourier mass

If $p=\sum_{T\in\mathcal T}c_T\chi_T$ has strict sign $f$, then

$$ \sum_{T\in\mathcal T}|\widehat f(T)|\geq1. $$

**Proof.** Choose a coefficient of maximum absolute value $K\gt0$. Orthogonality and $|\chi_T|=1$ imply $K\leq\mathbb E|p|$. Since $fp=|p|$,

$$ K\leq\mathbb E|p|=\mathbb E[fp]=\sum_{T\in\mathcal T}c_T\widehat f(T)\leq K\sum_{T\in\mathcal T}|\widehat f(T)|. $$

Divide by $K$. In particular, $\mathrm{dns}(f)\geq1/\max_T|\widehat f(T)|$. This elementary lemma is also [O'Donnell, Theorem 5.10](https://www.cs.cmu.edu/~odonnell/papers/Analysis-of-Boolean-Functions-by-Ryan-ODonnell.pdf). Its more general finite orthogonal-dictionary form is Lean checked in `SpectralDensityBarrier.lean`. $\blacksquare$

### Lemma 3. Largest majority coefficient

For majority on $2r+1$ signs, every Fourier coefficient has absolute value at most

$$ a_r=\frac{\binom{2r}{r}}{4^r}. $$

**Proof.** Its constant coefficient is zero because negating all signs reverses majority. For a nonempty set $T$, fix $i\in T$ and first average over $z_i$. The half-difference of the two majority values is exactly the indicator that the other $2r$ signs sum to zero. Hence

$$ \widehat{\mathrm{Maj}}(T)=\mathbb E_{z_{-i}}\left[\chi_{T\setminus\lbrace i\rbrace}(z_{-i})\mathbf1_{\lbrace\sum_{j\neq i}z_j=0\rbrace}\right]. $$

Taking absolute values bounds this by the probability of a tie among the other signs, namely $a_r$. Equality holds for a singleton $T$. No formula for the other coefficients is needed. $\blacksquare$

For disjoint blocks, Fourier coefficients of a product factor into the product of the block coefficients. Therefore the largest absolute coefficient of $f_{k,r}$ is exactly $a_r^k$. Lemma 2 proves the first density lower bound.

Finally $a_0=1$ and $a_{r+1}=a_r(2r+1)/(2r+2)$. Induction gives $a_r^2\leq1/(r+1)$: the required step follows from

$$ 4(r+1)^3-(2r+1)^2(r+2)=3r+2\geq0. $$

This proves the second density lower bound. Choosing an integer $k\gt2a$ and letting $r$ grow disproves any proposed bound $Cn^aH^b$, since $H=2^{k-1}$ is then fixed and the density grows at least as $n^{k/2}$.

## The ordinary zero-one monomial dictionary also fails

Changing the dictionary to the ordinary monomials $\prod_{i\in T}x_i$ does not repair a polynomial-size conversion. Parity has head complexity $n$, but every strict polynomial sign representation of parity has all $2^n$ coefficients nonzero after multilinearization.

Indeed, let $p(\mathbf1_T)$ have sign $(-1)^{|T|}$ and let $c_S$ be its multilinear coefficient. Boolean Möbius inversion gives

$$ (-1)^{|S|}c_S=\sum_{T\subseteq S}(-1)^{|T|}p(\mathbf1_T)\gt0. $$

Each summand is positive, including the summand for the empty subset. Thus every $c_S$ is nonzero. Multilinearizing an arbitrary polynomial cannot increase its number of monomials, so the same lower bound applies before reduction. Reversing the parity convention only reverses the coefficient signs.

## Audit boundary and consequences for the research

The general finite-difference, conditioning, majority, and Möbius arguments above are complete written proofs. The four-head realization, the general finite orthogonal-dictionary sparsity inequality, tensor correlation factorization, and the central-ratio recurrence inequality are separately Lean checked. Identification of that recurrence with the binomial ratio remains a written proof. The independent exact verifier tests the rational path identity, the four-head majority witnesses, the majority spectra, and the Möbius formula on finite instances. Those computations supplement the general proofs.

The threshold-density results for intersections of halfspaces in [Sherstov, Section 5.4](https://web.cs.ucla.edu/~sherstov/pdf/hardest-hs.pdf) concern another class. The argument here uses products and supplies the missing explicit attention-head realization, so it needs no transfer from an intersection circuit.

Both standard fixed polynomial dictionaries are now excluded as the target of any universal polynomial-size head-to-sign-support conversion. A different dictionary or a weaker representation invariant would require a new mechanism and its own proof. Nothing here bounds the number of signs of unrestricted head sums, and the original asymptotic head lower-bound objective remains unproved.
