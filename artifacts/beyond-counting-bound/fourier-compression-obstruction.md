# Exponential Fourier Density with Linearly Many Heads

## Statement and scope

For every $m\geq1$, there is an explicit Boolean function on $n=2m$ inputs with head complexity exactly $m$ such that every strict sign representation in the Walsh character basis has at least $2^m$ nonzero coefficients. Consequently, a polynomial bound in $n$ and $H$ on the Fourier support of an equivalent sign polynomial cannot hold for all $H$-head functions.

This is a counterexample to a Fourier-basis compression argument, not the requested worst-case head lower bound. It does not establish the same obstruction for sparsity in a different polynomial basis.

## The function and its head complexity

On the vector space $\mathbb F_2^n$, define

$$ q(x)=\sum_{i\lt j}x_ix_j\pmod2,\qquad g(x)=(-1)^{q(x)},\qquad f(x)=\mathbf1[g(x)=1]. $$

The quadratic expression here is over $\mathbb F_2$, not a real quadratic sign polynomial. If $w$ is the Hamming weight, then $q(x)=\binom w2\pmod2$. Hence $g$ is positive at weights congruent to zero or one modulo four and negative at weights congruent to two or three. Its profile changes sign at exactly the $m$ transitions from odd weight to the following even weight between zero and $2m$. The manuscript's symmetric-function theorem therefore gives

$$ H^{\ast}(f)=m. $$

An explicit strict polynomial in the weight with exactly this degree is $(-1)^m\prod_{j=1}^m(2w-4j+1)$. Its roots are the half-integers at precisely the required transitions.

## Flat Fourier spectrum

The complete quadratic function is a classical bent function in even dimension; see [Sherstov, Theorem 13.7](https://web.cs.ucla.edu/~sherstov/pdf/Sherstov_Dissertation.pdf), with attribution there to Bruck. The following calculation gives the needed fact directly. All additions in its exponents are in $\mathbb F_2$.

For $a\in\mathbb F_2^n$, put $p(a)=\sum_i a_i$. Expanding the quadratic expression gives

$$ q(x+a)+q(x)+q(a)=x\cdot\bigl(a+p(a)\mathbf1\bigr). $$

If $a\neq0$, the vector on the right is nonzero. Otherwise $a=p(a)\mathbf1$, and summing coordinates, using even $n$, forces $p(a)=0$ and then $a=0$. A nonzero linear functional on the cube is balanced, by pairing each input with its translate in a coordinate having nonzero coefficient. Thus the autocorrelation satisfies

$$ C(a):=\sum_xg(x)g(x+a)=\begin{cases}2^n,&a=0,\cr0,&a\neq0.\end{cases} $$

Let $\chi_s(x)=(-1)^{s\cdot x}$ and $W(s)=\sum_xg(x)\chi_s(x)$. Changing variables from the pair $(x,y)$ to $(x,a=x+y)$ gives

$$ W(s)^2=\sum_a\chi_s(a)C(a)=2^n. $$

Therefore every normalized Fourier coefficient has absolute value $2^{-m}$.

## The support lower bound

The density criterion is due to [Bruck, Harmonic Analysis of Polynomial Threshold Functions](https://www.paradise.caltech.edu/cns188/bruck90.pdf). Here is its short norm argument in the needed setting. Suppose $P=\sum_{s\in S}c_s\chi_s$ satisfies $g(x)P(x)\gt0$ everywhere. Let $k=|S|$, $L=\sum_s|c_s|$, $R=\sum_sc_s^2\gt0$, and $A=\mathbb E|P|$, with expectation uniform on the cube. Orthogonality, the pointwise bound $|P|\leq L$, and the flat spectrum imply

$$ R=\mathbb E P^2\leq LA,\qquad A=\mathbb E(gP)\leq2^{-m}L,\qquad L^2\leq kR. $$

The final inequality is Cauchy-Schwarz. Combining them gives $R\leq2^{-m}kR$, and division by $R\gt0$ proves $k\geq2^m$.

A polynomial whose zero values are assigned to the false class can be made strict by subtracting a sufficiently small positive constant. This adds at most one Fourier term. The corresponding weak-sign support lower bound is therefore $2^m-1$, which still excludes polynomial support bounds. $\blacksquare$

## Audit boundary

`formalization/HeadComplexity/Results/CompleteQuadraticProfile.lean` defines the weight profile. Its `profile_change`, `signChanges_eq`, and `HStar_eq` declarations prove the exact sign-change count and exact-model head complexity. The identification with the quadratic character, autocorrelation calculation, and Fourier density bound are the written proofs above, not Lean declarations. No result here refutes $W(n)=O(2^n/n^2)$.

`verify_complete_quadratic.py` independently checks the integer weight polynomial and full Walsh spectrum in every even dimension from two through twelve, and checks every autocorrelation directly through dimension eight. The exact records are in `complete-quadratic-checks.json`; the general proof does not depend on these finite checks.
