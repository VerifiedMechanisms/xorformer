# Quadratic Characters Do Not Preserve Real Sign Complexity

## Scope

This audit concerns a proposed arithmetic route to the head lower bound. The two statements below explain why transferring a finite rational representation to quadratic characters does not, by itself, give a useful counting argument. Neither statement proves an asymptotic attention-head lower bound.

## Finite rational signs can be transferred

Let $r_1,\ldots,r_M$ be nonzero rational numbers. There are infinitely many odd primes $p$, dividing none of their numerators or denominators, such that

$$ \chi_p(r_j\bmod p)=\mathrm{sgn}(r_j)\qquad(1\leq j\leq M). $$

**Proof.** Let $L$ be the product of the distinct odd primes dividing any numerator or denominator in the list, with the empty product equal to one. Dirichlet's theorem supplies infinitely many primes $p\equiv-1\pmod{8L}$. Discard the finitely many primes occurring in the list.

The supplementary quadratic-reciprocity laws give $\chi_p(-1)=-1$ and $\chi_p(2)=1$. For each odd prime $\ell\mid L$, quadratic reciprocity and $p\equiv-1\pmod\ell$ give

$$ \chi_p(\ell)=\chi_\ell(p)(-1)^{(\ell-1)/2}=\chi_\ell(-1)(-1)^{(\ell-1)/2}=1. $$

Here $(p-1)/2$ is odd, which accounts for the displayed reciprocity sign. Multiplicativity, including inversion for rational denominators, now proves the assertion. $\blacksquare$

For a fixed rational attention representation with strict output signs, this statement can simultaneously preserve the characters of all nonzero coefficients, all denominator values, and all score values. The prime depends on that representation. No uniform upper bound for the required prime follows from this argument.

## A single affine form has unrestricted character tables

Fix $n\geq1$ and put $N=2^n$. For every sufficiently large prime $p$, every labeling $\varepsilon:\lbrace0,1\rbrace^n\to\lbrace-1,1\rbrace$ has a seed $a\in\mathbb F_p$ such that all the arguments below are nonzero and

$$ \chi_p\left(a+\sum_{i=0}^{n-1}2^i x_i\right)=\varepsilon(x)\qquad\text{for every }x\in\lbrace0,1\rbrace^n. $$

**Proof.** The binary statistic enumerates the distinct offsets $0,\ldots,N-1$ when $p\gt N$. [Peralta's Corollary 5](https://www.cs.umd.edu/users/gasarch/TOPICS/res/resperalta.pdf) gives at least $p/2^N-N(3+\sqrt p)$ seeds for each prescribed residue/nonresidue pattern, counting zero as a residue. At most $N$ seeds have a zero argument. Thus at least

$$ \frac{p}{2^N}-N(4+\sqrt p) $$

seeds realize the prescribed nonzero character values. This expression is positive, for example, whenever $p\gt(4N2^N)^2$. The bound is uniform over the $2^N$ patterns. $\blacksquare$

This is a statement about quadratic-character readout over finite fields. Real thresholding of the same affine expressions does not have this property.

## Exact eight-input certificate

At the prime $p=1367$, all 256 patterns already occur among the eight consecutive values $a,a+1,\ldots,a+7$, with positive integer seeds $a\leq1076$. The seed for every pattern is stored in [the certificate](quadratic-character-certificate.json). Its index has the first desired positive character in the least significant binary position.

The same prime satisfies

$$ \chi_{1367}(1)=\chi_{1367}(2)=\chi_{1367}(3)=\chi_{1367}(4)=1. $$

Consequently the real affine-ratio functions

$$ S_a(x)=\frac{a+x_0+2x_1+4x_2}{1+x_0+x_1+x_2} $$

are all strictly positive on the three-dimensional Boolean cube and have admissible denominator slopes. After reduction modulo 1367, their quadratic characters realize every labeling of that cube. This is an explicit loss of real-order information even when the reduced denominator characters are all positive.

`formalization/HeadComplexity/Atoms/QuadraticCharacterTransfer.lean` checks the numerator character certificate through Euler's criterion. It uses a fixed addition chain for exponent 683 and kernel-checked modular arithmetic. The real positivity assertion and the existence of a seed for every labeling are included in `eight_character_tests_shattered`. The denominator-character observation above is a separate direct modular calculation in the certificate verifier.

## Blocked inference

The forward transfer theorem does not provide a converse that preserves real sign patterns. The character relaxation already realizes arbitrary truth tables with one affine numerator. Counting that relaxation over unbounded primes therefore cannot distinguish hard real attention functions. An arithmetic approach would need a new invariant retaining real-order information, or a proved uniform arithmetic restriction compatible with every admissible real representation. Neither is established here.
