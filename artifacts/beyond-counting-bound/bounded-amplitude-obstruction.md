# Bounded Amplitude Is Not a Free Normalization

## Statement and scope

There are explicit nonconstant halfspaces with head complexity one for which a score with uniformly bounded positive signed margins requires a growing number of heads. This is an obstruction to a normalization step, not a proof of the requested lower bound for worst-case head complexity.

The model and admissible denominators are unchanged. In particular, the head parameters may depend on the target function and have unrestricted real magnitude.

### Theorem 1. Amplitude obstruction

There are absolute constants $a,c\gt 0$ and explicit halfspaces $h_n:\lbrace 0,1\rbrace^n\to\lbrace -1,1\rbrace$ with the following property for all sufficiently large $n$. Suppose an admissible score $T$ has $H$ heads, where $1\leq H\leq cn$, and satisfies

$$ 1\leq h_n(x)T(x)\leq M\qquad\text{for every }x\in\lbrace 0,1\rbrace^n. $$

Then

$$ M+1\gt 2^{1+an/H}. $$

Thus any fixed amplitude ratio requires $H=\Omega(n)$, and an amplitude ratio bounded by a fixed power of $n$ requires $H=\Omega(n/\log n)$. Nevertheless, $H^{\ast}(h_n)=1$.

## Proof

Write the actual head score as a sum of affine fractions with positive denominators:

$$ T(x)=c_0+\sum_{j=1}^H\frac{A_j(x)}{B_j(x)},\qquad B_j(x)\gt 0. $$

Clearing these denominators gives $T=P/Q$, with $Q=\prod_jB_j$ positive on the cube and both polynomial degrees at most $H$. This uses the particular denominators in the representation, so no common or target-independent dictionary is assumed.

For any $y\in\lbrace -1,1\rbrace$ and $1\leq ys\leq M$, direct multiplication by $M+1\gt 0$ gives

$$ \left|y-\frac{2s}{M+1}\right|\leq\frac{M-1}{M+1}=1-\frac{2}{M+1}. $$

Consequently, the rational function $2P/((M+1)Q)$ approximates $h_n$ uniformly to error at most $1-2/(M+1)$ and has numerator and denominator degrees at most $H$.

[Sherstov, The Hardest Halfspace, Theorem 1.2](https://web.cs.ucla.edu/~sherstov/pdf/hardest-hs.pdf) constructs halfspaces whose degree $d$ rational approximation error is greater than $1-2^{-an/d}$ for $1\leq d\leq cn$, after choosing suitable absolute constants. Applying that theorem at $d=H$ yields

$$ 1-2^{-an/H}\lt 1-\frac{2}{M+1},\qquad \frac{2}{M+1}\lt 2^{-an/H}. $$

This is the claimed inequality. For $M\gt 1$, it equivalently implies

$$ H\gt\frac{an}{\log_2(M+1)-1}. $$

If a representation has $H\gt cn$, the stated asymptotic consequences already hold. The case $M=1$ is impossible in the range of Theorem 1. A nonconstant halfspace is computed by one positive-denominator affine ratio, whose numerator is its defining affine form, and cannot be computed by a constant score. This proves the last assertion. $\blacksquare$

## A related composition obstruction

### Theorem 2. Conjunction can increase head complexity

There are explicit halfspaces $h_n$ for which the conjunction of two copies on disjoint inputs has head complexity $\Omega(n)$, although each copy has head complexity one.

**Proof.** [Sherstov's Theorem 1.6](https://web.cs.ucla.edu/~sherstov/pdf/hardest-hs.pdf) gives threshold degree $\Omega(n)$ for this conjunction on $2n$ bits. Clearing any admissible $H$-head representation produces a polynomial sign representation of degree at most $H$. Hence $H=\Omega(n)$. $\blacksquare$

This rules out a constant-cost conjunction compiler even for one-head inputs. It does not rule out the existing two-head construction for the sign of a product of two affine forms: that computes sign agreement, a different Boolean operation.

## Formal audit

`formalization/HeadComplexity/Atoms/BoundedAmplitude.lean` proves the interval inequality and the rational certificate for genuine `FracAtom` scores. Its theorem `amplitude_ratio_obstruction` takes an explicit rational-approximation hardness hypothesis and concludes $2\lt\delta(M+1)$ when the hardness threshold is $1-\delta$.

The Sherstov hardness theorems are cited external results, not Lean axioms and not formalized in this file. Kernel checks of the three new declarations report only `propext`, `Classical.choice`, and `Quot.sound`.

The origin repair theorem from this run supplies a lower bound on signed margins. It supplies no upper bound on scores, so Theorem 1 does not contradict it. Neither theorem in this note is a lower bound of order $2^n/n^\alpha$, for any fixed $\alpha$, and neither completes the selected target.
