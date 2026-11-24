# Parity obstructs sparse anchored affine compilation

## Statement

An anchored affine block is an arbitrary affine function multiplied by either a positive monomial or a negative monomial:

$$ g(x)=A(x)\prod_{i\in S}x_i\qquad\text{or}\qquad g(x)=A(x)\prod_{i\in S}(1-x_i). $$

Suppose a bias plus $K$ such blocks strictly sign-represents parity on $n$ bits. Then

$$ K+1\geq\frac{2}{n+2}\left(\frac32\right)^n. $$

This is a written proof. The existing original-model theorem `HeadComplexity.HStar_parity` in `formalization/HeadComplexity/Results/ExactFamilies.lean` proves that parity itself has head complexity exactly $n$. Consequently there is no universal compiler from $H$ original heads to $CH+\exp(o(n))$ anchored affine blocks. This does not rule out such a compiler restricted to the critical widths $H\asymp2^n/\mathrm{poly}(n)$, whose permitted budget is larger than the displayed obstruction.

## Proof by counting all cube faces

A cube face specifies, independently for each coordinate, one of three states: fixed to zero, fixed to one, or free. There are exactly $3^n$ faces, including the zero-dimensional faces.

For a face $F$ with free-coordinate set $T$, define the alternating sum of a real score $P$ over that face by

$$ \Delta_F P=\sum_{z\in\lbrace0,1\rbrace^T}(-1)^{|z|}P(x(F,z)). $$

If $P$ strictly represents parity, every summand in this sum has the same strict sign after multiplication by one common sign depending on the fixed coordinates. Therefore $\Delta_F P\neq0$ for every face. Since alternating sums are linear, at least one of the $K$ blocks or the bias must have nonzero alternating sum on every face.

Consider a negative block $A(x)\prod_{i\in S}(1-x_i)$ and write $s=|S|$. If any coordinate of $S$ is fixed to one, the block vanishes on the face. Otherwise each free coordinate of $S$ is forced to zero wherever the block is nonzero. After summing over these coordinates, the remaining expression is an affine function of the free coordinates outside $S$. Its alternating sum vanishes when there are at least two such coordinates.

Thus a necessary condition for this block to contribute is that all fixed coordinates of $S$ are zero and at most one free coordinate lies outside $S$. There are $2^s$ choices of fixed-zero or free status on $S$. Outside $S$, there are $2^{n-s}$ choices with no free coordinate and $(n-s)2^{n-s-1}$ choices with one free coordinate. For $s=n$, the second count is zero. Hence the number of faces on which the block can contribute is at most

$$ 2^s\left(2^{n-s}+(n-s)2^{n-s-1}\right)=2^n\left(1+\frac{n-s}{2}\right)\leq(n+2)2^{n-1}. $$

The same count holds for positive blocks by complementing all coordinates. A constant bias is the special case of an empty-anchor affine block, so the same bound applies to it. Covering all $3^n$ faces therefore gives

$$ 3^n\leq(K+1)(n+2)2^{n-1}, $$

which proves the claim. The bound does not assume positive block coefficients, bounded coefficients, disjoint faces, or absence of cancellation. $\blacksquare$

## What this rules out

The positive anchored-face decomposition of an original head has controlled total mass, but a sparse classifier in that dictionary can still require exponentially many terms. Parity supplies an explicit example: it has only $n$ original heads while every exact anchored affine classifier has at least $\exp(\Omega(n))$ blocks. This rules out a global support-compression theorem with constant multiplicative and subexponential additive overhead in this particular dictionary.

The argument concerns finite sums of the limiting affine-face blocks. It does not apply to arbitrary original heads, nor does it claim that every original head is itself an anchored affine block. Replacing blocks by approximating genuine heads can introduce small tails outside the anchor. With arbitrary signed cancellation those tails can determine labels; the face-count proof does not control them. It would therefore be incorrect to use this result as an unrestricted margin obstruction.

For the benchmark widths, the remaining possibility is a compiler whose guarantee is specific to exponentially large $H$, or a compiler allowed to introduce genuinely new denominator directions without passing through a sparse anchored-face score. Neither possibility is disproved here.
