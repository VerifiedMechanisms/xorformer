# Counting Lower Bound For Worst-Case Head Complexity

## Statement

Let

$$ W(n) := \max_{f : \lbrace0,1\rbrace^n \to \lbrace0,1\rbrace} H^{\ast}(f). $$

Then

$$ W(n) = \Omega \left(\frac{2^n}{n^2}\right). $$

More quantitatively, for fixed $n$ and $H$, the number of $n$-bit Boolean functions computable with at most $H$ heads is at most

$$ 2^{O(n^2H)} $$

whenever $1 \leq H \leq 2^n$. Hence, if

$$ H = o \left(\frac{2^n}{n^2}\right), $$

then the fraction of $n$-bit Boolean functions computable with at most $H$ heads tends to $0$ as $n \to \infty$.

> **Interpretation.** Almost all Boolean functions require exponentially many heads, up to the polynomial slack in this counting argument. Thus no polynomial head bound can hold for all functions.

## Proof

We count sign patterns produced by the linear-fractional normal form.

### Lemma 1. An H-head score is controlled by few polynomial inequalities

Every $H$-head score is a special case of

$$ S(x) = c+\sum_{h=1}^{H}\frac{A_h(x)}{B_h(x)}, $$

where

$$ A_h(x)=a_{h,0}+\sum_{i=1}^{n}a_{h,i}x_i, \qquad B_h(x)=b_{h,0}+\sum_{i=1}^{n}b_{h,i}x_i, $$

and $B_h(x)\gt0$ on the cube. This is a slight relaxation of the exact atom form from [010_linear_fractional_normal_form.md](010_linear_fractional_normal_form.md), so counting this larger family can only increase the number of possible Boolean functions.

The relaxed family has

$$ p := 1+2H(n+1) $$

real parameters: one constant $c$, the affine numerator coefficients, and the affine denominator coefficients.

For each cube point $x\in\lbrace0,1\rbrace^n$, clear denominators and define

$$ P_x(\theta) := c\prod_{h=1}^{H}B_h(x) + \sum_{h=1}^{H}A_h(x)\prod_{j\neq h}B_j(x), $$

where $\theta$ denotes all $p$ real parameters. For each fixed $x$, this is a polynomial in $\theta$ of degree at most $H+1$.

If the score computes a Boolean function using a non-strict negative side, perturb the folded constant in the score slightly downward. Since the cube is finite and every positive input has strictly positive score, this gives an equivalent representation whose cleared values are strictly positive on positive inputs and strictly negative on negative inputs.

Thus every Boolean function computable with $H$ heads gives a strict sign pattern of the $2^n$ polynomials

$$ \lbrace P_x : x\in\lbrace0,1\rbrace^n\rbrace $$

in $p$ real variables, each of degree at most $H+1$. $\blacksquare$

### Lemma 2. Warren's sign-pattern bound

We use the following standard form of Warren's theorem. If $N$ real polynomials of degree at most $d$ in $p$ variables are evaluated over $\mathbb{R}^p$, and $N\geq p$, then the number of strict sign patterns they realize is at most

$$ \left(\frac{4edN}{p}\right)^p. $$

Apply this with

$$ N=2^n, \qquad d=H+1, \qquad p=1+2H(n+1). $$

When $N\geq p$, Lemma 1 gives

$$ \lvert\lbrace f : H^{\ast}(f)\leq H\rbrace\rvert \leq \left( \frac{4e(H+1)2^n}{1+2H(n+1)} \right)^{1+2H(n+1)}. $$

When $N\lt p$, the trivial bound $2^N$ is enough for the asymptotic conclusion below, because $p\gt N$ already implies

$$ H \gt \frac{2^n-1}{2(n+1)}. $$

### Lemma 3. The number of H-head functions is small for small H

Assume first that $1\leq H\leq 2^n$ and $N\geq p$. Since $p=O(nH)$ and $d=H+1\leq 2^{n}+1$, the logarithm of the Warren factor is $O(n)$. Therefore

$$ \log_2 \lvert\lbrace f : H^{\ast}(f)\leq H\rbrace\rvert \leq O(n^2H). $$

Equivalently,

$$ \lvert\lbrace f : H^{\ast}(f)\leq H\rbrace\rvert \leq 2^{O(n^2H)}. $$

If $N\lt p$, then $H=\Omega(2^n/n)$, so the trivial bound $2^{2^n}$ is also at most $2^{O(n^2H)}$. Hence the same estimate holds for every $1\leq H\leq 2^n$.

There are

$$ 2^{2^n} $$

Boolean functions on $\lbrace0,1\rbrace^n$. If

$$ H=o \left(\frac{2^n}{n^2}\right), $$

then

$$ 2^{O(n^2H)} = 2^{o(2^n)} $$

is a vanishing fraction of all Boolean functions. More explicitly, for some absolute constant $c\gt0$, the fraction of $n$-bit Boolean functions with

$$ H^{\ast}(f) \leq c\frac{2^n}{n^2} $$

is at most $2^{-\Omega(2^n)}$. Thus almost every $n$-bit Boolean function requires $\Omega(2^n/n^2)$ heads.

In particular, the worst-case quantity satisfies

$$ W(n)=\Omega \left(\frac{2^n}{n^2}\right). $$

$\blacksquare$

## Consequence

Keeping the exact Warren estimate also gives the leading asymptotic coefficient

$$ W(n)\geq\left(\frac12-o(1)\right)\frac{2^n}{n^2}. $$

Indeed, the logarithm of the exact pattern bound is at most
$(2+o(1))Hn^2$. Taking $H\leq(1/2-\varepsilon)2^n/n^2$ leaves an exponentially
small fraction of all truth tables for every fixed $\varepsilon\gt0$. This is
an arithmetic consequence of the existing exact estimate, not a separate
counting mechanism. Lean already exposes the exact finite estimate; this
asymptotic simplification is stated here in prose.

The newer [neighborhood interpolation theorem](../02_complexity_measure_upper_bounds/199_neighborhood_interpolation_universal_bound.md)
sharpens the general upper side to strictly below $3\cdot2^n/(2n)$ for
$n\geq8$, without changing the counting premise.

The general worst-case head complexity is therefore bracketed, for $n\geq8$, as

$$ \left(\frac12-o(1)\right)\frac{2^n}{n^2}\leq W(n)\lt\frac{3\cdot2^n}{2n}, $$

with the lower side conditional on Warren's estimate and the upper side unconditional. The original positive weighted-sum bound from [009_weighted_sum_upper_bound.md](009_weighted_sum_upper_bound.md) remains available in every dimension.

For the finite range $3\leq n\leq 12$, the compact determinant certificates improve the upper side to

$$ W(n) \leq \left\lceil \frac{2^n-1}{n} \right\rceil. $$

This counting lemma does not identify the exact invariant $H^{\ast}(f)$. It shows that any exact invariant must be able to take exponentially large values on typical Boolean functions.

## Lean Correspondence

The complete finite reduction is kernel-checked in `formalization/HeadComplexity/Results/CountingLowerBound.lean`. The multivariate Warren inequality is isolated as the proposition `WarrenStrictSignPatternBound`; it is an explicit premise of the final counting theorems and is not introduced as an axiom.

- `card_countingParameter` proves the exact parameter count $1+2H(n+1)$.

- `countingClearedPoly_totalDegree_le` and `eval_countingClearedPoly` prove that every fixed-input parameter polynomial has degree at most $H+1$ and specializes exactly to the cleared affine-fraction score.

- `mem_strictPatterns_of_computable` performs strictification and proves that every $H$-head truth table belongs to the resulting strict sign-pattern family.

- `card_headComputableFunctions_le_warren` is the faithful specialization of Warren's displayed real-valued estimate.

- `card_headComputableFunctions_le_two_pow_of_warren` proves the explicit bound $2^{35n^2H}$ for $1\leq n$, $1\leq H\leq2^n$, including the trivial branch where the parameter count exceeds the number of cube inputs.

- `card_headComputableFunctions_mul_deficit_le_all_of_warren`, `exists_HStar_gt_of_warren`, and `worstCaseHeadComplexity_gt_div_of_warren` prove the finite density deficit, existence of hard truth tables, and an explicit division-form worst-case lower bound.

- `card_all_booleanFunctions` proves the exact total count $2^{2^n}$, while `worstCaseHeadComplexity_le` proves the matching elementary upper side $W(n)\leq2^n-1$.

The pinned Mathlib version does not contain the required multivariate Warren, Milnor-Thom sign-pattern theorem. Consequently, only that analytic inequality remains external; all head-model, polynomial-degree, finite-counting, and worst-case deductions from it are axiom-clean Lean theorems.
