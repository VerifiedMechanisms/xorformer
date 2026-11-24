# Compact analytic charts for bounded coherent reciprocal atoms

## Status and scope

This note gives an exact compact parameterization of every individual bounded original-model atom. Arbitrarily large or small denominator coefficient ratios are included in the closures of finitely many charts whose evaluation denominators stay uniformly away from zero. The result isolates cancellation between different heads as the remaining source of poor relative margin. It does not bound that cancellation or prove an unrestricted head lower bound.

The proof is written mathematics and has not been formalized in Lean.

## Theorem

Let $n\geq1$. Every atom $\phi=A/B$ in the original model with $\|\phi\|_\infty\leq1$ belongs to one of at most $2(n+1)!$ families parameterized by

$$ (t,v)\in[0,1]^n\times[-1,1]^{n+1}. $$

For each fixed chart and Boolean input, its value is a rational function $N_x(t,v)/D_x(t)$. The denominator is a polynomial of degree at most $n$, the numerator has total degree at most $n+1$, and

$$ 1\leq D_x(t)\leq n+1 $$

throughout the closed parameter box. Consequently every chart is real analytic on a neighborhood of that box, simultaneously at all cube inputs. The chart families may contain additional tables that do not obey the original atom restriction.

## Proof

Reflect all coordinates of a head when its denominator slopes are negative. In the resulting coordinates $y$, write

$$ B(y)=b_0+\sum_{i=1}^n b_i y_i,\qquad b_0\gt0,\qquad b_i\geq0. $$

There are two orientation choices. Let $v_0=\phi(0)$ and $v_i=\phi(e_i)$, so all $v_i$ lie in $[-1,1]$. Affineness determines the numerator exactly:

$$ A(y)=b_0\left((1-|y|)v_0+\sum_{i=1}^n y_i v_i\right)+\sum_{i=1}^n b_i y_i v_i. $$

Choose one of the $(n+1)!$ permutations $\pi$ such that $b_{\pi(0)}\geq\cdots\geq b_{\pi(n)}$. Scale every coefficient by the positive largest coefficient. Write the resulting ordered coefficients as products

$$ b_{\pi(k)}/b_{\pi(0)}=\prod_{\ell=1}^k t_\ell,\qquad 0\leq t_\ell\leq1. $$

When the preceding coefficient is positive, choose its actual consecutive ratio. After the first zero coefficient, take the remaining ratios to be zero. This gives the displayed identity in the constant-denominator case too.

For a fixed input $y$, the set of present indices is

$$ I(y)=\lbrace0\rbrace\cup\lbrace i:y_i=1\rbrace. $$

Let $r(y)$ be the smallest order position whose index belongs to $I(y)$. For each present index $i=\pi(k)$, define the polynomial

$$ w_i(t;y)=\prod_{\ell=r(y)+1}^{k}t_\ell. $$

The empty product corresponding to $i=\pi(r(y))$ is one. Set $w_i(t;y)=0$ for absent indices, for use in the sums below. The index $0$ is always present, so $w_0$ is always defined by the product formula. At parameters coming from an actual admissible atom the present-index polynomials are precisely $b_i/q(y)$, where $q(y)=b_{\pi(r(y))}\gt0$.

Define the chart at every point of the closed parameter box by

$$ D_y(t)=\sum_{i\in I(y)}w_i(t;y),\qquad N_y(t,v)=w_0(t;y)\left((1-|y|)v_0+\sum_{i=1}^n y_i v_i\right)+\sum_{i=1}^n y_i w_i(t;y)v_i. $$

Each factor $w_i$ lies in $[0,1]$, and one equals one. Hence $1\leq D_y\leq n+1$. Its degree is at most $n$, while the numerator degree is at most $n+1$. At the parameters of the original atom, dividing the numerator and denominator formulas by $q(y)$ proves $\phi(y)=N_y/D_y$.

The displayed formulas define the chart even at parameters for which a canceled common coefficient would be zero. They are therefore a genuine compact extension, not a division by a vanishing coefficient. Since there are finitely many inputs and the denominators are strictly positive on the compact box, every chart extends analytically to a common open neighborhood of that box. $\blacksquare$

## A uniform neighborhood estimate

One can make the last assertion quantitative. For $t\in[0,1]^n$, allow each coordinate a complex perturbation of absolute value at most

$$ \rho=\frac{1}{8n(n+1)}. $$

Every monomial $w_i$ is a product of at most $n$ distinct coordinates. Telescoping the difference of the perturbed product and the original product bounds it by $n\rho(1+\rho)^{n-1}\leq2n\rho$. Summing at most $n+1$ monomials gives $|D_y(z)-D_y(t)|\leq1/4$. Thus $|D_y(z)|\geq3/4$ for every input throughout this neighborhood. The numerator is polynomial and causes no poles.

## Why this does not repair sparse margins

For a general head, first divide its table by its positive supremum norm and put that norm into its external coefficient. The zero atom needs no parameterization. Every finite representation can therefore be written using bounded atoms from the compact chart families and signed external coefficients. Dividing all coefficients and the free bias by their total absolute sum makes that coefficient vector compact too.

This normalization does not keep the resulting score away from the zero table. Different atoms can approach an exact linear dependence while their coefficients remain bounded and their total absolute sum stays one. After dividing a small resulting score by its own norm, limiting derivative directions can appear. The compact chart theorem supplies no uniform bound on the order of those cancellations, no lower bound on the best relative margin at a fixed head count, and no control of the number of strict Boolean labels of those limiting directions.

In particular, coefficient-scale compactness alone cannot replace the missing width-preserving margin repair in `margin_sensitive_polynomial_capacity.md`.
