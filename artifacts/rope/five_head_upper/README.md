# Five vanilla heads for the explicit pure separation

This certificate improves the vanilla upper bound in [Theorem 22](../../../theorems/03_rotary_attention/022_explicit_pure_rope_separation.md) to five heads. Together with its lower bound, the explicit function has three pure RoPE heads and between four and five vanilla heads. The exact vanilla minimum remains open.

## Exact five fractions

Use the theorem's rational forms $S_h$, $B_h$, and $D_h=1+B_h$, its positive rational margin $\varepsilon$, and set

$$ U_0=S_0-\varepsilon D_0,\qquad U_1=S_1,\qquad U_2=S_2,\qquad G=U_0D_1D_2+U_1D_0D_2+U_2D_0D_1. $$

The full-cube certificate gives $|G|\geq\varepsilon/8$, with the sign prescribed by the Boolean function. Define

$$ E=10D_0-D_1,\qquad u=D_0,\qquad v=D_2,\qquad a=\frac{\varepsilon}{2^{40}}. $$

Take readout constant zero and the following five denominator and numerator pairs. Each numerator is affine in the original input bits.

| Head | Denominator | Numerator |
| --- | --- | --- |
| 0 | $E$ | $(10-2a)U_0+U_1+(10-2a)U_2$ |
| 1 | $E+au$ | $-10U_0-U_1+(-20+2a)U_2$ |
| 2 | $E+2au$ | $10U_2$ |
| 3 | $E+av$ | $(-10+2a)U_0-U_1$ |
| 4 | $E+a(u+v)$ | $10U_0+U_1$ |

Let $T_a$ be their sum. These are exact rational parameters, including the specified rational value of $a$; no limiting parameter is left to choose.

## Admissibility in the original model

The earlier cube bounds give $1/2\lt D_h\lt2$, $|U_h|\lt2$, and therefore $E\gt3$. All five denominators are positive on the entire cube.

For each group index $i\in\lbrace1,\ldots,14\rbrace$, direct exact arithmetic gives

$$ 10b_{0i}-b_{1i}\leq-\frac{411}{16\cdot10^9}. $$

Every denominator in the table has centered group slope $10b_{0i}-b_{1i}+a(c_0b_{0i}+c_2b_{2i})$, where $(c_0,c_2)$ belongs to $(0,0),(1,0),(2,0),(0,1),(1,1)$. Since $|b_{hi}|\lt1$ and $\varepsilon\lt1/16$,

$$ |a(c_0b_{0i}+c_2b_{2i})|\leq2a\lt2^{-43}\lt\frac{411}{16\cdot10^9}. $$

Thus every centered slope is strictly negative. Each original bit slope is the corresponding centered slope multiplied by $2/m$, so it is strictly negative as well. Positive cube denominators with uniformly negative slopes, and arbitrary affine numerators, are exactly admissible original vanilla atoms. The established scalar-to-shared-architecture equivalence therefore implements all five fractions in the unchanged original xorformer architecture, at finite width and with real parameters.

## Full-cube sign verification

For positive $E,u,v,a$, define the exact reciprocal differences

$$ \delta_u=\frac1E-\frac1{E+au},\qquad \Delta_{uv}=\frac1E-\frac1{E+au}-\frac1{E+av}+\frac1{E+a(u+v)}. $$

Collecting the five fractions gives

$$ \frac{T_a}{a^2}=10U_2\frac{\Delta_{uu}}{a^2}+(10U_0+U_1)\frac{\Delta_{uv}}{a^2}-2U_2\frac{\delta_u}{a}-2U_0\frac{\delta_v}{a}. $$

The exact identities

$$ \frac{\delta_u}{a}=\frac{u}{E(E+au)},\qquad \frac{\Delta_{uv}}{a^2}=uv\left(\frac1{E(E+au)(E+av)}+\frac1{(E+au)(E+av)(E+a(u+v))}\right) $$

imply, for $0\lt u,v\lt2$,

$$ \left|\frac{\delta_u}{a}-\frac{u}{E^2}\right|\leq\frac{8a}{E^3},\qquad \left|\frac{\Delta_{uv}}{a^2}-\frac{2uv}{E^3}\right|\leq\frac{96a}{E^4}. $$

For completeness, subtracting two products of three reciprocals one factor at a time bounds the second difference by $3auv(u+v)/E^4\leq48a/E^4$, which is stronger than the displayed bound. The first difference is exactly $au^2/[E^2(E+au)]\leq4a/E^3$ in absolute value. These algebraic estimates also apply when $v=u$.

Since $D_1=10u-E$, the desired leading term is

$$ G=10U_2u^2+(10U_0+U_1)uv-E(U_2u+U_0v). $$

Using $|U_h|\lt2$ and $E\gt3$, the total error satisfies

$$ \left|\frac{T_a}{a^2}-\frac{2G}{E^3}\right|\leq\frac{4032a}{E^4}+\frac{64a}{E^3}\leq\frac{4096a}{E^3}=\frac{\varepsilon}{2^{28}E^3}\lt\frac{\varepsilon}{4E^3}\leq\left|\frac{2G}{E^3}\right|. $$

Consequently $T_a$ has exactly the sign of $G$ at every Boolean input. This proves the five-head upper bound without enumerating the enormous cube. $\blacksquare$

## Reproduction and scope

Run `python3 artifacts/rope/five_head_upper/verify.py`. The script uses only exact rational arithmetic and integer polynomial identities. It checks the reciprocal identities, the collected five numerators, the target identity, every group slope bound, and all numerical constants in the sign estimate. It does not substitute sampling for the full-cube proof above.

The accompanying Lean generic five-head compiler and the concrete oriented denominator certificate provide the corresponding formal upper bound; the explicit rational step size and its error estimate are recorded here independently of the limiting compiler.
