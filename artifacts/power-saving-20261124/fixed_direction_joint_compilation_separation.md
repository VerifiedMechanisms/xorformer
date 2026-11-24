# Joint Numerator Recalibration Does Not Repair Fixed Exponential Directions

## Status

This is a new obstruction proved during the 2026-11-24 run. Two admissible reciprocal heads realize a strict four-bit table that cannot be represented using the corresponding two exponential directions, even after jointly changing both affine numerators and the free bias. The directions and their common scale are fixed in this comparison. Arbitrarily choosing new exponential directions remains allowed in the open compilation problem, so this is not a lower bound for unrestricted head complexity.

The exact finite reciprocal witness and the exponential impossibility are formalized in `formalization/HeadComplexity/Research/RadialSpanSeparation.lean`. The Grassmannian limit calculation below is a separate written proof.

## Exact two-head witness

On $\lbrace0,1\rbrace^4$, put

$$ s=x_1+x_2+x_3+x_4,\qquad \Delta=x_1+x_2,\qquad a=x_1-x_2,\qquad u=x_3+x_4. $$

Define the target to be true exactly on the following inputs: $x_1=1$, $x_2=0$, and $u\geq1$; or $x_1=0$, $x_2=1$, and $u=0$. It is false when $x_1=x_2$.

The two-head score

$$ S(x)=\frac{-22a}{1+s/4}+\frac{26a-1/4}{1+(s+\Delta)/4} $$

strictly represents this target. Both denominators have positive constant one and strictly positive slopes on all four coordinates. Thus both heads are admissible in the original model; their arbitrary affine numerators are permitted.

**Proof.** Clearing the positive denominator product gives

$$ (1+s/4)(1+(s+\Delta)/4)S=a(u-1/2)-1/4-s/16. $$

Here $a\Delta=a$ on Boolean inputs. If $a=0$, the right side is negative. If $a=1$, it is negative at $u=0$ and positive at $u=1,2$. If $a=-1$, it is positive at $u=0$ and negative at $u=1,2$. None of these values is zero. $\blacksquare$

## Arbitrary recalibration of the same exponential directions fails

For every $t,c\in\mathbb R$ and arbitrary affine forms $U,V$, the score

$$ G(x)=c+U(x)e^{-ts(x)}+V(x)e^{-t(s(x)+\Delta(x))} $$

fails to represent this target, even with the convention that false inputs may have score zero.

**Proof.** Write $L_z=(1,0,z_1,z_2)$ and $R_z=(0,1,z_1,z_2)$. Multiply the score by the positive function $e^{ts(x)}$. Since $s(L_z)=s(R_z)=1+z_1+z_2$ and $\Delta(L_z)=\Delta(R_z)=1$, the difference between the two normalized rows is

$$ e^{ts(L_z)}G(L_z)-e^{ts(R_z)}G(R_z)=U(L_z)-U(R_z)+e^{-t}(V(L_z)-V(R_z)). $$

Both affine differences are independent of $z$. Thus one normalized row is everywhere at least the other; their positive suffix sets must be nested. The target instead makes $L_{(0,0)}$ false and $R_{(0,0)}$ true, but makes $L_{(1,0)}$ true and $R_{(1,0)}$ false. These strict inequalities force the same row difference to be both negative and positive. This is impossible. $\blacksquare$

An equivalent four-point identity, used in Lean, is

$$ G(L_{(1,0)})-G(R_{(1,0)})=e^{-t}\bigl(G(L_{(0,0)})-G(R_{(0,0)})\bigr). $$

The contradiction therefore holds for every real common scale, not only for small positive scales.

## A bounded analytic numerator path

The separation also occurs along fixed straight radial denominator germs with bounded analytic numerators. For $0\lt t\lt1/2$, define

$$ R_t(x)=\frac{-(1+3t/2)a}{1+ts}+\frac{(1+5t/2)a-t^2/4}{1+t(s+\Delta)}. $$

Direct expansion using $a\Delta=a$ gives

$$ (1+ts)(1+t(s+\Delta))R_t=t^2\bigl(a(u-1/2)-1/4-ts/4\bigr). $$

The factor in parentheses has the target signs throughout $0\lt t\lt1/2$. At the smallest positive value, attained when $a=1$ and $u=1$, it is $1/4-t/2\gt0$. All false entries remain negative. At $t=1/4$, multiplying this score by sixteen yields the displayed finite witness.

Thus failure is not caused by unbounded numerators or curved pole paths. Bounded analytic moving numerators of degree two already defeat any same-direction compilation that is allowed to recalibrate the exponential affine numerators and bias. This is stronger than merely observing that direct substitution with unchanged numerators can reverse a sign.

## The limiting numerator spaces differ

Let $\mathcal A$ denote all affine tables on the four-bit cube. The reciprocal numerator space after clearing positive denominators is, for $t\neq0$,

$$ \mathcal V_R(t)=\mathcal A(1+ts)+\mathcal A\Delta. $$

Set

$$ W=\mathrm{span}\lbrace1,x_1,x_2,x_1x_2,x_3,x_4,x_3\Delta,x_4\Delta\rbrace. $$

This space has dimension eight. The reciprocal family has dimension nine, and its limit is

$$ \lim_{t\to0}\mathcal V_R(t)=W+\mathrm{span}\lbrace a(x_3+x_4)\rbrace. $$

For an explicit basis, take the five tables $(1+ts)$ and $x_i(1+ts)$, the three tables $x_1\Delta,x_3\Delta,x_4\Delta$, and the ninth table $as$. The last belongs to the space because

$$ as=\frac{a(1+ts)-a\Delta}{t}. $$

Their nine limits are independent: the first eight span $W$, and $as=a+a(x_3+x_4)$ adds an antisymmetric suffix interaction. The space has dimension at most nine because the ten displayed affine-generator columns have the exact relation $\Delta(1+ts)-(1+ts)\Delta=0$. These independent limiting columns establish the claim.

For the full exponential numerator class, multiplying by $e^{ts}$ gives

$$ \mathcal V_E(t)=\mathcal A+\mathcal A e^{-t\Delta}+\mathrm{span}\lbrace e^{ts}\rbrace. $$

For $t\neq0$, its first two summands have dimension eight. On the first two coordinates, they span all four tables. Each suffix coordinate supplies the two tables $x_j$ and $x_je^{-t\Delta}$. Their limit is exactly $W$.

The final bias column adds a ninth direction whose limit modulo those eight columns is $x_3x_4$. To see the order explicitly, write $r=e^{-t}$, $q=e^t$, and expand

$$ e^{ts}=e^{t\Delta}\bigl(1+(q-1)(x_3+x_4)+(q-1)^2x_3x_4\bigr). $$

The suffix-free term is already in the four-dimensional prefix table space. For each suffix-linear term, approximate $e^{t\Delta}$ by $2-e^{-t\Delta}$; their difference is $O(t^2)$ uniformly on the finite prefix cube. Multiplying by $q-1=O(t)$ gives only $O(t^3)$. The remaining suffix-quadratic coefficient is $(q-1)^2e^{t\Delta}=t^2+O(t^3)$. After division by $t^2$, the extra direction therefore tends to $x_3x_4$.

Consequently

$$ \lim_{t\to0}\mathcal V_E(t)=W+\mathrm{span}\lbrace x_3x_4\rbrace. $$

This differs from the reciprocal limit. The strict sign separation above shows that the discrepancy is not merely about exact real-table equality.

## Verification boundary and remaining route

The Lean declarations `target_computableWith_two_heads` and `not_exponentialScore_represents_target` respectively connect the exact reciprocal witness to the original attention model and rule out every choice of affine numerators, bias, and common exponential scale for these two directions. The analytic path and Grassmannian limit calculation are written proofs, not Lean-checked limit theorems.

A joint transformation may choose entirely new directions, give each exponential its own scale, or increase the number of product atoms. The result does not exclude any of those possibilities. In particular, it supplies no fixed exponent saving for unrestricted worst-case head complexity.
