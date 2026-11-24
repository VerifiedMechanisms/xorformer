# Two original heads can require three adaptive affine product atoms

## Statement and verification status

There exists a strict Boolean target on $38$ input bits represented by two admissible original affine-ratio heads and a free bias, which has no strict sign representation by two affine-times-product atoms and a free bias. The product factors and affine numerators may be chosen jointly and depend arbitrarily on the target.

This is a finite exact separation, not an asymptotic lower bound. It refutes same-width adaptive compilation at width two. It does not refute compilation using $O(H)$ product atoms or any fixed larger constant factor.

The construction uses the rational certificate `two_head_six_row_sign_rank_candidate.json`. Despite its discovery filename, every entry needed for the theorem is independently verified with exact `Fraction` arithmetic by `check_two_head_adaptive_product_separation.py`. The checker imports no numerical solver. Its output is saved in `two-head-adaptive-product-exact-audit.json`. The general rank argument below is a written proof. No Lean verification is claimed.

## The exact finite certificate

Use six row coordinates and $32$ column coordinates. The row parameters are

$$ u=(9,15,11,1,3,13),\qquad z=(12,14,11,5,8,27), $$

$$ r=(18,28,30,-22,15,27),\qquad t=(23,27,-4,11,-30,-16). $$

For each column $j$, the JSON certificate supplies rational parameters $(v_j,q_j,s_j,w_j)$ and a six-bit sign code. Define the table with six rows and $32$ columns

$$ R_{ij}=\frac{r_i+s_j}{u_i+v_j}+\frac{t_i+w_j}{z_i+q_j}. $$

The exact checker verifies all of the following:

1. Every $u_i+v_j$ and $z_i+q_j$ is strictly positive.

2. All $192$ entries are nonzero and have the recorded signs.

3. The $32$ recorded sign columns contain exactly one representative from every antipodal pair in $\lbrace-1,1\rbrace^6$.

4. The minimum absolute entry is exactly $1/20670$.

The numerical discovery used linear programming only to propose rational column witnesses. Those numerical calculations are not used in the exact verification or the rank argument.

## Compilation into the original model

Let $u_{\min}=\min_i u_i$, $z_{\min}=\min_i z_i$, $v_{\min}=\min_jv_j$, and $q_{\min}=\min_jq_j$. Set

$$ \varepsilon=\frac14\min(u_{\min}+v_{\min},z_{\min}+q_{\min})\gt0. $$

On $x\in\lbrace0,1\rbrace^{38}$, define the affine denominator $B_1$ to have constant $u_{\min}+v_{\min}-2\varepsilon$, row slopes $u_i-u_{\min}+\varepsilon$, and column slopes $v_j-v_{\min}+\varepsilon$. Define $B_2$ by the same construction using $z$ and $q$.

Every slope and both constants are strictly positive. The exact constants are $1/2048$ and $4077/38912$, and the smallest slope among both denominators is $1/4096$. Consequently both denominators are positive on the entire Boolean cube and obey the original strict coherence condition.

Let $A_1$ have zero constant, row slopes $r_i$, and column slopes $s_j$. Let $A_2$ have zero constant, row slopes $t_i$, and column slopes $w_j$. Their slopes are unrestricted because both denominators are nonconstant. At the input with row bit $i$ and column bit $j$ set to one, and every other bit zero, the score $A_1/B_1+A_2/B_2$ equals $R_{ij}$ exactly.

To make the score strict at every cube vertex, including vertices outside the selected table, add the bias

$$ c=\frac{\sqrt2}{82680}. $$

Every unperturbed cube score is rational. The bias is irrational, so no perturbed score is zero. Also $0\lt c\lt1/41340$, which is less than the minimum absolute selected entry. Hence the selected $192$ signs are unchanged. Define the Boolean target $F$ to be the sign of this strict full-cube score. This is an admissible original representation with two heads.

## The sign rank is six

Consider any real matrix $M$ having the certified sign pattern. If its rank were less than six, a nonzero vector $a\in\mathbb R^6$ would satisfy $a^{\mathsf T}M=0$.

Extend the signs of the nonzero coordinates of $a$ to an arbitrary vector $\sigma\in\lbrace-1,1\rbrace^6$. Some certified column has sign $\sigma$ or $-\sigma$, because all antipodal classes are represented. In the former case every nonzero summand of $\sum_i a_iM_{ij}$ is positive; in the latter case every nonzero summand is negative. At least one summand is nonzero. Either case contradicts $a^{\mathsf T}M=0$.

Thus every matrix with this sign pattern has rank six. In particular, its sign rank is six.

## Two affine product atoms have rank at most five

Allow the very general product atom

$$ \Phi(x)=L(x)\prod_{k=1}^{38}g_k(x_k), $$

where $L$ is affine and each $g_k$ is an arbitrary real-valued function on one bit. This includes positive product parameters and also permits zero or negative factors.

At the selected row-column inputs, split the product into a row factor $U_i$ and a column factor $V_j$. Write $L$ at those inputs as $a_0+a_i+b_j$. Then

$$ \Phi_{ij}=\big((a_0+a_i)U_i\big)V_j+U_i\big(b_jV_j\big). $$

This is a sum of two rank-one matrices. A free bias contributes at most rank one. Therefore two arbitrary affine product atoms plus a bias have matrix rank at most five on the selected inputs. Such a score cannot realize a sign pattern of sign rank six.

This argument permits the entire replacement to depend jointly on the target. It is not an atomwise substitution obstruction, and no original denominator directions are held fixed.

## Consequences and limitations

The constructed target has original head complexity exactly two: a single positive-denominator head has the signs of an affine function, whose selected row-column table has rank at most two. The sign-rank-six submatrix excludes that possibility.

Every affine-times-product representation of this target requires at least three atoms, even with a free bias. If affine prefactors are disallowed, every product atom has rank at most one, so at least five product atoms are required with a free bias.

The three-atom lower bound is sharp for two original heads. To see this, absorb the output bias into the first affine numerator and write the score as $A/B+D/C$, with $B,C\gt0$ on the cube. For $t\gt0$, define

$$ T_t=A(e^{tC}-1)+D(e^{tB}-1)=Ae^{tC}+De^{tB}-(A+D). $$

At every cube vertex,

$$ \lim_{t\to0^+}\frac{T_t}{t}=AC+DB=BC\left(\frac AB+\frac DC\right). $$

If the original score is strict, the limit has its sign. Finiteness of the cube gives one sufficiently small positive $t$ for which all signs agree simultaneously. The exponential of an affine Boolean form is a product of positive one-bit factors, so $T_t$ is a sum of three affine-times-product atoms.

This upper bound is formalized by `HeadComplexity.TwoHeadProductCompilation.uniform_two_head_sign_compilation` and `HeadComplexity.TwoHeadProductCompilation.affine_exponential_product` in `formalization/HeadComplexity/Research/TwoHeadProductCompilation.lean`. The finite lower-bound certificate and sign-rank argument remain exact computation and written proof respectively.

Thus three affine product atoms are necessary for this target and sufficient for every strict two-head target. For arbitrary head counts, the separate theorem in `adaptive_product_compiler_logarithmic_obstruction.md` excludes a uniform constant-overhead adaptive compiler. A dimension-dependent overhead such as $O(\log n)$ remains open and could still support the desired unrestricted lower-bound route.
