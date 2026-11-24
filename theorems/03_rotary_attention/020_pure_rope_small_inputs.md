# Theorem 20. Pure Rotary Equality on at Most Four Input Bits

## Statement

For every $0 \leq n \leq 4$, every Boolean function $f$ on $n$ bits, and every head count $H$, pure RoPE computes $f$ with $H$ heads if and only if unchanged vanilla attention does. Consequently their minimum head counts agree.

The statement includes $n=0$ and $H=0$. By [Theorem 18](018_pure_rope_architectural_bridge.md), it applies to the literal rectangular architecture, both standard fixed rotary frequencies and freely chosen frequencies, a fixed query attending to the input positions and itself, and unrotated token-only values. Width and real parameters remain unrestricted and finite.

The main new finite classification is:

$$ f \neq \mathrm{PARITY}_4 \text{ and } f \neq \neg\mathrm{PARITY}_4 \quad\Longrightarrow\quad H^{\ast}_{\mathrm{vanilla}}(f) \leq 3. $$

All statements in this note are proved in Lean without `sorry` or new axioms. This is a result for at most four input bits, not a proof for arbitrary input lengths.

## Three-bit exact score interpolation

Every real-valued function on the three-bit cube has an exact representation as a constant plus three vanilla-admissible affine fractions. Use the denominators

$$ D_1=1+x_1+x_2+x_3,\qquad D_2=1+x_1+2x_2+2x_3,\qquad D_3=1+2x_1+x_2+2x_3. $$

The eight functions

$$ 1,\quad x_1/D_1,\quad x_2/D_1,\quad x_3/D_1,\quad x_1/D_2,\quad x_2/D_2,\quad x_3/D_2,\quad x_1/D_3 $$

form an interpolation basis. With vertices in lexicographic order, their evaluation matrix has determinant $-1/27993600$. `exists_threeBit_affineFraction_score` verifies an explicit integer inverse, symbolically in the eight prescribed function values. All denominator slopes are strictly positive, so the unchanged affine-fraction normal form realizes these three fractions.

## Four-bit certificate

### Theorem 1. Three fixed denominator families

The certificate uses the following three families. Each row in a family is the slope vector of one denominator, whose constant term is $1$.

| Family | First denominator slopes | Second denominator slopes | Third denominator slopes |
|---|---|---|---|
| 0 | $(17,17,3,2)$ | $(3,19,14,13)$ | $(9,12,4,13)$ |
| 1 | $(1,1,1,1)$ | $(2,2,2,2)$ | $(3,3,3,3)$ |
| 2 | $(16,11,4,13)$ | $(11,11,1,3)$ | $(6,4,18,8)$ |

For one family, write its denominators as $D_1,D_2,D_3$, and put $Q=D_1D_2D_3$. The associated integer feature matrix has sixteen rows and thirteen columns:

$$ T(x)=\bigl(Q(x), x_1D_2D_3,\ldots,x_4D_2D_3, x_1D_1D_3,\ldots,x_4D_1D_3, x_1D_1D_2,\ldots,x_4D_1D_2\bigr). $$

Thus every coefficient vector $a$ gives a three-head vanilla score:

$$ \frac{T(x)a}{Q(x)}=a_0+\sum_{h=1}^{3}\frac{\sum_{i=1}^{4}a_{4(h-1)+i}x_i}{D_h(x)}. $$

Since $Q$ is strictly positive at every Boolean input, the integer feature value and this score have the same strict sign. `FourBitCertificate.score_eq` verifies this identity for every family and vertex, with arbitrary integer coefficients.

### Theorem 2. Exact strict-sign templates

A template consists of integer coefficient vectors $b,u_0,\ldots,u_{15}$, an integer $\delta \gt 0$, and four prescribed input signs. Let $I$ be the four-element support. Outside $I$, the certificate checks

$$ T(v)b=0,\qquad T(v)u_j=\begin{cases}\delta&j=v,\cr 0&j\neq v.\end{cases} $$

On the support it checks the strict dominance inequalities

$$ |T(v)b|\gt\sum_{j=0}^{15}|T(v)u_j|,\qquad v\in I, $$

together with the prescribed sign of $T(v)b$. Given any target signs $y_j\in\lbrace-1,1\rbrace$ extending the four prescribed signs, take

$$ a=b+\sum_{j=0}^{15}y_j u_j. $$

Outside the support, $T(v)a=\delta y_v$. On the support, the triangle inequality and the strict dominance bound preserve the prescribed sign. Negating the construction handles the opposite orientation of the same four signs.

This argument is `SignTemplate.exists_strict_score_or_neg`. All 24 templates are checked with integer arithmetic by `decide +kernel`; no numerical linear-programming result is assumed.

### Theorem 3. Finite coverage

Number the vertices from $0$ to $15$ in lexicographic order. Encode a labeling as an integer whose bit at position $v$ is the label at vertex $v$. A support mask $s$ and positive mask $p$ cover the label masks $z$ satisfying either

$$ z\mathbin{\&}s=p\qquad\text{or}\qquad z\mathbin{\&}s=s\mathbin{\oplus}p. $$

The 24 checked templates have the following masks.

| Template | Family | Support mask | Positive mask |
|---|---|---|---|
| 0 | 0 | 15 | 14 |
| 1 | 0 | 23 | 21 |
| 2 | 0 | 51 | 51 |
| 3 | 0 | 275 | 259 |
| 4 | 2 | 23 | 18 |
| 5 | 2 | 32781 | 32772 |
| 6 | 2 | 278 | 272 |
| 7 | 0 | 33797 | 32769 |
| 8 | 0 | 180 | 160 |
| 9 | 2 | 45 | 44 |
| 10 | 0 | 35841 | 35841 |
| 11 | 0 | 29 | 29 |
| 12 | 2 | 4110 | 4102 |
| 13 | 0 | 4172 | 4104 |
| 14 | 2 | 298 | 264 |
| 15 | 1 | 4193 | 4192 |
| 16 | 1 | 1098 | 1098 |
| 17 | 0 | 12354 | 12352 |
| 18 | 0 | 20483 | 20481 |
| 19 | 0 | 4290 | 4288 |
| 20 | 0 | 4865 | 4097 |
| 21 | 1 | 1112 | 1112 |
| 22 | 1 | 360 | 360 |
| 23 | 2 | 51 | 50 |

These cylinders cover every one of the $65534$ nonparity labelings. The only uncovered masks are $27030$ and $38505$, respectively parity and its complement. `FourBitCertificate.mask_coverage` proves this finite fact with a 163-node Boolean decision tree using ordinary case splits and simplification. The independent checker [check_four_bit_three_head_circuits.py](../../artifacts/rope/certificates/check_four_bit_three_head_circuits.py) also verifies exact integer ranks, kernel relations, four-row circuits, and coverage from [the compact circuit certificate](../../artifacts/rope/certificates/four_bit_three_head_circuits.json).

The integer template certificate is stronger than trusting the circuit-generation procedure: Lean checks the interpolation and dominance identities themselves. The generator and the Python checker are not axioms of the Lean result.

Combining coverage, strict-sign templates, and the exact feature-to-fraction identity proves `vanilla_three_computes_fourBit_nonparity`.

## Equality at every head count

If $H\leq2$, [Theorem 16](016_pure_rope_two_heads.md) supplies the reverse implication for every input length. If $H\geq3$, every target on at most three input bits has a three-head vanilla implementation. On four bits, the certificate handles every target except parity and its complement.

Parity and its complement are symmetric functions with four sign changes. Positive-denominator clearing proves that any pure realization has at least four heads; the existing symmetric-function construction realizes them with four vanilla heads. Unused heads can be padded by identically zero admissible fractions. This proves the reverse implication at the original head count in all cases.

The forward implication is already known. Therefore pure and vanilla computability agree at every head count, and their minimum counts agree, for every input length at most four. $\blacksquare$

## Lean declarations

- [RoPESmallInputs.lean](../../formalization/HeadComplexity/Results/RoPESmallInputs.lean): `exists_threeBit_affineFraction_score`, `computableWithSharedHeadsN_mono`, `pureRoPEComputable_iff_vanilla_of_input_le_three`.
- [FourBitThreeHeadCertificate.lean](../../formalization/HeadComplexity/Results/FourBitThreeHeadCertificate.lean): `SignTemplate.exists_strict_score`, `SignTemplate.exists_strict_score_or_neg`.
- [FourBitThreeHeadData.lean](../../formalization/HeadComplexity/Results/FourBitThreeHeadData.lean): `FourBitCertificate.certificates_valid` and all 24 individual integer certificates.
- [FourBitThreeHeadCoverage.lean](../../formalization/HeadComplexity/Results/FourBitThreeHeadCoverage.lean): `FourBitCertificate.mask_coverage`, `FourBitCertificate.maskMatches_matches`.
- [FourBitThreeHeadRealization.lean](../../formalization/HeadComplexity/Results/FourBitThreeHeadRealization.lean): `FourBitCertificate.score_eq`, `FourBitCertificate.vanilla_of_strict_feature_score`.
- [RoPEFourInputs.lean](../../formalization/HeadComplexity/Results/RoPEFourInputs.lean): `vanilla_three_computes_fourBit_nonparity`, `vanilla_of_pureRoPEComputable_symmetric`, `pureRoPEComputable_iff_vanilla_of_input_le_four`, `pureRoPEHStar_eq_vanilla_of_input_le_four`.

No existing vanilla architectural definition is changed. Any strict separation must therefore use at least five inputs and at least three pure heads. [Theorem 22](022_pure_rope_three_head_separation.md) gives a mathematical separation for a sufficiently large replicated family; it does not determine the smallest separating input length.
