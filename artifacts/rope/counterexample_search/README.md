# Exact Compilers And Targeted Pure Rotary Searches

No pure-RoPE versus vanilla Boolean separation is certified here.

## Exact two-head compilation

`compile_pure_two.py` constructs two vanilla heads directly from a strict rational two-head pure certificate. It does not use the stored vanilla fits or an optimizer.

For a pure atom with affine numerator $N$ and denominator $D$, unequal token values give a positive affine form $B$ in their span whose slopes are all strictly positive or all strictly negative. For example, if $v_1\gt v_0$ and the query value exceeds $v_0$, take $B=N-v_0D$. Its constant is positive and its slopes are $(v_1-v_0)b_i\gt0$. The other endpoint handles the remaining query values and the reversed token ordering.

After rewriting the cleared two-head polynomial as $AB+CD$, choose a positive integer $e$ large enough that $E=eB+D$ has the same strict slope orientation as $B$. Both denominators are positive, and

$$ \frac{C}{B}+\frac{A-eC}{E}=\frac{AB+CD}{BE}. $$

If both pure heads have equal token values, the script first changes one token-one value by an explicit rational amount smaller than half the minimum strict score margin. This preserves every Boolean label and supplies a nonconstant numerator pencil.

The compiler was checked on all 830 previously committed pure certificates, covering 1,441,280 cube vertices. Two records used the finite perturbation. Every output denominator and every classification were checked with exact integers and rational numbers.

```bash
heavy python3 artifacts/rope/counterexample_search/compile_pure_two.py \
  artifacts/rope/search/exact_n8_n10.jsonl \
  artifacts/rope/search/exact_n12.jsonl \
  artifacts/rope/search/exact_cancellation_n10.jsonl
```

The universal handwritten and Lean results are recorded in the main theorem notes. This script is a constructive certificate check, not a substitute for those proofs or the scalar-to-architecture bridge.

## Mixed tribes

Split the bits into three terms. Each term requires some specified bits to equal one and the remaining specified bits to equal zero. The function is true if any term is completely matched.

For the balanced family, each term has $m$ specified ones and $m$ specified zeros, so there are $n=6m$ bits. Let $d_h$ count mismatched literals in term $h$. Three pure atoms give the exact score

$$ S(x)=-5+\sum_{h=1}^{3}\frac{1}{1/10+d_h(x)}. $$

At a true input, $S\geq5$. At a false input, $S\leq30/11-5=-25/11$. Thus all signs are strict.

Exact integer atom parameters are obtained by setting $U=10(n+1)$, query weight $\gamma=1$, token values $v_0=v_1=0$, and query numerator $\eta=U$. At a required-one coordinate take $(a_i,b_i)=(1+U,1)$; at a required-zero coordinate take $(a_i,b_i)=(1,1+U)$; outside the term take $(a_i,b_i)=(1,1)$. Then $D=(n+1)(1+10d_h)$ and the atom equals the displayed reciprocal. The fixed-frequency scalar-to-architecture construction of Theorem 14 realizes these positive rational atoms.

### Threshold degree

For every $m\geq2$, the balanced family has threshold degree exactly three. The pure score gives the upper bound after clearing denominators. For the lower bound, restrict each term to four free literals by fixing all other literals to their required values. Complementing some coordinates converts these free literals into ordinary match bits without changing polynomial degree.

Average any hypothetical strict quadratic sign polynomial over permutations within each four-literal term and permutations of the three terms. If $w_1,w_2,w_3$ are the three match counts, the averaged polynomial lies in the span of

$$ 1,\qquad w_1+w_2+w_3,\qquad w_1^2+w_2^2+w_3^2,\qquad w_1w_2+w_1w_3+w_2w_3. $$

The count vectors $(0,3,3)$ and $(1,1,4)$ have different labels but identical feature vectors $(1,6,18,9)$. This contradicts strict sign representation. The verifier checks this exact moment identity. Averaging is used only for the degree lower bound; no symmetry restriction on competing vanilla architectures is inferred.

### Matching vanilla certificates

| Bits | Term width | Exact vanilla certificate | Verification domain |
| --- | --- | --- | --- |
| 9 | 3 | Three heads | All 512 cube inputs |
| 12 | 4 | Three heads | All 4,096 cube inputs |
| 18 | 6 | Three heads | All 4,096 six-group count tuples |
| 24 | 8 | Three heads | All 15,625 six-group count tuples |

The 12-, 18-, and 24-bit examples therefore have exactly three pure heads and exactly three vanilla heads. For the nine-bit example only the three-head upper bounds are asserted here; its threshold degree is two.

`exact_mixed_tribes.jsonl` stores the nine- and twelve-bit certificates. `exact_mixed_tribes_grid.jsonl` stores the larger certificates. In the latter, every coefficient is constant within each literal group. Each denominator is written in the six integer centered counts $Z_g=2c_g-m$ and satisfies $D_0\gt m\sum_g|D_g|$. Its slopes have one strict common sign. The same coefficients, shared over the original bits in each group, are therefore admissible vanilla denominators. Count-grid verification covers every Boolean input exactly.

```bash
python3 artifacts/rope/counterexample_search/verify_mixed_tribes.py \
  artifacts/rope/counterexample_search/exact_mixed_tribes.jsonl
python3 artifacts/rope/counterexample_search/verify_mixed_tribes_grid.py \
  artifacts/rope/counterexample_search/exact_mixed_tribes_grid.jsonl
```

These verification commands use only the Python standard library. NumPy and SciPy are imported only by the optional rationalization paths.

Twelve random fitting restarts failed for the 24-bit example. Continuing from the exact 18-bit solution then produced a valid certificate. The failed restarts were inconclusive and were never used as a lower bound.

## Other targeted searches

`search_g12_pure_three.py` explored the twelve-bit four-vanilla-head quadratic and a fresh-bit XOR of the seven-bit retained example. The twelve-bit search was stopped when the symbolic pure-three obstruction was obtained. No certificate was found for the XOR target; its search status remains inconclusive.

`pure_fixed_denominator_lp.py` uses a linear characterization of the pure numerator cone for fixed centered denominator directions. For each choice of the sign $e$ of the token-value difference, it introduces $K\gt0$ and requires

$$ e(u_i-\ell\beta_i)\gt K|\beta_i|,\qquad \sum_i e(u_i-\ell\beta_i)\lt K. $$

These inequalities are equivalent to $u=ks+\ell\beta$, $|\beta_i|\lt s_i$, and $\sum_i s_i\lt1$, with $k=eK$. All numerator and value choices with nonzero token-value difference are included at those fixed denominators. Sampling denominator directions still does not exclude untested representations.

No original model definition, threshold convention, or architectural admissibility condition is changed by these experiments.
