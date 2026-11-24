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

`search_mixed_tribes_active.py` continues a smaller certificate on a larger count grid, repeatedly adding violating inputs. The tested continuations at $m=5$ and $m=6$ did not produce a certificate. These are unresolved searches, including unrestricted vanilla representations that need not share coefficients within literal groups.

## Balanced parity extensions

`search_balanced_extension.py` extends a three-bit parity realization to ten or twelve bits. Every head has mixed denominator slopes whose sum is zero, so their span contains no strictly oriented slope vector. The extra slopes are chosen close to the denominator positivity boundary. This excludes a simple exact-score reorientation argument but does not itself imply a Boolean head lower bound.

The starting identity is the partial-fraction expansion

$$ \frac{s^3-4s}{\prod_{h=1}^{3}(1+t_hs)}=c_0+\sum_{h=1}^{3}\frac{\rho_h}{1+t_hs}. $$

At $s=z_1+z_2+z_3$ on three spins, the numerator is $6z_1z_2z_3$. The generator uses integer centered denominator slopes $\beta_{h1}=\beta_{h2}=\beta_{h3}=1000t_h$ and balances the remaining slopes so their total sum is zero. The denominator restricted to the face where every extra bit is zero is exactly $1000(1+t_hs)$.

Twenty-four of the certificates also use unequal token values $v_0=-k_h$ and $v_1=k_h$. Let $p_h=1000t_h$, choose centered masses $s_{hi}=|\beta_{hi}|+1$, and put $r_h=k_h(p_h+1)/p_h$. The query numerator is

$$ \eta_h=1000\rho_h+1000r_h+k_h\sum_{i\gt3}s_{hi},\qquad c=c_0-\sum_h r_h. $$

The balanced slopes give the restricted numerator $1000\rho_h+r_hD_h$, so the same parity restriction remains exact. All atom weights, query weights, query numerators, and readout constants are rational and stored explicitly.

`exact_balanced_extensions.jsonl` contains 56 matching pure and vanilla three-head certificates: eight ten-bit functions and 48 twelve-bit functions. Exact verification covers 204,800 cube vertices. The parity restriction proves threshold degree at least three: averaging a hypothetical degree-at-most-two sign polynomial against parity gives zero, whereas every signed summand would be strictly positive. Clearing the three positive denominators proves the matching degree upper bound. Thus every stored function has exactly three heads in both scalar models, and the established scalar-to-architecture bridges give the same architectural counts.

```bash
python3 artifacts/rope/higher_search/verify_small.py \
  artifacts/rope/counterexample_search/exact_balanced_extensions.jsonl
```

`certify_balanced_extension.py` rounds proposed vanilla coefficients and accepts only exact integer sign verification. It and the verifier use only the Python standard library. Six cases initially lacked numerical fits. One also timed out in all four complete real-algebraic orientation searches. Additional fitting produced exact vanilla certificates for all six, so neither the failed fits nor those timeouts supply a lower bound.

## Other targeted searches

`search_g12_pure_three.py` explored the twelve-bit four-vanilla-head quadratic and a fresh-bit XOR of the seven-bit retained example. The twelve-bit search was stopped when the symbolic pure-three obstruction was obtained. No certificate was found for the XOR target; its search status remains inconclusive.

`pure_fixed_denominator_lp.py` uses a linear characterization of the pure numerator cone for fixed centered denominator directions. For each choice of the sign $e$ of the token-value difference, it introduces $K\gt0$ and requires

$$ e(u_i-\ell\beta_i)\gt K|\beta_i|,\qquad \sum_i e(u_i-\ell\beta_i)\lt K. $$

These inequalities are equivalent to $u=ks+\ell\beta$, $|\beta_i|\lt s_i$, and $\sum_i s_i\lt1$, with $k=eK$. All numerator and value choices with nonzero token-value difference are included at those fixed denominators. Sampling denominator directions still does not exclude untested representations.

No original model definition, threshold convention, or architectural admissibility condition is changed by these experiments.

## Four-head local patterns

`search_local_pure_four.py` implements two finite selector-orbit patterns. The original pattern contains 404 distinct inputs. It was abandoned after the common-positive-functional Gram obstruction was proved: its cross matrix must have a positive inverse, while its within-right-block Gram matrix must have negative off-diagonal entries. Together with the positive pure mass columns, these conditions contradict the split Gram form. The main theorem notes contain the rigorous obstruction.

The replacement pattern uses middle-layer column-sum witnesses. Its 420 listed constraints contain 364 distinct inputs. The search script checks that repeated witnesses have consistent labels. Its analytic gradient was compared against finite differences; the largest observed absolute discrepancy was below $1.4\cdot10^{-10}$.

`exact_projected_relaxation.json` certifies a quadratic relaxation of the replacement pattern. It gives an integer matrix with sixteen rows and eight columns, a strictly positive first column, and the split form with four positive and four negative squares. Its quadratic satisfies all 91 distinct spatial witnesses, and its cross matrix has negative off-diagonal entries and positive column sums. Verification is entirely integer arithmetic:

```bash
python3 artifacts/rope/counterexample_search/verify_projected_relaxation.py \
  artifacts/rope/counterexample_search/exact_projected_relaxation.json
```

This relaxation is not a pure-head certificate. A common positive functional does not supply the full pure mass cone, the selector parameters, or the required unprojected score signs. `search_projected_embedding.py` and `adapt_projected_isometry.py` explore those additional constraints. `quadratic_sign_cone.py` tests candidate-specific sign implications by floating linear programming; any claimed implication would still require an exact dual certificate.

The two stored pure middle-matrix seeds were also tested. The zero-selector-linear seed has no spatial orbit on which all four unprojected score signs agree with its projected selector sign. Its full projected sign table permits competing quadratic sign polynomials with nonnegative tested off-diagonal cross entries. Thus those seeds do not already give a Boolean lower-bound certificate.

`search_adaptive_local_pattern.py` searches the actual full score for local witnesses at alternative centers, coordinate partitions, and middle-layer backgrounds. Its `--arbitrary-faces` option lets each required cross-coefficient sign use an independent alternating two-face. The resulting witnesses would apply to all competing vanilla representations. No such witness was found in the tested proposals. This is a search result, not an impossibility proof.

`search_pure_four_hard_cross.py` keeps every desired cross-coefficient and column-sum inequality as a hard linear constraint while optimizing score signs. It supports both block orientations and the original and replacement local patterns. The derivative of the cleared cross coefficients was checked by finite differences and against full-cube Fourier extraction. All outputs remain numerical proposals unless separately certified.

### An exact exclusion of a near-fit function

The best tested numerical fit to the block-complemented 404-point pattern missed four labels. Its full spatial orbit labels were precisely the two radius-one Hamming balls centered at the opposite block-constant vertices. That Boolean function already has an exact vanilla-three representation, independently of the numerical fit.

Write $L=\sum_{i=1}^{8}X_i-\sum_{j=1}^{8}Y_j$ and let $t$ be the selector. The function has sign $t(L^2-169)$. Set $R=1000+20(t+\sum_iX_i+\sum_jY_j)$ and use

$$ (D_1,D_2,D_3)=(R,R+L-13t,R+L+13t),\qquad (N_1,N_2,N_3)=(26t,-L-13t,L-13t). $$

Every denominator has strictly positive slopes and is positive throughout the cube. Direct expansion gives

$$ \sum_{h=1}^{3}N_h\prod_{j\neq h}D_j=26t(L^2-169t^2). $$

Since $t^2=1$, the three-head score has exactly the required signs. The integer verifier checks the identity and strict signs on all 131,072 inputs. The denominator lower bounds are 660, 673, and 647, and the minimum absolute cleared score is 650.

The threshold degree is exactly three. A hypothetical quadratic sign representation can be averaged to be odd in $t$ and even under simultaneous negation of all spatial spins. Its result is $t$ times a constant, which cannot represent both the positive spatial label at $L=16$ and the negative spatial label at $L=0$. Consequently the vanilla head count is exactly three, using the original scalar-to-architecture bridge. No pure head claim is needed for this exclusion.

```bash
python3 artifacts/rope/counterexample_search/verify_radial_selector.py
```

## Three-head cubic faces

`exact_tripartite_projection.json` gives three exact pure atoms on eleven bits, partitioned into six left, two middle, and three right coordinates. After clearing the positive denominators, arrange the coefficients of $X_iY_jZ_k$ into a six-by-six matrix, with rows indexed by $i$ and columns by the six pairs $(j,k)$. Every off-diagonal entry is negative and every column sum is positive. The verifier reconstructs this matrix from the pure atom parameters with rational arithmetic.

```bash
python3 artifacts/rope/counterexample_search/verify_tripartite_projection.py
```

This is only a coefficient relaxation. Exact-score restrictions do not imply the same restrictions on every polynomial with the same Boolean signs. The unresolved step is to force these coefficient signs using strict parity-face labels of the actual pure score.

`search_tripartite_faces.py` tests that step without imposing a global symmetry. Each off-diagonal coefficient may use its own ordinary three-dimensional parity face. Each column sum may use a parity face where all six left coordinates are tied to one bit, while the chosen middle and right coordinates are the other two bits. It tests every six-two-three partition and every matching of rows to column pairs. Any discovered witness still needs exact parameter and sign verification before it can support the all-vanilla lower bound.
