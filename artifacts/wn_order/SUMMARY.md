# Run summary: Worst-Case Head Complexity at Order 2^n/n^2 (20 November 2026)

## Question
Prove $W(n)=\max_fH^{\ast}(f)\leq c\cdot2^n/n^2$ for the one-layer softmax attention model of version-5.tex, closing the gap
$(\tfrac12+o(1))2^n/n^2\leq W(n)\leq(1+o(1))2^n/n$.

## Outcome (honest status)
Not proved and not refuted. No complete proof of either $W(n)=O(2^n/n^2)$ or $W(n)=\omega(2^n/n^2)$ was found; the
question is open in the literature as of the newest papers (Rajaraman, Sundaram, Tesfaye, Sept. 2026: universal bound
$2^n$, counting bound $\Omega(2^n/n^2)$; the audited paper is ahead with $(1+o(1))2^n/n$). What this run delivers is a
rigorous map of the obstruction, new rigidity theorems, a transfer theorem for a combinatorial sub-model, an audit of the
paper's proofs, a literature survey, and certified computational evidence. Everything is in the repository
(branch of this run): `theorems/02_complexity_measure_upper_bounds/199_worst_case_order_rigidity.md`,
`artifacts/wn_order/wn_order_section.tex`, `artifacts/wn_order/AUDIT.md`, `notes/wn_order_notes.md`, `experiments/wn_search/`,
`formalization/HeadComplexity/Tropical/SwapExclusion.lean`.

## Rigorous results (new)
1. Normalization and information location: fixed denominator lists realize at most $2\sum_{i\leq nH}\binom{N-1}i$ functions
   (Cover), so with $H=cN/n^2$ the denominators must depend on the target and carry $N(1-o(1))$ bits.
2. Precision requirement: parameters of $p$ bits give at most $2^{(2nH+1)(2p+2)}$ functions, so an $O(N/n^2)$ construction needs
   $\Omega(n)$-bit parameters; polynomial precision forces $\Omega(N/(n\log n))$ heads.
3. Common-direction collapse: if all denominators share one direction, the sign patterns lie in a fixed linear space of
   dimension $\leq(n+1)H+1$; such lists need $H\geq(\tfrac12-o(1))N/(n+1)$ for almost all functions. The degree factor of
   Warren's bound is illusory unless the denominator directions spread (Chow-degree explanation: products of affine forms in
   one variable form a degree-one variety, in $n\geq2$ variables a variety of degree $(nH)!/(H!(n!)^H)$).
4. Tropical transfer theorem: decision lists over the rules $\lbrace x_{\pi_h(k)}=1,x_{\pi_h(j)}=0\ (j\lt k)\rbrace$ with
   priorities and signs are realized by $H$ heads with exponentially spread parameters; this sub-model is counting-compatible
   with $N/n^2$ but exponentially weaker on parity (Lemmas A, B in the notes: swap exclusion, edge explanation; both
   machine-checked in core Lean 4: `Tropical.Model.swap_exclusion`, `Tropical.Model.edge_explanation` in
   `formalization/HeadComplexity/Tropical/SwapExclusion.lean`, axiom-clean).
5. Rate caps: dominant cells give at most $2nk\log_2(e|R|/(2nk))$ controllable points per $k$ heads; regular-zero exact
   representations are capped at $(\tfrac12+o(1))N/n$ by the parameter count; boosting with atoms as weak learners stops at $N/n$.
6. Parity in the tropical sub-model needs at least $(1-o(1))\,n2^{n/2}/32$ heads (fibers are swap-free independent sets, bounded
   by a shadow argument; an edge count caps the average finalizer dimension; one rule per dimension per head), an exponential
   separation from $H^{\ast}(\mathrm{PARITY}_n)=n$; the two structural lemmas it rests on are machine-checked in core Lean 4.

## Audit of the paper
Theorems 3.5, 3.7, 3.8 and the spanning lemmas were re-derived and found correct (details in the notes, Section 13).

## Computational evidence (certified successes only)
Random functions: 8 heads at 7 bits, 11 to 12 at 8 bits (fixed-list threshold 16), 22 to 24 at 9 bits, 38 to 40 at 10 bits,
with denominator slopes clipped to $[0.1,10]$ (so the gain over fixed lists is not suppression). Exact tropical optima
(SAT) for random targets: means $3.0, 4.1, 6.0, 10.6$ at $n=4..7$ and brackets $[12,17],[12,19],[12,22],[12,19]$ at $n=8$:
$Tn/N\approx0.74,0.66,0.56,0.58$ and $Tn^2/N\approx3.0,3.3,3.4,4.0$, between the two scalings. Interpolation multiplicity:
$19,27,26,12,12$ real solutions for $(n,H)=(5,2),(5,3),(6,2),(7,2),(6,3)$ against Chow degrees up to $2.9\cdot10^6$.
Weight-two miniature: random graphs on $16,32,64$ vertices with $3,4,8$ heads (about half the Cover threshold).

## What remains open
Whether the non-perturbative regime (many heads of comparable magnitude at a typical input) is Warren-tight; equivalently
whether the real admissible interpolation multiplicity at $2nH$ cube points is $2^{\Theta(n^2H)}$.
