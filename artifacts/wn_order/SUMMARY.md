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
`artifacts/wn_order/wn_order_section.tex`, `notes/wn_order_notes.md`, `experiments/wn_search/`.

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

## Audit of the paper
Theorems 3.5, 3.7, 3.8 and the spanning lemmas were re-derived and found correct (details in the notes, Section 13).

## Computational evidence (certified successes only)
Random 7-bit functions: 8 heads; random 8-bit: 12 to 14 heads (fixed-list threshold 16); exact tropical optima for random
targets scale like $0.55N/n$ for $n\leq7$; interpolation multiplicity at $n=5$: 19 and 27 real solutions for $H=2,3$.

## What remains open
Whether the non-perturbative regime (many heads of comparable magnitude at a typical input) is Warren-tight; equivalently
whether the real admissible interpolation multiplicity at $2nH$ cube points is $2^{\Theta(n^2H)}$.
