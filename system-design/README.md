# automlr

A from-scratch attack on the head-complexity problem: what is the minimum number of attention heads $H^{\ast}(f)$ that a single-layer, attention-only transformer with a linear readout needs to compute a Boolean function $f$?

This attack deliberately started with only the problem definition. No prior results, proofs, or surveys were carried over.

The answer is exact: $H^\ast(f)$ is the positive linear-fractional threshold
rank of $f$, equivalently the least shared-positive-linear-factor width of a
strict polynomial threshold for $f$.  The proof and consequences are in
`answer.md`.

Concretely, for nonconstant $f$ and $\chi_f=2f-1$, it is the least $H$
for which

$$
 \chi_f(x)\sum_{h=1}^H\frac{N_h(x)}{D_h(x)}\gt 0
 \quad\text{on }\lbrace 0,1\rbrace^n,
$$

where the $N_h$'s are affine and each $D_h\gt 0$ has all its nonconstant
coefficients strictly positive or all strictly negative.  This is a genuine
normal-form theorem in both directions: scalar heads and one shared
$(n+2)$-dimensional embedding already realize every such certificate.

- [`problem_statement.md`](problem_statement.md): the problem, the central quantity $H^{\ast}(f)$, and the core questions.
- [`model.md`](model.md): the precise architecture (embeddings, attention heads, residual stream, readout, masking convention, deliberate simplifications).
- [`answer.md`](answer.md): the exact linear-fractional characterization, proofs, classical comparisons, natural families, and worst-case bounds.
- [`approach_registry.md`](approach_registry.md): the proof-search families, completed routes, computational checks, and explicitly blocked conjectural improvements.
- [`formalization/`](formalization/): Lean 4 formalization of the scalar normal-form theorem, its exact converse, denominator clearing, and the one-head sign criterion.
- [`selftests/run`](selftests/run): fast exact-arithmetic sanity checks for the main constructions and finite certificates.
- [`selftests/four_bit_exhaustive`](selftests/four_bit_exhaustive): the slower exact covector certificate for the complete four-bit theorem.
- [`selftests/interpolation_modular_large`](selftests/interpolation_modular_large): the larger exact modular-rank certificates for sharp universal interpolation widths.
- [`selftests/address_three_bit_four_heads`](selftests/address_three_bit_four_heads): the exact rational four-head construction for three-bit indexing.
