# Read-only research refresh at 18:52 UTC

## Ref update

On November 24, 2026, the remote heads of `VerifiedMechanisms/xorformer-runs`, `VerifiedMechanisms/autoresearch-runs`, and `VerifiedMechanisms/xorformer` were fetched into their corresponding remote-ref namespaces. The first two repositories supplied no changed refs. The third supplied these new completed-run branches:

- `origin/ar/76e0187067db`, `bdca97f8ac10d02ba20ddb6a39c63405bb4bfafa`, timestamp 18:28:20 UTC.

- `origin/ar/737fec7c7b5d`, `b4c663512134ed6c835c0bc9e353015053991b42`, timestamp 18:34:56 UTC.

- `origin/ar/7be651882de5`, `55bf9be423ecbe419daa2b5cf10e833f264f1123`, timestamp 18:35:58 UTC.

Their new commits concern exact scalar simulation by pure RoPE atoms and small-head RoPE comparisons. They supply no density-sensitive unrestricted sign count or relative-margin repair. No code from these branches was imported or represented as independently rebuilt.

## Relevant earlier written arguments rechecked

The following earlier artifacts were read directly at their recorded commits. These are written proofs, not newly verified Lean declarations.

- Commit `0f771323a0ec4890c2ec3b9ab071a2648fe9db10`, `artifacts/head-compression/reciprocal-segre-degeneration.tex`, uses the Catalisano, Geramita, and Gimigliano Segre secant theorem to prove an exact-value upper bound of twice the ceiling of the Boolean table size divided by the dimension plus one. The local invertible transform is a rescaled Boolean Möbius transform. It preserves differential rank, but does not preserve Boolean sign chambers. Its positive-parameter and finite-cube admissibility checks do not yield a sign-preserving compiler or a bound for the degree of the complete reciprocal secant variety.

- Commit `7633c01d5a1d6a48dbf5c6862850a2cf9f0e8a16`, `artifacts/head-compression/ambient-relative-rank-audit.tex`, audits Basu and Parida's real relative-rank theorem. The product-family bound retains the head count inside a logarithm. Its explicit smooth lift satisfies the stated real-dimension hypothesis, but the displayed degree estimate gives a weaker lower bound than Warren. Even a hypothetical constant degree leaves the original exponent-two scale. This does not prove a density-sensitive degree estimate for Boolean reciprocal secants.

- Commit `63678d18b40e2f08489dd7dfa2ca50a20e27d778`, `artifacts/head-compression/histogram-confluent-density-audit.tex`, proves a sign-change obstruction for fixed finite collections of small-scale tangent sheets after an injective moment-cutoff hypothesis. The proof has no scale bound uniform in head count or pole profiles. It cannot be applied to an arbitrary finite-scale model without proving that additional quantitative hypothesis.

- Commit `a64e6e4ff5293c73e0f41ed037e819a805f3756b`, `artifacts/head-compression/continuation-integer-fiber-jets.tex`, constructs zero representations and independent polynomial readouts on weighted integer fibers. Its resource audit explicitly bounds the strict leading-readout capacity and leaves higher vanishing orders unresolved. It supplies no universal margin repair.

The current starting revision already contains the arbitrary-direction product-compiler obstruction in `artifacts/power-saving-20261124/adaptive_product_compiler_logarithmic_obstruction.md`. Its logarithmic overhead lower bound occurs at polynomial width in the input dimension. It does not rule out logarithmic or other subpolynomial overhead at the exponential widths relevant to the requested benchmark. The stronger exponential-node obstruction in `signed_exponential_quadrature_obstruction.md` keeps the original denominator directions and numerator factors; allowing new directions makes that specific target easy.

## Result of the refresh

No new unconditional bridge from the margin count to unrestricted worst-case head complexity was found. No remote theorem was imported in this refresh. The precise open requirements remain a quantitatively controlled full-model reconstruction, a suitable freely chosen product compiler, a universal low-margin truth-table count, or an independent density-sensitive capacity theorem.
