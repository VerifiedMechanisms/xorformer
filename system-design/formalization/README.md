# Lean formalization

The project uses Lean 4.31.0 and mathlib 4.31.0. Build it with:

```sh
cd formalization
lake build
```

`Automlr/NormalForm.lean` kernel-checks the algebraic core of the answer:

- expansion of a scalar softmax head into affine numerator and denominator;
- positivity and coherent orientation of every nondegenerate head denominator;
- an explicit converse realizing every attention-positive affine fraction by
  a scalar head with positive masses and zero bit-dependent value increment;
- equivalence of strict fixed-width scalar-head and positive
  linear-fractional certificates;
- the shared-factor denominator-clearing identity and preservation of sign;
- the exact equivalence between width-one fractional certificates and strict
  linear threshold representations.

The current trusted boundary is intentionally explicit. This project does not
yet formalize the matrix-level shared-embedding construction, the finite-margin
perturbation which removes heads with attention ratio exactly one, polynomial
threshold degree, the symmetric-function theorem, the asymptotic counting
bounds, or the larger finite certificates. Those results remain proved or
certified in `answer.md` and `selftests/`; they are not claimed to be checked by
Lean.
