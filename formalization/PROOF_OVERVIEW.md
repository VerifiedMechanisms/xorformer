# Proof architecture

How the core formalized results and selected later theorem-stack results fit
together.
See `README.md` for the theorem→theorem→file map,
`HeadComplexity/Results/All.lean` for a verified table of contents,
and `BUILDING.md` to reproduce the build.

The public theorem surface lives under `HeadComplexity.Results`; lower-level
`Model`, `Polynomial`, and `Atoms` modules hold the technical proofs and
constructions imported by those result facades. There is also an examples umbrella
for an explicit list of direct applications.

## The model (`Foundation/Vec.lean`, `Model/Head.lean`)

A single softmax attention head is `Head n d`: token embeddings `Fin 3 → Vec d`
(bit-0 / bit-1 / query), positional embeddings `Option (Fin n) → Vec d`, and linear
maps `WQ, WK, WV`. On input `bits`, position `p` has embedding
`x p = tokenEmbed (seqTok bits p) + posEmbed p`; the softmax weight is
`σ p = exp ⟪WK (x p), WQ (x none)⟫`; the head's update is the normalized value
average `attnUpdate = (∑ p σ p)⁻¹ • ∑ p σ p • WV (x p)`. A function is
`computableWithHeadsN n H f` when some `H`-head family's summed update, read by a
linear `⟪w, ·⟫ > τ`, equals `f`. `HStar n f` (= `H*`) is the least such `H`
(`Nat.find`, `0` if none, but every `f` is computable, so this default never
bites; see Theorem 9 universal bound).

## Two spines

Everything is built from a **lower-bound spine** (you need many heads) and an
**upper-bound spine** (you can build the heads).

### Lower bounds through threshold degree and restriction

```
computableWithHeadsN n H f
  └─ L6  degree_le_of_computableWithHeadsN       (Results/ThresholdDegree.lean)
        clears each head's softmax ratio to a degree-≤1 affine polynomial;
        H heads ⟹ a degree-≤H real polynomial sign-representing f  (ThresholdDegLE f H)
  └─ for symmetric f:  ThresholdDegLE f H → signChanges ≤ H        (Polynomial/UnivariateReduction.lean)
        strictify → symmetrize over Equiv.Perm → reduce to a univariate
        polynomial in the Hamming weight → count real roots (IVT)
```

This gives the `≥` halves: Theorem 3 (checkerboard, via antipode identities L1/L2 +
segment non-separability), Theorem 5 lower bounds, Theorem 7 (`deg±(parity) = n`,
reusing the symmetric chain), and the `≥` half of Theorem 12.

The coordinate-restriction API formalizes the restriction monotonicity from
theorem 28. `FracAtom.restrict` keeps each atom inside the same abstraction after
coordinates are fixed, so `HStar_restrict_le` transfers the theorem 12 symmetric
sign-change value on a face into a lower bound for an arbitrary ambient function.

### Upper bounds through explicit softmax heads

Each construction is one `Head` whose readout is a prescribed rational/affine
function, proved by clearing the softmax denominator. They form a family, sharing
a value coordinate so one readout sums them.

| gadget | readout | used by |
|--------|---------|---------|
| `atomHead` (`Atoms/HammingAtom.lean`) | `b/(\|x\|+a)` | L12 upper bound |
| `weightedAtomHead` (`Atoms/WeightedAtom.lean`) | `b/(∑λᵢxᵢ+a)` | L9, theorem 69 |
| `affineHead` (`Atoms/AffineHead.lean`) | affine `L(x)`, const absorbed in `τ` | L11 |
| `atomHead'` (`Atoms/FracAtomHead.lean`) | a full linear-fractional atom | L10 |

The L12 upper bound (`Atoms/SignPolynomial.lean` → `Atoms/PartialFraction.lean` →
`Atoms/HammingAtom.lean` → `Results/SymmetricComplexity.lean`) builds a degree-`signChanges` sign polynomial,
splits it by partial fractions into `b_h/(k+a_h)` atoms, and realizes one per head.
L9 generalizes `|x|` to a weighted sum (Lagrange interpolation over the image
nodes). L10's two directions show this is tight: *every* head **is** an atom
(`Atoms/HeadToFracAtom.lean`, reading the atom parameters off the head's maps) and *every*
atom is realized by a head (`Atoms/FracAtomHead.lean`), so `H* = L_frac`.

The formalization of theorem 69 factors this construction through two reusable
interfaces. The polynomial-side
`UnivariateThresholdDegLE t f K` records a degree-`K` sign polynomial in an arbitrary
real statistic. The atom-side `PositiveWeightedSignDegLE f K` chooses a positive
weighted statistic and invokes `exists_partialFraction_sign_atoms` plus
`weightedAtomFamily_readout` to realize the certificate with exactly `K` heads. Its
minimum, `positiveWeightedSignDeg`, is finite by binary-weight interpolation and is
the polynomial-certificate presentation of the existing positive-projection
invariant $C_{+}$. `PositiveProjection` separately records the strictly ordered
finite statistic image and its label alternations. The formalization proves
`positiveProjectionSignChanges_eq_positiveWeightedSignDeg`, so the two
presentations are interchangeable inside Lean.

## Capstones

* **L12** (`Results/SymmetricComplexity.lean`): `HStar_symmetricFn`, with `≥` from the lower-bound spine,
  `≤` from the upper-bound spine, joined by `le_antisymm` over `Nat.find`.
* **L4, L5, L8** (`Results/ExactFamilies.lean`): corollaries of L12. The head complexity
  of a standard family is the number of sign changes of its profile.
* **L10** (`Results/FractionalNormalForm.lean`), **L11** (`Results/LowComplexity.lean`): the exact normal form and
  the level-0/1 classification, both using that every `f` is computable.

## Later theorem-stack interfaces

* **Theorems 12 and 28** (`Results/SymmetricFaceLowerBound.lean`):
  `HStar_lower_bound_of_symmetric_face` combines atom restriction with the theorem
  12 sign-change value on a face.
* **Theorem 69** (`Results/PositiveWeightedSignDegree.lean`,
  `Results/PositiveProjection.lean`, `Results/WeightedFaceExact.lean`): the
  ordered-image and polynomial presentations are equal. Both give the
  threshold-degree and head-complexity sandwich, endpoint exactness, the
  low-alternation classification, and fixed-certificate instances.
* **Theorem 28** (`Results/DummyVariables.lean`,
  `Results/StructuralInvariances.lean`, `Results/PartitionSignRank.lean`):
  restriction, dummy-variable, junta, complement, permutation, and global bit
  flip invariance, followed by the tangent and degree partition sign-rank caps
  and their logarithmic inversion.
* **Theorems 45 and 48** (`Results/FourierSupport.lean`,
  `Results/AffineFreeSparsity.lean`): uniform atom approximation compiles sparse
  Walsh scores and squarefree polynomial-threshold scores while retaining their
  natural support costs.
* **Theorem 62** (`Results/AffineSlab.lean`): two explicit affine-ratio atoms
  give the full zero, one, or two affine-slab classification.
* **Theorem 110** (`Results/AffineCylinderThreshold.lean`): finite cylinder and
  affine-cylinder certificates are attained and compile into the complete
  threshold-degree, head-complexity, and certificate-cost sandwich.
* **Theorem 183** (`Results/FourBitCertificateChecker.lean`,
  `Results/SmallDimensionExactCertificate.lean`): exact integral cleared scores
  and nonnegative moment circuits feed a total Boolean checker for all four-bit
  complement representatives. `smallDimension_exact_of_check_eq_true` proves
  end-to-end soundness through four variables. The large archived data value and
  its successful kernel check are not bundled.
* **Theorems 193 and 194** (`Polynomial/PositiveSecantBlowup.lean`,
  `Polynomial/SignedSecantBlowup.lean`,
  `Results/SecantObstruction.lean`): exact division at the secant diagonal,
  finite continuity opening, atom-to-tangent normalization, and head-padding
  turn signed-blow-up infeasibility into a strict head lower bound. Head
  permutation symmetry reduces the search to $H+1$ orientation counts and
  $4(n+1)+2$ normalization chart types per count branch.
* **Theorem 195** (`Atoms/AtomicMargin.lean`, `Atoms/AtomicSampling.lean`,
  `Results/AtomicMarginSparsification.lean`): independent finite sampling,
  sub-Gaussian Hoeffding bounds, and a finite union bound sparsify an
  output-normalized finite atomic-margin certificate. The exact sample count has
  constant 32 under a ceiling, and the real-valued Results theorem has absolute
  constant 33. `AtomicConditionLE` records arbitrary certified ratio bounds
  without introducing a literal infimum wrapper.
* **Theorems 82, 138, 141, and 144**
  (`Results/OneBitGateThresholdDegree.lean`,
  `Results/PositiveOrderOneBitGate.lean`): fresh-coordinate polynomial
  operations give the exact threshold-degree trichotomy, while shared-shift
  partial fractions give the universal positive-order gate sandwich and its
  degree-tight exact table.

## Strict separation

**L13** (`Results/StrictSeparation.lean`) defines an explicit ten-bit function
with threshold degree two and head complexity at least three. Its lower-bound
chain is:

```text
two heads
  -> two linear-fractional atoms
  -> clear two positive denominators
  -> a sum of two products of affine forms
  -> mixed antipodal matrix has rank at most four
```

Five target slices force the same matrix to be strictly column diagonally
dominant, hence to have rank five. This contradiction rules out two heads. An
XOR restriction proves the matching threshold-degree lower bound, while the
displayed quadratic supplies the degree-two upper bound.

The same `le_antisymm`-over-two-`Nat.find` shape recurs in L10 and L12: a per-`H`
equivalence between two complexity predicates forces their minima to agree.
