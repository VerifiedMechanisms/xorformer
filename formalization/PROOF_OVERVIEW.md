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

## The model (`Foundation/Vec.lean`, `Model/Head.lean`, `Model/SharedEmbedding.lean`)

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

`SharedHeadFamily n d H` is the literal model from `model.md`: it has one token
embedding and one positional embedding, with only `WQ`, `WK`, and `WV` indexed
by the head. `shareHeadEmbeddings` converts any head-local width-`d` family to a
shared-embedding width-`H * d` family by concatenating the local parameter
blocks. `computableWithHeadsN_iff_computableWithSharedHeadsN` proves that this
widening preserves head-count expressivity in both directions. In particular,
`SharedHStar_eq_HStar` identifies their least head counts, and
`SharedHStar_eq_Lfrac` states the later Theorem 10 directly for the literal
shared-embedding model.

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
* **Theorem 30** (`Results/ThresholdDegreeSpan.lean`): a fixed family of
  positive affine denominators whose reduced cleared features span every
  squarefree polynomial of degree at most $d$ computes every Boolean function of
  threshold degree at most $d$. Linear independence of the low-degree
  monomials also gives the necessary dimension inequality
  $D(n,d)\leq1+nH$.
* **Theorem 25** (`Results/CompactThresholdCertificate.lean`): the explicit
  modular denominator formula, its blockwise feature selection, the head and
  residual counts, and the ten recorded nonzero residues are defined in Lean.
  The determinant bridge derives the universal compact bound from either the
  exact recorded-residue equality or a modular right inverse. The ten large
  numerical matrix witnesses are not present in the repository and remain the
  only dimension-specific premises.
* **Theorem 26** (`Results/CountingLowerBound.lean`): a relaxed $H$-fraction
  family has exactly $1+2H(n+1)$ parameters. At every cube point, its cleared
  score is a universal parameter polynomial of degree at most $H+1$.
  Strictification and positive denominator clearing inject all $H$-head truth
  tables into the corresponding strict sign patterns. From an explicit
  proposition expressing Warren's multivariate sign-pattern inequality, Lean
  derives the exact count, the bound $2^{35n^2H}$, density decay, existence of
  hard functions, and the finite worst-case lower bound. The Warren inequality
  itself remains the single named external analytic premise, not an axiom.
* **Theorem 27** (`Results/TopThresholdDegree.lean`): the Boolean truth-table
  sign vector is projected away from the top parity character. When the table
  is neither parity nor its complement, the remaining vector keeps the strict
  target sign and is interpolated by an explicit cube polynomial of degree at
  most $n-1$. Consequently, ambient threshold degree $n$ occurs exactly for
  parity and its output complement when $n\geq1$.
* **Theorem 62** (`Results/AffineSlab.lean`): two explicit affine-ratio atoms
  give the full zero, one, or two affine-slab classification.
* **Theorems 49 and 63** (`Results/EqualityExact.lean`,
  `Results/AffineStatisticSignChanges.lean`): equality is an affine level set
  with an XOR checkerboard restriction, giving exact threshold degree and head
  complexity two. More generally, ordered sign changes along an arbitrary
  affine statistic give exact zero- and one-change cases, the complete
  two-change LTF split, and a support-sensitive bound thereafter.
* **Theorem 53** (`Results/LocalPatternCountProfile.lean`): a one-bit identity
  or complement slice restricts a local two-bit count profile to the symmetric
  sign-change theorem. In the other direction, the univariate sign polynomial
  in the count is expanded through the canonical multilinear products of the
  local predicate. The union of their nonlinear supports, plus one shared
  affine charge when needed, gives the exact expansion-cost upper bound.
* **Theorem 109** (`Results/LowAffineCylinderCost.lean`): when affine-cylinder
  cost is at most two, the universal constant, nonconstant LTF, and remaining
  cases have exact head complexity zero, one, and two, respectively.
* **Theorem 110** (`Results/AffineCylinderThreshold.lean`): finite cylinder and
  affine-cylinder certificates are attained and compile into the complete
  threshold-degree, head-complexity, and certificate-cost sandwich.
* **Theorem 114** (`Results/SplitAffineCylinder.lean`,
  `Results/AffineCylinderCofactorRecursion.lean`,
  `Results/SplitAffineCylinderRefinement.lean`): positive and negative split
  data compile cofactor scores into an ambient affine-cylinder certificate.
  Cost-preserving coordinate permutations turn the fixed first-coordinate
  construction into invariants minimized over every coordinate. Positive
  squarefree monomials then realize the split affine-free pair cost exactly,
  proving the full global refinement chain.
* **Theorem 120** (`Results/AffineCylinderCofactorRecursion.lean`): attained
  optimal cofactor certificates are normalized by deleting vacuous cylinders,
  then interpolated in either fresh-literal orientation. The two estimates are
  minimized to obtain the cofactor recurrence, both at a fixed split and for
  the coordinate-minimized invariant at every selected coordinate.
* **Theorem 124** (`Results/FreshXorTargetCost.lean`): a normalized
  affine-cylinder score is interpolated with its negation in both fresh-bit
  orientations. Minimizing the exact resulting cost gives `xorTargetCost`.
  Fresh-bit threshold-degree amplification supplies the lower endpoint,
  output complement supplies XNOR, and equality of the endpoints gives the
  exactness statements.
* **Theorem 73** (`Results/DnfCnfHybrid.lean`): exact DNF and CNF certificates
  on their used-variable cubes simultaneously give the sparse-volume,
  oriented-literal, universal-junta, and width-degree bounds. Junta transport
  preserves head complexity in the ambient cube, and CNF follows from the DNF
  of falsifying cylinders together with output-complement invariance.
* **Theorem 183** (`Results/FourBitCertificateChecker.lean`,
  `Results/SmallDimensionExactCertificate.lean`): exact integral cleared scores
  and nonnegative moment circuits feed a total Boolean checker for all four-bit
  complement representatives. `smallDimension_exact_of_check_eq_true` proves
  end-to-end soundness through four variables. The large archived data value and
  its successful kernel check are not bundled.
* **Theorem 186** (`Results/FiveBitDegreeFourCertificate.lean`): integral
  cleared-feature rows have a Boolean checker and compile through the existing
  oriented-denominator certificate. The rank-and-margin argument is proved as
  an exact finite gluing lemma: a base row vanishing on a zero set dominates
  off that set after positive integral scaling, while an arbitrary perturbation
  realizes the requested signs on it. The formal certificate boundary records
  the sixty shattering families, all five named residual orbits, and the full
  coordinate-permutation, global-input-flip, and output-complement quotient.
  The large archive rows and their coverage proof are not embedded.
* **Theorem 187** (`Results/FiveBitDegreeTwoCertificate.lean`): the
  triangle-free two-coloring reduction on $K_5$, exact nonnegative integral
  Gordan-circuit soundness, and the weak wrong-edge obstruction are
  machine-checked. Coordinate permutations, simultaneous input complement,
  and output complement preserve the archive conclusion. A finite family of
  integral two-head representatives therefore proves exact degree-two head
  complexity once the absent cocircuit and tangent-cover archive supplies the
  stated symmetry-coverage premise. No archive enumeration runs in Lean.
* **Theorems 193 and 194** (`Polynomial/PositiveSecantBlowup.lean`,
  `Polynomial/SignedSecantBlowup.lean`,
  `Results/SecantObstruction.lean`): exact division at the secant diagonal,
  finite continuity opening, atom-to-tangent normalization, and head-padding
  turn both positive and signed blow-up infeasibility into strict head lower
  bounds. Head
  permutation symmetry reduces the search to $H+1$ orientation counts and
  $4(n+1)+2$ normalization chart types per count branch.
* **Theorem 195** (`Atoms/AtomicMargin.lean`, `Atoms/AtomicSampling.lean`,
  `Results/AtomicMarginSparsification.lean`, `Results/AtomicCondition.lean`): independent finite sampling,
  sub-Gaussian Hoeffding bounds, and a finite union bound sparsify an
  output-normalized finite atomic-margin certificate. The exact sample count has
  constant 32 under a ceiling, and the real-valued Results theorem has absolute
  constant 33. The finite explicit certificate wrapper is always inhabited for
  nonconstant Boolean functions, and its literal infimum
  `atomicConditionNumber` satisfies the same quadratic bound.
* **Theorems 82, 138, 141, and 144**
  (`Results/OneBitGateThresholdDegree.lean`,
  `Results/PositiveOrderOneBitGate.lean`): fresh-coordinate polynomial
  operations give the exact threshold-degree trichotomy, while shared-shift
  partial fractions give the universal positive-order gate sandwich and its
  degree-tight exact table.
* **Theorem 83** (`Results/ParityBlockThresholdDegree.lean`): iteration of the
  fresh-bit XOR identity raises threshold degree by exactly the parity-block
  size. A reusable sparse-monomial certificate transforms $H$ terms into
  $2H+1$ terms at each fresh XOR, giving the matching
  $2^k(\mathrm{ptfsp}(T)+1)-1$ fallback upper bound.
* **Theorems 85, 87, and 93** (`Results/CalibratedThresholdVote.lean`,
  `Results/OneBitNonXorGate.lean`, `Results/RawCalibratedVote.lean`): uniform
  atom approximations compose through a strict weighted vote when their total
  weighted error stays below its margin. Raw calibration cost is attained on
  the finite cube, is bounded by exact affine-free multilinear support, and
  adds only over active vote features. Independently, every one-fresh-bit gate
  other than XOR and XNOR costs at most one additional head.
* **Theorems 170 and 173** (`Results/PositiveMultigrid.lean`): finite scale
  separation turns any lexicographically ordered product of positive block
  statistics into one positive projection with exactly the same label
  alternations. This proves the per-certificate upper and fiber lower bounds,
  then minimizes over all positive statistics and block orders to obtain the
  attained multigrid cost, its $H^{\ast}$ and $C_{+}$ bounds, endpoint
  exactness, and complement, block-relabeling, and coordinate-permutation
  invariance.
* **Theorem 179** (`Results/TwoBlockAffineGridStrip.lean`): a two-block affine
  grid strip is an affine slab on the cube and therefore has the exact zero-,
  one-, or two-head classification. An independent bivariate polynomial
  threshold degree is developed on the finite grid. Strictification followed
  by averaging over within-block permutations proves that grid and cube LTF
  cases coincide, yielding unconditional equality of the two complexities for
  nonempty blocks.
* **Theorem 190** (`Results/SliceRankTwo.lean`): homogenizing the affine
  numerator and denominator forms makes the cleared score homogeneous of
  degree $H$. Isolating one head gives two degree $(1,H-1)$ slices, with an
  actual positive denominator as the second linear generator. The certificate
  includes real and scalar-extension common-zero containment, strict Boolean
  sign preservation, and the resulting contrapositive lower bound on $H^{\ast}$.
* **Theorem 192** (`Results/MultiwaySignTensorRank.lean`): block-local affine
  splitting expands a cleared tangent score into one pure tensor for every
  active assignment-block pair. Their exact count is
  $k(k^H-(k-1)^H)$. A separate fiber expansion proves the ambient
  $2^{n-|I_j|}$ ceiling, and the checked arithmetic comparison shows that on
  $n\leq2H+1$ coordinates no nonempty multiway partition can exceed the
  tangent count.

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
