import HeadComplexity.Atoms.FracAtomDummy
import HeadComplexity.Results.SymmetricFaceLowerBound

set_option linter.style.header false

/-!
# Dummy-variable and junta invariance

Adjoining coordinates on which a Boolean function does not depend preserves
head complexity exactly.  The active coordinates may occupy arbitrary ambient
positions, specified by an injection.  The upper inequality is the small
positive-weight fractional-atom lift; the lower inequality is coordinate-face
restriction monotonicity.
-/

namespace HeadComplexity

variable {m n H : ℕ}

/-- Dummy-coordinate extension is an equivalence at every fixed atom count. -/
theorem fracComputable_dummyVariablesAlong_iff (e : Fin m ↪ Fin n)
    (f : (Fin m → Bool) → Bool) :
    fracComputable n H (fun y ↦ f (pullBitsAlong e y)) ↔
      fracComputable m H f := by
  constructor
  · intro hf
    simpa using hf.restrict (embeddingFace e)
  · exact fracComputable.liftDummyAlong e

/-- Dummy-coordinate extension is an equivalence at every fixed head count. -/
theorem computableWithHeadsN_dummyVariablesAlong_iff (e : Fin m ↪ Fin n)
    (f : (Fin m → Bool) → Bool) :
    computableWithHeadsN n H (fun y ↦ f (pullBitsAlong e y)) ↔
      computableWithHeadsN m H f := by
  constructor
  · intro hf
    simpa using hf.restrict (embeddingFace e)
  · exact computableWithHeadsN.liftDummyAlong e

/-- **Dummy-variable equality.** Pulling a Boolean function back along any
coordinate injection leaves its minimum head count unchanged. -/
theorem HStar_dummyVariablesAlong (e : Fin m ↪ Fin n)
    (f : (Fin m → Bool) → Bool) :
    HStar n (fun y ↦ f (pullBitsAlong e y)) = HStar m f := by
  apply Nat.le_antisymm
  · exact HStar_le_of_computableWithHeadsN
      ((HStar_computable f).liftDummyAlong e)
  · simpa using HStar_restrict_le (embeddingFace e)
      (fun y ↦ f (pullBitsAlong e y))

/-- The block form of dummy-variable equality from theorem 28: the first `m`
coordinates are active and the final `r` coordinates are dummy. -/
theorem HStar_dummyVariables (r : ℕ) (f : (Fin m → Bool) → Bool) :
    HStar (m + r) (fun y ↦ f (fun i ↦ y (Fin.castAdd r i))) = HStar m f := by
  have hfun :
      (fun y ↦ f (pullBitsAlong (Fin.castAddEmb r) y)) =
        (fun y ↦ f (fun i ↦ y (Fin.castAdd r i))) := by
    funext y
    congr 1
  rw [← hfun]
  exact HStar_dummyVariablesAlong (Fin.castAddEmb r) f

/-- An ambient function is represented as a junta on the coordinates selected
by `e` when it factors through `pullBitsAlong e` with the displayed core. -/
def IsJuntaVia (e : Fin m ↪ Fin n) (core : (Fin m → Bool) → Bool)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ y, f y = core (pullBitsAlong e y)

/-- **Junta transport.** The head complexity of a junta is exactly that of any
displayed core through which it factors. -/
theorem IsJuntaVia.HStar_eq {e : Fin m ↪ Fin n}
    {core : (Fin m → Bool) → Bool} {f : (Fin n → Bool) → Bool}
    (hf : IsJuntaVia e core f) :
    HStar n f = HStar m core := by
  have hfun : f = fun y ↦ core (pullBitsAlong e y) := funext hf
  rw [hfun]
  exact HStar_dummyVariablesAlong e core

/-- A direct corollary convenient when the factorization is supplied as a
function equality rather than through `IsJuntaVia`. -/
theorem HStar_juntaTransport (e : Fin m ↪ Fin n)
    (core : (Fin m → Bool) → Bool) (f : (Fin n → Bool) → Bool)
    (hf : f = fun y ↦ core (pullBitsAlong e y)) :
    HStar n f = HStar m core := by
  rw [hf]
  exact HStar_dummyVariablesAlong e core

end HeadComplexity
