import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Approximation lemma for the fixed raw alphabet simulation

Finite sums from a five-element alphabet are dense. Consequently any finite
strict-sign certificate depending continuously on its effective coefficients
has another certificate whose coefficients are such sums. The conversion of
these sums into extra attention coordinates is proved in the accompanying
TeX note, not in this module. An alphabet containing `sqrt 2` is not a finite
binary-rational precision format.
-/

namespace HeadComplexity

/-- A fixed alphabet for the raw-coordinate simulation. -/
noncomputable def rawScalarAlphabet : Finset ℝ := by
  classical
  exact {0, 1, -1, Real.sqrt 2, -Real.sqrt 2}

/-- A scalar that can be encoded by finitely many raw alphabet entries. -/
def RawAlphabetSum (x : ℝ) : Prop :=
  ∃ l : List ℝ, (∀ a ∈ l, a ∈ rawScalarAlphabet) ∧ l.sum = x

theorem neg_mem_rawScalarAlphabet {a : ℝ} (ha : a ∈ rawScalarAlphabet) :
    -a ∈ rawScalarAlphabet := by
  classical
  simp only [rawScalarAlphabet, Finset.mem_insert, Finset.mem_singleton] at ha ⊢
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp

theorem rawAlphabetSum_of_mem_pair_closure {x : ℝ}
    (hx : x ∈ AddSubgroup.closure ({Real.sqrt 2, 1} : Set ℝ)) :
    RawAlphabetSum x := by
  classical
  refine AddSubgroup.closure_induction
    (p := fun x _ ↦ RawAlphabetSum x) ?_ ?_ ?_ ?_ hx
  · intro a ha
    refine ⟨[a], ?_, by simp⟩
    intro b hb
    have hba : b = a := by simpa using hb
    subst b
    rcases ha with rfl | ha
    · simp [rawScalarAlphabet]
    · have ha' : a = 1 := by simpa using ha
      simp [ha', rawScalarAlphabet]
  · exact ⟨[], by simp, by simp⟩
  · intro a b _ _ ha hb
    obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨m, hm, rfl⟩ := hb
    refine ⟨l ++ m, ?_, by simp⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hl a ha
    · exact hm a ha
  · intro a _ ha
    obtain ⟨l, hl, rfl⟩ := ha
    refine ⟨l.map (fun a ↦ -a), ?_, (List.sum_neg l).symm⟩
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact neg_mem_rawScalarAlphabet (hl b hb)

/-- The available effective coefficients become dense when arbitrarily many
raw coordinates may be added. -/
theorem dense_rawAlphabetSum : Dense {x : ℝ | RawAlphabetSum x} := by
  have hd : Dense (AddSubgroup.closure ({Real.sqrt 2, 1} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr (by simpa using irrational_sqrt_two)
  exact hd.mono fun _ hx ↦ rawAlphabetSum_of_mem_pair_closure hx

theorem dense_rawAlphabetSum_vectors (K : Type*) :
    Dense {θ : K → ℝ | ∀ k, RawAlphabetSum (θ k)} := by
  simpa [Set.pi] using
    (dense_pi Set.univ (fun (_k : K) _ ↦ dense_rawAlphabetSum))

/-- Arbitrary finite strict signs survive approximation by finite sums of
five-symbol raw coordinates. This lemma concerns effective scalar scores;
it asserts neither a head-count saving nor a width bound. -/
theorem exists_rawAlphabetSum_strict_certificate
    {I K : Type*} [Finite I]
    (score : (K → ℝ) → I → ℝ)
    (hcontinuous : ∀ i, Continuous (fun θ ↦ score θ i))
    (f : I → Bool) (θ : K → ℝ)
    (hstrict : ∀ i, if f i then 0 < score θ i else score θ i < 0) :
    ∃ ξ : K → ℝ, (∀ k, RawAlphabetSum (ξ k)) ∧
      ∀ i, if f i then 0 < score ξ i else score ξ i < 0 := by
  have hopen (i : I) : IsOpen
      {ξ : K → ℝ | if f i then 0 < score ξ i else score ξ i < 0} := by
    cases hi : f i with
    | false => simpa using isOpen_lt (hcontinuous i) continuous_const
    | true => simpa using isOpen_lt continuous_const (hcontinuous i)
  have hopen' : IsOpen
      {ξ : K → ℝ | ∀ i, if f i then 0 < score ξ i else score ξ i < 0} := by
    simpa only [Set.ofPred_forall] using isOpen_iInter_of_finite hopen
  obtain ⟨ξ, hξ, hsign⟩ := (dense_rawAlphabetSum_vectors K).exists_mem_open
    hopen' ⟨θ, hstrict⟩
  exact ⟨ξ, hξ, hsign⟩

end HeadComplexity
