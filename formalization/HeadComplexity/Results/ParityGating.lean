import HeadComplexity.Atoms.ClearedNormalForm
import HeadComplexity.Atoms.UniformApproximationSum
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Gating by arbitrary parity checks

An existing classifier on selected information coordinates can be restricted
by finitely many parity equations. Each parity check costs the cardinality of
its coordinate support, with no boundedness assumptions on the original real
parameters. This is an upper bound for a restricted target family, not an
asymptotic lower bound for worst-case head complexity.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {m n H r : ℕ}

/-- A Walsh character always has one of the two signed Boolean values. -/
theorem walshCharacter_eq_one_or_neg_one (S : Finset (Fin n))
    (bits : Fin n → Bool) :
    walshCharacter S bits = 1 ∨ walshCharacter S bits = -1 := by
  unfold walshCharacter
  split <;> simp

/-- A classifier can be gated by arbitrary parity checks at the sum of their
support sizes. The final representation uses genuine attention atoms. -/
theorem computableWithHeadsN_parityGate
    (e : Fin m ↪ Fin n) (S : Fin r → Finset (Fin n))
    (sigma : Fin r → ℝ) (hsigma : ∀ j, sigma j = 1 ∨ sigma j = -1)
    {g : (Fin m → Bool) → Bool} (hg : computableWithHeadsN m H g)
    {f : (Fin n → Bool) → Bool}
    (hf : ∀ x, f x = if ∀ j, walshCharacter (S j) x = sigma j
      then g (pullBitsAlong e x) else false) :
    computableWithHeadsN n (H + ∑ j, (S j).card) f := by
  classical
  obtain ⟨phi, c, hphi⟩ :=
    exists_strict_fracCertificate (fracComputable_of_computable hg)
  let G : (Fin m → Bool) → ℝ := fun x ↦ c + ∑ h, (phi h).eval x
  obtain ⟨largest, -, hmax⟩ :=
    (Finset.univ : Finset (Fin m → Bool)).exists_max_image
      (fun x ↦ |G x|) Finset.univ_nonempty
  let M : ℝ := |G largest| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hbound : ∀ x, |G x| < M := by
    intro x
    have hx := hmax x (Finset.mem_univ x)
    dsimp [M]
    linarith
  let penalty : Fin r → (Fin n → Bool) → ℝ :=
    fun j x ↦ M / 2 * (1 - sigma j * walshCharacter (S j) x)
  have hpen_nonneg : ∀ j x, 0 ≤ penalty j x := by
    intro j x
    rcases hsigma j with hs | hs <;>
      rcases walshCharacter_eq_one_or_neg_one (S j) x with hw | hw <;>
      simp [penalty, hs, hw] <;> positivity
  have hpen_zero : ∀ j x, walshCharacter (S j) x = sigma j → penalty j x = 0 := by
    intro j x heq
    rcases hsigma j with hs | hs <;> simp [penalty, heq, hs]
  have hpen_bad : ∀ j x, walshCharacter (S j) x ≠ sigma j → penalty j x = M := by
    intro j x hneq
    rcases hsigma j with hs | hs <;>
      rcases walshCharacter_eq_one_or_neg_one (S j) x with hw | hw <;>
      simp_all [penalty] <;> ring
  let score : (Fin n → Bool) → ℝ :=
    fun x ↦ G (pullBitsAlong e x) - ∑ j, penalty j x
  have hstrict : StrictSignRepresentsScore score f := by
    intro x
    by_cases hcheck : ∀ j, walshCharacter (S j) x = sigma j
    · have hzero : ∑ j, penalty j x = 0 :=
        Finset.sum_eq_zero fun j _ ↦ hpen_zero j x (hcheck j)
      have heq : score x = G (pullBitsAlong e x) := by simp [score, hzero]
      rw [heq, hf x, ite_eq_left hcheck]
      have hx := hphi (pullBitsAlong e x)
      change (if g (pullBitsAlong e x) then 0 < G (pullBitsAlong e x)
        else G (pullBitsAlong e x) < 0) at hx
      cases hb : g (pullBitsAlong e x) <;> simp only [hb, Bool.false_eq_true,
        ↓reduceIte] at hx ⊢
      · exact ⟨iff_false_intro (not_lt.mpr hx.le), ne_of_lt hx⟩
      · exact ⟨iff_true_intro hx, ne_of_gt hx⟩
    · obtain ⟨j, hj⟩ := not_forall.mp hcheck
      have hsum : M ≤ ∑ i, penalty i x := by
        rw [← hpen_bad j x hj]
        exact Finset.single_le_sum (fun i _ ↦ hpen_nonneg i x) (Finset.mem_univ j)
      have hneg : score x < 0 := by
        have hu := le_abs_self (G (pullBitsAlong e x))
        have hb := hbound (pullBitsAlong e x)
        dsimp [score]
        linarith
      rw [hf x, ite_eq_right hcheck]
      simp only [Bool.false_eq_true]
      exact ⟨iff_false_intro (not_lt.mpr hneg.le), ne_of_lt hneg⟩
  let J := Fin H ⊕ Fin r
  let I : J → Type := fun j ↦ match j with
    | Sum.inl _ => Fin 1
    | Sum.inr k => Fin (S k).card
  let : ∀ j, Fintype (I j) := fun j ↦ by
    cases j <;> dsimp [I] <;> infer_instance
  let component : J → (Fin n → Bool) → ℝ := fun j ↦ match j with
    | Sum.inl h => fun x ↦ (phi h).eval (pullBitsAlong e x)
    | Sum.inr k => fun x ↦ M / 2 * sigma k * walshCharacter (S k) x
  have happrox : ∀ j, UniformlyAtomsApproximable (I j) (component j) := by
    intro j
    cases j with
    | inl h =>
        intro epsilon hepsilon
        obtain ⟨delta, hdelta, hdelta_close⟩ :=
          exists_liftDummyAlong_uniform (fun _ : Fin 1 ↦ phi h) 0 e epsilon hepsilon
        refine ⟨fun _ ↦ (phi h).liftDummy e delta hdelta, 0, fun x ↦ ?_⟩
        simpa [component] using hdelta_close x
    | inr k =>
        exact uniformlyAtomsApproximable_walshCharacter (S k) (M / 2 * sigma k)
  let bias : ℝ := c - M / 2 * r
  have hscore : (fun x ↦ bias + ∑ j, component j x) = score := by
    funext x
    change bias + (∑ j : Fin H ⊕ Fin r, component j x) = score x
    rw [Fintype.sum_sum_type]
    simp only [component]
    dsimp [score, G, bias, penalty]
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hc := computableWithHeadsCard_of_uniformlyAtomsApproximable
    component happrox bias (hscore.symm ▸ hstrict)
  have hcard : Fintype.card (Sigma I) = H + ∑ j, (S j).card := by
    simp [Fintype.card_sigma, I, J, Fintype.sum_sum_type]
  rwa [hcard] at hc

/-- Head complexity version of the parity-gating construction. -/
theorem HStar_parityGate_le
    (e : Fin m ↪ Fin n) (S : Fin r → Finset (Fin n))
    (sigma : Fin r → ℝ) (hsigma : ∀ j, sigma j = 1 ∨ sigma j = -1)
    (g : (Fin m → Bool) → Bool) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, f x = if ∀ j, walshCharacter (S j) x = sigma j
      then g (pullBitsAlong e x) else false) :
    HStar n f ≤ HStar m g + ∑ j, (S j).card :=
  HStar_le_of_computableWithHeadsN
    (computableWithHeadsN_parityGate e S sigma hsigma (HStar_computable g) hf)

end HeadComplexity
