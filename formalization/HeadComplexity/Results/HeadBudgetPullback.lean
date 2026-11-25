import HeadComplexity.Results.RoPEComparison
import HeadComplexity.Results.FractionalNormalForm

/-!
# Exact head preservation under surjective coordinate identification

For pure atoms, input masses add over the fibers. For vanilla atoms, attention
masses add and positional values become their weighted averages. Surjectivity
ensures every new input mass is strictly positive. Both constructions preserve
the entire real score and apply to zero head budgets and empty input types.
-/

namespace HeadComplexity

open scoped BigOperators

namespace CoordinateIdentification

noncomputable def fiberSum {n N : ℕ} (π : Fin N → Fin n) (w : Fin N → ℝ)
    (i : Fin n) : ℝ := ∑ j ∈ Finset.univ.filter (fun j ↦ π j = i), w j

theorem fiberSum_pos {n N : ℕ} (π : Fin N → Fin n) (hπ : Function.Surjective π)
    (w : Fin N → ℝ) (hw : ∀ j, 0 < w j) (i : Fin n) : 0 < fiberSum π w i := by
  obtain ⟨j, hj⟩ := hπ i
  exact Finset.sum_pos' (fun j _ ↦ (hw j).le) ⟨j, by simp [hj], hw j⟩

theorem sum_fiberSum {n N : ℕ} (π : Fin N → Fin n) (w : Fin N → ℝ) :
    ∑ i, fiberSum π w i = ∑ j, w j :=
  Finset.sum_fiberwise Finset.univ π w

theorem sum_by_fibers {n N : ℕ} (π : Fin N → Fin n) (F : Fin n → Fin N → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ π j = i), F i j) =
      ∑ j, F (π j) j := by
  calc
    _ = ∑ i, fiberSum π (fun j ↦ F (π j) j) i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      change F i j = F (π j) j
      rw [(Finset.mem_filter.mp hj).2]
    _ = _ := sum_fiberSum π _

end CoordinateIdentification

namespace PureRoPEAtom

open CoordinateIdentification

noncomputable def identifyInputs {n N : ℕ} (p : PureRoPEAtom N)
    (π : Fin N → Fin n) (hπ : Function.Surjective π) : PureRoPEAtom n where
  a := fiberSum π p.a
  b := fiberSum π p.b
  γ := p.γ
  η := p.η
  v₀ := p.v₀
  v₁ := p.v₁
  ha := fiberSum_pos π hπ p.a p.ha
  hb := fiberSum_pos π hπ p.b p.hb
  hγ := p.hγ

theorem identifyInputs_eval {n N : ℕ} (p : PureRoPEAtom N)
    (π : Fin N → Fin n) (hπ : Function.Surjective π) (x : Fin n → Bool) :
    (p.identifyInputs π hπ).eval x = p.eval (x ∘ π) := by
  unfold eval identifyInputs
  congr 1
  · congr 1
    calc
      _ = ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ π j = i),
          if x i then p.b j * p.v₁ else p.a j * p.v₀ := by
        apply Finset.sum_congr rfl
        intro i _
        cases x i <;> simp [fiberSum, Finset.sum_mul]
      _ = _ := sum_by_fibers π _
  · congr 1
    calc
      _ = ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ π j = i),
          if x i then p.b j else p.a j := by
        apply Finset.sum_congr rfl
        intro i _
        cases x i <;> simp [fiberSum]
      _ = _ := sum_by_fibers π _

end PureRoPEAtom

namespace FracAtom

open CoordinateIdentification

noncomputable def identifyInputs {n N : ℕ} (p : FracAtom N)
    (π : Fin N → Fin n) (hπ : Function.Surjective π) : FracAtom n where
  η := p.η
  δ := p.δ
  γ := p.γ
  α := p.α
  ρ := fiberSum π p.ρ
  m i := fiberSum π (fun j ↦ p.ρ j * p.m j) i / fiberSum π p.ρ i
  hγ := p.hγ
  hα := p.hα
  hρ := fiberSum_pos π hπ p.ρ p.hρ

theorem identifyInputs_eval {n N : ℕ} (p : FracAtom N)
    (π : Fin N → Fin n) (hπ : Function.Surjective π) (x : Fin n → Bool) :
    (p.identifyInputs π hπ).eval x = p.eval (x ∘ π) := by
  unfold eval wt identifyInputs
  congr 1
  · congr 1
    calc
      _ = ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ π j = i),
          p.ρ j * (if x i then p.α else 1) * (p.m j + if x i then p.δ else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        have hρ := (fiberSum_pos π hπ p.ρ p.hρ i).ne'
        cases x i <;> simp only [Bool.false_eq_true, if_false, if_true]
        · simp only [add_zero, mul_one]
          rw [mul_div_cancel₀ _ hρ]
          rfl
        · rw [show fiberSum π p.ρ i * p.α *
              (fiberSum π (fun j ↦ p.ρ j * p.m j) i / fiberSum π p.ρ i + p.δ) =
              fiberSum π (fun j ↦ p.ρ j * p.m j) i * p.α +
                fiberSum π p.ρ i * p.α * p.δ by field_simp]
          simp only [fiberSum, Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = _ := sum_by_fibers π _
  · congr 1
    calc
      _ = ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ π j = i),
          p.ρ j * (if x i then p.α else 1) := by
        simp only [fiberSum, Finset.sum_mul]
      _ = _ := sum_by_fibers π _

end FracAtom

namespace CoordinateIdentification

theorem pure_pullback {n N H : ℕ} (π : Fin N → Fin n) (hπ : Function.Surjective π)
    {f : (Fin N → Bool) → Bool} (hf : pureRoPEComputable N H f) :
    pureRoPEComputable n H (fun x ↦ f (x ∘ π)) := by
  obtain ⟨p, c, hc⟩ := hf
  exact ⟨fun h ↦ (p h).identifyInputs π hπ, c,
    fun x ↦ by simpa only [PureRoPEAtom.identifyInputs_eval] using hc (x ∘ π)⟩

theorem vanilla_pullback {n N H : ℕ} (π : Fin N → Fin n) (hπ : Function.Surjective π)
    {f : (Fin N → Bool) → Bool} (hf : computableWithSharedHeadsN N H f) :
    computableWithSharedHeadsN n H (fun x ↦ f (x ∘ π)) := by
  obtain ⟨p, c, hc⟩ := (computableWithSharedHeadsN_iff_fracComputable H f).mp hf
  apply (computableWithSharedHeadsN_iff_fracComputable H _).mpr
  exact ⟨fun h ↦ (p h).identifyInputs π hπ, c,
    fun x ↦ by simpa only [FracAtom.identifyInputs_eval] using hc (x ∘ π)⟩

theorem original_vanilla_pullback {n N H : ℕ} (π : Fin N → Fin n)
    (hπ : Function.Surjective π) {f : (Fin N → Bool) → Bool}
    (hf : computableWithHeadsN N H f) :
    computableWithHeadsN n H (fun x ↦ f (x ∘ π)) :=
  computableWithHeadsN_of_computableWithSharedHeadsN
    (vanilla_pullback π hπ
      ((computableWithHeadsN_iff_computableWithSharedHeadsN N H f).mp hf))

theorem pure_minimum_pullback_le {n N : ℕ} (π : Fin N → Fin n)
    (hπ : Function.Surjective π) (f : (Fin N → Bool) → Bool) :
    PureRoPEHStar n (fun x ↦ f (x ∘ π)) ≤ PureRoPEHStar N f := by
  classical
  exact Nat.find_min' (exists_pureRoPEComputable _)
    (pure_pullback π hπ (pureRoPEHStar_computable f))

theorem original_minimum_pullback_le {n N : ℕ} (π : Fin N → Fin n)
    (hπ : Function.Surjective π) (f : (Fin N → Bool) → Bool) :
    HStar n (fun x ↦ f (x ∘ π)) ≤ HStar N f := by
  classical
  have he := exists_computable (fun x : Fin n → Bool ↦ f (x ∘ π))
  unfold HStar
  rw [dif_pos he]
  exact Nat.find_min' he (original_vanilla_pullback π hπ (HStar_computable f))

theorem shared_minimum_pullback_le {n N : ℕ} (π : Fin N → Fin n)
    (hπ : Function.Surjective π) (f : (Fin N → Bool) → Bool) :
    SharedHStar n (fun x ↦ f (x ∘ π)) ≤ SharedHStar N f := by
  simpa only [SharedHStar_eq_HStar] using original_minimum_pullback_le π hπ f

end CoordinateIdentification
end HeadComplexity
