import HeadComplexity.Results.FourBitThreeHeadCoverage

set_option linter.style.header false

namespace HeadComplexity.FourBitCertificate

open scoped BigOperators
open SignTemplate

def vertex : Fin 16 → Fin 4 → Bool :=
  ![![false, false, false, false], ![false, false, false, true], ![false, false, true, false], ![false, false, true, true], ![false, true, false, false], ![false, true, false, true], ![false, true, true, false], ![false, true, true, true], ![true, false, false, false], ![true, false, false, true], ![true, false, true, false], ![true, false, true, true], ![true, true, false, false], ![true, true, false, true], ![true, true, true, false], ![true, true, true, true]]

theorem vertex_surjective : Function.Surjective vertex := by
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3] := by
    ext i
    fin_cases i <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨13, rfl⟩
  · exact ⟨14, rfl⟩
  · exact ⟨15, rfl⟩

def slopes : Fin 3 → Fin 3 → Fin 4 → ℝ :=
  ![![![17, 17, 3, 2], ![3, 19, 14, 13], ![9, 12, 4, 13]], ![![1, 1, 1, 1], ![2, 2, 2, 2], ![3, 3, 3, 3]], ![![16, 11, 4, 13], ![11, 11, 1, 3], ![6, 4, 18, 8]]]

noncomputable def ratios (f : Fin 3) (a : Fin 13 → ℤ) : Fin 3 → AffineFraction 4 :=
  fun h => ⟨fun i => (a ⟨1 + h.val * 4 + i.val, by omega⟩ : ℝ), 0, slopes f h, 1⟩

noncomputable def denominator (f : Fin 3) (x : Fin 4 → Bool) : ℝ :=
  ∏ h : Fin 3, (1 + ∑ i : Fin 4, slopes f h i * boolToReal (x i))

theorem slopes_pos (f : Fin 3) (h : Fin 3) (i : Fin 4) : 0 < slopes f h i := by
  fin_cases f <;> fin_cases h <;> fin_cases i <;> norm_num [slopes]

theorem ratios_admissible (f : Fin 3) (a : Fin 13 → ℤ) (h : Fin 3) :
    (ratios f a h).Admissible := by
  refine ⟨?_, Or.inl (slopes_pos f h), ?_⟩
  · intro x
    have hn : 0 ≤ ∑ i, slopes f h i * boolToReal (x i) := by
      apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg (slopes_pos f h i).le
      cases x i <;> norm_num [boolToReal]
    change 0 < 1 + ∑ i, slopes f h i * boolToReal (x i)
    linarith
  · intro hz
    have hh := hz 0
    have hp := slopes_pos f h 0
    change slopes f h 0 = 0 at hh
    linarith

theorem denominator_pos (f : Fin 3) (x : Fin 4 → Bool) : 0 < denominator f x := by
  unfold denominator
  apply Finset.prod_pos
  intro h _
  exact (ratios_admissible f (fun _ => 0) h).1 x

set_option maxHeartbeats 0 in
-- Checking all 48 finite vertex/family pairs connects the integer data literally.
theorem score_eq (f : Fin 3) (a : Fin 13 → ℤ) (v : Fin 16) :
    (a 0 : ℝ) + ∑ h, (ratios f a h).eval (vertex v) =
      (SignTemplate.eval (features f) a v : ℝ) / denominator f (vertex v) := by
  fin_cases f <;> fin_cases v <;>
    norm_num [ratios, AffineFraction.eval, AffineFraction.numerator,
      AffineFraction.denominator, denominator, slopes, vertex, features,
      features0, features1, features2, SignTemplate.eval, Fin.sum_univ_succ,
      Fin.prod_univ_succ, boolToReal] <;> dsimp <;> norm_num <;> ring

theorem vanilla_of_strict_feature_score (f : (Fin 4 → Bool) → Bool)
    (j : Fin 3) (a : Fin 13 → ℤ)
    (ha : ∀ v, if f (vertex v) then 0 < SignTemplate.eval (features j) a v
      else SignTemplate.eval (features j) a v < 0) :
    computableWithSharedHeadsN 4 3 f := by
  apply (computableWithSharedHeadsN_iff_affineFractionComputable 3 f).mpr
  refine ⟨ratios j a, (a 0 : ℝ), ratios_admissible j a, ?_⟩
  intro x
  obtain ⟨v, rfl⟩ := vertex_surjective x
  rw [score_eq]
  have hd := denominator_pos j (vertex v)
  have hv := ha v
  cases hf : f (vertex v)
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    have hn : (SignTemplate.eval (features j) a v : ℝ) < 0 := by exact_mod_cast hv
    exact iff_false_intro (not_lt.mpr (div_neg_of_neg_of_pos hn hd).le)
  · simp only [hf, ↓reduceIte] at hv ⊢
    have hn : 0 < (SignTemplate.eval (features j) a v : ℝ) := by exact_mod_cast hv
    exact iff_true_intro (div_pos hn hd)

end HeadComplexity.FourBitCertificate
