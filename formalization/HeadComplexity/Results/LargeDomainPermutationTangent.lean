import HeadComplexity.Results.JointFamilyPermutationData

set_option linter.style.header false

/-! Distinct-pole permutation tangents. The two banks have `H + H` heads,
with exact zero-column axis and positive denominators on the full cube.
The final decoder hypothesis is explicit and is not proved in this file. -/

namespace HeadComplexity.LargeDomain

open AxisZeroGluing Filter Topology
open scoped BigOperators

private theorem tangent_negative_affine_pos {n : ℕ} (C : ℝ) (b : Fin n → ℝ)
    (hb : ∀ i, b i < 0) (hC : (∑ i, -b i) < C) (bits : Fin n → Bool) :
    0 < affineValue C b bits := by
  have hs : (∑ i, b i) ≤ ∑ i, b i * boolToReal (bits i) := by
    apply Finset.sum_le_sum
    intro i _
    cases bits i <;> simp [boolToReal, (hb i).le]
  simp only [Finset.sum_neg_distrib] at hC
  unfold affineValue
  linarith

private theorem tangent_complement_sum {k : ℕ} (d : Fin k → ℝ)
    (x : Fin k → Bool) :
    (∑ i, d i) - ∑ i, d i * boolToReal (x i) =
      ∑ i, d i * boolToReal (!(x i)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [boolToReal]

/-- Shared row directions may depend on the complete label family. Every
scalar column residue and compact offset is independent. -/
theorem exists_reverse_cube_star_scalar_score {k s H : ℕ}
    (η : ℝ) (_hη : 0 < η) (hmarginη : (s : ℝ) * η < 1 + η)
    (d : Fin H → Fin k → ℝ) (a b : Fin H → Fin s → ℝ)
    (hd : ∀ h i, 0 < d h i) (hb : ∀ h j, 1 < b h j ∧ b h j < 1 + η) :
    ∃ L : ReverseCubeStarData k s H, ∀ x j,
      L.score (cubeStarInput x j) =
        ∑ h, a h j / (b h j + ∑ i, d h i * boolToReal (!(x i))) := by
  classical
  let C (h : Fin H) := 1 + η + ∑ i, d h i
  let A (h : Fin H) : Fin (k + s) → ℝ := Fin.addCases (fun _ ↦ 0) (a h)
  let B (h : Fin H) : Fin (k + s) → ℝ :=
    Fin.addCases (fun i ↦ -d h i) (fun j ↦ b h j - (1 + η))
  have hnegative (h : Fin H) (i : Fin (k + s)) : B h i < 0 := by
    refine Fin.addCases ?_ ?_ i
    · intro l
      simpa [B] using neg_neg_of_pos (hd h l)
    · intro j
      simpa [B] using sub_neg.mpr (hb h j).2
  have hmargin (h : Fin H) : (∑ i, -B h i) < C h := by
    have hsum : (∑ j : Fin s, (1 + η - b h j)) ≤ (s : ℝ) * η := by
      calc
        _ ≤ ∑ _j : Fin s, η := by
          apply Finset.sum_le_sum
          intro j _
          linarith [(hb h j).1]
        _ = (s : ℝ) * η := by simp
    simp only [B, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      neg_neg, neg_sub] at ⊢
    dsimp [C]
    linarith
  let L : ReverseCubeStarData k s H :=
    { a₀ := fun _ ↦ 0
      b₀ := C
      a := A
      b := B
      positive := fun h bits ↦ tangent_negative_affine_pos _ _ (hnegative h) (hmargin h) bits
      negative := hnegative
      zero_column := by
        intro x
        simp [A, affineValue, Fin.sum_univ_add, boolToReal] }
  refine ⟨L, ?_⟩
  intro x j
  apply Finset.sum_congr rfl
  intro h _
  have hn : affineValue (L.a₀ h) (L.a h) (cubeStarInput x j) = a h j := by
    simp [L, A, affineValue, cubeStarInput, Fin.sum_univ_add, boolToReal]
  have hd' : affineValue (L.b₀ h) (L.b h) (cubeStarInput x j) =
      b h j + ∑ i, d h i * boolToReal (!(x i)) := by
    simp only [L, C, B, affineValue, cubeStarInput, Fin.sum_univ_add,
      Fin.addCases_left, Fin.addCases_right]
    have hj : (∑ l : Fin s, (b h l - (1 + η)) * boolToReal (decide (l = j))) =
        b h j - (1 + η) := by simp [boolToReal]
    rw [hj]
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [← tangent_complement_sum]
    ring
  change affineValue (L.a₀ h) (L.a h) (cubeStarInput x j) /
    affineValue (L.b₀ h) (L.b h) (cubeStarInput x j) = _
  rw [hn, hd']

noncomputable def permutationTangentScore {k s H : ℕ}
    (w : Fin k → ℝ) (b u₀ v₀ : Fin H → ℝ)
    (u v : Fin H → Fin k → ℝ) (π : Fin s → Equiv.Perm (Fin H))
    (x : Fin k → Bool) (j : Fin s) : ℝ :=
  ∑ h, (affineValue (v₀ (π j h)) (v (π j h)) x - affineValue (u₀ h) (u h) x) /
    (b h + ∑ i, w i * boolToReal (x i)) ^ 2

noncomputable def permutationTangentApprox {k s H : ℕ}
    (w : Fin k → ℝ) (b u₀ v₀ : Fin H → ℝ)
    (u v : Fin H → Fin k → ℝ) (π : Fin s → Equiv.Perm (Fin H))
    (t : ℝ) (x : Fin k → Bool) (j : Fin s) : ℝ :=
  ∑ h, (affineValue (v₀ (π j h)) (v (π j h)) x - affineValue (u₀ h) (u h) x) /
    ((b h + (∑ i, w i * boolToReal (x i)) + affineValue (u₀ h) (u h) x / t) *
      (b h + (∑ i, w i * boolToReal (x i)) +
        affineValue (v₀ (π j h)) (v (π j h)) x / t))

private theorem tangent_denominator_positive {k : ℕ}
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (b : ℝ) (hb : 0 < b)
    (x : Fin k → Bool) : 0 < b + ∑ i, w i * boolToReal (x i) := by
  exact add_pos_of_pos_of_nonneg hb
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hw i).le (boolToReal_nonneg _)))

/-- The first-order score includes one affine feature vector per pole. -/
theorem permutationTangentApprox_tendsto {k s H : ℕ}
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (b u₀ v₀ : Fin H → ℝ)
    (hb : ∀ h, 0 < b h) (u v : Fin H → Fin k → ℝ)
    (π : Fin s → Equiv.Perm (Fin H)) (x : Fin k → Bool) (j : Fin s) :
    Tendsto (fun t : ℝ ↦ permutationTangentApprox w b u₀ v₀ u v π t x j)
      atTop (𝓝 (permutationTangentScore w b u₀ v₀ u v π x j)) := by
  unfold permutationTangentApprox permutationTangentScore
  apply tendsto_finsetSum
  intro h _
  have h₁ : Tendsto (fun t : ℝ ↦ b h + (∑ i, w i * boolToReal (x i)) +
      affineValue (u₀ h) (u h) x / t) atTop
      (𝓝 (b h + ∑ i, w i * boolToReal (x i))) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_const_nhds (x := affineValue (u₀ h) (u h) x)).div_atTop
        (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop))
  have h₂ : Tendsto (fun t : ℝ ↦ b h + (∑ i, w i * boolToReal (x i)) +
      affineValue (v₀ (π j h)) (v (π j h)) x / t) atTop
      (𝓝 (b h + ∑ i, w i * boolToReal (x i))) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_const_nhds (x := affineValue (v₀ (π j h)) (v (π j h)) x)).div_atTop
        (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop))
  have hne := (tangent_denominator_positive w hw (b h) (hb h) x).ne'
  convert (tendsto_const_nhds
    (x := affineValue (v₀ (π j h)) (v (π j h)) x - affineValue (u₀ h) (u h) x)).div
      (h₁.mul h₂) (mul_ne_zero hne hne) using 1
  simp [pow_two]

private theorem tangent_affine_perturb {k : ℕ} (w u : Fin k → ℝ) (b u₀ t : ℝ)
    (x : Fin k → Bool) :
    (b + u₀ / t) + ∑ i, (w i + u i / t) * boolToReal (x i) =
      b + (∑ i, w i * boolToReal (x i)) + affineValue u₀ u x / t := by
  simp only [add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div, ← Finset.sum_div,
    affineValue, add_div]
  ring

/-- Compact offsets and positive row directions survive any fixed affine
perturbation for all sufficiently large scales, uniformly over the family. -/
theorem permutationTangent_eventual_admissible {k s H : ℕ}
    (η : ℝ) (w : Fin k → ℝ) (hw : ∀ i, 0 < w i)
    (b u₀ v₀ : Fin H → ℝ) (hb : ∀ h, 1 < b h ∧ b h < 1 + η)
    (u v : Fin H → Fin k → ℝ) (π : Fin s → Equiv.Perm (Fin H)) :
    ∀ᶠ t : ℝ in atTop,
      (∀ h i, 0 < w i + u h i / t) ∧ (∀ h i, 0 < w i + v h i / t) ∧
      (∀ h (_j : Fin s), 1 < b h + u₀ h / t ∧ b h + u₀ h / t < 1 + η) ∧
      (∀ h j, 1 < b ((π j).symm h) + v₀ h / t ∧
        b ((π j).symm h) + v₀ h / t < 1 + η) := by
  have hpos (q : Fin H → Fin k → ℝ) :
      ∀ᶠ t : ℝ in atTop, ∀ h i, 0 < w i + q h i / t := by
    apply Filter.eventually_all.mpr
    intro h
    apply Filter.eventually_all.mpr
    intro i
    have ht : Tendsto (fun t : ℝ ↦ w i + q h i / t) atTop (𝓝 (w i)) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_const_nhds (x := q h i)).div_atTop
          (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop))
    exact ht.eventually (eventually_gt_nhds (hw i))
  have hoff (q : Fin H → ℝ) (ρ : Fin s → Equiv.Perm (Fin H)) :
      ∀ᶠ t : ℝ in atTop, ∀ h j,
        1 < b (ρ j h) + q h / t ∧ b (ρ j h) + q h / t < 1 + η := by
    apply Filter.eventually_all.mpr
    intro h
    apply Filter.eventually_all.mpr
    intro j
    have ht : Tendsto (fun t : ℝ ↦ b (ρ j h) + q h / t) atTop
        (𝓝 (b (ρ j h))) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_const_nhds (x := q h)).div_atTop
          (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop))
    exact (ht.eventually (eventually_gt_nhds (hb (ρ j h)).1)).and
      (ht.eventually (eventually_lt_nhds (hb (ρ j h)).2))
  have hu := hoff u₀ (fun _ ↦ Equiv.refl _)
  have hv := hoff v₀ (fun j ↦ (π j).symm)
  filter_upwards [hpos u, hpos v, hu, hv] with t h₁ h₂ h₃ h₄
  exact ⟨h₁, h₂, by simpa using h₃, h₄⟩

/-- A single scale realizes the exact difference quotient using two banks.
The negative bank's column offsets are independently permuted. -/
theorem exists_permutationTangentApprox_data {k s H : ℕ}
    (η : ℝ) (hη : 0 < η) (hmarginη : (s : ℝ) * η < 1 + η)
    (w : Fin k → ℝ) (b u₀ v₀ : Fin H → ℝ)
    (u v : Fin H → Fin k → ℝ) (π : Fin s → Equiv.Perm (Fin H))
    (t : ℝ) (ht : 0 < t)
    (hu : ∀ h i, 0 < w i + u h i / t)
    (hv : ∀ h i, 0 < w i + v h i / t)
    (hbu : ∀ h, 1 < b h + u₀ h / t ∧ b h + u₀ h / t < 1 + η)
    (hbv : ∀ h j, 1 < b ((π j).symm h) + v₀ h / t ∧
      b ((π j).symm h) + v₀ h / t < 1 + η) :
    ∃ L : ReverseCubeStarData k s (H + H), ∀ x j,
      L.score (cubeStarInput (fun i ↦ !(x i)) j) =
        permutationTangentApprox w b u₀ v₀ u v π t x j := by
  obtain ⟨P, hP⟩ := exists_reverse_cube_star_scalar_score η hη hmarginη
    (fun h i ↦ w i + u h i / t) (fun _ _ ↦ t)
    (fun h _ ↦ b h + u₀ h / t) hu (fun h _ ↦ hbu h)
  obtain ⟨Q, hQ⟩ := exists_reverse_cube_star_scalar_score η hη hmarginη
    (fun h i ↦ w i + v h i / t) (fun _ _ ↦ -t)
    (fun h j ↦ b ((π j).symm h) + v₀ h / t) hv hbv
  refine ⟨jointFamilyAppendData P Q, ?_⟩
  intro x j
  rw [jointFamilyAppendData_score, hP, hQ]
  simp only [Bool.not_not, tangent_affine_perturb]
  have hreindex :
      (∑ h, -t / (b ((π j).symm h) + (∑ i, w i * boolToReal (x i)) +
        affineValue (v₀ h) (v h) x / t)) =
      ∑ h, -t / (b h + (∑ i, w i * boolToReal (x i)) +
        affineValue (v₀ (π j h)) (v (π j h)) x / t) := by
    conv_lhs => rw [← Equiv.sum_comp (π j)
      (fun h ↦ -t / (b ((π j).symm h) + (∑ i, w i * boolToReal (x i)) +
        affineValue (v₀ h) (v h) x / t))]
    simp only [Equiv.symm_apply_apply]
  rw [hreindex, ← Finset.sum_add_distrib]
  unfold permutationTangentApprox
  apply Finset.sum_congr rfl
  intro h _
  have hdu : b h + (∑ i, w i * boolToReal (x i)) +
      affineValue (u₀ h) (u h) x / t ≠ 0 := by
    rw [← tangent_affine_perturb]
    exact (tangent_denominator_positive _ (hu h) _ (by linarith [(hbu h).1]) x).ne'
  have hdv : b h + (∑ i, w i * boolToReal (x i)) +
      affineValue (v₀ (π j h)) (v (π j h)) x / t ≠ 0 := by
    rw [← tangent_affine_perturb]
    have hb' := (hbv (π j h) j).1
    simp only [Equiv.symm_apply_apply] at hb'
    exact (tangent_denominator_positive _ (hv (π j h)) _ (by linarith) x).ne'
  rw [div_add_div _ _ hdu hdv]
  congr 1
  field_simp [ht.ne']
  ring

/-- Strict target signs and any prior score are preserved simultaneously.
No correction is needed on the columnzero axis: each bank is already zero. -/
theorem permutationTangent_preserves_signs {k s H : ℕ}
    (η : ℝ) (hη : 0 < η) (hmarginη : (s : ℝ) * η < 1 + η)
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i)
    (b u₀ v₀ : Fin H → ℝ) (hb : ∀ h, 1 < b h ∧ b h < 1 + η)
    (u v : Fin H → Fin k → ℝ) (π : Fin s → Equiv.Perm (Fin H))
    (σ prior : (Fin k → Bool) → Fin s → ℝ)
    (hstrict : ∀ x j, 0 < σ x j *
      (prior x j + permutationTangentScore w b u₀ v₀ u v π x j)) :
    ∃ L : ReverseCubeStarData k s (H + H), ∀ x j,
      0 < σ x j * (prior x j + L.score (cubeStarInput (fun i ↦ !(x i)) j)) := by
  have hadm := permutationTangent_eventual_admissible η w hw b u₀ v₀ hb u v π
  have hsign : ∀ᶠ t : ℝ in atTop, ∀ x j, 0 < σ x j *
      (prior x j + permutationTangentApprox w b u₀ v₀ u v π t x j) := by
    apply Filter.eventually_all.mpr
    intro x
    apply Filter.eventually_all.mpr
    intro j
    exact ((tendsto_const_nhds.add
      (permutationTangentApprox_tendsto w hw b u₀ v₀
        (fun h ↦ by linarith [(hb h).1]) u v π x j)).const_mul (σ x j)).eventually
          (eventually_gt_nhds (hstrict x j))
  have hbu : ∀ᶠ t : ℝ in atTop, ∀ h,
      1 < b h + u₀ h / t ∧ b h + u₀ h / t < 1 + η := by
    apply Filter.eventually_all.mpr
    intro h
    have ht : Tendsto (fun t : ℝ ↦ b h + u₀ h / t) atTop (𝓝 (b h)) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_const_nhds (x := u₀ h)).div_atTop
          (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop))
    exact (ht.eventually (eventually_gt_nhds (hb h).1)).and
      (ht.eventually (eventually_lt_nhds (hb h).2))
  obtain ⟨t, ht, hadm, hbu, hsign⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (hadm.and (hbu.and hsign))).exists
  obtain ⟨L, hL⟩ := exists_permutationTangentApprox_data η hη hmarginη
    w b u₀ v₀ u v π t ht hadm.1 hadm.2.1 hbu hadm.2.2.2
  exact ⟨L, fun x j ↦ by rw [hL]; exact hsign x j⟩

/-- This is the unresolved projected-permutation-orbit hypothesis. Directions,
poles and affine perturbations may be adapted to the entire label family. -/
def HasCompactPermutationTangentDecoder (k s H : ℕ) : Prop :=
  ∀ table : (Fin k → Bool) → Fin s → Bool, ∀ η : ℝ, 0 < η →
    ∃ w : Fin k → ℝ, ∃ b u₀ v₀ : Fin H → ℝ,
      ∃ u v : Fin H → Fin k → ℝ, ∃ π : Fin s → Equiv.Perm (Fin H),
        (∀ i, 0 < w i) ∧ (∀ h, 1 < b h ∧ b h < 1 + η) ∧
        ∀ x j, 0 < outputSign (table x j) * permutationTangentScore w b u₀ v₀ u v π x j

theorem hasReverseCubeStarCompiler_of_permutationTangent {k s H : ℕ}
    (hdecoder : HasCompactPermutationTangentDecoder k s H) :
    HasReverseCubeStarCompiler k s (H + H) := by
  classical
  intro table
  let η : ℝ := 1 / ((s : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : η * ((s : ℝ) + 1) = 1 := by
    dsimp [η]
    exact div_mul_cancel₀ _ (by positivity)
  obtain ⟨w, b, u₀, v₀, u, v, π, hw, hb, hsign⟩ :=
    hdecoder (fun x j ↦ table (fun i ↦ !(x i)) j) η hη
  obtain ⟨L, hL⟩ := permutationTangent_preserves_signs η hη (by nlinarith)
    w hw b u₀ v₀ hb u v π (fun x j ↦ outputSign (table (fun i ↦ !(x i)) j))
      (fun _ _ ↦ 0) (by simpa using hsign)
  refine ⟨H + H, le_rfl, L, fun x j ↦ ?_⟩
  simpa only [Bool.not_not, zero_add] using hL (fun i ↦ !(x i)) j

/-- Conditional global count in the original model, including the exception face. -/
theorem worstCaseHeadComplexity_real_le_of_permutationTangent {k s H : ℕ}
    (hs : 0 < s) (hdecoder : HasCompactPermutationTangentDecoder k s H) :
    (worstCaseHeadComplexity (k + s) : ℝ) ≤
      22 * (2 : ℝ) ^ s * (H + H) / s + 2 ^ (k + 1) := by
  have ht := worstCaseHeadComplexity_real_le_of_cube_star_compiler hs
    (hasReverseCubeStarCompiler_of_permutationTangent hdecoder)
  simpa only [Nat.cast_add] using ht

end HeadComplexity.LargeDomain
