import HeadComplexity.Results.LargeDomainPermutationTangent

set_option linter.style.header false

/-! Independent column residues and reciprocal corrections enlarge the tangent
family at the same two-bank cost. The decoder hypothesis remains unproved. -/

namespace HeadComplexity.LargeDomain

open AxisZeroGluing Filter Topology
open scoped BigOperators

noncomputable def weightedPermutationTangentScore {k s H : ℕ}
    (w : Fin k → ℝ) (b u₀ v₀ : Fin H → ℝ)
    (u v : Fin H → Fin k → ℝ) (π : Fin s → Equiv.Perm (Fin H))
    (a c : Fin H → Fin s → ℝ)
    (x : Fin k → Bool) (j : Fin s) : ℝ :=
  ∑ h, (a h j * (affineValue (v₀ (π j h)) (v (π j h)) x - affineValue (u₀ h) (u h) x) /
    (b h + ∑ i, w i * boolToReal (x i)) ^ 2 +
      c h j / (b h + ∑ i, w i * boolToReal (x i)))

noncomputable def weightedPermutationTangentApprox {k s H : ℕ}
    (w : Fin k → ℝ) (b u₀ v₀ : Fin H → ℝ)
    (u v : Fin H → Fin k → ℝ) (π : Fin s → Equiv.Perm (Fin H))
    (a c : Fin H → Fin s → ℝ)
    (t : ℝ) (x : Fin k → Bool) (j : Fin s) : ℝ :=
  ∑ h, (a h j * (affineValue (v₀ (π j h)) (v (π j h)) x - affineValue (u₀ h) (u h) x) /
    ((b h + (∑ i, w i * boolToReal (x i)) + affineValue (u₀ h) (u h) x / t) *
      (b h + (∑ i, w i * boolToReal (x i)) +
        affineValue (v₀ (π j h)) (v (π j h)) x / t)) +
      c h j / (b h + (∑ i, w i * boolToReal (x i)) + affineValue (u₀ h) (u h) x / t))

private theorem tangent_denominator_positive {k : ℕ}
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (b : ℝ) (hb : 0 < b)
    (x : Fin k → Bool) : 0 < b + ∑ i, w i * boolToReal (x i) := by
  exact add_pos_of_pos_of_nonneg hb
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hw i).le (boolToReal_nonneg _)))

/-- The first-order score includes one affine feature vector per pole. -/
theorem weightedPermutationTangentApprox_tendsto {k s H : ℕ}
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (b u₀ v₀ : Fin H → ℝ)
    (hb : ∀ h, 0 < b h) (u v : Fin H → Fin k → ℝ)
    (π : Fin s → Equiv.Perm (Fin H))
    (a c : Fin H → Fin s → ℝ) (x : Fin k → Bool) (j : Fin s) :
    Tendsto (fun t : ℝ ↦ weightedPermutationTangentApprox w b u₀ v₀ u v π a c t x j)
      atTop (𝓝 (weightedPermutationTangentScore w b u₀ v₀ u v π a c x j)) := by
  unfold weightedPermutationTangentApprox weightedPermutationTangentScore
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
  have hf := (tendsto_const_nhds
    (x := a h j * (affineValue (v₀ (π j h)) (v (π j h)) x - affineValue (u₀ h) (u h) x))).div
      (h₁.mul h₂) (mul_ne_zero hne hne)
  convert hf.add ((tendsto_const_nhds (x := c h j)).div h₁ hne) using 1
  simp [pow_two]

private theorem tangent_affine_perturb {k : ℕ} (w u : Fin k → ℝ) (b u₀ t : ℝ)
    (x : Fin k → Bool) :
    (b + u₀ / t) + ∑ i, (w i + u i / t) * boolToReal (x i) =
      b + (∑ i, w i * boolToReal (x i)) + affineValue u₀ u x / t := by
  simp only [add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div, ← Finset.sum_div,
    affineValue, add_div]
  ring

/-- A single scale realizes the exact difference quotient using two banks.
The negative bank's column offsets are independently permuted. -/
theorem exists_weightedPermutationTangentApprox_data {k s H : ℕ}
    (η : ℝ) (hη : 0 < η) (hmarginη : (s : ℝ) * η < 1 + η)
    (w : Fin k → ℝ) (b u₀ v₀ : Fin H → ℝ)
    (u v : Fin H → Fin k → ℝ) (π : Fin s → Equiv.Perm (Fin H))
    (a c : Fin H → Fin s → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hu : ∀ h i, 0 < w i + u h i / t)
    (hv : ∀ h i, 0 < w i + v h i / t)
    (hbu : ∀ h, 1 < b h + u₀ h / t ∧ b h + u₀ h / t < 1 + η)
    (hbv : ∀ h j, 1 < b ((π j).symm h) + v₀ h / t ∧
      b ((π j).symm h) + v₀ h / t < 1 + η) :
    ∃ L : ReverseCubeStarData k s (H + H), ∀ x j,
      L.score (cubeStarInput (fun i ↦ !(x i)) j) =
        weightedPermutationTangentApprox w b u₀ v₀ u v π a c t x j := by
  obtain ⟨P, hP⟩ := exists_reverse_cube_star_scalar_score η hη hmarginη
    (fun h i ↦ w i + u h i / t) (fun h j ↦ t * a h j + c h j)
    (fun h _ ↦ b h + u₀ h / t) hu (fun h _ ↦ hbu h)
  obtain ⟨Q, hQ⟩ := exists_reverse_cube_star_scalar_score η hη hmarginη
    (fun h i ↦ w i + v h i / t) (fun h j ↦ -t * a ((π j).symm h) j)
    (fun h j ↦ b ((π j).symm h) + v₀ h / t) hv hbv
  refine ⟨jointFamilyAppendData P Q, ?_⟩
  intro x j
  rw [jointFamilyAppendData_score, hP, hQ]
  simp only [Bool.not_not, tangent_affine_perturb]
  have hreindex :
      (∑ h, (-t * a ((π j).symm h) j) / (b ((π j).symm h) + (∑ i, w i * boolToReal (x i)) +
        affineValue (v₀ h) (v h) x / t)) =
      ∑ h, (-t * a h j) / (b h + (∑ i, w i * boolToReal (x i)) +
        affineValue (v₀ (π j h)) (v (π j h)) x / t) := by
    conv_lhs => rw [← Equiv.sum_comp (π j)
      (fun h ↦ (-t * a ((π j).symm h) j) / (b ((π j).symm h) + (∑ i, w i * boolToReal (x i)) +
        affineValue (v₀ h) (v h) x / t))]
    simp only [Equiv.symm_apply_apply]
  rw [hreindex, ← Finset.sum_add_distrib]
  unfold weightedPermutationTangentApprox
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
  rw [add_div]
  have hpair : t * a h j /
      (b h + (∑ i, w i * boolToReal (x i)) + affineValue (u₀ h) (u h) x / t) +
      (-t * a h j) /
      (b h + (∑ i, w i * boolToReal (x i)) +
        affineValue (v₀ (π j h)) (v (π j h)) x / t) =
      a h j * (affineValue (v₀ (π j h)) (v (π j h)) x -
        affineValue (u₀ h) (u h) x) /
      ((b h + (∑ i, w i * boolToReal (x i)) + affineValue (u₀ h) (u h) x / t) *
        (b h + (∑ i, w i * boolToReal (x i)) +
          affineValue (v₀ (π j h)) (v (π j h)) x / t)) := by
    rw [div_add_div _ _ hdu hdv]
    congr 1
    field_simp [ht.ne']
    ring
  linarith [hpair]

/-- Strict target signs and any prior score are preserved simultaneously.
No correction is needed on the columnzero axis: each bank is already zero. -/
theorem weightedPermutationTangent_preserves_signs {k s H : ℕ}
    (η : ℝ) (hη : 0 < η) (hmarginη : (s : ℝ) * η < 1 + η)
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i)
    (b u₀ v₀ : Fin H → ℝ) (hb : ∀ h, 1 < b h ∧ b h < 1 + η)
    (u v : Fin H → Fin k → ℝ) (π : Fin s → Equiv.Perm (Fin H))
    (a c : Fin H → Fin s → ℝ)
    (σ prior : (Fin k → Bool) → Fin s → ℝ)
    (hstrict : ∀ x j, 0 < σ x j *
      (prior x j + weightedPermutationTangentScore w b u₀ v₀ u v π a c x j)) :
    ∃ L : ReverseCubeStarData k s (H + H), ∀ x j,
      0 < σ x j * (prior x j + L.score (cubeStarInput (fun i ↦ !(x i)) j)) := by
  have hadm := permutationTangent_eventual_admissible η w hw b u₀ v₀ hb u v π
  have hsign : ∀ᶠ t : ℝ in atTop, ∀ x j, 0 < σ x j *
      (prior x j + weightedPermutationTangentApprox w b u₀ v₀ u v π a c t x j) := by
    apply Filter.eventually_all.mpr
    intro x
    apply Filter.eventually_all.mpr
    intro j
    exact ((tendsto_const_nhds.add
      (weightedPermutationTangentApprox_tendsto w hw b u₀ v₀
        (fun h ↦ by linarith [(hb h).1]) u v π a c x j)).const_mul (σ x j)).eventually
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
  obtain ⟨L, hL⟩ := exists_weightedPermutationTangentApprox_data η hη hmarginη
    w b u₀ v₀ u v π a c t ht hadm.1 hadm.2.1 hbu hadm.2.2.2
  exact ⟨L, fun x j ↦ by rw [hL]; exact hsign x j⟩

/-- This is the unresolved projected-permutation-orbit hypothesis. Directions,
poles and affine perturbations may be adapted to the entire label family. -/
def HasCompactWeightedPermutationTangentDecoder (k s H : ℕ) : Prop :=
  ∀ table : (Fin k → Bool) → Fin s → Bool, ∀ η : ℝ, 0 < η →
    ∃ w : Fin k → ℝ, ∃ b u₀ v₀ : Fin H → ℝ,
      ∃ u v : Fin H → Fin k → ℝ, ∃ π : Fin s → Equiv.Perm (Fin H),
        ∃ a c : Fin H → Fin s → ℝ,
        (∀ i, 0 < w i) ∧ (∀ h, 1 < b h ∧ b h < 1 + η) ∧
        ∀ x j, 0 < outputSign (table x j) * weightedPermutationTangentScore w b u₀ v₀ u v π a c x j

theorem hasReverseCubeStarCompiler_of_weightedPermutationTangent {k s H : ℕ}
    (hdecoder : HasCompactWeightedPermutationTangentDecoder k s H) :
    HasReverseCubeStarCompiler k s (H + H) := by
  classical
  intro table
  let η : ℝ := 1 / ((s : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : η * ((s : ℝ) + 1) = 1 := by
    dsimp [η]
    exact div_mul_cancel₀ _ (by positivity)
  obtain ⟨w, b, u₀, v₀, u, v, π, a, c, hw, hb, hsign⟩ :=
    hdecoder (fun x j ↦ table (fun i ↦ !(x i)) j) η hη
  obtain ⟨L, hL⟩ := weightedPermutationTangent_preserves_signs η hη (by nlinarith)
    w hw b u₀ v₀ hb u v π a c (fun x j ↦ outputSign (table (fun i ↦ !(x i)) j))
      (fun _ _ ↦ 0) (by simpa using hsign)
  refine ⟨H + H, le_rfl, L, fun x j ↦ ?_⟩
  simpa only [Bool.not_not, zero_add] using hL (fun i ↦ !(x i)) j

/-- Conditional global count in the original model, including the exception face. -/
theorem worstCaseHeadComplexity_real_le_of_weightedPermutationTangent {k s H : ℕ}
    (hs : 0 < s) (hdecoder : HasCompactWeightedPermutationTangentDecoder k s H) :
    (worstCaseHeadComplexity (k + s) : ℝ) ≤
      22 * (2 : ℝ) ^ s * (H + H) / s + 2 ^ (k + 1) := by
  have ht := worstCaseHeadComplexity_real_le_of_cube_star_compiler hs
    (hasReverseCubeStarCompiler_of_weightedPermutationTangent hdecoder)
  simpa only [Nat.cast_add] using ht

end HeadComplexity.LargeDomain
