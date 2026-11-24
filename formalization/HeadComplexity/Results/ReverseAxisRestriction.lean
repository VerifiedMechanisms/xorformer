import HeadComplexity.Results.ReverseGridEmbedding

set_option linter.style.header false

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

private noncomputable def pushBits {n m : ℕ} (e : Fin n ↪ Fin m)
    (bits : Fin n → Bool) (j : Fin m) : Bool := by
  classical
  exact decide (∃ i, e i = j ∧ bits i = true)

private theorem pushBits_apply {n m : ℕ} (e : Fin n ↪ Fin m)
    (bits : Fin n → Bool) (i : Fin n) : pushBits e bits (e i) = bits i := by
  classical
  simp [pushBits, e.injective.eq_iff]

private theorem pushBits_false {n m : ℕ} (e : Fin n ↪ Fin m) :
    pushBits e (fun _ ↦ false) = fun _ ↦ false := by
  classical
  funext j
  simp [pushBits]

private theorem sum_pushBits {n m : ℕ} (e : Fin n ↪ Fin m)
    (bits : Fin n → Bool) (a : Fin m → ℝ) :
    (∑ j, a j * boolToReal (pushBits e bits j)) =
      ∑ i, a (e i) * boolToReal (bits i) := by
  classical
  have himage : (∑ j ∈ Finset.univ.image e, a j * boolToReal (pushBits e bits j)) =
      ∑ i, a (e i) * boolToReal (bits i) := by
    rw [Finset.sum_image]
    · simp only [pushBits_apply]
    · exact fun _ _ _ _ h ↦ e.injective h
  rw [← himage]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  have hn : ∀ i, e i ≠ j := by simpa using hj
  simp [pushBits, hn, boolToReal]

private def restrictSlope {r s R S : ℕ} (u : Fin r ↪ Fin R)
    (v : Fin s ↪ Fin S) (a : Fin (R + S) → ℝ) : Fin (r + s) → ℝ :=
  Fin.addCases (fun i ↦ a (Fin.castAdd S (u i)))
    (fun j ↦ a (Fin.natAdd R (v j)))

private theorem restrict_affine {r s R S : ℕ} (u : Fin r ↪ Fin R)
    (v : Fin s ↪ Fin S) (a : Fin (R + S) → ℝ) (c : ℝ)
    (bits : Fin (r + s) → Bool) :
    affineValue c (restrictSlope u v a) bits = affineValue c a
      (Fin.addCases (pushBits u (fun i ↦ bits (Fin.castAdd s i)))
        (pushBits v (fun j ↦ bits (Fin.natAdd r j)))) := by
  simp only [affineValue, Fin.sum_univ_add, restrictSlope, Fin.addCases_left,
    Fin.addCases_right, sum_pushBits]

/-- Restricting either coordinate block sets every unused coordinate to zero.
It preserves the head count, strict slopes, and both full axis identities. -/
noncomputable def ReverseAxisData.restrict {r s R S H : ℕ}
    (L : ReverseAxisData R S H) (u : Fin r ↪ Fin R) (v : Fin s ↪ Fin S) :
    ReverseAxisData r s H where
  a₀ := L.a₀
  b₀ := L.b₀
  a := fun h ↦ restrictSlope u v (L.a h)
  b := fun h ↦ restrictSlope u v (L.b h)
  positive := by
    intro h bits
    rw [restrict_affine]
    exact L.positive h _
  negative := by
    intro h k
    refine Fin.addCases ?_ ?_ k <;> intro i
    · simpa only [restrictSlope, Fin.addCases_left] using
        L.negative h (Fin.castAdd S (u i))
    · simpa only [restrictSlope, Fin.addCases_right] using
        L.negative h (Fin.natAdd R (v i))
  zero_left := by
    intro w
    simp only [restrict_affine, Fin.addCases_left, Fin.addCases_right, pushBits_false]
    exact L.zero_left (pushBits v w)
  zero_right := by
    intro z
    simp only [restrict_affine, Fin.addCases_left, Fin.addCases_right, pushBits_false]
    exact L.zero_right (pushBits u z)

theorem ReverseAxisData.restrict_grid {r s R S H : ℕ}
    (L : ReverseAxisData R S H) (u : Fin r ↪ Fin R) (v : Fin s ↪ Fin S)
    (i : Fin r) (j : Fin s) :
    (L.restrict u v).score (localGrid i j) = L.score (localGrid (u i) (v j)) := by
  classical
  have hbits {a b : ℕ} (e : Fin a ↪ Fin b) (i : Fin a) :
      pushBits e (fun k ↦ decide (k = i)) = fun k ↦ decide (k = e i) := by
    funext k
    simp [pushBits, eq_comm]
  simp only [ReverseAxisData.score, ReverseAxisData.restrict, restrict_affine,
    localGrid, Fin.addCases_left, Fin.addCases_right, hbits]
  rfl

theorem HasReverseAxisCompiler.restrict {r s R S M : ℕ}
    (h : HasReverseAxisCompiler R S M) (u : Fin r ↪ Fin R) (v : Fin s ↪ Fin S) :
    HasReverseAxisCompiler r s M := by
  classical
  intro table
  let big : Fin R → Fin S → Bool := fun i j ↦
    decide (∃ a b, u a = i ∧ v b = j ∧ table a b = true)
  have hbig (i : Fin r) (j : Fin s) : big (u i) (v j) = table i j := by
    simp [big, u.injective.eq_iff, v.injective.eq_iff]
  obtain ⟨H, hH, L, hL⟩ := h big
  refine ⟨H, hH, L.restrict u v, ?_⟩
  intro i j
  rw [L.restrict_grid]
  simpa only [hbig] using hL (u i) (v j)

end HeadComplexity.AxisZeroGluing
