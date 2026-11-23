import HeadComplexity.Atoms.PositiveAffineRatio

set_option linter.style.header false

/-!
# Exact reciprocal histogram identities on the Boolean cube

Permutations with the same difference histogram give identical reciprocal
sums on an entire Boolean cube. The denominators below have strictly positive
coefficients and therefore are original admissible fractional atoms.
No conclusion about independent signs or worst-case head complexity is drawn.
-/

namespace HeadComplexity
namespace ReciprocalHistogram

open scoped BigOperators

/-- The multiset of pole differences for a permutation. -/
noncomputable def differences {H : ℕ} (poles : Fin H → ℝ)
    (π : Equiv.Perm (Fin H)) : Multiset ℝ :=
  (Finset.univ : Finset (Fin H)).val.map (fun h ↦ poles h - poles (π h))

theorem sum_eq_of_differences_eq {H : ℕ} (poles : Fin H → ℝ)
    (π τ : Equiv.Perm (Fin H)) (heq : differences poles π = differences poles τ)
    (f : ℝ → ℝ) :
    (∑ h, f (poles h - poles (π h))) = ∑ h, f (poles h - poles (τ h)) := by
  have heq' := congrArg (fun m : Multiset ℝ ↦ (m.map f).sum) heq
  simpa [differences, Multiset.map_map, Finset.sum, Function.comp_def] using heq'

/-- Seven possible difference states of three bits suffice for the identity.
There is no positivity assumption in this purely algebraic statement. -/
theorem reciprocal_sum_eq {H : ℕ} (poles : Fin H → ℝ)
    (π τ : Equiv.Perm (Fin H)) (heq : differences poles π = differences poles τ)
    (D : ℝ) (x y z : Bool) :
    (∑ h, 1 / (D + poles h * (boolToReal x - boolToReal y) +
      poles (π h) * (boolToReal y - boolToReal z))) =
    ∑ h, 1 / (D + poles h * (boolToReal x - boolToReal y) +
      poles (τ h) * (boolToReal y - boolToReal z)) := by
  have hpos := sum_eq_of_differences_eq poles π τ heq (fun t ↦ 1 / (D + t))
  have hneg := sum_eq_of_differences_eq poles π τ heq (fun t ↦ 1 / (D - t))
  have hperm (f : ℝ → ℝ) : (∑ h, f (poles (π h))) = ∑ h, f (poles (τ h)) :=
    (Equiv.sum_comp π (fun h ↦ f (poles h))).trans (Equiv.sum_comp τ (fun h ↦ f (poles h))).symm
  cases x <;> cases y <;> cases z <;> norm_num [boolToReal] <;>
    first
    | simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc, add_comm,
        add_left_comm, one_div] using hpos
    | simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc, add_comm,
        add_left_comm, one_div] using hneg
    | simpa only [one_div] using hperm (fun t ↦ 1 / (D + -t))
    | simpa only [one_div] using hperm (fun t ↦ 1 / (D + t))

/-- Strict positive coefficients for one triple and any filler coordinates. -/
noncomputable def slopes {H q : ℕ} (π : Equiv.Perm (Fin H))
    (b : Fin q → ℝ) (h : Fin H) : Fin (3 + q) → ℝ :=
  Fin.addCases ![(H : ℝ) + 1 + h, (H : ℝ) + 1 + (π h : ℝ) - h,
    (H : ℝ) + 1 - (π h : ℝ)] b

theorem slopes_pos {H q : ℕ} (π : Equiv.Perm (Fin H))
    (b : Fin q → ℝ) (hb : ∀ i, 0 < b i) (h : Fin H) (i : Fin (3 + q)) :
    0 < slopes π b h i := by
  have hh : (h : ℝ) < H := by exact_mod_cast h.isLt
  have hp : (π h : ℝ) < H := by exact_mod_cast (π h).isLt
  have hh0 : (0 : ℝ) ≤ h := by positivity
  have hp0 : (0 : ℝ) ≤ π h := by positivity
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · fin_cases j <;> simp [slopes] <;> linarith
  · simpa [slopes] using hb j

/-- Each reciprocal in the histogram family is an admissible atom. -/
noncomputable def atom {H q : ℕ} (π : Equiv.Perm (Fin H))
    (b : Fin q → ℝ) (hb : ∀ i, 0 < b i) (h : Fin H) : FracAtom (3 + q) :=
  FracAtom.ofPositiveAffineRatio 1 (fun _ ↦ 0) 1 (slopes π b h)
    (by norm_num) (slopes_pos π b hb h)

theorem atom_eval {H q : ℕ} (π : Equiv.Perm (Fin H))
    (b : Fin q → ℝ) (hb : ∀ i, 0 < b i) (h : Fin H)
    (x : Fin 3 → Bool) (y : Fin q → Bool) :
    (atom π b hb h).eval (Fin.addCases x y) =
      1 / (1 + ((H : ℝ) + 1) * (boolToReal (x 0) + boolToReal (x 1) +
        boolToReal (x 2)) + (∑ i, b i * boolToReal (y i)) +
        (h : ℝ) * (boolToReal (x 0) - boolToReal (x 1)) +
        (π h : ℝ) * (boolToReal (x 1) - boolToReal (x 2))) := by
  rw [atom, FracAtom.ofPositiveAffineRatio_eval]
  simp only [affineValue, slopes, Fin.sum_univ_add, Fin.addCases_left,
    Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  simp [Fin.sum_univ_succ]
  ring

/-- The full-cube identity holds for actual atoms, with unchanged dimension. -/
theorem atoms_sum_eq {H q : ℕ} (π τ : Equiv.Perm (Fin H))
    (heq : differences (fun h : Fin H ↦ (h : ℝ)) π =
      differences (fun h : Fin H ↦ (h : ℝ)) τ)
    (b : Fin q → ℝ) (hb : ∀ i, 0 < b i) (bits : Fin (3 + q) → Bool) :
    (∑ h, (atom π b hb h).eval bits) = ∑ h, (atom τ b hb h).eval bits := by
  let x : Fin 3 → Bool := fun i ↦ bits (Fin.castAdd q i)
  let y : Fin q → Bool := fun i ↦ bits (Fin.natAdd 3 i)
  have hbits : bits = Fin.addCases x y := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp [x, y]
  rw [hbits]
  simp_rw [atom_eval]
  exact reciprocal_sum_eq (fun h ↦ (h : ℝ)) π τ heq _ (x 0) (x 1) (x 2)

/-- The two adjacent swaps already give a nontrivial three-head identity. -/
theorem adjacent_swaps_differences :
    differences (fun h : Fin 3 ↦ (h : ℝ)) (Equiv.swap 0 1) =
      differences (fun h : Fin 3 ↦ (h : ℝ)) (Equiv.swap 1 2) := by
  norm_num [differences, Fin.univ_succ, Equiv.swap_apply_def]
  simp only [← Multiset.singleton_add]
  ac_rfl

/-- An unconditional exact equality between two concrete admissible families. -/
theorem adjacent_swaps_atoms_sum_eq {q : ℕ}
    (b : Fin q → ℝ) (hb : ∀ i, 0 < b i) (bits : Fin (3 + q) → Bool) :
    (∑ h : Fin 3, (atom (Equiv.swap 0 1) b hb h).eval bits) =
      ∑ h : Fin 3, (atom (Equiv.swap 1 2) b hb h).eval bits :=
  atoms_sum_eq _ _ adjacent_swaps_differences b hb bits

end ReciprocalHistogram
end HeadComplexity
