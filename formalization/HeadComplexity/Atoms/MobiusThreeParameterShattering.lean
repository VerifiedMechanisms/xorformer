import Mathlib.Tactic

set_option linter.style.header false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Exact finite witnesses in a separable reciprocal relaxation. No assertion
about worst-case attention-head complexity is made in this file. -/
namespace HeadComplexity.MobiusThreeParameterShattering

def scale : ℤ := 1000000000000

def poles : Fin 6 → Fin 3 → ℤ :=
  ![![233368000000000, 93580600000, 9252780000000],
    ![1687220000000, 1045810000000000, 7648300000000],
    ![136276000000, 1427700000000, 416615],
    ![4500140000000, 729847000, 72179000000000],
    ![12841100000, 41531700000000, 38629100000000],
    ![980608000000000, 306928000000, 194556000000000]]

def residues : Fin 6 → Fin 3 → ℤ :=
  ![![242688000000000, -92586300000, -17460000000],
    ![-185895000000, 620953000000000, -716991000000],
    ![-17154500000000, -80552700000, -14483100000],
    ![1249800000000, 886264000, -163429000000000],
    ![7383870000, -56696100000000, 72720100000000],
    ![-755264000000000, 97740300000, -161808000000000]]

def thresholds : Fin 6 → ℤ := ![119577000000, 446687000000, -74598800000000, -1587140000000, 518105000000, -1266160000000]

def witness : Fin 64 → Fin 3 → ℤ :=
  ![![46415900000, 3981070000, 3414550000000],
    ![7356420000, 541170000000, 11659100000000],
    ![11659100000000, 1165910000, 100000000],
    ![7356420000, 46415900000, 11659100000000],
    ![158489000000, 2154430000, 1000000000000],
    ![158489000000, 7356420000, 1000000000000],
    ![1000000000000, 2154430000, 1847850000000],
    ![158489000000, 46415900000, 11659100000000],
    ![46415900000, 100000000, 3414550000000],
    ![13593600000, 73564200000000, 73564200000000],
    ![11659100000000, 100000000, 100000000],
    ![100000000, 85769600000, 21544300000000],
    ![158489000000, 100000000, 1000000000000],
    ![158489000000, 73564200000000, 39810700000000],
    ![1000000000000, 100000000, 1847850000000],
    ![158489000000, 85769600000, 21544300000000],
    ![100000000, 2154430000, 100000000],
    ![100000000, 7356420000, 100000000],
    ![1847850000000, 1165910000, 100000000],
    ![1847850000000, 13593600000, 100000000],
    ![158489000000, 2154430000, 1165910000],
    ![158489000000, 7356420000, 1165910000],
    ![1847850000000, 1165910000, 341455000],
    ![292864000000, 21544300000000, 11659100000000],
    ![100000000, 100000000, 100000000],
    ![100000000, 39810700000000, 21544300000000],
    ![1847850000000, 100000000, 100000000],
    ![100000000, 6309570000000, 21544300000000],
    ![158489000000, 100000000, 1165910000],
    ![158489000000, 73564200000000, 21544300000000],
    ![1847850000000, 100000000, 341455000],
    ![158489000000, 39810700000000, 21544300000000],
    ![25118900000, 3981070000, 6309570000000],
    ![25118900000, 7356420000, 6309570000000],
    ![39810700000000, 1165910000, 100000000],
    ![7356420000, 13593600000, 11659100000000],
    ![158489000000, 3981070000, 6309570000000],
    ![158489000000, 7356420000, 6309570000000],
    ![292864000000, 3981070000, 6309570000000],
    ![158489000000, 13593600000, 11659100000000],
    ![25118900000, 100000000, 6309570000000],
    ![100000000, 73564200000000, 135936000000000],
    ![100000000, 100000000, 21544300000000],
    ![100000000, 7356420000, 21544300000000],
    ![158489000000, 100000000, 6309570000000],
    ![158489000000, 135936000000000, 135936000000000],
    ![158489000000, 100000000, 11659100000000],
    ![158489000000, 7356420000, 11659100000000],
    ![100000000, 3981070000, 6309570000000],
    ![100000000, 7356420000, 6309570000000],
    ![73564200000000, 25118900000, 100000000],
    ![3981070000, 13593600000, 11659100000000],
    ![2928640000000000, 135936000000000, 341455000],
    ![857696000000000, 135936000000000, 341455000],
    ![73564200000000, 25118900000, 341455000],
    ![135936000000000, 85769600000, 341455000],
    ![100000000, 100000000, 6309570000000],
    ![100000000, 7356420000, 11659100000000],
    ![3981070000, 100000000, 11659100000000],
    ![3981070000, 7356420000, 11659100000000],
    ![2928640000000000, 464159000000000, 39810700000000],
    ![251189000000000, 464159000000000, 73564200000000],
    ![2928640000000000, 135936000000000, 39810700000000],
    ![464159000000000, 135936000000000, 39810700000000]]

def labels (i : Fin 64) (q : Fin 6) : Bool :=
  decide (i.val / 2 ^ q.val % 2 = 1)

def cleared (x : Fin 3 → ℤ) (q : Fin 6) : ℤ :=
  let d := fun h => x h + poles q h
  scale * (residues q 0 * d 1 * d 2 + residues q 1 * d 0 * d 2 +
    residues q 2 * d 0 * d 1) - thresholds q * d 0 * d 1 * d 2

theorem poles_positive : ∀ q h, 0 < poles q h := by
  decide +kernel

theorem witnesses_positive : ∀ i h, 0 < witness i h := by
  decide +kernel

theorem labels_surjective : Function.Surjective labels := by
  decide +kernel

theorem cleared_signs : ∀ i q, cleared (witness i) q ≠ 0 ∧
    (0 < cleared (witness i) q ↔ labels i q = true) := by
  decide +kernel

noncomputable def test (x : Fin 3 → ℝ) (q : Fin 6) : ℝ :=
  (residues q 0 : ℝ) / (x 0 + poles q 0) +
  (residues q 1 : ℝ) / (x 1 + poles q 1) +
  (residues q 2 : ℝ) / (x 2 + poles q 2) - (thresholds q : ℝ) / scale

theorem test_cleared (x : Fin 3 → ℤ) (q : Fin 6)
    (hx : ∀ h, 0 < x h) :
    test (fun h => (x h : ℝ)) q =
    (cleared x q : ℝ) / ((scale : ℝ) *
      ((x 0 : ℝ) + poles q 0) * ((x 1 : ℝ) + poles q 1) *
      ((x 2 : ℝ) + poles q 2)) := by
  have hp (h : Fin 3) : 0 < (x h : ℝ) + poles q h := by
    exact_mod_cast add_pos (hx h) (poles_positive q h)
  have h0 := ne_of_gt (hp 0)
  have h1 := ne_of_gt (hp 1)
  have h2 := ne_of_gt (hp 2)
  simp only [test, cleared, Int.cast_sub, Int.cast_mul, Int.cast_add]
  norm_num only [scale, Int.cast_ofNat]
  field_simp

theorem witness_test_signs (i : Fin 64) (q : Fin 6) :
    test (fun h => (witness i h : ℝ)) q ≠ 0 ∧
      (0 < test (fun h => (witness i h : ℝ)) q ↔ labels i q = true) := by
  rw [test_cleared (witness i) q (witnesses_positive i)]
  have hp (h : Fin 3) : 0 < (witness i h : ℝ) + poles q h := by
    exact_mod_cast add_pos (witnesses_positive i h) (poles_positive q h)
  have hk : (0 : ℝ) < scale := by norm_num [scale]
  have hd := mul_pos (mul_pos (mul_pos hk (hp 0)) (hp 1)) (hp 2)
  constructor
  · exact div_ne_zero (by exact_mod_cast (cleared_signs i q).1) (ne_of_gt hd)
  · rw [div_pos_iff_of_pos_right hd]
    exact (by exact_mod_cast (cleared_signs i q).2)

/-- Six fixed separable reciprocal tests are shattered by three positive real
parameters. This refutes a proposed `2*H-1` bound for this relaxation. -/
theorem six_tests_shattered : ∀ ε : Fin 6 → Bool,
    ∃ x : Fin 3 → ℝ, (∀ h, 0 < x h) ∧ ∀ q,
      test x q ≠ 0 ∧ (0 < test x q ↔ ε q = true) := by
  intro ε
  obtain ⟨i, hi⟩ := labels_surjective ε
  refine ⟨fun h => (witness i h : ℝ), ?_, ?_⟩
  · intro h
    change (0 : ℝ) < (witness i h : ℝ)
    exact_mod_cast witnesses_positive i h
  · intro q
    simpa only [hi] using witness_test_signs i q

#print axioms six_tests_shattered

end HeadComplexity.MobiusThreeParameterShattering
