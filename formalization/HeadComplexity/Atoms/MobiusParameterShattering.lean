import Mathlib.Tactic

set_option linter.style.header false

/-! A finite obstruction to counting sign tests by the number of positive
parameters alone. This is a separable reciprocal relaxation, not a theorem
about the attention model's asymptotic head complexity. -/
namespace HeadComplexity.MobiusParameterShattering

noncomputable def test (x y : ℝ) : Fin 3 → ℝ :=
  ![1 / (x + 1) - 1 / (y + 1),
    -8 / (x + 1) + 15 / (y + 2) - 1,
    1 / 3 - 1 / (x + 1)]

noncomputable def witness : Fin 8 → ℝ × ℝ :=
  ![(1/2, 2/5), (1/2, 1), (1/2, 1/4), (3/2, 31/20),
    (4, 39/10), (4, 5), (4, 1), (5/2, 51/20)]

def labels : Fin 8 → Fin 3 → Bool :=
  ![![false, false, false], ![true, false, false],
    ![false, true, false], ![true, true, false],
    ![false, false, true], ![true, false, true],
    ![false, true, true], ![true, true, true]]

theorem labels_surjective : Function.Surjective labels := by
  decide +kernel

theorem witnesses_positive : ∀ i, 0 < (witness i).1 ∧ 0 < (witness i).2 := by
  intro i
  fin_cases i <;> norm_num [witness]

theorem witness_signs : ∀ i j,
    test (witness i).1 (witness i).2 j ≠ 0 ∧
      (0 < test (witness i).1 (witness i).2 j ↔ labels i j = true) := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [test, witness, labels]

/-- Three fixed reciprocal predicates realize every strict sign vector while
only two positive real parameters vary. -/
theorem three_tests_shattered : ∀ ε : Fin 3 → Bool,
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ ∀ j,
      test x y j ≠ 0 ∧ (0 < test x y j ↔ ε j = true) := by
  intro ε
  obtain ⟨i, hi⟩ := labels_surjective ε
  refine ⟨(witness i).1, (witness i).2,
    (witnesses_positive i).1, (witnesses_positive i).2, ?_⟩
  simpa only [hi] using witness_signs i

end HeadComplexity.MobiusParameterShattering
