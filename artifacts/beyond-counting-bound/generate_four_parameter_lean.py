"""Generate the exact nine-test reciprocal certificate on four parameters."""
from fractions import Fraction as F
import json
from pathlib import Path

root=Path(__file__).resolve().parent
r=json.loads((root/'separable-mobius/n4-m9-step-exact.json').read_text())
assert r['patterns']==512 and r['queries']==9 and r['heads']==4
def vec(row):return '!['+', '.join(map(str,row))+']'
def mat(rows):return '!['+',\n    '.join(vec(row) for row in rows)+']'
cuts=[F(x)*2 for x in r['thresholds']]
assert all(x.denominator==1 for x in cuts)
text='''import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.header false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

/-! An exact finite certificate for a separable reciprocal relaxation.
The 512 witnesses are checked by kernel reduction. No head lower bound follows.
-/
namespace HeadComplexity.MobiusFourParameterShattering

def scale : ℤ := 2

'''
text+='def poles : Fin 9 → Fin 4 → ℤ :=\n  '+mat(r['poles'])+'\n\n'
text+='def residues : Fin 9 → Fin 4 → ℤ :=\n  '+mat(r['residuals'])+'\n\n'
text+='def thresholds : Fin 9 → ℤ := '+vec([x.numerator for x in cuts])+'\n\n'
def cut(value):
    exponent=0
    while value>1:
        assert value%257==0
        value//=257;exponent+=1
    assert exponent%2==1
    return (exponent-1)//2
text+='def cutsData : Array (Fin 4 → ℕ) :=\n  #'+mat([[cut(x) for x in r['witnesses'][str(i)]] for i in range(512)])[1:]+'\n\n'
text+='def cuts (i : Fin 512) : Fin 4 → ℕ :=\n  cutsData[i.val]\'(by change i.val < 512; exact i.isLt)\n\n'
text+='def witness (i : Fin 512) (h : Fin 4) : ℤ := (257 : ℤ) ^ (2 * cuts i h + 1)\n\n'
text+='''def labels (i : Fin 512) (q : Fin 9) : Bool :=
  decide (i.val / 2 ^ q.val % 2 = 1)

def cleared (x : Fin 4 → ℤ) (q : Fin 9) : ℤ :=
  let d := fun h => x h + poles q h
  scale * (residues q 0 * d 1 * d 2 * d 3 +
    residues q 1 * d 0 * d 2 * d 3 +
    residues q 2 * d 0 * d 1 * d 3 +
    residues q 3 * d 0 * d 1 * d 2) - thresholds q * d 0 * d 1 * d 2 * d 3

#check witness

theorem poles_positive : ∀ q h, 0 < poles q h := by
  decide +kernel

#check poles_positive

theorem witnesses_positive : ∀ i h, 0 < witness i h := by
  intro i h
  exact pow_pos (by norm_num : (0 : ℤ) < 257) _

#check witnesses_positive

theorem labels_surjective : Function.Surjective labels := by
  intro epsilon
  let f : Fin 9 → Fin 2 := fun q => finTwoEquiv.symm (epsilon q)
  let i : Fin 512 := finFunctionFinEquiv f
  refine ⟨i, ?_⟩
  funext q
  have h := congrArg (fun g : Fin 9 → Fin 2 => (g q).val)
    (finFunctionFinEquiv.symm_apply_apply f)
  change i.val / 2 ^ q.val % 2 = (f q).val at h
  unfold labels
  rw [h]
  cases he : epsilon q <;> simp [f, he, finTwoEquiv]

#check labels_surjective

def index (block : Fin 32) (offset : Fin 16) : Fin 512 :=
  ⟨block.val * 16 + offset.val, by omega⟩

theorem checked_0 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 0 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 0 s)) q ↔ labels (index 0 s) q = true) := by
  decide +kernel

theorem checked_1 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 1 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 1 s)) q ↔ labels (index 1 s) q = true) := by
  decide +kernel

theorem checked_2 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 2 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 2 s)) q ↔ labels (index 2 s) q = true) := by
  decide +kernel

theorem checked_3 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 3 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 3 s)) q ↔ labels (index 3 s) q = true) := by
  decide +kernel

theorem checked_4 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 4 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 4 s)) q ↔ labels (index 4 s) q = true) := by
  decide +kernel

theorem checked_5 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 5 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 5 s)) q ↔ labels (index 5 s) q = true) := by
  decide +kernel

theorem checked_6 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 6 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 6 s)) q ↔ labels (index 6 s) q = true) := by
  decide +kernel

theorem checked_7 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 7 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 7 s)) q ↔ labels (index 7 s) q = true) := by
  decide +kernel

theorem checked_8 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 8 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 8 s)) q ↔ labels (index 8 s) q = true) := by
  decide +kernel

theorem checked_9 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 9 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 9 s)) q ↔ labels (index 9 s) q = true) := by
  decide +kernel

theorem checked_10 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 10 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 10 s)) q ↔ labels (index 10 s) q = true) := by
  decide +kernel

theorem checked_11 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 11 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 11 s)) q ↔ labels (index 11 s) q = true) := by
  decide +kernel

theorem checked_12 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 12 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 12 s)) q ↔ labels (index 12 s) q = true) := by
  decide +kernel

theorem checked_13 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 13 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 13 s)) q ↔ labels (index 13 s) q = true) := by
  decide +kernel

theorem checked_14 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 14 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 14 s)) q ↔ labels (index 14 s) q = true) := by
  decide +kernel

theorem checked_15 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 15 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 15 s)) q ↔ labels (index 15 s) q = true) := by
  decide +kernel

theorem checked_16 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 16 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 16 s)) q ↔ labels (index 16 s) q = true) := by
  decide +kernel

theorem checked_17 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 17 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 17 s)) q ↔ labels (index 17 s) q = true) := by
  decide +kernel

theorem checked_18 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 18 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 18 s)) q ↔ labels (index 18 s) q = true) := by
  decide +kernel

theorem checked_19 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 19 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 19 s)) q ↔ labels (index 19 s) q = true) := by
  decide +kernel

theorem checked_20 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 20 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 20 s)) q ↔ labels (index 20 s) q = true) := by
  decide +kernel

theorem checked_21 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 21 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 21 s)) q ↔ labels (index 21 s) q = true) := by
  decide +kernel

theorem checked_22 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 22 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 22 s)) q ↔ labels (index 22 s) q = true) := by
  decide +kernel

theorem checked_23 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 23 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 23 s)) q ↔ labels (index 23 s) q = true) := by
  decide +kernel

theorem checked_24 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 24 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 24 s)) q ↔ labels (index 24 s) q = true) := by
  decide +kernel

theorem checked_25 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 25 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 25 s)) q ↔ labels (index 25 s) q = true) := by
  decide +kernel

theorem checked_26 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 26 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 26 s)) q ↔ labels (index 26 s) q = true) := by
  decide +kernel

theorem checked_27 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 27 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 27 s)) q ↔ labels (index 27 s) q = true) := by
  decide +kernel

theorem checked_28 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 28 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 28 s)) q ↔ labels (index 28 s) q = true) := by
  decide +kernel

theorem checked_29 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 29 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 29 s)) q ↔ labels (index 29 s) q = true) := by
  decide +kernel

theorem checked_30 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 30 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 30 s)) q ↔ labels (index 30 s) q = true) := by
  decide +kernel

theorem checked_31 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 31 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 31 s)) q ↔ labels (index 31 s) q = true) := by
  decide +kernel

theorem cleared_signs : ∀ i q, cleared (witness i) q ≠ 0 ∧
    (0 < cleared (witness i) q ↔ labels i q = true) := by
  have chunks (b : Fin 32) : ∀ s : Fin 16, ∀ q : Fin 9,
      cleared (witness (index b s)) q ≠ 0 ∧
      (0 < cleared (witness (index b s)) q ↔ labels (index b s) q = true) := by
    fin_cases b
    · exact checked_0
    · exact checked_1
    · exact checked_2
    · exact checked_3
    · exact checked_4
    · exact checked_5
    · exact checked_6
    · exact checked_7
    · exact checked_8
    · exact checked_9
    · exact checked_10
    · exact checked_11
    · exact checked_12
    · exact checked_13
    · exact checked_14
    · exact checked_15
    · exact checked_16
    · exact checked_17
    · exact checked_18
    · exact checked_19
    · exact checked_20
    · exact checked_21
    · exact checked_22
    · exact checked_23
    · exact checked_24
    · exact checked_25
    · exact checked_26
    · exact checked_27
    · exact checked_28
    · exact checked_29
    · exact checked_30
    · exact checked_31
  intro i q
  let b : Fin 32 := ⟨i.val / 16, by omega⟩
  let s : Fin 16 := ⟨i.val % 16, by omega⟩
  have hi : index b s = i := by
    apply Fin.ext
    dsimp [index, b, s]
    omega
  simpa only [hi] using chunks b s q

#check cleared_signs

noncomputable def test (x : Fin 4 → ℝ) (q : Fin 9) : ℝ :=
  (residues q 0 : ℝ) / (x 0 + poles q 0) +
  (residues q 1 : ℝ) / (x 1 + poles q 1) +
  (residues q 2 : ℝ) / (x 2 + poles q 2) +
  (residues q 3 : ℝ) / (x 3 + poles q 3) - (thresholds q : ℝ) / scale

theorem test_cleared (x : Fin 4 → ℤ) (q : Fin 9)
    (hx : ∀ h, 0 < x h) :
    test (fun h => (x h : ℝ)) q =
    (cleared x q : ℝ) / ((scale : ℝ) *
      ((x 0 : ℝ) + poles q 0) * ((x 1 : ℝ) + poles q 1) *
      ((x 2 : ℝ) + poles q 2) * ((x 3 : ℝ) + poles q 3)) := by
  have hp (h : Fin 4) : 0 < (x h : ℝ) + poles q h := by
    exact_mod_cast add_pos (hx h) (poles_positive q h)
  have h0 := ne_of_gt (hp 0)
  have h1 := ne_of_gt (hp 1)
  have h2 := ne_of_gt (hp 2)
  have h3 := ne_of_gt (hp 3)
  simp only [test, cleared, Int.cast_sub, Int.cast_mul, Int.cast_add]
  norm_num only [scale, Int.cast_ofNat]
  field_simp

theorem witness_test_signs (i : Fin 512) (q : Fin 9) :
    test (fun h => (witness i h : ℝ)) q ≠ 0 ∧
      (0 < test (fun h => (witness i h : ℝ)) q ↔ labels i q = true) := by
  rw [test_cleared (witness i) q (witnesses_positive i)]
  have hp (h : Fin 4) : 0 < (witness i h : ℝ) + poles q h := by
    exact_mod_cast add_pos (witnesses_positive i h) (poles_positive q h)
  have hk : (0 : ℝ) < scale := by norm_num [scale]
  have hd := mul_pos (mul_pos (mul_pos (mul_pos hk (hp 0)) (hp 1)) (hp 2)) (hp 3)
  constructor
  · exact div_ne_zero (by exact_mod_cast (cleared_signs i q).1) (ne_of_gt hd)
  · rw [div_pos_iff_of_pos_right hd]
    exact (by exact_mod_cast (cleared_signs i q).2)

/-- Nine fixed reciprocal tests on four positive parameters realize every label
vector. In particular a universal bound of twice the number of parameters fails
for this freely chosen query relaxation. -/
theorem nine_tests_shattered : ∀ ε : Fin 9 → Bool,
    ∃ x : Fin 4 → ℝ, (∀ h, 0 < x h) ∧ ∀ q,
      test x q ≠ 0 ∧ (0 < test x q ↔ ε q = true) := by
  intro ε
  obtain ⟨i, hi⟩ := labels_surjective ε
  refine ⟨fun h => (witness i h : ℝ), ?_, ?_⟩
  · intro h
    change (0 : ℝ) < (witness i h : ℝ)
    exact_mod_cast witnesses_positive i h
  · intro q
    simpa only [hi] using witness_test_signs i q

#print axioms nine_tests_shattered

end HeadComplexity.MobiusFourParameterShattering
'''
p=Path('formalization/HeadComplexity/Atoms/MobiusFourParameterShattering.lean')
p.write_text(text)
print(json.dumps({'file':str(p),'bytes':p.stat().st_size}))
