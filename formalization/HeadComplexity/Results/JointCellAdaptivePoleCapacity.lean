import HeadComplexity.Results.WarrenBound

set_option linter.style.header false

/-!
# Counting a sample-dependent shared-residue Cauchy dictionary

The pole pencil may vary between memory points, and each memory point has an
independent scalar token in each column. Residues are shared between points.
All these parameters, including point-bit biases, may be chosen after seeing
the complete label table. Clearing denominators gives an unconditional Warren
bound with the actual shared parameter count. This auxiliary family does not
change the original model or assert a lower bound for unrestricted heads.
-/

namespace HeadComplexity.AxisZeroGluing

open Finset MvPolynomial
open scoped BigOperators

abbrev JointCellAdaptivePoleParameter (M a q s : ℕ) :=
  ((Fin a × Fin q) ⊕ (Fin M × Fin q)) ⊕
    ((Fin M × Fin s) ⊕ (Fin M × Fin a))

abbrev JointCellAdaptivePoleInput (M a s : ℕ) := Fin M × Fin a × Fin s

theorem jointCell_card_adaptivePoleParameter (M a q s : ℕ) :
    Fintype.card (JointCellAdaptivePoleParameter M a q s) =
      a * q + M * (q + s + a) := by
  simp [JointCellAdaptivePoleParameter]
  ring

noncomputable def jointCellAdaptivePoleDen {M a q s : ℕ}
    (g : Fin M) (j : Fin s) (z : Fin q) :
    MvPolynomial (JointCellAdaptivePoleParameter M a q s) ℝ :=
  X (Sum.inl (Sum.inr (g, z))) - X (Sum.inr (Sum.inl (g, j)))

noncomputable def jointCellAdaptivePoleCleared {M a q s : ℕ}
    (x : JointCellAdaptivePoleInput M a s) :
    MvPolynomial (JointCellAdaptivePoleParameter M a q s) ℝ :=
  X (Sum.inr (Sum.inr (x.1, x.2.1))) * ∏ z, jointCellAdaptivePoleDen x.1 x.2.2 z +
    ∑ z, X (Sum.inl (Sum.inl (x.2.1, z))) *
      ∏ v ∈ Finset.univ.erase z, jointCellAdaptivePoleDen x.1 x.2.2 v

theorem jointCellAdaptivePoleDen_degree {M a q s : ℕ}
    (g : Fin M) (j : Fin s) (z : Fin q) :
    (jointCellAdaptivePoleDen (a := a) g j z).totalDegree ≤ 1 := by
  unfold jointCellAdaptivePoleDen
  exact (totalDegree_sub _ _).trans (by simp)

private theorem adaptivePole_product_degree {M a q s : ℕ}
    (g : Fin M) (j : Fin s) (t : Finset (Fin q)) :
    (∏ z ∈ t, jointCellAdaptivePoleDen (a := a) g j z).totalDegree ≤ t.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1
    (fun z _ ↦ jointCellAdaptivePoleDen_degree g j z)).trans ?_
  simp

theorem jointCellAdaptivePoleCleared_degree {M a q s : ℕ}
    (x : JointCellAdaptivePoleInput M a s) :
    (jointCellAdaptivePoleCleared (q := q) x).totalDegree ≤ q + 1 := by
  classical
  unfold jointCellAdaptivePoleCleared
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    have hp := adaptivePole_product_degree (a := a) (q := q) x.1 x.2.2 Finset.univ
    simp only [Finset.card_univ, Fintype.card_fin] at hp
    rw [totalDegree_X]
    omega
  · refine totalDegree_finsetSum_le fun z _ ↦ ?_
    refine (totalDegree_mul _ _).trans ?_
    have hp := adaptivePole_product_degree (a := a) x.1 x.2.2 (Finset.univ.erase z)
    rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ,
      Fintype.card_fin] at hp
    rw [totalDegree_X]
    omega

noncomputable def jointCellAdaptivePolePoint {M a q s : ℕ}
    (η : Fin a → Fin q → ℝ) (pole : Fin M → Fin q → ℝ)
    (token : Fin M → Fin s → ℝ) (bias : Fin M → Fin a → ℝ) :
    JointCellAdaptivePoleParameter M a q s → ℝ
  | Sum.inl (Sum.inl (b, z)) => η b z
  | Sum.inl (Sum.inr (g, z)) => pole g z
  | Sum.inr (Sum.inl (g, j)) => token g j
  | Sum.inr (Sum.inr (g, b)) => bias g b

theorem jointCellAdaptivePoleCleared_eval {M a q s : ℕ}
    (η : Fin a → Fin q → ℝ) (pole : Fin M → Fin q → ℝ)
    (token : Fin M → Fin s → ℝ) (bias : Fin M → Fin a → ℝ)
    (hden : ∀ g j z, pole g z - token g j ≠ 0)
    (x : JointCellAdaptivePoleInput M a s) :
    eval (jointCellAdaptivePolePoint η pole token bias)
        (jointCellAdaptivePoleCleared x) =
      (∏ z, (pole x.1 z - token x.1 x.2.2)) *
        (bias x.1 x.2.1 + ∑ z, η x.2.1 z / (pole x.1 z - token x.1 x.2.2)) := by
  classical
  simp only [jointCellAdaptivePoleCleared, jointCellAdaptivePoleDen, map_add,
    map_mul, map_prod, map_sum, map_sub, eval_X, jointCellAdaptivePolePoint]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [← Finset.mul_prod_erase Finset.univ
      (fun v ↦ pole x.1 v - token x.1 x.2.2) (Finset.mem_univ z)]
    field_simp [hden x.1 x.2.2 z]

theorem jointCellAdaptivePole_strictPattern {M a q s : ℕ}
    (f : JointCellAdaptivePoleInput M a s → Bool)
    (η : Fin a → Fin q → ℝ) (pole : Fin M → Fin q → ℝ)
    (token : Fin M → Fin s → ℝ) (bias : Fin M → Fin a → ℝ)
    (hden : ∀ g j z, 0 < pole g z - token g j)
    (hsign : ∀ x : JointCellAdaptivePoleInput M a s,
      if f x then 0 < bias x.1 x.2.1 +
          ∑ z, η x.2.1 z / (pole x.1 z - token x.1 x.2.2)
      else bias x.1 x.2.1 +
          ∑ z, η x.2.1 z / (pole x.1 z - token x.1 x.2.2) < 0) :
    StrictPolynomialSignPattern (jointCellAdaptivePoleCleared (q := q)) f := by
  refine ⟨jointCellAdaptivePolePoint η pole token bias, fun x ↦ ?_⟩
  rw [jointCellAdaptivePoleCleared_eval η pole token bias
    (fun g j z ↦ (hden g j z).ne') x]
  have hp : 0 < ∏ z, (pole x.1 z - token x.1 x.2.2) :=
    Finset.prod_pos fun z _ ↦ hden x.1 x.2.2 z
  have hs := hsign x
  split_ifs at hs ⊢
  · exact mul_pos hp hs
  · exact mul_neg_of_pos_of_neg hp hs

/-- All table parameters may be selected jointly after the labels are given. -/
def JointCellHasAdaptivePoleDecoder (M a q s : ℕ) : Prop :=
    ∀ f : JointCellAdaptivePoleInput M a s → Bool,
      ∃ (η : Fin a → Fin q → ℝ) (pole : Fin M → Fin q → ℝ)
        (token : Fin M → Fin s → ℝ) (bias : Fin M → Fin a → ℝ),
        (∀ g j z, 0 < pole g z - token g j) ∧
        ∀ x : JointCellAdaptivePoleInput M a s,
          if f x then 0 < bias x.1 x.2.1 +
              ∑ z, η x.2.1 z / (pole x.1 z - token x.1 x.2.2)
          else bias x.1 x.2.1 +
              ∑ z, η x.2.1 z / (pole x.1 z - token x.1 x.2.2) < 0

/-- Universal finite-sample decoding is constrained by the actual number of
shared residues, point poles, independent tokens, and point-bit biases. -/
theorem jointCell_adaptivePole_universal_capacity {M a q s : ℕ}
    (hp : 0 < a * q + M * (q + s + a))
    (hpN : a * q + M * (q + s + a) ≤ M * a * s)
    (hdecode : JointCellHasAdaptivePoleDecoder M a q s) :
    (2 : ℝ) ^ (M * a * s) ≤
      (4 * Real.exp 1 * (q + 1) * (M * a * s) /
        (a * q + M * (q + s + a))) ^ (a * q + M * (q + s + a)) := by
  classical
  have hfull : strictPolynomialSignPatterns
      (jointCellAdaptivePoleCleared (M := M) (a := a) (q := q) (s := s)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro f
    obtain ⟨η, pole, token, bias, hden, hsign⟩ := hdecode f
    exact jointCellAdaptivePole_strictPattern f η pole token bias hden hsign
  have hc : Fintype.card (JointCellAdaptivePoleInput M a s) = M * a * s := by
    simp [JointCellAdaptivePoleInput, Nat.mul_assoc]
  have hW := warrenStrictSignPatternBound (M * a * s) (q + 1)
    (a * q + M * (q + s + a)) (by omega) hp hpN
    (JointCellAdaptivePoleInput M a s) (JointCellAdaptivePoleParameter M a q s)
    jointCellAdaptivePoleCleared hc (jointCell_card_adaptivePoleParameter M a q s)
    jointCellAdaptivePoleCleared_degree
  rw [hfull] at hW
  simpa [Set.ncard_univ, Fintype.card_fun, hc] using hW

/-- Even dictionaries tailored to only `s` observed words have logarithmic
word length in this shared-residue class when poles and bits number at most
the columns and each pole has a memory point available. -/
theorem jointCell_adaptivePole_log_budget {M a q s l : ℕ}
    (hM : 0 < M) (hs : 0 < s) (ha : a ≤ s) (hq : q ≤ s) (hqM : q ≤ M)
    (hsl : s ≤ 2 ^ l) (hdecode : JointCellHasAdaptivePoleDecoder M a q s) :
    a ≤ 20 + 8 * l := by
  by_cases ha4 : a ≤ 4
  · omega
  have h4a : 4 ≤ a := by omega
  let P := a * q + M * (q + s + a)
  have hMs : 0 < M * s := Nat.mul_pos hM hs
  have hPlo : M * s ≤ P := by dsimp [P]; nlinarith
  have hPup : P ≤ 4 * (M * s) := by
    have h1 : a * q ≤ s * M := Nat.mul_le_mul ha hqM
    have h2 : M * (q + s + a) ≤ M * (3 * s) :=
      Nat.mul_le_mul_left M (by omega)
    dsimp [P]
    nlinarith
  have hP : 0 < P := lt_of_lt_of_le hMs hPlo
  have hPN : P ≤ M * a * s := by nlinarith
  have hcap := jointCell_adaptivePole_universal_capacity hP hPN hdecode
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hMsr : (0 : ℝ) < M * s := by exact_mod_cast hMs
  have hPlor : (M : ℝ) * s ≤ P := by exact_mod_cast hPlo
  have hPupper : (P : ℝ) ≤ 4 * ((M : ℝ) * s) := by exact_mod_cast hPup
  have har : (a : ℝ) ≤ s := by exact_mod_cast ha
  have hqr : (q : ℝ) ≤ s := by exact_mod_cast hq
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have harg :
      4 * Real.exp 1 * (q + 1) * ((M : ℝ) * a * s) / P ≤
        24 * (s : ℝ) ^ 2 := by
    apply (div_le_iff₀ hPr).mpr
    have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    have h1 : 4 * Real.exp 1 * (q + 1 : ℝ) ≤ 24 * s := by
      nlinarith [Real.exp_pos 1]
    have h2 := mul_le_mul_of_nonneg_right h1
      (show (0 : ℝ) ≤ M * a * s by positivity)
    have h3 := mul_le_mul_of_nonneg_left har
      (show (0 : ℝ) ≤ 24 * s * M * s by positivity)
    have h4 := mul_le_mul_of_nonneg_left hPlor
      (show (0 : ℝ) ≤ 24 * (s : ℝ) ^ 2 by positivity)
    nlinarith
  have hslr : (s : ℝ) ≤ (2 : ℝ) ^ l := by exact_mod_cast hsl
  have hbase : 24 * (s : ℝ) ^ 2 ≤ (2 : ℝ) ^ (5 + 2 * l) := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ s) hslr 2
    rw [show 5 + 2 * l = 5 + l * 2 by omega, pow_add, pow_mul]
    norm_num
    nlinarith [sq_nonneg ((2 : ℝ) ^ l)]
  have hpow1 := pow_le_pow_left₀
    (show (0 : ℝ) ≤ 4 * Real.exp 1 * (q + 1) * ((M : ℝ) * a * s) / P by positivity)
    (harg.trans hbase) P
  have hpow2 := pow_le_pow_right₀
    (show (1 : ℝ) ≤ (2 : ℝ) ^ (5 + 2 * l) from one_le_pow₀ (by norm_num)) hPup
  have hfinal : (2 : ℝ) ^ (M * a * s) ≤
      ((2 : ℝ) ^ (5 + 2 * l)) ^ (4 * (M * s)) := by
    apply hcap.trans
    simpa [P, Nat.cast_add, Nat.cast_mul] using hpow1.trans hpow2
  rw [← pow_mul] at hfinal
  have hnat := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hfinal
  nlinarith

theorem jointCell_adaptivePole_log2_limit {M a q s : ℕ}
    (hM : 0 < M) (hs : 0 < s) (ha : a ≤ s) (hq : q ≤ s) (hqM : q ≤ M)
    (hdecode : JointCellHasAdaptivePoleDecoder M a q s) :
    a ≤ 28 + 8 * s.log2 := by
  have h := jointCell_adaptivePole_log_budget hM hs ha hq hqM
    ((Nat.lt_log2_self (n := s)).le) hdecode
  omega

end HeadComplexity.AxisZeroGluing
