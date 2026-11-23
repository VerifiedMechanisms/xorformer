import Mathlib.Tactic

set_option linter.style.header false

/-! Exact algebra for divergence of normalized denominator energy under
two-head cancellation. The differential interpretation is in the companion
writeup. This file asserts no asymptotic head lower bound. -/
namespace HeadComplexity.CancellationEnergy
noncomputable section

def s0 (t : ℝ) : ℝ := t / (4 - 2*t)
def s1 (t : ℝ) : ℝ := -t / (16 - 4*t)
def s2 (t : ℝ) : ℝ := -t / (16 + 4*t)
def s3 (t : ℝ) : ℝ := t / (36 + 6*t)
def normSq (t : ℝ) : ℝ := (s0 t)^2 + (s1 t)^2 + (s2 t)^2 + (s3 t)^2
def gram (t : ℝ) : ℝ := normSq t * ((1/8 : ℝ)^2 + (1/18 : ℝ)^2) -
  (s1 t / 8 + s3 t / 18)^2
def angularEnergy (t : ℝ) : ℝ := gram t / (normSq t)^2

theorem ratio_difference (t A B D : ℝ) (hD : D ≠ 0) (hE : D + t * B ≠ 0) :
    A/D - A/(D+t*B) = t*A*B/(D*(D+t*B)) := by
  field_simp
  ring

def bit (x : Bool) : ℝ := if x then 1 else 0
def firstHead (x y : Bool) : ℝ := (bit x-1/2)/(1+bit x+bit y)
def secondHead (t : ℝ) (x y : Bool) : ℝ :=
  -(bit x-1/2)/(1+bit x+bit y+t*(bit y-1/2))

theorem denominator_positive (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (x y : Bool) :
    0 < 1+bit x+bit y+t*(bit y-1/2) := by
  cases x <;> cases y <;> norm_num [bit] <;> linarith

theorem table_values (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    firstHead false false + secondHead t false false = s0 t ∧
    firstHead true false + secondHead t true false = s1 t ∧
    firstHead false true + secondHead t false true = s2 t ∧
    firstHead true true + secondHead t true true = s3 t := by
  have h0 : 4-2*t ≠ 0 := by linarith
  have h1 : 16-4*t ≠ 0 := by linarith
  have h2 : 16+4*t ≠ 0 := by linarith
  have h3 : 36+6*t ≠ 0 := by linarith
  have he0 : 1-t/2 ≠ 0 := by linarith
  have he1 : 2-t/2 ≠ 0 := by linarith
  have he2 : 2+t/2 ≠ 0 := by linarith
  have he3 : 3+t/2 ≠ 0 := by linarith
  have hp2 : 2-t ≠ 0 := by linarith
  have hp4 : 4-t ≠ 0 := by linarith
  have hf (x y : Bool) : firstHead x y + secondHead t x y =
      t*(bit x-1/2)*(bit y-1/2)/
        ((1+bit x+bit y)*(1+bit x+bit y+t*(bit y-1/2))) := by
    have hd : 1+bit x+bit y ≠ 0 := by
      cases x <;> cases y <;> norm_num [bit]
    have he := ne_of_gt (denominator_positive t ht ht1 x y)
    simpa only [firstHead, secondHead, neg_div, sub_eq_add_neg] using
      ratio_difference t (bit x-1/2) (bit y-1/2) (1+bit x+bit y) hd he
  rw [hf, hf, hf, hf]
  norm_num [bit, s0, s1, s2, s3]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_nf <;>
    field_simp (disch := (first | positivity | linarith)) <;> ring

theorem four_signs (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    0 < s0 t ∧ s1 t < 0 ∧ s2 t < 0 ∧ 0 < s3 t := by
  dsimp [s0, s1, s2, s3]
  refine ⟨div_pos ht (by linarith), ?_, ?_, div_pos ht (by linarith)⟩
  · exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  · exact div_neg_of_neg_of_pos (by linarith) (by linarith)

theorem no_affine_separator (c a b : ℝ) :
    ¬ (0 < c ∧ c+a < 0 ∧ c+b < 0 ∧ 0 < c+a+b) := by
  rintro ⟨h0,h1,h2,h3⟩
  linarith

theorem square_minor_identity (v0 v1 v2 v3 : ℝ) :
    (v0^2+v1^2+v2^2+v3^2)*((1/8 : ℝ)^2+(1/18 : ℝ)^2) -
      (v1/8+v3/18)^2 =
    (v0/8)^2+(v0/18)^2+(v2/8)^2+(v1/18-v3/8)^2+(v2/18)^2 := by
  ring

theorem coordinate_bounds (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    t/4 ≤ s0 t ∧ s0 t ≤ t/2 ∧
    -(t/2) ≤ s1 t ∧ s1 t ≤ 0 ∧
    -(t/2) ≤ s2 t ∧ s2 t ≤ 0 ∧
    0 ≤ s3 t ∧ s3 t ≤ t/2 := by
  have h0 : 0 < 4-2*t := by linarith
  have h1 : 0 < 16-4*t := by linarith
  have h2 : 0 < 16+4*t := by linarith
  have h3 : 0 < 36+6*t := by linarith
  dsimp [s0, s1, s2, s3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ h0).mpr
    nlinarith [sq_nonneg t]
  · apply (div_le_iff₀ h0).mpr
    nlinarith [mul_nonneg (le_of_lt ht) (sub_nonneg.mpr ht1)]
  · apply (le_div_iff₀ h1).mpr
    nlinarith [mul_nonneg (le_of_lt ht) (sub_nonneg.mpr ht1)]
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) h1.le
  · apply (le_div_iff₀ h2).mpr
    nlinarith [sq_nonneg t]
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
  · exact div_nonneg ht.le h3.le
  · apply (div_le_iff₀ h3).mpr
    nlinarith [sq_nonneg t]

theorem normSq_bounds (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    0 < normSq t ∧ normSq t ≤ t^2 := by
  obtain ⟨h0l,h0u,h1l,h1u,h2l,h2u,h3l,h3u⟩ := coordinate_bounds t ht ht1
  have h0p : 0 < s0 t := by linarith
  have h0s : (s0 t)^2 ≤ (t/2)^2 := by nlinarith
  have h1s : (s1 t)^2 ≤ (t/2)^2 := by nlinarith
  have h2s : (s2 t)^2 ≤ (t/2)^2 := by nlinarith
  have h3s : (s3 t)^2 ≤ (t/2)^2 := by nlinarith
  dsimp [normSq]
  constructor
  · positivity
  · nlinarith

theorem gram_lower (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    t^2/1024 ≤ gram t := by
  have h0 := (coordinate_bounds t ht ht1).1
  have h0p : 0 < s0 t := by linarith
  have hid := square_minor_identity (s0 t) (s1 t) (s2 t) (s3 t)
  change _ ≤ ((s0 t)^2+(s1 t)^2+(s2 t)^2+(s3 t)^2) *
    ((1/8 : ℝ)^2+(1/18 : ℝ)^2) - (s1 t/8+s3 t/18)^2
  rw [hid]
  nlinarith [sq_nonneg (s0 t/18), sq_nonneg (s2 t/8),
    sq_nonneg (s1 t/18-s3 t/8), sq_nonneg (s2 t/18)]

theorem angularEnergy_lower (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    1/(1024*t^2) ≤ angularEnergy t := by
  obtain ⟨hGp,hGu⟩ := normSq_bounds t ht ht1
  have hgram := gram_lower t ht ht1
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hG2 : 0 < (normSq t)^2 := sq_pos_of_pos hGp
  have hG4 : (normSq t)^2 ≤ (t^2)^2 := by nlinarith
  dsimp [angularEnergy]
  apply (div_le_div_iff₀ (by positivity : 0 < 1024*t^2) hG2).mpr
  nlinarith [mul_nonneg (by positivity : 0 ≤ t^2) (sub_nonneg.mpr hgram)]

theorem angularEnergy_unbounded (C : ℝ) (hC : 0 ≤ C) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ C < angularEnergy t := by
  let t : ℝ := 1/(1024*(C+1))
  have hd : 0 < 1024*(C+1) := by positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ hd).mpr
    linarith
  refine ⟨t, ht, ht1, lt_of_lt_of_le ?_ (angularEnergy_lower t ht ht1)⟩
  have hid : 1/(1024*t^2) = 1024*(C+1)^2 := by
    dsimp [t]
    field_simp
  rw [hid]
  nlinarith [sq_nonneg C]

theorem first_block_energy_dominates (v w : ℝ) :
    v^2 ≤ 2*v^2+2*v*w+2*w^2 := by
  nlinarith [sq_nonneg (v+w), sq_nonneg w]

end
end HeadComplexity.CancellationEnergy
