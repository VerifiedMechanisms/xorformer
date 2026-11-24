import HeadComplexity.Results.AffinePlaneIncidence

set_option linter.style.header false

/-!
# Affine-plane selectors on larger product domains

The existing affine-plane compiler may choose arbitrary line selectors on a
one-hot row set. On a product row set, restrictions of affine numerators are
additive across the two factors. If every nonvertical line selector remains
additive and the field has three distinct slopes, the memory-point assignment
must depend on only one factor. Thus that direct enlargement cannot use both
row coordinates. This is an obstruction to this selector architecture, not a
lower bound for general attention scores.
-/

namespace HeadComplexity
namespace LargeDomain

variable {F α β : Type*} [Field F]

/-- The intercept of the nonvertical line of slope `a` through `p`. -/
def lineCoordinate (a : F) (p : F × F) : F := p.2 - a * p.1

theorem eq_of_two_lineCoordinates {a b : F} (hab : a ≠ b)
    {p q : F × F} (ha : lineCoordinate a p = lineCoordinate a q)
    (hb : lineCoordinate b p = lineCoordinate b q) : p = q := by
  unfold lineCoordinate at ha hb
  have hx : p.1 = q.1 := by
    have hprod : (a - b) * (p.1 - q.1) = 0 := by
      linear_combination hb - ha
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hab))
  apply Prod.ext hx
  linear_combination ha + a * hx

/-- Three directions distinguish a corner from both adjacent corners. -/
theorem corner_eq_of_three_lineCoordinates {a b c : F}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {p q r : F × F}
    (ha : lineCoordinate a p = lineCoordinate a q ∨
      lineCoordinate a p = lineCoordinate a r)
    (hb : lineCoordinate b p = lineCoordinate b q ∨
      lineCoordinate b p = lineCoordinate b r)
    (hc : lineCoordinate c p = lineCoordinate c q ∨
      lineCoordinate c p = lineCoordinate c r) : p = q ∨ p = r := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact Or.inl (eq_of_two_lineCoordinates hab ha hb)
  · exact Or.inl (eq_of_two_lineCoordinates hab ha hb)
  · exact Or.inl (eq_of_two_lineCoordinates hac ha hc)
  · exact Or.inr (eq_of_two_lineCoordinates hbc hb hc)
  · exact Or.inl (eq_of_two_lineCoordinates hbc hb hc)
  · exact Or.inr (eq_of_two_lineCoordinates hac ha hc)
  · exact Or.inr (eq_of_two_lineCoordinates hab ha hb)
  · exact Or.inr (eq_of_two_lineCoordinates hab ha hb)

/-- The selector values permitted by an affine numerator on a product grid. -/
def AdditiveLineSelectors (g : α → β → F × F) : Prop := by
  classical
  exact ∀ a b : F, ∃ (constant : ℝ) (left : α → ℝ) (right : β → ℝ),
    ∀ x y, (if lineCoordinate a (g x y) = b then (1 : ℝ) else 0) =
      constant + left x + right y

theorem lineCoordinate_corner_or_of_additive_selectors
    {g : α → β → F × F} (hg : AdditiveLineSelectors g)
    (a : F) (x x' : α) (y y' : β) :
    lineCoordinate a (g x y) = lineCoordinate a (g x y') ∨
      lineCoordinate a (g x y) = lineCoordinate a (g x' y) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨constant, left, right, h⟩ := hg a (lineCoordinate a (g x y))
  have hrect :
      (if lineCoordinate a (g x y) = lineCoordinate a (g x y) then (1 : ℝ) else 0) +
        (if lineCoordinate a (g x' y') = lineCoordinate a (g x y) then (1 : ℝ) else 0) =
      (if lineCoordinate a (g x y') = lineCoordinate a (g x y) then (1 : ℝ) else 0) +
        (if lineCoordinate a (g x' y) = lineCoordinate a (g x y) then (1 : ℝ) else 0) := by
    rw [h, h, h, h]
    ring
  simp only [ite_true, Ne.symm hn.1, Ne.symm hn.2, ite_false, add_zero] at hrect
  split_ifs at hrect <;> norm_num at hrect

/-- A function with no corner varying in both directions uses at most one axis. -/
theorem depends_on_one_axis_of_corner_property {γ : Type*}
    [Nonempty α] [Nonempty β] (g : α → β → γ)
    (hg : ∀ x x' y y', g x y = g x y' ∨ g x y = g x' y) :
    (∃ u : α → γ, ∀ x y, g x y = u x) ∨
      (∃ v : β → γ, ∀ x y, g x y = v y) := by
  classical
  by_cases hrow : ∀ x y y', g x y = g x y'
  · let y₀ : β := Classical.choice inferInstance
    exact Or.inl ⟨fun x ↦ g x y₀, fun x y ↦ hrow x y y₀⟩
  · push Not at hrow
    obtain ⟨x₀, y₀, y₁, hne⟩ := hrow
    refine Or.inr ⟨g x₀, ?_⟩
    intro x y
    by_cases hy : g x₀ y = g x₀ y₀
    · have hyy : g x₀ y ≠ g x₀ y₁ := by simpa only [hy] using hne
      exact ((hg x₀ x y y₁).resolve_left hyy).symm
    · exact ((hg x₀ x y y₀).resolve_left hy).symm

/-- Directly lifting all affine-plane selectors to a product row domain forces
the assignment of memory points to ignore one factor, whenever three distinct
slopes are available. Arbitrary rational combinations are not restricted here. -/
theorem additive_line_selectors_depend_on_one_axis
    [Nonempty α] [Nonempty β] {g : α → β → F × F}
    (hg : AdditiveLineSelectors g) {a b c : F}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∃ u : α → F × F, ∀ x y, g x y = u x) ∨
      (∃ v : β → F × F, ∀ x y, g x y = v y) := by
  apply depends_on_one_axis_of_corner_property g
  intro x x' y y'
  exact corner_eq_of_three_lineCoordinates hab hac hbc
    (lineCoordinate_corner_or_of_additive_selectors hg a x x' y y')
    (lineCoordinate_corner_or_of_additive_selectors hg b x x' y y')
    (lineCoordinate_corner_or_of_additive_selectors hg c x x' y y')

/-- An injective product of memory addresses cannot retain all the original
affine line selectors once both factors have at least two elements. -/
theorem not_additive_line_selectors_of_injective
    {g : α → β → F × F}
    (hinj : Function.Injective (fun p : α × β ↦ g p.1 p.2))
    {x₀ x₁ : α} (hx : x₀ ≠ x₁) {y₀ y₁ : β} (hy : y₀ ≠ y₁)
    {a b c : F} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ AdditiveLineSelectors g := by
  intro hg
  have hcorner := corner_eq_of_three_lineCoordinates hab hac hbc
    (lineCoordinate_corner_or_of_additive_selectors hg a x₀ x₁ y₀ y₁)
    (lineCoordinate_corner_or_of_additive_selectors hg b x₀ x₁ y₀ y₁)
    (lineCoordinate_corner_or_of_additive_selectors hg c x₀ x₁ y₀ y₁)
  rcases hcorner with h | h
  · have hp : (x₀, y₀) = (x₀, y₁) := hinj h
    exact hy (congrArg Prod.snd hp)
  · have hp : (x₀, y₀) = (x₁, y₀) := hinj h
    exact hx (congrArg Prod.fst hp)

/-- Uniform additive approximation of all nonvertical line indicators. -/
def ApproxAdditiveLineSelectors (g : α → β → F × F) (ε : ℝ) : Prop := by
  classical
  exact ∀ a b : F, ∃ (constant : ℝ) (left : α → ℝ) (right : β → ℝ),
    ∀ x y, |(if lineCoordinate a (g x y) = b then (1 : ℝ) else 0) -
      (constant + left x + right y)| ≤ ε

theorem lineCoordinate_corner_or_of_approx_additive_selectors
    {g : α → β → F × F} {ε : ℝ} (hε : 4 * ε < 1)
    (hg : ApproxAdditiveLineSelectors g ε)
    (a : F) (x x' : α) (y y' : β) :
    lineCoordinate a (g x y) = lineCoordinate a (g x y') ∨
      lineCoordinate a (g x y) = lineCoordinate a (g x' y) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨constant, left, right, h⟩ := hg a (lineCoordinate a (g x y))
  have hp := (abs_le.mp (h x y)).2
  have hq := (abs_le.mp (h x y')).1
  have hr := (abs_le.mp (h x' y)).1
  have hs := (abs_le.mp (h x' y')).2
  simp only [ite_true] at hp
  simp only [Ne.symm hn.1, ite_false, zero_sub] at hq
  simp only [Ne.symm hn.2, ite_false, zero_sub] at hr
  have hnonneg : (0 : ℝ) ≤
      if lineCoordinate a (g x' y') = lineCoordinate a (g x y) then 1 else 0 := by
    split_ifs <;> norm_num
  linarith

/-- The exact rigidity survives any uniform selector error below one quarter.
Hence arbitrarily accurate affine approximations cannot bypass the obstruction. -/
theorem approx_additive_line_selectors_depend_on_one_axis
    [Nonempty α] [Nonempty β] {g : α → β → F × F} {ε : ℝ}
    (hε : 4 * ε < 1) (hg : ApproxAdditiveLineSelectors g ε) {a b c : F}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∃ u : α → F × F, ∀ x y, g x y = u x) ∨
      (∃ v : β → F × F, ∀ x y, g x y = v y) := by
  apply depends_on_one_axis_of_corner_property g
  intro x x' y y'
  exact corner_eq_of_three_lineCoordinates hab hac hbc
    (lineCoordinate_corner_or_of_approx_additive_selectors hε hg a x x' y y')
    (lineCoordinate_corner_or_of_approx_additive_selectors hε hg b x x' y y')
    (lineCoordinate_corner_or_of_approx_additive_selectors hε hg c x x' y y')

theorem not_approx_additive_line_selectors_of_injective
    {g : α → β → F × F}
    (hinj : Function.Injective (fun p : α × β ↦ g p.1 p.2))
    {x₀ x₁ : α} (hx : x₀ ≠ x₁) {y₀ y₁ : β} (hy : y₀ ≠ y₁)
    {a b c : F} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {ε : ℝ} (hε : 4 * ε < 1) :
    ¬ ApproxAdditiveLineSelectors g ε := by
  intro hg
  have hcorner := corner_eq_of_three_lineCoordinates hab hac hbc
    (lineCoordinate_corner_or_of_approx_additive_selectors hε hg a x₀ x₁ y₀ y₁)
    (lineCoordinate_corner_or_of_approx_additive_selectors hε hg b x₀ x₁ y₀ y₁)
    (lineCoordinate_corner_or_of_approx_additive_selectors hε hg c x₀ x₁ y₀ y₁)
  rcases hcorner with h | h
  · have hp : (x₀, y₀) = (x₀, y₁) := hinj h
    exact hy (congrArg Prod.snd hp)
  · have hp : (x₀, y₀) = (x₁, y₀) := hinj h
    exact hx (congrArg Prod.fst hp)

end LargeDomain
end HeadComplexity
