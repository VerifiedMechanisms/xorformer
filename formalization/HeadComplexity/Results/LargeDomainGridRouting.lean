import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity.LargeDomain

private lemma fin_orderEmbedding_lower {p m : ℕ} (e : Fin p ↪o Fin m) (i : Fin p) :
    i.val ≤ (e i).val := by
  have aux : ∀ r : ℕ, ∀ j : Fin p, j.val = r → r ≤ (e j).val := by
    intro r
    induction r with
    | zero => intro j hj; omega
    | succ r ih =>
      intro j hj
      let t : Fin p := ⟨r, by omega⟩
      have ht : t < j := by change r < j.val; omega
      have he := e.strictMono ht
      have hp := ih t rfl
      change (e t).val < (e j).val at he
      omega
  exact aux i.val i rfl

private lemma fin_orderEmbedding_upper {p m : ℕ} (e : Fin p ↪o Fin m) (i : Fin p) :
    (e i).val + p ≤ m + i.val := by
  let f : Fin p ↪o Fin m :=
    { toFun := fun j ↦ Fin.rev (e (Fin.rev j))
      inj' := Fin.rev_injective.comp (e.injective.comp Fin.rev_injective)
      map_rel_iff' := by intro a b; simp }
  have h := fin_orderEmbedding_lower f (Fin.rev i)
  change (Fin.rev i).val ≤ (Fin.rev (e (Fin.rev (Fin.rev i)))).val at h
  simp only [Fin.rev_rev, Fin.val_rev] at h
  have hi := i.isLt
  have he := (e i).isLt
  omega

/-- Every independent left/right prescription on the `m` half-integer sources
has an injective realization in the `m+1` integer catalog points. -/
theorem exists_interval_sign_injection (m : ℕ) (σ : Fin m → Bool) :
    ∃ f : Fin m → Fin (m + 1), Function.Injective f ∧
      ∀ i, (σ i = true → i.val < (f i).val) ∧
        (σ i = false → (f i).val ≤ i.val) := by
  classical
  let N : Finset (Fin m) := Finset.univ.filter (fun i ↦ σ i = false)
  let P : Finset (Fin m) := Finset.univ.filter (fun i ↦ σ i = true)
  have hNP : N.card + P.card = m := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m))) (p := fun i ↦ σ i = false)
    simpa [N, P, Bool.not_eq_false] using h
  let nr (i : Fin m) (hi : σ i = false) : Fin N.card :=
    (N.orderIsoOfFin rfl).symm ⟨i, by simp [N, hi]⟩
  let pr (i : Fin m) (hi : σ i = true) : Fin P.card :=
    (P.orderIsoOfFin rfl).symm ⟨i, by simp [P, hi]⟩
  have hnval (i : Fin m) (hi : σ i = false) :
      N.orderEmbOfFin rfl (nr i hi) = i := by
    exact congrArg Subtype.val ((N.orderIsoOfFin rfl).apply_symm_apply _)
  have hpval (i : Fin m) (hi : σ i = true) :
      P.orderEmbOfFin rfl (pr i hi) = i := by
    exact congrArg Subtype.val ((P.orderIsoOfFin rfl).apply_symm_apply _)
  let f : Fin m → Fin (m + 1) := fun i ↦
    if hi : σ i = true then
      ⟨N.card + (pr i hi).val + 1, by have := (pr i hi).isLt; omega⟩
    else
      ⟨(nr i (by simpa using hi)).val, by
        have := (nr i (by simpa using hi)).isLt; omega⟩
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    have hv := congrArg Fin.val hij
    by_cases hi : σ i = true <;> by_cases hj : σ j = true
    · simp only [f, dite_eq_left hi, dite_eq_left hj] at hv
      have he : pr i hi = pr j hj := Fin.ext (by omega)
      have := congrArg (P.orderEmbOfFin rfl) he
      simpa [hpval] using this
    · simp only [f, dite_eq_left hi, dite_eq_right hj] at hv
      have := (nr j (by simpa using hj)).isLt
      omega
    · simp only [f, dite_eq_right hi, dite_eq_left hj] at hv
      have := (nr i (by simpa using hi)).isLt
      omega
    · simp only [f, dite_eq_right hi, dite_eq_right hj] at hv
      have he : nr i (by simpa using hi) = nr j (by simpa using hj) := Fin.ext hv
      have := congrArg (N.orderEmbOfFin rfl) he
      simpa [hnval] using this
  · intro i
    constructor
    · intro hi
      have h := fin_orderEmbedding_upper (P.orderEmbOfFin rfl) (pr i hi)
      rw [hpval i hi] at h
      simp only [f, dite_eq_left hi]
      omega
    · intro hi
      have h := fin_orderEmbedding_lower (N.orderEmbOfFin rfl) (nr i hi)
      rw [hnval i hi] at h
      simp only [f, dite_eq_right (show ¬σ i = true by simp [hi])]
      exact h

/-- A Cartesian catalog with one extra level in each coordinate routes every
independent sign word at every source. No balancing hypothesis is imposed on
the labels. The source threshold is `x i + 1/2`. -/
theorem exists_grid_sign_injection (m a : ℕ)
    (σ : (Fin a → Fin m) → Fin a → Bool) :
    ∃ f : (Fin a → Fin m) → (Fin a → Fin (m + 1)), Function.Injective f ∧
      ∀ x i, (σ x i = true → (x i).val < (f x i).val) ∧
        (σ x i = false → (f x i).val ≤ (x i).val) := by
  classical
  induction a with
  | zero =>
    refine ⟨fun _ i ↦ Fin.elim0 i, ?_, ?_⟩
    · intro x y h; funext i; exact Fin.elim0 i
    · intro x i; exact Fin.elim0 i
  | succ a ih =>
    by_cases hm : m = 0
    · subst m
      exact ⟨fun x ↦ False.elim (Fin.elim0 (x 0)),
        fun x ↦ False.elim (Fin.elim0 (x 0)),
        fun x ↦ False.elim (Fin.elim0 (x 0))⟩
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    choose r hr hs using fun z : Fin a → Fin m ↦
      exists_interval_sign_injection m (fun t ↦ σ (Fin.cons t z) 0)
    let pick (c : Fin (m + 1)) (z : Fin a → Fin m) : Fin m :=
      if h : ∃ t, r z t = c then Classical.choose h else ⟨0, hmpos⟩
    have hpick (z : Fin a → Fin m) (t : Fin m) : pick (r z t) z = t := by
      have hex : ∃ q, r z q = r z t := ⟨t, rfl⟩
      have heq : r z (Classical.choose hex) = r z t := Classical.choose_spec hex
      simpa [pick, hex] using hr z heq
    choose g hg hgs using fun c : Fin (m + 1) ↦
      ih (fun z i ↦ σ (Fin.cons (pick c z) z) i.succ)
    let f (x : Fin (a + 1) → Fin m) : Fin (a + 1) → Fin (m + 1) :=
      Fin.cons (r (Fin.tail x) (x 0))
        (g (r (Fin.tail x) (x 0)) (Fin.tail x))
    refine ⟨f, ?_, ?_⟩
    · intro x y hxy
      have hc : r (Fin.tail x) (x 0) = r (Fin.tail y) (y 0) := by
        simpa [f] using congrFun hxy 0
      have ht : Fin.tail x = Fin.tail y := by
        apply hg (r (Fin.tail y) (y 0))
        have h := congrArg Fin.tail hxy
        simpa [f, hc] using h
      have hzero : x 0 = y 0 := by
        apply hr (Fin.tail y)
        simpa [ht] using hc
      rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hzero, ht]
    · intro x i
      cases i using Fin.cases with
      | zero =>
        simpa [f, Fin.cons_self_tail] using hs (Fin.tail x) (x 0)
      | succ i =>
        have h := hgs (r (Fin.tail x) (x 0)) (Fin.tail x) i
        simpa [f, hpick, Fin.cons_self_tail, Fin.tail] using h

/-- Padding each side of the integer catalog by `r` gives signed margin at least
`r + 1/2`, with the catalog value interpreted as `f i - r`. -/
theorem exists_interval_padded_sign_injection (m r : ℕ) (σ : Fin m → Bool) :
    ∃ f : Fin m → Fin (m + 2 * r + 1), Function.Injective f ∧
      ∀ i, (σ i = true → i.val + 2 * r < (f i).val) ∧
        (σ i = false → (f i).val ≤ i.val) := by
  classical
  let N : Finset (Fin m) := Finset.univ.filter (fun i ↦ σ i = false)
  let P : Finset (Fin m) := Finset.univ.filter (fun i ↦ σ i = true)
  have hNP : N.card + P.card = m := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m))) (p := fun i ↦ σ i = false)
    simpa [N, P, Bool.not_eq_false] using h
  let nr (i : Fin m) (hi : σ i = false) : Fin N.card :=
    (N.orderIsoOfFin rfl).symm ⟨i, by simp [N, hi]⟩
  let pr (i : Fin m) (hi : σ i = true) : Fin P.card :=
    (P.orderIsoOfFin rfl).symm ⟨i, by simp [P, hi]⟩
  have hnval (i : Fin m) (hi : σ i = false) :
      N.orderEmbOfFin rfl (nr i hi) = i := by
    exact congrArg Subtype.val ((N.orderIsoOfFin rfl).apply_symm_apply _)
  have hpval (i : Fin m) (hi : σ i = true) :
      P.orderEmbOfFin rfl (pr i hi) = i := by
    exact congrArg Subtype.val ((P.orderIsoOfFin rfl).apply_symm_apply _)
  let f : Fin m → Fin (m + 2 * r + 1) := fun i ↦
    if hi : σ i = true then
      ⟨N.card + (pr i hi).val + 2 * r + 1, by have := (pr i hi).isLt; omega⟩
    else
      ⟨(nr i (by simpa using hi)).val, by
        have := (nr i (by simpa using hi)).isLt; omega⟩
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    have hv := congrArg Fin.val hij
    by_cases hi : σ i = true <;> by_cases hj : σ j = true
    · simp only [f, dite_eq_left hi, dite_eq_left hj] at hv
      have he : pr i hi = pr j hj := Fin.ext (by omega)
      have := congrArg (P.orderEmbOfFin rfl) he
      simpa [hpval] using this
    · simp only [f, dite_eq_left hi, dite_eq_right hj] at hv
      have := (nr j (by simpa using hj)).isLt
      omega
    · simp only [f, dite_eq_right hi, dite_eq_left hj] at hv
      have := (nr i (by simpa using hi)).isLt
      omega
    · simp only [f, dite_eq_right hi, dite_eq_right hj] at hv
      have he : nr i (by simpa using hi) = nr j (by simpa using hj) := Fin.ext hv
      have := congrArg (N.orderEmbOfFin rfl) he
      simpa [hnval] using this
  · intro i
    constructor
    · intro hi
      have h := fin_orderEmbedding_upper (P.orderEmbOfFin rfl) (pr i hi)
      rw [hpval i hi] at h
      simp only [f, dite_eq_left hi]
      omega
    · intro hi
      have h := fin_orderEmbedding_lower (N.orderEmbOfFin rfl) (nr i hi)
      rw [hnval i hi] at h
      simp only [f, dite_eq_right (show ¬σ i = true by simp [hi])]
      exact h

/-- The padded Cartesian catalog routes every independent sign word with
coordinate displacement at least `r + 1/2`. Interpret its value as `f x i - r`. -/
theorem exists_grid_padded_sign_injection (m a r : ℕ)
    (σ : (Fin a → Fin m) → Fin a → Bool) :
    ∃ f : (Fin a → Fin m) → (Fin a → Fin (m + 2 * r + 1)), Function.Injective f ∧
      ∀ x i, (σ x i = true → (x i).val + 2 * r < (f x i).val) ∧
        (σ x i = false → (f x i).val ≤ (x i).val) := by
  classical
  induction a with
  | zero =>
    refine ⟨fun _ i ↦ Fin.elim0 i, ?_, ?_⟩
    · intro x y h; funext i; exact Fin.elim0 i
    · intro x i; exact Fin.elim0 i
  | succ a ih =>
    by_cases hm : m = 0
    · subst m
      exact ⟨fun x ↦ False.elim (Fin.elim0 (x 0)),
        fun x ↦ False.elim (Fin.elim0 (x 0)),
        fun x ↦ False.elim (Fin.elim0 (x 0))⟩
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    choose route hr hs using fun z : Fin a → Fin m ↦
      exists_interval_padded_sign_injection m r (fun t ↦ σ (Fin.cons t z) 0)
    let pick (c : Fin (m + 2 * r + 1)) (z : Fin a → Fin m) : Fin m :=
      if h : ∃ t, route z t = c then Classical.choose h else ⟨0, hmpos⟩
    have hpick (z : Fin a → Fin m) (t : Fin m) : pick (route z t) z = t := by
      have hex : ∃ q, route z q = route z t := ⟨t, rfl⟩
      have heq : route z (Classical.choose hex) = route z t := Classical.choose_spec hex
      simpa [pick, hex] using hr z heq
    choose g hg hgs using fun c : Fin (m + 2 * r + 1) ↦
      ih (fun z i ↦ σ (Fin.cons (pick c z) z) i.succ)
    let f (x : Fin (a + 1) → Fin m) : Fin (a + 1) → Fin (m + 2 * r + 1) :=
      Fin.cons (route (Fin.tail x) (x 0))
        (g (route (Fin.tail x) (x 0)) (Fin.tail x))
    refine ⟨f, ?_, ?_⟩
    · intro x y hxy
      have hc : route (Fin.tail x) (x 0) = route (Fin.tail y) (y 0) := by
        simpa [f] using congrFun hxy 0
      have ht : Fin.tail x = Fin.tail y := by
        apply hg (route (Fin.tail y) (y 0))
        have h := congrArg Fin.tail hxy
        simpa [f, hc] using h
      have hzero : x 0 = y 0 := by
        apply hr (Fin.tail y)
        simpa [ht] using hc
      rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hzero, ht]
    · intro x i
      cases i using Fin.cases with
      | zero =>
        simpa [f, Fin.cons_self_tail] using hs (Fin.tail x) (x 0)
      | succ i =>
        have h := hgs (route (Fin.tail x) (x 0)) (Fin.tail x) i
        simpa [f, hpick, Fin.cons_self_tail, Fin.tail] using h

/-- The natural-number routing theorem gives a uniform real margin after
centering the padded catalog. -/
theorem exists_grid_padded_margin_injection (m a r : ℕ)
    (σ : (Fin a → Fin m) → Fin a → Bool) :
    ∃ f : (Fin a → Fin m) → (Fin a → Fin (m + 2 * r + 1)),
      Function.Injective f ∧ ∀ x i,
      let D : ℝ := (f x i).val - r - ((x i).val + 1 / 2)
      ((σ x i = true → (r : ℝ) + 1 / 2 ≤ D) ∧
        (σ x i = false → (r : ℝ) + 1 / 2 ≤ -D)) ∧
        |D| ≤ (m : ℝ) + r + 1 / 2 := by
  obtain ⟨f, hf, hs⟩ := exists_grid_padded_sign_injection m a r σ
  refine ⟨f, hf, ?_⟩
  intro x i
  dsimp
  have hx : ((x i).val : ℝ) < m := by exact_mod_cast (x i).isLt
  have hx0 : 0 ≤ ((x i).val : ℝ) := Nat.cast_nonneg _
  have hy : ((f x i).val : ℝ) < (m : ℝ) + 2 * r + 1 := by
    exact_mod_cast (f x i).isLt
  have hy0 : 0 ≤ ((f x i).val : ℝ) := Nat.cast_nonneg _
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  constructor
  · constructor
    · intro hp
      have h : ((x i).val : ℝ) + 2 * r + 1 ≤ (f x i).val := by
        exact_mod_cast (hs x i).1 hp
      linarith
    · intro hn
      have h : ((f x i).val : ℝ) ≤ (x i).val := by
        exact_mod_cast (hs x i).2 hn
      linarith
  · apply abs_le.mpr
    constructor <;> linarith

/-- An absolute row-sum bound controls a dense kernel's error against the
ideal source selector, uniformly over every bounded displacement vector. -/
theorem grid_kernel_error_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (D : ι → ℝ) (B : ℝ)
    (hD : ∀ h, |D h| ≤ B) (x : ι) :
    |(∑ h, K x h * D h) - D x| ≤
      B * ∑ h, |K x h - if h = x then 1 else 0| := by
  classical
  have hid : (∑ h : ι, (if h = x then (1 : ℝ) else 0) * D h) = D x := by
    simp
  have he : (∑ h, K x h * D h) - D x =
      ∑ h, (K x h - if h = x then 1 else 0) * D h := by
    simp only [sub_mul, Finset.sum_sub_distrib, hid]
  rw [he]
  calc
    |∑ h, (K x h - if h = x then 1 else 0) * D h| ≤
        ∑ h, |(K x h - if h = x then 1 else 0) * D h| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h, |K x h - if h = x then 1 else 0| * B := by
      apply Finset.sum_le_sum
      intro h _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hD h) (abs_nonneg _)
    _ = B * ∑ h, |K x h - if h = x then 1 else 0| := by
      rw [← Finset.sum_mul, mul_comm]

/-- The robust routing margin survives a dense kernel whenever its absolute
row-sum deviation from the identity is smaller than margin over magnitude. -/
theorem grid_kernel_preserves_margin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (D : ι → ℝ) (B μ : ℝ)
    (hD : ∀ h, |D h| ≤ B) (x : ι)
    (hK : B * ∑ h, |K x h - if h = x then 1 else 0| < μ) :
    (μ ≤ D x → 0 < ∑ h, K x h * D h) ∧
      (μ ≤ -D x → (∑ h, K x h * D h) < 0) := by
  have he := (grid_kernel_error_bound K D B hD x).trans_lt hK
  have he' := abs_lt.mp he
  constructor <;> intro hx <;> linarith

end HeadComplexity.LargeDomain
