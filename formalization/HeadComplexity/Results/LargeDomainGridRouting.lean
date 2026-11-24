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

end HeadComplexity.LargeDomain
