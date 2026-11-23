import Mathlib.Tactic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Option

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false

/-! Algebraic ingredients for the global convex-hull description of
amplitude-bounded heads. No bound on the number of heads is asserted. -/
namespace HeadComplexity.PriorityConvexHull

open scoped BigOperators

theorem elimination_identity (k C B U : ℝ)
    (hD : 1+B ≠ 0) (hW : 1+B+U ≠ 0) :
    (k+C+U*((k+C)/(1+B)))/(1+B+U) = (k+C)/(1+B) := by
  field_simp

theorem binary_gate_interpolation (x : Bool) (c a : ℝ) :
    (if x then c else a) =
      ((1+c)/2)*(if x then 1 else a)+((1-c)/2)*(if x then -1 else a) := by
  cases x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

theorem dominant_choice_error (w v a c t n : ℝ)
    (hw : 0 < w) (hv : 0 ≤ v) (ht : 0 < t)
    (hres : |a-c*v| ≤ 2*v) (hsmall : t*v ≤ n*w) :
    |(c*w+a)/(w+v)-c| ≤ 2*n/t := by
  have hden : 0 < w+v := add_pos_of_pos_of_nonneg hw hv
  have he : (c*w+a)/(w+v)-c = (a-c*v)/(w+v) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hden]
  calc
    _ ≤ 2*v/(w+v) := div_le_div_of_nonneg_right hres hden.le
    _ ≤ 2*v/w := div_le_div_of_nonneg_left (by positivity) hw (by linarith)
    _ ≤ 2*n/t := by
      apply (div_le_div_iff₀ hw ht).mpr
      nlinarith

theorem affine_hyperplane_transfer {I X : Type*} [Fintype I] [Fintype X]
    (w : I → ℝ) (p : I → X → ℝ) (μ : X → ℝ) (a : ℝ)
    (hw : ∑ i, w i = 1) (hp : ∀ i, a+∑ x, μ x*p i x = 0) :
    a+∑ x, μ x*(∑ i, w i*p i x) = 0 := by
  have hsum : (∑ i, w i*(a+∑ x, μ x*p i x)) = 0 := by
    simp_rw [hp, mul_zero]
    exact Finset.sum_const_zero
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul] at hsum
  have hid : (∑ x, μ x*(∑ i, w i*p i x)) = ∑ i, w i*(∑ x, μ x*p i x) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hid]
  exact hsum

noncomputable def ratio {I : Type*} (k : (I → Bool) → ℝ) (b c : I → ℝ)
    (s : Finset I) (x : I → Bool) : ℝ :=
  (k x+∑ i ∈ s, if x i then b i*c i else 0)/(1+∑ i ∈ s, if x i then b i else 0)

def gate {I : Type*} (j : I) (c : ℝ) (g : (I → Bool) → ℝ) (x : I → Bool) : ℝ :=
  if x j then c else g x

theorem ratio_erase_of_false {I : Type*} [DecidableEq I]
    (k : (I → Bool) → ℝ) (b c : I → ℝ) (s : Finset I)
    (j : I) (hj : j ∈ s) (x : I → Bool) (hx : x j = false) :
    ratio k b c (s.erase j) x = ratio k b c s x := by
  unfold ratio
  rw [Finset.sum_erase_eq_sub hj, Finset.sum_erase_eq_sub hj]
  simp [hx]

theorem ratio_elimination {I : Type*} [DecidableEq I]
    (k : (I → Bool) → ℝ) (b c : I → ℝ) (hb : ∀ i, 0 ≤ b i) (s : Finset I) :
    ratio k b c s = (1/(1+∑ i ∈ s, b i)) • k +
      ∑ j ∈ s, (b j/(1+∑ i ∈ s, b i)) • gate j (c j) (ratio k b c (s.erase j)) := by
  funext x
  let B := ∑ i ∈ s, b i
  let A := ∑ i ∈ s, if x i then b i else 0
  let C := ∑ i ∈ s, if x i then b i*c i else 0
  have hB : 0 ≤ B := Finset.sum_nonneg fun i hi ↦ hb i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i hi ↦ ite_nonneg (hb i) (le_refl 0)
  have hg (j : I) (hj : j ∈ s) :
      gate j (c j) (ratio k b c (s.erase j)) x =
        if x j then c j else ratio k b c s x := by
    cases hx : x j
    · simp [gate, hx, ratio_erase_of_false k b c s j hj x hx]
    · simp [gate, hx]
  have hs : (∑ j ∈ s, b j*(if x j then c j else ratio k b c s x)) =
      C+(B-A)*ratio k b c s x := by
    calc
      _ = ∑ j ∈ s, ((if x j then b j*c j else 0)+
          (b j-(if x j then b j else 0))*ratio k b c s x) := by
        apply Finset.sum_congr rfl
        intro j hj
        cases x j <;> simp
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  have hsumgate :
      (∑ j ∈ s, (b j/(1+∑ i ∈ s, b i))*gate j (c j) (ratio k b c (s.erase j)) x) =
      ∑ j ∈ s, (b j/(1+∑ i ∈ s, b i))*(if x j then c j else ratio k b c s x) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hg j hj]
  rw [hsumgate]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, hs]
  change (k x+C)/(1+A) = (1*k x)/(1+B)+(C+(B-A)*((k x+C)/(1+A)))/(1+B)
  have hD : 1+A ≠ 0 := by linarith
  have hW : 1+B ≠ 0 := by linarith
  field_simp [hD, hW]
  ring

/-- Convex sets closed under coordinate gates contain every normalized choice table
with their chosen fallback. This is the full finite elimination induction. -/
theorem ratio_mem_of_gate_closed {I : Type*} [DecidableEq I]
    (P : Set ((I → Bool) → ℝ)) (hP : Convex ℝ P)
    (k : (I → Bool) → ℝ) (hk : k ∈ P) (b c : I → ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (hgate : ∀ j g, g ∈ P → gate j (c j) g ∈ P) (s : Finset I) :
    ratio k b c s ∈ P := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    let W := 1+∑ i ∈ s, b i
    have hW : 0 < W := by
      have := Finset.sum_nonneg (fun i (_ : i ∈ s) ↦ hb i)
      dsimp [W]
      linarith
    let w : Option I → ℝ := fun o ↦ o.elim (1/W) (fun i ↦ b i/W)
    let z : Option I → ((I → Bool) → ℝ) :=
      fun o ↦ o.elim k (fun i ↦ gate i (c i) (ratio k b c (s.erase i)))
    have hw : ∀ o ∈ s.insertNone, 0 ≤ w o := by
      intro o ho
      cases o <;> simp only [w, Option.elim_none, Option.elim_some]
      · positivity
      · exact div_nonneg (hb _) hW.le
    have hsum : ∑ o ∈ s.insertNone, w o = 1 := by
      rw [Finset.sum_insertNone]
      simp only [w, Option.elim_none, Option.elim_some]
      rw [← Finset.sum_div, ← add_div]
      exact div_self hW.ne'
    have hz : ∀ o ∈ s.insertNone, z o ∈ P := by
      intro o ho
      cases o with
      | none => exact hk
      | some i =>
        have hi : i ∈ s := Finset.some_mem_insertNone.mp ho
        exact hgate i _ (ih _ (Finset.erase_ssubset hi))
    have hm := hP.sum_mem hw hsum hz
    rw [Finset.sum_insertNone] at hm
    simpa only [w, z, Option.elim_none, Option.elim_some, W,
      ← ratio_elimination k b c hb s] using hm

def priority {I : Type*} (order : List I) (outputs : I → ℝ) (default : ℝ)
    (x : I → Bool) : ℝ :=
  match order with
  | [] => default
  | i :: tail => if x i then outputs i else priority tail outputs default x

def priorityTables (I : Type*) : Set ((I → Bool) → ℝ) :=
  {f | ∃ order : List I, order.Nodup ∧ ∃ outputs : I → ℝ,
    (∀ i, outputs i = -1 ∨ outputs i = 1) ∧ ∃ default : ℝ,
    (default = -1 ∨ default = 1) ∧ f = priority order outputs default}

theorem priority_update_of_false {I : Type*} [DecidableEq I]
    (order : List I) (r : I → ℝ) (a c : ℝ) (j : I) (x : I → Bool)
    (hx : x j = false) :
    priority order (Function.update r j c) a x = priority order r a x := by
  induction order with
  | nil => rfl
  | cons i tail ih =>
    by_cases hij : i = j
    · subst i
      simp [priority, hx, ih]
    · simp [priority, Function.update_of_ne hij, ih]

theorem priority_erase_of_false {I : Type*} [DecidableEq I]
    (order : List I) (r : I → ℝ) (a : ℝ) (j : I) (x : I → Bool)
    (hx : x j = false) :
    priority (order.erase j) r a x = priority order r a x := by
  induction order with
  | nil => rfl
  | cons i tail ih =>
    by_cases hij : i = j
    · subst i
      simp [priority, hx]
    · simp [List.erase_cons_tail, hij, priority, ih]

theorem signed_gate_mem_priority {I : Type*} [DecidableEq I]
    (j : I) (c : ℝ) (hc : c = -1 ∨ c = 1) (f : (I → Bool) → ℝ)
    (hf : f ∈ priorityTables I) : gate j c f ∈ priorityTables I := by
  obtain ⟨order, hn, r, hr, a, ha, rfl⟩ := hf
  refine ⟨j :: order.erase j, List.nodup_cons.mpr ⟨hn.not_mem_erase, hn.erase j⟩,
    Function.update r j c, ?_, a, ha, ?_⟩
  · intro i
    by_cases hij : i = j
    · subst i
      simpa using hc
    · simpa [Function.update_of_ne hij] using hr i
  · funext x
    cases hx : x j
    · simp only [gate, priority, hx, Bool.false_eq_true, ↓reduceIte]
      rw [priority_update_of_false _ _ _ _ _ _ hx, priority_erase_of_false _ _ _ _ _ hx]
    · simp [gate, priority, hx]

theorem signed_gate_mem_convexHull {I : Type*} [DecidableEq I]
    (j : I) (c : ℝ) (hc : c = -1 ∨ c = 1) (f : (I → Bool) → ℝ)
    (hf : f ∈ convexHull ℝ (priorityTables I)) :
    gate j c f ∈ convexHull ℝ (priorityTables I) := by
  have hP := convex_convexHull ℝ (priorityTables I)
  apply convexHull_min (t := {g | gate j c g ∈ convexHull ℝ (priorityTables I)}) ?_ ?_ hf
  · intro g hg
    exact subset_convexHull ℝ _ (signed_gate_mem_priority j c hc g hg)
  · intro g hg h hh a b ha hb hab
    have hm := hP hg hh ha hb hab
    have he : gate j c (a • g+b • h) = a • gate j c g+b • gate j c h := by
      funext x
      cases hx : x j
      · simp [gate, hx]
      · simp only [gate, hx, ↓reduceIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [← add_mul, hab, one_mul]
    change gate j c (a • g+b • h) ∈ convexHull ℝ (priorityTables I)
    rwa [he]

theorem bounded_gate_mem_convexHull {I : Type*} [DecidableEq I]
    (j : I) (c : ℝ) (hc : |c| ≤ 1) (f : (I → Bool) → ℝ)
    (hf : f ∈ convexHull ℝ (priorityTables I)) :
    gate j c f ∈ convexHull ℝ (priorityTables I) := by
  have hm := (convex_convexHull ℝ (priorityTables I))
    (signed_gate_mem_convexHull j 1 (Or.inr rfl) f hf)
    (signed_gate_mem_convexHull j (-1) (Or.inl rfl) f hf)
    (show 0 ≤ (1+c)/2 by have := (abs_le.mp hc).1; linarith)
    (show 0 ≤ (1-c)/2 by have := (abs_le.mp hc).2; linarith)
    (show (1+c)/2+(1-c)/2=1 by ring)
  have he : gate j c f = ((1+c)/2) • gate j 1 f+((1-c)/2) • gate j (-1) f := by
    funext x
    exact binary_gate_interpolation (x j) c (f x)
  rwa [he]

theorem ratio_mem_priorityHull {I : Type*} [DecidableEq I]
    (k : (I → Bool) → ℝ) (hk : k ∈ convexHull ℝ (priorityTables I))
    (b c : I → ℝ) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, |c i| ≤ 1) (s : Finset I) :
    ratio k b c s ∈ convexHull ℝ (priorityTables I) :=
  ratio_mem_of_gate_closed _ (convex_convexHull ℝ _) k hk b c hb
    (fun j g hg ↦ bounded_gate_mem_convexHull j (c j) (hc j) g hg) s

end HeadComplexity.PriorityConvexHull
