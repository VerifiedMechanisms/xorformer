import HeadComplexity.Results.AffineStatisticUpperBound
import HeadComplexity.Results.RoPEComparison

set_option linter.style.header false

/-!
# Adding unused inputs preserves pure rotary head counts

Every added position has a strictly positive attention mass. A finite strict
sign margin permits these masses to be sufficiently small, while preserving
the Boolean classifier on every assignment to the added bits.
-/

namespace HeadComplexity.InputPadding

open scoped BigOperators Topology

def project {n k : ℕ} (x : Fin (n + k) → Bool) : Fin n → Bool :=
  fun i ↦ x (i.castAdd k)

def extend {n k : ℕ} (x : Fin n → Bool) : Fin (n + k) → Bool :=
  Fin.addCases x (fun _ ↦ false)

@[simp] theorem project_extend {n k : ℕ} (x : Fin n → Bool) :
    project (k := k) (extend x) = x := by
  funext i
  simp [project, extend]

def classifier {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool) :
    (Fin (n + k) → Bool) → Bool := fun x ↦ f (project x)

noncomputable def atom {n : ℕ} (k : ℕ) (p : PureRoPEAtom n)
    (t : ℝ) (ht : 0 < t) : PureRoPEAtom (n + k) where
  a := Fin.addCases p.a (fun _ ↦ t)
  b := Fin.addCases p.b (fun _ ↦ t)
  γ := p.γ
  η := p.η
  v₀ := p.v₀
  v₁ := p.v₁
  ha := Fin.addCases (fun i ↦ by simpa using p.ha i) (fun _ ↦ by simpa using ht)
  hb := Fin.addCases (fun i ↦ by simpa using p.hb i) (fun _ ↦ by simpa using ht)
  hγ := p.hγ

/-- This expression remains defined at zero, where the auxiliary new masses
vanish. Only positive parameters are used to construct actual heads. -/
noncomputable def score {n : ℕ} (k : ℕ) (p : PureRoPEAtom n)
    (t : ℝ) (x : Fin (n + k) → Bool) : ℝ :=
  ((p.η + ∑ i, if project x i then p.b i * p.v₁ else p.a i * p.v₀) +
    t * ∑ j : Fin k, if x (Fin.natAdd n j) then p.v₁ else p.v₀) /
  ((p.γ + ∑ i, if project x i then p.b i else p.a i) + (k : ℝ) * t)

theorem atom_eval {n : ℕ} (k : ℕ) (p : PureRoPEAtom n)
    (t : ℝ) (ht : 0 < t) (x : Fin (n + k) → Bool) :
    (atom k p t ht).eval x = score k p t x := by
  simp only [PureRoPEAtom.eval, atom, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right, score, project]
  have hn : (∑ j : Fin k, if x (Fin.natAdd n j) then t * p.v₁ else t * p.v₀) =
      t * ∑ j : Fin k, if x (Fin.natAdd n j) then p.v₁ else p.v₀ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split <;> rfl
  have hd : (∑ j : Fin k, if x (Fin.natAdd n j) then t else t) = (k : ℝ) * t := by
    simp
  rw [hn, hd]
  simp only [add_assoc]
  rfl

@[simp] theorem score_zero {n : ℕ} (k : ℕ) (p : PureRoPEAtom n)
    (x : Fin (n + k) → Bool) : score k p 0 x = p.eval (project x) := by
  simp [score, PureRoPEAtom.eval]

theorem continuousAt_score {n : ℕ} (k : ℕ) (p : PureRoPEAtom n)
    (x : Fin (n + k) → Bool) : ContinuousAt (fun t ↦ score k p t x) 0 := by
  have hd : p.γ + ∑ i, (if project x i then p.b i else p.a i) ≠ 0 := by
    rw [← p.denominator_eq]
    exact (p.denominator_pos (project x)).ne'
  unfold score
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  simpa only [mul_zero, add_zero] using hd

/-- Adding any finite number of ignored input bits preserves the exact pure
head budget. The actual new attention masses are all strictly positive. -/
theorem pure_computable {n H : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : pureRoPEComputable n H f) :
    pureRoPEComputable (n + k) H (classifier k f) := by
  classical
  obtain ⟨p, c, hclass⟩ := hf
  obtain ⟨δ, _, hshift⟩ := exists_strict_shift (fun x ↦ c + ∑ h, (p h).eval x)
  let S : ℝ → (Fin (n + k) → Bool) → ℝ :=
    fun t x ↦ (c - δ) + ∑ h, score k (p h) t x
  have hzero (x : Fin (n + k) → Bool) :
      S 0 x = (c + ∑ h, (p h).eval (project x)) - δ := by
    simp only [S, score_zero]
    ring
  have hcont (x : Fin (n + k) → Bool) : ContinuousAt (fun t ↦ S t x) 0 := by
    have hc (h : Fin H) := continuousAt_score k (p h) x
    unfold S
    fun_prop
  obtain ⟨t, ht, _, hstable⟩ := exists_pos_lt_sign_preserving S hcont
    (fun x ↦ by rw [hzero]; exact (hshift (project x)).2) 1 zero_lt_one
  refine ⟨fun h ↦ atom k (p h) t ht, c - δ, fun x ↦ ?_⟩
  simp only [atom_eval]
  change (0 < S t x) ↔ f (project x) = true
  rw [(hstable x).1, hzero]
  exact (hshift (project x)).1.trans (hclass (project x))

end HeadComplexity.InputPadding
