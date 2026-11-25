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

noncomputable def restrictAtom {n k : ℕ} (p : PureRoPEAtom (n + k)) :
    PureRoPEAtom n where
  a i := p.a (i.castAdd k)
  b i := p.b (i.castAdd k)
  γ := p.γ + ∑ j : Fin k, p.a (Fin.natAdd n j)
  η := p.η + ∑ j : Fin k, p.a (Fin.natAdd n j) * p.v₀
  v₀ := p.v₀
  v₁ := p.v₁
  ha i := p.ha (i.castAdd k)
  hb i := p.hb (i.castAdd k)
  hγ := add_pos_of_pos_of_nonneg p.hγ
    (Finset.sum_nonneg (fun j _ ↦ (p.ha (Fin.natAdd n j)).le))

theorem restrictAtom_eval {n k : ℕ} (p : PureRoPEAtom (n + k)) (x : Fin n → Bool) :
    (restrictAtom p).eval x = p.eval (extend x) := by
  simp only [PureRoPEAtom.eval, restrictAtom, extend, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right, Bool.false_eq_true, if_false]
  congr 1 <;> abel

/-- Fixing all added bits to zero preserves pure head budgets exactly. Their
constant contributions are absorbed into the query mass and query value. -/
theorem pure_restrict {n k H : ℕ} (f : (Fin (n + k) → Bool) → Bool)
    (hf : pureRoPEComputable (n + k) H f) :
    pureRoPEComputable n H (fun x ↦ f (extend x)) := by
  obtain ⟨p, c, hp⟩ := hf
  exact ⟨fun h ↦ restrictAtom (p h), c, fun x ↦ by
    simp only [restrictAtom_eval]
    exact hp (extend x)⟩

theorem pure_classifier_iff {n H : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool) :
    pureRoPEComputable (n + k) H (classifier k f) ↔ pureRoPEComputable n H f := by
  refine ⟨fun hf ↦ ?_, pure_computable k f⟩
  simpa only [classifier, project_extend] using pure_restrict (classifier k f) hf

theorem pureHStar_classifier {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool) :
    PureRoPEHStar (n + k) (classifier k f) = PureRoPEHStar n f := by
  classical
  apply Nat.le_antisymm
  · exact Nat.find_min' _ (pure_computable k f (pureRoPEHStar_computable f))
  · exact Nat.find_min' _ ((pure_classifier_iff k f).mp
      (pureRoPEHStar_computable (classifier k f)))

noncomputable def vanillaAtom {n : ℕ} (k : ℕ) (p : FracAtom n)
    (t : ℝ) (ht : 0 < t) : FracAtom (n + k) where
  η := p.η
  δ := p.δ
  γ := p.γ
  α := p.α
  ρ := Fin.addCases p.ρ (fun _ ↦ t)
  m := Fin.addCases p.m (fun _ ↦ 0)
  hγ := p.hγ
  hα := p.hα
  hρ := Fin.addCases (fun i ↦ by simpa using p.hρ i) (fun _ ↦ by simpa using ht)

noncomputable def vanillaScore {n : ℕ} (k : ℕ) (p : FracAtom n)
    (t : ℝ) (x : Fin (n + k) → Bool) : ℝ :=
  ((p.η + ∑ i, p.wt (project x) i * (p.m i + if project x i then p.δ else 0)) +
    t * ∑ j : Fin k, (if x (Fin.natAdd n j) then p.α else 1) *
      (if x (Fin.natAdd n j) then p.δ else 0)) /
  ((p.γ + ∑ i, p.wt (project x) i) +
    t * ∑ j : Fin k, if x (Fin.natAdd n j) then p.α else 1)

theorem vanillaAtom_eval {n : ℕ} (k : ℕ) (p : FracAtom n)
    (t : ℝ) (ht : 0 < t) (x : Fin (n + k) → Bool) :
    (vanillaAtom k p t ht).eval x = vanillaScore k p t x := by
  simp only [FracAtom.eval, FracAtom.wt, vanillaAtom, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right, vanillaScore, project,
    zero_add, Finset.mul_sum, mul_assoc, add_assoc]
  rfl

@[simp] theorem vanillaScore_zero {n : ℕ} (k : ℕ) (p : FracAtom n)
    (x : Fin (n + k) → Bool) : vanillaScore k p 0 x = p.eval (project x) := by
  simp [vanillaScore, FracAtom.eval]

theorem continuousAt_vanillaScore {n : ℕ} (k : ℕ) (p : FracAtom n)
    (x : Fin (n + k) → Bool) : ContinuousAt (fun t ↦ vanillaScore k p t x) 0 := by
  unfold vanillaScore
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  simpa only [zero_mul, add_zero] using (p.denom_pos (project x)).ne'

/-- Vanilla attention also preserves an exact head budget when adding unused
input bits. Positive positional masses are chosen by a finite strict margin. -/
theorem vanilla_computable {n H : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : computableWithSharedHeadsN n H f) :
    computableWithSharedHeadsN (n + k) H (classifier k f) := by
  classical
  obtain ⟨p, c, hclass⟩ := (computableWithSharedHeadsN_iff_fracComputable H f).mp hf
  obtain ⟨δ, _, hshift⟩ := exists_strict_shift (fun x ↦ c + ∑ h, (p h).eval x)
  let S : ℝ → (Fin (n + k) → Bool) → ℝ :=
    fun t x ↦ (c - δ) + ∑ h, vanillaScore k (p h) t x
  have hzero (x : Fin (n + k) → Bool) :
      S 0 x = (c + ∑ h, (p h).eval (project x)) - δ := by
    simp only [S, vanillaScore_zero]
    ring
  have hcont (x : Fin (n + k) → Bool) : ContinuousAt (fun t ↦ S t x) 0 := by
    have hc (h : Fin H) := continuousAt_vanillaScore k (p h) x
    unfold S
    fun_prop
  obtain ⟨t, ht, _, hstable⟩ := exists_pos_lt_sign_preserving S hcont
    (fun x ↦ by rw [hzero]; exact (hshift (project x)).2) 1 zero_lt_one
  apply (computableWithSharedHeadsN_iff_fracComputable H _).mpr
  refine ⟨fun h ↦ vanillaAtom k (p h) t ht, c - δ, fun x ↦ ?_⟩
  simp only [vanillaAtom_eval]
  change (0 < S t x) ↔ f (project x) = true
  rw [(hstable x).1, hzero]
  exact (hshift (project x)).1.trans (hclass (project x))

end HeadComplexity.InputPadding
