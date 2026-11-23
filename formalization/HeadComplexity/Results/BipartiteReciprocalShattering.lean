import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Results.ReciprocalMatchingShattering

set_option linter.style.header false
set_option maxHeartbeats 1000000

/-! Replicate free reciprocal queries across disjoint input coordinates.
This yields genuine attention shattering on a two-hot subset of the cube.
It does not shatter the full cube and is not a worst-case head lower bound. -/
namespace HeadComplexity.BipartiteReciprocalShattering
open scoped BigOperators

def pairPoint {R M : ℕ} (r : Fin R) (j : Fin M) : Fin (R+M) → Bool :=
  Fin.addCases (fun i ↦ decide (i=r)) (fun k ↦ decide (k=j))

theorem affineValue_pairPoint {R M : ℕ} (c : ℝ)
    (a : Fin R → ℝ) (b : Fin M → ℝ) (r : Fin R) (j : Fin M) :
    affineValue c (Fin.addCases a b) (pairPoint r j) = c+a r+b j := by
  unfold affineValue pairPoint
  rw [Fin.sum_univ_add]
  simp [boolToReal]
  ring

theorem pairPoint_injective {R M : ℕ} :
    Function.Injective (fun q : Fin R × Fin M ↦ pairPoint q.1 q.2) := by
  intro a b hab
  have hr := congrFun hab (Fin.castAdd M a.1)
  have hj := congrFun hab (Fin.natAdd R a.2)
  simp only [pairPoint, Fin.addCases_left, Fin.addCases_right, decide_true] at hr hj
  have har : a.1 = b.1 := of_decide_eq_true hr.symm
  have haj : a.2 = b.2 := of_decide_eq_true hj.symm
  exact Prod.ext har haj

private theorem positive_common_lower_bound {R M : ℕ}
    (a : Fin R → ℝ) (b : Fin M → ℝ)
    (ha : ∀ r, 0 < a r) (hb : ∀ j, 0 < b j) :
    ∃ d : ℝ, 0 < d ∧ (∀ r, d ≤ a r) ∧ (∀ j, d ≤ b j) := by
  classical
  let g : Fin (R+M+1) → ℝ := Fin.cons 1 (Fin.addCases a b)
  obtain ⟨i, hi, hm⟩ := (Finset.univ : Finset (Fin (R+M+1))).exists_min_image
    g Finset.univ_nonempty
  have hp : ∀ i, 0 < g i := by
    intro i
    refine Fin.cases (by norm_num [g]) (fun k ↦ ?_) i
    dsimp [g]
    refine Fin.addCases (fun r ↦ ?_) (fun j ↦ ?_) k
    · simpa using ha r
    · simpa using hb j
  refine ⟨g i, hp i, ?_, ?_⟩
  · intro r
    simpa [g] using hm (Fin.castAdd M r).succ (Finset.mem_univ _)
  · intro j
    simpa [g] using hm (Fin.natAdd R j).succ (Finset.mem_univ _)

/-- Every row has its own positive parameter vector; the query poles and
residues are shared. All resulting denominator slopes are strictly positive. -/
theorem exists_exact_bipartite_embedding {R M P : ℕ}
    (theta : Fin R → Fin P → ℝ) (poles residues : Fin M → Fin P → ℝ)
    (htheta : ∀ r h, 0 < theta r h) (hpoles : ∀ j h, 0 < poles j h) :
    ∃ phi : Fin P → FracAtom (R+M), ∀ r j,
      (∑ h, (phi h).eval (pairPoint r j)) =
        ∑ h, residues j h / (theta r h + poles j h) := by
  classical
  have each (h : Fin P) : ∃ phi : FracAtom (R+M), ∀ r j,
      phi.eval (pairPoint r j) = residues j h / (theta r h + poles j h) := by
    obtain ⟨d, hd, hdt, hdp⟩ := positive_common_lower_bound
      (fun r ↦ theta r h) (fun j ↦ poles j h) (fun r ↦ htheta r h)
      (fun j ↦ hpoles j h)
    let a : Fin (R+M) → ℝ := Fin.addCases (fun _ ↦ 0) (fun j ↦ residues j h)
    let b : Fin (R+M) → ℝ :=
      Fin.addCases (fun r ↦ theta r h-d/2) (fun j ↦ poles j h-d/2)
    have hb : ∀ i, 0 < b i := by
      intro i
      refine Fin.addCases (fun r ↦ ?_) (fun j ↦ ?_) i
      · simp only [b, Fin.addCases_left]; linarith [hdt r]
      · simp only [b, Fin.addCases_right]; linarith [hdp j]
    refine ⟨FracAtom.ofPositiveAffineRatio 0 a d b hd hb, ?_⟩
    intro r j
    rw [FracAtom.ofPositiveAffineRatio_eval]
    dsimp [a, b]
    rw [affineValue_pairPoint, affineValue_pairPoint]
    congr 1 <;> ring
  choose phi hphi using each
  exact ⟨phi, fun r j ↦ Finset.sum_congr rfl (fun h _ ↦ hphi h r j)⟩

/-- Free-query shattering transfers to genuine attention on a Boolean sample,
and the number of sample points is multiplied by the number of data rows. -/
theorem replicate_shattering {M P : ℕ}
    (poles residues : Fin M → Fin P → ℝ) (hpoles : ∀ j h, 0 < poles j h)
    (hshatter : ∀ label : Fin M → Bool, ∃ theta : Fin P → ℝ,
      (∀ h, 0 < theta h) ∧ ∀ j,
        (if label j then (1:ℝ) else -1) *
          (∑ h, residues j h / (theta h + poles j h)) > 1/2)
    (R : ℕ) (label : Fin R × Fin M → Bool) :
    ∃ f : (Fin (R+M) → Bool) → Bool,
      computableWithHeadsN (R+M) P f ∧ ∀ r j, f (pairPoint r j) = label (r,j) := by
  classical
  have each (r : Fin R) := hshatter (fun j ↦ label (r,j))
  choose theta htheta hmargin using each
  obtain ⟨phi, hphi⟩ := exists_exact_bipartite_embedding theta poles residues htheta hpoles
  let score := fun x ↦ ∑ h, (phi h).eval x
  let f := fun x ↦ decide (0 < score x)
  refine ⟨f, computable_of_fracComputable ⟨phi, 0, ?_⟩, ?_⟩
  · intro x
    simp [f, score]
  · intro r j
    have hm := hmargin r j
    dsimp [f, score]
    simp only [hphi]
    cases hl : label (r,j) <;> simp only [hl, Bool.false_eq_true, ite_false,
      ite_true, one_mul, neg_one_mul] at hm ⊢
    · exact decide_eq_false (by linarith)
    · exact decide_eq_true (by linarith)

/-- No uniform linear upper bound in the manuscript's normalized parameter
count can bound shattering on all subsets of Boolean cubes. The sample is a
two-hot bipartite layer, not the full cube. -/
theorem unbounded_actual_tests_per_parameter (C : ℕ) :
    ∃ H m : ℕ, 0 < H ∧ C*(2*(m+m)*H) < m*m ∧
      ∀ label : Fin m × Fin m → Bool,
        ∃ f : (Fin (m+m) → Bool) → Bool,
          computableWithHeadsN (m+m) H f ∧
          ∀ r j, f (pairPoint r j) = label (r,j) := by
  classical
  obtain ⟨H, m, hH, hm, poles, residues, hpoles, hshatter⟩ :=
    ReciprocalMatchingShattering.unbounded_tests_per_positive_parameter (4*C)
  refine ⟨H, m, hH, ?_, fun label ↦
    replicate_shattering poles residues hpoles hshatter m label⟩
  have hmp : 0 < m := by omega
  have hmul := Nat.mul_lt_mul_of_pos_left hm hmp
  nlinarith

#print axioms affineValue_pairPoint
#print axioms pairPoint_injective
#print axioms exists_exact_bipartite_embedding
#print axioms replicate_shattering
#print axioms unbounded_actual_tests_per_parameter
end HeadComplexity.BipartiteReciprocalShattering
