import HeadComplexity.Atoms.RoPE
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.style.header false

/-!
# Construct pure rotary atoms from centered affine data

The numerator coefficients have the token-only relation k s + ell b. Strict
mass inequalities give positive token attention weights and query weight.
The second part records an exact one-hot auxiliary-context construction.
-/

namespace HeadComplexity.PureRoPECenteredConstruction

noncomputable section

open scoped BigOperators

def spin (b : Bool) : ℝ := if b then 1 else -1

def linear {n : ℕ} (v : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, v i * spin (x i)

def atom {n : ℕ} (s b : Fin n → ℝ) (d n₀ k ell : ℝ)
    (hs : ∀ i, |b i| < s i) (hd : ∑ i, s i < d) : PureRoPEAtom n where
  a i := s i - b i
  b i := s i + b i
  γ := d - ∑ i, s i
  η := n₀ - ∑ i, (ell * s i + k * b i)
  v₀ := ell - k
  v₁ := ell + k
  ha i := by linarith [le_abs_self (b i), hs i]
  hb i := by linarith [neg_le_abs (b i), hs i]
  hγ := sub_pos.mpr hd

theorem atom_denominator {n : ℕ} (s b : Fin n → ℝ) (d n₀ k ell : ℝ)
    (hs : ∀ i, |b i| < s i) (hd : ∑ i, s i < d) (x : Fin n → Bool) :
    (atom s b d n₀ k ell hs hd).γ +
      (∑ i, if x i then (atom s b d n₀ k ell hs hd).b i
        else (atom s b d n₀ k ell hs hd).a i) = d + linear b x := by
  have hi (i) : (if x i then s i + b i else s i - b i) = s i + b i * spin (x i) := by
    cases x i <;> simp [spin]
    ring
  simp only [atom, hi, Finset.sum_add_distrib, linear]
  ring

theorem atom_numerator {n : ℕ} (s b : Fin n → ℝ) (d n₀ k ell : ℝ)
    (hs : ∀ i, |b i| < s i) (hd : ∑ i, s i < d) (x : Fin n → Bool) :
    (atom s b d n₀ k ell hs hd).η +
      (∑ i, if x i then (atom s b d n₀ k ell hs hd).b i *
        (atom s b d n₀ k ell hs hd).v₁ else
        (atom s b d n₀ k ell hs hd).a i * (atom s b d n₀ k ell hs hd).v₀) =
      n₀ + linear (fun i ↦ k * s i + ell * b i) x := by
  have hi (i) :
      (if x i then (s i + b i) * (ell + k) else (s i - b i) * (ell - k)) =
        (ell * s i + k * b i) + (k * s i + ell * b i) * spin (x i) := by
    cases x i <;> simp [spin] <;> ring
  simp only [atom, hi, Finset.sum_add_distrib, linear]
  ring

theorem atom_eval {n : ℕ} (s b : Fin n → ℝ) (d n₀ k ell : ℝ)
    (hs : ∀ i, |b i| < s i) (hd : ∑ i, s i < d) (x : Fin n → Bool) :
    (atom s b d n₀ k ell hs hd).eval x =
      (n₀ + linear (fun i ↦ k * s i + ell * b i) x) / (d + linear b x) := by
  unfold PureRoPEAtom.eval
  rw [atom_numerator, atom_denominator]

def baseD (l₀ r₀ : ℝ) : ℝ := (r₀ - l₀) / 2
def baseP (l₀ r₀ : ℝ) : ℝ := (r₀ + l₀) / 2
def controlB {m : ℕ} (d : Fin m → ℝ) (l₀ r₀ : ℝ) (i : Fin m) : ℝ :=
  (d i - baseD l₀ r₀) / 2
def controlS {m : ℕ} (p : Fin m → ℝ) (l₀ r₀ : ℝ) (i : Fin m) : ℝ :=
  (p i - baseP l₀ r₀) / 2

theorem control_mass {m : ℕ} (d p : Fin m → ℝ) (l₀ r₀ : ℝ)
    (hl : ∀ i, l₀ < p i - d i) (hr : ∀ i, r₀ < p i + d i) (i : Fin m) :
    |controlB d l₀ r₀ i| < controlS p l₀ r₀ i := by
  rw [abs_lt]
  dsimp [controlB, controlS, baseD, baseP]
  constructor <;> linarith [hl i, hr i]

/-- Query mass after adding one auxiliary coordinate per context. -/
theorem query_mass {m : ℕ} (d p : Fin m → ℝ) (l₀ r₀ S : ℝ) :
    baseD l₀ r₀ + (∑ i, controlB d l₀ r₀ i) - S - (∑ i, controlS p l₀ r₀ i) =
      (r₀ + ((m : ℝ) - 1) * l₀ - (∑ i, (p i - d i))) / 2 - S := by
  simp only [controlB, controlS, baseD, baseP, ← Finset.sum_div,
    Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Any lower bounds on the two light-cone coordinates with positive mass
slack give simultaneous pure one-hot contexts. Finite minima provide the
sharp criterion stated in the accompanying note. -/
theorem exists_oneHot_controls {m : ℕ} (d p : Fin m → ℝ) (L R S : ℝ)
    (hL : ∀ i, L ≤ p i - d i) (hR : ∀ i, R ≤ p i + d i)
    (hgap : 2 * S < R + ((m : ℝ) - 1) * L - ∑ i, (p i - d i)) :
    ∃ l₀ r₀ : ℝ, (∀ i, |controlB d l₀ r₀ i| < controlS p l₀ r₀ i) ∧
      S + (∑ i, controlS p l₀ r₀ i) < baseD l₀ r₀ + ∑ i, controlB d l₀ r₀ i := by
  let gap := R + ((m : ℝ) - 1) * L - (∑ i, (p i - d i)) - 2 * S
  have hg : 0 < gap := sub_pos.mpr hgap
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  let δ := gap / (2 * ((m : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have heq : δ * (2 * ((m : ℝ) + 1)) = gap := by
    dsimp [δ]
    field_simp
  refine ⟨L - δ, R - δ, ?_, ?_⟩
  · exact control_mass d p _ _ (fun i ↦ by linarith [hL i]) (fun i ↦ by linarith [hR i])
  · have hmass := query_mass d p (L - δ) (R - δ) S
    dsimp [gap] at heq hg
    nlinarith

def oneHot {m : ℕ} (a : Fin m) : Fin m → Bool := fun i ↦ decide (i = a)

theorem linear_oneHot {m : ℕ} (v : Fin m → ℝ) (a : Fin m) :
    linear v (oneHot a) = 2 * v a - ∑ i, v i := by
  classical
  have hi (i) : v i * spin (oneHot a i) = (if i = a then 2 * v i else 0) - v i := by
    by_cases h : i = a <;> simp [oneHot, spin, h]
    ring
  simp [linear, hi, Finset.sum_sub_distrib]

theorem oneHot_denominator {m : ℕ} (d : Fin m → ℝ) (l₀ r₀ : ℝ) (a : Fin m) :
    baseD l₀ r₀ + (∑ i, controlB d l₀ r₀ i) + linear (controlB d l₀ r₀) (oneHot a) = d a := by
  rw [linear_oneHot]
  dsimp [controlB]
  ring

theorem oneHot_numerator {m : ℕ} (d p : Fin m → ℝ) (l₀ r₀ k ell : ℝ) (a : Fin m) :
    k * (baseP l₀ r₀ + ∑ i, controlS p l₀ r₀ i) +
      ell * (baseD l₀ r₀ + ∑ i, controlB d l₀ r₀ i) +
      linear (fun i ↦ k * controlS p l₀ r₀ i + ell * controlB d l₀ r₀ i) (oneHot a) =
        k * p a + ell * d a := by
  rw [linear_oneHot]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  dsimp [controlB, controlS]
  ring

end
end HeadComplexity.PureRoPECenteredConstruction
