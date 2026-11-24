import HeadComplexity.Research.SplitSmoothableCapacity
import HeadComplexity.Research.FeasibleChartEntropy
import HeadComplexity.Research.ConditionalMarginLowerBounds

set_option linter.style.header false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.SplitSmoothableEstimates
open scoped BigOperators
open SplitSmoothableCapacity

variable {n G q : ℕ}

def coarseWeight (n G q : ℕ) : Parameter n G q → ℕ
  | Sum.inl _ => G * (q+1)
  | Sum.inr (_, Sum.inl (false, none, _)) => 1
  | Sum.inr (_, Sum.inl _) => G
  | Sum.inr (_, Sum.inr _) => 1

theorem coarseWeight_le (k : Fin G → Fin q → ℕ)
    (hkpos : ∀ g i, 0 < k g i) (hk : ∀ g i, k g i ≤ q)
    (i : Parameter n G q) : coarseWeight n G q i ≤ weight n G q k i := by
  rcases i with u | ⟨g, v⟩
  · rfl
  · rcases v with ⟨kind, j, a⟩ | ij
    · cases kind
      · cases j with
        | none => rfl
        | some j =>
          change G ≤ G * k g j + 1
          have hh : G * 1 ≤ G * k g j := Nat.mul_le_mul_left G (hkpos g j)
          omega
      · cases j with
        | none =>
          change G ≤ G * (q+1)
          nlinarith
        | some j =>
          change G ≤ G * (q+1-k g j)
          have hh : 1 ≤ q+1-k g j := by have := hk g j; omega
          simpa using Nat.mul_le_mul_left G hh
    · rfl

theorem prod_coarseWeight :
    (∏ i : Parameter n G q, (coarseWeight n G q i : ℝ)) =
      (G*(q+1) : ℕ) * (G : ℝ) ^ (G*(2*q+1)*(n+1)) := by
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type,
    Fintype.prod_bool, Fintype.prod_option, Fintype.card_unique,
    coarseWeight, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    pow_one, one_mul, mul_one, Nat.cast_one, one_pow]
  simp only [← pow_succ', ← pow_mul, ← pow_add]
  congr 1
  congr 1
  ring

theorem prod_weight_lower (k : Fin G → Fin q → ℕ)
    (hkpos : ∀ g i, 0 < k g i) (hk : ∀ g i, k g i ≤ q) :
    (G*(q+1) : ℕ) * (G : ℝ) ^ (G*(2*q+1)*(n+1)) ≤
      ∏ i : Parameter n G q, (weight n G q k i : ℝ) := by
  rw [← prod_coarseWeight]
  apply Finset.prod_le_prod₀
  · intro i _
    positivity
  · intro i _
    exact_mod_cast coarseWeight_le k hkpos hk i


def parameterCount (n G q : ℕ) : ℕ :=
  1 + 2*(n+1)*(G*(q+1)) + G*(q+1)^2

def clusterEntropy (n G q : ℕ) : ℝ :=
  parameterCount n G q *
    Real.log (4*Real.exp 1*(3+2*(q+1))*(2:ℝ)^n / parameterCount n G q) +
  (2*(n+1)*(G*(q+1)) : ℕ) * Real.log (q+1) +
  ((n+1)*G+G*(q+1)^2 : ℕ) * Real.log (G*(q+1))

private theorem cancellation_identity (A G Q : ℝ) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (a b : ℕ) :
    (A*(G*Q))^(1+a+b) / ((G*Q)*G^a) =
      A^(1+a+b) * (G*Q)^b * Q^a := by
  simp only [mul_pow, pow_add, pow_one]
  field_simp

theorem card_smoothableFunctions_le_coarse (k : Fin G → Fin q → ℕ)
    (hG : 0 < G) (hkpos : ∀ g i, 0 < k g i) (hk : ∀ g i, k g i ≤ q)
    (hp : parameterCount n G q ≤ 2^n) :
    ((smoothableFunctions n G q k).ncard : ℝ) ≤
      (4*Real.exp 1*(3+2*(q+1))*(2:ℝ)^n / parameterCount n G q)^parameterCount n G q *
      (q+1 : ℝ)^(2*(n+1)*(G*(q+1))) *
      (G*(q+1) : ℕ)^((n+1)*G+G*(q+1)^2) := by
  let K : ℕ := G*(q+1)
  let a : ℕ := G*(2*q+1)*(n+1)
  let b : ℕ := (n+1)*G+G*(q+1)^2
  let A : ℝ := 4*Real.exp 1*(3+2*(q+1))*(2:ℝ)^n / parameterCount n G q
  have hGr : (0:ℝ) < G := by exact_mod_cast hG
  have hQr : (0:ℝ) < q+1 := by positivity
  have hK : (0:ℝ) < K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A,parameterCount]; positivity
  have hab : parameterCount n G q = 1+a+b := by dsimp [parameterCount,a,b]; ring
  have ha : a ≤ 2*(n+1)*(G*(q+1)) := by dsimp [a]; nlinarith
  have hQone : (1:ℝ) ≤ q+1 := by
    have hh : (0:ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hpow : (q+1:ℝ)^a ≤ (q+1:ℝ)^(2*(n+1)*(G*(q+1))) :=
    pow_le_pow_right₀ hQone ha
  have hcount := card_smoothableFunctions_le k hG hk hp
  have hw := prod_weight_lower (n := n) k hkpos hk
  have hden : 0 < (K:ℝ)*(G:ℝ)^a := mul_pos hK (pow_pos hGr _)
  have hnum : 0 ≤
      (4*Real.exp 1*((3+2*(q+1))*(G*(q+1)) : ℕ)*(2:ℝ)^n /
        (1+2*(n+1)*(G*(q+1))+G*(q+1)^2 : ℕ))^
        (1+2*(n+1)*(G*(q+1))+G*(q+1)^2) := by positivity
  have hle := div_le_div_of_nonneg_left hnum hden hw
  have hrewrite :
      4*Real.exp 1*((3+2*(q+1))*(G*(q+1)) : ℕ)*(2:ℝ)^n /
        (1+2*(n+1)*(G*(q+1))+G*(q+1)^2 : ℕ) = A*(G*(q+1)) := by
    dsimp [A,parameterCount]
    push_cast
    ring
  calc
    _ ≤ _ := hcount.trans hle
    _ = A^parameterCount n G q * (G*(q+1):ℝ)^b * (q+1:ℝ)^a := by
      rw [hrewrite]
      change (A*((G:ℝ)*(q+1)))^parameterCount n G q /
        ((K:ℝ)*(G:ℝ)^a) = _
      rw [hab]
      dsimp [K]
      push_cast
      exact cancellation_identity A G (q+1) hGr.ne' hQr.ne' a b
    _ ≤ A^parameterCount n G q * (G*(q+1):ℝ)^b *
        (q+1:ℝ)^(2*(n+1)*(G*(q+1))) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by dsimp [A,b]; push_cast; ring

theorem card_smoothableFunctions_le_exp (k : Fin G → Fin q → ℕ)
    (hG : 0 < G) (hkpos : ∀ g i, 0 < k g i) (hk : ∀ g i, k g i ≤ q)
    (hp : parameterCount n G q ≤ 2^n) :
    ((smoothableFunctions n G q k).ncard : ℝ) ≤ Real.exp (clusterEntropy n G q) := by
  calc
    _ ≤ _ := card_smoothableFunctions_le_coarse k hG hkpos hk hp
    _ = _ := by
      have hG' : (0:ℝ) < G := by exact_mod_cast hG
      have hp' : (0:ℝ) < parameterCount n G q := by
        dsimp [parameterCount]
        positivity
      simp only [clusterEntropy, Real.exp_add, Real.exp_nat_mul]
      rw [Real.exp_log (by positivity), Real.exp_log (by positivity),
        Real.exp_log (by positivity)]
      push_cast
      rfl

abbrev OrderAssignment (G q : ℕ) := Fin G → Fin q → Fin q

def orderValues (a : OrderAssignment G q) : Fin G → Fin q → ℕ :=
  fun g i => (a g i).val+1

def smoothableUnion (n G q : ℕ) : Set ((Fin n → Bool) → Bool) :=
  ⋃ a : OrderAssignment G q, smoothableFunctions n G q (orderValues a)

def unionEntropy (n G q : ℕ) : ℝ :=
  clusterEntropy n G q + (G*q : ℕ)*Real.log (q+1)

theorem card_smoothableUnion_le_exp (hG : 0 < G)
    (hp : parameterCount n G q ≤ 2^n) :
    ((smoothableUnion n G q).ncard : ℝ) ≤ Real.exp (unionEntropy n G q) := by
  classical
  have hc (a : OrderAssignment G q) :
      ((smoothableFunctions n G q (orderValues a)).ncard : ℝ) ≤
        Real.exp (clusterEntropy n G q) := by
    apply card_smoothableFunctions_le_exp _ hG
    · intro g i
      exact Nat.succ_pos _
    · intro g i
      exact Nat.succ_le_of_lt (a g i).isLt
    · exact hp
  have hs : ((smoothableUnion n G q).ncard : ℝ) ≤
      ∑ a : OrderAssignment G q,
        ((smoothableFunctions n G q (orderValues a)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_iUnion_le_of_fintype
      (fun a : OrderAssignment G q => smoothableFunctions n G q (orderValues a))
  calc
    _ ≤ _ := hs
    _ ≤ ∑ _a : OrderAssignment G q, Real.exp (clusterEntropy n G q) :=
      Finset.sum_le_sum fun a _ => hc a
    _ = (q:ℝ)^(G*q) * Real.exp (clusterEntropy n G q) := by
      simp [OrderAssignment, ← pow_mul, Nat.mul_comm q G]
    _ ≤ (q+1:ℝ)^(G*q) * Real.exp (clusterEntropy n G q) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _)
        (Real.exp_pos _).le
    _ = Real.exp (unionEntropy n G q) := by
      simp only [unionEntropy, Real.exp_add, Real.exp_nat_mul]
      rw [Real.exp_log (by positivity)]
      ring

/-- A real-variable estimate covering square-root and logarithmic cluster
lengths. The coefficient count includes all matrix entries and order choices. -/
theorem uniform_cluster_entropy_bound {r N g Q t : ℝ}
    (hr : 32 ≤ r) (hN : 0 < N) (hg : 1 ≤ g) (hQ : 1 ≤ Q)
    (htlo : Real.log (r+1) ≤ t) (hQt : Q ≤ t) (htr : t ≤ r)
    (hrQt : r ≤ Q*t) (hlogK : Real.log (g*Q) ≤ r)
    (hbudget : g*Q ≤ N/(1000*r*t)) :
    let p := 1+2*(r+1)*(g*Q)+(g*Q)*Q
    p*Real.log (4*Real.exp 1*(3+2*Q)*N/p) +
      2*(r+1)*(g*Q)*Real.log Q +
      ((r+1)*g+(g*Q)*Q)*Real.log (g*Q) +
      g*(Q-1)*Real.log Q ≤ 8*N/25 := by
  dsimp only
  let K := g*Q
  let p := 1+2*(r+1)*K+K*Q
  have hr0 : 0 < r := by linarith
  have ht0 : 0 < t := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hK1 : 1 ≤ K := by dsimp [K]; nlinarith
  have hK0 : 0 < K := by linarith
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hb : 1000*r*t*K ≤ N := by
    have hh := (le_div_iff₀ (by positivity : 0 < 1000*r*t)).mp hbudget
    dsimp [K]
    nlinarith
  have hp4 : p ≤ 4*r*K := by
    dsimp [p]
    have hh := mul_le_mul_of_nonneg_left (hQt.trans htr) hK0.le
    nlinarith
  have hpbudget : p ≤ N/(25*t) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hp4 (by positivity : 0 ≤ 25*t)
    nlinarith
  have he : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht0.le
  have hdegree : 3+2*Q ≤ 6*(r+1)*Real.exp t := by
    have hh := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ 6*(r+1))
    nlinarith
  have hmain := MarginCapacityEstimates.entropy_bound hr hN (le_refl (0:ℝ))
    hp0 (by linarith : 0 < 3+2*Q) htlo htr
    (by positivity) hpbudget hdegree
  simp only [zero_mul, zero_add] at hmain
  have hlogQ : Real.log Q ≤ t :=
    (Real.log_le_log (by linarith) (by linarith : Q ≤ r+1)).trans htlo
  have hterm1 : 2*(r+1)*K*Real.log Q ≤ 4*r*K*t := by
    have hh := mul_le_mul_of_nonneg_left hlogQ (by positivity : 0 ≤ 2*(r+1)*K)
    have hh' : 2*(r+1)*K*t ≤ 4*r*K*t := by nlinarith [mul_nonneg hK0.le ht0.le]
    exact hh.trans hh'
  have hb1 : (r+1)*g*r ≤ 2*r*K*t := by
    have hh := mul_le_mul_of_nonneg_left hrQt (by positivity : 0 ≤ 2*r*g)
    dsimp [K]
    nlinarith
  have hb2 : K*Q*r ≤ r*K*t := by
    have hh := mul_le_mul_of_nonneg_left hQt (by positivity : 0 ≤ r*K)
    nlinarith
  have hterm2 : ((r+1)*g+K*Q)*Real.log K ≤ 3*r*K*t := by
    have hh := mul_le_mul_of_nonneg_left hlogK
      (by positivity : 0 ≤ (r+1)*g+K*Q)
    dsimp [K] at hh ⊢
    dsimp [K] at hb1 hb2
    nlinarith
  have hterm3 : g*(Q-1)*Real.log Q ≤ r*K*t := by
    have hh := mul_le_mul_of_nonneg_left hlogQ
      (mul_nonneg hg0 (by linarith : 0 ≤ Q-1))
    have hh' : g*(Q-1)*t ≤ r*K*t := by
      dsimp [K]
      nlinarith [mul_nonneg hg0 ht0.le, mul_nonneg hK0.le ht0.le]
    exact hh.trans hh'
  change p*Real.log (4*Real.exp 1*(3+2*Q)*N/p) +
      2*(r+1)*K*Real.log Q + ((r+1)*g+K*Q)*Real.log K +
      g*(Q-1)*Real.log Q ≤ 8*N/25
  nlinarith

theorem unionEntropy_at_budget {t : ℝ} (hn : 32 ≤ n) (hG : 0 < G)
    (htlo : Real.log ((n:ℝ)+1) ≤ t) (hQt : (q:ℝ)+1 ≤ t) (htn : t ≤ n)
    (hnQt : (n:ℝ) ≤ ((q:ℝ)+1)*t)
    (hbudget : (G*(q+1):ℕ) ≤ (2:ℝ)^n/(1000*n*t)) :
    unionEntropy n G q ≤ 8*(2:ℝ)^n/25 := by
  have hn' : (32:ℝ) ≤ n := by exact_mod_cast hn
  have hG' : (1:ℝ) ≤ G := by exact_mod_cast hG
  have hQ' : (1:ℝ) ≤ q+1 := by
    have hh : (0:ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have ht1 : 1 ≤ t := hQ'.trans hQt
  have hK0 : (0:ℝ) < G*(q+1) := by positivity
  have hKN : (G:ℝ)*(q+1) ≤ (2:ℝ)^n := by
    have hh : (1:ℝ) ≤ 1000*n*t := by nlinarith
    have h := hbudget.trans (div_le_self (by positivity) hh)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h
  have hlogK : Real.log ((G:ℝ)*(q+1)) ≤ n := by
    calc
      _ ≤ Real.log ((2:ℝ)^n) := Real.log_le_log hK0 hKN
      _ = (n:ℝ)*Real.log 2 := Real.log_pow _ _
      _ ≤ n := by
        have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2))
          (by positivity : (0:ℝ) ≤ n)
        norm_num at hh ⊢
        exact hh
  have h := uniform_cluster_entropy_bound (N := (2:ℝ)^n) hn' (by positivity) hG' hQ'
    htlo hQt htn hnQt hlogK (by exact_mod_cast hbudget)
  simpa only [unionEntropy,clusterEntropy,parameterCount,Nat.cast_add,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat,add_sub_cancel_right,pow_two,mul_assoc] using h

theorem parameterCount_le_at_budget {t : ℝ} (hn : 32 ≤ n) (hG : 0 < G)
    (hQt : (q:ℝ)+1 ≤ t) (htn : t ≤ n)
    (hbudget : (G*(q+1):ℕ) ≤ (2:ℝ)^n/(1000*n*t)) :
    parameterCount n G q ≤ 2^n := by
  have hn' : (32:ℝ) ≤ n := by exact_mod_cast hn
  have hG' : (1:ℝ) ≤ G := by exact_mod_cast hG
  have hq : (0:ℝ) ≤ q := Nat.cast_nonneg q
  have ht1 : 1 ≤ t := by linarith
  have hK1 : (1:ℝ) ≤ G*(q+1) := by nlinarith
  have hb : 1000*n*t*((G:ℝ)*(q+1)) ≤ (2:ℝ)^n := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<1000*n*t)).mp hbudget
    push_cast at hh
    nlinarith
  have hp4 : (parameterCount n G q:ℝ) ≤ 4*n*((G:ℝ)*(q+1)) := by
    dsimp [parameterCount]
    push_cast
    have hh := mul_le_mul_of_nonneg_left (hQt.trans htn)
      (by positivity : (0:ℝ) ≤ G*(q+1))
    nlinarith
  have hpN : (parameterCount n G q:ℝ) ≤ (2:ℝ)^n := by
    have hh := mul_le_mul_of_nonneg_left ht1
      (by positivity : (0:ℝ) ≤ 1000*n*((G:ℝ)*(q+1)))
    nlinarith
  exact_mod_cast hpN

theorem card_smoothableUnion_le_exp_at_budget {t : ℝ} (hn : 32 ≤ n) (hG : 0 < G)
    (htlo : Real.log ((n:ℝ)+1) ≤ t) (hQt : (q:ℝ)+1 ≤ t) (htn : t ≤ n)
    (hnQt : (n:ℝ) ≤ ((q:ℝ)+1)*t)
    (hbudget : (G*(q+1):ℕ) ≤ (2:ℝ)^n/(1000*n*t)) :
    ((smoothableUnion n G q).ncard : ℝ) ≤ Real.exp (8*(2:ℝ)^n/25) := by
  exact (card_smoothableUnion_le_exp hG (parameterCount_le_at_budget hn hG hQt htn hbudget)).trans
    (Real.exp_le_exp.mpr (unionEntropy_at_budget hn hG htlo hQt htn hnQt hbudget))

theorem card_smoothableUnion_le_half_tables {t : ℝ} (hn : 32 ≤ n) (hG : 0 < G)
    (htlo : Real.log ((n:ℝ)+1) ≤ t) (hQt : (q:ℝ)+1 ≤ t) (htn : t ≤ n)
    (hnQt : (n:ℝ) ≤ ((q:ℝ)+1)*t)
    (hbudget : (G*(q+1):ℕ) ≤ (2:ℝ)^n/(1000*n*t)) :
    (smoothableUnion n G q).ncard ≤ 2^(2^(n-1)) := by
  have hc := card_smoothableUnion_le_exp_at_budget hn hG htlo hQt htn hnQt hbudget
  have hpow : (2:ℝ)^n = 2*(2:ℝ)^(n-1) := by
    conv_lhs => rw [show n = (n-1)+1 by omega,pow_succ]
    ring
  have hlog : (16:ℝ)/25 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he : 8*(2:ℝ)^n/25 ≤ ((2^(n-1):ℕ):ℝ)*Real.log 2 := by
    rw [hpow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hlog (show 0 ≤ (2:ℝ)^(n-1) by positivity)]
  have hh : ((smoothableUnion n G q).ncard:ℝ) ≤ (2:ℝ)^(2^(n-1)) := by
    calc
      _ ≤ _ := hc
      _ ≤ Real.exp (((2^(n-1):ℕ):ℝ)*Real.log 2) := Real.exp_le_exp.mpr he
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  exact_mod_cast hh

theorem sqrt_cluster_range (hn : 32 ≤ n) :
    Real.log ((n:ℝ)+1) ≤ 2*Real.sqrt n ∧
    ((⌊Real.sqrt (n:ℝ)⌋₊:ℝ)+1 ≤ 2*Real.sqrt n) ∧
    2*Real.sqrt n ≤ n ∧
    (n:ℝ) ≤ ((⌊Real.sqrt (n:ℝ)⌋₊:ℝ)+1)*(2*Real.sqrt n) := by
  have hn' : (32:ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sqrt_nonneg (n:ℝ)
  have hs2 : 2 ≤ Real.sqrt (n:ℝ) := by
    have hh := Real.sqrt_le_sqrt (by linarith : (4:ℝ) ≤ n)
    norm_num at hh
    exact hh
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hf := Nat.floor_le hs
  have hf' := Nat.lt_floor_add_one (Real.sqrt (n:ℝ))
  refine ⟨?_,?_,?_,?_⟩
  · have hh := (MarginCapacityEstimates.sqrt_test_range hn).1
    linarith
  · linarith
  · nlinarith
  · nlinarith

theorem card_smoothableUnion_sqrt_scale (hn : 32 ≤ n) (hG : 0 < G)
    (hbudget : (G*(⌊Real.sqrt (n:ℝ)⌋₊+1):ℕ) ≤
      (2:ℝ)^n/(2000*n*Real.sqrt n)) :
    (smoothableUnion n G ⌊Real.sqrt (n:ℝ)⌋₊).ncard ≤ 2^(2^(n-1)) := by
  obtain ⟨h1,h2,h3,h4⟩ := sqrt_cluster_range hn
  apply card_smoothableUnion_le_half_tables hn hG h1 h2 h3 h4
  convert hbudget using 1 <;> ring

theorem logarithmic_cluster_range (hn : 32 ≤ n) :
    Real.log ((n:ℝ)+1) ≤ 2*((n:ℝ)/Real.log n) ∧
    ((⌊Real.log (n:ℝ)⌋₊:ℝ)+1 ≤ 2*((n:ℝ)/Real.log n)) ∧
    2*((n:ℝ)/Real.log n) ≤ n ∧
    (n:ℝ) ≤ ((⌊Real.log (n:ℝ)⌋₊:ℝ)+1)*(2*((n:ℝ)/Real.log n)) := by
  have hn' : (32:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by positivity
  have hl2 : 2 ≤ Real.log (n:ℝ) := by
    apply (Real.le_log_iff_exp_le hn0).mpr
    have hh : Real.exp (2:ℝ) < 9 := by
      rw [show (2:ℝ) = 1+1 by norm_num,Real.exp_add]
      nlinarith [Real.exp_one_lt_three,Real.exp_pos (1:ℝ)]
    linarith
  have hl0 : 0 < Real.log (n:ℝ) := by linarith
  have ht0 : 0 < (n:ℝ)/Real.log n := div_pos hn0 hl0
  have hs := (MarginCapacityEstimates.sqrt_test_range hn).1
  have hlroot : Real.log (n:ℝ) ≤ Real.sqrt n :=
    (Real.log_le_log hn0 (by linarith : (n:ℝ) ≤ n+1)).trans hs
  have hlsq : (Real.log (n:ℝ))^2 ≤ n := by
    nlinarith [Real.sq_sqrt hn0.le]
  have hllt : Real.log (n:ℝ) ≤ (n:ℝ)/Real.log n :=
    (le_div_iff₀ hl0).mpr (by nlinarith)
  have hf := Nat.floor_le hl0.le
  have hf' := Nat.lt_floor_add_one (Real.log (n:ℝ))
  refine ⟨?_,?_,?_,?_⟩
  · have hh := (MarginCapacityEstimates.logarithmic_test_range hn).1
    linarith
  · linarith
  · have hh : 2*(n:ℝ)/Real.log n ≤ (n:ℝ) :=
      (div_le_iff₀ hl0).mpr (by nlinarith)
    simpa only [mul_div_assoc] using hh
  · have heq : ((n:ℝ)/Real.log n)*Real.log n = n := div_mul_cancel₀ _ hl0.ne'
    nlinarith

theorem card_smoothableUnion_logarithmic_scale (hn : 32 ≤ n) (hG : 0 < G)
    (hbudget : (G*(⌊Real.log (n:ℝ)⌋₊+1):ℕ) ≤
      (2:ℝ)^n*Real.log n/(2000*(n:ℝ)^2)) :
    (smoothableUnion n G ⌊Real.log (n:ℝ)⌋₊).ncard ≤ 2^(2^(n-1)) := by
  obtain ⟨h1,h2,h3,h4⟩ := logarithmic_cluster_range hn
  apply card_smoothableUnion_le_half_tables hn hG h1 h2 h3 h4
  convert hbudget using 1 <;> field_simp <;> ring

/-- Only the universally low-margin truth tables need cluster access in this
alternative. A badly conditioned chosen representation does not establish it. -/
theorem worstCase_gt_of_lowMargin_access {H K : ℕ} {gamma t : ℝ}
    (hn : 32 ≤ n) (hG : 0 < G)
    (htlo : Real.log ((n:ℝ)+1) ≤ t) (hQt : (q:ℝ)+1 ≤ t) (htn : t ≤ n)
    (hnQt : (n:ℝ) ≤ ((q:ℝ)+1)*t)
    (hbudget : (G*(q+1):ℕ) ≤ (2:ℝ)^n/(1000*n*t))
    (hhigh : (RelativeMarginQuantifiers.highMarginFunctions n K gamma).ncard ≤ 2^(2^(n-1)))
    (haccess : RelativeMarginQuantifiers.allRepresentationsLowMargin n H K gamma ⊆
      smoothableUnion n G q) : H < worstCaseHeadComplexity n := by
  apply ConditionalMarginLowerBounds.worstCase_gt_of_two_half_counts (by omega) hhigh
  exact (Set.ncard_le_ncard haccess (Set.toFinite _)).trans
    (card_smoothableUnion_le_half_tables hn hG htlo hQt htn hnQt hbudget)

/-- This premise requires access for the whole truth table, with all original
unrestricted representations in scope. It is not supplied by the cluster count. -/
def HasSmoothableAccess (n H G q : ℕ) : Prop :=
  headComputableFunctions n H ⊆ smoothableUnion n G q

theorem worstCase_gt_of_smoothable_access {H : ℕ} (hG : 0 < G)
    (hp : parameterCount n G q ≤ 2^n)
    (hE : unionEntropy n G q ≤ 8*(2:ℝ)^n/25)
    (haccess : HasSmoothableAccess n H G q) : H < worstCaseHeadComplexity n := by
  apply FeasibleChartEntropy.worstCase_gt_of_card_le_exp
  have hs : ((headComputableFunctions n H).ncard : ℝ) ≤
      ((smoothableUnion n G q).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard haccess (Set.toFinite _)
  exact hs.trans ((card_smoothableUnion_le_exp hG hp).trans (Real.exp_le_exp.mpr hE))

end HeadComplexity.SplitSmoothableEstimates

