import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Algebraic ingredients for projectively normalized critical points

These declarations check a transverse kernel, the selected pair reconstruction,
and the Schur-complement kernel calculation in the accompanying written proof.
They do not formalize its analytic implicit-function theorem or prove a head
complexity lower bound.
-/

namespace HeadComplexity.ProjectiveCriticalPoints

open scoped BigOperators

theorem transverse_kernel {d : ℕ} (hd : 2 ≤ d) (A : Fin d → ℝ) (N : ℝ)
    (hN : N ≠ 0) (hsum : ∑ i, A i = N + d - 1) (v : Fin d → ℝ)
    (hv : ∀ i, -v i + A i / N * (∑ j, v j) = 0) : v = 0 := by
  classical
  let T : ℝ := ∑ i, v i
  have hi (i : Fin d) : v i = A i / N * T := by
    have := hv i
    change -v i + A i / N * T = 0 at this
    linarith
  have ht : T = (∑ i, A i) / N * T := by
    calc
      T = ∑ i, A i / N * T := Finset.sum_congr rfl (fun i _ ↦ hi i)
      _ = (∑ i, A i) / N * T := by rw [← Finset.sum_mul, ← Finset.sum_div]
  rw [hsum] at ht
  have hz : ((d : ℝ) - 1) * T = 0 := by
    field_simp [hN] at ht
    nlinarith
  have hd' : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hT : T = 0 := (mul_eq_zero.mp hz).resolve_left (by linarith)
  funext i
  simpa [hT] using hi i

theorem selected_pair_kernel {d k : ℕ} (hd : 0 < d) (hk : 2 ≤ k)
    (a : Fin d → ℝ) (t : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ j, 0 < t j)
    (da : Fin d → ℝ) (dt : Fin k → ℝ)
    (hfirst : ∀ j, a ⟨0, hd⟩ * dt j = (1 + t j) * da ⟨0, hd⟩)
    (hother : ∀ i, a i * dt ⟨0, by omega⟩ =
      (1 + t ⟨0, by omega⟩) * da i)
    (hpair : dt ⟨0, by omega⟩ + dt ⟨1, by omega⟩ = 0) :
    da = 0 ∧ dt = 0 := by
  let i0 : Fin d := ⟨0, hd⟩
  let j0 : Fin k := ⟨0, by omega⟩
  let j1 : Fin k := ⟨1, by omega⟩
  have h0 := hfirst j0
  have h1 := hfirst j1
  have hp : dt j0 + dt j1 = 0 := hpair
  have ht0 := ht j0
  have ht1 := ht j1
  have heq : (2 + t j0 + t j1) * da i0 = 0 := by
    change a i0 * dt j0 = (1 + t j0) * da i0 at h0
    change a i0 * dt j1 = (1 + t j1) * da i0 at h1
    have hprod : a i0 * (dt j0 + dt j1) = 0 := by rw [hp, mul_zero]
    nlinarith [hprod]
  have ha0 : da i0 = 0 := (mul_eq_zero.mp heq).resolve_left (by linarith)
  have hdt : dt = 0 := by
    funext j
    have hj := hfirst j
    change a i0 * dt j = (1 + t j) * da i0 at hj
    rw [ha0, mul_zero] at hj
    exact (mul_eq_zero.mp hj).resolve_left (ne_of_gt (ha i0))
  refine ⟨?_, hdt⟩
  funext i
  have hi := hother i
  rw [hdt] at hi
  simp only [Pi.zero_apply, mul_zero] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left (by linarith)

theorem schur_kernel
    {U V : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    (C : V →ₗ[ℝ] U) (Ct : U →ₗ[ℝ] V) (D : V →ₗ[ℝ] V)
    (lam : ℝ) (hlam : lam ≠ 0)
    (hinj : Function.Injective (fun v : V ↦ D v + lam⁻¹ • Ct (C v)))
    (u : U) (v : V) (hfirst : -lam • u + C v = 0)
    (hsecond : Ct u + D v = 0) : u = 0 ∧ v = 0 := by
  have hc : C v = lam • u := by
    have := eq_neg_of_add_eq_zero_left (add_comm (-lam • u) (C v) ▸ hfirst)
    simpa using this
  have hu : u = lam⁻¹ • C v := by
    rw [hc, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have hz : D v + lam⁻¹ • Ct (C v) = D 0 + lam⁻¹ • Ct (C 0) := by
    rw [hu, map_smul] at hsecond
    simpa [add_comm] using hsecond
  have hv : v = 0 := hinj hz
  refine ⟨?_, hv⟩
  simpa [hv] using hu

theorem projection_term_vanishes
    {U V : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    (Jt : U →ₗ[ℝ] V) (K w : U) (c : ℝ) (hK : Jt K = 0) :
    Jt (w - c • K) = Jt w := by
  simp [map_sub, map_smul, hK]

#print axioms transverse_kernel
#print axioms selected_pair_kernel
#print axioms schur_kernel
#print axioms projection_term_vanishes

end HeadComplexity.ProjectiveCriticalPoints
