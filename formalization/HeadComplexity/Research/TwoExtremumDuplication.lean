import HeadComplexity.Research.FullCubeNormOptimization

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.TwoExtremumDuplication

/-- Two affine forms with distinct ratios at two endpoints span arbitrary
values at those endpoints. Any functional vanishing on both forms and on the
common endpoint kernel therefore vanishes on the entire ambient subspace. -/
theorem two_endpoint_annihilator {X : Type*}
    (V : Submodule ℝ (X → ℝ)) (A B : X → ℝ) (p q : X)
    (hA : A ∈ V) (hB : B ∈ V)
    (hdet : A p*B q-A q*B p ≠ 0)
    (L : (X → ℝ) →ₗ[ℝ] ℝ) (hLA : L A = 0) (hLB : L B = 0)
    (hzero : ∀ E ∈ V, E p = 0 → E q = 0 → L E = 0) :
    ∀ E ∈ V, L E = 0 := by
  intro E hE
  let det := A p*B q-A q*B p
  let a := (E p*B q-E q*B p)/det
  let b := (A p*E q-A q*E p)/det
  have hd : det ≠ 0 := hdet
  let E₀ : X → ℝ := E-a•A-b•B
  have hE₀ : E₀ ∈ V := V.sub_mem (V.sub_mem hE (V.smul_mem a hA)) (V.smul_mem b hB)
  have hp : E₀ p = 0 := by
    change E p - a*A p - b*B p = 0
    dsimp [a,b]
    field_simp [hd]
    dsimp [det]
    ring
  have hq : E₀ q = 0 := by
    change E q - a*A q - b*B q = 0
    dsimp [a,b]
    field_simp [hd]
    dsimp [det]
    ring
  have hz := hzero E₀ hE₀ hp hq
  simpa only [E₀, map_sub, map_smul, hLA, hLB, smul_eq_mul, mul_zero, sub_zero] using hz

/-- A nonconstant ratio's distinct extrema give the required determinant. -/
theorem endpoint_det_ne_zero {X : Type*} (A B : X → ℝ) (p q : X) (u l : ℝ)
    (hBp : B p ≠ 0) (hBq : B q ≠ 0) (hul : u ≠ l)
    (hp : A p = u*B p) (hq : A q = l*B q) :
    A p*B q-A q*B p ≠ 0 := by
  rw [hp,hq]
  have he : u*B p*B q-l*B q*B p = (u-l)*B p*B q := by ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hul) hBp) hBq

/-- The algebraic core of the two-extremum duplication test. The functional
is the residual signed Hessian row; its first-order annihilation of A and B
and its endpoint-kernel annihilation are explicit hypotheses. -/
theorem ratio_endpoint_annihilator {X : Type*}
    (V : Submodule ℝ (X → ℝ)) (A B : X → ℝ) (p q : X) (u l : ℝ)
    (hA : A ∈ V) (hB : B ∈ V)
    (hBp : B p ≠ 0) (hBq : B q ≠ 0) (hul : u ≠ l)
    (hp : A p = u*B p) (hq : A q = l*B q)
    (L : (X → ℝ) →ₗ[ℝ] ℝ) (hLA : L A = 0) (hLB : L B = 0)
    (hzero : ∀ E ∈ V, E p = 0 → E q = 0 → L E = 0) :
    ∀ E ∈ V, L E = 0 :=
  two_endpoint_annihilator V A B p q hA hB
    (endpoint_det_ne_zero A B p q u l hBp hBq hul hp hq) L hLA hLB hzero

end HeadComplexity.TwoExtremumDuplication
