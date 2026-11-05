module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option autoImplicit false

/-!
# Positive hollow matrices of rank three
A nonprincipal four-by-four determinant identity gives an explicit Lorentz
factorization.  Positivity selects one sheet of the null cone, which can then
be normalized to the unit circle.  The angles are actual complex arguments.
-/
namespace VolumeVerification.CircleFactorization
open scoped Matrix BigOperators

private theorem bordered_det
    (a b c u v w u' v' w' p : ℝ) :
    Matrix.det !![0, a, b, u';
                 a, 0, c, v';
                 b, c, 0, w';
                 u, v, w, p] =
      2*a*b*c*p -
      (-c^2*u*u' - b^2*v*v' - a^2*w*w' +
        b*c*(u*v' + v*u') + a*c*(u*w' + w*u') + a*b*(v*w' + w*v')) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  ring

private theorem lorentz_identity
    (a b c r u v w u' v' w' : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hr : r ≠ 0) (hrsq : a*r^2 = 2*b*c) :
    ((u + 2*v/a)/2) * ((u' + 2*v'/a)/2) -
      ((2*v/a - u)/2) * ((2*v'/a - u')/2) -
      ((c*u + b*v - a*w)/(a*r)) * ((c*u' + b*v' - a*w')/(a*r)) =
      (-c^2*u*u' - b^2*v*v' - a^2*w*w' +
        b*c*(u*v' + v*u') + a*c*(u*w' + w*u') + a*b*(v*w' + w*v')) /
        (2*a*b*c) := by
  have hd : (a*r)*(a*r) = 2*a*b*c := by
    calc
      (a*r)*(a*r) = a*(a*r^2) := by ring
      _ = 2*a*b*c := by rw [hrsq]; ring
  have hy :
      ((c*u + b*v - a*w)/(a*r)) * ((c*u' + b*v' - a*w')/(a*r)) =
        ((c*u + b*v - a*w)*(c*u' + b*v' - a*w'))/(2*a*b*c) := by
    rw [div_mul_div_comm, hd]
  rw [hy]
  field_simp [ha, hb, hc]
  ring

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem four_minor_zero (P : Matrix ι ι ℝ) (hrank : P.rank ≤ 3)
    (rows cols : Fin 4 → ι) :
    (P.submatrix rows cols).det = 0 := by
  by_contra hdet
  have hr := Matrix.rank_of_det_ne_zero hdet
  have hle := Matrix.rank_submatrix_le P rows cols
  norm_num only [Fintype.card_fin] at hr
  omega

theorem schur_formula (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hrank : P.rank ≤ 3) (i₀ i₁ i₂ i j : ι) :
    2 * P i₀ i₁ * P i₀ i₂ * P i₁ i₂ * P i j =
      -(P i₁ i₂)^2 * P i₀ i * P i₀ j -
        (P i₀ i₂)^2 * P i₁ i * P i₁ j -
        (P i₀ i₁)^2 * P i₂ i * P i₂ j +
        P i₀ i₂ * P i₁ i₂ * (P i₀ i * P i₁ j + P i₁ i * P i₀ j) +
        P i₀ i₁ * P i₁ i₂ * (P i₀ i * P i₂ j + P i₂ i * P i₀ j) +
        P i₀ i₁ * P i₀ i₂ * (P i₁ i * P i₂ j + P i₂ i * P i₁ j) := by
  have hz := four_minor_zero P hrank ![i₀,i₁,i₂,i] ![i₀,i₁,i₂,j]
  have he :
      P.submatrix ![i₀,i₁,i₂,i] ![i₀,i₁,i₂,j] =
        !![0, P i₀ i₁, P i₀ i₂, P i₀ j;
           P i₀ i₁, 0, P i₁ i₂, P i₁ j;
           P i₀ i₂, P i₁ i₂, 0, P i₂ j;
           P i₀ i, P i₁ i, P i₂ i, P i j] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.submatrix, hdiag, hsym i₁ i₀, hsym i₂ i₀,
        hsym i₂ i₁, hsym i i₀, hsym i i₁, hsym i i₂]
  rw [he, bordered_det] at hz
  linarith

/-- An explicit future-null-cone factorization, before choosing circle angles. -/
theorem exists_normalized_lorentz_factorization (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) (hrank : P.rank ≤ 3)
    (i₀ i₁ i₂ : ι) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    ∃ t x y : ι → ℝ,
      (∀ i, 0 < t i) ∧
      (∀ i, x i ^ 2 + y i ^ 2 = t i ^ 2) ∧
      (∀ i j, P i j = t i * t j - x i * x j - y i * y j) ∧
      t i₀ = 1 ∧ x i₀ = 1 ∧ y i₀ = 0 := by
  let a := P i₀ i₁
  let b := P i₀ i₂
  let c := P i₁ i₂
  have ha : 0 < a := hpos _ _ h01
  have hb : 0 < b := hpos _ _ h02
  have hc : 0 < c := hpos _ _ h12
  let r := Real.sqrt (2*b*c/a)
  have hinside : 0 < 2*b*c/a := by positivity
  have hr : 0 < r := Real.sqrt_pos.mpr hinside
  have hrsq : a*r^2 = 2*b*c := by
    have hsq : r^2 = 2*b*c/a := Real.sq_sqrt hinside.le
    rw [hsq]
    field_simp [ha.ne']
  let t : ι → ℝ := fun i => (P i₀ i + 2*P i₁ i/a)/2
  let x : ι → ℝ := fun i => (2*P i₁ i/a - P i₀ i)/2
  let y : ι → ℝ := fun i => (c*P i₀ i + b*P i₁ i - a*P i₂ i)/(a*r)
  have hnonneg : ∀ i j, 0 ≤ P i j := by
    intro i j
    by_cases hij : i = j
    · subst j; rw [hdiag]
    · exact (hpos i j hij).le
  have ht : ∀ i, 0 < t i := by
    intro i
    by_cases hi : i = i₀
    · subst i
      have hval : t i₀ = 1 := by
        dsimp [t]
        rw [hdiag, hsym i₁ i₀]
        change (0 + 2*a/a)/2 = 1
        field_simp [ha.ne']
        ring
      rw [hval]
      norm_num
    · have hui : 0 < P i₀ i := hpos _ _ (Ne.symm hi)
      have hvi : 0 ≤ P i₁ i := hnonneg _ _
      dsimp [t]
      positivity
  have hfactor : ∀ i j, P i j = t i*t j - x i*x j - y i*y j := by
    intro i j
    have hs := schur_formula P hsym hdiag hrank i₀ i₁ i₂ i j
    have hl := lorentz_identity a b c r
      (P i₀ i) (P i₁ i) (P i₂ i) (P i₀ j) (P i₁ j) (P i₂ j)
      ha.ne' hb.ne' hc.ne' hr.ne' hrsq
    change P i j = ((P i₀ i + 2*P i₁ i/a)/2) *
        ((P i₀ j + 2*P i₁ j/a)/2) -
      ((2*P i₁ i/a - P i₀ i)/2) * ((2*P i₁ j/a - P i₀ j)/2) -
      ((c*P i₀ i + b*P i₁ i - a*P i₂ i)/(a*r)) *
        ((c*P i₀ j + b*P i₁ j - a*P i₂ j)/(a*r))
    rw [hl]
    apply (eq_div_iff (by positivity : 2*a*b*c ≠ 0)).mpr
    dsimp [a,b,c]
    nlinarith [hs]
  refine ⟨t,x,y,ht,?_,hfactor,?_,?_,?_⟩
  · intro i
    have hi := hfactor i i
    rw [hdiag] at hi
    nlinarith
  · dsimp [t]
    rw [hdiag, hsym i₁ i₀]
    change (0 + 2*a/a)/2 = 1
    field_simp [ha.ne']
    ring
  · dsimp [x]
    rw [hdiag, hsym i₁ i₀]
    change (2*a/a - 0)/2 = 1
    field_simp [ha.ne']
    ring
  · dsimp [y]
    rw [hdiag, hsym i₁ i₀, hsym i₂ i₀]
    change (c*0 + b*a - a*b)/(a*r) = 0
    ring

/-- The Lorentz factorization without fixing the distinguished point. -/
theorem exists_lorentz_factorization (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) (hrank : P.rank ≤ 3)
    (i₀ i₁ i₂ : ι) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    ∃ t x y : ι → ℝ,
      (∀ i, 0 < t i) ∧
      (∀ i, x i ^ 2 + y i ^ 2 = t i ^ 2) ∧
      (∀ i j, P i j = t i * t j - x i * x j - y i * y j) := by
  obtain ⟨t,x,y,ht,hn,hP,_,_,_⟩ :=
    exists_normalized_lorentz_factorization P hsym hdiag hpos hrank
      i₀ i₁ i₂ h01 h02 h12
  exact ⟨t,x,y,ht,hn,hP⟩

/-- A fully quantified circle factorization with distinct principal arguments. -/
theorem exists_circle_factorization (P : Matrix ι ι ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) (hrank : P.rank ≤ 3)
    (i₀ i₁ i₂ : ι) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    ∃ a θ : ι → ℝ, (∀ i, 0 < a i) ∧ Function.Injective θ ∧
      (∀ i, θ i ∈ Set.Ioc (-Real.pi) Real.pi) ∧
      ∀ i j, P i j = a i*a j*(1 - Real.cos (θ i - θ j)) := by
  obtain ⟨a,x,y,ha,hnull,hfactor⟩ :=
    exists_lorentz_factorization P hsym hdiag hpos hrank i₀ i₁ i₂ h01 h02 h12
  let z : ι → ℂ := fun i => ⟨x i/a i,y i/a i⟩
  have hunit : ∀ i, (x i/a i)^2 + (y i/a i)^2 = 1 := by
    intro i
    field_simp [(ha i).ne']
    exact hnull i
  have hnorm : ∀ i, ‖z i‖ = 1 := by
    intro i
    rw [Complex.norm_def]
    change Real.sqrt ((x i/a i)*(x i/a i) + (y i/a i)*(y i/a i)) = 1
    rw [← sq, ← sq, hunit i]
    norm_num
  have hz : ∀ i, z i ≠ 0 := by
    intro i h
    have hi := hnorm i
    rw [h, norm_zero] at hi
    norm_num at hi
  let θ : ι → ℝ := fun i => Complex.arg (z i)
  have hcos : ∀ i, Real.cos (θ i) = x i/a i := by
    intro i
    simpa [θ, hnorm i, z] using Complex.cos_arg (hz i)
  have hsin : ∀ i, Real.sin (θ i) = y i/a i := by
    intro i
    simpa [θ, hnorm i, z] using Complex.sin_arg (z i)
  have hP : ∀ i j, P i j = a i*a j*(1 - Real.cos (θ i - θ j)) := by
    intro i j
    rw [Real.cos_sub, hcos, hcos, hsin, hsin, hfactor]
    field_simp [(ha i).ne', (ha j).ne']
    ring
  refine ⟨a,θ,ha,?_,fun i => Complex.arg_mem_Ioc (z i),hP⟩
  intro i j hij
  by_contra hne
  have hp := hpos i j hne
  rw [hP i j, hij, sub_self, Real.cos_zero] at hp
  norm_num at hp

end
end VolumeVerification.CircleFactorization

