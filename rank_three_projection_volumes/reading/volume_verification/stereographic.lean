module
public import VolumeVerification.CircleFactorization
public import VolumeVerification.QuadraticCone
public import Mathlib.Data.Finset.Sort
@[expose] public section
set_option autoImplicit false

/-!
# Stereographic coordinates for positive hollow rank-three matrices

One distinguished null vector is the point at infinity.  All other indices
become distinct real nodes, and the column space becomes weighted evaluation
of quadratic polynomials, with leading coefficient evaluated at infinity.
-/
namespace VolumeVerification.Stereographic
open scoped BigOperators Matrix
open QuadraticCone

theorem exists_parameters {N : ℕ}
    (P : Matrix (Fin (N+3)) (Fin (N+3)) ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) (hrank : P.rank ≤ 3) :
    ∃ w t : Fin (N+2) → ℝ,
      (∀ i, 0 < w i) ∧ Function.Injective t ∧
      (∀ i, P 0 i.succ = w i) ∧
      ∀ i j, P i.succ j.succ = (w i*w j/2)*(t i-t j)^2 := by
  obtain ⟨T,X,Y,hT,hnull,hP,hT0,hX0,hY0⟩ :=
    CircleFactorization.exists_normalized_lorentz_factorization P hsym hdiag hpos hrank
      0 1 2
      (by intro h; have hv := congrArg Fin.val h
          change 0 = 1 % (N + 3) at hv
          rw [Nat.mod_eq_of_lt (show 1 < N + 3 by omega)] at hv
          omega)
      (by intro h; have hv := congrArg Fin.val h
          change 0 = 2 % (N + 3) at hv
          rw [Nat.mod_eq_of_lt (show 2 < N + 3 by omega)] at hv
          omega)
      (by intro h; have hv := congrArg Fin.val h
          change 1 % (N + 3) = 2 % (N + 3) at hv
          rw [Nat.mod_eq_of_lt (show 1 < N + 3 by omega),
            Nat.mod_eq_of_lt (show 2 < N + 3 by omega)] at hv
          omega)
  let w : Fin (N+2) → ℝ := fun i => P 0 i.succ
  let t : Fin (N+2) → ℝ := fun i => Y i.succ / w i
  have hw : ∀ i, 0 < w i :=
    fun i => hpos 0 i.succ (Ne.symm (Fin.succ_ne_zero i))
  have hwdef : ∀ i, w i = T i.succ-X i.succ := by
    intro i
    dsimp [w]
    rw [hP,hT0,hX0,hY0]
    ring
  have hy : ∀ i, Y i.succ = w i*t i := by
    intro i
    dsimp [t]
    field_simp [(hw i).ne']
  have hplus : ∀ i, T i.succ+X i.succ = w i*(t i)^2 := by
    intro i
    have hprod : (T i.succ+X i.succ)*w i = (Y i.succ)^2 := by
      rw [hwdef]
      nlinarith [hnull i.succ]
    apply mul_right_cancel₀ (hw i).ne'
    rw [hprod,hy]
    ring
  have ht : ∀ i, T i.succ = w i*((t i)^2+1)/2 := by
    intro i
    have h1 := hwdef i
    have h2 := hplus i
    nlinarith
  have hx : ∀ i, X i.succ = w i*((t i)^2-1)/2 := by
    intro i
    have h1 := hwdef i
    have h2 := hplus i
    nlinarith
  have hfinite : ∀ i j,
      P i.succ j.succ = (w i*w j/2)*(t i-t j)^2 := by
    intro i j
    rw [hP,ht,ht,hx,hx,hy,hy]
    ring
  refine ⟨w,t,hw,?_,fun _ => rfl,hfinite⟩
  intro i j hij
  by_contra hne
  have hsucc : i.succ ≠ j.succ := fun h => hne (Fin.succ_inj.mp h)
  have hp := hpos i.succ j.succ hsucc
  rw [hfinite,hij,sub_self] at hp
  norm_num at hp

noncomputable def markedEvaluation {m : ℕ}
    (w t : Fin m → ℝ) : Coeff →ₗ[ℝ] (Fin (m+1) → ℝ) where
  toFun p := Fin.cons (2*p 0) (fun i => w i*evaluate p (t i))
  map_add' p q := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [Fin.cons_zero]; ring
    · simp [evaluate_add,Fin.cons_succ,mul_add]
  map_smul' c p := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [Fin.cons_zero]; ring
    · simp [evaluate_smul,Fin.cons_succ]; ring

@[simp] theorem markedEvaluation_zero {m : ℕ}
    (w t : Fin m → ℝ) (p : Coeff) :
    markedEvaluation w t p 0 = 2*p 0 := rfl

@[simp] theorem markedEvaluation_succ {m : ℕ}
    (w t : Fin m → ℝ) (p : Coeff) (i : Fin m) :
    markedEvaluation w t p i.succ = w i*evaluate p (t i) := rfl

noncomputable def columnCoefficients {m : ℕ} (w t : Fin m → ℝ) :
    Fin (m+1) → Coeff :=
  Fin.cons (constant 1)
    (fun j => ![w j/2, -w j*t j, w j*(t j)^2/2])

theorem marked_columns {m : ℕ}
    (P : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (w t : Fin m → ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hzero : ∀ i, P 0 i.succ = w i)
    (hfinite : ∀ i j, P i.succ j.succ = (w i*w j/2)*(t i-t j)^2)
    (j : Fin (m+1)) :
    markedEvaluation w t (columnCoefficients w t j) = fun i => P i j := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) j
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp [columnCoefficients,constant,hdiag]
    · simp [columnCoefficients,evaluate_constant,hsym i.succ 0,hzero]
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp [columnCoefficients,hzero]
      ring
    · simp [columnCoefficients,evaluate,hfinite]
      ring

/-- The equality concerns the actual range of the matrix map. -/
theorem range_eq_markedEvaluation {m : ℕ}
    (P : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (w t : Fin m → ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hrank : P.rank = 3)
    (hzero : ∀ i, P 0 i.succ = w i)
    (hfinite : ∀ i j, P i.succ j.succ = (w i*w j/2)*(t i-t j)^2) :
    P.mulVecLin.range = (markedEvaluation w t).range := by
  let C : (Fin (m+1) → ℝ) →ₗ[ℝ] Coeff :=
    ∑ j, (LinearMap.proj j).smulRight (columnCoefficients w t j)
  have hfactor : P.mulVecLin = (markedEvaluation w t).comp C := by
    ext u i
    simp only [C,LinearMap.comp_apply,LinearMap.sum_apply,
      LinearMap.smulRight_apply,LinearMap.proj_apply,map_sum,map_smul,
      marked_columns P w t hsym hdiag hzero hfinite,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVecLin_apply,
      Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsub : P.mulVecLin.range ≤ (markedEvaluation w t).range := by
    rw [hfactor]
    exact LinearMap.range_comp_le_range _ _
  have hdim := (markedEvaluation w t).finrank_range_add_finrank_ker
  have hle : Module.finrank ℝ (markedEvaluation w t).range ≤ 3 := by
    simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at hdim
    omega
  apply Submodule.eq_of_le_of_finrank_le hsub
  change Module.finrank ℝ (markedEvaluation w t).range ≤ P.rank
  rw [hrank]
  exact hle

theorem exists_sorting {m : ℕ} (t : Fin m → ℝ) (ht : Function.Injective t) :
    ∃ σ : Equiv.Perm (Fin m), StrictMono (fun i => t (σ i)) := by
  classical
  let e : Fin m ≃ Set.range t := Equiv.ofInjective t ht
  letI : Fintype (Set.range t) := Fintype.ofFinite _
  have hcard : Fintype.card (Set.range t) = m := by
    rw [← Fintype.card_congr e]
    simp
  let o : Fin m ≃o Set.range t := Fintype.orderIsoFinOfCardEq _ hcard
  let σ : Equiv.Perm (Fin m) := o.toEquiv.trans e.symm
  have hval : ∀ i, t (σ i) = (o i).val := by
    intro i
    exact congrArg Subtype.val (e.apply_symm_apply (o i))
  refine ⟨σ,?_⟩
  intro i j hij
  change t (σ i) < t (σ j)
  rw [hval,hval]
  exact o.strictMono hij

def fixInfinity {m : ℕ} (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m+1)) :=
  (finSuccEquiv m).trans ((Equiv.optionCongr σ).trans (finSuccEquiv m).symm)

@[simp] theorem fixInfinity_zero {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    fixInfinity σ 0 = 0 := by simp [fixInfinity]

@[simp] theorem fixInfinity_succ {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    fixInfinity σ i.succ = (σ i).succ := by simp [fixInfinity]

end VolumeVerification.Stereographic

