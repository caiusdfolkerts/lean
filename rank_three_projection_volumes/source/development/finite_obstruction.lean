module

public import development.compactification
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.SolveByElim
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

#assert_standard_axioms RankThreeProjection.theorem31

/- Source module: VolumeVerification.QuadraticCone. SHA256: 08c96a8755c85213d5d09c8be98a58d8bdb467ce083fd8edb4d873ba711ba743 -/
section DevelopmentSource0











@[expose] public section
set_option autoImplicit false

/-!
# Nonnegative quadratic evaluations on an ordered finite set and infinity

The extreme-generator description is proved by subtracting the minimum nodal
value, then using the two neighboring quadratic factors at a minimizing node.
This avoids a separate planar polygon adjacency theorem.
-/
namespace VolumeVerification.QuadraticCone
open scoped BigOperators Matrix

abbrev Coeff := Fin 3 → ℝ

def evaluate (p : Coeff) (t : ℝ) : ℝ := p 0*t^2 + p 1*t + p 2

def constant (c : ℝ) : Coeff := ![0,0,c]
def leftRay (a : ℝ) : Coeff := ![0,1,-a]
def rightRay (b : ℝ) : Coeff := ![0,-1,b]
def pairRay (a b : ℝ) : Coeff := ![1,-(a+b),a*b]

@[simp] theorem evaluate_constant (c t : ℝ) : evaluate (constant c) t = c := by
  simp [evaluate,constant]
@[simp] theorem evaluate_leftRay (a t : ℝ) : evaluate (leftRay a) t = t-a := by
  simp [evaluate,leftRay,sub_eq_add_neg]
@[simp] theorem evaluate_rightRay (b t : ℝ) : evaluate (rightRay b) t = b-t := by
  simp [evaluate,rightRay,sub_eq_add_neg,add_comm]
@[simp] theorem evaluate_pairRay (a b t : ℝ) :
    evaluate (pairRay a b) t = (t-a)*(t-b) := by
  simp [evaluate,pairRay]
  ring

theorem evaluate_add (p q : Coeff) (t : ℝ) :
    evaluate (p+q) t = evaluate p t + evaluate q t := by
  simp [evaluate]
  ring

theorem evaluate_smul (c : ℝ) (p : Coeff) (t : ℝ) :
    evaluate (c • p) t = c * evaluate p t := by
  simp [evaluate]
  ring

def Generated {ι : Type*} [Fintype ι] (v : ι → Coeff) (p : Coeff) : Prop :=
  ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • v i = p

theorem generated_generator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Coeff) (i : ι) : Generated v (v i) := by
  classical
  refine ⟨Pi.single i 1, ?_, ?_⟩
  · intro j
    by_cases h : j = i <;> simp [Pi.single_apply,h]
  · simp [Pi.single_apply, ite_smul]

theorem generated_add {ι : Type*} [Fintype ι] (v : ι → Coeff)
    {p q : Coeff} (hp : Generated v p) (hq : Generated v q) : Generated v (p+q) := by
  obtain ⟨a,ha,rfl⟩ := hp
  obtain ⟨b,hb,rfl⟩ := hq
  exact ⟨fun i => a i+b i, fun i => add_nonneg (ha i) (hb i), by
    simp [add_smul, Finset.sum_add_distrib]⟩

theorem generated_smul {ι : Type*} [Fintype ι] (v : ι → Coeff)
    {p : Coeff} (hp : Generated v p) {c : ℝ} (hc : 0 ≤ c) :
    Generated v (c • p) := by
  obtain ⟨a,ha,rfl⟩ := hp
  exact ⟨fun i => c*a i, fun i => mul_nonneg hc (ha i), by
    simp [Finset.smul_sum, smul_smul]⟩

theorem constant_decomposition (a b c : ℝ) (hab : a < b) :
    constant c = (c/(b-a)) • leftRay a + (c/(b-a)) • rightRay b := by
  ext i
  fin_cases i <;> simp [constant,leftRay,rightRay] <;>
    field_simp [(sub_pos.mpr hab).ne'] <;> ring

def slopeAt (p : Coeff) (x : ℝ) : ℝ := 2*p 0*x+p 1

theorem left_difference (p : Coeff) (l x : ℝ) :
    evaluate p l - evaluate p x =
      (x-l)*(p 0*(x-l)-slopeAt p x) := by
  simp [evaluate,slopeAt]
  ring

theorem right_difference (p : Coeff) (x r : ℝ) :
    evaluate p r - evaluate p x =
      (r-x)*(slopeAt p x+p 0*(r-x)) := by
  simp [evaluate,slopeAt]
  ring

theorem left_numerator_nonnegative (p : Coeff) {l x : ℝ} (hlx : l < x)
    (hmin : evaluate p x ≤ evaluate p l) :
    0 ≤ p 0*(x-l)-slopeAt p x := by
  have hp : 0 ≤ (x-l)*(p 0*(x-l)-slopeAt p x) := by
    rw [← left_difference]
    exact sub_nonneg.mpr hmin
  exact (mul_nonneg_iff_of_pos_left (sub_pos.mpr hlx)).mp hp

theorem right_numerator_nonnegative (p : Coeff) {x r : ℝ} (hxr : x < r)
    (hmin : evaluate p x ≤ evaluate p r) :
    0 ≤ slopeAt p x+p 0*(r-x) := by
  have hp : 0 ≤ (r-x)*(slopeAt p x+p 0*(r-x)) := by
    rw [← right_difference]
    exact sub_nonneg.mpr hmin
  exact (mul_nonneg_iff_of_pos_left (sub_pos.mpr hxr)).mp hp

theorem middle_decomposition (p : Coeff) (l x r : ℝ) (hlr : l < r) :
    p = constant (evaluate p x) +
      ((slopeAt p x+p 0*(r-x))/(r-l)) • pairRay l x +
      ((p 0*(x-l)-slopeAt p x)/(r-l)) • pairRay x r := by
  ext i
  fin_cases i <;> simp [constant,pairRay,evaluate,slopeAt] <;>
    field_simp [(sub_pos.mpr hlr).ne'] <;> ring

theorem minimum_left_decomposition (p : Coeff) (x r : ℝ) :
    p = constant (evaluate p x) + p 0 • pairRay x r +
      (slopeAt p x+p 0*(r-x)) • leftRay x := by
  ext i
  fin_cases i <;> simp [constant,pairRay,leftRay,evaluate,slopeAt] <;> ring

theorem minimum_right_decomposition (p : Coeff) (l x : ℝ) :
    p = constant (evaluate p x) + p 0 • pairRay l x +
      (p 0*(x-l)-slopeAt p x) • rightRay x := by
  ext i
  fin_cases i <;> simp [constant,pairRay,rightRay,evaluate,slopeAt] <;> ring

section Nodes
variable {N : ℕ} (t : Fin (N+1) → ℝ)

def generators : Fin (N+2) → Coeff :=
  Fin.cons (leftRay (t 0)) fun i : Fin (N+1) =>
    if i = Fin.last N then rightRay (t (Fin.last N))
    else pairRay (t i) (t (finRotate (N+1) i))

@[simp] theorem generators_zero :
    generators t 0 = leftRay (t 0) := rfl

theorem generators_last :
    generators t (Fin.last (N+1)) = rightRay (t (Fin.last N)) := by
  simp [generators]

theorem generators_succ {i : Fin (N+1)} (hi : i ≠ Fin.last N) :
    generators t i.succ = pairRay (t i) (t (finRotate (N+1) i)) := by
  simp [generators,hi]

theorem zero_lt_last (hN : 1 ≤ N) : (0 : Fin (N+1)) < Fin.last N := by
  change 0 < N
  omega

theorem adjacent_alternative (i j : Fin (N+1)) (hi : i ≠ Fin.last N) :
    j ≤ i ∨ finRotate (N+1) i ≤ j := by
  have hval := coe_finRotate_of_ne_last hi
  simp only [Fin.le_def]
  omega

theorem generators_nonnegative (ht : StrictMono t) :
    ∀ e : Fin (N+2), 0 ≤ generators t e 0 ∧
      ∀ i, 0 ≤ evaluate (generators t e) (t i) := by
  intro e
  induction e using Fin.cases with
  | zero =>
      constructor
      · simp [generators,leftRay]
      · intro i
        rw [generators_zero,evaluate_leftRay]
        exact sub_nonneg.mpr (ht.monotone (Fin.zero_le i))
  | succ e =>
      by_cases he : e = Fin.last N
      · subst e
        constructor
        · simp [generators,rightRay]
        · intro i
          simpa [generators] using sub_nonneg.mpr (ht.monotone i.le_last)
      · rw [generators_succ t he]
        constructor
        · simp [pairRay]
        · intro i
          rw [evaluate_pairRay]
          have hnext : e < finRotate (N+1) e :=
            (lt_finRotate_iff_ne_last e).mpr he
          rcases adjacent_alternative e i he with hil | hir
          · exact mul_nonneg_of_nonpos_of_nonpos
              (sub_nonpos.mpr (ht.monotone hil))
              (sub_nonpos.mpr (ht.monotone (hil.trans hnext.le)))
          · exact mul_nonneg
              (sub_nonneg.mpr (ht.monotone (hnext.le.trans hir)))
              (sub_nonneg.mpr (ht.monotone hir))

theorem constant_generated (hN : 1 ≤ N) (ht : StrictMono t) {c : ℝ} (hc : 0 ≤ c) :
    Generated (generators t) (constant c) := by
  have hgap : 0 < t (Fin.last N)-t 0 := sub_pos.mpr (ht (zero_lt_last hN))
  rw [constant_decomposition _ _ _ (ht (zero_lt_last hN))]
  apply generated_add
  · exact generated_smul _ (by simpa using generated_generator (generators t) 0)
      (div_nonneg hc hgap.le)
  · exact generated_smul _ (by
      simpa only [generators_last] using
        generated_generator (generators t) (Fin.last (N+1))) (div_nonneg hc hgap.le)

/-- Every nonnegative nodal quadratic with nonnegative leading coefficient
is generated by the two endpoint linears and consecutive-root quadratics. -/
theorem generated_of_nonnegative (hN : 1 ≤ N) (ht : StrictMono t)
    (p : Coeff) (hlead : 0 ≤ p 0) (hvalues : ∀ i, 0 ≤ evaluate p (t i)) :
    Generated (generators t) p := by
  classical
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin (N+1) => evaluate p (t i)) Finset.univ_nonempty
  have hm : ∀ j, evaluate p (t i) ≤ evaluate p (t j) :=
    fun j => hmin j (Finset.mem_univ j)
  have hc : Generated (generators t) (constant (evaluate p (t i))) :=
    constant_generated t hN ht (hvalues i)
  by_cases hi0 : i = 0
  · subst i
    have hiLast : (0 : Fin (N+1)) ≠ Fin.last N := (zero_lt_last hN).ne
    have hnext : (0 : Fin (N+1)) < finRotate (N+1) 0 :=
      (lt_finRotate_iff_ne_last 0).mpr hiLast
    have hp : Generated (generators t)
        (pairRay (t 0) (t (finRotate (N+1) 0))) := by
      simpa only [generators_succ t hiLast] using
        generated_generator (generators t) (Fin.succ 0)
    have hl : Generated (generators t) (leftRay (t 0)) := by
      simpa only [generators_zero] using generated_generator (generators t) 0
    rw [minimum_left_decomposition p (t 0) (t (finRotate (N+1) 0))]
    exact generated_add _ (generated_add _ hc (generated_smul _ hp hlead))
      (generated_smul _ hl (right_numerator_nonnegative p (ht hnext) (hm _)))
  by_cases hiLast : i = Fin.last N
  · subst i
    let j := (finRotate (N+1)).symm (Fin.last N)
    have hji : j < Fin.last N :=
      (finRotate_symm_lt_iff_ne_zero _).mpr (Ne.symm (zero_lt_last hN).ne)
    have hjLast : j ≠ Fin.last N := hji.ne
    have hnextj : finRotate (N+1) j = Fin.last N := (finRotate _).apply_symm_apply _
    have hp : Generated (generators t) (pairRay (t j) (t (Fin.last N))) := by
      simpa only [generators_succ t hjLast,hnextj] using
        generated_generator (generators t) j.succ
    have hr : Generated (generators t) (rightRay (t (Fin.last N))) := by
      simpa only [generators_last] using
        generated_generator (generators t) (Fin.last (N+1))
    rw [minimum_right_decomposition p (t j) (t (Fin.last N))]
    exact generated_add _ (generated_add _ hc (generated_smul _ hp hlead))
      (generated_smul _ hr (left_numerator_nonnegative p (ht hji) (hm j)))
  · let j := (finRotate (N+1)).symm i
    let k := finRotate (N+1) i
    have hji : j < i := (finRotate_symm_lt_iff_ne_zero i).mpr hi0
    have hik : i < k := (lt_finRotate_iff_ne_last i).mpr hiLast
    have hjLast : j ≠ Fin.last N := by
      intro h
      rw [h] at hji
      exact (not_lt_of_ge i.le_last) hji
    have hnextj : finRotate (N+1) j = i := (finRotate _).apply_symm_apply _
    have hleft : Generated (generators t) (pairRay (t j) (t i)) := by
      simpa only [generators_succ t hjLast,hnextj] using
        generated_generator (generators t) j.succ
    have hright : Generated (generators t) (pairRay (t i) (t k)) := by
      simpa only [generators_succ t hiLast] using
        generated_generator (generators t) i.succ
    have hden : 0 < t k-t j := sub_pos.mpr (ht (hji.trans hik))
    rw [middle_decomposition p (t j) (t i) (t k) (ht (hji.trans hik))]
    apply generated_add
    · exact generated_add _ hc (generated_smul _ hleft
        (div_nonneg (right_numerator_nonnegative p (ht hik) (hm k)) hden.le))
    · exact generated_smul _ hright
        (div_nonneg (left_numerator_nonnegative p (ht hji) (hm j)) hden.le)

end Nodes
end VolumeVerification.QuadraticCone

end
end DevelopmentSource0

/- Source module: VolumeVerification.Stereographic. SHA256: fa401ad763b3c8bb3b98c8a0d4102bf852337f883e73baa3da81d86edd4830e1 -/
section DevelopmentSource1




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

end
end DevelopmentSource1

/- Source module: VolumeVerification.CycleObstruction. SHA256: b81e97566c5ad51debd870bf55e4c73cf68528213c86a3addad7a83cd834f108 -/
section DevelopmentSource2








@[expose] public section
set_option autoImplicit false

/-!
# The cyclic linear algebra in the full-dimensional projection obstruction

This file proves the final finite-dimensional contradiction in Proposition 4.2.
The hypotheses are explicit matrix identities.  The construction of those
identities from mixed-area measures is a separate geometric theorem.
-/
namespace VolumeVerification.CycleObstruction
open scoped BigOperators Matrix

section Cycle
variable {n : ℕ} [NeZero n]

theorem zero_propagates_around_cycle (w : Fin n → ℝ)
    (hstep : ∀ i, w i = 0 → w (finRotate n i) = 0)
    (i : Fin n) (hi : w i = 0) : w = 0 := by
  have hiter : ∀ k : ℕ, w ((finRotate n)^[k] i) = 0 := by
    intro k
    induction k with
    | zero => simpa using hi
    | succ k ih =>
        rw [Function.iterate_succ', Function.comp_apply]
        exact hstep _ ih
  funext j
  have hj := hiter ((j - i).val)
  rw [← finCycle_eq_finRotate_iterate (k := j - i)] at hj
  have hindex : finCycle (j - i) i = j := by
    change i + (j - i) = j
    abel
  simpa only [hindex, Pi.zero_apply] using hj

theorem finrank_le_one_of_zero_propagation
    (K : Submodule ℝ (Fin n → ℝ))
    (hstep : ∀ w ∈ K, ∀ i, w i = 0 → w (finRotate n i) = 0) :
    Module.finrank ℝ K ≤ 1 := by
  let ev : K →ₗ[ℝ] ℝ := (LinearMap.proj (0 : Fin n)).comp K.subtype
  have hinj : Function.Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro w hw
    have hw0 : (w : Fin n → ℝ) 0 = 0 := hw
    have hz := zero_propagates_around_cycle (w : Fin n → ℝ)
      (hstep _ w.property) 0 hw0
    exact Subtype.ext hz
  rw [← LinearMap.finrank_range_of_inj hinj]
  simpa using ev.range.finrank_le

/-- Column i is alpha_i e_i + beta_i e_(i+1). -/
def cycleIncidence (alpha beta : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if i = j then alpha j else 0) +
    (if i = finRotate n j then beta j else 0)

theorem transpose_cycleIncidence_mulVec (alpha beta w : Fin n → ℝ) (i : Fin n) :
    ((cycleIncidence alpha beta)ᵀ *ᵥ w) i =
      alpha i * w i + beta i * w (finRotate n i) := by
  simp [Matrix.mulVec, dotProduct, cycleIncidence, Matrix.transpose_apply,
    add_mul, ite_mul, Finset.sum_add_distrib]

theorem weighted_cycle_zero_propagation (alpha beta w : Fin n → ℝ)
    (hbeta : ∀ i, beta i ≠ 0)
    (hrel : ∀ i, alpha i * w i + beta i * w (finRotate n i) = 0) :
    ∀ i, w i = 0 → w (finRotate n i) = 0 := by
  intro i hi
  have h := hrel i
  rw [hi, mul_zero, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left (hbeta i)

theorem cycle_kernel_finrank_le_one (alpha beta : Fin n → ℝ)
    (hbeta : ∀ i, beta i ≠ 0) :
    Module.finrank ℝ (cycleIncidence alpha beta)ᵀ.mulVecLin.ker ≤ 1 := by
  apply finrank_le_one_of_zero_propagation
  intro w hw
  have hrel : ∀ i, alpha i * w i + beta i * w (finRotate n i) = 0 := by
    intro i
    have hi := congrFun hw i
    simpa only [Matrix.mulVecLin_apply, transpose_cycleIncidence_mulVec,
      Pi.zero_apply] using hi
  exact weighted_cycle_zero_propagation alpha beta w hbeta hrel

theorem odd_weighted_cycle_zero (alpha beta w : Fin n → ℝ)
    (halpha : ∀ i, 0 < alpha i) (hbeta : ∀ i, 0 < beta i)
    (hodd : Odd n)
    (hrel : ∀ i, alpha i * w i + beta i * w (finRotate n i) = 0) :
    w = 0 := by
  have hmul : ∀ i, alpha i * w i = (-beta i) * w (finRotate n i) := by
    intro i
    linarith [hrel i]
  have hprod := congrArg (fun f : Fin n → ℝ => ∏ i, f i) (funext hmul)
  have hrotate : (∏ i, w (finRotate n i)) = ∏ i, w i :=
    Fintype.prod_equiv (finRotate n) _ _ (fun _ => rfl)
  simp only [Finset.prod_mul_distrib, Finset.prod_neg, Finset.card_univ,
    Fintype.card_fin, hodd.neg_one_pow, hrotate] at hprod
  have hpa : 0 < ∏ i, alpha i := Finset.prod_pos fun i _ => halpha i
  have hpb : 0 < ∏ i, beta i := Finset.prod_pos fun i _ => hbeta i
  have hpw : (∏ i, w i) = 0 := by
    have he : ((∏ i, alpha i) + ∏ i, beta i) * (∏ i, w i) = 0 := by
      nlinarith [hprod]
    exact (mul_eq_zero.mp he).resolve_left (add_pos hpa hpb).ne'
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hpw
  exact zero_propagates_around_cycle w
    (weighted_cycle_zero_propagation alpha beta w (fun i => (hbeta i).ne') hrel) i hi

theorem odd_cycle_kernel_eq_bot (alpha beta : Fin n → ℝ)
    (halpha : ∀ i, 0 < alpha i) (hbeta : ∀ i, 0 < beta i) (hodd : Odd n) :
    (cycleIncidence alpha beta)ᵀ.mulVecLin.ker = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro w hw
  apply odd_weighted_cycle_zero alpha beta w halpha hbeta hodd
  intro i
  have hi := congrFun hw i
  simpa only [Matrix.mulVecLin_apply, transpose_cycleIncidence_mulVec,
    Pi.zero_apply] using hi

theorem cycle_rank_add_one_ge (alpha beta : Fin n → ℝ)
    (hbeta : ∀ i, beta i ≠ 0) :
    n ≤ (cycleIncidence alpha beta).rank + 1 := by
  have hk := cycle_kernel_finrank_le_one alpha beta hbeta
  have hr := (cycleIncidence alpha beta)ᵀ.mulVecLin.finrank_range_add_finrank_ker
  change (cycleIncidence alpha beta)ᵀ.rank +
    Module.finrank ℝ (cycleIncidence alpha beta)ᵀ.mulVecLin.ker =
      Module.finrank ℝ (Fin n → ℝ) at hr
  rw [Matrix.rank_transpose] at hr
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hr
  omega

theorem odd_cycle_rank (alpha beta : Fin n → ℝ)
    (halpha : ∀ i, 0 < alpha i) (hbeta : ∀ i, 0 < beta i) (hodd : Odd n) :
    (cycleIncidence alpha beta).rank = n := by
  have hr := (cycleIncidence alpha beta)ᵀ.mulVecLin.finrank_range_add_finrank_ker
  change (cycleIncidence alpha beta)ᵀ.rank +
    Module.finrank ℝ (cycleIncidence alpha beta)ᵀ.mulVecLin.ker =
      Module.finrank ℝ (Fin n → ℝ) at hr
  rw [odd_cycle_kernel_eq_bot alpha beta halpha hbeta hodd] at hr
  simpa only [finrank_bot, add_zero, Matrix.rank_transpose,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hr

end Cycle

section RankBounds
variable {n : ℕ} [NeZero n]

theorem transpose_kernel_finrank_eq (Z : Matrix (Fin n) (Fin n) ℝ) :
    Module.finrank ℝ Zᵀ.mulVecLin.ker = Module.finrank ℝ Z.mulVecLin.ker := by
  have h1 := Z.mulVecLin.finrank_range_add_finrank_ker
  have h2 := Zᵀ.mulVecLin.finrank_range_add_finrank_ker
  change Z.rank + Module.finrank ℝ Z.mulVecLin.ker =
    Module.finrank ℝ (Fin n → ℝ) at h1
  change Zᵀ.rank + Module.finrank ℝ Zᵀ.mulVecLin.ker =
    Module.finrank ℝ (Fin n → ℝ) at h2
  rw [Matrix.rank_transpose] at h2
  omega

theorem rank_le_kernel_finrank_of_mul_zero
    (Z M : Matrix (Fin n) (Fin n) ℝ) (hZM : Z * M = 0) :
    M.rank ≤ Module.finrank ℝ Z.mulVecLin.ker := by
  have hsub : M.mulVecLin.range ≤ Z.mulVecLin.ker := by
    rintro x ⟨y,rfl⟩
    change Z *ᵥ (M *ᵥ y) = 0
    rw [Matrix.mulVec_mulVec, hZM, Matrix.zero_mulVec]
  exact Submodule.finrank_mono hsub

/-- The final contradiction of Proposition 4.2, for every n >= 5.
The geometric construction must supply the displayed identities. -/
theorem no_cycle_factorization (hn : 5 ≤ n)
    (W : Matrix (Fin (n-3)) (Fin n) ℝ) (hW : W.rank = n-3)
    (Z : Matrix (Fin n) (Fin n) ℝ)
    (hrelations : ∀ w, Zᵀ *ᵥ w = 0 →
      ∀ i, w i = 0 → w (finRotate n i) = 0)
    (alpha beta : Fin n → ℝ)
    (halpha : ∀ i, 0 < alpha i) (hbeta : ∀ i, 0 < beta i)
    (L : Matrix (Fin (n-3)) (Fin n) ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hZM : Z * M = 0)
    (hfactor : W * cycleIncidence alpha beta = L * M) :
    False := by
  have hkerT : Module.finrank ℝ Zᵀ.mulVecLin.ker ≤ 1 :=
    finrank_le_one_of_zero_propagation _ (fun w hw => hrelations w hw)
  have hker : Module.finrank ℝ Z.mulVecLin.ker ≤ 1 := by
    rwa [transpose_kernel_finrank_eq] at hkerT
  have hM : M.rank ≤ 1 :=
    (rank_le_kernel_finrank_of_mul_zero Z M hZM).trans hker
  have hupper : (W * cycleIncidence alpha beta).rank ≤ 1 := by
    rw [hfactor]
    exact (Matrix.rank_mul_le_right L M).trans hM
  have hge := Matrix.rank_mul_ge W (cycleIncidence alpha beta)
  rw [hW, Fintype.card_fin] at hge
  by_cases hfive : n = 5
  · have hodd : Odd n := by rw [hfive]; exact ⟨2, rfl⟩
    rw [odd_cycle_rank alpha beta halpha hbeta hodd] at hge
    omega
  · have hD := cycle_rank_add_one_ge alpha beta (fun i => (hbeta i).ne')
    omega

end RankBounds
end VolumeVerification.CycleObstruction

end
end DevelopmentSource2

/- Source module: VolumeVerification.ConicCaratheodory. SHA256: 23ffb1c78134e3b47311547fa3b28fe273070e567a8408e0f09734dffc87bcaf -/
section DevelopmentSource3







@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Finite conic Carathéodory reduction

This proof follows the recovered finite-cone argument, with its finite-minimum
step written explicitly for the pinned library. Only this general algebraic
lemma is needed for the measurable selector; the unrelated face and closedness
results are excluded from its build dependency.
-/
namespace VolumeVerification.ConicCaratheodory
open scoped BigOperators
variable {Index : Type*}

lemma conic_caratheodory {Scalar Ambient : Type*} [Field Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar]
    [AddCommGroup Ambient] [Module Scalar Ambient] [Fintype Index]
    (vectors : Index → Ambient) (coefficients : Index → Scalar) (hc : ∀ index, 0 ≤ coefficients index) :
    ∃ (reducedCoefficients : Index → Scalar) (support : Finset Index), (∀ index, 0 ≤ reducedCoefficients index) ∧ (∀ index ∉ support, reducedCoefficients index = 0) ∧
      LinearIndepOn Scalar vectors support ∧ (∑ index ∈ support, reducedCoefficients index • vectors index) = ∑ index, coefficients index • vectors index := by
  classical
  obtain ⟨support, hs⟩ : ∃ support : Finset Index,
      (∃ reducedCoefficients : Index → Scalar, (∀ index, 0 ≤ reducedCoefficients index) ∧ (∀ index ∉ support, reducedCoefficients index = 0) ∧
        (∑ index ∈ support, reducedCoefficients index • vectors index = ∑ index, coefficients index • vectors index)) ∧
      ∀ smallerSupport : Finset Index, (∃ reducedCoefficients : Index → Scalar, (∀ index, 0 ≤ reducedCoefficients index) ∧ (∀ index ∉ smallerSupport, reducedCoefficients index = 0) ∧
        (∑ index ∈ smallerSupport, reducedCoefficients index • vectors index = ∑ index, coefficients index • vectors index)) → support.card ≤ smallerSupport.card := by
    let S : Set (Finset Index) := {s | ∃ d : Index → Scalar,
      (∀ index, 0 ≤ d index) ∧ (∀ index ∉ s, d index = 0) ∧
        (∑ index ∈ s, d index • vectors index = ∑ index, coefficients index • vectors index)}
    have hS : S.Nonempty := ⟨Finset.univ, coefficients, hc,
      fun index hk => False.elim (hk (Finset.mem_univ index)), by simp⟩
    exact Set.exists_min_image S Finset.card (Set.toFinite S) hS
  by_cases h_lin_dep : ¬ LinearIndepOn Scalar vectors support
  · obtain ⟨reducedCoefficients, hd_nonneg, hd_zero, hd_sum⟩ := hs.left
    obtain ⟨dependency, ha_nonzero, ha_support, ha_sum⟩ : ∃ dependency : Index → Scalar,
        (∃ index ∈ support, dependency index ≠ 0) ∧ (∀ index ∉ support, dependency index = 0) ∧
        (∑ index ∈ support, dependency index • vectors index = 0) ∧ (∃ index ∈ support, dependency index > 0) := by
      obtain ⟨dependency, ha_nonzero, ha_sum⟩ : ∃ dependency : Index → Scalar,
          (∃ index ∈ support, dependency index ≠ 0) ∧ (∀ index ∉ support, dependency index = 0) ∧
          (∑ index ∈ support, dependency index • vectors index = 0) := by
        rw [linearIndepOn_iff'] at h_lin_dep
        push Not at h_lin_dep
        obtain ⟨smallerSupport, weights, ht, hg, chosenIndex, hi, hi'⟩ := h_lin_dep
        refine ⟨fun index => if index ∈ smallerSupport then weights index else 0, ⟨chosenIndex, ht hi, by simpa [hi] using hi'⟩,
          fun index hk => by
            change (if index ∈ smallerSupport then weights index else 0) = 0
            split
            · rename_i hkt
              exact (hk (ht hkt)).elim
            · rfl, ?_⟩
        calc ∑ index ∈ support, (if index ∈ smallerSupport then weights index else 0) • vectors index
            = ∑ index ∈ support, if index ∈ smallerSupport then weights index • vectors index else 0 := by
              refine Finset.sum_congr rfl (fun index _ => ?_); rw [ite_smul, zero_smul]
          _ = ∑ index ∈ support ∩ smallerSupport, weights index • vectors index := Finset.sum_ite_mem support smallerSupport _
          _ = ∑ index ∈ smallerSupport, weights index • vectors index := by rw [Finset.inter_eq_right.mpr ht]
          _ = 0 := hg
      by_cases h_neg : ∀ index ∈ support, dependency index ≤ 0
      · obtain ⟨index, hks, hk⟩ := ha_nonzero
        exact ⟨fun index => -dependency index, ⟨index, hks, neg_ne_zero.mpr hk⟩,
          fun index hk => by simp only [ha_sum.1 index hk, neg_zero],
          by simp [neg_smul, ha_sum.2],
          ⟨index, hks, neg_pos.mpr (lt_of_le_of_ne (h_neg index hks) hk)⟩⟩
      · exact ⟨dependency, ha_nonzero, ha_sum.1, ha_sum.2, by
          push Not at h_neg
          exact h_neg⟩
    obtain ⟨step, hθ_min⟩ : ∃ step,
        (∀ index ∈ support, reducedCoefficients index - step * dependency index ≥ 0) ∧ (∃ index ∈ support, reducedCoefficients index - step * dependency index = 0) := by
      obtain ⟨minimumIndex, hk₀⟩ : ∃ minimumIndex ∈ support, dependency minimumIndex > 0 ∧
          ∀ index ∈ support, dependency index > 0 → reducedCoefficients index / dependency index ≥ reducedCoefficients minimumIndex / dependency minimumIndex := by
        obtain ⟨positiveIndex, hkp⟩ := ha_sum.2
        obtain ⟨minimumIndex, hk₀f, hk₀min⟩ :=
          Finset.exists_min_image (support.filter (fun index => dependency index > 0)) (fun index => reducedCoefficients index / dependency index)
            ⟨positiveIndex, Finset.mem_filter.mpr hkp⟩
        obtain ⟨hk₀s, hk₀pos⟩ := Finset.mem_filter.mp hk₀f
        exact ⟨minimumIndex, hk₀s, hk₀pos, fun index hk hk' =>
          hk₀min index (Finset.mem_filter.mpr ⟨hk, hk'⟩)⟩
      refine ⟨reducedCoefficients minimumIndex / dependency minimumIndex, ?_, minimumIndex, hk₀.1, ?_⟩
      · intro index hk
        by_cases hk' : dependency index > 0
        · have hle : reducedCoefficients minimumIndex / dependency minimumIndex * dependency index ≤ reducedCoefficients index :=
            (le_div_iff₀ hk').1 (hk₀.2.2 index hk hk')
          linarith
        · have h2 : reducedCoefficients minimumIndex / dependency minimumIndex * dependency index ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hd_nonneg _) hk₀.2.1.le)
              (le_of_not_gt hk')
          linarith [hd_nonneg index]
      · rw [div_mul_cancel₀ _ hk₀.2.1.ne', sub_self]
    set smallerSupport := support.filter (fun index => reducedCoefficients index - step * dependency index ≠ 0) with ht_def
    have h_t_support : ∀ index, 0 ≤ reducedCoefficients index - step * dependency index := by
      exact fun index => if hk : index ∈ support then hθ_min.1 index hk else by
        simp [hd_zero index hk, ha_support index hk]
    have h_t_zero : ∀ index ∉ smallerSupport, reducedCoefficients index - step * dependency index = 0 := by
      intro index hk
      by_cases hks : index ∈ support
      · by_contra hP
        exact hk (by rw [ht_def]; exact Finset.mem_filter.mpr ⟨hks, hP⟩)
      · rw [hd_zero index hks, ha_support index hks]
        ring
    have h_t_sum : ∑ index ∈ smallerSupport, (reducedCoefficients index - step * dependency index) • vectors index = ∑ index, coefficients index • vectors index := by
      convert congr_arg (fun vector => vector - step • ∑ index ∈ support, dependency index • vectors index) hd_sum using 1
      · rw [Finset.sum_filter_of_ne]
        · simp [sub_smul, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul]
        · exact fun index _ hk' hk'' => hk' <| by rw [hk'', zero_smul]
      · simp [ha_sum.1]
    contrapose! hs
    refine fun _ => ⟨smallerSupport, ⟨fun index => reducedCoefficients index - step * dependency index, h_t_support, h_t_zero, h_t_sum⟩, ?_⟩
    refine Finset.card_lt_card ?_
    rw [ht_def]
    obtain ⟨k₁, hk₁s, hk₁0⟩ := hθ_min.2
    exact ⟨Finset.filter_subset _ _, fun hsub => (Finset.mem_filter.mp (hsub hk₁s)).2 hk₁0⟩
  · exact ⟨hs.1.choose, support, hs.1.choose_spec.1, hs.1.choose_spec.2.1,
      Classical.not_not.mp h_lin_dep, hs.1.choose_spec.2.2⟩

end VolumeVerification.ConicCaratheodory
end
end DevelopmentSource3

/- Source module: VolumeVerification.ConeSelection. SHA256: dc1f649e8413ae1776106b9d41bbba8343fd4d7f2266cf500dcf3f0870e61c99 -/
section DevelopmentSource4











@[expose] public section
set_option autoImplicit false

/-!
# Measurable coefficients for a finitely generated cone

A finite family of linear left inverses is enough: enumerate the independent
supports, and choose the first inverse giving nonnegative coefficients and
the correct vector.  The candidate sets are closed.  Conic Caratheodory
supplies a successful support for every vector in the cone.
-/
namespace VolumeVerification.ConeSelection
open scoped BigOperators Classical
open Set MeasureTheory

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def combinationMap (v : ι → E) (s : Finset ι) : (s → ℝ) →ₗ[ℝ] E :=
  ∑ i : s, (LinearMap.proj i).smulRight (v i)

theorem combinationMap_apply (v : ι → E) (s : Finset ι) (c : s → ℝ) :
    combinationMap v s c = ∑ i : s, c i • v i := by
  simp [combinationMap]

noncomputable def coefficientMap (v : ι → E) (s : Finset ι) :
    E →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi fun i =>
    if h : i ∈ s then
      (LinearMap.proj (⟨i,h⟩ : s)).comp (combinationMap v s).leftInverse
    else 0

theorem coefficientMap_apply (v : ι → E) (s : Finset ι) (x : E) (i : ι) :
    coefficientMap v s x i =
      if h : i ∈ s then (combinationMap v s).leftInverse x ⟨i,h⟩ else 0 := by
  classical
  by_cases h : i ∈ s <;> simp [coefficientMap, h]

def Candidate (v : ι → E) (s : Finset ι) (x : E) : Prop :=
  (∀ i, 0 ≤ coefficientMap v s x i) ∧
    ∑ i, coefficientMap v s x i • v i = x

theorem candidate_isClosed (v : ι → E) (s : Finset ι) :
    IsClosed {x : E | Candidate v s x} := by
  have hc : Continuous (coefficientMap v s) :=
    (coefficientMap v s).continuous_of_finiteDimensional
  have hci : ∀ i, Continuous (fun x : E => coefficientMap v s x i) :=
    fun i => (continuous_apply i).comp hc
  have hsum : Continuous (fun x : E => ∑ i, coefficientMap v s x i • v i) :=
    continuous_finsetSum _ (fun i _ => (hci i).smul continuous_const)
  have he :
      {x : E | Candidate v s x} =
        (⋂ i, {x : E | 0 ≤ coefficientMap v s x i}) ∩
          {x : E | ∑ i, coefficientMap v s x i • v i = x} := by
    ext x
    simp [Candidate]
  rw [he]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (hci i)).inter
    (isClosed_eq hsum continuous_id)

noncomputable def selectFrom (v : ι → E) : List (Finset ι) → E → (ι → ℝ)
  | [], _ => 0
  | s :: rest, x => if Candidate v s x then coefficientMap v s x else selectFrom v rest x

theorem selectFrom_measurable (v : ι → E) (supports : List (Finset ι)) :
    Measurable (selectFrom v supports) := by
  classical
  induction supports with
  | nil => exact measurable_const
  | cons s rest ih =>
      exact Measurable.ite (candidate_isClosed v s).measurableSet
        (coefficientMap v s).continuous_of_finiteDimensional.measurable ih

theorem selectFrom_nonnegative (v : ι → E) (supports : List (Finset ι)) :
    ∀ x i, 0 ≤ selectFrom v supports x i := by
  classical
  induction supports with
  | nil => intro x i; simp [selectFrom]
  | cons s rest ih =>
      intro x i
      by_cases h : Candidate v s x
      · simpa only [selectFrom, if_pos h] using h.1 i
      · simpa only [selectFrom, if_neg h] using ih x i

theorem selectFrom_reconstructs (v : ι → E) (supports : List (Finset ι)) (x : E)
    (hex : ∃ s ∈ supports, Candidate v s x) :
    ∑ i, selectFrom v supports x i • v i = x := by
  classical
  induction supports with
  | nil => simp at hex
  | cons s rest ih =>
      by_cases h : Candidate v s x
      · simpa only [selectFrom, if_pos h] using h.2
      · simp only [selectFrom, if_neg h]
        apply ih
        obtain ⟨t,ht,hvalid⟩ := hex
        rcases List.mem_cons.mp ht with rfl | ht
        · exact False.elim (h hvalid)
        · exact ⟨t,ht,hvalid⟩

noncomputable def selectionBound (v : ι → E) (supports : List (Finset ι)) : ℝ :=
  (supports.map fun s => ‖(coefficientMap v s).toContinuousLinearMap‖).sum

theorem selectionBound_nonnegative (v : ι → E) (supports : List (Finset ι)) :
    0 ≤ selectionBound v supports := by
  unfold selectionBound
  exact List.sum_nonneg fun x hx => by
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _

theorem selectFrom_norm_bound (v : ι → E) (supports : List (Finset ι)) (x : E) :
    ‖selectFrom v supports x‖ ≤ selectionBound v supports * ‖x‖ := by
  classical
  induction supports with
  | nil => simp [selectFrom, selectionBound]
  | cons s rest ih =>
      have hb := selectionBound_nonnegative v rest
      have hmap := norm_nonneg (coefficientMap v s).toContinuousLinearMap
      have hsplit : selectionBound v (s :: rest) =
          ‖(coefficientMap v s).toContinuousLinearMap‖ + selectionBound v rest := rfl
      rw [hsplit]
      by_cases h : Candidate v s x
      · simp only [selectFrom, if_pos h]
        exact ((coefficientMap v s).toContinuousLinearMap.le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))
      · simp only [selectFrom, if_neg h]
        exact ih.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))

theorem coefficientMap_eq_of_reduced (v : ι → E) (s : Finset ι)
    (c : ι → ℝ) (x : E)
    (hoff : ∀ i ∉ s, c i = 0)
    (hli : LinearIndepOn ℝ v (s : Set ι))
    (hsum : ∑ i ∈ s, c i • v i = x) :
    coefficientMap v s x = c := by
  classical
  have hinj : Function.Injective (combinationMap v s) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    rw [combinationMap_apply] at ha
    funext i
    exact Fintype.linearIndependent_iff.mp hli a ha i
  have hker : (combinationMap v s).ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hs : combinationMap v s (fun i : s => c i) = x := by
    rw [combinationMap_apply]
    exact (Finset.sum_coe_sort s (fun i => c i • v i)).trans hsum
  have hleft := LinearMap.leftInverse_apply_of_inj hker (fun i : s => c i)
  rw [hs] at hleft
  funext i
  rw [coefficientMap_apply]
  by_cases hi : i ∈ s
  · rw [dif_pos hi]
    exact congrFun hleft ⟨i,hi⟩
  · rw [dif_neg hi, hoff i hi]

theorem exists_candidate (v : ι → E) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    ∃ s : Finset ι, Candidate v s (∑ i, c i • v i) := by
  classical
  obtain ⟨d,s,hd,hoff,hli,hsum⟩ :=
    ConicCaratheodory.conic_caratheodory v c hc
  have he := coefficientMap_eq_of_reduced v s d _ hoff hli hsum
  refine ⟨s, ?_⟩
  rw [Candidate, he]
  refine ⟨hd, ?_⟩
  have hfull : (∑ i ∈ s, d i • v i) = ∑ i, d i • v i := by
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i _ hi
    rw [hoff i hi, zero_smul]
  rw [← hfull]
  exact hsum

noncomputable def select (v : ι → E) : E → (ι → ℝ) :=
  selectFrom v (Finset.univ : Finset (Finset ι)).toList

/-- One globally measurable, nonnegative selector, with a global linear bound.
Reconstruction holds at every point of the actual finitely generated cone. -/
theorem measurable_cone_coefficients (v : ι → E) :
    Measurable (select v) ∧
      (∀ x i, 0 ≤ select v x i) ∧
      (∀ x, (∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • v i = x) →
        ∑ i, select v x i • v i = x) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖select v x‖ ≤ C * ‖x‖ := by
  classical
  refine ⟨selectFrom_measurable v _, selectFrom_nonnegative v _, ?_, ?_⟩
  · rintro x ⟨c,hc,rfl⟩
    apply selectFrom_reconstructs
    obtain ⟨s,hs⟩ := exists_candidate v c hc
    exact ⟨s, by simp, hs⟩
  · exact ⟨selectionBound v _, selectionBound_nonnegative v _,
      selectFrom_norm_bound v _⟩

end VolumeVerification.ConeSelection

end
end DevelopmentSource4

/- Source module: VolumeVerification.ConeMeasureDecomposition. SHA256: d7c1adb6743dad6c1afa04c063fd9826ebf4f21c36953f9af8e59242d56212f9 -/
section DevelopmentSource5




@[expose] public section
set_option autoImplicit false

/-!
# Decomposing a positive vector of measures along a finite cone

The Radon--Nikodym densities and the measurable cone selector give finite
positive measures on the generators.  All signed relations are expressed as
equalities of the actual real masses on measurable sets.
-/
namespace VolumeVerification.ConeMeasureDecomposition
open scoped BigOperators ENNReal Matrix
open MeasureTheory Set

variable {Ω ι κ ζ : Type*} [MeasurableSpace Ω]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ζ] [DecidableEq ζ]

theorem withDensity_finsetSum (μ : Measure Ω) (s : Finset κ)
    (f : κ → Ω → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    μ.withDensity (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, μ.withDensity (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [withDensity_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      change μ.withDensity (f i + fun x => ∑ j ∈ s, f j x) =
        μ.withDensity (f i) + ∑ j ∈ s, μ.withDensity (f j)
      rw [withDensity_add_left (hf i), ih]

theorem decompose_density (μ : Measure Ω)
    (r : κ → ι → ℝ) (hr : ∀ e i, 0 ≤ r e i)
    (a : Ω → ι → ℝ) (ha : Measurable a) (hai : Integrable a μ)
    (hcone : ∀ᵐ x ∂μ, ∃ c : κ → ℝ,
      (∀ e, 0 ≤ c e) ∧ ∑ e, c e • r e = a x) :
    ∃ ν : κ → Measure Ω,
      (∀ e, IsFiniteMeasure (ν e)) ∧
      ∀ i, μ.withDensity (fun x => ENNReal.ofReal (a x i)) =
        ∑ e, ENNReal.ofReal (r e i) • ν e := by
  classical
  obtain ⟨hselect,hselectpos,hreconstruct,C,hC,hbound⟩ :=
    ConeSelection.measurable_cone_coefficients r
  let c : Ω → κ → ℝ := fun x => ConeSelection.select r (a x)
  have hc : Measurable c := hselect.comp ha
  have hcpos : ∀ x e, 0 ≤ c x e := fun x e => hselectpos (a x) e
  have hci : Integrable c μ :=
    (hai.norm.const_mul C).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hbound (a x))
  let ν : κ → Measure Ω :=
    fun e => μ.withDensity (fun x => ENNReal.ofReal (c x e))
  have hνfinite : ∀ e, IsFiniteMeasure (ν e) := by
    intro e
    apply isFiniteMeasure_withDensity
    exact (lintegral_ofReal_ne_top_iff_integrable
      (hci.eval e).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hcpos x e)).mpr (hci.eval e)
  refine ⟨ν,hνfinite,?_⟩
  intro i
  have heq : (fun x => ENNReal.ofReal (a x i)) =ᵐ[μ]
      (fun x => ∑ e, ENNReal.ofReal (r e i) * ENNReal.ofReal (c x e)) := by
    filter_upwards [hcone] with x hx
    have hx' := congrFun (hreconstruct (a x) hx) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx'
    rw [← hx', ENNReal.ofReal_sum_of_nonneg
      (fun e _ => mul_nonneg (hcpos x e) (hr e i))]
    apply Finset.sum_congr rfl
    intro e _
    rw [ENNReal.ofReal_mul (hcpos x e)]
    exact mul_comm _ _
  rw [withDensity_congr_ae heq,
    withDensity_finsetSum μ Finset.univ
      (fun e x => ENNReal.ofReal (r e i) * ENNReal.ofReal (c x e))
      (fun e => measurable_const.mul ((measurable_pi_apply e).comp hc).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro e _
  change μ.withDensity (ENNReal.ofReal (r e i) •
      (fun x => ENNReal.ofReal (c x e))) =
    ENNReal.ofReal (r e i) • μ.withDensity (fun x => ENNReal.ofReal (c x e))
  exact withDensity_smul _ (((measurable_pi_apply e).comp hc).ennreal_ofReal)

noncomputable def realDensity (μ : Measure Ω) (μi : ι → Measure Ω) :
    Ω → ι → ℝ :=
  fun x i => ((μi i).rnDeriv μ x).toReal

theorem realDensity_measurable (μ : Measure Ω) (μi : ι → Measure Ω) :
    Measurable (realDensity μ μi) :=
  Measurable.of_eval fun i => ((μi i).measurable_rnDeriv μ).ennreal_toReal

theorem realDensity_integrable (μ : Measure Ω) (μi : ι → Measure Ω)
    [∀ i, IsFiniteMeasure (μi i)] :
    Integrable (realDensity μ μi) μ := by
  apply integrable_pi_iff.mpr
  intro i
  simpa only [integrableOn_univ, realDensity] using
    (Measure.integrableOn_toReal_rnDeriv (μ := μi i) (ν := μ)
      (s := Set.univ) (measure_ne_top (μi i) Set.univ))

theorem realDensity_reconstructs (μ : Measure Ω) (μi : ι → Measure Ω)
    [IsFiniteMeasure μ] [∀ i, IsFiniteMeasure (μi i)]
    (hdom : ∀ i, μi i ≤ μ) (i : ι) :
    μ.withDensity (fun x => ENNReal.ofReal (realDensity μ μi x i)) = μi i := by
  have heq : (fun x => ENNReal.ofReal (realDensity μ μi x i)) =ᵐ[μ]
      (μi i).rnDeriv μ := by
    filter_upwards [Measure.rnDeriv_ne_top (μi i) μ] with x hx
    exact ENNReal.ofReal_toReal hx
  rw [withDensity_congr_ae heq]
  exact Measure.withDensity_rnDeriv_eq _ _ (hdom i).absolutelyContinuous

theorem realDensity_linear_relations (μ : Measure Ω) (μi : ι → Measure Ω)
    [IsFiniteMeasure μ] [∀ i, IsFiniteMeasure (μi i)]
    (hdom : ∀ i, μi i ≤ μ) (W : Matrix ζ ι ℝ)
    (hrelations : ∀ k s, MeasurableSet s →
      ∑ i, W k i * (μi i).real s = 0) :
    ∀ᵐ x ∂μ, W *ᵥ realDensity μ μi x = 0 := by
  have ha := realDensity_integrable μ μi
  have hrows : ∀ k, (fun x => ∑ i, W k i * realDensity μ μi x i) =ᵐ[μ] 0 := by
    intro k
    have hi : Integrable (fun x => ∑ i, W k i * realDensity μ μi x i) μ :=
      integrable_finsetSum Finset.univ (fun i _ => (ha.eval i).const_mul (W k i))
    apply hi.ae_eq_zero_of_forall_setIntegral_eq_zero
    intro s hs _
    rw [integral_finsetSum Finset.univ
      (fun i _ => ((ha.eval i).const_mul (W k i)).integrableOn)]
    calc
      (∑ i, ∫ x in s, W k i * realDensity μ μi x i ∂μ) =
          ∑ i, W k i * (μi i).real s := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul]
        congr 1
        exact Measure.setIntegral_toReal_rnDeriv (hdom i).absolutelyContinuous s
      _ = 0 := hrelations k s hs
  have hall : ∀ᵐ x ∂μ, ∀ k, ∑ i, W k i * realDensity μ μi x i = 0 :=
    (ae_all_iff).mpr hrows
  filter_upwards [hall] with x hx
  funext k
  exact hx k

/-- Equation (7) follows from actual finite positive measures, actual linear
relations on all measurable sets, and a finite generating description of the
nonnegative kernel cone. -/
theorem decompose_positive_measure_vector
    (μ : Measure Ω) (μi : ι → Measure Ω)
    [IsFiniteMeasure μ] [∀ i, IsFiniteMeasure (μi i)]
    (hdom : ∀ i, μi i ≤ μ)
    (W : Matrix ζ ι ℝ) (r : κ → ι → ℝ)
    (hr : ∀ e i, 0 ≤ r e i)
    (hspan : ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) → W *ᵥ y = 0 →
      ∃ c : κ → ℝ, (∀ e, 0 ≤ c e) ∧ ∑ e, c e • r e = y)
    (hrelations : ∀ k s, MeasurableSet s →
      ∑ i, W k i * (μi i).real s = 0) :
    ∃ ν : κ → Measure Ω,
      (∀ e, IsFiniteMeasure (ν e)) ∧
      ∀ i, μi i = ∑ e, ENNReal.ofReal (r e i) • ν e := by
  have hkernel := realDensity_linear_relations μ μi hdom W hrelations
  have hcone : ∀ᵐ x ∂μ, ∃ c : κ → ℝ, (∀ e, 0 ≤ c e) ∧
      ∑ e, c e • r e = realDensity μ μi x := by
    filter_upwards [hkernel] with x hx
    exact hspan _ (fun i => ENNReal.toReal_nonneg) hx
  obtain ⟨ν,hν,hdecomp⟩ := decompose_density μ r hr (realDensity μ μi)
    (realDensity_measurable μ μi) (realDensity_integrable μ μi) hcone
  refine ⟨ν,hν,?_⟩
  intro i
  rw [← realDensity_reconstructs μ μi hdom i]
  exact hdecomp i

end VolumeVerification.ConeMeasureDecomposition

end
end DevelopmentSource5

/- Source module: VolumeVerification.EdgeMoments. SHA256: d19027a82faa886605c532e500fb616f6f7a9c9b8481cc80eb279912ba4a8db2 -/
section DevelopmentSource6




@[expose] public section
set_option autoImplicit false

/-!
# Endpoint moments in the polygonal measure decomposition

Every endpoint moment used in the cyclic rank contradiction is derived from
the original centered measures and their positive decomposition.  The only
geometric input here is the measure identity and the endpoint-zero pattern
of the actual cone rays.
-/
namespace VolumeVerification.EdgeMoments
open scoped BigOperators ENNReal Matrix
open MeasureTheory Set
variable {n : ℕ}

def next (i : Fin n) : Fin n := finRotate n i
def prev (i : Fin n) : Fin n := (finRotate n).symm i

@[simp] theorem next_prev (i : Fin n) : next (prev i) = i := by
  exact (finRotate n).apply_symm_apply i

@[simp] theorem prev_next (i : Fin n) : prev (next i) = i := by
  exact (finRotate n).symm_apply_apply i

theorem next_ne (hn : 2 ≤ n) (i : Fin n) : next i ≠ i := by
  letI : NeZero n := i.neZero
  intro h
  have he : i + 1 = i + 0 := by simpa [next, finRotate_apply] using h
  have h1 : (1 : Fin n) = 0 := add_left_cancel he
  have hv := congrArg Fin.val h1
  change 1 % n = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
  omega

theorem prev_ne (hn : 2 ≤ n) (i : Fin n) : prev i ≠ i := by
  intro h
  have he := congrArg next h
  rw [next_prev] at he
  exact next_ne hn i he.symm

theorem prev_ne_next (hn : 3 ≤ n) (i : Fin n) : prev i ≠ next i := by
  letI : NeZero n := i.neZero
  intro h
  have he : i = next (next i) := by
    calc
      i = next (prev i) := (next_prev i).symm
      _ = next (next i) := congrArg next h
  simp only [next, finRotate_apply] at he
  have htwo : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    change (1 % n + 1 % n) % n = 2 % n
    simp only [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h2 : (2 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    calc
      i + 2 = (i + 1) + 1 := by
        rw [← htwo, add_assoc]
      _ = i := he.symm
      _ = i + 0 := by simp
  have hv := congrArg Fin.val h2
  change 2 % n = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega : 2 < n)] at hv
  omega

section Compact
variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

theorem continuous_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C,hC⟩ := (isCompact_range hf.norm).bddAbove
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hC ⟨x,rfl⟩)

def coordinate (Z : Matrix (Fin n) (Fin n) ℝ)
    (φ : Ω → Fin n → ℝ) (i : Fin n) (x : Ω) : ℝ := (Z *ᵥ φ x) i

theorem coordinate_continuous (Z : Matrix (Fin n) (Fin n) ℝ)
    (φ : Ω → Fin n → ℝ) (hφ : Continuous φ) (i : Fin n) :
    Continuous (coordinate Z φ i) := by
  unfold coordinate
  fun_prop

theorem integral_matrix_row {m : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Matrix (Fin m) (Fin n) ℝ)
    (φ : Ω → Fin n → ℝ) (hφ : Continuous φ) (i : Fin m) :
    (∫ x, (A *ᵥ φ x) i ∂μ) = ∑ j, A i j * ∫ x, φ x j ∂μ := by
  have hj : ∀ j, Integrable (fun x => A i j * φ x j) μ := by
    intro j
    exact (continuous_integrable μ _ ((continuous_apply j).comp hφ)).const_mul _
  simp only [Matrix.mulVec, dotProduct]
  rw [integral_finsetSum Finset.univ (fun j _ => hj j)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_const_mul _ _

theorem integral_coordinate (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Matrix (Fin n) (Fin n) ℝ)
    (φ : Ω → Fin n → ℝ) (hφ : Continuous φ) (i : Fin n) :
    (∫ x, coordinate Z φ i x ∂μ) =
      ∑ j, Z i j * ∫ x, φ x j ∂μ := by
  exact integral_matrix_row μ Z φ hφ i

variable (μ : Fin n → Measure Ω) (ν : Fin n → Measure Ω)
  [∀ i, IsFiniteMeasure (μ i)] [∀ e, IsFiniteMeasure (ν e)]
  (r : Fin n → Fin n → ℝ)

def RayPattern : Prop :=
  (∀ e, r e e = 0) ∧
  (∀ e, r e (next e) = 0) ∧
  (∀ e i, i ≠ e → i ≠ next e → 0 < r e i)

theorem ray_nonnegative (hr : RayPattern r) : ∀ e i, 0 ≤ r e i := by
  intro e i
  by_cases hi : i = e
  · subst i; rw [hr.1]
  by_cases hin : i = next e
  · rw [hin, hr.2.1]
  exact (hr.2.2 e i hi hin).le

theorem transfer_ae (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
    (e i : Fin n) (hi : i ≠ e) (hin : i ≠ next e)
    {p : Ω → Prop} (hp : ∀ᵐ x ∂μ i, p x) :
    ∀ᵐ x ∂ν e, p x := by
  have hri := hr.2.2 e i hi hin
  have hle : ENNReal.ofReal (r e i) • ν e ≤ μ i := by
    rw [hdecomp]
    exact Finset.single_le_sum
      (f := fun j => ENNReal.ofReal (r j i) • ν j)
      (fun j _ => Measure.zero_le _) (Finset.mem_univ e)
  have hs : ∀ᵐ x ∂ENNReal.ofReal (r e i) • ν e, p x :=
    hp.filter_mono (ae_mono hle)
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hri).ne').mp hs

theorem integral_decomposition (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
    (g : Ω → ℝ) (hg : Continuous g) (i : Fin n) :
    (∫ x, g x ∂μ i) = ∑ e, r e i * ∫ x, g x ∂ν e := by
  rw [hdecomp]
  rw [integral_finsetSum_measure
    (fun e _ => (continuous_integrable (ν e) g hg).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro e _
  rw [integral_smul_measure, ENNReal.toReal_ofReal (ray_nonnegative r hr e i)]
  rfl

theorem isolate_outgoing (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
    (i : Fin n) (g : Ω → ℝ) (hg : Continuous g)
    (hzero : ∀ e, i ≠ e → i ≠ next e → g =ᵐ[ν e] 0) :
    (∫ x, g x ∂μ (prev i)) = r i (prev i) * ∫ x, g x ∂ν i := by
  rw [integral_decomposition μ ν r hr hdecomp g hg]
  apply Finset.sum_eq_single i
  · intro e _ hei
    by_cases h : i = next e
    · have he : e = prev i := by rw [h, prev_next]
      subst e
      rw [hr.1, zero_mul]
    · rw [integral_eq_zero_of_ae (hzero e (Ne.symm hei) h), mul_zero]
  · simp

theorem isolate_incoming (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
    (i : Fin n) (g : Ω → ℝ) (hg : Continuous g)
    (hzero : ∀ e, i ≠ e → i ≠ next e → g =ᵐ[ν e] 0) :
    (∫ x, g x ∂μ (next i)) = r (prev i) (next i) * ∫ x, g x ∂ν (prev i) := by
  rw [integral_decomposition μ ν r hr hdecomp g hg]
  apply Finset.sum_eq_single (prev i)
  · intro e _ hei
    by_cases he : i = e
    · subst e
      rw [hr.2.1, zero_mul]
    · have hin : i ≠ next e := by
        intro h
        apply hei
        rw [h, prev_next]
      rw [integral_eq_zero_of_ae (hzero e he hin), mul_zero]
  · simp

variable (P Z : Matrix (Fin n) (Fin n) ℝ)
  (φ : Ω → Fin n → ℝ) (hφ : Continuous φ)
  (hdiag : ∀ i, P i i = 0)
  (hpos : ∀ i j, i ≠ j → 0 < P i j)
  (hpair : ∀ i j, P i j = ∫ x, |coordinate Z φ j x| ∂μ i)
  (hcenter : ∀ i j, ∫ x, φ x j ∂μ i = 0)

include hφ hdiag hpair in
theorem coordinate_zero_on_original (i : Fin n) :
    coordinate Z φ i =ᵐ[μ i] 0 := by
  have hi : (∫ x, |coordinate Z φ i x| ∂μ i) = 0 := by
    rw [← hpair, hdiag]
  have hz := (integral_eq_zero_iff_of_nonneg
    (fun x => abs_nonneg _) (continuous_integrable (μ i) _
      (coordinate_continuous Z φ hφ i).abs)).mp hi
  filter_upwards [hz] with x hx
  exact abs_eq_zero.mp hx

include hφ hdiag hpair in
theorem coordinate_zero_off_edge (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
    (e i : Fin n) (hi : i ≠ e) (hin : i ≠ next e) :
    coordinate Z φ i =ᵐ[ν e] 0 :=
  transfer_ae μ ν r hr hdecomp e i hi hin
    (coordinate_zero_on_original μ P Z φ hφ hdiag hpair i)

include hφ hcenter in
theorem original_coordinate_centered (i j : Fin n) :
    (∫ x, coordinate Z φ j x ∂μ i) = 0 := by
  rw [integral_coordinate (μ i) Z φ hφ j]
  simp [hcenter]

include hφ hdiag hpos hpair hcenter in
theorem outgoing_moments (hn : 3 ≤ n) (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e) (i : Fin n) :
    (∫ x, coordinate Z φ i x ∂ν i) = 0 ∧
      0 < ∫ x, |coordinate Z φ i x| ∂ν i := by
  have hc := coordinate_continuous Z φ hφ i
  have hz := coordinate_zero_off_edge μ ν r P Z φ hφ hdiag hpair hr hdecomp
  have hs := isolate_outgoing μ ν r hr hdecomp i _ hc (fun e => hz e i)
  have ha := isolate_outgoing μ ν r hr hdecomp i _ hc.abs
    (fun e hi hin => (hz e i hi hin).mono fun x hx => by simp [hx])
  have hrpos := hr.2.2 i (prev i) (prev_ne (by omega) i) (prev_ne_next hn i)
  rw [original_coordinate_centered μ Z φ hφ hcenter] at hs
  have hs0 : (∫ x, coordinate Z φ i x ∂ν i) = 0 :=
    (mul_eq_zero.mp hs.symm).resolve_left hrpos.ne'
  refine ⟨hs0, ?_⟩
  have hp := hpos (prev i) i (prev_ne (by omega) i)
  rw [hpair, ha] at hp
  by_contra h
  have hle : (∫ x, |coordinate Z φ i x| ∂ν i) ≤ 0 := le_of_not_gt h
  have := mul_nonpos_of_nonneg_of_nonpos hrpos.le hle
  linarith

include hφ hdiag hpos hpair hcenter in
theorem incoming_moments (hn : 3 ≤ n) (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e) (i : Fin n) :
    (∫ x, coordinate Z φ i x ∂ν (prev i)) = 0 ∧
      0 < ∫ x, |coordinate Z φ i x| ∂ν (prev i) := by
  have hc := coordinate_continuous Z φ hφ i
  have hz := coordinate_zero_off_edge μ ν r P Z φ hφ hdiag hpair hr hdecomp
  have hs := isolate_incoming μ ν r hr hdecomp i _ hc (fun e => hz e i)
  have ha := isolate_incoming μ ν r hr hdecomp i _ hc.abs
    (fun e hi hin => (hz e i hi hin).mono fun x hx => by simp [hx])
  have hnex : next i ≠ prev i := Ne.symm (prev_ne_next hn i)
  have hne2 : next i ≠ next (prev i) := by simpa using next_ne (by omega) i
  have hrpos := hr.2.2 (prev i) (next i) hnex hne2
  rw [original_coordinate_centered μ Z φ hφ hcenter] at hs
  have hs0 : (∫ x, coordinate Z φ i x ∂ν (prev i)) = 0 :=
    (mul_eq_zero.mp hs.symm).resolve_left hrpos.ne'
  refine ⟨hs0, ?_⟩
  have hp := hpos (next i) i (next_ne (by omega) i)
  rw [hpair, ha] at hp
  by_contra h
  have hle : (∫ x, |coordinate Z φ i x| ∂ν (prev i)) ≤ 0 := le_of_not_gt h
  have := mul_nonpos_of_nonneg_of_nonpos hrpos.le hle
  linarith

end Compact
end VolumeVerification.EdgeMoments

end
end DevelopmentSource6

/- Source module: VolumeVerification.MarkedPolynomialCone. SHA256: e9881aa88cf11322d7fd84b8016d9608172b4d5bcaae802ef84b66b1462cdc47 -/
section DevelopmentSource7



@[expose] public section
set_option autoImplicit false

/-!
# The cyclic cone rays of a positive hollow rank-three matrix

The rays are explicit weighted evaluations of neighboring-root quadratic
polynomials, with infinity as one of the nodes.  Generation follows from
QuadraticCone.generated_of_nonnegative, not from an assumed polygon theorem.
-/
namespace VolumeVerification.MarkedPolynomialCone
open scoped BigOperators Matrix
open QuadraticCone Stereographic

section Ordered
variable {N : ℕ} (w t : Fin (N+1) → ℝ)

noncomputable def rays : Fin (N+2) → Fin (N+2) → ℝ :=
  fun e => markedEvaluation w t (generators t e)

private theorem next_zero :
    EdgeMoments.next (0 : Fin (N+2)) = (0 : Fin (N+1)).succ := by
  apply Fin.ext
  simp [EdgeMoments.next,finRotate_apply]

private theorem next_last :
    EdgeMoments.next (Fin.last (N+1)) = (0 : Fin (N+2)) := by
  exact finRotate_last

private theorem next_succ (i : Fin (N+1)) (hi : i ≠ Fin.last N) :
    EdgeMoments.next i.succ = (finRotate (N+1) i).succ := by
  have hi' : i.succ ≠ Fin.last (N+1) := by
    intro h
    apply hi
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa using hv
  apply Fin.ext
  change (finRotate (N+2) i.succ).val = (finRotate (N+1) i).val+1
  calc
    (finRotate (N+2) i.succ).val = i.succ.val + 1 := coe_finRotate_of_ne_last hi'
    _ = (i.val + 1) + 1 := rfl
    _ = (finRotate (N+1) i).val + 1 :=
      (congrArg (fun x : ℕ => x + 1) (coe_finRotate_of_ne_last hi)).symm

theorem rays_nonnegative (hw : ∀ i, 0 < w i) (ht : StrictMono t) :
    ∀ e i, 0 ≤ rays w t e i := by
  intro e i
  obtain ⟨hlead,hvalues⟩ := generators_nonnegative t ht e
  refine Fin.cases ?_ (fun i => ?_) i
  · change 0 ≤ 2*generators t e 0
    positivity
  · change 0 ≤ w i*evaluate (generators t e) (t i)
    exact mul_nonneg (hw i).le (hvalues i)

/-- The cyclic endpoint-zero pattern is derived from strict ordering of the
actual finite nodes and positivity of the actual coordinate weights. -/
theorem rayPattern (hN : 1 ≤ N)
    (hw : ∀ i, 0 < w i) (ht : StrictMono t) :
    EdgeMoments.RayPattern (rays w t) := by
  have hleft :
      ∀ i : Fin (N+2), rays w t 0 i = 0 ↔
        i = 0 ∨ i = (0 : Fin (N+1)).succ := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [rays,generators,leftRay]
    · simp only [rays,markedEvaluation_succ,generators_zero,evaluate_leftRay]
      rw [mul_eq_zero]
      simp only [(hw i).ne',false_or,sub_eq_zero]
      constructor
      · intro h
        exact Or.inr (congrArg Fin.succ (ht.injective h))
      · rintro (h | h)
        · exact False.elim (Fin.succ_ne_zero i h)
        · exact congrArg t (Fin.succ_inj.mp h)
  have hright :
      ∀ i : Fin (N+2), rays w t (Fin.last (N+1)) i = 0 ↔
        i = Fin.last (N+1) ∨ i = 0 := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [rays,generators_last,rightRay]
    · simp only [rays,markedEvaluation_succ,generators_last,evaluate_rightRay]
      rw [mul_eq_zero]
      simp only [(hw i).ne',false_or,sub_eq_zero]
      constructor
      · intro h
        left
        have hi : i = Fin.last N := (ht.injective h).symm
        subst i
        rfl
      · rintro (h | h)
        · apply congrArg t
          apply Fin.ext
          have hv := congrArg Fin.val h
          simpa using hv.symm
        · exact False.elim (Fin.succ_ne_zero i h)
  have hmiddle :
      ∀ (e : Fin (N+1)), e ≠ Fin.last N →
        ∀ i : Fin (N+2), rays w t e.succ i = 0 ↔
          i = e.succ ∨ i = (finRotate (N+1) e).succ := by
    intro e he i
    refine Fin.cases ?_ (fun i => ?_) i
    · have hnonzero : rays w t e.succ 0 ≠ 0 := by
        simp [rays,generators_succ t he,pairRay]
      constructor
      · intro h
        exact False.elim (hnonzero h)
      · rintro (h | h)
        · exact False.elim (Fin.succ_ne_zero e h.symm)
        · exact False.elim (Fin.succ_ne_zero (finRotate (N+1) e) h.symm)
    · simp only [rays,markedEvaluation_succ,generators_succ t he,evaluate_pairRay]
      rw [mul_eq_zero]
      simp only [(hw i).ne',false_or,mul_eq_zero,sub_eq_zero]
      constructor
      · rintro (h | h)
        · exact Or.inl (congrArg Fin.succ (ht.injective h))
        · exact Or.inr (congrArg Fin.succ (ht.injective h))
      · rintro (h | h)
        · exact Or.inl (congrArg t (Fin.succ_inj.mp h))
        · exact Or.inr (congrArg t (Fin.succ_inj.mp h))
  have hzeros : ∀ e i, rays w t e i = 0 ↔
      i = e ∨ i = EdgeMoments.next e := by
    intro e i
    refine Fin.cases ?_ (fun e => ?_) e
    · rw [next_zero]
      exact hleft i
    · by_cases he : e = Fin.last N
      · subst e
        change rays w t (Fin.last (N+1)) i = 0 ↔
          i = Fin.last (N+1) ∨ i = EdgeMoments.next (Fin.last (N+1))
        rw [next_last]
        exact hright i
      · rw [next_succ e he]
        exact hmiddle e he i
  refine ⟨?_,?_,?_⟩
  · intro e
    exact (hzeros e e).mpr (Or.inl rfl)
  · intro e
    exact (hzeros e (EdgeMoments.next e)).mpr (Or.inr rfl)
  · intro e i hie hin
    apply lt_of_le_of_ne (rays_nonnegative w t hw ht e i)
    intro h
    rcases (hzeros e i).mp h.symm with h' | h'
    · exact hie h'
    · exact hin h'

theorem generated_of_nonnegative_range (hN : 1 ≤ N)
    (hw : ∀ i, 0 < w i) (ht : StrictMono t)
    (y : Fin (N+2) → ℝ)
    (hy : ∀ i, 0 ≤ y i)
    (hrange : y ∈ (markedEvaluation w t).range) :
    ∃ c : Fin (N+2) → ℝ,
      (∀ e, 0 ≤ c e) ∧ ∑ e, c e • rays w t e = y := by
  obtain ⟨p,rfl⟩ := hrange
  have hlead : 0 ≤ p 0 := by
    have h0 := hy 0
    change 0 ≤ 2*p 0 at h0
    linarith
  have hvalues : ∀ i, 0 ≤ evaluate p (t i) := by
    intro i
    have hi := hy i.succ
    change 0 ≤ w i*evaluate p (t i) at hi
    exact (mul_nonneg_iff_of_pos_left (hw i)).mp hi
  obtain ⟨c,hc,hp⟩ := generated_of_nonnegative t hN ht p hlead hvalues
  refine ⟨c,hc,?_⟩
  have he := congrArg (markedEvaluation w t) hp
  simpa only [map_sum,map_smul,rays] using he

theorem generated_iff_nonnegative_range (hN : 1 ≤ N)
    (hw : ∀ i, 0 < w i) (ht : StrictMono t)
    (y : Fin (N+2) → ℝ) :
    (∃ c : Fin (N+2) → ℝ,
      (∀ e, 0 ≤ c e) ∧ ∑ e, c e • rays w t e = y) ↔
    (∀ i, 0 ≤ y i) ∧ y ∈ (markedEvaluation w t).range := by
  constructor
  · rintro ⟨c,hc,rfl⟩
    constructor
    · intro i
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      exact Finset.sum_nonneg fun e _ =>
        mul_nonneg (hc e) (rays_nonnegative w t hw ht e i)
    · refine ⟨∑ e, c e • generators t e,?_⟩
      simp only [map_sum,map_smul,rays]
  · rintro ⟨hy,hrange⟩
    exact generated_of_nonnegative_range w t hN hw ht y hy hrange

end Ordered

/-- Sorting is a permutation of all original labels, fixing the distinguished
one.  The resulting cone rays generate precisely the nonnegative column space
of the permuted original matrix. -/
theorem exists_sorted_rays {N : ℕ}
    (P : Matrix (Fin (N+3)) (Fin (N+3)) ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) (hrank : P.rank = 3) :
    ∃ σ : Equiv.Perm (Fin (N+3)),
    ∃ r : Fin (N+3) → Fin (N+3) → ℝ,
      σ 0 = 0 ∧ EdgeMoments.RayPattern r ∧
      ∀ y : Fin (N+3) → ℝ,
        (∃ c : Fin (N+3) → ℝ,
          (∀ e, 0 ≤ c e) ∧ ∑ e, c e • r e = y) ↔
        (∀ i, 0 ≤ y i) ∧ y ∈ (P.submatrix σ σ).mulVecLin.range := by
  obtain ⟨w,t,hw,ht,hzero,hfinite⟩ :=
    exists_parameters P hsym hdiag hpos hrank.le
  obtain ⟨τ,hτ⟩ := exists_sorting t ht
  let σ := fixInfinity τ
  let Q := P.submatrix σ σ
  let w' : Fin (N+2) → ℝ := fun i => w (τ i)
  let t' : Fin (N+2) → ℝ := fun i => t (τ i)
  have hQsym : ∀ i j, Q i j = Q j i := fun i j => hsym _ _
  have hQdiag : ∀ i, Q i i = 0 := fun i => hdiag _
  have hQrank : Q.rank = 3 := by
    dsimp [Q]
    rw [Matrix.rank_submatrix,hrank]
  have hQzero : ∀ i, Q 0 i.succ = w' i := by
    intro i
    simpa [Q,σ,Matrix.submatrix,w'] using hzero (τ i)
  have hQfinite : ∀ i j,
      Q i.succ j.succ = (w' i*w' j/2)*(t' i-t' j)^2 := by
    intro i j
    simpa [Q,σ,Matrix.submatrix,w',t'] using hfinite (τ i) (τ j)
  have hrange := range_eq_markedEvaluation Q w' t'
    hQsym hQdiag hQrank hQzero hQfinite
  refine ⟨σ,rays w' t',fixInfinity_zero τ,
    rayPattern w' t' (by omega) (fun i => hw (τ i)) hτ,?_⟩
  intro y
  change _ ↔ (∀ i, 0 ≤ y i) ∧ y ∈ Q.mulVecLin.range
  rw [hrange]
  exact generated_iff_nonnegative_range w' t' (by omega)
    (fun i => hw (τ i)) hτ y

end VolumeVerification.MarkedPolynomialCone

end
end DevelopmentSource7

/- Source module: VolumeVerification.PolygonMeasureObstruction. SHA256: c5fdfbdd06fe9a8ee798185b12121c400de4b5764116304dce84821023dd79b6 -/
section DevelopmentSource8


@[expose] public section
set_option autoImplicit false

/-!
# The polygonal positive-measure obstruction

This is the exact measure-and-linear-algebra conclusion of Proposition 4.2.
Every endpoint weight and moment matrix is defined by an actual integral.
The hypotheses on the measures are the identities obtained from mixed volumes,
the finite cone decomposition, and equality rigidity.
-/
namespace VolumeVerification.PolygonMeasureObstruction
open scoped BigOperators ENNReal Matrix
open MeasureTheory Set
open EdgeMoments
variable {n : ℕ}
variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

private theorem sum_two (f : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b)
    (hzero : ∀ i, i ≠ a → i ≠ b → f i = 0) :
    ∑ i, f i = f a + f b := by
  classical
  have he : ∀ i, f i =
      (if i = a then f a else 0) + (if i = b then f b else 0) := by
    intro i
    by_cases ha : i = a
    · subst i; simp [hab]
    by_cases hb : i = b
    · subst i; simp [Ne.symm hab]
    · simp [ha,hb,hzero i ha hb]
  calc
    (∑ i, f i) =
        ∑ i, ((if i = a then f a else 0) + (if i = b then f b else 0)) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = f a + f b := by simp [Finset.sum_add_distrib]

theorem linear_relation_coordinate
    (Z : Matrix (Fin n) (Fin n) ℝ) (φ : Ω → Fin n → ℝ)
    (w : Fin n → ℝ) (hw : Zᵀ *ᵥ w = 0) (x : Ω) :
    ∑ i, w i * coordinate Z φ i x = 0 := by
  change w ⬝ᵥ (Z *ᵥ φ x) = 0
  rw [← Matrix.dotProduct_transpose_mulVec Z (φ x) w, hw]
  simp

noncomputable def moments (ν : Fin n → Measure Ω) (φ : Ω → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i e => ∫ x, φ x i ∂ν e

noncomputable def alpha (ν : Fin n → Measure Ω)
    (Z : Matrix (Fin n) (Fin n) ℝ) (φ : Ω → Fin n → ℝ) (e : Fin n) : ℝ :=
  ∫ x, |coordinate Z φ e x| ∂ν e

noncomputable def beta (ν : Fin n → Measure Ω)
    (Z : Matrix (Fin n) (Fin n) ℝ) (φ : Ω → Fin n → ℝ) (e : Fin n) : ℝ :=
  ∫ x, |coordinate Z φ (next e) x| ∂ν e

variable (hn : 5 ≤ n)
  (μ ν : Fin n → Measure Ω)
  [∀ i, IsFiniteMeasure (μ i)] [∀ e, IsFiniteMeasure (ν e)]
  (r : Fin n → Fin n → ℝ) (hr : RayPattern r)
  (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
  (P Z : Matrix (Fin n) (Fin n) ℝ)
  (φ : Ω → Fin n → ℝ) (hφ : Continuous φ)
  (hdiag : ∀ i, P i i = 0)
  (hpos : ∀ i j, i ≠ j → 0 < P i j)
  (hpair : ∀ i j, P i j = ∫ x, |coordinate Z φ j x| ∂μ i)
  (hcenter : ∀ i j, ∫ x, φ x j ∂μ i = 0)

include hn hr hdecomp hφ hdiag hpos hpair hcenter in
theorem endpoint_alpha_positive : ∀ e, 0 < alpha ν Z φ e := by
  intro e
  exact (outgoing_moments μ ν r P Z φ hφ hdiag hpos hpair hcenter
    (by omega) hr hdecomp e).2

include hn hr hdecomp hφ hdiag hpos hpair hcenter in
theorem endpoint_beta_positive : ∀ e, 0 < beta ν Z φ e := by
  intro e
  simpa [beta] using
    (incoming_moments μ ν r P Z φ hφ hdiag hpos hpair hcenter
      (by omega) hr hdecomp (next e)).2

include hr hdecomp hφ hdiag hpair in
theorem coordinate_zero_ae_all (e : Fin n) :
    ∀ᵐ x ∂ν e, ∀ i, i ≠ e → i ≠ next e → coordinate Z φ i x = 0 := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi : i = e
  · exact Filter.Eventually.of_forall fun x h => False.elim (h hi)
  by_cases hin : i = next e
  · exact Filter.Eventually.of_forall fun x _ h => False.elim (h hin)
  exact (coordinate_zero_off_edge μ ν r P Z φ hφ hdiag hpair hr hdecomp e i hi hin).mono
    (fun x hx _ _ => hx)

include hn hr hdecomp hφ hdiag hpos hpair hcenter in
theorem relation_zero_propagation :
    ∀ w, Zᵀ *ᵥ w = 0 → ∀ e, w e = 0 → w (finRotate n e) = 0 := by
  intro w hw e he
  by_contra hne
  have hz : coordinate Z φ (next e) =ᵐ[ν e] 0 := by
    filter_upwards [coordinate_zero_ae_all μ ν r hr hdecomp P Z φ hφ hdiag hpair e]
      with x hx
    have hsum : (∑ i, w i * coordinate Z φ i x) =
        w (next e) * coordinate Z φ (next e) x := by
      apply Finset.sum_eq_single (next e)
      · intro i _ hin
        by_cases hie : i = e
        · subst i; rw [he,zero_mul]
        · rw [hx i hie hin,mul_zero]
      · simp
    have hmul : w (next e) * coordinate Z φ (next e) x = 0 := by
      rw [← hsum]
      exact linear_relation_coordinate Z φ w hw x
    exact (mul_eq_zero.mp hmul).resolve_left hne
  have hβ : beta ν Z φ e = 0 := by
    apply integral_eq_zero_of_ae
    exact hz.mono fun x hx => by simp [hx]
  have hposβ := endpoint_beta_positive hn μ ν r hr hdecomp P Z φ hφ hdiag hpos hpair hcenter e
  linarith

include hn hr hdecomp hφ hdiag hpos hpair hcenter in
theorem moment_matrix_kernel : Z * moments ν φ = 0 := by
  ext i e
  change (∑ j, Z i j * ∫ x, φ x j ∂ν e) = 0
  rw [← integral_coordinate (ν e) Z φ hφ i]
  by_cases hi : i = e
  · subst i
    exact (outgoing_moments μ ν r P Z φ hφ hdiag hpos hpair hcenter
      (by omega) hr hdecomp e).1
  by_cases hin : i = next e
  · rw [hin]
    simpa using (incoming_moments μ ν r P Z φ hφ hdiag hpos hpair hcenter
      (by omega) hr hdecomp (next e)).1
  exact integral_eq_zero_of_ae
    (coordinate_zero_off_edge μ ν r P Z φ hφ hdiag hpair hr hdecomp e i hi hin)

theorem cycleIncidence_mul_apply (W : Matrix (Fin (n-3)) (Fin n) ℝ)
    (a b : Fin n → ℝ) (k : Fin (n-3)) (e : Fin n) :
    (W * CycleObstruction.cycleIncidence a b) k e =
      W k e * a e + W k (next e) * b e := by
  simp [Matrix.mul_apply, CycleObstruction.cycleIncidence, next,
    mul_add, mul_ite, Finset.sum_add_distrib]

include hn hr hdecomp hφ hdiag hpair in
theorem moment_factorization
    (W L : Matrix (Fin (n-3)) (Fin n) ℝ)
    (hrigidity : ∀ i, ∀ᵐ x ∂μ i,
      W *ᵥ (fun j => |coordinate Z φ j x|) = L *ᵥ φ x) :
    W * CycleObstruction.cycleIncidence (alpha ν Z φ) (beta ν Z φ) =
      L * moments ν φ := by
  ext k e
  have hc : prev e ≠ e := prev_ne (by omega) e
  have hcn : prev e ≠ next e := prev_ne_next (by omega) e
  have hrig : ∀ᵐ x ∂ν e,
      W *ᵥ (fun j => |coordinate Z φ j x|) = L *ᵥ φ x :=
    transfer_ae μ ν r hr hdecomp e (prev e) hc hcn (hrigidity (prev e))
  have hint := integral_congr_ae (hrig.mono fun x hx => congrFun hx k)
  have hleft :
      (∫ x, (W *ᵥ (fun j => |coordinate Z φ j x|)) k ∂ν e) =
        W k e * alpha ν Z φ e + W k (next e) * beta ν Z φ e := by
    have hi : ∀ i, Integrable (fun x => W k i * |coordinate Z φ i x|) (ν e) := by
      intro i
      exact (continuous_integrable (ν e) _
        (coordinate_continuous Z φ hφ i).abs).const_mul _
    simp only [Matrix.mulVec, dotProduct]
    rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
    simp only [integral_const_mul]
    apply sum_two _ e (next e) (Ne.symm (next_ne (by omega) e))
    intro i hi hin
    have hz := coordinate_zero_off_edge μ ν r P Z φ hφ hdiag hpair
      hr hdecomp e i hi hin
    have hi0 : (∫ x, |coordinate Z φ i x| ∂ν e) = 0 :=
      integral_eq_zero_of_ae (hz.mono fun x hx => by simp [hx])
    rw [hi0,mul_zero]
  have hright :
      (∫ x, (L *ᵥ φ x) k ∂ν e) = (L * moments ν φ) k e := by
    exact integral_matrix_row (ν e) L φ hφ k
  rw [hleft,hright] at hint
  rw [cycleIncidence_mul_apply]
  exact hint

include hn hr hdecomp hφ hdiag hpos hpair hcenter in
/-- No data satisfying the original measure identities and the polygonal
ray pattern can exist in any dimension n >= 5. -/
theorem impossible_positive_polygon_measure_data
    (W : Matrix (Fin (n-3)) (Fin n) ℝ) (hW : W.rank = n-3)
    (L : Matrix (Fin (n-3)) (Fin n) ℝ)
    (hrigidity : ∀ i, ∀ᵐ x ∂μ i,
      W *ᵥ (fun j => |coordinate Z φ j x|) = L *ᵥ φ x) :
    False := by
  letI : NeZero n := ⟨by omega⟩
  exact CycleObstruction.no_cycle_factorization hn W hW Z
    (relation_zero_propagation hn μ ν r hr hdecomp P Z φ hφ hdiag hpos hpair hcenter)
    (alpha ν Z φ) (beta ν Z φ)
    (endpoint_alpha_positive hn μ ν r hr hdecomp P Z φ hφ hdiag hpos hpair hcenter)
    (endpoint_beta_positive hn μ ν r hr hdecomp P Z φ hφ hdiag hpos hpair hcenter)
    L (moments ν φ)
    (moment_matrix_kernel hn μ ν r hr hdecomp P Z φ hφ hdiag hpos hpair hcenter)
    (moment_factorization hn μ ν r hr hdecomp P Z φ hφ hdiag hpair W L hrigidity)

end VolumeVerification.PolygonMeasureObstruction

end
end DevelopmentSource8

/- Source module: VolumeVerification.ProjectionLinearRelations. SHA256: 2fcc9891a966d7d54ffd96cc80884f6eb9e50ba5f21e046bd7418121498ed80c -/
section DevelopmentSource9




@[expose] public section
set_option autoImplicit false

/-!
# A full-rank system of equations for the column space

The matrix W is constructed from the actual quotient by the column space.
Its full row rank, its kernel, and its row relations follow from that
construction.  No basis-size or rank hypothesis is added to the application.
-/
namespace VolumeVerification.ProjectionLinearRelations
open scoped BigOperators Matrix
open Module

theorem exists_relation_matrix {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hrank : P.rank = 3) :
    ∃ W : Matrix (Fin (n-3)) (Fin n) ℝ,
      W.rank = n-3 ∧
      (∀ y, W *ᵥ y = 0 ↔ y ∈ P.mulVecLin.range) ∧
      W * P = 0 := by
  classical
  let S : Submodule ℝ (Fin n → ℝ) := P.mulVecLin.range
  have hdim : finrank ℝ ((Fin n → ℝ) ⧸ S) = n-3 := by
    have h := S.finrank_quotient_add_finrank
    have hS : finrank ℝ S = 3 := hrank
    simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,hS] at h
    omega
  let e : ((Fin n → ℝ) ⧸ S) ≃ₗ[ℝ] (Fin (n-3) → ℝ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hdim])
  let f : (Fin n → ℝ) →ₗ[ℝ] (Fin (n-3) → ℝ) :=
    e.toLinearMap.comp S.mkQ
  let W : Matrix (Fin (n-3)) (Fin n) ℝ := f.toMatrix'
  have hWmap : W.mulVecLin = f := by
    apply LinearMap.ext
    intro y
    change f.toMatrix' *ᵥ y = f y
    exact LinearMap.toMatrix'_mulVec f y
  have hsurj : Function.Surjective f :=
    e.surjective.comp S.mkQ_surjective
  have hWrank : W.rank = n-3 := by
    change finrank ℝ W.mulVecLin.range = n-3
    rw [hWmap,LinearMap.range_eq_top.mpr hsurj]
    simp
  have hker : ∀ y, W *ᵥ y = 0 ↔ y ∈ S := by
    intro y
    change f.toMatrix' *ᵥ y = 0 ↔ y ∈ S
    rw [LinearMap.toMatrix'_mulVec]
    change e (S.mkQ y) = 0 ↔ y ∈ S
    rw [e.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero S
  refine ⟨W,hWrank,hker,?_⟩
  ext k j
  have hc : (fun i => P i j) ∈ S := by
    refine ⟨Pi.single j 1,?_⟩
    ext i
    simp [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,Pi.single_apply]
  exact congrFun ((hker _).mpr hc) k

theorem rows_in_kernel {m n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, P i j = P j i)
    (W : Matrix (Fin m) (Fin n) ℝ) (hWP : W*P = 0) (k : Fin m) :
    P *ᵥ W k = 0 := by
  ext i
  calc
    (P *ᵥ W k) i = (W*P) k i := by
      simp only [Matrix.mulVec,dotProduct,Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      change P i j * W k j = W k j * P j i
      rw [hsym i j,mul_comm]
    _ = 0 := by rw [hWP]; rfl

theorem sum_permute {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (σ : Equiv.Perm ι) (f : ι → M) :
    ∑ i, f (σ i) = ∑ i, f i := by
  exact Equiv.sum_comp σ f

theorem reindex_columns_mulVec {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (y : Fin n → ℝ) :
    (W.submatrix id σ) *ᵥ y = W *ᵥ (fun i => y (σ.symm i)) := by
  ext k
  simpa [Matrix.submatrix,Matrix.mulVec,dotProduct] using
    sum_permute σ (fun i => W k i*y (σ.symm i))

theorem reindex_square_mulVec {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) :
    (P.submatrix σ σ) *ᵥ (fun i => x (σ i)) =
      fun i => (P *ᵥ x) (σ i) := by
  ext i
  simpa [Matrix.submatrix,Matrix.mulVec,dotProduct] using
    sum_permute σ (fun j => P (σ i) j*x j)

theorem reindex_range_iff {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (y : Fin n → ℝ) :
    y ∈ (P.submatrix σ σ).mulVecLin.range ↔
      (fun i => y (σ.symm i)) ∈ P.mulVecLin.range := by
  constructor
  · rintro ⟨x,hx⟩
    change (P.submatrix σ σ) *ᵥ x = y at hx
    refine ⟨fun i => x (σ.symm i),?_⟩
    have he := reindex_square_mulVec P σ (fun i => x (σ.symm i))
    simp only [Equiv.symm_apply_apply] at he
    ext i
    have hi := congrFun he (σ.symm i)
    simpa [Matrix.mulVecLin_apply,hx] using hi.symm
  · rintro ⟨x,hx⟩
    refine ⟨fun i => x (σ i),?_⟩
    rw [Matrix.mulVecLin_apply,reindex_square_mulVec]
    ext i
    have hi := congrFun hx (σ i)
    simpa [Matrix.mulVecLin_apply] using hi

theorem reindex_relation_matrix {m n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (W : Matrix (Fin m) (Fin n) ℝ)
    (hker : ∀ y, W *ᵥ y = 0 ↔ y ∈ P.mulVecLin.range)
    (σ : Equiv.Perm (Fin n)) :
    ∀ y, (W.submatrix id σ) *ᵥ y = 0 ↔
      y ∈ (P.submatrix σ σ).mulVecLin.range := by
  intro y
  rw [reindex_columns_mulVec,hker,reindex_range_iff]

end VolumeVerification.ProjectionLinearRelations

end
end DevelopmentSource9

/- Source module: VolumeVerification.ProjectionMeasureReduction. SHA256: e2c567420c90a67d608b16d247f26bca7499d095da6726b9ac16be2fed3dd224 -/
section DevelopmentSource10


@[expose] public section
set_option autoImplicit false

/-!
# From the mixed-area identities to the full-dimensional obstruction

This theorem removes the finite-cone, measurable-selection and moment-matrix
interfaces from the geometric proof.  Its remaining geometric inputs are
the actual centered mixed-area measures, their mixed-volume pairing, and
the equality-rigidity implications.  Those implications must still be proved
for convex bodies; they are not declared as axioms here.
-/
namespace VolumeVerification.ProjectionMeasureReduction
open scoped BigOperators ENNReal Matrix
open MeasureTheory Set
open ProjectionLinearRelations
open EdgeMoments

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

theorem impossible_measure_data {n : ℕ} (hn : 5 ≤ n)
    (P Z : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, P i j = P j i)
    (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (hrank : P.rank = 3)
    (μ : Fin n → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (φ : Ω → Fin n → ℝ) (hφ : Continuous φ)
    (hpair : ∀ i j, P i j = ∫ x, |coordinate Z φ j x| ∂μ i)
    (hcenter : ∀ i j, ∫ x, φ x j ∂μ i = 0)
    (hrelations : ∀ w : Fin n → ℝ, P *ᵥ w = 0 →
      ∀ s, MeasurableSet s → ∑ i, w i*(μ i).real s = 0)
    (hrigidity : ∀ w : Fin n → ℝ, P *ᵥ w = 0 →
      ∃ l : Fin n → ℝ, ∀ i, ∀ᵐ x ∂μ i,
        (∑ j, w j*|coordinate Z φ j x|) = ∑ j, l j*φ x j) :
    False := by
  classical
  obtain ⟨N,rfl⟩ : ∃ N, n = N+3 := ⟨n-3,by omega⟩
  obtain ⟨W,hWrank,hWker,hWP⟩ := exists_relation_matrix P hrank
  choose L hL using fun k : Fin (N+3-3) =>
    hrigidity (W k) (rows_in_kernel P hsym W hWP k)
  obtain ⟨σ,r,_,hr,hcone⟩ :=
    MarkedPolynomialCone.exists_sorted_rays P hsym hdiag hpos hrank
  let Q := P.submatrix σ σ
  let Z' := Z.submatrix σ id
  let W' := W.submatrix id σ
  let μ' : Fin (N+3) → Measure Ω := fun i => μ (σ i)
  letI : ∀ i, IsFiniteMeasure (μ' i) := fun i => inferInstance
  let μtotal : Measure Ω := ∑ i, μ' i
  letI : IsFiniteMeasure μtotal := by
    dsimp [μtotal]
    infer_instance
  have hdom : ∀ i, μ' i ≤ μtotal := by
    intro i
    exact Finset.single_le_sum (fun j _ => Measure.zero_le _) (Finset.mem_univ i)
  have hWr : ∀ k s, MeasurableSet s →
      ∑ i, W' k i*(μ' i).real s = 0 := by
    intro k s hs
    change (∑ i, W k (σ i)*(μ (σ i)).real s) = 0
    exact (sum_permute σ (fun i => W k i * (μ i).real s)).trans
      (hrelations (W k) (rows_in_kernel P hsym W hWP k) s hs)
  have hspan : ∀ y : Fin (N+3) → ℝ,
      (∀ i, 0 ≤ y i) → W' *ᵥ y = 0 →
      ∃ c : Fin (N+3) → ℝ, (∀ e, 0 ≤ c e) ∧ ∑ e, c e • r e = y := by
    intro y hy hWy
    apply (hcone y).mpr
    refine ⟨hy,?_⟩
    exact (reindex_relation_matrix P W hWker σ y).mp hWy
  obtain ⟨ν,hν,hdecomp⟩ :=
    ConeMeasureDecomposition.decompose_positive_measure_vector
      μtotal μ' hdom W' r (ray_nonnegative r hr) hspan hWr
  letI : ∀ e, IsFiniteMeasure (ν e) := hν
  have hW'rank : W'.rank = N+3-3 := by
    dsimp [W']
    simpa using (Matrix.rank_submatrix W (Equiv.refl _) σ).trans hWrank
  have hQdiag : ∀ i, Q i i = 0 := fun i => hdiag _
  have hQpos : ∀ i j, i ≠ j → 0 < Q i j := by
    intro i j hij
    exact hpos _ _ (fun h => hij (σ.injective h))
  have hcoord : ∀ j x, coordinate Z' φ j x = coordinate Z φ (σ j) x := by
    intro j x
    rfl
  have hQpair : ∀ i j, Q i j = ∫ x, |coordinate Z' φ j x| ∂μ' i := by
    intro i j
    simpa only [Q, μ', Matrix.submatrix_apply, hcoord] using hpair (σ i) (σ j)
  have hQcenter : ∀ i j, ∫ x, φ x j ∂μ' i = 0 :=
    fun i j => hcenter (σ i) j
  have hrig : ∀ i, ∀ᵐ x ∂μ' i,
      W' *ᵥ (fun j => |coordinate Z' φ j x|) = L *ᵥ φ x := by
    intro i
    have hall : ∀ᵐ x ∂μ (σ i), ∀ k : Fin (N+3-3),
        (∑ j, W k j*|coordinate Z φ j x|) =
          ∑ j, L k j*φ x j :=
      ae_all_iff.mpr fun k => hL k (σ i)
    filter_upwards [hall] with x hx
    ext k
    change (∑ j, W k (σ j)*|coordinate Z' φ j x|) = _
    simp only [hcoord]
    simpa only [Matrix.mulVec, dotProduct] using
      (sum_permute σ (fun j => W k j * |coordinate Z φ j x|)).trans (hx k)
  exact PolygonMeasureObstruction.impossible_positive_polygon_measure_data
    hn μ' ν r hr hdecomp Q Z' φ hφ hQdiag hQpos hQpair hQcenter
    W' hW'rank L hrig

end VolumeVerification.ProjectionMeasureReduction

end
end DevelopmentSource10

#check @VolumeVerification.ProjectionMeasureReduction.impossible_measure_data
#print axioms VolumeVerification.ProjectionMeasureReduction.impossible_measure_data
#assert_standard_axioms VolumeVerification.ProjectionMeasureReduction.impossible_measure_data
#export_checked_module_dependencies ".lake/reports/verification/FiniteObstruction.dependencies.json"
