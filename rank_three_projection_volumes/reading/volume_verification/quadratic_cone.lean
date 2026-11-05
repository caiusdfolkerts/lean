module
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Logic.Equiv.Fin.Rotate
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

