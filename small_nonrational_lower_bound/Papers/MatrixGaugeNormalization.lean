module
public import Papers.RationalKernelCharts
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.FunProp

@[expose] public section
noncomputable section
open Matrix Set Filter Topology
open scoped BigOperators

namespace Papers.MatrixGaugeNormalization

variable {ι : Type*} [DecidableEq ι]

/-- An ordered rooted forest: every edge introduces one previously unassigned node. -/
inductive ValidSteps (w : ι→ι→ℝ) : Finset ι → List (ι×ι) → Prop
  | nil (S) : ValidSteps w S []
  | cons {S u v t} (hu : u∈S) (hv : v∉S) (hw : w u v≠0)
      (ht : ValidSteps w (insert v S) t) : ValidSteps w S ((u,v)::t)

def step (w : ι→ι→ℝ) (a : ι→ℝ) (u v : ι) : ι→ℝ :=
  Function.update a v (w u v*a u)⁻¹

def run (w : ι→ι→ℝ) : List (ι×ι) → (ι→ℝ) → (ι→ℝ)
  | [],a => a
  | (u,v)::t,a => run w t (step w a u v)

theorem run_correct (w : ι→ι→ℝ) {S : Finset ι} {t : List (ι×ι)}
    (h : ValidSteps w S t) (a : ι→ℝ) (ha : ∀i,a i≠0) :
    (∀i,run w t a i≠0) ∧
    (∀i∈S,run w t a i=a i) ∧
    ∀e∈t,run w t a e.1*w e.1 e.2*run w t a e.2=1 := by
  induction h generalizing a with
  | nil S => exact ⟨ha,fun _ _ => rfl,by simp⟩
  | @cons S u v t hu hv hw ht ih =>
    have huv : u≠v := fun heq => hv (heq ▸ hu)
    have hstep : ∀i,step w a u v i≠0 := by
      intro i
      by_cases hi : i=v
      · subst i
        simpa only [step,Function.update_self] using inv_ne_zero (mul_ne_zero hw (ha u))
      · simpa only [step,Function.update_of_ne hi] using ha i
    obtain ⟨hn,hfixed,hedges⟩ := ih (step w a u v) hstep
    refine ⟨hn,?_,?_⟩
    · intro i hi
      have hiv : i≠v := fun heq => hv (heq ▸ hi)
      exact (hfixed i (Finset.mem_insert_of_mem hi)).trans
        (Function.update_of_ne hiv _ _)
    · intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e
        change run w t (step w a u v) u*w u v*run w t (step w a u v) v=1
        rw [hfixed u (Finset.mem_insert_of_mem hu),hfixed v (Finset.mem_insert_self _ _)]
        simp only [step,Function.update_of_ne huv,Function.update_self]
        rw [mul_comm (a u) (w u v),mul_inv_cancel₀ (mul_ne_zero hw (ha u))]
      · exact hedges e he

theorem exists_forest_normalization (w : ι→ι→ℝ) {S : Finset ι}
    {t : List (ι×ι)} (h : ValidSteps w S t) :
    ∃a : ι→ℝ,(∀i,a i≠0) ∧ (∀i∈S,a i=1) ∧
      ∀e∈t,a e.1*w e.1 e.2*a e.2=1 :=
  ⟨run w t (fun _ => 1),run_correct w h _ (fun _ => one_ne_zero)⟩

def scaleRowsColumns {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (a : Fin n→ℝ) (b : Fin r→ℝ) : Matrix (Fin n) (Fin r) ℝ :=
  Matrix.of (fun i j => a i*p i j*b j)

theorem scaleRowsColumns_matrix {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (a : Fin n→ℝ) (b : Fin r→ℝ) :
    scaleRowsColumns p a b=Matrix.diagonal a*p*Matrix.diagonal b := by
  ext i j
  simp [scaleRowsColumns,Matrix.diagonal_mul,Matrix.mul_diagonal]

theorem scaleRowsColumns_minor {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (a : Fin n→ℝ) (b : Fin r→ℝ) (s : Fin r→Fin n) :
    ((scaleRowsColumns p a b).submatrix s id).det=
      (∏i,a (s i))*(p.submatrix s id).det*(∏j,b j) := by
  have heq : (scaleRowsColumns p a b).submatrix s id=
      Matrix.diagonal (a∘s)*(p.submatrix s id)*Matrix.diagonal b := by
    ext i j
    simp [scaleRowsColumns,Matrix.submatrix,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rw [heq,Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal,Matrix.det_diagonal]
  rfl

theorem scaleRowsColumns_zero_minor_iff {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (a : Fin n→ℝ) (b : Fin r→ℝ)
    (ha : ∀i,a i≠0) (hb : ∀j,b j≠0) (s : Fin r→Fin n) :
    ((scaleRowsColumns p a b).submatrix s id).det=0 ↔ (p.submatrix s id).det=0 := by
  rw [scaleRowsColumns_minor]
  have hA : (∏i,a (s i))≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => ha (s i))
  have hB : (∏j,b j)≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hb j)
  simp only [mul_eq_zero,hA,hB,false_or,or_false]

theorem scaleRowsColumns_inverse {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (a : Fin n→ℝ) (b : Fin r→ℝ) (ha : ∀i,a i≠0) (hb : ∀j,b j≠0) :
    scaleRowsColumns (scaleRowsColumns p a b) (fun i => (a i)⁻¹) (fun j => (b j)⁻¹)=p := by
  ext i j
  simp only [scaleRowsColumns,Matrix.of_apply]
  field_simp [ha i,hb j]

theorem scaleRowsColumns_rational {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (a : Fin n→ℝ) (b : Fin r→ℝ)
    (hp : Papers.RationalKernelCharts.RationalCoordinates p)
    (ha : ∀i,Papers.RationalKernelCharts.RatScalar (a i))
    (hb : ∀j,Papers.RationalKernelCharts.RatScalar (b j)) :
    Papers.RationalKernelCharts.RationalCoordinates (scaleRowsColumns p a b) :=
  fun i j => ((ha i).mul (hp i j)).mul (hb j)

theorem continuous_scaleRowsColumns (n r : ℕ) :
    Continuous (fun z : Matrix (Fin n) (Fin r) ℝ × (Fin n→ℝ) × (Fin r→ℝ) =>
      scaleRowsColumns z.1 z.2.1 z.2.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : Matrix (Fin n) (Fin r) ℝ × (Fin n→ℝ) × (Fin r→ℝ) =>
    z.2.1 i*z.1 i j*z.2.2 j)
  fun_prop

end Papers.MatrixGaugeNormalization
