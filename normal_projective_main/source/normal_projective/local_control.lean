module
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
/-! # The explicit local 2d normal–projective control word -/
@[expose] public section
noncomputable section
open Set Filter Matrix
open scoped BigOperators Topology
namespace NormalProjective.LocalControl
variable {n : ℕ} {ι : Type*} [Fintype ι]

abbrev NormalMatrix (ι : Type*) (n : ℕ) := Matrix ι (Fin (n + 1)) ℝ
abbrev MatrixData (ι : Type*) (n : ℕ) := NormalMatrix ι n × (ι → ℝ)

def ratio (A B : NormalMatrix ι n) (i : ι) : ℝ :=
  A i (Fin.last n) / B i (Fin.last n)

def support (A B : NormalMatrix ι n) (η : ℝ) (j : Fin (n + 1)) (i : ι) : ℝ :=
  if j = Fin.last n then ratio A B i
  else ratio A B i + (ratio A B i * B i j - A i j) / η

def stage (A B : NormalMatrix ι n) (η : ℝ) (k : ℕ) : NormalMatrix ι n :=
  fun i j => A i j + if j.val < k then η * support A B η j i else 0

def direction (η : ℝ) (j : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  if j = Fin.last n then
    fun k => if k.val < n then -η else 0
  else fun k => if k = j then η else 0

def beforeData (A B : NormalMatrix ι n) (η : ℝ) (j : Fin (n + 1)) : MatrixData ι n :=
  (stage A B η j.val,
    if hj : j.val = 0 then fun _ => 1
    else support A B η ⟨j.val - 1, by omega⟩)

def afterNormalData (A B : NormalMatrix ι n) (η : ℝ) (j : Fin (n + 1)) :
    MatrixData ι n := (stage A B η j.val, support A B η j)

def finalData (A B : NormalMatrix ι n) : MatrixData ι n :=
  ((fun i j => ratio A B i * B i j), ratio A B)

@[simp] theorem stage_zero (A B : NormalMatrix ι n) (η : ℝ) : stage A B η 0 = A := by
  ext i j
  simp [stage]

theorem stage_step (A B : NormalMatrix ι n) (η : ℝ) (j : Fin n) :
    stage A B η (j.val + 1) =
      stage A B η j.val + Matrix.vecMulVec (support A B η j.castSucc)
        (direction η j.castSucc) := by
  have hj : j.castSucc ≠ Fin.last n := Fin.castSucc_ne_last j
  ext i k
  simp only [stage, Matrix.add_apply, Matrix.vecMulVec_apply, direction, if_neg hj]
  by_cases hkj : k = j.castSucc
  · subst k
    simp
    ring
  · have hval : k.val ≠ j.val := by
      intro hh
      apply hkj
      exact Fin.ext hh
    have hiff : k.val < j.val + 1 ↔ k.val < j.val := by omega
    simp [hkj, hiff]

theorem final_step (A B : NormalMatrix ι n) (η : ℝ) (hη : η ≠ 0)
    (hB : ∀ i, B i (Fin.last n) ≠ 0) :
    stage A B η n + Matrix.vecMulVec (support A B η (Fin.last n))
      (direction η (Fin.last n)) = (finalData A B).1 := by
  ext i j
  by_cases hj : j = Fin.last n
  · subst j
    simp [stage, support, direction, finalData, ratio, hB i, Matrix.vecMulVec]
  · have hjn : j.val < n := by
      have hne : j.val ≠ n := fun hh => hj (Fin.ext hh)
      omega
    simp [stage, support, direction, finalData, hj, hjn, Matrix.vecMulVec, ratio]
    field_simp [hη]
    ring

@[simp] theorem ratio_self (A : NormalMatrix ι n) (hA : ∀ i, A i (Fin.last n) ≠ 0) :
    ratio A A = fun _ => 1 := by
  funext i
  exact div_self (hA i)

@[simp] theorem support_self (A : NormalMatrix ι n) (hA : ∀ i, A i (Fin.last n) ≠ 0)
    (η : ℝ) (j : Fin (n + 1)) : support A A η j = fun _ => 1 := by
  ext i
  simp [support, ratio_self A hA]

theorem stage_self (A : NormalMatrix ι n) (hA : ∀ i, A i (Fin.last n) ≠ 0)
    (η : ℝ) (k : ℕ) :
    stage A A η k = fun i j => A i j + if j.val < k then η else 0 := by
  ext i j
  simp [stage, support_self A hA]

theorem continuousAt_ratio (A : NormalMatrix ι n) (hA : ∀ i, A i (Fin.last n) ≠ 0) :
    ContinuousAt (fun B => ratio A B) A := by
  apply continuousAt_pi.mpr
  intro i
  exact continuousAt_const.div
    ((continuous_apply (Fin.last n)).comp (continuous_apply i)).continuousAt (hA i)

theorem continuousAt_support (A : NormalMatrix ι n)
    (hA : ∀ i, A i (Fin.last n) ≠ 0) (η : ℝ) (j : Fin (n + 1)) :
    ContinuousAt (fun B => support A B η j) A := by
  apply continuousAt_pi.mpr
  intro i
  by_cases hj : j = Fin.last n
  · simp only [support, if_pos hj]
    exact continuousAt_pi.mp (continuousAt_ratio A hA) i
  · simp only [support, if_neg hj]
    have hri := continuousAt_pi.mp (continuousAt_ratio A hA) i
    exact hri.add
      (((hri.mul ((continuous_apply j).comp (continuous_apply i)).continuousAt).sub
        continuousAt_const).div_const η)

theorem continuousAt_stage (A : NormalMatrix ι n)
    (hA : ∀ i, A i (Fin.last n) ≠ 0) (η : ℝ) (k : ℕ) :
    ContinuousAt (fun B => stage A B η k) A := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  by_cases hj : j.val < k
  · simp only [stage, if_pos hj]
    exact continuousAt_const.add
      (continuousAt_const.mul (continuousAt_pi.mp (continuousAt_support A hA η j) i))
  · simp only [stage, if_neg hj]
    exact continuousAt_const

theorem baseline_stage_continuous (A : NormalMatrix ι n)
    (hA : ∀ i, A i (Fin.last n) ≠ 0) (k : ℕ) :
    Continuous (fun η => stage A A η k) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hj : j.val < k
  · simp only [stage, support_self A hA, if_pos hj, mul_one]
    exact continuous_const.add continuous_id
  · simp only [stage, if_neg hj]
    exact continuous_const

theorem baseline_before_continuous (A : NormalMatrix ι n)
    (hA : ∀ i, A i (Fin.last n) ≠ 0) (j : Fin (n + 1)) :
    Continuous (fun η => beforeData A A η j) := by
  by_cases hj : j.val = 0
  · simpa only [beforeData, dif_pos hj] using
      (baseline_stage_continuous A hA j.val).prodMk
        (continuous_const : Continuous (fun _ : ℝ => (fun _ : ι => (1 : ℝ))))
  · simpa only [beforeData, dif_neg hj, support_self A hA] using
      (baseline_stage_continuous A hA j.val).prodMk
        (continuous_const : Continuous (fun _ : ℝ => (fun _ : ι => (1 : ℝ))))

theorem baseline_after_continuous (A : NormalMatrix ι n)
    (hA : ∀ i, A i (Fin.last n) ≠ 0) (j : Fin (n + 1)) :
    Continuous (fun η => afterNormalData A A η j) := by
  simpa only [afterNormalData, support_self A hA] using
    (baseline_stage_continuous A hA j.val).prodMk
      (continuous_const : Continuous (fun _ : ℝ => (fun _ : ι => (1 : ℝ))))

@[simp] theorem baseline_before_zero (A : NormalMatrix ι n)
    (hA : ∀ i, A i (Fin.last n) ≠ 0) (j : Fin (n + 1)) :
    beforeData A A 0 j = (A, fun _ => 1) := by
  simp [beforeData, stage_self A hA, support_self A hA]

@[simp] theorem baseline_after_zero (A : NormalMatrix ι n)
    (hA : ∀ i, A i (Fin.last n) ≠ 0) (j : Fin (n + 1)) :
    afterNormalData A A 0 j = (A, fun _ => 1) := by
  simp [afterNormalData, stage_self A hA, support_self A hA]

theorem continuousAt_before (A : NormalMatrix ι n)
    (hA : ∀ i, A i (Fin.last n) ≠ 0) (η : ℝ) (j : Fin (n + 1)) :
    ContinuousAt (fun B => beforeData A B η j) A := by
  unfold beforeData
  apply ContinuousAt.prodMk (continuousAt_stage A hA η j.val)
  split_ifs
  · exact continuousAt_const
  · exact continuousAt_support A hA η _

theorem continuousAt_after (A : NormalMatrix ι n)
    (hA : ∀ i, A i (Fin.last n) ≠ 0) (η : ℝ) (j : Fin (n + 1)) :
    ContinuousAt (fun B => afterNormalData A B η j) A :=
  (continuousAt_stage A hA η j.val).prodMk (continuousAt_support A hA η j)

theorem continuousAt_final (A : NormalMatrix ι n)
    (hA : ∀ i, A i (Fin.last n) ≠ 0) :
    ContinuousAt (fun B => finalData A B) A := by
  apply ContinuousAt.prodMk _ (continuousAt_ratio A hA)
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (continuousAt_pi.mp (continuousAt_ratio A hA) i).mul
    ((continuous_apply j).comp (continuous_apply i)).continuousAt

@[simp] theorem final_self (A : NormalMatrix ι n) (hA : ∀ i, A i (Fin.last n) ≠ 0) :
    finalData A A = (A, fun _ => 1) := by
  simp [finalData, ratio_self A hA]

end NormalProjective.LocalControl

