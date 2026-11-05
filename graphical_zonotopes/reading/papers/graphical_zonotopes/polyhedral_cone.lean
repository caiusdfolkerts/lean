module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Tauto
public import Aesop

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! A finite system of homogeneous linear inequalities and its exact extreme-ray criterion. -/
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Polyhedral
variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]

def Nonnegative (A : I → E →ₗ[ℝ] ℝ) (y : E) : Prop := ∀ i, 0 ≤ A i y

def Pointed (A : I → E →ₗ[ℝ] ℝ) : Prop :=
  ∀ y, (∀ i, A i y = 0) → y = 0

def ExtremeRay (A : I → E →ₗ[ℝ] ℝ) (y : E) : Prop :=
  Nonnegative A y ∧ y ≠ 0 ∧
  ∀ u v, Nonnegative A u → Nonnegative A v → u + v = y →
    ∃ a : ℝ, 0 ≤ a ∧ u = a • y

def tightKernel (A : I → E →ₗ[ℝ] ℝ) (y : E) : Submodule ℝ E where
  carrier := {v | ∀ i, A i y = 0 → A i v = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv i hi; simp [hu i hi, hv i hi]
  smul_mem' := by intro a v hv i hi; simp [hv i hi]

@[simp] theorem mem_tightKernel (A : I → E →ₗ[ℝ] ℝ) (y v : E) :
    v ∈ tightKernel A y ↔ ∀ i, A i y = 0 → A i v = 0 := Iff.rfl

theorem self_mem_tightKernel (A : I → E →ₗ[ℝ] ℝ) (y : E) : y ∈ tightKernel A y :=
  fun _ h => h

theorem Pointed.exists_positive {A : I → E →ₗ[ℝ] ℝ} (hA : Pointed A)
    {y : E} (hy : Nonnegative A y) (hne : y ≠ 0) : ∃ i, 0 < A i y := by
  by_contra h
  push_neg at h
  exact hne (hA y (fun i => le_antisymm (h i) (hy i)))

theorem summand_mem_tightKernel {A : I → E →ₗ[ℝ] ℝ} {y u v : E}
    (hu : Nonnegative A u) (hv : Nonnegative A v) (he : u + v = y) :
    u ∈ tightKernel A y := by
  intro i hi
  have hsum : A i u + A i v = 0 := by rw [← map_add, he, hi]
  have h1 := hu i
  have h2 := hv i
  linarith

theorem extremeRay_of_tightKernel {A : I → E →ₗ[ℝ] ℝ} (hA : Pointed A)
    {y : E} (hy : Nonnegative A y) (hne : y ≠ 0)
    (hk : tightKernel A y = Submodule.span ℝ {y}) : ExtremeRay A y := by
  refine ⟨hy, hne, ?_⟩
  intro u v hu hv he
  have huK := summand_mem_tightKernel hu hv he
  rw [hk, Submodule.mem_span_singleton] at huK
  obtain ⟨a, ha⟩ := huK
  refine ⟨a, ?_, ha.symm⟩
  obtain ⟨i, hi⟩ := hA.exists_positive hy hne
  have h := hu i
  rw [← ha, map_smul, smul_eq_mul] at h
  exact nonneg_of_mul_nonneg_left h hi

theorem exists_two_sided_perturbation {A : I → E →ₗ[ℝ] ℝ} {y v : E}
    (hy : Nonnegative A y) (hv : v ∈ tightKernel A y) :
    ∃ ε : ℝ, 0 < ε ∧ Nonnegative A ((1 / 2 : ℝ) • y + ε • v) ∧
      Nonnegative A ((1 / 2 : ℝ) • y - ε • v) := by
  classical
  have aux : ∀ s : Finset I, ∃ ε : ℝ, 0 < ε ∧
      ∀ i ∈ s, ε * |A i v| ≤ A i y / 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      by_cases hyi : A i y = 0
      · refine ⟨ε, hε, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          simp [hyi, hv i hyi]
        · exact hbound j hj
      · have hyi' : 0 < A i y := lt_of_le_of_ne (hy i) (Ne.symm hyi)
        let δ := min ε (A i y / (2 * (|A i v| + 1)))
        have hδ : 0 < δ := lt_min hε (div_pos hyi' (by positivity))
        refine ⟨δ, hδ, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          have hle : δ ≤ A i y / (2 * (|A i v| + 1)) := min_le_right _ _
          have hm := (le_div_iff₀ (show 0 < 2 * (|A i v| + 1) by positivity)).mp hle
          nlinarith
        · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)).trans
            (hbound j hj)
  obtain ⟨ε, hε, hbound⟩ := aux Finset.univ
  refine ⟨ε, hε, ?_, ?_⟩
  · intro i
    simp only [map_add, map_smul, smul_eq_mul]
    have h1 := hbound i (Finset.mem_univ i)
    have h2 := neg_abs_le (A i v)
    nlinarith
  · intro i
    simp only [map_sub, map_smul, smul_eq_mul]
    have h1 := hbound i (Finset.mem_univ i)
    have h2 := le_abs_self (A i v)
    nlinarith

theorem ExtremeRay.tightKernel_eq_span {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : ExtremeRay A y) : tightKernel A y = Submodule.span ℝ {y} := by
  apply le_antisymm
  · intro v hv
    obtain ⟨ε, hε, hp, hm⟩ := exists_two_sided_perturbation hy.1 hv
    have he : ((1 / 2 : ℝ) • y + ε • v) + ((1 / 2 : ℝ) • y - ε • v) = y := by module
    obtain ⟨a, ha, hae⟩ := hy.2.2 _ _ hp hm he
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(a - 1 / 2) / ε, ?_⟩
    have hvε : ε • v = (a - 1 / 2) • y := by
      rw [sub_smul]
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hae)
    calc
      ((a - 1 / 2) / ε) • y = ε⁻¹ • ((a - 1 / 2) • y) := by
        rw [smul_smul]; congr 1; ring
      _ = ε⁻¹ • (ε • v) := by rw [hvε]
      _ = v := by rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hε), one_smul]
  · exact Submodule.span_le.mpr (by
      intro v hv
      have hvy : v = y := Set.mem_singleton_iff.mp hv
      subst v
      exact self_mem_tightKernel A y)

theorem extremeRay_iff_tightKernel {A : I → E →ₗ[ℝ] ℝ} (hA : Pointed A)
    {y : E} (hy : Nonnegative A y) (hne : y ≠ 0) :
    ExtremeRay A y ↔ tightKernel A y = Submodule.span ℝ {y} :=
  ⟨ExtremeRay.tightKernel_eq_span, extremeRay_of_tightKernel hA hy hne⟩

end Polyhedral
end GraphicalZonotopes
