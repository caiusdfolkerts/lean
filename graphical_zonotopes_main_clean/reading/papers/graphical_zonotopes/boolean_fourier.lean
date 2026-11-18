module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Cube (I : Type*) := I → Bool

def spin (b : Bool) : ℝ := if b then -1 else 1

theorem spin_isSign (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

@[simp] theorem spin_mul_self (b : Bool) : spin b*spin b=1 := by
  cases b <;> norm_num [spin]

theorem spin_ne_zero (b : Bool) : spin b ≠ 0 := by
  cases b <;> norm_num [spin]

def character (A : Finset I) (u : Cube I) : ℝ :=
  ∏ i, if i∈A then spin (u i) else 1

@[simp] theorem character_empty (u : Cube I) : character ∅ u=1 := by
  simp [character]

@[simp] theorem character_univ (u : Cube I) :
    character univ u=∏ i,spin (u i) := by
  simp [character]

theorem character_ne_zero (A : Finset I) (u : Cube I) : character A u≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs <;> simp [spin_ne_zero]

@[simp] theorem character_square (A : Finset I) (u : Cube I) :
    character A u*character A u=1 := by
  simp only [character,← prod_mul_distrib]
  have h : ∀ i : I,(if i∈A then spin (u i) else 1)*
      (if i∈A then spin (u i) else 1)=1 := by
    intro i
    split_ifs <;> simp
  simp only [h,prod_const_one]

theorem character_compl (A : Finset I) (u : Cube I) :
    character univ u*character A u=character Aᶜ u := by
  simp only [character,mem_univ,ite_true,← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  by_cases h : i∈A <;> simp [h]

theorem character_orthogonality (A B : Finset I) :
    (∑ u : Cube I,character A u*character B u)=
      if A=B then (2 : ℝ)^Fintype.card I else 0 := by
  simp only [character,← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    (if i∈A then spin b else 1)*(if i∈B then spin b else 1))]
  have hlocal : ∀ i : I,
      (∑ b : Bool,(if i∈A then spin b else 1)*(if i∈B then spin b else 1))=
      if (i∈A ↔ i∈B) then (2 : ℝ) else 0 := by
    intro i
    by_cases ha : i∈A <;> by_cases hb : i∈B <;> norm_num [ha,hb,spin]
  simp_rw [hlocal]
  by_cases h : A=B
  · subst B
    simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ : ∃ i : I,¬(i∈A ↔ i∈B) := by
      by_contra! hh
      exact h (Finset.ext hh)
    exact prod_eq_zero (mem_univ i) (if_neg hi)

theorem coefficient_extraction (c : Finset I → ℝ) (B : Finset I) :
    (∑ u : Cube I,character B u*(∑ A : Finset I,c A*character A u))=
      (2 : ℝ)^Fintype.card I*c B := by
  simp_rw [mul_sum]
  rw [sum_comm]
  have hterm : ∀ A : Finset I,
      (∑ u : Cube I,character B u*(c A*character A u))=
      c A*(∑ u : Cube I,character B u*character A u) := by
    intro A
    rw [mul_sum]
    apply sum_congr rfl
    intro u hu
    ring
  simp_rw [hterm,character_orthogonality]
  simp [mul_comm]

theorem character_linearIndependent : LinearIndependent ℝ (character (I := I)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc B
  have hz : ∀ u : Cube I,(∑ A : Finset I,c A*character A u)=0 := by
    intro u
    have h := congrFun hc u
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using h
  have h := coefficient_extraction c B
  simp only [hz,mul_zero,sum_const_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (by norm_num))

theorem character_span : Submodule.span ℝ (Set.range (character (I := I)))=⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card character_linearIndependent,Module.finrank_pi,
    Fintype.card_finset,Fintype.card_fun]
  simp

theorem exists_character_expansion (f : Cube I → ℝ) :
    ∃ c : Finset I → ℝ,∀ u,f u=∑ A : Finset I,c A*character A u := by
  have h : f∈Submodule.span ℝ (Set.range (character (I := I))) := by
    rw [character_span]
    trivial
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp h
  refine ⟨c,fun u => ?_⟩
  have hcu := congrFun hc u
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hcu.symm

/-- A function depends on the indicated coordinates, with no representation
or regularity assumption on the remaining coordinates. -/
def DependsOn (A : Finset I) (f : Cube I → ℝ) : Prop :=
  ∀ u v : Cube I,(∀ i∈A,u i=v i) → f u=f v

theorem dependsOn_const (A : Finset I) (c : ℝ) : DependsOn A (fun _ => c) :=
  fun _ _ _ => rfl

theorem dependsOn_univ (f : Cube I → ℝ) : DependsOn univ f := by
  intro u v h
  congr 1
  exact funext fun i => h i (mem_univ i)

theorem dependsOn_character (A : Finset I) : DependsOn A (character A) := by
  intro u v h
  apply prod_congr rfl
  intro i hi
  by_cases hia : i∈A
  · simp [hia,h i hia]
  · simp [hia]

theorem DependsOn.add {A : Finset I} {f g : Cube I → ℝ}
    (hf : DependsOn A f) (hg : DependsOn A g) : DependsOn A (f+g) := by
  intro u v h
  change f u+g u=f v+g v
  rw [hf u v h,hg u v h]

theorem DependsOn.smul {A : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn A f) (c : ℝ) : DependsOn A (c • f) := by
  intro u v h
  change c*f u=c*f v
  rw [hf u v h]

theorem DependsOn.mono {A B : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn A f) (hAB : A⊆B) : DependsOn B f :=
  fun u v h => hf u v fun i hi => h i (hAB hi)

theorem dependsOn_empty_iff (f : Cube I → ℝ) :
    DependsOn ∅ f ↔ ∃ c : ℝ,∀ u,f u=c := by
  constructor
  · intro h
    exact ⟨f (fun _ => false),fun u => h u (fun _ => false) (by simp)⟩
  · rintro ⟨c,hc⟩ u v huv
    rw [hc u,hc v]

def mix (A : Finset I) (u v : Cube I) : Cube I :=
  fun i => if i∈A then u i else v i

theorem DependsOn.mix_left {A : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn A f) (u v : Cube I) : f (mix A u v)=f u := by
  apply hf
  intro i hi
  simp [mix,hi]

theorem DependsOn.mix_right {A : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn Aᶜ f) (u v : Cube I) : f (mix A u v)=f v := by
  apply hf
  intro i hi
  simp only [mem_compl] at hi
  simp [mix,hi]

end BooleanFourier
end GraphicalZonotopes
