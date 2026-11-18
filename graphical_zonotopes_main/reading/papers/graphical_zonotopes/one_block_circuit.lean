module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace OneBlockCircuit
open Finset
open scoped BigOperators
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The columns used in the small-count construction: the indicator of a
proper set of pairs, followed by the complements of its individual pairs. -/
def column (A : Finset E) : Option ↥A → E → ℝ
  | none,e => if e∈A then 1 else 0
  | some a,e => if e=a.1 then 0 else 1

def response (A : Finset E) (t : Option ↥A → ℝ) (e : E) : ℝ :=
  ∑ j : Option ↥A,t j*column A j e

def tailSum (A : Finset E) (t : Option ↥A → ℝ) : ℝ :=
  ∑ a : ↥A,t (some a)

theorem response_outside (A : Finset E) (t : Option ↥A → ℝ)
    {e : E} (he : e∉A) : response A t e=tailSum A t := by
  rw [response,Fintype.sum_option]
  simp only [column,if_neg he,mul_zero,zero_add]
  apply sum_congr rfl
  intro a ha
  have hea : e≠a.1:=fun h => he (h.symm ▸ a.2)
  simp only [if_neg hea,mul_one]

theorem response_at (A : Finset E) (t : Option ↥A → ℝ) (a : ↥A) :
    response A t a.1=t none+tailSum A t-t (some a) := by
  rw [response,Fintype.sum_option]
  simp only [column,if_pos a.2,mul_one]
  have hs : (∑ b : ↥A,t (some b)*(if a.1=b.1 then 0 else 1))=
      tailSum A t-t (some a) := by
    calc
      _=∑ b : ↥A,(t (some b)-(if a=b then t (some b) else 0)) := by
        apply sum_congr rfl
        intro b hb
        by_cases hab : a=b
        · subst b
          simp
        · have hv : a.1≠b.1:=fun h => hab (Subtype.ext h)
          simp only [if_neg hv,if_neg hab,mul_one,sub_zero]
      _=tailSum A t-t (some a) := by
        rw [sum_sub_distrib]
        simp only [sum_ite_eq,mem_univ,ite_true,tailSum]
  rw [hs]
  ring

/-- A missing pair fixes the common block value. Comparing every selected
pair with it then forces every column scale to equal the first one. -/
theorem constant_response_iff (A : Finset E) (hA : ∃ e,e∉A)
    (t : Option ↥A → ℝ) :
    (∃ c : ℝ,∀ e,response A t e=c) ↔ ∃ a : ℝ,∀ j,t j=a := by
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨e₀,he₀⟩:=hA
    have hc₀ : c=tailSum A t:=(hc e₀).symm.trans (response_outside A t he₀)
    refine ⟨t none,?_⟩
    intro j
    cases j with
    | none => rfl
    | some a =>
      have ha:=hc a.1
      rw [response_at,hc₀] at ha
      linarith
  · rintro ⟨a,ha⟩
    refine ⟨tailSum A t,?_⟩
    intro e
    by_cases he : e∈A
    · have h:=response_at A t ⟨e,he⟩
      rw [ha none,ha (some ⟨e,he⟩)] at h
      linarith
    · exact response_outside A t he

theorem unit_response (A : Finset E) (e : E) :
    response A (fun _ => 1) e=(A.card : ℝ) := by
  have hs : tailSum A (fun _ => 1)=(A.card : ℝ) := by
    simp [tailSum]
  by_cases he : e∈A
  · rw [response_at A (fun _ => 1) ⟨e,he⟩,hs]
    ring
  · rw [response_outside A (fun _ => 1) he,hs]

def relationSpace (A : Finset E) : Submodule ℝ (Option ↥A → ℝ) where
  carrier:={t | ∃ c : ℝ,∀ e,response A t e=c}
  zero_mem':=by refine ⟨0,?_⟩; intro e; simp [response]
  add_mem':=by
    rintro t u ⟨c,hc⟩ ⟨d,hd⟩
    refine ⟨c+d,?_⟩
    intro e
    simp only [response,Pi.add_apply,add_mul,sum_add_distrib]
    exact congrArg₂ (·+·) (hc e) (hd e)
  smul_mem':=by
    rintro a t ⟨c,hc⟩
    refine ⟨a*c,?_⟩
    intro e
    simp only [response,Pi.smul_apply,smul_eq_mul,mul_assoc,← mul_sum]
    exact congrArg (a*·) (hc e)

theorem relationSpace_eq_span (A : Finset E) (hA : ∃ e,e∉A) :
    relationSpace A=Submodule.span ℝ {(fun _ : Option ↥A => (1 : ℝ))} := by
  ext t
  change (∃ c : ℝ,∀ e,response A t e=c) ↔ _
  rw [constant_response_iff A hA,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    funext j
    simp only [Pi.smul_apply,smul_eq_mul,mul_one]
    exact (hc j).symm
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    intro j
    have h:=congrFun hc j
    simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using h.symm

end OneBlockCircuit
end BooleanModule
end GraphicalZonotopes
