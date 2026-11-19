module

public import Papers.GraphicalZonotopes.BooleanFace
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The local factors of the actual three-dimensional space in transformed
coordinates. -/
def tensorFactor (b : Option Bool) (u v : Bool) : ℝ :=
  match b with
  | none => 1
  | some false => spin u
  | some true => spin u*spin v

/-- Products of arbitrary local linear combinations lie in the actual tensor
space. The proof is the finite distributive law over all choices of factors. -/
theorem tensor_product_mem (w : I → Option Bool → ℝ) :
    (fun uv : Cube I × Cube I =>
      ∏ i,∑ b : Option Bool,w i b*tensorFactor b (uv.1 i) (uv.2 i))∈tensorSpace := by
  have h : (∑ a : I → Option Bool,(∏ i,w i (a i)) • tensorMonomial a)∈tensorSpace :=
    (tensorSpace (I := I)).sum_mem fun a _ =>
      (tensorSpace (I := I)).smul_mem _ (Submodule.subset_span ⟨a,rfl⟩)
  convert h using 1
  funext uv
  rw [Fintype.prod_sum]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,tensorMonomial]
  apply sum_congr rfl
  intro a ha
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  cases a i <;> rfl

/-- A selected original membership bit in each part, with no bit selected for
`none`. A clique of a graph with doubled parts has exactly this form. -/
def indicatorMonomial (a : I → Option Bool) (s : Cube I × Cube I) : ℝ :=
  ∏ i,match a i with
    | none => 1
    | some false => if s.1 i then 1 else 0
    | some true => if s.2 i then 1 else 0

def indicatorCoefficients (a : Option Bool) (b : Option Bool) : ℝ :=
  match a with
  | none => if b=none then 1 else 0
  | some q => if b=none then 1/2 else if b=some q then -1/2 else 0

theorem indicator_local_expansion (a : Option Bool) (u v : Bool) :
    (∑ b : Option Bool,indicatorCoefficients a b*tensorFactor b u v)=
      match a with
      | none => 1
      | some false => if u then 1 else 0
      | some true => if Bool.xor u v then 1 else 0 := by
  cases a with
  | none => simp [indicatorCoefficients,tensorFactor]
  | some q =>
    cases q <;> cases u <;> cases v <;>
      norm_num [indicatorCoefficients,tensorFactor,spin,Fintype.sum_option,Fintype.sum_bool]

/-- Actual membership monomials become tensor-space elements under the
invertible coordinate substitution `(u,v) ↦ (u,u xor v)`. -/
theorem indicatorMonomial_mem_tensorSpace (a : I → Option Bool) :
    (fun uv => indicatorMonomial a (coordinateChange.symm uv))∈tensorSpace := by
  have h := tensor_product_mem (fun i => indicatorCoefficients (a i))
  convert h using 1
  funext uv
  simp only [indicatorMonomial]
  apply prod_congr rfl
  intro i hi
  rw [indicator_local_expansion]
  cases a i with
  | none => rfl
  | some q => cases q <;> rfl

theorem indicatorMonomial_eq (a : I → Option Bool) (s : Cube I × Cube I) :
    indicatorMonomial a s=
      if (∀ i, a i=some false → s.1 i=true) ∧
        (∀ i,a i=some true → s.2 i=true) then 1 else 0 := by
  classical
  by_cases hall : (∀ i,a i=some false → s.1 i=true) ∧
      (∀ i,a i=some true → s.2 i=true)
  · rw [if_pos hall]
    apply prod_eq_one
    intro i hi
    cases h : a i with
    | none => rfl
    | some q =>
      cases q
      · simp [h,hall.1 i h]
      · simp [h,hall.2 i h]
  · rw [if_neg hall]
    have hn : (∃ i,a i=some false ∧ s.1 i≠true) ∨
        (∃ i,a i=some true ∧ s.2 i≠true) := by
      simpa only [not_and_or,not_forall,not_imp,exists_prop] using hall
    rcases hn with ⟨i,ha,hs⟩ | ⟨i,ha,hs⟩
    · apply Finset.prod_eq_zero (mem_univ i)
      simp [ha,hs]
    · apply Finset.prod_eq_zero (mem_univ i)
      simp [ha,hs]

end BooleanFourier
end GraphicalZonotopes
