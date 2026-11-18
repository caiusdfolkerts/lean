module

public import Papers.GraphicalZonotopes.NegativePureBooleanResponses

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
variable {H : Type*} [Fintype H] [LinearOrder H]

abbrev ResponseQuotient (H : Type*) [Fintype H] [LinearOrder H] :=
  (HubResponseRow H → ℝ) ⧸ LinearMap.range (centralCoefficientSlack (H:=H))

def responseClass (F : SetFunction H) : ResponseQuotient H :=
  (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ (responseVector F)

def coefficientClass : (HubResponseRow H → ℝ) →ₗ[ℝ] ResponseQuotient H :=
  (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ ∘ₗ rowLowerEquiv.toLinearMap

def pureCoordinate (C : Finset H) (u v : H) : ResponseQuotient H :=
  coefficientClass (fun r : HubResponseRow H =>
    if rowClique r=C ∧ r.1.1.1=u ∧ r.1.1.2=v then 1 else 0)

theorem responseClass_eq_coefficientClass (F : SetFunction H) :
    responseClass F=coefficientClass (rowLowerEquiv.symm (responseVector F)) := by
  simp only [coefficientClass,LinearMap.comp_apply,LinearEquiv.coe_coe,
    rowLowerEquiv.apply_symm_apply,responseClass]

theorem coefficientClass_eq_zero_iff (x : HubResponseRow H → ℝ) :
    coefficientClass x=0 ↔ BlockConstant x := by
  change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ (rowLowerEquiv x)=0 ↔ _
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ,central_range_iff_blockConstant,
    rowLowerEquiv.symm_apply_apply]

/-- The common coordinate in a block is exactly a central coefficient and
vanishes in the response quotient, including all pair and higher blocks. -/
theorem coefficientClass_block_zero (C : Finset H) :
    coefficientClass (fun r : HubResponseRow H => if rowClique r=C then 1 else 0)=0 := by
  apply (coefficientClass_eq_zero_iff _).mpr
  intro r t he
  have hv : rowClique r=rowClique t:=congrArg Subtype.val he
  change (if rowClique r=C then (1 : ℝ) else 0)=(if rowClique t=C then 1 else 0)
  rw [hv]

theorem positivePairModule_class (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u<v) :
    responseClass (positivePairModule C u v)=pureCoordinate C u v := by
  rw [responseClass_eq_coefficientClass,positivePairModule_coefficients C hu hv huv]
  rfl

theorem negativePairModule_class (C : Finset H) (hC : 3≤C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u<v) :
    responseClass (negativePairModule C u v)= -pureCoordinate C u v := by
  rw [responseClass_eq_coefficientClass,negativePairModule_coefficients C hC hu hv huv]
  have he : (fun r : HubResponseRow H =>
      if rowClique r=C ∧ ¬(r.1.1.1=u ∧ r.1.1.2=v) then (1 : ℝ) else 0)=
      (fun r : HubResponseRow H => if rowClique r=C then 1 else 0)-
        (fun r : HubResponseRow H =>
          if rowClique r=C ∧ r.1.1.1=u ∧ r.1.1.2=v then 1 else 0) := by
    funext r
    by_cases hr : rowClique r=C <;>
      by_cases hp : r.1.1.1=u ∧ r.1.1.2=v <;> simp [hr,hp,and_assoc]
  rw [he,map_sub,coefficientClass_block_zero,zero_sub]
  rfl

/-- Lemma7.4 with its actual quotient classes, all variables of `C`
essential, and every other ambient variable explicitly ignored. -/
theorem both_signs_of_pure_coordinate (C : Finset H) (hC : 3≤C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u<v) :
    ∃ P R : SetFunction H,
      IsMonotoneBoolean P ∧ IsMonotoneBoolean R ∧
      (∀ a∈C,Essential P a ∧ Essential R a) ∧
      (∀ a,a∉C → ∀ X,P (insert a X)=P X ∧ R (insert a X)=R X) ∧
      responseClass P=pureCoordinate C u v ∧ responseClass R= -pureCoordinate C u v := by
  refine ⟨positivePairModule C u v,negativePairModule C u v,
    (positivePairBlocks_family C hu hv (ne_of_lt huv)).module_boolean,
    (negativePairBlocks_family C hC hu hv (ne_of_lt huv)).module_boolean,?_,?_,
    positivePairModule_class C hu hv huv,negativePairModule_class C hC hu hv huv⟩
  · intro a ha
    exact ⟨positivePairModule_essential C hu hv (ne_of_lt huv) ha,
      negativePairModule_essential C hC hu hv (ne_of_lt huv) ha⟩
  · intro a ha X
    exact ⟨complementModule_ignores_outside C _ ha X,
      complementModule_ignores_outside C _ ha X⟩

end BooleanModule
end GraphicalZonotopes
