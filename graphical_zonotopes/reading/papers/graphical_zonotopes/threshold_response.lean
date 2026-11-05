module

public import Papers.GraphicalZonotopes.ThresholdBoolean
public import Papers.GraphicalZonotopes.PureResponseClasses

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
variable {H : Type*} [Fintype H] [LinearOrder H]

def thresholdCoefficients (a : H) : HubResponseRow H → ℝ :=
  fun r => absentCoefficient a (fun T => exactlyOneCoefficient T.card) r.2.1

/-- The actual inverse of the pairwise response zeta transform, with every
context retained. This is computed from the Boolean function, not stipulated
as a response vector. -/
theorem thresholdStar_coefficients (a : H) :
    rowLowerEquiv.symm (responseVector (thresholdStar a))=thresholdCoefficients a := by
  apply rowLowerEquiv.injective
  rw [rowLowerEquiv.apply_symm_apply]
  funext r
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  change negativeResponse (thresholdStar a) r.1.1.1 r.1.1.2 r.2.1=
    lowerSum (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
      (fun T => absentCoefficient a (fun U => exactlyOneCoefficient U.card) T.1) r.2
  rw [lowerSum_restriction]
  change negativeResponse (thresholdStar a) r.1.1.1 r.1.1.2 r.2.1=
    zeta (absentCoefficient a (fun U => exactlyOneCoefficient U.card)) r.2.1
  rw [zeta_absent_exactlyOne,
    thresholdStar_negativeResponse a (ne_of_lt r.1.2.1) r.2.1 hu hv]

def thresholdSign (n : ℕ) : ℝ :=
  if n=0 then 0 else (-1 : ℝ)^(n-1)

theorem exactlyOneCoefficient_sub_sign (n : ℕ) (hn : 0<n) :
    exactlyOneCoefficient n-thresholdSign n= -exactlyOneCoefficient (n-1) := by
  have hs:=exactlyOneCoefficient_step (n-1)
  have he : n-1+1=n:=by omega
  rw [he] at hs
  rw [thresholdSign,if_neg (Nat.ne_of_gt hn)]
  linarith

theorem rowClique_card_eq_context_add_two (r : HubResponseRow H) :
    (rowClique r).card=r.2.1.card+2 := by
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hu' : r.1.1.1∉insert r.1.1.2 r.2.1 := by
    simpa only [mem_insert,not_or] using And.intro (ne_of_lt r.1.2.1) hu
  simp only [rowClique,card_insert_of_notMem hu',card_insert_of_notMem hv]

def thresholdCommon (a : H) (C : Finset H) : ℝ :=
  exactlyOneCoefficient (C.card-2)-if a∈C then thresholdSign (C.card-2) else 0

/-- The literal signed-star representative appearing in equation (7.2),
including its zero value on blocks not containing the distinguished hub. -/
def thresholdSignedStar (a : H) : HubResponseRow H → ℝ :=
  fun r => if 3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2)
    then (-1 : ℝ)^((rowClique r).card-3) else 0

theorem thresholdSignedStar_eq (a : H) (r : HubResponseRow H) :
    thresholdSignedStar a r=
      if a=r.1.1.1 ∨ a=r.1.1.2 then thresholdSign r.2.1.card else 0 := by
  have hc:=rowClique_card_eq_context_add_two r
  by_cases ha : a=r.1.1.1 ∨ a=r.1.1.2
  · by_cases hn : r.2.1.card=0
    · have hC : ¬3≤(rowClique r).card:=by omega
      simp [thresholdSignedStar,ha,hC,thresholdSign,hn]
    · have hC : 3≤(rowClique r).card:=by omega
      have he : (rowClique r).card-3=r.2.1.card-1:=by omega
      simp [thresholdSignedStar,ha,hC,thresholdSign,hn,he]
  · simp only [thresholdSignedStar,ha,and_false,ite_false]

/-- Before passing to the quotient, the response differs from the signed
star by exactly one common coefficient on each full clique block. -/
theorem thresholdCoefficients_decomposition (a : H) :
    thresholdCoefficients a=
      (fun r : HubResponseRow H => thresholdCommon a (rowClique r))+
        thresholdSignedStar a := by
  funext r
  have hc:=rowClique_card_eq_context_add_two r
  have hsub : (rowClique r).card-2=r.2.1.card:=by omega
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  simp only [Pi.add_apply,thresholdCoefficients,thresholdCommon,hsub,
    thresholdSignedStar_eq,absentCoefficient]
  by_cases hp : a=r.1.1.1 ∨ a=r.1.1.2
  · have ha : a∈rowClique r := by
      rcases hp with ha | ha
      · simp only [rowClique,ha,mem_insert_self]
      · simp [rowClique,ha]
    have haS : a∉r.2.1 := by
      rcases hp with ha | ha
      · simpa only [ha] using hu
      · simpa only [ha] using hv
    rw [if_neg haS,if_pos ha,if_pos hp]
    ring
  · by_cases haS : a∈r.2.1
    · have ha : a∈rowClique r:=mem_insert_of_mem (mem_insert_of_mem haS)
      have hn : 0<r.2.1.card:=card_pos.mpr ⟨a,haS⟩
      rw [if_pos haS,if_pos ha,if_neg hp,add_zero,card_erase_of_mem haS,
        exactlyOneCoefficient_sub_sign _ hn]
    · have ha : a∉rowClique r := by
        simp only [rowClique,mem_insert]
        intro h
        rcases h with h | h | h
        · exact hp (Or.inl h)
        · exact hp (Or.inr h)
        · exact haS h
      rw [if_neg haS,if_neg ha,if_neg hp,sub_zero,add_zero]

/-- Lemma 7.6 in the actual quotient by all central elemental responses.
There are no omitted contexts or unproved block-identification assumptions. -/
theorem thresholdStar_response_class (a : H) :
    responseClass (thresholdStar a)=coefficientClass (thresholdSignedStar a) := by
  rw [responseClass_eq_coefficientClass,thresholdStar_coefficients,
    thresholdCoefficients_decomposition,map_add]
  have hz : coefficientClass
      (fun r : HubResponseRow H => thresholdCommon a (rowClique r))=0 := by
    apply (coefficientClass_eq_zero_iff _).mpr
    intro r t hrt
    exact congrArg (thresholdCommon a) (congrArg Subtype.val hrt)
  rw [hz,zero_add]

theorem thresholdStar_response_lemma (hs : 3≤Fintype.card H) (a : H) :
    IsMonotoneBoolean (thresholdStar a) ∧
    (∀ i,Essential (thresholdStar a) i) ∧
    responseClass (thresholdStar a)=coefficientClass (thresholdSignedStar a) :=
  ⟨thresholdStar_boolean a,thresholdStar_essential hs a,thresholdStar_response_class a⟩

end BooleanModule
end GraphicalZonotopes
