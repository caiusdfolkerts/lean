module

public import Papers.GraphicalZonotopes.ThresholdResponse

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule
open Finset PowersetTransform
variable {H : Type*} [Fintype H] [LinearOrder H]

/-- The second all-essential anchor, `x_a` conjoined with the disjunction of
all other variables. -/
def junctionStar (a : H) : SetFunction H :=
  fun S => if a∈S ∧ 2≤S.card then 1 else 0

theorem junctionStar_boolean (hs : 2≤Fintype.card H) (a : H) :
    IsMonotoneBoolean (junctionStar a) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro S T hST
    by_cases hS : a∈S ∧ 2≤S.card
    · have hT : a∈T ∧ 2≤T.card := ⟨hST hS.1,hS.2.trans (card_le_card hST)⟩
      simp only [junctionStar,if_pos hS,if_pos hT,le_refl]
    · unfold junctionStar
      rw [if_neg hS]
      split_ifs <;> norm_num
  · intro S
    unfold junctionStar
    split_ifs <;> simp
  · simp [junctionStar]
  · simp [junctionStar,hs]

theorem junctionStar_zero_iff (a : H) (S : Finset H) :
    junctionStar a S=0 ↔ a∉S ∨ S.card<2 := by
  by_cases ha : a∈S <;> simp [junctionStar,ha] <;> omega

theorem junctionStar_one_iff (a : H) (S : Finset H) :
    junctionStar a S=1 ↔ a∈S ∧ 2≤S.card := by
  by_cases ha : a∈S <;> simp [junctionStar,ha] <;> omega

theorem junctionStar_essential (hs : 2≤Fintype.card H) (a i : H) :
    Essential (junctionStar a) i := by
  by_cases hi : i=a
  · subst i
    have he : ∃ b : H,b≠a := by
      by_contra hn
      have hsub : (univ : Finset H)⊆{a} := by
        intro b hb
        simp only [mem_singleton]
        by_contra hba
        exact hn ⟨b,hba⟩
      have hc := card_le_card hsub
      simp only [card_univ,card_singleton] at hc
      omega
    obtain ⟨b,hba⟩ := he
    refine ⟨{b},by simpa only [mem_singleton] using hba.symm,?_⟩
    simp [junctionStar,hba,Ne.symm hba]
  · refine ⟨{a},by simpa only [mem_singleton] using hi,?_⟩
    simp [junctionStar,hi,Ne.symm hi]

theorem junctionStar_negativeResponse (hs : 2≤Fintype.card H) (a : H)
    {u v : H} (huv : u≠v) (S : Finset H) (hu : u∉S) (hv : v∉S) :
    negativeResponse (junctionStar a) u v S=
      if a∈S then exactlyOne S else 0 := by
  have hone : negativeResponse (junctionStar a) u v S=1 ↔ a∈S ∧ S.card=1 := by
    rw [negativeResponse_eq_one_iff (junctionStar_boolean hs a),
      junctionStar_zero_iff,junctionStar_one_iff,junctionStar_one_iff]
    simp only [mem_insert,card_insert_of_notMem hu,card_insert_of_notMem hv]
    constructor
    · rintro ⟨hzero,⟨hua,huc⟩,⟨hva,hvc⟩⟩
      have ha : a∈S := by
        by_contra hn
        have hau : a=u := hua.resolve_right hn
        have hav : a=v := hva.resolve_right hn
        exact huv (hau.symm.trans hav)
      have hc : S.card<2 := hzero.resolve_left (not_not.mpr ha)
      exact ⟨ha,by omega⟩
    · rintro ⟨ha,hc⟩
      exact ⟨Or.inr (by omega),⟨Or.inr ha,by omega⟩,⟨Or.inr ha,by omega⟩⟩
  rcases negativeResponse_values (junctionStar_boolean hs a) u v S with hz | ho
  · have hn : ¬(a∈S ∧ S.card=1) := by
      intro h
      have hh := hone.mpr h
      rw [hz] at hh
      norm_num at hh
    by_cases ha : a∈S
    · have hc : S.card≠1 := fun h => hn ⟨ha,h⟩
      simp [hz,ha,exactlyOne,hc]
    · simp [hz,ha]
  · obtain ⟨ha,hc⟩ := hone.mp ho
    simp [ho,ha,exactlyOne,hc]

/-- Both anchor responses are opposite in the actual quotient, in every
clique block simultaneously. -/
theorem junctionStar_response_class (hs : 2≤Fintype.card H) (a : H) :
    responseClass (junctionStar a)= -responseClass (thresholdStar a) := by
  let x : HubResponseRow H → ℝ := fun r => exactlyOneCoefficient r.2.1.card
  have hvec : responseVector (junctionStar a)+responseVector (thresholdStar a)=
      rowLowerEquiv x := by
    funext r
    have hu : r.1.1.1∉r.2.1 := by
      intro h
      exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
    have hv : r.1.1.2∉r.2.1 := by
      intro h
      exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
    change negativeResponse (junctionStar a) r.1.1.1 r.1.1.2 r.2.1+
      negativeResponse (thresholdStar a) r.1.1.1 r.1.1.2 r.2.1=
      lowerSum (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
        (fun T => exactlyOneCoefficient T.1.card) r.2
    rw [junctionStar_negativeResponse hs a (ne_of_lt r.1.2.1) _ hu hv,
      thresholdStar_negativeResponse a (ne_of_lt r.1.2.1) _ hu hv,
      lowerSum_restriction _ (fun T : Finset H => exactlyOneCoefficient T.card) r.2]
    change _=zeta (fun T : Finset H => exactlyOneCoefficient T.card) r.2.1
    rw [zeta_exactlyOneCoefficient]
    by_cases ha : a∈r.2.1 <;> simp [ha]
  have hz : coefficientClass x=0 := by
    apply (coefficientClass_eq_zero_iff x).mpr
    intro r t hrt
    have hc := congrArg (fun C : CliqueIndex (⊤ : SimpleGraph H) => C.1.card) hrt
    have hr := rowClique_card_eq_context_add_two r
    have ht := rowClique_card_eq_context_add_two t
    have he : r.2.1.card=t.2.1.card := by
      change (rowClique r).card=(rowClique t).card at hc
      omega
    change exactlyOneCoefficient r.2.1.card=exactlyOneCoefficient t.2.1.card
    rw [he]
  have hsum : responseClass (junctionStar a)+responseClass (thresholdStar a)=0 := by
    change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ _+
      (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ _=0
    rw [← map_add,hvec]
    exact hz
  exact eq_neg_of_add_eq_zero_left hsum

end GraphicalZonotopes.BooleanModule
