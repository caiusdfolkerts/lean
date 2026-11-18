module

public import Papers.GraphicalZonotopes.PureBooleanResponses

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {H : Type*} [Fintype H] [LinearOrder H]

def negativePairBlocks (C : Finset H) (u v : H) : Finset (Finset H):=
  insert {u,v} ((C\{u,v}).image singleton)

theorem mem_negativePairBlocks (C : Finset H) (u v : H) (B : Finset H) :
    B∈negativePairBlocks C u v ↔
      B={u,v} ∨ ∃ a,a∈C ∧ a≠u ∧ a≠v ∧ B={a} := by
  constructor
  · intro hB
    rcases mem_insert.mp hB with he | he
    · exact Or.inl he
    · obtain ⟨a,ha,he⟩:=mem_image.mp he
      have ha':=mem_sdiff.mp ha
      have hn : a≠u ∧ a≠v:=by simpa only [mem_insert,mem_singleton,not_or] using ha'.2
      exact Or.inr ⟨a,ha'.1,hn.1,hn.2,he.symm⟩
  · rintro (he | ⟨a,ha,hau,hav,he⟩)
    · exact mem_insert.mpr (Or.inl he)
    · apply mem_insert_of_mem
      exact mem_image.mpr ⟨a,mem_sdiff.mpr ⟨ha,by simp [hau,hav]⟩,he.symm⟩

theorem negativePairBlocks_family (C : Finset H) (hC : 3≤C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠v) :
    ComplementFamily C (negativePairBlocks C u v) := by
  have hpair : ({u,v} : Finset H)⊆C:=by simp [insert_subset_iff,singleton_subset_iff,hu,hv]
  have hdiff : (C\{u,v}).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff_of_subset hpair,card_pair huv]
    omega
  obtain ⟨a,ha⟩:=hdiff
  have ha':=mem_sdiff.mp ha
  have hauv : a≠u ∧ a≠v:=by simpa only [mem_insert,mem_singleton,not_or] using ha'.2
  have hpairmem : ({u,v} : Finset H)∈negativePairBlocks C u v:=by
    exact (mem_negativePairBlocks _ _ _ _).mpr (Or.inl rfl)
  have hasingle : ({a} : Finset H)∈negativePairBlocks C u v:=
    (mem_negativePairBlocks _ _ _ _).mpr (Or.inr ⟨a,ha'.1,hauv.1,hauv.2,rfl⟩)
  have hne : ({u,v} : Finset H)≠{a} := by
    intro he
    have hc:=congrArg Finset.card he
    rw [card_pair huv,card_singleton] at hc
    omega
  refine ⟨?_,?_,?_,?_⟩
  · have hh : 1<(negativePairBlocks C u v).card:=
      one_lt_card.mpr ⟨{u,v},hpairmem,{a},hasingle,hne⟩
    omega
  · intro B hB
    rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
    · exact hpair
    · exact singleton_subset_iff.mpr hb
  · intro B hB
    rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
    · exact ⟨u,by simp⟩
    · exact singleton_nonempty b
  · intro A hA B hB hAB
    rcases (mem_negativePairBlocks _ _ _ _).mp hA with rfl | ⟨a,ha,hau,hav,rfl⟩
    · rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
      · exact False.elim (hAB rfl)
      · simp [hbu,hbv,Ne.symm hbu,Ne.symm hbv]
    · rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
      · simp [hau,hav,Ne.symm hau,Ne.symm hav]
      · have hab : a≠b:=fun he => hAB (congrArg singleton he)
        simp [hab]

theorem crosses_negativePairBlocks (C : Finset H) (hC : 3≤C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠v) (a b : H) :
    Crosses (negativePairBlocks C u v) a b ↔
      a∈C ∧ b∈C ∧ a≠b ∧ ¬(a∈({u,v} : Finset H) ∧ b∈({u,v} : Finset H)) := by
  let hfamily:=negativePairBlocks_family C hC hu hv huv
  have hpairmem : ({u,v} : Finset H)∈negativePairBlocks C u v:=
    (mem_negativePairBlocks _ _ _ _).mpr (Or.inl rfl)
  have hsingle : ∀ x,x∈C → x∉({u,v} : Finset H) →
      ({x} : Finset H)∈negativePairBlocks C u v := by
    intro x hx hxn
    have hn : x≠u ∧ x≠v:=by simpa only [mem_insert,mem_singleton,not_or] using hxn
    exact (mem_negativePairBlocks _ _ _ _).mpr (Or.inr ⟨x,hx,hn.1,hn.2,rfl⟩)
  constructor
  · rintro ⟨A,hA,B,hB,hAB,ha,hb⟩
    refine ⟨hfamily.subsets A hA ha,hfamily.subsets B hB hb,?_,?_⟩
    · intro he
      exact hAB (hfamily.shared_mem_eq hA hB ha (he.symm ▸ hb))
    · rintro ⟨hap,hbp⟩
      exact hAB ((hfamily.shared_mem_eq hA hpairmem ha hap).trans
        (hfamily.shared_mem_eq hpairmem hB hbp hb))
  · rintro ⟨ha,hb,hab,hnot⟩
    by_cases hap : a∈({u,v} : Finset H)
    · have hbp : b∉({u,v} : Finset H):=fun hh => hnot ⟨hap,hh⟩
      refine ⟨{u,v},hpairmem,{b},hsingle b hb hbp,?_,hap,mem_singleton_self b⟩
      intro he
      exact hbp (he.symm ▸ mem_singleton_self b)
    · by_cases hbp : b∈({u,v} : Finset H)
      · refine ⟨{a},hsingle a ha hap,{u,v},hpairmem,?_,mem_singleton_self a,hbp⟩
        intro he
        exact hap (he ▸ mem_singleton_self a)
      · exact ⟨{a},hsingle a ha hap,{b},hsingle b hb hbp,
          fun he => hab (singleton_injective he),mem_singleton_self a,mem_singleton_self b⟩

def negativePairModule (C : Finset H) (u v : H) : SetFunction H:=
  complementModule C (negativePairBlocks C u v)

theorem ordered_pair_membership {a b u v : H} (hab : a<b) (huv : u<v) :
    (a∈({u,v} : Finset H) ∧ b∈({u,v} : Finset H)) ↔ a=u ∧ b=v := by
  simp only [mem_insert,mem_singleton]
  constructor
  · rintro ⟨ha,hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim ((lt_irrefl _) hab)
    · exact ⟨rfl,rfl⟩
    · exact False.elim ((not_lt_of_ge huv.le) hab)
    · exact False.elim ((lt_irrefl _) hab)
  · rintro ⟨rfl,rfl⟩
    exact ⟨Or.inl rfl,Or.inr rfl⟩

/-- The negative pure module has every coordinate in its clique block except
the specified pair. Modulo the diagonal this is the negative pair class. -/
theorem negativePairModule_coefficients (C : Finset H) (hC : 3≤C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u<v) :
    rowLowerEquiv.symm (responseVector (negativePairModule C u v))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ ¬(r.1.1.1=u ∧ r.1.1.2=v) then 1 else 0 := by
  rw [negativePairModule,complementModule_response_coefficients
    (negativePairBlocks_family C hC hu hv (ne_of_lt huv))]
  funext r
  rw [crosses_negativePairBlocks C hC hu hv (ne_of_lt huv),
    ordered_pair_membership r.1.2.1 huv]
  by_cases hrow : rowClique r=C
  · have ha : r.1.1.1∈C:=by rw [← hrow]; simp [rowClique]
    have hb : r.1.1.2∈C:=by rw [← hrow]; simp [rowClique]
    have hne : r.1.1.1≠r.1.1.2 := ne_of_lt r.1.2.1
    simp [hrow,ha,hb,hne]
  · simp only [hrow,false_and,ite_false]

theorem negativePairModule_essential (C : Finset H) (hC : 3≤C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠v) {a : H} (ha : a∈C) :
    Essential (negativePairModule C u v) a :=
  (negativePairBlocks_family C hC hu hv huv).essential ha

end BooleanModule
end GraphicalZonotopes
