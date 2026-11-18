module

public import Papers.GraphicalZonotopes.PureResponseClasses

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {H : Type*} [Fintype H] [LinearOrder H]

def partialStarBlocks (a : H) (B : Finset H) : Finset (Finset H) := {{a},B}

theorem partialStarBlocks_family (C : Finset H) {a : H} {B : Finset H}
    (ha : a∈C) (hB : B⊆C) (hne : B.Nonempty) (haB : a∉B) :
    ComplementFamily C (partialStarBlocks a B) := by
  have hnot : ({a} : Finset H)≠B := by
    intro he
    exact haB (he ▸ mem_singleton_self a)
  refine ⟨?_,?_,?_,?_⟩
  · simp only [partialStarBlocks,card_pair hnot,le_refl]
  · intro D hD
    simp only [partialStarBlocks,mem_insert,mem_singleton] at hD
    rcases hD with rfl | rfl
    · exact singleton_subset_iff.mpr ha
    · exact hB
  · intro D hD
    simp only [partialStarBlocks,mem_insert,mem_singleton] at hD
    rcases hD with rfl | rfl
    · exact singleton_nonempty a
    · exact hne
  · intro D hD E hE hDE
    simp only [partialStarBlocks,mem_insert,mem_singleton] at hD hE
    rcases hD with rfl | rfl <;> rcases hE with rfl | rfl
    · exact False.elim (hDE rfl)
    · exact disjoint_singleton_left.mpr haB
    · exact disjoint_singleton_right.mpr haB
    · exact False.elim (hDE rfl)

def StarPair (a : H) (B : Finset H) (u v : H) : Prop :=
  (u=a ∧ v∈B) ∨ (v=a ∧ u∈B)

instance (a : H) (B : Finset H) (u v : H) : Decidable (StarPair a B u v) :=
  inferInstanceAs (Decidable ((u=a ∧ v∈B) ∨ (v=a ∧ u∈B)))

theorem crosses_partialStarBlocks {a : H} {B : Finset H} (haB : a∉B)
    (u v : H) : Crosses (partialStarBlocks a B) u v ↔ StarPair a B u v := by
  have hnot : ({a} : Finset H)≠B := by
    intro he
    exact haB (he ▸ mem_singleton_self a)
  constructor
  · rintro ⟨D,hD,E,hE,hDE,hu,hv⟩
    simp only [partialStarBlocks,mem_insert,mem_singleton] at hD hE
    rcases hD with rfl | rfl <;> rcases hE with rfl | rfl
    · exact False.elim (hDE rfl)
    · exact Or.inl ⟨mem_singleton.mp hu,hv⟩
    · exact Or.inr ⟨mem_singleton.mp hv,hu⟩
    · exact False.elim (hDE rfl)
  · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
    · exact ⟨{a},by simp [partialStarBlocks],B,by simp [partialStarBlocks],
        hnot,mem_singleton.mpr hu,hv⟩
    · exact ⟨B,by simp [partialStarBlocks],{a},by simp [partialStarBlocks],
        hnot.symm,hu,mem_singleton.mpr hv⟩

/-- The two-minterm function used for every partial-star column in Lemma7.7. -/
def partialStarModule (C : Finset H) (a : H) (B : Finset H) : SetFunction H :=
  complementModule C (partialStarBlocks a B)

theorem partialStarModule_properties (C : Finset H) {a : H} {B : Finset H}
    (ha : a∈C) (hB : B⊆C) (hne : B.Nonempty) (haB : a∉B) :
    IsMonotoneBoolean (partialStarModule C a B) ∧
    (∀ i∈C,Essential (partialStarModule C a B) i) ∧
    (∀ i,i∉C → ∀ X,partialStarModule C a B (insert i X)=partialStarModule C a B X) ∧
    rowLowerEquiv.symm (responseVector (partialStarModule C a B))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ StarPair a B r.1.1.1 r.1.1.2 then 1 else 0 := by
  have hf:=partialStarBlocks_family C ha hB hne haB
  refine ⟨hf.module_boolean,fun i hi => hf.essential hi,?_,?_⟩
  · exact fun i hi X => complementModule_ignores_outside C _ hi X
  · rw [partialStarModule,complementModule_response_coefficients hf]
    funext r
    simp only [crosses_partialStarBlocks haB]

def cliqueBlocks (U : Finset H) : Finset (Finset H) := U.image singleton

theorem cliqueBlocks_family (C U : Finset H) (hU : U⊆C) (hcard : 2≤U.card) :
    ComplementFamily C (cliqueBlocks U) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [cliqueBlocks,card_image_of_injective _ singleton_injective] using hcard
  · intro B hB
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hB
    exact singleton_subset_iff.mpr (hU hi)
  · intro B hB
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hB
    exact singleton_nonempty i
  · intro A hA B hB hAB
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hA
    obtain ⟨j,hj,rfl⟩:=mem_image.mp hB
    apply disjoint_singleton_left.mpr
    intro h
    have he : i=j:=mem_singleton.mp h
    exact hAB (congrArg singleton he)

theorem crosses_cliqueBlocks (U : Finset H) (u v : H) :
    Crosses (cliqueBlocks U) u v ↔ u∈U ∧ v∈U ∧ u≠v := by
  constructor
  · rintro ⟨A,hA,B,hB,hAB,hu,hv⟩
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hA
    obtain ⟨j,hj,rfl⟩:=mem_image.mp hB
    have hui : u=i:=mem_singleton.mp hu
    have hvj : v=j:=mem_singleton.mp hv
    refine ⟨hui.symm ▸ hi,hvj.symm ▸ hj,?_⟩
    intro huv
    exact hAB (congrArg singleton (hui.symm.trans (huv.trans hvj)))
  · rintro ⟨hu,hv,huv⟩
    exact ⟨{u},mem_image.mpr ⟨u,hu,rfl⟩,
      {v},mem_image.mpr ⟨v,hv,rfl⟩,
      fun he => huv (singleton_injective he),mem_singleton_self _,mem_singleton_self _⟩

/-- The disjunction of the complements of the singleton vertices of `U`. -/
def cliqueModule (C U : Finset H) : SetFunction H :=
  complementModule C (cliqueBlocks U)

theorem cliqueModule_properties (C U : Finset H) (hU : U⊆C) (hcard : 2≤U.card) :
    IsMonotoneBoolean (cliqueModule C U) ∧
    (∀ i∈C,Essential (cliqueModule C U) i) ∧
    (∀ i,i∉C → ∀ X,cliqueModule C U (insert i X)=cliqueModule C U X) ∧
    rowLowerEquiv.symm (responseVector (cliqueModule C U))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ r.1.1.1∈U ∧ r.1.1.2∈U then 1 else 0 := by
  have hf:=cliqueBlocks_family C U hU hcard
  refine ⟨hf.module_boolean,fun i hi => hf.essential hi,?_,?_⟩
  · exact fun i hi X => complementModule_ignores_outside C _ hi X
  · rw [cliqueModule,complementModule_response_coefficients hf]
    funext r
    rw [crosses_cliqueBlocks]
    simp [ne_of_lt r.1.2.1]

end BooleanModule
end GraphicalZonotopes
