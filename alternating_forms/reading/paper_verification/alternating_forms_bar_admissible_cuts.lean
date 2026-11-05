module

public import PaperVerification.AlternatingFormsBarCompositions

/-!
# Admissible bar blocks and mandatory cuts

For any adjacency relation on letters, a nonempty block is normal exactly
when each adjacent pair inside it is allowed. This file identifies actual
factorizations into such blocks with boundary sets containing the two
endpoints and every forbidden adjacency. No algebraic or homological
condition is assumed in this combinatorial correspondence.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarCompositions

variable {α : Type*} (R : α → α → Prop) (W : List α)

def block (c : Composition W.length) (i : Fin c.length) : List α :=
  (W.take (c.sizeUpTo (i.val+1))).drop (c.sizeUpTo i.val)

theorem block_length (c : Composition W.length) (i : Fin c.length) :
    (block W c i).length=c.sizeUpTo (i.val+1)-c.sizeUpTo i.val := by
  simp only [block,List.length_drop,List.length_take,
    Nat.min_eq_left (c.sizeUpTo_le _)]

theorem block_getElem (c : Composition W.length) (i : Fin c.length)
    (q : ℕ) (hq : q<(block W c i).length) :
    (block W c i)[q]=W[c.sizeUpTo i.val+q]'(by
      rw [block_length] at hq
      have hu := c.sizeUpTo_le (i.val+1)
      omega) := by
  simp only [block,List.getElem_drop,List.getElem_take]

def BadCut (j : Fin (W.length+1)) : Prop :=
  ∃ a : ℕ,∃ ha : a+1<W.length,
    j.val=a+1 ∧ ¬R (W[a]'(by omega)) (W[a+1]'ha)

def mandatoryCuts : Finset (Fin (W.length+1)) := by
  classical
  exact insert 0 (insert (Fin.last W.length) (Finset.univ.filter (BadCut R W)))

@[simp] theorem mem_mandatoryCuts (j : Fin (W.length+1)) :
    j∈mandatoryCuts R W ↔ j=0 ∨ j=Fin.last W.length ∨ BadCut R W j := by
  classical
  simp only [mandatoryCuts,Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and]

theorem block_admissible_iff (c : Composition W.length) :
    (∀ i : Fin c.length,(block W c i).IsChain R) ↔
      mandatoryCuts R W⊆c.boundaries := by
  constructor
  · intro hc j hj
    rcases (mem_mandatoryCuts R W j).mp hj with rfl | rfl | ⟨a,ha,hja,hbad⟩
    · exact c.toCompositionAsSet.zero_mem
    · exact c.toCompositionAsSet.getLast_mem
    · by_contra hjn
      have hj0 : 0<j.val := by omega
      have hjN : j.val<W.length := by omega
      obtain ⟨i,hlo,hup⟩ := (not_mem_boundaries_iff c j hj0 hjN).mp hjn
      let q := a-c.sizeUpTo i.val
      have hlow : c.sizeUpTo i.val≤a := by omega
      have hq : q+1<(block W c i).length := by
        rw [block_length]
        dsimp only [q]
        omega
      have hqa : c.sizeUpTo i.val+q=a := Nat.add_sub_of_le hlow
      have hqb : c.sizeUpTo i.val+(q+1)=a+1 := by omega
      have he := List.isChain_iff_getElem.mp (hc i) q hq
      rw [block_getElem,block_getElem] at he
      apply hbad
      simpa only [hqa,hqb] using he
  · intro hc i
    apply List.isChain_iff_getElem.mpr
    intro q hq
    rw [block_getElem,block_getElem]
    by_contra hbad
    have hq' := hq
    rw [block_length] at hq'
    have hu := c.sizeUpTo_le (i.val+1)
    let a := c.sizeUpTo i.val+q
    have ha : a+1<W.length := by dsimp only [a]; omega
    let j : Fin (W.length+1) := ⟨a+1,by omega⟩
    have hjbad : BadCut R W j := by
      refine ⟨a,ha,rfl,?_⟩
      simpa only [a,Nat.add_assoc] using hbad
    have hj : j∈c.boundaries := hc ((mem_mandatoryCuts R W j).mpr (Or.inr (Or.inr hjbad)))
    have hjn : j∉c.boundaries :=
      (not_mem_boundaries_iff c j (by dsimp only [j]; omega) ha).mpr
        ⟨i,by dsimp only [j,a]; omega,by dsimp only [j,a]; omega⟩
    exact hjn hj

theorem split_admissible_iff_blocks (c : Composition W.length) :
    (∀ T∈W.splitWrtComposition c,T.IsChain R) ↔
      ∀ i : Fin c.length,(block W c i).IsChain R := by
  constructor
  · intro h i
    have hi : i.val<(W.splitWrtComposition c).length := by
      rw [List.length_splitWrtComposition]
      exact i.isLt
    have he := h ((W.splitWrtComposition c)[i.val]) (List.getElem_mem hi)
    simpa only [List.getElem_splitWrtComposition,block] using he
  · intro h T hT
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hT
    have hj' : j<c.length := by rwa [List.length_splitWrtComposition] at hj
    have hh := h (⟨j,hj'⟩ : Fin c.length)
    rw [List.getElem_splitWrtComposition] at he
    simpa only [block,he] using hh

theorem split_admissible_iff (c : Composition W.length) :
    (∀ T∈W.splitWrtComposition c,T.IsChain R) ↔ mandatoryCuts R W⊆c.boundaries :=
  (split_admissible_iff_blocks R W c).trans (block_admissible_iff R W c)

def AdmissibleFactorization :=
  {L : Factorization W // ∀ T∈L.val,T.IsChain R}

def AdmissibleCutSet :=
  {S : Finset (Fin (W.length+1)) // mandatoryCuts R W⊆S}

theorem factorization_admissible_iff (L : Factorization W) :
    (∀ T∈L.val,T.IsChain R) ↔ mandatoryCuts R W⊆boundaries W L := by
  have h := split_admissible_iff R W (factorizationComposition W L)
  have he := congrArg Subtype.val (split_compositionFactorization W L)
  change W.splitWrtComposition (factorizationComposition W L)=L.val at he
  simpa only [he,boundaries] using h

def admissibleCutMap (L : AdmissibleFactorization R W) : AdmissibleCutSet R W :=
  ⟨boundaries W L.val,(factorization_admissible_iff R W L.val).mp L.property⟩

theorem admissibleCutMap_bijective : Function.Bijective (admissibleCutMap R W) := by
  constructor
  · intro L M h
    apply Subtype.ext
    apply boundaries_injective W
    exact congrArg Subtype.val h
  · intro S
    have h0 : (0 : Fin (W.length+1))∈S.val :=
      S.property ((mem_mandatoryCuts R W _).mpr (Or.inl rfl))
    have hN : Fin.last W.length∈S.val :=
      S.property ((mem_mandatoryCuts R W _).mpr (Or.inr (Or.inl rfl)))
    obtain ⟨L,hL,hunique⟩ := exists_unique_factorization W S.val h0 hN
    have hLa : ∀ T∈L.val,T.IsChain R :=
      (factorization_admissible_iff R W L).mpr (hL.symm ▸ S.property)
    refine ⟨⟨L,hLa⟩,?_⟩
    exact Subtype.ext hL

/-- The basis index correspondence for the literal monomial bar complex. -/
def admissibleCutEquiv : AdmissibleFactorization R W ≃ AdmissibleCutSet R W :=
  Equiv.ofBijective (admissibleCutMap R W) (admissibleCutMap_bijective R W)

theorem admissibleCutEquiv_card (L : AdmissibleFactorization R W) :
    (admissibleCutEquiv R W L).val.card=L.val.val.length+1 :=
  boundaries_card W L.val

end PaperVerification.AlternatingForms.BarCompositions

