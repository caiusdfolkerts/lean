module

public import Papers.GraphicalZonotopes.BookModuleGeometry

@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The nonempty, disjoint complements of the minimal winning sets. Their
union may be smaller than `C`; the remaining variables occur in every term. -/
structure ComplementFamily (C : Finset H) (blocks : Finset (Finset H)) : Prop where
  card_two : 2≤blocks.card
  subsets : ∀ B∈blocks,B⊆C
  nonempty : ∀ B∈blocks,B.Nonempty
  disjoint : ∀ A∈blocks,∀ B∈blocks,A≠B → Disjoint A B

def complementModule (C : Finset H) (blocks : Finset (Finset H)) : SetFunction H :=
  fun S => if ∃ B∈blocks,C\B⊆S then 1 else 0

theorem complementModule_one_iff (C : Finset H) (blocks : Finset (Finset H)) (S : Finset H) :
    complementModule C blocks S=1 ↔ ∃ B∈blocks,C\B⊆S := by
  classical
  simp [complementModule]

theorem complementModule_zero_iff (C : Finset H) (blocks : Finset (Finset H)) (S : Finset H) :
    complementModule C blocks S=0 ↔ ¬∃ B∈blocks,C\B⊆S := by
  classical
  simp [complementModule]

theorem ComplementFamily.exists_other {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) (A : Finset H) : ∃ B∈blocks,B≠A := by
  by_contra hn
  push_neg at hn
  have hc : blocks.card≤1:=card_le_one.mpr (fun B hB D hD =>
    (hn B hB).trans (hn D hD).symm)
  have hh:=h.card_two
  omega

theorem ComplementFamily.shared_mem_eq {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {A B : Finset H} (hA : A∈blocks) (hB : B∈blocks)
    {a : H} (ha : a∈A) (hb : a∈B) : A=B := by
  by_contra hne
  exact (disjoint_left.mp (h.disjoint A hA B hB hne)) ha hb

theorem ComplementFamily.module_boolean {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) : IsMonotoneBoolean (complementModule C blocks) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro S T hST
    by_cases hs : ∃ B∈blocks,C\B⊆S
    · have ht : ∃ B∈blocks,C\B⊆T := by
        obtain ⟨B,hB,hBS⟩:=hs
        exact ⟨B,hB,hBS.trans hST⟩
      simp only [complementModule,if_pos hs,if_pos ht,le_refl]
    · simp only [complementModule,if_neg hs]
      split_ifs <;> norm_num
  · intro S
    unfold complementModule
    split_ifs <;> simp
  · apply (complementModule_zero_iff _ _ _).mpr
    rintro ⟨B,hB,hBE⟩
    obtain ⟨D,hD,hDB⟩:=h.exists_other B
    obtain ⟨a,ha⟩:=h.nonempty D hD
    have haC:=h.subsets D hD ha
    have haB : a∉B:=fun hb => (disjoint_left.mp (h.disjoint D hD B hB hDB)) ha hb
    exact notMem_empty a (hBE (mem_sdiff.mpr ⟨haC,haB⟩))
  · apply (complementModule_one_iff _ _ _).mpr
    obtain ⟨B,hB,_⟩:=h.exists_other ∅
    exact ⟨B,hB,subset_univ _⟩

/-- The complete multipartite graph on the union of the complement blocks;
vertices of `C` outside that union are isolated in this response graph. -/
def Crosses (blocks : Finset (Finset H)) (u v : H) : Prop :=
  ∃ A∈blocks,∃ B∈blocks,A≠B ∧ u∈A ∧ v∈B

theorem Crosses.symm {blocks : Finset (Finset H)} {u v : H}
    (h : Crosses blocks u v) : Crosses blocks v u := by
  obtain ⟨A,hA,B,hB,hAB,hu,hv⟩:=h
  exact ⟨B,hB,A,hA,hAB.symm,hv,hu⟩

/-- All negative second differences are literal full-context indicators on
the crossing pairs, even when the function ignores hubs outside `C`. -/
theorem complementModule_negative_one_iff {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {u v : H} (huv : u≠v) {S : Finset H}
    (hu : u∉S) (hv : v∉S) :
    negativeResponse (complementModule C blocks) u v S=1 ↔
      Crosses blocks u v ∧ C⊆insert u (insert v S) := by
  rw [negativeResponse_eq_one_iff h.module_boolean]
  simp only [complementModule_zero_iff,complementModule_one_iff]
  constructor
  · rintro ⟨hn,⟨A,hA,hAu⟩,⟨B,hB,hBv⟩⟩
    have huCA : u∈C\A := by
      by_contra hh
      apply hn
      refine ⟨A,hA,?_⟩
      intro x hx
      rcases mem_insert.mp (hAu hx) with he | he
      · exact False.elim (hh (he ▸ hx))
      · exact he
    have hvCB : v∈C\B := by
      by_contra hh
      apply hn
      refine ⟨B,hB,?_⟩
      intro x hx
      rcases mem_insert.mp (hBv hx) with he | he
      · exact False.elim (hh (he ▸ hx))
      · exact he
    have huC:=(mem_sdiff.mp huCA).1
    have hvC:=(mem_sdiff.mp hvCB).1
    have huA:=(mem_sdiff.mp huCA).2
    have hvB:=(mem_sdiff.mp hvCB).2
    have hvA : v∈A := by
      by_contra hh
      rcases mem_insert.mp (hAu (mem_sdiff.mpr ⟨hvC,hh⟩)) with he | he
      · exact huv he.symm
      · exact hv he
    have huB : u∈B := by
      by_contra hh
      rcases mem_insert.mp (hBv (mem_sdiff.mpr ⟨huC,hh⟩)) with he | he
      · exact huv he
      · exact hu he
    have hBA : B≠A := fun he => huA (he ▸ huB)
    refine ⟨⟨B,hB,A,hA,hBA,huB,hvA⟩,?_⟩
    intro x hx
    by_cases hxA : x∈A
    · have hxB : x∉B:=fun hxB => (disjoint_left.mp
        (h.disjoint A hA B hB hBA.symm)) hxA hxB
      exact mem_insert_of_mem (hBv (mem_sdiff.mpr ⟨hx,hxB⟩))
    · exact (insert_subset_insert u (subset_insert v S))
        (hAu (mem_sdiff.mpr ⟨hx,hxA⟩))
  · rintro ⟨⟨A,hA,B,hB,hAB,huA,hvB⟩,hCS⟩
    have huC:=h.subsets A hA huA
    have hvC:=h.subsets B hB hvB
    refine ⟨?_,?_,?_⟩
    · rintro ⟨D,hD,hDS⟩
      have huD : u∈D := by
        by_contra hh
        exact hu (hDS (mem_sdiff.mpr ⟨huC,hh⟩))
      have hvD : v∈D := by
        by_contra hh
        exact hv (hDS (mem_sdiff.mpr ⟨hvC,hh⟩))
      exact hAB ((h.shared_mem_eq hA hD huA huD).trans
        (h.shared_mem_eq hD hB hvD hvB))
    · refine ⟨B,hB,?_⟩
      intro x hx
      have hxC:=(mem_sdiff.mp hx).1
      have hxB:=(mem_sdiff.mp hx).2
      rcases mem_insert.mp (hCS hxC) with he | he
      · exact mem_insert.mpr (Or.inl he)
      · rcases mem_insert.mp he with hev | heS
        · exact False.elim (hxB (hev.symm ▸ hvB))
        · exact mem_insert_of_mem heS
    · refine ⟨A,hA,?_⟩
      intro x hx
      have hxC:=(mem_sdiff.mp hx).1
      have hxA:=(mem_sdiff.mp hx).2
      rcases mem_insert.mp (hCS hxC) with he | he
      · exact False.elim (hxA (he.symm ▸ huA))
      · exact he

theorem complementModule_negative {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {u v : H} (huv : u≠v) {S : Finset H}
    (hu : u∉S) (hv : v∉S) :
    negativeResponse (complementModule C blocks) u v S=
      if Crosses blocks u v ∧ C⊆insert u (insert v S) then 1 else 0 := by
  classical
  by_cases hc : Crosses blocks u v ∧ C⊆insert u (insert v S)
  · rw [if_pos hc]
    exact (complementModule_negative_one_iff h huv hu hv).mpr hc
  · rw [if_neg hc]
    rcases negativeResponse_values h.module_boolean u v S with h0 | h1
    · exact h0
    · exact False.elim (hc ((complementModule_negative_one_iff h huv hu hv).mp h1))

theorem ComplementFamily.essential {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {a : H} (ha : a∈C) :
    Essential (complementModule C blocks) a := by
  obtain ⟨A,hA,_⟩:=h.exists_other ∅
  obtain ⟨B,hB,haB⟩ : ∃ B∈blocks,a∉B := by
    by_cases haA : a∈A
    · obtain ⟨B,hB,hBA⟩:=h.exists_other A
      exact ⟨B,hB,fun hb => (disjoint_left.mp (h.disjoint B hB A hA hBA)) hb haA⟩
    · exact ⟨A,hA,haA⟩
  let X:=(C\B).erase a
  have hwin : complementModule C blocks (insert a X)=1 := by
    apply (complementModule_one_iff _ _ _).mpr
    refine ⟨B,hB,?_⟩
    rw [insert_erase (mem_sdiff.mpr ⟨ha,haB⟩)]
  have hlose : complementModule C blocks X=0 := by
    apply (complementModule_zero_iff _ _ _).mpr
    rintro ⟨D,hD,hDX⟩
    by_cases hDB : D=B
    · subst D
      exact notMem_erase a (C\B) (hDX (mem_sdiff.mpr ⟨ha,haB⟩))
    · obtain ⟨b,hb⟩:=h.nonempty B hB
      have hbC:=h.subsets B hB hb
      have hbD : b∉D:=fun hd => (disjoint_left.mp (h.disjoint D hD B hB hDB)) hd hb
      have hbad:=mem_of_mem_erase (hDX (mem_sdiff.mpr ⟨hbC,hbD⟩))
      exact (mem_sdiff.mp hbad).2 hb
  exact ⟨X,notMem_erase _ _,by rw [hwin,hlose,sub_zero]⟩

theorem complementModule_ignores_outside (C : Finset H) (blocks : Finset (Finset H))
    {a : H} (ha : a∉C) (S : Finset H) :
    complementModule C blocks (insert a S)=complementModule C blocks S := by
  classical
  have he : (∃ B∈blocks,C\B⊆insert a S) ↔ ∃ B∈blocks,C\B⊆S := by
    constructor
    · rintro ⟨B,hB,hBS⟩
      refine ⟨B,hB,?_⟩
      intro x hx
      rcases mem_insert.mp (hBS hx) with hxa | hxS
      · exact False.elim (ha (hxa ▸ (mem_sdiff.mp hx).1))
      · exact hxS
    · rintro ⟨B,hB,hBS⟩
      exact ⟨B,hB,hBS.trans (subset_insert _ _)⟩
  simp only [complementModule,he]

end BooleanModule
end GraphicalZonotopes
