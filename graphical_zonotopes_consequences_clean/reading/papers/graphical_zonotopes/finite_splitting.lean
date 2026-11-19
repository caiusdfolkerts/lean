module

public import Mathlib.Order.Partition.Finpartition
public import Lean.Elab.Tactic.Omega

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {E : Type*} [DecidableEq E]

/-- A finite family whose nonsingleton members can be split into two members
admits every intermediate number of disjoint parts. The statement records
actual partitions; the later pure-response argument supplies their columns. -/
theorem partition_every_size_of_splitting (P : Finset E → Prop)
    (hsplit : ∀ A,P A → 2≤A.card →
      ∃ B D : Finset E,B.Nonempty ∧ D.Nonempty ∧ Disjoint B D ∧
        B∪D=A ∧ P B ∧ P D)
    {A : Finset E} (hA : A.Nonempty) (hPA : P A) :
    ∀ k,1≤k → k≤A.card →
      ∃ Q : Finpartition A,Q.parts.card=k ∧ ∀ B∈Q.parts,P B := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk hkA
    by_cases hk0 : k=0
    · subst k
      refine ⟨Finpartition.indiscrete hA.ne_empty,?_,?_⟩
      · rfl
      · intro B hB
        have he : B=A:=mem_singleton.mp hB
        exact he.symm ▸ hPA
    · obtain ⟨Q,hQcard,hQP⟩:=ih (by omega) (by omega)
      have hlarge : ∃ B∈Q.parts,2≤B.card := by
        by_contra hn
        have hsingle : ∀ B∈Q.parts,B.card=1 := by
          intro B hB
          have hlt : B.card<2:=Nat.lt_of_not_ge (fun h => hn ⟨B,hB,h⟩)
          have hpos : 0<B.card:=card_pos.mpr (nonempty_iff_ne_empty.mpr (Q.ne_bot hB))
          omega
        have hsum : (∑ B∈Q.parts,B.card)=Q.parts.card := by
          calc
            _ = ∑ _B∈Q.parts,1 := sum_congr rfl hsingle
            _ = _ := by simp
        rw [Q.sum_card_parts,hQcard] at hsum
        omega
      obtain ⟨B,hB,hBcard⟩:=hlarge
      obtain ⟨D,F,hD,hF,hDF,hunion,hPD,hPF⟩:=hsplit B (hQP B hB) hBcard
      let splitPart : Finpartition B :=
        (Finpartition.indiscrete hD.ne_empty).extend hF.ne_empty hDF hunion
      have hsplitCard : splitPart.parts.card=2 := by
        rw [Finpartition.card_extend]
        rfl
      have hsplitP : ∀ C∈splitPart.parts,P C := by
        intro C hC
        change C∈insert F {D} at hC
        rcases mem_insert.mp hC with he | he
        · exact he.symm ▸ hPF
        · exact (mem_singleton.mp he).symm ▸ hPD
      let pieces : ∀ C∈Q.parts,Finpartition C := fun C hC =>
        if he : C=B then he.symm ▸ splitPart else Finpartition.indiscrete (Q.ne_bot hC)
      have hpieceCard : ∀ C (hC : C∈Q.parts),(pieces C hC).parts.card=
          1+(if C=B then 1 else 0) := by
        intro C hC
        by_cases he : C=B
        · subst C
          simp [pieces,hsplitCard]
        · simp only [pieces,dif_neg he,if_neg he,Finpartition.indiscrete,card_singleton,add_zero]
      have hpieceP : ∀ C (hC : C∈Q.parts),∀ D∈(pieces C hC).parts,P D := by
        intro C hC D hD
        by_cases he : C=B
        · subst C
          simp only [pieces,dif_pos rfl] at hD
          exact hsplitP D hD
        · simp only [pieces,dif_neg he,Finpartition.indiscrete,mem_singleton] at hD
          exact hD.symm ▸ hQP C hC
      refine ⟨Q.bind pieces,?_,?_⟩
      · rw [Finpartition.card_bind]
        simp_rw [hpieceCard]
        rw [sum_add_distrib]
        have hcount : (∑ C∈Q.parts.attach,if C.1=B then (1 : ℕ) else 0)=1 := by
          have he : ∀ C : Q.parts,C.1=B ↔ C=⟨B,hB⟩ :=
            fun C => ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
          simp_rw [he]
          simp
        rw [hcount]
        simp only [sum_const,card_attach,nsmul_eq_mul,mul_one,hQcard,Nat.succ_eq_add_one]
        rfl
      · intro C hC
        obtain ⟨D,hD,hCD⟩:=Finpartition.mem_bind.mp hC
        exact hpieceP D hD C hCD

end BooleanModule
end GraphicalZonotopes
