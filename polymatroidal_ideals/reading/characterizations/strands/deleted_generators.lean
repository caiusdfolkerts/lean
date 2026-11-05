import Characterizations.BoundedFamilies
import CommAlg.KoszulComplex.FaceCombinatorics

/-! # The actual ideal obtained by deleting one Veronese generator -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def deletedVeronese (a : Exponent V) : Family V := deletedBounded a.degree ∅ a

@[simp] theorem mem_deletedVeronese (a b : Exponent V) :
    b ∈ deletedVeronese a ↔ b ≠ a ∧ b.degree = a.degree := by
  simp [deletedVeronese]

theorem deletedVeronese_equigenerated (a : Exponent V) :
    Equigenerated (deletedVeronese a) a.degree :=
  fun b hb => (mem_deletedVeronese a b).mp hb |>.2

theorem deletedVeronese_contains (a b : Exponent V) (ha : 2 ≤ a.support.card) :
    Contains (deletedVeronese a) b ↔ a.degree ≤ b.degree ∧ b ≠ a := by
  constructor
  · rintro ⟨c, hc, hcb⟩
    obtain ⟨hca, hcd⟩ := (mem_deletedVeronese a c).mp hc
    refine ⟨hcd ▸ degree_mono hcb, ?_⟩
    intro he
    subst b
    exact hca (eq_of_le_of_degree_eq hcb hcd)
  · rintro ⟨hdeg, hba⟩
    obtain ⟨c, hcb, hcd⟩ := Finsupp.exists_le_degree_eq b a.degree hdeg
    by_cases hca : c = a
    · subst c
      have hex : ∃ j, a j < b j := by
        by_contra h
        push_neg at h
        exact hba (le_antisymm h hcb)
      obtain ⟨j, hj⟩ := hex
      obtain ⟨i, hi, hij⟩ := Finset.exists_mem_ne (show 1 < a.support.card by omega) j
      have hipos : 0 < a i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
      refine ⟨exchange a i j, (mem_deletedVeronese a _).mpr
        ⟨exchange_ne hij hipos, exchange_degree a i j hipos⟩, ?_⟩
      intro x
      have hx := hcb x
      by_cases hxj : x = j
      · subst x
        simp only [exchange_apply, if_neg hij.symm, ite_true, Nat.sub_zero]
        omega
      · simp only [exchange_apply, if_neg hxj, Nat.add_zero]
        split_ifs <;> omega
    · exact ⟨c, (mem_deletedVeronese a c).mpr ⟨hca, hcd⟩, hcb⟩

theorem deletedVeronese_degree_pos (a : Exponent V) (ha : 2 ≤ a.support.card) :
    0 < a.degree := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < a.support.card by omega)
  have h := Finset.single_le_sum (f := fun i => a i) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
  have hi' := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  rw [Finsupp.degree_eq_sum]
  omega

end Characterizations
