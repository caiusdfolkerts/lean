module

public import Papers.GraphicalZonotopes.TwoHubPartition

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub.PartitionData
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (P : PartitionData I)

theorem cell_eq_of_fixed_ones {C D : Cell I}
    (hf : C.fixed=D.fixed) (ho : C.ones=D.ones) : C=D := by
  cases C
  cases D
  cases hf
  cases ho
  rfl

def totalDepth : ℕ := ∑ C : P.cells,C.1.fixed.card

/-- The natural-number form of L−k+2, with subtraction performed locally
on the positive depths. `partitionDilation_eq` proves the printed formula. -/
def partitionDilation : ℕ := (∑ C : P.cells,(C.1.fixed.card-1))+2

def fixCount (i : I) : ℕ := (univ.filter (fun C : P.cells => i∈C.1.fixed)).card

theorem depth_positive (C : P.cells) : 1≤C.1.fixed.card :=
  card_pos.mpr (P.proper C.1 C.2)

theorem sum_pred_depth_add_card :
    (∑ C : P.cells,(C.1.fixed.card-1))+P.cells.card=P.totalDepth := by
  have he : (∑ C : P.cells,((C.1.fixed.card-1)+1))=∑ C : P.cells,C.1.fixed.card := by
    apply sum_congr rfl
    intro C hC
    exact Nat.sub_add_cancel (P.depth_positive C)
  simpa only [sum_add_distrib,sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,
    mul_one,Nat.cast_id,totalDepth] using he

theorem partitionDilation_eq : P.partitionDilation=P.totalDepth-P.cells.card+2 := by
  have h := P.sum_pred_depth_add_card
  unfold partitionDilation
  omega

theorem partitionDilation_ge_two : 2≤P.partitionDilation := by
  unfold partitionDilation
  omega

theorem fixed_card_le_partitionDilation (C : P.cells) :
    C.1.fixed.card≤P.partitionDilation := by
  have hh : C.1.fixed.card-1≤∑ D : P.cells,(D.1.fixed.card-1) :=
    single_le_sum (fun D (_ : D∈(univ : Finset P.cells)) => Nat.zero_le (D.1.fixed.card-1))
      (mem_univ C)
  have hp := P.depth_positive C
  unfold partitionDilation
  omega

/-- There are at most two distinct cube cells with the same singleton
fixed set: the bit fixed there is either zero or one. -/
theorem singleton_fixed_count_le_two (i : I) :
    (univ.filter (fun C : P.cells => C.1.fixed={i})).card≤2 := by
  have hc := card_le_card_of_injOn
    (s := univ.filter (fun C : P.cells => C.1.fixed={i})) (t := (univ : Finset Bool))
    (fun C : P.cells => decide (i∈C.1.ones)) (by intro C hC; exact mem_univ _) (by
      intro C hC D hD he
      have hCf := (mem_filter.mp hC).2
      have hDf := (mem_filter.mp hD).2
      have hbits : i∈C.1.ones ↔ i∈D.1.ones := decide_eq_decide.mp he
      apply Subtype.ext
      apply cell_eq_of_fixed_ones
      · exact hCf.trans hDf.symm
      · ext j
        by_cases hji : j=i
        · subst j
          exact hbits
        · have hCj : j∉C.1.ones := by
            intro hj
            have hf := C.1.ones_subset hj
            rw [hCf] at hf
            exact hji (mem_singleton.mp hf)
          have hDj : j∉D.1.ones := by
            intro hj
            have hf := D.1.ones_subset hj
            rw [hDf] at hf
            exact hji (mem_singleton.mp hf)
          simp only [hCj,hDj,not_false_eq_true])
  simpa only [card_univ,Fintype.card_bool] using hc

theorem fixCount_le_partitionDilation (i : I) : P.fixCount i≤P.partitionDilation := by
  have hterm (C : P.cells) :
      (if i∈C.1.fixed then 1 else 0)≤C.1.fixed.card-1+
        (if C.1.fixed={i} then 1 else 0) := by
    by_cases hi : i∈C.1.fixed
    · by_cases hc : C.1.fixed.card=1
      · have he : C.1.fixed={i} :=
          (eq_of_subset_of_card_le (singleton_subset_iff.mpr hi) (by simp [hc])).symm
        simp [hi,he]
      · have hp := P.depth_positive C
        simp only [if_pos hi]
        split_ifs <;> omega
    · simp only [if_neg hi]
      exact Nat.zero_le _
  have hh := sum_le_sum (fun C (_ : C∈(univ : Finset P.cells)) => hterm C)
  simp only [sum_add_distrib,sum_boole,Nat.cast_id] at hh
  have htwo := P.singleton_fixed_count_le_two i
  unfold fixCount partitionDilation
  omega

theorem missCount_le_partitionDilation (i : I) : P.missCount i≤P.partitionDilation := by
  apply le_trans _ (P.fixCount_le_partitionDilation i)
  apply card_le_card
  intro C hC
  exact mem_filter.mpr ⟨mem_univ _,((mem_filter.mp hC).2).1⟩

end GraphicalZonotopes.TwoHub.PartitionData
