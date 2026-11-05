module

public import Papers.GraphicalZonotopes.SaturatedBookPartition

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators

variable {s : ℕ}

def lastHub (hs : 1≤s) : Fin s := ⟨s-1,by omega⟩
def oneHub (hs : 2≤s) : Fin s := ⟨1,by omega⟩

def omittedStar (hs : 5≤s) : Finset (HubPair s) :=
  starPairs univ (oneHub (by omega))
    (((univ : Finset (Fin s)).erase (oneHub (by omega))).erase (lastHub (by omega)))

theorem mem_omittedStar (hs : 5≤s) (e : HubPair s) :
    e∈omittedStar hs ↔
      (e.1.1.1.val=0 ∧ e.1.1.2.val=1) ∨
      (e.1.1.1.val=1 ∧ e.1.1.2.val<s-1) := by
  have huv : e.1.1.1.val<e.1.1.2.val := e.1.2.1
  have hub := e.1.1.2.isLt
  have hone : (oneHub (show 2≤s by omega)).val=1 := rfl
  have hlast : (lastHub (show 1≤s by omega)).val=s-1 := rfl
  simp only [omittedStar,mem_starPairs,StarPair,mem_erase,mem_univ,and_true,
    Fin.ext_iff,hone,hlast]
  dsimp
  omega

theorem omittedStar_card (hs : 5≤s) : (omittedStar hs).card=s-2 := by
  rw [omittedStar,starPairs_card _ (mem_univ _) (subset_univ _) (by simp)]
  have hne : lastHub (show 1≤s by omega)≠oneHub (show 2≤s by omega) := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [lastHub,oneHub] at hv
    omega
  rw [card_erase_of_mem (by simp [hne]),card_erase_of_mem (mem_univ _),card_univ]
  simp only [Fintype.card_fin]
  omega

theorem retainedPairs_eq_sdiff (hs : 5≤s) :
    retainedPairs s=univ\(insert (natPair 2 3 (by omega) (by omega)) (omittedStar hs)) := by
  ext e
  simp only [mem_retainedPairs,mem_sdiff,mem_univ,true_and,mem_insert,mem_omittedStar]
  have heq : e=natPair 2 3 (by omega) (by omega) ↔
      e.1.1.1.val=2 ∧ e.1.1.2.val=3 := by
    constructor
    · rintro rfl
      exact ⟨rfl,rfl⟩
    · rintro ⟨hu,hv⟩
      exact Subtype.ext (Subtype.ext (Prod.ext (Fin.ext hu) (Fin.ext hv)))
  rw [heq]
  unfold Retained
  tauto

theorem retainedPairs_card (hs : 5≤s) : (retainedPairs s).card=s.choose 2-(s-1) := by
  rw [retainedPairs_eq_sdiff hs,card_sdiff_of_subset (subset_univ _),
    card_insert_of_notMem]
  · rw [omittedStar_card hs,card_univ,pairIn_card,card_univ]
    simp only [Fintype.card_fin]
    congr 1
    omega
  · rw [mem_omittedStar]
    simp only [natPair,orderedPair]
    omega

theorem retained_count_add_anchors (hs : 5≤s) :
    (s-1)+(retainedPairs s).card=s.choose 2 := by
  rw [retainedPairs_card hs]
  have hchoose : s-1≤s.choose 2 := by
    rw [Nat.choose_two_right]
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    calc
      (s-1)*2≤(s-1)*s := Nat.mul_le_mul_left _ (by omega)
      _ = s*(s-1) := Nat.mul_comm _ _
  omega

end GraphicalZonotopes.BooleanModule.Saturated
